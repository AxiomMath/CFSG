module

public import CFSG.Quasithin.Background.B3ThreeGen

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] noncomputable def incl (n : ℕ) (k k' : Mod) (hW : k.W n ≤ k'.W n)
    (hN : ∀ w ∈ k.W n, w ∈ k.N n → w ∈ k'.N n) : Mod.V n k →* Mod.V n k' :=
  QuotientGroup.map ((k.N n).subgroupOf (k.W n)) ((k'.N n).subgroupOf (k'.W n))
    (Subgroup.inclusion hW) (fun x hx => hN x x.2 hx)

variable {k k' : Mod}

theorem incl_toV (hW : k.W n ≤ k'.W n) (hN : ∀ w ∈ k.W n, w ∈ k.N n → w ∈ k'.N n) {m : ℕ}
    (hm : inWk n k m = true) : incl n k k' hW hN (toV n k m) = toV n k' m := by
  have hm' : inWk n k' m = true := by
    rw [← vecOfNat_mem_W]
    exact hW ((vecOfNat_mem_W k m).2 hm)
  rw [toV_of_inW hm, toV_of_inW hm']
  rfl

theorem incl_act (hW : k.W n ≤ k'.W n) (hN : ∀ w ∈ k.W n, w ∈ k.N n → w ∈ k'.N n) (g : Gp n)
    (v : Mod.V n k) : incl n k k' hW hN (Mod.act n k g v) = Mod.act n k' g (incl n k k' hW hN v) := by
  induction v using QuotientGroup.induction_on with
  | H w => rfl

theorem incl_injective (hW : k.W n ≤ k'.W n) (hN : ∀ w ∈ k.W n, w ∈ k.N n → w ∈ k'.N n)
    (hinj : ∀ w ∈ k.W n, w ∈ k'.N n → w ∈ k.N n) : Function.Injective (incl n k k' hW hN) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  induction v using QuotientGroup.induction_on with
  | H w =>
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hW w) : Mod.V n k') = 1 := hv
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 : (w : U n) ∈ k'.N n := h1
    show (QuotientGroup.mk w : Mod.V n k) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hinj w w.2 h2

theorem permAct_mul_mem_U0 (σ : Gp n) (w : U n) : permAct n σ w * w ∈ U0 n := by
  by_cases hw : w ∈ U0 n
  · exact (U0 n).mul_mem (isInv_U0 n σ w hw) hw
  · refine mul_mem_U0_of_not_mem ?_ hw
    intro h
    apply hw
    have h2 := isInv_U0 n σ⁻¹ _ h
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    exact h2

theorem inWk_ratio (hkW : ∀ m, inWk n k m = popPar n m) (σ : Gp n) (m : ℕ) :
    inWk n k (actM n (tab σ) m ^^^ m) = true := by
  rw [hkW, ← vecOfNat_mem_U0, vecOfNat_xor, vecOfNat_actM]
  exact permAct_mul_mem_U0 σ _

section Ext

variable (hW : k.W n ≤ k'.W n) (hN : ∀ w ∈ k.W n, w ∈ k.N n → w ∈ k'.N n)

theorem ext_trivQ (hkW : ∀ m, inWk n k m = popPar n m) (g : Gp n) (v : Mod.V n k') : Mod.act n k' g v * v⁻¹ ∈ (incl n k k' hW hN).range := by
  obtain ⟨m, -, hm, rfl⟩ := toV_surj k' v
  rw [toV_ratio g hm]
  exact ⟨toV n k (actM n (tab g) m ^^^ m), incl_toV hW hN (inWk_ratio hkW g m)⟩

theorem ext_sup (hkW : ∀ m, inWk n k m = popPar n m) (hk'W : ∀ m, inWk n k' m = true)
    (h1 : popPar n 1 = false) :
    (incl n k k' hW hN).range ⊔ Subgroup.zpowers (toV n k' 1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨m, -, hm, rfl⟩ := toV_surj k' v
  by_cases hmk : inWk n k m = true
  · exact Subgroup.mem_sup_left ⟨toV n k m, incl_toV hW hN hmk⟩
  · have hm1 : inWk n k (m ^^^ 1) = true := by
      rw [hkW, ← vecOfNat_mem_U0, vecOfNat_xor]
      refine mul_mem_U0_of_not_mem ?_ ?_
      · rw [vecOfNat_mem_U0, ← hkW]
        simpa using hmk
      · rw [vecOfNat_mem_U0, h1]
        exact Bool.noConfusion
    have e : toV n k' m = toV n k' (m ^^^ 1) * toV n k' 1 := by
      rw [← toV_xor (hk'W _) (hk'W _), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [e]
    exact Subgroup.mul_mem_sup ⟨toV n k (m ^^^ 1), incl_toV hW hN hm1⟩ (Subgroup.mem_zpowers _)

theorem ext_not_mem (hkW : ∀ m, inWk n k m = popPar n m) (hk'W : ∀ m, inWk n k' m = true)
    (h1 : popPar n 1 = false) (hNW : ∀ w ∈ k'.N n, w ∈ U0 n) :
    toV n k' 1 ∉ (incl n k k' hW hN).range := by
  rintro ⟨x, hx⟩
  obtain ⟨m, -, hm, rfl⟩ := toV_surj k x
  rw [incl_toV hW hN hm] at hx
  have h2 : inNk n k' (m ^^^ 1) = true :=
    inNk_of_toV_eq (hk'W _) (hk'W _) hx
  have h3 : vecOfNat n (m ^^^ 1) ∈ k'.N n := (vecOfNat_mem_N k' _).2 h2
  have h4 := hNW _ h3
  rw [vecOfNat_xor] at h4
  have h5 : vecOfNat n m ∈ U0 n := by rw [vecOfNat_mem_U0, ← hkW]; exact hm
  have h6 : vecOfNat n 1 ∈ U0 n := by
    have := (U0 n).mul_mem h4 ((U0 n).inv_mem h5)
    simpa using this
  rw [vecOfNat_mem_U0, h1] at h6
  exact Bool.noConfusion h6

theorem incl_d0 (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (hk : k = Mod.u0 ∨ k = Mod.ut0)
    (hk'W : ∀ m, inWk n k' m = true) (x : LG n) :
    incl n k k' hW hN (d0 n k x) = Mod.act n k' x.1 (toV n k' 1) * (toV n k' 1)⁻¹ := by
  unfold d0
  rw [incl_toV hW hN (inWk_d0m hk (popPar_one_false hn) x.1), toV_ratio x.1 (hk'W 1)]

end Ext

end CFSG.Quasithin.B3
