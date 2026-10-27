module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5FinPerm

public section

namespace CFSG.Quasithin

namespace B5FinS8

abbrev Ker8 : Subgroup ↥(G6.coreMod 8) :=
  (Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8).subgroupOf (G6.coreMod 8)

abbrev Mod8 : Type := ↥(G6.coreMod 8) ⧸ Ker8

@[expose] noncomputable def act8 (σ : Equiv.Perm (Fin 8)) : Mod8 →* Mod8 :=
  (FFModel.symDn_isActionModel 8).modEnd σ

theorem act8_mk (σ : Equiv.Perm (Fin 8)) (m : ↥(G6.coreMod 8)) :
    act8 σ (QuotientGroup.mk m) =
      QuotientGroup.mk (⟨G6.permAct 8 σ m.1, G6.permAct_mem_coreMod σ m.2⟩ : ↥(G6.coreMod 8)) :=
  rfl

@[expose] def ev (i : Fin 8) : Fin 8 → ZMod 2 := Pi.single i 1

@[expose] def pv (a b : Fin 8) : Fin 8 → ZMod 2 := ev a + ev b

theorem sum_pv : ∀ a b : Fin 8, ∑ i, pv a b i = 0 := by decide +kernel

@[expose] def pelt (a b : Fin 8) : ↥(G6.coreMod 8) :=
  ⟨Multiplicative.ofAdd (pv a b), (G6.mem_coreMod).2 (sum_pv a b)⟩

@[expose] def pclass (a b : Fin 8) : Mod8 := QuotientGroup.mk (pelt a b)

theorem vec_add_self : ∀ u : Fin 8 → ZMod 2, u + u = 0 := by decide +kernel

theorem mk_eq_mk_iff (x y : ↥(G6.coreMod 8)) :
    (QuotientGroup.mk x : Mod8) = QuotientGroup.mk y ↔
      (Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1 = 0 ∨
        Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1 = fun _ => 1) := by
  rw [QuotientGroup.eq]
  change x.1⁻¹ * y.1 ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 ↔ _
  rw [Subgroup.mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  have hcore : x.1⁻¹ * y.1 ∈ G6.coreMod 8 := (x⁻¹ * y).2
  have hneg : ∀ u : Fin 8 → ZMod 2, -u = u := by decide +kernel
  have e1 : Multiplicative.toAdd (x.1⁻¹ * y.1) =
      Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1 := by
    rw [toAdd_mul, toAdd_inv, hneg]
  constructor
  · rintro ⟨h | h, -⟩
    · left
      rw [← e1, h]
      rfl
    · right
      rw [← e1, h]
      rfl
  · rintro (h | h)
    · exact ⟨Or.inl (Multiplicative.toAdd.injective (by rw [e1, h]; rfl)), hcore⟩
    · exact ⟨Or.inr (Multiplicative.toAdd.injective (by rw [e1, h]; rfl)), hcore⟩

theorem pv_ne : ∀ a b : Fin 8, a ≠ b → pv a b ≠ 0 ∧ pv a b ≠ fun _ => 1 := by decide +kernel

theorem pclass_ne_one (a b : Fin 8) (hab : a ≠ b) : pclass a b ≠ 1 := by
  intro h
  have h1 : (QuotientGroup.mk (pelt a b) : Mod8) = QuotientGroup.mk 1 := h
  rw [mk_eq_mk_iff] at h1
  have h2 : Multiplicative.toAdd (pelt a b).1 + Multiplicative.toAdd (1 : ↥(G6.coreMod 8)).1 =
      pv a b := by
    change pv a b + 0 = pv a b
    exact add_zero _
  rw [h2] at h1
  rcases h1 with h1 | h1
  · exact (pv_ne a b hab).1 h1
  · exact (pv_ne a b hab).2 h1

theorem permAct_pv (σ : Equiv.Perm (Fin 8)) (a b : Fin 8) :
    G6.permAct 8 σ (Multiplicative.ofAdd (pv a b)) = Multiplicative.ofAdd (pv (σ a) (σ b)) := by
  apply Multiplicative.toAdd.injective
  funext i
  change pv a b (σ⁻¹ i) = pv (σ a) (σ b) i
  have h1 : (σ⁻¹ i = a) ↔ (i = σ a) := by rw [Equiv.Perm.inv_eq_iff_eq]
  have h2 : (σ⁻¹ i = b) ↔ (i = σ b) := by rw [Equiv.Perm.inv_eq_iff_eq]
  simp only [pv, ev, Pi.add_apply, Pi.single_apply, h1, h2]

theorem act8_pclass (σ : Equiv.Perm (Fin 8)) (a b : Fin 8) :
    act8 σ (pclass a b) = pclass (σ a) (σ b) := by
  rw [pclass, act8_mk, pclass]
  congr 1
  exact Subtype.ext (permAct_pv σ a b)

@[expose] def cyc (a b c : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap a b * Equiv.swap b c

@[expose] def inv3 (a b c i : Fin 8) : Fin 8 :=
  if i = b then a else if i = c then b else if i = a then c else i

theorem cyc_inv : ∀ i : Fin 8, (cyc 2 3 4)⁻¹ i = inv3 2 3 4 i ∧ (cyc 3 4 5)⁻¹ i = inv3 3 4 5 i ∧
    (cyc 4 5 6)⁻¹ i = inv3 4 5 6 i ∧ (cyc 5 6 7)⁻¹ i = inv3 5 6 7 i := by
  decide +kernel

theorem sign_cyc (a b c : Fin 8) (hab : a ≠ b) (hbc : b ≠ c) :
    Equiv.Perm.sign (cyc a b c) = 1 := by
  rw [cyc, map_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc]
  decide

abbrev FixCond (f : Fin 8 → Fin 8) (v : Fin 8 → ZMod 2) : Prop :=
  v + (fun i => v (f i)) = 0 ∨ v + (fun i => v (f i)) = fun _ => 1

theorem fixed_pair : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 →
    FixCond (inv3 2 3 4) v → FixCond (inv3 3 4 5) v → FixCond (inv3 4 5 6) v →
    FixCond (inv3 5 6 7) v →
    v = 0 ∨ v = (fun _ => 1) ∨ v = pv 0 1 ∨ v = pv 0 1 + fun _ => 1 := by
  decide +kernel

@[expose] def sigma (i : Fin 8) : Equiv.Perm (Fin 8) :=
  if i = 1 then 1 else List.formPerm [1, i, if i = 2 then 3 else 2]

theorem sigma_spec (i : Fin 8) (hi : i ≠ 0) :
    Equiv.Perm.sign (sigma i) = 1 ∧ sigma i 0 = 0 ∧ sigma i 1 = i := by
  revert i
  decide +kernel

theorem exists_pv_sum : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 →
    v = (v 1).val • pv 0 1 + (v 2).val • pv 0 2 + (v 3).val • pv 0 3 + (v 4).val • pv 0 4 +
      (v 5).val • pv 0 5 + (v 6).val • pv 0 6 + (v 7).val • pv 0 7 := by
  decide +kernel

theorem k8 (μ : Mod8 →* Mod8) (hinj : Function.Injective μ)
    (hcomm : ∀ σ : Equiv.Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) → ∀ q : Mod8,
      μ (act8 σ q) = act8 σ (μ q)) :
    ∀ q : Mod8, μ q = q := by
  have hne : pclass 0 1 ≠ 1 := pclass_ne_one 0 1 (by decide)
  have hq0 : μ (pclass 0 1) = pclass 0 1 := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (μ (pclass 0 1))
    have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
    have hfix : ∀ a b c : Fin 8, a ≠ b → b ≠ c → (∀ i, (cyc a b c)⁻¹ i = inv3 a b c i) →
        cyc a b c 0 = 0 → cyc a b c 1 = 1 →
        FixCond (inv3 a b c) (Multiplicative.toAdd x.1) := by
      intro a b c hab hbc hinv h0 h1'
      have hτA : cyc a b c ∈ alternatingGroup (Fin 8) :=
        Equiv.Perm.mem_alternatingGroup.2 (sign_cyc a b c hab hbc)
      have h1 := hcomm (cyc a b c) hτA (pclass 0 1)
      rw [act8_pclass, h0, h1', ← hx, act8_mk] at h1
      have h2 := (mk_eq_mk_iff _ _).1 h1
      have h3 : Multiplicative.toAdd (G6.permAct 8 (cyc a b c) x.1) =
          fun i => Multiplicative.toAdd x.1 (inv3 a b c i) := by
        funext i
        exact congrArg (Multiplicative.toAdd x.1) (hinv i)
      have h4 : Multiplicative.toAdd (⟨G6.permAct 8 (cyc a b c) x.1,
          G6.permAct_mem_coreMod (cyc a b c) x.2⟩ : ↥(G6.coreMod 8)).1 =
          fun i => Multiplicative.toAdd x.1 (inv3 a b c i) := h3
      rw [h4] at h2
      exact h2
    rcases fixed_pair _ hvsum
        (hfix 2 3 4 (by decide) (by decide) (fun i => (cyc_inv i).1) (by decide) (by decide))
        (hfix 3 4 5 (by decide) (by decide) (fun i => (cyc_inv i).2.1) (by decide) (by decide))
        (hfix 4 5 6 (by decide) (by decide) (fun i => (cyc_inv i).2.2.1) (by decide) (by decide))
        (hfix 5 6 7 (by decide) (by decide) (fun i => (cyc_inv i).2.2.2) (by decide) (by decide))
        with h | h | h | h
    · exfalso
      have hmk : (QuotientGroup.mk x : Mod8) = 1 := by
        change (QuotientGroup.mk x : Mod8) = QuotientGroup.mk 1
        rw [mk_eq_mk_iff]
        left
        change Multiplicative.toAdd x.1 + 0 = 0
        rw [h, add_zero]
      exact hne (hinj ((hx.symm.trans hmk).trans (map_one μ).symm))
    · exfalso
      have hmk : (QuotientGroup.mk x : Mod8) = 1 := by
        change (QuotientGroup.mk x : Mod8) = QuotientGroup.mk 1
        rw [mk_eq_mk_iff]
        right
        change Multiplicative.toAdd x.1 + 0 = fun _ => 1
        rw [add_zero]
        exact h
      exact hne (hinj ((hx.symm.trans hmk).trans (map_one μ).symm))
    · have hxe : x = pelt 0 1 := Subtype.ext (Multiplicative.toAdd.injective h)
      rw [← hx, hxe]
      rfl
    · rw [← hx, pclass, mk_eq_mk_iff]
      right
      change Multiplicative.toAdd x.1 + pv 0 1 = fun _ => 1
      rw [h, add_right_comm, vec_add_self, zero_add]
  have hq : ∀ i : Fin 8, i ≠ 0 →
      μ (QuotientGroup.mk (pelt 0 i)) = (QuotientGroup.mk (pelt 0 i) : Mod8) := by
    intro i hi
    obtain ⟨hsg, h0, h1⟩ := sigma_spec i hi
    have hA : sigma i ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 hsg
    have h := hcomm (sigma i) hA (pclass 0 1)
    rw [act8_pclass, hq0, act8_pclass, h0, h1] at h
    exact h
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hvsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
  have hx : x = (pelt 0 1) ^ (Multiplicative.toAdd x.1 1).val *
      (pelt 0 2) ^ (Multiplicative.toAdd x.1 2).val * (pelt 0 3) ^ (Multiplicative.toAdd x.1 3).val *
      (pelt 0 4) ^ (Multiplicative.toAdd x.1 4).val * (pelt 0 5) ^ (Multiplicative.toAdd x.1 5).val *
      (pelt 0 6) ^ (Multiplicative.toAdd x.1 6).val * (pelt 0 7) ^ (Multiplicative.toAdd x.1 7).val := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, toAdd_mul, toAdd_pow]
    exact exists_pv_sum _ hvsum
  rw [hx]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, map_mul, map_pow]
  rw [hq 1 (by decide), hq 2 (by decide), hq 3 (by decide), hq 4 (by decide), hq 5 (by decide),
    hq 6 (by decide), hq 7 (by decide)]

end B5FinS8

end CFSG.Quasithin
