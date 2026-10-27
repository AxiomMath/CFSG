module

public import CFSG.Quasithin.H13.A6S1372L76M
public import CFSG.Quasithin.H13.A6S1372L76O

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix CFSG.ComponentClassification.PresentationLocal

namespace A6L76R

@[expose] def fixSub (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : AddSubgroup (Fin 4 → ZMod 2) where
  carrier := {v | M *ᵥ v = v}
  add_mem' := fun {a b} ha hb => by
    show M *ᵥ (a + b) = a + b
    rw [Matrix.mulVec_add, show M *ᵥ a = a from ha, show M *ᵥ b = b from hb]
  zero_mem' := Matrix.mulVec_zero M
  neg_mem' := fun {a} ha => by
    show M *ᵥ (-a) = -a
    rw [Matrix.mulVec_neg, show M *ᵥ a = a from ha]

theorem card_W : Nat.card (Fin 4 → ZMod 2) = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rfl

theorem card_addSubgroup (F : AddSubgroup (Fin 4 → ZMod 2)) :
    Nat.card F = 1 ∨ Nat.card F = 2 ∨ Nat.card F = 4 ∨ Nat.card F = 8 ∨ Nat.card F = 16 := by
  have h : Nat.card F ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 from rfl, ← card_W]
    exact AddSubgroup.card_addSubgroup_dvd_card F
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  interval_cases k <;> simp [hk']

theorem mulVec_pow_succ (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) (k : ℕ) (v : Fin 4 → ZMod 2) :
    y ^ (k + 1) *ᵥ v = y *ᵥ (y ^ k *ᵥ v) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec]

theorem card_modEq_five {y : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hy : y ^ 5 = 1)
    (F : AddSubgroup (Fin 4 → ZMod 2)) (hF : ∀ v ∈ F, y *ᵥ v ∈ F) :
    Nat.card F ≡ Nat.card ↥(F ⊓ fixSub y) [MOD 5] := by
  classical
  have hpow : ∀ k : ℕ, ∀ v ∈ F, y ^ k *ᵥ v ∈ F := by
    intro k
    induction k with
    | zero => intro v hv; rwa [pow_zero, Matrix.one_mulVec]
    | succ k ih => intro v hv; rw [mulVec_pow_succ]; exact hF _ (ih v hv)
  have h5 : ∀ v, y ^ 5 *ᵥ v = v := fun v => by rw [hy, Matrix.one_mulVec]
  let σ : Equiv.Perm ↥F :=
    { toFun := fun v => ⟨y *ᵥ v, hF _ v.2⟩
      invFun := fun v => ⟨y ^ 4 *ᵥ v, hpow 4 _ v.2⟩
      left_inv := fun v => Subtype.ext (by
        show y ^ 4 *ᵥ (y *ᵥ (v : Fin 4 → ZMod 2)) = v
        rw [Matrix.mulVec_mulVec, ← pow_succ, h5])
      right_inv := fun v => Subtype.ext (by
        show y *ᵥ (y ^ 4 *ᵥ (v : Fin 4 → ZMod 2)) = v
        rw [← mulVec_pow_succ, h5]) }
  have hσk : ∀ (k : ℕ) (v : ↥F), (((σ ^ k) v : ↥F) : Fin 4 → ZMod 2) = y ^ k *ᵥ v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, pow_zero, Matrix.one_mulVec]; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', Equiv.Perm.mul_apply, mulVec_pow_succ, ← ih]
      rfl
  have hσ5 : σ ^ (5 ^ 1) = 1 := by
    ext v
    rw [hσk, pow_one, h5]
    rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := Equiv.Perm.card_compl_support_modEq hσ5
  have e : (σ.supportᶜ).card = Nat.card ↥(F ⊓ fixSub y) := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact
      { toFun := fun v => ⟨v.1.1, v.1.2, by
          have h1 := v.2
          rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at h1
          exact congrArg Subtype.val h1⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
          rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
          exact Subtype.ext w.2.2⟩
        left_inv := fun v => rfl
        right_inv := fun w => rfl }
  rw [e, ← Nat.card_eq_fintype_card] at h
  exact h.symm

theorem fixSub_eq_bot_of_five {y : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hy : y ^ 5 = 1)
    (hy1 : y ≠ 1) : fixSub y = ⊥ := by
  have h := card_modEq_five hy ⊤ (fun _ _ => AddSubgroup.mem_top _)
  rw [top_inf_eq, AddSubgroup.card_top, card_W] at h
  rcases card_addSubgroup (fixSub y) with h1 | h1 | h1 | h1 | h1
  · exact AddSubgroup.eq_bot_of_card_eq _ h1
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · exfalso
    apply hy1
    have htop := AddSubgroup.eq_top_of_card_eq _ (h1.trans card_W.symm)
    refine A6L76M.mat_ext fun v => ?_
    have hv : v ∈ fixSub y := htop ▸ AddSubgroup.mem_top v
    rw [Matrix.one_mulVec]
    exact hv

theorem fixSub_eq_bot_of_comm {x y : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hy : y ^ 5 = 1)
    (hy1 : y ≠ 1) (hx1 : x ≠ 1) (hxy : x * y = y * x) : fixSub x = ⊥ := by
  have hF : ∀ v ∈ fixSub x, y *ᵥ v ∈ fixSub x := by
    intro v hv
    show x *ᵥ (y *ᵥ v) = y *ᵥ v
    rw [Matrix.mulVec_mulVec, hxy, ← Matrix.mulVec_mulVec, show x *ᵥ v = v from hv]
  have h := card_modEq_five hy (fixSub x) hF
  rw [fixSub_eq_bot_of_five hy hy1, inf_bot_eq, AddSubgroup.card_bot] at h
  rcases card_addSubgroup (fixSub x) with h1 | h1 | h1 | h1 | h1
  · exact AddSubgroup.eq_bot_of_card_eq _ h1
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · exfalso
    apply hx1
    have htop := AddSubgroup.eq_top_of_card_eq _ (h1.trans card_W.symm)
    refine A6L76M.mat_ext fun v => ?_
    have hv : v ∈ fixSub x := htop ▸ AddSubgroup.mem_top v
    rw [Matrix.one_mulVec]
    exact hv

@[expose] def u5 : alternatingGroup (Fin 8) :=
  A6L76O.alt8 (swap 3 4 * swap 4 5 * swap 5 6 * swap 6 7) (by decide)

theorem u5_facts : u5 ^ 5 = 1 ∧ u5 ≠ 1 ∧ A6L76O.t8 * u5 = u5 * A6L76O.t8 ∧ A6L76O.t8 ≠ 1 := by
  decide +kernel

theorem fpf_t8 (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2)
    (hv : ((α A6L76O.t8 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) :
    v = 0 := by
  obtain ⟨h5, hu1, hcomm, ht1⟩ := u5_facts
  have hval : ∀ g h : ↥(alternatingGroup (Fin 8)),
      ((α (g * h) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        (α g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (α h : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
    fun g h => by rw [map_mul, Units.val_mul]
  have hy : ((α u5 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h5, map_one, Units.val_one]
  have hne : ∀ g : ↥(alternatingGroup (Fin 8)), g ≠ 1 →
      ((α g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ 1 := by
    intro g hg h
    apply hg
    apply α.injective
    rw [map_one]
    exact Units.ext h
  have h := fixSub_eq_bot_of_comm hy (hne _ hu1) (hne _ ht1) (by rw [← hval, hcomm, hval])
  have hv' : v ∈ fixSub _ := hv
  rw [h] at hv'
  exact (AddSubgroup.mem_bot).1 hv'

theorem altLift7_castSucc (σ : alternatingGroup (Fin 7)) (j : Fin 7) :
    ((altLift7 σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) j.castSucc =
      ((σ : Perm (Fin 7)) j).castSucc := by
  simp only [altLift7, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    Equiv.Perm.viaEmbeddingHom_apply]
  exact Equiv.Perm.viaEmbedding_apply _ _ _

theorem altLift7_last' (σ : alternatingGroup (Fin 7)) :
    ((altLift7 σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) (Fin.last 7) = Fin.last 7 := by
  simp only [altLift7, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    Equiv.Perm.viaEmbeddingHom_apply]
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

theorem altLift7_gen7 : altLift7 (B45Alt7.gen7 false) = A6L76O.t8 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
    rw [altLift7_last']
    decide
  | cast j =>
    rw [altLift7_castSucc]
    revert j
    decide

end A6L76R

namespace A6L76R

theorem mk_inj_a7 {α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)}
    {a b : ↥(FFModel.a7Four α).sec}
    (h : (QuotientGroup.mk a : ↥(FFModel.a7Four α).sec ⧸ (FFModel.a7Four α).ker.subgroupOf
      (FFModel.a7Four α).sec) = QuotientGroup.mk b) : a = b := by
  rw [QuotientGroup.eq] at h
  have h' : (show Multiplicative (Fin 4 → ZMod 2) from (a⁻¹ * b : ↥(FFModel.a7Four α).sec).1) =
      1 :=
    (Subgroup.mem_bot).1
      (Subgroup.mem_subgroupOf.1 h : _ ∈ (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))))
  exact inv_mul_eq_one.1 (Subtype.ext h')

theorem fixV_eq_bot_of_a7Four (V : Type) [CommGroup V] [Finite V] (Y : Subgroup (MulAut V))
    (hV2 : ∀ v : V, v * v = 1) (htop : commV Y = ⊤)
    (hA : A7Four Y (commV Y) (fixV Y ⊓ commV Y)) : fixV Y = ⊥ := by
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add]
    exact hV2 (Additive.toMul x)
  obtain ⟨α, π, hπ⟩ := hA
  obtain ⟨hπs, -, -, -, -, -, -, β, -, hβk, hβe⟩ := hπ
  let θ : ↥(alternatingGroup (Fin 7)) →* MulAut V := Y.subtype.comp π
  let ρ : Representation (ZMod 2) ↥(alternatingGroup (Fin 7)) (Additive V) :=
    { toFun := fun σ => (AddMonoidHom.mk'
        (fun x : Additive V => Additive.ofMul (θ σ (Additive.toMul x)))
        (fun x y => by simp)).toZModLinearMap 2
      map_one' := by
        ext x
        simp
      map_mul' := fun s t => by
        ext x
        simp }
  have hρ : ∀ σ x, ρ σ x = Additive.ofMul (θ σ (Additive.toMul x)) := fun _ _ => rfl
  let U : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (fixV Y))
  have hmemU : ∀ x, x ∈ U ↔ Additive.toMul x ∈ fixV Y := fun x => Iff.rfl
  have hθY : ∀ σ, θ σ ∈ Y := fun σ => (π σ).2
  have hU : ∀ g, ∀ u ∈ U, ρ g u = u := by
    intro g u hu
    rw [hρ]
    exact congrArg Additive.ofMul ((hmemU u).1 hu (θ g) (hθY g))
  have hfpf : ∀ v, ρ (B45Alt7.gen7 false) v - v ∈ U → v ∈ U := by
    intro v hv
    rw [hmemU] at hv ⊢
    have hv' : θ (B45Alt7.gen7 false) (Additive.toMul v) * (Additive.toMul v)⁻¹ ∈ fixV Y := by
      have h0 := hv
      rwa [toMul_sub, div_eq_mul_inv] at h0
    have hwC : Additive.toMul v ∈ commV Y := htop ▸ Subgroup.mem_top _
    have hθC : θ (B45Alt7.gen7 false) (Additive.toMul v) ∈ commV Y := htop ▸ Subgroup.mem_top _
    have hcC : θ (B45Alt7.gen7 false) (Additive.toMul v) * (Additive.toMul v)⁻¹ ∈ commV Y :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨_, hwC⟩)
    have h1 : β ⟨_, hθC⟩ = QuotientGroup.mk ⟨(FFModel.a7Four α).act (B45Alt7.gen7 false) m.1,
        Subgroup.mem_top _⟩ :=
      hβe (B45Alt7.gen7 false) ⟨_, hwC⟩ m hθC (Subgroup.mem_top _) hm.symm
    have h2 : β ⟨_, hcC⟩ = 1 := (hβk _).2 ⟨hv', hcC⟩
    have h3 : β ⟨_, hθC⟩ = β ⟨_, hwC⟩ := by
      have e : (⟨_, hθC⟩ : ↥(commV Y)) = ⟨_, hcC⟩ * ⟨_, hwC⟩ :=
        Subtype.ext (inv_mul_cancel_right _ _).symm
      rw [e, map_mul, h2, one_mul]
    rw [h1, ← hm] at h3
    have h4 := mk_inj_a7 h3
    have h5 := congrArg (fun z : ↥(FFModel.a7Four α).sec =>
      Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from z.1)) h4
    simp only at h5
    have h6 : ((α A6L76O.t8 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from m.1) =
        Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from m.1) := by
      rw [← altLift7_gen7]
      exact h5
    have h7 := fpf_t8 α _ h6
    have h8 : m = 1 := Subtype.ext (show (show Multiplicative (Fin 4 → ZMod 2) from m.1) = 1 from
      toAdd_eq_zero.1 h7)
    have h9 : β ⟨_, hwC⟩ = 1 := by rw [← hm, h8, QuotientGroup.mk_one]
    exact ((hβk _).1 h9).1
  have hspan : ∀ C : Submodule (ZMod 2) (Additive V), (∀ g v, ρ g v - v ∈ C) → C = ⊤ := by
    intro C hC
    let C' : Subgroup V :=
      { carrier := {w | Additive.ofMul w ∈ C}
        one_mem' := C.zero_mem
        mul_mem' := fun ha hb => C.add_mem ha hb
        inv_mem' := fun ha => C.neg_mem ha }
    have hle : commV Y ≤ C' := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨y, hy, v, rfl⟩
      obtain ⟨σ, hσ⟩ := hπs ⟨y, hy⟩
      have hy' : θ σ = y := congrArg Subtype.val hσ
      show Additive.ofMul (y v * v⁻¹) ∈ C
      have e : Additive.ofMul (y v * v⁻¹) =
          ρ (show ↥(alternatingGroup (Fin 7)) from σ) (Additive.ofMul v) - Additive.ofMul v := by
        rw [← hy', hρ, ← div_eq_mul_inv, ofMul_div]
        rfl
      rw [e]
      exact hC σ (Additive.ofMul v)
    rw [eq_top_iff]
    intro x _
    exact hle (htop ▸ Subgroup.mem_top (Additive.toMul x))
  have hbot := A7Q528.eq_bot_of_split hU hfpf hspan
  rw [eq_bot_iff]
  intro w hw
  have h1 : Additive.ofMul w ∈ U := (hmemU _).2 hw
  rw [hbot, Submodule.mem_bot] at h1
  exact (Subgroup.mem_bot).2 (Additive.ofMul.injective h1)

end A6L76R

end CFSG.Quasithin.H13.A6
