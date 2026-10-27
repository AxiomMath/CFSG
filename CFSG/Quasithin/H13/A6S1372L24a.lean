module

public import CFSG.Quasithin.H13.A6S1372Aut
public import CFSG.Quasithin.EmptyFaithful.S153WJFin
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.QuasithinUnique

namespace A6L24

variable {G : Type} [Group G] {K P E : Subgroup G} {X : Type} [Group X]

theorem alpha_conjK_eq (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) {k k' : ↥K} (h : α k = α k') :
    α (AutA6Rank.conjK hEK e k) = α (AutA6Rank.conjK hEK e k') := by
  have h1 : α (k⁻¹ * k') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((k⁻¹ * k' : ↥K) : G) ∈ P := (hα _).1 h1
  have h3 : (e : G) * ((k⁻¹ * k' : ↥K) : G) * (e : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hEP e.2) _).mp h2
  have h4 : α ((AutA6Rank.conjK hEK e k)⁻¹ * AutA6Rank.conjK hEK e k') = 1 := by
    rw [hα]
    convert h3 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, AutA6Rank.conjK_coe]
    group
  rw [map_mul, map_inv, inv_mul_eq_one] at h4
  exact h4

@[expose] noncomputable def gamFunX (hEK : E ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* X} (hs : Function.Surjective α) (e : ↥E) (a : X) : X :=
  α (AutA6Rank.conjK hEK e (Function.surjInv hs a))

theorem gamFunX_apply (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) (k : ↥K) :
    gamFunX hEK hs e (α k) = α (AutA6Rank.conjK hEK e k) :=
  alpha_conjK_eq hEK hEP hα e (Function.surjInv_eq hs (α k))

theorem gamFunX_mul (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) (a b : X) :
    gamFunX hEK hs e (a * b) = gamFunX hEK hs e a * gamFunX hEK hs e b := by
  obtain ⟨k, rfl⟩ := hs a
  obtain ⟨k', rfl⟩ := hs b
  rw [← map_mul, gamFunX_apply hEK hEP hs hα, gamFunX_apply hEK hEP hs hα,
    gamFunX_apply hEK hEP hs hα, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [AutA6Rank.conjK_coe, Subgroup.coe_mul]
  group

theorem gamFunX_comp (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e e' : ↥E) (a : X) :
    gamFunX hEK hs (e * e') a = gamFunX hEK hs e (gamFunX hEK hs e' a) := by
  obtain ⟨k, rfl⟩ := hs a
  rw [gamFunX_apply hEK hEP hs hα, gamFunX_apply hEK hEP hs hα, gamFunX_apply hEK hEP hs hα]
  congr 1
  apply Subtype.ext
  simp only [AutA6Rank.conjK_coe, Subgroup.coe_mul, mul_inv_rev]
  group

theorem gamFunX_one (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (a : X) :
    gamFunX hEK hs 1 a = a := by
  obtain ⟨k, rfl⟩ := hs a
  rw [gamFunX_apply hEK hEP hs hα]
  congr 1
  apply Subtype.ext
  simp [AutA6Rank.conjK_coe]

@[expose] noncomputable def gamX (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) :
    ↥E →* MulAut X where
  toFun e :=
    { toFun := gamFunX hEK hs e
      invFun := gamFunX hEK hs e⁻¹
      left_inv := fun a => by
        rw [← gamFunX_comp hEK hEP hs hα, inv_mul_cancel, gamFunX_one hEK hEP hs hα]
      right_inv := fun a => by
        rw [← gamFunX_comp hEK hEP hs hα, mul_inv_cancel, gamFunX_one hEK hEP hs hα]
      map_mul' := gamFunX_mul hEK hEP hs hα e }
  map_one' := MulEquiv.ext fun a => gamFunX_one hEK hEP hs hα a
  map_mul' e e' := MulEquiv.ext fun a => gamFunX_comp hEK hEP hs hα e e' a

theorem gamX_apply (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* X}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) (k : ↥K) :
    gamX hEK hEP hs hα e (α k) = α (AutA6Rank.conjK hEK e k) :=
  gamFunX_apply hEK hEP hs hα e k

theorem mem_ker_gamX_iff (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hEP : E ≤ Subgroup.normalizer (P : Set G))
    {α : ↥K →* X} (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P)
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ P) → e ∈ P) (e : ↥E) :
    e ∈ (gamX hEK hEP hs hα).ker ↔ (e : G) ∈ P := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    refine hfaith e e.2 fun k hk => ?_
    have h1 := congrArg (fun γ : MulAut X => γ (α ⟨k, hk⟩)) h
    simp only [gamX_apply, MulAut.one_apply] at h1
    have h2 : α (AutA6Rank.conjK hEK e ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hα _).1 h2
    simpa [AutA6Rank.conjK_coe] using h3
  · intro he
    refine MulEquiv.ext fun a => ?_
    obtain ⟨k, rfl⟩ := hs a
    rw [gamX_apply, MulAut.one_apply]
    have h1 : α ((AutA6Rank.conjK hEK e k) * k⁻¹) = 1 := by
      rw [hα]
      have hk : (k : G) * (e : G)⁻¹ * (k : G)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hKP k.2) _).mp (P.inv_mem he)
      have e1 : ((AutA6Rank.conjK hEK e k * k⁻¹ : ↥K) : G) =
          (e : G) * ((k : G) * (e : G)⁻¹ * (k : G)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, AutA6Rank.conjK_coe]
        group
      rw [e1]
      exact P.mul_mem he hk
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1

theorem relIndex_le_four [Finite G] (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hs : Function.Surjective α)
    (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P)
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ P) → e ∈ P) (hsq : ∀ e ∈ E, e * e ∈ P) :
    (P ⊓ E).relIndex E ≤ 4 := by
  classical
  set Γ := gamX hEK hEP hs hα with hΓ
  have hker : Γ.ker = P.subgroupOf E := by
    ext e
    rw [mem_ker_gamX_iff hKP hEK hEP hs hα hfaith, Subgroup.mem_subgroupOf]
  have hidx : (P ⊓ E).relIndex E = Nat.card Γ.range := by
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex, ← hker, Subgroup.index_ker]
  let c : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
        (by norm_num))
  set Y := Γ.range.map c.symm.toMonoidHom with hY
  have hsqY : ∀ y ∈ Y, y * y = 1 := by
    rintro _ ⟨γ, ⟨e, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    have he : e * e ∈ Γ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hsq e e.2
    rw [MonoidHom.mem_ker.mp he, map_one]
  have hY2 : CFSG.Open.IsElemAbelian 2 Y := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => by rw [pow_two]; exact hsqY y hy⟩
    have key : ∀ x ∈ Y, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsqY x hx)
    have e1 : (a : Equiv.Perm (Fin 5)) * b = ((a : Equiv.Perm (Fin 5)) * b)⁻¹ :=
      (key _ (Y.mul_mem a.2 b.2)).symm
    rw [mul_inv_rev, key _ a.2, key _ b.2] at e1
    exact e1
  have h4 := W153.card_le_four_of_isElemAbelian_perm5 Y hY2
  rw [hY, Subgroup.card_map_of_injective c.symm.injective] at h4
  rw [hidx]
  exact h4

theorem mul_self_eq_fin_two {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem eq_zero_of_mulVec_eq {F : Type} [Field F] [CharP F 2] {M : Matrix (Fin 2) (Fin 2) F}
    (hdet : M.det = 1) (h3 : M * M * M = 1) (h1 : M ≠ 1) {v : Fin 2 → F}
    (hv : M.mulVec v = v) : v = 0 := by
  have hCH := mul_self_eq_fin_two M
  rw [hdet, one_smul] at hCH
  have h2v : (M * M).mulVec v = v := by rw [← Matrix.mulVec_mulVec, hv, hv]
  rw [hCH, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, Matrix.one_mulVec] at h2v
  have htv : M.trace • v = 0 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have e : M.trace • v = M.trace • v - v + v := by abel
    rw [e, h2v, ← two_smul F v, h2, zero_smul]
  by_contra hv0
  have htr : M.trace = 0 := by
    by_contra htr
    exact hv0 (by simpa [htr] using htv)
  rw [htr, zero_smul, zero_sub] at hCH
  have hM2 : M * M = 1 := by
    rw [hCH, neg_eq_iff_eq_neg]
    have : (-1 : F) = 1 := by
      rw [neg_eq_iff_eq_neg]
      exact (CharTwo.neg_eq (1 : F)).symm
    calc (1 : Matrix (Fin 2) (Fin 2) F) = (1 : F) • 1 := (one_smul F _).symm
      _ = (-1 : F) • 1 := by rw [this]
      _ = -1 := by rw [neg_smul, one_smul]
  apply h1
  calc M = M * M * M := by rw [hM2, one_mul]
    _ = 1 := h3

end A6L24

end CFSG.Quasithin.H13.A6
