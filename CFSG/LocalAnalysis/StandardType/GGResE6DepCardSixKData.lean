module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixFinite
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem cs6J_injective (jj : Fin 5) : Function.Injective (cs6J jj) := by
  revert jj
  decide +kernel

private def cs6TypeCoxeter : Fin 4 → CoxeterMatrix (Fin 5) :=
  ![CoxeterMatrix.A 5, CoxeterMatrix.B 5, CoxeterMatrix.B 5, ggCoxeterMatrixD 5]

private theorem cs6TypeCoxeter_intCartan (X : Fin 4) :
    GGIntCartan (cs6TypeCoxeter X) (cs6TypeCartan X) := by
  fin_cases X
  · exact ggIntCartan_A 5
  · exact ggIntCartan_B 5
  · exact ggIntCartan_C 5
  · exact ggIntCartan_D 5

private theorem cs6_order_of_model
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa)} {X : Fin 4}
    (hCKK : GGIntCartan MK CK)
    (hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan X i j) :
    MK = (cs6TypeCoxeter X).reindex e5 := by
  have heq : CK = fun o o' => cs6TypeCartan X (e5.symm o) (e5.symm o') := by
    ext o o'
    have h := hX (e5.symm o) (e5.symm o')
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  have hCX : GGIntCartan ((cs6TypeCoxeter X).reindex e5) CK := by
    rw [heq]
    exact l05nBL_intCartan_reindex (cs6TypeCoxeter_intCartan X) e5.symm
  exact ggIntCartan_coxeter_eq hCKK hCX

private theorem cs6_order_bound
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa)} {X : Fin 4}
    (hCKK : GGIntCartan MK CK)
    (hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan X i j) :
    Nat.card MK.Group ≤ 3840 ∧ (cs6TypeDet X = 6 → Nat.card MK.Group ≤ 720) := by
  have hcox := cs6_order_of_model hCKK hX
  have hcard : Nat.card MK.Group = Nat.card (cs6TypeCoxeter X).Group := by
    rw [hcox]
    exact Nat.card_congr (CoxeterMatrix.reindexGroupEquiv (cs6TypeCoxeter X) e5).toEquiv
  constructor
  · rw [hcard]
    fin_cases X
    · show Nat.card (CoxeterMatrix.A 5).Group ≤ 3840
      rw [l05nK3a_card_coxeterA]; norm_num
    · show Nat.card (CoxeterMatrix.B 5).Group ≤ 3840
      exact le_trans (card_coxeterB_le 5) (by norm_num)
    · show Nat.card (CoxeterMatrix.B 5).Group ≤ 3840
      exact le_trans (card_coxeterB_le 5) (by norm_num)
    · show Nat.card (ggCoxeterMatrixD 5).Group ≤ 3840
      rw [OrthF3.card_coxeterD_eq 5 (by omega)]; norm_num
  · intro hX6
    have hX0 : X = 0 := by
      fin_cases X
      · rfl
      · simp [cs6TypeDet] at hX6
      · simp [cs6TypeDet] at hX6
      · simp [cs6TypeDet] at hX6
    subst X
    rw [hcard]
    show Nat.card (CoxeterMatrix.A 5).Group ≤ 720
    rw [l05nK3a_card_coxeterA]; norm_num

private theorem cs6_model_data
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (e6 : Fin 6 ≃ Λ) (jj : Fin 5)
    (τ : Fin 4 → {i : Λ // i ∉ S}) (hτ : ∀ i, (τ i : Λ) = e6 (cs6J jj i))
    (a0 : Λa)
    (hKL : ∀ i j : {i : Λ // i ∉ S},
      ((CK (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (e6.symm i) (e6.symm j) : ℤ) : ZMod 3))
    (e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa))
    (X : Fin 4)
    (hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan X i j) :
    ∃ pi < cs6NumPat jj, cs6PatDet jj pi = cs6TypeDet X ∧
      (∀ i : Fin 4,
        ((CK (Sum.inl (τ i)) (Sum.inr a0) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).1 ∧
        ((CK (Sum.inr a0) (Sum.inl (τ i)) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).2) := by
  classical
  let nodeAtFun : Fin 5 → ({i : Λ // i ∉ S} ⊕ Λa) :=
    Fin.lastCases (Sum.inr a0) (fun i : Fin 4 => Sum.inl (τ i))
  have hnode_cast : ∀ i : Fin 4, nodeAtFun i.castSucc = Sum.inl (τ i) := by
    intro i; simp [nodeAtFun, Fin.lastCases_castSucc]
  have hnode_last : nodeAtFun (Fin.last 4) = Sum.inr a0 := by
    show Fin.lastCases (Sum.inr a0) (fun i : Fin 4 => Sum.inl (τ i)) (Fin.last 4) = Sum.inr a0
    exact Fin.lastCases_last
  have hτ_inj : Function.Injective τ := by
    intro i j hij
    have h1 : e6 (cs6J jj i) = e6 (cs6J jj j) := by
      rw [← hτ i, ← hτ j, hij]
    exact cs6J_injective jj (e6.injective h1)
  have hnode_inj : Function.Injective nodeAtFun := by
    intro u v huv
    rcases Fin.eq_castSucc_or_eq_last u with ⟨i, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last v with ⟨j, rfl⟩ | rfl
    · rw [hnode_cast, hnode_cast, Sum.inl.injEq] at huv
      exact congrArg Fin.castSucc (hτ_inj huv)
    · rw [hnode_cast, hnode_last] at huv; exact (Sum.inl_ne_inr huv).elim
    · rw [hnode_last, hnode_cast] at huv; exact (Sum.inr_ne_inl huv).elim
    · rfl
  let σ : Equiv.Perm (Fin 5) :=
    (Equiv.ofBijective (fun u => e5.symm (nodeAtFun u))
      (Finite.injective_iff_bijective.mp (e5.symm.injective.comp hnode_inj))).symm
  have hσsymm : ∀ u, σ.symm u = e5.symm (nodeAtFun u) := fun u => rfl
  have hσ : ∀ u v, cs6TypeCartan X (σ.symm u) (σ.symm v) =
      CK (nodeAtFun u) (nodeAtFun v) := by
    intro u v
    rw [hσsymm u, hσsymm v]
    have h := hX (e5.symm (nodeAtFun u)) (e5.symm (nodeAtFun v))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  have hJ : ∀ i j : Fin 4,
      ((cs6TypeCartan X (σ.symm i.castSucc) (σ.symm j.castSucc) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (cs6J jj i) (cs6J jj j) : ℤ) : ZMod 3) := by
    intro i j
    rw [hσ i.castSucc j.castSucc, hnode_cast i, hnode_cast j, hKL (τ i) (τ j)]
    simp [hτ]
  rcases cs6_pattern_bridge jj X σ hJ with ⟨pi, hpi, hdet, hres⟩
  refine ⟨pi, hpi, hdet, ?_⟩
  intro i
  exact ⟨by rw [← (hres i).1, hσ i.castSucc (Fin.last 4), hnode_cast i, hnode_last],
         by rw [← (hres i).2, hσ (Fin.last 4) i.castSucc, hnode_cast i, hnode_last]⟩

private theorem cs6_finish
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (e6 : Fin 6 ≃ Λ) (jj : Fin 5) (τ : Fin 4 → {i : Λ // i ∉ S})
    (hτ : ∀ i, (τ i : Λ) = e6 (cs6J jj i)) (a0 : Λa) (ha0 : ∀ a : Λa, a = a0)
    (hKL : ∀ i j : {i : Λ // i ∉ S},
      ((CK (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (e6.symm i) (e6.symm j) : ℤ) : ZMod 3))
    (e5 : Fin 5 ≃ ({i : Λ // i ∉ S} ⊕ Λa)) (X : Fin 4)
    (hCKK : GGIntCartan MK CK)
    (hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan X i j) :
    ∃ (pi : Nat) (a0' : Λa) (τ' : Fin 4 → {i : Λ // i ∉ S}),
      (∀ i, (τ' i : Λ) = e6 (cs6J jj i)) ∧ (∀ a : Λa, a = a0') ∧ pi < cs6NumPat jj ∧
      (∀ i : Fin 4,
        ((CK (Sum.inl (τ' i)) (Sum.inr a0') : ℤ) : ZMod 3) = (cs6PatPair jj pi i).1 ∧
        ((CK (Sum.inr a0') (Sum.inl (τ' i)) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).2) ∧
      Nat.card MK.Group ≤ 3840 ∧ (cs6PatDet jj pi = 6 → Nat.card MK.Group ≤ 720) := by
  obtain ⟨pi, hpi, hdet, hres⟩ := cs6_model_data e6 jj τ hτ a0 hKL e5 X hX
  obtain ⟨hbound, hbound6⟩ := cs6_order_bound hCKK hX
  exact ⟨pi, a0, τ, hτ, ha0, hpi, hres, hbound, fun h6 => hbound6 (hdet ▸ h6)⟩

private theorem cs6_Kdata_body
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (e6 : Fin 6 ≃ Λ) (hΛa : Nat.card Λa = 1)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (hKL : ∀ i j : {i : Λ // i ∉ S},
      ((CK (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (e6.symm i) (e6.symm j) : ℤ) : ZMod 3))
    (jj : Fin 5)
    (hsurv : ∀ t : Fin 6, e6 t ∈ S ↔ t ∉ Set.range (cs6J jj)) :
    ∃ (pi : Nat) (a0 : Λa) (τ : Fin 4 → {i : Λ // i ∉ S}),
      (∀ i, (τ i : Λ) = e6 (cs6J jj i)) ∧ (∀ a : Λa, a = a0) ∧ pi < cs6NumPat jj ∧
      (∀ i : Fin 4,
        ((CK (Sum.inl (τ i)) (Sum.inr a0) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).1 ∧
        ((CK (Sum.inr a0) (Sum.inl (τ i)) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).2) ∧
      Nat.card MK.Group ≤ 3840 ∧ (cs6PatDet jj pi = 6 → Nat.card MK.Group ≤ 720) := by
  classical
  haveI hsub : Subsingleton Λa := (Nat.card_eq_one_iff_unique.mp hΛa).1
  let a0 : Λa := Classical.choice (Nat.card_eq_one_iff_unique.mp hΛa).2
  have ha0 : ∀ a : Λa, a = a0 := fun a => Subsingleton.elim a a0
  let τ : Fin 4 ≃ {i : Λ // i ∉ S} := Equiv.ofBijective
    (fun i => ⟨e6 (cs6J jj i), fun h => (hsurv (cs6J jj i)).mp h ⟨i, rfl⟩⟩)
    (by
      constructor
      · intro a b hab
        have h1 : e6 (cs6J jj a) = e6 (cs6J jj b) := congrArg Subtype.val hab
        exact cs6J_injective jj (e6.injective h1)
      · intro u
        have hmem : e6.symm u.1 ∈ Set.range (cs6J jj) := by
          by_contra hc
          exact u.2 (by simpa using (hsurv (e6.symm u.1)).mpr hc)
        obtain ⟨a, ha⟩ := hmem
        refine ⟨a, Subtype.ext ?_⟩
        show e6 (cs6J jj a) = u.1
        rw [ha, Equiv.apply_symm_apply])
  have hτ : ∀ i, (τ i : Λ) = e6 (cs6J jj i) := fun i => rfl
  have hcard5' : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_sum, ← Nat.card_congr τ, Nat.card_fin, hΛa]
  rcases ggIntCartan_models hWMK hCKK with
    ⟨n, e5, hn, hdisj⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG⟩
  · have hn5 : n = 5 := by
      have h := Fintype.card_congr e5
      simpa only [Fintype.card_fin, hcard5'] using h
    subst n
    rcases hdisj with hA | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩
    · have hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan 0 i j := by
        intro i j; rw [hA i j]; rfl
      exact cs6_finish e6 jj τ hτ a0 ha0 hKL e5 0 hCKK hX
    · have hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan 1 i j := by
        intro i j; rw [hB i j]; rfl
      exact cs6_finish e6 jj τ hτ a0 ha0 hKL e5 1 hCKK hX
    · have hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan 2 i j := by
        intro i j; rw [hC i j]; rfl
      exact cs6_finish e6 jj τ hτ a0 ha0 hKL e5 2 hCKK hX
    · have hX : ∀ i j, CK (e5 i) (e5 j) = cs6TypeCartan 3 i j := by
        intro i j; rw [hD i j]; rfl
      exact cs6_finish e6 jj τ hτ a0 ha0 hKL e5 3 hCKK hX
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard5'] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard5'] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard5'] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard5'] at h
    omega
  · exfalso
    have h := Fintype.card_congr e
    rw [Fintype.card_fin, hcard5'] at h
    omega

private theorem cs6_hsurv_of_eq
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    (e6 : Fin 6 ≃ Λ) (jj : Fin 5) (U : Finset (Fin 6))
    (h : S.image e6.symm = U)
    (hcheck : ∀ t : Fin 6, t ∈ U ↔ t ∉ Set.range (cs6J jj)) :
    ∀ t : Fin 6, e6 t ∈ S ↔ t ∉ Set.range (cs6J jj) := by
  have hmem : ∀ t : Fin 6, e6 t ∈ S ↔ t ∈ S.image e6.symm := by
    intro t
    constructor
    · intro hh
      exact Finset.mem_image.mpr ⟨e6 t, hh, by simp⟩
    · intro hh
      rcases Finset.mem_image.mp hh with ⟨a, ha, hae⟩
      rw [← hae, Equiv.apply_symm_apply]
      exact ha
  intro t
  rw [hmem t, h]
  exact hcheck t

theorem cs6_Kdata {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    (e6 : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e6)
    (hS2 : S.card = 2) (hΛa : Nat.card Λa = 1) (hdel : GGDeletedConnectedS ML S)
    (hWMK : GGIsWeylMatrix MK) (hCKK : GGIntCartan MK CK)
    (hKL : ∀ i j : {i : Λ // i ∉ S},
      ((CK (Sum.inl i) (Sum.inl j) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (e6.symm i) (e6.symm j) : ℤ) : ZMod 3)) :
    ∃ (jj : Fin 5) (pi : Nat) (a0 : Λa) (τ : Fin 4 → {i : Λ // i ∉ S}),
      (∀ i, (τ i : Λ) = e6 (cs6J jj i)) ∧ (∀ a : Λa, a = a0) ∧ pi < cs6NumPat jj ∧
      (∀ i : Fin 4,
        ((CK (Sum.inl (τ i)) (Sum.inr a0) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).1 ∧
        ((CK (Sum.inr a0) (Sum.inl (τ i)) : ℤ) : ZMod 3) = (cs6PatPair jj pi i).2) ∧
      Nat.card MK.Group ≤ 3840 ∧ (cs6PatDet jj pi = 6 → Nat.card MK.Group ≤ 720) := by
  classical
  rcases ggDeletedConnectedS_E6_deletion_image e6 hML hS2 hdel with h | h | h | h | h
  · refine ⟨4, cs6_Kdata_body e6 hΛa hWMK hCKK hKL 4 ?_⟩
    exact cs6_hsurv_of_eq e6 4 ({0, 1} : Finset (Fin 6)) h (by decide +kernel)
  · refine ⟨3, cs6_Kdata_body e6 hΛa hWMK hCKK hKL 3 ?_⟩
    exact cs6_hsurv_of_eq e6 3 ({0, 2} : Finset (Fin 6)) h (by decide +kernel)
  · refine ⟨2, cs6_Kdata_body e6 hΛa hWMK hCKK hKL 2 ?_⟩
    exact cs6_hsurv_of_eq e6 2 ({0, 5} : Finset (Fin 6)) h (by decide +kernel)
  · refine ⟨1, cs6_Kdata_body e6 hΛa hWMK hCKK hKL 1 ?_⟩
    exact cs6_hsurv_of_eq e6 1 ({1, 5} : Finset (Fin 6)) h (by decide +kernel)
  · refine ⟨0, cs6_Kdata_body e6 hΛa hWMK hCKK hKL 0 ?_⟩
    exact cs6_hsurv_of_eq e6 0 ({4, 5} : Finset (Fin 6)) h (by decide +kernel)

end CFSG.StandardType
