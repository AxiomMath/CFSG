module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP2

variable {G : Type*} [Group G]

@[expose] noncomputable def a7Rep (K : Subgroup G)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) :
    ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7) :=
  let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
        (by norm_num) (by norm_num))
  e.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp
    ((CFSG.pCoreQuotMulAut ↥K).comp K.normalizerMonoidHom))

theorem a7Rep_conj (K : Subgroup G)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (g : ↥(Subgroup.normalizer (K : Set G))) (x : ↥K) :
    ((φ ((⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      a7Rep K φ g * (φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) : Equiv.Perm (Fin 7)) *
        (a7Rep K φ g)⁻¹ := by
  let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
        (by norm_num) (by norm_num))
  have h1 : e (a7Rep K φ g) =
      MulAut.congr φ (CFSG.pCoreQuotMulAut ↥K (K.normalizerMonoidHom g)) := by
    dsimp only [a7Rep]
    exact MulEquiv.apply_symm_apply e _
  have hnorm : K.normalizerMonoidHom g x =
      (⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥K) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have h2 : ((e (a7Rep K φ g)) (φ (x : ↥K ⧸ CFSG.pCore 2 ↥K)) :
      alternatingGroup (Fin 7)) =
      φ ((⟨g * x * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [h1, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, CFSG.pCoreQuotMulAut_mk, hnorm]
  rw [← h2]
  rw [show e (a7Rep K φ g) = MulAut.conjNormal (a7Rep K φ g) from rfl,
    MulAut.conjNormal_apply]

theorem a7Rep_eq_of_conj (K : Subgroup G)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (g : ↥(Subgroup.normalizer (K : Set G))) {σ : Equiv.Perm (Fin 7)}
    (hσ : ∀ x : ↥K,
      ((φ ((⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      σ * (φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) : Equiv.Perm (Fin 7)) * σ⁻¹) :
    a7Rep K φ g = σ := by
  let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
        (by norm_num) (by norm_num))
  apply e.injective
  have h1 : e (a7Rep K φ g) =
      MulAut.congr φ (CFSG.pCoreQuotMulAut ↥K (K.normalizerMonoidHom g)) := by
    dsimp only [a7Rep]
    exact MulEquiv.apply_symm_apply e _
  rw [h1]
  change MulAut.congr φ (CFSG.pCoreQuotMulAut ↥K (K.normalizerMonoidHom g)) =
    MulAut.conjNormal σ
  apply MulEquiv.ext
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm a)
  have ha : φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) = a := by
    rw [hx, MulEquiv.apply_symm_apply]
  rw [← ha]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, CFSG.pCoreQuotMulAut_mk]
  have hnorm : K.normalizerMonoidHom g x =
      (⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥K) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  rw [hnorm]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  exact hσ x

theorem a7Rep_of_mem (K : Subgroup G)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) (x : ↥K) :
    a7Rep K φ ⟨x, Subgroup.le_normalizer x.2⟩ =
      (φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) : Equiv.Perm (Fin 7)) := by
  let g : ↥(Subgroup.normalizer (K : Set G)) := ⟨x, Subgroup.le_normalizer x.2⟩
  change a7Rep K φ g = (φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) : Equiv.Perm (Fin 7))
  apply a7Rep_eq_of_conj K φ g
    (σ := (φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) : Equiv.Perm (Fin 7)))
  intro y
  have hK : (⟨g * y * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.2 y).mp y.2⟩ : ↥K) = x * y * x⁻¹ := by
    apply Subtype.ext
    simp [g]
  have hq : ((⟨g * y * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.2 y).mp y.2⟩ : ↥K) :
      ↥K ⧸ CFSG.pCore 2 ↥K) =
      (x : ↥K ⧸ CFSG.pCore 2 ↥K) * (y : ↥K ⧸ CFSG.pCore 2 ↥K) *
        (x : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹ := by
    rw [hK]
    simp
  rw [hq, map_mul, map_mul, map_inv]
  rfl

theorem a7Rep_eq_one_iff (K : Subgroup G)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (g : ↥(Subgroup.normalizer (K : Set G))) :
    a7Rep K φ g = 1 ↔
      ∀ y ∈ K, (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have h1 : a7Rep K φ g = 1 ↔ ∀ x : ↥K,
      φ ((⟨g * x * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 x).mp x.2⟩ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) =
      φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) := by
    constructor
    · intro h x
      apply Subtype.val_injective
      simpa [h] using a7Rep_conj K φ g x
    · intro h
      apply a7Rep_eq_of_conj K φ g (σ := 1)
      intro x
      simpa using congrArg (fun a : alternatingGroup (Fin 7) =>
        (a : Equiv.Perm (Fin 7))) (h x)
  rw [h1]
  constructor
  · intro h y hy
    let yK : ↥K := ⟨y, hy⟩
    let a : ↥K := ⟨g * yK * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.2 yK).mp yK.2⟩
    have ha : (a : ↥K ⧸ CFSG.pCore 2 ↥K) =
        (yK : ↥K ⧸ CFSG.pCore 2 ↥K) := φ.injective (h yK)
    have hmem : a / yK ∈ CFSG.pCore 2 ↥K :=
      (QuotientGroup.eq_iff_div_mem).mp ha
    have hcoe : ((a / yK : ↥K) : G) =
        (g : G) * y * (g : G)⁻¹ * y⁻¹ := by
      simp [a, yK, div_eq_mul_inv, mul_assoc]
    rw [← hcoe]
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) (a / yK)).mpr hmem
  · intro h yK
    let a : ↥K := ⟨g * yK * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.2 yK).mp yK.2⟩
    have hmemG : (g : G) * (yK : G) * (g : G)⁻¹ * (yK : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 K := h (yK : G) yK.2
    have hmem : a / yK ∈ CFSG.pCore 2 ↥K := by
      refine (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) (a / yK)).mp ?_
      simpa [a, div_eq_mul_inv, mul_assoc] using hmemG
    exact congrArg φ ((QuotientGroup.eq_iff_div_mem).mpr hmem)

end CFSG.RankThree.PartTwo.KFacts.KP2

end
