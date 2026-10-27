module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsD3
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem520
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_normalizer_conjClosure_of_le {K T I : Subgroup Γ}
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hKI : K ≤ Subgroup.normalizer (I : Set Γ)) :
    K ≤ Subgroup.normalizer (conjClosure I T : Set Γ) := by
  intro k hk
  apply mem_normalizer_of_forall_conj_mem'
  intro x hx
  have hle : conjClosure I T ≤ (conjClosure I T).comap (MulAut.conj k).toMonoidHom := by
    refine conjClosure_le fun t ht y hy => ?_
    show k * (t * y * t⁻¹) * k⁻¹ ∈ conjClosure I T
    have hk' : t⁻¹ * k * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem ht)) k).mp hk
      simpa using this
    have hy' : (t⁻¹ * k * t) * y * (t⁻¹ * k * t)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hKI hk') y).mp hy
    have e : k * (t * y * t⁻¹) * k⁻¹ =
        t * ((t⁻¹ * k * t) * y * (t⁻¹ * k * t)⁻¹) * t⁻¹ := by group
    rw [e]
    exact mem_conjClosure ht hy'
  exact hle hx

theorem pCoreOf_eq_bot_of_isSimpleGroup {X : Subgroup Γ} [IsSimpleGroup ↥X]
    (hX : ¬ IsPGroup 2 ↥X) : pCoreOf 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pCoreOf 2 X).subgroupOf X) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, pCoreOf_le 2 X hx⟩ : ↥X) ∈ (pCoreOf 2 X).subgroupOf X := hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · exfalso
    apply hX
    intro x
    have hx : (x : Γ) ∈ pCoreOf 2 X := by
      have : x ∈ (pCoreOf 2 X).subgroupOf X := by rw [h]; trivial
      exact this
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨x, hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem two_lt_qhatInt_of_irrPlusIn
    (hD : D310L34Fact) (hB : B45L34Fact) {M K T I : Subgroup Γ}
    (hS : SQTKGroup ↥M) (hT : IsSylowTwoOf T M) (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set Γ)) (hM : M = K ⊔ T)
    (hI : IsIrrPlusIn K (conjClosure I T) T I) (hVT : IsElemAbelian 2 (conjClosure I T))
    (hO2 : pCoreOf 2 (autOn M (conjClosure I T)) = ⊥)
    (hL : LieModel ↥(autOn K (conjClosure I T)) .PSL 3 2 2)
    (hker : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (conjClosure I T : Set Γ)))
    (hdiag : E2.IsDiagramNontrivial T K (T ⊓ K)) :
    (2 : WithTop ℚ) < qhatInt M (conjClosure I T) hVT := by
  by_contra hle
  rw [not_lt] at hle
  have heq : I = conjClosure I T := hD Γ M K T I hS hT hKM hMK hM hI hVT hO2 hL hle
  obtain ⟨-, -, hKI, hcomm, hlt, hirr, -⟩ := hI
  set U := conjClosure I T with hUdef
  have : IsMulCommutative ↥U := hVT.1
  have hTM : T ≤ M := hT.1
  have hTK : T ≤ Subgroup.normalizer (K : Set Γ) := hTM.trans hMK
  have hKU : K ≤ Subgroup.normalizer (U : Set Γ) := le_normalizer_conjClosure_of_le hTK hKI
  have hTU : T ≤ Subgroup.normalizer (U : Set Γ) := le_normalizer_conjClosure I T
  have hMU : M ≤ Subgroup.normalizer (U : Set Γ) := by rw [hM]; exact sup_le hKU hTU
  have hsimple : IsSimpleGroup ↥(autOn K U) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL
  have hcard := card_of_lieModel_L34 hL
  have hZ : Subgroup.center ↥(autOn K U) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_not_prime (by rw [hcard]; norm_num)
  have hquasi : CFSG.IsQuasisimple ↥(autOn K U) := by
    have := isPerfect_of_isSimpleGroup_of_center_eq_bot hZ
    exact isQuasisimple_of_isSimpleGroup_of_isPerfect
  have hO2K : pCoreOf 2 (autOn K U) = ⊥ := by
    refine pCoreOf_eq_bot_of_isSimpleGroup fun hp => ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hcard] at hk
    have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : 7 ∣ 20160)
    exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h7))) (by norm_num)
  have hsec : InternalSec.ISec U M K (Subgroup.centralizer (K : Set Γ)) := by
    refine ⟨hVT.2, hMU, hKM, hMK, ?_, ?_, inf_le_right, ?_, ?_, ?_, hO2K, hquasi⟩
    · intro y hy
      rw [hM] at hy
      have hset : ((K ⊔ T : Subgroup Γ) : Set Γ) = (K : Set Γ) * (T : Set Γ) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK
      have hy' : y ∈ (K : Set Γ) * (T : Set Γ) := by rw [← hset]; exact hy
      obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hy'
      obtain ⟨e, he⟩ := hT.2.1 ⟨t, ht⟩
      have hte : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
      obtain ⟨k', hk', hke⟩ := pow_mul_mem_of_mem_normalizer hk (hTK ht) (2 ^ e)
      refine ⟨e, ?_⟩
      rw [hke, hte, mul_one]
      exact Subgroup.mem_sup_left hk'
    · exact le_normalizer_inf hMU (le_normalizer_centralizer_of_le_normalizer hMK)
    · rw [← heq]; exact hcomm
    · intro hUC
      apply hlt.ne
      rw [← heq] at hUC
      exact inf_eq_left.mpr hUC
    · intro J hJ1 hJ2 hJ3
      rw [← heq] at hJ1 hJ2 ⊢
      exact hirr J hJ1 hJ2 hJ3
  have hSK : SQTKGroup ↥(autOn K U) :=
    InternalSec.sqtkGroup_autOn hKU (InternalSec.sqtkGroup_mono hS hKM) hker
  have h1 := hB Γ U M K T (Subgroup.centralizer (K : Set Γ)) hsec hSK hL hTM hT hM hdiag
  have h2 := hsec.qhatOf_sec_le
  have h3 : qhatOf (autOn M U) ≤ (2 : WithTop ℚ) := hle
  exact absurd (lt_of_lt_of_le h1 (h2.trans h3)) (lt_irrefl _)

end CFSG.Quasithin.H13
