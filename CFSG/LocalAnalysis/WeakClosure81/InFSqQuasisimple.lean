module

public import CFSG.LocalAnalysis.WeakClosure81.InFSqAlmostSimple
public import CFSG.GroupTheory.PCore.InfPCoreOf

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_inFSq_zero_of_perfect_bar2 {H X : Subgroup G}
    (hXH : X ≤ H) (hperf : Group.IsPerfect (Bar2 X)) (hnt : Nontrivial (Bar2 X)) :
    ¬ InFSq 0 H := by
  classical
  let πH : ↥H →* Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let φ : ↥X →* Bar2 H := πH.comp (Subgroup.inclusion hXH)
  let K : Subgroup (Bar2 H) := φ.range
  have hker : φ.ker = (X ⊓ pCoreOf 2 H).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx' : Subgroup.inclusion hXH x ∈ CFSG.pCore 2 ↥H :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hXH x)).mp (by simpa [φ, πH] using hx)
      rw [← CFSG.openPCoreOf_subgroupOf 2 H] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    · rintro ⟨-, hx⟩
      apply (QuotientGroup.eq_one_iff (Subgroup.inclusion hXH x)).mpr
      rw [← CFSG.openPCoreOf_subgroupOf 2 H]
      exact Subgroup.mem_subgroupOf.mpr hx
  have hker_le : φ.ker ≤ CFSG.pCore 2 ↥X := by
    rw [hker]
    intro x hx
    have hx' : (x : G) ∈ X ⊓ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hx
    have hx2 : (x : G) ∈ pCoreOf 2 X :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXH hx'
    rw [← CFSG.openPCoreOf_subgroupOf 2 X]
    exact Subgroup.mem_subgroupOf.mpr hx2
  let ψ' : ↥X →* ↥K := φ.rangeRestrict
  let M : Subgroup ↥K := (CFSG.pCore 2 ↥X).map ψ'
  have hψ'surj : Function.Surjective ψ' := MonoidHom.rangeRestrict_surjective φ
  have hMn : M.Normal :=
    Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 ↥X).Normal) ψ' hψ'surj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥X →* (↥K ⧸ M) := (QuotientGroup.mk' M).comp ψ'
  have hψker : ψ.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : ψ' x ∈ M := (QuotientGroup.eq_one_iff (ψ' x)).mp hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
      have hd : x * y⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have hval : φ x = φ y := by
          have h2 : (ψ' y : Bar2 H) = (ψ' x : Bar2 H) := congrArg Subtype.val hxy
          exact h2.symm
        rw [map_mul, map_inv, hval, mul_inv_cancel]
      have hdle := hker_le hd
      have : x = (x * y⁻¹) * y := by group
      rw [this]
      exact (CFSG.pCore 2 ↥X).mul_mem hdle hy
    · intro hx
      have hx' : ψ' x ∈ M := ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff (ψ' x)).mpr hx'
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective M).comp hψ'surj
  have hiso : Nonempty ((↥K ⧸ M) ≃* Bar2 X) := by
    let e1 : (↥X ⧸ ψ.ker) ≃* (↥K ⧸ M) :=
      QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj
    let e2 : Bar2 X ≃* (↥X ⧸ ψ.ker) :=
      (QuotientGroup.quotientMulEquivOfEq hψker).symm
    exact ⟨e1.symm.trans e2.symm⟩
  have hXeven : 2 ∣ Nat.card (Bar2 X) := by
    by_contra hodd
    have hodd' : Odd (Nat.card (Bar2 X)) := Nat.odd_iff.mpr (by omega)
    exact Group.IsPerfect.not_isSolvable (Bar2 X)
      (CFSG.FeitThompson.isSolvable_of_odd_natCard (G := Bar2 X) hodd')
  have hKnot2 : ¬ IsPGroup 2 ↥K := by
    intro hK2
    have hquot : IsPGroup 2 (↥K ⧸ M) :=
      IsPGroup.of_surjective hK2 (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
    obtain ⟨e⟩ := hiso
    have hX2 : IsPGroup 2 (Bar2 X) := IsPGroup.of_equiv hquot e
    exact Group.IsPerfect.not_isNilpotent (Bar2 X) hX2.isNilpotent
  have hKeven : 2 ∣ Nat.card ↥K := by
    have hcard : Nat.card ↥K = Nat.card (↥K ⧸ M) * Nat.card ↥M :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup M
    rw [hcard]
    obtain ⟨e⟩ := hiso
    have h2 : 2 ∣ Nat.card (↥K ⧸ M) := by
      rw [Nat.card_congr e.toEquiv]
      exact hXeven
    exact dvd_mul_of_dvd_left h2 _
  have hnot2 : ¬ IsPGroup 2 (Bar2 H) := by
    intro hbar
    have hbar' : IsPGroup 2 (↥(⊤ : Subgroup (Bar2 H))) :=
      IsPGroup.of_equiv hbar (Subgroup.topEquiv).symm
    exact hKnot2 (hbar'.to_le (le_top : K ≤ ⊤))
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 hKeven
  have ha2 : a ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha] at h
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha
    omega
  have hAne : (Subgroup.zpowers a).map K.subtype ≠ ⊥ := by
    intro hbot
    have h1 : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    have h2 : K.subtype a ∈ (Subgroup.zpowers a).map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype h1
    rw [hbot] at h2
    exact ha1 (by simpa using Subgroup.mem_bot.mp h2)
  exact not_inFSq_zero hnot2 ⟨(Subgroup.zpowers a).map K.subtype, hAne,
    (CFSG.Open.isElemAbelian_zpowers (p := 2) ha2).map K.subtype⟩

theorem not_inFSq_zero_of_isQuasisimple_bar2 {H X : Subgroup G} (hXH : X ≤ H)
    (hX : CFSG.Open.IsQuasisimple (Bar2 X)) : ¬ InFSq 0 H := by
  have : IsSimpleGroup (Bar2 X ⧸ Subgroup.center (Bar2 X)) := hX.2
  exact not_inFSq_zero_of_perfect_bar2 hXH (Group.isPerfect_def.mpr hX.1)
    (QuotientGroup.mk'_surjective (Subgroup.center (Bar2 X))).nontrivial

end CFSG.LocalAnalysis.WeakClosure81
