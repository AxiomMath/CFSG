module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Family
public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Position
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainRoots
public import CFSG.RankThree.PartTwo.Sec21.FF81F4L3
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.RankThree.PartTwo.Sec21.FF81 CFSG.LieType.Universal

section HasAmalgam


theorem hasLeviAmalgam_of_injective {G : Type} [Group G]
    (ψ : F42.K →* G) (hψ : Function.Injective ψ) : HasLeviAmalgam F42 ↥ψ.range := by
  let Ψ : F42.K ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  have hΨ : Function.Injective Ψ.toMonoidHom := Ψ.injective
  refine ⟨fun J => (F42.D.leviAmalgam J).map Ψ.toMonoidHom,
    fun J => (F42.D.leviAmalgam J).equivMapOfInjective Ψ.toMonoidHom hΨ, ?_, ?_⟩
  · have hgen : ⨆ J, F42.D.leviAmalgam J = ⊤ :=
      CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
        (CFSG.LieType.RootSystem.isCTRootSystem F42.D.isFiniteType F42.D.divisible)
        (Adjoint.f4_isCTGroupDatum (GaloisField 2 1))
    show ⨆ J, (F42.D.leviAmalgam J).map Ψ.toMonoidHom = ⊤
    rw [← Subgroup.map_iSup, hgen]
    exact Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective
  · intro I J _ x y hxy
    exact congrArg Ψ hxy

end HasAmalgam

section Cen3

open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.StandardType.TableBF4TwoInputs (card_C3Levi_two)


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_cen_ge_of_mem_rootSL2 (hK : Nat.card K = 2) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {y : ↥(adjointGroup .F4 K)} (hy : y ∈ rootSL2 K γ) (hy3 : orderOf y = 3) :
    3 * 1451520 ≤ Nat.card ↥(Subgroup.centralizer ({y} : Set ↥(adjointGroup .F4 K))) := by
  have hfin := finite_adjointGroup_F4 (K := K)
  have hcyc : IsCyclic (Subgroup.zpowers y) := Subgroup.isCyclic_zpowers y
  have hYJ : Subgroup.zpowers y ≤ rootSL2 K γ := Subgroup.zpowers_le.2 hy
  have hY : Nat.card (Subgroup.zpowers y) = Nat.card K + 1 := by
    rw [Nat.card_zpowers, hy3, hK]
  obtain ⟨e⟩ := nonempty_perfectCore_centralizer_of_le_rootSL2 hγ hYJ hcyc hY
  set Z := Subgroup.centralizer ((Subgroup.zpowers y : Subgroup ↥(adjointGroup .F4 K)) :
    Set ↥(adjointGroup .F4 K)) with hZ
  set core := perfectCore Z with hcore
  have hcoreZ : core ≤ Z := perfectCore_le Z
  have hcard : Nat.card ↥core = 1451520 := by
    rw [Nat.card_congr e.toEquiv, card_C3Levi_two hK]
  have hYZ : Subgroup.zpowers y ≤ Z := le_centralizer_self_of_isCyclic hcyc
  have hdisj : Subgroup.zpowers y ⊓ core = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzY, hzc⟩ := Subgroup.mem_inf.1 hz
    have hcen : (⟨z, hzc⟩ : ↥core) ∈ Subgroup.center ↥core := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hc : (c : ↥(adjointGroup .F4 K)) ∈ Z := hcoreZ c.2
      have := Subgroup.mem_centralizer_iff.1 hc z hzY
      exact Subtype.ext this.symm
    have h1 : e ⟨z, hzc⟩ ∈ Subgroup.center ↥(C3Levi K) := by
      rw [← Subgroup.map_center_eq e]
      exact Subgroup.mem_map_of_mem _ hcen
    rw [center_C3Levi_eq_bot, Subgroup.mem_bot] at h1
    have h2 : (⟨z, hzc⟩ : ↥core) = 1 := e.injective (h1.trans (map_one e).symm)
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val h2)
  have hcomm : core ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup ↥(adjointGroup .F4 K)) :
      Set ↥(adjointGroup .F4 K)) := hcoreZ
  have hsup := card_sup_eq_mul_of_le_centralizer (A := Subgroup.zpowers y) (B := core) hcomm hdisj
  have hle : Subgroup.zpowers y ⊔ core ≤
      Subgroup.centralizer ({y} : Set ↥(adjointGroup .F4 K)) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((Commute.refl y).zpow_left k).eq
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hcoreZ hx) y (Subgroup.mem_zpowers y)).symm
  have := Subgroup.card_le_of_le hle
  rw [hsup, Nat.card_zpowers, hy3, hcard] at this
  exact this

end Cen3

section Cen2

open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)
open CFSG.RankThree.PartTwo.Sec21.FF81.F4 (rootElt card_cen_rootElt orderOf_rootElt card_cen_isConj)
open CFSG.RankThree.PartTwo.Sec21.FF79 (conjBy IsSylowOf)
open CFSG.RankThree.PartTwo.Sec21.FF79.L41 (exists_conjBy_eq_sylowOf isSylowOf_of_card_p)
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8 (f4Rep coe_f4Rep_singleton)
open CFSG.LieType.Chevalley (rootOperatorFamily f4_isRoot_pos)
open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_cen_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have h : Subgroup.centralizer ({e x} : Set H) =
      (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hz]
  rw [h, Subgroup.card_map_of_injective e.injective]

omit [Finite K] [CharP K 2] in
theorem pinnedFamilySign_cast_one' {K : Type} [Field K] [CharP K 2]
    (γ : Fin (Tag.rank .F4) → ℤ) :
    ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : K)) = 1 := by
  have h := (rootOperatorFamily .F4).pinnedFamilySign_mul_self K γ
  have h2 : (((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : K) + 1 = 0 := by
    have : ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : K) + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, sq, h, one_pow, one_add_one_eq_two]; exact CharTwo.two_eq_zero
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact CharTwo.add_eq_zero.1 h2

theorem f4Par_one_eq_rootElt (i : Fin 24) :
    Adjoint.f4Par (ZMod 2) (orbitCertRoot .F4 (24 + i)) 1 = rootElt i := by
  have hγ : IsRoot .F4 (orbitCertRoot .F4 (24 + i)) :=
    (f4_isRoot_pos (i := 24 + (i : ℕ)) ⟨Nat.le_add_right _ _, by omega⟩).1
  apply Subtype.ext
  rw [coe_f4Par_eq_pinnedX hγ, pinnedFamilySign_cast_one', one_mul]
  show _ = (f4Rep (ZMod 2) [24 + (i : ℕ)] : ModGL .F4 (ZMod 2))
  rw [coe_f4Rep_singleton]
  rfl

theorem congr_f4Par_one (ζ : K ≃+* ZMod 2) (i : Fin 24) :
    CFSG.TauCetiBridge.adjointGroupCongr ζ (Adjoint.f4Par K (orbitCertRoot .F4 (24 + i)) 1) =
      rootElt i := by
  rw [← f4Par_one_eq_rootElt]
  apply Subtype.ext
  have h := baseChangeGL_f4Par (ζ : K →+* ZMod 2) (orbitCertRoot .F4 (24 + i)) 1
  rw [map_one] at h
  exact h

theorem card_cen_f4Par_one (ζ : K ≃+* ZMod 2) (i : Fin 24) :
    Nat.card ↥(Subgroup.centralizer
      ({Adjoint.f4Par K (orbitCertRoot .F4 (24 + i)) 1} : Set ↥(adjointGroup .F4 K))) =
      2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  have h1 := card_cen_equiv (CFSG.TauCetiBridge.adjointGroupCongr ζ)
    (Adjoint.f4Par K (orbitCertRoot .F4 (24 + i)) 1)
  rw [congr_f4Par_one] at h1
  rw [← h1]
  exact card_cen_rootElt i

theorem exists_conj_involution_rootSL2 (hK : Nat.card K = 2) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {u x : ↥(adjointGroup .F4 K)} (hu : u ∈ rootSL2 K γ)
    (hx : x ∈ rootSL2 K γ) (hu2 : orderOf u = 2) (hx2 : orderOf x = 2) :
    ∃ g ∈ rootSL2 K γ, g * x * g⁻¹ = u := by
  have hfin := finite_adjointGroup_F4 (K := K)
  have h6 := card_rootSL2 hK hγ
  have hS : ∀ y ∈ rootSL2 K γ, orderOf y = 2 →
      IsSylowOf 2 (Subgroup.zpowers y) (rootSL2 K γ) := by
    intro y hy hy2
    refine isSylowOf_of_card_p (p := 2) (Subgroup.zpowers_le.2 hy) ?_
    rw [Nat.card_zpowers, hy2, h6]
    have : (6 : ℕ).factorization 2 = 1 := by
      have h := Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by norm_num : (6 : ℕ) ≠ 0)
        (by norm_num : 2 ∣ 6)
      have h2 : ¬ 2 ^ 2 ∣ 6 := by norm_num
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num : (6 : ℕ) ≠ 0)
        (k := 2))
      omega
    rw [this]
    norm_num
  obtain ⟨k, hk, hkx⟩ := exists_conjBy_eq_sylowOf (hS u hu hu2) (hS x hx hx2)
  refine ⟨k, hk, ?_⟩
  have hw : k * x * k⁻¹ ∈ Subgroup.zpowers u := by
    rw [← hkx]
    exact ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
  have hw2 : orderOf (k * x * k⁻¹) = 2 := by
    rw [← hx2]
    exact (orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective x)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [← zpow_mod_orderOf, hu2] at hj
  have hj2 : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hj2 with h0 | h1
  · rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h0, zpow_zero] at hj
    rw [← hj, orderOf_one] at hw2
    omega
  · rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h1, zpow_one] at hj
    exact hj.symm

theorem simple_root_pos : ∀ j : Fin (Tag.rank .F4), ∃ i : Fin 24,
    orbitCertRoot .F4 (24 + i) = Pi.single j 1 := by
  decide +kernel

theorem Lv_eq_rootSL2 (j : Fin (Tag.rank .F4)) : Lv K {j} = rootSL2 K (Pi.single j 1) := by
  unfold Lv
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  unfold CFSG.LieType.CurtisTits.rankOne
  exact (rootSL2_eq_sup (isRoot_single _ j)).symm

theorem card_cen_involution_of_mem_Lv (ζ : K ≃+* ZMod 2) (hK : Nat.card K = 2)
    {j : Fin (Tag.rank .F4)} {u : ↥(adjointGroup .F4 K)} (hu : u ∈ Lv K {j})
    (hu2 : orderOf u = 2) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set ↥(adjointGroup .F4 K))) =
      2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  obtain ⟨i, hi⟩ := simple_root_pos j
  have hγ : IsRoot .F4 (Pi.single j 1) := isRoot_single _ j
  rw [Lv_eq_rootSL2] at hu
  have hxJ : Adjoint.f4Par K (Pi.single j 1) 1 ∈ rootSL2 K (Pi.single j 1) := by
    rw [rootSL2_eq_sup hγ]
    exact Subgroup.mem_sup_left (Adjoint.xPar_mem hγ 1)
  have hx2 : orderOf (Adjoint.f4Par K (Pi.single j 1) 1) = 2 := by
    have h := congr_f4Par_one ζ i
    rw [hi] at h
    rw [← orderOf_injective (CFSG.TauCetiBridge.adjointGroupCongr ζ).toMonoidHom
      (CFSG.TauCetiBridge.adjointGroupCongr ζ).injective]
    exact (congrArg orderOf h).trans (orderOf_rootElt i)
  obtain ⟨g, -, hgx⟩ := exists_conj_involution_rootSL2 hK hγ hu hxJ hu2 hx2
  rw [← card_cen_isConj (isConj_iff.2 ⟨g, hgx⟩), ← hi]
  exact card_cen_f4Par_one ζ i

end Cen2

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
