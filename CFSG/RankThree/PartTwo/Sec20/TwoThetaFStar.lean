module

public import CFSG.RankThree.PartTwo.Sec20.TwoThetaStatement
public import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofNonsolv
import CFSG.RankThree.PartTwo.Sec20.TwoThetaNorm
import CFSG.RankThree.PartTwo.Sec20.TwoThetaPCore
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofComp
import CFSG.GroupTheory.ConjActionModPCore
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace TwoTheta

section Layer


variable {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ] {Y : Type} [Group Y] [Finite Y]

theorem stabilizes_component
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) (hK : CFSG.IsKGroup Y)
    (h3 : ¬ 3 ∣ Nat.card Y) (h2 : CFSG.pCore 2 Y = ⊥)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 2) (φ : Λ →* MulAut Y) {K : Subgroup Y}
    (hKc : IsComponent K) (g : Λ) : K.map (φ g).toMonoidHom = K := by
  have hcomp : ∀ K' : Subgroup Y, IsComponent K' →
      Subgroup.center K' = ⊥ ∧ 5 ∣ Nat.card K' := fun K' hK' =>
    ⟨(CFSG.RankThree.PartTwo.Sec16.suzuki_component_facts hK h3 h2 hK').1,
      (CFSG.RankThree.PartTwo.Sec16.suzuki_component_facts hK h3 h2 hK').2.1⟩
  open scoped Pointwise in
  let T : Subgroup Λ := (MulAction.stabilizer (MulAut Y) K).comap φ
  have hmem : ∀ x, x ∈ T ↔ K.map (φ x).toMonoidHom = K := fun x => by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  have hT : T = ⊤ := eq_top_of_threeElements_subset e (by
    rintro x ⟨k, hk⟩
    rw [SetLike.mem_coe, hmem]
    exact CFSG.RankThree.PartTwo.Sec16.Comp167.map_eq_of_isComponent h5 hcomp (n := k)
      (by rw [← map_pow, hk, map_one]) hKc)
  exact (hmem g).mp (hT ▸ Subgroup.mem_top g)

theorem fixes_component
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) (hK : CFSG.IsKGroup Y)
    (h3 : ¬ 3 ∣ Nat.card Y) (h2 : CFSG.pCore 2 Y = ⊥)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 2) (φ : Λ →* MulAut Y) {K : Subgroup Y}
    (hKc : IsComponent K) (g : Λ) : ∀ x ∈ K, φ g x = x := by
  have hinv := stabilizes_component e hK h3 h2 h5 φ hKc
  obtain ⟨hZ, -, hout⟩ := CFSG.RankThree.PartTwo.Sec16.suzuki_component_facts hK h3 h2 hKc
  set ρ := Res5.restrictAut φ K hinv with hρ
  have hinner : ∀ l : Λ, ρ l ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    intro l
    have h1 : (⊤ : Subgroup Λ).map ρ = ⁅(⊤ : Subgroup Λ).map ρ, (⊤ : Subgroup Λ).map ρ⁆ := by
      rw [← Subgroup.map_commutator]
      congr 1
      exact (Group.IsPerfect.commutator_eq_top (G := Λ)).symm
    have h2 : ρ l ∈ (⊤ : Subgroup Λ).map ρ := ⟨l, Subgroup.mem_top l, rfl⟩
    rw [h1] at h2
    exact hout (Subgroup.commutator_mono le_top le_top h2)
  have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : x ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun σ : MulAut ↥K => σ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [hZ] at hxc
    exact hxc
  set ψ : Λ →* ↥K := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (ρ.codRestrict _ hinner) with hψ
  have h3K : ¬ 3 ∣ Nat.card K := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card K))
  have hrK : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 1 := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_eq_zero_of_not_dvd 3 Nat.prime_three h3K]
    exact Nat.zero_le _
  have hψ1 := Res5.hom_eq_one_of_l34 e hrK ψ
  have hρg : ρ g = 1 := by
    have h3' := congrArg (fun f : Λ →* ↥K => f g) hψ1
    simp only [hψ, MonoidHom.comp_apply, MonoidHom.one_apply, MulEquiv.coe_toMonoidHom] at h3'
    have h4 : ρ.codRestrict _ hinner g = 1 :=
      (MonoidHom.ofInjective hinj).symm.injective (h3'.trans (map_one _).symm)
    exact congrArg Subtype.val h4
  intro x hx
  have h5' : ρ g ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hρg]; rfl
  exact (Res5.restrictAut_apply φ K hinv g ⟨x, hx⟩).symm.trans (congrArg Subtype.val h5')

theorem fixes_layer
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) (hK : CFSG.IsKGroup Y)
    (h3 : ¬ 3 ∣ Nat.card Y) (h2 : CFSG.pCore 2 Y = ⊥)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 2) (φ : Λ →* MulAut Y) (g : Λ) :
    ∀ x ∈ CFSG.layer Y, φ g x = x := by
  have hle : CFSG.layer Y ≤ (φ g).toMonoidHom.eqLocus (MonoidHom.id Y) :=
    sSup_le fun K hKc y hy => fixes_component e hK h3 h2 h5 φ hKc g y hy
  exact fun x hx => hle hx

end Layer

section Main

variable {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ] {Y : Type} [Group Y] [Finite Y]

theorem fixes_fittingSubgroup
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) (h3 : ¬ 3 ∣ Nat.card Y)
    (h2 : CFSG.pCore 2 Y = ⊥)
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2)
    (φ : Λ →* MulAut Y) (g : Λ) : ∀ x ∈ fittingSubgroup Y, φ g x = x := by
  have hle : fittingSubgroup Y ≤ (φ g).toMonoidHom.eqLocus (MonoidHom.id Y) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun ⟨p, hp⟩ => ?_
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    by_cases hp2 : p = 2
    · subst hp2
      simp [h2]
    · have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpd)
      exact fun y hy => fixes_pCore e hpp (Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3)
        (hrank p hpp (Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3)) φ g y hy
  exact fun x hx => hle hx


section Certificates


theorem eq_one_of_threePrime
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) (hK : CFSG.IsKGroup Y)
    (h3 : ¬ 3 ∣ Nat.card Y) (h2 : CFSG.pCore 2 Y = ⊥)
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2)
    (φ : Λ →* MulAut Y) : φ = 1 := by
  have h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 2 := hrank 5 (by norm_num) le_rfl
  have hFfix : ∀ g : Λ, ∀ f ∈ CFSG.generalizedFitting Y, φ g f = f := by
    intro g f hf
    have hle : CFSG.generalizedFitting Y ≤ (φ g).toMonoidHom.eqLocus (MonoidHom.id Y) :=
      sup_le (fun x hx => fixes_fittingSubgroup e h3 h2 hrank φ g x hx)
        (fun x hx => fixes_layer e hK h3 h2 h5 φ g x hx)
    exact hle hf
  have hcomm : ∀ a b : Λ, φ a * φ b = φ b * φ a := fun a b =>
    Res5.commute_of_fix_generalizedFitting (hFfix a) (hFfix b)
  have : IsMulCommutative ↥φ.range := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : MulAut Y) * y = y * x
    rw [← ha, ← hb]
    exact hcomm a b
  have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative
    φ.rangeRestrict
  ext g y
  have h2 := congrArg (fun f : Λ →* ↥φ.range => ((f g : ↥φ.range) : MulAut Y) y) h1
  exact h2


end Certificates

end Main

end TwoTheta

section Certificates



theorem kF207ThetaTwo : KF207ThetaTwo := by
  intro G _ _ Θ L hΘK h3 hrank hLΘ hLL ⟨e⟩
  haveI : Group.IsPerfect ↥L := by
    refine ⟨?_⟩
    apply Subgroup.map_injective L.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hLL]
  have h3Θ : ¬ 3 ∣ Nat.card Θ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3
  have hKY : CFSG.IsKGroup (↥Θ ⧸ CFSG.pCore 2 ↥Θ) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hΘK _
  have h2Y : CFSG.pCore 2 (↥Θ ⧸ CFSG.pCore 2 ↥Θ) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have h3Y : ¬ 3 ∣ Nat.card (↥Θ ⧸ CFSG.pCore 2 ↥Θ) := fun h =>
    h3Θ (h.trans (Subgroup.card_quotient_dvd_card _))
  have hrankY : ∀ p : ℕ, p.Prime → 5 ≤ p →
      CFSG.Open.pRank p (⊤ : Subgroup (↥Θ ⧸ CFSG.pCore 2 ↥Θ)) ≤ 2 := by
    intro p hp hp5
    haveI : Fact p.Prime := ⟨hp⟩
    have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥Θ) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Θ))
      intro hd
      rw [hk] at hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
      omega
    rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥Θ) hN,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Θ]
    exact hrank p hp hp5
  set φ := CFSG.GroupTheory.conjModPCore 2 Θ L hLΘ with hφ
  have hφ1 : φ = 1 := TwoTheta.eq_one_of_threePrime e hKY h3Y h2Y hrankY φ
  have hker : φ.ker.map L.subtype = L := by
    rw [hφ1, MonoidHom.ker_one, Subgroup.map_top, Subgroup.range_subtype]
  have hLle : L ≤ φ.ker.map L.subtype := hker.ge
  have := (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 Θ L L hLΘ le_rfl).mp hLle
  rwa [Subgroup.commutator_comm] at this


end Certificates

end CFSG.RankThree.PartTwo.Sec20
