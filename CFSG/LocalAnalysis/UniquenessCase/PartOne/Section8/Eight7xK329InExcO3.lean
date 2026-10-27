module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
import CFSG.ClassicalGroups.PCoreSection
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour
import CFSG.GH74.GLS.IVK.Proofs2.Ivk41R
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

private theorem k329inudat_normalizer_le_normalizer_pCoreOf {G : Type*} [Group G]
    (M : Subgroup G) :
    Subgroup.normalizer (M : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 3 M : Set G) := by
  have hmap_le : ∀ g ∈ Subgroup.normalizer (M : Set G),
      (CFSG.Open.pCoreOf 3 M).map (MulAut.conj g).toMonoidHom ≤ CFSG.Open.pCoreOf 3 M := by
    intro g hg
    have hconj : ∀ x : G, (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := fun _ => rfl
    have hfix : M.map (MulAut.conj g).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf ?_ ?_ ?_
    · calc (CFSG.Open.pCoreOf 3 M).map (MulAut.conj g).toMonoidHom
          ≤ M.map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 3 M)
        _ = M := hfix
    · intro x hx y hy
      obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hy
      have hz : g⁻¹ * x * g ∈ M := by
        have hgi := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
        exact hgi (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]; exact hx)
      refine Subgroup.mem_map.mpr
        ⟨(g⁻¹ * x * g) * o * (g⁻¹ * x * g)⁻¹,
          CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hz ho, ?_⟩
      simp only [hconj]
      group
    · exact (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 3 M).map _
  intro g hg
  have hconj : ∀ x : G, (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := fun _ => rfl
  rw [Subgroup.mem_normalizer_iff]
  intro o
  refine ⟨fun ho => ?_, fun h => ?_⟩
  · have ho' := hmap_le g hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ho)
    rwa [hconj o] at ho'
  · have hmem := hmap_le g⁻¹ ((Subgroup.normalizer (M : Set G)).inv_mem hg)
      (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom h)
    have hconj' : ∀ x : G, (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * (g⁻¹)⁻¹ :=
      fun _ => rfl
    rw [hconj'] at hmem
    rwa [show g⁻¹ * (g * o * g⁻¹) * (g⁻¹)⁻¹ = o from by group] at hmem

theorem k329in_udatum_normal_three (S : Type) [Group S] [Finite S] (u : S)
    (hu : K329UDatum S u) :
    ∃ N : Subgroup S, N ≤ Subgroup.centralizer ({u} : Set S) ∧
      (N.subgroupOf (Subgroup.centralizer ({u} : Set S))).Normal ∧ IsPGroup 3 N ∧
        ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
  unfold K329UDatum at hu
  obtain ⟨-, M, N₀, hMC, hMn, hN₀M, hN₀n, hN₀p, a, ha, b, hb, hab⟩ := hu
  have hN₀n' : ∀ x ∈ M, ∀ y ∈ N₀, x * y * x⁻¹ ∈ N₀ :=
    fun x hx y hy => (Subgroup.normal_subgroupOf_iff hN₀M).mp hN₀n y x hy hx
  have hN₀le : N₀ ≤ CFSG.Open.pCoreOf 3 M :=
    CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hN₀M hN₀n' hN₀p
  have hCM : Subgroup.centralizer ({u} : Set S) ≤ Subgroup.normalizer (M : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMC).mp hMn
  refine ⟨CFSG.Open.pCoreOf 3 M, (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 3 M).trans hMC,
    ?_, CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 3 M, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 3 M).trans hMC)).mpr
      (hCM.trans (k329inudat_normalizer_le_normalizer_pCoreOf M))
  · exact ⟨a, hN₀le ha, b, hN₀le hb, hab⟩

private def k329inog2_Q (Γ : Type) [Group Γ] (z : Γ) : Prop :=
  ∀ M : Subgroup ↥(Subgroup.centralizer ({z} : Set Γ)),
    M.Normal → IsPGroup 3 ↥M → ∀ a b : M, a * b = b * a

private theorem k329inog2_Q_of_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ']
    (e : Γ ≃* Γ') (z : Γ) (h : k329inog2_Q Γ' (e z)) : k329inog2_Q Γ z := by
  intro M hMn hM3
  let C : Subgroup Γ := Subgroup.centralizer ({z} : Set Γ)
  let C' : Subgroup Γ' := Subgroup.centralizer ({e z} : Set Γ')
  have hCmap : C.map (e : Γ →* Γ') = C' := by
    apply le_antisymm
    · simpa [C, C', Set.image_singleton] using
        Subgroup.map_centralizer_le_centralizer_image ({z} : Set Γ) (e : Γ →* Γ')
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  let eC : ↥C ≃* ↥C' := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hCmap)
  have hMn' : (M.map (eC : ↥C →* ↥C')).Normal := hMn.map _ eC.surjective
  have hM3' : IsPGroup 3 ↥(M.map (eC : ↥C →* ↥C')) := hM3.of_equiv (eC.subgroupMap M)
  have key := h (M.map (eC : ↥C →* ↥C')) hMn' hM3'
  intro a b
  refine (eC.subgroupMap M).injective ?_
  rw [map_mul, map_mul]
  exact key _ _

private theorem k329inog2_P_of_Q {Γ : Type} [Group Γ] (z : Γ) (h : k329inog2_Q Γ z) :
    ∀ N : Subgroup Γ, N ≤ Subgroup.centralizer ({z} : Set Γ) →
      (N.subgroupOf (Subgroup.centralizer ({z} : Set Γ))).Normal →
      IsPGroup 3 N → ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  intro N hN hNn hN3 a ha b hb
  let C : Subgroup Γ := Subgroup.centralizer ({z} : Set Γ)
  let M : Subgroup ↥C := N.subgroupOf C
  have hMn : M.Normal := hNn
  have hM3 : IsPGroup 3 ↥M := by
    refine hN3.of_injective
      { toFun := fun x => ⟨x.1.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl } ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥N => (t : Γ)) hxy))
  have hkey := h M hMn hM3
  have := hkey ⟨⟨a, hN ha⟩, ha⟩ ⟨⟨b, hN hb⟩, hb⟩
  simpa using congrArg (fun x : ↥M => x.1.1) this

private theorem k329inog2_Q_of_isQuasisimple_centralizer {A : Type} [Group A] [Finite A]
    (z : A) (hQ : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({z} : Set A))) (hz1 : z ≠ 1) :
    k329inog2_Q A z := by
  have hQO : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({z} : Set A)) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hQ
  intro M hMn hM3
  have hMne : M ≠ ⊤ := by
    intro hMtop
    have hQ3 : IsPGroup 3 ↥(Subgroup.centralizer ({z} : Set A)) := by
      have htop : IsPGroup 3 ↥(⊤ : Subgroup ↥(Subgroup.centralizer ({z} : Set A))) :=
        hMtop ▸ hM3
      exact htop.of_equiv Subgroup.topEquiv
    have : Nontrivial ↥(Subgroup.centralizer ({z} : Set A)) := by
      refine ⟨⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, 1, ?_⟩
      intro hh
      exact hz1 (congrArg Subtype.val hh)
    have : Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set A)) := hQ.1
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact Group.IsPerfect.not_isNilpotent _ (hQ3.isNilpotent)
  have hc := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hQO M hMne
  intro a b
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hc a.2) b).symm)

private theorem k329inog2_Q_of_longGroup {A : Type} [Group A]
    {z : A} {S0 : Subgroup A}
    (hS0C : S0 ≤ Subgroup.centralizer ({z} : Set A))
    (hBC1 : ∀ x ∈ Subgroup.centralizer ({z} : Set A),
      ∀ y ∈ Subgroup.centralizer ({z} : Set A), x * y * x⁻¹ * y⁻¹ ∈ S0)
    (hS0simple : IsSimpleGroup ↥S0)
    (hnot3 : ¬ IsPGroup 3 ↥S0) :
    k329inog2_Q A z := by
  intro M hMn hM3
  let C : Subgroup A := Subgroup.centralizer ({z} : Set A)
  let N : Subgroup A := M.map C.subtype
  have hNC : N ≤ C := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hNm : N.subgroupOf C = M := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmx⟩
      have : m = x := Subtype.ext hmx
      rwa [this] at hm
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hNn : (N.subgroupOf C).Normal := by rw [hNm]; exact hMn
  have hN3 : IsPGroup 3 ↥N := hM3.of_surjective
    { toFun := fun x => ⟨C.subtype x.1, ⟨x.1, x.2, rfl⟩⟩, map_one' := rfl,
      map_mul' := fun _ _ => rfl } (by
        rintro ⟨y, hy⟩
        obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨m, hm⟩, rfl⟩)
  have hNconj : ∀ h k, h ∈ N → k ∈ C → k * h * k⁻¹ ∈ N :=
    (Subgroup.normal_subgroupOf_iff hNC).mp hNn
  have hM'norm : ((N ⊓ S0).subgroupOf S0).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact ⟨hNconj h k hh.1 (hS0C hk),
      S0.mul_mem (S0.mul_mem hk hh.2) (S0.inv_mem hk)⟩
  have hM' : N ⊓ S0 = ⊥ := by
    rcases hM'norm.eq_bot_or_eq_top with hbot | htop
    · have := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ S0 ≤ S0)
      rw [hbot, Subgroup.map_bot] at this
      exact this.symm
    · exfalso
      apply hnot3
      have hS0N : S0 ≤ N := by
        intro s hs
        have : (⟨s, hs⟩ : ↥S0) ∈ (N ⊓ S0).subgroupOf S0 := htop ▸ Subgroup.mem_top _
        exact this.1
      exact hN3.of_injective
        { toFun := fun x => ⟨x.1, hS0N x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl } (by
          intro x y hxy
          exact Subtype.ext (congrArg (fun t : ↥N => (t : A)) hxy))
  intro a b
  have hxN : a.1.1 ∈ N := Subgroup.mem_map.mpr ⟨a.1, a.2, rfl⟩
  have hyN : b.1.1 ∈ N := Subgroup.mem_map.mpr ⟨b.1, b.2, rfl⟩
  have hcommN : a.1.1 * b.1.1 * a.1.1⁻¹ * b.1.1⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem hxN hyN) (N.inv_mem hxN)) (N.inv_mem hyN)
  have hcommS0 : a.1.1 * b.1.1 * a.1.1⁻¹ * b.1.1⁻¹ ∈ S0 :=
    hBC1 a.1.1 a.1.2 b.1.1 b.1.2
  have hone : a.1.1 * b.1.1 * a.1.1⁻¹ * b.1.1⁻¹ = 1 := by
    have hmem : a.1.1 * b.1.1 * a.1.1⁻¹ * b.1.1⁻¹ ∈ N ⊓ S0 := ⟨hcommN, hcommS0⟩
    rw [hM', Subgroup.mem_bot] at hmem
    exact hmem
  have hxy : a.1.1 * b.1.1 = b.1.1 * a.1.1 := by
    have h1 : a.1.1 * b.1.1 * (b.1.1 * a.1.1)⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa only [mul_assoc] using hone
    exact mul_inv_eq_one.mp h1
  exact Subtype.ext (Subtype.ext hxy)

private theorem k329inog2_Q_adjoint
    {K : Type} [Field K] [Finite K] [Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)]
    (hcard : Nat.card K = 8)
    (z : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    k329inog2_Q ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) z := by
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hcard]; norm_num
  have hK4 : 4 ≤ Nat.card K := by rw [hcard]; norm_num
  obtain ⟨g, hg | hg⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
      (K := K) h3 hK4 z hz3 hz1
  · have hgz3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [← MulAut.conj_apply g z, ← map_pow, hz3, map_one]
    have hgz1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      have h' : MulAut.conj g z = 1 := by simpa [MulAut.conj_apply] using h
      exact hz1 ((MulAut.conj g).injective (by rw [h', map_one]))
    have hQ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.isQuasisimple_centralizer_threeA
      (K := K) h3 hK4 hg hgz3 hgz1
    refine k329inog2_Q_of_mulEquiv (MulAut.conj g) z ?_
    simpa [MulAut.conj_apply] using
      (k329inog2_Q_of_isQuasisimple_centralizer (g * z * g⁻¹) hQ hgz1)
  · set z' : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := g * z * g⁻¹ with hz'def
    have hz'3 : z' ^ 3 = 1 := by
      rw [hz'def, ← MulAut.conj_apply g z, ← map_pow, hz3, map_one]
    have hz'1 : z' ≠ 1 := by
      intro h
      have h' : MulAut.conj g z = 1 := by simpa [hz'def, MulAut.conj_apply] using h
      exact hz1 ((MulAut.conj g).injective (by rw [h', map_one]))
    have hBC := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ThreeBCentMinus_holds
      (K := K) h3 hK4 z' hg hz'3 hz'1
    have : CharP K 2 :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.charP_of_natCard_eq_pow Nat.prime_two
        (show Nat.card K = 2 ^ 3 by rw [hcard]; norm_num)
    have hS0C : CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K ≤
        Subgroup.centralizer ({z'} : Set ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hg
    have hS0simple : IsSimpleGroup
        ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K) := by
      have hSL2 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
        CFSG.RankThree.PartOne.KCOrthogonal.sl2_isSimpleGroup (F := K) hK4
      obtain ⟨e⟩ :=
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
      exact (MulEquiv.isSimpleGroup_congr e).mp hSL2
    have hnot3 : ¬ IsPGroup 3
        ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K) := by
      intro hS03
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS03
      have hcardS0 : Nat.card
          ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K) = 504 := by
        obtain ⟨e⟩ :=
          CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
        rw [← Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula K, hcard]
        norm_num
      rw [hcardS0] at hn
      have h7 : 7 ∣ 3 ^ n := by rw [← hn]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_seven h7) (by norm_num)
    have hQlong : k329inog2_Q ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) z' :=
      k329inog2_Q_of_longGroup hS0C hBC.1 hS0simple hnot3
    refine k329inog2_Q_of_mulEquiv (MulAut.conj g) z ?_
    simpa [hz'def, MulAut.conj_apply] using hQlong

theorem k329in_excO3_G2
    (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hL : LieModel S .G2 0 2 3) (u : S) (hu : orderOf u = 3) (N : Subgroup S)
    (hNC : N ≤ Subgroup.centralizer ({u} : Set S))
    (hN : (N.subgroupOf (Subgroup.centralizer ({u} : Set S))).Normal) (hN3 : IsPGroup 3 N) :
    ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  have _hS : IsSimpleGroup S := hS
  intro a ha b hb
  have hCE := hL.chevalleyExceptionalModel (by decide)
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel,
    CFSG.Blueprint.UntwistedChevalleyModel] at hCE
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eS⟩⟩ := hCE
  have hcard : Nat.card K = 8 := by rw [hKcard]; norm_num
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let eA : CFSG.Blueprint.AdjointQuotient .G2 K ≃*
      ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let φ : S ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := eS.trans eA
  have : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    Finite.of_equiv S φ.toEquiv
  have hu3 : u ^ 3 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    omega
  have hφu3 : (φ u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hφu1 : φ u ≠ 1 := by
    intro h
    exact hu1 (φ.injective (by rw [h, map_one]))
  have hQS : k329inog2_Q S u :=
    k329inog2_Q_of_mulEquiv φ u
      (k329inog2_Q_adjoint (K := K) hcard (φ u) hφu3 hφu1)
  exact k329inog2_P_of_Q u hQS N hNC hN hN3 a ha b hb

theorem k329ExceptionalO3Statement_holds
    : k329ExceptionalO3Statement := by
  intro S _ _ hS hL u hu
  obtain ⟨N, hNC, hNn, hN3, a, ha, b, hb, hab⟩ := k329in_udatum_normal_three S u hu
  exact hab (k329in_excO3_G2 S hS hL u hu.1 N hNC hNn hN3 a ha b hb)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
