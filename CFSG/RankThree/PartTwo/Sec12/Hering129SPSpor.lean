module

public import CFSG.RankThree.PartTwo.Sec12.Hering129SPLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24KFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Monster.Schur.M24
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofSpor

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129SP

open CFSG CFSG.Blueprint CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.ThreeCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    ↥(Subgroup.centralizer ({g} : Set G)) ≃* ↥(Subgroup.centralizer ({e g} : Set H)) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr
    (CFSG.AGLEmbeddingD2.Wilson.Proving.centralizer_map_mulEquiv_wilson e g))

theorem card_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  rw [← Subgroup.map_center_eq e]
  exact (Subgroup.card_map_of_injective e.injective).symm

theorem quasisimple_center_three_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsQuasisimple A ∧ Nat.card (Subgroup.center A) = 3) :
    CFSG.IsQuasisimple B ∧ Nat.card (Subgroup.center B) = 3 :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.1,
    by rw [← card_center_eq_of_mulEquiv e]; exact h.2⟩

theorem inner3_of_outer_le_two {W : Type} [Group W] [Finite W]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer W) ≤ 2) :
    ∀ γ : MulAut W, γ ^ 3 = 1 → ∃ w : W, γ = MulAut.conj w := by
  intro γ hγ
  have hγ' : γ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner W :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.mem_inner_of_card_outer_le_two hout
      ⟨1, by rw [pow_one]; exact hγ⟩
  obtain ⟨w, hw⟩ := hγ'
  exact ⟨w, hw.symm⟩

theorem inner3_of_mulEquiv {X W : Type} [Group X] [Group W] (e : X ≃* W)
    (h : ∀ γ : MulAut W, γ ^ 3 = 1 → ∃ w : W, γ = MulAut.conj w) :
    ∀ β : MulAut X, β ^ 3 = 1 → ∃ x : X, β = MulAut.conj x := by
  intro β hβ
  obtain ⟨w, hw⟩ := h (MulAut.congr e β) (by rw [← map_pow, hβ, map_one])
  refine ⟨e.symm w, ?_⟩
  apply (MulAut.congr e).injective
  rw [hw]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem not_prime_of_dvd_two {n : ℕ} (h2 : 2 ∣ n) (hn : 2 < n) : ¬ n.Prime := fun hp => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  omega

theorem nonabelian_of_simple_not_prime {W : Type} [Group W] [Finite W] (hs : IsSimpleGroup W)
    (hp : ¬ (Nat.card W).Prime) : ∃ a b : W, a * b ≠ b * a := by
  by_contra h
  push_neg at h
  haveI := hs
  letI : CommGroup W := { ‹Group W› with mul_comm := h }
  exact hp (IsSimpleGroup.prime_card (α := W))

theorem noPerfectDoubleCover_of_trivialMultiplier {W : Type} [Group W] [Finite W]
    (hs : IsSimpleGroup W) (hn : ∃ a b : W, a * b ≠ b * a)
    (hmult : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
      Nonempty (Q ⧸ Subgroup.center Q ≃* W) → Subgroup.center Q = ⊥) :
    CFSG.Monster.Schur.NoPerfectDoubleCover W := by
  intro E _ π hπ hperf hcard
  haveI := hs
  have hkerfin : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Finite (E ⧸ π.ker) :=
    Finite.of_equiv W (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv.symm
  haveI : Finite E :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := π.ker)).symm
  have hcentral : π.ker ≤ Subgroup.center E := fun x hx =>
    CFSG.Monster.Schur.mem_center_of_mem_ker π hcard hx
  have hZker : Subgroup.center E = π.ker := by
    apply le_antisymm _ hcentral
    have hn' : ((Subgroup.center E).map π).Normal := Subgroup.Normal.map inferInstance π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center E).map π) with h | h
    · intro z hz
      have : π z ∈ (Subgroup.center E).map π := Subgroup.mem_map_of_mem π hz
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      obtain ⟨a', ha', rfl⟩ : a ∈ (Subgroup.center E).map π := by rw [h]; trivial
      obtain ⟨b', hb', rfl⟩ : b ∈ (Subgroup.center E).map π := by rw [h]; trivial
      exact hab (by rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha' b'])
  have hquot : Nonempty (E ⧸ Subgroup.center E ≃* W) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZker).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩
  have hq : CFSG.IsQuasisimple E := by
    refine ⟨hperf, ?_, ?_⟩
    · obtain ⟨e⟩ := hquot
      exact e.isSimpleGroup
    · obtain ⟨e⟩ := hquot
      obtain ⟨a, b, hab⟩ := hn
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hbot := hmult E hq hquot
  rw [hZker] at hbot
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

theorem SporLocal.of_mulEquiv {W X : Type} [Group W] [Group X] (e : W ≃* X) (h : SporLocal W) :
    SporLocal X where
  simple := @MulEquiv.isSimpleGroup _ _ _ _ h.simple e.symm
  nonabelian := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact ⟨e a, e b, fun h' => hab (e.injective (by simpa using h'))⟩
  inner3 := inner3_of_mulEquiv e.symm h.inner3
  noDouble := CFSG.Monster.Schur.NoPerfectDoubleCover.of_mulEquiv e h.noDouble
  threeCases := by
    intro w hw
    have hw' : orderOf (e.symm w) = 3 := by rw [MulEquiv.orderOf_eq]; exact hw
    have hew : e (e.symm w) = w := e.apply_symm_apply w
    let f : ↥(Subgroup.centralizer ({e.symm w} : Set W)) ≃*
        ↥(Subgroup.centralizer ({w} : Set X)) :=
      (centralizerEquiv e (e.symm w)).trans (MulEquiv.subgroupCongr (by rw [hew]))
    rcases h.threeCases (e.symm w) hw' with h3 | h4
    · exact Or.inl (quasisimple_center_three_of_mulEquiv f h3)
    · exact Or.inr (by rw [← Nat.card_congr f.toEquiv]; exact h4)

theorem threeCases_M24
    (w : NativeSporadic.M24) (hw : orderOf w = 3) :
    (CFSG.IsQuasisimple ↥(Subgroup.centralizer ({w} : Set NativeSporadic.M24)) ∧
      Nat.card (Subgroup.center ↥(Subgroup.centralizer ({w} : Set NativeSporadic.M24))) = 3) ∨
    Nat.card ↥(Subgroup.centralizer ({w} : Set NativeSporadic.M24)) = 504 := by
  have hord : orderOf ((w : NativeSporadic.M24) : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe]; exact hw
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover w.2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    left
    let gP : NativeSporadic.M24 := ⟨g, hg⟩
    let φ : NativeSporadic.M24 ≃* NativeSporadic.M24 := MulAut.conj gP⁻¹
    have hφ : φ w = m24y := by
      apply Subtype.ext
      show g⁻¹ * ((w : NativeSporadic.M24) : Equiv.Perm (Fin 24)) * g = permOfArr 24 m24xA
      rw [hgr]
      show g⁻¹ * (g * permOfArr 24 m24xA * g⁻¹) * g = permOfArr 24 m24xA
      group
    obtain ⟨-, ⟨e'⟩, -⟩ := m24_layer
    have hspec := m24Tc_spec
    let f : ↥(Subgroup.centralizer ({w} : Set NativeSporadic.M24)) ≃*
        ↥(Subgroup.centralizer ({m24y} : Set NativeSporadic.M24)) :=
      (centralizerEquiv φ w).trans (MulEquiv.subgroupCongr (by rw [hφ]))
    exact quasisimple_center_three_of_mulEquiv (f.trans e').symm ⟨hspec.2.1, hspec.2.2.1⟩
  ·
    right
    calc Nat.card ↥(Subgroup.centralizer ({w} : Set NativeSporadic.M24))
        = Nat.card ↥((Subgroup.centralizer ({w} : Set NativeSporadic.M24)).map
            NativeSporadic.M24.subtype) :=
          (Subgroup.card_map_of_injective NativeSporadic.M24.subtype_injective).symm
      _ = Nat.card ↥(NativeSporadic.M24 ⊓ Subgroup.centralizer
            ({((w : NativeSporadic.M24) : Equiv.Perm (Fin 24))} :
              Set (Equiv.Perm (Fin 24)))) := by
          rw [CFSG.AGLEmbeddingD2.Wilson.ThreeCore.map_subtype_centralizer]
      _ = Nat.card ↥(Subgroup.centralizer ({((w : NativeSporadic.M24) :
            Equiv.Perm (Fin 24))} : Set (Equiv.Perm (Fin 24))) ⊓ NativeSporadic.M24) := by
          rw [inf_comm]
      _ = Nat.card ↥(Subgroup.centralizer ({tp 24 m24Row3B.rep} :
            Set (Equiv.Perm (Fin 24))) ⊓ NativeSporadic.M24) :=
          (CFSG.RankThree.Native.card_centralizer_inf_conj NativeSporadic.M24 hg hgr.symm).symm
      _ = 504 := by rw [inf_comm]; exact m24_threeSpec_rowB

theorem sporLocal_M24 :
    SporLocal NativeSporadic.M24 where
  simple := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  nonabelian := ⟨_, _, CFSG.Sporadic.Schreier.m24_gens_not_comm⟩
  inner3 := fun β _ => by
    have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M24 = ⊤ :=
      CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
        CFSG.Sporadic.Schreier.m24_mulAut_card
    have hβ : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M24 := by
      rw [hinner]; trivial
    obtain ⟨w, hw⟩ := hβ
    exact ⟨w, hw.symm⟩
  noDouble := CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24
  threeCases := threeCases_M24

theorem threeCases_He
    {X : Type} [Group X]
    (e : X ≃* NativeSporadic.He) (w : X) (hw : orderOf w = 3) :
    (CFSG.IsQuasisimple ↥(Subgroup.centralizer ({w} : Set X)) ∧
      Nat.card (Subgroup.center ↥(Subgroup.centralizer ({w} : Set X))) = 3) ∨
    Nat.card ↥(Subgroup.centralizer ({w} : Set X)) = 504 := by
  obtain ⟨e', -⟩ : ∃ e' : X ≃* CFSG.Sporadic.HeldB.heP, True :=
    ⟨e.trans CFSG.Sporadic.HeldB.heEquivP, trivial⟩
  have hord : orderOf (((e' w : CFSG.Sporadic.HeldB.heP)) : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hw
  rcases CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.three_conj_cases (e' w).2 hord with
    ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  ·
    left
    obtain ⟨φ, hφ⟩ : ∃ φ : X ≃* CFSG.Sporadic.HeldB.heP, φ w = heY := by
      refine ⟨e'.trans (MulAut.conj (⟨c, hc⟩ : CFSG.Sporadic.HeldB.heP)⁻¹), ?_⟩
      apply Subtype.ext
      show c⁻¹ * (((e' w : CFSG.Sporadic.HeldB.heP)) : Equiv.Perm (Fin 8330)) * c =
        CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.bOf
          CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeWordsA
      rw [hcx]
      group
    obtain ⟨-, ⟨e''⟩, -⟩ := he_layer
    have hspec := heTc_spec
    let f : ↥(Subgroup.centralizer ({w} : Set X)) ≃*
        ↥(Subgroup.centralizer ({heY} : Set CFSG.Sporadic.HeldB.heP)) :=
      (centralizerEquiv φ w).trans (MulEquiv.subgroupCongr (by rw [hφ]))
    exact quasisimple_center_three_of_mulEquiv (f.trans e'').symm ⟨hspec.2.1, hspec.2.2.1⟩
  ·
    right
    obtain ⟨φ, hφ⟩ : ∃ φ : X ≃* CFSG.Sporadic.HeldB.heP,
        ((φ w : CFSG.Sporadic.HeldB.heP) : Equiv.Perm (Fin 8330)) =
        CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.bOf
          CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeWordsB := by
      refine ⟨e'.trans (MulAut.conj (⟨c, hc⟩ : CFSG.Sporadic.HeldB.heP)⁻¹), ?_⟩
      show c⁻¹ * (((e' w : CFSG.Sporadic.HeldB.heP)) : Equiv.Perm (Fin 8330)) * c =
        CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.bOf
          CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeWordsB
      rw [hcx]
      group
    calc Nat.card ↥(Subgroup.centralizer ({w} : Set X))
        = Nat.card ↥(Subgroup.centralizer ({φ w} : Set CFSG.Sporadic.HeldB.heP)) :=
          Nat.card_congr (centralizerEquiv φ w).toEquiv
      _ = Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn CFSG.Sporadic.HeldB.heP
            ((φ w : CFSG.Sporadic.HeldB.heP) : Equiv.Perm (Fin 8330))) := card_centralizer_heP _
      _ = 504 := by rw [hφ]; exact CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.card_cent_B

theorem sporLocal_He
    {X : Type} [Group X] (e : X ≃* NativeSporadic.He) :
    SporLocal X := by
  have hcard : Nat.card X = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.He.card_He
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e
  have hn : ∃ a b : X, a * b ≠ b * a :=
    nonabelian_of_simple_not_prime hs (by
      rw [hcard]
      exact not_prime_of_dvd_two (by norm_num) (by norm_num))
  haveI : Finite NativeSporadic.He := Finite.of_equiv X e.toEquiv
  have h3 : ∀ β : MulAut X, β ^ 3 = 1 → ∃ x : X, β = MulAut.conj x :=
    @inner3_of_mulEquiv X NativeSporadic.He _ _ e
      (@inner3_of_outer_le_two NativeSporadic.He _ _ CFSG.Sporadic.Schreier.AT_He_Schreier.1)
  refine ⟨hs, hn, h3, ?_, fun w hw => threeCases_He e w hw⟩
  · refine noPerfectDoubleCover_of_trivialMultiplier hs hn ?_
    intro Q _ _ hQ ⟨f⟩
    exact CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate Q hQ
      ⟨f.trans e⟩

theorem sporLocal_of_equiv
    {X : Type} [Group X]
    (h : Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.He)) :
    SporLocal X := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact SporLocal.of_mulEquiv e.symm sporLocal_M24
  · obtain ⟨e⟩ := h
    exact sporLocal_He e

end CFSG.RankThree.PartTwo.Sec12.Hering129SP
