module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofTheta
import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step166SolDelta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ X ∈ scriptY3Star A (lB A), ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) →
      ∀ J ∈ thetaComponentsIn (pPrimeCoreOf 3 X),
        (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥J ⧸ aschbacherSolvableCore 3 ↥J) 2 m) →
          J = delta A (lB A) J

@[expose] def Step166SolDeltaHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ X ∈ scriptY3Star A (lB A), ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) →
        ∀ J ∈ thetaComponentsIn (pPrimeCoreOf 3 X),
          (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥J ⧸ aschbacherSolvableCore 3 ↥J) 2 m) →
            J = delta A (lB A) J

namespace Steps166

section Sol

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_thetaQuot_of_not_three_dvd {X J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn X) (h3 : ¬ 3 ∣ Nat.card J) :
    IsSimpleGroup (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
  have hq := Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 hJ
  refine isSimpleGroup_of_isQuasisimple_of_center_eq_bot hq ?_
  set θ := aschbacherSolvableCore 3 ↥J with hθ
  obtain ⟨hθs, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
  set Zh := (Subgroup.center (↥J ⧸ θ)).comap (QuotientGroup.mk' θ) with hZh
  have hZhn : Zh.Normal := Subgroup.Normal.comap inferInstance _
  have hθZh : θ ≤ Zh := fun x hx => by
    change QuotientGroup.mk' θ x ∈ Subgroup.center (↥J ⧸ θ)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  have hZhs : Group.IsSolvable Zh := by
    let f : ↥(θ.subgroupOf Zh) →* ↥Zh := (θ.subgroupOf Zh).subtype
    let g : ↥Zh →* Subgroup.center (↥J ⧸ θ) :=
      ((QuotientGroup.mk' θ).comp Zh.subtype).codRestrict _ fun x => x.2
    have hfg : g.ker ≤ f.range := by
      intro x hx
      have hx1 : QuotientGroup.mk' θ (x : ↥J) = 1 := congrArg Subtype.val hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      exact ⟨⟨x, hx1⟩, rfl⟩
    have : Group.IsSolvable ↥(θ.subgroupOf Zh) := by
      have e := Subgroup.subgroupOfEquivOfLe hθZh
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have : Group.IsSolvable (Subgroup.center (↥J ⧸ θ)) := inferInstance
    exact Group.isSolvable_of_ker_le_range f g hfg
  have hZh3 : ¬ 3 ∣ Nat.card Zh := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card Zh))
  have hle : Zh ≤ θ := hθmax Zh hZhn hZhs hZh3
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ z
  have hx : x ∈ θ := hle hz
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact Subgroup.one_mem _

theorem inCatalog_thetaQuot (hG : TheoremFourHyp G) {J : Subgroup G} (hJ : J ≠ ⊤)
    (hs : IsSimpleGroup (↥J ⧸ aschbacherSolvableCore 3 ↥J))
    (hnab : ∃ a b : ↥J ⧸ aschbacherSolvableCore 3 ↥J, a * b ≠ b * a) :
    CFSG.Assembly.InCatalog (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
  set θ := aschbacherSolvableCore 3 ↥J with hθ
  set Lθ : Subgroup G := θ.map J.subtype with hLθ
  have hsub : Lθ.subgroupOf J = θ := by
    rw [hLθ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
  have : (Lθ.subgroupOf J).Normal := by rw [hsub]; infer_instance
  let e : ↥J ⧸ Lθ.subgroupOf J ≃* ↥J ⧸ θ := QuotientGroup.quotientMulEquivOfEq hsub
  have hs' : IsSimpleGroup (↥J ⧸ Lθ.subgroupOf J) := e.isSimpleGroup
  have hnab' : ∃ a b : ↥J ⧸ Lθ.subgroupOf J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨e'⟩⟩ := hG.kProper J Lθ hJ (Subgroup.map_subtype_le θ) hs' hnab'
  exact ⟨i, ⟨e.symm.trans e'⟩⟩

theorem sol166_of_delta
    {A : Subgroup G} {Y₀ : Subgroup G} (hG : TheoremFourHyp G) (htheta : Step166Theta)
    (hΔ : ∀ X ∈ scriptY3Star A (lB A), ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) →
      ∀ J ∈ thetaComponentsIn (pPrimeCoreOf 3 X),
        (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥J ⧸ aschbacherSolvableCore 3 ↥J) 2 m) →
          J = delta A (lB A) J) :
    Sol166 A Y₀ := by
  intro hΩ X hX _ hXM
  by_contra hsol
  set O := pPrimeCoreOf 3 X with hO
  have h3O : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X)
  obtain ⟨J', hJ'⟩ := Proof1423.exists_mem_thetaComponents_of_not_isSolvable h3O hsol
  set J := J'.map O.subtype with hJdef
  have hJO : J ∈ thetaComponentsIn O := ⟨J', hJ', rfl⟩
  have hOX : O ≤ X := pPrimeCoreOf_le 3 X
  have hOn : (O.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr (le_normalizer_pPrimeCoreOf 3 X)
  have hJX : J ∈ thetaComponentsIn X :=
    Proof1423.mem_thetaComponentsIn_of_isSubnormal hJO hOX hOn.isSubnormal
  have hJleO : J ≤ O := le_of_mem_thetaComponentsIn hJO
  have h3J : ¬ 3 ∣ Nat.card J := fun h => h3O (h.trans (Subgroup.card_dvd_of_le hJleO))
  have hs := isSimpleGroup_thetaQuot_of_not_three_dvd hJX h3J
  have hq := Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 hJX
  have hnab : ∃ a b : ↥J ⧸ aschbacherSolvableCore 3 ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
    exact ⟨a', b', fun h => hab (by rw [← map_mul, ← map_mul, h])⟩
  have hXtop : X ≠ ⊤ := hX.prop.1.1.1
  have hJtop : J ≠ ⊤ := fun h => hXtop (eq_top_iff.mpr (h ▸ le_of_mem_thetaComponentsIn hJX))
  have hcat := inCatalog_thetaQuot hG hJtop hs hnab
  have h3Q : ¬ 3 ∣ Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) := fun h =>
    h3J (h.trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨m, hm⟩ :=
    KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd _ hnab hcat h3Q
  have hθ := htheta G hG X J hJX m hm
  have hm' : CFSG.Blueprint.SuzukiModel (↥J ⧸ CFSG.pCore 2 ↥J) 2 m :=
    suzukiModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hθ) hm
  exact hXM (hΩ J X (hΔ X hX hXM J hJO ⟨m, hm⟩) ⟨m, hm'⟩ (le_of_mem_thetaComponentsIn hJX) hX)

end Sol

end Steps166

theorem step166Sol_of
    (h2 : Step166ThetaTwo) (hΔ : Step166SolDelta) : Step166Sol :=
  fun G _ _ A c L Y₀ h => Steps166.sol166_of_delta h.toTheoremFourHyp (step166Theta_of h2)
    (hΔ G A c L Y₀ h)

theorem step166SolHJ_of
    (h2 : Step166ThetaTwo) (hΔ : Step166SolDeltaHJ) : Step166SolHJ :=
  fun G _ _ A c L Y₀ h hJ => Steps166.sol166_of_delta h.toTheoremFourHyp (step166Theta_of h2)
    (hΔ G A c L Y₀ h hJ)

end CFSG.RankThree.PartTwo.Sec16
