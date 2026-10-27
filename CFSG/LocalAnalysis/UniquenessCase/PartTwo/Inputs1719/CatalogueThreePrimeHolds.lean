module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEvenHolds
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtStar
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_CatalogueThreePrimeSz_holds :
    K_CatalogueThreePrimeSz := by
  intro J _ _ hK hQ h3
  have hperf : Group.IsPerfect J := ⟨hQ.1⟩
  have hsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hQ.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ3 : ¬ 3 ∣ Nat.card J := by
    intro h
    exact h3 ⟨Nat.prime_three, by simpa [Subgroup.card_top] using h⟩
  have hZ3 : ¬ 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    intro h
    exact hJ3 (h.trans (Subgroup.card_quotient_dvd_card (Subgroup.center J)))
  have hKq : CFSG.Open.IsKGroup (J ⧸ Subgroup.center J) :=
    hK.quotient (Subgroup.center J)
  have hnab : ¬ ∀ a b : J ⧸ Subgroup.center J, a * b = b * a := by
    intro h
    have : IsMulCommutative (J ⧸ Subgroup.center J) := ⟨⟨h⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (J ⧸ Subgroup.center J) inferInstance
  obtain ⟨n, hn⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.kFactSuzukiThreeFree_holds
      (J := J ⧸ Subgroup.center J) hsimple hnab hKq hZ3
  let O : Subgroup J := CFSG.pCore 2 J
  let N : Type := J ⧸ O
  have hO : O.Normal := CFSG.pCore_normal
  have hntJ : Nontrivial J :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hOtop : CFSG.pCore 2 J ≠ ⊤ := by
    intro htop
    have hP : IsPGroup 2 J := by
      have h := CFSG.pCore_isPGroup (p := 2) (G := J)
      rw [htop] at h
      have : IsPGroup 2 (⊤ : Subgroup J) := h
      exact IsPGroup.of_equiv h Subgroup.topEquiv
    have : Group.IsNilpotent J := hP.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (G := J) inferInstance
  have hntN : Nontrivial N := QuotientGroup.nontrivial_iff.mpr hOtop
  have hperfN : Group.IsPerfect N := inferInstance
  let π : J →* N := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  let ψ : J →* N ⧸ Subgroup.center N :=
    (QuotientGroup.mk' (Subgroup.center N)).comp π
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (Subgroup.center N)).comp hπ
  have hZψ : Subgroup.center J ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (π z) : N ⧸ Subgroup.center N) = 1
    rw [QuotientGroup.eq_one_iff]
    refine Subgroup.mem_center_iff.2 fun y => ?_
    obtain ⟨w, rfl⟩ := hπ y
    show π w * π z = π z * π w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
  let f : (J ⧸ Subgroup.center J) →* (N ⧸ Subgroup.center N) :=
    QuotientGroup.lift (Subgroup.center J) ψ hZψ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]⟩
  have hfker : f.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exfalso
      have hf1 : f = 1 := MonoidHom.ker_eq_top_iff.1 h
      have : Subsingleton (N ⧸ Subgroup.center N) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hf a
        obtain ⟨y, rfl⟩ := hf b
        simp [hf1]
      have hcenter : Subgroup.center N = ⊤ := QuotientGroup.subsingleton_iff.1 inferInstance
      have : IsMulCommutative N := ⟨⟨fun a b =>
        Subgroup.mem_center_iff.1 (hcenter ▸ Subgroup.mem_top b) a⟩⟩
      exact Group.IsPerfect.not_isMulCommutative N inferInstance
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hfker
  let e : (J ⧸ Subgroup.center J) ≃* (N ⧸ Subgroup.center N) :=
    MulEquiv.ofBijective f ⟨hfinj, hf⟩
  have hodd : Odd (Nat.card (Subgroup.center N)) := uc22p20p_odd_center_bar2 J
  have hSzN : CFSG.Blueprint.SuzukiModel (N ⧸ Subgroup.center N) 2 n :=
    CFSG.SectionRank.suzukiModel_of_mulEquiv e.symm hn
  have hSz : CFSG.Blueprint.SuzukiModel N 2 n :=
    CFSG.Quasithin.H13.P31Sz.suzukiModel_of_odd_center hodd hSzN
  exact ⟨n, CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, hSz⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
