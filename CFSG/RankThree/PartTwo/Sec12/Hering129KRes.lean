module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFK
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeQuasisimpleSL
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KRes

theorem isQuasisimple_of_isSLThreePiAt {X : Type} [Group X] {m : ℕ} (hX : Sec4.IsSLThreePiAt X m)
    (hm : 2 < m) : CFSG.IsQuasisimple X := by
  obtain ⟨π, p, f, K, hF, hK, hmod, hpf, ⟨e⟩⟩ := Item128StepsProof.exists_model hX
  subst hpf
  exact CFSG.IsQuasisimple.of_mulEquiv e
    (Sec4.Item462AltProof.KSLThree.isQuasisimple_slPi hK hm)

theorem map_theta_eq_bot {X Q : Type} [Group X] [Finite X] [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Nat.card (Subgroup.center Q) = 3) (φ : X →* Q) (hφ : Function.Surjective φ) :
    (aschbacherSolvableCore 3 X).map φ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  haveI := hθs
  set M := (aschbacherSolvableCore 3 X).map φ with hM
  haveI hMn : M.Normal := Subgroup.Normal.map inferInstance φ hφ
  have hMsolv : Group.IsSolvable M := solvable_of_surjective (φ.subgroupMap_surjective _)
  have hMZ : M ≤ Subgroup.center Q := Hering129HLift.solvable_normal_le_center hQ M hMsolv
  have hMcard : Nat.card M ∣ Nat.card (aschbacherSolvableCore 3 X) :=
    Subgroup.card_dvd_of_surjective (φ.subgroupMap_surjective (aschbacherSolvableCore 3 X))
  have hMZc : Nat.card M ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hMZ
  have hM1 : Nat.card M = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hMZc with h | h
    · exact h
    · exact absurd (h ▸ hMcard) hθ3
  exact Subgroup.eq_bot_of_card_eq M hM1


theorem exists_quotTheta_resCent_equiv {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    {c : G} (hcY : c ∈ Y) (hc3 : c ^ 3 = 1) {m : ℕ} (hm : 2 < m)
    (hI : Sec4.IsSLThreePiAt
      ↥(resCent (⊤ : Subgroup (↥Y ⧸ aschbacherSolvableCore 3 ↥Y))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Y) ⟨c, hcY⟩)) m) :
    Nonempty (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c) ≃*
      ↥(resCent (⊤ : Subgroup (↥Y ⧸ aschbacherSolvableCore 3 ↥Y))
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Y) ⟨c, hcY⟩))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, hθc, hθ3, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  set N := aschbacherSolvableCore 3 ↥Y with hN
  haveI : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  set c₀ : ↥Y := ⟨c, hcY⟩ with hc₀
  have hc₀3 : c₀ ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  set I := resCent Y c with hIdef
  have hIY : I ≤ Y := (resCent_le Y c).trans inf_le_left
  set Î := resCent (⊤ : Subgroup (↥Y ⧸ N)) (π c₀) with hÎdef
  have hQÎ : CFSG.IsQuasisimple ↥Î := isQuasisimple_of_isSLThreePiAt hI hm
  have hZÎ : Nat.card (Subgroup.center ↥Î) = 3 := card_center_eq_three_of_isSLThreePi ⟨m, hI⟩
  set R := inSubgroup perfectResidual (Subgroup.centralizer ({c₀} : Set ↥Y)) with hR
  have hIR : I = R.map Y.subtype := resCent_eq_map Y hcY
  have hRÎ : R.map π = Î := map_resCent_quot N hθ3 hc₀3
  let ρ0 : ↥I →* (↥Y ⧸ N) := π.comp (Subgroup.inclusion hIY)
  have hρ0 : ∀ i : ↥I, ∃ r ∈ R, (r : G) = (i : G) ∧ ρ0 i = π r := by
    intro i
    have hi : (i : G) ∈ R.map Y.subtype := hIR ▸ i.2
    obtain ⟨r, hr, hri⟩ := hi
    refine ⟨r, hr, hri, ?_⟩
    have : Subgroup.inclusion hIY i = r := Subtype.ext hri.symm
    show π (Subgroup.inclusion hIY i) = π r
    rw [this]
  have hmemÎ : ∀ i : ↥I, ρ0 i ∈ Î := by
    intro i
    obtain ⟨r, hr, -, h⟩ := hρ0 i
    rw [h, ← hRÎ]
    exact Subgroup.mem_map_of_mem _ hr
  let ρ : ↥I →* ↥Î := ρ0.codRestrict Î hmemÎ
  have hρ : Function.Surjective ρ := by
    rintro ⟨w, hw⟩
    rw [← hRÎ] at hw
    obtain ⟨r, hr, hrw⟩ := hw
    have hrI : (r : G) ∈ I := hIR ▸ ⟨r, hr, rfl⟩
    refine ⟨⟨(r : G), hrI⟩, Subtype.ext ?_⟩
    show ρ0 ⟨(r : G), hrI⟩ = w
    rw [← hrw]
    show π (Subgroup.inclusion hIY ⟨(r : G), hrI⟩) = π r
    rfl
  obtain ⟨hθIs, hθIc, hθI3, hθImax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥I) Nat.prime_three
  have hker : ρ.ker = aschbacherSolvableCore 3 ↥I := by
    apply le_antisymm
    · intro i hi
      have h1 : ρ0 i = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hi)
        exact this
      have h2 : Subgroup.inclusion hIY i ∈ N := (QuotientGroup.eq_one_iff _).mp h1
      have h3 : (i : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := ⟨_, h2, rfl⟩
      exact mem_theta_of_mem_theta_of_le hIY i.2 h3
    · intro t ht
      haveI : Group.IsSolvable (aschbacherSolvableCore 3 ↥I) := hθIs
      set M := (aschbacherSolvableCore 3 ↥I).map ρ with hM
      haveI hMn : M.Normal := Subgroup.Normal.map inferInstance ρ hρ
      have hMsolv : Group.IsSolvable M := solvable_of_surjective (ρ.subgroupMap_surjective _)
      have hMZ : M ≤ Subgroup.center ↥Î :=
        Hering129HLift.solvable_normal_le_center hQÎ M hMsolv
      have hMcard : Nat.card M ∣ Nat.card (aschbacherSolvableCore 3 ↥I) :=
        Subgroup.card_dvd_of_surjective (ρ.subgroupMap_surjective (aschbacherSolvableCore 3 ↥I))
      have hMZc : Nat.card M ∣ 3 := hZÎ ▸ Subgroup.card_dvd_of_le hMZ
      have hM1 : Nat.card M = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hMZc with h | h
        · exact h
        · exact absurd (h ▸ hMcard) hθI3
      have htM : ρ t ∈ M := Subgroup.mem_map_of_mem ρ ht
      have hM0 : M = ⊥ := Subgroup.eq_bot_of_card_eq M hM1
      rw [hM0, Subgroup.mem_bot] at htM
      exact MonoidHom.mem_ker.mpr htM
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

theorem false_of_threeA_image {X Q : Type} [Group X] [Finite X] [Group Q]
    (hXp : Group.IsPerfect X) (φ : X →* Q) (hker : φ.ker ≤ aschbacherSolvableCore 3 X)
    {z : Q} {m : ℕ} (hm : 2 < m) (hz : Sec4.IsSLThreePiAt ↥(resCent (⊤ : Subgroup Q) z) m)
    (hPz : φ.range ≤ resCent (⊤ : Subgroup Q) z)
    (hsub : (φ.range.subgroupOf (resCent (⊤ : Subgroup Q) z)).IsSubnormal)
    (hne : φ.range ≠ ⊥)
    (hZ2 : ∀ w ∈ Subgroup.center (X ⧸ aschbacherSolvableCore 3 X), w ^ 2 = 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := resCent (⊤ : Subgroup Q) z with hC
  have hQ := isQuasisimple_of_isSLThreePiAt hz hm
  have hZ3 : Nat.card (Subgroup.center ↥C) = 3 := card_center_eq_three_of_isSLThreePi ⟨m, hz⟩
  haveI : Group.IsPerfect X := hXp
  have hPperf : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have hP'perf : Group.IsPerfect (φ.range.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPz).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPz).symm.surjective
  have hP'ne : φ.range.subgroupOf C ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have hyC : y ∈ C := hPz hy
    have : (⟨y, hyC⟩ : ↥C) ∈ φ.range.subgroupOf C := hy
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    exact Subgroup.mem_bot.mpr this
  have htop := Sec11.FieldCentRigid82.eq_top_of_isSubnormal_of_isQuasisimple hQ hsub hP'perf hP'ne
  let φ' : X →* ↥C := φ.codRestrict C (fun x => hPz ⟨x, rfl⟩)
  have hφ' : Function.Surjective φ' := by
    intro q
    have hq : q ∈ φ.range.subgroupOf C := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z₀ ∈ Subgroup.center ↥C, z₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Subgroup.center ↥C = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this] at hZ3
    simp at hZ3
  have hz₀3 : z₀ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center ↥C) (x := ⟨z₀, hz₀Z⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  obtain ⟨x₀, hx₀⟩ := hφ' z₀
  have hcen : (QuotientGroup.mk x₀ : X ⧸ aschbacherSolvableCore 3 X) ∈
      Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) := by
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    have h1 : φ' y * z₀ = z₀ * φ' y := (Subgroup.mem_center_iff.mp hz₀Z (φ' y))
    have hmem : (y * x₀)⁻¹ * (x₀ * y) ∈ aschbacherSolvableCore 3 X := by
      apply hker
      show φ ((y * x₀)⁻¹ * (x₀ * y)) = 1
      have h2 : φ' ((y * x₀)⁻¹ * (x₀ * y)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hx₀, h1]
        group
      exact congrArg Subtype.val h2
    exact QuotientGroup.eq.mpr hmem
  have hsq := hZ2 _ hcen
  have hx₀2 : x₀ ^ 2 ∈ aschbacherSolvableCore 3 X := by
    rw [← QuotientGroup.mk_pow] at hsq
    exact (QuotientGroup.eq_one_iff _).mp hsq
  have hbot := map_theta_eq_bot hQ hZ3 φ' hφ'
  have hz₀2 : z₀ ^ 2 = 1 := by
    have : φ' (x₀ ^ 2) ∈ (aschbacherSolvableCore 3 X).map φ' := Subgroup.mem_map_of_mem φ' hx₀2
    rw [hbot, Subgroup.mem_bot, map_pow, hx₀] at this
    exact this
  apply hz₀1
  have : z₀ = z₀ ^ 3 * (z₀ ^ 2)⁻¹ := by group
  rw [this, hz₀3, hz₀2]
  simp

theorem mem_resCent_of_image {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (hN2 : ∀ n ∈ N, ∃ k : ℕ, n ^ (2 ^ k) = 1) {t s : Y}
    (ht3 : t ^ 3 = 1) (hs3 : s ^ 3 = 1) (hts : s * t = t * s)
    (hs : QuotientGroup.mk' N s ∈ resCent (⊤ : Subgroup (Y ⧸ N)) (QuotientGroup.mk' N t)) :
    s ∈ inSubgroup perfectResidual (Subgroup.centralizer ({t} : Set Y)) := by
  set T := Subgroup.centralizer ({t} : Set Y) with hT
  have hsT : s ∈ T := Subgroup.mem_centralizer_singleton_iff.mpr hts
  set P : Subgroup T := perfectResidual T with hP
  haveI : P.Characteristic := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  haveI : P.Normal := inferInstance
  rw [← map_resCent_quot N hN ht3] at hs
  obtain ⟨y, hy, hys⟩ := hs
  obtain ⟨p, hpP, hpy⟩ := hy
  let sT : T := ⟨s, hsT⟩
  let nT : T := sT * p⁻¹
  have hnN : (nT : Y) ∈ N := by
    have h1 : QuotientGroup.mk' N ((nT : T) : Y) = 1 := by
      change QuotientGroup.mk' N (s * ((p : T) : Y)⁻¹) = 1
      rw [map_mul, map_inv]
      have : QuotientGroup.mk' N ((p : T) : Y) = QuotientGroup.mk' N s := by
        rw [show ((p : T) : Y) = y from hpy]
        exact hys
      rw [this, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := hN2 _ hnN
  have hnk : nT ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hs3T : sT ^ 3 = 1 := Subtype.ext (by simpa using hs3)
  have hsT' : sT = nT * p := by
    change sT = sT * p⁻¹ * p
    group
  have := Hering129HLift.mem_of_mul_mem_of_pow_three P hpP hsT' hs3T ⟨k, hnk⟩
  exact ⟨sT, this, rfl⟩

end Hering129KRes

end CFSG.RankThree.PartTwo.Sec12
