module

public import CFSG.OddTranspositions.PartFour.RankOneBender
public import CFSG.OddTranspositions.PartFour.RankOneKernel
public import CFSG.OddTranspositions.PartFour.RankOneLine
public import CFSG.OddTranspositions.PartFour.RootMeetsSq
import CFSG.OddTranspositions.PartFour.RankOneSemiregular
import CFSG.OddTranspositions.BenderMeetsSq

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_isSolvable_Halpha_of_isBenderGroup (hC : HypothesisC D)
    (hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    ¬ Group.IsSolvable (Halpha D hC.alpha) := by
  intro hsol
  haveI := hsol
  have htop : CFSG.solvableRadical (Halpha D hC.alpha) = ⊤ :=
    top_le_iff.mp (le_solvableRadical (N := ⊤) Subgroup.normal_top inferInstance)
  haveI : Nontrivial (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    (IsBenderGroup.isSimpleGroup hX).toNontrivial
  have hall : ∀ x : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha), x = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    rw [QuotientGroup.eq_one_iff, htop]
    exact Subgroup.mem_top a
  obtain ⟨x, hx⟩ := exists_ne (1 : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
  exact hx (hall x)

theorem meetsSq_imageClass_of_isBenderGroup (hC : HypothesisC D)
    (hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    MeetsSq (imageClass hC) := by
  exact bender_meetsSq hX (imageClass_isClass hC)
    (imageClass_involutions hC (not_isSolvable_Halpha_of_isBenderGroup hC hX))

private theorem rankOneMeetsSq_four_le_two_pow {f j : ℕ} (hf : 2 ≤ f) (hj : 0 < j) :
    4 ≤ 2 ^ (f * j) := by
  have hle : f ≤ f * j := Nat.le_mul_of_pos_right f hj
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (f * j) := Nat.pow_le_pow_of_le (by norm_num) (le_trans hf hle)

private theorem rankOneMeetsSq_two_le_two_pow_sub_one {f : ℕ} (hf : 2 ≤ f) :
    2 ≤ 2 ^ f - 1 := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_of_le (by norm_num) hf
  exact Nat.le_sub_one_of_lt (by omega)

private theorem rankOneMeetsSq_two_pow_sub_one_lt {f j : ℕ} (hf : 2 ≤ f) (hj : 0 < j) :
    2 ^ f - 1 < 2 ^ (f * j) := by
  have hle : f ≤ f * j := Nat.le_mul_of_pos_right f hj
  have hlt : 2 ^ f - 1 < 2 ^ f := Nat.sub_one_lt (Nat.two_pow_pos f).ne'
  exact lt_of_lt_of_le hlt (Nat.pow_le_pow_of_le (by norm_num) hle)

private theorem rankOneMeetsSq_mul_ne_mul_add_one {f k j : ℕ} (hf : 2 ≤ f) :
    f * k ≠ f * j + 1 := by
  intro h
  have hdvd : f ∣ f * j + 1 := by rw [← h]; exact dvd_mul_right f k
  have h1 : f ∣ 1 := (Nat.dvd_add_right (dvd_mul_right f j)).mp hdvd
  have hle : f ≤ 1 := Nat.le_of_dvd (by norm_num) h1
  omega

private theorem rankOneMeetsSq_exists_point (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ b : Halpha D hC.alpha, (b : G) ∈ β := by
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  exact ⟨⟨b, Subgroup.subset_closure ⟨β, hβ, hb⟩⟩, hb⟩

private theorem rankOneMeetsSq_mk_mem_imageClass (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈ imageClass hC :=
  ⟨b, ⟨β, hβ, hb⟩, rfl⟩

private theorem rankOneMeetsSq_exists_S₀ (hC : HypothesisC D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) {n : ℕ}
    (hn : 0 < n)
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hconj : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 →
      ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ imageClass hC, x ∈ K0 ∧ ∃ y ∈ imageClass hC, y ∈ K0 ∧
      orderOf (x * y) = 2 ^ n + 1)
    {b : Halpha D hC.alpha}
    (hx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈ imageClass hC) :
    ∃ S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      S₀ ⊆ imageClass hC ∧
      Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ⊆ S₀ ∧
      (∃ w ∈ S₀,
        ¬ Commute w (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)) ∧
      (∀ y ∈ S₀, ∀ z ∈ S₀, z * y * z⁻¹ ∈ S₀) ∧
      (∀ y ∈ S₀, ∀ z ∈ S₀, ¬ Commute y z →
        Subgroup.closure (insert z {w | w ∈ S₀ ∧ Commute w y}) = Subgroup.closure S₀) ∧
      (∀ y ∈ S₀, ∀ z ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * y * g⁻¹ = z) ∧
      ∃ y ∈ S₀, ∃ z ∈ S₀, orderOf (y * z) = 2 ^ n + 1 := by
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  have hd₀mem : d₀ ∈ imageClass hC := by rw [hd₀]; exact IsConj.refl d₀
  have hs₀ : orderOf d₀ = 2 := imageClass_involutions hC hHns d₀ hd₀mem
  exact exists_rootLiftClass_of_subgroup (s := d₀) (E := imageClass hC) hs₀ hd₀ K0 hn hgen
    hconj hord hx

private theorem rankOneMeetsSq_exists_exponent (hC : HypothesisC D) {f k : ℕ} (hf : 2 ≤ f)
    (hpow : ∀ β ∈ Dalpha D hC.alpha, ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (f * j)) :
    ∃ s : ℕ, 1 ≤ s ∧ (∀ β ∈ Dalpha D hC.alpha,
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ s) ∧
      f * k ≠ s + 1 := by
  classical
  by_cases hne : (Dalpha D hC.alpha).Nonempty
  · obtain ⟨β₀, hβ₀⟩ := hne
    obtain ⟨j₀, hj₀, hβ₀j⟩ := hpow β₀ hβ₀
    refine ⟨f * j₀, by have := Nat.mul_pos (by omega : 0 < f) hj₀; omega, ?_, ?_⟩
    · intro β hβ
      calc ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard
          = ((fun x => cimg x β₀) '' (Malpha D hC.alpha : Set G)).ncard :=
            ncard_orbit_Malpha_eq hC hβ₀ hβ
        _ = 2 ^ (f * j₀) := hβ₀j
    · exact rankOneMeetsSq_mul_ne_mul_add_one (j := j₀) hf
  · refine ⟨f, by omega, ?_, ?_⟩
    · exact fun β hβ => absurd ⟨β, hβ⟩ hne
    · simpa using rankOneMeetsSq_mul_ne_mul_add_one (j := 1) hf

section Certified


theorem ncard_blockImage_eq_one_of_rankOne (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (hVf : ∀ x ∈ imageClass hC, (Vmem (imageClass hC) x).ncard = 2 ^ f - 1)
    (K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) {n : ℕ}
    (hn : 0 < n)
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hconj : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 →
      ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ imageClass hC, x ∈ K0 ∧ ∃ y ∈ imageClass hC, y ∈ K0 ∧
      orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {j : ℕ} (hj : 0 < j)
    (hβj : ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (f * j)) :
    (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1 := by
  obtain ⟨b, hb⟩ := rankOneMeetsSq_exists_point hC hβ
  have hx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈ imageClass hC :=
    rankOneMeetsSq_mk_mem_imageClass hC hβ hb
  obtain ⟨S₀, hS₀, hVS₀, hw, hinv, hgen', hconj', hord'⟩ :=
    rankOneMeetsSq_exists_S₀ hC hHns K0 hn hgen hconj hord hx
  obtain ⟨N, hNM, hexp, hsemi, hcover⟩ :=
    exists_semiregular_of_rootLift h89 h113 hC hrad hW hn3 hMZ hHns hS₀ hn hinv hgen' hconj'
      hord' hβ hb hVS₀ hw
  exact ncard_blockImage_eq_one_of_lt h89 h113 hC hrad hW hn3 hMZ hHns
    (fun v hv => by
      rw [hVf v hv]
      exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
    hβ N hNM hexp hsemi hcover
    (by rw [hβj]; exact rankOneMeetsSq_four_le_two_pow hf hj)
    hb
    (by rw [hVf _ hx, hβj]; exact rankOneMeetsSq_two_pow_sub_one_lt hf hj)

theorem meetsSq_of_isBenderGroup_imageClass (h87 : PartThree.Theorem8_7)
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hX : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    {f k : ℕ} (hf : 2 ≤ f)
    (hB : CFSG.Open.fusionBenderBorel
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (2 ^ f) k)
    (K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) {n : ℕ}
    (hn : 0 < n)
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hconj : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 →
      ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ imageClass hC, x ∈ K0 ∧ ∃ y ∈ imageClass hC, y ∈ K0 ∧
      orderOf (x * y) = 2 ^ n + 1)
    (hpow : ∀ β ∈ Dalpha D hC.alpha, ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (f * j)) :
    MeetsSq D := by
  have hHns := not_isSolvable_Halpha_of_isBenderGroup hC hX
  have hsq := meetsSq_imageClass_of_isBenderGroup hC hX
  have hn3 := not_threeTransp_of_meetsSq hC hsq
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  have hd₀mem : d₀ ∈ imageClass hC := by rw [hd₀]; exact IsConj.refl d₀
  have hs₀ : orderOf d₀ = 2 := imageClass_involutions hC hHns d₀ hd₀mem
  have hVf : ∀ x ∈ imageClass hC, (Vmem (imageClass hC) x).ncard = 2 ^ f - 1 := fun x hx =>
    ncard_Vmem_eq_of_fusionBenderBorel hX hs₀ hd₀ hB hx
  have hS : (Vmem (imageClass hC) '' imageClass hC).ncard = 2 ^ (f * k) + 1 := by
    rw [ncard_image_Vmem_eq_of_fusionBenderBorel hX hs₀ hd₀ hB, ← pow_mul]
  have hTI : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, Commute x y →
      y ∈ Vmem (imageClass hC) x := by
    intro x hx y hy hxy
    rw [hd₀] at hx hy ⊢
    exact mem_Vmem_of_commute_of_isBenderGroup hX hs₀ hx hy hxy
  have hroot : ∀ x ∈ imageClass hC,
      ∃ R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
        (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
          insert 1 (Vmem (imageClass hC) x) := by
    intro x hx
    rw [hd₀] at hx ⊢
    exact exists_subgroup_eq_insert_Vmem_of_isBenderGroup hX hs₀ hx
  have h2 : ∀ x ∈ imageClass hC, 2 ≤ (Vmem (imageClass hC) x).ncard := fun x hx => by
    rw [hVf x hx]
    exact rankOneMeetsSq_two_le_two_pow_sub_one hf
  have hr1 : ∀ β ∈ Dalpha D hC.alpha,
      (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1 := by
    intro β hβ
    obtain ⟨j, hj, hβj⟩ := hpow β hβ
    exact ncard_blockImage_eq_one_of_rankOne h89 h113 hC hrad hW hn3 hMZ hHns hf hVf
      K0 hn hgen hconj hord hβ hj hβj
  obtain ⟨s, hs, hm, has⟩ := rankOneMeetsSq_exists_exponent hC hf hpow
  have hker := exists_kernel_config_of_rankOne h87 h89 h113 hC hrad hW hn3 hMZ hHns hTI hr1
    (a := f * k) hS hm hs has
  exact meetsSq_of_kernel h89 h113 hC hrad hW hMZ hsq hker hroot h2 hr1

end Certified

end CFSG.OddTranspositions.PartFour
