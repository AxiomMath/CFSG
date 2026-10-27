module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCentral
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open scoped commutatorElement

namespace BThreeCensus

section Quotient

variable {Y₀ : Type*} [Group Y₀] [Finite Y₀]

theorem center_quotient_theta_eq_bot (h3 : ¬ 3 ∣ Nat.card Y₀) :
    Subgroup.center (Y₀ ⧸ aschbacherSolvableCore 3 Y₀) = ⊥ := by
  set θ := aschbacherSolvableCore 3 Y₀ with hθ
  obtain ⟨hθs, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := Y₀)
    Nat.prime_three
  set D := (Subgroup.center (Y₀ ⧸ θ)).comap (QuotientGroup.mk' θ) with hD
  have hDn : D.Normal := (Subgroup.center (Y₀ ⧸ θ)).normal_comap _
  have hθD : θ ≤ D := fun x hx => by
    change (QuotientGroup.mk' θ x) ∈ Subgroup.center (Y₀ ⧸ θ)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hDs : Group.IsSolvable D := by
    let g : D →* Subgroup.center (Y₀ ⧸ θ) :=
      ((QuotientGroup.mk' θ).comp D.subtype).codRestrict _ fun d => d.2
    have : Group.IsSolvable θ := hθs
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθD) g fun d hd => ?_
    have hd' : (QuotientGroup.mk' θ (d : Y₀)) = 1 := congrArg Subtype.val hd
    exact ⟨⟨d, (QuotientGroup.eq_one_iff _).mp hd'⟩, rfl⟩
  have hD3 : ¬ 3 ∣ Nat.card D := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card D))
  have hDθ : D ≤ θ := hmax D hDn hDs hD3
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  have hyD : y ∈ D := hz
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff y).mpr (hDθ hyD)

theorem isSimpleGroup_quotient_theta (h3 : ¬ 3 ∣ Nat.card Y₀)
    (hq : IsQuasisimple (Y₀ ⧸ aschbacherSolvableCore 3 Y₀)) :
    IsSimpleGroup (Y₀ ⧸ aschbacherSolvableCore 3 Y₀) := by
  have : IsSimpleGroup ((Y₀ ⧸ aschbacherSolvableCore 3 Y₀) ⧸
      Subgroup.center (Y₀ ⧸ aschbacherSolvableCore 3 Y₀)) := hq.2.1
  have e := (QuotientGroup.quotientMulEquivOfEq (center_quotient_theta_eq_bot h3)).trans
    (QuotientGroup.quotientBot (G := Y₀ ⧸ aschbacherSolvableCore 3 Y₀))
  exact e.symm.isSimpleGroup

omit [Finite Y₀] in
theorem exists_mul_ne_of_isQuasisimple (hq : IsQuasisimple (Y₀ ⧸ aschbacherSolvableCore 3 Y₀)) :
    ∃ a b : Y₀ ⧸ aschbacherSolvableCore 3 Y₀, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem exists_suzukiModel_quotient_theta
    {H Y : Subgroup G} (hK : IsKGroup H) (hYH : Y ≤ H)
    (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) (hY3 : ¬ 3 ∣ Nat.card Y) :
    ∃ f, SuzukiModel (Y ⧸ aschbacherSolvableCore 3 Y) 2 f := by
  have hsimp := isSimpleGroup_quotient_theta hY3 hYq
  set e₀ : Y.subgroupOf H ≃* Y := Subgroup.subgroupOfEquivOfLe hYH with he₀
  set e : (Y.subgroupOf H) ⧸ aschbacherSolvableCore 3 (Y.subgroupOf H) ≃*
      Y ⧸ aschbacherSolvableCore 3 Y :=
    QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀) with he
  have hsimp' : IsSimpleGroup ((Y.subgroupOf H) ⧸ aschbacherSolvableCore 3 (Y.subgroupOf H)) :=
    e.isSimpleGroup
  obtain ⟨i, ⟨ei⟩⟩ := hK (Y.subgroupOf H) (aschbacherSolvableCore 3 (Y.subgroupOf H)) hsimp'
  have hcat : Assembly.InCatalog (Y ⧸ aschbacherSolvableCore 3 Y) := ⟨i, ⟨e.symm.trans ei⟩⟩
  have h3 : ¬ 3 ∣ Nat.card (Y ⧸ aschbacherSolvableCore 3 Y) := fun h =>
    hY3 (h.trans (Subgroup.card_quotient_dvd_card _))
  exact KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd _
    (exists_mul_ne_of_isQuasisimple hYq) hcat h3

theorem subgroupOf_theta_le {X Y : Subgroup G} (hYX : Y ≤ X) :
    (inSubgroup (aschbacherSolvableCore 3) X).subgroupOf Y ≤ aschbacherSolvableCore 3 Y := by
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := Y)
    Nat.prime_three
  set T := inSubgroup (aschbacherSolvableCore 3) X with hT
  obtain ⟨hTs, hT3⟩ := theta_solvable_and_not_dvd X
  let ι : T.subgroupOf Y →* T :=
    { toFun := fun x => ⟨(x : Y), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun z : T => (z : G)) hxy))
  refine hmax _ ⟨fun n hn y => ?_⟩ ?_ ?_
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta X (hYX y.2)) n).mp hn
    simpa using this
  · have := hTs
    exact Group.isSolvable_of_isSolvable_injective (f := ι) hι
  · exact fun h => hT3 (h.trans (Subgroup.card_dvd_of_injective ι hι))

section Image

variable {X Y : Subgroup G}

@[expose] noncomputable def toImage (hYX : Y ≤ X) : Y →* Sec8.imageModTheta X Y :=
  ((QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (Subgroup.inclusion hYX)).codRestrict _
    fun y => ⟨Subgroup.inclusion hYX y, y.2, rfl⟩

theorem coe_toImage (hYX : Y ≤ X) (y : Y) :
    (toImage hYX y : X ⧸ aschbacherSolvableCore 3 X) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 X) (Subgroup.inclusion hYX y) :=
  rfl

theorem toImage_surjective (hYX : Y ≤ X) : Function.Surjective (toImage hYX) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem map_toImage_theta (hYX : Y ≤ X) :
    (aschbacherSolvableCore 3 Y).map (toImage hYX) =
      (Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y)).subgroupOf
        (Sec8.imageModTheta X Y) := by
  ext ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨t, ht, htz⟩
    refine ⟨Subgroup.inclusion hYX t, ⟨t, ht, rfl⟩, ?_⟩
    have := congrArg Subtype.val htz
    rw [coe_toImage] at this
    exact this
  · rintro ⟨x, ⟨t, ht, htx⟩, rfl⟩
    refine ⟨t, ht, Subtype.ext ?_⟩
    rw [coe_toImage]
    congr 1
    exact Subtype.ext htx

theorem normal_imageModTheta_theta (hYX : Y ≤ X) :
    ((Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y)).subgroupOf
      (Sec8.imageModTheta X Y)).Normal := by
  rw [← map_toImage_theta hYX]
  exact (aschbacherSolvableCore_normal 3 Y).map _ (toImage_surjective hYX)

theorem comap_toImage_theta (hYX : Y ≤ X) :
    ((Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y)).subgroupOf
      (Sec8.imageModTheta X Y)).comap (toImage hYX) = aschbacherSolvableCore 3 Y := by
  rw [← map_toImage_theta hYX, Subgroup.comap_map_eq, sup_eq_left]
  intro y hy
  have hy1 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) (Subgroup.inclusion hYX y) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    rwa [coe_toImage] at this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy1
  exact subgroupOf_theta_le hYX ⟨Subgroup.inclusion hYX y, hy1, rfl⟩

theorem nonempty_quotientThetaEquiv (hYX : Y ≤ X)
    [((Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y)).subgroupOf
      (Sec8.imageModTheta X Y)).Normal] :
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
      Sec8.imageModTheta X Y ⧸
        (Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y)).subgroupOf
          (Sec8.imageModTheta X Y)) := by
  set N := (Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y)).subgroupOf
    (Sec8.imageModTheta X Y) with hN
  have hker : ((QuotientGroup.mk' N).comp (toImage hYX)).ker = aschbacherSolvableCore 3 Y := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hN, comap_toImage_theta hYX]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp (toImage_surjective hYX)))⟩

end Image

theorem commutator_theta_le_of_threePrimeB3
    {H X Y : Subgroup G} (hK : IsKGroup H) (hXH : X ≤ H)
    (hB3 : ThreePrimeB3 (X ⧸ aschbacherSolvableCore 3 X)) {b : G} (hb3 : b ^ 3 = 1)
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hYXC : Y ≤ X ⊓ Subgroup.centralizer {b})
    (hYp : Group.IsPerfect Y) (hYsn : (Y.subgroupOf (X ⊓ Subgroup.centralizer {b})).IsSubnormal)
    (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) (hY3 : ¬ 3 ∣ Nat.card Y) :
    ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYX : Y ≤ X := hYXC.trans inf_le_left
  set θX := aschbacherSolvableCore 3 X with hθX
  set π := QuotientGroup.mk' θX with hπ
  set W := X ⊓ Subgroup.centralizer ({b} : Set G) with hW
  have hWX : W ≤ X := inf_le_left
  set β := Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbX⟩) with hβ
  set C := Sec8.barCentralizer (Subgroup.zpowers b) X with hC
  set Yb := Sec8.imageModTheta X Y with hYb
  set Rb := Sec8.imageModTheta X (inSubgroup (aschbacherSolvableCore 3) Y) with hRb
  have hRn : (Rb.subgroupOf Yb).Normal := normal_imageModTheta_theta hYX
  have hβ3 : β ^ 3 = 1 := by
    have h1 : (⟨b, hbX⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    rw [hβ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hCfix : ∀ z, z ∈ C ↔ β z = z := KFacts.mem_barCentralizer_zpowers_iff hbX
  have hCW : Sec8.imageModTheta X W = C :=
    KFacts.imageModTheta_centralizer_eq hbX ⟨1, by simpa using hb3⟩
  have hYbC : Yb ≤ C := by
    rw [← hCW]
    exact Subgroup.map_mono fun x hx => hYXC hx
  have hsn : (Yb.subgroupOf C).IsSubnormal := by
    let ρ : W →* C := ((π.comp (Subgroup.inclusion hWX)).codRestrict C fun w => by
      rw [← hCW]
      exact ⟨Subgroup.inclusion hWX w, w.2, rfl⟩)
    have hρ : Function.Surjective ρ := by
      rintro ⟨c, hc⟩
      rw [← hCW] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    have hmap : (Y.subgroupOf W).map ρ = Yb.subgroupOf C := by
      ext ⟨c, hc⟩
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨w, hw, hwc⟩
        refine ⟨Subgroup.inclusion hWX w, hw, ?_⟩
        exact congrArg Subtype.val hwc
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hYXC hx⟩, hx, Subtype.ext rfl⟩
    rw [← hmap]
    exact hYsn.map hρ
  have hYp' : Group.IsPerfect Yb := by
    have := hYp
    rw [hYb, Sec8.imageModTheta, ← Subgroup.inclusion_range hYX, MonoidHom.map_range]
    exact Group.IsPerfect.range _
  have hYb3 : ¬ 3 ∣ Nat.card Yb := fun h => hY3 (h.trans
    (Subgroup.card_dvd_of_surjective (f := toImage hYX) (toImage_surjective hYX)))
  have hRY : Rb ≤ Yb := Subgroup.map_mono fun x hx => theta_le Y hx
  have hRs : Group.IsSolvable Rb := by
    have hs := (theta_solvable_and_not_dvd Y).1
    have hle : inSubgroup (aschbacherSolvableCore 3) Y ≤ X := (theta_le Y).trans hYX
    let ι : (inSubgroup (aschbacherSolvableCore 3) Y) →* Rb :=
      ((π.comp (Subgroup.inclusion hle)).codRestrict Rb fun t =>
        ⟨Subgroup.inclusion hle t, t.2, rfl⟩)
    refine Group.isSolvable_of_surjective (f := ι) ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hsz : ∃ f, SuzukiModel (Yb ⧸ Rb.subgroupOf Yb) 2 f := by
    obtain ⟨f, hf⟩ := exists_suzukiModel_quotient_theta hK (hYX.trans hXH) hYq hY3
    obtain ⟨h2, a, ha, K, _, _, hfa, hKc, ⟨e⟩⟩ := hf
    obtain ⟨e'⟩ := nonempty_quotientThetaEquiv hYX
    exact ⟨f, h2, a, ha, K, inferInstance, inferInstance, hfa, hKc, ⟨e'.symm.trans e⟩⟩
  have key := hB3 β hβ3 C Yb Rb hCfix hYbC hsn hYp' hYb3 hRY hRs hsz
  rw [Subgroup.commutator_le]
  intro t ht y hy
  have htX : t ∈ X := hYX (theta_le Y ht)
  have hyX : y ∈ X := hYX hy
  refine ⟨⁅(⟨t, htX⟩ : X), (⟨y, hyX⟩ : X)⁆, ?_, rfl⟩
  rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
    map_commutatorElement]
  have h1 : ⁅π ⟨t, htX⟩, π ⟨y, hyX⟩⁆ ∈ ⁅Rb, Yb⁆ :=
    Subgroup.commutator_mem_commutator ⟨⟨t, htX⟩, ht, rfl⟩ ⟨⟨y, hyX⟩, hy, rfl⟩
  rw [key] at h1
  exact h1

end BThreeCensus

open BThreeCensus in
theorem bThreePropertyThreePrimeCentral_of_threePrimeB3
    (h46 : Sec4.Item4_6)
    (hcen : ∀ (Q : Type) [Group Q] [Finite Q], Sec4.IsList46 Q → IsQuasisimple Q →
      ThreePrimeB3 Q) :
    BThreePropertyThreePrimeCentral := by
  intro G _ _ H hH hZ X hX b _ hb3 hbX Y hYXC hYp hYsn hYq hY3
  obtain ⟨hXH, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  have hB3' := hcen _ (h46 H hH hZ (X.subgroupOf H) hX') hX'.2.2
  set e₀ : X.subgroupOf H ≃* X := Subgroup.subgroupOfEquivOfLe hXH with he₀
  set e : (X.subgroupOf H) ⧸ aschbacherSolvableCore 3 (X.subgroupOf H) ≃*
      X ⧸ aschbacherSolvableCore 3 X :=
    QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀) with he
  exact commutator_theta_le_of_threePrimeB3 hH.kGroup hXH (threePrimeB3_of_mulEquiv e.symm hB3')
    hb3 hbX hYXC hYp hYsn hYq hY3

end CFSG.RankThree.PartTwo.Sec6
