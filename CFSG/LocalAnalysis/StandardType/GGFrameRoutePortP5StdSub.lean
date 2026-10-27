module

public import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5Cover
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.RankThree.PartOne

variable {G : Type} [Group G] {L : Subgroup G} {R : Type} [Group R]

private def coverProjection (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (J : Subgroup R) :
    ↥(coverComponent θ J) →* ↥J :=
  ((coverMap θ).comp (Subgroup.inclusion (Subgroup.map_subtype_le
    (derivedPreimage (coverMap θ) J)))).codRestrict J fun l => by
    have hl : (l : G) ∈ (derivedPreimage (coverMap θ) J).map L.subtype := l.2
    obtain ⟨d, hd, hdl⟩ := Subgroup.mem_map.mp hl
    have hincl : Subgroup.inclusion (Subgroup.map_subtype_le
        (derivedPreimage (coverMap θ) J)) l = d :=
      Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hdl.symm)
    change coverMap θ (Subgroup.inclusion (Subgroup.map_subtype_le
      (derivedPreimage (coverMap θ) J)) l) ∈ J
    rw [hincl]
    exact derivedPreimage_le_comap (coverMap θ) J hd

private theorem coverProjection_surjective (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {J : Subgroup R} (hJ : Group.IsPerfect ↥J) :
    Function.Surjective (coverProjection θ J) := by
  intro j
  have hmap : (derivedPreimage (coverMap θ) J).map (coverMap θ) = J :=
    map_derivedPreimage_of_perfect (coverMap_surjective θ) hJ
  obtain ⟨d, hd, hdπ⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact j.2)
  refine ⟨⟨L.subtype d, Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change coverMap θ (Subgroup.inclusion (Subgroup.map_subtype_le
    (derivedPreimage (coverMap θ) J)) ⟨L.subtype d, _⟩) = (j : R)
  rw [show Subgroup.inclusion (Subgroup.map_subtype_le
      (derivedPreimage (coverMap θ) J)) ⟨L.subtype d, _⟩ = d from
    Subtype.ext (by rw [Subgroup.coe_inclusion]; rfl)]
  exact hdπ

private theorem coverProjection_ker_le_center (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (J : Subgroup R) :
    (coverProjection θ J).ker ≤ Subgroup.center ↥(coverComponent θ J) := by
  intro l hl
  rw [Subgroup.mem_center_iff]
  intro m
  apply Subtype.ext
  have hlπ : coverMap θ (Subgroup.inclusion (Subgroup.map_subtype_le
      (derivedPreimage (coverMap θ) J)) l) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
  have hlL : Subgroup.inclusion (Subgroup.map_subtype_le
      (derivedPreimage (coverMap θ) J)) l ∈ (coverMap θ).ker := MonoidHom.mem_ker.mpr hlπ
  rw [coverMap_ker] at hlL
  have hcomm := Subgroup.mem_center_iff.mp hlL
    (Subgroup.inclusion (Subgroup.map_subtype_le (derivedPreimage (coverMap θ) J)) m)
  have hval := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul] at hval
  exact hval

private theorem comap_center_coverProjection_le (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {J : Subgroup R} (hJ : CFSG.IsQuasisimple ↥J) :
    (Subgroup.center ↥J).comap (coverProjection θ J) ≤
      Subgroup.center ↥(coverComponent θ J) := by
  intro a ha
  have hperf : Group.IsPerfect ↥(coverComponent θ J) := (isQuasisimple_coverComponent θ hJ).1
  have hker := coverProjection_ker_le_center θ J
  have hcent : a ∈ Subgroup.centralizer (⊤ : Set ↥(coverComponent θ J)) := by
    refine CFSG.mem_centralizer_of_commutator_mem_center (J := ⊤)
      (Group.IsPerfect.top_iff.mpr hperf) (Subgroup.le_normalizer (Subgroup.mem_top a)) ?_
    intro j _
    have hzker : a * j * a⁻¹ * j⁻¹ ∈ (coverProjection θ J).ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [show coverProjection θ J a * coverProjection θ J j =
          coverProjection θ J j * coverProjection θ J a from
        (Subgroup.mem_center_iff.mp ha (coverProjection θ J j)).symm]
      group
    have hz := hker hzker
    refine Subgroup.mem_map.mpr ⟨⟨a * j * a⁻¹ * j⁻¹, Subgroup.mem_top _⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hz (w : ↥(coverComponent θ J))
  rw [Subgroup.mem_center_iff]
  intro b
  exact Subgroup.mem_centralizer_iff.mp hcent b (Subgroup.mem_top b)

theorem nonempty_centerQuot_coverComponent (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {J : Subgroup R}
    (hJ : CFSG.IsQuasisimple ↥J) :
    Nonempty (↥(coverComponent θ J) ⧸ Subgroup.center ↥(coverComponent θ J) ≃*
      ↥J ⧸ Subgroup.center ↥J) := by
  let J₁ : Subgroup G := coverComponent θ J
  change Nonempty (↥J₁ ⧸ Subgroup.center ↥J₁ ≃* ↥J ⧸ Subgroup.center ↥J)
  have hmapc : Subgroup.map (coverProjection θ J) (Subgroup.center ↥J₁) ≤
      Subgroup.center ↥J :=
    Subgroup.map_center_le_center (coverProjection_surjective θ hJ.1)
  have hZle : Subgroup.center ↥J₁ ≤ (Subgroup.center ↥J).comap (coverProjection θ J) := by
    intro a ha
    rw [Subgroup.mem_comap]
    exact hmapc (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  have hZge := comap_center_coverProjection_le θ hJ
  let Φ : ↥J₁ ⧸ Subgroup.center ↥J₁ →* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.map (Subgroup.center ↥J₁) (Subgroup.center ↥J) (coverProjection θ J) hZle
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y
    obtain ⟨a, rfl⟩ := coverProjection_surjective θ hJ.1 j
    refine ⟨QuotientGroup.mk' (Subgroup.center ↥J₁) a, ?_⟩
    change (QuotientGroup.map (Subgroup.center ↥J₁) (Subgroup.center ↥J)
      (coverProjection θ J) hZle) (QuotientGroup.mk' (Subgroup.center ↥J₁) a) = _
    rw [QuotientGroup.map_mk']
    rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J₁) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J₁) y
    change (QuotientGroup.map (Subgroup.center ↥J₁) (Subgroup.center ↥J)
      (coverProjection θ J) hZle) (QuotientGroup.mk' (Subgroup.center ↥J₁) a) =
      (QuotientGroup.map (Subgroup.center ↥J₁) (Subgroup.center ↥J)
      (coverProjection θ J) hZle) (QuotientGroup.mk' (Subgroup.center ↥J₁) b) at hxy
    rw [QuotientGroup.map_mk', QuotientGroup.map_mk'] at hxy
    change (QuotientGroup.mk a : ↥J₁ ⧸ Subgroup.center ↥J₁) = QuotientGroup.mk b
    rw [QuotientGroup.eq_iff_div_mem] at hxy ⊢
    exact hZge (Subgroup.mem_comap.mpr (by rwa [map_div]))
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

section Cover

variable (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {J : Subgroup R}

theorem largeEvenMarking_coverComponent (hJ : CFSG.IsQuasisimple ↥J)
    {P : LargeEvenLabel → (Q : Type) → [Group Q] → Set (MulAut Q) → Set (MulAut Q) → Prop}
    (h : LargeEvenMarking ↥J fun lab Q _ I F _ => P lab Q I F) :
    LargeEvenMarking ↥(coverComponent θ J) fun lab Q _ I F _ => P lab Q I F := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  obtain ⟨e⟩ := nonempty_centerQuot_coverComponent θ hJ
  refine ⟨(isQuasisimple_coverComponent θ hJ).1.commutator_eq_top, lab, hlab,
    largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ', hθ'⟩
  exact ⟨hs, hna, e.trans θ', hθ'⟩

theorem not_largeEvenSmall_coverComponent (hJ : CFSG.IsQuasisimple ↥J)
    (hbig : 25920 < Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    ¬ LargeEvenSmall (coverComponent θ J) := by
  obtain ⟨e⟩ := nonempty_centerQuot_coverComponent θ hJ
  have he : Nat.card (↥(coverComponent θ J) ⧸ Subgroup.center ↥(coverComponent θ J)) =
      Nat.card (↥J ⧸ Subgroup.center ↥J) := Nat.card_congr e.toEquiv
  intro hsmall
  have hdvd : Nat.card (↥(coverComponent θ J) ⧸ Subgroup.center ↥(coverComponent θ J)) ∣
      Nat.card ↥(coverComponent θ J) := Subgroup.card_quotient_dvd_card _
  rcases hsmall with hU | hA
  · rw [IOneOrthEnd.card_of_isU42 hU] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · obtain ⟨e6⟩ := hA
    rw [Nat.card_congr e6.toEquiv, IOneOrthEnd.card_alternatingGroup_six] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem inf_centralizer_coverComponent_eq (hJ : Group.IsPerfect ↥J) {Bs F : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {ψ : G → MulAut R}
    (hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ψ b))
    (hF : ∀ b, b ∈ F ↔ b ∈ Bs ∧ ∀ j ∈ J, ψ b j = j) :
    Bs ⊓ Subgroup.centralizer (coverComponent θ J : Set G) = F := by
  ext b
  rw [Subgroup.mem_inf, hF b]
  constructor
  · rintro ⟨hb, hc⟩
    exact ⟨hb, (mem_centralizer_coverComponent_iff θ hJ (hN hb) (hψ b hb)).mp hc⟩
  · rintro ⟨hb, hfix⟩
    exact ⟨hb, (mem_centralizer_coverComponent_iff θ hJ (hN hb) (hψ b hb)).mpr hfix⟩

theorem rank3Witness_coverComponent [Finite G] (hJ : Group.IsPerfect ↥J) {r : ℕ}
    (h : ∀ (J₂ : Type) [Group J₂] [Finite J₂] (π : J₂ →* ↥J), Function.Surjective π →
      π.ker ≤ Subgroup.center J₂ → Rank3Witness J₂ r) :
    Rank3Witness ↥(coverComponent θ J) r :=
  h _ (coverProjection θ J) (coverProjection_surjective θ hJ) (coverProjection_ker_le_center θ J)

end Cover

theorem largeEvenStdSub_of_component {B Bs D J F : Subgroup G} {x : G}
    (hDB : D ≤ B) (hDe : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)))
    (hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hBBs : B ≤ Bs) (hF : Bs ⊓ Subgroup.centralizer (J : Set G) = F) (hBF : B ⊓ F = D)
    (hns : ¬ LargeEvenSmall J) : LargeEvenStdSub 3 B x L D J := by
  refine ⟨⟨hDB, hDe, hDc, hxD, hJ, hJc, ?_⟩, fun _ => hns⟩
  rw [← hBF, ← hF, ← inf_assoc, inf_eq_left.mpr hBBs]

theorem exists_goodPlane_component_of_cover (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    {B Bs F : Subgroup G} {x z : G} {φ : MulAut R} {J : Subgroup R}
    (hDB : Subgroup.closure {x, z} ≤ B) (hDe : IsElemAbelian 3 (Subgroup.closure {x, z}))
    (hDc : Nat.card (Subgroup.closure {x, z}) = 3 ^ 2)
    (hx : x ∈ Subgroup.centralizer (L : Set G)) (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) φ)
    (hJ : CFSG.IsQuasisimple ↥J) (hfix : J ≤ TauCeti.fixedSubgroup φ.toMonoidHom)
    [(J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal]
    (hsolv : IsSolvable (↥(TauCeti.fixedSubgroup φ.toMonoidHom) ⧸
      J.subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)))
    (hbig : 25920 < Nat.card (↥J ⧸ Subgroup.center ↥J)) {lab₀ : LargeEvenLabel}
    (hmark : LargeEvenMarking ↥J fun lab _ _ _ _ _ => lab = lab₀)
    (hBBs : B ≤ Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {ψ : G → MulAut R}
    (hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (ψ b))
    (hF : ∀ b, b ∈ F ↔ b ∈ Bs ∧ ∀ j ∈ J, ψ b j = j)
    (hBF : B ⊓ F = Subgroup.closure {x, z}) :
    let D₁ := Subgroup.closure {x, z}
    let C := L ⊓ Subgroup.centralizer (D₁ : Set G)
    ∃ J₁ : Subgroup G, J₁ = LargeEvenLayer C ∧ IsComponentOf J₁ C ∧ CFSG.IsQuasisimple ↥J₁ ∧
      (J₁.subgroupOf C).Normal ∧
      (∀ _ : (J₁.subgroupOf C).Normal, IsSolvable (↥C ⧸ J₁.subgroupOf C)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = lab₀) ∧
      Bs ⊓ Subgroup.centralizer (J₁ : Set G) = F ∧ LargeEvenStdSub 3 B x L D₁ J₁ := by
  dsimp only
  have hlayer := coverComponent_eq_layer θ hx hz hφ hJ hfix hsolv
  dsimp only at hlayer
  obtain ⟨hLay, hComp, hNorm, hSolv⟩ := hlayer
  have hcent := inf_centralizer_coverComponent_eq θ hJ.1 hN hψ hF
  refine ⟨coverComponent θ J, hLay, hComp, isQuasisimple_coverComponent θ hJ, hNorm, hSolv,
    largeEvenMarking_coverComponent θ hJ hmark, hcent, ?_⟩
  exact largeEvenStdSub_of_component hDB hDe hDc (Subgroup.subset_closure (by simp))
    hLay hComp hBBs hcent hBF (not_largeEvenSmall_coverComponent θ hJ hbig)

theorem closure_pair_facts {G : Type} [Group G] [Finite G] {B : Subgroup G} {x z : G}
    (hEab : CFSG.Open.IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hzB : z ∈ B)
    (hznot : z ∉ Subgroup.zpowers x) (hB9 : 9 < Nat.card B) :
    Subgroup.closure {x, z} ≤ B ∧ CFSG.Open.IsElemAbelian 3 (Subgroup.closure {x, z}) ∧
      Nat.card (Subgroup.closure {x, z}) = 3 ^ 2 ∧ Subgroup.closure {x, z} ≠ B := by
  have hcomm : Commute x z := by
    rw [commute_iff_eq]
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hEab.1) ⟨x, hxB⟩ ⟨z, hzB⟩)
  have hx3 : x ^ 3 = 1 := hEab.2 x hxB
  have hz3 : z ^ 3 = 1 := hEab.2 z hzB
  have hz1 : z ≠ 1 := fun hz => hznot (hz.symm ▸ Subgroup.one_mem _)
  have hDc : Nat.card (Subgroup.closure {x, z}) = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_sq Nat.prime_three hcomm
      (orderOf_eq_prime hx3 hx1) (orderOf_eq_prime hz3 hz1) hznot
  refine ⟨?_, ?_, hDc, ?_⟩
  · refine (Subgroup.closure_le B).mpr ?_
    rintro y (rfl | rfl)
    · exact hxB
    · exact hzB
  · exact CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair hcomm hx3 hz3
  · intro h
    have hcardB : Nat.card B = 9 := by rw [← h, hDc]; norm_num
    omega

theorem ggBstar_card_bounds {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) {n : ℕ}
    (hcard : Nat.card Bs = 3 ^ (n + 1)) :
    3 ^ n ≤ Nat.card B ∧ LargeEvenTwoLocalRank 3 G ≤ n + 1 ∧
      (B ≠ Bs → LargeEvenTwoLocalRank 3 G ≤ n) := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  have hpow : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 ^ (n + 1) := by
    rw [← hBcard, ← hcard]
    exact hle
  refine ⟨?_, (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow, ?_⟩
  · have hp : 3 ^ (n + 1) = 3 ^ n * 3 := by rw [pow_succ]
    have h1 : 3 ^ n * 3 ≤ Nat.card B * 3 := by
      calc 3 ^ n * 3 = 3 ^ (n + 1) := hp.symm
        _ = Nat.card Bs := hcard.symm
        _ ≤ 3 * Nat.card B := hBs.2.2.1
        _ = Nat.card B * 3 := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  · intro hBne
    have hlt : Nat.card B < Nat.card Bs :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hBs.1 hBne)
    have hpowlt : 3 ^ LargeEvenTwoLocalRank 3 G < 3 ^ (n + 1) := by
      rw [← hBcard, ← hcard]
      exact hlt
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hpowlt
    omega

theorem not_le_centralizer_of_inf_eq {G : Type*} [Group G] {B Bs F D J : Subgroup G}
    (hB : B ≤ Bs) (hF : Bs ⊓ Subgroup.centralizer (J : Set G) = F) (hBF : B ⊓ F = D)
    (hDB : D ≠ B) : ¬ Bs ≤ Subgroup.centralizer (J : Set G) := by
  intro hle
  apply hDB
  rw [← hBF, ← hF, inf_eq_left.mpr hle, inf_eq_left.mpr hB]

end CFSG.StandardType.FrameRoute
