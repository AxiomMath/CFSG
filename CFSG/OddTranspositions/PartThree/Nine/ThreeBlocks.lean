module

public import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
public import CFSG.OddTranspositions.SixEight
public import CFSG.OddTranspositions.SevenOne
public import CFSG.OddTranspositions.SevenLocalSecond
public import CFSG.OddTranspositions.BlockGraph
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.StronglyEmbedded.BenderCentre
public import CFSG.GroupTheory.CardSupInf
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.OddTranspositions.BlockAction2
public import CFSG.OddTranspositions.CommutatorSize
public import CFSG.OddTranspositions.SixSevenLocalStep
public import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_not_commute_DalphaStar (hC : HypothesisC D) (hH : Th91Hyp D hC) :
    ∃ x ∈ DalphaStar D hC.alpha, ∃ y ∈ DalphaStar D hC.alpha, ¬ Commute x y := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hH.bender
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
  apply hab
  have hc : IsMulCommutative (Halpha D hC.alpha) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hne x hx y hy
  have hab' : a * b = b * a := hc.is_comm.comm a b
  exact (Commute.map (show Commute a b from hab') (QuotientGroup.mk' _))

omit [Finite G] in
theorem conj_image_block_eq {β : Set G} {g : G}
    (hg : g ∈ Subgroup.normalizer β) : (fun x => g * x * g⁻¹) '' β = β := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hg x).mp hx
  · intro hy
    refine ⟨g⁻¹ * y * g, (hg _).mpr ?_, by group⟩
    convert hy using 1
    group

theorem mem_normalizer_block_of_conj_mem (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {v g : G} (hv : v ∈ β) (hgv : g * v * g⁻¹ ∈ β) :
    g ∈ Subgroup.normalizer β := by
  have hblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ
  by_contra hg
  exact Set.disjoint_left.mp (hblock.disjoint_conj hg) hgv ⟨v, hv, rfl⟩

omit [Finite G] in
theorem commute_of_mem_alpha_of_mem_DalphaStar (hC : HypothesisC D) {a e : G}
    (ha : a ∈ hC.alpha) (he : e ∈ DalphaStar D hC.alpha) : Commute a e := by
  obtain ⟨γ, hγ, heγ⟩ := he
  exact (mem_Dalpha_iff.mp hγ).2.2.2 a ha e heγ

omit [Finite G] in
theorem Halpha_le_centralizer_of_forall_commute (hC : HypothesisC D) {y : G}
    (hy : ∀ e ∈ DalphaStar D hC.alpha, Commute e y) :
    Halpha D hC.alpha ≤ Subgroup.centralizer ({y} : Set G) := by
  rw [Halpha, Subgroup.closure_le]
  intro e he
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (hy e he).eq

theorem mem_block_of_commute_imp (hC : HypothesisC D) (hH : Th91Hyp D hC)
    {β : Set G} (hβ : β ∈ blockClass hC.alpha) {x y : G} (hx : x ∈ β) (hy : y ∈ D)
    (h : ∀ e ∈ D, Commute e x → Commute e y) : y ∈ β := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have hy₀D : g⁻¹ * y * g⁻¹⁻¹ ∈ D := hC.setup.conj_mem g⁻¹ hy
  rw [inv_inv] at hy₀D
  refine ⟨g⁻¹ * y * g, ?_, by group⟩
  have hEcomm : ∀ e ∈ DalphaStar D hC.alpha, Commute e (g⁻¹ * y * g) := by
    intro e he
    have heD : e ∈ D := DalphaStar_subset hC.isBlock_alpha he
    have hex : Commute (g * e * g⁻¹) (g * x₀ * g⁻¹) :=
      (commute_of_mem_alpha_of_mem_DalphaStar hC hx₀ he).symm.conj g
    have hey := (h (g * e * g⁻¹) (hC.setup.conj_mem g heD) hex).conj g⁻¹
    rwa [inv_inv, show g⁻¹ * (g * e * g⁻¹) * g = e by group] at hey
  rw [hC.alpha_eq_normSet_diff, ← hC.DalphaStar_alpha]
  refine ⟨⟨hy₀D, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩, fun hy₀ => ?_⟩
  · rw [(hEcomm e he).symm.eq, mul_inv_cancel_right]
    exact he
  · have hc := (hEcomm _ he).eq
    have : e = (g⁻¹ * y * g) * e * (g⁻¹ * y * g)⁻¹ := by
      calc e = (g⁻¹ * y * g)⁻¹ * ((g⁻¹ * y * g) * e * (g⁻¹ * y * g)⁻¹) * (g⁻¹ * y * g) := by
            group
        _ = (g⁻¹ * y * g) * e * (g⁻¹ * y * g)⁻¹ := by
            rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact he
  · obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute_DalphaStar hC hH
    have hcent := Halpha_le_centralizer_of_forall_commute hC hEcomm
    have hfix : ∀ c ∈ DalphaStar D hC.alpha, c = g⁻¹ * y * g := by
      intro c hc
      obtain ⟨k, hk, hkc⟩ := hC.Halpha_transitive _ hy₀ c hc
      rw [← hkc, Subgroup.mem_centralizer_singleton_iff.mp (hcent hk), mul_inv_cancel_right]
    exact hab (by rw [hfix a ha, hfix b hb])

theorem mem_block_of_mul_mem (hC : HypothesisC D) (hH : Th91Hyp D hC) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {v y : G} (hv : v ∈ β) (hvD : v ∈ D) (hy : y ∈ D)
    (hne : v ≠ y) (hc : Commute v y) (hvy : v * y ∈ D) : y ∈ β :=
  mem_block_of_commute_imp hC hH hβ hv hy fun e he hev => by
    have h := (centralizer_eq_of_mul_mem hC.setup hvD hy hne hc hvy).1
    have he' : e ∈ D ∩ Subgroup.centralizer ({v} : Set G) :=
      ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr hev.eq⟩
    rw [h] at he'
    exact Subgroup.mem_centralizer_singleton_iff.mp he'.2

theorem mem_block_or_DalphaStar_of_commute (hC : HypothesisC D) {γ : Set G}
    (hγ : γ ∈ blockClass hC.alpha) {x e : G} (hx : x ∈ γ) (he : e ∈ D) (hxe : Commute x e) :
    e ∈ γ ∨ e ∈ DalphaStar D γ := by
  by_cases heγ : e ∈ γ
  · exact Or.inl heγ
  right
  have hγb : IsBlock D γ := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ
  obtain ⟨δ, hδ, heδ⟩ := exists_mem_blockClass_of_mem hC.setup.isClass hγb he
  have hδγ : δ ≠ γ := fun h => heγ (h ▸ heδ)
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hδ
  have hcomm := commute_block_of_mem_apply hC.setup.normal hC.setup.oddT hγb hδγ hx heδ hxe
  exact ⟨_, ⟨hδ, fun b hb => by
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact hC.setup.conj_mem g (hγb.subset hb₀), hδγ, hcomm⟩, heδ⟩

omit [Finite G] in
theorem DalphaStar_conj_eq (hC : HypothesisC D) (g : G) :
    DalphaStar D ((fun x => g * x * g⁻¹) '' hC.alpha) =
      (fun x => g * x * g⁻¹) '' DalphaStar D hC.alpha := by
  ext y
  constructor
  · intro hy
    have h := DalphaStar.conj hC.setup.normal hy g⁻¹
    rw [Set.image_image] at h
    simp only [inv_inv, show ∀ x : G, g⁻¹ * (g * x * g⁻¹) * g = x from fun x => by group,
      Set.image_id'] at h
    exact ⟨g⁻¹ * y * g, h, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact DalphaStar.conj hC.setup.normal hx g

theorem DalphaStar_ne_block (hC : HypothesisC D) (hH : Th91Hyp D hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) : DalphaStar D hC.alpha ≠ β := by
  classical
  intro hE
  obtain ⟨hβc, hβD, hβα, hαβ⟩ := mem_Dalpha_iff.mp hβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβc
  have hinj : Function.Injective fun x : G => g * x * g⁻¹ := fun a b h => by
    simpa using h
  have hαDβ : hC.alpha ∈ Dalpha D β := by
    refine ⟨mem_blockClass_of_mem_blockClass hβc (mem_blockClass_self _),
      hC.isBlock_alpha.subset, hβα.symm, fun b hb a ha => (hαβ a ha b hb).symm⟩
  have hDβ : DalphaStar D β = hC.alpha := by
    refine (Set.eq_of_subset_of_ncard_le (subset_DalphaStar hαDβ) ?_ (Set.toFinite _)).symm
    rw [hg, DalphaStar_conj_eq hC g, Set.ncard_image_of_injective _ hinj, hE, hg,
      Set.ncard_image_of_injective _ hinj]
  have hclosed : ∀ x ∈ hC.alpha ∪ β, ∀ e ∈ D, Commute x e → e ∈ hC.alpha ∪ β := by
    rintro x (hx | hx) e he hxe
    · rcases mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) hx he hxe with h | h
      · exact Or.inl h
      · exact Or.inr (hE ▸ h)
    · rcases mem_block_or_DalphaStar_of_commute hC hβc hx he hxe with h | h
      · exact Or.inr h
      · exact Or.inl (hDβ ▸ h)
  have hDsub : ∀ d ∈ D, d ∈ hC.alpha ∪ β := fun d hd =>
    mem_of_reach hclosed (Or.inl hC.d_mem_alpha) (reach_of_not_disconnected hC.conn hC.hd hd)
  have hnorm : ∀ d ∈ D, d ∈ Subgroup.normalizer β := by
    intro d hd
    rcases hDsub d hd with hdα | hdβ
    · obtain ⟨b, hb⟩ := blockClass_nonempty hC.isBlock_alpha.nonempty hβc
      refine mem_normalizer_block_of_conj_mem hC hβc hb ?_
      rw [(hαβ d hdα b hb).eq, mul_inv_cancel_right]
      exact hb
    · exact mem_normalizer_block_of_conj_mem hC hβc hdβ (by rw [mul_inv_cancel_right]; exact hdβ)
  have hnormG : ∀ c : G, c ∈ Subgroup.normalizer β := by
    have hle : Subgroup.closure D ≤ Subgroup.normalizer β := Subgroup.closure_le _ |>.mpr hnorm
    rw [hC.setup.gen] at hle
    exact fun c => hle (Subgroup.mem_top c)
  have hcommD : ∀ d ∈ D, ∀ b ∈ β, Commute d b := by
    intro d hd b hb
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hd)
    have hb' : c⁻¹ * b * c⁻¹⁻¹ ∈ β := (hnormG c⁻¹ b).mp hb
    rw [inv_inv] at hb'
    have h := (hαβ hC.d hC.d_mem_alpha _ hb').conj c
    rwa [show c * (c⁻¹ * b * c) * c⁻¹ = b by group] at h
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute_DalphaStar hC hH
  rw [hE] at ha hb
  exact hab (hcommD a (hβD ha) b hb)

theorem mem_sylow_of_mem_sup_center {K : Type} [Group K] [Finite K]
    (hOZ : CFSG.oddCore K ≤ Subgroup.center K) (T : Sylow 2 K) {w : K}
    (hw : w ∈ (T : Subgroup K) ⊔ Subgroup.center K) (hw2 : w * w = 1) : w ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (T : Subgroup K) ⊔ Subgroup.center K ≤ (T : Subgroup K) ⊔ CFSG.oddCore K :=
    sup_le le_sup_left (center_le_pCore_sup_oddCore.trans
      (sup_le ((CFSG.fitting_pCore_le_sylow T).trans le_sup_left) le_sup_right))
  obtain ⟨t, ht, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hle hw)
  have hoc : ∀ x : K, o * x = x * o := fun x => Subgroup.mem_center_iff.mp (hOZ ho) x |>.symm
  have hodd : Odd (Nat.card (CFSG.oddCore K)) := CFSG.ABGLocalTools.odd_card_oddCore
  have hTO : (T : Subgroup K) ⊓ CFSG.oddCore K = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  have ho2 : o * o = 1 := by
    have hto : Commute t o := (hoc t).symm
    have h1 : t ^ 2 * o ^ 2 = 1 := by rw [← hto.mul_pow, pow_two]; exact hw2
    have h2 : o ^ 2 = (t ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmem : o ^ 2 ∈ (T : Subgroup K) ⊓ CFSG.oddCore K :=
      ⟨h2 ▸ (T : Subgroup K).inv_mem ((T : Subgroup K).pow_mem ht 2),
        (CFSG.oddCore K).pow_mem ho 2⟩
    rw [hTO, Subgroup.mem_bot, pow_two] at hmem
    exact hmem
  have ho1 : o = 1 := by
    have hord : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
    have hoddo : Odd (orderOf o) := by
      rw [← Subgroup.orderOf_mk o ho]
      exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hoddo
      exact absurd hoddo (by decide)
  rw [ho1, mul_one]
  exact ht

theorem block_subset_sylow (hC : HypothesisC D) (hH : Th91Hyp D hC)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : v ∈ β)
    (T : Sylow 2 (Halpha D hC.alpha))
    (hvT : v ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hTv : ∀ t ∈ (T : Subgroup (Halpha D hC.alpha)), (t : G) * v * (t : G)⁻¹ = v) :
    β ⊆ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβc : β ∈ blockClass hC.alpha := (mem_Dalpha_iff.mp hβ).1
  have hβH : β ⊆ Halpha D hC.alpha := fun x hx =>
    Subgroup.subset_closure (subset_DalphaStar hβ hx)
  have hvH : v ∈ Halpha D hC.alpha := hβH hv
  let Nβ : Subgroup (Halpha D hC.alpha) :=
    (Subgroup.normalizer β).comap (Halpha D hC.alpha).subtype
  have hTN : (T : Subgroup (Halpha D hC.alpha)) ≤ Nβ := fun t ht =>
    mem_normalizer_block_of_conj_mem hC hβc hv ((hTv t ht).symm ▸ hv)
  have hZN : Subgroup.center (Halpha D hC.alpha) ≤ Nβ := by
    intro z hz
    refine mem_normalizer_block_of_conj_mem hC hβc hv ?_
    have hzv : (z : G) * v = v * z :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨v, hvH⟩).symm
    show (z : G) * v * (z : G)⁻¹ ∈ β
    rw [hzv, mul_inv_cancel_right]
    exact hv
  let π := QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Tb : Sylow 2 (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
    T.mapSurjective hπs
  have hfus := CFSG.StronglyEmbedded.BenderCentre.fusionIsBenderGroup_of_isBenderGroup hH.bender
  have hTbN : (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) ≤
      Nβ.map π := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hTN
  have hNβcomap : (Nβ.map π).comap π = Nβ := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr hZN
  have hconj : ∀ w ∈ β, ∃ h ∈ Nβ, (h : G) * v * (h : G)⁻¹ = w := by
    intro w hw
    obtain ⟨h, hh, hhw⟩ := hC.Halpha_transitive v (subset_DalphaStar hβ hv) w
      (subset_DalphaStar hβ hw)
    exact ⟨⟨h, hh⟩, mem_normalizer_block_of_conj_mem hC hβc hv (hhw ▸ hw), hhw⟩
  rcases CFSG.ComponentClassification.RankTwoBender.le_normalizer_or_eq_top hfus Tb hTbN with
    hle | htop
  · intro w hw
    obtain ⟨h, hhN, rfl⟩ := hconj w hw
    obtain ⟨v', hv'T, hv'⟩ := Subgroup.mem_map.mp hvT
    have hv'v : (v' : G) = v := hv'
    have hhn := hle (Subgroup.mem_map_of_mem π hhN)
    have hv'b :
        π v' ∈ (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π hv'T
    have hcj : π (h * v' * h⁻¹) ∈
        (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) := by
      rw [map_mul, map_mul, map_inv]
      exact (hhn _).mp hv'b
    have hmem : h * v' * h⁻¹ ∈
        (T : Subgroup (Halpha D hC.alpha)) ⊔ Subgroup.center (Halpha D hC.alpha) := by
      have : h * v' * h⁻¹ ∈
          (Tb : Subgroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))).comap π := hcj
      rwa [Sylow.coe_mapSurjective, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    have hv'2 : v' * v' = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, hv'v, Subgroup.coe_one]
      exact hC.setup.oddT.mul_self_eq_one (DalphaStar_subset hC.isBlock_alpha
        (subset_DalphaStar hβ hv)))
    have hsq : (h * v' * h⁻¹) * (h * v' * h⁻¹) = 1 := by
      calc (h * v' * h⁻¹) * (h * v' * h⁻¹) = h * (v' * v') * h⁻¹ := by group
        _ = 1 := by rw [hv'2, mul_one, mul_inv_cancel]
    have hT := mem_sylow_of_mem_sup_center (oddCore_le_center_of_isBenderGroup hH.bender) T
      hmem hsq
    refine Subgroup.mem_map.mpr ⟨_, hT, ?_⟩
    simp [hv'v]
  · exfalso
    have hNtop : Nβ = ⊤ := by rw [← hNβcomap, htop, Subgroup.comap_top]
    apply DalphaStar_ne_block hC hH hβ
    refine Set.Subset.antisymm (fun w hw => ?_) (subset_DalphaStar hβ)
    obtain ⟨h, hh, hhw⟩ := hC.Halpha_transitive v (subset_DalphaStar hβ hv) w hw
    have hhN : (⟨h, hh⟩ : Halpha D hC.alpha) ∈ Nβ := hNtop ▸ Subgroup.mem_top _
    rw [← hhw]
    exact (hhN v).mp hv

theorem eq_one_of_commute_centSet (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hαc : ∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b)
    {v : G} (hv : v ∈ DalphaStar D hC.alpha) {x : G}
    (hxu : ∀ e ∈ D, Commute e hC.d → Commute x e) (hxv : ∀ e ∈ D, Commute e v → Commute x e) :
    x = 1 := by
  classical
  set A : Set G := {e | e ∈ D ∧ Commute e hC.d} ∪ {e | e ∈ D ∧ Commute e v} with hA
  have hAD : A ⊆ D := by rintro e (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
  set X := Subgroup.closure A with hX
  have hXD : X = Subgroup.closure ((X : Set G) ∩ D) :=
    le_antisymm (Subgroup.closure_le _ |>.mpr fun e he =>
        Subgroup.subset_closure ⟨Subgroup.subset_closure he, hAD he⟩)
      (Subgroup.closure_le _ |>.mpr fun e he => he.1)
  have hdX : hC.d ∈ X := Subgroup.subset_closure (Or.inl ⟨hC.hd, Commute.refl _⟩)
  have hEX : hC.E ⊆ (X : Set G) := by
    intro e he
    have he' : e ∈ DalphaStar D hC.alpha := hC.DalphaStar_alpha ▸ he
    exact Subgroup.subset_closure (Or.inl (hC.DalphaStar_subset_commute he'))
  by_cases hXtop : X = ⊤
  ·
    have hxc : ∀ g : G, Commute x g := by
      intro g
      have hg : g ∈ X := hXtop ▸ Subgroup.mem_top g
      induction hg using Subgroup.closure_induction with
      | mem e he =>
        rcases he with ⟨he, heu⟩ | ⟨he, hev⟩
        · exact hxu e he heu
        · exact hxv e he hev
      | one => exact Commute.one_right x
      | mul a b _ _ ha hb => exact ha.mul_right hb
      | inv a _ ha => exact ha.inv_right
    have hxZ : x ∈ Subgroup.center G :=
      Subgroup.mem_center_iff.mpr fun g => (hxc g).eq.symm
    have hZ := hH.solv (Subgroup.center G) inferInstance inferInstance
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact hxZ
  · exfalso
    have h68 := inter_D_subset_perp hC hXD hdX hEX hXtop
    have hsub : {e | e ∈ D ∧ Commute e v} ⊆ {e | e ∈ D ∧ Commute e hC.d} := by
      intro e he
      have heX : e ∈ (X : Set G) ∩ D := ⟨Subgroup.subset_closure (Or.inr he), he.1⟩
      rcases h68 heX with heα | heE
      · exact ⟨he.1, hαc e heα _ hC.d_mem_alpha⟩
      · exact hC.DalphaStar_subset_commute heE
    obtain ⟨γ, hγ, hvγ⟩ := hv
    have huγ : hC.d ∈ γ := mem_block_of_commute_imp hC hH (mem_Dalpha_iff.mp hγ).1 hvγ hC.hd
      fun e he hev => (hsub ⟨he, hev⟩).2
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp (mem_Dalpha_iff.mp hγ).1
    have hgN : g ∉ Subgroup.normalizer hC.alpha := by
      intro hgN
      exact (mem_Dalpha_iff.mp hγ).2.2.1 (hg.trans (conj_image_block_eq hgN))
    exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hgN) hC.d_mem_alpha (hg ▸ huγ)

end CFSG.OddTranspositions.PartThree.Nine
