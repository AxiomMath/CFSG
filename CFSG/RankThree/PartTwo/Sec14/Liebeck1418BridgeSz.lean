module

public import CFSG.RankThree.PartTwo.Sec4.Item41PRankNarrow41
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

private theorem pRank_five_normalizer_le_two {X : Type} [Group X] [Finite X]
    (hX : SectionFourHyp X) {T : Subgroup X} (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (Subgroup.normalizer (T : Set X))) ≤ 2 := by
  have h1 := CFSG.RankThree.OddKernel.pRank_normalizer_le_localRank (p := 5) (by norm_num) hT1 hT2
  have h2 := hX.localRank_lt 5 (by norm_num) (by norm_num)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  omega

private theorem pRank_five_le_of_section {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    (h41 : Sec4.Item4_1PRankLargePrime) (h3 : CFSG.Open.pRank 5 (⊤ : Subgroup G) ≤ 3)
    {M W : Type} [Group M] [Group W] [Finite W] (ι : M →* G) (hι : Function.Injective ι)
    (g : M →* W) (hg : Function.Surjective g) (hW : layer W = ⊤) :
    CFSG.Open.pRank 5 (⊤ : Subgroup W) ≤ CFSG.Open.pRank 5 (⊤ : Subgroup G) := by
  set H : Subgroup G := ι.range
  let e : M ≃* H := MonoidHom.ofInjective hι
  let gg : H →* W := g.comp e.symm.toMonoidHom
  have hgg : Function.Surjective gg := hg.comp e.symm.surjective
  let eQ : H ⧸ gg.ker ≃* W := QuotientGroup.quotientKerEquivOfSurjective gg hgg
  have hlay : layer (H ⧸ gg.ker) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hW eQ.symm.toMonoidHom eQ.symm.surjective
  have h := h41 G hG H gg.ker hlay 5 (by norm_num) (by norm_num) h3
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eQ] at h

theorem false_of_section_pRank_five {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    (h41 : Sec4.Item4_1PRankLargePrime) {D : Subgroup X} {S : Subgroup D} [S.Normal]
    {T W : Subgroup (D ⧸ S)} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hWT : W ≤ Subgroup.normalizer (T : Set (D ⧸ S))) (hWT' : W ⊓ T = ⊥)
    (hWl : layer W = ⊤) (hW5 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup W)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Tsyl⟩ : Nonempty (Sylow 2 (T.comap (QuotientGroup.mk' S))) := inferInstance
  obtain ⟨hmap, hnorm, -⟩ := CFSG.RankThree.OddKernel.sylow_preimage_map_normalizer S T hT2 Tsyl
  set T₀ : Subgroup D := (Tsyl : Subgroup (T.comap (QuotientGroup.mk' S))).map
    (T.comap (QuotientGroup.mk' S)).subtype
  have hT₀2 : IsPGroup 2 T₀ := Tsyl.isPGroup'.map _
  have hT₀1 : T₀ ≠ ⊥ := fun h => hT1 (by rw [← hmap, h, Subgroup.map_bot])
  set Ts : Subgroup X := T₀.map D.subtype
  have hTs2 : IsPGroup 2 Ts := hT₀2.map _
  have hTs1 : Ts ≠ ⊥ := fun h =>
    hT₀1 ((Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h)
  set G' : Subgroup X := Subgroup.normalizer (Ts : Set X)
  have hG'S : SectionFourHyp G' := Sec4.sectionFourHyp_subgroup hX G'
  have h5 : CFSG.Open.pRank 5 (⊤ : Subgroup G') ≤ 2 := pRank_five_normalizer_le_two hX hTs1 hTs2
  set M₀ : Subgroup D := Subgroup.normalizer (T₀ : Set D) ⊓ W.comap (QuotientGroup.mk' S)
  have hmem : ∀ m : M₀, ((m : D) : X) ∈ G' := fun m => by
    have h := Subgroup.le_normalizer_map (H := T₀) D.subtype
    exact h (Subgroup.mem_map_of_mem _ m.2.1)
  let ι : M₀ →* G' := (D.subtype.comp M₀.subtype).codRestrict G' hmem
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (D.subtype_injective (congrArg (fun z : G' => (z : X)) h))
  let g : M₀ →* W := ((QuotientGroup.mk' S).comp M₀.subtype).codRestrict W fun m => m.2.2
  have hg : Function.Surjective g := by
    intro w
    have hw : (w : D ⧸ S) ∈ (Subgroup.normalizer (T₀ : Set D)).map (QuotientGroup.mk' S) := by
      rw [hnorm]
      exact hWT w.2
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
    exact ⟨⟨y, hy, by have := w.2; rwa [← hyw] at this⟩, Subtype.ext hyw⟩
  have := pRank_five_le_of_section hG'S h41 (h5.trans (by norm_num)) ι hι g hg hWl
  omega

private theorem comm_of_ne {Ω : Type*} [Group Ω] [Finite Ω] {K L : Subgroup Ω}
    (hK : IsComponent K) (hL : IsComponent L) (hne : K ≠ L) :
    ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · intro a ha b hb
    have hle : K ≤ Subgroup.centralizer (L : Set Ω) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

private theorem eq_one_of_forall_commute {Ω : Type*} [Group Ω] {K : Subgroup Ω}
    (hK : IsComponent K) (hs : IsSimpleGroup K) :
    ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1 := by
  intro x hx hc
  have hmem : (⟨x, hx⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    exact fun y => Subtype.ext (hc y y.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a')) b').symm

theorem false_of_four_components {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    (h41 : Sec4.Item4_1PRankLargePrime) {D : Subgroup X} {S : Subgroup D} [S.Normal]
    (Y : Fin 4 → Subgroup (D ⧸ S)) (hY : ∀ i, IsComponent (Y i)) (hinj : Function.Injective Y)
    (hsimple : ∀ i, IsSimpleGroup (Y i)) (h5 : ∀ i, 5 ∣ Nat.card (Y i))
    (h2 : ∀ i, 2 ∣ Nat.card (Y i)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcomm : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ Y i, ∀ b ∈ Y j, a * b = b * a := fun i j hij =>
    comm_of_ne (hY i) (hY j) fun h => hij (hinj h)
  have hZ : ∀ i : Fin 4, ∀ x ∈ Y i, (∀ y ∈ Y i, x * y = y * x) → x = 1 := fun i =>
    eq_one_of_forall_commute (hY i) (hsimple i)
  set W : Subgroup (D ⧸ S) := Y 1 ⊔ Y 2 ⊔ Y 3
  have hWcent : W ≤ Subgroup.centralizer (Y 0 : Set (D ⧸ S)) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro b hb <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro a ha
    · exact hcomm 0 1 (by decide) a ha b hb
    · exact hcomm 0 2 (by decide) a ha b hb
    · exact hcomm 0 3 (by decide) a ha b hb
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (h2 0)
  have ht2 : orderOf (t : D ⧸ S) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hTY : Subgroup.zpowers (t : D ⧸ S) ≤ Y 0 := Subgroup.zpowers_le.mpr t.2
  have hT2 : IsPGroup 2 (Subgroup.zpowers (t : D ⧸ S)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hT1 : Subgroup.zpowers (t : D ⧸ S) ≠ ⊥ := by
    intro h
    have h1 : (t : D ⧸ S) = 1 := by
      have := Subgroup.mem_zpowers (t : D ⧸ S)
      rwa [h, Subgroup.mem_bot] at this
    rw [h1, orderOf_one] at ht2
    omega
  have hWT : W ≤ Subgroup.normalizer (Subgroup.zpowers (t : D ⧸ S) : Set (D ⧸ S)) :=
    hWcent.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTY)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hWT' : W ⊓ Subgroup.zpowers (t : D ⧸ S) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huW, huT⟩
    rw [Subgroup.mem_bot]
    exact hZ 0 u (hTY huT) fun y hy => (Subgroup.mem_centralizer_iff.mp (hWcent huW) y hy).symm
  have hY1W : Y 1 ≤ W := le_sup_left.trans le_sup_left
  have hY2W : Y 2 ≤ W := le_sup_right.trans le_sup_left
  have hY3W : Y 3 ≤ W := le_sup_right
  have hYle : ∀ i : Fin 4, Y i ≤ W → Y i ≤ (layer W).map W.subtype := fun i hi x hx =>
    ⟨⟨x, hi hx⟩, CFSG.LocalCores.component_le_layer
      (CFSG.LocalCores.component_overgroup (hY i) hi) (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hWl : layer W = ⊤ := by
    have hWle : W ≤ (layer W).map W.subtype :=
      sup_le (sup_le (hYle 1 hY1W) (hYle 2 hY2W)) (hYle 3 hY3W)
    rw [eq_top_iff]
    intro w _
    obtain ⟨l, hl, hlw⟩ := hWle w.2
    have hlw' : l = w := Subtype.ext hlw
    rwa [hlw'] at hl
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' 5 (h5 1)
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' 5 (h5 2)
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' 5 (h5 3)
  have ho₁ : orderOf (x₁ : D ⧸ S) = 5 := (Subgroup.orderOf_coe x₁).trans hx₁
  have ho₂ : orderOf (x₂ : D ⧸ S) = 5 := (Subgroup.orderOf_coe x₂).trans hx₂
  have ho₃ : orderOf (x₃ : D ⧸ S) = 5 := (Subgroup.orderOf_coe x₃).trans hx₃
  have hpow : ∀ {x : D ⧸ S}, orderOf x = 5 → x ^ 5 = 1 := fun {x} h => by
    rw [← h]
    exact pow_orderOf_eq_one x
  have hne : ∀ {x : D ⧸ S}, orderOf x = 5 → x ≠ 1 := fun {x} h h1 => by
    rw [h1, orderOf_one] at h
    omega
  have hzx : (x₂ : D ⧸ S) ∉ Subgroup.zpowers (x₁ : D ⧸ S) := fun h =>
    hne ho₂ (hZ 1 _ (Subgroup.zpowers_le.mpr x₁.2 h) fun y hy =>
      (hcomm 1 2 (by decide) y hy _ x₂.2).symm)
  have hcxz : (x₃ : D ⧸ S) ∉ Subgroup.zpowers (x₁ : D ⧸ S) ⊔ Subgroup.zpowers (x₂ : D ⧸ S) := by
    intro h
    have h12 : Y 1 ⊔ Y 2 ≤ Subgroup.centralizer (Y 3 : Set (D ⧸ S)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
        intro b hb
      · exact (hcomm 1 3 (by decide) a ha b hb).symm
      · exact (hcomm 2 3 (by decide) a ha b hb).symm
    refine hne ho₃ (hZ 3 _ x₃.2 fun y hy => ?_)
    exact ((Subgroup.mem_centralizer_iff.mp (h12 (sup_le_sup (Subgroup.zpowers_le.mpr x₁.2)
      (Subgroup.zpowers_le.mpr x₂.2) h)) y hy).symm)
  have hW5 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup W) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.PartOne.Torsion37.three_le_pRank_of_commuting (by norm_num) (hY1W x₁.2)
      (hY2W x₂.2) (hY3W x₃.2) (hcomm 1 2 (by decide) _ x₁.2 _ x₂.2)
      (hcomm 1 3 (by decide) _ x₁.2 _ x₃.2) (hcomm 2 3 (by decide) _ x₂.2 _ x₃.2) (hpow ho₁)
      (hpow ho₂) (hpow ho₃) (hne ho₁) (hne ho₂) hzx hcxz
  exact false_of_section_pRank_five hX h41 hT2 hT1 hWT hWT' hWl hW5

end CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge
