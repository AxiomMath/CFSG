module

public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S2b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

@[expose] def star (B N H : Subgroup G) [(N.subgroupOf B).Normal] :
    Subgroup (↥B ⧸ N.subgroupOf B) :=
  (H.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B))

omit [Finite G] in
theorem mk_mem_star {B N H : Subgroup G} [(N.subgroupOf B).Normal] {h : G} (hB : h ∈ B)
    (hH : h ∈ H) : QuotientGroup.mk' (N.subgroupOf B) ⟨h, hB⟩ ∈ star B N H :=
  Subgroup.mem_map.mpr ⟨⟨h, hB⟩, Subgroup.mem_subgroupOf.mpr hH, rfl⟩

omit [Finite G] in
theorem mem_star_iff {B N H : Subgroup G} [(N.subgroupOf B).Normal]
    {q : ↥B ⧸ N.subgroupOf B} :
    q ∈ star B N H ↔
      ∃ (h : G) (hB : h ∈ B), h ∈ H ∧ QuotientGroup.mk' (N.subgroupOf B) ⟨h, hB⟩ = q := by
  constructor
  · rintro ⟨⟨h, hB⟩, hH, rfl⟩
    exact ⟨h, hB, Subgroup.mem_subgroupOf.mp hH, rfl⟩
  · rintro ⟨h, hB, hH, rfl⟩
    exact mk_mem_star hB hH

omit [Finite G] in
theorem star_mono {B N H H' : Subgroup G} [(N.subgroupOf B).Normal] (h : H ≤ H') :
    star B N H ≤ star B N H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite G] in
theorem star_eq_bot_iff {B N H : Subgroup G} [(N.subgroupOf B).Normal] (hH : H ≤ B) :
    star B N H = ⊥ ↔ H ≤ N := by
  constructor
  · intro h x hx
    have := mk_mem_star (N := N) (hH hx) hx
    rw [h, Subgroup.mem_bot] at this
    exact (mk_eq_one_iff (hH hx)).mp this
  · intro h
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, hxB, hx, rfl⟩ := mem_star_iff.mp hq
    exact (Subgroup.mem_bot).mpr ((mk_eq_one_iff hxB).mpr (h hx))

omit [Finite G] in
theorem star_normal {B N H : Subgroup G} [(N.subgroupOf B).Normal]
    (hBH : B ≤ Subgroup.normalizer (H : Set G)) : (star B N H).Normal := by
  have hn : (H.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBH
  exact hn.map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem star_sup_eq {B N H : Subgroup G} [(N.subgroupOf B).Normal] (hH : H ≤ B) (hN : N ≤ B) :
    star B N (H ⊔ N) = star B N H := by
  have h1 : star B N N = ⊥ := (star_eq_bot_iff hN).mpr le_rfl
  unfold star at h1 ⊢
  rw [Subgroup.subgroupOf_sup hH hN, Subgroup.map_sup, h1, sup_bot_eq]

omit [Finite G] in
theorem star_commutator {B N H K : Subgroup G} [(N.subgroupOf B).Normal] (hH : H ≤ B)
    (hK : K ≤ B) : star B N ⁅H, K⁆ = ⁅star B N H, star B N K⁆ := by
  unfold star
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective B.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH, inf_eq_left.mpr hK,
    inf_eq_left.mpr ((Subgroup.commutator_mono hH hK).trans (A3.commutator_self_le B))]

omit [Finite G] in
theorem isSolvable_star {B N H : Subgroup G} [(N.subgroupOf B).Normal] (hH : H ≤ B)
    (hs : Group.IsSolvable ↥H) : Group.IsSolvable ↥(star B N H) := by
  have : Group.IsSolvable ↥(H.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hH).injective
  exact Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (N.subgroupOf B)).subgroupMap_surjective (H.subgroupOf B))

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem isSolvable_TD : Group.IsSolvable ↥(T ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable ↥D := CFSG.Milestones.odd_order_solvable H.h.Dodd
  have : Group.IsNilpotent ↥T := H.h.sylow.1.isNilpotent
  exact A3.isSolvable_sup_of_le_normalizer H.h.DN

theorem le_normalizer_commutator :
    X ⊔ T ⊔ D ≤ Subgroup.normalizer
      ((⁅conjClosure X D, conjClosure X D⁆ : Subgroup G) : Set G) := by
  set Y := conjClosure X D with hY
  refine Main3324.le_normalizer_of_conj fun g hg c hc => ?_
  have hle : ⁅Y, Y⁆ ≤ ⁅Y, Y⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅a, b⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator
      ((Subgroup.mem_normalizer_iff.mp (H.hBY hg) a).mp ha)
      ((Subgroup.mem_normalizer_iff.mp (H.hBY hg) b).mp hb)
  have := hle hc
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

omit [Finite G] H in
theorem star_Y_perfect (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    ⁅star (X ⊔ T ⊔ D) B₀ (conjClosure X D), star (X ⊔ T ⊔ D) B₀ (conjClosure X D)⁆ =
      star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
  set Y := conjClosure X D with hYdef
  have hYB : Y ≤ X ⊔ T ⊔ D := Y_le_B
  have hYY : ⁅Y, Y⁆ ≤ X ⊔ T ⊔ D :=
    (Subgroup.commutator_mono hYB hYB).trans (A3.commutator_self_le _)
  refine le_antisymm (A3.commutator_self_le _) ?_
  rw [← star_commutator hYB hYB]
  calc star (X ⊔ T ⊔ D) B₀ Y ≤ star (X ⊔ T ⊔ D) B₀ (⁅Y, Y⁆ ⊔ B₀) := star_mono hY
    _ = star (X ⊔ T ⊔ D) B₀ ⁅Y, Y⁆ := star_sup_eq hYY hB.le

theorem star_Y_ne_bot (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    star (X ⊔ T ⊔ D) B₀ (conjClosure X D) ≠ ⊥ := by
  rw [Ne, star_eq_bot_iff Y_le_B]
  exact fun h => H.not_X_le_B₀ hB.inf ((le_conjClosure X D).trans h)

theorem not_isSolvable_star_Y (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    ¬ Group.IsSolvable ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) := by
  intro hs
  rw [isSolvable_iff_perfectCore_eq_bot,
    perfectCore_eq_self_of_perfect (star_Y_perfect hB hY)] at hs
  exact H.star_Y_ne_bot hB hs

theorem le_B₀_of_isSolvable (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀) {N : Subgroup G}
    (hNB : N ≤ X ⊔ T ⊔ D) (hBN : X ⊔ T ⊔ D ≤ Subgroup.normalizer (N : Set G))
    (hs : Group.IsSolvable ↥N) : N ≤ B₀ := by
  have hN : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  by_contra hcon
  have hlt : B₀ < N ⊔ B₀ := lt_of_le_of_ne le_sup_right fun h => hcon (le_sup_left.trans h.symm.le)
  have hNn : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((N ⊔ B₀ : Subgroup G) : Set G) := fun g hg =>
    ChiefCount.mem_normalizer_sup (hBN hg) (hB.nor hg)
  have hYN := (H.X_le_of_normal hNn (hB.max _ hlt (sup_le hNB hB.le) hNn)).2
  apply H.not_isSolvable_star_Y hB hY
  have h1 : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) ≤ star (X ⊔ T ⊔ D) B₀ N := by
    rw [← star_sup_eq hNB hB.le]
    exact star_mono hYN
  have hsN := isSolvable_star (N := B₀) hNB hs
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)

theorem star_le_star_Y [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {K : Subgroup G}
    (hKB : K ≤ X ⊔ T ⊔ D) (hK : ⁅K, K⁆ = K) :
    star (X ⊔ T ⊔ D) B₀ K ≤ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
  set Q := ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)
  set Ŷ := star (X ⊔ T ⊔ D) B₀ (conjClosure X D) with hŶ
  have hYn : Ŷ.Normal := star_normal H.hBY
  have hTDB : T ⊔ D ≤ X ⊔ T ⊔ D := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  let f : ↥(T ⊔ D) →* Q ⧸ Ŷ := (QuotientGroup.mk' Ŷ).comp
    ((QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))).comp (Subgroup.inclusion hTDB))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Ŷ z
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk'_surjective (B₀.subgroupOf (X ⊔ T ⊔ D)) q
    obtain ⟨y, hy, k, hk, rfl⟩ := H.mem_Y_TD hb
    refine ⟨⟨k, hk⟩, ?_⟩
    have e : (⟨y * k, hb⟩ : ↥(X ⊔ T ⊔ D)) = ⟨y, Y_le_B hy⟩ * ⟨k, hTDB hk⟩ := rfl
    have hy1 : QuotientGroup.mk' Ŷ (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))
        ⟨y, Y_le_B hy⟩) = 1 := (QuotientGroup.eq_one_iff _).mpr (mk_mem_star (Y_le_B hy) hy)
    simp only [f, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, hy1, one_mul]
    rfl
  have hQs : Group.IsSolvable (Q ⧸ Ŷ) := by
    have := H.isSolvable_TD
    exact Group.isSolvable_of_surjective hf
  have hKp : ⁅star (X ⊔ T ⊔ D) B₀ K, star (X ⊔ T ⊔ D) B₀ K⁆ = star (X ⊔ T ⊔ D) B₀ K := by
    rw [← star_commutator hKB hKB, hK]
  have h1 : (star (X ⊔ T ⊔ D) B₀ K).map (QuotientGroup.mk' Ŷ) = ⊥ := by
    have hp : ⁅(star (X ⊔ T ⊔ D) B₀ K).map (QuotientGroup.mk' Ŷ),
        (star (X ⊔ T ⊔ D) B₀ K).map (QuotientGroup.mk' Ŷ)⁆ =
        (star (X ⊔ T ⊔ D) B₀ K).map (QuotientGroup.mk' Ŷ) := by
      rw [← Subgroup.map_commutator, hKp]
    have hle := le_perfectCore_of_perfect (le_top :
      (star (X ⊔ T ⊔ D) B₀ K).map (QuotientGroup.mk' Ŷ) ≤ ⊤) hp
    have hsol : Group.IsSolvable ↥(⊤ : Subgroup (Q ⧸ Ŷ)) := inferInstance
    rw [(isSolvable_iff_perfectCore_eq_bot ⊤).mp hsol] at hle
    exact le_bot_iff.mp hle
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

theorem inf_B₀_eq_solvRad (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀) {K : Subgroup G}
    (hK : K ∈ cComp (X ⊔ T ⊔ D)) (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G))
    (hKB₀ : ¬ K ≤ B₀) : K ⊓ B₀ = solvRad K := by
  have hKB : K ≤ X ⊔ T ⊔ D := le_of_mem_cComp hK
  refine le_antisymm ?_ (le_inf (solvRad_le K) ?_)
  · refine le_solvRad_of_subnormal_lt hK (A3.subnormal_of_normal inf_le_left ?_)
      (lt_of_le_of_ne inf_le_left fun h => hKB₀ (h ▸ inf_le_right))
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => ?_
    exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hk) (hB.nor (hKB hk))
  · exact H.le_B₀_of_isSolvable hB hY ((solvRad_le K).trans hKB)
      (hBK.trans (normalizer_le_normalizer_solvRad K)) (solvRad_isSolvable K)

theorem star_eq_star_Y (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) :
    star (X ⊔ T ⊔ D) B₀ K = star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
  have hKB : K ≤ X ⊔ T ⊔ D := le_of_mem_cComp hK
  refine le_antisymm (H.star_le_star_Y hKB (perfect_of_mem_cComp hK)) ?_
  have hlt : B₀ < K ⊔ B₀ :=
    lt_of_le_of_ne le_sup_right fun h => hKB₀ (le_sup_left.trans h.symm.le)
  have hNn : X ⊔ T ⊔ D ≤ Subgroup.normalizer ((K ⊔ B₀ : Subgroup G) : Set G) := fun g hg =>
    ChiefCount.mem_normalizer_sup (hBK hg) (hB.nor hg)
  have hYK := (H.X_le_of_normal hNn (hB.max _ hlt (sup_le hKB hB.le) hNn)).2
  rw [← star_sup_eq hKB hB.le]
  exact star_mono hYK

theorem isSimpleGroup_star (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) :
    IsSimpleGroup ↥(star (X ⊔ T ⊔ D) B₀ K) ∧
      ∃ a b : ↥(star (X ⊔ T ⊔ D) B₀ K), a * b ≠ b * a := by
  have hKB : K ≤ X ⊔ T ⊔ D := le_of_mem_cComp hK
  obtain ⟨-, ⟨hsimp, hnab⟩, -⟩ := cComp_structure hK
  let φ : ↥K →* ↥(star (X ⊔ T ⊔ D) B₀ K) :=
    { toFun := fun k => ⟨QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨k, hKB k.2⟩,
        mk_mem_star (hKB k.2) k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul (QuotientGroup.mk' _)
        (⟨a, hKB a.2⟩ : ↥(X ⊔ T ⊔ D)) ⟨b, hKB b.2⟩) }
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨k, hkB, hk, rfl⟩ := mem_star_iff.mp hq
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker : φ.ker = (solvRad K).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← H.inf_B₀_eq_solvRad hB hY hK hBK hKB₀]
    constructor
    · intro h1
      exact ⟨k.2, (mk_eq_one_iff (hKB k.2)).mp (congrArg Subtype.val h1)⟩
    · intro h1
      exact Subtype.ext ((mk_eq_one_iff (hKB k.2)).mpr h1.2)
  let e : (↥K ⧸ (solvRad K).subgroupOf K) ≃* ↥(star (X ⊔ T ⊔ D) B₀ K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have := hsimp
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

end Hyp3320

end S3320

end CFSG.Quasithin.H13
