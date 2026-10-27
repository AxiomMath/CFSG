module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Quasithin.SteinbergCF

open CFSG Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {H : Type*} [Group H]

@[expose] noncomputable def conjCenterQuotientHom (L : Subgroup H) [L.Normal] :
    H →* MulAut (L ⧸ center L) :=
  (centerQuotientHom L).comp MulAut.conjNormal

theorem conjCenterQuotientHom_apply_mk (L : Subgroup H) [L.Normal] (g : H) (x : L) :
    conjCenterQuotientHom L g (QuotientGroup.mk' (center L) x) =
      QuotientGroup.mk' (center L) (MulAut.conjNormal g x) :=
  onCenterQuotient_apply_mk _ x

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hQ
    have ha : a ∈ center Q := h ▸ mem_top a
    exact absurd (mem_center_iff.mp ha b).symm hab

theorem conj_injective_of_center_eq_bot {Q : Type*} [Group Q] (hQ : center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ center Q := mem_center_iff.mpr fun g => by
    have h := DFunLike.congr_fun ha g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * a = a * g * a⁻¹ * a := by rw [h]
      _ = a * g := by group
  rw [hQ, mem_bot] at hmem
  exact hmem

theorem central_Sylow_elementary_actions_inner_outer_order_bound [Finite H] {p : ℕ}
    [Fact p.Prime] (P : Sylow p H) {Z : Subgroup H}
    (hZP : Z ≤ (center (P : Subgroup H)).map (P : Subgroup H).subtype)
    (hZ : IsElementaryAbelian p Z)
    (hchar : ∀ z ∈ Z, z ≠ 1 → IsCharacteristicP p (centralizer ({z} : Set H)))
    (L : Subgroup H) [L.Normal] (hL : IsQuasisimple L) :
    let ρ : Z →* MulAut (L ⧸ center L) := (conjCenterQuotientHom L).comp Z.subtype
    let Rbar : Subgroup (L ⧸ center L) :=
      ((P : Subgroup H).subgroupOf L).map (QuotientGroup.mk' (center L))
    let D : Subgroup (L ⧸ center L) := (ρ.range ⊓ inner (L ⧸ center L)).comap MulAut.conj
    let ρout : Z →* Outer (L ⧸ center L) := (QuotientGroup.mk' (inner (L ⧸ center L))).comp ρ
    Function.Injective ρ ∧ (∃ T : Sylow p (L ⧸ center L), (T : Subgroup (L ⧸ center L)) = Rbar) ∧
      IsElementaryAbelian p D ∧ D ≤ (center Rbar).map Rbar.subtype ∧
      Nat.card Z = Nat.card D * Nat.card ρout.range ∧
      (¬ p ∣ Nat.card (Outer (L ⧸ center L)) → Nat.card Z ≤ Nat.card (center Rbar)) := by
  intro ρ Rbar D ρout
  obtain ⟨hLp, hsimple, hnonab⟩ := hL
  have hS : center (L ⧸ center L) = ⊥ := center_eq_bot_of_simple hnonab
  have hc := conj_injective_of_center_eq_bot hS
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : MulAut.conjNormal (z : H) = (1 : MulAut L) :=
      CFSG.ComponentClassification.CentralCover.perfect_central_quotient_automorphism_faithful L
        (hz.trans (map_one _).symm)
    by_contra hz1
    have hz1' : (z : H) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hLC : L ≤ centralizer ({(z : H)} : Set H) := by
      intro l hl
      rw [mem_centralizer_iff]
      rintro _ rfl
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨l, hl⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc (z : H) * l = (z : H) * l * (z : H)⁻¹ * z := by group
        _ = l * z := by rw [h2]
    have hcomp : IsComponent (L.subgroupOf (centralizer ({(z : H)} : Set H))) :=
      LocalCores.component_overgroup ⟨⟨hLp, hsimple, hnonab⟩,
        (inferInstance : L.Normal).isSubnormal⟩ hLC
    have hlayer := layer_eq_bot_of_isCharacteristicP _ p (hchar z z.2 hz1')
    have hbot : L.subgroupOf (centralizer ({(z : H)} : Set H)) = ⊥ :=
      le_bot_iff.mp (hlayer ▸ le_sSup hcomp)
    have hL1 : L = ⊥ := by
      rw [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hLC] at hbot
      exact hbot
    have : Nontrivial L := LocalCores.isQuasisimple_nontrivial ⟨hLp, hsimple, hnonab⟩
    exact (nontrivial_iff_ne_bot L).mp this hL1
  obtain ⟨RL, hRL⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P
    (inferInstance : L.Normal).isSubnormal
  have hRLeq : (RL : Subgroup L) = (P : Subgroup H).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hRL, subgroupOf_map_subtype]
  set T : Sylow p (L ⧸ center L) := RL.mapSurjective (QuotientGroup.mk'_surjective (center L))
  have hT : (T : Subgroup (L ⧸ center L)) = Rbar := by
    simp only [T, Sylow.coe_mapSurjective, hRLeq, Rbar]
  have hDmap : D.map MulAut.conj = ρ.range ⊓ inner (L ⧸ center L) := by
    simp only [D]
    rw [map_comap_eq]
    exact inf_eq_right.mpr inf_le_right
  have hcardD : Nat.card D = Nat.card (ρ.range ⊓ inner (L ⧸ center L) : Subgroup _) := by
    rw [← hDmap, card_map_of_injective hc]
  have hZc : ∀ a b : Z, a * b = b * a := fun a b => hZ.toIsMulCommutative.is_comm.comm a b
  have hZp : ∀ a : Z, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p Z) a
  have hDρ : ∀ d ∈ D, ∃ z : Z, ρ z = MulAut.conj d := fun d hd => hd.1
  have hDcomm : ∀ a b : D, a * b = b * a := fun a b => Subtype.ext (hc (by
    obtain ⟨za, hza⟩ := hDρ a a.2
    obtain ⟨zb, hzb⟩ := hDρ b b.2
    rw [coe_mul, coe_mul, map_mul, map_mul, ← hza, ← hzb, ← map_mul, ← map_mul, hZc]))
  have hDexp : ∀ a : D, a ^ p = 1 := fun a => Subtype.ext (hc (by
    obtain ⟨za, hza⟩ := hDρ a a.2
    rw [coe_pow, coe_one, map_pow, map_one, ← hza, ← map_pow, hZp, map_one]))
  have hDE : IsElementaryAbelian p D :=
    { toIsMulCommutative := ⟨⟨hDcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hDexp }
  have hfix : ∀ z : Z, ∀ r ∈ Rbar, ρ z r = r := by
    rintro z _ ⟨x, hx, rfl⟩
    have hzP := hZP z.2
    obtain ⟨⟨w, hwP⟩, hw, hwz⟩ := hzP
    have hcomm : (z : H) * x * (z : H)⁻¹ = x := by
      have hxw := mem_center_iff.mp hw ⟨x, hx⟩
      have h2 : (x : H) * w = w * x := congrArg Subtype.val hxw
      rw [← hwz]
      change w * x * w⁻¹ = x
      rw [← h2]
      group
    change conjCenterQuotientHom L z (QuotientGroup.mk' (center L) x) =
      QuotientGroup.mk' (center L) x
    rw [conjCenterQuotientHom_apply_mk]
    congr 1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hcomm)
  have hDC : D ≤ centralizer (Rbar : Set (L ⧸ center L)) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨z, hz⟩ := hDρ d hd
    have h := hfix z r hr
    rw [hz, MulAut.conj_apply] at h
    calc r * d = d * r * d⁻¹ * d := by rw [h]
      _ = d * r := by group
  have hD2 : IsPGroup p D := IsElementaryAbelian.isPGroup p D
  have hDR : D ≤ Rbar := by
    have hsup : IsPGroup p (D ⊔ Rbar : Subgroup (L ⧸ center L)) :=
      hD2.to_sup_of_normal_right' (hT ▸ T.isPGroup') (hDC.trans (centralizer_le_normalizer _))
    have h := T.is_maximal' (hT ▸ hsup) (hT ▸ le_sup_right)
    rw [hT] at h
    exact le_sup_left.trans h.le
  have hDZ : D ≤ (center Rbar).map Rbar.subtype := fun d hd =>
    ⟨⟨d, hDR hd⟩, mem_center_iff.mpr fun r => Subtype.ext
      (mem_centralizer_iff.mp (hDC hd) r r.2), rfl⟩
  have hker : ρout.ker.map ρ = ρ.range ⊓ inner (L ⧸ center L) := by
    ext a
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, rfl⟩, (QuotientGroup.eq_one_iff _).mp hz⟩
    · rintro ⟨⟨z, rfl⟩, ha⟩
      exact ⟨z, (QuotientGroup.eq_one_iff _).mpr ha, rfl⟩
  have hcardker : Nat.card ρout.ker = Nat.card D := by
    rw [hcardD, ← hker, card_map_of_injective hρ]
  have hformula : Nat.card Z = Nat.card D * Nat.card ρout.range := by
    rw [← card_mul_index ρout.ker, index_ker, hcardker]
  refine ⟨hρ, ⟨T, hT⟩, hDE, hDZ, hformula, fun hpOut => ?_⟩
  have hZ2 : IsPGroup p Z := IsElementaryAbelian.isPGroup p Z
  have hrange : Nat.card ρout.range = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (hZ2.of_surjective ρout.rangeRestrict ρout.rangeRestrict_surjective)
    have hdvd : Nat.card ρout.range ∣ Nat.card (Outer (L ⧸ center L)) :=
      card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd) hpOut
  rw [hformula, hrange, mul_one]
  calc Nat.card D ≤ Nat.card ((center Rbar).map Rbar.subtype) := card_le_of_le hDZ
    _ = Nat.card (center Rbar) := card_map_of_injective Rbar.subtype_injective

end CFSG.Quasithin.SteinbergCF
