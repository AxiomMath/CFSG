module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLabel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoOrder3
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSTheta
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Cent
import CFSG.Adapters.StatedSLTwoField
import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.StandardType.FF81

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.StandardType.GGSixE6Two
open CFSG.SeitzReduction (highRoot)

section Position

private lemma e6Pos_map_conj_eq_lE {u : EC} (hu : ∀ y ∈ lE, u * y * u⁻¹ = y) :
    Subgroup.map (MulAut.conj u).toMonoidHom lE = lE := by
  have hu' : ∀ y ∈ lE, u⁻¹ * y * u = y := by
    intro y hy
    calc u⁻¹ * y * u = u⁻¹ * (u * y * u⁻¹) * u := by rw [hu y hy]
      _ = y := by group
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu z hz]
    exact hz
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨u⁻¹ * y * u, ?_, ?_⟩
    · rw [hu' y hy]
      exact hy
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private lemma e6Pos_map_conj_eq_lE_of_mem_centralizer {u : EC}
    (hu : u ∈ Subgroup.centralizer (lE : Set EC)) :
    Subgroup.map (MulAut.conj u).toMonoidHom lE = lE := by
  apply e6Pos_map_conj_eq_lE
  intro y hy
  have h := Subgroup.mem_centralizer_iff.mp hu y hy
  rw [← h]
  group

private lemma e6Pos_zpow_conj_zE (k : ℤ) :
    zE ^ k * zE * (zE ^ k)⁻¹ = zE ∧ zE ^ k * zE⁻¹ * (zE ^ k)⁻¹ = zE⁻¹ := by
  have h : Commute (zE ^ k) zE := (Commute.refl zE).zpow_left k
  have h' : Commute (zE ^ k) zE⁻¹ := Commute.inv_right_iff.mpr h
  exact ⟨by rw [h.eq]; group, by rw [h'.eq]; group⟩

private lemma e6Pos_finish {G : Type} [Group G] {Y L : Subgroup G} {b t : G}
    (hLY : L ≤ Y) (hbY : b ∈ Y) (htY : t ∈ Y) (χ : ↥Y ≃* EC)
    (hbχ : χ ⟨b, hbY⟩ = zE) (htχ : χ ⟨t, htY⟩ = xr (highRoot .E6))
    (hLχ : (L.subgroupOf Y).map χ.toMonoidHom = lE) :
    ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = Y ∧
      φ (xr (highRoot .E6)) = t ∧ φ zE = b ∧ lE.map φ = L := by
  refine ⟨Y.subtype.comp χ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [MonoidHom.coe_comp, Function.comp_def] using
      (Subgroup.subtype_injective Y).comp χ.symm.injective
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr χ.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  · show Y.subtype (χ.symm (xr (highRoot .E6))) = t
    rw [← htχ, MulEquiv.symm_apply_apply]
    rfl
  · show Y.subtype (χ.symm zE) = b
    rw [← hbχ, MulEquiv.symm_apply_apply]
    rfl
  · show Subgroup.map (Y.subtype.comp χ.symm.toMonoidHom) lE = L
    have hsymm : Subgroup.map χ.symm.toMonoidHom lE = L.subgroupOf Y := by
      rw [← hLχ, Subgroup.map_map]
      rw [show χ.symm.toMonoidHom.comp χ.toMonoidHom = MonoidHom.id ↥Y from
        MonoidHom.ext fun x => χ.symm_apply_apply x]
      rw [Subgroup.map_id]
    rw [← Subgroup.map_map, hsymm, Subgroup.map_subgroupOf_eq_of_le hLY]

private lemma e6Pos_card_of_psl {L : Type} [Group L]
    (hL : StatedClassicalModel L .PSL 6 2 1) : Nat.card L = ordA 5 2 := by
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hL
  rw [Nat.card_congr e.toEquiv]
  calc Nat.card (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) = Nat.card ↥lE := by
        rw [← card_lE_eq_card_specialLinearGroup]
    _ = ordA 5 2 := card_lE

private lemma e6Pos_conj_xr_zE_inv :
    xr (highRoot .E6) * zE⁻¹ * (xr (highRoot .E6))⁻¹ = zE := by
  have h : xr (highRoot .E6) * zE * (xr (highRoot .E6))⁻¹ = zE⁻¹ :=
    xr_highRoot_mul_zE_mul_inv
  calc xr (highRoot .E6) * zE⁻¹ * (xr (highRoot .E6))⁻¹
      = (xr (highRoot .E6) * zE * (xr (highRoot .E6))⁻¹)⁻¹ := by group
    _ = zE := by rw [h, inv_inv]

private lemma e6Pos_xr_mem_centralizer_lE :
    xr (highRoot .E6) ∈ Subgroup.centralizer (lE : Set EC) :=
  Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (commute_of_mem_sTheta_of_mem_lE xr_highRoot_mem_sTheta hy).symm

private lemma e6Pos_map_eq_lE {G : Type} [Group G] {Y L : Subgroup G} {b : G}
    (hLY : L ≤ Y) (hbY : b ∈ Y) (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hL : StatedClassicalModel ↥L .PSL 6 2 1) {χ : ↥Y ≃* EC}
    (hχb : χ ⟨b, hbY⟩ = zE ∨ χ ⟨b, hbY⟩ = zE⁻¹) :
    (L.subgroupOf Y).map χ.toMonoidHom = lE := by
  have hcommχ : ∀ l : ↥(L.subgroupOf Y),
      χ (l : ↥Y) * χ ⟨b, hbY⟩ = χ ⟨b, hbY⟩ * χ (l : ↥Y) := by
    intro l
    have hlb : (l : ↥Y) * ⟨b, hbY⟩ = ⟨b, hbY⟩ * (l : ↥Y) := by
      apply Subtype.ext
      have hcomm : ((l : ↥Y) : G) * b = b * ((l : ↥Y) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLC l.2)
      simpa using hcomm
    calc χ (l : ↥Y) * χ ⟨b, hbY⟩ = χ ((l : ↥Y) * ⟨b, hbY⟩) := by rw [map_mul]
      _ = χ (⟨b, hbY⟩ * (l : ↥Y)) := by rw [hlb]
      _ = χ ⟨b, hbY⟩ * χ (l : ↥Y) := by rw [map_mul]
  have hle : (L.subgroupOf Y).map χ.toMonoidHom ≤ Subgroup.zpowers zE ⊔ lE := by
    rintro y ⟨l, hl, rfl⟩
    have h1 := hcommχ ⟨l, hl⟩
    have hy : χ l ∈ Subgroup.centralizer ({χ ⟨b, hbY⟩} : Set EC) :=
      Subgroup.mem_centralizer_singleton_iff.mpr h1
    rcases hχb with hb | hb
    · rw [hb] at hy
      rw [← centralizer_zE.1]
      exact hy
    · rw [hb] at hy
      rw [← centralizer_zE.1, ← centralizer_zE_inv]
      exact hy
  have hcard : Nat.card ↥((L.subgroupOf Y).map χ.toMonoidHom) = Nat.card ↥lE := by
    rw [Subgroup.card_map_of_injective χ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv,
      e6Pos_card_of_psl hL, card_lE]
  have hperf : commutator ↥((L.subgroupOf Y).map χ.toMonoidHom) = ⊤ := by
    have hSL : commutator (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) = ⊤ :=
      CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (n := 6) (by norm_num)
    obtain ⟨eL⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hL
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) :=
      Group.IsPerfect.mk hSL
    have hL' : commutator ↥(L.subgroupOf Y) = ⊤ :=
      (Group.IsPerfect.ofSurjective
        (f := ((Subgroup.subgroupOfEquivOfLe hLY).trans eL).symm.toMonoidHom)
        ((Subgroup.subgroupOfEquivOfLe hLY).trans eL).symm.surjective).commutator_eq_top
    haveI : Group.IsPerfect ↥(L.subgroupOf Y) := Group.IsPerfect.mk hL'
    exact (Group.IsPerfect.ofSurjective
      (f := ((L.subgroupOf Y).equivMapOfInjective χ.toMonoidHom χ.injective).toMonoidHom)
      ((L.subgroupOf Y).equivMapOfInjective χ.toMonoidHom χ.injective).surjective).commutator_eq_top
  exact eq_lE_of_le_of_perfect hle hperf hcard

private lemma e6Pos_thirtyOne_dvd_centralizer {G : Type} [Group G] [Finite G]
    {Y L : Subgroup G} {b : G} (hbY : b ∈ Y) (hLY : L ≤ Y)
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hL : StatedClassicalModel ↥L .PSL 6 2 1) (ψ : ↥Y ≃* EC) :
    31 ∣ Nat.card (Subgroup.centralizer ({ψ ⟨b, hbY⟩} : Set EC)) := by
  have hmapC : (L.subgroupOf Y).map ψ.toMonoidHom ≤
      Subgroup.centralizer ({ψ ⟨b, hbY⟩} : Set EC) := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlb : (l : ↥Y) * ⟨b, hbY⟩ = ⟨b, hbY⟩ * (l : ↥Y) := by
      apply Subtype.ext
      have hcomm : ((l : ↥Y) : G) * b = b * ((l : ↥Y) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)
      simpa using hcomm
    calc ψ (l : ↥Y) * ψ ⟨b, hbY⟩ = ψ ((l : ↥Y) * ⟨b, hbY⟩) := by rw [map_mul]
      _ = ψ (⟨b, hbY⟩ * (l : ↥Y)) := by rw [hlb]
      _ = ψ ⟨b, hbY⟩ * ψ (l : ↥Y) := by rw [map_mul]
  have hdvd : Nat.card ↥((L.subgroupOf Y).map ψ.toMonoidHom) ∣
      Nat.card ↥(Subgroup.centralizer ({ψ ⟨b, hbY⟩} : Set EC)) := by
    have h := Subgroup.card_subgroup_dvd_card
      (((L.subgroupOf Y).map ψ.toMonoidHom).subgroupOf
        (Subgroup.centralizer ({ψ ⟨b, hbY⟩} : Set EC)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmapC).toEquiv] at h
  have hcardM : Nat.card ↥((L.subgroupOf Y).map ψ.toMonoidHom) = Nat.card ↥lE := by
    rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv, e6Pos_card_of_psl hL,
      card_lE]
  have h31lE : 31 ∣ Nat.card ↥lE := by
    rw [card_lE]
    exact thirtyOne_dvd_ordA
  rw [hcardM] at hdvd
  exact h31lE.trans hdvd

private lemma e6Pos_first_equiv {G : Type} [Group G] [Finite G] {Y L : Subgroup G} {b : G}
    (hbY : b ∈ Y) (hb : orderOf b = 3) (hLY : L ≤ Y)
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hL : StatedClassicalModel ↥L .PSL 6 2 1) (ψ : ↥Y ≃* EC) :
    ∃ χ : ↥Y ≃* EC, (χ ⟨b, hbY⟩ = zE ∨ χ ⟨b, hbY⟩ = zE⁻¹) ∧
      (L.subgroupOf Y).map χ.toMonoidHom = lE := by
  have hxord : orderOf (ψ ⟨b, hbY⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨b, hbY⟩ : ↥Y)]
    exact hb
  have h31 := e6Pos_thirtyOne_dvd_centralizer hbY hLY hLC hL ψ
  obtain ⟨g, hg⟩ := e6Two_order3Conj e6TwoCentT31_holds (ψ ⟨b, hbY⟩) hxord h31
  have hval : (ψ.trans (MulAut.conj g)) ⟨b, hbY⟩ = g * ψ ⟨b, hbY⟩ * g⁻¹ := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
  refine ⟨ψ.trans (MulAut.conj g), ?_, ?_⟩
  · rw [hval]
    exact hg
  · exact e6Pos_map_eq_lE hLY hbY hLC hL (by rw [hval]; exact hg)

private lemma e6Pos_adjust_involution {G : Type} [Group G] {Y L : Subgroup G} {b t : G}
    (hbY : b ∈ Y) (htY : t ∈ Y) (ht : orderOf t = 2)
    (htL : ∀ y ∈ L, t * y = y * t) {χ : ↥Y ≃* EC}
    (hχb : χ ⟨b, hbY⟩ = zE ∨ χ ⟨b, hbY⟩ = zE⁻¹)
    (hχL : (L.subgroupOf Y).map χ.toMonoidHom = lE) :
    ∃ χ₁ : ↥Y ≃* EC, (χ₁ ⟨b, hbY⟩ = zE ∨ χ₁ ⟨b, hbY⟩ = zE⁻¹) ∧
      χ₁ ⟨t, htY⟩ = xr (highRoot .E6) ∧ (L.subgroupOf Y).map χ₁.toMonoidHom = lE := by
  have ht' : orderOf (⟨t, htY⟩ : ↥Y) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨t, htY⟩ : ↥Y)]
    exact ht
  let s : EC := χ ⟨t, htY⟩
  have hsord : orderOf s = 2 := by
    rw [show s = χ ⟨t, htY⟩ from rfl, MulEquiv.orderOf_eq]
    exact ht'
  have hscomm : ∀ y ∈ lE, s * y = y * s := by
    intro y hy
    have hy' : y ∈ (L.subgroupOf Y).map χ.toMonoidHom := by rw [hχL]; exact hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy'
    have hlt : (l : ↥Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * (l : ↥Y) := by
      apply Subtype.ext
      have h := htL ((l : ↥Y) : G) hl
      simpa using h.symm
    calc s * χ (l : ↥Y) = χ ⟨t, htY⟩ * χ (l : ↥Y) := by
          rw [show s = χ ⟨t, htY⟩ from rfl]
      _ = χ (⟨t, htY⟩ * (l : ↥Y)) := by rw [map_mul]
      _ = χ ((l : ↥Y) * ⟨t, htY⟩) := by rw [hlt]
      _ = χ (l : ↥Y) * χ ⟨t, htY⟩ := by rw [map_mul]
      _ = χ (l : ↥Y) * s := by rw [show s = χ ⟨t, htY⟩ from rfl]
  have hsmem : s ∈ sTheta := mem_sTheta_of_commute_lE hscomm (by rw [hsord]; decide)
  obtain ⟨k, hk⟩ := exists_zpow_conj_eq_xr_highRoot hsmem hsord
  have hval : ∀ x : ↥Y, (χ.trans (MulAut.conj (zE ^ k))) x =
      zE ^ k * χ x * (zE ^ k)⁻¹ := by
    intro x
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
  refine ⟨χ.trans (MulAut.conj (zE ^ k)), ?_, ?_, ?_⟩
  · rw [hval]
    rcases hχb with hb | hb
    · left
      rw [hb]
      exact (e6Pos_zpow_conj_zE k).1
    · right
      rw [hb]
      exact (e6Pos_zpow_conj_zE k).2
  · rw [hval]
    exact hk
  · rw [show (χ.trans (MulAut.conj (zE ^ k))).toMonoidHom =
        (MulAut.conj (zE ^ k)).toMonoidHom.comp χ.toMonoidHom from rfl,
      ← Subgroup.map_map, hχL]
    exact e6Pos_map_conj_eq_lE_of_mem_centralizer
      (centralizer_zE.2.2 (Subgroup.zpow_mem (Subgroup.zpowers zE)
        (Subgroup.mem_zpowers zE) k))

theorem exists_e6Position_of_le {G : Type} [Group G] [Finite G] {Y L : Subgroup G} {b t : G}
    (hY : GGHasLabel ⟨.E6, 0, 1⟩ ↥Y) (hbY : b ∈ Y) (hb : orderOf b = 3) (hLY : L ≤ Y)
    (hLC : L ≤ Subgroup.centralizer ({b} : Set G))
    (hL : StatedClassicalModel ↥L .PSL 6 2 1) (htY : t ∈ Y) (ht : orderOf t = 2)
    (htL : ∀ y ∈ L, t * y = y * t) :
    ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = Y ∧
      φ (xr (highRoot .E6)) = t ∧ φ zE = b ∧ lE.map φ = L := by
  classical
  obtain ⟨ψ⟩ := nonempty_mulEquiv_EC_of_ggHasLabel hY
  obtain ⟨χ, hχb, hχL⟩ := e6Pos_first_equiv hbY hb hLY hLC hL ψ
  obtain ⟨χ₁, hχ₁b, hχ₁t, hχ₁L⟩ :=
    e6Pos_adjust_involution hbY htY ht htL hχb hχL
  rcases hχ₁b with hb | hb
  · exact e6Pos_finish hLY hbY htY χ₁ hb hχ₁t hχ₁L
  · have hχ₂b : (χ₁.trans (MulAut.conj (xr (highRoot .E6)))) ⟨b, hbY⟩ = zE := by
      rw [MulEquiv.trans_apply, MulAut.conj_apply, hb]
      exact e6Pos_conj_xr_zE_inv
    have hχ₂t : (χ₁.trans (MulAut.conj (xr (highRoot .E6)))) ⟨t, htY⟩ =
        xr (highRoot .E6) := by
      rw [MulEquiv.trans_apply, hχ₁t, MulAut.conj_apply]
      group
    have hχ₂L : (L.subgroupOf Y).map
        (χ₁.trans (MulAut.conj (xr (highRoot .E6)))).toMonoidHom = lE := by
      rw [show (χ₁.trans (MulAut.conj (xr (highRoot .E6)))).toMonoidHom =
          (MulAut.conj (xr (highRoot .E6))).toMonoidHom.comp χ₁.toMonoidHom from rfl,
        ← Subgroup.map_map, hχ₁L]
      exact e6Pos_map_conj_eq_lE_of_mem_centralizer e6Pos_xr_mem_centralizer_lE
    exact e6Pos_finish hLY hbY htY (χ₁.trans (MulAut.conj (xr (highRoot .E6))))
      hχ₂b hχ₂t hχ₂L

theorem exists_e6Position {G : Type} [Group G] [Finite G] {Y L : Subgroup G} {b t : G}
    (hY : GGHasLabel ⟨.E6, 0, 1⟩ ↥Y) (hbY : b ∈ Y) (hb : orderOf b = 3)
    (hcen : Subgroup.centralizer ({b} : Set G) ⊓ Y = Subgroup.zpowers b ⊔ L)
    (hL : StatedClassicalModel ↥L .PSL 6 2 1) (htY : t ∈ Y) (ht : orderOf t = 2)
    (htL : ∀ y ∈ L, t * y = y * t) :
    ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = Y ∧
      φ (xr (highRoot .E6)) = t ∧ φ zE = b ∧ lE.map φ = L := by
  have hLle : L ≤ Subgroup.centralizer ({b} : Set G) ⊓ Y := by
    rw [hcen]
    exact le_sup_right
  exact exists_e6Position_of_le hY hbY hb (hLle.trans inf_le_right) (hLle.trans inf_le_left) hL
    htY ht htL

theorem centralizer_inf_eq_of_e6Position {G : Type} [Group G] {Y L : Subgroup G} {b : G}
    {φ : EC →* G} (hinj : Function.Injective φ) (hrange : φ.range = Y) (hz : φ zE = b)
    (hL : lE.map φ = L) :
    Subgroup.centralizer ({b} : Set G) ⊓ Y = Subgroup.zpowers b ⊔ L := by
  apply le_antisymm
  · rintro x ⟨hxc, hxY⟩
    rw [← hrange] at hxY
    obtain ⟨y, rfl⟩ := hxY
    have hy : y ∈ Subgroup.centralizer ({zE} : Set EC) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul, hz]
      exact Subgroup.mem_centralizer_singleton_iff.1 hxc
    rw [centralizer_zE.1] at hy
    have h := Subgroup.mem_map_of_mem φ hy
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hz, hL] at h
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, ?_⟩
      rw [← hrange, ← hz]
      exact ⟨zE, rfl⟩
    · rw [← hL]
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hrange ▸ ⟨y, rfl⟩⟩
      rw [← hz, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 (lE_le_centralizer_zE hy)]

theorem exists_e6Position_of_yData {G : Type} [Group G] [Finite G] {n : ℕ} {b t : G}
    {L : Subgroup G} {K : ℕ → Subgroup G} (hA : HypA G n b L) (hU : Upstream n b L K t)
    (hYD : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t) (hn : n = 5)
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ))) :
    ∃ φ : EC →* G, Function.Injective φ ∧ φ.range = ⨆ i : Fin (n + 2), K (i : ℕ) ∧
      φ (xr (highRoot .E6)) = t ∧ φ zE = b ∧ lE.map φ = L ∧ sTheta.map φ = K 0 := by
  obtain ⟨z, -, hFS⟩ := hU
  subst hn
  have hbK0 : b ∈ K 0 := by
    rw [hFS.K0]
    exact (le_sup_left : Subgroup.zpowers b ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers t)
      (Subgroup.mem_zpowers b)
  have htK0 : t ∈ K 0 := by
    rw [hFS.K0]
    exact (le_sup_right : Subgroup.zpowers t ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers t)
      (Subgroup.mem_zpowers t)
  have hbY : b ∈ ⨆ i : Fin (5 + 2), K (i : ℕ) :=
    (le_iSup (fun i : Fin (5 + 2) => K (i : ℕ)) (0 : Fin (5 + 2))) hbK0
  have htY : t ∈ ⨆ i : Fin (5 + 2), K (i : ℕ) :=
    (le_iSup (fun i : Fin (5 + 2) => K (i : ℕ)) (0 : Fin (5 + 2))) htK0
  obtain ⟨φ, hφinj, hφrange, hφx, hφz, hφL⟩ :=
    exists_e6Position (Y := ⨆ i : Fin (5 + 2), K (i : ℕ)) (L := L) (b := b) (t := t)
      hlab hbY hA.ord hYD.cen_b hA.model htY hFS.ord_t (fun y hy => hFS.comm_L t htK0 y hy)
  refine ⟨φ, hφinj, hφrange, hφx, hφz, hφL, ?_⟩
  rw [sTheta_eq_zpowers_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, hφz, hφx, hFS.K0]

end Position

end CFSG.StandardType.FF81

end
