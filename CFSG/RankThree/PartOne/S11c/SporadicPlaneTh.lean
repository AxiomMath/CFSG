module

public import CFSG.RankThree.PartOne.KS.PlaneTh
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne.ThPlane

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates.ExtraspecialNF
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Sporadic.ThSchreier (ctuc_Th_full_automorphism_group)

section TwoGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_into_M_gen_two {M : Subgroup G} (h : InvCentConj M) {t : G} (V : Subgroup G)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hVt : ∀ x ∈ V, x * t = t * x) :
    ∃ g : G, g⁻¹ * t * g ∈ M ∧ ∀ x ∈ V, g⁻¹ * x * g ∈ M := by
  have hnt : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hV
  have hZnt : Nontrivial (Subgroup.center V) := hV2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center V) := hV2.to_subgroup _
  have hZcard : 2 ∣ Nat.card (Subgroup.center V) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : Nat.card (Subgroup.center V) = 1 := by simpa using hk
      exact absurd (Nat.card_eq_one_iff_unique.mp this).1 (not_subsingleton _)
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center V) 2 hZcard
  set v : G := (((x0 : Subgroup.center V) : V) : G) with hv
  have hvo : orderOf v = 2 := by
    have h1 : orderOf (((x0 : Subgroup.center V) : V)) = 2 := by
      rw [← hx0]
      exact Subgroup.orderOf_coe x0
    rw [hv, Subgroup.orderOf_coe, h1]
  have hvc : ∀ y ∈ V, y * v = v * y := fun y hy => by
    have := Subgroup.mem_center_iff.mp x0.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ := h v hvo
  have key : ∀ y : G, y ∈ Subgroup.centralizer ({v} : Set G) → g⁻¹ * y * g ∈ M := by
    intro y hy
    rw [hg] at hy
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    have : g⁻¹ * y * g = m := by
      rw [← hmy]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hm
  refine ⟨g, key t (Subgroup.mem_centralizer_singleton_iff.mpr ?_),
    fun x hx => key x (Subgroup.mem_centralizer_singleton_iff.mpr (hvc x hx))⟩
  exact (hVt _ ((x0 : Subgroup.center V) : V).2).symm

end TwoGroups

section Quotient

variable {G : Type} [Group G]

theorem ExtQuotData.card_le_eight_seven [Finite G]
    (D : ExtQuotData G (alternatingGroup (Fin 9))) {t w : G}
    (ht : t ∈ D.M) (hw : w ∈ D.M) (hπw : orderOf (D.π ⟨w, hw⟩) = 7) (hto : orderOf t = 7)
    (D0 : Finset (Fin 8 → ZMod 2)) (hD0 : ∀ v, D.act w v = v → v ∈ D0) (hD0card : D0.card ≤ 4)
    {V : Subgroup G} (hVM : V ≤ D.M) (hVc : ∀ x ∈ V, x * t = t * x) (hV2 : IsPGroup 2 V) :
    Nat.card V ≤ 8 := by
  have hπt := D.orderOf_proj ht (by decide) (by norm_num) hto
  have hconj : ∃ a : alternatingGroup (Fin 9), a * D.π ⟨t, ht⟩ * a⁻¹ = D.π ⟨w, hw⟩ :=
    exists_conj_alt (by decide) (by norm_num) le_rfl _ _ hπt hπw
  have hVQ : ∀ x ∈ V, x ∈ D.Q := by
    let ψ : V →* alternatingGroup (Fin 9) := D.π.comp (Subgroup.inclusion hVM)
    have hpg : IsPGroup 2 ψ.range := hV2.of_surjective ψ.rangeRestrict
      (by intro y; obtain ⟨x, hx⟩ := y.2; exact ⟨x, Subtype.ext hx⟩)
    have hbot : ψ.range = ⊥ := by
      refine eq_bot_of_commute_seven (D.π ⟨t, ht⟩) hπt ψ.range ?_ hpg
      rintro _ ⟨x, rfl⟩
      show D.π (Subgroup.inclusion hVM x) * D.π ⟨t, ht⟩ =
        D.π ⟨t, ht⟩ * D.π (Subgroup.inclusion hVM x)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVc _ x.2)
    intro x hx
    have h1 : ψ ⟨x, hx⟩ = 1 := by
      have : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hbot] at this
      exact this
    exact (D.ker (Subgroup.inclusion hVM ⟨x, hx⟩)).1 h1
  obtain ⟨g, hg, hk1, -⟩ := D.fix_conj ht hw hconj
  have hginj : ∀ u u' : Fin 8 → ZMod 2, D.act g u = D.act g u' → u = u' := by
    intro u u' h
    have := congrArg (D.act g⁻¹) h
    rwa [D.act_inv_act hg, D.act_inv_act hg] at this
  let a : V → (Fin 8 → ZMod 2) := fun x => D.act g (coord D.z D.q (x : G))
  have ha_mem : ∀ x : V, a x ∈ D0 := fun x =>
    hD0 _ (hk1 _ (D.act_coord_of_commute ht (hVQ _ x.2) (hVc _ x.2).symm))
  have ha_add : ∀ x y : V, a (x * y) = a x + a y := by
    intro x y
    show D.act g (coord D.z D.q ((x : G) * (y : G))) = _
    rw [coord_mul D.rel D.inj (hVQ _ x.2) (hVQ _ y.2), D.act_add hg]
  let ψ' : V →* Multiplicative (Fin 8 → ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (a x)
      map_one' := by
        show Multiplicative.ofAdd (D.act g (coord D.z D.q ((1 : V) : G))) = 1
        rw [Subgroup.coe_one, D.coord_one, D.act_zero hg]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (a (x * y)) =
          Multiplicative.ofAdd (a x) * Multiplicative.ofAdd (a y)
        rw [ha_add]
        rfl }
  have hcard := Subgroup.card_ker_mul_card_range ψ'
  have hz2 : Nat.card (Subgroup.zpowers D.z) = 2 := by
    rw [Nat.card_zpowers, D.orderOf_z]
  have hker : Nat.card ψ'.ker ≤ 2 := by
    refine le_trans ?_ hz2.le
    have hmem : ∀ x : ψ'.ker, ((x : V) : G) ∈ Subgroup.zpowers D.z := by
      intro x
      have hx0 : a (x : V) = 0 := by
        have h1 : ψ' (x : V) = 1 := x.2
        exact h1
      have : coord D.z D.q ((x : V) : G) = 0 := by
        apply hginj
        rw [D.act_zero hg]
        exact hx0
      exact (coord_eq_zero_iff D.rel D.inj (hVQ _ (x : V).2)).1 this
    refine Nat.card_le_card_of_injective (fun x : ψ'.ker => (⟨((x : V) : G), hmem x⟩ :
      Subgroup.zpowers D.z)) ?_
    intro x y hxy
    have h1 : ((x : V) : G) = ((y : V) : G) :=
      congrArg (fun u : Subgroup.zpowers D.z => (u : G)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card ψ'.range ≤ 4 := by
    have hsub : ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2))) ⊆
        ((D0.image Multiplicative.ofAdd : Finset (Multiplicative (Fin 8 → ZMod 2))) :
          Set (Multiplicative (Fin 8 → ZMod 2))) := by
      rintro _ ⟨x, rfl⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨a x, ha_mem x, rfl⟩
    calc Nat.card ψ'.range
        = Set.ncard ((ψ'.range : Subgroup _) : Set (Multiplicative (Fin 8 → ZMod 2))) :=
          Nat.card_coe_set_eq _
      _ ≤ Set.ncard ((D0.image Multiplicative.ofAdd : Finset (Multiplicative (Fin 8 → ZMod 2))) :
          Set (Multiplicative (Fin 8 → ZMod 2))) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (D0.image Multiplicative.ofAdd).card := Set.ncard_coe_finset _
      _ ≤ D0.card := Finset.card_image_le
      _ ≤ 4 := hD0card
  calc Nat.card V = Nat.card ψ'.ker * Nat.card ψ'.range := hcard.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num

end Quotient

section Generic

variable {G : Type} [Group G] [Finite G] (D : ExtQuotData G (alternatingGroup (Fin 9)))

theorem card_le_eight_five_gen (h : InvCentConj D.M) {w : G} (hw : w ∈ D.M)
    (hπw : orderOf (D.π ⟨w, hw⟩) = 5) (hfix : ∀ v, D.act w v = v → v = 0) (t : G)
    (ht : orderOf t = 5) (R2 : Subgroup G) (hR2 : IsPGroup 2 R2)
    (hle : R2 ≤ Subgroup.centralizer ({t} : Set G)) : Nat.card R2 ≤ 8 := by
  by_cases hbot : R2 = ⊥
  · rw [hbot, Subgroup.card_bot]
    norm_num
  have hVt : ∀ x ∈ R2, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  obtain ⟨g, hgt, hgV⟩ := exists_conj_into_M_gen_two h R2 hbot hR2 hVt
  have hle8 : Nat.card (R2.map (MulAut.conj g⁻¹).toMonoidHom) ≤ 8 := by
    refine D.card_le_eight (t := g⁻¹ * t * g) (w := w) hgt hw hπw (orderOf_conj_gen g t ht) hfix
      (conj_subgroup_le_M_gen hgV) ?_ (hR2.map _)
    rintro _ ⟨x, hx, rfl⟩
    exact conj_commute_gen (hVt x hx)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hle8

theorem card_le_eight_seven_gen (h : InvCentConj D.M) {w : G} (hw : w ∈ D.M)
    (hπw : orderOf (D.π ⟨w, hw⟩) = 7) (D0 : Finset (Fin 8 → ZMod 2))
    (hD0 : ∀ v, D.act w v = v → v ∈ D0) (hD0card : D0.card ≤ 4) (t : G) (ht : orderOf t = 7)
    (R2 : Subgroup G) (hR2 : IsPGroup 2 R2) (hle : R2 ≤ Subgroup.centralizer ({t} : Set G)) :
    Nat.card R2 ≤ 8 := by
  by_cases hbot : R2 = ⊥
  · rw [hbot, Subgroup.card_bot]
    norm_num
  have hVt : ∀ x ∈ R2, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  obtain ⟨g, hgt, hgV⟩ := exists_conj_into_M_gen_two h R2 hbot hR2 hVt
  have hle8 : Nat.card (R2.map (MulAut.conj g⁻¹).toMonoidHom) ≤ 8 := by
    refine D.card_le_eight_seven (t := g⁻¹ * t * g) (w := w) hgt hw hπw (orderOf_conj_gen g t ht)
      D0 hD0 hD0card (conj_subgroup_le_M_gen hgV) ?_ (hR2.map _)
    rintro _ ⟨x, hx, rfl⟩
    exact conj_commute_gen (hVt x hx)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hle8

theorem le_seven_gen (h : InvCentConj D.M) {w : G} (hw : w ∈ D.M)
    (hπw : orderOf (D.π ⟨w, hw⟩) = 7) (D0 : Finset (Fin 8 → ZMod 2))
    (hD0 : ∀ v, D.act w v = v → v ∈ D0) (hD0card : D0.card ≤ 4)
    (hpair : ∀ e ∈ (↑D0 : Set (Fin 8 → ZMod 2)), ∀ e' ∈ (↑D0 : Set (Fin 8 → ZMod 2)), e ≠ 0 →
      e' ≠ 0 → e ≠ e' → bil D.c e e' = 1) (t : G) (ht : orderOf t = 7)
    (R2 : Subgroup G) (hR2 : IsPGroup 2 R2) (hle : R2 ≤ Subgroup.centralizer ({t} : Set G))
    (hel : Nat.card R2 = 8 → IsElementaryAbelian 2 R2) : Nat.card R2 ≤ 7 := by
  by_contra hbig
  have h8 := card_le_eight_seven_gen D h hw hπw D0 hD0 hD0card t ht R2 hR2 hle
  have heq : Nat.card R2 = 8 := by omega
  have hbot : R2 = ⊥ := q2_seven D h hw hπw (↑D0) (fun v hv => Finset.mem_coe.mpr (hD0 v hv))
    hpair t ht R2 hle (hel heq) (by rw [heq]; decide)
  rw [hbot, Subgroup.card_bot] at heq
  omega

end Generic

end CFSG.RankThree.PartOne.ThPlane

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Sporadic.ThSchreier (ctuc_Th_full_automorphism_group)
open CFSG.Sporadic.Th.Max3 (natCard_J)

theorem sporadicPlanesCentralize_Th :
    SporadicPlanesCentralize (Carrier .Th) := by
  have hinv : ThPlane.InvCentConj ThPlane.thData.M := ThPlane.invCentConj_J
  have hfix5 : ∀ v, ThPlane.thData.act ThPlane.w5 v = v → v = 0 := fun v hv =>
    ThPlane.fix5 v (by rw [← ThPlane.act_w5]; exact hv)
  have hfix7 : ∀ v, ThPlane.thData.act ThPlane.w7 v = v → v ∈ ThPlane.D7 := fun v hv =>
    ThPlane.fix7 v (by rw [← ThPlane.act_w7]; exact hv)
  have hpair : ∀ e ∈ (↑ThPlane.D7 : Set (Fin 8 → ZMod 2)), ∀ e' ∈ (↑ThPlane.D7 : Set (Fin 8 → ZMod
  2)),
      e ≠ 0 → e' ≠ 0 → e ≠ e' → CFSG.Certificates.ExtraspecialNF.bil ThPlane.thData.c e e' = 1 :=
    fun e he e' he' h0 h0' hne =>
      ThPlane.pair7 e (Finset.mem_coe.mp he) e' (Finset.mem_coe.mp he') h0 h0' hne
  refine sporadicPlanesCentralize_of_data_abel (P := (⊤ : Subgroup J)) (R := (⊤ : Subgroup J))
    le_rfl (thEquivJ.trans Subgroup.topEquiv.symm) (S := {5, 7}) ?_ ?_ ?_
  · intro T _ _ hs hnab ⟨eT⟩ p hp hp3
    by_cases h57 : p = 5 ∨ p = 7
    · refine Or.inl ?_
      rcases h57 with rfl | rfl <;> simp
    · refine Or.inr ?_
      have := hs
      let e0 : T ≃* CFSG.Blueprint.NativeSporadic.Th := eT
      obtain ⟨-, hsub⟩ := ctuc_Th_full_automorphism_group.2 T ⟨e0⟩
      have hc : Subgroup.center T = ⊥ := center_eq_bot_of_simple hnab
      rw [card_mulAut_eq_mul_card_outer hc]
      have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) = 1 :=
        Nat.card_of_subsingleton 1
      have hT : Nat.card T = 90745943887872000 :=
        (Nat.card_congr (e0.toEquiv.trans thEquivJ.toEquiv)).trans natCard_J
      rw [hout, hT, mul_one]
      exact ThPlane.not_sq_dvd_card_J hp hp3 h57
  · intro p hp T _ _ eT α hα
    let e0 : T ≃* CFSG.Blueprint.NativeSporadic.Th := eT
    obtain ⟨hinn, -⟩ := ctuc_Th_full_automorphism_group.2 T ⟨e0⟩
    have hmem : α ∈ inner T := hinn ▸ Subgroup.mem_top α
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, hb⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp7
    · refine ⟨8, Or.inl ⟨rfl, by norm_num⟩, ?_⟩
      intro y _ hord f _ _ _ R2 h2 hle _ _ _
      exact ThPlane.card_le_eight_five_gen ThPlane.thData hinv ThPlane.w5_mem
        ThPlane.orderOf_π_w5 hfix5 y hord R2 h2 (hle.trans inf_le_right)
    · rw [Finset.mem_singleton] at hp7
      subst hp7
      refine ⟨7, Or.inr ⟨rfl, by norm_num⟩, ?_⟩
      intro y _ hord f _ _ _ R2 h2 hle _ _ hel
      exact ThPlane.le_seven_gen ThPlane.thData hinv ThPlane.w7_mem ThPlane.orderOf_π_w7
        ThPlane.D7 hfix7 (by unfold ThPlane.D7; exact Finset.card_le_four) hpair y hord R2 h2
        (hle.trans inf_le_right) (hel rfl)

end CFSG.RankThree.PartOne
