module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAuxSet

public section

open CFSG.SignalizerFunctorTheorem Nonsolvable CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

theorem surjective_perfectResidual_quotient {Y : Type*} [Group Y] [Finite Y]
    (hY : oStar Y = ⊤) : Function.Surjective ((QuotientGroup.mk' (CFSG.solvableRadical Y)).comp
      (CFSG.perfectResidual Y).subtype) := by
  set T := CFSG.solvableRadical Y with hT
  set P := CFSG.perfectResidual Y with hP
  set ι := (QuotientGroup.mk' T).comp P.subtype with hι
  set W : Subgroup (Y ⧸ T) := ι.range with hW
  have hWn : W.Normal := by
    have : W = P.map (QuotientGroup.mk' T) := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p, p.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp⟩, rfl⟩
    rw [this]
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hperf : Group.IsPerfect (Y ⧸ T) := by
    have hl : CFSG.layer (Y ⧸ T) = ⊤ := KAPI.oStar_eq_top_iff.mp hY
    have := CFSG.LocalCores.layer_isPerfect (G := Y ⧸ T)
    rw [hl] at this
    exact Group.IsPerfect.top_iff.mp this
  have hPW : P ≤ ((QuotientGroup.mk' W).comp (QuotientGroup.mk' T)).ker := by
    intro p hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨p, hp⟩, rfl⟩
  let ν : Y ⧸ P →* (Y ⧸ T) ⧸ W := QuotientGroup.lift P _ hPW
  have hν : Function.Surjective ν := by
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk'_surjective W z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T z'
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hsolv : Group.IsSolvable ((Y ⧸ T) ⧸ W) := by
    have hs : Group.IsSolvable (Y ⧸ P) :=
      (CFSG.perfect_residual_characterization (G := Y)).2.2.2.1
    exact Group.isSolvable_of_surjective hν
  have hsub : Subsingleton ((Y ⧸ T) ⧸ W) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ((Y ⧸ T) ⧸ W) hsolv
  intro z
  have : (QuotientGroup.mk z : (Y ⧸ T) ⧸ W) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff z).mp this

theorem card_quot_le_layer {Q : Type*} [Group Q] [Finite Q]
    (hsol : CFSG.solvableRadical Q = ⊥) (hB : ∀ J ∈ lcal (⊤ : Subgroup Q), HypB ↥J)
    {Y : Subgroup Q} (hY : oStar ↥Y = ⊤) (hdeg : deg ↥(CFSG.layer Q) ≤ deg ↥Y) :
    Nat.card (↥Y ⧸ CFSG.solvableRadical ↥Y) ≤ Nat.card ↥(CFSG.layer Q) ∧
      (Nat.card (↥Y ⧸ CFSG.solvableRadical ↥Y) = Nat.card ↥(CFSG.layer Q) →
        Y = CFSG.layer Q) := by
  set T : Subgroup ↥Y := CFSG.solvableRadical ↥Y with hT
  set P : Subgroup ↥Y := CFSG.perfectResidual ↥Y with hP
  obtain ⟨hP'o, hP'p, hP'd⟩ := perfectResidual_map_props hY
  set P' : Subgroup Q := P.map Y.subtype with hP'
  have hP'le : P' ≤ CFSG.layer Q :=
    le_layer_of_deg_le hsol hB hP'o hP'p (by rw [hP'd]; exact hdeg)
  have hP'Y : P' ≤ Y := Subgroup.map_subtype_le _
  let ι : P →* ↥Y ⧸ T := (QuotientGroup.mk' T).comp P.subtype
  have hι : Function.Surjective ι := surjective_perfectResidual_quotient hY
  have hcard1 : Nat.card (↥Y ⧸ T) ≤ Nat.card ↥P := Nat.card_le_card_of_surjective ι hι
  have hcard2 : Nat.card ↥P = Nat.card ↥P' :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ Y.subtype_injective).toEquiv
  have hcard3 : Nat.card ↥P' ≤ Nat.card ↥(CFSG.layer Q) := Subgroup.card_le_of_le hP'le
  refine ⟨by omega, fun heq => ?_⟩
  have hP'eq : P' = CFSG.layer Q := Subgroup.eq_of_le_of_card_ge hP'le (by omega)
  have hιbij : Function.Bijective ι := hι.bijective_of_nat_card_le (by omega)
  have hTP : ∀ t ∈ T, ∀ p ∈ P, p * t = t * p := by
    intro t ht p hp
    have hc1 : p * t * p⁻¹ * t⁻¹ ∈ P := by
      have : p * t * p⁻¹ * t⁻¹ = p * (t * p⁻¹ * t⁻¹) := by group
      rw [this]
      exact mul_mem hp ((inferInstance : P.Normal).conj_mem _ (inv_mem hp) t)
    have hc2 : p * t * p⁻¹ * t⁻¹ ∈ T := by
      exact mul_mem ((inferInstance : T.Normal).conj_mem t ht p) (inv_mem ht)
    have h1 : ι ⟨_, hc1⟩ = 1 := by
      show QuotientGroup.mk' T (p * t * p⁻¹ * t⁻¹) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc2
    have h2 : (⟨_, hc1⟩ : P) = 1 := hιbij.1 (by rw [h1, map_one])
    have h3 : p * t * p⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h2
    calc p * t = p * t * p⁻¹ * t⁻¹ * t * p := by group
      _ = t * p := by rw [h3]; group
  have hT1 : T = ⊥ := by
    refine eq_bot_iff.mpr fun t ht => ?_
    have hmem : (t : Q) ∈ Subgroup.centralizer (CFSG.layer Q : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [← hP'eq] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      exact congrArg Subtype.val (hTP t ht p hp)
    rw [centralizer_layer_eq_bot hsol, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  refine le_antisymm ?_ (hP'eq ▸ hP'Y)
  intro y hy
  obtain ⟨p, hp⟩ := hι (QuotientGroup.mk (⟨y, hy⟩ : ↥Y))
  have hp' : (p : ↥Y)⁻¹ * ⟨y, hy⟩ ∈ T := by
    have : QuotientGroup.mk (p : ↥Y) = (QuotientGroup.mk (⟨y, hy⟩ : ↥Y) : ↥Y ⧸ T) := hp
    exact QuotientGroup.eq.mp this
  rw [hT1, Subgroup.mem_bot, inv_mul_eq_one] at hp'
  rw [← hP'eq]
  exact ⟨p, p.2, by rw [hp']; rfl⟩

section Transfer

variable {H : Type*} [Group H] [Finite H]

theorem card_quot_oStar_eq :
    Nat.card (↥(oStar H) ⧸ CFSG.solvableRadical ↥(oStar H)) =
      Nat.card ↥(CFSG.layer (H ⧸ CFSG.solvableRadical H)) := by
  set R := CFSG.solvableRadical H with hR
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical
  set π := QuotientGroup.mk' R with hπ
  let ψ : ↥(oStar H) →* ↥(CFSG.layer (H ⧸ R)) :=
    (π.comp (oStar H).subtype).codRestrict (CFSG.layer (H ⧸ R)) fun x =>
      (mem_oStar_iff_map_mem_layer x.1).mp x.2
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective R y
    exact ⟨⟨h, (mem_oStar_iff_map_mem_layer h).mpr (by rw [hh]; exact y.2)⟩, Subtype.ext hh⟩
  have hψker : Group.IsSolvable ψ.ker := by
    let g : ψ.ker →* R := ((oStar H).subtype.comp ψ.ker.subtype).codRestrict R (fun x => by
      have hx := MonoidHom.mem_ker.mp x.2
      have := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp this)
    refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have h1 := Nat.card_congr (KAPI.solQuotEquiv hψs hψker).toEquiv
  rw [h1]
  have hrad : CFSG.solvableRadical ↥(CFSG.layer (H ⧸ R)) = ⊥ := by
    have hlayerN : (CFSG.layer (H ⧸ R)).Normal := by
      have : (CFSG.layer (H ⧸ R)).Characteristic := CFSG.LocalCores.layer_characteristic
      infer_instance
    have h := map_subtype_solvableRadical_eq_inf (hlayerN.isSubnormal)
    rw [solvableRadical_quotient, inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (CFSG.layer _).subtype_injective).mp h
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hrad).trans
    QuotientGroup.quotientBot).toEquiv

theorem card_quot_le_oStar (hC : HypC H) {Y : Subgroup H} (hY : Y ∈ bSet H)
    (hdeg : deg ↥(oStar H) ≤ deg ↥Y) :
    Nat.card (↥Y ⧸ CFSG.solvableRadical ↥Y) ≤
        Nat.card (↥(oStar H) ⧸ CFSG.solvableRadical ↥(oStar H)) ∧
      (Nat.card (↥(oStar H) ⧸ CFSG.solvableRadical ↥(oStar H)) ≤
          Nat.card (↥Y ⧸ CFSG.solvableRadical ↥Y) →
        (Y : Set H) * (CFSG.solvableRadical H : Set H) = (oStar H : Set H)) := by
  have hYo : oStar ↥Y = ⊤ := (kOf_eq_self_iff_oStar_eq_top Y).mp hY
  obtain ⟨hYbo, hYbd, hYbc⟩ := map_quotient_props hYo
  set π := QuotientGroup.mk' (CFSG.solvableRadical H) with hπ
  obtain ⟨hc1, hc2⟩ := card_quot_le_layer solvableRadical_quotient (hypB_components_quotient hC)
    hYbo (by rw [deg_layer_quotient, hYbd]; exact hdeg)
  rw [hYbc] at hc1 hc2
  rw [card_quot_oStar_eq]
  refine ⟨hc1, fun hle => ?_⟩
  have hYb : Y.map π = CFSG.layer (H ⧸ CFSG.solvableRadical H) := hc2 (le_antisymm hc1 hle)
  ext x
  constructor
  · rintro ⟨y, hy, r, hr, rfl⟩
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical H) r = 1 :=
      (QuotientGroup.eq_one_iff r).mpr hr
    rw [SetLike.mem_coe, mem_oStar_iff_map_mem_layer, map_mul, h1, mul_one, ← hYb]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [SetLike.mem_coe, mem_oStar_iff_map_mem_layer, ← hYb] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
    rw [SetLike.mem_coe, ← QuotientGroup.ker_mk' (CFSG.solvableRadical H), MonoidHom.mem_ker,
      map_mul, map_inv, hyx, inv_mul_cancel]

end Transfer

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
