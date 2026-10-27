module

public import CFSG.GroupTheory.InvariantSubgroup
public import CFSG.RankThree.GF2n.Tim79aSec23Twist
public import CFSG.RankThree.GF2n.Tim79aSec23MinGrp
public import CFSG.RankThree.GF2n.Tim79aSec23Tilde

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

theorem exists_lift_H (y : Xbar V H) :
    ∃ (h : G) (hh : h ∈ H), piBar V H ⟨h, hh⟩ = (y : Hbar V H) := by
  obtain ⟨x, -, hx⟩ := mem_barOf_iff.mp y.2
  exact ⟨x.1, x.2, hx⟩

theorem isPGroup_barOf_sup_iff_vy {y : Xbar V H} {h : G} (hh : h ∈ H)
    (hlift : piBar V H ⟨h, hh⟩ = (y : Hbar V H)) :
    IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V)) ↔
      IsPGroup 2 ↥(Vy V H ⊔ conjSubgroup y (Vy V H)) := by
  set N := barOf V H (xOf V H) with hN
  have hconj : barOf V H (conjSubgroup h V) = conjSubgroup (y : Hbar V H) (barOf V H V) := by
    rw [← hlift]
    exact (conjSubgroup_piBar_barOf ⟨h, hh⟩ V).symm
  have hV : barOf V H V ≤ N := barOf_V_le V H
  have hcV : conjSubgroup (y : Hbar V H) (barOf V H V) ≤ N := by
    intro z hz
    have h1 := hV (mem_conjSubgroup.mp hz)
    have : z = (y : Hbar V H) * ((y : Hbar V H)⁻¹ * z * (y : Hbar V H)) *
        (y : Hbar V H)⁻¹ := by group
    rw [this]
    exact N.mul_mem (N.mul_mem y.2 h1) (N.inv_mem y.2)
  have e1 : Vy V H = (barOf V H V).subgroupOf N := rfl
  have e2 : conjSubgroup y (Vy V H) =
      (conjSubgroup (y : Hbar V H) (barOf V H V)).subgroupOf N :=
    (subgroupOf_conjSubgroup N (barOf V H V) y).symm
  have e3 : Vy V H ⊔ conjSubgroup y (Vy V H) =
      (barOf V H V ⊔ conjSubgroup (y : Hbar V H) (barOf V H V)).subgroupOf N := by
    rw [e2, e1, Subgroup.subgroupOf_sup hV hcV]
  rw [hconj, e3]
  exact ⟨fun h => h.of_equiv (Subgroup.subgroupOfEquivOfLe (sup_le hV hcV)).symm,
    fun h => h.of_equiv (Subgroup.subgroupOfEquivOfLe (sup_le hV hcV))⟩

@[expose] noncomputable def tildeAut (V H : Subgroup G) (b : Hbar V H) :
    MulAut (Xbar V H ⧸ Subgroup.center (Xbar V H)) :=
  haveI := normal_barOf_xOf V H
  QuotientGroup.congr (Subgroup.center (Xbar V H)) (Subgroup.center (Xbar V H))
    (MulAut.conjNormal b) (Subgroup.map_center_eq (MulAut.conjNormal b))

theorem tildeAut_mk (b : Hbar V H) (z : Xbar V H) :
    tildeAut V H b (QuotientGroup.mk' (Subgroup.center (Xbar V H)) z) =
      QuotientGroup.mk' (Subgroup.center (Xbar V H))
        (haveI := normal_barOf_xOf V H; MulAut.conjNormal b z) := by
  unfold tildeAut
  exact QuotientGroup.congr_mk _ _ _ _ z

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem vy_sq {a : Xbar V H} (ha : a ∈ Vy V H) : a * a = 1 := by
  have h := hc.barOf_V_sq (Subgroup.mem_subgroupOf.mp ha)
  apply Subtype.ext
  simpa [pow_two] using h

theorem isPGroup_barOf_sup_iff_tilde {y : Xbar V H} {h : G} (hh : h ∈ H)
    (hlift : piBar V H ⟨h, hh⟩ = (y : Hbar V H)) :
    IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V)) ↔
      IsPGroup 2 ↥(Vtilde V H ⊔ conjSubgroup (QuotientGroup.mk' (Subgroup.center (Xbar V H)) y)
        (Vtilde V H)) :=
  (isPGroup_barOf_sup_iff_vy hh hlift).trans
    (isPGroup_sup_iff_map_center (fun _ ha => hc.vy_sq ha) y)

theorem commute_of_isPGroup_tilde {y : Xbar V H}
    (h2 : IsPGroup 2 ↥(Vtilde V H ⊔ conjSubgroup
      (QuotientGroup.mk' (Subgroup.center (Xbar V H)) y) (Vtilde V H))) :
    ∀ a ∈ Vy V H, ∀ b ∈ conjSubgroup y (Vy V H), a * b = b * a := by
  obtain ⟨h, hh, hlift⟩ := exists_lift_H (V := V) (H := H) y
  have h2' := (hc.isPGroup_barOf_sup_iff_tilde hh hlift).mpr h2
  have hcomm := hc.commute_of_isPGroup_barOf_sup hh h2'
  intro a ha b hb
  obtain ⟨u, hu, hua⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp ha)
  have hb' : y⁻¹ * b * y ∈ Vy V H := mem_conjSubgroup.mp hb
  obtain ⟨u', hu', hu'b⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hb')
  have hv : h * (u' : G) * h⁻¹ ∈ conjSubgroup h V := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hu'
  have key := hcomm (u : G) hu _ hv
  have key' : u * (⟨h, hh⟩ * u' * ⟨h, hh⟩⁻¹) = (⟨h, hh⟩ * u' * ⟨h, hh⟩⁻¹) * u :=
    Subtype.ext (by simpa using key)
  have key2 := congrArg (piBar V H) key'
  simp only [map_mul, map_inv, hua, hlift, hu'b] at key2
  apply Subtype.ext
  have e : (y : Hbar V H) * ((y : Hbar V H)⁻¹ * (b : Hbar V H) * (y : Hbar V H)) *
      (y : Hbar V H)⁻¹ = (b : Hbar V H) := by group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key2 ⊢
  rw [e] at key2
  exact key2

theorem exists_vy_mem_Dy (hd : Sec23Data V H) :
    ∃ a ∈ Vy V H, a ∈ Dy V H ∧
      QuotientGroup.mk' (Subgroup.center (Xbar V H)) a ≠ 1 := by
  obtain ⟨⟨v, hvV⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.barOf_V_ne_bot
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hvX : v ∈ barOf V H (xOf V H) := barOf_V_le V H hvV
  have haD : (⟨v, hvX⟩ : Xbar V H) ∈ Dy V H := hc.barOf_V_subset_dbarOf hvV hv1
  refine ⟨⟨v, hvX⟩, Subgroup.mem_subgroupOf.mpr hvV, haD, fun h => ?_⟩
  exact hd.noncentral _ haD ((QuotientGroup.eq_one_iff _).mp h)

theorem commute_of_mem_barOf_P {b a : Hbar V H} (hb : b ∈ barOf V H P)
    (ha : a ∈ barOf V H V) : b * a = a * b := by
  obtain ⟨p, hp, rfl⟩ := mem_barOf_iff.mp hb
  obtain ⟨v, hv, rfl⟩ := mem_barOf_iff.mp ha
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc.commute_of_mem_P hp hv).symm

theorem tildeAut_fix {b : Hbar V H} (hb : b ∈ barOf V H P) :
    ∀ v ∈ Vtilde V H, tildeAut V H b v = v := by
  rintro _ ⟨a, ha, rfl⟩
  rw [tildeAut_mk]
  congr 1
  apply Subtype.ext
  haveI := normal_barOf_xOf V H
  rw [MulAut.conjNormal_apply]
  have := hc.commute_of_mem_barOf_P hb (Subgroup.mem_subgroupOf.mp ha)
  simp only [mul_inv_eq_iff_eq_mul]
  exact this

theorem false_of_invariant
    (hsimple : IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)))
    (hd : Sec23Data V H) (x : Xbar V H ⧸ Subgroup.center (Xbar V H))
    (Λ : Subgroup (Xbar V H ⧸ Subgroup.center (Xbar V H)))
    (hnp : ¬ IsPGroup 2 ↥(Vtilde V H ⊔ conjSubgroup x (Vtilde V H)))
    (hxΛ : conjSubgroup x (Vtilde V H) ≤ Λ) (hΛ : Λ ≠ ⊤)
    (hinv : ∀ α : MulAut (Xbar V H ⧸ Subgroup.center (Xbar V H)),
      (∀ v ∈ Vtilde V H, α v = v) → Λ.map α.toMonoidHom ≤ Λ) : False := by
  haveI := normal_barOf_xOf V H
  haveI := hsimple
  set π := QuotientGroup.mk' (Subgroup.center (Xbar V H)) with hπ
  obtain ⟨ŷ, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨h, hh, hlift⟩ := exists_lift_H (V := V) (H := H) ŷ
  have hnp' : ¬ IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V)) := fun h2 =>
    hnp ((hc.isPGroup_barOf_sup_iff_tilde hh hlift).mp h2)
  set Ybar : Subgroup (Hbar V H) := (Λ.comap π).map (barOf V H (xOf V H)).subtype with hY
  have hmemY : ∀ z : Xbar V H, (z : Hbar V H) ∈ Ybar ↔ π z ∈ Λ := by
    intro z
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := Subtype.ext hwz
      subst this
      exact hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hconj : ∀ b ∈ barOf V H P, ∀ u ∈ Ybar, b * u * b⁻¹ ∈ Ybar := by
    intro b hb u hu
    obtain ⟨z, hz, rfl⟩ := hu
    have hzz : (b * (z : Hbar V H) * b⁻¹) =
        ((MulAut.conjNormal b z : Xbar V H) : Hbar V H) := by
      rw [MulAut.conjNormal_apply]
    rw [Subgroup.coe_subtype, hzz, hmemY, ← tildeAut_mk]
    exact hinv (tildeAut V H b) (hc.tildeAut_fix hb) ⟨π z, hz, rfl⟩
  have hP : barOf V H P ≤ Subgroup.normalizer (Ybar : Set (Hbar V H)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hconj b hb u hu
    · intro hu
      have := hconj b⁻¹ ((barOf V H P).inv_mem hb) _ hu
      simpa [mul_assoc] using this
  have hU : barOf V H (conjSubgroup h V) ≤ Subgroup.normalizer (Ybar : Set (Hbar V H)) := by
    refine le_trans ?_ (Subgroup.le_normalizer (H := Ybar))
    intro u hu
    have e := conjSubgroup_piBar_barOf (V := V) (H := H) ⟨h, hh⟩ V
    rw [hlift] at e
    have hu' : u ∈ conjSubgroup (ŷ : Hbar V H) (barOf V H V) := by
      rw [e]
      exact hu
    have hw := mem_conjSubgroup.mp hu'
    have hwN : (ŷ : Hbar V H)⁻¹ * u * (ŷ : Hbar V H) ∈ barOf V H (xOf V H) :=
      barOf_V_le V H hw
    set w' : Xbar V H := ⟨_, hwN⟩ with hw'
    have hw'V : w' ∈ Vy V H := Subgroup.mem_subgroupOf.mpr hw
    have hzu : ((ŷ * w' * ŷ⁻¹ : Xbar V H) : Hbar V H) = u := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw']
      group
    rw [← hzu, hmemY]
    apply hxΛ
    rw [mem_conjSubgroup]
    have : (π ŷ)⁻¹ * π (ŷ * w' * ŷ⁻¹) * π ŷ = π w' := by
      simp only [map_mul, map_inv]
      group
    rw [this]
    exact ⟨w', hw'V, rfl⟩
  have htop := hc.eq_top_of_not_isPGroup hh hnp' hP hU
  haveI hnormY : Ybar.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  haveI hΛn : Λ.Normal := by
    refine ⟨fun l hl w => ?_⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ l
    obtain ⟨z₂, rfl⟩ := QuotientGroup.mk'_surjective _ w
    have h1 : (z : Hbar V H) ∈ Ybar := (hmemY z).mpr hl
    have h2 := hnormY.conj_mem _ h1 (z₂ : Hbar V H)
    have e : (z₂ : Hbar V H) * z * (z₂ : Hbar V H)⁻¹ = ((z₂ * z * z₂⁻¹ : Xbar V H) : Hbar V H) :=
      rfl
    rw [e, hmemY] at h2
    simpa only [map_mul, map_inv] using h2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Λ with h0 | h1
  · obtain ⟨a, haV, -, ha1⟩ := hc.exists_vy_mem_Dy hd
    have hmem : π ŷ * π a * (π ŷ)⁻¹ ∈ Λ := hxΛ ⟨π a, ⟨a, haV, rfl⟩, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    apply ha1
    have : π a = (π ŷ)⁻¹ * (π ŷ * π a * (π ŷ)⁻¹) * π ŷ := by group
    rw [this, hmem]
    group
  · exact hΛ h1

theorem isElemAbelian_Vy : IsElemAbelian 2 (Vy V H) :=
  ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (by
    simpa using hc.barOf_V_comm (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩, fun x hx => by
      rw [pow_two]
      exact hc.vy_sq hx⟩

theorem isElemAbelian_Vtilde : IsElemAbelian 2 (Vtilde V H) :=
  (hc.isElemAbelian_Vy).map _

theorem Vtilde_mem_Dtilde {a : Xbar V H ⧸ Subgroup.center (Xbar V H)}
    (ha : a ∈ Vtilde V H) (ha1 : a ≠ 1) : a ∈ Dtilde V H := by
  obtain ⟨v, hv, rfl⟩ := ha
  have hv1 : v ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hv' : (v : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.mp hv
  exact ⟨v, hc.barOf_V_subset_dbarOf hv' (fun h => hv1 (Subtype.ext h)), rfl⟩

theorem exists_Vtilde_ne_one (hd : Sec23Data V H) :
    ∃ a ∈ Vtilde V H, a ≠ 1 ∧ a ∈ Dtilde V H := by
  obtain ⟨a, haV, haD, ha1⟩ := hc.exists_vy_mem_Dy hd
  exact ⟨QuotientGroup.mk' _ a, ⟨a, haV, rfl⟩, ha1, ⟨a, haD, rfl⟩⟩

theorem Vtilde_ne_bot (hd : Sec23Data V H) : Vtilde V H ≠ ⊥ := by
  obtain ⟨a, haV, ha1, -⟩ := hc.exists_Vtilde_ne_one hd
  intro h
  rw [h, Subgroup.mem_bot] at haV
  exact ha1 haV

theorem classD_Vtilde (hd : Sec23Data V H)
    (hnd : ∃ d ∈ Dy V H, ∃ e ∈ Dy V H, orderOf (d * e) = 4) :
    classD (Vtilde V H) = Dtilde V H := by
  have hH := hc.tilde_hyp hd hnd
  obtain ⟨a₀, ha₀V, ha₀1, ha₀D⟩ := hc.exists_Vtilde_ne_one hd
  ext x
  constructor
  · rintro ⟨g, t, ht, ht1, rfl⟩
    simpa using hH.conj_mem g⁻¹ (hc.Vtilde_mem_Dtilde ht ht1)
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (hH.isConj ha₀D hx)
    exact ⟨g⁻¹, a₀, ha₀V, ha₀1, by rw [inv_inv, hg]⟩

theorem card_Vtilde (hd : Sec23Data V H) : Nat.card (Vtilde V H) = Nat.card (barOf V H V) := by
  set π := QuotientGroup.mk' (Subgroup.center (Xbar V H)) with hπ
  have hbij : Function.Bijective ((π.subgroupMap (Vy V H))) := by
    refine ⟨?_, MonoidHom.subgroupMap_surjective _ _⟩
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : π (a : Xbar V H) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have h2 : (a : Xbar V H) ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff _).mp h1
    by_contra hne
    have haV : (a : Xbar V H) ∈ Vy V H := a.2
    have hne' : (a : Xbar V H) ≠ 1 := fun h => hne (Subtype.ext h)
    have hv' : ((a : Xbar V H) : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.mp haV
    have hD : (a : Xbar V H) ∈ Dy V H :=
      hc.barOf_V_subset_dbarOf hv' (fun h => hne' (Subtype.ext h))
    exact hd.noncentral _ hD h2
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm.trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (barOf_V_le V H)).toEquiv)

end MinCex

end CFSG.RankThree.GF2n.Tim79a
