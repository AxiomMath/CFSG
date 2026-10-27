module

public import CFSG.Quasithin.Background.B4L3Coord
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3AAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_card_sec_of_l3Data [Finite W] {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) :
    Nat.card (Sec I Z) = 8 := by
  classical
  have hβ := Subgroup.card_ker_mul_card_range D.β
  have hker : D.β.ker = Z.subgroupOf I := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact D.ker_β u
  have hkerCard : Nat.card ↥D.β.ker = Nat.card ↥Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv
  have hrange : D.β.range = ⊤ := MonoidHom.range_eq_top.mpr D.β_surj
  have hrangeCard : Nat.card ↥D.β.range = 8 := by
    rw [hrange, Subgroup.card_top]
    exact CFSG.Quasithin.L3Data.card_vec
  have hI : Nat.card ↥I = Nat.card ↥Z * 8 := by
    rw [hkerCard, hrangeCard] at hβ
    exact hβ.symm
  have hsec := CFSG.Quasithin.card_sec_mul (V := W) (W := I) (U := Z) hZI
  have hpos : 0 < Nat.card ↥Z := Nat.card_pos
  have : Nat.card (Sec I Z) * Nat.card ↥Z = 8 * Nat.card ↥Z := by
    rw [hsec, hI]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

private noncomputable def s16h_secEquivOfL3Data [Finite W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) :
    Sec I Z ≃* Multiplicative CFSG.Quasithin.L3.Vec := by
  classical
  have hker : Z.subgroupOf I ≤ D.β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    exact (D.ker_β u).mpr (Subgroup.mem_subgroupOf.mp hu)
  let κ : Sec I Z →* Multiplicative CFSG.Quasithin.L3.Vec :=
    QuotientGroup.lift (Z.subgroupOf I) D.β hker
  have hκmk : ∀ u : ↥I, κ (QuotientGroup.mk u) = D.β u := fun u => rfl
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [hκmk] at hx
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr ((D.ker_β u).mp hx)
  have hκsurj : Function.Surjective κ := by
    intro y
    obtain ⟨u, hu⟩ := D.β_surj y
    exact ⟨QuotientGroup.mk u, by rw [hκmk, hu]⟩
  exact MulEquiv.ofBijective κ ⟨hκinj, hκsurj⟩

private theorem s16h_secEquivOfL3Data_mk [Finite W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (u : ↥I) :
    s16h_secEquivOfL3Data D hZI (QuotientGroup.mk u) = D.β u := by
  unfold s16h_secEquivOfL3Data
  rfl

private theorem s16h_secEquivOfL3Data_secHom [Finite W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hLI : L ≤ stabSub I)
    (hLZ : L ≤ stabSub Z) {δ : CFSG.Quasithin.L3.Γ} (x : Sec I Z) :
    s16h_secEquivOfL3Data D hZI
        (CFSG.Quasithin.B5.secHom L hLI hLZ (D.π δ) x) =
      Multiplicative.ofAdd (CFSG.Quasithin.L3.act δ
        (Multiplicative.toAdd (s16h_secEquivOfL3Data D hZI x))) := by
  classical
  induction x using QuotientGroup.induction_on with
  | H u =>
    have hu : ((D.π δ : ↥L) : MulAut W) (u : W) ∈ I :=
      D.inv_U (D.π δ) (D.π δ).2 u u.2
    have h1 := D.equi δ u hu
    rw [CFSG.Quasithin.B5.secHom_mk]
    rw [s16h_secEquivOfL3Data_mk D hZI, s16h_secEquivOfL3Data_mk D hZI]
    exact h1

private def s16h_img (Z I U : Subgroup W) : Subgroup (Sec U Z) :=
  Subgroup.map (QuotientGroup.mk' (Z.subgroupOf U)) (I.subgroupOf U)

private theorem s16h_iSup_fin_two {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ i, f i) = f 0 ⊔ f 1 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i <;> simp
  · exact sup_le (le_iSup _ _) (le_iSup _ _)

private theorem s16h_iSup_ne_zero {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ (j : Fin 2) (_ : j ≠ 0), f j) = f 1 := by
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    rw [hj1]
  · exact le_iSup_of_le 1 (le_iSup_of_le (by norm_num) le_rfl)

private theorem s16h_img_inf_eq_bot [Finite W] {Z I J U : Subgroup W}
    (hZI : Z ≤ I) (hZJ : Z ≤ J) (hIU : I ≤ U) (hJU : J ≤ U) (hinf : I ⊓ J ≤ Z) :
    s16h_img Z I U ⊓ s16h_img Z J U = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxI, hxJ⟩ := hx
  rw [s16h_img] at hxI hxJ
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxI
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hxJ
  rw [Subgroup.mem_bot]
  have huI : (u : W) ∈ I := Subgroup.mem_subgroupOf.mp hu
  have hvJ : (v : W) ∈ J := Subgroup.mem_subgroupOf.mp hv
  have hzu : (u : W) ∈ Z := by
    have h1 : (v * u⁻¹ : ↥U) ∈ Z.subgroupOf U := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (Z.subgroupOf U) (v * u⁻¹) = 1
      rw [map_mul, map_inv, hvu, mul_inv_cancel]
    have hz : ((v * u⁻¹ : ↥U) : W) ∈ Z := Subgroup.mem_subgroupOf.mp h1
    have hmemJ : (u : W) ∈ J := by
      have h2 : (((v * u⁻¹ : ↥U) : W))⁻¹ ∈ Z := Z.inv_mem hz
      have h3 : (((v * u⁻¹ : ↥U) : W))⁻¹ * (v : W) = (u : W) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [← h3]
      exact mul_mem (hZJ h2) hvJ
    exact hinf ⟨huI, hmemJ⟩
  exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr hzu)

private theorem s16h_img_sup_eq_top [Finite W] {Z I J U : Subgroup W}
    (hIU : I ≤ U) (hJU : J ≤ U) (hIJ : I ⊔ J = U) :
    s16h_img Z I U ⊔ s16h_img Z J U = ⊤ := by
  rw [s16h_img, s16h_img, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hIU hJU, hIJ,
    Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (N := Z.subgroupOf U))

private theorem s16h_img_card [Finite W] {L : Subgroup (MulAut W)} {Z I U : Subgroup W}
    (D : CFSG.Quasithin.L3Data L I Z) (hZI : Z ≤ I) (hIU : I ≤ U) :
    Nat.card ↥(s16h_img Z I U) = 8 := by
  have hinj := s16h_secIncl_injective Z I U hIU
  have hrange := s16h_secIncl_range Z I U hIU
  let e : Sec I Z ≃ ↥(s16h_img Z I U) := Equiv.ofBijective
    (fun x => ⟨s16h_secIncl Z I U hIU x, by
      rw [show s16h_img Z I U = (s16h_secIncl Z I U hIU).range from hrange.symm]
      exact ⟨x, rfl⟩⟩)
    ⟨fun x y h => hinj (Subtype.ext_iff.mp h), fun y => by
      have hy : (y : Sec U Z) ∈ (s16h_secIncl Z I U hIU).range := by
        rw [hrange]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e]
  exact s16h_card_sec_of_l3Data D hZI

private theorem s16h_eq_of_mul_eq_mul {Q : Type*} [CommGroup Q] {A B : Subgroup Q}
    (hinf : A ⊓ B = ⊥) {a a' b b' : Q} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hA : a'⁻¹ * a ∈ A := mul_mem (A.inv_mem ha') ha
  have hB : b' * b⁻¹ ∈ B := mul_mem hb' (B.inv_mem hb)
  have hbot : a'⁻¹ * a ∈ (⊥ : Subgroup Q) := by
    rw [← hinf]
    refine ⟨hA, ?_⟩
    rw [h1]
    exact hB
  have h2 : a'⁻¹ * a = 1 := Subgroup.mem_bot.mp hbot
  have haeq : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' * 1 := by rw [h2]
      _ = a' := mul_one _
  have hbeq : b = b' := by
    rw [haeq] at h
    exact mul_left_cancel h
  exact ⟨haeq, hbeq⟩

private theorem s16h_card_dvd_of_free {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x) : Nat.card G ∣ Nat.card X := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype X := Fintype.ofFinite X
  have hsum := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hfixed : ∀ g : G, Fintype.card (MulAction.fixedBy X g) =
      if g = 1 then Fintype.card X else 0 := by
    intro g
    by_cases hg : g = 1
    · subst hg
      rw [if_pos rfl]
      have hone : MulAction.fixedBy X (1 : G) = Set.univ := by
        ext x
        simp [MulAction.mem_fixedBy]
      exact Fintype.card_congr ((Set.equivOfEq hone).trans (Equiv.Set.univ X))
    · rw [if_neg hg]
      have hempty : MulAction.fixedBy X g = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hfree g hg x ((MulAction.mem_fixedBy).mp hx)).elim
        · intro hx
          simp at hx
      haveI : IsEmpty ↥(MulAction.fixedBy X g) := by
        refine ⟨fun x => ?_⟩
        have hx : (x : X) ∈ (∅ : Set X) := hempty ▸ x.2
        simpa using hx
      exact Fintype.card_eq_zero_iff.mpr inferInstance
  rw [Finset.sum_congr rfl (fun g _ => hfixed g)] at hsum
  rw [Finset.sum_ite_eq' Finset.univ (1 : G) (fun _ => Fintype.card X)] at hsum
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [Finset.mem_univ, if_true] at hsum
  exact ⟨_, by rw [hsum, mul_comm]⟩

theorem s16h_twoNat_covering [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hS : SumOfNat (fun H U Z => CFSG.Quasithin.BinaryNaturalSL H U Z 3 1) L U Z 2)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hLcard : Nat.card ↥L = 168)
    (E : Subgroup (MulAut W)) (hEN : E ≤ normalizer (L : Set (MulAut W)))
    (hEU : E ≤ stabSub U) (hEZ : E ≤ stabSub Z) (hEab : IsElemAbelian 3 E)
    (hEcard : 9 * Nat.card ↥(E ⊓ centSub U) ≤ Nat.card ↥E)
    (hErank : Nat.card ↥(autSub E U) ≤ 9) (hZcard : Nat.card ↥Z ≤ 2) :
    ∀ v : Sec U Z, v ≠ 1 → ∃ g : ↥L, ∃ b : ↥E, (b : MulAut W) ∉ centSub U ∧
      ∃ (hmem : (g : MulAut W) * (b : MulAut W) * (g : MulAut W)⁻¹ ∈
          stabSub U ⊓ stabSub Z),
        CFSG.Quasithin.B5.secHom (stabSub U ⊓ stabSub Z) inf_le_left inf_le_right
          ⟨(g : MulAut W) * (b : MulAut W) * (g : MulAut W)⁻¹, hmem⟩ v = v := by
  intro v hvne
  classical
  obtain ⟨d, hdne, l, hdfix⟩ :=
    s16h_twoNat_orbit_fix hS hLU hLZ hLcard E hEN hEU hEZ hEab hEcard hErank hZcard v hvne
  set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀
  have hX₀U : X₀ ≤ stabSub U := inf_le_left
  have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
  have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
  have hLX₀ : L ≤ X₀ := le_inf hLU hLZ
  have hEsecEq : (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
      autSec E U Z :=
    CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀
  have hLsecEq : (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) =
      autSec L U Z :=
    CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hLX₀
  have hdmem : (d : MulAut (Sec U Z)) ∈
      (E.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) := by
    rw [hEsecEq]
    exact d.2
  obtain ⟨b0, hb0E, hb0sec⟩ := Subgroup.mem_map.mp hdmem
  have hlmem : (CFSG.Quasithin.B5.secHom L hLU hLZ l : MulAut (Sec U Z)) ∈
      (L.subgroupOf X₀).map (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) := by
    rw [hLsecEq, ← CFSG.Quasithin.B5.range_secHom L hLU hLZ]
    exact ⟨l, rfl⟩
  obtain ⟨l0, hl0L, hl0sec⟩ := Subgroup.mem_map.mp hlmem
  have h1 : (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) l0 v =
      CFSG.Quasithin.B5.secHom L hLU hLZ l v := by
    rw [hl0sec]
  have hinv : (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0)⁻¹
      (CFSG.Quasithin.B5.secHom L hLU hLZ l v) = v := by
    rw [hl0sec]
    have hcancel : (CFSG.Quasithin.B5.secHom L hLU hLZ l)⁻¹ *
        CFSG.Quasithin.B5.secHom L hLU hLZ l = 1 := inv_mul_cancel _
    calc (CFSG.Quasithin.B5.secHom L hLU hLZ l)⁻¹
          (CFSG.Quasithin.B5.secHom L hLU hLZ l v)
        = ((CFSG.Quasithin.B5.secHom L hLU hLZ l)⁻¹ *
            CFSG.Quasithin.B5.secHom L hLU hLZ l) v := rfl
      _ = (1 : MulAut (Sec U Z)) v := by rw [hcancel]
      _ = v := rfl
  have h3 : (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) (l0⁻¹ * b0 * l0) v = v := by
    rw [map_mul, map_mul, map_inv]
    change (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0)⁻¹
      ((CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0)
        ((CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z l0) v)) = v
    rw [h1, hb0sec, hdfix]
    exact hinv
  have hb0E' : ((b0 : X₀) : MulAut W) ∈ E := Subgroup.mem_subgroupOf.mp hb0E
  have hl0L' : ((l0 : X₀) : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hl0L
  have hbcent : ((b0 : X₀) : MulAut W) ∉ centSub U := by
    intro hbc
    have hcentsec : ((b0 : X₀) : MulAut W) ∈ centSec U Z :=
      centSub_le_centSec U Z hbc
    have hker : b0 ∈ (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z).ker :=
      (CFSG.Quasithin.B5.mem_ker_secHom X₀ hX₀U hX₀Z b0).2 hcentsec
    have hb0one : CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z b0 = 1 :=
      MonoidHom.mem_ker.mp hker
    have hd1 : (d : MulAut (Sec U Z)) = 1 := by
      rw [← hb0sec]
      exact hb0one
    exact hdne hd1
  refine ⟨⟨((l0 : X₀) : MulAut W)⁻¹, L.inv_mem hl0L'⟩,
    ⟨((b0 : X₀) : MulAut W), hb0E'⟩, hbcent, ?_, ?_⟩
  · simp only [hX₀]
    exact (l0⁻¹ * b0 * l0).2
  · change (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z) (l0⁻¹ * b0 * l0) v = v
    exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
