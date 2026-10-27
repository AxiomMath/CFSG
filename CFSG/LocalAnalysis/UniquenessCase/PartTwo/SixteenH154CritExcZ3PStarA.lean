module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_z3_subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
    (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem s16h_z3_barImage11_barPreimage11 (D : Data G) {V₀ V : Subgroup G}
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal]
    (Xbar : Subgroup (F11.MBar11 D.M V₀ V)) :
    F11.barImage11 D.M V₀ V (F11.barPreimage11 D.M V₀ V Xbar) = Xbar := by
  have hsub : (((Xbar.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M))).map
      D.M.subtype).subgroupOf D.M) =
      Xbar.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold F11.barImage11 F11.barPreimage11
  rw [hsub]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Xbar

theorem s16h_z3_card_eq_barSub_mul {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {M Y : Subgroup G} (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hY : Y ≤ stabTil V₀ V) :
    Nat.card ↥Y = Nat.card ↥(barSub V₀ V hV Y) * Nat.card ↥(Y ⊓ F11.CTilde M V₀ V) := by
  have h := uc22p22u_card_eq_map_mul_inf_ker (actTil V₀ V hV) (Y.subgroupOf (stabTil V₀ V))
  have h1 : (Y.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) = barSub V₀ V hV Y := rfl
  have h2 : (Y.subgroupOf (stabTil V₀ V)) ⊓ (actTil V₀ V hV).ker =
      (Y ⊓ F11.CTilde M V₀ V).subgroupOf (stabTil V₀ V) := by
    ext x
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hxY, hx1⟩
      refine ⟨hxY, ?_⟩
      change (x : G) ∈ F11.CTilde M V₀ V
      rw [mem_cTilde_iff (M := M) (V₀ := V₀) (V := V) hV hM]
      exact ⟨hYM hxY, x.2, by simpa using hx1⟩
    · rintro ⟨hxY, hxC⟩
      refine ⟨hxY, ?_⟩
      change (x : G) ∈ F11.CTilde M V₀ V at hxC
      obtain ⟨-, h, h1⟩ := (mem_cTilde_iff (M := M) (V₀ := V₀) (V := V) hV hM).1 hxC
      rw [show x = (⟨(x : G), h⟩ : stabTil V₀ V) from Subtype.ext rfl]
      exact h1
  have h3 : Nat.card ↥(Y.subgroupOf (stabTil V₀ V)) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have h4 : Nat.card ↥((Y ⊓ F11.CTilde M V₀ V).subgroupOf (stabTil V₀ V)) =
      Nat.card ↥(Y ⊓ F11.CTilde M V₀ V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hY)).toEquiv
  rw [h1, h2, h4, h3] at h
  exact h

theorem s16h_z3_le_cTilde_of_barSub_eq_bot {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {M Y : Subgroup G} (hM : M ≤ normalizer (V : Set G)) (hYM : Y ≤ M)
    (hY : Y ≤ stabTil V₀ V) (hbar : barSub V₀ V hV Y = ⊥) :
    Y ≤ F11.CTilde M V₀ V := by
  intro y hy
  rw [mem_cTilde_iff (M := M) (V₀ := V₀) (V := V) hV hM]
  refine ⟨hYM hy, hY hy, ?_⟩
  have hmem : actTil V₀ V hV ⟨y, hY hy⟩ ∈ barSub V₀ V hV Y :=
    actTil_mem_barSub V₀ V hV hy (hY hy)
  rw [hbar] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem s16h_z3_conj_mem_barSub {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {N Y : Subgroup G} (hN : N ≤ normalizer (Y : Set G))
    {n : stabTil V₀ V} (hn : (n : G) ∈ N)
    {ψ : MulAut (Vtil V₀ V hV)} (hψ : ψ ∈ barSub V₀ V hV Y) :
    actTil V₀ V hV n * ψ * (actTil V₀ V hV n)⁻¹ ∈ barSub V₀ V hV Y := by
  obtain ⟨y, hy, rfl⟩ := (mem_barSub V₀ V hV Y ψ).1 hψ
  have hny : ((n * y * n⁻¹ : stabTil V₀ V) : G) ∈ Y := by
    have h := (Subgroup.mem_normalizer_iff.1 (hN hn) (y : G)).1 hy
    simpa using h
  have hval : actTil V₀ V hV n * actTil V₀ V hV y * (actTil V₀ V hV n)⁻¹ =
      actTil V₀ V hV (n * y * n⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
  rw [hval]
  exact actTil_mem_barSub V₀ V hV hny (n * y * n⁻¹).2

theorem s16h_z3_exists_xbar_of_bar {D : Data G} {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p n : ℕ}
    {X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))}
    (hXn : ∀ q ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, ∀ x ∈ X, q * x * q⁻¹ ∈ X)
    (hXe : IsElemAbelian p X)
    (hXd : X ≤ ⁅Mbar D.M V₀ V h.hyp125.isElemAbelian, Mbar D.M V₀ V h.hyp125.isElemAbelian⁆)
    (hcard : Nat.card ↥X = p ^ n) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    ∃ Xbar : Subgroup (F11.MBar11 D.M V₀ V), Xbar.Normal ∧ IsElemAbelian p Xbar ∧
      Nat.card Xbar = p ^ n ∧ Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ ∧
      barSub V₀ V h.hyp125.isElemAbelian (F11.barPreimage11 D.M V₀ V Xbar) ≤ X := by
  let hV := h.hyp125.isElemAbelian
  have hXM : X ≤ Mbar D.M V₀ V hV := hXd.trans (Subgroup.commutator_le_self _)
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv hV hMs
  set Xbar : Subgroup (F11.MBar11 D.M V₀ V) :=
    (X.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom with hXbar
  have hNnorm : (X.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hXn (q : MulAut (Vtil V₀ V hV)) q.2 (x : MulAut (Vtil V₀ V hV)) hx
  have hXnorm : Xbar.Normal := by
    rw [hXbar]
    exact hNnorm.map e.symm.toMonoidHom e.symm.surjective
  have hXab : IsElemAbelian p Xbar := by
    rw [hXbar]
    exact (hXe.subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom
  have hcardX : Nat.card ↥Xbar = p ^ n := by
    rw [hXbar, Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hcard]
  have hcomm_le : X.subgroupOf (Mbar D.M V₀ V hV) ≤
      (⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf (Mbar D.M V₀ V hV) :=
    fun x hx => hXd (Subgroup.mem_subgroupOf.1 hx)
  have hcommmap : ((⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆).subgroupOf
        (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom =
      ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [s16h_z3_subgroupOf_commutator_self, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.symm.surjective]
  have hXcomm : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), ⊤⁆ := by
    rw [hXbar]
    exact le_trans (Subgroup.map_mono hcomm_le) (le_of_eq hcommmap)
  have hXM' : F11.barPreimage11 D.M V₀ V Xbar ≤ D.M := by
    unfold F11.barPreimage11
    exact Subgroup.map_subtype_le _
  have himg : F11.barImage11 D.M V₀ V (F11.barPreimage11 D.M V₀ V Xbar) = Xbar :=
    s16h_z3_barImage11_barPreimage11 D Xbar
  have h2 : Xbar.map e.toMonoidHom = X.subgroupOf (Mbar D.M V₀ V hV) := by
    rw [hXbar, Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [hcomp, Subgroup.map_id]
  refine ⟨Xbar, hXnorm, hXab, hcardX, hXcomm, ?_⟩
  intro φ hφ
  have hφM : φ ∈ Mbar D.M V₀ V hV := (barSub_mono V₀ V hV hXM') hφ
  have h1 := he (F11.barPreimage11 D.M V₀ V Xbar) hXM'
  rw [himg, h2] at h1
  have hmem : (⟨φ, hφM⟩ : ↥(Mbar D.M V₀ V hV)) ∈
      (barSub V₀ V hV (F11.barPreimage11 D.M V₀ V Xbar)).subgroupOf
        (Mbar D.M V₀ V hV) := hφ
  rw [← h1] at hmem
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
