module

public import CFSG.Quasithin.H13.VolII16SL3
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Quasithin.Background.SmithB51SL3B

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Cover

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

theorem mk_mem_fixV_autSec {B : Subgroup (MulAut V)} {W U : Subgroup V} {w : ↥W}
    (hw : (w : V) ∈ fixSec B W U) : (QuotientGroup.mk w : Sec W U) ∈ fixV (autSec B W U) := by
  apply mk_mem_fixV_autQuot.2
  intro g hg _
  obtain ⟨b, hbB, rfl⟩ := mem_autSub.1 hg
  rw [Subgroup.mem_subgroupOf]
  exact hw.2 b hbB

theorem commV_autSec_eq_top {X Y₀ : Subgroup V} (hLX : L ≤ stabSub X) (hLY₀ : L ≤ stabSub Y₀)
    (hY₀X : Y₀ ≤ X) (hcomm : X ≤ commSub X L ⊔ Y₀) : commV (autSec L X Y₀) = ⊤ := by
  set q := QuotientGroup.mk' (Y₀.subgroupOf X) with hq
  set T := (commV (autSec L X Y₀)).comap q with hT
  have hgen : commSub X L ≤ T.map X.subtype := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    have hlw : l w ∈ X := ((hLX hl) w).2 hw
    refine ⟨⟨l w * w⁻¹, X.mul_mem hlw (X.inv_mem hw)⟩, ?_, rfl⟩
    show q _ ∈ commV (autSec L X Y₀)
    have he : q ⟨l w * w⁻¹, X.mul_mem hlw (X.inv_mem hw)⟩ =
        secHom L hLX hLY₀ ⟨l, hl⟩ (q ⟨w, hw⟩) * (q ⟨w, hw⟩)⁻¹ := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, secHom_mk,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
    rw [he]
    refine Subgroup.subset_closure ⟨_, ?_, _, rfl⟩
    rw [← range_secHom L hLX hLY₀]
    exact ⟨⟨l, hl⟩, rfl⟩
  rw [eq_top_iff]
  intro s _
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨a, ha, y, hy, hay⟩ := Subgroup.mem_sup.1 (hcomm hx)
  obtain ⟨⟨a', ha'X⟩, ha'T, rfl⟩ := hgen ha
  have hyX : y ∈ X := hY₀X hy
  have hsplit : (⟨x, hx⟩ : ↥X) = ⟨a', ha'X⟩ * ⟨y, hyX⟩ := Subtype.ext hay.symm
  have hqy : q ⟨y, hyX⟩ = 1 := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy
  show q ⟨x, hx⟩ ∈ commV (autSec L X Y₀)
  rw [hsplit, map_mul, hqy, mul_one]
  exact ha'T

variable [Finite V]

theorem eq_of_sl3_cover (hV : ∀ v : V, v ^ 2 = 1) {X Y₀ Z₀ : Subgroup V} (hY₀Z₀ : Y₀ ≤ Z₀)
    (hZ₀X : Z₀ ≤ X) (hLX : L ≤ stabSub X) (hLY₀ : L ≤ stabSub Y₀)
    (htriv : ∀ l ∈ L, ∀ z ∈ Z₀, l z * z⁻¹ ∈ Y₀) (hcomm : X ≤ commSub X L ⊔ Y₀)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2 ^ n)
    (c : NatSec L X Z₀ K) : Z₀ = Y₀ := by
  classical
  set q := QuotientGroup.mk' (Y₀.subgroupOf X) with hq
  have hY₀X : Y₀ ≤ X := hY₀Z₀.trans hZ₀X
  set Z := (Z₀.subgroupOf X).map q with hZ
  have hZfix : Z ≤ fixV (autSec L X Y₀) := by
    rintro _ ⟨z, hz, rfl⟩
    apply mk_mem_fixV_autQuot.2
    intro g hg _
    obtain ⟨l, hl, rfl⟩ := mem_autSub.1 hg
    rw [Subgroup.mem_subgroupOf]
    exact htriv l hl z (Subgroup.mem_subgroupOf.1 hz)
  have hcomm' := commV_autSec_eq_top hLX hLY₀ hY₀X hcomm
  have hker : Y₀.subgroupOf X ≤ c.f.ker := fun y hy => by
    rw [MonoidHom.mem_ker, c.hfk]
    exact hY₀Z₀ (Subgroup.mem_subgroupOf.1 hy)
  set fb : Sec X Y₀ →* Multiplicative (Fin 3 → K) := QuotientGroup.lift _ c.f hker with hfb
  have hfb_mk : ∀ x : ↥X, fb (q x) = c.f x := fun x => rfl
  have hmem : ∀ l : ↥L, secHom L hLX hLY₀ l ∈ autSec L X Y₀ := fun l => by
    rw [← range_secHom L hLX hLY₀]; exact ⟨l, rfl⟩
  set ρ : ↥L →* ↥(autSec L X Y₀) := (secHom L hLX hLY₀).codRestrict _ hmem with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [← range_secHom L hLX hLY₀] at hy
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l, rfl⟩
  set π' := ρ.comp c.π with hπ'
  have hR : (FFModel.nat (StatedSL 3 K)).RealizesVia (autSec L X Y₀) ⊤ Z π' := by
    refine FFC.realizesVia_nat_of (hρs.comp c.hπ.2) le_top (fun _ _ _ => trivial)
      (fun h z hz => by rw [hZfix hz _ h.2]; exact hz)
      (fb.comp (⊤ : Subgroup (Sec X Y₀)).subtype)
      (fun y => ?_) (fun u => ?_) (fun γ u hu => ?_)
    · obtain ⟨x, hx⟩ := c.hfs y
      exact ⟨⟨q x, trivial⟩, hx⟩
    · obtain ⟨⟨x, hxX⟩, hux⟩ := QuotientGroup.mk_surjective (u : Sec X Y₀)
      have hu' : (u : Sec X Y₀) = q ⟨x, hxX⟩ := hux.symm
      show fb (u : Sec X Y₀) = 1 ↔ (u : Sec X Y₀) ∈ Z
      rw [hu', hfb_mk, c.hfk]
      constructor
      · intro hz
        exact ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have : z * (⟨x, hxX⟩ : ↥X)⁻¹ ∈ Y₀.subgroupOf X := by
          rw [← QuotientGroup.eq_one_iff (N := Y₀.subgroupOf X), QuotientGroup.mk_mul,
            QuotientGroup.mk_inv]
          change q z * (q ⟨x, hxX⟩)⁻¹ = 1
          rw [hzx, mul_inv_cancel]
        have h1 : (z : V) * x⁻¹ ∈ Y₀ := by simpa using Subgroup.mem_subgroupOf.1 this
        have h2 := Subgroup.mem_subgroupOf.1 hz
        have : (x : V) = ((z : V) * x⁻¹)⁻¹ * z := by group
        show x ∈ Z₀
        rw [this]
        exact Z₀.mul_mem (Z₀.inv_mem (hY₀Z₀ h1)) h2
    · obtain ⟨⟨x, hxX⟩, hux⟩ := QuotientGroup.mk_surjective (u : Sec X Y₀)
      have hu' : (u : Sec X Y₀) = q ⟨x, hxX⟩ := hux.symm
      have hx' : ((c.π γ : ↥L) : MulAut V) x ∈ X := ((hLX (c.π γ).2) x).2 hxX
      show fb (((π' γ : ↥(autSec L X Y₀)) : MulAut (Sec X Y₀)) (u : Sec X Y₀)) = natAct _ γ
        (fb (u : Sec X Y₀))
      have hact : ((π' γ : ↥(autSec L X Y₀)) : MulAut (Sec X Y₀)) (q ⟨x, hxX⟩) =
          q ⟨_, hx'⟩ := by
        rw [hπ', MonoidHom.comp_apply, hρ, MonoidHom.codRestrict_apply, hq,
          QuotientGroup.mk'_apply, secHom_mk]
        rfl
      rw [hu', hact, hfb_mk, hfb_mk, c.hfe γ ⟨x, hxX⟩ hx']
  have hZbot := H13.VolI.sl3_cover hn hK (sq_eq_one_sec hV X Y₀) hZfix hcomm' ⟨π', hR⟩
  refine le_antisymm (fun z hz => ?_) hY₀Z₀
  have h1 : q ⟨z, hZ₀X hz⟩ ∈ Z := ⟨⟨z, hZ₀X hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
  rw [hZbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  exact h1

theorem card_sup_zpowers_le (hV : ∀ v : V, v ^ 2 = 1) (H : Subgroup V) (m : V) :
    Nat.card ↥(H ⊔ Subgroup.zpowers m) ≤ Nat.card H * 2 := by
  have h1 := card_sup_mul_card_inf H (Subgroup.zpowers m)
  have h2 : Nat.card ↥(Subgroup.zpowers m) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (hV m)
  have h3 : 0 < Nat.card ↥(H ⊓ Subgroup.zpowers m) := Nat.card_pos
  calc Nat.card ↥(H ⊔ Subgroup.zpowers m)
      ≤ Nat.card ↥(H ⊔ Subgroup.zpowers m) * Nat.card ↥(H ⊓ Subgroup.zpowers m) :=
        Nat.le_mul_of_pos_right _ h3
    _ = Nat.card H * Nat.card ↥(Subgroup.zpowers m) := h1
    _ ≤ Nat.card H * 2 := Nat.mul_le_mul_left _ h2

theorem eq_one_of_ne_zero_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {k : K} (hk : k ≠ 0) : k = 1 := by
  classical
  by_contra h1
  have := Fintype.ofFinite K
  have hsub : ({0, 1, k} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h1)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, Ne.symm hk⟩
  have := Finset.card_le_univ ({0, 1, k} : Finset K)
  rw [hsub, ← Nat.card_eq_fintype_card, hK] at this
  omega

theorem exists_three_gens {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ t : Fin 3 → ↥(StatedSL 3 K), Subgroup.closure (Set.range t) = ⊤ ∧
      ∀ i, ∀ v, slAct (t i) v = v + Pi.single i (v (i + 1)) := by
  classical
  let T : ∀ {i j : Fin 3}, i ≠ j → Matrix.SpecialLinearGroup (Fin 3) K :=
    fun h => Matrix.SpecialLinearGroup.transvection h 1
  set S := Subgroup.closure ({T (show (0 : Fin 3) ≠ 1 by decide),
    T (show (1 : Fin 3) ≠ 2 by decide), T (show (2 : Fin 3) ≠ 0 by decide)} :
      Set (Matrix.SpecialLinearGroup (Fin 3) K)) with hS
  have h01 : T (show (0 : Fin 3) ≠ 1 by decide) ∈ S := Subgroup.subset_closure (by simp)
  have h12 : T (show (1 : Fin 3) ≠ 2 by decide) ∈ S := Subgroup.subset_closure (by simp)
  have h20 : T (show (2 : Fin 3) ≠ 0 by decide) ∈ S := Subgroup.subset_closure (by simp)
  have hcm : ∀ {a b : Matrix.SpecialLinearGroup (Fin 3) K}, a ∈ S → b ∈ S → ⁅a, b⁆ ∈ S :=
    fun ha hb => S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have h02 : T (show (0 : Fin 3) ≠ 2 by decide) ∈ S := by
    have key := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) (1 : K) 1
    rw [one_mul] at key
    show Matrix.SpecialLinearGroup.transvection _ 1 ∈ S
    rw [← key]
    exact hcm h01 h12
  have h10 : T (show (1 : Fin 3) ≠ 0 by decide) ∈ S := by
    have key := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (1 : Fin 3) ≠ 2 by decide) (show (2 : Fin 3) ≠ 0 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (1 : K) 1
    rw [one_mul] at key
    show Matrix.SpecialLinearGroup.transvection _ 1 ∈ S
    rw [← key]
    exact hcm h12 h20
  have h21 : T (show (2 : Fin 3) ≠ 1 by decide) ∈ S := by
    have key := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (2 : Fin 3) ≠ 0 by decide) (show (0 : Fin 3) ≠ 1 by decide)
      (show (2 : Fin 3) ≠ 1 by decide) (1 : K) 1
    rw [one_mul] at key
    show Matrix.SpecialLinearGroup.transvection _ 1 ∈ S
    rw [← key]
    exact hcm h20 h01
  have hall : ∀ {i j : Fin 3} (h : i ≠ j), T h ∈ S := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | assumption
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation,
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    by_cases hc : c = 0
    · subst hc
      have : Matrix.SpecialLinearGroup.transvection hij (0 : K) = 1 := by
        apply Subtype.ext
        simp
      rw [this]
      exact S.one_mem
    · rw [eq_one_of_ne_zero_of_card_two hK hc]
      exact hall hij
  let ψ := specialLinearGroupEquivStatedSL 3 K
  let t : Fin 3 → ↥(StatedSL 3 K) := fun i => ψ (Matrix.SpecialLinearGroup.transvection
    (show i ≠ i + 1 by fin_cases i <;> decide) 1)
  refine ⟨t, ?_, fun i v => ?_⟩
  · have hrange : Set.range t = ψ.toMonoidHom '' ({T (show (0 : Fin 3) ≠ 1 by decide),
        T (show (1 : Fin 3) ≠ 2 by decide), T (show (2 : Fin 3) ≠ 0 by decide)} : Set _) := by
      ext g
      simp only [Set.mem_range, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact ⟨_, Or.inl rfl, rfl⟩
        · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
      · rintro ⟨x, hx | hx | hx, rfl⟩
        · exact ⟨0, by rw [hx]; rfl⟩
        · exact ⟨1, by rw [hx]; rfl⟩
        · exact ⟨2, by rw [hx]; rfl⟩
    have hS' : Subgroup.closure ({T (show (0 : Fin 3) ≠ 1 by decide),
        T (show (1 : Fin 3) ≠ 2 by decide), T (show (2 : Fin 3) ≠ 0 by decide)} :
          Set (Matrix.SpecialLinearGroup (Fin 3) K)) = ⊤ := hS
    rw [hrange, ← MonoidHom.map_closure, hS', ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 ψ.surjective
  · show ((((ψ _ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).mulVec v = _
    rw [specialLinearGroupEquivStatedSL_coe, Matrix.SpecialLinearGroup.transvection_coe]
    have := H.transvection_mulVec i (i + 1) (1 : K) v
    rw [one_mul] at this
    exact this

theorem eq_of_axis_two (hV : ∀ v : V, v ^ 2 = 1) {X Y₀ Z₀ : Subgroup V} (hY₀Z₀ : Y₀ ≤ Z₀)
    (hZ₀X : Z₀ ≤ X) (hLX : L ≤ stabSub X) (hcomm : X ≤ commSub X L ⊔ Y₀)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (c : NatSec L X Z₀ K)
    (hax : ∀ (i : Fin 3) (g : ↥(StatedSL 3 K)), (∀ v, slAct g v = v + Pi.single i (v (i + 1))) →
      ∀ x : ↥X, Multiplicative.toAdd (c.f x) (i + 1) = 0 →
        ((c.π g : ↥L) : MulAut V) x * (x : V)⁻¹ ∈ Y₀) :
    Z₀ = Y₀ := by
  classical
  obtain ⟨t, hgen, ht⟩ := exists_three_gens hK
  choose xs hxs using fun i : Fin 3 => c.hfs (Multiplicative.ofAdd (Pi.single (i + 1) 1))
  set m : Fin 3 → V := fun i =>
    ((c.π (t i) : ↥L) : MulAut V) (xs i : V) * ((xs i : ↥X) : V)⁻¹ with hm
  have hcm : ∀ (l : MulAut V) (x y : V), l (x * y) * (x * y)⁻¹ = (l x * x⁻¹) * (l y * y⁻¹) :=
    fun l x y => by rw [map_mul, mul_inv, mul_mul_mul_comm]
  have key : ∀ i, ∀ x : ↥X, ((c.π (t i) : ↥L) : MulAut V) x * (x : V)⁻¹ ∈
      Y₀ ⊔ Subgroup.zpowers (m i) := by
    intro i x
    by_cases ha : Multiplicative.toAdd (c.f x) (i + 1) = 0
    · exact Subgroup.mem_sup_left (hax i (t i) (ht i) x ha)
    · have ha1 := eq_one_of_ne_zero_of_card_two hK ha
      set x' : ↥X := x * (xs i)⁻¹ with hx'
      have hx'0 : Multiplicative.toAdd (c.f x') (i + 1) = 0 := by
        rw [hx', map_mul, map_inv, hxs i, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
          toAdd_ofAdd, ha1, Pi.single_eq_same, add_neg_cancel]
      have h1 := hax i (t i) (ht i) x' hx'0
      have hxx : (x : V) = (x' : V) * (xs i : V) := by
        rw [hx']; simp
      rw [hxx, hcm]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  set M := ((Y₀ ⊔ Subgroup.zpowers (m 0)) ⊔ Subgroup.zpowers (m 1)) ⊔
    Subgroup.zpowers (m 2) with hM
  have hY₀M : Y₀ ≤ M := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hkeyM : ∀ i, ∀ x : ↥X, ((c.π (t i) : ↥L) : MulAut V) x * (x : V)⁻¹ ∈ M := by
    intro i x
    have := key i x
    fin_cases i
    · exact (sup_le (hY₀M) (le_sup_right.trans (le_sup_left.trans le_sup_left))) this
    · exact (sup_le hY₀M (le_sup_right.trans le_sup_left)) this
    · exact (sup_le hY₀M le_sup_right) this
  let S' : Subgroup (MulAut V) :=
    { carrier := {l | l ∈ stabSub X ∧ ∀ x ∈ X, l x * x⁻¹ ∈ M}
      one_mem' := ⟨(stabSub X).one_mem, fun x _ => by simp [M.one_mem]⟩
      mul_mem' := by
        rintro l l' ⟨hl, hlM⟩ ⟨hl', hl'M⟩
        refine ⟨(stabSub X).mul_mem hl hl', fun x hx => ?_⟩
        have hy : l' x ∈ X := (hl' x).2 hx
        have hm' : l' x * x⁻¹ ∈ X := X.mul_mem hy (X.inv_mem hx)
        have e : (l * l') x * x⁻¹ = (l (l' x * x⁻¹) * (l' x * x⁻¹)⁻¹) * (l' x * x⁻¹) *
            (l x * x⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e]
        exact M.mul_mem (M.mul_mem (hlM _ hm') (hl'M x hx)) (hlM x hx)
      inv_mem' := by
        rintro l ⟨hl, hlM⟩
        refine ⟨(stabSub X).inv_mem hl, fun x hx => ?_⟩
        have hy : l⁻¹ x ∈ X := ((stabSub X).inv_mem hl x).2 hx
        have e : l⁻¹ x * x⁻¹ = (l (l⁻¹ x) * (l⁻¹ x)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]; group
        rw [e]
        exact M.inv_mem (hlM _ hy) }
  have hall : ∀ γ ∈ Subgroup.closure (Set.range t), ((c.π γ : ↥L) : MulAut V) ∈ S' := by
    intro γ hγt
    induction hγt using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact ⟨hLX (c.π (t i)).2, fun x hx => hkeyM i ⟨x, hx⟩⟩
    | one => rw [map_one]; exact S'.one_mem
    | mul g g' _ _ hg hg' => rw [map_mul, Subgroup.coe_mul]; exact S'.mul_mem hg hg'
    | inv g _ hg => rw [map_inv, Subgroup.coe_inv]; exact S'.inv_mem hg
  have hLS : L ≤ S' := by
    intro l hl
    obtain ⟨γ, hγ⟩ := c.hπ.2 ⟨l, hl⟩
    have := hall γ (by rw [hgen]; trivial)
    rwa [hγ] at this
  have hXM : X ≤ M := by
    intro x hx
    have h1 : commSub X L ≤ M := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, w, hw, rfl⟩
      exact (hLS hl).2 w hw
    exact (sup_le h1 hY₀M) (hcomm hx)
  have hcM : Nat.card M ≤ Nat.card Y₀ * 8 := by
    have h1 := card_sup_zpowers_le hV Y₀ (m 0)
    have h2 := card_sup_zpowers_le hV (Y₀ ⊔ Subgroup.zpowers (m 0)) (m 1)
    have h3 := card_sup_zpowers_le hV ((Y₀ ⊔ Subgroup.zpowers (m 0)) ⊔ Subgroup.zpowers (m 1))
      (m 2)
    rw [← hM] at h3
    omega
  have hcX : Nat.card X = 8 * Nat.card Z₀ := by
    have h1 := card_sec_mul hZ₀X
    have h2 := card_sec_nat hZ₀X c.f c.hfs c.hfk
    rw [h2, hK] at h1
    omega
  have hle := Subgroup.card_le_of_le hXM
  refine Subgroup.eq_of_le_of_card_ge hY₀Z₀ ?_ |>.symm
  omega

end Cover

end B5

end CFSG.Quasithin
