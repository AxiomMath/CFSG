module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Conj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_T7_inducesTransvection {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {U K : Subgroup W} (hKU : K ≤ U) (hK : E3.mQuot U K ≤ 1)
    {φ : MulAut W} (hφ : φ ∈ stabSub U) (hφK : ∀ k ∈ K, φ k = k)
    (hne : ∃ u ∈ U, φ u ≠ u) : InducesTransvection φ U := by
  classical
  refine ⟨hφ, ?_⟩
  have hW2 : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW
  have hU2 : IsPGroup 2 U := hW2.to_subgroup U
  obtain ⟨u₀, hu₀U, hu₀⟩ := hne
  have hu₀K : u₀ ∉ K := fun h => hu₀ (hφK u₀ h)
  have hKne : K ≠ U := fun h => hu₀K (h ▸ hu₀U)
  have hmq : E3.mQuot U K = 1 := by
    have h0 : E3.mQuot U K ≠ 0 := fun h => hKne ((E3.mQuot_eq_zero_iff hU2 hKU).1 h)
    omega
  have hidx : (K.subgroupOf U).index = 2 := by
    have := E3.relIndex_eq_two_pow hU2 K
    rw [hmq] at this
    simpa [Subgroup.relIndex] using this
  have hcoset : ∀ u ∈ U, u ∉ K → u * u₀⁻¹ ∈ K := by
    intro u hu huK
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u, hu⟩)
      (b := (⟨u₀, hu₀U⟩ : U)⁻¹)).2
    have h2 : ((⟨u, hu⟩ : U) * (⟨u₀, hu₀U⟩ : U)⁻¹) ∈ K.subgroupOf U := by
      apply h1
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_inv, inv_mem_iff]
      exact iff_of_false huK hu₀K
    simpa [Subgroup.mem_subgroupOf] using h2
  have hA_U : Subgroup.zpowers φ ≤ stabSub U := Subgroup.zpowers_le.2 hφ
  have hA_K : Subgroup.zpowers φ ≤ stabSub K :=
    Subgroup.zpowers_le.2 (centSub_le_stabSub K (mem_centSub.2 hφK))
  have hφq : ∀ a ∈ Subgroup.zpowers φ, ∀ u ∈ U, a u * u⁻¹ ∈ K :=
    s15_LP_mul_inv_mem_of_mQuot_le_one hW hKU hA_U hA_K hK
  set c : W := φ u₀ * u₀⁻¹ with hc
  have hc1 : c ≠ 1 := fun h => hu₀ (mul_inv_eq_one.1 h)
  have hc2 : c ^ 2 = 1 := hW c
  let B : Subgroup (MulAut W) :=
    { carrier := {a | a ∈ stabSub U ∧ ∀ u ∈ U, a u * u⁻¹ ∈ Subgroup.zpowers c}
      one_mem' := ⟨one_mem _, fun u _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hau⟩ ⟨hb, hbu⟩
        refine ⟨mul_mem ha hb, fun u hu => ?_⟩
        have hbuU : b u ∈ U := (mem_stabSub.1 hb u).2 hu
        have := mul_mem (hau (b u) hbuU) (hbu u hu)
        simpa [MulAut.mul_apply, mul_assoc] using this
      inv_mem' := by
        rintro a ⟨ha, hau⟩
        refine ⟨inv_mem ha, fun u hu => ?_⟩
        have h1 : a⁻¹ u ∈ U := (mem_stabSub.1 (inv_mem ha) u).2 hu
        have h2 := inv_mem (hau (a⁻¹ u) h1)
        have h3 : a (a⁻¹ u) = u := by simp
        rw [h3] at h2
        simpa [mul_comm] using h2 }
  have hφB : φ ∈ B := by
    refine ⟨hφ, fun u hu => ?_⟩
    by_cases huK : u ∈ K
    · rw [hφK u huK]
      simp
    · have hk : φ (u * u₀⁻¹) = u * u₀⁻¹ := hφK _ (hcoset u hu huK)
      rw [map_mul, map_inv] at hk
      have : φ u * u⁻¹ = c := by
        rw [hc]
        have h7 : (φ u * u⁻¹) * (φ u₀ * u₀⁻¹)⁻¹ = (φ u * (φ u₀)⁻¹) * (u * u₀⁻¹)⁻¹ := by
          simp [mul_comm, mul_left_comm, mul_assoc]
        rw [hk, mul_inv_cancel] at h7
        exact mul_inv_eq_one.1 h7
      rw [this]
      exact Subgroup.mem_zpowers c
  have hAB : Subgroup.zpowers φ ≤ B := Subgroup.zpowers_le.2 hφB
  have hS : commSub U (Subgroup.zpowers φ) = Subgroup.zpowers c := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, u, hu, rfl⟩
      exact (hAB ha).2 u hu
    · exact Subgroup.zpowers_le.2
        (Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, u₀, hu₀U, rfl⟩)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  rw [hS]
  unfold rk
  rw [Nat.card_zpowers, hord]
  exact padicValNat_self

theorem s15_T7_actTil_congr {V₀ V₁ V : Subgroup G} (hV : IsElemAbelian 2 V) (h01 : V₀ ≤ V₁)
    {x y : stabTil V₀ V} {x' y' : stabTil V₁ V} (hx : (x : G) = x') (hy : (y : G) = y')
    (hxy : actTil V₀ V hV x = actTil V₀ V hV y) : actTil V₁ V hV x' = actTil V₁ V hV y' := by
  have h1 : actTil V₀ V hV (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rw [actTil_eq_one_iff] at h1
  have h2 : actTil V₁ V hV (y'⁻¹ * x') = 1 := by
    rw [actTil_eq_one_iff]
    intro v hv
    have h3 := h1 v hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, hy] at h3 ⊢
    exact h01 h3
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

theorem s15_T7_barSub_le_of_barSub_le {M V₀ V₁ V X Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁) (hM : M ≤ stabTil V₀ V) (hM₁ : M ≤ stabTil V₁ V) (hX : X ≤ M) (hY : Y ≤ M)
    (h : barSub V₀ V hV X ≤ barSub V₀ V hV Y) : barSub V₁ V hV X ≤ barSub V₁ V hV Y := by
  intro φ hφ
  obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₁ V hV X φ).1 hφ
  have hx0 : (x : G) ∈ stabTil V₀ V := hM (hX hxX)
  obtain ⟨y, hyY, hxy⟩ := (mem_barSub V₀ V hV Y _).1 (h (actTil_mem_barSub V₀ V hV hxX hx0))
  have hy1 : (y : G) ∈ stabTil V₁ V := hM₁ (hY hyY)
  refine (mem_barSub V₁ V hV Y _).2 ⟨⟨y, hy1⟩, hyY, ?_⟩
  exact (s15_T7_actTil_congr hV h01 (x := ⟨x, hx0⟩) (y := y) (x' := x) (y' := ⟨y, hy1⟩) rfl rfl
    hxy.symm).symm

theorem s15_T7_actTil_mkTil_eq_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : stabTil V₀ V) (z : IntMod V hV) :
    actTil V₀ V hV g (mkTil V₀ V hV z) = mkTil V₀ V hV z ↔
      (g : G) * z.val * (g : G)⁻¹ * (z.val)⁻¹ ∈ V₀ := by
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]

theorem s15_T7_actTil_mem_centSub_iff (V₀ V U : Subgroup G) (hV : IsElemAbelian 2 V)
    (hU : U ≤ V) (g : stabTil V₀ V) :
    actTil V₀ V hV g ∈ centSub (imgTil V₀ V hV U) ↔
      ∀ d ∈ U, (g : G) * d * (g : G)⁻¹ * d⁻¹ ∈ V₀ := by
  rw [mem_centSub]
  constructor
  · intro h d hd
    have h1 := h (mkTil V₀ V hV (IntMod.mk hV ⟨d, hU hd⟩))
      ((mem_imgTil V₀ V hV U _).2 ⟨IntMod.mk hV ⟨d, hU hd⟩, hd, rfl⟩)
    exact (s15_T7_actTil_mkTil_eq_iff V₀ V hV g _).1 h1
  · intro h q hq
    obtain ⟨z, hz, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
    exact (s15_T7_actTil_mkTil_eq_iff V₀ V hV g z).2 (h z.val hz)

theorem s15_T7_wSub_sup_v1Sub_le {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L ≤ V :=
  sup_le (preTil_le V₀ V h.isElemAbelian _) (s15_Infra_v1Sub_le h.hyp125 h.isElemAbelian)

theorem s15_T7_imgTil_wSub_sup_v1Sub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
      (wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L) =
      wStar D.M V₀ V h.isElemAbelian L :=
  s15_Infra_imgTil_sup_left h.isElemAbelian (preTil_le V₀ V h.isElemAbelian _)
    (s15_Infra_v1Sub_le h.hyp125 h.isElemAbelian)

theorem s15_T7_le_stabTil_v1Sub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    D.M ≤ stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 _)

theorem s15_T7_barSub_le_stabSub_wStar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {F : Subgroup G} (hFM : F ≤ D.M)
    (hFN : F ≤ normalizer ((wSub V₀ V h.isElemAbelian L ⊔
      v1Sub D.M V₀ V h.isElemAbelian L : Subgroup G) : Set G)) :
    barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian F ≤
      stabSub (wStar D.M V₀ V h.isElemAbelian L) := by
  have := s15_LP_barSub_le_stabSub_imgTil (V₀ := v1Sub D.M V₀ V h.isElemAbelian L) (V := V)
    h.isElemAbelian (hFM.trans (s15_T7_le_stabTil_v1Sub h)) hFN
  rwa [s15_T7_imgTil_wSub_sup_v1Sub h] at this

theorem s15_T7_rk_autSub_eq (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {F C : Subgroup G} (hFM : F ≤ D.M) (hCF : C ≤ F)
    (hFN : F ≤ normalizer ((wSub V₀ V h.isElemAbelian L ⊔
      v1Sub D.M V₀ V h.isElemAbelian L : Subgroup G) : Set G))
    (hC : ∀ x ∈ F, x ∈ C ↔ ∀ d ∈ wSub V₀ V h.isElemAbelian L ⊔
      v1Sub D.M V₀ V h.isElemAbelian L, x * d * x⁻¹ * d⁻¹ ∈ v1Sub D.M V₀ V h.isElemAbelian L) :
    rk ↥(autSub (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian F)
      (wStar D.M V₀ V h.isElemAbelian L)) = E3.mQuot F C := by
  have hV := h.isElemAbelian
  have hFs : F ≤ stabTil (v1Sub D.M V₀ V hV L) V := hFM.trans (s15_T7_le_stabTil_v1Sub h)
  have hE := s15_T7_wSub_sup_v1Sub_le h
  have himg := s15_T7_imgTil_wSub_sup_v1Sub h
  have hcent : ∀ g : stabTil (v1Sub D.M V₀ V hV L) V,
      actTil (v1Sub D.M V₀ V hV L) V hV g ∈ centSub (wStar D.M V₀ V hV L) ↔
        ∀ d ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L,
          (g : G) * d * (g : G)⁻¹ * d⁻¹ ∈ v1Sub D.M V₀ V hV L := fun g => by
    rw [← himg]
    exact s15_T7_actTil_mem_centSub_iff _ V _ hV hE g
  rw [s15_LP_rk_autSub_eq_mQuot (s15_T7_barSub_le_stabSub_wStar D h hFM hFN),
    s15_LP_mQuot_barSub_preBarSub hV hFs
      (inf_le_left : _ ≤ barSub (v1Sub D.M V₀ V hV L) V hV F)]
  congr 1
  ext x
  rw [mem_preBarSub]
  constructor
  · rintro ⟨hxF, hxs, hxq⟩
    exact (hC x hxF).2 ((hcent ⟨x, hxs⟩).1 (Subgroup.mem_inf.1 hxq).2)
  · intro hxC
    have hxF := hCF hxC
    exact ⟨hxF, hFs hxF, Subgroup.mem_inf.2
      ⟨actTil_mem_barSub _ V hV hxF (hFs hxF), (hcent ⟨x, hFs hxF⟩).2 ((hC x hxF).1 hxC)⟩⟩

theorem s15_T7_imgTil_le_wStar {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {K : Subgroup G}
    (hKE : K ≤ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L) :
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K ≤
      wStar D.M V₀ V h.isElemAbelian L := by
  rw [← s15_T7_imgTil_wSub_sup_v1Sub h]
  exact s15_LP_imgTil_mono h.isElemAbelian hKE

theorem s15_T7_mQuot_imgTil_axis {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {K : Subgroup G}
    (hKE : K ≤ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L)
    (hK : E3.mQuot (wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L) K ≤ 1) :
    E3.mQuot (wStar D.M V₀ V h.isElemAbelian L)
      (imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K) ≤ 1 := by
  rw [← s15_T7_imgTil_wSub_sup_v1Sub h]
  exact (s15_LP_mQuot_imgTil_le h.isElemAbelian hKE (s15_T7_wSub_sup_v1Sub_le h)).trans hK

theorem s15_T7_barSub_fixes_axis {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {F K : Subgroup G} (hFM : F ≤ D.M)
    (hKE : K ≤ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L)
    (hFK : ∀ x ∈ F, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ v1Sub D.M V₀ V h.isElemAbelian L) :
    ∀ φ ∈ barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian F,
      ∀ k ∈ imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K, φ k = k := by
  intro φ hφ k hk
  obtain ⟨g, hgF, rfl⟩ := (mem_barSub _ V h.isElemAbelian F φ).1 hφ
  exact mem_centSub.1 ((s15_T7_actTil_mem_centSub_iff _ V K h.isElemAbelian
    (hKE.trans (s15_T7_wSub_sup_v1Sub_le h)) g).2 fun d hd => hFK g hgF d hd) k hk

theorem s15_T7_barSub_le_normalizer_lStar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {F : Subgroup G} (hFN : F ≤ nBar D.M V₀ V h.isElemAbelian L) :
    barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian F ≤
      normalizer ((lStar D.M V₀ V h.isElemAbelian L : Subgroup _) : Set _) := by
  have hV := h.isElemAbelian
  have hMs₁ := s15_T7_le_stabTil_v1Sub h
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  intro φ hφ
  obtain ⟨g, hgF, rfl⟩ := (mem_barSub _ V hV F φ).1 hφ
  have hgM : (g : G) ∈ D.M := (mem_preBarSub D.M V₀ V hV _).1 (hFN hgF) |>.1
  have hconj := (s15_Infra_mem_nBar_iff h.hyp125 hV hgM).1 (hFN hgF)
  have hLM : conjSubgroup L (g : G) ≤ D.M := by
    have := E3.conjSubgroup_mono_left (g : G) h.le
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hgM)] at this
  have hbar : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup L (g : G)) =
      barSub (v1Sub D.M V₀ V hV L) V hV L :=
    le_antisymm (s15_T7_barSub_le_of_barSub_le hV (s15_Infra_le_v1Sub _ V₀ V hV L) hMs₀ hMs₁
      hLM h.le hconj.le) (s15_T7_barSub_le_of_barSub_le hV (s15_Infra_le_v1Sub _ V₀ V hV L)
      hMs₀ hMs₁ h.le hLM hconj.ge)
  rw [s15_Infra_barSub_conjSubgroup _ V hV g.2 L] at hbar
  exact inv_mem_iff.1 (Subgroup.mem_normalizer_iff_map_conj_eq.2 hbar)

theorem s15_T7_autSub_le_normalizer {V : Type} [CommGroup V] {E A : Subgroup (MulAut V)}
    {U : Subgroup V} (hAN : A ≤ normalizer (E : Set (MulAut V))) :
    autSub A U ≤ normalizer ((autSub E U : Subgroup (MulAut U)) : Set (MulAut U)) := by
  have key : ∀ x ∈ autSub A U, ∀ y ∈ autSub E U, x * y * x⁻¹ ∈ autSub E U := by
    intro x hx y hy
    obtain ⟨g, hgA, rfl⟩ := mem_autSub.1 hx
    obtain ⟨e, heE, rfl⟩ := mem_autSub.1 hy
    refine mem_autSub.2 ⟨g * e * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hAN hgA) e).1 heE
    · rw [map_mul, map_mul, map_inv]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

@[expose] def s15T7Group (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (Q : Subgroup (MulAut (vStar D.M V₀ V hV L))) : Prop :=
  Q ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV ∧ Q ≤ stabSub (wStar D.M V₀ V hV L) ∧
    Q ≤ normalizer ((lStar D.M V₀ V hV L : Subgroup _) : Set _) ∧
    2 ≤ rk ↥(autSub Q (wStar D.M V₀ V hV L)) ∧
    ∃ A : Subgroup (vStar D.M V₀ V hV L), A ≤ wStar D.M V₀ V hV L ∧
      E3.mQuot (wStar D.M V₀ V hV L) A ≤ 1 ∧ ∀ φ ∈ Q, ∀ k ∈ A, φ k = k

theorem s15_T7_exists_group (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {F C K : Subgroup G}
    (hcfg : s15T7Config D.M (wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L)
      (v1Sub D.M V₀ V h.isElemAbelian L) F C K) :
    s15T7Group D V₀ V L h.isElemAbelian
      (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian F) := by
  obtain ⟨-, hFM, hCF, hFN, hC, -, hKE, hmK, hFK, hmFC⟩ := hcfg
  have hFnBar : F ≤ nBar D.M V₀ V h.isElemAbelian L := by
    rw [← inf_normalizer_wSub_sup_v1Sub_eq_nBar D h h.isElemAbelian]
    exact le_inf hFM hFN
  refine ⟨?_, s15_T7_barSub_le_stabSub_wStar D h hFM hFN,
    s15_T7_barSub_le_normalizer_lStar D h hFnBar, ?_,
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K,
    s15_T7_imgTil_le_wStar h hKE, s15_T7_mQuot_imgTil_axis h hKE hmK.le,
    s15_T7_barSub_fixes_axis h hFM hKE hFK⟩
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub _ V h.isElemAbelian F φ).1 hφ
    exact (mem_barSub _ V h.isElemAbelian D.M _).2 ⟨g, hFM hg, rfl⟩
  · rw [s15_T7_rk_autSub_eq D h hFM hCF hFN hC]
    exact hmFC

theorem s15_T7_exists_transvection (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {Q : Subgroup (MulAut (vStar D.M V₀ V h.isElemAbelian L))}
    (hQ : s15T7Group D V₀ V L h.isElemAbelian Q) :
    ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L) := by
  obtain ⟨hQM, hQs, -, hrk, A, hAW, hAm, hfix⟩ := hQ
  have hne : autSub Q (wStar D.M V₀ V h.isElemAbelian L) ≠ ⊥ := fun hb => by
    rw [hb] at hrk
    simp [rk] at hrk
  obtain ⟨ψ, hψ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨g, hgQ, hg⟩ := mem_autSub.1 ψ.2
  have hmove : ∃ u ∈ wStar D.M V₀ V h.isElemAbelian L, (g : MulAut _) u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hψ1
    apply Subtype.ext
    rw [← hg]
    ext u
    exact hcon u.1 u.2
  exact ⟨g, hQM hgQ, s15_T7_inducesTransvection (s15_LP_vtil_sq_eq_one _ V h.isElemAbelian) hAW
    hAm g.2 (hfix g hgQ) hmove⟩

@[expose] noncomputable def s15T7Kappa (V₀ V₁ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁) : Vtil V₀ V hV →* Vtil V₁ V hV :=
  QuotientGroup.map (modNull V₀ V hV) (modNull V₁ V hV) (MonoidHom.id _) (fun x hx => h01 hx)

theorem s15_T7_kappa_mk (V₀ V₁ V : Subgroup G) (hV : IsElemAbelian 2 V) (h01 : V₀ ≤ V₁)
    (x : IntMod V hV) : s15T7Kappa V₀ V₁ V hV h01 (mkTil V₀ V hV x) = mkTil V₁ V hV x := rfl

theorem s15_T7_kappa_surjective (V₀ V₁ V : Subgroup G) (hV : IsElemAbelian 2 V) (h01 : V₀ ≤ V₁) :
    Function.Surjective (s15T7Kappa V₀ V₁ V hV h01) := by
  intro q
  obtain ⟨x, rfl⟩ := mkTil_surjective V₁ V hV q
  exact ⟨mkTil V₀ V hV x, rfl⟩

theorem s15_T7_kappa_act (V₀ V₁ V : Subgroup G) (hV : IsElemAbelian 2 V) (h01 : V₀ ≤ V₁)
    {g : G} (hg₀ : g ∈ stabTil V₀ V) (hg₁ : g ∈ stabTil V₁ V) (q : Vtil V₀ V hV) :
    s15T7Kappa V₀ V₁ V hV h01 (actTil V₀ V hV ⟨g, hg₀⟩ q) =
      actTil V₁ V hV ⟨g, hg₁⟩ (s15T7Kappa V₀ V₁ V hV h01 q) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
  rw [actTil_mk, s15_T7_kappa_mk, s15_T7_kappa_mk, actTil_mk]
  congr 1

theorem s15_T7_imgTil_preTil_eq_map (V₀ V₁ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁) (S : Subgroup (Vtil V₀ V hV)) :
    imgTil V₁ V hV (preTil V₀ V hV S) = S.map (s15T7Kappa V₀ V₁ V hV h01) := by
  ext q
  rw [mem_imgTil, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hx
    have : y = x := IntMod.val_injective hy
    subst this
    exact ⟨mkTil V₀ V hV y, hyS, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV z
    exact ⟨x, (mem_preTil V₀ V hV S).2 ⟨x, rfl, hz⟩, rfl⟩

theorem s15_T7_kappa_map_commSub {M V₀ V₁ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁) (hM₀ : M ≤ stabTil V₀ V) (hM₁ : M ≤ stabTil V₁ V) (hL : L ≤ M) :
    (commSub ⊤ (barSub V₀ V hV L)).map (s15T7Kappa V₀ V₁ V hV h01) =
      commSub ⊤ (barSub V₁ V hV L) := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨φ, hφ, w, -, rfl⟩, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₀ V hV L φ).1 hφ
    have hg1 : (g : G) ∈ stabTil V₁ V := hM₁ (hL hgL)
    refine ⟨actTil V₁ V hV ⟨g, hg1⟩,
      (mem_barSub V₁ V hV L _).2 ⟨⟨g, hg1⟩, hgL, rfl⟩, s15T7Kappa V₀ V₁ V hV h01 w,
      Subgroup.mem_top _, ?_⟩
    rw [map_mul, map_inv, s15_T7_kappa_act V₀ V₁ V hV h01 g.2 hg1]
  · rintro ⟨ψ, hψ, w', -, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub V₁ V hV L ψ).1 hψ
    obtain ⟨w, rfl⟩ := s15_T7_kappa_surjective V₀ V₁ V hV h01 w'
    have hg0 : (g : G) ∈ stabTil V₀ V := hM₀ (hL hgL)
    refine ⟨_, ⟨actTil V₀ V hV ⟨g, hg0⟩, (mem_barSub V₀ V hV L _).2 ⟨⟨g, hg0⟩, hgL, rfl⟩, w,
      Subgroup.mem_top _, rfl⟩, ?_⟩
    rw [map_mul, map_inv, s15_T7_kappa_act V₀ V₁ V hV h01 hg0 g.2]

theorem s15_T7_wStar_eq_commSub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    wStar D.M V₀ V h.isElemAbelian L = commSub ⊤ (lStar D.M V₀ V h.isElemAbelian L) := by
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  unfold wStar wSub wTil lStar
  rw [s15_T7_imgTil_preTil_eq_map V₀ _ V h.isElemAbelian (s15_Infra_le_v1Sub _ V₀ V _ L),
    s15_T7_kappa_map_commSub h.isElemAbelian (s15_Infra_le_v1Sub _ V₀ V _ L) hMs₀
      (s15_T7_le_stabTil_v1Sub h) h.le]

theorem s15_T7_isElemAbelian_barSub (p : ℕ) {M V₀ V₁ V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁) (hM : M ≤ stabTil V₀ V) (hM₁ : M ≤ stabTil V₁ V) (hX : X ≤ M)
    (h : IsElemAbelian p (barSub V₀ V hV X)) : IsElemAbelian p (barSub V₁ V hV X) := by
  have hc := h.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun φ hφ => ?_⟩
  · obtain ⟨x, hxX, hxa⟩ := (mem_barSub V₁ V hV X a.1).1 a.2
    obtain ⟨y, hyX, hyb⟩ := (mem_barSub V₁ V hV X b.1).1 b.2
    have hx0 : (x : G) ∈ stabTil V₀ V := hM (hX hxX)
    have hy0 : (y : G) ∈ stabTil V₀ V := hM (hX hyX)
    have h1 := congrArg Subtype.val (mul_comm' (⟨actTil V₀ V hV ⟨x, hx0⟩,
      actTil_mem_barSub V₀ V hV hxX hx0⟩ : barSub V₀ V hV X)
      ⟨actTil V₀ V hV ⟨y, hy0⟩, actTil_mem_barSub V₀ V hV hyX hy0⟩)
    simp only [Subgroup.coe_mul, ← map_mul] at h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    exact s15_T7_actTil_congr hV h01 (x := ⟨x, hx0⟩ * ⟨y, hy0⟩) (y := ⟨y, hy0⟩ * ⟨x, hx0⟩)
      (x' := x * y) (y' := y * x) rfl rfl h1
  · obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₁ V hV X φ).1 hφ
    have hx0 : (x : G) ∈ stabTil V₀ V := hM (hX hxX)
    have h1 := h.2 _ (actTil_mem_barSub V₀ V hV hxX hx0)
    rw [← map_pow, ← map_one (actTil V₀ V hV)] at h1
    rw [← map_pow, ← map_one (actTil V₁ V hV)]
    exact s15_T7_actTil_congr hV h01 (x := ⟨x, hx0⟩ ^ p) (y := 1) (x' := x ^ p) (y' := 1) rfl rfl h1

theorem s15_T7_barSub_eq_of_barSub_eq {M V₀ V₁ V X Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (h01 : V₀ ≤ V₁) (hM : M ≤ stabTil V₀ V) (hM₁ : M ≤ stabTil V₁ V) (hX : X ≤ M) (hY : Y ≤ M)
    (h : barSub V₀ V hV X = barSub V₀ V hV Y) : barSub V₁ V hV X = barSub V₁ V hV Y :=
  le_antisymm (s15_T7_barSub_le_of_barSub_le hV h01 hM hM₁ hX hY h.le)
    (s15_T7_barSub_le_of_barSub_le hV h01 hM hM₁ hY hX h.ge)

theorem s15_T7_isElemAbelian_autSub {V : Type} [CommGroup V] (p : ℕ) {X : Subgroup (MulAut V)}
    (U : Subgroup V) (h : IsElemAbelian p X) : IsElemAbelian p (autSub X U) :=
  (h.subgroupOf (stabSub U)).map (resHom U)

theorem s15_T7_lStar_le_stabSub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    lStar D.M V₀ V h.isElemAbelian L ≤ stabSub (wStar D.M V₀ V h.isElemAbelian L) := by
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hLn : L ≤ nBar D.M V₀ V h.isElemAbelian L := fun g hg => by
    rw [nBar, mem_preBarSub]
    exact ⟨h.le hg, hMs₀ (h.le hg), Subgroup.le_normalizer (actTil_mem_barSub V₀ V _ hg _)⟩
  rw [← inf_normalizer_wSub_sup_v1Sub_eq_nBar D h h.isElemAbelian] at hLn
  exact s15_T7_barSub_le_stabSub_wStar D h h.le fun g hg => (hLn hg).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
