module

public import CFSG.LocalAnalysis.StandardType.FS81.RootD6EltDefs
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.LocalAnalysis.StandardType.FS81.D6InnerAux
public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

private def d6Good (e : Coords 7) : Prop :=
  (wt e = 1 ∧ e 0 ≠ 0) ∨ (wt e = 2 ∧ e 0 = 0) ∨
    (wt e = 7 ∧ ∏ i : Fin 6, e i.succ = 1)

private instance d6DecidableGood (e : Coords 7) : Decidable (d6Good e) := by
  unfold d6Good
  infer_instance

private def d6GoodSet : Finset (Coords 7) := Finset.univ.filter d6Good

private noncomputable def d6LineSet {G : Type} [Group G] (B : Basis3 G 7) :
    Finset (Subgroup G) := by
  classical
  exact d6GoodSet.image B.line

private lemma ne_zero_of_d6Good {e : Coords 7} (h : d6Good e) : e ≠ 0 := by
  rintro rfl
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [wt] at h1

private lemma neg_of_d6Good {e : Coords 7} (h : d6Good e) : d6Good (-e) := by
  rcases h with ⟨h1, h0⟩ | ⟨h1, h0⟩ | ⟨h1, hprod⟩
  · exact Or.inl ⟨by rw [wt_neg, h1], by simpa using h0⟩
  · exact Or.inr (Or.inl ⟨by rw [wt_neg, h1], by simpa using h0⟩)
  · refine Or.inr (Or.inr ⟨by rw [wt_neg, h1], ?_⟩)
    rw [show (∏ i : Fin 6, (-e) i.succ) = ∏ i : Fin 6, -(e i.succ) from rfl,
      Finset.prod_neg, Finset.card_univ, Fintype.card_fin,
      show (-1 : ZMod 3) ^ 6 = 1 by decide, one_mul]
    exact hprod

private lemma card_d6GoodSet : d6GoodSet.card = 126 := by
  rw [d6GoodSet]
  decide +kernel

private noncomputable def d6Fiber {G : Type} [Group G] (B : Basis3 G 7)
    (L : Subgroup G) : Finset (Coords 7) := by
  classical
  exact d6GoodSet.filter fun e => B.line e = L

private lemma card_d6Fiber {G : Type} [Group G] {B : Basis3 G 7} {L : Subgroup G}
    (hL : L ∈ d6LineSet B) : (d6Fiber B L).card = 2 := by
  classical
  rw [d6Fiber]
  obtain ⟨e, he, hLe⟩ := Finset.mem_image.mp hL
  have hgood : d6Good e := by
    simpa [d6GoodSet] using he
  have he0 : e ≠ 0 := ne_zero_of_d6Good hgood
  have hne : e ≠ -e := by
    intro h
    apply he0
    funext i
    exact (by decide : ∀ x : ZMod 3, x = -x → x = 0) (e i) (congrFun h i)
  have hsub : d6GoodSet.filter (fun e' => B.line e' = B.line e) = {e, -e} := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he', hline⟩
      have he'good : d6Good e' := by
        simpa [d6GoodSet] using he'
      have he'0 : e' ≠ 0 := ne_zero_of_d6Good he'good
      have hmem : B.vec e' ∈ Subgroup.zpowers (B.vec e) := by
        have h : B.vec e' ∈ B.line e' := Subgroup.mem_zpowers _
        rw [hline, Basis3.line] at h
        exact h
      rcases B.eq_or_eq_neg_of_vec_mem_zpowers he'0 hmem with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨he, rfl⟩
      · exact ⟨by simpa [d6GoodSet] using neg_of_d6Good (e := e) hgood,
          by rw [Basis3.line, Basis3.line, B.vec_neg_eq_inv, Subgroup.zpowers_inv]⟩
  rw [show (d6GoodSet.filter fun e' => B.line e' = L) =
      d6GoodSet.filter (fun e' => B.line e' = B.line e) by rw [← hLe]]
  rw [hsub, Finset.card_pair hne]

private lemma card_d6LineSet {G : Type} [Group G] (B : Basis3 G 7) :
    (d6LineSet B).card = 63 := by
  classical
  have hsum := Finset.card_eq_sum_card_fiberwise (s := d6GoodSet) (t := d6LineSet B)
    (f := fun e => B.line e) (by
      intro e he
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hsum2 : d6GoodSet.card = ∑ L ∈ d6LineSet B, 2 :=
    hsum.trans (Finset.sum_congr rfl fun L hL => by
      simpa [d6Fiber] using card_d6Fiber hL)
  rw [Finset.sum_const, card_d6GoodSet] at hsum2
  have h : (d6LineSet B).card * 2 = 126 := by
    simpa [smul_eq_mul, mul_comm] using hsum2.symm
  omega

private lemma map_conj_mem_d6LineSet {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G 7} (hrec : RecOutD6 B b₀) {q : G}
    (hq : q ∈ Subgroup.normalizer (B.span : Set G)) {L : Subgroup G}
    (hL : L ∈ d6LineSet B) :
    L.map (MulAut.conj q).toMonoidHom ∈ d6LineSet B := by
  classical
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hL
  have hgood : d6Good e := by
    simpa [d6GoodSet] using he
  have he0 : e ≠ 0 := ne_zero_of_d6Good hgood
  have hqmem : q * B.vec e * q⁻¹ ∈ B.span :=
    (Subgroup.mem_normalizer_iff.mp hq (B.vec e)).mp (B.vec_mem_span e)
  obtain ⟨e', he'⟩ := B.exists_vec_eq hqmem
  have hline : (B.line e).map (MulAut.conj q).toMonoidHom = B.line e' := by
    rw [Basis3.line, Basis3.line, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, ← he']
  have hconj : IsConjLine b₀ (B.line e') := by
    rw [← hline]
    exact isConjLine_map_conj ((hrec.2 e he0).mpr hgood) q
  have he'0 : e' ≠ 0 := by
    intro h0
    have hconj1 : (MulAut.conj q) (B.vec e) = (MulAut.conj q) 1 := by
      rw [MulAut.conj_apply, map_one, ← he', h0, B.vec_zero]
    have hvec : B.vec e = 1 := (MulAut.conj q).injective hconj1
    exact he0 (B.vec_injective (by rw [hvec, B.vec_zero]))
  have hgood' : d6Good e' := (hrec.2 e' he'0).mp hconj
  exact Finset.mem_image.mpr ⟨e', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood'⟩,
    hline.symm⟩

@[instance_reducible]
private noncomputable def d6LineSetConjAction {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G 7} (hrec : RecOutD6 B b₀) (P : Subgroup G)
    (hPnorm : P ≤ Subgroup.normalizer (B.span : Set G)) :
    MulAction P ↥(d6LineSet B) := by
  classical
  letI : MulAction (ConjAct G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction P (Subgroup G) :=
    MulAction.compHom (Subgroup G) (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  refine
    { smul := fun q L => ⟨q • (L : Subgroup G), ?_⟩
      one_smul := fun L => Subtype.ext (one_smul P (L : Subgroup G))
      mul_smul := fun q r L => Subtype.ext (mul_smul q r (L : Subgroup G)) }
  change (ConjAct.toConjAct ((q : P) : G) • (L : Subgroup G)) ∈ d6LineSet B
  rw [show ConjAct.toConjAct ((q : P) : G) • (L : Subgroup G) =
      (L : Subgroup G).map (MulAut.conj (((q : P) : G))).toMonoidHom by
    rw [Subgroup.pointwise_smul_def]
    rfl]
  exact map_conj_mem_d6LineSet hrec (hPnorm q.2) L.2

private lemma exists_mem_d6LineSet_fixed {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G 7} (hrec : RecOutD6 B b₀) (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPnorm : P ≤ Subgroup.normalizer (B.span : Set G)) :
    ∃ L ∈ d6LineSet B, ∀ q ∈ P, L.map (MulAut.conj q).toMonoidHom = L := by
  classical
  letI : MulAction P ↥(d6LineSet B) := d6LineSetConjAction hrec P hPnorm
  letI : MulAction (ConjAct G) (Subgroup G) := Subgroup.pointwiseMulAction
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ Nat.card ↥(d6LineSet B) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_d6LineSet B]
    decide
  obtain ⟨L, hL⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card ↥(d6LineSet B) hnot
  refine ⟨L.1, L.2, fun q hq => ?_⟩
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hL ⟨q, hq⟩)
  change ConjAct.toConjAct q • (L : Subgroup G) = L at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.conjAct_pointwise_smul_iff.mp h)

private lemma mem_normalizer_zpowers_of_map_conj {G : Type} [Group G] {Y E : Subgroup G}
    (hEY : E ≤ Y) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {x : G} (hxE : x ∈ E)
    {a q : ↥(adjointGroup .E7 (ZMod 2))} (hψa : ψ a = ⟨x, hEY hxE⟩)
    (hqline : (Subgroup.zpowers x).map
      (MulAut.conj (((ψ q : ↥Y) : G))).toMonoidHom = Subgroup.zpowers x) :
    q ∈ Subgroup.normalizer
      (Subgroup.zpowers a : Set ↥(adjointGroup .E7 (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hinj : Function.Injective (Y.subtype.comp ψ.toMonoidHom) :=
    Y.subtype_injective.comp ψ.injective
  have himg2 : (Subgroup.zpowers a).map (Y.subtype.comp ψ.toMonoidHom) =
      Subgroup.zpowers x := by
    simp [hψa]
  have hqa : (Y.subtype.comp ψ.toMonoidHom) (q * a * q⁻¹) =
      ((ψ q : ↥Y) : G) * x * (((ψ q : ↥Y) : G))⁻¹ := by
    simp [hψa]
  have himg1 : ((Subgroup.zpowers a).map (MulAut.conj q).toMonoidHom).map
        (Y.subtype.comp ψ.toMonoidHom) = Subgroup.zpowers x := by
    calc
      ((Subgroup.zpowers a).map (MulAut.conj q).toMonoidHom).map
          (Y.subtype.comp ψ.toMonoidHom)
          = Subgroup.zpowers ((Y.subtype.comp ψ.toMonoidHom) ((MulAut.conj q) a)) := by
            rw [Subgroup.map_map, MonoidHom.map_zpowers]
            rfl
      _ = Subgroup.zpowers ((Y.subtype.comp ψ.toMonoidHom) (q * a * q⁻¹)) := by
            rw [MulAut.conj_apply]
      _ = Subgroup.zpowers (((ψ q : ↥Y) : G) * x * (((ψ q : ↥Y) : G))⁻¹) := by
            rw [hqa]
      _ = (Subgroup.zpowers x).map (MulAut.conj (((ψ q : ↥Y) : G))).toMonoidHom := by
            rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      _ = Subgroup.zpowers x := hqline
  exact Subgroup.map_injective hinj (himg1.trans himg2.symm)

private lemma le_normalizer_zpowers_of_fixed {G : Type} [Group G] {Y E : Subgroup G}
    (hEY : E ≤ Y) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {x : G} (hxE : x ∈ E)
    {a : ↥(adjointGroup .E7 (ZMod 2))} (hψa : ψ a = ⟨x, hEY hxE⟩)
    {L : Subgroup G} (hLx : L = Subgroup.zpowers x)
    {Q : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    (hLfix : ∀ q : ↥(adjointGroup .E7 (ZMod 2)), q ∈ Q →
      L.map (MulAut.conj (((ψ q : ↥Y) : G))).toMonoidHom = L) :
    Q ≤ Subgroup.normalizer
      (Subgroup.zpowers a : Set ↥(adjointGroup .E7 (ZMod 2))) := by
  intro q hq
  have hqline : (Subgroup.zpowers x).map
      (MulAut.conj (((ψ q : ↥Y) : G))).toMonoidHom = Subgroup.zpowers x := by
    rw [← hLx]
    exact hLfix q hq
  exact mem_normalizer_zpowers_of_map_conj hEY ψ hxE hψa hqline

private lemma zpow_mem_highRootSL2
    {a g : ↥(adjointGroup .E7 (ZMod 2))}
    (hgH : ((g * a * g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
      CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2))
    (j : ℤ) :
    (((g * a * g⁻¹) ^ j : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
      CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) := by
  have h := Subgroup.zpow_mem
    (K := CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2)) hgH j
  simpa [Subgroup.coe_zpow] using h

private lemma conj_zpow_eq_of_mem_zpowers {G : Type} [Group G] {Y : Subgroup G} {b₀ : G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {x : G} (hxY : x ∈ Y)
    {a g : ↥(adjointGroup .E7 (ZMod 2))} (hψa : ψ a = ⟨x, hxY⟩)
    {g₁ : G} {j : ℤ} (hj : x ^ j = g₁ * b₀ * g₁⁻¹) :
    ((ψ ((g * a * g⁻¹) ^ j) : ↥Y) : G) =
      (((ψ g : ↥Y) : G) * g₁) * b₀ * (((ψ g : ↥Y) : G) * g₁)⁻¹ := by
  have hψa' : ((ψ (g * a * g⁻¹) : ↥Y) : G) =
      ((ψ g : ↥Y) : G) * x * (((ψ g : ↥Y) : G))⁻¹ := by
    simp [hψa]
  have hψr : ((ψ ((g * a * g⁻¹) ^ j) : ↥Y) : G) =
      ((ψ (g * a * g⁻¹) : ↥Y) : G) ^ j := by
    simp
  rw [hψr, hψa']
  calc
    (((ψ g : ↥Y) : G) * x * (((ψ g : ↥Y) : G))⁻¹) ^ j
        = (MulAut.conj (((ψ g : ↥Y) : G))) (x ^ j) := by
          rw [map_zpow, MulAut.conj_apply]
    _ = (MulAut.conj (((ψ g : ↥Y) : G))) (g₁ * b₀ * g₁⁻¹) := by rw [hj]
    _ = (((ψ g : ↥Y) : G) * g₁) * b₀ * (((ψ g : ↥Y) : G) * g₁)⁻¹ := by
          rw [MulAut.conj_apply]
          group

private lemma exists_rootElt_of_zpowers
    {G : Type} [Group G] {Y : Subgroup G} {b₀ : G}
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {x : G} (hxY : x ∈ Y)
    {a g : ↥(adjointGroup .E7 (ZMod 2))} (hψa : ψ a = ⟨x, hxY⟩)
    (hgH : ((g * a * g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
      CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2))
    {g₁ : G} (hg₁ : Subgroup.zpowers (g₁ * b₀ * g₁⁻¹) = Subgroup.zpowers x) :
    ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈
        CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
      ((ψ r : ↥Y) : G) =
        (((ψ g : ↥Y) : G) * g₁) * b₀ * (((ψ g : ↥Y) : G) * g₁)⁻¹ := by
  have hmemx : g₁ * b₀ * g₁⁻¹ ∈ Subgroup.zpowers x := by
    have h : g₁ * b₀ * g₁⁻¹ ∈ Subgroup.zpowers (g₁ * b₀ * g₁⁻¹) := Subgroup.mem_zpowers _
    rwa [hg₁] at h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmemx
  exact ⟨(g * a * g⁻¹) ^ j, zpow_mem_highRootSL2 hgH j,
    conj_zpow_eq_of_mem_zpowers ψ hxY hψa hj⟩

private theorem exists_rootElt_of_conj_mem
    {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G 7} {Y : Subgroup G}
    (h : RootSetting Row.D6 b₀ K E B Y)
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) (hA : E8AutAt Row.D6)
    (hT : E8TorusAt Row.D6) {x : G} (hxY : x ∈ Y)
    {a g : ↥(adjointGroup .E7 (ZMod 2))} (hψa : ψ a = ⟨x, hxY⟩)
    (hgH : ((g * a * g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
      CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2))
    {g₁ : G} (hg₁ : Subgroup.zpowers (g₁ * b₀ * g₁⁻¹) = Subgroup.zpowers x) :
    ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈
        CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
      ∃ y ∈ Y, ((ψ r : ↥Y) : G) = y * b₀ * y⁻¹ := by
  obtain ⟨r, hrH, hmain⟩ := exists_rootElt_of_zpowers ψ hxY hψa hgH hg₁
  have hgY : (((ψ g : ↥Y) : G) * g₁) * b₀ * (((ψ g : ↥Y) : G) * g₁)⁻¹ ∈ Y := by
    rw [← hmain]
    exact (ψ r).2
  obtain ⟨y, hyY, hy⟩ := h.exists_conj_eq_of_conj_mem hA hT hgY
  exact ⟨r, hrH, y, hyY, hmain.trans hy⟩

private lemma exists_vec_facts_of_d6Good {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G 7} {Y : Subgroup G}
    (h : RootSetting Row.D6 b₀ K E B Y)
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y)
    {A : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    (hAdef : A = (E.subgroupOf Y).map ψ.symm.toMonoidHom)
    {e : Coords 7} (he : e ∈ d6GoodSet) :
    ∃ (x : G) (_ : x ∈ E) (hxY : x ∈ Y) (a : ↥(adjointGroup .E7 (ZMod 2))),
      x = B.vec e ∧ a ∈ A ∧ a ≠ 1 ∧ ψ a = ⟨x, hxY⟩ := by
  have hgood : d6Good e := by
    simpa [d6GoodSet] using he
  let x : G := B.vec e
  have hxE : x ∈ E := h.adapted.1 ▸ B.vec_mem_span e
  have hxY : x ∈ Y := h.torus_le hxE
  let a : ↥(adjointGroup .E7 (ZMod 2)) := ψ.symm ⟨x, hxY⟩
  have hψa : ψ a = ⟨x, hxY⟩ := ψ.apply_symm_apply ⟨x, hxY⟩
  have haA : a ∈ A := by
    rw [hAdef]
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hxE, rfl⟩
  have hane : a ≠ 1 := by
    intro ha1
    have h1 : (⟨x, hxY⟩ : ↥Y) = 1 := by
      rw [← hψa, ha1, map_one]
    have hxne : x ≠ 1 := by
      intro hx1
      have h0 : B.vec e = B.vec 0 := by
        rw [B.vec_zero]
        exact hx1
      exact ne_zero_of_d6Good hgood (B.vec_injective h0)
    exact hxne (by simpa using congrArg Subtype.val h1)
  exact ⟨x, hxE, hxY, a, rfl, haA, hane, hψa⟩

private theorem exists_rootElt_of_mem_d6LineSet
    {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G 7} {Y : Subgroup G}
    (h : RootSetting Row.D6 b₀ K E B Y)
    (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) (hA : E8AutAt Row.D6)
    (hT : E8TorusAt Row.D6) {A Q : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    (hAdef : A = (E.subgroupOf Y).map ψ.symm.toMonoidHom)
    (hQroot : ∀ a ∈ A, a ≠ 1 → Q ≤ Subgroup.normalizer
        (Subgroup.zpowers a : Set ↥(adjointGroup .E7 (ZMod 2))) →
      ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
        ((g * a * g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
          CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2))
    {L : Subgroup G} (hLline : L ∈ d6LineSet B)
    (hLfix : ∀ q : ↥(adjointGroup .E7 (ZMod 2)), q ∈ Q →
      L.map (MulAut.conj (((ψ q : ↥Y) : G))).toMonoidHom = L) :
    ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈
        CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
      ∃ y ∈ Y, ((ψ r : ↥Y) : G) = y * b₀ * y⁻¹ := by
  classical
  obtain ⟨e, he, hLe⟩ := Finset.mem_image.mp hLline
  have hgood : d6Good e := by
    simpa [d6GoodSet] using he
  obtain ⟨x, hxE, hxY, a, hx, haA, hane, hψa⟩ := exists_vec_facts_of_d6Good h ψ hAdef he
  have hLx : L = Subgroup.zpowers x := by
    rw [← hLe, hx]
    rfl
  have hQnorma := le_normalizer_zpowers_of_fixed h.torus_le ψ hxE hψa hLx hLfix
  obtain ⟨g, hgH⟩ := hQroot a haA hane hQnorma
  have hconj : IsConjLine b₀ (B.line e) :=
    (h.recOut.2 e (ne_zero_of_d6Good hgood)).mpr hgood
  obtain ⟨g₁, hg₁⟩ := hconj
  exact exists_rootElt_of_conj_mem h ψ hA hT hxY hψa hgH (hg₁.trans (hLe.trans hLx))

private lemma isElemAbelian_card_map_symm {G : Type} [Group G] {Y E : Subgroup G}
    (hEY : E ≤ Y) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y) {A : Subgroup _}
    (hAdef : A = (E.subgroupOf Y).map ψ.symm.toMonoidHom)
    (hEea : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 7) :
    IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 7 := by
  rw [hAdef]
  refine ⟨(hEea.subgroupOf Y).map ψ.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective ψ.symm.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hEcard]

private lemma exists_isPGroup_normalizer_span {G : Type} [Group G] {Y E : Subgroup G}
    {B : Basis3 G 7} (hEY : E ≤ Y) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y)
    {A Q : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    (hAdef : A = (E.subgroupOf Y).map ψ.symm.toMonoidHom)
    (hQ2 : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (A : Set ↥(adjointGroup .E7 (ZMod 2))))
    (hspan : B.span = E) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ Subgroup.normalizer (B.span : Set G) ∧
      ∀ q ∈ Q, ((ψ q : ↥Y) : G) ∈ P := by
  let QY : Subgroup ↥Y := Q.map ψ.toMonoidHom
  let P : Subgroup G := QY.map Y.subtype
  have hAmap : A.map ψ.toMonoidHom = E.subgroupOf Y := by
    rw [hAdef, Subgroup.map_map]
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id ↥Y := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hQYnorm : QY ≤ (Subgroup.normalizer (E : Set G)).subgroupOf Y := by
    rw [Subgroup.subgroupOf_normalizer_eq hEY]
    have h := Subgroup.map_mono (f := ψ.toMonoidHom) hQN
    rwa [Subgroup.map_equiv_normalizer_eq A ψ, hAmap] at h
  refine ⟨P, (hQ2.map ψ.toMonoidHom).map Y.subtype, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    have hqE : ((q : ↥Y) : G) ∈ Subgroup.normalizer (E : Set G) :=
      Subgroup.mem_subgroupOf.mp (hQYnorm hq)
    simpa [hspan] using hqE
  · intro q hq
    exact Subgroup.mem_map.mpr ⟨ψ q, Subgroup.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩

theorem d6RootEltAt_of_rootLines
    (hL : E7TorusRootLines) (hA : E8AutAt Row.D6) (hT : E8TorusAt Row.D6) :
    D6RootEltAt := by
  intro G _ _ b₀ K E B Y h ψ
  have hrec : RecOutD6 B b₀ := h.recOut
  have hEY : E ≤ Y := h.torus_le
  have hEea : IsElemAbelian 3 E := h.std.2.1.2.1.2.1
  have hEcard : Nat.card E = 3 ^ 7 := by
    have h' := h.std.2.1.2.2.2.1
    rwa [show Row.D6.m = 7 from rfl] at h'
  let A : Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
    (E.subgroupOf Y).map ψ.symm.toMonoidHom
  obtain ⟨hAea, hAcard⟩ := isElemAbelian_card_map_symm hEY ψ rfl hEea hEcard
  obtain ⟨Q, hQ2, hQN, hQroot⟩ := hL A hAea hAcard
  obtain ⟨P, hP2, hPnorm, hPmem⟩ :=
    exists_isPGroup_normalizer_span hEY ψ rfl hQ2 hQN h.adapted.1
  obtain ⟨L, hLline, hLfixP⟩ := exists_mem_d6LineSet_fixed hrec P hP2 hPnorm
  have hLfix : ∀ q : ↥(adjointGroup .E7 (ZMod 2)), q ∈ Q →
      L.map (MulAut.conj (((ψ q : ↥Y) : G))).toMonoidHom = L :=
    fun q hq => hLfixP _ (hPmem q hq)
  exact exists_rootElt_of_mem_d6LineSet h ψ hA hT rfl hQroot hLline hLfix

end CFSG.StandardType.FrameRoute.FS81
