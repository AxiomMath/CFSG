module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameTrans
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeRoots
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6EltDefs
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}

set_option maxRecDepth 100000 in
theorem e7Good_neg : ∀ v : Coords 8, e7Good v → e7Good (-v) := by
  decide +kernel

@[expose] def goodA : Finset (Coords 8) := Finset.univ.filter fun v => e7Good v ∧ v 0 = 0

noncomputable def lineSetA (B : Basis3 G 8) : Finset (Subgroup G) := by
  classical
  exact goodA.image B.line

open scoped Classical in
private theorem card_fiber_lineSetA {B : Basis3 G 8} {L : Subgroup G} (hL : L ∈ lineSetA B) :
    (goodA.filter fun e => B.line e = L).card = 2 := by
  classical
  obtain ⟨e, he, hLe⟩ := Finset.mem_image.mp hL
  have hgood : e7Good e ∧ e 0 = 0 := by simpa [goodA] using he
  have he0 : e ≠ 0 := hgood.1.ne_zero
  have hne : e ≠ -e := by
    intro h
    apply he0
    funext i
    exact (by decide : ∀ x : ZMod 3, x = -x → x = 0) (e i) (congrFun h i)
  have hsub : goodA.filter (fun e' => B.line e' = B.line e) = {e, -e} := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he', hline⟩
      have he'good : e7Good e' ∧ e' 0 = 0 := by simpa [goodA] using he'
      have hmem : B.vec e' ∈ Subgroup.zpowers (B.vec e) := by
        have h : B.vec e' ∈ B.line e' := Subgroup.mem_zpowers _
        rw [hline, Basis3.line] at h
        exact h
      exact B.eq_or_eq_neg_of_vec_mem_zpowers he'good.1.ne_zero hmem
    · rintro (rfl | rfl)
      · exact ⟨he, rfl⟩
      · refine ⟨?_, by rw [Basis3.line, Basis3.line, B.vec_neg_eq_inv, Subgroup.zpowers_inv]⟩
        simp only [goodA, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e7Good_neg e hgood.1, by rw [Pi.neg_apply, hgood.2, neg_zero]⟩
  rw [show (goodA.filter fun e' => B.line e' = L) =
      goodA.filter (fun e' => B.line e' = B.line e) by rw [← hLe]]
  rw [hsub, Finset.card_pair hne]

theorem card_lineSetA (B : Basis3 G 8) : (lineSetA B).card = 63 := by
  classical
  have hsum := Finset.card_eq_sum_card_fiberwise (s := goodA) (t := lineSetA B)
    (f := fun e => B.line e) (fun e he => Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hsum2 : goodA.card = ∑ L ∈ lineSetA B, 2 :=
    hsum.trans (Finset.sum_congr rfl fun L hL => by convert card_fiber_lineSetA hL)
  rw [Finset.sum_const] at hsum2
  have hgood : goodA.card = 126 := card_good_zero
  have h : (lineSetA B).card * 2 = 126 := by
    simpa [smul_eq_mul, hgood] using hsum2.symm
  omega

theorem map_conj_mem_lineSetA [Finite G] (hstd : StdAssumptions b₀ K E Row.E7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) {q : G}
    (hqA : q ∈ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G)) {L : Subgroup G}
    (hL : L ∈ lineSetA B) : L.map (MulAut.conj q).toMonoidHom ∈ lineSetA B := by
  classical
  obtain ⟨-, ⟨⟨hb₀ord, -⟩, -, hb₀E, -⟩, ⟨-, hdisj, -⟩⟩ := hstd
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hL
  have hgood : e7Good e ∧ e 0 = 0 := by simpa [goodA] using he
  have heA : B.vec e ∈ E ⊓ K := ⟨hB.1 ▸ B.vec_mem_span e, vec_mem_K hB hgood.2⟩
  have hqmem : q * B.vec e * q⁻¹ ∈ E ⊓ K := (Subgroup.mem_normalizer_iff.mp hqA _).mp heA
  obtain ⟨e', he'⟩ := B.exists_vec_eq (hB.1.symm ▸ hqmem.1 : q * B.vec e * q⁻¹ ∈ B.span)
  have hline : (B.line e).map (MulAut.conj q).toMonoidHom = B.line e' := by
    rw [Basis3.line, Basis3.line, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, ← he']
  have he'0 : e' ≠ 0 := by
    intro h0
    have hconj1 : (MulAut.conj q) (B.vec e) = (MulAut.conj q) 1 := by
      rw [MulAut.conj_apply, map_one, ← he', h0, B.vec_zero]
    have hvec : B.vec e = 1 := (MulAut.conj q).injective hconj1
    exact hgood.1.ne_zero (B.vec_injective (by rw [hvec, B.vec_zero]))
  have hconj : IsConjLine b₀ (B.line e') := by
    rw [← hline]
    exact isConjLine_map_conj ((hrec.2.1 e hgood.1.ne_zero).mpr hgood.1) q
  have hgood' : e7Good e' := (hrec.2.1 e' he'0).mp hconj
  have he'K : e' 0 = 0 := zero_of_vec_mem_K hB hb₀ord hdisj hb₀E (he' ▸ hqmem.2)
  refine Finset.mem_image.mpr ⟨e', ?_, hline.symm⟩
  simp only [goodA, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hgood', he'K⟩

@[instance_reducible]
private noncomputable def lineSetAConjAction [Finite G] (hstd : StdAssumptions b₀ K E Row.E7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) (P : Subgroup G)
    (hPA : P ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G)) :
    MulAction P ↥(lineSetA B) := by
  classical
  letI : MulAction (ConjAct G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction P (Subgroup G) :=
    MulAction.compHom (Subgroup G) (ConjAct.toConjAct.toMonoidHom.comp P.subtype)
  refine
    { smul := fun q L => ⟨q • (L : Subgroup G), ?_⟩
      one_smul := fun L => Subtype.ext (one_smul P (L : Subgroup G))
      mul_smul := fun q r L => Subtype.ext (mul_smul q r (L : Subgroup G)) }
  change (ConjAct.toConjAct ((q : P) : G) • (L : Subgroup G)) ∈ lineSetA B
  rw [show ConjAct.toConjAct ((q : P) : G) • (L : Subgroup G) =
      (L : Subgroup G).map (MulAut.conj (((q : P) : G))).toMonoidHom by
    rw [Subgroup.pointwise_smul_def]
    rfl]
  exact map_conj_mem_lineSetA hstd hB hrec (hPA q.2) L.2

theorem exists_mem_lineSetA_fixed [Finite G] (hstd : StdAssumptions b₀ K E Row.E7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) (P : Subgroup G)
    (hP : IsPGroup 2 P) (hPA : P ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G)) :
    ∃ L ∈ lineSetA B, ∀ q ∈ P, L.map (MulAut.conj q).toMonoidHom = L := by
  classical
  let : MulAction P ↥(lineSetA B) := lineSetAConjAction hstd hB hrec P hPA
  let : MulAction (ConjAct G) (Subgroup G) := Subgroup.pointwiseMulAction
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ Nat.card ↥(lineSetA B) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_lineSetA B]
    decide
  obtain ⟨L, hL⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card ↥(lineSetA B) hnot
  refine ⟨L.1, L.2, fun q hq => ?_⟩
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hL ⟨q, hq⟩)
  change ConjAct.toConjAct q • (L : Subgroup G) = L at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.conjAct_pointwise_smul_iff.mp h)

private theorem mem_normalizer_zpowers_of_map_conj (ψ : ↥L7 ≃* ↥K) {x : G} (hxK : x ∈ K)
    {a q : ↥L7} (hψa : ψ a = ⟨x, hxK⟩)
    (hqline : (Subgroup.zpowers x).map
      (MulAut.conj (((ψ q : ↥K) : G))).toMonoidHom = Subgroup.zpowers x) :
    q ∈ Subgroup.normalizer (Subgroup.zpowers a : Set ↥L7) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hinj : Function.Injective (K.subtype.comp ψ.toMonoidHom) :=
    K.subtype_injective.comp ψ.injective
  have himg2 : (Subgroup.zpowers a).map (K.subtype.comp ψ.toMonoidHom) = Subgroup.zpowers x := by
    simp [hψa]
  have hqa : (K.subtype.comp ψ.toMonoidHom) (q * a * q⁻¹) =
      ((ψ q : ↥K) : G) * x * (((ψ q : ↥K) : G))⁻¹ := by
    simp [hψa]
  have himg1 : ((Subgroup.zpowers a).map (MulAut.conj q).toMonoidHom).map
        (K.subtype.comp ψ.toMonoidHom) = Subgroup.zpowers x := by
    calc
      ((Subgroup.zpowers a).map (MulAut.conj q).toMonoidHom).map (K.subtype.comp ψ.toMonoidHom)
          = Subgroup.zpowers ((K.subtype.comp ψ.toMonoidHom) ((MulAut.conj q) a)) := by
            rw [Subgroup.map_map, MonoidHom.map_zpowers]
            rfl
      _ = Subgroup.zpowers ((K.subtype.comp ψ.toMonoidHom) (q * a * q⁻¹)) := by
            rw [MulAut.conj_apply]
      _ = Subgroup.zpowers (((ψ q : ↥K) : G) * x * (((ψ q : ↥K) : G))⁻¹) := by
            rw [hqa]
      _ = (Subgroup.zpowers x).map (MulAut.conj (((ψ q : ↥K) : G))).toMonoidHom := by
            rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      _ = Subgroup.zpowers x := hqline
  exact Subgroup.map_injective hinj (himg1.trans himg2.symm)

section Root


theorem exists_model_b1 [Finite G] (hL : E7TorusRootLines) (hW : E7NatWeyl)
    (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutE7 B b₀)
    (hcard : Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) = 2903040)
    (hCKC : Subgroup.centralizer ({b₀} : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G))
    (ψ : ↥L7 ≃* ↥K) :
    ∃ (ψ' : ↥L7 ≃* ↥K) (z : ↥L7), (z : ModGL .E7 (ZMod 2)) ∈ Jn 0 ∧ ((ψ' z : ↥K) : G) = B.b 1 := by
  classical
  have hEea : IsElemAbelian 3 E := hstd.2.1.2.1.2.1
  have hAcard : Nat.card ↥(E ⊓ K) = 3 ^ 7 := hstd.2.2.2.2.2.2.1
  let A' : Subgroup ↥L7 := (E.subgroupOf K).map ψ.symm.toMonoidHom
  have hA'ea : IsElemAbelian 3 A' := (hEea.subgroupOf K).map _
  have hA'card : Nat.card A' = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective ψ.symm.injective, ← hAcard,
      ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
  obtain ⟨Q, hQ2, hQN, hQroot⟩ := hL A' hA'ea hA'card
  have hAmap : A'.map ψ.toMonoidHom = (E ⊓ K).subgroupOf K := by
    rw [Subgroup.map_map, Subgroup.inf_subgroupOf_right]
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id ↥K := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hQnorm : Q.map ψ.toMonoidHom ≤
      (Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G)).subgroupOf K := by
    rw [Subgroup.subgroupOf_normalizer_eq inf_le_right]
    have h := Subgroup.map_mono (f := ψ.toMonoidHom) hQN
    rwa [Subgroup.map_equiv_normalizer_eq A' ψ, hAmap] at h
  let P : Subgroup G := (Q.map ψ.toMonoidHom).map K.subtype
  have hP2 : IsPGroup 2 P := (hQ2.map ψ.toMonoidHom).map K.subtype
  have hPA : P ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQnorm hy)
  obtain ⟨L, hL, hLfix⟩ := exists_mem_lineSetA_fixed hstd hB hrec P hP2 hPA
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hL
  have hgood : e7Good v ∧ v 0 = 0 := by simpa [goodA] using hv
  have hxK : B.vec v ∈ K := vec_mem_K hB hgood.2
  let a : ↥L7 := ψ.symm ⟨B.vec v, hxK⟩
  have hψa : ψ a = ⟨B.vec v, hxK⟩ := ψ.apply_symm_apply _
  have haA : a ∈ A' :=
    Subgroup.mem_map.mpr ⟨⟨B.vec v, hxK⟩,
      Subgroup.mem_subgroupOf.mpr (hB.1 ▸ B.vec_mem_span v), rfl⟩
  have hane : a ≠ 1 := by
    intro ha1
    have h1 : (⟨B.vec v, hxK⟩ : ↥K) = 1 := by rw [← hψa, ha1, map_one]
    have hv1 : B.vec v = B.vec 0 := by
      rw [B.vec_zero]
      exact congrArg Subtype.val h1
    exact hgood.1.ne_zero (B.vec_injective hv1)
  have hQa : Q ≤ Subgroup.normalizer (Subgroup.zpowers a : Set ↥L7) := by
    intro q hq
    refine mem_normalizer_zpowers_of_map_conj ψ hxK hψa ?_
    have hqP : ((ψ q : ↥K) : G) ∈ P := ⟨ψ q, ⟨q, hq, rfl⟩, rfl⟩
    exact hLfix _ hqP
  obtain ⟨g, hgr⟩ := hQroot a haA hane hQa
  obtain ⟨k, hkC, -, hk⟩ := exists_conj_b1 hstd hB hrec hcard hgood.1 hgood.2
  obtain ⟨κ, hκ, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy x hx) (hCKC hkC)
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hκb : κ * B.b 1 * κ⁻¹ = B.vec v := by
    rw [← hk]
    have hcb : c * B.b 1 = B.b 1 * c := (Subgroup.mem_centralizer_iff.mp hc _ hb₁K).symm
    calc κ * B.b 1 * κ⁻¹ = κ * (c * B.b 1 * c⁻¹) * κ⁻¹ := by rw [hcb]; group
      _ = κ * c * B.b 1 * (κ * c)⁻¹ := by group
  let κ' : ↥L7 := ψ.symm ⟨κ, hκ⟩
  let b' : ↥L7 := ψ.symm ⟨B.b 1, hb₁K⟩
  have hab : a = κ' * b' * κ'⁻¹ := by
    apply ψ.injective
    apply Subtype.ext
    simp only [a, κ', b', map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact hκb.symm
  obtain ⟨⟨w, hwL, hw⟩, -⟩ := hW
  let w' : ↥L7 := ⟨w, hwL⟩
  have hJθ : J theta = CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) :=
    (exceptional_Lang_root_rank_one_torus_transport .E7 (ZMod 2)
      (CFSG.SeitzReduction.isRoot_highRoot .E7)).1
  let r : ↥L7 := g * a * g⁻¹
  have hrJ : (r : ModGL .E7 (ZMod 2)) ∈ J theta := hJθ ▸ hgr
  let y : ↥L7 := κ'⁻¹ * g⁻¹ * w'⁻¹
  refine ⟨(MulAut.conj y).trans ψ, w' * r * w'⁻¹, ?_, ?_⟩
  · rw [← hw]
    exact ⟨r, hrJ, rfl⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply]
    have hy : y * (w' * r * w'⁻¹) * y⁻¹ = b' := by
      simp only [y, r, hab]
      group
    rw [hy]
    simp [b']

end Root

end CFSG.StandardType.FrameRoute.FS81.E7Frame
