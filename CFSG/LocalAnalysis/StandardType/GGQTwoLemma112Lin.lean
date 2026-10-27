module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Class
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Transport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2xKDe_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma ggQ2xKDe_range_simpleRefl {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {ι : Type} (h : ι → U) (α : ι → Module.Dual (ZMod 3) U) (s : ι → U ≃ₗ[ZMod 3] U)
    (hs : ∀ i v, s i v = v - α i v • h i) :
    Set.range s = {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, hs i⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, hs j v]⟩

private lemma ggQ2xKDe_isReflLin_form {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Fact (Nat.Prime 3)] (t : U ≃ₗ[ZMod 3] U) (ht : IsReflLin t) :
    ∃ (v : U) (f : Module.Dual (ZMod 3) U), ∀ x, t x = x - f x • v := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  exact ⟨c, φ, fun x => Module.reflection_apply x hφ⟩

private lemma ggQ2xKDe_sq_of_isReflLin {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Fact (Nat.Prime 3)] (t : U ≃ₗ[ZMod 3] U) (ht : IsReflLin t) : t ^ 2 = 1 := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  ext x
  rw [pow_two, LinearEquiv.mul_apply]
  simpa using Module.involutive_reflection hφ x

private lemma ggQ2xKDe_reflection_ne_one {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (c : U) (f : Module.Dual (ZMod 3) U) (hf : f c = 2) : Module.reflection hf ≠ 1 := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact (by decide : (2 : ZMod 3) ≠ 0) hf.symm
  intro h1
  have h2 : Module.reflection hf c = c := by rw [h1]; rfl
  rw [Module.reflection_apply, hf] at h2
  have h3 : (2 : ZMod 3) • c = 0 := sub_eq_self.mp h2
  exact hc ((smul_eq_zero.mp h3).resolve_left (by decide))

private lemma ggQ2xKDe_conj_mem {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Fact (Nat.Prime 3)] (hfin : Finite U) (h : Fin 6 → U) (hb : LinearIndependent (ZMod 3) h)
    (α : Fin 6 → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.E 6 i j : ℤ) : ZMod 3))
    (s : Fin 6 → U ≃ₗ[ZMod 3] U) (hs : ∀ i v, s i v = v - α i v • h i)
    (S : U ≃ₗ[ZMod 3] U)
    (hS : ∀ x ∈ Subgroup.closure (Set.range s), S * x * S⁻¹ ∈ Subgroup.closure (Set.range s)) :
    ∀ t ∈ ggReflConj s, S * t * S⁻¹ ∈ ggReflConj s := by
  haveI : Finite U := hfin
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 6) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
    rwa [TauCeti.DynkinType.cartanMatrix_E6] at h
  have hclosed : GGReflClosed s :=
    ggReflClosed_of_indep (p := 3) (by norm_num) hFT ggIntCartan_E₆ h α
      (fun i j => by simpa using hα i j) hb s hs
  intro t ht
  obtain ⟨u, hu, k, rfl⟩ := ht
  have hself : α k (h k) = 2 := by rw [hα k k]; simp [CartanMatrix.E]
  have hsk : s k = Module.reflection hself :=
    LinearEquiv.ext fun v => by rw [hs k v, Module.reflection_apply]
  have huk : u * s k * u⁻¹ ∈ Subgroup.closure (Set.range s) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hu (Subgroup.subset_closure ⟨k, rfl⟩))
      (Subgroup.inv_mem _ hu)
  have hSuk : S * (u * s k * u⁻¹) * S⁻¹ ∈ Subgroup.closure (Set.range s) := hS _ huk
  have hrefl : IsReflLin (S * (u * s k * u⁻¹) * S⁻¹) := by
    have h1 : IsReflLin (s k) := ⟨h k, α k, hself, hsk⟩
    exact ggQ2_isReflLin_conj S (u * s k * u⁻¹) (ggQ2_isReflLin_conj u (s k) h1)
  have hne : S * (u * s k * u⁻¹) * S⁻¹ ≠ 1 := by
    have hsk1 : s k ≠ 1 := by
      rw [hsk]
      exact ggQ2xKDe_reflection_ne_one (h k) (α k) hself
    intro h1
    have h2 : u * s k * u⁻¹ = 1 := by
      have := congrArg (fun x => S⁻¹ * x * S) h1
      simpa [mul_assoc] using this
    have h3 : s k = 1 := by
      have := congrArg (fun x => u⁻¹ * x * u) h2
      simpa [mul_assoc] using this
    exact hsk1 h3
  exact hclosed _ hSuk (ggQ2xKDe_sq_of_isReflLin _ hrefl) hne
    (ggQ2xKDe_isReflLin_form _ hrefl)

theorem ggQ2WeylInner_E6 : GGQ2WeylInner 6 (CartanMatrix.E 6) := by
  classical
  intro U instACG instMod h hb hspan α hα T hT
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfr : Module.finrank (ZMod 3) U = 6 := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  have hfin : Finite U := by
    have hmod : Module.Finite (ZMod 3) (↥(Submodule.span (ZMod 3) (Set.range h))) :=
      Module.Finite.span_of_finite (ZMod 3) (Set.finite_range h)
    rw [hspan] at hmod
    haveI : Module.Finite (ZMod 3) (↥(⊤ : Submodule (ZMod 3) U)) := hmod
    haveI : Finite (↥(⊤ : Submodule (ZMod 3) U)) := Module.finite_of_finite (ZMod 3)
    exact Finite.of_surjective (Subtype.val : ↥(⊤ : Submodule (ZMod 3) U) → U)
      (fun u => ⟨⟨u, Submodule.mem_top⟩, rfl⟩)
  let D' : GGQ2Lin 3 :=
    { ι := Fin 6
      coxeter := CoxeterMatrix.E₆
      cartan := CartanMatrix.E 6
      V := U
      coroot := h
      root := α
      a := ⟨5, by norm_num⟩
      b := ⟨0, by norm_num⟩
      a_ne_b := by decide
      a_leaf := by
        refine ⟨⟨4, by norm_num⟩, ⟨by decide, by decide⟩, ?_⟩
        intro y hy
        fin_cases y <;> simp_all [CartanMatrix.E]
      isWeyl := Or.inr (Or.inl ⟨Equiv.refl _, (ggQ2xKDe_reindex_refl _).symm⟩)
      isCartan := ggIntCartan_E₆
      pairing := fun i j => by simpa using hα i j }
  have hbas : D'.Basis := by
    change LinearIndependent (ZMod 3) h ∧ Fintype.card (Fin 6) = Module.finrank (ZMod 3) U
    exact ⟨hb, by simp [hfr]⟩
  have hE6 : ∃ e : Fin 6 ≃ D'.ι, D'.coxeter = CoxeterMatrix.E₆.reindex e :=
    ⟨Equiv.refl _, (ggQ2xKDe_reindex_refl CoxeterMatrix.E₆).symm⟩
  have hgen : Set.range D'.simpleRefl =
      {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} :=
    ggQ2xKDe_range_simpleRefl h α D'.simpleRefl (fun i v => by
      rw [GGQ2Lin.simpleRefl, Module.reflection_apply])
  have hWclos : D'.weyl = Subgroup.closure (Set.range D'.simpleRefl) := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]
  have hweylEq : D'.weyl = ggQ2WeylOf h α := by
    rw [hWclos, hgen]
    rfl
  have hT' : T ∈ Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U)) := by
    rwa [hweylEq]
  have hconjEq : ggReflConj D'.simpleRefl = ggQ2xQ_isConjRefl D' := by
    ext x
    constructor
    · rintro ⟨u, hu, i, rfl⟩
      exact ⟨i, u, hWclos.symm ▸ hu, rfl⟩
    · rintro ⟨i, u, hu, rfl⟩
      exact ⟨u, hWclos ▸ hu, i, rfl⟩
  have hconj_mem : ∀ S ∈ Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U)),
      ∀ t ∈ ggQ2xQ_isConjRefl D', S * t * S⁻¹ ∈ ggQ2xQ_isConjRefl D' := by
    intro S hS t ht
    have hS' : ∀ x ∈ Subgroup.closure (Set.range D'.simpleRefl),
        S * x * S⁻¹ ∈ Subgroup.closure (Set.range D'.simpleRefl) := by
      intro x hx
      have hxW : x ∈ D'.weyl := hWclos.symm ▸ hx
      exact hWclos ▸ (Subgroup.mem_normalizer_iff.mp hS x).mp hxW
    exact hconjEq ▸ ggQ2xKDe_conj_mem hfin h hb α hα D'.simpleRefl
      (fun i v => by rw [GGQ2Lin.simpleRefl, Module.reflection_apply]) S hS'
      t (hconjEq.symm ▸ ht)
  let π : (U ≃ₗ[ZMod 3] U) → (U ≃ₗ[ZMod 3] U) := fun t => T * t * T⁻¹
  have hπT : ∀ t ∈ ggQ2xQ_isConjRefl D', π t ∈ ggQ2xQ_isConjRefl D' := by
    intro t ht
    change T * t * T⁻¹ ∈ ggQ2xQ_isConjRefl D'
    exact hconj_mem T hT' t ht
  have hsurj : Set.SurjOn π (ggQ2xQ_isConjRefl D') (ggQ2xQ_isConjRefl D') := by
    intro b hb
    refine ⟨T⁻¹ * b * T, ?_, ?_⟩
    · change T⁻¹ * b * T ∈ ggQ2xQ_isConjRefl D'
      exact hconj_mem T⁻¹ (Subgroup.inv_mem _ hT') b hb
    · change T * (T⁻¹ * b * T) * T⁻¹ = b
      group
  have hinj : Set.InjOn π (ggQ2xQ_isConjRefl D') := by
    intro a _ b _ hab
    change T * a * T⁻¹ = T * b * T⁻¹ at hab
    have h := congrArg (fun x => T⁻¹ * x * T) hab
    simpa [mul_assoc] using h
  have hπ : ∀ s ∈ ggQ2xQ_isConjRefl D', ∀ t ∈ ggQ2xQ_isConjRefl D',
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹ := by
    intro s _ t _
    change T * (s * t * s⁻¹) * T⁻¹ =
      (T * s * T⁻¹) * (T * t * T⁻¹) * (T * s * T⁻¹)⁻¹
    group
  obtain ⟨g, hgW, hgconj⟩ := ggQ2_quandle_aut_E D' hbas (Or.inl hE6) π hπT hinj hsurj hπ
  refine ⟨g, hweylEq ▸ hgW, ?_⟩
  intro x hx
  have hx' : x ∈ Subgroup.closure (Set.range D'.simpleRefl) :=
    hWclos ▸ (hweylEq.symm ▸ hx)
  have hkey : ∀ y ∈ Subgroup.closure (Set.range D'.simpleRefl),
      T * y * T⁻¹ = g * y * g⁻¹ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨k, rfl⟩ := hz
        exact hgconj _ (ggQ2xQ_simpleRefl_mem_isConjRefl D' k)
    | one => group
    | mul y z _ _ ihy ihz =>
        rw [show T * (y * z) * T⁻¹ = (T * y * T⁻¹) * (T * z * T⁻¹) by group, ihy, ihz]
        group
    | inv y _ ihy =>
        rw [show T * y⁻¹ * T⁻¹ = (T * y * T⁻¹)⁻¹ by group, ihy]
        group
  exact hkey x hx'

theorem GGQ2Lin.inner_of_span {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (xV : D.V)
    (hx0 : xV ≠ 0)
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ D.a} => D.coroot i))
    (hspan : xV ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ D.a} => D.coroot i))
    (hdim : Module.finrank (ZMod p) D.V ≤ Fintype.card {k // k ≠ D.a} + 1)
    (h4 : 4 ≤ Module.finrank (ZMod p) D.V)
    (hTF : TransvectionFree (D.parab {k | k ≠ D.a}))
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV})
    (T : D.V ≃ₗ[ZMod p] D.V)
    (hTnorm : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod p] D.V)))
    (hTx : T xV ∈ Submodule.span (ZMod p) {xV}) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ g ∈ D.parab {k | k ≠ D.a}, T * g * T⁻¹ = w * g * w⁻¹ := by
  have hα := GGQ2Lin.root_eq_zero_of_fix hp D xV hfix
  have hcard : 3 ≤ Fintype.card {k // k ≠ D.a} := by omega
  subst hp
  rcases GGQ2Lin.compl_leaf_A_or_E6 D xV hx0 hspan hα hcard with ⟨k, hk, e, he⟩ | ⟨e, he⟩
  · exact GGQ2Lin.inner_of_transport D _ e he hind hdim hTF (ggQ2WeylInner_A (by omega)) T hTnorm
  · exact GGQ2Lin.inner_of_transport D _ e he hind hdim hTF ggQ2WeylInner_E6 T hTnorm

theorem GGQ2Lin.pmW_of_inner {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV})
    (T : D.V ≃ₗ[ZMod p] D.V)
    (hinner : ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ g ∈ D.parab {k | k ≠ D.a},
      T * g * T⁻¹ = w * g * w⁻¹) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod p) {xV} := by
  obtain ⟨w, hwW, hw⟩ := hinner
  set S : D.V ≃ₗ[ZMod p] D.V := w⁻¹ * T with hSdef
  have hcommS : ∀ g ∈ D.parab {k | k ≠ D.a}, S * g = g * S := by
    intro g hg
    have h1 : S * g * S⁻¹ = g := by
      rw [hSdef]
      calc (w⁻¹ * T) * g * (w⁻¹ * T)⁻¹
          = w⁻¹ * (T * g * T⁻¹) * w := by group
        _ = w⁻¹ * (w * g * w⁻¹) * w := by rw [hw g hg]
        _ = g := by group
    calc S * g = (S * g * S⁻¹) * S := by group
      _ = g * S := by rw [h1]
  obtain ⟨c, hc⟩ := GGQ2Lin.exists_scalar_of_commute hp D xV hfix
      (GGQ2Lin.reflTransGen_compl_leaf hp D) (S : D.V →ₗ[ZMod p] D.V) (fun g hg v => by
        have h := congrArg (fun (e : D.V ≃ₗ[ZMod p] D.V) => e v) (hcommS g hg)
        simp only [LinearEquiv.mul_apply] at h
        have h' : (S : D.V →ₗ[ZMod p] D.V) (g v) =
            g ((S : D.V →ₗ[ZMod p] D.V) v) := h
        rw [h', sub_self]
        exact Submodule.zero_mem _)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hS : ∀ v, S v ∈ Submodule.span (ZMod p) {xV} := by
      intro v
      have hv := hc v
      rw [hc0, zero_smul, sub_zero] at hv
      exact hv
    let j : {k // k ≠ D.a} := ⟨D.b, D.a_ne_b.symm⟩
    have hj : D.coroot j ∈ Submodule.span (ZMod p) {xV} := by
      obtain ⟨v, hv⟩ := S.surjective (D.coroot j)
      rw [← hv]
      exact hS v
    exact GGQ2Lin.coroot_not_mem_span_of_fix hp D xV hfix j hj
  subst hp
  have hc01 : c = 1 ∨ c = -1 := ggQ2_zmod3_eq_one_or_neg_one c hc_ne
  have hTw : ∀ v : D.V, T (w⁻¹ v) = S v := by
    intro v
    have hT_eq : T = w * S := by
      rw [hSdef]
      group
    have hSw : S (w⁻¹ v) = w⁻¹ (S v) := by
      have h := congrArg (fun (e : D.V ≃ₗ[ZMod 3] D.V) => e v)
        (hcommS w⁻¹ (Subgroup.inv_mem _ hwW))
      simpa only [LinearEquiv.mul_apply] using h
    rw [hT_eq, LinearEquiv.mul_apply, hSw]
    exact LinearEquiv.apply_symm_apply w (S v)
  refine ⟨w⁻¹, Subgroup.inv_mem _ hwW, c, hc01, ?_⟩
  intro v
  rw [hTw v]
  exact hc v

theorem GGQ2Lin.pmW_of_span {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (xV : D.V)
    (hx0 : xV ≠ 0)
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ D.a} => D.coroot i))
    (hspan : xV ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ D.a} => D.coroot i))
    (hdim : Module.finrank (ZMod p) D.V ≤ Fintype.card {k // k ≠ D.a} + 1)
    (h4 : 4 ≤ Module.finrank (ZMod p) D.V)
    (hTF : TransvectionFree (D.parab {k | k ≠ D.a}))
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV})
    (T : D.V ≃ₗ[ZMod p] D.V)
    (hTnorm : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod p] D.V)))
    (hTx : T xV ∈ Submodule.span (ZMod p) {xV}) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod p) {xV} :=
  GGQ2Lin.pmW_of_inner hp D xV hfix T
    (GGQ2Lin.inner_of_span hp D xV hx0 hind hspan hdim h4 hTF hfix T hTnorm hTx)
end CFSG.StandardType

end
