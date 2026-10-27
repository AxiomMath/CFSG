module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def CentralIndex (S : Type) [Group S] : Prop :=
  ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → ∀ x ∈ P,
    (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P ≤ 2 →
      x ∈ Subgroup.centralizer (P : Set S)

variable {S : Type} [Group S]

theorem CentralIndex.of_mulEquiv {L : Type} [Group L] [Finite S] (e : S ≃* L)
    (h : CentralIndex L) : CentralIndex S := by
  have : Finite L := Finite.of_equiv S e.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP x hx hidx
  set f : S →* L := e.toMonoidHom with hf
  have hP' : IsSylowTwoOf (P.map f) ⊤ := by
    have h1 := Setup.X6.isSylowOf_map_injective (p := 2) f e.injective
      (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hP)
    rw [Subgroup.map_top_of_surjective f e.surjective] at h1
    exact Setup.X6.isSylowTwoOf_iff_isSylowOf.2 h1
  have hmap : (P ⊓ Subgroup.centralizer ({x} : Set S)).map f =
      P.map f ⊓ Subgroup.centralizer ({f x} : Set L) := by
    rw [Subgroup.map_inf_eq _ _ f e.injective]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, ?_, by simp [hf]⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  have hidx' : (P.map f ⊓ Subgroup.centralizer ({f x} : Set L)).relIndex (P.map f) ≤ 2 := by
    rw [← hmap, Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx
  have h1 := h _ hP' (f x) ⟨x, hx, rfl⟩ hidx'
  refine Subgroup.mem_centralizer_iff.2 fun y hy => e.injective ?_
  rw [map_mul, map_mul]
  exact Subgroup.mem_centralizer_iff.1 h1 (f y) ⟨y, hy, rfl⟩

theorem map_conj_inf_centralizer (P : Subgroup S) (g x : S) :
    (P ⊓ Subgroup.centralizer ({x} : Set S)).map (MulAut.conj g).toMonoidHom =
      P.map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.centralizer ({(MulAut.conj g).toMonoidHom x} : Set S) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨(MulAut.conj g).symm y, ?_, (MulAut.conj g).apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem centralIndex_of_sylow [Finite S] {U : Subgroup S} (hU : IsSylowTwoOf U ⊤)
    (h : ∀ x ∈ U, (U ⊓ Subgroup.centralizer ({x} : Set S)).relIndex U ≤ 2 →
      x ∈ Subgroup.centralizer (U : Set S)) : CentralIndex S := by
  intro P hP x hx hidx
  obtain ⟨g, -, hg⟩ := hU.exists_conj hP
  subst hg
  obtain ⟨u, hu, rfl⟩ := hx
  rw [← map_conj_inf_centralizer,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hidx
  have h1 := h u hu hidx
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 h1 y hy]

theorem map_conj_eq_of_mem_normalizer {P : Subgroup S} {g : S}
    (hg : g ∈ Subgroup.normalizer (P : Set S)) : P.map (MulAut.conj g).toMonoidHom = P := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg z).1 hz
  · intro hy
    refine ⟨g⁻¹ * y * g, (Subgroup.mem_normalizer_iff.1 hg _).2 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    · change g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem relIndex_inf_centralizer_conj {P : Subgroup S} {g : S}
    (hg : g ∈ Subgroup.normalizer (P : Set S)) (x : S) :
    (P ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set S)).relIndex P =
      (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P := by
  have h := Subgroup.relIndex_map_map_of_injective (P ⊓ Subgroup.centralizer ({x} : Set S)) P
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_conj_inf_centralizer, map_conj_eq_of_mem_normalizer hg] at h
  exact h

theorem mem_centralizer_of_conj {P : Subgroup S} {g x : S}
    (hg : g ∈ Subgroup.normalizer (P : Set S))
    (h : g * x * g⁻¹ ∈ Subgroup.centralizer (P : Set S)) :
    x ∈ Subgroup.centralizer (P : Set S) := by
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have h1 := Subgroup.mem_centralizer_iff.1 h (g * y * g⁻¹)
    ((Subgroup.mem_normalizer_iff.1 hg y).1 hy)
  have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
    calc g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := h1
      _ = g * (x * y) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem conj_mul_conj_comm {g a x : S} (h : a * x = x * a) :
    g * a * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * a * g⁻¹) := by
  calc g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
    _ = g * (x * a) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * (g * a * g⁻¹) := by group

theorem mul_mem_of_relIndex_le_two [Finite S] {P C : Subgroup S} (h : (P ⊓ C).relIndex P ≤ 2)
    {g g' : S} (hg : g ∈ P) (hg' : g' ∈ P) (hgC : g ∉ C) (hg'C : g' ∉ C) : g * g' ∈ C := by
  rw [Subgroup.inf_relIndex_left] at h
  have h0 : C.relIndex P ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show C.relIndex P = 1 ∨ C.relIndex P = 2 by omega) with h1 | h2
  · exact absurd (Subgroup.relIndex_eq_one.1 h1 hg) hgC
  · exact (Subgroup.mul_mem_iff_of_index_two (H := C.subgroupOf P) h2 (a := ⟨g, hg⟩)
      (b := ⟨g', hg'⟩)).2 (iff_of_false hgC hg'C)

theorem mul_self_mem_of_relIndex_le_two [Finite S] {P C : Subgroup S}
    (h : (P ⊓ C).relIndex P ≤ 2) {g : S} (hg : g ∈ P) : g * g ∈ C := by
  by_cases hgC : g ∈ C
  · exact C.mul_mem hgC hgC
  · exact mul_mem_of_relIndex_le_two h hg hg hgC hgC

theorem exists_ne_one_commute [Finite S] {P R : Subgroup S} (hRP : R ≤ P)
    (hR : 2 < Nat.card R) {x : S} (hx : (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P ≤ 2) :
    ∃ r ∈ R, r ≠ 1 ∧ r * x = x * r := by
  by_contra hcon
  push Not at hcon
  have hbot : Subgroup.centralizer ({x} : Set S) ⊓ R = ⊥ := by
    refine eq_bot_iff.2 fun r hr => Subgroup.mem_bot.2 ?_
    by_contra hr1
    exact hcon r hr.2 hr1 (Subgroup.mem_centralizer_singleton_iff.1 hr.1)
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({x} : Set S)) R
  rw [hbot, Subgroup.card_bot, mul_one] at h1
  have h2 : (Subgroup.centralizer ({x} : Set S)).relIndex R ≤
      (Subgroup.centralizer ({x} : Set S)).relIndex P :=
    Subgroup.relIndex_le_of_le_right hRP Subgroup.index_ne_zero_of_finite
  rw [Subgroup.inf_relIndex_left] at hx
  omega

theorem exists_ne_zero_commute_of_hom [Finite S] {F : Type} [AddGroup F] {P : Subgroup S}
    (φ : Multiplicative F →* S) (hφ : Function.Injective φ) (hφP : ∀ a, φ a ∈ P)
    (hF : 2 < Nat.card F) {x : S}
    (hx : (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P ≤ 2) :
    ∃ a : F, a ≠ 0 ∧ φ (Multiplicative.ofAdd a) * x = x * φ (Multiplicative.ofAdd a) := by
  have hcard : Nat.card φ.range = Nat.card F := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact Nat.card_congr Multiplicative.toAdd
  obtain ⟨_, ⟨a, rfl⟩, ha1, hax⟩ := exists_ne_one_commute (R := φ.range)
    (by rintro _ ⟨a, rfl⟩; exact hφP a) (by rw [hcard]; exact hF) hx
  refine ⟨Multiplicative.toAdd a, fun h0 => ha1 ?_, hax⟩
  rw [show a = 1 from Multiplicative.toAdd.injective (by rw [h0]; rfl), map_one]

theorem card_range_le_two_of_commute [Finite S] {F M : Type} [AddCommGroup F] [AddCommGroup M]
    {P : Subgroup S} (ψ : Multiplicative F →* S) (hψP : ∀ a, ψ a ∈ P) (f : F →+ M) {x : S}
    (hx : (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P ≤ 2)
    (hf : ∀ t, ψ (Multiplicative.ofAdd t) * x = x * ψ (Multiplicative.ofAdd t) → f t = 0) :
    Nat.card (AddMonoidHom.toMultiplicative f).range ≤ 2 := by
  set C := Subgroup.centralizer ({x} : Set S) with hC
  have hrange : ψ.range ≤ P := by
    rintro _ ⟨a, rfl⟩
    exact hψP a
  have h1 : (C.comap ψ).index ≤ 2 := by
    rw [Subgroup.index_comap]
    calc C.relIndex ψ.range ≤ C.relIndex P :=
          Subgroup.relIndex_le_of_le_right hrange Subgroup.index_ne_zero_of_finite
      _ = (P ⊓ C).relIndex P := by rw [Subgroup.inf_relIndex_left]
      _ ≤ 2 := hx
  have hfin : (C.comap ψ).FiniteIndex :=
    ⟨by rw [Subgroup.index_comap]; exact Subgroup.index_ne_zero_of_finite⟩
  have h2 : C.comap ψ ≤ (AddMonoidHom.toMultiplicative f).ker := by
    intro a ha
    have ha' : ψ a * x = x * ψ a := Subgroup.mem_centralizer_singleton_iff.1 ha
    rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicative_apply_apply,
      hf (Multiplicative.toAdd a) (by simpa using ha'), ofAdd_zero]
  have h3 := Subgroup.index_antitone h2
  rw [Subgroup.index_ker] at h3
  omega

theorem card_range_toMultiplicative_of_surjective {F M : Type} [AddCommGroup F] [AddCommGroup M]
    {f : F →+ M} (hf : Function.Surjective f) :
    Nat.card (AddMonoidHom.toMultiplicative f).range = Nat.card M := by
  rw [(MonoidHom.range_eq_top (f := AddMonoidHom.toMultiplicative f)).2 hf, Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

theorem centralIndex_of_le {G : Type} [Group G] [Finite G] {C U : Subgroup G} (hUC : U ≤ C)
    (hU : IsSylowTwoOf U C)
    (h : ∀ x ∈ U, (U ⊓ Subgroup.centralizer ({x} : Set G)).relIndex U ≤ 2 →
      x ∈ Subgroup.centralizer (U : Set G)) : CentralIndex ↥C := by
  refine centralIndex_of_sylow (Setup.X6.isSylowTwoOf_subgroupOf_top hU) fun x hx hidx => ?_
  have hmap : (U.subgroupOf C ⊓ Subgroup.centralizer ({x} : Set ↥C)).map C.subtype =
      U ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨hy'U, hy'x⟩ := Subgroup.mem_inf.1 hy'
      refine Subgroup.mem_inf.2 ⟨hy'U, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy'x ⊢
      exact congrArg Subtype.val hy'x
    · intro hy
      obtain ⟨hyU, hyx⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx
      refine ⟨⟨y, hUC hyU⟩, Subgroup.mem_inf.2 ⟨hyU, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hyx
  have hmap2 : (U.subgroupOf C).map C.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUC
  have hidx' : (U ⊓ Subgroup.centralizer ({(x : G)} : Set G)).relIndex U ≤ 2 := by
    have e := Subgroup.relIndex_map_map_of_injective
      (U.subgroupOf C ⊓ Subgroup.centralizer ({x} : Set ↥C)) (U.subgroupOf C) C.subtype_injective
    rw [hmap, hmap2] at e
    rw [e]
    exact hidx
  have h1 := h x hx hidx'
  refine Subgroup.mem_centralizer_iff.2 fun y hy => Subtype.ext ?_
  exact Subgroup.mem_centralizer_iff.1 h1 y hy

theorem card_range_le_two_of_commute' [Finite S] {F M : Type} [AddCommGroup F] [AddCommGroup M]
    {P : Subgroup S} (φ : ↥P →* Multiplicative F) (hφ : Function.Surjective φ) (f : F →+ M)
    {x : S} (hx : (P ⊓ Subgroup.centralizer ({x} : Set S)).relIndex P ≤ 2)
    (hf : ∀ y : P, (y : S) * x = x * y → f (Multiplicative.toAdd (φ y)) = 0) :
    Nat.card (AddMonoidHom.toMultiplicative f).range ≤ 2 := by
  set C := (Subgroup.centralizer ({x} : Set S)).subgroupOf P with hC
  have h1 : C.index ≤ 2 := by
    rw [hC, ← Subgroup.relIndex, ← Subgroup.inf_relIndex_left]
    exact hx
  have hfin : C.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  set g := (AddMonoidHom.toMultiplicative f).comp φ with hg
  have h2 : C ≤ g.ker := by
    intro y hy
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply,
      hf y hy, ofAdd_zero]
  have h3 := Subgroup.index_antitone h2
  rw [Subgroup.index_ker] at h3
  have h4 : g.range = (AddMonoidHom.toMultiplicative f).range := by
    rw [hg, MonoidHom.range_comp, (MonoidHom.range_eq_top (f := φ)).2 hφ, ← MonoidHom.range_eq_map]
  rw [h4] at h3
  omega

theorem conj_eq_of_commutator {G : Type*} [Group G] {g h c : G} (hc : ⁅g, h⁆ = c) :
    MulAut.conj g h = c * h := by
  rw [MulAut.conj_apply, ← hc, commutatorElement_def]
  group

theorem conj_eq_of_commutator' {G : Type*} [Group G] {g h c : G} (hc : ⁅g, h⁆ = c) :
    MulAut.conj h g = c⁻¹ * g := by
  rw [MulAut.conj_apply, ← hc, commutatorElement_def]
  group

theorem conj_eq_of_commute {G : Type*} [Group G] {g h : G} (hc : Commute g h) :
    MulAut.conj g h = h := by
  rw [MulAut.conj_apply, hc.eq, mul_inv_cancel_right]

end CFSG.Quasithin.H13.NQCat.LieCentral
