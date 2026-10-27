module

public import CFSG.LocalAnalysis.SteinbergBVA7TransvectionCenters
public import CFSG.Quasithin.SteinbergBNA7Transvection
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def transvectionSet (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
    Set (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
  {t | t ∈ N ∧ IsBinaryTransvection t}

@[expose] def HasCenterFourGroup (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
    Prop :=
  ∃ (u : V) (f g : Dual (ZMod 2) V), u ≠ 0 ∧ LinearIndependent (ZMod 2) ![f, g] ∧ f u = 0 ∧
    g u = 0 ∧ ∃ Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (Q : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) =
        {n : LinearMap.GeneralLinearGroup (ZMod 2) V | ∃ h ∈ Submodule.span (ZMod 2) {f, g},
          (n : Module.End (ZMod 2) V) = LinearMap.id + h.smulRight u} ∧
      Q ≤ N ∧ Nat.card Q = 4 ∧ ∀ n ∈ Q, n ≠ 1 → IsBinaryTransvection n

namespace PairingForm

open BinaryTransvection

theorem mem_transvectionSet {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {t : LinearMap.GeneralLinearGroup (ZMod 2) V} :
    t ∈ transvectionSet N ↔ t ∈ N ∧ IsBinaryTransvection t :=
  Iff.rfl

theorem zmodTwo_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem exists_unit_eq_id_add_smulRight {u : V} {f : Dual (ZMod 2) V} (hfu : f u = 0) :
    ∃ n : LinearMap.GeneralLinearGroup (ZMod 2) V,
      (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u := by
  have h : (LinearMap.id + f.smulRight u : Module.End (ZMod 2) V) *
      (LinearMap.id + f.smulRight u) = 1 := by
    rw [id_add_smulRight_mul hfu, BinaryTransvection.add_self_eq_zero, LinearMap.zero_smulRight,
      add_zero]
    rfl
  exact ⟨⟨_, _, h, h⟩, rfl⟩

theorem eq_of_id_add_smulRight_eq_same {u : V} (hu : u ≠ 0) {f g : Dual (ZMod 2) V}
    (h : (LinearMap.id + f.smulRight u : Module.End (ZMod 2) V) =
      LinearMap.id + g.smulRight u) : f = g := by
  have h' : f.smulRight u = g.smulRight u := add_left_cancel h
  ext x
  exact smul_left_injective (ZMod 2) hu (by simpa using LinearMap.congr_fun h' x)

theorem form_apply_eq_of_isometry {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.IsAlt)
    (hnd : β.Nondegenerate) {n : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hn : ∀ x y, β ((n : Module.End (ZMod 2) V) x) ((n : Module.End (ZMod 2) V) y) = β x y)
    {u : V} {h : Dual (ZMod 2) V} (hu : u ≠ 0) (hh : h ≠ 0)
    (hhn : (n : Module.End (ZMod 2) V) = LinearMap.id + h.smulRight u) (x : V) :
    β u x = h x := by
  obtain ⟨y, hy⟩ := exists_eq_one_of_ne_zero hh
  have hker : ∀ z, h z = 0 → β u z = 0 := by
    intro z hz
    have := hn z y
    rw [hhn] at this
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, hz, hy,
      zero_smul, add_zero, one_smul, map_add] at this
    rw [Quasithin.SteinbergBN.isAlt_apply_comm hβ]
    exact add_eq_left.1 this
  obtain ⟨z, hz⟩ : ∃ z, β u z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (hnd.1 u hcon)
  have hz1 : h z = 1 := zmodTwo_eq_one_of_ne_zero fun h0 => hz (hker z h0)
  rcases zmodTwo_eq_zero_or_eq_one (h x) with hx | hx
  · rw [hx, hker x hx]
  · have hxz : h (x + z) = 0 := by
      rw [map_add, hx, hz1]
      rfl
    have hsum := hker _ hxz
    rw [map_add, zmodTwo_eq_one_of_ne_zero hz] at hsum
    rw [hx]
    have key : ∀ a : ZMod 2, a + 1 = 0 → a = 1 := by decide
    exact key _ hsum

theorem spans_of_irreducible [FiniteDimensional (ZMod 2) V] (hV : 2 ≤ finrank (ZMod 2) V)
    {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure (transvectionSet N))
    {v : LinearMap.GeneralLinearGroup (ZMod 2) V → V}
    {φ : LinearMap.GeneralLinearGroup (ZMod 2) V → Dual (ZMod 2) V}
    (hvφ : ∀ t ∈ transvectionSet N, v t ≠ 0 ∧ φ t ≠ 0 ∧ φ t (v t) = 0 ∧
      (t : Module.End (ZMod 2) V) = LinearMap.id + (φ t).smulRight (v t)) :
    Submodule.span (ZMod 2) (v '' transvectionSet N) = ⊤ ∧
      Submodule.span (ZMod 2) (φ '' transvectionSet N) = ⊤ := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) := Finite.of_injective
    (fun u : LinearMap.GeneralLinearGroup (ZMod 2) V => (u : Module.End (ZMod 2) V))
    Units.val_injective
  have hTfin : (transvectionSet N).Finite := Set.toFinite _
  set D := hTfin.toFinset with hD
  have hDT : (D : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) = transvectionSet N :=
    hTfin.coe_toFinset
  have hmemD : ∀ t, t ∈ D ↔ t ∈ transvectionSet N := fun t => hTfin.mem_toFinset
  have hDne : D.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hN : N = ⊥ := by
      rw [hgen, ← hDT, hne, Finset.coe_empty, Subgroup.closure_empty]
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    rcases hirr (Submodule.span (ZMod 2) {x}) (fun n hn u hu => by
        rw [hN, Subgroup.mem_bot] at hn
        rw [hn]
        exact hu) with h | h
    · exact hx (Submodule.span_singleton_eq_bot.1 h)
    · have := finrank_span_singleton (K := ZMod 2) hx
      rw [h, finrank_top] at this
      omega
  have hrank : ∀ t ∈ D,
      finrank (ZMod 2) (LinearMap.range ((t : V →ₗ[ZMod 2] V) - 1)) = 1 := by
    intro t ht
    obtain ⟨hvt, hφt, -, htv⟩ := hvφ t ((hmemD t).1 ht)
    rw [htv, show (1 : Module.End (ZMod 2) V) = LinearMap.id from rfl, add_sub_cancel_left]
    exact finrank_range_smulRight hvt hφt
  have hvφ' : ∀ t ∈ D, ∀ x, ((t : V →ₗ[ZMod 2] V) - 1) x = φ t x • v t := by
    intro t ht x
    obtain ⟨-, -, -, htv⟩ := hvφ t ((hmemD t).1 ht)
    rw [htv, show (1 : Module.End (ZMod 2) V) = LinearMap.id from rfl, add_sub_cancel_left,
      LinearMap.smulRight_apply]
  have hirrD : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ Subgroup.closure (D : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)),
        ∀ u ∈ U, (n : V →ₗ[ZMod 2] V) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hirr U fun n hn => hU n ?_
    rw [hDT, ← hgen]
    exact hn
  obtain ⟨hspanv, hspanφ, -⟩ :=
    (CFSG.QuasithinUnique.rank_one_generator_chain_irreducibility_criterion D hDne hrank v φ
      (fun t ht => (hvφ t ((hmemD t).1 ht)).1) (fun t ht => (hvφ t ((hmemD t).1 ht)).2.1)
      hvφ').1 hirrD
  rw [hDT] at hspanv hspanφ
  exact ⟨hspanv, hspanφ⟩

theorem exists_form_of_pairing [FiniteDimensional (ZMod 2) V]
    {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hgen : N = Subgroup.closure (transvectionSet N))
    {v : LinearMap.GeneralLinearGroup (ZMod 2) V → V}
    {φ : LinearMap.GeneralLinearGroup (ZMod 2) V → Dual (ZMod 2) V}
    (hvφ : ∀ t ∈ transvectionSet N, v t ≠ 0 ∧ φ t ≠ 0 ∧ φ t (v t) = 0 ∧
      (t : Module.End (ZMod 2) V) = LinearMap.id + (φ t).smulRight (v t))
    (hspanv : Submodule.span (ZMod 2) (v '' transvectionSet N) = ⊤)
    (hspanφ : Submodule.span (ZMod 2) (φ '' transvectionSet N) = ⊤)
    (hpair : ∀ s ∈ transvectionSet N, ∀ t ∈ transvectionSet N, φ s (v t) = φ t (v s)) :
    ∃ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
      N ≤ Quasithin.SteinbergBN.isometryGroup β := by
  set D := transvectionSet N with hD
  set A : (↥D →₀ ZMod 2) →ₗ[ZMod 2] V :=
    Finsupp.linearCombination (ZMod 2) (fun t : ↥D => v t) with hA
  set B : (↥D →₀ ZMod 2) →ₗ[ZMod 2] Dual (ZMod 2) V :=
    Finsupp.linearCombination (ZMod 2) (fun t : ↥D => φ t) with hB
  have hAsurj : LinearMap.range A = ⊤ := by
    rw [hA, Finsupp.range_linearCombination, ← Set.image_eq_range, hspanv]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine LinearMap.ext_on hspanv ?_
    rintro _ ⟨s, hs, rfl⟩
    have h1 : B c (v s) = φ s (A c) := by
      rw [← Dual.eval_apply (ZMod 2) V (v s) (B c), hA, hB, Finsupp.apply_linearCombination,
        Finsupp.apply_linearCombination]
      congr 2
      funext t
      simp only [Function.comp_apply, Dual.eval_apply]
      exact (hpair s hs t t.2).symm
    rw [h1, hc, map_zero, LinearMap.zero_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A hAsurj
  set L : V →ₗ[ZMod 2] Dual (ZMod 2) V := B ∘ₗ g with hL
  have hLA : ∀ c, L (A c) = B c := by
    intro c
    have hmem : g (A c) - c ∈ LinearMap.ker A := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hg, LinearMap.id_apply, sub_self]
    have := hker hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  have hLv : ∀ t ∈ D, L (v t) = φ t := by
    intro t ht
    have := hLA (Finsupp.single ⟨t, ht⟩ 1)
    rw [hA, hB, Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul,
      one_smul] at this
    exact this
  have hflip : L = L.flip := by
    refine LinearMap.ext_on hspanv ?_
    rintro _ ⟨s, hs, rfl⟩
    refine LinearMap.ext_on hspanv ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.flip_apply, hLv s hs, hLv t ht]
    exact hpair s hs t ht
  have hsymm : ∀ x y, L x y = L y x := fun x y => by
    have := LinearMap.congr_fun (LinearMap.congr_fun hflip x) y
    rwa [LinearMap.flip_apply] at this
  have halt : ∀ x, L x x = 0 := by
    intro x
    have hx : x ∈ Submodule.span (ZMod 2) (v '' D) := by
      rw [hspanv]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hLv t ht]
      exact (hvφ t ht).2.2.1
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add L, LinearMap.add_apply, map_add (L x), map_add (L y), hx, hy, hsymm y x,
        zero_add, add_zero, CharTwo.add_self_eq_zero]
    | smul a x _ hx =>
      rw [map_smul L, LinearMap.smul_apply, map_smul (L x), hx, smul_zero, smul_zero]
  have hright : ∀ y, (∀ x, L x y = 0) → y = 0 := by
    intro y hy
    have hφy : ∀ ψ ∈ Submodule.span (ZMod 2) (φ '' D), ψ y = 0 := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨t, ht, rfl⟩ := hψ
        rw [← hLv t ht]
        exact hy (v t)
      | zero => rfl
      | add ψ ψ' _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
      | smul a ψ _ h => rw [LinearMap.smul_apply, h, smul_zero]
    rw [hspanφ] at hφy
    exact (Module.forall_dual_apply_eq_zero_iff (ZMod 2) y).1 fun ψ => hφy ψ Submodule.mem_top
  have hleft : ∀ x, (∀ y, L x y = 0) → x = 0 := fun x hx =>
    hright x fun y => (hsymm y x).trans (hx y)
  have hLalt : LinearMap.BilinForm.IsAlt L := halt
  refine ⟨L, hLalt, And.intro hleft hright, ?_⟩
  rw [hgen, Subgroup.closure_le]
  intro t ht
  have ht' : t = Quasithin.SteinbergBN.transv hLalt (v t) := by
    refine Units.ext (LinearMap.ext fun x => ?_)
    rw [Quasithin.SteinbergBN.transv_apply, (hvφ t ht).2.2.2, LinearMap.add_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, hLv t ht]
  rw [SetLike.mem_coe, ht']
  exact Quasithin.SteinbergBN.transv_mem_isometryGroup hLalt (v t)

theorem hasCenterFourGroup_of_one_way {N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {u w : V} {f g : Dual (ZMod 2) V} (hu : u ≠ 0) (hf : f ∈ centerFunctionals N u)
    (hfw : f w = 1) (hg : g ∈ centerFunctionals N w) (hg0 : g ≠ 0) (hgu : g u = 0) :
    HasCenterFourGroup N := by
  classical
  have hgu' : g ∈ centerFunctionals N u := mem_of_incidence hf hfw hg hgu
  have hfu : f u = 0 := (mem_centerFunctionals.1 hf).1
  have hgw : g w = 0 := (mem_centerFunctionals.1 hg).1
  set S := Submodule.span (ZMod 2) ({f, g} : Set (Dual (ZMod 2) V)) with hS
  have hSF : S ≤ centerFunctionals N u := by
    rw [hS, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hf, hgu'⟩
  have hSu : ∀ h ∈ S, h u = 0 := fun h hh => (mem_centerFunctionals.1 (hSF hh)).1
  have hli : LinearIndependent (ZMod 2) ![f, g] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := LinearMap.congr_fun hab w
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hfw, hgw, smul_eq_mul, mul_one,
      mul_zero, add_zero, LinearMap.zero_apply] at h1
    subst h1
    refine ⟨rfl, ?_⟩
    rw [zero_smul, zero_add] at hab
    rcases smul_eq_zero.1 hab with hb | hb
    · exact hb
    · exact absurd hb hg0
  let Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    { carrier := {n | ∃ h ∈ S, (n : Module.End (ZMod 2) V) = LinearMap.id + h.smulRight u}
      mul_mem' := by
        rintro a b ⟨h, hh, ha⟩ ⟨h', hh', hb⟩
        exact ⟨h + h', S.add_mem hh hh', by
          rw [Units.val_mul, ha, hb, id_add_smulRight_mul (hSu h hh)]⟩
      one_mem' := ⟨0, S.zero_mem, by ext x; simp⟩
      inv_mem' := by
        rintro a ⟨h, hh, ha⟩
        exact ⟨h, hh, by rw [inv_eq_of_val_eq (hSu h hh) ha, ha]⟩ }
  have hQN : Q ≤ N := by
    intro n hn
    obtain ⟨h, hh, hnh⟩ := hn
    obtain ⟨-, m, hm, hmh⟩ := mem_centerFunctionals.1 (hSF hh)
    have : n = m := Units.ext (hnh.trans hmh.symm)
    rw [this]
    exact hm
  have hcard : Nat.card Q = 4 := by
    have hfin : finrank (ZMod 2) S = 2 := by
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
      exact this
    have hex : ∀ h : S, ∃ n : LinearMap.GeneralLinearGroup (ZMod 2) V,
        (n : Module.End (ZMod 2) V) = LinearMap.id + (h : Dual (ZMod 2) V).smulRight u :=
      fun h => exists_unit_eq_id_add_smulRight (hSu h h.2)
    choose ψ hψ using hex
    have hψQ : ∀ h, ψ h ∈ Q := fun h => ⟨h, h.2, hψ h⟩
    have hbij : Function.Bijective (fun h : S => (⟨ψ h, hψQ h⟩ : Q)) := by
      constructor
      · intro h h' hhh
        have := congrArg (fun n : Q => ((n : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          Module.End (ZMod 2) V)) hhh
        simp only [hψ] at this
        exact Subtype.ext (eq_of_id_add_smulRight_eq_same hu this)
      · rintro ⟨n, h, hh, hn⟩
        exact ⟨⟨h, hh⟩, Subtype.ext (Units.ext ((hψ _).trans hn.symm))⟩
    have : Module.Finite (ZMod 2) S := FiniteDimensional.span_of_finite (ZMod 2) (Set.toFinite _)
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Module.natCard_eq_pow_finrank (K := ZMod 2),
      hfin, Nat.card_zmod]
    norm_num
  have hntriv : ∀ n ∈ Q, n ≠ 1 → IsBinaryTransvection n := by
    intro n hn hn1
    obtain ⟨h, hh, hnh⟩ := hn
    refine ⟨u, h, hu, fun h0 => hn1 (Units.ext ?_), hSu h hh, hnh⟩
    ext x
    simp [hnh, h0]
  exact ⟨u, f, g, hu, hli, hfu, hgu, Q, rfl, hQN, hcard, hntriv⟩

end PairingForm

open BinaryTransvection PairingForm in
theorem binary_transvection_pairing_form_dichotomy [FiniteDimensional (ZMod 2) V]
    (hV : 2 ≤ finrank (ZMod 2) V) (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure (transvectionSet N))
    (v : LinearMap.GeneralLinearGroup (ZMod 2) V → V)
    (φ : LinearMap.GeneralLinearGroup (ZMod 2) V → Dual (ZMod 2) V)
    (hvφ : ∀ t ∈ transvectionSet N, v t ≠ 0 ∧ φ t ≠ 0 ∧ φ t (v t) = 0 ∧
      (t : Module.End (ZMod 2) V) = LinearMap.id + (φ t).smulRight (v t)) :
    ((∃ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
        N ≤ Quasithin.SteinbergBN.isometryGroup β) ↔
      ∀ s ∈ transvectionSet N, ∀ t ∈ transvectionSet N, φ s (v t) = φ t (v s)) ∧
    ((∀ s ∈ transvectionSet N, ∀ t ∈ transvectionSet N, φ s (v t) = φ t (v s)) →
      ∃! β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
        N ≤ Quasithin.SteinbergBN.isometryGroup β) ∧
    (∀ (β : LinearMap.BilinForm (ZMod 2) V) (hβ : β.IsAlt), β.Nondegenerate →
      N ≤ Quasithin.SteinbergBN.isometryGroup β →
        (∀ t ∈ transvectionSet N, ∀ x, β (v t) x = φ t x) ∧
        ∀ t ∈ transvectionSet N, t = Quasithin.SteinbergBN.transv hβ (v t)) ∧
    (¬ (∀ s ∈ transvectionSet N, ∀ t ∈ transvectionSet N, φ s (v t) = φ t (v s)) →
      HasCenterFourGroup N) ∧
    (HasCenterFourGroup N → ¬ ∃ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧
      β.Nondegenerate ∧ N ≤ Quasithin.SteinbergBN.isometryGroup β) := by
  obtain ⟨hspanv, hspanφ⟩ := spans_of_irreducible hV hirr hgen hvφ
  have hform : ∀ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt → β.Nondegenerate →
      N ≤ Quasithin.SteinbergBN.isometryGroup β →
        ∀ t ∈ transvectionSet N, ∀ x, β (v t) x = φ t x := by
    intro β hβ hnd hNβ t ht x
    obtain ⟨hvt, hφt, -, htv⟩ := hvφ t ht
    exact form_apply_eq_of_isometry hβ hnd (hNβ (mem_transvectionSet.1 ht).1) hvt hφt htv x
  have huniq : ∀ β β' : LinearMap.BilinForm (ZMod 2) V,
      (β.IsAlt ∧ β.Nondegenerate ∧ N ≤ Quasithin.SteinbergBN.isometryGroup β) →
      (β'.IsAlt ∧ β'.Nondegenerate ∧ N ≤ Quasithin.SteinbergBN.isometryGroup β') → β = β' := by
    rintro β β' ⟨hβ, hnd, hNβ⟩ ⟨hβ', hnd', hNβ'⟩
    refine LinearMap.ext_on hspanv ?_
    rintro _ ⟨t, ht, rfl⟩
    ext x
    rw [hform β hβ hnd hNβ t ht x, hform β' hβ' hnd' hNβ' t ht x]
  refine ⟨⟨?_, exists_form_of_pairing hgen hvφ hspanv hspanφ⟩, fun hpair => ?_, ?_, ?_, ?_⟩
  · rintro ⟨β, hβ, hnd, hNβ⟩ s hs t ht
    rw [← hform β hβ hnd hNβ s hs, ← hform β hβ hnd hNβ t ht,
      Quasithin.SteinbergBN.isAlt_apply_comm hβ]
  · obtain ⟨β, hP⟩ := exists_form_of_pairing hgen hvφ hspanv hspanφ hpair
    exact ⟨β, hP, fun β' hP' => huniq β' β hP' hP⟩
  · intro β hβ hnd hNβ
    refine ⟨hform β hβ hnd hNβ, fun t ht => Units.ext (LinearMap.ext fun x => ?_)⟩
    rw [Quasithin.SteinbergBN.transv_apply, (hvφ t ht).2.2.2, LinearMap.add_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, hform β hβ hnd hNβ t ht x]
  · intro hnot
    push Not at hnot
    obtain ⟨s, hs, t, ht, hst⟩ := hnot
    obtain ⟨hvs, hφs, hφvs, hsv⟩ := hvφ s hs
    obtain ⟨hvt, hφt, hφvt, htv⟩ := hvφ t ht
    have hFs : φ s ∈ centerFunctionals N (v s) :=
      mem_centerFunctionals.2 ⟨hφvs, s, (mem_transvectionSet.1 hs).1, hsv⟩
    have hFt : φ t ∈ centerFunctionals N (v t) :=
      mem_centerFunctionals.2 ⟨hφvt, t, (mem_transvectionSet.1 ht).1, htv⟩
    rcases zmodTwo_eq_zero_or_eq_one (φ s (v t)) with h1 | h1
    · have h2 : φ t (v s) = 1 := zmodTwo_eq_one_of_ne_zero fun h => hst (h1.trans h.symm)
      exact hasCenterFourGroup_of_one_way hvt hFt h2 hFs hφs h1
    · have h2 : φ t (v s) = 0 := zmodTwo_eq_zero_of_ne_one fun h => hst (h1.trans h.symm)
      exact hasCenterFourGroup_of_one_way hvs hFs h1 hFt hφt h2
  · rintro ⟨u, f, g, hu, hli, hfu, hgu, Q, hQ, hQN, -, -⟩ ⟨β, hβ, hnd, hNβ⟩
    have hf0 : f ≠ 0 := by simpa using hli.ne_zero 0
    have hg0 : g ≠ 0 := by simpa using hli.ne_zero 1
    have hfg : f ≠ g := by simpa using hli.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
    have key : ∀ h ∈ ({f, g} : Set (Dual (ZMod 2) V)), h ≠ 0 → h u = 0 → ∀ x, β u x = h x := by
      intro h hh h0 hhu x
      obtain ⟨n, hn⟩ := exists_unit_eq_id_add_smulRight hhu
      have hnQ : n ∈ Q := by
        rw [← SetLike.mem_coe, hQ]
        exact ⟨h, Submodule.subset_span hh, hn⟩
      exact form_apply_eq_of_isometry hβ hnd (hNβ (hQN hnQ)) hu h0 hn x
    apply hfg
    ext x
    rw [← key f (by simp) hf0 hfu x, key g (by simp) hg0 hgu x]

end CFSG.LocalAnalysis.SteinbergBV
