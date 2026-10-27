module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFrattiniGeneratorBound

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup
open scoped Pointwise commutatorElement

theorem exists_generators_card_frattini {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) : ∃ (n : ℕ) (g : Fin n → R), Nat.card (R ⧸ frattini R) = p ^ n ∧
      closure (Set.range g) = ⊤ := by
  obtain ⟨-, -, -, -, n, hn, ⟨e⟩⟩ := CFSG.GroupTheory.frattini_elementary_quotient hR
  set v : Fin n → R ⧸ frattini R := fun i => Additive.toMul (e.symm (Pi.single i 1)) with hv
  have hgen : closure (Set.range v) = ⊤ := by
    apply Subgroup.toAddSubgroup.injective
    rw [Subgroup.toAddSubgroup_closure, OrderIso.map_top]
    have hpre : (⇑Additive.toMul ⁻¹' Set.range v) =
        Set.range fun i : Fin n => e.symm (Pi.single i 1) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_range, hv]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Additive.toMul.injective hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hpre, Set.range_comp' e.symm (fun i : Fin n => (Pi.single i (1 : ZMod p))),
      show (⇑e.symm) = ⇑(e.symm.toAddMonoidHom) from rfl, ← AddMonoidHom.map_closure]
    have htop : AddSubgroup.closure (Set.range fun i : Fin n => (Pi.single i (1 : ZMod p))) =
        ⊤ := by
      rw [eq_top_iff]
      intro w _
      rw [← Finset.univ_sum_single w]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      have : (Pi.single i (w i) : Fin n → ZMod p) = (w i).val • Pi.single i 1 := by
        rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      rw [this]
      exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    rw [htop, AddSubgroup.map_top_of_surjective _ e.symm.surjective]
  refine ⟨n, fun i => (v i).out, hn, ?_⟩
  apply CFSG.LocalAnalysis.ComponentInitial.frattini_generator_lifting
  convert hgen
  ext w
  simp only [Set.mem_image, Set.mem_range, QuotientGroup.mk'_apply]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (QuotientGroup.out_eq' (v i)).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, QuotientGroup.out_eq' (v i)⟩

theorem normal_extraspecial_irreducible_central_product {p : ℕ} (hp : p.Prime) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) (D : Subgroup P) [D.Normal]
    (hD : CFSG.IsExtraspecialPGroup p D) (H : Subgroup (MulAut P))
    (hHD : ∀ h ∈ H, ∀ x ∈ D, h x ∈ D)
    (hirr : ∀ X : Subgroup P, (center D).map D.subtype ≤ X → X ≤ D →
      (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = (center D).map D.subtype ∨ X = D) :
    (D : Set P) * (centralizer (D : Set P) : Set P) = Set.univ ∧
      ⁅D, centralizer (D : Set P)⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hDp, hDcomm, hDfrat, hDcard⟩ := hD
  set Zc := (center D).map D.subtype with hZcdef
  have hZcD : Zc ≤ D := map_subtype_le _
  have hZcc : Nat.card Zc = p := by
    rw [hZcdef, card_map_of_injective D.subtype_injective, hDcard]
  have hZcn : Zc.Normal :=
    CFSG.LocalAnalysis.GorensteinLyons.map_subtype_normal_of_characteristic D (center D)
  have hZcmem : ∀ z (hz : z ∈ Zc), (⟨z, hZcD hz⟩ : D) ∈ center D := by
    rintro _ ⟨c, hc, rfl⟩
    exact hc
  have hDZ : ¬ D ≤ Zc := by
    intro h
    have hctop : center D = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hZcmem x (h x.2)
    have hcb : center D = ⊥ := by
      rw [← hDcomm, eq_bot_iff, _root_.commutator_def, commutator_le]
      intro a _ b _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hctop ▸ mem_top b) a)
    rw [hcb, card_bot] at hDcard
    exact hp.one_lt.ne hDcard
  have hQp : IsPGroup p (P ⧸ Zc) := hP.to_quotient Zc
  have := hQp.isNilpotent
  have hDbar : (D.map (QuotientGroup.mk' Zc)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Zc)
  have hDbar1 : D.map (QuotientGroup.mk' Zc) ≠ ⊥ := by
    intro h
    apply hDZ
    rw [← QuotientGroup.ker_mk' Zc]
    exact (Subgroup.map_eq_bot_iff _).mp h
  obtain ⟨⟨_, ⟨d, hd, rfl⟩, hdZ⟩, hd1⟩ :=
    ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hDbar1)
  set X := D ⊓ (center (P ⧸ Zc)).comap (QuotientGroup.mk' Zc) with hXdef
  have hZX : Zc ≤ X := fun z hz => ⟨hZcD hz, by
    show QuotientGroup.mk' Zc z ∈ center (P ⧸ Zc)
    rw [show QuotientGroup.mk' Zc z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact one_mem _⟩
  have hHZ : ∀ h ∈ H, ∀ z ∈ Zc, h z ∈ Zc := by
    intro h hh z hz
    have hhz : h z ∈ D := hHD h hh z (hZcD hz)
    refine ⟨⟨h z, hhz⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    have hy' : h⁻¹ (y : P) ∈ D := hHD h⁻¹ (H.inv_mem hh) y y.2
    have hzc := congrArg Subtype.val (mem_center_iff.mp (hZcmem z hz) ⟨h⁻¹ (y : P), hy'⟩)
    change h⁻¹ (y : P) * z = z * h⁻¹ (y : P) at hzc
    show (y : P) * h z = h z * y
    have hyy : h (h⁻¹ (y : P)) = y := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    calc (y : P) * h z = h (h⁻¹ (y : P)) * h z := by rw [hyy]
      _ = h (h⁻¹ (y : P) * z) := (map_mul h _ _).symm
      _ = h (z * h⁻¹ (y : P)) := by rw [hzc]
      _ = h z * h (h⁻¹ (y : P)) := map_mul h _ _
      _ = h z * y := by rw [hyy]
  have hXinv : ∀ h ∈ H, ∀ x ∈ X, h x ∈ X := by
    intro h hh x hx
    refine ⟨hHD h hh x hx.1, mem_center_iff.mpr fun q' => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Zc q'
    have hxc := mem_center_iff.mp hx.2 (QuotientGroup.mk' Zc (h⁻¹ y))
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hxc
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hyy : h (h⁻¹ y) = y := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have e : (y * h x)⁻¹ * (h x * y) = h ((h⁻¹ y * x)⁻¹ * (x * h⁻¹ y)) := by
      rw [map_mul, map_inv, map_mul, map_mul, hyy]
    rw [e]
    exact hHZ h hh _ hxc
  have hXZ : X ≠ Zc := by
    intro h
    apply hd1
    have hdX : d ∈ X := ⟨hd, hdZ⟩
    rw [h] at hdX
    exact Subtype.ext ((QuotientGroup.eq_one_iff d).mpr hdX)
  have hXD : X = D := (hirr X hZX inf_le_left hXinv).resolve_left hXZ
  have htriv : ∀ x : P, ∀ a ∈ D, a⁻¹ * (x * a * x⁻¹) ∈ Zc := by
    intro x a ha
    have haX : a ∈ X := hXD ▸ ha
    have hc := mem_center_iff.mp haX.2 (QuotientGroup.mk' Zc x⁻¹)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hc
    have e : (x⁻¹ * a)⁻¹ * (a * x⁻¹) = a⁻¹ * (x * a * x⁻¹) := by group
    rwa [e] at hc
  obtain ⟨n, g, hgcard, hgen⟩ := exists_generators_card_frattini hDp
  rw [hDfrat] at hgcard
  have hθmem : ∀ (a : D) (i : Fin n), (g i)⁻¹ * (a * g i * a⁻¹) ∈ center D := fun a i => by
    have e : (g i)⁻¹ * (a * g i * a⁻¹) = ⁅(g i)⁻¹, a⁆ := by
      rw [commutatorElement_def, inv_inv]
      group
    have h := commutator_mem_commutator (mem_top (g i)⁻¹) (mem_top a)
    rw [← _root_.commutator_def, hDcomm] at h
    rw [e]
    exact h
  let θ : D →* (Fin n → center D) := MonoidHom.mk'
    (fun a i => ⟨(g i)⁻¹ * (a * g i * a⁻¹), hθmem a i⟩) fun a b => by
      funext i
      apply Subtype.ext
      have hc : ∀ y : D, ((g i)⁻¹ * (b * g i * b⁻¹)) * y = y * ((g i)⁻¹ * (b * g i * b⁻¹)) :=
        fun y => (mem_center_iff.mp (hθmem b i) y).symm
      show (g i)⁻¹ * (a * b * g i * (a * b)⁻¹) =
        (g i)⁻¹ * (a * g i * a⁻¹) * ((g i)⁻¹ * (b * g i * b⁻¹))
      calc (g i)⁻¹ * (a * b * g i * (a * b)⁻¹)
          = (g i)⁻¹ * a * g i * (((g i)⁻¹ * (b * g i * b⁻¹)) * a⁻¹) := by group
        _ = (g i)⁻¹ * a * g i * (a⁻¹ * ((g i)⁻¹ * (b * g i * b⁻¹))) := by rw [hc a⁻¹]
        _ = (g i)⁻¹ * (a * g i * a⁻¹) * ((g i)⁻¹ * (b * g i * b⁻¹)) := by group
  have hθker : θ.ker = center D := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have hcomm : ∀ i, a * g i = g i * a := by
        intro i
        have h1 := congrArg (fun f : Fin n → center D => ((f i : center D) : D)) h
        change (g i)⁻¹ * (a * g i * a⁻¹) = 1 at h1
        have h2 : a * g i * a⁻¹ = g i := by
          calc a * g i * a⁻¹ = g i * ((g i)⁻¹ * (a * g i * a⁻¹)) := by group
            _ = g i := by rw [h1, mul_one]
        calc a * g i = a * g i * a⁻¹ * a := by group
          _ = g i * a := by rw [h2]
      have hcent : a ∈ centralizer (Set.range g) := by
        rw [mem_centralizer_iff]
        rintro _ ⟨i, rfl⟩
        exact (hcomm i).symm
      rw [← centralizer_closure, hgen, coe_top, centralizer_univ] at hcent
      exact hcent
    · intro ha
      funext i
      apply Subtype.ext
      change (g i)⁻¹ * (a * g i * a⁻¹) = 1
      rw [← mem_center_iff.mp ha (g i), mul_inv_cancel_right, inv_mul_cancel]
  have hθsurj : Function.Surjective θ := by
    have h1 := card_ker_mul_card_range θ
    rw [hθker] at h1
    have h2 := card_eq_card_quotient_mul_card_subgroup (center D)
    rw [hgcard] at h2
    have h3 : Nat.card (Fin n → center D) = p ^ n := by rw [Nat.card_fun, hDcard, Nat.card_fin]
    have hrange : Nat.card θ.range = p ^ n := by
      have hpos : 0 < Nat.card (center D) := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [h1, h2, mul_comm]
    rw [← MonoidHom.range_eq_top]
    exact eq_of_le_of_card_ge le_top (by rw [card_top, h3, hrange])
  have hgenP : closure (Set.range fun i => (g i : P)) = D := by
    have himg : (Set.range fun i => (g i : P)) = D.subtype '' Set.range g := by
      ext y
      simp
    rw [himg, ← MonoidHom.map_closure, hgen, ← MonoidHom.range_eq_map, range_subtype]
  have hcentP : ∀ c : P, (∀ i, c * (g i : P) * c⁻¹ = g i) → c ∈ centralizer (D : Set P) := by
    intro c hc
    rw [← hgenP, centralizer_closure, mem_centralizer_iff]
    rintro _ ⟨i, rfl⟩
    calc (g i : P) * c = c * g i * c⁻¹ * c := by rw [hc i]
      _ = c * g i := by group
  have hmul : ∀ x : P, ∃ a ∈ D, ∃ c ∈ centralizer (D : Set P), a * c = x := by
    intro x
    set t : Fin n → center D := fun i => ⟨⟨(g i : P)⁻¹ * (x * g i * x⁻¹),
      hZcD (htriv x _ (g i).2)⟩, hZcmem _ (htriv x _ (g i).2)⟩ with ht
    obtain ⟨a, ha⟩ := hθsurj t
    refine ⟨a, a.2, (a : P)⁻¹ * x, hcentP _ fun i => ?_, by group⟩
    have h1 := congrArg (fun f : Fin n → center D => (((f i : center D) : D) : P)) ha
    change (g i : P)⁻¹ * (a * g i * (a : P)⁻¹) = (g i : P)⁻¹ * (x * g i * x⁻¹) at h1
    have h2 : (a : P) * g i * (a : P)⁻¹ = x * g i * x⁻¹ := mul_left_cancel h1
    calc (a : P)⁻¹ * x * g i * ((a : P)⁻¹ * x)⁻¹ = (a : P)⁻¹ * (x * g i * x⁻¹) * a := by group
      _ = (a : P)⁻¹ * (a * g i * (a : P)⁻¹) * a := by rw [h2]
      _ = g i := by group
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨a, ha, c, hc, rfl⟩ := hmul x
    exact Set.mul_mem_mul ha hc
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro d hd
    rw [mem_centralizer_iff]
    intro c hc
    exact (mem_centralizer_iff.mp hc d hd).symm

end CFSG.RankThree.GroupTheory.SteinbergBM
