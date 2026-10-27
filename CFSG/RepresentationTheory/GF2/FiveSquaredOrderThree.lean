module

public import CFSG.RepresentationTheory.GF2.FiveSquaredGroup
import CFSG.LinearAlgebra.OrthogonalIdempotentsFinrank
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane

public section

namespace CFSG.RepresentationTheory.GF2

open CFSG.RankThree.Classical

section

open Module

theorem four_dvd_finrank_of_fiveGroup_fixedPointFree {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hG : IsPGroup 5 G)
    (hfix : ∀ w : W, (∀ g : G, ρ g w = w) → w = 0) :
    4 ∣ Module.finrank (ZMod 2) W := by
  classical
  letI : MulAction G W :=
    { smul := fun g w => ρ g w
      one_smul := by
        intro w
        change (ρ 1) w = w
        rw [map_one]
        rfl
      mul_smul := by
        intro g h w
        change (ρ (g * h)) w = (ρ g) ((ρ h) w)
        rw [map_mul]
        rfl }
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hmod := hG.card_modEq_card_fixedPoints W
  have hfixSet : MulAction.fixedPoints G W = {0} := by
    ext w
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hw
      exact hfix w fun g => hw g
    · rintro rfl
      exact fun g => map_zero (ρ g)
  have hcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [hcard] at hmod
  have hmod' : 2 ^ Module.finrank (ZMod 2) W ≡ 1 [MOD 5] := by
    simpa [hfixSet] using hmod
  have h2 : ((2 : ZMod 5) ^ Module.finrank (ZMod 2) W) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff (2 ^ Module.finrank (ZMod 2) W) 1 5).2 hmod'
    simpa using h
  have hdvd : orderOf (2 : ZMod 5) ∣ Module.finrank (ZMod 2) W :=
    orderOf_dvd_of_pow_eq_one h2
  have hord : orderOf (2 : ZMod 5) = 4 := by
    have hnot : ¬ (2 : ZMod 5) ^ 2 ^ 1 = 1 := by decide
    have hfin : (2 : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by decide
    have h := orderOf_eq_prime_pow (x := (2 : ZMod 5)) (p := 2) (n := 1) hnot hfin
    norm_num at h
    exact h
  rwa [hord] at hdvd

theorem avgOp_map_of_aut {K V E Γ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Group E] [Fintype E] [Group Γ]
    (ρ : Γ →* Module.End K V) (ρE : E →* Module.End K V)
    (c : MulAut E) (g : Γ)
    (hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹)
    (L : Subgroup E) [Fintype L] [Fintype (L.map c.toMonoidHom)] :
    ρ g * avgOp ρE L * ρ g⁻¹ = avgOp ρE (L.map c.toMonoidHom) := by
  classical
  rw [avgOp_def, avgOp_def]
  have hcard' : Fintype.card (L.map c.toMonoidHom) = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Subgroup.card_map_of_injective c.injective]
  rw [hcard']
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    ρ g * (∑ l : L, ρE l) * ρ g⁻¹ = ∑ l : L, ρ g * ρE l * ρ g⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ l : L, ρE (c l) := by
      exact Finset.sum_congr rfl fun l _ => (hgc l).symm
    _ = ∑ m : L.map c.toMonoidHom, ρE m := by
      exact Fintype.sum_equiv (L.equivMapOfInjective c.toMonoidHom c.injective) _ _
        fun l => rfl

theorem commute_avgOp {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Group E] [Fintype E]
    (ρ : E →* Module.End K V) (D : Subgroup E) [Fintype D] {e : E}
    (h : ∀ d ∈ D, Commute (ρ e) (ρ d)) : Commute (ρ e) (avgOp ρ D) := by
  rw [avgOp_def]
  refine (Commute.sum_right (Finset.univ : Finset D) (fun d : D => ρ (d : E)) (ρ e) ?_).smul_right _
  intro d _
  exact h d d.2

end

end CFSG.RepresentationTheory.GF2

namespace CFSG.RepresentationTheory.GF2

open CFSG.RankThree.Classical
open CFSG.LinearAlgebra

theorem exists_lineIdem_ne_zero_of_nontrivial {E : Type*} {U : Type} [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρE : E →* Module.End (ZMod 2) U)
    (hEcard : Nat.card E = 5 ^ 2) (hexp : ∀ x : E, x ^ 5 = 1)
    (hpK : (5 : ZMod 2) ≠ 0) (hne : ∃ x : E, ρE x ≠ 1) :
    ∃ M : {M : Subgroup E // Nat.card M = 5}, lineIdem ρE 5 (some M) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hsum := sum_lineIdem (K := ZMod 2) (V := U) (ρ := ρE) (p := 5) Nat.prime_five hexp hEcard hpK
  have hnone : lineIdem ρE 5 (none : Option {M : Subgroup E // Nat.card M = 5}) = 1 := by
    have hsum' : (∑ i : Option {M : Subgroup E // Nat.card M = 5},
        lineIdem ρE 5 i) = lineIdem ρE 5 none := by
      rw [Fintype.sum_option]
      simp [h]
    rwa [hsum'] at hsum
  have hEA : avgOp ρE ⊤ = 1 := by simpa [lineIdem] using hnone
  obtain ⟨x, hx⟩ := hne
  have hmul := mul_avgOp (ρ := ρE) (D := ⊤) (g := x) (Subgroup.mem_top x)
  rw [hEA] at hmul
  exact hx (by simpa using hmul)

theorem commute_lineIdem {E : Type*} {U : Type} [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρE : E →* Module.End (ZMod 2) U)
    (hcomm : ∀ e d : E, Commute (ρE e) (ρE d)) (e : E)
    (i : Option {M : Subgroup E // Nat.card M = 5}) :
    Commute (ρE e) (lineIdem ρE 5 i) := by
  classical
  rcases i with _ | ⟨M, hM⟩
  · simpa [lineIdem] using commute_avgOp ρE ⊤ (fun d _ => hcomm e d)
  · have hMcomm := commute_avgOp ρE M (fun d _ => hcomm e d)
    have htopcomm := commute_avgOp ρE ⊤ (fun d _ => hcomm e d)
    simpa [lineIdem] using hMcomm.sub_right htopcomm

theorem conj_lineIdem {Γ E : Type*} {U : Type} [Group Γ] [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Γ →* Module.End (ZMod 2) U) (ρE : E →* Module.End (ZMod 2) U)
    (c : MulAut E) (g : Γ) (hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹)
    {L : Subgroup E} (hL : Nat.card L = 5) :
    ρ g * lineIdem ρE 5 (some ⟨L, hL⟩) * ρ g⁻¹ =
      lineIdem ρE 5 (some ⟨L.map c.toMonoidHom, by
        rw [Subgroup.card_map_of_injective c.injective, hL]⟩) := by
  classical
  have h1 := avgOp_map_of_aut ρ ρE c g hgc L
  have h2 : ρ g * avgOp ρE ⊤ * ρ g⁻¹ = avgOp ρE ⊤ := by
    have hmap_top : (⊤ : Subgroup E).map c.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top_of_surjective c.toMonoidHom]
      exact c.surjective
    have h := avgOp_map_of_aut ρ ρE c g hgc (⊤ : Subgroup E)
    rwa [hmap_top] at h
  simp only [lineIdem]
  rw [mul_sub, sub_mul, h1, h2]

theorem four_dvd_finrank_range_lineIdem {E : Type*} {U : Type} [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρE : E →* Module.End (ZMod 2) U) (hcomm : ∀ e d : E, Commute (ρE e) (ρE d))
    (hexp : ∀ x : E, x ^ 5 = 1) (hEcard : Nat.card E = 25)
    {L : Subgroup E} (hL : Nat.card L = 5) :
    4 ∣ Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some ⟨L, hL⟩))) := by
  classical
  let f := lineIdem ρE 5 (some ⟨L, hL⟩)
  let Wsub : Subrepresentation ρE :=
    { toSubmodule := LinearMap.range f
      apply_mem_toSubmodule := by
        intro e w hw
        obtain ⟨u, rfl⟩ := hw
        refine ⟨ρE e u, ?_⟩
        have h := congrArg (fun k : Module.End (ZMod 2) U => k u)
          (commute_lineIdem ρE hcomm e (some ⟨L, hL⟩)).symm.eq
        simpa [Module.End.mul_apply] using h }
  have hfixW : ∀ w : Wsub.toSubmodule, (∀ e : E, Wsub.toRepresentation e w = w) → w = 0 := by
    rintro ⟨u, hu⟩ hw
    obtain ⟨v, rfl⟩ := hu
    have hw' : ∀ e : E, ρE e (f v) = f v := fun e => congrArg Subtype.val (hw e)
    have htop : avgOp ρE ⊤ (f v) = f v := by
      apply avgOp_apply_of_fixed
      · rw [← Nat.card_eq_fintype_card, Subgroup.card_top, hEcard]
        decide
      · intro e _
        exact hw' e
    have hzero : avgOp ρE ⊤ (f v) = 0 := by
      have hne : (none : Option {M : Subgroup E // Nat.card M = 5}) ≠ some ⟨L, hL⟩ := by simp
      have h : avgOp ρE ⊤ * f = 0 := by
        simpa [f, lineIdem] using lineIdem_mul_of_ne (K := ZMod 2) (V := U) (ρ := ρE)
          (p := 5) Nat.prime_five hexp (by rw [hEcard]; norm_num) (by decide) hne
      have := congrArg (fun k : Module.End (ZMod 2) U => k v) h
      simpa [Module.End.mul_apply] using this
    apply Subtype.ext
    change f v = 0
    rw [← htop, hzero]
  haveI : Finite U := Module.finite_of_finite (ZMod 2)
  have hEisP : IsPGroup 5 E := by
    rw [IsPGroup.iff_card]
    exact ⟨2, by rw [hEcard]; norm_num⟩
  have h4 := four_dvd_finrank_of_fiveGroup_fixedPointFree (ρ := Wsub.toRepresentation) hEisP hfixW
  simpa [Wsub, f] using h4

theorem orbit_line_injective {E : Type*} [Group E]
    (c : MulAut E) (hc3 : c ^ 3 = 1) {L : Subgroup E} (hL : Nat.card L = 5)
    (hfixed : ∀ M : Subgroup E, Nat.card M = 5 → M.map c.toMonoidHom ≠ M) :
    Function.Injective fun i : Fin 3 =>
      (⟨L.map ((c ^ (i : ℕ)).toMonoidHom), by
        rw [Subgroup.card_map_of_injective (c ^ (i : ℕ)).injective, hL]⟩ :
        {M : Subgroup E // Nat.card M = 5}) := by
  have h0 : L.map c.toMonoidHom ≠ L := hfixed L hL
  have h2 : L.map ((c ^ 2).toMonoidHom) ≠ L := by
    intro h
    have hmap := congrArg (fun M : Subgroup E => M.map c.toMonoidHom) h
    rw [Subgroup.map_map] at hmap
    have hleft : L.map (c.toMonoidHom.comp ((c ^ 2).toMonoidHom)) = L := by
      change L.map ((c * c ^ 2).toMonoidHom) = L
      rw [show c * c ^ 2 = c ^ 3 by group, hc3]
      exact Subgroup.map_id L
    rw [hleft] at hmap
    exact h0 hmap.symm
  intro i j hij
  have hsub : L.map ((c ^ (i : ℕ)).toMonoidHom) = L.map ((c ^ (j : ℕ)).toMonoidHom) :=
    congrArg Subtype.val hij
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at hsub
  · rfl
  · exact (h0 (by simpa [MulAut.one_def, MulEquiv.toMonoidHom_refl] using hsub.symm)).elim
  · exact (h2 (by simpa [MulAut.one_def, MulEquiv.toMonoidHom_refl] using hsub.symm)).elim
  · exact (h0 (by simpa [MulAut.one_def, MulEquiv.toMonoidHom_refl] using hsub)).elim
  · rfl
  · have hmap := congrArg (fun M : Subgroup E => M.map c.toMonoidHom) hsub
    simp only [Subgroup.map_map] at hmap
    change L.map ((c * c).toMonoidHom) = L.map ((c * c ^ 2).toMonoidHom) at hmap
    rw [show c * c ^ 2 = c ^ 3 by group, hc3] at hmap
    have hmap' : L.map ((c ^ 2).toMonoidHom) = L := by
      simpa [pow_two, MulAut.one_def, MulEquiv.toMonoidHom_refl] using hmap
    exact (h2 hmap').elim
  · exact (h2 (by simpa [MulAut.one_def, MulEquiv.toMonoidHom_refl] using hsub)).elim
  · have hmap := congrArg (fun M : Subgroup E => M.map c.toMonoidHom) hsub
    simp only [Subgroup.map_map] at hmap
    change L.map ((c * c ^ 2).toMonoidHom) = L.map ((c * c).toMonoidHom) at hmap
    rw [show c * c ^ 2 = c ^ 3 by group, hc3] at hmap
    have hmap' : L.map ((c ^ 2).toMonoidHom) = L := by
      simpa [pow_two, MulAut.one_def, MulEquiv.toMonoidHom_refl] using hmap.symm
    exact (h2 hmap').elim
  · rfl

theorem orthogonalIdempotents_lineIdem {E : Type*} {U : Type} [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρE : E →* Module.End (ZMod 2) U) (hexp : ∀ x : E, x ^ 5 = 1)
    (hEcard' : Nat.card E = 5 ^ 2) (hpK : (5 : ZMod 2) ≠ 0)
    {ι : Type*} (L : ι → {M : Subgroup E // Nat.card M = 5})
    (hL : Function.Injective L) :
    OrthogonalIdempotents fun i => lineIdem ρE 5 (some (L i)) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact lineIdem_mul_self (K := ZMod 2) (V := U) (ρ := ρE) (p := 5) hEcard' hpK (some (L i))
  · intro i j hij
    have hne : L i ≠ L j := fun h => hij (hL h)
    have hsome : (some (L i) : Option {M : Subgroup E // Nat.card M = 5}) ≠ some (L j) := by
      simpa using hne
    exact lineIdem_mul_of_ne (K := ZMod 2) (V := U) (ρ := ρE) (p := 5)
      Nat.prime_five hexp hEcard' hpK hsome

theorem finrank_range_lineIdem_map {Γ E : Type*} {U : Type} [Group Γ] [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Γ →* Module.End (ZMod 2) U) (ρE : E →* Module.End (ZMod 2) U)
    (c : MulAut E) (g : Γ) (hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹)
    {L : Subgroup E} (hL : Nat.card L = 5) :
    Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5
        (some ⟨L.map c.toMonoidHom, by
          rw [Subgroup.card_map_of_injective c.injective, hL]⟩))) =
      Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some ⟨L, hL⟩))) := by
  have hconj := conj_lineIdem ρ ρE c g hgc hL
  have hρg_inv : (ρ g⁻¹).comp (ρ g) = 1 := by
    ext x
    simp
  rw [← hconj]
  exact finrank_range_conj_of_inv (K := ZMod 2) (ρ g) (ρ g⁻¹) hρg_inv _

theorem conj_lineIdem_pow_two {Γ E : Type*} {U : Type} [Group Γ] [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Γ →* Module.End (ZMod 2) U) (ρE : E →* Module.End (ZMod 2) U)
    (c : MulAut E) (g : Γ) (hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹)
    {L : Subgroup E} (hL : Nat.card L = 5) :
    ρ (g ^ 2) * lineIdem ρE 5 (some ⟨L, hL⟩) * ρ ((g ^ 2)⁻¹) =
      lineIdem ρE 5 (some ⟨L.map ((c ^ 2).toMonoidHom), by
        rw [Subgroup.card_map_of_injective (c ^ 2).injective, hL]⟩) := by
  have hgc2 : ∀ x : E, ρE ((c ^ 2) x) = ρ (g ^ 2) * ρE x * ρ (g ^ 2)⁻¹ := by
    intro x
    calc
      ρE ((c ^ 2) x) = ρE (c (c x)) := by rw [pow_two, MulAut.mul_apply]
      _ = ρ g * ρE (c x) * ρ g⁻¹ := hgc (c x)
      _ = ρ g * (ρ g * ρE x * ρ g⁻¹) * ρ g⁻¹ := by rw [hgc x]
      _ = (ρ g * ρ g) * ρE x * (ρ (g⁻¹) * ρ (g⁻¹)) := by group
      _ = ρ (g ^ 2) * ρE x * ρ ((g ^ 2)⁻¹) := by
        rw [pow_two, map_mul, show (g * g)⁻¹ = g⁻¹ * g⁻¹ by group, map_mul]
  exact conj_lineIdem ρ ρE (c ^ 2) (g ^ 2) hgc2 hL

theorem finrank_range_lineIdem_pow_two {Γ E : Type*} {U : Type} [Group Γ] [Group E]
    [Fintype E] [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Γ →* Module.End (ZMod 2) U) (ρE : E →* Module.End (ZMod 2) U)
    (c : MulAut E) (g : Γ) (hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹)
    {L : Subgroup E} (hL : Nat.card L = 5) :
    Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5
        (some ⟨L.map ((c ^ 2).toMonoidHom), by
          rw [Subgroup.card_map_of_injective (c ^ 2).injective, hL]⟩))) =
      Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some ⟨L, hL⟩))) := by
  have hconj := conj_lineIdem_pow_two ρ ρE c g hgc hL
  have hρg_inv : (ρ ((g ^ 2)⁻¹)).comp (ρ (g ^ 2)) = 1 := by
    ext x
    change ρ ((g ^ 2)⁻¹) (ρ (g ^ 2) x) = x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← hconj]
  exact finrank_range_conj_of_inv (K := ZMod 2) (ρ (g ^ 2)) (ρ ((g ^ 2)⁻¹)) hρg_inv _

theorem twelve_le_of_orthogonal_three {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (f : Fin 3 → Module.End (ZMod 2) U)
    (hOrth : OrthogonalIdempotents f)
    (hdim : ∀ i, Module.finrank (ZMod 2) (LinearMap.range (f i)) =
      Module.finrank (ZMod 2) (LinearMap.range (f 0)))
    (h4 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (f 0))) :
    12 ≤ Module.finrank (ZMod 2) U := by
  have hsum := sum_finrank_range_le (K := ZMod 2) (V := U) hOrth
  have hsum' : Module.finrank (ZMod 2) (LinearMap.range (f 0)) +
      Module.finrank (ZMod 2) (LinearMap.range (f 1)) +
      Module.finrank (ZMod 2) (LinearMap.range (f 2)) ≤ Module.finrank (ZMod 2) U := by
    simpa [Fin.sum_univ_three, add_assoc] using hsum
  rw [hdim 0, hdim 1, hdim 2] at hsum'
  omega

theorem four_le_finrank_range_lineIdem {E : Type*} {U : Type} [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρE : E →* Module.End (ZMod 2) U) (hcomm : ∀ e d : E, Commute (ρE e) (ρE d))
    (hexp : ∀ x : E, x ^ 5 = 1) (hEcard : Nat.card E = 25)
    {L : Subgroup E} (hL : Nat.card L = 5) (hLne : lineIdem ρE 5 (some ⟨L, hL⟩) ≠ 0) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some ⟨L, hL⟩))) := by
  have h4dvd := four_dvd_finrank_range_lineIdem ρE hcomm hexp hEcard hL
  have hpos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some ⟨L, hL⟩))) := by
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    apply hLne
    rw [← LinearMap.range_eq_bot]
    exact hbot
  exact Nat.le_of_dvd (by omega) h4dvd

theorem twelve_le_of_line_orbit {Γ E : Type*} {U : Type} [Group Γ] [Group E] [Fintype E]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Γ →* Module.End (ZMod 2) U) (ρE : E →* Module.End (ZMod 2) U)
    (hexp : ∀ x : E, x ^ 5 = 1) (hpK : (5 : ZMod 2) ≠ 0)
    (hEcard : Nat.card E = 25)
    (hcommρE : ∀ e d : E, Commute (ρE e) (ρE d))
    (c : MulAut E) (g : Γ) (hc3 : c ^ 3 = 1)
    (hfixed : ∀ M : Subgroup E, Nat.card M = 5 → M.map c.toMonoidHom ≠ M)
    (hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹)
    (L : {M : Subgroup E // Nat.card M = 5})
    (hLne : lineIdem ρE 5 (some L) ≠ 0) :
    12 ≤ Module.finrank (ZMod 2) U := by
  classical
  let Lf : Fin 3 → {M : Subgroup E // Nat.card M = 5} := fun i =>
    (⟨L.1.map ((c ^ (i : ℕ)).toMonoidHom), by
      rw [Subgroup.card_map_of_injective (c ^ (i : ℕ)).injective, L.2]⟩ :
      {M : Subgroup E // Nat.card M = 5})
  have hLf_zero : Lf 0 = L := by
    apply Subtype.ext
    simp [Lf, MulAut.one_def, MulEquiv.toMonoidHom_refl, Subgroup.map_id]
  have hLf_one : Lf 1 = ⟨L.1.map c.toMonoidHom, by
      rw [Subgroup.card_map_of_injective (f := c.toMonoidHom) c.injective, L.2]⟩ := by
    apply Subtype.ext
    simp [Lf, pow_one]
  have hLf_two : Lf 2 = ⟨L.1.map ((c ^ 2).toMonoidHom), by
      rw [Subgroup.card_map_of_injective (f := (c ^ 2).toMonoidHom) (c ^ 2).injective, L.2]⟩ := by
    apply Subtype.ext
    rfl
  have hEcard' : Nat.card E = 5 ^ 2 := by rw [hEcard]; norm_num
  have hinj : Function.Injective Lf := orbit_line_injective c hc3 L.2 hfixed
  let f : Fin 3 → Module.End (ZMod 2) U := fun i => lineIdem ρE 5 (some (Lf i))
  have hOrth : OrthogonalIdempotents f := by
    simpa [f] using orthogonalIdempotents_lineIdem ρE hexp hEcard' hpK Lf hinj
  have hdim : ∀ i, Module.finrank (ZMod 2) (LinearMap.range (f i)) =
      Module.finrank (ZMod 2) (LinearMap.range (f 0)) := by
    intro i
    fin_cases i
    · rfl
    · change Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some (Lf 1)))) =
        Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some (Lf 0))))
      rw [hLf_zero, hLf_one]
      simpa using finrank_range_lineIdem_map ρ ρE c g hgc L.2
    · change Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some (Lf 2)))) =
        Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some (Lf 0))))
      rw [hLf_zero, hLf_two]
      simpa using finrank_range_lineIdem_pow_two ρ ρE c g hgc L.2
  have h4 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (f 0)) := by
    change 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (lineIdem ρE 5 (some (Lf 0))))
    rw [hLf_zero]
    exact four_le_finrank_range_lineIdem ρE hcommρE hexp hEcard L.2 hLne
  exact twelve_le_of_orthogonal_three f hOrth hdim h4

theorem twelve_le_finrank_of_fiveSq_orderThree {Γ : Type*} [Group Γ]
    {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Γ U) {a b g : Γ}
    (ha : a ^ 5 = 1) (ha1 : a ≠ 1) (hb : b ^ 5 = 1) (hab : a * b = b * a)
    (hb' : ∀ i : ℕ, b ≠ a ^ i) (hg : g ^ 3 = 1)
    (hga : ∃ i j : ℕ, g * a * g⁻¹ = a ^ i * b ^ j)
    (hgb : ∃ i j : ℕ, g * b * g⁻¹ = a ^ i * b ^ j)
    (hgnc : g * a * g⁻¹ ≠ a ∨ g * b * g⁻¹ ≠ b) (hρ : ρ a ≠ 1 ∨ ρ b ≠ 1) :
    12 ≤ Module.finrank (ZMod 2) U := by
  classical
  let E := fiveSqSubgroup a b ha hb hab
  have hEcard : Nat.card E = 25 := card_fiveSqSubgroup ha ha1 hb hab hb'
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  have hEcard' : Nat.card E = 5 ^ 2 := by rw [hEcard]; norm_num
  have hexp : ∀ x : E, x ^ 5 = 1 := fun x => pow_five_eq_one x
  let ρE : Representation (ZMod 2) E U := ρ.comp E.subtype
  have hpK : (5 : ZMod 2) ≠ 0 := by decide
  have hcommE : ∀ x y : E, x * y = y * x := fun x y =>
    Subtype.ext (fiveSqSubgroup_comm (x := (x : Γ)) x.2 (y := (y : Γ)) y.2)
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hcommE }
  have hne : ∃ x : E, ρE x ≠ 1 := by
    by_contra h
    push Not at h
    have hρa : ρ a = 1 := by simpa [ρE] using h ⟨a, mem_fiveSqSubgroup_left⟩
    have hρb : ρ b = 1 := by simpa [ρE] using h ⟨b, mem_fiveSqSubgroup_right⟩
    rcases hρ with h | h
    · exact h hρa
    · exact h hρb
  obtain ⟨L, hLne⟩ := exists_lineIdem_ne_zero_of_nontrivial ρE hEcard' hexp hpK hne
  have hgE : g ∈ Subgroup.normalizer (E : Set Γ) :=
    fiveSqSubgroup_le_normalizer ha hb hab hga hgb
  let c : MulAut E := fiveSqConjAut ha hb hab hgE
  have hc3 : c ^ 3 = 1 := fiveSqConjAut_pow_three ha hb hab hgE hg
  have hcne : c ≠ 1 := fiveSqConjAut_ne_one ha hb hab hgE hgnc
  have hfixed : ∀ M : Subgroup E, Nat.card M = 5 → M.map c.toMonoidHom ≠ M := fun M hM =>
    fiveSq_no_fixed_line_of_order_three ha ha1 hb hab hb' c hc3 hcne hM
  have hgc : ∀ x : E, ρE (c x) = ρ g * ρE x * ρ g⁻¹ := by
    intro x
    change ρ ((c x : E) : Γ) = ρ g * ρ (x : Γ) * ρ g⁻¹
    rw [fiveSqConjAut_apply, map_mul, map_mul]
  have hcommρE : ∀ e d : E, Commute (ρE e) (ρE d) := by
    intro e d
    change ρE e * ρE d = ρE d * ρE e
    rw [← map_mul, ← map_mul, hcommE e d]
  exact twelve_le_of_line_orbit ρ ρE hexp hpK hEcard hcommρE c g hc3 hfixed hgc L hLne

end CFSG.RepresentationTheory.GF2
