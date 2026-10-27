module

public import CFSG.RankThree.Literature.SemiExtraspecial
public import CFSG.RankThree.Literature.AlternatingPencil
public import CFSG.RankThree.GroupTheory.ClassTwoThree

public section

namespace CFSG.RankThree.Literature

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {P : Type*} [Group P]

theorem IsSemiExtraspecial.rank_data [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    [Nontrivial P] (hS : IsSemiExtraspecial p P) :
    ∃ n m : ℕ, 1 ≤ n ∧ (center P).index = p ^ (2 * n) ∧ Nat.card (center P) = p ^ m ∧
      1 ≤ m ∧ m ≤ n ∧ ∀ A : Subgroup P, (∀ a ∈ A, ∀ b ∈ A, Commute a b) →
        (center P).relIndex (A ⊔ center P) ≤ p ^ n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨hcomm, hfr, hZea⟩ := hS.special hp hP
  have hc : commutator P ≤ center P := hcomm.le
  have hp2 : 2 ≤ p := hp.two_le
  have hof : ∀ v : Additive (Abelianization P), ∃ x : P,
      Additive.ofMul (Abelianization.of x) = v := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, hx⟩
  have hof1 : ∀ x : P, Additive.ofMul (Abelianization.of x) = 0 ↔ x ∈ center P := by
    intro x
    rw [← hcomm, ← Abelianization.ker_of, MonoidHom.mem_ker]
    exact Additive.ofMul.injective.eq_iff' rfl
  have hpV : ∀ v : Additive (Abelianization P), p • v = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := hof v
    rw [← ofMul_pow, ← map_pow]
    exact (hof1 _).mpr (hfr ▸ pth_power_mem_frattini_of_isPGroup x)
  have _ : Module (ZMod p) (Additive (Abelianization P)) := AddCommGroup.zmodModule hpV
  have : Finite (Additive (Abelianization P)) :=
    Finite.of_surjective (fun x : P => Additive.ofMul (Abelianization.of x)) fun v => hof v
  have : Module.Finite (ZMod p) (Additive (Abelianization P)) := Module.Finite.of_finite
  let _ : CommGroup (center P) := IsMulCommutative.instCommGroup
  have hpW : ∀ w : Additive (center P), p • w = 0 := by
    intro w
    have h := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := center P)
      ((Additive.toMul w : center P) : P) (Additive.toMul w).2
    change Additive.ofMul (Additive.toMul w ^ p) = 0
    rw [show Additive.toMul w ^ p = 1 from Subtype.ext (by simpa using h)]
    rfl
  have _ : Module (ZMod p) (Additive (center P)) := AddCommGroup.zmodModule hpW
  have : Module.Finite (ZMod p) (Additive (center P)) := Module.Finite.of_finite
  let pr : Abelianization P → Abelianization P → center P := fun u v =>
    ⟨CFSG.RankThree.commPairing hc u v, hc (CFSG.RankThree.commPairing hc u v).2⟩
  have pr_mul_right : ∀ x y y', pr x (y * y') = pr x y * pr x y' := fun x y y' => by
    have h := congrArg Subtype.val (CFSG.RankThree.commPairing_mul_right hc x y y')
    exact Subtype.ext h
  have pr_mul_left : ∀ x x' y, pr (x * x') y = pr x y * pr x' y := fun x x' y => by
    have h := congrArg Subtype.val (CFSG.RankThree.commPairing_mul_left hc x x' y)
    exact Subtype.ext h
  have pr_one_right : ∀ x, pr x 1 = 1 := fun x => by
    have h := pr_mul_right x 1 1
    rw [mul_one] at h
    exact mul_eq_left.mp h.symm
  have pr_one_left : ∀ y, pr 1 y = 1 := fun y => by
    have h := pr_mul_left 1 1 y
    rw [mul_one] at h
    exact mul_eq_left.mp h.symm
  let β₀ : Additive (Abelianization P) →+ Additive (Abelianization P) →+
      Additive (center P) :=
    { toFun := fun u =>
        { toFun := fun v => Additive.ofMul (pr (Additive.toMul u) (Additive.toMul v))
          map_zero' := by
            change Additive.ofMul (pr _ 1) = 0
            rw [pr_one_right]
            rfl
          map_add' := fun v v' => by
            change Additive.ofMul (pr _ (Additive.toMul v * Additive.toMul v')) = _
            rw [pr_mul_right]
            rfl }
      map_zero' := by
        refine AddMonoidHom.ext fun v => ?_
        change Additive.ofMul (pr 1 _) = 0
        rw [pr_one_left]
        rfl
      map_add' := fun u u' => by
        refine AddMonoidHom.ext fun v => ?_
        change Additive.ofMul (pr (Additive.toMul u * Additive.toMul u') _) = _
        rw [pr_mul_left]
        rfl }
  let β : Additive (Abelianization P) →ₗ[ZMod p] Additive (Abelianization P) →ₗ[ZMod p]
      Additive (center P) :=
    LinearMap.mk₂ (ZMod p) (fun u v => β₀ u v)
      (fun u u' v => by rw [map_add, AddMonoidHom.add_apply])
      (fun c u v => (AddMonoidHom.toZModLinearMap p (β₀.flip v)).map_smul c u)
      (fun u v v' => map_add _ _ _)
      (fun c u v => (AddMonoidHom.toZModLinearMap p (β₀ u)).map_smul c v)
  have hβ : ∀ x y : P, β (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) =
        Additive.ofMul ⟨CFSG.RankThree.lcomm x y, hc (CFSG.RankThree.lcomm_mem_commutator x y)⟩ :=
    fun x y => rfl
  have hβself : ∀ v, β v v = 0 := by
    intro v
    change Additive.ofMul (pr (Additive.toMul v) (Additive.toMul v)) = 0
    have : pr (Additive.toMul v) (Additive.toMul v) = 1 := by
      have h := congrArg Subtype.val (CFSG.RankThree.commPairing_self hc (Additive.toMul v))
      exact Subtype.ext h
    rw [this]
    rfl
  have hsurjZ : ∀ x : P, x ∉ center P → ∀ z ∈ center P,
      ∃ y : P, CFSG.RankThree.lcomm x y = z := by
    intro x hx z hz
    have hx' : x⁻¹ ∉ center P := fun h => hx (by simpa using inv_mem h)
    obtain ⟨-, hrange, -, -⟩ := hS.commutator_map hp hP hx'
    have hzc : z ∈ (center P : Set P) := hz
    rw [← hrange] at hzc
    obtain ⟨y, hy⟩ := hzc
    refine ⟨y⁻¹, ?_⟩
    rw [← hy]
    simp only [CFSG.RankThree.lcomm, commutatorElement_def, inv_inv]
  let Bf : Module.Dual (ZMod p) (Additive (center P)) →
      LinearMap.BilinForm (ZMod p) (Additive (Abelianization P)) := fun l => β.compr₂ l
  have halt : ∀ l : Module.Dual (ZMod p) (Additive (center P)), (Bf l).IsAlt := by
    intro l v
    rw [LinearMap.compr₂_apply, hβself, map_zero]
  have hnd : ∀ l : Module.Dual (ZMod p) (Additive (center P)), l ≠ 0 →
      (Bf l).Nondegenerate := by
    intro l hl
    have hsep : ∀ v, (∀ w, Bf l v w = 0) → v = 0 := by
      intro v hv
      obtain ⟨x, rfl⟩ := hof v
      by_contra hne
      have hx : x ∉ center P := fun h => hne ((hof1 x).mpr h)
      apply hl
      ext w
      obtain ⟨⟨z, hz⟩, rfl⟩ : ∃ z : center P, Additive.ofMul z = w := ⟨Additive.toMul w, rfl⟩
      obtain ⟨y, hy⟩ := hsurjZ x hx z hz
      have h := hv (Additive.ofMul (Abelianization.of y))
      rw [LinearMap.compr₂_apply, hβ] at h
      have heq : (⟨CFSG.RankThree.lcomm x y, hc (CFSG.RankThree.lcomm_mem_commutator x y)⟩ :
          center P) = ⟨z, hz⟩ := Subtype.ext hy
      rw [heq] at h
      simpa using h
    refine ⟨hsep, fun v hv => hsep v fun w => ?_⟩
    rw [← (halt l).neg_eq, hv w]
    exact neg_zero
  set d := Module.finrank (ZMod p) (Additive (Abelianization P)) with hd
  set m := Module.finrank (ZMod p) (Additive (center P)) with hm
  have hindex : (center P).index = p ^ d := by
    rw [← hcomm, index_eq_card, ← Nat.card_zmod p]
    exact Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (Abelianization P))
  have hcardZ : Nat.card (center P) = p ^ m := by
    rw [← Nat.card_zmod p]
    exact Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (center P))
  have hZne : center P ≠ ⊥ := (nontrivial_iff_ne_bot _).mp hP.center_nontrivial
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      apply hZne
      apply Subgroup.eq_bot_of_card_eq
      rw [hcardZ, h, pow_zero]
    · exact h
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso
      rw [h, pow_zero, index_eq_one] at hindex
      apply hZne
      rw [← hcomm, eq_bot_iff, commutator_eq_closure, closure_le]
      rintro _ ⟨x, y, rfl⟩
      rw [SetLike.mem_coe, mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (hindex ▸ mem_top x) y).symm
    · exact h
  let wb := Module.finBasisOfFinrankEq (ZMod p) (Additive (center P)) hm.symm
  let l₀ := wb.coord ⟨0, hm1⟩
  have hl₀ : l₀ ≠ 0 := by
    intro h
    have := congrArg (fun f => f (wb ⟨0, hm1⟩)) h
    simp [l₀] at this
  obtain ⟨n, hn⟩ := (halt l₀).even_finrank (hnd l₀ hl₀)
  have hd2 : d = 2 * n := by rw [hd, hn, two_mul]
  have hn1 : 1 ≤ n := by omega
  let eb := Module.finBasisOfFinrankEq (ZMod p) (Additive (Abelianization P)) (hd.symm.trans hd2)
  let Ag : Fin m → Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod p) := fun i =>
    LinearMap.BilinForm.toMatrix eb (Bf (wb.coord i))
  have hmn : 2 * m ≤ 2 * n := by
    refine Beisiegel.two_mul_le_of_det_ne_zero (by omega) Ag (fun i j => ?_) (fun i j l => ?_)
      (fun a ha => ?_)
    · simp only [Ag, LinearMap.BilinForm.toMatrix_apply]
      exact halt _ _
    · simp only [Ag, LinearMap.BilinForm.toMatrix_apply]
      exact ((halt _).neg_eq _ _).symm
    · let la : Module.Dual (ZMod p) (Additive (center P)) := ∑ i, a i • wb.coord i
      have hla : la ≠ 0 := by
        intro h
        apply ha
        funext j
        have := congrArg (fun f => f (wb j)) h
        simpa [la, Module.Basis.coord_apply, Finsupp.single_apply] using this
      have hsum : (∑ i, a i • Ag i) = LinearMap.BilinForm.toMatrix eb (Bf la) := by
        ext j l
        simp only [Ag, la, Bf, Matrix.sum_apply, Matrix.smul_apply,
          LinearMap.BilinForm.toMatrix_apply, LinearMap.compr₂_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, smul_eq_mul]
      rw [hsum]
      exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero eb).mp (hnd la hla)
  refine ⟨n, m, hn1, by rw [hindex, hd2], hcardZ, hm1, by omega, fun A hA => ?_⟩
  let U : Submodule (ZMod p) (Additive (Abelianization P)) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup (A.map Abelianization.of))
  have hUiso : U ≤ (Bf l₀).orthogonal U := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨a, ha, hau⟩ := hu
    obtain ⟨b, hb, hbv⟩ := hv
    rw [LinearMap.compr₂_apply]
    have hu' : u = Additive.ofMul (Abelianization.of a) := by rw [hau]; rfl
    have hv' : v = Additive.ofMul (Abelianization.of b) := by rw [hbv]; rfl
    rw [hu', hv', hβ]
    have h1 : (⟨CFSG.RankThree.lcomm a b, hc (CFSG.RankThree.lcomm_mem_commutator a b)⟩ :
        center P) = 1 := by
      apply Subtype.ext
      simp only [CFSG.RankThree.lcomm, OneMemClass.coe_one]
      have hab := (hA a ha b hb).eq
      calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (a * b) := by group
        _ = a⁻¹ * b⁻¹ * (b * a) := by rw [hab]
        _ = 1 := by group
    rw [h1]
    exact map_zero l₀
  have hUdim : Module.finrank (ZMod p) U ≤ n := by
    have h1 := Submodule.finrank_mono hUiso
    rw [LinearMap.BilinForm.finrank_orthogonal (hnd l₀ hl₀)] at h1
    omega
  have hUcard : Nat.card U = (center P).relIndex A := by
    have h1 : Nat.card U = Nat.card (A.map Abelianization.of) :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => Iff.rfl)
    have h2 := index_ker (Abelianization.of.domRestrict A)
    rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, Abelianization.ker_of,
      hcomm] at h2
    rw [h1, ← h2]
    rfl
  have hUcard' : Nat.card U = p ^ Module.finrank (ZMod p) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := U), Nat.card_zmod]
  rw [relIndex_sup_right, ← hUcard, hUcard']
  exact Nat.pow_le_pow_right hp.pos hUdim

theorem IsSemiExtraspecial.index_center [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    [Nontrivial P] (hS : IsSemiExtraspecial p P) :
    ∃ n m : ℕ, 1 ≤ n ∧ (center P).index = p ^ (2 * n) ∧ Nat.card (center P) = p ^ m ∧
      1 ≤ m ∧ m ≤ n ∧ Nat.card (center P) ^ 2 ≤ (center P).index := by
  obtain ⟨n, m, hn, hindex, hcard, hm, hmn, -⟩ := hS.rank_data hp hP
  refine ⟨n, m, hn, hindex, hcard, hm, hmn, ?_⟩
  rw [hindex, hcard, ← pow_mul, mul_comm]
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem IsSemiExtraspecial.abelian_bound [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    [Nontrivial P] (hS : IsSemiExtraspecial p P) {n m : ℕ}
    (hindex : (center P).index = p ^ (2 * n)) (hcard : Nat.card (center P) = p ^ m)
    (A : Subgroup P) (hA : ∀ a ∈ A, ∀ b ∈ A, Commute a b) :
    (center P).relIndex (A ⊔ center P) ≤ p ^ n ∧
      Nat.card (A ⊔ center P : Subgroup P) ≤ p ^ (n + m) := by
  obtain ⟨n', m', -, hindex', -, -, -, hA'⟩ := hS.rank_data hp hP
  have hnn : n' = n := by
    have := Nat.pow_right_injective hp.two_le (hindex'.symm.trans hindex)
    omega
  subst hnn
  have hrel := hA' A hA
  refine ⟨hrel, ?_⟩
  have h := relIndex_mul_card (center P) (A ⊔ center P)
  rw [inf_eq_left.mpr le_sup_right, hcard] at h
  rw [← h, pow_add]
  exact Nat.mul_le_mul_right _ hrel

theorem IsSemiExtraspecial.lcomm_map [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    [Nontrivial P] (hS : IsSemiExtraspecial p P) {x : P} (hx : x ∉ center P) :
    (∃ f : P →* center P, (∀ y, (f y : P) = CFSG.RankThree.lcomm x y) ∧
      Function.Surjective f ∧ f.ker = centralizer {x}) ∧
      Set.range (fun y => CFSG.RankThree.lcomm x y) = (center P : Set P) ∧
      closure (Set.range fun y => CFSG.RankThree.lcomm x y) = center P := by
  have hx' : x⁻¹ ∉ center P := fun h => hx (by simpa using inv_mem h)
  obtain ⟨⟨g, hg, hgs, hgk⟩, -, -, -⟩ := hS.commutator_map hp hP hx'
  have hcomm : ∀ a b : center P, a * b = b * a := fun a b =>
    (inferInstance : IsMulCommutative (center P)).is_comm.comm a b
  let f : P →* center P :=
    { toFun := fun y => (g y)⁻¹
      map_one' := by simp only [map_one, inv_one]
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        exact hcomm _ _ }
  have hf : ∀ y, (f y : P) = CFSG.RankThree.lcomm x y := by
    intro y
    change ((g y)⁻¹ : center P).1 = _
    rw [← map_inv, hg, CFSG.RankThree.lcomm_eq_commutatorElement]
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := hgs z⁻¹
    exact ⟨y, by change (g y)⁻¹ = z; rw [hy, inv_inv]⟩
  have hfk : f.ker = centralizer {x} := by
    ext y
    rw [MonoidHom.mem_ker, mem_centralizer_singleton_iff]
    change (g y)⁻¹ = 1 ↔ _
    rw [inv_eq_one, ← MonoidHom.mem_ker, hgk, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc y * x = x * (x⁻¹ * y) * x := by group
        _ = x * (y * x⁻¹) * x := by rw [h]
        _ = x * y := by group
    · intro h
      calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
        _ = x⁻¹ * (y * x) * x⁻¹ := by rw [h]
        _ = x⁻¹ * y := by group
  have hrange : Set.range (fun y => CFSG.RankThree.lcomm x y) = (center P : Set P) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      show CFSG.RankThree.lcomm x y ∈ center P
      rw [← hf]
      exact (f y).2
    · intro hz
      obtain ⟨y, hy⟩ := hfs ⟨z, hz⟩
      exact ⟨y, by show CFSG.RankThree.lcomm x y = z; rw [← hf, hy]⟩
  exact ⟨⟨f, hf, hfs, hfk⟩, hrange, by rw [hrange, closure_eq]⟩

end CFSG.RankThree.Literature
