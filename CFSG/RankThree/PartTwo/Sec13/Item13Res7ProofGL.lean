module

public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open Matrix CFSG
open scoped MatrixGroups

structure AltTarget (T : Type*) [Group T] [Finite T] : Prop where
  simple : IsSimpleGroup T
  perfect : Group.IsPerfect T
  even : 2 ∣ Nat.card T
  card_ne : ∀ q : ℕ, q.Prime → 5 ≤ q →
    q * (q ^ 2 - 1) ≠ Nat.card T ∧ q * (q ^ 2 - 1) ≠ 2 * Nat.card T

theorem sl2_order_ne {N : ℕ} {bound : ℕ} (hb : N < bound * (bound ^ 2 - 1))
    (hcheck : ∀ q < bound, 5 ≤ q → q.Prime → q * (q ^ 2 - 1) ≠ N) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) : q * (q ^ 2 - 1) ≠ N := by
  by_cases hqb : q < bound
  · exact hcheck q hqb hq5 hq
  · intro h
    push Not at hqb
    have h1 : bound ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqb 2
    have h2 : bound * (bound ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hqb (Nat.sub_le_sub_right h1 1)
    omega

theorem altTarget_six : AltTarget (alternatingGroup (Fin 6)) where
  simple := alternatingGroup.isSimpleGroup (by simp)
  perfect := Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  even := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  card_ne q hq hq5 := by
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [hc]
    refine ⟨sl2_order_ne (bound := 10) (by norm_num) (fun q hq hq5 hqp => ?_) hq hq5,
      sl2_order_ne (bound := 10) (by norm_num) (fun q hq hq5 hqp => ?_) hq hq5⟩
    · interval_cases q <;> revert hqp <;> norm_num
    · interval_cases q <;> revert hqp <;> norm_num

theorem altTarget_seven : AltTarget (alternatingGroup (Fin 7)) where
  simple := alternatingGroup.isSimpleGroup (by simp)
  perfect := Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  even := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  card_ne q hq hq5 := by
    have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [hc]
    refine ⟨sl2_order_ne (bound := 18) (by norm_num) (fun q hq hq5 hqp => ?_) hq hq5,
      sl2_order_ne (bound := 18) (by norm_num) (fun q hq hq5 hqp => ?_) hq hq5⟩
    · interval_cases q <;> revert hqp <;> norm_num
    · interval_cases q <;> revert hqp <;> norm_num

theorem AltTarget.nontrivial {T : Type*} [Group T] [Finite T] (hT : AltTarget T) :
    Nontrivial T :=
  hT.simple.toNontrivial

theorem AltTarget.exists_ne_comm {T : Type*} [Group T] [Finite T] (hT : AltTarget T) :
    ∃ a b : T, a * b ≠ b * a := by
  have := hT.perfect
  have := hT.nontrivial
  by_contra h
  push Not at h
  have : IsMulCommutative T := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative T this

theorem AltTarget.map_eq_bot_of_odd {T : Type*} [Group T] [Finite T] (hT : AltTarget T)
    {Y : Type*} [Group Y] [Finite Y] (ψ : Y →* T) (hψ : Function.Surjective ψ) {N : Subgroup Y}
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N.map ψ = ⊥ := by
  have := hT.simple
  have := hN.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ψ) with h | h
  · exact h
  · exfalso
    have hd : Nat.card (N.map ψ) ∣ Nat.card N := Subgroup.card_map_dvd N ψ
    rw [h, Subgroup.card_top] at hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hT.even.trans hd))

theorem card_eq_of_surj_SL2 {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {T : Type*} [Group T]
    [Nontrivial T] (φ : SL(2, ZMod q) →* T) (hφ : Function.Surjective φ) :
    q * (q ^ 2 - 1) = Nat.card T ∨ q * (q ^ 2 - 1) = 2 * Nat.card T := by
  have hQ := Sec4.Census.isQuasisimple_SL2 (p := q) hq5
  have hZ := Sec4.Census.card_center_SL2 (p := q) (by omega)
  have hcard := Sec4.Census.card_SL2 (p := q)
  rcases LocalCores.quasisimple_normal_subgroups hQ φ.normal_ker with h | h
  · exfalso
    obtain ⟨t, ht⟩ := exists_ne (1 : T)
    obtain ⟨g, rfl⟩ := hφ t
    apply ht
    rw [← MonoidHom.mem_ker, h]
    exact Subgroup.mem_top g
  · have hdvd : Nat.card φ.ker ∣ 2 := by
      have h' := Subgroup.card_dvd_of_le h
      rwa [hZ] at h'
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (SL(2, ZMod q) ⧸ φ.ker) = Nat.card T :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
    rw [h2, hcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h3 | h3 <;> rw [h3] at h1
    · left
      rw [h1, mul_one]
    · right
      rw [h1, mul_comm]

theorem map_perfectResidual_eq_top {Y : Type*} [Group Y] [Finite Y] {T : Type*} [Group T]
    [Group.IsPerfect T] (ψ : Y →* T) (hψ : Function.Surjective ψ) :
    (CFSG.perfectResidual Y).map ψ = ⊤ := by
  obtain ⟨⟨m, hm, -⟩, -⟩ := CFSG.perfect_residual_characterization (G := Y)
  rw [hm, map_derivedSeries_eq hψ, Group.IsPerfect.derivedSeries_eq_top]

theorem false_of_gl2 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {Y : Type*} [Group Y] [Finite Y] (ρ : Y →* GL (Fin 2) (ZMod p)) {T : Type*} [Group T]
    [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ)
    (hker : ρ.ker ≤ ψ.ker) : False := by
  classical
  have := hT.perfect
  have := hT.nontrivial
  set J := CFSG.perfectResidual Y with hJ
  obtain ⟨-, -, hJperf, -⟩ := CFSG.perfect_residual_characterization (G := Y)
  have hψJ : J.map ψ = ⊤ := map_perfectResidual_eq_top ψ hψ
  set R := J.map ρ with hR
  have : Group.IsPerfect R := Group.IsPerfect.map ρ
  set f : J →* R := ρ.subgroupMap J with hf
  have hfs : Function.Surjective f := ρ.subgroupMap_surjective J
  set g : J →* T := ψ.comp J.subtype with hg
  have hfg : f.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : ρ (x : Y) = 1 := by
      have h := congrArg (fun r : R => (r : GL (Fin 2) (ZMod p))) hx
      exact h
    exact hker hx'
  set ψR : R →* T := f.liftOfRightInverse (Function.surjInv hfs)
    (Function.rightInverse_surjInv hfs) ⟨g, hfg⟩ with hψR
  have hψRf : ∀ x : J, ψR (f x) = g x := fun x =>
    f.liftOfRightInverse_comp_apply (Function.surjInv hfs) (Function.rightInverse_surjInv hfs)
      ⟨g, hfg⟩ x
  have hψRs : Function.Surjective ψR := by
    intro t
    have ht : t ∈ J.map ψ := hψJ ▸ Subgroup.mem_top t
    obtain ⟨y, hy, rfl⟩ := ht
    exact ⟨f ⟨y, hy⟩, by rw [hψRf]; rfl⟩
  have hRbot : R ≠ ⊥ := by
    intro hbot
    obtain ⟨t, ht⟩ := exists_ne (1 : T)
    obtain ⟨r, rfl⟩ := hψRs t
    apply ht
    have hr : r = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall R).mp hbot r r.2)
    rw [hr, map_one]
  rcases SubgroupLists.perfect_gl2_mulEquiv (by omega) R hRbot with he | he
  · obtain ⟨e⟩ := he
    have hφ : Function.Surjective (ψR.comp e.symm.toMonoidHom) :=
      hψRs.comp e.symm.surjective
    rcases card_eq_of_surj_SL2 hp5 _ hφ with h | h
    · exact (hT.card_ne p Fact.out hp5).1 h
    · exact (hT.card_ne p Fact.out hp5).2 h
  · obtain ⟨e⟩ := he
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hφ : Function.Surjective (ψR.comp e.symm.toMonoidHom) :=
      hψRs.comp e.symm.surjective
    rcases card_eq_of_surj_SL2 le_rfl _ hφ with h | h
    · exact (hT.card_ne 5 (by norm_num) le_rfl).1 h
    · exact (hT.card_ne 5 (by norm_num) le_rfl).2 h

theorem matrix_mul_comm_of_le_one {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 1)
    (A B : Matrix (Fin d) (Fin d) R) : A * B = B * A := by
  ext i j
  have hij : i = j := by
    apply Fin.ext
    have := i.2
    have := j.2
    omega
  subst hij
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k = i := by
    apply Fin.ext
    have := i.2
    have := k.2
    omega
  subst hk
  rw [mul_comm]

theorem false_of_gl_le_one {p : ℕ} {d : ℕ} (hd : d ≤ 1) {Y : Type*} [Group Y]
    (ρ : Y →* GL (Fin d) (ZMod p)) {T : Type*} [Group T] [Finite T] (hT : AltTarget T)
    (ψ : Y →* T) (hψ : Function.Surjective ψ) (hker : ρ.ker ≤ ψ.ker) : False := by
  obtain ⟨a, b, hab⟩ := hT.exists_ne_comm
  obtain ⟨x, rfl⟩ := hψ a
  obtain ⟨y, rfl⟩ := hψ b
  apply hab
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : ρ x * ρ y = ρ y * ρ x :=
      Units.ext (matrix_mul_comm_of_le_one hd _ _)
    rw [hc]
    group
  have h2 := hker h1
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  calc ψ x * ψ y = ψ x * ψ y * (ψ x)⁻¹ * (ψ y)⁻¹ * (ψ y * ψ x) := by group
    _ = ψ y * ψ x := by rw [h2, one_mul]

section Rep

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {Y : Type*} [Group Y]

@[expose] noncomputable def restrictRep (ρ : Y →* Module.End (ZMod p) V)
    (W : Submodule (ZMod p) V) (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) :
    Y →* Module.End (ZMod p) W where
  toFun y := (ρ y).restrict (hW y)
  map_one' := by
    ext w
    simp [LinearMap.restrict_apply]
  map_mul' x y := by
    ext w
    simp [LinearMap.restrict_apply]

theorem restrictRep_apply (ρ : Y →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) (y : Y) (w : W) :
    (restrictRep ρ W hW y w : V) = ρ y w :=
  rfl

theorem restrictRep_eq_one_iff (ρ : Y →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) (y : Y) :
    restrictRep ρ W hW y = 1 ↔ ∀ w ∈ W, ρ y w = w := by
  constructor
  · intro h w hw
    have := congrArg (fun f : Module.End (ZMod p) W => (f ⟨w, hw⟩ : V)) h
    simpa [restrictRep_apply] using this
  · intro h
    ext w
    rw [restrictRep_apply]
    exact h w w.2

@[expose] noncomputable def fixKer (ρ : Y →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) : Subgroup Y :=
  (restrictRep ρ W hW).toHomUnits.ker

theorem mem_fixKer_iff (ρ : Y →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) (y : Y) :
    y ∈ fixKer ρ W hW ↔ ∀ w ∈ W, ρ y w = w := by
  rw [fixKer, MonoidHom.mem_ker, ← restrictRep_eq_one_iff ρ W hW y, ← Units.val_inj]
  rfl

theorem fixKer_normal (ρ : Y →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) : (fixKer ρ W hW).Normal :=
  MonoidHom.normal_ker _

theorem false_of_rep_one [FiniteDimensional (ZMod p) V] [Finite Y]
    (hp5 : 5 ≤ p)
    (ρ : Y →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW2 : Module.finrank (ZMod p) W ≤ 2) (hW : ∀ y, ∀ w ∈ W, ρ y w ∈ W) {T : Type*}
    [Group T] [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ)
    (hker : ∀ y, (∀ w ∈ W, ρ y w = w) → ψ y = 1) : False := by
  classical
  set ρW := restrictRep ρ W hW with hρW
  have hkerW : ∀ y, ρW y = 1 → ψ y = 1 := fun y hy =>
    hker y ((restrictRep_eq_one_iff ρ W hW y).mp hy)
  rcases Nat.lt_or_ge (Module.finrank (ZMod p) W) 2 with hlt | hge
  ·
    set b := Module.finBasis (ZMod p) W
    set ρM : Y →* GL (Fin (Module.finrank (ZMod p) W)) (ZMod p) :=
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρW.toHomUnits with hρM
    refine false_of_gl_le_one (by omega) ρM hT ψ hψ ?_
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    apply hkerW
    have h1 := congrArg Units.val hy
    simp only [hρM, MonoidHom.comp_apply, Units.coe_map, Units.val_one,
      MonoidHom.coe_toHomUnits] at h1
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_one]
    exact h1
  ·
    have h2 : Module.finrank (ZMod p) W = 2 := le_antisymm hW2 hge
    set b := Module.finBasisOfFinrankEq (ZMod p) W h2
    set ρM : Y →* GL (Fin 2) (ZMod p) :=
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρW.toHomUnits with hρM
    refine false_of_gl2 hp5 ρM hT ψ hψ ?_
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    apply hkerW
    have h1 := congrArg Units.val hy
    simp only [hρM, MonoidHom.comp_apply, Units.coe_map, Units.val_one,
      MonoidHom.coe_toHomUnits] at h1
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_one]
    exact h1

theorem false_of_rep_two [FiniteDimensional (ZMod p) V] [Finite Y]
    (hp5 : 5 ≤ p)
    (ρ : Y →* Module.End (ZMod p) V) (W₁ W₂ : Submodule (ZMod p) V)
    (h₁ : Module.finrank (ZMod p) W₁ ≤ 2) (h₂ : Module.finrank (ZMod p) W₂ ≤ 2)
    (hW₁ : ∀ y, ∀ w ∈ W₁, ρ y w ∈ W₁) (hW₂ : ∀ y, ∀ w ∈ W₂, ρ y w ∈ W₂) {T : Type*}
    [Group T] [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ)
    (hker : ∀ y, (∀ w ∈ W₁, ρ y w = w) → (∀ w ∈ W₂, ρ y w = w) → ψ y = 1) : False := by
  set N := fixKer ρ W₁ hW₁ with hN
  have hNn : N.Normal := fixKer_normal ρ W₁ hW₁
  have := hT.simple
  have := hNn.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ψ) with h | h
  · refine false_of_rep_one hp5 ρ W₁ h₁ hW₁ hT ψ hψ fun y hy => ?_
    have hyN : y ∈ N := (mem_fixKer_iff ρ W₁ hW₁ y).mpr hy
    have : ψ y ∈ N.map ψ := ⟨y, hyN, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · have hs : Function.Surjective (ψ.comp N.subtype) := by
      intro t
      have ht : t ∈ N.map ψ := h ▸ Subgroup.mem_top t
      obtain ⟨y, hy, rfl⟩ := ht
      exact ⟨⟨y, hy⟩, rfl⟩
    refine false_of_rep_one hp5 (ρ.comp N.subtype) W₂ h₂ (fun y => hW₂ y) hT _ hs
      fun y hy => ?_
    exact hker y ((mem_fixKer_iff ρ W₁ hW₁ y).mp y.2) hy

theorem false_of_rep_three [FiniteDimensional (ZMod p) V] [Finite Y]
    (hp5 : 5 ≤ p)
    (ρ : Y →* Module.End (ZMod p) V) (W₁ W₂ W₃ : Submodule (ZMod p) V)
    (h₁ : Module.finrank (ZMod p) W₁ ≤ 2) (h₂ : Module.finrank (ZMod p) W₂ ≤ 2)
    (h₃ : Module.finrank (ZMod p) W₃ ≤ 2)
    (hW₁ : ∀ y, ∀ w ∈ W₁, ρ y w ∈ W₁) (hW₂ : ∀ y, ∀ w ∈ W₂, ρ y w ∈ W₂)
    (hW₃ : ∀ y, ∀ w ∈ W₃, ρ y w ∈ W₃) {T : Type*} [Group T] [Finite T] (hT : AltTarget T)
    (ψ : Y →* T) (hψ : Function.Surjective ψ)
    (hker : ∀ y, (∀ w ∈ W₁, ρ y w = w) → (∀ w ∈ W₂, ρ y w = w) → (∀ w ∈ W₃, ρ y w = w) →
      ψ y = 1) : False := by
  set N := fixKer ρ W₁ hW₁ with hN
  have hNn : N.Normal := fixKer_normal ρ W₁ hW₁
  have := hT.simple
  have := hNn.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ψ) with h | h
  · refine false_of_rep_one hp5 ρ W₁ h₁ hW₁ hT ψ hψ fun y hy => ?_
    have hyN : y ∈ N := (mem_fixKer_iff ρ W₁ hW₁ y).mpr hy
    have : ψ y ∈ N.map ψ := ⟨y, hyN, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · have hs : Function.Surjective (ψ.comp N.subtype) := by
      intro t
      have ht : t ∈ N.map ψ := h ▸ Subgroup.mem_top t
      obtain ⟨y, hy, rfl⟩ := ht
      exact ⟨⟨y, hy⟩, rfl⟩
    refine false_of_rep_two hp5 (ρ.comp N.subtype) W₂ W₃ h₂ h₃ (fun y => hW₂ y)
      (fun y => hW₃ y) hT _ hs fun y hy₂ hy₃ => ?_
    exact hker y ((mem_fixKer_iff ρ W₁ hW₁ y).mp y.2) hy₂ hy₃

end Rep

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
