module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaSUPiece

public section

namespace CFSG.StandardType

namespace NoOffOm

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB Multiplicative

section Frame

variable {f n : ℕ} {K : Type} [Field K] {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

@[expose] def fixOn (f n : ℕ) (K : Type) [Field K] (W : Set (Fin n → K)) :
    Subgroup ↥(unitarySU 2 f K n) where
  carrier := {c | ∀ u ∈ W, lin c u = u}
  mul_mem' {c d} hc hd u hu := by
    rw [lin_mul, Module.End.mul_apply, hd u hu, hc u hu]
  one_mem' u _ := by rw [lin_one]; rfl
  inv_mem' {c} hc u hu := by
    have h1 : lin c⁻¹ (lin c u) = u := by
      rw [← Module.End.mul_apply, ← lin_mul, inv_mul_cancel, lin_one]
      rfl
    rwa [hc u hu] at h1

theorem mem_fixOn {W : Set (Fin n → K)} {c : ↥(unitarySU 2 f K n)} :
    c ∈ fixOn f n K W ↔ ∀ u ∈ W, lin c u = u :=
  Iff.rfl

theorem eq_zero_of_pow_fix (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A)
    {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) {k : ℕ} (hk : ¬ p ∣ k) {u : Fin n → K}
    (hu : u ∈ rng y) (hfix : lin (y ^ k) u = u) : u = 0 := by
  have hcop : Nat.Coprime k p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hA.prime).mpr hk)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hA.prime.one_lt
  have hiter : ∀ j : ℕ, lin (y ^ (k * j)) u = u := by
    intro j
    induction j with
    | zero => rw [Nat.mul_zero, pow_zero, lin_one]; rfl
    | succ j ih => rw [Nat.mul_succ, pow_add, lin_mul, Module.End.mul_apply, hfix, ih]
  have hy1 : y ^ (k * m) = y := by
    rw [pow_eq_pow_mod (k * m) (hA.pow y hy), hm, pow_one]
  have h1 := hiter m
  rw [hy1] at h1
  exact eq_zero_of_mem_rng h hA hy hu h1

theorem exists_pieceFrame [FiniteDimensional K (Fin n → K)] (h : UnitaryFieldData 2 f K)
    (hA : MaxElemAb p A) :
    ∃ (r : ℕ) (ι₀ : Multiplicative (Fin r → ZMod p) →* ↥(unitarySU 2 f K n)),
      Function.Injective ι₀ ∧ ι₀.range = A ∧
        ∀ s s' : Fin r → ZMod p,
          ((∀ v, lin (ι₀ (ofAdd s')) v = v → lin (ι₀ (ofAdd s)) v = v) ↔ SuppLE s s') := by
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  obtain ⟨S, hS, hterm⟩ := exists_terminal_pieceSet (h := h) hA
  set r := S.card with hr
  set e : Fin r ≃ ↥S := S.equivFin.symm with he
  set y : Fin r → ↥(unitarySU 2 f K n) := fun i => (e i : ↥(unitarySU 2 f K n)) with hy
  have hyS : ∀ i, y i ∈ S := fun i => (e i).2
  have hyA : ∀ i, y i ∈ A := fun i => hS.mem _ (hyS i)
  have hyinj : Function.Injective y := fun i j hij => e.injective (Subtype.ext hij)
  have hyS' : ∀ z ∈ S, ∃ i, y i = z := fun z hz =>
    ⟨e.symm ⟨z, hz⟩, by simp only [hy, Equiv.apply_symm_apply]⟩
  set U : Fin r → Submodule K (Fin n → K) := fun i => rng (y i) with hU
  have hUnd : ∀ i, NondegOn (stdHermForm h n) (U i) := fun i => nondegOn_rng hA (hyA i)
  have hUA : ∀ i, ∀ a ∈ A, ∀ u ∈ U i, lin a u ∈ U i := fun i a ha => rng_inv hA (hyA i) ha
  have hUorth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, stdHermForm h n u v = 0 :=
    fun i j hij => hS.orth _ (hyS i) _ (hyS j) (fun e' => hij (hyinj e'))
  have hUne : ∀ i, ∃ u ∈ U i, u ≠ 0 := fun i =>
    (Submodule.ne_bot_iff _).mp (rng_ne_bot (hS.ne_one _ (hyS i)))
  have hUperp : ∀ j, ∀ u ∈ U j, u ∈ (U j).orthogonalBilin (stdHermForm h n) → u = 0 :=
    fun j u hu hu' => hUnd j u hu fun m hm => (Submodule.mem_orthogonalBilin.mp hu') m hm
  have hUsub : ∀ i j, i ≠ j → ∀ u ∈ U j, u ∈ (U i).orthogonalBilin (stdHermForm h n) :=
    fun i j hij u hu => Submodule.mem_orthogonalBilin.mpr fun m hm => hUorth i j hij m hm u hu
  have hb : ∀ i, ∃ g ∈ A, (∀ w ∈ U i, lin g w = lin (y i) w) ∧
      ∀ v ∈ (U i).orthogonalBilin (stdHermForm h n), lin g v = v :=
    fun i => exists_mem_restrict h hA (hUnd i) (hUA i) (hyA i)
  choose b hbA hbon hboff using hb
  have hbpow : ∀ j (k : ℕ), ∀ u ∈ U j, lin (b j ^ k) u = lin (y j ^ k) u := by
    intro j k
    induction k with
    | zero => intro u _; rw [pow_zero, pow_zero]
    | succ k ih =>
      intro u hu
      have hyk : lin (y j ^ k) u ∈ U j := hUA j _ (A.pow_mem (hyA j) k) u hu
      rw [pow_succ', lin_mul, Module.End.mul_apply, ih u hu, hbon j _ hyk, ← Module.End.mul_apply,
        ← lin_mul, ← pow_succ']
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a c => Subtype.ext (hA.comm _ a.2 _ c.2) }
  set bA : Fin r → A := fun i => ⟨b i, hbA i⟩ with hbA'
  have hbAp : ∀ i, bA i ^ p = 1 := fun i => Subtype.ext (hA.pow _ (hbA i))
  set ι₁ : Multiplicative (Fin r → ZMod p) →* A :=
    { toFun := fun s => ∏ i, bA i ^ (toAdd s i).val
      map_one' := by simp
      map_mul' := fun s s' => by
        simp only [toAdd_mul, Pi.add_apply]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [ZMod.val_add, ← pow_eq_pow_mod _ (hbAp i), pow_add] } with hι₁
  have hι₁_apply : ∀ s, ι₁ s = ∏ i, bA i ^ (toAdd s i).val := fun s => rfl
  have hact : ∀ (s : Multiplicative (Fin r → ZMod p)) j, ∀ u ∈ U j,
      lin ((ι₁ s : A) : ↥(unitarySU 2 f K n)) u = lin (y j ^ (toAdd s j).val) u := by
    intro s j u hu
    have hrest : (∏ i ∈ Finset.univ.erase j, bA i ^ (toAdd s i).val) ∈
        (fixOn f n K (U j : Set (Fin n → K))).comap A.subtype := by
      refine Subgroup.prod_mem _ fun i hi => Subgroup.pow_mem _ ?_ _
      exact fun w hw => hboff i w (hUsub i j (Finset.ne_of_mem_erase hi) w hw)
    have hrest' : lin ((∏ i ∈ Finset.univ.erase j, bA i ^ (toAdd s i).val : A) :
        ↥(unitarySU 2 f K n)) u = u := hrest u hu
    rw [hι₁_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Subgroup.coe_mul, lin_mul,
      Module.End.mul_apply, hrest', SubgroupClass.coe_pow, hbpow j _ u hu]
  have hfix : ∀ (s : Multiplicative (Fin r → ZMod p)) (v : Fin n → K),
      lin ((ι₁ s : A) : ↥(unitarySU 2 f K n)) v = v ↔
        ∀ j, toAdd s j ≠ 0 → v ∈ (U j).orthogonalBilin (stdHermForm h n) := by
    intro s v
    constructor
    · intro hv j hj
      set g : ↥(unitarySU 2 f K n) := ((ι₁ s : A) : ↥(unitarySU 2 f K n)) with hg
      set k := (toAdd s j).val with hk
      have hkp : ¬ p ∣ k := by
        intro hdvd
        apply hj
        rw [← ZMod.natCast_zmod_val (toAdd s j), ← hk]
        exact (ZMod.natCast_eq_zero_iff k p).mpr hdvd
      have hmaps : ∀ x ∈ U j, (lin (y j ^ k) - 1) x ∈ U j := fun x hx =>
        (U j).sub_mem (hUA j _ (A.pow_mem (hyA j) k) x hx) hx
      set φ : Module.End K ↥(U j) := (lin (y j ^ k) - 1).restrict hmaps with hφ
      have hφinj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨x, hx⟩ hx0
        have h1 : (lin (y j ^ k) - 1) x = 0 := congrArg Subtype.val hx0
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
        exact Subtype.ext (eq_zero_of_pow_fix h hA (hyA j) hkp hx h1)
      have hφsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hφinj
      refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
      obtain ⟨⟨x, hx⟩, hxm⟩ := hφsurj ⟨m, hm⟩
      have hm' : m = lin g x - x := by
        have h1 : (lin (y j ^ k) - 1) x = m := by
          have h2 := congrArg Subtype.val hxm
          simpa only [hφ, LinearMap.restrict_apply] using h2
        rw [← h1, LinearMap.sub_apply, Module.End.one_apply, hg, hact s j x hx]
      change stdHermForm h n m v = 0
      rw [hm', map_sub, LinearMap.sub_apply, ← isometry_lin h g x v, hv, sub_self]
    · intro hv
      have hmem : ∀ i, bA i ^ (toAdd s i).val ∈ (fixOn f n K {v}).comap A.subtype := by
        intro i
        by_cases hi : toAdd s i = 0
        · rw [hi, ZMod.val_zero, pow_zero]
          exact Subgroup.one_mem _
        · refine Subgroup.pow_mem _ ?_ _
          intro w hw
          rw [Set.mem_singleton_iff.mp hw]
          exact hboff i v (hv i hi)
      have h1 := Subgroup.prod_mem _ fun i (_ : i ∈ Finset.univ) => hmem i
      rw [← hι₁_apply] at h1
      exact h1 v rfl
  have hinj₁ : Function.Injective ι₁ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, toAdd s j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (toAdd.injective (funext hcon))
    obtain ⟨u, hu, hu0⟩ := hUne j
    have h1 : lin ((ι₁ s : A) : ↥(unitarySU 2 f K n)) u = u := by
      rw [hs, OneMemClass.coe_one, lin_one]
      rfl
    exact hu0 (hUperp j u hu ((hfix s u).mp h1 j hj))
  have hrange₁ : ∀ c ∈ A, ∃ s, ((ι₁ s : A) : ↥(unitarySU 2 f K n)) = c := by
    intro c hc
    have hk : ∀ j, ∃ k : ℕ, ∀ u ∈ U j, lin c u = lin (y j ^ k) u :=
      fun j => hS.cyc _ (hyS j) c hc
    choose k hk using hk
    refine ⟨ofAdd fun j => (k j : ZMod p), ?_⟩
    set g : ↥(unitarySU 2 f K n) := ((ι₁ (ofAdd fun j => (k j : ZMod p)) : A) :
      ↥(unitarySU 2 f K n)) with hg
    have hgA : g ∈ A := (ι₁ _).2
    have hag : ∀ j, ∀ u ∈ U j, lin g u = lin c u := by
      intro j u hu
      rw [hg, hact _ j u hu, hk j u hu, toAdd_ofAdd, ZMod.val_natCast,
        ← pow_eq_pow_mod _ (hA.pow _ (hyA j))]
    have hle : pieceSpan S ≤ LinearMap.ker (lin (g⁻¹ * c) - 1) := by
      refine iSup₂_le fun z hz => ?_
      obtain ⟨j, rfl⟩ := hyS' z hz
      intro u hu
      have h1 : lin g⁻¹ (lin g u) = u := by
        rw [← Module.End.mul_apply, ← lin_mul, inv_mul_cancel, lin_one]
        rfl
      rw [LinearMap.mem_ker, LinearMap.sub_apply, lin_mul, Module.End.mul_apply, ← hag j u hu, h1,
        Module.End.one_apply, sub_self]
    have hc1 : g⁻¹ * c = 1 := hterm _ (A.mul_mem (A.inv_mem hgA) hc) fun v hv =>
      sub_eq_zero.mp (hle hv)
    exact (inv_mul_eq_one.mp hc1)
  refine ⟨r, A.subtype.comp ι₁, fun s t hst => hinj₁ (Subtype.ext hst), ?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact (ι₁ s).2
    · intro hc
      obtain ⟨s, hs⟩ := hrange₁ c hc
      exact ⟨s, hs⟩
  · intro s s'
    change ((∀ v, lin ((ι₁ (ofAdd s') : A) : ↥(unitarySU 2 f K n)) v = v →
      lin ((ι₁ (ofAdd s) : A) : ↥(unitarySU 2 f K n)) v = v) ↔ SuppLE s s')
    constructor
    · intro himp j hj
      by_contra hj'
      obtain ⟨u, hu, hu0⟩ := hUne j
      have h1 : lin ((ι₁ (ofAdd s') : A) : ↥(unitarySU 2 f K n)) u = u := by
        refine (hfix _ u).mpr fun i hi => hUsub i j (fun hij => hi ?_) u hu
        rw [hij]
        exact hj'
      exact hu0 (hUperp j u hu ((hfix _ u).mp (himp u h1) j hj))
    · intro hsupp v hv
      exact (hfix _ v).mpr fun j hj => (hfix _ v).mp hv j (hsupp j hj)

end Frame

end NoOffOm

end CFSG.StandardType
