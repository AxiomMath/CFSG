module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaSUFrame

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm Multiplicative

section PieceSet

open Classical

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

variable (h) in
@[expose] def MinPiece (A : Subgroup ↥(unitarySU 2 f K n)) (y : ↥(unitarySU 2 f K n)) : Prop :=
  ∀ W : Submodule K (Fin n → K), W ≤ rng y → W ≠ ⊥ → NondegOn (stdHermForm h n) W →
    (∀ a ∈ A, ∀ w ∈ W, lin a w ∈ W) → W = rng y

variable (h) in
structure IsMinPieceSet (A : Subgroup ↥(unitarySU 2 f K n)) (S : Finset ↥(unitarySU 2 f K n)) :
    Prop where
  pieceSet : IsPieceSet h A S
  minimal : ∀ y ∈ S, MinPiece h A y

theorem IsMinPieceSet.exists_insert [FiniteDimensional K (Fin n → K)] (hA : MaxElemAb p A)
    {S : Finset ↥(unitarySU 2 f K n)} (hS : IsMinPieceSet h A S)
    (hne : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ pieceSpan S, lin c v = v) :
    ∃ y, y ∉ S ∧ IsMinPieceSet h A (insert y S) := by
  obtain ⟨y, hy⟩ := exists_isPiece (h := h) hA hne
  have hyS : y ∉ S := by
    intro hyS
    apply rng_ne_bot hy.ne_one
    refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
    have hle : rng y ≤ pieceSpan S := le_iSup₂ (f := fun y _ => rng y) y hyS
    exact eq_zero_of_mem_rng h hA hy.mem hu (hy.triv u (hle hu))
  have horth := rng_orth_of_triv (h := h) hy.triv
  have hle : ∀ y' ∈ S, rng y' ≤ pieceSpan S := fun y' hy' =>
    le_iSup₂ (f := fun y _ => rng y) y' hy'
  refine ⟨y, hyS, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.mem
    · exact hS.pieceSet.mem y' hy'
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.ne_one
    · exact hS.pieceSet.ne_one y' hy'
  · intro y₁ hy₁ y₂ hy₂ hne₁₂ u hu v hv
    rcases Finset.mem_insert.mp hy₁ with rfl | h₁ <;>
      rcases Finset.mem_insert.mp hy₂ with rfl | h₂
    · exact absurd rfl hne₁₂
    · exact (horth u hu v (hle y₂ h₂ hv)).1
    · exact (horth v hv u (hle y₁ h₁ hu)).2
    · exact hS.pieceSet.orth y₁ h₁ y₂ h₂ hne₁₂ u hu v hv
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.cyc
    · exact hS.pieceSet.cyc y' hy'
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.minimal
    · exact hS.minimal y' hy'

theorem exists_terminal_minPieceSet [FiniteDimensional K (Fin n → K)] (hA : MaxElemAb p A) :
    ∃ S, IsMinPieceSet h A S ∧ ∀ c ∈ A, (∀ v ∈ pieceSpan S, lin c v = v) → c = 1 := by
  set P : ℕ → Prop := fun k => ∃ S, IsMinPieceSet h A S ∧ S.card = k with hP
  have hP0 : P 0 := ⟨∅, ⟨⟨by simp, by simp, by simp, by simp⟩, by simp⟩, rfl⟩
  have hbound : ∀ k, P k → k ≤ n := by
    rintro k ⟨S, hS, rfl⟩
    have h1 := (hS.pieceSet.nondegOn_card hA).2
    have h2 := Submodule.finrank_le (pieceSpan S)
    rw [Module.finrank_fin_fun] at h2
    omega
  set m := Nat.findGreatest P n with hm
  obtain ⟨S, hS, hSm⟩ : P m := Nat.findGreatest_spec (Nat.zero_le n) hP0
  refine ⟨S, hS, fun c hc htriv => ?_⟩
  by_contra hc1
  obtain ⟨y, hyS, hyS'⟩ := hS.exists_insert hA ⟨c, hc, hc1, htriv⟩
  have hPm : P (m + 1) := ⟨_, hyS', by rw [Finset.card_insert_of_notMem hyS, hSm]⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self m) (hbound _ hPm) hPm

end PieceSet

section Frame

variable {f n : ℕ} {K : Type} [Field K] {p : ℕ}

variable (f n K) in
structure PieceFrame (h : UnitaryFieldData 2 f K) (p : ℕ) (A : Subgroup ↥(unitarySU 2 f K n)) where
  r : ℕ
  y : Fin r → ↥(unitarySU 2 f K n)
  b : Fin r → ↥(unitarySU 2 f K n)
  ι : Multiplicative (Fin r → ZMod p) →* ↥(unitarySU 2 f K n)
  y_mem : ∀ i, y i ∈ A
  y_ne_one : ∀ i, y i ≠ 1
  b_mem : ∀ i, b i ∈ A
  orth : ∀ i j, i ≠ j → ∀ u ∈ rng (y i), ∀ v ∈ rng (y j), stdHermForm h n u v = 0
  cyc : ∀ i, ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ rng (y i), lin c u = lin (y i ^ k) u
  minimal : ∀ i, MinPiece h A (y i)
  b_on : ∀ i, ∀ u ∈ rng (y i), lin (b i) u = lin (y i) u
  b_off : ∀ i, ∀ v ∈ (rng (y i)).orthogonalBilin (stdHermForm h n), lin (b i) v = v
  ι_single : ∀ i, ι (ofAdd (Pi.single i 1)) = b i
  ι_on : ∀ s j, ∀ u ∈ rng (y j), lin (ι s) u = lin (y j ^ (toAdd s j).val) u
  ι_injective : Function.Injective ι
  ι_range : ι.range = A
  ι_fix : ∀ (s : Multiplicative (Fin r → ZMod p)) (v : Fin n → K), lin (ι s) v = v ↔
    ∀ j, toAdd s j ≠ 0 → v ∈ (rng (y j)).orthogonalBilin (stdHermForm h n)

theorem exists_pieceFrame' [FiniteDimensional K (Fin n → K)] (h : UnitaryFieldData 2 f K)
    {A : Subgroup ↥(unitarySU 2 f K n)} (hA : MaxElemAb p A) :
    Nonempty (PieceFrame f n K h p A) := by
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  have : Fact (1 < p) := ⟨hA.prime.one_lt⟩
  obtain ⟨S, hS, hterm⟩ := exists_terminal_minPieceSet (h := h) hA
  set r := S.card with hr
  set e : Fin r ≃ ↥S := S.equivFin.symm with he
  set y : Fin r → ↥(unitarySU 2 f K n) := fun i => (e i : ↥(unitarySU 2 f K n)) with hy
  have hyS : ∀ i, y i ∈ S := fun i => (e i).2
  have hyA : ∀ i, y i ∈ A := fun i => hS.pieceSet.mem _ (hyS i)
  have hyinj : Function.Injective y := fun i j hij => e.injective (Subtype.ext hij)
  have hyS' : ∀ z ∈ S, ∃ i, y i = z := fun z hz =>
    ⟨e.symm ⟨z, hz⟩, by simp only [hy, Equiv.apply_symm_apply]⟩
  set U : Fin r → Submodule K (Fin n → K) := fun i => rng (y i) with hU
  have hUnd : ∀ i, NondegOn (stdHermForm h n) (U i) := fun i => nondegOn_rng hA (hyA i)
  have hUA : ∀ i, ∀ a ∈ A, ∀ u ∈ U i, lin a u ∈ U i := fun i a ha => rng_inv hA (hyA i) ha
  have hUorth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, stdHermForm h n u v = 0 :=
    fun i j hij => hS.pieceSet.orth _ (hyS i) _ (hyS j) (fun e' => hij (hyinj e'))
  have hUne : ∀ i, ∃ u ∈ U i, u ≠ 0 := fun i =>
    (Submodule.ne_bot_iff _).mp (rng_ne_bot (hS.pieceSet.ne_one _ (hyS i)))
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
  have hsingle : ∀ i, ((ι₁ (ofAdd (Pi.single i 1)) : A) : ↥(unitarySU 2 f K n)) = b i := by
    intro i
    rw [hι₁_apply, Finset.prod_eq_single i (fun j _ hji => by
      simp [toAdd_ofAdd, Pi.single_eq_of_ne hji]) (fun h' => absurd (Finset.mem_univ i) h')]
    simp [toAdd_ofAdd, ZMod.val_one, hbA']
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
      fun j => hS.pieceSet.cyc _ (hyS j) c hc
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
  refine ⟨⟨r, y, b, A.subtype.comp ι₁, hyA, fun i => hS.pieceSet.ne_one _ (hyS i), hbA,
    hUorth, fun i => hS.pieceSet.cyc _ (hyS i), fun i => hS.minimal _ (hyS i), hbon, hboff,
    hsingle, hact, fun s t hst => hinj₁ (Subtype.ext hst), ?_, hfix⟩⟩
  ext c
  constructor
  · rintro ⟨s, rfl⟩
    exact (ι₁ s).2
  · intro hc
    obtain ⟨s, hs⟩ := hrange₁ c hc
    exact ⟨s, hs⟩

end Frame

end NsFrameComp

end CFSG.StandardType
