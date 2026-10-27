module

public import CFSG.Quasithin.Background.C35InspA8D
public import CFSG.Quasithin.Background.C35InspA8A
public import CFSG.Quasithin.Background.C35InspA8C
public import CFSG.Quasithin.Background.C35InspL45D

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A]

theorem shape_a8T23 : Shape 3 3 a8T23 := by
  refine ⟨fun i j hj => ?_, fun i j hi => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp_all [a8T23]

theorem shape_a8T01 : Shape 1 1 a8T01 := by
  refine ⟨fun i j hj => ?_, fun i j hi => ?_⟩ <;> fin_cases i <;> fin_cases j <;> simp_all [a8T01]

theorem colC_a8T23 (h0 : 0 + 3 ≤ 4) :
    restrictBlk 0 3 h0 (colC a8T23 ⟨3, by omega⟩) = Pi.single 2 1 := by
  revert h0
  decide +kernel

theorem rowC_a8T01 (h1 : 1 + 3 ≤ 4) :
    restrictBlk 1 3 h1 (rowC a8T01 ⟨0, by omega⟩) = Pi.single 0 1 := by
  revert h1
  decide +kernel

theorem a8G0SL_eq_nat (h0 : 0 + 3 ≤ 4) :
    a8G0SL = liftT 0 3 h0 (show (0 : Fin 3) ≠ 1 by decide) *
      SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 3 by decide) (1 : ZMod 2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_liftT, CFSG.LinearGroups.coe_transvection]
  revert h0
  decide +kernel

theorem a8G0SL_eq_dual (h1 : 1 + 3 ≤ 4) :
    a8G0SL = SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) (1 : ZMod 2) *
      liftT 1 3 h1 (show (1 : Fin 3) ≠ 2 by decide) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_liftT, CFSG.LinearGroups.coe_transvection]
  revert h1
  decide +kernel

omit [Finite A] in
theorem cover_data {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V)
    (hc2 : Nat.card ↥(Subgroup.center ↥K) = 2)
    (θ : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hθs : Function.Surjective θ)
    (hθker : θ.ker = Subgroup.center ↥K) :
    ∃ z : ↥K, z ∈ Subgroup.center ↥K ∧ θ z = 1 ∧ (∀ y, θ y = 1 → y = 1 ∨ y = z) ∧
      z * z = 1 ∧ z ≠ 1 ∧ commutator ↥K = ⊤ ∧ 20160 < Nat.card ↥K := by
  obtain ⟨⟨z, hz⟩, hz1, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥K))).mp hc2
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hθz : θ z = 1 := by
    rw [← MonoidHom.mem_ker, hθker]
    exact hz
  have hker : ∀ y, θ y = 1 → y = 1 ∨ y = z := fun y hy => by
    have hyc : y ∈ Subgroup.center ↥K := by
      rw [← hθker]
      exact hy
    by_cases h1 : y = 1
    · exact Or.inl h1
    · right
      have := hzuniq ⟨y, hyc⟩ (fun h => h1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  have hzz : z * z = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥K)) (x := ⟨z, hz⟩)
    rw [hc2] at h
    have h2 := congrArg Subtype.val h
    simpa [pow_two] using h2
  have hcard : Nat.card ↥K = 2 * 20160 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    rw [← hθker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv,
      hθker, hc2, ← Nat.card_congr (glEquivSL 4).toEquiv,
      CFSG.GH74.Exceptional.card_GL_four_two] at h1
    omega
  exact ⟨z, hz, hθz, hker, hzz, hz1', hD.quasisimple.1, by omega⟩

omit [Finite A] in
theorem commutator_coe {K : Subgroup A} (x y : ↥K) :
    ((⁅x, y⁆ : ↥K) : A) = ⁅(x : A), (y : A)⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  rfl

theorem a8_nat {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc2 : Nat.card ↥(Subgroup.center ↥K) = 2) {I : Set ℕ} (h0 : 0 + 3 ≤ 4)
    (hno : ∀ c ∈ I, ¬ (0 < c ∧ c < 0 + 3))
    (θ : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hθs : Function.Surjective θ)
    (hθker : θ.ker = Subgroup.center ↥K)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 0 3 h0 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hcross : ∀ (k l : Fin 4) (hkl : IsCross 0 3 k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))
    (hM : img θ M₀ = perfectCore (flagStabilizer 4 (ZMod 2) I)) :
    centerOf K = V ⊓ Subgroup.centralizer (M₀ : Set A) ∧ IsB48TwoModule M₀ V := by
  classical
  obtain ⟨z, hz, hθz, hker2, hzz, hz1, hperf, hcardK⟩ := cover_data hD hc2 θ hθs hθker
  set j₀ : Fin 4 := ⟨3, by omega⟩ with hj₀
  have hsh : ∀ v : ↥V, Shape 3 3 (mV hD hM₀K θ v) := fun v => by
    obtain ⟨-, -, hcc, hd⟩ := data_of_mem hD hM₀K h0 θ α hker hblk hcross v.2
    exact ⟨fun i j hj => col_std hcc hd j (Or.inr ⟨by omega, by omega, by omega⟩) i,
      fun i j hi => row_std hcc hd i (Or.inr ⟨by omega, by omega⟩) j⟩
  have hcol0 : ∀ (v : ↥V) (i : Fin 4), 3 ≤ (i : ℕ) → colC (mV hD hM₀K θ v) j₀ i = 0 :=
    fun v i hi => colC_eq_zero (hsh v) j₀ i hi
  let β : ↥V →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (restrictBlk 0 3 h0 (colC (mV hD hM₀K θ v) j₀))
      map_one' := by
        rw [mV_one]
        apply Multiplicative.toAdd.injective
        funext i
        simp [colC, restrictBlk]
      map_mul' := fun u v => by
        rw [mV_mul, colC_mul (hsh u) (hsh v)]
        rfl }
  have hβv : ∀ v, Multiplicative.toAdd (β v) = restrictBlk 0 3 h0 (colC (mV hD hM₀K θ v) j₀) :=
    fun v => rfl
  have hinvM : ∀ x : ↥M₀, ((θ ⟨x, hM₀K x.2⟩)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) =
      θ ⟨(x⁻¹ : ↥M₀), hM₀K x⁻¹.2⟩ := fun x => by rw [← map_inv]; rfl
  have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u) := by
    intro a u v huv
    have hg : BlockForm 0 3 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
      rw [hinvM]
      exact (hblk a⁻¹).2
    rw [hβv, hβv, mV_conj hD hM₀K θ a u v huv, colC_conj _ hg (hsh u) j₀ le_rfl,
      ← (hblk a).1]
    exact (mulVec_of_blockForm_blk h0 (hblk a).2 fun j hj => by
      rcases hj with hj | hj
      · omega
      · exact hcol0 u j (by omega)).2
  have hβθ : ∀ v : ↥V, β v = 1 ↔ θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := by
    intro v
    constructor
    · intro hv
      have h1 : colC (mV hD hM₀K θ v) j₀ = colC 1 j₀ := by
        refine eq_of_restrictBlk h0 (hcol0 v) (fun i _ => by simp [colC]) ?_
        have := congrArg Multiplicative.toAdd hv
        rw [hβv] at this
        rw [this]
        funext i
        simp [colC, restrictBlk]
      have h2 : mV hD hM₀K θ v = 1 := eq_of_colC (hsh v) shape_one fun j hj => by
        have : j = j₀ := Fin.ext (by simp [hj₀]; omega)
        rw [this, h1]
      exact Subtype.ext h2
    · intro hv
      have h2 : mV hD hM₀K θ v = 1 := by
        show ((θ ⟨v, hM₀K (hD.V_le v.2)⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1
        rw [hv, Matrix.SpecialLinearGroup.coe_one]
      apply Multiplicative.toAdd.injective
      rw [hβv, h2]
      funext i
      simp [colC, restrictBlk]
  have hMV := le_normalizer_of_comm hD.V_comm
  have hβs := beta_surjective (by norm_num) hMV α hαs β hequiv
    (exists_beta_ne_one hD hM₀K θ hθker β hβθ)
  have hO : ∀ y : ↥M₀, α y = 1 → ∃ v : ↥V, θ ⟨v, hM₀K (hD.V_le v.2)⟩ = θ ⟨y, hM₀K y.2⟩ := by
    intro y hy'
    have hb := (hblk y).1
    rw [hy', Matrix.SpecialLinearGroup.coe_one] at hb
    have hshy := shape_of_blockForm h0 (hblk y).2 hb
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (restrictBlk 0 3 h0
      (colC ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) j₀)))
    have h1 : colC (mV hD hM₀K θ v) j₀ = colC ((θ ⟨y, hM₀K y.2⟩ :
        SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) j₀ :=
      eq_of_restrictBlk h0 (hcol0 v) (fun i hi => colC_eq_zero hshy j₀ i hi)
        (congrArg Multiplicative.toAdd hv)
    have h2 : mV hD hM₀K θ v = ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) := eq_of_colC (hsh v) hshy fun j hj => by
      have : j = j₀ := Fin.ext (by simp [hj₀]; omega)
      rw [this, h1]
    exact ⟨v, Subtype.ext h2⟩
  obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (Pi.single 2 1))
  have hmv : mV hD hM₀K θ v = a8T23 := by
    refine eq_of_colC (hsh v) shape_a8T23 fun j hj => ?_
    have hj3 : j = j₀ := Fin.ext (by simp [hj₀]; omega)
    rw [hj3]
    refine eq_of_restrictBlk h0 (hcol0 v) (fun i hi => colC_eq_zero shape_a8T23 j₀ i hi) ?_
    rw [← hβv, hv]
    exact (colC_a8T23 h0).symm
  have hvT : θ ⟨v, hM₀K (hD.V_le v.2)⟩ = a8T23SL := Subtype.ext hmv
  have hv1 : (⟨v, hM₀K (hD.V_le v.2)⟩ : ↥K) * ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := by
    apply Subtype.ext
    have := hD.V_elem.2 v v.2
    simpa [pow_two] using this
  have hmem : a8G0SL ∈ img θ M₀ := by
    rw [hM, a8G0SL_eq_nat h0]
    exact mul_mem (liftT_mem_perfectCore h0 (by norm_num) hno _)
      (transvection_mem_perfectCore h0 (by norm_num) hno
        (show IsCross 0 3 (2 : Fin 4) 3 from Or.inr ⟨by norm_num, by norm_num, by norm_num⟩))
  obtain ⟨m, hm, hmg⟩ := hmem
  have hT23 : SqOne θ a8T23SL := sqOne_of_lift hz hker2 hzz hvT hv1
  have htg : a8T23SL * a8G0SL = a8G0SL * a8T23SL := Subtype.ext a8_mat_facts.2.2.2.2.2.1
  have htg1 : SqOne θ (a8T23SL * a8G0SL) := by
    have e : a8T23SL * a8G0SL = a8T01SL := Subtype.ext a8_mat_facts.2.2.2.2.2.2.2.1
    rw [e]
    exact (sqOne_a8T01_iff hθs).2 hT23
  have hcz := commutator_eq_z_of_lifts hθs hz hθz hker2 hzz hz1 hperf hcardK htg htg1 hvT hmg hv1
  have hm' : (m : A) ∈ M₀ := Subgroup.mem_subgroupOf.1 hm
  have hzA : ⁅(v : A), (m : A)⁆ = (z : A) := by
    have := congrArg Subtype.val hcz
    rw [commutator_coe] at this
    exact this
  refine b48_of_coords hD hM₀K θ hθker hc2 α hαs hker β hequiv hβθ hβs hO v.2 hm' ?_ ?_
  · rw [hzA]
    exact fun h => hz1 (Subtype.ext h)
  · rw [hzA]
    exact mem_centerOf_iff.2 hz

theorem a8_dual {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc2 : Nat.card ↥(Subgroup.center ↥K) = 2) {I : Set ℕ} (h1 : 1 + 3 ≤ 4)
    (hno : ∀ c ∈ I, ¬ (1 < c ∧ c < 1 + 3))
    (θ : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hθs : Function.Surjective θ)
    (hθker : θ.ker = Subgroup.center ↥K)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 1 3 h1 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 1 3 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hcross : ∀ (k l : Fin 4) (hkl : IsCross 1 3 k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))
    (hM : img θ M₀ = perfectCore (flagStabilizer 4 (ZMod 2) I)) :
    centerOf K = V ⊓ Subgroup.centralizer (M₀ : Set A) ∧ IsB48TwoModule M₀ V := by
  classical
  obtain ⟨z, hz, hθz, hker2, hzz, hz1, hperf, hcardK⟩ := cover_data hD hc2 θ hθs hθker
  have hmn : 1 + 3 = 4 := rfl
  set i₀ : Fin 4 := ⟨0, by omega⟩ with hi₀
  have hsh : ∀ v : ↥V, Shape 1 1 (mV hD hM₀K θ v) := fun v => by
    obtain ⟨-, -, hcc, hd⟩ := data_of_mem hD hM₀K h1 θ α hker hblk hcross v.2
    exact ⟨fun i j hj => col_std hcc hd j (Or.inl ⟨hj, by omega, by omega⟩) i,
      fun i j hi => row_std hcc hd i (Or.inl ⟨hi, by omega, by omega⟩) j⟩
  have hrow0 : ∀ (v : ↥V) (j : Fin 4), (j : ℕ) < 1 → rowC (mV hD hM₀K θ v) i₀ j = 0 :=
    fun v j hj => rowC_eq_zero (hsh v) i₀ j hj
  let β : ↥V →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (restrictBlk 1 3 h1 (rowC (mV hD hM₀K θ v) i₀))
      map_one' := by
        rw [mV_one]
        apply Multiplicative.toAdd.injective
        funext i
        simp [rowC, restrictBlk]
      map_mul' := fun u v => by
        rw [mV_mul, rowC_mul (hsh u) (hsh v)]
        rfl }
  have hβv : ∀ v, Multiplicative.toAdd (β v) = restrictBlk 1 3 h1 (rowC (mV hD hM₀K θ v) i₀) :=
    fun v => rfl
  have hinvM : ∀ x : ↥M₀, ((θ ⟨x, hM₀K x.2⟩)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) =
      θ ⟨(x⁻¹ : ↥M₀), hM₀K x⁻¹.2⟩ := fun x => by rw [← map_inv]; rfl
  set α' : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (CFSG.Quasithin.JonesParshall.invTransposeSL 3 (ZMod 2)).toMonoidHom.comp α with hα'
  have hα's : Function.Surjective α' :=
    (CFSG.Quasithin.JonesParshall.invTransposeSL 3 (ZMod 2)).surjective.comp hαs
  have hker' : α'.ker = CFSG.pCore 2 ↥M₀ := by
    rw [← hker]
    ext x
    simp only [hα', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α' a : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u) := by
    intro a u v huv
    have hg : ∀ i j : Fin 4, (i : ℕ) < 1 → (j : ℕ) < 1 →
        ((θ ⟨a, hM₀K a.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = if i = j then 1 else 0 :=
      fun i j hi hj => (hblk a).2.2.2.1 i j hi hj
    have hbf : BlockForm 1 3 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
      rw [hinvM]
      exact (hblk a⁻¹).2
    have hbl : blkAt 1 3 h1 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = (((α a)⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [hinvM, (hblk a⁻¹).1, map_inv]
    show _ = (((α a)⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ _
    rw [hβv, hβv, mV_conj hD hM₀K θ a u v huv, rowC_conj _ hg (hsh u) i₀ (by simp [hi₀]),
      ← hbl]
    exact (transpose_mulVec_of_blockForm_blk h1 hbf fun j hj => by
      rcases hj with hj | hj
      · exact hrow0 u j hj
      · omega).2
  have hβθ : ∀ v : ↥V, β v = 1 ↔ θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := by
    intro v
    constructor
    · intro hv
      have h2 : rowC (mV hD hM₀K θ v) i₀ = rowC 1 i₀ := by
        refine eq_of_restrictBlk_last h1 hmn (hrow0 v) (fun j _ => by simp [rowC]) ?_
        have := congrArg Multiplicative.toAdd hv
        rw [hβv] at this
        rw [this]
        funext i
        simp [rowC, restrictBlk]
      have h3 : mV hD hM₀K θ v = 1 := eq_of_rowC (hsh v) shape_one fun i hi => by
        have : i = i₀ := Fin.ext (by simp [hi₀]; omega)
        rw [this, h2]
      exact Subtype.ext h3
    · intro hv
      have h2 : mV hD hM₀K θ v = 1 := by
        show ((θ ⟨v, hM₀K (hD.V_le v.2)⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1
        rw [hv, Matrix.SpecialLinearGroup.coe_one]
      apply Multiplicative.toAdd.injective
      rw [hβv, h2]
      funext i
      simp [rowC, restrictBlk]
  have hMV := le_normalizer_of_comm hD.V_comm
  have hβs := beta_surjective (by norm_num) hMV α' hα's β hequiv
    (exists_beta_ne_one hD hM₀K θ hθker β hβθ)
  have hO : ∀ y : ↥M₀, α' y = 1 → ∃ v : ↥V, θ ⟨v, hM₀K (hD.V_le v.2)⟩ = θ ⟨y, hM₀K y.2⟩ := by
    intro y hy'
    have hy : α y = 1 := by
      have : y ∈ α'.ker := hy'
      rw [hker', ← hker] at this
      exact this
    have hb := (hblk y).1
    rw [hy, Matrix.SpecialLinearGroup.coe_one] at hb
    have hshy := shape_of_blockForm_last h1 hmn (hblk y).2 hb
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (restrictBlk 1 3 h1
      (rowC ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) i₀)))
    have h2 : rowC (mV hD hM₀K θ v) i₀ = rowC ((θ ⟨y, hM₀K y.2⟩ :
        SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i₀ :=
      eq_of_restrictBlk_last h1 hmn (hrow0 v) (fun j hj => rowC_eq_zero hshy i₀ j hj)
        (congrArg Multiplicative.toAdd hv)
    have h3 : mV hD hM₀K θ v = ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) := eq_of_rowC (hsh v) hshy fun i hi => by
      have : i = i₀ := Fin.ext (by simp [hi₀]; omega)
      rw [this, h2]
    exact ⟨v, Subtype.ext h3⟩
  obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hmv : mV hD hM₀K θ v = a8T01 := by
    refine eq_of_rowC (hsh v) shape_a8T01 fun i hi => ?_
    have hi0 : i = i₀ := Fin.ext (by simp [hi₀]; omega)
    rw [hi0]
    refine eq_of_restrictBlk_last h1 hmn (hrow0 v) (fun j hj => rowC_eq_zero shape_a8T01 i₀ j hj) ?_
    rw [← hβv, hv]
    exact (rowC_a8T01 h1).symm
  have hvT : θ ⟨v, hM₀K (hD.V_le v.2)⟩ = a8T01SL := Subtype.ext hmv
  have hv1 : (⟨v, hM₀K (hD.V_le v.2)⟩ : ↥K) * ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := by
    apply Subtype.ext
    have := hD.V_elem.2 v v.2
    simpa [pow_two] using this
  have hmem : a8G0SL ∈ img θ M₀ := by
    rw [hM, a8G0SL_eq_dual h1]
    exact mul_mem (transvection_mem_perfectCore h1 (by norm_num) hno
        (show IsCross 1 3 (0 : Fin 4) 1 from Or.inl ⟨by norm_num, by norm_num, by norm_num⟩))
      (liftT_mem_perfectCore h1 (by norm_num) hno _)
  obtain ⟨m, hm, hmg⟩ := hmem
  have hT01 : SqOne θ a8T01SL := sqOne_of_lift hz hker2 hzz hvT hv1
  have htg : a8T01SL * a8G0SL = a8G0SL * a8T01SL := Subtype.ext a8_mat_facts.2.2.2.2.2.2.1
  have htg1 : SqOne θ (a8T01SL * a8G0SL) := by
    have e : a8T01SL * a8G0SL = a8T23SL := Subtype.ext a8_mat_facts.2.2.2.2.2.2.2.2.1
    rw [e]
    exact (sqOne_a8T01_iff hθs).1 hT01
  have hcz := commutator_eq_z_of_lifts hθs hz hθz hker2 hzz hz1 hperf hcardK htg htg1 hvT hmg hv1
  have hm' : (m : A) ∈ M₀ := Subgroup.mem_subgroupOf.1 hm
  have hzA : ⁅(v : A), (m : A)⁆ = (z : A) := by
    have := congrArg Subtype.val hcz
    rw [commutator_coe] at this
    exact this
  refine b48_of_coords hD hM₀K θ hθker hc2 α' hα's hker' β hequiv hβθ hβs hO v.2 hm' ?_ ?_
  · rw [hzA]
    exact fun h => hz1 (Subtype.ext h)
  · rw [hzA]
    exact mem_centerOf_iff.2 hz

theorem isQuasisimple_of_open_alt8 {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    CFSG.IsQuasisimple X := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsimp := h.2
  have htop : commutator (X ⧸ Subgroup.center X) = ⊤ := by
    rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _), ← h.1, commutator_def, commutator_def,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hbot : commutator (X ⧸ Subgroup.center X) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcon y x
  rw [htop] at hbot
  obtain ⟨a, b, hab⟩ := hsimp.toNontrivial.exists_pair_ne
  apply hab
  have ha : a ∈ (⊥ : Subgroup (X ⧸ Subgroup.center X)) := hbot ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup (X ⧸ Subgroup.center X)) := hbot ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem a8cover_holds : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A),
    C35Data K Y M₀ V → Nat.card ↥(Subgroup.center ↥K) = 2 →
    (IsPSL 4 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 8 (↥K ⧸ Subgroup.center ↥K)) →
    C35Concl10 K M₀ V := by
  intro A _ _ K Y M₀ V hD hc2 hfam
  classical
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hD.parabolic.1
  obtain ⟨e, e'⟩ : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥(alternatingGroup (Fin 8))) := by
    obtain ⟨φ, -⟩ := CFSG.Quasithin.exists_iso_alt8_carm
    rcases hfam with h | h
    · obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two h
      exact ⟨⟨e⟩, ⟨e.trans ((glEquivSL 4).symm.trans φ.symm)⟩⟩
    · obtain ⟨e⟩ := h
      exact ⟨⟨(e.trans φ).trans (glEquivSL 4)⟩, ⟨e⟩⟩
  obtain ⟨e⟩ := e
  set ψ : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hψ
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Subgroup.center ↥K := by
    ext x
    simp only [hψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨g, I, a, m, h, α, hm3, ha, hb, hno, hIc, hprop, -, hM, hαs, hker, hblk, hcross⟩ :=
    config_cov hD hM₀K (n := 4) (by norm_num) (by norm_num) ψ hψs hψker.le
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hθ
  have hθs : Function.Surjective θ := (MulAut.conj g⁻¹).surjective.comp hψs
  have hθker : θ.ker = Subgroup.center ↥K := by
    rw [← hψker]
    ext x
    simp only [hθ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hm3' : m = 3 := by omega
  subst hm3'
  have hconcl : centerOf K = V ⊓ Subgroup.centralizer (M₀ : Set A) ∧ IsB48TwoModule M₀ V := by
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · exact a8_nat hD hM₀K hc2 h hno θ hθs hθker α hαs hker hblk hcross hM
    · exact a8_dual hD hM₀K hc2 h hno θ hθs hθker α hαs hker hblk hcross hM
  exact ⟨⟨isQuasisimple_of_open_alt8 hD.quasisimple, hc2, e'⟩, hconcl⟩

end CFSG.Quasithin.C35Pf
