module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdentA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped TensorProduct commutatorElement

section LinearAlgebra

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [Module.Finite (ZMod 2) Y]

theorem s16c1610_end_eq_zero_or_id (hd : 2 ≤ Module.finrank (ZMod 2) Y)
    {φ : Y →ₗ[ZMod 2] Y}
    (hφ : ∀ τ : Y ≃ₗ[ZMod 2] Y, ∀ y, φ (τ y) = τ (φ y)) : φ = 0 ∨ φ = LinearMap.id :=
  CFSG.Quasithin.H13.Mult.eq_zero_or_eq_id_of_commute hd hφ

theorem s16c1610_exists_linearEquiv_apply_eq {y₀ y : Y} (hy₀ : y₀ ≠ 0) (hy : y ≠ 0) :
    ∃ τ : Y ≃ₗ[ZMod 2] Y, τ y₀ = y :=
  CFSG.Quasithin.H13.Mult.exists_linearEquiv_apply_eq hy₀ hy

end LinearAlgebra

section SumTwo

variable {W : Type} [CommGroup W] {Lb : Subgroup (MulAut W)} {m : ℕ}

private theorem s16c1610_iSup_ne_zero (I : Fin 2 → Subgroup W) :
    (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
  refine le_antisymm (iSup_le fun j => iSup_le fun hj => ?_) ?_
  · fin_cases j
    · exact absurd rfl hj
    · exact le_rfl
  · exact le_iSup₂ (f := fun j (_ : j ≠ 0) => I j) 1 (by decide)

private theorem s16c1610_iSup_two (I : Fin 2 → Subgroup W) :
    (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem s16c1610_sum_two_of_sumOfNat
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) Lb ⊤ ⊥ 2) :
    ∃ I : Fin 2 → Subgroup W, I 0 ⊓ I 1 = ⊥ ∧ I 0 ⊔ I 1 = ⊤ ∧
      (∀ i, BinaryNaturalSL Lb (I i) ⊥ m 1) := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := hsum
  refine ⟨I, ?_, ?_, hnat⟩
  · rw [eq_bot_iff]
    have h0 := hind 0
    rwa [s16c1610_iSup_ne_zero I, bot_sup_eq] at h0
  · rw [← s16c1610_iSup_two I]
    simpa using hsup

end SumTwo

section Direct

variable {W : Type} [CommGroup W] {Mb Kb Lb : Subgroup (MulAut W)}

theorem s16c1610_commute_of_commutator_eq_bot (hdir : IsInternalDirect Kb Lb Mb) :
    ∀ k ∈ Kb, ∀ l ∈ Lb, k * l = l * k := by
  have hle : Kb ≤ Subgroup.centralizer (Lb : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hdir.1
  intro k hk l hl
  exact (Subgroup.mem_centralizer_iff.1 (hle hk) l hl).symm

theorem s16c1610_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have hba : b * a' = a' * b := (hc a' ha' b hb).eq.symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hba]
      _ = a * a' * (b * b') := by group
  | inv y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have hba : b * a = a * b := (hc a ha b hb).eq.symm
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hba]

theorem s16c1610_mem_sup_prod (hdir : IsInternalDirect Kb Lb Mb) {x : MulAut W}
    (hx : x ∈ Mb) : ∃ k ∈ Kb, ∃ l ∈ Lb, x = k * l := by
  have hx' : x ∈ Kb ⊔ Lb := by
    rw [hdir.2.2]
    exact hx
  exact s16c1610_mem_sup_of_commute
    (s16c1610_commute_of_commutator_eq_bot hdir) hx'

theorem s16c1610_prod_unique (hdir : IsInternalDirect Kb Lb Mb)
    {k k' l l' : MulAut W} (hk : k ∈ Kb) (hl : l ∈ Lb) (hk' : k' ∈ Kb) (hl' : l' ∈ Lb)
    (h : k * l = k' * l') : k = k' ∧ l = l' := by
  have hmem : k'⁻¹ * k = l' * l⁻¹ := by
    calc k'⁻¹ * k = k'⁻¹ * k * 1 := by rw [mul_one]
      _ = k'⁻¹ * k * (l * l⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = k'⁻¹ * (k * l) * l⁻¹ := by group
      _ = k'⁻¹ * (k' * l') * l⁻¹ := by rw [h]
      _ = l' * l⁻¹ := by group
  have hK : k'⁻¹ * k ∈ Kb := Subgroup.mul_mem Kb (Subgroup.inv_mem Kb hk') hk
  have hL : l' * l⁻¹ ∈ Lb := Subgroup.mul_mem Lb hl' (Subgroup.inv_mem Lb hl)
  have hbot : k'⁻¹ * k ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← hdir.2.1]
    exact Subgroup.mem_inf.2 ⟨hK, hmem ▸ hL⟩
  have h1 : k'⁻¹ * k = 1 := Subgroup.mem_bot.1 hbot
  have hk_eq : k = k' := by
    calc k = k' * (k'⁻¹ * k) := by group
      _ = k' * 1 := by rw [h1]
      _ = k' := mul_one k'
  refine ⟨hk_eq, ?_⟩
  rw [hk_eq] at h
  exact mul_left_cancel h

private noncomputable def s16c1610_prodFst (hdir : IsInternalDirect Kb Lb Mb) (x : ↥Mb) :
    ↥Kb :=
  ⟨Classical.choose (s16c1610_mem_sup_prod hdir x.2),
    (Classical.choose_spec (s16c1610_mem_sup_prod hdir x.2)).1⟩

private noncomputable def s16c1610_prodSnd (hdir : IsInternalDirect Kb Lb Mb) (x : ↥Mb) :
    ↥Lb :=
  ⟨Classical.choose (Classical.choose_spec (s16c1610_mem_sup_prod hdir x.2)).2,
    (Classical.choose_spec
      (Classical.choose_spec (s16c1610_mem_sup_prod hdir x.2)).2).1⟩

private theorem s16c1610_prodFst_mul_prodSnd (hdir : IsInternalDirect Kb Lb Mb) (x : ↥Mb) :
    (s16c1610_prodFst hdir x : MulAut W) * (s16c1610_prodSnd hdir x : MulAut W) =
      (x : MulAut W) :=
  (Classical.choose_spec
    (Classical.choose_spec (s16c1610_mem_sup_prod hdir x.2)).2).2.symm

noncomputable def s16c1610_prodEquiv (hdir : IsInternalDirect Kb Lb Mb) :
    ↥Mb ≃* ↥Kb × ↥Lb where
  toFun x := (s16c1610_prodFst hdir x, s16c1610_prodSnd hdir x)
  invFun p := ⟨(p.1 : MulAut W) * (p.2 : MulAut W),
    Subgroup.mul_mem Mb ((hdir.2.2 ▸ Subgroup.mem_sup_left p.1.2))
      ((hdir.2.2 ▸ Subgroup.mem_sup_right p.2.2))⟩
  left_inv x := Subtype.ext (s16c1610_prodFst_mul_prodSnd hdir x)
  right_inv p := by
    rcases p with ⟨k, l⟩
    have hfst : s16c1610_prodFst hdir
        (⟨(k : MulAut W) * (l : MulAut W),
          Subgroup.mul_mem Mb (hdir.2.2 ▸ Subgroup.mem_sup_left k.2)
            (hdir.2.2 ▸ Subgroup.mem_sup_right l.2)⟩ : ↥Mb) = k := by
      apply Subtype.ext
      exact (s16c1610_prod_unique hdir
        (s16c1610_prodFst hdir _).2 (s16c1610_prodSnd hdir _).2 k.2 l.2
        (s16c1610_prodFst_mul_prodSnd hdir _)).1
    have hsnd : s16c1610_prodSnd hdir
        (⟨(k : MulAut W) * (l : MulAut W),
          Subgroup.mul_mem Mb (hdir.2.2 ▸ Subgroup.mem_sup_left k.2)
            (hdir.2.2 ▸ Subgroup.mem_sup_right l.2)⟩ : ↥Mb) = l := by
      apply Subtype.ext
      exact (s16c1610_prod_unique hdir
        (s16c1610_prodFst hdir _).2 (s16c1610_prodSnd hdir _).2 k.2 l.2
        (s16c1610_prodFst_mul_prodSnd hdir _)).2
    exact Prod.ext hfst hsnd
  map_mul' x y := by
    have hcomm := s16c1610_commute_of_commutator_eq_bot hdir
    have heq : ((s16c1610_prodFst hdir x : MulAut W) *
          (s16c1610_prodFst hdir y : MulAut W)) *
        ((s16c1610_prodSnd hdir x : MulAut W) *
          (s16c1610_prodSnd hdir y : MulAut W)) = ((x * y : ↥Mb) : MulAut W) := by
      have hswap : (s16c1610_prodFst hdir y : MulAut W) *
          (s16c1610_prodSnd hdir x : MulAut W) =
          (s16c1610_prodSnd hdir x : MulAut W) *
            (s16c1610_prodFst hdir y : MulAut W) :=
        hcomm _ (s16c1610_prodFst hdir y).2 _ (s16c1610_prodSnd hdir x).2
      calc ((s16c1610_prodFst hdir x : MulAut W) *
            (s16c1610_prodFst hdir y : MulAut W)) *
          ((s16c1610_prodSnd hdir x : MulAut W) *
            (s16c1610_prodSnd hdir y : MulAut W))
          = (s16c1610_prodFst hdir x : MulAut W) *
              ((s16c1610_prodFst hdir y : MulAut W) *
                ((s16c1610_prodSnd hdir x : MulAut W) *
                  (s16c1610_prodSnd hdir y : MulAut W))) := by group
        _ = (s16c1610_prodFst hdir x : MulAut W) *
              ((s16c1610_prodSnd hdir x : MulAut W) *
                ((s16c1610_prodFst hdir y : MulAut W) *
                  (s16c1610_prodSnd hdir y : MulAut W))) := by
            congr 1
            calc (s16c1610_prodFst hdir y : MulAut W) *
                  ((s16c1610_prodSnd hdir x : MulAut W) *
                    (s16c1610_prodSnd hdir y : MulAut W))
                = ((s16c1610_prodFst hdir y : MulAut W) *
                    (s16c1610_prodSnd hdir x : MulAut W)) *
                    (s16c1610_prodSnd hdir y : MulAut W) := (mul_assoc _ _ _).symm
              _ = ((s16c1610_prodSnd hdir x : MulAut W) *
                    (s16c1610_prodFst hdir y : MulAut W)) *
                    (s16c1610_prodSnd hdir y : MulAut W) := by rw [hswap]
              _ = (s16c1610_prodSnd hdir x : MulAut W) *
                    ((s16c1610_prodFst hdir y : MulAut W) *
                      (s16c1610_prodSnd hdir y : MulAut W)) := mul_assoc _ _ _
        _ = (s16c1610_prodFst hdir x : MulAut W) *
              (s16c1610_prodSnd hdir x : MulAut W) *
                ((s16c1610_prodFst hdir y : MulAut W) *
                  (s16c1610_prodSnd hdir y : MulAut W)) := by group
        _ = ((x : MulAut W) * (y : MulAut W)) := by
            rw [s16c1610_prodFst_mul_prodSnd hdir x,
              s16c1610_prodFst_mul_prodSnd hdir y]
        _ = ((x * y : ↥Mb) : MulAut W) := rfl
    have huniq := s16c1610_prod_unique hdir
      (Subgroup.mul_mem Kb (s16c1610_prodFst hdir x).2 (s16c1610_prodFst hdir y).2)
      (Subgroup.mul_mem Lb (s16c1610_prodSnd hdir x).2 (s16c1610_prodSnd hdir y).2)
      (s16c1610_prodFst hdir (x * y)).2 (s16c1610_prodSnd hdir (x * y)).2
      (heq.trans (s16c1610_prodFst_mul_prodSnd hdir (x * y)).symm)
    exact Prod.ext (Subtype.ext huniq.1.symm) (Subtype.ext huniq.2.symm)

theorem s16c1610_card_IsSym_three {X : Type} [Group X] (h : IsSym X 3) : Nat.card X = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num

end Direct

section Natural

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W} {n a : ℕ}

theorem s16c1610_stable_of_binaryNaturalSL (h : BinaryNaturalSL H U Z n a) :
    ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := by
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  exact (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).U_inv

theorem s16c1610_sq_eq_one_of_binaryNaturalSL (h : BinaryNaturalSL H U ⊥ n 1) {u : W}
    (hu : u ∈ U) : u ^ 2 = 1 := by
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  letI := hK
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card K = 2 := by simpa using hK2
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime (p := 2)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨β, hβsurj, hβk, hβe⟩ :=
    (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro x y hxy
    have h1 : β (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : ((x * y⁻¹ : ↥U) : W) = 1 :=
      Subgroup.mem_bot.1 ((hβk (x * y⁻¹)).1 h1)
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  have hu2 : u ^ 2 ∈ U := Subgroup.pow_mem U hu 2
  have hsq : β ⟨u ^ 2, hu2⟩ = 1 := by
    have hcast : (⟨u ^ 2, hu2⟩ : ↥U) = ⟨u, hu⟩ ^ 2 := by ext; simp
    rw [hcast, map_pow]
    apply Multiplicative.toAdd.injective
    show (2 : ℕ) • Multiplicative.toAdd (β ⟨u, hu⟩) = 0
    ext i
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [CharP.cast_eq_zero (R := K) (p := 2), zero_mul]
    rfl
  have h3 : ((⟨u ^ 2, hu2⟩ : ↥U) : W) = 1 :=
    Subgroup.mem_bot.1 ((hβk (⟨u ^ 2, hu2⟩ : ↥U)).1 hsq)
  exact h3

theorem s16c1610_statedSL_eq_top_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (n : ℕ) : StatedSL n K = ⊤ := by
  have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hcard).1
  have hset : {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1} = Set.univ := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hunit : IsUnit (A : Matrix (Fin n) (Fin n) K).det := by
      have h : (A : Matrix (Fin n) (Fin n) K) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have h2 := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_one] at h2
      exact IsUnit.of_mul_eq_one _ h2
    calc (A : Matrix (Fin n) (Fin n) K).det = (hunit.unit : K) := hunit.unit_spec.symm
      _ = ((1 : Kˣ) : K) := by rw [Subsingleton.elim hunit.unit 1]
      _ = 1 := rfl
  rw [StatedSL, hset, Subgroup.closure_univ]

noncomputable def s16c1610_glMulEquiv {K : Type} [Field K] {m : ℕ}
    (e : ZMod 2 ≃+* K) : GL (Fin m) (ZMod 2) ≃* GL (Fin m) K :=
  Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem s16c1610_isSimpleGroup_GL_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) : IsSimpleGroup (GL (Fin m) K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hfc : Fintype.card K = 2 := by simpa using hK
  have e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hfc
  haveI : IsSimpleGroup (GL (Fin m) (ZMod 2)) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two hm
  exact (s16c1610_glMulEquiv e).symm.isSimpleGroup

theorem s16c1610_sq_eq_one_of_sum_two {W : Type} [CommGroup W]
    {Lb : Subgroup (MulAut W)} {m : ℕ}
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) Lb ⊤ ⊥ 2) (w : W) :
    w * w = 1 := by
  obtain ⟨I, hinf, hsup, hnat⟩ := s16c1610_sum_two_of_sumOfNat hsum
  have hw : w ∈ I 0 ⊔ I 1 := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    s16c1610_mem_sup_of_commute (fun a _ b _ => Commute.all a b) hw
  have ha2 : a * a = 1 := by
    simpa [pow_two] using s16c1610_sq_eq_one_of_binaryNaturalSL (hnat 0) ha
  have hb2 : b * b = 1 := by
    simpa [pow_two] using s16c1610_sq_eq_one_of_binaryNaturalSL (hnat 1) hb
  rw [mul_mul_mul_comm, ha2, hb2, one_mul]

end Natural

theorem s16c1610_one_lt_card_of_isLn {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    (h : IsLn X m 1) : 1 < Nat.card X := by
  have hcard := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two h
  have hb := CFSG.SeitzReduction.LinearPilot.ordA_two_pow_bounds (n := m - 1) (f := 1)
    (by omega) le_rfl
  have hexp : 3 ≤ 1 * ((m - 1) * ((m - 1) + 1) / 2) := by
    have h2 : 2 ≤ m - 1 := by omega
    have h6 : 6 ≤ (m - 1) * ((m - 1) + 1) := by nlinarith
    rw [one_mul, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    norm_num
    exact h6
  have hge : 2 ^ 3 ≤ Open.ordA (m - 1) (2 ^ 1) := by
    calc 2 ^ 3 ≤ 2 ^ (1 * ((m - 1) * ((m - 1) + 1) / 2)) :=
          Nat.pow_le_pow_right (by norm_num) hexp
      _ ≤ Open.ordA (m - 1) (2 ^ 1) := Nat.le_of_dvd hb.2.1 hb.1
  rw [hcard]
  exact lt_of_lt_of_le (by norm_num : 1 < 8) (by simpa using hge)

section Coords

variable {W : Type} [CommGroup W] {Lb : Subgroup (MulAut W)} {U : Subgroup W} {m : ℕ}

private noncomputable def s16c1610_stdModMulEquiv {K : Type} [Field K] (f : ZMod 2 ≃+* K)
    (m : ℕ) : Multiplicative (Fin m → K) ≃* Multiplicative (Fin m → ZMod 2) where
  toFun y := Multiplicative.ofAdd fun i => f.symm (Multiplicative.toAdd y i)
  invFun y := Multiplicative.ofAdd fun i => f (Multiplicative.toAdd y i)
  left_inv y := by
    apply Multiplicative.toAdd.injective
    ext i
    simp
  right_inv y := by
    apply Multiplicative.toAdd.injective
    ext i
    simp
  map_mul' y z := by
    apply Multiplicative.toAdd.injective
    ext i
    simp [map_add]

private theorem s16c1610_coords_of_binaryNaturalSL (hm : 3 ≤ m) (hLbig : 1 < Nat.card ↥Lb)
    (h : BinaryNaturalSL Lb U ⊥ m 1) :
    ∃ (b : ↥U ≃* Multiplicative (Fin m → ZMod 2))
      (ρ : ↥Lb ≃* GL (Fin m) (ZMod 2)),
      ∀ (x : ↥Lb) (u : ↥U) (hu : (x : MulAut W) (u : W) ∈ U),
        Multiplicative.toAdd (b ⟨(x : MulAut W) (u : W), hu⟩) =
          (((ρ x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
            (Multiplicative.toAdd (b u))) := by
  obtain ⟨K, hKfld, hKfin, hK2, π, hπ⟩ := h
  letI := hKfld
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = 2 := by simpa using hK2
  have hfc : Fintype.card K = 2 := by simpa using hcard
  let rK : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hfc
  have hS : StatedSL m K = ⊤ := s16c1610_statedSL_eq_top_of_card_two hcard m
  haveI : IsSimpleGroup (GL (Fin m) K) := s16c1610_isSimpleGroup_GL_of_card_two hcard hm
  let glE : ↥(StatedSL m K) ≃* GL (Fin m) K :=
    { toFun := fun γ => (γ : GL (Fin m) K)
      invFun := fun x => ⟨x, by rw [hS]; exact Subgroup.mem_top x⟩
      left_inv := fun γ => rfl
      right_inv := fun x => rfl
      map_mul' := fun γ δ => rfl }
  haveI : IsSimpleGroup ↥(StatedSL m K) := glE.isSimpleGroup
  let πh : ↥(StatedSL m K) →* ↥Lb :=
    { toFun := fun γ => π (show (FFModel.nat (StatedSL m K)).Gam from γ)
      map_one' := map_one π
      map_mul' := fun a b => map_mul π _ _ }
  have hπsurj : Function.Surjective πh := by
    intro y
    obtain ⟨g, hg⟩ := hπ.1 y
    exact ⟨show ↥(StatedSL m K) from g, hg⟩
  have hπinj : Function.Injective πh := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := πh.ker) with hbot | htop
    · exact MonoidHom.ker_eq_bot_iff πh |>.1 hbot
    · exfalso
      have hsub : Subsingleton ↥Lb := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hπsurj a
        obtain ⟨y, rfl⟩ := hπsurj b
        have hx : x ∈ πh.ker := by rw [htop]; exact Subgroup.mem_top x
        have hy : y ∈ πh.ker := by rw [htop]; exact Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]⟩
      have hle : Nat.card ↥Lb ≤ 1 := by
        have h := Nat.card_le_card_of_injective (fun _ : ↥Lb => (() : Unit))
          (fun a b _ => Subsingleton.elim a b)
        simpa using h
      omega
  let πe : ↥(StatedSL m K) ≃* ↥Lb := MulEquiv.ofBijective πh ⟨hπinj, hπsurj⟩
  obtain ⟨eK, heK⟩ :=
    CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub (StatedSL m K) hπ
  let glQ : GL (Fin m) K ≃* GL (Fin m) (ZMod 2) :=
    Units.mapEquiv (RingEquiv.mapMatrix rK.symm).toMulEquiv
  let ρ : ↥Lb ≃* GL (Fin m) (ZMod 2) := πe.symm.trans (glE.trans glQ)
  refine ⟨eK.trans (s16c1610_stdModMulEquiv rK m), ρ, ?_⟩
  intro x u hu
  set γ : ↥(StatedSL m K) := πe.symm x with hγ
  have hπγ : πe γ = x := πe.apply_symm_apply x
  have hval : ((πe γ : ↥Lb) : MulAut W) = (x : MulAut W) := congrArg Subtype.val hπγ
  have heK' : eK ⟨(x : MulAut W) (u : W), hu⟩ =
      CFSG.Quasithin.natAct (StatedSL m K) γ (eK u) := by
    have hsub : (⟨(x : MulAut W) (u : W), hu⟩ : ↥U) =
        ⟨((πe γ : ↥Lb) : MulAut W) (u : W), hval.symm ▸ hu⟩ :=
      Subtype.ext (congrArg (fun z : MulAut W => z (u : W)) hval.symm)
    rw [hsub]
    exact heK γ u (hval.symm ▸ hu)
  have hmat : ((ρ x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      rK.symm.mapMatrix ((γ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    simp only [ρ, MulEquiv.trans_apply, glQ, glE, Units.coe_mapEquiv, hγ]
    rfl
  have hb : Multiplicative.toAdd (eK u) =
      fun i => rK (Multiplicative.toAdd ((eK.trans (s16c1610_stdModMulEquiv rK m)) u) i) := by
    funext i
    show Multiplicative.toAdd (eK u) i = rK (Multiplicative.toAdd
      (s16c1610_stdModMulEquiv rK m (eK u)) i)
    simp [s16c1610_stdModMulEquiv]
  apply Multiplicative.toAdd.injective
  show (fun i => rK.symm (Multiplicative.toAdd
      (eK ⟨(x : MulAut W) (u : W), hu⟩) i)) =
    (rK.symm.mapMatrix ((γ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)).mulVec
      (Multiplicative.toAdd ((eK.trans (s16c1610_stdModMulEquiv rK m)) u))
  rw [heK']
  funext i
  rw [show Multiplicative.toAdd
      (CFSG.Quasithin.natAct (StatedSL m K) γ (eK u)) =
      ((γ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).mulVec
        (Multiplicative.toAdd (eK u)) from rfl]
  rw [hb]
  refine (RingHom.map_mulVec rK.symm.toRingHom
    ((γ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
    (fun j => rK (Multiplicative.toAdd
      ((eK.trans (s16c1610_stdModMulEquiv rK m)) u) j)) i).trans ?_
  simp only [Matrix.map_apply, RingEquiv.mapMatrix_apply]
  rw [show (⇑rK.symm.toRingHom ∘ fun j => rK (Multiplicative.toAdd
        ((eK.trans (s16c1610_stdModMulEquiv rK m)) u) j)) =
      Multiplicative.toAdd ((eK.trans (s16c1610_stdModMulEquiv rK m)) u) from by
    funext j
    simp]
  rfl

end Coords

section Components

open CFSG.Quasithin.H13.Mult

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
  {I : Fin 2 → Subgroup W} {Lb : Subgroup (MulAut W)} {m : ℕ}

private noncomputable def s16c1610_T00
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  (LinearMap.fst (ZMod 2) _ _) ∘ₗ (c.toLinearMap ∘ₗ (κ.toLinearMap ∘ₗ (c.symm.toLinearMap ∘ₗ
    (LinearMap.inl (ZMod 2) _ _))))

private noncomputable def s16c1610_T01
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  (LinearMap.fst (ZMod 2) _ _) ∘ₗ (c.toLinearMap ∘ₗ (κ.toLinearMap ∘ₗ (c.symm.toLinearMap ∘ₗ
    (LinearMap.inr (ZMod 2) _ _))))

private noncomputable def s16c1610_T10
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  (LinearMap.snd (ZMod 2) _ _) ∘ₗ (c.toLinearMap ∘ₗ (κ.toLinearMap ∘ₗ (c.symm.toLinearMap ∘ₗ
    (LinearMap.inl (ZMod 2) _ _))))

private noncomputable def s16c1610_T11
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  (LinearMap.snd (ZMod 2) _ _) ∘ₗ (c.toLinearMap ∘ₗ (κ.toLinearMap ∘ₗ (c.symm.toLinearMap ∘ₗ
    (LinearMap.inr (ZMod 2) _ _))))

private theorem s16c1610_coord_action
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) (x : Additive W) :
    c (κ x) = (s16c1610_T00 c κ (c x).1 + s16c1610_T01 c κ (c x).2,
      s16c1610_T10 c κ (c x).1 + s16c1610_T11 c κ (c x).2) := by
  have hx : x = c.symm (LinearMap.inl (ZMod 2) _ _ (c x).1) +
      c.symm (LinearMap.inr (ZMod 2) _ _ (c x).2) := by
    rw [← map_add, show LinearMap.inl (ZMod 2) _ _ (c x).1 +
      LinearMap.inr (ZMod 2) _ _ (c x).2 = c x from by
        ext <;> simp [LinearMap.inl_apply, LinearMap.inr_apply],
      LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hx]
  rw [map_add, map_add]
  ext <;> simp [s16c1610_T00, s16c1610_T01, s16c1610_T10, s16c1610_T11]

@[simp] private theorem s16c1610_T00_apply
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) (z : Fin m → ZMod 2) :
    s16c1610_T00 c κ z = (c (κ (c.symm
      (LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2) z)))).1 := rfl

@[simp] private theorem s16c1610_T01_apply
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) (z : Fin m → ZMod 2) :
    s16c1610_T01 c κ z = (c (κ (c.symm
      (LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2) z)))).1 := rfl

@[simp] private theorem s16c1610_T10_apply
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) (z : Fin m → ZMod 2) :
    s16c1610_T10 c κ z = (c (κ (c.symm
      (LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2) z)))).2 := rfl

@[simp] private theorem s16c1610_T11_apply
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)))
    (κ : Additive W ≃ₗ[ZMod 2] Additive W) (z : Fin m → ZMod 2) :
    s16c1610_T11 c κ z = (c (κ (c.symm
      (LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2) z)))).2 := rfl

end Components

section ComponentSchur

open CFSG.Quasithin.H13.Mult

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
  {I : Fin 2 → Subgroup W} {Lb : Subgroup (MulAut W)} {m : ℕ}

private noncomputable def s16c1610_diag (ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2))
    (l : ↥Lb) (z : (Fin m → ZMod 2) × (Fin m → ZMod 2)) :
    (Fin m → ZMod 2) × (Fin m → ZMod 2) :=
  ((((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z.1),
   (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z.2))

private theorem s16c1610_linEquiv_comm {κ l : MulAut W} (h : κ * l = l * κ)
    (y : Additive W) :
    CFSG.Quasithin.H13.Mult.linEquiv κ (CFSG.Quasithin.H13.Mult.linEquiv l y) =
      CFSG.Quasithin.H13.Mult.linEquiv l (CFSG.Quasithin.H13.Mult.linEquiv κ y) := by
  have h' : CFSG.Quasithin.H13.Mult.linEquiv κ * CFSG.Quasithin.H13.Mult.linEquiv l =
      CFSG.Quasithin.H13.Mult.linEquiv l * CFSG.Quasithin.H13.Mult.linEquiv κ := by
    rw [← map_mul, ← map_mul, h]
  simpa only [LinearEquiv.mul_apply] using congrArg
    (fun f : Additive W ≃ₗ[ZMod 2] Additive W => f y) h'

private noncomputable def s16c1610_D
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))) (l : ↥Lb) :
    ((Fin m → ZMod 2) × (Fin m → ZMod 2)) ≃ₗ[ZMod 2]
      ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  c.symm.trans ((CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W)).trans c)

private theorem s16c1610_D_apply {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (l : ↥Lb) (z : (Fin m → ZMod 2) × (Fin m → ZMod 2)) :
    s16c1610_D c l z = s16c1610_diag ρ0 ρ1 l z := by
  show c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) (c.symm z)) = _
  rw [hNat l (c.symm z), LinearEquiv.apply_symm_apply]

private theorem s16c1610_D_symm_apply
    (c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))) (l : ↥Lb)
    (z : (Fin m → ZMod 2) × (Fin m → ZMod 2)) :
    c.symm (s16c1610_D c l z) = CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) (c.symm z) := by
  show c.symm (c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) (c.symm z))) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem s16c1610_D_inl {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (l : ↥Lb) (z : Fin m → ZMod 2) :
    s16c1610_D c l (LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2) z) =
      LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
        (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) := by
  rw [s16c1610_D_apply hNat l]
  simp [s16c1610_diag, LinearMap.inl_apply, Matrix.mulVec_zero]

private theorem s16c1610_D_inr {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (l : ↥Lb) (z : Fin m → ZMod 2) :
    s16c1610_D c l (LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2) z) =
      LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
        (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) := by
  rw [s16c1610_D_apply hNat l]
  simp [s16c1610_diag, LinearMap.inr_apply, Matrix.mulVec_zero]

private theorem s16c1610_conj {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (l : ↥Lb) (hκl : κ * (l : MulAut W) = (l : MulAut W) * κ)
    (z : (Fin m → ZMod 2) × (Fin m → ZMod 2)) :
    c (CFSG.Quasithin.H13.Mult.linEquiv κ (c.symm (s16c1610_D c l z))) =
      s16c1610_D c l (c (CFSG.Quasithin.H13.Mult.linEquiv κ (c.symm z))) := by
  rw [s16c1610_D_symm_apply]
  show c (CFSG.Quasithin.H13.Mult.linEquiv κ
      (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) (c.symm z))) =
    c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W)
      (c.symm (c (CFSG.Quasithin.H13.Mult.linEquiv κ (c.symm z)))))
  rw [LinearEquiv.symm_apply_apply, s16c1610_linEquiv_comm hκl]

private theorem s16c1610_T00_comm {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (l : ↥Lb) (hκl : κ * (l : MulAut W) = (l : MulAut W) * κ)
    (z : Fin m → ZMod 2) :
    s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ)
        (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
      (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        (s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ) z)) := by
  rw [s16c1610_T00_apply, s16c1610_T00_apply, ← s16c1610_D_inl hNat l z,
    s16c1610_conj hNat κ l hκl, s16c1610_D_apply hNat l]
  simp [s16c1610_diag]

private theorem s16c1610_T01_comm {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (l : ↥Lb) (hκl : κ * (l : MulAut W) = (l : MulAut W) * κ)
    (z : Fin m → ZMod 2) :
    s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ)
        (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
      (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        (s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) z)) := by
  rw [s16c1610_T01_apply, s16c1610_T01_apply, ← s16c1610_D_inr hNat l z,
    s16c1610_conj hNat κ l hκl, s16c1610_D_apply hNat l]
  simp [s16c1610_diag]

private theorem s16c1610_T10_comm {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (l : ↥Lb) (hκl : κ * (l : MulAut W) = (l : MulAut W) * κ)
    (z : Fin m → ZMod 2) :
    s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ)
        (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
      (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        (s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) z)) := by
  rw [s16c1610_T10_apply, s16c1610_T10_apply, ← s16c1610_D_inl hNat l z,
    s16c1610_conj hNat κ l hκl, s16c1610_D_apply hNat l]
  simp [s16c1610_diag]

private theorem s16c1610_T11_comm {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (l : ↥Lb) (hκl : κ * (l : MulAut W) = (l : MulAut W) * κ)
    (z : Fin m → ZMod 2) :
    s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ)
        (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
      (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        (s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ) z)) := by
  rw [s16c1610_T11_apply, s16c1610_T11_apply, ← s16c1610_D_inr hNat l z,
    s16c1610_conj hNat κ l hκl, s16c1610_D_apply hNat l]
  simp [s16c1610_diag]

private theorem s16c1610_T00_schur {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (hκl : ∀ l : ↥Lb, κ * (l : MulAut W) = (l : MulAut W) * κ)
    (hm : 3 ≤ m) :
    s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 ∨
      s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = LinearMap.id := by
  refine s16c1610_end_eq_zero_or_id_pi (m := m) (by omega) ?_
  intro τ y
  obtain ⟨A, rfl⟩ := (s16c1610_glAction m).surjective τ
  rw [s16c1610_glAction_apply, s16c1610_glAction_apply]
  obtain ⟨l, rfl⟩ := ρ0.surjective A
  exact s16c1610_T00_comm hNat κ l (hκl l) y

private theorem s16c1610_T11_schur {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (hκl : ∀ l : ↥Lb, κ * (l : MulAut W) = (l : MulAut W) * κ)
    (hm : 3 ≤ m) :
    s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 ∨
      s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = LinearMap.id := by
  refine s16c1610_end_eq_zero_or_id_pi (m := m) (by omega) ?_
  intro τ y
  obtain ⟨A, rfl⟩ := (s16c1610_glAction m).surjective τ
  rw [s16c1610_glAction_apply, s16c1610_glAction_apply]
  obtain ⟨l, rfl⟩ := ρ1.surjective A
  exact s16c1610_T11_comm hNat κ l (hκl l) y

private theorem s16c1610_T01_schur {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (hκl : ∀ l : ↥Lb, κ * (l : MulAut W) = (l : MulAut W) * κ) :
    s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 ∨
      Function.Bijective (s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ)) := by
  have hker : ∀ τ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ z, s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) z = 0 →
        s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) (τ z) = 0 := by
    intro τ z hz
    obtain ⟨A, rfl⟩ := (s16c1610_glAction m).surjective τ
    rw [s16c1610_glAction_apply]
    obtain ⟨l, rfl⟩ := ρ1.surjective A
    rw [s16c1610_T01_comm hNat κ l (hκl l) z, hz, Matrix.mulVec_zero]
  rcases s16c1610_eq_zero_or_injective_pi
    (φ := s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ)) hker with h0 | hinj
  · exact Or.inl h0
  · exact Or.inr ⟨hinj, s16c1610_injective_surjective_pi hinj⟩

private theorem s16c1610_T10_schur {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (hκl : ∀ l : ↥Lb, κ * (l : MulAut W) = (l : MulAut W) * κ) :
    s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 ∨
      Function.Bijective (s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ)) := by
  have hker : ∀ τ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ z, s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) z = 0 →
        s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) (τ z) = 0 := by
    intro τ z hz
    obtain ⟨A, rfl⟩ := (s16c1610_glAction m).surjective τ
    rw [s16c1610_glAction_apply]
    obtain ⟨l, rfl⟩ := ρ0.surjective A
    rw [s16c1610_T10_comm hNat κ l (hκl l) z, hz, Matrix.mulVec_zero]
  rcases s16c1610_eq_zero_or_injective_pi
    (φ := s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ)) hker with h0 | hinj
  · exact Or.inl h0
  · exact Or.inr ⟨hinj, s16c1610_injective_surjective_pi hinj⟩

end ComponentSchur

section StepThree

open CFSG.Quasithin.H13.Mult

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
  {I : Fin 2 → Subgroup W} {Lb : Subgroup (MulAut W)} {m : ℕ}

private noncomputable def s16c1610_e0 (hm : 1 ≤ m) : Fin m → ZMod 2 :=
  Pi.single ⟨0, hm⟩ 1

private theorem s16c1610_e0_ne_zero (hm : 1 ≤ m) : s16c1610_e0 (m := m) hm ≠ 0 := by
  intro hh
  have h1 := congrFun hh ⟨0, hm⟩
  simp [s16c1610_e0] at h1

private theorem s16c1610_T00_ne_zero_of_offdiag {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (hm : 1 ≤ m)
    (hT01 : s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0)
    (hT10 : s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0) :
    s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ) ≠ 0 := by
  intro h0
  let x : Additive W := c.symm (LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
    (s16c1610_e0 (m := m) hm))
  have hx : c x = LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
      (s16c1610_e0 (m := m) hm) := LinearEquiv.apply_symm_apply c _
  have hxne : x ≠ 0 := by
    intro hh
    have h2 : LinearMap.inl (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
        (s16c1610_e0 (m := m) hm) = 0 := by rw [← hx, hh, map_zero]
    exact s16c1610_e0_ne_zero hm (by simpa [LinearMap.inl_apply] using congrArg Prod.fst h2)
  have hz : c (CFSG.Quasithin.H13.Mult.linEquiv κ x) = 0 := by
    have h1 := s16c1610_coord_action c (CFSG.Quasithin.H13.Mult.linEquiv κ) x
    rw [hx] at h1
    obtain ⟨h1a, h1b⟩ := Prod.ext_iff.mp h1
    rw [h0, hT01, hT10] at h1a h1b
    refine Prod.ext ?_ ?_
    · simp only [h1a, LinearMap.zero_apply, zero_add]
      rfl
    · simp only [h1b, LinearMap.inl_apply, LinearMap.zero_apply, LinearMap.map_zero, add_zero]
      rfl
  have hzero : CFSG.Quasithin.H13.Mult.linEquiv κ x = 0 := c.injective (by rw [hz, c.map_zero])
  exact hxne ((CFSG.Quasithin.H13.Mult.linEquiv κ).injective (by rw [hzero, map_zero]))

private theorem s16c1610_T11_ne_zero_of_offdiag {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    (κ : MulAut W) (hm : 1 ≤ m)
    (hT01 : s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0)
    (hT10 : s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0) :
    s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ) ≠ 0 := by
  intro h0
  let x : Additive W := c.symm (LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
    (s16c1610_e0 (m := m) hm))
  have hx : c x = LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
      (s16c1610_e0 (m := m) hm) := LinearEquiv.apply_symm_apply c _
  have hxne : x ≠ 0 := by
    intro hh
    have h2 : LinearMap.inr (ZMod 2) (Fin m → ZMod 2) (Fin m → ZMod 2)
        (s16c1610_e0 (m := m) hm) = 0 := by rw [← hx, hh, map_zero]
    exact s16c1610_e0_ne_zero hm (by simpa [LinearMap.inr_apply] using congrArg Prod.snd h2)
  have hz : c (CFSG.Quasithin.H13.Mult.linEquiv κ x) = 0 := by
    have h1 := s16c1610_coord_action c (CFSG.Quasithin.H13.Mult.linEquiv κ) x
    rw [hx] at h1
    obtain ⟨h1a, h1b⟩ := Prod.ext_iff.mp h1
    rw [h0, hT01, hT10] at h1a h1b
    refine Prod.ext ?_ ?_
    · simp only [h1a, LinearMap.inr_apply, LinearMap.zero_apply, LinearMap.map_zero, add_zero]
      rfl
    · simp only [h1b, LinearMap.zero_apply, zero_add]
      rfl
  have hzero : CFSG.Quasithin.H13.Mult.linEquiv κ x = 0 := c.injective (by rw [hz, c.map_zero])
  exact hxne ((CFSG.Quasithin.H13.Mult.linEquiv κ).injective (by rw [hzero, map_zero]))

private theorem s16c1610_exists_offdiag {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x))
    {Kb : Subgroup (MulAut W)} (hcomm : ∀ (κ : ↥Kb) (l : ↥Lb),
      (κ : MulAut W) * (l : MulAut W) = (l : MulAut W) * κ)
    (hm : 3 ≤ m) (hK : IsSym ↥Kb 3) :
    ∃ κ : ↥Kb, s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) ≠ 0 ∨
      s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) ≠ 0 := by
  by_contra hcon
  rw [not_exists] at hcon
  have hcon' : ∀ κ : ↥Kb,
      s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) = 0 ∧
      s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) = 0 := by
    intro κ
    simpa only [not_ne_iff, not_or] using hcon κ
  have htriv : ∀ κ : ↥Kb, (κ : MulAut W) = 1 := by
    intro κ
    have h00 : s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) = LinearMap.id := by
      rcases s16c1610_T00_schur hNat (κ : MulAut W) (hcomm κ) hm with h | h
      · exfalso
        exact (s16c1610_T00_ne_zero_of_offdiag hNat (κ : MulAut W) (by omega)
          (hcon' κ).2 (hcon' κ).1) h
      · exact h
    have h11 : s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) = LinearMap.id := by
      rcases s16c1610_T11_schur hNat (κ : MulAut W) (hcomm κ) hm with h | h
      · exfalso
        exact (s16c1610_T11_ne_zero_of_offdiag hNat (κ : MulAut W) (by omega)
          (hcon' κ).2 (hcon' κ).1) h
      · exact h
    apply CFSG.Quasithin.H13.Mult.linEquiv.injective
    refine LinearEquiv.ext fun x => ?_
    have h1 := s16c1610_coord_action c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W)) x
    rw [h00, h11, (hcon' κ).1, (hcon' κ).2] at h1
    simp at h1
    rw [show CFSG.Quasithin.H13.Mult.linEquiv (1 : MulAut W) = 1 from map_one _]
    simpa using h1
  have hbot : Kb = ⊥ := by
    rw [eq_bot_iff]
    intro κ hκ
    rw [Subgroup.mem_bot]
    exact htriv ⟨κ, hκ⟩
  have hcard : Nat.card ↥Kb = 1 := by rw [hbot]; simp
  have h6 := s16c1610_card_IsSym_three hK
  omega

end StepThree

section StepFour

open CFSG.Quasithin.H13.Mult

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
  {I : Fin 2 → Subgroup W} {Lb : Subgroup (MulAut W)} {m : ℕ}

private theorem s16c1610_one_ne_zero_pi (hm : 1 ≤ m) :
    (1 : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) ≠ 0 := by
  haveI : Nontrivial (Fin m → ZMod 2) :=
    ⟨⟨s16c1610_e0 (m := m) hm, 0, s16c1610_e0_ne_zero hm⟩⟩
  exact one_ne_zero

private theorem s16c1610_eps_id {φ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hm : 1 ≤ m) (h : φ = 0 ∨ φ = LinearMap.id) :
    φ = (if φ = 0 then (0 : ZMod 2) else 1) • (LinearMap.id : (Fin m → ZMod 2) →ₗ[ZMod 2] _) := by
  rcases h with h | h
  · rw [h, if_pos rfl, zero_smul]
  · have hne : φ ≠ 0 := by rw [h]; exact s16c1610_one_ne_zero_pi hm
    rw [if_neg hne, h, one_smul]

private noncomputable def s16c1610_matA {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (κ : MulAut W) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j =>
    if (if i = 0 then
          (if j = 0 then s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ)
            else s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ))
        else
          (if j = 0 then s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ)
            else s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ))) = 0
      then (0 : ZMod 2) else 1

private theorem s16c1610_matA_zero_zero {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))} (κ : MulAut W) :
    s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 0 0 =
      (if s16c1610_T00 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 then 0 else 1) := by
  simp [s16c1610_matA]

private theorem s16c1610_matA_zero_one {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))} (κ : MulAut W) :
    s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 0 1 =
      (if s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 then 0 else 1) := by
  simp [s16c1610_matA]

private theorem s16c1610_matA_one_zero {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))} (κ : MulAut W) :
    s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 1 0 =
      (if s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 then 0 else 1) := by
  simp [s16c1610_matA]

private theorem s16c1610_matA_one_one {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))} (κ : MulAut W) :
    s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 1 1 =
      (if s16c1610_T11 c (CFSG.Quasithin.H13.Mult.linEquiv κ) = 0 then 0 else 1) := by
  simp [s16c1610_matA]

end StepFour

section Assembly

open CFSG.Quasithin.H13.Mult

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
  {I : Fin 2 → Subgroup W} {Lb Kb Mb : Subgroup (MulAut W)} {m : ℕ}

private theorem s16c1610_comp_eq_zero_or_id {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    (κ : MulAut W) (hm : 3 ≤ m)
    {φ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)}
    (hcomm : ∀ (l : ↥Lb) (z : Fin m → ZMod 2),
      φ (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
        (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (φ z))) :
    φ = 0 ∨ φ = LinearMap.id := by
  refine s16c1610_end_eq_zero_or_id_pi (m := m) (by omega) ?_
  intro τ y
  obtain ⟨A, rfl⟩ := (s16c1610_glAction m).surjective τ
  rw [s16c1610_glAction_apply, s16c1610_glAction_apply]
  obtain ⟨l, rfl⟩ := ρ0.surjective A
  exact hcomm l y

private noncomputable def s16c1610_actA {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (κ : MulAut W) :
    ((Fin m → ZMod 2) × (Fin m → ZMod 2)) → ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  fun p =>
    ((s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ) 0 0 • p.1 +
        (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ) 0 1 • p.2,
      (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ) 1 0 • p.1 +
        (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ) 1 1 • p.2)

private theorem s16c1610_coord_matA {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ0 l (c x))
    (κ : MulAut W) (hκl : ∀ l : ↥Lb, κ * (l : MulAut W) = (l : MulAut W) * κ)
    (hm : 3 ≤ m) (x : Additive W) :
    c (CFSG.Quasithin.H13.Mult.linEquiv κ x) =
      s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) κ (c x) := by
  have h00 := s16c1610_eps_id (m := m) (by omega)
    (s16c1610_comp_eq_zero_or_id (m := m) κ hm
      (fun l z => s16c1610_T00_comm hNat κ l (hκl l) z))
  have h01 := s16c1610_eps_id (m := m) (by omega)
    (s16c1610_comp_eq_zero_or_id (m := m) κ hm
      (fun l z => s16c1610_T01_comm hNat κ l (hκl l) z))
  have h10 := s16c1610_eps_id (m := m) (by omega)
    (s16c1610_comp_eq_zero_or_id (m := m) κ hm
      (fun l z => s16c1610_T10_comm hNat κ l (hκl l) z))
  have h11 := s16c1610_eps_id (m := m) (by omega)
    (s16c1610_comp_eq_zero_or_id (m := m) κ hm
      (fun l z => s16c1610_T11_comm hNat κ l (hκl l) z))
  rw [s16c1610_coord_action c (CFSG.Quasithin.H13.Mult.linEquiv κ) x, h00, h01, h10, h11]
  apply Prod.ext <;>
    simp only [LinearMap.smul_apply, LinearMap.id_apply, s16c1610_actA,
      s16c1610_matA_zero_zero, s16c1610_matA_zero_one, s16c1610_matA_one_zero,
      s16c1610_matA_one_one, Prod.fst, Prod.snd] <;> rfl

private theorem s16c1610_smul_e0_cancel (hm : 1 ≤ m) {r s : ZMod 2}
    (h : r • s16c1610_e0 (m := m) hm = s • s16c1610_e0 (m := m) hm) : r = s := by
  have h1 := congrFun h ⟨0, hm⟩
  simpa [s16c1610_e0] using h1

private theorem s16c1610_actA_eq {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))} (κ : MulAut W)
    (u v : Fin m → ZMod 2) :
    s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ (u, v) =
      (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 0 0 • u +
          s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 0 1 • v,
        s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 1 0 • u +
          s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 1 1 • v) := rfl

private theorem s16c1610_matA_mul {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ0 l (c x))
    (hm : 3 ≤ m) (κ κ' : MulAut W)
    (hκl : ∀ l : ↥Lb, κ * (l : MulAut W) = (l : MulAut W) * κ)
    (hκ'l : ∀ l : ↥Lb, κ' * (l : MulAut W) = (l : MulAut W) * κ') :
    s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ * κ') =
      s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) κ *
        s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) κ' := by
  have hmul : ∀ u v : Fin m → ZMod 2,
      s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ * κ') (u, v) =
        s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) κ
          (s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) κ' (u, v)) := by
    intro u v
    obtain ⟨x, hx⟩ := c.surjective (u, v)
    rw [← hx]
    rw [← s16c1610_coord_matA hNat (κ * κ') (fun l => by
        rw [mul_assoc, hκ'l l, ← mul_assoc, hκl l, mul_assoc]) hm x,
      ← s16c1610_coord_matA hNat κ' hκ'l hm x,
      ← s16c1610_coord_matA hNat κ hκl hm _]
    rw [map_mul]
    rfl
  ext i j
  fin_cases i <;> fin_cases j
  · have h := congrArg Prod.fst (hmul (s16c1610_e0 (m := m) (by omega)) 0)
    simp only [s16c1610_actA_eq, Prod.fst, smul_zero, add_zero, zero_add, smul_smul] at h
    rw [← add_smul] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact s16c1610_smul_e0_cancel (m := m) (by omega) h
  · have h := congrArg Prod.fst (hmul 0 (s16c1610_e0 (m := m) (by omega)))
    simp only [s16c1610_actA_eq, Prod.fst, smul_zero, add_zero, zero_add, smul_smul] at h
    rw [← add_smul] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact s16c1610_smul_e0_cancel (m := m) (by omega) h
  · have h := congrArg Prod.snd (hmul (s16c1610_e0 (m := m) (by omega)) 0)
    simp only [s16c1610_actA_eq, Prod.snd, smul_zero, add_zero, zero_add, smul_smul] at h
    rw [← add_smul] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact s16c1610_smul_e0_cancel (m := m) (by omega) h
  · have h := congrArg Prod.snd (hmul 0 (s16c1610_e0 (m := m) (by omega)))
    simp only [s16c1610_actA_eq, Prod.snd, smul_zero, add_zero, zero_add, smul_smul] at h
    rw [← add_smul] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact s16c1610_smul_e0_cancel (m := m) (by omega) h

private theorem s16c1610_actA_one {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ0 l (c x))
    (hm : 3 ≤ m) (p : (Fin m → ZMod 2) × (Fin m → ZMod 2)) :
    s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) p = p := by
  obtain ⟨x, hx⟩ := c.surjective p
  rw [← hx]
  rw [← s16c1610_coord_matA hNat (1 : MulAut W) (fun l => by rw [one_mul, mul_one]) hm x,
    map_one]
  rfl

private theorem s16c1610_matA_one {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ0 l (c x))
    (hm : 3 ≤ m) :
    s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) = 1 := by
  let e : Fin m → ZMod 2 := s16c1610_e0 (m := m) (by omega)
  have h1 : s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) 0 0 = 1 := by
    have h := congrArg Prod.fst (s16c1610_actA_one hNat hm (e, 0))
    simp only [s16c1610_actA_eq, Prod.fst, smul_zero, add_zero, zero_add] at h
    exact s16c1610_smul_e0_cancel (m := m) (by omega) (by rw [one_smul]; exact h)
  have h2 : s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) 1 0 = 0 := by
    have h := congrArg Prod.snd (s16c1610_actA_one hNat hm (e, 0))
    simp only [s16c1610_actA_eq, Prod.snd, smul_zero, add_zero, zero_add] at h
    exact s16c1610_smul_e0_cancel (m := m) (by omega) (by rw [zero_smul]; exact h)
  have h3 : s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) 0 1 = 0 := by
    have h := congrArg Prod.fst (s16c1610_actA_one hNat hm (0, e))
    simp only [s16c1610_actA_eq, Prod.fst, smul_zero, add_zero, zero_add] at h
    exact s16c1610_smul_e0_cancel (m := m) (by omega) (by rw [zero_smul]; exact h)
  have h4 : s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) 1 1 = 1 := by
    have h := congrArg Prod.snd (s16c1610_actA_one hNat hm (0, e))
    simp only [s16c1610_actA_eq, Prod.snd, smul_zero, add_zero, zero_add] at h
    exact s16c1610_smul_e0_cancel (m := m) (by omega) (by rw [one_smul]; exact h)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4, Matrix.one_apply]

private theorem s16c1610_exists_permEquiv {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))}
    (hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ0 l (c x))
    (hm : 3 ≤ m) (hK : IsSym ↥Kb 3)
    (hcomm : ∀ (κ : ↥Kb) (l : ↥Lb),
      (κ : MulAut W) * (l : MulAut W) = (l : MulAut W) * κ) :
    ∃ s : ↥Kb ≃* Equiv.Perm (Fin 3),
      ∀ κ : ↥Kb, s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ : MulAut W) =
        s16c1610_permMat (s κ) := by
  have hone : s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (1 : MulAut W) = 1 :=
    s16c1610_matA_one hNat hm
  have hmul : ∀ κ κ' : ↥Kb,
      s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) ((κ : MulAut W) * κ') =
        s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ : MulAut W) *
          s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ' : MulAut W) :=
    fun κ κ' => s16c1610_matA_mul hNat hm (κ : MulAut W) (κ' : MulAut W)
      (hcomm κ) (hcomm κ')
  have hunit : ∀ κ : ↥Kb, IsUnit (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c)
      (κ : MulAut W)) := by
    intro κ
    refine ⟨⟨_, s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ⁻¹ : ↥Kb), ?_, ?_⟩, rfl⟩
    · have h := hmul κ κ⁻¹
      rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, hone] at h
      exact h.symm
    · have h := hmul κ⁻¹ κ
      rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, hone] at h
      exact h.symm
  let fgl : ↥Kb →* GL (Fin 2) (ZMod 2) :=
    { toFun := fun κ => Matrix.GeneralLinearGroup.mk'' _
        ((Matrix.isUnit_iff_isUnit_det _).mp (hunit κ))
      map_one' := Units.ext (by simpa using hone)
      map_mul' := fun κ κ' => Units.ext (by simpa [Units.val_mul] using hmul κ κ') }
  have hinj : Function.Injective fgl := by
    intro κ κ' h
    have hA : s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ : MulAut W) =
        s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ' : MulAut W) := by
      have := congrArg (fun g : GL (Fin 2) (ZMod 2) =>
        (g : Matrix (Fin 2) (Fin 2) (ZMod 2))) h
      exact this
    have hlin : CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W) =
        CFSG.Quasithin.H13.Mult.linEquiv (κ' : MulAut W) := by
      refine LinearEquiv.ext fun x => c.injective ?_
      show c (CFSG.Quasithin.H13.Mult.linEquiv (κ : MulAut W) x) =
        c (CFSG.Quasithin.H13.Mult.linEquiv (κ' : MulAut W) x)
      rw [s16c1610_coord_matA hNat (κ : MulAut W) (hcomm κ) hm x,
        s16c1610_coord_matA hNat (κ' : MulAut W) (hcomm κ') hm x]
      simp only [s16c1610_actA, hA]
    apply Subtype.ext
    exact CFSG.Quasithin.H13.Mult.linEquiv.injective hlin
  have hcardGL : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
    rw [← Nat.card_congr s16c1610_permGL.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hbij : Function.Bijective fgl :=
    (Nat.bijective_iff_injective_and_card fgl).mpr
      ⟨hinj, by rw [s16c1610_card_IsSym_three hK, hcardGL]⟩
  refine ⟨(MulEquiv.ofBijective fgl hbij).trans (s16c1610_permGL).symm, fun κ => ?_⟩
  show s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ : MulAut W) =
    s16c1610_permMat ((MulEquiv.ofBijective fgl hbij).trans
      (s16c1610_permGL).symm κ)
  rw [MulEquiv.trans_apply, ← s16c1610_permGL_coe
    (s16c1610_permGL.symm ((MulEquiv.ofBijective fgl hbij) κ)), MulEquiv.apply_symm_apply]
  rfl

private theorem s16c1610_actA_smul {ρ0 ρ1 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    {c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2))} (κ : MulAut W)
    (r s : ZMod 2) (z : Fin m → ZMod 2) :
    s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ (r • z, s • z) =
      ((s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 0 0 * r +
          s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 0 1 * s) • z,
        (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 1 0 * r +
          s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ1) (c := c) κ 1 1 * s) • z) := by
  simp only [s16c1610_actA, smul_smul, ← add_smul]

private theorem s16c1610_assemble {ρ0 : ↥Lb ≃* GL (Fin m) (ZMod 2)}
    (hinf : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    {b0 : ↥(I 0) ≃* Multiplicative (Fin m → ZMod 2)}
    {b1 : ↥(I 1) ≃* Multiplicative (Fin m → ZMod 2)}
    (hb0 : ∀ (x : ↥Lb) (u : ↥(I 0)) (hu : (x : MulAut W) (u : W) ∈ I 0),
      Multiplicative.toAdd (b0 ⟨(x : MulAut W) (u : W), hu⟩) =
        (((ρ0 x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b0 u))))
    (hb1 : ∀ (x : ↥Lb) (u : ↥(I 1)) (hu : (x : MulAut W) (u : W) ∈ I 1),
      Multiplicative.toAdd (b1 ⟨(x : MulAut W) (u : W), hu⟩) =
        (((ρ0 x : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
          (Multiplicative.toAdd (b1 u))))
    (hstab0 : ∀ (x : ↥Lb) (u : ↥(I 0)), (x : MulAut W) (u : W) ∈ I 0)
    (hstab1 : ∀ (x : ↥Lb) (u : ↥(I 1)), (x : MulAut W) (u : W) ∈ I 1)
    (hdir : IsInternalDirect Kb Lb Mb) (hK : IsSym ↥Kb 3)
    (hcomm : ∀ (κ : ↥Kb) (l : ↥Lb),
      (κ : MulAut W) * (l : MulAut W) = (l : MulAut W) * κ)
    (hm : 3 ≤ m) : IsTensorS3L2 W Mb m := by
  let c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
    s16c1610_coordEquiv hinf hsup b0 b1
  have hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ0 l (c x) :=
    fun l x => s16c1610_coordEquiv_natural hinf hsup b0 b1 ρ0 ρ0 hb0 hb1 hstab0 hstab1 l x
  obtain ⟨s, hs⟩ := s16c1610_exists_permEquiv (ρ0 := ρ0) (c := c) hNat hm hK hcomm
  let φ : ↥Mb ≃* Equiv.Perm (Fin 3) × GL (Fin m) (ZMod 2) :=
    (s16c1610_prodEquiv hdir).trans (s.prodCongr ρ0)
  let Ψlin : Additive W ≃ₗ[ZMod 2]
      (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) :=
    c.trans (s16c1610_tensorEquiv m)
  let ψ : W ≃* Multiplicative
      (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) :=
    AddEquiv.toMultiplicativeRight Ψlin.toAddEquiv
  refine ⟨φ, ψ, ?_⟩
  intro γ a a' c0 c0' ha' hc'
  obtain ⟨κ0, hκ0, l0, hl0, hγ⟩ := s16c1610_mem_sup_prod hdir γ.2
  have hk := s16c1610_prod_unique hdir (s16c1610_prodFst hdir γ).2
    (s16c1610_prodSnd hdir γ).2 hκ0 hl0
    ((s16c1610_prodFst_mul_prodSnd hdir γ).trans hγ)
  have hφ1 : (φ γ).1 = s ⟨κ0, hκ0⟩ := by
    change s (s16c1610_prodFst hdir γ) = s ⟨κ0, hκ0⟩
    rw [show s16c1610_prodFst hdir γ = ⟨κ0, hκ0⟩ from Subtype.ext hk.1]
  have hφ2 : (φ γ).2 = ρ0 ⟨l0, hl0⟩ := by
    change ρ0 (s16c1610_prodSnd hdir γ) = ρ0 ⟨l0, hl0⟩
    rw [show s16c1610_prodSnd hdir γ = ⟨l0, hl0⟩ from Subtype.ext hk.2]
  rw [hφ1] at ha'
  rw [hφ2] at hc'
  let w : W := ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c0))
  have hΨ : Ψlin (Additive.ofMul w) = a ⊗ₜ[ZMod 2] c0 := by
    have h := MulEquiv.apply_symm_apply ψ (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c0))
    rw [show ψ w = Multiplicative.ofAdd (Ψlin (Additive.ofMul w)) from rfl] at h
    exact Multiplicative.ofAdd.injective h
  have hΨw : Additive.ofMul w =
      c.symm ((s16c1610_pi0 a) • c0, (s16c1610_pi1 a) • c0) := by
    calc Additive.ofMul w = Ψlin.symm (Ψlin (Additive.ofMul w)) :=
          (LinearEquiv.symm_apply_apply _ _).symm
      _ = Ψlin.symm (a ⊗ₜ[ZMod 2] c0) := by rw [hΨ]
      _ = c.symm ((s16c1610_tensorEquiv m).symm (a ⊗ₜ[ZMod 2] c0)) := rfl
      _ = c.symm ((s16c1610_pi0 a) • c0, (s16c1610_pi1 a) • c0) := by
          rw [s16c1610_tensorEquiv_symm_tmul]
  have hl : c (CFSG.Quasithin.H13.Mult.linEquiv (l0 : MulAut W) (Additive.ofMul w)) =
      ((s16c1610_pi0 a) • ((ρ0 ⟨l0, hl0⟩ : GL (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c0,
        (s16c1610_pi1 a) • ((ρ0 ⟨l0, hl0⟩ : GL (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c0) := by
    rw [hΨw, hNat ⟨l0, hl0⟩, LinearEquiv.apply_symm_apply]
    simp only [s16c1610_diag, Prod.fst, Prod.snd, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_zero, add_zero, zero_add]
  have hκ : c (CFSG.Quasithin.H13.Mult.linEquiv (κ0 : MulAut W)
      (CFSG.Quasithin.H13.Mult.linEquiv (l0 : MulAut W) (Additive.ofMul w))) =
      s16c1610_actA (ρ0 := ρ0) (ρ1 := ρ0) (c := c) (κ0 : MulAut W)
        ((s16c1610_pi0 a) • ((ρ0 ⟨l0, hl0⟩ : GL (Fin m) (ZMod 2)) :
            Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c0,
          (s16c1610_pi1 a) • ((ρ0 ⟨l0, hl0⟩ : GL (Fin m) (ZMod 2)) :
            Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c0) := by
    rw [← hl]
    exact s16c1610_coord_matA hNat (κ0 : MulAut W) (hcomm ⟨κ0, hκ0⟩) hm _
  have hgoal : Ψlin (Additive.ofMul ((γ : MulAut W) w)) = a' ⊗ₜ[ZMod 2] c0' := by
    rw [hγ]
    change (s16c1610_tensorEquiv m)
      (c (CFSG.Quasithin.H13.Mult.linEquiv (κ0 * l0) (Additive.ofMul w))) = _
    rw [map_mul, LinearEquiv.mul_apply, hκ]
    rw [s16c1610_actA_smul, s16c1610_tensorEquiv_apply]
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    rw [← hc']
    congr 1
    have h0 : s16c1610_pi0 a' = (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c)
        (κ0 : MulAut W)).mulVec ![s16c1610_pi0 a, s16c1610_pi1 a] 0 := by
      show (a' : Fin 3 → ZMod 2) 0 = _
      rw [ha', hs ⟨κ0, hκ0⟩]
      exact s16c1610_permAct_eq (s ⟨κ0, hκ0⟩) a 0
    have h1 : s16c1610_pi1 a' = (s16c1610_matA (ρ0 := ρ0) (ρ1 := ρ0) (c := c)
        (κ0 : MulAut W)).mulVec ![s16c1610_pi0 a, s16c1610_pi1 a] 1 := by
      show (a' : Fin 3 → ZMod 2) 1 = _
      rw [ha', hs ⟨κ0, hκ0⟩]
      exact s16c1610_permAct_eq (s ⟨κ0, hκ0⟩) a 1
    rw [show a' = s16c1610_pi0 a' • s16c1610_b1 + s16c1610_pi1 a' • s16c1610_b2 from
      (s16c1610_pi0_smul_b1_add_pi1_smul_b2 a').symm, h0, h1]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  rw [show ψ ((γ : MulAut W) w) = Multiplicative.ofAdd (Ψlin (Additive.ofMul ((γ : MulAut W) w)))
      from rfl, hgoal]

end Assembly

theorem s16c1610_isTensorS3L2_of_sum_natural {W : Type} [CommGroup W] [Finite W]
    {Mb Kb Lb : Subgroup (MulAut W)} {m : ℕ} (hm : 3 ≤ m) (hK : IsSym ↥Kb 3)
    (hL : IsLn ↥Lb m 1) (hdir : IsInternalDirect Kb Lb Mb)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) Lb ⊤ ⊥ 2) :
    IsTensorS3L2 W Mb m := by
  classical
  have h2 : ∀ w : W, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact s16c1610_sq_eq_one_of_sum_two hsum w
  letI : Module (ZMod 2) (Additive W) := CFSG.Quasithin.H13.Mult.zmodModuleW h2
  obtain ⟨I, hinf, hsup, hnat⟩ := s16c1610_sum_two_of_sumOfNat hsum
  have hLbig : 1 < Nat.card ↥Lb := s16c1610_one_lt_card_of_isLn hm hL
  obtain ⟨b0, ρ0, hb0⟩ := s16c1610_coords_of_binaryNaturalSL (U := I 0) hm hLbig (hnat 0)
  obtain ⟨b1, ρ1, hb1⟩ := s16c1610_coords_of_binaryNaturalSL (U := I 1) hm hLbig (hnat 1)
  have hstab0 : ∀ (x : ↥Lb) (u : ↥(I 0)), (x : MulAut W) (u : W) ∈ I 0 :=
    fun x u => s16c1610_stable_of_binaryNaturalSL (hnat 0) x u u.2
  have hstab1 : ∀ (x : ↥Lb) (u : ↥(I 1)), (x : MulAut W) (u : W) ∈ I 1 :=
    fun x u => s16c1610_stable_of_binaryNaturalSL (hnat 1) x u u.2
  let c : Additive W ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
    s16c1610_coordEquiv hinf hsup b0 b1
  have hNat : ∀ (l : ↥Lb) (x : Additive W),
      c (CFSG.Quasithin.H13.Mult.linEquiv (l : MulAut W) x) = s16c1610_diag ρ0 ρ1 l (c x) :=
    fun l x => s16c1610_coordEquiv_natural hinf hsup b0 b1 ρ0 ρ1 hb0 hb1 hstab0 hstab1 l x
  have hcomm : ∀ (κ : ↥Kb) (l : ↥Lb),
      (κ : MulAut W) * (l : MulAut W) = (l : MulAut W) * κ :=
    fun κ l => s16c1610_commute_of_commutator_eq_bot hdir κ κ.2 l l.2
  obtain ⟨κ₀, hκ₀⟩ := s16c1610_exists_offdiag hNat hcomm hm hK
  have hb1' : ∀ (θ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)),
      (∀ (l : ↥Lb) (z : Fin m → ZMod 2),
        θ (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
          (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (θ z))) →
      ∃ b1' : ↥(I 1) ≃* Multiplicative (Fin m → ZMod 2),
        ∀ (l : ↥Lb) (u : ↥(I 1)) (hu : (l : MulAut W) (u : W) ∈ I 1),
          Multiplicative.toAdd (b1' ⟨(l : MulAut W) (u : W), hu⟩) =
            (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
              (Multiplicative.toAdd (b1' u))) := by
    intro θ hθ
    refine ⟨b1.trans (AddEquiv.toMultiplicative θ.symm.toAddEquiv), ?_⟩
    intro l u hu
    have h1 : Multiplicative.toAdd ((b1.trans (AddEquiv.toMultiplicative θ.symm.toAddEquiv))
        ⟨(l : MulAut W) (u : W), hu⟩) =
        θ.symm (Multiplicative.toAdd (b1 ⟨(l : MulAut W) (u : W), hstab1 l u⟩)) := rfl
    rw [h1, hb1 l u (hstab1 l u)]
    conv_rhs => rw [show Multiplicative.toAdd ((b1.trans
        (AddEquiv.toMultiplicative θ.symm.toAddEquiv)) u) =
        θ.symm (Multiplicative.toAdd (b1 u)) from rfl]
    have h2 := hθ l (θ.symm (Multiplicative.toAdd (b1 u)))
    rw [LinearEquiv.apply_symm_apply] at h2
    rw [← h2, LinearEquiv.symm_apply_apply]
  rcases hκ₀ with h10 | h01
  · have hbij :
        Function.Bijective (s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) :=
      (s16c1610_T10_schur hNat (κ₀ : MulAut W) (hcomm κ₀)).resolve_left h10
    let θ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
      LinearEquiv.ofBijective
        (s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) hbij
    have hθ : ∀ (l : ↥Lb) (z : Fin m → ZMod 2),
        θ (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
          (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (θ z)) := by
      intro l z
      change (s16c1610_T10 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) _ = _
      rw [s16c1610_T10_comm hNat (κ₀ : MulAut W) l (hcomm κ₀ l) z]
      rfl
    obtain ⟨b1', hb1'⟩ := hb1' θ hθ
    exact s16c1610_assemble hinf hsup hb0 hb1' hstab0 hstab1 hdir hK hcomm hm
  · have hbij :
        Function.Bijective (s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) :=
      (s16c1610_T01_schur hNat (κ₀ : MulAut W) (hcomm κ₀)).resolve_left h01
    let θ : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
      (LinearEquiv.ofBijective
        (s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) hbij).symm
    have hθ : ∀ (l : ↥Lb) (z : Fin m → ZMod 2),
        θ (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
          (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (θ z)) := by
      intro l z
      apply (LinearEquiv.ofBijective (s16c1610_T01 c
        (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) hbij).injective
      rw [LinearEquiv.apply_symm_apply]
      show (((ρ0 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec z) =
        (s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W)))
          (((ρ1 l : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (θ z))
      rw [s16c1610_T01_comm hNat (κ₀ : MulAut W) l (hcomm κ₀ l) (θ z)]
      rw [show (s16c1610_T01 c (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) (θ z) = z from by
        show (LinearEquiv.ofBijective (s16c1610_T01 c
          (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) hbij)
            ((LinearEquiv.ofBijective (s16c1610_T01 c
              (CFSG.Quasithin.H13.Mult.linEquiv (κ₀ : MulAut W))) hbij).symm z) = z
        rw [LinearEquiv.apply_symm_apply]]
    obtain ⟨b1', hb1'⟩ := hb1' θ hθ
    exact s16c1610_assemble hinf hsup hb0 hb1' hstab0 hstab1 hdir hK hcomm hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
