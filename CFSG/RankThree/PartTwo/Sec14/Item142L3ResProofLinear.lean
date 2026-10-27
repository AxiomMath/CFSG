module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofSinger
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {K : Type} [Field K]

@[expose] noncomputable def rhoSL (q : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin 3) K →* projImage (slPi true 3 q K) where
  toFun g := ⟨ProjGenLinGroup.mk (SpecialLinearGroup.toGL g),
    SpecialLinearGroup.toGL g, (mem_slPi_true q).mpr g.2, rfl⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem coe_rhoSL (q : ℕ) (g : SpecialLinearGroup (Fin 3) K) :
    ((rhoSL q K g : projImage (slPi true 3 q K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) :=
  rfl

theorem rhoSL_surjective (q : ℕ) : Function.Surjective (rhoSL q K) := by
  intro m
  obtain ⟨A, hA, hAm⟩ := m.2
  let g : SpecialLinearGroup (Fin 3) K := ⟨(A : Matrix (Fin 3) (Fin 3) K), (mem_slPi_true q).mp hA⟩
  refine ⟨g, Subtype.ext ?_⟩
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) = _
  rw [← hAm]
  congr 1
  exact Units.ext rfl

theorem rhoSL_conjUnit {p f : ℕ} (hπ : true = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi true 3 (p ^ f) K) (x : SpecialLinearGroup (Fin 3) K) :
    rhoSL (p ^ f) K (conjUnit g x) = Res8Hess.conjM' hπ hg (rhoSL (p ^ f) K x) := by
  apply Subtype.ext
  rw [Res8Hess.coe_conjM', coe_rhoSL, coe_rhoSL, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rfl

theorem heisC_irreducible {β : K} (hβ : ¬ ∃ μ : K, μ ^ 3 = β) (W : Submodule K (Fin 3 → K))
    (hW : ∀ v ∈ W, heisC β *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_invariant (fun μ hμ => hβ ⟨μ, hμ⟩) (heisC_pow_three β) hW

theorem diagTau_mul_heisC {τ : K} (hτ : τ ^ 3 = 1) (β : K) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * heisC β =
      τ • (heisC β * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-1 : K) * hτ

theorem heisC_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (β : K) :
    heisC β * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ ^ 2 • (((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * heisC β) := by
  rw [coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-τ) * hτ | linear_combination (-β) * hτ

theorem heisC_mul_diagSL (β a b d : K) (h : a * b * d = 1) (h' : d * a * b = 1) :
    heisC β * ((diagSL a b d h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((diagSL d a b h' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        heisC β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, diagSL, Matrix.mul_apply, Fin.sum_univ_three]
  ring1

theorem diagSL_mul (a b d a' b' d' : K) (h : a * b * d = 1) (h' : a' * b' * d' = 1)
    (h'' : a * a' * (b * b') * (d * d') = 1) :
    diagSL a b d h * diagSL a' b' d' h' = diagSL (a * a') (b * b') (d * d') h'' := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem diagSL_pow (a b d : K) (h : a * b * d = 1) (n : ℕ) :
    diagSL a b d h ^ n = diagSL (a ^ n) (b ^ n) (d ^ n)
      (by rw [← mul_pow, ← mul_pow, h, one_pow]) := by
  induction n with
  | zero =>
    rw [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagSL]
  | succ n ih =>
    rw [pow_succ, ih, diagSL_mul _ _ _ _ _ _ _ _ (by
      rw [← pow_succ, ← pow_succ, ← pow_succ, ← mul_pow, ← mul_pow, h, one_pow])]
    congr 1 <;> rw [pow_succ]

theorem diagSL_one (h : (1 : K) * 1 * 1 = 1) : diagSL 1 1 1 h = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagSL]

@[expose] def torusSL (c : GL (Fin 3) K) : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  (Subgroup.centralizer {c}).comap SpecialLinearGroup.toGL

theorem mem_torusSL {c : GL (Fin 3) K} {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ torusSL c ↔ (c : Matrix (Fin 3) (Fin 3) K) * g = (g : Matrix (Fin 3) (Fin 3) K) * c := by
  rw [torusSL, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Units.ext_iff]
  exact eq_comm

theorem conjUnit_mem_torusSL {c h : GL (Fin 3) K} {s : Kˣ}
    (hhc : h * c * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s * c)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ torusSL c) : conjUnit h g ∈ torusSL c := by
  rw [torusSL, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  have e : SpecialLinearGroup.toGL (conjUnit h g) = h * SpecialLinearGroup.toGL g * h⁻¹ :=
    Units.ext rfl
  rw [e]
  set z := Matrix.GeneralLinearGroup.scalar (Fin 3) s with hz
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s x).eq
  set u := SpecialLinearGroup.toGL g with hu
  have hzc' : ∀ x : GL (Fin 3) K, x * z⁻¹ = z⁻¹ * x := fun x => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hzc, inv_mul_cancel_left]
  have hc : c = z⁻¹ * (h * c * h⁻¹) := by rw [hhc]; group
  calc h * u * h⁻¹ * c = h * u * h⁻¹ * (z⁻¹ * (h * c * h⁻¹)) := by rw [← hc]
    _ = z⁻¹ * (h * u * h⁻¹ * (h * c * h⁻¹)) := by
        rw [← mul_assoc (h * u * h⁻¹), hzc' (h * u * h⁻¹), mul_assoc]
    _ = z⁻¹ * (h * (u * c) * h⁻¹) := by group
    _ = z⁻¹ * (h * (c * u) * h⁻¹) := by rw [hg]
    _ = z⁻¹ * (h * c * h⁻¹) * (h * u * h⁻¹) := by group
    _ = c * (h * u * h⁻¹) := by rw [← hc]

variable [Finite K]

@[expose] def diagMuSL (K : Type) [Field K] [Finite K] :
    Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ (a b d : K) (h : a * b * d = 1), a ∈ muM K ∧ b ∈ muM K ∧ d ∈ muM K ∧
    g = diagSL a b d h}
  mul_mem' := by
    rintro _ _ ⟨a, b, d, h, ha, hb, hd, rfl⟩ ⟨a', b', d', h', ha', hb', hd', rfl⟩
    have h'' : a * a' * (b * b') * (d * d') = 1 := by
      calc a * a' * (b * b') * (d * d') = (a * b * d) * (a' * b' * d') := by ring
        _ = 1 := by rw [h, h', one_mul]
    exact ⟨a * a', b * b', d * d', h'', muM_mul ha ha', muM_mul hb hb', muM_mul hd hd',
      diagSL_mul a b d a' b' d' h h' h''⟩
  one_mem' := ⟨1, 1, 1, by ring, one_mem_muM, one_mem_muM, one_mem_muM, (diagSL_one _).symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, d, h, ha, hb, hd, rfl⟩
    have ha0 := ne_zero_of_mem_muM ha
    have hb0 := ne_zero_of_mem_muM hb
    have hd0 := ne_zero_of_mem_muM hd
    have h' : a⁻¹ * b⁻¹ * d⁻¹ = 1 := by
      rw [← mul_inv, ← mul_inv, h, inv_one]
    refine ⟨a⁻¹, b⁻¹, d⁻¹, h', muM_inv ha, muM_inv hb, muM_inv hd, ?_⟩
    refine inv_eq_of_mul_eq_one_left ?_
    rw [diagSL_mul a⁻¹ b⁻¹ d⁻¹ a b d h' h (by
      rw [inv_mul_cancel₀ ha0, inv_mul_cancel₀ hb0, inv_mul_cancel₀ hd0]; ring)]
    simp only [inv_mul_cancel₀ ha0, inv_mul_cancel₀ hb0, inv_mul_cancel₀ hd0]
    exact diagSL_one _

theorem pow_eq_one_of_mem_diagMuSL {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ diagMuSL K) :
    g ^ ordCompl[3] (Nat.card K - 1) = 1 := by
  obtain ⟨a, b, d, h, ha, hb, hd, rfl⟩ := hg
  rw [diagSL_pow]
  simp only [(mem_muM).mp ha, (mem_muM).mp hb, (mem_muM).mp hd]
  exact diagSL_one _

theorem three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ]
    omega

theorem ne_three_pow_of_ne_four {p f k : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 3 = 1)
    (h4 : p ^ f ≠ 4) : p ^ f - 1 ≠ 3 ^ k := by
  intro hk
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  rcases hp.eq_two_or_odd' with rfl | hpo
  · rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | hf3
    · norm_num at hq
    · exact h4 (by norm_num)
    · have h8 : 2 ^ f % 8 = 0 := by
        obtain ⟨j, rfl⟩ : ∃ j, f = j + 3 := ⟨f - 3, by omega⟩
        rw [pow_add]
        norm_num [Nat.mul_mod_left]
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      rcases three_pow_mod_eight k with h | h <;> omega
  · have hpf : Odd (p ^ f) := hpo.pow
    have h1 : 1 ≤ p ^ f := hpf.pos
    have : Even (p ^ f - 1) := by
      obtain ⟨r, hr⟩ := hpf
      exact ⟨r, by omega⟩
    rw [hk] at this
    exact (Nat.not_even_iff_odd.mpr hodd) this

theorem exists_muM_pow_three_ne_one {p f : ℕ} (hK : PiField true p f K)
    (hq : ModThree true (p ^ f)) (h4 : p ^ f ≠ 4) : ∃ b ∈ muM K, b ^ 3 ≠ 1 := by
  have hcard : Nat.card K = p ^ f := hK.card
  have hq' : p ^ f % 3 = 1 := hq
  have hpf : 1 < p ^ f := Nat.one_lt_pow (by have := hK.one_le; omega) hK.prime.one_lt
  set m := ordCompl[3] (Nat.card K - 1) with hmdef
  set k := (Nat.card K - 1).factorization 3 with hkdef
  have hqkm : 3 ^ k * m = Nat.card K - 1 := Nat.ordProj_mul_ordCompl_eq_self _ 3
  have hm3 : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three (by omega)
  have hm1 : m ≠ 1 := by
    intro h1
    rw [h1, mul_one, hcard] at hqkm
    exact ne_three_pow_of_ne_four hK.prime hK.one_le hq' h4 hqkm.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hk0 : 3 ^ k ≠ 0 := by positivity
  have hgk : orderOf (g ^ 3 ^ k) = m := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hgo, ← hqkm]; exact dvd_mul_right _ _), hgo, ← hqkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨((g ^ 3 ^ k : Kˣ) : K), ?_, ?_⟩
  · rw [mem_muM, ← hmdef, ← Units.val_pow_eq_pow_val, ← hgk, pow_orderOf_eq_one, Units.val_one]
  · intro h3
    have h3' : (g ^ 3 ^ k) ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h3,
      Units.val_one])
    have hdvd := orderOf_dvd_of_pow_eq_one h3'
    rw [hgk] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact hm1 h
    · exact hm3 ⟨1, by omega⟩

variable {p f : ℕ}

theorem torus_mem_invSet142 (hπ : true = false → UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0) {β : K} {cβ : GL (Fin 3) K}
    (hcβ : cβ ∈ glPi true 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi true 3 (p ^ f) K)
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) (hβ : ¬ ∃ μ : K, μ ^ 3 = β) :
    (torusSL cβ).map (rhoSL (p ^ f) K) ∈
      invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (cβ : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    rw [hcβm]
    exact heisC_irreducible hβ
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  refine ⟨not_three_dvd_card_of_pow_three ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ hg3
    have hs3 : SpecialLinearGroup.toGL g ^ 3 ∈ StatedScalars (Fin 3) K := by
      have e := congrArg Subtype.val hg3
      rw [Subgroup.coe_pow, coe_rhoSL, OneMemClass.coe_one, ← map_pow] at e
      exact mk_eq_one_iff_mem_statedScalars.mp e
    have hsZ : SpecialLinearGroup.toGL g ∈ StatedScalars (Fin 3) K := by
      by_contra hsZ
      refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 g.2 hs3 hsZ ?_ hirr
      exact Units.ext ((mem_torusSL.mp hg).trans rfl)
    apply Subtype.ext
    rw [coe_rhoSL, OneMemClass.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨conjUnit cβ g, conjUnit_mem_torusSL (s := 1) (by rw [map_one, one_mul]; group) hg,
      ?_⟩
    exact rhoSL_conjUnit hπ hcβ g
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨conjUnit (diagTau hτ) g, conjUnit_mem_torusSL (s := Units.mk0 τ hτ0) ?_ hg,
      rhoSL_conjUnit hπ hd g⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hcβm, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0, diagTau_mul_heisC hτ β, Matrix.smul_mul, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]

theorem diagMu_mem_invSet142 (hπ : true = false → UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) {β : K} {cβ : GL (Fin 3) K}
    (hcβ : cβ ∈ glPi true 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi true 3 (p ^ f) K)
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) :
    (diagMuSL K).map (rhoSL (p ^ f) K) ∈
      invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd) := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  refine ⟨not_three_dvd_card_of_pow_three ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ hg3
    have hm : rhoSL (p ^ f) K g ^ ordCompl[3] (Nat.card K - 1) = 1 := by
      rw [← map_pow, pow_eq_one_of_mem_diagMuSL hg, map_one]
    have hm3 : Nat.Coprime (ordCompl[3] (Nat.card K - 1)) 3 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (Nat.not_dvd_ordCompl Nat.prime_three (by
          have : 1 < Nat.card K := Finite.one_lt_card
          omega)))
    have := pow_gcd_eq_one.mpr ⟨hm, hg3⟩
    rwa [hm3, pow_one] at this
  · rintro _ ⟨_, ⟨g, ⟨a, b, d, h, ha, hb, hd', rfl⟩, rfl⟩, rfl⟩
    have h' : d * a * b = 1 := by rw [← h]; ring
    refine ⟨diagSL d a b h', ⟨d, a, b, h', hd', ha, hb, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← rhoSL_conjUnit hπ hcβ]
    congr 1
    exact (Sec19.Item19Res5Proof.conjUnit_eq_of_mul_eq
      (by rw [hcβm]; exact heisC_mul_diagSL β a b d h h')).symm
  · rintro _ ⟨_, ⟨g, ⟨a, b, d, h, ha, hb, hd', rfl⟩, rfl⟩, rfl⟩
    refine ⟨diagSL a b d h, ⟨a, b, d, h, ha, hb, hd', rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← rhoSL_conjUnit hπ hd]
    congr 1
    refine (Sec19.Item19Res5Proof.conjUnit_eq_of_mul_eq ?_).symm
    rw [coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem ks142L3PGLGenStd_linear (hπ : true = false → UnitaryFieldData p f K)
    (hK : PiField true p f K) (hq : ModThree true (p ^ f)) (h4 : p ^ f ≠ 4)
    [Group.IsPerfect (projImage (slPi true 3 (p ^ f) K))] {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K} (hcβ : cβ ∈ glPi true 3 (p ^ f) K)
    (hd : diagTau hτ ∈ glPi true 3 (p ^ f) K)
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) (hβ : ¬ ∃ μ : K, μ ^ 3 = β) :
    sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hω : τ ^ 2 + τ + 1 = 0 := by
    have h1 : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hτ1)
  have h3 : (3 : K) ≠ 0 := by
    intro h
    apply hτ1
    have h2 : (τ - 1) ^ 2 = 0 := by linear_combination hω - τ * h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hβ ⟨0, by ring⟩
  set σ := Res8Hess.conjM' hπ hcβ with hσ
  set N := sSup (invSet142 σ (Res8Hess.conjM' hπ hd)) with hN
  have hτ' : τ * τ ^ 2 * 1 = 1 := by linear_combination hτ
  set D := rhoSL (p ^ f) K (diagSL τ (τ ^ 2) 1 hτ') with hD
  have hDm : SpecialLinearGroup.toGL (diagSL τ (τ ^ 2) 1 hτ') = diagTau hτ := by
    apply Units.ext
    rw [coe_diagTau]
    rfl
  have hconjD : Res8Hess.conjM' hπ hd = MulAut.conj D := by
    ext m
    rw [Res8Hess.coe_conjM', MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hD, coe_rhoSL, hDm]
  have hσD : σ D = D := by
    apply Subtype.ext
    rw [hσ, Res8Hess.coe_conjM', hD, coe_rhoSL, hDm, ← map_inv, ← map_mul, ← map_mul,
      ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 (τ ^ 2)⁻¹ (inv_ne_zero (pow_ne_zero 2 hτ0)), Units.ext ?_⟩
    have e := heisC_mul_diagTau hτ β
    rw [← hcβm] at e
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0, e, Matrix.smul_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero 2 hτ0), one_smul]
  set Y := N ⊔ Subgroup.zpowers D with hY
  set K₁ := Y.comap (rhoSL (p ^ f) K) with hK₁
  have hNY : N ≤ Y := le_sup_left
  have hinvN := map_sSup_invSet142_le (σ := σ) (τ := Res8Hess.conjM' hπ hd)
  obtain ⟨b, hbS, hb3⟩ := exists_muM_pow_three_ne_one hK hq h4
  have hdiag : ∀ (a b d : K) (h : a * b * d = 1), a ∈ muM K → b ∈ muM K → d ∈ muM K →
      diagSL a b d h ∈ K₁ := by
    intro a b d h ha hb hd'
    exact hNY (le_sSup (diagMu_mem_invSet142 hπ hτ hcβ hd hcβm)
      ⟨diagSL a b d h, ⟨a, b, d, h, ha, hb, hd', rfl⟩, rfl⟩)
  have hD1 : ∀ h : 1 * τ * τ ^ 2 = 1, diagSL 1 τ (τ ^ 2) h ∈ K₁ := by
    intro h
    have e : rhoSL (p ^ f) K (diagSL 1 τ (τ ^ 2) h) = D := by
      apply Subtype.ext
      rw [hD, coe_rhoSL, coe_rhoSL, ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨Units.mk0 τ hτ0, Units.ext ?_⟩
      change (diagSL 1 τ (τ ^ 2) h : Matrix (Fin 3) (Fin 3) K) *
          ((Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) = (diagSL τ (τ ^ 2) 1 hτ' : Matrix (Fin 3) (Fin 3) K)
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | ring1 | linear_combination hτ
    change rhoSL (p ^ f) K (diagSL 1 τ (τ ^ 2) h) ∈ Y
    rw [e]
    exact le_sup_right (a := N) (Subgroup.mem_zpowers D)
  have hT : ∀ y : SpecialLinearGroup (Fin 3) K,
      heisC β * (y : Matrix (Fin 3) (Fin 3) K) = (y : Matrix (Fin 3) (Fin 3) K) * heisC β →
        y ∈ K₁ := by
    intro y hy
    rw [← hcβm] at hy
    exact hNY (le_sSup (torus_mem_invSet142 hπ hτ hτ1 h3 hcβ hd hcβm hβ)
      ⟨y, mem_torusSL.mpr hy, rfl⟩)
  have hinv : ∀ x ∈ K₁, conjUnit cβ x ∈ K₁ := by
    intro x hx
    change rhoSL (p ^ f) K (conjUnit cβ x) ∈ Y
    rw [rhoSL_conjUnit hπ hcβ]
    have hYσ : Y.map σ.toMonoidHom ≤ Y := by
      rw [hY, Subgroup.map_sup]
      refine sup_le (hinvN.1.trans le_sup_left) ?_
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hσD]
      exact le_sup_right
    exact hYσ ⟨_, hx, rfl⟩
  have hK₁top : K₁ = ⊤ :=
    eq_top_of_singer_muM hω hτ1 hβ0 hβ hbS hb3 hdiag hD1 hT hcβm hinv
  have hYtop : Y = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨g, rfl⟩ := rhoSL_surjective (p ^ f) m
    have : g ∈ K₁ := hK₁top ▸ Subgroup.mem_top g
    exact this
  have hND : N.map (MulAut.conj D).toMonoidHom ≤ N := by
    rw [← hconjD]
    exact hinvN.2
  exact eq_top_of_sup_zpowers hND hYtop

end CFSG.RankThree.PartTwo.Sec14.L3PGL
