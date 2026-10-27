module

public import CFSG.LocalAnalysis.StandardType.UnitaryEvenTorusEntries
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.UnitaryCubeRoots
public import CFSG.Open.LocalVocabulary
public import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.StandardType

namespace UnitaryEvenTorus

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open

variable {F : Type} [Field F]

@[expose] noncomputable def diagUnits (n : ℕ) : (Fin n → Fˣ) →* GL (Fin n) F :=
  (Units.map
      (diagonalRingHom (Fin n) F : (Fin n → F) →+* Matrix (Fin n) (Fin n) F).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => F)).symm.toMonoidHom

theorem coe_diagUnits (n : ℕ) (d : Fin n → Fˣ) :
    ((diagUnits n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun k => (d k : F) :=
  rfl

theorem diagUnits_mem_SU (σ : F ≃+* F) {n : ℕ} (d : Fin n → Fˣ)
    (hd : ∀ j, σ (d j : F) * (d (Fin.rev j) : F) = 1) (hdet : ∏ j, d j = 1) :
    diagUnits n d ∈ SU σ n := by
  rw [mem_SU]
  constructor
  · rw [coe_diagUnits, Matrix.det_diagonal]
    have hcoe : ((∏ j, d j : Fˣ) : F) = ∏ j, (d j : F) := by
      simpa using map_prod (Units.coeHom F) d Finset.univ
    rw [← hcoe, hdet, Units.val_one]
  · rw [coe_diagUnits, conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, antidiag, Matrix.of_apply]
    by_cases h : j = Fin.rev i
    · subst h
      simpa [antidiag] using hd i
    · simp [antidiag, h]

lemma diagonal_conj_single {n : ℕ} (d : Fin n → Fˣ) (i j : Fin n) (hij : i ≠ j) (c : F) :
    diagonal (fun k => (d k : F)) * (1 + single i j c) * diagonal (fun k => ((d k : F))⁻¹)
      = 1 + single i j ((d i : F) * c * ((d j : F))⁻¹) := by
  ext p q
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.diagonal_apply]
  by_cases h1 : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hij]
  · by_cases h2 : p = q
    · subst h2
      simp [h1, hij, Units.ne_zero]
    · simp [h1, h2]

section Even

variable [Finite F] [CharP F 2] {f : ℕ}

theorem exists_subgroup_card_three (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfe : Even f) :
    ∃ μ : Subgroup Fˣ, Nat.card μ = 3 ∧ ∀ x ∈ μ, unitaryInvolution F 2 f (x : F) = x := by
  obtain ⟨ζ, hζ1, hζ3, hσζ⟩ :=
    UnitaryCubeRoots.exists_cubeRoot_fixed_of_even (F := F) hF hf hfe
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ3
    norm_num at hζ3
  let ω : Fˣ := Units.mk0 ζ hζ0
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext
    simp [ω, hζ3]
  have hω1 : ω ≠ 1 := by
    intro h
    apply hζ1
    have := congrArg (fun u : Fˣ => (u : F)) h
    simpa [ω] using this
  have horder : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  refine ⟨Subgroup.zpowers ω, ?_, ?_⟩
  · rw [Nat.card_zpowers, horder]
  · intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hσω : unitaryInvolution F 2 f (ω : F) = (ω : F) := hσζ
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hσω]

variable {σ : F ≃+* F} {μ : Subgroup Fˣ} {n m : ℕ}

theorem diagUnits_torusEntry_mem_SU (h2m : 2 * m ≤ n) (hσμ : ∀ x ∈ μ, σ (x : F) = x)
    (hμ3 : ∀ x ∈ μ, x ^ 3 = 1) (a : Fin m → μ) : diagUnits n (torusEntry μ a) ∈ SU σ n := by
  refine diagUnits_mem_SU σ (torusEntry μ a) (fun j => ?_) (prod_torusEntry μ h2m hμ3 a)
  rw [hσμ _ (torusEntry_mem μ a j)]
  have h := congrArg (fun u : Fˣ => (u : F)) (torusEntry_mul_rev μ h2m a j)
  simpa using h

@[expose] noncomputable def torusHom (h2m : 2 * m ≤ n) (hσμ : ∀ x ∈ μ, σ (x : F) = x)
    (hμ3 : ∀ x ∈ μ, x ^ 3 = 1) : (Fin m → μ) →* SU σ n :=
  ((diagUnits n).comp (entryHom n μ)).codRestrict (SU σ n)
    (fun a => diagUnits_torusEntry_mem_SU h2m hσμ hμ3 a)

theorem coe_torusHom (h2m : 2 * m ≤ n) (hσμ : ∀ x ∈ μ, σ (x : F) = x) (hμ3 : ∀ x ∈ μ, x ^ 3 = 1)
    (a : Fin m → μ) :
    ((torusHom h2m hσμ hμ3 a : SU σ n) : GL (Fin n) F) = diagUnits n (torusEntry μ a) :=
  rfl

theorem torusHom_injective (h2m : 2 * m ≤ n) (hσμ : ∀ x ∈ μ, σ (x : F) = x)
    (hμ3 : ∀ x ∈ μ, x ^ 3 = 1) : Function.Injective (torusHom h2m hσμ hμ3) := by
  intro a b h
  apply entryHom_injective n μ (by omega)
  funext j
  apply Units.ext
  have hmat := congrArg (fun g : SU σ n =>
    (((g : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) j j) h
  simpa [coe_torusHom, coe_diagUnits, entryHom_apply] using hmat

theorem zero_ne_rev (hn : 2 ≤ n) : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
  intro h
  have h' : ((Fin.rev (⟨0, by omega⟩ : Fin n)) : ℕ) = 0 := by
    rw [← h]
  rw [Fin.val_rev] at h'
  simp at h'
  omega

theorem torusHom_conj_longRootHom_mem_range (hn : 2 ≤ n) (hm : 1 ≤ m) (h2m : 2 * m ≤ n)
    (hσμ : ∀ x ∈ μ, σ (x : F) = x) (hμ3 : ∀ x ∈ μ, x ^ 3 = 1) (a : Fin m → μ)
    (c : Multiplicative (traceZero σ)) :
    torusHom h2m hσμ hμ3 a * longRootHom σ (zero_ne_rev hn) c * (torusHom h2m hσμ hμ3 a)⁻¹ ∈
      (longRootHom σ (zero_ne_rev hn)).range := by
  have hm0 : 0 < m := by omega
  set u : F := (((a ⟨0, hm0⟩ : μ) : Fˣ) : F) with hu
  set c0 : F := (c.toAdd : F) with hc0
  have hc0zero : c0 + σ c0 = 0 := c.toAdd.2
  have hσu : σ u = u := by
    rw [hu]
    exact hσμ _ (a ⟨0, hm0⟩).2
  have hmem2 : u ^ 2 * c0 + σ (u ^ 2 * c0) = 0 := by
    rw [map_mul, map_pow, hσu, ← mul_add, hc0zero, mul_zero]
  let i : Fin n := ⟨0, by omega⟩
  let d : Fin n → Fˣ := torusEntry μ a
  have hdi : d i = a ⟨0, hm0⟩ := by
    change torusEntry μ a i = a ⟨0, hm0⟩
    rw [torusEntry_of_lt μ a (show i.val < m by simpa using hm0)]
  have hdj : d (Fin.rev i) = (a ⟨0, hm0⟩)⁻¹ := by
    change torusEntry μ a (Fin.rev i) = (a ⟨0, hm0⟩)⁻¹
    rw [torusEntry_of_rev_lt μ a (by rw [Fin.val_rev]; have hi : i.val = 0 := rfl; omega)
      (by rw [Fin.rev_rev]; exact hm0)]
    exact congrArg (fun z : Fin m => (((a z : μ) : Fˣ))⁻¹) (Fin.ext (by simp [i]))
  have hDinv : (((torusHom h2m hσμ hμ3 a)⁻¹ : SU σ n) : GL (Fin n) F) = diagUnits n d⁻¹ := by
    change (((torusHom h2m hσμ hμ3 a : SU σ n) : GL (Fin n) F))⁻¹ = diagUnits n d⁻¹
    rw [coe_torusHom]
    exact (map_inv (diagUnits n) d).symm
  have hA : (((torusHom h2m hσμ hμ3 a : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (fun k => (d k : F)) := by
    rw [coe_torusHom, coe_diagUnits]
  have hB : (((longRootHom σ (zero_ne_rev hn) c : SU σ n) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = 1 + single i (Fin.rev i) c0 := by
    rw [coe_longRootHom, longRootMatrix]
  have hC : ((((torusHom h2m hσμ hμ3 a)⁻¹ : SU σ n) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = diagonal (fun k => ((d k : F))⁻¹) := by
    rw [hDinv, coe_diagUnits]
    congr 1
    funext k
    simp
  have hR : (((torusHom h2m hσμ hμ3 a * longRootHom σ (zero_ne_rev hn) c *
        (torusHom h2m hσμ hμ3 a)⁻¹ : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (fun k => (d k : F)) * (1 + single i (Fin.rev i) c0) *
        diagonal (fun k => ((d k : F))⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simp only [Units.val_mul]
    rw [hA, hB, hC]
  refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd ⟨u ^ 2 * c0, hmem2⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext p q
  rw [coe_longRootHom]
  rw [hR]
  rw [diagonal_conj_single d i (Fin.rev i) (zero_ne_rev hn) c0]
  have hval : (d i : F) * c0 * ((d (Fin.rev i) : F))⁻¹ = u ^ 2 * c0 := by
    have h0 : (d i : F) = u := by rw [hdi, hu]
    have h1 : (d (Fin.rev i) : F) = u⁻¹ := by
      rw [hdj, hu]
      rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    rw [h0, h1, inv_inv]
    ring
  rw [hval]
  rfl

theorem torusHom_range_le_normalizer (hn : 2 ≤ n) (hm : 1 ≤ m) (h2m : 2 * m ≤ n)
    (hσμ : ∀ x ∈ μ, σ (x : F) = x) (hμ3 : ∀ x ∈ μ, x ^ 3 = 1) :
    (torusHom h2m hσμ hμ3).range ≤
      Subgroup.normalizer (((longRootHom σ (zero_ne_rev hn)).range : Subgroup (SU σ n)) :
        Set (SU σ n)) := by
  intro g hg
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hh
    exact torusHom_conj_longRootHom_mem_range hn hm h2m hσμ hμ3 a c
  · intro hh
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hh
    have hconj := torusHom_conj_longRootHom_mem_range hn hm h2m hσμ hμ3 a⁻¹ c
    rw [hc] at hconj
    rw [map_inv] at hconj
    convert hconj using 1
    group

theorem isPGroup_two_range_longRootHom (hn : 2 ≤ n) :
    IsPGroup 2 (longRootHom σ (zero_ne_rev hn)).range := by
  have hdom : IsPGroup 2 (Multiplicative (traceZero σ)) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    apply Multiplicative.ext
    apply Subtype.ext
    change (g.toAdd : F) + (g.toAdd : F) = 0
    exact CharTwo.add_self_eq_zero (g.toAdd : F)
  exact hdom.of_surjective (longRootHom σ (zero_ne_rev hn)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem range_longRootHom_ne_bot (hn : 2 ≤ n) :
    (longRootHom σ (zero_ne_rev hn)).range ≠ ⊥ := by
  intro hbot
  have h1 : (1 : F) + σ 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hmem : longRootHom σ (zero_ne_rev hn) (Multiplicative.ofAdd ⟨1, h1⟩) ∈
      (longRootHom σ (zero_ne_rev hn)).range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hentry := congrArg (fun g : SU σ n =>
    (((g : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) (⟨0, by omega⟩ : Fin n)
      (Fin.rev (⟨0, by omega⟩ : Fin n))) hmem
  rw [coe_longRootHom] at hentry
  rw [Subgroup.coe_one, Units.val_one, longRootMatrix] at hentry
  simp [Matrix.one_apply, Matrix.single_apply, zero_ne_rev hn] at hentry

end Even

theorem exists_elemAbelian_three_normalizing_longRoot [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hfe : Even f) {n : ℕ} (hn : 2 ≤ n) :
    ∃ U E : Subgroup (SU (unitaryInvolution F 2 f) n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set (SU (unitaryInvolution F 2 f) n)) ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ (n / 2) := by
  obtain ⟨μ, hμcard, hσμ⟩ := exists_subgroup_card_three (F := F) hF hf hfe
  have hμ3 : ∀ x ∈ μ, x ^ 3 = 1 := by
    intro x hx
    have hpow := pow_card_eq_one' (G := μ) (x := ⟨x, hx⟩)
    rw [hμcard] at hpow
    simpa using hpow
  set m : ℕ := n / 2 with hmdef
  have hm : 1 ≤ m := by omega
  have h2m : 2 * m ≤ n := by omega
  let U : Subgroup (SU (unitaryInvolution F 2 f) n) :=
    (longRootHom (unitaryInvolution F 2 f) (zero_ne_rev hn)).range
  let E : Subgroup (SU (unitaryInvolution F 2 f) n) :=
    (torusHom h2m hσμ hμ3).range
  have hUne : U ≠ ⊥ := range_longRootHom_ne_bot (σ := unitaryInvolution F 2 f) hn
  have hP : IsPGroup 2 U := isPGroup_two_range_longRootHom (σ := unitaryInvolution F 2 f) hn
  have hN : E ≤ Subgroup.normalizer (U : Set (SU (unitaryInvolution F 2 f) n)) :=
    torusHom_range_le_normalizer hn hm h2m hσμ hμ3
  have hcomm : IsMulCommutative E := by
    refine IsMulCommutative.of_comm fun x y => ?_
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  have hpow3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
    rw [← ha, ← map_pow]
    have ha3 : a ^ 3 = 1 := by
      funext j
      apply Subtype.ext
      simpa [Pi.pow_apply] using hμ3 (a j) (a j).2
    rw [ha3, map_one]
  have hcard : Nat.card E = 3 ^ (n / 2) := by
    have heq : Nat.card (Fin m → μ) = Nat.card E :=
      Nat.card_congr (MonoidHom.ofInjective (torusHom_injective h2m hσμ hμ3)).toEquiv
    rw [← heq, Nat.card_fun, hμcard]
    congr 1
    simp [m]
  exact ⟨U, E, hUne, hP, hN, ⟨hcomm, hpow3⟩, hcard⟩

end UnitaryEvenTorus

end CFSG.StandardType
