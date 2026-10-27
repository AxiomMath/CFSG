module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfA
public import CFSG.Quasithin.Background.C35InspL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Quasithin.H13.NQCatParabolicSL3
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112

public section

namespace CFSG.Quasithin.H13.Ch9.F112Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits Matrix
open scoped commutatorElement

section Coord

variable {A : Type*} [Group A] [Finite A] {D : Subgroup A} {F : Type} [Field F] [CharP F 2]

theorem pCore_eq_ker (hK4 : ∃ s : Finset F, s.card = 4) (act : ↥D →* SpecialLinearGroup (Fin 2) F)
    (hact : Function.Surjective act) (hker : IsPGroup 2 act.ker) :
    CFSG.Open.pCore 2 ↥D = act.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_pCore 2 (MonoidHom.normal_ker act) hker)
  have hs : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
  have hp : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hK4
  have hn : ((CFSG.Open.pCore 2 ↥D).map act).Normal := Subgroup.Normal.map inferInstance act hact
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCore 2 ↥D).map act) with h | h
  · intro x hx
    have h1 := Subgroup.mem_map_of_mem act hx
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · exfalso
    have : Finite (SpecialLinearGroup (Fin 2) F) := Finite.of_surjective act hact
    have hO := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥D)
    have h2 : IsPGroup 2 (SpecialLinearGroup (Fin 2) F) := by
      intro y
      have hy : y ∈ (CFSG.Open.pCore 2 ↥D).map act := h ▸ Subgroup.mem_top y
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨k, hk⟩ := hO ⟨a, ha⟩
      refine ⟨k, ?_⟩
      have e : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow, e, map_one]
    exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent

theorem genComm_of_coord (hK4 : ∃ s : Finset F, s.card = 4)
    (act : ↥D →* SpecialLinearGroup (Fin 2) F) (hact : Function.Surjective act)
    (hker : IsPGroup 2 act.ker) (c : ↥D → (Fin 2 → F))
    (hmul : ∀ r s, act r = 1 → act s = 1 → c (r * s) = c r + c s)
    (hconj : ∀ n r, act r = 1 → c (n * r * n⁻¹) =
      ((act n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ c r)
    (hZ : ∀ r, act r = 1 → c r = 0 → (r : A) ∈ ⁅pCoreOf 2 D, D⁆) : GenComm D := by
  have hOk := pCore_eq_ker hK4 act hact hker
  set N := ⁅pCoreOf 2 D, D⁆ with hN
  have hc1 : c 1 = 0 := by
    have h := hmul 1 1 (map_one act) (map_one act)
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  have hinv : ∀ r, act r = 1 → c r⁻¹ = -c r := by
    intro r hr
    have h := hmul r r⁻¹ hr (by rw [map_inv, hr, inv_one])
    rw [mul_inv_cancel, hc1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hstep : ∀ k, act k = 1 → ∀ n, act ⁅k, n⁆ = 1 ∧ ((⁅k, n⁆ : ↥D) : A) ∈ N ∧
      c ⁅k, n⁆ = c k - ((act n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        c k := by
    intro k hk n
    have hk' : act (n * k⁻¹ * n⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hk, inv_one, mul_one, map_inv, mul_inv_cancel]
    refine ⟨?_, ?_, ?_⟩
    · rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hk]
      group
    · have hkO : (k : A) ∈ pCoreOf 2 D := ⟨k, by rw [hOk]; exact hk, rfl⟩
      have e : ((⁅k, n⁆ : ↥D) : A) = ⁅(k : A), (n : A)⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp
      rw [e]
      exact Subgroup.commutator_mem_commutator hkO n.2
    · have e : ⁅k, n⁆ = k * (n * k⁻¹ * n⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e, hmul _ _ hk hk', hconj n k⁻¹ (by rw [map_inv, hk, inv_one]), hinv k hk,
        Matrix.mulVec_neg, sub_eq_add_neg]
  have hcu : ∀ k, act k = 1 → ∀ t : F, ∃ m, act m = 1 ∧ (m : A) ∈ N ∧ c m = ![-(t * c k 1), 0] := by
    intro k hk t
    obtain ⟨n, hn⟩ := hact ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    obtain ⟨h1, h2, h3⟩ := hstep k hk n
    refine ⟨_, h1, h2, ?_⟩
    rw [h3, hn]
    ext i
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_two]
  have hcl : ∀ k, act k = 1 → ∀ t : F, ∃ m, act m = 1 ∧ (m : A) ∈ N ∧ c m = ![0, -(t * c k 0)] := by
    intro k hk t
    obtain ⟨n, hn⟩ := hact ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩
    obtain ⟨h1, h2, h3⟩ := hstep k hk n
    refine ⟨_, h1, h2, ?_⟩
    rw [h3, hn]
    ext i
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_two]
  have hmain : ∀ r, act r = 1 → (r : A) ∈ N := by
    intro r hr
    have hex : ∃ m, act m = 1 ∧ (m : A) ∈ N ∧ c m = c r := by
      by_cases h0 : c r 0 = 0 <;> by_cases h1 : c r 1 = 0
      · refine ⟨1, map_one act, N.one_mem, ?_⟩
        rw [hc1]
        ext i
        fin_cases i <;> simp [h0, h1]
      · obtain ⟨m₁, hm₁, -, hc₁⟩ := hcu r hr (-1)
        obtain ⟨m₂, hm₂, hN₂, hc₂⟩ := hcl m₁ hm₁ (-1)
        refine ⟨m₂, hm₂, hN₂, ?_⟩
        rw [hc₂, hc₁]
        ext i
        fin_cases i <;> simp [h0]
      · obtain ⟨m₁, hm₁, -, hc₁⟩ := hcl r hr (-1)
        obtain ⟨m₂, hm₂, hN₂, hc₂⟩ := hcu m₁ hm₁ (-1)
        refine ⟨m₂, hm₂, hN₂, ?_⟩
        rw [hc₂, hc₁]
        ext i
        fin_cases i <;> simp [h1]
      · obtain ⟨m₁, hm₁, hN₁, hc₁⟩ := hcu r hr (-(c r 0 / c r 1))
        obtain ⟨m₂, hm₂, hN₂, hc₂⟩ := hcl r hr (-(c r 1 / c r 0))
        refine ⟨m₁ * m₂, by rw [map_mul, hm₁, hm₂, mul_one], ?_, ?_⟩
        · rw [Subgroup.coe_mul]
          exact N.mul_mem hN₁ hN₂
        · rw [hmul _ _ hm₁ hm₂, hc₁, hc₂]
          ext i
          fin_cases i
          · simp
            field_simp
          · simp
            field_simp
    obtain ⟨m, hm, hmN, hcm⟩ := hex
    have hr' : act (m⁻¹ * r) = 1 := by rw [map_mul, map_inv, hm, hr, inv_one, one_mul]
    have hc' : c (m⁻¹ * r) = 0 := by
      rw [hmul _ _ (by rw [map_inv, hm, inv_one]) hr, hinv m hm, hcm, neg_add_cancel]
    have e : (r : A) = m * ((m⁻¹ * r : ↥D) : A) := by simp
    rw [e]
    exact N.mul_mem hmN (hZ _ hr' hc')
  intro x hx
  obtain ⟨r, hr, rfl⟩ := hx
  rw [hOk] at hr
  exact hmain r hr

end Coord

section L3

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {A : Type*} [Group A]

theorem genComm_map_iff_injOn {B : Type*} [Group B] {f : A →* B} {D : Subgroup A}
    (hf : Set.InjOn f D) : GenComm (D.map f) ↔ GenComm D := by
  have hρ : Function.Injective (f.comp D.subtype) := fun x y h => Subtype.ext (hf x.2 y.2 h)
  have e1 : D.map f = (⊤ : Subgroup ↥D).map (f.comp D.subtype) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have e2 : (⊤ : Subgroup ↥D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [e1, genComm_map_iff hρ, ← genComm_map_iff D.subtype_injective, e2]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem genComm_Q3 (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (hK4 : ∃ s : Finset K, s.card = 4)
    (j : Fin 2) : GenComm (perfectCore (Q3 K j)) := by
  obtain ⟨act, c, hacts, hker, hmul, hc0, hconj⟩ := C35Pf.radical_data hK hK4 j
  refine genComm_of_coord hK4 act hacts hker c hmul hconj fun r hr h0 => ?_
  rw [hc0 r hr h0, Subgroup.coe_one]
  exact Subgroup.one_mem _

theorem injOn_proj_Q3 (j : Fin 2) :
    Set.InjOn (proj 3 K) (perfectCore (Q3 K j) : Set (SpecialLinearGroup (Fin 3) K)) := by
  intro x hx y hy hxy
  have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have h1 := blk3_scalars j ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩ ((ker_proj 3 K).le hz)
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

theorem hasModelFacts_l3 (f : ℕ) (hf : 2 ≤ f) : HasModelFacts (IsLieOverTwo .PSL 3 f) := by
  intro Y _ hY
  have hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 3 2 f := by
    rcases hY with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  have hfin : Finite Y := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hX
    exact Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, fun T hT => ?_⟩
  obtain ⟨K, _, _, _, φ, hcard, hφ, hres, -⟩ := even_rank_two_residual_linear hX hT
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨_, hres, fun j => ⟨?_, ?_⟩⟩
  · have hT' : T = (projUnitriangular 3 K).map φ.symm.toMonoidHom := by
      rw [← hφ, Subgroup.map_map]
      have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
        ext
        simp
      rw [e, Subgroup.map_id]
    have h1 : projUnitriangular 3 K ≤ perfectCore ((Q3 K j).map (proj 3 K)) := by
      rw [← map_perfectCore]
      exact Subgroup.map_mono (NQCat.SL3.unitriangular_le_perfectCore hK4 j)
    show T ≤ perfectCore (((Q3 K j).map (proj 3 K)).map φ.symm.toMonoidHom)
    rw [hT', ← map_perfectCore]
    exact Subgroup.map_mono h1
  · show GenComm (perfectCore (((Q3 K j).map (proj 3 K)).map φ.symm.toMonoidHom))
    rw [← map_perfectCore, genComm_map_iff φ.symm.injective, ← map_perfectCore,
      genComm_map_iff_injOn (injOn_proj_Q3 j)]
    exact genComm_Q3 hK hK4 j

end L3

end CFSG.Quasithin.H13.Ch9.F112Pf
