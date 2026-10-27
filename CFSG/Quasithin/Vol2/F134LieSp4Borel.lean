module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSuborbit
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Basic
public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.F134.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher SymplecticFour Submodule
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauEquiv tauMat_apply tauPair)

variable {K : Type} [Field K]

local notation "M[" g "]" => Units.val (Subtype.val g)

theorem mem_flag_one_iff {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ flag 2 K 1 ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 ∧ v (Sum.inl 1) = 0 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0, h1 1, h2 1 (by simp)⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h0
      · exact h1
    · fin_cases j
      · simp at hj
      · exact h2

theorem mem_flag_two_iff {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ flag 2 K 2 ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  rw [mem_flag_of_le le_rfl, mem_isoFlag]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    fin_cases j
    · exact h0
    · exact h1

theorem eq_smul_e1_of_mem_flag_one {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K 1) :
    v = v (Sum.inl 0) • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) := by
  obtain ⟨h0, h1, h2⟩ := mem_flag_one_iff.mp hv
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [h0, h1, h2]

theorem single_inl_zero_ne_zero : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl 0)
  simp at this

theorem mem_stabilizer_of_mulVec_mem' {r : ℕ} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {g : StatedSp r K} (h : ∀ v ∈ W, M[g] *ᵥ v ∈ W) : g ∈ stabilizer r K W := by
  rw [mem_stabilizer]
  refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_map_spAct g W)
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

theorem mulVec_mem_of_mem_stabilizer {r : ℕ} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {g : StatedSp r K} (hg : g ∈ stabilizer r K W) {v : Fin r ⊕ Fin r → K} (hv : v ∈ W) :
    M[g] *ᵥ v ∈ W := by
  rw [← mem_stabilizer.mp hg]
  exact ⟨v, hv, rfl⟩

theorem mem_stabilizer_one_iff {g : StatedSp 2 K} : g ∈ stabilizer 2 K (flag 2 K 1) ↔
    M[g] (Sum.inr 0) (Sum.inl 0) = 0 ∧ M[g] (Sum.inr 1) (Sum.inl 0) = 0 ∧
      M[g] (Sum.inl 1) (Sum.inl 0) = 0 := by
  constructor
  · intro hg
    have he : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 :=
      mem_flag_one_iff.mpr (by simp)
    simpa using mem_flag_one_iff.mp (mulVec_mem_of_mem_stabilizer hg he)
  · intro h
    refine mem_stabilizer_of_mulVec_mem' fun v hv => ?_
    rw [eq_smul_e1_of_mem_flag_one hv, mulVec_smul]
    refine Submodule.smul_mem _ _ (mem_flag_one_iff.mpr ?_)
    simpa using h

theorem mem_stabilizer_two_iff {g : StatedSp 2 K} : g ∈ stabilizer 2 K (flag 2 K 2) ↔
    ∀ i j : Fin 2, M[g] (Sum.inr i) (Sum.inl j) = 0 := by
  constructor
  · intro hg i j
    have he : (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 :=
      mem_flag_two_iff.mpr (by simp)
    have h := mem_flag_two_iff.mp (mulVec_mem_of_mem_stabilizer hg he)
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  · intro h
    refine mem_stabilizer_of_mulVec_mem' fun v hv => ?_
    obtain ⟨h0, h1⟩ := mem_flag_two_iff.mp hv
    rw [mem_flag_two_iff]
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h, h0, h1]

theorem mem_borelSubgroup_iff {g : StatedSp 2 K} : g ∈ borelSubgroup 2 K ↔
    g ∈ stabilizer 2 K (flag 2 K 1) ∧ g ∈ stabilizer 2 K (flag 2 K 2) := by
  rw [mem_borelSubgroup]
  constructor
  · intro h
    exact ⟨h 1 le_rfl (by norm_num), h 2 (by norm_num) le_rfl⟩
  · rintro ⟨h1, h2⟩ i hi1 hi2
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · exact h1
    · exact h2

theorem unipotent_mulVec_e1 {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K) :
    M[u] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) = Pi.single (Sum.inl 0) 1 := by
  have h := (unitriangular_invariant_isotropic_subspaces (r := 2) (K := K)).1
  have hmem : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈
      {v : Fin 2 ⊕ Fin 2 → K | ∀ u ∈ unipotent 2 K, M[u] *ᵥ v = v} := by
    rw [h]
    exact mem_flag_one_iff.mpr (by simp)
  exact hmem u hu

theorem exists_mulVec_e1 {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K) {x : StatedSp 2 K} (hx : x ∈ P) :
    ∃ y ∈ P, M[y] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) =
      M[u] *ᵥ (M[x] *ᵥ Pi.single (Sum.inl 0) 1) := by
  obtain ⟨y, hy, s, hs, hus⟩ := hPU u hu x hx
  refine ⟨y, hy, ?_⟩
  rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, hus, Subgroup.coe_mul, Units.val_mul,
    ← mulVec_mulVec, unipotent_mulVec_e1 hs]

theorem tau_sym2_mulVec_inl_zero (a b : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[tau (sym2_transpose a b 0)] *ᵥ v) (Sum.inl 0) =
      v (Sum.inl 0) + (a * v (Sum.inr 0) + b * v (Sum.inr 1)) := by
  rw [coe_tau]
  simp [mulVec, dotProduct, Fin.sum_univ_two, sym2]

theorem tau_sym2_mulVec_inl_one (a b : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (M[tau (sym2_transpose a b 0)] *ᵥ v) (Sum.inl 1) = v (Sum.inl 1) + b * v (Sum.inr 0) := by
  rw [coe_tau]
  simp [mulVec, dotProduct, Fin.sum_univ_two, sym2]

theorem mulVec_e1_inr_zero [Finite K] {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hcard : Nat.card P < Nat.card K ^ 2) {x : StatedSp 2 K} (hx : x ∈ P) :
    (M[x] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) (Sum.inr 0) = 0 := by
  by_contra hne
  set v := M[x] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with hv
  have key : ∀ p : K × K, ∃ y : P, M[(y : StatedSp 2 K)] *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) = M[tau (sym2_transpose p.1 p.2 0)] *ᵥ v := by
    intro p
    obtain ⟨y, hy, hyv⟩ :=
      exists_mulVec_e1 hPU (tau_mem_unipotent (sym2_transpose p.1 p.2 0)) hx
    exact ⟨⟨y, hy⟩, hyv⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro p p' hpp'
    have h := (hf p).symm.trans ((congrArg (fun y : P => M[(y : StatedSp 2 K)] *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) hpp').trans (hf p'))
    have h0 := congrFun h (Sum.inl 0)
    have h1 := congrFun h (Sum.inl 1)
    rw [tau_sym2_mulVec_inl_zero, tau_sym2_mulVec_inl_zero] at h0
    rw [tau_sym2_mulVec_inl_one, tau_sym2_mulVec_inl_one] at h1
    have hb : p.2 = p'.2 := mul_right_cancel₀ hne (add_left_cancel h1)
    have ha : p.1 = p'.1 := by
      rw [hb] at h0
      exact mul_right_cancel₀ hne (add_right_cancel (add_left_cancel h0))
    exact Prod.ext ha hb
  have hle := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, ← pow_two] at hle
  omega

theorem exists_le_stabilizer_flag [Finite K] {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hcard : Nat.card P < Nat.card K ^ 2) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ P ≤ stabilizer 2 K (flag 2 K d) := by
  set s : P → Fin 2 ⊕ Fin 2 → K := fun y =>
    M[(y : StatedSp 2 K)] *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with hs
  set W := span K (Set.range s) with hW
  have hiso : IsTotallyIsotropic (pairedSympForm K 2) W := by
    refine isTotallyIsotropic_span_range fun y z => ?_
    have h := pairedSympForm_mulVec ((y : StatedSp 2 K)⁻¹) (s y) (s z)
    simp only [hs] at h ⊢
    rw [← h, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, one_mulVec,
      pairedSympForm_single_inl]
    exact mulVec_e1_inr_zero hPU hcard (P.mul_mem (P.inv_mem y.2) z.2)
  have hmap : ∀ g : StatedSp 2 K, (∀ y : P, ∃ y' : P, s y' = M[g] *ᵥ s y) →
      ∀ v ∈ W, M[g] *ᵥ v ∈ W := by
    intro g hg v hv
    have hle : W ≤ W.comap (mulVecLin M[g]) := by
      rw [hW, span_le]
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', hy'⟩ := hg y
      change M[g] *ᵥ s y ∈ W
      rw [← hy']
      exact subset_span ⟨y', rfl⟩
    exact hle hv
  have hU : ∀ u ∈ unipotent 2 K, ∀ v ∈ W, M[u] *ᵥ v ∈ W := by
    intro u hu
    refine hmap u fun y => ?_
    obtain ⟨y', hy', h⟩ := exists_mulVec_e1 hPU hu y.2
    exact ⟨⟨y', hy'⟩, h⟩
  have hP : P ≤ stabilizer 2 K W := by
    intro g hg
    refine mem_stabilizer_of_mulVec_mem' (hmap g fun y => ⟨⟨g * y, P.mul_mem hg y.2⟩, ?_⟩)
    simp only [hs, Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]
  obtain ⟨d, hd, hWd⟩ :=
    ((unitriangular_invariant_isotropic_subspaces (r := 2) (K := K)).2.1 W).mp ⟨hiso, hU⟩
  have he1 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    have : s 1 = Pi.single (Sum.inl 0) 1 := by
      simp only [hs, OneMemClass.coe_one, Units.val_one, one_mulVec]
    rw [← this]
    exact subset_span ⟨1, rfl⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [hWd, mem_flag_of_le (by norm_num), mem_isoFlag] at he1
    simpa using he1.2 0 (by simp)
  exact ⟨d, by omega, hWd ▸ hP⟩

theorem isCyclic_of_isPGroup_GL_two [Finite K] {r : ℕ} [hr : Fact r.Prime]
    (hrQ : ¬ r ∣ Nat.card K) (hr1 : ¬ r ∣ Nat.card K - 1) {R : Subgroup (GL (Fin 2) K)}
    (hR : IsPGroup r R) : IsCyclic R := by
  have hr' := hr.out
  set Q := Nat.card K with hQ
  have hQ1 : 1 ≤ Q := Nat.card_pos
  obtain ⟨Z, hZ, hZcard⟩ := CFSG.SectionRank.OddCover.exists_isCyclic_card_GL K 2
  refine CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_card_eq_mul (Z := Z)
    (m := Q * (Q - 1)) ?_ (hr'.not_dvd_mul hrQ hr1) hR
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hZcard]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [← hQ]
  have e1 : Q ^ 2 - Q = Q * (Q - 1) := by
    zify [hQ1, Nat.le_self_pow (by norm_num : 2 ≠ 0) Q]
    ring
  rw [e1]

noncomputable def blockHom : stabilizer 2 K (flag 2 K 2) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := toBlocks₁₁ M[(g : StatedSp 2 K)]
  map_one' := by
    ext i j
    simp [toBlocks₁₁, one_apply]
  map_mul' g h := by
    ext i j
    simp only [toBlocks₁₁, of_apply, Subgroup.coe_mul, Units.val_mul, mul_apply,
      Fintype.sum_sum_type, mem_stabilizer_two_iff.mp h.2, mul_zero, Finset.sum_const_zero,
      add_zero]

theorem sq_eq_one_of_blockHom [CharP K 2] (g : stabilizer 2 K (flag 2 K 2))
    (hg : blockHom g = 1) : (g : StatedSp 2 K) ^ 2 = 1 := by
  set x := M[(g : StatedSp 2 K)] with hx
  have hsym := SymplecticTorusWeyl.mem_statedSp_iff.mp (g : StatedSp 2 K).2
  have h21 : toBlocks₂₁ x = 0 := by
    ext i j
    exact mem_stabilizer_two_iff.mp g.2 i j
  have hblk : x = fromBlocks 1 (toBlocks₁₂ x) 0 (toBlocks₂₂ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks x]
    rw [show toBlocks₁₁ x = 1 from hg, h21]
  have hD : toBlocks₂₂ x = 1 := by
    rw [← hx, hblk, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
      fromBlocks_inj] at hsym
    simpa using hsym.2.1
  apply SymplecticTorusWeyl.statedSp_ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, ← hx, Subgroup.coe_one, Units.val_one, hblk, hD,
    fromBlocks_multiply]
  simp [CharTwo.add_self_eq_zero, fromBlocks_one]

theorem false_of_le_stabilizer_two [Finite K] [CharP K 2] {P : Subgroup (StatedSp 2 K)}
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) (hP9 : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hq3 : ¬ 3 ∣ Nat.card K) (hq31 : ¬ 3 ∣ Nat.card K - 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := P.subgroupOf (stabilizer 2 K (flag 2 K 2))
  let ρ : Q →* GL (Fin 2) K := (blockHom (K := K)).toHomUnits.comp Q.subtype
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have h1 : blockHom (q : stabilizer 2 K (flag 2 K 2)) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hq)
      simpa [ρ] using this
    have h2 := sq_eq_one_of_blockHom (q : stabilizer 2 K (flag 2 K 2)) h1
    have h3 : ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) ^ 3 = 1 :=
      hexp _ (Subgroup.mem_subgroupOf.mp q.2)
    have hq1 : ((q : stabilizer 2 K (flag 2 K 2)) : StatedSp 2 K) = 1 := by
      rw [pow_succ, h2, one_mul] at h3
      exact h3
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext hq1)
  have hQ9 : Nat.card Q = 9 := by
    rw [← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv
  have hR9 : Nat.card ρ.range = 9 := by
    rw [← hQ9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hRexp : ∀ x ∈ ρ.range, x ^ 3 = 1 := by
    rintro _ ⟨q, rfl⟩
    rw [← map_pow]
    have : q ^ 3 = 1 := Subtype.ext (Subtype.ext (hexp _ (Subgroup.mem_subgroupOf.mp q.2)))
    rw [this, map_one]
  have hR3 : IsPGroup 3 ρ.range := IsPGroup.of_card (n := 2) (by rw [hR9]; norm_num)
  exact CFSG.Quasithin.F134.not_isCyclic_of_card_nine hR9 hRexp
    (isCyclic_of_isPGroup_GL_two hq3 hq31 hR3)

theorem lam_mulVec_of_mem_flag_two (a : K) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K 2) :
    M[lam a] *ᵥ v = fun i => Sum.elim ![v (Sum.inl 0) + a * v (Sum.inl 1), v (Sum.inl 1)]
      (fun _ => 0) i := by
  obtain ⟨h0, h1⟩ := mem_flag_two_iff.mp hv
  rw [coe_lam]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_two, unitri, h0, h1]

theorem le_stabilizer_one_of_le_stabilizer_two [Finite K] {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) (hP9 : Nat.card P ∣ 9)
    (hq : 3 ∣ Nat.card K - 1) : P ≤ stabilizer 2 K (flag 2 K 1) := by
  set e := (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with he
  have he0 : e ≠ 0 := single_inl_zero_ne_zero
  have heF : e ∈ flag 2 K 2 := by
    rw [mem_flag_two_iff]
    simp [he]
  suffices hfix : ∀ y ∈ P, M[y] *ᵥ e ∈ flag 2 K 1 by
    intro y hy
    refine mem_stabilizer_of_mulVec_mem' fun v hv => ?_
    rw [eq_smul_e1_of_mem_flag_one hv, mulVec_smul]
    exact Submodule.smul_mem _ _ (hfix y hy)
  by_contra hne
  obtain ⟨y₀, hy₀, hv₀⟩ := not_forall₂.mp hne
  set v := M[y₀] *ᵥ e with hv
  have hvF : v ∈ flag 2 K 2 := mulVec_mem_of_mem_stabilizer (hPF hy₀) heF
  obtain ⟨hv0, hv1⟩ := mem_flag_two_iff.mp hvF
  have hvl : v (Sum.inl 1) ≠ 0 := fun h => hv₀ (mem_flag_one_iff.mpr ⟨hv0, hv1, h⟩)
  set p₀ := SpPoint.ofVec e he0
  have hsmul : ∀ y : P, y • p₀ = SpPoint.ofVec (M[(y : StatedSp 2 K)] *ᵥ e)
      (fun h => he0 (spAct_injective (y : StatedSp 2 K) (h.trans (map_zero _).symm))) :=
    fun y => smul_ofVec (y : StatedSp 2 K) e he0
  have horbit : MulAction.orbit P p₀ = {M : SpPoint 2 K | M.line ≤ flag 2 K 2} := by
    ext Mp
    constructor
    · rintro ⟨y, rfl⟩
      change (y • p₀).line ≤ flag 2 K 2
      rw [hsmul y, line_ofVec, span_le, Set.singleton_subset_iff]
      exact mulVec_mem_of_mem_stabilizer (hPF y.2) heF
    · intro hM
      obtain ⟨w, hw, rfl⟩ := Mp.exists_ofVec
      have hwF : w ∈ flag 2 K 2 := by
        apply hM
        rw [line_ofVec]
        exact mem_span_singleton_self w
      obtain ⟨hw0, hw1⟩ := mem_flag_two_iff.mp hwF
      by_cases hwl : w (Sum.inl 1) = 0
      · have hw' : w = w (Sum.inl 0) • e := eq_smul_e1_of_mem_flag_one
          (mem_flag_one_iff.mpr ⟨hw0, hw1, hwl⟩)
        have hc : w (Sum.inl 0) ≠ 0 := fun h => hw (by rw [hw', h, zero_smul])
        refine ⟨1, ?_⟩
        change (1 : P) • p₀ = _
        rw [one_smul]
        exact (ofVec_smul_eq he0 hc (hw' ▸ hw)).symm.trans (by congr 1; exact hw'.symm)
      · set a := w (Sum.inl 0) / w (Sum.inl 1) - v (Sum.inl 0) / v (Sum.inl 1)
        obtain ⟨y, hy, hyv⟩ := exists_mulVec_e1 hPU (lam_mem_unipotent a) hy₀
        set c := v (Sum.inl 1) / w (Sum.inl 1)
        have hc : c ≠ 0 := div_ne_zero hvl hwl
        have hlam : M[lam a] *ᵥ v = c • w := by
          rw [lam_mulVec_of_mem_flag_two a hvF]
          ext i
          rcases i with i | i <;> fin_cases i <;> simp [c, a, hw0, hw1]
          · field_simp
            ring
          · field_simp
        refine ⟨⟨y, hy⟩, ?_⟩
        change (⟨y, hy⟩ : P) • p₀ = _
        rw [hsmul]
        have hcw : c • w ≠ 0 := smul_ne_zero hc hw
        refine (SpPoint.ext ?_).trans (ofVec_smul_eq hw hc hcw)
        rw [line_ofVec, line_ofVec]
        congr 1
        rw [Set.singleton_eq_singleton_iff]
        change M[y] *ᵥ e = c • w
        rw [hyv, ← hlam]
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hpts : Nat.card {M : SpPoint 2 K // M.line ≤ flag 2 K 2} = Nat.card K + 1 := by
    have h := card_pointsLe_mul (flag 2 K 2)
    rw [finrank_flag (by norm_num)] at h
    have h2 := Nat.sq_sub_sq (Nat.card K) 1
    rw [one_pow] at h2
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have hcardO : Nat.card (MulAction.orbit P p₀) = Nat.card K + 1 := by
    rw [horbit]
    exact hpts
  have hdvd : Nat.card (MulAction.orbit P p₀) ∣ Nat.card P := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  rw [hcardO] at hdvd
  have h9 := hdvd.trans hP9
  have hle := Nat.le_of_dvd (by norm_num) h9
  have hK8 : Nat.card K ≤ 8 := by omega
  obtain ⟨k, hk⟩ := h9
  interval_cases h : Nat.card K <;> omega

section Tau

variable [CharP K 2]

theorem tauSp_mem_stabilizer_two {g : StatedSp 2 K} (hg : g ∈ stabilizer 2 K (flag 2 K 1)) :
    tauSp g ∈ stabilizer 2 K (flag 2 K 2) := by
  obtain ⟨h0, h1, h2⟩ := mem_stabilizer_one_iff.mp hg
  rw [mem_stabilizer_two_iff]
  intro i j
  rw [coe_tauSp, tauMat_apply]
  fin_cases i <;> fin_cases j <;> simp [tauPair, h0, h1, h2]

theorem tauSp_mem_stabilizer_one {g : StatedSp 2 K} (hg : g ∈ stabilizer 2 K (flag 2 K 2)) :
    tauSp g ∈ stabilizer 2 K (flag 2 K 1) := by
  have h := mem_stabilizer_two_iff.mp hg
  rw [mem_stabilizer_one_iff]
  simp only [coe_tauSp, tauMat_apply]
  simp [tauPair, h]

variable [Finite K]

theorem map_tauEquiv_borelSubgroup :
    (borelSubgroup 2 K).map (tauEquiv (F := K)).toMonoidHom = borelSubgroup 2 K := by
  have hle : (borelSubgroup 2 K).map (tauEquiv (F := K)).toMonoidHom ≤ borelSubgroup 2 K := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := mem_borelSubgroup_iff.mp hg
    exact mem_borelSubgroup_iff.mpr ⟨tauSp_mem_stabilizer_one h2, tauSp_mem_stabilizer_two h1⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := (tauEquiv (F := K)).toMonoidHom)
    (tauEquiv (F := K)).injective]

theorem isSylowTwoOf_unipotent :
    CFSG.QuasithinUnique.IsSylowTwoOf (unipotent 2 K) (⊤ : Subgroup (StatedSp 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_unipotent (K := K) 2 2
  refine ⟨le_top, hS ▸ S.isPGroup', ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right, ← hS]
  exact S.not_dvd_index

theorem map_tauEquiv_unipotent :
    (unipotent 2 K).map (tauEquiv (F := K)).toMonoidHom = unipotent 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := isSylowTwoOf_unipotent (K := K)
  have hτU : IsPGroup 2 ((unipotent 2 K).map (tauEquiv (F := K)).toMonoidHom) :=
    hU.2.1.map _
  have hN : (unipotent 2 K).map (tauEquiv (F := K)).toMonoidHom ≤
      Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
    rw [normalizer_unipotent, ← map_tauEquiv_borelSubgroup]
    exact Subgroup.map_mono unipotent_le_borelSubgroup
  have hle := CFSG.Quasithin.P134.le_of_isSylowTwoOf hU le_sup_right le_top
    (hτU.to_sup_of_normal_right' hU.2.1 hN)
  refine Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hle) ?_
  rw [Subgroup.card_map_of_injective (f := (tauEquiv (F := K)).toMonoidHom)
    (tauEquiv (F := K)).injective]

end Tau

theorem le_borelSubgroup_of_le_stabilizer_two [Finite K] [CharP K 2]
    {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hP9 : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) (hq3 : ¬ 3 ∣ Nat.card K)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) : P ≤ borelSubgroup 2 K ∧ 3 ∣ Nat.card K - 1 := by
  have h3 : 3 ∣ Nat.card K - 1 := by
    by_contra h
    exact false_of_le_stabilizer_two hPF hP9 hexp hq3 h
  refine ⟨fun y hy => mem_borelSubgroup_iff.mpr ⟨?_, hPF hy⟩, h3⟩
  exact le_stabilizer_one_of_le_stabilizer_two hPU hPF (by rw [hP9]) h3 hy

theorem le_borelSubgroup_of_mul [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {P : Subgroup (StatedSp 2 K)}
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hP9 : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    P ≤ borelSubgroup 2 K ∧ 3 ∣ Nat.card K - 1 := by
  have hq3 : ¬ 3 ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    intro h
    have := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hcard : Nat.card P < Nat.card K ^ 2 := by
    rw [hP9]
    nlinarith
  obtain ⟨d, hd, hPd⟩ := exists_le_stabilizer_flag hPU hcard
  rcases hd with rfl | rfl
  ·
    set τ := (tauEquiv (F := K)).toMonoidHom with hτ
    have hτF : P.map τ ≤ stabilizer 2 K (flag 2 K 2) := by
      rintro _ ⟨y, hy, rfl⟩
      exact tauSp_mem_stabilizer_two (hPd hy)
    have hτ9 : Nat.card (P.map τ) = 9 := by
      rw [Subgroup.card_map_of_injective (f := τ) (tauEquiv (F := K)).injective, hP9]
    have hτexp : ∀ x ∈ P.map τ, x ^ 3 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hexp y hy, map_one]
    have hτU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P.map τ, ∃ y ∈ P.map τ, ∃ s ∈ unipotent 2 K,
        u * x = y * s := by
      intro u hu x hx
      rw [← map_tauEquiv_unipotent] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, s, hs, hzs⟩ := hPU u' hu' y hy
      refine ⟨τ z, ⟨z, hz, rfl⟩, τ s, ?_, by rw [← map_mul, hzs, map_mul]⟩
      rw [← map_tauEquiv_unipotent]
      exact ⟨s, hs, rfl⟩
    obtain ⟨hB, h3⟩ := le_borelSubgroup_of_le_stabilizer_two hτU hτ9 hτexp hq3 hτF
    refine ⟨fun y hy => ?_, h3⟩
    have hy' : τ y ∈ borelSubgroup 2 K := hB ⟨y, hy, rfl⟩
    rw [← map_tauEquiv_borelSubgroup] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    rwa [(tauEquiv (F := K)).injective hzy] at hz
  · exact le_borelSubgroup_of_le_stabilizer_two hPU hP9 hexp hq3 hPd

end CFSG.Quasithin.F134.Sp4
