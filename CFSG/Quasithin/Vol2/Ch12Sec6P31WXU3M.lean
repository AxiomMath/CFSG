module

public import CFSG.Quasithin.Background.Harris.AutBorel.U3Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Coord
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXBT
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXCS

public section

namespace CFSG.Quasithin.H13.P31X

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique CFSG.Open

variable {n : ℕ} {K : Type} [Field K]


theorem u3_hypBorel_eq (h : UnitaryFieldData 2 n K) :
    hypBorel h 1 1 = isoStabilizer h 1 1 (hypFlag h 1 1 1) := by
  ext g
  rw [mem_hypBorel, mem_isoStabilizer]
  constructor
  · intro hg
    exact hg 1 le_rfl le_rfl
  · intro hg i hi1 hir
    obtain rfl : i = 1 := le_antisymm hir hi1
    exact hg

theorem u3_card_hypBorel (h : UnitaryFieldData 2 n K) :
    Nat.card (hypBorel h 1 1) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  have hfinite := h.finite
  obtain ⟨hU, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hle := hypUnitriangular_le_hypBorel h (r := 1) (ε := 1)
  have h1 : Nat.card ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)) *
      ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)).index =
      Nat.card (hypBorel h 1 1) :=
    ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)).card_mul_index
  have h2 : Nat.card ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)) =
      Nat.card (hypUnitriangular h 1 1) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h3 : ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)).index =
      Nat.card (hypDiagHom h 1 1 le_rfl).range :=
    card_quotient_hypUnitriangular (h := h) (r := 1) le_rfl
  rw [range_hypDiagHom_odd (h := h) (r := 1) le_rfl, Subgroup.card_top, card_fun_units h 1] at h3
  rw [← h1, h2, hU, h3]
  norm_num

theorem u3_card_N_E (h : UnitaryFieldData 2 n K) :
    Nat.card (Subgroup.normalizer (hypUnitriangular h 1 1 : Set (hypSU h 1 1))) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  rw [normalizer_hypUnitriangular h le_rfl le_rfl]
  exact u3_card_hypBorel h

theorem u3_card_U_E (h : UnitaryFieldData 2 n K) :
    Nat.card (hypUnitriangular h 1 1) = (2 ^ n) ^ 3 := by
  rw [(unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl).1]

theorem u3_card_U_P (h : UnitaryFieldData 2 n K) :
    Nat.card (hypProjUnitriangular h 1 1) = (2 ^ n) ^ 3 := by
  obtain ⟨hU, -, -, ⟨e, he⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  rw [← Nat.card_congr e.toEquiv, hU]

theorem u3_card_N_P (h : UnitaryFieldData 2 n K) :
    Nat.card (Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1))) *
      Nat.gcd 3 (2 ^ n + 1) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  have hfinite := h.finite
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl, hypProjBorel]
  have hker : (hypProj h 1 1).ker ≤ hypBorel h 1 1 := by
    rw [ker_hypProj, u3_hypBorel_eq]
    exact hypScalars_le_isoStabilizer _
  have h1 := bt_card_map_mul_card_ker (hypProj h 1 1) hker
  rw [u3_card_hypBorel, show Nat.card (hypProj h 1 1).ker = Nat.gcd 3 (2 ^ n + 1) from ?_] at h1
  · exact h1
  · rw [ker_hypProj, card_hypScalars h (r := 1) (ε := 1) (by norm_num)]

theorem u3_cyc_E (h : UnitaryFieldData 2 n K) :
    ∃ g ∈ hypBorel h 1 1, ∀ b ∈ hypBorel h 1 1,
      ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ hypUnitriangular h 1 1 := by
  have hfinite := h.finite
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hsurj := range_hypDiagHom_odd (h := h) (r := 1) le_rfl
  obtain ⟨g₀, hg₀⟩ : (fun _ : Fin 1 => γ) ∈ (hypDiagHom h 1 1 le_rfl).range := by
    rw [hsurj]; exact Subgroup.mem_top _
  refine ⟨(g₀ : hypSU h 1 1), g₀.2, fun b hb => ?_⟩
  have hl : (hypDiagHom h 1 1 le_rfl ⟨b, hb⟩) 0 ∈ Submonoid.powers γ :=
    mem_powers_iff_mem_zpowers.mpr (hγ _)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ γ).mp hl
  refine ⟨k, ?_⟩
  have hker : (g₀ ^ k)⁻¹ * ⟨b, hb⟩ ∈ (hypDiagHom h 1 1 le_rfl).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hg₀]
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.one_apply]
    rw [Subsingleton.elim i 0, hk]
    simp
  rw [ker_hypDiagHom, Subgroup.mem_subgroupOf] at hker
  simpa using hker

theorem u3_isSylow_E (h : UnitaryFieldData 2 n K) : IsSylowTwoOf (hypUnitriangular h 1 1) ⊤ := by
  obtain ⟨-, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  rw [← hP]
  exact isSylowTwoOf_top_of_sylow P

theorem u3_isSylow_P (h : UnitaryFieldData 2 n K) :
    IsSylowTwoOf (hypProjUnitriangular h 1 1) ⊤ := by
  obtain ⟨-, -, -, -, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  rw [← hP]
  exact isSylowTwoOf_top_of_sylow P

theorem u3_coatom_E (h : UnitaryFieldData 2 n K) :
    IsCoatom (Subgroup.normalizer (hypUnitriangular h 1 1 : Set (hypSU h 1 1))) := by
  rw [normalizer_hypUnitriangular h le_rfl le_rfl, u3_hypBorel_eq]
  refine ⟨isoStabilizer_hypFlag_ne_top h le_rfl le_rfl le_rfl, fun A hA => ?_⟩
  rcases eq_of_isoStabilizer_hypFlag_le h le_rfl le_rfl le_rfl le_rfl A hA.le with he | he
  · exact absurd he hA.ne'
  · exact he

theorem u3_coatom_P (h : UnitaryFieldData 2 n K) :
    IsCoatom (Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1))) := by
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl, hypProjBorel, u3_hypBorel_eq]
  exact isCoatom_projIsoStabilizer_hypFlag h le_rfl le_rfl le_rfl le_rfl



theorem inv_diag_of_blockTriangular {X : GL (HypIndex 1 1) K}
    (hX : (X : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos) (a : HypIndex 1 1) :
    ((X⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a *
      (X : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a = 1 := by
  have h1 := mul_apply_self_of_blockTriangular fullPos_injective
    (blockTriangular_inv_fullPos hX) hX a
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq] at h1
  exact h1.symm

theorem comm_mem_fullUnitriangular {X Y : GL (HypIndex 1 1) K}
    (hX : (X : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos)
    (hY : (Y : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos) :
    X * Y * X⁻¹ * Y⁻¹ ∈ fullUnitriangular 1 1 K := by
  have hXi := blockTriangular_inv_fullPos hX
  have hYi := blockTriangular_inv_fullPos hY
  have hXY : (((X * Y : GL (HypIndex 1 1) K)) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
    rw [Units.val_mul]
    exact hX.mul hY
  have hXYX : (((X * Y * X⁻¹ : GL (HypIndex 1 1) K)) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
    rw [Units.val_mul]
    exact hXY.mul hXi
  refine ⟨by rw [Units.val_mul]; exact hXYX.mul hYi, fun a => ?_⟩
  rw [Units.val_mul, mul_apply_self_of_blockTriangular fullPos_injective hXYX hYi,
    Units.val_mul, mul_apply_self_of_blockTriangular fullPos_injective hXY hXi,
    Units.val_mul, mul_apply_self_of_blockTriangular fullPos_injective hX hY]
  have hx := inv_diag_of_blockTriangular hX a
  have hy := inv_diag_of_blockTriangular hY a
  have hx0 : (X : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a ≠ 0 :=
    right_ne_zero_of_mul_eq_one hx
  have hy0 : (Y : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a ≠ 0 :=
    right_ne_zero_of_mul_eq_one hy
  have hxi : ((X⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a =
      ((X : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a)⁻¹ := eq_inv_of_mul_eq_one_left hx
  have hyi : ((Y⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a =
      ((Y : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a)⁻¹ := eq_inv_of_mul_eq_one_left hy
  rw [hxi, hyi]
  field_simp

theorem glAut_mem_hypSU' (h : UnitaryFieldData 2 n K) (σ : K ≃+* K) (g : hypSU h 1 1) :
    glAut σ (g : GL (HypIndex 1 1) K) ∈ hypSU h 1 1 := by
  have hx : (SemidirectProduct.inr σ : SemiGL (HypIndex 1 1) K) ∈
      semilinearSimilitudes h 1 1 := ⟨1, one_ne_zero, map_one _, by simp⟩
  have := conj_mem_hypSU hx g
  simpa using this


theorem blockTriangular_glAut {σ : K ≃+* K} {g : GL (HypIndex 1 1) K}
    (hg : (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos) :
    ((glAut σ g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular
      fullPos := by
  intro i j hij
  rw [coe_glAut, Matrix.map_apply, hg hij, map_zero]

theorem u3_core (h : UnitaryFieldData 2 n K) {σ : K ≃+* K} {j : ℕ}
    (hσ : ∀ x : K, σ x = x ^ 2 ^ j) {B : GL (HypIndex 1 1) K}
    (hBt : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos)
    {b w : hypSU h 1 1} (hb : b ∈ hypBorel h 1 1)
    (hw : (w : GL (HypIndex 1 1) K) = B * glAut σ (b : GL (HypIndex 1 1) K) * B⁻¹) :
    w * (b ^ 2 ^ j)⁻¹ ∈ hypUnitriangular h 1 1 := by
  set y : hypSU h 1 1 := ⟨glAut σ (b : GL (HypIndex 1 1) K), glAut_mem_hypSU' h σ b⟩ with hy
  have hbt := blockTriangular_of_mem_hypBorel h le_rfl hb
  have hyt : ((y : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular
      fullPos := blockTriangular_glAut hbt
  have hyB : y ∈ hypBorel h 1 1 := mem_hypBorel_of_blockTriangular h hyt
  have h1 : w * y⁻¹ ∈ hypUnitriangular h 1 1 := by
    show (w * y⁻¹ : hypSU h 1 1) ∈ (fullUnitriangular 1 1 K).subgroupOf (hypSU h 1 1)
    rw [Subgroup.mem_subgroupOf]
    have : ((w * y⁻¹ : hypSU h 1 1) : GL (HypIndex 1 1) K) =
        B * glAut σ (b : GL (HypIndex 1 1) K) * B⁻¹ * (glAut σ (b : GL (HypIndex 1 1) K))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hw]
    rw [this]
    exact comm_mem_fullUnitriangular hBt hyt
  have h2 : y * (b ^ 2 ^ j)⁻¹ ∈ hypUnitriangular h 1 1 := by
    have hmemB : y * (b ^ 2 ^ j)⁻¹ ∈ hypBorel h 1 1 :=
      mul_mem hyB (inv_mem (pow_mem hb _))
    have hker : (⟨y * (b ^ 2 ^ j)⁻¹, hmemB⟩ : hypBorel h 1 1) ∈ (hypDiagHom h 1 1 le_rfl).ker := by
      have hdecomp : (⟨y * (b ^ 2 ^ j)⁻¹, hmemB⟩ : hypBorel h 1 1) =
          ⟨y, hyB⟩ * (⟨b, hb⟩ ^ 2 ^ j)⁻¹ := rfl
      rw [MonoidHom.mem_ker, hdecomp, map_mul, map_inv, map_pow]
      have hd : hypDiagHom h 1 1 le_rfl ⟨y, hyB⟩ = hypDiagHom h 1 1 le_rfl ⟨b, hb⟩ ^ 2 ^ j := by
        funext i
        apply Units.ext
        rw [coe_hypDiagHom, Pi.pow_apply, Units.val_pow_eq_pow_val, coe_hypDiagHom]
        show ((glAut σ (b : GL (HypIndex 1 1) K) : GL (HypIndex 1 1) K) :
            Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl i) (.inl i) =
          (((b : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl i) (.inl i)) ^
            2 ^ j
        rw [coe_glAut, Matrix.map_apply, hσ]
      rw [hd, mul_inv_cancel]
    rw [ker_hypDiagHom, Subgroup.mem_subgroupOf] at hker
    exact hker
  have := mul_mem h1 h2
  simpa [mul_assoc] using this


theorem u3_ringEquiv_pow [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ j : ℕ, ∀ x : K, σ x = x ^ 2 ^ j := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ x : ZMod 2, σ (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod 2) K))
      (algebraMap (ZMod 2) K)) x
  let f : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv hcomm
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 f
  refine ⟨n, fun x => ?_⟩
  have h1 : ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (n : ℕ)) x = f x :=
    DFunLike.congr_fun hn x
  have h2 : ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (n : ℕ)) x =
      x ^ 2 ^ (n : ℕ) := by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  exact (h2.symm.trans h1).symm

open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.Quasithin.Background.Harris.AutBorel in
theorem u3_aut_data (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (α : MulAut (hypPSU h 1 1))
    (hα : (hypProjUnitriangular h 1 1).map α.toMonoidHom = hypProjUnitriangular h 1 1) :
    ∃ (σ : K ≃+* K) (j : ℕ) (B : GL (HypIndex 1 1) K), (∀ x : K, σ x = x ^ 2 ^ j) ∧
      (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos ∧
      ∀ g : hypSU h 1 1, ∃ hg : B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹ ∈ hypSU h 1 1,
        α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩ := by
  have hfin := h.finite
  have hchar : CharP K 2 := h.charP
  have hq : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨σ, B, hB, hα'⟩ := exists_isometry_hypPSU h hq α
  obtain ⟨c, hc0, hBe⟩ := exists_smul_eOne h hα hα'
  have hcol : ∀ i : HypIndex 1 1, (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) i (.inl 0) =
      (c • eOne K) i := by
    intro i
    rw [← hBe]
    simp [eOne, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.single_apply]
  have hwe : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inl 0) = 0 := by
    rw [hcol]; simp [eOne]
  have hfe : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inl 0) = 0 := by
    rw [hcol]; simp [eOne]
  have hee : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) = c := by
    rw [hcol]; simp [eOne]
  have hfw : (B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
    have h1 := congrFun (congrFun hB (.inl 0)) (.inr (.inl 0))
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hwe, hfe, hee] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (by simpa using hc0)
    · exact h1
  obtain ⟨j, hj⟩ := u3_ringEquiv_pow σ
  exact ⟨σ, j, B, hj, CFSG.GH74.GLS.Stage2.Bender.Thm1.u3_blockTriangular_of_hyp3 hwe hfe hfw, hα'⟩


theorem mem_center_iff_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    g ∈ Subgroup.center G ↔ e g ∈ Subgroup.center H := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro hg k
    have := congrArg e (hg (e.symm k))
    simpa using this
  · intro hg k
    apply e.injective
    simpa using hg (e k)

theorem u3_hypScalars_eq_center (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) :
    hypScalars h 1 1 = Subgroup.center (hypSU h 1 1) := by
  have hfin := h.finite
  have hF : Nat.card K = (2 ^ n) ^ 2 := h.card_eq_sq
  have hq : (3, 2 ^ n) ≠ (3, 2) := by
    intro h32
    have h1 : 2 ^ n = 2 := (Prod.mk.inj h32).2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨-, hcenter⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K) (p := 2) (f := n) (n := 3) hF le_rfl hq
  have hZ : unitaryScalars h 3 = Subgroup.center (StatedSU 3 (2 ^ n) K) :=
    (unitaryScalars_eq h (by norm_num)).trans hcenter.symm
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e : hypSU h 1 1 ≃* ↥(StatedSU 3 (2 ^ n) K) := hypTransport h hR
  ext z
  rw [mem_hypScalars_iff_transport hR z, mem_center_iff_of_mulEquiv' e z]
  have hiff : e z ∈ unitaryScalars h 3 ↔ e z ∈ Subgroup.center (StatedSU 3 (2 ^ n) K) := by
    rw [hZ]
  exact hiff


theorem u3_isPerfect_hypSU (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) :
    Group.IsPerfect (hypSU h 1 1) := by
  have hfin := h.finite
  have hF : Nat.card K = (2 ^ n) ^ 2 := h.card_eq_sq
  have hq : (3, 2 ^ n) ≠ (3, 2) := by
    intro h32
    have h1 : 2 ^ n = 2 := (Prod.mk.inj h32).2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) (p := 2) (f := n)
    (n := 3) hF le_rfl hq
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e : hypSU h 1 1 ≃* ↥(StatedSU 3 (2 ^ n) K) := hypTransport h hR
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem u3_aut_P (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (α : MulAut (hypPSU h 1 1))
    (hα : (hypProjUnitriangular h 1 1).map α.toMonoidHom = hypProjUnitriangular h 1 1) :
    ∃ j : ℕ, ∀ b ∈ Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1)),
      α b * (b ^ 2 ^ j)⁻¹ ∈ hypProjUnitriangular h 1 1 := by
  obtain ⟨σ, j, B, hj, hBt, hα'⟩ := u3_aut_data h hn α hα
  refine ⟨j, fun b hb => ?_⟩
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  obtain ⟨hg, hαb⟩ := hα' b₀
  have hc := u3_core h hj hBt hb₀ (w := ⟨_, hg⟩) rfl
  rw [hαb]
  exact ⟨_, hc, by simp [map_mul, map_inv, map_pow]⟩

theorem u3_aut_E (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (α : MulAut (hypSU h 1 1))
    (hα : (hypUnitriangular h 1 1).map α.toMonoidHom = hypUnitriangular h 1 1) :
    ∃ j : ℕ, ∀ b ∈ Subgroup.normalizer (hypUnitriangular h 1 1 : Set (hypSU h 1 1)),
      α b * (b ^ 2 ^ j)⁻¹ ∈ hypUnitriangular h 1 1 := by
  haveI := u3_isPerfect_hypSU h hn
  have hZ := u3_hypScalars_eq_center h hn
  have hmap : (hypScalars h 1 1).map α.toMonoidHom = hypScalars h 1 1 := by
    rw [hZ]
    exact Subgroup.map_center_eq α
  let β : MulAut (hypPSU h 1 1) := QuotientGroup.congr (hypScalars h 1 1) (hypScalars h 1 1) α hmap
  have hβ : ∀ g, β (hypProj h 1 1 g) = hypProj h 1 1 (α g) := fun g => rfl
  have hβU : (hypProjUnitriangular h 1 1).map β.toMonoidHom = hypProjUnitriangular h 1 1 := by
    rw [hypProjUnitriangular, Subgroup.map_map]
    have hcomp : β.toMonoidHom.comp (hypProj h 1 1) = (hypProj h 1 1).comp α.toMonoidHom := by
      ext g
      rfl
    rw [hcomp, ← Subgroup.map_map, hα]
  obtain ⟨σ, j, B, hj, hBt, hα'⟩ := u3_aut_data h hn β hβU
  let φ₂ : hypSU h 1 1 →* hypSU h 1 1 :=
    { toFun := fun g => ⟨B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹, (hα' g).1⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g g' => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
        group }
  have hφ : α.toMonoidHom = φ₂ := by
    apply bt_eq_of_inv_mul_mem_center
    intro g
    obtain ⟨hg, hβg⟩ := hα' g
    rw [← hZ, ← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv]
    have hp : hypProj h 1 1 (α g) = hypProj h 1 1 (φ₂ g) := by
      rw [← hβ, hβg]
      rfl
    change (hypProj h 1 1 (α g))⁻¹ * hypProj h 1 1 (φ₂ g) = 1
    rw [hp, inv_mul_cancel]
  refine ⟨j, fun b hb => ?_⟩
  rw [normalizer_hypUnitriangular h le_rfl le_rfl] at hb
  have hw : ((α b : hypSU h 1 1) : GL (HypIndex 1 1) K) =
      B * glAut σ (b : GL (HypIndex 1 1) K) * B⁻¹ := by
    have := DFunLike.congr_fun hφ b
    exact congrArg Subtype.val this
  exact u3_core h hj hBt hb hw


theorem u3_cyc_N_E (h : UnitaryFieldData 2 n K) :
    ∃ c ∈ Subgroup.normalizer (hypUnitriangular h 1 1 : Set (hypSU h 1 1)),
      ∀ b ∈ Subgroup.normalizer (hypUnitriangular h 1 1 : Set (hypSU h 1 1)),
        ∃ k : ℕ, (c ^ k)⁻¹ * b ∈ hypUnitriangular h 1 1 := by
  rw [normalizer_hypUnitriangular h le_rfl le_rfl]
  exact u3_cyc_E h

theorem u3_cyc_N_P (h : UnitaryFieldData 2 n K) :
    ∃ c ∈ Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1)),
      ∀ b ∈ Subgroup.normalizer (hypProjUnitriangular h 1 1 : Set (hypPSU h 1 1)),
        ∃ k : ℕ, (c ^ k)⁻¹ * b ∈ hypProjUnitriangular h 1 1 := by
  rw [normalizer_hypProjUnitriangular h le_rfl le_rfl]
  obtain ⟨g₀, hg₀, hcyc⟩ := u3_cyc_E h
  refine ⟨hypProj h 1 1 g₀, ⟨g₀, hg₀, rfl⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨k, hk⟩ := hcyc b hb
  exact ⟨k, ⟨_, hk, by simp⟩⟩

end CFSG.Quasithin.H13.P31X
