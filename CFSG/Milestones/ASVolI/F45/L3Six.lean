module

public import CFSG.Milestones.ASVolI.F45.L3
public import CFSG.Milestones.ASVolI.F45.Six
public import CFSG.Milestones.ASVolI.F4Native
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F45.L3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Flag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F431.F45.PgGeom

variable {K : Type} [Field K]

theorem burnsideF45_exists_line_param {L : Ln K} (hL : inc (p0 : Pt K) L) (hne : L ≠ l0) :
    ∃ a : K, (![0, a, 1] : V3 K) ∈ L.1 := by
  obtain ⟨s, t, hd, hv⟩ := exists_dir_line hL
  by_cases ht : t = 0
  · exfalso
    subst ht
    have hd' : s ≠ 0 ∨ (0 : K) ≠ 0 := hd
    have hpt : (p0 : Pt K) ≠ mkPt (PgGeom.vec s 0) (vec_ne_zero hd') := by
      intro h
      exact not_mem_p0_vec hd' (by rw [h]; exact mem_mkPt _)
    exact hne (two_pts (p0 : Pt K) (mkPt (PgGeom.vec s 0) (vec_ne_zero hd')) L l0 hL
      (inc_mkPt_iff.mpr hv) inc_p0_l0
      (inc_mkPt_iff.mpr ((mem_l0 _).mpr (by simp [PgGeom.vec]))) hpt)
  · refine ⟨s / t, ?_⟩
    have h : (![0, s / t, 1] : V3 K) = t⁻¹ • PgGeom.vec s t := by
      ext i
      fin_cases i <;> simp [PgGeom.vec, div_eq_inv_mul, ht]
    rw [h]
    exact L.1.smul_mem _ hv

theorem burnsideF45_exists_pt_param {P : Pt K} (hP : inc P (l0 : Ln K)) (hne : P ≠ p0) :
    ∃ a : K, (![a, 1, 0] : V3 K) ∈ P.1 := by
  obtain ⟨s, t, hd, hv⟩ := exists_dir_pt hP
  by_cases ht : t = 0
  · exfalso
    subst ht
    have hs : s ≠ 0 := hd.resolve_right fun h => h rfl
    have hu0 : (PgGeom.vec' s 0 : V3 K) ≠ 0 := by
      intro h
      exact hs (by simpa [PgGeom.vec'] using congrFun h 0)
    have hu : (PgGeom.vec' s 0 : V3 K) ∈ (p0 : Pt K).1 :=
      (mem_p0 _).mpr ⟨by simp [PgGeom.vec'], by simp [PgGeom.vec']⟩
    exact hne (Subtype.ext (hv.trans (pt_eq_span_of_mem hu hu0).symm))
  · refine ⟨s / t, ?_⟩
    have h : (![s / t, 1, 0] : V3 K) = t⁻¹ • PgGeom.vec' s t := by
      ext i
      fin_cases i <;> simp [PgGeom.vec', div_eq_inv_mul, ht]
    rw [h, hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem burnsideF45_mulVec_y (b : K) (v : V3 K) :
    ((yMat b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ![v 0, v 1 + b * v 2, v 2] := by
  show yM b *ᵥ v = _
  ext i
  fin_cases i <;> simp [yM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideF45_mulVec_x (b : K) (v : V3 K) :
    ((xMat b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ![v 0 + b * v 1, v 1, v 2] := by
  show xM b *ᵥ v = _
  ext i
  fin_cases i <;> simp [xM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideF45_line_eq {L : Ln K} {a : K} (hL : inc (p0 : Pt K) L)
    (h : (![0, a, 1] : V3 K) ∈ L.1) :
    L.1 = Submodule.span K {(ev 0 : V3 K)} ⊔ Submodule.span K {(![0, a, 1] : V3 K)} := by
  refine line_eq_span_pair (inc_p0_iff.mp hL) h (ev_ne_zero 0) (fun h0 => ?_) fun c hc => ?_
  · simpa using congrFun h0 2
  · have := congrFun hc 2
    simp [ev_apply] at this

theorem burnsideF45_yP_smul_line {L L' : Ln K} {a a' : K} (hL : inc (p0 : Pt K) L)
    (hL' : inc (p0 : Pt K) L') (h : (![0, a, 1] : V3 K) ∈ L.1)
    (h' : (![0, a', 1] : V3 K) ∈ L'.1) : yP (a' - a) • L = L' := by
  show LinearFlag.proj 3 K (yMat (a' - a)) • L = L'
  refine proj_smul_eq_of_gens (yMat (a' - a)) L L' (burnsideF45_line_eq hL h) ?_ ?_
  · have he : ((yMat (a' - a) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (ev 0 : V3 K) = ev 0 := by
      rw [burnsideF45_mulVec_y]
      ext i
      fin_cases i <;> simp [ev_apply]
    rw [he]
    exact inc_p0_iff.mp hL'
  · have he : ((yMat (a' - a) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (![0, a, 1] : V3 K) = ![0, a', 1] := by
      rw [burnsideF45_mulVec_y]
      ext i
      fin_cases i <;> simp
    rw [he]
    exact h'

theorem burnsideF45_xP_smul_pt {P P' : Pt K} {a a' : K} (h : (![a, 1, 0] : V3 K) ∈ P.1)
    (h' : (![a', 1, 0] : V3 K) ∈ P'.1) : xP (a' - a) • P = P' := by
  show LinearFlag.proj 3 K (xMat (a' - a)) • P = P'
  refine proj_smul_pt_eq h (fun h0 => ?_) ?_
  · simpa using congrFun h0 1
  · have he : ((xMat (a' - a) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (![a, 1, 0] : V3 K) = ![a', 1, 0] := by
      rw [burnsideF45_mulVec_x]
      ext i
      fin_cases i <;> simp
    rw [he]
    exact h'

theorem burnsideF45_mem_V1_of_fix_line {u : LinearFlag.projectiveSL 3 K}
    (hu : u ∈ LinearFlag.projUnitriangular 3 K) {L : Ln K} {a : K} (hL : inc (p0 : Pt K) L)
    (h : (![0, a, 1] : V3 K) ∈ L.1) (hfix : u • L = L) : u ∈ burnsideF45_V1 K := by
  obtain ⟨A, hA, rfl⟩ := hu
  obtain ⟨hl, hd⟩ := LinearFlag.mem_unitriangular.mp hA
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h10 := hl 1 0 (by decide)
  have h20 := hl 2 0 (by decide)
  have h21 := hl 2 1 (by decide)
  have hL1 : slMap A L.1 = L.1 := congrArg Subtype.val hfix
  have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (![0, a, 1] : V3 K) ∈ L.1 := by
    rw [← hL1]
    exact mem_slMap.mpr ⟨_, h, rfl⟩
  rw [burnsideF45_line_eq hL h] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have e1 := congrFun hyz 1
  have e2 := congrFun hyz 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ev_apply, h11, h21, h22] at e1 e2
  subst e2
  have h12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by linear_combination -e1
  exact ⟨A, burnsideF45_mem_elation_one.mpr ⟨_, _, burnsideF45_eq_q1_of_entries h00 h10 h20 h11
    h12 h21 h22⟩, rfl⟩

theorem burnsideF45_mem_V2_of_fix_pt {u : LinearFlag.projectiveSL 3 K}
    (hu : u ∈ LinearFlag.projUnitriangular 3 K) {P : Pt K} {a : K}
    (h : (![a, 1, 0] : V3 K) ∈ P.1) (hfix : u • P = P) : u ∈ burnsideF45_V2 K := by
  obtain ⟨A, hA, rfl⟩ := hu
  obtain ⟨hl, hd⟩ := LinearFlag.mem_unitriangular.mp hA
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h10 := hl 1 0 (by decide)
  have h20 := hl 2 0 (by decide)
  have h21 := hl 2 1 (by decide)
  have hP1 : slMap A P.1 = P.1 := congrArg Subtype.val hfix
  have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (![a, 1, 0] : V3 K) ∈ P.1 := by
    rw [← hP1]
    exact mem_slMap.mpr ⟨_, h, rfl⟩
  have hu0 : (![a, 1, 0] : V3 K) ≠ 0 := fun h0 => by simpa using congrFun h0 1
  rw [pt_eq_span_of_mem h hu0] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h10, h11] at e0 e1
  subst e1
  have h01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by linear_combination -e0
  exact ⟨A, burnsideF45_mem_elation_two.mpr ⟨_, _, burnsideF45_eq_q2_of_entries h00 h01 h10 h11
    h20 h21 h22⟩, rfl⟩

end Flag

section Borel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.F45.PgGeom

variable {K : Type} [Field K]

theorem burnsideF45_U_le_flag :
    LinearFlag.projUnitriangular 3 K ≤
      MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inl (p0 : Pt K) : Pt K ⊕ Ln K) ⊓
        MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inr (l0 : Ln K) : Pt K ⊕ Ln K) := by
  rw [burnsideF45_stabilizer_inl_p0, burnsideF45_stabilizer_inr_l0]
  exact le_inf
    (Subgroup.map_mono ((LinearFlag.unitriangular_le_upperTriangular 3 K).trans
      (LinearFlag.upperTriangular_le_stabilizer_flagSpace 1)))
    (Subgroup.map_mono ((LinearFlag.unitriangular_le_upperTriangular 3 K).trans
      (LinearFlag.upperTriangular_le_stabilizer_flagSpace 2)))

theorem burnsideF45_flag_le_normalizer :
    MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inl (p0 : Pt K) : Pt K ⊕ Ln K) ⊓
        MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inr (l0 : Ln K) : Pt K ⊕ Ln K) ≤
      Subgroup.normalizer
        ((LinearFlag.projUnitriangular 3 K : Subgroup (LinearFlag.projectiveSL 3 K)) :
          Set (LinearFlag.projectiveSL 3 K)) := by
  rw [burnsideF45_stabilizer_inl_p0, burnsideF45_stabilizer_inr_l0,
    ← burnsideF4h_cl_map_inf_of_ker_le _
      (by rw [LinearFlag.ker_proj]; exact LinearFlag.scalars_le_stabilizer _),
    burnsideF4h_cl_sl_stab_inf, ← LinearFlag.normalizer_unitriangular]
  exact Subgroup.le_normalizer_map _

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem burnsideF45_oPPrime_flag :
    oPPrime p (MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inl (p0 : Pt K) :
        Pt K ⊕ Ln K) ⊓
      MulAction.stabilizer (LinearFlag.projectiveSL 3 K) (Sum.inr (l0 : Ln K) : Pt K ⊕ Ln K)) =
      LinearFlag.projUnitriangular 3 K := by
  obtain ⟨S, hS⟩ := LinearFlag.exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  have hUp : IsPGroup p (LinearFlag.projUnitriangular 3 K) := hS ▸ S.isPGroup'
  apply le_antisymm
  · unfold oPPrime
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, k, hk⟩
    have hz : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hxN : x ∈ Subgroup.normalizer ((S : Subgroup (LinearFlag.projectiveSL 3 K)) :
        Set (LinearFlag.projectiveSL 3 K)) := by
      rw [hS]
      exact burnsideF45_flag_le_normalizer hx
    have hmem := (hz.inf_normalizer_sylow S).le ⟨Subgroup.mem_zpowers x, hxN⟩
    rw [← hS]
    exact hmem.2
  · intro u hu
    obtain ⟨n, hn⟩ := hUp ⟨u, hu⟩
    have hn' : u ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hn')
    exact Subgroup.subset_closure ⟨burnsideF45_U_le_flag hu, j, hj⟩

end Borel

section Main

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.F45.PgGeom

theorem burnsideF45_C6_L3 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hGp : Gp = ⊤) :
    ∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v := by
  obtain ⟨chart, hbor, hpts, hlines⟩ := hyp.lie_amalgam
  obtain ⟨marking, h1, h2, h3, -⟩ := burnsideF4f_L3_marking chart
  have hp : p.Prime := marking.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hm : 3 ≤ GLKind.L3.m := burnsideF45_three_le_m .L3
  haveI : Finite marking.field := marking.finiteField
  have hK : Nat.card marking.field = p ^ f := by simpa using marking.field_card
  haveI : CharP marking.field p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      marking.exponent_pos hK
  have hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
    have hmap := burnsideF4h_isLieParabolics_map Gp.subtype Gp.subtype_injective
      (burnsideF4h_cl_L3 p f ↥Gp marking)
    rw [burnsideF4h_map_subtype_top] at hmap
    rw [hbor, hpts, hlines, h1, h2, h3]
    exact hmap
  have hsub : ∀ (M : Subgroup E) (b : Bool), Gp ⊓ M = (marking.parabolic b).map Gp.subtype →
      ∀ y, ((burnsideF45_theta marking y : ↥Gp) : E) ∈ M ↔
        burnsideF45_theta marking y ∈ marking.parabolic b := by
    intro M b hM y
    constructor
    · intro hy
      have hmem : ((burnsideF45_theta marking y : ↥Gp) : E) ∈ Gp ⊓ M :=
        ⟨(burnsideF45_theta marking y).2, hy⟩
      rw [hM] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      rwa [Subtype.ext hzy] at hz
    · intro hy
      have hmem : ((burnsideF45_theta marking y : ↥Gp) : E) ∈ Gp ⊓ M := by
        rw [hM]
        exact ⟨_, hy, rfl⟩
      exact hmem.2
  have hstab1 : ∀ y, ((burnsideF45_theta marking y : ↥Gp) : E) ∈ M₁ ↔
      y • (Sum.inl (p0 : Pt marking.field) : Pt marking.field ⊕ Ln marking.field) =
        Sum.inl p0 := by
    intro y
    rw [hsub M₁ false (hpts.trans h2) y, burnsideF45_theta_mem_parabolic,
      ← MulAction.mem_stabilizer_iff, burnsideF45_stabilizer_inl_p0]
    exact Iff.rfl
  have hstab2 : ∀ y, ((burnsideF45_theta marking y : ↥Gp) : E) ∈ M₂ ↔
      y • (Sum.inr (l0 : Ln marking.field) : Pt marking.field ⊕ Ln marking.field) =
        Sum.inr l0 := by
    intro y
    rw [hsub M₂ true (hlines.trans h3) y, burnsideF45_theta_mem_parabolic,
      ← MulAction.mem_stabilizer_iff, burnsideF45_stabilizer_inr_l0]
    exact Iff.rfl
  have hc₁ : ∀ w₁ w₂ : Pt marking.field ⊕ Ln marking.field,
      (Gr marking.field).Adj (Sum.inl p0) w₁ → w₁ ≠ Sum.inr l0 →
      (Gr marking.field).Adj (Sum.inl p0) w₂ → w₂ ≠ Sum.inr l0 →
      ∃ y ∈ oPPrime p (MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
          (Sum.inl (p0 : Pt marking.field) : Pt marking.field ⊕ Ln marking.field) ⊓
        MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
          (Sum.inr (l0 : Ln marking.field) : Pt marking.field ⊕ Ln marking.field)),
        y • w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₁' hw₂ hw₂'
    obtain ⟨L₁, rfl, hL₁⟩ := incGraph_adj_inl hw₁
    obtain ⟨L₂, rfl, hL₂⟩ := incGraph_adj_inl hw₂
    obtain ⟨a₁, ha₁⟩ := burnsideF45_exists_line_param hL₁ fun h => hw₁' (by rw [h])
    obtain ⟨a₂, ha₂⟩ := burnsideF45_exists_line_param hL₂ fun h => hw₂' (by rw [h])
    refine ⟨yP (a₂ - a₁), ?_, ?_⟩
    · rw [burnsideF45_oPPrime_flag]
      exact ⟨yMat (a₂ - a₁), LinearCover.yMat_mem_unitriangular _, rfl⟩
    · rw [Sum.smul_inr, burnsideF45_yP_smul_line hL₁ hL₂ ha₁ ha₂]
  have hd₁ : ∀ y ∈ oPPrime p (MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
        (Sum.inl (p0 : Pt marking.field) : Pt marking.field ⊕ Ln marking.field) ⊓
      MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
        (Sum.inr (l0 : Ln marking.field) : Pt marking.field ⊕ Ln marking.field)),
      ∀ w : Pt marking.field ⊕ Ln marking.field, (Gr marking.field).Adj (Sum.inl p0) w →
        w ≠ Sum.inr l0 → y • w = w →
        y ∈ pCoreOf p (MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
          (Sum.inl (p0 : Pt marking.field) : Pt marking.field ⊕ Ln marking.field)) := by
    intro y hy w hw hw' hyw
    rw [burnsideF45_oPPrime_flag] at hy
    obtain ⟨L, rfl, hL⟩ := incGraph_adj_inl hw
    obtain ⟨a, ha⟩ := burnsideF45_exists_line_param hL fun h => hw' (by rw [h])
    rw [Sum.smul_inr] at hyw
    rw [burnsideF45_stabilizer_inl_p0, burnsideF45_pCoreOf_stab_one]
    exact burnsideF45_mem_V1_of_fix_line hy hL ha (Sum.inr.inj hyw)
  have hc₂ : ∀ w₁ w₂ : Pt marking.field ⊕ Ln marking.field,
      (Gr marking.field).Adj (Sum.inr l0) w₁ → w₁ ≠ Sum.inl p0 →
      (Gr marking.field).Adj (Sum.inr l0) w₂ → w₂ ≠ Sum.inl p0 →
      ∃ y ∈ oPPrime p (MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
          (Sum.inr (l0 : Ln marking.field) : Pt marking.field ⊕ Ln marking.field) ⊓
        MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
          (Sum.inl (p0 : Pt marking.field) : Pt marking.field ⊕ Ln marking.field)),
        y • w₁ = w₂ := by
    intro w₁ w₂ hw₁ hw₁' hw₂ hw₂'
    obtain ⟨P₁, rfl, hP₁⟩ := incGraph_adj_inr hw₁
    obtain ⟨P₂, rfl, hP₂⟩ := incGraph_adj_inr hw₂
    obtain ⟨a₁, ha₁⟩ := burnsideF45_exists_pt_param hP₁ fun h => hw₁' (by rw [h])
    obtain ⟨a₂, ha₂⟩ := burnsideF45_exists_pt_param hP₂ fun h => hw₂' (by rw [h])
    refine ⟨xP (a₂ - a₁), ?_, ?_⟩
    · rw [inf_comm, burnsideF45_oPPrime_flag]
      exact ⟨xMat (a₂ - a₁), LinearCover.xMat_mem_unitriangular _, rfl⟩
    · rw [Sum.smul_inl, burnsideF45_xP_smul_pt ha₁ ha₂]
  have hd₂ : ∀ y ∈ oPPrime p (MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
        (Sum.inr (l0 : Ln marking.field) : Pt marking.field ⊕ Ln marking.field) ⊓
      MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
        (Sum.inl (p0 : Pt marking.field) : Pt marking.field ⊕ Ln marking.field)),
      ∀ w : Pt marking.field ⊕ Ln marking.field, (Gr marking.field).Adj (Sum.inr l0) w →
        w ≠ Sum.inl p0 → y • w = w →
        y ∈ pCoreOf p (MulAction.stabilizer (LinearFlag.projectiveSL 3 marking.field)
          (Sum.inr (l0 : Ln marking.field) : Pt marking.field ⊕ Ln marking.field)) := by
    intro y hy w hw hw' hyw
    rw [inf_comm, burnsideF45_oPPrime_flag] at hy
    obtain ⟨P, rfl, hP⟩ := incGraph_adj_inr hw
    obtain ⟨a, ha⟩ := burnsideF45_exists_pt_param hP fun h => hw' (by rw [h])
    rw [Sum.smul_inl] at hyw
    rw [burnsideF45_stabilizer_inr_l0, burnsideF45_pCoreOf_stab_two]
    exact burnsideF45_mem_V2_of_fix_pt hy ha (Sum.inl.inj hyw)
  obtain ⟨hx, hl⟩ := burnsideF45_C6cd_base_of_model hyp hp hm hGp (burnsideF45_theta marking)
    (v₁ := Sum.inl (p0 : Pt marking.field)) (v₂ := Sum.inr (l0 : Ln marking.field))
    hstab1 hstab2
    (fun y z => by
      rw [Sum.smul_inl, Sum.smul_inr]
      exact Sum.inl_ne_inr)
    (fun y z => by
      rw [Sum.smul_inl, Sum.smul_inl]
      exact fun h => h)
    (fun y z => by
      rw [Sum.smul_inr, Sum.smul_inr]
      exact fun h => h)
    (incGraph_adj_inl_inr.mpr inc_p0_l0) isGenPolygon_gr three_p0 three_l0
    (by
      rw [burnsideF45_stabilizer_inl_p0, burnsideF45_pCoreOf_stab_one]
      exact burnsideF45_modelBase_p0)
    (by
      rw [burnsideF45_stabilizer_inr_l0, burnsideF45_pCoreOf_stab_two]
      exact burnsideF45_modelBase_l0)
    hc₁ hd₁ hc₂ hd₂
  exact fun u v huv => burnsideF45_C6_of_base hyp hp hm hP hx hl huv

end Main

end CFSG.ASVolI
