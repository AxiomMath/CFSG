module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4312Lev

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436 Vol2.KGNat
open scoped MatrixGroups commutatorElement Matrix

namespace SL3Pt

variable {F : Type} [Field F]

theorem exists_stabE0_mulVec_e1 {v : Fin 3 → F} (hv : v 1 ≠ 0 ∨ v 2 ≠ 0) :
    ∃ B ∈ stabE0 F, (B : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = v := by
  by_cases h1 : v 1 = 0
  · have h2 : v 2 ≠ 0 := hv.resolve_left (not_not.mpr h1)
    refine ⟨⟨!![1, v 0, 0; 0, 0, -(v 2)⁻¹; 0, v 2, 0], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h2]
    · refine mem_stabE0.mpr ?_
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1]
  · refine ⟨⟨!![1, v 0, 0; 0, v 1, 0; 0, v 2, (v 1)⁻¹], ?_⟩, ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h1]
    · refine mem_stabE0.mpr ?_
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem stabE0_trans {v w : Fin 3 → F} (hv : v 1 ≠ 0 ∨ v 2 ≠ 0) (hw : w 1 ≠ 0 ∨ w 2 ≠ 0) :
    ∃ B ∈ stabE0 F, (B : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w := by
  obtain ⟨Bv, hBv, hv'⟩ := exists_stabE0_mulVec_e1 hv
  obtain ⟨Bw, hBw, hw'⟩ := exists_stabE0_mulVec_e1 hw
  refine ⟨Bw * Bv⁻¹, (stabE0 F).mul_mem hBw ((stabE0 F).inv_mem hBv), ?_⟩
  rw [← hv', ← hw', Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel_right]

theorem eq_smul_e0 {v : Fin 3 → F} (h1 : v 1 = 0) (h2 : v 2 = 0) : v = v 0 • ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [h1, h2]

theorem eq_top_of_stabE0_le {X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hX : stabE0 F ≤ X) {g : Matrix.SpecialLinearGroup (Fin 3) F} (hg : g ∈ X)
    (hge : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 1 ≠ 0 ∨
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0) : X = ⊤ := by
  classical
  rw [eq_top_iff]
  intro h _
  set w := (h : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] with hw
  obtain ⟨x, hxX, hxw⟩ : ∃ x ∈ X, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = w := by
    by_cases hw' : w 1 ≠ 0 ∨ w 2 ≠ 0
    · obtain ⟨B, hB, hBw⟩ := stabE0_trans hge hw'
      refine ⟨B * g, X.mul_mem (hX hB) hg, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hBw]
    · push Not at hw'
      have hc0 : w 0 ≠ 0 := by
        intro h0
        have hw0 : w = 0 := by
          funext i
          fin_cases i <;> simp [h0, hw'.1, hw'.2]
        have hdet : ((h : Matrix (Fin 3) (Fin 3) F)).det ≠ 0 := by rw [h.2]; exact one_ne_zero
        have h1 := Matrix.eq_zero_of_mulVec_eq_zero hdet (hw ▸ hw0 : _)
        have := congrFun h1 0
        simp at this
      set u := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ![1, 0, 0] with hu
      have hgu : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ u = ![1, 0, 0] := by
        rw [hu, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      have hu' : u 1 ≠ 0 ∨ u 2 ≠ 0 := by
        by_contra hno
        push Not at hno
        have hue := eq_smul_e0 hno.1 hno.2
        have h1 : ![1, 0, 0] = u 0 • ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) := by
          rw [← Matrix.mulVec_smul, ← hue, hgu]
        have h0 : u 0 ≠ 0 := by
          intro h0
          rw [h0, zero_smul] at h1
          have := congrFun h1 0
          simp at this
        have e : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = (u 0)⁻¹ • ![1, 0, 0] := by
          calc (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
                (u 0)⁻¹ • (u 0 • ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0])) := by
                rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
            _ = (u 0)⁻¹ • ![1, 0, 0] := by rw [← h1]
        rw [e] at hge
        simp at hge
      have hcu : (w 0 • u) 1 ≠ 0 ∨ (w 0 • u) 2 ≠ 0 := by
        rcases hu' with h | h
        · left
          simp [h, hc0]
        · right
          simp [h, hc0]
      obtain ⟨B, hB, hBu⟩ := stabE0_trans hu' hcu
      refine ⟨g * B * g⁻¹, X.mul_mem (X.mul_mem hg (hX hB)) (X.inv_mem hg), ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu, hBu, Matrix.mulVec_smul, hgu]
      exact (eq_smul_e0 hw'.1 hw'.2).symm
  have hxh : x⁻¹ * h ∈ stabE0 F := by
    refine mem_stabE0.mpr ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hw, ← hxw,
      Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have := X.mul_mem hxX (hX hxh)
  rwa [mul_inv_cancel_left] at this

theorem exists_mulVec_eq {v w : Fin 3 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w := by
  obtain ⟨gv, hgv⟩ := exists_mulVec_e0 hv
  obtain ⟨gw, hgw⟩ := exists_mulVec_e0 hw
  refine ⟨gw * gv⁻¹, ?_⟩
  rw [← hgv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right,
    hgw]

theorem eq_bot_of_normal_isPGroup_SL3 [Finite F] [CharP F 2]
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hNn : N.Normal) (hN : IsPGroup 2 N) :
    N = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥N (Fin 3 → F) :=
    { smul := fun n v => ((n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      one_smul := fun v => by
        show (((1 : ↥N) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v
        simp
      mul_smul := fun a b v => by
        show (((a * b : ↥N) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          v = ((a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            (((b : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
        rw [Matrix.mulVec_mulVec]
        rfl }
  have hmod := hN.card_modEq_card_fixedPoints (Fin 3 → F)
  have hcard : 2 ∣ Nat.card (Fin 3 → F) := by
    have : Nontrivial F := inferInstance
    rw [Nat.card_fun, Nat.card_fin]
    have h2 : 2 ∣ Nat.card F := by
      have h1 : addOrderOf (1 : F) = 2 := CharP.eq F (CharP.addOrderOf_one F) inferInstance
      rw [← h1]
      exact addOrderOf_dvd_natCard (1 : F)
    exact dvd_pow h2 (by norm_num)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥N (Fin 3 → F)) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hcard)))
  have h0 : (0 : Fin 3 → F) ∈ MulAction.fixedPoints ↥N (Fin 3 → F) := fun n => by
    show ((n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ 0 = 0
    exact Matrix.mulVec_zero _
  obtain ⟨v, hvfix, hv0⟩ : ∃ v ∈ MulAction.fixedPoints ↥N (Fin 3 → F), v ≠ 0 := by
    by_contra hno
    push Not at hno
    have hsub : MulAction.fixedPoints ↥N (Fin 3 → F) ⊆ {0} := fun v hv => hno v hv
    have hle : Nat.card (MulAction.fixedPoints ↥N (Fin 3 → F)) ≤ 1 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton] at this
      rwa [Nat.card_coe_set_eq]
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥N (Fin 3 → F)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, Set.toFinite _⟩
    have := Nat.le_of_dvd hpos hfix2
    omega
  have hall : ∀ n ∈ N, ∀ w : Fin 3 → F,
      ((n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    intro n hn w
    by_cases hw0 : w = 0
    · rw [hw0, Matrix.mulVec_zero]
    obtain ⟨g, hg⟩ := exists_mulVec_eq hv0 hw0
    have hconj : g⁻¹ * n * g ∈ N := by
      have := hNn.conj_mem n hn g⁻¹
      simpa using this
    have hfx := hvfix ⟨_, hconj⟩
    have hfx' : ((g⁻¹ * n * g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        v = v := hfx
    rw [← hg]
    have e : g * (g⁻¹ * n * g) = n * g := by group
    calc ((n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
          ((n * g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
      _ = ((g * (g⁻¹ * n * g) : Matrix.SpecialLinearGroup (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) *ᵥ v := by rw [e]
      _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
          rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hfx']
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  have := congrFun (hall n hn (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simp only [Matrix.one_apply]
  rw [show ((n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
    (((n : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).col j) i from rfl, this]
  simp [Pi.single_apply]

end SL3Pt

variable {G : Type} [Group G] [Finite G]

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem stab_eq : H ⊓ M ⊓ K = K ⊓ Subgroup.normalizer (v432 T M L : Set G) := by
  obtain ⟨m₀, F₀, _, _, -, -, -, -, -, -, -, hline⟩ := s.c3
  have hline' : IsStabilizedLineOfNatural F₀ (pCoreOf 2 I) (H ⊓ M) K (v432 T M L) := by
    rcases hline with h | ⟨h2, -⟩
    · exact h
    · exact absurd h2 (not_isC134Case2_of_isC134Case3 s.c134)
  obtain ⟨-, -, -, -, -, -, hstab⟩ := hline'
  exact hstab

theorem normalizer_ZS_le (hL : L ≤ Subgroup.normalizer (ZS : Set G)) :
    Subgroup.normalizer (ZS : Set G) ≤ M := by
  refine isUniqueM_normalizer_le s.sk.lemma_4_3_5 s.ZS_ne_bot s.ZS_isPGroup ?_
  refine _root_.sup_le hL (_root_.sup_le (inf_le_left.trans s.T_le_normalizer_ZS) ?_)
  exact Subgroup.zpowers_le.mpr (s.T_le_normalizer_ZS s.sk.t_mem)

theorem exists_L_not_normalizer_ZS : ∃ l ∈ L, l ∉ Subgroup.normalizer (ZS : Set G) := by
  classical
  by_contra hno
  push Not at hno
  have hN := s.normalizer_ZS_le hno
  have hK₂M : K₂ ≤ M := (s.K₂_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)).trans hN
  have hK₂H : K₂ ≤ H := s.K₂_le_K.trans (le_of_mem_cComp s.sk.cComp)
  have hK₂V : K₂ ≤ Subgroup.normalizer (v432 T M L : Set G) := by
    intro k hk
    have : k ∈ H ⊓ M ⊓ K := ⟨⟨hK₂H hk, hK₂M hk⟩, s.K₂_le_K hk⟩
    rw [s.stab_eq] at this
    exact this.2
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W', w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra hno'
    push Not at hno'
    have hle : W' ≤ Submodule.span F {![1, 0, 0]} := by
      intro w hw
      rw [Submodule.mem_span_singleton]
      exact ⟨w 0, (SL3Pt.eq_smul_e0 (hno' w hw).1 (hno' w hw).2).symm⟩
    have h1 := Submodule.finrank_mono hle
    rw [s.W'_rank, finrank_span_singleton (by
      intro h
      have := congrFun h 0
      simp at this)] at h1
    omega
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → F, u ∉ W' := by
    by_contra hno'
    push Not at hno'
    have htop : W' = ⊤ := eq_top_iff.mpr fun u _ => hno' u
    have := s.W'_rank
    rw [htop, finrank_top, Module.finrank_fin_fun] at this
    omega
  have hu' : u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    rw [SL3Pt.eq_smul_e0 h.1 h.2]
    exact W'.smul_mem _ s.e0_mem
  obtain ⟨B, hB, hBw⟩ := SL3Pt.stabE0_trans hw hu'
  have hB' : specialLinearGroupEquivStatedSL 3 F B ∈ stE0 F := ⟨B, hB, rfl⟩
  rw [← s.K₂_map] at hB'
  obtain ⟨⟨k, hkK⟩, hk, hαk⟩ := hB'
  obtain ⟨v, hv⟩ := s.β_bij.2 (Multiplicative.ofAdd w)
  have hvV : (v : G) ∈ v432 T M L := (s.V_iff v).mpr (by rw [hv]; exact hwW)
  have hkv : k * v * k⁻¹ ∈ v432 T M L := (Subgroup.mem_normalizer_iff.mp (hK₂V hk) v).mp hvV
  have hkvU : k * v * k⁻¹ ∈ u4311 I K := s.V_le hkv
  have h1 := s.β_act ⟨k, hkK⟩ v ⟨_, hkvU⟩ rfl
  rw [hαk, specialLinearGroupEquivStatedSL_coe, hv, toAdd_ofAdd, hBw] at h1
  exact hu (h1 ▸ (s.V_iff ⟨_, hkvU⟩).mp hkv)

theorem α_moves_e0 {l : G} (hl : l ∈ L) (hlN : l ∉ Subgroup.normalizer (ZS : Set G)) :
    ((((α ⟨l, s.sk.L_le_K hl⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ![1, 0, 0]) 1 ≠ 0 ∨
      ((((α ⟨l, s.sk.L_le_K hl⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ![1, 0, 0]) 2 ≠ 0 := by
  by_contra h
  push Not at h
  have he := SL3Pt.eq_smul_e0 h.1 h.2
  set d := ((((α ⟨l, s.sk.L_le_K hl⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 0 with hd
  apply hlN
  apply mem_normalizer_of_map_conj_le
  rintro _ ⟨z, hz, rfl⟩
  have hzU := s.ZS_le_U hz
  have hlK := s.sk.L_le_K hl
  have hlzU : l * z * l⁻¹ ∈ u4311 I K := (Subgroup.mem_normalizer_iff.mp (s.K_U hlK) z).mp hzU
  obtain ⟨c, hc⟩ := (s.ZS_iff ⟨z, hzU⟩).mp hz
  have h1 := s.β_act ⟨l, hlK⟩ ⟨z, hzU⟩ ⟨_, hlzU⟩ rfl
  refine (s.ZS_iff ⟨_, hlzU⟩).mpr ⟨c * d, ?_⟩
  rw [h1, hc, Matrix.mulVec_smul, he, smul_smul]

theorem map_J_eq_top : ((L ⊔ K₂).subgroupOf K).map α = ⊤ := by
  obtain ⟨l, hl, hlN⟩ := s.exists_L_not_normalizer_ZS
  have hLK : L ≤ K := s.sk.L_le_K
  set X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (((L ⊔ K₂).subgroupOf K).map α).comap (specialLinearGroupEquivStatedSL 3 F).toMonoidHom
    with hXdef
  have hX : stabE0 F ≤ X := by
    intro B hB
    show specialLinearGroupEquivStatedSL 3 F B ∈ ((L ⊔ K₂).subgroupOf K).map α
    have h1 : specialLinearGroupEquivStatedSL 3 F B ∈ stE0 F := ⟨B, hB, rfl⟩
    rw [← s.K₂_map] at h1
    obtain ⟨k, hk, hkB⟩ := h1
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hk)),
      hkB⟩
  have hg : (specialLinearGroupEquivStatedSL 3 F).symm (α ⟨l, hLK hl⟩) ∈ X := by
    show specialLinearGroupEquivStatedSL 3 F ((specialLinearGroupEquivStatedSL 3 F).symm
      (α ⟨l, hLK hl⟩)) ∈ ((L ⊔ K₂).subgroupOf K).map α
    rw [MulEquiv.apply_symm_apply]
    exact ⟨⟨l, hLK hl⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl), rfl⟩
  have hcoe : ((((specialLinearGroupEquivStatedSL 3 F).symm (α ⟨l, hLK hl⟩) :
      Matrix.SpecialLinearGroup (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      (((α ⟨l, hLK hl⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
  have htop := SL3Pt.eq_top_of_stabE0_le hX hg (by rw [hcoe]; exact s.α_moves_e0 hl hlN)
  rw [eq_top_iff]
  intro x _
  have h1 : (specialLinearGroupEquivStatedSL 3 F).symm x ∈ X := htop ▸ Subgroup.mem_top _
  have h2 : specialLinearGroupEquivStatedSL 3 F ((specialLinearGroupEquivStatedSL 3 F).symm x) ∈
      ((L ⊔ K₂).subgroupOf K).map α := h1
  rwa [MulEquiv.apply_symm_apply] at h2

theorem J_le_K : L ⊔ K₂ ≤ K := _root_.sup_le s.sk.L_le_K s.K₂_le_K

theorem exists_mul_of_mem_K (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {k : G}
    (hk : k ∈ K) : ∃ j ∈ L ⊔ K₂, j⁻¹ * k ∈ q4311 I K := by
  have h0 : α ⟨k, hk⟩ ∈ ((L ⊔ K₂).subgroupOf K).map α := s.map_J_eq_top ▸ Subgroup.mem_top _
  obtain ⟨j, hj, hjk⟩ := h0
  refine ⟨j, Subgroup.mem_subgroupOf.mp hj, ?_⟩
  have h1 : α (j⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hjk, inv_mul_cancel]
  have h2 : j⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by rw [← s.modO2.2]; exact h1
  have h3 := (mem_pCoreOf_iff' _).mpr h2
  rw [s.pCoreOf_K_eq h135 hR hC h37 h38 h39] at h3
  simpa using h3

theorem K_le_normalizer_q4311 (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    K ≤ Subgroup.normalizer ((q4311 I K : Subgroup G) : Set G) := by
  rw [← s.pCoreOf_K_eq h135 hR hC h37 h38 h39]
  exact le_normalizer_pCoreOf 2 K

theorem pCoreOf_J_eq (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    pCoreOf 2 (L ⊔ K₂) = (L ⊔ K₂) ⊓ q4311 I K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  have hJK := s.J_le_K
  have hKQ := s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39
  apply le_antisymm
  · intro x hx
    have hxJ : x ∈ L ⊔ K₂ := pCoreOf_le 2 _ hx
    have hxK : x ∈ K := hJK hxJ
    refine ⟨hxJ, ?_⟩
    set e := specialLinearGroupEquivStatedSL 3 F with he
    set N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
      (((pCoreOf 2 (L ⊔ K₂)).subgroupOf K).map α).comap e.toMonoidHom with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨w, hw, hwn⟩ := hn
      have hg : e g ∈ ((L ⊔ K₂).subgroupOf K).map α := s.map_J_eq_top ▸ Subgroup.mem_top _
      obtain ⟨j, hj, hjg⟩ := hg
      have hjN : (j : G) ∈ Subgroup.normalizer ((pCoreOf 2 (L ⊔ K₂) : Subgroup G) : Set G) :=
        le_normalizer_pCoreOf 2 _ (Subgroup.mem_subgroupOf.mp hj)
      have hw' : (j : G) * w * (j : G)⁻¹ ∈ pCoreOf 2 (L ⊔ K₂) :=
        (Subgroup.mem_normalizer_iff.mp hjN w).mp (Subgroup.mem_subgroupOf.mp hw)
      refine ⟨j * w * j⁻¹, Subgroup.mem_subgroupOf.mpr hw', ?_⟩
      show α (j * w * j⁻¹) = e (g * n * g⁻¹)
      rw [map_mul, map_mul, map_inv, hjg, hwn, map_mul, map_mul, map_inv]
      rfl
    have hN2 : IsPGroup 2 ↥N := by
      intro n
      obtain ⟨w, hw, hwn⟩ := n.2
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (L ⊔ K₂)) ⟨w, Subgroup.mem_subgroupOf.mp hw⟩
      have hk' : w ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      refine ⟨k, Subtype.ext (e.injective ?_)⟩
      show e ((n : Matrix.SpecialLinearGroup (Fin 3) F) ^ 2 ^ k) = e 1
      rw [map_pow, map_one]
      have h1 : e (n : Matrix.SpecialLinearGroup (Fin 3) F) = α w := hwn.symm
      rw [h1, ← map_pow, hk', map_one]
    have hbot := SL3Pt.eq_bot_of_normal_isPGroup_SL3 hNn hN2
    have hmem : e.symm (α ⟨x, hxK⟩) ∈ N := by
      show e (e.symm (α ⟨x, hxK⟩)) ∈ ((pCoreOf 2 (L ⊔ K₂)).subgroupOf K).map α
      rw [MulEquiv.apply_symm_apply]
      exact ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hα1 : α ⟨x, hxK⟩ = 1 := by
      have := congrArg e hmem
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have h2 : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by rw [← s.modO2.2]; exact hα1
    have h3 := (mem_pCoreOf_iff' _).mpr h2
    rwa [s.pCoreOf_K_eq h135 hR hC h37 h38 h39] at h3
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun j hj => ?_)
      ((isPGroup_q4311 I K).to_le inf_le_right)
    exact mem_normalizer_inf (Subgroup.le_normalizer hj) (hKQ (hJK hj))

theorem q4311_le_K : q4311 I K ≤ K := by
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp s.sk.cComp
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    s.sk.base.pCoreOf_le_S.trans s.sk.S_le_normalizer
  rw [q4311, c134Q]
  exact (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1.trans (pCoreOf_le 2 K)

theorem exists_K₂_inf_U_ne_one : ∃ c ∈ K₂, c ∈ u4311 I K ∧ c ≠ 1 := by
  classical
  let A : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hB : specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL A) ∈ stE0 F :=
    ⟨_, SL3Pt.blkSL_mem_stabE0 A, rfl⟩
  rw [← s.K₂_map] at hB
  obtain ⟨⟨k, hkK⟩, hk, hαk⟩ := hB
  have hk₂ : k ∈ K₂ := hk
  obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd ![0, 0, 1])
  have huU : (u : G) ∈ u4311 I K := u.2
  have huK : (u : G) ∈ K := s.q4311_le_K huU.1
  have huC : (u : G) ∈ Subgroup.centralizer (ZS : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subgroup.mem_centralizer_iff.mp huU.2 z (s.ZS_le_U hz).1
  have huN : (u : G) ∈ Subgroup.normalizer (K₂ : Set G) := by
    rw [s.K₂_eq]
    exact normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer ⟨huK, huC⟩)
  have hkuU : k * u * k⁻¹ ∈ u4311 I K := (Subgroup.mem_normalizer_iff.mp (s.K_U hkK) u).mp huU
  refine ⟨k * u * k⁻¹ * (u : G)⁻¹, ?_, ?_, ?_⟩
  · have h1 : (u : G) * k⁻¹ * (u : G)⁻¹ ∈ K₂ :=
      (Subgroup.mem_normalizer_iff.mp huN k⁻¹).mp (K₂.inv_mem hk₂)
    have e : k * u * k⁻¹ * (u : G)⁻¹ = k * ((u : G) * k⁻¹ * (u : G)⁻¹) := by group
    rw [e]
    exact K₂.mul_mem hk₂ h1
  · exact (u4311 I K).mul_mem hkuU ((u4311 I K).inv_mem huU)
  · intro h1
    have hkuk : k * u * k⁻¹ = u := by
      calc k * u * k⁻¹ = (k * u * k⁻¹ * (u : G)⁻¹) * u := by group
        _ = u := by rw [h1, one_mul]
    have h2 := s.β_act ⟨k, hkK⟩ u ⟨_, hkuU⟩ rfl
    have h3 : (⟨k * u * k⁻¹, hkuU⟩ : ↥(u4311 I K)) = u := Subtype.ext hkuk
    rw [h3, hαk, specialLinearGroupEquivStatedSL_coe, hu, toAdd_ofAdd] at h2
    have := congrFun h2 1
    simp [SL3Pt.blkSL, SL3Pt.blk, Matrix.mulVec, dotProduct, Fin.sum_univ_three, A] at this

theorem U_le_J : u4311 I K ≤ L ⊔ K₂ := by
  obtain ⟨c, hcK₂, hcU, hc1⟩ := s.exists_K₂_inf_U_ne_one
  have hne : ∀ x : ↥(u4311 I K), x ≠ 1 → Multiplicative.toAdd (β x) ≠ 0 := by
    intro x hx h
    apply hx
    apply s.β_bij.1
    rw [map_one]
    exact Multiplicative.toAdd.injective (by rw [h, toAdd_one])
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact Subgroup.one_mem _
  have hβc := hne ⟨c, hcU⟩ (fun h => hc1 (congrArg Subtype.val h))
  have hβv := hne ⟨v, hv⟩ (fun h => hv1 (congrArg Subtype.val h))
  obtain ⟨g, hg⟩ := SL3Pt.exists_mulVec_eq hβc hβv
  have hgJ : specialLinearGroupEquivStatedSL 3 F g ∈ ((L ⊔ K₂).subgroupOf K).map α :=
    s.map_J_eq_top ▸ Subgroup.mem_top _
  obtain ⟨j, hj, hjg⟩ := hgJ
  have hjcU : (j : G) * c * (j : G)⁻¹ ∈ u4311 I K :=
    (Subgroup.mem_normalizer_iff.mp (s.K_U j.2) c).mp hcU
  have h1 := s.β_act j ⟨c, hcU⟩ ⟨_, hjcU⟩ rfl
  rw [hjg, specialLinearGroupEquivStatedSL_coe, hg] at h1
  have h2 : (⟨_, hjcU⟩ : ↥(u4311 I K)) = ⟨v, hv⟩ := s.β_bij.1 (Multiplicative.toAdd.injective h1)
  have h3 : (j : G) * c * (j : G)⁻¹ = v := congrArg Subtype.val h2
  rw [← h3]
  have hjJ : (j : G) ∈ L ⊔ K₂ := Subgroup.mem_subgroupOf.mp hj
  exact (L ⊔ K₂).mul_mem ((L ⊔ K₂).mul_mem hjJ (Subgroup.mem_sup_right hcK₂))
    ((L ⊔ K₂).inv_mem hjJ)

theorem comm_mem_u {a b : G} (ha : a ∈ q4311 I K) (hb : b ∈ q4311 I K) :
    a * b * a⁻¹ * b⁻¹ ∈ u4311 I K := by
  obtain ⟨-, -, β₂, -, hβ₂k, -⟩ := s.dualQ
  have h1 : β₂ (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (β₂ ⟨a, ha⟩) (β₂ ⟨b, hb⟩)]
    group
  have h2 : (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥(q4311 I K)) ∈ β₂.ker := h1
  rw [hβ₂k, Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem K_le_normalizer_pCoreOf_J (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    K ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ K₂) : Subgroup G) : Set G) := by
  rw [s.pCoreOf_J_eq h135 hR hC h37 h38 h39]
  intro k hk
  obtain ⟨j, hj, hq⟩ := s.exists_mul_of_mem_K h135 hR hC h37 h38 h39 hk
  have hkjq : k = j * (j⁻¹ * k) := by group
  have hKQ := s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39
  have hjN : j ∈ Subgroup.normalizer (((L ⊔ K₂) ⊓ q4311 I K : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hj) (hKQ (s.J_le_K hj))
  have hqN : j⁻¹ * k ∈ Subgroup.normalizer (((L ⊔ K₂) ⊓ q4311 I K : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨x, hx, rfl⟩
    have hc := s.comm_mem_u ((q4311 I K).inv_mem hx.2) hq
    have hcJ := s.U_le_J hc
    refine ⟨?_, ?_⟩
    · have e : (MulAut.conj (j⁻¹ * k)).toMonoidHom x =
          x * (x⁻¹ * (j⁻¹ * k) * x⁻¹⁻¹ * (j⁻¹ * k)⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (L ⊔ K₂).mul_mem hx.1 hcJ
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (q4311 I K).mul_mem ((q4311 I K).mul_mem hq hx.2) ((q4311 I K).inv_mem hq)
  rw [hkjq]
  exact Subgroup.mul_mem _ hjN hqN

theorem not_T_le_normalizer_K₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ¬ T ≤ Subgroup.normalizer (K₂ : Set G) := by
  intro hT
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    s.sk.base.hyp.normal (s.sk.base.hyp.T_le hx)
  have hTJ : T ≤ Subgroup.normalizer ((L ⊔ K₂ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL hx),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hT hx)]
  have hTO : T ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ K₂) : Subgroup G) : Set G) :=
    hTJ.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hLO : L ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ K₂) : Subgroup G) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨c, hcK₂, hcU, hc1⟩ := s.exists_K₂_inf_U_ne_one
  have hcO : c ∈ pCoreOf 2 (L ⊔ K₂) := by
    rw [s.pCoreOf_J_eq h135 hR hC h37 h38 h39]
    exact ⟨Subgroup.mem_sup_right hcK₂, hcU.1⟩
  have hne : pCoreOf 2 (L ⊔ K₂) ≠ ⊥ := fun h => by
    rw [h, Subgroup.mem_bot] at hcO
    exact hc1 hcO
  have hN := isUniqueM_normalizer_le s.sk.lemma_4_3_5 hne (pCoreOf_isPGroup 2 _)
    (_root_.sup_le hLO (_root_.sup_le (inf_le_left.trans hTO)
      (Subgroup.zpowers_le.mpr (hTO s.sk.t_mem))))
  have hKM : K ≤ M := (s.K_le_normalizer_pCoreOf_J h135 hR hC h37 h38 h39).trans hN
  exact s.sk.not_le (le_inf (le_of_mem_cComp s.sk.cComp) hKM)

theorem lemma_4_3_13 (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {KZ : Subgroup G}
    (hKZn : Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G))
    (hK₂ : K₂ ≤ KZ) : K₂ < KZ := by
  refine lt_of_le_of_ne hK₂ fun h => s.not_T_le_normalizer_K₂ h135 hR hC h37 h38 h39 ?_
  rw [h]
  exact s.T_le_normalizer_ZS.trans hKZn

end Setting4311

end CFSG.Quasithin.H13.Ch4
