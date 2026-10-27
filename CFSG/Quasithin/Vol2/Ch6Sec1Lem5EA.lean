module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DN
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5EFF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

theorem eq_top_of_upper_ch615 {F : Type} [Field F] {S : Subgroup (SL(2, F))}
    (hS : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 → g ∈ S)
    {y : SL(2, F)} (hyS : y ∈ S) (hy : (y : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : S = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact hS g hg
  set α : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 0 -
    (y : Matrix (Fin 2) (Fin 2) F) 0 0 / (y : Matrix (Fin 2) (Fin 2) F) 1 0 with hα
  have hB : ((y⁻¹ * (unipSL α)⁻¹ * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hα]
    field_simp
    ring
  have e : g = unipSL α * y * (y⁻¹ * (unipSL α)⁻¹ * g) := by group
  rw [e]
  exact S.mul_mem (S.mul_mem (hS _ (by simp [coe_unipSL])) hyS) (hS _ hB)

theorem upper_conj_unipSL_ch615 {F : Type} [Field F] {A : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (b : F) :
    A * unipSL b * A⁻¹ = unipSL ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b) := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two, hA, mul_zero, sub_zero] at this
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, hA]
  all_goals first
    | linear_combination hdet
    | ring

theorem eq_unipSL_of_upper_ch615 {F : Type} [Field F] {A : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (h1 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) :
    A = unipSL ((A : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two, hA, mul_zero, sub_zero, h1, one_mul] at this
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, hA, h1, hdet]

variable {G : Type} [Group G]

namespace QCoord

variable {L N : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem mem_borelL_of_upper_ch615 [Finite G] {T : Subgroup G} (hc : QCoord L N (T ⊓ L) F ψ Y)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T) {g : G} (hg : g ∈ L)
    (hup : (ψ (autHom hc.le_normalizer ⟨g, hg⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    g ∈ borelL T L := by
  have hLN := hc.le_normalizer
  refine Subgroup.mem_inf.mpr ⟨hg, mem_normalizer_of_conj_mem_ch6 fun s hs => ?_⟩
  have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
  have hgs : g * s * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hg hsL) (L.inv_mem hg)
  refine Subgroup.mem_inf.mpr ⟨?_, hgs⟩
  have hsS : ((autHom hLN ⟨s, hsL⟩ : ↥(autOn L N)) : MulAut ↥N) ∈ autOn (T ⊓ L) N :=
    mem_autOn_iff.mpr ⟨⟨s, hLN hsL⟩, hs, rfl⟩
  obtain ⟨b, hb⟩ := (hc.sylow _).mp hsS
  have hgsb : ψ (autHom hLN ⟨g * s * g⁻¹, hgs⟩) =
      unipSL ((ψ (autHom hLN ⟨g, hg⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b) := by
    have : (autHom hLN ⟨g * s * g⁻¹, hgs⟩ : ↥(autOn L N)) =
        autHom hLN ⟨g, hg⟩ * autHom hLN ⟨s, hsL⟩ * (autHom hLN ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this, map_mul, map_mul, map_inv, hb, upper_conj_unipSL_ch615 hup]
  have hmem : ((autHom hLN ⟨g * s * g⁻¹, hgs⟩ : ↥(autOn L N)) : MulAut ↥N) ∈
      autOn (T ⊓ L) N := (hc.sylow _).mpr ⟨_, hgsb⟩
  exact mem_of_conjAct_mem_autOn hC ⟨g * s * g⁻¹, hLN hgs⟩ (Subgroup.mem_sup_left hgs) hmem

theorem exists_mem_borelL_eq_ch615 [Finite G] {T : Subgroup G} (hc : QCoord L N (T ⊓ L) F ψ Y)
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T) {A : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∃ (g : G) (hg : g ∈ borelL T L), ψ (autHom hc.le_normalizer ⟨g, hg.1⟩) = A := by
  have hLN := hc.le_normalizer
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two, hA, mul_zero, sub_zero] at this
    exact this
  have ha0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  obtain ⟨g, hg, hgc⟩ := hc.exists_mem_borel hC ha0
  set B := ψ (autHom hLN ⟨g, hg.1⟩) with hBdef
  have hBup : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hc.upper hg.1 hg.2
  have hBdet : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have := B.2
    rw [Matrix.det_fin_two, hBup, mul_zero, sub_zero] at this
    exact this
  have hBA1 : ((B⁻¹ * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, hBup, hA]
  have hBA0 : ((B⁻¹ * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, hBup, hA]
    rw [← hgc]
    linear_combination hBdet
  have hu := eq_unipSL_of_upper_ch615 hBA1 hBA0
  set b := ((B⁻¹ * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 with hbdef
  have hsS : ((ψ.symm (unipSL b) : ↥(autOn L N)) : MulAut ↥N) ∈ autOn (T ⊓ L) N :=
    (hc.sylow _).mpr ⟨b, by simp⟩
  obtain ⟨p, hp, hpc⟩ := mem_autOn_iff.mp hsS
  have hpL : (p : G) ∈ L := (Subgroup.mem_inf.mp hp).2
  have hps : autHom hLN ⟨p, hpL⟩ = ψ.symm (unipSL b) := Subtype.ext hpc
  refine ⟨g * p, (borelL T L).mul_mem hg (Hyp5_0_1.inf_le_borel T L hp), ?_⟩
  have e : (autHom hLN ⟨g * p, L.mul_mem hg.1 hpL⟩ : ↥(autOn L N)) =
      autHom hLN ⟨g, hg.1⟩ * autHom hLN ⟨p, hpL⟩ := by
    rw [← map_mul]
    rfl
  rw [e, map_mul, hps, MulEquiv.apply_symm_apply, ← hu, ← hBdef, mul_inv_cancel_left]

end QCoord

variable [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem inf_eq_borelL_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n) :
    (borelL T L ⊔ H) ⊓ L = borelL T L := by
  classical
  have h := c.hyp
  refine le_antisymm (fun g hg => ?_) (le_inf le_sup_left inf_le_left)
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨F, _, _, _, -, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [c.V_eq]; exact hS.centralizer_le
  have hLN := hc.le_normalizer
  by_cases hup : (ψ (autHom hLN ⟨g, hg.2⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact hc.mem_borelL_of_upper_ch615 hCV hg.2 hup
  exfalso
  set X := borelL T L ⊔ H with hXdef
  set φ : ↥L →* SL(2, F) := ψ.toMonoidHom.comp (autHom hLN) with hφ
  have htop : ((X ⊓ L).subgroupOf L).map φ = ⊤ := by
    refine eq_top_of_upper_ch615 (fun A hA => ?_)
      ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩ hup
    obtain ⟨b, hb, hbA⟩ := hc.exists_mem_borelL_eq_ch615 hCV hA
    exact ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_sup_left hb, hb.1⟩, hbA⟩
  have hLX : L ≤ X := by
    intro l hl
    have hmem : φ ⟨l, hl⟩ ∈ ((X ⊓ L).subgroupOf L).map φ := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxl⟩ := hmem
    have hx' : (x : G) ∈ X ⊓ L := Subgroup.mem_subgroupOf.mp hx
    have h1 : autHom hLN (x⁻¹ * ⟨l, hl⟩) = 1 := by
      have h2 : φ (x⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hxl, inv_mul_cancel]
      apply ψ.injective
      rw [map_one]
      exact h2
    have hcen := mem_centralizer_of_autHom_eq_one hLN h1
    have hxlT : ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ T :=
      hCV ⟨Subgroup.mem_sup_left (x⁻¹ * ⟨l, hl⟩).2, hcen⟩
    have hxlX : ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ X :=
      Subgroup.mem_sup_left (Hyp5_0_1.inf_le_borel T L ⟨hxlT, (x⁻¹ * ⟨l, hl⟩).2⟩)
    have e : l = (x : G) * ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact X.mul_mem hx'.1 hxlX
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, c.X_O2, pCoreOf_isPGroup 2 X, rfl⟩
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
  have hTX : T ≤ X := c.hH.1.1.trans le_sup_right
  exact c.hH.2.1 ((le_sup_right.trans hXN).trans (le_of_isUniqueM_of_le_twoLocal
    (h.isUniqueM h432) (sup_le (hLX.trans hXN) (hTX.trans hXN)) hloc))

end Cx615C

theorem res615E_of (h432 : Stmt4_3_2) (hFF : Res615EFF) : Res615E := by
  intro G _ _ T M L V H n c hN
  have h := c.hyp
  obtain ⟨z, hz, hz1, ⟨d, hdB, hdodd, hd1, hdz⟩, hnot⟩ := hFF G T M L V H n c hN
  apply hnot
  have hzZ := mem_quasithinOmegaOneCenter_iff.mp hz.1
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := c.CZd d hdB hdodd hd1 ⟨hz.1, hzd⟩
  have hord : orderOf z = 2 := orderOf_eq_prime hzZ.2.2 hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers z ≠ ⊥ := fun h0 => hz1 (by
    have := Subgroup.mem_zpowers z
    rw [h0] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (fun l hl => Cx615C.mem_normalizer_zpowers_ch615
      (Subgroup.mem_centralizer_iff.mp hzL l hl))
      (fun t ht => Cx615C.mem_normalizer_zpowers_ch615
        (Subgroup.mem_centralizer_iff.mp hzZ.2.1 t ht))
  have hNM := le_of_isUniqueM_of_le_twoLocal (h.isUniqueM h432) hLT hloc
  intro x hx
  have hxz : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hx.2 z rfl).symm
  have hxM : x ∈ M := hNM (Cx615C.mem_normalizer_zpowers_ch615 hxz)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.normal hxM
  have hxX : x ∈ Subgroup.normalizer ((borelL T L ⊔ H : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hx.1
  have hxXL := Subgroup.inf_normalizer_le_normalizer_inf ⟨hxX, hxL⟩
  rwa [c.inf_eq_borelL_ch615 h432] at hxXL

end CFSG.Quasithin.H13
