module

public import CFSG.Quasithin.Vol2.Ch11SecFU2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique.C5 (conjSubgroup_mono conjSubgroup_normalizer conjSubgroup_inf
  conjSubgroup_centralizer conjSubgroup_eq_self conjSubgroup_commutator)
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev wH (T I V₁ : Subgroup G) : Subgroup G :=
  conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))

abbrev qOf (T I V₁ : Subgroup G) (y : G) : Subgroup G :=
  (wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔
    (conjSubgroup (wH T I V₁) y ⊓ Subgroup.centralizer (fsuV T I : Set G))

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem commutator_wH_le (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) :
    ⁅wH T I V₁, wH T I V₁⁆ ≤ V₁ := by
  have hVW := commutator_fsuV_conjClosure_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
    hV₂ hV₃ hk
  have hG₁W : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ : Subgroup G) : Set G) := le_normalizer_conjClosure _ _
  rw [Subgroup.commutator_comm]
  have hS : wH T I V₁ ≤ commSub (wH T I V₁) V₁ := by
    refine conjClosure_le fun g hg v hv => mem_commSub.mpr ⟨?_, fun x hx => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg
        (SecA.IsVi.le_normalizer hV₁ (SecA.fsuV_le_T h hv))) (Subgroup.inv_mem _ hg)
    · have hx' : g⁻¹ * x * g ∈ wH T I V₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (hG₁W (Subgroup.inv_mem _ hg)) x).mp hx
        simpa using this
      have h1 : ⁅g⁻¹ * x * g, v⁆ ∈ V₁ := by
        rw [Subgroup.commutator_comm] at hVW
        exact hVW (Subgroup.commutator_mem_commutator hx' hv)
      have heq : ⁅x, g * v * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, v⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp h1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (mem_commSub.mp (hS hy)).2 x hx

theorem sq_mem_of_mem_wH (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hV₁₃ : V₁ ≤ V₃) {w : G} (hw : w ∈ wH T I V₁) : w ^ 2 ∈ V₁ := by
  have hC := conjClosure_le_centralizer_V₃ hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
    hV₃ hk
  have hWW := commutator_wH_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
  have hV₁C : wH T I V₁ ≤ Subgroup.centralizer (V₁ : Set G) :=
    hC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV₁₃))
  let S : Subgroup G :=
    { carrier := {x | x ∈ wH T I V₁ ∧ x ^ 2 ∈ V₁}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have heq : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
          simp only [commutatorElement_def, sq]; group
        rw [heq]
        exact V₁.mul_mem (V₁.mul_mem ha'
          (hWW (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha) hb))) hb'
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow]; exact V₁.inv_mem ha'⟩ }
  have hWS : wH T I V₁ ≤ S := by
    refine conjClosure_le fun g hg v hv => ⟨mem_conjClosure hg hv, ?_⟩
    have hv2 : v ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 v hv
    have heq : (g * v * g⁻¹) ^ 2 = g * v ^ 2 * g⁻¹ := by
      simp only [sq]; group
    rw [heq, hv2, mul_one, mul_inv_cancel]
    exact V₁.one_mem
  exact (hWS hw).2

theorem conjSubgroup_centralizer_fsuV (h : Hyp11 G T L I n) {y : G} (hy : y ∈ L) :
    conjSubgroup (Subgroup.centralizer (fsuV T I : Set G)) y =
      Subgroup.centralizer (fsuV T I : Set G) := by
  rw [conjSubgroup_centralizer, conjSubgroup_eq_self (SecA.L_le_normalizer_fsuV h hy)]

theorem fsuV_le_conj_wH (h : Hyp11 G T L I n) {y : G} (hy : y ∈ L) :
    fsuV T I ≤ conjSubgroup (wH T I V₁) y := by
  intro v hv
  rw [mem_conjSubgroup_iff]
  exact le_conjClosure_self _ _
    ((Subgroup.mem_normalizer_iff.mp (SecA.L_le_normalizer_fsuV h hy) v).mp hv)

omit [Finite G] in
theorem centralizer_le_normalizer_wH (hV₁ : IsVi T L I n 1 V₁) :
    Subgroup.centralizer (fsuV T I : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ : Subgroup G) : Set G) :=
  ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecA.IsVi.le_fsuV hV₁))).trans
    (Subgroup.centralizer_le_normalizer _)).trans (le_normalizer_conjClosure _ _)

theorem centralizer_le_normalizer_conj_wH (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    {y : G} (hy : y ∈ L) :
    Subgroup.centralizer (fsuV T I : Set G) ≤
      Subgroup.normalizer ((conjSubgroup (wH T I V₁) y : Subgroup G) : Set G) := by
  rw [← conjSubgroup_normalizer, ← conjSubgroup_centralizer_fsuV h hy]
  exact conjSubgroup_mono (centralizer_le_normalizer_wH hV₁) y

theorem centralizer_le_normalizer_inf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    {y : G} (hy : y ∈ L) :
    Subgroup.centralizer (fsuV T I : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y : Subgroup G) : Set G) :=
  fun _ hc => SecD.mem_normalizer_inf (centralizer_le_normalizer_wH hV₁ hc)
    (centralizer_le_normalizer_conj_wH h hV₁ hy hc)

theorem qOf_le_pCoreOf_sup (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hQ : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) {y : G} (hy : y ∈ L) :
    qOf T I V₁ y ≤ pCoreOf 2 (L ⊔ T) := by
  have hWT : wH T I V₁ ≤ T :=
    (conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_T h hV₁)
  have hA : wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    (inf_le_inf_right _ hWT).trans (inf_centralizer_le_pCoreOf_sup h1102 h)
  refine sup_le hA ?_
  have hyO : y ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hy)
  rw [← conjSubgroup_centralizer_fsuV h hy, ← conjSubgroup_inf, ← conjSubgroup_eq_self hyO]
  exact conjSubgroup_mono hA y

theorem commutator_qOf_le (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    {y : G} (hy : y ∈ L) :
    ⁅qOf T I V₁ y, qOf T I V₁ y⁆ ≤ wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y := by
  have hWW := commutator_wH_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
  have hVN : fsuV T I ≤ wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y :=
    le_inf (le_conjClosure_self _ _) (fsuV_le_conj_wH h hy)
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hCN := centralizer_le_normalizer_inf h hV₁ hy
  have hAN : wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y : Subgroup G) : Set G) :=
    inf_le_right.trans hCN
  have hBN : conjSubgroup (wH T I V₁) y ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y : Subgroup G) : Set G) :=
    inf_le_right.trans hCN
  have hAA : ⁅wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G),
      wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G)⁆ ≤
      wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans (hWW.trans (hV₁V.trans hVN))
  have hBB : ⁅conjSubgroup (wH T I V₁) y ⊓ Subgroup.centralizer (fsuV T I : Set G),
      conjSubgroup (wH T I V₁) y ⊓ Subgroup.centralizer (fsuV T I : Set G)⁆ ≤
      wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y := by
    refine (Subgroup.commutator_mono inf_le_left inf_le_left).trans ?_
    rw [← conjSubgroup_commutator]
    refine (conjSubgroup_mono (hWW.trans hV₁V) y).trans ?_
    rw [conjSubgroup_eq_self (SecA.L_le_normalizer_fsuV h hy)]
    exact hVN
  have hAB : ⁅wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G),
      conjSubgroup (wH T I V₁) y ⊓ Subgroup.centralizer (fsuV T I : Set G)⁆ ≤
      wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y := by
    refine (commutator_le_inf_of_le_normalizer ?_ ?_).trans (inf_le_inf inf_le_left inf_le_left)
    · exact fun a ha => SecD.mem_normalizer_inf (centralizer_le_normalizer_conj_wH h hV₁ hy ha.2)
        (Subgroup.le_normalizer ha.2)
    · exact fun b hb => SecD.mem_normalizer_inf (centralizer_le_normalizer_wH hV₁ hb.2)
        (Subgroup.le_normalizer hb.2)
  have hBA := hAB
  rw [Subgroup.commutator_comm] at hBA
  have hAQ := commutator_sup_right_le hAN hBN hAA hAB
  have hBQ := commutator_sup_right_le hAN hBN hBA hBB
  rw [Subgroup.commutator_comm] at hAQ hBQ
  exact commutator_sup_right_le hAN hBN hAQ hBQ

theorem sq_mem_of_mem_qOf (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hV₁₃ : V₁ ≤ V₃) {y : G} (hy : y ∈ L) {x : G} (hx : x ∈ qOf T I V₁ y) :
    x ^ 2 ∈ wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y := by
  have hQQ := commutator_qOf_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk hy
  have hVN : fsuV T I ≤ wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y :=
    le_inf (le_conjClosure_self _ _) (fsuV_le_conj_wH h hy)
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  let S : Subgroup G :=
    { carrier := {x | x ∈ qOf T I V₁ y ∧ x ^ 2 ∈ wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have heq : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
          simp only [commutatorElement_def, sq]; group
        rw [heq]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha'
          (hQQ (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha) hb))) hb'
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow]; exact Subgroup.inv_mem _ ha'⟩ }
  have hAS : wH T I V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ S := fun a ha =>
    ⟨Subgroup.mem_sup_left ha, hVN (hV₁V (sq_mem_of_mem_wH hF h1102 h1103 h1113 h1141 h1143
      h1154 h1156 h hV₁ hV₂ hV₃ hk hV₁₃ ha.1))⟩
  have hBS : conjSubgroup (wH T I V₁) y ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ S := by
    intro b hb
    refine ⟨Subgroup.mem_sup_right hb, hVN ?_⟩
    have hb' : y * b * y⁻¹ ∈ wH T I V₁ := mem_conjSubgroup_iff.mp hb.1
    have h2 := sq_mem_of_mem_wH hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
      hV₁₃ hb'
    have heq : (y * b * y⁻¹) ^ 2 = y * b ^ 2 * y⁻¹ := by simp only [sq]; group
    rw [heq] at h2
    have h3 : b ^ 2 ∈ conjSubgroup (fsuV T I) y :=
      mem_conjSubgroup_iff.mpr (hV₁V h2)
    rwa [conjSubgroup_eq_self (SecA.L_le_normalizer_fsuV h hy)] at h3
  exact (sup_le hAS hBS hx).2

theorem frattini_le_of_le_qOf (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hV₁₃ : V₁ ≤ V₃) {y : G} (hy : y ∈ L) {P : Subgroup G} (hPQ : P ≤ qOf T I V₁ y)
    (hP : IsPGroup 2 P) :
    (frattini ↥P).map P.subtype ≤ wH T I V₁ ⊓ conjSubgroup (wH T I V₁) y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  have hQQ := commutator_qOf_le hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk hy
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | ⟨z, rfl⟩
  · have h1 : (_root_.commutator ↥P).map P.subtype = ⁅P, P⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h2 : (x : G) ∈ ⁅P, P⁆ := h1 ▸ Subgroup.mem_map_of_mem P.subtype hx
    exact hQQ (Subgroup.commutator_mono hPQ hPQ h2)
  · have h3 := sq_mem_of_mem_qOf hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk
      hV₁₃ hy (hPQ z.2)
    simpa using h3

end CFSG.Quasithin.Vol2.Ch11.SecF
