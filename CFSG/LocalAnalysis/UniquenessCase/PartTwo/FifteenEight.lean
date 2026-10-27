module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Eight_le_of_core (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hcore : ∀ g : G, conjSubgroup V g ≤ D.M →
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
        normalizer (wSub V₀ V hV L : Set G)) :
    E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V hV L : Set G) := by
  refine s15_Glue_wClos_zero_le hV (fun g hgM => ?_)
  have hspan := iSup_wConj_eq D h1217 h.hyp151 hV hL
  have hVg : conjSubgroup V g = ⨆ X ∈ wConj D.M V₀ V hV L, conjSubgroup X g := by
    have := congrArg (fun U => conjSubgroup U g) hspan
    simp only [conjSubgroup, Subgroup.map_iSup] at this
    exact this.symm
  rw [hVg]
  refine iSup₂_le fun X hX => ?_
  obtain ⟨m, hm, rfl⟩ := hX
  have hVm : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp151.hyp125.pairFacts.le_normalizer hm)
  have hVmg : conjSubgroup V (m * g) = conjSubgroup V g := by
    rw [← conjSubgroup_conjSubgroup, hVm]
  have hc := hcore (m * g) (hVmg ▸ hgM)
  rw [conjSubgroup_conjSubgroup]
  exact (E3.conjSubgroup_mono_left (m * g) le_sup_left).trans hc

theorem s15_Eight_not_le_conj (D : Data G) (h156 : R15_6 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G}
    (hgM : conjSubgroup V g ≤ D.M)
    (hB : ¬ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G)) :
    ¬ V ≤ conjSubgroup D.M g := by
  intro hVg
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ := h156 V₀ V L h hL g hVg hgM
  apply hB
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hBV : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hWV
  intro b hb
  have hbC : b ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : ⁅x, b⁆ ∈ ⁅V, conjSubgroup V g⁆ := Subgroup.commutator_mem_commutator hx (hBV hb)
    rw [hcomm] at h1
    have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by
      have := Subgroup.mem_bot.1 h1
      rwa [commutatorElement_def] at this
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [h2, one_mul]
  have hWV' : ((wSub V₀ V hV L : Subgroup G) : Set G) ⊆ (V : Set G) :=
    fun x hx => preTil_le V₀ V hV _ hx
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hWV' hbC)

theorem s15_Eight_fix_of_ne (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G} {B E : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hgM : conjSubgroup V g ≤ D.M) (hVg : ¬ V ≤ conjSubgroup D.M g) (hEB : E ≤ B)
    (hE1 : E3.mQuot B E = 1)
    (hs : ¬ (s15 D.M V₀ V hV L = 2 ∧
      delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1))
    {v : G} (hv : v ∈ V) (hfix : ∀ e ∈ E, e * v * e⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L) :
    ∀ b ∈ B, b * v * b⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L := by
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hγ := two_le_gamma15 D h151 hV hL
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h125 hV
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) hV1V
  have hBV : B ≤ conjSubgroup V g := hB ▸ E3.conjSubgroup_mono_left g hWV
  have hBM : B ≤ D.M := hBV.trans hgM
  have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
  have hV12 : IsPGroup 2 (v1Sub D.M V₀ V hV L) := hV.isPGroup.to_le hV1V
  have hBV0 : B ⊓ V = ⊥ := hB ▸ s15_Glue_inf_V_eq_bot D h hV hVg
  have horb := s15_Glue_orbit_mem_of_fix hV hV1V hv hfix
  have hvM : v ∈ conjSubgroup D.M g := by
    by_contra hvM
    have h0 := s15_Tools_inf_centralizer_eq_bot D h hV hB hvM
    have h1 := s15_Tools_mQuot_inf_centralizer_le_add hB2 hEB hV12 horb
    rw [h0, hE1] at h1
    have h2 := s15_FiveTen_mQuot_conj_bot D h125 hV (L := L) g
    rw [← hB] at h2
    omega
  have hcomm1 : ∀ e ∈ E, e * v * e⁻¹ * v⁻¹ = 1 := by
    intro e he
    by_contra hne1
    have hcV₁ : e * v * e⁻¹ * v⁻¹ ∈ v1Sub D.M V₀ V hV L := hfix e he
    have hvm : g * v * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hvM
    have heB : e ∈ B := hEB he
    have heA : g * e * g⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
      rw [hB] at heB
      exact mem_conjSubgroup_iff.1 heB
    have hy : g * v * g⁻¹ * (g * e * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ ∈
        conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * v * g⁻¹)⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have : (g * v * g⁻¹)⁻¹ * (g * v * g⁻¹ * (g * e * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹) *
          ((g * v * g⁻¹)⁻¹)⁻¹ = (g * e * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ heA
    have hV1m : conjSubgroup (v1Sub D.M V₀ V hV L) (g * v * g⁻¹)⁻¹ = v1Sub D.M V₀ V hV L :=
      conjSubgroup_eq_iff_mem_normalizer.mpr
        (Subgroup.inv_mem _ (s15_Infra_le_normalizer_v1Sub h125 hV hvm))
    have hsup : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * v * g⁻¹)⁻¹ =
        conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔ v1Sub D.M V₀ V hV L := by
      have h1 : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (g * v * g⁻¹)⁻¹ =
          conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔
            conjSubgroup (v1Sub D.M V₀ V hV L) (g * v * g⁻¹)⁻¹ := by
        simp only [conjSubgroup]
        exact Subgroup.map_sup _ _ _
      rw [h1, hV1m]
    have hyW : g * v * g⁻¹ * (g * e * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ ∈
        conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔ v1Sub D.M V₀ V hV L := hsup ▸ hy
    have hgc : g * (e * v * e⁻¹ * v⁻¹) * g⁻¹ = (g * e * g⁻¹) *
        (g * v * g⁻¹ * (g * e * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹) := by group
    by_cases hWm : conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ = wSub V₀ V hV L
    · have hc1 : g * (e * v * e⁻¹ * v⁻¹) * g⁻¹ ∈
          wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
        rw [hgc]
        refine Subgroup.mul_mem _ heA ?_
        rwa [hWm] at hyW
      have hcB : e * v * e⁻¹ * v⁻¹ ∈ B := by
        rw [hB]
        exact mem_conjSubgroup_iff.2 hc1
      have h2 : e * v * e⁻¹ * v⁻¹ ∈ B ⊓ V := Subgroup.mem_inf.2 ⟨hcB, hV1V hcV₁⟩
      rw [hBV0] at h2
      exact hne1 (Subgroup.mem_bot.1 h2)
    · have hginv : g⁻¹ ∉ D.M := by
        intro hginv
        apply hVg
        have hg : g ∈ D.M := by simpa using D.M.inv_mem hginv
        rw [s15_Tools_conjSubgroup_M D hg]
        exact h125.pairFacts.le_M
      have hthird := h.third g⁻¹ hginv (wSub V₀ V hV L)
        ⟨1, D.M.one_mem, (conjSubgroup_one _).symm⟩
        (conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹)
        ⟨(g * v * g⁻¹)⁻¹, D.M.inv_mem hvm, rfl⟩ (fun heq => hWm heq.symm) ?_
      · exact hs hthird
      · intro hbot
        have hmem : g * (e * v * e⁻¹ * v⁻¹) * g⁻¹ ∈
            (wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔
              v1Sub D.M V₀ V hV L) ⊓
              conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g⁻¹ := by
          refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
          · rw [hgc]
            refine Subgroup.mul_mem _ ?_ ?_
            · have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
                  wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔
                    v1Sub D.M V₀ V hV L :=
                sup_le (le_sup_left.trans le_sup_left) le_sup_right
              exact hle heA
            · have hle : conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔
                    v1Sub D.M V₀ V hV L ≤
                  wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) (g * v * g⁻¹)⁻¹ ⊔
                    v1Sub D.M V₀ V hV L :=
                sup_le (le_sup_right.trans le_sup_left) le_sup_right
              exact hle hyW
          · rw [mem_conjSubgroup_iff]
            have : g⁻¹ * (g * (e * v * e⁻¹ * v⁻¹) * g⁻¹) * (g⁻¹)⁻¹ = e * v * e⁻¹ * v⁻¹ := by
              group
            rw [this]
            exact Subgroup.mem_sup_right hcV₁
        rw [hbot] at hmem
        have h3 := Subgroup.mem_bot.1 hmem
        apply hne1
        have h4 : e * v * e⁻¹ * v⁻¹ = g⁻¹ * (g * (e * v * e⁻¹ * v⁻¹) * g⁻¹) * g := by group
        rw [h4, h3]
        group
  have hvC : v ∈ centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    calc e * v = (e * v * e⁻¹ * v⁻¹) * (v * e) := by group
      _ = v * e := by rw [hcomm1 e he, one_mul]
  have hlt : E3.mQuot B E < gamma15 D.M V₀ V hV L := by omega
  have hcen := (centralizer_le_normalizer_of_mQuot_lt D h hV hB hEB hlt).2
  have hvN : v ∈ normalizer (B : Set G) := (Subgroup.mem_inf.1 (hcen hvC)).2
  intro b hb
  have hbV : b ∈ normalizer (V : Set G) := h125.pairFacts.le_normalizer (hBM hb)
  have h1 : b * v * b⁻¹ * v⁻¹ ∈ B ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h2 := (Subgroup.mem_normalizer_iff.1 hvN b⁻¹).1 (B.inv_mem hb)
      have h3 : b * (v * b⁻¹ * v⁻¹) ∈ B := B.mul_mem hb h2
      simpa [mul_assoc] using h3
    · have h2 := (Subgroup.mem_normalizer_iff.1 hbV v).1 hv
      exact V.mul_mem h2 (V.inv_mem hv)
  rw [hBV0] at h1
  rw [Subgroup.mem_bot.1 h1]
  exact one_mem _

theorem s15_Eight_fix_of_s_two (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G} {B : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g)
    (hgM : conjSubgroup V g ≤ D.M) (hVg : ¬ V ≤ conjSubgroup D.M g)
    (hs : s15 D.M V₀ V hV L = 2 ∧ delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1)
    {w : G} (hw : w ∈ wSub V₀ V hV L)
    (hfix : ∀ e ∈ B ⊓ normalizer (wSub V₀ V hV L : Set G),
      e * w * e⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L) :
    ∀ b ∈ B, b * w * b⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L := by
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
  have hBV : B ≤ conjSubgroup V g := hB ▸ E3.conjSubgroup_mono_left g hWV
  have hBM : B ≤ D.M := hBV.trans hgM
  have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
  have hV12 : IsPGroup 2 ↥(v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) :=
    hV.isPGroup.to_le (inf_le_left.trans (s15_Infra_v1Sub_le h125 hV))
  have hBV0 : B ⊓ V = ⊥ := hB ▸ s15_Glue_inf_V_eq_bot D h hV hVg
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  have horb : ∀ e ∈ B ⊓ normalizer (wSub V₀ V hV L : Set G),
      w⁻¹ * (e⁻¹ * w * e) ∈ v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L := by
    intro e he
    have heN : e ∈ normalizer (wSub V₀ V hV L : Set G) := (Subgroup.mem_inf.1 he).2
    have h1 : e⁻¹ * w * (e⁻¹)⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L :=
      hfix e⁻¹ (Subgroup.inv_mem _ he)
    rw [inv_inv] at h1
    exact s15_Tools_orbit_mem D h125 hV (Subgroup.inv_mem _ heN) hw h1
  have hle := s15_Tools_mQuot_inf_centralizer_le_add hB2 inf_le_left hV12 horb
  have hm1 := s15_Glue_mQuot_inf_normalizer_le_one D h151 hV hBM hB2 hs.1
  have hδ : E3.mQuot (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ⊥ = delta15 D.M V₀ V hV L :=
    s15_FiveTen_mQuot_bot_eq_rk _
  have hlt : E3.mQuot B (B ⊓ centralizer ({w} : Set G)) < gamma15 D.M V₀ V hV L := by
    have := hs.2
    omega
  have hcen := (centralizer_le_normalizer_of_mQuot_lt D h hV hB
    (inf_le_left : B ⊓ centralizer ({w} : Set G) ≤ B) hlt).2
  have hwR : w ∈ centralizer ((B ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr).2
  have hwN : w ∈ normalizer (B : Set G) := (Subgroup.mem_inf.1 (hcen hwR)).2
  intro b hb
  have hbV : b ∈ normalizer (V : Set G) := h125.pairFacts.le_normalizer (hBM hb)
  have h1 : b * w * b⁻¹ * w⁻¹ ∈ B ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h2 := (Subgroup.mem_normalizer_iff.1 hwN b⁻¹).1 (B.inv_mem hb)
      have h3 : b * (w * b⁻¹ * w⁻¹) ∈ B := B.mul_mem hb h2
      simpa [mul_assoc] using h3
    · have h2 := (Subgroup.mem_normalizer_iff.1 hbV w).1 hwV
      exact V.mul_mem h2 (V.inv_mem hwV)
  rw [hBV0] at h1
  rw [Subgroup.mem_bot.1 h1]
  exact one_mem _

theorem s15_Eight_core (D : Data G) (h156 : R15_6 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G}
    (hgM : conjSubgroup V g ≤ D.M) :
    conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G) := by
  by_contra hB
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hVg := s15_Eight_not_le_conj D h156 h hV hL hgM hB
  set B := conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g with hBdef
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
  have hBV : B ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hWV
  have hBM : B ≤ D.M := hBV.trans hgM
  have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
  have hlt : B ⊓ normalizer (wSub V₀ V hV L : Set G) < B := by
    refine lt_of_le_of_ne inf_le_left fun heq => hB ?_
    calc B = B ⊓ normalizer (wSub V₀ V hV L : Set G) := heq.symm
      _ ≤ normalizer (wSub V₀ V hV L : Set G) := inf_le_right
  obtain ⟨E, hBE, hEB, hE1⟩ := s15_Glue_exists_hyperplane hB2 hlt
  have hEne : E ≠ B := by
    rintro rfl
    rw [E3.mQuot_self] at hE1
    exact absurd hE1 (by norm_num)
  obtain ⟨v, hvV, hEv, ⟨b, hb, hbv⟩, hvW⟩ :=
    fifteen_seven_G D h151 hV hL hBM hB2 hEB hBE hEne
  by_cases hcase : s15 D.M V₀ V hV L = 2 ∧
      delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1
  · have hEN : E ≤ normalizer (wSub V₀ V hV L : Set G) := by
      have hle := s15_Glue_mQuot_inf_normalizer_le_one D h151 hV hBM hB2 hcase.1
      have h1 := E3.mQuot_add (V := B) hBE hEB
      have h2 : E3.mQuot E (B ⊓ normalizer (wSub V₀ V hV L : Set G)) = 0 := by omega
      have h3 := (E3.mQuot_eq_zero_iff (hB2.to_le hEB) hBE).1 h2
      rw [← h3]
      exact inf_le_right
    exact hbv (s15_Eight_fix_of_s_two D h hV hL hBdef hgM hVg hcase (hvW hEN)
      (fun e he => hEv e (hBE he)) b hb)
  · exact hbv (s15_Eight_fix_of_ne D h hV hL hBdef hgM hVg hEB hE1 hcase hvV hEv b hb)

theorem fifteen_eight (D : Data G) (h1217 : R1217 D) (h156 : R15_6 D) : R15_8 D := by
  intro V₀ V L h hL
  exact s15_Eight_le_of_core D h1217 h h.hyp151.isElemAbelian hL
    (fun g hg => s15_Eight_core D h156 h h.hyp151.isElemAbelian hL hg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
