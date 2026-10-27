module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4e
public import CFSG.Quasithin.H13.GoldschmidtM22EndN4a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include hk P h hZ in
theorem exists_mul_of_mem_centralizer_V (h621 : Stmt6_2_1) (h629 : Stmt6_2_9)
    (h6110 : Stmt6_1_10) (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) {q : G}
    (hq : q ∈ Subgroup.centralizer (V : Set G)) :
    ∃ v ∈ V, ∃ c ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V, q = v * c := by
  have key : ∀ q' ∈ Subgroup.centralizer (V : Set G) ⊓ CHU T L V,
      ∃ v ∈ V, ∃ c ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V, q' = v * c := by
    intro q' hq'
    obtain ⟨hq'C, hq'CHU⟩ := Subgroup.mem_inf.mp hq'
    have hR := hk.inf_le_centralizerMod h hZ h621 h6211 hq'
    obtain ⟨d, hdD, hdc⟩ := hk.exists_mul_of_mem_centralizerMod hR
    have hdCHU : d ∈ CHU T L V := hk.D_le_CHU hdD
    have hcCHU : d⁻¹ * q' ∈ CHU T L V := (CHU T L V).mul_mem ((CHU T L V).inv_mem hdCHU) hq'CHU
    have hcV : d⁻¹ * q' ∈ Subgroup.centralizer (V : Set G) :=
      hk.centralizer_inf_CHU_le_centralizer_V h h6110 h6211 h6212 ⟨hdc, hcCHU⟩
    have hdV : d ∈ Subgroup.centralizer (V : Set G) := by
      have : d = q' * (d⁻¹ * q')⁻¹ := by group
      rw [this]
      exact (Subgroup.centralizer (V : Set G)).mul_mem hq'C
        ((Subgroup.centralizer (V : Set G)).inv_mem hcV)
    have hd0 : d ∈ V ⊓ CHU T L V := hk.D_inf_centralizer_le h P hZ h6210 h6211 ⟨hdD, hdV⟩
    exact ⟨d, (Subgroup.mem_inf.mp hd0).1, d⁻¹ * q', ⟨hdc, hcCHU⟩, by group⟩
  have hqT : q ∈ T := P.centralizer_le_T h hZ h621 h629 h6210 h6212 hq
  have hqH : q ∈ HH T := T_le_HH T hqT
  by_cases hqCHU : q ∈ CHU T L V
  · exact key q ⟨hq, hqCHU⟩
  · obtain ⟨a, haV, haC⟩ := PsiData.exists_a h hZ h6210
    have h1 := P.psi_eq_of_mem_M h h629 a haV haC ⟨q, hqH⟩ (h.T_le hqT)
    have hψ : P.ψ ⟨q, hqH⟩ = P.ψ a := by
      rcases h1 with h1 | h1
      · exact absurd ((P.ker _).mp h1) hqCHU
      · exact h1
    have haq : (a : G)⁻¹ * q ∈ CHU T L V := by
      have : P.ψ (a⁻¹ * ⟨q, hqH⟩) = 1 := by rw [map_mul, map_inv, hψ, inv_mul_cancel]
      exact (P.ker _).mp this
    have haC' : (a : G) ∈ Subgroup.centralizer (V : Set G) := V_le_centralizer_V h haV
    have hq'' : (a : G)⁻¹ * q ∈ Subgroup.centralizer (V : Set G) ⊓ CHU T L V :=
      ⟨(Subgroup.centralizer (V : Set G)).mul_mem ((Subgroup.centralizer (V : Set G)).inv_mem haC')
        hq, haq⟩
    obtain ⟨v, hv, c, hc, hvc⟩ := key _ hq''
    refine ⟨(a : G) * v, V.mul_mem haV hv, c, hc, ?_⟩
    rw [mul_assoc, ← hvc]
    group

include h in
theorem centralizer_V0_le_normalizer_V (h6110 : Stmt6_1_10) (h6211 : Stmt6_2_11) :
    Subgroup.centralizer ((V ⊓ CHU T L V : Subgroup G) : Set G) ≤
      Subgroup.normalizer (V : Set G) := by
  by_contra hC
  have hr : ((2 : ℕ) : ℕ∞) ≤ rParam V := (h6110 G T M L V 2 h.toHyp611Nat).1
  have hle := rParam_le_mQuot (inf_le_left : V ⊓ CHU T L V ≤ V) hC
  have hm : mQuot V (V ⊓ CHU T L V) = 1 := by
    unfold mQuot
    rw [relIndex_V_CHU h h6211]
    simp
  rw [hm] at hle
  have := hr.trans hle
  norm_num at this

include hk P h hZ in
theorem centralizer_inf_HH_le_CHU (h621 : Stmt6_2_1) (h629 : Stmt6_2_9) (h6110 : Stmt6_1_10)
    (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) :
    Subgroup.centralizer (D : Set G) ⊓ HH T ≤ CHU T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCHU : CHU T L V = pCoreOf 2 (HH T) := (h6212 G T M L V h).2.2
  have hle : Subgroup.centralizer (D : Set G) ⊓ HH T ≤ T := by
    intro x hx
    obtain ⟨hxD, hxH⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
      centralizer_V0_le_normalizer_V h h6110 h6211 (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hxD y (hk.V0_le_D hy))
    have : x ∈ HH T ⊓ M := ⟨hxH, (h621 G T M L V h).2 hxN⟩
    rwa [P.HH_inf_M_eq_T h hZ h629 h6210 h6212] at this
  have hnorm : HH T ≤ Subgroup.normalizer ((Subgroup.centralizer (D : Set G) ⊓ HH T :
      Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : y ∈ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer,
        CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
        conjSubgroup_eq_iff_mem_normalizer.mpr (hk.H_le_normalizer_D hy)]
    have h2 := Subgroup.mem_normalizer_iff.mp h1 x
    simp only [Subgroup.mem_inf]
    have h3 : x ∈ HH T ↔ y * x * y⁻¹ ∈ HH T := by
      constructor
      · intro hx
        exact (HH T).mul_mem ((HH T).mul_mem hy hx) ((HH T).inv_mem hy)
      · intro hx
        have := (HH T).mul_mem ((HH T).mul_mem ((HH T).inv_mem hy) hx) hy
        simpa [mul_assoc] using this
    rw [h2, h3]
  rw [hCHU]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
    (h.sylow.1.to_le hle)

end KData

end CFSG.Quasithin.H13.GM22
