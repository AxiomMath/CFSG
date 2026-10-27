module

public import CFSG.Quasithin.H13.L32A725b
public import CFSG.Quasithin.H13.L32A724c

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

theorem lemma14_7_25_case_ii (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    {W₁ W₂ : Subgroup G} (h : Case2 T L V H W₁ W₂) :
    ∃ D' : Subgroup G, D' ≤ oTwoUpper H ∧ (∀ x ∈ D', ∀ y ∈ oTwoUpper H, x * y = y * x) ∧
      Nat.card D' = 4 ∧ fsuV1 T V < D' ∧ H ≤ Subgroup.normalizer (D' : Set G) := by
  have SM := secMod_r C D
  have := SM.normal
  obtain ⟨ρ, hρ, hiso⟩ := Case2.isoMod_core_r C D h
  have hcLl : θ ⟨c, D.c_L⟩ ∈ Ll := (D.ll _).mpr D.c_N
  obtain ⟨e, ⟨l, hl, r₁, hr₁, r₂, hr₂, rfl⟩, heV, hfix⟩ :=
    SM.exists_core_fix hρ hiso hcLl D.theta_c3 D.theta_c
  have hlH : (l : G) ∈ H := mem_h_of_mem_normalizer C D ((D.ll l).mp hl)
  have hc'L1 : ((l * ⟨c, D.c_L⟩ * l⁻¹ : ↥L) : G) ∈ L32A.l1 T L V := by
    have := conj_mem_of_mem_normalizer (C.l1_normal hlH) D.c_mem
    simpa using this
  have hcomm : ∀ {x r : G}, x ∈ L32A.l1 T L V → r ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L →
      x * r * x⁻¹ * r⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓
        pCoreOf 2 (oTwoUpper H) ⊓ W₁ := by
    intro x r hx hr
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem
      (conj_mem_of_mem_normalizer (le_normalizer_r (l1_le_l D hx)) hr) (inv_mem hr),
      (Subgroup.mem_inf.mp (comm_mem_p_of_mem_l1 C D hx (r_le_s C D hr))).2⟩, ?_⟩
    have h1 := h.comm₁ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_inf.mpr ⟨s_le_h C D (r_le_s C D hr), r_le_centralizer_u C hr⟩) (l1_le_k C hx))
    rw [commutatorElement_def] at h1
    have e : x * r * x⁻¹ * r⁻¹ = (r * x * r⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have h1 : c * r₁ * c⁻¹ * r₁⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓
      pCoreOf 2 (oTwoUpper H) ⊓ W₁ := hcomm D.c_mem hr₁
  have h2 := hcomm hc'L1 hr₂
  set e := ((⟨c, D.c_L⟩ : ↥L) : G) * r₁ * ((⟨c, D.c_L⟩ : ↥L) : G)⁻¹ * r₁⁻¹ *
    (((l * ⟨c, D.c_L⟩ * l⁻¹ : ↥L) : G) * r₂ * ((l * ⟨c, D.c_L⟩ * l⁻¹ : ↥L) : G)⁻¹ * r₂⁻¹) with he
  have heRPW : e ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ⊓ pCoreOf 2 (oTwoUpper H) ⊓ W₁ :=
    mul_mem h1 h2
  have heR := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp heRPW).1).1
  have heP := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp heRPW).1).2
  have heW₁ := (Subgroup.mem_inf.mp heRPW).2
  have hL1e : ∀ x ∈ L32A.l1 T L V, x * e * x⁻¹ * e⁻¹ ∈ V := fun x hx =>
    hfix ⟨x, l1_le_l D hx⟩ ((D.ll _).mpr (D.l1_le hx).2)
  have heW₂ : e ∈ W₂ := Case2.fpf_l1 C D h e heW₁ fun x hx =>
    h.u_le (le_conjClosure V _ (hL1e x hx))
  have heU : e ∉ fsuU T V := by
    intro heU
    have heE : e ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
      rw [← u_inf_r C D]
      exact Subgroup.mem_inf.mpr ⟨heU, heR⟩
    exact heV (C.fpf_e e heE hL1e)
  have hKe : ∀ y ∈ oTwoUpper H, y * e * y⁻¹ * e⁻¹ ∈ fsuU T V := by
    intro y hy
    have h3 := h.comm₂ (Subgroup.commutator_mem_commutator heW₂ hy)
    rw [commutatorElement_def] at h3
    have e3 : y * e * y⁻¹ * e⁻¹ = (e * y * e⁻¹ * y⁻¹)⁻¹ := by group
    rw [e3]
    exact inv_mem h3
  have hPe : ∀ x ∈ pCoreOf 2 (oTwoUpper H),
      x * e * x⁻¹ * e⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := fun x hx =>
    C.v_le_e (hL1e x (p_le_l1 C hx))
  obtain ⟨d, hdP, hdV, hdK⟩ := exists_central C D heP heU hKe hPe
  exact exists_d C D hdP hdV hdK

theorem lemma14_7_25_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G) (γ γ' : F8.Geom T L H)
      (g k : ↥((L ⊔ T) ⊔ H)), Ctx722 G T L V H γ γ' g k →
      ∃ D : Subgroup G, D ≤ oTwoUpper H ∧ (∀ d ∈ D, ∀ x ∈ oTwoUpper H, d * x = x * d) ∧
        Nat.card D = 4 ∧ fsuV1 T V < D ∧ H ≤ Subgroup.normalizer (D : Set G) := by
  intro G _ _ T L V H γ γ' g k C
  obtain ⟨θ, c, D⟩ := exists_data h1222 h1332 h1334 C.setting
  rcases C.cases_720 with hi | ⟨W₁, W₂, hUW, hW, hWP, hn₁, hn₂, hidx, helem, hirr, hfaith, hc₂,
    hc₁⟩
  · exact lemma14_7_25_case_i C D hi
  · exact lemma14_7_25_case_ii C D ⟨hUW, hW, hWP, hn₁, hn₂, hidx, helem, hirr, hfaith, hc₂, hc₁⟩

end CFSG.Quasithin.H13.S4
