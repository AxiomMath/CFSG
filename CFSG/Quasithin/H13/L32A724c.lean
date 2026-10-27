module

public import CFSG.Quasithin.H13.L32A724b
public import CFSG.Quasithin.H13.L32AS4e

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

theorem lemma14_7_25_case_i (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c)
    (hi : ⁅H ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper H⁆ ≤ fsuU T V) :
    ∃ D' : Subgroup G, D' ≤ oTwoUpper H ∧ (∀ x ∈ D', ∀ y ∈ oTwoUpper H, x * y = y * x) ∧
      Nat.card D' = 4 ∧ fsuV1 T V < D' ∧ H ≤ Subgroup.normalizer (D' : Set G) := by
  have SM := secMod_s C D
  haveI := SM.normal
  obtain ⟨ρ, hρ, hiso⟩ := isoMod_core_s C D hi
  have hcLl : θ ⟨c, D.c_L⟩ ∈ Ll := (D.ll _).mpr D.c_N
  obtain ⟨e, ⟨l, hl, s₁, hs₁, s₂, hs₂, rfl⟩, heR, hfix⟩ :=
    SM.exists_core_fix hρ hiso hcLl D.theta_c3 D.theta_c
  have hlH : (l : G) ∈ H := mem_h_of_mem_normalizer C D ((D.ll l).mp hl)
  have hc'L1 : ((l * ⟨c, D.c_L⟩ * l⁻¹ : ↥L) : G) ∈ L32A.l1 T L V := by
    have := conj_mem_of_mem_normalizer (C.l1_normal hlH) D.c_mem
    simpa using this
  have h1 : c * s₁ * c⁻¹ * s₁⁻¹ ∈ L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) :=
    comm_mem_p_of_mem_l1 C D D.c_mem hs₁
  have h2 := comm_mem_p_of_mem_l1 C D hc'L1 hs₂
  set e := ((⟨c, D.c_L⟩ : ↥L) : G) * s₁ * ((⟨c, D.c_L⟩ : ↥L) : G)⁻¹ * s₁⁻¹ *
    (((l * ⟨c, D.c_L⟩ * l⁻¹ : ↥L) : G) * s₂ * ((l * ⟨c, D.c_L⟩ * l⁻¹ : ↥L) : G)⁻¹ * s₂⁻¹) with he
  have heSP : e ∈ L32A.sL T L V ⊓ pCoreOf 2 (oTwoUpper H) := mul_mem h1 h2
  have heP : e ∈ pCoreOf 2 (oTwoUpper H) := (Subgroup.mem_inf.mp heSP).2
  have heH : e ∈ H := (pCoreOf_le 2 _).trans (oTwoUpper_le H) heP
  have hce : c * e * c⁻¹ * e⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    hfix ⟨c, D.c_L⟩ hcLl
  have heC : e ∈ Subgroup.centralizer (fsuU T V : Set G) :=
    fpf_pc C D heP (r_le_centralizer_u C hce)
  have heU : e ∉ fsuU T V := by
    intro heU
    have h3 : c * e * c⁻¹ * e⁻¹ ∈ fsuU T V ⊓ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
      Subgroup.mem_inf.mpr ⟨mul_mem (conj_c_mem_u C D heU) (inv_mem heU), hce⟩
    rw [u_inf_r C D] at h3
    exact heR (le_conjClosure _ L (fpf_ue C D heU h3))
  have hKe : ∀ y ∈ oTwoUpper H, y * e * y⁻¹ * e⁻¹ ∈ fsuU T V := by
    intro y hy
    have h3 := hi (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨heH, heC⟩) hy)
    rw [commutatorElement_def] at h3
    have e3 : y * e * y⁻¹ * e⁻¹ = (e * y * e⁻¹ * y⁻¹)⁻¹ := by group
    rw [e3]
    exact inv_mem h3
  have hPe : ∀ x ∈ pCoreOf 2 (oTwoUpper H),
      x * e * x⁻¹ * e⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
    intro x hx
    have hxL1 := p_le_l1 C hx
    have h3 : x * e * x⁻¹ * e⁻¹ ∈ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
      hfix ⟨x, l1_le_l D hxL1⟩ ((D.ll _).mpr (D.l1_le hxL1).2)
    rw [← u_inf_r C D]
    exact Subgroup.mem_inf.mpr ⟨hKe x (pCoreOf_le 2 _ hx), h3⟩
  obtain ⟨d, hdP, hdV, hdK⟩ := exists_central C D heP heU hKe hPe
  exact exists_d C D hdP hdV hdK

end CFSG.Quasithin.H13.S4
