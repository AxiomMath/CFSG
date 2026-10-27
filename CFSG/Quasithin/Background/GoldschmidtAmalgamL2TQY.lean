module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TQA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped Pointwise

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section QY

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

omit [Finite D] g in
theorem conjSub_K_le_yGrp {y : D} (hy : y ∈ A) : conjSub y (kerK B V) ≤ yGrp A B V := by
  intro u hu
  have hk : y⁻¹ * u * y ∈ kerK B V := mem_conjSub.mp hu
  have h1 := mem_conjClosure (Z := kerK B V) (H := A) hy hk
  have e : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
  rwa [e] at h1

theorem card_kerK_sup_conj {y : D} (hyA : y ∈ A) (hyT : y ∉ A ⊓ B) :
    Nat.card ↥(kerK B V ⊔ conjSub y (kerK B V)) = 16 := by
  have hint : kerK B V ⊓ conjSub y (kerK B V) = ⊥ := g.hyp.K_inf_conj_eq_bot hyA hyT
  have h1 := card_sup_mul_card_inf_of_commute' (g.hyp.kerK_comm_conjSub hyA hyT)
  rw [hint, Subgroup.card_bot, card_conjSub, g.hyp.card_kerK] at h1
  omega

theorem yGrp_eq_sup (hT : Nat.card ↥(A ⊓ B) = 64) {y : D} (hyA : y ∈ A) (hyT : y ∉ A ⊓ B) :
    yGrp A B V = kerK B V ⊔ conjSub y (kerK B V) ∧ Nat.card ↥(yGrp A B V) = 16 := by
  have hY₀ : kerK B V ⊔ conjSub y (kerK B V) ≤ yGrp A B V :=
    sup_le K_le_yGrp (conjSub_K_le_yGrp hyA)
  have hc₀ := card_kerK_sup_conj g hyA hyT
  have hQ := card_QA_of_card_T g hT
  have hYQ := yGrp_le_QA g
  have hlow : 16 ≤ Nat.card ↥(yGrp A B V) := hc₀ ▸ Subgroup.card_le_of_le hY₀
  have hdvd : Nat.card ↥(yGrp A B V) ∣ 32 := hQ ▸ Subgroup.card_dvd_of_le hYQ
  have hne : Nat.card ↥(yGrp A B V) ≠ 32 := fun h32 =>
    yGrp_ne_QA g hT (Subgroup.eq_of_le_of_card_ge hYQ (by rw [hQ, h32]))
  have hcard : Nat.card ↥(yGrp A B V) = 16 := by
    have hle : Nat.card ↥(yGrp A B V) ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(yGrp A B V) = m at *
    interval_cases m <;> omega
  exact ⟨(Subgroup.eq_of_le_of_card_ge hY₀ (by rw [hcard, hc₀])).symm, hcard⟩

theorem zpowers_z_le_K : Subgroup.zpowers z ≤ kerK B V :=
  Subgroup.zpowers_le.mpr (g.hyp.center_U_le_K g.hyp.z_mem_center_U)

theorem V_le_yGrp : V ≤ yGrp A B V := by
  refine g.hyp.natural.V_eq.le.trans ?_
  refine conjClosure_le fun a' ha' z' hz' => ?_
  have hz'Y : z' ∈ yGrp A B V := K_le_yGrp (zpowers_z_le_K g hz')
  exact (Subgroup.mem_normalizer_iff.mp (A_le_normalizer_yGrp ha') z').mp hz'Y

theorem centralizer_yGrp_le :
    A ⊓ Subgroup.centralizer (yGrp A B V : Set D) ≤ pCoreOf 2 A := by
  rw [← g.hyp.natural.centralizer_eq]
  exact inf_le_inf_left A (Subgroup.centralizer_le (V_le_yGrp g))

theorem yGrp_inf_QB_le_U (hT : Nat.card ↥(A ⊓ B) = 64) :
    yGrp A B V ⊓ pCoreOf 2 B ≤ conjClosure V B := by
  intro u hu
  rw [U_eq_centralizer g hT]
  refine ⟨hu.2, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_⟩
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  exact yGrp_comm g (c_mem_yGrp g) hu.1

theorem card_yGrp_inf_U (hT : Nat.card ↥(A ⊓ B) = 64) :
    Nat.card ↥(yGrp A B V ⊓ conjClosure V B) = 8 ∧
      yGrp A B V ⊓ conjClosure V B = conjClosure V B ⊓ pCoreOf 2 A := by
  obtain ⟨y, hyA, hyT⟩ := g.hyp.exists_y
  have hY := (yGrp_eq_sup g hT hyA hyT).2
  have hR : Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) = 16 := card_R_of_card_T g hT
  have hQ : Nat.card ↥(pCoreOf 2 A) = 32 := card_QA_of_card_T g hT
  have hYQ : yGrp A B V ≤ pCoreOf 2 A := yGrp_le_QA g
  have hRnorm : (pCoreOf 2 A ⊓ pCoreOf 2 B) ≤ Subgroup.normalizer (yGrp A B V : Set D) :=
    inf_le_left.trans ((g.hyp.QA_le_T.trans inf_le_left).trans A_le_normalizer_yGrp)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hRnorm
  have hRY : Nat.card ↥((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ yGrp A B V) ≤ 32 :=
    hQ ▸ Subgroup.card_le_of_le (sup_le inf_le_left hYQ)
  rw [hR, hY] at h1
  have hlow : 8 ≤ Nat.card ↥((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊓ yGrp A B V) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊔ yGrp A B V) *
        Nat.card ↥((pCoreOf 2 A ⊓ pCoreOf 2 B) ⊓ yGrp A B V) ≤ 32 * 7 :=
      Nat.mul_le_mul hRY (by omega)
    omega
  have hsub : (pCoreOf 2 A ⊓ pCoreOf 2 B) ⊓ yGrp A B V ≤ yGrp A B V ⊓ conjClosure V B :=
    fun u hu => ⟨hu.2, yGrp_inf_QB_le_U g hT ⟨hu.2, hu.1.2⟩⟩
  have hge : 8 ≤ Nat.card ↥(yGrp A B V ⊓ conjClosure V B) :=
    hlow.trans (Subgroup.card_le_of_le hsub)
  have hle : yGrp A B V ⊓ conjClosure V B ≤ conjClosure V B ⊓ pCoreOf 2 A :=
    fun u hu => ⟨hu.2, hYQ hu.1⟩
  have hup := card_U_inf_QA_le g
  have hle' := Subgroup.card_le_of_le hle
  exact ⟨le_antisymm (hle'.trans hup) hge, Subgroup.eq_of_le_of_card_ge hle (by omega)⟩

end QY

end GoldAmL2T

end F6

end CFSG.Quasithin
