module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42PData

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private theorem he42wl_side {L K A J : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hP : PData L K A J ψ) (h3 : ¬ 3 ∣ Nat.card A) {y y₀ : G}
    (hyL : y ∈ normalizer (L : Set G)) (hyK : y ∈ normalizer (K : Set G)) (hy3 : y ^ 3 = 1)
    (hyJ : ∀ j ∈ J, y * j * y⁻¹ * j⁻¹ ∈ A) (hf : ∀ a ∈ A, a * y = y * a → a = 1)
    (hyC : Commute y y₀) (hy₀K : y₀ ∈ K) (hy₀J : y₀ ∉ J) (hy₀3 : orderOf y₀ = 3) :
    (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ A) ∧
      ∃ l : G, l ∈ L ∧ l * y = y * l ∧ l * l = 1 ∧ l ∉ K ∧ l * y₀ * l⁻¹ = y₀⁻¹ := by
  have hcomm : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ A := PData.comm_of_klein hP hyL hyK hy3 hyJ
  refine ⟨hcomm, ?_⟩
  have hcompl := PData.exists_mul_centralizer hP hyL hy3 hcomm h3
  have hAy : A ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haA, hac⟩ := Subgroup.mem_inf.mp ha
    exact hf a haA (Subgroup.mem_centralizer_singleton_iff.mp hac)
  have hy₀C : y₀ ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyC.symm.eq
  have hy₀ : y₀ ∈ L ⊓ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hP.KL hy₀K, hy₀C⟩
  obtain ⟨l, hl, hl2, hlK, hlinv⟩ :=
    PData.exists_inverting hP hcompl hAy hy₀ hy₀K (fun h => hy₀J (hP.AJ h)) hy₀3
  exact ⟨l, (Subgroup.mem_inf.mp hl).1,
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hl).2, hl2, hlK, hlinv⟩

theorem HeSetup.exists_wspec (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) {y₁ y₂ : G}
    (hY : YSpec S y₁ y₂) (hn : S.StepYnorm y₁ y₂) (hf : S.StepYfpf y₁ y₂)
    (h0 : S.StepY0 y₁ y₂) :
    S.StepComm y₁ y₂ ∧ ∃ l₁ l₂ : G, WSpec S y₁ y₂ l₁ l₂ := by
  obtain ⟨⟨ψ₁, hP₁⟩, ⟨ψ₂, hP₂⟩⟩ := hP
  have hy₁3 : y₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₁
    rwa [hY.ord₁] at h
  have hy₂3 : y₂ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₂
    rwa [hY.ord₂] at h
  have hc12 : Commute y₁ y₂ := hY.comm
  have hc0₁ : Commute y₁ (y₁ * y₂⁻¹) := (Commute.refl y₁).mul_right hc12.inv_right
  have hc0₂ : Commute y₂ (y₁ * y₂⁻¹) := hc12.symm.mul_right (Commute.refl y₂).inv_right
  obtain ⟨hcomm₁, l₁, hl₁, hl₁y, hl₁2, hl₁K, hl₁inv⟩ :=
    he42wl_side hP₁ (by rw [hB.card_A]; omega) hn.1.1 hn.1.2.1 hy₁3 hn.1.2.2 hf.1 hc0₁
      h0.1 h0.2.1 h0.2.2
  obtain ⟨hcomm₂, l₂, hl₂, hl₂y, hl₂2, hl₂K, hl₂inv⟩ :=
    he42wl_side hP₂ (by rw [hB.card_A']; omega) hn.2.1 hn.2.2.1 hy₂3 hn.2.2.2 hf.2 hc0₂
      h0.1 h0.2.1 h0.2.2
  exact ⟨And.intro hcomm₁ hcomm₂, l₁, l₂,
    ⟨hl₁, hl₂, hl₁2, hl₂2, hl₁K, hl₂K, hl₁y, hl₂y, hl₁inv, hl₂inv⟩⟩

end CFSG.Quasithin.A94.He42
