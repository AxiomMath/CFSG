module

public import CFSG.Quasithin.EmptyFaithful.S153PA1b

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace S153P

namespace PA1

section EFacts

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem conj_Eg_of_cent {c e : G} (hc : c ∈ Subgroup.centralizer (V0g Z y : Set G))
    (he : e ∈ Eg U Mc y) : c * e * c⁻¹ ∈ Eg U Mc y := by
  rw [mem_Eg_iff A] at he ⊢
  exact ⟨A.U_norm c (cent_mem_Mc A hc) e he.1, conjMc_conj_U' A (cent_mem_conjMc A hc) he.2⟩

theorem comm_Eg_J : ∀ e ∈ Eg U Mc y, ∀ j ∈ Jg U y, ⁅e, j⁆ ∈ V0g Z y := by
  let S : Subgroup G :=
    { carrier := {j | j ∈ Subgroup.normalizer (V0g Z y : Set G) ∧
        ∀ e ∈ Eg U Mc y, ⁅e, j⁆ ∈ V0g Z y}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun e he => ?_⟩
        have h1 : ⁅e, a * b⁆ = ⁅e, a⁆ * (a * ⁅e, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact mul_mem (ha' e he) ((Subgroup.mem_normalizer_iff.mp ha _).mp (hb' e he))
      one_mem' := ⟨one_mem _, fun e he => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun e he => ?_⟩
        have h1 : ⁅e, a⁻¹⁆ = a⁻¹ * ⁅e, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff''.mp ha _).mp (inv_mem (ha' e he)) }
  have hU : U ≤ S := fun u hu =>
    ⟨U_le_normV0 A hu, fun e he =>
      Subgroup.mem_sup_left (A.U_comm e ((mem_Eg_iff A).mp he).1 u hu)⟩
  have hU' : conjSubgroup U y ≤ S := fun u hu =>
    ⟨U'_le_normV0 A hu, fun e he =>
      Subgroup.mem_sup_right (U'_comm A ((mem_Eg_iff A).mp he).2 hu)⟩
  have hJ : Jg U y ≤ S := sup_le hU hU'
  exact fun e he j hj => (hJ hj).2 e he

end EFacts

end PA1

namespace Abs56

variable {G : Type} [Group G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

theorem E_comm : ⁅Eg U Mc y, Jg U y⁆ ≤ V0g Z y :=
  Subgroup.commutator_le.mpr (PA1.comm_Eg_J A)

theorem E_normal : ∀ j ∈ Jg U y, ∀ e ∈ Eg U Mc y, j * e * j⁻¹ ∈ Eg U Mc y := by
  intro j hj e he
  have h1 : ⁅e, j⁆ ∈ V0g Z y := PA1.comm_Eg_J A e he j hj
  have h2 : ⁅j, e⁆ ∈ V0g Z y := by
    rw [← commutatorElement_inv]; exact inv_mem h1
  have h3 : ⁅j, e⁆ ∈ Eg U Mc y := PA1.V0_le_Eg A h2
  have eq : j * e * j⁻¹ = ⁅j, e⁆ * e := by simp only [commutatorElement_def]; group
  rw [eq]
  exact mul_mem h3 he

theorem cent_normalizes_E : ∀ c ∈ Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G),
    c ∈ Subgroup.normalizer ((Eg U Mc y : Subgroup G) : Set G) := by
  intro c hc
  exact PA1.mem_normalizer_of_conj (fun v hv => PA1.conj_Eg_of_cent A hc hv)
    (fun v hv => by simpa using PA1.conj_Eg_of_cent A (inv_mem hc) hv)

theorem N_abel : ∀ a ∈ Ng U Mc y, ∀ b ∈ Ng U Mc y, ⁅a, b⁆ ∈ Eg U Mc y := by
  have hEn : ∀ f ∈ Fg U Mc y, ∀ e ∈ Eg U Mc y, f * e * f⁻¹ ∈ Eg U Mc y := fun f hf e he =>
    E_normal A f (Subgroup.mem_sup_left ((PA1.mem_Fg_iff A).mp hf).1) e he
  have hFF : ∀ f ∈ Fg U Mc y, ∀ f' ∈ Fg U Mc y, ⁅f, f'⁆ ∈ Eg U Mc y := fun f hf f' hf' =>
    PA1.Z_le_Eg A (A.U_comm f ((PA1.mem_Fg_iff A).mp hf).1 f' ((PA1.mem_Fg_iff A).mp hf').1)
  have hXX : ∀ x ∈ Xg U Mc y, ∀ x' ∈ Xg U Mc y, ⁅x, x'⁆ ∈ Eg U Mc y := fun x hx x' hx' =>
    PA1.conjZ_le_Eg A
      (PA1.U'_comm A ((PA1.mem_Xg_iff A).mp hx).1 ((PA1.mem_Xg_iff A).mp hx').1)
  have hXF : ∀ x ∈ Xg U Mc y, ∀ f ∈ Fg U Mc y, ⁅x, f⁆ ∈ Eg U Mc y := fun x hx f hf => by
    rw [← commutatorElement_inv]; exact inv_mem (PA1.K3 A hf hx)
  have hA : ∀ b : G, (∀ f ∈ Fg U Mc y, ⁅f, b⁆ ∈ Eg U Mc y) →
      (∀ x ∈ Xg U Mc y, ⁅x, b⁆ ∈ Eg U Mc y) → ∀ a ∈ Ng U Mc y, ⁅a, b⁆ ∈ Eg U Mc y := by
    intro b hF hX a ha
    obtain ⟨f, hf, x, hx, rfl⟩ := N_prod A a ha
    have e : ⁅f * x, b⁆ = f * ⁅x, b⁆ * f⁻¹ * ⁅f, b⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hEn f hf _ (hX x hx)) (hF f hf)
  intro a ha b hb
  obtain ⟨f, hf, x, hx, rfl⟩ := N_prod A b hb
  have hAF : ⁅a, f⁆ ∈ Eg U Mc y :=
    hA f (fun f' hf' => hFF f' hf' f hf) (fun x' hx' => hXF x' hx' f hf) a ha
  have hAX : ⁅a, x⁆ ∈ Eg U Mc y :=
    hA x (fun f' hf' => PA1.K3 A hf' hx) (fun x' hx' => hXX x' hx' x hx) a ha
  have e : ⁅a, f * x⁆ = ⁅a, f⁆ * (f * ⁅a, x⁆ * f⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem hAF (hEn f hf _ hAX)

end Abs56

end S153P

end CFSG.Quasithin
