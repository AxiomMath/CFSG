module

public import Certificates.Certificate7108
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.Quasithin.Asc94
open CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Setup.X1
open scoped Pointwise

abbrev Hbar : Subgroup ↥NativeSporadic.M23 := Gbar ⊓ M2bar

abbrev IxBar : Subgroup ↥NativeSporadic.M23 :=
  quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22 ⊓ Gbar

abbrev F4bar : Subgroup ↥NativeSporadic.M23 :=
  fixingSubgroup ↥NativeSporadic.M23 (({16, 19, 21, 22} : Finset (Fin 23)) : Set (Fin 23))

theorem IxBar_le_Hbar : IxBar ≤ Hbar := by
  intro g hg
  obtain ⟨hq, hG⟩ := Subgroup.mem_inf.mp hg
  exact Subgroup.mem_inf.mpr ⟨hG, mem_stabilizer_heptad₀_of_mem_quadStab (by decide)
    (by decide) hq⟩

theorem exists_conj_of_hom_Hbar (hcard : Nat.card ↥Hbar ≤ 1920)
    (γ : ↥Hbar →* ↥NativeSporadic.M23) (hγinj : Function.Injective γ)
    (hγH : ∀ h, γ h ∈ Hbar) (hγL : ∀ h : ↥Hbar, (h : ↥NativeSporadic.M23) ∈ Lbar → γ h ∈ Lbar) :
    ∃ g ∈ Hbar, (g : Equiv.Perm (Fin 23)) 19 = 19 ∧
      ∀ i : ↥Hbar, (i : ↥NativeSporadic.M23) ∈ IxBar → γ i = g * i * g⁻¹ :=
  Certificates.certificate7108.1 hcard γ hγinj hγH hγL

theorem eq_refl_of_fix_F4bar
    (α : ↥Lbar ≃* ↥Lbar) (hα : ∀ f : ↥Lbar, (f : ↥NativeSporadic.M23) ∈ F4bar → α f = f) :
    α = MulEquiv.refl _ :=
  Certificates.certificate7108.2 (card_fix3 _ (by decide)) α hα

open CFSG.KC.Ord CFSG.KC.LQT.P in
theorem a7Count56_eq :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 7) =>
      Equiv.Perm.sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6).card = 60 := by
  have h7 : (7 : ℕ) ≤ 32 := by norm_num
  have h := cntP_eq h7 fun s => andB (even 7 s) (andB (Nat.beq (img s 5) 5) (Nat.beq (img s 6) 6))
  have hc : cntP 7 (fun s => andB (even 7 s) (andB (Nat.beq (img s 5) 5) (Nat.beq (img s 6) 6))) =
      60 := by
    decide +kernel
  have key : ∀ σ : Equiv.Perm (Fin 7), (Equiv.Perm.sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6) ↔
      andB (even 7 (code σ)) (andB (Nat.beq (img (code σ) 5) 5) (Nat.beq (img (code σ) 6) 6)) =
        true := by
    intro σ
    have e5 : img (code σ) 5 = ((σ 5 : Fin 7) : ℕ) := img_code h7 σ 5
    have e6 : img (code σ) 6 = ((σ 6 : Fin 7) : ℕ) := img_code h7 σ 6
    rw [andB_iff, andB_iff, even_code h7, beq_iff, beq_iff, e5, e6]
    exact ⟨fun ⟨a, b, c⟩ => ⟨a, congrArg Fin.val b, congrArg Fin.val c⟩,
      fun ⟨a, b, c⟩ => ⟨a, Fin.ext b, Fin.ext c⟩⟩
  rw [hc] at h
  rw [h]
  exact congrArg Finset.card (Finset.filter_congr fun σ _ => key σ)

end CFSG.Quasithin.H13
