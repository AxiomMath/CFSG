module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OffenderB10
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_mem_sup {A C : Subgroup G} (h : ∀ c ∈ C, ∀ a ∈ A, a * c = c * a) {x : G}
    (hx : x ∈ A ⊔ C) : ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  rw [← EmptyFaithful.Stellmacher.OrdinaryProofs.range_prodMulHom h] at hx
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p.1, p.1.2, p.2, p.2.2,
    EmptyFaithful.Stellmacher.OrdinaryProofs.prodMulHom_apply h p⟩

omit [Finite G] in
theorem swap_comm_mem {A B B' : Subgroup G} {q : G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB' : ∀ a ∈ A, ∀ b ∈ B', a * b = b * a)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hR1 : A ⊓ B ≤ B') (hR2 : B ⊓ B' ≤ A) (hBe : B ≤ A ⊔ B') (hB'e : B' ≤ A ⊔ B)
    (hqA : ∀ a ∈ A, q * a * q⁻¹ ∈ A) (hz : ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ A ⊓ B)
    (hqB : ∀ y ∈ B, q * y * q⁻¹ ∈ B') (hqB' : ∀ y ∈ B', q * y * q⁻¹ ∈ B) :
    ∀ y ∈ B, q * y * q⁻¹ * y⁻¹ ∈ A := by
  intro y hy
  obtain ⟨a₁, ha₁, y₁, hy₁, e1⟩ :=
    exists_mul_of_mem_sup (fun c hc a ha => hAB a ha c hc) (hB'e (hqB y hy))
  obtain ⟨a', ha', u, hu, e2⟩ :=
    exists_mul_of_mem_sup (fun c hc a ha => hAB' a ha c hc) (hBe hy)
  have hu' : u = a'⁻¹ * y := by rw [e2]; group
  have hinv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right (hA2 a' ha')
  have hqu : q * u * q⁻¹ ∈ B := hqB' u hu
  have hca : q * a'⁻¹ * q⁻¹ ∈ A := hqA _ (A.inv_mem ha')
  have h3 : (q * a'⁻¹ * q⁻¹) * a₁ ∈ A ⊓ B := by
    refine ⟨A.mul_mem hca ha₁, ?_⟩
    have : (q * a'⁻¹ * q⁻¹) * a₁ = (q * u * q⁻¹) * y₁⁻¹ := by
      have e3 : q * u * q⁻¹ = (q * a'⁻¹ * q⁻¹) * (q * y * q⁻¹) := by rw [hu']; group
      rw [e3, e1]; group
    rw [this]
    exact B.mul_mem hqu (B.inv_mem hy₁)
  have h4 : (q * a'⁻¹ * q⁻¹) * a'⁻¹⁻¹ ∈ A ⊓ B := by
    have := hz a'⁻¹ (A.inv_mem ha')
    simpa using this
  have h5 : a' * a₁ ∈ A ⊓ B := by
    have h6 := (A ⊓ B).mul_mem ((A ⊓ B).inv_mem h4) h3
    have : ((q * a'⁻¹ * q⁻¹) * a'⁻¹⁻¹)⁻¹ * ((q * a'⁻¹ * q⁻¹) * a₁) = a'⁻¹ * a₁ := by group
    rw [this, hinv] at h6
    exact h6
  have hyy : y₁ * y⁻¹ ∈ B := B.mul_mem hy₁ (B.inv_mem hy)
  have hcomm : (y₁ * y⁻¹) * a' = a' * (y₁ * y⁻¹) := (hAB a' ha' _ hyy).symm
  have h7 : (q * y * q⁻¹) * u⁻¹ ∈ B' := B'.mul_mem (hqB y hy) (B'.inv_mem hu)
  have h8 : (q * y * q⁻¹) * u⁻¹ = (a₁ * a') * (y₁ * y⁻¹) := by
    rw [e1, hu']
    calc a₁ * y₁ * (a'⁻¹ * y)⁻¹ = a₁ * ((y₁ * y⁻¹) * a') := by group
      _ = a₁ * (a' * (y₁ * y⁻¹)) := by rw [hcomm]
      _ = (a₁ * a') * (y₁ * y⁻¹) := by group
  have h9 : a₁ * a' ∈ B' := by
    rw [hAc a₁ ha₁ a' ha']
    exact hR1 h5
  have h10 : y₁ * y⁻¹ ∈ B' := by
    have := B'.mul_mem (B'.inv_mem h9) h7
    rw [h8, inv_mul_cancel_left] at this
    exact this
  have h11 : y₁ * y⁻¹ ∈ A := hR2 ⟨hyy, h10⟩
  have : q * y * q⁻¹ * y⁻¹ = a₁ * (y₁ * y⁻¹) := by rw [e1]; group
  rw [this]
  exact A.mul_mem ha₁ h11

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
