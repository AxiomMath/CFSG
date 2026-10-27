module

public import CFSG.Quasithin.EmptyFaithful.S153E57F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EO61

open S153E57

section Generic

theorem exists_eq_mul_tau {X : Type*} [CommGroup X] {W₁ W₂ : Subgroup X} {τ : MulAut X}
    (hdec : ∀ w : X, ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = w) (hint : ∀ w : X, w ∈ W₁ → w ∈ W₂ → w = 1)
    (hττ : ∀ w, τ (τ w) = w) (hτ₁ : ∀ x ∈ W₁, τ x ∈ W₂) (hτ₂ : ∀ x ∈ W₂, τ x ∈ W₁)
    {c : X} (hc : τ c = c) : ∃ a ∈ W₁, c = a * τ a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hdec c
  have h4 : τ a * τ b = a * b := by
    rw [← map_mul, hab]
    exact hc
  have h5 : a * (τ b)⁻¹ = 1 := by
    apply hint _ (W₁.mul_mem ha (W₁.inv_mem (hτ₂ b hb)))
    have e : τ a * b⁻¹ = a * (τ b)⁻¹ :=
      calc τ a * b⁻¹ = (τ a * τ b) * (τ b)⁻¹ * b⁻¹ := by group
        _ = (a * b) * (τ b)⁻¹ * b⁻¹ := by rw [h4]
        _ = a * (b * (τ b)⁻¹) * b⁻¹ := by rw [mul_assoc a b]
        _ = a * ((τ b)⁻¹ * b) * b⁻¹ := by rw [mul_comm b]
        _ = a * (τ b)⁻¹ := by group
    rw [← e]
    exact W₂.mul_mem (hτ₁ a ha) (W₂.inv_mem hb)
  have h6 : a = τ b := mul_inv_eq_one.1 h5
  have h7 : b = τ a := by rw [h6, hττ]
  exact ⟨a, ha, by rw [← hab, h7]⟩

end Generic

section Lift

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

abbrev UTil (T M V₁ Mc : Subgroup G) : Type :=
  ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

theorem mem_U_of_rho_eq_one (cx : Ctx15350 T Mc M V₁ V₂ t) (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc)
    (n : NZ T) (hn : rho cx n = 1) : (n : G) ∈ UH153 T M V₁ Mc := by
  have hnMc : (n : G) ∈ Mc := NZ_le_Mc cx n.2
  have key : ∀ u ∈ UH153 T M V₁ Mc, (n : G) * u * (n : G)⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro u hu
    have h1 := piU_conj cx n hnMc ⟨u, hu⟩
    rw [hn, MulAut.one_apply] at h1
    have h2 : piU cx ((⟨(n : G) * u * (n : G)⁻¹, S153E.U_conj_mem hnMc hu⟩ : ↥(UH153 T M V₁ Mc)) *
        (⟨u, hu⟩ : ↥(UH153 T M V₁ Mc))⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    simpa using (piU_eq_one_iff cx _).1 h2
  have hmem : (n : G) ∈ centralizerMod (quasithinOmegaOneCenter T) Mc (UH153 T M V₁ Mc) :=
    ⟨hnMc, n.2, key⟩
  rw [hUQ, cx.hF.pCoreOf_eq_centralizerMod]
  exact hmem

theorem exists_lift (cx : Ctx15350 T Mc M V₁ V₂ t) (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc)
    {t₂ : G} (ht₂T : t₂ ∈ T) (ht₂ : t₂ * t₂ = 1)
    {W₁ W₂ : Subgroup (UTil T M V₁ Mc)}
    (hcomm : ∀ a b : UTil T M V₁ Mc, a * b = b * a) (hsq : ∀ a : UTil T M V₁ Mc, a * a = 1)
    (hdec : ∀ w : UTil T M V₁ Mc, ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = w)
    (hint : ∀ w : UTil T M V₁ Mc, w ∈ W₁ → w ∈ W₂ → w = 1)
    (hτ₁ : ∀ x ∈ W₁, rho cx ⟨t₂, t₁_mem_NZ cx ht₂T⟩ x ∈ W₂)
    (hτ₂ : ∀ x ∈ W₂, rho cx ⟨t₂, t₁_mem_NZ cx ht₂T⟩ x ∈ W₁)
    {d : MulAut (UTil T M V₁ Mc)} (hd : d ∈ HStar153 T M V₁ Mc)
    (hdτ : d * rho cx ⟨t₂, t₁_mem_NZ cx ht₂T⟩ = rho cx ⟨t₂, t₁_mem_NZ cx ht₂T⟩ * d) :
    ∃ y : NZ T, (y : G) ∈ Mc ∧ rho cx y = d ∧
      (y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹ ∈ quasithinOmegaOneCenter T := by
  let _ : CommGroup (UTil T M V₁ Mc) := { (inferInstance : Group (UTil T M V₁ Mc)) with mul_comm := hcomm }
  have ht₂N : t₂ ∈ NZ T := t₁_mem_NZ cx ht₂T
  have ht₂Mc : t₂ ∈ Mc := S153E.T_le_Mc cx ht₂T
  have hinv : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right ht₂
  let t₂N : NZ T := ⟨t₂, ht₂N⟩
  set τ := rho cx t₂N with hτdef
  have hττ : ∀ w, τ (τ w) = w := by
    intro w
    have h1 : τ * τ = 1 := by
      rw [hτdef, ← map_mul]
      have : (t₂N * t₂N : NZ T) = 1 := Subtype.ext ht₂
      rw [this, map_one]
    have := congrArg (fun f : MulAut (UTil T M V₁ Mc) => f w) h1
    simpa using this
  obtain ⟨y, hyMc, hyd⟩ := (mem_XStar_iff cx Mc d).1 hd
  have hρ0 : rho cx (y * t₂N * y⁻¹ * t₂N⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyd]
    change d * τ * d⁻¹ * τ⁻¹ = 1
    rw [hdτ]
    group
  have hc₀U : (y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹ ∈ UH153 T M V₁ Mc :=
    mem_U_of_rho_eq_one cx hUQ _ hρ0
  let c₀ : ↥(UH153 T M V₁ Mc) := ⟨(y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹, hc₀U⟩
  have hτc₀ : τ (piU cx c₀) = piU cx c₀ := by
    have h1 := piU_conj cx t₂N ht₂Mc c₀
    have h2 : (⟨(t₂N : G) * (c₀ : G) * (t₂N : G)⁻¹, S153E.U_conj_mem ht₂Mc c₀.2⟩ :
        ↥(UH153 T M V₁ Mc)) = c₀⁻¹ := by
      apply Subtype.ext
      show t₂ * ((y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹) * t₂⁻¹ = ((y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹)⁻¹
      calc t₂ * ((y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹) * t₂⁻¹
          = t₂ * (y : G) * t₂ * (y : G)⁻¹ * (t₂⁻¹ * t₂⁻¹) := by group
        _ = t₂ * (y : G) * t₂ * (y : G)⁻¹ := by rw [hinv, ht₂, mul_one]
        _ = t₂ * (y : G) * t₂⁻¹ * (y : G)⁻¹ := by rw [hinv]
        _ = ((y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹)⁻¹ := by group
    rw [h2, map_inv] at h1
    rw [← h1]
    exact inv_eq_of_mul_eq_one_right (hsq _)
  obtain ⟨a, ha, hca⟩ := exists_eq_mul_tau hdec hint hττ hτ₁ hτ₂ hτc₀
  obtain ⟨u, hu⟩ := piU_surjective cx a
  have huU : (u : G) ∈ UH153 T M V₁ Mc := u.2
  have huNZ : (u : G) ∈ NZ T := U_le_NZ cx huU
  let uN : NZ T := ⟨(u : G), huNZ⟩
  have huMc : (u : G) ∈ Mc := pCoreOf_le 2 Mc (S153E.U_le_Q cx huU)
  refine ⟨uN * y, Mc.mul_mem huMc hyMc, ?_, ?_⟩
  · rw [map_mul, rho_eq_one_of_mem_U cx uN huU, hyd, one_mul]
  · have hw : t₂ * (u : G)⁻¹ * t₂⁻¹ ∈ UH153 T M V₁ Mc :=
      S153E.U_conj_mem ht₂Mc ((UH153 T M V₁ Mc).inv_mem huU)
    let w : ↥(UH153 T M V₁ Mc) := ⟨t₂ * (u : G)⁻¹ * t₂⁻¹, hw⟩
    have hpw : piU cx w = (τ a)⁻¹ := by
      have h1 := piU_conj cx t₂N ht₂Mc u⁻¹
      rw [map_inv, hu, map_inv] at h1
      exact h1
    have hcu : ((uN * y : NZ T) : G) * t₂ * ((uN * y : NZ T) : G)⁻¹ * t₂⁻¹ = ((u * c₀ * w : ↥(UH153 T M V₁ Mc)) : G) := by
      show (u : G) * (y : G) * t₂ * ((u : G) * (y : G))⁻¹ * t₂⁻¹ =
        (u : G) * ((y : G) * t₂ * (y : G)⁻¹ * t₂⁻¹) * (t₂ * (u : G)⁻¹ * t₂⁻¹)
      group
    rw [hcu]
    have h1 : piU cx (u * c₀ * w) = 1 := by
      rw [map_mul, map_mul, hu, hca, hpw]
      calc a * (a * τ a) * (τ a)⁻¹ = a * a := by group
        _ = 1 := hsq a
    exact (piU_eq_one_iff cx _).1 h1

end Lift

end S153EO61

end CFSG.Quasithin
