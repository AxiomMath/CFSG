module

public import CFSG.Quasithin.EmptyFaithful.S143FG
public import CFSG.Quasithin.EmptyFaithful.S143IB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Frame

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.mem_Z_cases {z u : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hu : u ∈ quasithinOmegaOneCenter T) : u = 1 ∨ u = z := by
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp
    c.h1281.card_omegaOneCenter
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · right
    have h1 := hw ⟨u, hu⟩ (fun he => hu1 (congrArg Subtype.val he))
    have h2 := hw ⟨z, hz⟩ (fun he => hz1 (congrArg Subtype.val he))
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem Counter.mem_mcOf_of_comm {z w : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hw : w * z = z * w) : w ∈ mcOf T := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rcases c.mem_Z_cases hz hz1 hu with h | h
  · rw [h]; simp
  · rw [h]; exact hw.symm

theorem Counter.commutator_mem_qOf_of_cube {x : G} (hxH : x ∈ mcOf T) (hx3 : x ^ 3 = 1)
    {E : Subgroup G} (hEH : E ≤ mcOf T) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEsq : ∀ a ∈ E, a * a = 1) (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E) :
    ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ qOf T := by
  have hF := c.oddFacts
  have hmem : ∀ w : ↥(mcOf T), c.actK w ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) := by
    intro w
    rw [← c.actK_range]
    exact ⟨w, rfl⟩
  let E' : Subgroup (MulAut (UT T M)) := (E.subgroupOf (mcOf T)).map c.actK
  have hE'X : E' ≤ autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) := by
    rintro _ ⟨a, -, rfl⟩
    exact hmem a
  have hE'ab : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEab _ ha _ hb)
  have hE'sq : ∀ a ∈ E', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hEsq _ ha)
    rw [this, map_one]
  let x' : ↥(mcOf T) := ⟨x, hxH⟩
  have hx3' : c.actK x' ^ 3 = 1 := by
    rw [← map_pow]
    have : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hxE' : ∀ e ∈ E', c.actK x' * e * (c.actK x')⁻¹ ∈ E' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨x' * a * x'⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact hxE _ ha
  have hcen := centralizes_of_cube hF hE'X hE'ab hE'sq (hmem x') hx3' hxE'
  intro e he
  have heH : e ∈ mcOf T := hEH he
  let e' : ↥(mcOf T) := ⟨e, heH⟩
  have he'E : c.actK e' ∈ E' := ⟨e', he, rfl⟩
  have h1 := hcen _ he'E
  have h2 : c.actK (x' * e' * x'⁻¹ * e'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h1]
    exact mul_inv_cancel _
  exact c.mem_qOf_of_actK_eq_one h2

theorem Counter.exists_two_involutions_of_card_eight {P : Subgroup (MulAut (UT T M))}
    (hPX : P ≤ autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (hP8 : Nat.card P = 8) :
    ∃ e₁ ∈ P, ∃ e₂ ∈ P, e₁ ≠ e₂ ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType
    (W := ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (q := q)
    (tilde_mul_self h) hq4 hq1 hq2 hq3
  rw [hq6] at hPX
  exact S143.exists_two_involutions_of_card_eight hS hPX hP8

theorem Counter.mem_qOf_of_card_eight {P : Subgroup G} (hPH : P ≤ mcOf T) (hP8 : Nat.card P = 8)
    {ι : G} (huniq : ∀ x ∈ P, x * x = 1 → x ≠ 1 → x = ι) : ι ∈ qOf T := by
  by_contra hιQ
  let ψ : ↥P →* MulAut (UT T M) := c.actK.comp (Subgroup.inclusion hPH)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hxP : orderOf x ∣ 8 := by
      rw [← hP8]; exact orderOf_dvd_natCard x
    have hne : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
    obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ 3 := hpx.trans (by simpa using hxP)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst hp2
    have hord0 : orderOf x ≠ 0 := by
      intro h0; rw [h0] at hxP; norm_num at hxP
    set y : ↥P := x ^ (orderOf x / 2) with hy
    have hy2 : orderOf y = 2 := orderOf_pow_orderOf_div hord0 hpx
    have hyker : ψ y = 1 := by
      rw [hy, map_pow, MonoidHom.mem_ker.mp hx, one_pow]
    have hyy : y * y = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one y
      rwa [hy2] at this
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    have hyι : (y : G) = ι :=
      huniq y y.2 (congrArg Subtype.val hyy) (fun h => hy1 (Subtype.ext h))
    apply hιQ
    rw [← hyι]
    exact c.mem_qOf_of_actK_eq_one (x := Subgroup.inclusion hPH y) hyker
  have hrange : ψ.range ≤ autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) := by
    rw [← c.actK_range]
    rintro _ ⟨a, rfl⟩
    exact ⟨Subgroup.inclusion hPH a, rfl⟩
  have hcard : Nat.card ψ.range = 8 := by
    rw [← hP8]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  obtain ⟨e₁, he₁, e₂, he₂, hne, he₁1, he₂1, he₁₁, he₂₂⟩ :=
    c.exists_two_involutions_of_card_eight hrange hcard
  obtain ⟨p₁, rfl⟩ := he₁
  obtain ⟨p₂, rfl⟩ := he₂
  have hp₁ : p₁ * p₁ = 1 := hψ (by rw [map_mul, he₁₁, map_one])
  have hp₂ : p₂ * p₂ = 1 := hψ (by rw [map_mul, he₂₂, map_one])
  have hp₁1 : p₁ ≠ 1 := fun h1 => he₁1 (by rw [h1, map_one])
  have hp₂1 : p₂ ≠ 1 := fun h1 => he₂1 (by rw [h1, map_one])
  have h1 : (p₁ : G) = ι :=
    huniq p₁ p₁.2 (congrArg Subtype.val hp₁) (fun h => hp₁1 (Subtype.ext h))
  have h2 : (p₂ : G) = ι :=
    huniq p₂ p₂.2 (congrArg Subtype.val hp₂) (fun h => hp₂1 (Subtype.ext h))
  exact hne (by rw [Subtype.ext (h1.trans h2.symm)])

end Frame

end S143

end CFSG.Quasithin
