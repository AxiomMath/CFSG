module

public import CFSG.Permutation.UnitaryThreeRecognition.Basic

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def centQ (Q : Subgroup G) (t : G) : Subgroup G :=
  Q ⊓ Subgroup.centralizer ({t} : Set G)

theorem mem_centQ {Q : Subgroup G} {t u : G} : u ∈ centQ Q t ↔ u ∈ Q ∧ t * u = u * t := by
  simp only [centQ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]

theorem smul_smul_eq_conj_smul {a b : Ω} {t : G} (ht : t ∈ pairStab G a b) (u : G) :
    t • (u • b) = (t * u * t⁻¹) • b := by
  have htb : t⁻¹ • b = b := by rw [inv_smul_eq_iff]; exact ht.2.symm
  rw [mul_smul, mul_smul, htb]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem fixes_iff {b : Ω} (hb : b ≠ a) {t u : G} (ht : t ∈ pairStab G a b) (hu : u ∈ Q) :
    t • (u • b) = u • b ↔ t * u = u * t := by
  rw [smul_smul_eq_conj_smul ht]
  constructor
  · intro h
    have hconj : t * u * t⁻¹ ∈ Q := hQ.normal t ht.1 u hu
    have := hQ.eq_of_smul_eq hconj hu hb h
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [this]
  · intro h
    rw [h, mul_inv_cancel_right]

theorem fixedPoints_equiv {b : Ω} (hb : b ≠ a) {t : G} (ht : t ∈ pairStab G a b) :
    Nonempty ({β : Ω // t • β = β} ≃ Option (centQ Q t)) := by
  classical
  let φ : Option (centQ Q t) → {β : Ω // t • β = β} := fun o =>
    match o with
    | none => ⟨a, ht.1⟩
    | some u => ⟨(u : G) • b, (hQ.fixes_iff hb ht (mem_centQ.mp u.property).1).mpr
        (mem_centQ.mp u.property).2⟩
  have hinj : Function.Injective φ := by
    intro o₁ o₂ h
    have hv := congrArg Subtype.val h
    rcases o₁ with _ | u₁ <;> rcases o₂ with _ | u₂
    · rfl
    · exact absurd hv.symm (hQ.smul_ne (mem_centQ.mp u₂.property).1 hb)
    · exact absurd hv (hQ.smul_ne (mem_centQ.mp u₁.property).1 hb)
    · congr 1
      exact Subtype.ext (hQ.eq_of_smul_eq (mem_centQ.mp u₁.property).1
        (mem_centQ.mp u₂.property).1 hb hv)
  have hsurj : Function.Surjective φ := by
    rintro ⟨β, hβ⟩
    by_cases hβa : β = a
    · subst hβa
      exact ⟨none, rfl⟩
    · obtain ⟨u, huQ, hu⟩ := hQ.exists_smul_eq hb hβa
      have hcomm : t * u = u * t := (hQ.fixes_iff hb ht huQ).mp (by rw [hu]; exact hβ)
      exact ⟨some ⟨u, mem_centQ.mpr ⟨huQ, hcomm⟩⟩, Subtype.ext hu⟩
  exact ⟨(Equiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem card_fixedPoints [Finite Ω] {b : Ω} (hb : b ≠ a) {t : G} (ht : t ∈ pairStab G a b) :
    Nat.card {β : Ω // t • β = β} = Nat.card (centQ Q t) + 1 := by
  obtain ⟨e⟩ := hQ.fixedPoints_equiv hb ht
  have : Finite (centQ Q t) := by
    have : Finite {β : Ω // t • β = β} := inferInstance
    exact Finite.of_injective (fun u => e.symm (some u)) (fun x y h => by simpa using h)
  rw [Nat.card_congr e, Finite.card_option]

theorem card_centralizer [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {t : G} (ht : t ∈ pairStab G a b) {g : G} (hga : g • a = b) (hgt : g * t = t * g) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
      (Nat.card (centQ Q t) + 1) * (Nat.card (centQ Q t) * Nat.card (pairStab G a b)) := by
  classical
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  have memC : ∀ c : G, c ∈ C ↔ t * c = c * t := by
    intro c
    simp only [hCdef, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  have horbit : ∀ β : Ω, β ∈ orbit C a ↔ t • β = β := by
    intro β
    constructor
    · rintro ⟨c, rfl⟩
      change t • ((c : G) • a) = (c : G) • a
      rw [smul_smul, (memC c).mp c.property, mul_smul, ht.1]
    · intro hβ
      by_cases hβa : β = a
      · subst hβa; exact mem_orbit_self _
      · obtain ⟨u, huQ, hu⟩ := hQ.exists_smul_eq hb hβa
        have hcu : t * u = u * t := (hQ.fixes_iff hb ht huQ).mp (by rw [hu]; exact hβ)
        have hug : u * g ∈ C := by
          rw [memC]
          calc t * (u * g) = (t * u) * g := by group
            _ = u * (t * g) := by rw [hcu]; group
            _ = u * (g * t) := by rw [hgt]
            _ = u * g * t := by group
        refine ⟨⟨u * g, hug⟩, ?_⟩
        change (u * g) • a = β
        rw [mul_smul, hga, hu]
  have horbit_card : Nat.card (orbit C a) = Nat.card (centQ Q t) + 1 := by
    rw [← hQ.card_fixedPoints hb ht]
    exact Nat.card_congr (Equiv.subtypeEquivRight horbit)
  have hstab : Nat.card (stabilizer C a) = Nat.card (centQ Q t) * Nat.card (pairStab G a b) := by
    let ψ : centQ Q t × pairStab G a b → stabilizer C a := fun p =>
      ⟨⟨(p.1 : G) * p.2, by
          rw [memC]
          have h1 : t * (p.1 : G) = p.1 * t := (mem_centQ.mp p.1.property).2
          have h2 : t * (p.2 : G) = p.2 * t := hcomm t ht p.2 p.2.property
          calc t * ((p.1 : G) * p.2) = (t * p.1) * p.2 := by group
            _ = p.1 * (t * p.2) := by rw [h1]; group
            _ = p.1 * (p.2 * t) := by rw [h2]
            _ = (p.1 : G) * p.2 * t := by group⟩, by
        change ((p.1 : G) * p.2) • a = a
        rw [mul_smul, p.2.property.1, hQ.smul_self (mem_centQ.mp p.1.property).1]⟩
    have hinj : Function.Injective ψ := by
      rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ hψ
      have hv : (x₁ : G) * h₁ = x₂ * h₂ := congrArg (fun z : stabilizer C a => ((z : C) : G)) hψ
      obtain ⟨hx, hh⟩ := hQ.mul_pairStab_unique hb (mem_centQ.mp x₁.property).1
        (mem_centQ.mp x₂.property).1 h₁.property h₂.property hv
      exact Prod.ext (Subtype.ext hx) (Subtype.ext hh)
    have hsurj : Function.Surjective ψ := by
      rintro ⟨⟨c, hcC⟩, hca⟩
      have hca' : c • a = a := hca
      obtain ⟨x, hxQ, h, hh, rfl⟩ := hQ.exists_mul_pairStab hb hca'
      have hth : t * h = h * t := hcomm t ht h hh
      have htxh : t * (x * h) = x * h * t := (memC _).mp hcC
      have htx : t * x = x * t := by
        have : t * x * h = x * t * h := by
          calc t * x * h = t * (x * h) := by group
            _ = x * h * t := htxh
            _ = x * (h * t) := by group
            _ = x * (t * h) := by rw [hth]
            _ = x * t * h := by group
        exact mul_right_cancel this
      exact ⟨⟨⟨x, mem_centQ.mpr ⟨hxQ, htx⟩⟩, ⟨h, hh⟩⟩, rfl⟩
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)).symm
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup C a)
  rw [Nat.card_prod, horbit_card, hstab] at hos
  exact hos.symm

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
