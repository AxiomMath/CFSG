module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_map_conj {I₀ : Subgroup G} {S : Set G} {r : G}
    (hcomm : ∀ b ∈ S, ∀ v ∈ I₀, b * (r * v * r⁻¹) * b⁻¹ = r * (b * v * b⁻¹) * r⁻¹) :
    (I₀ ⊓ centralizer S).map (MulAut.conj r).toMonoidHom =
      conjSubgroup I₀ r⁻¹ ⊓ centralizer S := by
  have hmem : ∀ w, w ∈ conjSubgroup I₀ r⁻¹ ↔ r⁻¹ * w * r ∈ I₀ := fun w => by
    rw [mem_conjSubgroup_iff]
    simp
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, hmem]
  constructor
  · rintro ⟨v, ⟨hv, hvc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply, mul_assoc] using hv
    · intro b hb
      have h1 := hcomm b hb v hv
      have h2 : b * v = v * b := hvc b hb
      simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom]
      have h3 : b * v * b⁻¹ = v := by rw [h2]; group
      rw [h3] at h1
      calc b * (r * v * r⁻¹) = (b * (r * v * r⁻¹) * b⁻¹) * b := by group
        _ = (r * v * r⁻¹) * b := by rw [h1]
  · rintro ⟨hw, hwc⟩
    refine ⟨r⁻¹ * w * r, ⟨hw, ?_⟩, ?_⟩
    · intro b hb
      have h1 := hcomm b hb _ hw
      have h5 : r * (r⁻¹ * w * r) * r⁻¹ = w := by group
      rw [h5] at h1
      have h6 : b * w * b⁻¹ = w := by rw [hwc b hb]; group
      rw [h6] at h1
      have h7 : b * (r⁻¹ * w * r) * b⁻¹ = r⁻¹ * w * r := by
        have := congrArg (fun z => r⁻¹ * z * r) h1
        simpa [mul_assoc] using this.symm
      calc b * (r⁻¹ * w * r) = (b * (r⁻¹ * w * r) * b⁻¹) * b := by group
        _ = (r⁻¹ * w * r) * b := by rw [h7]
    · simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom]
      group

theorem s16c167_twenty_two_card_conj {I₀ I B' : Subgroup G} {r : G}
    (hI : conjSubgroup I₀ r⁻¹ = I)
    (hcomm : ∀ b ∈ B', ∀ v ∈ I₀, b * (r * v * r⁻¹) * b⁻¹ = r * (b * v * b⁻¹) * r⁻¹) :
    Nat.card ↥(I ⊓ centralizer (B' : Set G)) = Nat.card ↥(I₀ ⊓ centralizer (B' : Set G)) := by
  rw [← hI, ← s16c167_twenty_two_map_conj (S := (B' : Set G)) hcomm]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj r).toMonoidHom)
    (MulAut.conj r).injective

theorem s16c167_twenty_two_transitive {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) {π : ↥(Mbar M ⊥ V hV) →* Equiv.Perm (Fin 3)}
    (hcomm : ∀ x : ↥(Mbar M ⊥ V hV), (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      ((∀ y ∈ oddBar M ⊥ V hV, (x : MulAut (Vtil ⊥ V hV)) * y = y * x) ↔ π x = 1))
    (htrans : ∀ i j : Fin 3, ∃ y : ↥(Mbar M ⊥ V hV),
      (y : MulAut (Vtil ⊥ V hV)) ∈ oddBar M ⊥ V hV ∧ π y i = j) (i j : Fin 3) :
    ∃ r : ↥M, π (s16c167_barHom hV hM r) i = j ∧ ∀ b : ↥M, b ^ 2 = 1 →
      π (s16c167_barHom hV hM b) = 1 → ∀ v ∈ V,
        (b : G) * ((r : G) * v * (r : G)⁻¹) * (b : G)⁻¹ =
          (r : G) * ((b : G) * v * (b : G)⁻¹) * (r : G)⁻¹ := by
  obtain ⟨y, hyodd, hyij⟩ := htrans i j
  obtain ⟨⟨g, hgs⟩, hgM, hgy⟩ := (mem_barSub ⊥ V hV M (y : MulAut (Vtil ⊥ V hV))).1 y.2
  refine ⟨⟨g, hgM⟩, ?_, ?_⟩
  · have : s16c167_barHom hV hM ⟨g, hgM⟩ = y := Subtype.ext hgy
    rw [this]
    exact hyij
  · intro b hb2 hb1 v hv
    have hx2 : ∃ k : ℕ, (s16c167_barHom hV hM b) ^ (2 ^ k) = 1 :=
      ⟨1, by rw [pow_one, ← map_pow, hb2, map_one]⟩
    have hc := ((hcomm _ hx2).2 hb1) _ hyodd
    have hc' := congrArg
      (fun φ : MulAut (Vtil ⊥ V hV) => φ (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩))) hc
    simp only [MulAut.mul_apply] at hc'
    rw [← hgy] at hc'
    have hb : (b : G) ∈ stabTil ⊥ V := s16c167_mem_stabTil_bot (hM b.2)
    rw [s16c167_barHom_apply] at hc'
    simp only [actTil_mk] at hc'
    rw [mkTil_eq_iff, Subgroup.mem_bot, mul_inv_eq_one] at hc'
    simp only [actStab_apply_val] at hc'
    exact hc'

theorem s16c167_twenty_two_card_family {M V B' : Subgroup G} {I : Fin 3 → Subgroup G}
    {ρ : ↥M →* Equiv.Perm (Fin 3)} (hle : ∀ i, I i ≤ V)
    (hconj : ∀ (m : ↥M) (i : Fin 3), conjSubgroup (I i) (m : G)⁻¹ = I (ρ m i))
    (htr : ∀ i j : Fin 3, ∃ r : ↥M, ρ r i = j ∧ ∀ b : ↥M, b ^ 2 = 1 → ρ b = 1 → ∀ v ∈ V,
      (b : G) * ((r : G) * v * (r : G)⁻¹) * (b : G)⁻¹ =
        (r : G) * ((b : G) * v * (b : G)⁻¹) * (r : G)⁻¹)
    (hB'M : B' ≤ M) (hB'2 : ∀ b ∈ B', b ^ 2 = 1) (hB'ρ : ∀ b : ↥M, (b : G) ∈ B' → ρ b = 1)
    (i₀ i : Fin 3) :
    Nat.card ↥(I i ⊓ centralizer (B' : Set G)) = Nat.card ↥(I i₀ ⊓ centralizer (B' : Set G)) := by
  obtain ⟨r, hri, hr⟩ := htr i₀ i
  refine s16c167_twenty_two_card_conj (r := (r : G)) (by rw [hconj, hri]) ?_
  intro b hb v hv
  have hbM : b ∈ M := hB'M hb
  have h2 : (⟨b, hbM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by simpa using hB'2 b hb)
  exact hr ⟨b, hbM⟩ h2 (hB'ρ ⟨b, hbM⟩ hb) v (hle i₀ hv)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
