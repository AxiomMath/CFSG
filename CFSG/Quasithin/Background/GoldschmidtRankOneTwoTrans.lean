module

public import CFSG.Quasithin.Background.GoldschmidtRankOneLift

public section

open scoped Pointwise

namespace CFSG.Quasithin

open CFSG.Open

section TwoTransitive

variable {G Ω : Type*} [Group G] (ρ : G →* Equiv.Perm Ω)

@[expose] def pointStab (x : Ω) : Subgroup G :=
  (MulAction.stabilizer (Equiv.Perm Ω) x).comap ρ

theorem mem_pointStab {x : Ω} {g : G} : g ∈ pointStab ρ x ↔ ρ g x = x := Iff.rfl

theorem mem_pointStab_smul_iff (x : Ω) (g h : G) :
    h ∈ MulAut.conj g • pointStab ρ x ↔ h ∈ pointStab ρ (ρ g x) := by
  have hc : (MulAut.conj g)⁻¹ • h = g⁻¹ * h * g := by
    rw [MulAut.smul_def]
    rfl
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hc, mem_pointStab, mem_pointStab]
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  constructor
  · intro hh
    have := congrArg (ρ g) hh
    simpa using this
  · intro hh
    rw [hh]
    simp

variable (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, ρ g a = c ∧ ρ g b = d)
  (hne : ∃ a b : Ω, a ≠ b)

include h2 hne in
theorem exists_smul_eq_of_two_transitive (x y : Ω) : ∃ g : G, ρ g x = y := by
  by_cases hxy : x = y
  · exact ⟨1, by simp [hxy]⟩
  · obtain ⟨a, b, hab⟩ := hne
    have hx : ∃ x' : Ω, x' ≠ x := by
      by_cases ha : a = x
      · exact ⟨b, fun h => hab (ha.trans h.symm)⟩
      · exact ⟨a, ha⟩
    have hy : ∃ y' : Ω, y' ≠ y := by
      by_cases ha : a = y
      · exact ⟨b, fun h => hab (ha.trans h.symm)⟩
      · exact ⟨a, ha⟩
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨g, hg, -⟩ := h2 x x' y y' hx'.symm hy'.symm
    exact ⟨g, hg⟩

include h2 in
theorem eq_pointStab_of_le (x : Ω) {M : Subgroup G} (hM : pointStab ρ x ≤ M) (hMtop : M ≠ ⊤) :
    M = pointStab ρ x := by
  by_contra hne'
  obtain ⟨m, hm, hmx⟩ : ∃ m ∈ M, ρ m x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hne' (le_antisymm (fun m hm => hcon m hm) hM)
  apply hMtop
  rw [eq_top_iff]
  intro g _
  by_cases hg : ρ g x = x
  · exact hM hg
  · obtain ⟨h, hh1, hh2⟩ := h2 x (ρ m x) x (ρ g x) (fun e => hmx e.symm) (fun e => hg e.symm)
    have hhM : h ∈ M := hM hh1
    have hm' : h * m ∈ M := M.mul_mem hhM hm
    have hm'x : ρ (h * m) x = ρ g x := by simp [hh2]
    have hstab : (h * m)⁻¹ * g ∈ pointStab ρ x := by
      rw [mem_pointStab, map_mul, map_inv, Equiv.Perm.mul_apply, ← hm'x]
      simp
    have := M.mul_mem hm' (hM hstab)
    rwa [mul_inv_cancel_left] at this

theorem mem_pointStab_apply_iff (x : Ω) (g h : G) :
    h ∈ pointStab ρ (ρ g x) ↔ g⁻¹ * h * g ∈ pointStab ρ x := by
  rw [mem_pointStab, mem_pointStab]
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
  constructor
  · intro hh
    rw [hh]
    simp
  · intro hh
    have := congrArg (ρ g) hh
    simpa using this

include h2 hne in
theorem isRankOneSylowCyclic_of_two_transitive [Finite G] (hρ : Function.Injective ρ) (ω : Ω)
    (hp : IsPGroup 2 (pointStab ρ ω)) (hodd : ¬ 2 ∣ (pointStab ρ ω).index)
    (hnt : pointStab ρ ω ≠ ⊥) : IsRankOneSylowCyclic G := by
  have hmax := eq_pointStab_of_le ρ h2
  have hexists := exists_smul_eq_of_two_transitive ρ h2 hne
  have hsyl : ∀ T : Subgroup G, IsPGroup 2 T → ¬ 2 ∣ T.index →
      ∃ x : Ω, T = pointStab ρ x ∧ T ≠ ⊥ := by
    intro T hT hTodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hp.toSylow hodd) (hT.toSylow hTodd)
    have h1 : MulAut.conj g • pointStab ρ ω = T := by
      have := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
      simpa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
    have hT' : T = pointStab ρ (ρ g ω) := by
      ext h
      rw [← h1, mem_pointStab_smul_iff]
    refine ⟨ρ g ω, hT', fun hbot => hnt ?_⟩
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    intro h hh
    have : g * h * g⁻¹ ∈ pointStab ρ (ρ g ω) := by
      rw [mem_pointStab_apply_iff]
      simpa [mul_assoc] using hh
    rw [← hT'] at this
    have h0 := hbot _ this
    simpa using h0
  have hnn : ∀ x : Ω, pointStab ρ x ≠ ⊥ → ¬ (pointStab ρ x).Normal := by
    intro x hx hN
    apply hx
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    apply hρ
    ext y
    obtain ⟨g, hg⟩ := hexists x y
    have h1 : g * t * g⁻¹ ∈ pointStab ρ x := hN.conj_mem t ht g
    have h2' : t ∈ pointStab ρ (ρ g x) := by
      rw [mem_pointStab_apply_iff]
      have := hN.conj_mem t ht g⁻¹
      simpa using this
    rw [hg] at h2'
    rw [map_one]
    exact (mem_pointStab ρ).mp h2'
  have key : ∀ T : Subgroup G, IsPGroup 2 T → ¬ 2 ∣ T.index →
      Subgroup.normalizer (T : Set G) = T ∧ (¬ (Subgroup.normalizer (T : Set G) = ⊤)) ∧
        ∀ M : Subgroup G, T ≤ M → M ≠ ⊤ → M = T := by
    intro T hT hTodd
    obtain ⟨x, hx, hTnt⟩ := hsyl T hT hTodd
    subst hx
    have hne' : ¬ Subgroup.normalizer ((pointStab ρ x : Subgroup G) : Set G) = ⊤ := fun h =>
      hnn x hTnt (Subgroup.normalizer_eq_top_iff.mp h)
    exact ⟨hmax x Subgroup.le_normalizer hne', hne', fun M hM hMt => hmax x hM hMt⟩
  refine ⟨fun T hT hTodd => ?_, fun T hT hTodd => ?_⟩
  · obtain ⟨hN, hne', hM⟩ := key T hT hTodd
    refine ⟨hne', fun M hTM hMt => ?_, fun x hx y hy => ?_⟩
    · rw [hM M hTM hMt]
      exact Subgroup.le_normalizer
    · rw [hN] at hx hy
      exact T.mul_mem (T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)) (T.inv_mem hy)
  · obtain ⟨hN, -, -⟩ := key T hT hTodd
    exact ⟨⊥, inferInstance, by rw [sup_bot_eq, hN]⟩

end TwoTransitive

end CFSG.Quasithin
