module

public import CFSG.RankThree.PartTwo.Sec13.K135K3Sylow
public import CFSG.RankThree.PartOne.KS.HeSevenCentralizers
public import CFSG.Milestones.ASVolI.A3Spor.Out

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.RankThree.PartOne

theorem hsyl_He
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.He) :
    ∀ Q : Subgroup S, IsPGroup 7 Q → 7 ^ 3 ≤ Nat.card Q → ∀ l : S, l ^ 3 = 1 →
      (∀ g ∈ Q, l * g = g * l) → l = 1 := by
  obtain ⟨⟨hQle, hSyl, hcard343, -⟩, ⟨hlines, -⟩, -, -, -, -, -, ⟨hC2eq, hC2card⟩, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  obtain ⟨S7, hS7⟩ := hSyl
  intro Q hQ hQcard l hl3 hcomm
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let θ : S ≃* ↥heP := e.trans heEquivP
  haveI : Finite ↥heP := Finite.of_equiv S θ.toEquiv
  have hQ'p : IsPGroup 7 (Q.map θ.toMonoidHom) := isPGroup_map_of_equiv θ hQ
  have hQ'card : Nat.card (Q.map θ.toMonoidHom) = Nat.card Q :=
    Subgroup.card_map_of_injective θ.injective
  have hS7card : Nat.card (S7 : Subgroup ↥heP) = 343 := by
    rw [hS7, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv]
    exact hcard343
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_ge S7 (Q.map θ.toMonoidHom) hQ'p (by
    rw [hS7card, hQ'card]
    omega)
  have hline : heSevenLine 2 ∈ heSevenQ := by
    have hmem : zpowers (heSevenLine 2) ∈ {H : Subgroup (Equiv.Perm (Fin 8330)) |
        H ≤ heSevenQ ∧ Nat.card H = 7} := by
      rw [hlines]
      exact ⟨2, rfl⟩
    exact hmem.1 (Subgroup.mem_zpowers _)
  let u0 : ↥heP := ⟨heSevenLine 2, hQle hline⟩
  have hu0 : u0 ∈ (S7 : Subgroup ↥heP) := by
    rw [hS7, Subgroup.mem_subgroupOf]
    exact hline
  have hu : g * u0 * g⁻¹ ∈ Q.map θ.toMonoidHom := conj_mem_of_eq_smul hg hu0
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu
  have hcl : θ l * (g * u0 * g⁻¹) = (g * u0 * g⁻¹) * θ l := by
    rw [← hvu]
    change θ l * θ v = θ v * θ l
    rw [← map_mul, ← map_mul, hcomm v hv]
  let m : ↥heP := g⁻¹ * θ l * g
  have hmu : u0 * m = m * u0 := by
    calc u0 * m = g⁻¹ * ((g * u0 * g⁻¹) * θ l) * g := by simp only [m]; group
      _ = g⁻¹ * (θ l * (g * u0 * g⁻¹)) * g := by rw [hcl]
      _ = m * u0 := by simp only [m]; group
  have hm3 : m ^ 3 = 1 := by
    have h1 : m = MulAut.conj g⁻¹ (θ l) := by simp [m, MulAut.conj_apply]
    rw [h1, ← map_pow, ← map_pow, hl3, map_one, map_one]
  have hmC : (m : Equiv.Perm (Fin 8330)) ∈ heSevenC2 := by
    rw [hC2eq, Subgroup.mem_inf]
    refine ⟨?_, heP_le_heAutGroup m.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact congrArg Subtype.val hmu
  have hm1 : (m : Equiv.Perm (Fin 8330)) = 1 :=
    eq_one_of_pow_three_of_coprime heSevenC2 (by rw [hC2card]; norm_num) hmC (by
      have := congrArg Subtype.val hm3
      simpa using this)
  have hm1' : m = 1 := Subtype.ext hm1
  have hθl : θ l = 1 := by
    have : θ l = g * m * g⁻¹ := by simp only [m]; group
    rw [this, hm1', mul_one, mul_inv_cancel]
  exact θ.injective (by rw [hθl, map_one])

theorem k3_He
    {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.He) :
    ∀ P : Subgroup (MulAut S), IsPGroup 7 P → 7 ^ 3 ≤ Nat.card P →
      ∀ α : MulAut S, α ^ 3 = 1 → (∀ π ∈ P, α * π = π * α) → α = 1 := by
  have hsimp : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
  have hcard : Nat.card NativeSporadic.He = 4030387200 := CFSG.Sporadic.He.card_He
  have hnp : ¬ Nat.Prime 4030387200 := by norm_num
  haveI : IsSimpleGroup NativeSporadic.He := hsimp
  haveI : Finite NativeSporadic.He := Finite.of_equiv S e.toEquiv
  have hcen : Subgroup.center S = ⊥ := by
    refine center_eq_bot_of_simple_card (X := NativeSporadic.He) e ?_
    intro hp
    rw [hcard] at hp
    exact hnp hp
  have hodd : ∀ β : MulAut S, Odd (orderOf β) → ∃ l : S, β = MulAut.conj l :=
    CFSG.ASVolI.burnsideA315s_oddInner_He e
  have h7 : ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    CFSG.Quasithin.A318P.not_dvd_outer_He e (by norm_num) (by norm_num)
  intro P hP hcard' α hα hcomm
  exact k3_of_data hcen hodd (inner_of_not_dvd_outer (by norm_num) h7) (hsyl_He e) P hP hcard' α
    hα hcomm

end CFSG.RankThree.PartTwo.Sec13.F135Last
