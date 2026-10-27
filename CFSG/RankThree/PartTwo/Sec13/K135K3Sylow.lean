module

public import CFSG.RankThree.PartTwo.Sec13.K135K3Core

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped Pointwise

theorem exists_conj_eq_of_card_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S0 : Sylow p G) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hcard : Nat.card (S0 : Subgroup G) ≤ Nat.card Q) :
    ∃ g : G, Q = MulAut.conj g • (S0 : Subgroup G) := by
  obtain ⟨T, hT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 T
  have hTcard : Nat.card (T : Subgroup G) = Nat.card (S0 : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  refine ⟨g, ?_⟩
  have hQT : Q = (T : Subgroup G) := Subgroup.eq_of_le_of_card_ge hT (by rw [hTcard]; exact hcard)
  rw [hQT, ← hg]
  rfl

theorem conj_mem_of_eq_smul {G : Type*} [Group G] {S0 Q : Subgroup G} {g : G}
    (hQ : Q = MulAut.conj g • S0) {u : G} (hu : u ∈ S0) : g * u * g⁻¹ ∈ Q := by
  rw [hQ]
  exact Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) S0 hu

theorem centralizer_le_of_conj {G : Type*} [Group G] {S0 Q : Subgroup G} {g : G}
    (hQ : Q = MulAut.conj g • S0) (hC : Subgroup.centralizer (S0 : Set G) ≤ S0) :
    Subgroup.centralizer (Q : Set G) ≤ Q := by
  intro x hx
  rw [hQ, Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨g⁻¹ * x * g, hC ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hmem : g * q * g⁻¹ ∈ Q := conj_mem_of_eq_smul hQ hq
    have h := (Subgroup.mem_centralizer_iff.1 hx) (g * q * g⁻¹) hmem
    calc q * (g⁻¹ * x * g) = g⁻¹ * ((g * q * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * q * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * x * g) * q := by group
  · simp only [MulAut.smul_def, MulAut.conj_apply]
    group

theorem center_eq_bot_of_simple_card {S X : Type*} [Group S] [Group X] [Finite X]
    [IsSimpleGroup X] (e : S ≃* X) (hX : ¬ (Nat.card X).Prime) : Subgroup.center S = ⊥ := by
  haveI : IsSimpleGroup S := MulEquiv.isSimpleGroup e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    letI : CommGroup S := Group.commGroupOfCenterEqTop h
    haveI : Finite S := Finite.of_equiv X e.symm.toEquiv
    exact hX (by rw [← Nat.card_congr e.toEquiv]; exact IsSimpleGroup.prime_card)

theorem isPGroup_map_of_equiv {G H : Type*} [Group G] [Group H] (θ : G ≃* H) {p : ℕ}
    {Q : Subgroup G} (hQ : IsPGroup p Q) : IsPGroup p (Q.map θ.toMonoidHom) :=
  IsPGroup.of_surjective hQ (θ.toMonoidHom.subgroupMap Q) (MonoidHom.subgroupMap_surjective _ _)

theorem eq_one_of_sylow_centralizer {S G : Type*} [Group S] [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p ≠ 3) (θ : S ≃* G) (S0 : Sylow p G)
    (hC : Subgroup.centralizer (S0 : Set G) ≤ (S0 : Subgroup G))
    {Q : Subgroup S} (hQ : IsPGroup p Q) (hQcard : Nat.card (S0 : Subgroup G) ≤ Nat.card Q)
    {l : S} (hl3 : l ^ 3 = 1) (hcomm : ∀ g ∈ Q, l * g = g * l) : l = 1 := by
  have hQ'p : IsPGroup p (Q.map θ.toMonoidHom) := isPGroup_map_of_equiv θ hQ
  have hQ'card : Nat.card (Q.map θ.toMonoidHom) = Nat.card Q :=
    Subgroup.card_map_of_injective θ.injective
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_ge S0 (Q.map θ.toMonoidHom) hQ'p (by
    rw [hQ'card]
    exact hQcard)
  have hC' := centralizer_le_of_conj hg hC
  have hlQ : θ l ∈ Subgroup.centralizer ((Q.map θ.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have := hcomm v hv
    change θ v * θ l = θ l * θ v
    rw [← map_mul, ← map_mul, ← this]
  have hmem : θ l ∈ Q.map θ.toMonoidHom := hC' hlQ
  obtain ⟨n, hn⟩ := hQ'p.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (Q.map θ.toMonoidHom)) := by
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three Fact.out).2 (Ne.symm hp3))
  have h1 : θ l = 1 :=
    eq_one_of_pow_three_of_coprime _ hcop hmem (by rw [← map_pow, hl3, map_one])
  exact θ.injective (by rw [h1, map_one])

end CFSG.RankThree.PartTwo.Sec13.F135Last
