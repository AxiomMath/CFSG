module

public import CFSG.LocalAnalysis.QuasithinUnique.AGFusion

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.RankTwoShapes

variable {G : Type*} [Group G] [Finite G]

theorem fusion_chain_of_ag {T N N' : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hAG : ∀ D : Subgroup G, IsAGMember T D → Subgroup.normalizer (D : Set G) ≤ N ∨
      Subgroup.normalizer (D : Set G) ≤ N')
    {x g : G} (hx : x ∈ T) (hxg : g⁻¹ * x * g ∈ T) :
    Relation.ReflTransGen (fun a b : G => a ∈ T ∧ b ∈ T ∧
      ((∃ m ∈ N, m * a * m⁻¹ = b) ∨ (∃ m ∈ N', m * a * m⁻¹ = b))) x (g⁻¹ * x * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hx1 : x = 1
  · subst hx1
    simp only [mul_one, inv_mul_cancel]
    exact Relation.ReflTransGen.refl
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let S : Sylow 2 G := hT.2.1.toSylow hT2
  have hP : Subgroup.zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hx
  have hxg' : g⁻¹ * x * g ∈ (S : Subgroup G) := hxg
  have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hxg')
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  have hxP : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  have key : ∀ c : G, AlperinDecomposition 2 (S : Subgroup G) (Subgroup.zpowers x) c →
      c⁻¹ * x * c ∈ T ∧ Relation.ReflTransGen (fun a b : G => a ∈ T ∧ b ∈ T ∧
        ((∃ m ∈ N, m * a * m⁻¹ = b) ∨ (∃ m ∈ N', m * a * m⁻¹ = b))) x (c⁻¹ * x * c) := by
    intro c hc
    induction hc with
    | one =>
      simp only [inv_one, one_mul, mul_one]
      exact ⟨hx, Relation.ReflTransGen.refl⟩
    | @step c n Q _ hQ hPQ hn ih =>
      obtain ⟨hcT, hchain⟩ := ih
      have hxQ : c⁻¹ * x * c ∈ Q := by
        have := hPQ ⟨x, hxP, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using this
      have hQ1 : Q ≠ ⊥ := by
        intro hQ0
        rw [hQ0, Subgroup.mem_bot] at hxQ
        apply hx1
        have h1 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
        rw [← h1, hxQ]
        group
      have hAGQ := isAGMember_of_isAlperinSubgroup hT hQ hQ1
      have hQT : Q ≤ T := hAGQ.1
      have hy : n⁻¹ * (c⁻¹ * x * c) * n ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) (c⁻¹ * x * c)).1 hxQ
        simpa [mul_assoc] using this
      have hstep : c⁻¹ * x * c ∈ T ∧ n⁻¹ * (c⁻¹ * x * c) * n ∈ T ∧
          ((∃ m ∈ N, m * (c⁻¹ * x * c) * m⁻¹ = n⁻¹ * (c⁻¹ * x * c) * n) ∨
            (∃ m ∈ N', m * (c⁻¹ * x * c) * m⁻¹ = n⁻¹ * (c⁻¹ * x * c) * n)) := by
        refine ⟨hcT, hQT hy, ?_⟩
        rcases hAG Q hAGQ with h | h
        · exact Or.inl ⟨n⁻¹, h (Subgroup.inv_mem _ hn), by simp [mul_assoc]⟩
        · exact Or.inr ⟨n⁻¹, h (Subgroup.inv_mem _ hn), by simp [mul_assoc]⟩
      have e : (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
      rw [e]
      exact ⟨hQT hy, hchain.tail hstep⟩
  obtain ⟨-, hchain⟩ := key c hc
  rwa [hcg x hxP] at hchain

end CFSG.Quasithin.H13.F431.Un
