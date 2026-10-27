module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Two

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph
open scoped Pointwise

local notation "pval" => CFSG.Quasithin.Fan86.valence

theorem exists_subgroup_mul_of_swap {G : Type*} [Group G] (A B : Subgroup G)
    (h : ∀ b ∈ B, ∀ a ∈ A, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') :
    ∃ T : Subgroup G, (T : Set G) = (A : Set G) * (B : Set G) := by
  refine ⟨{ carrier := (A : Set G) * (B : Set G)
            one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    obtain ⟨a', ha', b', hb', e⟩ := h b₁ hb₁ a₂ ha₂
    refine ⟨a₁ * a', A.mul_mem ha₁ ha', b' * b₂, B.mul_mem hb' hb₂, ?_⟩
    calc a₁ * a' * (b' * b₂) = a₁ * (a' * b') * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [e]
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', ha', b', hb', e⟩ := h b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha)
    exact ⟨a', ha', b', hb', by rw [mul_inv_rev, e]⟩

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace XSetup

variable {F : FanTree Γ G} {α β : V} {x : G} (S : XSetup F α β x)

include S

theorem false_of_comm (L : LocalFacts F) (h32 : Fan32 F) {U : Subgroup G}
    (hUα : U ≤ MulAction.stabilizer G α) (hUn : (U.subgroupOf (MulAction.stabilizer G α)).Normal)
    (hUβ : U ≤ nbrStab Γ G β) (hcomm : ∀ g ∈ nbrStab Γ G α, x * g * x⁻¹ * g⁻¹ ∈ U) : False := by
  have hnorm : MulAction.stabilizer G α ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUα).1 hUn
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := hnorm S.mem
  have hA : ∀ k ∈ MulAction.stabilizer G α, ∃ (i : ℕ) (u : G), u ∈ U ∧ k * x * k⁻¹ = x ^ i * u := by
    intro k hk
    obtain ⟨i, k', hk', hkk'⟩ := L.conj_mem S.mem S.ord hk
    refine ⟨i, k', ?_, hkk'⟩
    obtain ⟨m, hm⟩ := (F.nbrStab_isPGroup α) ⟨k', hk'⟩
    refine mem_of_commute_mod (i := i) U hxU (hnorm (F.nbrStab_le_stabilizer α hk'))
      (F.odd_valence α) S.pow_valence_eq_one (congrArg Subtype.val hm) (hcomm k' hk') ?_
    rw [← hkk']
    have : (k * x * k⁻¹) ^ pval Γ α = 1 := by
      rw [conj_pow, S.pow_valence_eq_one]
      group
    rw [this]
    exact U.one_mem
  have hswap : ∀ b ∈ U, ∀ a ∈ Subgroup.zpowers x, ∃ a' ∈ Subgroup.zpowers x, ∃ b' ∈ U,
      b * a = a' * b' := by
    intro b hb a ha
    have han : a ∈ Subgroup.normalizer (U : Set G) := (Subgroup.zpowers_le.2 hxU) ha
    refine ⟨a, ha, a⁻¹ * b * a, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem han) b).1 hb
    simpa using this
  obtain ⟨T, hT⟩ := exists_subgroup_mul_of_swap (Subgroup.zpowers x) U hswap
  have hxT : ∀ k ∈ nbrStab Γ G β, k * x * k⁻¹ ∈ T := by
    intro k hk
    obtain ⟨i, u, hu, e⟩ := hA k (F.nbrStab_le_edge β S.adj.symm hk).2
    have : k * x * k⁻¹ ∈ (T : Set G) := by
      rw [hT, e]
      exact ⟨x ^ i, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i, u, hu, rfl⟩
    exact this
  have hC : ∀ k ∈ nbrStab Γ G β, ∀ a ∈ Subgroup.zpowers x, ∃ a' ∈ Subgroup.zpowers x,
      ∃ k' ∈ nbrStab Γ G β, k * a = a' * k' := by
    intro k hk a ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hmem : k * x ^ j * k⁻¹ ∈ T := by
      have := T.zpow_mem (hxT k hk) j
      rwa [conj_zpow] at this
    have hmem' : k * x ^ j * k⁻¹ ∈ (T : Set G) := hmem
    rw [hT] at hmem'
    obtain ⟨c, hc, u, hu, hcu⟩ := hmem'
    refine ⟨c, hc, u * k, (nbrStab Γ G β).mul_mem (hUβ hu) hk, ?_⟩
    calc k * x ^ j = (k * x ^ j * k⁻¹) * k := by group
      _ = (c * u) * k := by rw [← hcu]
      _ = c * (u * k) := by group
  obtain ⟨H, hH⟩ := exists_subgroup_mul_of_swap (Subgroup.zpowers x) (nbrStab Γ G β) hC
  exact F.not_pclosed α ((h32 α β S.adj x S.mem S.ord).1 ⟨H, hH⟩)

end XSetup

theorem fan_3_3 {F : FanTree Γ G} (L : LocalFacts F) (h32 : Fan32 F) : Fan33 F := by
  intro α β hαβ x hx hord
  have S : XSetup F α β x := ⟨hαβ, hx, hord⟩
  have hnp := F.not_pclosed α
  have hii : ¬ Fan33ii Γ α β x := by
    rintro ⟨U, hUα, hUn, hUβ, hcomm⟩
    exact S.false_of_comm L h32 hUα hUn hUβ hcomm
  have hi : ¬ (nbrStab Γ G α ⊓ nbrStab Γ G β = ballStab Γ G 2 α) := by
    intro h
    refine hii ⟨ballStab Γ G 2 α, ?_, F.normal_ballStab_two α, ?_, S.comm_mod_of_inf_eq L h⟩
    · exact fun g hg => F.nbrStab_le_stabilizer α ((F.ballStab_two_le_inf hαβ hg).1)
    · exact fun g hg => (F.ballStab_two_le_inf hαβ hg).2
  exact ⟨⟨fun h => (hi h).elim, fun h => (hii h).elim⟩,
    ⟨fun h => (hii h).elim, fun h => (hnp h).elim⟩, fun h => (hnp h).elim⟩

end CFSG.Quasithin.Fan86
