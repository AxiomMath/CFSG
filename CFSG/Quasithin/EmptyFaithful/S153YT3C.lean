module

public import CFSG.Quasithin.EmptyFaithful.S153YT3B

public section

namespace CFSG.Quasithin.YG

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] {I S K₀ K₁ M₀ : Subgroup G}

namespace A3Pair

variable [Finite G] (c : A3Pair I S K₀ K₁)
include c

theorem comm_mem_blockU_of_centralizes {j : G} (hjN : j ∈ Subgroup.normalizer (K₀ : Set G))
    (hj : ∀ u ∈ blockU K₀, j * u = u * j) {k : G} (hk : k ∈ K₀) :
    k * j * k⁻¹ * j⁻¹ ∈ blockU K₀ := by
  have hwK : k * j * k⁻¹ * j⁻¹ ∈ K₀ := by
    have h1 : j * k⁻¹ * j⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.1 hjN k⁻¹).1 (K₀.inv_mem hk)
    have := K₀.mul_mem hk h1
    simpa [mul_assoc] using this
  refine c.a4₀.mem_of_centralizes hwK fun u hu => ?_
  have hu₁ : k⁻¹ * u * k ∈ blockU K₀ := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU K₀ (K₀.inv_mem hk)) u).1 hu
    simpa using h1
  have e1 : j⁻¹ * u = u * j⁻¹ := by
    calc j⁻¹ * u = j⁻¹ * (u * j) * j⁻¹ := by group
      _ = j⁻¹ * (j * u) * j⁻¹ := by rw [hj u hu]
      _ = u * j⁻¹ := by group
  have e3 : j * (k⁻¹ * u * k) = (k⁻¹ * u * k) * j := hj _ hu₁
  have e4 : k * (k⁻¹ * u * k) = u * k := by group
  calc k * j * k⁻¹ * j⁻¹ * u = k * j * k⁻¹ * (j⁻¹ * u) := by group
    _ = k * j * (k⁻¹ * u) * j⁻¹ := by rw [e1]; group
    _ = k * j * ((k⁻¹ * u * k) * k⁻¹) * j⁻¹ := by group
    _ = k * (j * (k⁻¹ * u * k)) * k⁻¹ * j⁻¹ := by group
    _ = k * ((k⁻¹ * u * k) * j) * k⁻¹ * j⁻¹ := by rw [e3]
    _ = (k * (k⁻¹ * u * k)) * j * k⁻¹ * j⁻¹ := by group
    _ = (u * k) * j * k⁻¹ * j⁻¹ := by rw [e4]
    _ = u * (k * j * k⁻¹ * j⁻¹) := by group

theorem not_thompsonJ_le_pCoreOf (hM₀ : M₀ ≤ Subgroup.normalizer (S : Set G))
    (hb : C5.NoCommonNormal S I M₀) : ¬ thompsonJ S ≤ pCoreOf 2 I := by
  intro hJ
  have hQS : pCoreOf 2 I ≤ S := c.sylow.pCoreOf_le
  have hJQ : thompsonJ (pCoreOf 2 I) = thompsonJ S := GammaExtra.thompsonJ_eq_of_le hJ hQS
  have hM₀J : M₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    hM₀.trans (GammaExtra.normalizer_le_normalizer_thompsonJ S)
  have hIJ : I ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← hJQ]
    exact (le_normalizer_pCoreOf 2 I).trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hJne : thompsonJ S ≠ ⊥ := by
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
    intro hbot
    have hAbot : A = ⊥ := le_bot_iff.mp (hbot ▸ GammaExtra.le_thompsonJ hA)
    have h4 : Nat.card (blockU K₀) ≤ Nat.card A :=
      hA.2.2 (blockU K₀) c.U₀_le_S c.isElemAbelian_blockU₀
    rw [c.card_blockU₀, hAbot, Subgroup.card_bot] at h4
    omega
  exact hb (thompsonJ S) (GammaExtra.thompsonJ_le_self S) hJne hIJ hM₀J

end A3Pair

theorem thompson_a3_pair {G : Type} [Group G] [Finite G] {I S M₀ K₀ K₁ : Subgroup G}
    (hS : IsSylowTwoOf S I) (hK₀ : IsBlock2 I K₀) (hK₁ : IsBlock2 I K₁)
    (h₀ : IsAltType K₀ 3) (h₁ : IsAltType K₁ 3)
    (hcomm : ∀ a ∈ K₀, ∀ b ∈ K₁, a * b = b * a)
    (hperm₀ : ∀ t ∈ S, B6.conjSub t K₀ = K₀ ∨ B6.conjSub t K₀ = K₁)
    (hperm₁ : ∀ t ∈ S, B6.conjSub t K₁ = K₀ ∨ B6.conjSub t K₁ = K₁)
    (hgen : I = S ⊔ (K₀ ⊔ K₁))
    (htrans : ∃ t ∈ S, B6.conjSub t K₀ = K₁)
    (hM₀ : M₀ ≤ Subgroup.normalizer (S : Set G))
    (hb : C5.NoCommonNormal S I M₀) :
    ⁅K₀, thompsonJ S⁆ = K₀ := by
  have c : A3Pair I S K₀ K₁ := ⟨hS, hK₀, hK₁, h₀, h₁, hcomm, hperm₀, hperm₁, hgen⟩
  obtain ⟨t, htS, htK⟩ := htrans
  set J := thompsonJ S with hJdef
  have hJ₀ : J ≤ Subgroup.normalizer (K₀ : Set G) := c.thompsonJ_le_normalizer
  have hJS : J ≤ S := GammaExtra.thompsonJ_le_self S
  have hJU : J ≤ Subgroup.normalizer (blockU K₀ : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (hJ₀ hg)
  have hJn : ∀ g ∈ S, ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.1 (GammaExtra.normalizer_le_normalizer_thompsonJ S
      (Subgroup.le_normalizer hg)) j).1 hj
  by_cases hJC : J ≤ Subgroup.centralizer (blockU K₀ : Set G)
  · exfalso
    have hJcomm : ∀ j ∈ J, ∀ v ∈ blockU K₀, j * v = v * j := fun j hj v hv =>
      (Subgroup.mem_centralizer_iff.1 (hJC hj) v hv).symm
    have h₀' : ∀ j ∈ J, ∀ k ∈ K₀, k * j * k⁻¹ * j⁻¹ ∈ blockU K₀ := fun j hj k hk =>
      c.comm_mem_blockU_of_centralizes (hJ₀ hj) (hJcomm j hj) hk
    have h₁' : ∀ j ∈ J, ∀ k ∈ K₁, k * j * k⁻¹ * j⁻¹ ∈ blockU K₁ := by
      intro j hj k hk
      have hk' : k ∈ B6.conjSub t K₀ := by rw [htK]; exact hk
      have hk₀ : t⁻¹ * k * t ∈ K₀ := B6.mem_conjSub.1 hk'
      have hj' : t⁻¹ * j * t ∈ J := by
        have := hJn t⁻¹ (S.inv_mem htS) j hj
        simpa using this
      have := mem_blockU_conj_of_conjSub_eq htK (h₀' _ hj' _ hk₀)
      convert this using 1
      group
    have hJQ : J ≤ pCoreOf 2 I := fun j hj =>
      c.mem_pCoreOf_of_comm_blockU (hJS hj) (h₀' j hj) (h₁' j hj)
    exact c.not_thompsonJ_le_pCoreOf hM₀ hb hJQ
  · exact c.a4₀.commutator_eq (hS.isPGroup.to_le hJS) hJ₀ hJU hJC

end CFSG.Quasithin.YG
