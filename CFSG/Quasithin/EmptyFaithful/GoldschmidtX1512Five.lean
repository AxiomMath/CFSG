module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Syl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Shape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G] [Finite G]

theorem card_img_mul_card_fix {n : ℕ} (hn : n = 3 ∨ n = 5) {T P H U L N A : Subgroup G}
    [(L.subgroupOf N).Normal] (c : ShapeCtx T P H U L N A)
    {θ : ↥H →* Equiv.Perm (Fin n)} {β : ↥(G6.coreMod n) →* ↥N ⧸ L.subgroupOf N}
    (hker : θ.ker = (cSecIn H L N).subgroupOf H) (hM : NatMod n H L N θ β) :
    Nat.card ((A.subgroupOf H).map θ) * Nat.card (fixΔ n ((A.subgroupOf H).map θ)) =
      2 ^ (n - 1) := by
  have hLN : L ≤ N := c.step.2.2.1.le
  have hAH : A ≤ H := c.le.trans c.mp.isSylow.1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_forall c.step.2.1.2
  have hAC : A ⊓ cSecIn H L N = A ⊓ pCoreOf 2 H := (inf_cSecIn_eq hAH hHL).trans c.count.1
  have h1 := card_eq_inf_mul_card_map hker hAH
  rw [hAC] at h1
  have h2 := c.count.2
  have hq : 0 < Nat.card ↥(A ⊓ pCoreOf 2 H) := Nat.card_pos
  have hf : 0 < Nat.card (fixSecIn A L N) := Nat.card_pos
  have h3 : Nat.card ((A.subgroupOf H).map θ) * Nat.card (fixSecIn A L N) = Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_left hq
    calc Nat.card ↥(A ⊓ pCoreOf 2 H) * (Nat.card ((A.subgroupOf H).map θ) *
          Nat.card (fixSecIn A L N))
        = (Nat.card ↥(A ⊓ pCoreOf 2 H) * Nat.card ((A.subgroupOf H).map θ)) *
          Nat.card (fixSecIn A L N) := by ring
      _ = Nat.card A * Nat.card (fixSecIn A L N) := by rw [← h1]
      _ = Nat.card ↥(A ⊓ pCoreOf 2 H) * Nat.card N := h2
  have hfN : fixSecIn A L N ≤ N := (Subgroup.closure_le N).mpr fun x hx => hx.1
  have h4 := Subgroup.relIndex_mul_card (H := fixSecIn A L N) (K := N)
  rw [inf_eq_left.mpr hfN] at h4
  have h5 : (fixSecIn A L N).relIndex N = Nat.card ((A.subgroupOf H).map θ) :=
    Nat.eq_of_mul_eq_mul_right hf (h4.trans h3.symm)
  have h6 := relIndex_fixSecIn_eq hM hLN hAH
  rw [h5] at h6
  have h7 := Subgroup.card_mul_index (fixΔ n ((A.subgroupOf H).map θ))
  rw [← h6, card_coreMod hn] at h7
  rw [mul_comm]
  exact h7

theorem shapeDatum_nat {n : ℕ} (hn : n = 3 ∨ n = 5) {T P H U L N A : Subgroup G}
    [(L.subgroupOf N).Normal] (c : ShapeCtx T P H U L N A)
    (hK : ¬ oTwoUpper H ≤ cSecIn H L N) (hNat : NaturalSn n H L N) :
    ShapeDatum H P (cSecIn H L N) A := by
  obtain ⟨θ, β, hθs, hker, hM⟩ := natMod_of_naturalSn hn hNat
  have hTH : T ≤ H := c.mp.isSylow.1
  have hAH : A ≤ H := c.le.trans hTH
  obtain ⟨hCP, -⟩ := le_and_isSylow c.mp (S152Fin.cSecIn_le_left H L N) c.normalizes c.pCoreOf_le hK
  have hD : IsSylowTwoOf ((T.subgroupOf H).map θ) ⊤ :=
    sylow_map_top θ hθs (sylow_subgroupOf_top c.mp.isSylow)
  have hDcard := card_sylow_perm hn hD
  have hBD : (A.subgroupOf H).map θ ≤ (T.subgroupOf H).map θ := by
    refine Subgroup.map_mono fun a ha => ?_
    exact Subgroup.mem_subgroupOf.mpr (c.le (Subgroup.mem_subgroupOf.mp ha))
  have hBe : IsElemAbelian 2 ((A.subgroupOf H).map θ) := isElemAbelian_map_subgroupOf θ c.abelian
  have hcount := card_img_mul_card_fix hn c hker hM
  have hBne : (A.subgroupOf H).map θ ≠ ⊥ := by
    obtain ⟨a₁, ha₁A, ha₁Q⟩ := Set.not_subset.mp c.offender
    have ha₁C : a₁ ∉ cSecIn H L N := c.not_mem_of_not_mem hK ha₁A ha₁Q
    intro hB
    apply ha₁C
    have h1 : θ ⟨a₁, hAH ha₁A⟩ ∈ (A.subgroupOf H).map θ :=
      ⟨⟨a₁, hAH ha₁A⟩, Subgroup.mem_subgroupOf.mpr ha₁A, rfl⟩
    rw [hB, Subgroup.mem_bot] at h1
    have h2 : (⟨a₁, hAH ha₁A⟩ : ↥H) ∈ θ.ker := h1
    rw [hker] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  obtain ⟨ξ, hξ3, hξ1, hξnorm, hξinv, hξcl⟩ :=
    (fin_main hn hDcard hBD hBe).2 hcount hBne
  obtain ⟨xh, hxh⟩ := hθs ξ
  obtain ⟨hx3, hxA, hxinv⟩ := datum_conditions hker hAH xh (by rw [hxh]; exact hξ3)
    (fun g hg => by rw [hxh]; exact hξnorm g hg) (by rw [hxh]; exact hξinv)
  refine ⟨(xh : G), xh.2, ?_, hx3, hxA, hxinv⟩
  intro hxP
  have hsub : ({ξ} ∪ ((T.subgroupOf H).map θ : Set (Equiv.Perm (Fin n)))) ⊆
      ((P.subgroupOf H).map θ : Subgroup (Equiv.Perm (Fin n))) := by
    rintro _ (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨xh, Subgroup.mem_subgroupOf.mpr hxP, hxh⟩
    · exact ⟨t, Subgroup.mem_subgroupOf.mpr (c.mp.le (Subgroup.mem_subgroupOf.mp ht)), rfl⟩
  have htop : (P.subgroupOf H).map θ = ⊤ := by
    rw [eq_top_iff, ← hξcl]
    exact (Subgroup.closure_le _).mpr hsub
  exact lt_irrefl _ (lt_of_lt_of_le c.mp.maximal.1 (le_of_map_eq_top hker hCP htop))

end X1512

end CFSG.Quasithin
