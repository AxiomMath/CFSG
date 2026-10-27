module

public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin.F53Mod

open Equiv CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem SecData.o2_comm_mem_iff {n : ℕ} {M : Model n} {K L X : Subgroup G}
    [(L.subgroupOf X).Normal] {Ψ : ↥K →* Perm (Fin n)} {β : M.W →* ↥X ⧸ L.subgroupOf X}
    (h : SecData M K L X Ψ β) {U : Subgroup G} (hLU : L ≤ U) {Y : Subgroup M.W}
    (hYm : Y.map β = (U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X))) {s : G}
    (hs : s ∈ K) :
    (∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ U) ↔ ∀ w : M.W, M.act (Ψ ⟨s, hs⟩) w * w⁻¹ ∈ Y := by
  constructor
  · intro hx w
    obtain ⟨x, hxw⟩ := QuotientGroup.mk_surjective (β w)
    obtain ⟨hax, h1⟩ := h.beta_comm hs hxw.symm
    have hmem : β (M.act (Ψ ⟨s, hs⟩) w * w⁻¹) ∈ Y.map β := by
      rw [hYm, h1]
      exact ⟨⟨s * (x : G) * s⁻¹ * (x : G)⁻¹, hax⟩, Subgroup.mem_subgroupOf.mpr (hx x x.2), rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    rwa [← h.inj hyeq]
  · intro hw x hx
    obtain ⟨w, hwx⟩ := h.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
    obtain ⟨hax, h1⟩ := h.beta_comm hs hwx
    have hmem : β (M.act (Ψ ⟨s, hs⟩) w * w⁻¹) ∈ Y.map β := ⟨_, hw w, rfl⟩
    rw [hYm, h1] at hmem
    obtain ⟨c, hc, hceq⟩ := hmem
    have h2 := mk_eq_iff_mem.mp hceq
    have e : s * x * s⁻¹ * x⁻¹ = (s * x * s⁻¹ * x⁻¹ * (c : G)⁻¹) * (c : G) := by group
    rw [e]
    exact U.mul_mem (hLU h2) (Subgroup.mem_subgroupOf.mp hc)

namespace O2

@[expose] def commIterFO2 (M : Model 5) [Fintype M.W] [DecidableEq M.W]
    (Bf : Finset (Perm (Fin 5))) : ℕ → Finset M.W
  | 0 => Finset.univ
  | i + 1 => spanF (commGensF M Bf (commIterFO2 M Bf i))

theorem mem_commIter_iff_o2 (M : Model 5) [Fintype M.W] [DecidableEq M.W]
    {B : Subgroup (Perm (Fin 5))} {Bf : Finset (Perm (Fin 5))} (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf)
    (i : ℕ) (w : M.W) : w ∈ commIter M B i ↔ w ∈ commIterFO2 M Bf i := by
  induction i generalizing w with
  | zero => simp [commIter, commIterFO2]
  | succ i ih => exact mem_commW_iff M hB ih w

set_option maxRecDepth 100000 in
private theorem orth_l2_table : ∀ τ ∈ S5SylF,
    (∀ y ∈ commIterFO2 orth S5SylF 2, orth.act τ y = y) ↔ τ ∈ S5ThatF := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem orth_quot_table : ∀ τ ∈ S5SylF,
    (∀ w : orth.W, orth.act τ w * w⁻¹ ∈ commIterFO2 orth S5SylF 2) ↔ τ ∈ S5ThatF := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem orth_l2_card : (commIterFO2 orth S5SylF 2).card = 4 := by
  decide +kernel

theorem mem_S5ThatF_iff_eq (σ : Perm (Fin 5)) :
    σ ∈ S5ThatF ↔ σ = 1 ∨ σ = swap 0 2 ∨ σ = swap 1 3 ∨ σ = swap 0 2 * swap 1 3 := by
  unfold S5ThatF
  simp

theorem S5That_comm : ∀ s ∈ S5That, ∀ t ∈ S5That, s * t = t * s := by
  intro s hs t ht
  rw [mem_S5That_iff] at hs ht
  revert s t
  decide +kernel

private theorem cent_swap02 : ∀ s ∈ S5SylF, s * swap 0 2 = swap 0 2 * s → s ∈ S5ThatF := by
  decide +kernel

theorem S5That_centralizer : ∀ s ∈ S5Syl, (∀ t ∈ S5That, s * t = t * s) → s ∈ S5That := by
  intro s hs h
  rw [mem_S5Syl_iff] at hs
  rw [mem_S5That_iff]
  exact cent_swap02 s hs (h (swap 0 2) (by rw [mem_S5That_iff, mem_S5ThatF_iff_eq]; simp))

theorem exists_S5Syl_not_S5That : ∃ τ ∈ S5Syl, τ ∉ S5That := by
  refine ⟨S5g, ?_, ?_⟩
  · rw [mem_S5Syl_iff]; decide +kernel
  · rw [mem_S5That_iff]; decide +kernel

theorem card_S5That : Nat.card S5That = 4 := by
  have h : S5ThatF.card = 4 := by decide +kernel
  rw [← h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight mem_S5That_iff)

private theorem conj_swap02 : S5g * swap (0 : Fin 5) 2 * S5g⁻¹ = swap 1 3 := by decide +kernel

private theorem conj_swap13 : S5g * swap (1 : Fin 5) 3 * S5g⁻¹ = swap 0 2 := by decide +kernel

private theorem sign_swap_mul : Perm.sign (swap (0 : Fin 5) 2 * swap 1 3) = 1 := by
  decide +kernel

private theorem orderOf_swap_mul : orderOf (swap (0 : Fin 5) 2 * swap 1 3) = 2 := by
  have h2 : (swap (0 : Fin 5) 2 * swap 1 3) ^ 2 = 1 := by decide +kernel
  have h1 : swap (0 : Fin 5) 2 * swap 1 3 ≠ 1 := by decide +kernel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 h1

theorem S5That_dichotomy (N : Subgroup (Perm (Fin 5))) (hN : N ≤ S5That)
    (hn : ∀ s ∈ S5Syl, ∀ b ∈ N, s * b * s⁻¹ ∈ N) (h0 : N ≠ ⊥) :
    (Nat.card N = 2 ∧ N ≤ alternatingGroup (Fin 5)) ∨ N = S5That := by
  have hg : S5g ∈ S5Syl := by rw [mem_S5Syl_iff]; decide +kernel
  by_cases hab : swap (0 : Fin 5) 2 ∈ N ∨ swap (1 : Fin 5) 3 ∈ N
  · right
    have ha : swap (0 : Fin 5) 2 ∈ N := by
      rcases hab with h | h
      · exact h
      · have := hn S5g hg _ h
        rwa [conj_swap13] at this
    have hb : swap (1 : Fin 5) 3 ∈ N := by
      have := hn S5g hg _ ha
      rwa [conj_swap02] at this
    refine le_antisymm hN (fun σ hσ => ?_)
    rw [mem_S5That_iff, mem_S5ThatF_iff_eq] at hσ
    rcases hσ with rfl | rfl | rfl | rfl
    · exact N.one_mem
    · exact ha
    · exact hb
    · exact N.mul_mem ha hb
  · left
    push Not at hab
    obtain ⟨ha, hb⟩ := hab
    have hall : ∀ n ∈ N, n = 1 ∨ n = swap 0 2 * swap 1 3 := by
      intro n hnN
      have := hN hnN
      rw [mem_S5That_iff, mem_S5ThatF_iff_eq] at this
      rcases this with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hnN ha
      · exact absurd hnN hb
      · exact Or.inr rfl
    have hc : swap (0 : Fin 5) 2 * swap 1 3 ∈ N := by
      obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h0
      rcases hall n n.2 with h | h
      · exact absurd (Subtype.ext h) hn1
      · rw [← h]; exact n.2
    have hNeq : N = Subgroup.zpowers (swap (0 : Fin 5) 2 * swap 1 3) := by
      apply le_antisymm
      · intro n hnN
        rcases hall n hnN with rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      · exact (Subgroup.zpowers_le).mpr hc
    refine ⟨by rw [hNeq, Nat.card_zpowers, orderOf_swap_mul], fun n hnN => ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases hall n hnN with rfl | rfl
    · exact Equiv.Perm.sign_one
    · exact sign_swap_mul

structure OrthDatum (F L X S₀ U : Subgroup G) where
  Ψ : ↥F →* Perm (Fin 5)
  ker : ∀ a : ↥F, Ψ a = 1 ↔ (a : G) ∈ pCoreOf 2 F
  map_syl : (S₀.subgroupOf F).map Ψ = S5Syl
  kerU : ∀ a : ↥F, (a : G) ∈ S₀ →
    ((∀ u ∈ U, (a : G) * u * (a : G)⁻¹ * u⁻¹ ∈ L) ↔ Ψ a ∈ S5That)
  kerX : ∀ a : ↥F, (a : G) ∈ S₀ →
    ((∀ x ∈ X, (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ U) ↔ Ψ a ∈ S5That)
  odd : ∀ a : ↥F, (a : G) ∈ oTwoRes F ⊔ pCoreOf 2 F ↔ Ψ a ∈ alternatingGroup (Fin 5)

theorem exists_orthDatum [Finite G] {F L X S₀ U : Subgroup G} (h : IsOrthSec F L X)
    (hq : Nonempty (OTwoQuot F ≃* Perm (Fin 5))) (hS : IsSylowTwoOf S₀ F) (hLU : L ≤ U)
    (hUX : U ≤ X) (hn : S₀ ≤ Subgroup.normalizer (U : Set G)) (h4 : L.relIndex U = 4) :
    Nonempty (OrthDatum F L X S₀ U) := by
  have hcs : cSecIn F L X = pCoreOf 2 F := IsModelSec.cSecIn_eq_pCoreOf h hq
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := h
  have hS₀F : S₀ ≤ F := hS.1
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  have hinvU : ∀ k ∈ S₀, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    ((Subgroup.mem_normalizer_iff.mp (hn hk)) u).mp hu
  obtain ⟨Y, hY, hYm⟩ := (hsd'.invariant_iff_sub hS₀F hLU hUX).mp hinvU
  have hYinv : IsInvSub orth S5Syl Y := by rw [← hPS]; exact hY
  have hYcard : Nat.card Y = 4 := by
    have h1 : Nat.card (Y.map β') = Nat.card Y := Subgroup.card_map_of_injective hsd'.inj
    rw [← h1, hYm]
    have hk : (QuotientGroup.mk' (L.subgroupOf X)).ker = L.subgroupOf X :=
      QuotientGroup.ker_mk' _
    rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hUX, h4]
  have hc2 : Nat.card (commIter orth S5Syl 2) = 2 ^ 2 := by
    have h1 : Nat.card (commIter orth S5Syl 2) = (commIterFO2 orth S5SylF 2).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_commIter_iff_o2 orth
        mem_S5Syl_iff 2 w)
    rw [h1, orth_l2_card]
    norm_num
  have hYeq : Y = commIter orth S5Syl 2 :=
    (lemma26 orth (Or.inl rfl) 2 (by norm_num)).unique ⟨hYinv, by rw [hYcard]; norm_num⟩
      ⟨isInvSub_commIter orth S5Syl 2, hc2⟩
  have hmemY : ∀ w, w ∈ Y ↔ w ∈ commIterFO2 orth S5SylF 2 := fun w => by
    rw [hYeq]; exact mem_commIter_iff_o2 orth mem_S5Syl_iff 2 w
  have hmemΨ : ∀ a : ↥F, (a : G) ∈ S₀ → Ψ a ∈ S5SylF := fun a ha => by
    rw [← mem_S5Syl_iff, ← hPS]; exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  refine ⟨{ Ψ := Ψ, ker := ?_, map_syl := hPS, kerU := ?_, kerX := ?_, odd := ?_ }⟩
  · intro a
    rw [← MonoidHom.mem_ker, hkΨ, Subgroup.mem_subgroupOf, hcs]
  · intro a ha
    rw [hsd'.act_trivial_iff hUX hYm a.2, mem_S5That_iff, ← orth_l2_table (Ψ a) (hmemΨ a ha)]
    exact ⟨fun h y hy => h y ((hmemY y).mpr hy), fun h y hy => h y ((hmemY y).mp hy)⟩
  · intro a ha
    rw [hsd'.o2_comm_mem_iff hLU hYm a.2, mem_S5That_iff, ← orth_quot_table (Ψ a) (hmemΨ a ha)]
    exact ⟨fun h w => (hmemY _).mp (h w), fun h w => (hmemY _).mpr (h w)⟩
  · intro a
    have h1 := mem_oTwoRes_sup_iff hθs hθk a.2
    rw [hcs] at h1
    rw [h1, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.mem_alternatingGroup, hsgn]

end O2

end CFSG.Quasithin.F53Mod
