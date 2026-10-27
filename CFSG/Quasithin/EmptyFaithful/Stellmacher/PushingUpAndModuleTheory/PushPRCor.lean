module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRProp

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X P Z : Subgroup G}

theorem commutator_ne_bot_of_not_le (h : PushHyp X P Z) {y : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hle : ¬ cj y Z ≤ pCoreOf 2 X) :
    ⁅Z, cj y Z⁆ ≠ ⊥ := by
  intro hbot
  apply hle
  intro b hb
  rw [← h.inf_centralizer_eq]
  refine ⟨cj_le_of_le_of_mem_normalizer hy h.Z_le hb, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.commutator_mem_commutator ha hb
  rw [Subgroup.mem_bot, commutatorElement_def] at this
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

theorem two_dvd_relIndex {H₀ Q : Subgroup G} {g : G} (hg : g ∈ H₀)
    (hgg : g * g ∈ Subgroup.normalizer (Q : Set G)) (hg1 : g ∉ Subgroup.normalizer (Q : Set G))
    (hn : ∀ n ∈ H₀, n ∈ Subgroup.normalizer (Q : Set G) →
      n ∈ Subgroup.normalizer ((cj g Q : Subgroup G) : Set G)) :
    2 ∣ (Subgroup.normalizer (Q : Set G) ⊓ H₀).relIndex H₀ := by
  set N0 : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ H₀ with hN0
  have hcj : cj g⁻¹ N0 ≤ N0 := by
    intro x hx
    rw [mem_cj] at hx
    simp only [inv_inv] at hx
    have h1 := hn _ hx.2 hx.1
    rw [mem_normalizer_cj_iff] at h1
    refine ⟨?_, ?_⟩
    · have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h1
    · have := H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hg) hx.2) hg
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at this
  have hgN : g ∈ Subgroup.normalizer (N0 : Set G) := by
    have := mem_normalizer_of_cj_le hcj
    simpa using Subgroup.inv_mem _ this
  set T : Subgroup G := Subgroup.normalizer (N0 : Set G) ⊓ H₀ with hT
  have hN0T : N0 ≤ T := le_inf Subgroup.le_normalizer inf_le_right
  have hTH : T ≤ H₀ := inf_le_right
  have hnorm : (N0.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0T).mpr inf_le_left
  have hgT : g ∈ T := ⟨hgN, hg⟩
  have hgN0 : g ∉ N0 := fun hh => hg1 hh.1
  have hgg0 : g * g ∈ N0 := ⟨hgg, H₀.mul_mem hg hg⟩
  let ĝ : ↥T ⧸ N0.subgroupOf T := QuotientGroup.mk ⟨g, hgT⟩
  have hsq : ĝ ^ 2 = 1 := by
    show (QuotientGroup.mk (⟨g, hgT⟩ : ↥T) : ↥T ⧸ N0.subgroupOf T) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa [pow_two] using hgg0)
  have hne : ĝ ≠ 1 := by
    intro h1
    have := (QuotientGroup.eq_one_iff _).mp h1
    exact hgN0 (Subgroup.mem_subgroupOf.mp this)
  have hord : orderOf ĝ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hsq hne
  have hdvd : 2 ∣ N0.relIndex T := by
    have := orderOf_dvd_natCard ĝ
    rw [hord] at this
    unfold Subgroup.relIndex
    rwa [Subgroup.index_eq_card]
  exact hdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex N0 T H₀ hN0T hTH))

theorem cor42_cj_le (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z)
    {H₀ : Subgroup G} (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G))
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    ∀ g ∈ H₀, cj g Z ≤ pCoreOf 2 X := by
  intro g hg
  by_contra hle
  have hne := commutator_ne_bot_of_not_le h (hH₀ hg) hle
  obtain ⟨h1, h2, h3, h4⟩ := prop41 h hB hN (hH₀ hg) hne
  have := two_dvd_relIndex hg h1 h2 (fun n hn hnQ => h4 n (hH₀ hn) hnQ)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)

theorem cor42_join_le (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z)
    {H₀ : Subgroup G} (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G))
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    conjJoinOf H₀ Z ≤ pCoreOf 2 X :=
  iSup₂_le fun g hg => cor42_cj_le h hB hN hH₀ hodd g hg

theorem le_normalizer_of_core (h : PushHyp X P Z) (hB : BaumannC X Z) {H₀ : Subgroup G}
    (hP : P ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G))
    (hle : conjJoinOf H₀ Z ≤ pCoreOf 2 X) (hZ : Z ≤ conjJoinOf H₀ Z) :
    X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G) := by
  have hL : pResidualOf 2 X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G) := by
    intro l hl
    have hfwd : ∀ l ∈ pResidualOf 2 X, ∀ s ∈ conjJoinOf H₀ Z, l * s * l⁻¹ ∈ conjJoinOf H₀ Z := by
      intro l hl s hs
      have h1 : ⁅l, s⁆ ∈ ⁅pResidualOf 2 X, pCoreOf 2 X⁆ :=
        Subgroup.commutator_mem_commutator hl (hle hs)
      rw [Subgroup.commutator_comm] at h1
      have h2 := hZ (hB h1)
      have e : l * s * l⁻¹ = ⁅l, s⁆ * s := by simp only [commutatorElement_def]; group
      rw [e]
      exact (conjJoinOf H₀ Z).mul_mem h2 hs
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨hfwd l hl s, fun hs => ?_⟩
    have := hfwd l⁻¹ ((pResidualOf 2 X).inv_mem hl) _ hs
    simpa [mul_assoc] using this
  have := sup_le hL hP
  rw [pResidualOf_sup_eq_of_sylow h.sylow] at this
  exact this

theorem cor42 (h : PushHyp X P Z) (hB : BaumannC X Z) (hN : NatFacts X P Z)
    {H₀ : Subgroup G} (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G)) (hPH : P ≤ H₀)
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    Cor42Concl X Z H₀ := by
  have hle := cor42_join_le h hB hN hH₀ hodd
  refine ⟨hle, le_normalizer_of_core h hB ?_ hle ?_⟩
  · exact hPH.trans (le_normalizer_conjJoin H₀ Z)
  · exact (cj_one Z).symm.le.trans (cj_le_conjJoin H₀.one_mem)

end CFSG.Quasithin.F53Push
