module

public import CFSG.RankThree.GF2n.Tim79aOddTranspRoot
public import CFSG.RankThree.GF2n.Tim81.Cited.Sec6
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Connectivity

section RootSubgroups

variable {K : Type} [Group K] {D : Set K}

theorem conjSub_closure_rootSet (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup K D) (d g : K)
    (hd : d ∈ D) :
    CFSG.Timmesfeld.ARS.conjSub (Subgroup.closure (CFSG.Timmesfeld.rootSet D d)) g =
      Subgroup.closure (CFSG.Timmesfeld.rootSet D (g * d * g⁻¹)) :=
  (rootGroup_conj ⟨d, hS.eq_setOf_isConj hd⟩ g d).symm

private theorem mul_self_of_mem (hD : IsOddTransp D) {d a : K} (hd : d ∈ D)
    (ha : a ∈ Subgroup.closure (rootSet D d)) : a * a = 1 :=
  mul_self_eq_one_of_mem_closure (pairwise_commute_rootSet hd)
    (fun _ hx => hD.mul_self_eq_one hx.1) ha

private theorem commuting_iff {d f : K} (hd : d ∈ D) (hf : f ∈ D) :
    Commuting (Subgroup.closure (rootSet D d)) (Subgroup.closure (rootSet D f)) ↔
      Commute d f :=
  ⟨fun h => h d (Subgroup.subset_closure (mem_rootSet_self hd)) f
      (Subgroup.subset_closure (mem_rootSet_self hf)),
    fun hdf _ ha _ hb => commute_of_mem_rootGroup_of_commute' hf ha hb hdf⟩

theorem four_le_card_closure_rootSet [Finite K] (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup K D)
    (hsq : ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) (d : K) (hd : d ∈ D) :
    4 ≤ Nat.card (Subgroup.closure (CFSG.Timmesfeld.rootSet D d)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, v, hv, huv, hc, hw⟩ := hsq
  have hvr : v ∈ rootSet D u := mem_rootSet_of_mul_mem hS.oddT hu hv hc hw
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hu hd)
  rw [← conjSub_closure_rootSet hS u g hu,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hsub : ({1, u, v} : Set K) ⊆ (Subgroup.closure (rootSet D u) : Set K) := by
    intro w hw
    rcases hw with h | h | h
    · rw [h]
      exact (Subgroup.closure (rootSet D u)).one_mem
    · rw [h]
      exact Subgroup.subset_closure (mem_rootSet_self hu)
    · rw [Set.mem_singleton_iff.1 h]
      exact Subgroup.subset_closure hvr
  have h3 : ({1, u, v} : Set K).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, u, v, (hS.oddT.ne_one hu).symm, (hS.oddT.ne_one hv).symm, huv, rfl⟩
  have hle : 3 ≤ Nat.card (Subgroup.closure (rootSet D u)) := by
    rw [← h3, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_closure_of_pairwise
    (pairwise_commute_rootSet hu) (fun _ hx => hS.oddT.mul_self_eq_one hx.1))
  rw [hk] at hle ⊢
  rcases k with _ | _ | k
  · norm_num at hle
  · norm_num at hle
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem closure_rootSet_eq {d x : K} (hx : x ∈ D)
    (h : ∀ f ∈ D, Commute d f ↔ Commute x f) :
    Subgroup.closure (rootSet D d) = Subgroup.closure (rootSet D x) := by
  rw [rootSet_eq_of_mem (⟨hx, fun f hf => (h f hf).symm⟩ : x ∈ rootSet D d)]

private theorem isTransvectionClass (hS : Setup K D)
    (hL2 : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x →
      Tim81.IsL2Gen (Subgroup.closure (rootSet D d)) (Subgroup.closure (rootSet D x))) :
    IsTransvectionClass {A | ∃ d ∈ D, A = Subgroup.closure (rootSet D d)} := by
  have hD := hS.oddT
  have hroot : IsRootClass {A | ∃ d ∈ D, A = Subgroup.closure (rootSet D d)} := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨d₀, hd₀⟩ := hS.nonempty
      refine ⟨Subgroup.closure (rootSet D d₀), Set.ext fun A => ⟨?_, ?_⟩⟩
      · rintro ⟨d, hd, rfl⟩
        obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd₀ hd)
        exact ⟨g, conjSub_closure_rootSet hS d₀ g hd₀⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g * d₀ * g⁻¹, hS.conj_mem g hd₀, conjSub_closure_rootSet hS d₀ g hd₀⟩
    · rintro A ⟨d, hd, rfl⟩ h
      have h1 : d ∈ Subgroup.closure (rootSet D d) :=
        Subgroup.subset_closure (mem_rootSet_self hd)
      rw [h, Subgroup.mem_bot] at h1
      exact hD.ne_one hd h1
    · rintro A ⟨d, hd, rfl⟩ a ha
      exact mul_self_of_mem hD hd ha
    · rintro A ⟨d, hd, rfl⟩ B ⟨x, hx, rfl⟩ -
      by_cases hdx : Commute d x
      · exact Or.inl ((commuting_iff hd hx).2 hdx)
      · exact Or.inr (Or.inl (hL2 d hd x hx hdx).opposite)
    · rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
      intro d hd
      exact (le_iSup₂ (f := fun A (_ : A ∈ {A | ∃ d ∈ D, A = Subgroup.closure (rootSet D d)}) =>
        A) (Subgroup.closure (rootSet D d)) ⟨d, hd, rfl⟩)
        (Subgroup.subset_closure (mem_rootSet_self hd))
  refine ⟨hroot, ?_⟩
  rintro A ⟨d, hd, rfl⟩ B ⟨x, hx, rfl⟩ hsp
  by_cases hdx : Commute d x
  · exact hroot.ne_bot _ hsp.1
      (commuting_iff_commutator_eq_bot.1 ((commuting_iff hd hx).2 hdx))
  · exact (hL2 d hd x hx hdx).not_special _ hsp

private theorem exists_commuting (hS : Setup K D) (hZ : Subgroup.center K = ⊥)
    (hconn : ¬ Disconnected D) :
    ∃ A ∈ {A | ∃ d ∈ D, A = Subgroup.closure (rootSet D d)},
      ∃ B ∈ {A | ∃ d ∈ D, A = Subgroup.closure (rootSet D d)}, A ≠ B ∧ Commuting A B := by
  by_contra hno
  have hstep : ∀ e ∈ D, ∀ e' ∈ D, Commute e e' → e' ∈ rootSet D e := by
    intro e he e' he' hee'
    by_contra hn
    refine hno ⟨_, ⟨e, he, rfl⟩, _, ⟨e', he', rfl⟩, fun heq => hn ?_,
      (commuting_iff he he').2 hee'⟩
    refine ⟨he', fun f hf => ?_⟩
    rw [← commuting_iff he' hf, ← heq, commuting_iff he hf]
  obtain ⟨u, hu⟩ := hS.nonempty
  have hall : ∀ x ∈ D, x ∈ rootSet D u := by
    intro x hx
    have hreach : Reach D u x := by
      by_contra h
      exact hconn ⟨u, hu, x, hx, h⟩
    refine mem_of_reach (S := rootSet D u) ?_ (mem_rootSet_self hu) hreach
    intro y hy z hz hyz
    rw [← rootSet_eq_of_mem hy]
    exact hstep y hy.1 z hz hyz
  have hle : Subgroup.closure D ≤ Subgroup.centralizer {u} := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (((hall x hx).2 u hu).2 (Commute.refl u)).eq
  have hcen : u ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer {u} := hle (hS.gen ▸ Subgroup.mem_top g)
    rwa [Subgroup.mem_centralizer_singleton_iff] at hg
  rw [hZ, Subgroup.mem_bot] at hcen
  exact hS.oddT.ne_one hu hcen

end RootSubgroups

theorem transvectionHyp_of_connected (hL2 : CFSG.RankThree.GF2n.Tim81.OddTranspRootL2)
    {K : Type} [Group K] [Finite K] {D : Set K}
    (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup K D) (hP : CFSG.pCore 2 K = ⊥)
    (hZ : Subgroup.center K = ⊥) (hsq : ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D)
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected D) :
    CFSG.Timmesfeld.Transvection.TransvectionHyp K
      {A | ∃ d ∈ D, A = Subgroup.closure (CFSG.Timmesfeld.rootSet D d)} := by
  refine ⟨inferInstance, isTransvectionClass hS (hL2 K D hS hP hZ hsq hconn), ?_, hZ,
    exists_commuting hS hZ hconn, ?_⟩
  · rintro A ⟨d, hd, rfl⟩ B ⟨x, hx, rfl⟩ h
    refine closure_rootSet_eq hx fun f hf => ?_
    rw [← commuting_iff hd hf, ← commuting_iff hx hf]
    exact h (Subgroup.closure (rootSet D f)) ⟨f, hf, rfl⟩
  · rintro ⟨A, ⟨d, hd, rfl⟩, h2⟩
    have h4 := four_le_card_closure_rootSet hS hsq d hd
    exact absurd h2 (by omega)

end CFSG.RankThree.GF2n.Tim79a
