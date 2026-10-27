module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_le_of_isPGroup {K P Q : Subgroup G} (hP : IsSylowIn 2 P K) (hPQ : P ≤ Q)
    (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) : IsSylowIn 2 Q K :=
  ⟨hQK, hQ, fun hd => hP.not_dvd_relIndex (hd.trans (Subgroup.relIndex_dvd_of_le_left K hPQ))⟩

theorem isSylowIn_conjSub {P K : Subgroup G} (hP : IsSylowIn 2 P K) (g : G) :
    IsSylowIn 2 (A1b.conjSub g P) (A1b.conjSub g K) :=
  B6.isSylowTwoOf_conjSub hP g

theorem exists_conj_isSylowIn_inf_normalizer {H M T U₀ : Subgroup G} (hT : IsSylowIn 2 T H)
    (hTM : T ≤ M) (hU₀ : U₀ ≤ T) :
    ∃ m ∈ M ⊓ H, A1b.conjSub m U₀ ≤ T ∧
      IsSylowIn 2 (T ⊓ normalizer (A1b.conjSub m U₀ : Set G))
        (M ⊓ (H ⊓ normalizer (A1b.conjSub m U₀ : Set G))) := by
  have hTH : T ≤ H := hT.le
  have hU₀2 : IsPGroup 2 U₀ := hT.isPGroup.to_le hU₀
  have hU₀K : U₀ ≤ M ⊓ (H ⊓ normalizer (U₀ : Set G)) :=
    le_inf (hU₀.trans hTM) (le_inf (hU₀.trans hTH) Subgroup.le_normalizer)
  obtain ⟨P, hP, hU₀P⟩ := exists_isSylowIn_ge 2 hU₀K hU₀2
  have hPK : P ≤ M ⊓ (H ⊓ normalizer (U₀ : Set G)) := hP.le
  have hPM : P ≤ M := hPK.trans inf_le_left
  have hPH : P ≤ H := (hPK.trans inf_le_right).trans inf_le_left
  obtain ⟨m, hm, hmP⟩ := exists_conjSub_le_of_isSylowIn hT hTM hP.isPGroup hPM hPH
  refine ⟨m, hm, (A1b.conjSub_mono m hU₀P).trans hmP, ?_⟩
  have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).1
  have hmH : m ∈ H := (Subgroup.mem_inf.1 hm).2
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  have hcM : A1b.conjSub m M = M := B6.conjSub_eq_self (Subgroup.le_normalizer hmM)
  have hK : M ⊓ (H ⊓ normalizer (A1b.conjSub m U₀ : Set G)) =
      A1b.conjSub m (M ⊓ (H ⊓ normalizer (U₀ : Set G))) := by
    rw [inf_normalizer_conjSub hmH]
    calc M ⊓ A1b.conjSub m (H ⊓ normalizer (U₀ : Set G))
        = A1b.conjSub m M ⊓ A1b.conjSub m (H ⊓ normalizer (U₀ : Set G)) := by rw [hcM]
      _ = A1b.conjSub m (M ⊓ (H ⊓ normalizer (U₀ : Set G))) :=
        (Subgroup.map_inf _ _ _ hinj).symm
  have hPs : IsSylowIn 2 (A1b.conjSub m P)
      (M ⊓ (H ⊓ normalizer (A1b.conjSub m U₀ : Set G))) := by
    rw [hK]
    exact isSylowIn_conjSub hP m
  have hPN : A1b.conjSub m P ≤ normalizer (A1b.conjSub m U₀ : Set G) :=
    (hPs.le.trans inf_le_right).trans inf_le_right
  exact isSylowIn_of_le_of_isPGroup hPs (le_inf hmP hPN)
    (le_inf (inf_le_left.trans hTM) (le_inf (inf_le_left.trans hTH) inf_le_right))
    (hT.isPGroup.to_le inf_le_left)

theorem exists_card_max_U {H M T : Subgroup G} {Ω : Set (Subgroup G)} (h : FiveTenHyp H M T Ω) :
    ∃ U : Subgroup G, U ≤ E1.weakClosure T Ω ∧ E1.weakClosure U Ω = U ∧
      ¬ H ⊓ normalizer (U : Set G) ≤ M ∧
      ∀ X : Subgroup G, X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X →
        ¬ H ⊓ normalizer (X : Set G) ≤ M → Nat.card X ≤ Nat.card U := by
  have hbot : (⊥ : Subgroup G) ∈ {X : Subgroup G | X ≤ E1.weakClosure T Ω ∧
      E1.weakClosure X Ω = X ∧ ¬ H ⊓ normalizer (X : Set G) ≤ M} := by
    refine ⟨bot_le, le_bot_iff.1 E1.weakClosure_le, ?_⟩
    have hN : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.2 inferInstance
    rw [hN, inf_top_eq]
    exact h.not_le
  obtain ⟨U, hU, hmax⟩ := Set.exists_max_image
    {X : Subgroup G | X ≤ E1.weakClosure T Ω ∧ E1.weakClosure X Ω = X ∧
      ¬ H ⊓ normalizer (X : Set G) ≤ M} (fun X => Nat.card X) (Set.toFinite _) ⟨⊥, hbot⟩
  exact ⟨U, hU.1, hU.2.1, hU.2.2, fun X hXW hXc hXn => hmax X ⟨hXW, hXc, hXn⟩⟩

theorem exists_conj_good_U {H M T U₀ : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) (hU₀ : U₀ ≤ E1.weakClosure T Ω) (hc₀ : E1.weakClosure U₀ Ω = U₀)
    (hn₀ : ¬ H ⊓ normalizer (U₀ : Set G) ≤ M)
    (hmax : ∀ X : Subgroup G, X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X →
      ¬ H ⊓ normalizer (X : Set G) ≤ M → Nat.card X ≤ Nat.card U₀) :
    ∃ U : Subgroup G, U ≤ E1.weakClosure T Ω ∧ E1.weakClosure U Ω = U ∧
      ¬ H ⊓ normalizer (U : Set G) ≤ M ∧
      (∀ X : Subgroup G, X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X → U < X →
        H ⊓ normalizer (X : Set G) ≤ M) ∧
      IsSylowIn 2 (T ⊓ normalizer (U : Set G)) (M ⊓ (H ⊓ normalizer (U : Set G))) := by
  have hWT : E1.weakClosure T Ω ≤ T := E1.weakClosure_le
  obtain ⟨m, hm, hmT, hsyl⟩ :=
    exists_conj_isSylowIn_inf_normalizer h.sylow h.le_M (hU₀.trans hWT)
  have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).1
  have hmH : m ∈ H := (Subgroup.mem_inf.1 hm).2
  have hcl : E1.weakClosure (A1b.conjSub m U₀) Ω = A1b.conjSub m U₀ := by
    rw [← conjSub_weakClosure h.invColl hmH U₀, hc₀]
  have hUW : A1b.conjSub m U₀ ≤ E1.weakClosure T Ω := by
    rw [← hcl]
    exact weakClosure_mono Ω hmT
  have hn : ¬ H ⊓ normalizer (A1b.conjSub m U₀ : Set G) ≤ M := by
    rw [inf_normalizer_conjSub hmH, conjSub_le_iff_of_mem hmM]
    exact hn₀
  have hcard : Nat.card (A1b.conjSub m U₀) = Nat.card U₀ :=
    Nat.card_congr (Subgroup.equivMapOfInjective U₀ (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective).toEquiv.symm
  refine ⟨A1b.conjSub m U₀, hUW, hcl, hn, fun X hXW hXc hlt => ?_, hsyl⟩
  by_contra hXn
  have h1 := hmax X hXW hXc hXn
  have h2 : Nat.card (A1b.conjSub m U₀) < Nat.card X := Subgroup.card_lt_of_lt hlt
  omega

theorem exists_good_U {H M T : Subgroup G} {Ω : Set (Subgroup G)} (h : FiveTenHyp H M T Ω) :
    ∃ U : Subgroup G, U ≤ E1.weakClosure T Ω ∧ E1.weakClosure U Ω = U ∧
      ¬ H ⊓ normalizer (U : Set G) ≤ M ∧
      (∀ X : Subgroup G, X ≤ E1.weakClosure T Ω → E1.weakClosure X Ω = X → U < X →
        H ⊓ normalizer (X : Set G) ≤ M) ∧
      IsSylowIn 2 (T ⊓ normalizer (U : Set G)) (M ⊓ (H ⊓ normalizer (U : Set G))) := by
  obtain ⟨U₀, h1, h2, h3, h4⟩ := exists_card_max_U h
  exact exists_conj_good_U h h1 h2 h3 h4

end CFSG.LocalAnalysis.WeakClosure81
