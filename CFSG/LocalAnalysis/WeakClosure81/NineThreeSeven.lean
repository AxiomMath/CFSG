module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

theorem nineThree_conj_mono {B C : Subgroup G} (h : B ≤ C) (g : G) :
    conjSubgroup B g ≤ conjSubgroup C g :=
  fun _ hx => mem_conjSubgroup_iff.2 (h (mem_conjSubgroup_iff.1 hx))

theorem nineThree_conj_inv (B : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup B g) g⁻¹ = B := by
  rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
    CFSG.Quasithin.conjSubgroup_one]

theorem nineThree_conj_inv' (B : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup B g⁻¹) g = B := by
  rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
    CFSG.Quasithin.conjSubgroup_one]

theorem nineThree_conj_injective {B C : Subgroup G} {g : G}
    (e : conjSubgroup B g = conjSubgroup C g) : B = C := by
  rw [← nineThree_conj_inv B g, e, nineThree_conj_inv]

theorem nineThree_conj_le_iff {P B : Subgroup G} {n : G} (hn : n ∈ normalizer (P : Set G)) :
    conjSubgroup B n ≤ P ↔ B ≤ P := by
  have hP : conjSubgroup P n = P := conjSubgroup_eq_iff_mem_normalizer.2 hn
  have hP' : conjSubgroup P n⁻¹ = P :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ hn)
  constructor
  · intro h
    have h1 := nineThree_conj_mono h n⁻¹
    rwa [nineThree_conj_inv, hP'] at h1
  · intro h
    have h1 := nineThree_conj_mono h n
    rwa [hP] at h1

theorem nineThree_le_of_normalizer {P Q : Subgroup G} (hQ : IsPGroup 2 Q) (hPQ : P ≤ Q)
    (h : ∀ n ∈ Q, n ∈ normalizer (P : Set G) → n ∈ P) : Q ≤ P := by
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun e => hne e.symm.le)
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt' : P.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact not_le_of_gt hlt htop
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥Q) _ hlt'
  obtain ⟨x, hxN, hxQ⟩ := SetLike.exists_of_lt hgrow
  have hxN' : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
    have := hxN
    rw [← Subgroup.subgroupOf_normalizer_eq hlt.le] at this
    exact this
  exact hxQ (Subgroup.mem_subgroupOf.2 (h _ x.2 hxN'))

theorem nineThree_le_of_isSylowIn {Q P K : Subgroup G} (hQ : IsSylowIn 2 Q K) (hQP : Q ≤ P)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) : P ≤ Q := by
  have h1 : Q.relIndex P ∣ Q.relIndex K :=
    ⟨P.relIndex K, (Subgroup.relIndex_mul_relIndex Q P K hQP hPK).symm⟩
  have h2 : Q.relIndex P = 2 ^ E3.mQuot P Q := E3.relIndex_eq_two_pow hP Q
  by_contra hne
  have h3 : Q.relIndex P ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.1 h)
  have h4 : 2 ∣ Q.relIndex P := by
    rw [h2]
    refine dvd_pow_self 2 fun h0 => h3 ?_
    rw [h2, h0, pow_zero]
  exact hQ.not_dvd_relIndex (h4.trans h1)

theorem nineThree_isSylowIn_of_le {P K K' : Subgroup G} (hP : IsSylowIn 2 P K)
    (hPK' : P ≤ K') (hK'K : K' ≤ K) : IsSylowIn 2 P K' := by
  refine ⟨hPK', hP.isPGroup, fun h => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K' K hPK' hK'K]
  exact h.mul_right _

theorem nineThree_mem_stab_of_mapsTo {g : G}
    (hg : ∀ B ∈ nineDelta V S, conjSubgroup B g ∈ nineDelta V S) : g ∈ nineDeltaStab V S := by
  intro B
  refine ⟨hg B, fun hB => ?_⟩
  have hpow : ∀ k : ℕ, ∀ B ∈ nineDelta V S, conjSubgroup B (g ^ k) ∈ nineDelta V S := by
    intro k
    induction k with
    | zero =>
      intro B hB
      rwa [pow_zero, CFSG.Quasithin.conjSubgroup_one]
    | succ k ih =>
      intro B hB
      have := hg _ (ih B hB)
      rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, ← pow_succ] at this
  have hn : 0 < orderOf g := orderOf_pos g
  have := hpow (orderOf g - 1) _ hB
  rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, ← pow_succ', Nat.sub_add_cancel hn,
    pow_orderOf_eq_one, CFSG.Quasithin.conjSubgroup_one] at this

namespace Nine3Core

theorem S_le_nineDeltaStab (h : Nine3Core V T A K S X p) : S ≤ nineDeltaStab V S := by
  intro s hs B
  have hsn : s ∈ normalizer (S : Set G) := Subgroup.le_normalizer hs
  constructor
  · rintro ⟨⟨g, rfl⟩, hB⟩
    refine ⟨⟨g * s, ?_⟩, (nineThree_conj_le_iff hsn).2 hB⟩
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
  · rintro ⟨⟨g, hg⟩, hB⟩
    refine ⟨⟨g * s⁻¹, ?_⟩, (nineThree_conj_le_iff hsn).1 hB⟩
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← hg, nineThree_conj_inv]

theorem le_centralizer_of_mem_nineDelta (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineDelta V S) : B ≤ T ⊓ centralizer (A : Set G) := by
  refine le_inf (hB.2.trans h.leS) fun b hb => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hW := nine_three_six h
  have hbW : b ∈ nineW V S := (le_iSup₂_of_le B hB le_rfl : B ≤ nineW V S) hb
  have haW : a ∈ nineW V S :=
    (le_iSup₂_of_le A h.A_mem_nineDelta le_rfl : A ≤ nineW V S) ha
  have := hW.is_comm.comm ⟨a, haW⟩ ⟨b, hbW⟩
  exact congrArg Subtype.val this

theorem mem_nineDelta_of_le (h : Nine3Core V T A K S X p) {B : Subgroup G} (hB : IsGConj V B)
    (hle : B ≤ T ⊓ centralizer (A : Set G)) : B ∈ nineDelta V S :=
  ⟨hB, hle.trans (nine_three_four_centralizer h)⟩

end Nine3Core

theorem nine_three_seven (h : Nine3Core V T A K S X p) :
    ¬ nineDeltaStab V S ≤ normalizer (V : Set G) := by
  intro hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := T ⊓ centralizer (A : Set G) with hPdef
  have hPS : P ≤ S := nine_three_four_centralizer h
  have hPT : P ≤ T := inf_le_left
  have hPM : P ≤ normalizer (V : Set G) := hPT.trans h.h9.sylow.le
  have hP2 : IsPGroup 2 P := h.h9.sylow.isPGroup.to_le hPT
  obtain ⟨S1, hS1, hPS1⟩ := exists_isSylowIn_ge 2
    (inf_le_right : P ≤ centralizer (A : Set G)) hP2
  have h1 : S1 ⊓ normalizer (V : Set G) ≤ P :=
    nineThree_le_of_isSylowIn h.syl (le_inf hPS1 hPM)
      (fun x hx => ⟨hx.2, hS1.le hx.1⟩) (hS1.isPGroup.to_le inf_le_left)
  have h2 : ∀ n ∈ S1, n ∈ normalizer (P : Set G) → n ∈ P := by
    intro n hn1 hn2
    have hn : n ∈ nineDeltaStab V S := by
      refine nineThree_mem_stab_of_mapsTo fun B hB => ?_
      obtain ⟨⟨g, hg⟩, -⟩ := id hB
      refine h.mem_nineDelta_of_le ⟨g * n, ?_⟩ ?_
      · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← hg]
      · exact (nineThree_conj_le_iff hn2).2 (h.le_centralizer_of_mem_nineDelta hB)
    exact h1 ⟨hn1, hN hn⟩
  have h3 : S1 ≤ P := nineThree_le_of_normalizer hS1.isPGroup hPS1 h2
  have hPsyl : IsSylowIn 2 P (centralizer (A : Set G)) := by
    rwa [le_antisymm h3 hPS1] at hS1
  obtain ⟨g₀, hg₀⟩ := h.conj
  have hWS : nineW V S ≤ S := iSup₂_le fun B hB => hB.2
  have hW2 : IsPGroup 2 (nineW V S) := h.h9.sylow.isPGroup.to_le (hWS.trans h.leS)
  have hVW : V ≤ nineW V S := le_iSup₂_of_le V h.V_mem_nineDelta le_rfl
  have hWV : nineW V S ≤ centralizer (V : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr (nine_three_six h)).trans
      (Subgroup.centralizer_le hVW)
  have hWgC : conjSubgroup (nineW V S) g₀ ≤ centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hx' : g₀ * x * g₀⁻¹ ∈ nineW V S := mem_conjSubgroup_iff.1 hx
    have ha' : g₀ * a * g₀⁻¹ ∈ V := by
      rw [hg₀] at ha
      exact mem_conjSubgroup_iff.1 ha
    have e := Subgroup.mem_centralizer_iff.1 (hWV hx') _ ha'
    calc a * x = g₀⁻¹ * ((g₀ * a * g₀⁻¹) * (g₀ * x * g₀⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * ((g₀ * x * g₀⁻¹) * (g₀ * a * g₀⁻¹)) * g₀ := by rw [e]
      _ = x * a := by group
  have hWg2 : IsPGroup 2 (conjSubgroup (nineW V S) g₀) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hW2
    exact IsPGroup.iff_card.2 ⟨n, by rw [E3.card_conjSubgroup, hn]⟩
  obtain ⟨c, hcC, hWc⟩ := E3.exists_le_conj_of_isSylowIn hPsyl hWgC hWg2
  have hWg' : conjSubgroup (nineW V S) (g₀ * c⁻¹) ≤ P := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup]
    have := nineThree_conj_mono hWc c⁻¹
    rwa [nineThree_conj_inv] at this
  have hVg' : conjSubgroup V (g₀ * c⁻¹) = A := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← hg₀]
    exact conjSubgroup_eq_iff_mem_normalizer.2
      (Subgroup.centralizer_le_normalizer (A : Set G) (Subgroup.inv_mem _ hcC))
  have hmaps : ∀ B ∈ nineDelta V S, conjSubgroup B (g₀ * c⁻¹) ∈ nineDelta V S := by
    intro B hB
    obtain ⟨⟨g, hg⟩, -⟩ := id hB
    refine ⟨⟨g * (g₀ * c⁻¹), ?_⟩, ?_⟩
    · rw [hg, CFSG.Quasithin.conjSubgroup_conjSubgroup]
    · exact (nineThree_conj_mono (le_iSup₂_of_le B hB le_rfl) (g₀ * c⁻¹)).trans
        (hWg'.trans hPS)
  have hmem := hN (nineThree_mem_stab_of_mapsTo hmaps)
  exact h.ne (by rw [← hVg']; exact conjSubgroup_eq_iff_mem_normalizer.2 hmem)

namespace Nine3Core

theorem exists_conj_of_mem_nineDelta (h : Nine3Core V T A K S X p) {B B' : Subgroup G}
    (hB : B ∈ nineDelta V S) (hB' : B' ∈ nineDelta V S) (hBV : B ≠ V) (hB'V : B' ≠ V) :
    ∃ s ∈ S, conjSubgroup B s = B' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : B ∈ nineOmegaIn V K S := (h.mem_nineDelta_iff.1 hB).resolve_left hBV
  have h2 : B' ∈ nineOmegaIn V K S := (h.mem_nineDelta_iff.1 hB').resolve_left hB'V
  obtain ⟨r, hr, hrB⟩ := nine_two_two_R h.hyp7 h.rk_gt h.hyp h1 h2
  exact ⟨r, pCoreOf_le_of_isSylowIn h.hyp.base.sylowTwo hr, hrB.symm⟩

theorem exists_mem_nineDeltaStab_conj_eq (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineDelta V S) : ∃ n ∈ nineDeltaStab V S, conjSubgroup V n = B := by
  by_cases hBV : B = V
  · exact ⟨1, Subgroup.one_mem _, by rw [hBV, CFSG.Quasithin.conjSubgroup_one]⟩
  obtain ⟨n₀, hn₀, hn₀M⟩ := SetLike.not_le_iff_exists.1 (nine_three_seven h)
  have hV1 : conjSubgroup V n₀ ∈ nineDelta V S :=
    (mem_nineDeltaStab.1 hn₀ V).1 h.V_mem_nineDelta
  have hV2 : conjSubgroup V n₀ ≠ V := fun e =>
    hn₀M (conjSubgroup_eq_iff_mem_normalizer.1 e)
  obtain ⟨s, hs, hsB⟩ := h.exists_conj_of_mem_nineDelta hV1 hB hV2 hBV
  refine ⟨n₀ * s, Subgroup.mul_mem _ hn₀ (h.S_le_nineDeltaStab hs), ?_⟩
  rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup]
  exact hsB

end Nine3Core

theorem nine_three_two_transitive (h : Nine3Core V T A K S X p) {B₁ B₂ C₁ C₂ : Subgroup G}
    (hB₁ : B₁ ∈ nineDelta V S) (hB₂ : B₂ ∈ nineDelta V S) (hC₁ : C₁ ∈ nineDelta V S)
    (hC₂ : C₂ ∈ nineDelta V S) (hB : B₁ ≠ B₂) (hC : C₁ ≠ C₂) :
    ∃ n ∈ nineDeltaStab V S, conjSubgroup B₁ n = C₁ ∧ conjSubgroup B₂ n = C₂ := by
  obtain ⟨m₁, hm₁, hm₁B⟩ := h.exists_mem_nineDeltaStab_conj_eq hB₁
  obtain ⟨m₂, hm₂, hm₂C⟩ := h.exists_mem_nineDeltaStab_conj_eq hC₁
  have ha : m₁⁻¹ ∈ nineDeltaStab V S := Subgroup.inv_mem _ hm₁
  have hb : m₂⁻¹ ∈ nineDeltaStab V S := Subgroup.inv_mem _ hm₂
  have hB₁V : conjSubgroup B₁ m₁⁻¹ = V := by rw [← hm₁B, nineThree_conj_inv]
  have hC₁V : conjSubgroup C₁ m₂⁻¹ = V := by rw [← hm₂C, nineThree_conj_inv]
  have hB₂a : conjSubgroup B₂ m₁⁻¹ ∈ nineDelta V S := (mem_nineDeltaStab.1 ha B₂).1 hB₂
  have hC₂b : conjSubgroup C₂ m₂⁻¹ ∈ nineDelta V S := (mem_nineDeltaStab.1 hb C₂).1 hC₂
  have hB₂V : conjSubgroup B₂ m₁⁻¹ ≠ V := fun e =>
    hB (nineThree_conj_injective (e.trans hB₁V.symm)).symm
  have hC₂V : conjSubgroup C₂ m₂⁻¹ ≠ V := fun e =>
    hC (nineThree_conj_injective (e.trans hC₁V.symm)).symm
  obtain ⟨s, hs, hsB⟩ := h.exists_conj_of_mem_nineDelta hB₂a hC₂b hB₂V hC₂V
  have hsV : conjSubgroup V s = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (h.S_le_normalizer hs)
  refine ⟨m₁⁻¹ * s * m₂⁻¹⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha
    (h.S_le_nineDeltaStab hs)) (Subgroup.inv_mem _ hb), ?_, ?_⟩
  · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← CFSG.Quasithin.conjSubgroup_conjSubgroup,
      hB₁V, hsV, inv_inv, hm₂C]
  · rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← CFSG.Quasithin.conjSubgroup_conjSubgroup,
      hsB, nineThree_conj_inv]

end CFSG.LocalAnalysis.WeakClosure81
