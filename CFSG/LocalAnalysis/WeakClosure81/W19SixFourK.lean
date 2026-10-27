module

public import CFSG.LocalAnalysis.WeakClosure81.W19SixSix
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_inf {x : G} {P Q : Subgroup G} (hP : x ∈ normalizer (P : Set G))
    (hQ : x ∈ normalizer (Q : Set G)) : x ∈ normalizer ((P ⊓ Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 hP y,
    Subgroup.mem_normalizer_iff.1 hQ y]

private theorem mem_normalizer_sup {x : G} {P Q : Subgroup G} (hP : x ∈ normalizer (P : Set G))
    (hQ : x ∈ normalizer (Q : Set G)) : x ∈ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
  apply E1.mem_normalizer_of_conj_mem
  intro y hy
  have hle : P ⊔ Q ≤ (P ⊔ Q).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hP z).1 hz)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hQ z).1 hz)
  have := hle hy
  rwa [Subgroup.mem_comap] at this

theorem pCoreOf_inf_le_pCoreOf {J K : Subgroup G} (hKJ : K ≤ J) :
    pCoreOf 2 J ⊓ K ≤ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).to_le inf_le_left)
  intro k hk
  exact mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J (hKJ hk))
    (Subgroup.le_normalizer hk)

section K0

variable {D : Data G} {X A K : Subgroup G}

theorem le_K0193 : A ≤ K0193 D X A K := by
  have h : conjSubgroup A 1 ≤ ⨆ k ∈ K, conjSubgroup A k :=
    le_iSup₂ (f := fun (k : G) (_ : k ∈ K) => conjSubgroup A k) (1 : G) K.one_mem
  rw [conjSubgroup_one] at h
  exact h.trans le_sup_left

theorem K0193_le_of_le (hAK : A ≤ K) (hOK : pCoreOf 2 (X ⊔ D.T) ≤ K) : K0193 D X A K ≤ K := by
  refine sup_le (iSup₂_le fun k hk x hx => ?_) hOK
  rw [mem_conjSubgroup_iff] at hx
  have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [e]
  exact K.mul_mem (K.mul_mem (K.inv_mem hk) (hAK hx)) hk

theorem le_J193 (hK : K ≤ X ⊔ D.T) : K ≤ J193 D X A K := fun k hk =>
  Subgroup.mem_inf.2 ⟨hK hk, le_normalizer_K0193 hK hk⟩

end K0

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem K0193_le_K (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    K0193 D X (conjSubgroup V g) K ≤ K :=
  K0193_le_of_le (hc.A_le_K c) (hc.pCoreOf_le_K c)

theorem A_le_J193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ≤ J193 D X (conjSubgroup V g) K :=
  (hc.A_le_K c).trans (le_J193 hc.le_H)

theorem K_le_J193 (hc : Conf196 D V X g K) : K ≤ J193 D X (conjSubgroup V g) K :=
  le_J193 hc.le_H

theorem pCoreOf_le_J193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    pCoreOf 2 (X ⊔ D.T) ≤ J193 D X (conjSubgroup V g) K :=
  (hc.pCoreOf_le_K c).trans hc.K_le_J193

theorem pCoreOf_le_pCoreOf_J193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    pCoreOf 2 (X ⊔ D.T) ≤ pCoreOf 2 (J193 D X (conjSubgroup V g) K) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hc.pCoreOf_le_J193 c)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem not_A_le_pCoreOf_J193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    ¬ conjSubgroup V g ≤ pCoreOf 2 (J193 D X (conjSubgroup V g) K) := fun h =>
  hc.not_A_le_pCoreOf c
    ((le_inf h (hc.A_le_K c)).trans (pCoreOf_inf_le_pCoreOf hc.K_le_J193))

theorem inf_pCoreOf_J193_le (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ⊓ pCoreOf 2 (J193 D X (conjSubgroup V g) K) ≤
      conjSubgroup V g ⊓ pCoreOf 2 K := fun x hx =>
  Subgroup.mem_inf.2 ⟨hx.1, pCoreOf_inf_le_pCoreOf hc.K_le_J193 ⟨hx.2, hc.A_le_K c hx.1⟩⟩

theorem pCoreOf_K0193_le (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    pCoreOf 2 (K0193 D X (conjSubgroup V g) K) ≤ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (hc.K0193_le_K c)) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact (le_normalizer_K0193 hc.le_H).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem K0193_inf_pCoreOf_le (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    K0193 D X (conjSubgroup V g) K ⊓ pCoreOf 2 K ≤
      pCoreOf 2 (K0193 D X (conjSubgroup V g) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right)
  intro k hk
  have hkK : k ∈ K := hc.K0193_le_K c hk
  exact mem_normalizer_inf (le_normalizer_K0193 hc.le_H hkK)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hkK)

theorem inf_pCoreOf_le_pCoreOf_K0193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ⊓ pCoreOf 2 K ≤ pCoreOf 2 (K0193 D X (conjSubgroup V g) K) :=
  fun x hx => hc.K0193_inf_pCoreOf_le c ⟨le_K0193 hx.1, hx.2⟩

theorem A_le_normalizer_sup (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ≤ normalizer
      (((X ⊓ J193 D X (conjSubgroup V g) K) ⊔
        pCoreOf 2 (J193 D X (conjSubgroup V g) K) : Subgroup G) : Set G) := by
  set A := conjSubgroup V g with hA
  set J := J193 D X A K with hJ
  set O := pCoreOf 2 (X ⊔ D.T) with hO
  have hAJ : A ≤ J := hc.A_le_J193 c
  have hN1 : A ≤ normalizer ((X ⊔ O : Subgroup G) : Set G) :=
    hc.le_T.trans (le_sup_right.trans c.le_normalizer_sup_pCoreOf)
  have hOJ : O ≤ J := hc.pCoreOf_le_J193 c
  have hXO : X ≤ normalizer (O : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hded : (X ⊔ O) ⊓ J = (X ⊓ J) ⊔ O := by
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ X ⊔ O := hx.1
      have hxJ : x ∈ J := hx.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X O hXO] at hxN
      obtain ⟨x₀, hx₀, o, ho, rfl⟩ := hxN
      have hx₀J : x₀ ∈ J := by
        have := J.mul_mem hxJ (J.inv_mem (hOJ ho))
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hx₀, hx₀J⟩))
        (Subgroup.mem_sup_right ho)
    · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hOJ)
  have hsup : ((X ⊓ J) ⊔ O) ⊔ pCoreOf 2 J = (X ⊓ J) ⊔ pCoreOf 2 J := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (hc.pCoreOf_le_pCoreOf_J193 c |>.trans le_sup_right))
        le_sup_right
    · exact sup_le_sup_right le_sup_left _
  rw [← hsup]
  intro a ha
  refine mem_normalizer_sup ?_ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J (hAJ ha))
  rw [← hded]
  exact mem_normalizer_inf (hN1 ha) (Subgroup.le_normalizer (hAJ ha))

theorem p_le_card_inf_J193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    p ≤ Nat.card ↥(X ⊓ J193 D X (conjSubgroup V g) K) := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hKne := c.inf_K_ne_bot hc
  have hle : X ⊓ K ≤ X ⊓ J193 D X (conjSubgroup V g) K := inf_le_inf_left X hc.K_le_J193
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1
    (c.hyp.isPGroup.to_le (inf_le_left : X ⊓ J193 D X (conjSubgroup V g) K ≤ X))
  rw [hn]
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hKne
    rw [pow_zero] at hn
    exact le_bot_iff.1 (hle.trans (Subgroup.card_eq_one.1 hn).le)
  exact Nat.le_self_pow hn0 p

end Conf196

end CFSG.LocalAnalysis.WeakClosure81

end
