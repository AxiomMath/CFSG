module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeE
public import CFSG.LocalAnalysis.WeakClosure81.NineMinimalI
public import CFSG.LocalAnalysis.WeakClosure81.NineThirteenAux
public import CFSG.LocalAnalysis.WeakClosure81.NineTwoFourUncond
public import CFSG.GroupTheory.TwoResidualOddOrder
public import CFSG.Goldschmidt.Steps.Sec87d

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T S K X : Subgroup G}

theorem commutator_cClos_ne_bot_of_parity (h9 : Hyp9 V T) (hST : S ≤ T)
    (hTS : T ≤ normalizer (S : Set G))
    (hS2 : ∀ x ∈ T, ∀ y ∈ T, x ∉ S → y ∉ S → x * y ∈ S)
    (hX : X ∈ calP V) (hX1 : X ≠ ⊥) (hXK : X ≤ twoResidual K)
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    ⁅twoResidual K, E3.cClos V 1 S⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcomm
  rcases hX with ⟨p, hp, hp2, hXp, hXM, hXG, hXtriv⟩
  have hleC : twoResidual K ≤ centralizer (E3.cClos V 1 S : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
  have hXC : X ≤ centralizer (E3.cClos V 1 S : Set G) := hXK.trans hleC
  have hVnorm : (V.subgroupOf (normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hVp : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h9.hyp7.1
  have hVT : V ≤ T := h9.sylow.le_of_normal Subgroup.le_normalizer hVnorm hVp
  have hVW : V ≤ E3.wClos V 1 T := E3.le_wClos_of_mQuot_le_self h9.hyp7.1 hVT le_rfl
    (k := 1) (by rw [E3.mQuot_self]; norm_num) (by have := h9.rk_gt; omega)
  obtain ⟨h, hhN, hhM⟩ := SetLike.not_le_iff_exists.1 h1
  have hW1h : conjSubgroup (E3.wClos V 1 T) h = E3.wClos V 1 T :=
    (conjSubgroup_eq_iff_mem_normalizer).2 hhN
  have hVhW1 : conjSubgroup V h ≤ E3.wClos V 1 T := by
    have h1' : conjSubgroup V h ≤ conjSubgroup (E3.wClos V 1 T) h :=
      E3.conjSubgroup_mono_left h hVW
    rwa [hW1h] at h1'
  have hVhT : conjSubgroup V h ≤ T := hVhW1.trans (E3.wClos_le 1 T)
  have hW1N : E3.wClos V 1 T ≤ normalizer (conjSubgroup V h : Set G) := by
    have h1' : conjSubgroup (E3.wClos V 1 T) h ≤
        conjSubgroup (normalizer (V : Set G)) h :=
      E3.conjSubgroup_mono_left h ((E3.wClos_le 1 T).trans h9.sylow.le)
    rwa [hW1h, E3.conjSubgroup_normalizer] at h1'
  have hW1S : E3.wClos V 1 T ≤ normalizer (S : Set G) :=
    (E3.wClos_le 1 T).trans hTS
  have hW1U : E3.wClos V 1 T ≤
      normalizer ((conjSubgroup V h ⊓ S : Subgroup G) : Set G) :=
    (le_inf hW1N hW1S).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAcard : 2 < Nat.card (conjSubgroup V h) := by
    rw [E3.card_conjSubgroup]
    exact h9.hyp7.2.1
  have hAne : conjSubgroup V h ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  have hUne : conjSubgroup V h ⊓ S ≠ ⊥ := by
    intro hbot
    have hnle : ¬ conjSubgroup V h ≤ S := by
      intro hle
      have hEq : conjSubgroup V h ⊓ S = conjSubgroup V h := inf_eq_left.2 hle
      rw [hEq] at hbot
      exact hAne hbot
    obtain ⟨u, huA, huS⟩ := SetLike.not_le_iff_exists.1 hnle
    have hne : conjSubgroup V h ⊓ S ≠ ⊥ :=
      inf_ne_bot_of_forall_mem_or_mul_mem hAcard huA (fun x hx => by
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr (hS2 u (hVhT huA) x (hVhT hx) huS hxS))
    exact hne hbot
  have hW1two : IsPGroup 2 (E3.wClos V 1 T) :=
    h9.sylow.isPGroup.to_le (E3.wClos_le 1 T)
  have hbne : (conjSubgroup V h ⊓ S) ⊓
      (E3.wClos V 1 T ⊓ centralizer (E3.wClos V 1 T : Set G)) ≠ ⊥ :=
    CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hW1two (inf_le_left.trans hVhW1) hW1U hUne
  obtain ⟨⟨b, hbmem⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbne
  have hbU : b ∈ conjSubgroup V h ⊓ S := hbmem.1
  have hbA : b ∈ conjSubgroup V h := hbU.1
  have hbS : b ∈ S := hbU.2
  have hbC : b ∈ centralizer (E3.wClos V 1 T : Set G) := hbmem.2.2
  have hb1' : b ≠ 1 := fun hb => hb1 (Subtype.ext hb)
  have hbCS : b ∈ centralizer (E3.wClos V 1 S : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hbC ⊢
    intro y hy
    exact hbC y (E3.wClos_mono hST hy)
  have hbC1 : b ∈ E3.cClos V 1 S := ⟨hbS, hbCS⟩
  have hXcent : X ≤ centralizer ({b} : Set G) := by
    intro x hx
    have hxc : x ∈ centralizer (E3.cClos V 1 S : Set G) := hXC hx
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hxc b hbC1
  have hXN : X ≤ normalizer (conjSubgroup V h : Set G) :=
    hXcent.trans (centralizer_le_normalizer_conj h9.hyp7.2.2 h hbA hb1')
  have hXMh : X ≤ conjSubgroup (normalizer (V : Set G)) h := by
    rw [E3.conjSubgroup_normalizer]
    exact hXN
  have hVhM : conjSubgroup V h ≤ normalizer (V : Set G) :=
    hVhT.trans h9.sylow.le
  have hXbot : X = ⊥ := by
    have htriv := hXtriv h hhM hVhM
    rw [← inf_eq_left.2 hXMh]
    exact htriv
  exact hX1 hXbot

section Certificates


theorem le_normalizer_wClos_of_irreducible_permutes {p : ℕ} (h9 : Hyp9 V T)
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : X ∈ calP V) (hXp : IsPGroup p X)
    (hXnc : ¬ IsCyclic ↥X) (hST : S ≤ T) (hTS : T ≤ normalizer (S : Set G))
    (hS2 : ∀ x ∈ T, ∀ y ∈ T, x ∉ S → y ∉ S → x * y ∈ S)
    (hXS : (X : Set G) * S = S * X)
    (hirr : ∀ Y : Subgroup G, Y ≤ X → (Y : Set G) * S = S * Y → Y = ⊥ ∨ Y = X)
    (h1 : ¬ normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G)) :
    X ⊔ S ≤ normalizer (E3.wClos V 0 S : Set G) := by
  by_contra hnot
  have : Fact p.Prime := ⟨hp⟩
  have hXmem : X ∈ calP V := hX
  rcases hX with ⟨q, hq, hq2, hXq, hXV, hXG, hXtriv⟩
  have hX1 : X ≠ ⊥ := by
    intro hbot
    exact hXnc (by rw [hbot]; exact isCyclic_of_subsingleton)
  have hS2g : IsPGroup 2 S := h9.sylow.isPGroup.to_le hST
  have hSV : S ≤ normalizer (V : Set G) := hST.trans h9.sylow.le
  have hSW : S ≤ normalizer (E3.wClos V 0 S : Set G) :=
    (Subgroup.le_normalizer (H := S)).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) S)
  have hmin : ∀ K₀ : Subgroup G, S ≤ K₀ → K₀ < X ⊔ S →
      K₀ ≤ normalizer (E3.wClos V 0 S : Set G) := by
    intro K₀ hSK hK
    obtain ⟨hK0eq, hperm⟩ := exists_inf_sup_of_le_sup hXS hSK hK.le
    rcases hirr (K₀ ⊓ X) inf_le_right hperm with hbot | htop
    · rw [hbot, bot_sup_eq] at hK0eq
      rw [← hK0eq]
      exact hSW
    · rw [htop] at hK0eq
      exact absurd hK0eq.symm hK.ne
  have h9One : Nine1Hyp V (X ⊔ S) S X p :=
    nine1Hyp_of_minimal (W := E3.wClos V 0 S) hp hp2 hXp hXV hS2g hSV hXS hSW hnot hmin
  have hXres : X ≤ twoResidual (X ⊔ S) := by
    refine CFSG.GroupTheory.le_twoResidual_of_odd_card le_sup_left ?_
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hnotC : ⁅twoResidual (X ⊔ S), E3.cClos V 1 S⁆ ≠ ⊥ :=
    commutator_cClos_ne_bot_of_parity h9 hST hTS hS2 hXmem hX1 hXres h1
  exact hXnc (nine_two_four_uncond h9.hyp7 h9.rk_gt
    { base := h9One, mem := hXmem, notW := hnot, notC := hnotC })

end Certificates

end CFSG.LocalAnalysis.WeakClosure81
