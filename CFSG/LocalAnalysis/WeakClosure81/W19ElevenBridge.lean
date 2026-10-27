module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenIdx
public import CFSG.LocalAnalysis.WeakClosure81.W19GL3
public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenK

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

structure Pair1911 (D : Data G) (V X : Subgroup G) (g₁ g₂ : G) (K₁ K₂ : Subgroup G)
    (k₁ k₂ : G) : Prop where
  conf₁ : Conf196 D V X g₁ K₁
  conf₂ : Conf196 D V X g₂ K₂
  mem₁ : k₁ ∈ K₁
  mem₂ : k₂ ∈ K₂
  not₁ : ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g₁) k₁)
  not₂ : ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g₂) k₂)
  ne : X ⊓ K₁ ≠ X ⊓ K₂
  le₁ : X ⊓ K₁ ≤ pairSub (conjSubgroup V g₁) k₁
  le₂ : X ⊓ K₂ ≤ pairSub (conjSubgroup V g₂) k₂

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_plane_Z193 (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (h2 : Nat.card V₀ = 2) {g₁ g₂ : G} {K₁ K₂ : Subgroup G} {k₁ k₂ : G}
    (hp : Pair1911 D V X g₁ g₂ K₁ K₂ k₁ k₂)
    (hb₁ : Nat.card ↥(Z193 D V) ≤
      2 * Nat.card ↥(Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G)))
    (hb₂ : Nat.card ↥(Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G)) ≤
      2 * Nat.card ↥(Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G) ⊓
        centralizer (pairSub (conjSubgroup V g₂) k₂ : Set G))) :
    ∃ I : Subgroup G, I ≤ Z193 D V ∧ Nat.card ↥I = 4 ∧ V₀ ≤ I ∧
      normalizer (Z193 D V : Set G) ≤ normalizer (I : Set G) ∧
      ∃ g ∈ normalizer (Z193 D V : Set G), g ∉ D.M ∧ g ^ 2 ∈ D.M := by
  classical
  haveI hcomm : IsMulCommutative ↥(Z193 D V) := c.isElemAbelian_Z193.1
  obtain ⟨v, hvV, hv1, hV₀⟩ := c.exists_v₀ h2
  have hvZ : v ∈ Z193 D V := c.V₀_le_Z193 h2 hvV
  obtain ⟨g₀, hg₀N, hg₀M⟩ := c.exists_mem_normalizer_Z
  have hP₁ : Nat.card ↥(X ⊓ K₁) = p := hp.conf₁.card_inf_K c h162 h763
  have hP₂ : Nat.card ↥(X ⊓ K₂) = p := hp.conf₂.card_inf_K c h162 h763
  have hfixM : ∀ m ∈ D.M, m * v * m⁻¹ = v := fun m hm => c.conj_eq_of_mem_M hvV hv1 hV₀ hm
  have hMfix : ∀ n : G, n * v * n⁻¹ = v → n ∈ D.M := fun n hn => c.mem_M_of_conj_eq hvV hV₀ hn
  set N := normalizer (Z193 D V : Set G) with hN
  have key : GL3.Hyp (D.T.subgroupOf N) (⟨v, hvZ⟩ : ↥(Z193 D V))
      ((Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G)).subgroupOf (Z193 D V))
      ((Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G) ⊓
        centralizer (pairSub (conjSubgroup V g₂) k₂ : Set G)).subgroupOf (Z193 D V)) := by
    refine
      { exp := ?_, fix := ?_, ne_one := ?_, fix_v₀ := ?_, move := ?_, tfix := ?_, gamma := ?_,
        le := ?_, idx₁ := ?_, idx₂ := ?_, ti := ?_ }
    · intro a
      exact Subtype.ext (by simpa [pow_two] using c.isElemAbelian_Z193.2 (a : G) a.2)
    · intro a ha
      apply Subtype.ext
      refine c.eq_one_of_centralizes_normalizer_Z193 a.2 fun n hn => ?_
      exact congrArg Subtype.val (ha ⟨n, hn⟩)
    · intro h
      exact hv1 (congrArg Subtype.val h)
    · intro t ht
      apply Subtype.ext
      exact hfixM t (D.sylowM.le (Subgroup.mem_subgroupOf.1 ht))
    · refine ⟨⟨g₀, hg₀N⟩, fun h => hg₀M (hMfix g₀ ?_)⟩
      exact congrArg Subtype.val h
    · intro S hS1 hSinv
      have hS'Z : S.map (Z193 D V).subtype ≤ Z193 D V := Subgroup.map_subtype_le S
      have hS'1 : S.map (Z193 D V).subtype ≠ ⊥ := fun h =>
        hS1 ((Subgroup.map_eq_bot_iff_of_injective S (Z193 D V).subtype_injective).1 h)
      obtain ⟨s, hsS, hs1, hsT⟩ := c.exists_ne_one_centralizes_of_normalized hS'Z hS'1
        (fun t ht s hs => by
          obtain ⟨s₀, hs₀S, rfl⟩ := Subgroup.mem_map.1 hs
          exact ⟨(⟨t, c.T_le_normalizer_Z193 ht⟩ : ↥N) • s₀,
            hSinv ⟨t, c.T_le_normalizer_Z193 ht⟩ (Subgroup.mem_subgroupOf.2 ht) s₀ hs₀S, rfl⟩)
      obtain ⟨s₀, hs₀S, rfl⟩ := Subgroup.mem_map.1 hsS
      refine ⟨s₀, hs₀S, fun h => hs1 (by rw [h]; rfl), fun t ht => ?_⟩
      exact Subtype.ext (hsT (t : G) (Subgroup.mem_subgroupOf.1 ht))
    · intro Y hY1 hYT n hn
      have hY'Z : Y.map (Z193 D V).subtype ≤ Z193 D V := Subgroup.map_subtype_le Y
      have hY'1 : Y.map (Z193 D V).subtype ≠ ⊥ := fun h =>
        hY1 ((Subgroup.map_eq_bot_iff_of_injective Y (Z193 D V).subtype_injective).1 h)
      have hnM : (n : G) ∈ D.M := by
        refine c.mem_M_of_normalizes_fixed hY'Z hY'1 (fun y hy t ht => ?_) (fun y hy => ?_)
        · obtain ⟨y₀, hy₀Y, rfl⟩ := Subgroup.mem_map.1 hy
          exact congrArg Subtype.val
            (hYT y₀ hy₀Y ⟨t, c.T_le_normalizer_Z193 ht⟩ (Subgroup.mem_subgroupOf.2 ht))
        · obtain ⟨y₀, hy₀Y, rfl⟩ := Subgroup.mem_map.1 hy
          exact ⟨n • y₀, hn y₀ hy₀Y, rfl⟩
      exact Subtype.ext (hfixM n hnM)
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
    · have hle : Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G) ≤ Z193 D V :=
        inf_le_left
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact hb₁
    · have hle : Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G) ⊓
          centralizer (pairSub (conjSubgroup V g₂) k₂ : Set G) ≤ Z193 D V :=
        inf_le_left.trans inf_le_left
      have hle' : Z193 D V ⊓ centralizer (pairSub (conjSubgroup V g₁) k₁ : Set G) ≤ Z193 D V :=
        inf_le_left
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv]
      exact hb₂
    · intro n hn z hz hnz
      have hnM : (n : G) ∉ D.M := fun h => hn (Subtype.ext (hfixM n h))
      have hz' := Subgroup.mem_subgroupOf.1 hz
      have hnz' := Subgroup.mem_subgroupOf.1 hnz
      refine Subtype.ext (c.eq_one_of_conj_mem h2 hP₁ hP₂ hp.ne inf_le_left inf_le_left hp.le₁
        hp.le₂ n.2 hnM z.2 (fun l hl => Subgroup.mem_centralizer_iff.1 hz'.1.2 l hl)
        (fun l hl => Subgroup.mem_centralizer_iff.1 hz'.2 l hl) hnz'.1
        (fun l hl => Subgroup.mem_centralizer_iff.1 hnz'.2 l hl))
  obtain ⟨I, hI4, hvI, hIinv, g, hg1, hg2⟩ := key.exists_plane
  refine ⟨I.map (Z193 D V).subtype, Subgroup.map_subtype_le I, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Z193 D V).subtype_injective]
    exact hI4
  · intro x hx
    rcases hV₀ x hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨⟨_, hvZ⟩, hvI, rfl⟩
  · intro n hn
    refine mem_normalizer_of_conj_mem_fin fun x hx => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨(⟨n, hn⟩ : ↥N) • x₀, hIinv ⟨n, hn⟩ x₀ hx₀, rfl⟩
  · refine ⟨g, g.2, fun h => hg1 (Subtype.ext (hfixM g h)), ?_⟩
    apply hMfix
    have h3 := congrArg Subtype.val hg2
    calc (g : G) ^ 2 * v * ((g : G) ^ 2)⁻¹ = (g : G) * ((g : G) * v * (g : G)⁻¹) * (g : G)⁻¹ := by
          rw [pow_two]
          group
      _ = v := h3

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
