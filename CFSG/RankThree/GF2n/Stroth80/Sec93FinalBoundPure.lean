module

public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalBound
public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalListFacts
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.GF2Type.Aschbacher1976Common.NotZStar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem sec93f_conjNormal_mem_inner_iff {Y : Type} [Group Y] {S : Subgroup Y} [S.Normal] (y : Y) :
    MulAut.conjNormal (H := S) y ∈ inner ↥S ↔ y ∈ S ⊔ Subgroup.centralizer (S : Set Y) := by
  constructor
  · rintro ⟨s, hs⟩
    have hsy : ∀ x : ↥S, (s : Y) * x * (s : Y)⁻¹ = y * x * y⁻¹ := by
      intro x
      have h1 := congrArg (fun a : MulAut ↥S => ((a x : ↥S) : Y)) hs
      simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h1
    have hc : (s : Y)⁻¹ * y ∈ Subgroup.centralizer (S : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := hsy ⟨x, hx⟩
      simp only at h2
      calc x * ((s : Y)⁻¹ * y) = (s : Y)⁻¹ * ((s : Y) * x * (s : Y)⁻¹) * y := by group
        _ = (s : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
        _ = (s : Y)⁻¹ * y * x := by group
    have : y = (s : Y) * ((s : Y)⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup s.2 hc
  · intro hy
    obtain ⟨s, hsS, c, hcC, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hconj : MulAut.conjNormal (H := S) c = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := Subgroup.mem_centralizer_iff.mp hcC x x.2
      calc c * (x : Y) * c⁻¹ = (x : Y) * c * c⁻¹ := by rw [this]
        _ = x := by group
    rw [map_mul, hconj, mul_one]
    exact ⟨⟨s, hsS⟩, by rw [← MulAut.conjNormal_val]⟩

theorem listOutRank_of_outElemAbelianBound (h : ListOutElemAbelianBoundStatement) :
    ListOutRankStatement := by
  intro Y _ _ S L hSn hList hLel
  haveI : S.Normal := hSn
  set C : Subgroup Y := Subgroup.centralizer (S : Set Y) with hC
  let ρ : ↥L →* Outer ↥S :=
    (QuotientGroup.mk' (inner ↥S)).comp ((MulAut.conjNormal (H := S)).comp L.subtype)
  have hrange : IsElemAbelian 2 ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, l₁, rfl⟩ := a
      obtain ⟨b, l₂, rfl⟩ := b
      refine Subtype.ext ?_
      show ρ l₁ * ρ l₂ = ρ l₂ * ρ l₁
      rw [← map_mul, ← map_mul, hLel.1.is_comm.comm l₁ l₂]
    · obtain ⟨l, rfl⟩ := hx
      rw [← map_pow]
      have : l ^ 2 = 1 := Subtype.ext (hLel.2 (l : Y) l.2)
      rw [this, map_one]
  have hbd : Nat.card ρ.range ≤ 4 := h ↥S hList ρ.range hrange
  have hker : ρ.ker = (L ⊓ (S ⊔ C)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show (QuotientGroup.mk' (inner ↥S)) (MulAut.conjNormal (H := S) (l : Y)) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      sec93f_conjNormal_mem_inner_iff]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ (S ⊔ C) ≤ L)).toEquiv]
    at hcard
  rw [← hcard]
  calc Nat.card ↥(L ⊓ (S ⊔ C)) * Nat.card ρ.range ≤ Nat.card ↥(L ⊓ (S ⊔ C)) * 4 :=
        Nat.mul_le_mul_left _ hbd
    _ = 4 * Nat.card ↥(L ⊓ (S ⊔ C)) := mul_comm _ _

theorem sec93f_corBHyp_subgroupOf {Y : Type} [Group Y] {T N : Subgroup Y} (hTN : T ≤ N)
    (h : CorBHyp T) : CorBHyp (T.subgroupOf N) := by
  obtain ⟨hel, hTI, hcomm⟩ := h
  have hconj : ∀ g : ↥N, conjSubgroup g (T.subgroupOf N) =
      (conjSubgroup (g : Y) T).subgroupOf N := by
    intro g
    ext x
    simp only [mem_conjSubgroup, Subgroup.mem_subgroupOf]
    rfl
  have hconjN : ∀ g : ↥N, conjSubgroup (g : Y) T ≤ N := by
    intro g x hx
    rw [mem_conjSubgroup] at hx
    have h1 : (g : Y) * ((g : Y)⁻¹ * x * (g : Y)) * (g : Y)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem g.2 (hTN hx)) (N.inv_mem g.2)
    have h2 : (g : Y) * ((g : Y)⁻¹ * x * (g : Y)) * (g : Y)⁻¹ = x := by group
    rwa [h2] at h1
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, fun g => ?_, fun g => ?_⟩
  · have h2 := congrArg (fun z : ↥T => (z : Y))
      (hel.1.is_comm.comm ⟨(a : ↥N), a.2⟩ ⟨(b : ↥N), b.2⟩)
    exact Subtype.ext (Subtype.ext h2)
  · exact Subtype.ext (hel.2 (x : Y) hx)
  · rcases hTI (g : Y) with h0 | h1
    · left
      refine eq_bot_iff.mpr fun x hx => ?_
      rw [hconj g] at hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hx3 : (x : Y) ∈ T ⊓ conjSubgroup (g : Y) T := ⟨hx1, hx2⟩
      rw [h0, Subgroup.mem_bot] at hx3
      rw [Subgroup.mem_bot]
      exact Subtype.ext hx3
    · right
      refine le_antisymm inf_le_left fun x hx => ?_
      rw [hconj g]
      refine ⟨hx, ?_⟩
      have hx1 : (x : Y) ∈ T ⊓ conjSubgroup (g : Y) T := by rw [h1]; exact hx
      exact Subgroup.mem_subgroupOf.mpr hx1.2
  · rw [hconj g]
    constructor
    · intro hc
      have hconjeq : conjSubgroup (g : Y) T = T := by
        refine (hcomm (g : Y)).mp fun x hx y hy => ?_
        have hxN : x ∈ N := hTN hx
        have hyN : y ∈ N := hconjN g hy
        have := hc ⟨x, hxN⟩ hx ⟨y, hyN⟩ hy
        exact congrArg Subtype.val this
      rw [hconjeq]
    · intro hc
      have hconjeq : conjSubgroup (g : Y) T = T := by
        refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
        · have hxN : x ∈ N := hconjN g hx
          have : (⟨x, hxN⟩ : ↥N) ∈ (conjSubgroup (g : Y) T).subgroupOf N := hx
          rw [hc] at this
          exact this
        · have hxN : x ∈ N := hTN hx
          have : (⟨x, hxN⟩ : ↥N) ∈ T.subgroupOf N := hx
          rw [← hc] at this
          exact this
      intro x hx y hy
      have h3 := (hcomm (g : Y)).mpr hconjeq
      exact Subtype.ext (h3 x hx y hy)

theorem sec93f_card_ge_four {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) {T : Subgroup S} (hT0 : T ≠ ⊥) (hCor : CorBHyp T) :
    4 ≤ Nat.card T := by
  by_contra hlt
  push Not at hlt
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := fun g => ⟨1, Subtype.ext (by simpa using hCor.1.2 (g : S) g.2)⟩
  obtain ⟨k, hk⟩ := hTp.exists_card_eq
  have hT1 : 1 < Nat.card T := (Subgroup.one_lt_card_iff_ne_bot T).mpr hT0
  have hcard : Nat.card T = 2 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · rw [pow_zero] at hk
        omega
      · rw [pow_one] at hk
        exact hk
    · have h4 : 4 ≤ 2 ^ k :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
  obtain ⟨⟨t, htT⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT0
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  have htt : t * t = 1 := by
    have := hCor.1.2 t htT
    rwa [pow_two] at this
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have huniq : ∀ x ∈ T, x = 1 ∨ x = t := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥T)).mp hcard
      have h1 : (⟨x, hx⟩ : ↥T) = y := hy _ (fun h => hx1 (congrArg Subtype.val h))
      have h2 : (⟨t, htT⟩ : ↥T) = y := hy _ ht1'
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hisol : ∀ g : S, g * t * g⁻¹ * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    have hcommute : Commute (g * t * g⁻¹) t := hg
    have hconj : conjSubgroup g T = T := by
      refine (hCor.2.2 g).mp fun x hx y hy => ?_
      have hy' : g⁻¹ * y * g ∈ T := mem_conjSubgroup.mp hy
      have hye : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rcases huniq x hx with hx1 | hxt
      · rw [hx1]
        exact Commute.one_left y
      · rw [hxt]
        rcases huniq _ hy' with h | h
        · have hy1 : y = 1 := by
            rw [hye, h]
            group
          rw [hy1]
          exact Commute.one_right _
        · have hyc : y = g * t * g⁻¹ := by
            rw [hye, h]
          rw [hyc]
          exact hcommute.symm
    have hmem : g * t * g⁻¹ ∈ T := by
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      have : g * t * g⁻¹ ∈ conjSubgroup g T := mem_conjSubgroup.mpr (by rw [e]; exact htT)
      rwa [hconj] at this
    rcases huniq _ hmem with h | h
    · exfalso
      apply ht1
      have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [e, h]
      group
    · exact h
  haveI := Fintype.ofFinite S
  obtain ⟨N, hN, hNodd, hcomm⟩ := CFSG.Milestones.glauberman_zStar S t ht1 htt hisol
  refine CFSG.GF2Type.Aschbacher1976Common.not_inZStar_of_isSimpleGroup hnc hord ?_
  exact ⟨N, hN, hNodd, hcomm⟩

theorem listMaxElemAb_of_centralizerInvolutions (h : ListCentralizerInvolutionsStatement)
    (hsimple : ∀ (D : Type) [Group D] [Finite D], ListGroup D → IsSimpleGroup D)
    (hnc : ∀ (D : Type) [Group D] [Finite D], ListGroup D → ∃ a b : D, a * b ≠ b * a) :
    ListMaxElemAbStatement := by
  intro Y _ _ T E hT0 hCor hList hE hTE hEN
  set N : Subgroup Y := Subgroup.normalClosure (T : Set Y) with hN
  have hTN : T ≤ N := Subgroup.le_normalClosure
  have hT'0 : T.subgroupOf N ≠ ⊥ := by
    intro hbot
    apply hT0
    rw [eq_bot_iff]
    intro x hx
    have hxN : x ∈ N := hTN hx
    have hx' : (⟨x, hxN⟩ : ↥N) ∈ T.subgroupOf N := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  have hcor' : CorBHyp (T.subgroupOf N) := sec93f_corBHyp_subgroupOf hTN hCor
  haveI : IsSimpleGroup ↥N := hsimple _ hList
  have h4 : 4 ≤ Nat.card ↥(T.subgroupOf N) := sec93f_card_ge_four (hnc _ hList) hT'0 hcor'
  have hsub : E ≤ T := by
    intro e he
    have heN : e ∈ N := hEN he
    have hcent : (⟨e, heN⟩ : ↥N) ∈ Subgroup.centralizer ((T.subgroupOf N : Subgroup ↥N) :
        Set ↥N) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyT : (y : Y) ∈ T := hy
      have h1 := congrArg (fun z : ↥E => (z : Y))
        (hE.1.is_comm.comm ⟨(y : Y), hTE hyT⟩ ⟨e, he⟩)
      exact Subtype.ext h1
    have hsq : (⟨e, heN⟩ : ↥N) * ⟨e, heN⟩ = 1 := by
      refine Subtype.ext ?_
      have := hE.2 e he
      rw [pow_two] at this
      exact this
    exact h ↥N hList (T.subgroupOf N) h4 hcor' _ hcent hsq
  exact le_antisymm hsub hTE

theorem listWCBound_of_listFacts (h1 : ListCentralizerInvolutionsStatement)
    (h2 : ListOutElemAbelianBoundStatement)
    (hsimple : ∀ (D : Type) [Group D] [Finite D], ListGroup D → IsSimpleGroup D)
    (hnc : ∀ (D : Type) [Group D] [Finite D], ListGroup D → ∃ a b : D, a * b ≠ b * a) :
    ListWCBoundStatement :=
  listWCBound_of_parts (listMaxElemAb_of_centralizerInvolutions h1 hsimple hnc)
    (listOutRank_of_outElemAbelianBound h2) hsimple hnc

end CFSG.RankThree.GF2n.Stroth80
