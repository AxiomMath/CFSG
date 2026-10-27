module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf {X N : Subgroup G} (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) {g n : G} (hg : g ∈ X) (hn : n ∈ N) : g * n * g⁻¹ ∈ N := by
  have h := hN.conj_mem ⟨n, hNX hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem mul_comm_of_inf_eq_bot_of_normal {X S T : Subgroup G} (hSX : S ≤ X) (hTX : T ≤ X)
    (hS : (S.subgroupOf X).Normal) (hT : (T.subgroupOf X).Normal) (hdis : S ⊓ T = ⊥) {s t : G}
    (hs : s ∈ S) (ht : t ∈ T) : s * t = t * s := by
  have hs' : t * s⁻¹ * t⁻¹ ∈ S :=
    b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf hSX hS (hTX ht) (inv_mem hs)
  have ht' : s * t * s⁻¹ ∈ T :=
    b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf hTX hT (hSX hs) ht
  have hc : s * t * s⁻¹ * t⁻¹ = 1 := by
    have hmemS : s * t * s⁻¹ * t⁻¹ ∈ S := by
      have heq : s * t * s⁻¹ * t⁻¹ = s * (t * s⁻¹ * t⁻¹) := by group
      rw [heq]
      exact mul_mem hs hs'
    have hmemT : s * t * s⁻¹ * t⁻¹ ∈ T := by
      have heq : s * t * s⁻¹ * t⁻¹ = (s * t * s⁻¹) * t⁻¹ := by group
      rw [heq]
      exact mul_mem ht' (inv_mem ht)
    have hmem : s * t * s⁻¹ * t⁻¹ ∈ S ⊓ T := ⟨hmemS, hmemT⟩
    rw [hdis] at hmem
    exact Subgroup.mem_bot.1 hmem
  have h2 : s * t * s⁻¹ = t := mul_inv_eq_one.1 hc
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem conjSubgroup_le_and_normal {H X S : Subgroup G} (hXH : X ≤ H)
    (hX : (X.subgroupOf H).Normal) (hSX : S ≤ X) (hS : (S.subgroupOf X).Normal) {a : G}
    (ha : a ∈ H) : conjSubgroup S a ≤ X ∧ ((conjSubgroup S a).subgroupOf X).Normal := by
  constructor
  · intro x hx
    have hxa : a * x * a⁻¹ ∈ S := mem_conjSubgroup_iff.1 hx
    have hmem : a * x * a⁻¹ ∈ X := hSX hxa
    have hconj : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ ∈ X :=
      b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf hXH hX (inv_mem ha) hmem
    have heq : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [heq] at hconj
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [mem_conjSubgroup_iff] at hn ⊢
    have hgX : a * (g : G) * a⁻¹ ∈ X :=
      b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf hXH hX ha g.2
    have hnS : a * (n : G) * a⁻¹ ∈ S := hn
    have hconjS : (a * (g : G) * a⁻¹) * (a * (n : G) * a⁻¹) * (a * (g : G) * a⁻¹)⁻¹ ∈ S :=
      b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf hSX hS hgX hnS
    have heq : a * ((g * n * g⁻¹ : ↥X) : G) * a⁻¹ =
        (a * (g : G) * a⁻¹) * (a * (n : G) * a⁻¹) * (a * (g : G) * a⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact hconjS

theorem mem_of_commute_of_maxOver_eq_singleton {H M A : Subgroup G} (h : Sec5Hyp H M A)
    (hM : maxOver H A = {M}) (hK : kerMOf M H = ⊥) {a g : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hg : g ∈ H) (hcomm : g * a = a * g) : g ∈ M := by
  let C : Subgroup G := H ⊓ Subgroup.centralizer ({a} : Set G)
  have hAC : A ≤ C := by
    intro b hb
    have hbH : b ∈ H := h.le_group hb
    have hcommb : b * a = a * b :=
      congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    exact ⟨hbH, Subgroup.mem_centralizer_singleton_iff.2 hcommb⟩
  rcases le_or_eq_of_maxOver_eq_singleton hM inf_le_left hAC with hCM | hCH
  · exact hCM ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  · exfalso
    have hall : ∀ x ∈ H, x * a = a * x := by
      intro x hx
      have hxc : x ∈ C := by
        change x ∈ H ⊓ Subgroup.centralizer ({a} : Set G)
        rw [hCH]
        exact hx
      exact Subgroup.mem_centralizer_singleton_iff.1 hxc.2
    let Z : Subgroup G := Subgroup.zpowers a
    have hZH : Z ≤ H := Subgroup.zpowers_le.2 (h.le_group ha)
    have hZM : Z ≤ M := Subgroup.zpowers_le.2 (h.le_M ha)
    have hZn : (Z.subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      have hga : Commute (g : G) a := hall (g : G) g.2
      have hgk : (g : G) * a ^ k = a ^ k * (g : G) := hga.zpow_right k
      have hnk : (n : G) = a ^ k := hk.symm
      have hconj : (g : G) * (n : G) * (g : G)⁻¹ = a ^ k := by
        rw [hnk, hgk]
        group
      have hgoal : a ^ k = ((g * n * g⁻¹ : ↥H) : G) := by
        rw [← hconj]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hgoal
    have hle : Z ≤ kerMOf M H := le_kerMOf_of_normal hZH hZn hZM
    rw [hK] at hle
    have haZ : a ∈ Z := Subgroup.mem_zpowers a
    have hazero : a = 1 := Subgroup.mem_bot.1 (hle haZ)
    exact ha1 hazero

theorem le_M_of_not_mem_normalizer {H M A X S : Subgroup G} (h : Sec5Hyp H M A)
    (hM : maxOver H A = {M}) (hK : kerMOf M H = ⊥) (hXH : X ≤ H) (hX : (X.subgroupOf H).Normal)
    (hSX : S ≤ X) (hS : (S.subgroupOf X).Normal) (hsimple : IsSimpleGroup ↥S)
    (hnab : ¬ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {a : G} (ha : a ∈ A)
    (hna : a ∉ Subgroup.normalizer (S : Set G)) : S ≤ M := by
  haveI := hsimple
  have haH : a ∈ H := h.le_group ha
  have ha1 : a ≠ 1 := by
    intro h1
    exact hna (by rw [h1]; exact Subgroup.one_mem _)
  have haa : a * a = 1 := by
    have h := h.isElemAbelian.2 a ha
    simpa [pow_two] using h
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hMH : M ≤ H := (isUniqueMaxOver_iff.1 hM).1.le
  let S' : Subgroup G := conjSubgroup S a
  have hS'X : S' ≤ X := (conjSubgroup_le_and_normal hXH hX hSX hS haH).1
  have hS'n : (S'.subgroupOf X).Normal := (conjSubgroup_le_and_normal hXH hX hSX hS haH).2
  have hdis : S ⊓ S' = ⊥ := by
    let W : Subgroup ↥S := (S ⊓ S').subgroupOf S
    have hWn : W.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨mul_mem (mul_mem g.2 hn.1) (inv_mem (s := S) (x := (g : G)) g.2),
        b5_FiveFiveSwap_conj_mem_of_normal_subgroupOf hS'X hS'n (hSX g.2) hn.2⟩
    haveI : W.Normal := hWn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hW | hW
    · ext x
      constructor
      · intro hx
        have hxW : (⟨x, hx.1⟩ : ↥S) ∈ W := by
          rw [Subgroup.mem_subgroupOf]
          exact hx
        rw [hW] at hxW
        have hx1 : (⟨x, hx.1⟩ : ↥S) = 1 := Subgroup.mem_bot.1 hxW
        simpa using congrArg Subtype.val hx1
      · intro hx
        rw [Subgroup.mem_bot] at hx
        rw [hx]
        exact ⟨one_mem _, one_mem _⟩
    · exfalso
      change (S ⊓ S').subgroupOf S = ⊤ at hW
      have hle : S ≤ S ⊓ S' := Subgroup.subgroupOf_eq_top.1 hW
      have hS'card : Nat.card ↥S' = Nat.card ↥S := by
        have hcard := Subgroup.card_map_of_injective (K := S)
          (f := (MulAut.conj a⁻¹).toMonoidHom) (MulAut.conj a⁻¹).injective
        simpa [S', conjSubgroup] using hcard
      have hle' : S ≤ S' := hle.trans inf_le_right
      have hSeq : S = S' := Subgroup.eq_of_le_of_card_ge hle' hS'card.le
      have hconj : conjSubgroup S a = S := hSeq.symm
      exact hna (conjSubgroup_eq_iff_mem_normalizer.1 hconj)
  have hcomm : ∀ s ∈ S, ∀ t ∈ S', s * t = t * s := by
    intro s hs t ht
    exact mul_comm_of_inf_eq_bot_of_normal hSX hS'X hS hS'n hdis hs ht
  have hdeltaM : ∀ s ∈ S, s * (a⁻¹ * s * a) ∈ M := by
    intro s hs
    have hs' : a⁻¹ * s * a ∈ S' := by
      rw [mem_conjSubgroup_iff]
      have heq : a * (a⁻¹ * s * a) * a⁻¹ = s := by group
      rw [heq]
      exact hs
    have hsH : s ∈ H := hXH (hSX hs)
    have hs'H : a⁻¹ * s * a ∈ H := hXH (hS'X hs')
    have hconj : a * (s * (a⁻¹ * s * a)) * a⁻¹ = s * (a⁻¹ * s * a) := by
      have hsp : a * (a⁻¹ * s * a) * a⁻¹ = s := by group
      have hsp' : a * s * a⁻¹ = a⁻¹ * s * a := by rw [hinv]
      calc a * (s * (a⁻¹ * s * a)) * a⁻¹
          = (a * s * a⁻¹) * (a * (a⁻¹ * s * a) * a⁻¹) := by group
        _ = (a⁻¹ * s * a) * s := by rw [hsp, hsp']
        _ = s * (a⁻¹ * s * a) := (hcomm s hs (a⁻¹ * s * a) hs').symm
    exact mem_of_commute_of_maxOver_eq_singleton h hM hK ha ha1 (mul_mem hsH hs'H)
      (mul_inv_eq_iff_eq_mul.1 hconj).symm
  have hnorm : ((S ⊓ M).subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨mul_mem (mul_mem g.2 hn.1) (inv_mem (s := S) (x := (g : G)) g.2), ?_⟩
    have hs' : a⁻¹ * (g : G) * a ∈ S' := by
      rw [mem_conjSubgroup_iff]
      have heq : a * (a⁻¹ * (g : G) * a) * a⁻¹ = (g : G) := by group
      rw [heq]
      exact g.2
    have hδm : (g : G) * (a⁻¹ * (g : G) * a) ∈ M := hdeltaM (g : G) g.2
    have hcomm' : (a⁻¹ * (g : G) * a) * (n : G) = (n : G) * (a⁻¹ * (g : G) * a) :=
      (hcomm (n : G) hn.1 (a⁻¹ * (g : G) * a) hs').symm
    have hmemM : ((g : G) * (a⁻¹ * (g : G) * a)) * (n : G)
        * ((g : G) * (a⁻¹ * (g : G) * a))⁻¹ ∈ M :=
      mul_mem (mul_mem hδm hn.2) (inv_mem hδm)
    have heq : ((g : G) * (a⁻¹ * (g : G) * a)) * (n : G)
        * ((g : G) * (a⁻¹ * (g : G) * a))⁻¹ =
        (g : G) * (n : G) * (g : G)⁻¹ := by
      calc ((g : G) * (a⁻¹ * (g : G) * a)) * (n : G)
            * ((g : G) * (a⁻¹ * (g : G) * a))⁻¹
          = (g : G) * ((a⁻¹ * (g : G) * a) * (n : G)
              * (a⁻¹ * (g : G) * a)⁻¹) * (g : G)⁻¹ := by group
        _ = (g : G) * (n : G) * (g : G)⁻¹ := by rw [hcomm']; group
    have hcoe : ((g * n * g⁻¹ : ↥S) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, ← heq]
    exact hmemM
  haveI : ((S ⊓ M).subgroupOf S).Normal := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S ⊓ M).subgroupOf S) with hbot | htop
  · exfalso
    have hdisM : S ⊓ M = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxW : (⟨x, hx.1⟩ : ↥S) ∈ (S ⊓ M).subgroupOf S := by
          rw [Subgroup.mem_subgroupOf]
          exact hx
        rw [hbot] at hxW
        have hx1 : (⟨x, hx.1⟩ : ↥S) = 1 := Subgroup.mem_bot.1 hxW
        simpa using congrArg Subtype.val hx1
      · intro hx
        rw [Subgroup.mem_bot] at hx
        rw [hx]
        exact ⟨one_mem _, one_mem _⟩
    exact inf_ne_bot_of_odd_relIndex hMH h.odd_relIndex hXH hX hSX hS hsimple hnab hdisM
  · have hle : S ≤ S ⊓ M := Subgroup.subgroupOf_eq_top.1 htop
    exact hle.trans inf_le_right

end CFSG.LocalAnalysis.WeakClosure81
