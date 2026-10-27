module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BFrame
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem asc80NoUMax_of_sporGenAt {s : TauCeti.SporadicName} (h : Asch54SporGenAt s) :
    Asc80NoUMax fun X _ => CFSG.Models.IsSporadic X s := by
  intro Q _ _ L T hLn hLs hnab hC hP hT
  rintro ⟨M, hM, hMax⟩
  have hgen := h Q L T hLn hP hC hT
  have hle : lGen IsCalL0 ⊤ T ≤ M := iSup₂_le fun X hX => hMax X hX.1 hX.2.1
  rw [hgen] at hle
  exact hM.ne (le_antisymm le_top hle)

theorem asc80ThmBCase_isSporadic {s : TauCeti.SporadicName}
    (h : Asc80NoUMax fun X _ => CFSG.Models.IsSporadic X s) :
    Asc80ThmBCase fun X _ => CFSG.Models.IsSporadic X s := by
  refine asc80ThmBCase_of_noUMax ?_ h
  intro X Y _ _ ⟨e⟩ hX
  obtain ⟨f⟩ := hX
  exact ⟨e.symm.trans f⟩

theorem asc80ThmBCase_of_sup_centralizer {P : ∀ (X : Type) [Group X], Prop}
    (hOut : ∀ (X : Type) [Group X] [Finite X], P X → Nat.card (Outer X) = 1)
    (hsup : ∀ (X : Type) [Group X] [Finite X], P X → ∀ t₁ t₂ : X, orderOf t₁ = 2 →
      orderOf t₂ = 2 → t₁ ≠ t₂ → centralizer ({t₁} : Set X) ⊔ centralizer {t₂} = ⊤)
    (hcomm : ∀ (X : Type) [Group X] [Finite X], P X → ∀ t : X, orderOf t = 2 →
      ∃ t' : X, orderOf t' = 2 ∧ t' ≠ t ∧ t * t' = t' * t) :
    Asc80ThmBCase P := by
  classical
  intro G _ _ H A M hs hnab hP hAH hA hM
  have S := asc80BSetup hs hnab hAH hA hM
  exfalso
  have hFH : Fstar H ≤ H := fstar_le_group H
  haveI : ((Fstar H).subgroupOf H).Normal := normal_subgroupOf_fstar H
  have hCent : Subgroup.centralizer (((Fstar H).subgroupOf H : Subgroup ↥H) : Set ↥H) = ⊥ := by
    rw [CFSG.centralizer_subgroupOf_eq (Fstar H) H hFH]
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : G) ∈ H ⊓ Subgroup.centralizer (Fstar H : Set G) := ⟨x.2, hx⟩
    rw [S.inf_centralizer] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hOutL : Nat.card (Outer ↥((Fstar H).subgroupOf H)) = 1 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (Subgroup.subgroupOfEquivOfLe hFH)).toEquiv]
    exact hOut ↥(Fstar H) hP
  have hLtop : (Fstar H).subgroupOf H = ⊤ := Subgroup.index_eq_one.1 (le_antisymm
    ((index_le_card_outer ((Fstar H).subgroupOf H) hCent).trans hOutL.le)
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite))
  have hFH' : H ≤ Fstar H := by
    intro x hx
    have hxL : (⟨x, hx⟩ : ↥H) ∈ (Fstar H).subgroupOf H := hLtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hxL
  obtain ⟨a, haA, ha1⟩ : ∃ a : G, a ∈ A ∧ a ≠ 1 := by
    by_contra h
    apply S.ne_bot
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have haord : orderOf a = 2 := orderOf_eq_prime (hA.2 a haA) ha1
  have haF : a ∈ Fstar H := hFH' (hAH haA)
  have hcommA : ∀ x ∈ A, x * a = a * x := fun x hx =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)
  have key : ∀ t₁ t₂ : ↥(Fstar H), orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ →
      A ≤ Subgroup.centralizer ({(t₁ : G)} : Set G) →
      A ≤ Subgroup.centralizer ({(t₂ : G)} : Set G) → False := by
    intro t₁ t₂ ht₁ ht₂ htne hAc₁ hAc₂
    have hne1 : t₁ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht₁
      exact absurd ht₁ (by norm_num)
    have hne2 : t₂ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht₂
      exact absurd ht₂ (by norm_num)
    have hsupH := hsup ↥(Fstar H) hP t₁ t₂ ht₁ ht₂ htne
    have hlt : ∀ t : ↥(Fstar H), t ≠ 1 →
        H ⊓ Subgroup.centralizer ({(t : G)} : Set G) < H := by
      intro t ht1
      refine lt_of_le_of_ne inf_le_left ?_
      intro hKeq
      have hHle : H ≤ Subgroup.centralizer ({(t : G)} : Set G) :=
        hKeq.symm.le.trans inf_le_right
      have hmem : (t : G) ∈ H ⊓ Subgroup.centralizer (Fstar H : Set G) := by
        refine ⟨hFH t.2, ?_⟩
        change (t : G) ∈ Subgroup.centralizer (Fstar H : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        exact (Subgroup.mem_centralizer_iff.mp (hHle (hFH hf)) (t : G) (by simp)).symm
      rw [S.inf_centralizer] at hmem
      exact ht1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
    have hK₁M : H ⊓ Subgroup.centralizer ({(t₁ : G)} : Set G) ≤ M :=
      S.le_of_lt _ (le_inf hAH hAc₁) (hlt t₁ hne1)
    have hK₂M : H ⊓ Subgroup.centralizer ({(t₂ : G)} : Set G) ≤ M :=
      S.le_of_lt _ (le_inf hAH hAc₂) (hlt t₂ hne2)
    have hmap₁ : (Subgroup.centralizer ({t₁} : Set ↥(Fstar H))).map (Fstar H).subtype ≤
        H ⊓ Subgroup.centralizer ({(t₁ : G)} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hFH y.2, ?_⟩
      change y ∈ Subgroup.centralizer ({t₁} : Set ↥(Fstar H)) at hy
      change (y : G) ∈ Subgroup.centralizer ({(t₁ : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff] at hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact congrArg Subtype.val (hy t₁ (by simp))
    have hmap₂ : (Subgroup.centralizer ({t₂} : Set ↥(Fstar H))).map (Fstar H).subtype ≤
        H ⊓ Subgroup.centralizer ({(t₂ : G)} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hFH y.2, ?_⟩
      change y ∈ Subgroup.centralizer ({t₂} : Set ↥(Fstar H)) at hy
      change (y : G) ∈ Subgroup.centralizer ({(t₂ : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff] at hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact congrArg Subtype.val (hy t₂ (by simp))
    have hFK : Fstar H ≤ M := by
      calc Fstar H = (⊤ : Subgroup ↥(Fstar H)).map (Fstar H).subtype := by
            rw [Subgroup.map_top, Subgroup.range_subtype]
        _ = ((Subgroup.centralizer ({t₁} : Set ↥(Fstar H))) ⊔
              Subgroup.centralizer ({t₂} : Set ↥(Fstar H))).map (Fstar H).subtype := by
            rw [hsupH]
        _ = (Subgroup.centralizer ({t₁} : Set ↥(Fstar H))).map (Fstar H).subtype ⊔
              (Subgroup.centralizer ({t₂} : Set ↥(Fstar H))).map (Fstar H).subtype :=
            Subgroup.map_sup _ _ _
        _ ≤ (H ⊓ Subgroup.centralizer ({(t₁ : G)} : Set G)) ⊔
              (H ⊓ Subgroup.centralizer ({(t₂ : G)} : Set G)) := sup_le_sup hmap₁ hmap₂
        _ ≤ M := sup_le hK₁M hK₂M
    exact S.not_fstar_le hFK
  by_cases hAbig : ∃ b : G, b ∈ A ∧ b ≠ 1 ∧ b ≠ a
  ·
    obtain ⟨b, hbA, hb1, hba⟩ := hAbig
    have hbF : b ∈ Fstar H := hFH' (hAH hbA)
    have ht₁ : orderOf (⟨a, haF⟩ : ↥(Fstar H)) = 2 :=
      (Subgroup.orderOf_mk a haF).trans haord
    have ht₂ : orderOf (⟨b, hbF⟩ : ↥(Fstar H)) = 2 :=
      (Subgroup.orderOf_mk b hbF).trans
        (orderOf_eq_prime (hA.2 b hbA) hb1)
    have htne : (⟨a, haF⟩ : ↥(Fstar H)) ≠ ⟨b, hbF⟩ := by
      intro h
      exact hba (congrArg Subtype.val h).symm
    refine key _ _ ht₁ ht₂ htne ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommA x hx
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩)
  ·
    have hA2 : ∀ x ∈ A, x = 1 ∨ x = a := by
      intro x hx
      by_contra h
      push Not at h
      exact hAbig ⟨x, hx, h.1, h.2⟩
    obtain ⟨c, hc2, hcne, hccomm⟩ := hcomm ↥(Fstar H) hP (⟨a, haF⟩ : ↥(Fstar H))
      ((Subgroup.orderOf_mk a haF).trans haord)
    have hacomm : a * (c : G) = (c : G) * a := congrArg Subtype.val hccomm
    have ht₁ : orderOf (⟨a, haF⟩ : ↥(Fstar H)) = 2 :=
      (Subgroup.orderOf_mk a haF).trans haord
    refine key _ _ ht₁ hc2 (fun h => hcne h.symm) ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommA x hx
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hA2 x hx with h1 | ha
      · rw [h1]; simp
      · rw [ha]; exact hacomm

end CFSG.LocalAnalysis.WeakClosure81

end
