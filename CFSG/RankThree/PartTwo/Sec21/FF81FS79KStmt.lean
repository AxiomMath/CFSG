module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Final
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Iso
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Local

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

def Prop2OneAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (b t c : G) (J : Subgroup G),
    orderOf b = 3 → orderOf t = 2 → t * b * t⁻¹ = b⁻¹ →
    Nonempty (↥J ≃* Equiv.Perm (Fin 3)) → J ≤ Cen b → J ≤ Cen t →
    Nor (Subgroup.zpowers b) ≤ Nor J →
    setMul (Opp 3 (Nor (Subgroup.zpowers b))) (Subgroup.closure {b, t} ⊔ J) =
      Nor (Subgroup.zpowers b) →
    c ∈ J → orderOf c = 3 →
    setMul (Opp 3 (Nor (Subgroup.zpowers c)))
      (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers c)) = Nor (Subgroup.zpowers c) →
    (∀ R : Subgroup G, IsPGroup 2 R → Subgroup.closure {b, c} ≤ Nor R → R = ⊥) →
    (∀ h : G, conjBy h (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) →
      conjBy h (Subgroup.zpowers b) = Subgroup.zpowers b) →
    setMul (Opp 3 (⊤ : Subgroup G)) (Nor (Subgroup.zpowers b)) = Set.univ

def KF_FS79Prop2OneK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KCore.KGroupNonab InCatalog G → Prop2OneAt G

def Prop2At (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (b t b₁ b₂ : H) (J : Subgroup H),
    orderOf b = 3 → orderOf t = 2 → t * b * t⁻¹ = b⁻¹ →
    Nonempty (↥J ≃* Equiv.Perm (Fin 6)) → J ≤ Cen b → J ≤ Cen t →
    Nor (Subgroup.zpowers b) ≤ Nor J →
    setMul (Opp 3 (Nor (Subgroup.zpowers b))) (Subgroup.closure {b, t} ⊔ J) =
      Nor (Subgroup.zpowers b) →
    b₁ ∈ J → b₂ ∈ J → IsElemAb 3 2 (Subgroup.closure {b₁, b₂}) →
    (∀ n ∈ J ⊓ Nor (Subgroup.closure {b₁, b₂}), ∀ x ∈ ({b₁, b₂} : Set H),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹} : Set H)) →
    (∀ x ∈ ({b₁, b₂} : Set H), setMul (Opp 3 (Nor (Subgroup.zpowers x)))
      (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers x)) = Nor (Subgroup.zpowers x)) →
    (∀ R : Subgroup H, IsPGroup 2 R → Subgroup.closure {b, b₁, b₂} ≤ Nor R → R = ⊥) →
    (∀ h : H, conjBy h (Subgroup.zpowers b) ≤ Nor (Subgroup.zpowers b) →
      conjBy h (Subgroup.zpowers b) = Subgroup.zpowers b) →
    setMul (Opp 3 (⊤ : Subgroup H)) (Nor (Subgroup.zpowers b)) = Set.univ

def KF_FS79Prop2K : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H → Prop2At H

def FS79R34K : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
    ∀ (b t b₁ b₂ : H) (J : Subgroup H), FS79Hyp b t b₁ b₂ J → R34Stmt b b₁ b₂

def FS79R38K : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
    ∀ (b t b₁ b₂ : H) (J : Subgroup H) (S : Std b t b₁ b₂ J), R38Stmt b (J6.T1.map S.ι)

def FS79R38'K : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
    ∀ (b t b₁ b₂ : H) (J : Subgroup H) (S : Std b t b₁ b₂ J), R38Stmt b (J6.V1.map S.ι)

theorem kf_fs79Prop2K_of_hyp
    (h : ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
      ∀ (b t b₁ b₂ : H) (J : Subgroup H), FS79Hyp b t b₁ b₂ J →
        setMul (Opp 3 (⊤ : Subgroup H)) (Nor (Subgroup.zpowers b)) = Set.univ) :
    KF_FS79Prop2K := by
  intro H _ _ hK b t b₁ b₂ J hb ht htb hJ hJb hJt hNJ hN hb₁ hb₂ hE hmono hNbi hno hweak
  exact h H hK b t b₁ b₂ J ⟨hb, ht, htb, hJ, hJb, hJt, hNJ, hN, hb₁, hb₂, hE, hmono, hNbi, hno,
    hweak⟩

theorem kf_fs79Prop2K_of_local (h34 : FS79R34K) (h38 : FS79R38K) (h38' : FS79R38'K) :
    KF_FS79Prop2K := by
  refine kf_fs79Prop2K_of_hyp ?_
  intro H _ _ hK b t b₁ b₂ J hH
  have S : Std b t b₁ b₂ J := hH.std
  have hR34 : R34Stmt b b₁ b₂ := h34 H hK b t b₁ b₂ J hH
  have hiso : ∀ g : H, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    rcases S.dichotomy hR34 with hXi | hXi
    · exact S.isolated_of_frame J6.T1 J6.V1 J6.T1_le_R (fun s hs => J6.T1fin_sq s hs)
        (fun a ha c hc => J6.T1fin_comm a ha c hc) J6.card_T1 J6.card_Nor_T1 J6.R_norm_T1
        J6.R_conj_T1 (fun X hX hc hs hco => S.E16 X hX hc hs hco) (S.not_conj_TV hR34) hXi
        (h38 H hK b t b₁ b₂ J S)
    · refine S.isolated_of_frame J6.V1 J6.T1 J6.V1_le_R (fun s hs => J6.V1fin_sq s hs)
        (fun a ha c hc => J6.V1fin_comm a ha c hc) J6.card_V1 J6.card_Nor_V1 J6.R_norm_V1
        J6.R_conj_V1 (fun X hX hc hs hco => (S.E16 X hX hc hs hco).symm) ?_ hXi
        (h38' H hK b t b₁ b₂ J S)
      intro g hg
      apply S.not_conj_TV hR34 g⁻¹
      rw [← hg]
      exact L14.conjBy_conjBy_inv g _
  exact hH.conclusion_of_isolated hiso

end CFSG.RankThree.PartTwo.Sec21.FF81
