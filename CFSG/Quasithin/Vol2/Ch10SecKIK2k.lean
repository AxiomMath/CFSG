module

public import CFSG.Quasithin.Background.A3Structure318Star
public import CFSG.Quasithin.Vol2.Ch10SecKIK2g

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF

variable {Γ : Type} [Group Γ] [Finite Γ] {H R J L V : Subgroup Γ} {hV : IsElemAbelian 2 V}

theorem sqtkHypCat_y (hc : S5Core H R J L V hV) :
    Vol2Native.SQTKHypCat (↥J ⧸ CFSG.pCore 2 ↥J) :=
  C10E4.sqtkHypCat_quot (le_of_mem_cComp hc.2.2.2.1) (SQTKGroup.isSQTKCat hc.1)

theorem y_structure (h36 : A36ForSQTK) (hc : S5Core H R J L V hV)
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hJN : J ≤ Subgroup.normalizer (V : Set Γ))
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ)) :
    (piJ hV hJN hO).ker ≤ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) ∧
      (Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 1 ∨
        Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 3) ∧
      (Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = Nat.card ↥(autI hV J) ∨
        Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 3 * Nat.card ↥(autI hV J)) := by
  set Y := ↥J ⧸ CFSG.pCore 2 ↥J
  set π := piJ hV hJN hO with hπ
  have hπs := piJ_surjective hV hJN hO
  have hJq := isQuasisimple_of_open hc.2.2.2.2.2.2.2.2.2.1
  have hker : π.ker ≤ Subgroup.center Y := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (inferInstance : π.ker.Normal) with h | h
    · exfalso
      have : Nontrivial ↥(autI hV J) := CFSG.LocalCores.isQuasisimple_nontrivial hJq
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥(autI hV J))
      obtain ⟨y, rfl⟩ := hπs x
      exact hx (by have : y ∈ π.ker := by rw [h]; trivial
                   exact this)
    · exact h
  have hYc := sqtkHypCat_y hc
  have h36Y := h36 _ (sqtkHyp_of_cat hYc)
  have hT := C10E4.top_mem_cComp_quot hc.2.2.2.1
  have hqT : CFSG.IsQuasisimple ↥(⊤ : Subgroup Y) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mpr hq
  have hZT : Nat.card (Subgroup.center ↥(⊤ : Subgroup Y)) = Nat.card (Subgroup.center Y) :=
    Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv
  have hZ : Nat.card (Subgroup.center Y) = 1 ∨ Nat.card (Subgroup.center Y) = 3 := by
    rw [← hZT]
    rcases (h36Y ⊤ hT).1 with ⟨-, hs, -⟩ | ⟨-, h3, -⟩ | h3 | h4
    · left
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(⊤ : Subgroup Y)) with
        h | h
      · rw [h, Subgroup.card_bot]
      · exfalso
        obtain ⟨a, b, hab⟩ := hqT.2.2
        have : Subsingleton (↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y)) :=
          QuotientGroup.subsingleton_iff.mpr h
        exact hab (Subsingleton.elim _ _)
    · exact Or.inr h3
    · exact absurd (Or.inl h3) (A318.not_case34_of_quasisimple hqT)
    · exact absurd (Or.inr h4) (A318.not_case34_of_quasisimple hqT)
  refine ⟨hker, hZ, ?_⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hπs
  have hdvd : Nat.card π.ker ∣ Nat.card (Subgroup.center Y) := Subgroup.card_dvd_of_le hker
  rcases hZ with h1 | h3
  · rw [h1, Nat.dvd_one] at hdvd
    left
    rw [← hcard, hdvd, one_mul]
  · rw [h3] at hdvd
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · left
      rw [← hcard, h, one_mul]
    · right
      rw [← hcard, h]

theorem lbar_ne_top (hc : S5Core H R J L V hV) (hJN : J ≤ Subgroup.normalizer (V : Set Γ))
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ)) : modO2Image J L ≠ ⊤ := by
  intro htop
  apply hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hJq := isQuasisimple_of_open hc.2.2.2.2.2.2.2.2.2.1
  have hNs : Group.IsSolvable ↥(⊥ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) :=
    Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  exact autI_eq_of_sup hV hJN hO hJq hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hNs (by rw [htop, sup_bot_eq])

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
