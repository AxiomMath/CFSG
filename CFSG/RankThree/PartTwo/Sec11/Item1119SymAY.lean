module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSymTypes
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolIndexArg
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolExistsF
import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements

variable {G : Type} [Group G]

@[expose] noncomputable def sym1119Theta (a : G) : Subgroup G :=
  (aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))).map
    (Subgroup.centralizer ({a} : Set G)).subtype

@[expose] def sym1119Q (R : Subgroup G) (g a : G) : Subgroup G :=
  sec11P R g ⊓ Subgroup.centralizer ({a} : Set G)

end Statements

section Statements2


@[expose] def Sym1119YAlphaSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      Nat.card ↥(A ⊓ (Y ⊔ sym1119Theta a)) = 9 ∧ a ∉ A ⊓ (Y ⊔ sym1119Theta a)

@[expose] def Sym1119YAlphaComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      A ⊓ (Y ⊔ sym1119Theta a) ≤ ⁅sym1119Q R g a, sym1119Q R g a⁆

@[expose] def Sym1119CommLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sym1119Ctx G A c L a R Y d x s r g →
      ⁅sym1119Q R g a, sym1119Q R g a⁆ ≤ Y ⊔ sym1119Theta a

end Statements2

section Main


theorem centralizer_le_normalizer_sym1119Theta {G : Type} [Group G] [Finite G] (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((sym1119Theta a : Subgroup G) : Set G) := by
  intro y hy
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  obtain ⟨t', ht', rfl⟩ := ht
  refine ⟨⟨y, hy⟩ * t' * ⟨y, hy⟩⁻¹,
    (aschbacherSolvableCore_normal 3 _).conj_mem t' ht' ⟨y, hy⟩, ?_⟩
  simp

theorem not_three_dvd_card_sym1119Theta {G : Type} [Group G] [Finite G] (a : G) :
    ¬ 3 ∣ Nat.card (sym1119Theta a) := by
  unfold sym1119Theta
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact KFacts.not_three_dvd_card_aschbacherSolvableCore _

theorem step1119AY_of_yalpha (h45 : Sec4.Item4_5) (hS : Sym1119YAlphaSplit)
    (hC : Sym1119YAlphaComm) (hQ : Sym1119CommLe) : Step1119AY := by
  intro G _ _ A c L a R Y d x s r g hctx
  have h := hctx.big.toSec11Data
  obtain ⟨hcard, haB⟩ := hS G A c L a R Y d x s r g hctx
  have hBQ := hC G A c L a R Y d x s r g hctx
  have hQY := hQ G A c L a R Y d x s r g hctx
  have hAe := h.mem_partTwoF.1
  have hYC : Y ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hA3 : IsPGroup 3 A := fun u => ⟨1, by
    have := hAe.2 u.1 u.2
    ext
    simpa using this⟩
  have hBY : A ⊓ (Y ⊔ sym1119Theta a) ≤ Y :=
    Item1119Sym.le_of_normalizes_of_coprime Y (sym1119Theta a) _
      (hYC.trans (centralizer_le_normalizer_sym1119Theta a)) (not_three_dvd_card_sym1119Theta a)
      (IsPGroup.to_le hA3 inf_le_left) (inf_le_left.trans hAY) inf_le_right
  have hdY : d ∈ Y := h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hdB : d ∈ A ⊓ (Y ⊔ sym1119Theta a) := ⟨hdA, Subgroup.mem_sup_left hdY⟩
  have hd3 : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hd1 : d ≠ 1 := fun h1 => by simp [h1] at hd3
  obtain ⟨f, hfB, hfad, hfeq⟩ := Item1119Sym.exists_f_of_card_nine (A ⊓ (Y ⊔ sym1119Theta a)) a d
    hcard hdB hd1 (Item1117Proof.pow_three_of_mem_A h hdA) haB
    (Item1117Proof.pow_three_of_mem_A h h.a_mem)
    (Item1117Proof.commute_of_mem_A h h.a_mem hdA)
  refine ⟨f, hfB.1, hfad, hfeq ▸ hBY, ?_⟩
  rw [hfeq]
  exact le_antisymm (fun z hz => ⟨hBQ hz, hz.1⟩) (fun z hz => ⟨hz.2, hQY hz.1⟩)

end Main

end CFSG.RankThree.PartTwo.Sec11

end
