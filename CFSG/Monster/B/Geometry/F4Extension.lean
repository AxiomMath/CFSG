module

public import CFSG.Monster.B.Geometry.GlobalExtension
public import CFSG.LieType.Chevalley.LongestElement

public section

namespace CFSG.Monster.B.Geometry

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.CosetBuilding

@[expose] def f4LongestWord : List (Fin Tag.F4.rank) :=
  (List.replicate 6 [(0 : Fin 4), 1, 2, 3]).flatten

@[expose] def f4WordAct (ω : List (Fin Tag.F4.rank)) (v : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → ℤ :=
  ω.foldr (fun i v => reflect .F4 i v) v

theorem f4WordAct_neg (j : Fin Tag.F4.rank) :
    f4WordAct f4LongestWord (Pi.single j 1) = -Pi.single j 1 := by
  revert j
  decide +kernel

theorem wordProd_smul
    (ω : List (Fin Tag.F4.rank)) (v : Fin Tag.F4.rank → ℤ) :
    (coxeterSystem .F4).wordProd ω • v = f4WordAct ω v := by
  induction ω with
  | nil => simp [f4WordAct]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih]
    exact simple_smul i _

theorem f4Longest_smul
    (v : Fin Tag.F4.rank → ℤ) :
    (coxeterSystem .F4).wordProd f4LongestWord • v = -v := by
  have hsum : v = ∑ j, v j • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) := by
    ext k
    simp [Pi.single_apply]
  rw [hsum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_def, map_zsmul, ← smul_def, wordProd_smul, f4WordAct_neg, smul_neg]

theorem longest_f4_eq :
    longest (coxeterSystem .F4) Set.univ = (coxeterSystem .F4).wordProd f4LongestWord := by
  have hrev : ReversesSigns ((coxeterSystem .F4).wordProd f4LongestWord) := by
    intro α _ hpos
    rw [f4Longest_smul, height_neg]
    omega
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element .F4
  have h := (reversesSigns_of_forall_length_le hmax).eq hrev
  have hl : IsLongest (coxeterSystem .F4) Set.univ w₀ :=
    ⟨by rw [CoxeterSystem.parabolic_univ]; trivial, fun v _ => hmax v⟩
  rw [← hl.eq_longest, h]

theorem longest_f4_central
    (w : WeylGroup .F4) :
    longest (coxeterSystem .F4) Set.univ * w = w * longest (coxeterSystem .F4) Set.univ := by
  rw [longest_f4_eq]
  refine ext_single fun j => ?_
  rw [mul_smul, mul_smul, f4Longest_smul, f4Longest_smul, smul_neg]

theorem card_f4_index : Nat.card (Fin Tag.F4.rank) = 4 := Nat.card_eq_fintype_card.trans rfl

variable {C : Type*} {δ : C → C → WeylGroup .F4} {C' : Type*} {δ' : C' → C' → WeylGroup .F4}

theorem F4_global_extension_from_rank_three_opposition
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hδ' : IsWeylDistanceBuilding (coxeterSystem .F4) δ')
    (hext : Ext₃ (coxeterSystem .F4) δ δ') (hrig : Rig₂ (coxeterSystem .F4) δ)
    (hrig' : Rig₂ (coxeterSystem .F4) δ') {c d : C} {c' d' : C'}
    (hcd : δ c d = longest (coxeterSystem .F4) Set.univ)
    (hcd' : δ' c' d' = longest (coxeterSystem .F4) Set.univ) {φ : C → C'}
    (hφ : IsWeylIsometry δ δ' (foundation (coxeterSystem .F4) δ 2 c ∪ {d})
      (foundation (coxeterSystem .F4) δ' 2 c' ∪ {d'}) φ)
    (hφc : φ c = c') (hφd : φ d = d') :
    ∃ F : C → C', IsTypeIso (coxeterSystem .F4) δ δ' Set.univ Set.univ F ∧
      Set.EqOn F φ (foundation (coxeterSystem .F4) δ 2 c ∪ {d}) ∧
      ∀ F' : C → C', IsTypeIso (coxeterSystem .F4) δ δ' Set.univ Set.univ F' →
        Set.EqOn F' φ (foundation (coxeterSystem .F4) δ 2 c ∪ {d}) → F' = F :=
  global_extension_of_rank_three_opposition hδ hδ' card_f4_index longest_f4_central hext hrig
    hrig' hcd hcd' hφ hφc hφd

end CFSG.Monster.B.Geometry
