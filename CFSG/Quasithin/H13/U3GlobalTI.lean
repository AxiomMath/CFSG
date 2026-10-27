module

public import CFSG.Quasithin.H13.U3Basic
public import CFSG.Quasithin.SteinbergBMTIPairCalculus

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Module CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem binary_six_global_TI_conjugates_with_mutual_normalizer_commute [Finite G]
    {V : Subgroup G} [IsElementaryAbelian 2 V] (hV : Nat.card V = 64)
    (hTI : ∀ x : G, V ⊓ CFSG.conjugate V x = ⊥ ∨ CFSG.conjugate V x = V)
    (b : LinearMap.BilinForm (ZMod 2) (Additive V))
    (hprof : QTBinarySixProfile b (u3ConjLin V (normalizer (V : Set G)) le_rfl).range) :
    (∀ g : G, (V ⊓ normalizer (CFSG.conjugate V g : Set G) ≠ ⊥ ∨
        CFSG.conjugate V g ⊓ normalizer (V : Set G) ≠ ⊥) → ⁅V, CFSG.conjugate V g⁆ = ⊥) ∧
      ∀ T : Subgroup G, T ≤ normalizer (V : Set G) →
        (∀ g : G, CFSG.conjugate V g ⊓ T ≠ ⊥ → ⁅V, CFSG.conjugate V g⁆ = ⊥) ∧
        (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤
          T ⊓ centralizer (V : Set G) := by
  classical
  set N := normalizer (V : Set G) with hN
  set φ := u3ConjLin V N le_rfl with hφ
  obtain ⟨hVc, hV2⟩ := SteinbergBM.elementaryAbelian_two_facts (inferInstance :
    IsElementaryAbelian 2 V)
  have hVbot : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV
    norm_num at hV
  obtain ⟨-, -, -, -, -, hprofE⟩ := hprof
  have main : ∀ g : G, (V ⊓ normalizer (CFSG.conjugate V g : Set G) ≠ ⊥ ∨
      CFSG.conjugate V g ⊓ normalizer (V : Set G) ≠ ⊥) → ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
    intro g hg
    set A := CFSG.conjugate V g with hA
    have hAe : IsElementaryAbelian 2 A := isElementaryAbelian_conjugate V g
    obtain ⟨hAc, hA2⟩ := SteinbergBM.elementaryAbelian_two_facts hAe
    have hAcard : Nat.card A = 64 := (card_conjugate V g).trans hV
    have hATI := conjugate_TI hTI g
    rcases hTI g with hVA | hAV
    swap
    · rw [show A = V from hAV, commutator_eq_bot_iff_le_centralizer]
      intro x hx
      exact mem_centralizer_iff.2 fun y hy => hVc y hy x hx
    have hU : V ⊓ normalizer (A : Set G) ≠ ⊥ := by
      rcases hg with h | h
      · exact h
      · obtain ⟨⟨a, haA, haN⟩, ha1⟩ := ne_bot_iff_exists_ne_one.mp h
        have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
        obtain ⟨v, hv, hv1, hav⟩ :=
          SteinbergBM.exists_ne_one_commute hVc hV2 hVbot haN (hA2 a haA)
        have hvN : v ∈ normalizer (A : Set G) :=
          SteinbergBM.mem_normalizer_of_commute_of_TI hATI haA ha1' hav.symm
        exact ne_bot_iff_exists_ne_one.mpr ⟨⟨v, hv, hvN⟩, fun h' => hv1 (congrArg Subtype.val h')⟩
    have hcalc := SteinbergBM.equal_rank_elementary_TI_pair_mutual_normalizer_calculus (n := 6)
      inferInstance hAe (hV.trans (by norm_num)) (hAcard.trans (by norm_num)) hVA hTI hATI hU
    obtain ⟨hB1, -, -, ⟨-, -, hUB⟩, -, -, -, hUeq, hUlt⟩ := hcalc
    rcases (inf_le_left : V ⊓ normalizer (A : Set G) ≤ V).lt_or_eq with hlt | heq
    swap
    · exact (hUeq heq).2
    exfalso
    obtain ⟨-, hUBcard, hfaith, hCb, -⟩ := hUlt hlt
    set U := V ⊓ normalizer (A : Set G) with hUdef
    set B := A ⊓ normalizer (V : Set G) with hBdef
    have hBN : B ≤ N := inf_le_right
    have hUcB : U ≤ centralizer (B : Set G) := commutator_eq_bot_iff_le_centralizer.1 hUB
    set SB := B.subgroupOf N with hSB
    set E := SB.map φ with hE
    have hφinj : ∀ s ∈ SB, φ s = 1 → s = 1 := by
      intro s hs h1
      have h2 := (u3ConjLin_eq_one_iff s).1 h1
      have h3 := hfaith s hs fun v hv => by
        rw [← mem_centralizer_iff.1 h2 v hv, mul_inv_cancel_right]
      exact Subtype.ext h3
    have hEcard : Nat.card E = Nat.card B := by
      have hinj : Function.Injective (φ.comp SB.subtype) := by
        rw [injective_iff_map_eq_one]
        intro s hs
        exact Subtype.ext (hφinj s s.2 hs)
      have h1 : (φ.comp SB.subtype).range = E := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← h1, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
        Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv]
    have hEelt : ∀ e ∈ E, e ≠ 1 → ∃ s : N, (s : G) ∈ B ∧ (s : G) ≠ 1 ∧ φ s = e := by
      rintro _ ⟨s, hs, rfl⟩ he
      exact ⟨s, hs, fun h => he (by rw [show s = 1 from Subtype.ext h, map_one]), rfl⟩
    have hkerU : ∀ s : N, (s : G) ∈ B → (s : G) ≠ 1 →
        LinearMap.ker ((φ s : Additive V →ₗ[ZMod 2] Additive V) - LinearMap.id) = subOf V U := by
      intro s hs hs1
      rw [ker_u3ConjLin_sub_id]
      refine le_antisymm (subOf_le_subOf (by rw [hCb _ hs hs1]))
        (subOf_le_subOf fun x hx => ?_)
      have h1 : x ∈ V ⊓ centralizer ({(s : G)} : Set G) := by
        rw [hCb _ hs hs1]
        exact hx.2
      exact h1.2
    have hfixE : linFix E = subOf V U := by
      obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := ne_bot_iff_exists_ne_one.mp hB1
      have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
      refine le_antisymm ((linFix_le_ker (show φ ⟨b₀, hBN hb₀⟩ ∈ E from
        ⟨⟨b₀, hBN hb₀⟩, hb₀, rfl⟩)).trans (hkerU ⟨b₀, hBN hb₀⟩ hb₀ hb₀1').le) ?_
      rw [hE, linFix_map_u3ConjLin]
      refine subOf_le_subOf fun x hx => ?_
      rw [subgroupOf_map_subtype, inf_of_le_left hBN]
      exact hUcB hx.2
    have hU8 : 8 ≤ Nat.card U := by
      obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := ne_bot_iff_exists_ne_one.mp hB1
      have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
      have h1 := SteinbergBM.card_le_card_inf_centralizer_sq hVc hV2 hb₀.2 (hA2 b₀ hb₀.1)
      rw [hCb _ hb₀ hb₀1', hV] at h1
      by_contra h2
      push Not at h2
      have h3 : Nat.card U ^ 2 ≤ 7 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hEΓ : E ≤ φ.range := map_le_range φ SB
    have hEbot : E ≠ ⊥ := by
      intro h
      rw [← card_eq_one, hEcard, ← hUBcard] at h
      omega
    have hEab : IsElementaryAbelian 2 E := by
      refine SteinbergBM.isElementaryAbelian_two_of ?_ ?_
      · rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hAc _ hs.1 _ hs'.1)
      · rintro _ ⟨s, hs, rfl⟩
        rw [← map_mul, show s * s = 1 from Subtype.ext (hA2 _ hs.1), map_one]
    have hidx : ∀ F : Subgroup (Additive V ≃ₗ[ZMod 2] Additive V), F ≤ E →
        F.relIndex E = 2 → linFix F = linFix E := by
      intro F hFE hFidx
      have hF : F ≠ ⊥ := ne_bot_of_relIndex_eq_two hFE hFidx (by
        rw [hEcard, ← hUBcard]; omega)
      obtain ⟨⟨f, hf⟩, hf1⟩ := ne_bot_iff_exists_ne_one.mp hF
      have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
      obtain ⟨s, hs, hs1, rfl⟩ := hEelt f (hFE hf) hf1'
      exact le_antisymm ((linFix_le_ker hf).trans ((hkerU s hs hs1).trans hfixE.symm).le)
        (linFix_antitone hFE)
    obtain ⟨hE8, -, -, e, heE, he1, herank⟩ := hprofE E hEΓ hEbot hEab hidx
    obtain ⟨s, hs, hs1, rfl⟩ := hEelt e heE he1
    have h1 := two_pow_linRank_mul_card (hH := (le_rfl : N ≤ N)) s
    rw [herank, hCb _ hs hs1, hV, hUBcard, ← hEcard, hE8] at h1
    norm_num at h1
  refine ⟨main, fun T hTN => ⟨fun g hg => main g (Or.inr fun h => hg (le_bot_iff.1
    ((inf_le_inf_left _ hTN).trans h.le))), ?_⟩⟩
  refine iSup₂_le fun g hgT => le_inf hgT ?_
  have h1 : CFSG.conjugate V g ⊓ T ≠ ⊥ := by
    rw [inf_of_le_left hgT]
    intro h
    have h2 := card_conjugate V g
    rw [h, card_bot, hV] at h2
    norm_num at h2
  have h3 := main g (Or.inr fun h => h1 (le_bot_iff.1 ((inf_le_inf_left _ hTN).trans h.le)))
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at h3
  exact h3

end CFSG.Quasithin.H13.U3
