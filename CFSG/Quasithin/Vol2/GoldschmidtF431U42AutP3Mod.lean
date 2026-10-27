module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3Core

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45 L0S image_lineSet lineSet_eq_of_sameSet)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45)
open scoped Pointwise

@[expose] def fusW : List (List ℕ) :=
  [[], [], [], [1, 3, 2, 3, 2, 2], [1, 3, 2, 2], [1, 1, 3, 2], [], [], [],
    [2, 0, 1, 1, 0, 2, 0, 2], [], [], [], [], [2, 3, 2, 3, 2, 0, 2], [], [],
    [2, 3, 0, 1, 1, 0, 1], [2, 0, 1, 1, 0, 1, 1], [2, 0, 2, 0, 1, 1, 3, 2], [],
    [1, 3, 1, 0, 2, 0, 2], [], [], [1, 3, 2, 2], [2, 0, 1, 1, 3, 1, 3, 1],
    [2, 0, 2, 2, 3, 0, 1], [], [2, 3, 1, 0, 2, 3, 1], [1, 3, 1, 3, 1, 3, 1], [], [], [],
    [2, 0, 1, 0, 2], [2, 0, 2, 0, 1, 0, 1], [], [2, 3, 2, 3, 2, 3, 2], [], [], [],
    [1, 3, 0, 2], [], [], [], [], [], [], [], [], [], [1, 3, 2, 3, 2, 2], [], [],
    [1, 3, 2, 0, 1], [1, 3, 0, 2], [], [1, 3, 2, 2], [1, 1, 3, 2], [], [], [],
    [1, 0, 1, 1, 0, 2, 0, 1], [], []]

@[expose] def fusJ : List ℕ :=
  [0, 0, 0, 6, 58, 58, 6, 0, 0, 20, 0, 0, 0, 0, 20, 0, 0, 20, 20, 20, 20, 20, 0, 0, 20, 20, 20,
    0, 20, 20, 0, 0, 0, 20, 20, 0, 20, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 20, 58,
    0, 6, 6, 58, 0, 0, 6, 0, 0]

theorem Thl_nodup : Thl.Nodup := by decide +kernel

theorem fus_targets : ∀ j ∈ [6, 20, 58], 64 ≤ (Thl.filter fun l =>
    comp l (Tl.getD j []) == comp (Tl.getD j []) l).length := by
  decide +kernel

theorem fus_check : ∀ i < 64, (comp (Tl.getD i []) (Tl.getD i []) = idL ∧ Tl.getD i [] ≠ idL) →
    fusJ.getD i 0 ∈ [6, 20, 58] ∧
    comp (comp (evalAL (fusW.getD i [])) (Tl.getD i [])) (evalAL (invAL (fusW.getD i []))) =
      Tl.getD (fusJ.getD i 0) [] ∧
    ((evalAL (fusW.getD i [])).getD 0 0 = 0 ∨
      sameSet (imgSet (evalAL (fusW.getD i [])) L0) L0 = true) := by
  decide +kernel

theorem card_cent_ge {v : Ah} {vL : PL}
    (hv : RepL vL (v : P45))
    (h : 64 ≤ (Thl.filter fun l => comp l vL == comp vL l).length) :
    64 ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)) := by
  set F := Thl.filter fun l => comp l vL == comp vL l with hF
  have hnd : F.Nodup := Thl_nodup.filter _
  have key : ∀ l ∈ F, ∃ g : Ah, g ∈ That ⊓ Subgroup.centralizer ({v} : Set Ah) ∧
      RepL l (g : P45) := by
    intro l hl
    rw [hF, List.mem_filter] at hl
    obtain ⟨g, hg, hrep⟩ := exists_That_of_mem_Thl hl.1
    have hc : comp l vL = comp vL l := by simpa using hl.2
    refine ⟨g, Subgroup.mem_inf.2 ⟨hg, ?_⟩, hrep⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 := repL_mul hv hrep
    have h2 := repL_mul hrep hv
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (eq_of_repL (l := comp vL l) h1 (hc ▸ h2)).symm
  choose! gf hgf using key
  have hinj : Function.Injective fun i : Fin F.length =>
      (⟨gf (F.get i), (hgf _ (List.get_mem F i)).1⟩ :
        ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah))) := by
    intro i j hij
    have h1 : gf (F.get i) = gf (F.get j) := congrArg Subtype.val hij
    have h2 := hgf _ (List.get_mem F i)
    have h3 := hgf _ (List.get_mem F j)
    have : F.get i = F.get j := by
      apply repL_unique h2.2
      rw [h1]
      exact h3.2
    exact (hnd.get_inj_iff).1 this
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem fusion_model {u : Ah}
    (hu : u ∈ TAh) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g u' : Ah, (g ∈ P1h ∨ g ∈ P2h) ∧ u' ∈ TAh ∧ u' * u' = 1 ∧ g * u * g⁻¹ = u' ∧
      64 ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({u'} : Set Ah)) := by
  obtain ⟨y, hy, rfl⟩ := (mem_TAh_iff u).1 hu
  obtain ⟨i, hi, hrep⟩ := (U42.mem_T_iff y).1 hy
  have hsq : ((y : Y) : P45) * ((y : Y) : P45) = 1 :=
    congrArg (fun a : Ah => (a : P45)) hu2
  have hinv : comp (Tl.getD i []) (Tl.getD i []) = idL ∧ Tl.getD i [] ≠ idL := by
    refine ⟨repL_unique (repL_mul hrep hrep) (by rw [hsq]; exact repL_one 45), fun h => hu1 ?_⟩
    have h1 : ((y : Y) : P45) = 1 := eq_of_repL hrep (h ▸ repL_one 45)
    exact (congrArg (incl) (Subtype.ext h1 : y = 1)).trans (map_one incl)
  obtain ⟨hj, hconj, hP⟩ := fus_check i hi hinv
  have hcard := fus_targets _ hj
  have hj64 : fusJ.getD i 0 < 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  set w := fusW.getD i [] with hw
  obtain ⟨y₁, hy₁, hrep₁⟩ := U42.exists_Tel hj64
  have hg : RepL (evalAL w) ((wordAP w : P45)) := repL_wordAP w
  have hconjA : (⟨wordAP w, wordAP_mem w⟩ : Ah) * incl y * (⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹ =
      incl y₁ := by
    apply Subtype.ext
    have hinvrep : RepL (evalAL (invAL w)) ((wordAP w : P45)⁻¹) := by
      rw [← wordAP_invAL]
      exact repL_wordAP _
    have h1 : RepL (comp (comp (evalAL w) (Tl.getD i [])) (evalAL (invAL w)))
        ((wordAP w : P45) * (y : P45) * (wordAP w : P45)⁻¹) :=
      repL_mul (repL_mul hg hrep) hinvrep
    rw [hconj] at h1
    exact eq_of_repL h1 hrep₁
  refine ⟨⟨wordAP w, wordAP_mem w⟩, incl y₁, ?_, (mem_TAh_iff _).2 ⟨y₁, hy₁, rfl⟩, ?_, hconjA,
    card_cent_ge hrep₁ hcard⟩
  · rcases hP with h | h
    · left
      rw [mem_P1h_iff]
      apply Fin.ext
      rw [← hg.2 0]
      exact h
    · right
      rw [mem_P2h_iff]
      show (wordAP w) '' L0S = L0S
      rw [L0S, image_lineSet hg (by decide), lineSet_eq_of_sameSet h]
  · rw [← hconjA]
    calc (⟨wordAP w, wordAP_mem w⟩ : Ah) * incl y * (⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹ *
        ((⟨wordAP w, wordAP_mem w⟩ : Ah) * incl y * (⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹)
        = (⟨wordAP w, wordAP_mem w⟩ : Ah) * (incl y * incl y) *
          (⟨wordAP w, wordAP_mem w⟩ : Ah)⁻¹ := by group
      _ = 1 := by rw [hu2]; group

end CFSG.Quasithin.H13.F431.U42Aut
