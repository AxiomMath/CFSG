module

public import CFSG.RankThree.GF2n.Tim81.Sec5.TwoPoint
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbEpsilon
import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

namespace Hyp

theorem conjSubgroup_Pc_eq_of_conjSubgroup_eq (h : Hyp M V) {a b : G}
    (hab : conjSubgroup a V = conjSubgroup b V) :
    conjSubgroup a (Pc M V) = conjSubgroup b (Pc M V) := by
  have hb : b⁻¹ * a ∈ M := by
    rw [← h.normalizer_eq, mem_normalizer_iff_conjSubgroup_eq]
    calc conjSubgroup (b⁻¹ * a) V = conjSubgroup b⁻¹ (conjSubgroup a V) :=
          (CGT.Timmesfeld75.conjSubgroup_conjSubgroup b⁻¹ a V).symm
      _ = conjSubgroup b⁻¹ (conjSubgroup b V) := by rw [hab]
      _ = V := by
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  calc conjSubgroup a (Pc M V) = conjSubgroup b (conjSubgroup (b⁻¹ * a) (Pc M V)) := by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup b (Pc M V) := by
        rw [conjSubgroup_eq_self_iff.mpr (h.le_normalizer_Pc hb)]

theorem hOf_eq_of_conjSubgroup_eq_conj (h : Hyp M V) {g g' p : G} (hp : p ∈ Pc M V)
    (he : conjSubgroup g V = conjSubgroup p (conjSubgroup g' V)) :
    hOf M V g = hOf M V g' := by
  have hPp : conjSubgroup p (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.le_normalizer_Pc (h.Pc_le_M hp))
  have he' : conjSubgroup g V = conjSubgroup (p * g') V := by
    rw [he, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
  have hP : conjSubgroup g (Pc M V) = conjSubgroup p (conjSubgroup g' (Pc M V)) := by
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact h.conjSubgroup_Pc_eq_of_conjSubgroup_eq he'
  calc hOf M V g = Pc M V ⊔ conjSubgroup p (conjSubgroup g' (Pc M V)) := by
        rw [hOf, hP]
    _ = conjSubgroup p (Pc M V ⊔ conjSubgroup g' (Pc M V)) := by
        rw [CGT.Timmesfeld75.conjSubgroup_sup, hPp]
    _ = hOf M V g' := by
        have hp' : p ∈ hOf M V g' := Subgroup.mem_sup_left hp
        rw [conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hp')]

end Hyp

namespace Sec45Shape

theorem exists_map_imgK_eq_conj_utri (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) {x : G}
    (hx : x ∈ H) : ∃ s : SL(2, F),
      (imgK V H (conjSubgroup x (Pc M V))).map ψ.toMonoidHom = conjSubgroup s (utri F) := by
  obtain ⟨-, -, a, -, hAeq, -, -⟩ :=
    h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  refine ⟨ψ (piK V H ⟨x, hx⟩) * a, ?_⟩
  rw [imgK_conjSubgroup hx hS.Pc_le, map_conjSubgroup_mulEquiv, hAeq,
    CGT.Timmesfeld75.conjSubgroup_conjSubgroup]

theorem map_imgK_conj_sylow (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) {x : G}
    (hx : x ∈ H) :
    (∀ a ∈ (imgK V H (conjSubgroup x (Pc M V))).map ψ.toMonoidHom, a * a = 1) ∧
      Nat.card ((imgK V H (conjSubgroup x (Pc M V))).map ψ.toMonoidHom) = Fintype.card F := by
  obtain ⟨hA2, hAcard, -⟩ := h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  rw [imgK_conjSubgroup hx hS.Pc_le, map_conjSubgroup_mulEquiv]
  constructor
  · intro a ha
    let g : SL(2, F) := ψ (piK V H ⟨x, hx⟩)
    have ha' : g⁻¹ * a * g ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom := mem_conjSubgroup.mp ha
    have h := hA2 _ ha'
    have haeq : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [haeq, show g * (g⁻¹ * a * g) * g⁻¹ * (g * (g⁻¹ * a * g) * g⁻¹) =
      g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ by group, h]
    group
  · rw [card_conjSubgroup, hAcard]

theorem imgK_conj_eq_iff (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {x x' : G}
    (hx : x ∈ H) (hx' : x' ∈ H) :
    imgK V H (conjSubgroup x (Pc M V)) = imgK V H (conjSubgroup x' (Pc M V)) ↔
      conjSubgroup x V = conjSubgroup x' V := by
  constructor
  · intro heq
    have hP := RootHyp.conjSubgroup_eq_of_imgK_conjSubgroup_eq h hS.Pc_le
      hx hx' heq
    calc conjSubgroup x V = Subgroup.centralizer (conjSubgroup x (Pc M V) : Set G) := by
          rw [h.toHyp.centralizer_conj_Pc]
      _ = Subgroup.centralizer (conjSubgroup x' (Pc M V) : Set G) := by rw [hP]
      _ = conjSubgroup x' V := by rw [h.toHyp.centralizer_conj_Pc]
  · intro hV
    rw [h.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hV]

theorem conj_eq_of_imgK_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {b x : G}
    (hbH : conjSubgroup b H = H) (hx : x ∈ H)
    (heq : imgK V H (conjSubgroup b (conjSubgroup x (Pc M V))) =
      imgK V H (conjSubgroup x (Pc M V))) :
    conjSubgroup b (conjSubgroup x V) = conjSubgroup x V := by
  have hxPH : conjSubgroup x (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hx
  have hbxPH : conjSubgroup (b * x) (Pc M V) ≤ H := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, ← hbH]
    exact conjSubgroup_mono (g := b) hxPH
  have heq' : imgK V H (conjSubgroup (b * x) (Pc M V)) =
      imgK V H (conjSubgroup x (Pc M V)) := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact heq
  obtain ⟨z, hzH, hPz, hVz⟩ := h.toHyp.exists_mem_conj_eq_of_conj_Pc_le hS.Pc_le hbxPH
  have himg : imgK V H (conjSubgroup z (Pc M V)) = imgK V H (conjSubgroup x (Pc M V)) := by
    rw [← hPz]
    exact heq'
  have hVzx : conjSubgroup z V = conjSubgroup x V :=
    (hS.imgK_conj_eq_iff h hzH hx).mp himg
  calc conjSubgroup b (conjSubgroup x V) = conjSubgroup (b * x) V :=
        CGT.Timmesfeld75.conjSubgroup_conjSubgroup b x V
    _ = conjSubgroup z V := hVz
    _ = conjSubgroup x V := hVzx

theorem exists_mem_eq_map_imgK (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {A : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1) (hAc : Nat.card A = Fintype.card F) :
    ∃ x ∈ H, A = (imgK V H (conjSubgroup x (Pc M V))).map ψ.toMonoidHom := by
  obtain ⟨-, -, a, -, hAeq, -, -⟩ :=
    h.imgK_map_sl2 hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  obtain ⟨s, hs⟩ := Sec2.exists_conj_utri_of_exp_two A hA2 hAc
  obtain ⟨t, ht⟩ : ∃ t : HBar V H, ψ t = s * a⁻¹ := ψ.surjective (s * a⁻¹)
  obtain ⟨z, hz⟩ := piK_surjective V H t
  have hmain : (imgK V H (conjSubgroup (z : G) (Pc M V))).map ψ.toMonoidHom =
      conjSubgroup (ψ (piK V H z) * a) (utri F) := by
    rw [imgK_conjSubgroup z.2 hS.Pc_le, map_conjSubgroup_mulEquiv, hAeq,
      CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
  refine ⟨z, z.2, ?_⟩
  rw [hs, hmain, hz, ht]
  congr 1
  group


theorem isHMember_sup_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    IsHMember M V (Pc M V ⊔ conjSubgroup y (Pc M V)) := by
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hy
  have hLH : Pc M V ⊔ conjSubgroup y (Pc M V) ≤ H := sup_le hS.Pc_le hPyH
  refine ⟨?_, le_sup_left, ?_⟩
  · set L : Subgroup G := Pc M V ⊔ conjSubgroup y (Pc M V)
    set B : Subgroup G := Tim79a.xOf V H ⊓ L
    have hBL : B ≤ L := inf_le_right
    have hLNB : L ≤ Subgroup.normalizer (B : Set G) := by
      intro l hl
      exact mem_normalizer_inf (Tim79a.H_le_normalizer_xOf V H (hLH hl))
        (Subgroup.le_normalizer hl)
    have hB2 : IsPGroup 2 B := (hS.isElemAbelian h).isPGroup.to_le inf_le_left
    have hBle : B ≤ inSubgroup (pCore 2) L := Tim78.le_inSubgroup_pCore hBL hLNB hB2
    have hVB : V ≤ B :=
      le_inf (le_xOf_self V H) (le_trans h.toHyp.le_Pc le_sup_left)
    have hBne : B ≠ ⊥ := by
      intro hbot
      exact h.toHyp.ne_bot (le_bot_iff.mp (hVB.trans (le_of_eq hbot)))
    intro hbot
    exact hBne (le_bot_iff.mp (hBle.trans (le_of_eq hbot)))
  · intro hLM
    have hnorm : imgK V H (conjSubgroup y (Pc M V)) ≤
        Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
      intro z hz
      obtain ⟨x, hxPy, hxeq⟩ := (mem_imgK_iff).mp hz
      rw [← hxeq, mem_normalizer_iff_conjSubgroup_eq]
      have hxH : (x : G) ∈ H := hLH (Subgroup.mem_sup_right hxPy)
      have hxM : (x : G) ∈ M := hLM (Subgroup.mem_sup_right hxPy)
      have hconjP : conjSubgroup (x : G) (Pc M V) = Pc M V :=
        conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hxM)
      rw [← imgK_conjSubgroup hxH hS.Pc_le, hconjP]
    exact hS.imgK_conj_ne h hy hyV
      (h.weaklyClosed_imgK hS.Pc_le hy hnorm)

theorem conjSubgroup_mem_sigmaSet (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G} (hy : y ∈ H)
    (hyV : conjSubgroup y V ≠ V) : conjSubgroup y V ∈ sigmaSet M V :=
  ⟨y, rfl, hS.isHMember_sup_conj h hy hyV⟩

end Sec45Shape

namespace Sec45Shape

private theorem hBarConj_congr {V H : Subgroup G} {b b' : G} (hbb' : b = b')
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G))
    (hb'H : b' ∈ Subgroup.normalizer (H : Set G))
    (hb'K : b' ∈ Subgroup.normalizer (kOf V H : Set G)) :
    hBarConj hbH hbK = hBarConj hb'H hb'K := by
  subst hbb'
  refine MulEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := piK_surjective V H y
  calc hBarConj hbH hbK (piK V H z)
      = piK V H ⟨b * (z : G) * b⁻¹,
          (Subgroup.mem_normalizer_iff.mp hbH (z : G)).mp z.2⟩ := hBarConj_piK hbH hbK z
    _ = piK V H ⟨b * (z : G) * b⁻¹,
          (Subgroup.mem_normalizer_iff.mp hb'H (z : G)).mp z.2⟩ :=
        congrArg (piK V H) (Subtype.ext rfl)
    _ = hBarConj hb'H hb'K (piK V H z) := (hBarConj_piK hb'H hb'K z).symm

private theorem hBarConj_eq_one_of_eq_one {V H : Subgroup G} {b : G}
    (hbH : b ∈ Subgroup.normalizer (H : Set G))
    (hbK : b ∈ Subgroup.normalizer (kOf V H : Set G)) (hb : b = 1) :
    hBarConj hbH hbK = 1 :=
  (hBarConj_congr hb hbH hbK (Subgroup.one_mem _) (Subgroup.one_mem _)).trans hBarConj_one

private theorem mem_normalizer_of_fix_conj {V H : Subgroup G} {A : Subgroup G} {x₁ : G}
    (hA2 : ∀ a ∈ A, a * a = 1) (hAH : ∀ a ∈ A, conjSubgroup a H = H) (hx₁ : x₁ ∈ H)
    (hA₁ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₁ V) = conjSubgroup x₁ V)
    {a : G} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) ∧
      a ∈ Subgroup.normalizer (kOf V H : Set G) := by
  have haH : conjSubgroup a H = H := hAH a ha
  have hy : a * x₁⁻¹ * a * x₁ ∈ H := by
    have h1 : a * x₁⁻¹ * a⁻¹ ∈ H := by
      rw [← haH]
      refine mem_conjSubgroup.mpr ?_
      show a⁻¹ * (a * x₁⁻¹ * a⁻¹) * a ∈ H
      rw [show a⁻¹ * (a * x₁⁻¹ * a⁻¹) * a = x₁⁻¹ by group]
      exact H.inv_mem hx₁
    rw [show a * x₁⁻¹ * a * x₁ = (a * x₁⁻¹ * a⁻¹) * (a * a) * x₁ by group,
      hA2 a ha, mul_one]
    exact H.mul_mem h1 hx₁
  have hVy : conjSubgroup a V = conjSubgroup (a * x₁⁻¹ * a * x₁) V := by
    have h1 : conjSubgroup (a * x₁) V = conjSubgroup x₁ V := by
      rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact hA₁ a ha
    calc conjSubgroup a V = conjSubgroup (a * x₁⁻¹) (conjSubgroup x₁ V) := by
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
          congr 1
          group
      _ = conjSubgroup (a * x₁⁻¹) (conjSubgroup (a * x₁) V) := by rw [← h1]
      _ = conjSubgroup (a * x₁⁻¹ * (a * x₁)) V := by
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      _ = conjSubgroup (a * x₁⁻¹ * a * x₁) V := by
          congr 1
          group
  exact ⟨mem_normalizer_iff_conjSubgroup_eq.mpr
      (conjSubgroup_xOf_eq_of_conj_eq haH hy hVy),
    mem_normalizer_kOf_of_conj_eq haH hy hVy⟩

private noncomputable def hBarConjAut {V H : Subgroup G} {A : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hNH : ∀ a ∈ A, a ∈ Subgroup.normalizer (H : Set G))
    (hNK : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf V H : Set G)) :
    (a : G) → a ∈ A → MulAut (SL(2, F)) :=
  fun a ha => MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha))

private theorem hBarConjAut_fixes_sylow {M V H : Subgroup G} {A : Subgroup G} {x₁ x₂ : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (h : Hyp M V) (hPc : Pc M V ≤ H)
    (hNH : ∀ a ∈ A, a ∈ Subgroup.normalizer (H : Set G))
    (hNK : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf V H : Set G))
    (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H)
    (hA₁ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₁ V) = conjSubgroup x₁ V)
    (hA₂ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₂ V) = conjSubgroup x₂ V)
    (a : G) (ha : a ∈ A) :
    (((imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom).map
        (hBarConjAut ψ hNH hNK a ha).toMonoidHom =
      (imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom) ∧
    (((imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom).map
        (hBarConjAut ψ hNH hNK a ha).toMonoidHom =
      (imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom) := by
  have hbar : hBarConjAut ψ hNH hNK a ha =
      MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) := rfl
  constructor
  · have hP : conjSubgroup a (conjSubgroup x₁ (Pc M V)) = conjSubgroup x₁ (Pc M V) := by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact h.conjSubgroup_Pc_eq_of_conjSubgroup_eq
        (by rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]; exact hA₁ a ha)
    calc ((imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom).map
          (hBarConjAut ψ hNH hNK a ha).toMonoidHom
        = (((imgK V H (conjSubgroup x₁ (Pc M V))).map (hBarConj
            (hNH a ha) (hNK a ha)).toMonoidHom).map ψ.toMonoidHom) := by
          rw [hbar, CFSG.map_mulAut_congr]
      _ = (imgK V H (conjSubgroup a (conjSubgroup x₁ (Pc M V)))).map ψ.toMonoidHom := by
          rw [hBarConj_map_imgK (hNH a ha) (hNK a ha)
            (conjSubgroup_le_of_le_of_mem hPc hx₁)]
      _ = (imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom := by rw [hP]
  · have hP : conjSubgroup a (conjSubgroup x₂ (Pc M V)) = conjSubgroup x₂ (Pc M V) := by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact h.conjSubgroup_Pc_eq_of_conjSubgroup_eq
        (by rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]; exact hA₂ a ha)
    calc ((imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom).map
          (hBarConjAut ψ hNH hNK a ha).toMonoidHom
        = (((imgK V H (conjSubgroup x₂ (Pc M V))).map (hBarConj
            (hNH a ha) (hNK a ha)).toMonoidHom).map ψ.toMonoidHom) := by
          rw [hbar, CFSG.map_mulAut_congr]
      _ = (imgK V H (conjSubgroup a (conjSubgroup x₂ (Pc M V)))).map ψ.toMonoidHom := by
          rw [hBarConj_map_imgK (hNH a ha) (hNK a ha)
            (conjSubgroup_le_of_le_of_mem hPc hx₂)]
      _ = (imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom := by rw [hP]

private theorem hBarConjAut_mul_self {V H : Subgroup G} {A : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hNH : ∀ a ∈ A, a ∈ Subgroup.normalizer (H : Set G))
    (hNK : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf V H : Set G))
    (hA2 : ∀ a ∈ A, a * a = 1) :
    ∀ (a : G) (ha : a ∈ A),
      hBarConjAut ψ hNH hNK a ha * hBarConjAut ψ hNH hNK a ha = 1 := by
  intro a ha
  have hbar : hBarConj (hNH a ha) (hNK a ha) * hBarConj (hNH a ha) (hNK a ha) = 1 := by
    rw [← hBarConj_mul (hNH a ha) (hNK a ha) (hNH a ha) (hNK a ha)]
    exact hBarConj_eq_one_of_eq_one _ _ (hA2 a ha)
  calc hBarConjAut ψ hNH hNK a ha * hBarConjAut ψ hNH hNK a ha
      = MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha) *
          hBarConj (hNH a ha) (hNK a ha)) := by
        rw [show hBarConjAut ψ hNH hNK a ha =
            MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) from rfl, ← map_mul]
    _ = 1 := by rw [hbar, map_one]

private theorem hBarConjAut_comm {V H : Subgroup G} {A : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hNH : ∀ a ∈ A, a ∈ Subgroup.normalizer (H : Set G))
    (hNK : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf V H : Set G))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      hBarConjAut ψ hNH hNK a ha * hBarConjAut ψ hNH hNK b hb =
        hBarConjAut ψ hNH hNK b hb * hBarConjAut ψ hNH hNK a ha := by
  intro a ha b hb
  have hbar : hBarConj (hNH a ha) (hNK a ha) * hBarConj (hNH b hb) (hNK b hb) =
      hBarConj (hNH b hb) (hNK b hb) * hBarConj (hNH a ha) (hNK a ha) := by
    rw [← hBarConj_mul (hNH a ha) (hNK a ha) (hNH b hb) (hNK b hb),
      ← hBarConj_mul (hNH b hb) (hNK b hb) (hNH a ha) (hNK a ha)]
    exact hBarConj_congr (hAc a ha b hb) _ _ _ _
  calc hBarConjAut ψ hNH hNK a ha * hBarConjAut ψ hNH hNK b hb
      = MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha) *
          hBarConj (hNH b hb) (hNK b hb)) := by
        rw [show hBarConjAut ψ hNH hNK a ha =
            MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) from rfl,
          show hBarConjAut ψ hNH hNK b hb =
            MulAut.congr ψ (hBarConj (hNH b hb) (hNK b hb)) from rfl, ← map_mul]
    _ = MulAut.congr ψ (hBarConj (hNH b hb) (hNK b hb) *
          hBarConj (hNH a ha) (hNK a ha)) := by rw [hbar]
    _ = hBarConjAut ψ hNH hNK b hb * hBarConjAut ψ hNH hNK a ha := by
        rw [show hBarConjAut ψ hNH hNK b hb =
            MulAut.congr ψ (hBarConj (hNH b hb) (hNK b hb)) from rfl,
          show hBarConjAut ψ hNH hNK a ha =
            MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) from rfl, map_mul]

private theorem hBarConjAut_mul {V H : Subgroup G} {A : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hNH : ∀ a ∈ A, a ∈ Subgroup.normalizer (H : Set G))
    (hNK : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf V H : Set G)) :
    ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      hBarConjAut ψ hNH hNK (a * b) (Subgroup.mul_mem A ha hb) =
        hBarConjAut ψ hNH hNK a ha * hBarConjAut ψ hNH hNK b hb := by
  intro a ha b hb
  rw [show hBarConjAut ψ hNH hNK (a * b) (Subgroup.mul_mem A ha hb) =
      MulAut.congr ψ (hBarConj (hNH (a * b) (Subgroup.mul_mem A ha hb))
        (hNK (a * b) (Subgroup.mul_mem A ha hb))) from rfl,
    show hBarConjAut ψ hNH hNK a ha =
      MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) from rfl,
    show hBarConjAut ψ hNH hNK b hb =
      MulAut.congr ψ (hBarConj (hNH b hb) (hNK b hb)) from rfl,
    ← map_mul, ← hBarConj_mul (hNH a ha) (hNK a ha) (hNH b hb) (hNK b hb)]

private theorem sylow_pair_properties (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {x₁ x₂ : G} (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H)
    (hne : conjSubgroup x₁ V ≠ conjSubgroup x₂ V) :
    (∀ a ∈ (imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom, a * a = 1) ∧
      Nat.card ((imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom) =
        Fintype.card F ∧
      (∀ a ∈ (imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom, a * a = 1) ∧
      Nat.card ((imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom) =
        Fintype.card F ∧
      (imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom ≠
        (imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom := by
  refine ⟨(hS.map_imgK_conj_sylow h ψ hx₁).1, (hS.map_imgK_conj_sylow h ψ hx₁).2,
    (hS.map_imgK_conj_sylow h ψ hx₂).1, (hS.map_imgK_conj_sylow h ψ hx₂).2, ?_⟩
  intro heq
  exact hne ((hS.imgK_conj_eq_iff h hx₁ hx₂).mp
    (Subgroup.map_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective (by simpa using heq)))

private theorem exists_two_ne_one {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : 2 < Nat.card A) :
    ∃ a₁ : ↥A, ∃ a₂ : ↥A, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₁ ≠ a₂ := by
  classical
  letI : Fintype ↥A := Fintype.ofFinite ↥A
  have hcardA : 2 < Fintype.card ↥A := by
    rw [← Nat.card_eq_fintype_card]
    exact hA
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcardA
  by_cases ha1 : a = 1
  · exact ⟨b, c, fun h => hab (ha1.trans h.symm), fun h => hac (ha1.trans h.symm), hbc⟩
  · by_cases hb1 : b = 1
    · exact ⟨a, c, ha1, fun h => hbc (hb1.trans h.symm), hac⟩
    · exact ⟨a, b, ha1, hb1, hab⟩

private theorem exists_theta_eq_one {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] {A₁ A₂ : Subgroup SL(2, F)}
    (θ : (a : G) → a ∈ A → MulAut (SL(2, F)))
    (hA2 : ∀ a ∈ A, a * a = 1)
    (hA₁2 : ∀ a ∈ A₁, a * a = 1) (hA₁c : Nat.card A₁ = Fintype.card F)
    (hA₂2 : ∀ a ∈ A₂, a * a = 1) (hA₂c : Nat.card A₂ = Fintype.card F)
    (hne : A₁ ≠ A₂)
    (hfixA₁ : ∀ (a : G) (ha : a ∈ A), A₁.map (θ a ha).toMonoidHom = A₁)
    (hfixA₂ : ∀ (a : G) (ha : a ∈ A), A₂.map (θ a ha).toMonoidHom = A₂)
    (hθ2 : ∀ (a : G) (ha : a ∈ A), θ a ha * θ a ha = 1)
    (hθc : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      θ a ha * θ b hb = θ b hb * θ a ha)
    (hθmul : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      θ (a * b) (Subgroup.mul_mem A ha hb) = θ a ha * θ b hb)
    (hA : 2 < Nat.card A) :
    ∃ (a : G) (ha : a ∈ A), a ≠ 1 ∧ θ a ha = 1 := by
  classical
  obtain ⟨a₁, a₂, ha₁1, ha₂1, ha₁₂⟩ := exists_two_ne_one hA
  have hcase := Sec2.MulAut.eq_one_or_eq_of_two_sylow (θ₁ := θ a₁ a₁.2)
    (θ₂ := θ a₂ a₂.2) hA₁2 hA₁c hA₂2 hA₂c hne
    (hfixA₁ a₁ a₁.2) (hfixA₂ a₁ a₁.2) (hfixA₁ a₂ a₂.2) (hfixA₂ a₂ a₂.2)
    (hθ2 a₁ a₁.2) (hθ2 a₂ a₂.2) (hθc a₁ a₁.2 a₂ a₂.2)
  rcases hcase with h1 | h2 | h12
  · exact ⟨↑a₁, a₁.2, fun h => ha₁1 (Subtype.ext h), h1⟩
  · exact ⟨↑a₂, a₂.2, fun h => ha₂1 (Subtype.ext h), h2⟩
  · have hθmul' : θ (↑(a₁ * a₂)) (a₁ * a₂).2 = θ a₁ a₁.2 * θ a₂ a₂.2 := by
      simpa using hθmul a₁ a₁.2 a₂ a₂.2
    refine ⟨(↑(a₁ * a₂) : G), (a₁ * a₂).2, ?_, ?_⟩
    · intro h
      apply ha₁₂
      apply Subtype.ext
      have h2 : (a₂ : G) * (a₂ : G) = 1 := hA2 a₂ a₂.2
      have hh : (a₁ : G) * (a₂ : G) = 1 := h
      calc (a₁ : G) = (a₁ : G) * ((a₂ : G) * (a₂ : G)) := by rw [h2, mul_one]
        _ = ((a₁ : G) * (a₂ : G)) * (a₂ : G) := by group
        _ = 1 * (a₂ : G) := by rw [hh]
        _ = (a₂ : G) := one_mul _
    · rw [hθmul', h12, hθ2 a₂ a₂.2]

private theorem exists_hBarConj_eq_one (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA : 2 < Nat.card A) (hAH : ∀ a ∈ A, conjSubgroup a H = H) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H) (hne : conjSubgroup x₁ V ≠ conjSubgroup x₂ V)
    (hA₁ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₁ V) = conjSubgroup x₁ V)
    (hA₂ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₂ V) = conjSubgroup x₂ V) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ H, ⁅a, x⁆ ∈ kOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hNK : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf V H : Set G) := fun a ha =>
    (mem_normalizer_of_fix_conj hA2 hAH hx₁ hA₁ ha).2
  have hNH : ∀ a ∈ A, a ∈ Subgroup.normalizer (H : Set G) :=
    fun a ha => mem_normalizer_iff_conjSubgroup_eq.mpr (hAH a ha)
  let A₁ : Subgroup SL(2, F) := (imgK V H (conjSubgroup x₁ (Pc M V))).map ψ.toMonoidHom
  let A₂ : Subgroup SL(2, F) := (imgK V H (conjSubgroup x₂ (Pc M V))).map ψ.toMonoidHom
  have hpair := sylow_pair_properties h hS ψ hx₁ hx₂ hne
  have hA₁2 : ∀ a ∈ A₁, a * a = 1 := hpair.1
  have hA₁c : Nat.card A₁ = Fintype.card F := hpair.2.1
  have hA₂2 : ∀ a ∈ A₂, a * a = 1 := hpair.2.2.1
  have hA₂c : Nat.card A₂ = Fintype.card F := hpair.2.2.2.1
  have hne' : A₁ ≠ A₂ := hpair.2.2.2.2
  let θ : (a : G) → a ∈ A → MulAut (SL(2, F)) := hBarConjAut ψ hNH hNK
  have hfixA₁ : ∀ (a : G) (ha : a ∈ A), A₁.map (θ a ha).toMonoidHom = A₁ := fun a ha =>
    (hBarConjAut_fixes_sylow ψ h.toHyp hS.Pc_le hNH hNK hx₁ hx₂ hA₁ hA₂ a ha).1
  have hfixA₂ : ∀ (a : G) (ha : a ∈ A), A₂.map (θ a ha).toMonoidHom = A₂ := fun a ha =>
    (hBarConjAut_fixes_sylow ψ h.toHyp hS.Pc_le hNH hNK hx₁ hx₂ hA₁ hA₂ a ha).2
  have hθ2 : ∀ (a : G) (ha : a ∈ A), θ a ha * θ a ha = 1 :=
    hBarConjAut_mul_self ψ hNH hNK hA2
  have hθc : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      θ a ha * θ b hb = θ b hb * θ a ha := hBarConjAut_comm ψ hNH hNK hAc
  have hθmul : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      θ (a * b) (Subgroup.mul_mem A ha hb) = θ a ha * θ b hb := hBarConjAut_mul ψ hNH hNK
  obtain ⟨a, ha, ha1, hθ1⟩ := exists_theta_eq_one θ hA2 hA₁2 hA₁c hA₂2 hA₂c hne'
    hfixA₁ hfixA₂ hθ2 hθc hθmul hA
  refine ⟨a, ha, ha1, ?_⟩
  have hbar1 : hBarConj (hNH a ha) (hNK a ha) = 1 := by
    have h1 : MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) = 1 := by
      rw [show MulAut.congr ψ (hBarConj (hNH a ha) (hNK a ha)) = θ a ha from rfl, hθ1]
    exact (MulAut.congr ψ).injective (by rw [h1, map_one])
  exact (hBarConj_eq_one_iff (hNH a ha) (hNK a ha)).mp hbar1

theorem exists_ne_one_mem_centralizer_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA : 2 < Nat.card A) (hAH : ∀ a ∈ A, conjSubgroup a H = H) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H) (hne : conjSubgroup x₁ V ≠ conjSubgroup x₂ V)
    (hA₁ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₁ V) = conjSubgroup x₁ V)
    (hA₂ : ∀ a ∈ A, conjSubgroup a (conjSubgroup x₂ V) = conjSubgroup x₂ V) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  obtain ⟨a, ha, ha1, hbK⟩ :=
    exists_hBarConj_eq_one h hS hA2 hAc hA hAH hx₁ hx₂ hne hA₁ hA₂
  exact ⟨a, ha, ha1, mem_centralizer_xOf_of_commutator_mem_kOf h hS hbK (k := 1)
    (by simpa [pow_two] using hA2 a ha)⟩

end Sec45Shape

namespace Sec5Hyp

private theorem mem_centralizer_conj_of_commutator_eq_bot {c : G} {U : Subgroup G}
    (hUU' : ⁅U, conjSubgroup c V⁆ = ⊥) {u : G} (huU : u ∈ U) :
    u ∈ Subgroup.centralizer (conjSubgroup c V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hmem : ⁅u, v⁆ ∈ ⁅U, conjSubgroup c V⁆ :=
    Subgroup.commutator_mem_commutator huU hv
  rw [hUU'] at hmem
  have h1 : ⁅u, v⁆ = 1 := Subgroup.mem_bot.mp hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem mem_normalizer_conj_Pc_of_centralizer (h : RootHyp M V) {c u : G}
    (huCc : u ∈ Subgroup.centralizer (conjSubgroup c V : Set G)) :
    u ∈ Subgroup.normalizer (conjSubgroup c (Pc M V) : Set G) := by
  have huVc : conjSubgroup u (conjSubgroup c V) = conjSubgroup c V :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ huCc)
  have hcuc : conjSubgroup (c⁻¹ * u * c) V = V := by
    calc conjSubgroup (c⁻¹ * u * c) V
        = conjSubgroup c⁻¹ (conjSubgroup u (conjSubgroup c V)) := by
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
            CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      _ = conjSubgroup c⁻¹ (conjSubgroup c V) := by rw [huVc]
      _ = V := by
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hcucM : c⁻¹ * u * c ∈ M :=
    h.toHyp.normalizer_eq ▸ mem_normalizer_iff_conjSubgroup_eq.mpr hcuc
  have hPu : conjSubgroup u (conjSubgroup c (Pc M V)) = conjSubgroup c (Pc M V) := by
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show u * c = c * (c⁻¹ * u * c) by group,
      ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hcucM)]
  exact conjSubgroup_eq_self_iff.mp hPu

private theorem commutator_mem_kOf_of_mem_sigmaSet (h : RootHyp M V) {c : G}
    (hSc : Sec45Shape M V (hOf M V c) c) {y : G} (hyH : y ∈ hOf M V c)
    (hyV : conjSubgroup y V ≠ V) (hVy : conjSubgroup c V = conjSubgroup y V)
    {U : Subgroup G}
    (hle : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G))
    {u : G} (huU : u ∈ U) :
    ∀ p ∈ Pc M V, ⁅u, p⁆ ∈ kOf V (hOf M V c) := by
  have hCV : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) =
      Pc M V ⊓ kOf V (hOf M V c) := by
    rw [show conjSubgroup c V = conjSubgroup y V from hVy,
      hSc.Pc_inf_centralizer_conj h hyH hyV]
  intro p hp
  have hmem : ⁅u, p⁆ ∈ ⁅U, Pc M V⁆ := Subgroup.commutator_mem_commutator huU hp
  have hmem' : ⁅u, p⁆ ∈ ⁅Pc M V, U⁆ := by
    rwa [Subgroup.commutator_comm]
  exact (hCV ▸ hle hmem').2

private theorem exists_pow_two_pow_eq_one_of_mem_sigmaSet (h : RootHyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {u : G} (huU : u ∈ U) : ∃ k : ℕ, u ^ 2 ^ k = 1 := by
  obtain ⟨g, hUeq, -⟩ := hU
  have hU2 : IsPGroup 2 U := by
    rw [hUeq]
    exact h.toHyp.isPGroup_V.map (MulAut.conj g).toMonoidHom
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU2 ⟨u, huU⟩
  refine ⟨k, ?_⟩
  have hpow := pow_orderOf_eq_one (⟨u, huU⟩ : U)
  rw [hk] at hpow
  simpa using congrArg Subtype.val hpow

theorem forall_commutator_mem_kOf_of_le (hS : Sec5Hyp M V) {c : G}
    (hU' : conjSubgroup c V ∈ sigmaSet M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V)
    (hUU' : ⁅U, conjSubgroup c V⁆ = ⊥)
    (hle : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)) :
    ∀ u ∈ U, (∀ z ∈ hOf M V c, ⁅u, z⁆ ∈ kOf V (hOf M V c)) ∧
      u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V c) : Set G) := by
  have h := hS.toRootHyp
  have hSc : Sec45Shape M V (hOf M V c) c := hS.shape hU'
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSc.Pc_le hSc.hH
  have hyV : conjSubgroup y V ≠ V := by
    intro hc
    exact ne_of_mem_sigmaSet h hU' (hVy.trans hc)
  intro u huU
  have huM : u ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 huU
  have huCc := mem_centralizer_conj_of_commutator_eq_bot hUU' huU
  have huP := commutator_mem_kOf_of_mem_sigmaSet h hSc hyH hyV hVy hle huU
  have huPc := mem_normalizer_conj_Pc_of_centralizer h huCc
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem_sigmaSet h hU huU
  exact ⟨Sec45Shape.commutator_mem_kOf_of_fix_Pc h hSc huM huP huPc,
    Sec45Shape.mem_centralizer_xOf_of_fix_Pc h hSc huM huP huPc hk⟩

end Sec5Hyp

namespace Sec45Shape

theorem exists_commutator_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {e v : G}
    (he : e ∈ Pc M V) (heK : e ∉ kOf V H) (hv : v ∈ V) :
    ∃ w ∈ Pc M V ⊓ Tim79a.xOf V H, ⁅e, w⁆ = v := by
  classical
  let A : Subgroup G := Pc M V ⊓ Tim79a.xOf V H
  have hZA : V ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (by rwa [← h.toHyp.centralizer_Pc] at hx) a
      (Subgroup.mem_inf.mp ha).1
  have hxA : ∀ a ∈ A, ⁅e, a⁆ ∈ V := by
    intro a ha
    have hmem : ⁅e, a⁆ ∈ ⁅Pc M V, Pc M V⁆ :=
      Subgroup.commutator_mem_commutator he (Subgroup.mem_inf.mp ha).1
    rwa [hS.commutator_Pc h] at hmem
  let φ : ↥A →* ↥V := commutatorElementHom e hZA hxA
  have hker : φ.ker = (A ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf A :=
    ker_commutatorElementHom e hZA hxA
  have hAinf : A ⊓ Subgroup.centralizer ({e} : Set G) =
      Tim79a.xOf V H ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2,
        (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      have hxP : (x : G) ∈ Pc M V := (hS.xOf_inf_centralizer_le_and_card h he heK).1 hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxP, hx.1⟩, hx.2⟩
  have hkercard : Nat.card ↥φ.ker = Nat.card V ^ 2 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ _ ≤ A)).toEquiv]
    rw [hAinf]
    exact (hS.xOf_inf_centralizer_le_and_card h he heK).2
  have hrangecard : Nat.card ↥φ.range = Nat.card V := by
    have hkr := Subgroup.card_ker_mul_card_range φ
    rw [hkercard] at hkr
    have hAcard : Nat.card A = Nat.card V ^ 3 := hS.card_inf_Pc_xOf h
    have hq : 0 < Nat.card V ^ 2 := Nat.pow_pos Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    rw [hkr, hAcard]
    ring
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq φ.range (by rw [hrangecard])
  have hmem : (⟨v, hv⟩ : ↥V) ∈ φ.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem exists_commutator_eq_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {x e u : G}
    (hx : x ∈ H) (he : e ∈ conjSubgroup x (Pc M V)) (heK : e ∉ kOf V H)
    (hu : u ∈ conjSubgroup x V) : ∃ w ∈ Tim79a.xOf V H, ⁅e, w⁆ = u := by
  have hxW : x ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) := Tim79a.H_le_normalizer_xOf V H hx
  have hxK : x ∈ Subgroup.normalizer (kOf V H : Set G) := le_normalizer_kOf V H hx
  have he' : x⁻¹ * e * x ∈ Pc M V := mem_conjSubgroup.mp he
  have heK' : x⁻¹ * e * x ∉ kOf V H := by
    intro hmem
    apply heK
    have heq : e = x * (x⁻¹ * e * x) * x⁻¹ := by group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp hxK _).mp hmem
  have hu' : x⁻¹ * u * x ∈ V := mem_conjSubgroup.mp hu
  obtain ⟨w', hw'mem, hw'⟩ := hS.exists_commutator_eq h he' heK' hu'
  refine ⟨x * w' * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxW w').mp hw'mem.2, ?_⟩
  have hconj : ∀ a b : G, ⁅x * a * x⁻¹, x * b * x⁻¹⁆ = x * ⁅a, b⁆ * x⁻¹ := by
    intro a b
    rw [commutatorElement_def]
    group
  calc ⁅e, x * w' * x⁻¹⁆ = ⁅x * (x⁻¹ * e * x) * x⁻¹, x * w' * x⁻¹⁆ := by
        congr 1
        group
    _ = x * ⁅x⁻¹ * e * x, w'⁆ * x⁻¹ := hconj _ _
    _ = x * (x⁻¹ * u * x) * x⁻¹ := by rw [hw']
    _ = u := by group

section FixedPointsRepSec

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
variable {hl : Fintype.card F = 2 ^ (2 * l)} {ψ : HBar V H ≃* SL(2, F)}
variable (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
variable [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal] [Module (ZMod 2) (SecMod hs)]

private theorem subSec_le_fixedSub_repSec_Pc (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) ≤
      fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) := by
  classical
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have hfix₁ : fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (Pc M V)).map ψ.toMonoidHom) =
      subSec hs (secCent hs (Pc M V) hS.Pc_le) :=
    fixedSub_repSec hs hs.comm ψ hS.Pc_le
  rw [hfix₁]
  refine subSec_mono hs ?_
  refine sup_le ?_ ?_
  · intro n hn
    refine (mem_secCent hs hS.Pc_le).mpr ⟨(Subgroup.mem_inf.mp hn).2, ?_⟩
    intro s hsP
    have hmem : ⁅(n : G), s⁆ ∈ ⁅Pc M V, Pc M V⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hn).1 hsP
    rw [hS.commutator_Pc h] at hmem
    exact le_xOf_self V H hmem
  · intro n hn
    refine (mem_secCent hs hS.Pc_le).mpr ⟨hWK hn, ?_⟩
    intro s hsP
    have hmem : ⁅(n : G), s⁆ ∈ ⁅Tim79a.xOf V H, Pc M V⁆ :=
      Subgroup.commutator_mem_commutator hn hsP
    rw [← hS.inf_Pc_xOf_eq_commutator h] at hmem
    exact hmem.2

private theorem subSec_le_fixedSub_repSec_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {y : G} (hyH : y ∈ H) :
    subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H) ≤
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom) := by
  classical
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hyH
  have hfix₂ : fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom) =
      subSec hs (secCent hs (conjSubgroup y (Pc M V)) hPyH) :=
    fixedSub_repSec hs hs.comm ψ hPyH
  rw [hfix₂]
  refine subSec_mono hs ?_
  refine sup_le ?_ ?_
  · intro n hn
    refine (mem_secCent hs hPyH).mpr ⟨(Subgroup.mem_inf.mp hn).2, ?_⟩
    intro s hsPy
    have hn' : y⁻¹ * (n : G) * y ∈ Pc M V := mem_conjSubgroup.mp (Subgroup.mem_inf.mp hn).1
    have hs' : y⁻¹ * s * y ∈ Pc M V := mem_conjSubgroup.mp hsPy
    have hmem : ⁅y⁻¹ * (n : G) * y, y⁻¹ * s * y⁆ ∈ ⁅Pc M V, Pc M V⁆ :=
      Subgroup.commutator_mem_commutator hn' hs'
    rw [hS.commutator_Pc h] at hmem
    have heq : ⁅(n : G), s⁆ = y * ⁅y⁻¹ * (n : G) * y, y⁻¹ * s * y⁆ * y⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hyH) _).mp
      (le_xOf_self V H hmem)
  · intro n hn
    refine (mem_secCent hs hPyH).mpr ⟨hWK hn, ?_⟩
    intro s hsPy
    have hn' : y⁻¹ * (n : G) * y ∈ Tim79a.xOf V H := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (Tim79a.H_le_normalizer_xOf V H (H.inv_mem hyH)) (n : G)).mp hn
    have hs' : y⁻¹ * s * y ∈ Pc M V := mem_conjSubgroup.mp hsPy
    have hmem : ⁅y⁻¹ * (n : G) * y, y⁻¹ * s * y⁆ ∈ Tim79a.xOf V H := by
      have h1 := Subgroup.commutator_mem_commutator hn' hs'
      rw [← hS.inf_Pc_xOf_eq_commutator h] at h1
      exact h1.2
    have heq : ⁅(n : G), s⁆ = y * ⁅y⁻¹ * (n : G) * y, y⁻¹ * s * y⁆ * y⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hyH) _).mp hmem

private theorem subSec_sup_eq_top (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hPy : conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V)) :
    subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) ⊔
      subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H) = ⊤ := by
  classical
  have hWK : Tim79a.xOf V H ≤ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore
  rw [← subSec_sup (N := kOf V H) (N₀ := Tim79a.xOf V H) hs
    (sup_le inf_le_right hWK) (sup_le inf_le_right hWK)]
  have hK : ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) ⊔
      ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H) = kOf V H := by
    refine le_antisymm (sup_le (sup_le inf_le_right hWK) (sup_le inf_le_right hWK)) ?_
    calc kOf V H = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) := hS.kFact
      _ = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) := by rw [hPy]
      _ ≤ ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) ⊔
            ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H) := by
          refine sup_le ?_ ?_
          · exact le_trans le_sup_left le_sup_left
          · exact le_trans le_sup_left le_sup_right
  rw [hK, subSec_self]

private theorem fixedSub_inf_eq_bot (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hw : Sec45ShapeWith M V H F l hl ψ) {y : G} (hyH : y ∈ H)
    (hyV : conjSubgroup y V ≠ V) :
    fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom) = ⊥ := by
  have hσ : Sec2.IsNatSumModule (repSec hs hs.comm SL(2, F) ψ) :=
    hw.natSum hs (inferInstance : Module (ZMod 2) (SecMod hs))
  have hne : (imgK V H (Pc M V)).map ψ.toMonoidHom ≠
      (imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom := by
    intro heq
    exact hS.imgK_conj_ne h hyH hyV
      (Subgroup.map_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective
        (by simpa using heq.symm))
  have hP2 : (∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1) ∧
      Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = Fintype.card F := by
    simpa [conjSubgroup_one] using hS.map_imgK_conj_sylow h ψ H.one_mem
  exact (Sec2.IsNatSumModule.fixedSub_inf_sup hσ hP2.1 hP2.2
    (hS.map_imgK_conj_sylow h ψ hyH).1
    (hS.map_imgK_conj_sylow h ψ hyH).2 hne).1

end FixedPointsRepSec

theorem fixedSub_repSec_Pc (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ} {hl : Fintype.card F = 2 ^ (2 * l)}
    {ψ : HBar V H ≃* SL(2, F)} (hw : Sec45ShapeWith M V H F l hl ψ)
    (hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal] [Module (ZMod 2) (SecMod hs)] :
    fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) =
      subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) := by
  classical
  obtain ⟨y, hyH, hPy, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hS.Pc_le hS.hH
  have hyV : conjSubgroup y V ≠ V := by
    intro hc
    have hh₀ : conjSubgroup h₀ V = V := hVy.trans hc
    have hh₀M : h₀ ∈ M := h.toHyp.normalizer_eq ▸ mem_normalizer_iff_conjSubgroup_eq.mpr hh₀
    have hP : conjSubgroup h₀ (Pc M V) = Pc M V :=
      conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hh₀M)
    exact hS.not_le (by rw [hS.hH, hP]; exact sup_le h.toHyp.Pc_le_M h.toHyp.Pc_le_M)
  have hX₁le := subSec_le_fixedSub_repSec_Pc (ψ := ψ) hs h hS
  have hX₂le := subSec_le_fixedSub_repSec_conj (ψ := ψ) hs h hS hyH
  have hsup := subSec_sup_eq_top hs h hS hPy
  have hdisj := fixedSub_inf_eq_bot (ψ := ψ) hs h hS hw hyH hyV
  calc fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom)
      = fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
          ⊤ := (inf_top_eq _).symm
    _ = fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
          (subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) ⊔
            subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H)) := by
        rw [hsup]
    _ = subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) ⊔
          (fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
            subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H)) := by
        rw [sup_comm (a := subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H)),
          ← inf_sup_assoc_of_le
            (y := subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H)) hX₁le,
          sup_comm (a := fixedSub (repSec hs hs.comm SL(2, F) ψ)
            ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
            subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H))]
    _ = subSec hs ((Pc M V ⊓ kOf V H) ⊔ Tim79a.xOf V H) := by
        have hbot : fixedSub (repSec hs hs.comm SL(2, F) ψ)
              ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
            subSec hs ((conjSubgroup y (Pc M V) ⊓ kOf V H) ⊔ Tim79a.xOf V H) = ⊥ :=
          le_bot_iff.mp ((inf_le_inf_left _ hX₂le).trans (le_of_eq hdisj))
        rw [hbot, sup_bot_eq]

end Sec45Shape


end CFSG.RankThree.GF2n.Tim81
