module

public import CFSG.Quasithin.Background.D2Z12
public import CFSG.Quasithin.Background.D2Z10
public import CFSG.Quasithin.Background.D2Z11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

section Classify

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem rk_commSub_Nt_A (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (hne : centR X t ≠ ⊥) (hr2 : rk (commV (centR X t)) = 2) :
    rk (commSub (commV (centR X t)) A) = 1 := by
  have hsum := commSub_card_four (E := A) k.ha k.hb k.mem (Nt_inv_A' h k.ha)
  have s1 := rk_commSub_Nt_self hV h k hne
  have e1 := rk_Nt_eq_two_mul hV h k hne
  have hbot : commSub (commV (centR X t)) (Subgroup.zpowers t) = ⊥ := by
    have : rk (commSub (commV (centR X t)) (Subgroup.zpowers t)) = 0 := by omega
    exact (rk_eq_zero_iff hV).mp this
  rw [hsum, hbot, bot_sup_eq]
  omega

theorem centR_le_commutator (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {s u : MulAut V}
    (k : KleinData A s u) : centR X s ≤ ⁅pCoreOf 3 X, A⁆ := by
  intro y hy
  have hyP := centR_le_pCoreOf X s hy
  have hinv := inverts_centR hV h k y hy
  have hy3 := centR_pow_three hV h k hy
  have hc : ⁅y, u⁆ = y * y := by
    simp only [commutatorElement_def]
    calc y * u * y⁻¹ * u⁻¹ = y * (u * y * u⁻¹)⁻¹ := by group
      _ = y * (y⁻¹)⁻¹ := by rw [hinv]
      _ = y * y := by rw [inv_inv]
  have hmem : y * y ∈ ⁅pCoreOf 3 X, A⁆ := hc ▸ Subgroup.commutator_mem_commutator hyP k.hb
  have : y = (y * y) * (y * y) := by
    calc y = y ^ 3 * y := by rw [hy3, one_mul]
      _ = (y * y) * (y * y) := by rw [pow_three']; group
  rw [this]
  exact Subgroup.mul_mem _ hmem hmem

theorem commutator_pCoreOf_eq (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ⁅pCoreOf 3 X, A⁆ = pCoreOf 3 X := by
  apply le_antisymm
  · refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    have : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact (pCoreOf 3 X).mul_mem hg₁ (h.conj_mem hg₂ ((pCoreOf 3 X).inv_mem hg₁))
  · obtain ⟨a, b, k⟩ := h.exists_klein hV
    exact (pCoreOf_eq_sup_centR hV h k).le.trans (sup_le (sup_le (centR_le_commutator hV h k)
      (centR_le_commutator hV h k.symm)) (centR_le_commutator hV h k.third.symm))

@[expose] def Case7i (X A : Subgroup (MulAut V)) (Pi : Fin 2 → Subgroup (MulAut V)) : Prop :=
  (∃ t u : MulAut V, KleinData A t u ∧ conjBy t (Pi 0) = Pi 1 ∧ conjBy t (Pi 1) = Pi 0 ∧
      conjBy u (Pi 0) = Pi 1 ∧ conjBy u (Pi 1) = Pi 0) ∧
    ∃ L₁ L₂ : Subgroup (MulAut V), (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∧ L₁ ⊓ L₂ = ⊥ ∧
      L₁ ⊔ L₂ = pCoreOf 3 X ⊔ A ∧ Nonempty (↥L₁ ≃* DihedralGroup 3) ∧
      Nonempty (↥L₂ ≃* DihedralGroup 3) ∧ ∀ i, Pi i ⊓ L₁ = ⊥ ∧ Pi i ⊓ L₂ = ⊥

@[expose] def Case7ii (A : Subgroup (MulAut V)) (Pi : Fin 3 → Subgroup (MulAut V)) : Prop :=
  (∀ g ∈ A, ∀ i, conjBy g (Pi i) = Pi i) ∧ ∀ i, rk (commSub (commV (Pi i)) A) = 1

theorem case7ii_of_three (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (kt : KTriple A t u w) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) (h3 : centR X w ≠ ⊥) :
    Case7ii A ![centR X t, centR X u, centR X w] := by
  obtain ⟨-, r1, r2, r3, -, -, -⟩ := caseThree hV h kt h1 h2 h3
  refine ⟨?_, ?_⟩
  · intro g hg i
    fin_cases i
    · exact conjBy_eq_of_forall_mem fun y hy => h.centR_conj kt.tu.ha hg hy
    · exact conjBy_eq_of_forall_mem fun y hy => h.centR_conj kt.tu.hb hg hy
    · exact conjBy_eq_of_forall_mem fun y hy => h.centR_conj kt.tw.hb hg hy
  · intro i
    fin_cases i
    · exact rk_commSub_Nt_A hV h kt.tu h1 r1
    · exact rk_commSub_Nt_A hV h kt.tu.symm h2 r2
    · exact rk_commSub_Nt_A hV h kt.tw.symm h3 r3

theorem D214_classify (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    r = 3 / 2 ∧
      ((∃ Pi : Fin 2 → Subgroup (MulAut V), PDecomp X Pi ∧ Case7i X A Pi) ∨
        (∃ Pi : Fin 3 → Subgroup (MulAut V), PDecomp X Pi ∧ Case7ii A Pi)) := by
  obtain ⟨a₀, b₀, k₀⟩ := h.exists_klein hV
  obtain ⟨t, u, kt, h1, h2⟩ := exists_nontrivial_pair hV h k₀
  by_cases h3 : centR X (t * u) = ⊥
  · obtain ⟨hr, -, -⟩ := caseTwo hV h kt h1 h2 h3
    refine ⟨hr, Or.inl ?_⟩
    obtain ⟨a, b, haQ, hbQ, haz, hbz, hao, hbo, hd, hc1, hc2, hc3, hc4⟩ :=
      pdecomp_two hV h kt h1 h2 h3
    obtain ⟨L₁, L₂, hcomm, hinf, hsup, hD1, hD2, hdg1, hdg2⟩ :=
      two_dihedral hV h kt haQ hbQ haz hbz hao hbo h3
    refine ⟨_, hd, ⟨t, u, kt, ?_, ?_, ?_, ?_⟩, L₁, L₂, hcomm, hinf, hsup, hD1, hD2, ?_⟩
    · simpa using hc1
    · simpa using hc2
    · simpa using hc3
    · simpa using hc4
    · intro i
      fin_cases i
      · simpa using hdg1
      · simpa using hdg2
  · have h3' : centR X (t * u) ≠ ⊥ := h3
    obtain ⟨hr, -⟩ := caseThree hV h kt.toTriple h1 h2 h3'
    exact ⟨hr, Or.inr ⟨_, pdecomp_three hV h kt.toTriple h1 h2 h3',
      case7ii_of_three hV h kt.toTriple h1 h2 h3'⟩⟩

theorem exists_pdecomp (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ ∃ Pi : Fin s → Subgroup (MulAut V),
      PDecomp X Pi ∧ Set.range Pi = Pfam X := by
  obtain ⟨-, h1 | h1⟩ := D214_classify hV h
  · obtain ⟨Pi, hd, -⟩ := h1
    exact ⟨2, Or.inl rfl, Pi, hd, hd.range_eq hV (pCoreOf_comm hV h)⟩
  · obtain ⟨Pi, hd, -⟩ := h1
    exact ⟨3, Or.inr rfl, Pi, hd, hd.range_eq hV (pCoreOf_comm hV h)⟩

theorem D2_14_2 (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ ∃ Pi : Fin s → Subgroup (MulAut V),
      (∀ i, Pi i ≤ pCoreOf 3 X ∧ Nat.card (Pi i) = 3) ∧ iSupIndep Pi ∧
        ⨆ i, Pi i = pCoreOf 3 X ∧ Set.range Pi = Pfam X ∧ ⁅pCoreOf 3 X, A⁆ = pCoreOf 3 X := by
  obtain ⟨s, hs, Pi, hd, hr⟩ := exists_pdecomp hV h
  exact ⟨s, hs, Pi, fun i => ⟨hd.le_P i, hd.card_eq i⟩, hd.indep, hd.sup_eq, hr,
    commutator_pCoreOf_eq hV h⟩

theorem D2_14_3 (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ ∃ Pi : Fin s → Subgroup (MulAut V),
      ((∀ i, Pi i ≤ pCoreOf 3 X ∧ Nat.card (Pi i) = 3) ∧ iSupIndep Pi ∧
        ⨆ i, Pi i = pCoreOf 3 X ∧ Set.range Pi = Pfam X) ∧
      commV (pCoreOf 3 X) = ⨆ i, commV (Pi i) ∧ iSupIndep (fun i => commV (Pi i)) ∧
        ∀ i, rk (commV (Pi i)) = 2 := by
  obtain ⟨s, hs, Pi, hd, hr⟩ := exists_pdecomp hV h
  exact ⟨s, hs, Pi, ⟨fun i => ⟨hd.le_P i, hd.card_eq i⟩, hd.indep, hd.sup_eq, hr⟩,
    hd.vsup.symm, hd.vindep, hd.rk_eq⟩

theorem D2_14_6 (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) : r = 3 / 2 :=
  (D214_classify hV h).1

theorem D2_14_7 (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    (∃ Pi : Fin 2 → Subgroup (MulAut V), PDecomp X Pi ∧ Set.range Pi = Pfam X ∧
        Case7i X A Pi) ∨
      (∃ Pi : Fin 3 → Subgroup (MulAut V), PDecomp X Pi ∧ Set.range Pi = Pfam X ∧
        Case7ii A Pi) := by
  obtain ⟨-, h1 | h1⟩ := D214_classify hV h
  · obtain ⟨Pi, hd, hc⟩ := h1
    exact Or.inl ⟨Pi, hd, hd.range_eq hV (pCoreOf_comm hV h), hc⟩
  · obtain ⟨Pi, hd, hc⟩ := h1
    exact Or.inr ⟨Pi, hd, hd.range_eq hV (pCoreOf_comm hV h), hc⟩

end Classify

end CFSG.Quasithin
