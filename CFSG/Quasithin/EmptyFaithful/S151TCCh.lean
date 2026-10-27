module

public import CFSG.Quasithin.EmptyFaithful.S151TBDef
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.S151TB
open scoped commutatorElement Pointwise

section CentreFree

variable {G : Type} [Group G]

@[expose] def CentreFreeModTwoCore (A : Subgroup G) : Prop :=
  ∀ a ∈ A, (∀ l ∈ A, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 A) → a ∈ pCoreOf 2 A

theorem CentreFreeModTwoCore.map {A : Subgroup G} (h : CentreFreeModTwoCore A) (f : G ≃* G) :
    CentreFreeModTwoCore (A.map f.toMonoidHom) := by
  intro a ha hc
  rw [pCoreOf_map_equiv 2 f A] at hc ⊢
  rw [Subgroup.mem_map_equiv] at ha ⊢
  refine h _ ha fun l hl => ?_
  have hfl : f l ∈ A.map f.toMonoidHom := Subgroup.mem_map_equiv.mpr (by simpa using hl)
  have := Subgroup.mem_map_equiv.mp (hc (f l) hfl)
  simpa using this

private theorem mem_pCoreOf_iff {L : Subgroup G} (x : ↥L) :
    (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.pCore 2 ↥L := CFSG.mem_openPCoreOf_iff x

theorem centreFreeModTwoCore_of_center_eq_bot {L : Subgroup G}
    (hLZ : Subgroup.center (LStar L) = ⊥) : CentreFreeModTwoCore L := by
  intro a ha h
  have hmem : (QuotientGroup.mk (⟨a, ha⟩ : ↥L) : LStar L) ∈ Subgroup.center (LStar L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine (QuotientGroup.eq_iff_div_mem.mpr ?_).symm
    have e : (⟨a, ha⟩ : ↥L) * l / (l * ⟨a, ha⟩) = ⟨a, ha⟩ * l * ⟨a, ha⟩⁻¹ * l⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc]
    rw [e]
    exact (mem_pCoreOf_iff (⟨a, ha⟩ * l * ⟨a, ha⟩⁻¹ * l⁻¹ : ↥L)).mp (h l l.2)
  rw [hLZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact (mem_pCoreOf_iff ⟨a, ha⟩).mpr hmem

private theorem le_normalizer_of_conj_mem {S K : Subgroup G}
    (h : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K) : S ≤ Subgroup.normalizer (K : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h s hs k, fun hk => ?_⟩
  have := h s⁻¹ (S.inv_mem hs) _ hk
  simpa [mul_assoc] using this

theorem charTwo_sup_of_commutator_le {A B : Subgroup G} (hA : CharTwo A) (hB : CharTwo B)
    (hAZ : CentreFreeModTwoCore A) (hBZ : CentreFreeModTwoCore B)
    (hcomm : ⁅A, B⁆ ≤ pCoreOf 2 A ⊓ pCoreOf 2 B) : CharTwo (A ⊔ B) := by
  set PA : Subgroup G := pCoreOf 2 A with hPA
  set PB : Subgroup G := pCoreOf 2 B with hPB
  have hPA2 : IsPGroup 2 PA := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 A
  have hPB2 : IsPGroup 2 PB := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 B
  have hPAA : PA ≤ A := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 A
  have hPBB : PB ≤ B := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 B
  have hAPA : A ≤ Subgroup.normalizer (PA : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 A
  have hBPB : B ≤ Subgroup.normalizer (PB : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 B
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ PA ⊓ PB := fun a ha b hb =>
    hcomm (Subgroup.commutator_mem_commutator ha hb)
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ PA ⊓ PB := fun b hb a ha => by
    have : ⁅b, a⁆ ∈ ⁅A, B⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb ha
    exact hcomm this
  have hAnB : A ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_conj_mem fun a ha b hb => by
      have h1 : a * b * a⁻¹ * b⁻¹ ∈ B := hPBB (hAB a ha b hb).2
      simpa [mul_assoc] using B.mul_mem h1 hb
  have hBnA : B ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_conj_mem fun b hb a ha => by
      have h1 : b * a * b⁻¹ * a⁻¹ ∈ A := hPAA (hBA b hb a ha).1
      simpa [mul_assoc] using A.mul_mem h1 ha
  set X : Subgroup G := A ⊔ B with hX
  have hAX : A ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXA : X ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBnA
  have hXB : X ≤ Subgroup.normalizer (B : Set G) := sup_le hAnB Subgroup.le_normalizer
  have hXPA : X ≤ Subgroup.normalizer (PA : Set G) :=
    sup_le hAPA (hBnA.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 A))
  have hXPB : X ≤ Subgroup.normalizer (PB : Set G) :=
    sup_le (hAnB.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 B)) hBPB
  have hPAX : PA ≤ pCoreOf 2 X :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (hPAA.trans hAX) hXPA hPA2
  have hPBX : PB ≤ pCoreOf 2 X :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (hPBB.trans hBX) hXPB hPB2
  set P : Subgroup G := pCoreOf 2 X with hP
  have hXP : X ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  set C : Subgroup G := X ⊓ Subgroup.centralizer (P : Set G) with hC
  have hXC : X ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf X X _
      Subgroup.le_normalizer
      (hXP.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer P))
  have hCcomm : ∀ d ∈ C, ∀ l ∈ X, d * l * d⁻¹ * l⁻¹ ∈ C := fun d hd l hl => by
    have h1 : l * d⁻¹ * l⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hXC hl) _).mp (C.inv_mem hd)
    simpa [mul_assoc] using C.mul_mem hd h1
  intro d hd
  have hdC : d ∈ C := hd
  have hdX : d ∈ X := hd.1
  have hdAB : d ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hAnB]
    exact hdX
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hdAB
  have haPA : a ∈ PA := by
    refine hAZ a ha fun l hl => ?_
    have heC := hCcomm (a * b) hdC l (hAX hl)
    have heA : a * b * l * (a * b)⁻¹ * l⁻¹ ∈ A := by
      have h1 : a * b * l * (a * b)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hXA hdX) l).mp hl
      exact A.mul_mem h1 (A.inv_mem hl)
    have he : a * b * l * (a * b)⁻¹ * l⁻¹ ∈ PA :=
      hA ⟨heA, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPAX) heC.2⟩
    have ho : a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ ∈ PA :=
      (Subgroup.mem_normalizer_iff.mp (hAPA ha) _).mp (hBA b hb l hl).1
    have key : a * l * a⁻¹ * l⁻¹ =
        (a * (b * l * b⁻¹ * l⁻¹) * a⁻¹)⁻¹ * (a * b * l * (a * b)⁻¹ * l⁻¹) := by group
    rw [key]
    exact PA.mul_mem (PA.inv_mem ho) he
  have hbPB : b ∈ PB := by
    refine hBZ b hb fun l hl => ?_
    have heC := hCcomm (a * b) hdC l (hBX hl)
    have heB : a * b * l * (a * b)⁻¹ * l⁻¹ ∈ B := by
      have h1 : a * b * l * (a * b)⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hXB hdX) l).mp hl
      exact B.mul_mem h1 (B.inv_mem hl)
    have he : a * b * l * (a * b)⁻¹ * l⁻¹ ∈ PB :=
      hB ⟨heB, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPBX) heC.2⟩
    have hm : b * l * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hl) (B.inv_mem hb)
    have ho : a * (b * l * b⁻¹) * a⁻¹ * (b * l * b⁻¹)⁻¹ ∈ PB := (hAB a ha _ hm).2
    have key : b * l * b⁻¹ * l⁻¹ =
        (a * (b * l * b⁻¹) * a⁻¹ * (b * l * b⁻¹)⁻¹)⁻¹ * (a * b * l * (a * b)⁻¹ * l⁻¹) := by group
    rw [key]
    exact PB.mul_mem (PB.inv_mem ho) he
  exact P.mul_mem (hPAX haPA) (hPBX hbPB)

end CentreFree

set_option linter.unusedVariables false in
theorem charTwo_conjClosure_sup_of_two {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (ρ : G) (hρ : ρ ∈ R) (hR2 : IsPGroup 2 R)
    (hL : ⁅L, L⁆ = L) (hLc : CharTwo L) (hLq : CFSG.IsQuasisimple (LStar L))
    (hLZ : Subgroup.center (LStar L) = ⊥)
    (hconj : ∀ σ ∈ R, L.map (MulAut.conj σ).toMonoidHom = L ∨
      L.map (MulAut.conj σ).toMonoidHom = L.map (MulAut.conj ρ).toMonoidHom)
    (hcomm : ⁅L, L.map (MulAut.conj ρ).toMonoidHom⁆ ≤
      pCoreOf 2 L ⊓ pCoreOf 2 (L.map (MulAut.conj ρ).toMonoidHom)) :
    CharTwo (conjClosure L R ⊔ R) := by
  have hZ : CentreFreeModTwoCore L := centreFreeModTwoCore_of_center_eq_bot hLZ
  have hX : CharTwo (L ⊔ L.map (MulAut.conj ρ).toMonoidHom) :=
    charTwo_sup_of_commutator_le hLc ((charTwo_map_equiv_iff (MulAut.conj ρ) L).mpr hLc) hZ
      (hZ.map (MulAut.conj ρ)) hcomm
  have hcc : conjClosure L R = L ⊔ L.map (MulAut.conj ρ).toMonoidHom := by
    refine le_antisymm (conjClosure_le fun h hh z hz => ?_) ?_
    · have hz' : h * z * h⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom :=
        ⟨z, hz, by simp [MulAut.conj_apply]⟩
      rcases hconj h hh with e | e
      · rw [e] at hz'
        exact Subgroup.mem_sup_left hz'
      · rw [e] at hz'
        exact Subgroup.mem_sup_right hz'
    · refine sup_le (le_conjClosure L R) ?_
      rintro _ ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure hρ hz
  rw [hcc]
  exact Unc25G2.charTwo_sup_of_isPGroup_le_normalizer hX hR2 (hcc ▸ le_normalizer_conjClosure L R)

end CFSG.Quasithin.S151TC
