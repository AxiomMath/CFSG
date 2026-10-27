module

public import Certificates.Kernel.Co2Cen.GlueChecks
public import Certificates.Kernel.Co2Census.Facts
public import CFSG.Certificates.Kernel.Co2Cen.Look
public import CFSG.Certificates.Kernel.Co2JRank.Sound
public import CFSG.RankThree.Co2.WFacts

@[expose] public section

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.Co2Cen CFSG.KC.Co2JRank
  CFSG.KC.TabMatGrp CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2TInv
  CertificateChecks.KernelSpor.Co2Cls CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem isUnit_Cm : ∀ x ∈ Cm, IsUnit x := by
  rw [Cm_eq]
  exact isUnit_C

theorem crConj_rec {c : ℕ} (hc : c < 10) {i : ℕ} (hi : i < NCS c) :
    CrConj (repMat c) (MatP 22 (elemAt (CFS c) i)) := by
  obtain ⟨g, hg, e⟩ := tree_conj (recsAll c hc) i hi
  exact ⟨g, by rw [Cm_eq]; exact hg, by rw [Co2Syl.repMat_eq hc]; exact e⟩

theorem crConj_look {X r cls : ℕ} (hcls : cls < 1024) (h : lookC CFS NCS X r cls = true) :
    cls.testBit (Nat.land r 15) = true ∧ CrConj (repMat (Nat.land r 15)) (MatP 22 X) := by
  obtain ⟨hb, hi, e⟩ := lookC_spec h
  refine ⟨hb, ?_⟩
  rw [← e]
  exact crConj_rec (lt_ten_of_testBit hcls hb) hi

theorem rec_of_conj {CF : ℕ → ℕ} {X0 N : ℕ} (hok : ∀ k < N, recC CF GC 21 X0 N k = true)
    (hcard : Nat.card (Conj X0) = N) {x : M22} (h : ∃ g ∈ genMonN 21 GC, g * MatP 22 X0 = x * g) :
    ∃ k < N, MatP 22 (elemAt CF k) = x := by
  let f : Fin N → Conj X0 := fun k => ⟨MatP 22 (elemAt CF k), tree_conj hok k k.isLt⟩
  have hf : Function.Injective f := fun a b e =>
    Fin.ext (CFSG.KC.Co2Cls.tree_inj hok a a.isLt b b.isLt (congrArg Subtype.val e))
  obtain ⟨k, hk⟩ := (hf.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])).2 ⟨x, h⟩
  exact ⟨k, k.isLt, congrArg Subtype.val hk⟩

theorem cm_conj {c : ℕ} (hc : c < 10) {x : M22} (h : CrConj (repMat c) x) :
    ∃ g ∈ genMonN 21 GC, g * MatP 22 (RP c) = x * g := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨g, by rw [← Cm_eq]; exact hg, by rw [← Co2Syl.repMat_eq hc]; exact e⟩

theorem rec_of_conj2 {x : M22} (h : CrConj (repMat 2) x) :
    ∃ k < 1260, MatP 22 (elemAt C2 k) = x :=
  rec_of_conj rec2 Final.class2.1 (cm_conj (by norm_num) h)

theorem rec_of_conj7 {x : M22} (h : CrConj (repMat 7) x) :
    ∃ k < 1008, MatP 22 (elemAt C7 k) = x :=
  rec_of_conj rec7 Final.class7.1 (cm_conj (by norm_num) h)

theorem rank_conj {a x : M22} (h : CrConj a x) : (x + 1).rank = (a + 1).rank := by
  obtain ⟨g, hg, e⟩ := h
  refine CFSG.KC.Co2Cls.rank_eq_of_mul (isUnit_Cm g hg) ?_
  rw [add_mul, mul_add, one_mul, mul_one, e]

theorem rk_of {c ρ j : ℕ} (hc : c < 10) (hρ : ρ ≤ 22)
    (h : rankL (Nat.xor (RP c) IDP) (elemOf (RK j)) (scQ (RK j)) ρ = true) :
    (repMat c + 1).rank = ρ := by
  rw [Co2Syl.repMat_eq hc, ← MatP_xorI]
  exact rankL_sound hρ h

theorem rk_rep : (repMat 0 + 1).rank = 6 ∧ (repMat 1 + 1).rank = 8 ∧ (repMat 2 + 1).rank = 6 ∧
    (repMat 3 + 1).rank = 8 ∧ (repMat 5 + 1).rank = 8 ∧ (repMat 7 + 1).rank = 6 :=
  ⟨rk_of (by norm_num) (by norm_num) (repRk 0 (by norm_num)),
    rk_of (by norm_num) (by norm_num) (repRk 1 (by norm_num)),
    rk_of (by norm_num) (by norm_num) (repRk 2 (by norm_num)),
    rk_of (by norm_num) (by norm_num) (repRk 3 (by norm_num)),
    rk_of (by norm_num) (by norm_num) (repRk 4 (by norm_num)),
    rk_of (by norm_num) (by norm_num) (repRk 5 (by norm_num))⟩

theorem rank_InA {x : M22} (h : InA x) : (x + 1).rank = 6 := by
  obtain ⟨c, hc, e⟩ := h
  rw [rank_conj e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact rk_rep.1
  · exact rk_rep.2.2.1
  · exact rk_rep.2.2.2.2.2

theorem rank_InB {x : M22} (h : InB x) : (x + 1).rank = 8 := by
  obtain ⟨c, hc, e⟩ := h
  rw [rank_conj e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact rk_rep.2.1
  · exact rk_rep.2.2.2.1
  · exact rk_rep.2.2.2.2.1

end CertificateChecks.KernelSpor.Co2Cen

end
