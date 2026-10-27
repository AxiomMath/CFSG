module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108H207
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint (LieModel)
open F10 (IsList207 K108FamL2 K108FamSz K108FamU3 K108FamL3 K108FamSp4 K108FamG2 K108Fam3D4 K108Fam2F4 K108FamU4
  K108FamU5 K108FamL4 K108FamSp6 K108FamO8m K108Fam3D4two)

variable {G : Type} [Group G] [Finite G]

section Shape207


theorem uc22p22r_lieModel_of_szL2Product207 {X P : Type} [Group X] [Finite X] [Group P] {K' : Subgroup X}
    (e : P ≃* ↥K') (hP : CFSG.Open.IsQuasisimple P) (hsub : CFSG.Open.IsSubnormal K' ⊤) {n : ℕ}
    (h : IsSzL2Product X n) : IsSz (P ⧸ Subgroup.center P) n ∨ IsL2 (P ⧸ Subgroup.center P) n := by
  obtain ⟨A, B, _, _, ⟨f⟩, hA, hB⟩ := h
  have hK' : CFSG.Open.IsComponentOf K' ⊤ :=
    ⟨le_top, hsub, CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hP⟩
  have hne : K' ≠ ⊥ := uc22p22r_ne_bot_of_equiv e hP
  have hsub' : K'.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hsub
  have fin : ∀ {C : Type} [Group C], (IsSz C n ∨ IsL2 C n) → Nonempty (P ≃* C) →
      IsSz (P ⧸ Subgroup.center P) n ∨ IsL2 (P ⧸ Subgroup.center P) n := by
    intro C _ hC ⟨g⟩
    rcases hC with hC | hC
    · exact Or.inl (uc22p22r_lieModel_quot_center g hP (by decide) hC)
    · exact Or.inr (uc22p22r_lieModel_quot_center g hP (by decide) hC)
  have hsimp : ∀ {C : Type} [Group C], (IsSz C n ∨ IsL2 C n) → IsSimpleGroup C := by
    intro C _ hC
    rcases hC with hC | hC
    · exact uc22p22r_lieModel_isSimple (by decide) hC
    · exact uc22p22r_lieModel_isSimple (by decide) hC
  haveI : IsSimpleGroup A := hsimp hA
  haveI : IsSimpleGroup B := hsimp hB
  have hsup : ((MonoidHom.snd A B).comp f.toMonoidHom).ker ⊔
      ((MonoidHom.fst A B).comp f.toMonoidHom).ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = f.symm ((f x).1, 1) * f.symm (1, (f x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · show (f (f.symm ((f x).1, 1))).2 = 1
      simp
    · show (f (f.symm (1, (f x).2))).1 = 1
      simp
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · obtain ⟨g⟩ := uc22p22r_equiv_factor f hsub' hne hle
    exact fin hA ⟨e.trans g⟩
  · obtain ⟨g⟩ := uc22p22r_equiv_factor (f.trans MulEquiv.prodComm) hsub' hne (fun x hx => hle hx)
    exact fin hB ⟨e.trans g⟩

theorem uc22p22r_shape207 (D : Data G) (h207 : S20_7 D) (h1930 : H1930 D) {L K : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L) : IsList207 (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
  obtain ⟨K', -, ⟨e, -⟩, -, -, hsub⟩ := uc22p22r_bar2_quasisimple_iso hK
  have hqs : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hA : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ},
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus ∨ t = .twistedB2 ∨ t = .G2 ∨
        t = .trialityD4 ∨ t = .twistedF4) → LieModel (Bar2 L) t m 2 n →
      LieModel (Bar2 K ⧸ Subgroup.center (Bar2 K)) t m 2 n :=
    fun ht h => uc22p22r_lieModel_of_subnormal e hqs hsub ht h
  rcases h207 h1930 L hL with ⟨n, hn, h⟩ | h | h | h | h | h | ⟨n, hn, h⟩ | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · have hF : K108FamSz _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamL2 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamL3 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamU3 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamL4 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamU4 _ := ⟨n, hn.le, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamG2 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108Fam3D4 _ := ⟨n, hn.le, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108Fam2F4 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamSp4 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamL3 _ := ⟨n, hn, uc22p22r_lieModel_of_quasisimple e hqs hsub h.1 h.2⟩
      simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamU3 _ := ⟨n, hn, uc22p22r_lieModel_of_quasisimple e hqs hsub h.1 h.2⟩
      simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamSp6 _ := ⟨n, hn, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamO8m _ := ⟨n, hn.le, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
  · have hF : K108FamU4 _ := ⟨2, le_rfl, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
  · have hF : K108FamU5 _ := hA (by decide) h; simp only [IsList207, hF, true_or, or_true]
  · have hF : K108FamO8m _ := ⟨2, le_rfl, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
  · have hF : K108Fam3D4 _ := ⟨2, le_rfl, hA (by decide) h⟩; simp only [IsList207, hF, true_or, or_true]
  · have hF : K108Fam3D4two _ := hA (by decide) h; simp only [IsList207, hF, or_true]
  · rcases uc22p22r_lieModel_of_szL2Product207 e hqs hsub h with h | h
    · have hF : K108FamSz _ := ⟨n, hn, h⟩; simp only [IsList207, hF, true_or, or_true]
    · have hF : K108FamL2 _ := ⟨n, hn, h⟩; simp only [IsList207, hF, true_or]
  · have hF : K108FamU3 _ := ⟨3, by norm_num, uc22p22r_lieModel_of_suCentralSquare e hqs hsub h⟩
    simp only [IsList207, hF, true_or, or_true]

end Shape207

end CFSG.LocalAnalysis.UniquenessCase.UC22
