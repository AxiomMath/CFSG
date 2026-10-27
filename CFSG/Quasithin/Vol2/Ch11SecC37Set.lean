module

public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Vol2.Ch11SecC37K

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Z_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

omit [Finite G] in
theorem Z_le_VZ (T H : Subgroup G) : quasithinOmegaOneCenter T ≤ VZ T H := le_conjClosure _ _

omit [Finite G] in
theorem le_normalizer_VZ (T H : Subgroup G) : H ≤ Subgroup.normalizer (VZ T H : Set G) :=
  le_normalizer_conjClosure _ _

omit [Finite G] in
theorem K_le_normalizer_VZ (T H : Subgroup G) :
    oTwoUpper H ≤ Subgroup.normalizer (VZ T H : Set G) :=
  (oTwoUpper_le H).trans (le_normalizer_VZ T H)

structure Set37 (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G) (g : G) : Prop where
  hyp : Hyp11 G T L I n
  hV₁ : IsVi T L I n 1 V₁
  h31 : Hyp11_3_1 T L I n V₁ H
  hnot : ¬ Concl11_3_2 T L I n V₁ H
  hAT : conjSubgroup (fsuV T I) g ≤ T
  hAC : ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G)

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem two_le : 2 ≤ n := s.hyp.one_lt

theorem sylow : QuasithinUnique.IsSylowTwoOf T H := SecA.isSylowTwoOf_of_isHStar s.hyp s.h31.hstar

theorem T_le : T ≤ H := s.sylow.1

theorem charTwo : QuasithinUnique.CharTwo H :=
  charTwo_of_inH s.hyp.fsu.qtke.2.1 (s.hyp.fsu.sylow.1.toSylow s.hyp.fsu.sylow.2) s.h31.hstar.1

theorem vz : VZ T H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
    IsElemAbelian 2 (VZ T H) ∧ IsTwoReducedIn H (VZ T H) :=
  conjClosure_isTwoReducedIn_of_charTwo s.sylow s.charTwo le_rfl

theorem isElemAbelian_VZ : IsElemAbelian 2 (VZ T H) := s.vz.2.1

theorem isTwoReducedIn_VZ : IsTwoReducedIn H (VZ T H) := s.vz.2.2

theorem VZ_le_T : VZ T H ≤ T :=
  s.vz.1.trans (inf_le_left.trans (F7.isSylowTwoOf_pCoreOf_le s.sylow))

theorem sup_eq : oTwoUpper H ⊔ T = H := oTwoUpper_sup_eq s.sylow

theorem not_le_M : ¬ H ≤ Subgroup.normalizer (L : Set G) := s.h31.hstar.2.1

theorem K_not_le_M : ¬ oTwoUpper H ≤ Subgroup.normalizer (L : Set G) := fun h =>
  s.not_le_M (s.sup_eq.ge.trans (sup_le h s.hyp.normal))

theorem kind (h1134 : Stmt11_3_4) : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n :=
  (h1134 G T L I n V₁ H g s.hyp s.hV₁ s.h31 s.hnot s.hAT s.hAC).2.1

theorem sParam_eq (hF : SecA.NatFacts) (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4) (hV : IsElemAbelian 2 (fsuV T I)) :
    E3.sParam hV = n := by
  obtain ⟨U₁, U₂, -, h₁, h₂, -, -, -, -, -, -⟩ := SecA.exists_isVi hF h1102 s.hyp
  have hnG2 : ¬ KindG2 L (fsuV T I) n := by
    intro hG
    rcases s.kind h1134 with h | h
    · exact SecA.kind_not_SL3_G2 hG2 s.two_le h hG
    · exact SecA.kind_not_Sp4_G2 hG2 s.two_le h hG
  exact (h1122 G T L I n n U₁ U₂ s.hyp h₁ h₂ (Or.inr ⟨hnG2, rfl⟩)).2.2.2.1 hV

theorem aStar_mem [IsMulCommutative ↥(VZ T H)] (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4) :
    autOn (conjSubgroup (fsuV T I) g) (VZ T H) ∈ E3.aSet n (autOn H (VZ T H)) := by
  obtain ⟨_, h⟩ := (h1134 G T L I n V₁ H g s.hyp s.hV₁ s.h31 s.hnot s.hAT s.hAC).1
  have hV := SecA.isElemAbelian_fsuV s.hyp
  have := h hV
  rwa [s.sParam_eq hF h1102 hG2 h1122 h1134 hV] at this

theorem kStar_equiv (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥(autOn (oTwoUpper H) (VZ T H)) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, ⟨e₁⟩, F, _, _, hF, ⟨e₂⟩⟩ := lemma11_3_7_one h1135 h1136 s.hyp s.hV₁ s.h31 s.hnot
  exact ⟨F, inferInstance, inferInstance, hF, ⟨e₁.trans e₂⟩⟩

theorem pCore_hStar : CFSG.pCore 2 ↥(autOn H (VZ T H)) = ⊥ := by
  have h := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot s.isTwoReducedIn_VZ
  rw [pCoreOf] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (autOn H (VZ T H)).subtype_injective).1 h

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
