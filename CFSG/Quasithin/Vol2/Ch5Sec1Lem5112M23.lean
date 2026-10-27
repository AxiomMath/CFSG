module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lie
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Par
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34Out
public import CFSG.Quasithin.H13.A7Nat1238QTab

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch11.SecB (L2BadType FactMathieuOrders)

@[expose] def FactM23L34 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L A S R : Subgroup Γ), IsSporadic .M23 ↥L → A ≤ L →
    IsSL3Ch5 2 (ModO2 A) → IsSylowTwoOf S A → R ≤ Subgroup.normalizer (L : Set Γ) →
    R ≤ Subgroup.normalizer (A : Set Γ) → R ≤ Subgroup.normalizer (S : Set Γ) →
    ∃ P : Subgroup Γ, IsMaxParabolic2 A P ∧ A ⊓ Subgroup.normalizer (S : Set Γ) ≤ P ∧
      R ≤ Subgroup.normalizer (P : Set Γ)

theorem IsSL3Ch5.of_mulEquiv {Y Z : Type} [Group Y] [Group Z] {m : ℕ} (e : Y ≃* Z)
    (h : IsSL3Ch5 m Y) : IsSL3Ch5 m Z := by
  rcases h with h | ⟨F, hF, hFf, hcard, ⟨eF⟩⟩
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr ⟨F, hF, hFf, hcard, ⟨e.symm.trans eF⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_psl3_quotient {K : Subgroup G} [Group.IsPerfect ↥K] {m : ℕ} (hm : 2 ≤ m)
    (h : IsSL3Ch5 m (O2Q K)) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (_ : IsSimpleGroup Y) (ψ : ↥K →* Y),
      Function.Surjective ψ ∧ IsPSL 3 2 m Y ∧
        CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
  rcases h with hL3 | ⟨F, _, _, hF, ⟨eF⟩⟩
  · have hY : IsPSL 3 2 m (O2Q K) :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL3
    have : IsSimpleGroup (O2Q K) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 m hY).2
    exact ⟨O2Q K, inferInstance, inferInstance, inferInstance, QuotientGroup.mk' _,
      QuotientGroup.mk'_surjective _, hY, openQuasisimple_of isQuasisimple_o2q_of_simple⟩
  · have hY : IsPSL 3 2 m (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      ⟨⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance,
        hF, ⟨projectiveSpecialLinearGroupEquivStatedProj 3 F⟩⟩
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 m hY).2
    have hq : CFSG.IsQuasisimple (O2Q K) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl)
    exact ⟨Matrix.ProjectiveSpecialLinearGroup (Fin 3) F, inferInstance, inferInstance,
      inferInstance, ((QuotientGroup.mk' _).comp eF.toMonoidHom).comp (QuotientGroup.mk' _),
      ((QuotientGroup.mk'_surjective _).comp eF.surjective).comp (QuotientGroup.mk'_surjective _),
      hY, openQuasisimple_of hq⟩

namespace EmbLoc

variable {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
include l

theorem false_of_l34 (hM : FactMathieuOrders)
    (hM23 : FactM23L34) (h312 : A312ForSQTK)
    (hSL : IsSL3Ch5 2 (O2Q K)) (hD : E2.IsDiagramNontrivial S K (S ⊓ K)) : False := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
  obtain ⟨Y, _, _, _, ψ, hψ, hY, hQ⟩ := exists_psl3_quotient le_rfl hSL
  have hYab := Vol2.Ch11.SecB.nonabelian_of_perfect_surjective ψ hψ
  rcases l.cases h312 with hc | hnq
  · have hM23L := Vol2.Ch11.SecB.m23_of_case_of_l34 hYab (isPGroup_openPCore K) hQ ψ hψ hY hM
      (barMap l.le_X) (barMap_surjective _) hc
    obtain ⟨eB⟩ := l.bar_equiv
    have hSLb : IsSL3Ch5 2 (ModO2 (modO2Image X K)) := IsSL3Ch5.of_mulEquiv eB hSL
    have hTK : S ≤ Subgroup.normalizer (K : Set G) := l.normalizes
    have hTbK : o2Img X S ≤ Subgroup.normalizer ((modO2Image X K : Subgroup (O2Q X)) :
        Set (O2Q X)) := A7.map_le_normalizer_modO2Image hTK
    have hTbH : o2Img X S ≤ Subgroup.normalizer ((modO2Image X Kh : Subgroup (O2Q X)) :
        Set (O2Q X)) := A7.map_le_normalizer_modO2Image l.S_le_normalizer_hat
    have hTbS : o2Img X S ≤ Subgroup.normalizer
        ((o2Img X S ⊓ modO2Image X K : Subgroup (O2Q X)) : Set (O2Q X)) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer ht, hTbK ht⟩)
    have hSb : IsSylowTwoOf (o2Img X S ⊓ modO2Image X K) (modO2Image X K) := by
      have h1 : IsSylowTwoOf (o2Img X S) (modO2Image X K ⊔ o2Img X S) :=
        QuasithinUnique.isSylowTwoOf_of_le l.sylowBar le_sup_right
      have h2 := A312.isSylowTwoOf_inf_of_subnormal
        (subnormal_of_mem_cComp (show modO2Image X K ∈ cComp (modO2Image X K ⊔ o2Img X S)
          from l.bar_lFamily)) h1
      exact h2
    obtain ⟨Pb, hPb, hBPb, hTPb⟩ := hM23 (O2Q X) (modO2Image X Kh) (modO2Image X K)
      (o2Img X S ⊓ modO2Image X K) (o2Img X S) hM23L
      (Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr
        (l.le_hat (Subgroup.mem_subgroupOf.mp hx)))
      hSLb hSb hTbH hTbK hTbS
    have hSK : IsSylowTwoOf (S ⊓ K) K := l.sylowK
    obtain ⟨P, hP, hBP, hTP⟩ := exists_maxParabolic_lift l.sylowX l.le_X hTK hSK hSb hPb
      hBPb hTPb
    exact hD P hP hBP hTP
  · exact Vol2.Ch11.SecB.false_of_a312Nonquasi (k := 2) le_rfl (Or.inr (Or.inr (Or.inl hY))) hQ
      ψ hψ l.bar_lt.le (barMap l.le_X) (barMap_surjective _) hnq

end EmbLoc

namespace Emb512

variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem false_of_l34 (hM : FactMathieuOrders)
    (hM23 : FactM23L34) (h312 : A312ForSQTK) (heq : K₁ = oTwoUpper H)
    (hSL : IsSL3Ch5 2 (O2Q K₁)) (hD : E2.IsDiagramNontrivial T K₁ (T ⊓ K₁)) : False :=
  (e.toLoc heq).false_of_l34 hM hM23 h312 hSL hD

end Emb512

end CFSG.Quasithin.H13
