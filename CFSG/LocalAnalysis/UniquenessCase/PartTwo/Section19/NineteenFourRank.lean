module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightF
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09n
public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveA5
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846Ker

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem ker_rhoL_sup_eq_pCoreOf {J T JT : Subgroup G} (hJT : JT = J ⊔ T)
    (hJalt : IsAlt (Bar2 J) 5) (hT2 : IsPGroup 2 T)
    (hJTN : JT ≤ Subgroup.normalizer (J : Set G)) :
    ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL J).comp
        (Subgroup.inclusion hJTN)).ker = (pCoreOf 2 JT).subgroupOf JT := by
  subst hJT
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun hx => UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one hT2 (le_sup_right.trans hJTN)
      (fun y hy _ hρ => UC22.F09.mem_pCoreOf_of_rhoL_eq_one hJalt hy hρ) x.2 (hJTN x.2) hx,
    fun hx => UC6S846.rhoL_eq_one_of_mem_pCoreOf le_sup_left (hJTN x.2) hx⟩

theorem mQuot_le_two_19 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {A J : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hJ : JChoice19 D L K J)
    (hJ5 : ¬ (J = L ⊔ K ∨ (J = L ∧ IsU3 (Bar2 L) 2))) :
    E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) ≤ 2 := by
  classical
  have hJeq : J = L ∨ J = K := by
    rcases hJ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (Or.inl h1) hJ5
  have hLN : (L.subgroupOf D.M).Normal := by
    rcases hJ with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (Or.inl h1) hJ5
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hKn : (K.subgroupOf D.M).Normal := by
    rcases dichotomy_19 h with ⟨-, x, hxM, hKx⟩ | ⟨-, -, hKn⟩
    · exfalso
      have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLN hxM
      refine h.hne (hKx.trans ?_)
      exact conjSubgroup_eq_iff_mem_normalizer.mpr hxN
    · exact hKn
  have hTN : D.T ≤ Subgroup.normalizer (J : Set G) := by
    rcases hJeq with hJL | hJK
    · rw [hJL]
      exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLN)
    · rw [hJK]
      exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKn)
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hJalt : IsAlt (Bar2 J) 5 := by
    rcases hJeq with hJL | hJK
    · rw [hJL]
      rcases h.shape with hL2 | hU3
      · exact CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL2
      · exact absurd (Or.inr ⟨hJL, hU3⟩) hJ5
    · rw [hJK]
      exact h.hKshape
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg
      (CFSG.Quasithin.E3.isElemAbelian_conjSubgroup
        h.hyp.hyp125.pairFacts.elemAbelian₀ g)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have hcomm : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  let JT : Subgroup G := J ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 JT
  change E3.mQuot A (A ⊓ Q) ≤ 2
  have hJTN : JT ≤ Subgroup.normalizer (J : Set G) := sup_le le_normalizer hTN
  have hφker : ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL J).comp
      (Subgroup.inclusion hJTN)).ker = Q.subgroupOf JT :=
    ker_rhoL_sup_eq_pCoreOf rfl hJalt hT2 hJTN
  let φ : ↥JT →* MulAut (Bar2 J) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL J).comp (Subgroup.inclusion hJTN)
  have hQsubEq : Q.subgroupOf JT = CFSG.pCore 2 ↥JT :=
    CFSG.openPCoreOf_subgroupOf 2 JT
  have hQker : CFSG.pCore 2 ↥JT ≤ φ.ker := by
    rw [hφker]
    intro x hx
    exact Subgroup.mem_map_of_mem JT.subtype hx
  have hCQ : φ.ker ≤ CFSG.pCore 2 ↥JT := by
    rw [hφker, hQsubEq]
  let Ψ : (↥JT ⧸ CFSG.pCore 2 ↥JT) →* MulAut (Bar2 J) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥JT) φ hQker
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hφab : φ a = φ b := by
      have h1 : Ψ (QuotientGroup.mk a) = Ψ (QuotientGroup.mk b) := hxy
      simpa [Ψ, QuotientGroup.lift_mk] using h1
    refine QuotientGroup.eq.mpr ?_
    have hmem : a⁻¹ * b ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφab, inv_mul_cancel]
    exact hCQ hmem
  have hpRankAut : CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut (Bar2 J))) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num) ?_
    intro E _ hEab
    obtain ⟨e5⟩ := hJalt
    let e : MulAut (Bar2 J) ≃* Equiv.Perm (Fin 5) :=
      (MulAut.congr e5).trans CFSG.Quasithin.L139A5.autA5.symm
    have h4 := CFSG.ComponentClassification.RankTwoAltFive.card_le_four_of_elemAbelian_perm
      (E := E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hEab e.toMonoidHom)
    calc Nat.card E = Nat.card (E.map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ ≤ 4 := h4
      _ = 2 ^ 2 := by norm_num
  have hquotRank :
      CFSG.Open.pRank 2 (⊤ : Subgroup (↥JT ⧸ CFSG.pCore 2 ↥JT)) ≤ 2 := by
    have h1 := CFSG.Quasithin.E3.pRank_le_pRank_map Ψ hΨinj (p := 2) Nat.prime_two
      (⊤ : Subgroup (↥JT ⧸ CFSG.pCore 2 ↥JT))
    have h2 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num : 1 < 2)
      (H := Ψ.range) (K := ⊤) le_top
    calc CFSG.Open.pRank 2 (⊤ : Subgroup (↥JT ⧸ CFSG.pCore 2 ↥JT))
        ≤ CFSG.Open.pRank 2 ((⊤ : Subgroup (↥JT ⧸ CFSG.pCore 2 ↥JT)).map Ψ) := h1
      _ = CFSG.Open.pRank 2 Ψ.range := by rw [Subgroup.map_top]
      _ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (MulAut (Bar2 J))) := h2
      _ ≤ 2 := hpRankAut
  exact (CFSG.Quasithin.RonanE42.mQuot_inf_pCoreOf_le (K := JT) (B := A)
    (hAT.trans le_sup_right) hAel.2 hAc).trans hquotRank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
