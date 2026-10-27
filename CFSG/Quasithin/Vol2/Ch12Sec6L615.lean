module

public import CFSG.Quasithin.Vol2.Ch12Sec6L69
public import CFSG.Quasithin.Vol2.Ch12Sec6L45

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G]

theorem isElemAbelian_Usec (Kv S : Subgroup G) : IsElemAbelian 2 (Usec Kv S) :=
  B2F.isElemAbelian_closure (fun _ ha _ hb => (Subgroup.mem_centralizer_iff.1 ha.1.2 _ hb.1.1).symm)
    fun _ ha => ha.2

theorem Usec_le (Kv S : Subgroup G) : Usec Kv S ≤ pCoreOf 2 (Kv ⊔ S) :=
  (Subgroup.closure_le _).2 fun _ hz => hz.1.1

theorem normalizer_le_normalizer_Usec (Kv S : Subgroup G) :
    Subgroup.normalizer (pCoreOf 2 (Kv ⊔ S) : Set G) ≤
      Subgroup.normalizer (Usec Kv S : Set G) := by
  set P := pCoreOf 2 (Kv ⊔ S) with hP
  have key : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ x ∈ Usec Kv S, g * x * g⁻¹ ∈ Usec Kv S := by
    intro g hg x hx
    have hle : Usec Kv S ≤ (Usec Kv S).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      obtain ⟨⟨hzP, hzC⟩, hz2⟩ := hz
      show (MulAut.conj g) z ∈ Usec Kv S
      rw [MulAut.conj_apply]
      apply Subgroup.subset_closure
      refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzP, ?_⟩, ?_⟩
      · show g * z * g⁻¹ ∈ Subgroup.centralizer (P : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have hs : g⁻¹ * t * g ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) t).mp ht
          simpa using this
        have hzs := (Subgroup.mem_centralizer_iff.mp hzC) _ hs
        calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hzs]
          _ = g * z * g⁻¹ * t := by group
      · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

end S126T2

theorem lemma12_6_15_of (h1222 : Stmt12_2_2) (hD3 : Lemma12_6_6_9) (hD7 : Lemma12_6_13)
    (hD8 : Lemma12_6_14) : Lemma12_6_15 := by
  intro G _ _ T L V _ F v Kv S hC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hS := hC.sylow
  have hTvS := hC.tv_le
  set P := pCoreOf 2 (Kv ⊔ S) with hP
  have hU := isElemAbelian_Usec Kv S
  refine ⟨hU, ?_⟩
  obtain ⟨hJT, hLvJ⟩ := (hD3 G T L V F v Kv S hC).2.2.2.2 (hD8 G T L V F v Kv S hC)
  obtain ⟨A₁, hA₁, hA₁Tv⟩ := exists_max_le_Tv h1222 F hH hv hβ hJT
  have hTsyl := isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow (le_top : T ≤ ⊤)
  have hA₁top := B6.isMaxElemAbelian_of_sylow hTsyl hA₁
  have hsubS : ∀ A : Subgroup G, IsMaxElemAbelian (Tv T v) A → IsMaxElemAbelian S A :=
    fun A hA => ⟨hA.1.trans hTvS, hA.2.1, fun B _ hBe =>
      (hA₁top.2.2 B le_top hBe).trans (hA.2.2 _ hA₁Tv hA₁.2.1)⟩
  have hKG : Kv ≤ Gv v := by
    rw [hC.kv_eq]
    exact (Subgroup.closure_le _).2 fun x hx => perfectCore_le _ hx.1
  have hSKS := isSylowTwoOf_of_le_of_le hS (le_sup_right : S ≤ Kv ⊔ S) (sup_le hKG hS.1)
  have hKSP : Kv ⊔ S ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 _
  have hPS : P ≤ S := hSKS.le_of_normalizes (pCoreOf_le 2 _) hKSP (pCoreOf_isPGroup 2 _)
  have hUS : Usec Kv S ≤ S := (Usec_le Kv S).trans hPS
  have hKSU : Kv ⊔ S ≤ Subgroup.normalizer (Usec Kv S : Set G) :=
    hKSP.trans (normalizer_le_normalizer_Usec Kv S)
  have hCU : (Kv ⊔ S) ⊓ Subgroup.centralizer (Usec Kv S : Set G) = P :=
    (hD7 G T L V F v Kv S hC).1.2.symm
  obtain ⟨A, hA, hAU⟩ : ∃ A : Subgroup G, IsMaxElemAbelian (Tv T v) A ∧
      ¬ A ≤ Subgroup.centralizer (Usec Kv S : Set G) := by
    by_contra h
    push Not at h
    have hJP : thompsonJ (Tv T v) ≤ P := by
      rw [← hCU]
      exact le_inf ((B6.thompsonJ_le _).trans (hTvS.trans le_sup_right))
        (iSup₂_le fun A hA => h A hA)
    have hle : ⁅Lv L v, thompsonJ (Tv T v)⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      rw [commutatorElement_def]
      have hlKS : l ∈ Kv ⊔ S := le_sup_left (b := S) (hC.lv_le hl)
      have h1 : l * j * l⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hKSP hlKS) j).1 (hJP hj)
      exact P.mul_mem h1 (P.inv_mem (hJP hj))
    exact Lv_not_le (P := P) h1222 F hH hv hβ (pCoreOf_isPGroup 2 _) (hLvJ.le.trans hle)
  have hAS := hsubS A hA
  have hcard := card_le_relIndex_mul_card hU hUS hAS
  have hAKS : A ≤ Kv ⊔ S := hAS.1.trans le_sup_right
  have hAN : A ≤ Subgroup.normalizer (Usec Kv S : Set G) := hAKS.trans hKSU
  refine ⟨autI hU A, autI_mono hU hAKS, (autI_eq_bot_iff hU hAN).not.2 hAU,
    isElemAbelian2_autI hU hA.2.1 hAN, ?_⟩
  rw [card_autI_eq hU hAN, card_fixV_autI hU hAN]
  exact hcard

end CFSG.Quasithin.H13
