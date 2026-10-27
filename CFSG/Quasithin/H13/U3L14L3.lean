module

public import CFSG.Quasithin.H13.U3L14Kp
public import CFSG.Quasithin.H13.U3L14Aut
public import CFSG.Quasithin.H13.FiveMenu
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.U3L14G

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_subgroupOf_eq (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem exists_odd : ∃ x ∈ Lp, Odd (orderOf x) ∧ x ≠ 1 := by
  by_contra h
  push Not at h
  have hle : Lp ≤ pCoreOf 2 Lp := by
    rw [S.Lp_eq]
    refine (closure_le _).2 fun x hx => ?_
    rw [h x hx.1 hx.2]
    exact one_mem _
  have h3 := S.Lp3
  rw [relIndex_eq_one.mpr hle] at h3
  exact absurd h3 (by norm_num)

theorem pCoreOf_K_le {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) : pCoreOf 2 K ≤ T ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : K ⊔ T ≤ normalizer (pCoreOf 2 K : Set G) :=
    sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hD.T_K.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) hKn
      (LieType.BorelTits.pCoreOf_isPGroup 2 K)
  refine le_inf (h1.trans ?_) (LieType.BorelTits.pCoreOf_le 2 K)
  exact pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ K ⊔ T)).2.1
    (S.syl (le_sup_right : T ≤ K ⊔ T)).2.2

theorem sylowImage {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) :
    IsPGroup 2 (((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))) ∧
      ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map
        (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_of_le_normalizer (S.syl (le_sup_right : T ≤ K ⊔ T)) le_sup_left
      (sup_le le_normalizer hD.T_K)
  refine ⟨IsPGroup.map (hsyl.2.1.of_equiv (subgroupOfEquivOfLe hsyl.1).symm) _, ?_⟩
  have hker : (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)).ker ≤ (T ⊓ K).subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact S.pCoreOf_K_le hD hy
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective ((pCoreOf 2 K).subgroupOf K)) hker]
  exact hsyl.2.2

theorem not_L32 {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    (h : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hxo, hx1⟩ := S.exists_odd
  have hx3 : x ^ 3 = 1 := S.odd_pow_three hx hxo
  set α := kAct K ⟨x, hD.Lp_K hx⟩ with hα
  have hα1 : α ≠ 1 := S.kAct_ne_one hD hx hxo hx1
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨x, hD.Lp_K hx⟩ : ↥(normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  set π := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hπ
  set P := ((T ⊓ K).subgroupOf K).map π with hP
  obtain ⟨hP2, hPi⟩ := S.sylowImage hD
  have hxTK := S.mem_normalizer_inf_K hD hg hx
  have hαP : P.map α.toMonoidHom = P := by
    have hle : P.map α.toMonoidHom ≤ P := by
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨⟨x * t * x⁻¹, (mem_normalizer_iff.mp (hD.Lp_K hx) t).mp t.2⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf] at ht ⊢
        exact (mem_normalizer_iff.mp hxTK t).mp ht
      · show π ⟨x * t * x⁻¹, _⟩ = α (π t)
        rw [hα, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          CFSG.SignalizerFunctorTheorem.sectionAction_mk]
        congr 1
        exact Subtype.ext (CFSG.SignalizerFunctorTheorem.coe_sectionConjAut _
          (⟨x, hD.Lp_K hx⟩ : ↥(normalizer (K : Set G))) t).symm
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    exact (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).symm.le
  obtain ⟨e₀⟩ := nonempty_mulEquiv_sl_two_of_lieModel h
  let e : (↥K ⧸ (pCoreOf 2 K).subgroupOf K) ≃* GL (Fin 3) (ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_eq K)).trans e₀).trans
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3)
  set α' := MulAut.congr e α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα3, map_one]
  have hP'2 : IsPGroup 2 (P.map e.toMonoidHom) := hP2.map _
  have hP'i : ¬ 2 ∣ (P.map e.toMonoidHom).index := by
    rw [show e.toMonoidHom = (e : _ →* _) from rfl, index_map_equiv]
    exact hPi
  have hα'P : (P.map e.toMonoidHom).map α'.toMonoidHom = P.map e.toMonoidHom := by
    rw [map_map]
    conv_rhs => rw [← hαP, map_map]
    congr 1
    ext p
    simp [hα', MulAut.congr_apply]
  have h1 := mulAut_gl32_eq_one hα'3 hP'2 hP'i hα'P
  apply hα1
  have : α = (MulAut.congr e).symm α' := by rw [hα', MulEquiv.symm_apply_apply]
  rw [this, h1, map_one]

end Set14

end CFSG.Quasithin.H13.U3
