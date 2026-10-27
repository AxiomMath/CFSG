module

public import CFSG.LocalAnalysis.StandardType.GGSporKStepBFour
public import CFSG.LocalAnalysis.StandardType.GGSporKBSevenOrd
public import CFSG.LocalAnalysis.StandardType.GGSporKStepZero
public import CFSG.LocalAnalysis.StandardType.GGSporKStepOne
public import CFSG.LocalAnalysis.StandardType.GGSporKB7a3
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZDefs
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

private theorem gk7_isComponentOf_map_equiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    {K C : Subgroup G} (h : IsComponentOf K C) :
    IsComponentOf (K.map φ.toMonoidHom) (C.map φ.toMonoidHom) := by
  have h' := CFSG.Assembly.isComponentOf_iff_open.mp h
  exact CFSG.Assembly.isComponentOf_iff_open.mpr
    (CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv φ h')

theorem ggSporK_E_le_layer_B {W : Type} [Group W] [Finite W] (hOrd : BSevenOrd W)
    (h49 : (Nat.card W).factorization 7 = 2) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat 7 H E) {L : Subgroup W} (hLH : L ≤ H) (hLs : IsSimpleGroup ↥L)
    (hmark : StandardType.LargeEvenMarking ↥L (fun _ _ _ _ _ _ => True))
    (hcent : H ⊓ Subgroup.centralizer (L : Set W) = ⊥)
    (hnorm : H ≤ Subgroup.normalizer (L : Set W)) : E ≤ L := by
  have hp : Nat.Prime 7 := by norm_num
  have hE7 : IsElemAbelian 7 E := hyp.1.2.2.1
  have hEcard : Nat.card E = 7 ^ 2 := hyp.1.2.2.2.1
  have hEH : E ≤ H := hyp.1.2.2.2.2.1
  let f : ↥H →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hact : ∀ (h : ↥H) (x : ↥L), (((f h) x : ↥L) : W) = (h : W) * (x : W) * (h : W)⁻¹ :=
    fun _ _ => rfl
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have hc : (h : W) ∈ Subgroup.centralizer (L : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hact h ⟨x, hx⟩
      rw [hh] at h1
      have h2' : x = (h : W) * x * (h : W)⁻¹ := h1
      calc x * (h : W) = (h : W) * x * (h : W)⁻¹ * (h : W) := by rw [← h2']
        _ = (h : W) * x := by group
    have hmem : (h : W) ∈ H ⊓ Subgroup.centralizer (L : Set W) := ⟨h.2, hc⟩
    rw [hcent, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hdvdAut : Nat.card ↥H ∣ Nat.card (MulAut ↥L) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hH49 : 7 ^ 2 ∣ Nat.card ↥H := hEcard ▸ Subgroup.card_dvd_of_le hEH
  have hHW : Nat.card ↥H ∣ Nat.card W := Subgroup.card_subgroup_dvd_card H
  have hLW : Nat.card ↥L ∣ Nat.card W := Subgroup.card_subgroup_dvd_card L
  haveI : Finite (MulAut ↥L) :=
    Finite.of_injective (fun φ : MulAut ↥L => (φ : ↥L → ↥L)) DFunLike.coe_injective
  have hAutne : Nat.card (MulAut ↥L) ≠ 0 := Nat.card_pos.ne'
  have hAut2 : 2 ≤ (Nat.card (MulAut ↥L)).factorization 7 :=
    (hp.pow_dvd_iff_le_factorization hAutne).mp (hH49.trans hdvdAut)
  have hL2 : 2 ≤ (Nat.card ↥L).factorization 7 := hAut2.trans (hOrd L hLs hmark)
  have hLne : Nat.card ↥L ≠ 0 := Nat.card_pos.ne'
  have hWne : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have hHne : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have hLle : (Nat.card ↥L).factorization 7 ≤ 2 := by
    rw [← h49]; exact (Nat.factorization_le_iff_dvd hLne hWne).mpr hLW 7
  have hLeq : (Nat.card ↥L).factorization 7 = 2 := le_antisymm hLle hL2
  have hHle : (Nat.card ↥H).factorization 7 ≤ 2 := by
    rw [← h49]; exact (Nat.factorization_le_iff_dvd hHne hWne).mpr hHW 7
  have hHeq : (Nat.card ↥H).factorization 7 = 2 :=
    le_antisymm hHle ((hp.pow_dvd_iff_le_factorization hHne).mp hH49)
  set N : Subgroup ↥H := L.subgroupOf H with hN
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hnorm
  have hNcard : Nat.card ↥N = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv
  have hidx : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul : Nat.card ↥N * N.index = Nat.card ↥H := Subgroup.card_mul_index N
  have h7idx : ¬ 7 ∣ N.index := by
    intro hd
    have h1 : 0 < N.index.factorization 7 := hp.factorization_pos_of_dvd hidx hd
    have h2 : (Nat.card ↥H).factorization 7 =
        (Nat.card ↥N).factorization 7 + N.index.factorization 7 := by
      rw [← hmul, Nat.factorization_mul (by rw [hNcard]; exact hLne) hidx, Finsupp.add_apply]
    rw [hHeq, hNcard, hLeq] at h2
    omega
  intro x hx
  have hxH : x ∈ H := hEH hx
  have hq : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) ^ 7 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 7 = 1 := Subtype.ext (hE7.2 x hx)
    rw [this]
    exact QuotientGroup.mk_one _
  have hord1 : orderOf (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) ∣ 7 :=
    orderOf_dvd_of_pow_eq_one hq
  have hord2 : orderOf (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) ∣ N.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hone : orderOf (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) = 1 := by
    rcases (Nat.dvd_prime hp).mp hord1 with h | h
    · exact h
    · rw [h] at hord2
      exact absurd hord2 h7idx
  have hmem : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ N) = 1 := orderOf_eq_one_iff.mp hone
  have hxN : (⟨x, hxH⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).mp hmem
  exact Subgroup.mem_subgroupOf.mp hxN

theorem ggSporK_false_of_E_le_layer_B {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hb : BSevenCentAbelian W) (hLie : LieSevenOddCentre7sq W) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat 7 H E) {L : Subgroup W} (hLH : L ≤ H) (hLs : IsSimpleGroup ↥L)
    (hmark : StandardType.LargeEvenMarking ↥L (fun _ _ _ _ _ _ => True))
    (hnorm : H ≤ Subgroup.normalizer (L : Set W)) (hEL : E ≤ L) : False := by
  have hE7 : IsElemAbelian 7 E := hyp.1.2.2.1
  have hEcard : Nat.card E = 7 ^ 2 := hyp.1.2.2.2.1
  have hfus : GGControlsStrongFusion H E := hyp.1.2.2.2.2
  have hEH : E ≤ H := hfus.1
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hEcard49 : Nat.card E = 49 := by rw [hEcard]; norm_num
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hEcard
    omega
  obtain ⟨⟨e, heE⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have he7 : orderOf e = 7 := orderOf_eq_prime (hE7.2 e heE) he1'
  have hy : ∃ y ∈ E, y ∉ Subgroup.zpowers e := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers e := fun y hy => hcon y hy
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, he7, hEcard] at this
    omega
  obtain ⟨y, hyE, hyx⟩ := hy
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hy7 : orderOf y = 7 := orderOf_eq_prime (hE7.2 y hyE) hy1
  obtain ⟨J, hJ, hJuniq, hJz, -⟩ := ha e he7
  have hCH : Subgroup.centralizer {e} ≤ H := hfus.centralizer_le heE he1'
  have hNn : ∀ c ∈ Subgroup.centralizer ({e} : Set W), ∀ n ∈ L ⊓ Subgroup.centralizer {e},
      c * n * c⁻¹ ∈ L ⊓ Subgroup.centralizer {e} := by
    intro c hc n hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hnorm (hCH hc)) n).mp (Subgroup.mem_inf.mp hn).1
      simpa using this
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (Subgroup.mem_inf.mp hn).2)
        (Subgroup.inv_mem _ hc)
  have hyC : y ∈ Subgroup.centralizer ({e} : Set W) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact congrArg Subtype.val (hE7.1.is_comm.comm ⟨e, heE⟩ ⟨y, hyE⟩)
  have hyN : y ∈ L ⊓ Subgroup.centralizer {e} := Subgroup.mem_inf.mpr ⟨hEL hyE, hyC⟩
  have hJn : ∀ c ∈ Subgroup.centralizer ({e} : Set W), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    have hcomp := gk7_isComponentOf_map_equiv (MulAut.conj c) hJ
    have hmap : (Subgroup.centralizer ({e} : Set W)).map (MulAut.conj c).toMonoidHom =
        Subgroup.centralizer ({e} : Set W) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hw) (Subgroup.inv_mem _ hc)
      · intro hz
        refine ⟨c⁻¹ * z * c, ?_, ?_⟩
        · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hz) hc
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
    rw [hmap] at hcomp
    have hEq := hJuniq _ hcomp
    have hmem : c * j * c⁻¹ ∈ J.map (MulAut.conj c).toMonoidHom := ⟨j, hj, by simp⟩
    rwa [hEq] at hmem
  have hJN : J ≤ L ⊓ Subgroup.centralizer {e} :=
    ggSporK_B7a3 hb hE7 hEcard49 heE he7 hJ hJn inf_le_right hNn hyE hyN hyx
  have hJL : IsComponentOf J (L ⊓ Subgroup.centralizer {e}) :=
    IsComponentOf.of_le_of_le hJ hJN inf_le_right
  have h7sq : 7 ^ 2 ∣ Nat.card ↥L := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hEL
  have hodd := hLie L hLs hmark h7sq e (hEL heE) he7 J hJL
  rw [hJz] at hodd
  exact absurd hodd (by decide)

theorem ggSporK_false_of_inputsB_W {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hb : BSevenCentAbelian W) (hc : BSevenSpread W) (hOrd : BSevenOrd W)
    (hLie : LieSevenOddCentre7sq W) (h49 : (Nat.card W).factorization 7 = 2) (H E : Subgroup W)
    (hyp : GGHypThreeSixteenFlat 7 H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) : False := by
  have hP' : LargeEvenPPrimeCore 7 ↥H = ⊥ := ggSporK_pPrimeCore_eq_bot_B ha hc hyp
  have h2 : CFSG.pCore 2 ↥H = ⊥ := ggSporK_pCore_two_eq_bot hyp.1.1 hyp.1.2.1 hP'
  have hJ : ∃ J : Subgroup W, IsComponentOf J H := ggSporK_exists_component h2 hL
  have hP : CFSG.pCore 7 ↥H = ⊥ := ggSporK_pCore_eq_bot_B ha h49 hyp hP' hJ
  obtain ⟨L, hLc, hLs, -, hcent, hnorm⟩ := ggSporK_layer_simple_B ha hb h49 hyp hP' hP hJ
  obtain ⟨-, hmark⟩ := ggSporK_component_data hyp h2 hLc
  exact ggSporK_false_of_E_le_layer_B ha hb hLie hyp hLc.1 hLs hmark hnorm
    (ggSporK_E_le_layer_B hOrd h49 hyp hLc.1 hLs hmark hcent hnorm)

end CFSG.StandardType.SporadicShape
