module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.PCore.SubgroupCore

public noncomputable section

namespace CFSG.StandardType.QTwoOrthogonalCav

open CFSG.Assembly CFSG.RankThree.Classical2 Module CFSG.GroupTheory.WeirSylow

private theorem beta_inner_trans
    {G : Type} [Group G] {Bs L : Subgroup G} {R R' : Type} [Group R] [Group R']
    (θ : L ⧸ Subgroup.center L ≃* R) (e : R ≃* R')
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinner : (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range) :
    (ggBeta L (θ.trans e) hN).range ≤ (MulAut.conj : R' →* MulAut R').range := by
  rintro φ ⟨b, rfl⟩
  have h := congrArg (fun f : Bs →* MulAut R' => f b) (QTwoCav.beta_trans θ e hN)
  change MulAut.congr e (ggBeta L θ hN b) = ggBeta L (θ.trans e) hN b at h
  rw [← h]
  obtain ⟨q, hq⟩ := hinner ⟨b, rfl⟩
  rw [← hq]
  refine ⟨e q, ?_⟩
  ext z
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem exists_orthogonal_marking
    {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G} {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo p lab) (htag : lab.tag = .D ∨ lab.tag = .twD) (hr : 4 ≤ lab.rank)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V), Nat.card K = 2 ∧
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ finrank K V = 2 * lab.rank ∧
        (IsPlusType Q ↔ lab.tag = .D) ∧
        (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* ↥(orthDerived Q),
          Subgroup.center ↥(orthDerived Q) = ⊥ ∧
            (ggBeta L θ hN).range ≤
              (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)).range := by
  obtain ⟨hL, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, hGroup₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab' = lab := hP₀.1
  subst lab'
  have hn : lab.n = 1 := by
    have h1 := hlab'.1
    change lab.n < 2 at hq2
    omega
  rcases htag with hD | hD
  · have hr3 : lab.rank ≠ 3 := by omega
    simp only [LargeEvenRawDatumLegacy, LargeEvenRawDatum, hD, ite_eq_right hr3] at hraw
    obtain ⟨K, hField, hFinite, hcard, hs, hna, θ, hP⟩ := hraw
    letI : Field K := hField
    letI : Finite K := hFinite
    have hK : Nat.card K = 2 := by simpa only [hn, pow_one] using hcard
    letI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
      (f := 1) (by simpa using hK)
    let Q := TableBOrth.qPlusForm K lab.rank
    let e := OrthTorus.rPlusEquiv K (show 1 ≤ lab.rank by omega)
    letI : IsSimpleGroup (OrthRest.RPlus K lab.rank) := hs
    have hZ : Subgroup.center (OrthRest.RPlus K lab.rank) = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative (by
        intro h
        obtain ⟨a, b, hab⟩ := hna
        exact hab (h.is_comm.comm a b))
    have hZ' : Subgroup.center ↥(orthDerived Q) = ⊥ := by
      have he := Subgroup.map_center_eq e
      rw [hZ, Subgroup.map_bot] at he
      exact he.symm
    have hinner : (ggBeta L θ hN).range ≤
        (MulAut.conj : OrthRest.RPlus K lab.rank →* MulAut _).range := by
      rintro φ ⟨b, rfl⟩
      exact ggLAut_mem_of_induces L θ hN hP.2.2 b.property
    have hdim : finrank K (Fin lab.rank ⊕ Fin lab.rank → K) = 2 * lab.rank := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have htype : IsPlusType Q ↔ lab.tag = .D := by
      refine ⟨fun _ => hD, fun _ => ?_⟩
      exact isPlusType_quadPlus K lab.rank
    have hT : ∃ T : Submodule K (Fin lab.rank ⊕ Fin lab.rank → K),
        finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 := by
      change ∃ T : Submodule K (Fin lab.rank ⊕ Fin lab.rank → K),
        finrank K T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm K lab.rank v = 0
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ lab.rank)]
      exact OrthTorus.exists_totallySingular_qPlusForm (K := K) (n := lab.rank - 1)
        (by omega : 3 ≤ lab.rank - 1)
    exact ⟨K, hField, hFinite, inferInstance, Fin lab.rank ⊕ Fin lab.rank → K,
      inferInstance, inferInstance, inferInstance, Q, hK,
      TableBOrth.nondegenerate_qPlusForm lab.rank, hdim, htype, hT, θ.trans e, hZ',
      beta_inner_trans θ e hN hinner⟩
  · have hr2 : lab.rank ≠ 2 := by omega
    have hr3 : lab.rank ≠ 3 := by omega
    simp only [LargeEvenRawDatumLegacy, LargeEvenRawDatum, hD, ite_eq_right hr2,
      ite_eq_right hr3] at hraw
    obtain ⟨K, hField, hFinite, hcard, b, c, hbc, hs, hna, θ, hP⟩ := hraw
    letI : Field K := hField
    letI : Finite K := hFinite
    have hK : Nat.card K = 2 := by simpa only [hn, pow_one] using hcard
    letI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
      (f := 1) (by simpa using hK)
    let Q := TableBOrth.qMinusForm K (lab.rank - 1) b c
    let e := OrthTorus.rMinusEquiv K (lab.rank - 1) b c
    letI : IsSimpleGroup (OrthRest.RMinus K (lab.rank - 1) b c) := hs
    have hZ : Subgroup.center (OrthRest.RMinus K (lab.rank - 1) b c) = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative (by
        intro h
        obtain ⟨a, b, hab⟩ := hna
        exact hab (h.is_comm.comm a b))
    have hZ' : Subgroup.center ↥(orthDerived Q) = ⊥ := by
      have he := Subgroup.map_center_eq e
      rw [hZ, Subgroup.map_bot] at he
      exact he.symm
    have hinner : (ggBeta L θ hN).range ≤
        (MulAut.conj : OrthRest.RMinus K (lab.rank - 1) b c →* MulAut _).range := by
      rintro φ ⟨a, rfl⟩
      exact ggLAut_mem_of_induces L θ hN hP.2.2 a.property
    have hdim : finrank K (LargeEvenMinusIdx (lab.rank - 1) → K) = 2 * lab.rank := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    have hnot : ¬ IsPlusType Q := by
      intro hp
      exact not_isPlusType_quadMinus (n := (lab.rank - 1) + 1) (by omega) hbc
        ((isPlusType_congr (TableBOrth.qMinusIsometry (lab.rank - 1) b c)).mp hp)
    have htype : IsPlusType Q ↔ lab.tag = .D := by
      refine ⟨fun hp => absurd hp hnot, fun hD' => ?_⟩
      exact absurd hD' (by rw [hD]; decide)
    have hT : ∃ T : Submodule K (LargeEvenMinusIdx (lab.rank - 1) → K),
        finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
      (OrthTorus.charSum_qMinusForm (lab.rank - 1) hbc).2 (by omega)
    exact ⟨K, hField, hFinite, inferInstance, LargeEvenMinusIdx (lab.rank - 1) → K,
      inferInstance, inferInstance, inferInstance, Q, hK,
      TableBOrth.nondegenerate_qMinusForm (lab.rank - 1) hbc, hdim, htype, hT, θ.trans e,
      hZ', beta_inner_trans θ e hN hinner⟩

theorem exists_orthogonal_original_realization
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G} {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo p lab)
    (htag : (lab.tag = .D ∧ 5 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V), Nat.card K = 2 ∧
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ finrank K V = 2 * lab.rank ∧
        (IsPlusType Q ↔ lab.tag = .D) ∧
        (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) ∧
        Subgroup.center ↥L = ⊥ ∧
        ∃ (θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(orthDerived Q))
          (e : ↥L ≃* ↥(orthDerived Q)),
          (∀ z : ↥L, e z = θ (QuotientGroup.mk z)) ∧
          (ggBeta L θ hN).range ≤
            (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)).range := by
  obtain ⟨lab₀, hlab₀, hHas₀, R, hR, I, F, θ₀, hP₀⟩ := largeEvenMarking_exists_hasLabel hmark
  have hlab : lab₀ = lab := hP₀.1
  subst lab₀
  have hn : lab.n = 1 := by
    have h1 := hlab₀.1
    change lab.n < 2 at hq2
    omega
  haveI : Finite ↥L := inferInstance
  haveI : Group.IsPerfect ↥L := ⟨hmark.1⟩
  have hZ : Subgroup.center ↥L = ⊥ :=
    OrthTorus.center_eq_bot_of_hasLabel_orth_two htag hn hHas₀
  have htag' : lab.tag = .D ∨ lab.tag = .twD := by
    rcases htag with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hr : 4 ≤ lab.rank := by
    rcases htag with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim,
    htype, hT, θ, hZQ, hinner⟩ := exists_orthogonal_marking hq2 htag' hr hmark hN
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module K V := hMod
  letI : FiniteDimensional K V := hFinDim
  let qe : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e : ↥L ≃* ↥(orthDerived Q) := qe.symm.trans θ
  have he : ∀ z : ↥L, e z = θ (QuotientGroup.mk z) := by
    intro z
    change θ (qe.symm z) = θ (QuotientGroup.mk z)
    congr 1
  exact ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim,
    htype, hT, hZ, θ, e, he, hinner⟩

theorem exists_orthogonal_full_image
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .D ∨ lab.tag = .twD) (hr : 4 ≤ lab.rank)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V), Nat.card K = 2 ∧
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ finrank K V = 2 * lab.rank ∧
        ∃ (θ : L ⧸ Subgroup.center L ≃* ↥(orthDerived Q))
          (E : Subgroup ↥(orthDerived Q)),
          Subgroup.center ↥(orthDerived Q) = ⊥ ∧ CFSG.Open.IsElemAbelian 3 E ∧
            Nat.card E = 3 ^ lab.rank ∧
            E.map (MulAut.conj : ↥(orthDerived Q) →* MulAut _) = (ggBeta L θ hN).range := by
  obtain ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim, -,
    -, θ, hZ, hinner⟩ := exists_orthogonal_marking hq2 htag hr hmark hN
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module K V := hMod
  letI : FiniteDimensional K V := hFinDim
  have hconj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  let E := (ggBeta L θ hN).range.comap (MulAut.conj : ↥(orthDerived Q) →* MulAut _)
  have hmap : E.map (MulAut.conj : ↥(orthDerived Q) →* MulAut _) =
      (ggBeta L θ hN).range := Subgroup.map_comap_eq_self hinner
  let eE : E ≃* (ggBeta L θ hN).range :=
    (Subgroup.equivMapOfInjective E (MulAut.conj : ↥(orthDerived Q) →* MulAut _) hconj).trans
      (MulEquiv.subgroupCongr hmap)
  have hβ := QTwoCav.beta_image_of_index hS.1.1.2.1.2.1 hS.2.1.1 θ hN hidx
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv eE.symm hβ.1.isElementaryAbelian)
  have hcardE : Nat.card E = 3 ^ lab.rank := (Nat.card_congr eE.toEquiv).trans hβ.2
  exact ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim,
    θ, E, hZ, hE, hcardE, hmap⟩

theorem exists_orthogonal_full_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .D ∨ lab.tag = .twD) (hr : 4 ≤ lab.rank)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (Q : QuadraticForm K V), Nat.card K = 2 ∧
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ finrank K V = 2 * lab.rank ∧
        ∃ (θ : L ⧸ Subgroup.center L ≃* ↥(orthDerived Q))
          (E : Subgroup ↥(orthDerived Q)) (t : ↥(orthDerived Q)),
          Subgroup.center ↥(orthDerived Q) = ⊥ ∧ CFSG.Open.IsElemAbelian 3 E ∧
            Nat.card E = 3 ^ lab.rank ∧
            E.map (MulAut.conj : ↥(orthDerived Q) →* MulAut _) = (ggBeta L θ hN).range ∧
            t ∈ E ∧ t ^ 3 = 1 ∧ t ≠ 1 ∧ orderOf t = 3 ∧
            IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
              (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))) := by
  obtain ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim,
    θ, E, hZ, hE, hcardE, hmap⟩ := exists_orthogonal_full_image hS hq2 htag hr hmark hidx hN
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module K V := hMod
  letI : FiniteDimensional K V := hFinDim
  obtain ⟨d, hd1, -, hcommon⟩ := QTwoCav.exists_beta_d_generator θ Nat.prime_three hS hN
  have hDBs : D ≤ Bs := hS.1.1.2.2.1.1.trans hS.1.1.2.1.1
  have hle := range_ggBeta_le θ hDBs (QTwoCav.d_le_normalizer hS hN) hN
  have hdIn : ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d ∈ (ggBeta L θ hN).range :=
    hle ⟨d, rfl⟩
  obtain ⟨t, htE, ht⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hdIn)
  have ht3 : t ^ 3 = 1 := hE.2 t htE
  have ht1 : t ≠ 1 := by
    intro h1
    apply hd1
    rw [← ht, h1, map_one]
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hfix : ggFix (MulAut.conj t) = Subgroup.centralizer ({t} : Set ↥(orthDerived Q)) := by
    ext z
    rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro hz
      have hcomm : t * z = z * t := mul_inv_eq_iff_eq_mul.mp hz
      exact hcomm.symm
    · intro hz
      exact mul_inv_eq_iff_eq_mul.mpr hz.symm
  have hJ := QTwoCav.isComponentOf_quotient_image (QTwoCav.d_le_normalizer hS hN) θ
    hS.1.1.2.2.1.2.2.2.2.2.1
  rw [hcommon, ← ht, hfix] at hJ
  exact ⟨K, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, Q, hK, hQ, hdim,
    θ, E, t, hZ, hE, hcardE, hmap, htE, ht3, ht1, horder, hJ⟩

theorem card_automizer_eq_original_image
    {G : Type} [Group G] {Bs L J : Subgroup G} {R : Type} [Group R]
    (hL : commutator L = ⊤) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* R) (hZ : Subgroup.center R = ⊥)
    {E : Subgroup R} (hE : E.map (MulAut.conj : R →* MulAut R) = (ggBeta L θ hN).range) :
    Nat.card (ggAutomizer ((J.subgroupOf L).map (ggQuotHom θ)) E) =
      Nat.card (ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
        (ggGamma L hN).range) := by
  have hf := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hcard : Nat.card (ggAutomizer
      (((J.subgroupOf L).map (ggQuotHom θ)).map (MulAut.conj : R →* MulAut R))
      (ggBeta L θ hN).range) = Nat.card (ggAutomizer ((J.subgroupOf L).map (ggQuotHom θ)) E) := by
    rw [F4AutWeyl.ggAutomizer_map_eq hf ((J.subgroupOf L).map (ggQuotHom θ)) E hE,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  exact hcard.symm.trans (QTwoCav.card_automizer_quotient_image_eq (J := J) θ hL hN)

end CFSG.StandardType.QTwoOrthogonalCav

end
