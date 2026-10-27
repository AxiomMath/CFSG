module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListCorrected
public import CFSG.OddTranspositions.PartFour.Thirteen
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Open

theorem closure_setOf_isConj_eq_normalClosure {G : Type*} [Group G] (s : G) :
    Subgroup.closure {x : G | IsConj s x} = Subgroup.normalClosure ({s} : Set G) := by
  rw [Subgroup.normalClosure]
  congr 1
  ext g
  simp [Group.mem_conjugatesOfSet_iff]

theorem setup_setOf_isConj {X : Type*} [Group X] {s : X}
    (hodd : IsOddTransp {x : X | IsConj s x})
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤) : Setup X {x : X | IsConj s x} :=
  ⟨⟨s, rfl⟩, hodd, by rw [closure_setOf_isConj_eq_normalClosure, hncl]⟩

variable {X : Type} [Group X] [Finite X]

theorem mk_ne_one_of_isConj {s : X} (hodd : IsOddTransp {x : X | IsConj s x})
    (hO2 : CFSG.pCore 2 X = ⊥) :
    ∀ d ∈ {x : X | IsConj s x}, QuotientGroup.mk' (Subgroup.center X) d ≠ 1 := by
  intro d hd h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hd2 : orderOf d = 2 := hodd.1 d hd
  have hn : (Subgroup.zpowers d).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr h)
  have hp : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd2, pow_one])
  have hle : Subgroup.zpowers d ≤ CFSG.pCore 2 X := le_sSup ⟨hn, hp⟩
  rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hd2
  exact absurd hd2 (by decide)

theorem setup_quotient_center {s : X} (hodd : IsOddTransp {x : X | IsConj s x})
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤) (hO2 : CFSG.pCore 2 X = ⊥) :
    Setup (X ⧸ Subgroup.center X)
      {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} := by
  have h := (setup_setOf_isConj hodd hncl).map (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (mk_ne_one_of_isConj hodd hO2)
  rw [h.eq_setOf_isConj ⟨s, IsConj.refl s, rfl⟩] at h
  exact h

theorem eq_bot_of_normal_isSolvable_quotient_center (hO2 : CFSG.pCore 2 X = ⊥)
    (hOZ : fusionOddCore X ≤ Subgroup.center X) :
    ∀ N : Subgroup (X ⧸ Subgroup.center X), N.Normal → Group.IsSolvable N → N = ⊥ := by
  intro N hN hNs
  have hR : CFSG.solvableRadical X ≤ Subgroup.center X :=
    otg2_solvableRadical_le_center (by rw [hO2]; exact bot_le) hOZ
  have hZP : Subgroup.center X ≤ N.comap (QuotientGroup.mk' (Subgroup.center X)) :=
    fun z hz => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
      exact N.one_mem
  haveI : Group.IsSolvable ↥(Subgroup.center X) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  haveI : Group.IsSolvable ↥(N.comap (QuotientGroup.mk' (Subgroup.center X))) := by
    refine solvable_of_ker_le_range (Subgroup.inclusion hZP)
      ((QuotientGroup.mk' (Subgroup.center X)).subgroupComap N) fun p hp => ?_
    have hpZ : (p : X) ∈ Subgroup.center X := by
      rw [MonoidHom.mem_ker] at hp
      exact (QuotientGroup.eq_one_iff (p : X)).mp (congrArg Subtype.val hp)
    exact ⟨⟨p, hpZ⟩, rfl⟩
  have hPR : N.comap (QuotientGroup.mk' (Subgroup.center X)) ≤ CFSG.solvableRadical X :=
    le_sSup ⟨hN.comap _, inferInstance⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) x
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hR (hPR hx)

private noncomputable def l2WreathEquivWreathSymTwo (f m : ℕ) :
    L2Wreath f m ≃* WreathSym (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) m :=
  SemidirectProduct.congr
    (MulEquiv.piCongrRight fun _ =>
      CFSG.RankThree.projectiveSpecialLinearTwoEquivSLOfCharTwo (GaloisField 2 f))
    (MulEquiv.refl _) (fun σ => by ext h i; rfl)

private theorem l2WreathEquivWreathSymTwo_inr (f m : ℕ) (σ : Equiv.Perm (Fin m)) :
    l2WreathEquivWreathSymTwo f m (SemidirectProduct.inr σ) = SemidirectProduct.inr σ := by
  refine SemidirectProduct.ext ?_ rfl
  funext i
  simp [l2WreathEquivWreathSymTwo]

theorem isWreathTransposition_of_isConj {s : X} {f r : ℕ} (hf : 2 ≤ f)
    (Φ : X ⧸ Subgroup.center X ≃* L2Wreath f r) {i j : Fin r} (hij : i ≠ j)
    (hc : IsConj (SemidirectProduct.inr (Equiv.swap i j)) (Φ (QuotientGroup.mk s))) :
    IsWreathTransposition X f r s := by
  refine ⟨by omega, GaloisField 2 f, inferInstance, inferInstance,
    GaloisField.card 2 f (by omega), Φ.trans (l2WreathEquivWreathSymTwo f r), i, j, hij, ?_⟩
  have h := (l2WreathEquivWreathSymTwo f r).toMonoidHom.map_isConj hc
  change IsConj (l2WreathEquivWreathSymTwo f r (SemidirectProduct.inr (Equiv.swap i j)))
    (l2WreathEquivWreathSymTwo f r (Φ (QuotientGroup.mk s))) at h
  rw [l2WreathEquivWreathSymTwo_inr] at h
  exact h.symm

section AlmostSimple

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_orderOf_eq_two_mem (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : M ≠ ⊥) {u : G} (hu : u ∈ D) : ∃ w ∈ M, orderOf w = 2 := by
  obtain ⟨m, hm, hne, hcomm⟩ := exists_commute_conj_of_normal hS hrad hM hu
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hv2 : (m * u * m⁻¹) * (m * u * m⁻¹) = 1 := hS.oddT.mul_self_eq_one (hS.conj_mem m hu)
  refine ⟨u * (m * u * m⁻¹), ?_, orderOf_eq_prime ?_ ?_⟩
  · have e : u * (m * u * m⁻¹) = (u * m * u⁻¹) * m⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hu2]
      group
    rw [e]
    exact M.mul_mem (‹M.Normal›.conj_mem m hm u) (M.inv_mem hm)
  · rw [hcomm.mul_pow, pow_two, pow_two, hu2, hv2, one_mul]
  · intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hu2]

theorem sup_zpowers_hyps (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hcent : Subgroup.centralizer (M : Set G) = ⊥) {u : G} (hu : u ∈ D)
    (hcls : IsOddTranspClass (conjSet M u)) :
    orderOf (⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ : ↥(M ⊔ Subgroup.zpowers u)) =
        2 ∧
      IsOddTransp {y : ↥(M ⊔ Subgroup.zpowers u) |
        IsConj ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ y} ∧
      Subgroup.normalClosure
        ({⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩} : Set ↥(M ⊔ Subgroup.zpowers u)) =
        ⊤ ∧
      CFSG.pCore 2 ↥(M ⊔ Subgroup.zpowers u) = ⊥ ∧
      fusionOddCore ↥(M ⊔ Subgroup.zpowers u) = ⊥ ∧
      (∀ N : Subgroup ↥(M ⊔ Subgroup.zpowers u), N.Normal → Group.IsSolvable N → N = ⊥) ∧
      derivedSeries ↥(M ⊔ Subgroup.zpowers u) 1 = derivedSeries ↥(M ⊔ Subgroup.zpowers u) 2 := by
  have hMna : ¬ IsMulCommutative M := not_isMulCommutative_of_ne_bot hrad hM.2.1
  have hle : M ≤ M ⊔ Subgroup.zpowers u := le_sup_left
  have hSY := setup_sup_zpowers hcls
  have hcY : {y : ↥(M ⊔ Subgroup.zpowers u) |
      IsConj ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ y} = conjSet M u :=
    (hSY.eq_setOf_isConj ⟨1, M.one_mem, by simp⟩).symm
  have hradY := solvableRadical_sup_zpowers_eq_bot (u := u) hMs hMna hcent
  obtain ⟨w, hwM, hw2⟩ := exists_orderOf_eq_two_mem hS hrad hM.2.1 hu
  refine ⟨?_, ?_, ?_, ?_, ?_, hradY, derivedSeries_sup_zpowers hMs hMna⟩
  · rw [Subgroup.orderOf_mk]
    exact hS.oddT.1 u hu
  · rw [hcY]
    exact hcls.2.1
  · rw [← closure_setOf_isConj_eq_normalClosure, hcY]
    exact hcls.2.2
  ·
    refine le_bot_iff.mp (sSup_le fun K hK => le_bot_iff.mpr ?_)
    obtain ⟨hKn, hK2⟩ := hK
    haveI := hK2.isNilpotent
    exact hradY K hKn inferInstance
  ·
    refine le_bot_iff.mp (sSup_le fun N hN => le_bot_iff.mpr ?_)
    obtain ⟨hNn, hNodd⟩ := hN
    refine eq_bot_of_not_le_subgroupOf hMs hcent fun hMN => ?_
    have hwN : (⟨w, hle hwM⟩ : ↥(M ⊔ Subgroup.zpowers u)) ∈ N :=
      hMN (Subgroup.mem_subgroupOf.mpr hwM)
    have hdvd := orderOf_dvd_natCard (⟨⟨w, hle hwM⟩, hwN⟩ : ↥N)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hw2] at hdvd
    exact Nat.not_even_iff_odd.mpr hNodd (even_iff_two_dvd.mpr hdvd)

theorem oddTranspListAlt_sup_zpowers (hD : OddTranspositionListInputClsDerivedEq) (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : Asc72.IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hcent : Subgroup.centralizer (M : Set G) = ⊥) {u : G} (hu : u ∈ D)
    (hcls : IsOddTranspClass (conjSet M u)) :
    OddTranspListAlt ↥(M ⊔ Subgroup.zpowers u)
      ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u)⟩ := by
  obtain ⟨hord, hodd, hncl, hO2, hO, -, hder⟩ := sup_zpowers_hyps hS hrad hM hMs hcent hu hcls
  refine hD _ _ hord hodd hncl hO2 (hO ▸ bot_le) ?_
  have hsurj := QuotientGroup.mk'_surjective (Subgroup.center ↥(M ⊔ Subgroup.zpowers u))
  rw [← map_derivedSeries_eq hsurj 1, ← map_derivedSeries_eq hsurj 2, hder]

end AlmostSimple

theorem oddTranspositionListInputClsCorrected_of_derivedEq
    (hD : OddTranspositionListInputClsDerivedEq) :
    OddTranspositionListInputClsCorrected := by
  intro X _ _ s hord hodd hncl hO2 hOZ
  have hS := setup_quotient_center hodd hncl hO2
  have hrad := eq_bot_of_normal_isSolvable_quotient_center hO2 hOZ
  rcases derivedSeries_eq_or_l2Wreath_or_almostSimpleCase hS hrad with
    hder | ⟨f, r, hf, -, Φ, hΦ⟩ | ⟨M, hMn, hM, huniq, hMs, hcent, hidx, hW, hcls⟩
  · exact Or.inl (hD X s hord hodd hncl hO2 hOZ hder)
  · obtain ⟨i, j, hij, hc⟩ := hΦ _ (IsConj.refl _)
    exact Or.inl (Or.inl ⟨r, f, Or.inr (Or.inr (Or.inr (isWreathTransposition_of_isConj hf Φ hij hc)))⟩)
  · exact Or.inr ⟨M, hMn, hM, huniq, hMs, hcent, hidx, hW, hcls _ (IsConj.refl _),
      oddTranspListAlt_sup_zpowers hD hS hrad hM hMs hcent (IsConj.refl _) (hcls _ (IsConj.refl _))⟩

end CFSG.OddTranspositions.PartFour
