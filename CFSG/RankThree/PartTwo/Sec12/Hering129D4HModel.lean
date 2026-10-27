module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HLie
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HNum
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HSL2
public import CFSG.RankThree.PartTwo.Sec12.Hering129LD4
import CFSG.Models.PGLSimple
import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Card
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.Sec12.Hering129KRes

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem isSubnormal_map_centralizer (φ : G ≃* G') {y : G} {X : Subgroup G}
    (h : (X.subgroupOf (Subgroup.centralizer ({y} : Set G))).IsSubnormal) :
    ((X.map φ.toMonoidHom).subgroupOf (Subgroup.centralizer ({φ y} : Set G'))).IsSubnormal := by
  let ε : ↥(Subgroup.centralizer ({φ y} : Set G')) →* ↥(Subgroup.centralizer ({y} : Set G)) :=
    { toFun := fun u => ⟨φ.symm (u : G'), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.mp u.2
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact this⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have heq : (X.map φ.toMonoidHom).subgroupOf (Subgroup.centralizer ({φ y} : Set G')) =
      (X.subgroupOf (Subgroup.centralizer ({y} : Set G))).comap ε := by
    ext u
    show (u : G') ∈ X.map φ.toMonoidHom ↔ φ.symm (u : G') ∈ X
    rw [Subgroup.mem_map_equiv]
  rw [heq]
  exact h.comap ε

end Transport

section Quotient

open CFSG.Assembly.RankThreeEven (projSL)

theorem isSimpleGroup_projSL_two {p m : ℕ} [Fact p.Prime] (h4 : 4 ≤ p ^ m) :
    IsSimpleGroup (projSL 2 (GaloisField p m)) := by
  have hm : m ≠ 0 := by
    rintro rfl
    norm_num at h4
  have hcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  exact CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 2) (GaloisField p m) le_rfl
    (Or.inr (by rw [hcard]; omega)) (Or.inr (by rw [hcard]; omega))

theorem card_of_isSLThreePiAt {D : Type} [Group D] {q : ℕ} (h : Sec4.IsSLThreePiAt D q) :
    (q % 3 = 1 ∧ Nat.card D = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∨
      (q % 3 = 2 ∧ Nat.card D = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) := by
  obtain ⟨K, _, _, hcase⟩ := h
  rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
  · left
    refine ⟨hq, ?_⟩
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toEquiv,
      CFSG.LieType.SteinbergBR.BlockPar.card_SL_three' (F := K), hK]
  · right
    refine ⟨hq, ?_⟩
    rw [Nat.card_congr e.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.card_statedSU_three_of' hK, mul_assoc]

theorem no_surjection_slThreePi_psl2 {D : Type} [Group D] [Finite D] {n : ℕ} (hn : 2 ≤ n)
    (hD : Sec4.IsSLThreePiAt D (2 ^ n)) {p m : ℕ} [Fact p.Prime] (h4 : 4 ≤ p ^ m)
    (φ : D →* projSL 2 (GaloisField p m)) (hφ : Function.Surjective φ) : False := by
  have hq2 : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hQ := Hering129KRes.isQuasisimple_of_isSLThreePiAt hD hq2
  have hZ3 : Nat.card (Subgroup.center D) = 3 := card_center_eq_three_of_isSLThreePi ⟨_, hD⟩
  have hSs : IsSimpleGroup (projSL 2 (GaloisField p m)) := isSimpleGroup_projSL_two h4
  haveI hDp : Group.IsPerfect D := hQ.1
  haveI hSp : Group.IsPerfect (projSL 2 (GaloisField p m)) :=
    Group.IsPerfect.ofSurjective (f := φ) hφ
  have hnc : ∃ a b : projSL 2 (GaloisField p m), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup (projSL 2 (GaloisField p m)) :=
      { (inferInstance : Group (projSL 2 (GaloisField p m))) with mul_comm := hcon }
    exact Group.IsPerfect.not_isSolvable (projSL 2 (GaloisField p m)) inferInstance
  have hZS : Subgroup.center (projSL 2 (GaloisField p m)) = ⊥ :=
    Hering129HLift.center_eq_bot_of_simple hSs hnc
  have hZle : Subgroup.center D ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : φ z ∈ Subgroup.center (projSL 2 (GaloisField p m)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨d, rfl⟩ := hφ s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz d]
    rw [hZS] at this
    exact Subgroup.mem_bot.mp this
  let φ' : D ⧸ Subgroup.center D →* projSL 2 (GaloisField p m) :=
    QuotientGroup.lift (Subgroup.center D) φ hZle
  have hφ' : Function.Surjective φ' := by
    intro s
    obtain ⟨d, rfl⟩ := hφ s
    exact ⟨(d : D ⧸ Subgroup.center D), rfl⟩
  have hSimp : IsSimpleGroup (D ⧸ Subgroup.center D) := hQ.2.1
  have hinj : Function.Injective φ' := by
    rcases hSimp.eq_bot_or_eq_top_of_normal φ'.ker with h0 | h1
    · exact (MonoidHom.ker_eq_bot_iff φ').mp h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      obtain ⟨x, rfl⟩ := hφ' a
      obtain ⟨y, rfl⟩ := hφ' b
      have hx : φ' x = 1 := MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top x)
      have hy : φ' y = 1 := MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top y)
      rw [hx, hy]
  have hcardS : Nat.card (D ⧸ Subgroup.center D) = Nat.card (projSL 2 (GaloisField p m)) :=
    Nat.card_congr (Equiv.ofBijective φ' ⟨hinj, hφ'⟩)
  have hDcard : Nat.card D = 3 * Nat.card (projSL 2 (GaloisField p m)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center D), hcardS, hZ3,
      mul_comm]
  have hm : m ≠ 0 := by
    rintro rfl
    norm_num at h4
  have hF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have hN := Sec11.KSListsProof.card_projSL_two_mul (GaloisField p m)
  rw [hF] at hN
  have hs' : (∃ k, p ^ m = 2 ^ k) ∨ Odd (p ^ m) := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with hp2 | hp2
    · exact Or.inl ⟨m, by rw [hp2]⟩
    · exact Or.inr (hp2.pow)
  rcases card_of_isSLThreePiAt hD with ⟨-, hc⟩ | ⟨-, hc⟩
  · exact no_psl2_card_eq_psl3 hn h4 hs' (t := (2 ^ n) ^ 3 - 1) (Or.inl rfl) hN
      (hDcard.symm.trans hc)
  · exact no_psl2_card_eq_psl3 hn h4 hs' (t := (2 ^ n) ^ 3 + 1) (Or.inr rfl) hN
      (hDcard.symm.trans hc)

end Quotient

section Model

open CFSG.RankThree.PartTwo.Sec4.E27 CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
  CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec12.Hering129L
open CFSG.Assembly.RankThreeEven (projSL)


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem d4_resCent_threeB' (P : D4Par n X σ) {t : C0 σ} (htB : t ∈ Bsub σ)
    (ht : orderOf t = 3) : resCent (⊤ : Subgroup (C0 σ)) t = Asub σ := by
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  have ht3 : t ^ 3 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hX4 : 4 ≤ Nat.card X := by
    rw [P.card]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) P.one_le
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2 3
  apply le_antisymm
  · show inSubgroup perfectResidual ((⊤ : Subgroup (C0 σ)) ⊓
      Subgroup.centralizer ({t} : Set (C0 σ))) ≤ _
    rw [top_inf_eq]
    exact (inSubgroup_perfectResidual_le_commutator' _).trans
      (centralizer_comm_le_asub σ n P.one_le P.card P.frob htB ht3 ht1)
  · have hperf : Group.IsPerfect ↥(Asub σ) := (isQuasisimple_d4ShortSL2 P.sigma_pow_three hX4).1
    have hle : Asub σ ≤ (⊤ : Subgroup (C0 σ)) ⊓ Subgroup.centralizer ({t} : Set (C0 σ)) := by
      refine le_inf le_top fun a ha => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Asub_Bsub_commute ha htB
    exact le_inSubgroup_perfectResidual_of_isPerfect hle hperf

@[expose] def ThreeAExcl (σ : X ≃+* X) : Prop :=
  ∀ a ∈ Asub σ, orderOf a = 3 → ∀ Xm : Subgroup (C0 σ),
    Xm ≤ Subgroup.centralizer ({a} : Set (C0 σ)) → Group.IsPerfect Xm →
    (Xm.subgroupOf (Subgroup.centralizer ({a} : Set (C0 σ)))).IsSubnormal →
    ∀ (p m : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ m →
      ∀ φ : Xm →* projSL 2 (GaloisField p m), Function.Surjective φ → False

theorem threeAExcl_of_solvable (σ : X ≃+* X)
    (hs : ∀ a ∈ Asub σ, orderOf a = 3 →
      Group.IsSolvable ↥(Subgroup.centralizer ({a} : Set (C0 σ)))) : ThreeAExcl σ := by
  intro a haA ha3 Xm hXC hXp hXs p m _ h4 φ hφ
  haveI := hs a haA ha3
  haveI : Group.IsSolvable ↥Xm :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXC)
      (Subgroup.inclusion_injective hXC)
  haveI := hXp
  haveI : Nontrivial (projSL 2 (GaloisField p m)) := (isSimpleGroup_projSL_two h4).toNontrivial
  haveI : Nontrivial ↥Xm := hφ.nontrivial
  exact Group.IsPerfect.not_isSolvable ↥Xm ‹_›

theorem threeAExcl_of_two_le (P : D4Par n X σ) (hn : 2 ≤ n) : ThreeAExcl σ := by
  intro a haA ha3 Xm hXC hXp hXs p m _ h4 φ hφ
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  have hA : IsThreeA a (2 ^ n) := Hering129L.d4_isThreeA P hn haA ha3
  have hq2 : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set C := Subgroup.centralizer ({a} : Set (C0 σ)) with hC
  set D := resCent (⊤ : Subgroup (C0 σ)) a with hDdef
  have hDC : D ≤ C := (resCent_le ⊤ a).trans inf_le_right
  have hXD : Xm ≤ D :=
    le_inSubgroup_perfectResidual_of_isPerfect (X := (⊤ : Subgroup (C0 σ)) ⊓ C) (P := Xm)
      (le_inf le_top hXC) hXp
  have hsub : (Xm.subgroupOf D).IsSubnormal := by
    have heq : Xm.subgroupOf D = (Xm.subgroupOf C).comap (Subgroup.inclusion hDC) := by
      ext u
      rfl
    rw [heq]
    exact hXs.comap _
  have hQ : CFSG.IsQuasisimple ↥D := Hering129KRes.isQuasisimple_of_isSLThreePiAt hA.2.2 hq2
  haveI hSs : Nontrivial (projSL 2 (GaloisField p m)) := (isSimpleGroup_projSL_two h4).toNontrivial
  have hP' : Group.IsPerfect (Xm.subgroupOf D) := by
    haveI := hXp
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXD).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXD).symm.surjective
  have hne : Xm.subgroupOf D ≠ ⊥ := by
    intro h0
    obtain ⟨s, t, hst⟩ := hSs.exists_pair_ne
    apply hst
    obtain ⟨x, rfl⟩ := hφ s
    obtain ⟨y, rfl⟩ := hφ t
    have hx : x = 1 := by
      have : (⟨(x : C0 σ), hXD x.2⟩ : ↥D) ∈ Xm.subgroupOf D := x.2
      rw [h0, Subgroup.mem_bot] at this
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    have hy : y = 1 := by
      have : (⟨(y : C0 σ), hXD y.2⟩ : ↥D) ∈ Xm.subgroupOf D := y.2
      rw [h0, Subgroup.mem_bot] at this
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    rw [hx, hy]
  have htop := Sec11.FieldCentRigid82.eq_top_of_isSubnormal_of_isQuasisimple hQ hsub hP' hne
  have hDX : D ≤ Xm := by
    intro d hd
    have : (⟨d, hd⟩ : ↥D) ∈ Xm.subgroupOf D := by rw [htop]; trivial
    exact this
  have hXeq : Xm = D := le_antisymm hXD hDX
  exact no_surjection_slThreePi_psl2 hn hA.2.2 h4
    (φ.comp (MulEquiv.subgroupCongr hXeq.symm).toMonoidHom)
    (hφ.comp (MulEquiv.subgroupCongr hXeq.symm).surjective)

theorem exists_conj_std (P : D4Par n X σ) (hex : ThreeAExcl σ) {c y : C0 σ}
    (hpd : PairData c y) : ∃ γ : C0 σ, γ * c * γ⁻¹ = zStd P ∧ γ * y * γ⁻¹ = tStd P := by
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI := P.charP
  have hy3 : orderOf y = 3 := orderOf_eq_prime hpd.y3 hpd.y1
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds X (2 ^ n) σ P.card P.frob h3 y hpd.y3 hpd.y1
  obtain ⟨Xk, hXC, hXp, hXs, hcX, p, m, hp, h4, φ, hφ⟩ := hpd.X
  let cg : C0 σ ≃* C0 σ := MulAut.conj g
  have hy1o : orderOf (g * y * g⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hy3
  have hXg : Xk.map cg.toMonoidHom ≤ Subgroup.centralizer ({g * y * g⁻¹} : Set (C0 σ)) := by
    rw [centralizer_conj_eq_map]
    exact Subgroup.map_mono hXC
  have hperf : Group.IsPerfect (Xk.map cg.toMonoidHom) := by
    haveI := hXp
    exact Group.IsPerfect.ofSurjective
      (f := (Xk.equivMapOfInjective cg.toMonoidHom cg.injective).toMonoidHom)
      (Xk.equivMapOfInjective cg.toMonoidHom cg.injective).surjective
  have hsubg : ((Xk.map cg.toMonoidHom).subgroupOf
      (Subgroup.centralizer ({g * y * g⁻¹} : Set (C0 σ)))).IsSubnormal :=
    isSubnormal_map_centralizer cg hXs
  rcases hg with hA | hB
  · exfalso
    exact hex (g * y * g⁻¹) hA hy1o (Xk.map cg.toMonoidHom) hXg hperf hsubg p m hp h4
      (φ.comp (Xk.equivMapOfInjective cg.toMonoidHom cg.injective).symm.toMonoidHom)
      (hφ.comp (Xk.equivMapOfInjective cg.toMonoidHom cg.injective).symm.surjective)
  ·
    have hresB := d4_resCent_threeB' P hB hy1o
    have hXA : Xk.map cg.toMonoidHom ≤ Asub σ := by
      rw [← hresB]
      exact le_inSubgroup_perfectResidual_of_isPerfect (X := (⊤ : Subgroup (C0 σ)) ⊓
        Subgroup.centralizer ({g * y * g⁻¹} : Set (C0 σ))) (le_inf le_top hXg) hperf
    have hc1A : g * c * g⁻¹ ∈ Asub σ := hXA (Subgroup.mem_map.mpr ⟨c, hcX, rfl⟩)
    have hc1o : orderOf (g * c * g⁻¹) = 3 := by
      rw [orderOf_conj_eq]
      exact orderOf_eq_prime hpd.c3 hpd.c1
    haveI : CharP ↥(fixSubfield σ) 2 := inferInstance
    set b := (bsubEquiv P).symm ⟨g * y * g⁻¹, hB⟩ with hb
    have hb3 : b ^ 3 = 1 := by
      apply (bsubEquiv P).injective
      rw [map_pow, map_one, hb, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, hpd.y3]
      group
    have hb1 : b ≠ 1 := by
      intro h
      have := congrArg (bsubEquiv P) h
      rw [hb, MulEquiv.apply_symm_apply, map_one] at this
      have h1 : g * y * g⁻¹ = 1 := congrArg Subtype.val this
      exact hpd.y1 (conj_eq_one_iff.mp h1)
    obtain ⟨x, hx⟩ := sl2_exists_conj_sl2Three hb3 hb1
    set β : C0 σ := ((bsubEquiv P x : Bsub σ) : C0 σ) with hβ
    have hβB : β ∈ Bsub σ := (bsubEquiv P x).2
    have hβy : β * (g * y * g⁻¹) * β⁻¹ = tStd P := by
      have := congrArg (fun w => ((bsubEquiv P w : Bsub σ) : C0 σ)) hx
      simp only [map_mul, map_inv, hb, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      exact this
    set a := (asubEquiv P).symm ⟨g * c * g⁻¹, hc1A⟩ with ha
    have ha3 : a ^ 3 = 1 := by
      apply (asubEquiv P).injective
      rw [map_pow, map_one, ha, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, hpd.c3]
      group
    have ha1 : a ≠ 1 := by
      intro h
      have := congrArg (asubEquiv P) h
      rw [ha, MulEquiv.apply_symm_apply, map_one] at this
      have h1 : g * c * g⁻¹ = 1 := congrArg Subtype.val this
      exact hpd.c1 (conj_eq_one_iff.mp h1)
    obtain ⟨u, hu⟩ := sl2_exists_conj_sl2Three ha3 ha1
    set α : C0 σ := ((asubEquiv P u : Asub σ) : C0 σ) with hα
    have hαA : α ∈ Asub σ := (asubEquiv P u).2
    have hαc : α * (g * c * g⁻¹) * α⁻¹ = zStd P := by
      have := congrArg (fun w => ((asubEquiv P w : Asub σ) : C0 σ)) hu
      simp only [map_mul, map_inv, ha, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      exact this
    have htB : tStd P ∈ Bsub σ := (bsubEquiv P _).2
    refine ⟨α * β * g, ?_, ?_⟩
    ·
      have hcomm : β * (g * c * g⁻¹) = (g * c * g⁻¹) * β :=
        (Asub_Bsub_commute hc1A hβB).symm
      calc α * β * g * c * (α * β * g)⁻¹ = α * (β * (g * c * g⁻¹) * β⁻¹) * α⁻¹ := by group
        _ = α * (g * c * g⁻¹) * α⁻¹ := by rw [hcomm]; group
        _ = zStd P := hαc
    · have hcomm : α * tStd P = tStd P * α := Asub_Bsub_commute hαA htB
      calc α * β * g * y * (α * β * g)⁻¹ = α * (β * (g * y * g⁻¹) * β⁻¹) * α⁻¹ := by group
        _ = α * tStd P * α⁻¹ := by rw [hβy]
        _ = tStd P := by rw [hcomm]; group

theorem exists_hessF_of_pairData (hKF : KF_D4_HESS) (P : D4Par n X σ) (hex : ThreeAExcl σ)
    {c y : C0 σ} (hpd : PairData c y) : ∃ F : Subgroup (C0 σ), HessF c y F := by
  obtain ⟨γ, hγc, hγy⟩ := exists_conj_std P hex hpd
  obtain ⟨F₀, hF₀⟩ := hKF n X σ P
  refine ⟨F₀.map (MulAut.conj γ⁻¹).toMonoidHom, ?_⟩
  have h := HessF.map (MulAut.conj γ⁻¹) hF₀
  have hc : (MulAut.conj γ⁻¹) (zStd P) = c := by
    rw [MulAut.conj_apply, ← hγc]
    group
  have hy : (MulAut.conj γ⁻¹) (tStd P) = y := by
    rw [MulAut.conj_apply, ← hγy]
    group
  rw [hc, hy] at h
  exact h

end Model

section MapPair

open CFSG.Assembly.RankThreeEven (projSL)

variable {K K' : Type} [Group K] [Group K'] [Finite K] [Finite K']

theorem PairData.map (e : K ≃* K') {c y : K} (h : PairData c y) : PairData (e c) (e y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h.c3, map_one]
  · rw [← map_pow, h.y3, map_one]
  · intro h1
    exact h.c1 (e.injective (by rw [h1, map_one]))
  · intro h1
    exact h.y1 (e.injective (by rw [h1, map_one]))
  · rw [← map_mul, ← map_mul, h.comm]
  · obtain ⟨Xk, hXC, hXp, hXs, hcX, p, m, hp, h4, φ, hφ⟩ := h.X
    refine ⟨Xk.map e.toMonoidHom, ?_, ?_, ?_, Subgroup.mem_map_of_mem _ hcX, p, m, hp, h4,
      φ.comp (Xk.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom,
      hφ.comp (Xk.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective⟩
    · rw [Hering129L.centralizer_map_equiv_eq e y]
      exact Subgroup.map_mono hXC
    · haveI := hXp
      exact Group.IsPerfect.ofSurjective
        (f := (Xk.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (Xk.equivMapOfInjective e.toMonoidHom e.injective).surjective
    · exact isSubnormal_map_centralizer e hXs

end MapPair

section Final

open CFSG.Assembly.RankThreeEven (projSL)


@[expose] def TwoThreeAExcl : Prop :=
  ∀ (X : Type) [Field X] [Finite X] (σ : X ≃+* X), D4Par 1 X σ → ThreeAExcl σ

theorem gap129HessD4_of (hKF : KF_D4_HESS) (hTwo : TwoThreeAExcl) : Gap129HessD4 := by
  intro P _ _ Yh Bh xh bh ch hD hex
  obtain ⟨r, hr, hp2, ⟨e⟩⟩ := hex
  haveI := hD.normal
  obtain ⟨hZ, ⟨a⟩⟩ := exists_act_of_d4 hD hp2 e
  have hpd := pairData_of_hess hD hZ a
  obtain ⟨Kf, hKf1, hKf2, σ, hK, hσ, ⟨eM⟩⟩ := Hering129KModels.exists_d4_model e
  have hrc : r.card = 2 ^ r.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
  have Ppar : D4Par r.exponent Kf σ :=
    ⟨r.exponent_pos, by rw [hK, hrc], fun c => by rw [hσ c, hrc]⟩
  have hexcl : ThreeAExcl σ := by
    by_cases hn : 2 ≤ r.exponent
    · exact threeAExcl_of_two_le Ppar hn
    · have h1 : r.exponent = 1 := by
        have := r.exponent_pos
        omega
      have Ppar1 : D4Par 1 Kf σ := by
        rw [← h1]
        exact Ppar
      exact hTwo Kf σ Ppar1
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  obtain ⟨F, hF⟩ := exists_hessF_of_pairData hKF Ppar hexcl (hpd.map eM)
  have hF' := HessF.map eM.symm hF
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at hF'
  exact hessConcl_of_hessF hD hZ a hF'

end Final


end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
