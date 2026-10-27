module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.ProjLine
public import CFSG.Quasithin.Recognition.CertF9
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.Asc83Table Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction
  CFSG.RankThree.PartTwo.Sec4.Sporadic.ProjLine CFSG.Quasithin Matrix
open scoped commutatorElement MatrixGroups

theorem elts_spec : okA xArr = true ∧ okA yArr = true ∧ okA zArr = true ∧ okA g0Arr = true ∧
    okA h8Arr = true ∧ (∀ k < gensCzArr.size, okA gensCzArr[k]! = true) ∧
    eqA 315 (powArr 315 xArr 3) (idA 315) = true ∧ eqA 315 (powArr 315 yArr 3) (idA 315) = true ∧
    eqA 315 zArr (commutatorA 315 xArr yArr) = true ∧ commA zArr xArr = true ∧
    commA zArr yArr = true ∧ eqA 315 zArr (idA 315) = false ∧
    (∀ k < gensCzArr.size, commA gensCzArr[k]! zArr = true) ∧
    eqA 315 (conjA 315 g0Arr zArr) (compA 315 zArr zArr) = true ∧
    inCert cP3 (conjA 315 h8Arr xArr) = true ∧ inCert cP3 (conjA 315 h8Arr yArr) = true ∧
    inCert cP3 (powArr 315 h8Arr 4) = false ∧ inCert cP3 (powArr 315 h8Arr 8) = true := by
  have h := j2_check3_parts.1
  simp only [chkElts, Bool.and_eq_true, Bool.not_eq_true', allLt_iff, and_assoc] at h
  exact h

theorem enum_spec : enumOK 315 gensP3 keyPts cP3 = true ∧ cP3.pts.size = 27 ∧
    enumOK 315 gensCzArr keyPts cCz = true ∧ cCz.pts.size = 1080 ∧
    enumOK 315 gensNZArr keyPts cNZ = true ∧ cNZ.pts.size = 2160 ∧
    enumOK 315 gensNP keyPts cNP = true ∧ cNP.pts.size = 216 := by
  have h := j2_check3_parts.2.1
  simp only [chkEnum, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

@[expose] noncomputable def xJ : GJ := elA xArr (okA_spec elts_spec.1)

@[expose] noncomputable def yJ : GJ := elA yArr (okA_spec elts_spec.2.1)

@[expose] noncomputable def zJ : GJ := elA zArr (okA_spec elts_spec.2.2.1)

@[expose] noncomputable def g0J : GJ := elA g0Arr (okA_spec elts_spec.2.2.2.1)

@[expose] noncomputable def h8J : GJ := elA h8Arr (okA_spec elts_spec.2.2.2.2.1)

theorem rep_x : Rep 315 xArr xJ.1 := rep_elA _

theorem rep_y : Rep 315 yArr yJ.1 := rep_elA _

theorem rep_z : Rep 315 zArr zJ.1 := rep_elA _

theorem rep_g0 : Rep 315 g0Arr g0J.1 := rep_elA _

theorem rep_h8 : Rep 315 h8Arr h8J.1 := rep_elA _

theorem x_cube : xJ ^ 3 = 1 := eq_of_rep (rep_pow rep_x 3) rep_one elts_spec.2.2.2.2.2.2.1

theorem y_cube : yJ ^ 3 = 1 := eq_of_rep (rep_pow rep_y 3) rep_one elts_spec.2.2.2.2.2.2.2.1

theorem rep_comm : Rep 315 (commutatorA 315 xArr yArr) ⁅xJ, yJ⁆.1 := by
  have := rep_commutatorA (okA_spec elts_spec.1).1 (okA_spec elts_spec.2.1).1
  rw [(rep_of_validA (okA_spec elts_spec.1).1).unique rep_x,
    (rep_of_validA (okA_spec elts_spec.2.1).1).unique rep_y] at this
  simpa [commutatorElement_def] using this

theorem z_eq : zJ = ⁅xJ, yJ⁆ := eq_of_rep rep_z rep_comm elts_spec.2.2.2.2.2.2.2.2.1

theorem rep_z' : Rep 315 zArr ⁅xJ, yJ⁆.1 := z_eq ▸ rep_z

theorem z_comm_x : Commute ⁅xJ, yJ⁆ xJ :=
  commute_of_commA rep_z' rep_x elts_spec.2.2.2.2.2.2.2.2.2.1

theorem z_comm_y : Commute ⁅xJ, yJ⁆ yJ :=
  commute_of_commA rep_z' rep_y elts_spec.2.2.2.2.2.2.2.2.2.2.1

theorem z_ne_one : ⁅xJ, yJ⁆ ≠ 1 := by
  intro h
  have h1 := (eqA_iff rep_z' rep_one).2 (by rw [h])
  rw [elts_spec.2.2.2.2.2.2.2.2.2.2.2.1] at h1
  exact Bool.noConfusion h1

@[expose] noncomputable def P3 : Subgroup GJ := closure {xJ, yJ}

theorem card_P3 : Nat.card P3 = 27 := ex27_card x_cube y_cube z_comm_x z_comm_y z_ne_one

theorem permsA_P3 : permsA 315 gensP3 = {xJ.1, yJ.1} := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [gensP3] using hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [gensP3], rfl⟩
    · exact ⟨1, by simp [gensP3], rfl⟩

theorem P3_eq_subOf : P3 = subOf gensP3 := by
  rw [P3, subOf_eq_closure]
  rw [permsA_P3, Set.image_pair]
  rfl

theorem rep_mem_P3 {g : GJ} (hg : g ∈ P3) : ∃ i < 27, Rep 315 cP3.pts[i]! g.1 := by
  rw [P3_eq_subOf] at hg
  obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) enum_spec.1 hg
  exact ⟨i, by rw [← enum_spec.2.1]; exact hi, hr⟩

theorem cube_of_mem_P3 {g : GJ} (hg : g ∈ P3) : g ^ 3 = 1 :=
  pow_three_eq_one_of_mem x_cube z_comm_x z_comm_y y_cube hg

theorem z_mem_P3 : ⁅xJ, yJ⁆ ∈ P3 := by
  have hx : xJ ∈ P3 := subset_closure (by simp)
  have hy : yJ ∈ P3 := subset_closure (by simp)
  rw [commutatorElement_def]
  exact P3.mul_mem (P3.mul_mem (P3.mul_mem hx hy) (P3.inv_mem hx)) (P3.inv_mem hy)

theorem not_comm_P3 : ¬ IsMulCommutative P3 := by
  intro h
  apply z_ne_one
  rw [commutatorElement_eq_one_iff_mul_comm]
  have h1 := congrArg Subtype.val (h.is_comm.comm ⟨xJ, subset_closure (by simp)⟩
    ⟨yJ, subset_closure (by simp)⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
  exact h1

theorem isExtraspecial_P3 : CFSG.IsExtraspecialPGroup 3 P3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three
    (IsPGroup.of_card (n := 3) (by rw [card_P3]; norm_num)) (fun g => Subtype.ext ?_)
    (by rw [card_P3]; norm_num) not_comm_P3
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact cube_of_mem_P3 g.2

theorem exponent_P3 : Monoid.exponent P3 = 3 := by
  have hdvd : Monoid.exponent P3 ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact cube_of_mem_P3 g.2)
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd) with h | h
  · exfalso
    have h1 := Monoid.pow_exponent_eq_one (⟨xJ, subset_closure (by simp)⟩ : P3)
    rw [h, pow_one] at h1
    have hx1 : xJ = 1 := by simpa using congrArg Subtype.val h1
    apply z_ne_one
    rw [hx1, commutatorElement_one_left]
  · exact h

theorem isHeisThree_P3 : IsHeisThree P3 := ⟨isExtraspecial_P3, card_P3, exponent_P3⟩

theorem inf_centralizer_P3 : P3 ⊓ centralizer (P3 : Set GJ) = zpowers ⁅xJ, yJ⁆ := by
  rw [inf_centralizer_eq_map_center]
  have hcen : Nat.card (center P3) = 3 := isExtraspecial_P3.2.2.2
  have hz : (⟨⁅xJ, yJ⁆, z_mem_P3⟩ : P3) ∈ center P3 := by
    rw [mem_center_iff]
    intro g
    have hle : P3 ≤ centralizer {⁅xJ, yJ⁆} := by
      rw [P3, closure_le]
      rintro s (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 z_comm_x.eq.symm
      · exact mem_centralizer_singleton_iff.2 z_comm_y.eq.symm
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hle g.2))
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [zpowers_le]
    exact ⟨_, hz, rfl⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcen, Nat.card_zpowers,
      orderOf_eq_prime (cube_of_mem_P3 z_mem_P3) z_ne_one]

theorem gensCz_spec (k : ℕ) (hk : k < gensCzArr.size) :
    validA 315 gensCzArr[k]! = true ∧ inP gensCzArr[k]! = true :=
  okA_spec (elts_spec.2.2.2.2.2.1 k hk)

theorem gensNZ_spec (k : ℕ) (hk : k < gensNZArr.size) :
    validA 315 gensNZArr[k]! = true ∧ inP gensNZArr[k]! = true :=
  spec_push gensCz_spec (okA_spec elts_spec.2.2.2.1) k hk

theorem gensCz_mem_centralizer (k : ℕ) (hk : k < gensCzArr.size) :
    permOfArr 315 gensCzArr[k]! ∈
      Subgroup.centralizer ({zJ.1} : Set (Equiv.Perm (Fin 315))) := by
  rw [mem_centralizer_singleton_iff]
  have hc := elts_spec.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk
  exact ((eqA_iff (rep_compA (rep_of_validA (gensCz_spec k hk).1) rep_z)
    (rep_compA rep_z (rep_of_validA (gensCz_spec k hk).1))).1 hc)

@[expose] noncomputable def decJ (t : Array ℕ) : GJ := by
  classical
  exact if h : permOfArr 315 t ∈ P then ⟨permOfArr 315 t, h⟩ else 1

theorem decJ_of_mem {t : Array ℕ} (h : permOfArr 315 t ∈ P) :
    decJ t = ⟨permOfArr 315 t, h⟩ := by
  unfold decJ
  simp [h]

@[expose] noncomputable def conjGen (k : ℕ) : ConjAct GJ :=
  ConjAct.toConjAct (if k = 0 then (⟨permA, permA_mem⟩ : GJ) else ⟨permB, permB_mem⟩)

theorem conjGen_zero :
    conjGen 0 = ConjAct.toConjAct (⟨permA, permA_mem⟩ : GJ) := by
  simp [conjGen]

theorem conjGen_one :
    conjGen 1 = ConjAct.toConjAct (⟨permB, permB_mem⟩ : GJ) := by
  simp [conjGen]

theorem closure_conjGen :
    Subgroup.closure (conjGen '' {k | k < 2}) = ⊤ := by
  have himg : conjGen '' {k | k < 2} = (ConjAct.toConjAct : GJ ≃* ConjAct GJ) ''
      (((↑) : P → Equiv.Perm (Fin 315)) ⁻¹' {permA, permB}) := by
    ext c
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      interval_cases k
      · exact ⟨⟨permA, permA_mem⟩, Or.inl rfl, rfl⟩
      · exact ⟨⟨permB, permB_mem⟩, Or.inr rfl, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      rcases hg with hg | hg
      · refine ⟨0, by norm_num, ?_⟩
        rw [conjGen_zero]
        exact congrArg _ (Subtype.ext hg.symm)
      · refine ⟨1, by norm_num, ?_⟩
        rw [conjGen_one]
        exact congrArg _ (Subtype.ext hg.symm)
  have h2 : (ConjAct.toConjAct : GJ ≃* ConjAct GJ) ''
      (((↑) : P → Equiv.Perm (Fin 315)) ⁻¹' {permA, permB}) =
      (ConjAct.toConjAct : GJ ≃* ConjAct GJ).toMonoidHom ''
        (((↑) : P → Equiv.Perm (Fin 315)) ⁻¹' {permA, permB}) := rfl
  have hc : Subgroup.closure (((↑) : P → Equiv.Perm (Fin 315)) ⁻¹' {permA, permB}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [himg, h2, ← MonoidHom.map_closure, hc]
  exact Subgroup.map_top_of_surjective _ (ConjAct.toConjAct : GJ ≃* ConjAct GJ).surjective

theorem decJ_conj (k : ℕ)
    (hk : k < 2) (a : Array ℕ) (ha : okA a = true) : decJ (zConj k a) = conjGen k • decJ a := by
  have hc := j2_check3_parts.2.2.1
  simp only [chkClass, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hva, hvb⟩, -⟩, -⟩ := hc
  have hA := okA_spec ha
  have hP : permOfArr 315 a ∈ P := (mem_P_iff (rep_of_validA hA.1)).1 hA.2
  have hk2 : k < 2 := hk
  interval_cases k
  · have he := CFSG.RankThree.Native.permOfArr_eq_of_rep
      (rep_conj_perm rep_permA hva (rep_of_validA hA.1))
    have hm : permOfArr 315 (zConj 0 a) ∈ P := by
      rw [zConj, he]
      exact P.mul_mem (P.mul_mem permA_mem hP) (P.inv_mem permA_mem)
    rw [decJ_of_mem hm, decJ_of_mem hP, conjGen_zero,
      ConjAct.toConjAct_smul]
    exact Subtype.ext he
  · have he := CFSG.RankThree.Native.permOfArr_eq_of_rep
      (rep_conj_perm rep_permB hvb (rep_of_validA hA.1))
    have hm : permOfArr 315 (zConj 1 a) ∈ P := by
      rw [zConj, he]
      exact P.mul_mem (P.mul_mem permB_mem hP) (P.inv_mem permB_mem)
    rw [decJ_of_mem hm, decJ_of_mem hP, conjGen_one,
      ConjAct.toConjAct_smul]
    exact Subtype.ext he

theorem ncard_class_z :
    (MulAction.orbit (ConjAct GJ) zJ).ncard = 560 := by
  have hc := j2_check3_parts.2.2.1
  simp only [chkClass, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨-, hok⟩, hsz⟩ := hc
  have hkey : ∀ a b, okA a = true → okA b = true → decJ a = decJ b →
      keyA 315 keyPts a = keyA 315 keyPts b := by
    intro a b ha hb hab
    have hA := okA_spec ha
    have hB := okA_spec hb
    have hPa : permOfArr 315 a ∈ P := (mem_P_iff (rep_of_validA hA.1)).1 hA.2
    have hPb : permOfArr 315 b ∈ P := (mem_P_iff (rep_of_validA hB.1)).1 hB.2
    rw [decJ_of_mem hPa, decJ_of_mem hPb] at hab
    exact keyA_eq (by decide) hA.1 hB.1 (congrArg Subtype.val hab)
  have h := CFSG.Monster.B.Fischer.ncard_orbit_of_arrCertOK (dec := decJ) (gens := conjGen) hok
    (fun k hk a ha => decJ_conj k hk a ha) hkey
  rw [closure_conjGen, hsz] at h
  have hroot : decJ zArr = zJ := by
    have hz := okA_spec elts_spec.2.2.1
    have hPz : permOfArr 315 zArr ∈ P := (mem_P_iff (rep_of_validA hz.1)).1 hz.2
    rw [decJ_of_mem hPz]
    rfl
  rw [hroot] at h
  have htop : MulAction.orbit (⊤ : Subgroup (ConjAct GJ)) zJ = MulAction.orbit (ConjAct GJ) zJ := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
  rw [← htop]
  exact h

theorem centralizer_z : centralizer ({zJ} : Set GJ) = subOf gensCzArr := by
  have hle : subOf gensCzArr ≤ centralizer ({zJ} : Set GJ) := by
    intro g hg
    rw [mem_subOf] at hg
    have hcl : Subgroup.closure (permsA 315 gensCzArr) ≤
        Subgroup.centralizer ({zJ.1} : Set (Equiv.Perm (Fin 315))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact gensCz_mem_centralizer k hk
    have := mem_centralizer_singleton_iff.1 (hcl hg)
    exact mem_centralizer_singleton_iff.2 (Subtype.ext this)
  have horb := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct GJ) zJ)
  rw [MulAction.index_stabilizer, ncard_class_z] at horb
  have hG : Nat.card (ConjAct GJ) = 604800 := by
    rw [← card_GJ]
    exact Nat.card_congr (ConjAct.toConjAct : GJ ≃* ConjAct GJ).toEquiv.symm
  have hS : Nat.card (centralizer ({zJ} : Set GJ)) =
      Nat.card (MulAction.stabilizer (ConjAct GJ) zJ) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Nat.card_congr (Equiv.subtypeEquiv (ConjAct.toConjAct : GJ ≃* ConjAct GJ).toEquiv
      fun g => Subgroup.mem_comap)
  rw [hG, ← hS] at horb
  have hC : Nat.card (centralizer ({zJ} : Set GJ)) = 1080 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) (horb.trans (by norm_num))
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [hC, card_subOf (by decide) enum_spec.2.2.1 gensCz_spec, enum_spec.2.2.2.1])).symm

theorem card_centralizer_z : Nat.card (centralizer ({zJ} : Set GJ)) = 1080 := by
  rw [centralizer_z, card_subOf (by decide) enum_spec.2.2.1 gensCz_spec, enum_spec.2.2.2.1]

theorem z_cube : zJ ^ 3 = 1 := by rw [z_eq]; exact cube_of_mem_P3 z_mem_P3

theorem zJ_ne_one : zJ ≠ 1 := by rw [z_eq]; exact z_ne_one

theorem g0_conj_z : g0J * zJ * g0J⁻¹ = zJ ^ 2 :=
  eq_of_rep (rep_conj rep_g0 (okA_spec elts_spec.2.2.2.1).1 rep_z)
    (by rw [sq]; exact rep_mul rep_z rep_z) elts_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem permOfArr_g0 : permOfArr 315 g0Arr = g0J.1 :=
  (rep_of_validA (okA_spec elts_spec.2.2.2.1).1).unique rep_g0

theorem normalizer_Z : normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) = subOf gensNZArr :=
  normalizer_zpowers_eq z_cube zJ_ne_one centralizer_z gensCz_spec rep_g0
    (okA_spec elts_spec.2.2.2.1).1 g0_conj_z

theorem card_normalizer_Z :
    Nat.card (normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) = 2160 := by
  rw [normalizer_Z, card_subOf (by decide) enum_spec.2.2.2.2.1 gensNZ_spec,
    enum_spec.2.2.2.2.2.1]

theorem gensNP_spec (k : ℕ) (hk : k < gensNP.size) :
    validA 315 gensNP[k]! = true ∧ inP gensNP[k]! = true := by
  have hk3 : k < 3 := by simpa [gensNP] using hk
  interval_cases k
  · exact okA_spec elts_spec.1
  · exact okA_spec elts_spec.2.1
  · exact okA_spec elts_spec.2.2.2.2.1

theorem x_mem_P3 : xJ ∈ P3 := subset_closure (by simp)

theorem y_mem_P3 : yJ ∈ P3 := subset_closure (by simp)

theorem mem_P3_of_inCert {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : inCert cP3 t = true) : g ∈ P3 := by
  rw [P3_eq_subOf]
  exact mem_of_inCert enum_spec.1 ht h

theorem inCert_P3 {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (hg : g ∈ P3) :
    inCert cP3 t = true :=
  inCert_of_mem enum_spec.1 ht (P3_eq_subOf ▸ hg)

theorem mem_normalizer_of_conj_gens {G : Type*} [Group G] [Finite G] {S : Set G} {g : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) : g ∈ normalizer ((closure S : Subgroup G) : Set G) :=
  mem_normalizer_closure_of_conj_mem h

theorem h8_mem_normalizer : h8J ∈ normalizer ((P3 : Subgroup GJ) : Set GJ) := by
  refine mem_normalizer_of_conj_gens ?_
  rintro s (rfl | rfl)
  · exact mem_P3_of_inCert (rep_conj rep_h8 (okA_spec elts_spec.2.2.2.2.1).1 rep_x)
      elts_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact mem_P3_of_inCert (rep_conj rep_h8 (okA_spec elts_spec.2.2.2.2.1).1 rep_y)
      elts_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normalizer_P3_le : normalizer ((P3 : Subgroup GJ) : Set GJ) ≤
    normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) := by
  intro g hg
  have key : ∀ g ∈ normalizer ((P3 : Subgroup GJ) : Set GJ), ∀ c ∈ zpowers zJ,
      g * c * g⁻¹ ∈ zpowers zJ := by
    intro g hg c hc
    rw [z_eq, ← inf_centralizer_P3] at hc ⊢
    refine ⟨(mem_normalizer_iff.mp hg c).mp hc.1, mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hp' : g⁻¹ * p * g ∈ P3 := by
      have := (mem_normalizer_iff.mp (inv_mem hg) p).mp hp
      simpa using this
    have hcp := mem_centralizer_iff.mp hc.2 _ hp'
    calc p * (g * c * g⁻¹) = g * ((g⁻¹ * p * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * p * g)) * g⁻¹ := by rw [hcp]
      _ = g * c * g⁻¹ * p := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem normalizer_P3 : normalizer ((P3 : Subgroup GJ) : Set GJ) = subOf gensNP := by
  apply le_antisymm
  · intro g hg
    have hgZ := normalizer_P3_le hg
    rw [normalizer_Z] at hgZ
    obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.2.2.1 hgZ
    have hv : validA 315 cNZ.pts[i]! = true :=
      (enumOK_spec (by decide) enum_spec.2.2.2.2.1).2.2 i hi
    have hck := allLt_spec j2_check3_parts.2.2.2.1 hi
    have h1 : inCert cP3 (conjA 315 cNZ.pts[i]! xArr) = true :=
      inCert_P3 (rep_conj hr hv rep_x) ((mem_normalizer_iff.mp hg xJ).mp x_mem_P3)
    have h2 : inCert cP3 (conjA 315 cNZ.pts[i]! yArr) = true :=
      inCert_P3 (rep_conj hr hv rep_y) ((mem_normalizer_iff.mp hg yJ).mp y_mem_P3)
    simp only [h1, h2, Bool.and_self, Bool.not_true, Bool.false_or] at hck
    exact mem_of_inCert enum_spec.2.2.2.2.2.2.1 hr hck
  · intro g hg
    rw [mem_subOf] at hg
    have hle : Subgroup.closure (permsA 315 gensNP) ≤
        (normalizer ((P3 : Subgroup GJ) : Set GJ)).map
          (CFSG.ComponentClassification.J2Cover.P).subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      have hk3 : k < 3 := by simpa [gensNP] using hk
      interval_cases k
      · exact ⟨xJ, le_normalizer x_mem_P3,
          ((rep_of_validA (okA_spec elts_spec.1).1).unique rep_x).symm⟩
      · exact ⟨yJ, le_normalizer y_mem_P3,
          ((rep_of_validA (okA_spec elts_spec.2.1).1).unique rep_y).symm⟩
      · exact ⟨h8J, h8_mem_normalizer,
          ((rep_of_validA (okA_spec elts_spec.2.2.2.2.1).1).unique rep_h8).symm⟩
    obtain ⟨g', hg', hgg'⟩ := hle hg
    rw [← Subtype.ext hgg']
    exact hg'

theorem card_normalizer_P3 : Nat.card (normalizer ((P3 : Subgroup GJ) : Set GJ)) = 216 := by
  rw [normalizer_P3, card_subOf (by decide) enum_spec.2.2.2.2.2.2.1 gensNP_spec,
    enum_spec.2.2.2.2.2.2.2]

abbrev QP3 : Type :=
  normalizer ((P3 : Subgroup GJ) : Set GJ) ⧸
    (P3 : Subgroup GJ).subgroupOf (normalizer ((P3 : Subgroup GJ) : Set GJ))

theorem card_QP3 : Nat.card QP3 = 8 := by
  have h := (P3.subgroupOf (normalizer ((P3 : Subgroup GJ) : Set GJ))
    ).card_eq_card_quotient_mul_card_subgroup
  rw [card_normalizer_P3, Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv,
    card_P3] at h
  change 216 = Nat.card QP3 * 27 at h
  omega

theorem quotient_normalizer_P3 : Nonempty (QP3 ≃* Multiplicative (ZMod 8)) := by
  set q : QP3 := QuotientGroup.mk ⟨h8J, h8_mem_normalizer⟩
  have h8 : q ^ 8 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact mem_P3_of_inCert (rep_pow rep_h8 8) elts_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h4 : q ^ 4 ≠ 1 := by
    rw [Ne, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    intro hmem
    have := inCert_P3 (rep_pow rep_h8 4) hmem
    rw [elts_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at this
    exact Bool.noConfusion this
  have hord : orderOf q = 8 := by
    have hdvd : orderOf q ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have h4' : ¬ orderOf q ∣ 2 ^ 2 := fun hd => h4 (orderOf_dvd_iff_pow_eq_one.1 hd)
    rw [hk'] at h4' ⊢
    have hk3 : k = 3 := by
      by_contra hne
      exact h4' (pow_dvd_pow 2 (by omega))
    rw [hk3]
    norm_num
  have : IsCyclic QP3 := isCyclic_of_orderOf_eq_card q (by rw [hord, card_QP3])
  exact ⟨mulEquivOfCyclicCardEq (by rw [card_QP3, Nat.card_eq_fintype_card]; rfl)⟩

theorem inZ_spec {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (h : inZ t = true) :
    g ∈ zpowers zJ := by
  simp only [inZ, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [eq_of_rep ht rep_one h]; exact one_mem _
  · rw [eq_of_rep ht rep_z h]; exact mem_zpowers _
  · rw [eq_of_rep ht (rep_mul rep_z rep_z) h]
    exact mul_mem (mem_zpowers _) (mem_zpowers _)

theorem card_fixed_conj (g u : Equiv.Perm (Fin 315)) :
    Nat.card {i : Fin 315 // (g⁻¹ * u * g) i = i} = Nat.card {i : Fin 315 // u i = i} := by
  refine Nat.card_congr
    { toFun := fun i => ⟨g i.1, ?_⟩
      invFun := fun i => ⟨g⁻¹ i.1, ?_⟩
      left_inv := fun i => Subtype.ext (by simp)
      right_inv := fun i => Subtype.ext (by simp) }
  · have := i.2
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at this
    exact Equiv.Perm.inv_eq_iff_eq.1 this
  · have := i.2
    simp [this]

theorem weaklyClosed (g : GJ) (h : conjugate (zpowers zJ) g ≤ P3) :
    conjugate (zpowers zJ) g = zpowers zJ := by
  have hu : g⁻¹ * zJ * g ∈ P3 := h ⟨zJ, mem_zpowers zJ, by simp⟩
  obtain ⟨k, hk, hr⟩ := rep_mem_P3 hu
  have hfix : Nat.card {i : Fin 315 // (g⁻¹ * zJ * g).1 i = i} = 45 := by
    rw [show (g⁻¹ * zJ * g).1 = g.1⁻¹ * zJ.1 * g.1 from rfl, card_fixed_conj,
      card_fixed_eq_fixedCount rep_z]
    have := j2_check3_parts.2.2.2.2.1
    simp only [chkFix, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  have hck := allLt_spec (by
    have := j2_check3_parts.2.2.2.2.1
    simp only [chkFix, Bool.and_eq_true] at this
    exact this.2) (show k < cP3.pts.size by rw [enum_spec.2.1]; exact hk)
  rw [card_fixed_eq_fixedCount hr] at hfix
  simp only [hfix, Bool.or_eq_true, beq_iff_eq, show (45 : ℕ) ≠ 0 by norm_num, or_false] at hck
  have hmem := inZ_spec hr hck
  apply Subgroup.eq_of_le_of_card_ge
  · rw [conjugate, MonoidHom.map_zpowers, zpowers_le]
    simpa using hmem
  · rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj _).injective]

@[expose] noncomputable def Ej (j : Fin 4) : Subgroup GJ :=
  (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one j).sub

theorem nine_eq : {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9} = Set.range Ej := by
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hB, h9⟩
    rcases eq_of_le_of_card_eq_nine x_cube y_cube z_comm_x z_comm_y card_P3 hB h9 with
      h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨?_, (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one j).card⟩
    rw [Ej, E9Basis.sub, closure_le]
    rintro s (rfl | rfl)
    · exact z_mem_P3
    · obtain ⟨a, b, -, -, -, hw⟩ := ex27Rep_eq (x := xJ) (y := yJ) j
      change ex27Rep xJ yJ j ∈ P3
      rw [hw]
      exact P3.mul_mem (P3.pow_mem x_mem_P3 a) (P3.pow_mem y_mem_P3 b)

theorem rep_bArr (j : Fin 4) : Rep 315 (bArr j) (ex27Rep xJ yJ j).1 := by
  fin_cases j
  · simp only [bArr, ex27Rep]
    exact rep_x
  · simp only [bArr, ex27Rep]
    exact rep_y
  · simp only [bArr, ex27Rep]
    simpa using rep_mul rep_x rep_y
  · simp only [bArr, ex27Rep]
    simpa [sq, mul_assoc] using rep_mul rep_x (rep_mul rep_y rep_y)

theorem mem_Ej_of_inE {j : Fin 4} {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : inE j t = true) : g ∈ Ej j := by
  rw [inE, List.any_eq_true] at h
  obtain ⟨a, -, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨c, -, h⟩ := h
  have hg := eq_of_rep ht (rep_mul (rep_pow rep_z' a) (rep_pow (rep_bArr j) c)) h
  rw [hg]
  exact (Ej j).mul_mem ((Ej j).pow_mem (subset_closure (Or.inl rfl)) a)
    ((Ej j).pow_mem (subset_closure (Or.inr rfl)) c)

theorem exists_conj_E0 (j : Fin 4) :
    ∃ n ∈ normalizer ((P3 : Subgroup GJ) : Set GJ), conjugate (Ej 0) n = Ej j := by
  by_cases hj : j = 0
  · exact ⟨1, one_mem _, by rw [hj, conjugate, inv_one, map_one]; exact Subgroup.map_id _⟩
  have hd := j2_check3_parts.2.2.2.2.2.2.2.2
  simp only [chkDelta, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    List.any_eq_true, List.mem_range, Bool.and_eq_true] at hd
  have hj' : (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by omega
  obtain ⟨k, hk, h1, h2⟩ := hd j hj'
  have hv : validA 315 cNP.pts[k]! = true :=
    (enumOK_spec (by decide) enum_spec.2.2.2.2.2.2.1).2.2 k hk
  set n : GJ := elA cNP.pts[k]! ⟨hv, (mem_P_iff (rep_of_validA hv)).2 (closure_le_P gensNP_spec
    ((enumOK_spec (by decide) enum_spec.2.2.2.2.2.2.1).1 _ |>.2 ⟨k, hk, rfl⟩))⟩
  have hn : Rep 315 cNP.pts[k]! n.1 := rep_elA _
  have hnN : n ∈ normalizer ((P3 : Subgroup GJ) : Set GJ) := by
    rw [normalizer_P3]
    exact mem_of_inCert enum_spec.2.2.2.2.2.2.1 hn (by
      rw [inCert, List.any_eq_true]
      exact ⟨cNP.pts[k]!, by rw [getElem!_pos _ k hk]; exact Array.getElem_mem_toList hk,
        (eqA_iff hn hn).2 rfl⟩)
  refine ⟨n, hnN, ?_⟩
  have hjj : (j : Fin 4) = ⟨(j : ℕ), j.2⟩ := rfl
  apply Subgroup.eq_of_le_of_card_ge
  · rw [conjugate, Ej, E9Basis.sub, MonoidHom.map_closure, closure_le, Set.image_pair]
    rintro s (rfl | rfl)
    · exact mem_Ej_of_inE (rep_conjInv hn hv rep_z') h1
    · exact mem_Ej_of_inE (rep_conjInv hn hv rep_x) h2
  · rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj _).injective, Ej, Ej,
      E9Basis.card, E9Basis.card]

theorem conjugate_conjugate (H : Subgroup GJ) (n m : GJ) :
    conjugate (conjugate H n) m = conjugate H (n * m) := by
  rw [conjugate, conjugate, conjugate, Subgroup.map_map]
  congr 1

theorem delta_transitive :
    ∀ B ∈ {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9},
      ∀ B' ∈ {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9},
        ∃ n ∈ normalizer ((P3 : Subgroup GJ) : Set GJ), B' = conjugate B n := by
  rw [nine_eq]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  obtain ⟨n, hn, hni⟩ := exists_conj_E0 i
  obtain ⟨m, hm, hmj⟩ := exists_conj_E0 j
  refine ⟨n⁻¹ * m, mul_mem (inv_mem hn) hm, ?_⟩
  rw [← hni, conjugate_conjugate, mul_inv_cancel_left, hmj]

@[expose] def finOf (S : Array ℕ) : Finset (Fin 315) := Finset.univ.filter fun p => S.contains p.val

theorem mem_finOf {S : Array ℕ} {p : Fin 315} : p ∈ finOf S ↔ S.contains p.val = true := by
  simp [finOf]

theorem card_finOf {S : Array ℕ} (hS : ∀ p ∈ S, p < 315) (hnd : S.toList.Nodup) :
    (finOf S).card = S.size := by
  have h : (finOf S).map Fin.valEmbedding = S.toList.toFinset := by
    ext p
    simp only [Finset.mem_map, mem_finOf, Fin.valEmbedding_apply, List.mem_toFinset,
      Array.mem_toList_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact Array.contains_iff_mem.1 hq
    · intro hp
      exact ⟨⟨p, hS p hp⟩, Array.contains_iff_mem.2 hp, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, List.toFinset_card_of_nodup hnd, Array.length_toList]

theorem mapsInto_spec {t S T : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : mapsInto t S T = true) :
    ∀ p ∈ finOf S, (CFSG.ComponentClassification.J2Cover.P).subtype g p ∈ finOf T := by
  intro p hp
  rw [mem_finOf] at hp ⊢
  rw [mapsInto, Array.all_eq_true] at h
  obtain ⟨i, hi, hpi⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hp)
  have := h i hi
  rw [hpi, ht.apply p.2] at this
  exact this

theorem setsOK_spec {F : Array (Array ℕ)} {m : ℕ} (h : setsOK F m = true) :
    (∀ i < F.size, F[i]!.size = m ∧ (∀ p ∈ F[i]!, p < 315) ∧ F[i]!.toList.Nodup) ∧
      ∀ i < F.size, ∀ j < F.size, i ≠ j → ∃ p ∈ F[i]!, F[j]!.contains p = false := by
  simp only [setsOK, Bool.and_eq_true, Array.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Array.any_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · rw [getElem!_pos F i hi]
    exact ⟨(h1 i hi).1.1, fun p hp => by
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hp
      exact (h1 i hi).1.2 k hk, (h1 i hi).2⟩
  · rcases h2 i hi j hj with h | ⟨k, hk, hk'⟩
    · exact absurd h hij
    · exact ⟨_, Array.getElem_mem hk, hk'⟩

theorem sets_spec : o6Sets.size = 6 ∧ setsOK o6Sets 15 = true ∧ fixesSets o6Sets zArr = true ∧
    s10Sets.size = 10 ∧ setsOK s10Sets 9 = true ∧ fixesSets s10Sets zArr = true := by
  have h := j2_check3_parts.2.2.2.2.2.2.2.1
  simp only [chkSets, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

@[expose] def famOf (F : Array (Array ℕ)) {m : ℕ} (_ : F.size = m) (i : Fin m) :
    Finset (Fin 315) :=
  finOf F[i.val]!

theorem famOf_injective {F : Array (Array ℕ)} {m k : ℕ} (hm : F.size = m)
    (h : setsOK F k = true) : Function.Injective (famOf F hm) := by
  intro i j hij
  by_contra hne
  obtain ⟨p, hp, hp'⟩ := (setsOK_spec h).2 i (hm ▸ i.2) j (hm ▸ j.2) (fun e => hne (Fin.ext e))
  have hp315 : p < 315 := ((setsOK_spec h).1 i (hm ▸ i.2)).2.1 p hp
  have hmem : (⟨p, hp315⟩ : Fin 315) ∈ famOf F hm i := by
    rw [famOf, mem_finOf]
    exact Array.contains_iff_mem.2 hp
  rw [hij, famOf, mem_finOf] at hmem
  rw [hmem] at hp'
  exact Bool.noConfusion hp'

theorem card_famOf {F : Array (Array ℕ)} {m k : ℕ} (hm : F.size = m) (h : setsOK F k = true)
    (i : Fin m) : (famOf F hm i).card = k := by
  have := (setsOK_spec h).1 i (hm ▸ i.2)
  rw [famOf, card_finOf this.2.1 this.2.2, this.1]

theorem image_famOf {F : Array (Array ℕ)} {m k : ℕ} (hm : F.size = m) (h : setsOK F k = true)
    {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (hp : permutesSets F t = true) (i : Fin m) :
    ∃ j, (famOf F hm i).image ((CFSG.ComponentClassification.J2Cover.P).subtype g) =
      famOf F hm j := by
  rw [permutesSets, Array.all_eq_true] at hp
  obtain ⟨j, hj, hmaps⟩ := Array.any_eq_true.1 (hp i (hm ▸ i.2))
  refine ⟨⟨j, hm ▸ hj⟩, image_eq_of_subset _ ?_ (by rw [card_famOf hm h, card_famOf hm h])⟩
  have := mapsInto_spec ht (S := F[(i : ℕ)]!) (T := F[j]!) (by
    rw [getElem!_pos F i.1 (hm ▸ i.2), getElem!_pos F j hj]
    exact hmaps)
  exact this

theorem chkSix_spec : allLt cCz.pts.size (fun k => permutesSets o6Sets cCz.pts[k]! &&
      (!(fixesSets o6Sets cCz.pts[k]!) || inZ cCz.pts[k]!)) = true ∧
    allLt gensCzArr.size (fun k => actsBy o6Sets gensCzArr[k]! (sigCz.getD k [])) = true := by
  have h := j2_check3_parts.2.2.2.2.2.1
  simp only [chkSix, Bool.and_eq_true] at h
  exact h

theorem chkTen_spec : allLt cNZ.pts.size (fun k => permutesSets s10Sets cNZ.pts[k]! &&
      (!(fixesSets s10Sets cNZ.pts[k]!) || inZ cNZ.pts[k]!)) = true ∧
    allLt gensNZArr.size (fun k => actsBy s10Sets gensNZArr[k]! (sigNZ.getD k [])) = true := by
  have h := j2_check3_parts.2.2.2.2.2.2.1
  simp only [chkTen, Bool.and_eq_true] at h
  exact h

@[expose] def F6 : Fin 6 → Finset (Fin 315) := famOf o6Sets sets_spec.1

theorem F6_injective : Function.Injective F6 := famOf_injective _ sets_spec.2.1

theorem image_F6 : ∀ h ∈ centralizer ({zJ} : Set GJ), ∀ i, ∃ j,
    (F6 i).image ((CFSG.ComponentClassification.J2Cover.P).subtype h) = F6 j := by
  intro h hh i
  rw [centralizer_z] at hh
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 hh
  have hck := allLt_spec chkSix_spec.1 hk
  simp only [Bool.and_eq_true] at hck
  exact image_famOf sets_spec.1 sets_spec.2.1 hr hck.1 i

@[expose] noncomputable def act6 : centralizer ({zJ} : Set GJ) →* Equiv.Perm (Fin 6) :=
  setAct F6_injective image_F6

theorem z_mem_C : zJ ∈ centralizer ({zJ} : Set GJ) := mem_centralizer_singleton_iff.2 rfl

theorem fixesSets_of_image {F : Array (Array ℕ)} {m k : ℕ} (hm : F.size = m)
    (h : setsOK F k = true) {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (hfix : ∀ i, (famOf F hm i).image ((CFSG.ComponentClassification.J2Cover.P).subtype g) =
      famOf F hm i) : fixesSets F t = true := by
  rw [fixesSets, Array.all_eq_true]
  intro i hi
  rw [mapsInto, Array.all_eq_true]
  intro j hj
  have hp : F[i][j] < 315 := ((setsOK_spec h).1 i hi).2.1 _ (by
    rw [getElem!_pos F i hi]; exact Array.getElem_mem hj)
  have hmem : (⟨F[i][j], hp⟩ : Fin 315) ∈ famOf F hm ⟨i, hm ▸ hi⟩ := by
    rw [famOf, mem_finOf, getElem!_pos F i hi]
    exact Array.contains_iff_mem.2 (Array.getElem_mem hj)
  have himg := Finset.mem_image_of_mem ((CFSG.ComponentClassification.J2Cover.P).subtype g) hmem
  rw [hfix, famOf, mem_finOf, getElem!_pos F i hi] at himg
  rw [ht.apply hp]
  exact himg

theorem image_of_fixesSets {F : Array (Array ℕ)} {m k : ℕ} (hm : F.size = m)
    (_h : setsOK F k = true) {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (hfix : fixesSets F t = true) (i : Fin m) :
    (famOf F hm i).image ((CFSG.ComponentClassification.J2Cover.P).subtype g) =
      famOf F hm i := by
  rw [fixesSets, Array.all_eq_true] at hfix
  refine image_eq_of_subset _ ?_ rfl
  exact mapsInto_spec ht (S := F[(i : ℕ)]!) (T := F[(i : ℕ)]!) (by
    rw [getElem!_pos F i.1 (hm ▸ i.2)]; exact hfix i (hm ▸ i.2))

theorem ker_act6 : act6.ker = (zpowers zJ).subgroupOf (centralizer ({zJ} : Set GJ)) := by
  ext ⟨g, hg⟩
  rw [act6, mem_ker_setAct, mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 (centralizer_z ▸ hg)
    have hck := allLt_spec chkSix_spec.1 hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hck
    rcases hck.2 with h1 | h1
    · rw [fixesSets_of_image sets_spec.1 sets_spec.2.1 hr h] at h1
      exact absurd h1 Bool.noConfusion
    · exact inZ_spec hr h1
  · intro h
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp h
    have hz : (⟨zJ, z_mem_C⟩ : centralizer ({zJ} : Set GJ)) ∈ act6.ker := by
      rw [act6, mem_ker_setAct]
      exact image_of_fixesSets sets_spec.1 sets_spec.2.1 rep_z sets_spec.2.2.1
    have hzn := Subgroup.zpow_mem _ hz n
    rw [act6, mem_ker_setAct] at hzn
    exact hzn

@[expose] def F10 : Fin 10 → Finset (Fin 315) := famOf s10Sets sets_spec.2.2.2.1

theorem F10_injective : Function.Injective F10 := famOf_injective _ sets_spec.2.2.2.2.1

theorem image_F10 : ∀ h ∈ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ), ∀ i, ∃ j,
    (F10 i).image ((CFSG.ComponentClassification.J2Cover.P).subtype h) = F10 j := by
  intro h hh i
  rw [normalizer_Z] at hh
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.2.2.1 hh
  have hck := allLt_spec chkTen_spec.1 hk
  simp only [Bool.and_eq_true] at hck
  exact image_famOf sets_spec.2.2.2.1 sets_spec.2.2.2.2.1 hr hck.1 i

@[expose] noncomputable def act10 :
    normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) →* Equiv.Perm (Fin 10) :=
  setAct F10_injective image_F10

@[expose] def labelOf (n : ℕ) : Option GF9 := if n = 9 then none else some (GF9.ofNat' n)

@[expose] def invLam : List ℕ := [1, 2, 7, 6, 8, 3, 9, 4, 5, 0]

@[expose] def unlabel : Option GF9 → Fin 10
  | none => ⟨invLam.getD 9 0 % 10, Nat.mod_lt _ (by norm_num)⟩
  | some x => ⟨invLam.getD x.toNat 0 % 10, Nat.mod_lt _ (by norm_num)⟩

@[expose] def lamE : Fin 10 ≃ Option GF9 where
  toFun i := labelOf (lam10[i.val]!)
  invFun := unlabel
  left_inv := by decide
  right_inv := by decide

theorem range_le_of_closure {H : Subgroup GJ} {S : Set GJ} (hH : H = closure S) {M : Type*}
    [Group M] (f : H →* M) (T : Subgroup M)
    (hS : ∀ g (hg : g ∈ S), f ⟨g, hH ▸ subset_closure hg⟩ ∈ T) : f.range ≤ T := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  have hg' : g ∈ closure S := hH ▸ hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    have : (⟨1, hg⟩ : H) = 1 := rfl
    rw [this, map_one]
    exact T.one_mem
  | mul x y hx hy ihx ihy =>
    have : (⟨x * y, hg⟩ : H) = ⟨x, hH ▸ hx⟩ * ⟨y, hH ▸ hy⟩ := rfl
    rw [this, map_mul]
    exact T.mul_mem (ihx _) (ihy _)
  | inv x hx ih =>
    have : (⟨x⁻¹, hg⟩ : H) = (⟨x, hH ▸ hx⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact T.inv_mem (ih _)

theorem card_range_of_ker {H : Type*} [Group H] [Finite H] {M : Type*} [Group M]
    (f : H →* M) : Nat.card f.range * Nat.card f.ker = Nat.card H := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← f.ker.card_eq_card_quotient_mul_card_subgroup]

@[expose] def listFun (m : ℕ) (hm : 0 < m) (l : List ℕ) (i : Fin m) : Fin m :=
  ⟨l.getD i.val 0 % m, Nat.mod_lt _ hm⟩

theorem image_actsBy {F : Array (Array ℕ)} {m k : ℕ} (hm : F.size = m) (h : setsOK F k = true)
    {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) {l : List ℕ} (hl : ∀ i < m, l.getD i 0 < m)
    (hact : actsBy F t l = true) (i : Fin m) :
    (famOf F hm i).image ((CFSG.ComponentClassification.J2Cover.P).subtype g) =
      famOf F hm (listFun m (Fin.pos i) l i) := by
  rw [actsBy, List.all_eq_true] at hact
  have hi := hact i (List.mem_range.2 (hm ▸ i.2))
  refine image_eq_of_subset _ ?_ (by rw [card_famOf hm h, card_famOf hm h])
  have e : (listFun m (Fin.pos i) l i : ℕ) = l.getD i 0 := Nat.mod_eq_of_lt (hl i i.2)
  exact mapsInto_spec ht (S := F[(i : ℕ)]!) (T := F[(listFun m (Fin.pos i) l i : ℕ)]!)
    (by rw [e]; exact hi)

theorem gensCz_size : gensCzArr.size = 2 := rfl

theorem gensNZ_size : gensNZArr.size = 3 := rfl

theorem gCz_mem (k : ℕ) (hk : k < gensCzArr.size) :
    gElt gensCzArr gensCz_spec k hk ∈ centralizer ({zJ} : Set GJ) := by
  rw [centralizer_z]
  exact gElt_mem _ _ k hk

theorem act6_gen (k : ℕ) (hk : k < gensCzArr.size)
    (hm : gElt gensCzArr gensCz_spec k hk ∈ centralizer ({zJ} : Set GJ)) :
    ∀ i, act6 ⟨gElt gensCzArr gensCz_spec k hk, hm⟩ i =
      listFun 6 (by norm_num) (sigCz.getD k []) i := by
  intro i
  have hk2 : k < 2 := hk
  have hl : ∀ i < 6, (sigCz.getD k []).getD i 0 < 6 := by
    interval_cases k <;> decide
  have hact := allLt_spec chkSix_spec.2 hk
  rw [act6, setAct_eq_of_image F6_injective image_F6 (h := ⟨_, hm⟩) (σ := Equiv.ofBijective
      (listFun 6 (by norm_num) (sigCz.getD k []))
      ((Finite.injective_iff_bijective).1 (by interval_cases k <;> decide)))
    (fun j => image_actsBy sets_spec.1 sets_spec.2.1 (rep_elA (gensCz_spec k hk)) hl hact j)]
  rfl

theorem listFun_six_mem : ∀ k < 2, ∃ σ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
    ∀ i, σ i = listFun 6 (by norm_num) (sigCz.getD k []) i := by
  intro k hk
  interval_cases k
  · exact ⟨Equiv.swap 1 3 * Equiv.swap 2 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide,
      by decide⟩
  · exact ⟨List.formPerm [0, 2, 1, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide,
      by decide⟩

theorem range_act6_le : act6.range ≤ alternatingGroup (Fin 6) := by
  refine range_le_of_closure (by rw [centralizer_z, subOf_eq_closure_gElt gensCzArr gensCz_spec])
    act6 _ ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨σ, hσ, hσk⟩ := listFun_six_mem k hk
  convert hσ using 1
  ext i
  rw [act6_gen k hk _ i, ← hσk i]

theorem card_zpowers_z : Nat.card (zpowers zJ) = 3 := by
  rw [Nat.card_zpowers, orderOf_eq_prime z_cube zJ_ne_one]

theorem card_ker_act6 : Nat.card act6.ker = 3 := by
  rw [ker_act6, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr z_mem_C)).toEquiv,
    card_zpowers_z]

theorem range_act6 : act6.range = alternatingGroup (Fin 6) := by
  apply Subgroup.eq_of_le_of_card_ge range_act6_le
  have h := card_range_of_ker act6
  rw [card_ker_act6, card_centralizer_z] at h
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [h360]
  omega

theorem centralizer_zpowers_eq (g : GJ) :
    centralizer ((zpowers g : Subgroup GJ) : Set GJ) = centralizer ({g} : Set GJ) := by
  ext c
  rw [mem_centralizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h g (mem_zpowers g)).symm
  · intro h k hk
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    exact ((Commute.zpow_right (show Commute c g from h) n).eq).symm

theorem isExtOf_of_mulEquiv {X Y A B : Type*} [Group X] [Group Y] [Group A] [Group B]
    (e : X ≃* Y) (h : IsExtOf Y A B) : IsExtOf X A B := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have hmap : (K.comap e.toMonoidHom).map e.toMonoidHom = K :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective K
  refine ⟨K.comap e.toMonoidHom, hK.comap _, ⟨?_⟩, ⟨?_⟩⟩
  · exact ((K.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hmap).trans eK)
  · exact (QuotientGroup.congr _ _ e hmap).trans eQ

theorem isExtOf_of_hom {X : Type*} [Group X] (f : X →* Equiv.Perm (Fin 6))
    (hrange : f.range = alternatingGroup (Fin 6)) (hker : Nat.card f.ker = 3) :
    IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨f.ker, f.normal_ker, ⟨mulEquivOfPrimeCardEq hker ?_⟩,
    ⟨(QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)⟩⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem isExtOf_centralizer :
    IsExtOf (centralizer ((zpowers zJ : Subgroup GJ) : Set GJ)) (alternatingGroup (Fin 6))
      (Multiplicative (ZMod 3)) :=
  isExtOf_of_mulEquiv (MulEquiv.subgroupCongr (centralizer_zpowers_eq zJ))
    (isExtOf_of_hom act6 range_act6 card_ker_act6)

theorem z_mem_NZ : zJ ∈ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) :=
  le_normalizer (mem_zpowers zJ)

theorem ker_act10 :
    act10.ker = (zpowers zJ).subgroupOf (normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) := by
  ext ⟨g, hg⟩
  rw [act10, mem_ker_setAct, mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.2.2.1 (normalizer_Z ▸ hg)
    have hck := allLt_spec chkTen_spec.1 hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hck
    rcases hck.2 with h1 | h1
    · rw [fixesSets_of_image sets_spec.2.2.2.1 sets_spec.2.2.2.2.1 hr h] at h1
      exact absurd h1 Bool.noConfusion
    · exact inZ_spec hr h1
  · intro h
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp h
    have hz : (⟨zJ, z_mem_NZ⟩ : normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) ∈
        act10.ker := by
      rw [act10, mem_ker_setAct]
      exact image_of_fixesSets sets_spec.2.2.2.1 sets_spec.2.2.2.2.1 rep_z sets_spec.2.2.2.2.2
    have hzn := Subgroup.zpow_mem _ hz n
    rw [act10, mem_ker_setAct] at hzn
    exact hzn

theorem card_ker_act10 : Nat.card act10.ker = 3 := by
  rw [ker_act10, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr z_mem_NZ)).toEquiv,
    card_zpowers_z]

theorem gNZ_mem (k : ℕ) (hk : k < gensNZArr.size) :
    gElt gensNZArr gensNZ_spec k hk ∈ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) := by
  rw [normalizer_Z]
  exact gElt_mem _ _ k hk

theorem act10_gen (k : ℕ) (hk : k < gensNZArr.size)
    (hm : gElt gensNZArr gensNZ_spec k hk ∈ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) :
    ∀ i, act10 ⟨gElt gensNZArr gensNZ_spec k hk, hm⟩ i =
      listFun 10 (by norm_num) (sigNZ.getD k []) i := by
  intro i
  have hk3 : k < 3 := hk
  have hl : ∀ i < 10, (sigNZ.getD k []).getD i 0 < 10 := by
    interval_cases k <;> decide
  have hact := allLt_spec chkTen_spec.2 hk
  rw [act10, setAct_eq_of_image F10_injective image_F10 (h := ⟨_, hm⟩) (σ := Equiv.ofBijective
      (listFun 10 (by norm_num) (sigNZ.getD k []))
      ((Finite.injective_iff_bijective).1 (by interval_cases k <;> decide)))
    (fun j => image_actsBy sets_spec.2.2.2.1 sets_spec.2.2.2.2.1 (rep_elA (gensNZ_spec k hk)) hl
      hact j)]
  rfl

@[expose] def gf9 (n : ℕ) : GF9 := GF9.ofNat' n

@[expose] def matOf (q : ℕ × ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) GF9 :=
  !![gf9 q.1, gf9 q.2.1; gf9 q.2.2.1, gf9 q.2.2.2]

theorem det_matOf (k : ℕ) (hk : k < 3) : (matOf (mats.getD k (1, 0, 0, 1))).det ≠ 0 := by
  interval_cases k <;> decide

@[expose] noncomputable def glOf (k : ℕ) (hk : k < 3) : GL (Fin 2) GF9 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_matOf k hk)

@[expose] noncomputable def psi10 :
    normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) →* Equiv.Perm (Option GF9) :=
  (Equiv.permCongrHom lamE).toMonoidHom.comp act10

theorem glOf_val (k : ℕ) (hk : k < 3) :
    ((glOf k hk : GL (Fin 2) GF9) : Matrix (Fin 2) (Fin 2) GF9) =
      matOf (mats.getD k (1, 0, 0, 1)) :=
  rfl

theorem mob_gen (k : ℕ) (hk : k < 3) (o : Option GF9) :
    mobHom GF9 (ProjGenLinGroup.mk (glOf k hk)) o =
      lamE (listFun 10 (by norm_num) (sigNZ.getD k []) (lamE.symm o)) := by
  cases o with
  | none =>
    rw [mobHom_mk_none, glOf_val]
    interval_cases k <;> decide
  | some x =>
    rw [mobHom_mk_some, glOf_val]
    revert x
    interval_cases k <;> decide

theorem psi10_gen (k : ℕ) (hk : k < gensNZArr.size)
    (hm : gElt gensNZArr gensNZ_spec k hk ∈ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) :
    psi10 ⟨gElt gensNZArr gensNZ_spec k hk, hm⟩ = mobHom GF9 (ProjGenLinGroup.mk (glOf k hk)) := by
  ext o : 1
  rw [mob_gen k hk o, psi10, MonoidHom.comp_apply]
  change lamE (act10 _ (lamE.symm o)) = _
  rw [act10_gen k hk hm]

theorem range_psi10_le : psi10.range ≤ (mobHom GF9).range := by
  refine range_le_of_closure (by rw [normalizer_Z, subOf_eq_closure_gElt gensNZArr gensNZ_spec])
    psi10 _ ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [psi10_gen k hk _]
  exact ⟨_, rfl⟩

theorem ker_psi10 : psi10.ker = act10.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, psi10, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (Equiv.permCongrHom lamE).injective]

theorem card_GF9 : Fintype.card GF9 = 9 := by decide

theorem card_PGL_GF9 : Nat.card PGL(Fin 2, GF9) = 720 := by
  have h := card_PGL_two GF9
  rw [card_GF9] at h
  omega

theorem card_range_psi10 : Nat.card psi10.range = 720 := by
  have h := card_range_of_ker psi10
  rw [ker_psi10, card_ker_act10, card_normalizer_Z] at h
  omega

theorem range_psi10 : psi10.range = (mobHom GF9).range := by
  apply Subgroup.eq_of_le_of_card_ge range_psi10_le
  rw [card_range_psi10, ← Nat.card_congr (MonoidHom.ofInjective (mobHom_injective GF9)).toEquiv,
    card_PGL_GF9]

@[expose] noncomputable def gf9Equiv : GF9 ≃+* GaloisField 3 2 :=
  haveI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card (α := GaloisField 3 2), GaloisField.card 3 2 (by norm_num),
      card_GF9]
    norm_num)

theorem quotient_normalizer_Z :
    Nonempty (normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) ⧸
      (zpowers zJ).subgroupOf (normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) ≃*
        Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_act10.symm.trans ker_psi10.symm)).trans
    ((QuotientGroup.quotientKerEquivRange psi10).trans ((MulEquiv.subgroupCongr range_psi10).trans
      ((MonoidHom.ofInjective (mobHom_injective GF9)).symm.trans (pglCongr gf9Equiv))))⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
