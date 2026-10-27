module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoElemAbelian
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.Line63

variable {K : Type} [Field K] [Finite K]

noncomputable def e6QTwoBstarConjAction {G : Type} [Group G] {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) : Bs →* MulAut L :=
  (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hNL)

theorem e6QTwoBstarConjAction_apply {G : Type} [Group G] {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : Bs) (l : L) :
    ((e6QTwoBstarConjAction hNL b) l : G) = (b : G) * l * (b : G)⁻¹ := by
  have hb : (b : G) ∈ Subgroup.normalizer (L : Set G) := hNL b.2
  have hmem : (b : G) * (l : G) * (b : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hb (l : G)).mp l.2
  change (((Subgroup.normalizerMonoidHom (H := L))
    (Subgroup.inclusion hNL b)) l : G) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem e6QTwoBstarConjAction_eq_one_iff {G : Type} [Group G] {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : Bs) :
    e6QTwoBstarConjAction hNL b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := congrArg (fun f : MulAut L => f ⟨l, hl⟩) h1
    rw [MulAut.one_apply] at h2
    have h2'' : ((e6QTwoBstarConjAction hNL b) ⟨l, hl⟩ : G) = l := by rw [h2]
    have h3 := e6QTwoBstarConjAction_apply hNL b ⟨l, hl⟩
    have h4 : (b : G) * l * (b : G)⁻¹ = l := by
      rw [h3] at h2''
      exact h2''
    calc l * (b : G) = ((b : G) * l * (b : G)⁻¹) * (b : G) := by rw [h4]
      _ = (b : G) * l := by group
  · intro hb
    have hmem : Subgroup.inclusion hNL b ∈ (Subgroup.normalizerMonoidHom (H := L)).ker := by
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa using hb
    simpa [e6QTwoBstarConjAction, MonoidHom.mem_ker] using hmem

theorem e6QTwoCenterMapMulAut {L' : Type} [Group L'] (a : MulAut L') :
    (Subgroup.center L').map (a : L' →* L') = Subgroup.center L' := by
  simpa using Subgroup.map_center_eq a

noncomputable def e6QTwoQuotCenterAutHom (L' : Type) [Group L'] :
    MulAut L' →* MulAut (L' ⧸ Subgroup.center L') where
  toFun a := QuotientGroup.congr (Subgroup.center L') (Subgroup.center L') a
    (Subgroup.map_center_eq a)
  map_one' := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center L') x
    rw [QuotientGroup.congr_mk]
    simp
  map_mul' a b := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center L') x
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      QuotientGroup.congr_mk, MulAut.mul_apply]

theorem e6QTwoQuotCenterAutHom_mk {L' : Type} [Group L'] (a : MulAut L') (l : L') :
    e6QTwoQuotCenterAutHom L' a (QuotientGroup.mk' (Subgroup.center L') l) =
      QuotientGroup.mk' (Subgroup.center L') (a l) :=
  QuotientGroup.congr_mk' (Subgroup.center L') (Subgroup.center L') a
    (Subgroup.map_center_eq a) l

theorem e6QTwoQuotCenterAutHom_injective {L' : Type} [Group L']
    (hperf : commutator L' = ⊤) : Function.Injective (e6QTwoQuotCenterAutHom L') := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hfixl : ∀ l : L', l⁻¹ * a l ∈ Subgroup.center L' := by
    intro l
    have h := e6QTwoQuotCenterAutHom_mk a l
    rw [ha, MulAut.one_apply] at h
    have h2 : QuotientGroup.mk' (Subgroup.center L') (l⁻¹ * a l) = 1 := by
      rw [map_mul, map_inv, ← h, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (l⁻¹ * a l)).mp h2
  letI : CommGroup (Subgroup.center L') :=
    { (inferInstance : Group (Subgroup.center L')) with
      mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp x.2 y).symm }
  let f : L' →* Subgroup.center L' :=
    { toFun := fun l => ⟨l⁻¹ * a l, hfixl l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show (l * m)⁻¹ * a (l * m) = l⁻¹ * a l * (m⁻¹ * a m)
        have hc := Subgroup.mem_center_iff.mp (hfixl l) m⁻¹
        calc (l * m)⁻¹ * a (l * m) = m⁻¹ * (l⁻¹ * a l) * a m := by rw [map_mul]; group
          _ = (l⁻¹ * a l) * m⁻¹ * a m := by rw [hc]
          _ = l⁻¹ * a l * (m⁻¹ * a m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
  ext l
  have h1 : l⁻¹ * a l = 1 := congrArg Subtype.val (hf l)
  exact (inv_mul_eq_one.mp h1).symm

theorem e6QTwoQuotCenterAutHom_conj {L' : Type} [Group L'] (l : L') :
    e6QTwoQuotCenterAutHom L' (MulAut.conj l) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center L') l) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L') x
  rw [e6QTwoQuotCenterAutHom_mk]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem e6QTwoMkEqMkOfMemCenter {L' : Type} [Group L'] {x y : L'}
    (h : x * y⁻¹ ∈ Subgroup.center L') :
    QuotientGroup.mk' (Subgroup.center L') x = QuotientGroup.mk' (Subgroup.center L') y := by
  have h1 : QuotientGroup.mk' (Subgroup.center L') (x * y⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (x * y⁻¹)).mpr h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem e6QTwoConjEqConjOfCommute {L' : Type} [Group L'] {a : MulAut L'} {l : L'}
    (hcomm : a * MulAut.conj l = MulAut.conj l * a) :
    MulAut.conj l = MulAut.conj (a⁻¹ l) := by
  ext y
  have hpt : a (l * y * l⁻¹) = l * (a y) * l⁻¹ := by
    have h := congrArg (fun f : MulAut L' => f y) hcomm
    simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] using h
  calc l * y * l⁻¹ = a⁻¹ (a (l * y * l⁻¹)) := by simp
    _ = a⁻¹ (l * (a y) * l⁻¹) := by rw [hpt]
    _ = a⁻¹ l * y * (a⁻¹ l)⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulAut.inv_apply_self]

theorem e6QTwoMemCenterMulInvOfConjEq {L' : Type} [Group L'] {x y : L'}
    (h : MulAut.conj x = MulAut.conj y) : x * y⁻¹ ∈ Subgroup.center L' := by
  have h1 : MulAut.conj (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [Subgroup.mem_center_iff]
  intro g
  have h2 : (x * y⁻¹) * g * (x * y⁻¹)⁻¹ = g := by
    have := congrArg (fun f : MulAut L' => f g) h1
    simpa only [MulAut.conj_apply, MulAut.one_apply] using this
  calc g * (x * y⁻¹) = ((x * y⁻¹) * g * (x * y⁻¹)⁻¹) * (x * y⁻¹) := by rw [h2]
    _ = (x * y⁻¹) * g := by group

theorem e6QTwoEqOneOfPowThreeOfPowTwo {L' : Type} [Group L'] {y : L'} {k : ℕ}
    (h3 : y ^ 3 = 1) (h2 : y ^ 2 ^ k = 1) : y = 1 := by
  have hdvd3 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hdvd2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdvd2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd2
    norm_num at this

private theorem e6QTwoExistsFixedLiftMemCenter {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA3 : IsPGroup 3 A) (hZ2 : IsPGroup 2 (Subgroup.center L'))
    {H : Subgroup L'} (hH : ∀ a ∈ A, ∀ h ∈ H, a h ∈ H)
    {xb : L' ⧸ Subgroup.center L'}
    (hxb : xb ∈ H.map (QuotientGroup.mk' (Subgroup.center L')))
    (hfix : ∀ a ∈ A, e6QTwoQuotCenterAutHom L' a xb = xb) :
    ∃ x ∈ H, QuotientGroup.mk' (Subgroup.center L') x = xb ∧ ∀ a ∈ A, a x = x := by
  obtain ⟨x₀, hx₀H, rfl⟩ := hxb
  set Y : Subgroup L' := H ⊓ Subgroup.center L' with hY
  have hYc : Y ≤ Subgroup.center L' := fun y hy => hy.2
  have hY2 : IsPGroup 2 Y := hZ2.to_le inf_le_right
  have hYA : ∀ a ∈ A, ∀ y ∈ Y, a y ∈ Y := fun a ha y hy => by
    refine ⟨hH a ha y hy.1, ?_⟩
    have hmem : a y ∈ (Subgroup.center L').map (a : L' →* L') :=
      Subgroup.mem_map_of_mem (a : L' →* L') hy.2
    rwa [e6QTwoCenterMapMulAut] at hmem
  have hT3 : IsPGroup 3 (⊥ : Subgroup L') := fun g => ⟨0, Subsingleton.elim _ _⟩
  have hTA : ∀ a ∈ A, ∀ t ∈ (⊥ : Subgroup L'), a t = t := fun a _ t ht => by
    rw [Subgroup.mem_bot] at ht
    rw [ht, map_one]
  have hn₀ : ∀ a ∈ A, x₀ * (a x₀)⁻¹ ∈ (⊥ : Subgroup L') ⊔ Y := by
    intro a ha
    refine Subgroup.mem_sup_right ?_
    have h1 : (QuotientGroup.mk' (Subgroup.center L') x₀ : L' ⧸ Subgroup.center L') =
        QuotientGroup.mk' (Subgroup.center L') (a x₀) := by
      rw [← hfix a ha, e6QTwoQuotCenterAutHom_mk]
    have h2 : QuotientGroup.mk' (Subgroup.center L') (x₀ * (a x₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hc : x₀ * (a x₀)⁻¹ ∈ Subgroup.center L' :=
      (QuotientGroup.eq_one_iff (x₀ * (a x₀)⁻¹)).mp h2
    exact ⟨H.mul_mem hx₀H (H.inv_mem (hH a ha x₀ hx₀H)), hc⟩
  obtain ⟨z, hz, hzT⟩ := exists_lift_weyl hYc hY2 hT3 hA3 hYA hTA x₀ hn₀
  refine ⟨x₀ * z, H.mul_mem hx₀H hz.1, ?_, fun a ha => ?_⟩
  · have hz1 : QuotientGroup.mk' (Subgroup.center L') z = 1 :=
      (QuotientGroup.eq_one_iff z).mpr hz.2
    rw [map_mul, hz1, mul_one]
  · have h1 := hzT a ha
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1.symm

theorem e6QTwoExistsFixedCubeLiftCenter {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA3 : IsPGroup 3 A) (hZ2 : IsPGroup 2 (Subgroup.center L'))
    {H : Subgroup L'} (hH : ∀ a ∈ A, ∀ h ∈ H, a h ∈ H)
    {xb : L' ⧸ Subgroup.center L'}
    (hxb : xb ∈ H.map (QuotientGroup.mk' (Subgroup.center L')))
    (hfix : ∀ a ∈ A, e6QTwoQuotCenterAutHom L' a xb = xb) (hx3 : xb ^ 3 = 1) :
    ∃ x ∈ H, QuotientGroup.mk' (Subgroup.center L') x = xb ∧ x ^ 3 = 1 ∧ ∀ a ∈ A, a x = x := by
  obtain ⟨x₁, hx₁H, hx₁, hx₁fix⟩ := e6QTwoExistsFixedLiftMemCenter hA3 hZ2 hH hxb hfix
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
  set m : ℕ := 4 ^ k with hm
  have hm3 : m % 3 = 1 := by rw [hm, Nat.pow_mod]; norm_num
  have h13 : x₁ ^ 3 ∈ Subgroup.center L' := by
    have h2 : QuotientGroup.mk' (Subgroup.center L') (x₁ ^ 3) = 1 := by
      rw [map_pow, hx₁, hx3]
    exact (QuotientGroup.eq_one_iff (x₁ ^ 3)).mp h2
  have hord : orderOf (x₁ ^ 3) ∣ 2 ^ k := by
    have h1 : orderOf (x₁ ^ 3) = orderOf (⟨x₁ ^ 3, h13⟩ : Subgroup.center L') :=
      Subgroup.orderOf_coe (⟨x₁ ^ 3, h13⟩ : Subgroup.center L')
    rw [h1, ← hk]
    exact orderOf_dvd_natCard _
  have h24 : 2 ^ k ∣ m := by
    rw [hm, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have hmx : (x₁ ^ 3) ^ m = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact dvd_trans hord h24
  obtain ⟨j, hj⟩ : ∃ j, m = 3 * j + 1 := ⟨m / 3, by omega⟩
  refine ⟨x₁ ^ m, H.pow_mem hx₁H m, ?_, ?_, fun a ha => by rw [map_pow, hx₁fix a ha]⟩
  · rw [map_pow, hx₁, hj, pow_succ, pow_mul, hx3, one_pow, one_mul]
  · rw [← pow_mul, mul_comm, pow_mul, hmx]

theorem e6QTwoMulAutConjCongr {L' R : Type*} [Group L'] [Group R] (e : L' ≃* R) (l : L') :
    MulAut.conj (e l) = (MulAut.congr e) (MulAut.conj l) := by
  ext r
  obtain ⟨x, rfl⟩ := e.surjective r
  rw [MulAut.conj_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
    MulAut.conj_apply, map_mul, map_inv]

theorem e6QTwoMulAutCongrApply {L' R : Type*} [Group L'] [Group R] (e : L' ≃* R)
    (f : MulAut L') (x : L') : (MulAut.congr e) f (e x) = e (f x) := by
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

theorem e6QTwoLargeEvenInducesEqOfForallExists {R : Type} {L' : Type*} [Group L'] [Group R]
    {θ : L' ⧸ Subgroup.center L' ≃* R} {rel : L' → L' → Prop}
    (hrel : ∀ l : L', ∃ l' : L', rel l l') {φ φ' : MulAut R}
    (hφ : LargeEvenInduces θ rel φ) (hφ' : LargeEvenInduces θ rel φ') : φ = φ' := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center L') q
  obtain ⟨l', hl'⟩ := hrel l
  rw [hφ l l' hl', hφ' l l' hl']

private theorem e6QTwoFrameActConjOfGGFrameActs {d n : ℕ} {h : UnitaryFieldData 2 n K}
    {Q : GL (Fin d) K}
    {hQ : Q ∈ primeFormUnitary h (RankThree.PartOne.KCUnitaryModel.idGram K d)}
    {r : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} {σ : Fin d → Kˣ}
    (hact : SURep.GGFrameActs (InndiagSU.frameMk h Q hQ) r σ) :
    TableBUD.FrameAct h Q hQ (MulAut.conj r) σ := by
  obtain ⟨hσ, hfr⟩ := hact
  intro u v huv
  rw [MulAut.conj_apply, hfr u v huv]

theorem e6QTwoFrameActMulComm {d n : ℕ} {h : UnitaryFieldData 2 n K}
    {Q : GL (Fin d) K}
    {hQ : Q ∈ primeFormUnitary h (RankThree.PartOne.KCUnitaryModel.idGram K d)}
    {e e' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    {σ σ' : Fin d → Kˣ} (he : TableBUD.FrameAct h Q hQ e σ)
    (he' : TableBUD.FrameAct h Q hQ e' σ')
    (hσ : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1)
    (hσ' : ∀ k, ((σ' k : Kˣ) : K) ^ (2 ^ n + 1) = 1)
    (hcomm : σ * σ' = σ' * σ) : e * e' = e' * e := by
  have h1 : TableBUD.FrameAct h Q hQ (e * e') (σ * σ') := he.mul he' hσ'
  have h2 : TableBUD.FrameAct h Q hQ (e' * e) (σ' * σ) := he'.mul he hσ
  rw [← hcomm] at h2
  have hnorm : ∀ k, ((σ * σ' : Fin d → Kˣ) k : K) ^ (2 ^ n + 1) = 1 := by
    intro k
    rw [Pi.mul_apply, Units.val_mul, mul_pow, hσ k, hσ' k, one_mul]
  exact TableBUD.FrameAct.unique hnorm h1 h2

private noncomputable def e6QTwoProdUnitsHom : (Fin 6 → Kˣ) →* Kˣ where
  toFun σ := ∏ k, σ k
  map_one' := by simp
  map_mul' σ τ := Finset.prod_mul_distrib

noncomputable def e6QTwoTorParamSubgroup : Subgroup (Fin 6 → Kˣ) := e6QTwoProdUnitsHom.ker

private theorem e6QTwoMemTorParamSubgroup {σ : Fin 6 → Kˣ} :
    σ ∈ e6QTwoTorParamSubgroup ↔ ∏ k, σ k = 1 := by
  rw [e6QTwoTorParamSubgroup, MonoidHom.mem_ker]; rfl

private theorem e6QTwoDiagHomMemUnitarySU (hK : Nat.card K = 4) {σ : Fin 6 → Kˣ}
    (hprod : ∏ k, σ k = 1) :
    SectionRank.OddCover.diagHom 6 σ ∈
      ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6 := by
  have h : UnitaryFieldData 2 1 K := USixTwo.fieldDataFour hK
  have hnorm : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
    intro k
    rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      USixTwo.cube_unit_eq_one hK, Units.val_one]
  refine TableBUE.mem_unitarySU_of_mem_primeFormUnitary h
    (TableBUD.diagHom_mem_primeFormUnitary h hnorm) ?_
  rw [SectionRank.OddCover.det_diagHom, ← Units.coe_prod, hprod, Units.val_one]

private noncomputable def e6QTwoTorParamToSU (hK : Nat.card K = 4) :
    e6QTwoTorParamSubgroup (K := K) →*
      ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) where
  toFun σ := ⟨SectionRank.OddCover.diagHom 6 σ.1,
    e6QTwoDiagHomMemUnitarySU hK (e6QTwoMemTorParamSubgroup.mp σ.2)⟩
  map_one' := by ext; simp
  map_mul' σ τ := by ext; simp [map_mul]

private noncomputable def e6QTwoTorSUU :
    Subgroup ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
  (TauCeti.diagonalTorus K 6).comap
    (ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6).subtype

private theorem e6QTwoRangeTorParamToSU (hK : Nat.card K = 4) :
    (e6QTwoTorParamToSU hK).range = e6QTwoTorSUU := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    rw [e6QTwoTorSUU, Subgroup.mem_comap]
    refine TauCeti.mem_diagonalTorus_iff.mpr ?_
    rw [show ((ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6).subtype (e6QTwoTorParamToSU hK σ) :
        GL (Fin 6) K) = SectionRank.OddCover.diagHom 6 σ.1 from rfl]
    rw [SectionRank.OddCover.coe_diagHom]
    exact Matrix.isDiag_diagonal _
  · intro hx
    rw [e6QTwoTorSUU, Subgroup.mem_comap] at hx
    obtain ⟨t, ht⟩ := TableBUE.exists_diagHom_of_isDiag
      (TauCeti.mem_diagonalTorus_iff.mp hx)
    have hdet : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
      (ClassicalGroups.UnitaryFlag.mem_unitarySU_iff (USixTwo.fieldDataFour hK)).mp x.2 |>.1
    have hdet2 : ((SectionRank.OddCover.diagHom 6 t : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [← ht]
      exact hdet
    rw [SectionRank.OddCover.det_diagHom] at hdet2
    have hprod : ∏ k, t k = 1 := by
      apply Units.ext
      rw [Units.coe_prod]
      exact hdet2
    refine ⟨⟨t, e6QTwoMemTorParamSubgroup.mpr hprod⟩, ?_⟩
    apply Subtype.ext
    rw [e6QTwoTorParamToSU]
    exact ht.symm

private noncomputable def e6QTwoStdTorusHom (hK : Nat.card K = 4) :
    e6QTwoTorParamSubgroup (K := K) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  (InndiagSU.projU 1 6 K).comp (e6QTwoTorParamToSU hK)

private theorem e6QTwoRangeStdTorusHom (hK : Nat.card K = 4) :
    (e6QTwoStdTorusHom hK).range = USixTwo.torU K := by
  rw [e6QTwoStdTorusHom, MonoidHom.range_comp, e6QTwoRangeTorParamToSU, USixTwo.torU]
  rfl

noncomputable def e6QTwoFrameTorusHom (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6)) :
    e6QTwoTorParamSubgroup (K := K) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  (InndiagSU.frameMk (USixTwo.fieldDataFour hK) Q hQ).comp (e6QTwoTorParamToSU hK)

theorem e6QTwoFrameActFrameTorusHom (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (σ : e6QTwoTorParamSubgroup) :
    TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
      (MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ)) σ.1 := by
  have hnorm : ∀ k, ((σ.1 k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
    intro k
    rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
      USixTwo.cube_unit_eq_one hK, Units.val_one]
  let x : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6) :=
    (TableBUE.conjSU (USixTwo.fieldDataFour hK) Q hQ).symm (e6QTwoTorParamToSU hK σ)
  have hx : ((TableBUE.conjSU (USixTwo.fieldDataFour hK) Q hQ x :
      ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) : GL (Fin 6) K) =
      SectionRank.OddCover.diagHom 6 σ.1 := by
    rw [show TableBUE.conjSU (USixTwo.fieldDataFour hK) Q hQ x = e6QTwoTorParamToSU hK σ
      from MulEquiv.apply_symm_apply _ _]
    rfl
  have hact := TableBUI.frameActs_of_eq (USixTwo.fieldDataFour hK) Q hQ hx hnorm
  have hb : (InndiagSU.projU 1 6 K) x = e6QTwoFrameTorusHom hK Q hQ σ := rfl
  rw [hb] at hact
  exact e6QTwoFrameActConjOfGGFrameActs hact

private noncomputable def e6QTwoFrameChange (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6)) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  TableBUE.conjProj (USixTwo.fieldDataFour hK) Q hQ

private theorem e6QTwoFrameChangeApply (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (x : ↥(ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6)) :
    e6QTwoFrameChange hK Q hQ ((InndiagSU.projU 1 6 K) x) =
      (InndiagSU.projU 1 6 K)
        ((TableBUE.conjSU (USixTwo.fieldDataFour hK) Q hQ) x) :=
  TableBUE.conjProj_mk (USixTwo.fieldDataFour hK) Q hQ x

private theorem e6QTwoFrameTorusHomApplyEq (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (σ : e6QTwoTorParamSubgroup) :
    e6QTwoFrameTorusHom hK Q hQ σ = (e6QTwoFrameChange hK Q hQ).symm (e6QTwoStdTorusHom hK σ) := by
  apply (e6QTwoFrameChange hK Q hQ).injective
  rw [MulEquiv.apply_symm_apply]
  rw [e6QTwoFrameTorusHom, e6QTwoStdTorusHom, MonoidHom.comp_apply, MonoidHom.comp_apply]
  rw [InndiagSU.frameMk_apply, e6QTwoFrameChangeApply, MulEquiv.apply_symm_apply]

theorem e6QTwoCardRangeFrameTorusHom (hK : Nat.card K = 4) (Q : GL (Fin 6) K)
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6)) :
    Nat.card (e6QTwoFrameTorusHom hK Q hQ).range = 3 ^ 4 := by
  have hhom : e6QTwoFrameTorusHom hK Q hQ =
      (e6QTwoFrameChange hK Q hQ).symm.toMonoidHom.comp (e6QTwoStdTorusHom hK) := by
    ext σ
    exact e6QTwoFrameTorusHomApplyEq hK Q hQ σ
  calc Nat.card (e6QTwoFrameTorusHom hK Q hQ).range
      = Nat.card (Subgroup.map (e6QTwoFrameChange hK Q hQ).symm.toMonoidHom
          (e6QTwoStdTorusHom hK).range) := by rw [hhom, MonoidHom.range_comp]
    _ = Nat.card (e6QTwoStdTorusHom hK).range :=
        Subgroup.card_map_of_injective (e6QTwoFrameChange hK Q hQ).symm.injective
    _ = 3 ^ 4 := by rw [e6QTwoRangeStdTorusHom, USixTwo.card_torU hK]

end CFSG.StandardType.E6QTwo

end
