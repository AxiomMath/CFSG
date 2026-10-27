module

public import CFSG.Walter.Bender1970.S3.FStar
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedFittingSubgroupConjugate
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

theorem primesOfOrder_eq_singleton {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) : primesOfOrder X = {p} := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hX1 hk
  ext q
  simp only [primesOfOrder, Set.mem_ofPred_eq, Set.mem_singleton_iff, hk,
    Nat.primeFactors_prime_pow hk0 hp, Finset.mem_singleton]

theorem exists_isPGroup_of_card_primesOfOrder_eq_one {X : Subgroup G}
    (h : Nat.card (primesOfOrder X) = 1) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p X ∧ X ≠ ⊥ ∧ primesOfOrder X = {p} := by
  obtain ⟨p, hp⟩ := Set.ncard_eq_one.mp h
  have hpmem : p ∈ primesOfOrder X := hp ▸ Set.mem_singleton p
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  refine ⟨p, hpp, isPGroup_of_primeFactors_subset_singleton X hpp fun r hr => ?_, ?_, hp⟩
  · have : r ∈ primesOfOrder X := hr
    rw [hp] at this
    exact this
  · rintro rfl
    simp [primesOfOrder] at hpmem

theorem isPGroup_of_primesOfOrder_subset {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h : primesOfOrder X ⊆ {p}) : IsPGroup p X :=
  isPGroup_of_primeFactors_subset_singleton X hp fun _ hr => h hr

theorem primesOfOrder_subset_of_isPGroup {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p X) : primesOfOrder X ⊆ {p} := by
  by_cases hX1 : X = ⊥
  · subst hX1
    intro q hq
    simp [primesOfOrder] at hq
  · rw [primesOfOrder_eq_singleton hp hX hX1]

theorem one_le_card_primesOfOrder {X : Subgroup G} (hX : X ≠ ⊥) :
    1 ≤ Nat.card (primesOfOrder X) := by
  have hfin : (primesOfOrder X).Finite := (Nat.card X).primeFactors.finite_toSet
  have := hfin.to_subtype
  obtain ⟨q, hq⟩ := primesOfOrder_nonempty_of_ne_bot X hX
  have : Nonempty (primesOfOrder X) := ⟨⟨q, hq⟩⟩
  exact Nat.card_pos

theorem card_primesOfOrder_le_one_of_isPGroup {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p X) : Nat.card (primesOfOrder X) ≤ 1 := by
  by_cases hX1 : X = ⊥
  · subst hX1
    have : primesOfOrder (⊥ : Subgroup G) = ∅ := by
      ext q
      simp [primesOfOrder]
    rw [this]
    simp
  · rw [primesOfOrder_eq_singleton hp hX hX1]
    simp

theorem generalizedFittingSubgroupOf_ne_bot {X : Subgroup G} (hX : X ≠ ⊥) :
    generalizedFittingSubgroupOf X ≠ ⊥ := by
  intro h
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq X, Subgroup.map_eq_bot_iff_of_injective _
    X.subtype_injective] at h
  have hC := CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le (G := X)
  rw [h] at hC
  apply hX
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp (hC hmem)))

theorem primesOfOrder_generalizedFitting_eq_singleton {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p (generalizedFittingSubgroupOf X)) (hX1 : X ≠ ⊥) :
    primesOfOrder (generalizedFittingSubgroupOf X) = {p} :=
  primesOfOrder_eq_singleton hp hX (generalizedFittingSubgroupOf_ne_bot hX1)

omit [Finite G] in
theorem map_subtype_centralizer_subgroupOf {X U : Subgroup G} (hUX : U ≤ X) :
    (Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      X ⊓ Subgroup.centralizer (U : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X) := hy
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff] at hy' ⊢
    intro u hu
    exact congrArg Subtype.val (hy' ⟨u, hUX hu⟩ (Subgroup.mem_subgroupOf.mpr hu))
  · rintro ⟨hxX, hxC⟩
    have hxC' : x ∈ Subgroup.centralizer (U : Set G) := hxC
    refine ⟨⟨x, hxX⟩, ?_, rfl⟩
    show (⟨x, hxX⟩ : X) ∈ Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X)
    rw [Subgroup.mem_centralizer_iff] at hxC' ⊢
    intro u hu
    exact Subtype.ext (hxC' u (Subgroup.mem_subgroupOf.mp hu))

theorem isPGroup_generalizedFitting_inf_centralizer {X U : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p (generalizedFittingSubgroupOf X)) (hUX : U ≤ X) (hU : IsPGroup p U) :
    IsPGroup p (generalizedFittingSubgroupOf (X ⊓ Subgroup.centralizer (U : Set G))) := by
  have hX' : IsPGroup p (generalizedFittingSubgroupOf (⊤ : Subgroup X)) := by
    have e : generalizedFittingSubgroupOf (⊤ : Subgroup X) ≃* generalizedFittingSubgroupOf X :=
      ((generalizedFittingSubgroupOf (⊤ : Subgroup X)).equivMapOfInjective X.subtype
        X.subtype_injective).trans
        (MulEquiv.subgroupCongr (generalizedFittingSubgroupOf_subgroup_top_eq X))
    exact hX.of_equiv e.symm
  have hU' : IsPGroup p (U.subgroupOf X) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have h := (bender1970_1_8_centralizerNormalizer_pGroup (G := X) p hp hX' _ hU').1
  have hmap := h.map X.subtype
  rwa [generalizedFittingSubgroupOf_map_subtype', map_subtype_centralizer_subgroupOf hUX] at hmap

omit [Finite G] in
theorem commutatorElement_eq_sq_of_conj_eq_inv {t x : G} (h : t * x⁻¹ * t⁻¹ = x) :
    ⁅x, t⁆ = x ^ 2 := by
  rw [commutatorElement_def, pow_two, mul_assoc, mul_assoc, ← mul_assoc t, h]

omit [Finite G] in
theorem isMulCommutative_of_conj_eq_inv {P : Subgroup G} {t : G}
    (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) : IsMulCommutative P := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h1 := hinv _ (P.mul_mem a.2 b.2)
  rw [show t * ((a : G) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group, hinv _ a.2,
    hinv _ b.2] at h1
  have h2 : (a : G) * b = ((a : G)⁻¹ * (b : G)⁻¹)⁻¹ := by rw [h1]; group
  rw [Subgroup.coe_mul, Subgroup.coe_mul, h2]
  group

theorem odd_card_of_conj_eq_inv {P : Subgroup G} {t : G}
    (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹)
    (hfix : P ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) : Odd (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (even_iff_two_dvd.mp hodd)
  have hx2 : (x : G) * x = 1 := by
    have := pow_orderOf_eq_one (x : G)
    rw [Subgroup.orderOf_coe, hx, pow_two] at this
    exact this
  have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hmem : (x : G) ∈ P ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := hinv _ x.2
    rw [hxinv] at h
    calc (x : G) * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  rw [hfix, Subgroup.mem_bot] at hmem
  have hx1 : x = 1 := Subtype.ext hmem
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

omit [Finite G] in
theorem commutator_zpowers_eq_self_of_conj_eq_inv {P : Subgroup G} {t : G}
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹)
    (hodd : Odd (Nat.card P)) : ⁅P, Subgroup.zpowers t⁆ = P := by
  refine le_antisymm (commutator_zpowers_le_of_mem_normalizer htP) fun x hx => ?_
  have hxo : Odd (orderOf x) := by
    have h := Subgroup.orderOf_dvd_natCard P hx
    exact Odd.of_dvd_nat hodd h
  set y := x ^ ((orderOf x + 1) / 2)
  have hy : y ∈ P := P.pow_mem hx _
  have hy2 : y ^ 2 = x := by
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hxo.add_one), pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hty : t * y⁻¹ * t⁻¹ = y := by rw [hinv _ (P.inv_mem hy), inv_inv]
  rw [← hy2, ← commutatorElement_eq_sq_of_conj_eq_inv hty]
  exact Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers t)

theorem generalizedFitting_le_centralizer_qCoreOf {A : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hab : IsMulCommutative (qCoreOf A p)) :
    generalizedFittingSubgroupOf A ≤ Subgroup.centralizer (qCoreOf A p : Set G) := by
  refine sup_le ?_ ?_
  · rw [fittingSubgroupOf_eq_iSup_qCoreOf A]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    · exact qCoreOf_centralizer_of_ne A hp hq (Ne.symm hqp) |>.trans le_rfl
  · exact (componentLayerOf_le_centralizer_fitting A).trans
      (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf A p hp))

theorem qCoreOf_props_of_fixedPointFree {A : Subgroup G} {t : G} (htA : t ∈ A)
    (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime)
    (hfix : qCoreOf A p ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    (∀ x ∈ qCoreOf A p, t * x * t⁻¹ = x⁻¹) ∧ IsMulCommutative (qCoreOf A p) ∧
      Odd (Nat.card (qCoreOf A p)) ∧
      ⁅qCoreOf A p, Subgroup.zpowers t⁆ = qCoreOf A p ∧
      generalizedFittingSubgroupOf A ≤ Subgroup.centralizer (qCoreOf A p : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htN : t ∈ Subgroup.normalizer (qCoreOf A p : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in A p) htA
  have hinv : ∀ x ∈ qCoreOf A p, t * x * t⁻¹ = x⁻¹ := fun x hx =>
    conj_eq_inv_of_inf_centralizer_eq_bot ht2 htN hfix hx
  have hab := isMulCommutative_of_conj_eq_inv hinv
  have hodd := odd_card_of_conj_eq_inv hinv hfix
  exact ⟨hinv, hab, hodd, commutator_zpowers_eq_self_of_conj_eq_inv htN hinv hodd,
    generalizedFitting_le_centralizer_qCoreOf hp hab⟩

theorem eq_of_isPGroup_of_isPGroup {X : Subgroup G} {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hXp : IsPGroup p X) (hXr : IsPGroup r X) (hX : X ≠ ⊥) : p = r := by
  have h1 := primesOfOrder_eq_singleton hp hXp hX
  rw [primesOfOrder_eq_singleton hr hXr hX] at h1
  exact (Set.singleton_eq_singleton_iff.mp h1).symm

omit [Finite G] in
theorem isNormalIn_centralizer {K A : Subgroup G} (hK : IsNormalIn K A)
    (hCA : Subgroup.centralizer (K : Set G) ≤ A) :
    IsNormalIn (Subgroup.centralizer (K : Set G)) A := by
  refine ⟨hCA, fun a ha c hc => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have hk' : a⁻¹ * k * a ∈ K := by
    have := hK.2 a⁻¹ (A.inv_mem ha) k hk
    simpa using this
  have := hc _ hk'
  calc k * (a * c * a⁻¹) = a * ((a⁻¹ * k * a) * c) * a⁻¹ := by group
    _ = a * (c * (a⁻¹ * k * a)) * a⁻¹ := by rw [this]
    _ = a * c * a⁻¹ * k := by group

theorem generalizedFittingSubgroupOf_le_of_isNormalIn {N A : Subgroup G} (hN : IsNormalIn N A) :
    generalizedFittingSubgroupOf N ≤ generalizedFittingSubgroupOf A :=
  generalizedFittingSubgroupOf_le_of_isSubnormal hN.1 (isSubnormal_subgroupOf_of_isNormalIn hN)

theorem BenderCounterexample.normalizer_ne_top {G : Type} [Group G] [Finite G]
    (hG : BenderCounterexample G) {V : Subgroup G} (hV1 : V ≠ ⊥) (hVtop : V ≠ ⊤) :
    Subgroup.normalizer (V : Set G) ≠ ⊤ := by
  have := hG.isSimpleGroup
  intro h
  have hn : V.Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h' | h'
  · exact hV1 h'
  · exact hVtop h'

theorem BenderCounterexample.exists_isCoatom_normalizer_le {G : Type} [Group G] [Finite G]
    (hG : BenderCounterexample G) {H V : Subgroup G} (hH : IsCoatom H) (hVH : V ≤ H)
    (hV1 : V ≠ ⊥) : ∃ B : Subgroup G, IsCoatom B ∧ Subgroup.normalizer (V : Set G) ≤ B := by
  rcases eq_top_or_exists_le_coatom (Subgroup.normalizer (V : Set G)) with h | ⟨B, hB, hNB⟩
  · exact absurd h (hG.normalizer_ne_top hV1 fun h' => hH.1 (top_le_iff.mp (h' ▸ hVH)))
  · exact ⟨B, hB, hNB⟩

theorem BenderCounterexample.normalizer_eq_of_isNormalIn {G : Type} [Group G] [Finite G]
    (hG : BenderCounterexample G) {H K : Subgroup G} (hH : IsCoatom H) (hK : IsNormalIn K H)
    (hK1 : K ≠ ⊥) : Subgroup.normalizer (K : Set G) = H :=
  normalizer_eq_of_nontrivial_normal_in_coatom hG.isSimpleGroup hH hK.1 hK1
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mpr (le_normalizer_of_isNormalIn hK))

theorem qCoreOf_isNormalIn_generalizedFitting (A : Subgroup G) {p : ℕ} (hp : p.Prime) :
    IsNormalIn (qCoreOf A p) (generalizedFittingSubgroupOf A) :=
  ⟨(qCoreOf_le_fittingSubgroupOf A p hp).trans le_sup_left, fun h hh k hk =>
    (qCoreOf_normal_in A p).2 h (generalizedFittingSubgroupOf_le A hh) k hk⟩

theorem BenderCounterexample.qCoreOf_mem_benderABar {G : Type} [Group G] [Finite G]
    (hG : BenderCounterexample G) {H : Subgroup G} (hH : IsCoatom H) {t : G} (htH : t ∈ H)
    (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime) (hne : qCoreOf H p ≠ ⊥)
    (hfix : qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    qCoreOf H p ∈ benderABar H := by
  have hN := hG.normalizer_eq_of_isNormalIn hH (qCoreOf_normal_in H p) hne
  have hnF := qCoreOf_isNormalIn_generalizedFitting H hp
  refine ⟨hnF.1, isSubnormal_subgroupOf_of_isNormalIn hnF, fun _ => hN.le, fun hπ => ?_⟩
  obtain ⟨r, hr, hFr, hF1, hπr⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ
  obtain ⟨-, hab, -, -, -⟩ := qCoreOf_props_of_fixedPointFree htH ht hp hfix
  have hpr : p = r := eq_of_isPGroup_of_isPGroup hp hr (qCoreOf_isPGroup H p)
    (hFr.to_le hnF.1) hne
  have hCH : Subgroup.centralizer (qCoreOf H p : Set G) ≤ H :=
    (Subgroup.centralizer_le_normalizer _).trans hN.le
  have hCn := isNormalIn_centralizer (qCoreOf_normal_in H p) hCH
  have hFC : IsPGroup r (generalizedFittingSubgroupOf (Subgroup.centralizer
      (qCoreOf H p : Set G))) :=
    hFr.to_le (generalizedFittingSubgroupOf_le_of_isNormalIn hCn)
  have hC1 : Subgroup.centralizer (qCoreOf H p : Set G) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff, ← h]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hπr]
  exact primesOfOrder_generalizedFitting_eq_singleton hr hFC hC1

theorem primesOfOrder_map_conj (X : Subgroup G) (g : G) :
    primesOfOrder (X.map (MulAut.conj g).toMonoidHom) = primesOfOrder X := by
  ext q
  show q ∈ (Nat.card _).primeFactors ↔ q ∈ (Nat.card _).primeFactors
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]

omit [Finite G] in
theorem isSubnormal_map_conj {U F : Subgroup G} (g : G) (hU : (U.subgroupOf F).IsSubnormal) :
    ((U.map (MulAut.conj g).toMonoidHom).subgroupOf
      (F.map (MulAut.conj g).toMonoidHom)).IsSubnormal := by
  have hmem : ∀ y ∈ F.map (MulAut.conj g).toMonoidHom, g⁻¹ * y * g ∈ F := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  let ψ : (F.map (MulAut.conj g).toMonoidHom) →* F :=
    { toFun := fun y => ⟨g⁻¹ * y * g, hmem y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  convert hU.comap ψ using 1
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxy
    show g⁻¹ * (y : G) * g ∈ U
    rw [← hxy]
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_mem_benderABar {G : Type} [Group G] [Finite G] {H U : Subgroup G} (g : G)
    (hU : U ∈ benderABar H) :
    U.map (MulAut.conj g).toMonoidHom ∈ benderABar (H.map (MulAut.conj g).toMonoidHom) := by
  have hF : generalizedFittingSubgroupOf (H.map (MulAut.conj g).toMonoidHom) =
      (generalizedFittingSubgroupOf H).map (MulAut.conj g).toMonoidHom :=
    generalizedFittingSubgroupOf_conjugateSubgroup H g
  have hπ : primesOfOrder (generalizedFittingSubgroupOf (H.map (MulAut.conj g).toMonoidHom)) =
      primesOfOrder (generalizedFittingSubgroupOf H) := by
    rw [hF, primesOfOrder_map_conj]
  refine ⟨?_, ?_, fun h2 => ?_, fun h1 => ?_⟩
  · rw [hF]
    exact Subgroup.map_mono hU.1
  · rw [hF]
    exact isSubnormal_map_conj g hU.2.1
  · rw [hπ] at h2
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hU.2.2.1 h2)
  · rw [hπ] at h1 ⊢
    have hC : Subgroup.centralizer ((U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        (Subgroup.centralizer (U : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [map_centralizer_mulEquiv, Subgroup.coe_map]
      rfl
    rw [hC, ← hU.2.2.2 h1]
    have h := generalizedFittingSubgroupOf_conjugateSubgroup
      (Subgroup.centralizer (U : Set G)) g
    change primesOfOrder (generalizedFittingSubgroupOf
      (conjugateSubgroup (Subgroup.centralizer (U : Set G)) g)) = _
    rw [h, primesOfOrder_map_conj]

end CFSG.Walter
