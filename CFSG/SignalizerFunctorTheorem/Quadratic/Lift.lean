module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Thompson

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Glauberman

namespace CFSG.SignalizerFunctorTheorem.Quadratic

section CoprimeKernel

variable {H : Type*} [Group H] {K : Type*} [Group K]

private theorem lift_inf_eq_bot {q : ℕ} {Y N : Subgroup H} (hY : IsPGroup q Y)
    (hN : Nat.Coprime q (Nat.card N)) : Y ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzY, hzN⟩
  obtain ⟨k, hk⟩ := hY ⟨z, hzY⟩
  have hk' : z ^ (q ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf z ∣ q ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf z ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hzN
  have h3 : orderOf z ∣ Nat.gcd (q ^ k) (Nat.card N) := Nat.dvd_gcd h1 h2
  rw [(Nat.Coprime.pow_left k hN).gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one h3)

private theorem lift_inj_on {q : ℕ} (psi : H →* K) {Y : Subgroup H} (hY : IsPGroup q Y)
    (hkc : Nat.Coprime q (Nat.card psi.ker)) :
    ∀ x ∈ Y, ∀ y ∈ Y, psi x = psi y → x = y := by
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ Y ⊓ psi.ker :=
    ⟨Y.mul_mem (Y.inv_mem hx) hy,
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
  rw [lift_inf_eq_bot hY hkc] at hmem
  have := Subgroup.mem_bot.mp hmem
  rw [inv_mul_eq_one] at this
  exact this

end CoprimeKernel

section LiftFrattini

variable {H : Type*} [Group H] {K : Type*} [Group K]

private theorem lift_inf_normalizer [Finite H] {q : ℕ} (hq : q.Prime) (psi : H →* K)
    (hs : Function.Surjective psi) {U Y : Subgroup H} (hker : psi.ker ≤ U)
    (hkc : Nat.Coprime q (Nat.card psi.ker)) (hY : IsPGroup q Y) :
    U.map psi ⊓ Subgroup.normalizer (Y.map psi : Set K) =
      (U ⊓ Subgroup.normalizer (Y : Set H)).map psi := by
  apply le_antisymm
  · rintro x ⟨⟨u, hu, rfl⟩, hx⟩
    have hx' : psi u ∈ (Subgroup.normalizer (Y : Set H)).map psi := by
      rw [CFSG.SignalizerFunctor.Helpers.coprime_surjective_normalizer_image q hq psi hs Y hkc hY]
      exact hx
    obtain ⟨m, hm, hmu⟩ := hx'
    refine ⟨m, ⟨?_, hm⟩, hmu⟩
    have hmem : m * u⁻¹ ∈ psi.ker := MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hmu,
      mul_inv_cancel])
    simpa using U.mul_mem (hker hmem) hu
  · exact le_inf (Subgroup.map_mono inf_le_left)
      ((Subgroup.map_mono inf_le_right).trans (Subgroup.le_normalizer_map psi))

private theorem lift_inf_centralizer [Finite H] {q : ℕ} (hq : q.Prime) (psi : H →* K)
    (hs : Function.Surjective psi) {U Y : Subgroup H} (hker : psi.ker ≤ U)
    (hkc : Nat.Coprime q (Nat.card psi.ker)) (hY : IsPGroup q Y) :
    U.map psi ⊓ Subgroup.centralizer (Y.map psi : Set K) =
      (U ⊓ Subgroup.centralizer (Y : Set H)).map psi := by
  apply le_antisymm
  · rintro x hx
    have hxN : x ∈ U.map psi ⊓ Subgroup.normalizer (Y.map psi : Set K) :=
      ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
    rw [lift_inf_normalizer hq psi hs hker hkc hY] at hxN
    obtain ⟨m, ⟨hmU, hmN⟩, rfl⟩ := hxN
    refine ⟨m, ⟨hmU, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, rfl⟩
    have hc : m * y * m⁻¹ * y⁻¹ ∈ Y ⊓ psi.ker := by
      refine ⟨Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hmN y).mp hy) (Y.inv_mem hy),
        MonoidHom.mem_ker.mpr ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hx.2 (psi y) (Subgroup.mem_map_of_mem psi hy)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← this]
      group
    rw [lift_inf_eq_bot hY hkc] at hc
    have := Subgroup.mem_bot.mp hc
    rw [mul_inv_eq_one] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  · rintro x ⟨c, ⟨hcU, hcC⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem psi hcU, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hcC y hy]

end LiftFrattini

section LiftSubgroups

variable {H : Type*} [Group H] {K : Type*} [Group K]

private theorem lift_inf_centralizer_action {r : ℕ} (hr : r.Prime) (psi : H →* K)
    {U A : Subgroup H} (hA : IsElemAbelian r A) (hAU : A ≤ Subgroup.normalizer (U : Set H))
    (hcop : Nat.Coprime r (Nat.card U)) :
    (U ⊓ Subgroup.centralizer (A : Set H)).map psi =
      U.map psi ⊓ Subgroup.centralizer (A.map psi : Set K) :=
  CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image_elementary r hr psi A U hA hAU hcop

private theorem lift_card_map_of_inj_on (psi : H →* K) {W : Subgroup H}
    (hinj : ∀ x ∈ W, ∀ y ∈ W, psi x = psi y → x = y) : Nat.card (W.map psi) = Nat.card W := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (psi.subgroupMap W) ⟨?_, psi.subgroupMap_surjective W⟩)
  intro a b hab
  exact Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab))

private theorem lift_exists_pgroup [Finite H] [Finite K] {q : ℕ} (hq : q.Prime) (psi : H →* K)
    (hkc : Nat.Coprime q (Nat.card psi.ker)) {S : Subgroup H} {Wb : Subgroup K}
    (hW : IsPGroup q Wb) (hWS : Wb ≤ S.map psi) :
    ∃ W : Subgroup H, W ≤ S ∧ IsPGroup q W ∧ W.map psi = Wb ∧
      ∀ x ∈ W, ∀ y ∈ W, psi x = psi y → x = y := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  set C : Subgroup H := S ⊓ Wb.comap psi
  have hCmap : C.map psi = Wb := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hc.2
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := hWS hx
      exact ⟨s, ⟨hs, hx⟩, rfl⟩
  have hdvd : q ^ k ∣ Nat.card C := by
    rw [← hk, ← hCmap]
    exact Subgroup.card_map_dvd C psi
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  set W := K₀.map C.subtype with hWdef
  have hWpg : IsPGroup q W := (IsPGroup.of_card hK₀).map C.subtype
  have hWC : W ≤ C := Subgroup.map_subtype_le K₀
  have hinj := lift_inj_on psi hWpg hkc
  have hle : W.map psi ≤ Wb := by
    rw [← hCmap]
    exact Subgroup.map_mono hWC
  refine ⟨W, hWC.trans inf_le_left, hWpg, Subgroup.eq_of_le_of_card_ge hle ?_, hinj⟩
  rw [hk, lift_card_map_of_inj_on psi hinj, hWdef, Subgroup.card_map_of_injective
    C.subtype_injective, hK₀]

private theorem lift_exists_surj (psi : H →* K) {S : Subgroup H} {Db : Subgroup K}
    (hDS : Db ≤ S.map psi) :
    ∃ D : Subgroup H, D ≤ S ∧ ∃ f : D →* Db, Function.Surjective f := by
  refine ⟨S ⊓ Db.comap psi, inf_le_left, (psi.comp (S ⊓ Db.comap psi).subtype).codRestrict Db
    (fun d => d.2.2), ?_⟩
  intro b
  obtain ⟨s, hs, hsb⟩ := hDS b.2
  exact ⟨⟨s, hs, Subgroup.mem_comap.mpr (by rw [hsb]; exact b.2)⟩, Subtype.ext hsb⟩

private theorem lift_elem_map {p : ℕ} (f : H →* K) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

private theorem lift_elem_comap {p : ℕ} {f : K →* H} (hf : Function.Injective f) {E : Subgroup H}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap f) := by
  obtain ⟨hcomm, hpow⟩ := hE
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply hf
    show f (a * b) = f (b * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨f a, ha⟩ ⟨f b, hb⟩)
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hpow _ hx

private theorem lift_elem_of_inj_on {p : ℕ} (psi : H →* K) {W : Subgroup H}
    (hinj : ∀ x ∈ W, ∀ y ∈ W, psi x = psi y → x = y) (hE : IsElemAbelian p (W.map psi)) :
    IsElemAbelian p W := by
  obtain ⟨hcomm, hpow⟩ := hE
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    show a * b = b * a
    apply hinj _ (W.mul_mem ha hb) _ (W.mul_mem hb ha)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨psi a, Subgroup.mem_map_of_mem psi ha⟩
      ⟨psi b, Subgroup.mem_map_of_mem psi hb⟩)
  · intro x hx
    apply hinj _ (W.pow_mem hx p) _ W.one_mem
    rw [map_pow, map_one]
    exact hpow _ (Subgroup.mem_map_of_mem psi hx)

end LiftSubgroups

section PrimeCore

open CFSG.SignalizerFunctor.Helpers

variable {G : Type*} [Group G]

private theorem lift_primeCoreIn_le (π : Set ℕ) (U : Subgroup G) : primeCoreIn π U ≤ U :=
  Subgroup.map_subtype_le _

private theorem lift_primeCoreIn_normal (π : Set ℕ) (U : Subgroup G) :
    ((primeCoreIn π U).subgroupOf U).Normal := by
  have h : (primeCoreIn π U).subgroupOf U = primeSetCore (GroupType := U) π :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  rw [h]
  exact prime_set_core_normal π

private theorem lift_primeCoreIn_cop [Finite G] {q : ℕ} (hq : q.Prime) (U : Subgroup G) :
    Nat.Coprime q (Nat.card (primeCoreIn ({q}ᶜ : Set ℕ) U)) := by
  have hcard : Nat.card (primeCoreIn ({q}ᶜ : Set ℕ) U) =
      Nat.card (primeSetCore (GroupType := U) ({q}ᶜ : Set ℕ)) :=
    Subgroup.card_map_of_injective U.subtype_injective
  rw [hcard]
  exact (prime_supported_complement_singleton_iff_coprime q hq _).mp
    (prime_set_core_supported _)

private theorem lift_le_primeCoreIn {q : ℕ} (hq : q.Prime) {U M : Subgroup G} (hMU : M ≤ U)
    (hM : (M.subgroupOf U).Normal) (hcop : Nat.Coprime q (Nat.card M)) :
    M ≤ primeCoreIn ({q}ᶜ : Set ℕ) U := by
  have hsupp : primeSupported ({q}ᶜ : Set ℕ) (Nat.card (M.subgroupOf U)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMU).toEquiv]
    exact (prime_supported_complement_singleton_iff_coprime q hq _).mpr hcop
  have h1 := prime_set_core_contains _ (M.subgroupOf U) hM hsupp
  have h2 := Subgroup.map_mono (f := U.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hMU] at h2

end PrimeCore

section Setup

variable {H : Type*} [Group H] {K : Type*} [Group K]

private theorem lift_card_map_mul (psi : H →* K) (M : Subgroup H) :
    Nat.card (M.map psi) * Nat.card (psi.ker.subgroupOf M) = Nat.card M := by
  have hker : (psi.subgroupMap M).ker = psi.ker.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hrange : (psi.subgroupMap M).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (psi.subgroupMap_surjective M)
  have h := Subgroup.card_ker_mul_card_range (psi.subgroupMap M)
  rw [hker, hrange, Subgroup.card_top] at h
  rw [mul_comm]
  exact h

private structure LiftSetup (q r : ℕ) (psi : H →* K) (U A T : Subgroup H) : Prop where
  prime_q : q.Prime
  prime_r : r.Prime
  surj : Function.Surjective psi
  ker_le : psi.ker ≤ U
  ker_cop : Nat.Coprime q (Nat.card psi.ker)
  ker_max : ∀ M : Subgroup H, M ≤ U → (M.subgroupOf U).Normal → Nat.Coprime q (Nat.card M) →
    M ≤ psi.ker
  solvable : Group.IsSolvable U
  elem : IsElemAbelian r A
  cop : Nat.Coprime r (Nat.card U)
  normU : A ≤ Subgroup.normalizer (U : Set H)
  sylow : IsSylowOf q T U
  normT : A ≤ Subgroup.normalizer (T : Set H)

variable {q r : ℕ} {psi : H →* K} {U A T : Subgroup H}

private theorem LiftSetup.isPGroup_T (h : LiftSetup q r psi U A T) : IsPGroup q T := by
  obtain ⟨P, rfl⟩ := h.sylow
  exact P.isPGroup'.map U.subtype

private theorem LiftSetup.inj_T (h : LiftSetup q r psi U A T) :
    ∀ x ∈ T, ∀ y ∈ T, psi x = psi y → x = y :=
  lift_inj_on psi h.isPGroup_T h.ker_cop

private theorem LiftSetup.reduced [Finite H] [Finite K] (h : LiftSetup q r psi U A T) :
    Reduced q r (U.map psi) (A.map psi) (T.map psi) where
  prime_q := h.prime_q
  prime_r := h.prime_r
  solvable := by
    have := h.solvable
    exact Group.isSolvable_of_surjective (psi.subgroupMap_surjective U)
  noCore := by
    intro Mb hMbU hnorm hcop
    set M : Subgroup H := U ⊓ Mb.comap psi
    have hMU : M ≤ U := inf_le_left
    have hMnorm : (M.subgroupOf U).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMU, Subgroup.le_normalizer_iff]
      rintro u hu x ⟨hxU, hxM⟩
      refine ⟨U.mul_mem (U.mul_mem hu hxU) (U.inv_mem hu), ?_⟩
      have key := hnorm.conj_mem ⟨psi x, Subgroup.mem_map_of_mem psi hxU⟩
        (Subgroup.mem_subgroupOf.mpr hxM) ⟨psi u, Subgroup.mem_map_of_mem psi hu⟩
      show psi (u * x * u⁻¹) ∈ Mb
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mem_subgroupOf.mp key
    have hMmap : M.map psi = Mb := by
      apply le_antisymm
      · rintro _ ⟨c, hc, rfl⟩
        exact hc.2
      · intro x hx
        obtain ⟨u, hu, rfl⟩ := hMbU hx
        exact ⟨u, ⟨hu, hx⟩, rfl⟩
    have hMcop : Nat.Coprime q (Nat.card M) := by
      rw [← lift_card_map_mul psi M, hMmap]
      exact Nat.Coprime.mul_right hcop (h.ker_cop.coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective psi.ker M.subtype M.subtype_injective))
    have hMker := h.ker_max M hMU hMnorm hMcop
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hMbU hx
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (hMker ⟨hu, hx⟩))
  elem := lift_elem_map psi h.elem
  cop := h.cop.coprime_dvd_right (Subgroup.card_map_dvd U psi)
  normU := CFSG.SignalizerFunctor.Helpers.normalizer_image_le psi A U h.normU
  sylow := by
    have : Fact q.Prime := ⟨h.prime_q⟩
    obtain ⟨P, hP⟩ := h.sylow
    refine ⟨Sylow.mapSurjective (psi.subgroupMap_surjective U) P, ?_⟩
    rw [Sylow.coe_mapSurjective, ← hP, Subgroup.map_map, Subgroup.map_map]
    rfl
  normT := CFSG.SignalizerFunctor.Helpers.normalizer_image_le psi A T h.normT

private theorem LiftSetup.core_bar [Finite H] [Finite K] (h : LiftSetup q r psi U A T) :
    primeCoreIn ({q}ᶜ : Set ℕ) (U.map psi) = ⊥ :=
  h.reduced.noCore _ (lift_primeCoreIn_le _ _) (lift_primeCoreIn_normal _ _)
    (lift_primeCoreIn_cop h.prime_q _)

private theorem LiftSetup.thompsonJ_eq [Finite H] (h : LiftSetup q r psi U A T) :
    thompsonJ q (T.map psi) = (thompsonJ q T).map psi :=
  (map_thompsonJ q psi h.inj_T).symm

private theorem LiftSetup.omegaCenter_eq [Finite H] (h : LiftSetup q r psi U A T) :
    omegaCenter q (T.map psi) = (omegaCenter q T).map psi :=
  (map_omegaCenter q psi h.inj_T).symm

private theorem LiftSetup.bar_normalizer [Finite H] (h : LiftSetup q r psi U A T) :
    U.map psi ⊓ Subgroup.normalizer (thompsonJ q (T.map psi) : Set K) =
      (U ⊓ Subgroup.normalizer (thompsonJ q T : Set H)).map psi := by
  rw [h.thompsonJ_eq]
  exact lift_inf_normalizer h.prime_q psi h.surj h.ker_le h.ker_cop
    (h.isPGroup_T.to_le (thompsonJ_le q T))

private theorem LiftSetup.bar_centralizer_omega [Finite H] (h : LiftSetup q r psi U A T) :
    U.map psi ⊓ Subgroup.centralizer (omegaCenter q (T.map psi) : Set K) =
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set H)).map psi := by
  rw [h.omegaCenter_eq]
  exact lift_inf_centralizer h.prime_q psi h.surj h.ker_le h.ker_cop
    (h.isPGroup_T.to_le (omegaCenter_le q T))

private theorem LiftSetup.bar_centralizer_A (h : LiftSetup q r psi U A T) :
    (U ⊓ Subgroup.centralizer (A : Set H)).map psi =
      U.map psi ⊓ Subgroup.centralizer (A.map psi : Set K) :=
  lift_inf_centralizer_action h.prime_r psi h.elem h.normU h.cop

private theorem lift_ker_sup_eq (psi : H →* K) {Z U : Subgroup H} (hker : psi.ker ≤ U)
    (hZ : Z.map psi = U.map psi) : psi.ker ⊔ Z = U := by
  have h := congrArg (Subgroup.comap psi) hZ
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_eq_left.mpr hker, sup_comm] at h
  exact h

private theorem LiftSetup.factor_of_bar [Finite H] [Finite K] (h : LiftSetup q r psi U A T)
    (hfac : ThompsonFactorizable q (U.map psi) (T.map psi)) :
    psi.ker ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set H)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set H)) = U := by
  unfold ThompsonFactorizable at hfac
  rw [h.core_bar, bot_sup_eq, h.bar_normalizer, h.bar_centralizer_omega, ← Subgroup.map_sup] at hfac
  rw [sup_assoc]
  exact lift_ker_sup_eq psi h.ker_le hfac

private theorem lift_generation_core [Finite H] [Finite K] (h : LiftSetup q r psi U A T) :
    psi.ker ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set H)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set H)) ⊔
      (U ⊓ Subgroup.centralizer (A : Set H)) = U := by
  have hgen := reduced_generation h.reduced
  rw [h.core_bar, bot_sup_eq, h.bar_normalizer, h.bar_centralizer_omega, ← h.bar_centralizer_A,
    ← Subgroup.map_sup, ← Subgroup.map_sup] at hgen
  refine Eq.trans ?_ (lift_ker_sup_eq psi h.ker_le hgen)
  simp only [sup_assoc]

private theorem lift_three_core [Finite H] [Finite K] {r : ℕ} {psi : H →* K} {U A T : Subgroup H}
    (h : LiftSetup 3 r psi U A T)
    (hnot : ¬ (psi.ker ⊔ (U ⊓ Subgroup.normalizer (thompsonJ 3 T : Set H)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter 3 T : Set H)) = U)) :
    (∃ W : Subgroup H, W ≤ U ⊓ Subgroup.centralizer (A : Set H) ∧ IsElemAbelian 3 W ∧
      Nat.card W = 9) ∧
    ∃ D : Subgroup H, D ≤ U ⊓ Subgroup.centralizer (A : Set H) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ := by
  obtain ⟨⟨Wb, hWb, hWe, hWc⟩, Db, hDb, φb, hφb⟩ :=
    reduced_three h.reduced (fun hfac => hnot (h.factor_of_bar hfac))
  have hA3 := h.bar_centralizer_A
  obtain ⟨W, hWS, hWpg, hWmap, hWinj⟩ := lift_exists_pgroup h.prime_q psi h.ker_cop
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 3 Wb hWe)
    (by rw [hA3]; exact hWb)
  obtain ⟨D, hDS, f, hf⟩ := lift_exists_surj psi (S := U ⊓ Subgroup.centralizer (A : Set H))
    (Db := Db) (by rw [hA3]; exact hDb)
  refine ⟨⟨W, hWS, lift_elem_of_inj_on psi hWinj (by rw [hWmap]; exact hWe), ?_⟩, D, hDS,
    φb.comp f, hφb.comp hf⟩
  rw [← lift_card_map_of_inj_on psi hWinj, hWmap]
  exact hWc

private theorem lift_two_core [Finite H] [Finite K] {r : ℕ} {psi : H →* K} {U A T : Subgroup H}
    (h : LiftSetup 2 r psi U A T)
    (hnot : ¬ (psi.ker ⊔ (U ⊓ Subgroup.normalizer (thompsonJ 2 T : Set H)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter 2 T : Set H)) = U)) :
    ∃ W : Subgroup H, W ≤ U ⊓ Subgroup.centralizer (A : Set H) ∧ IsElemAbelian 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ U ⊓ Subgroup.centralizer (A : Set H),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set H) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 := by
  obtain ⟨Wb, hWb, hWe, hWc, db, hdb, hd3, hdN, hfix⟩ :=
    reduced_two h.reduced (fun hfac => hnot (h.factor_of_bar hfac))
  have hA3 := h.bar_centralizer_A
  obtain ⟨W, hWS, hWpg, hWmap, hWinj⟩ := lift_exists_pgroup h.prime_q psi h.ker_cop
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 Wb hWe)
    (by rw [hA3]; exact hWb)
  have hAW : A ≤ Subgroup.normalizer (W : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha w hw
    have hc := Subgroup.mem_centralizer_iff.mp (hWS hw).2 a ha
    rw [hc, mul_inv_cancel_right]
    exact hw
  have hAUW : A ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.normalizer (W : Set H) : Subgroup H) : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    rintro a ha x ⟨hxU, hxW⟩
    exact ⟨Subgroup.le_normalizer_iff.mp h.normU a ha x hxU,
      (Subgroup.normalizer (W : Set H)).mul_mem
        ((Subgroup.normalizer (W : Set H)).mul_mem (hAW ha) hxW)
        ((Subgroup.normalizer (W : Set H)).inv_mem (hAW ha))⟩
  have hcopUW : Nat.Coprime r (Nat.card (U ⊓ Subgroup.normalizer (W : Set H) : Subgroup H)) :=
    h.cop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hL3 := lift_inf_centralizer_action h.prime_r psi h.elem hAUW hcopUW
  have hL1 := lift_inf_normalizer h.prime_q psi h.surj h.ker_le h.ker_cop hWpg
  rw [hWmap] at hL1
  have hdmem : db ∈ ((U ⊓ Subgroup.normalizer (W : Set H)) ⊓
      Subgroup.centralizer (A : Set H)).map psi := by
    rw [hL3, ← hL1]
    exact ⟨⟨hdb.1, hdN⟩, hdb.2⟩
  obtain ⟨n0, ⟨⟨hn0U, hn0N⟩, hn0C⟩, hn0⟩ := hdmem
  set m := orderOf n0 / 3 ^ (orderOf n0).factorization 3
  have hmul : 3 ^ (orderOf n0).factorization 3 * m = orderOf n0 :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  have hm3 : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three (orderOf_pos n0).ne'
  have hmdvd : m ∣ orderOf n0 := Dvd.intro_left _ hmul
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact (orderOf_pos n0).ne hmul
  have hord : orderOf (n0 ^ m) = 3 ^ (orderOf n0).factorization 3 := by
    rw [orderOf_pow_of_dvd hm0 hmdvd]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) hmul.symm
  refine ⟨W, hWS, lift_elem_of_inj_on psi hWinj (by rw [hWmap]; exact hWe), ?_, n0 ^ m,
    (U ⊓ Subgroup.centralizer (A : Set H)).pow_mem ⟨hn0U, hn0C⟩ m,
    IsPGroup.of_card (n := (orderOf n0).factorization 3) (by rw [Nat.card_zpowers, hord]),
    (Subgroup.normalizer (W : Set H)).pow_mem hn0N m, ?_⟩
  · rw [← lift_card_map_of_inj_on psi hWinj, hWmap]
    exact hWc
  · intro w hw hfixw
    have hy : db ^ m * psi w * (db ^ m)⁻¹ = psi w := by
      have := congrArg psi hfixw
      rw [map_mul, map_mul, map_inv, map_pow, hn0] at this
      exact this
    obtain ⟨b, hb⟩ := hd3.exists_card_eq
    rw [Nat.card_zpowers] at hb
    have hcop' : Nat.Coprime (orderOf db) m := by
      rw [hb]
      exact Nat.Coprime.pow_left b hm3
    have hle : Subgroup.zpowers (db ^ m) ≤ Subgroup.zpowers db :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers db) m)
    have hcard : Nat.card (Subgroup.zpowers db) ≤ Nat.card (Subgroup.zpowers (db ^ m)) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hcop'.orderOf_pow]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have hdbmem : db ∈ Subgroup.zpowers (db ^ m) := heq ▸ Subgroup.mem_zpowers db
    have hcentr : db ∈ Subgroup.centralizer {psi w} := by
      have hpm : db ^ m ∈ Subgroup.centralizer {psi w} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp hy
      exact Subgroup.zpowers_le.mpr hpm hdbmem
    have hy1 : db * psi w * db⁻¹ = psi w := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hcentr
      rw [hcentr, mul_inv_cancel_right]
    have hpsi1 : psi w = 1 :=
      hfix (psi w) (hWmap ▸ Subgroup.mem_map_of_mem psi hw) hy1
    exact hWinj w hw 1 W.one_mem (by rw [hpsi1, map_one])

end Setup

section InjMap

variable {H : Type*} [Group H] {G : Type*} [Group G] {i : H →* G}

private theorem lift_map_normalizer_eq (hi : Function.Injective i) (X : Subgroup H) :
    (Subgroup.normalizer (X : Set H)).map i =
      i.range ⊓ Subgroup.normalizer (X.map i : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, Subgroup.le_normalizer_map i (Subgroup.mem_map_of_mem i hx)⟩
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, Subgroup.mem_normalizer_iff.mpr fun z => ?_, rfl⟩
    have h1 := Subgroup.mem_normalizer_iff.mp hy (i z)
    rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hi,
      Subgroup.mem_map_iff_mem hi] at h1
    exact h1

private theorem lift_map_centralizer_eq (hi : Function.Injective i) (X : Subgroup H) :
    (Subgroup.centralizer (X : Set H)).map i =
      i.range ⊓ Subgroup.centralizer (X.map i : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx z hz]
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, Subgroup.mem_centralizer_iff.mpr fun z hz => hi ?_, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hy (i z) (Subgroup.mem_map_of_mem i hz)

private theorem lift_map_inf_normalizer (hi : Function.Injective i) (U X : Subgroup H) :
    (U ⊓ Subgroup.normalizer (X : Set H)).map i =
      U.map i ⊓ Subgroup.normalizer (X.map i : Set G) := by
  rw [Subgroup.map_inf _ _ _ hi, lift_map_normalizer_eq hi, ← inf_assoc,
    inf_eq_left.mpr (Subgroup.map_le_range i U)]

private theorem lift_map_inf_centralizer (hi : Function.Injective i) (U X : Subgroup H) :
    (U ⊓ Subgroup.centralizer (X : Set H)).map i =
      U.map i ⊓ Subgroup.centralizer (X.map i : Set G) := by
  rw [Subgroup.map_inf _ _ _ hi, lift_map_centralizer_eq hi, ← inf_assoc,
    inf_eq_left.mpr (Subgroup.map_le_range i U)]

end InjMap

section Reduce

open CFSG.SignalizerFunctor.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

private theorem lift_le_normalizer_primeCoreIn (π : Set ℕ) {A U : Subgroup G}
    (h : A ≤ Subgroup.normalizer (U : Set G)) :
    A ≤ Subgroup.normalizer (primeCoreIn π U : Set G) := by
  have : (primeSetCore (GroupType := U) π).Characteristic := prime_set_core_characteristic π
  exact characteristic_subgroup_map_normalized A U h (primeSetCore (GroupType := U) π)

private theorem lift_isSylowOf_iff {q : ℕ} (hq : q.Prime) {T U : Subgroup G} :
    IsSylowOf q T U ↔ T ≤ U ∧ Nat.card T = q ^ (Nat.card U).factorization q := by
  have : Fact q.Prime := ⟨hq⟩
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact S.card_eq_multiplicity
  · rintro ⟨hle, hcard⟩
    refine ⟨Sylow.ofCard (T.subgroupOf U) ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact hcard
    · rw [Sylow.coe_ofCard]
      exact Subgroup.map_subgroupOf_eq_of_le hle

private theorem lift_isSylowOf_subgroupOf {q : ℕ} (hq : q.Prime) {T U P : Subgroup G}
    (hUP : U ≤ P) (hT : IsSylowOf q T U) :
    IsSylowOf q (T.subgroupOf P) (U.subgroupOf P) := by
  obtain ⟨hle, hcard⟩ := (lift_isSylowOf_iff hq).mp hT
  refine (lift_isSylowOf_iff hq).mpr ⟨Subgroup.comap_mono hle, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hle.trans hUP)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv]
  exact hcard

omit [Finite G] in
private theorem lift_subgroupOf_le_normalizer {X Y : Subgroup G} (P : Subgroup G)
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    X.subgroupOf P ≤ Subgroup.normalizer (Y.subgroupOf P : Set P) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  exact Subgroup.le_normalizer_iff.mp h x hx y hy

private theorem lift_reduce {q r : ℕ} (hq : q.Prime) (hr : r.Prime) {U A T : Subgroup G}
    (hU : Group.IsSolvable U) (hA : IsElemAbelian r A) (hcop : Nat.Coprime r (Nat.card U))
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hT : IsSylowOf q T U)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    ∃ (P : Subgroup G) (K : Type u) (_ : Group K) (_ : Finite K) (psi : ↥P →* K),
      U ≤ P ∧ A ≤ P ∧ T ≤ P ∧ psi.ker = (primeCoreIn ({q}ᶜ : Set ℕ) U).subgroupOf P ∧
      LiftSetup q r psi (U.subgroupOf P) (A.subgroupOf P) (T.subgroupOf P) := by
  set N := primeCoreIn ({q}ᶜ : Set ℕ) U
  have hNU : N ≤ U := lift_primeCoreIn_le _ _
  have hUP : U ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNU).mp (lift_primeCoreIn_normal _ _)
  have hAP : A ≤ Subgroup.normalizer (N : Set G) := lift_le_normalizer_primeCoreIn _ hAU
  have hTU : T ≤ U := ((lift_isSylowOf_iff hq).mp hT).1
  have hNP : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  refine ⟨Subgroup.normalizer (N : Set G), ↥(Subgroup.normalizer (N : Set G)) ⧸
    N.subgroupOf (Subgroup.normalizer (N : Set G)), inferInstance, inferInstance,
    QuotientGroup.mk' (N.subgroupOf (Subgroup.normalizer (N : Set G))), hUP, hAP,
    hTU.trans hUP, QuotientGroup.ker_mk' _, hq, hr, QuotientGroup.mk'_surjective _, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [QuotientGroup.ker_mk']
    exact Subgroup.comap_mono hNU
  · rw [QuotientGroup.ker_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv]
    exact lift_primeCoreIn_cop hq U
  · intro M₀ hM₀U hM₀norm hM₀cop
    rw [QuotientGroup.ker_mk']
    have hMU : M₀.map (Subgroup.normalizer (N : Set G)).subtype ≤ U := by
      rintro _ ⟨m, hm, rfl⟩
      exact hM₀U hm
    have hnorm₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hM₀U).mp hM₀norm
    have hUnorm : U ≤ Subgroup.normalizer
        (M₀.map (Subgroup.normalizer (N : Set G)).subtype : Set G) := by
      have := normalizer_image_le (Subgroup.normalizer (N : Set G)).subtype
        (U.subgroupOf (Subgroup.normalizer (N : Set G))) M₀ hnorm₀
      rwa [Subgroup.map_subgroupOf_eq_of_le hUP] at this
    have hMnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hMU).mpr hUnorm
    have hMcop : Nat.Coprime q
        (Nat.card (M₀.map (Subgroup.normalizer (N : Set G)).subtype)) := by
      rw [Subgroup.card_map_of_injective (Subgroup.normalizer (N : Set G)).subtype_injective]
      exact hM₀cop
    have hMN := lift_le_primeCoreIn hq hMU hMnorm hMcop
    intro x hx
    exact hMN ⟨x, hx, rfl⟩
  · have := hU
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hUP).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hUP).injective
  · exact lift_elem_comap (Subgroup.normalizer (N : Set G)).subtype_injective hA
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv]
    exact hcop
  · exact lift_subgroupOf_le_normalizer _ hAU
  · exact lift_isSylowOf_subgroupOf hq hUP hT
  · exact lift_subgroupOf_le_normalizer _ hAT

end Reduce

section Pieces

variable {G : Type*} [Group G]

private theorem lift_map_normalizer_J (q : ℕ) {P U T : Subgroup G} (hUP : U ≤ P) (hTP : T ≤ P) :
    (U.subgroupOf P ⊓ Subgroup.normalizer (thompsonJ q (T.subgroupOf P) : Set P)).map P.subtype =
      U ⊓ Subgroup.normalizer (thompsonJ q T : Set G) := by
  rw [lift_map_inf_normalizer P.subtype_injective,
    map_thompsonJ q P.subtype (fun x _ y _ h => P.subtype_injective h),
    Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_subgroupOf_eq_of_le hTP]

private theorem lift_map_centralizer_omega (q : ℕ) {P U T : Subgroup G} (hUP : U ≤ P)
    (hTP : T ≤ P) :
    (U.subgroupOf P ⊓
      Subgroup.centralizer (omegaCenter q (T.subgroupOf P) : Set P)).map P.subtype =
      U ⊓ Subgroup.centralizer (omegaCenter q T : Set G) := by
  rw [lift_map_inf_centralizer P.subtype_injective,
    map_omegaCenter q P.subtype (fun x _ y _ h => P.subtype_injective h),
    Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_subgroupOf_eq_of_le hTP]

private theorem lift_map_centralizer_A {P U A : Subgroup G} (hUP : U ≤ P) (hAP : A ≤ P) :
    (U.subgroupOf P ⊓ Subgroup.centralizer (A.subgroupOf P : Set P)).map P.subtype =
      U ⊓ Subgroup.centralizer (A : Set G) := by
  rw [lift_map_inf_centralizer P.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hUP,
    Subgroup.map_subgroupOf_eq_of_le hAP]

private theorem lift_factorizable_of_subgroupOf (q : ℕ) {P U T : Subgroup G} (hUP : U ≤ P)
    (hTP : T ≤ P)
    (h : (primeCoreIn ({q}ᶜ : Set ℕ) U).subgroupOf P ⊔
      (U.subgroupOf P ⊓ Subgroup.normalizer (thompsonJ q (T.subgroupOf P) : Set P)) ⊔
      (U.subgroupOf P ⊓ Subgroup.centralizer (omegaCenter q (T.subgroupOf P) : Set P)) =
        U.subgroupOf P) :
    ThompsonFactorizable q U T := by
  have key := congrArg (Subgroup.map P.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_sup, lift_map_normalizer_J q hUP hTP,
    lift_map_centralizer_omega q hUP hTP,
    Subgroup.map_subgroupOf_eq_of_le ((lift_primeCoreIn_le _ _).trans hUP),
    Subgroup.map_subgroupOf_eq_of_le hUP] at key
  exact key

end Pieces

section Transport

variable {H : Type*} [Group H] {G : Type*} [Group G] {i : H →* G}

private theorem lift_two_map (hi : Function.Injective i) {U A : Subgroup H}
    (h : ∃ W : Subgroup H, W ≤ U ⊓ Subgroup.centralizer (A : Set H) ∧ IsElemAbelian 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ U ⊓ Subgroup.centralizer (A : Set H),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set H) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) :
    ∃ W : Subgroup G, W ≤ U.map i ⊓ Subgroup.centralizer (A.map i : Set G) ∧
      IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      ∃ d ∈ U.map i ⊓ Subgroup.centralizer (A.map i : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 := by
  obtain ⟨W, hW, he, hc, d, hd, hd3, hdN, hfix⟩ := h
  have hmap := lift_map_inf_centralizer hi U A
  refine ⟨W.map i, by rw [← hmap]; exact Subgroup.map_mono hW, lift_elem_map i he, ?_, i d,
    by rw [← hmap]; exact Subgroup.mem_map_of_mem i hd, ?_,
    Subgroup.le_normalizer_map i (Subgroup.mem_map_of_mem i hdN), ?_⟩
  · rw [Subgroup.card_map_of_injective hi]
    exact hc
  · rw [← MonoidHom.map_zpowers]
    exact hd3.map i
  · rintro _ ⟨w, hw, rfl⟩ hfw
    have : d * w * d⁻¹ = w := hi (by rw [map_mul, map_mul, map_inv]; exact hfw)
    rw [hfix w hw this, map_one]

private theorem lift_three_map (hi : Function.Injective i) {U A : Subgroup H}
    (h : (∃ W : Subgroup H, W ≤ U ⊓ Subgroup.centralizer (A : Set H) ∧ IsElemAbelian 3 W ∧
      Nat.card W = 9) ∧
    ∃ D : Subgroup H, D ≤ U ⊓ Subgroup.centralizer (A : Set H) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ) :
    (∃ W : Subgroup G, W ≤ U.map i ⊓ Subgroup.centralizer (A.map i : Set G) ∧
      IsElemAbelian 3 W ∧ Nat.card W = 9) ∧
    ∃ D : Subgroup G, D ≤ U.map i ⊓ Subgroup.centralizer (A.map i : Set G) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ := by
  obtain ⟨⟨W, hW, he, hc⟩, D, hD, φ, hφ⟩ := h
  have hmap := lift_map_inf_centralizer hi U A
  refine ⟨⟨W.map i, by rw [← hmap]; exact Subgroup.map_mono hW, lift_elem_map i he, ?_⟩,
    D.map i, by rw [← hmap]; exact Subgroup.map_mono hD,
    φ.comp (D.equivMapOfInjective i hi).symm.toMonoidHom,
    hφ.comp (MulEquiv.surjective _)⟩
  rw [Subgroup.card_map_of_injective hi]
  exact hc

end Transport

variable {G : Type*} [Group G] [Finite G]

theorem lift_generation {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf q T U) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (A : Set G)) = U := by
  obtain ⟨P, K, _, _, psi, hUP, hAP, hTP, hker, h⟩ := lift_reduce hq hr hU hA hcop hAU hT hAT
  have key := congrArg (Subgroup.map P.subtype) (lift_generation_core h)
  rw [hker, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, lift_map_normalizer_J q hUP hTP,
    lift_map_centralizer_omega q hUP hTP, lift_map_centralizer_A hUP hAP,
    Subgroup.map_subgroupOf_eq_of_le ((lift_primeCoreIn_le _ _).trans hUP),
    Subgroup.map_subgroupOf_eq_of_le hUP] at key
  exact key

theorem lift_two {r : ℕ} (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf 2 T U) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hnot : ¬ ThompsonFactorizable 2 U T) :
    ∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ U ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 := by
  obtain ⟨P, K, _, _, psi, hUP, hAP, hTP, hker, h⟩ :=
    lift_reduce Nat.prime_two hr hU hA hcop hAU hT hAT
  have hnot' := fun hfac => hnot (lift_factorizable_of_subgroupOf 2 hUP hTP (hker ▸ hfac))
  have := lift_two_map P.subtype_injective (lift_two_core h hnot')
  rwa [Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_subgroupOf_eq_of_le hAP] at this

theorem lift_three {r : ℕ} (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf 3 T U) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hnot : ¬ ThompsonFactorizable 3 U T) :
    (∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 3 W ∧
      Nat.card W = 9) ∧
    ∃ D : Subgroup G, D ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ := by
  obtain ⟨P, K, _, _, psi, hUP, hAP, hTP, hker, h⟩ :=
    lift_reduce Nat.prime_three hr hU hA hcop hAU hT hAT
  have hnot' := fun hfac => hnot (lift_factorizable_of_subgroupOf 3 hUP hTP (hker ▸ hfac))
  have := lift_three_map P.subtype_injective (lift_three_core h hnot')
  rwa [Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_subgroupOf_eq_of_le hAP] at this

end CFSG.SignalizerFunctorTheorem.Quadratic
