module

public import CFSG.Timmesfeld.Bridge.RootSetsRankOne
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Timmesfeld.Bridge.StrongEmbedding

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped Pointwise

section Bender

variable {Y : Type*} [Group Y]

theorem mul_comm_of_forall_mul_self {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) : a * b = b * a := by
  have h := inv_eq_of_mul_eq_one_right (hexp _ (P.mul_mem ha hb))
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hexp b hb),
    inv_eq_of_mul_eq_one_right (hexp a ha)] at h
  exact h.symm

theorem not_isCyclic_of_mul_self {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1)
    (hq : 4 ≤ Nat.card P) : ¬ IsCyclic P := by
  intro hcyc
  have h := Monoid.exponent_dvd_of_forall_pow_eq_one (G := P) (n := 2) fun a =>
    Subtype.ext (by simpa [pow_two] using hexp a a.2)
  rw [IsCyclic.exponent_eq_card] at h
  have := Nat.le_of_dvd two_pos h
  omega

theorem not_quaternion_of_mul_self {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1) {n : ℕ}
    [NeZero n] (e : P ≃* QuaternionGroup n) : False := by
  have h4 := QuaternionGroup.orderOf_xa (n := n) 0
  rw [← e.symm.orderOf_eq] at h4
  have h2 : orderOf (e.symm (QuaternionGroup.xa 0)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simpa [pow_two] using hexp _ (e.symm (QuaternionGroup.xa 0)).2))
  rw [h4] at h2
  norm_num at h2

theorem commute_of_le_normalizer {P M : Subgroup Y} [M.Normal]
    (hMP : M ≤ Subgroup.normalizer (P : Set Y)) (hPM : P ⊓ M = ⊥) {a m : Y} (ha : a ∈ P)
    (hm : m ∈ M) : m * a = a * m := by
  have h1 : m * a * m⁻¹ * a⁻¹ ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.1 (hMP hm) a).1 ha) (P.inv_mem ha)
  have h2 : m * a * m⁻¹ * a⁻¹ ∈ M := by
    have := M.mul_mem hm (Subgroup.Normal.conj_mem inferInstance m⁻¹ (M.inv_mem hm) a)
    simpa only [mul_assoc] using this
  have h3 : m * a * m⁻¹ * a⁻¹ ∈ P ⊓ M := ⟨h1, h2⟩
  rw [hPM, Subgroup.mem_bot] at h3
  calc m * a = m * a * m⁻¹ * a⁻¹ * (a * m) := by group
    _ = a * m := by rw [h3, one_mul]

theorem false_of_fusionBenderBorel {K : Type*} [Group K] {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hq : 2 ≤ q) (hk : 2 ≤ k) (Q : Sylow 2 K)
    (hQ : ∀ a ∈ (Q : Subgroup K), ∀ b ∈ (Q : Subgroup K), a * b = b * a) : False := by
  obtain ⟨-, -, -, hZ, hcard⟩ := hB Q
  have hcenter : Subgroup.center (Q : Subgroup K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hQ _ y.2 _ x.2)
  rw [hcenter, Subgroup.card_top, hcard] at hZ
  have hlt : q < q ^ k :=
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem card_SL_two_galoisField_two (f : ℕ) (hf : f ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) =
      2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  let := Fintype.ofFinite (GaloisField 2 f)
  have hK : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f hf]
  have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow hf
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, hK,
    show (2 ^ f) ^ 2 - 2 ^ f = 2 ^ f * (2 ^ f - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_psl_two_galoisField_two (f : ℕ) (hf : f ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) =
      2 ^ f * ((2 ^ f) ^ 2 - 1) :=
  (Nat.card_congr (psl2EquivSL2 (GaloisField 2 f)).toEquiv).trans
    (card_SL_two_galoisField_two f hf)

variable [Finite Y]

omit [Finite Y] in
theorem mem_sylow_of_mem_normalizer (P : Sylow 2 Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer ((P : Subgroup Y) : Set Y)) (hx2 : x * x = 1) :
    x ∈ (P : Subgroup Y) := by
  have hdvd : orderOf x ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hx2])
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hmax := P.is_maximal' (IsPGroup.to_sup_of_normal_right' hp P.isPGroup'
    (Subgroup.zpowers_le.2 hx)) le_sup_right
  have hmem : x ∈ Subgroup.zpowers x ⊔ (P : Subgroup Y) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  rwa [hmax] at hmem

theorem fusionStronglyEmbedded_normalizer_of_isTI (P : Sylow 2 Y)
    (hTI : fusionIsTI (P : Subgroup Y))
    (hne : Subgroup.normalizer ((P : Subgroup Y) : Set Y) ≠ ⊤)
    (heven : Even (Nat.card (P : Subgroup Y))) :
    fusionStronglyEmbedded (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) := by
  refine ⟨hne, even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans
    (Subgroup.card_dvd_of_le Subgroup.le_normalizer)), fun g hg => ?_⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have hxo : orderOf (x : Y) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hx2 : (x : Y) * x = 1 := by
    have h := pow_orderOf_eq_one (x : Y)
    rwa [hxo, pow_two] at h
  have hx1 : (x : Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hxP : (x : Y) ∈ (P : Subgroup Y) := mem_sylow_of_mem_normalizer P x.2.1 hx2
  have hgx := mem_map_conj_inv_iff.1 x.2.2
  have hgx2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx2, mul_one,
      mul_inv_cancel]
  have hxP' : (x : Y) ∈ (P : Subgroup Y).map (MulAut.conj g⁻¹).toMonoidHom :=
    mem_map_conj_inv_iff.2 (mem_sylow_of_mem_normalizer P hgx hgx2)
  have hfix : (P : Subgroup Y).map (MulAut.conj g⁻¹).toMonoidHom = P := by
    by_contra hne'
    have hmem : (x : Y) ∈ (P : Subgroup Y) ⊓ (P : Subgroup Y).map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨hxP, hxP'⟩
    rw [hTI g⁻¹ hne', Subgroup.mem_bot] at hmem
    exact hx1 hmem
  exact hg (by simpa using Subgroup.inv_mem _ (map_conj_eq_self_iff.1 hfix))

theorem le_normalizer_of_isTI {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1)
    (hq : 4 ≤ Nat.card P) (hTI : fusionIsTI P) (M : Subgroup Y) [M.Normal]
    (hM : Odd (Nat.card M)) : M ≤ Subgroup.normalizer (P : Set Y) := by
  have : CFSG.IsElementaryAbelian 2 P :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm_of_forall_mul_self hexp a.2 b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa [pow_two] using hexp a a.2) }
  let : MulDistribMulAction P M :=
    MulDistribMulAction.compHom M ((MulAut.conjNormal (H := M)).comp P.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := P) (H := M)
    (by simpa using hq) (fun h => (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h))
  intro m hm
  have hle : ⨆ (a : P) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) M ≤
      (Subgroup.normalizer (P : Set Y)).comap M.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have h := congrArg Subtype.val hy
    change ((MulAut.conjNormal (a : Y)) y : Y) = y at h
    rw [MulAut.conjNormal_apply] at h
    have hc : (a : Y) * y = y * a := by
      calc (a : Y) * y = (a * y * (a : Y)⁻¹) * a := by group
        _ = y * a := by rw [h]
    show (y : Y) ∈ Subgroup.normalizer (P : Set Y)
    rw [← map_conj_eq_self_iff]
    by_contra hne
    have hmem : (a : Y) ∈ P ⊓ P.map (MulAut.conj (y : Y)).toMonoidHom := by
      refine ⟨a.2, mem_map_conj.2 ?_⟩
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
      exact a.2
    rw [hTI y hne, Subgroup.mem_bot] at hmem
    exact ha (Subtype.ext hmem)
  exact hle (hgen.symm ▸ Subgroup.mem_top (⟨m, hm⟩ : M))

theorem card_sylow_two_le_of_isTI (P : Sylow 2 Y) (hexp : ∀ a ∈ (P : Subgroup Y), a * a = 1)
    (hq : 4 ≤ Nat.card (P : Subgroup Y)) (hTI : fusionIsTI (P : Subgroup Y))
    (hgen : ∀ N : Subgroup Y, (∀ y : Y, y * y = 1 → y ∈ N) → N = ⊤) {t : Y}
    (ht : t ∈ (P : Subgroup Y))
    (htrans : ∀ e ∈ (P : Subgroup Y), e ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((P : Subgroup Y) : Set Y), n * t * n⁻¹ = e) :
    Nat.card (Sylow 2 Y) ≤ Nat.card (P : Subgroup Y) + 1 := by
  classical
  rw [Sylow.card_eq_index_normalizer P]
  change (Subgroup.normalizer ((P : Subgroup Y) : Set Y)).index ≤ Nat.card (P : Subgroup Y) + 1
  by_cases hnorm : Subgroup.normalizer ((P : Subgroup Y) : Set Y) = ⊤
  · rw [hnorm, Subgroup.index_top]
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk] at hq
    norm_num at hq
  have heven : Even (Nat.card (P : Subgroup Y)) := by
    rw [hk]
    exact Nat.even_pow.2 ⟨even_two, hk0⟩
  have hSE := fusionStronglyEmbedded_normalizer_of_isTI P hTI hnorm heven
  rcases bender_strongly_embedded_normal_series Y _ hSE with hcq |
    ⟨M, N, hMn, hNn, hMN, -, hModd, hNodd, hB⟩
  · exfalso
    rcases hcq P with hcyc | ⟨r, -, ⟨e⟩⟩
    · exact not_isCyclic_of_mul_self hexp hq hcyc
    · have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      exact not_quaternion_of_mul_self hexp e
  have hNtop : N = ⊤ := hgen N fun y hy => by
    obtain ⟨j, hj⟩ := hNodd
    have hpow : y ^ N.index ∈ N := Subgroup.pow_index_mem N y
    rwa [hj, pow_succ, pow_mul, pow_two, hy, one_pow, one_mul] at hpow
  subst hNtop
  have hMH : M ≤ Subgroup.normalizer ((P : Subgroup Y) : Set Y) :=
    le_normalizer_of_isTI hexp hq hTI M hModd
  have hPM : (P : Subgroup Y) ⊓ M = ⊥ := disjoint_iff.1
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hModd)))
  have hcomm : ∀ a ∈ (P : Subgroup Y), ∀ m ∈ M, m * a = a * m :=
    fun a ha m hm => commute_of_le_normalizer hMH hPM ha hm
  have hcardY : Nat.card Y =
      Nat.card (↥(⊤ : Subgroup Y) ⧸ M.subgroupOf ⊤) * Nat.card M := by
    rw [← Subgroup.card_top (G := Y),
      Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf ⊤),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv]
  set π := QuotientGroup.mk' (M.subgroupOf ⊤)
  have hQp : IsPGroup 2 (((P : Subgroup Y).subgroupOf ⊤).map π) :=
    (P.isPGroup'.comap_subtype).map π
  have hQi : ¬ 2 ∣ (((P : Subgroup Y).subgroupOf ⊤).map π).index := by
    intro h
    apply Sylow.not_dvd_index P
    have h1 := h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))
    have h2 : ((P : Subgroup Y).subgroupOf ⊤).index = (P : Subgroup Y).index :=
      Subgroup.relIndex_top_right _
    rwa [h2] at h1
  have hQcomm : ∀ a ∈ (((P : Subgroup Y).subgroupOf ⊤).map π),
      ∀ b ∈ (((P : Subgroup Y).subgroupOf ⊤).map π), a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_forall_mul_self hexp hx hy)
  obtain ⟨f, hf, hcardK⟩ : ∃ f : ℕ, 2 ≤ f ∧
      Nat.card (↥(⊤ : Subgroup Y) ⧸ M.subgroupOf ⊤) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact ⟨f, hf, (Nat.card_congr e.toEquiv).trans (card_psl_two_galoisField_two f (by omega))⟩
    · exfalso
      have : Finite (PSU3 2 f) := Finite.of_surjective e e.surjective
      refine false_of_fusionBenderBorel ((bender_psu3_borel_full f hf).map_mulEquiv e.symm)
        ?_ (by norm_num) (hQp.toSylow hQi) hQcomm
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exfalso
      have : Finite (Sz a) := Finite.of_surjective e e.surjective
      refine false_of_fusionBenderBorel ((bender_suzuki_borel_full a ha).map_mulEquiv e.symm)
        ?_ le_rfl (hQp.toSylow hQi) hQcomm
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hodd1 : Odd (((2 ^ f) ^ 2 - 1) * Nat.card M) := by
    refine Odd.mul (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) ?_ odd_one) hModd
    exact Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩
  have hidx : Odd (P : Subgroup Y).index :=
    Nat.not_even_iff_odd.1 fun h => Sylow.not_dvd_index P (even_iff_two_dvd.1 h)
  have hPf : Nat.card (P : Subgroup Y) = 2 ^ f := by
    have hY := (P : Subgroup Y).card_mul_index
    rw [hcardY, hcardK, hk, mul_assoc] at hY
    rw [hk]
    apply Nat.dvd_antisymm
    · exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd1)).dvd_of_dvd_mul_right
        (Dvd.intro _ hY)
    · exact (Nat.Coprime.pow_left f (Nat.coprime_two_left.2 hidx)).dvd_of_dvd_mul_right
        (Dvd.intro _ hY.symm)
  have htrans' : ∀ e : {a : (P : Subgroup Y) // a ≠ 1},
      ∃ n ∈ Subgroup.normalizer ((P : Subgroup Y) : Set Y), n * t * n⁻¹ = e :=
    fun e => htrans e.1 e.1.2 fun h => e.2 (Subtype.ext h)
  choose n hnH hnt using htrans'
  have hconj : ∀ (e : {a : (P : Subgroup Y) // a ≠ 1}) (a : (P : Subgroup Y)) (m : M),
      n e * a * m * t * (n e * a * m)⁻¹ = ((e : (P : Subgroup Y)) : Y) := by
    intro e a m
    have h1 : (m : Y) * t = t * m := hcomm t ht m m.2
    have h2 : (a : Y) * t = t * a := mul_comm_of_forall_mul_self hexp a.2 ht
    calc n e * a * m * t * (n e * a * m)⁻¹ = n e * a * (m * t) * (m : Y)⁻¹ * (a : Y)⁻¹ *
          (n e)⁻¹ := by group
      _ = n e * (a * t) * (a : Y)⁻¹ * (n e)⁻¹ := by rw [h1]; group
      _ = n e * t * (n e)⁻¹ := by rw [h2]; group
      _ = e := hnt e
  let F : {a : ↥(P : Subgroup Y) // a ≠ 1} × ↥(P : Subgroup Y) × ↥M →
      Subgroup.normalizer ((P : Subgroup Y) : Set Y) := fun x =>
    ⟨n x.1 * x.2.1 * x.2.2, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnH x.1)
      (Subgroup.le_normalizer x.2.1.2)) (hMH x.2.2.2)⟩
  have hFinj : Function.Injective F := by
    rintro ⟨e, a, m⟩ ⟨e', a', m'⟩ h
    have h' : n e * a * m = n e' * a' * m' := congrArg Subtype.val h
    have hee : e = e' :=
      Subtype.ext (Subtype.ext (by rw [← hconj e a m, ← hconj e' a' m', h']))
    subst hee
    have ham : (a : Y) * m = a' * m' := by
      rw [mul_assoc, mul_assoc] at h'
      exact mul_left_cancel h'
    have hx : (a' : Y)⁻¹ * a = m' * (m : Y)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← ham, mul_inv_cancel_right]
    have hmem : (a' : Y)⁻¹ * a ∈ (P : Subgroup Y) ⊓ M := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a'.2) a.2, ?_⟩
      rw [hx]
      exact Subgroup.mul_mem _ m'.2 (Subgroup.inv_mem _ m.2)
    rw [hPM, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have haa : a = a' := Subtype.ext hmem.symm
    subst haa
    have hmm : m = m' := Subtype.ext (mul_left_cancel ham)
    subst hmm
    rfl
  have hlow : (Nat.card (P : Subgroup Y) - 1) * (Nat.card (P : Subgroup Y) * Nat.card M) ≤
      Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) := by
    have h1 := Nat.card_le_card_of_injective F hFinj
    rw [Nat.card_prod, Nat.card_prod] at h1
    have h2 : Nat.card {a : (P : Subgroup Y) // a ≠ 1} + 1 = Nat.card (P : Subgroup Y) := by
      rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe 1)]
    have h3 : Nat.card {a : (P : Subgroup Y) // a ≠ 1} = Nat.card (P : Subgroup Y) - 1 := by
      omega
    rwa [h3] at h1
  have hY : Nat.card Y = (Nat.card (P : Subgroup Y) + 1) *
      ((Nat.card (P : Subgroup Y) - 1) * (Nat.card (P : Subgroup Y) * Nat.card M)) := by
    rw [hcardY, hcardK, ← hPf]
    rw [show Nat.card (P : Subgroup Y) ^ 2 - 1 =
        (Nat.card (P : Subgroup Y) + 1) * (Nat.card (P : Subgroup Y) - 1) by
      simpa using Nat.sq_sub_sq (Nat.card (P : Subgroup Y)) 1]
    ring
  have hHpos : 0 < Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) := Nat.card_pos
  apply Nat.le_of_mul_le_mul_right _ hHpos
  rw [Subgroup.index_mul_card, hY]
  exact Nat.mul_le_mul_left _ hlow

end Bender

section RootGroups

variable {G : Type*} [Group G] {D : Set G}

theorem map_subtype_map_conj_subgroupOf {H X : Subgroup G} (hH : H ≤ X) (y : X) :
    ((H.subgroupOf X).map (MulAut.conj y).toMonoidHom).map X.subtype =
      H.map (MulAut.conj (y : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨⟨z, hH hz⟩, hz, rfl⟩, rfl⟩

theorem map_conj_subgroupOf_eq_self_iff {H X : Subgroup G} (hH : H ≤ X) (y : X) :
    (H.subgroupOf X).map (MulAut.conj y).toMonoidHom = H.subgroupOf X ↔
      H.map (MulAut.conj (y : G)).toMonoidHom = H := by
  rw [← (Subgroup.map_injective X.subtype_injective).eq_iff, map_subtype_map_conj_subgroupOf hH,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hH]

theorem rankOneTransitive_of_sylow [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hq : 4 ≤ Nat.card (rootGroup D d))
    (hsyl : ∀ P : Subgroup G, IsPGroup 2 P → rootGroup D d ≤ P →
      P ≤ rootGroup D d ⊔ rootGroup D c → P = rootGroup D d) :
    RankOneTransitive D d c := by
  classical
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = rootGroup D d ⊔ rootGroup D c := ⟨_, rfl⟩
  have hAX : rootGroup D d ≤ X := hX ▸ le_sup_left
  have hBX : rootGroup D c ≤ X := hX ▸ le_sup_right
  rw [← hX] at hsyl
  let P : Sylow 2 X :=
    { toSubgroup := (rootGroup D d).subgroupOf X
      isPGroup' := (isPGroup_rootGroup hD hd).comap_subtype
      is_maximal' := fun {Q} hQ hle => by
        have h := hsyl (Q.map X.subtype) (hQ.map _)
          (fun a ha => ⟨⟨a, hAX ha⟩, @hle ⟨a, hAX ha⟩ ha, rfl⟩) (Subgroup.map_subtype_le Q)
        rw [← Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q, h]
        rfl }
  have hcardP : Nat.card (P : Subgroup X) = Nat.card (rootGroup D d) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have hexp : ∀ a ∈ (P : Subgroup X), a * a = 1 := fun a ha =>
    Subtype.ext (mul_self_eq_one_of_mem_rootGroup hD hd ha)
  have hTI : fusionIsTI (P : Subgroup X) := by
    intro y hne
    have hne' : (rootGroup D d).map (MulAut.conj (y : G)).toMonoidHom ≠ rootGroup D d :=
      fun h => hne ((map_conj_subgroupOf_eq_self_iff hAX y).2 h)
    have hyd : (y : G) * d * (y : G)⁻¹ ∈ D := conj_mem_of_isClass hclass _ hd
    have hroot : rootSet D d ≠ rootSet D ((y : G) * d * (y : G)⁻¹) := by
      intro h
      apply hne'
      rw [← rootGroup_conj hclass, rootGroup, rootGroup, h]
    have hbot := rootGroup_inf_eq_bot_of_rootClosure hD hrc hd hyd hroot
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz2 : (z : G) ∈ (rootGroup D d).map (MulAut.conj (y : G)).toMonoidHom := by
      rw [← map_subtype_map_conj_subgroupOf hAX y]
      exact Subgroup.mem_map_of_mem _ hz.2
    rw [← rootGroup_conj hclass] at hz2
    have hmem : (z : G) ∈ rootGroup D d ⊓ rootGroup D ((y : G) * d * (y : G)⁻¹) := ⟨hz.1, hz2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hgen : ∀ N : Subgroup X, (∀ y : X, y * y = 1 → y ∈ N) → N = ⊤ := by
    intro N hN
    have hAN : (rootGroup D d).subgroupOf X ≤ N := fun a ha =>
      hN a (Subtype.ext (mul_self_eq_one_of_mem_rootGroup hD hd ha))
    have hBN : (rootGroup D c).subgroupOf X ≤ N := fun b hb =>
      hN b (Subtype.ext (mul_self_eq_one_of_mem_rootGroup hD hc hb))
    have htop : (rootGroup D d ⊔ rootGroup D c).subgroupOf X = ⊤ :=
      Subgroup.subgroupOf_eq_top.2 hX.le
    rw [eq_top_iff, ← htop, Subgroup.subgroupOf_sup hAX hBX]
    exact sup_le hAN hBN
  have hdX : d ∈ X := hAX (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  have hcX : c ∈ X := hBX (rootSet_subset_rootGroup D c (mem_rootSet_self hc))
  have hdP : (⟨d, hdX⟩ : X) ∈ (P : Subgroup X) :=
    rootSet_subset_rootGroup D d (mem_rootSet_self hd)
  have hd2 := hD.mul_self_eq_one hd
  have hc2 := hD.mul_self_eq_one hc
  have htrans : ∀ e ∈ (P : Subgroup X), e ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), n * ⟨d, hdX⟩ * n⁻¹ = e := by
    intro e he he1
    have heT : (e : G) ∈ rootSet D d :=
      mem_rootSet_of_mem_rootGroup_of_ne_one hD hrc hd he fun h => he1 (Subtype.ext h)
    have he2 := hD.mul_self_eq_one heT.1
    have hoe := (odd_orderOf_mul_of_mem_rootSet hD hd hc heT (mem_rootSet_self hc) hodd hdc).1
    have hrX : dihedralSwap d c ∈ X :=
      Subgroup.mul_mem _ hdX (Subgroup.pow_mem _ (Subgroup.mul_mem _ hdX hcX) _)
    have hr'X : dihedralSwap (e : G) c ∈ X :=
      Subgroup.mul_mem _ e.2 (Subgroup.pow_mem _ (Subgroup.mul_mem _ e.2 hcX) _)
    have hconj : dihedralSwap (e : G) c * dihedralSwap d c * d *
        (dihedralSwap (e : G) c * dihedralSwap d c)⁻¹ = e := by
      rw [mul_inv_rev, show dihedralSwap (e : G) c * dihedralSwap d c * d *
          ((dihedralSwap d c)⁻¹ * (dihedralSwap (e : G) c)⁻¹) = dihedralSwap (e : G) c *
          (dihedralSwap d c * d * (dihedralSwap d c)⁻¹) * (dihedralSwap (e : G) c)⁻¹ by group,
        dihedralSwap_conj hd2 hc2 hodd, dihedralSwap_conj' he2 hc2 hoe]
    refine ⟨⟨_, Subgroup.mul_mem _ hr'X hrX⟩, ?_, Subtype.ext hconj⟩
    rw [← map_conj_eq_self_iff]
    refine (map_conj_subgroupOf_eq_self_iff hAX _).2 ?_
    change (rootGroup D d).map (MulAut.conj (dihedralSwap (e : G) c *
      dihedralSwap d c)).toMonoidHom = rootGroup D d
    rw [← rootGroup_conj hclass, hconj, rootGroup_eq_of_mem heT]
  have hcard := card_sylow_two_le_of_isTI P hexp (hcardP ▸ hq) hTI hgen hdP htrans
  have hsm : ∀ y : X, ((y • P : Sylow 2 X) : Subgroup X).map X.subtype =
      (rootGroup D d).map (MulAut.conj (y : G)).toMonoidHom := by
    intro y
    rw [Sylow.coe_subgroup_smul]
    exact map_subtype_map_conj_subgroupOf hAX y
  have key : ∀ y y' : X, y • P = y' • P → (rootGroup D d).map (MulAut.conj (y : G)).toMonoidHom =
      (rootGroup D d).map (MulAut.conj (y' : G)).toMonoidHom := by
    intro y y' h
    rw [← hsm, ← hsm, h]
  have hσX : dihedralSwap d c ∈ X :=
    Subgroup.mul_mem _ hdX (Subgroup.pow_mem _ (Subgroup.mul_mem _ hdX hcX) _)
  have hσA := map_conj_dihedralSwap hclass hD hd hc hodd
  have hAB := rootGroup_ne_of_opposite hclass hd hc hdc
  have hgB : ∀ g ∈ rootGroup D c,
      (rootGroup D d).map (MulAut.conj g).toMonoidHom ≠ rootGroup D c := by
    intro g hg h
    apply hAB
    rw [map_conj_eq_iff, map_conj_of_mem ((rootGroup D c).inv_mem hg)] at h
    exact h
  let F : Option (rootGroup D c) → Sylow 2 X := fun o =>
    o.elim ((⟨_, hσX⟩ : X) • P) fun g => (⟨g, hBX g.2⟩ : X) • P
  have hF : Function.Injective F := by
    rintro (_ | g) (_ | g') h
    · rfl
    · exact absurd ((key _ _ h).symm.trans hσA) (hgB g' g'.2)
    · exact absurd ((key _ _ h).trans hσA) (hgB g g.2)
    · exact congrArg some (Subtype.ext (map_conj_rootGroup_injOn hclass hD hrc hd hc hdc hodd
        g.2 g'.2 (key _ _ h)))
  have hle : Nat.card (Sylow 2 X) ≤ Nat.card (Option (rootGroup D c)) := by
    rw [Finite.card_option, card_rootGroup_eq hclass hD hrc hd hc, ← hcardP]
    exact hcard
  have hbij := hF.bijective_of_nat_card_le hle
  intro x hx hne
  rw [← hX] at hx
  obtain ⟨o, ho⟩ := hbij.2 ((⟨x, hx⟩ : X) • P)
  cases o with
  | none => exact absurd ((key _ _ ho).symm.trans hσA) hne
  | some g => exact ⟨g, g.2, (key _ _ ho).symm⟩

theorem four_le_card_rootGroup [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hrc : RootClosure D) (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d)
    {d : G} (hd : d ∈ D) : 4 ≤ Nat.card (rootGroup D d) := by
  obtain ⟨d₀, hd₀, e, he, hne⟩ := hl
  obtain ⟨m, hm⟩ := exists_card_rootGroup_eq_two_pow hD hd
  have h3 : 3 ≤ Nat.card (rootGroup D d) := by
    rw [card_rootGroup_eq hclass hD hrc hd₀ hd, card_rootGroup_of_rootClosure hD hrc hd₀]
    have : 1 < (rootSet D d₀).ncard :=
      (Set.one_lt_ncard (Set.toFinite _)).2 ⟨e, he, d₀, mem_rootSet_self hd₀, hne⟩
    omega
  rw [hm] at h3 ⊢
  have h2 : 2 ≤ m := by
    by_contra h
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2

end RootGroups

end CFSG.Timmesfeld.Bridge
