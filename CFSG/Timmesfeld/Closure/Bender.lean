module

public import CFSG.Timmesfeld.Closure.MinCex
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.StronglyEmbedded
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Timmesfeld.Connectivity

open CFSG.Open

universe u

section Embedding

variable {X : Type*} [Group X] {M : Subgroup X}

theorem not_mem_of_odd_card {H : Subgroup X} (hH : Odd (Nat.card H)) {t : X}
    (ht : orderOf t = 2) : t ∉ H := by
  intro htH
  have h := Subgroup.orderOf_dvd_natCard H htH
  rw [ht] at h
  exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 h)

theorem odd_card_inf_map_conj (hM : fusionStronglyEmbedded M) {g : X} (hg : g ∉ M) :
    Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) := by
  have hg' : g⁻¹ ∉ M := fun h => hg (by simpa using M.inv_mem h)
  simpa using hM.2.2 g⁻¹ hg'

theorem mem_of_commute_of_stronglyEmbedded (hM : fusionStronglyEmbedded M) {t c : X}
    (htM : t ∈ M) (ht : orderOf t = 2) (hc : Commute c t) : c ∈ M := by
  by_contra hcM
  refine not_mem_of_odd_card (odd_card_inf_map_conj hM hcM) ht (Subgroup.mem_inf.2 ⟨htM, ?_⟩)
  refine Subgroup.mem_map.2 ⟨t, htM, ?_⟩
  simp [MulAut.conj_apply, hc.eq]

theorem conj_pow_mul_left {u j : X} (hu : u * u = 1) (hj : j * j = 1) (m : ℕ) :
    u * (u * j) ^ m * u⁻¹ = ((u * j) ^ m)⁻¹ := by
  have hj' : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have h1 : u * (u * j) * u⁻¹ = (u * j)⁻¹ :=
    calc u * (u * j) * u⁻¹ = (u * u) * j * u⁻¹ := by group
      _ = (u * j)⁻¹ := by rw [hu, one_mul, mul_inv_rev, hj']
  rw [← conj_pow, h1, inv_pow]

theorem conj_pow_mul_right {u j : X} (hu : u * u = 1) (hj : j * j = 1) (m : ℕ) :
    j * (u * j) ^ m * j⁻¹ = ((u * j) ^ m)⁻¹ := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h1 : j * (u * j) * j⁻¹ = (u * j)⁻¹ :=
    calc j * (u * j) * j⁻¹ = j * u * (j * j⁻¹) := by group
      _ = (u * j)⁻¹ := by rw [mul_inv_cancel, mul_one, mul_inv_rev, hu',
          inv_eq_of_mul_eq_one_right hj]
  rw [← conj_pow, h1, inv_pow]

theorem commute_of_conj_eq {u k : X} (h : u * k * u⁻¹ = k) : Commute k u := by
  show k * u = u * k
  calc k * u = (u * k * u⁻¹) * u := by rw [h]
    _ = u * k := by group

theorem isConj_of_stronglyEmbedded [Finite X] (hM : fusionStronglyEmbedded M) {g : X} (hg : g ∉ M)
    {u j : X} (huM : u ∈ M) (hu : orderOf u = 2) (hjM : j ∈ M.map (MulAut.conj g).toMonoidHom)
    (hj : orderOf j = 2) : IsConj u j := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hj2 : j * j = 1 := by rw [← pow_two, ← hj, pow_orderOf_eq_one]
  by_cases hodd : Odd (orderOf (u * j))
  · obtain ⟨h, -, hh⟩ := exists_conj_of_odd_orderOf_mul hu2 hj2 hodd
    exact isConj_iff.2 ⟨h, hh⟩
  exfalso
  have hpos : 0 < orderOf (u * j) := orderOf_pos _
  have hdvd : 2 ∣ orderOf (u * j) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  set k := (u * j) ^ (orderOf (u * j) / 2) with hk
  have hk2 : orderOf k = 2 := orderOf_pow_orderOf_div hpos.ne' hdvd
  have hkinv : k⁻¹ = k := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_two, ← hk2, pow_orderOf_eq_one]
  have hku : Commute k u := commute_of_conj_eq (by rw [conj_pow_mul_left hu2 hj2, hkinv])
  have hkj : Commute k j := commute_of_conj_eq (by rw [conj_pow_mul_right hu2 hj2, hkinv])
  have hkM : k ∈ M := mem_of_commute_of_stronglyEmbedded hM huM hu hku
  obtain ⟨j', hj'M, rfl⟩ := Subgroup.mem_map.1 hjM
  have hj'2 : orderOf j' = 2 := by
    rw [← hj]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective j').symm
  have hkM' : k ∈ M.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.mem_map.2 ⟨g⁻¹ * k * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    refine mem_of_commute_of_stronglyEmbedded hM hj'M hj'2 ?_
    have hc := hkj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
    show g⁻¹ * k * g * j' = j' * (g⁻¹ * k * g)
    have e := hc.eq
    calc g⁻¹ * k * g * j' = g⁻¹ * (k * (g * j' * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * j' * g⁻¹) * k) * g := by rw [e]
      _ = j' * (g⁻¹ * k * g) := by group
  exact not_mem_of_odd_card (odd_card_inf_map_conj hM hg) hk2 (Subgroup.mem_inf.2 ⟨hkM, hkM'⟩)

theorem commute_of_mem_sylow [Finite X] (Q : Sylow 2 X)
    (hM : fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup X) : Set X)))
    {u : X} (huQ : u ∈ (Q : Subgroup X)) (hu : orderOf u = 2) {v : X}
    (hvQ : v ∈ (Q : Subgroup X)) : Commute v u := by
  set M := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hMdef
  have hQM : (Q : Subgroup X) ≤ M := Subgroup.le_normalizer
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by decide)
  have hQnt : Nontrivial (Q : Subgroup X) :=
    ⟨⟨⟨u, huQ⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial (Subgroup.center (Q : Subgroup X)) := Q.isPGroup'.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center (Q : Subgroup X)) :=
    Q.isPGroup'.to_subgroup (Subgroup.center _)
  have hZdvd : 2 ∣ Nat.card (Subgroup.center (Q : Subgroup X)) := by
    have := Fact.mk Nat.prime_two
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    have hpos : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hn
    rw [hn]
    exact dvd_pow_self 2 hpos
  have := Fact.mk Nat.prime_two
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZdvd
  set z' : X := ((z : Q) : X) with hz'
  have hz'Q : z' ∈ (Q : Subgroup X) := (z : Q).2
  have hz'2 : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hz'c : ∀ w ∈ (Q : Subgroup X), Commute z' w := by
    intro w hw
    have := Subgroup.mem_center_iff.1 z.2 ⟨w, hw⟩
    exact congrArg Subtype.val this.symm
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra hall
    push Not at hall
    exact hM.1 (eq_top_iff.2 fun x _ => hall x)
  have hjM : g * z' * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.2 ⟨z', hQM hz'Q, by simp [MulAut.conj_apply]⟩
  have hj2 : orderOf (g * z' * g⁻¹) = 2 := by
    rw [← hz'2, ← orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z']
    simp [MulAut.conj_apply]
  have hconj : IsConj z' u :=
    ((isConj_of_stronglyEmbedded hM hg (hQM huQ) hu hjM hj2).trans
      (isConj_iff.2 ⟨g, rfl⟩).symm).symm
  obtain ⟨h, hh⟩ := isConj_iff.1 hconj
  set Q' := (Q : Subgroup X).map (MulAut.conj h).toMonoidHom with hQ'
  have hQ'M : Q' ≤ M := by
    rintro _ ⟨w, hw, rfl⟩
    refine mem_of_commute_of_stronglyEmbedded hM (hQM huQ) hu ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hh]
    have e := (hz'c w hw).eq
    show h * w * h⁻¹ * (h * z' * h⁻¹) = h * z' * h⁻¹ * (h * w * h⁻¹)
    calc h * w * h⁻¹ * (h * z' * h⁻¹) = h * (w * z') * h⁻¹ := by group
      _ = h * (z' * w) * h⁻¹ := by rw [e]
      _ = h * z' * h⁻¹ * (h * w * h⁻¹) := by group
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map _
  have hsup : IsPGroup 2 ↥((Q : Subgroup X) ⊔ Q') :=
    IsPGroup.to_sup_of_normal_left' Q.isPGroup' hQ'2 hQ'M
  have heq : (Q : Subgroup X) ⊔ Q' = Q := Q.is_maximal' hsup le_sup_left
  have hQ'le : Q' ≤ Q := heq ▸ le_sup_right
  have hcard : Nat.card Q' = Nat.card (Q : Subgroup X) :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hQ'eq : Q' = Q := Subgroup.eq_of_le_of_card_ge hQ'le hcard.ge
  have hvQ' : v ∈ Q' := hQ'eq ▸ hvQ
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 hvQ'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwv
  rw [← hwv, ← hh]
  have e := (hz'c w hw).eq
  show h * w * h⁻¹ * (h * z' * h⁻¹) = h * z' * h⁻¹ * (h * w * h⁻¹)
  calc h * w * h⁻¹ * (h * z' * h⁻¹) = h * (w * z') * h⁻¹ := by group
    _ = h * (z' * w) * h⁻¹ := by rw [e]
    _ = h * z' * h⁻¹ * (h * w * h⁻¹) := by group

theorem not_orderOf_mul_eq_four [Finite X]
    (hB : ∀ Q : Sylow 2 X, fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup X) : Set X)))
    {s t : X} (hs : orderOf s = 2) (ht : orderOf t = 2) : orderOf (s * t) ≠ 4 := by
  intro h4
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hpow : (s * t) ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← h4]
    exact pow_orderOf_eq_one _
  obtain ⟨Q, hQ⟩ := (isPGroup_two_closure_pair hs2 ht2 hpow).exists_le_sylow
  have hsQ : s ∈ (Q : Subgroup X) := hQ (Subgroup.subset_closure (by simp))
  have htQ : t ∈ (Q : Subgroup X) := hQ (Subgroup.subset_closure (by simp))
  have hc : Commute t s := commute_of_mem_sylow Q (hB Q) hsQ hs htQ
  have hsq : (s * t) ^ 2 = 1 := by
    rw [pow_two, show s * t * (s * t) = s * (t * s) * t by group, hc.eq,
      show s * (s * t) * t = (s * s) * (t * t) by group, hs2, ht2, one_mul]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [h4] at hdvd
  exact absurd hdvd (by decide)

end Embedding

section Bender

theorem exists_fusionBenderBorel_of_isBenderGroup {X : Type*} [Group X] [Finite X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) : ∃ q k : ℕ, fusionBenderBorel X q k := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_surjective e e.surjective
    exact ⟨_, _, (bender_psl2_borel_full n hn).map_mulEquiv e.symm⟩
  · have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : X ≃* Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (Sz n) := Finite.of_surjective e' e'.surjective
    exact ⟨_, _, (bender_suzuki_borel_full n hn).map_mulEquiv e'.symm⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : X ≃* PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (PSU3 2 n) := Finite.of_surjective e' e'.surjective
    exact ⟨_, _, (bender_psu3_borel_full n hn).map_mulEquiv e'.symm⟩

theorem not_orderOf_mul_eq_four_of_stronglyEmbedded {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] (M : Subgroup X) (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M)
    {s t : X} (hs : orderOf s = 2) (ht : orderOf t = 2) : orderOf (s * t) ≠ 4 := by
  obtain ⟨q, k, hB⟩ :=
    exists_fusionBenderBorel_of_isBenderGroup (CFSG.BenderSuzuki.bender_suzuki M hM)
  exact not_orderOf_mul_eq_four (fun Q => (hB Q).1) hs ht

end Bender

@[expose] def StrongEmbeddingInput : Prop :=
  ∀ (G : Type u) [Group G] (D : Set G) (hS : Setting D), Disconnected D → IsSimpleGroup G →
    ker hS.normal = ⊥ →
    (∀ L : Subgroup G, L ≠ ⊤ → ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → d ∈ L → e ∈ L →
      L ≤ compStab hS.normal d) →
    ∀ d ∈ D, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (compStab hS.normal d)

theorem simpleCaseInput_of_strongEmbedding (h : StrongEmbeddingInput.{u}) :
    SimpleCaseInput.{u} := by
  intro G _ D hS hdisc hsimp hfaith hM2
  have := hS.finite
  obtain ⟨d, hd, e, he, h4⟩ := hS.nondeg
  exact not_orderOf_mul_eq_four_of_stronglyEmbedded (compStab hS.normal d)
    (h G D hS hdisc hsimp hfaith hM2 d hd) (hS.root.orderOf_eq_two hd)
    (hS.root.orderOf_eq_two he) h4

theorem commConnected_of_strongEmbedding (h : StrongEmbeddingInput.{u}) {G : Type u} [Group G]
    {D : Set G} (hH : Hyp G D) : Closure.CommConnected D :=
  commConnected_of_simpleCase (simpleCaseInput_of_strongEmbedding h) hH

end CFSG.Timmesfeld.Connectivity
