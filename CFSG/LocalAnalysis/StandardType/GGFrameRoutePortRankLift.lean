module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift

public section

namespace CFSG.StandardType.FrameRoute

open scoped commutatorElement

private theorem inv_mul_inv_eq_self_of_pow_three {G : Type*} [Group G] {a : G}
    (ha : a ^ 3 = 1) : a⁻¹ * a⁻¹ = a := by
  have h : a * a * a = 1 := by simpa [pow_succ, mul_assoc] using ha
  calc a⁻¹ * a⁻¹ = a⁻¹ * a⁻¹ * (a * a * a) := by rw [h, mul_one]
    _ = a := by group

private theorem mem_center_of_map_eq_one {J M : Type*} [Group J] [Group M] {π : J →* M}
    (hker : π.ker ≤ Subgroup.center J) {z : J} (hz : π z = 1) :
    z ∈ Subgroup.center J :=
  hker (by simpa [MonoidHom.mem_ker] using hz)

private theorem cube_eq_one_of_inverting_lift {J M : Type*} [Group J] [Group M]
    {π : J →* M} (hker : π.ker ≤ Subgroup.center J) {f s : J}
    (hf3 : (π f) ^ 3 = 1) (hs : π (s * f * s⁻¹) = (π f)⁻¹) :
    (s * f * s⁻¹ * f⁻¹) ^ 3 = 1 ∧ π (s * f * s⁻¹ * f⁻¹) = π f := by
  set g : J := s * f * s⁻¹ with hg
  set c : J := f * g with hc
  have hπg : π g = (π f)⁻¹ := by rw [hg]; exact hs
  have hπc : π c = 1 := by rw [hc, map_mul, hπg, mul_inv_cancel]
  have hcZ : c ∈ Subgroup.center J := mem_center_of_map_eq_one hker hπc
  have hc_comm : ∀ z : J, c * z = z * c :=
    fun z => (Subgroup.mem_center_iff.mp hcZ z).symm
  have hgc : g = f⁻¹ * c := by rw [hc]; group
  have he : s * f * s⁻¹ * f⁻¹ = f⁻¹ * c * f⁻¹ := by rw [← hgc]
  have he' : s * f * s⁻¹ * f⁻¹ = f⁻¹ * f⁻¹ * c := by
    rw [he, mul_assoc, hc_comm f⁻¹, mul_assoc]
  have hf3Z : f ^ 3 ∈ Subgroup.center J := by
    apply mem_center_of_map_eq_one hker
    rw [map_pow, hf3]
  have hf3_comm : ∀ z : J, f ^ 3 * z = z * f ^ 3 :=
    fun z => (Subgroup.mem_center_iff.mp hf3Z z).symm
  have hconjpow : (s * f * s⁻¹) ^ 3 = s * f ^ 3 * s⁻¹ := by
    rw [pow_three', pow_three']
    group
  have hg3 : g ^ 3 = f ^ 3 := by
    rw [hg]
    calc (s * f * s⁻¹) ^ 3 = s * f ^ 3 * s⁻¹ := hconjpow
      _ = f ^ 3 := by rw [← hf3_comm s]; group
  have hg3' : g ^ 3 = (f⁻¹) ^ 3 * c ^ 3 := by
    rw [hgc]
    exact (show Commute f⁻¹ c from (hc_comm f⁻¹).symm).mul_pow 3
  have hc3 : c ^ 3 = f ^ 6 := by
    have h : f ^ 3 = (f⁻¹) ^ 3 * c ^ 3 := hg3.symm.trans hg3'
    calc c ^ 3 = f ^ 3 * ((f⁻¹) ^ 3 * c ^ 3) := by group
      _ = f ^ 3 * f ^ 3 := by rw [← h]
      _ = f ^ 6 := by rw [← pow_add]
  refine ⟨?_, ?_⟩
  · calc (s * f * s⁻¹ * f⁻¹) ^ 3 = (f⁻¹ * f⁻¹ * c) ^ 3 := by rw [he']
      _ = (f⁻¹ * f⁻¹) ^ 3 * c ^ 3 := by
        exact (show Commute (f⁻¹ * f⁻¹) c from (hc_comm (f⁻¹ * f⁻¹)).symm).mul_pow 3
      _ = (f⁻¹) ^ 6 * c ^ 3 := by group
      _ = (f⁻¹) ^ 6 * f ^ 6 := by rw [hc3]
      _ = 1 := by group
  · rw [he]
    simp only [map_mul, map_inv, hπc, mul_one]
    exact inv_mul_inv_eq_self_of_pow_three hf3

private theorem conj_commutator_eq_inv_of_mul_central {G : Type*} [Group G] {x y s c₁ c₂ : G}
    (hd : ⁅x, y⁆ ∈ Subgroup.center G) (hc₁ : c₁ ∈ Subgroup.center G)
    (hc₂ : c₂ ∈ Subgroup.center G) (hsx : s * x * s⁻¹ = x * c₁)
    (hsy : s * y * s⁻¹ = y⁻¹ * c₂) :
    MulAut.conj s ⁅x, y⁆ = ⁅x, y⁆⁻¹ := by
  have hmap : (MulAut.conj s) ⁅x, y⁆ =
      ⁅(MulAut.conj s) x, (MulAut.conj s) y⁆ := by
    simp
  rw [hmap, show (MulAut.conj s) x = x * c₁ by rw [MulAut.conj_apply]; exact hsx,
    show (MulAut.conj s) y = y⁻¹ * c₂ by rw [MulAut.conj_apply]; exact hsy]
  rw [CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_of_central_right _ hc₂,
    CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_of_central_left hc₁ _,
    commutatorElement_inv_right]
  have hd_inv : ⁅y, x⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem hd
  rw [commutatorElement_inv]
  rw [Subgroup.mem_center_iff.mp hd_inv y⁻¹]
  group

private theorem commute_of_twoElem_of_conj_fixes {J M : Type*} [Group J] [Group M]
    {π : J →* M} (hker : π.ker ≤ Subgroup.center J) {x t : J} (hx3 : x ^ 3 = 1)
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (hconj : π (t * x * t⁻¹) = π x) :
    Commute t x := by
  set c : J := ⁅t, x⁆ with hc
  have hcZ : c ∈ Subgroup.center J := by
    apply mem_center_of_map_eq_one hker
    rw [hc, commutatorElement_def]
    simp only [map_mul, map_inv, hconj, mul_inv_cancel]
  have hct : Commute t c := Subgroup.mem_center_iff.mp hcZ t
  have hcx : Commute x c := Subgroup.mem_center_iff.mp hcZ x
  have hc3 : c ^ 3 = 1 := by
    rw [hc]
    rw [(by rwa [hc] at hcx : Commute x ⁅t, x⁆).commutatorElement_pow_right 3, hx3]
    simp [commutatorElement_def]
  obtain ⟨k, hk⟩ := ht2
  have hc2 : c ^ 2 ^ k = 1 := by
    rw [hc]
    rw [(by rwa [hc] at hct : Commute t ⁅t, x⁆).commutatorElement_pow_left (2 ^ k), hk]
    simp [commutatorElement_def]
  have hdvd3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hdvd2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hone : orderOf c = 1 := by
    have hgcd : orderOf c ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hdvd3 hdvd2
    rw [hcop.gcd_eq_one] at hgcd
    exact Nat.dvd_one.mp hgcd
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hone
  rw [hc] at hc1
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

private theorem commute_of_cube_eq_one_of_conj {J M : Type*} [Group J] [Group M]
    {π : J →* M} (hker : π.ker ≤ Subgroup.center J) {x y s : J}
    (hx3 : x ^ 3 = 1) (hxy : Commute (π x) (π y))
    (hsx : π (s * x * s⁻¹) = π x) (hsy : π (s * y * s⁻¹) = (π y)⁻¹) :
    Commute x y := by
  set d : J := ⁅x, y⁆ with hd
  have hdZ : d ∈ Subgroup.center J := by
    apply mem_center_of_map_eq_one hker
    rw [hd, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
  have hd_comm : ∀ z : J, d * z = z * d :=
    fun z => (Subgroup.mem_center_iff.mp hdZ z).symm
  have hd3 : d ^ 3 = 1 := by
    rw [hd]
    have hdZ' : ⁅x, y⁆ ∈ Subgroup.center J := by rwa [hd] at hdZ
    have hx_d : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hdZ' x
    rw [hx_d.commutatorElement_pow_left 3, hx3]
    simp [commutatorElement_def]
  set c₁ : J := x⁻¹ * (s * x * s⁻¹) with hc₁
  set c₂ : J := y * (s * y * s⁻¹) with hc₂
  have hc₁Z : c₁ ∈ Subgroup.center J := by
    apply mem_center_of_map_eq_one hker
    rw [hc₁, map_mul, map_inv, hsx, inv_mul_cancel]
  have hc₂Z : c₂ ∈ Subgroup.center J := by
    apply mem_center_of_map_eq_one hker
    rw [hc₂, map_mul, hsy, mul_inv_cancel]
  have hsx' : s * x * s⁻¹ = x * c₁ := by rw [hc₁]; group
  have hsy' : s * y * s⁻¹ = y⁻¹ * c₂ := by rw [hc₂]; group
  have hconj : MulAut.conj s d = d⁻¹ := by
    rw [hd]
    exact conj_commutator_eq_inv_of_mul_central hdZ hc₁Z hc₂Z hsx' hsy'
  have hfix : MulAut.conj s d = d := by
    rw [MulAut.conj_apply, ← hd_comm s]
    group
  have hdd : d = d⁻¹ := hfix.symm.trans hconj
  have hd2 : d ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hdd]
    exact inv_mul_cancel d
  have hd1 : d = 1 := by
    calc d = d ^ 3 := by rw [pow_succ, hd2, one_mul]
      _ = 1 := hd3
  rw [hd] at hd1
  exact commutatorElement_eq_one_iff_mul_comm.mp hd1


private def rankLiftElem {J : Type*} [Group J] {r : ℕ} (ŝ f : Fin r → J) (i : Fin r) : J :=
  ŝ i * f i * (ŝ i)⁻¹ * (f i)⁻¹

private abbrev LiftDomain {J : Type*} [Group J] {r : ℕ} (ê : Fin r → J) :=
  (i : Fin r) → ↥(Subgroup.zpowers (ê i))

private theorem commute_zpowers_of_ne {G : Type*} [Group G] {r : ℕ} {x : Fin r → G}
    (h : ∀ i j, i ≠ j → Commute (x i) (x j)) :
    ∀ i j : Fin r, i ≠ j → ∀ a b : G, a ∈ Subgroup.zpowers (x i) →
      b ∈ Subgroup.zpowers (x j) → Commute a b := by
  intro i j hij a b ha hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (h i j hij).zpow_zpow m n

private theorem rankLift_cube {J M : Type*} [Group J] [Group M] {π : J →* M}
    (hker : π.ker ≤ Subgroup.center J) {r : ℕ} {e : Fin r → M} (he3 : ∀ i, e i ^ 3 = 1)
    {ŝ f : Fin r → J} {s : Fin r → M} (hπŝ : ∀ i, π (ŝ i) = s i)
    (hsinv : ∀ i, s i * e i * (s i)⁻¹ = (e i)⁻¹) (hπf : ∀ i, π (f i) = e i) :
    (∀ i, (rankLiftElem ŝ f i) ^ 3 = 1) ∧
      ∀ i, π (rankLiftElem ŝ f i) = e i := by
  have hcube : ∀ i, (ŝ i * f i * (ŝ i)⁻¹ * (f i)⁻¹) ^ 3 = 1 ∧
      π (ŝ i * f i * (ŝ i)⁻¹ * (f i)⁻¹) = e i := by
    intro i
    have hf3 : (π (f i)) ^ 3 = 1 := by rw [hπf]; exact he3 i
    have hs' : π (ŝ i * f i * (ŝ i)⁻¹) = (π (f i))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hπŝ i, hπf i, hsinv i]
    obtain ⟨h1, h2⟩ := cube_eq_one_of_inverting_lift hker hf3 hs'
    exact ⟨h1, by simpa [hπf i] using h2⟩
  exact ⟨fun i => by simpa [rankLiftElem] using (hcube i).1,
    fun i => by simpa [rankLiftElem] using (hcube i).2⟩

private theorem rankLift_pair_comm {J M : Type*} [Group J] [Group M] {π : J →* M}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J) {r : ℕ}
    {e : Fin r → M} (hcomm : ∀ i j, Commute (e i) (e j)) {ê : Fin r → J}
    (he3' : ∀ i, (ê i) ^ 3 = 1) (hπê : ∀ i, π (ê i) = e i)
    (hpair : ∀ i j, i ≠ j → ∃ s : M, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
      ((s * e i * s⁻¹ = e i ∧ s * e j * s⁻¹ = (e j)⁻¹) ∨
        (s * e i * s⁻¹ = (e i)⁻¹ ∧ s * e j * s⁻¹ = e j))) :
    ∀ i j, i ≠ j → Commute (ê i) (ê j) := by
  intro i j hij
  obtain ⟨sij, -, hfixinv⟩ := hpair i j hij
  obtain ⟨ŝij, hπŝij⟩ := hπ sij
  rcases hfixinv with ⟨hfixi, hinvj⟩ | ⟨hinvi, hfixj⟩
  · have hsx : π (ŝij * ê i * ŝij⁻¹) = π (ê i) := by
      rw [map_mul, map_mul, map_inv, hπŝij, hπê i, hfixi]
    have hsy : π (ŝij * ê j * ŝij⁻¹) = (π (ê j))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hπŝij, hπê j, hinvj]
    exact commute_of_cube_eq_one_of_conj hker (he3' i)
      (by rw [hπê i, hπê j]; exact hcomm i j) hsx hsy
  · have hsy : π (ŝij * ê j * ŝij⁻¹) = π (ê j) := by
      rw [map_mul, map_mul, map_inv, hπŝij, hπê j, hfixj]
    have hsx : π (ŝij * ê i * ŝij⁻¹) = (π (ê i))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hπŝij, hπê i, hinvi]
    exact (commute_of_cube_eq_one_of_conj hker (he3' j)
      (by rw [hπê j, hπê i]; exact hcomm j i) hsy hsx).symm

private theorem rankLift_prod_orderOf {M : Type*} [Group M] {r : ℕ} (e : Fin r → M)
    (he3 : ∀ i, e i ^ 3 = 1) (hcomm : ∀ i j, Commute (e i) (e j))
    (hcard : Nat.card (Subgroup.closure (Set.range e)) = 3 ^ r) :
    (∏ i, orderOf (e i)) = 3 ^ r := by
  have hcomm_pair : Pairwise fun i j : Fin r => ∀ x y : M,
      x ∈ Subgroup.zpowers (e i) → y ∈ Subgroup.zpowers (e j) → Commute x y := by
    intro i j _ x y hx hy
    exact commute_zpowers_of_ne (fun i j _ => hcomm i j) i j ‹i ≠ j› x y hx hy
  let FM0 : ((i : Fin r) → ↥(Subgroup.zpowers (e i))) →* M :=
    Subgroup.noncommPiCoprod hcomm_pair
  have hFM0range : FM0.range = Subgroup.closure (Set.range e) := by
    have hFM0 : FM0 = Subgroup.noncommPiCoprod hcomm_pair := rfl
    rw [hFM0, Subgroup.noncommPiCoprod_range]
    exact CFSG.LocalAnalysis.GorensteinLyons.iSup_zpowers_eq_closure_range e
  have hcardDom0 : Nat.card ((i : Fin r) → ↥(Subgroup.zpowers (e i))) =
      ∏ i, orderOf (e i) := by
    rw [Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => Nat.card_zpowers (e i)
  have hdiv0 : 3 ^ r ∣ ∏ i, orderOf (e i) := by
    rw [← hcard, ← hFM0range, ← hcardDom0]
    exact Subgroup.card_range_dvd FM0
  have hthree : (∏ i : Fin r, (3 : ℕ)) = 3 ^ r := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hproddiv : (∏ i, orderOf (e i)) ∣ 3 ^ r := by
    rw [← hthree]
    exact Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun i => orderOf (e i))
      (fun _ => 3) fun i _ => orderOf_dvd_of_pow_eq_one (he3 i)
  exact Nat.dvd_antisymm hproddiv hdiv0

private theorem rankLift_orderOf {M : Type*} [Group M] {r : ℕ} (e : Fin r → M)
    (he3 : ∀ i, e i ^ 3 = 1) (hcomm : ∀ i j, Commute (e i) (e j))
    (hcard : Nat.card (Subgroup.closure (Set.range e)) = 3 ^ r) :
    ∀ i, orderOf (e i) = 3 := by
  have hprodeq := rankLift_prod_orderOf e he3 hcomm hcard
  have hthree : (∏ i : Fin r, (3 : ℕ)) = 3 ^ r := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  intro i
  rcases (Nat.dvd_prime Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one (he3 i)) with h1 | h3
  · exfalso
    have hlt : (∏ j, orderOf (e j)) < ∏ j : Fin r, (3 : ℕ) := by
      apply Finset.prod_lt_prod₀
      · intro j _
        exact Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one (he3 j)) (by norm_num)
      · intro j _
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (he3 j))
      · exact ⟨i, Finset.mem_univ i, by rw [h1]; norm_num⟩
    rw [hprodeq, hthree] at hlt
    exact lt_irrefl _ hlt
  · exact h3

private theorem rankLift_orderOf_lift {J M : Type*} [Group J] [Group M] {π : J →* M}
    {r : ℕ} {e : Fin r → M} {ê : Fin r → J} (hπê : ∀ i, π (ê i) = e i)
    (he3' : ∀ i, (ê i) ^ 3 = 1) (hord_e : ∀ i, orderOf (e i) = 3) :
    ∀ i, orderOf (ê i) = 3 := by
  intro i
  have hdvd : orderOf (e i) ∣ orderOf (ê i) := by
    rw [← hπê i]
    exact orderOf_map_dvd π (ê i)
  rw [hord_e i] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one (he3' i)) with h1 | h3
  · rw [h1] at hdvd
    exact absurd hdvd (by norm_num)
  · exact h3

private theorem rankLift_card_domain {J : Type*} [Group J] {r : ℕ} {ê : Fin r → J}
    (hord_ê : ∀ i, orderOf (ê i) = 3) : Nat.card (LiftDomain ê) = 3 ^ r := by
  rw [Nat.card_pi]
  rw [show (∏ i, Nat.card ↥(Subgroup.zpowers (ê i))) = ∏ i, orderOf (ê i) from
    Finset.prod_congr rfl fun i _ => Nat.card_zpowers (ê i)]
  rw [show (∏ i, orderOf (ê i)) = ∏ i : Fin r, (3 : ℕ) from
    Finset.prod_congr rfl fun i _ => hord_ê i]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem rankLift_F_exists {J M : Type*} [Group J] [Group M] {π : J →* M}
    {r : ℕ} {e : Fin r → M} {ê : Fin r → J}
    (hcommê : ∀ i j, i ≠ j → Commute (ê i) (ê j)) (hπê : ∀ i, π (ê i) = e i)
    (hcard : Nat.card (Subgroup.closure (Set.range e)) = 3 ^ r)
    (hord_ê : ∀ i, orderOf (ê i) = 3) :
    ∃ F : LiftDomain ê →* J, F.range = Subgroup.closure (Set.range ê) ∧
      (π.comp F).range = Subgroup.closure (Set.range e) ∧
      Function.Injective (π.comp F) := by
  have hcomm_pair : Pairwise fun i j : Fin r => ∀ x y : J,
      x ∈ Subgroup.zpowers (ê i) → y ∈ Subgroup.zpowers (ê j) → Commute x y :=
    commute_zpowers_of_ne hcommê
  let F : LiftDomain ê →* J := Subgroup.noncommPiCoprod hcomm_pair
  have hFrange : F.range = Subgroup.closure (Set.range ê) := by
    have hF : F = Subgroup.noncommPiCoprod hcomm_pair := rfl
    rw [hF, Subgroup.noncommPiCoprod_range]
    exact CFSG.LocalAnalysis.GorensteinLyons.iSup_zpowers_eq_closure_range ê
  have hcardDom := rankLift_card_domain hord_ê
  have hFMrange : (π.comp F).range = Subgroup.closure (Set.range e) := by
    rw [MonoidHom.range_comp, hFrange, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, hxy⟩
      exact ⟨i, (hπê i).symm.trans hxy⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ê i, ⟨i, rfl⟩, hπê i⟩
  have hcardFMrange : Nat.card (π.comp F).range = 3 ^ r := by rw [hFMrange, hcard]
  have hFMker : (π.comp F).ker = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hkey := Subgroup.card_ker_mul_card_range (π.comp F)
    rw [hcardFMrange, hcardDom] at hkey
    have hkey' : Nat.card (π.comp F).ker * 3 ^ r = 1 * 3 ^ r := by simpa using hkey
    exact mul_right_cancel₀ (by positivity : (0 : ℕ) < 3 ^ r).ne' hkey'
  exact ⟨F, hFrange, hFMrange, (MonoidHom.ker_eq_bot_iff (π.comp F)).mp hFMker⟩

private theorem rankLift_F_inj_card {J M : Type*} [Group J] [Group M] {π : J →* M}
    {r : ℕ} {ê : Fin r → J} {F : LiftDomain ê →* J}
    (hFrange : F.range = Subgroup.closure (Set.range ê))
    (hFMinj : Function.Injective (π.comp F)) (hcardDom : Nat.card (LiftDomain ê) = 3 ^ r) :
    Function.Injective F ∧ Nat.card (Subgroup.closure (Set.range ê)) = 3 ^ r := by
  have hFinj : Function.Injective F := by
    intro a b hab
    exact hFMinj (congrArg π hab)
  refine ⟨hFinj, ?_⟩
  rw [← hFrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hFinj,
    Subgroup.card_top]
  exact hcardDom

private theorem rankLift_center_bot {J M : Type*} [Group J] [Group M] {π : J →* M}
    (hπ : Function.Surjective π) {r : ℕ} {e : Fin r → M} {ê : Fin r → J}
    {F : LiftDomain ê →* J} (hFrange : F.range = Subgroup.closure (Set.range ê))
    (hFMrange : (π.comp F).range = Subgroup.closure (Set.range e))
    (hFMinj : Function.Injective (π.comp F))
    (hZ : Subgroup.closure (Set.range e) ⊓ Subgroup.center M = ⊥) :
    Subgroup.closure (Set.range ê) ⊓ Subgroup.center J = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxÊ, hxZ⟩ := hx
  have hxÊ' : x ∈ F.range := by rwa [← hFrange] at hxÊ
  obtain ⟨c, rfl⟩ := hxÊ'
  rw [Subgroup.mem_bot]
  have hxc : π (F c) ∈ Subgroup.center M :=
    Subgroup.map_center_le_center hπ (Subgroup.mem_map_of_mem π hxZ)
  have hxE : π (F c) ∈ Subgroup.closure (Set.range e) := by
    rw [← hFMrange]
    show (π.comp F) c ∈ (π.comp F).range
    exact ⟨c, rfl⟩
  have hxbot : π (F c) ∈ (⊥ : Subgroup M) := by
    rw [← hZ]
    exact ⟨hxE, hxc⟩
  have hx1 : π (F c) = 1 := Subgroup.mem_bot.mpr hxbot
  have hc1 : c = 1 := hFMinj (by simpa using hx1)
  rw [hc1, map_one]

private theorem rankLift_t {J M : Type*} [Group J] [Group M] [Finite J] {π : J →* M}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J) {r : ℕ}
    {e : Fin r → M} {ê : Fin r → J} (he3' : ∀ i, (ê i) ^ 3 = 1)
    (hπê : ∀ i, π (ê i) = e i) {t : M} (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1)
    (htZ : t ∉ Subgroup.center M) (ht : ∀ i, Commute t (e i)) :
    ∃ tJ : J, π tJ = t ∧ (∃ k : ℕ, tJ ^ 2 ^ k = 1) ∧
      (∀ i, Commute tJ (ê i)) ∧ tJ ∉ Subgroup.center J := by
  obtain ⟨x₀, hx₀⟩ := hπ t
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hu : (x₀ ^ m) ^ 2 ^ e = 1 := by
    rw [← pow_mul, mul_comm m (2 ^ e), ← hord, pow_orderOf_eq_one]
  obtain ⟨u, hu'⟩ := exists_pow_eq_self_of_coprime (x := t)
    ((hm.coprime_two_right.pow_right _).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one ht2.choose_spec))
  let tJ := (x₀ ^ m) ^ u
  have hπt : π tJ = t := by
    change π ((x₀ ^ m) ^ u) = t
    rw [map_pow, map_pow, hx₀, hu']
  have htJ2 : ∃ N : ℕ, tJ ^ 2 ^ N = 1 := by
    refine ⟨e, ?_⟩
    change ((x₀ ^ m) ^ u) ^ 2 ^ e = 1
    rw [← pow_mul, mul_comm u (2 ^ e), pow_mul, hu, one_pow]
  have htJ_comm : ∀ i, Commute tJ (ê i) := by
    intro i
    refine commute_of_twoElem_of_conj_fixes hker (he3' i) htJ2 ?_
    rw [map_mul, map_mul, map_inv, hπt, hπê i, (ht i).eq, mul_assoc, mul_inv_cancel,
      mul_one]
  have htJZ : tJ ∉ Subgroup.center J := by
    intro htJc
    apply htZ
    have hmem : t ∈ (Subgroup.center J).map π := by
      rw [← hπt]
      exact Subgroup.mem_map_of_mem π htJc
    exact Subgroup.map_center_le_center hπ hmem
  exact ⟨tJ, hπt, htJ2, htJ_comm, htJZ⟩

private theorem rankLift_centralizer {J : Type*} [Group J] {r : ℕ} {ê : Fin r → J}
    {tJ : J} (h : ∀ i, Commute tJ (ê i)) :
    Subgroup.closure (Set.range ê) ≤ Subgroup.centralizer ({tJ} : Set J) := by
  have htJ_central : tJ ∈ Subgroup.centralizer (Subgroup.closure (Set.range ê) : Set J) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact (h i).eq.symm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (Subgroup.mem_centralizer_iff.mp htJ_central x hx).symm

private theorem rankLift_isElemAbelian {J : Type*} [Group J] {r : ℕ} {ê : Fin r → J}
    (he3' : ∀ i, (ê i) ^ 3 = 1) (hcommê : ∀ i j, i ≠ j → Commute (ê i) (ê j)) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure (Set.range ê)) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    by_cases hij : i = j
    · subst hij; rfl
    · exact hcommê i j hij
  · rintro a ⟨i, rfl⟩
    exact he3' i

theorem Rank3Witness.of_surjective {J M : Type*} [Group J] [Group M] [Finite J] (π : J →* M)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center J) {r : ℕ} (e : Fin r → M)
    (he3 : ∀ i, e i ^ 3 = 1) (hcomm : ∀ i j, Commute (e i) (e j))
    (hcard : Nat.card (Subgroup.closure (Set.range e)) = 3 ^ r)
    (hZ : Subgroup.closure (Set.range e) ⊓ Subgroup.center M = ⊥) {t : M}
    (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (htZ : t ∉ Subgroup.center M) (ht : ∀ i, Commute t (e i))
    (hinv : ∀ i, ∃ s : M, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s * e i * s⁻¹ = (e i)⁻¹)
    (hpair : ∀ i j, i ≠ j → ∃ s : M, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
      ((s * e i * s⁻¹ = e i ∧ s * e j * s⁻¹ = (e j)⁻¹) ∨
        (s * e i * s⁻¹ = (e i)⁻¹ ∧ s * e j * s⁻¹ = e j))) :
    Rank3Witness J r := by
  classical
  choose s hs using hinv
  choose ŝ hπŝ using fun i => hπ (s i)
  choose f hπf using fun i => hπ (e i)
  let ê : Fin r → J := fun i => ŝ i * f i * (ŝ i)⁻¹ * (f i)⁻¹
  have hcube := rankLift_cube hker he3 hπŝ (fun i => (hs i).2) hπf
  have he3' : ∀ i, (ê i) ^ 3 = 1 := fun i => by simpa [ê, rankLiftElem] using hcube.1 i
  have hπê : ∀ i, π (ê i) = e i := fun i => by simpa [ê, rankLiftElem] using hcube.2 i
  have hcommê : ∀ i j, i ≠ j → Commute (ê i) (ê j) :=
    rankLift_pair_comm hπ hker hcomm he3' hπê hpair
  have hord_e := rankLift_orderOf e he3 hcomm hcard
  have hord_ê : ∀ i, orderOf (ê i) = 3 := rankLift_orderOf_lift hπê he3' hord_e
  have hÊelem : CFSG.Open.IsElemAbelian 3 (Subgroup.closure (Set.range ê)) :=
    rankLift_isElemAbelian he3' hcommê
  obtain ⟨F, hFrange, hFMrange, hFMinj⟩ :=
    rankLift_F_exists (e := e) (ê := ê) hcommê hπê hcard hord_ê
  obtain ⟨hFinj, hcardÊ⟩ := rankLift_F_inj_card (ê := ê) hFrange hFMinj
      (rankLift_card_domain hord_ê)
  have hÊbot := rankLift_center_bot hπ hFrange hFMrange hFMinj hZ
  obtain ⟨tJ, hπt, htJ2, htJ_comm, htJZ⟩ := rankLift_t hπ hker he3' hπê ht2 htZ ht
  have hÊle := rankLift_centralizer htJ_comm
  exact ⟨Subgroup.closure (Set.range ê), tJ, hÊelem, hcardÊ, hÊbot, htJ2, htJZ, hÊle⟩

end CFSG.StandardType.FrameRoute

end
