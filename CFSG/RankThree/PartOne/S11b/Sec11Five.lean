module

public import CFSG.RankThree.PartOne.S11b.Sec11Indeed
import CFSG.RankThree.PartOne.S11b.Sec109Witness
import CFSG.RankThree.PartOne.S10.SectionTenFiveNormalPCoreWitness
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec11Indeed

section Counting

variable {p : ℕ} [Fact p.Prime] {X : Type*} [CommGroup X] [Finite X]

theorem exists_ne_one_mem_sup_inf (hcard : Nat.card X = p ^ 3) (hexp : ∀ x : X, x ^ p = 1)
    (u v w : X) (hgen : zpowers u ⊔ zpowers v ⊔ zpowers w = ⊤) (H : Subgroup X)
    (hH : H.index = p) : ∃ x ∈ zpowers u ⊔ zpowers v, x ∈ H ∧ x ≠ 1 := by
  classical
  set P : Subgroup X := zpowers u ⊔ zpowers v with hP
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hPidx : P.index ≤ p := by
    rw [Subgroup.index]
    have hsurj : Function.Surjective
        (fun i : Fin p => (QuotientGroup.mk w : X ⧸ P) ^ (i : ℕ)) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : x ∈ P ⊔ zpowers w := by
        rw [hgen]
        exact mem_top x
      obtain ⟨s, hs, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
      have hwp : (QuotientGroup.mk w : X ⧸ P) ^ p = 1 := by
        rw [← QuotientGroup.mk_pow, hexp w]
        rfl
      have hwpz : (QuotientGroup.mk w : X ⧸ P) ^ (p : ℤ) = 1 := by
        rw [zpow_natCast]
        exact hwp
      refine ⟨⟨(k % (p : ℤ)).toNat, ?_⟩, ?_⟩
      · have h1 := Int.emod_nonneg k (by omega : (p : ℤ) ≠ 0)
        have h2 := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < p)
        omega
      · have h1 := Int.emod_nonneg k (by omega : (p : ℤ) ≠ 0)
        simp only
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff s).mpr hs, one_mul, ← zpow_natCast,
          Int.toNat_of_nonneg h1, ← zpow_eq_zpow_emod k hwpz, QuotientGroup.mk_zpow]
    calc Nat.card (X ⧸ P) ≤ Nat.card (Fin p) := Nat.card_le_card_of_surjective _ hsurj
      _ = p := by simp
  have hinf : (P ⊓ H).index ≤ p * p := by
    have h : (P ⊓ H).index ≤ P.index * H.index := Subgroup.index_inf_le
    rw [hH] at h
    exact h.trans (Nat.mul_le_mul_right p hPidx)
  have hcardinf : 1 < Nat.card ↥(P ⊓ H) := by
    have h := (P ⊓ H).card_mul_index
    rw [hcard] at h
    by_contra hle
    push Not at hle
    have h2 : Nat.card ↥(P ⊓ H) * (P ⊓ H).index ≤ 1 * (p * p) := Nat.mul_le_mul hle hinf
    have : p * p < p ^ 3 := by nlinarith
    omega
  have : Nontrivial ↥(P ⊓ H) := Finite.one_lt_card_iff_nontrivial.mp hcardinf
  obtain ⟨⟨x, hxP, hxH⟩, hx1⟩ := exists_ne (1 : ↥(P ⊓ H))
  exact ⟨x, hxP, hxH, fun h => hx1 (Subtype.ext h)⟩

end Counting

variable {G : Type} [Group G] [Finite G]

theorem exists_nat_mul_add_dvd {p : ℕ} [Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (j : ℤ) :
    ∃ m : ℕ, (p : ℤ) ∣ u * m + j := by
  have hu' : (u : ZMod p) ≠ 0 := fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
  refine ⟨(-(j : ZMod p) / (u : ZMod p)).val, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

omit [Finite G] in
theorem pow_conj_eq {y a d : G} {k : ℤ} (hd : y * d * y⁻¹ = d)
    (ha : y * a * y⁻¹ = a * d ^ k) (m : ℕ) :
    y ^ m * a * (y ^ m)⁻¹ = a * d ^ ((m : ℤ) * k) ∧ y ^ m * d * (y ^ m)⁻¹ = d := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · have e : y ^ (m + 1) * a * (y ^ (m + 1))⁻¹ = y * (y ^ m * a * (y ^ m)⁻¹) * y⁻¹ := by
        rw [pow_succ']
        group
      rw [e, ih1]
      calc y * (a * d ^ ((m : ℤ) * k)) * y⁻¹
          = (y * a * y⁻¹) * (y * d ^ ((m : ℤ) * k) * y⁻¹) := by group
        _ = a * d ^ k * (y * d * y⁻¹) ^ ((m : ℤ) * k) := by rw [ha, conj_zpow]
        _ = a * d ^ (((m + 1 : ℕ) : ℤ) * k) := by
          rw [hd, mul_assoc, ← zpow_add]
          congr 2
          push_cast
          ring
    · have e : y ^ (m + 1) * d * (y ^ (m + 1))⁻¹ = y * (y ^ m * d * (y ^ m)⁻¹) * y⁻¹ := by
        rw [pow_succ']
        group
      rw [e, ih2, hd]

theorem exists_hyperplane_witness {p : ℕ} {A : Subgroup G}
    (hS : SteinbergBM.SectionTenSetup G p A) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) :
    ∃ H : Subgroup A, H.index = p ∧ ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      A ≤ normalizer (S : Set G) ∧ S = ⁅S, zpowers c⁆ ∧
      ∀ h : A, h ∈ H → S ≤ centralizer ({(h : G)} : Set G) := by
  classical
  have hp : p.Prime := sectionTenSetup_prime hS
  have hp3 := sectionTenSetup_three_lt hS
  have hAe : IsElementaryAbelian p A := hS.2.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, Q, hQ2, hAQ, -, -, hQne, -⟩ :=
    section_ten_five_normal_p_core_two_group_witness_frontier G p A hS c hcA hc1
  have hQp : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨H, hHidx, q, hqQ, hqH, hqc⟩ := Sec109.exists_hyperplane_not_commute hAQ hQp hcA hQne
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  let H' : Subgroup G := H.map A.subtype
  let Q1 : Subgroup G := Q ⊓ centralizer (H' : Set G)
  have hQ1Q : Q1 ≤ Q := inf_le_left
  have hcentH' : ∀ x ∈ H', ∀ s ∈ Q1, x * s = s * x := fun x hx s hs =>
    mem_centralizer_iff.mp hs.2 x hx
  have hfwd : ∀ a ∈ A, ∀ x ∈ Q1, a * x * a⁻¹ ∈ Q1 := by
    intro a ha x hx
    refine ⟨(mem_normalizer_iff.mp (hAQ ha) x).mp hx.1, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    have hya : Commute (y' : G) a := hAcomm y' y'.2 a ha
    have hyx : Commute (y' : G) x := hcentH' y' (mem_map.mpr ⟨y', hy', rfl⟩) x hx
    exact ((hya.mul_right hyx).mul_right hya.inv_right).eq
  have hAQ1 : A ≤ normalizer (Q1 : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hfwd a ha x, fun hx => ?_⟩
    have h1 := hfwd a⁻¹ (A.inv_mem ha) _ hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hAz : A ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
    have hfix : ∀ g ∈ A, ∀ h ∈ zpowers c, g * h * g⁻¹ = h := by
      intro g hg h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      have hcg : Commute (c ^ k) g := Commute.zpow_left (hAcomm c hcA g hg) k
      calc g * c ^ k * g⁻¹ = c ^ k * g * g⁻¹ := by rw [← hcg.eq]
        _ = c ^ k := by group
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hfix a ha h hh]; exact hh, fun hh => ?_⟩
    have h1 := hfix a⁻¹ (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rw [e] at h1
    rw [h1]
    exact hh
  have hzQ1 : zpowers c ≤ normalizer (Q1 : Set G) := zpowers_le.mpr (hAQ1 hcA)
  have hSle : ⁅Q1, zpowers c⁆ ≤ Q1 := Subgroup.le_normalizer_iff_commutator_le_left.mp hzQ1
  have hqQ1 : q ∈ Q1 := ⟨hqQ, mem_centralizer_iff.mpr fun x hx => by
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hx
    exact hqH y' hy'⟩
  refine ⟨H, hHidx, ⁅Q1, zpowers c⁆, ?_, hQ2.to_le (hSle.trans hQ1Q),
    Sec109.le_normalizer_commutator_of_le_normalizers hAQ1 hAz, ?_, ?_⟩
  · intro hbot
    have h1 : ⁅q, c⁆ ∈ ⁅Q1, zpowers c⁆ := commutator_mem_commutator hqQ1 (mem_zpowers c)
    rw [hbot, mem_bot, commutatorElement_def] at h1
    apply hqc
    calc c * q = (q * c * q⁻¹ * c⁻¹)⁻¹ * (q * c) := by group
      _ = q * c := by rw [h1]; simp
  · have hpow : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian c hcA
    have : IsElementaryAbelian p (zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hpow
    have hpg : IsPGroup p (zpowers c) := IsElementaryAbelian.isPGroup p _
    have hcompl : ¬ p ∣ Nat.card Q1 := fun h => hQp (h.trans (Subgroup.card_dvd_of_le hQ1Q))
    exact (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp
      (zpowers c) Q1 hpg hcompl hzQ1).symm
  · intro h hh s hs
    have hh' : (h : G) ∈ H' := mem_map.mpr ⟨h, hh, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact (hcentH' (h : G) hh' s (hSle hs)).symm

omit [Finite G] in
theorem mem_map_conj_iff {S : Subgroup G} (z x : G) :
    x ∈ S.map (MulAut.conj z).toMonoidHom ↔ z⁻¹ * x * z ∈ S := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : z⁻¹ * ((MulAut.conj z).toMonoidHom s) * z = s := by
      change z⁻¹ * (z * s * z⁻¹) * z = s
      group
    rw [this]
    exact hs
  · intro hx
    refine ⟨z⁻¹ * x * z, hx, ?_⟩
    change z * (z⁻¹ * x * z) * z⁻¹ = x
    group

theorem witnessAt_of_conj_elem {p : ℕ} [Fact p.Prime] {A : Subgroup G} {c a x z : G}
    (hap : a ^ p = 1) {i : ℤ} (hi : ¬ (p : ℤ) ∣ i)
    (hzA : ∀ e ∈ A, z⁻¹ * e * z ∈ A) (hzc : z * c = c * z) (hzx : z * x * z⁻¹ = a ^ i)
    {S : Subgroup G} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hSA : A ≤ normalizer (S : Set G))
    (hSc : S = ⁅S, zpowers c⁆) (hSx : S ≤ centralizer ({x} : Set G)) :
    ∃ R : Subgroup G, WitnessAt A c a R := by
  classical
  have hzpow : ∀ n : ℤ, (p : ℤ) ∣ n → a ^ n = 1 := fun n hn => by
    obtain ⟨t, rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, hap, one_zpow]
  obtain ⟨m', hm'⟩ := exists_nat_mul_add_dvd hi (-1)
  have hai : (a ^ i) ^ (m' : ℤ) = a := by
    rw [← zpow_mul]
    have h1 : a ^ (i * (m' : ℤ) + -1) = 1 := hzpow _ hm'
    calc a ^ (i * (m' : ℤ)) = a ^ (i * (m' : ℤ) + -1) * a := by
          rw [zpow_add, zpow_neg_one]
          group
      _ = a := by rw [h1, one_mul]
  have hinj : Function.Injective (MulAut.conj z).toMonoidHom := (MulAut.conj z).injective
  refine ⟨S.map (MulAut.conj z).toMonoidHom, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s' hs'
    rw [mem_centralizer_singleton_iff]
    obtain ⟨s, hs, rfl⟩ := mem_map.mp hs'
    have h1 : s * x = x * s := mem_centralizer_singleton_iff.mp (hSx hs)
    have hcomm' : Commute (z * s * z⁻¹) (a ^ i) := by
      rw [← hzx]
      change (z * s * z⁻¹) * (z * x * z⁻¹) = (z * x * z⁻¹) * (z * s * z⁻¹)
      calc (z * s * z⁻¹) * (z * x * z⁻¹) = z * (s * x) * z⁻¹ := by group
        _ = z * (x * s) * z⁻¹ := by rw [h1]
        _ = (z * x * z⁻¹) * (z * s * z⁻¹) := by group
    have hc2 : Commute (z * s * z⁻¹) a := by
      have := hcomm'.zpow_right (m' : ℤ)
      rwa [hai] at this
    exact hc2.eq
  · intro h
    exact hS1 (Subgroup.map_injective hinj (h.trans (Subgroup.map_bot _).symm))
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    exact IsPGroup.iff_card.mpr ⟨n, by rw [Subgroup.card_map_of_injective hinj, hn]⟩
  · intro e he
    rw [mem_normalizer_iff]
    intro x'
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have e1 : z⁻¹ * (e * x' * e⁻¹) * z =
        (z⁻¹ * e * z) * (z⁻¹ * x' * z) * (z⁻¹ * e * z)⁻¹ := by group
    rw [e1]
    exact mem_normalizer_iff.mp (hSA (hzA e he)) (z⁻¹ * x' * z)
  · have hcz : (zpowers c).map (MulAut.conj z).toMonoidHom = zpowers c := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change z * c * z⁻¹ = c
      rw [hzc]
      group
    calc S.map (MulAut.conj z).toMonoidHom = (⁅S, zpowers c⁆).map (MulAut.conj z).toMonoidHom := by
          rw [← hSc]
      _ = ⁅S.map (MulAut.conj z).toMonoidHom, (zpowers c).map (MulAut.conj z).toMonoidHom⁆ :=
          Subgroup.map_commutator _ _ _
      _ = ⁅S.map (MulAut.conj z).toMonoidHom, zpowers c⁆ := by rw [hcz]

theorem exists_conj_elem {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hAe : IsElementaryAbelian p A)
    {c a d y : G} {L : Subgroup G} (haA : a ∈ A) (hdA : d ∈ A)
    (hy : Transvection p A L d y a) (hyc : y * c = c * y) {i j : ℤ} (hi : ¬ (p : ℤ) ∣ i) :
    ∃ z : G, (∀ e ∈ A, z⁻¹ * e * z ∈ A) ∧ z * c = c * z ∧
      z * (a ^ i * d ^ j) * z⁻¹ = a ^ i := by
  classical
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcomm : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨x', hx'⟩)
  have hdp : d ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) d hdA
  have hzpow : ∀ n : ℤ, (p : ℤ) ∣ n → d ^ n = 1 := fun n hn => by
    obtain ⟨t, rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, hdp, one_zpow]
  have hda : Commute d a := hcomm d hdA a haA
  obtain ⟨k₀, hk₀⟩ := mem_zpowers_iff.mp (hy.comm_mem a haA)
  have hya : y * a * y⁻¹ = a * d ^ k₀ := by
    have h1 : y * a * y⁻¹ = d ^ k₀ * a := by
      rw [hk₀]
      group
    rw [h1, (Commute.zpow_left hda k₀).eq]
  have hk0 : ¬ (p : ℤ) ∣ k₀ := fun h =>
    hy.moves (by rw [hya, hzpow k₀ h, mul_one])
  obtain ⟨m, hm⟩ := exists_nat_mul_add_dvd (u := i * k₀) (fun h => by
    rcases hpZ.dvd_mul.mp h with h | h
    · exact hi h
    · exact hk0 h) j
  obtain ⟨hza, hzd⟩ := pow_conj_eq hy.cent_d hya m
  have hzc : y ^ m * c = c * y ^ m := (Commute.pow_left (show Commute y c from hyc) m).eq
  have hyA : ∀ e ∈ A, y * e * y⁻¹ ∈ A := by
    intro e he
    have h1 : y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
    rw [h1]
    exact A.mul_mem ((zpowers_le.mpr hdA) (hy.comm_mem e he)) he
  have hyN : y ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact hyA e he
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hzN : y ^ m ∈ normalizer (A : Set G) := (normalizer (A : Set G)).pow_mem hyN m
  have hzA : ∀ e ∈ A, (y ^ m)⁻¹ * e * y ^ m ∈ A := by
    intro e he
    have h1 := (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hzN) e).mp he
    simpa using h1
  refine ⟨y ^ m, hzA, hzc, ?_⟩
  have h1 : y ^ m * (a ^ i * d ^ j) * (y ^ m)⁻¹ =
      (y ^ m * a * (y ^ m)⁻¹) ^ i * (y ^ m * d * (y ^ m)⁻¹) ^ j := by
    rw [conj_zpow, conj_zpow]
    group
  rw [h1, hza, hzd, (hda.symm.zpow_right ((m : ℤ) * k₀)).mul_zpow, ← zpow_mul, mul_assoc,
    ← zpow_add, hzpow ((m : ℤ) * k₀ * i + j) (by convert hm using 1; ring), mul_one]

omit [Finite G] in
theorem sup_eq_top_of_sup_eq {A : Subgroup G} {u v w : G} (hu : u ∈ A) (hv : v ∈ A) (hw : w ∈ A)
    (h : zpowers u ⊔ zpowers v ⊔ zpowers w = A) :
    zpowers (⟨u, hu⟩ : A) ⊔ zpowers (⟨v, hv⟩ : A) ⊔ zpowers (⟨w, hw⟩ : A) = ⊤ := by
  apply Subgroup.map_injective A.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype]
  exact h

theorem exists_witnessAt_a {p : ℕ} {A : Subgroup G} {c a d y : G} {L : Subgroup G}
    (sit : Sit p A c L a d) (hy : Transvection p A L d y a) (hyc : y * c = c * y)
    (hcore : ∀ f ∈ zpowers a ⊔ zpowers c, f ≠ 1 → ∀ R : Subgroup G, WitnessAt A c d R →
      R ≤ centralizer ({f} : Set G) → False) :
    ∃ R : Subgroup G, WitnessAt A c a R := by
  classical
  have hS := sit.setup
  have hp : p.Prime := sectionTenSetup_prime hS
  have : Fact p.Prime := ⟨hp⟩
  have hAe : IsElementaryAbelian p A := hS.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := hS.2.2.2.2.2.2.2.1
  obtain ⟨H, hHidx, S, hS1, hS2, hSA, hSc, hSH⟩ :=
    exists_hyperplane_witness hS sit.c_mem sit.c_ne_one
  have hexp : ∀ x : A, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A)
  have hap : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) a sit.a_mem
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hgen1 := sup_eq_top_of_sup_eq sit.a_mem sit.d_mem sit.c_mem
    (by rw [sup_right_comm]; exact sit.A_eq.symm)
  obtain ⟨x, hxP, hxH, hx1⟩ := exists_ne_one_mem_sup_inf hAcard hexp _ _ _ hgen1 H hHidx
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hxP
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  by_cases hi : (p : ℤ) ∣ i
  ·
    have hai : (⟨a, sit.a_mem⟩ : A) ^ i = 1 := by
      obtain ⟨t, rfl⟩ := hi
      rw [zpow_mul, zpow_natCast, hexp, one_zpow]
    have hdp' : (⟨d, sit.d_mem⟩ : A) ^ p = 1 := hexp _
    have hj : ¬ (p : ℤ) ∣ j := by
      rintro ⟨t, rfl⟩
      apply hx1
      rw [hai, one_mul, zpow_mul, zpow_natCast, hdp', one_zpow]
    obtain ⟨m', hm'⟩ := exists_nat_mul_add_dvd hj (-1)
    have hdH : (⟨d, sit.d_mem⟩ : A) ∈ H := by
      have h1 : (⟨d, sit.d_mem⟩ : A) ^ (j * (m' : ℤ) + -1) = 1 := by
        obtain ⟨t, ht⟩ := hm'
        rw [ht, zpow_mul, zpow_natCast, hdp', one_zpow]
      have h2 : ((⟨d, sit.d_mem⟩ : A) ^ j) ^ (m' : ℤ) = ⟨d, sit.d_mem⟩ := by
        rw [← zpow_mul, mul_comm j, ← mul_comm j]
        calc (⟨d, sit.d_mem⟩ : A) ^ (j * (m' : ℤ)) =
            (⟨d, sit.d_mem⟩ : A) ^ (j * (m' : ℤ) + -1) * ⟨d, sit.d_mem⟩ := by
              rw [zpow_add, zpow_neg_one]
              group
          _ = ⟨d, sit.d_mem⟩ := by rw [h1, one_mul]
      rw [← h2]
      refine zpow_mem ?_ _
      rw [hai, one_mul] at hxH
      exact hxH
    have hgen2 := sup_eq_top_of_sup_eq sit.a_mem sit.c_mem sit.d_mem sit.A_eq.symm
    obtain ⟨x', hx'P, hx'H, hx'1⟩ := exists_ne_one_mem_sup_inf hAcard hexp _ _ _ hgen2 H hHidx
    obtain ⟨u', hu', v', hv', rfl⟩ := Subgroup.mem_sup.mp hx'P
    obtain ⟨i', rfl⟩ := mem_zpowers_iff.mp hu'
    obtain ⟨j', rfl⟩ := mem_zpowers_iff.mp hv'
    have hf : a ^ i' * c ^ j' ∈ zpowers a ⊔ zpowers c :=
      Subgroup.mul_mem_sup (zpow_mem (mem_zpowers a) _) (zpow_mem (mem_zpowers c) _)
    have hf1 : a ^ i' * c ^ j' ≠ 1 := fun h =>
      hx'1 (Subtype.ext (by simpa using h))
    have hSd : S ≤ centralizer ({d} : Set G) := hSH _ hdH
    have hSf : S ≤ centralizer ({a ^ i' * c ^ j'} : Set G) := by
      have := hSH _ hx'H
      simpa using this
    exact (hcore _ hf hf1 S ⟨hSd, hS1, hS2, hSA, hSc⟩ hSf).elim
  · have hSx : S ≤ centralizer ({a ^ i * d ^ j} : Set G) := by
      have := hSH _ hxH
      simpa using this
    obtain ⟨z, hzA, hzc, hzx⟩ := exists_conj_elem hAe sit.a_mem sit.d_mem hy hyc (j := j) hi
    exact witnessAt_of_conj_elem hap hi hzA hzc hzx hS1 hS2 hSA hSc hSx

@[expose] def FiveClaimCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → CFSG.pRank p ↥L = 1 → ∀ f ∈ zpowers a ⊔ zpowers c, f ≠ 1 →
      ∀ R : Subgroup G, WitnessAt A c d R → R ≤ centralizer ({f} : Set G) → False

theorem fiveClaim_of_core (hS : SchreierFor InCatalog) (hKF : KF128Rank1) (hcore : FiveClaimCore) :
    FiveClaim := by
  intro G _ _ p A c L a d sit h3
  have h := sit.setup
  have hp := sectionTenSetup_prime h
  have hp3 := sectionTenSetup_three_lt h
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  obtain ⟨hqL, hAL, -⟩ := moving_maximal_data_at hS h sit.L_mem.1.1 sit.c_mem sit.c_ne_one
    sit.L_mem.2
  have hevL : evenRank ↥L ≤ 3 :=
    (Sec9A.evenRank_subgroup_le L).trans (sectionTenSetup_evenRank_eq h).le
  have hdLmem : d ∈ L := (Subgroup.mem_inf.mp (sit.d_gen ▸ Subgroup.mem_zpowers d)).2
  obtain ⟨-, S, hSL, hS1, hS2, hAS, -⟩ := sit.L_mem.1.1.1
  obtain ⟨y, hyL, hyp, hyd, hya, hye⟩ := hKF G p L A a d hp hp5 hqL sit.even hevL h3.le sit.p_ndvd
    hAe hAL sit.a_mem sit.d_mem hdLmem sit.d_ne_one sit.a_field
    ⟨S, hSL, hS1, hS2, hAS sit.a_mem, hAS sit.d_mem⟩
  have hyc : y * c = c * y :=
    mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp sit.L_mem.2).1 hyL)
  exact exists_witnessAt_a sit ⟨hyL, hyp, hyd, hya, hye⟩ hyc (hcore G p A c L a d sit h3)

end Sec11Indeed

open Sec11Indeed in
theorem sec11OneIndeed_of_core_steps (hS : SchreierFor InCatalog) (h107 : InSec10Seven)
    (h112 : InSec11Two) (hKF : KF128Rank1) (h113 : ThreeClaim) (h114 : FourClaim)
    (hcore : FiveClaimCore) (hfin : FinalClaim) : Sec11OneIndeed :=
  sec11OneIndeed_of_steps hS h107 h112 hKF h113 h114 (fiveClaim_of_core hS hKF hcore) hfin

end CFSG.RankThree.PartOne
