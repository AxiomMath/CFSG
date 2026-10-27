module

public import CFSG.RankThree.PartOne.S12.Sec159FiveHom
public import CFSG.RankThree.PartOne.S12.Sec159Fin
public import CFSG.RankThree.PartOne.S12.Sec159Tr
import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree StrongP
open Sec159Cfg

namespace Sec159Five

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E A P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {x : M}

theorem Cfg5.centralizer_eq_bot (h : Cfg5 p X E A P N θ x) :
    Subgroup.centralizer
      (((X.map (QuotientGroup.mk' (actQ X θ).ker) : Subgroup (M ⧸ (actQ X θ).ker))) :
        Set (M ⧸ (actQ X θ).ker)) = ⊥ := by
  have : Group.IsPerfect (↥X ⧸ θ) := h.quasi.1
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (actQ X θ).ker y
  rw [Subgroup.mem_bot]
  have hcentral : ∀ z ∈ X, g * z * g⁻¹ * z⁻¹ ∈ (actQ X θ).ker := by
    intro z hz
    have h1 := Subgroup.mem_centralizer_iff.1 hy (QuotientGroup.mk' (actQ X θ).ker z) ⟨z, hz, rfl⟩
    have h2 : (QuotientGroup.mk' (actQ X θ).ker) (g * z) =
        (QuotientGroup.mk' (actQ X θ).ker) (z * g) := by
      rw [map_mul, map_mul]; exact h1.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at h2
    have : g * z / (z * g) = g * z * g⁻¹ * z⁻¹ := by simp [div_eq_mul_inv, mul_assoc]
    rwa [this] at h2
  have hg : actQ X θ g = 1 := by
    apply aut_eq_one_of_central
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      have hu : ((MulAut.conjNormal g y * y⁻¹ : ↥X) : M) ∈ (actQ X θ).ker := by
        simpa [MulAut.conjNormal_apply] using hcentral y y.2
      exact mk_mem_center_of_mem_ker (MulAut.conjNormal g y * y⁻¹ : ↥X).2 hu
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hg

theorem Cfg5.exists_mem_inf_normalizer (h : Cfg5 p X E A P N θ x) {y : M} (hy : y ∈ X)
    (hyn : QuotientGroup.mk' (actQ X θ).ker y ∈
      Subgroup.normalizer ((E.map (QuotientGroup.mk' (actQ X θ).ker) : Subgroup _) : Set _)) :
    ∃ n ∈ X ⊓ Subgroup.normalizer (E : Set M),
      QuotientGroup.mk' (actQ X θ).ker n = QuotientGroup.mk' (actQ X θ).ker y := by
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  set π := QuotientGroup.mk' K with hπ
  have hconj : ∀ r ∈ E, y * r * y⁻¹ ∈ K ⊔ E := by
    intro r hr
    have h1 : π (y * r * y⁻¹) ∈ E.map π := by
      have h3 := (Subgroup.mem_normalizer_iff.1 hyn (π r)).1 ⟨r, hr, rfl⟩
      rw [map_mul, map_mul, map_inv]
      exact h3
    have h2 : y * r * y⁻¹ ∈ (E.map π).comap π := h1
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
    rwa [sup_comm]
  obtain ⟨k, hk, hkn⟩ := h.exists_ker_mul_mem_normalizer le_rfl inf_le_right hconj
  have hksup := h.ker_le_sup hk
  have hZn : (K ⊓ X).Normal := inferInstance
  obtain ⟨z, hz, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hksup
  have hwE : w ∈ E := hw.2
  refine ⟨z⁻¹ * y, ⟨X.mul_mem (X.inv_mem hz.2) hy, ?_⟩, ?_⟩
  · have h1 : w * ((z * w)⁻¹ * y) ∈ Subgroup.normalizer (E : Set M) :=
      (Subgroup.normalizer (E : Set M)).mul_mem (Subgroup.le_normalizer hwE) hkn
    have h2 : w * ((z * w)⁻¹ * y) = z⁻¹ * y := by group
    rwa [h2] at h1
  · have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz.1
    rw [map_mul, map_inv, hπz]; simp

theorem Cfg5.automizer (h : Cfg5 p X E A P N θ x) {A₀ : Type} [Group A₀]
    (f : ↥(X ⊓ Subgroup.normalizer (E : Set M)) →* A₀) (hA : Nat.card A₀ ∣ 120)
    (hA' : ∀ a : A₀, orderOf a ≤ 6)
    (hker : ∀ n : ↥(X ⊓ Subgroup.normalizer (E : Set M)), f n = 1 → ∀ e ∈ E, (n : M) * e = e * n) :
    Nat.card ↥(torusImage (E.map (QuotientGroup.mk' (actQ X θ).ker))
      (X.map (QuotientGroup.mk' (actQ X θ).ker))) ∣ 120 ∧
    ∀ g ∈ torusImage (E.map (QuotientGroup.mk' (actQ X θ).ker))
      (X.map (QuotientGroup.mk' (actQ X θ).ker)), orderOf g ≤ 6 := by
  have hFin : Finite A₀ := Nat.finite_of_card_ne_zero (by
    intro h0; rw [h0] at hA; norm_num at hA)
  set K := (actQ X θ).ker with hK
  have hrange : torusImage (E.map (QuotientGroup.mk' K)) (X.map (QuotientGroup.mk' K)) =
      (autHom X E θ).range := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hφ
      obtain ⟨y, hy, hys⟩ := Subgroup.mem_subgroupOf.1 hs
      have hyn : QuotientGroup.mk' K y ∈ Subgroup.normalizer
          ((E.map (QuotientGroup.mk' K) : Subgroup _) : Set _) := hys ▸ s.2
      obtain ⟨n, hn, hπn⟩ := h.exists_mem_inf_normalizer hy hyn
      refine ⟨⟨n, hn⟩, ?_⟩
      show (E.map (QuotientGroup.mk' K)).normalizerMonoidHom _ = _
      congr 1
      exact Subtype.ext (hπn.trans hys)
    · rintro ⟨n, rfl⟩
      refine Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 ⟨n, n.2.1, rfl⟩, rfl⟩
  have hkerle : f.ker ≤ (autHom X E θ).ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    have hc := hker n hn
    ext ⟨y, e, he, rfl⟩
    rw [autHom_apply_coe]
    have : (n : M) * e * (n : M)⁻¹ = e := by rw [hc e he]; group
    simp only [MulAut.one_apply]
    rw [← map_mul, ← map_inv, ← map_mul, this]
  rw [hrange]
  refine ⟨(card_range_dvd_of_ker_le f (autHom X E θ) hkerle).trans
    ((Subgroup.card_subgroup_dvd_card f.range).trans hA), ?_⟩
  rintro _ ⟨n, rfl⟩
  have h1 := orderOf_dvd_of_ker_le f (autHom X E θ) hkerle n
  exact (Nat.le_of_dvd (orderOf_pos _) h1).trans (hA' _)

theorem Cfg5.false_of_sz
    (h : Cfg5 p X E A P N θ x) (hU : Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ^ 2)
    (hEK : ∀ e ∈ E, e ∈ X ⊔ (actQ X θ).ker)
    (hiso : Census3.IsoLie ↥(X.map (QuotientGroup.mk' (actQ X θ).ker)) (.suzuki 2)) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  set π := QuotientGroup.mk' K with hπ
  have hπE : E.map π ≤ X.map π := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 (hEK e he)
    refine ⟨a, ha, ?_⟩
    have hπb : π b = 1 := (QuotientGroup.eq_one_iff b).2 hb
    rw [← hab, map_mul, hπb, mul_one]
  have hSz : K159.SzAbs.SzSylow ↥(X.map π) := K159.SzAbs.szSylow_of_isoLie hiso
  have hEel : IsElementaryAbelian p ↥(E.map π) := Equivariance.isElementaryAbelian_map h.Eel _
  have hE2 : Nat.card ↥(E.map π) = p ^ 2 := by
    have h1 := h.card_map_E
    rw [hU] at h1
    have : Nat.card ↥(E.map π) * p ^ 2 = p ^ 2 * p ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) this
  set Ê : Subgroup ↥(X.map π) := (E.map π).subgroupOf (X.map π) with hÊ
  have hÊel : IsElementaryAbelian p ↥Ê := Sec159Tr.isElementaryAbelian_subgroupOf hEel
  have hÊcard : Nat.card ↥Ê = p ^ 2 := (Sec159Tr.card_subgroupOf hπE).trans hE2
  have hdvd : p ^ 2 ∣ 32537600 := by
    rw [← hSz.card, ← hÊcard]
    exact Subgroup.card_subgroup_dvd_card Ê
  have hp5 : p = 5 := by
    have hpd : p ∣ 32537600 := (dvd_pow_self p two_ne_zero).trans hdvd
    have hN : (32537600 : ℕ) = 2 ^ 10 * 5 ^ 2 * 31 * 41 := by norm_num
    rw [hN] at hpd hdvd
    rcases (Nat.Prime.dvd_mul h.prime).1 hpd with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.prime).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul h.prime).1 h2 with h3 | h3
        · have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 (h.prime.dvd_of_dvd_pow h3)
          have := h.p5
          omega
        · exact (Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 (h.prime.dvd_of_dvd_pow h3)
      · have h31 : p = 31 := (Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 h2
        subst h31
        norm_num at hdvd
    · have h41 : p = 41 := (Nat.prime_dvd_prime_iff_eq h.prime (by norm_num)).1 h1
      subst h41
      norm_num at hdvd
  subst hp5
  have hidx : Ê.index * Nat.card ↥Ê = Nat.card ↥(X.map π) := Ê.index_mul_card
  rw [hSz.card, hÊcard] at hidx
  have hidx' : Ê.index = 1301504 := by omega
  have hP2 : ¬ 5 ∣ Ê.index := by rw [hidx']; norm_num
  have hÊp : IsPGroup 5 ↥Ê := hÊel.isPGroup 5 ↥Ê
  have hcyc : IsCyclic ↥(hÊp.toSylow hP2 : Subgroup ↥(X.map π)) := hSz.cyclic _
  have hcyc' : IsCyclic ↥Ê := hcyc
  have : IsElementaryAbelian 5 ↥Ê := hÊel
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hÊcard hcyc'

end Sec159Five

end CFSG.RankThree.PartOne
