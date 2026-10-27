module

public import CFSG.RankThree.PartOne.TAIL.Sylow1

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

@[expose] def Qsub (K P : Subgroup G) : Subgroup G :=
  P ⊓ (K ⊔ Subgroup.centralizer (K : Set G))

theorem Qsub_le (K P : Subgroup G) : Qsub K P ≤ P := inf_le_left

theorem mem_KC_iff {K : Subgroup G} {x : G} :
    x ∈ K ⊔ Subgroup.centralizer (K : Set G) ↔
      ∃ k ∈ K, ∃ z ∈ Subgroup.centralizer (K : Set G), x = k * z := by
  have hK : K ≤ Subgroup.normalizer ((Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
    intro k hk
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz k hk).symm
  constructor
  · intro hx
    have : x ∈ ((K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hK] at this
    obtain ⟨k, hk, z, hz, rfl⟩ := Set.mem_mul.mp this
    exact ⟨k, hk, z, hz, rfl⟩
  · rintro ⟨k, hk, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hk hz

theorem conj_mem_KC {K : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) {x : G}
    (hx : x ∈ K ⊔ Subgroup.centralizer (K : Set G)) :
    n * x * n⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
  obtain ⟨k, hk, z, hz, rfl⟩ := mem_KC_iff.mp hx
  refine mem_KC_iff.mpr ⟨n * k * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn k).mp hk, n * z * n⁻¹, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k' hk'
  have hk'' : n⁻¹ * k' * n ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) k').mp hk'
    simpa using this
  have hz' := Subgroup.mem_centralizer_iff.mp hz _ hk''
  calc k' * (n * z * n⁻¹) = n * ((n⁻¹ * k' * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * k' * n)) * n⁻¹ := by rw [hz']
    _ = (n * z * n⁻¹) * k' := by group

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀) {P : Subgroup G} (hP : PData A B y₀ P)

include h in
theorem c_notMem_Q : c ∉ Qsub K P := fun hc => h.c_out (Subgroup.mem_inf.mp hc).2

include h hP

theorem c_mem_P : c ∈ P := hP.A_le h.c_mem

theorem Q_index : (Qsub K P).relIndex P = 7 := by
  have hidx := h.K_data.out_index P hP.pgroup (h.P_le_normalizer_K hP)
  have hmul := Subgroup.relIndex_mul_card (Qsub K P) P
  rw [inf_eq_left.mpr (Qsub_le K P), h.card_P hP] at hmul
  have hne : (Qsub K P).relIndex P ≠ 1 := by
    intro h1
    exact h.c_notMem_Q (P := P) (Subgroup.relIndex_eq_one.mp h1 (h.c_mem_P hP))
  have hdvd : (Qsub K P).relIndex P ∣ 7 ^ 5 := Dvd.intro _ hmul
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hdvd
  have hle : (Qsub K P).relIndex P ≤ 7 := hidx
  rw [hj'] at hne hle ⊢
  interval_cases j
  · exact absurd rfl hne
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

theorem Q_card : Nat.card (Qsub K P) = 7 ^ 4 := by
  have hmul := Subgroup.relIndex_mul_card (Qsub K P) P
  rw [inf_eq_left.mpr (Qsub_le K P), h.card_P hP, h.Q_index hP] at hmul
  have : 7 * Nat.card (Qsub K P) = 7 * 7 ^ 4 := by rw [hmul]; norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this

theorem Q_normal : ((Qsub K P).subgroupOf P).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Qsub_le K P)]
  intro x hx
  refine mem_normalizer_of_conj_mem (Qsub K P) fun q hq => ?_
  exact Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hx (Subgroup.mem_inf.mp hq).1) (P.inv_mem hx),
    conj_mem_KC (h.P_le_normalizer_K hP hx) (Subgroup.mem_inf.mp hq).2⟩

theorem Q_quot_card : Nat.card (↥P ⧸ (Qsub K P).subgroupOf P) = 7 := h.Q_index hP

theorem P_comm_mod_Q (x y : ↥P) : x * y * x⁻¹ * y⁻¹ ∈ (Qsub K P).subgroupOf P := by
  have := h.Q_normal hP
  have hq := h.Q_quot_card hP
  have : IsCyclic (↥P ⧸ (Qsub K P).subgroupOf P) := isCyclic_of_prime_card hq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥P ⧸ (Qsub K P).subgroupOf P)
  have hcomm : ∀ a b : ↥P ⧸ (Qsub K P).subgroupOf P, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact (Commute.zpow_zpow_self g i j).eq
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have e := hcomm (x : ↥P ⧸ (Qsub K P).subgroupOf P) (y : ↥P ⧸ (Qsub K P).subgroupOf P)
  calc (x : ↥P ⧸ (Qsub K P).subgroupOf P) * y * (x : ↥P ⧸ (Qsub K P).subgroupOf P)⁻¹ *
        (y : ↥P ⧸ (Qsub K P).subgroupOf P)⁻¹
      = (y * x) * (x : ↥P ⧸ (Qsub K P).subgroupOf P)⁻¹ *
        (y : ↥P ⧸ (Qsub K P).subgroupOf P)⁻¹ := by rw [e]
    _ = 1 := by group

theorem P_eq_zpowers_mul_Q {x : G} (hx : x ∈ P) : ∃ j : ℤ, ∃ q ∈ Qsub K P, x = c ^ j * q := by
  have := h.Q_normal hP
  have hq := h.Q_quot_card hP
  have hg1 : (⟨c, h.c_mem_P hP⟩ : ↥P) ∉ (Qsub K P).subgroupOf P := fun hc => h.c_notMem_Q (P := P) hc
  have hg : ((⟨c, h.c_mem_P hP⟩ : ↥P) : ↥P ⧸ (Qsub K P).subgroupOf P) ≠ 1 := by
    intro h1
    exact hg1 ((QuotientGroup.eq_one_iff _).mp h1)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card hq hg (g' := ((⟨x, hx⟩ : ↥P) : ↥P ⧸ (Qsub K P).subgroupOf P)))
  refine ⟨j, c ^ (-j) * x, ?_, by group⟩
  have h2 : (((⟨c, h.c_mem_P hP⟩ : ↥P) ^ j : ↥P) : ↥P ⧸ (Qsub K P).subgroupOf P) =
      ((⟨x, hx⟩ : ↥P) : ↥P ⧸ (Qsub K P).subgroupOf P) := by
    rw [QuotientGroup.mk_zpow]; exact hj
  have h3 := QuotientGroup.eq.mp h2
  have h4 : ((⟨c, h.c_mem_P hP⟩ : ↥P) ^ j)⁻¹ * ⟨x, hx⟩ ∈ (Qsub K P).subgroupOf P := h3
  rw [Subgroup.mem_subgroupOf] at h4
  have e : (((⟨c, h.c_mem_P hP⟩ : ↥P) ^ j)⁻¹ * ⟨x, hx⟩ : ↥P).1 = c ^ (-j) * x := by
    simp [zpow_neg]
  rw [e] at h4
  exact h4

omit hP in
include h in
theorem b_mem_centralizer_K : b ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (h.K_cent_b hk)

omit hP in
include h in
theorem B_eq_sup : B = Subgroup.zpowers b ⊔ Subgroup.zpowers d :=
  B_eq_sup_of (fun _ hx => h.A_pow hx) h.B_le h.B_card h.b_mem h.b_ne h.d_mem h.d_ne h.d_K
    h.K_cent_b h.K_data.inf_centralizer

theorem B_le_Q : B ≤ Qsub K P := by
  have hb : b ∈ Subgroup.centralizer (K : Set G) := h.b_mem_centralizer_K
  rw [h.B_eq_sup]
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
  · exact hP.A_le (h.B_le h.b_mem)
  · exact Subgroup.mem_sup_right hb
  · exact hP.A_le (h.B_le h.d_mem)
  · exact Subgroup.mem_sup_left h.d_K

theorem eps_surj_Q : ∀ β ∈ B, ∃ x ∈ Qsub K P, eps c x = β := by
  intro β hβ
  obtain ⟨x, hxP, hx⟩ := h.eps_surj_P hP β hβ
  obtain ⟨j, q, hq, rfl⟩ := h.P_eq_zpowers_mul_Q hP hxP
  refine ⟨q, hq, ?_⟩
  have hcj : c ^ j ∈ Xs A B :=
    centralizer_le_Xs h.B_le (h.A_le_centralizer (A.zpow_mem h.c_mem j))
  have hqX : q ∈ Xs A B := hP.le_Xs (Qsub_le K P hq)
  rw [h.eps_mul hcj hqX] at hx
  have h1 : eps c (c ^ j) = 1 := by unfold eps; group
  rw [h1, one_mul] at hx
  exact hx

theorem Q_cap_cent : ∀ q ∈ Qsub K P, eps c q = 1 → q ∈ B := by
  intro q hq hε
  have hQX : Qsub K P ≤ Xs A B := (Qsub_le K P).trans hP.le_Xs
  let φ : ↥(Qsub K P) →* ↥B := h.epsHom.comp (Subgroup.inclusion hQX)
  have hφapply : ∀ x : ↥(Qsub K P), ((φ x : ↥B) : G) = eps c (x : G) := fun x => rfl
  have hφ : Function.Surjective φ := by
    intro β
    obtain ⟨x, hxQ, hx⟩ := h.eps_surj_Q hP β.1 β.2
    exact ⟨⟨x, hxQ⟩, Subtype.ext (by rw [hφapply]; exact hx)⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [h.B_card, h.Q_card hP] at hcard
  have hker : Nat.card φ.ker = 7 ^ 2 := by
    have e : Nat.card φ.ker * 7 ^ 2 = 7 ^ 2 * 7 ^ 2 := by rw [hcard]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) e
  have hBle : B.subgroupOf (Qsub K P) ≤ φ.ker := by
    intro x hx
    have hxB : (x : G) ∈ B := hx
    have hxX : (x : G) ∈ Xs A B := hQX x.2
    have hxC : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact h.A_comm ha (h.B_le hxB)
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (by rw [hφapply]; exact (h.eps_eq_one_iff hxX).mpr hxC)
  have hBcard : Nat.card (B.subgroupOf (Qsub K P)) = 7 ^ 2 := by
    rw [← h.B_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.B_le_Q hP)).toEquiv
  have heq : B.subgroupOf (Qsub K P) = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hBle (by rw [hker, hBcard])
  have hmem : (⟨q, hq⟩ : ↥(Qsub K P)) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (by rw [hφapply]; exact hε)
  rw [← heq] at hmem
  exact hmem

theorem Q_pow_mem_B : ∀ v ∈ Qsub K P, v ^ 7 ∈ B := by
  intro v hv
  have hvX : v ∈ Xs A B := hP.le_Xs (Qsub_le K P hv)
  apply h.Q_cap_cent hP (v ^ 7) (Subgroup.pow_mem _ hv 7)
  have key : eps c (v ^ 7) = (eps c v) ^ 7 :=
    congrArg Subtype.val (map_pow h.epsHom (⟨v, hvX⟩ : ↥(Xs A B)) 7)
  rw [key]
  exact h.B_pow (h.eps_mem hvX)

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
