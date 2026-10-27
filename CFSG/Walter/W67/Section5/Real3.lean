module

public import CFSG.Walter.W67.Section5.Frame5

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Glauberman.Dickson

namespace Borel5

section PSL2

variable {F : Type} [Field F]

theorem unip_fixed_iff {y : F} (hy : y ≠ 0) (pt : PSL2ProjectiveLine F) :
    psl2QuotientMap F (sl2UpperUnipotent y) • pt = pt ↔ pt = psl2ProjectiveInfinity F := by
  constructor
  · induction pt using Projectivization.ind with
    | h v hv =>
        intro hfix
        rw [psl2QuotientMap_smul, Projectivization.smul_mk,
          Projectivization.mk_eq_mk_iff] at hfix
        obtain ⟨a, ha⟩ := hfix
        have hUv : sl2UpperUnipotent y • v = ![v 0 + y * v 1, v 1] := by
          change Matrix.mulVec (sl2UpperUnipotent y).val v = _
          ext i
          fin_cases i <;>
            simp [sl2UpperUnipotent, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
        rw [hUv] at ha
        by_cases hv1 : v 1 = 0
        · rw [psl2ProjectiveInfinity, Projectivization.mk_eq_mk_iff']
          refine ⟨v 0, ?_⟩
          ext i
          fin_cases i <;> simp [hv1]
        · have ha1 : (a : F) = 1 := by
            apply mul_right_cancel₀ hv1
            simpa [Units.smul_def] using congrFun ha 1
          have h0 : v 0 = v 0 + y * v 1 := by
            simpa [Units.smul_def, ha1] using congrFun ha 0
          have : y * v 1 = 0 := by
            have := congrArg (fun z => z - v 0) h0
            simpa using this.symm
          exact absurd this (mul_ne_zero hy hv1)
  · rintro rfl
    have hu : psl2QuotientMap F (sl2UpperUnipotent y) ∈ psl2UpperUnipotentSubgroup F :=
      (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨y, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp (psl2UpperUnipotent_le_borel hu)

theorem mem_borel_of_inverts {y : F} (hy : y ≠ 0) {t : PSL(2, F)}
    (ht : t * psl2QuotientMap F (sl2UpperUnipotent y) * t⁻¹ =
      (psl2QuotientMap F (sl2UpperUnipotent y))⁻¹) : t ∈ psl2Borel F := by
  set x := psl2QuotientMap F (sl2UpperUnipotent y)
  have hxinv : x⁻¹ = psl2QuotientMap F (sl2UpperUnipotent (-y)) := by
    rw [← map_inv, sl2UpperUnipotent_inv]
  have hfix : x⁻¹ • (t • psl2ProjectiveInfinity F) = t • psl2ProjectiveInfinity F := by
    calc x⁻¹ • (t • psl2ProjectiveInfinity F)
        = (t * x * t⁻¹) • (t • psl2ProjectiveInfinity F) := by rw [ht]
      _ = t • (x • psl2ProjectiveInfinity F) := by
          rw [← mul_smul, show t * x * t⁻¹ * t = t * x by group, mul_smul]
      _ = t • psl2ProjectiveInfinity F := by rw [(unip_fixed_iff hy _).mpr rfl]
  rw [hxinv, unip_fixed_iff (neg_ne_zero.mpr hy)] at hfix
  exact MulAction.mem_stabilizer_iff.mpr hfix

theorem not_inverted_unip [Fintype F] (hF : Fintype.card F % 4 = 3) {y : F} (hy : y ≠ 0)
    {t : PSL(2, F)}
    (ht : t * psl2QuotientMap F (sl2UpperUnipotent y) * t⁻¹ =
      (psl2QuotientMap F (sl2UpperUnipotent y))⁻¹) : False := by
  have htB := mem_borel_of_inverts hy ht
  have htUT := borel_le_unip_sup_torus htB
  obtain ⟨u, hu, d, hd, rfl⟩ := (mem_sup_iff_of_le_normalizer torus_le_normalizer_unip).mp htUT
  obtain ⟨c, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
  obtain ⟨a, rfl⟩ := hd
  have h1 : psl2QuotientMap F (sl2UpperUnipotent c) * torusHom F a *
      psl2QuotientMap F (sl2UpperUnipotent y) *
      (psl2QuotientMap F (sl2UpperUnipotent c) * torusHom F a)⁻¹ =
      psl2QuotientMap F (sl2UpperUnipotent ((a : F) ^ 2 * y)) := by
    have e1 : psl2QuotientMap F (sl2UpperUnipotent c) * torusHom F a *
        psl2QuotientMap F (sl2UpperUnipotent y) *
        (psl2QuotientMap F (sl2UpperUnipotent c) * torusHom F a)⁻¹ =
        psl2QuotientMap F (sl2UpperUnipotent c) *
        (torusHom F a * psl2QuotientMap F (sl2UpperUnipotent y) * (torusHom F a)⁻¹) *
        (psl2QuotientMap F (sl2UpperUnipotent c))⁻¹ := by group
    rw [e1, torusHom_conj, ← map_inv, ← map_mul, ← map_mul, sl2UpperUnipotent_inv,
      sl2UpperUnipotent_mul, sl2UpperUnipotent_mul]
    congr 2
    ring
  rw [h1, ← map_inv, sl2UpperUnipotent_inv] at ht
  have h2 : psl2QuotientMap F (sl2UpperUnipotent (((a : F) ^ 2 + 1) * y)) = 1 := by
    rw [show ((a : F) ^ 2 + 1) * y = (a : F) ^ 2 * y + y by ring, ← sl2UpperUnipotent_mul,
      map_mul, ht, ← map_mul, sl2UpperUnipotent_mul, neg_add_cancel, sl2UpperUnipotent_zero,
      map_one]
  have h3 := eq_zero_of_unip_eq_one h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · have hsq : IsSquare (-1 : F) := ⟨(a : F), by rw [← pow_two]; linear_combination -h4⟩
    exact (FiniteField.isSquare_neg_one_iff.mp hsq) hF
  · exact hy h4

theorem not_inverted_of_isPGroup {f : ℕ} [Fintype F] (hFcard : Nat.card F = 3 ^ f)
    (hF : Fintype.card F % 4 = 3) {x t : PSL(2, F)} (hx : x ≠ 1)
    (hx3 : IsPGroup 3 (Subgroup.zpowers x)) (ht : t * x * t⁻¹ = x⁻¹) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F hFcard
  obtain ⟨P, hP⟩ := hx3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, F) P Q
  have hxP : x ∈ (P : Subgroup PSL(2, F)) := hP (Subgroup.mem_zpowers x)
  have hgx : g * x * g⁻¹ ∈ psl2UpperUnipotentSubgroup F := by
    rw [← hQ, ← hg, Sylow.coe_subgroup_smul]
    exact ⟨x, hxP, rfl⟩
  obtain ⟨y, hy⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hgx
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [sl2UpperUnipotent_zero, map_one] at hy
    apply hx
    have := congrArg (fun z => g⁻¹ * z * g) hy
    simpa [mul_assoc] using this
  apply not_inverted_unip hF hy0 (t := g * t * g⁻¹)
  rw [← hy]
  calc g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * x * t⁻¹) * g⁻¹ := by group
    _ = (g * x * g⁻¹)⁻¹ := by rw [ht]; group

end PSL2

end Borel5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem index_ne_two_of_perfect_std (hperf : commutator G = ⊤) (N : Subgroup G) (hN : N.Normal) :
    N.index ≠ 2 := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index_eq_card, h2]
  have := isCyclic_of_prime_card hcard
  have hle : commutator G ≤ (QuotientGroup.mk' N).ker := Abelianization.commutator_subset_ker _
  rw [hperf, QuotientGroup.ker_mk', top_le_iff] at hle
  rw [hle, Subgroup.index_top] at h2
  exact absurd h2 (by norm_num)

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem exists_decomp_H_JM
    {x : G} (hx : x ∈ h.H) :
    ∃ j ∈ Subgroup.zpowers h.J, ∃ m ∈ h.K ⊔ fr.E, x = j * m := by
  obtain ⟨hsup, -, hcent⟩ := fr.isInternalDirectProduct_H
  have hN : Subgroup.zpowers h.J ≤ Subgroup.normalizer ((h.K ⊔ fr.E : Subgroup G) : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  rw [← hsup, sup_comm] at hx
  obtain ⟨m, hm, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hx
  exact ⟨j, hj, m, hm, Subgroup.mem_centralizer_iff.mp (hcent hj) m hm⟩

theorem commute_of_mem_KE
    {j m : G} (hj : j ∈ Subgroup.zpowers h.J) (hm : m ∈ h.K ⊔ fr.E) :
    j * m = m * j :=
  (Subgroup.mem_centralizer_iff.mp (fr.isInternalDirectProduct_H.2.2 hj) m hm).symm

theorem mem_K_of_mem_KE_of_mul_self
    {m : G} (hm : m ∈ h.K ⊔ fr.E) (hm2 : m * m = 1) :
    m ∈ h.K := by
  obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer fr.E_le_normalizer_K).mp hm
  have he2 : e * e ∈ h.K := by
    have h1 : e * e = (k * (e * k * e⁻¹))⁻¹ * (k * e * (k * e)) := by group
    rw [h1, hm2, mul_one]
    exact h.K.inv_mem (h.K.mul_mem hk
      ((Subgroup.mem_normalizer_iff.mp (fr.E_le_normalizer_K he) k).mp hk))
  have he2' : e * e = 1 := by
    have := Subgroup.mem_inf.mpr ⟨he2, fr.E.mul_mem he he⟩
    rw [fr.K_inf_E, Subgroup.mem_bot] at this
    exact this
  have he1 : e = 1 := by
    obtain ⟨n, hn⟩ := odd_orderOf_of_mem_oddPart he
    have hdvd : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, he2'])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · omega
  rw [he1, mul_one]
  exact hk

theorem mem_KE_of_odd
    {x : G} (hx : x ∈ h.H) (hodd : Odd (orderOf x)) : x ∈ h.K ⊔ fr.E := by
  obtain ⟨j, hj, m, hm, rfl⟩ := fr.exists_decomp_H_JM hx
  rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
  · rwa [one_mul]
  exfalso
  obtain ⟨n, hn⟩ := hodd
  have hc := fr.commute_of_mem_KE hj hm
  have h1 : (h.J * m) ^ orderOf (h.J * m) = 1 := pow_orderOf_eq_one _
  rw [(Commute.mul_pow hc), hn, pow_succ, pow_mul, pow_two, h.J_mul_J, one_pow,
    one_mul] at h1
  have hJ : h.J = (m ^ (2 * n + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
  apply h.J_not_mem_K
  have hJKE : h.J ∈ h.K ⊔ fr.E := by
    rw [hJ]
    exact (h.K ⊔ fr.E).inv_mem ((h.K ⊔ fr.E).pow_mem hm _)
  have hdisj := fr.isInternalDirectProduct_H.2.1
  have : h.J ∈ Subgroup.zpowers h.J ⊓ (h.K ⊔ fr.E) := ⟨Subgroup.mem_zpowers _, hJKE⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at this
  exact absurd this h.J_ne_one

end Frame

namespace Std

variable (s : Std G)

theorem q_mod_four (hp : s.p = 3) : s.q % 4 = 3 := by
  have h8 := s.toHyp.mod_eight
  have hq : s.q = 3 ^ s.f := by rw [Hyp.q, hp]
  rw [hq] at h8 ⊢
  rcases Nat.even_or_odd s.f with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    rw [hk, ← two_mul, pow_mul, Nat.pow_mod] at h8
    norm_num at h8
  · rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem no_real_three_K (hp : s.p = 3) {x t : G} (hx : x ∈ s.K) (ht : t ∈ s.K) (hx1 : x ≠ 1)
    {k : ℕ} (hx3 : x ^ (3 ^ k) = 1) (hinv : t * x * t⁻¹ = x⁻¹) : False := by
  set F := GaloisField s.p s.f
  let : Fintype F := Fintype.ofFinite F
  have hFcard : Nat.card F = 3 ^ s.f := by rw [GaloisField.card s.p s.f s.f_pos.ne', hp]
  have hF4 : Fintype.card F % 4 = 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card s.p s.f s.f_pos.ne']
    exact s.q_mod_four hp
  set x' := s.iso ⟨x, hx⟩
  set t' := s.iso ⟨t, ht⟩
  have hx'1 : x' ≠ 1 := by
    intro h1
    apply hx1
    have := congrArg Subtype.val (s.iso.injective (h1.trans (map_one s.iso).symm))
    exact this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx'3 : IsPGroup 3 (Subgroup.zpowers x') := by
    have hdvd : orderOf x' ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have : (⟨x, hx⟩ : s.K) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    apply IsPGroup.of_card (n := j)
    rw [Nat.card_zpowers, hj]
  have hinv' : t' * x' * t'⁻¹ = x'⁻¹ := by
    have : (⟨t, ht⟩ : s.K) * ⟨x, hx⟩ * (⟨t, ht⟩ : s.K)⁻¹ = (⟨x, hx⟩ : s.K)⁻¹ :=
      Subtype.ext (by simpa using hinv)
    rw [← map_mul, ← map_inv, ← map_mul, this, map_inv]
  exact Borel5.not_inverted_of_isPGroup hFcard hF4 hx'1 hx'3 hinv'

theorem no_real_three_H
    (hp : s.p = 3) {x t : G} (hx : x ∈ s.H) (ht : t ∈ s.H) (hx1 : x ≠ 1)
    {k : ℕ} (hx3 : x ^ (3 ^ k) = 1) (ht2 : t * t = 1) (hinv : t * x * t⁻¹ = x⁻¹) : False := by
  have hodd : Odd (orderOf x) := by
    have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hx3
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hdvd
  have hxKE := s.fr.mem_KE_of_odd hx hodd
  obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM ht
  have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => s.fr.commute_of_mem_KE hj hy
  have hjj : j * j = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
    · exact mul_one 1
    · exact s.J_mul_J
  have hmm : m * m = 1 := by
    calc m * m = (j * j)⁻¹ * (j * (j * m) * m) := by group
      _ = (j * j)⁻¹ * (j * (m * j) * m) := by rw [hjc m hm]
      _ = (j * j)⁻¹ * ((j * m) * (j * m)) := by group
      _ = 1 := by rw [ht2, hjj]; group
  have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmm
  have hmK := s.fr.mem_K_of_mem_KE_of_mul_self hm hmm
  have hmxKE : m * x * m⁻¹ ∈ s.K ⊔ s.fr.E :=
    (s.K ⊔ s.fr.E).mul_mem ((s.K ⊔ s.fr.E).mul_mem hm hxKE) ((s.K ⊔ s.fr.E).inv_mem hm)
  have hmx : m * x * m⁻¹ = x⁻¹ := by
    rw [← hinv]
    calc m * x * m⁻¹ = (m * x * m⁻¹ * j) * j⁻¹ := by group
      _ = (j * (m * x * m⁻¹)) * j⁻¹ := by rw [hjc _ hmxKE]
      _ = j * m * x * (j * m)⁻¹ := by group
  have hxm : x * m ∈ s.K := by
    refine s.fr.mem_K_of_mem_KE_of_mul_self ((s.K ⊔ s.fr.E).mul_mem hxKE hm) ?_
    calc x * m * (x * m) = x * (m * x * m⁻¹) * (m * m) := by group
      _ = 1 := by rw [hmx, hmm]; group
  have hxK : x ∈ s.K := by
    have := s.K.mul_mem hxm (s.K.inv_mem hmK)
    rwa [mul_inv_cancel_right] at this
  exact s.no_real_three_K hp hxK hmK hx1 hx3 hmx

theorem no_real_three
    (h22 : S_lemma_2_2) (hp : s.p = 3) {u x t : G} (hu : orderOf u = 2)
    (hx : x ∈ Subgroup.centralizer ({u} : Set G)) (ht : t ∈ Subgroup.centralizer ({u} : Set G))
    (hx1 : x ≠ 1) {k : ℕ} (hx3 : x ^ (3 ^ k) = 1) (ht2 : t * t = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) : False := by
  have hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    fun N hN => index_ne_two_of_perfect_std s.perfect N hN
  obtain ⟨g, hg⟩ := isConj_iff.mp ((h22 G s.toHyp s.fr hidx).2.2 u s.J hu s.orderOf_J)
  have hmem : ∀ y ∈ Subgroup.centralizer ({u} : Set G), g * y * g⁻¹ ∈ s.H := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hg]
    calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hy]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  apply s.no_real_three_H hp (hmem x hx) (hmem t ht) (k := k) _ _ _ _
  · intro h1
    apply hx1
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this
  · rw [conj_pow, hx3]
    group
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  · calc g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * x * t⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹)⁻¹ := by rw [hinv]; group

end Std

end CFSG.Walter.W67
