module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2PGL
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Defs
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

theorem card_closure_of_inverted {G : Type*} [Group G] [Finite G] {t a : G} {n : ℕ}
    (ht : t * t = 1) (ht1 : t ≠ 1) (ha : orderOf a = n)
    (hinv : t * a * t⁻¹ = a⁻¹) (hnodd : Odd n) :
    Nat.card (Subgroup.closure ({t, a} : Set G)) = 2 * n := by
  have htord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht) ht1
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le, CFSG.GroupTheory.mem_normalizer_zpowers_iff, hinv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hdisj : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxa hxt
    have h1 : orderOf x ∣ n := by
      have := orderOf_dvd_of_mem_zpowers hxa
      rwa [ha] at this
    have h2 : orderOf x ∣ 2 := by
      have := orderOf_dvd_of_mem_zpowers hxt
      rwa [htord] at this
    have hcop : Nat.Coprime n 2 := (Nat.coprime_two_left.mpr hnodd).symm
    have hdvd : orderOf x ∣ n.gcd 2 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  rw [show Subgroup.closure ({t, a} : Set G) =
      Subgroup.zpowers a ⊔ Subgroup.zpowers t by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure, sup_comm]]
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, Nat.card_zpowers, ha, htord]
  omega

private theorem no_overgroup_of_inverted_pslRange
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKcard : Nat.card K = p ^ f) {t a : PGL2 K}
    (htJ : t ∈ pslRange K) (haJ : a ∈ pslRange K)
    (ht : t * t = 1) (hinv : t * a * t⁻¹ = a⁻¹)
    {n : ℕ} (han : orderOf a = n)
    (hDcard : Nat.card (Subgroup.closure ({t, a} : Set (PGL2 K))) = 2 * n)
    (hn6 : 6 ≤ n) (hnp : Nat.Coprime p n)
    (hcase : (n = (p ^ f - 1) / 2 ∧ 13 ≤ p ^ f) ∨ n = (p ^ f + 1) / 2) :
    ∀ M : Subgroup (PGL2 K), Subgroup.closure ({t, a} : Set (PGL2 K)) < M →
      M ≤ pslRange K → M ≠ pslRange K → False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let φ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  have hφinj : Function.Injective φ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  intro M hDM hMJ hMJne
  obtain ⟨w, rfl⟩ := htJ
  obtain ⟨u, rfl⟩ := haJ
  have hDrange : Subgroup.closure ({φ w, φ u} : Set (PGL2 K)) ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨w, rfl⟩
    · exact ⟨u, rfl⟩
  have hMrange : M ≤ φ.range := hMJ
  let H := (Subgroup.closure ({φ w, φ u} : Set (PGL2 K))).comap φ
  let K' := M.comap φ
  have hHKle : H ≤ K' := Subgroup.comap_mono hDM.le
  have hHKne : H ≠ K' := by
    intro hEq
    have hmap : Subgroup.closure ({φ w, φ u} : Set (PGL2 K)) = M := by
      calc Subgroup.closure ({φ w, φ u} : Set (PGL2 K))
          = H.map φ := (Subgroup.map_comap_eq_self hDrange).symm
        _ = K'.map φ := by rw [hEq]
        _ = M := Subgroup.map_comap_eq_self hMrange
    exact (ne_of_gt hDM) hmap.symm
  have hHKlt : H < K' := lt_of_le_of_ne hHKle hHKne
  have hK'top : K' ≠ ⊤ := by
    intro htop
    apply hMJne
    calc M = K'.map φ := (Subgroup.map_comap_eq_self hMrange).symm
      _ = (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map φ := by
        rw [htop]
      _ = φ.range := Subgroup.map_top φ
      _ = pslRange K := rfl
  have huH : u ∈ H := by
    rw [Subgroup.mem_comap]
    exact Subgroup.subset_closure (by simp)
  have hwH : w ∈ H := by
    rw [Subgroup.mem_comap]
    exact Subgroup.subset_closure (by simp)
  have hinv' : w * u * w⁻¹ = u⁻¹ := by
    apply hφinj
    simpa only [map_mul, map_inv] using hinv
  have hun : orderOf u = n := by
    rw [← orderOf_injective φ hφinj u]
    exact han
  have hHcard : Nat.card H = 2 * n := by
    rw [← Subgroup.card_map_of_injective (K := H) (f := φ) hφinj,
      Subgroup.map_comap_eq_self hDrange, hDcard]
  exact CFSG.Glauberman.Dickson.MaxUp.no_overgroup_of_inverted hKcard hp2 H K' hHKlt hK'top
    huH hwH hinv' hun hHcard hn6 hnp hcase

private lemma outerTorus_div_two_basic (q : ℕ) (hq : Odd q) (h13 : 13 ≤ q) :
    Odd (outerTorusOrder q / 2) ∧ 6 ≤ outerTorusOrder q / 2 ∧
      ((outerTorusOrder q / 2 = (q - 1) / 2 ∧ 13 ≤ q) ∨
        outerTorusOrder q / 2 = (q + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hq
  have hm : outerTorusOrder (2*k+1) % 4 = 2 :=
    outerTorusOrder_mod_four (q := 2*k+1) (by exact ⟨k, rfl⟩)
  rcases outerTorusOrder_eq (q := 2*k+1) with h | h
  · rw [h]
    rw [show 2*k+2 = (k+1)*2 by omega, Nat.mul_div_left (k+1) (by norm_num)]
    have hk6 : 6 ≤ k+1 := by omega
    refine ⟨?_, hk6, Or.inr ?_⟩
    · rw [Nat.odd_iff]
      omega
    · rfl
  · have h' : outerTorusOrder (2*k+1) = 2*k := by omega
    rw [h']
    rw [show 2*k = k*2 by omega, Nat.mul_div_left k (by norm_num)]
    have hk6 : 6 ≤ k := by omega
    refine ⟨?_, hk6, Or.inl ⟨?_, by omega⟩⟩
    · rw [Nat.odd_iff]
      omega
    · rw [show (k*2+1-1)/2 = k by
        rw [show k*2+1-1 = k*2 by omega, Nat.mul_div_left k (by norm_num)]]

private lemma outerTorus_sub_arith (q : ℕ) (hq : Odd q) (h13 : 13 ≤ q) :
    ¬ (2*q - outerTorusOrder q) / 2 ∣ outerTorusOrder q ∧
      6 ≤ (2*q - outerTorusOrder q) / 2 := by
  obtain ⟨k, rfl⟩ := hq
  rcases outerTorusOrder_eq (q := 2*k+1) with h | h
  · rw [h]
    have he : 2*(2*k+1)-(2*k+1+1) = 2*k := by omega
    rw [he, show 2*k = k*2 by omega, Nat.mul_div_left k (by norm_num)]
    have hk6 : 6 ≤ k := by omega
    constructor
    · intro hd
      have hk2 : k ∣ 2*k+2 := by
        rw [show 2*k+2 = k*2+1+1 by omega]
        exact hd
      have hk0 : k ∣ 2*k := by rw [mul_comm]; exact dvd_mul_right k 2
      have hsub : k ∣ (2*k+2) - 2*k := Nat.dvd_sub hk2 hk0
      have hEq : (2*k+2) - 2*k = 2 := by omega
      rw [hEq] at hsub
      have := Nat.le_of_dvd (by norm_num) hsub
      omega
    · omega
  · have h' : outerTorusOrder (2*k+1) = 2*k := by omega
    rw [h']
    have he : 2*(2*k+1)-2*k = 2*k+2 := by omega
    rw [he, show 2*k+2 = (k+1)*2 by omega, Nat.mul_div_left (k+1) (by norm_num)]
    have hk7 : 7 ≤ k+1 := by omega
    constructor
    · intro hd
      have hk2 : k+1 ∣ 2*k := hd
      have hk1 : k+1 ∣ 2*(k+1) := by rw [mul_comm]; exact dvd_mul_right (k+1) 2
      have hsub : k+1 ∣ 2*(k+1) - 2*k := Nat.dvd_sub hk1 hk2
      have hEq : 2*(k+1) - 2*k = 2 := by omega
      rw [hEq] at hsub
      have := Nat.le_of_dvd (by norm_num) hsub
      omega
    · omega

theorem parrottGen_pgl2_of_thirteen_le {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f)
    (hq : 13 ≤ p ^ f) {t β : PGL2 K} (htJ : t ∈ pslRange K) (hβJ : β ∉ pslRange K)
    (ht : t * t = 1) (ht1 : t ≠ 1) (hβ : β * β = 1) (hcomm : t * β = β * t) :
    ParrottGen (pslRange K) t β := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hf0, hKcard⟩
  have : Fact p.Prime := ⟨hp⟩
  have hqodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hK
  have hqodd' : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcard : 3 < Nat.card K := by rw [hKcard]; omega
  have hJ2 : (pslRange K).index = 2 := pslRange_index_eq_two hK
  have hJnormal : (pslRange K).Normal := pslRange_normal hK hcard
  set n : ℕ := outerTorusOrder (p ^ f) / 2 with hn_def
  have harith := outerTorus_div_two_basic (p ^ f) hqodd' hq
  have hnodd : Odd n := by rw [hn_def]; exact harith.1
  have hn6 : 6 ≤ n := by rw [hn_def]; exact harith.2.1
  have hcase : (n = (p ^ f - 1) / 2 ∧ 13 ≤ p ^ f) ∨ n = (p ^ f + 1) / 2 := by
    rw [hn_def]
    exact harith.2.2
  have hnp : Nat.Coprime p n := by
    rw [hn_def]
    rcases outerTorusOrder_eq (q := p ^ f) with h | h
    · rw [h]
      exact CFSG.Glauberman.Dickson.MaxUp.coprime_half_add hp2 hf0
    · rw [h]
      exact CFSG.Glauberman.Dickson.MaxUp.coprime_half_sub hp2 hf0
  have hm4 := outerTorusOrder_mod_four hqodd
  have h2outer : 2 ∣ outerTorusOrder (Nat.card K) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  obtain ⟨U, w, hUc, hUcard, hβU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard (by rw [pow_two]; exact hβ) hβJ
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have htC : t ∈ Subgroup.centralizer ({β} : Set (PGL2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have htU : t ∉ U := by
    intro htU
    have hodd := odd_orderOf_of_mem_outer_torus hK hcard hβJ hUcard hβU htU htJ
    rw [orderOf_eq_prime (by rw [pow_two]; exact ht) ht1] at hodd
    exact absurd hodd (by decide)
  have htinvU := inverts_of_mem_sup_not_mem hUcomm hww hwinv (hC ▸ htC) htU
  have hinvU : ∀ y ∈ U, t * y * t⁻¹ = y⁻¹ := htinvU.2
  obtain ⟨gU, hgUord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  let g : PGL2 K := (gU : PGL2 K)
  have hgU : g ∈ U := gU.2
  have hgord : orderOf g = outerTorusOrder (Nat.card K) := by
    change orderOf (gU : PGL2 K) = outerTorusOrder (Nat.card K)
    rw [Subgroup.orderOf_coe gU, hgUord, hUcard]
  let τ₀ : PGL2 K := g ^ 2
  have hτ0U : τ₀ ∈ U := U.pow_mem hgU 2
  have hτ0J : τ₀ ∈ pslRange K := by
    simpa [τ₀, pow_two] using Subgroup.mul_self_mem_of_index_two hJ2 g
  have hτ0ord : orderOf τ₀ = n := by
    dsimp [τ₀]
    rw [orderOf_pow, hgord, Nat.gcd_eq_right h2outer]
    rw [hn_def, ← hKcard]
  have hτ01 : τ₀ ≠ 1 := by
    intro h
    have h1 : orderOf τ₀ = 1 := by rw [h, orderOf_one]
    rw [hτ0ord] at h1
    omega
  have hτ0inv : t * τ₀ * t⁻¹ = τ₀⁻¹ := hinvU τ₀ hτ0U
  have hβτ0 : β * τ₀ * β⁻¹ = τ₀ := by
    rw [hUcomm β hβU τ₀ hτ0U, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨z, hzt, hβz, hzord⟩ :=
    exists_inverted_of_inner_outer hK hcard ht ht1 htJ hβ hβJ hcomm
  have h2e : 2 ∣ 2 * Nat.card K - outerTorusOrder (Nat.card K) :=
    Nat.dvd_sub (dvd_mul_right 2 (Nat.card K)) h2outer
  have horderZ2 : orderOf (z ^ 2) =
      (2 * Nat.card K - outerTorusOrder (Nat.card K)) / 2 := by
    rw [orderOf_pow, hzord, Nat.gcd_eq_right h2e]
  have h2n_eq : 2 * n = outerTorusOrder (Nat.card K) := by
    rw [hn_def, ← hKcard]
    exact Nat.mul_div_cancel' h2outer
  have he_arith := outerTorus_sub_arith (Nat.card K) hqodd (by rw [hKcard]; exact hq)
  have hnotdvd : ¬ orderOf (z ^ 2) ∣ 2 * n := by
    intro hd
    apply he_arith.1
    rwa [horderZ2, h2n_eq] at hd
  set s : PGL2 K := z * β with hs_def
  set τ : PGL2 K := s * τ₀ * s⁻¹ with hτ_def
  have hτJ : τ ∈ pslRange K := hJnormal.conj_mem τ₀ hτ0J s
  have hτord : orderOf τ = n := by
    have hsem : SemiconjBy s τ₀ τ := by
      rw [hτ_def]
      change s * τ₀ = (s * τ₀ * s⁻¹) * s
      group
    rw [← SemiconjBy.orderOf_eq s hsem, hτ0ord]
  have hτodd : Odd (orderOf τ) := by rw [hτord]; exact hnodd
  have htz : t * z * t⁻¹ = z := by
    rw [← hzt, mul_assoc, mul_inv_cancel, mul_one]
  have htβ : t * β * t⁻¹ = β := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hts : t * s * t⁻¹ = s := by
    rw [hs_def]
    calc t * (z * β) * t⁻¹ = (t * z * t⁻¹) * (t * β * t⁻¹) := by group
      _ = z * β := by rw [htz, htβ]
  have hst : t * s = s * t := by
    calc t * s = (t * s * t⁻¹) * t := by group
      _ = s * t := by rw [hts]
  have hτinv : t * τ * t⁻¹ = τ⁻¹ := by
    rw [hτ_def]
    calc t * (s * τ₀ * s⁻¹) * t⁻¹ = (t * s) * τ₀ * (t * s)⁻¹ := by group
      _ = (s * t) * τ₀ * (s * t)⁻¹ := by rw [hst]
      _ = s * (t * τ₀ * t⁻¹) * s⁻¹ := by group
      _ = s * τ₀⁻¹ * s⁻¹ := by rw [hτ0inv]
      _ = (s * τ₀ * s⁻¹)⁻¹ := by group
  set c : PGL2 K := β * τ * β⁻¹ with hc_def
  have hcJ : c ∈ pslRange K := hJnormal.conj_mem τ hτJ β
  have hcord : orderOf c = n := by
    have hsem : SemiconjBy β τ c := by
      rw [hc_def]
      change β * τ = (β * τ * β⁻¹) * β
      group
    rw [← SemiconjBy.orderOf_eq β hsem, hτord]
  have hcodd : Odd (orderOf c) := by rw [hcord]; exact hnodd
  have hDcard : Nat.card (Subgroup.closure ({t, τ} : Set (PGL2 K))) = 2 * n :=
    card_closure_of_inverted ht ht1 hτord hτinv hnodd
  have hD0card : Nat.card (Subgroup.closure ({t, τ₀} : Set (PGL2 K))) = 2 * n :=
    card_closure_of_inverted ht ht1 hτ0ord hτ0inv hnodd
  have hc_notD : c ∉ Subgroup.closure ({t, τ} : Set (PGL2 K)) := by
    intro hcD
    have hczp : c ∈ Subgroup.zpowers τ := by
      have hD_eq : Subgroup.closure ({t, τ} : Set (PGL2 K)) =
          Subgroup.zpowers t ⊔ Subgroup.zpowers τ := by
        rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
          Subgroup.zpowers_eq_closure]
      have hmem : c ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers τ := by
        rw [← hD_eq]
        exact hcD
      have hτN : t ∈ Subgroup.normalizer (Subgroup.zpowers τ : Set (PGL2 K)) := by
        rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff, hτinv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers τ)
      have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
      obtain ⟨l, hl, hcl | hctl⟩ :=
        (mem_zpowers_sup_iff (L := Subgroup.zpowers τ) (a := t) hτN ht2).mp hmem
      · rw [hcl]
        exact hl
      · exfalso
        have hconj_l : t * l * t⁻¹ = l⁻¹ := by
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
          calc t * τ ^ j * t⁻¹ = (t * τ * t⁻¹) ^ j :=
                (conj_zpow (a := t) (b := τ) (i := j)).symm
            _ = (τ⁻¹) ^ j := by rw [hτinv]
            _ = (τ ^ j)⁻¹ := inv_zpow τ j
        have htl : t * l = l⁻¹ * t := by
          calc t * l = (t * l * t⁻¹) * t := by group
            _ = l⁻¹ * t := by rw [hconj_l]
        have hcc : c * c = 1 := by
          rw [hctl]
          calc (t * l) * (t * l) = (l⁻¹ * t) * (t * l) := by
                nth_rewrite 1 [htl]
                rfl
            _ = l⁻¹ * (t * t) * l := by group
            _ = l⁻¹ * 1 * l := by rw [ht]
            _ = 1 := by rw [mul_one, inv_mul_cancel]
        have hc1 := eq_one_of_mul_self_of_odd hcc hcodd
        rw [hc1, orderOf_one] at hcord
        omega
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hczp
    have hc_eq : β * τ * β⁻¹ = τ ^ k := by
      rw [← hc_def, ← hk]
    have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
    have hβz_inv : β * z⁻¹ * β⁻¹ = z := by
      have h := congrArg (fun y => y⁻¹) hβz
      simpa [mul_inv_rev, mul_assoc] using h
    have hβz_swap : β * z⁻¹ = z * β := by
      calc β * z⁻¹ = (β * z⁻¹ * β⁻¹) * β := by group
        _ = z * β := by rw [hβz_inv]
    have hs_beta : s⁻¹ * β * s = z ^ 2 * β := by
      rw [hs_def, mul_inv_rev, hβinv, hβz_swap]
      calc (z * β) * β * (z * β) = z * (β * β) * z * β := by group
        _ = z * 1 * z * β := by rw [hβ]
        _ = z ^ 2 * β := by rw [pow_two]; group
    have hs_tau0 : s⁻¹ * τ * s = τ₀ := by
      rw [hτ_def]
      group
    have hβτ0' : (z ^ 2 * β) * τ₀ * (z ^ 2 * β)⁻¹ =
        z ^ 2 * τ₀ * (z ^ 2)⁻¹ := by
      rw [mul_inv_rev]
      calc (z ^ 2 * β) * τ₀ * (β⁻¹ * (z ^ 2)⁻¹) =
          z ^ 2 * (β * τ₀ * β⁻¹) * (z ^ 2)⁻¹ := by group
        _ = z ^ 2 * τ₀ * (z ^ 2)⁻¹ := by rw [hβτ0]
    have hstep : s⁻¹ * (β * τ * β⁻¹) * s =
        (z ^ 2 * β) * τ₀ * (z ^ 2 * β)⁻¹ := by
      calc s⁻¹ * (β * τ * β⁻¹) * s =
          (s⁻¹ * β * s) * (s⁻¹ * τ * s) * (s⁻¹ * β * s)⁻¹ := by group
        _ = (z ^ 2 * β) * τ₀ * (z ^ 2 * β)⁻¹ := by rw [hs_beta, hs_tau0]
    have hτ_pow : τ ^ k = s * τ₀ ^ k * s⁻¹ := by
      rw [hτ_def]
      exact conj_zpow (a := s) (b := τ₀) (i := k)
    have hconj_zsq : z ^ 2 * τ₀ * (z ^ 2)⁻¹ = τ₀ ^ k := by
      calc z ^ 2 * τ₀ * (z ^ 2)⁻¹
          = (z ^ 2 * β) * τ₀ * (z ^ 2 * β)⁻¹ := hβτ0'.symm
        _ = s⁻¹ * (β * τ * β⁻¹) * s := hstep.symm
        _ = s⁻¹ * τ ^ k * s := by rw [hc_eq]
        _ = τ₀ ^ k := by
          rw [hτ_pow]
          group
    have hz2N : z ^ 2 ∈ Subgroup.normalizer
        (Subgroup.zpowers τ₀ : Set (PGL2 K)) := by
      rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff, hconj_zsq]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers τ₀) k
    have htN0 : t ∈ Subgroup.normalizer (Subgroup.zpowers τ₀ : Set (PGL2 K)) := by
      rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff, hτ0inv]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers τ₀)
    have hτ0N0 : τ₀ ∈ Subgroup.normalizer (Subgroup.zpowers τ₀ : Set (PGL2 K)) :=
      Subgroup.le_normalizer (Subgroup.mem_zpowers τ₀)
    have hz2J : z ^ 2 ∈ pslRange K := by
      simpa [pow_two] using Subgroup.mul_self_mem_of_index_two hJ2 z
    let M : Subgroup (PGL2 K) := Subgroup.closure ({t, τ₀, z ^ 2} : Set (PGL2 K))
    have hMJ : M ≤ pslRange K := by
      dsimp [M]
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact htJ
      · exact hτ0J
      · exact hz2J
    have hMnorm : M ≤ Subgroup.normalizer (Subgroup.zpowers τ₀ : Set (PGL2 K)) := by
      dsimp [M]
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact htN0
      · exact hτ0N0
      · exact hz2N
    have hD0leM : Subgroup.closure ({t, τ₀} : Set (PGL2 K)) ≤ M := by
      dsimp [M]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    have hz2M : z ^ 2 ∈ M := by
      dsimp [M]
      exact Subgroup.subset_closure (by simp)
    have hz2notD0 : z ^ 2 ∉ Subgroup.closure ({t, τ₀} : Set (PGL2 K)) := by
      intro hz2
      have hdvd : orderOf (z ^ 2) ∣
          Nat.card (Subgroup.closure ({t, τ₀} : Set (PGL2 K))) :=
        Subgroup.orderOf_dvd_natCard _ hz2
      rw [hD0card] at hdvd
      exact hnotdvd hdvd
    have hD0ltM : Subgroup.closure ({t, τ₀} : Set (PGL2 K)) < M := by
      refine lt_of_le_of_ne hD0leM ?_
      intro hEq
      have hz2D0 : z ^ 2 ∈ Subgroup.closure ({t, τ₀} : Set (PGL2 K)) := by
        rw [hEq]
        exact hz2M
      exact hz2notD0 hz2D0
    have hMneJ : M ≠ pslRange K := by
      intro hMeq
      let φ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
      have hφinj : Function.Injective φ :=
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* pslRange K :=
        MonoidHom.ofInjective (f := φ) hφinj
      have hJsimple : IsSimpleGroup (pslRange K) :=
        (MulEquiv.isSimpleGroup_congr e).mp
          (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := K) (by omega))
      have hHleJ : Subgroup.zpowers τ₀ ≤ pslRange K := by
        rw [Subgroup.zpowers_le]
        exact hτ0J
      have hHN : ((Subgroup.zpowers τ₀).subgroupOf (pslRange K)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHleJ, ← hMeq]
        exact hMnorm
      have : ((Subgroup.zpowers τ₀).subgroupOf (pslRange K)).Normal := hHN
      rcases Subgroup.Normal.eq_bot_or_eq_top
        ((Subgroup.zpowers τ₀).subgroupOf (pslRange K)) with hbot | htop
      · have hmem : (⟨τ₀, hτ0J⟩ : pslRange K) ∈
            (Subgroup.zpowers τ₀).subgroupOf (pslRange K) := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_zpowers τ₀
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hτ01 (congrArg Subtype.val hmem)
      · have hmem : (⟨t, htJ⟩ : pslRange K) ∈
            (Subgroup.zpowers τ₀).subgroupOf (pslRange K) := by
          rw [htop]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf] at hmem
        have htord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht) ht1
        have hdvd : 2 ∣ n := by
          have := orderOf_dvd_of_mem_zpowers hmem
          rwa [htord, hτ0ord] at this
        have hcop : Nat.Coprime n 2 := (Nat.coprime_two_left.mpr hnodd).symm
        have hdvd1 : 2 ∣ n.gcd 2 := Nat.dvd_gcd hdvd (dvd_refl 2)
        rw [hcop.gcd_eq_one] at hdvd1
        exact absurd hdvd1 (by norm_num)
    exact no_overgroup_of_inverted_pslRange hp hp2 hKcard htJ hτ0J ht hτ0inv
      hτ0ord hD0card hn6 hnp hcase M hD0ltM hMJ hMneJ
  let Ksub : Subgroup (PGL2 K) := Subgroup.closure ({t, τ, c} : Set (PGL2 K))
  have hDKle : Subgroup.closure ({t, τ} : Set (PGL2 K)) ≤ Ksub := by
    dsimp [Ksub]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hcK : c ∈ Ksub := by
    dsimp [Ksub]
    exact Subgroup.subset_closure (by simp)
  have hDK : Subgroup.closure ({t, τ} : Set (PGL2 K)) < Ksub := by
    refine lt_of_le_of_ne hDKle ?_
    intro hEq
    apply hc_notD
    rw [hEq]
    exact hcK
  have hKJ : Ksub ≤ pslRange K := by
    dsimp [Ksub]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact htJ
    · exact hτJ
    · exact hcJ
  have hKJe : Ksub = pslRange K := by
    by_contra hne
    exact no_overgroup_of_inverted_pslRange hp hp2 hKcard htJ hτJ ht hτinv
      hτord hDcard hn6 hnp hcase Ksub hDK hKJ hne
  have hgen : Ksub ≤ Subgroup.closure ({t, β, τ} : Set (PGL2 K)) := by
    dsimp [Ksub]
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have hβmem : β ∈ Subgroup.closure ({t, β, τ} : Set (PGL2 K)) :=
        Subgroup.subset_closure (by simp)
      have hτmem : τ ∈ Subgroup.closure ({t, β, τ} : Set (PGL2 K)) :=
        Subgroup.subset_closure (by simp)
      rw [hc_def]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ hβmem hτmem) (Subgroup.inv_mem _ hβmem)
  refine ⟨τ, hτJ, hτodd, hτinv, ?_⟩
  rw [← hKJe]
  exact hgen

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
