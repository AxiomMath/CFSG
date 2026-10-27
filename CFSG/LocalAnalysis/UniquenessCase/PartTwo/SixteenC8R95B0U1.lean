module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0D
public import CFSG.Open.FusionDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0E2
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenSE
import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

private lemma r95_odd_pow_mul_inv_mem {G : Type*} [Group G] {V : Subgroup G} {s v : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G)) (hs2 : s ^ 2 = 1) (hv : v ∈ V)
    {r : ℕ} (hr : Odd r) : (s * v) ^ r * s⁻¹ ∈ V := by
  obtain ⟨k, rfl⟩ := hr
  have hs_inv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hs2
  have hconj : s * v * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hs v).mp hv
  have hsq : (s * v) ^ 2 = (s * v * s⁻¹) * v := by
    rw [pow_two, hs_inv]
    group
  have hsqV : (s * v) ^ 2 ∈ V := by rw [hsq]; exact V.mul_mem hconj hv
  rw [pow_succ, pow_mul, mul_assoc]
  exact V.mul_mem (Subgroup.pow_mem V hsqV k) hconj

theorem r95_not_hasL32Quot_of_stronglyEmbedded {K : Type} [Group K] [Finite K]
    (hSE : ∀ S : Sylow 2 K, CFSG.Open.fusionStronglyEmbedded (Subgroup.normalizer ((S : Subgroup K)
    : Set K)))
    {E : Subgroup K} (hE : HasL32Quot E) : False := by
  classical
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  haveI : Finite Qm := Finite.of_surjective π hπ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm27 : LieModel Qm .PSL 2 7 1 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism Qm hm
  have hX : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo Qm :=
    CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_of_statedClassicalModel
      (hm27.statedClassicalModel (by decide))
  obtain ⟨V, s, g, hV2, _hV1, hs, hg, hg3, hg1, hsg, hs', hg', hs2⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.exists_s4_data hX
  have hsN : s ∈ Subgroup.normalizer (V : Set Qm) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    exact ⟨fun hv => hs v hv, fun hv => by
      have h1 := hs' (s * v * s⁻¹) hv
      rwa [show s⁻¹ * (s * v * s⁻¹) * s = v from by group] at h1⟩
  have hgN : g ∈ Subgroup.normalizer (V : Set Qm) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    exact ⟨fun hv => hg v hv, fun hv => by
      have h1 := hg' (g * v * g⁻¹) hv
      rwa [show g⁻¹ * (g * v * g⁻¹) * g = v from by group] at h1⟩
  obtain ⟨R₀, hR₀2, hR₀π, hfr⟩ := r95_frattini_lift π hπ 2 hV2
  obtain ⟨n_s, hn_s, v₁, hv₁, hπn_s⟩ := hfr s hsN
  obtain ⟨n_g, hn_g, v₂, hv₂, hπn_g⟩ := hfr g hgN
  have hR₀1 : R₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hR₀π
    exact _hV1 hR₀π.symm
  let R : Subgroup K := R₀.map E.subtype
  have hR2 : IsPGroup 2 R := hR₀2.map E.subtype
  have hR1 : R ≠ ⊥ := by
    intro h
    exact hR₀1 ((Subgroup.map_eq_bot_iff_of_injective (H := R₀) E.subtype_injective).mp h)
  obtain ⟨S, hRS⟩ := hR2.exists_le_sylow
  have hNB : Subgroup.normalizer (R : Set K) ≤
      Subgroup.normalizer ((S : Subgroup K) : Set K) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.normalizer_le_of_stronglyEmbedded
      S (hSE S) hR2 hR1 hRS
  let B : Subgroup K := Subgroup.normalizer ((S : Subgroup K) : Set K)
  let r : ℕ := ((S : Subgroup K).subgroupOf B).index
  haveI : ((S : Subgroup K).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl
  have hr_notdvd : ¬ 2 ∣ r := by
    intro h
    exact S.not_dvd_index
      (h.trans (Subgroup.relIndex_dvd_index_of_le (Subgroup.le_normalizer : (S : Subgroup K) ≤ B)))
  have hr_odd : Odd r := Nat.not_even_iff_odd.mp (fun he => hr_notdvd (even_iff_two_dvd.mp he))
  have hnsB : (n_s : K) ∈ B := by
    refine hNB ?_
    change (n_s : K) ∈ Subgroup.normalizer ((R₀.map E.subtype : Subgroup K) : Set K)
    exact Subgroup.le_normalizer_map E.subtype ⟨n_s, hn_s, rfl⟩
  have hngB : (n_g : K) ∈ B := by
    refine hNB ?_
    change (n_g : K) ∈ Subgroup.normalizer ((R₀.map E.subtype : Subgroup K) : Set K)
    exact Subgroup.le_normalizer_map E.subtype ⟨n_g, hn_g, rfl⟩
  have hnsS : (n_s : K) ^ r ∈ (S : Subgroup K) := by
    have h1 : (⟨(n_s : K), hnsB⟩ : ↥B) ^ ((S : Subgroup K).subgroupOf B).index ∈
        (S : Subgroup K).subgroupOf B :=
      Subgroup.pow_index_mem ((S : Subgroup K).subgroupOf B) ⟨(n_s : K), hnsB⟩
    have h2 : ((n_s : K) ^ ((S : Subgroup K).subgroupOf B).index) ∈ (S : Subgroup K) := by
      have hmem := Subgroup.mem_subgroupOf.mp h1
      simpa [Subgroup.coe_pow] using hmem
    exact h2
  let x : ↥E := n_s ^ r
  have hxS : (x : K) ∈ (S : Subgroup K) := by
    change ((n_s ^ r : ↥E) : K) ∈ (S : Subgroup K)
    rw [Subgroup.coe_pow]
    exact hnsS
  let a : Qm := π x
  let b : Qm := π n_g
  have haV : a * s⁻¹ ∈ V := by
    have ha_eq : a = (s * v₁) ^ r := by
      change π (n_s ^ r) = (s * v₁) ^ r
      rw [map_pow, hπn_s]
    rw [ha_eq]
    exact r95_odd_pow_mul_inv_mem hsN hs2 hv₁ hr_odd
  have hbV : b * g⁻¹ ∈ V := by
    have hb_eq : b = g * v₂ := by
      change π n_g = g * v₂
      exact hπn_g
    rw [hb_eq]
    exact hg v₂ hv₂
  let c_E : ↥E := x * n_g * x⁻¹ * n_g⁻¹
  let c' : Qm := π c_E
  have hc' : c' = a * b * a⁻¹ * b⁻¹ := by
    change π (x * n_g * x⁻¹ * n_g⁻¹) = π x * π n_g * (π x)⁻¹ * (π n_g)⁻¹
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hc'S : (c_E : K) ∈ (S : Subgroup K) := by
    have hcoe : (c_E : K) = (x : K) * (n_g : K) * (x : K)⁻¹ * (n_g : K)⁻¹ := by
      simp only [c_E, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, show (x : K) * (n_g : K) * (x : K)⁻¹ * (n_g : K)⁻¹
          = (x : K) * ((n_g : K) * (x : K)⁻¹ * (n_g : K)⁻¹) from by group]
    have hxinv : (x : K)⁻¹ ∈ (S : Subgroup K) := (S : Subgroup K).inv_mem hxS
    exact (S : Subgroup K).mul_mem hxS
      ((Subgroup.mem_normalizer_iff.mp hngB (x : K)⁻¹).1 hxinv)
  obtain ⟨m, hm⟩ := S.isPGroup' ⟨(c_E : K), hc'S⟩
  have hc'm : c' ^ (2 ^ m) = 1 := by
    have hE1 : c_E ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using congrArg Subtype.val hm
    change (π c_E) ^ (2 ^ m) = 1
    rw [← map_pow, hE1, map_one]
  let N : Subgroup Qm := Subgroup.normalizer (V : Set Qm)
  have haN : a ∈ N := by
    have h := N.mul_mem (Subgroup.le_normalizer haV) hsN
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h
  have hbN : b ∈ N := by
    have h := N.mul_mem (Subgroup.le_normalizer hbV) hgN
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h
  have hc'N : c' ∈ N := by
    rw [hc']
    exact N.mul_mem (N.mul_mem (N.mul_mem haN hbN) (N.inv_mem haN)) (N.inv_mem hbN)
  haveI : (V.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl
  let qq : ↥N →* (↥N ⧸ V.subgroupOf N) := QuotientGroup.mk' (V.subgroupOf N)
  let sN : ↥N := ⟨s, hsN⟩
  let gN : ↥N := ⟨g, hgN⟩
  let aN : ↥N := ⟨a, haN⟩
  let bN : ↥N := ⟨b, hbN⟩
  let cN : ↥N := ⟨c', hc'N⟩
  have hqq_a : qq aN = qq sN := by
    have hmem : aN * sN⁻¹ ∈ V.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      simpa [aN, sN] using haV
    have h1 : qq (aN * sN⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have hqq_b : qq bN = qq gN := by
    have hmem : bN * gN⁻¹ ∈ V.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      simpa [bN, gN] using hbV
    have h1 : qq (bN * gN⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have hsg_id : sN * gN * sN⁻¹ * gN⁻¹ = gN := by
    ext
    simp only [sN, gN, Subgroup.coe_mul, Subgroup.coe_inv]
    calc s * g * s⁻¹ * g⁻¹ = g⁻¹ * g⁻¹ := by rw [hsg]
      _ = g := by
        have h1 : g⁻¹ * g⁻¹ * g ^ 3 = g := by group
        rwa [hg3, mul_one] at h1
  have hc'eq : qq cN = qq gN := by
    have h_eq : cN = aN * bN * aN⁻¹ * bN⁻¹ := by
      ext
      simpa [cN, aN, bN, hc']
    calc qq cN = qq (aN * bN * aN⁻¹ * bN⁻¹) := by rw [h_eq]
      _ = qq aN * qq bN * (qq aN)⁻¹ * (qq bN)⁻¹ := by simp only [map_mul, map_inv]
      _ = qq sN * qq gN * (qq sN)⁻¹ * (qq gN)⁻¹ := by rw [hqq_a, hqq_b]
      _ = qq (sN * gN * sN⁻¹ * gN⁻¹) := by simp only [map_mul, map_inv]
      _ = qq gN := by rw [hsg_id]
  have hgV : g⁻¹ * c' ∈ V := by
    have hq : qq (gN⁻¹ * cN) = 1 := by
      rw [map_mul, map_inv, hc'eq, inv_mul_cancel]
    have hmem : gN⁻¹ * cN ∈ V.subgroupOf N := (QuotientGroup.eq_one_iff _).1 hq
    have hmem' := Subgroup.mem_subgroupOf.mp hmem
    simpa [gN, cN] using hmem'
  have hc'2 : IsPGroup 2 (Subgroup.zpowers c') :=
    IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_iff_pow_eq_one.mpr hc'm)
  have hc'zN : Subgroup.zpowers c' ≤ N := Subgroup.zpowers_le.mpr hc'N
  have hsup : IsPGroup 2 (Subgroup.zpowers c' ⊔ V : Subgroup Qm) :=
    hc'2.to_sup_of_normal_right' hV2 hc'zN
  have hgmem : g ∈ (Subgroup.zpowers c' ⊔ V : Subgroup Qm) := by
    have h1 : g = c' * (g⁻¹ * c')⁻¹ := by group
    rw [h1]
    exact (Subgroup.zpowers c' ⊔ V : Subgroup Qm).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c'))
      (Subgroup.mem_sup_right (V.inv_mem hgV))
  obtain ⟨n2, hn2⟩ := hsup ⟨g, hgmem⟩
  have hg2pow : g ^ (2 ^ n2) = 1 := by
    have := congrArg Subtype.val hn2
    simpa [Subgroup.coe_pow] using this
  have hgord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have h3dvd : 3 ∣ 2 ^ n2 := by
    rw [← hgord]
    exact orderOf_dvd_of_pow_eq_one hg2pow
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
  omega

theorem r95_gB_U3_even {Q : Type} [Group Q] [Finite Q] {f : ℕ} (hQ : LieModel Q .PSU 3 2 f)
    {E : Subgroup Q} (hE : HasL32Quot E) : False := by
  obtain ⟨-, hf1, -, hne⟩ := hQ.admissible
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hne (by norm_num)
  obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hf
    (hQ.statedClassicalModel (by decide))
  have : Finite (CFSG.Open.PSU3 2 f) := Finite.of_equiv Q e.toEquiv
  have hB := (CFSG.Open.bender_psu3_borel_full f hf).map_mulEquiv e.symm
  exact r95_not_hasL32Quot_of_stronglyEmbedded (fun S => (hB S).1) hE

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
