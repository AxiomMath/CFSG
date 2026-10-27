module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yd
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL2
import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_mk_mem_map_iff {L : Subgroup G} (Q : Sylow 2 ↥L) (l : ↥L) :
    (QuotientGroup.mk l : Bar2 L) ∈ (Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ↔
      l ∈ (Q : Subgroup ↥L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈ _ ↔ _
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.2 (CFSG.fitting_pCore_le_sylow Q)]

theorem uc22ine229_exists_mem_normalizer_of_concl {L T₀ : Subgroup G}
    (hT₀L : T₀ ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T₀ ⊓ L) L) {n s r : ℕ} (hn : n ≠ 0)
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    (hC : ∀ U : Sylow 2 (Bar2 L), (∀ (g : ↥T₀) (x : Bar2 L),
        x ∈ (U : Subgroup (Bar2 L)) ↔ uc22pwIndHom L T₀ hT₀L g x ∈ (U : Subgroup (Bar2 L))) →
      ∀ e m' : ℕ, Odd m' → n = 2 ^ e * m' →
        uc22pwlie_Concl uc22pwr1_shape (Bar2 L) U ↥T₀ (uc22pwIndHom L T₀ hT₀L) n m') :
    ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (T₀ : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, hQ⟩ := hS
  obtain ⟨U, hU⟩ : ∃ U : Sylow 2 (Bar2 L), ∀ l : ↥L,
      (QuotientGroup.mk l : Bar2 L) ∈ (U : Subgroup (Bar2 L)) ↔ (l : G) ∈ T₀ := by
    refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)), fun l => ?_⟩
    rw [Sylow.coe_mapSurjective, uc22ine229_mk_mem_map_iff, ← mem_map_iff_mem L.subtype_injective,
      hQ, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, l.2⟩⟩
  have hψ : ∀ (g : ↥T₀) (x : Bar2 L),
      x ∈ (U : Subgroup (Bar2 L)) ↔ uc22pwIndHom L T₀ hT₀L g x ∈ (U : Subgroup (Bar2 L)) := by
    intro g x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [uc22pwIndHom_apply, uc22p20uInd_mk, hU, hU]
    exact mem_normalizer_iff.1 (le_normalizer g.2) l
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hC' := hC U hψ e m' hm' hnem
  unfold uc22pwlie_Concl at hC'
  obtain ⟨E, -, ⟨hcyc, -, -⟩, hpi, -, hα, -⟩ := hC'
  haveI := hcyc
  have hsm : s ∣ m' :=
    (Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hs)).dvd_of_dvd_mul_left (hnem ▸ hsn)
  have hrm : r ∣ 2 ^ m' - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsm)
  have hrE : r ∣ Nat.card E := by
    have h : r ∈ etaSet n := ⟨hr, hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)⟩
    rw [← hpi] at h
    exact h.2
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) r hrE
  obtain ⟨xbar, hxo, hxα⟩ : ∃ xbar : Bar2 L, orderOf xbar = r ∧
      xbar ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E := by
    refine ⟨xb, by rw [Subgroup.orderOf_coe, hxb],
      uc22pwtb_mem_oPi IsCyclic.isMulCommutative xb.2 fun p hp hpd => ⟨hp, ?_⟩⟩
    rw [Subgroup.orderOf_coe, hxb] at hpd
    rwa [(Nat.prime_dvd_prime_iff_eq hp hr).1 hpd]
  have key : ∀ z : ↥L, (QuotientGroup.mk z : Bar2 L) ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E →
      ∀ h ∈ T₀, (z : G) * h * (z : G)⁻¹ ∈ T₀ := by
    intro z hz h hh
    have h1 := hα ⟨h⁻¹, inv_mem hh⟩ _ hz
    rw [uc22pwIndHom_apply, uc22p20uInd_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      hU] at h1
    have e1 : (z : G) * h * (z : G)⁻¹ = h * (h⁻¹ * z * h⁻¹⁻¹ * (z : G)⁻¹) := by group
    rw [e1]
    exact mul_mem hh (by simpa using h1)
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xbar
  have hx₀r : x₀ ^ r ∈ CFSG.pCore 2 ↥L := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_pow, ← hxo, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hx₀r⟩
  have hc' : (x₀ ^ r) ^ 2 ^ c = 1 := congrArg Subtype.val hc
  have hodd : Odd (2 ^ s - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hs.pos.ne'⟩) odd_one
  have hcop : (orderOf (QuotientGroup.mk x₀ : Bar2 L)).Coprime (2 ^ c) := by
    rw [hxo]
    exact (Nat.Coprime.coprime_dvd_left hrs (Nat.coprime_two_right.2 hodd)).pow_right c
  have hmk : orderOf (QuotientGroup.mk (x₀ ^ 2 ^ c) : Bar2 L) = r := by
    rw [QuotientGroup.mk_pow, hcop.orderOf_pow, hxo]
  obtain ⟨y, hyo, hyα⟩ : ∃ y : ↥L, orderOf y = r ∧
      (QuotientGroup.mk y : Bar2 L) ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E := by
    refine ⟨x₀ ^ 2 ^ c, Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_, ?_⟩
    · rw [← pow_mul, mul_comm (2 ^ c), pow_mul, hc']
    · rw [← hmk]
      exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) _
    · rw [QuotientGroup.mk_pow]
      exact pow_mem hxα _
  refine ⟨y, y.2, by rw [Subgroup.orderOf_coe, hyo],
    mem_normalizer_iff.2 fun h => ⟨key y hyα h, fun hh => ?_⟩⟩
  have h1 := key y⁻¹ (by rw [QuotientGroup.mk_inv]; exact inv_mem hyα) _ hh
  rwa [Subgroup.coe_inv,
    show (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G)⁻¹⁻¹ = h by group] at h1

theorem uc22ine229_exists_mem_normalizer_of_isL2 {L T₀ : Subgroup G} (hT₀ : IsPGroup 2 T₀)
    (hT₀L : T₀ ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T₀ ⊓ L) L) {n s r : ℕ}
    (hX : IsL2 (Bar2 L) n) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (T₀ : Set G) :=
  uc22ine229_exists_mem_normalizer_of_concl hT₀L hS
    (by have := (CFSG.Blueprint.LieModel.admissible hX).2.1; omega) hs hsn hr hrs
    fun U hψ _ _ hm' hnem => uc22pwr1_concl_of_isL2 hX U hT₀ _ hψ hm' hnem

theorem uc22ine229_exists_mem_normalizer_of_isSz {L T₀ : Subgroup G}
    (hT₀ : IsPGroup 2 T₀) (hT₀L : T₀ ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T₀ ⊓ L) L)
    {n s r : ℕ} (hX : IsSz (Bar2 L) n) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) : ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (T₀ : Set G) :=
  uc22ine229_exists_mem_normalizer_of_concl hT₀L hS
    (by have := (CFSG.Blueprint.LieModel.admissible hX).2.1; omega) hs hsn hr hrs
    fun U hψ _ _ hm' hnem => uc22pwr1_concl_of_isSz hX U hT₀ _ hψ hm' hnem

theorem uc22ine229_exists_mem_normalizer_of_isSU3
    {L T₀ : Subgroup G}
    (hT₀ : IsPGroup 2 T₀) (hT₀L : T₀ ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T₀ ⊓ L) L)
    {n s r : ℕ} (hX : IsSU3 (Bar2 L) n) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) : ∃ x ∈ L, orderOf x = r ∧ x ∈ normalizer (T₀ : Set G) := by
  have hn : n ≠ 0 := by have := (CFSG.Blueprint.LieModel.admissible hX.2).2.1; omega
  have h2n : 2 < n := by
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hsn
    obtain ⟨j, rfl⟩ := hs
    rcases j with _ | j
    · norm_num at hrs
      exact absurd hrs hr.ne_one
    · omega
  refine uc22ine229_exists_mem_normalizer_of_concl hT₀L hS hn hs hsn hr hrs
    fun U hψ e m' hm' hnem => ?_
  obtain ⟨E, h1, h2, h3, h4, h5⟩ :=
    uc22pwCartanSU3_holds (Bar2 L) hX.1 n h2n hX U ↥T₀ hT₀ _ hψ e m' hm' hnem
  exact ⟨E, h1, ⟨h2, h3, h4⟩, h5⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
