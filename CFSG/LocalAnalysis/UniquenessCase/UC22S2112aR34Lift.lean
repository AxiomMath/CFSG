module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GH74.Generic.S45.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_mem_normalizer {L T₀ : Subgroup G} (hT₀ : IsPGroup 2 T₀)
    (hT₀L : T₀ ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T₀ ⊓ L) L)
    (hK : CFSG.GH74.Generic.S45.KBase (Bar2 L)) :
    ∃ x ∈ L, orderOf x = 3 ∧ x ∈ normalizer (T₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  have hinner : ∀ g : ↥T₀, ∃ a ∈ (U : Subgroup (Bar2 L)),
      ∀ x : Bar2 L, uc22pwIndHom L T₀ hT₀L g x = a * x * a⁻¹ := by
    intro g
    obtain ⟨k, hk⟩ := hT₀ g
    have hψk : (uc22pwIndHom L T₀ hT₀L g) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have h2 : IsPGroup 2 (zpowers (uc22pwIndHom L T₀ hT₀L g)) := by
      rw [← MonoidHom.map_zpowers]
      exact (hT₀.to_subgroup (zpowers g)).map _
    obtain ⟨a, ha⟩ := hK.2.1 _ h2
    have hconj : ∀ x : Bar2 L, uc22pwIndHom L T₀ hT₀L g x = a * x * a⁻¹ := fun x => by
      rw [← ha, MulAut.conj_apply]
    have haN : a ∈ normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)) :=
      mem_normalizer_iff.2 fun x => by rw [hψ g x, hconj]
    have hak : a ^ 2 ^ k = 1 := by
      have hc : a ^ 2 ^ k ∈ center (Bar2 L) := by
        rw [mem_center_iff]
        intro x
        have h1 := congrArg (fun α : MulAut (Bar2 L) => α x)
          (show MulAut.conj (a ^ 2 ^ k) = 1 by rw [map_pow, ha, hψk])
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc x * a ^ 2 ^ k = a ^ 2 ^ k * x * (a ^ 2 ^ k)⁻¹ * a ^ 2 ^ k := by rw [h1]
          _ = a ^ 2 ^ k * x := by group
      rw [CFSG.OddStandard.L2Ree.kBase_center_eq_bot hK] at hc
      exact Subgroup.mem_bot.1 hc
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hak)
    have hza : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hmem : a ∈ zpowers a ⊓ normalizer (U : Set (Bar2 L)) := ⟨mem_zpowers a, haN⟩
    rw [IsPGroup.inf_normalizer_sylow hza U] at hmem
    exact ⟨a, hmem.2, hconj⟩
  obtain ⟨-, -, -, hN21⟩ := hK.2.2 U
  have h3N : 3 ∣ Nat.card (normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L))) := by
    rw [hN21]; exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(normalizer
    ((U : Subgroup (Bar2 L)) : Set (Bar2 L)))) 3 h3N
  obtain ⟨ybar, hyo, hyN⟩ : ∃ ybar : Bar2 L, orderOf ybar = 3 ∧
      ybar ∈ normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)) :=
    ⟨y, by rw [Subgroup.orderOf_coe, hy], y.2⟩
  have hα : ∀ (g : ↥T₀) (z : Bar2 L), z ∈ zpowers ybar →
      uc22pwIndHom L T₀ hT₀L g z * z⁻¹ ∈ (U : Subgroup (Bar2 L)) := by
    intro g z hz
    obtain ⟨a, haU, ha⟩ := hinner g
    have hzN : z ∈ normalizer ((U : Subgroup (Bar2 L)) : Set (Bar2 L)) :=
      (zpowers_le.2 hyN) hz
    rw [ha, show a * z * a⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) by group]
    exact mul_mem haU ((mem_normalizer_iff.1 hzN a⁻¹).1 (inv_mem haU))
  have key : ∀ z : ↥L, (QuotientGroup.mk z : Bar2 L) ∈ zpowers ybar →
      ∀ h ∈ T₀, (z : G) * h * (z : G)⁻¹ ∈ T₀ := by
    intro z hz h hh
    have h1 := hα ⟨h⁻¹, inv_mem hh⟩ _ hz
    rw [uc22pwIndHom_apply, uc22p20uInd_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      hU] at h1
    have e1 : (z : G) * h * (z : G)⁻¹ = h * (h⁻¹ * z * h⁻¹⁻¹ * (z : G)⁻¹) := by group
    rw [e1]
    exact mul_mem hh (by simpa using h1)
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective ybar
  have hx₀r : x₀ ^ 3 ∈ CFSG.pCore 2 ↥L := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_pow, ← hyo, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hx₀r⟩
  have hc' : (x₀ ^ 3) ^ 2 ^ c = 1 := congrArg Subtype.val hc
  have hcop : (orderOf (QuotientGroup.mk x₀ : Bar2 L)).Coprime (2 ^ c) := by
    rw [hyo]
    exact (Nat.coprime_two_right.2 (by decide)).pow_right c
  have hmk : orderOf (QuotientGroup.mk (x₀ ^ 2 ^ c) : Bar2 L) = 3 := by
    rw [QuotientGroup.mk_pow, hcop.orderOf_pow, hyo]
  obtain ⟨w, hwo, hwα⟩ : ∃ w : ↥L, orderOf w = 3 ∧
      (QuotientGroup.mk w : Bar2 L) ∈ zpowers (QuotientGroup.mk x₀ : Bar2 L) := by
    refine ⟨x₀ ^ 2 ^ c, Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_, ?_⟩
    · rw [← pow_mul, mul_comm (2 ^ c), pow_mul, hc']
    · rw [← hmk]
      exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) _
    · rw [QuotientGroup.mk_pow]
      exact pow_mem (mem_zpowers _) _
  refine ⟨w, w.2, by rw [Subgroup.orderOf_coe, hwo],
    mem_normalizer_iff.2 fun h => ⟨key w hwα h, fun hh => ?_⟩⟩
  have h1 := key w⁻¹ (by rw [QuotientGroup.mk_inv]; exact inv_mem hwα) _ hh
  rwa [Subgroup.coe_inv,
    show (w : G)⁻¹ * ((w : G) * h * (w : G)⁻¹) * (w : G)⁻¹⁻¹ = h by group] at h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
