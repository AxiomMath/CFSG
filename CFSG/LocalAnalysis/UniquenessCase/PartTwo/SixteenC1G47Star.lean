module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Base
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_pCore_bar (K : Subgroup G) : CFSG.pCore 2 (Bar2 K) = ⊥ :=
  CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥K) (p := 2)

theorem s16c1_G47_pRank_bar (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 H)) = CFSG.Open.pRank p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥H) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(CFSG.pCore 2 ↥H))).1
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
    intro hdvd
    have h2 : p ∣ 2 ^ n := hn ▸ hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
  exact CFSG.SectionRank.pRank_quotient_eq (p := p) (G := ↥H) (CFSG.pCore 2 ↥H) hnd

theorem s16c1_G47_xInf_le (L : Subgroup G) (z : G) :
    xInf L z ≤ centralizer ({z} : Set G) ⊓ L :=
  perfectCore_le _

theorem s16c1_G47_yGen_le (L : Subgroup G) (z : G) : yGen L z ≤ centralizer ({z} : Set G) := by
  rw [yGen, hConjClosure]
  refine iSup_le fun k => ?_
  calc conjSubgroup (xInf L z) (k : G)
      ≤ conjSubgroup (centralizer ({z} : Set G)) (k : G) :=
        E3.conjSubgroup_mono_left (k : G) (inf_le_left.trans' (s16c1_G47_xInf_le L z))
    _ = centralizer ({z} : Set G) :=
        (conjSubgroup_eq_iff_mem_normalizer (A := centralizer ({z} : Set G)) (g := (k : G))).2
          (Subgroup.le_normalizer k.2)

theorem s16c1_G47_yGen_normal (L : Subgroup G) (z : G) :
    ((yGen L z).subgroupOf (centralizer ({z} : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ yGen L z := Subgroup.mem_subgroupOf.1 hn
  have hinv := s16c1_conjSubgroup_hConjClosure (z := z) (xInf L z) g.2
  have : (n : G) ∈ conjSubgroup (yGen L z) (g : G) := by
    simpa only [yGen] using (hinv.symm ▸ hn' : (n : G) ∈ conjSubgroup (hConjClosure z (xInf L z)) g)
  exact Subgroup.mem_subgroupOf.2 (mem_conjSubgroup_iff.1 this)

theorem s16c1_G47_starImg_conj {H K V : Subgroup G} (hKH : K ≤ H)
    (hKV : K ≤ normalizer (V : Set G)) {b v : Bar2 H} (hb : b ∈ starImg H K)
    (hv : v ∈ starImg H V) : b * v * b⁻¹ ∈ starImg H V := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.1 hw
  refine Subgroup.mem_map.2 ⟨k * w * k⁻¹, ?_, by simp [map_mul, map_inv]⟩
  refine Subgroup.mem_subgroupOf.2 ?_
  have : (k : G) * (w : G) * (k : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hKV hkK) w).1 hwV
  simpa using this

theorem s16c1_G47_starImg_sq {H V : Subgroup G} (hV : IsElemAbelian 2 V) :
    (∀ v ∈ starImg H V, v * v = 1) ∧ IsPGroup 2 (starImg H V) := by
  have hsq : ∀ v ∈ starImg H V, v * v = 1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hv
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.1 hw
    have h2 : (w : G) ^ 2 = 1 := hV.2 (w : G) hwV
    have hw2 : w * w = 1 := by
      apply Subtype.ext
      simpa [pow_two] using h2
    rw [← map_mul, hw2, map_one]
  refine ⟨hsq, fun g => ⟨1, ?_⟩⟩
  apply Subtype.ext
  simpa [pow_two] using hsq g.1 g.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
