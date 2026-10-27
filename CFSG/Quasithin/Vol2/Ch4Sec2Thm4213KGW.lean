module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Syl
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213KG

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4

variable {G : Type} [Group G] [Finite G]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem hat_clause (hKG : KGHatA6M24He)
    (h5 : C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    ∀ z ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G),
      orderOf z = 2 →
        ¬ ⁅reducedAggregate (L ⊔ T), L⁆ ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz hz2 hVz
  obtain ⟨hK, hblk⟩ := h5
  obtain ⟨S, hS, hdir1, -⟩ := c.exists_sylow_acts
  have hVU := c.V_eq_blockU_of_isHatA6Block hblk
  obtain ⟨hzV, hzT⟩ := Subgroup.mem_inf.mp hz
  have hzS : z ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨t, ht, hts⟩ := hdir1 s hs
    have h2 : t * z * t⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp hzT t ht]
      group
    have h3 : s * z * s⁻¹ = z := (hts z hzV).trans h2
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h3]
  have hVK : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ K := c.V_le_LH.trans c.LH_le
  have hVC : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact c.V_comm _ hzV v hv
  have hle : ⁅reducedAggregate (L ⊔ T), L⁆ ≤
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
    refine le_trans (le_inf hVz (le_inf hVK hVC)) (le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => mem_normalizer_inf (le_normalizer_pCoreOf 2 _ hx.2) (Subgroup.le_normalizer hx))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left))
  rw [hVU] at hle hzV
  exact hKG G K (perfectCore (L ⊓ H)) S hK c.LH_le hblk hS z ⟨hzV, hzS⟩ hz2 hle

theorem psu_clause (hKG : KGG2BlockRu)
    (h7 : C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K)
    (hcard : Nat.card (⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) = 2 ^ 6) :
    ∃ V₃ : Subgroup G, V₃ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ ∧ Nat.card V₃ = 2 ^ 3 ∧
      T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) ∧ ¬ Subgroup.centralizer (V₃ : Set G) ≤ M := by
  obtain ⟨hK, hblk⟩ := h7
  obtain ⟨S, hS, -, hdir2⟩ := c.exists_sylow_acts
  obtain ⟨V₃, hV₃V, hV₃card, hSV₃, hCV₃⟩ := hKG G K (perfectCore (L ⊓ H)) S
    ⁅reducedAggregate (L ⊔ T), L⁆ (perfect_of_mem_cComp c.K_mem) hK c.LH_le hblk hS
    c.V_le_blockU c.LH_le_normalizer_V hcard
  refine ⟨V₃, hV₃V, hV₃card, fun t ht => ?_, fun hle => hCV₃ fun x hx => ?_⟩
  · obtain ⟨s, hs, hts⟩ := hdir2 t ht
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    rw [hts w (hV₃V hw)]
    exact (Subgroup.mem_normalizer_iff.mp (hSV₃ hs) w).mp hw
  · exact c.LH_normal ⟨le_of_mem_cComp c.K_mem hx.1, hle hx.2⟩

end Conf4212

end CFSG.Quasithin.H13.Ch4
