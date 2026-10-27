module

public import CFSG.Quasithin.EmptyFaithful.S143HC
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.EmptyFaithful.S143HA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Splits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.splits_kOf {A : Subgroup G} {t : G} (hb : Concl18b T M A t)
    (hK : IsA6Block (kOf T M A) A) :
    ∃ C : Subgroup G, C ≤ kOf T M A ∧ A ⊓ C = ⊥ ∧ A ⊔ C = kOf T M A := by
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq hb
  obtain ⟨C₀, hC₀le, hAC₀, hAC₀sup⟩ :=
    c.exists_complement_rOf_sup_uOfL22 hrW hrV hr2 hb.t_mem hb.t_nmem
  have hSyl := c.isSylowTwoOf_rOf_sup_uOfL22 hb hK
  set A := c.Ac hrW hrV hr2 with hAdef
  set K := kOf T M A with hKdef
  set P₀ := rOf T M ⊔ uOfL22 T M with hP₀def
  have hRT : rOf T M ≤ T := le_sup_left.trans (rq_le_of_hyp c.h1281)
  have hAR : A ≤ rOf T M := c.Ac_le_rOf hrW hrV hr2
  have hAP₀ : A ≤ P₀ := hAR.trans le_sup_left
  have hAK : A ≤ K := hAP₀.trans hSyl.le
  have hC₀K : C₀ ≤ K := hC₀le.trans hSyl.le
  have hAN : K ≤ Subgroup.normalizer (A : Set G) := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hNnormal : (A.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have hNcomm : IsMulCommutative (A.subgroupOf K) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (mul_comm_of_sq_eq_one (fun x hx => c.sq_Ac hrW hrV hr2 hx) a.2 b.2))⟩⟩
  have hA2 : IsPGroup 2 ↥A := c.hyp.sylow.1.to_le (hAR.trans hRT)
  have hN2 : IsPGroup 2 ↥(A.subgroupOf K) := hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have hP2 : IsPGroup 2 ↥(P₀.subgroupOf K) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
  let P : Sylow 2 ↥K := hP2.toSylow hSyl.2.2
  have hPeq : (P : Subgroup ↥K) = P₀.subgroupOf K := rfl
  have hNP : A.subgroupOf K ≤ (P : Subgroup ↥K) := by
    rw [hPeq]; exact Subgroup.subgroupOf_mono K hAP₀
  have hNK : A.subgroupOf K ⊓ C₀.subgroupOf K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ A ⊓ C₀ := ⟨hx.1, hx.2⟩
    rw [hAC₀, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hsup : A.subgroupOf K ⊔ C₀.subgroupOf K = (P : Subgroup ↥K) := by
    rw [hPeq]
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAK,
      Subgroup.map_subgroupOf_eq_of_le hC₀K, Subgroup.map_subgroupOf_eq_of_le hSyl.le, hAC₀sup]
  obtain ⟨D, hND, hNDsup⟩ := SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement
    Nat.prime_two hN2 P hNP hNK hsup
  refine ⟨D.map K.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, d, hd, rfl⟩
    have h1 : d ∈ A.subgroupOf K ⊓ D := ⟨hxA, hd⟩
    rw [hND, Subgroup.mem_bot] at h1
    rw [h1]
    exact (Subgroup.mem_bot).mpr rfl
  · have h1 := congrArg (Subgroup.map K.subtype) hNDsup
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAK, Subgroup.map_top,
      Subgroup.range_subtype] at h1
    exact h1

end Splits

theorem lemma_14_3_19_eight_nine :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
      Counter T M g → Concl14318 T M g A t → Concl19a T M → IsA6Block (kOf T M A) A →
        IsSylowTwoOf (rOf T M ⊔ uOfL22 T M) (kOf T M A) ∧
          ∃ C : Subgroup G, C ≤ kOf T M A ∧ A ⊓ C = ⊥ ∧ A ⊔ C = kOf T M A := by
  intro G _ _ T M g A t c c18 c19a hK
  exact ⟨c.isSylowTwoOf_rOf_sup_uOfL22 c18.b hK, c.splits_kOf c18.b hK⟩

theorem lemma14319Rest_of_parts (h4 : Lemma14319Four) (h567 : Lemma14319TenFiveSixSeven) :
    Lemma14319Rest := by
  intro G _ _ T M g A t c c18 c19a
  have hK := h4 G T M g A t c c18 c19a
  obtain ⟨h5, h6, h6', h6'', h7⟩ := h567 G T M g A t c c18 c19a hK
  obtain ⟨h8, h9⟩ := lemma_14_3_19_eight_nine G T M g A t c c18 c19a hK
  exact ⟨hK, h5, h6, h6', h6'', h7, h8, h9⟩

end S143

end CFSG.Quasithin
