module

public import Certificates.Certificate5186
public import Certificates.Certificate5187
public import CFSG.Sporadic.Recognition.McLASEnum
public import CFSG.Sporadic.Recognition.McLNoThree
public import CFSG.Sporadic.Recognition.McLNoThreeTransport
public import CFSG.Sporadic.SmallOddCore.McL

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier.PairNative

theorem mclNoThreeNormalized_of_certs :
    McLNoThreeNormalized := by
  obtain ⟨hsub, -⟩ := Certificates.certificate5186
  have F := subEnumOK_spec mcl_groupData hsub
  set S₀ := closure (tp 275 '' {x | x ∈ sylTwoGens})
  intro Q _ hQ S hS W hW hn
  obtain ⟨e⟩ := hQ
  have hP : Nat.card ↥mclP = 898128000 := card_mclP
  have : Finite ↥mclP := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  refine noThree_of_normalizer (P := ↥mclP) (S₀ := S₀.subgroupOf mclP) hP ?_ ?_
    (e.trans mclPermEquiv) hS hW hn
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe F.le).toEquiv, F.card]
    norm_num
  · intro V hV hnV
    rw [← Subgroup.map_eq_bot_iff_of_injective V (f := mclP.subtype) Subtype.val_injective]
    refine Certificates.certificate5187 _ (Subgroup.map_subtype_le V) (hV.map _) ?_
    intro a ha
    have haN := hnV ((Subgroup.mem_subgroupOf (h := (⟨a, F.le ha⟩ : ↥mclP))).2 ha)
    rw [mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_map, Subgroup.coe_subtype]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, (mem_normalizer_iff.1 haN v).1 hv, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      have hx : x ∈ mclP := by
        have h1 : a * x * a⁻¹ ∈ mclP := hvx ▸ v.2
        have := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem (F.le ha)) h1) (F.le ha)
        rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at this
      refine ⟨⟨x, hx⟩, (mem_normalizer_iff.1 haN ⟨x, hx⟩).2 ?_, rfl⟩
      have hv' : (⟨a, F.le ha⟩ : ↥mclP) * ⟨x, hx⟩ * (⟨a, F.le ha⟩ : ↥mclP)⁻¹ = v :=
        Subtype.ext (by simpa using hvx.symm)
      rw [hv']
      exact hv

end CFSG.Sporadic.Recognition.McLAS
