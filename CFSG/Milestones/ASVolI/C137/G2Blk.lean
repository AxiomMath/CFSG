module

public import CFSG.Milestones.ASVolI.C137.Gen
public import CFSG.Quasithin.H13.GoldschmidtC137Bridge

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.H13 (ModQ g2QAct g2QAct_injective)

variable {G : Type} [Group G]

theorem burnsideC137_derived_faithful (δ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆)
    (h : ∀ m : ↥(zornO0 (ZMod 2)),
      (QuotientGroup.mk (s := (zornR (ZMod 2)).subgroupOf (zornO0 (ZMod 2)))
        ⟨zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ δ m,
          zornAct_mem_O0 _ (Subgroup.commutator_le_self _) δ m.2⟩ : ModQ) =
        QuotientGroup.mk m) : δ = 1 := by
  have h1 : g2QAct (ZMod 2) ⟨δ.1, Subgroup.commutator_le_self _ δ.2⟩ = 1 := by
    ext q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact h m
  have h2 := g2QAct_injective (h1.trans (map_one _).symm)
  exact Subtype.ext (by simpa using congrArg Subtype.val h2)

theorem burnsideC137_isG2TwoBlockNatural {L : Subgroup G} (hB : IsG2Block L) :
    IsG2TwoBlockNatural L := by
  obtain ⟨hshort, -, -, α, hαs, hαk, β, hβs, hβk, hβ⟩ := id hB
  have hD := FFModel.zornQ_isActionModel ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
    (Subgroup.commutator_le_self _)
  have hLU : L ≤ normalizer (blockU L : Set G) := H13.U3.GC137.le_normalizer_blockU L
  have hLZ : L ≤ normalizer (blockZ L : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hLU hx) y
    have h2 := Subgroup.mem_normalizer_iff.1
      (burnsideC137_mem_normalizer_centralizer (L := L) (Subgroup.le_normalizer hx)) y
    simp only [blockZ, Subgroup.mem_inf]
    rw [h1, h2]
  have hQU : ∀ x : ↥L, x ∈ CFSG.pCore 2 ↥L → (x : G) ∈ centralizer (blockU L : Set G) := by
    intro x hx
    have hxQ : (x : G) ∈ blockQ L := ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 (hshort.2.2.1.1 hu).2 x hxQ).symm
  have hCQ : ∀ x : ↥L, (x : G) ∈ centralizer (blockU L : Set G) → x ∈ CFSG.pCore 2 ↥L := by
    intro x hx
    rw [← hαk, MonoidHom.mem_ker]
    refine burnsideC137_derived_faithful (α x) fun m => ?_
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    have hc : (u : G) * x = x * u := Subgroup.mem_centralizer_iff.1 hx u u.2
    have hux : ((u : ↥(blockU L)) : G) = (x : G) * (u : G) * ((x⁻¹ : ↥L) : G) := by
      rw [Subgroup.coe_inv, ← hc, mul_inv_cancel_right]
    obtain ⟨img, himg, hβv⟩ := hβ x u u m hux hu
    have h1 : (QuotientGroup.mk img :
        ↥(zornO0 (ZMod 2)) ⧸ (zornR (ZMod 2)).subgroupOf (zornO0 (ZMod 2))) =
        QuotientGroup.mk m := hβv.symm.trans hu
    rw [← h1]
    congr 1
    exact Subtype.ext himg.symm
  refine ⟨hB, inf_le_left, le_rfl, hLU, hLZ, hD.ker_le, hD.sec_inv, hD.ker_inv, α, β, hαs, ?_,
    hβs, hβk, ?_⟩
  · have hαk' : ∀ x : ↥L, α x = 1 ↔ x ∈ CFSG.pCore 2 ↥L := fun x => by
      rw [← MonoidHom.mem_ker, hαk]
    ext x
    rw [Subgroup.mem_subgroupOf]
    change α x = 1 ↔ _
    rw [hαk']
    exact ⟨fun h => ⟨x.2, hQU x h⟩, fun h => hCQ x h.2⟩
  · intro x u v m hm huv hum
    obtain ⟨img, himg, hβv⟩ := hβ x u v m huv hum
    rw [hβv]
    congr 1
    exact Subtype.ext himg

end CFSG.ASVolI
