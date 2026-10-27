module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetSplit
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4Meet_data {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hCfg : GGConfig 3 B Bs x L D J) (hCard : Nat.card Bs = 3 ^ 5)
    (hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g))
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹) :
    J ≤ L ∧ ∃ z : ↥L, z ≠ 1 ∧ z ^ 3 = 1 ∧
      J.subgroupOf L = LargeEvenLayer (Subgroup.centralizer ({z} : Set ↥L)) ∧
      IsComponentOf (J.subgroupOf L) (Subgroup.centralizer ({z} : Set ↥L)) ∧
      (Bs ⊓ L).subgroupOf L ≤ Subgroup.centralizer ({z} : Set ↥L) ∧
      IsElemAbelian 3 ((Bs ⊓ L).subgroupOf L) ∧
      Nat.card ((Bs ⊓ L).subgroupOf L) = 3 ^ 4 := by
  obtain ⟨hcardBL, z, hzL, hzBs, hz1, hz3, hCD⟩ := ggR4Meet_split hCfg hCard hZL hInnL
  have hPre : LargeEvenStdSubPre 3 B x L D J := hCfg.2.2.1
  obtain ⟨-, -, -, -, hJD, hJC, -⟩ := hPre
  have hJz : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hCD]
    exact hJD
  have hCz : IsComponentOf J (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← hCD]
    exact hJC
  obtain ⟨hJL, hJlayer, hJcomp⟩ := ggR4Meet_transport hzL hJz hCz
  have hcomm := hCfg.2.1.2.1.1
  refine ⟨hJL, ⟨z, hzL⟩, ?_, ?_, hJlayer, hJcomp, ?_, ?_, ?_⟩
  · intro h
    exact hz1 (by simpa using congrArg Subtype.val h)
  · apply Subtype.ext
    simpa using hz3
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hyB : (y : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp hy).1
    have h : (⟨y, hyB⟩ : ↥Bs) * ⟨z, hzBs⟩ = ⟨z, hzBs⟩ * ⟨y, hyB⟩ :=
      hcomm.is_comm.comm _ _
    have h' := congrArg Subtype.val h
    simpa using h'
  · refine ⟨?_, ?_⟩
    · exact IsMulCommutative.mk (Std.Commutative.mk fun a b =>
        Subtype.ext (Subtype.ext (by
          have ha : (a : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp a.2).1
          have hb : (b : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp b.2).1
          have h : (⟨a, ha⟩ : ↥Bs) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
            hcomm.is_comm.comm _ _
          have h' := congrArg Subtype.val h
          simpa using h')))
    · intro x hx
      apply Subtype.ext
      have hxB : (x : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp hx).1
      simpa using hCfg.2.1.2.1.2 (x : G) hxB
  · have hcard := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ L ≤ L)).toEquiv
    rw [hcard, hcardBL]

end CFSG.StandardType

end
