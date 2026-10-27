module

public import CFSG.Quasithin.EmptyFaithful.ModGRed2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.ModH

variable {G : Type} [Group G]

theorem ker_isPGroup {L I S : Subgroup G} (hLI : L ≤ I) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hIeq : I = L ⊔ S) (hS : IsPGroup 2 ↥S) (hSI : S ≤ I) (hcen : IsPGroup 2 (Subgroup.center ↥L))
    (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L)
    (hρ : ∀ l : ↥L, ρ ⟨l, hLI l.2⟩ = QuotientGroup.mk l) : IsPGroup 2 ρ.ker := by
  intro g
  obtain ⟨x, hx⟩ := g
  have hx1 : ρ x = 1 := hx
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hxmem : (x : G) ∈ L ⊔ S := hIeq ▸ x.2
  obtain ⟨p, hp, s, hs, hxe⟩ := ModG.Red.exists_mul_of_mem_sup' hSL hxmem
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hnorm : (L.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLI).2 hN
  let ψ : ↥I →* ↥I ⧸ L.subgroupOf I := QuotientGroup.mk' (L.subgroupOf I)
  have hψp : ψ ⟨p, hLI hp⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 hp
  have hxs : x = ⟨p, hLI hp⟩ * ⟨s, hSI hs⟩ := Subtype.ext hxe
  have hψx : ψ x = ψ ⟨s, hSI hs⟩ := by rw [hxs, map_mul, hψp, one_mul]
  have hsk : (⟨s, hSI hs⟩ : ↥I) ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : ↥S => ((z : ↥S) : G)) hk
    exact Subtype.ext (by simpa using this)
  have hψy : ψ (x ^ (2 ^ k)) = 1 := by rw [map_pow, hψx, ← map_pow, hsk, map_one]
  have hyL : ((x ^ (2 ^ k) : ↥I) : G) ∈ L := by
    have := (QuotientGroup.eq_one_iff _).1 hψy
    exact Subgroup.mem_subgroupOf.1 this
  have hρy : ρ (x ^ (2 ^ k)) = 1 := by rw [map_pow, hx1, one_pow]
  have hρy' : ρ ⟨((x ^ (2 ^ k) : ↥I) : G), hLI hyL⟩ = 1 := by
    have : (⟨((x ^ (2 ^ k) : ↥I) : G), hLI hyL⟩ : ↥I) = x ^ (2 ^ k) := rfl
    rw [this]; exact hρy
  rw [hρ ⟨_, hyL⟩, QuotientGroup.eq_one_iff] at hρy'
  obtain ⟨m, hm⟩ := hcen ⟨_, hρy'⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h1 := congrArg (fun z : ↥(Subgroup.center ↥L) => (((z : ↥L) : G))) hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
  rw [pow_add, pow_mul]
  show ((x ^ 2 ^ k) ^ 2 ^ m : ↥I) = 1
  apply Subtype.ext
  simpa using h1

end CFSG.Quasithin.ModH
