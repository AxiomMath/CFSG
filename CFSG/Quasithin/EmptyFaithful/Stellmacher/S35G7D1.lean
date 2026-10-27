module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even16A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.D

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Wb_smul (g : ↥(H ⊔ M)) (β : Geo H M) : Wb (g • β) = conjSub (g : G) (Wb β) := by
  unfold Wb
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = g • ρ' := ⟨g⁻¹ • ρ, by simp⟩
    have hρ' : dist ρ' β = 2 := by rwa [CosetGeom.dist_smul] at hρ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (ρ : Geo H M) (_ : dist ρ β = 2) => Vn ρ)
      ρ' hρ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun ρ hρ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (ρ : Geo H M) (_ : dist ρ (g • β) = 2) => Vn ρ) (g • ρ)
      (by rwa [CosetGeom.dist_smul]) le_rfl

omit [Finite G] in
theorem isSec_conj {X L N : Subgroup G} (g : G) (hs : IsSec X L N) :
    IsSec (conjSub g X) (conjSub g L) (conjSub g N) where
  le := conjSub_mono _ hs.le
  normN := by
    intro x hx
    rw [mem_conjSub] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSub, mem_conjSub]
    have h := Subgroup.mem_normalizer_iff.mp (hs.normN hx) (g⁻¹ * y * g)
    have e : g⁻¹ * (x * y * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e]
    exact h
  normL := by
    intro x hx
    rw [mem_conjSub] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSub, mem_conjSub]
    have h := Subgroup.mem_normalizer_iff.mp (hs.normL hx) (g⁻¹ * y * g)
    have e : g⁻¹ * (x * y * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e]
    exact h
  comm := by
    intro x hx y hy
    rw [mem_conjSub] at hx hy ⊢
    have h := hs.comm _ hx _ hy
    have e : g⁻¹ * (x * y * x⁻¹ * y⁻¹) * g =
        (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact h
  sq := by
    intro x hx
    rw [mem_conjSub] at hx ⊢
    have h := hs.sq _ hx
    have e : g⁻¹ * x ^ 2 * g = (g⁻¹ * x * g) ^ 2 := by rw [pow_two, pow_two]; group
    rw [e]
    exact h

omit [Finite G] in
theorem transv_smul (g : ↥(H ⊔ M)) {β : Geo H M} (hs : IsSec (stab β) (Vn β) (Wb β)) {x : G}
    (hx : x ∈ stab β) (hxQ : x ∉ Qv β) (h2 : secIdx (Subgroup.zpowers x) (Vn β) (Wb β) = 2) :
    IsSec (stab (g • β)) (Vn (g • β)) (Wb (g • β)) ∧ (g : G) * x * (g : G)⁻¹ ∈ stab (g • β) ∧
      (g : G) * x * (g : G)⁻¹ ∉ Qv (g • β) ∧
      secIdx (Subgroup.zpowers ((g : G) * x * (g : G)⁻¹)) (Vn (g • β)) (Wb (g • β)) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stab_smul, Vn_smul, Wb_smul]
    exact isSec_conj _ hs
  · rw [stab_smul]
    exact mul_mem_conjSub hx
  · rw [Qv_smul, mem_conjSub]
    simpa [mul_assoc] using hxQ
  · rw [Vn_smul, Wb_smul, ← S43.Even.C16.conjSub_zpowers, S43.Even.C16.secIdx_conjSub]
    exact h2

end S35.G7.D

end F53.Stellmacher

end CFSG.Quasithin
