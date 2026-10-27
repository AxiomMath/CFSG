module

public import CFSG.Quasithin.H13.AS91Sec6Inter

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Monster.Code
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem G3_eq_SM : c.G3 = c.S.M := by
  change centralizer ({z} : Set G) = centralizer ({c.S.z} : Set G)
  rw [c.S_z]

theorem conj_mem_Q {h : G} (hh : h ∈ c.G3) {q : G} (hq : q ∈ Q z) : h * q * h⁻¹ ∈ Q z := by
  have hQG : c.S.QG = Q z := c.S_QG
  rw [← hQG] at hq ⊢
  exact c.S.conj_mem_QG (c.G3_eq_SM ▸ hh) hq

theorem Q_le_G13 : Q z ≤ c.G13 := fun _ hq => c.QX_le (Subgroup.mem_sup_left hq)

theorem Q_le_G1 : Q z ≤ c.G1 := c.Q_le_G13.trans (c.G13_le_inf.trans inf_le_left)

theorem Q_le_G3 : Q z ≤ c.G3 := c.Q_le_G13.trans (c.G13_le_inf.trans inf_le_right)

end Loc49

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (r : ResM24T c)

@[expose] noncomputable def mapQ : Subgroup S24 := ((Q z).subgroupOf c.G1).map r.φ

theorem mem_mapQ {σ : S24} : σ ∈ r.mapQ ↔ ∃ q : ↥c.G1, (q : G) ∈ Q z ∧ r.φ q = σ := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, Subgroup.mem_subgroupOf.mp hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, Subgroup.mem_subgroupOf.mpr hq, rfl⟩

theorem mapQ_le : r.mapQ ≤ M24g := by
  rw [mapQ, ← r.range_eq]
  exact Subgroup.map_le_range _ _

theorem card_mapQ : Nat.card r.mapQ = 2 ^ 6 := by
  have h := c.card_map_mul_card_inf r (Q z) c.Q_le_G1
  rw [inf_comm, c.card_E_inf_Q, c.card_Qz] at h
  have h' : Nat.card ↥r.mapQ * 2 ^ 7 = 2 ^ 6 * 2 ^ 7 := by rw [mapQ, h]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem isPGroup_mapQ : IsPGroup 2 r.mapQ := IsPGroup.of_card r.card_mapQ

theorem mapQ_smul_U₀ {σ : S24} (hσ : σ ∈ r.mapQ) : σ • r.U₀ = r.U₀ := by
  obtain ⟨q, hq, rfl⟩ := (r.mem_mapQ).mp hσ
  exact (r.stab₃ q).mp (c.Q_le_G3 hq)

theorem mapQ_normal {σ : S24} (hσ : σ ∈ M24g) (hσU : σ • r.U₀ = r.U₀) {n : S24}
    (hn : n ∈ r.mapQ) : σ * n * σ⁻¹ ∈ r.mapQ := by
  obtain ⟨h, rfl⟩ := r.toResM24.exists_φ_eq hσ
  have hhG3 : (h : G) ∈ c.G3 := (r.stab₃ h).mpr hσU
  obtain ⟨q, hq, rfl⟩ := (r.mem_mapQ).mp hn
  refine (r.mem_mapQ).mpr ⟨h * q * h⁻¹, c.conj_mem_Q hhG3 hq, ?_⟩
  rw [map_mul, map_mul, map_inv]


end ResM24T

theorem le_of_injOn_commutator {G : Type*} [Group G] [Finite G] (Q E D : Subgroup G)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEQ : ∀ e ∈ E, ∀ q ∈ Q, e * q * e⁻¹ ∈ Q)
    (hD : ∀ d ∈ D, ∃ q ∈ Q, ∃ e ∈ E, d = q * e) {y : G}
    (hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D) (htriv : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Q)
    (hinj : ∀ d ∈ D, ∀ d' ∈ D, d⁻¹ * (y * d * y⁻¹) = d'⁻¹ * (y * d' * y⁻¹) → d = d') :
    D ≤ Q := by
  have hδQ : ∀ d ∈ D, d⁻¹ * (y * d * y⁻¹) ∈ Q := by
    intro d hd
    obtain ⟨q, hq, e, he, rfl⟩ := hD d hd
    have h1 : e⁻¹ * (q⁻¹ * (y * q * y⁻¹)) * e ∈ Q := by
      have := hEQ e⁻¹ (E.inv_mem he) _ (Q.mul_mem (Q.inv_mem hq) (hyQ q hq))
      simpa using this
    have h2 : e⁻¹ * (y * e * y⁻¹) ∈ Q := by
      have hcomm := hEc e⁻¹ (E.inv_mem he) (y * e * y⁻¹) (hyE e he)
      rw [hcomm]
      exact htriv e he
    have heq : (q * e)⁻¹ * (y * (q * e) * y⁻¹) =
        e⁻¹ * (q⁻¹ * (y * q * y⁻¹)) * e * (e⁻¹ * (y * e * y⁻¹)) := by group
    rw [heq]
    exact Q.mul_mem h1 h2
  let δ : ↥D → ↥D := fun d => ⟨(d : G)⁻¹ * (y * d * y⁻¹),
    D.mul_mem (D.inv_mem d.2) (hyD d d.2)⟩
  have hδinj : Function.Injective δ := by
    intro d d' h
    exact Subtype.ext (hinj d d.2 d' d'.2 (congrArg Subtype.val h))
  have hδsurj := Finite.injective_iff_surjective.mp hδinj
  intro x hx
  obtain ⟨d, hd⟩ := hδsurj ⟨x, hx⟩
  have := hδQ d d.2
  rw [show (x : G) = ((δ d : ↥D) : G) from (congrArg Subtype.val hd).symm]
  exact this

end CFSG.Quasithin.H13.AS91
