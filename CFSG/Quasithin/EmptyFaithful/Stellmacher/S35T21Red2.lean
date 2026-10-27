module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21Red
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

open S35.II

namespace S35.T21

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_comm {B : Subgroup G} {y : G} (h : ∀ b ∈ B, y * b = b * y) :
    y ∈ Subgroup.normalizer (B : Set G) := by
  have h1 : ∀ b ∈ B, y * b * y⁻¹ = b := fun b hb => by rw [h b hb]; group
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h1 b hb]
    exact hb
  · intro hb
    have h2 := h1 _ hb
    have h3 : y * b * y⁻¹ = b := by
      have := congrArg (fun z => y⁻¹ * z * y) h2
      simpa [mul_assoc] using this
    rw [h3] at hb
    exact hb

theorem comm_mem_Zv_of_mem_Qv_inf (hS : Sit H M S) (hII : CaseII H M) {β l δ σ : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hδ : δ ∈ nbrs l) (hσ : σ ∈ nbrs l)
    (hσδ : σ ≠ δ) {q : G} (hq : q ∈ Qv β ⊓ Qv l) {y : G}
    (hy : y ∈ Vn δ ⊓ (Vn σ ⊔ Vn β)) : q * y * q⁻¹ * y⁻¹ ∈ Zv l := by
  have hl3 : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hδ5 : vtype δ = false := Std.vtype_nbr_S3 hl3 hδ
  have hβl : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδ
  have hlσ : l ∈ nbrs σ := Std.mem_nbrs_symm.mp hσ
  have hW : ∀ ρ ∈ nbrs l, ∀ ρ' ∈ nbrs l, ∀ a ∈ Vn ρ, ∀ b ∈ Vn ρ', a * b = b * a :=
    fun ρ hρ ρ' hρ' a ha b hb => Std.Wl_comm hS l a (Std.Vn_le_Wl hρ ha) b (Std.Vn_le_Wl hρ' hb)
  obtain ⟨hqβ, hql⟩ := hq
  have hqσ : q ∈ stab σ := Std.Qv_le_stab hS hσ hql
  have hqδ : q ∈ stab δ := Std.Qv_le_stab hS hδ hql
  obtain ⟨hyδ, hyσβ⟩ := hy
  obtain ⟨s, hs, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm (hW σ hσ β hβl) hyσβ
  have hqs : q * s * q⁻¹ ∈ Vn σ :=
    (Subgroup.mem_normalizer_iff.mp (Std.Vn_normal σ hqσ) s).mp hs
  have hs' : q * s * q⁻¹ * s⁻¹ ∈ Vn σ := Subgroup.mul_mem _ hqs (Subgroup.inv_mem _ hs)
  have hb' : q * b * q⁻¹ * b⁻¹ ∈ Zv β := by
    rw [← Std.comm_Vn_Qv hS hβ, ← Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator hqβ hb
    rwa [commutatorElement_def] at this
  have hb'σ : q * b * q⁻¹ * b⁻¹ ∈ Vn σ :=
    (Std.Zv_le_Vn hlσ) (Std.Zv_le_Zv_of_nbr hS hβ hl hb')
  have hb'β : q * b * q⁻¹ * b⁻¹ ∈ Vn β := Std.Zv_le_Vn_S5 hS hβ hb'
  have hcomm : s * (q * b * q⁻¹ * b⁻¹) = (q * b * q⁻¹ * b⁻¹) * s :=
    hW σ hσ β hβl s hs _ hb'β
  have e : q * (s * b) * q⁻¹ * (s * b)⁻¹ =
      (q * s * q⁻¹ * s⁻¹) * (s * (q * b * q⁻¹ * b⁻¹) * s⁻¹) := by group
  have hmemσ : q * (s * b) * q⁻¹ * (s * b)⁻¹ ∈ Vn σ := by
    rw [e, hcomm]
    have : (q * b * q⁻¹ * b⁻¹) * s * s⁻¹ = q * b * q⁻¹ * b⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hs' hb'σ
  have hmemδ : q * (s * b) * q⁻¹ * (s * b)⁻¹ ∈ Vn δ :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (Std.Vn_normal δ hqδ) _).mp hyδ)
      (Subgroup.inv_mem _ hyδ)
  rw [← hII δ l σ hδ5 hlδ hlσ hσδ]
  exact ⟨hmemδ, hmemσ⟩

end S35.T21

end F53.Stellmacher

end CFSG.Quasithin
