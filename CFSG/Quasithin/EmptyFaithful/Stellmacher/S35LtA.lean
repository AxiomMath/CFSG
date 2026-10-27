module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Lt

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Vn_commute_nbrs (hS : Sit H M S) {l ρ σ : Geo H M} (hρ : ρ ∈ nbrs l) (hσ : σ ∈ nbrs l) :
    ∀ a ∈ Vn ρ, ∀ b ∈ Vn σ, a * b = b * a := by
  refine S34.Vn_commute hS.glob.amalg ?_
  have h1 := dist_le_dist_nbr hσ ρ
  have h2 : dist ρ l = 1 := dist_eq_one_iff_adj.mpr (Std.mem_nbrs_symm.mp hρ)
  have h3 := hS.b5
  omega

theorem Wl_comm (hS : Sit H M S) {l : Geo H M} :
    ∀ a ∈ Wl l, ∀ b ∈ Wl l, a * b = b * a := by
  have step1 : ∀ ρ ∈ nbrs l, ∀ a ∈ Vn ρ, ∀ b ∈ Wl l, a * b = b * a := by
    intro ρ hρ a ha b hb
    have : Wl l ≤ Subgroup.centralizer ({a} : Set G) :=
      iSup₂_le fun σ hσ c hc => by
        simpa [Subgroup.mem_centralizer_iff, eq_comm] using Vn_commute_nbrs hS hρ hσ a ha c hc
    simpa [Subgroup.mem_centralizer_iff, eq_comm] using this hb
  intro a ha b hb
  have : Wl l ≤ Subgroup.centralizer ({b} : Set G) :=
    iSup₂_le fun ρ hρ c hc => by
      simpa [Subgroup.mem_centralizer_iff, eq_comm] using step1 ρ hρ c hc b hb
  simpa [Subgroup.mem_centralizer_iff, eq_comm] using this ha

@[expose] def Dsub (x : G) (W Z : Subgroup G) (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hZ : Z ≤ W) : Subgroup G where
  carrier := {w | w ∈ W ∧ x * w * x⁻¹ * w⁻¹ ∈ Z}
  one_mem' := ⟨W.one_mem, by simp⟩
  mul_mem' := by
    rintro w₁ w₂ ⟨h₁, c₁⟩ ⟨h₂, c₂⟩
    refine ⟨W.mul_mem h₁ h₂, ?_⟩
    have e : x * (w₁ * w₂) * x⁻¹ * (w₁ * w₂)⁻¹ =
        (x * w₁ * x⁻¹ * w₁⁻¹) * (w₁ * (x * w₂ * x⁻¹ * w₂⁻¹) * w₁⁻¹) := by group
    have e2 : w₁ * (x * w₂ * x⁻¹ * w₂⁻¹) * w₁⁻¹ = x * w₂ * x⁻¹ * w₂⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul, hW _ h₁ _ (hZ c₂)]
    rw [e, e2]
    exact Z.mul_mem c₁ c₂
  inv_mem' := by
    rintro w ⟨h, c⟩
    refine ⟨W.inv_mem h, ?_⟩
    have e : x * w⁻¹ * x⁻¹ * w⁻¹⁻¹ = w⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * w := by group
    have e2 : w⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * w = (x * w * x⁻¹ * w⁻¹)⁻¹ := by
      rw [mul_assoc, ← hW _ h _ (hZ (Z.inv_mem c))]
      group
    rw [e, e2]
    exact Z.inv_mem c

omit [Finite G] in
theorem fixSecIn_le_Dsub (x : G) {W Z : Subgroup G} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hZ : Z ≤ W) : fixSecIn (Subgroup.zpowers x) Z W ≤ Dsub x W Z hW hZ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro w ⟨hw, h⟩
  exact ⟨hw, h x (Subgroup.mem_zpowers x)⟩

theorem exists_moved (hS : Sit H M S) {l : Geo H M} {x : G} (hx : x ∈ stab l) (hxQ : x ∉ Qv l) :
    ∃ ρ ∈ nbrs l, x ∉ stab ρ := by
  by_contra hne
  push Not at hne
  exact hxQ ((Std.mem_Qv_iff hS l).mpr ⟨hx, hne⟩)

theorem claimT (hS : Sit H M S) (hI : CaseI H M) : ClaimT H M := by
  intro l hl x hx hxQ
  obtain ⟨ρ, hρ, hxρ⟩ := exists_moved hS hx hxQ
  let g : ↥(H ⊔ M) := ⟨x, stab_le l hx⟩
  have hρ' : g • ρ ∈ nbrs l := Std.smul_mem_nbrs_of_stab (g := g) hx hρ
  have hne : g • ρ ≠ ρ := fun h => hxρ (mem_stab_of_smul_eq h)
  obtain ⟨hc8, hc32⟩ := hI ρ l (g • ρ) (Std.vtype_nbr_S3 hl hρ) (Std.mem_nbrs_symm.mp hρ)
    (Std.mem_nbrs_symm.mp hρ') hne
  have hZA : Zv l ≤ Vn ρ := Std.Zv_le_Vn (Std.mem_nbrs_symm.mp hρ)
  have hAW : Vn ρ ≤ Wl l :=
    le_iSup₂ (f := fun (ρ : Geo H M) (_ : ρ ∈ nbrs l) => Vn ρ) ρ hρ
  have hZW : Zv l ≤ Wl l := hZA.trans hAW
  let D := Dsub x (Wl l) (Zv l) (Wl_comm hS) hZW
  have hnz : D.relIndex (Wl l) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnzF : (fixSecIn (Subgroup.zpowers x) (Zv l) (Wl l)).relIndex (Wl l) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h1 : D.relIndex (Wl l) ≤ secIdx (Subgroup.zpowers x) (Zv l) (Wl l) := by
    refine Subgroup.relIndex_le_of_le_left (fixSecIn_le_Dsub x (Wl_comm hS) hZW) hnzF
  have h2 : D.relIndex (Vn ρ) ≤ D.relIndex (Wl l) := Subgroup.relIndex_le_of_le_right hAW hnz
  have h3 : D.relIndex (Vn ρ) * Nat.card ↥(D ⊓ Vn ρ) = Nat.card ↥(Vn ρ) :=
    Subgroup.relIndex_mul_card _ _
  have h4 : Nat.card ↥(D ⊓ Vn ρ) ≤ Nat.card ↥(Vn ρ ⊓ Vn (g • ρ)) := by
    have hmem : ∀ a ∈ D ⊓ Vn ρ, x * a * x⁻¹ ∈ Vn ρ ⊓ Vn (g • ρ) := by
      rintro a ⟨⟨_, hc⟩, ha⟩
      refine ⟨?_, ?_⟩
      · have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
        rw [e]
        exact (Vn ρ).mul_mem (hZA hc) ha
      · rw [Vn_smul]
        exact ⟨a, ha, by simp [MulAut.conj_apply, g]⟩
    refine Nat.card_le_card_of_injective
      (fun a => (⟨x * a.1 * x⁻¹, hmem a.1 a.2⟩ : ↥(Vn ρ ⊓ Vn (g • ρ)))) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have h5 : 0 < Nat.card ↥(D ⊓ Vn ρ) := Nat.card_pos
  rw [hc8] at h4
  rw [hc32] at h3
  by_contra hlt
  push Not at hlt
  have : D.relIndex (Vn ρ) ≤ 3 := by omega
  nlinarith

end S35.Lt

end F53.Stellmacher

end CFSG.Quasithin
