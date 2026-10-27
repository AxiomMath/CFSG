module

public import CFSG.Quasithin.Background.F918Z8Kg5a
public import CFSG.Quasithin.Background.F918Z8Kg5b
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918Z8Kb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_alt5_false (h : LocCfg Γ Λ S V)
    (e : ↥Λ ≃* ↥(alternatingGroup (Fin 5))) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k ≤ 2) (hds : DirectSumOfCopies Λ ⊤ ⊥ (FFModel.altDn 5) k) : False := by
  obtain rfl : k = 2 := le_antisymm hk hk2
  obtain ⟨hZ, hAut⟩ := lka_out_alt5 e
  have hcard : Nat.card ↥Λ = 60 := lka_card_of_alt5 e
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  set C : Subgroup (MulAut Y) := Γ ⊓ Subgroup.centralizer (Λ : Set (MulAut Y)) with hC
  have hCmem : ∀ c, c ∈ C ↔ c ∈ Γ ∧ ∀ l ∈ Λ, c * l = l * c := by
    intro c
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact and_congr_right fun _ => ⟨fun hc l hl => (hc l hl).symm, fun hc l hl => (hc l hl).symm⟩
  have hC8 : ∀ c ∈ C, c ^ 8 = 1 := by
    intro c hc
    obtain ⟨hcΓ, hcΛ⟩ := (hCmem c).1 hc
    have h24 : c ^ 24 = 1 := lka_pow_of_comm hds c hcΛ
    refine h.hK (c ^ 8) (Γ.pow_mem hcΓ 8) (fun x hx => ?_) 3 Nat.prime_three (by norm_num)
      (by rw [hcard]; norm_num) ⟨1, ?_⟩
    · exact (Commute.pow_left (hcΛ x hx) 8).eq
    · rw [← pow_mul]
      simpa using h24
  have hCp : IsPGroup 2 ↥C := fun x => ⟨3, Subtype.ext (by simpa using hC8 x x.2)⟩
  have hkey : ∀ g ∈ Γ, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨hcΓ, hcΛ⟩ := (hCmem c).1 hc
    refine (hCmem _).2 ⟨Γ.mul_mem (Γ.mul_mem hg hcΓ) (Γ.inv_mem hg), fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ Λ := hgn g⁻¹ (Γ.inv_mem hg) l hl
    have h1 := hcΛ _ hl'
    calc g * c * g⁻¹ * l = g * (c * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * l * g⁻¹⁻¹) * c) * g⁻¹ := by rw [h1]
      _ = l * (g * c * g⁻¹) := by group
  have hnorm : Γ ≤ Subgroup.normalizer (C : Set (MulAut Y)) := fun g hg =>
    Subgroup.mem_normalizer_iff.2 fun c =>
      ⟨fun hc => hkey g hg c hc, fun hc => by
        have h1 := hkey g⁻¹ (Γ.inv_mem hg) _ hc
        have e1 : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
        rwa [e1] at h1⟩
  have hCbot : C = ⊥ := by
    have hle : C ≤ pCoreOf 2 Γ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hCp
    rw [D31.pCoreOf_eq_bot h.std.hyp] at hle
    exact le_bot_iff.1 hle
  have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem (loc_irr_data h).1
  have hSs : S ≤ stabSub V := le_stabSub_of_forall_mem (loc_S_inv h)
  have hΓs : ∀ g ∈ Γ, g ∈ stabSub V := by
    intro g hg
    obtain ⟨c, hcΓ, hcΛ, x, hx, rfl⟩ := loc_mul_cent h hZ hAut g hg
    have hcC : c ∈ C := (hCmem c).2 ⟨hcΓ, hcΛ⟩
    rw [hCbot, Subgroup.mem_bot] at hcC
    rw [hcC, one_mul]
    exact (sup_le hLs hSs) hx
  apply h.ne
  rw [eq_top_iff, ← h.std.hyp.gen]
  exact iSup₂_le fun g hg => (map_eq_of_mem_stabSub (hΓs g hg)).le

end CFSG.Quasithin
