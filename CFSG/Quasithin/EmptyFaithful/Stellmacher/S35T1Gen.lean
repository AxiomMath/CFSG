module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T1Cent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T1Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T1

open S35.Std S35.II S35.Fin S35.Ch2 S35.Ch

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

omit [Finite G] in
theorem Xg_le_normalizer : Xg γ' m ≤ Subgroup.normalizer (Zv m : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le_normalizer _)

theorem Xg_le_sup (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ')
    (hW : ∀ w ∈ Wb β, ∀ z ∈ Zv α', ⁅w, z⁆ = 1) (hWm : ¬ Wb β ≤ stab m)
    {Q' : Subgroup G} (hQm : Q' ≤ Qv m) (hN : Qv γ' ⊓ Qv m ≤ Q')
    (hT : That2 γ' m ≤ Q' ⊔ Qv γ') : Xg γ' m ≤ Wb β ⊔ Q' := by
  obtain ⟨hm3, hγ5, hne, -, -⟩ := back_facts hp hb
  have hγm : γ' ∈ nbrs m := hb.2.1
  have hm : m ∈ nbrs γ' := mem_nbrs_symm.mp hγm
  obtain ⟨c⟩ := exists_chart2 hS hγ5 (δ := γ')
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hm
  have hWX := Wb_le_Xg hS hp hb hW
  have hQX : Q' ≤ Xg γ' m := hQm.trans (Qv_le_Xg hS hγm)
  have hSX : Wb β ⊔ Q' ≤ Xg γ' m := sup_le hWX hQX
  have hQs : Q' ≤ stab γ' := hQm.trans (Qv_le_stab hS hγm)
  have hTK : That (c.Dl m) ≤ c.bar (Wb β ⊔ Q') := by
    intro τ hτ
    rw [← c.bar_That2' hS hγ5 hm] at hτ
    obtain ⟨t, ht, rfl⟩ := (c.mem_bar_iff).mp hτ
    have ht' : (t : G) ∈ Qv γ' ⊔ Q' := by
      rw [sup_comm]
      exact hT ht
    have hnorm : Q' ≤ Subgroup.normalizer (Qv γ' : Set G) :=
      hQs.trans (le_normalizer_pCoreOf 2 (stab γ'))
    obtain ⟨a, ha, b, hb', hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp ht'
    have hbs : b ∈ stab γ' := hQs hb'
    have has : a ∈ stab γ' := Qv_le_stab' γ' ha
    have h1 : c.θ t = c.θ ⟨b, hbs⟩ := by
      have : t = ⟨a, has⟩ * ⟨b, hbs⟩ := Subtype.ext hab
      rw [this, map_mul, (c.ker_iff hS hγ5 ⟨a, has⟩).mpr ha, one_mul]
    rw [h1]
    exact c.mem_bar_of_mem (Subgroup.mem_sup_right hb') hbs
  have hKp : c.bar (Wb β ⊔ Q') ≤ ptStab (fixPt (c.Dl m)) := by
    intro σ hσ
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
    have hmem : (a : G) ∈ Mbl γ' m := ⟨Xg_le_normalizer (hSX ha), a.2⟩
    exact (c.mem_preθ_iff a).mp (c.Mbl_le_preθ hS hγ5 hm hmem)
  have hKD : ¬ c.bar (Wb β ⊔ Q') ≤ c.Dl m := by
    intro hle
    apply hWm
    intro w hw
    have hws : w ∈ stab γ' := Wb_le_stab hS hp hb hw
    have h1 := hle (c.bar_mono (le_sup_left (b := Q')) (c.mem_bar_of_mem hw hws))
    have h2 : w ∈ c.preθ (c.Dl m) := (c.mem_preθ_iff ⟨w, hws⟩).mpr h1
    rw [c.preθ_Dl hS hγ5 hm] at h2
    exact h2.2
  have hP := ptStab_le_of_That_le hD hTK hKp hKD
  intro x hx
  have hxs : x ∈ stab γ' := (mem_Xg.mp hx).1
  have hθ : c.θ ⟨x, hxs⟩ ∈ c.bar (Wb β ⊔ Q') := by
    refine hP ?_
    have hmem : x ∈ Mbl γ' m := ⟨Xg_le_normalizer hx, hxs⟩
    exact (c.mem_preθ_iff ⟨x, hxs⟩).mp (c.Mbl_le_preθ hS hγ5 hm hmem)
  obtain ⟨y, hy, hyθ⟩ := (c.mem_bar_iff).mp hθ
  have hn : (x : G) * (y : G)⁻¹ ∈ Qv γ' := by
    refine (c.ker_iff hS hγ5 (⟨x, hxs⟩ * y⁻¹)).mp ?_
    rw [map_mul, map_inv, hyθ, mul_inv_cancel]
  have hnX : (x : G) * (y : G)⁻¹ ∈ Xg γ' m := (Xg γ' m).mul_mem hx ((Xg γ' m).inv_mem (hSX hy))
  have hnm : (x : G) * (y : G)⁻¹ ∈ Qv m := Xg_inf_Qv_le hS hm3 hγm ⟨hnX, hn⟩
  have hnQ : (x : G) * (y : G)⁻¹ ∈ Q' := hN ⟨hn, hnm⟩
  have : x = ((x : G) * (y : G)⁻¹) * (y : G) := by group
  rw [this]
  exact (Wb β ⊔ Q').mul_mem (Subgroup.mem_sup_right hnQ) hy

end S35.T1

end F53.Stellmacher

end CFSG.Quasithin
