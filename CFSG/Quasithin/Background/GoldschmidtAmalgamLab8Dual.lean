module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Swap
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Lab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Ball

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7 CFSG.Quasithin.F6.GoldAmL3

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem Nm_le_ballStab_pred (h : TwoSys A B z V c V₂) (h3 : GoldHyp3 A B z V) {b : ℕ}
    (hb : critDist (A ⊔ B) A B V = b) (u : CosetGeom (A ⊔ B) A B) {n : ℕ} (hn : n + 1 ≤ b) :
    Nm A B V V₂ u ≤ ballStab n u := by
  intro x hx
  rw [mem_ballStab]
  intro w hw
  rcases Nat.eq_zero_or_pos (CosetGeom.dist u w) with h0 | hpos
  · obtain rfl : u = w := (dist_eq_zero_iff rfl).mp h0
    exact ballStab_le_stab 1 u ((goodV_all h u).nm_le hx)
  · obtain ⟨d, hd⟩ : ∃ d, CosetGeom.dist u w = d + 1 := ⟨CosetGeom.dist u w - 1, by omega⟩
    obtain ⟨v, hwv, hdv⟩ := exists_adj_dist_eq (rfl : A ⊔ B = A ⊔ B) (α := u) (δ := w) (d := d) hd
    have hxv := Nm_le_ballStab_of_dist h h3 hb u d v hdv (by omega) hx
    exact ballStab_le_stab_of_dist_le (n := 1) (γ := v) (δ := w)
      (dist_eq_one_iff_adj.mpr hwv.symm).le hxv

theorem goldHyp3_swap (d : Doubled A B z V c V₂) (h3 : GoldHyp3 A B z V)
    (hb : 4 ≤ critDist (A ⊔ B) A B V) : GoldHyp3 B A c V₂ where
  gold := h3.gold.symm
  natural := by
    have := d.sys.nat₂
    rwa [inf_comm] at this
  central := d.hc
  abelian := by
    have hA : A ≤ Subgroup.normalizer (V : Set D) := d.sys.nat.reduced.2.1
    have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := d.sys.nat₂.reduced.2.1
    refine HypF91.isElemAbelian_conjClosure_of_forall d.sys.nat₂.reduced.2.2.1 fun k hk => ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hkG : k ∈ A ⊔ B := (le_sup_left : A ≤ A ⊔ B) hk
    have hk0 : (⟨k, hkG⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B :=
      smul_γ₀_of_mem (le_sup_left : A ≤ A ⊔ B) hk
    have hadj : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B)
        ((⟨k, hkG⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B) := by
      have := (smul_adj (⟨k, hkG⟩ : ↥(A ⊔ B))).mpr (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B))
      rwa [hk0] at this
    have hle := Nm_le_ballStab_B_two d.sys h3 (b := critDist (A ⊔ B) A B V) rfl hb
      (u := γ₁ (A ⊔ B) A B) (w := γ₀ (A ⊔ B) A B)
      (m := (⟨k, hkG⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B) (by rw [vtype_smul]; rfl)
      (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm hadj
    have hv' : v ∈ Nm A B V V₂ (γ₁ (A ⊔ B) A B) := by rw [Nm_γ₁ hB]; exact hv
    have hw' : w ∈ Nm A B V V₂ ((⟨k, hkG⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B) := by
      rw [Nm_smul hA hB, Nm_γ₁ hB]; exact hw
    exact (goodV_all d.sys _).qv_cent v (hle hv') w hw'

theorem five_le_critDist_swap (d : Doubled A B z V c V₂) (h3 : GoldHyp3 A B z V)
    (hb : 5 ≤ critDist (A ⊔ B) A B V) : 5 ≤ critDist (B ⊔ A) B A V₂ := by
  have h3' := goldHyp3_swap d h3 (by omega)
  have h4 : 4 ≤ critDist (B ⊔ A) B A V₂ :=
    le_critDist_swap (h3'.gold.amalgamHypV h3'.natural) h3'.natural.natural.ne_bot (by omega)
      (by
        have := Nm_le_ballStab_pred d.sys h3 (b := critDist (A ⊔ B) A B V) rfl
          (γ₁ (A ⊔ B) A B) (n := 4) (by omega)
        rwa [Nm_γ₁ (d.sys.nat₂.reduced.2.1)] at this)
  have hne := h3'.critDist_ne_four
  omega

end GoldAmLab8

end F6

end CFSG.Quasithin
