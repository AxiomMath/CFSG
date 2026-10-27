module

public import CFSG.LocalAnalysis.StandardType.GGHalfInnerLocal
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerCommB
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

theorem exists_localR {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hK1 : GGHalfNormSL014 φ₁ φ₂) (e : ℕ)
    (he : e = 1 ∨ e = 2) :
    ∃ R : Subgroup G, ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R ∧
      (∀ r ∈ R, r * (vElt φ₁ * wElt φ₂ ^ e) = (vElt φ₁ * wElt φ₂ ^ e) * r) ∧
      (∀ r ∈ R, ∀ j ∈ J, r * j = j * r) ∧
      x ∈ R ⊔ Subgroup.zpowers (vElt φ₁ * wElt φ₂ ^ e) := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  obtain ⟨R0, hR0sub, hR0perf, hR0three, hR0comm, hR0omega⟩ := exists_local_sl24 hm e he
  let ψ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G :=
    (MulAut.conj (hElt φ₂)).toMonoidHom.comp φ₁
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply h.coords.inj₁
    apply (MulAut.conj (hElt φ₂)).injective
    show (MulAut.conj (hElt φ₂)).toMonoidHom (φ₁ a) =
        (MulAut.conj (hElt φ₂)).toMonoidHom (φ₁ b)
    simpa only [ψ, MonoidHom.comp_apply] using hab
  have hψtEps : ψ (tEps m e hm) = vElt φ₁ * wElt φ₂ ^ e := by
    show hElt φ₂ * φ₁ (tEps m e hm) * (hElt φ₂)⁻¹ = vElt φ₁ * wElt φ₂ ^ e
    exact conj_tEps h e
  have hψomega : ψ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) = wElt φ₂ := by
    have h0s : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) = 0 := by
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]
    have h1s : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) = 1 := by
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
    have h0 : tauPerm m ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc) =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
      rw [h0s, tauPerm_apply_zero m]
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_last, Fin.val_castSucc, Fin.val_mk]
    have h1 : tauPerm m ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ) =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ := by
      rw [h1s, tauPerm_apply_one m]
      apply Fin.ext
      rw [Fin.val_last, Fin.val_succ, Fin.val_mk]
    have hu : φ₁ (omegaBlock (m + 1 + 1) ⟨2, by have := h.nbr.2.2.1; omega⟩) =
        φ₂ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) := h.uElt_eq.symm
    show hElt φ₂ * φ₁ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) * (hElt φ₂)⁻¹ = wElt φ₂
    rw [hu, hElt, ← map_inv, ← map_mul, ← map_mul,
      slPerm_conj_omegaBlock (tauPerm m) h0 h1]
    rfl
  refine ⟨R0.map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator R0 R0 ψ, hR0perf]
  · rw [Subgroup.card_map_of_injective (K := R0) hψinj]
    exact hR0three
  · intro r hr
    obtain ⟨b, hb, rfl⟩ := hr
    rw [← hψtEps, ← map_mul, ← map_mul, hR0comm b hb]
  · intro r hr j hj
    obtain ⟨b, hb, rfl⟩ := hr
    change (hElt φ₂ * φ₁ b * (hElt φ₂)⁻¹) * j =
      j * (hElt φ₂ * φ₁ b * (hElt φ₂)⁻¹)
    exact conj_slOn_lt_four_comm_J h hK1 b (hR0sub hb) j hj
  · have hx : x ∈ Subgroup.zpowers (wElt φ₂) := by
      show x ∈ Subgroup.zpowers (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩))
      rw [← h.zpowers_x]
      exact Subgroup.mem_zpowers x
    have hmem : ψ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) ∈
        R0.map ψ ⊔ Subgroup.zpowers (vElt φ₁ * wElt φ₂ ^ e) := by
      have h1 : ψ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) ∈
          (R0 ⊔ Subgroup.zpowers (tEps m e hm)).map ψ :=
        Subgroup.mem_map.mpr ⟨omegaBlock (m + 1 + 1) ⟨2, by omega⟩, hR0omega, rfl⟩
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hψtEps] at h1
    rw [hψomega.symm] at hx
    exact (Subgroup.zpowers_le.mpr hmem) hx

end GGHalfCtx

end CFSG.StandardType

end
