module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.GroupTheory.CoprimeCosetFixed

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.PerfectAutomorphisms

theorem exists_fixed_lift_centerQuotient {L : Type} [Group L] [Finite L]
    (hodd : Odd (Nat.card (Subgroup.center L))) (α : MulAut L) (hα : α * α = 1)
    (x : L ⧸ Subgroup.center L) (hx : onCenterQuotient α x = x) :
    ∃ y : L, α y = y ∧ (QuotientGroup.mk y : L ⧸ Subgroup.center L) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) x
  have hfixg : (QuotientGroup.mk' (Subgroup.center L) (α g) :
      L ⧸ Subgroup.center L) = (g : L ⧸ Subgroup.center L) := by
    have h := hx
    rw [onCenterQuotient_apply_mk] at h
    exact h
  have hgZ : g⁻¹ * α g ∈ Subgroup.center L := by
    have hmem : (α g)⁻¹ * g ∈ Subgroup.center L := QuotientGroup.eq.mp hfixg
    simpa [mul_inv_rev, inv_inv] using (Subgroup.center L).inv_mem hmem
  have hN : ∀ n ∈ Subgroup.center L, α n ∈ Subgroup.center L := by
    intro n hn
    have hmap : (Subgroup.center L).map α.toMonoidHom = Subgroup.center L :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance α
    rw [← hmap]
    exact Subgroup.mem_map_of_mem α.toMonoidHom hn
  have hcop : Nat.Coprime (orderOf α) (Nat.card (Subgroup.center L)) := by
    have hdvd : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    exact (Nat.coprime_two_left.mpr hodd).coprime_dvd_left hdvd
  obtain ⟨n, hn, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime_mulAut
      (N := Subgroup.center L) α hN hgZ hcop
  refine ⟨g * n, hfix, ?_⟩
  have hmk : (QuotientGroup.mk' (Subgroup.center L) (g * n) :
      L ⧸ Subgroup.center L) = (QuotientGroup.mk' (Subgroup.center L) g :
      L ⧸ Subgroup.center L) := by
    rw [map_mul]
    simp only [QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff (N := Subgroup.center L) n).mpr hn, mul_one]
  exact hmk

theorem isInner_of_onCenterQuotient_inner {L : Type} [Group L] [Group.IsPerfect L] (α : MulAut L)
    (h : ∃ g : L ⧸ Subgroup.center L, ∀ x : L ⧸ Subgroup.center L,
      onCenterQuotient α x = g * x * g⁻¹) :
    ∃ g : L, ∀ x : L, α x = g * x * g⁻¹ := by
  obtain ⟨gBar, hgBar⟩ := h
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := Subgroup.center L) gBar
  refine ⟨g, ?_⟩
  have hconj : onCenterQuotient (MulAut.conj g) = MulAut.conj gBar := by
    ext x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) x
    rw [← hy]
    simp only [onCenterQuotient_apply_mk, MulAut.conj_apply, map_mul, map_inv]
    simp only [QuotientGroup.mk'_apply, hg]
  have hαeq : onCenterQuotient α = MulAut.conj gBar := by
    ext x
    rw [hgBar x, MulAut.conj_apply]
  have hα' : onCenterQuotient (α * (MulAut.conj g)⁻¹) = 1 := by
    have hmul : onCenterQuotient (α * (MulAut.conj g)⁻¹) =
        onCenterQuotient α * (onCenterQuotient (MulAut.conj g))⁻¹ := by
      change centerQuotientHom L (α * (MulAut.conj g)⁻¹) =
        centerQuotientHom L α * (centerQuotientHom L (MulAut.conj g))⁻¹
      rw [map_mul, map_inv]
    rw [hmul, hαeq, hconj, mul_inv_cancel]
  have hα'' : α * (MulAut.conj g)⁻¹ = 1 :=
    onCenterQuotient_eq_one_imp (α * (MulAut.conj g)⁻¹) hα'
  have hαmul : α = MulAut.conj g := mul_inv_eq_one.mp hα''
  intro x
  rw [hαmul, MulAut.conj_apply]

end CFSG.LocalAnalysis.WeakClosure81

end
