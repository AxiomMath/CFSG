module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private lemma isSwap_conj (g : Perm Ω) {s : Perm Ω} (hs : s.IsSwap) :
    (g * s * g⁻¹).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  exact ⟨g a, g b, fun h => hab (g.injective h), by rw [Equiv.swap_apply_apply]⟩

theorem eq_of_forall_isSwap_apply_eq {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤) {x y : Ω}
    (hx : ∀ t ∈ T, t.IsSwap → t x = x) (hy : ∀ t ∈ T, t.IsSwap → t y = y) : x = y := by
  by_contra hxy
  set M : Set Ω := {m | ∃ t ∈ T, t.IsSwap ∧ t m ≠ m} with hM
  set R : Subgroup (Perm Ω) := fixingSubgroup (Perm Ω) M with hR
  have hxM : x ∉ M := by
    rw [hM]
    rintro ⟨t, htT, htSwap, htx⟩
    exact htx (hx t htT htSwap)
  have hyM : y ∉ M := by
    rw [hM]
    rintro ⟨t, htT, htSwap, hty⟩
    exact hty (hy t htT htSwap)
  have hMinv : ∀ t ∈ T, ∀ m : Ω, t m ∈ M ↔ m ∈ M := by
    intro t htT m
    rw [hM]
    constructor
    · rintro ⟨s, hsT, hsSwap, hsm⟩
      refine ⟨t⁻¹ * s * t, T.mul_mem (T.mul_mem (T.inv_mem htT) hsT) htT, ?_, ?_⟩
      · simpa [inv_inv] using isSwap_conj t⁻¹ hsSwap
      · intro h
        exact hsm (by
          have := congrArg t h
          simpa [Equiv.Perm.mul_apply] using this)
    · rintro ⟨s, hsT, hsSwap, hsm⟩
      refine ⟨t * s * t⁻¹, T.mul_mem (T.mul_mem htT hsT) (T.inv_mem htT), ?_, ?_⟩
      · exact isSwap_conj t hsSwap
      · intro h
        exact hsm (by
          have := congrArg (Equiv.symm t) h
          simpa [Equiv.Perm.mul_apply] using this)
  have hTN : T ≤ Subgroup.normalizer (R : Set (Perm Ω)) := by
    intro t htT
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      rw [hR, mem_fixingSubgroup_iff] at hr
      rw [hR, mem_fixingSubgroup_iff]
      intro m hm
      have htm : t⁻¹ m ∈ M := (hMinv t⁻¹ (T.inv_mem htT) m).mpr hm
      have hrfix : r (t⁻¹ m) = t⁻¹ m := by
        simpa [Equiv.Perm.smul_def] using hr (t⁻¹ m) htm
      simp only [Equiv.Perm.smul_def, Equiv.Perm.mul_apply]
      rw [hrfix]
      simp
    · intro hr
      rw [hR, mem_fixingSubgroup_iff] at hr
      rw [hR, mem_fixingSubgroup_iff]
      intro m hm
      have htm : t m ∈ M := (hMinv t htT m).mpr hm
      have hrfix : (t * r * t⁻¹) (t m) = t m := by
        simpa [Equiv.Perm.smul_def] using hr (t m) htm
      simp only [Equiv.Perm.smul_def]
      calc r m = t⁻¹ ((t * r * t⁻¹) (t m)) := by simp [Equiv.Perm.mul_apply]
        _ = t⁻¹ (t m) := by rw [hrfix]
        _ = m := by simp
  have hswapR : Equiv.swap x y ∈ R := by
    rw [hR, mem_fixingSubgroup_iff]
    intro m hm
    rw [Equiv.Perm.smul_def]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hxM (h ▸ hm)) (fun h => hyM (h ▸ hm))
  have hN_sylow := B6.isSylowTwoOf_mono hT hTN le_top
  have hTR_sylow := B6.isSylowTwoOf_inf_normal (N := R) hN_sylow Subgroup.le_normalizer le_rfl
  have hswapSwap : (Equiv.swap x y).IsSwap := ⟨x, y, hxy, rfl⟩
  have hP : IsPGroup 2 (Subgroup.zpowers (Equiv.swap x y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hswapSwap.orderOf]
    norm_num
  obtain ⟨S, hS_sylow, hzleS⟩ :=
    B6.exists_isSylowTwoOf_ge (J := R) hP (Subgroup.zpowers_le.mpr hswapR)
  obtain ⟨g, hgR, hconj⟩ := B6.isSylowTwoOf_exists_conj hS_sylow hTR_sylow
  have hswapS : Equiv.swap x y ∈ S := hzleS (Subgroup.mem_zpowers _)
  have hgT : g * Equiv.swap x y * g⁻¹ ∈ T := by
    have hmem : g * Equiv.swap x y * g⁻¹ ∈ T ⊓ R := by
      rw [hconj, B6.mem_conjSub]
      simpa [mul_assoc] using hswapS
    exact (Subgroup.mem_inf.mp hmem).1
  have hgxy : g x ≠ g y := fun h => hxy (g.injective h)
  have hswapT : Equiv.swap (g x) (g y) ∈ T := by
    rw [Equiv.swap_apply_apply]
    exact hgT
  have hgxM : g x ∈ M := by
    rw [hM]
    exact ⟨Equiv.swap (g x) (g y), hswapT, ⟨g x, g y, hgxy, rfl⟩, by
      rw [Equiv.swap_apply_left]
      exact fun h => hgxy h.symm⟩
  have hgxNotM : g x ∉ M := by
    intro hmem
    have hgR' : g ∈ fixingSubgroup (Perm Ω) M := by rw [← hR]; exact hgR
    have hfix : g⁻¹ (g x) = g x := by
      have := Iff.mp (mem_fixingSubgroup_iff (Perm Ω))
        ((fixingSubgroup (Perm Ω) M).inv_mem hgR') (g x) hmem
      simpa [Equiv.Perm.smul_def] using this
    have hgx : g x = x := by simpa using hfix.symm
    exact hxM (hgx ▸ hmem)
  exact hgxNotM hgxM

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
