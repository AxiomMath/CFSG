module

public import CFSG.Quasithin.EmptyFaithful.SBc5S8Fix
public import CFSG.Quasithin.EmptyFaithful.SBc5S8Syl
public import CFSG.Quasithin.EmptyFaithful.SBd3S8Enum
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.G11.P4InspOrth

namespace SBc5S8

set_option maxRecDepth 100000

theorem gens_mem_Tstd : e1 ∈ SBd3S8.Tstd ∧ e2 ∈ SBd3S8.Tstd ∧ e3 ∈ SBd3S8.Tstd ∧ e4 ∈ SBd3S8.Tstd := by
  decide +kernel

theorem gens_mem_alt : e1 ∈ alternatingGroup (Fin 8) ∧ e2 ∈ alternatingGroup (Fin 8) ∧
    e3 ∈ alternatingGroup (Fin 8) ∧ e4 ∈ alternatingGroup (Fin 8) :=
  ⟨Equiv.Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide)),
    Equiv.Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide)),
    Equiv.Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide)),
    Equiv.Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide))⟩

theorem fix_P1 {T : Subgroup (Equiv.Perm (Fin 8))} {g : Equiv.Perm (Fin 8)}
    (hTg : T = B6.conjSub g SBd3S8.Tstd) {v : p4insporth_V8}
    (hv : ∀ p ∈ T ⊓ alternatingGroup (Fin 8), p4insporth_perm8Hom p v = v) :
    v = 0 ∨ v = p4insporth_perm8Hom g w0 := by
  have hgP : ∀ e : Equiv.Perm (Fin 8), e ∈ SBd3S8.Tstd → e ∈ alternatingGroup (Fin 8) →
      p4insporth_perm8Hom (g * e * g⁻¹) v = v := fun e he hA => by
    have hmem : g * e * g⁻¹ ∈ T := by
      rw [hTg, B6.mem_conjSub]
      simpa [mul_assoc] using he
    exact hv _ ⟨hmem, (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem e hA g⟩
  obtain ⟨t1, t2, t3, t4⟩ := gens_mem_Tstd
  obtain ⟨a1, a2, a3, a4⟩ := gens_mem_alt
  rcases fix_conj (hgP e1 t1 a1) (hgP e2 t2 a2) (hgP e3 t3 a3) (hgP e4 t4 a4) with h | h
  · left
    have h' := congrArg (p4insporth_perm8Hom g) h
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at h'
    exact h'
  · right
    have h' := congrArg (p4insporth_perm8Hom g) h
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h'
    exact h'

theorem s8_stab_isMaxParabolic2 {T : Subgroup (Equiv.Perm (Fin 8))} (hT : IsSylowTwoOf T ⊤)
    {w : p4insporth_V8} (hw : w ≠ 0) (hfix : ∀ t ∈ T, p4insporth_perm8Hom t w = w) :
    IsMaxParabolic2 (alternatingGroup (Fin 8)) (alternatingGroup (Fin 8) ⊓ s8Stab w) := by
  obtain ⟨g, -, hTg⟩ := B6.isSylowTwoOf_exists_conj SBd3S8.isSylowTwoOf_Tstd hT
  have hwg : w = p4insporth_perm8Hom g w0 := by
    rcases fix_P1 hTg (fun p hp => hfix p hp.1) with h | h
    · exact absurd h hw
    · exact h
  have hAn : B6.conjSub g (alternatingGroup (Fin 8)) = alternatingGroup (Fin 8) :=
    B6.conjSub_eq_self (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _)
  have hAn' : B6.conjSub g⁻¹ (alternatingGroup (Fin 8)) = alternatingGroup (Fin 8) :=
    B6.conjSub_eq_self (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _)
  have hinv : ∀ X : Subgroup (Equiv.Perm (Fin 8)), B6.conjSub g⁻¹ (B6.conjSub g X) = X := fun X => by
    rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hinv' : ∀ X : Subgroup (Equiv.Perm (Fin 8)), B6.conjSub g (B6.conjSub g⁻¹ X) = X := fun X => by
    rw [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]
  have hstab : s8Stab w = B6.conjSub g partStab := by
    ext σ
    rw [B6.mem_conjSub, ← s8Stab_w0, hwg, s8Stab_conj]
  have hK : alternatingGroup (Fin 8) ⊓ s8Stab w =
      B6.conjSub g (alternatingGroup (Fin 8) ⊓ partStab) := by
    rw [(B6.conjSub g).map_inf, hAn, hstab]
  have key : ∀ v : p4insporth_V8, (∀ p ∈ T ⊓ alternatingGroup (Fin 8), p4insporth_perm8Hom p v = v) →
      v = 0 ∨ v = w := fun v hv => by
    rcases fix_P1 hTg hv with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hwg.symm)
  have hnorm : ∀ x : Equiv.Perm (Fin 8), x ∈ alternatingGroup (Fin 8) →
      x ∈ Subgroup.normalizer ((T ⊓ alternatingGroup (Fin 8) : Subgroup (Equiv.Perm (Fin 8))) :
        Set (Equiv.Perm (Fin 8))) → p4insporth_perm8Hom x w = w := by
    intro x _ hxN
    have hfixu : ∀ p ∈ T ⊓ alternatingGroup (Fin 8),
        p4insporth_perm8Hom p (p4insporth_perm8Hom x w) = p4insporth_perm8Hom x w := by
      intro p hp
      have hp' : x⁻¹ * p * x ∈ T ⊓ alternatingGroup (Fin 8) := by
        refine (Subgroup.mem_normalizer_iff.1 hxN (x⁻¹ * p * x)).2 ?_
        simpa [mul_assoc] using hp
      have h1 : p4insporth_perm8Hom (x⁻¹ * p * x) w = w := hfix _ hp'.1
      rw [← LinearEquiv.mul_apply, ← map_mul, show p * x = x * (x⁻¹ * p * x) by group, map_mul,
        LinearEquiv.mul_apply, h1]
    rcases key _ hfixu with h | h
    · exfalso
      apply hw
      have h' := congrArg (p4insporth_perm8Hom x⁻¹) h
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h'
      exact h'
    · exact h
  refine ⟨⟨inf_le_left, T ⊓ alternatingGroup (Fin 8), isSylowTwoOf_inf_alt hT, ?_⟩, ?_, ?_⟩
  · rintro x ⟨hxA, hxN⟩
    exact ⟨hxA, hnorm x hxA hxN⟩
  · intro h
    apply partStab_alt_ne
    have h' : B6.conjSub g (alternatingGroup (Fin 8) ⊓ partStab) = B6.conjSub g (alternatingGroup (Fin 8)) := by
      rw [← hK, h, hAn]
    exact (B6.conjSub g).injective h'
  · intro Q hQ hQA hKQ
    have h1 : alternatingGroup (Fin 8) ⊓ partStab ≤ B6.conjSub g⁻¹ Q := by
      have := (B6.conjSub g⁻¹).monotone (hK ▸ hKQ)
      rwa [hinv] at this
    have h2 : B6.conjSub g⁻¹ Q ≤ alternatingGroup (Fin 8) := by
      have := (B6.conjSub g⁻¹).monotone hQ.1
      rwa [hAn'] at this
    rcases partStab_alt_max h1 h2 with h | h
    · rw [hK, ← h, hinv']
    · exfalso
      apply hQA
      rw [← hinv' Q, h, hAn]

end SBc5S8

end CFSG.Quasithin
