module

public import CFSG.RankThree.PartOne.U5K.Hyp.Parabolic
public import CFSG.RankThree.PartOne.U5K.Hyp.Cyc
public import CFSG.RankThree.PartOne.U5K.Hyp.Faith
public import CFSG.RankThree.PartOne.U5K.Hyp.Facts

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

section Irr

theorem irreducible_Sh {R : Subgroup (MulAut (hypPSU hK 2 1))} (hRS : R ≤ Sh hK)
    (hN : Pi hK ⊓ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) ≤
      Subgroup.normalizer (R : Set (MulAut (hypPSU hK 2 1)))) :
    R = ⊥ ∨ R = Vh hK ∨ R = Sh hK := by
  set R' : Subgroup (hypSU hK 2 1) := Ssub hK ⊓ R.comap (innM hK) with hR'
  have hR'S : R' ≤ Ssub hK := inf_le_left
  have hL : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ r ∈ R',
      lev A hA * r * (lev A hA)⁻¹ ∈ R' := by
    intro A hA r hr
    refine ⟨lev_conj_mem_Ssub A hA hr.1, ?_⟩
    have hlP : innM hK (lev A hA) ∈ Pi hK := range_innM (hK := hK) ▸ ⟨lev A hA, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1
      (hN ⟨hlP, innM_lev_mem_normalizer_Sh A hA⟩) (innM hK r)).1 hr.2
    show innM hK (lev A hA * r * (lev A hA)⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hRim : R = R'.map (innM hK) := by
    ext ρ
    constructor
    · intro hρ
      obtain ⟨s, hs, rfl⟩ := hRS hρ
      exact ⟨s, ⟨hs, hρ⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact hs.2
  rcases irreducible_Ssub hR'S hL with h | h | h
  · left
    rw [hRim, h, Subgroup.map_bot]
  · right; left
    rw [hRim, h]
    rfl
  · right; right
    rw [hRim, h]
    rfl

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem modelFacts_hyp {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpf : p ∣ 2 ^ f + 1) :
    ModelFacts p (Pi hK) (Dlin hK) (Sh hK) (Vh hK) where
  le_inn := Sh_le_Uh.trans Uh_le_Pi
  irreducible R hRS hN := irreducible_Sh hRS hN
  core R hR2 hN := by
    have h4 : 4 ≤ 2 ^ f := by
      have := Nat.le_of_dvd (by positivity) hpf
      omega
    exact core_Sh hZ h4 hR2 fun ρ hρP hρS => hN ⟨hρP, hρS⟩
  faithful B hBN hBel hBcard := faithful_Sh hZ hp hp5 hpf hBN hBel hBcard
  cyclic P hP hPC :=
    cyclic_of_central hZ hp (by omega) hP fun ρ hρ w hw =>
      (Subgroup.mem_centralizer_iff.1 (hPC hρ) w hw).symm

end Irr

section Conj

theorem map_conj_eq_of_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (k : G) :
    N.map (MulAut.conj k).toMonoidHom = N := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have := (inferInstance : N.Normal).conj_mem _ h k
    simpa [mul_assoc] using this
  · intro h
    have := (inferInstance : N.Normal).conj_mem _ h k⁻¹
    simpa [mul_assoc] using this

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem modelFacts_sylow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpf : p ∣ 2 ^ f + 1)
    {H T : Subgroup (MulAut (hypPSU hK 2 1))} (hH : Pi hK ≤ H)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) :
    ModelFacts p (Pi hK) (Dlin hK) (pushingUpS T) (zOf (pushingUpS T)) := by
  have := finite_mulAut_hyp hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 3 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) hpf
    omega
  have hTPi : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Pi hK) (Pi hK) :=
    hT.inf_of_le_normalizer hH (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  obtain ⟨k, hkPi, hk⟩ := hTPi.exists_mem_conj (isSylow_Uh hZ)
  set θ : MulAut (MulAut (hypPSU hK 2 1)) := MulAut.conj k with hθ
  set T' : Subgroup (MulAut (hypPSU hK 2 1)) := T.map θ.toMonoidHom with hT'
  have hT'2 : IsPGroup 2 T' := (CFSG.ABGLocalTools.IsSylowOf.isPGroup hT).map _
  have hT'U : T' ⊓ Pi hK = Uh hK := by
    ext x
    constructor
    · rintro ⟨hxT, hxP⟩
      obtain ⟨t, htT, rfl⟩ := hxT
      have hx' : k⁻¹ * θ.toMonoidHom t * k = t := by
        simp [hθ, MulAut.conj_apply, mul_assoc]
      have h2 : k⁻¹ * θ.toMonoidHom t * k ∈ Pi hK := by
        simpa using (inferInstance : (Pi hK).Normal).conj_mem _ hxP k⁻¹
      refine (hk _).2 ?_
      rw [hx'] at h2 ⊢
      exact ⟨htT, h2⟩
    · intro hx
      have h1 := ((hk x).1 hx).1
      refine ⟨⟨_, h1, ?_⟩, Uh_le_Pi hx⟩
      simp [hθ, MulAut.conj_apply, mul_assoc]
  have hS' : pushingUpS T' = Sh hK := pushingUpS_eq_Sh hZ hq hT'2 hT'U
  have hinj : ∀ X : Subgroup (MulAut (hypPSU hK 2 1)),
      Function.Injective (θ.toMonoidHom.comp X.subtype) := fun X =>
    θ.injective.comp X.subtype_injective
  have hSh : (pushingUpS T).map θ.toMonoidHom = Sh hK := by
    rw [← hS']
    exact map_pushingUpS θ.toMonoidHom (hinj T)
  have hVh : (zOf (pushingUpS T)).map θ.toMonoidHom = Vh hK := by
    rw [← zOf_Sh hZ, ← hSh]
    exact map_zOf θ.toMonoidHom (hinj _)
  have hD := modelFacts_hyp (hK := hK) hZ hp hp5 hpf
  refine ModelFacts.of_map hp θ ?_
  rw [hSh, hVh, hθ, map_conj_eq_of_normal (Pi hK) k, map_conj_eq_of_normal (Dlin hK) k]
  exact hD

end Conj

end CFSG.RankThree.PartOne.U5K.Hyp
