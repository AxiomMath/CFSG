module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLDims
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSUPos
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSpPos
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
public import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgTS_no_long_root {K : Type} [Group K] (D : UniversalRootDatum K)
    (h : D.rank = 0) (hroot : ∃ β, GGLongRoot D β) : False := by
  obtain ⟨β, w, γ₀, hγ₀, -, -⟩ := hroot
  rcases hγ₀ with ⟨w', i, -⟩ | ⟨w', i, -, -⟩ <;> exact absurd i.isLt (by omega)

private theorem irgTS_sp4_two_false
    {X : Type} [Group X] (φ : (ggU .PSp 2 1).K →* X)
    (hqs : CFSG.Assembly.IsQuasisimple ↥φ.range)
    (hk : φ.ker ≤ Subgroup.center (ggU .PSp 2 1).K) : False := by
  have hK2 : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by norm_num)
  let e : (ggU .PSp 2 1).K ≃* Equiv.Perm (Fin 6) := CFSG.SeitzReduction.F4Pilot.sp4EquivPerm hK2
  have hcen : ∀ x, x ∈ Subgroup.center (ggU .PSp 2 1).K → x = 1 := by
    intro x hx
    have hz : e x ∈ Subgroup.center (Equiv.Perm (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro w
      have h := congrArg e (hx (e.symm w))
      simpa using h
    rw [CFSG.center_perm_eq_bot_of_three_le_card (by simp)] at hz
    exact e.injective ((Subgroup.mem_bot.mp hz).trans (map_one e).symm)
  have hker : φ.ker = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr (fun x hx => hcen x (hk hx))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  haveI : Group.IsPerfect ↥φ.range := Group.isPerfect_def.2 hqs.1
  let f : ↥φ.range ≃* Equiv.Perm (Fin 6) := (MonoidHom.ofInjective hinj).symm.trans e
  haveI : Group.IsPerfect (Equiv.Perm (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  have hc : commutator (Equiv.Perm (Fin 6)) = ⊤ := Group.isPerfect_def.1 inferInstance
  have hle := Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ)
  rw [hc, top_le_iff] at hle
  have hmem : (Equiv.swap (0 : Fin 6) 1) ∈ (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ).ker := by
    rw [hle]
    exact Subgroup.mem_top _
  have h1 : Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 1) = 1 := MonoidHom.mem_ker.mp hmem
  rw [Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem irg_hyp_shape
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {t' : StatedLieTag} {m g' : ℕ} (ht' : GGPosTag t') (hg' : 1 ≤ g')
    (hroot : ∃ β : Fin (ggU t' m g').D.rank → ℤ, GGLongRoot (ggU t' m g').D β)
    (φ' : (ggU t' m g').K →* X) (hr : φ'.range = J)
    (hk : φ'.ker ≤ Subgroup.center (ggU t' m g').K) :
    StatedLieAdmissible t' m 2 g' ∨
      (t' = .F4 ∨ t' = .E6 ∨ t' = .E7 ∨ t' = .E8 ∨ t' = .twistedE6) ∨
      (t' = .PSp ∧ m = 1 ∧ 2 ≤ g') ∨ (t' = .PSU ∧ m = 2 ∧ 2 ≤ g') ∨
      (t' = .POmegaMinus ∧ (m = 2 ∨ m = 3)) ∨ (t' = .POmegaPlus ∧ m = 3) := by
  subst hr
  have hns : ¬ Group.IsSolvable ↥φ'.range := by
    intro hs
    haveI : Group.IsPerfect ↥φ'.range := ⟨hqs.1⟩
    haveI : Nontrivial ↥φ'.range := by
      haveI := hqs.2
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥φ'.range ⧸ Subgroup.center ↥φ'.range)
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨a, b, fun h => hab (by rw [h])⟩
    exact Group.IsPerfect.not_isSolvable ↥φ'.range hs
  have hsolv : Group.IsSolvable (ggU t' m g').K → False := fun h =>
    hns (Group.isSolvable_of_surjective φ'.rangeRestrict_surjective)
  rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    rcases m with _ | k
    · exfalso
      haveI : Subsingleton (ggU .PSL 0 g').K := by
        show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
        infer_instance
      exact hsolv inferInstance
    · have h1 : 1 ≤ k := CFSG.StandardType.LieKnownR2.PSL.one_le_of_not_isSolvable_psl φ' hns
      refine Or.inl ⟨Nat.prime_two, hg', by omega, ?_, ?_⟩
      · intro h
        obtain ⟨hk1, hpow⟩ := Prod.mk.inj h
        have hk1' : k = 1 := by omega
        subst hk1'
        have hK : Nat.card (GaloisField 2 g') = 2 := by
          rw [GaloisField.card 2 g' (by omega)]
          exact hpow
        haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 g')) :=
          CFSG.StandardType.isSolvable_specialLinear_of_card_eq_two (ι := Fin (1 + 1))
            (Q := GaloisField 2 g') (by simp) hK
        exact hsolv (inferInstanceAs (Group.IsSolvable
          (Matrix.SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 g'))))
      · intro h
        have h3 : 2 ^ g' = 3 := (Prod.mk.inj h).2
        rcases g' with _ | g''
        · omega
        · rw [pow_succ] at h3
          omega
  ·
    obtain ⟨hm2, hm3⟩ := CFSG.StandardType.LieKnownR2.PSU.jDim_selfDual_psu φ' hns
    by_cases h3 : 3 ≤ m
    · refine Or.inl ⟨Nat.prime_two, hg', h3, ?_⟩
      intro h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have hg2 : 2 ≤ g' := hm3 (by omega)
      have h4 : 2 ^ 2 ≤ 2 ^ g' := Nat.pow_le_pow_right (by norm_num) hg2
      omega
    · have hm : m = 2 := by omega
      subst hm
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm3 (by norm_num)⟩)))
  ·
    obtain ⟨hm1, hm2⟩ := CFSG.StandardType.LieKnownR2.PSp.jDim_sp φ' hns
    by_cases h1 : m = 1
    · subst h1
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm2 rfl⟩))
    · refine Or.inl ⟨Nat.prime_two, hg', by omega, ?_⟩
      intro h
      obtain ⟨h1', h2'⟩ := Prod.mk.inj h
      have hm2' : m = 2 := h1'
      subst hm2'
      have hg1 : g' = 1 := by
        have h5 : 2 ^ g' = 2 ^ 1 := by simpa using h2'
        exact Nat.pow_right_injective (le_refl 2) h5
      subst hg1
      exact irgTS_sp4_two_false φ' hqs hk
  ·
    by_cases h4 : 4 ≤ m
    · exact Or.inl ⟨Nat.prime_two, hg', h4⟩
    · by_cases h3 : m = 3
      · subst h3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      · exfalso
        have hnot : ¬ 3 ≤ m := by omega
        haveI : Subsingleton (ggU .POmegaPlus m g').K := by
          have hU : ggU .POmegaPlus m g' = trivialUniversal := by
            simp only [ggU, lieUniversal, hnot, ↓reduceDIte]
          rw [hU]
          show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2))
          infer_instance
        exact hsolv inferInstance
  ·
    by_cases h4 : 4 ≤ m
    · exact Or.inl ⟨Nat.prime_two, hg', h4⟩
    · by_cases h2 : 2 ≤ m
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))
      · exfalso
        exact irgTS_no_long_root (ggU .POmegaMinus m g').D (by show m - 1 = 0; omega) hroot
  · exact Or.inr (Or.inl (Or.inl rfl))
  · exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end CFSG.StandardType.RCKRP
