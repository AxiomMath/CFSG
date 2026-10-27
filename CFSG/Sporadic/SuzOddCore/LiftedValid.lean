module

public import CFSG.Certificates.LiftedSchreierSoundness

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum

variable {n : ℕ} {K : Type*} [Group K]

theorem lift_image_of_valid {Q : RawSchreierDatum n} {φ : K →* Equiv.Perm (Fin n)}
    {U : Vector K Q.originalCount} (hQ : ValidSchreier Q)
    (horig : ∀ j : Fin Q.originalCount, φ (U.get j) = Q.original.get j) (j : Fin Q.strongCount) :
    φ (Q.lift U j) = Q.strong.get j := by
  have hvalid := (validSchreier_iff Q).1 hQ
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount, j.val = a → φ (Q.lift U j) = Q.strong.get j := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · have hcast : Fin.castLE Q.originalCount_le ⟨j.val, hj⟩ = j := Fin.ext rfl
        rw [Q.lift_of_lt U j hj, horig, ← hvalid.1 ⟨j.val, hj⟩, hcast]
      · have hm := Nat.le_of_not_lt hj
        rw [Q.lift_of_le U j hm, map_schreierWordValue, hvalid.2.1 j hm,
          RawSchreierDatum.derivationValue]
        apply schreierWordValue_congr
        intro l
        exact ih l.val (by omega) _ rfl
  exact all j.val j rfl

section Inj

variable {Q : RawSchreierDatum n} {φ : K →* Equiv.Perm (Fin n)} {U : Vector K Q.originalCount}

theorem liftSift_of_sift (hQ : ValidSchreier Q)
    (horig : ∀ j : Fin Q.originalCount, φ (U.get j) = Q.original.get j)
    (hinj : ∀ x ∈ Q.liftedOriginalSubgroup U, φ x = 1 → x = 1) :
    ∀ d j, j + d = Q.baseCount → ∀ v ∈ Q.liftedOriginalSubgroup U,
      schreierSiftResidual (Q.siftLevels Q.orbitTables j) (φ v) = some 1 →
      liftSiftResidual φ (Q.liftedSiftLevels (Q.liftedOrbitTables U) j) v = some 1 := by
  have hlift := lift_image_of_valid hQ horig
  intro d
  induction d with
  | zero =>
    intro j hj v hv hs
    have hj' : j = Q.baseCount := by omega
    subst hj'
    have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
      List.drop_eq_nil_iff.2 (by simp)
    simp only [siftLevels, hdrop, List.map_nil, schreierSiftResidual, Option.some.injEq] at hs
    rw [Q.liftedSiftLevels_terminal, liftSiftResidual_nil, hinj v hv hs]
  | succ d ih =>
    intro j hj v hv hs
    let J : Fin Q.baseCount := ⟨j, by omega⟩
    rw [show j = J.val from rfl, Q.siftLevels_cons Q.orbitTables J] at hs
    rw [show j = J.val from rfl, Q.liftedSiftLevels_cons (Q.liftedOrbitTables U) J]
    cases ht : (Q.orbitTables.get J).transversal? (φ v (Q.base.get J)) with
    | none =>
      rw [schreierSiftResidual_unavailable _ _ _ _ ht] at hs
      cases hs
    | some t =>
      rw [schreierSiftResidual_available _ _ _ _ t ht] at hs
      rw [Q.orbitTables_get J] at ht
      obtain ⟨T, hT⟩ := Q.exists_lifted_record U J (φ v (Q.base.get J)) t ht
      have hTt : t = φ T := Q.lifted_record_map U φ hlift J _ (t, T) hT
      have hT' : ((Q.liftedOrbitTables U).get J).transversal? (φ v (Q.base.get J)) =
          some (t, T) := by rw [Q.liftedOrbitTables_get]; exact hT
      rw [liftSiftResidual_available φ _ _ _ v (t, T) hT']
      have hTH : T ∈ Q.liftedOriginalSubgroup U := by
        have := Q.lifted_record_mem U J _ (t, T) hT
        rw [← Q.liftedLevelSubgroup_zero U]
        exact Q.liftedLevelSubgroup_antitone U 0 J.val (Nat.zero_le _) this
      refine ih (J.val + 1) (by simp [J]; omega) (T⁻¹ * v)
        ((Q.liftedOriginalSubgroup U).mul_mem ((Q.liftedOriginalSubgroup U).inv_mem hTH) hv) ?_
      rw [map_mul, map_inv, ← hTt]
      exact hs

theorem validLiftedSchreier_of_injOn (hQ : ValidSchreier Q)
    (horig : ∀ j : Fin Q.originalCount, φ (U.get j) = Q.original.get j)
    (hinj : ∀ x ∈ Q.liftedOriginalSubgroup U, φ x = 1 → x = 1) : ValidLiftedSchreier Q φ U := by
  have hlift := lift_image_of_valid hQ horig
  have hvalid := (validSchreier_iff Q).1 hQ
  refine ⟨hQ, horig, ?_, ?_⟩
  · intro h hh
    obtain ⟨j, hj, rfl⟩ := (Q.mem_liftedLevelGenerators_iff U _ h).1 hh
    apply hinj _ (Q.lift_mem_liftedOriginalSubgroup U j)
    rw [hlift]
    apply hvalid.2.2.1
    rw [← Q.levelIndices_map_strong]
    exact List.mem_map_of_mem hj
  · intro i x tx htx p hp
    obtain ⟨t, hrec⟩ := (Q.liftedTransversal?_eq_some_iff U i x tx).1 htx
    have ht : Q.transversal? i x = some t := Q.transversal_of_lifted_record U i x (t, tx) hrec
    have htt : t = φ tx := Q.lifted_record_map U φ hlift i x (t, tx) hrec
    have hp1 : p.1 ∈ Q.levelSteps i.val := by
      rw [← Q.liftedLevelSteps_map_fst U]
      exact List.mem_map_of_mem hp
    have hpφ : φ p.2 = p.1 := by
      obtain ⟨j, -, rfl | rfl⟩ := (Q.mem_liftedLevelSteps_iff U i.val p).1 hp
      · exact hlift j
      · simp only [Prod.snd_inv, Prod.fst_inv, map_inv, hlift j]
    have hpH : p.2 ∈ Q.liftedOriginalSubgroup U := by
      obtain ⟨j, -, rfl | rfl⟩ := (Q.mem_liftedLevelSteps_iff U i.val p).1 hp
      · exact Q.lift_mem_liftedOriginalSubgroup U j
      · exact (Q.liftedOriginalSubgroup U).inv_mem (Q.lift_mem_liftedOriginalSubgroup U j)
    obtain ⟨ty', hty', hsift⟩ := hvalid.2.2.2 i x t ht p.1 hp1
    obtain ⟨T, hT⟩ := Q.exists_lifted_record U i (p.1 x) ty' hty'
    have hTt : ty' = φ T := Q.lifted_record_map U φ hlift i _ (ty', T) hT
    refine ⟨T, (Q.liftedTransversal?_eq_some_iff U i (p.1 x) T).2 ⟨ty', hT⟩, ?_⟩
    have hmemT : ∀ y (q : Equiv.Perm (Fin n) × K),
        (Q.liftedOrbitSearch U i).transversal? y = some q → q.2 ∈ Q.liftedOriginalSubgroup U := by
      intro y q hq
      have := Q.lifted_record_mem U i y q hq
      rw [← Q.liftedLevelSubgroup_zero U]
      exact Q.liftedLevelSubgroup_antitone U 0 i.val (Nat.zero_le _) this
    have hvH : T⁻¹ * p.2 * tx ∈ Q.liftedOriginalSubgroup U :=
      (Q.liftedOriginalSubgroup U).mul_mem ((Q.liftedOriginalSubgroup U).mul_mem
        ((Q.liftedOriginalSubgroup U).inv_mem (hmemT _ _ hT)) hpH) (hmemT _ _ hrec)
    refine liftSift_of_sift hQ horig hinj (Q.baseCount - (i.val + 1)) (i.val + 1) (by omega) _
      hvH ?_
    rw [map_mul, map_mul, map_inv, hpφ, ← hTt, ← htt]
    exact (schreierSiftSucceeds_eq_true_iff _ _).1 hsift

end Inj

end CFSG.Sporadic.SuzOddCore
