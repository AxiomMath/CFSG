module

public import CFSG.Monster.B.Fischer.CanonicalGroup
public import CFSG.Monster.B.Fischer.PinnedBridgeChecks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def xiPerm : Equiv.Perm (Fin 3510) := permOfArr 3510 pinXiRaw

theorem rep_xi :
    Rep 3510 pinXiRaw xiPerm := (rep_permOfArr bridge_check.1).1

theorem rep_xiSymm :
    Rep 3510 (invCand 3510 pinXiRaw) xiPerm.symm := by
  intro x
  have h := (isInvA_spec bridge_check.1 (xiPerm.symm x).2).2
  rw [rep_xi.apply (xiPerm.symm x).2, Fin.eta, Equiv.apply_symm_apply] at h
  exact h

@[expose] noncomputable def ιEquiv :
    Y ≃ Fin 3510 := Equiv.ofBijective ι ι_bijective

@[expose] noncomputable def psi :
    Y ≃ Fin 3510 := ιEquiv.trans xiPerm

@[expose] noncomputable def fi22StrongWord (w : List ℤ) : Equiv.Perm (Fin 3510) :=
  schreierWordValue fi22Chain.strong.get 19 (le_of_eq rfl) (toLetters 19 w)

theorem rep_candidate
    {k : ℕ} (hk : k < 13) :
    Rep 3510 (indCandidate k) (ιEquiv.permCongr (jGen k)) := by
  intro x
  obtain ⟨y, rfl⟩ := ιEquiv.surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact (ι_jGen hk y).symm

theorem rep_conj
    {k : ℕ} (hk : k < 13) :
    Rep 3510 (compA 3510 (compA 3510 pinXiRaw (indCandidate k)) (invCand 3510 pinXiRaw))
      (psi.permCongr (jGen k)) := by
  intro x
  rw [compA_get x.2, rep_xiSymm x, compA_get (xiPerm.symm x).2, rep_candidate hk, rep_xi,
    Equiv.permCongr_apply, Equiv.permCongr_apply, psi, Equiv.trans_apply,
    Equiv.symm_trans_apply]

theorem fi22StrongWord_pinWord
    {k : ℕ} (hk : k < 13) :
    fi22StrongWord (pinWord k) = psi.permCongr (jGen k) := by
  obtain ⟨hl, he⟩ := bridge_check.2.1 k hk
  have hw : fi22StrongWord (pinWord k) = Quiver.SchreierGraph.evalWord
      (fun h : Fin 19 => fi22StrongPerm h) (toLetters 19 (pinWord k)) := by
    rw [fi22StrongWord, schreierWordValue]
    simp only [fi22Chain_strong_get]
  rw [hw]
  exact eq_of_eqA (rep_wordA (gs := fi22StrongPerm) (fun h hh => rep_fi22Strong hh)
    (fun h hh => rep_fi22StrongInv hh) _ hl) (rep_conj hk) he

theorem fi22StrongWord_mem (w : List ℤ) : fi22StrongWord w ∈ fi22P :=
  schreierWordValue_mem_subgroup _ _ _ _ fun _ => fi22Chain_strong_mem _

theorem map_J_le :
    J.map psi.permCongrHom.toMonoidHom ≤ fi22P := by
  rw [J_eq_closure_jGen, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  change psi.permCongr (jGen k) ∈ fi22P
  rw [← fi22StrongWord_pinWord k.2]
  exact fi22StrongWord_mem _

theorem permCongr_mem
    {g : Equiv.Perm Y} (hg : g ∈ J) : psi.permCongr g ∈ fi22P :=
  map_J_le ⟨g, hg, rfl⟩

@[expose] noncomputable def bridgeHom :
    J →* fi22P :=
  (psi.permCongrHom.toMonoidHom.comp J.subtype).codRestrict fi22P fun g => permCongr_mem g.2

theorem bridgeHom_apply
    (g : J) : (bridgeHom g : Equiv.Perm (Fin 3510)) = psi.permCongr g := rfl

theorem bridgeHom_injective :
    Function.Injective bridgeHom := fun _ _ e =>
  Subtype.ext (psi.permCongr.injective (congrArg Subtype.val e))

end CFSG.Monster.B.Fischer
