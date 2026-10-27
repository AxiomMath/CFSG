module

public import CFSG.Quasithin.AppendixH.H16.H165FourData
public import CFSG.Quasithin.AppendixH.H16.H165FourAbs
public import CFSG.Quasithin.Background.RonanH163Base

public section

namespace CFSG.ASVolI.H16

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Monster.Code
open CFSG.ASVolI.ChH (cenMS)

@[expose] def h165U (m : ℕ) : G6.PermMod 24 := Multiplicative.ofAdd (bvec 24 m)

theorem h165U_mem {m : ℕ} (hsyn : syndM m = 0) (hpair : m.testBit 0 = m.testBit 1) :
    h165U m ∈ golayC ⊓ pairKer 0 1 := by
  rw [h165U, mem_code22, toAdd_ofAdd]
  refine ⟨(bvec_mem_C_iff m).2 hsyn, ?_⟩
  have hbit : bvec 24 m (0 : Fin 24) = bvec 24 m (1 : Fin 24) := by
    change (if m.testBit 0 then (1 : ZMod 2) else 0) =
      (if m.testBit 1 then (1 : ZMod 2) else 0)
    rw [hpair]
  rw [hbit]
  exact CharTwo.add_self_eq_zero _

theorem h165_kappa_fixed : ∀ m ∈ h165OctMasks,
    R ⟨h165Z0, h165Z0_mem⟩ (code22Coords.κ (h165U m)) = code22Coords.κ (h165U m) := by
  intro m hm
  have hpres : ∀ τ ∈ mog22plus, Preserves (golayC ⊓ pairKer 0 1)
      (Subgroup.zpowers (G6.allOnes 24)) τ := fun _ hτ => preserves_code22 hτ
  have hu : h165U m ∈ golayC ⊓ pairKer 0 1 :=
    h165U_mem (h165Oct_syndM m hm) (h165Oct_pair m hm)
  have h1 := SecCoords.κ_permAct_rho code22Coords mog22plus hpres
    ⟨h165Z0, h165Z0_mem⟩ hu
  have h2 : G6.permAct 24 h165Z0 (h165U m) = h165U m := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_permAct, h165U, toAdd_ofAdd]
    funext p
    simp only [permWord, Function.comp_apply]
    rw [show h165Z0⁻¹ = h165Z0 from inv_eq_of_mul_eq_one_right h165Z0_sq]
    rw [bvec_apply, bvec_apply, h165Oct_Z0 m hm p]
  change code22Coords.rho mog22plus hpres ⟨h165Z0, h165Z0_mem⟩
      (code22Coords.κ (h165U m)) = code22Coords.κ (h165U m)
  exact h1.symm.trans (congrArg code22Coords.κ h2)

theorem h165_oct_stable {g : P24} (hg : g ∈ mog22plus)
    (hfix : ∀ w ∈ fixV (rImg R (Subgroup.zpowers h165Z0)), R ⟨g, hg⟩ w = w) :
    ∀ m ∈ h165OctMasks, ∀ p : Fin 24, m.testBit (g p) = m.testBit p := by
  intro m hm p
  have hpres : ∀ τ ∈ mog22plus, Preserves (golayC ⊓ pairKer 0 1)
      (Subgroup.zpowers (G6.allOnes 24)) τ := fun _ hτ => preserves_code22 hτ
  have hmC : h165U m ∈ golayC ⊓ pairKer 0 1 :=
    h165U_mem (h165Oct_syndM m hm) (h165Oct_pair m hm)
  have hfixκ : code22Coords.κ (h165U m) ∈ fixV (rImg R (Subgroup.zpowers h165Z0)) :=
    (mem_fixV_rImg_zpowers R h165Z0_mem (code22Coords.κ (h165U m))).2
      (h165_kappa_fixed m hm)
  have hgfix : R ⟨g, hg⟩ (code22Coords.κ (h165U m)) = code22Coords.κ (h165U m) :=
    hfix _ hfixκ
  have hpermκ : code22Coords.κ (G6.permAct 24 g (h165U m)) = code22Coords.κ (h165U m) := by
    change code22Coords.rho mog22plus hpres ⟨g, hg⟩
        (code22Coords.κ (h165U m)) = code22Coords.κ (h165U m) at hgfix
    exact (SecCoords.κ_permAct_rho code22Coords mog22plus hpres ⟨g, hg⟩ hmC).trans hgfix
  have hsq : ∀ x : W10, x * x = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h3 : code22Coords.κ (G6.permAct 24 g (h165U m) * h165U m) = 1 := by
    rw [map_mul, hpermκ]
    exact hsq _
  have hmem : G6.permAct 24 g (h165U m) * h165U m ∈ golayC ⊓ pairKer 0 1 :=
    (golayC ⊓ pairKer 0 1).mul_mem ((preserves_code22 hg).1 _ hmC) hmC
  have hker : G6.permAct 24 g (h165U m) * h165U m ∈ Subgroup.zpowers (G6.allOnes 24) :=
    (code22Coords.ker_iff _ hmem).1 h3
  rcases (mem_zpowers_allOnes _).1 hker with h4 | h4
  · rw [toAdd_mul, toAdd_permAct, h165U, toAdd_ofAdd] at h4
    have hall : permWord g (bvec 24 m) = bvec 24 m := by
      funext i
      exact zmod2_eq_of_add (by simpa only [Pi.add_apply, Pi.zero_apply] using congrFun h4 i)
    have hgp : bvec 24 m p = bvec 24 m (g p) := by
      have h := congrFun hall (g p)
      have hgi : g⁻¹ (g p) = p := by simp
      simpa only [permWord, Function.comp_apply, hgi] using h
    rw [bvec_apply, bvec_apply] at hgp
    cases hpb : m.testBit p <;> cases hqb : m.testBit (g p) <;> simp_all
  · exfalso
    rw [toAdd_mul, toAdd_permAct, h165U, toAdd_ofAdd] at h4
    have hgimg : g⁻¹ (0 : Fin 24) = 0 ∨ g⁻¹ (0 : Fin 24) = 1 := by
      have hg' : g⁻¹ ∈ mog22plus := mog22plus.inv_mem hg
      rcases hg'.2 with ⟨h0, -⟩ | ⟨h0, -⟩
      · exact Or.inl h0
      · exact Or.inr h0
    have hbv : bvec 24 m (1 : Fin 24) = bvec 24 m (0 : Fin 24) := by
      change (if m.testBit 1 then (1 : ZMod 2) else 0) =
        (if m.testBit 0 then (1 : ZMod 2) else 0)
      rw [h165Oct_pair m hm]
    have hz : permWord g (bvec 24 m) 0 + bvec 24 m 0 = 0 := by
      rw [permWord, Function.comp_apply]
      rcases hgimg with h | h
      · rw [h]
        exact CharTwo.add_self_eq_zero _
      · rw [h, hbv]
        exact CharTwo.add_self_eq_zero _
    have h0 := congrFun h4 0
    rw [Pi.add_apply] at h0
    change permWord g (bvec 24 m) 0 + bvec 24 m 0 = (1 : ZMod 2) at h0
    rw [hz] at h0
    exact zero_ne_one h0

theorem h165_cen_pair {g : P24}
    (hg : g ∈ cenMS R (fixV (rImg R (Subgroup.zpowers h165Z0)))) :
    g ∈ mog22plus ∧ ∀ p : Fin 24, g p = p ∨ g p = h165Partner p := by
  obtain ⟨hgΓ, hfix⟩ := (mem_cenMS_iff R _ g).1 hg
  refine ⟨hgΓ, fun p => ?_⟩
  exact h165Oct_sep p (g p) (fun m hm => ((h165_oct_stable hgΓ hfix) m hm p).symm)

theorem h165_actFix : (List.range 1024).all (fun m =>
    !(actC10 (koArr 7) m == m) || (actC10 h165D0Arr m == m && actC10 h165ZD0Arr m == m)) = true := by
  decide +kernel

theorem h165_E0_fixes : ∀ w ∈ fixV (rImg R (Subgroup.zpowers h165Z0)),
    R ⟨h165D0, h165D0_mem⟩ w = w ∧ R ⟨h165ZD0, h165ZD0_mem⟩ w = w := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
  have hZ0 : R ⟨h165Z0, h165Z0_mem⟩ (toW 10 m) = toW 10 m :=
    (mem_fixV_rImg_zpowers R h165Z0_mem (toW 10 m)).1 hw
  have hZ0' : actC10 (koArr 7) m = m :=
    toW_inj (actC10_lt _ _) hm
      ((R_toW ⟨h165Z0, h165Z0_mem⟩ hasArr_h165Z0 m).symm.trans hZ0)
  have hm1024 : m < 1024 := by simpa using hm
  have hbool := (List.all_eq_true.1 h165_actFix) m (List.mem_range.2 hm1024)
  rw [Bool.or_eq_true, Bool.and_eq_true] at hbool
  have hnot : ¬ ((!(actC10 (koArr 7) m == m)) = true) := by
    rw [hZ0']
    simp
  have hD0 : actC10 h165D0Arr m = m := by
    rcases hbool with h' | ⟨h1, -⟩
    · exact absurd h' hnot
    · simpa using h1
  have hZD0 : actC10 h165ZD0Arr m = m := by
    rcases hbool with h' | ⟨-, h2⟩
    · exact absurd h' hnot
    · simpa using h2
  exact ⟨by rw [R_toW _ hasArr_h165D0 m, hD0],
    by rw [R_toW _ hasArr_h165ZD0 m, hZD0]⟩

end CFSG.ASVolI.H16
