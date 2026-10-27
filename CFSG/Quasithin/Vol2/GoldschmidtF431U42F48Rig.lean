module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Fin

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.H13.F431.U42.F48

@[expose] def f48PermConj {X Z : Type*} (e : X ≃ Z) : Equiv.Perm X →* Equiv.Perm Z where
  toFun σ := e.permCongr σ
  map_one' := by ext; simp [Equiv.permCongr_apply]
  map_mul' a b := by ext; simp [Equiv.permCongr_apply]

theorem f48PermConj_apply {X Z : Type*} (e : X ≃ Z) (σ : Equiv.Perm X) (z : Z) :
    f48PermConj e σ z = e (σ (e.symm z)) := rfl

section E


theorem u42_conj_mem_N1 (y : ↥P1) : (MulAut.conj (y : Y) : MulAut Y) ∈ A0.N1 := by
  rw [A0_N1]
  exact Subgroup.mem_map_of_mem _ y.2

theorem u42_conj_mem_N2 (y : ↥P2) : (MulAut.conj (y : Y) : MulAut Y) ∈ A0.N2 := by
  rw [A0_N2]
  exact Subgroup.mem_map_of_mem _ y.2

@[expose] noncomputable def u42E1 : ↥P1 →* u42Setting.α.G1 :=
  ((MulAut.conj : Y →* MulAut Y).comp P1.subtype).codRestrict A0.N1 u42_conj_mem_N1

theorem u42E1_surjective : Function.Surjective (u42E1 : ↥P1 →* u42Setting.α.G1) := by
  rintro ⟨φ, hφ⟩
  rw [show A0.N1 = P1.map (MulAut.conj : Y →* MulAut Y) from A0_N1] at hφ
  obtain ⟨y, hy, rfl⟩ := hφ
  exact ⟨⟨y, hy⟩, rfl⟩

theorem u42_f1_E1 (y : ↥P1) : f1 (c := u42Setting.ι) (u42E1 y) = eG (y : Y) := rfl

theorem u42_rigid
    (π : u42Setting.α.G1 →* Equiv.Perm (Pt u42Setting.ι))
    (hB : ∀ (x : u42Setting.α.G12) (z : Pt u42Setting.ι),
      π (u42Setting.α.α1 x) z = f1 (c := u42Setting.ι) (u42Setting.α.α1 x) • z)
    (hN : ∀ (p : u42Setting.α.G1) (z : Pt u42Setting.ι), Near u42Setting.ι z →
      π p z = f1 (c := u42Setting.ι) p • z) (p : u42Setting.α.G1) (z : Pt u42Setting.ι) :
    π p z = f1 (c := u42Setting.ι) p • z := by
  have hstd : ∀ (y : ↥P1) (z : Pt u42Setting.ι),
      u42Kappa (eG (y : Y) • z) = ((y : Y) : P45) (u42Kappa z) := by
    intro y z
    rw [u42Kappa_smul, stdG0_eG]
  have hmain : ∀ y : ↥P1, f48PermConj u42Kappa (π (u42E1 y)) = ((y : Y) : P45) := by
    refine f48_rigid ((f48PermConj u42Kappa).comp (π.comp u42E1)) ?_ ?_
    · intro y hy
      refine Equiv.ext fun m => ?_
      show u42Kappa (π (u42E1 y) (u42Kappa.symm m)) = _
      have hx : u42Setting.α.α1 (⟨MulAut.conj (y : Y), Subgroup.mem_inf.2
          ⟨u42_conj_mem_N1 y, u42_conj_mem_N2 ⟨y, hy⟩⟩⟩ : u42Setting.α.G12) = u42E1 y := rfl
      have hb := hB ⟨MulAut.conj (y : Y), Subgroup.mem_inf.2
          ⟨u42_conj_mem_N1 y, u42_conj_mem_N2 ⟨y, hy⟩⟩⟩ (u42Kappa.symm m)
      rw [hx] at hb
      rw [hb, u42_f1_E1, hstd, Equiv.apply_symm_apply]
    · intro y m hm
      show u42Kappa (π (u42E1 y) (u42Kappa.symm m)) = _
      have hz : Near u42Setting.ι (u42Kappa.symm m) :=
        near_of_coll (by rw [Equiv.apply_symm_apply]; exact hm)
      rw [hN _ _ hz, u42_f1_E1, hstd, Equiv.apply_symm_apply]
  obtain ⟨y, rfl⟩ := u42E1_surjective p
  have := congrArg (fun σ : P45 => σ (u42Kappa z)) (hmain y)
  simp only [f48PermConj_apply, Equiv.symm_apply_apply] at this
  rw [u42_f1_E1]
  exact u42Kappa.injective (this.trans (hstd y z).symm)

end E

end CFSG.Quasithin.H13.F431.U42
