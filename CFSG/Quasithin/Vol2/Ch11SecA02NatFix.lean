module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

theorem eq_zero_of_forall_mulVec_eq {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K] (x : Fin d → K)
    (hx : ∀ g : ↥(StatedSL d K),
      ((g : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec x = x) :
    x = 0 := by
  funext j
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨i, hij⟩ := exists_ne j
  have h1 : (Matrix.transvection i j (1 : K)).mulVec x = x :=
    hx (specialLinearGroupEquivStatedSL d K
      ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩)
  have h2 := congrFun h1 i
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
    Pi.add_apply, Function.update_self, one_mul] at h2
  simpa using h2

theorem eq_one_of_fixed_of_realizesVia {V : Type*} [CommGroup V] {d : ℕ} (hd : 2 ≤ d)
    {K : Type} [Field K] {H : Subgroup (MulAut V)} {π : ↥(StatedSL d K) →* ↥H}
    (hR : (FFModel.nat (StatedSL d K)).RealizesVia H ⊤ ⊥ π) {v : V}
    (hv : ∀ h ∈ H, h v = v) : v = 1 := by
  obtain ⟨-, -, -, -, -, -, -, β, -, hβk, hβc⟩ := hR
  let u : ↥(⊤ : Subgroup V) := ⟨v, trivial⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hfix : ∀ γ : ↥(StatedSL d K), (FFModel.nat (StatedSL d K)).act γ m.1 = m.1 := by
    intro γ
    have h1 := hβc γ u m trivial trivial hm.symm
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), trivial⟩ : ↥(⊤ : Subgroup V)) = u :=
      Subtype.ext (hv _ (π γ).2)
    have h3 := hm.trans ((congrArg β h2).symm.trans h1)
    rw [QuotientGroup.eq] at h3
    have h5 := Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp h3)
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h5
    exact (inv_mul_eq_one.mp h5).symm
  have hm1 : m = 1 := by
    apply Subtype.ext
    have h0 : Multiplicative.toAdd (α := Fin d → K) m.1 = 0 :=
      eq_zero_of_forall_mulVec_eq hd _
        (fun γ => congrArg (Multiplicative.toAdd (α := Fin d → K)) (hfix γ))
    exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  have hβu : β u = 1 := by rw [← hm, hm1]; rfl
  exact Subgroup.mem_bot.mp ((hβk u).mp hβu)

end CFSG.Quasithin.Vol2.Ch11.SecA
