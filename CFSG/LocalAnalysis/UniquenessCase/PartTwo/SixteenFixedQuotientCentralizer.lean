module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.Quasithin.Background.FixVLattice

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W Q : Type} [CommGroup W] [CommGroup Q]

theorem centralizer_pow_eq_one_of_fixed_quotient
    {H : Subgroup (MulAut W)} (q : W →* Q) (rho : H →* MulAut Q)
    (hq : Function.Surjective q)
    (hker : ∀ w : W, q w = 1 ↔ w ∈ fixV H)
    (heq : ∀ (h : H) (w : W), q ((h : MulAut W) w) = rho h (q w))
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    {n : ℕ}
    (hn : ∀ a ∈ Subgroup.centralizer (rho.range : Set (MulAut Q)), a ^ n = 1) :
    ∀ a ∈ Subgroup.centralizer (H : Set (MulAut W)), a ^ n = 1 := by
  classical
  intro a ha
  have hac : ∀ h ∈ H, a * h = h * a := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp ha h hh).symm
  have hstab : Subgroup.centralizer (H : Set (MulAut W)) ≤ stabSub (fixV H) :=
    CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer
      (Subgroup.centralizer_le_normalizer (H : Set (MulAut W)))
  have hZiff : ∀ z : W, z ∈ fixV H ↔ a z ∈ fixV H :=
    fun z => (hstab ha z).symm
  obtain ⟨ψ, hψ⟩ := s16g_exists_induced_aut q hq (φ := a) (fun w => by
    rw [hker w, hker (a w)]
    exact hZiff w)
  have hψcent : ∀ x ∈ rho.range, x * ψ = ψ * x := by
    intro x hx
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hx
    ext qv
    obtain ⟨w, rfl⟩ := hq qv
    have haw : (l : MulAut W) (a w) = a ((l : MulAut W) w) := by
      have h1 := congrFun (congrArg DFunLike.coe (hac l l.2)) w
      simpa only [MulAut.mul_apply] using h1.symm
    calc (rho l * ψ) (q w) = rho l (ψ (q w)) := rfl
      _ = rho l (q (a w)) := by rw [hψ w]
      _ = q ((l : MulAut W) (a w)) := (heq l (a w)).symm
      _ = q (a ((l : MulAut W) w)) := by rw [haw]
      _ = ψ (q ((l : MulAut W) w)) := (hψ _).symm
      _ = ψ (rho l (q w)) := by rw [heq l w]
      _ = (ψ * rho l) (q w) := rfl
  have hψn : ψ ^ n = 1 := hn ψ (by
    rw [Subgroup.mem_centralizer_iff]
    exact hψcent)
  have hqpow : ∀ k : ℕ, ∀ w : W, q ((a ^ k) w) = (ψ ^ k) (q w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        calc q ((a ^ (k + 1)) w) = q (a ((a ^ k) w)) := by
              rw [pow_succ', MulAut.mul_apply]
          _ = ψ (q ((a ^ k) w)) := (hψ _).symm
          _ = ψ ((ψ ^ k) (q w)) := by rw [ih]
          _ = (ψ ^ (k + 1)) (q w) := by rw [pow_succ', MulAut.mul_apply]
  have hqan : ∀ w : W, q ((a ^ n) w) = q w := by
    intro w
    rw [hqpow n w, hψn]
    rfl
  have hfix : ∀ w : W, (a ^ n) w * w⁻¹ ∈ fixV H := by
    intro w
    exact (hker _).1 (by rw [map_mul, map_inv, hqan w, mul_inv_cancel])
  have hacn : ∀ h ∈ H, a ^ n * h = h * a ^ n := by
    intro h hh
    exact (show Commute a h from hac h hh).pow_left n
  exact s16g_eq_one_of_commSub hcomm hacn hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
