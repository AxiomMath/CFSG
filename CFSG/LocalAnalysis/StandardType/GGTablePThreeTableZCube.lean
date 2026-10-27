module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

section TableZCubeAux

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

private theorem tableZCube_three_cast : (3 : ZMod 3) = 0 := ZMod.natCast_self 3

private theorem tableZCube_Bv (i : Fin Tag.E6.rank) :
    (∑ j, Tag.E6.symmetrizedCartan i j * e6ThreeVarpiOne j)
      = (Pi.single 0 (3 : ℤ) : Fin Tag.E6.rank → ℤ) i := by
  revert i
  decide +kernel

private theorem tableZCube_iform_single (i : Fin Tag.E6.rank) (y : Fin Tag.E6.rank → ℤ) :
    iform (Pi.single i 1) y = ∑ j, Tag.E6.symmetrizedCartan i j * y j := by
  simp only [iform]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    simp at h

private theorem tableZCube_iform_smul_left (c : ℤ) (x y : Fin Tag.E6.rank → ℤ) :
    iform (c • x) y = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem tableZCube_iform_smul_right (c : ℤ) (x y : Fin Tag.E6.rank → ℤ) :
    iform x (c • y) = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem tableZCube_iform_varpi (x : Fin Tag.E6.rank → ℤ) :
    iform x e6ThreeVarpiOne = 3 * x 0 := by
  have h : ∀ i, (∑ j, x i * Tag.E6.symmetrizedCartan i j * e6ThreeVarpiOne j)
      = x i * (∑ j, Tag.E6.symmetrizedCartan i j * e6ThreeVarpiOne j) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [iform]
  calc ∑ i, ∑ j, x i * Tag.E6.symmetrizedCartan i j * e6ThreeVarpiOne j
      = ∑ i, x i * (∑ j, Tag.E6.symmetrizedCartan i j * e6ThreeVarpiOne j) :=
        Finset.sum_congr rfl fun i _ => h i
    _ = ∑ i, x i * (Pi.single 0 (3 : ℤ) : Fin Tag.E6.rank → ℤ) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tableZCube_Bv i]
    _ = 3 * x 0 := by
        simp [Pi.single_apply]
        ring

private theorem tableZCube_ker_probe :
    ∀ z : Fin Tag.E6.rank → ZMod 3,
      (∀ i, ∑ j, ((Tag.E6.symmetrizedCartan i j : ℤ) : ZMod 3) * z j = 0) →
        ∀ k, z k = z 0 * ((e6ThreeVarpiOne k : ℤ) : ZMod 3) := by
  decide +kernel

private theorem tableZCube_ker (y : Fin Tag.E6.rank → ℤ)
    (hy : ∀ i, (iform (Pi.single i 1) y : ZMod 3) = 0) :
    ∀ k, (y k : ZMod 3) = (y 0 : ZMod 3) * ((e6ThreeVarpiOne k : ℤ) : ZMod 3) := by
  refine tableZCube_ker_probe (fun j => (y j : ZMod 3)) ?_
  intro i
  have h := hy i
  rw [tableZCube_iform_single i y] at h
  have hA : ((∑ j, Tag.E6.symmetrizedCartan i j * y j : ℤ) : ZMod 3)
      = ∑ j, ((Tag.E6.symmetrizedCartan i j : ℤ) : ZMod 3) * (y j : ZMod 3) := by
    push_cast
    rfl
  rw [← hA]
  exact h

private theorem tableZCube_rho_zsmul
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y : Fin Tag.E6.rank → ℤ, ρ (x + y) = ρ x + ρ y)
    (c : ℤ) (x : Fin Tag.E6.rank → ℤ) :
    ρ (c • x) = c • ρ x :=
  map_zsmul (AddMonoidHom.mk' ρ hadd) c x

private theorem tableZCube_dvd_rho_of_dvd
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y : Fin Tag.E6.rank → ℤ, ρ (x + y) = ρ x + ρ y)
    (d : Fin Tag.E6.rank → ℤ) (hd : ∀ k, (3 : ℤ) ∣ d k) :
    ∀ i, (3 : ℤ) ∣ (ρ d) i := by
  choose u hu using hd
  have hd' : d = (3 : ℤ) • u := by
    funext k
    rw [hu k]
    simp [Pi.smul_apply, smul_eq_mul]
  have hρd : ρ d = (3 : ℤ) • ρ u := by
    rw [hd']
    exact map_zsmul (AddMonoidHom.mk' ρ hadd) 3 u
  intro i
  rw [hρd]
  exact ⟨(ρ u) i, by simp [Pi.smul_apply, smul_eq_mul]⟩

private theorem tableZCube_rho_varpi
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hiso : ∀ x y, iform (ρ x) (ρ y) = iform x y)
    (hρ : ¬ E6CosetW ρ) :
    ∀ k, ((ρ e6ThreeVarpiOne) k : ZMod 3) = 2 * (e6ThreeVarpiOne k : ZMod 3) := by
  have hBrho : ∀ i, (iform (Pi.single i 1) (ρ e6ThreeVarpiOne) : ZMod 3) = 0 := by
    intro i
    have h := hiso (ρ.symm (Pi.single i 1)) e6ThreeVarpiOne
    simp only [Equiv.apply_symm_apply, tableZCube_iform_varpi] at h
    rw [h]
    push_cast
    rw [tableZCube_three_cast, zero_mul]
  have hkerRho : ∀ k, ((ρ e6ThreeVarpiOne) k : ZMod 3) =
      ((ρ e6ThreeVarpiOne) 0 : ZMod 3) * (e6ThreeVarpiOne k : ZMod 3) :=
    tableZCube_ker (ρ e6ThreeVarpiOne) hBrho
  have hm0 : ((ρ e6ThreeVarpiOne) 0 : ZMod 3) ≠ 0 := by
    intro h0
    have hdvd : ∀ k, (3 : ℤ) ∣ (ρ e6ThreeVarpiOne) k := by
      intro k
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (ρ e6ThreeVarpiOne k) 3).1
        (by rw [hkerRho k, h0, zero_mul])
    choose u hu using hdvd
    have hrho : ρ e6ThreeVarpiOne = (3 : ℤ) • u := by
      funext k
      rw [hu k]
      simp [Pi.smul_apply, smul_eq_mul]
    have hiso' := hiso e6ThreeVarpiOne e6ThreeVarpiOne
    rw [hrho, tableZCube_iform_smul_left, tableZCube_iform_smul_right] at hiso'
    have hv12 : iform e6ThreeVarpiOne e6ThreeVarpiOne = 12 := by
      rw [tableZCube_iform_varpi]
      decide +kernel
    rw [hv12] at hiso'
    omega
  have hm1 : ((ρ e6ThreeVarpiOne) 0 : ZMod 3) ≠ 1 := by
    intro h1
    refine hρ ?_
    intro k
    have h := hkerRho k
    rw [h1, one_mul] at h
    push_cast
    rw [h, sub_self]
  have hm : ((ρ e6ThreeVarpiOne) 0 : ZMod 3) = 2 := by
    have hm3 : ∀ m : ZMod 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide +kernel
    rcases hm3 ((ρ e6ThreeVarpiOne) 0 : ZMod 3) with h | h | h
    · exact absurd h hm0
    · exact absurd h hm1
    · exact h
  intro k
  rw [hkerRho k, hm]

end TableZCubeAux

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint in
theorem e6_twistedCube_congr (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (hiso : ∀ x y, iform (ρ x) (ρ y) = iform x y)
    (hρ : ¬ E6CosetW ρ) (κ : Fin Tag.E6.rank → ℤ)
    (hκ : ∀ i, (iform (Pi.single i 1) (ρ κ + κ) : ZMod 3) = 0) :
    ∀ i, ((κ - ρ κ + ρ (ρ κ)) i : ZMod 3) = 0 := by
  have hrv := tableZCube_rho_varpi ρ hiso hρ
  set y : Fin Tag.E6.rank → ℤ := ρ κ + κ with hy
  have hκ' : ∀ i, (iform (Pi.single i 1) y : ZMod 3) = 0 := by
    intro i
    simpa [hy] using hκ i
  have hker : ∀ k, (y k : ZMod 3) = (y 0 : ZMod 3) * ((e6ThreeVarpiOne k : ℤ) : ZMod 3) :=
    tableZCube_ker y hκ'
  set c : ℤ := y 0 with hc
  have hkerc : ∀ k, (y k : ZMod 3) = (c : ZMod 3) * ((e6ThreeVarpiOne k : ℤ) : ZMod 3) := by
    simpa [hc] using hker
  set d1 : Fin Tag.E6.rank → ℤ := y - c • e6ThreeVarpiOne with hd1_eq
  have hd1 : ∀ k, (3 : ℤ) ∣ d1 k := by
    intro k
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (d1 k) 3).1 ?_
    have h := hkerc k
    rw [hd1_eq]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [h]
    ring
  have hd2 : ∀ i, (3 : ℤ) ∣ (ρ d1) i := tableZCube_dvd_rho_of_dvd ρ hadd d1 hd1
  have hy' : y = c • e6ThreeVarpiOne + d1 := by
    funext k
    rw [hd1_eq]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hρy : ρ y = c • ρ e6ThreeVarpiOne + ρ d1 := by
    rw [hy', hadd (c • e6ThreeVarpiOne) d1, tableZCube_rho_zsmul ρ hadd]
  set e : Fin Tag.E6.rank → ℤ := d1 - (3 : ℤ) • ρ κ + ρ d1 with he_def
  have he : ∀ i, (3 : ℤ) ∣ e i := by
    intro i
    rw [he_def]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨a, ha⟩ := hd1 i
    obtain ⟨b, hb⟩ := hd2 i
    exact ⟨a - (ρ κ) i + b, by rw [ha, hb]; ring⟩
  have hfun : κ - ρ κ + ρ (ρ κ) = c • (e6ThreeVarpiOne + ρ e6ThreeVarpiOne) + e := by
    have h1 : κ - ρ κ + ρ (ρ κ) = y - (3 : ℤ) • ρ κ + ρ y := by
      rw [hy, hadd (ρ κ) κ]
      abel
    have h2 : y - (3 : ℤ) • ρ κ + ρ y = c • (e6ThreeVarpiOne + ρ e6ThreeVarpiOne) + e := by
      rw [hρy, hy', he_def, smul_add]
      abel
    exact h1.trans h2
  intro i
  have hei : (e i : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (e i) 3).2 (he i)
  calc ((κ - ρ κ + ρ (ρ κ)) i : ZMod 3)
      = ((c • (e6ThreeVarpiOne + ρ e6ThreeVarpiOne) + e) i : ZMod 3) := by rw [hfun]
    _ = (c : ZMod 3) * ((e6ThreeVarpiOne i : ZMod 3) +
          ((ρ e6ThreeVarpiOne) i : ZMod 3)) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [hei]
        ring
    _ = (c : ZMod 3) * ((e6ThreeVarpiOne i : ZMod 3) +
          2 * (e6ThreeVarpiOne i : ZMod 3)) := by rw [hrv i]
    _ = (3 : ZMod 3) * ((c : ZMod 3) * (e6ThreeVarpiOne i : ZMod 3)) := by ring
    _ = 0 := by rw [tableZCube_three_cast, zero_mul]

end CFSG.StandardType.TablePThreeKG

end
