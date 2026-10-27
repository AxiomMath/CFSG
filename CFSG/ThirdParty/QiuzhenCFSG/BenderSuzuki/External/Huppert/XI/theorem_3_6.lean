module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert-Blackburn XI.3.6

The statement follows Volume III, physical page 196.

Reusable TeX for the formalized statement (not a transcription of the
currently unavailable source page):

```tex
\begin{theorem}[Huppert--Blackburn XI.3.6]
For $m > 0$, the Suzuki group
$\operatorname{Sz}\!\left(2^{2m+1}\right)$ is simple, and
$3 \nmid \left|\operatorname{Sz}\!\left(2^{2m+1}\right)\right|$.
\end{theorem}
```
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open PFAppendixIII
open scoped LinearAlgebra.Projectivization
open scoped Pointwise

/-- The root, torus, and Weyl relations make the concrete Suzuki group
perfect. -/
private theorem suzukiMatrixGroup_isPerfect
    (m : ℕ) (hm : 0 < m) :
    Group.IsPerfect (SuzukiMatrixGroup m) := by
  classical
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 := by
    exact binaryGaloisField_tits_formula_sq m pi hpi
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  rcases huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_, _, _, _, _, _, _, _, hroot_mul, _, hcommutator_coordinates,
      htorus_equiv, htorus_conjugation, _, _⟩
  obtain ⟨e, he⟩ := htorus_equiv
  let S : Subgroup (GL (Fin 4) K) := SuzukiMatrixSubgroup m
  let phi : S →* Abelianization S := Abelianization.of
  have hroot_mem (a b : K) : SuzukiRootGL m a b ∈ S := by
    exact Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)
  have htorus_mem (u : Kˣ) : SuzukiTorusGL m u ∈ S := by
    exact Subgroup.subset_closure (Or.inr (Or.inl ⟨u, rfl⟩))
  have hweyl_mem : SuzukiWeylGL m ∈ S := by
    exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hq_card : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have h_nontrivial_torus_parameter : ∃ s : Kˣ, s ≠ 1 := by
    have hq_gt_two : 2 < q := by
      change 2 ^ 1 < 2 ^ (2 * m + 1)
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have h_units_card : 1 < Nat.card Kˣ := by
      rw [Nat.card_units, hq_card]
      omega
    let _ : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h_units_card
    exact exists_ne 1
  obtain ⟨s, hs⟩ := h_nontrivial_torus_parameter
  have hroot_image (a b : K) :
      phi ⟨SuzukiRootGL m a b, hroot_mem a b⟩ = 1 := by
    let r : K → K → S := fun x y =>
      ⟨SuzukiRootGL m x y, hroot_mem x y⟩
    let t : Kˣ → S := fun u => ⟨SuzukiTorusGL m u, htorus_mem u⟩
    change phi (r a b) = 1
    have hr_mul (x y x' y' : K) :
        r x y * r x' y' =
          r (x + x') (y + y' + x * pi x') := by
      apply Subtype.ext
      exact hroot_mul x y x' y'
    have hF_le_S : F ≤ S := by
      change Subgroup.closure {A | ∃ x y : K, A = SuzukiRootGL m x y} ≤
        Subgroup.closure (SuzukiMatrixGeneratorSet m)
      rw [Subgroup.closure_le]
      intro A hA
      exact Subgroup.subset_closure (Or.inl hA)
    let inclusion : F →* S := Subgroup.inclusion hF_le_S
    let psi : F →* Abelianization S := phi.comp inclusion
    have hcentral_image (y : K) : phi (r 0 y) = 1 := by
      have hroot_F : SuzukiRootGL m 0 y ∈ F := by
        exact Subgroup.subset_closure ⟨0, y, rfl⟩
      let z : F := ⟨SuzukiRootGL m 0 y, hroot_F⟩
      have hz_commutator : z ∈ commutator F :=
        (hcommutator_coordinates z).2 ⟨y, rfl⟩
      have hz_ker : z ∈ psi.ker :=
        Abelianization.commutator_subset_ker psi hz_commutator
      exact hz_ker
    have hforget_second (x y : K) : phi (r x y) = phi (r x 0) := by
      have hmul : r x 0 * r 0 y = r x y := by
        simpa using hr_mul x 0 0 y
      rw [← hmul, map_mul, hcentral_image, mul_one]
    have hroot_sq (x : K) : phi (r x 0) ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hr_mul]
      simpa only [CharTwo.add_self_eq_zero, zero_add] using
        hcentral_image (x * pi x)
    have hscale (x : K) : phi (r ((s : K) * x) 0) = phi (r x 0) := by
      have hconj : t s * r x 0 * (t s)⁻¹ = r ((s : K) * x) 0 := by
        apply Subtype.ext
        change SuzukiTorusGL m s * SuzukiRootGL m x 0 *
          (SuzukiTorusGL m s)⁻¹ = SuzukiRootGL m ((s : K) * x) 0
        simpa only [mul_zero] using htorus_conjugation x 0 s
      rw [← hconj, map_mul, map_mul, map_inv]
      calc
        phi (t s) * phi (r x 0) * (phi (t s))⁻¹ =
            phi (r x 0) * phi (t s) * (phi (t s))⁻¹ := by
          rw [mul_comm (phi (t s)) (phi (r x 0))]
        _ = phi (r x 0) := mul_inv_cancel_right _ _
    have hs_add_one : (s : K) + 1 ≠ 0 := by
      intro hzero
      apply hs
      apply Units.ext
      simpa only [CharTwo.neg_eq, Units.val_one] using
        add_eq_zero_iff_eq_neg.mp hzero
    let x : K := ((s : K) + 1)⁻¹ * a
    have hfirst : x + (s : K) * x = a := by
      dsimp only [x]
      rw [show ((s : K) + 1)⁻¹ * a + (s : K) *
          (((s : K) + 1)⁻¹ * a) =
        (((s : K) + 1)⁻¹ * ((s : K) + 1)) * a by ring]
      rw [inv_mul_cancel₀ hs_add_one, one_mul]
    have hproduct_image : phi (r x 0 * r ((s : K) * x) 0) = 1 := by
      rw [map_mul, hscale, ← pow_two, hroot_sq]
    rw [hr_mul, hfirst, hforget_second] at hproduct_image
    rw [hforget_second]
    exact hproduct_image
  have htorus_pow (u : Kˣ) :
      phi ⟨SuzukiTorusGL m u, htorus_mem u⟩ ^ (q - 1) = 1 := by
    have hH_le_S : H ≤ S := by
      change Subgroup.closure {A | ∃ v : Kˣ, A = SuzukiTorusGL m v} ≤
        Subgroup.closure (SuzukiMatrixGeneratorSet m)
      rw [Subgroup.closure_le]
      intro A hA
      exact Subgroup.subset_closure (Or.inr (Or.inl hA))
    let inclusion : H →* S := Subgroup.inclusion hH_le_S
    have htorus_eq :
        (⟨SuzukiTorusGL m u, htorus_mem u⟩ : S) = inclusion (e u) := by
      apply Subtype.ext
      exact (he u).symm
    have h_units_card : Nat.card Kˣ = q - 1 := by
      rw [Nat.card_units, hq_card]
    have hu : u ^ (q - 1) = 1 := by
      rw [← h_units_card]
      exact pow_card_eq_one'
    calc
      phi ⟨SuzukiTorusGL m u, htorus_mem u⟩ ^ (q - 1) =
          phi (⟨SuzukiTorusGL m u, htorus_mem u⟩ ^ (q - 1)) :=
        (map_pow phi _ _).symm
      _ = phi ((inclusion (e u)) ^ (q - 1)) := by rw [htorus_eq]
      _ = phi (inclusion ((e u) ^ (q - 1))) :=
        congrArg phi ((map_pow inclusion (e u) (q - 1)).symm)
      _ = phi (inclusion (e (u ^ (q - 1)))) :=
        congrArg (fun z : H => phi (inclusion z))
          ((map_pow e u (q - 1)).symm)
      _ = 1 := by rw [hu, map_one, map_one, map_one]
  have hq_even : Even q := by
    refine ⟨2 ^ (2 * m), ?_⟩
    dsimp only [q]
    rw [show 2 * m + 1 = 1 + 2 * m by omega, pow_add]
    omega
  have hcoprime : Nat.Coprime 2 (q - 1) := by
    exact (Nat.Even.sub_odd (m := q) (n := 1) (by
      dsimp only [q]
      exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) hq_even odd_one).coprime_two_left
  have hweyl_image : phi ⟨SuzukiWeylGL m, hweyl_mem⟩ = 1 := by
    let w : S := ⟨SuzukiWeylGL m, hweyl_mem⟩
    let r : K → K → S := fun a b =>
      ⟨SuzukiRootGL m a b, hroot_mem a b⟩
    let t : Kˣ → S := fun u => ⟨SuzukiTorusGL m u, htorus_mem u⟩
    change phi w = 1
    have hw_mul_self : w * w = 1 := by
      apply Subtype.ext
      exact suzukiWeylGL_mul_self m
    have hw_pow_two : phi w ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hw_mul_self, map_one]
    have hnorm :
        (0 : K) * 1 + pi 0 * (0 : K) ^ 2 + pi 1 ≠ 0 := by simp
    rcases suzukiWeyl_root_weyl_bruhat m pi hpi_sq hpi 0 1 hnorm with
      ⟨c, d, a, b, u, hbruhat⟩
    have hbruhat_S :
        w * r 0 1 * w = r c d * t u * w * r a b := by
      apply Subtype.ext
      exact hbruhat
    have hbruhat_image := congrArg phi hbruhat_S
    have hr_image (x y : K) : phi (r x y) = 1 := by
      exact hroot_image x y
    have hw_eq_torus : phi w = phi (t u) := by
      apply mul_right_cancel (b := phi w)
      simpa only [map_mul, hr_image, one_mul, mul_one] using hbruhat_image
    have hw_pow_q_sub_one : phi w ^ (q - 1) = 1 := by
      rw [hw_eq_torus]
      exact htorus_pow u
    have horder : orderOf (phi w) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcoprime
        (orderOf_dvd_of_pow_eq_one hw_pow_two)
        (orderOf_dvd_of_pow_eq_one hw_pow_q_sub_one)
    exact orderOf_eq_one_iff.mp horder
  have htorus_image (u : Kˣ) :
      phi ⟨SuzukiTorusGL m u, htorus_mem u⟩ = 1 := by
    let w : S := ⟨SuzukiWeylGL m, hweyl_mem⟩
    let t : Kˣ → S := fun v => ⟨SuzukiTorusGL m v, htorus_mem v⟩
    change phi (t u) = 1
    have hH_le_S : H ≤ S := by
      change Subgroup.closure {A | ∃ v : Kˣ, A = SuzukiTorusGL m v} ≤
        Subgroup.closure (SuzukiMatrixGeneratorSet m)
      rw [Subgroup.closure_le]
      intro A hA
      exact Subgroup.subset_closure (Or.inr (Or.inl hA))
    let inclusion : H →* S := Subgroup.inclusion hH_le_S
    have ht_eq_inclusion (v : Kˣ) : t v = inclusion (e v) := by
      apply Subtype.ext
      exact (he v).symm
    have ht_inv : t u⁻¹ = (t u)⁻¹ := by
      calc
        t u⁻¹ = inclusion (e u⁻¹) := ht_eq_inclusion u⁻¹
        _ = inclusion ((e u)⁻¹) := by rw [map_inv]
        _ = (inclusion (e u))⁻¹ := by rw [map_inv]
        _ = (t u)⁻¹ := congrArg Inv.inv (ht_eq_inclusion u).symm
    have hconj : w * t u * w = t u⁻¹ := by
      apply Subtype.ext
      exact suzukiWeylGL_conj_torus m u
    have hconj_image := congrArg phi hconj
    have hw_image : phi w = 1 := by exact hweyl_image
    have ht_eq_inv : phi (t u) = phi (t u⁻¹) := by
      simpa only [map_mul, hw_image, one_mul, mul_one] using hconj_image
    have ht_pow_two : phi (t u) ^ 2 = 1 := by
      calc
        phi (t u) ^ 2 = phi (t u) * phi (t u) := pow_two _
        _ = phi (t u) * phi (t u⁻¹) := congrArg (phi (t u) * ·) ht_eq_inv
        _ = phi (t u) * (phi (t u))⁻¹ := by rw [ht_inv, map_inv]
        _ = 1 := mul_inv_cancel _
    have horder : orderOf (phi (t u)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcoprime
        (orderOf_dvd_of_pow_eq_one ht_pow_two)
        (orderOf_dvd_of_pow_eq_one (htorus_pow u))
    exact orderOf_eq_one_iff.mp horder
  have hgenerator_image :
      ∀ g : S, g.1 ∈ SuzukiMatrixGeneratorSet m → phi g = 1 := by
    intro g hg
    rcases hg with ⟨a, b, hab⟩ | ⟨u, hu⟩ | hw
    · have hg_eq : g = ⟨SuzukiRootGL m a b, hroot_mem a b⟩ := Subtype.ext hab
      rw [hg_eq]
      exact hroot_image a b
    · have hg_eq : g = ⟨SuzukiTorusGL m u, htorus_mem u⟩ := Subtype.ext hu
      rw [hg_eq]
      exact htorus_image u
    · have hg_eq : g = ⟨SuzukiWeylGL m, hweyl_mem⟩ := Subtype.ext hw
      rw [hg_eq]
      exact hweyl_image
  apply Group.isPerfect_def.mpr
  rw [← Abelianization.ker_of S]
  change phi.ker = ⊤
  apply top_unique
  have hclosure :
      Subgroup.closure (S.subtype ⁻¹' SuzukiMatrixGeneratorSet m) =
        (⊤ : Subgroup S) := by
    change Subgroup.closure
      ((Subgroup.closure (SuzukiMatrixGeneratorSet m)).subtype ⁻¹'
        SuzukiMatrixGeneratorSet m) = ⊤
    exact Subgroup.closure_preimage_eq_top (SuzukiMatrixGeneratorSet m)
  rw [← hclosure]
  exact (Subgroup.closure_le (K := phi.ker)).2 fun g hg => hgenerator_image g hg

/-- The root-torus point stabilizer from XI.3.3 is solvable. -/
private theorem suzukiMatrixGroup_pointStabilizer_isSolvable
    (m : ℕ) (hm : 0 < m) :
    let K := BinaryGaloisField (2 * m + 1)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    let B : Subgroup (GL (Fin 4) K) := F ⊔ H
    let U : Subgroup (SuzukiMatrixGroup m) :=
      B.comap (SuzukiMatrixGroup m).subtype
    Group.IsSolvable U := by
  classical
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    binaryGaloisField_tits_formula_sq m pi hpi
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  let U : Subgroup (SuzukiMatrixGroup m) :=
    B.comap (SuzukiMatrixGroup m).subtype
  change Group.IsSolvable U
  rcases huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_, _, hF_pgroup, _, _, _, _, _, _, _, _, htorus_equiv, _, _, _⟩
  obtain ⟨e, _⟩ := htorus_equiv
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF_nilpotent : Group.IsNilpotent F := hF_pgroup.isNilpotent
  have hF_solvable : Group.IsSolvable F := by
    let _ : Group.IsNilpotent F := hF_nilpotent
    infer_instance
  have hH_solvable : Group.IsSolvable H := by
    let _ : Group.IsSolvable Kˣ := inferInstance
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.symm.toMonoidHom) e.symm.injective
  have hnormalizer : H ≤ Subgroup.normalizer F :=
    suzukiTorusClosure_le_normalizer_rootClosure m pi hpi_sq hpi
  have hF_le_B : F ≤ B := le_sup_left
  have hH_le_B : H ≤ B := le_sup_right
  let FB : Subgroup B := F.subgroupOf B
  have hB_le_normalizer : B ≤ Subgroup.normalizer F :=
    sup_le Subgroup.le_normalizer hnormalizer
  let _ : FB.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB_le_normalizer
  have hFB_solvable : Group.IsSolvable FB := by
    let eFB : FB ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_B
    let _ : Group.IsSolvable F := hF_solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := eFB.toMonoidHom) eFB.injective
  let quotientFromH : H →* B ⧸ FB :=
    (QuotientGroup.mk' FB).comp (Subgroup.inclusion hH_le_B)
  have hquotientFromH_surjective : Function.Surjective quotientFromH := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective FB z
    have hw_product :
        (w : GL (Fin 4) K) ∈
          (F : Set (GL (Fin 4) K)) * (H : Set (GL (Fin 4) K)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F H hnormalizer]
      exact w.property
    rcases hw_product with ⟨f, hf, h, hh, hfh⟩
    let hH : H := ⟨h, hh⟩
    refine ⟨hH, ?_⟩
    let fB : B := ⟨f, hF_le_B hf⟩
    let hB : B := ⟨h, hH_le_B hh⟩
    change QuotientGroup.mk' FB hB = QuotientGroup.mk' FB w
    have hfh_B : fB * hB = w := Subtype.ext hfh
    rw [← hfh_B, map_mul]
    have hf_FB : fB ∈ FB := hf
    have hmk_fB : QuotientGroup.mk' FB fB = 1 :=
      (QuotientGroup.eq_one_iff _).2 hf_FB
    rw [hmk_fB, one_mul]
  have hquotient_solvable : Group.IsSolvable (B ⧸ FB) := by
    let _ : Group.IsSolvable H := hH_solvable
    exact Group.isSolvable_of_surjective
      (f := quotientFromH) hquotientFromH_surjective
  have hB_solvable : Group.IsSolvable B := by
    let _ : Group.IsSolvable FB := hFB_solvable
    let _ : Group.IsSolvable (B ⧸ FB) := hquotient_solvable
    exact Group.isSolvable_of_ker_le_range FB.subtype (QuotientGroup.mk' FB) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hF_le_S : F ≤ SuzukiMatrixSubgroup m := by
    change Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b} ≤
      Subgroup.closure (SuzukiMatrixGeneratorSet m)
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_S : H ≤ SuzukiMatrixSubgroup m := by
    change Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u} ≤
      Subgroup.closure (SuzukiMatrixGeneratorSet m)
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hB_le_S : B ≤ SuzukiMatrixSubgroup m := sup_le hF_le_S hH_le_S
  let eU : U ≃* B := Subgroup.subgroupOfEquivOfLe hB_le_S
  let _ : Group.IsSolvable B := hB_solvable
  exact Group.isSolvable_of_isSolvable_injective (f := eU.toMonoidHom) eU.injective

/-- The faithful two-transitive ovoid action and its solvable point stabilizer
force the concrete perfect Suzuki group to be simple. -/
private theorem suzukiMatrixGroup_isSimple
    (m : ℕ) (hm : 0 < m) :
    IsSimpleGroup (SuzukiMatrixGroup m) := by
  classical
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  let U : Subgroup (SuzukiMatrixGroup m) :=
    B.comap (SuzukiMatrixGroup m).subtype
  rcases huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨h_action, _, h_faithful, h_two_transitive, _, _, _, h_stabilizer⟩
  let rho : SuzukiMatrixGroup m →*
      LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (SuzukiMatrixGroup m).subtype
  let _ : MulAction (SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) rho
  let Omega : SubMulAction (SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        exact h_action g z hz }
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  let _ : FaithfulSMul (SuzukiMatrixGroup m) Omega :=
    faithfulSMul_iff.mpr (by
      intro g hg
      apply h_faithful g
      intro z hz
      let zO : Omega := ⟨z, hz⟩
      exact congrArg Subtype.val (hg zO))
  have htwo :
      MulAction.IsMultiplyPretransitive (SuzukiMatrixGroup m) Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab' : (a : ℙ K (Fin 4 → K)) ≠ b := by
      intro h
      exact hab (Subtype.ext h)
    have hcd' : (c : ℙ K (Fin 4 → K)) ≠ d := by
      intro h
      exact hcd (Subtype.ext h)
    rcases h_two_transitive (a : ℙ K (Fin 4 → K)) b c d
        a.property b.property c.property d.property hab' hcd' with
      ⟨g, hga, hgb⟩
    exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
  let _ : MulAction.IsMultiplyPretransitive
      (SuzukiMatrixGroup m) Omega 2 := htwo
  let _ : MulAction.IsPreprimitive (SuzukiMatrixGroup m) Omega :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  let _ : MulAction.IsQuasiPreprimitive (SuzukiMatrixGroup m) Omega :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hroot_mem :
      SuzukiRootGL m (1 : K) 0 ∈ SuzukiMatrixSubgroup m :=
    Subgroup.subset_closure (Or.inl ⟨1, 0, rfl⟩)
  let rootOne : SuzukiMatrixGroup m :=
    ⟨SuzukiRootGL m (1 : K) 0, hroot_mem⟩
  have hrootOne_ne : rootOne ≠ 1 := by
    intro hrootOne
    have hval := congrArg Subtype.val hrootOne
    have hentry := congrArg
      (fun A : GL (Fin 4) K =>
        (A : Matrix (Fin 4) (Fin 4) K) 0 1) hval
    simp [rootOne, SuzukiRootGL, SuzukiRootMatrix] at hentry
  let _ : Nontrivial (SuzukiMatrixGroup m) :=
    nontrivial_iff_exists_ne 1 |>.2 ⟨rootOne, hrootOne_ne⟩
  have hU_eq_stabilizer :
      U = MulAction.stabilizer (SuzukiMatrixGroup m) pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ B ↔
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (h_stabilizer g).symm
  have hU_solvable : Group.IsSolvable U :=
    suzukiMatrixGroup_pointStabilizer_isSolvable m hm
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro N hN_normal
  by_cases hN_bot : N = ⊥
  · exact Or.inl hN_bot
  · refine Or.inr ?_
    let _ : N.Normal := hN_normal
    have hfixed_ne_univ : MulAction.fixedPoints N Omega ≠ Set.univ := by
      intro hfixed
      apply hN_bot
      rw [eq_bot_iff]
      intro n hn
      have hfix_all : ∀ omega : Omega, n • omega = omega := by
        intro omega
        have homega : omega ∈ MulAction.fixedPoints N Omega := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp homega ⟨n, hn⟩
      have hn_one : n = 1 :=
        FaithfulSMul.eq_of_smul_eq_smul (m₁ := n)
          (m₂ := (1 : SuzukiMatrixGroup m)) (by
            intro omega
            calc
              n • omega = omega := hfix_all omega
              _ = (1 : SuzukiMatrixGroup m) • omega :=
                (one_smul _ omega).symm)
      exact Subgroup.mem_bot.mpr hn_one
    have hN_transitive : MulAction.IsPretransitive N Omega :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
    let _ : MulAction.IsPretransitive N Omega := hN_transitive
    let quotientFromU : U →* SuzukiMatrixGroup m ⧸ N :=
      (QuotientGroup.mk' N).comp U.subtype
    have hquotientFromU_surjective : Function.Surjective quotientFromU := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
      obtain ⟨n, hn⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq N Omega inferInstance
          inferInstance pinfO (g • pinfO)
      have hn' : (n : SuzukiMatrixGroup m) • pinfO = g • pinfO := hn
      let uval : SuzukiMatrixGroup m := (n : SuzukiMatrixGroup m)⁻¹ * g
      have hu_stabilizer :
          uval ∈ MulAction.stabilizer (SuzukiMatrixGroup m) pinfO := by
        rw [MulAction.mem_stabilizer_iff]
        change ((n : SuzukiMatrixGroup m)⁻¹ * g) • pinfO = pinfO
        rw [mul_smul, ← hn']
        exact inv_smul_smul (n : SuzukiMatrixGroup m) pinfO
      have hu_U : uval ∈ U := by
        rw [hU_eq_stabilizer]
        exact hu_stabilizer
      let u : U := ⟨uval, hu_U⟩
      refine ⟨u, ?_⟩
      change QuotientGroup.mk' N uval = QuotientGroup.mk' N g
      apply QuotientGroup.eq_iff_div_mem.mpr
      change ((n : SuzukiMatrixGroup m)⁻¹ * g) / g ∈ N
      rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
      exact N.inv_mem n.property
    have hquotient_solvable :
        Group.IsSolvable (SuzukiMatrixGroup m ⧸ N) := by
      let _ : Group.IsSolvable U := hU_solvable
      exact Group.isSolvable_of_surjective
        (f := quotientFromU) hquotientFromU_surjective
    by_contra hN_top
    let _ : Nontrivial (SuzukiMatrixGroup m ⧸ N) :=
      QuotientGroup.nontrivial_iff.mpr hN_top
    let _ : Group.IsPerfect (SuzukiMatrixGroup m) :=
      suzukiMatrixGroup_isPerfect m hm
    let _ : Group.IsPerfect (SuzukiMatrixGroup m ⧸ N) := inferInstance
    exact Group.IsPerfect.not_isSolvable
      (SuzukiMatrixGroup m ⧸ N) hquotient_solvable

/-- The XI.3.3 order formula is prime to `3`. -/
private theorem suzukiMatrixGroup_card_not_dvd_three
    (m : ℕ) (hm : 0 < m) :
    ¬ 3 ∣ Nat.card (SuzukiMatrixGroup m) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  rcases huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨_, _, _, _, _, _, h_order, _⟩
  let q := 2 ^ (2 * m + 1)
  have h_order' :
      Nat.card (SuzukiMatrixGroup m) =
        (q ^ 2 + 1) * q ^ 2 * (q - 1) := by
    simpa only [q] using h_order
  have hfour_pow_mod : 4 ^ m % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ m) 1
    simpa only [one_pow] using
      (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq_eq : q = 2 * 4 ^ m := by
    dsimp only [q]
    rw [show 2 * m + 1 = 1 + 2 * m by omega, pow_add, pow_mul]
    norm_num
  have hq_mod : q % 3 = 2 := by
    rw [hq_eq, Nat.mul_mod, hfour_pow_mod]
  have hq_sq_mod : q ^ 2 % 3 = 1 := by
    calc
      q ^ 2 % 3 = (q % 3) ^ 2 % 3 := Nat.pow_mod q 2 3
      _ = 1 := by rw [hq_mod]
  have hq_sub_one_mod : (q - 1) % 3 = 1 := by
    omega
  intro hthree
  rw [h_order'] at hthree
  rcases Nat.prime_three.dvd_mul.mp hthree with hab | hc
  · rcases Nat.prime_three.dvd_mul.mp hab with ha | hb
    · have hzero := Nat.dvd_iff_mod_eq_zero.mp ha
      rw [Nat.add_mod, hq_sq_mod] at hzero
      norm_num at hzero
    · have hzero := Nat.dvd_iff_mod_eq_zero.mp hb
      omega
  · have hzero := Nat.dvd_iff_mod_eq_zero.mp hc
    omega

/-- Huppert-Blackburn XI.3.6: `Sz(q)` is simple and its order is prime to `3`. -/
public theorem huppert_blackburn_XI_3_6 (m : ℕ) (hm : 0 < m) :
    IsSimpleGroup (SuzukiMatrixGroup m) ∧
      ¬ 3 ∣ Nat.card (SuzukiMatrixGroup m) := by
  have h_simple : IsSimpleGroup (SuzukiMatrixGroup m) := by
    exact suzukiMatrixGroup_isSimple m hm
  have h_card : ¬ 3 ∣ Nat.card (SuzukiMatrixGroup m) := by
    exact suzukiMatrixGroup_card_not_dvd_three m hm
  exact ⟨h_simple, h_card⟩

end External
end CFSG.BenderSuzuki
