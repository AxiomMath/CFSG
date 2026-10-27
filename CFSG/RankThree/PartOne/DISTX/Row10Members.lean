module

public import CFSG.RankThree.PartOne.DISTX.LemmaA
public import CFSG.RankThree.PartOne.S13K.Sp6Four

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.DISTX

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.KFQ
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

omit [Field K] [Finite K] [CharP K 2] in
theorem eq_one_of_eq_inv {M : Type*} [Group M] (hp : p.Prime) (hp2 : p ≠ 2) {x : M}
    (hxp : x ^ p = 1) (h : x = x⁻¹) : x = 1 := by
  have h2 : x ^ 2 = 1 := by
    have : x * x = 1 := mul_eq_one_iff_eq_inv.mpr h
    simpa [sq] using this
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h3 : x ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨h2, hxp⟩
  simpa [hcop.gcd_eq_one] using h3

theorem exists_coord_one (hp : p.Prime) (hp2 : p ≠ 2) {π : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → Bool} (hs : ReflShape π ε) {a : Fin 3 → (Qext K)ˣ} (ha : ∀ i, a i ^ p = 1)
    (h : sact π ε a = a⁻¹) : ∃ j, a j = 1 := by
  rcases hs with ⟨rfl, i, hi, hrest⟩ | ⟨a₀, b₀, c₀, hab, hca, hcb, rfl, hεab, hεc⟩
  · obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := (by decide : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i) i
    refine ⟨j, eq_one_of_eq_inv hp hp2 (ha j) ?_⟩
    have h1 := congrFun h j
    simpa [sact_apply, hrest j hj] using h1
  · refine ⟨c₀, eq_one_of_eq_inv hp hp2 (ha c₀) ?_⟩
    have h1 := congrFun h c₀
    have hc : Equiv.swap a₀ b₀ c₀ = c₀ := Equiv.swap_apply_of_ne_of_ne hca hcb
    simpa [sact_apply, hc, hεc] using h1

theorem swap_sign : ∀ j i l : Fin 3, (Equiv.swap j i).symm l = j ↔ l = i := by decide +kernel

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem exists_fix_sign (C : Sp6Ctx p A c L E f K) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    (htL : t ∈ torusImage E L) {e : E} (he : t e = e⁻¹) :
    ∃ j : Fin 3, C.tSgn 1 (fun k => decide (k = j)) e = e := by
  obtain ⟨π, ε, hshape, rfl⟩ := C.exists_shape ht htL
  obtain ⟨a, ha, k, rfl⟩ := C.exists_decomp_eT e
  rw [C.tSgn_apply_decomp] at he
  have hmain : ((C.eT a ha : E) : G) * ((C.eT (sact π ε a) (sact_pow ha) : E) : G) = 1 := by
    have hX₀L : ((C.eT a ha : E) : G) ∈ L := C.phi_mem_L _
    have hX₁L : ((C.eT (sact π ε a) (sact_pow ha) : E) : G) ∈ L := C.phi_mem_L _
    have heq : ((C.eT (sact π ε a) (sact_pow ha) : E) : G) * c ^ k =
        (((C.eT a ha : E) : G) * c ^ k)⁻¹ := by
      have := congrArg Subtype.val he
      simpa [Sp6Ctx.cE] using this
    have hc : ((C.eT a ha : E) : G) * c ^ k = c ^ k * ((C.eT a ha : E) : G) :=
      C.R.commute_zpow hX₀L k
    obtain ⟨d, hd⟩ : ∃ d : G, d = c ^ k := ⟨_, rfl⟩
    rw [← hd] at heq hc
    generalize ((C.eT a ha : E) : G) = X₀ at *
    generalize ((C.eT (sact π ε a) (sact_pow ha) : E) : G) = X₁ at *
    have h1 : X₀ * X₁ = d⁻¹ * d⁻¹ := by
      calc X₀ * X₁ = X₀ * (X₁ * d) * d⁻¹ := by group
        _ = X₀ * (d * X₀)⁻¹ * d⁻¹ := by rw [heq, hc]
        _ = X₀ * (X₀⁻¹ * d⁻¹) * d⁻¹ := by rw [mul_inv_rev]
        _ = d⁻¹ * d⁻¹ := by group
    have hdz : d ∈ Subgroup.zpowers c := hd ▸ Subgroup.zpow_mem_zpowers c k
    have hmem : X₀ * X₁ ∈ Subgroup.zpowers c ⊓ L := by
      refine ⟨?_, L.mul_mem hX₀L hX₁L⟩
      rw [h1]
      exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem hdz)
        ((Subgroup.zpowers c).inv_mem hdz)
    rw [Sec12Three.zpowers_inf_eq_bot C.h.prime (Sec12Three.orderOf_c C.h) C.hcL,
      Subgroup.mem_bot] at hmem
    exact hmem
  have hsa : sact π ε a = a⁻¹ := by
    have hX : C.eT (sact π ε a) (sact_pow ha) = (C.eT a ha)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_inv]
      exact eq_inv_of_mul_eq_one_right hmain
    rw [C.eT_inv] at hX
    exact C.eT_injective hX
  obtain ⟨j, hj⟩ := exists_coord_one C.h.prime C.hp2 hshape ha hsa
  refine ⟨j, ?_⟩
  rw [C.tSgn_apply_decomp]
  refine congrArg (fun x => x * C.cE ^ k) (C.eT_congr ?_)
  funext l
  rw [sact_S]
  by_cases hl : l = j
  · subst hl
    simp [hj]
  · simp [hl]

theorem tSgn_conj_sign (C : Sp6Ctx p A c L E f K) (j i : Fin 3) :
    C.tSgn (Equiv.swap j i) (fun _ => false) * C.tSgn 1 (fun k => decide (k = j)) *
        (C.tSgn (Equiv.swap j i) (fun _ => false))⁻¹ = C.tSgn 1 (fun k => decide (k = i)) := by
  have hconj := sg10_conj_perm (K := K) (Equiv.swap j i) 1 (fun k => decide (k = j))
  have hperm : Equiv.swap j i * 1 * (Equiv.swap j i)⁻¹ = 1 := by simp
  have hsign : (fun l => (fun k => decide (k = j)) ((Equiv.swap j i).symm l)) =
      fun l => decide (l = i) := by
    funext l
    simp only [decide_eq_decide]
    exact swap_sign j i l
  rw [hperm, hsign] at hconj
  unfold Sp6Ctx.tSgn
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change C.phi (sg10 _ _) * C.phi (sg10 _ _) * (C.phi (sg10 _ _))⁻¹ = C.phi (sg10 1 _)
  rw [← map_inv, ← map_mul, ← map_mul, hconj]

theorem commute_z_sign (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hSame : KFCommSame)
    (C : Sp6Ctx p A c L E f K) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A)
    {z : MulAut E} (hz : z ∈ reflectionSet p E) (hLz : KFLiftAt p E z)
    (hzc : z C.cE = C.cE⁻¹) (hzL : ∀ g ∈ torusImage E L, z * g = g * z)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (h1D : conjAut E w hw * z * (conjAut E w hw)⁻¹ ∈ reflectionSet p E)
    (h1L : conjAut E w hw * z * (conjAut E w hw)⁻¹ ∈ torusImage E L)
    (h2L : (conjAut E w hw)⁻¹ * z * conjAut E w hw ∈ torusImage E L) (i : Fin 3) :
    kZero p E z ≤
      Subgroup.centralizer (kZero p E (C.tSgn 1 (fun k => decide (k = i))) : Set G) := by
  have hp := C.h.prime
  set a := conjAut E w hw with ha
  have hc₁ : (a * z * a⁻¹) (a C.cE) = (a C.cE)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hzc, map_inv]
  obtain ⟨j, hj⟩ := exists_fix_sign C h1D h1L hc₁
  set σ := Equiv.swap j i with hσ
  have hg1 := sg10_hg1 C.hpq' σ (fun _ => false)
  have hg2 := C.hg2_of_hg1 hg1
  set g : G := C.phi (sg10 σ (fun _ => false)) with hg
  have hgN : g ∈ Subgroup.normalizer (E : Set G) := C.mem_normalizer hg1 hg2
  have hSσ : C.tSgn σ (fun _ => false) ∈ torusImage E L := C.tSgn_mem_torusImage _ _
  have hw₂ : g * w ∈ Subgroup.normalizer (E : Set G) := mul_mem hgN hw
  have hconj₂ : conjAut E (g * w) hw₂ = C.tSgn σ (fun _ => false) * a := by
    unfold conjAut
    have : (⟨g * w, hw₂⟩ : Subgroup.normalizer (E : Set G)) = ⟨g, hgN⟩ * ⟨w, hw⟩ := rfl
    rw [this, map_mul]
    rfl
  have hX : conjBy (g * w) L ∈ thetaCompZeroStarE p E :=
    conjBy_mem_thetaCompZeroStarE hp hw₂ hF13.inZeroStar
  have hcX : conjBy (g * w) L ∈ thetaComponentsAt p ((g * w) * c * (g * w)⁻¹) :=
    conjBy_mem_thetaComponentsAt hp (g * w) c C.h.L_mem.2
  have hsX : z ∈ torusImage E (conjBy (g * w) L) := by
    rw [torusImage_conjBy E L hw₂]
    refine Subgroup.mem_map.mpr ⟨a⁻¹ * z * a, h2L, ?_⟩
    show conjAut E (g * w) hw₂ * (a⁻¹ * z * a) * (conjAut E (g * w) hw₂)⁻¹ = z
    rw [hconj₂]
    have hcz : z * C.tSgn σ (fun _ => false) = C.tSgn σ (fun _ => false) * z := hzL _ hSσ
    have hb : C.tSgn σ (fun _ => false) * z * (C.tSgn σ (fun _ => false))⁻¹ = z := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcz.symm
    calc (C.tSgn σ (fun _ => false) * a) * (a⁻¹ * z * a) * (C.tSgn σ (fun _ => false) * a)⁻¹
        = C.tSgn σ (fun _ => false) * z * (C.tSgn σ (fun _ => false))⁻¹ := by group
      _ = z := hb
  have hcXt : (g * w) * c * (g * w)⁻¹ ∈ autFixedInG E (C.tSgn 1 (fun k => decide (k = i))) := by
    have hval : ((conjAut E (g * w) hw₂ C.cE : E) : G) = (g * w) * c * (g * w)⁻¹ :=
      Equivariance.coe_conjAut hw₂ C.cE
    rw [← hval, mem_autFixedInG_iff_apply, hconj₂, ← tSgn_conj_sign C j i]
    change (C.tSgn σ (fun _ => false) * C.tSgn 1 (fun k => decide (k = j)) *
      (C.tSgn σ (fun _ => false))⁻¹) ((C.tSgn σ (fun _ => false) * a) C.cE) =
        (C.tSgn σ (fun _ => false) * a) C.cE
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [hj]
  have hSi := C.tSgn_mem_torusImage (1 : Equiv.Perm (Fin 3)) (fun k => decide (k = i))
  exact commute_of_member_centre hS hRe hSame C.h hF13 hT hEA hz (C.S_mem_reflectionSet hF13 i)
    hLz (KFAt.toLiftAt (C.kfAt_tSgn_S i)) (ne_of_inverts_c C.h hzc hSi) (hzL _ hSi) hX hsX hcX hcXt
    (fun h => C.h.c_ne_one (conj_eq_one_iff.1 h))

end CFSG.RankThree.PartOne.DISTX
