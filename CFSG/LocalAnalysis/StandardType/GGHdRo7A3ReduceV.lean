module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVIrr

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7A3ReduceVAux_move_le_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {M : Submodule (ZMod 3) V} (a : V ≃ₗ[ZMod 3] V) :
    ggLinMove a ≤ M ↔ ∀ v, a v - v ∈ M := by
  rw [ggLinMove]
  constructor
  · intro h v; exact h ⟨v, rfl⟩
  · rintro h w ⟨v, rfl⟩; exact h v

private theorem hdRo7A3ReduceVAux_mem_map {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {u : Fin m → ZMod 3}
    (hu : u ∈ a3Aug 3 m) : θ u ∈ (a3Aug 3 m).map θ := by
  rw [Submodule.mem_map]
  exact ⟨u, hu, rfl⟩

private theorem hdRo7A3ReduceVAux_aug_eq_span_diff {m : ℕ} (i : Fin m) :
    a3Aug 3 m =
      Submodule.span (ZMod 3) (Set.range fun k : Fin m =>
        (Pi.single k 1 - Pi.single i 1 : Fin m → ZMod 3)) := by
  apply le_antisymm
  · intro v hv
    change ∑ k, v k = 0 at hv
    have hsum : (∑ k : Fin m, v k • (Pi.single k 1 : Fin m → ZMod 3)) = v := by
      have h := (Pi.basisFun (ZMod 3) (Fin m)).sum_repr v
      simpa [Pi.basisFun_repr, Pi.basisFun_apply] using h
    have hsplit : (∑ k : Fin m, v k • (Pi.single k 1 - Pi.single i 1 : Fin m → ZMod 3)) = v := by
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hv, zero_smul, sub_zero]
      exact hsum
    rw [← hsplit]
    exact Submodule.sum_mem _ (fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact a3_single_sub_mem k i

private theorem hdRo7A3ReduceVAux_z_ne_zero {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    (hfr : A3Frame 3 m θ z) : z ≠ 0 := by
  rcases hfr.2.2 with ⟨-, hz⟩ | ⟨-, h⟩
  · exact hz
  · intro hz0
    exact h 0 (Submodule.zero_mem _) (by rw [map_zero, hz0])

private theorem hdRo7A3ReduceVAux_theta_const {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {c : ZMod 3}
    (hM1 : θ (fun _ => 1) = 0) : θ (fun _ : Fin m => c) = 0 := by
  rw [show (fun _ : Fin m => c) = c • (fun _ => (1 : ZMod 3)) by
    funext q; simp, map_smul, hM1, smul_zero]

private theorem hdRo7A3ReduceVAux_sup_span {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    (hfr : A3Frame 3 m θ z) :
    (a3Aug 3 m).map θ ⊔ Submodule.span (ZMod 3) {z} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 v
  exact Submodule.add_mem_sup (hdRo7A3ReduceVAux_mem_map hu)
    (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton z)))

private theorem hdRo7A3ReduceVAux_val_self {m : ℕ} {a b : Fin m} (h : a ≠ b) :
    ((Pi.single a 1 - Pi.single b 1 : Fin m → ZMod 3) a) = 1 := by
  simp [Pi.sub_apply, h]

private theorem hdRo7A3ReduceVAux_val_snd {m : ℕ} {a b : Fin m} (h : a ≠ b) :
    ((Pi.single a 1 - Pi.single b 1 : Fin m → ZMod 3) b) = -1 := by
  simp [Pi.sub_apply, Ne.symm h]

private theorem hdRo7A3ReduceVAux_val_other {m : ℕ} {a b q : Fin m} (h1 : q ≠ a)
    (h2 : q ≠ b) : ((Pi.single a 1 - Pi.single b 1 : Fin m → ZMod 3) q) = 0 := by
  simp [Pi.sub_apply, h1, h2]

private theorem hdRo7A3ReduceVAux_psi_ij {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    ((Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) i) -
      ((Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) j) = 2 := by
  rw [hdRo7A3ReduceVAux_val_self hij, hdRo7A3ReduceVAux_val_snd hij]
  norm_num

private theorem hdRo7A3ReduceVAux_psi_ik {m : ℕ} {i j k : Fin m}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    ((Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) i) -
      ((Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) k) = 1 := by
  rw [hdRo7A3ReduceVAux_val_self hij, hdRo7A3ReduceVAux_val_other hki hkj]
  norm_num

private theorem hdRo7A3ReduceVAux_transp {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hfr : A3Frame 3 m θ z) (hpm : 3 ∣ m) (hm : 3 ≤ m)
    (hPH : ∀ a, A3P 3 m θ z a → a ∈ H) {i j : Fin m} (hij : i ≠ j) :
    ∃ (t : V ≃ₗ[ZMod 3] V) (ψ : Module.Dual (ZMod 3) V),
      t ∈ H ∧ A3P 3 m θ z t ∧ GGLinRefl t ∧
      ReflData t (θ (Pi.single i 1 - Pi.single j 1)) ψ ∧ t z = z ∧
      (∀ u ∈ a3Aug 3 m, ψ (θ u) = u i - u j) ∧ ψ z = 0 := by
  obtain ⟨t, ψ, htu, htz, hψ, hψz, htv, hrefl⟩ :=
    a3_transp (p := 3) rfl hfr hpm hm hij
  have hmem : (Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) ∈ a3Aug 3 m :=
    a3_single_sub_mem i j
  have hpair : ψ (θ (Pi.single i 1 - Pi.single j 1)) = 2 := by
    rw [hψ _ hmem, hdRo7A3ReduceVAux_psi_ij hij]
  have hne : θ (Pi.single i 1 - Pi.single j 1) ≠ 0 :=
    a3_theta_single_sub_ne_zero hfr hm hij
  exact ⟨t, ψ, hPH t ⟨Equiv.swap i j, htu, htz⟩, ⟨Equiv.swap i j, htu, htz⟩, hrefl,
    ⟨hne, hpair, htv⟩, htz, hψ, hψz⟩

private theorem hdRo7A3ReduceVAux_aug_le_of_diff_mem {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hfr : A3Frame 3 m θ z) (hpm : 3 ∣ m) (hm : 3 ≤ m)
    (hPH : ∀ a, A3P 3 m θ z a → a ∈ H)
    {W : Submodule (ZMod 3) V} (hW : ∀ a, A3P 3 m θ z a → ∀ w ∈ W, a w ∈ W)
    {i j : Fin m} (hij : i ≠ j) (hdiff : θ (Pi.single i 1 - Pi.single j 1) ∈ W) :
    (a3Aug 3 m).map θ ≤ W := by
  classical
  have hstar : ∀ k : Fin m, k ≠ i → θ (Pi.single i 1 - Pi.single k 1) ∈ W := by
    intro k hki
    by_cases hkj : k = j
    · rw [hkj]; exact hdiff
    · obtain ⟨t, ψ, htH, htP, hrefl, hrd, htz, hψ, hψz⟩ :=
        hdRo7A3ReduceVAux_transp hfr hpm hm hPH (Ne.symm hki)
      have hψik : ψ (θ (Pi.single i 1 - Pi.single j 1)) = 1 := by
        rw [hψ _ (a3_single_sub_mem i j), hdRo7A3ReduceVAux_psi_ik hij hki hkj]
      have htx : t (θ (Pi.single i 1 - Pi.single j 1)) ∈ W := hW t htP _ hdiff
      have happ := hrd.apply (θ (Pi.single i 1 - Pi.single j 1))
      rw [hψik, one_smul] at happ
      have hxd : θ (Pi.single i 1 - Pi.single k 1) =
          θ (Pi.single i 1 - Pi.single j 1) - t (θ (Pi.single i 1 - Pi.single j 1)) := by
        rw [happ]; abel
      rw [hxd]
      exact W.sub_mem hdiff htx
  have hall : ∀ a b : Fin m, a ≠ b → θ (Pi.single a 1 - Pi.single b 1) ∈ W := by
    intro a b hab
    by_cases hai : a = i
    · have hbi : b ≠ i := by rw [← hai]; exact Ne.symm hab
      rw [hai]
      exact hstar b hbi
    · by_cases hbi : b = i
      · rw [hbi]
        have h1 : θ (Pi.single i 1 - Pi.single a 1) ∈ W := hstar a hai
        have hneg : θ (Pi.single a 1 - Pi.single i 1) =
            -θ (Pi.single i 1 - Pi.single a 1) := by
          rw [show (Pi.single a 1 - Pi.single i 1 : Fin m → ZMod 3) =
            -(Pi.single i 1 - Pi.single a 1) by funext q; simp [Pi.sub_apply], map_neg]
        rw [hneg]
        exact W.neg_mem h1
      · have h1 : θ (Pi.single i 1 - Pi.single a 1) ∈ W := hstar a hai
        have h2 : θ (Pi.single i 1 - Pi.single b 1) ∈ W := hstar b hbi
        have hgoal : θ (Pi.single a 1 - Pi.single b 1) =
            -(θ (Pi.single i 1 - Pi.single a 1) - θ (Pi.single i 1 - Pi.single b 1)) := by
          rw [← map_sub, ← map_neg]
          congr 1
          funext q
          simp only [Pi.sub_apply, Pi.neg_apply]
          ring
        rw [hgoal]
        exact W.neg_mem (W.sub_mem h1 h2)
  have hMeq : (a3Aug 3 m).map θ = Submodule.span (ZMod 3)
      (Set.range fun k : Fin m => θ (Pi.single k 1 - Pi.single i 1)) := by
    conv_lhs => rw [hdRo7A3ReduceVAux_aug_eq_span_diff i]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hMeq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rcases eq_or_ne k i with rfl | hk
  · simp
  · exact hall k i hk

private theorem hdRo7A3ReduceVAux_aug_le_of_mem {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hfr : A3Frame 3 m θ z) (hpm : 3 ∣ m) (hm : 3 ≤ m)
    (hM1 : θ (fun _ => 1) = 0) (hPH : ∀ a, A3P 3 m θ z a → a ∈ H)
    {W : Submodule (ZMod 3) V} (hW : ∀ a, A3P 3 m θ z a → ∀ w ∈ W, a w ∈ W)
    {w : V} (hw : w ∈ W) (hwz : w ∉ Submodule.span (ZMod 3) {z}) :
    (a3Aug 3 m).map θ ≤ W := by
  classical
  obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 w
  have hθu : θ u ≠ 0 := by
    intro h0
    apply hwz
    rw [show θ u + c • z = c • z by rw [h0, zero_add]]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton z))
  have hnc : ∃ i j : Fin m, u i ≠ u j := by
    by_contra h
    push Not at h
    apply hθu
    have hi : u = fun _ : Fin m => u ⟨0, by omega⟩ := funext fun i => h i _
    rw [hi, hdRo7A3ReduceVAux_theta_const (m := m) hM1]
  obtain ⟨i, j, hij⟩ := hnc
  have hij' : i ≠ j := fun h => hij (by rw [h])
  obtain ⟨t, ψ, htH, htP, hrefl, hrd, htz, hψ, hψz⟩ :=
    hdRo7A3ReduceVAux_transp hfr hpm hm hPH hij'
  have hψw : ψ (θ u + c • z) = u i - u j := by
    rw [map_add, map_smul, hψ u hu, hψz, smul_zero, add_zero]
  have htw : t (θ u + c • z) ∈ W := hW t htP _ hw
  have hc : u i - u j ≠ 0 := sub_ne_zero.mpr hij
  have hxd : θ (Pi.single i 1 - Pi.single j 1) ∈ W := by
    have happ := hrd.apply (θ u + c • z)
    rw [hψw] at happ
    have heq : θ (Pi.single i 1 - Pi.single j 1) =
        (u i - u j)⁻¹ • ((θ u + c • z) - t (θ u + c • z)) := by
      rw [happ, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [heq]
    exact W.smul_mem _ (W.sub_mem hw htw)
  exact hdRo7A3ReduceVAux_aug_le_of_diff_mem hfr hpm hm hPH hW hij' hxd

private theorem hdRo7A3ReduceVAux_le_span_singleton {F : Type} [Field F] {M : Type}
    [AddCommGroup M] [Module F M] (x : M) (W : Submodule F M)
    (h : W ≤ Submodule.span F {x}) : W = ⊥ ∨ W = Submodule.span F {x} := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    apply le_antisymm h
    have hnz : ∃ w ∈ W, w ≠ 0 := by
      by_contra hc
      apply hbot
      rw [Submodule.eq_bot_iff]
      intro y hy
      by_contra hy0
      exact hc ⟨y, hy, hy0⟩
    obtain ⟨w, hwW, hw0⟩ := hnz
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_singleton).mp (h hwW)
    have hc0 : cc ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hcc; exact hw0 hcc.symm
    rw [Submodule.span_le]
    rintro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have hmem : cc⁻¹ • w ∈ W := W.smul_mem _ hwW
    rwa [← hcc, inv_smul_smul₀ hc0] at hmem

private theorem hdRo7A3ReduceVAux_eq_of_le_sup {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    (hsup : (a3Aug 3 m).map θ ⊔ Submodule.span (ZMod 3) {z} = ⊤)
    {X : Submodule (ZMod 3) V} (hMX : (a3Aug 3 m).map θ ≤ X)
    (hzX : z ∉ X) : X = (a3Aug 3 m).map θ := by
  apply le_antisymm ?_ hMX
  intro v hv
  have hvt : v ∈ (a3Aug 3 m).map θ ⊔ Submodule.span (ZMod 3) {z} := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨m', hm', s, hs, hms⟩ := Submodule.mem_sup.mp hvt
  have hsX : s ∈ X := by
    have h : m' + s - m' = s := by abel
    rw [← h]
    have hmsX : m' + s ∈ X := by rw [hms]; exact hv
    exact Submodule.sub_mem _ hmsX (hMX hm')
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_singleton).mp hs
  rcases eq_or_ne cc 0 with h0 | hc0
  · have hsz : s = 0 := by rw [← hcc, h0, zero_smul]
    rw [hsz, add_zero] at hms
    rw [← hms]
    exact hm'
  · exfalso
    have hzX' : cc⁻¹ • s ∈ X := X.smul_mem cc⁻¹ hsX
    rw [← hcc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hzX'
    exact hzX hzX'

private theorem hdRo7A3ReduceVAux_move_le_of_gen {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] [Module.Finite (ZMod 3) V]
    {M : Submodule (ZMod 3) V} {H : Subgroup (V ≃ₗ[ZMod 3] V)} {S : Set (V ≃ₗ[ZMod 3] V)}
    (hHS : H = Subgroup.closure S) (hS : ∀ s ∈ S, ggLinMove s ≤ M) :
    ∀ a ∈ H, ggLinMove a ≤ M := by
  classical
  let K : Subgroup (V ≃ₗ[ZMod 3] V) :=
    { carrier := {x | ∀ v, x v - v ∈ M}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro x y hx hy v
        have hxy : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
          rw [LinearEquiv.mul_apply]; abel
        rw [hxy]
        exact Submodule.add_mem _ (hx (y v)) (hy v)
      inv_mem' := by
        intro x hx v
        have hxm : ∀ m ∈ M, x m ∈ M := by
          intro m hm
          have h := hx m
          have he : x m = m + (x m - m) := by abel
          rw [he]
          exact Submodule.add_mem _ hm h
        have hmap : M.map x.toLinearMap = M := by
          apply Submodule.eq_of_le_of_finrank_eq ?_ ?_
          · rintro _ ⟨m, hm, rfl⟩
            exact hxm m hm
          · exact (LinearEquiv.finrank_eq
              (Submodule.equivMapOfInjective x.toLinearMap x.injective M)).symm
        have hxinvM : ∀ m ∈ M, x⁻¹ m ∈ M := by
          intro m hm
          have hm' : m ∈ M.map x.toLinearMap := by rw [hmap]; exact hm
          obtain ⟨m', hm', hm'm⟩ := Submodule.mem_map.mp hm'
          rw [← hm'm]
          simpa using hm'
        have hsplit : x⁻¹ v - v = -(x⁻¹ (x v - v)) := by
          rw [map_sub]
          simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
          abel
        rw [hsplit]
        exact Submodule.neg_mem _ (hxinvM _ (hx v)) }
  have hSK : S ⊆ K := by
    intro s hs
    exact (hdRo7A3ReduceVAux_move_le_iff s).mp (hS s hs)
  have hHK : H ≤ K := by
    rw [hHS]
    exact (Subgroup.closure_le (K := K)).mpr hSK
  intro a ha
  exact (hdRo7A3ReduceVAux_move_le_iff a).mpr (hHK ha)

private theorem hdRo7A3ReduceVAux_axis_data {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hfr : A3Frame 3 m θ z) (hpm : 3 ∣ m) (hm : 3 ≤ m)
    (hHA : H ≤ A) (hPH : ∀ a, A3P 3 m θ z a → a ∈ H)
    (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a) (hM1 : θ (fun _ => 1) = 0)
    {s : V ≃ₗ[ZMod 3] V} {u : V} {φ : Module.Dual (ZMod 3) V}
    (hrd : ReflData s u φ) (hsH : s ∈ H)
    (hφM : ∀ w ∈ (a3Aug 3 m).map θ, φ w = 0) :
    (∃ c : ZMod 3, c ≠ 0 ∧ u = c • z) ∧ (∀ w ∈ (a3Aug 3 m).map θ, s w = w) ∧ s z = -z := by
  obtain ⟨û, hû, c, hu_eq⟩ := hfr.2.1 u
  have hconst : ∀ i j : Fin m, û i = û j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨t, ψ, htH, htP, hreflt, hrdt, htz, hψ, hψz⟩ :=
        hdRo7A3ReduceVAux_transp hfr hpm hm hPH hij
      have h0 : φ (θ (Pi.single i 1 - Pi.single j 1)) = 0 :=
        hφM _ (hdRo7A3ReduceVAux_mem_map (a3_single_sub_mem i j))
      have h1 : ψ u = 0 :=
        (hdRo7SUReduceVAux_zero_pair_iff hNoT hrd hrdt (hHA hsH) (hHA htH)).mp h0
      rw [hu_eq, map_add, map_smul, hψ û hû, hψz, smul_zero, add_zero] at h1
      exact sub_eq_zero.mp h1
  have huz : ∃ c' : ZMod 3, u = c' • z := by
    refine ⟨c, ?_⟩
    rw [hu_eq, show û = fun _ : Fin m => û ⟨0, by omega⟩ from funext fun i => hconst i _]
    rw [hdRo7A3ReduceVAux_theta_const (m := m) hM1, zero_add]
  obtain ⟨c', hc'⟩ := huz
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc'
    exact hrd.ne hc'
  refine ⟨⟨c', hc'0, hc'⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    rw [hrd.apply, hφM _ (hdRo7A3ReduceVAux_mem_map hv), zero_smul, sub_zero]
  · have h2 : φ z * c' = 2 := by
      have h := hrd.pair
      rw [hc', map_smul, smul_eq_mul, mul_comm] at h
      exact h
    rw [hrd.apply, hc', smul_smul, h2]
    rw [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul]
    abel

private theorem hdRo7A3ReduceVAux_axis_commute {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    (hfr : A3Frame 3 m θ z) {s t : V ≃ₗ[ZMod 3] V}
    (hsM : ∀ w ∈ (a3Aug 3 m).map θ, s w = w) (hsz : s z = -z)
    (htM : ∀ w ∈ (a3Aug 3 m).map θ, t w ∈ (a3Aug 3 m).map θ) (htz : t z = z) :
    s * t = t * s := by
  ext v
  obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 v
  have huM : θ u ∈ (a3Aug 3 m).map θ := hdRo7A3ReduceVAux_mem_map hu
  have htM' : t (θ u) ∈ (a3Aug 3 m).map θ := htM _ huM
  have h1 : t (θ u + c • z) = t (θ u) + c • z := by rw [map_add, map_smul, htz]
  have h2 : s (θ u + c • z) = θ u + c • -z := by rw [map_add, map_smul, hsM _ huM, hsz]
  have h3 : s (t (θ u) + c • z) = t (θ u) + c • -z := by
    rw [map_add, map_smul, hsM _ htM', hsz]
  have h4 : t (θ u + c • -z) = t (θ u) + c • -z := by
    rw [map_add, map_smul, map_neg, htz]
  show s (t (θ u + c • z)) = t (s (θ u + c • z))
  rw [h1, h2, h3, h4]

private theorem hdRo7A3ReduceVAux_phi_kills {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V}
    {H : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hMinv : ∀ a ∈ H, ∀ w ∈ (a3Aug 3 m).map θ, a w ∈ (a3Aug 3 m).map θ)
    {t : V ≃ₗ[ZMod 3] V} (htH : t ∈ H) {u : V} {φ : Module.Dual (ZMod 3) V}
    (hrd : ReflData t u φ) (huM : u ∉ (a3Aug 3 m).map θ) :
    ∀ w ∈ (a3Aug 3 m).map θ, φ w = 0 := by
  intro w hw
  have hsw : t w - w ∈ (a3Aug 3 m).map θ :=
    Submodule.sub_mem _ (hMinv t htH w hw) hw
  rw [hrd.apply w] at hsw
  have hstep : w - φ w • u - w = (-(φ w)) • u := by module
  rw [hstep] at hsw
  by_contra hφ
  apply huM
  have hc : -(φ w) ≠ 0 := neg_ne_zero.mpr hφ
  have hu : u = (-(φ w))⁻¹ • ((-(φ w)) • u) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hu]
  exact Submodule.smul_mem _ _ hsw

private theorem hdRo7A3ReduceVAux_not_preserves_M {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A)
    (hM1 : θ (fun _ => 1) = 0)
    (hspan : ∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ (a3Aug 3 m).map θ) :
    ¬ (∀ a ∈ H, ∀ w ∈ (a3Aug 3 m).map θ, a w ∈ (a3Aug 3 m).map θ) := by
  classical
  intro hMinv
  have hfin : Module.Finite (ZMod 3) V := a3_moduleFinite hD.hfr
  obtain ⟨S, hS, hHS, hconn⟩ := hD.hgen
  have hpm : 3 ∣ m := hD.h3
  have hm3 : 3 ≤ m := by have := hD.hm; omega
  have hz0 : z ≠ 0 := hdRo7A3ReduceVAux_z_ne_zero hD.hfr
  have h2ne : (2 : ZMod 3) ≠ 0 := hdRo7SUReduceVAux_two_ne_zero
  have hex : ∃ s ∈ S, ¬ ggLinMove s ≤ (a3Aug 3 m).map θ := by
    by_contra h
    push Not at h
    obtain ⟨r, hrH, hrrefl, hrmove⟩ := hspan
    exact hrmove (hdRo7A3ReduceVAux_move_le_of_gen hHS h r hrH)
  obtain ⟨s0, hs0S, hs0move⟩ := hex
  obtain ⟨hs0H, hs0refl⟩ := hS s0 hs0S
  have hs0A : s0 ∈ A := hD.hHA hs0H
  obtain ⟨u0, φ0, hrd0⟩ := hdRo7SUReduceVAux_reflData s0 hs0refl
  have hu0M : u0 ∉ (a3Aug 3 m).map θ := by
    intro hu
    apply hs0move
    rw [hdRo7SUReduceVAux_move_eq_span hrd0, Submodule.span_le, Set.singleton_subset_iff]
    exact hu
  have hφ0M : ∀ w ∈ (a3Aug 3 m).map θ, φ0 w = 0 :=
    hdRo7A3ReduceVAux_phi_kills hMinv hs0H hrd0 hu0M
  obtain ⟨⟨c0, hc00, hu0z⟩, hs0fix, hs0z⟩ :=
    hdRo7A3ReduceVAux_axis_data hD.hfr hpm hm3 hD.hHA hD.hPH hD.hNoT hM1 hrd0 hs0H hφ0M
  have hs0sq : s0 * s0 = 1 := hrd0.mul_self
  have hs0inv : s0⁻¹ = s0 := by
    rw [← mul_one s0⁻¹, ← hs0sq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcomm : ∀ t ∈ S, Commute s0 t := by
    intro t htS
    obtain ⟨htH, htrefl⟩ := hS t htS
    obtain ⟨ut, φt, hrdt⟩ := hdRo7SUReduceVAux_reflData t htrefl
    by_cases htmove : ggLinMove t ≤ (a3Aug 3 m).map θ
    · have hutM : ut ∈ (a3Aug 3 m).map θ := by
        rw [hdRo7SUReduceVAux_move_eq_span hrdt] at htmove
        exact htmove (Submodule.mem_span_singleton_self ut)
      have hφtu0 : φt u0 = 0 :=
        (hdRo7SUReduceVAux_zero_pair_iff hD.hNoT hrd0 hrdt hs0A (hD.hHA htH)).mp
          (hφ0M ut hutM)
      have hφtz : φt z = 0 := by
        have h1 : φt (c0 • z) = 0 := hu0z ▸ hφtu0
        rw [map_smul, smul_eq_mul] at h1
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hc00
        · exact h
      have htz : t z = z := by rw [hrdt.apply z, hφtz, zero_smul, sub_zero]
      exact hdRo7A3ReduceVAux_axis_commute hD.hfr hs0fix hs0z
        (fun w hw => hMinv t htH w hw) htz
    · have hutM : ut ∉ (a3Aug 3 m).map θ := by
        intro hu
        apply htmove
        rw [hdRo7SUReduceVAux_move_eq_span hrdt, Submodule.span_le, Set.singleton_subset_iff]
        exact hu
      have hφtM : ∀ w ∈ (a3Aug 3 m).map θ, φt w = 0 :=
        hdRo7A3ReduceVAux_phi_kills hMinv htH hrdt hutM
      obtain ⟨-, htfix, htz⟩ :=
        hdRo7A3ReduceVAux_axis_data hD.hfr hpm hm3 hD.hHA hD.hPH hD.hNoT hM1 hrdt htH hφtM
      have hteq : t = s0 := by
        ext v
        obtain ⟨u, hu, c, rfl⟩ := hD.hfr.2.1 v
        have huM : θ u ∈ (a3Aug 3 m).map θ := hdRo7A3ReduceVAux_mem_map hu
        have h1 : t (θ u + c • z) = θ u + c • -z := by
          rw [map_add, map_smul, htfix _ huM, htz]
        have h2 : s0 (θ u + c • z) = θ u + c • -z := by
          rw [map_add, map_smul, hs0fix _ huM, hs0z]
        rw [h1, h2]
      rw [hteq]
  have hSsing : S = {s0} := by
    ext t
    constructor
    · intro ht
      have h := hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge
        (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v)
        (fun b hb => hb.2.2 (hcomm b hb.2.1)) (hconn s0 hs0S t ht)
      rw [Set.mem_singleton_iff]
      exact h
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hs0S
  have hHs : ∀ x ∈ H, x = 1 ∨ x = s0 := by
    intro x hx
    rw [hHS, hSsing] at hx
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = s0) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Or.inr (Set.mem_singleton_iff.mp hy)
    · exact Or.inl rfl
    · intro a b _ _ ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · left; rw [one_mul]
      · right; rw [one_mul]
      · right; rw [mul_one]
      · left; rw [hs0sq]
    · intro a _ ha
      rcases ha with rfl | rfl
      · left; rw [inv_one]
      · right; exact hs0inv
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, j] at hv
  obtain ⟨t, ψ, htH, htP, hrefl, hrd, htz, hψ, hψz⟩ :=
    hdRo7A3ReduceVAux_transp hD.hfr hpm hm3 hD.hPH hij
  have hxne : θ (Pi.single i 1 - Pi.single j 1) ≠ 0 :=
    a3_theta_single_sub_ne_zero hD.hfr hm3 hij
  rcases hHs t htH with h1 | h1
  · have h2 : t (θ (Pi.single i 1 - Pi.single j 1)) =
        θ (Pi.single i 1 - Pi.single j 1) := by rw [h1]; rfl
    have happ := hrd.apply (θ (Pi.single i 1 - Pi.single j 1))
    rw [hrd.pair, h2] at happ
    have hzero : (2 : ZMod 3) • θ (Pi.single i 1 - Pi.single j 1) = 0 := by
      have h1' : θ (Pi.single i 1 - Pi.single j 1) +
          (2 : ZMod 3) • θ (Pi.single i 1 - Pi.single j 1) =
          θ (Pi.single i 1 - Pi.single j 1) + 0 := by
        rw [add_zero, ← eq_sub_iff_add_eq, ← happ]
      exact add_left_cancel h1'
    rcases smul_eq_zero.mp hzero with h | h
    · exact h2ne h
    · exact hxne h
  · rw [h1] at htz
    have h2 : z = -z := htz.symm.trans hs0z
    have h3 : (2 : ZMod 3) • z = 0 := by
      rw [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel z
    rcases smul_eq_zero.mp h3 with h | h
    · exact h2ne h
    · exact hz0 h

private theorem hdRo7A3ReduceVAux_eq_neg_one {c : ZMod 3} (h : c * c = 1) (h1 : c ≠ 1) :
    c = -1 := by
  revert c
  decide

private theorem hdRo7A3ReduceVAux_perm_preserves {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {p : V ≃ₗ[ZMod 3] V} (hp : A3P 3 m θ z p) :
    ∀ w ∈ (a3Aug 3 m).map θ, p w ∈ (a3Aug 3 m).map θ := by
  obtain ⟨σ, hσ, hpz⟩ := hp
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
  rw [hσ u hu]
  exact hdRo7A3ReduceVAux_mem_map (a3Aug_perm hu σ.symm)

private theorem hdRo7A3ReduceVAux_axis_of_neg {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hfr : A3Frame 3 m θ z) (hpm : 3 ∣ m) (hm : 3 ≤ m)
    (hHA : H ≤ A) (hPH : ∀ a, A3P 3 m θ z a → a ∈ H)
    (hNoT : ∀ a ∈ A, ¬ C2Transv (p := 3) a) (hz0 : z ≠ 0)
    {s : V ≃ₗ[ZMod 3] V} {u : V} {φ : Module.Dual (ZMod 3) V}
    (hrd : ReflData s u φ) (hsH : s ∈ H) (hsz : s z = -z) :
    ∀ w ∈ (a3Aug 3 m).map θ, s w = w := by
  have h2ne : (2 : ZMod 3) ≠ 0 := hdRo7SUReduceVAux_two_ne_zero
  have hu_z : ∃ c : ZMod 3, u = c • z := by
    have hh := hrd.apply z
    rw [hsz] at hh
    have h3 : -z + φ z • u = z := (eq_sub_iff_add_eq).mp hh
    have h5 : φ z • u = z + z := by
      have h6 := congrArg (fun y => z + y) h3
      simpa using h6
    have h4 : φ z • u = (2 : ZMod 3) • z := by
      rw [two_smul]
      exact h5
    by_cases hφz : φ z = 0
    · rw [hφz, zero_smul] at h4
      have h2z : (2 : ZMod 3) • z = 0 := h4.symm
      have hz : z = 0 := by
        have h : z = (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • z) := by
          rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul]
        rw [h, h2z, smul_zero]
      exact absurd hz hz0
    · refine ⟨(φ z)⁻¹ * 2, ?_⟩
      calc u = (φ z)⁻¹ • (φ z • u) := by rw [smul_smul, inv_mul_cancel₀ hφz, one_smul]
        _ = (φ z)⁻¹ • ((2 : ZMod 3) • z) := by rw [h4]
        _ = ((φ z)⁻¹ * 2) • z := by rw [smul_smul]
  obtain ⟨c, hc⟩ := hu_z
  have hpair : ∀ (i j : Fin m) (hij : i ≠ j),
      φ (θ (Pi.single i 1 - Pi.single j 1)) = 0 := by
    intro i j hij
    obtain ⟨t, ψ, htH, htP, hrefl, hrdt, htz, hψ, hψz⟩ :=
      hdRo7A3ReduceVAux_transp hfr hpm hm hPH hij
    have hψu : ψ u = 0 := by rw [hc, map_smul, hψz, smul_zero]
    exact (hdRo7SUReduceVAux_zero_pair_iff hNoT hrd hrdt (hHA hsH) (hHA htH)).mpr hψu
  have hφM : ∀ w ∈ (a3Aug 3 m).map θ, φ w = 0 := by
    have hi0 : Fin m := ⟨0, by omega⟩
    have hMeq : (a3Aug 3 m).map θ = Submodule.span (ZMod 3)
        (Set.range fun k : Fin m => θ (Pi.single k 1 - Pi.single hi0 1)) := by
      conv_lhs => rw [hdRo7A3ReduceVAux_aug_eq_span_diff hi0]
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have hker : (a3Aug 3 m).map θ ≤ LinearMap.ker φ := by
      rw [hMeq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rcases eq_or_ne k hi0 with rfl | hk
      · simp
      · exact hpair k hi0 hk
    intro w hw
    exact LinearMap.mem_ker.mp (hker hw)
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  rw [hrd.apply, hφM _ (hdRo7A3ReduceVAux_mem_map hv), zero_smul, sub_zero]

private theorem hdRo7A3ReduceVAux_two_smul_ne_zero {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (h2ne : (2 : ZMod 3) ≠ 0) {v : V} (hv : v ≠ 0) :
    (2 : ZMod 3) • v ≠ 0 := by
  intro h
  rcases smul_eq_zero.mp h with h' | h'
  · exact h2ne h'
  · exact hv h'

private theorem hdRo7A3ReduceVAux_transp_ne_one {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V}
    {i j : Fin m} {t : V ≃ₗ[ZMod 3] V} {ψ : Module.Dual (ZMod 3) V}
    (hrd : ReflData t (θ (Pi.single i 1 - Pi.single j 1)) ψ)
    (hxne : θ (Pi.single i 1 - Pi.single j 1) ≠ 0) : t ≠ 1 := by
  intro h1
  have h2ne : (2 : ZMod 3) ≠ 0 := hdRo7SUReduceVAux_two_ne_zero
  have h2 : t (θ (Pi.single i 1 - Pi.single j 1)) = θ (Pi.single i 1 - Pi.single j 1) := by
    rw [h1]; rfl
  have happ := hrd.apply (θ (Pi.single i 1 - Pi.single j 1))
  rw [hrd.pair, h2] at happ
  have hzero : (2 : ZMod 3) • θ (Pi.single i 1 - Pi.single j 1) = 0 := by
    have h1' : θ (Pi.single i 1 - Pi.single j 1) +
        (2 : ZMod 3) • θ (Pi.single i 1 - Pi.single j 1) =
        θ (Pi.single i 1 - Pi.single j 1) + 0 := by
      rw [add_zero, ← eq_sub_iff_add_eq, ← happ]
    exact add_left_cancel h1'
  exact hdRo7A3ReduceVAux_two_smul_ne_zero h2ne hxne hzero

private theorem hdRo7A3ReduceVAux_closure_singleton {G : Type} [Group G] {a : G}
    (hsq : a * a = 1) (hinv : a⁻¹ = a) {x : G} (hx : x ∈ Subgroup.closure {a}) :
    x = 1 ∨ x = a := by
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = a) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Or.inr (Set.mem_singleton_iff.mp hy)
  · exact Or.inl rfl
  · intro b c _ _ hb hc
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
    · left; rw [one_mul]
    · right; rw [one_mul]
    · right; rw [mul_one]
    · left; rw [hsq]
  · intro b _ hb
    rcases hb with rfl | rfl
    · left; rw [inv_one]
    · right; exact hinv

private theorem hdRo7A3ReduceVAux_not_preserves_z {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A)
    (hN : A3NormalizerLeaf) (hRF : A3ReflFixLeaf)
    (hmove : ∃ a ∈ H, a z ≠ z) :
    ¬ (∀ a ∈ H, ∀ w ∈ Submodule.span (ZMod 3) {z}, a w ∈ Submodule.span (ZMod 3) {z}) := by
  classical
  intro hzinv
  have hfin : Module.Finite (ZMod 3) V := a3_moduleFinite hD.hfr
  obtain ⟨S, hS, hHS, hconn⟩ := hD.hgen
  have hpm : 3 ∣ m := hD.h3
  have hm3 : 3 ≤ m := by have := hD.hm; omega
  have hz0 : z ≠ 0 := hdRo7A3ReduceVAux_z_ne_zero hD.hfr
  have hneg : ∀ s ∈ S, s z ≠ z → s z = -z := by
    intro s hs hsz
    obtain ⟨hsH, hsrefl⟩ := hS s hs
    obtain ⟨u, φ, hrd⟩ := hdRo7SUReduceVAux_reflData s hsrefl
    have hmem : s z ∈ Submodule.span (ZMod 3) {z} :=
      hzinv s hsH _ (Submodule.subset_span (Set.mem_singleton z))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hmem
    have hs2 : s (s z) = z := by
      rw [← LinearEquiv.mul_apply, hrd.mul_self]; rfl
    have hcc : c * c = 1 := by
      have h3 : s (s z) = (c * c) • z := by
        rw [show s z = c • z from hc.symm, map_smul, show s z = c • z from hc.symm,
          ← smul_smul]
      have h2 : (c * c) • z = z := by rw [← h3, hs2]
      have h4 : (c * c - 1) • z = 0 := by rw [sub_smul, one_smul, h2, sub_self]
      rcases smul_eq_zero.mp h4 with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 hz0
    have hc1 : c ≠ 1 := by
      intro h1
      apply hsz
      rw [← hc, h1, one_smul]
    have hcneg : c = -1 := hdRo7A3ReduceVAux_eq_neg_one hcc hc1
    rw [← hc, hcneg, neg_one_smul]
  have hP : ∀ s ∈ S, s z = z → A3P 3 m θ z s := by
    intro s hs hsz
    obtain ⟨hsH, hsrefl⟩ := hS s hs
    exact hRF hN 3 m V θ z H A hD s (hD.hHA hsH) hsrefl hsz
  by_cases hex : ∃ s ∈ S, s z ≠ z
  · obtain ⟨s0, hs0S, hs0z⟩ := hex
    have hs0neg : s0 z = -z := hneg s0 hs0S hs0z
    obtain ⟨hs0H, hs0refl⟩ := hS s0 hs0S
    obtain ⟨u0, φ0, hrd0⟩ := hdRo7SUReduceVAux_reflData s0 hs0refl
    have hs0fix : ∀ w ∈ (a3Aug 3 m).map θ, s0 w = w :=
      hdRo7A3ReduceVAux_axis_of_neg hD.hfr hpm hm3 hD.hHA hD.hPH hD.hNoT hz0 hrd0 hs0H hs0neg
    have hs0sq : s0 * s0 = 1 := hrd0.mul_self
    have hs0inv : s0⁻¹ = s0 := by
      rw [← mul_one s0⁻¹, ← hs0sq, ← mul_assoc, inv_mul_cancel, one_mul]
    have hcomm : ∀ t ∈ S, Commute s0 t := by
      intro t htS
      by_cases htz : t z = z
      · obtain ⟨htH, htrefl⟩ := hS t htS
        have htP : A3P 3 m θ z t := hP t htS htz
        exact hdRo7A3ReduceVAux_axis_commute hD.hfr hs0fix hs0neg
          (hdRo7A3ReduceVAux_perm_preserves htP) htz
      · have htneg : t z = -z := hneg t htS htz
        obtain ⟨htH, htrefl⟩ := hS t htS
        obtain ⟨ut, φt, hrdt⟩ := hdRo7SUReduceVAux_reflData t htrefl
        have htfix : ∀ w ∈ (a3Aug 3 m).map θ, t w = w :=
          hdRo7A3ReduceVAux_axis_of_neg hD.hfr hpm hm3 hD.hHA hD.hPH hD.hNoT hz0 hrdt htH htneg
        have hteq : t = s0 := by
          ext v
          obtain ⟨u, hu, c, rfl⟩ := hD.hfr.2.1 v
          have huM : θ u ∈ (a3Aug 3 m).map θ := hdRo7A3ReduceVAux_mem_map hu
          have h1 : t (θ u + c • z) = θ u + c • -z := by
            rw [map_add, map_smul, htfix _ huM, htneg]
          have h2 : s0 (θ u + c • z) = θ u + c • -z := by
            rw [map_add, map_smul, hs0fix _ huM, hs0neg]
          rw [h1, h2]
        rw [hteq]
    have hSsing : S = {s0} := by
      ext t
      constructor
      · intro ht
        have h := hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge
          (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v)
          (fun b hb => hb.2.2 (hcomm b hb.2.1)) (hconn s0 hs0S t ht)
        rw [Set.mem_singleton_iff]
        exact h
      · intro ht
        rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact hs0S
    have hHs : ∀ x ∈ H, x = 1 ∨ x = s0 := by
      intro x hx
      rw [hHS, hSsing] at hx
      exact hdRo7A3ReduceVAux_closure_singleton hs0sq hs0inv hx
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp [i, j] at hv
    obtain ⟨t, ψ, htH, htP, hrefl, hrd, htz, hψ, hψz⟩ :=
      hdRo7A3ReduceVAux_transp hD.hfr hpm hm3 hD.hPH hij
    have hxne : θ (Pi.single i 1 - Pi.single j 1) ≠ 0 :=
      a3_theta_single_sub_ne_zero hD.hfr hm3 hij
    have htne : t ≠ 1 := hdRo7A3ReduceVAux_transp_ne_one hrd hxne
    rcases hHs t htH with h1 | h1
    · exact htne h1
    · rw [h1] at htz
      have h2 : z = -z := htz.symm.trans hs0neg
      have h3 : z + z = 0 := by
        nth_rewrite 2 [h2]
        exact add_neg_cancel z
      have h4 : (2 : ZMod 3) • z = z + z := two_smul (ZMod 3) z
      rw [← h4] at h3
      have hz : z = 0 := by
        have h : z = (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • z) := by
          rw [smul_smul, inv_mul_cancel₀ hdRo7SUReduceVAux_two_ne_zero, one_smul]
        rw [h, h3, smul_zero]
      exact hz0 hz
  · push Not at hex
    have hPH' : ∀ x ∈ H, A3P 3 m θ z x := by
      intro x hx
      rw [hHS] at hx
      refine Subgroup.closure_induction (p := fun x _ => A3P 3 m θ z x) ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact hP y hy (hex y hy)
      · exact a3P_one
      · intro a b _ _ ha hb
        exact a3P_mul ha hb
      · intro a _ ha
        exact a3P_inv ha
    obtain ⟨a, ha, haz⟩ := hmove
    obtain ⟨-, -, hfix⟩ := hPH' a ha
    exact haz hfix

private theorem hdRo7A3ReduceVAux_exists_fourth {m : ℕ} (hm : 4 ≤ m) (i j k : Fin m) :
    ∃ ℓ : Fin m, ℓ ≠ i ∧ ℓ ≠ j ∧ ℓ ≠ k := by
  have hlt : ({i, j, k} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h1 : ({i, j, k} : Finset (Fin m)).card ≤ 3 := by
      have ha : ({i, j, k} : Finset (Fin m)).card ≤ ({j, k} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le i {j, k}
      have hb : ({j, k} : Finset (Fin m)).card ≤ ({k} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le j {k}
      have hc : ({k} : Finset (Fin m)).card = 1 := Finset.card_singleton k
      omega
    omega
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ
  exact ⟨ℓ, hℓ.1, hℓ.2.1, hℓ.2.2⟩

private theorem hdRo7A3ReduceVAux_root_indep {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    (hfr : A3Frame 3 m θ z) {i j k ℓ : Fin m} (hiℓ : ℓ ≠ i) (hjℓ : ℓ ≠ j) (hkℓ : ℓ ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {a b : ZMod 3}
    (h : a • θ (Pi.single i 1 - Pi.single j 1) + b • θ (Pi.single i 1 - Pi.single k 1) = 0) :
    a = 0 ∧ b = 0 := by
  have hv : θ (a • (Pi.single i 1 - Pi.single j 1) + b • (Pi.single i 1 - Pi.single k 1)) = 0 := by
    rw [map_add, map_smul, map_smul, h]
  have hmem : a • (Pi.single i 1 - Pi.single j 1) + b • (Pi.single i 1 - Pi.single k 1) ∈
      a3Aug 3 m :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (a3_single_sub_mem i j))
      (Submodule.smul_mem _ _ (a3_single_sub_mem i k))
  obtain ⟨c, hc⟩ := hfr.1 _ hmem hv
  have hℓ0 : (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) : Fin m → ZMod 3) ℓ = 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hdRo7A3ReduceVAux_val_other hiℓ hjℓ, hdRo7A3ReduceVAux_val_other hiℓ hkℓ]
    ring
  have hc0 : c = 0 := by rw [← congrFun hc ℓ, hℓ0]
  have hi0 : (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) : Fin m → ZMod 3) i = a + b := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hdRo7A3ReduceVAux_val_self hij, hdRo7A3ReduceVAux_val_self hik]
    ring
  have hj0 : (a • (Pi.single i 1 - Pi.single j 1) +
      b • (Pi.single i 1 - Pi.single k 1) : Fin m → ZMod 3) j = -a := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hdRo7A3ReduceVAux_val_snd hij, hdRo7A3ReduceVAux_val_other (Ne.symm hij) hjk]
    ring
  have hai : a + b = 0 := by rw [← hi0, congrFun hc i, hc0]
  have haj : a = 0 := by rw [← neg_eq_zero, ← hj0, congrFun hc j, hc0]
  refine ⟨haj, ?_⟩
  rw [haj, zero_add] at hai
  exact hai

private theorem hdRo7A3ReduceVAux_root_eigen {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hfr : A3Frame 3 m θ z) (hpm : 3 ∣ m) (hm : 3 ≤ m)
    (hPH : ∀ a, A3P 3 m θ z a → a ∈ H) {T : V →ₗ[ZMod 3] V}
    (hT : ∀ a ∈ H, T ∘ₗ (a : V →ₗ[ZMod 3] V) = (a : V →ₗ[ZMod 3] V) ∘ₗ T)
    {i j : Fin m} (hij : i ≠ j) :
    ∃ α : ZMod 3, T (θ (Pi.single i 1 - Pi.single j 1)) =
      α • θ (Pi.single i 1 - Pi.single j 1) := by
  obtain ⟨t, ψ, htH, htP, hrefl, hrd, htz, hψ, hψz⟩ :=
    hdRo7A3ReduceVAux_transp hfr hpm hm hPH hij
  have hcomm : T ((t : V →ₗ[ZMod 3] V) (θ (Pi.single i 1 - Pi.single j 1))) =
      (t : V →ₗ[ZMod 3] V) (T (θ (Pi.single i 1 - Pi.single j 1))) := by
    simpa only [LinearMap.comp_apply] using congrArg (fun (f : V →ₗ[ZMod 3] V) =>
      f (θ (Pi.single i 1 - Pi.single j 1))) (hT t htH)
  have hroot : (t : V →ₗ[ZMod 3] V) (θ (Pi.single i 1 - Pi.single j 1)) =
      -θ (Pi.single i 1 - Pi.single j 1) := hrd.apply_root
  have happ : ∀ y, (t : V →ₗ[ZMod 3] V) y =
      y - ψ y • θ (Pi.single i 1 - Pi.single j 1) := fun y => hrd.apply y
  rw [hroot, map_neg, happ] at hcomm
  refine ⟨(2 : ZMod 3)⁻¹ * ψ (T (θ (Pi.single i 1 - Pi.single j 1))), ?_⟩
  have h2 : (2 : ZMod 3) • T (θ (Pi.single i 1 - Pi.single j 1)) =
      ψ (T (θ (Pi.single i 1 - Pi.single j 1))) • θ (Pi.single i 1 - Pi.single j 1) := by
    have h3 : -T (θ (Pi.single i 1 - Pi.single j 1)) +
        ψ (T (θ (Pi.single i 1 - Pi.single j 1))) • θ (Pi.single i 1 - Pi.single j 1) =
        T (θ (Pi.single i 1 - Pi.single j 1)) := (eq_sub_iff_add_eq).mp hcomm
    have h4 : ψ (T (θ (Pi.single i 1 - Pi.single j 1))) • θ (Pi.single i 1 - Pi.single j 1) =
        T (θ (Pi.single i 1 - Pi.single j 1)) + T (θ (Pi.single i 1 - Pi.single j 1)) := by
      rw [← sub_neg_eq_add, eq_sub_iff_add_eq, add_comm]
      exact h3
    rw [two_smul]
    exact h4.symm
  calc T (θ (Pi.single i 1 - Pi.single j 1)) =
      (2 : ZMod 3)⁻¹ • ((2 : ZMod 3) • T (θ (Pi.single i 1 - Pi.single j 1))) := by
        rw [smul_smul, inv_mul_cancel₀ hdRo7SUReduceVAux_two_ne_zero, one_smul]
    _ = (2 : ZMod 3)⁻¹ • (ψ (T (θ (Pi.single i 1 - Pi.single j 1))) •
          θ (Pi.single i 1 - Pi.single j 1)) := by rw [h2]
    _ = ((2 : ZMod 3)⁻¹ * ψ (T (θ (Pi.single i 1 - Pi.single j 1)))) •
          θ (Pi.single i 1 - Pi.single j 1) := by rw [smul_smul]

private theorem hdRo7A3ReduceVAux_commutant {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A)
    (hM1 : θ (fun _ => 1) = 0)
    (hirr : ∀ W : Submodule (ZMod 3) V, (∀ a ∈ H, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    {T : V →ₗ[ZMod 3] V}
    (hT : ∀ a ∈ H, T ∘ₗ (a : V →ₗ[ZMod 3] V) = (a : V →ₗ[ZMod 3] V) ∘ₗ T) :
    ∃ c : ZMod 3, T = c • LinearMap.id := by
  classical
  have hpm : 3 ∣ m := hD.h3
  have hm3 : 3 ≤ m := by have := hD.hm; omega
  have hm4 : 4 ≤ m := by have := hD.hm; omega
  have hz0 : z ≠ 0 := hdRo7A3ReduceVAux_z_ne_zero hD.hfr
  have heig := fun (i j : Fin m) (hij : i ≠ j) =>
    hdRo7A3ReduceVAux_root_eigen hD.hfr hpm hm3 hD.hPH hT hij
  let i0 : Fin m := ⟨0, by omega⟩
  let j0 : Fin m := ⟨1, by omega⟩
  have hj0 : j0 ≠ i0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, j0] at hv
  obtain ⟨α, hα⟩ := heig i0 j0 (Ne.symm hj0)
  have hsame : ∀ (j k : Fin m), j ≠ i0 → k ≠ i0 → j ≠ k → ∀ α β : ZMod 3,
      T (θ (Pi.single i0 1 - Pi.single j 1)) = α • θ (Pi.single i0 1 - Pi.single j 1) →
      T (θ (Pi.single i0 1 - Pi.single k 1)) = β • θ (Pi.single i0 1 - Pi.single k 1) →
      α = β := by
    intro j k hj hk hjk β γ hβ hγ
    obtain ⟨ℓ, hℓi, hℓj, hℓk⟩ := hdRo7A3ReduceVAux_exists_fourth hm4 i0 j k
    obtain ⟨lam, hlam⟩ := heig k j (Ne.symm hjk)
    set xj : V := θ (Pi.single i0 1 - Pi.single j 1) with hxj
    set xk : V := θ (Pi.single i0 1 - Pi.single k 1) with hxk
    have hx : xj - xk = θ (Pi.single k 1 - Pi.single j 1) := by
      rw [hxj, hxk, ← map_sub]
      congr 1
      funext q
      simp only [Pi.sub_apply]
      ring
    have hTeq : T (xj - xk) = β • xj - γ • xk := by rw [map_sub, hβ, hγ]
    have hTeq2 : T (xj - xk) = lam • (xj - xk) := by rw [hx, hlam]
    have h4' : β • xj - γ • xk = lam • xj - lam • xk := by
      rw [← hTeq, hTeq2, smul_sub]
    have h5 : (β - lam) • xj + (lam - γ) • xk = 0 := by
      have h6 : (β - lam) • xj + (lam - γ) • xk =
          (β • xj - γ • xk) - (lam • xj - lam • xk) := by
        rw [sub_smul, sub_smul]; abel
      rw [h6, h4', sub_self]
    have hji : i0 ≠ j := Ne.symm hj
    have hki : i0 ≠ k := Ne.symm hk
    have hjk' : j ≠ k := hjk
    obtain ⟨h1, h2⟩ := hdRo7A3ReduceVAux_root_indep hD.hfr hℓi hℓj hℓk hji hki hjk' h5
    rw [sub_eq_zero] at h1 h2
    rw [h1, h2]
  have hαj : ∀ (j : Fin m) (hj : j ≠ i0), T (θ (Pi.single i0 1 - Pi.single j 1)) =
      α • θ (Pi.single i0 1 - Pi.single j 1) := by
    intro j hj
    rcases eq_or_ne j j0 with rfl | hne
    · exact hα
    · obtain ⟨β, hβ⟩ := heig i0 j (Ne.symm hj)
      have hβα : β = α :=
        hsame j j0 hj hj0 (fun h => hne h) β α hβ hα
      rw [hβα] at hβ
      exact hβ
  have hMα : ∀ w ∈ (a3Aug 3 m).map θ, T w = α • w := by
    have hMeq : (a3Aug 3 m).map θ = Submodule.span (ZMod 3)
        (Set.range fun j : Fin m => θ (Pi.single j 1 - Pi.single i0 1)) := by
      conv_lhs => rw [hdRo7A3ReduceVAux_aug_eq_span_diff i0]
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    intro w hw
    rw [hMeq] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        dsimp only
        by_cases hj : j = i0
        · rw [hj]; simp
        · have hxeq : θ (Pi.single j 1 - Pi.single i0 1) =
              -θ (Pi.single i0 1 - Pi.single j 1) := by
            rw [← map_neg]
            congr 1
            funext q
            simp only [Pi.sub_apply, Pi.neg_apply]
            ring
          rw [hxeq, map_neg, hαj j hj, smul_neg]
    | zero => rw [map_zero, smul_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul c x _ hx =>
        rw [map_smul, hx, smul_comm]
  obtain ⟨u, hu, d, hTz⟩ := hD.hfr.2.1 (T z)
  have hzfix : ∀ (i j : Fin m), i ≠ j → u i = u j := by
    intro i j hij
    obtain ⟨t, ψ, htH, htP, hrefl, hrd, htz, hψ, hψz⟩ :=
      hdRo7A3ReduceVAux_transp hD.hfr hpm hm3 hD.hPH hij
    have hcomm0 : T ((t : V →ₗ[ZMod 3] V) z) = (t : V →ₗ[ZMod 3] V) (T z) := by
      simpa only [LinearMap.comp_apply] using congrArg (fun (f : V →ₗ[ZMod 3] V) => f z) (hT t htH)
    have htzv : (t : V →ₗ[ZMod 3] V) z = z := htz
    have happ : (t : V →ₗ[ZMod 3] V) (T z) =
        T z - ψ (T z) • θ (Pi.single i 1 - Pi.single j 1) := hrd.apply (T z)
    rw [htzv, happ] at hcomm0
    have hzero : ψ (T z) • θ (Pi.single i 1 - Pi.single j 1) = 0 := by
      have h2 : T z - ψ (T z) • θ (Pi.single i 1 - Pi.single j 1) = T z := hcomm0.symm
      have h3 := congrArg (fun y => y - T z) h2
      simpa using h3
    have hψ0 : ψ (T z) = 0 := by
      rcases smul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h (a3_theta_single_sub_ne_zero hD.hfr hm3 hij)
    have h2 : ψ (T z) = ψ (θ u + d • z) := by rw [← hTz]
    rw [map_add, map_smul, hψ u hu, hψz, smul_zero, add_zero] at h2
    exact sub_eq_zero.mp (h2 ▸ hψ0)
  have hTz' : T z = d • z := by
    rw [hTz, show u = fun _ : Fin m => u i0 from
      funext fun q => by
        by_cases h : q = i0
        · rw [h]
        · exact hzfix q i0 h]
    rw [hdRo7A3ReduceVAux_theta_const (m := m) hM1, zero_add]
  by_cases hαd : α = d
  · refine ⟨α, ?_⟩
    ext v
    obtain ⟨w, hw, e, rfl⟩ := hD.hfr.2.1 v
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul,
      hMα _ (hdRo7A3ReduceVAux_mem_map hw), hTz', ← hαd, smul_add, smul_smul, smul_smul,
      mul_comm e α]
  · exfalso
    have hzW : z ∉ LinearMap.ker (T - α • LinearMap.id) := by
      intro hz
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hTz'] at hz
      have h1 : (d - α) • z = 0 := by
        rw [← sub_smul] at hz
        exact hz
      rcases smul_eq_zero.mp h1 with h | h
      · exact hαd (sub_eq_zero.mp h).symm
      · exact hz0 h
    have hMW : (a3Aug 3 m).map θ ≤ LinearMap.ker (T - α • LinearMap.id) := by
      intro w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hMα w hw, sub_self]
    have hinv : ∀ a ∈ H, ∀ w ∈ LinearMap.ker (T - α • LinearMap.id),
        a w ∈ LinearMap.ker (T - α • LinearMap.id) := by
      intro a ha w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        at hw ⊢
      change T ((a : V →ₗ[ZMod 3] V) w) - α • (a : V →ₗ[ZMod 3] V) w = 0
      have hcomm0 : T ((a : V →ₗ[ZMod 3] V) w) = (a : V →ₗ[ZMod 3] V) (T w) := by
        simpa only [LinearMap.comp_apply] using congrArg (fun (f : V →ₗ[ZMod 3] V) => f w) (hT a ha)
      rw [hcomm0]
      have h1 : α • (a : V →ₗ[ZMod 3] V) w = (a : V →ₗ[ZMod 3] V) (α • w) :=
        (LinearMap.map_smul (a : V →ₗ[ZMod 3] V) α w).symm
      rw [h1, ← map_sub, hw, map_zero]
    rcases hirr _ hinv with hbot | htop
    · rw [hbot] at hMW
      have hzero : θ (Pi.single i0 1 - Pi.single j0 1) = 0 := by
        have hmem := hMW (hdRo7A3ReduceVAux_mem_map (a3_single_sub_mem i0 j0))
        simpa using hmem
      exact a3_theta_single_sub_ne_zero hD.hfr hm3 (Ne.symm hj0) hzero
    · rw [htop] at hzW
      exact hzW (Submodule.mem_top)

private theorem hdRo7A3ReduceVAux_two_mul_le_pow {m : ℕ} (hm : 4 ≤ m) : 2 * m ≤ 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h1 : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
        rw [show n + 1 - 1 = n - 1 + 1 by omega, pow_succ]
        ring
      rw [h1]
      have h2 : 2 ≤ 2 ^ (n - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

private theorem hdRo7A3ReduceVAux_irred {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A)
    (hN : A3NormalizerLeaf) (hRF : A3ReflFixLeaf) (hM1 : θ (fun _ => 1) = 0)
    (hspan : ∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ (a3Aug 3 m).map θ)
    (hmove : ∃ a ∈ H, a z ≠ z) :
    ∀ W : Submodule (ZMod 3) V, (∀ a ∈ H, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hnotM := hdRo7A3ReduceVAux_not_preserves_M hD hM1 hspan
  have hnotz := hdRo7A3ReduceVAux_not_preserves_z hD hN hRF hmove
  have hsup := hdRo7A3ReduceVAux_sup_span hD.hfr
  have hpm : 3 ∣ m := hD.h3
  have hm3 : 3 ≤ m := by have := hD.hm; omega
  by_cases hWz : W ≤ Submodule.span (ZMod 3) {z}
  · rcases hdRo7A3ReduceVAux_le_span_singleton z W hWz with hbot | hspan_eq
    · exact Or.inl hbot
    · exact absurd (fun a ha w hw => by
        rw [← hspan_eq] at hw ⊢
        exact hW a ha w hw) hnotz
  · right
    obtain ⟨w, hwW, hwz⟩ : ∃ w ∈ W, w ∉ Submodule.span (ZMod 3) {z} := by
      by_contra h
      push Not at h
      exact hWz fun y hy => h y hy
    have hMW : (a3Aug 3 m).map θ ≤ W :=
      hdRo7A3ReduceVAux_aug_le_of_mem hD.hfr hpm hm3 hM1 hD.hPH
        (fun a ha w hw => hW a (hD.hPH a ha) w hw) hwW hwz
    by_cases hzW : z ∈ W
    · have htop : (⊤ : Submodule (ZMod 3) V) ≤ W := by
        rw [← hsup]
        refine sup_le hMW ?_
        rw [Submodule.span_le]
        rintro x rfl
        exact hzW
      exact le_antisymm le_top htop
    · exfalso
      have hWM : W = (a3Aug 3 m).map θ := hdRo7A3ReduceVAux_eq_of_le_sup hsup hMW hzW
      exact hnotM fun a ha w hw => by
        rw [← hWM] at hw ⊢
        exact hW a ha w hw

private theorem hdRo7A3ReduceVAux_card_le {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A)
    (hSC : A3StabCardLeaf) (hN : A3NormalizerLeaf) :
    Nat.card H ≤ 6 ^ (m - 1) * (m - 1).factorial := by
  have hpm : 3 ∣ m := hD.h3
  have hm2 : 2 ≤ m := by have := hD.hm; omega
  have hfin : Module.Finite (ZMod 3) V := a3_moduleFinite hD.hfr
  have hVfin : Finite V := a3_finite hD.hfr
  have : Fintype V := Fintype.ofFinite V
  have hlin : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e f h => LinearEquiv.ext fun v => congrFun h v)
  have : Fintype (V ≃ₗ[ZMod 3] V) := Fintype.ofFinite _
  have : Fintype H := Fintype.ofFinite H
  have : Fintype ↥(MulAction.orbit H z) := Fintype.ofFinite _
  have : Fintype ↥(MulAction.stabilizer H z) := Fintype.ofFinite _
  have hcardV : Fintype.card V = 3 ^ (m - 1) := by
    rw [← FiniteField.pow_finrank_eq_card 3 V, a3_finrank hD.hfr hpm hm2]
  have hOS : Fintype.card (MulAction.orbit H z) * Fintype.card (MulAction.stabilizer H z) =
      Fintype.card H := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H z
  have horbit : Fintype.card (MulAction.orbit H z) ≤ 3 ^ (m - 1) := by
    rw [← hcardV]
    exact Fintype.card_le_of_injective (fun v : ↥(MulAction.orbit H z) => v.1)
      Subtype.val_injective
  have hstab : Fintype.card (MulAction.stabilizer H z) ≤ 2 * m.factorial := by
    have hP3 : Nat.card {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a z = z} ≤ 2 * m.factorial :=
      hSC hN 3 m V θ z H A hD
    let e : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a z = z} ≃ ↥(MulAction.stabilizer H z) :=
      { toFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2⟩
        invFun := fun q => ⟨q.1.1, q.1.2, q.2⟩
        left_inv := fun q => rfl
        right_inv := fun q => rfl }
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e]
    exact hP3
  have hmfac : m.factorial = m * (m - 1).factorial := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.factorial_succ]
    simp
  have hmul : 2 * m ≤ 2 ^ (m - 1) := hdRo7A3ReduceVAux_two_mul_le_pow (by have := hD.hm; omega)
  calc Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    _ = Fintype.card (MulAction.orbit H z) * Fintype.card (MulAction.stabilizer H z) := hOS.symm
    _ ≤ 3 ^ (m - 1) * (2 * m.factorial) := Nat.mul_le_mul horbit hstab
    _ = 2 * (3 ^ (m - 1) * m.factorial) := by ring
    _ = (2 * m) * (3 ^ (m - 1) * (m - 1).factorial) := by rw [hmfac]; ring
    _ ≤ 2 ^ (m - 1) * (3 ^ (m - 1) * (m - 1).factorial) := Nat.mul_le_mul_right _ hmul
    _ = (2 * 3) ^ (m - 1) * (m - 1).factorial := by
        rw [mul_pow]
        ring
    _ = 6 ^ (m - 1) * (m - 1).factorial := by norm_num

private theorem hdRo7A3ReduceVAux_closure_refl {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A) :
    H = Subgroup.closure {r : V ≃ₗ[ZMod 3] V | r ∈ H ∧ GGLinRefl r} := by
  obtain ⟨S, hS, hHS, hconn⟩ := hD.hgen
  apply le_antisymm
  · conv_lhs => rw [hHS]
    exact Subgroup.closure_mono fun s hs => hS s hs
  · exact (Subgroup.closure_le _).mpr fun r hr => hr.1

theorem a3_reduceV_holds : A3ReduceVLeaf := by
  intro hSC hRF hN p hpFact m V instV instM θ z H A hD hM1 h12 hspan hmove
  have hp3 : p = 3 := hD.hp
  subst hp3
  have hfin : Module.Finite (ZMod 3) V := a3_moduleFinite hD.hfr
  have : Module.Finite (ZMod 3) V := hfin
  have hpm : 3 ∣ m := hD.h3
  have hm2 : 2 ≤ m := by have := hD.hm; omega
  have hirr : ∀ W : Submodule (ZMod 3) V, (∀ a ∈ H, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hdRo7A3ReduceVAux_irred hD hN hRF hM1 hspan hmove W hW
  refine ⟨V, instV, instM, H, a3_finrank hD.hfr hpm hm2, ⟨hirr, ?_⟩,
    hdRo7A3ReduceVAux_closure_refl hD, hdRo7A3ReduceVAux_card_le hD hSC hN, id⟩
  intro T hT
  exact hdRo7A3ReduceVAux_commutant hD hM1 hirr hT

end CFSG.StandardType.HdRo7A3
