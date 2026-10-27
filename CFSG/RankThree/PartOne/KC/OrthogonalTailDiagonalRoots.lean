module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitDiagonalRoots
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootGen

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section Tail

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {r p : ℕ}
  {qA : QuadraticForm K U}

theorem prodHom_apply_hypVec (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
    (c : Fin r ⊕ Fin r) (l : K) (hg : g (Pi.single c 1) = l • Pi.single c 1) :
    prodHom U g (hypVec K U c) = l • hypVec K U c := by
  rw [prodHom_apply, hypVec_smul]
  simp only [hypVec, LinearEquiv.prodCongr_apply, hg, map_zero]

theorem prodHom_apply_tail (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (u : U) :
    prodHom U g ((0 : Fin r ⊕ Fin r → K), u) = (0, u) := by
  rw [prodHom_apply]
  simp

theorem span_hypVec_tail_eq_top :
    Submodule.span K (Set.range (hypVec K U (r := r)) ∪
      {v : (Fin r ⊕ Fin r → K) × U | ∃ u : U, v = ((0 : Fin r ⊕ Fin r → K), u)}) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨x, u⟩ := v
  have h1 : ((x, 0) : (Fin r ⊕ Fin r → K) × U) = ∑ c, x c • hypVec K U c := by
    refine Prod.ext ?_ (by simp [hypVec, Prod.snd_sum])
    simp only [hypVec, Prod.smul_mk, smul_zero, Prod.fst_sum]
    funext c'
    simp [Pi.single_apply]
  have h2 : ((x, u) : (Fin r ⊕ Fin r → K) × U) = (x, 0) + (0, u) := by
    simp
  rw [h2, h1]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨c, rfl⟩)))
    (Submodule.subset_span (Or.inr ⟨u, rfl⟩))

theorem apply_hypVec_of_chars [NeZero p]
    {A : Subgroup (((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))} {ζ : K}
    (hζ : ζ ^ p = 1) (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) (hypVec K U (Sum.inl i)) =
          ζ ^ (χ i g).toAdd.val • hypVec K U (Sum.inl i) ∧
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inr i)) = (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K U (Sum.inr i))
    (g : A) (c : Fin r ⊕ Fin r) :
    (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) (hypVec K U c) =
      zetaPow ζ (coordChar χ c g).toAdd • hypVec K U c := by
  rcases c with i | i
  · exact (hχ g i).1
  · rw [(hχ g i).2]
    simp only [coordChar, Sum.elim_inr, MonoidHom.inv_apply, toAdd_inv, zetaPow_neg hζ]
    rfl

end Tail

section TailRoots

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {r p : ℕ}
  {qA : QuadraticForm K U}

theorem tailLongElt_eq_eichler_pair {α : Fin r → ℤ} {a b : Fin r ⊕ Fin r}
    (h1 : ∀ t : K, rootElt r K α t = rpElt a b t) (t : K) :
    tailLongElt r qA α t =
      eichler (quadTail r qA) (hypVec K U a) (t • -(hypVec K U b.swap)) := by
  rw [tailLongElt_eq_prodCongr, h1]
  show (eichler (quadPlus r K) (Pi.single a 1) ((-t) • Pi.single b.swap 1)).prodCongr
    (LinearEquiv.refl K U) = _
  rw [← eichler_prod_fst]
  congr 1
  rw [smul_neg, neg_smul, hypVec_smul]
  simp

theorem eps_sub_eps_mem_roots {i j : Fin r} (hij : i ≠ j) : eps r i - eps r j ∈ roots r := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, Or.inl rfl⟩
  · exact ⟨j, i, h, Or.inr (Or.inl (by abel))⟩

theorem prodHom_mem_tail {ζ : K} {α : Fin r → ℤ} (hr : 3 ≤ r) (hα : α ∈ roots r)
    (hζ0 : ζ ≠ 0) :
    prodHom U (torusElt r K fun i => (Units.mk0 ζ hζ0) ^ α i) ∈
      orthElementaryGroup (quadTail r qA) := by
  have h := rootH_mem (r := r) (K := K) α ζ
  rw [show rootH r K α ζ = torusElt r K fun i => (Units.mk0 ζ hζ0) ^ α i from
    rootH_eq_torusElt hα (Units.mk0 ζ hζ0)] at h
  have h2 : torusElt r K (fun i => (Units.mk0 ζ hζ0) ^ α i) ∈ rootSupr r K := by
    rw [← (orthogonal_geometry_split_root_generation hr).1]
    exact h
  exact tailRootSupr_le (map_rootSupr_le (Subgroup.mem_map_of_mem _ h2))

end TailRoots

section TailRootsMain

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {r p : ℕ}
  {qA : QuadraticForm K U}

theorem tail_long_root_le_derivedCentralizer (hp : p.Prime) (hp3 : 3 < p) {ζ : K}
    (hζ : orderOf ζ = p) (hr : 3 ≤ r)
    (A : Subgroup (((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)))
    (hAG : A ≤ orthElementaryGroup (quadTail r qA)) (hAcard : Nat.card A = p ^ 2)
    (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) (hypVec K U (Sum.inl i)) =
          ζ ^ (χ i g).toAdd.val • hypVec K U (Sum.inl i) ∧
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inr i)) = (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K U (Sum.inr i))
    (hfix : ∀ (g : A) (u : U),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) ((0 : Fin r ⊕ Fin r → K), u) =
        (0, u))
    {α : Fin r → ℤ} (hα : α ∈ roots r) :
    ∃ a ∈ A, a ≠ 1 ∧
      tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζ2 : ζ * ζ ≠ 1 := fun h => by
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have h2 := Nat.le_of_dvd (by norm_num) (hζ ▸ h1)
    omega
  obtain ⟨a, b, hab, hwt, h1, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
  obtain ⟨g, hg1, hgψ⟩ := exists_ne_one_mem_ker hp hAcard (coordChar χ a * (coordChar χ b)⁻¹)
  have hgab : coordChar χ a g = coordChar χ b g := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at hgψ
    exact hgψ
  refine ⟨(g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)), g.2,
    fun h => hg1 (Subtype.ext h), ?_⟩
  have hgc := apply_hypVec_of_chars hζp χ hχ g
  have hκ : zetaPow ζ (coordChar χ a g).toAdd * zetaPow ζ (coordChar χ b.swap g).toAdd = 1 := by
    rw [← zetaPow_add hζp, coordChar_swap, MonoidHom.inv_apply, toAdd_inv, hgab, add_neg_cancel,
      zetaPow_zero]
  set ζ' : Kˣ := Units.mk0 ζ hζ0 with hζ'
  set δ := prodHom U (torusElt r K fun i => ζ' ^ α i) with hδ
  have hδG : δ ∈ orthElementaryGroup (quadTail r qA) := prodHom_mem_tail hr hα hζ0
  have hδc : ∀ c : Fin r ⊕ Fin r,
      δ (hypVec K U c) = ((ζ' ^ (coordWt c ⬝ᵥ α) : Kˣ) : K) • hypVec K U c := fun c =>
    prodHom_apply_hypVec _ c _ (by rw [torusElt_apply_single, sumElim_zpow_eq])
  have hα' : α = coordWt a - coordWt b := hwt.symm
  have hμ : coordWt a ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct, ite_eq_left rfl,
      ite_eq_right (ne_of_coordIdx_ne hab), ite_eq_right (ne_swap_of_coordIdx_ne hab)]
    norm_num
  have hν : coordWt b.swap ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct,
      ite_eq_right (fun h => ne_swap_of_coordIdx_ne hab h.symm),
      ite_eq_right (swap_ne_swap_of_coordIdx_ne hab).symm, ite_eq_right (swap_ne_self b),
      ite_eq_left rfl]
    norm_num
  have hδa : δ * (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) =
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) * δ :=
    mul_comm_of_eigen span_hypVec_tail_eq_top (by
      rintro v (⟨c, rfl⟩ | ⟨u, rfl⟩)
      · exact ⟨_, _, hδc c, hgc c⟩
      · exact ⟨1, 1, by rw [one_smul]; exact prodHom_apply_tail _ u,
          by rw [one_smul]; exact hfix g u⟩)
  have hG₀ : orthElementaryGroup (quadTail r qA) ≤ TauCeti.QuadraticMap.orthogonalGroup
      (quadTail r qA) := orthElementaryGroup_le _
  have hpolar : ∀ t : K, polar (quadTail r qA) (hypVec K U a) (t • -(hypVec K U b.swap)) = 0 :=
    fun t => by
      rw [smul_neg, polar_neg_right, polar_smul_right_eq, polar_hypVec_hypVec,
        ite_eq_right (swap_ne_swap_of_coordIdx_ne hab).symm, mul_zero, neg_zero]
  intro y hy
  obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long hα).1 hy
  rw [tailLongElt_eq_eichler_pair h1 t]
  refine eichler_mem_derivedCentralizer (Q := quadTail r qA) hG₀ (hpolar t)
    (fun s => eichler_mem_elementaryGroup _ _ _) (hAG g.2) hδG hδa
    (κ := zetaPow ζ (coordChar χ a g).toAdd) (κ' := zetaPow ζ (coordChar χ b.swap g).toAdd)
    (μ := ζ) (ν := ζ) (hgc a) ?_ hκ ?_ ?_ hζ2
  · rw [smul_neg, map_neg, map_smul, hgc b.swap, smul_neg, smul_comm]
  · rw [hδc a, hμ]
    simp [hζ']
  · rw [smul_neg, map_neg, map_smul, hδc b.swap, hν, smul_neg, smul_comm]
    simp [hζ']

end TailRootsMain

section TailShort

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {r p : ℕ}
  {qA : QuadraticForm K U}

theorem tail_short_root_le_derivedCentralizer (hp : p.Prime) {ζ : K}
    (hζ : orderOf ζ = p) (hr : 3 ≤ r)
    (A : Subgroup (((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)))
    (hAG : A ≤ orthElementaryGroup (quadTail r qA)) (hAcard : Nat.card A = p ^ 2)
    (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) (hypVec K U (Sum.inl i)) =
          ζ ^ (χ i g).toAdd.val • hypVec K U (Sum.inl i) ∧
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inr i)) = (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K U (Sum.inr i))
    (hfix : ∀ (g : A) (u : U),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) ((0 : Fin r ⊕ Fin r → K), u) =
        (0, u))
    {α : Fin r → ℤ} (hα : ∃ i : Fin r, α = eps r i ∨ α = -eps r i) :
    ∃ a ∈ A, a ≠ 1 ∧
      tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a := by
  obtain ⟨i, hi⟩ := hα
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζ1' : ζ⁻¹ * 1 ≠ 1 := fun h => hζ1 (by
    rw [mul_one] at h
    exact inv_eq_one.mp h)
  obtain ⟨g, hg1, hgχ⟩ := exists_ne_one_mem_ker hp hAcard (χ i)
  have hk : (χ i g).toAdd = 0 := by rw [hgχ]; rfl
  have hgi : (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
      (hypVec K U (Sum.inl i)) = hypVec K U (Sum.inl i) := by
    have h := (hχ g i).1
    rw [hk] at h
    simpa using h
  have hgf : (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
      (hypVec K U (Sum.inr i)) = hypVec K U (Sum.inr i) := by
    have h := (hχ g i).2
    rw [hk] at h
    simpa using h
  refine ⟨(g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)), g.2,
    fun h => hg1 (Subtype.ext h), ?_⟩
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hj⟩ := exists_ne i
  set ζ' : Kˣ := Units.mk0 ζ hζ0 with hζ'
  set α' : Fin r → ℤ := eps r i - eps r j with hα'
  have hα'r : α' ∈ roots r := eps_sub_eps_mem_roots hj.symm
  set d : Fin r → Kˣ := fun k => ζ' ^ α' k with hd
  set δ := prodHom U (torusElt r K d) with hδ
  have hδG : δ ∈ orthElementaryGroup (quadTail r qA) := prodHom_mem_tail hr hα'r hζ0
  have hα'i : α' i = 1 := by
    simp [hα', eps_apply, hj.symm]
  have hδc : ∀ c : Fin r ⊕ Fin r,
      δ (hypVec K U c) = ((Sum.elim d d⁻¹ c : Kˣ) : K) • hypVec K U c := fun c =>
    prodHom_apply_hypVec _ c _ (torusElt_apply_single d c)
  have hδe : δ (hypVec K U (Sum.inl i)) = ζ • hypVec K U (Sum.inl i) := by
    rw [hδc, Sum.elim_inl, hd]
    simp [hα'i, hζ']
  have hδf : δ (hypVec K U (Sum.inr i)) = ζ⁻¹ • hypVec K U (Sum.inr i) := by
    rw [hδc, Sum.elim_inr, hd]
    simp [hα'i, hζ']
  have hgc := apply_hypVec_of_chars hζp χ hχ g
  have hδa : δ * (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) =
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) * δ :=
    mul_comm_of_eigen span_hypVec_tail_eq_top (by
      rintro v (⟨c, rfl⟩ | ⟨u, rfl⟩)
      · exact ⟨_, _, hδc c, hgc c⟩
      · exact ⟨1, 1, by rw [one_smul]; exact prodHom_apply_tail _ u,
          by rw [one_smul]; exact hfix g u⟩)
  have hG₀ : orthElementaryGroup (quadTail r qA) ≤ TauCeti.QuadraticMap.orthogonalGroup
      (quadTail r qA) := orthElementaryGroup_le _
  rcases hi with rfl | rfl
  · intro y hy
    obtain ⟨u₀, rfl⟩ := mem_tailRootGroup_eps.1 hy
    refine eichler_mem_derivedCentralizer (Q := quadTail r qA) hG₀ (polar_hypVec_tail _ u₀)
      (fun s => eichler_mem_elementaryGroup _ _ _) (hAG g.2) hδG hδa (κ := 1) (κ' := 1)
      (μ := ζ) (ν := 1) (by rw [hgi, one_smul]) (by rw [hfix g u₀, one_smul]) (one_mul 1) hδe
      (by rw [prodHom_apply_tail, one_smul]) (by rwa [mul_one])
  · intro y hy
    obtain ⟨u₀, rfl⟩ := mem_tailRootGroup_neg_eps.1 hy
    refine eichler_mem_derivedCentralizer (Q := quadTail r qA) hG₀ (polar_hypVec_tail _ u₀)
      (fun s => eichler_mem_elementaryGroup _ _ _) (hAG g.2) hδG hδa (κ := 1) (κ' := 1)
      (μ := ζ⁻¹) (ν := 1) (by rw [hgf, one_smul]) (by rw [hfix g u₀, one_smul]) (one_mul 1) hδf
      (by rw [prodHom_apply_tail, one_smul]) hζ1'

end TailShort

end CFSG.RankThree.PartOne.KCOrthogonal
