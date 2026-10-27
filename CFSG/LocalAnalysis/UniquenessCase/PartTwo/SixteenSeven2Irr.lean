module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2V1
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallCases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise Matrix

private theorem eq_bot_or_eq_top_of_map
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {I : Subgroup W}
    {M : Type} [Group M] {β : ↥I →* M} (hβinj : Function.Injective β)
    (hstab : ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I)
    (hirr : ∀ K : Subgroup M,
      (∀ (x : ↥H) (u : ↥I), β u ∈ K → β ⟨(x : MulAut W) u, hstab x u u.2⟩ ∈ K) →
      K = ⊥ ∨ K = ⊤) :
    ∀ J : Subgroup W, StableUnder H J → J ≤ I → J = ⊥ ∨ J = I := by
  intro J hJ hJI
  have hmap : (J.subgroupOf I).map β = ⊥ ∨ (J.subgroupOf I).map β = ⊤ := by
    refine hirr ((J.subgroupOf I).map β) ?_
    intro x u hu
    obtain ⟨j, hj, hjβ⟩ := Subgroup.mem_map.1 hu
    have hju : (j : ↥I) = u := hβinj hjβ
    have hjJ : (j : W) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have huJ : (u : W) ∈ J := by rw [← hju]; exact hjJ
    refine Subgroup.mem_map.2
      ⟨⟨(x : MulAut W) (u : W), hstab x u u.2⟩,
        Subgroup.mem_subgroupOf.2 (hJ (x : MulAut W) x.2 u huJ), rfl⟩
  rcases hmap with h | h
  · left
    refine le_bot_iff.1 fun j hj => ?_
    have hmem : β ⟨j, hJI hj⟩ ∈ (J.subgroupOf I).map β :=
      Subgroup.mem_map.2 ⟨⟨j, hJI hj⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : (⟨j, hJI hj⟩ : ↥I) = 1 := hβinj (by rw [hmem, map_one])
    simpa using congrArg Subtype.val h1
  · right
    refine le_antisymm hJI fun j hj => ?_
    have hmem : β ⟨j, hj⟩ ∈ (J.subgroupOf I).map β := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨j', hj', hj'β⟩ := Subgroup.mem_map.1 hmem
    have hjj : j' = ⟨j, hj⟩ := hβinj hj'β
    rw [hjj] at hj'
    exact Subgroup.mem_subgroupOf.1 hj'

private theorem mem_irrSet_of_map
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {I : Subgroup W}
    {M : Type} [Group M] [Nontrivial M] {β : ↥I →* M} (hβinj : Function.Injective β)
    (hβsurj : Function.Surjective β)
    (hstab : ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I)
    (hfix : I ⊓ fixV H = ⊥)
    (hirr : ∀ K : Subgroup M,
      (∀ (x : ↥H) (u : ↥I), β u ∈ K → β ⟨(x : MulAut W) u, hstab x u u.2⟩ ∈ K) →
      K = ⊥ ∨ K = ⊤) :
    I ∈ irrSet H := by
  have hstab' : StableUnder H I := fun x hx u hu => hstab ⟨x, hx⟩ u hu
  have hmin := eq_bot_or_eq_top_of_map hβinj hstab hirr
  have hIne : I ≠ ⊥ := by
    intro hI
    obtain ⟨m, hm⟩ := exists_ne (1 : M)
    obtain ⟨u, hu⟩ := hβsurj m
    have hmem : (u : W) ∈ (⊥ : Subgroup W) := by
      rw [← hI]
      exact u.2
    have : (u : ↥I) = 1 := Subtype.ext (Subgroup.mem_bot.1 hmem)
    rw [this, map_one] at hu
    exact hm hu.symm
  have hIbot : (⊥ : Subgroup W) < I := lt_of_le_of_ne bot_le (Ne.symm hIne)
  have hCstab : StableUnder H (commSub I H) := by
    intro x hx u hu
    refine Subgroup.closure_induction (p := fun y _ => x y ∈ commSub I H)
      ?_ ?_ ?_ ?_ hu
    · rintro y ⟨z, hz, w, hw, rfl⟩
      refine Subgroup.subset_closure ⟨x * z * x⁻¹, H.mul_mem (H.mul_mem hx hz) (H.inv_mem hx),
        x w, hstab' x hx w hw, ?_⟩
      calc (x * z * x⁻¹) (x w) * (x w)⁻¹ = x (z w) * (x w)⁻¹ := by
            simp only [MulAut.mul_apply, MulAut.inv_apply_self]
        _ = x (z w) * x w⁻¹ := by rw [← map_inv]
        _ = x (z w * w⁻¹) := by rw [map_mul]
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b _ _ iha ihb; rw [map_mul]; exact Subgroup.mul_mem _ iha ihb
    · intro a _ iha; rw [map_inv]; exact Subgroup.inv_mem _ iha
  have hCI : commSub I H ≤ I := commSub_le_of_invariant hstab'
  have hcomm : commSub I H = I := by
    rcases hmin (commSub I H) hCstab hCI with h | h
    · exfalso
      have hIle : I ≤ fixV H := commSub_eq_bot_iff.1 h
      have : I = ⊥ := by
        rw [← hfix]
        exact le_antisymm (le_inf le_rfl hIle) inf_le_left
      exact hIbot.ne' this
    · exact h
  refine ⟨hcomm, ?_⟩
  rw [hfix]
  refine ⟨hIbot, hstab', ?_, ?_⟩
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJ _ hJI
    exact hmin J hJ hJI

theorem s16c167_mem_irrSet_alt {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {I : Subgroup W} {n : ℕ} (hn : 5 ≤ n) (h : AlternatingNatural H I ⊥ n) : I ∈ irrSet H := by
  have hn0 : 0 < n := by omega
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hsurj, -, hksec, hIinv, -, hsecinv, -, β, hβsurj, hβker, hβeq⟩ := hπ
  let e : (↥(G6.coreMod n) ⧸ (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃*
      Multiplicative (AltHeart n) := CFSG.Quasithin.C124.altQuotEquiv n hn0
  let β' : ↥I →* Multiplicative (AltHeart n) := e.toMonoidHom.comp β
  have hstab : ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I := hIinv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hβinj' : Function.Injective β' := e.injective.comp hβinj
  have hβsurj' : Function.Surjective β' := e.surjective.comp hβsurj
  have hβe' : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥I)
      (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I),
      β' ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
        (FFModel.altDn n).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  have hfix : I ⊓ fixV H = ⊥ := by
    refine le_bot_iff.1 fun w hw => ?_
    obtain ⟨hwI, hwfix⟩ := Subgroup.mem_inf.1 hw
    have hbeta : β' ⟨w, hwI⟩ = 1 := by
      have h2 : Multiplicative.toAdd (β' ⟨w, hwI⟩) = 0 := by
        apply CFSG.Quasithin.C41Pf.AltN.heart_fixed_eq_zero (by omega)
        intro σ hσ
        have hfixw : ((π ⟨σ, hσ⟩ : ↥H) : MulAut W) w = w :=
          (mem_fixV.1 hwfix) _ (π ⟨σ, hσ⟩).2
        have h3 := hβe' ⟨σ, hσ⟩ ⟨w, hwI⟩ (hstab (π ⟨σ, hσ⟩) w hwI)
        have h4 : β' ⟨((π ⟨σ, hσ⟩ : ↥H) : MulAut W) w,
            hstab (π ⟨σ, hσ⟩) w hwI⟩ = β' ⟨w, hwI⟩ := congrArg β' (Subtype.ext hfixw)
        have h5 := congrArg Multiplicative.toAdd (h3.symm.trans h4)
        simpa using h5
      exact Multiplicative.toAdd.injective (by simpa using h2)
    have h6 : (⟨w, hwI⟩ : ↥I) = 1 := hβinj' (by rw [hbeta]; exact (map_one β').symm)
    simpa using congrArg Subtype.val h6
  have hirr : ∀ K : Subgroup (Multiplicative (AltHeart n)),
      (∀ (x : ↥H) (u : ↥I), β' u ∈ K → β' ⟨(x : MulAut W) u, hstab x u u.2⟩ ∈ K) →
      K = ⊥ ∨ K = ⊤ := by
    intro K hK
    set Y : AddSubgroup (AltHeart n) := Subgroup.toAddSubgroup' K with hY
    have hYinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ y ∈ Y,
        CFSG.Quasithin.C41Pf.AltN.hAct n σ y ∈ Y := by
      intro σ hσ y hy
      rw [Subgroup.mem_toAddSubgroup'] at hy ⊢
      obtain ⟨u, hu⟩ := hβsurj' (Multiplicative.ofAdd y)
      have h1 : β' ⟨((π ⟨σ, hσ⟩ : ↥H) : MulAut W) (u : W),
          hstab (π ⟨σ, hσ⟩) u u.2⟩ ∈ K := hK (π ⟨σ, hσ⟩) u (by rw [hu]; exact hy)
      rw [hβe' ⟨σ, hσ⟩ u (hstab (π ⟨σ, hσ⟩) u u.2), hu] at h1
      exact h1
    rcases CFSG.Quasithin.C41Pf.AltN.heart_irreducible (by omega : 4 ≤ n) Y hYinv with h | h
    · left
      refine le_bot_iff.1 fun z hz => ?_
      have hz' : Multiplicative.toAdd z ∈ Y :=
        (Subgroup.mem_toAddSubgroup' K (Multiplicative.toAdd z)).2 hz
      rw [h] at hz'
      have hz0 : Multiplicative.toAdd z = 0 := AddSubgroup.mem_bot.1 hz'
      exact Multiplicative.toAdd.injective (by simpa using hz0)
    · right
      refine le_antisymm le_top fun z _ => ?_
      have hz : Multiplicative.toAdd z ∈ Y := by rw [h]; exact AddSubgroup.mem_top _
      exact (Subgroup.mem_toAddSubgroup' K (Multiplicative.toAdd z)).1 hz
  haveI : Nontrivial (Multiplicative (AltHeart n)) := by
    refine ⟨?_, ?_, ?_⟩
    · exact Multiplicative.ofAdd (QuotientAddGroup.mk
        (CFSG.Quasithin.C41Pf.AltN.pairVec (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))
    · exact 1
    · intro h
      have h' : (QuotientAddGroup.mk
          (CFSG.Quasithin.C41Pf.AltN.pairVec (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) :
            AltHeart n) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa using this
      exact CFSG.Quasithin.C41Pf.AltN.mk_pairVec_ne_zero (by omega) (by simp) h'
  exact @mem_irrSet_of_map W _ H I (Multiplicative (AltHeart n)) _ _ β'
    hβinj' hβsurj' hstab hfix hirr

theorem s16c167_mem_irrSet_ln {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {I : Subgroup W} {m : ℕ} (hm : 2 ≤ m) (h : BinaryNaturalSL H I ⊥ m 1) : I ∈ irrSet H := by
  have hfix : I ⊓ fixV H = ⊥ := s16c167_inf_fixV_eq_bot_of_binaryNaturalSL hm h
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  letI := hK
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I := R.U_inv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  haveI : Nontrivial (Multiplicative (Fin m → K)) := by
    haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    infer_instance
  refine mem_irrSet_of_map hβinj hβsurj hstab hfix ?_
  intro A hA
  have hA' : ∀ (i j : Fin m) (hij : i ≠ j) (c : K) (v : Fin m → K),
      v ∈ Subgroup.toAddSubgroup' A →
      Matrix.transvection i j c *ᵥ v ∈ Subgroup.toAddSubgroup' A := by
    intro i j hij c v hv
    have hvA : Multiplicative.ofAdd v ∈ A :=
      (Subgroup.mem_toAddSubgroup' A v).1 hv
    let g : ↥(StatedSL m K) :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
        (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero),
       Subgroup.subset_closure (by
        change (Matrix.transvection i j c).det = 1
        exact Matrix.det_transvection_of_ne i j hij c)⟩
    have hγA : natAct (StatedSL m K) g (Multiplicative.ofAdd v) ∈ A := by
      obtain ⟨u, hu⟩ := hβsurj (Multiplicative.ofAdd v)
      have h1 : β ⟨((π g : ↥H) : MulAut W) (u : W), hstab (π g) u u.2⟩ ∈ A :=
        hA (π g) u (by rw [hu]; exact hvA)
      have h2 : natAct (StatedSL m K) g (β u) ∈ A :=
        (hβe g u (hstab (π g) u u.2)) ▸ h1
      rwa [hu] at h2
    refine (Subgroup.mem_toAddSubgroup' A (Matrix.transvection i j c *ᵥ v)).2 ?_
    have heq : natAct (StatedSL m K) g (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd (Matrix.transvection i j c *ᵥ v) := rfl
    rw [← heq]
    exact hγA
  rcases CFSG.Quasithin.H.eq_bot_or_eq_top_of_transvection_inv hm
      (Subgroup.toAddSubgroup' A) hA' with h | h
  · left
    refine le_bot_iff.1 fun z hz => ?_
    have hz' : Multiplicative.toAdd z ∈ Subgroup.toAddSubgroup' A :=
      (Subgroup.mem_toAddSubgroup' A (Multiplicative.toAdd z)).2 hz
    rw [h] at hz'
    exact Multiplicative.toAdd.injective (by simpa using AddSubgroup.mem_bot.1 hz')
  · right
    refine le_antisymm le_top fun z _ => ?_
    have hz : Multiplicative.toAdd z ∈ Subgroup.toAddSubgroup' A := by
      rw [h]; exact AddSubgroup.mem_top _
    exact (Subgroup.mem_toAddSubgroup' A (Multiplicative.toAdd z)).1 hz

section Symplectic

variable {d : ℕ} {K : Type} [Field K]

private def spForm (d : ℕ) (K : Type) [Field K] :
    (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K) →ₗ[K] K :=
  Matrix.toLinearMap₂' K (Matrix.J (Fin d) K)

private theorem spForm_apply (x y : Fin d ⊕ Fin d → K) :
    spForm d K x y =
      ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i)) := by
  simp [spForm, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Matrix.J,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

private theorem spForm_self (x : Fin d ⊕ Fin d → K) : spForm d K x x = 0 := by
  rw [spForm_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

private theorem spForm_swap (x y : Fin d ⊕ Fin d → K) : spForm d K y x = -spForm d K x y := by
  rw [spForm_apply, spForm_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem spForm_swap_ne_zero {x y : Fin d ⊕ Fin d → K} (h : spForm d K x y ≠ 0) :
    spForm d K y x ≠ 0 := by
  rw [spForm_swap]
  exact neg_ne_zero.mpr h

private theorem spForm_single_inl (x : Fin d ⊕ Fin d → K) (i : Fin d) :
    spForm d K x (Pi.single (Sum.inl i) 1) = x (Sum.inr i) := by
  rw [spForm_apply]
  simp [Pi.single_apply]

private theorem spForm_single_inr (x : Fin d ⊕ Fin d → K) (i : Fin d) :
    spForm d K x (Pi.single (Sum.inr i) 1) = -x (Sum.inl i) := by
  rw [spForm_apply]
  simp [Pi.single_apply]

private theorem spEq_zero_of_form_eq_zero {x : Fin d ⊕ Fin d → K}
    (h : ∀ y, spForm d K x y = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    rw [spForm_single_inr] at this
    simpa using this
  · have := h (Pi.single (Sum.inl i) 1)
    rwa [spForm_single_inl] at this

private theorem spExists_form_ne_zero {x : Fin d ⊕ Fin d → K} (hx : x ≠ 0) :
    ∃ y, spForm d K x y ≠ 0 := by
  by_contra h
  exact hx (spEq_zero_of_form_eq_zero fun y => not_not.mp fun hy => h ⟨y, hy⟩)

private theorem spExists_form_ne_zero_ne_zero {v w : Fin d ⊕ Fin d → K} (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ z, spForm d K v z ≠ 0 ∧ spForm d K w z ≠ 0 := by
  obtain ⟨y₁, hy₁⟩ := spExists_form_ne_zero hv
  obtain ⟨y₂, hy₂⟩ := spExists_form_ne_zero hw
  by_cases h₁ : spForm d K w y₁ = 0
  · by_cases h₂ : spForm d K v y₂ = 0
    · refine ⟨y₁ + y₂, ?_, ?_⟩
      · rwa [map_add, h₂, add_zero]
      · rwa [map_add, h₁, zero_add]
    · exact ⟨y₂, h₂, hy₂⟩
  · exact ⟨y₁, hy₁, h₁⟩

private theorem spMem_iff_form (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) :
    A ∈ Matrix.symplecticGroup (Fin d) K ↔
      ∀ x y, spForm d K (A *ᵥ x) (A *ᵥ y) = spForm d K x y := by
  have key : ∀ x y, spForm d K (A *ᵥ x) (A *ᵥ y) =
      Matrix.toLinearMap₂' K (Aᵀ * Matrix.J (Fin d) K * A) x y := by
    intro x y
    rw [← Matrix.toLinearMap₂'_comp]
    simp [spForm, Matrix.toLin'_apply]
  rw [SymplecticGroup.mem_iff']
  constructor
  · intro h x y
    rw [key, h]
    rfl
  · intro h
    have h2 : (Matrix.toLinearMap₂' K (Aᵀ * Matrix.J (Fin d) K * A) :
        (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K) →ₗ[K] K) = spForm d K := by
      apply LinearMap.ext₂
      intro x y
      rw [← key, h]
    have h3 := congrArg (LinearMap.toMatrix₂' K) h2
    rwa [spForm, LinearMap.toMatrix'_toLinearMap₂', LinearMap.toMatrix'_toLinearMap₂'] at h3

private def spOfLin (f : (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K))
    (hf : ∀ x y, spForm d K (f x) (f y) = spForm d K x y) :
    TauCeti.GLSymplectic (Fin d) K :=
  ⟨TauCeti.GLSymplectic.ofSymplecticGroup (Fin d) K
    ⟨LinearMap.toMatrix' f, (spMem_iff_form _).mpr (by
      simpa [LinearMap.toMatrix'_mulVec] using hf)⟩,
    TauCeti.GLSymplectic.ofSymplecticGroup_mem _ _ _⟩

private theorem spOfLin_smul (f : (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K))
    (hf : ∀ x y, spForm d K (f x) (f y) = spForm d K x y) (x : Fin d ⊕ Fin d → K) :
    spOfLin f hf • x = f x := by
  change (TauCeti.GLSymplectic.ofSymplecticGroup (Fin d) K _ :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) *ᵥ x = f x
  rw [TauCeti.GLSymplectic.coe_ofSymplecticGroup]
  exact LinearMap.toMatrix'_mulVec f x

private def spTv (u : Fin d ⊕ Fin d → K) (c : K) : TauCeti.GLSymplectic (Fin d) K :=
  spOfLin (LinearMap.id + (c • (spForm d K).flip u).smulRight u) (by
    intro x y
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, map_add, map_smul, spForm_self]
    rw [spForm_swap u y]
    ring)

private theorem spTv_smul (u : Fin d ⊕ Fin d → K) (c : K) (x : Fin d ⊕ Fin d → K) :
    spTv u c • x = x + (c * spForm d K x u) • u := by
  rw [spTv, spOfLin_smul]
  simp

private theorem spExists_fix_map {u v w : Fin d ⊕ Fin d → K}
    (h : spForm d K u v = spForm d K u w) (hvw : spForm d K v w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin d) K, g • u = u ∧ g • v = w := by
  refine ⟨spTv (w - v) (spForm d K v w)⁻¹, ?_, ?_⟩
  · rw [spTv_smul, map_sub, h, sub_self, mul_zero, zero_smul, add_zero]
  · rw [spTv_smul, map_sub, spForm_self, sub_zero, inv_mul_cancel₀ hvw, one_smul]
    abel

private theorem spExists_fix_map_two {u v z w : Fin d ⊕ Fin d → K}
    (h₁ : spForm d K u v = spForm d K u z) (h₂ : spForm d K u z = spForm d K u w)
    (hvz : spForm d K v z ≠ 0) (hzw : spForm d K z w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin d) K, g • u = u ∧ g • v = w := by
  obtain ⟨g₁, hg₁u, hg₁v⟩ := spExists_fix_map h₁ hvz
  obtain ⟨g₂, hg₂u, hg₂z⟩ := spExists_fix_map h₂ hzw
  exact ⟨g₂ * g₁, by rw [mul_smul, hg₁u, hg₂u], by rw [mul_smul, hg₁v, hg₂z]⟩

private theorem spExists_smul_eq_vec {v w : Fin d ⊕ Fin d → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : TauCeti.GLSymplectic (Fin d) K, g • v = w := by
  by_cases hvw : spForm d K v w = 0
  · obtain ⟨z, hvz, hwz⟩ := spExists_form_ne_zero_ne_zero hv hw
    obtain ⟨g, -, hg⟩ := spExists_fix_map_two (u := 0) (v := v) (z := z) (w := w)
      (by simp) (by simp) hvz (spForm_swap_ne_zero hwz)
    exact ⟨g, hg⟩
  · obtain ⟨g, -, hg⟩ := spExists_fix_map (u := 0) (by simp) hvw
    exact ⟨g, hg⟩

private theorem spNatAct_eq (g : TauCeti.GLSymplectic (Fin d) K) (x : Fin d ⊕ Fin d → K) :
    natAct (StatedSp d K)
      ⟨(g : Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K), by
        rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]; exact g.2⟩
      (Multiplicative.ofAdd x) = Multiplicative.ofAdd (g • x) := rfl

private theorem spNatAct_irr {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K]
    (A : Subgroup (Multiplicative (Fin d ⊕ Fin d → K)))
    (hA : ∀ γ : ↥(StatedSp d K), ∀ x ∈ A, natAct (StatedSp d K) γ x ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have haA : (a : Multiplicative (Fin d ⊕ Fin d → K)) ∈ A := a.2
  set v : Fin d ⊕ Fin d → K := Multiplicative.toAdd (a : Multiplicative (Fin d ⊕ Fin d → K)) with hv
  have hv0 : v ≠ 0 := by
    intro h
    apply ha1
    apply Subtype.ext
    have h' : Multiplicative.toAdd (a : Multiplicative (Fin d ⊕ Fin d → K)) = 0 := by
      rw [← hv]; exact h
    simpa using congrArg Multiplicative.ofAdd h'
  have haeq : (a : Multiplicative (Fin d ⊕ Fin d → K)) = Multiplicative.ofAdd v := by
    rw [hv]; rfl
  refine eq_top_iff.2 fun x _ => ?_
  set w : Fin d ⊕ Fin d → K := Multiplicative.toAdd x with hw
  by_cases hw0 : w = 0
  · have hx0 : Multiplicative.toAdd x = 0 := by rw [← hw, hw0]
    rw [show x = 1 from Multiplicative.toAdd.injective (by simpa using hx0)]
    exact Subgroup.one_mem A
  · obtain ⟨g, hg⟩ := spExists_smul_eq_vec (K := K) hv0 hw0
    have hgmem : (g : Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K) ∈ StatedSp d K := by
      rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]; exact g.2
    have hγ := hA ⟨(g : Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K), hgmem⟩ a haA
    rw [haeq, spNatAct_eq g v, hg] at hγ
    simpa [hw] using hγ

private theorem spFixed_eq_zero {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K]
    {v : Fin d ⊕ Fin d → K}
    (hv : ∀ γ : ↥(StatedSp d K),
      natAct (StatedSp d K) γ (Multiplicative.ofAdd v) = Multiplicative.ofAdd v) : v = 0 := by
  by_contra hv0
  obtain ⟨w, hw⟩ := spExists_form_ne_zero hv0
  have hgmem : (spTv w (spForm d K v w)⁻¹ :
      Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K) ∈ StatedSp d K := by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (spTv w (spForm d K v w)⁻¹).2
  have hfix := hv ⟨(spTv w (spForm d K v w)⁻¹ :
    Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K), hgmem⟩
  rw [spNatAct_eq (spTv w (spForm d K v w)⁻¹) v, spTv_smul, inv_mul_cancel₀ hw, one_smul] at hfix
  have hvw : v + w = v := Multiplicative.ofAdd.injective hfix
  have hw0 : w = 0 := add_left_cancel (a := v) (by simpa using hvw)
  rw [hw0] at hw
  exact hw (map_zero (spForm d K v))

end Symplectic

theorem s16c167_mem_irrSet_sp {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {I : Subgroup W} {n : ℕ} (hn : 2 ≤ n) (h : NatSpn H I ⊥ n 1) : I ∈ irrSet H := by
  obtain ⟨hEven, K, hK, hKf, hK2, π, hπ⟩ := h
  letI := hK
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I := R.U_inv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  haveI : Nontrivial (Multiplicative (Fin (n / 2) ⊕ Fin (n / 2) → K)) := by
    haveI : Nonempty (Fin (n / 2)) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hdiv : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hEven
  have hn2 : 1 ≤ n / 2 := by omega
  refine @mem_irrSet_of_map W _ H I (Multiplicative (Fin (n / 2) ⊕ Fin (n / 2) → K)) _ _ β
    hβinj hβsurj hstab ?_ ?_
  · refine le_bot_iff.1 fun w hw => ?_
    obtain ⟨hwI, hwfix⟩ := Subgroup.mem_inf.1 hw
    have hbeta : β ⟨w, hwI⟩ = 1 := by
      have h2 : Multiplicative.toAdd (β ⟨w, hwI⟩) = 0 := by
        refine spFixed_eq_zero hn2 (K := K) fun γ => ?_
        have hfixw : ((π γ : ↥H) : MulAut W) w = w := (mem_fixV.1 hwfix) _ (π γ).2
        have h3 := hβe γ ⟨w, hwI⟩ (hstab (π γ) w hwI)
        have h4 : β ⟨((π γ : ↥H) : MulAut W) w, hstab (π γ) w hwI⟩ = β ⟨w, hwI⟩ :=
          congrArg β (Subtype.ext hfixw)
        have h5 := congrArg Multiplicative.toAdd (h3.symm.trans h4)
        simpa using h5
      exact Multiplicative.toAdd.injective (by simpa using h2)
    have h6 : (⟨w, hwI⟩ : ↥I) = 1 := hβinj (by rw [hbeta]; exact (map_one β).symm)
    simpa using congrArg Subtype.val h6
  · intro A hA
    have hA' : ∀ γ : ↥(StatedSp (n / 2) K), ∀ x ∈ A,
        natAct (StatedSp (n / 2) K) γ x ∈ A := by
      intro γ x hx
      obtain ⟨u, hu⟩ := hβsurj x
      have h1 : β ⟨((π γ : ↥H) : MulAut W) (u : W), hstab (π γ) u u.2⟩ ∈ A :=
        hA (π γ) u (by rw [hu]; exact hx)
      have h2 : natAct (StatedSp (n / 2) K) γ (β u) ∈ A :=
        (hβe γ u (hstab (π γ) u u.2)) ▸ h1
      rwa [hu] at h2
    rcases spNatAct_irr hn2 (K := K) A hA' with h | h
    · left; exact h
    · right; exact h

section OrthogonalIrr

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth

private theorem elemGroup_submodule_eq_bot_or_top
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    (W : Submodule K V) (hW : ∀ g ∈ elementaryGroup Q, ∀ x ∈ W, g x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨P, hPorth⟩ := hP
  have hWe : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W :=
    fun u w x hx => hW _ (eichler_mem_elementaryGroup Q u w) x hx
  have htwo : ∀ i : Fin 2, ∃ j : Fin 2, j ≠ i := by
    intro i
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have hsing : ∃ u : V, u ≠ 0 ∧ Q u = 0 ∧ u ∈ W := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    by_cases hA : ∃ i : Fin 2, polar Q x (P i).e ≠ 0
    · obtain ⟨i, hi⟩ := hA
      obtain ⟨j, hji⟩ := htwo i
      exact ⟨(P i).e, (P i).e_ne_zero, (P i).Q_e,
        exchange_mem (P i) (P j) (hPorth i j (Ne.symm hji)) W (hWe _ _) (hWe _ _) hxW hi⟩
    by_cases hB : ∃ i : Fin 2, polar Q x (P i).f ≠ 0
    · obtain ⟨i, hi⟩ := hB
      obtain ⟨j, hji⟩ := htwo i
      exact ⟨(P i).f, (P i).f_ne_zero, (P i).Q_f,
        exchange_mem (swapPair (P i)) (P j) (orth_swapPair_left (hPorth i j (Ne.symm hji))) W
          (hWe _ _) (hWe _ _) hxW hi⟩
    push Not at hA hB
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx0
    set w : V := y - (polar Q y (P 0).f) • (P 0).e - (polar Q y (P 0).e) • (P 0).f with hw
    have hwe : polar Q (P 0).e w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).e, polar_self_eq_zero (P 0).Q_e, (P 0).polar_ef]
      ring
    have hwf : polar Q (P 0).f w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).f, (P 0).polar_fe, polar_self_eq_zero (P 0).Q_f]
      ring
    have hxw : polar Q x w ≠ 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        hA 0, hB 0]
      simpa using hy
    exact ⟨(P 0).e, (P 0).e_ne_zero, (P 0).Q_e,
      perp_extract_mem (P 0) W hxW (hA 0) (HypPair.mem_perp.2 ⟨hwe, hwf⟩)
        (hWe (P 0).e w x hxW) hxw⟩
  obtain ⟨u₀, hu₀0, hu₀Q, hu₀W⟩ := hsing
  have hall : ∀ v : V, Q v = 0 → v ∈ W := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact W.zero_mem
    obtain ⟨g, hg, hgv⟩ :=
      exists_mem_elementaryGroup_apply_eq hQ (hPorth 0 1 (by decide)) hu₀0 hv0
        (by rw [hu₀Q, hv])
    rw [← hgv]
    exact hW g hg u₀ hu₀W
  rw [eq_top_iff]
  intro v _
  have hle : Submodule.span K {u : V | Q u = 0} ≤ W := by
    rw [Submodule.span_le]
    rintro u hu
    exact hall u hu
  exact hle (by rw [span_singular_eq_top (P 0)]; exact Submodule.mem_top)

end OrthogonalIrr

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
  CFSG.LieType.Universal.Spin

private theorem mem_irrSet_omegaMinus_of_eichler {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {I : Subgroup W} {d : ℕ} (hd : 3 ≤ d)
    {K : Type} [Field K] [Finite K] (b c : K) (hK2 : Nat.card K = 2)
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hE : ∀ g ∈ elementaryGroup (quadMinus d K b c),
      (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g ∈
        StatedOmega (StatedQuadMinus d K b c))
    (hReal : (FFModel.nat (StatedOmega (StatedQuadMinus d K b c))).Realizes H I ⊥) :
    I ∈ irrSet H := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨π, hπ⟩ := hReal
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I := R.U_inv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have htwo : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    have h2 : x ^ 2 = x := by
      have := FiniteField.pow_card x
      rwa [← Nat.card_eq_fintype_card, hK2] at this
    have h3 : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hQ : (polarBilin (quadMinus d K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite d K hpoly
  have hP : ∃ P : Fin 2 → HypPair (quadMinus d K b c), ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨fun i => minusPair K b c (Fin.castLE (by omega : 2 ≤ d - 1) i), ?_⟩
    intro i j hij
    exact minusPair_orth (fun h => hij (Fin.castLE_injective _ h))
  obtain ⟨P, hPorth⟩ := hP
  have hmodel : ∀ A : Subgroup (Multiplicative (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K)),
      (∀ γ : ↥(StatedOmega (StatedQuadMinus d K b c)), ∀ x ∈ A,
        natAct (StatedOmega (StatedQuadMinus d K b c)) γ x ∈ A) → A = ⊥ ∨ A = ⊤ := by
    intro A hAc
    let W : Submodule K (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) :=
      { carrier := {x | Multiplicative.ofAdd x ∈ A}
        zero_mem' := Subgroup.one_mem A
        add_mem' := by
          intro x y hx hy
          change Multiplicative.ofAdd (x + y) ∈ A
          rw [show Multiplicative.ofAdd (x + y) =
            Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl]
          exact Subgroup.mul_mem A hx hy
        smul_mem' := by
          intro t x hx
          rcases htwo t with rfl | rfl
          · change Multiplicative.ofAdd (0 • x) ∈ A; rw [zero_smul]; exact Subgroup.one_mem A
          · change Multiplicative.ofAdd (1 • x) ∈ A; rw [one_smul]; exact hx }
    have hW : ∀ g ∈ elementaryGroup (quadMinus d K b c), ∀ x ∈ W, g x ∈ W := by
      intro g hg x hx
      change Multiplicative.ofAdd (g x) ∈ A
      have hmem := hE g hg
      have h1 := hAc ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩
        (Multiplicative.ofAdd x) hx
      have hval : natAct (StatedOmega (StatedQuadMinus d K b c))
          ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩
          (Multiplicative.ofAdd x) = Multiplicative.ofAdd (g x) := by
        rw [natAct]
        congr 1
        rw [← toLinEquiv_apply]
        simp
      rwa [hval] at h1
    rcases elemGroup_submodule_eq_bot_or_top hQ ⟨P, hPorth⟩ W hW with hbot | htop
    · left
      refine le_bot_iff.1 fun x hx => ?_
      have hxW : Multiplicative.toAdd x ∈ W := hx
      rw [hbot] at hxW
      exact Multiplicative.toAdd.injective (by simpa using hxW)
    · right
      refine le_antisymm le_top fun x _ => ?_
      exact (show Multiplicative.toAdd x ∈ W from by rw [htop]; exact Submodule.mem_top)
  haveI : Nontrivial (Multiplicative (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K)) := by
    haveI : Nonempty (Fin (d - 1)) := ⟨⟨0, by omega⟩⟩
    infer_instance
  refine @mem_irrSet_of_map W _ H I
    (Multiplicative (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K)) _ _ β hβinj hβsurj hstab ?_ ?_
  ·
    refine le_bot_iff.1 fun w hw => ?_
    obtain ⟨hwI, hwfix⟩ := Subgroup.mem_inf.1 hw
    have hbeta : β ⟨w, hwI⟩ = 1 := by
      by_contra hbne
      set v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K :=
        Multiplicative.toAdd (β ⟨w, hwI⟩) with hv
      have hv0 : v ≠ 0 := fun h =>
        hbne (Multiplicative.toAdd.injective (by rw [← hv, h, toAdd_one]))
      have hline : ∀ g ∈ elementaryGroup (quadMinus d K b c),
          ∀ x ∈ Submodule.span K ({v} : Set _), g x ∈ Submodule.span K ({v} : Set _) := by
        intro g hg x hx
        obtain ⟨cc, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul]
        refine Submodule.smul_mem _ cc ?_
        have hmem := hE g hg
        have hfixw : ((π ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩ :
            ↥H) : MulAut W) w = w := (mem_fixV.1 hwfix) _ (π _).2
        have h3 := hβe ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩
          ⟨w, hwI⟩ (hstab _ w hwI)
        have h4 : β ⟨((π ⟨(toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g, hmem⟩ :
            ↥H) : MulAut W) w, hstab _ w hwI⟩ = β ⟨w, hwI⟩ :=
          congrArg β (Subtype.ext hfixw)
        have h5 := congrArg Multiplicative.toAdd (h3.symm.trans h4)
        have hgv : g v = v := by
          have h5' : ((toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g :
              GL (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K) *ᵥ v = v := h5
          rw [← toLinEquiv_apply
            (A := (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g)] at h5'
          rwa [MulEquiv.apply_symm_apply] at h5'
        rw [hgv]
        exact Submodule.subset_span (Set.mem_singleton v)
      rcases elemGroup_submodule_eq_bot_or_top hQ ⟨P, hPorth⟩
          (Submodule.span K ({v} : Set _)) hline with hbot | htop
      · have : v ∈ (⊥ : Submodule K _) := hbot ▸ Submodule.subset_span (Set.mem_singleton v)
        exact hv0 (by simpa using this)
      · have h0 : (P 0).e ∈ Submodule.span K ({v} : Set _) := htop ▸ Submodule.mem_top
        have h1 : (P 1).e ∈ Submodule.span K ({v} : Set _) := htop ▸ Submodule.mem_top
        obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp h0
        obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp h1
        have hc₀0 : c₀ ≠ 0 := fun h => (P 0).e_ne_zero (by rw [← hc₀, h, zero_smul])
        have hkey : c₁ * polar (quadMinus d K b c) v (P 0).f = 0 := by
          have hfe : polar (quadMinus d K b c) (P 1).e (P 0).f = 0 := by
            have h := (hPorth 0 1 (by decide)).fe
            rwa [polar_comm] at h
          rw [← hc₁] at hfe
          rwa [polar_smul_left_eq] at hfe
        have hone : c₀ * polar (quadMinus d K b c) v (P 0).f = 1 := by
          have hef : polar (quadMinus d K b c) (P 0).e (P 0).f = 1 := (P 0).polar_ef
          rw [← hc₀] at hef
          rwa [polar_smul_left_eq] at hef
        have hc₁0 : c₁ = 0 := by
          rcases mul_eq_zero.mp hkey with h | h
          · exact h
          · exfalso
            rw [h, mul_zero] at hone
            exact one_ne_zero hone.symm
        exact (P 1).e_ne_zero (by rw [← hc₁, hc₁0, zero_smul])
    have h6 : (⟨w, hwI⟩ : ↥I) = 1 := hβinj (by rw [hbeta]; exact (map_one β).symm)
    simpa using congrArg Subtype.val h6
  ·
    intro A hA
    have hA' : ∀ γ : ↥(StatedOmega (StatedQuadMinus d K b c)), ∀ x ∈ A,
        natAct (StatedOmega (StatedQuadMinus d K b c)) γ x ∈ A := by
      intro γ x hx
      obtain ⟨u, hu⟩ := hβsurj x
      have h1 : β ⟨((π γ : ↥H) : MulAut W) (u : W), hstab (π γ) u u.2⟩ ∈ A :=
        hA (π γ) u (by rw [hu]; exact hx)
      have h2 : natAct (StatedOmega (StatedQuadMinus d K b c)) γ (β u) ∈ A :=
        (hβe γ u (hstab (π γ) u u.2)) ▸ h1
      rwa [hu] at h2
    exact hmodel A hA'

private theorem elementaryGroup_le_commutator_of_perfect {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (hperf : Group.IsPerfect ↥(elementaryGroup Q)) :
    elementaryGroup Q ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  haveI := hperf
  calc elementaryGroup Q = ⁅elementaryGroup Q, elementaryGroup Q⁆ :=
        (Subgroup.commutator_eq_self).symm
    _ ≤ _ := Subgroup.commutator_mono (elementaryGroup_le_orthogonalGroup Q)
        (elementaryGroup_le_orthogonalGroup Q)

private theorem eichler_mem_statedOmega {d : ℕ} (hd : 3 ≤ d) {K : Type} [Field K] (b c : K)
    (hK2 : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K)}
    (hg : g ∈ elementaryGroup (quadMinus d K b c)) :
    (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g ∈
      StatedOmega (StatedQuadMinus d K b c) := by
  haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK2
  have hQ : (polarBilin (quadMinus d K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite d K hpoly
  have hfr : 6 ≤ Module.finrank K (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega
  have hperf : Group.IsPerfect ↥(elementaryGroup (quadMinus d K b c)) :=
    Group.isPerfect_def.mpr
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.commutator_elementaryGroup_eq_top_f2
        hQ hfr)
  have hle : elementaryGroup (quadMinus d K b c) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c)⁆ :=
    elementaryGroup_le_commutator_of_perfect hperf
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
    (CFSG.LieType.Universal.Spin.coe_quadMinus d K b c), Subgroup.mem_comap]
  change (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K)
    ((toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g) ∈
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c)⁆
  rw [MulEquiv.apply_symm_apply]
  exact hle hg

theorem s16c167_mem_irrSet_omegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {I : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 8)
    (h : NatOmegaMinus H I ⊥ n 1) : I ∈ irrSet H := by
  rcases hn with rfl | rfl
  · obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
    letI := hK
    haveI : Finite K := hKf
    exact mem_irrSet_omegaMinus_of_eichler (d := 3) (by norm_num) b c hK2 hpoly
      (fun g hg => eichler_mem_statedOmega (by norm_num) b c hK2 hpoly hg) ⟨π, hπ⟩
  · obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
    letI := hK
    haveI : Finite K := hKf
    exact mem_irrSet_omegaMinus_of_eichler (d := 4) (by norm_num) b c hK2 hpoly
      (fun g hg => eichler_mem_statedOmega (by norm_num) b c hK2 hpoly hg) ⟨π, hπ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
