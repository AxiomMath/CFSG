module

public import CFSG.Quasithin.Background.C48PfFourModPfMat
public import CFSG.Quasithin.Background.C48PfFourModPfSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L

variable {W : Type*} [CommGroup W]

theorem eq_bot_of_forall_fixed {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut W} {A : Subgroup Γ}
    {V : Subgroup W} (hgen : V ≤ Subgroup.closure {w | ∃ t ∈ A, ∃ v ∈ V, ρ t v * v⁻¹ = w})
    (hfix : ∀ t ∈ A, ∀ v ∈ V, ρ t v = v) : V = ⊥ := by
  rw [eq_bot_iff]
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨t, ht, v, hv, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_bot, hfix t ht v hv, mul_inv_cancel]

theorem le_of_forall_comm_mem {Γ : Type*} [Group Γ] {ρ : Γ →* MulAut W} {A : Subgroup Γ}
    {V J : Subgroup W} (hgen : V ≤ Subgroup.closure {w | ∃ t ∈ A, ∃ v ∈ V, ρ t v * v⁻¹ = w})
    (hJ : ∀ t ∈ A, ∀ v ∈ V, ρ t v * v⁻¹ ∈ J) : V ≤ J := by
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨t, ht, v, hv, rfl⟩
  exact hJ t ht v hv

theorem exists_compHom {k : ℕ} (I : Fin k → Subgroup W)
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    ∃ c : ↥(⨆ i, I i) →* (∀ i, ↥(I i)), ∀ (v : ↥(⨆ i, I i)) (f : ∀ i, ↥(I i)),
      ∏ i, (f i : W) = v ↔ c v = f := by
  classical
  let P : (∀ i, ↥(I i)) →* ↥(⨆ i, I i) :=
    { toFun := fun f => ⟨∏ i, (f i : W), Subgroup.prod_mem _ fun i _ =>
        Subgroup.mem_iSup_of_mem i (f i).2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun f g => by
        apply Subtype.ext
        simp [Finset.prod_mul_distrib] }
  have hPinj : Function.Injective P := by
    intro f g hfg
    have h := congrArg Subtype.val hfg
    simp only [P, MonoidHom.coe_mk, OneHom.coe_mk] at h
    funext i
    apply Subtype.ext
    have hd : ∏ j, ((f j : W) * (g j : W)⁻¹) = 1 := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, h, mul_inv_cancel]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)] at hd
    have h1 : (f i : W) * (g i : W)⁻¹ = (∏ j ∈ Finset.univ.erase i, ((f j : W) * (g j : W)⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_left hd
    have hmem1 : (f i : W) * (g i : W)⁻¹ ∈ I i := (I i).mul_mem (f i).2 ((I i).inv_mem (g i).2)
    have hmem2 : (f i : W) * (g i : W)⁻¹ ∈ ⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
      rw [h1]
      refine Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j hj => ?_))
      exact Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem (Finset.ne_of_mem_erase hj)
        ((I j).mul_mem (f j).2 ((I j).inv_mem (g j).2)))
    have h2 : (f i : W) * (g i : W)⁻¹ ∈ I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) :=
      ⟨hmem1, hmem2⟩
    rw [hind i] at h2
    exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 h2)
  have hPsurj : Function.Surjective P := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ : ∃ f : ∀ i, ↥(I i), ∏ i, (f i : W) = x := by
      refine Subgroup.iSup_induction I (C := fun x => ∃ f : ∀ i, ↥(I i), ∏ i, (f i : W) = x)
        hx ?_ ?_ ?_
      · intro i x hxi
        refine ⟨fun j => if h : j = i then ⟨x, by rw [h]; exact hxi⟩ else 1, ?_⟩
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj
          simp [hj]
        · simp
      · exact ⟨1, by simp⟩
      · rintro x y ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f * g, by simp [Finset.prod_mul_distrib]⟩
    exact ⟨f, Subtype.ext hf⟩
  let E := MulEquiv.ofBijective P ⟨hPinj, hPsurj⟩
  refine ⟨E.symm.toMonoidHom, fun v f => ?_⟩
  constructor
  · intro h
    have : P f = v := Subtype.ext h
    rw [← this]
    exact E.symm_apply_apply f
  · intro h
    rw [← h]
    exact congrArg Subtype.val (E.apply_symm_apply v)


theorem compHom_map {k : ℕ} {I : Fin k → Subgroup W} {c : ↥(⨆ i, I i) →* (∀ i, ↥(I i))}
    (hc : ∀ (v : ↥(⨆ i, I i)) (f : ∀ i, ↥(I i)), ∏ i, (f i : W) = v ↔ c v = f)
    (g : MulAut W) (hg : ∀ i, ∀ u ∈ I i, g u ∈ I i) (v : ↥(⨆ i, I i))
    (hv : g (v : W) ∈ ⨆ i, I i) (i : Fin k) :
    ((c ⟨g v, hv⟩ i : ↥(I i)) : W) = g (c v i) := by
  have h1 : c ⟨g v, hv⟩ = fun j => ⟨g (c v j), hg j _ (c v j).2⟩ := by
    rw [← hc]
    have h2 : ∏ j, ((c v j : ↥(I j)) : W) = v := (hc v (c v)).2 rfl
    simp only
    rw [← map_prod, h2]
  rw [h1]

theorem prod_compHom {k : ℕ} {I : Fin k → Subgroup W} {c : ↥(⨆ i, I i) →* (∀ i, ↥(I i))}
    (hc : ∀ (v : ↥(⨆ i, I i)) (f : ∀ i, ↥(I i)), ∏ i, (f i : W) = v ↔ c v = f)
    (v : ↥(⨆ i, I i)) : ∏ i, ((c v i : ↥(I i)) : W) = v :=
  (hc v (c v)).2 rfl

variable {n : ℕ} {ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut W}

theorem nat_coord_eq_zero {J : Subgroup W} {β : ↥J →* Multiplicative (Fin n → ZMod 2)}
    (hβ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥J) (hu : ρ h u ∈ J),
      Multiplicative.toAdd (β ⟨ρ h u, hu⟩) =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u))
    {k l : Fin n} (hkl : k ≠ l) (u : ↥J)
    (hfix : ρ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u = u) :
    Multiplicative.toAdd (β u) l = 0 := by
  have h1 := hβ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u (by rw [hfix]; exact u.2)
  have h2 : (⟨ρ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u, by rw [hfix]; exact u.2⟩ :
      ↥J) = u := Subtype.ext hfix
  rw [h2, CFSG.LinearGroups.coe_transvection] at h1
  exact (transvection_mulVec_eq_self_iff _).1 h1.symm

theorem dual_coord_eq_zero {J : Subgroup W} {β : ↥J →* Multiplicative (Fin n → ZMod 2)}
    (hβ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥J) (hu : ρ h u ∈ J),
      Multiplicative.toAdd (β ⟨ρ h u, hu⟩) =
        ((h⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          Multiplicative.toAdd (β u))
    {k l : Fin n} (hkl : k ≠ l) (u : ↥J)
    (hfix : ρ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u = u) :
    Multiplicative.toAdd (β u) k = 0 := by
  have h1 := hβ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u (by rw [hfix]; exact u.2)
  have h2 : (⟨ρ (SpecialLinearGroup.transvection hkl (1 : ZMod 2)) u, by rw [hfix]; exact u.2⟩ :
      ↥J) = u := Subtype.ext hfix
  rw [h2] at h1
  exact (transvection_dual_mulVec_eq_self_iff hkl _).1 h1.symm

theorem natSum_zero {k m : ℕ} (hm : 1 ≤ m) (h0 : 0 + m ≤ n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm 0 m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (I : Fin k → Subgroup W) (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hIinv : ∀ i (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ I i, ρ h u ∈ I i)
    (β : ∀ i, ↥(I i) →* Multiplicative (Fin n → ZMod 2)) (hβinj : ∀ i, Function.Injective (β i))
    (hβ : ∀ i (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥(I i)) (hu : ρ h u ∈ I i),
      Multiplicative.toAdd (β i ⟨ρ h u, hu⟩) =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β i u))
    {V : Subgroup W} (hVU : V ≤ ⨆ i, I i)
    (hcross : ∀ (k l : Fin n) (hc : IsCross 0 m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∃ Ψ : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2), Function.Injective Ψ ∧
      ∀ t ∈ A, ∀ (v : ↥V) (hv : ρ t v ∈ V),
        Multiplicative.toAdd (Ψ ⟨ρ t v, hv⟩) =
          diagAct (blkAt 0 m h0 (t : Matrix (Fin n) (Fin n) (ZMod 2)))
            (Multiplicative.toAdd (Ψ v)) := by
  classical
  obtain ⟨c, hc⟩ := exists_compHom I hind
  let ι : ↥V →* ↥(⨆ i, I i) := Subgroup.inclusion hVU
  let w : ↥V → Fin k → Fin n → ZMod 2 := fun v i => Multiplicative.toAdd (β i (c (ι v) i))
  have hwmul : ∀ u v, w (u * v) = w u + w v := fun u v => by
    funext i
    simp [w, map_mul]
  have hsupp : ∀ (v : ↥V) i (l : Fin n), m ≤ (l : ℕ) → w v i l = 0 := by
    intro v i l hl
    have hc0 : IsCross 0 m (⟨0, by omega⟩ : Fin n) l :=
      Or.inr ⟨Nat.zero_le _, show 0 < 0 + m by omega, show 0 + m ≤ (l : ℕ) by omega⟩
    have hfix := hcross _ _ hc0 v v.2
    have hιv : ((ι v : ↥(⨆ i, I i)) : W) = v := rfl
    have hv' : ρ (SpecialLinearGroup.transvection hc0.ne (1 : ZMod 2))
        ((ι v : ↥(⨆ i, I i)) : W) ∈ ⨆ i, I i := by
      rw [hιv, hfix]
      exact hVU v.2
    have h1 := compHom_map hc (ρ (SpecialLinearGroup.transvection hc0.ne (1 : ZMod 2)))
      (fun j u hu => hIinv j _ u hu) (ι v) hv' i
    have h2 : c ⟨ρ (SpecialLinearGroup.transvection hc0.ne (1 : ZMod 2)) (ι v), hv'⟩ =
        c (ι v) := by
      congr 1
      exact Subtype.ext hfix
    rw [h2] at h1
    exact nat_coord_eq_zero (hβ i) hc0.ne (c (ι v) i) h1.symm
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd fun i => restrictBlk 0 m h0 (w v i)
            map_one' := by
              apply Multiplicative.toAdd.injective
              funext i j
              simp [w, restrictBlk]
            map_mul' := fun u v => by
              apply Multiplicative.toAdd.injective
              funext i j
              simp only [hwmul, toAdd_ofAdd, toAdd_mul]
              rfl }, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hw0 : ∀ i, w v i = 0 := by
      intro i
      funext l
      by_cases hl : m ≤ (l : ℕ)
      · exact hsupp v i l hl
      · have := congrFun (congrFun (congrArg Multiplicative.toAdd hv) i) ⟨l, by omega⟩
        simpa [restrictBlk] using this
    have hc1 : ∀ i, c (ι v) i = 1 := fun i => by
      apply hβinj i
      rw [map_one]
      exact Multiplicative.toAdd.injective (hw0 i)
    apply Subtype.ext
    show (v : W) = 1
    have hιv : ((ι v : ↥(⨆ i, I i)) : W) = v := rfl
    rw [← hιv, ← prod_compHom hc (ι v)]
    simp [hc1]
  · intro t ht v hv
    funext i
    show restrictBlk 0 m h0 (w ⟨ρ t v, hv⟩ i) =
      blkAt 0 m h0 (t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ restrictBlk 0 m h0 (w v i)
    have hιv : ρ t ((ι v : ↥(⨆ i, I i)) : W) ∈ ⨆ i, I i := hVU hv
    have h1 := compHom_map hc (ρ t) (fun j u hu => hIinv j _ u hu) (ι v) hιv i
    have h2 : c (ι ⟨ρ t v, hv⟩) = c ⟨ρ t (ι v), hιv⟩ := rfl
    have hwt : w ⟨ρ t v, hv⟩ i = (t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w v i := by
      simp only [w]
      rw [h2]
      have h3 : c ⟨ρ t (ι v), hιv⟩ i = ⟨ρ t (c (ι v) i), hIinv i t _ (c (ι v) i).2⟩ :=
        Subtype.ext h1
      rw [h3, hβ i t (c (ι v) i)]
    rw [hwt]
    exact (mulVec_of_blockForm_blk h0 (hA t ht) fun j hj => hsupp v i j (by omega)).2

theorem natSum_pos {k a m : ℕ} (ha : 0 < a) (hm : 1 ≤ m)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (I : Fin k → Subgroup W) (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hIinv : ∀ i (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ I i, ρ h u ∈ I i)
    (β : ∀ i, ↥(I i) →* Multiplicative (Fin n → ZMod 2)) (hβinj : ∀ i, Function.Injective (β i))
    (hβ : ∀ i (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥(I i)) (hu : ρ h u ∈ I i),
      Multiplicative.toAdd (β i ⟨ρ h u, hu⟩) =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β i u))
    {V : Subgroup W} (hVU : V ≤ ⨆ i, I i)
    (hcross : ∀ (k l : Fin n) (hc : IsCross a m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∀ t ∈ A, ∀ v ∈ V, ρ t v = v := by
  classical
  obtain ⟨c, hc⟩ := exists_compHom I hind
  intro t ht v hv
  set v' : ↥(⨆ i, I i) := ⟨v, hVU hv⟩
  have hfixc : ∀ (k l : Fin n) (hc' : IsCross a m k l) i,
      ρ (SpecialLinearGroup.transvection hc'.ne (1 : ZMod 2)) (c v' i) = c v' i := by
    intro k l hc' i
    have hfix := hcross _ _ hc' v hv
    have hv'' : ρ (SpecialLinearGroup.transvection hc'.ne (1 : ZMod 2)) (v' : W) ∈ ⨆ i, I i := by
      rw [show (v' : W) = v from rfl, hfix]
      exact hVU hv
    have h1 := compHom_map hc _ (fun j u hu => hIinv j _ u hu) v' hv'' i
    have h2 : c ⟨_, hv''⟩ = c v' := by
      congr 1
      exact Subtype.ext hfix
    rw [h2] at h1
    exact h1.symm
  have hsupp : ∀ i (l : Fin n), a ≤ (l : ℕ) → Multiplicative.toAdd (β i (c v' i)) l = 0 := by
    intro i l hl
    by_cases hlB : (l : ℕ) < a + m
    · have hc' : IsCross a m (⟨0, by omega⟩ : Fin n) l := Or.inl ⟨show 0 < a from ha, hl, hlB⟩
      exact nat_coord_eq_zero (hβ i) hc'.ne _ (hfixc _ _ hc' i)
    · have hc' : IsCross a m (⟨a, by omega⟩ : Fin n) l :=
        Or.inr ⟨show a ≤ a from le_rfl, show a < a + m by omega, show a + m ≤ (l : ℕ) by omega⟩
      exact nat_coord_eq_zero (hβ i) hc'.ne _ (hfixc _ _ hc' i)
  have hfixt : ∀ i, ρ t (c v' i) = c v' i := by
    intro i
    have h1 := hβ i t (c v' i) (hIinv i t _ (c v' i).2)
    rw [mulVec_eq_self_of_blockForm (hA t ht) (hsupp i)] at h1
    have h2 := hβinj i (Multiplicative.toAdd.injective h1)
    exact congrArg Subtype.val h2
  have hprod := prod_compHom hc v'
  rw [show (v : W) = v' from rfl, ← hprod, map_prod]
  exact Finset.prod_congr rfl fun i _ => hfixt i


section NatDual

variable {U₁ U₂ : Subgroup W}

theorem fixed_of_mul_fixed (hU : U₁ ⊓ U₂ = ⊥) {g : MulAut W} (hg₁ : ∀ u ∈ U₁, g u ∈ U₁)
    (hg₂ : ∀ u ∈ U₂, g u ∈ U₂) {y z : W} (hy : y ∈ U₁) (hz : z ∈ U₂) (hfix : g (y * z) = y * z) :
    g y = y ∧ g z = z := by
  rw [map_mul] at hfix
  have h1 : (g y)⁻¹ * y ∈ U₁ := U₁.mul_mem (U₁.inv_mem (hg₁ y hy)) hy
  have h2 : (g y)⁻¹ * y = g z * z⁻¹ := by
    calc (g y)⁻¹ * y = (g y)⁻¹ * (y * z) * z⁻¹ := by group
      _ = (g y)⁻¹ * (g y * g z) * z⁻¹ := by rw [hfix]
      _ = g z * z⁻¹ := by group
  have h3 : (g y)⁻¹ * y ∈ U₁ ⊓ U₂ := ⟨h1, h2 ▸ U₂.mul_mem (hg₂ z hz) (U₂.inv_mem hz)⟩
  rw [hU, Subgroup.mem_bot] at h3
  have h4 : g y = y := (inv_mul_eq_one.1 h3)
  refine ⟨h4, ?_⟩
  rw [h4] at hfix
  exact mul_left_cancel hfix

variable {ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut W}
  {β₁ : ↥U₁ →* Multiplicative (Fin n → ZMod 2)} {β₂ : ↥U₂ →* Multiplicative (Fin n → ZMod 2)}

theorem dual_fixed_of_lt {a m : ℕ} (hm : 1 ≤ m) (hamn : a + m < n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hinv₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₂, ρ h u ∈ U₂)
    (hβ₂inj : Function.Injective β₂)
    (hβ₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₂) (hu : ρ h u ∈ U₂),
      Multiplicative.toAdd (β₂ ⟨ρ h u, hu⟩) =
        ((h⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          Multiplicative.toAdd (β₂ u))
    (z : ↥U₂) (hzfix : ∀ (k l : Fin n) (hc : IsCross a m k l),
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) z = z) :
    ∀ t ∈ A, ρ t z = z := by
  intro t ht
  have hsupp : ∀ j : Fin n, (j : ℕ) < a + m → Multiplicative.toAdd (β₂ z) j = 0 := by
    intro j hj
    by_cases hja : (j : ℕ) < a
    · have hc : IsCross a m j (⟨a, by omega⟩ : Fin n) :=
        Or.inl ⟨hja, show a ≤ a from le_rfl, show a < a + m by omega⟩
      exact dual_coord_eq_zero hβ₂ hc.ne z (hzfix _ _ hc)
    · have hc : IsCross a m j (⟨a + m, hamn⟩ : Fin n) :=
        Or.inr ⟨by omega, hj, show a + m ≤ a + m from le_rfl⟩
      exact dual_coord_eq_zero hβ₂ hc.ne z (hzfix _ _ hc)
  have h1 := hβ₂ t z (hinv₂ t _ z.2)
  have hs : BlockForm a m ((t⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) := hA _ (A.inv_mem ht)
  rw [transpose_mulVec_eq_self_of_blockForm hs hsupp] at h1
  exact congrArg Subtype.val (hβ₂inj (Multiplicative.toAdd.injective h1))

theorem nat_fixed_of_pos {a m : ℕ} (ha : 0 < a) (hm : 1 ≤ m) (hamn : a + m ≤ n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hinv₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₁, ρ h u ∈ U₁)
    (hβ₁inj : Function.Injective β₁)
    (hβ₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₁) (hu : ρ h u ∈ U₁),
      Multiplicative.toAdd (β₁ ⟨ρ h u, hu⟩) =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β₁ u))
    (y : ↥U₁) (hyfix : ∀ (k l : Fin n) (hc : IsCross a m k l),
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) y = y) :
    ∀ t ∈ A, ρ t y = y := by
  intro t ht
  have hsupp : ∀ l : Fin n, a ≤ (l : ℕ) → Multiplicative.toAdd (β₁ y) l = 0 := by
    intro l hl
    by_cases hlB : (l : ℕ) < a + m
    · have hc : IsCross a m (⟨0, by omega⟩ : Fin n) l := Or.inl ⟨show 0 < a from ha, hl, hlB⟩
      exact nat_coord_eq_zero hβ₁ hc.ne y (hyfix _ _ hc)
    · have hc : IsCross a m (⟨a, by omega⟩ : Fin n) l :=
        Or.inr ⟨show a ≤ a from le_rfl, show a < a + m by omega, show a + m ≤ (l : ℕ) by omega⟩
      exact nat_coord_eq_zero hβ₁ hc.ne y (hyfix _ _ hc)
  have h1 := hβ₁ t y (hinv₁ t _ y.2)
  rw [mulVec_eq_self_of_blockForm (hA t ht) hsupp] at h1
  exact congrArg Subtype.val (hβ₁inj (Multiplicative.toAdd.injective h1))

theorem components_fixed (hU : U₁ ⊓ U₂ = ⊥)
    (hinv₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₁, ρ h u ∈ U₁)
    (hinv₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₂, ρ h u ∈ U₂)
    {a m : ℕ} {V : Subgroup W}
    (hcross : ∀ (k l : Fin n) (hc : IsCross a m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v)
    {v : W} (hv : v ∈ V) {y z : W} (hy : y ∈ U₁) (hz : z ∈ U₂) (hyz : y * z = v) :
    (∀ (k l : Fin n) (hc : IsCross a m k l),
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) y = y) ∧
    (∀ (k l : Fin n) (hc : IsCross a m k l),
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) z = z) := by
  have key : ∀ (k l : Fin n) (hc : IsCross a m k l),
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) (y * z) = y * z := by
    intro k l hc
    rw [hyz]
    exact hcross k l hc v hv
  exact ⟨fun k l hc => (fixed_of_mul_fixed hU (hinv₁ _) (hinv₂ _) hy hz (key k l hc)).1,
    fun k l hc => (fixed_of_mul_fixed hU (hinv₁ _) (hinv₂ _) hy hz (key k l hc)).2⟩

theorem natDual_zero_le {m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm 0 m (t : Matrix (Fin n) (Fin n) (ZMod 2))) (hU : U₁ ⊓ U₂ = ⊥)
    (hinv₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₁, ρ h u ∈ U₁)
    (hinv₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₂, ρ h u ∈ U₂)
    (hβ₂inj : Function.Injective β₂)
    (hβ₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₂) (hu : ρ h u ∈ U₂),
      Multiplicative.toAdd (β₂ ⟨ρ h u, hu⟩) =
        ((h⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          Multiplicative.toAdd (β₂ u))
    {V : Subgroup W} (hVU : V ≤ U₁ ⊔ U₂)
    (hgen : V ≤ Subgroup.closure {w | ∃ t ∈ A, ∃ v ∈ V, ρ t v * v⁻¹ = w})
    (hcross : ∀ (k l : Fin n) (hc : IsCross 0 m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) : V ≤ U₁ := by
  refine le_of_forall_comm_mem hgen fun t ht v hv => ?_
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 (hVU hv)
  obtain ⟨-, hzc⟩ := components_fixed hU hinv₁ hinv₂ hcross hv hy hz hyz
  have hzt := dual_fixed_of_lt hm (by omega : 0 + m < n) hA hinv₂ hβ₂inj hβ₂ ⟨z, hz⟩ hzc t ht
  have : ρ t v * v⁻¹ = ρ t y * y⁻¹ := by
    rw [← hyz, map_mul]
    change ρ t y * ρ t (⟨z, hz⟩ : ↥U₂) * (y * z)⁻¹ = _
    rw [hzt]
    group
  rw [this]
  exact U₁.mul_mem (hinv₁ t y hy) (U₁.inv_mem hy)

theorem natDual_last_le {a m : ℕ} (ha : 0 < a) (hm : 1 ≤ m) (hamn : a + m = n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2))) (hU : U₁ ⊓ U₂ = ⊥)
    (hinv₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₁, ρ h u ∈ U₁)
    (hinv₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₂, ρ h u ∈ U₂)
    (hβ₁inj : Function.Injective β₁)
    (hβ₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₁) (hu : ρ h u ∈ U₁),
      Multiplicative.toAdd (β₁ ⟨ρ h u, hu⟩) =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β₁ u))
    {V : Subgroup W} (hVU : V ≤ U₁ ⊔ U₂)
    (hgen : V ≤ Subgroup.closure {w | ∃ t ∈ A, ∃ v ∈ V, ρ t v * v⁻¹ = w})
    (hcross : ∀ (k l : Fin n) (hc : IsCross a m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) : V ≤ U₂ := by
  refine le_of_forall_comm_mem hgen fun t ht v hv => ?_
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 (hVU hv)
  obtain ⟨hyc, -⟩ := components_fixed hU hinv₁ hinv₂ hcross hv hy hz hyz
  have hyt := nat_fixed_of_pos ha hm hamn.le hA hinv₁ hβ₁inj hβ₁ ⟨y, hy⟩ hyc t ht
  have : ρ t v * v⁻¹ = ρ t z * z⁻¹ := by
    rw [← hyz, map_mul]
    change ρ t (⟨y, hy⟩ : ↥U₁) * ρ t z * (y * z)⁻¹ = _
    rw [hyt]
    show y * ρ t z * (y * z)⁻¹ = ρ t z * z⁻¹
    rw [_root_.mul_inv_rev, mul_comm z⁻¹ y⁻¹, mul_comm y (ρ t z)]
    group
  rw [this]
  exact U₂.mul_mem (hinv₂ t z hz) (U₂.inv_mem hz)

theorem natDual_mid {a m : ℕ} (ha : 0 < a) (hm : 1 ≤ m) (hamn : a + m < n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2))) (hU : U₁ ⊓ U₂ = ⊥)
    (hinv₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₁, ρ h u ∈ U₁)
    (hinv₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ u ∈ U₂, ρ h u ∈ U₂)
    (hβ₁inj : Function.Injective β₁)
    (hβ₁ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₁) (hu : ρ h u ∈ U₁),
      Multiplicative.toAdd (β₁ ⟨ρ h u, hu⟩) =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β₁ u))
    (hβ₂inj : Function.Injective β₂)
    (hβ₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₂) (hu : ρ h u ∈ U₂),
      Multiplicative.toAdd (β₂ ⟨ρ h u, hu⟩) =
        ((h⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          Multiplicative.toAdd (β₂ u))
    {V : Subgroup W} (hVU : V ≤ U₁ ⊔ U₂)
    (hcross : ∀ (k l : Fin n) (hc : IsCross a m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∀ t ∈ A, ∀ v ∈ V, ρ t v = v := by
  intro t ht v hv
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 (hVU hv)
  obtain ⟨hyc, hzc⟩ := components_fixed hU hinv₁ hinv₂ hcross hv hy hz hyz
  have hyt := nat_fixed_of_pos ha hm hamn.le hA hinv₁ hβ₁inj hβ₁ ⟨y, hy⟩ hyc t ht
  have hzt := dual_fixed_of_lt hm hamn hA hinv₂ hβ₂inj hβ₂ ⟨z, hz⟩ hzc t ht
  rw [← hyz, map_mul]
  change ρ t (⟨y, hy⟩ : ↥U₁) * ρ t (⟨z, hz⟩ : ↥U₂) = _
  rw [hyt, hzt]

theorem dualSingle_last {a m : ℕ} (hm : 1 ≤ m) (h : a + m ≤ n) (hamn : a + m = n)
    {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hA : ∀ t ∈ A, BlockForm a m (t : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hβ₂inj : Function.Injective β₂)
    (hβ₂ : ∀ (h : SpecialLinearGroup (Fin n) (ZMod 2)) (u : ↥U₂) (hu : ρ h u ∈ U₂),
      Multiplicative.toAdd (β₂ ⟨ρ h u, hu⟩) =
        ((h⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          Multiplicative.toAdd (β₂ u))
    {V : Subgroup W} (hVU : V ≤ U₂)
    (hcross : ∀ (k l : Fin n) (hc : IsCross a m k l), ∀ v ∈ V,
      ρ (SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) v = v) :
    ∃ Ψ : ↥V →* Multiplicative (Fin 1 → Fin m → ZMod 2), Function.Injective Ψ ∧
      ∀ t ∈ A, ∀ (v : ↥V) (hv : ρ t v ∈ V),
        Multiplicative.toAdd (Ψ ⟨ρ t v, hv⟩) =
          diagAct (blkAt a m h ((t⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ (Multiplicative.toAdd (Ψ v)) := by
  let ι : ↥V →* ↥U₂ := Subgroup.inclusion hVU
  let w : ↥V → Fin n → ZMod 2 := fun v => Multiplicative.toAdd (β₂ (ι v))
  have hsupp : ∀ (v : ↥V) (j : Fin n), ((j : ℕ) < a ∨ a + m ≤ (j : ℕ)) → w v j = 0 := by
    intro v j hj
    rcases hj with hj | hj
    · have hc : IsCross a m j (⟨a, by omega⟩ : Fin n) :=
        Or.inl ⟨hj, show a ≤ a from le_rfl, show a < a + m by omega⟩
      exact dual_coord_eq_zero hβ₂ hc.ne (ι v) (hcross _ _ hc v v.2)
    · exact absurd j.isLt (by omega)
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd fun _ => restrictBlk a m h (w v)
            map_one' := by
              apply Multiplicative.toAdd.injective
              funext i j
              simp [w, restrictBlk]
            map_mul' := fun u v => by
              apply Multiplicative.toAdd.injective
              funext i j
              simp [w, restrictBlk, map_mul] }, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hw0 : w v = 0 := by
      funext j
      by_cases hj : (j : ℕ) < a ∨ a + m ≤ (j : ℕ)
      · exact hsupp v j hj
      · have := congrFun (congrFun (congrArg Multiplicative.toAdd hv) 0) ⟨(j : ℕ) - a, by omega⟩
        have hj' : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
        simpa [restrictBlk, hj'] using this
    have h1 : β₂ (ι v) = 1 := Multiplicative.toAdd.injective hw0
    have h2 : ι v = 1 := hβ₂inj (by rw [h1, map_one])
    apply Subtype.ext
    simpa [ι] using congrArg Subtype.val h2
  · intro t ht v hv
    funext i
    show restrictBlk a m h (w ⟨ρ t v, hv⟩) = (blkAt a m h ((t⁻¹ : SpecialLinearGroup (Fin n)
      (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *ᵥ restrictBlk a m h (w v)
    have hwt : w ⟨ρ t v, hv⟩ = ((t⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w v :=
      hβ₂ t (ι v) (hVU hv)
    rw [hwt]
    exact (transpose_mulVec_of_blockForm_blk h (hA _ (A.inv_mem ht)) (hsupp v)).2

end NatDual

end CFSG.Quasithin.C48Pf.FMod
