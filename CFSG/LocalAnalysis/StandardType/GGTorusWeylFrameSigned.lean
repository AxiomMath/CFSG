module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

public section

namespace CFSG.StandardType

section SignedCoordinateAction

variable {n p : ℕ}

theorem spSignedGroup_map_mul {u : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ SpJoin.spSignedGroup n p) :
    ∀ f g : Fin n → Multiplicative (ZMod p), u (f * g) = u f * u g := by
  refine Subgroup.closure_induction
    (p := fun u _ => ∀ f g : Fin n → Multiplicative (ZMod p), u (f * g) = u f * u g)
    ?_ ?_ ?_ ?_ hu
  · rintro u ⟨i, rfl⟩
    by_cases h : i.val + 1 < n
    · rw [SpJoin.spReflPerm_of_lt n p i h]
      intro f g
      rfl
    · rw [SpJoin.spReflPerm_of_not_lt n p i h]
      intro f g
      funext t
      rw [SpJoin.coordInv_apply, SpJoin.coordInv_apply, SpJoin.coordInv_apply]
      by_cases ht : t = i
      · subst ht
        rw [Function.update_self]
        change (f t * g t)⁻¹ =
          Function.update f t (f t)⁻¹ t * Function.update g t (g t)⁻¹ t
        rw [Function.update_self, Function.update_self]
        apply Multiplicative.toAdd.injective
        simp [toAdd_inv, toAdd_mul, add_comm]
      · rw [Function.update_of_ne ht]
        change f t * g t =
          Function.update f i (f i)⁻¹ t * Function.update g i (g i)⁻¹ t
        rw [Function.update_of_ne ht, Function.update_of_ne ht]
  · intro f g
    rfl
  · intro x y _ _ ihx ihy f g
    calc (x * y) (f * g) = x (y (f * g)) := rfl
      _ = x (y f * y g) := by rw [ihy f g]
      _ = x (y f) * x (y g) := ihx (y f) (y g)
      _ = (x * y) f * (x * y) g := rfl
  · intro x _ ih f g
    have h1 : x (x⁻¹ (f * g)) = x (x⁻¹ f * x⁻¹ g) := by
      rw [ih (x⁻¹ f) (x⁻¹ g)]
      simp
    exact Equiv.injective x h1

@[expose] noncomputable def spSignedPermMulAut (u : ↥(SpJoin.spSignedGroup n p)) :
    MulAut (Fin n → Multiplicative (ZMod p)) where
  toFun := u
  invFun := (u : Equiv.Perm (Fin n → Multiplicative (ZMod p))).symm
  left_inv f := (u : Equiv.Perm (Fin n → Multiplicative (ZMod p))).left_inv f
  right_inv f := (u : Equiv.Perm (Fin n → Multiplicative (ZMod p))).right_inv f
  map_mul' := spSignedGroup_map_mul u.2

@[expose] noncomputable def spSignedPermHom :
    ↥(SpJoin.spSignedGroup n p) →* MulAut (Fin n → Multiplicative (ZMod p)) where
  toFun := spSignedPermMulAut
  map_one' := by
    apply MulEquiv.ext
    intro f
    rfl
  map_mul' := by
    intro u v
    apply MulEquiv.ext
    intro f
    rfl

@[simp] theorem spSignedPermHom_apply (u : ↥(SpJoin.spSignedGroup n p))
    (f : Fin n → Multiplicative (ZMod p)) :
    spSignedPermHom u f = (u : Equiv.Perm (Fin n → Multiplicative (ZMod p))) f := rfl

theorem spSignedPermHom_injective : Function.Injective (spSignedPermHom (n := n) (p := p)) := by
  intro u v h
  apply Subtype.ext
  apply Equiv.ext
  intro f
  simpa using congrArg (fun w : MulAut (Fin n → Multiplicative (ZMod p)) => w f) h

end SignedCoordinateAction

theorem exists_markedWeylB_ggAutomizer {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hk : 2 ≤ k)
    {G : Type} [Group G] (E : Subgroup G)
    (ι : (Fin k → Multiplicative (ZMod p)) →* G)
    (hι : Function.Injective ι) (hrange : ι.range = E)
    (n : Fin k → G)
    (hn : ∀ (i : Fin k) (f : Fin k → Multiplicative (ZMod p)),
      n i * ι f * (n i)⁻¹ = ι (SpJoin.spReflPerm k p i f))
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set G), ∃ σ ∈ SpJoin.spSignedGroup k p,
      ∀ f, g * ι f * g⁻¹ = ι (σ f)) :
    ∃ hnN : ∀ i : Fin k, n i ∈ Subgroup.normalizer (E : Set G),
      ggAutomizer (⊤ : Subgroup G) E =
          Subgroup.closure (Set.range fun i => ggConjAut E (hnN i)) ∧
        ∃ e : (CoxeterMatrix.B k).Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) E),
          ∀ i : Fin k, (e ((CoxeterMatrix.B k).simple i) : MulAut ↥E) = ggConjAut E (hnN i) := by
  classical
  let V := Fin k → Multiplicative (ZMod p)
  let eT : V ≃* ↥E :=
    (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  have heT_apply : ∀ f : V, ((eT f : ↥E) : G) = ι f := by
    intro f
    change (((MulEquiv.subgroupCongr hrange) (MonoidHom.ofInjective hι f) : ↥E) : G) = _
    rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  obtain ⟨eB, heB⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 hk
  let ρc : ↥(SpJoin.spSignedGroup k p) →* MulAut ↥E :=
    (MulAut.congr eT).toMonoidHom.comp (spSignedPermHom (n := k) (p := p))
  let ρ : (CoxeterMatrix.B k).Group →* MulAut ↥E :=
    ρc.comp eB.toMonoidHom
  have hcongr_apply : ∀ (φ : MulAut V) (b : ↥E),
      ((MulAut.congr eT φ) b : ↥E) = eT (φ (eT.symm b)) := fun φ b => rfl
  have hρc_apply : ∀ (u : ↥(SpJoin.spSignedGroup k p)) (f : V),
      ((ρc u (eT f) : ↥E) : G) = ι ((u : Equiv.Perm V) f) := by
    intro u f
    change ((MulAut.congr eT (spSignedPermHom (n := k) (p := p) u) (eT f) : ↥E) : G) = _
    rw [hcongr_apply, MulEquiv.symm_apply_apply, spSignedPermHom_apply, heT_apply]
  have hnN : ∀ i : Fin k, n i ∈ Subgroup.normalizer (E : Set G) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp (hrange ▸ hx)
      exact hrange ▸ MonoidHom.mem_range.mpr ⟨SpJoin.spReflPerm k p i f, (hn i f).symm⟩
    · intro hx
      have hx' : n i * x * (n i)⁻¹ ∈ ι.range := hrange ▸ hx
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hx'
      obtain ⟨f, hf⟩ := (SpJoin.spReflPerm k p i).surjective g
      have hιf : ι f = x := by
        have h : n i * ι f * (n i)⁻¹ = n i * x * (n i)⁻¹ := by
          rw [hn i f, hf, hg]
        calc ι f = (n i)⁻¹ * (n i * ι f * (n i)⁻¹) * (n i) := by group
          _ = (n i)⁻¹ * (n i * x * (n i)⁻¹) * (n i) := by rw [h]
          _ = x := by group
      exact hrange ▸ MonoidHom.mem_range.mpr ⟨f, hιf⟩
  have hρ_simple : ∀ i : Fin k, ρ ((CoxeterMatrix.B k).simple i) = ggConjAut E (hnN i) := by
    intro i
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    set f : V := eT.symm b with hf
    have hb : eT f = b := by rw [hf, MulEquiv.apply_symm_apply]
    rw [← hb]
    change ((ρc (eB ((CoxeterMatrix.B k).simple i)) (eT f) : ↥E) : G) =
      ((ggConjAut E (hnN i) (eT f) : ↥E) : G)
    rw [hρc_apply, ggConjAut_apply, heT_apply, heB i]
    exact (hn i f).symm
  have hρ_inj : Function.Injective ρ := by
    have hρc_inj : Function.Injective ρc :=
      (MulAut.congr eT).injective.comp (spSignedPermHom_injective (n := k) (p := p))
    intro v w h
    exact eB.injective (hρc_inj h)
  have hgens : ρ.range =
      Subgroup.closure (Set.range fun i => ρ ((CoxeterMatrix.B k).simple i)) := by
    rw [MonoidHom.range_eq_map,
      ← (CoxeterMatrix.B k).toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    ext x
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [CoxeterMatrix.toCoxeterSystem_simple]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(CoxeterMatrix.B k).toCoxeterSystem.simple i, ⟨i, rfl⟩, by
        rw [CoxeterMatrix.toCoxeterSystem_simple]⟩
  have hρrange_le : ρ.range ≤ ggAutomizer (⊤ : Subgroup G) E := by
    rw [hgens]
    refine (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr ?_)
    intro i
    rw [hρ_simple i]
    exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top (n i)) (hnN i)
  have hAuto_le : ggAutomizer (⊤ : Subgroup G) E ≤ ρ.range := by
    rw [ggAutomizer_eq]
    intro φ hφ
    obtain ⟨g, -, hg, hφg⟩ := hφ
    obtain ⟨σ, hσmem, hσ⟩ := hN g hg
    obtain ⟨v, hv⟩ := eB.surjective ⟨σ, hσmem⟩
    have hρcσ : ρc ⟨σ, hσmem⟩ = φ := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      set f : V := eT.symm b with hf
      have hb : eT f = b := by rw [hf, MulEquiv.apply_symm_apply]
      rw [← hb, hρc_apply, hφg, heT_apply, hσ]
    refine ⟨v, ?_⟩
    change ρc (eB v) = φ
    rw [hv]
    exact hρcσ
  have hρrange : ρ.range = ggAutomizer (⊤ : Subgroup G) E :=
    le_antisymm hρrange_le hAuto_le
  have hclosure : ggAutomizer (⊤ : Subgroup G) E =
      Subgroup.closure (Set.range fun i => ggConjAut E (hnN i)) := by
    rw [← hρrange, hgens]
    rw [show (fun i => ρ ((CoxeterMatrix.B k).simple i)) =
      (fun i => ggConjAut E (hnN i)) from funext hρ_simple]
  refine ⟨hnN, hclosure, ?_⟩
  refine ⟨(MonoidHom.ofInjective hρ_inj).trans (MulEquiv.subgroupCongr hρrange), ?_⟩
  intro i
  simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  exact hρ_simple i

@[expose] def coordFlip (k p : ℕ) (T : Finset (Fin k)) :
    Equiv.Perm (Fin k → Multiplicative (ZMod p)) where
  toFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  invFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  left_inv v := by
    funext t
    by_cases h : t ∈ T <;> simp [h]
  right_inv v := by
    funext t
    by_cases h : t ∈ T <;> simp [h]

@[simp] theorem coordFlip_apply (k p : ℕ) (T : Finset (Fin k))
    (v : Fin k → Multiplicative (ZMod p)) (t : Fin k) :
    coordFlip k p T v t = if t ∈ T then (v t)⁻¹ else v t := rfl

theorem coordFlip_mem_spSignedGroup {k p : ℕ} (T : Finset (Fin k)) :
    coordFlip k p T ∈ SpJoin.spSignedGroup k p := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      have h : coordFlip k p ∅ = 1 := by
        ext v t
        simp [coordFlip_apply]
      rw [h]
      exact Subgroup.one_mem _
  | insert a T ha ih =>
      have hstep : coordFlip k p (insert a T) =
          SpJoin.coordInv k p a * coordFlip k p T := by
        ext v t
        rw [coordFlip_apply, Equiv.Perm.mul_apply, SpJoin.coordInv_apply]
        by_cases ht : t = a
        · subst ht
          simp [ha]
        · rw [Function.update_apply, if_neg ht, coordFlip_apply]
          simp [Finset.mem_insert, ht]
      rw [hstep]
      exact Subgroup.mul_mem _ (SpJoin.coordInv_mem_spSignedGroup a) ih

theorem signedPerm_mem_spSignedGroup {p k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ σ ∈ SpJoin.spSignedGroup k p, ∀ f : Fin k → Multiplicative (ZMod p),
      σ f = fun i => f (π.symm i) ^ ε (π.symm i) := by
  classical
  let T : Finset (Fin k) := Finset.univ.filter fun i => ε i = -1
  have hmem : ∀ i : Fin k, i ∈ T ↔ ε i = -1 := by
    intro i
    simp [T]
  refine ⟨SpJoin.coordPerm k p π * coordFlip k p T, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (SpJoin.coordPerm_mem_spSignedGroup π)
      (coordFlip_mem_spSignedGroup T)
  · intro f
    funext i
    rw [Equiv.Perm.mul_apply, SpJoin.coordPerm_apply, coordFlip_apply]
    by_cases h : ε (π.symm i) = -1
    · rw [if_pos ((hmem (π.symm i)).mpr h), h, zpow_neg_one]
    · have h1 : ε (π.symm i) = 1 := (hε _).resolve_right h
      rw [if_neg (fun hh => h ((hmem (π.symm i)).mp hh)), h1, zpow_one]


theorem mem_spSignedGroup_of_isSignedPerm {p k : ℕ}
    {a : MulAut (Fin k → Multiplicative (ZMod p))} (ha : SpCoord.IsSignedPerm a) :
    a.toEquiv ∈ SpJoin.spSignedGroup k p := by
  have hr : a ∈ (spSignedPermHom (n := k) (p := p)).range := by
    refine SpCoord.mem_of_isSignedPerm (fun i => ?_) (fun i j _ => ?_) ha
    · refine MonoidHom.mem_range.mpr ⟨⟨SpJoin.coordInv k p i,
        SpJoin.coordInv_mem_spSignedGroup i⟩, ?_⟩
      apply MulEquiv.ext
      intro f
      rfl
    · refine MonoidHom.mem_range.mpr ⟨⟨SpJoin.coordPerm k p (Equiv.swap i j),
        SpJoin.coordPerm_mem_spSignedGroup (Equiv.swap i j)⟩, ?_⟩
      apply MulEquiv.ext
      intro f
      rfl
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hr
  rw [← hσ]
  exact σ.2

theorem exists_surjective_fixedHom_spReflPerm {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin k) :
    ∃ χ : (Fin k → Multiplicative (ZMod p)) →* Multiplicative (ZMod p),
      Function.Surjective χ ∧
        ∀ u, SpJoin.spReflPerm k p i u = u ↔ χ u = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let V := Fin k → Multiplicative (ZMod p)
  let M := Multiplicative (ZMod p)
  by_cases hi : i.val + 1 < k
  · let j : Fin k := ⟨i.val + 1, hi⟩
    have hji : j ≠ i := Fin.ne_of_val_ne (by dsimp only [j]; omega)
    let χ : V →* M :=
      Pi.evalMonoidHom (fun _ : Fin k => M) i *
        (Pi.evalMonoidHom (fun _ : Fin k => M) j)⁻¹
    have hχ (u : V) : χ u = u i * (u j)⁻¹ := rfl
    refine ⟨χ, ?_, ?_⟩
    · intro z
      refine ⟨Pi.mulSingle i z, ?_⟩
      rw [hχ, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hji]
      simp
    · intro u
      rw [SpJoin.spReflPerm_of_lt k p i hi, hχ]
      constructor
      · intro hu
        have h := congrArg (fun v : V => v i) hu
        rw [SpJoin.coordPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h
        change u j = u i at h
        rw [h, mul_inv_cancel]
      · intro h
        have hij : u i = u j := mul_inv_eq_one.mp h
        funext a
        rw [SpJoin.coordPerm_apply, Equiv.symm_swap]
        by_cases hai : a = i
        · subst a
          rw [Equiv.swap_apply_left]
          exact hij.symm
        · by_cases haj : a = j
          · subst a
            rw [Equiv.swap_apply_right]
            exact hij
          · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
  · let χ : V →* M := Pi.evalMonoidHom (fun _ : Fin k => M) i
    refine ⟨χ, ?_, ?_⟩
    · intro z
      refine ⟨Pi.mulSingle i z, ?_⟩
      change (Pi.mulSingle i z : V) i = z
      rw [Pi.mulSingle_eq_same]
    · intro u
      rw [SpJoin.spReflPerm_of_not_lt k p i hi]
      change SpJoin.coordInv k p i u = u ↔ u i = 1
      constructor
      · intro hu
        have h := congrArg (fun v : V => v i) hu
        rw [SpJoin.coordInv_apply, Function.update_self] at h
        have hsq : (u i) ^ 2 = 1 := by
          simpa only [pow_two, h] using inv_mul_cancel (u i)
        have hpw : (u i) ^ p = 1 := by
          apply Multiplicative.toAdd.injective
          change p • Multiplicative.toAdd (u i) = 0
          simp [nsmul_eq_mul]
        have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
        exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hsq, hpw⟩
      · intro h
        funext a
        rw [SpJoin.coordInv_apply]
        by_cases hai : a = i
        · subst a
          simp [h]
        · rw [Function.update_of_ne hai]


end CFSG.StandardType

end
