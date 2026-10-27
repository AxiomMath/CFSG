module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.StandardType.TypeBDatum
open Multiplicative

namespace TypeDDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def tbD_iota (m p : ℕ) :
    Additive (Fin m → Multiplicative (ZMod p)) ≃+ (Fin m → ZMod p) where
  toFun f i := toAdd (f i)
  invFun v i := ofAdd (v i)
  left_inv f := by funext i; rfl
  right_inv v := by funext i; rfl
  map_add' f g := by
    funext i
    change toAdd ((f + g).toMul i) = toAdd (f.toMul i) + toAdd (g.toMul i)
    rw [toMul_add, Pi.mul_apply, toAdd_mul]

private lemma tbD_fin_ne_succ {k : ℕ} {i : Fin k} (hi : i.val + 1 < k) :
    i ≠ ⟨i.val + 1, hi⟩ := by
  intro hh
  have h2 : i.val = i.val + 1 := by
    have := congrArg Fin.val hh
    simpa using this
  omega

private lemma tbD_toAdd_permAut {p k : ℕ} (σ : Equiv.Perm (Fin k)) (v : Fin k → ZMod p)
    (j : Fin k) :
    toAdd ((permAut σ (fun l => ofAdd (v l))) j) = v (σ⁻¹ j) := by
  rw [permAut_apply, Function.comp_apply]
  exact toAdd_ofAdd (v (σ⁻¹ j))

private noncomputable def tbD_h (m p : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (i : Fin m) :
    Fin m → ZMod p :=
  ggDSimple p m i

private noncomputable def tbD_alpha (m p : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    Module.Dual (ZMod p) (Fin m → ZMod p) :=
  ggQ2_DW_dotLin p m (ggDSimple p m i)

private lemma tbD_toAdd_sgnAut_pair {p k : ℕ} {a b : Fin k} (hab : a ≠ b)
    (v : Fin k → ZMod p) (j : Fin k) :
    toAdd (((sgnAut a * sgnAut b : MulAut (Fin k → Multiplicative (ZMod p)))
        (fun l => ofAdd (v l))) j) =
      if j = b then -v b else if j = a then -v a else v j := by
  by_cases hja : j = a
  · subst hja
    rw [MulAut.mul_apply, sgnAut_apply, sgnAut_apply, Function.update_self,
      Function.update_of_ne hab, toAdd_inv, toAdd_ofAdd, if_neg hab, if_pos rfl]
  · by_cases hjb : j = b
    · subst hjb
      rw [MulAut.mul_apply, sgnAut_apply, sgnAut_apply, Function.update_of_ne (Ne.symm hab),
        Function.update_self, toAdd_inv, toAdd_ofAdd, if_pos rfl]
    · rw [MulAut.mul_apply, sgnAut_apply, sgnAut_apply, Function.update_of_ne hja,
        Function.update_of_ne hjb, toAdd_ofAdd, if_neg hjb, if_neg hja]

private lemma tbD_toAdd_sgnAut_pair_swap {p k : ℕ} {a b : Fin k} (hab : a ≠ b)
    (v : Fin k → ZMod p) (j : Fin k) :
    toAdd (((sgnAut a * sgnAut b : MulAut (Fin k → Multiplicative (ZMod p)))
        (fun l => ofAdd (v l))) (Equiv.swap a b j)) =
      if j = a then -v b else if j = b then -v a else v j := by
  rw [tbD_toAdd_sgnAut_pair (a := a) (b := b) hab v (Equiv.swap a b j)]
  by_cases hja : j = a
  · rw [hja, Equiv.swap_apply_left]; simp [hab, Ne.symm hab]
  · by_cases hjb : j = b
    · rw [hjb, Equiv.swap_apply_right]; simp [hab, Ne.symm hab]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]; simp [hja, hjb]

private theorem tbD_permAut_swap_mul_sgn_pair {p k : ℕ} {a b : Fin k} (hab : a ≠ b) :
    (permAut (p := p) (Equiv.swap a b) * (sgnAut a * sgnAut b) :
      MulAut (Fin k → Multiplicative (ZMod p))) =
    sgnAut a * sgnAut b * permAut (p := p) (Equiv.swap a b) := by
  let P : MulAut (Fin k → Multiplicative (ZMod p)) := permAut (p := p) (Equiv.swap a b)
  let Sa : MulAut (Fin k → Multiplicative (ZMod p)) := sgnAut (p := p) a
  let Sb : MulAut (Fin k → Multiplicative (ZMod p)) := sgnAut (p := p) b
  change P * (Sa * Sb) = Sa * Sb * P
  have hsa : Sa * Sa = 1 := OrthExcEven.sgnAut_mul_self a
  have hsb : Sb * Sb = 1 := OrthExcEven.sgnAut_mul_self b
  have hcomm : Sa * Sb = Sb * Sa := SpCoord.sgnAut_mul_comm a b
  have hPSa : P * Sa = Sb * P := by
    have h := OrthExcEven.sgnTransp_eq (p := p) hab
    change Sa * Sb * P = Sa * P * Sa⁻¹ at h
    have h' : Sb * P = P * Sa := by
      calc Sb * P = (Sa * Sa) * (Sb * P) := by rw [hsa]; group
        _ = Sa * (Sa * Sb * P) := by group
        _ = Sa * (Sa * P * Sa⁻¹) := by rw [h]
        _ = P * Sa := by
          rw [inv_eq_of_mul_eq_one_right hsa, ← mul_assoc, ← mul_assoc, hsa, one_mul]
    exact h'.symm
  have hPSb : P * Sb = Sa * P := by
    have h := OrthExcEven.sgnTransp_eq (p := p) (a := b) (b := a) (Ne.symm hab)
    rw [← Equiv.swap_comm] at h
    change Sb * Sa * P = Sb * P * Sb⁻¹ at h
    have h' : Sa * P = P * Sb := by
      calc Sa * P = (Sb * Sb) * (Sa * P) := by rw [hsb]; group
        _ = Sb * (Sb * Sa * P) := by group
        _ = Sb * (Sb * P * Sb⁻¹) := by rw [h]
        _ = P * Sb := by
          rw [inv_eq_of_mul_eq_one_right hsb]
          calc Sb * (Sb * P) * Sb = (Sb * Sb) * (P * Sb) := by group
            _ = P * Sb := by rw [hsb, one_mul]
    exact h'.symm
  calc P * (Sa * Sb) = (P * Sa) * Sb := by group
    _ = (Sb * P) * Sb := by rw [hPSa]
    _ = Sb * (P * Sb) := by group
    _ = Sb * (Sa * P) := by rw [hPSb]
    _ = Sa * Sb * P := by rw [← mul_assoc, ← hcomm]

private theorem tbD_typeDSimple_eq_simpleReflection {m p : ℕ} [Fact p.Prime] (hm : 4 ≤ m)
    (i : Fin m) :
    typeDSimple m p (by omega : 2 ≤ m) i =
      DScalarTorus.simpleReflection (m := p) (N := m) hm i := by
  by_cases hi : i.val + 1 < m
  · rw [typeDSimple, dif_pos hi, DScalarTorus.simpleReflection, dif_pos hi]
  · rw [typeDSimple, dif_neg hi, DScalarTorus.simpleReflection, dif_neg hi]
    exact tbD_permAut_swap_mul_sgn_pair
      (by intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_mk] at hv
          omega : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩)

private lemma tbD_ggLin_permAut (m p : ℕ) [Fact p.Prime] (σ : Equiv.Perm (Fin m))
    (v : Fin m → ZMod p) :
    ggLin (p := p) (tbD_iota m p) (permAut σ) v = ggQ2_DW_Q p m σ v := by
  funext j
  have hb : Additive.toMul ((tbD_iota m p).symm v) = fun k => ofAdd (v k) := by
    have h1 : (tbD_iota m p).symm v = Additive.ofMul (fun k => ofAdd (v k)) := by
      rw [AddEquiv.symm_apply_eq]; funext k; rfl
    rw [h1, toMul_ofMul]
  rw [ggLin_apply, hb, ggQ2_DW_Q_apply]
  change toAdd ((permAut σ (fun k => ofAdd (v k))) j) = v (σ.symm j)
  rw [tbD_toAdd_permAut]
  rfl

private theorem tbD_ggLin_g (m p : ℕ) [Fact p.Prime] (hm : 4 ≤ m) (i : Fin m)
    (v : Fin m → ZMod p) :
    ggLin (p := p) (tbD_iota m p) (typeDSimple m p (by omega) i) v
      = v - tbD_alpha m p (by omega) i v • tbD_h m p (by omega) i := by
  change ggLin (p := p) (tbD_iota m p) (typeDSimple m p (by omega) i) v
    = v - ggQ2_DW_dotLin p m (ggDSimple p m i) v • ggDSimple p m i
  by_cases hi : i.val + 1 < m
  · rw [show typeDSimple m p (by omega) i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        unfold typeDSimple; rw [dif_pos hi],
      tbD_ggLin_permAut]
    rw [← ggQ2_DW_r_eq_swap p m hm i hi, ggQ2_DW_r_apply]
  · have hbound1 : m - 1 < m := Nat.sub_lt (by omega) (by norm_num)
    have hbound2 : m - 2 < m := Nat.sub_lt (by omega) (by norm_num)
    have hlt : ¬ (⟨m - 1, hbound1⟩ : Fin m).val + 1 < m := by simp only [Fin.val_mk]; omega
    have hab : (⟨m - 2, hbound2⟩ : Fin m) ≠ ⟨m - 1, hbound1⟩ :=
      Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
    have hca : ((⟨m - 2, hbound2⟩ : Fin m) : ℕ) + 2 = m := by simp only [Fin.val_mk]; omega
    have hcb : ((⟨m - 1, hbound1⟩ : Fin m) : ℕ) + 1 = m := by simp only [Fin.val_mk]; omega
    have hieq : i = ⟨m - 1, hbound1⟩ := by
      apply Fin.ext
      show i.val = m - 1
      have h1 := i.isLt
      omega
    rw [hieq,
      show ggQ2_DW_dotLin p m (ggDSimple p m (⟨m - 1, hbound1⟩ : Fin m)) v
          = v ⟨m - 2, hbound2⟩ + v ⟨m - 1, hbound1⟩ from by
        rw [ggQ2_DW_dotLin_apply]
        exact ggQ2_DW_sum_ggDSimple_fork p m (by omega) ⟨m - 1, hbound1⟩ hlt v,
      show ggDSimple p m (⟨m - 1, hbound1⟩ : Fin m)
          = (fun l : Fin m => if (l : ℕ) + 2 = m ∨ (l : ℕ) + 1 = m then (1 : ZMod p) else 0)
        from by
        funext l
        exact ggQ2_DW_eval_fork p m ⟨m - 1, hbound1⟩ hlt l,
      show typeDSimple m p (by omega) (⟨m - 1, hbound1⟩ : Fin m) =
          permAut (Equiv.swap ⟨m - 2, hbound2⟩ ⟨m - 1, hbound1⟩) *
            (sgnAut ⟨m - 2, hbound2⟩ * sgnAut ⟨m - 1, hbound1⟩) from by
        unfold typeDSimple; rw [dif_neg hlt]]
    funext j
    have hb : Additive.toMul ((tbD_iota m p).symm v) = fun k => ofAdd (v k) := by
      have h1 : (tbD_iota m p).symm v = Additive.ofMul (fun k => ofAdd (v k)) := by
        rw [AddEquiv.symm_apply_eq]; funext k; rfl
      rw [h1, toMul_ofMul]
    rw [ggLin_apply, hb]
    change toAdd (((permAut (Equiv.swap ⟨m - 2, hbound2⟩ ⟨m - 1, hbound1⟩) *
        (sgnAut ⟨m - 2, hbound2⟩ * sgnAut ⟨m - 1, hbound1⟩) :
          MulAut (Fin m → Multiplicative (ZMod p))))
        (fun k => ofAdd (v k)) j) = _
    rw [MulAut.mul_apply, permAut_apply, Function.comp_apply, Equiv.swap_inv,
      tbD_toAdd_sgnAut_pair_swap (a := ⟨m - 2, hbound2⟩) (b := ⟨m - 1, hbound1⟩) hab v j]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hja : j = ⟨m - 2, hbound2⟩
    · subst hja
      rw [if_pos (Or.inl hca), if_pos rfl]
      ring
    · by_cases hjb : j = ⟨m - 1, hbound1⟩
      · subst hjb
        rw [if_pos (Or.inr hcb), if_neg (Ne.symm hab), if_pos rfl]
        ring
      · have hfa : ¬ ((j : ℕ) + 2 = m ∨ (j : ℕ) + 1 = m) := by
          rintro (h | h)
          · exact hja (Fin.ext (by have := j.isLt; omega))
          · exact hjb (Fin.ext (by have := j.isLt; omega))
        rw [if_neg hja, if_neg hjb, if_neg hfa]
        ring

private theorem tbD_hpair (m p : ℕ) [Fact p.Prime] (hm : 4 ≤ m) (i j : Fin m) :
    tbD_alpha m p (by omega) i (tbD_h m p (by omega) j) =
      (CartanMatrix.D m i j : ZMod p) := by
  change ggQ2_DW_dotLin p m (ggDSimple p m i) (ggDSimple p m j) = _
  rw [ggQ2_DW_dotLin_apply]
  exact ggQ2_DW_simple_dot p m hm i j

private lemma tbD_liftAut_injective {W : Type} [Group W] (W₀ : Type) [Group W₀] :
    Function.Injective (liftAut (W := W) W₀) := by
  intro σ τ h
  refine MulEquiv.ext fun w => ?_
  exact congrArg (fun e : MulAut (W × W₀) => (e (w, 1)).1) h

private lemma tbD_liftBs_injective {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type}
    [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) : Function.Injective (liftBs Θ) := by
  intro σ τ h
  exact tbD_liftAut_injective W₀ ((MulAut.congr Θ).injective h)

private lemma tbD_liftAut_sq {W : Type} [Group W] {W₀ : Type} [Group W₀] {σ : MulAut W}
    (hσ : σ ^ 2 = 1) : (liftAut W₀ σ) ^ 2 = 1 := by
  rw [← map_pow, hσ, map_one]

private lemma tbD_card_fix_lift {W : Type} [Group W] {W₀ : Type} [Group W₀] (σ : MulAut W) :
    Nat.card {f : W × W₀ // liftAut W₀ σ f = f} = Nat.card {w : W // σ w = w} * Nat.card W₀ := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  exact
  { toFun := fun f => (⟨f.1.1, congrArg Prod.fst f.2⟩, f.1.2)
    invFun := fun x => ⟨(x.1.1, x.2), Prod.ext x.1.2 rfl⟩
    left_inv := fun f => by ext <;> rfl
    right_inv := fun x => by ext <;> rfl }

private lemma tbD_isRefl_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L']
    {A : Subgroup L'} {W W₀ : Type} [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥A) {σ : MulAut W}
    (hσ : σ ^ 2 = 1) (hfix : Nat.card {w : W // σ w = w} * p = Nat.card W) :
    GGIsReflection p (liftBs Θ σ) :=
  ⟨by rw [← map_pow, hσ, map_one],
    (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 (tbD_liftAut_sq hσ))
      (by rw [tbD_card_fix_lift, Nat.card_prod, mul_right_comm, hfix])).2⟩

private lemma tbD_permAut_mem_evenSignedAut {m p : ℕ} (σ : Equiv.Perm (Fin m)) :
    permAut (p := p) σ ∈ evenSignedAut m p := by
  let P : Equiv.Perm (Fin m) →* MulAut (Fin m → Multiplicative (ZMod p)) :=
  { toFun := permAut (p := p)
    map_one' := by apply MulEquiv.ext; intro f; funext t; rfl
    map_mul' := by
      intro σ τ
      apply MulEquiv.ext; intro f; funext t; rfl }
  have hgen : Subgroup.closure {τ : Equiv.Perm (Fin m) | τ.IsSwap} = ⊤ :=
    Equiv.Perm.closure_isSwap
  have hle : Subgroup.closure {τ : Equiv.Perm (Fin m) | τ.IsSwap} ≤
      (evenSignedAut m p).comap P := by
    rw [Subgroup.closure_le]
    rintro τ hτ
    change P τ ∈ evenSignedAut m p
    obtain ⟨a, b, hab, rfl⟩ := hτ
    refine Subgroup.subset_closure ?_
    exact Or.inl ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩
  have : σ ∈ (evenSignedAut m p).comap P := by
    apply hle
    rw [hgen]; trivial
  exact this

theorem tbD_evenSignedAut_eq_evenSignedGroup {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    evenSignedAut m p = DScalarTorus.evenSignedGroup (p := p) (N := m) := by
  apply le_antisymm
  · unfold evenSignedAut evenSignedSupportedAut
    rw [Subgroup.closure_le]
    rintro σ (h | h)
    · obtain ⟨a, -, b, -, hab, rfl⟩ := h
      exact DScalarTorus.permAut_mem_evenSignedGroup _
    · obtain ⟨a, -, b, -, hab, rfl⟩ := h
      exact DScalarTorus.sgnAut_pair_mem_evenSignedGroup hab
  · exact DScalarTorus.evenSignedGroup_le (p := p) (N := m) hp2
      (fun i j hij => by
        refine Subgroup.subset_closure ?_
        exact Or.inr ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, hij, rfl⟩)
      (fun σ => tbD_permAut_mem_evenSignedAut σ)

private theorem tbD_closure_simple {m p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m) :
    Subgroup.closure (Set.range (fun i : Fin m => typeDSimple m p (by omega) i)) =
      evenSignedAut m p := by
  classical
  obtain ⟨eS, heS⟩ := DScalarTorus.exists_evenSignedCoxeterEquiv (p := p) (N := m) hp2 hm
  have hfun : (fun i : Fin m =>
        ((eS ((ggCoxeterMatrixD m).simple i) :
            DScalarTorus.evenSignedGroup (p := p) (N := m)) :
          MulAut (Fin m → Multiplicative (ZMod p)))) =
      (fun i : Fin m => typeDSimple m p (by omega) i) := by
    funext i
    rw [heS i, tbD_typeDSimple_eq_simpleReflection hm i]
  have htop : Subgroup.closure (Set.range (ggCoxeterMatrixD m).simple) = ⊤ :=
    (ggCoxeterMatrixD m).toCoxeterSystem.subgroup_closure_range_simple
  have hgen : Subgroup.closure (Set.range fun i : Fin m =>
      (eS ((ggCoxeterMatrixD m).simple i) :
        DScalarTorus.evenSignedGroup (p := p) (N := m))) = ⊤ := by
    have h := MonoidHom.map_closure eS.toMonoidHom (Set.range (ggCoxeterMatrixD m).simple)
    rw [htop, Subgroup.map_top_of_surjective eS.toMonoidHom eS.surjective] at h
    rw [h]
    congr 1
    change Set.range (eS.toMonoidHom ∘ (ggCoxeterMatrixD m).simple) =
      eS.toMonoidHom '' Set.range (ggCoxeterMatrixD m).simple
    rw [Set.range_comp]
  have hmap := MonoidHom.map_closure (DScalarTorus.evenSignedGroup (p := p) (N := m)).subtype
      (Set.range fun i : Fin m => (eS ((ggCoxeterMatrixD m).simple i) :
        DScalarTorus.evenSignedGroup (p := p) (N := m)))
  rw [hgen, Subgroup.map_top, Subgroup.range_subtype] at hmap
  rw [tbD_evenSignedAut_eq_evenSignedGroup hp2, hmap]
  congr 1
  rw [← Set.range_comp]
  exact congrArg Set.range hfun.symm

theorem exists_typeD_datum_of_evenSignedAut {G : Type} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (evenSignedAut m p).map (liftBs Θ)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin m → MulAut ↥Bs) (h : Fin m → V) (α : Fin m → Module.Dual (ZMod p) V),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (CartanMatrix.D m i j : ZMod p)) ∧
      (∃ f : (ggCoxeterMatrixD m).Group ≃* ↥(ggAutomizer X Bs),
        ∀ i, (f ((ggCoxeterMatrixD m).simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i : Fin m, φ i = liftBs Θ (typeDSimple m p (by omega) i)) := by
  classical
  have hp : p.Prime := Fact.out
  let W := Fin m → Multiplicative (ZMod p)
  let H : Subgroup (MulAut W) := evenSignedAut m p
  have hcomm : ∀ u v : W₀, u * v = v * u := by
    intro u v
    have h : Θ (1, u) * Θ (1, v) = Θ (1, v) * Θ (1, u) := hBs.1.is_comm.comm _ _
    have h' : Θ ((1, u) * (1, v)) = Θ ((1, v) * (1, u)) := by
      rw [map_mul, map_mul]
      exact h
    simpa using congrArg Prod.snd (Θ.injective h')
  have hpow : ∀ u : W₀, u ^ p = 1 := by
    intro u
    have h : Θ (1, u) ^ p = 1 := Subtype.ext (hBs.2 _ (Θ (1, u)).2)
    have h' : Θ ((1, u) ^ p) = Θ 1 := by rw [map_pow, h, map_one]
    simpa using congrArg Prod.snd (Θ.injective h')
  let iA : AddCommGroup (Additive W₀) :=
    { (inferInstance : AddGroup (Additive W₀)) with
      add_comm := fun a b => congrArg Additive.ofMul (hcomm (Additive.toMul a) (Additive.toMul b)) }
  let iM : Module (ZMod p) (Additive W₀) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hpow _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  let V := (Fin m → ZMod p) × Additive W₀
  let ι₀ : Additive (W × W₀) ≃+ V :=
    (AddEquiv.prodAdditive ..).trans (AddEquiv.prodCongr (tbD_iota m p) (AddEquiv.refl _))
  let ι : Additive ↥Bs ≃+ V := (MulEquiv.toAdditive Θ.symm).trans ι₀
  let φ : Fin m → MulAut ↥Bs := fun i => liftBs Θ (typeDSimple m p (by omega) i)
  have hinj : Function.Injective (liftBs Θ) := tbD_liftBs_injective Θ
  have hmapΦ : H.map (liftBs Θ) = ggAutomizer X Bs := by
    change (evenSignedAut m p).map (liftBs Θ) = ggAutomizer X Bs
    exact hX.symm
  obtain ⟨eS, heS⟩ := DScalarTorus.exists_evenSignedCoxeterEquiv (p := p) (N := m) hp2 hm
  have heqAut : DScalarTorus.evenSignedGroup (p := p) (N := m) = evenSignedAut m p :=
    (tbD_evenSignedAut_eq_evenSignedGroup hp2).symm
  let eEq : DScalarTorus.evenSignedGroup (p := p) (N := m) ≃* evenSignedAut m p :=
    MulEquiv.subgroupCongr heqAut
  let isoHAut : H ≃* ↥(ggAutomizer X Bs) :=
    (Subgroup.equivMapOfInjective H (liftBs Θ) hinj).trans (MulEquiv.subgroupCongr hmapΦ)
  have isoHAut_apply : ∀ h : H, (↑(isoHAut h) : MulAut ↥Bs) = liftBs Θ ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H (liftBs Θ) hinj).trans
        (MulEquiv.subgroupCongr hmapΦ) h) : MulAut ↥Bs) = liftBs Θ ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  let f : (ggCoxeterMatrixD m).Group ≃* ↥(ggAutomizer X Bs) :=
    (eS.trans eEq).trans isoHAut
  have hf_simple : ∀ i, (f ((ggCoxeterMatrixD m).simple i) : MulAut ↥Bs) = φ i := by
    intro i
    have h1 : (↑(eEq (eS ((ggCoxeterMatrixD m).simple i))) : MulAut W) =
        typeDSimple m p (by omega) i := by
      rw [MulEquiv.subgroupCongr_apply, heS i, tbD_typeDSimple_eq_simpleReflection hm i]
    calc (f ((ggCoxeterMatrixD m).simple i) : MulAut ↥Bs)
        = ↑(isoHAut (eEq (eS ((ggCoxeterMatrixD m).simple i)))) := rfl
      _ = liftBs Θ ↑(eEq (eS ((ggCoxeterMatrixD m).simple i))) := isoHAut_apply _
      _ = liftBs Θ (typeDSimple m p (by omega) i) := by rw [h1]
      _ = φ i := rfl
  have hpair' : ∀ i j, (tbD_alpha m p (by omega) i) (tbD_h m p (by omega) j) =
      (CartanMatrix.D m i j : ZMod p) := tbD_hpair m p hm
  have hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
    change ggAutomizer X Bs = Subgroup.closure (Set.range φ)
    rw [← hmapΦ]
    change H.map (liftBs Θ) = Subgroup.closure (Set.range φ)
    rw [show H = Subgroup.closure (Set.range (fun i : Fin m => typeDSimple m p (by omega) i))
        from (tbD_closure_simple hp2 hm).symm]
    rw [MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp]
    rfl
  refine ⟨V, inferInstance, inferInstance, ι, φ, fun i => (tbD_h m p (by omega) i, 0),
    fun i => (tbD_alpha m p (by omega) i).comp
      (LinearMap.fst (ZMod p) (Fin m → ZMod p) (Additive W₀)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i w
    obtain ⟨v, u⟩ := w
    rw [show ι = (MulEquiv.toAdditive Θ.symm).trans ι₀ from rfl,
      show φ i = MulAut.congr Θ (liftAut W₀ (typeDSimple m p (by omega) i)) from rfl,
      ggLin_mulEquiv_congr]
    have key : ggLin (p := p) ι₀ (liftAut W₀ (typeDSimple m p (by omega) i)) (v, u) =
        (ggLin (p := p) (tbD_iota m p) (typeDSimple m p (by omega) i) v, u) := by
      rw [ggLin_apply, ggLin_apply]
      rfl
    rw [key, tbD_ggLin_g m p hm i v]
    refine Prod.ext rfl ?_
    show u = u - (tbD_alpha m p (by omega) i v) • (0 : Additive W₀)
    rw [smul_zero, sub_zero]
  · intro i
    change GGIsReflection p (liftBs Θ (typeDSimple m p (by omega) i))
    by_cases hi : i.val + 1 < m
    · rw [show typeDSimple m p (by omega) i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
          unfold typeDSimple; rw [dif_pos hi]]
      exact tbD_isRefl_lift hp hp2 Θ (permAut_swap_sq _ _)
        (card_fix_permAut_swap hp hp2 (tbD_fin_ne_succ hi))
    · have hb2 : m - 2 < m := Nat.sub_lt (by omega) (by norm_num)
      have hb1 : m - 1 < m := Nat.sub_lt (by omega) (by norm_num)
      have hne : (⟨m - 2, hb2⟩ : Fin m) ≠ ⟨m - 1, hb1⟩ :=
        Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
      rw [tbD_typeDSimple_eq_simpleReflection hm i,
        show DScalarTorus.simpleReflection (m := p) (N := m) hm i =
          sgnAut ⟨m - 2, hb2⟩ * sgnAut ⟨m - 1, hb1⟩ *
            permAut (Equiv.swap ⟨m - 2, hb2⟩ ⟨m - 1, hb1⟩) from by
          rw [DScalarTorus.simpleReflection, dif_neg hi]]
      exact tbD_isRefl_lift hp hp2 Θ (OrthExcEven.sgnTransp_sq hne)
        (OrthExcEven.card_fix_sgnTransp hp hp2 hne)
  · intro i j
    exact hpair' i j
  · exact ⟨f, hf_simple⟩
  · exact hclos
  · intro i
    rfl

end TypeDDatum

end CFSG.StandardType

end
