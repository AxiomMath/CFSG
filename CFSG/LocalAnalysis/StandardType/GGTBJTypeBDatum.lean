module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.StandardType.SpJoin
open Multiplicative

namespace TypeBDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def signedSupportedAut (m p : ℕ) (S : Finset (Fin m)) :
    Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
  Subgroup.closure ({σ | ∃ i ∈ S, σ = sgnAut (p := p) i} ∪
    {σ | ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ σ = permAut (p := p) (Equiv.swap a b)})

@[expose] def signedAut (m p : ℕ) : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
  signedSupportedAut m p Finset.univ

theorem signedAut_eq_bSignedFull (m p : ℕ) : signedAut m p = bSignedFull m p := by
  unfold signedAut signedSupportedAut bSignedFull
  congr 1
  ext σ
  constructor
  · rintro (⟨i, -, rfl⟩ | ⟨a, -, b, -, hab, rfl⟩)
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨a, b, hab, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨a, b, hab, rfl⟩)
    · exact Or.inl ⟨i, Finset.mem_univ i, rfl⟩
    · exact Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩

@[expose] def permSupportedAut (m p : ℕ) (S : Finset (Fin m)) :
    Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
  Subgroup.closure {σ | ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ σ = permAut (p := p) (Equiv.swap a b)}

@[expose] def twistedPermAut (m p : ℕ) (S : Finset (Fin m)) (s : Fin m → ZMod p)
    (hs : ∀ i, s i * s i = 1) : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
  (permSupportedAut m p S).map (MulAut.conj (diagAut s hs)).toMonoidHom

@[expose] def liftAut {W : Type} [Group W] (W₀ : Type) [Group W₀] : MulAut W →* MulAut (W × W₀) where
  toFun σ := MulEquiv.prodCongr σ (MulEquiv.refl W₀)
  map_one' := by ext <;> rfl
  map_mul' σ τ := by ext <;> rfl

@[expose] def liftBs {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type} [Group W] [Group W₀]
    (Θ : (W × W₀) ≃* ↥Bs) : MulAut W →* MulAut ↥Bs :=
  (MulAut.congr Θ).toMonoidHom.comp (liftAut W₀)

@[simp] theorem liftAut_apply {W : Type} [Group W] (W₀ : Type) [Group W₀] (σ : MulAut W) (w : W)
    (u : W₀) : liftAut W₀ σ (w, u) = (σ w, u) := rfl

@[simp] theorem liftBs_apply {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type} [Group W]
    [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) (σ : MulAut W) (w : W) (u : W₀) :
    liftBs Θ σ (Θ (w, u)) = Θ (σ w, u) := by
  change (MulAut.congr Θ) (liftAut W₀ σ) (Θ (w, u)) = _
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private lemma tbB_toPerm_sgnAut {p k : ℕ} (i : Fin k) :
    MulAut.toPerm (Fin k → Multiplicative (ZMod p)) (sgnAut i) = coordInv k p i := by
  ext v; rfl

private lemma tbB_toPerm_permAut {p k : ℕ} (σ : Equiv.Perm (Fin k)) :
    MulAut.toPerm (Fin k → Multiplicative (ZMod p)) (permAut σ) = coordPerm k p σ := by
  ext v; rfl

private lemma tbB_toPerm_injective {p k : ℕ} :
    Function.Injective (MulAut.toPerm (Fin k → Multiplicative (ZMod p))) := by
  intro a b h
  exact MulEquiv.ext fun v =>
    congrArg (fun e : Equiv.Perm (Fin k → Multiplicative (ZMod p)) => e v) h

private lemma tbB_fin_ne_succ {k : ℕ} {i : Fin k} (hi : i.val + 1 < k) :
    i ≠ ⟨i.val + 1, hi⟩ := by
  intro hh
  have h2 : i.val = i.val + 1 := by
    have := congrArg Fin.val hh
    simpa using this
  omega

private lemma tbB_liftAut_injective {W : Type} [Group W] (W₀ : Type) [Group W₀] :
    Function.Injective (liftAut (W := W) W₀) := by
  intro σ τ h
  refine MulEquiv.ext fun w => ?_
  exact congrArg (fun e : MulAut (W × W₀) => (e (w, 1)).1) h

private lemma tbB_liftBs_injective {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type}
    [Group W] [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) : Function.Injective (liftBs Θ) := by
  intro σ τ h
  exact tbB_liftAut_injective W₀ ((MulAut.congr Θ).injective h)

private lemma tbB_liftAut_sq {W : Type} [Group W] {W₀ : Type} [Group W₀] {σ : MulAut W}
    (hσ : σ ^ 2 = 1) : (liftAut W₀ σ) ^ 2 = 1 := by
  rw [← map_pow, hσ, map_one]

private lemma tbB_card_fix_lift {W : Type} [Group W] {W₀ : Type} [Group W₀] (σ : MulAut W) :
    Nat.card {f : W × W₀ // liftAut W₀ σ f = f} = Nat.card {w : W // σ w = w} * Nat.card W₀ := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  exact
  { toFun := fun f => (⟨f.1.1, congrArg Prod.fst f.2⟩, f.1.2)
    invFun := fun x => ⟨(x.1.1, x.2), Prod.ext x.1.2 rfl⟩
    left_inv := fun f => by ext <;> rfl
    right_inv := fun x => by ext <;> rfl }

theorem _root_.CFSG.StandardType.ggIsReflection_liftBs {G : Type} [Group G] {Bs : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W W₀ : Type} [Group W] [Group W₀]
    (Θ : (W × W₀) ≃* ↥Bs) {σ : MulAut W}
    (hσ2 : σ ^ 2 = 1) (hcard : Nat.card {w : W // σ w = w} * p = Nat.card W) :
    GGIsReflection p (TypeBDatum.liftBs Θ σ) :=
  ⟨by rw [← map_pow, hσ2, map_one],
    (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2
      (tbB_liftAut_sq hσ2))
      (by rw [tbB_card_fix_lift, Nat.card_prod, mul_right_comm, hcard])).2⟩

private noncomputable def tbB_g (m p : ℕ) (i : Fin m) :
    MulAut (Fin m → Multiplicative (ZMod p)) :=
  if hi : i.val + 1 < m then permAut (Equiv.swap i ⟨i.val + 1, hi⟩) else sgnAut i

private noncomputable def tbB_h (m p : ℕ) [Fact p.Prime] (i : Fin m) : Fin m → ZMod p :=
  if hi : i.val + 1 < m then
    Pi.single i (1 : ZMod p) - Pi.single ⟨i.val + 1, hi⟩ (1 : ZMod p)
  else (2 : ZMod p) • Pi.single i (1 : ZMod p)

private noncomputable def tbB_alpha (m p : ℕ) (i : Fin m) :
    Module.Dual (ZMod p) (Fin m → ZMod p) :=
  if hi : i.val + 1 < m then
    (LinearMap.proj i - LinearMap.proj ⟨i.val + 1, hi⟩ : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p)
  else LinearMap.proj i

private noncomputable def tbB_iota (m p : ℕ) :
    Additive (Fin m → Multiplicative (ZMod p)) ≃+ (Fin m → ZMod p) where
  toFun f i := toAdd (f i)
  invFun v i := ofAdd (v i)
  left_inv f := by funext i; rfl
  right_inv v := by funext i; rfl
  map_add' f g := by
    funext i
    change toAdd ((f + g).toMul i) = toAdd (f.toMul i) + toAdd (g.toMul i)
    rw [toMul_add, Pi.mul_apply, toAdd_mul]

private lemma tbB_toAdd_sgnAut {p k : ℕ} (i : Fin k) (v : Fin k → ZMod p) (j : Fin k) :
    toAdd ((sgnAut i (fun l => ofAdd (v l))) j) = if j = i then -v i else v j := by
  rw [sgnAut_apply]
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self, toAdd_inv, toAdd_ofAdd, if_pos rfl]
  · rw [Function.update_of_ne hji, toAdd_ofAdd, if_neg hji]

private lemma tbB_toAdd_permAut {p k : ℕ} (σ : Equiv.Perm (Fin k)) (v : Fin k → ZMod p)
    (j : Fin k) :
    toAdd ((permAut σ (fun l => ofAdd (v l))) j) = v (σ⁻¹ j) := by
  rw [permAut_apply, Function.comp_apply]
  exact toAdd_ofAdd (v (σ⁻¹ j))

private lemma tbB_single_apply {m p : ℕ} (a b : Fin m) :
    (Pi.single a (1 : ZMod p) : Fin m → ZMod p) b = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

private theorem tbB_ggLin_g (m p : ℕ) [Fact p.Prime] (i : Fin m) (v : Fin m → ZMod p) :
    ggLin (p := p) (tbB_iota m p) (tbB_g m p i) v
      = v - tbB_alpha m p i v • tbB_h m p i := by
  funext j
  have hb : Additive.toMul ((tbB_iota m p).symm v) = fun k => ofAdd (v k) := by
    have h1 : (tbB_iota m p).symm v = Additive.ofMul (fun k => ofAdd (v k)) := by
      rw [AddEquiv.symm_apply_eq]
      funext k
      rfl
    rw [h1, toMul_ofMul]
  rw [ggLin_apply, hb]
  change toAdd ((tbB_g m p i (fun k => ofAdd (v k))) j)
    = (v - tbB_alpha m p i v • tbB_h m p i) j
  by_cases hi : i.val + 1 < m
  · rw [show tbB_g m p i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
          unfold tbB_g; rw [dif_pos hi],
        show tbB_alpha m p i = (LinearMap.proj i - LinearMap.proj ⟨i.val + 1, hi⟩) from by
          unfold tbB_alpha; rw [dif_pos hi],
        show tbB_h m p i = Pi.single i (1 : ZMod p) - Pi.single ⟨i.val + 1, hi⟩ (1 : ZMod p)
          from by unfold tbB_h; rw [dif_pos hi]]
    rw [tbB_toAdd_permAut, Equiv.swap_inv]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
      LinearMap.proj_apply]
    by_cases hji : j = i
    · subst hji
      rw [Equiv.swap_apply_left, Pi.single_eq_same,
        Pi.single_eq_of_ne' (tbB_fin_ne_succ hi).symm]
      ring
    · by_cases hjs : j = ⟨i.val + 1, hi⟩
      · subst hjs
        rw [Equiv.swap_apply_right, Pi.single_eq_same,
          Pi.single_eq_of_ne' (tbB_fin_ne_succ hi)]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hji hjs, Pi.single_eq_of_ne' (Ne.symm hji),
          Pi.single_eq_of_ne' (Ne.symm hjs)]
        ring
  · rw [show tbB_g m p i = sgnAut i from by unfold tbB_g; rw [dif_neg hi],
        show tbB_alpha m p i = LinearMap.proj i from by unfold tbB_alpha; rw [dif_neg hi],
        show tbB_h m p i = (2 : ZMod p) • Pi.single i (1 : ZMod p) from by
          unfold tbB_h; rw [dif_neg hi]]
    rw [tbB_toAdd_sgnAut]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LinearMap.proj_apply]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, Pi.single_eq_same]
      ring
    · rw [if_neg hji, Pi.single_eq_of_ne' (Ne.symm hji)]
      ring

private theorem tbB_toPerm_g (m p : ℕ) (i : Fin m) :
    MulAut.toPerm (Fin m → Multiplicative (ZMod p)) (tbB_g m p i) = spReflPerm m p i := by
  by_cases hi : i.val + 1 < m
  · rw [show tbB_g m p i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        unfold tbB_g; rw [dif_pos hi],
      tbB_toPerm_permAut, spReflPerm_of_lt m p i hi]
  · rw [show tbB_g m p i = sgnAut i from by unfold tbB_g; rw [dif_neg hi],
      tbB_toPerm_sgnAut, spReflPerm_of_not_lt m p i hi]

private theorem tbB_signedAut_map_toPerm (m p : ℕ) :
    (signedAut m p).map (MulAut.toPerm (Fin m → Multiplicative (ZMod p))) =
      spSignedGroup m p := by
  unfold signedAut signedSupportedAut
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨α, hα, rfl⟩
    rcases hα with hα | hα
    · obtain ⟨i, -, rfl⟩ := hα
      rw [tbB_toPerm_sgnAut]
      exact coordInv_mem_spSignedGroup i
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hα
      rw [tbB_toPerm_permAut]
      exact coordPerm_mem_spSignedGroup (Equiv.swap a b)
  · rw [spSignedGroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨i, rfl⟩
    by_cases hi : i.val + 1 < m
    · rw [spReflPerm_of_lt m p i hi]
      refine Subgroup.subset_closure ⟨permAut (Equiv.swap i ⟨i.val + 1, hi⟩), ?_, ?_⟩
      · exact Or.inr ⟨i, Finset.mem_univ i, ⟨i.val + 1, hi⟩, Finset.mem_univ _,
          tbB_fin_ne_succ hi, rfl⟩
      · rw [tbB_toPerm_permAut]
    · rw [spReflPerm_of_not_lt m p i hi]
      refine Subgroup.subset_closure ⟨sgnAut i, Or.inl ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
      · rw [tbB_toPerm_sgnAut]

private theorem tbB_closure_g (m p : ℕ) :
    Subgroup.closure (Set.range (tbB_g m p)) = signedAut m p := by
  have h1 : (Subgroup.closure (Set.range (tbB_g m p))).map
      (MulAut.toPerm (Fin m → Multiplicative (ZMod p))) = spSignedGroup m p := by
    rw [MonoidHom.map_closure, spSignedGroup]
    congr 1
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i => tbB_toPerm_g m p i)
  have hmapg : (Subgroup.closure (Set.range (tbB_g m p))).map
      (MulAut.toPerm (Fin m → Multiplicative (ZMod p))) =
      (signedAut m p).map (MulAut.toPerm (Fin m → Multiplicative (ZMod p))) :=
    h1.trans (tbB_signedAut_map_toPerm m p).symm
  exact Subgroup.map_injective (f := MulAut.toPerm (Fin m → Multiplicative (ZMod p)))
    (tbB_toPerm_injective (p := p) (k := m)) hmapg

theorem exists_typeB_datum_of_signedAut {G : Type} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 2 ≤ m) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin m → MulAut ↥Bs) (h : Fin m → V) (α : Fin m → Module.Dual (ZMod p) V)
      (C : Matrix (Fin m) (Fin m) ℤ),
      GGIntCartan (CoxeterMatrix.B m) C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : (CoxeterMatrix.B m).Group ≃* ↥(ggAutomizer X Bs),
        ∀ i, (f ((CoxeterMatrix.B m).simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∀ i : Fin m, φ i = liftBs Θ
        (if hi : i.val + 1 < m then permAut (p := p) (Equiv.swap i ⟨i.val + 1, hi⟩)
          else sgnAut (p := p) i)) := by
  classical
  have hp : p.Prime := Fact.out
  let W := Fin m → Multiplicative (ZMod p)
  let H : Subgroup (MulAut W) := signedAut m p
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
    (AddEquiv.prodAdditive ..).trans (AddEquiv.prodCongr (tbB_iota m p) (AddEquiv.refl _))
  let ι : Additive ↥Bs ≃+ V := (MulEquiv.toAdditive Θ.symm).trans ι₀
  let φ : Fin m → MulAut ↥Bs := fun i => liftBs Θ (tbB_g m p i)
  have hinj : Function.Injective (liftBs Θ) := tbB_liftBs_injective Θ
  have hmapPerm : H.map (MulAut.toPerm W) = spSignedGroup m p :=
    tbB_signedAut_map_toPerm m p
  have hmapΦ : H.map (liftBs Θ) = ggAutomizer X Bs := hX.symm
  obtain ⟨e, he⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 hm
  let isoHSp : H ≃* ↥(spSignedGroup m p) :=
    (Subgroup.equivMapOfInjective H (MulAut.toPerm W)
        (tbB_toPerm_injective (p := p) (k := m))).trans
      (MulEquiv.subgroupCongr hmapPerm)
  let isoHAut : H ≃* ↥(ggAutomizer X Bs) :=
    (Subgroup.equivMapOfInjective H (liftBs Θ) hinj).trans (MulEquiv.subgroupCongr hmapΦ)
  have isoHSp_apply : ∀ h : H, (↑(isoHSp h) : Equiv.Perm W) = MulAut.toPerm W ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H (MulAut.toPerm W)
        (tbB_toPerm_injective (p := p) (k := m))).trans (MulEquiv.subgroupCongr hmapPerm) h) :
        Equiv.Perm W) = MulAut.toPerm W ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  have isoHAut_apply : ∀ h : H, (↑(isoHAut h) : MulAut ↥Bs) = liftBs Θ ↑h := by
    intro h
    change (↑((Subgroup.equivMapOfInjective H (liftBs Θ) hinj).trans
        (MulEquiv.subgroupCongr hmapΦ) h) : MulAut ↥Bs) = liftBs Θ ↑h
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  let f : (CoxeterMatrix.B m).Group ≃* ↥(ggAutomizer X Bs) :=
    (e.trans isoHSp.symm).trans isoHAut
  have hg_toPerm : ∀ i, MulAut.toPerm W (tbB_g m p i) = spReflPerm m p i :=
    tbB_toPerm_g m p
  have hg_mem : ∀ i, tbB_g m p i ∈ H := by
    intro i
    change tbB_g m p i ∈ signedAut m p
    unfold signedAut signedSupportedAut
    refine Subgroup.subset_closure ?_
    by_cases hi : i.val + 1 < m
    · refine Or.inr ⟨i, Finset.mem_univ i, ⟨i.val + 1, hi⟩, Finset.mem_univ _,
        tbB_fin_ne_succ hi, ?_⟩
      unfold tbB_g; rw [dif_pos hi]
    · refine Or.inl ⟨i, Finset.mem_univ i, ?_⟩
      unfold tbB_g; rw [dif_neg hi]
  have hf_simple : ∀ i, (f ((CoxeterMatrix.B m).simple i) : MulAut ↥Bs) = φ i := by
    intro i
    have hei : e ((CoxeterMatrix.B m).simple i) =
        ⟨spReflPerm m p i, spReflPerm_mem_spSignedGroup m p i⟩ := Subtype.ext (he i)
    have hsymm : isoHSp.symm ⟨spReflPerm m p i, spReflPerm_mem_spSignedGroup m p i⟩ =
        ⟨tbB_g m p i, hg_mem i⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [isoHSp_apply]
      exact (hg_toPerm i).symm
    calc (f ((CoxeterMatrix.B m).simple i) : MulAut ↥Bs)
        = ↑(isoHAut (isoHSp.symm (e ((CoxeterMatrix.B m).simple i)))) := by
          simp only [f, MulEquiv.trans_apply]
      _ = ↑(isoHAut (isoHSp.symm ⟨spReflPerm m p i,
            spReflPerm_mem_spSignedGroup m p i⟩)) := by rw [hei]
      _ = ↑(isoHAut ⟨tbB_g m p i, hg_mem i⟩) := by rw [hsymm]
      _ = liftBs Θ (tbB_g m p i) := isoHAut_apply ⟨tbB_g m p i, hg_mem i⟩
      _ = φ i := rfl
  have hg_closure : Subgroup.closure (Set.range (tbB_g m p)) = H := tbB_closure_g m p
  have hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
    rw [hmapΦ.symm, ← hg_closure, MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hpair : ∀ i j, tbB_alpha m p i (tbB_h m p j) = (CartanMatrix.B m i j : ZMod p) := by
    intro i j
    by_cases hi : i.val + 1 < m <;> by_cases hj : j.val + 1 < m
    · have h1 : tbB_alpha m p i = LinearMap.proj i - LinearMap.proj ⟨i.val + 1, hi⟩ := by
        unfold tbB_alpha; rw [dif_pos hi]
      have h2 : tbB_h m p j =
          Pi.single j (1 : ZMod p) - Pi.single ⟨j.val + 1, hj⟩ (1 : ZMod p) := by
        unfold tbB_h; rw [dif_pos hj]
      rw [h1, h2]
      simp only [LinearMap.sub_apply, LinearMap.proj_apply, Pi.sub_apply, tbB_single_apply,
        CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
      push_cast
      split_ifs <;> (first | omega | norm_num | ring)
    · have h1 : tbB_alpha m p i = LinearMap.proj i - LinearMap.proj ⟨i.val + 1, hi⟩ := by
        unfold tbB_alpha; rw [dif_pos hi]
      have h2 : tbB_h m p j = (2 : ZMod p) • Pi.single j (1 : ZMod p) := by
        unfold tbB_h; rw [dif_neg hj]
      rw [h1, h2, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.proj_apply]
      simp only [Pi.smul_apply, smul_eq_mul, tbB_single_apply, CartanMatrix.B, Matrix.of_apply,
        Fin.ext_iff]
      push_cast
      split_ifs <;> (first | omega | norm_num | ring)
    · have h1 : tbB_alpha m p i = LinearMap.proj i := by
        unfold tbB_alpha; rw [dif_neg hi]
      have h2 : tbB_h m p j =
          Pi.single j (1 : ZMod p) - Pi.single ⟨j.val + 1, hj⟩ (1 : ZMod p) := by
        unfold tbB_h; rw [dif_pos hj]
      rw [h1, h2, LinearMap.proj_apply, Pi.sub_apply]
      simp only [tbB_single_apply, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
      push_cast
      split_ifs <;> (first | omega | norm_num | ring)
    · have h1 : tbB_alpha m p i = LinearMap.proj i := by
        unfold tbB_alpha; rw [dif_neg hi]
      have h2 : tbB_h m p j = (2 : ZMod p) • Pi.single j (1 : ZMod p) := by
        unfold tbB_h; rw [dif_neg hj]
      rw [h1, h2, LinearMap.proj_apply]
      simp only [Pi.smul_apply, smul_eq_mul, tbB_single_apply, CartanMatrix.B, Matrix.of_apply,
        Fin.ext_iff]
      push_cast
      split_ifs <;> (first | omega | norm_num | ring)
  refine ⟨V, inferInstance, inferInstance, ι, φ, fun i => (tbB_h m p i, 0),
    fun i => (tbB_alpha m p i).comp (LinearMap.fst (ZMod p) (Fin m → ZMod p) (Additive W₀)),
    CartanMatrix.B m, ggIntCartan_B m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i w
    obtain ⟨v, u⟩ := w
    rw [show ι = (MulEquiv.toAdditive Θ.symm).trans ι₀ from rfl,
      show φ i = MulAut.congr Θ (liftAut W₀ (tbB_g m p i)) from rfl,
      ggLin_mulEquiv_congr]
    have key : ggLin (p := p) ι₀ (liftAut W₀ (tbB_g m p i)) (v, u) =
        (ggLin (p := p) (tbB_iota m p) (tbB_g m p i) v, u) := by
      rw [ggLin_apply, ggLin_apply]
      rfl
    rw [key, tbB_ggLin_g]
    refine Prod.ext rfl ?_
    show u = u - (tbB_alpha m p i v) • (0 : Additive W₀)
    rw [smul_zero, sub_zero]
  · intro i
    change GGIsReflection p (liftBs Θ (tbB_g m p i))
    by_cases hi : i.val + 1 < m
    · rw [show tbB_g m p i = permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
          unfold tbB_g; rw [dif_pos hi]]
      exact ggIsReflection_liftBs hp hp2 Θ (permAut_swap_sq _ _)
        (card_fix_permAut_swap hp hp2 (tbB_fin_ne_succ hi))
    · rw [show tbB_g m p i = sgnAut i from by unfold tbB_g; rw [dif_neg hi]]
      exact ggIsReflection_liftBs hp hp2 Θ (sgnAut_sq i) (card_fix_sgnAut hp hp2 i)
  · intro i j
    exact hpair i j
  · exact ⟨f, hf_simple⟩
  · exact hclos
  · intro i
    rfl

theorem exists_prodEquiv_of_frame {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {W : Type} [Group W] (Θ₁ : W →* G)
    (hΘ₁ : Function.Injective Θ₁) (hle : Θ₁.range ≤ Bs) (C : Subgroup G) (hC : C ≤ Bs)
    (hsup : Θ₁.range ⊔ C = Bs) (hdisj : Θ₁.range ⊓ C = ⊥) :
    ∃ Θ : (W × ↥C) ≃* ↥Bs, ∀ (w : W) (c : ↥C), ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c := by
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let f : W × ↥C →* ↥Bs :=
    { toFun := fun x => ⟨Θ₁ x.1 * x.2, mul_mem (hle ⟨x.1, rfl⟩) (hC x.2.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have h := hcomm (x.2 : G) (hC x.2.2) (Θ₁ y.1) (hle ⟨y.1, rfl⟩)
        change Θ₁ (x.1 * y.1) * ((x.2 : G) * (y.2 : G)) = (Θ₁ x.1 * x.2) * (Θ₁ y.1 * y.2)
        rw [map_mul]
        calc Θ₁ x.1 * Θ₁ y.1 * (↑x.2 * ↑y.2) = Θ₁ x.1 * (Θ₁ y.1 * ↑x.2) * ↑y.2 := by group
          _ = Θ₁ x.1 * (↑x.2 * Θ₁ y.1) * ↑y.2 := by rw [← h]
          _ = _ := by group }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : Θ₁ x.1 * (x.2 : G) = Θ₁ y.1 * (y.2 : G) := congrArg Subtype.val hxy
    have hmem : Θ₁ (y.1⁻¹ * x.1) ∈ Θ₁.range ⊓ C := by
      refine ⟨⟨_, rfl⟩, ?_⟩
      have : Θ₁ (y.1⁻¹ * x.1) = (y.2 : G) * (x.2 : G)⁻¹ := by
        rw [map_mul, map_inv]
        have h' : (Θ₁ y.1)⁻¹ * (Θ₁ x.1 * (x.2 : G)) = (y.2 : G) := by
          rw [h]; group
        calc (Θ₁ y.1)⁻¹ * Θ₁ x.1 = ((Θ₁ y.1)⁻¹ * (Θ₁ x.1 * (x.2 : G))) * (x.2 : G)⁻¹ := by group
          _ = _ := by rw [h']
      rw [this]
      exact C.mul_mem y.2.2 (C.inv_mem x.2.2)
    rw [hdisj, Subgroup.mem_bot] at hmem
    have h1 : y.1⁻¹ * x.1 = 1 := hΘ₁ (by rw [hmem, map_one])
    have hx1 : x.1 = y.1 := by
      have := congrArg (fun z => y.1 * z) h1
      simpa using this
    have h2 : (x.2 : G) = (y.2 : G) := by
      rw [hx1] at h
      exact mul_left_cancel h
    exact Prod.ext hx1 (Subtype.ext h2)
  have hsurj : Function.Surjective f := by
    have hK0 : Θ₁.range ⊔ C ≤ (f.range).map Bs.subtype := by
      refine sup_le ?_ ?_
      · rintro _ ⟨w, rfl⟩
        exact ⟨f (w, 1), ⟨(w, 1), rfl⟩, by change Θ₁ w * 1 = Θ₁ w; simp⟩
      · intro c hc
        exact ⟨f (1, ⟨c, hc⟩), ⟨(1, ⟨c, hc⟩), rfl⟩, by change Θ₁ 1 * c = c; simp⟩
    have hK : Bs ≤ (f.range).map Bs.subtype := by
      rw [hsup] at hK0
      exact hK0
    intro b
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hK b.2
    exact ⟨y, Subtype.ext hy⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun w c => rfl⟩

theorem eq_liftBs_of_apply {G : Type} [Group G] {Bs : Subgroup G} {W W₀ : Type} [Group W]
    [Group W₀] (Θ : (W × W₀) ≃* ↥Bs) (a : MulAut ↥Bs) (σ : MulAut W)
    (h1 : ∀ w, a (Θ (w, 1)) = Θ (σ w, 1)) (h2 : ∀ u, a (Θ (1, u)) = Θ (1, u)) :
    a = liftBs Θ σ := by
  refine MulEquiv.ext fun b => ?_
  obtain ⟨⟨w, u⟩, rfl⟩ := Θ.surjective b
  have hwu : Θ (w, u) = Θ (w, 1) * Θ (1, u) := by
    rw [← map_mul]
    simp
  rw [liftBs_apply, hwu, map_mul, h1, h2, ← map_mul]
  simp

theorem exists_mem_signedAut_of_mem_spSignedGroup (m p : ℕ)
    {g : Equiv.Perm (Fin m → Multiplicative (ZMod p))} (hg : g ∈ spSignedGroup m p) :
    ∃ σ ∈ signedAut m p, MulAut.toPerm (Fin m → Multiplicative (ZMod p)) σ = g := by
  rw [← tbB_signedAut_map_toPerm m p] at hg
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨σ, hσ, rfl⟩

theorem map_liftBs_signedSupportedAut_le {G : Type} [Group G] {Bs : Subgroup G} {p m : ℕ}
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (S : Finset (Fin m)) {A : Subgroup (MulAut ↥Bs)}
    (hs : ∀ i ∈ S, liftBs Θ (sgnAut (p := p) i) ∈ A)
    (hp : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → liftBs Θ (permAut (p := p) (Equiv.swap a b)) ∈ A) :
    (signedSupportedAut m p S).map (liftBs Θ) ≤ A := by
  unfold signedSupportedAut
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, hσ | hσ, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := hσ
    exact hs i hi
  · obtain ⟨a, ha, b, hb, hab, rfl⟩ := hσ
    exact hp a ha b hb hab

theorem exists_prodEquiv_of_frame_centralizer {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) {W : Type} [Group W] (Θ₁ : W →* G)
    (hΘ₁ : Function.Injective Θ₁) (hmem : ∀ w, Θ₁ w ∈ Bs)
    (hdisj : ∀ w, Θ₁ w ∈ Subgroup.centralizer (X : Set G) → w = 1)
    (hact : ∀ b ∈ Bs, ∃ w, ∀ g ∈ X, b * g * b⁻¹ = Θ₁ w * g * (Θ₁ w)⁻¹) :
    ∃ Θ : (W × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs,
      ∀ (w : W) (c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G))),
        ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c := by
  have hle : Θ₁.range ≤ Bs := by
    rintro _ ⟨w, rfl⟩
    exact hmem w
  refine exists_prodEquiv_of_frame hBs Θ₁ hΘ₁ hle _ inf_le_left ?_ ?_
  · refine le_antisymm (sup_le hle inf_le_left) fun b hb => ?_
    obtain ⟨w, hw⟩ := hact b hb
    have hc : (Θ₁ w)⁻¹ * b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
      refine ⟨Bs.mul_mem (Bs.inv_mem (hmem w)) hb, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro g hg
      have h := hw g hg
      calc g * ((Θ₁ w)⁻¹ * b) = (Θ₁ w)⁻¹ * (Θ₁ w * g * (Θ₁ w)⁻¹) * b := by group
        _ = (Θ₁ w)⁻¹ * (b * g * b⁻¹) * b := by rw [h]
        _ = ((Θ₁ w)⁻¹ * b) * g := by group
    have hb' : b = Θ₁ w * ((Θ₁ w)⁻¹ * b) := by group
    rw [hb']
    exact Subgroup.mul_mem_sup ⟨w, rfl⟩ hc
  · refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨w, rfl⟩, -, hc⟩
    rw [hdisj w hc, map_one]
    exact Subgroup.one_mem _

theorem ggAutomizer_eq_map_liftBs {G : Type} [Group G] {p m : ℕ} {Bs X : Subgroup G}
    (Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G)
    (Θ : ((Fin m → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c)
    (hle : ∀ x ∈ X, x ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ σ ∈ spSignedGroup m p, ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (σ v))
    (hge : ∀ i : Fin m, ∃ x ∈ X, x ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (spReflPerm m p i v)) :
    ggAutomizer X Bs = (signedAut m p).map (liftBs Θ) := by
  have key : ∀ x ∈ X, ∀ σ : MulAut (Fin m → Multiplicative (ZMod p)),
      (∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (σ v)) → ∀ b : ↥Bs, ((liftBs Θ σ b : ↥Bs) : G) = x * b * x⁻¹ := by
    intro x hx σ hσ b
    obtain ⟨⟨w, c⟩, rfl⟩ := Θ.surjective b
    rw [liftBs_apply, hΘ, hΘ]
    have hxc : x * (c : G) * x⁻¹ = c := by
      have h := Subgroup.mem_centralizer_iff.mp c.2.2 x hx
      rw [h]
      group
    calc Θ₁ (σ w) * (c : G) = (x * Θ₁ w * x⁻¹) * (x * (c : G) * x⁻¹) := by rw [hσ, hxc]
      _ = x * (Θ₁ w * c) * x⁻¹ := by group
  refine le_antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨x, hx, hxN, hxφ⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨σ, hσ, hσx⟩ := hle x hx hxN
    obtain ⟨σ', hσ', hσ'σ⟩ := exists_mem_signedAut_of_mem_spSignedGroup m p hσ
    have hσσ' : ∀ v, σ' v = σ v := fun v => by rw [← hσ'σ]; rfl
    refine Subgroup.mem_map.mpr ⟨σ', hσ', ?_⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hxφ b]
    exact key x hx σ' (fun v => by rw [hσx v, hσσ' v]) b
  · rw [← tbB_closure_g m p, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxN, hxi⟩ := hge i
    refine mem_ggAutomizer_iff.mpr ⟨x, hx, hxN, key x hx (tbB_g m p i) (fun v => ?_)⟩
    rw [hxi v]
    have h := congrArg (fun e : Equiv.Perm (Fin m → Multiplicative (ZMod p)) => e v)
      (tbB_toPerm_g m p i)
    exact congrArg Θ₁ h.symm

end TypeBDatum

end CFSG.StandardType

end
