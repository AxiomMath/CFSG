module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod
public import CFSG.Quasithin.Background.F918V2F

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Defs

variable {W : Type} [CommGroup W]

@[expose] def s16e_two_cent (X H : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  X ⊓ Subgroup.centralizer (H : Set (MulAut W))

@[expose] def s16e_two_fixIrr (X H : Subgroup (MulAut W)) : Subgroup (MulAut W) where
  carrier := {x | x ∈ X ∧ ∀ I ∈ irrSet H, I.map x.toMonoidHom = I}
  mul_mem' := by
    rintro x y ⟨hxX, hx⟩ ⟨hyX, hy⟩
    refine ⟨mul_mem hxX hyX, fun I hI => ?_⟩
    have h : (x * y).toMonoidHom = x.toMonoidHom.comp y.toMonoidHom := by ext w; rfl
    rw [h, ← Subgroup.map_map, hy I hI, hx I hI]
  one_mem' := by
    refine ⟨one_mem X, fun I _ => ?_⟩
    have h : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext w; rfl
    rw [h, Subgroup.map_id]
  inv_mem' := by
    rintro x ⟨hxX, hx⟩
    refine ⟨inv_mem hxX, fun I hI => ?_⟩
    have h1 : I.map x⁻¹.toMonoidHom = (I.map x.toMonoidHom).map x⁻¹.toMonoidHom := by
      rw [hx I hI]
    rw [h1, Subgroup.map_map]
    have h2 : x⁻¹.toMonoidHom.comp x.toMonoidHom = MonoidHom.id W := by ext w; simp
    rw [h2, Subgroup.map_id]

structure s16e_two_NatFacts (P : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop)
    (H : Subgroup (MulAut W)) : Prop where
  irr : ∀ J, P H J ⊥ → J ∈ irrSet H
  fixV_inf : ∀ J, P H J ⊥ → J ⊓ fixV H = ⊥
  endUnits : ∀ J, P H J ⊥ → Z391.EndUnitsTrivial H J

end Defs

section Action

private lemma s16e_two_isIrr_iff {W : Type} [CommGroup W] (A : Subgroup (MulAut W))
    (J : Subgroup W) : IsIrrOn A J ⊥ ↔ XMod.IsIrr ↥A J := by
  unfold IsIrrOn XMod.IsIrr XMod.IsIrrSec XMod.IsInv StableUnder
  constructor
  · rintro ⟨hlt, hstab, -, hmin⟩
    exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
      fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩
  · rintro ⟨hinv, hlt, hmin⟩
    exact ⟨hlt, (fun a ha u hu => hinv ⟨a, ha⟩ u hu),
      (fun a _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]),
      fun J' hJ' _ hJ'J => hmin J' (fun a u hu => hJ' (a : MulAut W) a.2 u hu) bot_le hJ'J⟩

private theorem s16e_two_commSub_map_conj {W : Type} [CommGroup W] (g : MulAut W)
    (J : Subgroup W) (A : Subgroup (MulAut W)) :
    commSub (J.map g.toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) =
      (commSub J A).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨c₀, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj g).toMonoidHom x, ⟨x, hx, rfl⟩, g w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

private lemma s16e_two_isIrrOn_map {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
    {n : MulAut W} (hn : ∀ a ∈ A, n * a * n⁻¹ ∈ A) (hni : ∀ a ∈ A, n⁻¹ * a * n ∈ A)
    {J : Subgroup W} (hJ : IsIrrOn A J ⊥) : IsIrrOn A (J.map n.toMonoidHom) ⊥ := by
  have hcomp : (n⁻¹).toMonoidHom.comp n.toMonoidHom = MonoidHom.id W := by ext w; simp
  have hcomp' : n.toMonoidHom.comp (n⁻¹).toMonoidHom = MonoidHom.id W := by ext w; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    have h1 : J = ⊥ := by
      have h2 := congrArg (Subgroup.map (n⁻¹).toMonoidHom) h0
      rw [Subgroup.map_map, hcomp, Subgroup.map_id, Subgroup.map_bot] at h2
      exact h2
    exact hJ.1.ne' h1
  · intro a ha u hu
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hu
    have hb : n⁻¹ * a * n ∈ A := hni a ha
    exact Subgroup.mem_map.2
      ⟨(n⁻¹ * a * n) j, hJ.2.1 _ hb j hj, by simp [MulAut.mul_apply]⟩
  · intro a _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro K hK _ hKle
    set K' : Subgroup W := K.map (n⁻¹).toMonoidHom with hK'
    have hK'le : K' ≤ J := by
      have h := Subgroup.map_mono (f := (n⁻¹).toMonoidHom) hKle
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
      rw [hK']
      exact h
    have hK'stab : StableUnder A K' := by
      intro a ha u hu
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
      have hb : n * a * n⁻¹ ∈ A := hn a ha
      exact Subgroup.mem_map.2
        ⟨(n * a * n⁻¹) k, hK _ hb k hk, by simp [MulAut.mul_apply]⟩
    rcases hJ.2.2.2 K' hK'stab bot_le hK'le with h0 | hjeq
    · left
      have h1 := congrArg (Subgroup.map n.toMonoidHom) h0
      rw [hK', Subgroup.map_map, hcomp', Subgroup.map_id, Subgroup.map_bot] at h1
      exact h1
    · right
      have h1 := congrArg (Subgroup.map n.toMonoidHom) hjeq
      rw [hK', Subgroup.map_map, hcomp', Subgroup.map_id] at h1
      exact h1

theorem s16e_two_map_mem_irrSet {W : Type} [CommGroup W] {X L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) {x : MulAut W} (hx : x ∈ X)
    {I : Subgroup W} (hI : I ∈ irrSet L) : I.map x.toMonoidHom ∈ irrSet L := by
  obtain ⟨hIcomm, hIirr⟩ := hI
  rw [F.fix, inf_bot_eq] at hIirr
  unfold irrSet
  change commSub (I.map x.toMonoidHom) L = I.map x.toMonoidHom ∧
    IsIrrOn L (I.map x.toMonoidHom) ((I.map x.toMonoidHom) ⊓ fixV L)
  rw [F.fix, inf_bot_eq]
  refine ⟨?_, ?_⟩
  · rw [← F.norm x hx, s16e_two_commSub_map_conj x I L, hIcomm]
  · have hn : ∀ a ∈ L, x * a * x⁻¹ ∈ L := by
      intro a ha
      have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ha
      rwa [F.norm x hx] at h
    have hni : ∀ a ∈ L, x⁻¹ * a * x ∈ L := by
      intro a ha
      have h := Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom ha
      rwa [F.norm x⁻¹ (X.inv_mem hx)] at h
    exact s16e_two_isIrrOn_map hn hni hIirr

theorem s16e_two_map_injective {W : Type} [CommGroup W] (x : MulAut W) :
    Function.Injective (fun I : Subgroup W => I.map x.toMonoidHom) := by
  intro I I' h
  have h1 := congrArg (Subgroup.map (x⁻¹).toMonoidHom) h
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  have hcomp : (x⁻¹).toMonoidHom.comp x.toMonoidHom = MonoidHom.id W := by ext w; simp
  rwa [hcomp, Subgroup.map_id, Subgroup.map_id] at h1

@[expose] noncomputable def s16e_two_irrActFun {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (x : ↥X) : Equiv.Perm ↥(irrSet L) :=
  Equiv.ofBijective
    (fun I : ↥(irrSet L) =>
      ⟨(I : Subgroup W).map (x : MulAut W).toMonoidHom,
        s16e_two_map_mem_irrSet F x.2 I.2⟩)
    ⟨fun I I' h => Subtype.ext (s16e_two_map_injective (x : MulAut W)
        (Subtype.ext_iff.mp h)),
     fun I' => ⟨⟨(I' : Subgroup W).map (x⁻¹ : MulAut W).toMonoidHom,
        s16e_two_map_mem_irrSet F (X.inv_mem x.2) I'.2⟩, by
       apply Subtype.ext
       show ((I' : Subgroup W).map (x⁻¹ : MulAut W).toMonoidHom).map
           (x : MulAut W).toMonoidHom = (I' : Subgroup W)
       rw [Subgroup.map_map]
       have hcomp : (x : MulAut W).toMonoidHom.comp (x⁻¹ : MulAut W).toMonoidHom =
           MonoidHom.id W := by ext w; simp
       rw [hcomp, Subgroup.map_id]⟩⟩

theorem s16e_two_irrActFun_apply {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (x : ↥X) (I : ↥(irrSet L)) :
    (s16e_two_irrActFun F x I : Subgroup W) =
      (I : Subgroup W).map (x : MulAut W).toMonoidHom :=
  rfl

@[expose] noncomputable def s16e_two_irrAct {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) :
    ↥X →* Equiv.Perm ↥(irrSet L) where
  toFun := s16e_two_irrActFun F
  map_one' := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simp only [s16e_two_irrActFun_apply, Equiv.Perm.one_apply]
    exact Subgroup.map_id _
  map_mul' x y := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simp only [s16e_two_irrActFun_apply, Equiv.Perm.mul_apply]
    rw [Subgroup.map_map]
    congr 1

theorem s16e_two_irrAct_apply {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (x : ↥X) (I : ↥(irrSet L)) :
    (s16e_two_irrAct F x I : Subgroup W) =
      (I : Subgroup W).map (x : MulAut W).toMonoidHom :=
  rfl

theorem s16e_two_isIrrOn_of_mem {W : Type} [CommGroup W] {X L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) {I : Subgroup W}
    (hI : I ∈ irrSet L) : IsIrrOn L I ⊥ := by
  obtain ⟨-, hirr⟩ := hI
  rwa [F.fix, inf_bot_eq] at hirr

theorem s16e_two_isIrr_of_mem {W : Type} [CommGroup W] {X L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) {I : Subgroup W}
    (hI : I ∈ irrSet L) : XMod.IsIrr ↥L I :=
  (s16e_two_isIrr_iff L I).1 (s16e_two_isIrrOn_of_mem F hI)

private def s16e_two_idx {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    (J₀ J₁ I : Subgroup W) : Fin 3 :=
  if I = J₀ then 0 else if I = J₁ then 1 else 2

private lemma s16e_two_idx_eq_zero {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    {J₀ J₁ I : Subgroup W} (h : J₀ ≠ J₁) : s16e_two_idx J₀ J₁ I = 0 ↔ I = J₀ := by
  unfold s16e_two_idx
  split_ifs with h0 h1
  · exact iff_of_true rfl h0
  · exact iff_of_false (by decide) h0
  · exact iff_of_false (by decide) h0

private lemma s16e_two_idx_eq_one {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    {J₀ J₁ I : Subgroup W} (h : J₀ ≠ J₁) : s16e_two_idx J₀ J₁ I = 1 ↔ I = J₁ := by
  unfold s16e_two_idx
  split_ifs with h0 h1
  · exact iff_of_false (by decide) (fun hI => h (h0.symm.trans hI))
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1

private lemma s16e_two_idx_eq_two {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    {J₀ J₁ I : Subgroup W} :
    s16e_two_idx J₀ J₁ I = 2 ↔ I ≠ J₀ ∧ I ≠ J₁ := by
  unfold s16e_two_idx
  split_ifs with h0 h1
  · exact iff_of_false (by decide) (fun hc => hc.1 h0)
  · exact iff_of_false (by decide) (fun hc => hc.2 h1)
  · exact iff_of_true rfl ⟨h0, h1⟩

theorem s16e_two_eq_one_of_fixes {W : Type} [CommGroup W] {X L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    {k : MulAut W} (hk : k ∈ Subgroup.centralizer (L : Set (MulAut W)))
    (hfix₀ : J₀.map k.toMonoidHom = J₀) (hfix₁ : J₁.map k.toMonoidHom = J₁) : k = 1 := by
  have hpt : ∀ (J : Subgroup W) (hJ : J.map k.toMonoidHom = J),
      Z391.EndUnitsTrivial L J → ∀ x ∈ J, k x = x := by
    intro J hJ hE x hx
    let φ : ↥J ≃* ↥J :=
      (MulEquiv.subgroupMap k J).trans (MulEquiv.subgroupCongr hJ)
    have hφval : ∀ y : ↥J, ((φ y : ↥J) : W) = k y := fun y => rfl
    have hφeqv : Z391.V2fEqv ↥L φ := by
      intro l y y' hyy
      show (l : MulAut W) ((φ y : ↥J) : W) = ((φ y' : ↥J) : W)
      rw [hφval y, hφval y']
      have hcomm : k * (l : MulAut W) = (l : MulAut W) * k :=
        ((Subgroup.mem_centralizer_iff.1 hk) l l.2).symm
      have h1 := congrArg (fun f : MulAut W => f y) hcomm
      simp only [MulAut.mul_apply] at h1
      calc (l : MulAut W) (k y) = k ((l : MulAut W) y) := h1.symm
        _ = k y' := by rw [show (l : MulAut W) y = y' from hyy]
    have hφ1 : φ = MulEquiv.refl _ := hE φ hφeqv
    have h2 : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      have := congrArg (fun ψ : ↥J ≃* ↥J => ψ ⟨x, hx⟩) hφ1
      simpa using this
    have h3 := congrArg (fun y : ↥J => (y : W)) h2
    rw [hφval ⟨x, hx⟩] at h3
    simpa using h3
  have h₀ : ∀ x ∈ J₀, k x = x := hpt J₀ hfix₀ hE₀
  have h₁ : ∀ x ∈ J₁, k x = x := hpt J₁ hfix₁ hE₁
  ext w
  have hw : w ∈ J₀ ⊔ J₁ := by rw [F.sup_eq]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul, h₀ a ha, h₁ b hb]
  rfl

theorem s16e_two_irrAct_cent_injective {W : Type} [CommGroup W] {X H : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁) :
    Function.Injective ((s16e_two_irrAct F).comp
      (Subgroup.inclusion (inf_le_left : s16e_two_cent X H ≤ X))) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hk' : s16e_two_irrAct F (Subgroup.inclusion inf_le_left k) = 1 := hk
  have hcoe : ((Subgroup.inclusion inf_le_left k : ↥X) : MulAut W) = (k : MulAut W) :=
    Subgroup.coe_inclusion _ k
  apply Subtype.ext
  refine s16e_two_eq_one_of_fixes F hE₀ hE₁ (Subgroup.mem_inf.1 k.2).2 ?_ ?_
  · have h1 := congrArg (fun σ : Equiv.Perm ↥(irrSet H) => (σ ⟨J₀, F.irr₀⟩ : Subgroup W)) hk'
    simp only [Equiv.Perm.one_apply, s16e_two_irrAct_apply, hcoe] at h1
    exact h1
  · have h1 := congrArg (fun σ : Equiv.Perm ↥(irrSet H) => (σ ⟨J₁, F.irr₁⟩ : Subgroup W)) hk'
    simp only [Equiv.Perm.one_apply, s16e_two_irrAct_apply, hcoe] at h1
    exact h1

end Action

section Conj

variable {W : Type} [CommGroup W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}

@[expose] def s16e_two_conjAut (F : Cfg2Setting X H J₀ J₁) : ↥X →* MulAut ↥H where
  toFun x := (MulEquiv.subgroupMap (MulAut.conj (x : MulAut W)) H).trans
    (MulEquiv.subgroupCongr (F.norm x x.2))
  map_one' := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    change (1 : MulAut W) * (h : MulAut W) * (1 : MulAut W)⁻¹ = (h : MulAut W)
    group
  map_mul' x y := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    change (x : MulAut W) * (y : MulAut W) * (h : MulAut W) * ((x : MulAut W) * (y : MulAut W))⁻¹ =
      (x : MulAut W) * ((y : MulAut W) * (h : MulAut W) * (y : MulAut W)⁻¹) * (x : MulAut W)⁻¹
    group

theorem s16e_two_conjAut_apply (F : Cfg2Setting X H J₀ J₁) (x : ↥X) (h : ↥H) :
    ((s16e_two_conjAut F x h : ↥H) : MulAut W) =
      (x : MulAut W) * (h : MulAut W) * (x : MulAut W)⁻¹ :=
  rfl

theorem s16e_two_conjAut_ker (F : Cfg2Setting X H J₀ J₁) :
    (s16e_two_conjAut F).ker = (s16e_two_cent X H).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have h1 := congrArg (fun z : ↥H => (z : MulAut W)) (DFunLike.congr_fun hx ⟨h, hh⟩)
    simp only [s16e_two_conjAut_apply, MulAut.one_apply] at h1
    calc h * (x : MulAut W) = (x : MulAut W) * h * (x : MulAut W)⁻¹ * (x : MulAut W) := by
          rw [h1]
      _ = (x : MulAut W) * h := by group
  · rintro ⟨-, hx⟩
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have h1 := Subgroup.mem_centralizer_iff.1 hx (h : MulAut W) h.2
    change (x : MulAut W) * (h : MulAut W) * (x : MulAut W)⁻¹ = (h : MulAut W)
    rw [mul_inv_eq_iff_eq_mul, ← h1]

end Conj

theorem s16e_two_mem_sup_of_commute {Γ : Type*} [Group Γ] {K N : Subgroup Γ}
    (hcomm : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k) {x : Γ} (hx : x ∈ K ⊔ N) :
    ∃ k ∈ K, ∃ n ∈ N, x = k * n := by
  let S : Subgroup Γ :=
    { carrier := {y | ∃ k ∈ K, ∃ n ∈ N, y = k * n}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, n₁, hn₁, rfl⟩ ⟨k₂, hk₂, n₂, hn₂, rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, n₁ * n₂, N.mul_mem hn₁ hn₂, ?_⟩
        calc k₁ * n₁ * (k₂ * n₂) = k₁ * (n₁ * k₂) * n₂ := by group
          _ = k₁ * (k₂ * n₁) * n₂ := by rw [hcomm k₂ hk₂ n₁ hn₁]
          _ = k₁ * k₂ * (n₁ * n₂) := by group
      one_mem' := ⟨1, K.one_mem, 1, N.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨k, hk, n, hn, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, n⁻¹, N.inv_mem hn, ?_⟩
        calc (k * n)⁻¹ = n⁻¹ * k⁻¹ := mul_inv_rev k n
          _ = k⁻¹ * n⁻¹ := (hcomm k⁻¹ (K.inv_mem hk) n⁻¹ (N.inv_mem hn)).symm }
  have hle : K ⊔ N ≤ S :=
    sup_le (fun k hk => ⟨k, hk, 1, N.one_mem, (mul_one k).symm⟩)
      (fun n hn => ⟨1, K.one_mem, n, hn, (one_mul n).symm⟩)
  exact hle hx

section Counting

variable {W : Type} [CommGroup W] [Finite W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}

theorem s16e_two_irrSet_card_le_three (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) : Nat.card ↥(irrSet H) ≤ 3 := by
  classical
  have hJ₀ne : J₀ ≠ ⊥ := by
    obtain ⟨-, hirr⟩ := F.irr₀
    rw [F.fix, inf_bot_eq] at hirr
    exact hirr.1.ne'
  have hJ01 : J₀ ≠ J₁ := by
    intro h
    have h1 : J₀ ⊓ J₁ = J₀ := by rw [h, inf_idem]
    rw [F.inf_eq] at h1
    exact hJ₀ne h1.symm
  have hg_inj : Function.Injective
      (fun I : ↥(irrSet H) => s16e_two_idx J₀ J₁ (I : Subgroup W)) := by
    intro I I' h
    have h' : s16e_two_idx J₀ J₁ (I : Subgroup W) = s16e_two_idx J₀ J₁ (I' : Subgroup W) := h
    have hcases : s16e_two_idx J₀ J₁ (I : Subgroup W) = 0 ∨
        s16e_two_idx J₀ J₁ (I : Subgroup W) = 1 ∨ s16e_two_idx J₀ J₁ (I : Subgroup W) = 2 := by
      generalize hz : s16e_two_idx J₀ J₁ (I : Subgroup W) = z
      fin_cases z <;> simp_all
    rcases hcases with h0 | h1 | h2
    · have hI : (I : Subgroup W) = J₀ := (s16e_two_idx_eq_zero hJ01).1 h0
      have hI' : (I' : Subgroup W) = J₀ := (s16e_two_idx_eq_zero hJ01).1 (h' ▸ h0)
      exact Subtype.ext (hI.trans hI'.symm)
    · have hI : (I : Subgroup W) = J₁ := (s16e_two_idx_eq_one hJ01).1 h1
      have hI' : (I' : Subgroup W) = J₁ := (s16e_two_idx_eq_one hJ01).1 (h' ▸ h1)
      exact Subtype.ext (hI.trans hI'.symm)
    · have hI : (I : Subgroup W) ≠ J₀ ∧ (I : Subgroup W) ≠ J₁ := s16e_two_idx_eq_two.1 h2
      have hI' : (I' : Subgroup W) ≠ J₀ ∧ (I' : Subgroup W) ≠ J₁ :=
        s16e_two_idx_eq_two.1 (h' ▸ h2)
      have hle : (I : Subgroup W) ≤ J₀ ⊔ J₁ := F.sup_eq.symm ▸ le_top
      have hle' : (I' : Subgroup W) ≤ J₀ ⊔ J₁ := F.sup_eq.symm ▸ le_top
      exact Subtype.ext
        (Z391.v2f_eq_of_le_sup (A := ↥H) (P := J₀) (P' := J₁) (R := (I : Subgroup W))
          (R' := (I' : Subgroup W)) (s16e_two_isIrr_of_mem F F.irr₀)
          (s16e_two_isIrr_of_mem F F.irr₁) hE₀ (s16e_two_isIrr_of_mem F I.2)
          (s16e_two_isIrr_of_mem F I'.2) hle hle' hI.1 hI.2 hI'.1 hI'.2)
  exact (Nat.card_le_card_of_injective _ hg_inj).trans (by simp)

theorem s16e_two_card_cent_dvd_six (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁) :
    Nat.card ↥(s16e_two_cent X H) ∣ 6 := by
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite ↥(irrSet H) := Finite.of_injective _ Subtype.coe_injective
  have h1 : Nat.card ↥(s16e_two_cent X H) ∣ Nat.card (Equiv.Perm ↥(irrSet H)) :=
    Subgroup.card_dvd_of_injective _ (s16e_two_irrAct_cent_injective F hE₀ hE₁)
  rw [Nat.card_perm] at h1
  refine h1.trans ?_
  have h2 := Nat.factorial_dvd_factorial (s16e_two_irrSet_card_le_three F hE₀)
  have h3 : Nat.factorial 3 = 6 := by norm_num
  rw [h3] at h2
  exact h2

theorem s16e_two_card_dvd_mul_aut (F : Cfg2Setting X H J₀ J₁) :
    Nat.card ↥X ∣ Nat.card ↥(s16e_two_cent X H) * Nat.card (MulAut ↥H) := by
  have hker : Nat.card ↥((s16e_two_conjAut F).ker) = Nat.card ↥(s16e_two_cent X H) := by
    rw [s16e_two_conjAut_ker F]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : s16e_two_cent X H ≤ X)).toEquiv
  have hX : Nat.card ↥X = Nat.card ↥(s16e_two_cent X H) *
      Nat.card ↥((s16e_two_conjAut F).range) := by
    rw [← hker]
    exact (Subgroup.card_ker_mul_card_range (s16e_two_conjAut F)).symm
  rw [hX]
  exact mul_dvd_mul_left _ (Subgroup.card_subgroup_dvd_card (s16e_two_conjAut F).range)

theorem s16e_two_isSym_of_card_six (F : Cfg2Setting X H J₀ J₁)
    (hE₀ : Z391.EndUnitsTrivial H J₀) (hE₁ : Z391.EndUnitsTrivial H J₁)
    (h6 : Nat.card ↥(s16e_two_cent X H) = 6) : IsSym ↥(s16e_two_cent X H) 3 := by
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite ↥(irrSet H) := Finite.of_injective _ Subtype.coe_injective
  let f : ↥(s16e_two_cent X H) →* Equiv.Perm ↥(irrSet H) :=
    (s16e_two_irrAct F).comp (Subgroup.inclusion (inf_le_left : s16e_two_cent X H ≤ X))
  have hf : Function.Injective f := s16e_two_irrAct_cent_injective F hE₀ hE₁
  have hdiv : 6 ∣ Nat.factorial (Nat.card ↥(irrSet H)) := by
    have h1 := Subgroup.card_dvd_of_injective f hf
    rw [h6, Nat.card_perm] at h1
    exact h1
  have hnle : Nat.card ↥(irrSet H) ≤ 3 := s16e_two_irrSet_card_le_three F hE₀
  have hfac : Nat.factorial (Nat.card ↥(irrSet H)) = 6 := by
    have h2 := Nat.factorial_dvd_factorial hnle
    have h3 : Nat.factorial 3 = 6 := by norm_num
    rw [h3] at h2
    exact Nat.dvd_antisymm h2 hdiv
  have hn3 : Nat.card ↥(irrSet H) = 3 := by
    interval_cases (Nat.card ↥(irrSet H)) <;> simp_all
  have hcard : Nat.card (Equiv.Perm ↥(irrSet H)) = Nat.card ↥(s16e_two_cent X H) := by
    rw [Nat.card_perm, hfac, h6]
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (le_of_eq hcard)
  exact ⟨(MulEquiv.ofBijective f hbij).trans (Finite.equivFinOfCardEq hn3).permCongrHom⟩

theorem s16e_two_rk_irr_ge (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀)
    {m : ℕ} (h₀ : m ≤ rk ↥J₀) (h₁ : m ≤ rk ↥J₁) : ∀ I ∈ irrSet H, m ≤ rk ↥I := by
  intro I hI
  by_cases hI0 : I = J₀
  · rwa [hI0]
  by_cases hI1 : I = J₁
  · rwa [hI1]
  have hIrr₀ : XMod.IsIrr ↥H J₀ := s16e_two_isIrr_of_mem F F.irr₀
  have hIrr₁ : XMod.IsIrr ↥H J₁ := s16e_two_isIrr_of_mem F F.irr₁
  have hIrrI : XMod.IsIrr ↥H I := s16e_two_isIrr_of_mem F hI
  have hIle : I ≤ J₀ ⊔ J₁ := F.sup_eq.symm ▸ le_top
  have hI₀ : I ⊓ J₀ = ⊥ := Z391.v2f_inf_eq_bot hIrrI hIrr₀ hI0
  have hI₁ : I ⊓ J₁ = ⊥ := Z391.v2f_inf_eq_bot hIrrI hIrr₁ hI1
  obtain ⟨θ, -, hθ⟩ :=
    Z391.v2f_exists_graph hIrr₀ hIrr₁ hIrrI.1 hIrrI.2.1.ne' hIle hI₀ hI₁
  have hψmem : ∀ x : ↥J₀, (x : W) * (θ x : W) ∈ I := fun x => (hθ x (θ x)).2 rfl
  let ψ : ↥J₀ →* ↥I :=
    { toFun := fun x => ⟨(x : W) * (θ x : W), hψmem x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x : W) * (y : W) * (θ (x * y) : W) =
          ((x : W) * (θ x : W)) * ((y : W) * (θ y : W))
        rw [map_mul]
        ac_rfl }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : W) * (θ x : W) = (y : W) * (θ y : W) := congrArg Subtype.val hxy
    have h2 : (y : W)⁻¹ * (x : W) = (θ y : W) * (θ x : W)⁻¹ := by
      calc (y : W)⁻¹ * (x : W) =
            (y : W)⁻¹ * ((x : W) * (θ x : W)) * (θ x : W)⁻¹ := by group
        _ = (y : W)⁻¹ * ((y : W) * (θ y : W)) * (θ x : W)⁻¹ := by rw [h1]
        _ = (θ y : W) * (θ x : W)⁻¹ := by group
    have h3 : (x : W) * (y : W)⁻¹ = (θ y : W) * (θ x : W)⁻¹ := by
      rw [mul_comm]
      exact h2
    have hxyJ₀ : (x : W) * (y : W)⁻¹ ∈ J₀ := J₀.mul_mem x.2 (J₀.inv_mem y.2)
    have hxyJ₁ : (x : W) * (y : W)⁻¹ ∈ J₁ := by
      have hinv : ((x : W) * (y : W)⁻¹)⁻¹ ∈ J₁ := by
        have h4 : ((x : W) * (y : W)⁻¹)⁻¹ = (θ x : W) * (θ y : W)⁻¹ := by
          rw [h3]
          group
        rw [h4]
        exact J₁.mul_mem (θ x).2 (J₁.inv_mem (θ y).2)
      simpa using J₁.inv_mem hinv
    have hbot : (x : W) * (y : W)⁻¹ ∈ (⊥ : Subgroup W) := by
      rw [← F.inf_eq]
      exact Subgroup.mem_inf.2 ⟨hxyJ₀, hxyJ₁⟩
    exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))
  have hψsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hIle k.2)
    have hk : (a : W) * (b : W) ∈ I := hab ▸ k.2
    have hθa : θ ⟨a, ha⟩ = ⟨b, hb⟩ := (hθ ⟨a, ha⟩ ⟨b, hb⟩).1 hk
    exact ⟨⟨a, ha⟩, Subtype.ext (by
      show (a : W) * (θ ⟨a, ha⟩ : W) = (k : W)
      rw [hθa]
      exact hab)⟩
  have hcard : Nat.card ↥I = Nat.card ↥J₀ :=
    (Nat.card_congr (Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩)).symm
  have hrk : rk ↥I = rk ↥J₀ := by
    unfold rk
    rw [hcard]
  rw [hrk]
  exact h₀

theorem s16e_two_rk_comm_of_moves (F : Cfg2Setting X H J₀ J₁) {t : MulAut W} (htX : t ∈ X)
    {I : Subgroup W} (hI : I ∈ irrSet H) (hmove : I.map t.toMonoidHom ≠ I) :
    rk ↥I ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  have hstabI : StableUnder H I := (s16e_two_isIrrOn_of_mem F hI).2.1
  have hDstab : StableUnder H (I ⊓ I.map t.toMonoidHom) := by
    intro h hh u hu
    obtain ⟨huI, huMap⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨i, hiI, hti⟩ := Subgroup.mem_map.1 huMap
    refine Subgroup.mem_inf.2 ⟨hstabI h hh u huI, ?_⟩
    have hmem : (t⁻¹ * h * t) ∈ H := by
      have h1 : (MulAut.conj t⁻¹) h ∈ H := by
        have h2 := Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hh
        rwa [F.norm t⁻¹ (X.inv_mem htX)] at h2
      simpa [MulAut.conj_apply] using h1
    refine Subgroup.mem_map.2 ⟨(t⁻¹ * h * t) i, hstabI _ hmem i hiI, ?_⟩
    rw [← hti]
    show t ((t⁻¹ * h * t) i) = h (t i)
    simp [MulAut.mul_apply]
  rcases (s16e_two_isIrrOn_of_mem F hI).2.2.2 (I ⊓ I.map t.toMonoidHom) hDstab bot_le
    inf_le_left with hD | hD
  · have h := s16c167_rk_le_rkIdx_of_inf_map_eq_bot t hD
    rwa [rkIdx_fixV_zpowers, commV_eq_commSub] at h
  · exfalso
    have hle : I ≤ I.map t.toMonoidHom := inf_eq_left.mp hD
    have hcard : Nat.card ↥(I.map t.toMonoidHom) = Nat.card ↥I :=
      Subgroup.card_map_of_injective (MulEquiv.injective t)
    exact hmove (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

theorem s16e_two_rk_comm_ge (F : Cfg2Setting X H J₀ J₁) {h : MulAut W} (hh : h ∈ H) {m₀ m₁ : ℕ}
    (h₀ : m₀ ≤ rk ↥(commSub J₀ (Subgroup.zpowers h)))
    (h₁ : m₁ ≤ rk ↥(commSub J₁ (Subgroup.zpowers h))) :
    m₀ + m₁ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)) := by
  have hzh : Subgroup.zpowers h ≤ H := Subgroup.zpowers_le_of_mem hh
  have hA₀ : commSub J₀ (Subgroup.zpowers h) ≤ J₀ :=
    commSub_le_of_invariant fun x hx w hw =>
      (s16e_two_isIrrOn_of_mem F F.irr₀).2.1 x (hzh hx) w hw
  have hA₁ : commSub J₁ (Subgroup.zpowers h) ≤ J₁ :=
    commSub_le_of_invariant fun x hx w hw =>
      (s16e_two_isIrrOn_of_mem F F.irr₁).2.1 x (hzh hx) w hw
  have hAinf : commSub J₀ (Subgroup.zpowers h) ⊓ commSub J₁ (Subgroup.zpowers h) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← F.inf_eq]
    exact inf_le_inf hA₀ hA₁
  have hsup : commSub J₀ (Subgroup.zpowers h) ⊔ commSub J₁ (Subgroup.zpowers h) ≤
      commSub ⊤ (Subgroup.zpowers h) :=
    sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl)
  have hsum : rk ↥(commSub J₀ (Subgroup.zpowers h)) +
      rk ↥(commSub J₁ (Subgroup.zpowers h)) =
      rk ↥(commSub J₀ (Subgroup.zpowers h) ⊔ commSub J₁ (Subgroup.zpowers h)) := by
    have h := rk_sup_add_rk_inf (commSub J₀ (Subgroup.zpowers h))
      (commSub J₁ (Subgroup.zpowers h))
    rw [hAinf, rk_bot] at h
    omega
  calc m₀ + m₁ ≤ rk ↥(commSub J₀ (Subgroup.zpowers h)) +
        rk ↥(commSub J₁ (Subgroup.zpowers h)) := add_le_add h₀ h₁
    _ = rk ↥(commSub J₀ (Subgroup.zpowers h) ⊔ commSub J₁ (Subgroup.zpowers h)) := hsum
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)) := rk_mono hsup

end Counting

theorem s16e_two_three_dvd_of_cube {a b c : ℕ} (hX : 3 ^ 3 ∣ a) (hab : a ∣ b * c)
    (hc : ¬ 3 ^ 3 ∣ c) : 3 ∣ b := by
  by_contra hb
  have hcop : Nat.Coprime (3 ^ 3) b :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb)
  exact hc (hcop.dvd_of_dvd_mul_left (hX.trans hab))

section Transport

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]

theorem s16e_two_isSym_transport {X₁ K₁ : Subgroup Γ₁} {X₂ K₂ : Subgroup Γ₂} (ρ : ↥X₁ ≃* ↥X₂)
    (hK₁ : K₁ ≤ X₁) (hK₂ : K₂ ≤ X₂)
    (hK : (K₁.subgroupOf X₁).map ρ.toMonoidHom = K₂.subgroupOf X₂) {n : ℕ} (h : IsSym ↥K₂ n) :
    IsSym ↥K₁ n := by
  obtain ⟨e⟩ := h
  exact ⟨(((Subgroup.subgroupOfEquivOfLe hK₁).symm.trans
    (MulEquiv.subgroupMap ρ (K₁.subgroupOf X₁))).trans
    ((MulEquiv.subgroupCongr hK).trans (Subgroup.subgroupOfEquivOfLe hK₂))).trans e⟩

private theorem s16e_twoA_isInternalDirect_map_iff {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    {f : Γ₁ →* Γ₂} (hf : Function.Injective f) (U V X : Subgroup Γ₁) :
    IsInternalDirect (U.map f) (V.map f) (X.map f) ↔ IsInternalDirect U V X := by
  have h1 : ((U.map f) ⊔ (V.map f) = X.map f) ↔ (U ⊔ V = X) := by
    rw [← Subgroup.map_sup U V f]
    exact (Subgroup.map_injective hf).eq_iff
  have h2 : ((U.map f) ⊓ (V.map f) = ⊥) ↔ (U ⊓ V = ⊥) := by
    rw [← Subgroup.map_inf_eq U V f hf]
    exact ⟨fun h => Subgroup.map_injective hf (by rw [h, Subgroup.map_bot]),
      fun h => by rw [h, Subgroup.map_bot]⟩
  have h3 : (⁅U.map f, V.map f⁆ = ⊥) ↔ (⁅U, V⁆ = ⊥) := by
    rw [← Subgroup.map_commutator U V f]
    exact ⟨fun h => Subgroup.map_injective hf (by rw [h, Subgroup.map_bot]),
      fun h => by rw [h, Subgroup.map_bot]⟩
  unfold IsInternalDirect
  exact and_congr h3 (and_congr h2 h1)

private theorem s16e_twoA_subgroupOf_iff {Γ : Type} [Group Γ] {K L X : Subgroup Γ}
    (hK : K ≤ X) (hL : L ≤ X) :
    IsInternalDirect K L X ↔ IsInternalDirect (K.subgroupOf X) (L.subgroupOf X) ⊤ := by
  have h := s16e_twoA_isInternalDirect_map_iff X.subtype_injective (K.subgroupOf X)
    (L.subgroupOf X) ⊤
  rw [Subgroup.map_subgroupOf_eq_of_le hK, Subgroup.map_subgroupOf_eq_of_le hL,
    Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

private theorem s16e_twoA_direct_of_maps {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂]
    {X₁ K₁ H₁ : Subgroup Γ₁} {X₂ K₂ H₂ : Subgroup Γ₂} (ρ : ↥X₁ ≃* ↥X₂)
    (hK₁ : K₁ ≤ X₁) (hH₁ : H₁ ≤ X₁)
    (hK : (K₁.subgroupOf X₁).map ρ.toMonoidHom = K₂.subgroupOf X₂)
    (hH : (H₁.subgroupOf X₁).map ρ.toMonoidHom = H₂.subgroupOf X₂)
    (hdir : IsInternalDirect K₂ H₂ X₂) : IsInternalDirect K₁ H₁ X₁ := by
  have hK₂ : K₂ ≤ X₂ := hdir.2.2 ▸ le_sup_left
  have hH₂ : H₂ ≤ X₂ := hdir.2.2 ▸ le_sup_right
  have h1 : IsInternalDirect (K₂.subgroupOf X₂) (H₂.subgroupOf X₂) ⊤ :=
    (s16e_twoA_subgroupOf_iff hK₂ hH₂).1 hdir
  have h2 : IsInternalDirect ((K₁.subgroupOf X₁).map ρ.toMonoidHom)
      ((H₁.subgroupOf X₁).map ρ.toMonoidHom) ((⊤ : Subgroup ↥X₁).map ρ.toMonoidHom) := by
    rw [Subgroup.map_top_of_surjective ρ.toMonoidHom ρ.surjective, hK, hH]
    exact h1
  exact (s16e_twoA_subgroupOf_iff hK₁ hH₁).2
    ((s16e_twoA_isInternalDirect_map_iff ρ.injective (K₁.subgroupOf X₁)
      (H₁.subgroupOf X₁) ⊤).1 h2)

theorem s16e_two_direct_transport {X₁ K₁ : Subgroup Γ₁} {X₂ K₂ N₂ : Subgroup Γ₂}
    (ρ : ↥X₁ ≃* ↥X₂) (hK₁ : K₁ ≤ X₁)
    (hK : (K₁.subgroupOf X₁).map ρ.toMonoidHom = K₂.subgroupOf X₂)
    (hdir : IsInternalDirect K₂ N₂ X₂) :
    ∃ L₁ : Subgroup Γ₁, IsInternalDirect K₁ L₁ X₁ ∧ Nonempty (↥L₁ ≃* ↥N₂) := by
  have hN₂ : N₂ ≤ X₂ := hdir.2.2 ▸ le_sup_right
  let L₁ : Subgroup Γ₁ := ((N₂.subgroupOf X₂).map ρ.symm.toMonoidHom).map X₁.subtype
  have hL₁ : L₁ ≤ X₁ :=
    Subgroup.map_subtype_le ((N₂.subgroupOf X₂).map ρ.symm.toMonoidHom)
  have hL₁sub : L₁.subgroupOf X₁ = (N₂.subgroupOf X₂).map ρ.symm.toMonoidHom := by
    show (((N₂.subgroupOf X₂).map ρ.symm.toMonoidHom).map X₁.subtype).subgroupOf X₁ = _
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective X₁.subtype_injective]
  have hH : (L₁.subgroupOf X₁).map ρ.toMonoidHom = N₂.subgroupOf X₂ := by
    rw [hL₁sub, Subgroup.map_map]
    have hcomp : ρ.toMonoidHom.comp ρ.symm.toMonoidHom = MonoidHom.id ↥X₂ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  refine ⟨L₁, s16e_twoA_direct_of_maps ρ hK₁ hL₁ hK hH hdir, ?_⟩
  exact ⟨((Subgroup.subgroupOfEquivOfLe hL₁).symm.trans
    (MulEquiv.subgroupMap ρ (L₁.subgroupOf X₁))).trans
    ((MulEquiv.subgroupCongr hH).trans (Subgroup.subgroupOfEquivOfLe hN₂))⟩

theorem s16e_two_direct_transport_eq {X₁ K₁ H₁ : Subgroup Γ₁} {X₂ K₂ H₂ : Subgroup Γ₂}
    (ρ : ↥X₁ ≃* ↥X₂) (hK₁ : K₁ ≤ X₁) (hH₁ : H₁ ≤ X₁)
    (hK : (K₁.subgroupOf X₁).map ρ.toMonoidHom = K₂.subgroupOf X₂)
    (hH : (H₁.subgroupOf X₁).map ρ.toMonoidHom = H₂.subgroupOf X₂)
    (hdir : IsInternalDirect K₂ H₂ X₂) : IsInternalDirect K₁ H₁ X₁ := by
  exact s16e_twoA_direct_of_maps ρ hK₁ hH₁ hK hH hdir

private lemma s16e_twoA_cent_subgroupOf {Γ : Type} [Group Γ] {X H : Subgroup Γ} (hH : H ≤ X) :
    (X ⊓ Subgroup.centralizer (H : Set Γ)).subgroupOf X =
      Subgroup.centralizer ((H.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hc⟩ h hh
    exact Subtype.ext (hc (h : Γ) hh)
  · intro hc
    exact ⟨x.2, fun h hh => congrArg Subtype.val (hc ⟨h, hH hh⟩ hh)⟩

theorem s16e_two_map_cent {X₁ H₁ : Subgroup Γ₁} {X₂ H₂ : Subgroup Γ₂} (ρ : ↥X₁ ≃* ↥X₂)
    (hH₁ : H₁ ≤ X₁) (hH₂ : H₂ ≤ X₂)
    (hH : (H₁.subgroupOf X₁).map ρ.toMonoidHom = H₂.subgroupOf X₂) :
    ((X₁ ⊓ Subgroup.centralizer (H₁ : Set Γ₁)).subgroupOf X₁).map ρ.toMonoidHom =
      (X₂ ⊓ Subgroup.centralizer (H₂ : Set Γ₂)).subgroupOf X₂ := by
  rw [s16e_twoA_cent_subgroupOf hH₁, s16e_twoA_cent_subgroupOf hH₂]
  ext x₂
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx₁ h₂ hh₂
    have hw : ρ.symm h₂ ∈ H₁.subgroupOf X₁ :=
      Subgroup.mem_map_equiv.mp (hH.symm ▸ hh₂)
    have h4 := congrArg (fun z => ρ z) (hx₁ (ρ.symm h₂) hw)
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h4
  · intro hx₂ w hw
    have hw₂ : ρ w ∈ H₂.subgroupOf X₂ := hH ▸ Subgroup.mem_map_of_mem ρ.toMonoidHom hw
    have h4 := congrArg (fun z => ρ.symm z) (hx₂ (ρ w) hw₂)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using h4

end Transport

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
