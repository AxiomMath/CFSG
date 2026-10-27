module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Frame
public import CFSG.Quasithin.Background.F918V2F
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s16c167_isIrr_iff {W : Type} [CommGroup W] (A : Subgroup (MulAut W))
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

private theorem s16c167_commSub_map_conj {W : Type} [CommGroup W] (g : MulAut W)
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

private lemma s16c167_isIrrOn_map {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
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

private lemma s16c167_map_mem_irrSet {W : Type} [CommGroup W] {X L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) {x : MulAut W} (hx : x ∈ X)
    {I : Subgroup W} (hI : I ∈ irrSet L) : I.map x.toMonoidHom ∈ irrSet L := by
  obtain ⟨hIcomm, hIirr⟩ := hI
  rw [F.fix, inf_bot_eq] at hIirr
  unfold irrSet
  change commSub (I.map x.toMonoidHom) L = I.map x.toMonoidHom ∧
    IsIrrOn L (I.map x.toMonoidHom) ((I.map x.toMonoidHom) ⊓ fixV L)
  rw [F.fix, inf_bot_eq]
  refine ⟨?_, ?_⟩
  · rw [← F.norm x hx, s16c167_commSub_map_conj x I L, hIcomm]
  · have hn : ∀ a ∈ L, x * a * x⁻¹ ∈ L := by
      intro a ha
      have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ha
      rwa [F.norm x hx] at h
    have hni : ∀ a ∈ L, x⁻¹ * a * x ∈ L := by
      intro a ha
      have h := Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom ha
      rwa [F.norm x⁻¹ (X.inv_mem hx)] at h
    exact s16c167_isIrrOn_map hn hni hIirr

private lemma s16c167_map_injective {W : Type} [CommGroup W] (x : MulAut W) :
    Function.Injective (fun I : Subgroup W => I.map x.toMonoidHom) := by
  intro I I' h
  have h1 := congrArg (Subgroup.map (x⁻¹).toMonoidHom) h
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  have hcomp : (x⁻¹).toMonoidHom.comp x.toMonoidHom = MonoidHom.id W := by ext w; simp
  rwa [hcomp, Subgroup.map_id, Subgroup.map_id] at h1

private noncomputable def s16c167_irrSetActFun {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (x : ↥X) : Equiv.Perm ↥(irrSet L) :=
  Equiv.ofBijective
    (fun I : ↥(irrSet L) =>
      ⟨(I : Subgroup W).map (x : MulAut W).toMonoidHom,
        s16c167_map_mem_irrSet F x.2 I.2⟩)
    ⟨fun I I' h => Subtype.ext (s16c167_map_injective (x : MulAut W)
        (Subtype.ext_iff.mp h)),
     fun I' => ⟨⟨(I' : Subgroup W).map (x⁻¹ : MulAut W).toMonoidHom,
        s16c167_map_mem_irrSet F (X.inv_mem x.2) I'.2⟩, by
       apply Subtype.ext
       show ((I' : Subgroup W).map (x⁻¹ : MulAut W).toMonoidHom).map
           (x : MulAut W).toMonoidHom = (I' : Subgroup W)
       rw [Subgroup.map_map]
       have hcomp : (x : MulAut W).toMonoidHom.comp (x⁻¹ : MulAut W).toMonoidHom =
           MonoidHom.id W := by ext w; simp
       rw [hcomp, Subgroup.map_id]⟩⟩

private lemma s16c167_irrSetActFun_apply {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (x : ↥X) (I : ↥(irrSet L)) :
    (s16c167_irrSetActFun F x I : Subgroup W) =
      (I : Subgroup W).map (x : MulAut W).toMonoidHom :=
  rfl

private noncomputable def s16c167_irrSetAct {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) :
    ↥X →* Equiv.Perm ↥(irrSet L) where
  toFun := s16c167_irrSetActFun F
  map_one' := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simp only [s16c167_irrSetActFun_apply, Equiv.Perm.one_apply]
    exact Subgroup.map_id _
  map_mul' x y := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simp only [s16c167_irrSetActFun_apply, Equiv.Perm.mul_apply]
    rw [Subgroup.map_map]
    congr 1

private lemma s16c167_irrSetAct_apply {W : Type} [CommGroup W]
    {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (x : ↥X) (I : ↥(irrSet L)) :
    (s16c167_irrSetAct F x I : Subgroup W) =
      (I : Subgroup W).map (x : MulAut W).toMonoidHom :=
  rfl

private lemma s16c167_isIrrOn_of_mem {W : Type} [CommGroup W] {X L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) {I : Subgroup W}
    (hI : I ∈ irrSet L) : IsIrrOn L I ⊥ := by
  obtain ⟨-, hirr⟩ := hI
  rwa [F.fix, inf_bot_eq] at hirr

private def s16c167_idx {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    (J₀ J₁ I : Subgroup W) : Fin 3 :=
  if I = J₀ then 0 else if I = J₁ then 1 else 2

private lemma s16c167_idx_eq_zero {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    {J₀ J₁ I : Subgroup W} (h : J₀ ≠ J₁) : s16c167_idx J₀ J₁ I = 0 ↔ I = J₀ := by
  unfold s16c167_idx
  split_ifs with h0 h1
  · exact iff_of_true rfl h0
  · exact iff_of_false (by decide) h0
  · exact iff_of_false (by decide) h0

private lemma s16c167_idx_eq_one {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    {J₀ J₁ I : Subgroup W} (h : J₀ ≠ J₁) : s16c167_idx J₀ J₁ I = 1 ↔ I = J₁ := by
  unfold s16c167_idx
  split_ifs with h0 h1
  · exact iff_of_false (by decide) (fun hI => h (h0.symm.trans hI))
  · exact iff_of_true rfl h1
  · exact iff_of_false (by decide) h1

private lemma s16c167_idx_eq_two {W : Type} [CommGroup W] [DecidableEq (Subgroup W)]
    {J₀ J₁ I : Subgroup W} :
    s16c167_idx J₀ J₁ I = 2 ↔ I ≠ J₀ ∧ I ≠ J₁ := by
  unfold s16c167_idx
  split_ifs with h0 h1
  · exact iff_of_false (by decide) (fun hc => hc.1 h0)
  · exact iff_of_false (by decide) (fun hc => hc.2 h1)
  · exact iff_of_true rfl ⟨h0, h1⟩

private theorem s16c167_eq_one_of_fixes {W : Type} [CommGroup W] {X L K : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    {k : MulAut W} (hk : k ∈ K) (hfix₀ : J₀.map k.toMonoidHom = J₀)
    (hfix₁ : J₁.map k.toMonoidHom = J₁) : k = 1 := by
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
      have hcomm : k * (l : MulAut W) = (l : MulAut W) * k := hKL k hk l l.2
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

theorem s16c167_irr_three_abs {W : Type} [CommGroup W] [Finite W] {X L K : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) (hKX : K ≤ X)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hK : IsSym ↥K 3)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁) :
    ∃ (G3 : Fin 3 → Subgroup W) (π : ↥X →* Equiv.Perm (Fin 3)), Function.Injective G3 ∧
      irrSet L = Set.range G3 ∧
      (∀ (x : ↥X) (i : Fin 3), (G3 i).map (x : MulAut W).toMonoidHom = G3 (π x i)) ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ k : ↥K, π ⟨(k : MulAut W), hKX k.2⟩ = σ) ∧
      (∀ k : ↥K, π ⟨(k : MulAut W), hKX k.2⟩ = 1 → k = 1) := by
  classical
  have hJ₀lt : ⊥ < J₀ := by
    obtain ⟨-, hirr⟩ := F.irr₀
    rw [F.fix, inf_bot_eq] at hirr
    exact hirr.1
  have hJ₀ne : J₀ ≠ ⊥ := hJ₀lt.ne'
  have hJ01 : J₀ ≠ J₁ := by
    intro h
    have h1 : J₀ ⊓ J₁ = J₀ := by rw [h, inf_idem]
    rw [F.inf_eq] at h1
    exact hJ₀ne h1.symm
  have hIrrmem : ∀ I ∈ irrSet L, XMod.IsIrr ↥L I := fun I hI =>
    (s16c167_isIrr_iff L I).1 (s16c167_isIrrOn_of_mem F hI)
  have hg_inj : Function.Injective
      (fun I : ↥(irrSet L) => s16c167_idx J₀ J₁ (I : Subgroup W)) := by
    intro I I' h
    have h' : s16c167_idx J₀ J₁ (I : Subgroup W) =
        s16c167_idx J₀ J₁ (I' : Subgroup W) := h
    have hcases : s16c167_idx J₀ J₁ (I : Subgroup W) = 0 ∨
        s16c167_idx J₀ J₁ (I : Subgroup W) = 1 ∨
        s16c167_idx J₀ J₁ (I : Subgroup W) = 2 := by
      generalize hz : s16c167_idx J₀ J₁ (I : Subgroup W) = z
      fin_cases z <;> simp_all
    rcases hcases with h0 | h1 | h2
    · have hI : (I : Subgroup W) = J₀ := (s16c167_idx_eq_zero hJ01).1 h0
      have hI' : (I' : Subgroup W) = J₀ := (s16c167_idx_eq_zero hJ01).1 (h' ▸ h0)
      exact Subtype.ext (hI.trans hI'.symm)
    · have hI : (I : Subgroup W) = J₁ := (s16c167_idx_eq_one hJ01).1 h1
      have hI' : (I' : Subgroup W) = J₁ := (s16c167_idx_eq_one hJ01).1 (h' ▸ h1)
      exact Subtype.ext (hI.trans hI'.symm)
    · have hI : (I : Subgroup W) ≠ J₀ ∧ (I : Subgroup W) ≠ J₁ :=
        (s16c167_idx_eq_two).1 h2
      have hI' : (I' : Subgroup W) ≠ J₀ ∧ (I' : Subgroup W) ≠ J₁ :=
        (s16c167_idx_eq_two).1 (h' ▸ h2)
      have hle₀ : (I : Subgroup W) ≤ J₀ ⊔ J₁ := F.sup_eq.symm ▸ le_top
      have hle₁ : (I' : Subgroup W) ≤ J₀ ⊔ J₁ := F.sup_eq.symm ▸ le_top
      exact Subtype.ext
        (Z391.v2f_eq_of_le_sup (A := ↥L) (P := J₀) (P' := J₁)
          (R := (I : Subgroup W)) (R' := (I' : Subgroup W))
          (hIrrmem J₀ F.irr₀) (hIrrmem J₁ F.irr₁) hE₀
          (hIrrmem (I : Subgroup W) I.2) (hIrrmem (I' : Subgroup W) I'.2)
          hle₀ hle₁ hI.1 hI.2 hI'.1 hI'.2)
  have hfinS : Finite ↥(irrSet L) := Finite.of_injective _ hg_inj
  haveI : Fintype ↥(irrSet L) := Fintype.ofFinite ↥(irrSet L)
  have hcardS_le : Fintype.card ↥(irrSet L) ≤ 3 := by
    have h := Fintype.card_le_of_injective
      (fun I : ↥(irrSet L) => s16c167_idx J₀ J₁ (I : Subgroup W)) hg_inj
    simpa using h
  let actK : ↥K →* Equiv.Perm ↥(irrSet L) :=
    (s16c167_irrSetAct F).comp (Subgroup.inclusion hKX)
  have hactK : ∀ k : ↥K, actK k = s16c167_irrSetAct F ⟨(k : MulAut W), hKX k.2⟩ := by
    intro k
    change s16c167_irrSetAct F (Subgroup.inclusion hKX k) =
      s16c167_irrSetAct F ⟨(k : MulAut W), hKX k.2⟩
    have h : (Subgroup.inclusion hKX k : ↥X) = ⟨(k : MulAut W), hKX k.2⟩ :=
      Subtype.ext (Subgroup.coe_inclusion hKX k)
    rw [h]
  have htriv : ∀ k : ↥K, actK k = 1 → k = 1 := by
    intro k hk
    apply Subtype.ext
    refine s16c167_eq_one_of_fixes F hKL hE₀ hE₁ k.2 ?_ ?_
    · have h1 := congrArg
        (fun σ : Equiv.Perm ↥(irrSet L) => (σ ⟨J₀, F.irr₀⟩ : Subgroup W)) hk
      rw [hactK k] at h1
      simpa only [Equiv.Perm.one_apply, s16c167_irrSetAct_apply] using h1
    · have h1 := congrArg
        (fun σ : Equiv.Perm ↥(irrSet L) => (σ ⟨J₁, F.irr₁⟩ : Subgroup W)) hk
      rw [hactK k] at h1
      simpa only [Equiv.Perm.one_apply, s16c167_irrSetAct_apply] using h1
  have hinjK : Function.Injective actK := by
    intro k₁ k₂ h
    have h1 : actK (k₁ * k₂⁻¹) = 1 := by
      rw [map_mul, h, map_inv, mul_inv_cancel]
    have h2 : k₁ * k₂⁻¹ = 1 := htriv _ h1
    rwa [mul_inv_eq_one] at h2
  obtain ⟨eK⟩ := hK
  have hfinK : Finite ↥K := Finite.of_injective (eK : ↥K → Equiv.Perm (Fin 3)) eK.injective
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  have hcardK : Fintype.card ↥K = 6 := by
    have h1 : Fintype.card ↥K = Fintype.card (Equiv.Perm (Fin 3)) :=
      Fintype.card_congr eK.toEquiv
    rw [h1, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hle : Fintype.card ↥K ≤ Fintype.card (Equiv.Perm ↥(irrSet L)) :=
    Fintype.card_le_of_injective actK hinjK
  rw [Fintype.card_perm, hcardK] at hle
  have hcardS : Fintype.card ↥(irrSet L) = 3 := by
    have hge : 3 ≤ Fintype.card ↥(irrSet L) := by
      by_contra hcon
      have hlt : Fintype.card ↥(irrSet L) < 3 := not_le.1 hcon
      have hpos : 0 < Fintype.card ↥(irrSet L) := by
        by_contra h0
        have hz : Fintype.card ↥(irrSet L) = 0 := Nat.eq_zero_of_not_pos h0
        rw [hz] at hle
        simp only [Nat.factorial_zero] at hle
        omega
      have hlt' : Nat.factorial (Fintype.card ↥(irrSet L)) < 6 := by
        have h3 := (Nat.factorial_lt hpos).2 hlt
        rwa [show Nat.factorial 3 = 6 from by norm_num] at h3
      exact absurd hle (not_le.2 hlt')
    omega
  let e : Fin 3 ≃ ↥(irrSet L) := (Fintype.equivFinOfCardEq hcardS).symm
  let iso : Equiv.Perm ↥(irrSet L) ≃* Equiv.Perm (Fin 3) := (Equiv.permCongrHom e).symm
  let π : ↥X →* Equiv.Perm (Fin 3) := iso.toMonoidHom.comp (s16c167_irrSetAct F)
  let πK : ↥K →* Equiv.Perm (Fin 3) := iso.toMonoidHom.comp actK
  have hπK_eq : ∀ k : ↥K, πK k = π ⟨(k : MulAut W), hKX k.2⟩ := by
    intro k
    change iso (actK k) = iso (s16c167_irrSetAct F ⟨(k : MulAut W), hKX k.2⟩)
    rw [hactK k]
  have hπK_inj : Function.Injective πK := by
    intro k₁ k₂ h
    have h1 : actK k₁ = actK k₂ := by
      have := congrArg (fun σ => iso.symm σ) h
      simpa [πK, MonoidHom.comp_apply, MulEquiv.symm_apply_apply] using this
    exact hinjK h1
  have hsurj : Function.Surjective πK :=
    (Finite.injective_iff_surjective_of_equiv eK.toEquiv).1 hπK_inj
  let G3 : Fin 3 → Subgroup W := fun i => (e i : Subgroup W)
  refine ⟨G3, π, ?_, ?_, ?_, ?_, ?_⟩
  · intro i i' h
    exact e.injective (Subtype.ext h)
  · ext I
    constructor
    · intro hI
      exact ⟨e.symm ⟨I, hI⟩, by
        show (e (e.symm ⟨I, hI⟩) : Subgroup W) = I
        rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact (e i).2
  · intro x i
    have hπ : π x i = e.symm (s16c167_irrSetAct F x (e i)) := by
      show (iso (s16c167_irrSetAct F x)) i =
        e.symm (s16c167_irrSetAct F x (e i))
      rw [show iso = (Equiv.permCongrHom e).symm from rfl, Equiv.permCongrHom_symm]
      rfl
    show ((e i : Subgroup W).map (x : MulAut W).toMonoidHom) = (e (π x i) : Subgroup W)
    rw [hπ, Equiv.apply_symm_apply]
    exact (s16c167_irrSetAct_apply F x (e i)).symm
  · intro σ
    obtain ⟨k, hk⟩ := hsurj σ
    exact ⟨k, by rw [← hπK_eq k, hk]⟩
  · intro k hk
    apply hπK_inj
    rw [hπK_eq k, hk, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
