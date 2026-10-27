module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Main
public import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.CGT.PushingUpLit.CGT6.SixFourE9
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.GroupTheory.CoprimeSectionStability
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement
open CFSG.CGT.PushingUpLit.CGT6
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem chiefAction_eq_one_iff {H : Type*} [Group H] {N W₁ W₂ : Subgroup H}
    (hN₁ : N ≤ Subgroup.normalizer (W₁ : Set H))
    (hN₂ : N ≤ Subgroup.normalizer (W₂ : Set H)) [hW : (W₂.subgroupOf W₁).Normal] (n : ↥N) :
    CFSG.ABGLocalTools.chiefAction hN₁ hN₂ n = 1 ↔ ∀ w ∈ W₁, ⁅w, (n : H)⁆ ∈ W₂ := by
  have key : ∀ w : W₁, ((CFSG.ABGLocalTools.chiefConj hN₁ n w : W₁) :
      W₁ ⧸ W₂.subgroupOf W₁) = (w : W₁ ⧸ W₂.subgroupOf W₁) ↔ ⁅(w : H), (n : H)⁆ ∈ W₂ := by
    intro w
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc : ⁅(w : H), (n : H)⁆ =
        (w : H) * (((CFSG.ABGLocalTools.chiefConj hN₁ n w)⁻¹ * w : W₁) : H) * (w : H)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, CFSG.ABGLocalTools.chiefConj_apply_coe,
        commutatorElement_def]
      group
    rw [hc]
    constructor
    · intro h
      have := hW.conj_mem _ ((Subgroup.mem_subgroupOf).mpr h) w
      rwa [Subgroup.mem_subgroupOf] at this
    · intro h
      have hmem : (w * ((CFSG.ABGLocalTools.chiefConj hN₁ n w)⁻¹ * w) * w⁻¹ : W₁) ∈
          W₂.subgroupOf W₁ := by
        rw [Subgroup.mem_subgroupOf]
        simpa using h
      have := hW.conj_mem _ hmem w⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa [mul_assoc] using this
  constructor
  · intro h w hw
    have h1 := congrArg (fun f : MulAut (W₁ ⧸ W₂.subgroupOf W₁) =>
      f (QuotientGroup.mk (⟨w, hw⟩ : W₁))) h
    rw [MulAut.one_apply, CFSG.ABGLocalTools.chiefAction_mk hN₁ hN₂ n ⟨w, hw⟩] at h1
    exact (key ⟨w, hw⟩).mp h1
  · intro h
    ext x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.one_apply, CFSG.ABGLocalTools.chiefAction_mk hN₁ hN₂ n w]
    exact (key w).mpr (h w w.2)

theorem f4Theta_mem_hermSub_one {ω : Fq 2} (hω : ω ^ 2 + ω + 1 = 0) {x : Fin 5 → ZMod 2}
    (hx : ∑ i, x i = 0) : CFSG.Quasithin.H13.OrthFour.f4Theta ω x ∈ hermSub 1 := by
  rw [TwoEight.mem_hermSub_iff]
  have h := CFSG.Quasithin.H13.OrthFour.f4Theta_herm (K := Fq 2) hω x
  have hs : TwoEight.sigR 1 = fun y : Fq 2 => y ^ 2 := by
    funext y
    rw [TwoEight.sigR_apply]
    norm_num
  simpa [TwoEight.cstar, hs] using h

noncomputable def f4ThetaCoreHom (ω : Fq 2) (hω : ω ^ 2 + ω + 1 = 0) :
    ↥(CFSG.Quasithin.G6.coreMod 5) →* Multiplicative (hermSub 1) :=
  MonoidHom.mk' (fun m => Multiplicative.ofAdd
    ⟨CFSG.Quasithin.H13.OrthFour.f4Theta ω
        (Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5)),
      f4Theta_mem_hermSub_one hω (CFSG.Quasithin.G6.mem_coreMod.mp m.2)⟩)
    (fun m n => by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_ofAdd, toAdd_mul]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, AddSubgroup.coe_add, AddMemClass.coe_add, toAdd_mul,
        CFSG.Quasithin.H13.OrthFour.f4Theta_add])

theorem f4ThetaCoreHom_bijective (ω : Fq 2) (hω : ω ^ 2 + ω + 1 = 0)
    (h4 : ∀ x : Fq 2, x ^ 4 = x) : Function.Bijective (f4ThetaCoreHom ω hω) := by
  constructor
  · intro m n h
    have h1 : CFSG.Quasithin.H13.OrthFour.f4Theta ω
        (Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5)) =
        CFSG.Quasithin.H13.OrthFour.f4Theta ω
          (Multiplicative.toAdd (n : CFSG.Quasithin.G6.PermMod 5)) := by
      have := congrArg (fun y : Multiplicative (hermSub 1) => (Multiplicative.toAdd y).1) h
      simpa [f4ThetaCoreHom, MonoidHom.mk'_apply] using this
    have h2 : CFSG.Quasithin.H13.OrthFour.f4Theta ω
        (Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5) +
          Multiplicative.toAdd (n : CFSG.Quasithin.G6.PermMod 5)) = 0 := by
      rw [CFSG.Quasithin.H13.OrthFour.f4Theta_add, h1]
      exact CharTwo.add_self_eq_zero _
    have hsum : ∑ i, (Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5) +
          Multiplicative.toAdd (n : CFSG.Quasithin.G6.PermMod 5)) i = 0 := by
      simp [Finset.sum_add_distrib, CFSG.Quasithin.G6.mem_coreMod.mp m.2,
        CFSG.Quasithin.G6.mem_coreMod.mp n.2]
    have hzero := CFSG.Quasithin.H13.OrthFour.f4Theta_eq_zero hω hsum h2
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact CharTwo.add_eq_zero.mp (congrFun hzero i)
  · intro y
    have hy : ((Multiplicative.toAdd y).1.map (fun z : Fq 2 => z ^ 2))ᵀ =
        (Multiplicative.toAdd y).1 := by
      have h := (TwoEight.mem_hermSub_iff (n := 1) (Multiplicative.toAdd y).1).mp
        (Multiplicative.toAdd y).2
      have hs : TwoEight.sigR 1 = fun z : Fq 2 => z ^ 2 := by
        funext z
        rw [TwoEight.sigR_apply]
        norm_num
      simpa [TwoEight.cstar, hs] using h
    obtain ⟨x, hxsum, hfx⟩ := CFSG.Quasithin.H13.OrthFour.f4Theta_surj hω h4 hy
    refine ⟨⟨Multiplicative.ofAdd x, CFSG.Quasithin.G6.mem_coreMod.mpr hxsum⟩, ?_⟩
    show Multiplicative.ofAdd (⟨CFSG.Quasithin.H13.OrthFour.f4Theta ω x,
      f4Theta_mem_hermSub_one hω hxsum⟩ : hermSub 1) = y
    rw [← ofAdd_toAdd y]
    congr 1
    apply Subtype.ext
    simpa using hfx

theorem f4ThetaCoreHom_equivariant (ω : Fq 2) (hω : ω ^ 2 + ω + 1 = 0)
    (h4 : ∀ x : Fq 2, x ^ 4 = x)
    (e : Matrix.SpecialLinearGroup (Fin 2) (Fq 2) ≃* alternatingGroup (Fin 5))
    (he : ∀ s : Matrix.SpecialLinearGroup (Fin 2) (Fq 2),
      (e s : Equiv.Perm (Fin 5)) =
        CFSG.Quasithin.H13.OrthFour.f4PermHom hω h4 (Matrix.SpecialLinearGroup.toGL s))
    (s : Matrix.SpecialLinearGroup (Fin 2) (Fq 2))
    (m : ↥(CFSG.Quasithin.G6.coreMod 5)) :
    f4ThetaCoreHom ω hω (CFSG.Quasithin.G6.coreAct 5 (e s) m) =
      omegaMinusAct 1 s (f4ThetaCoreHom ω hω m) := by
  have hx : Multiplicative.toAdd (CFSG.Quasithin.G6.coreAct 5 (e s) m :
      CFSG.Quasithin.G6.PermMod 5) =
      fun i => Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5)
        ((e s : Equiv.Perm (Fin 5))⁻¹ i) := by
    funext i
    show Multiplicative.toAdd ((CFSG.Quasithin.G6.coreAct 5 (e s) m :
      CFSG.Quasithin.G6.coreMod 5) : CFSG.Quasithin.G6.PermMod 5) i = _
    rw [CFSG.Quasithin.G6.coreAct_coe, CFSG.Quasithin.G6.permAct_apply]
  have hcs : TwoEight.cstar 1 (s : Matrix (Fin 2) (Fin 2) (Fq 2)) =
      ((s : Matrix (Fin 2) (Fin 2) (Fq 2)).map (fun z : Fq 2 => z ^ 2))ᵀ := by
    have hs : TwoEight.sigR 1 = fun z : Fq 2 => z ^ 2 := by
      funext z
      rw [TwoEight.sigR_apply]
      norm_num
    simp [TwoEight.cstar, hs]
  rw [TwoEight.omegaMinusAct_eq]
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  simp only [f4ThetaCoreHom, MonoidHom.mk'_apply, TwoEight.minusAct, toAdd_ofAdd,
    AddSubgroup.coe_add, AddMemClass.coe_add]
  rw [hx, hcs]
  have hp := CFSG.Quasithin.H13.OrthFour.f4Theta_perm hω h4
    (Matrix.SpecialLinearGroup.toGL s) (Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5))
  rw [show (fun i => Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5)
      ((e s : Equiv.Perm (Fin 5))⁻¹ i)) =
      fun i => Multiplicative.toAdd (m : CFSG.Quasithin.G6.PermMod 5)
        ((CFSG.Quasithin.H13.OrthFour.f4PermHom hω h4
          (Matrix.SpecialLinearGroup.toGL s))⁻¹ i) from by funext i; rw [he s]]
  rw [hp]
  rfl

theorem hermSub_one_coreMod_five_equiv :
    ∃ (e : Matrix.SpecialLinearGroup (Fin 2) (Fq 2) ≃* alternatingGroup (Fin 5))
      (γ : Multiplicative (hermSub 1) ≃* CFSG.Quasithin.G6.coreMod 5),
      ∀ (s : Matrix.SpecialLinearGroup (Fin 2) (Fq 2)) (m : Multiplicative (hermSub 1)),
        γ (omegaMinusAct 1 s m) =
          CFSG.Quasithin.G6.coreAct 5 (e s : Equiv.Perm (Fin 5)) (γ m) := by
  have hcard4 : Nat.card (Fq 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨ω, hω⟩ := CFSG.Quasithin.H13.OrthFour.f4_exists_omega (K := Fq 2) hcard4
  have h4 := CFSG.Quasithin.H13.OrthFour.f4_pow_four (K := Fq 2) hcard4
  obtain ⟨e', he'⟩ := CFSG.Quasithin.H13.OrthFour.exists_equiv_alt hω h4 hcard4
  let e : Matrix.SpecialLinearGroup (Fin 2) (Fq 2) ≃* alternatingGroup (Fin 5) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (Fq 2)).trans e'
  have he : ∀ s : Matrix.SpecialLinearGroup (Fin 2) (Fq 2),
      (e s : Equiv.Perm (Fin 5)) =
        CFSG.Quasithin.H13.OrthFour.f4PermHom hω h4 (Matrix.SpecialLinearGroup.toGL s) := by
    intro s
    have h := he' (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (Fq 2) s)
    show ((e' (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (Fq 2) s)) :
      Equiv.Perm (Fin 5)) = _
    rw [h]
    exact congrArg (CFSG.Quasithin.H13.OrthFour.f4PermHom hω h4) (by
      apply Units.ext
      exact CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 (Fq 2) s)
  let Θe : ↥(CFSG.Quasithin.G6.coreMod 5) ≃* Multiplicative (hermSub 1) :=
    MulEquiv.ofBijective (f4ThetaCoreHom ω hω) (f4ThetaCoreHom_bijective ω hω h4)
  have heq : ∀ (s : Matrix.SpecialLinearGroup (Fin 2) (Fq 2))
      (m : ↥(CFSG.Quasithin.G6.coreMod 5)),
      Θe (CFSG.Quasithin.G6.coreAct 5 (e s) m) = omegaMinusAct 1 s (Θe m) :=
    fun s m => f4ThetaCoreHom_equivariant ω hω h4 e he s m
  refine ⟨e, Θe.symm, fun s m => ?_⟩
  have hconv : Θe.symm (omegaMinusAct 1 s m) =
      CFSG.Quasithin.G6.coreAct 5 (e s) (Θe.symm m) := by
    apply Θe.injective
    rw [MulEquiv.apply_symm_apply, heq, MulEquiv.apply_symm_apply]
  exact hconv

private abbrev A5Sec (N₀ N₁ : Subgroup G) [(N₁.subgroupOf N₀).Normal] : Type :=
  N₀ ⧸ N₁.subgroupOf N₀

section A5MinusModuleHelpers

variable {D N₀ N₁ : Subgroup G}

private noncomputable abbrev a5Rho
    (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal] :
    ↥D →* MulAut (A5Sec N₀ N₁) :=
  CFSG.ABGLocalTools.chiefAction hDN0 hDN1

private noncomputable abbrev a5G'
    (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal] :
    Subgroup (MulAut (A5Sec N₀ N₁)) :=
  (a5Rho hDN0 hDN1).range

private def a5GInv {V : Type} [Group V] (X : Subgroup (MulAut V)) (A : Subgroup V) : Prop :=
  ∀ g ∈ X, ∀ a ∈ A, g a ∈ A

private theorem a5_N₁_lt_N₀ (hN1le : N₁ ≤ N₀) (hidx : N₁.relIndex N₀ = 16) : N₁ < N₀ := by
  refine lt_of_le_of_ne hN1le ?_
  intro hEq
  rw [hEq, Subgroup.relIndex_self] at hidx
  omega

private theorem a5_N₀_le_normalizer_N₁ (hN1le : N₁ ≤ N₀)
    (hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, ⁅x, y⁆ ∈ N₁) :
    N₀ ≤ Subgroup.normalizer (N₁ : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
  intro x hx y hy
  exact hcomm x hx y (hN1le hy)

private theorem a5_conj_mem_N₁ (hN1le : N₁ ≤ N₀)
    (hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, ⁅x, y⁆ ∈ N₁) :
    ∀ x ∈ N₀, ∀ y ∈ N₁, x * y * x⁻¹ ∈ N₁ := by
  intro x hx y hy
  have h1 := hcomm x hx y (hN1le hy)
  rw [commutatorElement_def] at h1
  have h2 : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
  rw [h2]
  exact Subgroup.mul_mem _ h1 hy

private theorem a5_isChiefFactor (hN1le : N₁ ≤ N₀)
    (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G))
    (hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, ⁅x, y⁆ ∈ N₁) (hsq : ∀ x ∈ N₀, x ^ 2 ∈ N₁)
    (hidx : N₁.relIndex N₀ = 16)
    (hirr : ∀ Y : Subgroup G, N₁ ≤ Y → Y ≤ N₀ → D ≤ Subgroup.normalizer (Y : Set G) →
      Y = N₁ ∨ Y = N₀) :
    CFSG.ABGLocalTools.IsChiefFactorUnder 2 D N₀ N₁ :=
  ⟨a5_N₁_lt_N₀ hN1le hidx, hDN0, hDN1, a5_conj_mem_N₁ hN1le hcomm, hcomm, hsq, hirr⟩

private theorem a5_mem_map_comap [(N₁.subgroupOf N₀).Normal]
    {A : Subgroup (A5Sec N₀ N₁)} (n : ↥N₀) :
    (n : G) ∈ (A.comap (QuotientGroup.mk' (N₁.subgroupOf N₀))).map N₀.subtype ↔
      QuotientGroup.mk' (N₁.subgroupOf N₀) n ∈ A := by
  constructor
  · rintro ⟨m, hm, hmn⟩
    have : m = n := Subtype.ext hmn
    rwa [this] at hm
  · intro hn
    exact ⟨n, hn, rfl⟩

private theorem a5_centralizer_sup_eq_top (hN1le : N₁ ≤ N₀) (h2grp : IsPGroup 2 N₀)
    (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    (hN₀norm : N₀ ≤ Subgroup.normalizer (N₁ : Set G))
    {d : G} (hdD : d ∈ D) (hd3 : orderOf d = 3)
    (hρd : a5Rho hDN0 hDN1 ⟨d, hdD⟩ = 1) :
    (N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ N₁ = N₀ := by
  have hzpN0 : Subgroup.zpowers d ≤ Subgroup.normalizer (N₀ : Set G) :=
    Subgroup.zpowers_le.mpr (hDN0 hdD)
  have hzpN1 : Subgroup.zpowers d ≤ Subgroup.normalizer (N₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hDN1 hdD)
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥N₀) := by
    rw [Nat.card_zpowers, hd3]
    obtain ⟨k, hk⟩ := h2grp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  haveI : Group.IsNilpotent ↥N₀ := IsPGroup.isNilpotent h2grp
  have hsolv : Group.IsSolvable ↥N₀ := inferInstance
  have hzpow_fixed : N₀ ≤ (N₀ ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set G)) ⊔ N₁ := by
    intro n hn
    rw [← GroupTheory.CoprimeSection.mem_centralizer_sup_iff hN1le hN₀norm hzpN0 hzpN1
      hcop hsolv hn]
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have hρe : a5Rho hDN0 hDN1 (⟨d ^ k, zpow_mem hdD k⟩ : ↥D) = 1 := by
      rw [show (⟨d ^ k, zpow_mem hdD k⟩ : ↥D) = ⟨d, hdD⟩ ^ k from Subtype.ext rfl,
        map_zpow, hρd, one_zpow]
    have h1 := (chiefAction_eq_one_iff hDN0 hDN1 (⟨d ^ k, zpow_mem hdD k⟩ : ↥D)).mp hρe n hn
    rw [commutatorElement_def] at h1
    have h2 : d ^ k * n * (d ^ k)⁻¹ * n⁻¹ = (n * d ^ k * n⁻¹ * (d ^ k)⁻¹)⁻¹ := by group
    rw [h2]
    exact inv_mem h1
  refine le_antisymm (sup_le inf_le_left hN1le) ?_
  exact hzpow_fixed.trans (sup_le_sup_right
    (inf_le_inf_left N₀ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers d)))) N₁)

private theorem a5_rho_d_ne_one (hN1le : N₁ ≤ N₀) (h2grp : IsPGroup 2 N₀)
    (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    (hN₀norm : N₀ ≤ Subgroup.normalizer (N₁ : Set G))
    {d : G} (hdD : d ∈ D) (hd3 : orderOf d = 3)
    (hdidx : ((N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ N₁).relIndex N₀ = 4) :
    a5Rho hDN0 hDN1 ⟨d, hdD⟩ ≠ 1 := by
  intro hρd
  have hEq := a5_centralizer_sup_eq_top hN1le h2grp hDN0 hDN1 hN₀norm hdD hd3 hρd
  rw [hEq, Subgroup.relIndex_self] at hdidx
  omega

private theorem a5_centralizer_not_le {d : G}
    (hdidx : ((N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ N₁).relIndex N₀ = 4)
    (hidx : N₁.relIndex N₀ = 16) :
    ¬ (N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ≤ N₁ := by
  intro hle
  have hEq : (N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ N₁ = N₁ := sup_eq_right.mpr hle
  rw [hEq] at hdidx
  omega

private theorem a5_exists_fixed (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {d c : G} (hdD : d ∈ D) (hc : c ∈ N₀ ⊓ Subgroup.centralizer ({d} : Set G))
    (hcN1 : c ∉ N₁) :
    ∃ v : A5Sec N₀ N₁, v ≠ 1 ∧ a5Rho hDN0 hDN1 ⟨d, hdD⟩ v = v := by
  have hcd : d * c * d⁻¹ = c := by
    have hcomm : d * c = c * d := (Subgroup.mem_centralizer_iff.mp hc.2) d (by simp)
    rw [hcomm]; group
  refine ⟨QuotientGroup.mk' _ ⟨c, hc.1⟩, ?_, ?_⟩
  · intro h
    have h' : (⟨c, hc.1⟩ : ↥N₀) ∈ N₁.subgroupOf N₀ :=
      (QuotientGroup.eq_one_iff (N := N₁.subgroupOf N₀) ⟨c, hc.1⟩).mp h
    exact hcN1 h'
  · have hmk : (QuotientGroup.mk' (N₁.subgroupOf N₀) ⟨c, hc.1⟩ : A5Sec N₀ N₁) =
        ((⟨c, hc.1⟩ : ↥N₀) : A5Sec N₀ N₁) := QuotientGroup.mk'_apply _ _
    rw [hmk, CFSG.ABGLocalTools.chiefAction_mk hDN0 hDN1]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv,
      CFSG.ABGLocalTools.chiefConj_apply_coe, hcd]
    simpa using Subgroup.one_mem N₁

private theorem a5_ker_eq (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {φ : ↥D →* alternatingGroup (Fin 5)}
    (hφker : ∀ e : ↥D, φ e = 1 ↔ ∀ n ∈ N₀, ⁅n, (e : G)⁆ ∈ N₁) :
    (a5Rho hDN0 hDN1).ker = φ.ker := by
  ext e
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  rw [show a5Rho hDN0 hDN1 e = 1 ↔ ∀ n ∈ N₀, ⁅n, (e : G)⁆ ∈ N₁ from
    chiefAction_eq_one_iff hDN0 hDN1 e]
  exact (hφker e).symm

private theorem a5_ker_rangeRestrict (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal] :
    (a5Rho hDN0 hDN1).rangeRestrict.ker = (a5Rho hDN0 hDN1).ker := by
  ext e
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

private theorem a5_rangeRestrict_d_pow_three (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {d : G} (hdD : d ∈ D) (hd3 : orderOf d = 3)
    (hρd_ne : a5Rho hDN0 hDN1 ⟨d, hdD⟩ ≠ 1) :
    (a5Rho hDN0 hDN1).rangeRestrict ⟨d, hdD⟩ ^ 3 = 1 ∧
      (a5Rho hDN0 hDN1).rangeRestrict ⟨d, hdD⟩ ≠ 1 := by
  constructor
  · have hx3 : (⟨d, hdD⟩ : ↥D) ^ 3 = 1 := by
      rw [show (3 : ℕ) = orderOf (⟨d, hdD⟩ : ↥D) from by
            rw [(Subgroup.orderOf_coe ⟨d, hdD⟩).symm, hd3],
          pow_orderOf_eq_one]
    rw [← map_pow, hx3, map_one]
  · intro h
    apply hρd_ne
    have := congrArg (fun f : ↥(a5G' hDN0 hDN1) => (f : MulAut (A5Sec N₀ N₁))) h
    simpa using this

private theorem a5_nonempty_G'_equiv_SL (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {φ : ↥D →* alternatingGroup (Fin 5)} (hφsurj : Function.Surjective φ)
    (hφker : ∀ e : ↥D, φ e = 1 ↔ ∀ n ∈ N₀, ⁅n, (e : G)⁆ ∈ N₁) :
    Nonempty (↥(a5G' hDN0 hDN1) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq 2)) := by
  refine ⟨?_⟩
  refine (QuotientGroup.quotientKerEquivOfSurjective (a5Rho hDN0 hDN1).rangeRestrict
    (a5Rho hDN0 hDN1).rangeRestrict_surjective).symm.trans ?_
  refine (QuotientGroup.quotientMulEquivOfEq
    ((a5_ker_rangeRestrict hDN0 hDN1).trans (a5_ker_eq hDN0 hDN1 hφker))).trans ?_
  exact (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).trans
    (CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5.some.symm)

private theorem a5_card_sec [(N₁.subgroupOf N₀).Normal] (hidx : N₁.relIndex N₀ = 16) :
    Nat.card (A5Sec N₀ N₁) = 16 := by
  show Nat.card (↥N₀ ⧸ N₁.subgroupOf N₀) = 16
  rw [← Subgroup.index_eq_card]
  exact hidx

private theorem a5_card_sec_le [(N₁.subgroupOf N₀).Normal] (hidx : N₁.relIndex N₀ = 16) :
    Nat.card (A5Sec N₀ N₁) ≤ 2 ^ (2 * 2) := by
  rw [a5_card_sec hidx]
  norm_num

private theorem a5_le_normalizer_of_GInv (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {A : Subgroup (A5Sec N₀ N₁)} (hA : a5GInv (a5G' hDN0 hDN1) A) :
    D ≤ Subgroup.normalizer
      (((A.comap (QuotientGroup.mk' (N₁.subgroupOf N₀))).map N₀.subtype : Subgroup G) :
        Set G) := by
  let mk := QuotientGroup.mk' (N₁.subgroupOf N₀)
  let Y : Subgroup G := (A.comap mk).map N₀.subtype
  have hstep : ∀ e ∈ D, ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := by
    intro e he y hy
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    have hmA : mk m ∈ A := hm
    have h1 := hA (a5Rho hDN0 hDN1 ⟨e, he⟩)
      (MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩) (mk m) hmA
    change (CFSG.ABGLocalTools.chiefAction hDN0 hDN1 ⟨e, he⟩)
      (m : A5Sec N₀ N₁) ∈ A at h1
    rw [CFSG.ABGLocalTools.chiefAction_mk hDN0 hDN1] at h1
    have hconj : (CFSG.ABGLocalTools.chiefConj hDN0 ⟨e, he⟩ m : G) ∈ Y :=
      (a5_mem_map_comap (A := A) (CFSG.ABGLocalTools.chiefConj hDN0 ⟨e, he⟩ m)).mpr h1
    rw [← hmy]
    change (CFSG.ABGLocalTools.chiefConj hDN0 ⟨e, he⟩ m : G) ∈ Y
    exact hconj
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨hstep e he y, fun hy => by
    have h1 := hstep e⁻¹ (inv_mem he) (e * y * e⁻¹) hy
    rwa [show e⁻¹ * (e * y * e⁻¹) * (e⁻¹)⁻¹ = y from by group] at h1⟩

private theorem a5_GInv_of_le_normalizer (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {A : Subgroup (A5Sec N₀ N₁)}
    (hD : D ≤ Subgroup.normalizer
      (((A.comap (QuotientGroup.mk' (N₁.subgroupOf N₀))).map N₀.subtype : Subgroup G) :
        Set G)) :
    a5GInv (a5G' hDN0 hDN1) A := by
  intro g hg a ha
  obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hg
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
  have hnA : QuotientGroup.mk' (N₁.subgroupOf N₀) n ∈ A := ha
  have hnY : (n : G) ∈ (A.comap (QuotientGroup.mk' (N₁.subgroupOf N₀))).map N₀.subtype :=
    (a5_mem_map_comap (A := A) n).mpr hnA
  have hconj : (CFSG.ABGLocalTools.chiefConj hDN0 e n : G) ∈
      (A.comap (QuotientGroup.mk' (N₁.subgroupOf N₀))).map N₀.subtype := by
    rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hD e.2) (n : G)).mp hnY
  rw [show a5Rho hDN0 hDN1 = CFSG.ABGLocalTools.chiefAction hDN0 hDN1 from rfl,
    CFSG.ABGLocalTools.chiefAction_mk hDN0 hDN1]
  exact (a5_mem_map_comap (A := A) (CFSG.ABGLocalTools.chiefConj hDN0 e n)).mp hconj

private theorem a5_GInv_iff (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    (A : Subgroup (A5Sec N₀ N₁)) :
    a5GInv (a5G' hDN0 hDN1) A ↔ D ≤ Subgroup.normalizer
      (((A.comap (QuotientGroup.mk' (N₁.subgroupOf N₀))).map N₀.subtype : Subgroup G) :
        Set G) :=
  ⟨a5_le_normalizer_of_GInv hDN0 hDN1, a5_GInv_of_le_normalizer hDN0 hDN1⟩

private theorem a5_GInv_eq_bot_or_top (hN1le : N₁ ≤ N₀)
    (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    (hirr : ∀ Y : Subgroup G, N₁ ≤ Y → Y ≤ N₀ → D ≤ Subgroup.normalizer (Y : Set G) →
      Y = N₁ ∨ Y = N₀) :
    ∀ A : Subgroup (A5Sec N₀ N₁), a5GInv (a5G' hDN0 hDN1) A → A = ⊥ ∨ A = ⊤ := by
  intro A hA
  let mk := QuotientGroup.mk' (N₁.subgroupOf N₀)
  let Y : Subgroup G := (A.comap mk).map N₀.subtype
  have hYN0 : Y ≤ N₀ := Subgroup.map_subtype_le _
  have hN1Y : N₁ ≤ Y := by
    intro x hx
    refine ⟨⟨x, hN1le hx⟩, ?_, rfl⟩
    change mk ⟨x, hN1le hx⟩ ∈ A
    have h1 : mk ⟨x, hN1le hx⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    rw [h1]
    exact Subgroup.one_mem A
  have hYnorm : D ≤ Subgroup.normalizer (Y : Set G) := (a5_GInv_iff hDN0 hDN1 A).mp hA
  rcases hirr Y hN1Y hYN0 hYnorm with hY | hY
  · left
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
    have hnA : mk n ∈ A := ha
    have : (n : G) ∈ Y := (a5_mem_map_comap (A := A) n).mpr hnA
    rw [hY] at this
    rw [Subgroup.mem_bot]
    change (n : A5Sec N₀ N₁) = 1
    exact (QuotientGroup.eq_one_iff _).mpr this
  · right
    rw [eq_top_iff]
    intro a _
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
    have : (n : G) ∈ Y := by rw [hY]; exact n.2
    exact (a5_mem_map_comap (A := A) n).mp this

private theorem a5_not_trivial_action (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {d : G} (hdD : d ∈ D) (hρd_ne : a5Rho hDN0 hDN1 ⟨d, hdD⟩ ≠ 1)
    (htriv : ∀ g ∈ a5G' hDN0 hDN1, ∀ v : A5Sec N₀ N₁, g v = v) : False := by
  have hg1 : (a5Rho hDN0 hDN1).rangeRestrict ⟨d, hdD⟩ = 1 := by
    ext v
    exact htriv _ (MonoidHom.mem_range.mpr ⟨⟨d, hdD⟩, rfl⟩) v
  exact hρd_ne (by
    have := congrArg (fun f : ↥(a5G' hDN0 hDN1) => (f : MulAut (A5Sec N₀ N₁))) hg1
    simpa using this)

private theorem slNat_no_fixed_of_order_three {V : Type} [CommGroup V]
    {G : Subgroup (MulAut V)}
    (h : CFSG.CGT.PushingUpLit.BHS6.IsNatSectionBy (slAct 2) G ⊤ ⊥)
    {g : ↥G} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {v0 : V} (hv0ne : v0 ≠ 1) (hv0fix : (g : MulAut V) v0 = v0) : False := by
  obtain ⟨θ, β, hβsurj, hβker, hβeq⟩ := h.2
  let s : Matrix.SpecialLinearGroup (Fin 2) (Fq 2) := θ g
  have hs3 : s ^ 3 = 1 := by
    dsimp only [s]
    rw [← map_pow, hg3, map_one]
  have hs1 : s ≠ 1 := by
    intro hc
    apply hg1
    apply θ.injective
    rw [map_one]
    exact hc
  let p0 : ↥(⊤ : Subgroup V) := ⟨v0, Subgroup.mem_top v0⟩
  have hfixβ : (s : Matrix (Fin 2) (Fin 2) (Fq 2)).mulVec
      (Multiplicative.toAdd (β p0)) = Multiplicative.toAdd (β p0) := by
    have h1 := hβeq g p0 (Subgroup.mem_top _)
    have h2 : (g : MulAut V) v0 = v0 := hv0fix
    rw [h2] at h1
    have h1' : Multiplicative.toAdd (β p0) =
        (s : Matrix (Fin 2) (Fin 2) (Fq 2)).mulVec (Multiplicative.toAdd (β p0)) := by
      have := congrArg Multiplicative.toAdd h1
      simpa [s, p0, slAct] using this
    exact h1'.symm
  have hβp0 : β p0 ≠ 1 := by
    intro hker
    have h1 : p0 ∈ β.ker := MonoidHom.mem_ker.mpr hker
    rw [hβker] at h1
    have h2 : p0 = 1 := by simpa [Subgroup.mem_bot] using h1
    exact hv0ne (Subtype.ext_iff.mp h2)
  have hzero := CFSG.CGT.PushingUpLit.CGT6.fixed_vec_eq_zero_of_order_three hs3 hs1
    (Multiplicative.toAdd (β p0)) hfixβ
  exact hβp0 (Multiplicative.toAdd.injective (by simpa using hzero))

private theorem a5_isNatSection_omegaMinus {V : Type} [CommGroup V] [Finite V]
    (X : Subgroup (MulAut V))
    (hV2 : ∀ v : V, v ^ 2 = 1)
    (hGiso : Nonempty (↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq 2)))
    (hirrV : ∀ A : Subgroup V, GInv X A → A = ⊥ ∨ A = ⊤)
    (hcard : Nat.card V ≤ 2 ^ (2 * 2))
    (htriv : ¬ ∀ g ∈ X, ∀ v : V, g v = v)
    (hnat : ¬ CFSG.CGT.PushingUpLit.BHS6.IsNatSectionBy (slAct 2) X ⊤ ⊥) :
    CFSG.CGT.PushingUpLit.BHS6.IsNatSectionBy (omegaMinusAct 1) X ⊤ ⊥ := by
  rcases CFSG.CGT.PushingUpLit.CGT6.l2SmallModules_holds 2 (by norm_num) V hV2 X hGiso
    hirrV hcard with htriv' | hnat' | hOmega
  · exact (htriv htriv').elim
  · exact (hnat hnat').elim
  · obtain ⟨k, hk, hΩ⟩ := hOmega
    have hk1 : k = 1 := by omega
    subst hk1
    exact hΩ

private theorem a5_exists_beta {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}
    (hOmega : CFSG.CGT.PushingUpLit.BHS6.IsNatSectionBy (omegaMinusAct 1) G ⊤ ⊥) :
    ∃ (θ : ↥G ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq 2))
      (β' : V →* Multiplicative (hermSub 1)),
      Function.Bijective β' ∧
      ∀ (g : ↥G) (v : V), β' ((g : MulAut V) v) = omegaMinusAct 1 (θ g) (β' v) := by
  obtain ⟨θ, β, hβsurj, hβker, hβeq⟩ := hOmega.2
  have hβinj : Function.Injective β := by
    apply (MonoidHom.ker_eq_bot_iff β).mp
    simpa using hβker
  let β' : V →* Multiplicative (hermSub 1) :=
    { toFun := fun v => β ⟨v, Subgroup.mem_top v⟩
      map_one' := by
        rw [show (⟨1, Subgroup.mem_top (1 : V)⟩ : ↥(⊤ : Subgroup V)) = 1 from rfl, map_one]
      map_mul' := fun a b => by
        rw [show (⟨a * b, Subgroup.mem_top (a * b)⟩ : ↥(⊤ : Subgroup V)) =
          ⟨a, Subgroup.mem_top a⟩ * ⟨b, Subgroup.mem_top b⟩ from rfl, map_mul] }
  have hβ'inj : Function.Injective β' := by
    intro a b hab
    have h1 : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup V)) =
        ⟨b, Subgroup.mem_top b⟩ := hβinj hab
    exact Subtype.ext_iff.mp h1
  have hβ'surj : Function.Surjective β' := by
    intro m
    obtain ⟨p, hp⟩ := hβsurj m
    refine ⟨p.val, ?_⟩
    change β ⟨p.val, Subgroup.mem_top p.val⟩ = m
    rw [show (⟨p.val, Subgroup.mem_top p.val⟩ : ↥(⊤ : Subgroup V)) = p from Subtype.ext rfl]
    exact hp
  refine ⟨θ, β', ⟨hβ'inj, hβ'surj⟩, fun g v => ?_⟩
  simpa [β'] using hβeq g ⟨v, Subgroup.mem_top v⟩ (Subgroup.mem_top _)

private theorem a5_bridge_pi (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    {d : ↥D} {n n' : ↥N₀} (hn' : (n' : G) = (d : G) * n * (d : G)⁻¹) :
    a5Rho hDN0 hDN1 d (QuotientGroup.mk' (N₁.subgroupOf N₀) n) =
      QuotientGroup.mk' (N₁.subgroupOf N₀) n' := by
  have hcn' : CFSG.ABGLocalTools.chiefConj hDN0 d n = n' := by
    apply Subtype.ext
    rw [CFSG.ABGLocalTools.chiefConj_apply_coe, hn']
  rw [show a5Rho hDN0 hDN1 d = CFSG.ABGLocalTools.chiefAction hDN0 hDN1 d from rfl]
  rw [show (QuotientGroup.mk' (N₁.subgroupOf N₀) n : A5Sec N₀ N₁) =
    (n : A5Sec N₀ N₁) from QuotientGroup.mk'_apply _ _]
  rw [CFSG.ABGLocalTools.chiefAction_mk hDN0 hDN1]
  rw [show (QuotientGroup.mk' (N₁.subgroupOf N₀) n' : A5Sec N₀ N₁) =
    (n' : A5Sec N₀ N₁) from QuotientGroup.mk'_apply _ _]
  rw [hcn']

private theorem natA5Sec_of_bridge (hDN0 : D ≤ Subgroup.normalizer (N₀ : Set G))
    (hDN1 : D ≤ Subgroup.normalizer (N₁ : Set G)) [(N₁.subgroupOf N₀).Normal]
    (θ : ↥(a5G' hDN0 hDN1) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq 2))
    (β' : A5Sec N₀ N₁ →* Multiplicative (hermSub 1))
    (hβ'bij : Function.Bijective β')
    (hβ'eq : ∀ (g : ↥(a5G' hDN0 hDN1)) (v : A5Sec N₀ N₁),
      β' ((g : MulAut (A5Sec N₀ N₁)) v) = omegaMinusAct 1 (θ g) (β' v)) :
    NatA5Sec D N₀ N₁ := by
  obtain ⟨e, γ, hγeq⟩ := hermSub_one_coreMod_five_equiv
  let φ' : ↥D →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (θ.toMonoidHom.comp (a5Rho hDN0 hDN1).rangeRestrict)
  let ψ : ↥N₀ →* ↥(CFSG.Quasithin.G6.coreMod 5) :=
    γ.toMonoidHom.comp (β'.comp (QuotientGroup.mk' (N₁.subgroupOf N₀)))
  refine ⟨φ', ψ, ?_, ?_, ?_, ?_⟩
  · exact e.toEquiv.surjective.comp
      (θ.toEquiv.surjective.comp (a5Rho hDN0 hDN1).rangeRestrict_surjective)
  · exact γ.toEquiv.surjective.comp
      (hβ'bij.2.comp (QuotientGroup.mk'_surjective (N₁.subgroupOf N₀)))
  · have h1 : ψ.ker = (β'.comp (QuotientGroup.mk' (N₁.subgroupOf N₀))).ker := by
      rw [show ψ = γ.toMonoidHom.comp (β'.comp (QuotientGroup.mk' (N₁.subgroupOf N₀)))
        from rfl]
      exact MonoidHom.ker_comp_of_injective _ _ γ.injective
    have h2 : (β'.comp (QuotientGroup.mk' (N₁.subgroupOf N₀))).ker =
        (QuotientGroup.mk' (N₁.subgroupOf N₀)).ker :=
      MonoidHom.ker_comp_of_injective _ _ hβ'bij.1
    rw [h1, h2, QuotientGroup.ker_mk']
  · intro d n n' hn'
    have hπ := a5_bridge_pi hDN0 hDN1 hn'
    have hβeq' : β' (a5Rho hDN0 hDN1 d (QuotientGroup.mk' (N₁.subgroupOf N₀) n)) =
        omegaMinusAct 1 (θ ((a5Rho hDN0 hDN1).rangeRestrict d))
          (β' (QuotientGroup.mk' (N₁.subgroupOf N₀) n)) :=
      hβ'eq ((a5Rho hDN0 hDN1).rangeRestrict d) (QuotientGroup.mk' (N₁.subgroupOf N₀) n)
    show γ (β' (QuotientGroup.mk' (N₁.subgroupOf N₀) n')) =
      CFSG.Quasithin.G6.coreAct 5 (φ' d) (γ (β' (QuotientGroup.mk' (N₁.subgroupOf N₀) n)))
    rw [← hπ, hβeq', hγeq]
    rfl

end A5MinusModuleHelpers

theorem a5MinusModule : A5MinusModule := by
  intro G _ _ D N₀ N₁ hN1le h2grp hDN0 hDN1 hcomm hsq hidx hirr hφex hdex
  obtain ⟨φ, hφsurj, hφker⟩ := hφex
  obtain ⟨d, hdD, hd3, hdidx⟩ := hdex
  have hN₀norm : N₀ ≤ Subgroup.normalizer (N₁ : Set G) := a5_N₀_le_normalizer_N₁ hN1le hcomm
  haveI hN₁normal : (N₁.subgroupOf N₀).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hN₀norm
  have hchief : CFSG.ABGLocalTools.IsChiefFactorUnder 2 D N₀ N₁ :=
    a5_isChiefFactor hN1le hDN0 hDN1 hcomm hsq hidx hirr
  let V := A5Sec N₀ N₁
  haveI hElem : IsElementaryAbelian 2 V := hchief.isElementaryAbelian
  letI hCommGroup : CommGroup V :=
    { (inferInstance : Group V) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := V)).comm a b }
  have hV2 : ∀ v : V, v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hElem.exponent_dvd_p
  have hρd_ne : a5Rho hDN0 hDN1 ⟨d, hdD⟩ ≠ 1 :=
    a5_rho_d_ne_one hN1le h2grp hDN0 hDN1 hN₀norm hdD hd3 hdidx
  have hC_not_le : ¬ (N₀ ⊓ Subgroup.centralizer ({d} : Set G)) ≤ N₁ :=
    a5_centralizer_not_le hdidx hidx
  obtain ⟨c, hc, hcN1⟩ := SetLike.not_le_iff_exists.mp hC_not_le
  have hfix_exists : ∃ v : V, v ≠ 1 ∧ a5Rho hDN0 hDN1 ⟨d, hdD⟩ v = v :=
    a5_exists_fixed hDN0 hDN1 hdD hc hcN1
  have hGiso : Nonempty (↥(a5G' hDN0 hDN1) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq 2)) :=
    a5_nonempty_G'_equiv_SL hDN0 hDN1 hφsurj hφker
  have hirrV : ∀ A : Subgroup V, GInv (a5G' hDN0 hDN1) A → A = ⊥ ∨ A = ⊤ :=
    fun A hA => a5_GInv_eq_bot_or_top hN1le hDN0 hDN1 hirr A hA
  have hcard : Nat.card V ≤ 2 ^ (2 * 2) := a5_card_sec_le hidx
  have htriv_false : ¬ ∀ g ∈ a5G' hDN0 hDN1, ∀ v : V, g v = v :=
    fun h => a5_not_trivial_action hDN0 hDN1 hdD hρd_ne h
  have hnat_false : ¬ CFSG.CGT.PushingUpLit.BHS6.IsNatSectionBy (slAct 2)
      (a5G' hDN0 hDN1) ⊤ ⊥ := by
    intro hnat
    obtain ⟨hg3, hg1⟩ := a5_rangeRestrict_d_pow_three hDN0 hDN1 hdD hd3 hρd_ne
    obtain ⟨v0, hv0ne, hv0fix⟩ := hfix_exists
    exact slNat_no_fixed_of_order_three hnat hg3 hg1 hv0ne hv0fix
  have hOmega : CFSG.CGT.PushingUpLit.BHS6.IsNatSectionBy (omegaMinusAct 1)
      (a5G' hDN0 hDN1) ⊤ ⊥ :=
    a5_isNatSection_omegaMinus (a5G' hDN0 hDN1) hV2 hGiso hirrV hcard htriv_false hnat_false
  obtain ⟨θ, β', hβ'bij, hβ'eq⟩ := a5_exists_beta hOmega
  exact natA5Sec_of_bridge hDN0 hDN1 θ β' hβ'bij hβ'eq

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
