module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22br4_isKGroup_mbar_of_isKGroup (M V : Subgroup G) (hM : CFSG.Open.IsKGroup ↥M) :
    CFSG.Open.IsKGroup (MBar M V) :=
  hM.quotient _

theorem uc22br4_isKGroup_mbar (hG : CFSG.Open.IsKProper G) (M V : Subgroup G) (hM : M ≠ ⊤) :
    CFSG.Open.IsKGroup (MBar M V) :=
  uc22br4_isKGroup_mbar_of_isKGroup M V (hG.isKGroup M hM)

theorem uc22br4_isKGroup_catalog_of_open {X : Type} [Group X] [Finite X]
    (h : CFSG.Open.IsKGroup X) : CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple h

theorem uc22br4_isKGroup_mbar_catalog (hG : CFSG.Open.IsKProper G) (M V : Subgroup G)
    (hM : M ≠ ⊤) : CFSG.IsKGroup (MBar M V) :=
  uc22br4_isKGroup_catalog_of_open (uc22br4_isKGroup_mbar hG M V hM)

theorem uc22br4_M_ne_top (D : Data G) : D.M ≠ ⊤ := by
  haveI := D.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1

theorem uc22br4_isKGroup_mbar_data_catalog (D : Data G) (V : Subgroup G) :
    CFSG.IsKGroup (MBar D.M V) :=
  uc22br4_isKGroup_mbar_catalog D.standing.kProper D.M V (uc22br4_M_ne_top D)

@[expose] def uc22br4_phi (M V K : Subgroup G) (hKM : K ≤ M) : ↥K →* MBar M V :=
  (QuotientGroup.mk' (kerAct M V).normalCore).comp (Subgroup.inclusion hKM)

theorem uc22br4_phi_apply (M V K : Subgroup G) (hKM : K ≤ M) (k : ↥K) :
    uc22br4_phi M V K hKM k = (QuotientGroup.mk ⟨(k : G), hKM k.2⟩ : MBar M V) := rfl

theorem uc22br4_range_inclusion {K M : Subgroup G} (hKM : K ≤ M) :
    (Subgroup.inclusion hKM).range = K.subgroupOf M := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact k.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem uc22br4_range_phi (M V K : Subgroup G) (hKM : K ≤ M) :
    (uc22br4_phi M V K hKM).range = mbarImage M V K := by
  unfold uc22br4_phi mbarImage
  rw [MonoidHom.range_comp, uc22br4_range_inclusion hKM]

theorem uc22br4_ker_phi (M V K : Subgroup G) (hV : M ≤ normalizer (V : Set G)) (hKM : K ≤ M) :
    (uc22br4_phi M V K hKM).ker = (centralizer (V : Set G)).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, uc22br4_phi_apply, uc22br_gt_mk_eq_one_iff hV, Subgroup.mem_subgroupOf]

theorem uc22br4_card_mbarImage (M V K : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hKM : K ≤ M) :
    Nat.card (mbarImage M V K) = ((centralizer (V : Set G)).subgroupOf K).index := by
  rw [← uc22br4_range_phi M V K hKM, ← uc22br4_ker_phi M V K hV hKM, Subgroup.index_ker]

theorem uc22br4_mbarImage_eq_bot_iff (M V K : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hKM : K ≤ M) : mbarImage M V K = ⊥ ↔ K ≤ centralizer (V : Set G) := by
  rw [← uc22br4_range_phi M V K hKM, MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff,
    uc22br4_ker_phi M V K hV hKM]
  constructor
  · intro h x hx
    have : (⟨x, hx⟩ : ↥K) ∈ (centralizer (V : Set G)).subgroupOf K := by rw [h]; trivial
    exact this
  · intro h
    rw [eq_top_iff]
    intro x _
    exact h x.2

theorem uc22br4_mbarImage_normal (M V K : Subgroup G) (hKM : K ≤ M)
    (hMK : M ≤ normalizer (K : Set G)) : (mbarImage M V K).Normal := by
  have hn : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMK
  exact hn.map _ (QuotientGroup.mk'_surjective _)

theorem uc22br4_pCore_bot_iff (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G)) :
    CFSG.pCore 2 (MBar M V) = ⊥ ↔ TwoReduced M V := by
  constructor
  · intro h K hKM hMK _ ⟨n, hn⟩
    have hnorm : (mbarImage M V K).Normal := uc22br4_mbarImage_normal M V K hKM hMK
    have hp : IsPGroup 2 ↥(mbarImage M V K) :=
      IsPGroup.of_card (n := n) (by rw [uc22br4_card_mbarImage M V K hV hKM, hn])
    have hle : mbarImage M V K ≤ CFSG.pCore 2 (MBar M V) := le_sSup ⟨hnorm, hp⟩
    rw [h, le_bot_iff] at hle
    exact (uc22br4_mbarImage_eq_bot_iff M V K hV hKM).1 hle
  · intro h
    set π : ↥M →* MBar M V := QuotientGroup.mk' (kerAct M V).normalCore with hπ
    set Q := CFSG.pCore 2 (MBar M V) with hQ
    set K : Subgroup G := (Q.comap π).map M.subtype with hK
    have hKM : K ≤ M := Subgroup.map_subtype_le _
    have hKsub : K.subgroupOf M = Q.comap π :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    have hMK : M ≤ normalizer (K : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKM, hKsub]
      exact Subgroup.Normal.comap CFSG.pCore_normal π
    have himg : mbarImage M V K = Q := by
      unfold mbarImage
      rw [hKsub]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Q
    have hcard : ∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n := by
      rw [← uc22br4_card_mbarImage M V K hV hKM, himg]
      exact IsPGroup.exists_card_eq CFSG.pCore_isPGroup
    have hCK : M ⊓ centralizer (V : Set G) ≤ K := by
      rintro x ⟨hxM, hxC⟩
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      show π ⟨x, hxM⟩ ∈ Q
      have : π ⟨x, hxM⟩ = 1 := (uc22br_gt_mk_eq_one_iff hV ⟨x, hxM⟩).2 hxC
      rw [this]
      exact Q.one_mem
    have hKC := h K hKM hMK hCK hcard
    have := (uc22br4_mbarImage_eq_bot_iff M V K hV hKM).2 hKC
    rwa [himg] at this

theorem uc22br4_injective (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod)
    (hc : ConjModule M V e ρ) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro t ht
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective t
  rw [uc22br_gt_mk_eq_one_iff hV, Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := (uc22br_gt_conj_iff M V hV e ρ hc m ⟨v, hv⟩).2 (by rw [ht]; rfl)
  have h2 : (m : G) * v = v * m := by
    have := congrArg (· * (m : G)) h1
    simpa [mul_assoc] using this
  exact h2.symm

@[expose] def uc22br4_conjAut (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G)) :
    ↥M →* MulAut ↥V where
  toFun m :=
    { toFun := fun v => ⟨(m : G) * v * (m : G)⁻¹, uc22br_gt_conj_mem hV m.2 v.2⟩
      invFun := fun v => ⟨(m : G)⁻¹ * v * (m : G), by
        have := uc22br_gt_conj_mem hV (inv_mem m.2) v.2
        simpa using this⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [mul_assoc]

open scoped IsMulCommutative in
theorem uc22br4_exists_conjModule (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hel : CFSG.Open.IsElemAbelian 2 V) :
    ∃ (Vmod : Type) (_ : AddCommGroup Vmod) (_ : Module (ZMod 2) Vmod) (_ : Finite Vmod)
      (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod),
      ConjModule M V e ρ := by
  haveI : IsMulCommutative ↥V := hel.1
  letI : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule (n := 2) (fun x => by
    apply Additive.toMul.injective
    simp only [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hel.2 _ x.toMul.2))
  let T : ↥M →* Module.End (ZMod 2) (Additive ↥V) :=
    { toFun := fun m => AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk' (fun x : Additive ↥V => Additive.ofMul (uc22br4_conjAut M V hV m x.toMul))
          (fun x y => by simp))
      map_one' := by
        ext x
        simp [AddMonoidHom.toZModLinearMap]
      map_mul' := fun a b => by
        ext x
        simp [AddMonoidHom.toZModLinearMap] }
  have hker : (kerAct M V).normalCore ≤ T.ker := by
    intro x hx
    have hx' : x ∈ kerAct M V := Subgroup.normalCore_le _ hx
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun v => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    have hxc : (x : G) ∈ centralizer (V : Set G) := Subgroup.mem_subgroupOf.1 hx'
    have hcomm := Subgroup.mem_centralizer_iff.1 hxc (v.toMul : G) v.toMul.2
    show (x : G) * (v.toMul : G) * (x : G)⁻¹ = (v.toMul : G)
    rw [← hcomm]
    group
  let ρ : Representation (ZMod 2) (MBar M V) (Additive ↥V) :=
    QuotientGroup.lift (kerAct M V).normalCore T hker
  let e : ↥V ≃* Multiplicative (Additive ↥V) :=
    { toFun := fun v => Multiplicative.ofAdd (Additive.ofMul v)
      invFun := fun w => Additive.toMul (Multiplicative.toAdd w)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Additive ↥V, inferInstance, inferInstance, inferInstance, e, ρ, ?_⟩
  intro m v w hw
  have hρ : ρ (QuotientGroup.mk m) = T m := QuotientGroup.lift_mk _ _ _
  rw [hρ]
  have hw' : w = uc22br4_conjAut M V hV m v := Subtype.ext hw
  rw [hw']
  rfl

theorem uc22br4_isElemAbelian_of_equiv (V : Subgroup G) {Vmod : Type} [AddCommGroup Vmod]
    [Module (ZMod 2) Vmod] (e : ↥V ≃* Multiplicative Vmod) : CFSG.Open.IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact e.injective (by rw [map_mul, map_mul, mul_comm])
  · have h : (⟨x, hx⟩ : ↥V) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact (show ((2 : ℕ) : ZMod 2) = 0 from rfl) ▸ zero_smul _ _
    exact congrArg Subtype.val h

section Irr

variable {M V : Subgroup G} {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]

@[expose] def uc22br4_addSub (e : ↥V ≃* Multiplicative Vmod) (W : Subgroup G) :
    AddSubgroup Vmod where
  carrier := {x | ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) ∈ W}
  add_mem' := fun {x y} hx hy => by
    show ((e.symm (Multiplicative.ofAdd (x + y)) : ↥V) : G) ∈ W
    have : e.symm (Multiplicative.ofAdd (x + y)) =
        e.symm (Multiplicative.ofAdd x) * e.symm (Multiplicative.ofAdd y) := by
      rw [ofAdd_add, map_mul]
    rw [this]
    exact W.mul_mem hx hy
  zero_mem' := by
    show ((e.symm (Multiplicative.ofAdd (0 : Vmod)) : ↥V) : G) ∈ W
    rw [ofAdd_zero, map_one]
    exact W.one_mem
  neg_mem' := fun {x} hx => by
    show ((e.symm (Multiplicative.ofAdd (-x)) : ↥V) : G) ∈ W
    have : e.symm (Multiplicative.ofAdd (-x)) = (e.symm (Multiplicative.ofAdd x))⁻¹ := by
      rw [ofAdd_neg, map_inv]
    rw [this]
    exact W.inv_mem hx

theorem uc22br4_symm_rho (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) (m : ↥M) (x : Vmod) :
    ((e.symm (Multiplicative.ofAdd (ρ (QuotientGroup.mk m) x)) : ↥V) : G) =
      (m : G) * ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) * (m : G)⁻¹ := by
  set v : ↥V := e.symm (Multiplicative.ofAdd x) with hv
  have hmem := uc22br_gt_conj_mem hV m.2 v.2
  have h1 := hc m v ⟨(m : G) * v * (m : G)⁻¹, hmem⟩ rfl
  have hev : Multiplicative.toAdd (e v) = x := by simp [hv]
  rw [hev] at h1
  have h2 : (⟨(m : G) * v * (m : G)⁻¹, hmem⟩ : ↥V) =
      e.symm (Multiplicative.ofAdd (ρ (QuotientGroup.mk m) x)) := by
    rw [← h1]; simp
  exact (congrArg Subtype.val h2).symm

@[expose] def uc22br4_subrep (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) (W : Subgroup G)
    (hW : M ≤ normalizer (W : Set G)) : Subrepresentation ρ where
  toSubmodule := AddSubgroup.toZModSubmodule 2 (uc22br4_addSub e W)
  apply_mem_toSubmodule := by
    intro g x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    show ((e.symm (Multiplicative.ofAdd (ρ (QuotientGroup.mk m) x)) : ↥V) : G) ∈ W
    rw [uc22br4_symm_rho hV e ρ hc m x]
    exact (mem_normalizer_iff.1 (hW m.2) _).1 hx

theorem uc22br4_mem_subrep (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) (W : Subgroup G)
    (hW : M ≤ normalizer (W : Set G)) (x : Vmod) :
    x ∈ uc22br4_subrep hV e ρ hc W hW ↔ ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) ∈ W :=
  Iff.rfl

@[expose] def uc22br4_subgrp (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (S : Subrepresentation ρ) : Subgroup G where
  carrier := {g | ∃ h : g ∈ V, Multiplicative.toAdd (e ⟨g, h⟩) ∈ S}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨V.mul_mem ha1 hb1, ?_⟩
    have : e ⟨a * b, V.mul_mem ha1 hb1⟩ = e ⟨a, ha1⟩ * e ⟨b, hb1⟩ := by
      rw [← map_mul]; rfl
    rw [this, toAdd_mul]
    exact S.toSubmodule.add_mem ha2 hb2
  one_mem' := by
    refine ⟨V.one_mem, ?_⟩
    have : e ⟨1, V.one_mem⟩ = 1 := by
      rw [← map_one e]; rfl
    rw [this, toAdd_one]
    exact S.toSubmodule.zero_mem
  inv_mem' := fun {a} ha => by
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨V.inv_mem ha1, ?_⟩
    have : e ⟨a⁻¹, V.inv_mem ha1⟩ = (e ⟨a, ha1⟩)⁻¹ := by
      rw [← map_inv]; rfl
    rw [this, toAdd_inv]
    exact S.toSubmodule.neg_mem ha2

theorem uc22br4_subgrp_le (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (S : Subrepresentation ρ) :
    uc22br4_subgrp e ρ S ≤ V := fun _ hg => hg.1

theorem uc22br4_subgrp_normalizer (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ)
    (S : Subrepresentation ρ) : M ≤ normalizer (uc22br4_subgrp e ρ S : Set G) := by
  have key : ∀ m ∈ M, ∀ g ∈ uc22br4_subgrp e ρ S, m * g * m⁻¹ ∈ uc22br4_subgrp e ρ S := by
    intro m hm g hg
    obtain ⟨hgV, hgS⟩ := hg
    have hmem := uc22br_gt_conj_mem hV hm hgV
    refine ⟨hmem, ?_⟩
    have h1 := hc ⟨m, hm⟩ ⟨g, hgV⟩ ⟨m * g * m⁻¹, hmem⟩ rfl
    rw [h1, toAdd_ofAdd]
    exact S.apply_mem_toSubmodule _ hgS
  intro m hm
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key m hm h, fun hh => ?_⟩
  have := key m⁻¹ (inv_mem hm) _ hh
  simpa [mul_assoc] using this

end Irr

theorem uc22br4_isIrreducible_iff (M V : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod)
    (hc : ConjModule M V e ρ) : ρ.IsIrreducible ↔ V ≠ ⊥ ∧ IrrOn M V := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hV0
      have hzero : ∀ x : Vmod, x = 0 := by
        intro x
        have h1 : ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) ∈ V := (e.symm _).2
        have h1' : ∀ g ∈ V, g = 1 := fun g hg => Subgroup.mem_bot.1 (hV0 ▸ hg)
        have h2 : e.symm (Multiplicative.ofAdd x) = 1 := Subtype.ext (h1' _ h1)
        have h3 : Multiplicative.ofAdd x = e 1 := by
          rw [← h2]; simp
        rw [map_one] at h3
        exact Multiplicative.ofAdd.injective h3
      apply bot_ne_top (α := Subrepresentation ρ)
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.ext
      intro x
      rw [hzero x]
      exact ⟨fun _ => trivial, fun _ => Submodule.zero_mem _⟩
    · intro W hWV hW
      rcases IsSimpleOrder.eq_bot_or_eq_top (uc22br4_subrep hV e ρ hc W hW) with h1 | h1
      · left
        rw [eq_bot_iff]
        intro w hw
        have hwV : w ∈ V := hWV hw
        have hx : Multiplicative.toAdd (e ⟨w, hwV⟩) ∈ uc22br4_subrep hV e ρ hc W hW := by
          rw [uc22br4_mem_subrep]
          simpa using hw
        rw [h1] at hx
        have hx0 : Multiplicative.toAdd (e ⟨w, hwV⟩) = 0 := hx
        have h2 : e ⟨w, hwV⟩ = 1 := by
          have := congrArg Multiplicative.ofAdd hx0
          simpa using this
        have h3 : (⟨w, hwV⟩ : ↥V) = 1 := e.injective (by rw [h2, map_one])
        exact (Subgroup.mem_bot).2 (congrArg Subtype.val h3)
      · right
        refine le_antisymm hWV fun v hv => ?_
        have hx : Multiplicative.toAdd (e ⟨v, hv⟩) ∈ uc22br4_subrep hV e ρ hc W hW := by
          rw [h1]; trivial
        rw [uc22br4_mem_subrep] at hx
        simpa using hx
  · rintro ⟨hne, hirr⟩
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
      intro hbt
      have hx : Multiplicative.toAdd (e a) ∈ (⊤ : Subrepresentation ρ) := trivial
      rw [← hbt] at hx
      have hx0 : Multiplicative.toAdd (e a) = 0 := hx
      apply ha
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective hx0
    haveI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbt⟩⟩
    refine { eq_bot_or_eq_top := fun S => ?_ }
    rcases hirr (uc22br4_subgrp e ρ S) (uc22br4_subgrp_le e ρ S)
      (uc22br4_subgrp_normalizer hV e ρ hc S) with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have hg : ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) ∈ uc22br4_subgrp e ρ S := by
        refine ⟨(e.symm _).2, ?_⟩
        simpa using hx
      rw [h1, Subgroup.mem_bot] at hg
      have h2 : e.symm (Multiplicative.ofAdd x) = 1 := Subtype.ext hg
      have h3 : Multiplicative.ofAdd x = e 1 := by rw [← h2]; simp
      rw [map_one] at h3
      exact (Submodule.mem_bot (ZMod 2)).2 (Multiplicative.ofAdd.injective h3)
    · right
      rw [eq_top_iff]
      intro x _
      have hg : ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) ∈ uc22br4_subgrp e ρ S := by
        rw [h1]; exact (e.symm _).2
      obtain ⟨hgV, hgS⟩ := hg
      simpa using hgS

theorem uc22br4_isQuasisimple_of_surjective {S T : Type*} [Group S] [Group T]
    (hS : CFSG.Open.IsQuasisimple S) (ψ : S →* T) (hψ : Function.Surjective ψ) [Nontrivial T] :
    CFSG.Open.IsQuasisimple T := by
  obtain ⟨hperf, hsimp⟩ := hS
  haveI : Group.IsPerfect S := ⟨hperf⟩
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective hψ
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have hle : center S ≤ (center T).comap ψ := fun z hz =>
    Subgroup.map_center_le_center hψ (Subgroup.mem_map_of_mem ψ hz)
  let ψ' : S ⧸ center S →* T ⧸ center T := QuotientGroup.map (center S) (center T) ψ hle
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨s, rfl⟩ := hψ t
    exact ⟨QuotientGroup.mk s, rfl⟩
  haveI := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ'.ker with h | h
  · have hinj : Function.Injective ψ' := (MonoidHom.ker_eq_bot_iff ψ').1 h
    exact (MulEquiv.ofBijective ψ' ⟨hinj, hψ'⟩).isSimpleGroup_congr.1 hsimp
  · exfalso
    have hcomm : ∀ a b : T, a * b = b * a := by
      intro a b
      have h1 : (QuotientGroup.mk a : T ⧸ center T) = 1 := by
        obtain ⟨z, hz⟩ := hψ' (QuotientGroup.mk a)
        rw [← hz]
        exact (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top z))
      have ha : a ∈ center T := (QuotientGroup.eq_one_iff a).1 h1
      exact ((Subgroup.mem_center_iff.1 ha b)).symm
    haveI : IsMulCommutative T := ⟨⟨hcomm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative T ‹_›

theorem uc22br4_conj_mem_map_of_characteristic {Y : Type*} [Group Y] {X : Subgroup Y}
    {D : Subgroup X} [hD : D.Characteristic] {g : Y} (hg : g ∈ normalizer (X : Set Y)) {x : Y}
    (hx : x ∈ D.map X.subtype) : g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem uc22br4_map_pCore_le_pCore_of_isSubnormal {Y : Type*} [Group Y] (p : ℕ) {K : Subgroup Y}
    (hK : K.IsSubnormal) : (CFSG.pCore p K).map K.subtype ≤ CFSG.pCore p Y := by
  have key : ∀ {X Z : Subgroup Y}, X ≤ Z → Z ≤ normalizer (X : Set Y) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Z).map Z.subtype := by
    intro X Z hXZ hZN
    have hLZ : (CFSG.pCore p X).map X.subtype ≤ Z := (Subgroup.map_subtype_le _).trans hXZ
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Z ≤ CFSG.pCore p Z := by
      apply le_sSup
      refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using uc22br4_conj_mem_map_of_characteristic (hZN z.2) hl
      · exact ((CFSG.pCore_isPGroup (p := p) (G := X)).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLZ).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Z).map Z.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLZ).symm
      _ ≤ (CFSG.pCore p Z).map Z.subtype := Subgroup.map_mono hle
  induction hK with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => uc22br4_conj_mem_map_of_characteristic ?_ hl⟩,
      (CFSG.pCore_isPGroup (p := p) (G := (⊤ : Subgroup Y))).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Z hXZ hZ hN ih =>
    exact (key hXZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hXZ).mp hN)).trans ih

theorem uc22br4_isComponentOf_mbarImage (M V K : Subgroup G) (hV : M ≤ normalizer (V : Set G))
    (hO2 : CFSG.pCore 2 (MBar M V) = ⊥) (hK : K ∈ calC M) (hKV : ¬ K ≤ centralizer (V : Set G)) :
    CFSG.Open.IsComponentOf (mbarImage M V K) ⊤ := by
  obtain ⟨hsnK, -, hqs⟩ := hK
  have hKM : K ≤ M := hsnK.le
  have hsn : CFSG.Open.IsSubnormal (mbarImage M V K) ⊤ := by
    have h1 := (hsnK.comap M.subtype).map (QuotientGroup.mk' (kerAct M V).normalCore)
    have h2 : M.comap M.subtype = ⊤ := Subgroup.subgroupOf_self M
    rw [h2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    exact h1
  refine ⟨le_top, hsn, ?_⟩
  set φ := uc22br4_phi M V K hKM with hφ
  have hrange := uc22br4_range_phi M V K hKM
  have hφle : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hsnr : φ.range.IsSubnormal := by
      rw [hrange]
      exact CFSG.Open.IsSubnormal.top_iff.1 hsn
    have h1 := uc22br4_map_pCore_le_pCore_of_isSubnormal 2 hsnr
    rw [hO2] at h1
    have hnorm : ((CFSG.pCore 2 ↥K).map φ.rangeRestrict).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal _ φ.rangeRestrict_surjective
    have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K).map φ.rangeRestrict) :=
      CFSG.pCore_isPGroup.map φ.rangeRestrict
    have hle2 : (CFSG.pCore 2 ↥K).map φ.rangeRestrict ≤ CFSG.pCore 2 ↥φ.range :=
      le_sSup ⟨hnorm, hp⟩
    have h2 : φ.rangeRestrict x ∈ CFSG.pCore 2 ↥φ.range :=
      hle2 (Subgroup.mem_map_of_mem _ hx)
    have h3 : φ x ∈ (CFSG.pCore 2 ↥φ.range).map φ.range.subtype := ⟨φ.rangeRestrict x, h2, rfl⟩
    have h4 := h1 h3
    simpa using h4
  have hne : φ.range ≠ ⊥ := by
    rw [hrange]
    intro h
    exact hKV ((uc22br4_mbarImage_eq_bot_iff M V K hV hKM).1 h)
  haveI : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  let ψ : Bar2 K →* ↥φ.range :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) φ.rangeRestrict (by rwa [MonoidHom.ker_rangeRestrict])
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨k, hk⟩ := φ.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk k, by simpa [ψ] using hk⟩
  have := uc22br4_isQuasisimple_of_surjective hqs ψ hψ
  rw [← hrange]
  exact this

theorem uc22br4_conjClosure_eq (M K : Subgroup G) :
    conjClosure M K = ⨆ g : ↥M, K.map (MulAut.conj (g : G)).toMonoidHom := by
  unfold conjClosure conjSetOf
  apply le_antisymm
  · refine iSup₂_le fun K' hK' => ?_
    obtain ⟨g, hg, rfl⟩ := hK'
    exact le_iSup (fun g : ↥M => K.map (MulAut.conj (g : G)).toMonoidHom) ⟨g, hg⟩
  · refine iSup_le fun g => ?_
    have hmem : K.map (MulAut.conj (g : G)).toMonoidHom ∈
        {K' | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom} := ⟨g, g.2, rfl⟩
    exact le_iSup₂_of_le (K.map (MulAut.conj (g : G)).toMonoidHom) hmem le_rfl

theorem uc22br4_subgroupOf_iSup {ι : Type*} (M : Subgroup G) (X : ι → Subgroup G)
    (hX : ∀ i, X i ≤ M) : (⨆ i, X i).subgroupOf M = ⨆ i, (X i).subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le (iSup_le hX)]
  simp_rw [Subgroup.map_subgroupOf_eq_of_le (hX _)]

theorem uc22br4_subgroupOf_map_conj (M K : Subgroup G) (g : ↥M) :
    (K.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf M =
      (K.subgroupOf M).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyM : y ∈ M := by
      have : y = (g : G)⁻¹ * (x : G) * (g : G) := by rw [← hyx]; group
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem g.2) x.2) g.2
    refine ⟨⟨y, hyM⟩, hy, ?_⟩
    exact Subtype.ext (by simpa using hyx)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem uc22br4_mbarImage_map_conj (M V K : Subgroup G) (g : ↥M) :
    mbarImage M V (K.map (MulAut.conj (g : G)).toMonoidHom) =
      (mbarImage M V K).map (MulAut.conj (QuotientGroup.mk g : MBar M V)).toMonoidHom := by
  unfold mbarImage
  rw [uc22br4_subgroupOf_map_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem uc22br4_lgConj_mbarImage (M V K : Subgroup G) (hKM : K ≤ M) :
    Ext.lgConj (mbarImage M V K) = mbarImage M V (conjClosure M K) := by
  have hXM : ∀ g : ↥M, K.map (MulAut.conj (g : G)).toMonoidHom ≤ M := by
    rintro g _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem g.2 (hKM hy)) (M.inv_mem g.2)
  unfold Ext.lgConj
  rw [← (QuotientGroup.mk'_surjective (kerAct M V).normalCore).iSup_comp,
    uc22br4_conjClosure_eq]
  unfold mbarImage
  rw [uc22br4_subgroupOf_iSup M _ hXM, Subgroup.map_iSup]
  refine iSup_congr fun g => ?_
  have := uc22br4_mbarImage_map_conj M V K g
  unfold mbarImage at this
  rw [this]
  rfl

theorem uc22br4_lgConj_eq_of_normal {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal] :
    Ext.lgConj L = L := by
  unfold Ext.lgConj
  apply le_antisymm
  · refine iSup_le fun g => ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ‹L.Normal›.conj_mem y hy g
  · exact le_iSup_of_le 1 fun x hx => ⟨x, hx, by simp⟩

theorem uc22br4_lgConj_mbarImage_of_normal (M V K : Subgroup G) (hKM : K ≤ M)
    (hMK : M ≤ normalizer (K : Set G)) :
    Ext.lgConj (mbarImage M V K) = mbarImage M V K :=
  haveI := uc22br4_mbarImage_normal M V K hKM hMK
  uc22br4_lgConj_eq_of_normal _

theorem uc22br4_numConj_mbarImage_le (M V K : Subgroup G) :
    F05.numConj (mbarImage M V K) ≤ (conjSetOf M K).ncard := by
  have hsub : {X : Subgroup (MBar M V) | ∃ g : MBar M V,
      X = (mbarImage M V K).map (MulAut.conj g).toMonoidHom} ⊆
      (fun X => mbarImage M V X) '' conjSetOf M K := by
    rintro X ⟨gb, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    exact ⟨K.map (MulAut.conj (g : G)).toMonoidHom, ⟨g, g.2, rfl⟩,
      uc22br4_mbarImage_map_conj M V K g⟩
  calc F05.numConj (mbarImage M V K)
      ≤ ((fun X => mbarImage M V X) '' conjSetOf M K).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (conjSetOf M K).ncard := Set.ncard_image_le (Set.toFinite _)

theorem uc22br4_mBarGT_mono (M V₀ V : Subgroup G) {m n : ℕ} (h : MBarGT M V₀ V n)
    (hmn : m ≤ n) : MBarGT M V₀ V m := by
  have hp : 2 ^ (m + 1) ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun x hx h1 h2 => ?_, fun h3 => ?_⟩
  · exact le_trans (Nat.mul_le_mul_right _ hp) (h.1 x hx h1 h2)
  · exact le_trans (Nat.mul_le_mul_right _ hp) (h.2 h3)

@[expose] def uc22br4_K147Concl {H : Type} [Group H] [Finite H] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) H W) (L : Subgroup H) (n : ℕ) :
    Prop :=
  ((∀ g : H, g ∉ normalizer (L : Set H) →
      commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) ∧
    (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
      (∃ k : ℕ, n = 2 * k ∧
        (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
          SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
      (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8))) ∨
  NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n

theorem uc22br4_k147_apply (hK147 : K147) (D : Data G) {V : Subgroup G}
    (hVM : D.M ≤ normalizer (V : Set G)) (hne : V ≠ ⊥) (hirr : IrrOn D.M V)
    (hred : TwoReduced D.M V)
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar D.M V) Vmod)
    (hc : ConjModule D.M V e ρ) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKV : ¬ K ≤ centralizer (V : Set G)) {n : ℕ} (hcase : Case147 (mbarImage D.M V K) n)
    (hgt : ¬ MBarGT D.M ⊥ V (n + 1)) :
    uc22br4_K147Concl ρ (mbarImage D.M V K) n := by
  have hpc : CFSG.pCore 2 (MBar D.M V) = ⊥ := (uc22br4_pCore_bot_iff D.M V hVM).2 hred
  have hmg : F05.mGV ρ ≤ n + 1 := by
    have h := mbarGT_bot_iff_lt_mGV D.M V hVM (uc22br4_isElemAbelian_of_equiv V e) e ρ hc (n + 1)
    exact not_lt.1 fun hlt => hgt (h.2 hlt)
  exact hK147 (MBar D.M V) Vmod ρ (uc22br4_isKGroup_mbar_data_catalog D V) hpc
    (uc22br4_injective D.M V hVM e ρ hc) ((uc22br4_isIrreducible_iff D.M V hVM e ρ hc).2 ⟨hne, hirr⟩)
    (mbarImage D.M V K) (uc22br4_isComponentOf_mbarImage D.M V K hVM hpc hK hKV) n hcase hmg

theorem uc22br4_k147_apply_ctx (hK147 : K147) (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch)
    (hred : TwoReduced D.M c.V)
    {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
    (e : ↥c.V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar D.M c.V) Vmod)
    (hc : ConjModule D.M c.V e ρ) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKV : ¬ K ≤ centralizer (c.V : Set G)) {n : ℕ} (hcase : Case147 (mbarImage D.M c.V K) n)
    (h9 : ¬ MBarGT D.M ⊥ c.V (c.n + 1)) (hn : c.n ≤ n) :
    uc22br4_K147Concl ρ (mbarImage D.M c.V K) n :=
  uc22br4_k147_apply hK147 D c.hVM c.hVne c.hVirr hred e ρ hc hK hKV hcase
    (fun h => h9 (uc22br4_mBarGT_mono D.M ⊥ c.V h (by omega)))

theorem uc22br4_k147_exists (hK147 : K147) (D : Data G) {V : Subgroup G}
    (hVM : D.M ≤ normalizer (V : Set G)) (hel : CFSG.Open.IsElemAbelian 2 V) (hne : V ≠ ⊥)
    (hirr : IrrOn D.M V) (hred : TwoReduced D.M V) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKV : ¬ K ≤ centralizer (V : Set G)) {n : ℕ} (hcase : Case147 (mbarImage D.M V K) n)
    (hgt : ¬ MBarGT D.M ⊥ V (n + 1)) :
    ∃ (Vmod : Type) (_ : AddCommGroup Vmod) (_ : Module (ZMod 2) Vmod) (_ : Finite Vmod)
      (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar D.M V) Vmod),
      ConjModule D.M V e ρ ∧ uc22br4_K147Concl ρ (mbarImage D.M V K) n := by
  obtain ⟨Vmod, i1, i2, i3, e, ρ, hc⟩ := uc22br4_exists_conjModule D.M V hVM hel
  exact ⟨Vmod, i1, i2, i3, e, ρ, hc,
    uc22br4_k147_apply hK147 D hVM hne hirr hred e ρ hc hK hKV hcase hgt⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
