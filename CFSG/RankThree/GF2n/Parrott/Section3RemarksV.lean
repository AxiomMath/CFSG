module

public import CFSG.RankThree.GF2n.Parrott.CaseII

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem z_mem_J (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) : z ∈ J z := by
  have hz : z ∈ ⁅J z, J z⁆ := by
    rw [hcomm]
    exact Subgroup.mem_zpowers z
  exact Subgroup.commutator_le_self (J z) hz

omit [Finite G] in
theorem centerIn_J_eq_zpowers (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) : centerIn (J z) = Subgroup.zpowers z := by
  rw [CFSG.centerIn_eq_map_center, ← hJ.2.1, hcomm]

omit [Finite G] in
theorem orderOf_z (hJ : IsExtraspecial2 (J z)) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) :
    orderOf z = 2 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [← hcomm]
    exact hJ.2.2
  rwa [Nat.card_zpowers] at hcard

theorem card_center_J (hJ : IsExtraspecial2 (J z)) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) :
    Nat.card ↥(Subgroup.center (J z)) = 2 := by
  have hZ : Nat.card (centerIn (J z)) = 2 := by
    rw [centerIn_J_eq_zpowers hJ hcomm, Nat.card_zpowers, orderOf_z hJ hcomm]
  rw [← QuotientV.centerIn_subgroupOf_eq_center]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : centerIn (J z) ≤ J z)).toEquiv).trans hZ

theorem centralizer_J_eq_centerIn (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) :
    H z ⊓ Subgroup.centralizer (J z : Set G) = centerIn (J z) := by
  apply le_antisymm
  · intro x hx
    exact ⟨hCHJ hx, hx.2⟩
  · intro x hx
    exact ⟨J_le_H hx.1, hx.2⟩

omit [Finite G] in
theorem mul_self_eq_one_of_mem_zpowers (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {c : G} (hc : c ∈ Subgroup.zpowers z) :
    c * c = 1 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_z hJ hcomm]
  have h1 : (⟨c, hc⟩ : Subgroup.zpowers z) ^ Nat.card (Subgroup.zpowers z) = 1 :=
    pow_card_eq_one'
  rw [hcard] at h1
  have := congrArg Subtype.val h1
  simpa [pow_two] using this

omit [Finite G] in
theorem zpowers_le_centralizer (x : H z) :
    Subgroup.zpowers z ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
  intro c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((commute_z_sigma_A (z := z) x).zpow_left k).eq

theorem commutator_mem_centerIn (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) (a b : J z) :
    ⁅(a : G), (b : G)⁆ ∈ centerIn (J z) := by
  have hmem : ⁅(a : G), (b : G)⁆ ∈ ⁅J z, J z⁆ :=
    Subgroup.commutator_mem_commutator a.2 b.2
  rw [hcomm] at hmem
  exact (Subgroup.zpowers_le_of_mem (H := centerIn (J z))
    ⟨z_mem_J hcomm, z_centralizes_J_A (z := z)⟩) hmem

theorem conjJ'_mul_inv_mem_centerIn (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {g : H z}
    (hg : (g : G) ∈ J z) (x : J z) :
    ((conjJ' z g x : J z) : G) * (x : G)⁻¹ ∈ centerIn (J z) := by
  have hc := commutator_mem_centerIn hcomm (⟨(g : G), hg⟩ : J z) x
  simpa [conjJ'_apply_coe, commutatorElement_def] using hc

theorem conjVA_apply_pi_eq (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {g : H z}
    (hg : (g : G) ∈ J z) (x : J z) :
    conjVA z g (QuotientV.pi z x) = QuotientV.pi z x := by
  rw [conjVA_mk]
  change (QuotientGroup.mk (conjJ' z g x) :
      J z ⧸ (centerIn (J z)).subgroupOf (J z)) = QuotientGroup.mk x
  rw [QuotientGroup.eq_iff_div_mem]
  rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
  exact conjJ'_mul_inv_mem_centerIn hcomm hg x

theorem isMulCommutative_V (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) :
    IsMulCommutative (QuotientV.V z) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  intro x hx
  apply Subgroup.mem_subgroupOf.mpr
  have hz_center : z ∈ centerIn (J z) := ⟨z_mem_J hcomm, z_centralizes_J_A (z := z)⟩
  have hzp : Subgroup.zpowers z ≤ centerIn (J z) := Subgroup.zpowers_le_of_mem hz_center
  have hx' : (x : G) ∈ ⁅J z, J z⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  rw [hcomm] at hx'
  exact hzp hx'

theorem pow_two_eq_one_V (hJ : IsExtraspecial2 (J z)) (v : QuotientV.V z) : v ^ 2 = 1 := by
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
  have hj : ((j : J z) : G) * ((j : J z) : G) ∈ centerIn (J z) := by
    rw [CFSG.centerIn_eq_map_center]
    exact CFSG.IsExtraspecial2.mul_self_mem_center_map hJ j.2
  have hker : j * j ∈ (QuotientV.pi z).ker := by
    rw [QuotientV.pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hj
  have hmap : QuotientV.pi z (j * j) = 1 := MonoidHom.mem_ker.mp hker
  simpa [pow_two, map_mul] using hmap

theorem card_V (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) : Nat.card (QuotientV.V z) = 2 ^ 8 := by
  have hZsub : Nat.card ((centerIn (J z)).subgroupOf (J z)) = 2 := by
    rw [QuotientV.centerIn_subgroupOf_eq_center]
    exact card_center_J hJ hcomm
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((centerIn (J z)).subgroupOf (J z))
  rw [hcard, hZsub] at hc
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (hc.symm.trans (by norm_num))

@[expose, reducible] noncomputable def commGroupV (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) :
    CommGroup (QuotientV.V z) :=
  { (inferInstance : Group (QuotientV.V z)) with
    mul_comm := (isMulCommutative_V hcomm).is_comm.comm }

@[reducible] noncomputable def moduleV (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    Module (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV hcomm
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← pow_two]
    exact pow_two_eq_one_V hJ x.toMul

theorem finrank_addV (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    Module.finrank (ZMod 2) (Additive (QuotientV.V z)) = 8 := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  have hc : Nat.card (Additive (QuotientV.V z)) = 2 ^ 8 := by
    rw [Nat.card_congr Additive.toMul]
    exact card_V hJ hcard hcomm
  have hdim := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (QuotientV.V z))
  rw [hc, Nat.card_zmod] at hdim
  exact Nat.pow_right_injective (by norm_num) hdim.symm

@[expose] noncomputable def conjVLinearMap (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) :=
  letI : CommGroup (QuotientV.V z) := commGroupV hcomm
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  (addAutLinearEquivMonoidHom
    (MulAut.congr (mulEquivVAdd (z := z)) (conjVA z x))).toLinearMap

@[simp] theorem conjVLinearMap_apply (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    conjVLinearMap hcomm hJ x v = Additive.ofMul ((conjVA z x) (Additive.toMul v)) := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  rw [conjVLinearMap, addAutLinearEquivMonoidHom_toLinearMap, mulAutToLinearMap_apply]
  rfl

theorem conjVLinearMap_one (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    conjVLinearMap hcomm hJ 1 = 1 := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  ext v
  rw [conjVLinearMap_apply, map_one]
  rfl

theorem conjVLinearMap_mul (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x y : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    conjVLinearMap hcomm hJ (x * y) = conjVLinearMap hcomm hJ x * conjVLinearMap hcomm hJ y := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  ext v
  rw [Module.End.mul_apply, conjVLinearMap_apply, conjVLinearMap_apply, conjVLinearMap_apply,
    map_mul]
  rfl

@[expose] noncomputable def conjVRepresentation (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    Representation (ZMod 2) ↥(H z) (Additive (QuotientV.V z)) := by
  letI : CommGroup (QuotientV.V z) := commGroupV hcomm
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  exact
    { toFun := conjVLinearMap hcomm hJ
      map_one' := conjVLinearMap_one hcomm hJ
      map_mul' := conjVLinearMap_mul hcomm hJ }

@[expose] noncomputable def fixSubmodule (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV hcomm
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup (autFixedSubgroup (conjVA z x)))

@[simp] theorem mem_fixSubmodule_iff (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) (v : Additive (QuotientV.V z)) :
    v ∈ fixSubmodule hcomm hJ x ↔ Additive.toMul v ∈ autFixedSubgroup (conjVA z x) := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  rw [fixSubmodule, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]

theorem card_fixSubmodule (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) :
    Nat.card ↥(fixSubmodule hcomm hJ x) = Nat.card ↥(autFixedSubgroup (conjVA z x)) := by
  apply Nat.card_congr
  refine
    { toFun := fun v => ⟨Additive.toMul v.1, (mem_fixSubmodule_iff hcomm hJ x v.1).mp v.2⟩
      invFun := fun w =>
        ⟨Additive.ofMul w.1,
          (mem_fixSubmodule_iff hcomm hJ x (Additive.ofMul w.1)).mpr (by simp)⟩
      left_inv := by
        intro v
        ext
        simp
      right_inv := by
        intro w
        ext
        simp }

@[expose] noncomputable def fixDimV (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) : ℕ :=
  letI : CommGroup (QuotientV.V z) := commGroupV hcomm
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  Module.finrank (ZMod 2) (fixSubmodule hcomm hJ x)

theorem card_fix (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) (hJ : IsExtraspecial2 (J z))
    (x : H z) : Nat.card ↥(autFixedSubgroup (conjVA z x)) = 2 ^ fixDimV hcomm hJ x := by
  rw [← card_fixSubmodule hcomm hJ x]
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixSubmodule hcomm hJ x)),
    Nat.card_zmod]
  rfl

theorem fixSubmodule_eq_ker (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    fixSubmodule hcomm hJ x = LinearMap.ker (conjVLinearMap hcomm hJ x - 1) := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  ext v
  rw [mem_fixSubmodule_iff, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero, mem_autFixedSubgroup]
  change conjVA z x (Additive.toMul v) = Additive.toMul v ↔
    conjVLinearMap hcomm hJ x v = v
  rw [conjVLinearMap_apply]
  constructor
  · intro hfix
    simpa using congrArg Additive.ofMul hfix
  · intro hfix
    simpa using congrArg Additive.toMul hfix

theorem invariants_zpowers_eq_fixSubmodule (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hJ : IsExtraspecial2 (J z)) (x : ↥(H z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV hcomm
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
    Representation.invariants
        ((conjVRepresentation hcomm hJ).comp (Subgroup.zpowers x).subtype) =
      fixSubmodule hcomm hJ x := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  ext v
  rw [Representation.mem_invariants]
  constructor
  · intro hv
    rw [mem_fixSubmodule_iff, mem_autFixedSubgroup]
    have hfix := hv ⟨x, Subgroup.mem_zpowers x⟩
    have hfix' : conjVLinearMap hcomm hJ x v = v := by
      simpa [conjVRepresentation] using hfix
    simpa [conjVLinearMap_apply] using congrArg Additive.toMul hfix'
  · intro hv
    have hgen : ∀ a : Subgroup.zpowers x,
        a ∈ Subgroup.zpowers (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) := by
      intro a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    have hiff :
        (∀ a : Subgroup.zpowers x,
          ((conjVRepresentation hcomm hJ).comp (Subgroup.zpowers x).subtype) a v = v) ↔
        ((conjVRepresentation hcomm hJ).comp (Subgroup.zpowers x).subtype)
          ⟨x, Subgroup.mem_zpowers x⟩ v = v :=
      Representation.mem_invariants_iff_of_forall_mem_zpowers
        (ρ := (conjVRepresentation hcomm hJ).comp (Subgroup.zpowers x).subtype)
        (g := ⟨x, Subgroup.mem_zpowers x⟩) hgen v
    rw [hiff]
    have hfix : conjVA z x (Additive.toMul v) = Additive.toMul v := by
      rw [← mem_autFixedSubgroup]
      exact (mem_fixSubmodule_iff hcomm hJ x v).mp hv
    have hfix' : conjVLinearMap hcomm hJ x v = v := by
      rw [conjVLinearMap_apply]
      exact congrArg Additive.ofMul hfix
    simpa [conjVRepresentation] using hfix'

theorem card_centralizerJ_eq_two_mul (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {x : H z}
    (hx : orderOf x = 3) :
    Nat.card (centralizerJ x) = 2 * 2 ^ fixDimV hcomm hJ x := by
  have hcopx : Nat.Coprime (orderOf x) (Nat.card (J z)) := by
    rw [hx, hcard]
    norm_num
  have hcop : Nat.Coprime (orderOf (conjJ' z x)) (Nat.card (J z)) :=
    Nat.Coprime.of_dvd_left (orderOf_map_dvd (conjJ' z) x) hcopx
  have hmain := card_autFixedSubgroup_eq_card_inf_mul_card_quotient (conjJ' z x) hcop
  rw [card_autFixedSubgroup_quotientAut_eq_card_autFixedSubgroup_conjVA (z := z) (x := x)]
    at hmain
  rw [autFixedSubgroup_conjJ'_eq_centralizerJ] at hmain
  rw [hmain, card_fix hcomm hJ x]
  congr 1
  have hle : Subgroup.center (J z) ≤ centralizerJ x := by
    intro j hj
    rw [mem_centralizerJ_iff]
    have hjZ : (j : G) ∈ centerIn (J z) := by
      have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
        rwa [QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mp hj'
    rw [centerIn_J_eq_zpowers hJ hcomm] at hjZ
    exact Subgroup.mem_centralizer_singleton_iff.mp (zpowers_le_centralizer x hjZ)
  rw [inf_eq_right.mpr hle, card_center_J hJ hcomm]

theorem card_CJ_eq_two_mul (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {x : H z} (hx : orderOf x = 3) :
    Nat.card (CJ z (x : G)) = 2 * 2 ^ fixDimV hcomm hJ x := by
  have he : ↥(CJ z (x : G)) ≃ ↥(centralizerJ x) := by
    unfold centralizerJ CJ
    exact (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.centralizer ({(x : G)} : Set G) ⊓ J z ≤ J z)).symm.toEquiv
  rw [Nat.card_congr he]
  exact card_centralizerJ_eq_two_mul hJ hcard hcomm hx

theorem conjJ'_eq_one_of_conjVA_eq_one (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z) {σ : H z} (hσ : orderOf σ = 3)
    (hV : conjVA z σ = 1) : conjJ' z σ = 1 := by
  apply MulEquiv.ext
  intro x
  have hpi : QuotientV.pi z (conjJ' z σ x) = QuotientV.pi z x := by
    have h := congrArg (fun g : MulAut (QuotientV.V z) => g (QuotientV.pi z x)) hV
    simpa [conjVA_mk] using h
  have hker : conjJ' z σ x * x⁻¹ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker]
    calc QuotientV.pi z (conjJ' z σ x * x⁻¹)
        = QuotientV.pi z (conjJ' z σ x) * (QuotientV.pi z x)⁻¹ := by rw [map_mul, map_inv]
      _ = QuotientV.pi z x * (QuotientV.pi z x)⁻¹ := by rw [hpi]
      _ = 1 := mul_inv_cancel _
  rw [QuotientV.pi_ker] at hker
  let ζ : centerIn (J z) :=
    ⟨((conjJ' z σ x * x⁻¹ : J z) : G), Subgroup.mem_subgroupOf.mp hker⟩
  let ζJ : J z := ⟨(ζ : G), ζ.2.1⟩
  have hrel : (conjJ' z σ x : G) = (ζ : G) * (x : G) := by
    have hζ : (ζ : G) = (conjJ' z σ x : G) * (x : G)⁻¹ := rfl
    rw [hζ]
    group
  have hconjx : conjJ' z σ x = ζJ * x := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hrel
  have hζzp : (ζ : G) ∈ Subgroup.zpowers z := by
    rw [← centerIn_J_eq_zpowers hJ hcomm]
    exact ζ.2
  have hfixζ : conjJ' z σ ζJ = ζJ := by
    apply Subtype.ext
    change (conjJ' z σ ζJ : G) = (ζ : G)
    rw [conjJ'_apply_coe]
    have hc : Commute (σ : G) (ζ : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (zpowers_le_centralizer σ hζzp)).symm
    rw [hc.eq]
    group
  have hpow : ∀ k : ℕ, ((conjJ' z σ : MulAut (J z)) ^ k) x = ζJ ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc ((conjJ' z σ : MulAut (J z)) ^ (k + 1)) x
            = (conjJ' z σ) (((conjJ' z σ : MulAut (J z)) ^ k) x) := by
              rw [pow_succ']
              rfl
          _ = (conjJ' z σ) (ζJ ^ k * x) := by rw [ih]
          _ = (conjJ' z σ) (ζJ ^ k) * (conjJ' z σ) x := by rw [map_mul]
          _ = ζJ ^ k * (ζJ * x) := by rw [map_pow, hfixζ, hconjx]
          _ = ζJ ^ (k + 1) * x := by group
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have h3 : (conjJ' z σ : MulAut (J z)) ^ 3 = 1 := by
    rw [← map_pow, hσ3, map_one]
  have hx3 : ((conjJ' z σ : MulAut (J z)) ^ 3) x = x := by rw [h3]; rfl
  have hζ3 : ζJ ^ 3 = 1 := by
    have h := hpow 3
    rw [hx3] at h
    have h' : ζJ ^ 3 * x = 1 * x := by simpa using h.symm
    exact mul_right_cancel h'
  have hζ2 : (ζ : G) * (ζ : G) = 1 := mul_self_eq_one_of_mem_zpowers hJ hcomm hζzp
  have hζ3G : (ζ : G) ^ 3 = 1 := by
    have := congrArg (fun j : J z => (j : G)) hζ3
    simpa using this
  have hζeq : (ζ : G) = 1 := by
    have hcube : (ζ : G) ^ 3 = (ζ : G) * ((ζ : G) * (ζ : G)) := by
      rw [pow_succ, pow_two]
      group
    rw [hcube, hζ2, mul_one] at hζ3G
    exact hζ3G
  have hζJ_one : ζJ = 1 := by
    apply Subtype.ext
    change (ζ : G) = 1
    exact hζeq
  rw [hconjx, hζJ_one, one_mul]
  rfl

theorem conjVA_ne_one_of_order_three (hJ : IsExtraspecial2 (J z))
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) {σ : H z}
    (hσ : orderOf σ = 3) : conjVA z σ ≠ 1 := by
  intro hV
  have hconjJ : conjJ' z σ = 1 := conjJ'_eq_one_of_conjVA_eq_one hJ hcomm hσ hV
  have hσcent : (σ : G) ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hfix : conjJ' z σ ⟨y, hy⟩ = ⟨y, hy⟩ := by
      rw [hconjJ]
      rfl
    have hcoe := congrArg (fun j : J z => (j : G)) hfix
    rw [conjJ'_apply_coe] at hcoe
    have hc : (σ : G) * (y : G) = (y : G) * (σ : G) := by
      calc (σ : G) * (y : G) = ((σ : G) * (y : G) * (σ : G)⁻¹) * (σ : G) := by group
        _ = (y : G) * (σ : G) := by rw [hcoe]
    exact hc.symm
  have hmem : (σ : G) ∈ H z ⊓ Subgroup.centralizer (J z : Set G) := ⟨σ.2, hσcent⟩
  rw [centralizer_J_eq_centerIn hCHJ, centerIn_J_eq_zpowers hJ hcomm] at hmem
  have hdvd : orderOf (σ : G) ∣ Nat.card (Subgroup.zpowers z) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) hmem
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_z hJ hcomm]
  rw [hzcard, Subgroup.orderOf_coe, hσ] at hdvd
  norm_num at hdvd

theorem fixDimV_eq_two_of_cube (hJ : IsExtraspecial2 (J z)) (hcard : Nat.card (J z) = 2 ^ 9)
    (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) {y σ : H z}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ) : fixDimV hcomm hJ σ = 2 := by
  let : CommGroup (QuotientV.V z) := commGroupV hcomm
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV hcomm hJ
  have hy9 : y ^ 9 = 1 := by rw [← hy, pow_orderOf_eq_one]
  have hσ3 : orderOf σ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have hg9 : (MulAut.congr (mulEquivVAdd (z := z)) (conjVA z y)) ^ 9 = 1 := by
    rw [← map_pow,
      show (conjVA z y) ^ 9 = conjVA z (y ^ 9) from (map_pow (conjVA z) y 9).symm, hy9,
      map_one (conjVA z)]
    exact map_one (MulAut.congr (mulEquivVAdd (z := z)) : MulAut (QuotientV.V z) →*
      MulAut (Multiplicative (Additive (QuotientV.V z))))
  have hT9 : (conjVLinearMap hcomm hJ y) ^ 9 = 1 := by
    dsimp only [conjVLinearMap]
    rw [linearEquiv_toLinearMap_pow, ← addAutLinearEquivMonoidHom_pow, hg9, map_one,
      LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  have hg3 : (MulAut.congr (mulEquivVAdd (z := z)) (conjVA z y)) ^ 3 =
      MulAut.congr (mulEquivVAdd (z := z)) (conjVA z σ) := by
    rw [← map_pow,
      show (conjVA z y) ^ 3 = conjVA z (y ^ 3) from (map_pow (conjVA z) y 3).symm, hyσ]
  have hT3 : (conjVLinearMap hcomm hJ y) ^ 3 = conjVLinearMap hcomm hJ σ := by
    dsimp only [conjVLinearMap]
    rw [linearEquiv_toLinearMap_pow, ← addAutLinearEquivMonoidHom_pow, hg3]
  have hT3_ne_one : (conjVLinearMap hcomm hJ y) ^ 3 ≠ 1 := by
    intro h3
    have hlin : conjVLinearMap hcomm hJ σ = 1 := by
      rw [← hT3, h3]
    have heσ : addAutLinearEquivMonoidHom
        (MulAut.congr (mulEquivVAdd (z := z)) (conjVA z σ)) =
          LinearEquiv.refl (ZMod 2) (Additive (QuotientV.V z)) := by
      apply LinearEquiv.ext
      intro v
      have hv := LinearMap.congr_fun hlin v
      rw [show conjVLinearMap hcomm hJ σ = (addAutLinearEquivMonoidHom
        (MulAut.congr (mulEquivVAdd (z := z)) (conjVA z σ))).toLinearMap from rfl] at hv
      simpa using hv
    have hmapone : addAutLinearEquivMonoidHom
        (1 : MulAut (Multiplicative (Additive (QuotientV.V z)))) =
          LinearEquiv.refl (ZMod 2) (Additive (QuotientV.V z)) := by
      apply LinearEquiv.ext
      intro v
      simp
    have hgσ : MulAut.congr (mulEquivVAdd (z := z)) (conjVA z σ) = 1 := by
      apply addAutLinearEquivMonoidHom_injective
      rw [hmapone]
      exact heσ
    have hconjV : conjVA z σ = 1 := by
      simpa using (MulAut.congr (mulEquivVAdd (z := z))).injective hgσ
    exact conjVA_ne_one_of_order_three hJ hcomm hCHJ hσ3 hconjV
  have hmain := CFSG.LinearAlgebra.F2OrderNineFixed.finrank_ker_cube_sub_one_eq_two
    (V := Additive (QuotientV.V z)) (finrank_addV hJ hcard hcomm) (conjVLinearMap hcomm hJ y)
    hT9 hT3_ne_one
  rw [fixDimV, fixSubmodule_eq_ker hcomm hJ σ, ← hT3]
  exact hmain

end CFSG.RankThree.GF2n.Parrott.Remarks
