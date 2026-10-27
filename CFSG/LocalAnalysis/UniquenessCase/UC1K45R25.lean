module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45T
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R25Aux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement
open scoped IsMulCommutative

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem quaternion_two_a_comm :
    ∀ b : QuaternionGroup 2, (QuaternionGroup.a 2 : QuaternionGroup 2) * b =
      b * (QuaternionGroup.a 2 : QuaternionGroup 2) := by decide

theorem quaternion_two_a_sq :
    (QuaternionGroup.a 2 : QuaternionGroup 2) * (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
  decide

theorem quaternion_two_a_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem quaternion_two_sq_eq_one_or_a :
    ∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = (QuaternionGroup.a 2 : QuaternionGroup 2) := by
  decide

private noncomputable abbrev zof (e : ↥(Tof G D) ≃* QuaternionGroup 2) : G :=
  (e.symm (QuaternionGroup.a 2) : G)

private noncomputable abbrev Zof (e : ↥(Tof G D) ≃* QuaternionGroup 2) : Subgroup G :=
  Subgroup.zpowers (zof e)

private noncomputable abbrev Zof' (e : ↥(Tof G D) ≃* QuaternionGroup 2) : Subgroup ↥(Xof G) :=
  (Zof e).subgroupOf (Xof G)

private abbrev Vof (e : ↥(Tof G D) ≃* QuaternionGroup 2) : Type :=
  ↥(Xof G) ⧸ Zof' e

private theorem Tof_sq_eq_one_or_z (e : ↥(Tof G D) ≃* QuaternionGroup 2) {t : G}
    (ht : t ∈ Tof G D) : t * t = 1 ∨ t * t = zof e := by
  rcases quaternion_two_sq_eq_one_or_a (e ⟨t, ht⟩) with h | h
  · left
    have h1 : (⟨t, ht⟩ : ↥(Tof G D)) * ⟨t, ht⟩ = 1 :=
      e.injective (by rw [map_mul, h, map_one])
    simpa using congrArg (Subtype.val) h1
  · right
    have h1 : (⟨t, ht⟩ : ↥(Tof G D)) * ⟨t, ht⟩ = e.symm (QuaternionGroup.a 2) :=
      e.injective (by rw [map_mul, h, MulEquiv.apply_symm_apply])
    simpa [zof] using congrArg (Subtype.val) h1

private theorem zof_mem_center_T (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    e.symm (QuaternionGroup.a 2) ∈ Subgroup.center ↥(Tof G D) := by
  rw [Subgroup.mem_center_iff]
  intro b
  apply e.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  exact (quaternion_two_a_comm (e b)).symm

private theorem zof_mem_ZX (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    zof e ∈ ZXof G :=
  uc45_ZT_le_ZX c.toBase45 c.class_two.1 c.ZX_le
    (Subgroup.mem_map.mpr ⟨e.symm (QuaternionGroup.a 2), zof_mem_center_T e, rfl⟩)

private theorem Zof_le_ZX (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    Zof e ≤ ZXof G :=
  Subgroup.zpowers_le.mpr (zof_mem_ZX c e)

private theorem Zof_le_center (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    Zof e ≤ Subgroup.center G :=
  (Zof_le_ZX c e).trans c.ZX_le

private theorem zof_ne_one (e : ↥(Tof G D) ≃* QuaternionGroup 2) : zof e ≠ 1 := by
  intro h
  have h' : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext (by simpa [zof] using h)
  have : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
    rw [← MulEquiv.apply_symm_apply e (QuaternionGroup.a 2), h', map_one]
  exact quaternion_two_a_ne_one this

private theorem zof_sq (e : ↥(Tof G D) ≃* QuaternionGroup 2) : zof e * zof e = 1 := by
  have h : e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1 := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, quaternion_two_a_sq, map_one]
  simpa [zof] using congrArg (Subtype.val) h

private theorem eq_one_or_zof_of_mem_ZX_sq_one (c : Ctx45 p G D)
    (e : ↥(Tof G D) ≃* QuaternionGroup 2) {u : G} (hu : u ∈ ZXof G) (hu2 : u * u = 1) :
    u = 1 ∨ u = zof e := by
  classical
  haveI : IsCyclic ↥(Subgroup.center G) := c.center_cyclic
  haveI : IsCyclic ↥(ZXof G) := Subgroup.isCyclic_of_le c.ZX_le
  haveI : Fintype ↥(ZXof G) := Fintype.ofFinite _
  have hcard : (Finset.univ.filter (fun w : ↥(ZXof G) => w ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (n := 2) (by norm_num)
  let z' : ↥(ZXof G) := ⟨zof e, zof_mem_ZX c e⟩
  have hz'ne : (1 : ↥(ZXof G)) ≠ z' := fun h => zof_ne_one e (congrArg Subtype.val h).symm
  have hpair : ({1, z'} : Finset ↥(ZXof G)).card = 2 :=
    (Finset.card_pair_eq_two_iff (a := (1 : ↥(ZXof G))) (b := z')).mpr hz'ne
  have hsub : ({1, z'} : Finset ↥(ZXof G)) ⊆ Finset.univ.filter (fun w => w ^ 2 = 1) := by
    intro w hw
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · rw [hw, one_pow]
    · rw [hw]
      apply Subtype.ext
      simpa [z', zof, pow_two] using zof_sq e
  have heq : ({1, z'} : Finset ↥(ZXof G)) = Finset.univ.filter (fun w => w ^ 2 = 1) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hpair]; exact hcard)
  have hu' : (⟨u, hu⟩ : ↥(ZXof G)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hu2
  have hmem : (⟨u, hu⟩ : ↥(ZXof G)) ∈ ({1, z'} : Finset ↥(ZXof G)) := by
    rw [heq, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hu'⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

private theorem commutator_mem_Zof (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    {x y : G} (hx : x ∈ Xof G) (hy : y ∈ Xof G) : ⁅x, y⁆ ∈ Zof e := by
  have hmemZX : ⁅x, y⁆ ∈ ZXof G := by
    have hmem : ⁅(⟨x, hx⟩ : ↥(Xof G)), (⟨y, hy⟩ : ↥(Xof G))⁆ ∈
        Subgroup.center ↥(Xof G) :=
      c.class_two.1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    refine Subgroup.mem_map.mpr ⟨⁅(⟨x, hx⟩ : ↥(Xof G)), (⟨y, hy⟩ : ↥(Xof G))⁆, hmem, ?_⟩
    simp [commutatorElement_def]
  have hsq : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    set px : ↥(Xof G) := ⟨x, hx⟩ with hpx
    set py : ↥(Xof G) := ⟨y, hy⟩ with hpy
    have hp2 : px ^ 2 ∈ Subgroup.center ↥(Xof G) := c.class_two.2 px
    have hpc : ⁅px, py⁆ ∈ Subgroup.center ↥(Xof G) :=
      c.class_two.1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h1 : ⁅px ^ 2, py⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hp2 py).symm
    have h2 : ⁅px ^ 2, py⁆ = ⁅px, py⁆ ^ 2 := by
      have hiter : ⁅px, ⁅px, py⁆⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hpc px)
      have := TauCeti.commutatorElement_pow_left_of_commute (a := px) (b := py)
        (by rw [hiter]; exact Commute.one_right px)
        (by rw [hiter]; exact Commute.one_right ⁅px, py⁆) 2
      simpa [hiter] using this
    have h3 : (⁅px, py⁆ : ↥(Xof G)) ^ 2 = 1 := by rw [← h2, h1]
    have hcomm_coe : ⁅x, y⁆ = ((⁅px, py⁆ : ↥(Xof G)) : G) := by
      rw [hpx, hpy]; rfl
    calc ⁅x, y⁆ * ⁅x, y⁆ = ((⁅px, py⁆ : ↥(Xof G)) : G) * ((⁅px, py⁆ : ↥(Xof G)) : G) := by
          rw [hcomm_coe]
      _ = 1 := by
          simpa [pow_two] using congrArg (Subgroup.subtype (Xof G)) h3
  rcases eq_one_or_zof_of_mem_ZX_sq_one c e hmemZX hsq with h | h
  · rw [h]; exact (Zof e).one_mem
  · rw [h]; exact Subgroup.mem_zpowers _

private noncomputable def Yof (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    Subgroup G where
  carrier := {x | x ∈ Xof G ∧ x * x ∈ Zof e}
  one_mem' := ⟨(Xof G).one_mem, by simpa using (Zof e).one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxX, hxZ⟩ ⟨hyX, hyZ⟩
    refine ⟨(Xof G).mul_mem hxX hyX, ?_⟩
    have hcomm := commutator_mem_Zof c e ((Xof G).inv_mem hxX) hyX
    have hdecomp : (x * y) * (x * y) = (x * x) * ⁅x⁻¹, y⁆ * (y * y) := by
      simp only [commutatorElement_def]; group
    rw [hdecomp]
    exact (Zof e).mul_mem ((Zof e).mul_mem hxZ hcomm) hyZ
  inv_mem' := by
    rintro x ⟨hxX, hxZ⟩
    refine ⟨(Xof G).inv_mem hxX, ?_⟩
    have hdecomp : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [hdecomp]
    exact (Zof e).inv_mem hxZ

private theorem Yof_normal (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    (Yof c e).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨hxX, hxZ⟩ := hx
  refine ⟨(xof_normal (G := G)).conj_mem x hxX g, ?_⟩
  have hconj : (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [hconj]
  have hxcent : x * x ∈ Subgroup.center G := Zof_le_center c e hxZ
  have hcomm : g * (x * x) = (x * x) * g := Subgroup.mem_center_iff.mp hxcent g
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hxZ

private theorem Tof_le_Yof (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    Tof G D ≤ Yof c e := by
  intro t ht
  refine ⟨Subgroup.commutator_le_left (H₁ := Xof G) (H₂ := D) ht, ?_⟩
  rcases Tof_sq_eq_one_or_z e ht with h | h
  · rw [h]; exact (Zof e).one_mem
  · rw [h]; exact Subgroup.mem_zpowers _

private theorem sq_mem_Zof (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) {x : G}
    (hx : x ∈ Xof G) : x * x ∈ Zof e := by
  haveI : (Yof c e).Normal := Yof_normal c e
  have hXle : Xof G ≤ Yof c e := by
    rw [← c.X_gen]
    exact Subgroup.normalClosure_le_normal (Tof_le_Yof c e)
  exact (hXle hx).2

private theorem Zof'_le_center (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    Zof' e ≤ Subgroup.center ↥(Xof G) := by
  intro w hw
  rw [Subgroup.mem_subgroupOf] at hw
  obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp (Zof_le_ZX c e hw)
  exact (Subtype.ext hvw) ▸ hv

private theorem Zof'_normal (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    (Zof' e).Normal :=
  Subgroup.normal_of_le_center (Zof'_le_center c e)

private theorem commutator_le_Zof' (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) :
    commutator ↥(Xof G) ≤ Zof' e := by
  change ⁅(⊤ : Subgroup ↥(Xof G)), (⊤ : Subgroup ↥(Xof G))⁆ ≤ Zof' e
  rw [Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_subgroupOf]
  simpa [commutatorElement_def] using commutator_mem_Zof c e x.2 y.2

private theorem conjNormal_map_Zof' (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    (g : G) :
    (Zof' e).map (MulAut.conjNormal g).toMonoidHom = Zof' e := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ Zof e := Subgroup.mem_subgroupOf.mp hu
    have huc : (u : G) ∈ Subgroup.center G := Zof_le_center c e hu'
    have hcomm : g * (u : G) = (u : G) * g := Subgroup.mem_center_iff.mp huc g
    refine Subgroup.mem_subgroupOf.mpr ?_
    change ((MulAut.conjNormal g) u : G) ∈ Zof e
    rw [MulAut.conjNormal_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hu'
  · intro hw
    refine ⟨w, hw, ?_⟩
    apply Subtype.ext
    have hw' : (w : G) ∈ Zof e := Subgroup.mem_subgroupOf.mp hw
    have hwc : (w : G) ∈ Subgroup.center G := Zof_le_center c e hw'
    have hcomm : g * (w : G) = (w : G) * g := Subgroup.mem_center_iff.mp hwc g
    change ((MulAut.conjNormal g) w : G) = (w : G)
    rw [MulAut.conjNormal_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem conjNormal_mul_inv_mem_Zof' (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    {g x₀ c₀ : G} (hx₀ : x₀ ∈ Xof G) (hc₀ : c₀ ∈ Subgroup.center G) (hg : x₀ * c₀ = g)
    (w : ↥(Xof G)) : (MulAut.conjNormal g) w * w⁻¹ ∈ Zof' e := by
  have hconj : (MulAut.conjNormal g) w = (MulAut.conjNormal x₀) w := by
    rw [← hg, map_mul, MulAut.mul_apply]
    have hfix : (MulAut.conjNormal c₀) w = w := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hcomm : c₀ * (w : G) = (w : G) * c₀ :=
        (Subgroup.mem_center_iff.mp hc₀ (w : G)).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix]
  rw [hconj, Subgroup.mem_subgroupOf]
  have hcoe : (((MulAut.conjNormal x₀) w * w⁻¹ : ↥(Xof G)) : G) = ⁅x₀, (w : G)⁆ := by
    simp [MulAut.conjNormal_apply, commutatorElement_def]
  rw [hcoe]
  exact commutator_mem_Zof c e hx₀ w.2

private noncomputable def actOf (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    [(Zof' e).Normal] : G →* MulAut (Vof e) where
  toFun g := QuotientGroup.congr (Zof' e) (Zof' e) (MulAut.conjNormal g) (conjNormal_map_Zof' c e g)
  map_one' := by
    ext v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
    show QuotientGroup.mk' (Zof' e) ((MulAut.conjNormal 1) w) = QuotientGroup.mk' (Zof' e) w
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    ext v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
    show QuotientGroup.mk' (Zof' e) ((MulAut.conjNormal (g * h)) w) =
      QuotientGroup.mk' (Zof' e) ((MulAut.conjNormal g) ((MulAut.conjNormal h) w))
    rw [map_mul, MulAut.mul_apply]

private theorem actOf_mk' (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) [(Zof' e).Normal]
    (g : G) (x : ↥(Xof G)) :
    actOf c e g (QuotientGroup.mk' (Zof' e) x) =
      QuotientGroup.mk' (Zof' e) ((MulAut.conjNormal g) x) :=
  QuotientGroup.congr_mk (Zof' e) (Zof' e) (MulAut.conjNormal g) (conjNormal_map_Zof' c e g) x

private theorem actOf_ker (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) [(Zof' e).Normal]
    (η : G →* Equiv.Perm (Fin 5)) (hηk : η.ker = CFSG.pPrimeCore 3 G)
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G) :
    ∀ g, η g = 1 → ∀ v : Vof e, actOf c e g v = v := by
  intro g hg v
  have hgmem : g ∈ CFSG.pPrimeCore 3 G := by
    rw [← hηk]; exact MonoidHom.mem_ker.mpr hg
  rw [hH] at hgmem
  obtain ⟨x₀, hx₀, c₀, hc₀, hxc₀⟩ := Subgroup.mem_sup_of_normal_right.mp hgmem
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
  have hmem : (MulAut.conjNormal g) w * w⁻¹ ∈ Zof' e :=
    conjNormal_mul_inv_mem_Zof' c e hx₀ hc₀ hxc₀ w
  have h1 : QuotientGroup.mk' (Zof' e) (((MulAut.conjNormal g) w) * w⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_mul, map_inv] at h1
  have h2 : QuotientGroup.mk' (Zof' e) ((MulAut.conjNormal g) w) =
      QuotientGroup.mk' (Zof' e) w := mul_inv_eq_one.mp h1
  show (actOf c e g) (QuotientGroup.mk' (Zof' e) w) = QuotientGroup.mk' (Zof' e) w
  rw [actOf_mk' c e g w]
  exact h2

private noncomputable def psiOf (e : ↥(Tof G D) ≃* QuaternionGroup 2) [(Zof' e).Normal]
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5)) (h : Zof' e ≤ ψ.ker) :
    Vof e →* ↥(CFSG.Quasithin.G6.coreMod 5) :=
  QuotientGroup.lift (Zof' e) ψ h

private theorem psiOf_mk' (e : ↥(Tof G D) ≃* QuaternionGroup 2) [(Zof' e).Normal]
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5)) (h : Zof' e ≤ ψ.ker)
    (x : ↥(Xof G)) : psiOf e ψ h (QuotientGroup.mk' (Zof' e) x) = ψ x := by
  simp [psiOf]

private theorem psiOf_surjective (e : ↥(Tof G D) ≃* QuaternionGroup 2) [(Zof' e).Normal]
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5)) (h : Zof' e ≤ ψ.ker)
    (hψs : Function.Surjective ψ) : Function.Surjective (psiOf e ψ h) := by
  intro w
  obtain ⟨x, hx⟩ := hψs w
  exact ⟨QuotientGroup.mk' (Zof' e) x, by rw [psiOf_mk' e ψ h x]; exact hx⟩

private theorem psiOf_equivariant (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    [(Zof' e).Normal] (η : G →* Equiv.Perm (Fin 5))
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5)) (h : Zof' e ≤ ψ.ker)
    (hψe : ∀ g x, ψ (MulAut.conjNormal g x) = CFSG.Quasithin.G6.coreAct 5 (η g) (ψ x))
    (g : G) (v : Vof e) :
    psiOf e ψ h (actOf c e g v) = CFSG.Quasithin.G6.coreAct 5 (η g) (psiOf e ψ h v) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
  rw [actOf_mk' c e g x, psiOf_mk' e ψ h ((MulAut.conjNormal g) x), psiOf_mk' e ψ h x]
  exact hψe g x

private theorem psiOf_fix (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2) [(Zof' e).Normal]
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5)) (h : Zof' e ≤ ψ.ker)
    (hψk : ψ.ker = Subgroup.center ↥(Xof G)) (g : G) {v : Vof e}
    (hv : v ∈ (psiOf e ψ h).ker) : actOf c e g v = v := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
  have hwψ : ψ w = 1 := by
    have h' : psiOf e ψ h (QuotientGroup.mk' (Zof' e) w) = 1 := MonoidHom.mem_ker.mp hv
    rwa [psiOf_mk' e ψ h w] at h'
  have hwcent : w ∈ Subgroup.center ↥(Xof G) := hψk ▸ MonoidHom.mem_ker.mpr hwψ
  have hwG : (w : G) ∈ Subgroup.center G :=
    c.ZX_le (Subgroup.mem_map.mpr ⟨w, hwcent, rfl⟩)
  have hconj : (MulAut.conjNormal g) w = w := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hcomm : g * (w : G) = (w : G) * g := Subgroup.mem_center_iff.mp hwG g
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  show (actOf c e g) (QuotientGroup.mk' (Zof' e) w) = QuotientGroup.mk' (Zof' e) w
  rw [actOf_mk' c e g w, hconj]

private theorem closure_generators_eq_top (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    [(Zof' e).Normal] :
    Subgroup.closure {u : Vof e | ∃ g v, u = v * ((actOf c e g) v)⁻¹} = ⊤ := by
  have hK : ⁅Xof G, (⊤ : Subgroup G)⁆ = Xof G := by
    rw [← c.K_eq]; exact kof_commutator_top c.card_three c.gen
  let S : Set ↥(Xof G) := {u | ∃ g : G, ∃ a : ↥(Xof G),
    u = a * ((MulAut.conjNormal g) a)⁻¹}
  have htop : Subgroup.map (Xof G).subtype (⊤ : Subgroup ↥(Xof G)) = Xof G := by
    ext z
    constructor
    · intro hz; exact Subgroup.map_subtype_le _ hz
    · intro hz; exact Subgroup.mem_map.mpr ⟨⟨z, hz⟩, Subgroup.mem_top _, rfl⟩
  have hScomm : ∀ x ∈ Xof G, ∀ g : G,
      ⁅x, g⁆ ∈ Subgroup.map (Xof G).subtype (Subgroup.closure S) := by
    intro x hx g
    refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * ((MulAut.conjNormal g) ⟨x, hx⟩)⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨g, ⟨x, hx⟩, rfl⟩
    · change ((⟨x, hx⟩ * ((MulAut.conjNormal g) ⟨x, hx⟩)⁻¹ : ↥(Xof G)) : G) =
        x * g * x⁻¹ * g⁻¹
      simp only [MulAut.conjNormal_apply, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hXle : Xof G ≤ Subgroup.map (Xof G).subtype (Subgroup.closure S) := by
    have hcomm : ⁅Xof G, (⊤ : Subgroup G)⁆ ≤ Subgroup.map (Xof G).subtype (Subgroup.closure S) := by
      rw [Subgroup.commutator_le]
      intro x hx g _
      exact hScomm x hx g
    rwa [hK] at hcomm
  have hmapS : Subgroup.map (Xof G).subtype (Subgroup.closure S) = Xof G :=
    le_antisymm (Subgroup.map_subtype_le _) hXle
  have hS : Subgroup.closure S = ⊤ :=
    Subgroup.map_injective (Xof G).subtype_injective (by rw [hmapS, htop])
  have hGenEq : {u : Vof e | ∃ g v, u = v * ((actOf c e g) v)⁻¹} =
      (QuotientGroup.mk' (Zof' e)) '' S := by
    ext u
    constructor
    · rintro ⟨g, v, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
      refine ⟨a * ((MulAut.conjNormal g) a)⁻¹, ⟨g, a, rfl⟩, ?_⟩
      rw [actOf_mk' c e g a, map_mul, map_inv]
    · rintro ⟨s, ⟨g, a, rfl⟩, rfl⟩
      refine ⟨g, QuotientGroup.mk' (Zof' e) a, ?_⟩
      rw [actOf_mk' c e g a, map_mul, map_inv]
  rw [hGenEq, ← MonoidHom.map_closure (QuotientGroup.mk' (Zof' e)) S, hS]
  exact Subgroup.map_top_of_surjective (QuotientGroup.mk' (Zof' e))
    (QuotientGroup.mk'_surjective _)

private theorem Vof_sq_eq_one (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    [(Zof' e).Normal] : ∀ v : Vof e, v * v = 1 := by
  intro v
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Zof' e) v
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa using sq_mem_Zof c e w.2

private theorem center_le_Zof' (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    [(Zof' e).Normal] (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (h : Zof' e ≤ ψ.ker) (hψk : ψ.ker = Subgroup.center ↥(Xof G))
    (hker : (psiOf e ψ h).ker = ⊥) : Subgroup.center ↥(Xof G) ≤ Zof' e := by
  intro x hx
  have hx1 : psiOf e ψ h (QuotientGroup.mk' (Zof' e) x) = 1 := by
    rw [psiOf_mk' e ψ h x]
    exact MonoidHom.mem_ker.mp (hψk.symm ▸ hx)
  have hxker : QuotientGroup.mk' (Zof' e) x ∈ (psiOf e ψ h).ker := MonoidHom.mem_ker.mpr hx1
  rw [hker, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxker
  exact hxker

private theorem ZX_le_Zof (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    [(Zof' e).Normal] (hcenter : Subgroup.center ↥(Xof G) ≤ Zof' e) : ZXof G ≤ Zof e := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
  exact Subgroup.mem_subgroupOf.mp (hcenter hx)

private theorem card_ZX_eq_two (c : Ctx45 p G D) (e : ↥(Tof G D) ≃* QuaternionGroup 2)
    (hZX_le : ZXof G ≤ Zof e) : Nat.card ↥(ZXof G) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · calc Nat.card ↥(ZXof G) ≤ Nat.card ↥(Zof e) := Subgroup.card_le_of_le hZX_le
      _ = orderOf (zof e) := Nat.card_zpowers (zof e)
      _ = 2 := orderOf_eq_prime (p := 2) (by simpa [pow_two] using zof_sq e) (zof_ne_one e)
  · have hle' : Subgroup.zpowers (zof e) ≤ ZXof G := Subgroup.zpowers_le.mpr (zof_mem_ZX c e)
    calc 2 = Nat.card ↥(Subgroup.zpowers (zof e)) := by
            rw [Nat.card_zpowers,
              orderOf_eq_prime (p := 2) (by simpa [pow_two] using zof_sq e) (zof_ne_one e)]
        _ ≤ Nat.card ↥(ZXof G) := Subgroup.card_le_of_le hle'

theorem r2_center_two (c : Ctx45 p G D)
    (hH : CFSG.pPrimeCore 3 G = Xof G ⊔ Subgroup.center G) (hD5 : XDelta5 G) :
    Nat.card ↥(Subgroup.center ↥(Xof G)) = 2 := by
  obtain ⟨e⟩ := c.Q8
  obtain ⟨η, ψ, hηk, hηr, hψs, hψk, hψe⟩ := hD5
  haveI : (Zof' e).Normal := Zof'_normal c e
  have hle : commutator ↥(Xof G) ≤ Zof' e := commutator_le_Zof' c e
  haveI : IsMulCommutative (Vof e) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
  have hZof'_le_ker : Zof' e ≤ ψ.ker := by
    rw [hψk]; exact Zof'_le_center c e
  have hker : ∀ g, η g = 1 → ∀ v : Vof e, actOf c e g v = v := actOf_ker c e η hηk hH
  have hψbs : Function.Surjective (psiOf e ψ hZof'_le_ker) :=
    psiOf_surjective e ψ hZof'_le_ker hψs
  have hψb : ∀ g v, psiOf e ψ hZof'_le_ker (actOf c e g v) =
      CFSG.Quasithin.G6.coreAct 5 (η g) (psiOf e ψ hZof'_le_ker v) :=
    fun g v => psiOf_equivariant c e η ψ hZof'_le_ker hψe g v
  have hfix : ∀ g, ∀ x ∈ (psiOf e ψ hZof'_le_ker).ker, actOf c e g x = x :=
    fun g x hx => psiOf_fix c e ψ hZof'_le_ker hψk g hx
  have hA : ∀ g, η g ∈ alternatingGroup (Fin 5) := by
    intro g
    rw [← hηr]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ g, η g = σ := by
    intro σ hσ
    rw [← hηr] at hσ
    exact MonoidHom.mem_range.mp hσ
  have hgen : Subgroup.closure {u : Vof e | ∃ g v, u = v * ((actOf c e g) v)⁻¹} = ⊤ :=
    closure_generators_eq_top c e
  have hkerbot : (psiOf e ψ hZof'_le_ker).ker = ⊥ :=
    ker_eq_bot_of_equivariant_section η hA hs (Vof_sq_eq_one c e) (actOf c e) hker
      (psiOf e ψ hZof'_le_ker) hψbs hψb hfix hgen
  have hZX_le : ZXof G ≤ Zof e :=
    ZX_le_Zof c e (center_le_Zof' c e ψ hZof'_le_ker hψk hkerbot)
  have hcard_ZX : Nat.card ↥(ZXof G) = 2 := card_ZX_eq_two c e hZX_le
  rw [← Subgroup.card_map_of_injective (K := Subgroup.center ↥(Xof G)) (Xof G).subtype_injective]
  exact hcard_ZX

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
