module

public import CFSG.Sporadic.HNOddCore.Fusion
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2090
public import Certificates.Certificate2091
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import Certificates.Certificate2107
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub mem_fixSub)

section Transport

variable {S : Type*} [Group S] {G0 : Type*} [Group G0]

@[expose] def autTransport {Q : Subgroup G0} (θ : S ≃* Q) (α : MulAut S) : MulAut Q :=
  (θ.symm.trans α).trans θ

theorem autTransport_apply {Q : Subgroup G0} (θ : S ≃* Q) (α : MulAut S) (q : Q) :
    autTransport θ α q = θ (α (θ.symm q)) := rfl

theorem autTransport_mul {Q : Subgroup G0} (θ : S ≃* Q) (α β : MulAut S) :
    autTransport θ (α * β) = autTransport θ α * autTransport θ β := by
  refine MulEquiv.ext fun q => ?_
  rw [MulAut.mul_apply, autTransport_apply, autTransport_apply, autTransport_apply,
    MulEquiv.symm_apply_apply, MulAut.mul_apply]

theorem autTransport_one {Q : Subgroup G0} (θ : S ≃* Q) : autTransport θ 1 = 1 := by
  refine MulEquiv.ext fun q => ?_
  rw [autTransport_apply, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]

theorem autTransport_injective {Q : Subgroup G0} (θ : S ≃* Q) {α β : MulAut S}
    (h : autTransport θ α = autTransport θ β) : α = β := by
  refine MulEquiv.ext fun s => θ.injective ?_
  have e := DFunLike.congr_fun h (θ s)
  rwa [autTransport_apply, autTransport_apply, MulEquiv.symm_apply_apply] at e

theorem fixSub_autTransport {Q : Subgroup G0} (θ : S ≃* Q) (α : MulAut S) :
    Nonempty (fixSub α ≃* fixSub (autTransport θ α)) := by
  refine ⟨(θ.subgroupMap (fixSub α)).trans (MulEquiv.subgroupCongr ?_)⟩
  ext q
  rw [Subgroup.mem_map, mem_fixSub, autTransport_apply]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_fixSub] at hs
    show θ (α (θ.symm (θ s))) = θ s
    rw [MulEquiv.symm_apply_apply, hs]
  · intro hq
    refine ⟨θ.symm q, ?_, MulEquiv.apply_symm_apply θ q⟩
    rw [mem_fixSub]
    apply θ.injective
    rw [hq, MulEquiv.apply_symm_apply]

theorem mem_inner_of_autTransport {Q : Subgroup G0} (θ : S ≃* Q) {α : MulAut S} {g : Q}
    (h : MulAut.conj g = autTransport θ α) : α ∈ inner S := by
  refine ⟨θ.symm g, MulEquiv.ext fun s => ?_⟩
  have e := DFunLike.congr_fun h (θ s)
  rw [autTransport_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at e
  rw [MulAut.conj_apply, ← MulEquiv.symm_apply_apply θ (α s), ← e, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]

end Transport

theorem sub_centralizer_conj_equiv {G0 : Type*} [Group G0] {J R : Subgroup G0} (ι : J →* R)
    (g : J) (t : R) (A B : Subgroup J) (hA : ∀ j : J, j ∈ A ↔ ι j * (ι g * t * (ι g)⁻¹) =
      (ι g * t * (ι g)⁻¹) * ι j) (hB : ∀ j : J, j ∈ B ↔ ι j * t = t * ι j) :
    Nonempty (A ≃* B) := by
  refine ⟨((MulAut.conj g⁻¹).subgroupMap A).trans (MulEquiv.subgroupCongr ?_)⟩
  ext j
  rw [Subgroup.mem_map, hB]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hA] at ha
    show ι (g⁻¹ * a * g⁻¹⁻¹) * t = t * ι (g⁻¹ * a * g⁻¹⁻¹)
    rw [inv_inv, map_mul, map_mul, map_inv]
    calc (ι g)⁻¹ * ι a * ι g * t = (ι g)⁻¹ * (ι a * (ι g * t * (ι g)⁻¹)) * ι g := by group
      _ = (ι g)⁻¹ * ((ι g * t * (ι g)⁻¹) * ι a) * ι g := by rw [ha]
      _ = t * ((ι g)⁻¹ * ι a * ι g) := by group
  · intro hj
    refine ⟨g * j * g⁻¹, ?_, ?_⟩
    · rw [hA, map_mul, map_mul, map_inv]
      calc ι g * ι j * (ι g)⁻¹ * (ι g * t * (ι g)⁻¹) = ι g * (ι j * t) * (ι g)⁻¹ := by group
        _ = ι g * (t * ι j) * (ι g)⁻¹ := by rw [hj]
        _ = ι g * t * (ι g)⁻¹ * (ι g * ι j * (ι g)⁻¹) := by group
    · show g⁻¹ * (g * j * g⁻¹) * g⁻¹⁻¹ = j
      group

theorem fixSub_equiv_of_model {S : Type*} [Group S] {G0 : Type*} [Group G0] {J R : Subgroup G0}
    (θ : S ≃* J) (cj : R →* MulAut J) (hcj : Function.Bijective cj) (ι : J →* R)
    (hι : ∀ g : J, cj (ι g) = MulAut.conj g)
    (hfix : ∀ (y : R) (j : J), cj y j = j ↔ ι j * y = y * ι j) (t : R)
    (hfuse : ∀ y : R, y ^ 2 = 1 → y ≠ 1 → y ∉ ι.range → ∃ g : J, ι g * t * (ι g)⁻¹ = y)
    {P : Type*} [Group P] (C : Subgroup J) (hC : ∀ j : J, j ∈ C ↔ ι j * t = t * ι j)
    (hCP : Nonempty (C ≃* P)) (α : MulAut S) (hα : orderOf α = 2) (hout : α ∉ inner S) :
    Nonempty (fixSub α ≃* P) := by
  obtain ⟨y, hy⟩ := hcj.2 (autTransport θ α)
  have hα2 : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hy2 : y ^ 2 = 1 := hcj.1 (by
    rw [map_pow, hy, pow_two, ← autTransport_mul, hα2, autTransport_one, map_one])
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, ← autTransport_one θ] at hy
    rw [autTransport_injective θ hy.symm, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hyout : y ∉ ι.range := by
    rintro ⟨g, rfl⟩
    rw [hι] at hy
    exact hout (mem_inner_of_autTransport θ hy)
  obtain ⟨g, hg⟩ := hfuse y hy2 hy1 hyout
  obtain ⟨e1⟩ := fixSub_autTransport θ α
  obtain ⟨e2⟩ := sub_centralizer_conj_equiv ι g t (fixSub (autTransport θ α)) C
    (fun j => by rw [mem_fixSub, ← hy, hfix, hg]) hC
  obtain ⟨e3⟩ := hCP
  exact ⟨(e1.trans e2).trans e3⟩

theorem conjR_jR
    (g : JH) : conjR (jR g) = MulAut.conj g := by
  rw [jR_def]
  exact conjR_JH g

theorem conjR_fix_iff
    (y : RH) (j : JH) : conjR y j = j ↔ jR j * y = y * jR j := by
  constructor
  · intro h
    have e : ((conjR y j : JH) : GL (Fin hnsData.d) (ZMod 5)) = j := by rw [h]
    rw [conjR_apply] at e
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, jR_val]
    calc (j : GL (Fin hnsData.d) (ZMod 5)) * y =
        y * j * (y : GL (Fin hnsData.d) (ZMod 5))⁻¹ * y := by rw [e]
      _ = y * j := by group
  · intro h
    have e := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, jR_val] at e
    apply Subtype.ext
    rw [conjR_apply]
    calc (y : GL (Fin hnsData.d) (ZMod 5)) * j * (y : GL (Fin hnsData.d) (ZMod 5))⁻¹ =
        j * y * (y : GL (Fin hnsData.d) (ZMod 5))⁻¹ := by rw [e]
      _ = j := by group

theorem mem_range_of_J_conj
    {x y : RH} (hx : x ∈ jR.range) (h : ∃ g : JH, jR g * x * (jR g)⁻¹ = y) :
    y ∈ jR.range := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨a, rfl⟩ := hx
  exact ⟨g * a * g⁻¹, by rw [map_mul, map_mul, map_inv]⟩

theorem t4R_sq :
    (jR t4J) ^ 2 = 1 := by rw [← map_pow, t4J_sq', map_one]

theorem t4R_ne_one :
    jR t4J ≠ 1 := fun h => t4J_ne_one (jR_injective (h.trans (map_one jR).symm))

theorem fuse_t1R
    (y : RH) (h2 : y ^ 2 = 1) (h1 : y ≠ 1) (hout : y ∉ jR.range) :
    ∃ g : JH, jR g * t1R * (jR g)⁻¹ = y := by
  obtain ⟨hcls, -, -, -, hJ, -⟩ := ctuc_hn_involution_fusion_and_local_stabilizers
  rcases hcls y h2 h1 with hc | hc | hc
  · exact hJ t1R y (by rw [t1R_eq]; exact cR_sq) (by rw [t1R_eq]; exact cR_ne_one) hc
  · exact absurd (mem_range_of_J_conj ⟨t2J, rfl⟩ (hJ _ y t2_sqR t2_ne_oneR hc)) hout
  · exact absurd (mem_range_of_J_conj ⟨t4J, rfl⟩ (hJ _ y t4R_sq t4R_ne_one hc)) hout

theorem mem_CJ_t1R_iff
    (j : JH) : j ∈ (Subgroup.centralizer {t1R}).comap jR ↔
    jR j * t1R = t1R * jR j := by
  rw [Subgroup.mem_comap, sub_mem_centralizer_iff]

theorem hn_outer_involution_fixSub
    {S : Type*} [Group S] (e : S ≃* Blueprint.NativeSporadic.HN)
    (α : MulAut S) (hα : orderOf α = 2)
    (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S) :
    Nonempty (CFSG.Sporadic.Schreier.fixSub α ≃* Equiv.Perm (Fin 10)) :=
  fixSub_equiv_of_model (e.trans hnEquivJ) conjR conjR_bijective jR conjR_jR conjR_fix_iff t1R
    fuse_t1R _ mem_CJ_t1R_iff ctuc_hn_three_involution_centralizers_exact.2.2.1 α hα hout

end CFSG.Sporadic.HNOddCore
