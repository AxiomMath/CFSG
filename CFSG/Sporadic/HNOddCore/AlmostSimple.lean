module

public import CFSG.Sporadic.HNOddCore.AllExt
public import CFSG.Sporadic.FischerOddCore.AlmostSimple
public import CFSG.Sporadic.HNSchreier.FullAut
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
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
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Sporadic.FischerOddCore.Basic

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.FischerOddCore

theorem inf_subgroupOf_normal {G : Type*} [Group G] {A B : Subgroup G} (hA : A.Normal) :
    ((A ⊓ B).subgroupOf B).Normal := by
  refine ⟨fun x hx b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hA.conj_mem _ hxA _
  · exact (b * x * b⁻¹).2

theorem oddCore_inf_normal_bot {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hA : A.Normal) (hB : CFSG.oddCore B = ⊥) : CFSG.oddCore ↥(A ⊓ B) = ⊥ := by
  have := inf_subgroupOf_normal (B := B) hA
  exact oddCore_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    (oddCore_normal_bot hB _)

theorem oddCore_bot_of_map_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {K : Subgroup G} (h : CFSG.oddCore ↥(K.map f) = ⊥) :
    CFSG.oddCore ↥K = ⊥ :=
  oddCore_bot_of_mulEquiv (K.equivMapOfInjective f hf) h

variable {X : Type*} [Group X] {S : Subgroup X} [S.Normal]

@[expose] def conjTransportS {G0 : Type*} [Group G0] {Q : Subgroup G0} (θ : S ≃* Q) :
    X →* MulAut Q where
  toFun x := (θ.symm.trans (MulAut.conjNormal x)).trans θ
  map_one' := by
    ext q
    simp
  map_mul' x y := by
    ext q
    simp [map_mul, MulAut.mul_apply]

theorem conjTransportS_of_mem {G0 : Type*} [Group G0] {Q : Subgroup G0} (θ : S ≃* Q) (s : S) :
    conjTransportS θ (s : X) = MulAut.conj (θ s) := by
  refine MulEquiv.ext fun q => ?_
  show θ (MulAut.conjNormal (s : X) (θ.symm q)) = _
  rw [MulAut.conj_apply]
  have e : MulAut.conjNormal (s : X) (θ.symm q) = s * θ.symm q * s⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conjTransportS_injective {G0 : Type*} [Group G0] {Q : Subgroup G0} (θ : S ≃* Q)
    (hC : Subgroup.centralizer (S : Set X) = ⊥) : Function.Injective (conjTransportS θ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : conjTransportS θ x (θ ⟨s, hs⟩) = θ (MulAut.conjNormal x ⟨s, hs⟩) := by
    show θ (MulAut.conjNormal x (θ.symm (θ ⟨s, hs⟩))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hx, MulAut.one_apply] at h1
  have h2 := congrArg Subtype.val (θ.injective h1)
  rw [MulAut.conjNormal_apply] at h2
  change s = x * s * x⁻¹ at h2
  calc s * x = x * s * x⁻¹ * x := by rw [← h2]
    _ = x * s := by group

@[expose] def autR :
    RH ≃* MulAut JH := MulEquiv.ofBijective conjR conjR_bijective

@[expose] def hnEmbed
    (θ : S ≃* JH) : X →* RH where
  toFun x := autR.symm (conjTransportS θ x)
  map_one' := by
    apply autR.injective
    rw [MulEquiv.apply_symm_apply, map_one, map_one]
  map_mul' x y := by
    apply autR.injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]

theorem hnEmbed_injective
    (θ : S ≃* JH) (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    Function.Injective (hnEmbed θ) :=
  fun _ _ h => conjTransportS_injective θ hC (autR.symm.injective h)

theorem hnEmbed_of_mem
    (θ : S ≃* JH) (s : S) : hnEmbed θ s = jR (θ s) := by
  show autR.symm (conjTransportS θ s) = jR (θ s)
  rw [conjTransportS_of_mem, MulEquiv.symm_apply_eq]
  exact (conjR_JH (θ s)).symm

theorem hnEmbed_mem_of_odd
    (θ : S ≃* JH) (hC : Subgroup.centralizer (S : Set X) = ⊥)
    [Finite X] {x : X} (hx : Odd (orderOf x)) : x ∈ S := by
  have hf := hnEmbed_injective θ hC
  have hfx : Odd (orderOf (hnEmbed θ x)) := by rwa [orderOf_injective _ hf x]
  obtain ⟨g, hg⟩ := mem_of_odd_of_sq_mem sq_mem_range_jR hfx
  have e : hnEmbed θ (θ.symm g : X) = hnEmbed θ x := by
    rw [hnEmbed_of_mem, MulEquiv.apply_symm_apply, hg]
  rw [← hf e]
  exact (θ.symm g).2

theorem hnEmbed_map_inf
    (θ : S ≃* JH) (hC : Subgroup.centralizer (S : Set X) = ⊥) (t : X) :
    (S ⊓ Subgroup.centralizer ({t} : Set X)).map (hnEmbed θ) =
      jR.range ⊓ Subgroup.centralizer ({hnEmbed θ t} : Set RH) := by
  have hf := hnEmbed_injective θ hC
  ext p
  rw [Subgroup.mem_map, Subgroup.mem_inf, sub_mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxS, hxt⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxt
    refine ⟨⟨θ ⟨x, hxS⟩, ?_⟩, ?_⟩
    · rw [← hnEmbed_of_mem]
    · rw [← map_mul, hxt, map_mul]
  · rintro ⟨⟨g, rfl⟩, hpt⟩
    have hs : hnEmbed θ (θ.symm g : X) = jR g := by
      rw [hnEmbed_of_mem, MulEquiv.apply_symm_apply]
    refine ⟨θ.symm g, Subgroup.mem_inf.2 ⟨(θ.symm g).2,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hs⟩
    apply hf
    rw [map_mul, map_mul, hs, hpt]

theorem oddCore_CR_of_involution
    {r : RH} (h2 : r ^ 2 = 1) (h1 : r ≠ 1) :
    CFSG.oddCore (Subgroup.centralizer ({r} : Set RH)) = ⊥ := by
  by_cases hout : IsOuter r
  · exact ctuc_hn_all_extension_involution_centralizers_odd_core_trivial.2 r h2 h1 hout
  · obtain ⟨s, rfl⟩ := exists_of_not_isOuter hout
    have hs2 : s ^ 2 = 1 := jR_injective (by rw [map_pow, h2, map_one])
    have hs1 : s ≠ 1 := fun h => h1 (by rw [h, map_one])
    exact (ctuc_hn_all_extension_involution_centralizers_odd_core_trivial.1 s hs2 hs1).2

theorem ctuc_hn_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* Blueprint.NativeSporadic.HN))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    (S.index = 1 ∨ S.index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨e⟩ := hS
  set θ : S ≃* JH := e.trans hnEquivJ
  have hf := hnEmbed_injective θ hC
  refine ⟨?_, fun t ht => ?_⟩
  · have hle := Nat.card_le_card_of_injective _ hf
    have hi := S.card_mul_index
    rw [Nat.card_congr θ.toEquiv, card_JH] at hi
    rw [card_RH] at hle
    have hpos : 0 < Nat.card X := Nat.card_pos
    generalize S.index = k at hi ⊢
    generalize Nat.card X = n at hi hle hpos
    omega
  · have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have hft2 : (hnEmbed θ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
    have hft1 : hnEmbed θ t ≠ 1 := by
      intro h
      have h1 : t = 1 := hf (h.trans (map_one _).symm)
      rw [h1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have hK0 : CFSG.oddCore ↥(jR.range ⊓ Subgroup.centralizer ({hnEmbed θ t} : Set RH)) = ⊥ :=
      oddCore_inf_normal_bot range_jR_normal (oddCore_CR_of_involution hft2 hft1)
    have hK : CFSG.oddCore ↥(S ⊓ Subgroup.centralizer ({t} : Set X)) = ⊥ := by
      refine oddCore_bot_of_map_injective hf ?_
      rw [hnEmbed_map_inf θ hC t]
      exact hK0
    have hKC : S ⊓ Subgroup.centralizer ({t} : Set X) ≤ Subgroup.centralizer ({t} : Set X) :=
      inf_le_right
    refine oddCore_eq_bot_of_le ((S ⊓ Subgroup.centralizer ({t} : Set X)).subgroupOf _) ?_
      (oddCore_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC) hK)
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨hnEmbed_mem_of_odd θ hC ?_, x.2⟩
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem_oddCore hx

end CFSG.Sporadic.HNOddCore
