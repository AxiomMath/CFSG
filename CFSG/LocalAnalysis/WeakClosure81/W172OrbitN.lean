module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp64

variable {M V₀ V : Subgroup G} {x : G}

theorem w172_relIndex_uOf (h : Hyp64 1 M V₀ V x) : (UOf M V x).relIndex V = 2 := by
  have hV2 : IsPGroup 2 ↥V := B2F.isPGroup_of_isElemAbelian h.elemAbelian
  have hmq : E3.mQuot V (UOf M V x) ≤ 1 := mQuot_UOf_le h
  have hne : (UOf M V x).relIndex V ≠ 1 := fun h1 =>
    h.inCalOStar.1.2.1 ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
  obtain ⟨a, ha⟩ := hV2.exists_card_eq
  have hdvd : (UOf M V x).relIndex V ∣ 2 ^ a := by
    rw [← ha]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (UOf M V x) V)
  obtain ⟨b, -, hbeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hbeq)
  have hb1 : b ≤ 1 := by
    unfold E3.mQuot at hmq
    rw [hbeq, padicValNat.prime_pow] at hmq
    exact hmq
  rw [hbeq, show b = 1 by omega, pow_one]

theorem w172_mBar_sub_one_le_rk_nOf (h : Hyp64 1 M V₀ V x) :
    mBar M V₀ V h.elemAbelian - 1 ≤ rk ↥(NOf M V x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.elemAbelian
  have hM_le : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hVM : V ≤ M := by rw [← h.normalizer_eq]; exact Subgroup.le_normalizer
  have hindex : (UOf M V x).relIndex V = 2 := h.w172_relIndex_uOf
  have hgen : GenHyp M V x := genHyp_of_relIndex_two h hindex
  have hBne : barSub V₀ V hV (BOf M V x) ≠ ⊥ := barSub_BOf_ne_bot h hgen
  have hBnotCT : ¬ BOf M V x ≤ F11.CTilde M V₀ V := fun hle =>
    hBne ((barSub_eq_bot_iff hV hM_le h.le_normalizer₀ inf_le_right).2 hle)
  obtain ⟨u, huB, huCT⟩ : ∃ u ∈ BOf M V x, u ∉ F11.CTilde M V₀ V := by
    by_contra hcon
    refine hBnotCT fun y hy => ?_
    by_contra hy'
    exact hcon ⟨y, hy, hy'⟩
  have huM : u ∈ M := (Subgroup.mem_inf.1 huB).2
  have huVx : u ∈ conjSubgroup V x := (Subgroup.mem_inf.1 huB).1
  have huN : u ∈ Subgroup.normalizer (V : Set G) := hM_le huM
  have huVx_el : IsElemAbelian 2 (conjSubgroup V x) := E3.isElemAbelian_conjSubgroup hV x
  have hu2 : ∃ k : ℕ, orderOf u = 2 ^ k := by
    have hdvd : orderOf u ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr (huVx_el.2 u huVx)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  have hmbar : mBar M V₀ V hV ≤
      E3.mQuot V (V ⊓ Subgroup.centralizer ({u} : Set G)) := by
    by_contra hcon
    have hlt : (E3.mQuot V (V ⊓ Subgroup.centralizer ({u} : Set G)) : ℕ∞) <
        (mBar M V₀ V hV : ℕ∞) := by exact_mod_cast (not_le.1 hcon)
    exact huCT (mem_cTilde_of_mQuot_lt hV h.le hM_le h.le_normalizer₀ huM hu2
      inf_le_left inf_le_right hlt)
  haveI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  let g : MulAut ↥V := conjAct V ⟨u, huN⟩
  have hg_apply : ∀ v : ↥V, ((g v : ↥V) : G) = u * (v : G) * u⁻¹ := by
    intro v
    show ((conjAct V ⟨u, huN⟩ v : ↥V) : G) = u * (v : G) * u⁻¹
    rw [AutOn.coe_conjAct_apply]
  have hfixV : fixV (Subgroup.zpowers g) =
      (Subgroup.centralizer ({u} : Set G)).subgroupOf V := by
    ext v
    rw [mem_fixV_zpowers_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have hv' : u * (v : G) * u⁻¹ = (v : G) :=
        (hg_apply v).symm.trans (congrArg Subtype.val hv)
      have : u * (v : G) = (v : G) * u := by
        have := congrArg (fun z => z * u) hv'
        simpa [mul_assoc] using this
      exact this.symm
    · intro hv
      apply Subtype.ext
      rw [hg_apply]
      rw [← hv]
      group
  have hfix : E3.mQuot V (V ⊓ Subgroup.centralizer ({u} : Set G)) =
      rk (commV (Subgroup.zpowers g)) := by
    rw [E3.mQuot_eq_rkIdx]
    have hsub : (V ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf V =
        (Subgroup.centralizer ({u} : Set G)).subgroupOf V := by
      ext v
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩
    rw [hsub, ← hfixV, rkIdx_fixV_zpowers]
  let U' : Subgroup ↥V := (UOf M V x).subgroupOf V
  let f : ↥V →* ↥V := commHom g
  have hker : f.ker = fixV (Subgroup.zpowers g) := ker_commHom g
  have hrk_map : rk (U'.map f) + rk ↥(U' ⊓ f.ker) = rk U' := rk_map_add_rk_inf_ker f U'
  have hrk_inf : rk ↥(U' ⊓ f.ker) ≤ rk (fixV (Subgroup.zpowers g)) := by
    rw [hker]; exact rk_mono inf_le_right
  have hrkIdxU' : rkIdx U' = 1 := by
    change rkIdx ((UOf M V x).subgroupOf V) = 1
    rw [← E3.mQuot_eq_rkIdx]
    unfold E3.mQuot
    rw [hindex, padicValNat_self]
  have hrkU' : rk U' + 1 = rk ↥V := by
    have := rk_add_rkIdx U'
    omega
  have hrk_comm : rk (commV (Subgroup.zpowers g)) +
      rk (fixV (Subgroup.zpowers g)) = rk ↥V := rk_commV_add_rk_fixV g
  have hcomm_le : rk (commV (Subgroup.zpowers g)) - 1 ≤ rk (U'.map f) := by
    omega
  have hmemN : ∀ w : ↥V, (w : G) ∈ UOf M V x → ((f w : ↥V) : G) ∈ NOf M V x := by
    intro w hwU
    have hwV : (w : G) ∈ V := (Subgroup.mem_inf.1 hwU).1
    have hwMx : (w : G) ∈ conjSubgroup M x := (Subgroup.mem_inf.1 hwU).2
    have hMxN : conjSubgroup M x =
        Subgroup.normalizer (conjSubgroup V x : Set G) := by
      rw [← h.normalizer_eq, E3.conjSubgroup_normalizer]
    have hwNorm : (w : G) ∈ Subgroup.normalizer (conjSubgroup V x : Set G) := by
      rw [← hMxN]; exact hwMx
    have hcw : ((f w : ↥V) : G) = ⁅u, (w : G)⁆ := by
      show (((commHom g) w : ↥V) : G) = ⁅u, (w : G)⁆
      rw [commHom_apply]
      show (((g w * w⁻¹ : ↥V) : G)) = ⁅u, (w : G)⁆
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hg_apply, commutatorElement_def]
    rw [NOf_eq M V x hVM]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hcw]
      have huw : u * (w : G) * u⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp huN (w : G)).1 hwV
      simpa [commutatorElement_def, mul_assoc] using V.mul_mem huw (V.inv_mem hwV)
    · rw [hcw]
      have hwu : ⁅(w : G), u⁆ ∈ conjSubgroup V x := by
        rw [commutatorElement_def]
        have h1 : (w : G) * u * (w : G)⁻¹ ∈ conjSubgroup V x :=
          (Subgroup.mem_normalizer_iff.mp hwNorm u).1 huVx
        exact (conjSubgroup V x).mul_mem h1 ((conjSubgroup V x).inv_mem huVx)
      rw [show ⁅u, (w : G)⁆ = ⁅(w : G), u⁆⁻¹ from
        (commutatorElement_inv (w : G) u).symm]
      exact (conjSubgroup V x).inv_mem hwu
  have hle : (U'.map f).map V.subtype ≤ NOf M V x := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    exact hmemN w (Subgroup.mem_subgroupOf.mp hw)
  have hmap_le : rk (U'.map f) ≤ rk ↥(NOf M V x) := by
    have hcard : rk ((U'.map f).map V.subtype) = rk (U'.map f) := by
      unfold rk
      rw [Subgroup.card_map_of_injective V.subtype_injective]
    rw [← hcard]
    exact rk_mono hle
  have hmbar_le : mBar M V₀ V hV ≤ rk (commV (Subgroup.zpowers g)) := by
    rw [← hfix]
    exact hmbar
  calc mBar M V₀ V hV - 1 ≤ rk (commV (Subgroup.zpowers g)) - 1 :=
        Nat.sub_le_sub_right hmbar_le 1
    _ ≤ rk (U'.map f) := hcomm_le
    _ ≤ rk ↥(NOf M V x) := hmap_le

end Hyp64

end CFSG.LocalAnalysis.WeakClosure81

end
