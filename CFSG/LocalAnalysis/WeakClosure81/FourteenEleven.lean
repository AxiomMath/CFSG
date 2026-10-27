module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix
public import CFSG.LocalAnalysis.WeakClosure81.SixFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_mul_eq_of_mem_normalizer {A : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (A : Set G)) (g : G) :
    conjSubgroup A (m * g) = conjSubgroup A g := by
  rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.2 hm]

theorem commutator_conjSubgroup_le {M V₀ V X : Subgroup G} {g m : G}
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hN₀ : Subgroup.normalizer (V₀ : Set G) = M)
    (hXV₀ : ⁅V, X⁆ ≤ V₀) (hm : m ∈ M) :
    ⁅conjSubgroup V g, conjSubgroup X (m * g)⁆ ≤ conjSubgroup V₀ g := by
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hM hm
  have hmV₀ : m ∈ Subgroup.normalizer (V₀ : Set G) := by rw [hN₀]; exact hm
  rw [← conjSubgroup_mul_eq_of_mem_normalizer hmV g,
    ← conjSubgroup_mul_eq_of_mem_normalizer hmV₀ g]
  calc ⁅conjSubgroup V (m * g), conjSubgroup X (m * g)⁆
      = conjSubgroup ⁅V, X⁆ (m * g) := (conjSubgroup_commutator V X (m * g)).symm
    _ ≤ conjSubgroup V₀ (m * g) := conjSubgroup_mono hXV₀ (m * g)

theorem card_eq_two_of_le_of_rk_le_one {D A : Subgroup G} (hD : IsPGroup 2 D)
    (hDA : D ≤ A) (hne : D ≠ ⊥) (hA : rk ↥A ≤ 1) : Nat.card D = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hD
  have hkpos : 1 ≤ k := by
    have hlt : 1 < Nat.card ↥D := (Subgroup.one_lt_card_iff_ne_bot D).2 hne
    rw [hk] at hlt
    by_contra hk1
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hlt
    exact lt_irrefl 1 hlt
  have hkle : k ≤ 1 := by
    have hrk : rk ↥D = k := by
      unfold rk
      rw [hk, padicValNat.prime_pow]
    calc k = rk ↥D := hrk.symm
      _ ≤ rk ↥A := rk_mono hDA
      _ ≤ 1 := hA
  have hk1 : k = 1 := le_antisymm hkle hkpos
  rw [hk, hk1, pow_one]

theorem exists_ne_one_mem_inf_centralizer {W R C : Subgroup G} (hRW : R ≤ W)
    (hR : Nat.card R = 4) (hC : C.relIndex W = 2) :
    ∃ z ∈ R ⊓ C, z ≠ 1 := by
  have hle : C.relIndex R ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right hRW (E3.relIndex_ne_zero' W C)
    rwa [hC] at h
  have hmul : C.relIndex R * Nat.card ↥(C ⊓ R) = 4 := by
    rw [Subgroup.relIndex_mul_card, hR]
  have hcard : 2 ≤ Nat.card ↥(C ⊓ R) := by
    have h2 : 4 ≤ 2 * Nat.card ↥(C ⊓ R) := by
      calc 4 = C.relIndex R * Nat.card ↥(C ⊓ R) := hmul.symm
        _ ≤ 2 * Nat.card ↥(C ⊓ R) := Nat.mul_le_mul_right _ hle
    omega
  have hne : C ⊓ R ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    omega
  haveI : Nontrivial ↥(C ⊓ R) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(C ⊓ R))
  refine ⟨(z : G), Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 z.2).2,
    (Subgroup.mem_inf.1 z.2).1⟩, ?_⟩
  intro hz1
  exact hz (Subtype.ext (by simpa using hz1))

theorem normalizer_zpowers_le_rankThreeGamma {R : Subgroup G} {z : G} {M : Subgroup G}
    (hzR : z ∈ R) (hz : orderOf z = 2) (hR : IsElemAbelian 2 R)
    (hΓ : rankThreeGamma 1 2 R ≤ M) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M := by
  have hQR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.2 hzR
  have hQel : IsElemAbelian 2 (Subgroup.zpowers z) :=
    CFSG.Open.IsElemAbelian.mono hR hQR
  have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hz, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank 2 (Subgroup.zpowers z) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQel hcard
  have hle : Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ rankThreeGamma 1 2 R := by
    rw [rankThreeGamma, GLBCore]
    exact le_sSup ⟨Subgroup.zpowers z, hQR, hrank, rfl⟩
  exact hle.trans hΓ

theorem rk_conjSubgroup_V₀_inf_le_one {M V₀ V X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hN₀ : Subgroup.normalizer (V₀ : Set G) = M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀) (hgen : ConjGenerated M V₀ V)
    {g : G} (hg : g ∉ M) (hXM : X ≤ M)
    (hX2 : (Subgroup.centralizer (X : Set G)).relIndex V = 2) (hXV₀ : ⁅V, X⁆ ≤ V₀) :
    rk ↥(conjSubgroup V₀ g ⊓ V) ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVnotC : ¬ V ≤ Subgroup.centralizer (X : Set G) := by
    intro hle
    have h1 : (Subgroup.centralizer (X : Set G)).relIndex V = 1 :=
      Subgroup.relIndex_eq_one.2 hle
    rw [h1] at hX2
    norm_num at hX2
  obtain ⟨x, hxX, hxV⟩ : ∃ x ∈ X, ¬ V ≤ Subgroup.centralizer ({x} : Set G) := by
    by_contra h
    apply hVnotC
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x' hx'
    have hxv : v ∈ Subgroup.centralizer ({x'} : Set G) := by
      by_contra hc
      exact h ⟨x', hx', fun hle => hc (hle hv)⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxv).symm
  have hxM : x ∈ M := hXM hxX
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := le_of_eq hN₀.symm
  have hxs : x ∈ stabTil V₀ V := le_stabTil hM hM₀ hxM
  have hxTil : x ∈ F11.CTilde M V₀ V := by
    refine (mem_cTilde_iff hV hM).2 ⟨hxM, hxs, ?_⟩
    rw [actTil_eq_one_iff]
    intro v hv
    have h1 : ⁅v, x⁆ ∈ V₀ := hXV₀ (Subgroup.commutator_mem_commutator hv hxX)
    have h2 : ⁅x, v⁆ ∈ V₀ := by
      have := V₀.inv_mem h1
      rwa [commutatorElement_inv] at this
    simpa only [commutatorElement_def] using h2
  have hbound : E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
    have hsub : ({x} : Set G) ⊆ (X : Set G) := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rwa [hy]
    have hle : V ⊓ Subgroup.centralizer (X : Set G) ≤
        V ⊓ Subgroup.centralizer ({x} : Set G) :=
      inf_le_inf_left V (Subgroup.centralizer_le hsub)
    have hrel : (V ⊓ Subgroup.centralizer (X : Set G)).relIndex V =
        (Subgroup.centralizer (X : Set G)).relIndex V :=
      Subgroup.inf_relIndex_left (G := G) (H := V)
        (K := Subgroup.centralizer (X : Set G))
    calc E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G))
        ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (X : Set G)) := E3.mQuot_mono hle
      _ = 1 := by
          unfold E3.mQuot
          rw [hrel, hX2]
          exact padicValNat_self
  exact (mQuot_centralizer_ge_rk_conjSubgroup_inf hV hV₀ hM hN₀ hTI hgen hg hxTil hxV).trans
    hbound

theorem exists_mem_not_le_centralizer_conjSubgroup {M V₀ V X S : Subgroup G} {g : G}
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hgen : ConjGenerated M V₀ V)
    (hXV : ¬ V ≤ Subgroup.centralizer (X : Set G))
    (hS : S ≤ conjSubgroup V g) (hSV₀ : ¬ S ≤ conjSubgroup V₀ g) :
    ∃ m ∈ M, ¬ S ≤ Subgroup.centralizer (conjSubgroup X (m * g) : Set G) := by
  by_contra h
  push Not at h
  let T : Set G := {t : G | ∃ m ∈ M, t ∈ conjSubgroup X m}
  have hS'V : conjSubgroup S g⁻¹ ≤ V := by
    have h' := E3.conjSubgroup_mono_left g⁻¹ hS
    rwa [E3.conjSubgroup_conj_inv V g] at h'
  have hS'V₀ : ¬ conjSubgroup S g⁻¹ ≤ V₀ := by
    intro hle
    apply hSV₀
    have h' := E3.conjSubgroup_mono_left g hle
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h'
  have hS'C : conjSubgroup S g⁻¹ ≤ Subgroup.centralizer (T : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : ∃ m ∈ M, t ∈ conjSubgroup X m := ht
    obtain ⟨m, hmM, htm⟩ := ht'
    have hSm : S ≤ Subgroup.centralizer (conjSubgroup X (m * g) : Set G) := h m hmM
    have hxS : g⁻¹ * x * g ∈ S := E3.mem_conjSubgroup_inv_iff.1 hx
    have hu : g⁻¹ * t * g ∈ conjSubgroup X (m * g) := by
      rw [mem_conjSubgroup_iff]
      have he : (m * g) * (g⁻¹ * t * g) * (m * g)⁻¹ = m * t * m⁻¹ := by group
      rw [he]
      exact (mem_conjSubgroup_iff).1 htm
    have hcomm := (Subgroup.mem_centralizer_iff.1 (hSm hxS)) (g⁻¹ * t * g) hu
    have hcong := congrArg (fun z => g * z * g⁻¹) hcomm
    have h1 : g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ = t * x := by group
    have h2 : g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ = x * t := by group
    rw [h1, h2] at hcong
    exact hcong
  have hconj : ∀ m ∈ M, ∀ w ∈ Subgroup.centralizer (T : Set G),
      m * w * m⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    intro m hm w hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    intro t ht
    have ht' : ∃ m' ∈ M, t ∈ conjSubgroup X m' := ht
    obtain ⟨m', hm'M, htm'⟩ := ht'
    have ht'' : ∃ m₀ ∈ M, m⁻¹ * t * m ∈ conjSubgroup X m₀ := by
      refine ⟨m' * m, M.mul_mem hm'M hm, ?_⟩
      rw [mem_conjSubgroup_iff] at htm' ⊢
      have he : (m' * m) * (m⁻¹ * t * m) * (m' * m)⁻¹ = m' * t * m'⁻¹ := by group
      rw [he]
      exact htm'
    have htT : m⁻¹ * t * m ∈ T := ht''
    have hcomm := hw (m⁻¹ * t * m) htT
    calc t * (m * w * m⁻¹) = m * ((m⁻¹ * t * m) * w) * m⁻¹ := by group
      _ = m * (w * (m⁻¹ * t * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * w * m⁻¹) * t := by group
  have hconjW : ∀ m ∈ M, ∀ w ∈ V ⊓ Subgroup.centralizer (T : Set G),
      m * w * m⁻¹ ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
    intro m hm w hw
    obtain ⟨hwV, hwC⟩ := Subgroup.mem_inf.1 hw
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hM hm) w).1 hwV,
      hconj m hm w hwC⟩
  have hMW : M ≤ Subgroup.normalizer (V ⊓ Subgroup.centralizer (T : Set G)) := by
    intro m hm
    intro w
    exact ⟨fun hw => hconjW m hm w hw,
      fun hw => by
        have h' := hconjW m⁻¹ (M.inv_mem hm) (m * w * m⁻¹) hw
        simpa [mul_assoc] using h'⟩
  have hS'W : conjSubgroup S g⁻¹ ≤ V ⊓ Subgroup.centralizer (T : Set G) :=
    le_inf hS'V hS'C
  have hnot : ¬ (V ⊓ Subgroup.centralizer (T : Set G)) ≤ V₀ :=
    fun hle => hS'V₀ (hS'W.trans hle)
  have hW : V ⊓ Subgroup.centralizer (T : Set G) = V :=
    eq_of_normalizer_of_not_le_of_conjGenerated hgen inf_le_left hMW hnot
  have hVCT : V ≤ Subgroup.centralizer (T : Set G) := by
    rw [← hW]; exact inf_le_right
  apply hXV
  refine hVCT.trans ?_
  refine Subgroup.centralizer_le ?_
  intro x hx
  have hxT : ∃ m ∈ M, x ∈ conjSubgroup X m := ⟨1, M.one_mem, by rwa [conjSubgroup_one]⟩
  exact hxT

theorem commutator_eq_of_relIndex_two {W Y S : Subgroup G} (hW : IsMulCommutative W)
    (hY : Y ≤ Subgroup.normalizer (W : Set G))
    (hidx : (Subgroup.centralizer (Y : Set G)).relIndex W = 2)
    (hS : S ≤ W) (hSY : ¬ S ≤ Subgroup.centralizer (Y : Set G)) :
    ⁅W, Y⁆ = ⁅S, Y⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono hS le_rfl)
  refine Subgroup.commutator_le.2 ?_
  intro w hw y hy
  let C : Subgroup G := Subgroup.centralizer (Y : Set G)
  obtain ⟨s, hsS, hsC⟩ : ∃ s ∈ S, s ∉ C := by
    by_contra h
    apply hSY
    intro x hx
    by_contra hxC
    exact h ⟨x, hx, hxC⟩
  have hHs : s ∈ W := hS hsS
  by_cases hwC : w ∈ C
  · have hwy : ⁅w, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2
        ((Subgroup.mem_centralizer_iff.1 hwC) y hy).symm
    rw [hwy]
    exact Subgroup.one_mem _
  · have hsub : (C.subgroupOf W).index = 2 := by
      rw [← Subgroup.relIndex_top_right (H := C.subgroupOf W),
        ← Subgroup.subgroupOf_self W, Subgroup.relIndex_subgroupOf le_rfl]
      exact hidx
    have hmem : (⟨w, hw⟩ : ↥W) * (⟨s, hHs⟩ : ↥W)⁻¹ ∈ C.subgroupOf W := by
      rw [Subgroup.mul_mem_iff_of_index_two hsub]
      constructor
      · intro hwH
        exact absurd (Subgroup.mem_subgroupOf.1 hwH) hwC
      · intro hsH
        have hs : s⁻¹ ∈ C := Subgroup.mem_subgroupOf.1 hsH
        exact absurd (C.inv_mem_iff.1 hs) hsC
    have hc : w * s⁻¹ ∈ C := Subgroup.mem_subgroupOf.1 hmem
    have hcW : w * s⁻¹ ∈ W := W.mul_mem hw (W.inv_mem hHs)
    have hcy : ⁅w * s⁻¹, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2
        ((Subgroup.mem_centralizer_iff.1 hc) y hy).symm
    have hsyW : ⁅s, y⁆ ∈ W := by
      have hyW : y ∈ Subgroup.normalizer (W : Set G) := hY hy
      have h1 : y * s⁻¹ * y⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 hyW s⁻¹).1 (W.inv_mem hHs)
      have h2 : s * (y * s⁻¹ * y⁻¹) ∈ W := W.mul_mem hHs h1
      simpa [commutatorElement_def, mul_assoc] using h2
    have hcommW : (w * s⁻¹) * ⁅s, y⁆ = ⁅s, y⁆ * (w * s⁻¹) := by
      haveI : IsMulCommutative ↥W := hW
      exact congrArg Subtype.val (mul_comm' (⟨w * s⁻¹, hcW⟩ : ↥W) ⟨⁅s, y⁆, hsyW⟩)
    have hcomm : (w * s⁻¹) * ⁅s, y⁆ * (w * s⁻¹)⁻¹ = ⁅s, y⁆ := by
      rw [hcommW, mul_assoc, mul_inv_cancel, mul_one]
    have heq : ⁅w, y⁆ = ⁅s, y⁆ := by
      calc ⁅w, y⁆ = ⁅(w * s⁻¹) * s, y⁆ := by
            rw [show (w * s⁻¹) * s = w by group]
        _ = (w * s⁻¹) * ⁅s, y⁆ * (w * s⁻¹)⁻¹ * ⁅w * s⁻¹, y⁆ :=
            commutatorElement_mul_left_eq_conj_mul (w * s⁻¹) s y
        _ = ⁅s, y⁆ := by rw [hcy, hcomm, mul_one]
    rw [heq]
    exact Subgroup.commutator_mem_commutator hsS hy

theorem conjSubgroup_mul_le_of_rankThreeGamma_le {M V X R : Subgroup G} {g : G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hRV : R ≤ conjSubgroup V g) (hR : Nat.card R = 4)
    (hΓ : rankThreeGamma 1 2 R ≤ M)
    (hX2 : (Subgroup.centralizer (X : Set G)).relIndex V = 2)
    {m : G} (hm : m ∈ M) :
    conjSubgroup X (m * g) ≤ M := by
  let Y : Subgroup G := conjSubgroup X (m * g)
  have hVmg : conjSubgroup V (m * g) = conjSubgroup V g :=
    conjSubgroup_mul_eq_of_mem_normalizer (hM hm) g
  have hYcen : Subgroup.centralizer (Y : Set G) =
      conjSubgroup (Subgroup.centralizer (X : Set G)) (m * g) :=
    (E3.conjSubgroup_centralizer X (m * g)).symm
  have hidx : (Subgroup.centralizer (Y : Set G)).relIndex (conjSubgroup V g) = 2 := by
    rw [hYcen, ← hVmg, E3.relIndex_conjSubgroup]
    exact hX2
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_inf_centralizer hRV hR hidx
  have hzR : z ∈ R := (Subgroup.mem_inf.1 hz).1
  have hzC : z ∈ Subgroup.centralizer (Y : Set G) := (Subgroup.mem_inf.1 hz).2
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hRel : IsElemAbelian 2 R := CFSG.Open.IsElemAbelian.mono hVg hRV
  have hz2 : z ^ 2 = 1 := hVg.2 z (hRV hzR)
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hYcen' : Y ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hyz : Commute y z := (Subgroup.mem_centralizer_iff.1 hzC) y hy
    exact (hyz.zpow_right n).symm
  have hYnorm : Y ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    hYcen'.trans (Subgroup.centralizer_le_normalizer _)
  exact hYnorm.trans (normalizer_zpowers_le_rankThreeGamma hzR hzord hRel hΓ)

theorem fourteen_eleven {M V₀ V X R : Subgroup G} {g : G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hN₀ : Subgroup.normalizer (V₀ : Set G) = M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀) (hgen : ConjGenerated M V₀ V)
    (hg : g ∉ M) (hRV : R ≤ V ⊓ conjSubgroup V g) (hR : Nat.card R = 4)
    (hΓ : rankThreeGamma 1 2 R ≤ M)
    (hXM : X ≤ M) (hX2 : (Subgroup.centralizer (X : Set G)).relIndex V = 2)
    (hXV₀ : ⁅V, X⁆ ≤ V₀) :
    Nat.card ↥⁅V, X⁆ = 2 ∧ g ^ 2 ∉ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRV_V : R ≤ V := hRV.trans inf_le_left
  have hRVg : R ≤ conjSubgroup V g := hRV.trans inf_le_right
  have hVnotC : ¬ V ≤ Subgroup.centralizer (X : Set G) := by
    intro hle
    have h1 : (Subgroup.centralizer (X : Set G)).relIndex V = 1 :=
      Subgroup.relIndex_eq_one.2 hle
    rw [h1] at hX2
    norm_num at hX2
  have hrkV₀ : rk ↥(conjSubgroup V₀ g ⊓ V) ≤ 1 :=
    rk_conjSubgroup_V₀_inf_le_one hV hV₀ hM hN₀ hTI hgen hg hXM hX2 hXV₀
  have hrkR : rk ↥R = 2 := by
    unfold rk
    rw [hR, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hRnotV₀g : ¬ R ≤ conjSubgroup V₀ g := by
    intro hle
    have hle' : R ≤ conjSubgroup V₀ g ⊓ V := le_inf hle hRV_V
    have h2 : (2 : ℕ) ≤ 1 := by
      calc 2 = rk ↥R := hrkR.symm
        _ ≤ rk ↥(conjSubgroup V₀ g ⊓ V) := rk_mono hle'
        _ ≤ 1 := hrkV₀
    omega
  obtain ⟨m, hmM, hmR⟩ :=
    exists_mem_not_le_centralizer_conjSubgroup hM hgen hVnotC hRVg hRnotV₀g
  let Y : Subgroup G := conjSubgroup X (m * g)
  have hmR' : ¬ R ≤ Subgroup.centralizer (Y : Set G) := hmR
  have hYM : Y ≤ M :=
    conjSubgroup_mul_le_of_rankThreeGamma_le hV hM hRVg hR hΓ hX2 hmM
  have hVmg : conjSubgroup V (m * g) = conjSubgroup V g :=
    conjSubgroup_mul_eq_of_mem_normalizer (hM hmM) g
  have hYnorm : Y ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    have h := E3.conjSubgroup_mono_left (m * g) (hXM.trans hM)
    rw [E3.conjSubgroup_normalizer, hVmg] at h
    exact h
  have hYcen : Subgroup.centralizer (Y : Set G) =
      conjSubgroup (Subgroup.centralizer (X : Set G)) (m * g) :=
    (E3.conjSubgroup_centralizer X (m * g)).symm
  have hidx : (Subgroup.centralizer (Y : Set G)).relIndex (conjSubgroup V g) = 2 := by
    rw [hYcen, ← hVmg, E3.relIndex_conjSubgroup]
    exact hX2
  have hcomm : ⁅conjSubgroup V g, Y⁆ = ⁅R, Y⁆ :=
    commutator_eq_of_relIndex_two (E3.isElemAbelian_conjSubgroup hV g).1 hYnorm hidx hRVg hmR'
  have hDV₀ : ⁅conjSubgroup V g, Y⁆ ≤ conjSubgroup V₀ g :=
    commutator_conjSubgroup_le hM hN₀ hXV₀ hmM
  have hDle : ⁅R, Y⁆ ≤ conjSubgroup V₀ g := hcomm ▸ hDV₀
  have hDV : ⁅R, Y⁆ ≤ V := by
    refine Subgroup.commutator_le.2 ?_
    intro r hr y hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hM (hYM hy)
    have hrV : r ∈ V := hRV_V hr
    have h1 : y * r * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hyN r).1 hrV
    have h2 : (y * r * y⁻¹) * r⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hrV)
    have he : ⁅r, y⁆ = ((y * r * y⁻¹) * r⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [he]
    exact V.inv_mem h2
  have hDinf : ⁅R, Y⁆ ≤ conjSubgroup V₀ g ⊓ V := le_inf hDle hDV
  have hDne : ⁅R, Y⁆ ≠ ⊥ := by
    intro hbot
    apply hmR'
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : ⁅r, y⁆ ∈ ⁅R, Y⁆ := Subgroup.commutator_mem_commutator hr hy
    rw [hbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hDcard : Nat.card ↥⁅R, Y⁆ = 2 :=
    card_eq_two_of_le_of_rk_le_one ((B2F.isPGroup_of_isElemAbelian hV).to_le hDV) hDinf hDne
      hrkV₀
  have hcard : Nat.card ↥⁅V, X⁆ = 2 := by
    have hconj : conjSubgroup ⁅V, X⁆ (m * g) = ⁅R, Y⁆ := by
      rw [conjSubgroup_commutator, hVmg]
      exact hcomm
    rw [← E3.card_conjSubgroup ⁅V, X⁆ (m * g), hconj, hDcard]
  refine ⟨hcard, ?_⟩
  intro hg2
  have hDne' : ∃ d, d ∈ ⁅R, Y⁆ ∧ d ≠ 1 := by
    haveI : Nontrivial ↥⁅R, Y⁆ := (Subgroup.nontrivial_iff_ne_bot _).2 hDne
    obtain ⟨d, hd⟩ := exists_ne (1 : ↥⁅R, Y⁆)
    exact ⟨(d : G), d.2, fun hd1 => hd (Subtype.ext (by simpa using hd1))⟩
  obtain ⟨d, hdD, hd1⟩ := hDne'
  have hdV₀g : d ∈ conjSubgroup V₀ g := (Subgroup.mem_inf.1 (hDinf hdD)).1
  have hdV : d ∈ V := (Subgroup.mem_inf.1 (hDinf hdD)).2
  have hy₁V₀ : g * d * g⁻¹ ∈ V₀ := (mem_conjSubgroup_iff).1 hdV₀g
  have hy₁1 : g * d * g⁻¹ ≠ 1 := by
    intro h
    apply hd1
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using h'
  have hy₁Vg : g * d * g⁻¹ ∈ conjSubgroup V g := by
    rw [mem_conjSubgroup_iff]
    have hg2N : g ^ 2 ∈ Subgroup.normalizer (V : Set G) := hM hg2
    have h := (Subgroup.mem_normalizer_iff.1 hg2N d).1 hdV
    simpa [pow_two, mul_assoc] using h
  have hEne : V₀ ⊓ conjSubgroup V g ≠ ⊥ := by
    intro hbot
    have hmem : g * d * g⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.2 ⟨hy₁V₀, hy₁Vg⟩
    rw [Subgroup.mem_bot] at hmem
    exact hy₁1 hmem
  have hEnV₀g : ¬ V₀ ⊓ conjSubgroup V g ≤ conjSubgroup V₀ g := by
    intro hle
    have h1 : V₀ ⊓ conjSubgroup V g ≤ conjSubgroup V₀ g ⊓ V₀ := le_inf hle inf_le_left
    rw [conjSubgroup_inf_self_eq_bot hN₀ hTI hg] at h1
    exact hEne (le_bot_iff.1 h1)
  obtain ⟨m', hm'M, hm'E⟩ :=
    exists_mem_not_le_centralizer_conjSubgroup hM hgen hVnotC inf_le_right hEnV₀g
  let Y' : Subgroup G := conjSubgroup X (m' * g)
  have hm'E' : ¬ V₀ ⊓ conjSubgroup V g ≤ Subgroup.centralizer (Y' : Set G) := hm'E
  have hY'M : Y' ≤ M :=
    conjSubgroup_mul_le_of_rankThreeGamma_le hV hM hRVg hR hΓ hX2 hm'M
  obtain ⟨e, heE, heC⟩ : ∃ e ∈ V₀ ⊓ conjSubgroup V g, e ∉ Subgroup.centralizer (Y' : Set G) := by
    by_contra h
    apply hm'E'
    intro x hx
    by_contra hxC
    exact h ⟨x, hx, hxC⟩
  obtain ⟨y', hy'Y', hy'e⟩ : ∃ y' ∈ Y', y' * e ≠ e * y' := by
    by_contra h
    apply heC
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    by_contra hne
    exact h ⟨y', hy', hne⟩
  have hcommne : ⁅e, y'⁆ ≠ 1 := by
    intro h1
    exact hy'e ((commutatorElement_eq_one_iff_mul_comm.1 h1).symm)
  have heV₀ : e ∈ V₀ := (Subgroup.mem_inf.1 heE).1
  have heVg : e ∈ conjSubgroup V g := (Subgroup.mem_inf.1 heE).2
  have hcommV₀ : ⁅e, y'⁆ ∈ V₀ := by
    have hy'M : y' ∈ M := hY'M hy'Y'
    have hy'N₀ : y' ∈ Subgroup.normalizer (V₀ : Set G) := by rw [hN₀]; exact hy'M
    have h1 : y' * e * y'⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hy'N₀ e).1 heV₀
    have h2 : (y' * e * y'⁻¹) * e⁻¹ ∈ V₀ := V₀.mul_mem h1 (V₀.inv_mem heV₀)
    have he : ⁅e, y'⁆ = ((y' * e * y'⁻¹) * e⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [he]
    exact V₀.inv_mem h2
  have hcommV₀g : ⁅e, y'⁆ ∈ conjSubgroup V₀ g := by
    have hmem : ⁅e, y'⁆ ∈ ⁅conjSubgroup V g, Y'⁆ :=
      Subgroup.commutator_mem_commutator heVg hy'Y'
    have hle : ⁅conjSubgroup V g, Y'⁆ ≤ conjSubgroup V₀ g := by
      change ⁅conjSubgroup V g, conjSubgroup X (m' * g)⁆ ≤ conjSubgroup V₀ g
      exact commutator_conjSubgroup_le hM hN₀ hXV₀ hm'M
    exact hle hmem
  have hbot : ⁅e, y'⁆ ∈ (⊥ : Subgroup G) := by
    rw [← conjSubgroup_inf_self_eq_bot hN₀ hTI hg]
    exact Subgroup.mem_inf.2 ⟨hcommV₀g, hcommV₀⟩
  rw [Subgroup.mem_bot] at hbot
  exact hcommne hbot

end CFSG.LocalAnalysis.WeakClosure81
