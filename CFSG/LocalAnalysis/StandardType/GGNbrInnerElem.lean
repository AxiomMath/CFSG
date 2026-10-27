module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_conj_eq_ggBsAut_of_ggLAut_eq_conj {G : Type} [Group G] {p : ℕ}
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hK : commutator ↥K = ⊤)
    (hZ : Subgroup.center ↥K = ⊥) {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    {x : G} (hx : x ∈ Bs) (hxK : x ∉ Subgroup.centralizer (K : Set G)) {r : R}
    (hr : ggLAut K θ ⟨x, hN hx⟩ = MulAut.conj r) :
    ∃ h : ↥K, MulAut.conj h = ggBsAut hN ⟨x, hx⟩ ∧ h ≠ 1 ∧ (h : G) ∈ Bs := by
  obtain ⟨k, hkK, hk⟩ := NbrInnerMore.exists_conj_of_ggLAut_eq_conj hK θ (hN hx) hr
  have hk_eq : ∀ l : ↥K, (⟨k, hkK⟩ : ↥K) * l * (⟨k, hkK⟩ : ↥K)⁻¹ =
      ggBsAut hN ⟨x, hx⟩ l := by
    intro l
    apply Subtype.ext
    have hxlx : x * (l : G) * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hN hx) (l : G)).mp l.2
    have h1 := hk (x * (l : G) * x⁻¹) hxlx
    have h2 : (l : G) = k⁻¹ * (x * (l : G) * x⁻¹) * k := by
      rw [← h1]; group
    show k * (l : G) * k⁻¹ = x * (l : G) * x⁻¹
    calc k * (l : G) * k⁻¹ = k * (k⁻¹ * (x * (l : G) * x⁻¹) * k) * k⁻¹ := by
          conv_lhs => rw [h2]
      _ = x * (l : G) * x⁻¹ := by group
  have hmain : MulAut.conj (⟨k, hkK⟩ : ↥K) = ggBsAut hN ⟨x, hx⟩ := by
    ext l
    simpa only [MulAut.conj_apply] using congrArg Subtype.val (hk_eq l)
  have hconj_inj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    intro a b hab
    have hd : MulAut.conj (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hcent : a⁻¹ * b ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hc := congrArg (fun φ : MulAut ↥K => φ c) hd
      simp only [MulAut.conj_apply, MulAut.one_apply] at hc
      calc c * (a⁻¹ * b) = ((a⁻¹ * b) * c * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by rw [hc]
        _ = (a⁻¹ * b) * c := by group
    have hab1 : a⁻¹ * b = 1 := by simpa [hZ] using hcent
    exact inv_mul_eq_one.mp hab1
  refine ⟨⟨k, hkK⟩, hmain, ?_, ?_⟩
  ·
    intro h1
    apply hxK
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hβ : ggBsAut hN ⟨x, hx⟩ = 1 := by
      rw [← hmain, h1]
      simp
    have h2 : x * l * x⁻¹ = l := by
      have hc := congrArg (fun φ : MulAut ↥K => (φ ⟨l, hl⟩ : G)) hβ
      simpa [MulAut.one_apply, ggBsAut, normalizerMonoidHom_coe] using hc
    calc l * x = (x * l * x⁻¹) * x := by rw [h2]
      _ = x * l := by group
  ·
    have hhp : (⟨k, hkK⟩ : ↥K) ^ p = 1 := by
      apply hconj_inj
      have hxp : (⟨x, hx⟩ : ↥Bs) ^ p = 1 := Subtype.ext (hBs.2 x hx)
      calc MulAut.conj ((⟨k, hkK⟩ : ↥K) ^ p)
          = (MulAut.conj (⟨k, hkK⟩ : ↥K)) ^ p := by rw [map_pow]
        _ = (ggBsAut hN ⟨x, hx⟩) ^ p := by rw [hmain]
        _ = ggBsAut hN ((⟨x, hx⟩ : ↥Bs) ^ p) := by rw [map_pow]
        _ = ggBsAut hN 1 := by rw [hxp]
        _ = 1 := by rw [map_one]
        _ = MulAut.conj (1 : ↥K) := by rw [map_one]
    change k ∈ Bs
    refine hSC k ?_ (by simpa using congrArg Subtype.val hhp)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hβk : ggBsAut hN ⟨b, hb⟩ (⟨k, hkK⟩ : ↥K) = (⟨k, hkK⟩ : ↥K) := by
      apply hconj_inj
      calc MulAut.conj (ggBsAut hN ⟨b, hb⟩ (⟨k, hkK⟩ : ↥K))
          = ggBsAut hN ⟨b, hb⟩ * MulAut.conj (⟨k, hkK⟩ : ↥K) *
              (ggBsAut hN ⟨b, hb⟩)⁻¹ := by
            ext l
            simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
              MulAut.apply_inv_self]
        _ = ggBsAut hN ⟨b, hb⟩ * ggBsAut hN ⟨x, hx⟩ * (ggBsAut hN ⟨b, hb⟩)⁻¹ := by
            rw [hmain]
        _ = ggBsAut hN (⟨b, hb⟩ * ⟨x, hx⟩ * ⟨b, hb⟩⁻¹) := by
            rw [map_mul, map_mul, map_inv]
        _ = ggBsAut hN ⟨x, hx⟩ := by
            have hcomm : (⟨b, hb⟩ : ↥Bs) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨b, hb⟩ :=
              Subtype.ext (TableB.IsElemAbelian.comm hBs hb hx)
            rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        _ = MulAut.conj (⟨k, hkK⟩ : ↥K) := hmain.symm
    have hbk : b * (k : G) * b⁻¹ = k := by
      have hc := congrArg Subtype.val hβk
      simpa [ggBsAut, normalizerMonoidHom_coe] using hc
    calc b * k = b * k * b⁻¹ * b := by group
      _ = k * b := by rw [hbk]

theorem isComponentOf_subgroupOf_centralizer_of_conj_eq {G : Type} [Group G]
    {Bs K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ Bs)
    {h : ↥K} (hh : MulAut.conj h = ggBsAut hN ⟨x, hx⟩) {J : Subgroup G}
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G))) :
    IsComponentOf (J.subgroupOf K) (Subgroup.centralizer ({h} : Set ↥K)) := by
  have hmem : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({h} : Set ↥K) := by
    ext l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    have hconj : (h : G) * (l : G) * (h : G)⁻¹ = x * (l : G) * x⁻¹ := by
      have hc := congrArg (fun φ : MulAut ↥K => (φ l : G)) hh
      simpa [MulAut.conj_apply, ggBsAut, normalizerMonoidHom_coe] using hc
    constructor
    · rintro ⟨-, hx'⟩
      have hx'' : x * (l : G) * x⁻¹ = (l : G) := by
        calc x * (l : G) * x⁻¹ = ((l : G) * x) * x⁻¹ := by rw [← hx']
          _ = (l : G) := by group
      have hh' : (h : G) * (l : G) * (h : G)⁻¹ = (l : G) := by rw [hconj, hx'']
      apply Subtype.ext
      have hstep : (h : G) * (l : G) = (l : G) * (h : G) := by
        calc (h : G) * (l : G) = ((h : G) * (l : G) * (h : G)⁻¹) * (h : G) := by group
          _ = (l : G) * (h : G) := by rw [hh']
      exact hstep.symm
    · intro hlh
      have hlh' : (l : G) * (h : G) = (h : G) * (l : G) := congrArg Subtype.val hlh
      have hh'' : (h : G) * (l : G) * (h : G)⁻¹ = (l : G) := by rw [← hlh']; group
      have hx'' : x * (l : G) * x⁻¹ = (l : G) := by rw [← hconj, hh'']
      refine ⟨l.2, ?_⟩
      calc (l : G) * x = (x * (l : G) * x⁻¹) * x := by rw [hx'']
        _ = x * (l : G) := by group
  have h := ggIsComponentOf_subgroupOf hJ inf_le_left
  rwa [hmem] at h

end CFSG.StandardType
