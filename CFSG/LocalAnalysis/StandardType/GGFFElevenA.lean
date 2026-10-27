module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

private theorem comm_of_conj_eq {H : Type} [Group H] {c d : H} (h : c * d * c⁻¹ = d) :
    c * d = d * c := by
  calc c * d = c * d * c⁻¹ * c := by group
    _ = d * c := by rw [h]

omit [Finite G] in
theorem not_caseA (h : Setting b K z) (hN : ModelN K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    {x : G} (hxb : x * b * x⁻¹ = b⁻¹) (hxz : ∀ i, x * zs z i * x⁻¹ = zs z i) (hx2 : x * x = 1)
    {k : G} (hk : k ∈ K) (hin : ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹)
    {g : G} (hgb : g * b * g⁻¹ = zs z 1 * zs z 2)
    (hgx : g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ = b) : False := by
  have hkcomm : ∀ i, k * zs z i = zs z i * k := by
    intro i
    have h1 := hin (zs z i) (zs_mem z i)
    rw [hxz i] at h1
    calc k * zs z i = k * zs z i * k⁻¹ * k := by group
      _ = zs z i * k := by rw [h1.symm]
  have hk3 : k ^ 3 = 1 := by
    obtain ⟨v, hv⟩ := hN.cen ⟨k, hk⟩ fun i => Subtype.ext (hkcomm i)
    have hmemtor : (⟨k, hk⟩ : K) ∈ tor z := by
      rw [hv]
      exact vecElt_mem_tor z v
    have h3 : (⟨k, hk⟩ : K) ^ 3 = 1 :=
      (isElemAbelian_tor h.model.pow_z h.model.comm_z).2 ⟨k, hk⟩ hmemtor
    simpa using congrArg (Subtype.val : K → G) h3
  have hk2 : k * k = 1 := by
    refine h.eq_one_of_mem (K.mul_mem hk hk) fun y hy => ?_
    have h1 : x * y * x⁻¹ = k * y * k⁻¹ := hin y hy
    have h2 : x * (k * y * k⁻¹) * x⁻¹ = k * (k * y * k⁻¹) * k⁻¹ :=
      hin (k * y * k⁻¹) (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))
    have h3 : x * (x * y * x⁻¹) * x⁻¹ = y := by
      calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
        _ = y := by rw [hx2]; group
    have h2b : k * (k * y * k⁻¹) * k⁻¹ = y := by
      rw [h2.symm, ← h1]
      exact h3
    calc (k * k) * y = (k * k) * y * (k * k)⁻¹ * (k * k) := by group
      _ = y * (k * k) := by
          rw [show (k * k) * y * (k * k)⁻¹ = k * (k * y * k⁻¹) * k⁻¹ by group, h2b]
  have hk1 : k = 1 := by
    calc k = k ^ 3 * (k * k)⁻¹ := by group
      _ = 1 := by rw [hk3, hk2]; simp
  have hxK : ∀ y ∈ K, x * y = y * x := by
    intro y hy
    have h1 : x * y * x⁻¹ = y := by
      simpa [hk1] using hin y hy
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h1]
  have hx'K : g * x * g⁻¹ ∈ K := by
    have hC : g * x * g⁻¹ ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_conj_eq hgx
    have h2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
      calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    exact hmem _ hC 1 (by rw [pow_one, pow_two]; exact h2)
  have hbz : g⁻¹ * (zs z 1 * zs z 2) * g = b := by
    calc g⁻¹ * (zs z 1 * zs z 2) * g = g⁻¹ * (g * b * g⁻¹) * g := by rw [hgb]
      _ = b := by group
  have hx't : ∀ t : K, t * t = 1 → t * (z 1 * z 2) = z 1 * z 2 * t →
      g * x * g⁻¹ * t = t * (g * x * g⁻¹) := by
    intro t ht2 htz
    have htzG : (t : G) * (zs z 1 * zs z 2) = (zs z 1 * zs z 2) * (t : G) := by
      simpa [zs] using congrArg (Subtype.val : K → G) htz
    have ht2G : (t : G) * (t : G) = 1 := by
      simpa using congrArg (Subtype.val : K → G) ht2
    have hs2 : (g⁻¹ * (t : G) * g) * (g⁻¹ * (t : G) * g) = 1 := by
      calc (g⁻¹ * (t : G) * g) * (g⁻¹ * (t : G) * g)
          = g⁻¹ * ((t : G) * (t : G)) * g := by group
        _ = 1 := by rw [ht2G]; group
    have hsconj : (g⁻¹ * (t : G) * g) * b * (g⁻¹ * (t : G) * g)⁻¹ = b := by
      calc (g⁻¹ * (t : G) * g) * b * (g⁻¹ * (t : G) * g)⁻¹
          = g⁻¹ * ((t : G) * (g * b * g⁻¹) * (t : G)⁻¹) * g := by group
        _ = g⁻¹ * ((t : G) * (zs z 1 * zs z 2) * (t : G)⁻¹) * g := by rw [hgb]
        _ = g⁻¹ * (zs z 1 * zs z 2) * g := by
              rw [show (t : G) * (zs z 1 * zs z 2) * (t : G)⁻¹ = zs z 1 * zs z 2 by
                rw [htzG]; group]
        _ = b := hbz
    have hsC : g⁻¹ * (t : G) * g ∈ Cen b :=
      Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hsconj)
    have hsK : g⁻¹ * (t : G) * g ∈ K :=
      hmem _ hsC 1 (by rw [pow_one, pow_two]; exact hs2)
    have hsx : x * (g⁻¹ * (t : G) * g) = (g⁻¹ * (t : G) * g) * x := hxK _ hsK
    calc g * x * g⁻¹ * (t : G)
        = g * (x * (g⁻¹ * (t : G) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (t : G) * g) * x) * g⁻¹ := by rw [hsx]
      _ = (t : G) * (g * x * g⁻¹) := by group
  have hinv : g * x * g⁻¹ * (zs z 1 * zs z 2) * (g * x * g⁻¹)⁻¹ = (zs z 1 * zs z 2)⁻¹ := by
    calc g * x * g⁻¹ * (zs z 1 * zs z 2) * (g * x * g⁻¹)⁻¹
        = g * (x * (g⁻¹ * (zs z 1 * zs z 2) * g) * x⁻¹) * g⁻¹ := by group
      _ = g * (x * b * x⁻¹) * g⁻¹ := by rw [hbz]
      _ = g * b⁻¹ * g⁻¹ := by rw [hxb]
      _ = (g * b * g⁻¹)⁻¹ := by group
      _ = (zs z 1 * zs z 2)⁻¹ := by rw [hgb]
  obtain ⟨t₁, t₂, ht1, ht2, ht1z, ht2z, hcase⟩ := hN.caseA
  have hx't1 : g * x * g⁻¹ * (t₁ : G) = (t₁ : G) * (g * x * g⁻¹) := hx't t₁ ht1 ht1z
  have hx't2 : g * x * g⁻¹ * (t₂ : G) = (t₂ : G) * (g * x * g⁻¹) := hx't t₂ ht2 ht2z
  have hyz : g * x * g⁻¹ * (zs z 1 * zs z 2) = (zs z 1 * zs z 2) * (g * x * g⁻¹) := by
    have h := hcase ⟨g * x * g⁻¹, hx'K⟩ (Subtype.ext hx't1) (Subtype.ext hx't2)
    simpa [zs] using congrArg (Subtype.val : K → G) h
  have hinv' : (zs z 1 * zs z 2)⁻¹ = zs z 1 * zs z 2 := by
    rw [← hinv, hyz]
    group
  have hsqu : (zs z 1 * zs z 2) * (zs z 1 * zs z 2) = 1 := by
    calc (zs z 1 * zs z 2) * (zs z 1 * zs z 2)
        = (zs z 1 * zs z 2) * (zs z 1 * zs z 2)⁻¹ := by rw [hinv']
      _ = 1 := mul_inv_cancel _
  have hzc : (zs z 1 * zs z 2) ^ 3 = 1 := by
    have hcomm : Commute (zs z 1) (zs z 2) := h.zs_comm 1 2
    rw [hcomm.mul_pow, h.zs_pow 1, h.zs_pow 2, mul_one]
  have hp2 : (zs z 1 * zs z 2) ^ 2 = 1 := by
    rw [pow_two]
    exact hsqu
  have hz3 : (zs z 1 * zs z 2) ^ 3 = zs z 1 * zs z 2 := by
    rw [show (zs z 1 * zs z 2) ^ 3 =
      (zs z 1 * zs z 2) ^ 2 * (zs z 1 * zs z 2) from pow_succ _ 2, hp2, one_mul]
  have hzone : zs z 1 * zs z 2 = 1 := by
    rw [← hz3, hzc]
  have hzoneK : z 1 * z 2 = 1 := Subtype.ext (by simpa [zs] using hzone)
  have hsingle : ∀ i : Fin 3, vecElt z (Pi.single i 1) = z i := fun i =>
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one i
  have hs : (![0, 1, 1] : Fin 3 → ZMod 3) = Pi.single 1 1 + Pi.single 2 1 := by decide
  have hvecK : vecElt z ![0, 1, 1] = 1 := by
    rw [hs, vecElt_add h.model.pow_z h.model.comm_z, hsingle 1, hsingle 2, hzoneK]
  have hv0 : (![0, 1, 1] : Fin 3 → ZMod 3) = 0 := h.model.inj _ hvecK
  have h10 : (1 : ZMod 3) = 0 := by
    have h := congrFun hv0 1
    simp at h
  exact one_ne_zero h10

end CFSG.StandardType.GGFF.Setting

end
