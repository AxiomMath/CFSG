module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISplit
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUKb
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoordRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType.RCKK1IIISU

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1
  CFSG.StandardType.RCKK1IIISp CFSG.StandardType.LieOddCover

private theorem rckSUasm_ker_comp_mk_le_center {K Jb : Type*} [Group K] [Group Jb]
    (φ : K →* Jb) (hkerφ : φ.ker ≤ Subgroup.center K)
    (hZ2 : Subgroup.center (K ⧸ Subgroup.center K) = ⊥) :
    ((QuotientGroup.mk' (Subgroup.center Jb)).comp φ).ker ≤ Subgroup.center K := by
  intro x hx
  have hxφ : φ x ∈ Subgroup.center Jb := by
    have hx' : (QuotientGroup.mk' (Subgroup.center Jb)) (φ x) = 1 := hx
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center Jb) (φ x)).mp hx'
  rw [Subgroup.mem_center_iff] at hxφ
  have hmkx : (QuotientGroup.mk' (Subgroup.center K)) x ∈
      Subgroup.center (K ⧸ Subgroup.center K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    have hcomm : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K := by
      apply hkerφ
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [(hxφ (φ y)).symm]
      group
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) (x * y * x⁻¹ * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center K) _).mpr hcomm
    have h1' : (QuotientGroup.mk' (Subgroup.center K)) x *
        (QuotientGroup.mk' (Subgroup.center K)) y *
        ((QuotientGroup.mk' (Subgroup.center K)) x)⁻¹ *
        ((QuotientGroup.mk' (Subgroup.center K)) y)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    have key : (QuotientGroup.mk' (Subgroup.center K)) x *
        (QuotientGroup.mk' (Subgroup.center K)) y =
        ((QuotientGroup.mk' (Subgroup.center K)) x *
          (QuotientGroup.mk' (Subgroup.center K)) y *
          ((QuotientGroup.mk' (Subgroup.center K)) x)⁻¹ *
          ((QuotientGroup.mk' (Subgroup.center K)) y)⁻¹) *
          ((QuotientGroup.mk' (Subgroup.center K)) y *
          (QuotientGroup.mk' (Subgroup.center K)) x) := by group
    rw [key, h1', one_mul]
  rw [hZ2, Subgroup.mem_bot] at hmkx
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff (N := Subgroup.center K) x).mp hmkx)) y

theorem rckRowK1IIISU_holds
    (hcov : GGLieOddCover) : RCKRowK1IIISU := by
  intro Jb _ _ hodd hmark
  obtain ⟨k, φ0, hk, hsurj0, hker0⟩ := rckK1IIISU_model hcov hodd hmark
  let φ : SUG k →* Jb := φ0
  have hsurj : Function.Surjective φ := hsurj0
  have hker : φ.ker ≤ Subgroup.center (SUG k) := hker0
  have hF : Nat.card SUF = (2 ^ 1) ^ 2 := by
    have h := CFSG.LieType.Catalog.card_galoisField 2 2 (by norm_num)
    simpa using h
  have hperf : Group.IsPerfect (SUG k) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_SU (p := 2) (f := 1) hF (by omega)
      (by intro h; have h3 := congrArg Prod.fst h; simp only at h3; omega)).1
  haveI : Group.IsPerfect (SUG k) := hperf
  have hZ2 : Subgroup.center (SUG k ⧸ Subgroup.center (SUG k)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  haveI : Group.IsPerfect Jb := Group.IsPerfect.ofSurjective (f := φ) hsurj
  have hJ2 : Subgroup.center (Jb ⧸ Subgroup.center Jb) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  let ψ : SUG k →* Jb ⧸ Subgroup.center Jb := (QuotientGroup.mk' (Subgroup.center Jb)).comp φ
  have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hsurj
  have hψker : ψ.ker = Subgroup.center (SUG k) := by
    refine le_antisymm (rckSUasm_ker_comp_mk_le_center φ hker hZ2) ?_
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center (Jb ⧸ Subgroup.center Jb) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hψsurj q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hJ2, Subgroup.mem_bot] at hzc
    exact hzc
  let e : SUG k ⧸ Subgroup.center (SUG k) ≃* Jb ⧸ Subgroup.center Jb :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have he : ∀ g : SUG k, e (QuotientGroup.mk g) = ψ g := fun g => rfl
  have hdata := CFSG.StandardType.RCKK1IIp.rckK1Data_map e (rckSU_K1Data hk)
  obtain ⟨β, hβroots, hβlong, hβ2, hβV⟩ := rckSU_shortRoot hk hF
  refine ⟨e (QuotientGroup.mk (suR hk)),
    ((suV hk).map (QuotientGroup.mk' (Subgroup.center (SUG k)))).map e.toMonoidHom, hdata, ?_⟩
  refine ⟨.PSU, k, 1, β, ggRootSub (ggU .PSU k 1).D φ β 1, Or.inr rfl, le_rfl, hβroots, hβlong,
    hβ2, ⟨φ, MonoidHom.range_eq_top.mpr hsurj, hker, 1, rfl⟩, ?_⟩
  rw [he]
  refine Subgroup.mem_map.mpr ⟨φ (suR hk), ?_, rfl⟩
  let x : (ggU .PSU k 1).K := suR hk
  have hx : x ∈ (ggU .PSU k 1).D.rootGroup β := hβV (suR_mem_suV hk)
  have hconj : (MulAut.conj (1 : (ggU .PSU k 1).K)).toMonoidHom x = x := by
    show (1 : (ggU .PSU k 1).K) * x * (1 : (ggU .PSU k 1).K)⁻¹ = x
    rw [one_mul, inv_one, mul_one]
  exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_map.mpr ⟨x, hx, hconj⟩, rfl⟩

end CFSG.StandardType.RCKK1IIISU
