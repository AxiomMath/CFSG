module

public import CFSG.Quasithin.H13.A6S13827Gi
public import CFSG.Quasithin.H13.A6S13824f

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative

namespace A6G2

theorem exists_mem_fixV_ne_one {E : Type} [CommGroup E] [Finite E] (hE : ∀ v : E, v ^ 2 = 1)
    (hE1 : (⊤ : Subgroup E) ≠ ⊥) {A : Subgroup (MulAut E)} (hA : IsPGroup 2 ↥A) :
    ∃ x ∈ fixV A, x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hE)
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hE1
    rw [← Subgroup.card_eq_one, Subgroup.card_top, hk, pow_zero]
  have h2 : 2 ∣ Nat.card E := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have h1 : (1 : E) ∈ MulAction.fixedPoints ↥A E := fun a => map_one (a : MulAut E)
  obtain ⟨b, hb, hb1⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point E h2 h1
  exact ⟨b, fun a ha => hb ⟨a, ha⟩, fun h => hb1 h.symm⟩

end A6G2

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem no_transv_VH_u33
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13314 : Stmt13_3_14)
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) :
    ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure V H) (conjClosure S.V3 H) := by
  intro h hh ht
  have : IsMulCommutative ↥(conjClosure V H) := hd.hF.F911_2.1
  have hsV := hd.secV h13315 h1356two h13314 le_rfl (conjClosure_mono S.V3_le_V le_rfl) le_rfl
    (le_normalizer_conjClosure _ _) (le_normalizer_conjClosure _ _)
    (hd.knt_VH h13315 h1356two h13314)
  obtain ⟨c, hc⟩ := ht.2
  have hq := hsV.mem_pCoreOf_of_transvU33 hU (perfect_of_mem_cComp hd.hK) hh hc
  exact ht.1 fun x hx => hsV.hQ h hq x hx

theorem card_Uγ_le_four_u33
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13314 : Stmt13_3_14)
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g)
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ')) :
    (F8.Uγ S.V3 H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ S.V3 H (g : G)) ≤ 4 := by
  have hnot := S.lemma13_8_11_one hd.hS.hNS h13315 h1356two hd.hH hd.hF h13314 s hgen
    (Or.inr (hd.no_transv_VH_u33 h13315 h1356two h13314 hU))
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hd.hF.F911_3.1
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hd.hF.toHypF91.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  have hVel := hd.hF.isElemAbelian_Vγ (g := g)
  exact hsV.card_le_four_of_not_le hU hd.hF.Uγ_le_Vγ (hd.hF.Vγ_le_H s)
    (A6Gen.comm_mem_of_elem hVel _) (A6Gen.sq_mem_of_elem hVel _) hnot

theorem A₁_le_UH_u33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) {W : Subgroup G} (hV1W : fsuV1 T V ≤ W)
    (hWU : W < conjClosure S.V3 H) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (h4 : (F8.Uγ S.V3 H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ S.V3 H (g : G)) ≤ 4) :
    F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 H := by
  by_contra hA
  have hF := hd.hF
  have hA1 : F8.A₁ (fsuV1 T V) (g : G) ⊓ conjClosure S.V3 H = ⊥ := by
    by_contra hne
    exact hA (le_of_card_eq_two_of_inf_ne_bot hF.card_A₁ hne)
  have hUγH := hF.Uγ_le_H s
  have hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤
      centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) := by
    rintro d ⟨hdU, -, hdc⟩
    refine ⟨hdU, hHW (hd.UH_le_H hdU), fun u hu => ?_⟩
    have h2 : u * d⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (hUγH hu)) _).mp
        ((conjClosure S.V3 H).inv_mem hdU)
    have h3 : d * u * d⁻¹ * u⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) ⊓ conjClosure S.V3 H := by
      refine ⟨hdc u hu, ?_⟩
      have e : d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) := by group
      rw [e]
      exact (conjClosure S.V3 H).mul_mem hdU h2
    rw [hA1, Subgroup.mem_bot] at h3
    rw [h3]
    exact W.one_mem
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hle' : (centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))).relIndex
      (conjClosure S.V3 H) ≤
        (F8.Uγ S.V3 H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ S.V3 H (g : G)) := by
    calc (centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))).relIndex
          (conjClosure S.V3 H)
        ≤ (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) :=
          Subgroup.relIndex_le_of_le_left hDH (relIndex_ne_zero' _ _)
      _ = 2 ^ mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) :=
          HypF98.relIndex_eq_two_pow_mIdx hU2
      _ ≤ 2 ^ mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) :=
          Nat.pow_le_pow_right (by norm_num) hle
      _ = _ := (hd.relIndex_Uγ_eq s).symm
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  obtain ⟨h8, -⟩ := hsU.offender_u33 hU hmax hUγH (hd.not_Uγ_le s hDγ)
    (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _) hle'
  omega

theorem mem_normalizer_Uγ_of_comm (hG1 : S.G1 ≤ H) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) {y : G}
    (hy : y * ((g : G) * S.z * (g : G)⁻¹) = ((g : G) * S.z * (g : G)⁻¹) * y) :
    y ∈ Subgroup.normalizer (F8.Uγ S.V3 H (g : G) : Set G) := by
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hd.hF.amalgamHypV.le₂]
  refine HypF98.stab_le_normalizer_Uγ s hd.hF S.V3 ?_
  rw [hstab, mem_conjSub]
  apply hG1
  show _ ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  calc S.z * ((g : G)⁻¹ * y * (g : G)) =
        (g : G)⁻¹ * (((g : G) * S.z * (g : G)⁻¹) * y) * (g : G) := by group
    _ = (g : G)⁻¹ * (y * ((g : G) * S.z * (g : G)⁻¹)) * (g : G) := by rw [hy]
    _ = (g : G)⁻¹ * y * (g : G) * S.z := by group

theorem pow_four_le_normalizer (hG1 : S.G1 ≤ H) {W : Subgroup G} (hV1W : fsuV1 T V ≤ W)
    (hWU : W ≤ conjClosure S.V3 H) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hi : (fsuV1 T V).relIndex W ∣ 2) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) {h : G} (hh : h ∈ H)
    (hhW : h * ((g : G) * S.z * (g : G)⁻¹) * h⁻¹ * ((g : G) * S.z * (g : G)⁻¹)⁻¹ ∈ W) :
    h ^ 4 ∈ Subgroup.normalizer (F8.Uγ S.V3 H (g : G) : Set G) := by
  have hF := hd.hF
  have hF1 := hF.toHypF91
  set a := (g : G) * S.z * (g : G)⁻¹ with ha
  set d := h * a * h⁻¹ * a⁻¹ with hd'
  have hdW : d ∈ W := hhW
  set e := h * d * h⁻¹ * d⁻¹ with he'
  have heV : e ∈ fsuV1 T V :=
    A6G2.comm_mem_of_relIndex_dvd_two hi (hHW hh) (hF1.H_normalizes_V₁ hh) hdW
  have hsq : ∀ x ∈ conjClosure S.V3 H, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hF.F911_3.2 x hx
  have h4 : h ^ 4 * a * (h ^ 4)⁻¹ = a :=
    A6G2.pow_four_conj_eq (d := d) (e := e) (by rw [hd']; group) (by rw [he']; group)
      (hF1.conj_eq_of_mem_V₁ hh heV) (hsq d (hWU hdW))
      (hsq e (hV1W.trans hWU heV))
  refine hd.mem_normalizer_Uγ_of_comm hG1 s ?_
  calc h ^ 4 * a = h ^ 4 * a * (h ^ 4)⁻¹ * h ^ 4 := by group
    _ = a * h ^ 4 := by rw [h4]

theorem e4_u33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) (hG1 : S.G1 ≤ H) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) (hi : (fsuV1 T V).relIndex W ∣ 2)
    (h64 : W.relIndex (conjClosure S.V3 H) = 2 ^ 6) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hAU : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 H)
    (h4 : (F8.Uγ S.V3 H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ S.V3 H (g : G)) ≤ 4) :
    (F8.Uγ S.V3 H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ S.V3 H (g : G)) = 4 ∧
      8 ≤ Nat.card (commV (autSec (autOn (F8.Uγ S.V3 H (g : G)) (conjClosure S.V3 H)) ⊤
        (W.subgroupOf (conjClosure S.V3 H)))) := by
  have hF := hd.hF
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hUγH := hF.Uγ_le_H s
  set a := (g : G) * S.z * (g : G)⁻¹ with ha
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have haA : a ∈ F8.A₁ (fsuV1 T V) (g : G) := by
    rw [F8.A₁, mem_conjSub]
    simpa [ha, mul_assoc] using hz
  have haU : a ∈ conjClosure S.V3 H := hAU haA
  have haUγ : a ∈ F8.Uγ S.V3 H (g : G) := hF.A₁_le_Uγ haA
  have hnorm : ∀ k : ↥H, (k : G) * a * (k : G)⁻¹ * a⁻¹ ∈ W →
      ∀ f ∈ F8.Uγ S.V3 H (g : G), (k : G) ^ 4 * f * ((k : G) ^ 4)⁻¹ ∈ F8.Uγ S.V3 H (g : G) :=
    fun k hk f hf => (Subgroup.mem_normalizer_iff.mp
      (hd.pow_four_le_normalizer hG1 hV1W hWU.le hHW hi s k.2 hk) f).mp hf
  have hAe := hsU.isElemAbelian2_autSec hUγH (A6Gen.comm_mem_of_elem hUγel _)
    (A6Gen.sq_mem_of_elem hUγel _)
  by_cases haW : a ∈ W
  ·
    obtain ⟨x, hx, hx1⟩ := A6G2.exists_mem_fixV_ne_one
      (fun v => by rw [pow_two]; exact hsU.sec_sq v) hsU.top_ne_bot
      (A := autSec (autOn (F8.Uγ S.V3 H (g : G)) (conjClosure S.V3 H)) ⊤
        (W.subgroupOf (conjClosure S.V3 H)))
      (fun y => ⟨1, Subtype.ext (by rw [pow_one]; exact hAe.2 y.1 y.2)⟩)
    refine hsU.e4_of_fix hU h64 hUγH (hd.not_Uγ_le s hDγ) (A6Gen.comm_mem_of_elem hUγel _)
      (A6Gen.sq_mem_of_elem hUγel _) h4 hx1 hx fun k _ _ => hnorm k ?_
    exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHW k.2) a).mp haW) (W.inv_mem haW)
  ·
    have hx1 : InternalSec.secMk (W.subgroupOf (conjClosure S.V3 H)) ⟨a, haU⟩ ≠ 1 := fun h =>
      haW ((A6Mod.secMk_eq_one_iff _).1 h)
    have hx := hsU.secMk_mem_fixV (x := ⟨a, haU⟩) hUγH fun f hf => by
      have hc := isElemAbelian_comm hUγel hf haUγ
      have e : f * a * f⁻¹ * a⁻¹ = 1 := by rw [hc]; group
      rw [e]
      exact W.one_mem
    refine hsU.e4_of_fix hU h64 hUγH (hd.not_Uγ_le s hDγ) (A6Gen.comm_mem_of_elem hUγel _)
      (A6Gen.sq_mem_of_elem hUγel _) h4 hx1 hx fun k _ hkx => hnorm k ?_
    rw [SecHyp.act_secMk] at hkx
    have h1 : InternalSec.secMk (W.subgroupOf (conjClosure S.V3 H))
        (Setup.rho (conjClosure S.V3 H) H hsU.hHX k ⟨a, haU⟩ * (⟨a, haU⟩ : ↥(conjClosure S.V3 H))⁻¹)
          = 1 := by
      rw [map_mul, map_inv, hkx, mul_inv_cancel]
    rw [A6Mod.secMk_eq_one_iff] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe] using h1

end DK

end Setting4

end CFSG.Quasithin.H13.A6
