module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointCompl
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalGlue

import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSpecial
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalTorus
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointCoord

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique CFSG.Quasithin.H13
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open scoped MatrixGroups

private theorem radQ2_le_hypUnitriangular_ptv {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) : radQ2 h ≤ hypUnitriangular h 2 0 := by
  intro g hg
  obtain ⟨a1, -, a3, a4, a5, a6, a7, a8, a9, a10, -, a12⟩ := hg
  refine mem_hypUnitriangular.mpr ⟨?_, fun a => ?_⟩
  · intro i j hij
    rcases ix_cases i with rfl | rfl | rfl | rfl <;>
      rcases ix_cases j with rfl | rfl | rfl | rfl <;> simp at hij <;> assumption
  · rcases ix_cases a with rfl | rfl | rfl | rfl <;> assumption

private theorem exists_unitri_map_iff_ptv {F F' : Type} [Field F] [Field F'] (ρ : F ≃+* F')
    (M : SL(2, F)) :
    (∃ t : F', ((Matrix.SpecialLinearGroup.map ρ.toRingHom M : SL(2, F')) :
        Matrix (Fin 2) (Fin 2) F') = !![1, t; 0, 1]) ↔
      ∃ t : F, (M : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨ρ.symm t, ?_⟩
    have hM : (M : Matrix (Fin 2) (Fin 2) F) =
        ((M : Matrix (Fin 2) (Fin 2) F).map ρ.toRingHom).map ρ.symm.toRingHom := by
      ext i j
      simp
    rw [hM, ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rintro ⟨t, ht⟩
    refine ⟨ρ t, ?_⟩
    rw [ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem mem_radQ2_iff_of_pointPhi_ptv {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (hU : UnitaryFieldData 2 f K) {φ : (Fin 2 → F) →+ K}
    (hφ : Function.Injective φ) (q : ↥(pCoreOf 2 L1)) (g : ↥(radQ hU))
    (hqg : c₁.pointPhi φ q = radPhi hU g) :
    (g : hypSU hU 2 0) ∈ radQ2 hU ↔ (q : G) ∈ pCoreOf 2 L2 := by
  obtain ⟨x, y, c, hc, hg⟩ := g.2
  rw [radPhi_apply hU hg] at hqg
  have hxy := congrArg Multiplicative.toAdd hqg
  rw [c₁.toAdd_pointPhi, toAdd_ofAdd] at hxy
  obtain ⟨-, hy⟩ := Prod.mk.inj hxy
  rw [c₁.mem_inf_iff]
  constructor
  · intro hg2
    obtain ⟨x', c', -, hg'⟩ := (mem_radQ_inf_radQ2_iff hU).mp ⟨g.2, hg2⟩
    obtain ⟨-, rfl, -⟩ := sMat_injective hU (hg.symm.trans hg')
    exact hφ (hy.trans (map_zero φ).symm)
  · intro h0
    rw [h0, map_zero] at hy
    subst hy
    exact ((mem_radQ_inf_radQ2_iff hU).mpr ⟨x, c, (sAdm_of_y_zero_iff hU).mp hc, hg⟩).2

theorem U4qLocalData.exists_mulEquiv_parP (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {F K : Type} [Field F]
    [Field K] (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) :
    ∃ ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(parP hU),
      (∀ x : ↥(L1 ⊔ bigB L1 L2 S),
        (x : G) ∈ pCoreOf 2 L2 ↔ ((ψ x : ↥(parP hU)) : hypSU hU 2 0) ∈ radQ2 hU) ∧
      ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        ((ψ x : ↥(parP hU)) : hypSU hU 2 0) ∈
          Subgroup.normalizer (hypUnitriangular hU 2 0 : Set (hypSU hU 2 0)) := by
  classical
  haveI : Finite K := hU.finite
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  obtain ⟨H₀, hH₀B, hcomm, hcard, hconj, hH₀L, hsup⟩ := hD.exists_torus hf hH hS
  have hT : U4qTorusData L1 L2 S H₀ f := ⟨hH₀B, hcomm, hcard, hconj⟩
  obtain ⟨κ, hκ, -, -, -⟩ := hD.exists_torusCoord hH hS hT c₂ hU
  obtain ⟨ρ, φ, hφ, hρ, hφA⟩ := hD.exists_phiA hH hS c₁ c₂ hU
  obtain ⟨D, -, hDβ⟩ := c₁.exists_pointFormData hD
  obtain ⟨e, he⟩ := c₁.exists_pointComplEquiv hH hD hS hT hf hH₀L hU ρ κ
  have hKH : ∀ a ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G), ∀ b ∈ H₀, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm
  have hRQ := hT.torusCompl_le_normalizer
  have hP := hD.pCoreOf_sup_torusCompl hT hsup
  obtain ⟨hR'Q', hQR', hP'⟩ := radQ_semidirect_levHom_range_sup_u4PtTorus hU
  have he₀ : ∀ (n : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀)) (hn : (n : G) ∈ H₀),
      (e n : hypSU hU 2 0) = ((u4PtKappaEquiv hU).symm (κ ⟨n, hn⟩) : hypSU hU 2 0) := by
    intro n hn
    rw [he n 1 n (Subgroup.one_mem _) hn (one_mul _).symm]
    have h1 : c₁.α ⟨1, (Subgroup.one_mem (L1 ⊓ Subgroup.centralizer (H₀ : Set G))).1⟩ = 1 :=
      map_one c₁.α
    rw [h1, map_one, map_one, one_mul]
  have hδfix : hU.bar (hU.bar (φ (Pi.single 0 1)) * φ (Pi.single 1 1) +
      φ (Pi.single 0 1) * hU.bar (φ (Pi.single 1 1))) =
      hU.bar (φ (Pi.single 0 1)) * φ (Pi.single 1 1) +
        φ (Pi.single 0 1) * hU.bar (φ (Pi.single 1 1)) := by
    rw [map_add, map_mul, map_mul, hU.bar_bar, hU.bar_bar]
    ring
  let δ : hU.fixedField := ⟨_, (hU.mem_fixedField).mpr hδfix⟩
  have hδ : δ ≠ 0 := by
    haveI := hU.charP
    intro h0
    exact twistForm_basis_ne_zero hU.bar (hU.fixedField.subtype.comp ρ.toRingHom)
      (fun x hx => ⟨ρ.symm ⟨x, (hU.mem_fixedField).mpr hx⟩, by simp⟩) φ hρ hφ.1
      (congrArg Subtype.val h0)
  have hZQ : centerOf (pCoreOf 2 L1) ≤ pCoreOf 2 L1 := fun z hz => hz.1
  have hZc : ∀ z ∈ centerOf (pCoreOf 2 L1), ∀ x ∈ pCoreOf 2 L1, z * x = x * z :=
    fun z hz x hx => (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  have hZ2 : ∀ z ∈ centerOf (pCoreOf 2 L1), z ^ 2 = 1 := by
    intro z hz
    refine hD.isElemAbelian_right.2 z ((c₁.mem_inf_iff ⟨z, hz.1⟩).mpr ?_)
    have h1 : c₁.β ⟨z, hz.1⟩ = 1 := by
      rw [← MonoidHom.mem_ker, c₁.ker_β]
      exact Subgroup.mem_subgroupOf.mpr hz
    rw [h1, toAdd_one]
    rfl
  have hQ2 : ∀ x ∈ pCoreOf 2 L1, x ^ 2 ∈ centerOf (pCoreOf 2 L1) := by
    intro x hx
    rw [pow_two, ← D.range_ζ]
    exact MonoidHom.mem_range.mpr ⟨_, (D.mul_self_eq ⟨x, hx⟩).symm⟩
  have hRZ' : ∀ r ∈ (levHom hU).range ⊔ u4PtTorus hU, ∀ z ∈ zRad hU, r * z * r⁻¹ ∈ zRad hU :=
    fun r hr z hz => conj_mem_zRad_of_mem_normalizer hU r (hR'Q' hr) z hz
  have hfC : ∀ (r : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀))
      (v w : ↥(pCoreOf 2 L1)) (v' w' : ↥(radQ hU)), (w : G) = r * v * (r : G)⁻¹ →
      (w' : hypSU hU 2 0) = e r * v' * (e r : hypSU hU 2 0)⁻¹ →
      c₁.pointPhi φ v = radPhi hU v' → c₁.pointPhi φ w = radPhi hU w' := by
    intro r v w v' w' hw hw' hvv
    obtain ⟨k, hk, h₀, hh, hr⟩ := KProd.exists_mul_of_mem_sup_of_comm hKH r.2
    rw [he r k h₀ hk hh hr] at hw'
    rw [hr] at hw
    exact c₁.pointPhi_conj_eq_radPhi c₂ hH hD hS hT hU ρ hρ hφA κ hκ hk hh v w v' w' hw hw' hvv
  have hsqC : ∀ (u : ↥(pCoreOf 2 L1)) (v' : ↥(radQ hU)), c₁.pointPhi φ u = radPhi hU v' →
      ∀ hz : (u : G) ^ 2 ∈ centerOf (pCoreOf 2 L1),
        ((pointCenterEquiv hU D ρ δ hδ ⟨(u : G) ^ 2, hz⟩ : ↥(zRad hU)) : hypSU hU 2 0) =
          (v' : hypSU hU 2 0) ^ 2 :=
    fun u v' huv hz => c₁.pointCenterEquiv_sq hU D hDβ ρ hφ hρ δ rfl hδ u v' huv hz
  have hgC : ∀ (r : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀))
      (z w : ↥(centerOf (pCoreOf 2 L1))), (w : G) = r * z * (r : G)⁻¹ →
      ((pointCenterEquiv hU D ρ δ hδ w : ↥(zRad hU)) : hypSU hU 2 0) =
        (e r : hypSU hU 2 0) * (pointCenterEquiv hU D ρ δ hδ z : hypSU hU 2 0) *
          (e r : hypSU hU 2 0)⁻¹ := by
    intro r z w hw
    obtain ⟨u, hu⟩ := D.exists_mul_self_eq z.2
    obtain ⟨v', hv'⟩ := radPhi_surjective hU (c₁.pointPhi φ u)
    have hru : (r : G) * u * (r : G)⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (hRQ r.2) u).mp u.2
    have hrv : (e r : hypSU hU 2 0) * v' * (e r : hypSU hU 2 0)⁻¹ ∈ radQ hU :=
      (Subgroup.mem_normalizer_iff.mp (hR'Q' (e r).2) v').mp v'.2
    have h1 := hfC r u ⟨_, hru⟩ v' ⟨_, hrv⟩ rfl rfl hv'.symm
    have hz : (u : G) ^ 2 ∈ centerOf (pCoreOf 2 L1) := by
      rw [pow_two, hu]
      exact z.2
    have hw2 : ((r : G) * u * (r : G)⁻¹) ^ 2 = w := by
      rw [hw, ← hu, pow_two]
      group
    have hz' : ((r : G) * u * (r : G)⁻¹) ^ 2 ∈ centerOf (pCoreOf 2 L1) := by
      rw [hw2]
      exact w.2
    have hzu : (⟨(u : G) ^ 2, hz⟩ : ↥(centerOf (pCoreOf 2 L1))) = z :=
      Subtype.ext (by show (u : G) ^ 2 = z; rw [pow_two, hu])
    have hwu : (⟨((r : G) * u * (r : G)⁻¹) ^ 2, hz'⟩ : ↥(centerOf (pCoreOf 2 L1))) = w :=
      Subtype.ext hw2
    rw [← hzu, ← hwu, hsqC u v' hv'.symm hz, hsqC ⟨_, hru⟩ ⟨_, hrv⟩ h1 hz']
    show ((e r : hypSU hU 2 0) * v' * (e r : hypSU hU 2 0)⁻¹) ^ 2 = _
    simp only [pow_two]
    group
  obtain ⟨θ, ψ₀, hψQ, hψR, hθf, -⟩ := exists_vertexIso_special hRQ
    (hD.disjoint_pCoreOf_torusCompl hH hS hT hf hH₀L) hR'Q' hQR' hZQ hZc hZ2 hQ2
    hT.torusCompl_conj_mem_centerOf (zRad_le_radQ hU) (zRad_comm_radQ hU) (zRad_sq_eq_one hU)
    (sq_mem_zRad_of_mem_radQ hU) hRZ' e (c₁.pointQuotEquiv hU hφ)
    (pointCenterEquiv hU D ρ δ hδ)
    (fun r v w v' w' hw hw' hvv => (c₁.pointQuotEquiv_mk_eq_mk_iff hU hφ w w').mpr
      (hfC r v w v' w' hw hw' ((c₁.pointQuotEquiv_mk_eq_mk_iff hU hφ v v').mp hvv)))
    hgC (fun v v' hvv hz => hsqC v v' ((c₁.pointQuotEquiv_mk_eq_mk_iff hU hφ v v').mp hvv) hz)
    (c₁.crossedHomPrincipal_point c₂ hH hD hS hT hU hφ hφA κ hκ e he₀)
  have hθφ : ∀ v : ↥(pCoreOf 2 L1), c₁.pointPhi φ v = radPhi hU (θ v) := fun v =>
    (c₁.pointQuotEquiv_mk_eq_mk_iff hU hφ v (θ v)).mp (hθf v)
  let ψ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(parP hU) :=
    (MulEquiv.subgroupCongr hP.symm).trans (ψ₀.trans (MulEquiv.subgroupCongr hP'))
  have hψmul : ∀ (x : ↥(L1 ⊔ bigB L1 L2 S)) (q : ↥(pCoreOf 2 L1))
      (r : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀)), (x : G) = q * r →
      ((ψ x : ↥(parP hU)) : hypSU hU 2 0) = (θ q : hypSU hU 2 0) * (e r : hypSU hU 2 0) := by
    intro x q r hx
    have hx' : MulEquiv.subgroupCongr hP.symm x =
        ⟨q, Subgroup.mem_sup_left q.2⟩ * ⟨r, Subgroup.mem_sup_right r.2⟩ := Subtype.ext hx
    show ((ψ₀ (MulEquiv.subgroupCongr hP.symm x) : ↥(radQ hU ⊔ _)) : hypSU hU 2 0) = _
    rw [hx', map_mul, Subgroup.coe_mul, hψQ, hψR]
  have hdecomp : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), ∃ (q : ↥(pCoreOf 2 L1))
      (r : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀)), (x : G) = q * r := by
    intro x
    have hx : (x : G) ∈ ((pCoreOf 2 L1 ⊔ (L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊔ H₀) :
        Subgroup G) : Set G) := by
      rw [hP]
      exact x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRQ] at hx
    obtain ⟨q, hq, r, hr, hqr⟩ := Set.mem_mul.mp hx
    exact ⟨⟨q, hq⟩, ⟨r, hr⟩, hqr.symm⟩
  have hd1 : ∀ (h₀ : G) (hh : h₀ ∈ H₀),
      ((u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩) : hypSU hU 2 0) = 1 ↔ h₀ = 1 := by
    intro h₀ hh
    rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  have hSdec : ∀ (q k h₀ : G), q ∈ pCoreOf 2 L1 → k ∈ L1 → h₀ ∈ H₀ → q * (k * h₀) ∈ S →
      h₀ = 1 ∧ k ∈ S := by
    intro q k h₀ hq hk hh hx
    have hkh : k * h₀ ∈ S := (mul_mem_cancel_left (hH.pCoreOf_le_left hq)).mp hx
    have hh1 : h₀ = 1 := by
      have hL : h₀ ∈ L1 := by
        have e := L1.mul_mem (L1.inv_mem hk) (hSL1 hkh)
        rwa [inv_mul_cancel_left] at e
      have hm : h₀ ∈ H₀ ⊓ L1 := ⟨hh, hL⟩
      rwa [hH₀L, Subgroup.mem_bot] at hm
    subst hh1
    exact ⟨rfl, by rwa [mul_one] at hkh⟩
  have hunit : ∀ (k : G) (hk : k ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G)),
      (∃ t, ((Matrix.SpecialLinearGroup.map ρ.toRingHom (c₁.α ⟨k, hk.1⟩) :
        SL(2, hU.fixedField)) : Matrix (Fin 2) (Fin 2) hU.fixedField) = !![1, t; 0, 1]) ↔
        k ∈ S := by
    intro k hk
    rw [exists_unitri_map_iff_ptv ρ, ← c₁.mem_iff ⟨k, hk.1⟩]
  have hSU : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ x : ↥(parP hU)) : hypSU hU 2 0) ∈ hypUnitriangular hU 2 0 := by
    intro x
    obtain ⟨q, r, hx⟩ := hdecomp x
    obtain ⟨k, hk, h₀, hh, hr⟩ := KProd.exists_mul_of_mem_sup_of_comm hKH r.2
    rw [hψmul x q r hx, he r k h₀ hk hh hr,
      mul_mem_cancel_left (radQ_le_hypUnitriangular_u4 hU (θ q).2),
      levHom_mul_mem_hypUnitriangular_iff hU _ ((u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩)).2,
      hd1, hunit k hk, hx, hr]
    constructor
    · exact fun hS' => hSdec q k h₀ q.2 hk.1 hh hS'
    · rintro ⟨rfl, hkS⟩
      rw [mul_one]
      exact mul_mem (hH.pCoreOf_le_left q.2) hkS
  have hQ2iff : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L2 ↔
      ((ψ x : ↥(parP hU)) : hypSU hU 2 0) ∈ radQ2 hU := by
    intro x
    obtain ⟨q, r, hx⟩ := hdecomp x
    obtain ⟨k, hk, h₀, hh, hr⟩ := KProd.exists_mul_of_mem_sup_of_comm hKH r.2
    have hψx := hψmul x q r hx
    rw [he r k h₀ hk hh hr] at hψx
    rw [hr] at hx
    have hθ := mem_radQ2_iff_of_pointPhi_ptv c₁ hU hφ.1 q (θ q) (hθφ q)
    have hkey : (x : G) ∈ S → h₀ = 1 ∧ k ∈ pCoreOf 2 L2 ∧
        levHom hU (Matrix.SpecialLinearGroup.map ρ.toRingHom (c₁.α ⟨k, hk.1⟩)) *
          ((u4PtKappaEquiv hU).symm (κ ⟨h₀, hh⟩) : hypSU hU 2 0) ∈ radQ2 hU := by
      intro hxS
      rw [hx] at hxS
      obtain ⟨hh1, hkS⟩ := hSdec q k h₀ q.2 hk.1 hh hxS
      refine ⟨hh1, hD.inf_inf_centralizer_torus_le hH hS hT ⟨hkS, hk⟩, ?_⟩
      rw [(hd1 h₀ hh).mpr hh1, mul_one]
      obtain ⟨t, ht⟩ := (hunit k hk).mpr hkS
      exact levHom_mem_radQ2_of_eq hU ht
    constructor
    · intro hx2
      obtain ⟨rfl, hkQ, hlev⟩ := hkey (hH.pCoreOf_le_right hx2)
      have hqQ : (q : G) ∈ pCoreOf 2 L2 := by
        have e := mul_mem hx2 (inv_mem hkQ)
        rwa [hx, mul_one, mul_inv_cancel_right] at e
      rw [hψx]
      exact mul_mem (hθ.mpr hqQ) hlev
    · intro hψ2
      obtain ⟨rfl, hkQ, hlev⟩ :=
        hkey ((hSU x).mpr (radQ2_le_hypUnitriangular_ptv hU hψ2))
      have hθq : (θ q : hypSU hU 2 0) ∈ radQ2 hU := by
        have e := mul_mem hψ2 (inv_mem hlev)
        rwa [hψx, mul_inv_cancel_right] at e
      rw [hx, mul_one]
      exact mul_mem (hθ.mp hθq) hkQ
  exact ⟨ψ, hQ2iff, fun x => mem_normalizer_iff_of_mulEquiv ψ (hSL1.trans le_sup_left)
    ((hypUnitriangular_le_inf_u4 hU).trans inf_le_left) hSU x⟩

theorem isAmalgamOfGroup_psu4_of_u4qLocalData_of_card (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f) := by
  obtain ⟨F, hF, -, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  obtain ⟨K, hK, -, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hF
  letI := hK
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, c₂.card⟩
  obtain ⟨ψ₁, hψ₁Q, hψ₁N⟩ := hD.exists_mulEquiv_parP hf hH hS c₁ c₂ hU
  obtain ⟨ψ₂, hψ₂Q, -, hψ₂N⟩ := hD.exists_mulEquiv_parP2 hH hS c₁ c₂ hU
  exact isAmalgamOfGroup_psu4_of_mulEquiv hf hH hD hS hU ψ₁ hψ₁Q hψ₁N ψ₂ hψ₂Q hψ₂N

end CFSG.Quasithin.F112R.St84

end
