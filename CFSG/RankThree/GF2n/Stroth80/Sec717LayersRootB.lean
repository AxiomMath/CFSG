module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayersRoot
import CFSG.RankThree.GF2n.Stroth80.Sec78VtIrred
import CFSG.LargeExtraspecial.DWFldOrth
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSixSimple

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.sec717_even_finrank_map_opm (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (hM : GlobalModelData M Q Z γ M₀)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      Even (Module.finrank K ↥(T.map (opm (φ r)))) := by
  classical
  intro r hr
  obtain ⟨K', fK', finK', hKK, e, -, he⟩ :=
    hc.sec717_exists_transport hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ T hT
  obtain ⟨A, hA, hAe⟩ := he r hr
  haveI : CharP K' 2 := by
    obtain ⟨k, -, hk, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow ((hKK.trans hM.card).trans hk)
  set g := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K' A with hg
  have hev : Even (Module.finrank K' ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g)) := by
    have hmem : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadPlus 3 K'),
        TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 3 K')⁆ := by
      have h := hA
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
        (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K'), Subgroup.mem_comap] at h
      exact h
    exact (CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 3 K') hmem).2
  have hgv : ∀ v, (g v : Fin 3 ⊕ Fin 3 → K') = (A : Matrix _ _ K') *ᵥ v := fun v => rfl
  have hmap : ∀ v, ((e (g v - v) : ↥T) : M₀.E) = opm (φ r) (e v) := fun v => by
    rw [map_sub, Submodule.coe_sub, hgv, hAe, opm_apply]
  have hcard : Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g) =
      Nat.card ↥(T.map (opm (φ r))) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun u => ⟨((e u.1 : ↥T) : M₀.E), ?_⟩) ⟨fun u₁ u₂ h => ?_, fun y => ?_⟩)
    · obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp u.2
      rw [← hv, hmap]
      exact Submodule.mem_map_of_mem (e v).2
    · have h' : ((e u₁.1 : ↥T) : M₀.E) = ((e u₂.1 : ↥T) : M₀.E) :=
        congrArg (fun y : ↥(T.map (opm (φ r))) => (y : M₀.E)) h
      exact Subtype.ext (e.injective (Subtype.ext h'))
    · obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2
      set v := e.symm ⟨x, hx⟩ with hv
      have hev' : ((e v : ↥T) : M₀.E) = x := by rw [hv, AddEquiv.apply_symm_apply]
      refine ⟨⟨g v - v, CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨v, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      show ((e (g v - v) : ↥T) : M₀.E) = (y : M₀.E)
      rw [hmap, hev', hxy]
  have hq : 2 ≤ Nat.card K := by
    haveI : Nontrivial K := inferInstance
    exact Finite.one_lt_card
  rw [Module.natCard_eq_pow_finrank (K := K')
      (V := ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g)),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(T.map (opm (φ r)))), hKK] at hcard
  have hfin : Module.finrank K' ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g) =
      Module.finrank K ↥(T.map (opm (φ r))) := Nat.pow_right_injective hq hcard
  rw [← hfin]
  exact hev

theorem Ctx.sec717_T_irred (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∀ U : Submodule K M₀.E, U ≤ T →
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ U,
        φ r w ∈ U) → U = ⊥ ∨ U = T := by
  intro U hUT hU
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZVt : Z ≤ Vt M (LB M Q B) B Z t := le_sup_left
  have hTset := hc.sec717_T_eq_image hZcard hZc hZV hs hZ0 M₀ φ hφπ T hT
  have hπ1 : M₀.π 1 = 0 := (M₀.π_ker 1 Q.one_mem).mpr Z.one_mem
  have hπinv : ∀ v ∈ Q, M₀.π v⁻¹ = -M₀.π v := fun v hv => by
    have h := M₀.π_mul v hv v⁻¹ (Q.inv_mem hv)
    rw [mul_inv_cancel, hπ1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  let Ut' : Subgroup G :=
    { carrier := {v | v ∈ Vt M (LB M Q B) B Z t ∧ M₀.π v ∈ U}
      one_mem' := ⟨Subgroup.one_mem _, by rw [hπ1]; exact U.zero_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        rw [M₀.π_mul _ (hVtQ ha.1) _ (hVtQ hb.1)]
        exact U.add_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
        rw [hπinv a (hVtQ ha.1)]
        exact U.neg_mem ha.2⟩ }
  have hZU : Z ≤ Ut' := fun z hz =>
    (show z ∈ Vt M (LB M Q B) B Z t ∧ M₀.π z ∈ U from
      ⟨hZVt hz, by rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact U.zero_mem⟩)
  have hUV : Ut' ≤ Vt M (LB M Q B) B Z t := fun v hv =>
    (show v ∈ Vt M (LB M Q B) B Z t ∧ M₀.π v ∈ U from hv).1
  have hRU : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ Ut', r * u * r⁻¹ ∈ Ut' := by
    intro r hr u hu
    replace hu : u ∈ Vt M (LB M Q B) B Z t ∧ M₀.π u ∈ U := hu
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have hrH : QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr (hc.Rt_le_H0 t hr)
    refine (show r * u * r⁻¹ ∈ Vt M (LB M Q B) B Z t ∧ M₀.π (r * u * r⁻¹) ∈ U from ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) u).mp hu.1
    have h := hφπ ⟨r, hrM⟩ hrH u (hVtQ hu.1)
    rw [show ((⟨r, hrM⟩ : ↥M) : G) = r from rfl] at h
    rw [h]
    exact hU _ (Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr hr)) _ hu.2
  rcases sec7VtIrred_holds G M Q Z B hc n t hs Ut' hZU hUV hRU with h | h
  · left
    refine (Submodule.eq_bot_iff U).mpr fun w hw => ?_
    have hw' : w ∈ (T : Set M₀.E) := hUT hw
    rw [hTset] at hw'
    obtain ⟨v, hv, rfl⟩ := hw'
    have hvU : v ∈ Ut' := (show v ∈ Vt M (LB M Q B) B Z t ∧ M₀.π v ∈ U from ⟨hv, hw⟩)
    rw [h] at hvU
    exact (M₀.π_ker v (hVtQ hv)).mpr hvU
  · right
    refine le_antisymm hUT fun w hw => ?_
    have hw' : w ∈ (T : Set M₀.E) := hw
    rw [hTset] at hw'
    obtain ⟨v, hv, rfl⟩ := hw'
    have hvU : v ∈ Ut' := by rw [h]; exact hv
    exact (show v ∈ Vt M (LB M Q B) B Z t ∧ M₀.π v ∈ U from hvU).2

theorem Ctx.sec717_RN_simple (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) :
    ∀ S : Subgroup ↥(bar M Q (H0 M Z)),
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤ S →
      S ≤ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) →
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), ∀ s ∈ S,
        r * s * r⁻¹ ∈ S) →
      S = (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ∨
        S = (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) := by
  classical
  intro S hNS hSR hSn
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  obtain ⟨K', fK', finK', hK'Z, ρ, hρ, hρker, -⟩ := hp3
  haveI : CharP K' 2 := by
    obtain ⟨k, -, hk, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK'Z.trans hk)
  haveI := sec7_isSimpleGroup_omegaPlusSix (K := K') (hK'Z ▸ hc.hyp.q4)
  let π' : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (H0 M Z)) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (Q.subgroupOf M)).comp
      (Subgroup.inclusion (hc.Rt_le_M t))) (bar M Q (H0 M Z)) fun x =>
        (mk_mem_bar_iff_sec4 hQH _).mpr (hc.Rt_le_H0 t x.2)
  have hπ'R : ∀ x, π' x ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) :=
    fun x => Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr x.2)
  have hπ'N : ∀ x, π' x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ↔
      (x : G) ∈ hc.CN t := fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact mk_mem_bar_iff_sec4 hQN _
  have hlift : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∃ x, π' x = r := by
    intro r hr
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (r : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hr)
    exact ⟨⟨(y : G), hyR⟩, Subtype.ext hy⟩
  have hker : ∀ x, ρ x = 1 ↔ (x : G) ∈ hc.CN t := fun x => by
    rw [← MonoidHom.mem_ker, hρker, Subgroup.mem_subgroupOf]
  let ρ' : ↥(Rt M (LB M Q B) t) →* ↥(StatedOmega (StatedQuadPlus 3 K')) :=
    ρ.codRestrict _ fun x => by rw [← hρ]; exact ⟨x, rfl⟩
  have hρ'surj : Function.Surjective ρ' := by
    rintro ⟨A, hA⟩
    rw [← hρ] at hA
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, Subtype.ext hx⟩
  have hρ'ker : ∀ x, ρ' x = 1 ↔ (x : G) ∈ hc.CN t := fun x => by
    rw [← hker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hnorm : ((S.comap π').map ρ').Normal := by
    refine ⟨fun a ha b => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, rfl⟩ := hρ'surj b
    refine Subgroup.mem_map.mpr ⟨y * x * y⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hSn _ (hπ'R y) _ hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S.comap π').map ρ') with h | h
  · left
    refine le_antisymm (fun s hs' => ?_) hNS
    obtain ⟨x, rfl⟩ := hlift s (hSR hs')
    have hx : ρ' x ∈ (S.comap π').map ρ' :=
      Subgroup.mem_map_of_mem ρ' (show x ∈ S.comap π' from hs')
    rw [h, Subgroup.mem_bot] at hx
    exact (hπ'N x).mpr ((hρ'ker x).mp hx)
  · right
    refine le_antisymm hSR fun r hr => ?_
    obtain ⟨x, rfl⟩ := hlift r hr
    have hx : ρ' x ∈ (S.comap π').map ρ' := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : ρ' (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hN : π' (y⁻¹ * x) ∈ S := hNS ((hπ'N _).mpr ((hρ'ker _).mp hyx'))
    have e : x = y * (y⁻¹ * x) := by group
    rw [e, map_mul]
    exact S.mul_mem hy hN

end CFSG.RankThree.GF2n.Stroth80
