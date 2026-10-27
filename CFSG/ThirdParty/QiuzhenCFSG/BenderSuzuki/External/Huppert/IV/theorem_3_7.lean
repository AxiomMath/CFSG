module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_2.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.3.7

Book-order entry file for Grun's second theorem.

The source theorem states the quotient comparison
`G/G'(p) ~= N_G(Z(P))/N_G(Z(P))'(p)`.  The downstream normal-complement
consequence exported from `Core` remains:
* `hkt_grun_second_hasNormalPComplement_of_center_normalizer`
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u

/-- Huppert IV.3.7, denominator comparison after the two applications of
IV.3.3.

Book proof sentence: by IV.3.4,
`P ∩ G' = P ∩ N_G(Z(P))'`; hence the two Sylow quotients obtained from
IV.3.3 have the same denominator.  This is the only genuine source
calculation in IV.3.7. -/
private theorem huppert_IV_3_7_sylow_quotient_equiv_center_normalizer_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    let ZN : Subgroup Q :=
      Subgroup.normalizer
        ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
    let hS_le_ZN : (S : Subgroup Q) ≤ ZN := by
      simpa [ZN] using
        hkt_huppert_iv52_sylow_le_normalizer_centerIn (Q := Q) (q := q) S
    let SN : Sylow q ZN := S.subtype hS_le_ZN
    let KQ : Subgroup (S : Subgroup Q) :=
      huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
    let KZN : Subgroup (SN : Subgroup ZN) :=
      huppertIV33SylowDerivedSubgroup (Q := ZN) (q := q) SN
    letI : KQ.Normal := inferInstance
    letI : KZN.Normal := inferInstance
    Nonempty (((S : Subgroup Q) ⧸ KQ) ≃*
      ((SN : Subgroup ZN) ⧸ KZN)) := by
  classical
  -- Sentence 3 of Huppert IV.3.7: IV.3.4 identifies the two denominators
  -- `P ∩ Q'` and `P ∩ N_Q(Z(P))'` after `q`-normality controls the
  -- conjugate `P'` terms.  The rest is the quotient congruence induced by the
  -- tautological identification of `S` with its copy inside `ZN`.
  let ZN : Subgroup Q :=
    Subgroup.normalizer
      ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
  let hS_le_ZN : (S : Subgroup Q) ≤ ZN := by
    simpa [ZN] using
      hkt_huppert_iv52_sylow_le_normalizer_centerIn (Q := Q) (q := q) S
  let SN : Sylow q ZN := S.subtype hS_le_ZN
  let KQ : Subgroup (S : Subgroup Q) :=
    huppertIV33SylowDerivedSubgroup (Q := Q) (q := q) S
  let KZN : Subgroup (SN : Subgroup ZN) :=
    huppertIV33SylowDerivedSubgroup (Q := ZN) (q := q) SN
  have hSN_coe : (SN : Subgroup ZN) = (S : Subgroup Q).subgroupOf ZN := by
    exact Sylow.coe_subtype (P := S) (N := ZN) hS_le_ZN
  let eSN_S : (SN : Subgroup ZN) ≃* (S : Subgroup Q) :=
    (MulEquiv.subgroupCongr hSN_coe).trans
      (Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup Q)) (K := ZN) hS_le_ZN)
  have hden_eq : KZN.map eSN_S.toMonoidHom = KQ := by
    -- This is exactly the source calculation `S ∩ Q' = S ∩ N_Q(Z(S))'`.
    -- We keep it in this proof block and prove it from IV.3.4 below.
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyKZN, hyx⟩
      have hy_comm_ZN : ((y : (SN : Subgroup ZN)) : ZN) ∈ commutator ZN := by
        simpa [KZN, huppertIV33SylowDerivedSubgroup] using Subgroup.mem_subgroupOf.mp hyKZN
      have hy_comm_Q : (((y : (SN : Subgroup ZN)) : ZN) : Q) ∈ commutator Q := by
        have hmap : (commutator ZN).map ZN.subtype ≤ commutator Q := by
          rw [Subgroup.map_subtype_commutator]
          exact Subgroup.commutator_mono le_top le_top
        exact hmap ⟨((y : (SN : Subgroup ZN)) : ZN), hy_comm_ZN, rfl⟩
      have hx_val : (x : Q) = (((y : (SN : Subgroup ZN)) : ZN) : Q) := by
        exact congrArg Subtype.val hyx.symm
      change (x : Q) ∈ commutator Q
      simpa [hx_val]
    · intro hxKQ
      -- Huppert IV.3.4 in `Q` and in `ZN`, plus `q`-normality, give the
      -- reverse containment of the denominators.
      have hxQ : (x : Q) ∈ (S : Subgroup Q) ⊓ commutator Q := by
        exact ⟨x.property, by simpa [KQ, huppertIV33SylowDerivedSubgroup] using Subgroup.mem_subgroupOf.mp hxKQ⟩
      have hxZNcomm : (⟨(x : Q), hS_le_ZN x.property⟩ : ZN) ∈ commutator ZN := by
        -- Source sentence: by IV.3.4, it is enough to check the two families
        -- generating `S ∩ Q'`.  The `N_Q(S)'` family lies in `ZN'` because
        -- `N_Q(S) ≤ N_Q(Z(S))`.  For the `(S')^g` family we follow Huppert:
        -- set `T = S ∩ (S')^g`, conjugate the two Sylow subgroups of
        -- `N_Q(T)` containing `Z(S)` and `Z(S)^g`, then use `q`-normality to
        -- get `g*s ∈ N_Q(Z(S))`.
        let DQ : Subgroup Q := huppertIV34GrunKernelSubgroup (Q := Q) (S : Subgroup Q)
        let imageZNcomm : Subgroup Q := (commutator ZN).map ZN.subtype
        have hxDQ : (x : Q) ∈ DQ := by
          have h34 := huppert_IV_3_4_first_grun (Q := Q) (q := q) S
          have h34eq :
              (S : Subgroup Q) ⊓ commutator Q =
                huppertIV34GrunKernelSubgroup (Q := Q) (S : Subgroup Q) := by
            simpa using h34
          have hxinf : (x : Q) ∈ (S : Subgroup Q) ⊓ commutator Q := hxQ
          simpa [DQ] using h34eq ▸ hxinf
        have hDQ_le_image : DQ ≤ imageZNcomm := by
          -- Huppert IV.3.7, denominator paragraph after applying IV.3.4.
          -- We keep the whole book argument local: first the `N_Q(S)'` family,
          -- then the family `S ∩ (S')^g` controlled by the Sylow-center
          -- conjugacy argument inside `N_Q(T)`.
          let NS : Subgroup Q :=
            Subgroup.normalizer (((S : Subgroup Q) : Subgroup Q) : Set Q)
          let Pder : Subgroup Q :=
            (commutator (S : Subgroup Q)).map (S : Subgroup Q).subtype
          have hnormalizer_family :
              ∀ {y : Q}, y ∈ (S : Subgroup Q) →
                y ∈ (commutator NS).map NS.subtype → y ∈ imageZNcomm := by
            intro y hyS hyComm
            -- Since `N_Q(S) ≤ N_Q(Z(S))`, commutators from `N_Q(S)` map into
            -- the commutator subgroup of `N_Q(Z(S))`.
            have hNS_le_ZN : NS ≤ ZN := by
              simpa [NS, ZN, centerIn_eq_map_center_local] using
                hkt_normalizer_le_normalizer_map_subtype_of_characteristic
                  (Q := Q) (H := (S : Subgroup Q))
                  (K := Subgroup.center (S : Subgroup Q))
            change y ∈ (commutator ZN).map ZN.subtype
            rw [Subgroup.mem_map] at hyComm ⊢
            rcases hyComm with ⟨c, hc, rfl⟩
            let iNS_ZN : NS →* ZN :=
              { toFun := fun n => ⟨(n : Q), hNS_le_ZN n.property⟩
                map_one' := by ext; rfl
                map_mul' := by intro a b; ext; rfl }
            refine ⟨iNS_ZN c, ?_, rfl⟩
            have hmapc : (commutator NS).map iNS_ZN ≤ commutator ZN := by
              rw [_root_.commutator_def, Subgroup.map_commutator]
              exact Subgroup.commutator_mono le_top le_top
            exact hmapc ⟨c, hc, rfl⟩
          have hconjugate_family :
              ∀ {y : Q},
                (∃ g : Q, y ∈ (S : Subgroup Q) ∧ y ∈ rightConjugate Pder g) →
                  y ∈ imageZNcomm := by
            intro y hyCg
            rcases hyCg with ⟨g, hyS, hyPg⟩
            -- This is Huppert IV.3.7's nontrivial paragraph for
            -- `T = S ∩ (S')^g`.
            let T : Subgroup Q := (S : Subgroup Q) ⊓ rightConjugate Pder g
            have hyT : y ∈ T := by
              exact ⟨hyS, by simpa [Pder] using hyPg⟩
            let NT : Subgroup Q := Subgroup.normalizer ((T : Subgroup Q) : Set Q)
            have hZS_le_NT : centerIn (G := Q) (S : Subgroup Q) ≤ NT := by
              intro z hz
              rw [Subgroup.mem_normalizer_iff]
              intro t
              constructor
              · intro ht
                have hcomm : t * z = z * t :=
                  (Subgroup.mem_centralizer_iff.mp hz.2) t ht.1
                have hconj_eq : z * t * z⁻¹ = t := by
                  calc
                    z * t * z⁻¹ = t * z * z⁻¹ := by rw [← hcomm]
                    _ = t := by simp [mul_assoc]
                simpa [hconj_eq] using ht
              · intro ht
                have htS : t ∈ (S : Subgroup Q) := by
                  have hzS : z ∈ (S : Subgroup Q) := hz.1
                  have hztS : z * t * z⁻¹ ∈ (S : Subgroup Q) := ht.1
                  have htmp : z⁻¹ * (z * t * z⁻¹) * z ∈ (S : Subgroup Q) :=
                    (S : Subgroup Q).mul_mem
                      ((S : Subgroup Q).mul_mem ((S : Subgroup Q).inv_mem hzS) hztS) hzS
                  simpa [mul_assoc] using htmp
                have hcomm : t * z = z * t :=
                  (Subgroup.mem_centralizer_iff.mp hz.2) t htS
                have hconj_eq : z * t * z⁻¹ = t := by
                  calc
                    z * t * z⁻¹ = t * z * z⁻¹ := by rw [← hcomm]
                    _ = t := by simp [mul_assoc]
                simpa [hconj_eq] using ht
            have hZg_le_NT : rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g ≤ NT := by
              have hPder_le_S : Pder ≤ (S : Subgroup Q) := by
                intro a ha
                rcases Subgroup.mem_map.mp ha with ⟨aS, _haS, rfl⟩
                exact aS.property
              have hZg_comm :
                  ∀ {z t : Q},
                    z ∈ rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g →
                    t ∈ rightConjugate Pder g → t * z = z * t := by
                intro z t hz ht
                rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hz ht
                rcases hz with ⟨z0, hz0, rfl⟩
                rcases ht with ⟨t0, ht0, rfl⟩
                have ht0S : t0 ∈ (S : Subgroup Q) := hPder_le_S ht0
                have hcomm0 : t0 * z0 = z0 * t0 :=
                  (Subgroup.mem_centralizer_iff.mp hz0.2) t0 ht0S
                have hcomm_map := congrArg (fun a : Q => (MulAut.conj g⁻¹) a) hcomm0
                simpa [map_mul] using hcomm_map
              intro z hz
              rw [Subgroup.mem_normalizer_iff]
              intro t
              constructor
              · intro ht
                have hcomm : t * z = z * t := hZg_comm hz ht.2
                have hconj_eq : z * t * z⁻¹ = t := by
                  calc
                    z * t * z⁻¹ = t * z * z⁻¹ := by rw [← hcomm]
                    _ = t := by simp [mul_assoc]
                simpa [hconj_eq] using ht
              · intro ht
                let a : Q := z * t * z⁻¹
                have haT : a ∈ T := by simpa [a] using ht
                have hcomm : a * z = z * a := hZg_comm hz haT.2
                have ht_eq : t = a := by
                  calc
                    t = z⁻¹ * a * z := by simp [a, mul_assoc]
                    _ = z⁻¹ * (a * z) := by simp [mul_assoc]
                    _ = z⁻¹ * (z * a) := by rw [hcomm]
                    _ = a := by simp
                simpa [ht_eq] using haT
            have hZp_NT :
                IsPGroup q ((centerIn (G := Q) (S : Subgroup Q)).subgroupOf NT) := by
              have hZp : IsPGroup q (centerIn (G := Q) (S : Subgroup Q)) :=
                IsPGroup.to_le S.isPGroup'
                  (show centerIn (G := Q) (S : Subgroup Q) ≤ (S : Subgroup Q) from inf_le_left)
              exact hZp.of_equiv
                (Subgroup.subgroupOfEquivOfLe
                  (H := centerIn (G := Q) (S : Subgroup Q)) (K := NT) hZS_le_NT).symm
            obtain ⟨P1, hZ_le_P1⟩ :=
              IsPGroup.exists_le_sylow (G := NT) (p := q) hZp_NT
            have hZg_p_NT :
                IsPGroup q
                  ((rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g).subgroupOf NT) := by
              have hZp : IsPGroup q (centerIn (G := Q) (S : Subgroup Q)) :=
                IsPGroup.to_le S.isPGroup'
                  (show centerIn (G := Q) (S : Subgroup Q) ≤ (S : Subgroup Q) from inf_le_left)
              have hZg_p : IsPGroup q (rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g) := by
                have hmap : IsPGroup q ((centerIn (G := Q) (S : Subgroup Q)).map
                    (MulAut.conj g⁻¹).toMonoidHom) :=
                  IsPGroup.map (p := q) (H := centerIn (G := Q) (S : Subgroup Q))
                    hZp (MulAut.conj g⁻¹).toMonoidHom
                have h_eq : rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g =
                    (centerIn (G := Q) (S : Subgroup Q)).map (MulAut.conj g⁻¹).toMonoidHom := by
                  simp [rightConjugate, Subgroup.conjBy]
                rw [h_eq]
                exact hmap
              exact hZg_p.of_equiv
                (Subgroup.subgroupOfEquivOfLe
                  (H := rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g)
                  (K := NT) hZg_le_NT).symm
            obtain ⟨P2, hZg_le_P2⟩ :=
              IsPGroup.exists_le_sylow (G := NT) (p := q) hZg_p_NT
            obtain ⟨sN, hsN⟩ := MulAction.exists_smul_eq NT P2 P1
            let s : Q := (sN : Q)⁻¹
            have hs_mem_NT : s ∈ NT := NT.inv_mem sN.property
            obtain ⟨Pstar, hPstar_comap⟩ := Sylow.exists_comap_subtype_eq (P := P1)
            have hZS_le_Pstar :
                centerIn (G := Q) (S : Subgroup Q) ≤ (Pstar : Subgroup Q) := by
              intro z hz
              let zN : NT := ⟨z, hZS_le_NT hz⟩
              have hzP1 : zN ∈ (P1 : Subgroup NT) := by
                exact hZ_le_P1 (by simpa [Subgroup.mem_subgroupOf, zN] using hz)
              have hzComap : zN ∈ (Pstar : Subgroup Q).subgroupOf NT := by
                have hsub_eq : (Pstar : Subgroup Q).subgroupOf NT = (P1 : Subgroup NT) := hPstar_comap
                rw [hsub_eq]
                exact hzP1
              simpa [zN] using Subgroup.mem_subgroupOf.mp hzComap
            have hZgs_le_Pstar :
                rightConjugate (centerIn (G := Q) (S : Subgroup Q)) (g * s) ≤
                  (Pstar : Subgroup Q) := by
              intro z hz
              rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hz
              rcases hz with ⟨z0, hz0, rfl⟩
              let zg : Q := (MulAut.conj g⁻¹) z0
              have hzg_Zg : zg ∈ rightConjugate (centerIn (G := Q) (S : Subgroup Q)) g := by
                rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
                exact ⟨z0, hz0, rfl⟩
              have hzg_NT : zg ∈ NT := hZg_le_NT hzg_Zg
              let zgN : NT := ⟨zg, hzg_NT⟩
              have hzg_P2 : zgN ∈ (P2 : Subgroup NT) := by
                exact hZg_le_P2 (by simpa [Subgroup.mem_subgroupOf, zgN, zg] using hzg_Zg)
              have hconj_P1 : (MulAut.conj sN) zgN ∈ (P1 : Subgroup NT) := by
                rw [← hsN, Sylow.coe_subgroup_smul]
                exact Subgroup.smul_mem_pointwise_smul zgN (MulAut.conj sN) (P2 : Subgroup NT) hzg_P2
              have hconj_comap : (MulAut.conj sN) zgN ∈ (Pstar : Subgroup Q).subgroupOf NT := by
                have hsub_eq : (Pstar : Subgroup Q).subgroupOf NT = (P1 : Subgroup NT) := hPstar_comap
                rw [hsub_eq]
                exact hconj_P1
              have hconj_Q : (((MulAut.conj sN) zgN : NT) : Q) ∈ (Pstar : Subgroup Q) := by
                simpa using Subgroup.mem_subgroupOf.mp hconj_comap
              have hval_eq :
                  (MulAut.conj sN : NT ≃* NT) zgN =
                    ⟨((sN : Q) * (g⁻¹ * (z0 * (g * (sN : Q)⁻¹)))), by
                      simpa [zgN, zg, MulAut.conj_apply, mul_assoc] using
                        (((MulAut.conj sN : NT ≃* NT) zgN).property)⟩ := by
                ext
                simp [zgN, zg, MulAut.conj_apply, mul_assoc]
              have htarget_eq :
                  ((sN : Q) * (g⁻¹ * (z0 * (g * (sN : Q)⁻¹)))) =
                    (((MulAut.conj sN : NT ≃* NT) zgN : NT) : Q) := by
                exact congrArg Subtype.val hval_eq.symm
              simpa [s, MulAut.conj_apply, mul_assoc, htarget_eq] using hconj_Q
            have hcenter_Pstar :
                centerIn (G := Q) (S : Subgroup Q) =
                  centerIn (G := Q) (Pstar : Subgroup Q) :=
              hpnormal Pstar hZS_le_Pstar
            have hcenter_gs :
                centerIn (G := Q) (S : Subgroup Q) =
                  rightConjugate (centerIn (G := Q) (S : Subgroup Q)) (g * s) := by
              -- Since both `Z(S)` and `Z(S)^(g s)` lie in the same Sylow
              -- subgroup `Pstar`, `q`-normality identifies the two centers.
              let a : Q := g * s
              let Pstar_a : Sylow q Q := (MulAut.conj a) • Pstar
              have hZS_le_Pstar_a :
                  centerIn (G := Q) (S : Subgroup Q) ≤ (Pstar_a : Subgroup Q) := by
                intro z hz
                have hz_conj :
                    (MulAut.conj a⁻¹) z ∈
                      rightConjugate (centerIn (G := Q) (S : Subgroup Q)) a := by
                  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
                  exact ⟨z, hz, rfl⟩
                have hzP : (MulAut.conj a⁻¹) z ∈ (Pstar : Subgroup Q) :=
                  hZgs_le_Pstar (by simpa [a] using hz_conj)
                have hzImage :
                    (MulAut.conj a) ((MulAut.conj a⁻¹) z) ∈
                      ((MulAut.conj a) • (Pstar : Subgroup Q) : Subgroup Q) :=
                  Subgroup.smul_mem_pointwise_smul
                    ((MulAut.conj a⁻¹) z) (MulAut.conj a) (Pstar : Subgroup Q) hzP
                have hcomp : (MulAut.conj a) ((MulAut.conj a⁻¹) z) = z := by
                  simp [a, MulAut.conj_apply, mul_assoc]
                rw [hcomp] at hzImage
                simpa [Pstar_a, Sylow.pointwise_smul_def] using hzImage
              have hcenter_Pstar_a :
                  centerIn (G := Q) (S : Subgroup Q) =
                    centerIn (G := Q) (Pstar_a : Subgroup Q) :=
                hpnormal Pstar_a hZS_le_Pstar_a
              have hmap_center_Pstar :
                  (centerIn (G := Q) (Pstar : Subgroup Q)).map
                      (MulAut.conj a).toMonoidHom =
                    centerIn (G := Q) (Pstar_a : Subgroup Q) := by
                rw [centerIn_map_mulEquiv (MulAut.conj a) (Pstar : Subgroup Q)]
                rfl
              have hmap_ZS_a :
                  (centerIn (G := Q) (S : Subgroup Q)).map
                      (MulAut.conj a).toMonoidHom =
                    centerIn (G := Q) (S : Subgroup Q) := by
                calc
                  (centerIn (G := Q) (S : Subgroup Q)).map
                      (MulAut.conj a).toMonoidHom =
                      (centerIn (G := Q) (Pstar : Subgroup Q)).map
                        (MulAut.conj a).toMonoidHom := by rw [hcenter_Pstar]
                  _ = centerIn (G := Q) (Pstar_a : Subgroup Q) := hmap_center_Pstar
                  _ = centerIn (G := Q) (S : Subgroup Q) := hcenter_Pstar_a.symm
              ext z
              constructor
              · intro hz
                rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
                have hza :
                    (MulAut.conj a) z ∈ centerIn (G := Q) (S : Subgroup Q) := by
                  have hmem :
                      (MulAut.conj a) z ∈
                        (centerIn (G := Q) (S : Subgroup Q)).map
                          (MulAut.conj a).toMonoidHom :=
                    ⟨z, hz, rfl⟩
                  rw [hmap_ZS_a] at hmem
                  exact hmem
                refine ⟨(MulAut.conj a) z, hza, ?_⟩
                simp [a, MulAut.conj_apply, mul_assoc]
              · intro hz
                rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hz
                rcases hz with ⟨w, hw, hwz⟩
                have hw_map :
                    w ∈ (centerIn (G := Q) (S : Subgroup Q)).map
                        (MulAut.conj a).toMonoidHom := by
                  rw [hmap_ZS_a]
                  exact hw
                rcases Subgroup.mem_map.mp hw_map with ⟨v, hv, hvw⟩
                have hz_eq_v : z = v := by
                  rw [← hwz, ← hvw]
                  simp [a, MulAut.conj_apply, mul_assoc]
                simpa [hz_eq_v] using hv
            have hgs_ZN : g * s ∈ ZN := by
              -- Rewriting the equality of centers says exactly that `g s`
              -- normalizes `Z(S)`.
              let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
              change g * s ∈ Subgroup.normalizer ((Z : Subgroup Q) : Set Q)
              rw [Subgroup.mem_normalizer_iff]
              intro z
              constructor
              · intro hz
                have hzR : z ∈ rightConjugate Z (g * s) := by
                  change z ∈ centerIn (G := Q) (S : Subgroup Q) at hz
                  rw [hcenter_gs] at hz
                  simpa [Z] using hz
                rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hzR
                rcases hzR with ⟨w, hw, hwz⟩
                rw [← hwz]
                simpa [Z, MulAut.conj_apply, mul_assoc] using hw
              · intro hz
                have hzR : z ∈ rightConjugate Z (g * s) := by
                  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
                  refine ⟨(g * s) * z * (g * s)⁻¹, hz, ?_⟩
                  simp [mul_assoc]
                change z ∈ centerIn (G := Q) (S : Subgroup Q)
                rw [hcenter_gs]
                simpa [Z] using hzR
            have hyPgs : y ∈ rightConjugate Pder (g * s) := by
              have hsyT : s * y * s⁻¹ ∈ T :=
                (Subgroup.mem_normalizer_iff.mp hs_mem_NT y).1 hyT
              have hsyPg : s * y * s⁻¹ ∈ rightConjugate Pder g := hsyT.2
              rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hsyPg ⊢
              rcases hsyPg with ⟨p, hp, hpy⟩
              refine ⟨p, hp, ?_⟩
              have hpy' : g⁻¹ * p * g = s * y * s⁻¹ := by
                simpa [MulAut.conj_apply, mul_assoc] using hpy
              calc
                (MulAut.conj (g * s)⁻¹).toMonoidHom p = (g * s)⁻¹ * p * (g * s) := by
                  change ((g * s)⁻¹) * p * ((g * s)⁻¹)⁻¹ = (g * s)⁻¹ * p * (g * s)
                  group
                _ = s⁻¹ * (g⁻¹ * p * g) * s := by group
                _ = s⁻¹ * (s * y * s⁻¹) * s := by rw [hpy']
                _ = y := by group
            have hPder_le_ZNcomm : Pder ≤ imageZNcomm := by
              -- Since `S ≤ N_Q(Z(S))`, the image of `S'` lies in
              -- `N_Q(Z(S))'`.
              intro y hy
              change y ∈ (commutator ZN).map ZN.subtype
              rw [Subgroup.mem_map] at hy ⊢
              rcases hy with ⟨c, hc, rfl⟩
              let iS_ZN : (S : Subgroup Q) →* ZN :=
                { toFun := fun z => ⟨(z : Q), hS_le_ZN z.property⟩
                  map_one' := by ext; rfl
                  map_mul' := by intro a b; ext; rfl }
              refine ⟨iS_ZN c, ?_, rfl⟩
              have hmapc : (commutator (S : Subgroup Q)).map iS_ZN ≤ commutator ZN := by
                rw [_root_.commutator_def, Subgroup.map_commutator]
                exact Subgroup.commutator_mono le_top le_top
              exact hmapc ⟨c, hc, rfl⟩
            have hPder_gs_le_image : rightConjugate Pder (g * s) ≤ imageZNcomm := by
              -- Conjugation by `g s ∈ N_Q(Z(S))` preserves the commutator
              -- subgroup of `N_Q(Z(S))`.
              intro y hy
              rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hy
              rcases hy with ⟨p, hp, hpy⟩
              have hp_image : p ∈ imageZNcomm := hPder_le_ZNcomm hp
              change y ∈ (commutator ZN).map ZN.subtype
              rw [Subgroup.mem_map] at hp_image ⊢
              rcases hp_image with ⟨z, hzcomm, hzval⟩
              let aN : ZN := ⟨g * s, hgs_ZN⟩
              have hzconj : aN⁻¹ * z * aN ∈ commutator ZN := by
                haveI : (commutator ZN).Normal := inferInstance
                simpa [aN, mul_assoc] using
                  ((inferInstance : (commutator ZN).Normal).conj_mem z hzcomm aN⁻¹)
              refine ⟨aN⁻¹ * z * aN, hzconj, ?_⟩
              calc
                ((aN⁻¹ * z * aN : ZN) : Q) = (g * s)⁻¹ * (z : Q) * (g * s) := by
                  simp [aN, mul_assoc]
                _ = (MulAut.conj (g * s)⁻¹).toMonoidHom p := by
                  rw [← hzval]
                  simp [mul_assoc]
                _ = y := hpy
            exact hPder_gs_le_image hyPgs
          -- The preceding two local paragraphs are exactly the two generator
          -- families in Huppert IV.3.4, hence their closure `D_Q` lies in
          -- `N_Q(Z(S))'`.
          change huppertIV34GrunKernelSubgroup (Q := Q) (S : Subgroup Q) ≤ imageZNcomm
          rw [huppertIV34GrunKernelSubgroup_def (Q := Q) (P := (S : Subgroup Q))]
          dsimp only
          rw [Subgroup.closure_le]
          intro y hy
          rcases hy with hyN | hyC
          · change y ∈ (S : Subgroup Q) ∧
                y ∈ (commutator NS).map NS.subtype at hyN
            exact hnormalizer_family hyN.1 hyN.2
          · change ∃ g : Q,
                y ∈ (S : Subgroup Q) ∧ y ∈ rightConjugate Pder g at hyC
            exact hconjugate_family hyC
        have hx_image : (x : Q) ∈ imageZNcomm := hDQ_le_image hxDQ
        rcases Subgroup.mem_map.mp hx_image with ⟨z, hzcomm, hzval⟩
        have hz_eq : z = ⟨(x : Q), hS_le_ZN x.property⟩ := by
          ext
          exact hzval
        simpa [hz_eq] using hzcomm
      let y : (SN : Subgroup ZN) := by
        refine ⟨⟨(x : Q), hS_le_ZN x.property⟩, ?_⟩
        simp [SN, Subgroup.mem_subgroupOf]
      have hyKZN : y ∈ KZN := by
        have hyZN_comm : (y : ZN) ∈ commutator ZN := by
          simpa [y] using hxZNcomm
        simpa [KZN, huppertIV33SylowDerivedSubgroup, y] using
          Subgroup.mem_subgroupOf.mpr hyZN_comm
      refine ⟨y, hyKZN, ?_⟩
      ext
      rfl
  exact ⟨(QuotientGroup.congr (G' := KZN) (H' := KQ) (e := eSN_S) hden_eq).symm⟩

/-- Huppert IV.3.7, second theorem of Grun. -/
public theorem huppert_IV_3_7_second_grun
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    let ZN : Subgroup Q :=
      Subgroup.normalizer
        ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
    letI : (hktAbelianPResidual q Q).Normal :=
      hktAbelianPResidual_normal (Q := Q) (q := q)
    letI : (hktAbelianPResidual q ZN).Normal :=
      hktAbelianPResidual_normal (Q := ZN) (q := q)
    Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
      (ZN ⧸ hktAbelianPResidual q ZN)) := by
  classical
  let ZN : Subgroup Q :=
    Subgroup.normalizer
      ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
  let hS_le_ZN : (S : Subgroup Q) ≤ ZN := by
    simpa [ZN] using
      hkt_huppert_iv52_sylow_le_normalizer_centerIn (Q := Q) (q := q) S
  let SN : Sylow q ZN := S.subtype hS_le_ZN
  letI : (hktAbelianPResidual q Q).Normal :=
    hktAbelianPResidual_normal (Q := Q) (q := q)
  letI : (hktAbelianPResidual q ZN).Normal :=
    hktAbelianPResidual_normal (Q := ZN) (q := q)
  obtain ⟨eQ⟩ :=
    (huppert_IV_3_3_sylow_abelian_residual (Q := Q) (q := q) S).2
  obtain ⟨eSN⟩ :=
    (huppert_IV_3_3_sylow_abelian_residual (Q := ZN) (q := q) SN).2
  obtain ⟨eSylow⟩ :=
    huppert_IV_3_7_sylow_quotient_equiv_center_normalizer_source
      (Q := Q) (q := q) S hpnormal
  exact ⟨eQ.trans (eSylow.trans eSN.symm)⟩

end External
end CFSG.BenderSuzuki


