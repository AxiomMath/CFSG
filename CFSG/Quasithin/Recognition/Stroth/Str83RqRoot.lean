module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

def rootOmega (v : ℤ) : Subgroup G :=
  closure {x | x ∈ pCoreOf 2 (t.Gw v (v + 1)) ∧ x ^ 2 ∈ t.Qv v}

private def moveElt (t : Track L1 L2 S) (v : ℤ) : G :=
  if Even v then (t.x₂ * t.x₁) ^ (v / 2) else (t.x₂ * t.x₁) ^ (v / 2) * t.x₂

private theorem map_Gw_moveElt (t : Track L1 L2 S) (v : ℤ) :
    (t.Gw 0 1).map (MulAut.conj (moveElt t v)).toMonoidHom = t.Gw v (v + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · have hm : moveElt t (2 * k) = (t.x₂ * t.x₁) ^ k := by
      unfold moveElt
      rw [if_pos (even_two_mul k), show 2 * k / 2 = k by omega]
    rw [hm]
    change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 0 1).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
      win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (2 * k) (2 * k + 1)
    rw [map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 0 1 k]
    rw [show 0 + 2 * k = 2 * k by ring, show 1 + 2 * k = 2 * k + 1 by ring]
  · have hm : moveElt t (2 * k + 1) = (t.x₂ * t.x₁) ^ k * t.x₂ := by
      unfold moveElt
      rw [if_neg (Int.not_even_two_mul_add_one k), show (2 * k + 1) / 2 = k by omega]
    rw [hm, ← Subgroup.map_conj_map_conj (t.Gw 0 1) t.x₂ ((t.x₂ * t.x₁) ^ k)]
    rw [t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1]
    rw [show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num]
    rw [map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 1 2 k]
    rw [show 1 + 2 * k = 2 * k + 1 by ring, show 2 + 2 * k = 2 * k + 1 + 1 by ring]

private theorem map_Qv_zero_moveElt (t : Track L1 L2 S) {v : ℤ} (hv : Even v) :
    (t.Qv 0).map (MulAut.conj (moveElt t v)).toMonoidHom = t.Qv v := by
  obtain ⟨k, hk⟩ := hv
  rw [hk, show k + k = 2 * k by ring]
  have hm : moveElt t (2 * k) = (t.x₂ * t.x₁) ^ k := by
    unfold moveElt
    rw [if_pos (even_two_mul k), show 2 * k / 2 = k by omega]
  rw [hm]
  change (qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ 0).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
    qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ (2 * k)
  rw [map_qv_tau_pow (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S) 0 k]
  rw [show 0 + 2 * k = 2 * k by ring]

private theorem map_Qv_one_moveElt (t : Track L1 L2 S) {v : ℤ} (hv : ¬ Even v) :
    (t.Qv 1).map (MulAut.conj (moveElt t v)).toMonoidHom = t.Qv v := by
  obtain ⟨k, rfl⟩ := Int.not_even_iff_odd.mp hv
  have hm : moveElt t (2 * k + 1) = (t.x₂ * t.x₁) ^ k * t.x₂ := by
    unfold moveElt
    rw [if_neg (Int.not_even_two_mul_add_one k), show (2 * k + 1) / 2 = k by omega]
  rw [hm, ← Subgroup.map_conj_map_conj (t.Qv 1) t.x₂ ((t.x₂ * t.x₁) ^ k)]
  rw [t.track.map_qv_x₂ (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S)
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) 1]
  rw [show (2 : ℤ) - 1 = 1 by norm_num]
  rw [map_qv_tau_pow (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S) 1 k]
  rw [show 1 + 2 * k = 2 * k + 1 by ring]

private theorem rootOmega_eq_map_of (t : Track L1 L2 S) {v e : ℤ} {f : G}
    (hG : (t.Gw 0 1).map (MulAut.conj f).toMonoidHom = t.Gw v (v + 1))
    (hQ : (t.Qv e).map (MulAut.conj f).toMonoidHom = t.Qv v) :
    t.rootOmega v = (closure {y : G | y ∈ pCoreOf 2 (t.Gw 0 1) ∧ y ^ 2 ∈ t.Qv e}).map
      (MulAut.conj f).toMonoidHom := by
  have hP : pCoreOf 2 (t.Gw v (v + 1)) =
      (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj f).toMonoidHom := by
    rw [← hG, pCoreOf_map_mulEquiv]
  have hset : {x : G | x ∈ pCoreOf 2 (t.Gw v (v + 1)) ∧ x ^ 2 ∈ t.Qv v} =
      (MulAut.conj f) '' {y : G | y ∈ pCoreOf 2 (t.Gw 0 1) ∧ y ^ 2 ∈ t.Qv e} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, MulAut.conj_apply]
    constructor
    · rintro ⟨hxR, hxQ⟩
      have hyR : f⁻¹ * x * f ∈ pCoreOf 2 (t.Gw 0 1) := by
        have hxR' : x ∈ (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj f).toMonoidHom :=
          hP ▸ hxR
        exact (mem_map_conj_iff (K := pCoreOf 2 (t.Gw 0 1)) (g := f)).mp hxR'
      have hyQ : (f⁻¹ * x * f) ^ 2 ∈ t.Qv e := by
        rw [show (f⁻¹ * x * f) ^ 2 = f⁻¹ * x ^ 2 * f by
          rw [pow_two, pow_two]; group]
        have hxQ' : x ^ 2 ∈ (t.Qv e).map (MulAut.conj f).toMonoidHom := hQ.symm ▸ hxQ
        exact (mem_map_conj_iff (K := t.Qv e) (g := f)).mp hxQ'
      exact ⟨f⁻¹ * x * f, ⟨hyR, hyQ⟩, by group⟩
    · rintro ⟨y, ⟨hyR, hyQ⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hP]
        exact Subgroup.mem_map_of_mem _ hyR
      · rw [show (f * y * f⁻¹) ^ 2 = f * y ^ 2 * f⁻¹ by
          rw [pow_two, pow_two]; group]
        rw [← hQ]
        exact Subgroup.mem_map_of_mem _ hyQ
  unfold rootOmega
  rw [hset, MonoidHom.map_closure]
  simp only [MulEquiv.coe_toMonoidHom]

private theorem rootOmega_eq_map (t : Track L1 L2 S) (v : ℤ) :
    t.rootOmega v = (closure {y : G | y ∈ pCoreOf 2 (t.Gw 0 1) ∧
      y ^ 2 ∈ t.Qv (if Even v then 0 else 1)}).map
        (MulAut.conj (moveElt t v)).toMonoidHom := by
  by_cases hv : Even v
  · rw [if_pos hv]
    exact rootOmega_eq_map_of t (map_Gw_moveElt t v) (map_Qv_zero_moveElt t hv)
  · rw [if_neg hv]
    exact rootOmega_eq_map_of t (map_Gw_moveElt t v) (map_Qv_one_moveElt t hv)

private noncomputable def szEquiv {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* Sz a :=
  (oTwoQuotSupEquiv hfr.hF.1).trans (Classical.choice hfr.hSz)

private theorem baseSylow_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) :=
  isSylowTwoOf_sup_pCoreOf hfr.hF.1
    (eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩))

private theorem baseSylow_right {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSylowTwoOf S (L2 ⊔ Q2 L1 L2 S) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
      (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hfr.hF.1.symm
    (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

private theorem baseSz_facts {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    ∃ X0 : Subgroup G,
      (∀ x, x ∈ X0 ↔ x ∈ S ∧ x ^ 2 ∈ Q1 L1 L2 S) ∧
      Q1 L1 L2 S ≤ X0 ∧
      (Q1 L1 L2 S).relIndex X0 = 2 ^ (2 * a + 1) ∧
      t.K ≤ normalizer (X0 : Set G) ∧
      ⁅X0, S⁆ ≤ Q1 L1 L2 S ∧
      closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 0} = X0 := by
  classical
  obtain ⟨X0, hmem, hQ, hrel, -, -, -⟩ :=
    exists_X0_sz (L := L1 ⊔ Q1 L1 L2 S) (T := S) hfr.ha (szEquiv hfr) (baseSylow_left hfr)
  have hmem' : ∀ x, x ∈ X0 ↔ x ∈ S ∧ x ^ 2 ∈ Q1 L1 L2 S := by
    intro x
    rw [hmem x, pCoreOf_sup_pCoreOf hfr.hF.1]
  have hQ' : Q1 L1 L2 S ≤ X0 := by
    rw [← pCoreOf_sup_pCoreOf hfr.hF.1]
    exact hQ
  have hrel' : (Q1 L1 L2 S).relIndex X0 = 2 ^ (2 * a + 1) := by
    rw [← pCoreOf_sup_pCoreOf hfr.hF.1]
    exact hrel
  have hK : t.K ≤ normalizer (X0 : Set G) := by
    have hKS : t.K ≤ normalizer (S : Set G) :=
      (le_sup_right : t.K ≤ S ⊔ t.K).trans (t.sup_K_eq_bigB ▸ hfr.hN)
    have hKQ : t.K ≤ normalizer (Q1 L1 L2 S : Set G) :=
      t.K_le_Gv 0 |>.trans (by rw [t.Gv_zero]; exact le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hmem']
    constructor
    · intro hx
      have hxS : k * x * k⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hKS hk) x).mp hx.1
      have hxQ : k * x ^ 2 * k⁻¹ ∈ Q1 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hKQ hk) (x ^ 2)).mp hx.2
      refine ⟨hxS, ?_⟩
      rwa [show (k * x * k⁻¹) ^ 2 = k * x ^ 2 * k⁻¹ by
        rw [pow_two, pow_two]; group]
    · intro hx
      have hk' : k⁻¹ ∈ t.K := t.K.inv_mem hk
      refine ⟨?_, ?_⟩
      · have h1 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hKS hk') (k * x * k⁻¹)).mp hx.1
        have h2 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
        rwa [h2] at h1
      · have h1 : k⁻¹ * (k * x * k⁻¹) ^ 2 * k⁻¹⁻¹ ∈ Q1 L1 L2 S :=
          (Subgroup.mem_normalizer_iff.mp (hKQ hk') ((k * x * k⁻¹) ^ 2)).mp hx.2
        have h2 : k⁻¹ * (k * x * k⁻¹) ^ 2 * k⁻¹⁻¹ = x ^ 2 := by
          rw [pow_two, pow_two]; group
        rwa [h2] at h1
  have hcent : ⁅X0, S⁆ ≤ Q1 L1 L2 S := by
    let L := L1 ⊔ Q1 L1 L2 S
    let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
    have hQ0 : pCoreOf 2 L = Q1 L1 L2 S := pCoreOf_sup_pCoreOf hfr.hF.1
    have hSyl : IsSylowTwoOf S L := baseSylow_left hfr
    have hB : BenderType (oTwoQuot ↥L) (2 * a + 1) 2 1 :=
      BenderType.suzuki a hfr.ha (szEquiv hfr |>.trans
        (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
    obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf hSyl
    obtain ⟨t0, hc⟩ := hB.exists_benderCore P
    refine Subgroup.commutator_le.mpr fun x hx s hs => ?_
    have hxS : x ∈ S := (hmem' x).mp hx |>.1
    have hxQ : x ^ 2 ∈ Q1 L1 L2 S := (hmem' x).mp hx |>.2
    let xL : ↥L := ⟨x, hSyl.1 hxS⟩
    let sL : ↥L := ⟨s, hSyl.1 hs⟩
    have hxP : π xL ∈ (P : Subgroup (oTwoQuot ↥L)) := by
      rw [hP]
      refine Subgroup.mem_map_of_mem π (K := S.subgroupOf L) (x := xL) ?_
      rw [Subgroup.mem_subgroupOf]
      exact hxS
    have hsP : π sL ∈ (P : Subgroup (oTwoQuot ↥L)) := by
      rw [hP]
      refine Subgroup.mem_map_of_mem π (K := S.subgroupOf L) (x := sL) ?_
      rw [Subgroup.mem_subgroupOf]
      exact hs
    have hx2 : π xL * π xL = 1 := by
      have hsq : xL * xL ∈ pCore 2 ↥L := by
        refine (F1.mem_pCore_iff_coe (xL * xL)).mpr ?_
        rw [hQ0]
        simpa [Subgroup.coe_mul, pow_two] using hxQ
      have h1 : (QuotientGroup.mk (xL * xL) : oTwoQuot ↥L) = 1 :=
        (QuotientGroup.eq_one_iff (xL * xL)).mpr hsq
      simpa [π, map_mul] using h1
    have hroot := hc.mem_rootCenter_of_mul_self hxP hx2
    have hcomm : π sL * π xL = π xL * π sL := (mem_rootCenter_iff.mp hroot).2 (π sL) hsP
    have hpi : π ⁅xL, sL⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    have hpcL : ⁅xL, sL⁆ ∈ pCore 2 ↥L := by
      have h := MonoidHom.mem_ker.mpr hpi
      rwa [show π.ker = pCore 2 ↥L from QuotientGroup.ker_mk' _] at h
    have hcoe := (F1.mem_pCore_iff_coe ⁅xL, sL⁆).mp hpcL
    rw [hQ0] at hcoe
    simpa [commutatorElement_def] using hcoe
  have hclos : closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 0} = X0 := by
    have hset : {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 0} =
        (X0 : Set G) := by
      ext x
      change x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 0 ↔ x ∈ X0
      rw [hmem' x, t.pCoreOf_Gw_zero_one hfr, t.Qv_zero]
    rw [hset, Subgroup.closure_eq]
  exact ⟨X0, hmem', hQ', hrel', hK, hcent, hclos⟩

private theorem sq_mem_Q2_of_mem_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {x : G} (hx : x ∈ S) : x ^ 2 ∈ Q2 L1 L2 S := by
  let L := L2 ⊔ Q2 L1 L2 S
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hQ : pCoreOf 2 L = Q2 L1 L2 S := str86_pCoreOf_u3H hfr.hF
  have hSyl : IsSylowTwoOf S L := baseSylow_right hfr
  have hL2q : IsL2Quot f (oTwoQuot ↥L) := by
    simpa [L] using str86_isL2Quot_u3H hfr.hF hfr.hL2
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf hSyl
  have hsq := (l2Sylow_sq_mem hfr.hf hL2q P).1
  have hxL : x ∈ L := hSyl.1 hx
  let xL : ↥L := ⟨x, hxL⟩
  have hxP : π xL ∈ (P : Subgroup (oTwoQuot ↥L)) := by
    rw [hP]
    refine Subgroup.mem_map_of_mem π (K := S.subgroupOf L) (x := xL) ?_
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have h1 : π xL * π xL = 1 := hsq _ hxP
  have h2 : (QuotientGroup.mk (xL * xL) : oTwoQuot ↥L) = 1 := by
    rw [QuotientGroup.mk_mul]
    simpa [π] using h1
  have h3 : xL * xL ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff (xL * xL)).mp h2
  have h4 := (F1.mem_pCore_iff_coe (xL * xL)).mp h3
  rw [hQ] at h4
  simpa [Subgroup.coe_mul, pow_two] using h4

private theorem base_closure_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 1} = S := by
  have hset : {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 1} = (S : Set G) := by
    ext x
    rw [t.pCoreOf_Gw_zero_one hfr, t.Qv_one]
    exact ⟨fun h => h.1, fun hx => ⟨hx, sq_mem_Q2_of_mem_S hfr hx⟩⟩
  rw [hset, Subgroup.closure_eq]

private theorem S_commutator_le_Q2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ⁅S, S⁆ ≤ Q2 L1 L2 S := by
  classical
  let L := L2 ⊔ Q2 L1 L2 S
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hQ : pCoreOf 2 L = Q2 L1 L2 S := str86_pCoreOf_u3H hfr.hF
  have hSyl : IsSylowTwoOf S L := baseSylow_right hfr
  have hL2q : IsL2Quot f (oTwoQuot ↥L) := by
    simpa [L] using str86_isL2Quot_u3H hfr.hF hfr.hL2
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf hSyl
  have hsq := (l2Sylow_sq_mem hfr.hf hL2q P).1
  have hcommP : ∀ a ∈ (P : Subgroup (oTwoQuot ↥L)), ∀ b ∈ (P : Subgroup (oTwoQuot ↥L)),
      a * b = b * a := by
    intro a ha b hb
    have hab : a * b ∈ (P : Subgroup (oTwoQuot ↥L)) :=
      (P : Subgroup (oTwoQuot ↥L)).mul_mem ha hb
    have h1 : (a * b) * (a * b) = 1 := hsq _ hab
    have ha1 : a * a = 1 := hsq _ ha
    have hb1 : b * b = 1 := hsq _ hb
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right ha1, inv_eq_of_mul_eq_one_right hb1]
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  let xL : ↥L := ⟨x, hSyl.1 hx⟩
  let yL : ↥L := ⟨y, hSyl.1 hy⟩
  have hxP : π xL ∈ (P : Subgroup (oTwoQuot ↥L)) := by
    rw [hP]
    refine Subgroup.mem_map_of_mem π (K := S.subgroupOf L) (x := xL) ?_
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hyP : π yL ∈ (P : Subgroup (oTwoQuot ↥L)) := by
    rw [hP]
    refine Subgroup.mem_map_of_mem π (K := S.subgroupOf L) (x := yL) ?_
    rw [Subgroup.mem_subgroupOf]
    exact hy
  have hcomm : π xL * π yL = π yL * π xL := hcommP _ hxP _ hyP
  have hpi : π ⁅xL, yL⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hpcL : ⁅xL, yL⁆ ∈ pCore 2 ↥L := by
    have h := MonoidHom.mem_ker.mpr hpi
    rwa [show π.ker = pCore 2 ↥L from QuotientGroup.ker_mk' _] at h
  have hcoe := (F1.mem_pCore_iff_coe ⁅xL, yL⁆).mp hpcL
  rw [hQ] at hcoe
  simpa [commutatorElement_def] using hcoe

private theorem mem_pCoreOf_Gw_move_iff (t : Track L1 L2 S) {v : ℤ} {f : G}
    (hG : (t.Gw 0 1).map (MulAut.conj f).toMonoidHom = t.Gw v (v + 1)) {x : G} :
    x ∈ pCoreOf 2 (t.Gw v (v + 1)) ↔ f⁻¹ * x * f ∈ pCoreOf 2 (t.Gw 0 1) := by
  have hP : pCoreOf 2 (t.Gw v (v + 1)) =
      (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj f).toMonoidHom := by
    rw [← hG, pCoreOf_map_mulEquiv]
  rw [hP, mem_map_conj_iff]

private theorem mem_Qv_move_iff (t : Track L1 L2 S) {v e : ℤ} {f : G}
    (hQ : (t.Qv e).map (MulAut.conj f).toMonoidHom = t.Qv v) {x : G} :
    x ∈ t.Qv v ↔ f⁻¹ * x * f ∈ t.Qv e := by
  rw [← hQ, mem_map_conj_iff]

private theorem Qv_le_pCoreOf_Gw {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) :
    t.Qv v ≤ pCoreOf 2 (t.Gw v (v + 1)) := by
  have hG := map_Gw_moveElt t v
  have hP : pCoreOf 2 (t.Gw v (v + 1)) =
      (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj (moveElt t v)).toMonoidHom := by
    rw [← hG, pCoreOf_map_mulEquiv]
  by_cases hv : Even v
  · have hQ := map_Qv_zero_moveElt t hv
    rw [show t.Qv v = (t.Qv 0).map (MulAut.conj (moveElt t v)).toMonoidHom
      from hQ.symm, hP]
    refine Subgroup.map_mono ?_
    rw [t.pCoreOf_Gw_zero_one hfr, t.Qv_zero]
    exact F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hfr.hF)
  · have hQ := map_Qv_one_moveElt t hv
    rw [show t.Qv v = (t.Qv 1).map (MulAut.conj (moveElt t v)).toMonoidHom
      from hQ.symm, hP]
    refine Subgroup.map_mono ?_
    rw [t.pCoreOf_Gw_zero_one hfr, t.Qv_one]
    exact F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.hF)

theorem mem_rootOmega_iff {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) {x : G} :
    x ∈ t.rootOmega v ↔ x ∈ pCoreOf 2 (t.Gw v (v + 1)) ∧ x ^ 2 ∈ t.Qv v := by
  classical
  by_cases hv : Even v
  · obtain ⟨X0, hmem, -, -, -, -, hclos⟩ := baseSz_facts t hfr
    rw [rootOmega_eq_map t v, if_pos hv, hclos, mem_map_conj_iff, hmem]
    constructor
    · rintro ⟨hyS, hyQ⟩
      refine ⟨(mem_pCoreOf_Gw_move_iff t (map_Gw_moveElt t v)).mpr ?_,
        (mem_Qv_move_iff t (map_Qv_zero_moveElt t hv) (x := x ^ 2)).mpr ?_⟩
      · rw [t.pCoreOf_Gw_zero_one hfr]
        exact hyS
      · rw [t.Qv_zero]
        rw [show (moveElt t v)⁻¹ * x ^ 2 * moveElt t v =
          ((moveElt t v)⁻¹ * x * moveElt t v) ^ 2 by rw [pow_two, pow_two]; group]
        exact hyQ
    · rintro ⟨hxR, hxQ⟩
      refine ⟨?_, ?_⟩
      · have h := (mem_pCoreOf_Gw_move_iff t (map_Gw_moveElt t v)).mp hxR
        rwa [t.pCoreOf_Gw_zero_one hfr] at h
      · have h := (mem_Qv_move_iff t (map_Qv_zero_moveElt t hv) (x := x ^ 2)).mp hxQ
        rwa [t.Qv_zero, show (moveElt t v)⁻¹ * x ^ 2 * moveElt t v =
          ((moveElt t v)⁻¹ * x * moveElt t v) ^ 2 by rw [pow_two, pow_two]; group] at h
  · rw [rootOmega_eq_map t v, if_neg hv, base_closure_one t hfr, mem_map_conj_iff]
    constructor
    · intro hyS
      refine ⟨(mem_pCoreOf_Gw_move_iff t (map_Gw_moveElt t v)).mpr ?_,
        (mem_Qv_move_iff t (map_Qv_one_moveElt t hv) (x := x ^ 2)).mpr ?_⟩
      · rw [t.pCoreOf_Gw_zero_one hfr]
        exact hyS
      · have hyQ : ((moveElt t v)⁻¹ * x * moveElt t v) ^ 2 ∈ t.Qv 1 := by
          rw [t.Qv_one]
          exact sq_mem_Q2_of_mem_S hfr hyS
        have hyQ' : (moveElt t v)⁻¹ * x ^ 2 * moveElt t v ∈ t.Qv 1 := by
          rw [t.Qv_one]
          have h := hyQ
          rw [t.Qv_one] at h
          rw [show (moveElt t v)⁻¹ * x ^ 2 * moveElt t v =
            ((moveElt t v)⁻¹ * x * moveElt t v) ^ 2 by rw [pow_two, pow_two]; group]
          exact h
        exact hyQ'
    · rintro ⟨hxR, hxQ⟩
      have h := (mem_pCoreOf_Gw_move_iff t (map_Gw_moveElt t v)).mp hxR
      rwa [t.pCoreOf_Gw_zero_one hfr] at h

theorem Qv_le_rootOmega {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) : t.Qv v ≤ t.rootOmega v := by
  intro x hx
  rw [mem_rootOmega_iff t hfr v]
  exact ⟨Qv_le_pCoreOf_Gw t hfr v hx, (t.Qv v).pow_mem hx 2⟩

theorem relIndex_rootOmega {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) :
    (t.Qv v).relIndex (t.rootOmega v) = if Even v then 2 ^ (2 * a + 1) else 2 ^ f := by
  classical
  by_cases hv : Even v
  · obtain ⟨X0, -, -, hrel, -, -, hclos⟩ := baseSz_facts t hfr
    rw [rootOmega_eq_map t v, if_pos hv, hclos,
      show t.Qv v = (t.Qv 0).map (MulAut.conj (moveElt t v)).toMonoidHom
        from (map_Qv_zero_moveElt t hv).symm]
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    rw [t.Qv_zero, hrel, if_pos hv]
  · rw [rootOmega_eq_map t v, if_neg hv, base_closure_one t hfr,
      show t.Qv v = (t.Qv 1).map (MulAut.conj (moveElt t v)).toMonoidHom
        from (map_Qv_one_moveElt t hv).symm]
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    have hrelQ2 : (Q2 L1 L2 S).relIndex S = 2 ^ f := by
      have h := (t.relIndex_Qv_pCoreOf hfr 1).1
      rw [show (1 : ℤ) - 1 = 0 by norm_num, t.Qv_one, t.pCoreOf_Gw_zero_one hfr,
        if_neg Int.not_even_one] at h
      exact h
    rw [t.Qv_one, if_neg hv]
    exact hrelQ2

theorem commutator_rootOmega_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) :
    ⁅t.rootOmega v, pCoreOf 2 (t.Gw v (v + 1))⁆ ≤ t.Qv v := by
  classical
  have hP : pCoreOf 2 (t.Gw v (v + 1)) =
      S.map (MulAut.conj (moveElt t v)).toMonoidHom := by
    rw [show pCoreOf 2 (t.Gw v (v + 1)) =
        (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj (moveElt t v)).toMonoidHom from by
      rw [← map_Gw_moveElt t v, pCoreOf_map_mulEquiv], t.pCoreOf_Gw_zero_one hfr]
  by_cases hv : Even v
  · obtain ⟨X0, -, -, -, -, hcent, hclos⟩ := baseSz_facts t hfr
    have hQ := map_Qv_zero_moveElt t hv
    rw [rootOmega_eq_map t v, if_pos hv, hclos, hP, ← hQ, t.Qv_zero]
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hcent
  · have hQ := map_Qv_one_moveElt t hv
    rw [rootOmega_eq_map t v, if_neg hv, base_closure_one t hfr, hP, ← hQ, t.Qv_one]
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (S_commutator_le_Q2 hfr)

private theorem base_zero_closure_le_sup {a f : ℕ}
    (t : Track L1 L2 S) (hfr : Frame L1 L2 S a f) {X : Subgroup G}
    (hXR : X ≤ pCoreOf 2 (t.Gw 0 1))
    (hXK : t.K ≤ normalizer (X : Set G)) (hXQ : ¬ X ≤ t.Qv 0) :
    closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 0} ≤ X ⊔ t.Qv 0 := by
  classical
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hfr.hF)
  have hQ1L1 : Q1 L1 L2 S ≤ normalizer (L1 : Set G) :=
    (pCoreOf_le 2 (P1 L1 L2 S)).trans
      (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hfr.hF.1))
  have hQ1N1 : Q1 L1 L2 S ≤ normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
    intro q hq
    exact A4.mem_normalizer_inf ((hQ1S.trans Subgroup.le_normalizer) hq) (hQ1L1 hq)
  have hQ1normS : S ≤ normalizer (Q1 L1 L2 S : Set G) := by
    have hSB : S ≤ bigB L1 L2 S :=
      (le_sup_left : S ≤ S ⊔ t.K).trans (le_of_eq t.sup_K_eq_bigB)
    exact (hSB.trans le_sup_right).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  set X1 : Subgroup G := (X ⊔ Q1 L1 L2 S) ⊓ (S ⊓ L1) with hX1
  have hX1T : X1 ≤ S ⊓ L1 := inf_le_right
  have hD : RonanF13.HallTwoPrime t.D1
      (L1 ⊓ normalizer ((S ⊓ L1 : Subgroup G) : Set G)) := by
    simpa [borelOf] using t.hD1hall
  have hXD : t.D1 ≤ normalizer (X1 : Set G) := by
    intro d hd
    have hdK : d ∈ t.K := Subgroup.mem_sup_left hd
    have hdX : d ∈ normalizer (X : Set G) := hXK hdK
    have hdP : d ∈ P1 L1 L2 S := by
      have := t.K_le_Gv 0 hdK
      rwa [t.Gv_zero] at this
    have hdQ : d ∈ normalizer (Q1 L1 L2 S : Set G) :=
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hdP
    have hdXQ : d ∈ normalizer ((X ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (X := Subgroup.zpowers d) (zpowers_le.mpr hdX)
        (zpowers_le.mpr hdQ) (mem_zpowers d)
    have hdSL : d ∈ normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
      have hd' := t.hD1hall.1 hd
      exact (show d ∈ L1 ⊓ normalizer ((S ⊓ L1 : Subgroup G) : Set G) from by
        simpa [borelOf] using hd').2
    exact A4.mem_normalizer_inf hdXQ hdSL
  have hXnot : ¬ X1 ≤ pCoreOf 2 L1 := by
    intro hle
    apply hXQ
    intro x hx
    have hxS : x ∈ S := by rw [← t.pCoreOf_Gw_zero_one hfr]; exact hXR hx
    have hxSsup : x ∈ (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1 ▸ hxS
    obtain ⟨y, hyS1, q, hq, hxy⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ1N1).mp hxSsup
    have hyX1 : y ∈ X1 := by
      refine ⟨?_, hyS1⟩
      rw [show y = x * q⁻¹ by rw [hxy]; group]
      exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ((Q1 L1 L2 S).inv_mem hq))
    have hQ1leO : pCoreOf 2 L1 ≤ Q1 L1 L2 S :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
        (le_sup_left : L1 ≤ P1 L1 L2 S)
        (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hfr.hF.1))
    rw [hxy, t.Qv_zero]
    exact (Q1 L1 L2 S).mul_mem (hQ1leO (hle hyX1)) hq
  have key := mem_sup_pCoreOf_of_torus_of_sz (L := L1) (T := S ⊓ L1) (D := t.D1)
    (X := X1) hfr.ha hfr.hSz hfr.hF.1.h1.sylow hD hX1T hXD hXnot
  rw [Subgroup.closure_le]
  rintro x ⟨hxR, hxQ⟩
  have hxS : x ∈ S := by rw [← t.pCoreOf_Gw_zero_one hfr]; exact hxR
  have hxQ1 : x ^ 2 ∈ Q1 L1 L2 S := by rw [← t.Qv_zero]; exact hxQ
  have hxSsup : x ∈ (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1 ▸ hxS
  obtain ⟨y, hyS1, q, hq, hxy⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQ1N1).mp hxSsup
  have haQ : y * q * y⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hQ1normS hyS1.1) q).mp hq
  have hy2Q : y ^ 2 ∈ Q1 L1 L2 S := by
    have hx2eq : x ^ 2 = (y * q * y⁻¹) * y ^ 2 * q := by
      rw [hxy, pow_two, pow_two]; group
    have h1 : y ^ 2 = (y * q * y⁻¹)⁻¹ * x ^ 2 * q⁻¹ := by
      rw [hx2eq, pow_two]; group
    rw [h1]
    exact (Q1 L1 L2 S).mul_mem
      ((Q1 L1 L2 S).mul_mem ((Q1 L1 L2 S).inv_mem haQ) hxQ1)
      ((Q1 L1 L2 S).inv_mem hq)
  have hy2O : y ^ 2 ∈ pCoreOf 2 L1 := by
    have hmem : y ^ 2 ∈ L1 ⊓ Q1 L1 L2 S :=
      ⟨by simpa [pow_two] using L1.mul_mem hyS1.2 hyS1.2, hy2Q⟩
    rwa [str86_inf_p1_q1 hfr.hF] at hmem
  have hykey := key y hyS1 (by simpa [pow_two] using hy2O)
  have hQ1leO : pCoreOf 2 L1 ≤ Q1 L1 L2 S :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
      (le_sup_left : L1 ≤ P1 L1 L2 S)
      (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hfr.hF.1))
  have hX1le : X1 ⊔ pCoreOf 2 L1 ≤ X ⊔ Q1 L1 L2 S :=
    sup_le ((le_of_eq hX1).trans inf_le_left) (hQ1leO.trans le_sup_right)
  rw [hxy, t.Qv_zero]
  exact (X ⊔ Q1 L1 L2 S).mul_mem (hX1le hykey) (Subgroup.mem_sup_right hq)

private theorem base_one_closure_le_sup {a f : ℕ}
    (t : Track L1 L2 S) (hfr : Frame L1 L2 S a f) {X : Subgroup G}
    (hXR : X ≤ pCoreOf 2 (t.Gw 0 1))
    (hXK : t.K ≤ normalizer (X : Set G)) (hXQ : ¬ X ≤ t.Qv 1) :
    closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv 1} ≤ X ⊔ t.Qv 1 := by
  classical
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
      (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.hF)
  have hBL2 : bigB L1 L2 S ≤ normalizer (L2 : Set G) := by
    rw [bigB_comm]
    exact bigB_le_normalizer_of_hyp111 hfr.hF.1.symm
  have hQ2L2 : Q2 L1 L2 S ≤ normalizer (L2 : Set G) :=
    (pCoreOf_le 2 (P2 L1 L2 S)).trans (sup_le Subgroup.le_normalizer hBL2)
  have hQ2N2 : Q2 L1 L2 S ≤ normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
    intro q hq
    exact A4.mem_normalizer_inf ((hQ2S.trans Subgroup.le_normalizer) hq) (hQ2L2 hq)
  have hQ2normS : S ≤ normalizer (Q2 L1 L2 S : Set G) := by
    have hSB : S ≤ bigB L1 L2 S :=
      (le_sup_left : S ≤ S ⊔ t.K).trans (le_of_eq t.sup_K_eq_bigB)
    exact (hSB.trans le_sup_right).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  set X1 : Subgroup G := (X ⊔ Q2 L1 L2 S) ⊓ (S ⊓ L2) with hX1
  have hX1T : X1 ≤ S ⊓ L2 := inf_le_right
  have hD : RonanF13.HallTwoPrime t.D2
      (L2 ⊓ normalizer ((S ⊓ L2 : Subgroup G) : Set G)) := by
    simpa [borelOf] using t.hD2hall
  have hXD : t.D2 ≤ normalizer (X1 : Set G) := by
    intro d hd
    have hdK : d ∈ t.K := Subgroup.mem_sup_right hd
    have hdX : d ∈ normalizer (X : Set G) := hXK hdK
    have hdP : d ∈ P2 L1 L2 S := by
      have := t.K_le_Gv 1 hdK
      rwa [t.Gv_one] at this
    have hdQ : d ∈ normalizer (Q2 L1 L2 S : Set G) :=
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) hdP
    have hdXQ : d ∈ normalizer ((X ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (X := Subgroup.zpowers d) (zpowers_le.mpr hdX)
        (zpowers_le.mpr hdQ) (mem_zpowers d)
    have hdSL : d ∈ normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
      have hd' := t.hD2hall.1 hd
      exact (show d ∈ L2 ⊓ normalizer ((S ⊓ L2 : Subgroup G) : Set G) from by
        simpa [borelOf] using hd').2
    exact A4.mem_normalizer_inf hdXQ hdSL
  have hXnot : ¬ X1 ≤ pCoreOf 2 L2 := by
    intro hle
    apply hXQ
    intro x hx
    have hxS : x ∈ S := by rw [← t.pCoreOf_Gw_zero_one hfr]; exact hXR hx
    have hxSsup : x ∈ (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2 ▸ hxS
    obtain ⟨y, hyS2, q, hq, hxy⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N2).mp hxSsup
    have hyX1 : y ∈ X1 := by
      refine ⟨?_, hyS2⟩
      rw [show y = x * q⁻¹ by rw [hxy]; group]
      exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ((Q2 L1 L2 S).inv_mem hq))
    have hQ2leO : pCoreOf 2 L2 ≤ Q2 L1 L2 S :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
        (le_sup_left : L2 ≤ P2 L1 L2 S)
        (sup_le Subgroup.le_normalizer hBL2)
    rw [hxy, t.Qv_one]
    exact (Q2 L1 L2 S).mul_mem (hQ2leO (hle hyX1)) hq
  have key := le_sup_pCoreOf_of_torus_of_l2 (L := L2) (T := S ⊓ L2) (D := t.D2)
    (X := X1) hfr.hf hfr.hL2 hfr.hF.1.h2.sylow hD hX1T hXD hXnot
  rw [Subgroup.closure_le]
  rintro x ⟨hxR, -⟩
  have hxS : x ∈ S := by rw [← t.pCoreOf_Gw_zero_one hfr]; exact hxR
  have hxSsup : x ∈ (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2 ▸ hxS
  obtain ⟨y, hyS2, q, hq, hxy⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQ2N2).mp hxSsup
  have hykey := key hyS2
  have hQ2leO : pCoreOf 2 L2 ≤ Q2 L1 L2 S :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
      (le_sup_left : L2 ≤ P2 L1 L2 S)
      (sup_le Subgroup.le_normalizer hBL2)
  have hX1le : X1 ⊔ pCoreOf 2 L2 ≤ X ⊔ Q2 L1 L2 S :=
    sup_le ((le_of_eq hX1).trans inf_le_left) (hQ2leO.trans le_sup_right)
  rw [hxy, t.Qv_one]
  exact (X ⊔ Q2 L1 L2 S).mul_mem (hX1le hykey) (Subgroup.mem_sup_right hq)

private theorem moveElt_mem_normalizer_K (t : Track L1 L2 S) (v : ℤ) :
    moveElt t v ∈ normalizer (t.K : Set G) := by
  unfold moveElt
  split_ifs
  · exact zpow_mem t.track.tau_mem_normalizer _
  · exact mul_mem (zpow_mem t.track.tau_mem_normalizer _) t.track.x₂_norm

theorem rootOmega_le_sup {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) {X : Subgroup G} (hXR : X ≤ pCoreOf 2 (t.Gw v (v + 1)))
    (hXK : t.K ≤ normalizer (X : Set G)) (hXQ : ¬ X ≤ t.Qv v) :
    t.rootOmega v ≤ X ⊔ t.Qv v := by
  classical
  let e : ℤ := if Even v then 0 else 1
  let f : G := moveElt t v
  have hfK : f ∈ normalizer (t.K : Set G) := by
    simpa [f] using moveElt_mem_normalizer_K t v
  have hG : (t.Gw 0 1).map (MulAut.conj f).toMonoidHom = t.Gw v (v + 1) := by
    simpa [f] using map_Gw_moveElt t v
  have hQ : (t.Qv e).map (MulAut.conj f).toMonoidHom = t.Qv v := by
    by_cases hv : Even v
    · have he : e = 0 := by simp [e, hv]
      rw [he]
      simpa [f] using map_Qv_zero_moveElt t hv
    · have he : e = 1 := by simp [e, hv]
      rw [he]
      simpa [f] using map_Qv_one_moveElt t hv
  let Y : Subgroup G := X.map (MulAut.conj f⁻¹).toMonoidHom
  have hYR : Y ≤ pCoreOf 2 (t.Gw 0 1) := by
    intro y hy
    obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hy
    have hP : pCoreOf 2 (t.Gw v (v + 1)) =
        (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj f).toMonoidHom := by
      rw [← hG, pCoreOf_map_mulEquiv]
    have hx' : x ∈ (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj f).toMonoidHom := hP ▸ hXR hxX
    have hy' := (mem_map_conj_iff (K := pCoreOf 2 (t.Gw 0 1)) (g := f)).mp hx'
    simpa [MulAut.conj_apply] using hy'
  have hYK : t.K ≤ normalizer (Y : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hk' : f * k * f⁻¹ ∈ t.K :=
      (Subgroup.mem_normalizer_iff.mp hfK k).mp hk
    have hXk : X.map (MulAut.conj (f * k * f⁻¹)).toMonoidHom = X :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hXK hk')
    calc Y.map (MulAut.conj k).toMonoidHom
        = (X.map (MulAut.conj f⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom := rfl
      _ = X.map (MulAut.conj (k * f⁻¹)).toMonoidHom := by
            rw [Subgroup.map_conj_map_conj]
      _ = X.map (MulAut.conj (f⁻¹ * (f * k * f⁻¹))).toMonoidHom := by
            congr 1
            group
      _ = (X.map (MulAut.conj (f * k * f⁻¹)).toMonoidHom).map
            (MulAut.conj f⁻¹).toMonoidHom := by rw [Subgroup.map_conj_map_conj]
      _ = X.map (MulAut.conj f⁻¹).toMonoidHom := by rw [hXk]
      _ = Y := rfl
  have hYQ : ¬ Y ≤ t.Qv e := by
    intro hle
    apply hXQ
    intro x hx
    have hy : f⁻¹ * x * f ∈ Y := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj f⁻¹).toMonoidHom hx
      simpa [Y, MulAut.conj_apply] using h
    have hyQ : f⁻¹ * x * f ∈ t.Qv e := hle hy
    have hxmap : x ∈ (t.Qv e).map (MulAut.conj f).toMonoidHom :=
      (mem_map_conj_iff (K := t.Qv e) (g := f)).mpr hyQ
    rwa [hQ] at hxmap
  have hbase : closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv e} ≤
      Y ⊔ t.Qv e := by
    by_cases hv : Even v
    · have h0 : e = 0 := by simp [e, hv]
      rw [h0] at hYQ
      rw [h0]
      exact base_zero_closure_le_sup t hfr hYR hYK hYQ
    · have h1 : e = 1 := by simp [e, hv]
      rw [h1] at hYQ
      rw [h1]
      exact base_one_closure_le_sup t hfr hYR hYK hYQ
  have hYX : Y.map (MulAut.conj f).toMonoidHom = X := by
    calc Y.map (MulAut.conj f).toMonoidHom
        = (X.map (MulAut.conj f⁻¹).toMonoidHom).map (MulAut.conj f).toMonoidHom := rfl
      _ = X.map (MulAut.conj (f * f⁻¹)).toMonoidHom := by
            rw [Subgroup.map_conj_map_conj]
      _ = X := by
            rw [mul_inv_cancel]
            ext y
            simp [MulAut.conj_apply]
  rw [rootOmega_eq_map t v]
  change (closure {x : G | x ∈ pCoreOf 2 (t.Gw 0 1) ∧ x ^ 2 ∈ t.Qv e}).map
      (MulAut.conj f).toMonoidHom ≤ X ⊔ t.Qv v
  refine (Subgroup.map_mono (f := (MulAut.conj f).toMonoidHom) hbase).trans ?_
  rw [Subgroup.map_sup, hYX, hQ]

private theorem mem_pCoreOf_map_of {R0 Rv : Subgroup G} {f : G}
    (hG : R0.map (MulAut.conj f).toMonoidHom = Rv) {x : G}
    (hx : x ∈ pCoreOf 2 R0) : f * x * f⁻¹ ∈ pCoreOf 2 Rv := by
  have hP : pCoreOf 2 Rv = (pCoreOf 2 R0).map (MulAut.conj f).toMonoidHom := by
    rw [← hG, pCoreOf_map_mulEquiv]
  rw [hP]
  exact Subgroup.mem_map_of_mem _ hx

private theorem sq_mem_Qv_map {v e : ℤ} {f : G} {x : G}
    (hQ : (t.Qv e).map (MulAut.conj f).toMonoidHom = t.Qv v)
    (hx : x ^ 2 ∈ t.Qv e) : (f * x * f⁻¹) ^ 2 ∈ t.Qv v := by
  have hmap : (MulAut.conj f) (x ^ 2) ∈ (t.Qv e).map (MulAut.conj f).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [hQ] at hmap
  simpa [MulAut.conj_apply, map_pow] using hmap

private theorem mem_sup_map_inv_of_mem {v e : ℤ} {f : G} {X : Subgroup G} {x : G}
    (hQ : (t.Qv e).map (MulAut.conj f).toMonoidHom = t.Qv v)
    (hx : f * x * f⁻¹ ∈ X ⊔ t.Qv v) :
    x ∈ X.map (MulAut.conj f⁻¹).toMonoidHom ⊔ t.Qv e := by
  have hQinv : (t.Qv v).map (MulAut.conj f⁻¹).toMonoidHom = t.Qv e :=
    (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQ).symm
  have hxmap : x ∈ (X ⊔ t.Qv v).map (MulAut.conj f⁻¹).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨f * x * f⁻¹, hx, ?_⟩
    change (MulAut.conj f⁻¹) (f * x * f⁻¹) = x
    rw [MulAut.conj_apply]
    group
  rwa [Subgroup.map_sup, hQinv] at hxmap

private theorem exists_mul_of_mem_Gv_zero
    {a f : ℕ} (t : Track L1 L2 S)
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hXv : X ≤ t.Gv 0)
    (h₁ : ∀ x ∈ pCoreOf 2 (t.Gw 0 1), x ^ 2 ∈ t.Qv 0 → x ∈ X ⊔ t.Qv 0)
    (h₂ : ∀ x ∈ pCoreOf 2 (t.Gw (-1) 0), x ^ 2 ∈ t.Qv 0 → x ∈ X ⊔ t.Qv 0)
    {g : G} (hg : g ∈ t.Gv 0) :
    ∃ m ∈ X, ∃ s ∈ t.Gw 0 1, g = m * s := by
  classical
  let L := L1 ⊔ Q1 L1 L2 S
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hfr.hF)
  have hSB : S ≤ bigB L1 L2 S :=
    (le_sup_left : S ≤ S ⊔ t.K).trans (le_of_eq t.sup_K_eq_bigB)
  have hXvP1 : X ≤ P1 L1 L2 S := t.Gv_zero ▸ hXv
  have hXQ1 : X ≤ normalizer (Q1 L1 L2 S : Set G) :=
    hXvP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hT : IsSylowTwoOf S L := baseSylow_left hfr
  have hx1L1 : t.x₁ ∈ normalizer (L1 : Set G) :=
    (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hfr.hF.1)) t.track.x₁_mem
  have hx1Q : t.x₁ ∈ normalizer (Q1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) t.track.x₁_mem
  have hx1N : t.x₁ ∈ normalizer (L : Set G) :=
    F1.le_normalizer_sup (X := Subgroup.zpowers t.x₁) (zpowers_le.mpr hx1L1)
      (zpowers_le.mpr hx1Q) (mem_zpowers t.x₁)
  have hmapL : L.map (MulAut.conj t.x₁).toMonoidHom = L :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hx1N
  have hT' : IsSylowTwoOf (S.map (MulAut.conj t.x₁).toMonoidHom) L := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₁) hT
    rwa [hmapL] at h
  have hT'eq : pCoreOf 2 (t.Gw (-1) 0) = S.map (MulAut.conj t.x₁).toMonoidHom := by
    have hw : t.Gw (-1) 0 = (t.Gw 0 1).map (MulAut.conj t.x₁).toMonoidHom := by
      have h := t.track.map_win_x₁ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer 0 1
      simpa using h.symm
    rw [hw, pCoreOf_map_mulEquiv, t.pCoreOf_Gw_zero_one hfr]
  have hrel : (Q1 L1 L2 S).relIndex S = (2 ^ (2 * a + 1)) ^ 2 := by
    have h := (t.relIndex_Qv_pCoreOf hfr 0).2
    rw [show (0 : ℤ) + 1 = 1 by norm_num, t.Qv_zero, t.pCoreOf_Gw_zero_one hfr,
      if_pos (show Even (0 : ℤ) from ⟨0, by norm_num⟩)] at h
    exact h
  have hne : S ≠ S.map (MulAut.conj t.x₁).toMonoidHom := by
    intro heq
    have hT'S : S.map (MulAut.conj t.x₁).toMonoidHom ≤ t.Gw (-1) 0 := by
      rw [← hT'eq]
      exact pCoreOf_le 2 (t.Gw (-1) 0)
    have hS01 : S ≤ t.Gw 0 1 := by
      have h := pCoreOf_le 2 (t.Gw 0 1)
      rwa [t.pCoreOf_Gw_zero_one hfr] at h
    have hSwin : S ≤ t.Gw (-1) 1 := by
      intro x hx
      refine mem_win_iff.mpr fun i hi1 hi2 => ?_
      rcases (show i ≤ 0 ∨ i = 1 by omega) with h3 | h3
      · exact mem_win_iff.mp (hT'S (heq ▸ hx)) i hi1 h3
      · rw [h3]
        exact mem_win_iff.mp (hS01 hx) 1 (by omega) le_rfl
    have hSleQ : S ≤ Q1 L1 L2 S := by
      have h := t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0)
        (by norm_num) (by norm_num) hfr.hF.1.h1.pgroup hSwin
      rwa [t.Qv_zero] at h
    have h1 : (Q1 L1 L2 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSleQ
    rw [h1] at hrel
    have hgt : 1 < (2 ^ (2 * a + 1)) ^ 2 := by
      have hb : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
      exact Nat.one_lt_pow (by norm_num : 2 ≠ 0) hb
    omega
  have hgen : L ≤ X ⊔ Q1 L1 L2 S := by
    have h₁' : ∀ x ∈ S, x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L := by
      intro x hx hx2
      rw [pCoreOf_sup_pCoreOf hfr.hF.1] at hx2 ⊢
      have hx2' : x ^ 2 ∈ t.Qv 0 := by
        rw [t.Qv_zero, pow_two]
        exact hx2
      have h := h₁ x (by rwa [t.pCoreOf_Gw_zero_one hfr]) hx2'
      rwa [t.Qv_zero] at h
    have h₂' : ∀ x ∈ S.map (MulAut.conj t.x₁).toMonoidHom,
        x * x ∈ pCoreOf 2 L → x ∈ X ⊔ pCoreOf 2 L := by
      intro x hx hx2
      rw [pCoreOf_sup_pCoreOf hfr.hF.1] at hx2 ⊢
      have hx2' : x ^ 2 ∈ t.Qv 0 := by
        rw [t.Qv_zero, pow_two]
        exact hx2
      have h := h₂ x (by rwa [hT'eq]) hx2'
      rwa [t.Qv_zero] at h
    have h := le_sup_pCoreOf_of_sylow_ne_of_sz (L := L) (T := S)
      (T' := S.map (MulAut.conj t.x₁).toMonoidHom) (X := X)
      hfr.ha ⟨szEquiv hfr⟩ hT hT' hne h₁' h₂'
    rwa [pCoreOf_sup_pCoreOf hfr.hF.1] at h
  have hgP1 : g ∈ P1 L1 L2 S := t.Gv_zero ▸ hg
  obtain ⟨l, hlL1, b, hbB, hglb⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (bigB_le_normalizer_of_hyp111 hfr.hF.1)).mp hgP1
  have hlXQ : l ∈ X ⊔ Q1 L1 L2 S := hgen (Subgroup.mem_sup_left hlL1)
  have hlQX : l ∈ Q1 L1 L2 S ⊔ X := by rwa [sup_comm] at hlXQ
  obtain ⟨q, hqQ1, m, hmX, hlqm⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hXQ1).mp hlQX
  have hmqQ : m⁻¹ * q * m ∈ Q1 L1 L2 S := by
    have hmN : m ∈ normalizer (Q1 L1 L2 S : Set G) := hXQ1 hmX
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (Q1 L1 L2 S : Set G)).inv_mem hmN) q).mp hqQ1
    simpa using h
  have hmqB : m⁻¹ * q * m ∈ bigB L1 L2 S := (hQ1S.trans hSB) hmqQ
  refine ⟨m, hmX, (m⁻¹ * q * m) * b, ?_, ?_⟩
  · rw [t.Gw_zero_one hfr.hF]
    exact (bigB L1 L2 S).mul_mem hmqB hbB
  · rw [hglb, hlqm]
    group

private theorem exists_mul_of_mem_Gv_one
    {a f : ℕ} (t : Track L1 L2 S)
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hXv : X ≤ t.Gv 1)
    (h₁ : ∀ x ∈ pCoreOf 2 (t.Gw 1 2), x ^ 2 ∈ t.Qv 1 → x ∈ X ⊔ t.Qv 1)
    (h₂ : ∀ x ∈ pCoreOf 2 (t.Gw 0 1), x ^ 2 ∈ t.Qv 1 → x ∈ X ⊔ t.Qv 1)
    {g : G} (hg : g ∈ t.Gv 1) :
    ∃ m ∈ X, ∃ s ∈ t.Gw 1 2, g = m * s := by
  classical
  let L := L2 ⊔ Q2 L1 L2 S
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
      (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.hF)
  have hSB : S ≤ bigB L1 L2 S :=
    (le_sup_left : S ≤ S ⊔ t.K).trans (le_of_eq t.sup_K_eq_bigB)
  have hXvP2 : X ≤ P2 L1 L2 S := t.Gv_one ▸ hXv
  have hXQ2 : X ≤ normalizer (Q2 L1 L2 S : Set G) :=
    hXvP2.trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hBL2 : bigB L1 L2 S ≤ normalizer (L2 : Set G) := by
    rw [bigB_comm]
    exact bigB_le_normalizer_of_hyp111 hfr.hF.1.symm
  have hP2L2 : P2 L1 L2 S ≤ normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hBL2
  have hT : IsSylowTwoOf S L := baseSylow_right hfr
  have hx2QN : t.x₂ ∈ normalizer (Q2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) t.track.x₂_mem
  have hx2N : t.x₂ ∈ normalizer (L : Set G) :=
    F1.le_normalizer_sup (X := Subgroup.zpowers t.x₂)
      (zpowers_le.mpr (hP2L2 t.track.x₂_mem)) (zpowers_le.mpr hx2QN) (mem_zpowers t.x₂)
  have hmapL : L.map (MulAut.conj t.x₂).toMonoidHom = L :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hx2N
  have hTmap : IsSylowTwoOf (S.map (MulAut.conj t.x₂).toMonoidHom) L := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₂) hT
    rwa [hmapL] at h
  have hT_eq : pCoreOf 2 (t.Gw 1 2) = S.map (MulAut.conj t.x₂).toMonoidHom := by
    have hw : t.Gw 1 2 = (t.Gw 0 1).map (MulAut.conj t.x₂).toMonoidHom := by
      have h := t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer 0 1
      simpa using h.symm
    rw [hw, pCoreOf_map_mulEquiv, t.pCoreOf_Gw_zero_one hfr]
  have hrelQ2 : (Q2 L1 L2 S).relIndex S = 2 ^ f := by
    have h := (t.relIndex_Qv_pCoreOf hfr 1).1
    rw [show (1 : ℤ) - 1 = 0 by norm_num, t.Qv_one, t.pCoreOf_Gw_zero_one hfr,
      if_neg Int.not_even_one] at h
    exact h
  have hne : S.map (MulAut.conj t.x₂).toMonoidHom ≠ S := by
    intro heq
    have hTle : S.map (MulAut.conj t.x₂).toMonoidHom ≤ t.Gw 1 2 := by
      rw [← hT_eq]
      exact pCoreOf_le 2 (t.Gw 1 2)
    have hS01 : S ≤ t.Gw 0 1 := by
      have h := pCoreOf_le 2 (t.Gw 0 1)
      rwa [t.pCoreOf_Gw_zero_one hfr] at h
    have hS02 : S ≤ t.Gw 0 2 := by
      intro x hx
      refine mem_win_iff.mpr fun i hi1 hi2 => ?_
      rcases (show i ≤ 1 ∨ i = 2 by omega) with h3 | h3
      · exact mem_win_iff.mp (hS01 hx) i hi1 h3
      · rw [h3]
        exact mem_win_iff.mp (hTle (heq.symm ▸ hx)) 2 (by omega) le_rfl
    have hSleQ : S ≤ Q2 L1 L2 S := by
      have h := t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1)
        (by norm_num) (by norm_num) hfr.hF.1.h1.pgroup hS02
      rwa [t.Qv_one] at h
    have h1 : (Q2 L1 L2 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSleQ
    rw [h1] at hrelQ2
    have hgt : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hfr.hf; omega)
    omega
  have hgen : L ≤ X ⊔ Q2 L1 L2 S := by
    have hTle : S.map (MulAut.conj t.x₂).toMonoidHom ≤ X ⊔ Q2 L1 L2 S := by
      intro x hx
      have hxR : x ∈ pCoreOf 2 (t.Gw 1 2) := by rw [hT_eq]; exact hx
      have hx2Q : x ^ 2 ∈ t.Qv 1 := by
        rw [t.Qv_one]
        obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hx
        have hy2 : y ^ 2 ∈ Q2 L1 L2 S := sq_mem_Q2_of_mem_S hfr hyS
        have h := (Subgroup.mem_normalizer_iff.mp hx2QN (y ^ 2)).mp hy2
        simpa [MulAut.conj_apply] using h
      have h := h₁ x hxR hx2Q
      rwa [t.Qv_one] at h
    have hT'le : S ≤ X ⊔ Q2 L1 L2 S := by
      intro y hy
      have hy2 : y ^ 2 ∈ t.Qv 1 := by
        rw [t.Qv_one]
        exact sq_mem_Q2_of_mem_S hfr hy
      have hy' : y ∈ pCoreOf 2 (t.Gw 0 1) := by
        rw [t.pCoreOf_Gw_zero_one hfr]
        exact hy
      have h := h₂ y hy' hy2
      rwa [t.Qv_one] at h
    have hL2q : IsL2Quot f (oTwoQuot ↥L) := by
      simpa [L] using str86_isL2Quot_u3H hfr.hF hfr.hL2
    have h := le_sup_pCoreOf_of_sylow_ne_of_l2 (L := L)
      (T := S.map (MulAut.conj t.x₂).toMonoidHom) (T' := S) (X := X)
      hfr.hf hL2q hTmap hT hne
      (by rwa [← str86_pCoreOf_u3H hfr.hF] at hTle)
      (by rwa [← str86_pCoreOf_u3H hfr.hF] at hT'le)
    rwa [str86_pCoreOf_u3H hfr.hF] at h
  have hL2map : L2.map (MulAut.conj t.x₂).toMonoidHom = L2 :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hP2L2 t.track.x₂_mem)
  have hB'eq : (bigB L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom = t.Gw 1 2 := by
    rw [← t.Gw_zero_one hfr.hF]
    have h := t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1
    simpa using h
  have hP2map : P2 L1 L2 S = (P2 L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom :=
    ((Subgroup.mem_normalizer_iff_map_conj_eq).mp
      (Subgroup.le_normalizer t.track.x₂_mem)).symm
  have hP2eq : P2 L1 L2 S = L2 ⊔ t.Gw 1 2 := by
    calc P2 L1 L2 S = (P2 L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom := hP2map
      _ = (L2 ⊔ bigB L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom := rfl
      _ = L2.map (MulAut.conj t.x₂).toMonoidHom ⊔
            (bigB L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom := Subgroup.map_sup ..
      _ = L2 ⊔ t.Gw 1 2 := by rw [hL2map, hB'eq]
  have hB'P2 : t.Gw 1 2 ≤ P2 L1 L2 S := by
    have h := win_le_qv (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      (x₁ := t.x₁) (x₂ := t.x₂) (a := 1) (b := 2) (i := 1) le_rfl (by norm_num)
    have h' : t.Gw 1 2 ≤ t.Gv 1 := h
    rwa [t.Gv_one] at h'
  have hB'N : t.Gw 1 2 ≤ normalizer (L2 : Set G) := hB'P2.trans hP2L2
  have hgP2 : g ∈ P2 L1 L2 S := t.Gv_one ▸ hg
  have hg2 : g ∈ L2 ⊔ t.Gw 1 2 := by rwa [hP2eq] at hgP2
  obtain ⟨l, hlL2, b, hbB', hglb⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hB'N).mp hg2
  have hlXQ : l ∈ X ⊔ Q2 L1 L2 S := hgen (Subgroup.mem_sup_left hlL2)
  have hlQX : l ∈ Q2 L1 L2 S ⊔ X := by rwa [sup_comm] at hlXQ
  obtain ⟨q, hqQ2, m, hmX, hlqm⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hXQ2).mp hlQX
  have hmqQ : m⁻¹ * q * m ∈ Q2 L1 L2 S := by
    have hmN : m ∈ normalizer (Q2 L1 L2 S : Set G) := hXQ2 hmX
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (Q2 L1 L2 S : Set G)).inv_mem hmN) q).mp hqQ2
    simpa using h
  have hQ2B' : Q2 L1 L2 S ≤ t.Gw 1 2 := by
    have h := (Qv_le_pCoreOf_Gw t hfr 1).trans (pCoreOf_le 2 (t.Gw 1 2))
    rwa [t.Qv_one] at h
  refine ⟨m, hmX, (m⁻¹ * q * m) * b, ?_, ?_⟩
  · exact (t.Gw 1 2).mul_mem (hQ2B' hmqQ) hbB'
  · rw [hglb, hlqm]
    group

private theorem mem_Gv_map_inv_of_mem {v e : ℤ} {f : G}
    (hGv : (t.Gv e).map (MulAut.conj f).toMonoidHom = t.Gv v) {x : G}
    (hx : x ∈ t.Gv v) : f⁻¹ * x * f ∈ t.Gv e := by
  have hxmap : x ∈ (t.Gv e).map (MulAut.conj f).toMonoidHom := hGv.symm ▸ hx
  have h := (mem_map_conj_iff (K := t.Gv e) (g := f)).mp hxmap
  simpa [MulAut.conj_apply] using h

private theorem transport_hyp {v e : ℤ} {R0 Rv : Subgroup G} {f : G} {X : Subgroup G}
    (hG : R0.map (MulAut.conj f).toMonoidHom = Rv)
    (hQ : (t.Qv e).map (MulAut.conj f).toMonoidHom = t.Qv v)
    (h : ∀ x ∈ pCoreOf 2 Rv, x ^ 2 ∈ t.Qv v → x ∈ X ⊔ t.Qv v) :
    ∀ x ∈ pCoreOf 2 R0, x ^ 2 ∈ t.Qv e →
      x ∈ X.map (MulAut.conj f⁻¹).toMonoidHom ⊔ t.Qv e := by
  intro x hxR hxQ
  exact mem_sup_map_inv_of_mem t hQ
    (h _ (mem_pCoreOf_map_of hG hxR) (sq_mem_Qv_map t hQ hxQ))

theorem exists_mul_of_mem_Gv
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G} (hXv : X ≤ t.Gv v)
    (h₁ : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v → x ∈ X ⊔ t.Qv v)
    (h₂ : ∀ x ∈ pCoreOf 2 (t.Gw (v - 1) v), x ^ 2 ∈ t.Qv v → x ∈ X ⊔ t.Qv v)
    {g : G} (hg : g ∈ t.Gv v) : ∃ m ∈ X, ∃ s ∈ t.Gw v (v + 1), g = m * s := by

  classical
  have hXQv : ¬ X ≤ t.Qv v := by
    intro hle
    have hroot : t.rootOmega v ≤ t.Qv v := by
      intro x hx
      have hx' := (mem_rootOmega_iff t hfr v).mp hx
      exact (sup_le hle le_rfl) (h₁ x hx'.1 hx'.2)
    have hrel1 : (t.Qv v).relIndex (t.rootOmega v) = 1 :=
      Subgroup.relIndex_eq_one.mpr hroot
    have hrel := relIndex_rootOmega t hfr v
    rw [hrel1] at hrel
    by_cases hve : Even v
    · rw [if_pos hve] at hrel
      have hb : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
      omega
    · rw [if_neg hve] at hrel
      have hb : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hfr.hf; omega)
      omega
  by_cases hv : Even v
  · obtain ⟨k, hk⟩ := hv
    let f : G := (t.x₂ * t.x₁) ^ k
    have h2k : 2 * k = v := by omega
    have hQ : (t.Qv 0).map (MulAut.conj f).toMonoidHom = t.Qv v := by
      change (qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ 0).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ v
      rw [map_qv_tau_pow (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S) 0 k]
      rw [show 0 + 2 * k = v by omega]
    have hGv : (t.Gv 0).map (MulAut.conj f).toMonoidHom = t.Gv v := by
      change (qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 0).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ v
      rw [map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 0 k]
      rw [show 0 + 2 * k = v by omega]
    have hG : (t.Gw 0 1).map (MulAut.conj f).toMonoidHom = t.Gw v (v + 1) := by
      change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 0 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ v (v + 1)
      rw [map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 0 1 k]
      rw [show 0 + 2 * k = v by omega, show 1 + 2 * k = v + 1 by omega]
    have hG2 : (t.Gw (-1) 0).map (MulAut.conj f).toMonoidHom = t.Gw (v - 1) v := by
      change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (-1) 0).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (v - 1) v
      rw [map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) (-1) 0 k]
      rw [show -1 + 2 * k = v - 1 by omega, show 0 + 2 * k = v by omega]
    let Y : Subgroup G := X.map (MulAut.conj f⁻¹).toMonoidHom
    have hYv : Y ≤ t.Gv 0 := by
      intro y hy
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hy
      simpa [MulAut.conj_apply] using mem_Gv_map_inv_of_mem t hGv (hXv hxX)
    have hYQ : ¬ Y ≤ t.Qv 0 := by
      intro hle
      apply hXQv
      intro x hx
      have hy : f⁻¹ * x * f ∈ Y := by
        have h := Subgroup.mem_map_of_mem (MulAut.conj f⁻¹).toMonoidHom hx
        simpa [Y, MulAut.conj_apply] using h
      have hyQ := hle hy
      have hxmap : x ∈ (t.Qv 0).map (MulAut.conj f).toMonoidHom :=
        (mem_map_conj_iff (K := t.Qv 0) (g := f)).mpr hyQ
      rwa [hQ] at hxmap
    have hY1 : ∀ x ∈ pCoreOf 2 (t.Gw 0 1), x ^ 2 ∈ t.Qv 0 →
        x ∈ Y ⊔ t.Qv 0 := by
      intro x hxR hxQ
      have h := transport_hyp t (v := v) (e := 0)
        (R0 := t.Gw 0 1) (Rv := t.Gw v (v + 1)) hG hQ h₁ x hxR hxQ
      simpa [Y] using h
    have hY2 : ∀ x ∈ pCoreOf 2 (t.Gw (-1) 0), x ^ 2 ∈ t.Qv 0 →
        x ∈ Y ⊔ t.Qv 0 := by
      intro x hxR hxQ
      have h := transport_hyp t (v := v) (e := 0)
        (R0 := t.Gw (-1) 0) (Rv := t.Gw (v - 1) v) hG2 hQ h₂ x hxR hxQ
      simpa [Y] using h
    have hg0 : f⁻¹ * g * f ∈ t.Gv 0 := mem_Gv_map_inv_of_mem t hGv hg
    obtain ⟨m, hmY, s, hs, hgs⟩ := exists_mul_of_mem_Gv_zero t hfr hYv hY1 hY2 hg0
    have hYX : Y.map (MulAut.conj f).toMonoidHom = X := by
      unfold Y
      exact CFSG.Timmesfeld.RankOne.map_conj_map_conj_inv X f
    have hmX : f * m * f⁻¹ ∈ X := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom hmY
      rwa [hYX] at h
    have hsG : f * s * f⁻¹ ∈ t.Gw v (v + 1) := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom hs
      rwa [hG] at h
    refine ⟨f * m * f⁻¹, hmX, f * s * f⁻¹, hsG, ?_⟩
    rw [show g = f * (f⁻¹ * g * f) * f⁻¹ by group, hgs]
    group
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hv
    let f : G := (t.x₂ * t.x₁) ^ k
    have h2k : 2 * k = v - 1 := by omega
    have hQ : (t.Qv 1).map (MulAut.conj f).toMonoidHom = t.Qv v := by
      change (qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ v
      rw [map_qv_tau_pow (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S) 1 k]
      rw [show 1 + 2 * k = v by omega]
    have hGv : (t.Gv 1).map (MulAut.conj f).toMonoidHom = t.Gv v := by
      change (qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ v
      rw [map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 1 k]
      rw [show 1 + 2 * k = v by omega]
    have hG : (t.Gw 1 2).map (MulAut.conj f).toMonoidHom = t.Gw v (v + 1) := by
      change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 1 2).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ v (v + 1)
      rw [map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 1 2 k]
      rw [show 1 + 2 * k = v by omega, show 2 + 2 * k = v + 1 by omega]
    have hG2 : (t.Gw 0 1).map (MulAut.conj f).toMonoidHom = t.Gw (v - 1) v := by
      change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 0 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (v - 1) v
      rw [map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) 0 1 k]
      rw [show 0 + 2 * k = v - 1 by omega, show 1 + 2 * k = v by omega]
    let Y : Subgroup G := X.map (MulAut.conj f⁻¹).toMonoidHom
    have hYv : Y ≤ t.Gv 1 := by
      intro y hy
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hy
      simpa [MulAut.conj_apply] using mem_Gv_map_inv_of_mem t hGv (hXv hxX)
    have hYQ : ¬ Y ≤ t.Qv 1 := by
      intro hle
      apply hXQv
      intro x hx
      have hy : f⁻¹ * x * f ∈ Y := by
        have h := Subgroup.mem_map_of_mem (MulAut.conj f⁻¹).toMonoidHom hx
        simpa [Y, MulAut.conj_apply] using h
      have hyQ := hle hy
      have hxmap : x ∈ (t.Qv 1).map (MulAut.conj f).toMonoidHom :=
        (mem_map_conj_iff (K := t.Qv 1) (g := f)).mpr hyQ
      rwa [hQ] at hxmap
    have hY1 : ∀ x ∈ pCoreOf 2 (t.Gw 1 2), x ^ 2 ∈ t.Qv 1 →
        x ∈ Y ⊔ t.Qv 1 := by
      intro x hxR hxQ
      have h := transport_hyp t (v := v) (e := 1)
        (R0 := t.Gw 1 2) (Rv := t.Gw v (v + 1)) hG hQ h₁ x hxR hxQ
      simpa [Y] using h
    have hY2 : ∀ x ∈ pCoreOf 2 (t.Gw 0 1), x ^ 2 ∈ t.Qv 1 →
        x ∈ Y ⊔ t.Qv 1 := by
      intro x hxR hxQ
      have h := transport_hyp t (v := v) (e := 1)
        (R0 := t.Gw 0 1) (Rv := t.Gw (v - 1) v) hG2 hQ h₂ x hxR hxQ
      simpa [Y] using h
    have hg1 : f⁻¹ * g * f ∈ t.Gv 1 := mem_Gv_map_inv_of_mem t hGv hg
    obtain ⟨m, hmY, s, hs, hgs⟩ := exists_mul_of_mem_Gv_one t hfr hYv hY1 hY2 hg1
    have hYX : Y.map (MulAut.conj f).toMonoidHom = X := by
      unfold Y
      exact CFSG.Timmesfeld.RankOne.map_conj_map_conj_inv X f
    have hmX : f * m * f⁻¹ ∈ X := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom hmY
      rwa [hYX] at h
    have hsG : f * s * f⁻¹ ∈ t.Gw v (v + 1) := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom hs
      rwa [hG] at h
    refine ⟨f * m * f⁻¹, hmX, f * s * f⁻¹, hsG, ?_⟩
    rw [show g = f * (f⁻¹ * g * f) * f⁻¹ by group, hgs]
    group

end Track

end CFSG.Quasithin.Stroth.Rq

end
