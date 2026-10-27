module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbOddM6
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeAbDefs

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem zpow_eq_one_or_eq_self_of_mul_self {a : G} (ha : a * a = 1) (n : ℤ) :
    a ^ n = 1 ∨ a ^ n = a := by
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact ha
  have e : a ^ n = a ^ (n % 2) := by
    have hn : n = n % 2 + 2 * (n / 2) := by omega
    conv_lhs => rw [hn]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [e, h, zpow_zero]
  · right
    rw [e, h, zpow_one]

theorem zpowers_eq_conjSub (g x : G) :
    Subgroup.zpowers x = conjSub g (Subgroup.zpowers (g⁻¹ * x * g)) := by
  rw [conjSub, MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem card_commutator_zpowers_le_relIndex {U V : Subgroup G} (hUV : U ≤ V)
    (hV : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (ha2 : a * a = 1) :
    Nat.card (⁅U, Subgroup.zpowers a⁆ : Subgroup G) ≤
      (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex V := by
  have hC : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hC, ← H13.A7.card_range_commutator_eq_relIndex hV ha]
  refine Nat.card_mono (Set.toFinite _) fun x hx => ?_
  rw [SetLike.mem_coe, Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, hu, y, hy, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases zpow_eq_one_or_eq_self_of_mul_self ha2 n with h | h
    · rw [h, commutatorElement_one_right]
      exact ⟨1, by simp⟩
    · rw [h, commutatorElement_def]
      exact ⟨⟨u, hUV hu⟩, rfl⟩
  | one => exact ⟨1, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨v, rfl⟩ := ihx
    obtain ⟨w, rfl⟩ := ihy
    refine ⟨v * w, ?_⟩
    show ((v * w : V) : G) * a * ((v * w : V) : G)⁻¹ * a⁻¹ =
      ((v : G) * a * (v : G)⁻¹ * a⁻¹) * ((w : G) * a * (w : G)⁻¹ * a⁻¹)
    rw [Subgroup.coe_mul]
    have hX : a * (v : G)⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp ha _).mp (V.inv_mem v.2)
    have hY : a * (w : G)⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp ha _).mp (V.inv_mem w.2)
    have h1 := hV _ hX _ w.2
    have h2 := hV _ hX _ hY
    calc (v : G) * w * a * ((v : G) * w)⁻¹ * a⁻¹ =
        v * w * ((a * (w : G)⁻¹ * a⁻¹) * (a * (v : G)⁻¹ * a⁻¹)) := by group
      _ = v * w * ((a * (v : G)⁻¹ * a⁻¹) * (a * (w : G)⁻¹ * a⁻¹)) := by rw [h2]
      _ = v * (w * (a * (v : G)⁻¹ * a⁻¹)) * (a * (w : G)⁻¹ * a⁻¹) := by group
      _ = v * ((a * (v : G)⁻¹ * a⁻¹) * w) * (a * (w : G)⁻¹ * a⁻¹) := by rw [h1]
      _ = ((v : G) * a * (v : G)⁻¹ * a⁻¹) * ((w : G) * a * (w : G)⁻¹ * a⁻¹) := by group
  | inv x _ ih =>
    obtain ⟨v, rfl⟩ := ih
    refine ⟨v⁻¹, ?_⟩
    show ((v⁻¹ : V) : G) * a * ((v⁻¹ : V) : G)⁻¹ * a⁻¹ =
      ((v : G) * a * (v : G)⁻¹ * a⁻¹)⁻¹
    rw [Subgroup.coe_inv, inv_inv]
    have hX : a * (v : G) * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp ha _).mp v.2
    have h1 := hV _ hX _ (V.inv_mem v.2)
    calc (v : G)⁻¹ * a * v * a⁻¹ = (v : G)⁻¹ * (a * v * a⁻¹) := by group
      _ = (a * v * a⁻¹) * (v : G)⁻¹ := h1.symm
      _ = ((v : G) * a * (v : G)⁻¹ * a⁻¹)⁻¹ := by group

theorem str86_commutator_z2_q1
    {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hO : Str86OddModule L1 L2 S m) : ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S := by
  obtain ⟨-, -, -, hQ3, -⟩ := hO
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro z hz q hq
    by_cases hq2 : q ∈ Q2 L1 L2 S
    · have hc : z * q = q * z := Subgroup.mem_centralizer_iff.mp (hQ2C hq2) z hz
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
      exact (Z1 L1 L2 S).one_mem
    · exact (hQ3 q (hQ1S hq) hq2).le
        (Subgroup.commutator_mem_commutator hz (Subgroup.mem_zpowers q))
  · obtain ⟨x, hx1, hx2⟩ : ∃ x ∈ Q1 L1 L2 S, x ∉ Q2 L1 L2 S := by
      by_contra hcon
      have hle : Q1 L1 L2 S ≤ Q2 L1 L2 S := fun x hx => by
        by_contra h
        exact hcon ⟨x, hx, h⟩
      have hsup := str86_pCoreOf_sup_pCoreOf hI.hF.toW hI.hSB
        (Or.inr ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩) hI.hm hI.hL2
      rw [sup_eq_right.mpr hle] at hsup
      have hr := str86_relIndex_q2_s hI.hF.toW hI.hSB hI.hm hI.hL2
      rw [hsup, Subgroup.relIndex_self] at hr
      have h4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hI.hm
      omega
    rw [← hQ3 x (hQ1S hx1) hx2]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hx1)

theorem str86_oddModule_edge
    {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hO : Str86OddModule L1 L2 S m) {γ δ : Str86Γ L1 L2 S} (hγ : vtype γ = true)
    (hδ : δ ∈ nbrs γ) :
    Nat.card (omegaOneCenterOf (pCoreOf 2 (stab γ))) = 2 ^ m ∧
      (∀ x ∈ pCoreOf 2 (stab γ ⊓ stab δ), x ∉ pCoreOf 2 (stab δ) →
        ⁅Vv (Z2 L1 L2 S) δ, Subgroup.zpowers x⁆ = omegaOneCenterOf (pCoreOf 2 (stab γ))) ∧
      ⁅Vv (Z2 L1 L2 S) δ, pCoreOf 2 (stab γ)⁆ = omegaOneCenterOf (pCoreOf 2 (stab γ)) := by
  have hZQ1 := str86_commutator_z2_q1 hI hO
  obtain ⟨-, -, hcard, hQ3, -⟩ := hO
  obtain ⟨h0, h1, hS0, hV0, -⟩ := str86_base_values hI
  obtain ⟨g, rfl, rfl⟩ := F112Crit.exists_edge_conj (str86_vtype_of_mem_nbrs hγ hδ)
    (show γ ∈ nbrs δ from (show (graph _ _ _).Adj γ δ from hδ).symm)
  obtain ⟨hQγ, hZγ, hSγδ, -, -⟩ := str86_vertex_smul hI g
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  obtain ⟨hQδ, -, -, hVδ, -⟩ := str86_vertex_smul hI g
    (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  have eS : pCoreOf 2 (stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
      stab (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) = S := by
    rw [inf_comm]
    exact hS0
  rw [hZγ, hQγ, hSγδ, hQδ, hVδ, eS, h1, h0, hV0]
  refine ⟨?_, fun x hx hxQ => ?_, ?_⟩
  · rw [CosetGeom.card_conjSub]
    exact hcard
  · rw [mem_conjSub] at hx hxQ
    rw [zpowers_eq_conjSub (g : G) x, conjSub_commutator, hQ3 _ hx hxQ]
  · rw [conjSub_commutator, hZQ1]

theorem str86_commutator_Vv_pCoreOf
    {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hO : Str86OddModule L1 L2 S m) (_hb3 : 3 ≤ str86CritB L1 L2 S) {γ : Str86Γ L1 L2 S}
    (hγ : vtype γ = true) :
    ⁅Vv (Z2 L1 L2 S) γ, pCoreOf 2 (stab γ)⁆ = omegaOneCenterOf (pCoreOf 2 (stab γ)) := by
  have hc := hI.critHypN
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hγ
  have hδ : g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ∈ nbrs γ := by
    rw [hg]
    exact (CosetGeom.smul_adj g).mpr CosetGeom.adj_γ₀_γ₁.symm
  have hN : stab γ ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (stab γ)) : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf _
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    have hVsup : Vv (Z2 L1 L2 S) γ = ⨆ δ : {δ // δ ∈ nbrs γ}, Vv (Z2 L1 L2 S) δ.1 :=
      le_antisymm (F112Crit.Vv_le_of_forall_mem_nbrs hγ fun δ hδ =>
          le_iSup_of_le (⟨δ, hδ⟩ : {δ // δ ∈ nbrs γ}) le_rfl)
        (iSup_le fun δ => F112Crit.Vv_le_Vv_of_mem_nbrs hγ δ.2)
    rw [hVsup] at hv
    refine (Subgroup.iSup_induction (fun δ : {δ // δ ∈ nbrs γ} => Vv (Z2 L1 L2 S) δ.1)
      (C := fun v => v ∈ stab γ ∧ ⁅v, x⁆ ∈ omegaOneCenterOf (pCoreOf 2 (stab γ))) hv
      (fun δ z hz => ?_) ⟨(stab γ).one_mem, ?_⟩ (fun v w hvw hww => ?_)).2
    · have hδt : vtype δ.1 = false := str86_vtype_of_mem_nbrs hγ δ.2
      have hγδ : γ ∈ nbrs δ.1 := (show (graph _ _ _).Adj γ δ.1 from δ.2).symm
      refine ⟨?_, ?_⟩
      · have hzQ : z ∈ pCoreOf 2 (stab δ.1) := by
          rw [hD41 _ hδt] at hz
          exact omegaOneCenterOf_le _ hz
        exact ((CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam δ.1).trans
          (CosetGeom.ballStab_le_stab_of_dist_le
            (CosetGeom.dist_eq_one_iff_adj.mpr hγδ).le)) hzQ
      · rw [← (str86_oddModule_edge hI hO hγ δ.2).2.2]
        exact Subgroup.commutator_mem_commutator hz hx
    · rw [commutatorElement_one_left]
      exact Subgroup.one_mem _
    · refine ⟨(stab γ).mul_mem hvw.1 hww.1, ?_⟩
      have e : ⁅v * w, x⁆ = v * ⁅w, x⁆ * v⁻¹ * ⁅v, x⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hN hvw.1) _).mp hww.2) hvw.2
  · calc omegaOneCenterOf (pCoreOf 2 (stab γ)) =
        ⁅Vv (Z2 L1 L2 S) (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)),
          pCoreOf 2 (stab γ)⁆ := (str86_oddModule_edge hI hO hγ hδ).2.2.symm
      _ ≤ ⁅Vv (Z2 L1 L2 S) γ, pCoreOf 2 (stab γ)⁆ :=
        Subgroup.commutator_mono (F112Crit.Vv_le_Vv_of_mem_nbrs hγ hδ) le_rfl

theorem false_of_two_pow_le_of_two_mul_le {k m : ℕ} (hk : 1 ≤ k) (hkm : 2 * k ≤ m)
    (h : 2 ^ m ≤ 2 ^ k) : False := by
  have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hkm
  have h2 : 2 ^ k < 2 ^ (2 * k) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem str86_critPath_odd_O4
    {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hM6 : Str86UnitaryM6)
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    ⁅Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))),
        Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ ≠ ⊥ ∧
      ⁅Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 1)),
        Vv (Z2 L1 L2 S) (lam 1)⁆ ≠ ⊥ := by
  have hc := hI.critHypN
  obtain ⟨hO2a, hO2b⟩ := str86_critPath_odd_O2 hM6 hI hP hodd hb3
  obtain ⟨-, hO12, -, -, hEb, -, -, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨-, hF2, hF3, -⟩ := str86_critPath_odd_F4 hI hP hodd hb3
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨hv1, -, -, hvb, hn01, -, -, hnb', -⟩ := hP.odd_shape hI hodd hb3
  have hk1 : 1 ≤ k := by have := hI.hk; omega
  refine ⟨fun hbot => ?_, fun hbot => ?_⟩
  · by_cases hVQ : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))
    ·
      have hA'C := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hZβ : Vv (Z2 L1 L2 S) (lam 0) ≤ Vv (Z2 L1 L2 S) (lam 1) :=
        F112Crit.Vv_le_Vv_of_mem_nbrs hv1 hn01
      have hVQβ : ¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 0)) := by
        intro hle
        refine hP.critical (le_inf hZβ ?_ |>.trans hF2)
        rw [Subgroup.le_centralizer_iff]
        refine hle.trans ?_
        rw [hD41 _ hP.linear]
        exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf _
      obtain ⟨x, hxV, hxQ⟩ := SetLike.not_le_iff_exists.mp hVQβ
      have hxS : x ∈ pCoreOf 2 (stab (lam 1) ⊓ stab (lam 0)) :=
        str86_pCoreOf_le_pCoreOf_inf hI hn01 (hVQ hxV)
      have hx2 : x * x = 1 := by
        rw [← pow_two]
        exact hEb.2 x hxV
      have hOM := str86_oddModule_edge hI hO hv1 hn01
      have hZβe : IsElemAbelian 2 (Vv (Z2 L1 L2 S) (lam 0)) := by
        rw [hD41 _ hP.linear]
        exact SmithC27.isElemAbelian_omegaOneCenterOf _
      have hZβc : ∀ v ∈ Vv (Z2 L1 L2 S) (lam 0), ∀ w ∈ Vv (Z2 L1 L2 S) (lam 0), v * w = w * v :=
        fun v hv w hw => congrArg Subtype.val (hZβe.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
      have hxN : x ∈ Subgroup.normalizer (Vv (Z2 L1 L2 S) (lam 0) : Set G) :=
        CosetGeom.stab_le_normalizer_Vv hc.normalizes _ (pCoreOf_le 2 _ hxS).2
      have hcnt := card_commutator_zpowers_le_relIndex le_rfl hZβc hxN hx2
      rw [(hOM.2.1 x hxS hxQ), hOM.1] at hcnt
      have hCx : Vv (Z2 L1 L2 S) (lam 0) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) ≤
          Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
        refine (le_inf (inf_le_left.trans hZβ) inf_le_right).trans (hA'C.trans ?_)
        exact Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hxV)
      have hZβS : Vv (Z2 L1 L2 S) (lam 0) ≤
          pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab (lam (str86CritB L1 L2 S - 1))) := by
        rw [inf_comm]
        exact hZβ.trans (hO12.trans (str86_pCoreOf_le_pCoreOf_inf hI hnb'))
      have hU1 := (str86_edge_facts hI hvb (show lam (str86CritB L1 L2 S - 1) ∈
        nbrs (lam (str86CritB L1 L2 S)) from (show (graph _ _ _).Adj
          (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) from hnb').symm)).2.2.2.2.2.2
        _ hZβe hZβS
      have h' := Subgroup.relIndex_le_of_le_left (L := Vv (Z2 L1 L2 S) (lam 0)) hCx
        (D15Proof.relIndex_ne_zero _ _)
      exact false_of_two_pow_le_of_two_mul_le hk1 hkm ((hcnt.trans h').trans hU1)
    · refine (hO2b hVQ).ne' (le_antisymm (le_inf inf_le_left ?_) (le_inf inf_le_left hF2))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  · refine hO2a.ne' (le_antisymm (le_inf inf_le_left ?_) (le_inf inf_le_left hF3))
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem str86_critB_ne_three_of
    {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hM6 : Str86UnitaryM6) (hW : Str86LemmaW)
    (hmod : Str86OddModuleOf) (hI : Str86AbHyp L1 L2 S k m F) : str86CritB L1 L2 S ≠ 3 := by
  intro hb
  have hc := hI.critHypN
  have hodd : Odd (str86CritB L1 L2 S) := by rw [hb]; decide
  have hb3 : 3 ≤ str86CritB L1 L2 S := hb.ge
  have hkm := str86_two_mul_le_of_critB_odd hM6 hW hI hodd hb3
  obtain ⟨-, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨-, -, hab, -⟩ := str86_Vv_abelian hI
  have hO : Str86OddModule L1 L2 S m := hmod G L1 L2 S k m F hI.hF hI.hSB hI.hk hI.hFc hI.hU3
    hI.hB2 hI.hL2 hkm hI.hZI (hZQ (by omega)) (hab hb3)
  obtain ⟨lam, hP, -, -⟩ := str86_exists_critPath hI
  obtain ⟨-, -, -, hE1, hEb, -, -, hO18⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨hv1, hv2, -, hvb, -, -, hn21, hnb', -⟩ := hP.odd_shape hI hodd hb3
  have hk1 : 1 ≤ k := by have := hI.hk; omega
  have h21 : str86CritB L1 L2 S - 1 = 2 := by omega
  rw [h21] at hnb'
  have hVQα := str86_commutator_Vv_pCoreOf hI hO hb3 hv1
  have hVQα' := str86_commutator_Vv_pCoreOf hI hO hb3 hvb
  have hne : lam 1 ≠ lam (str86CritB L1 L2 S) := hP.isGeo.ne (by omega) le_rfl
  have hZZ := (str86_graph_F1 hI).1 (lam 2) (lam 1) (lam (str86CritB L1 L2 S)) hv2 hn21 hnb' hne
  have hAB : ⁅Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))),
      Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 1))⁆ = ⊥ := by
    rw [← le_bot_iff, ← hZZ]
    refine le_inf ?_ ?_
    · rw [← hVQα]
      exact Subgroup.commutator_mono inf_le_left inf_le_right
    · rw [← hVQα', Subgroup.commutator_comm]
      exact Subgroup.commutator_mono inf_le_left inf_le_right
  have hO4 := (str86_critPath_odd_O4 hM6 hI hO hkm hP hodd hb3).1
  by_cases hVQ : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))
  · rw [inf_eq_left.mpr hVQ] at hAB
    exact hO4 hAB
  ·
    obtain ⟨a, haA, haC⟩ := SetLike.not_le_iff_exists.mp
      (mt Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hO4)
    obtain ⟨μ, hμ, hμa⟩ : ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)),
        ¬ Vv (Z2 L1 L2 S) μ ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) :
          Set G) := by
      by_contra hcon
      apply haC
      rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff]
      refine F112Crit.Vv_le_of_forall_mem_nbrs hvb fun μ hμ => ?_
      by_contra h
      exact hcon ⟨μ, hμ, h⟩
    have hvμ : vtype μ = false := str86_vtype_of_mem_nbrs hvb hμ
    have haQμ : a ∉ pCoreOf 2 (stab μ) := by
      intro haμ
      apply hμa
      rw [Subgroup.le_centralizer_iff]
      refine (Subgroup.zpowers_le.mpr haμ).trans ?_
      rw [hD41 μ hvμ]
      exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf _
    have haS : a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab μ) :=
      str86_pCoreOf_le_pCoreOf_inf hI hμ (Subgroup.mem_inf.mp haA).2
    have hOM := str86_oddModule_edge hI hO hvb hμ
    have ha2 : a * a = 1 := by
      rw [← pow_two]
      exact hE1.2 a (Subgroup.mem_inf.mp haA).1
    have hVbc : ∀ v ∈ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)),
        ∀ w ∈ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)), v * w = w * v :=
      fun v hv w hw => congrArg Subtype.val (hEb.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
    have haN : a ∈ Subgroup.normalizer (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) : Set G) :=
      CosetGeom.stab_le_normalizer_Vv hc.normalizes _
        (pCoreOf_le 2 _ (Subgroup.mem_inf.mp haA).2)
    have hcnt := card_commutator_zpowers_le_relIndex
      (F112Crit.Vv_le_Vv_of_mem_nbrs hvb hμ) hVbc haN ha2
    rw [hOM.2.1 a haS haQμ, hOM.1] at hcnt
    have hBC : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 1)) ≤
        Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      have h' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB
      rw [Subgroup.le_centralizer_iff] at h'
      exact h'.trans (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr haA))
    have h' := Subgroup.relIndex_le_of_le_left
      (L := Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))) hBC (D15Proof.relIndex_ne_zero _ _)
    exact false_of_two_pow_le_of_two_mul_le hk1 hkm ((hcnt.trans h').trans hO18)

theorem str86CritNot3_of
    (hM6 : Str86UnitaryM6)
    (hW : Str86LemmaW) (hmod : Str86OddModuleOf) : Str86CritNot3 := by
  intro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI _hZ
  obtain ⟨k, m, F, _, _, hI⟩ := str86AbHyp_exists hF hSB h1 hB2 h2 hZI
  exact str86_critB_ne_three_of hM6 hW hmod hI

end CFSG.Quasithin.Stroth

end
