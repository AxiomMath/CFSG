module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Base

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) : A ≤ normalizer (B : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  refine ⟨h a ha b, fun hb => ?_⟩
  have := h a⁻¹ (inv_mem ha) _ hb
  simpa [mul_assoc] using this

variable [Finite G]

theorem qrc_short_generated_residual_Sylow_core_has_exact_whole_action_kernel
    {H T N R P : Subgroup G} (hH : CharTwo H) (hT : IsSylowTwoOf T H) (hNH : N ≤ H)
    (hNn : H ≤ normalizer (N : Set G)) (hHNT : N ⊔ T = H) (hNno : NoPQuotient 2 N)
    (hR1 : R ≠ ⊥) (hRT : R ≤ T) (hRTn : T ≤ normalizer (R : Set G))
    (hRsyl : IsSylowTwoOf R (N ⊔ R)) (hRP : R ≤ P) (hPNR : P ≤ N ⊔ R) (hHP : P ⊔ T = H)
    {s : ℕ} (hs : 1 ≤ s) (Y : Fin s → Subgroup G) (hY : ∀ i, IsBlock2 P (Y i))
    (hgen : R ⊔ ⨆ i, Y i = P) :
    let Q := blockQ (N ⊔ R)
    let P₀ := blockQ H
    let U := ⁅Q, N⁆
    N = ⨆ i, conjJoin T (Y i) ∧ Q = P₀ ⊓ (N ⊔ R) ∧ Q ≠ ⊥ ∧
      U ≠ ⊥ ∧ IsElemAbelian 2 U ∧ H ≤ normalizer (U : Set G) ∧
      U ≤ centerTorsion 2 Q ∧ centerTorsion 2 Q ≤ R ∧ ⁅U, N⁆ = U ∧
      H ⊓ centralizer (U : Set G) = P₀ ∧ (N ⊔ R) ⊓ centralizer (U : Set G) = Q ∧
      R ⊓ centralizer (U : Set G) = Q ∧ IsTwoReducedIn H U ∧
      ∀ i, ∀ t ∈ T, ⁅Q, CFSG.conjugate (Y i) t⁆ = blockU (CFSG.conjugate (Y i) t) ∧
        blockU (CFSG.conjugate (Y i) t) ≤ U ∧
        P₀ ≤ normalizer ((CFSG.conjugate (Y i) t : Subgroup G) : Set G) ∧
        P₀ ≤ centralizer (blockU (CFSG.conjugate (Y i) t) : Set G) := by
  intro Q P₀ U
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.1
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hR2 : IsPGroup 2 R := hRsyl.isPGroup
  have hRH : R ≤ H := hRT.trans hTH
  have hNRH : N ⊔ R ≤ H := sup_le hNH hRH
  have hTN : T ≤ normalizer (N : Set G) := fun t ht => hNn (hTH ht)
  have hRN : R ≤ normalizer (N : Set G) := fun r hr => hNn (hRH hr)
  have hHNR : H ≤ normalizer ((N ⊔ R : Subgroup G) : Set G) := by
    rw [← hHNT]
    exact sup_le (fun n hn => le_normalizer (mem_sup_left hn))
      fun t ht => C1.mem_normalizer_sup (hTN ht) (hRTn ht)
  have hNRchar : CharTwo (N ⊔ R) :=
    CharTwo.of_normal hH hNRH ((Subgroup.normal_subgroupOf_iff_le_normalizer hNRH).2 hHNR)
  obtain ⟨hNeq, hU1, hUea, hHU, hUW, hUN⟩ := normal_Sylow_part_block_centrality hT hNH hNn
    hHNT hNno hRT hRTn hRsyl hNRchar hRP hPNR hHP hs Y hY hgen
  have hQ2 : IsPGroup 2 Q := C1.blockQ_isPGroup _
  have hQNR : Q ≤ N ⊔ R := C1.blockQ_le _
  have hQR : Q ≤ R := hRsyl.pCoreOf_le
  have hHQ : H ≤ normalizer (Q : Set G) := fun h hh => C1.mem_normalizer_blockQ (hHNR hh)
  have hQP₀ : Q ≤ P₀ := C1.le_pCoreOf_of_normalized (hQNR.trans hNRH) hHQ hQ2
  have hP₀2 : IsPGroup 2 P₀ := C1.blockQ_isPGroup H
  have hP₀H : P₀ ≤ H := C1.blockQ_le H
  have hHP₀ : H ≤ normalizer (P₀ : Set G) := C1.le_normalizer_blockQ H
  have hQeq : Q = P₀ ⊓ (N ⊔ R) := le_antisymm (le_inf hQP₀ hQNR)
    (C1.le_pCoreOf_of_normalized inf_le_right
      (fun x hx => C5.mem_normalizer_inf (hHP₀ (hNRH hx)) (le_normalizer hx))
      (hP₀2.to_le inf_le_left))
  have hQ1 : Q ≠ ⊥ := by
    intro hQb
    apply hR1
    have hc : N ⊔ R ≤ Q := by
      intro x hx
      refine hNRchar ⟨hx, ?_⟩
      show x ∈ centralizer ((pCoreOf 2 (N ⊔ R) : Subgroup G) : Set G)
      rw [mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Q := hh
      rw [hQb, mem_bot] at hh'
      rw [hh', one_mul, mul_one]
    rw [eq_bot_iff, ← hQb]
    exact le_sup_right.trans hc
  have hQU : ∀ q ∈ Q, ∀ u ∈ U, q * u = u * q := fun q hq u hu =>
    (mem_centerTorsion_iff.1 (hUW hu)).2.1 q hq
  have hUQ : U ≤ Q := hUW.trans (centerTorsion_le 2 Q)
  have hYN : ∀ i, Y i ≤ N := fun i => le_of_noPQuotient (hY i).1.1
    fun y hy => exists_pow_mem_of_mem_sup_pGroup hR2 hRN (hPNR ((hY i).2.1 hy))
  have hP₀N : ∀ x ∈ P₀, ∀ a ∈ N, x⁻¹ * a * x * a⁻¹ ∈ Q := by
    intro x hx a ha
    rw [hQeq]
    refine ⟨?_, ?_⟩
    · have h1 : a * x * a⁻¹ ∈ P₀ := (mem_normalizer_iff.1 (hHP₀ (hNH ha)) x).1 hx
      have e : x⁻¹ * a * x * a⁻¹ = x⁻¹ * (a * x * a⁻¹) := by group
      rw [e]
      exact P₀.mul_mem (P₀.inv_mem hx) h1
    · have h1 : x⁻¹ * a * x⁻¹⁻¹ ∈ N := (mem_normalizer_iff.1 (hNn (hP₀H (P₀.inv_mem hx))) a).1 ha
      rw [inv_inv] at h1
      exact mem_sup_left (N.mul_mem h1 (N.inv_mem ha))
  have hP₀N' : ∀ x ∈ P₀, ∀ a ∈ N, x * a * x⁻¹ * a⁻¹ ∈ Q := fun x hx a ha => by
    have := hP₀N x⁻¹ (P₀.inv_mem hx) a ha
    rwa [inv_inv] at this
  have hmap : ∀ i, ∀ g ∈ T,
      ⁅Q, (Y i).map (MulAut.conj g).toMonoidHom⁆ = blockU ((Y i).map (MulAut.conj g).toMonoidHom) ∧
      blockU ((Y i).map (MulAut.conj g).toMonoidHom) ≤ U ∧
      P₀ ≤ normalizer (((Y i).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      P₀ ≤ centralizer (blockU ((Y i).map (MulAut.conj g).toMonoidHom) : Set G) ∧
      (Y i).map (MulAut.conj g).toMonoidHom ≤ N := by
    intro i g hg
    set Y' := (Y i).map (MulAut.conj g).toMonoidHom with hY'def
    have hblk : IsBlock2 (P.map (MulAut.conj g).toMonoidHom) Y' := isBlock2_map_conj (hY i) g
    have hRP' : R ≤ P.map (MulAut.conj g).toMonoidHom := by
      intro r hr
      refine ⟨g⁻¹ * r * g, hRP ?_, ?_⟩
      · have := (mem_normalizer_iff.mp (hRTn (T.inv_mem hg)) r).mp hr
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hP'NR : P.map (MulAut.conj g).toMonoidHom ≤ N ⊔ R := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (mem_normalizer_iff.mp (hHNR (hTH hg)) y).mp (hPNR hy)
    obtain ⟨-, hQY, -⟩ := full_Sylow_short_core_propagation hNRchar hRsyl hRP' hP'NR hblk
    have hY'N : Y' ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (mem_normalizer_iff.mp (hTN hg) y).mp (hYN i hy)
    have hUYU : blockU Y' ≤ U := hQY ▸ commutator_mono le_rfl hY'N
    have hUYY : blockU Y' ≤ Y' := blockU_le_self_of_isShort2 hblk.1
    have hQY' : Q ≤ normalizer (Y' : Set G) := le_normalizer_of_forall_conj_mem fun q hq y hy => by
      have h1 : ⁅q, y⁆ ∈ blockU Y' := hQY ▸ commutator_mem_commutator hq hy
      have e : q * y * q⁻¹ = ⁅q, y⁆ * y := by rw [commutatorElement_def]; group
      rw [e]
      exact Y'.mul_mem (hUYY h1) hy
    have hP₀Y' : P₀ ≤ normalizer (Y' : Set G) := by
      refine le_normalizer_of_forall_conj_mem fun x hx y hy => ?_
      have hle : Y'.map (MulAut.conj x).toMonoidHom ≤ Y' := by
        refine le_of_noPQuotient (isBlock2_map_conj hblk x).1.1 fun z hz => ?_
        obtain ⟨y', hy', rfl⟩ := hz
        refine exists_pow_mem_of_mem_sup_pGroup hQ2 hQY' ?_
        have hc : x * y' * x⁻¹ * y'⁻¹ ∈ Q := hP₀N' x hx y' (hY'N hy')
        have e : (MulAut.conj x).toMonoidHom y' = (x * y' * x⁻¹ * y'⁻¹) * y' := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hy')
      have := hle ⟨y, hy, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    have hP₀UY : P₀ ≤ centralizer (blockU Y' : Set G) := by
      have h := C1.inf_centralizer_blockU_eq hblk.1 (le_sup_left : Y' ≤ Y' ⊔ P₀)
        (sup_le le_normalizer hP₀Y') fun g hg => exists_pow_mem_of_mem_sup_pGroup hP₀2 hP₀Y' hg
      have hP₀O : P₀ ≤ pCoreOf 2 (Y' ⊔ P₀) := C1.le_pCoreOf_of_normalized le_sup_right
        (sup_le (fun y hy => hHP₀ (hNH (hY'N hy))) fun x hx => le_normalizer hx) hP₀2
      rw [← h] at hP₀O
      exact fun x hx => (hP₀O hx).2
    exact ⟨hQY, hUYU, hP₀Y', hP₀UY, hY'N⟩
  have hP₀U : P₀ ≤ centralizer (U : Set G) := by
    intro x hx
    have hconjU : ∀ a ∈ N, ∀ w ∈ U, x * w = w * x → x * (a * w * a⁻¹) = a * w * a⁻¹ * x := by
      intro a ha w hw hxw
      have hc : x⁻¹ * a * x * a⁻¹ ∈ Q := hP₀N x hx a ha
      have hw' : a * w * a⁻¹ ∈ U := (mem_normalizer_iff.1 (hHU (hNH ha)) w).1 hw
      have h1 := hQU _ hc _ hw'
      have h2 : (x * (x⁻¹ * a * x * a⁻¹)) * (a * w * a⁻¹) =
          (a * w * a⁻¹) * (x * (x⁻¹ * a * x * a⁻¹)) := by
        calc (x * (x⁻¹ * a * x * a⁻¹)) * (a * w * a⁻¹) = a * (x * w) * a⁻¹ := by group
          _ = a * (w * x) * a⁻¹ := by rw [hxw]
          _ = (a * w * a⁻¹) * (x * (x⁻¹ * a * x * a⁻¹)) := by group
      have h3 : x * (a * w * a⁻¹) * (x⁻¹ * a * x * a⁻¹) =
          a * w * a⁻¹ * x * (x⁻¹ * a * x * a⁻¹) := by
        calc x * (a * w * a⁻¹) * (x⁻¹ * a * x * a⁻¹) =
              x * ((a * w * a⁻¹) * (x⁻¹ * a * x * a⁻¹)) := mul_assoc _ _ _
          _ = x * ((x⁻¹ * a * x * a⁻¹) * (a * w * a⁻¹)) := by rw [h1]
          _ = (x * (x⁻¹ * a * x * a⁻¹)) * (a * w * a⁻¹) := (mul_assoc _ _ _).symm
          _ = (a * w * a⁻¹) * (x * (x⁻¹ * a * x * a⁻¹)) := h2
          _ = a * w * a⁻¹ * x * (x⁻¹ * a * x * a⁻¹) := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    let S : Subgroup G :=
      { carrier := {n | n ∈ N ∧ ∀ q ∈ Q, x * ⁅q, n⁆ = ⁅q, n⁆ * x}
        one_mem' := ⟨N.one_mem, fun q _ => by rw [commutatorElement_one_right, mul_one, one_mul]⟩
        mul_mem' := by
          rintro a b ⟨ha, hag⟩ ⟨hb, hbg⟩
          refine ⟨N.mul_mem ha hb, fun q hq => ?_⟩
          have e : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
            simp only [commutatorElement_def]
            group
          have h2 := hconjU a ha _ (commutator_mem_commutator hq hb) (hbg q hq)
          rw [e, ← mul_assoc, hag q hq, mul_assoc, h2, ← mul_assoc]
        inv_mem' := by
          rintro a ⟨ha, hag⟩
          refine ⟨N.inv_mem ha, fun q hq => ?_⟩
          have e : ⁅q, a⁻¹⁆ = a⁻¹ * (⁅q, a⁆)⁻¹ * a⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          have hx' : x * (⁅q, a⁆)⁻¹ = (⁅q, a⁆)⁻¹ * x := by
            have h := hag q hq
            calc x * (⁅q, a⁆)⁻¹ = (⁅q, a⁆)⁻¹ * (⁅q, a⁆ * x) * (⁅q, a⁆)⁻¹ := by group
              _ = (⁅q, a⁆)⁻¹ * (x * ⁅q, a⁆) * (⁅q, a⁆)⁻¹ := by rw [h]
              _ = (⁅q, a⁆)⁻¹ * x := by group
          rw [e]
          exact hconjU a⁻¹ (N.inv_mem ha) _ (U.inv_mem (commutator_mem_commutator hq ha)) hx' }
    have hNS : N ≤ S := by
      intro n hn
      rw [hNeq] at hn
      refine (iSup_le fun i => iSup_le fun t => ?_ : ⨆ i, conjJoin T (Y i) ≤ S) hn
      intro y hy
      obtain ⟨hQY, -, -, hcent, hYN'⟩ := hmap i t t.2
      refine ⟨hYN' hy, fun q hq => ?_⟩
      have h1 : ⁅q, y⁆ ∈ blockU ((Y i).map (MulAut.conj (t : G)).toMonoidHom) :=
        hQY ▸ commutator_mem_commutator hq hy
      exact (mem_centralizer_iff.1 (hcent hx) _ h1).symm
    have hUc : U ≤ centralizer ({x} : Set G) := by
      show ⁅Q, N⁆ ≤ _
      rw [commutator_le]
      intro q hq n hn
      rw [mem_centralizer_singleton_iff]
      exact ((hNS hn).2 q hq).symm
    rw [mem_centralizer_iff]
    intro u hu
    exact mem_centralizer_singleton_iff.1 (hUc hu)
  have hCU : H ⊓ centralizer (U : Set G) = P₀ := by
    refine le_antisymm ?_ (le_inf hP₀H hP₀U)
    refine C1.le_pCoreOf_of_normalized inf_le_left
      (fun h hh => C5.mem_normalizer_inf (le_normalizer hh)
        (C5.mem_normalizer_centralizer (hHU hh)))
      (isPGroup_two_of_forall_odd fun c hc hodd => ?_)
    have hcN : c ∈ N := Setup.Wreath.mem_of_odd_of_sup_eq hNn hTH hT2 hHNT hc.1 hodd
    have hcQ : ∀ x ∈ Q, c * x = x * c :=
      Setup.Wreath.centralizes_of_odd_trivial_factors hQ2 hUQ (fun q hq => hHU (hQNR.trans hNRH hq))
        (hHQ hc.1) hodd (fun u hu => (mem_centralizer_iff.1 hc.2 u hu).symm) fun x hx => by
          have h := commutator_mem_commutator (Q.inv_mem hx) hcN
          rw [commutatorElement_def, inv_inv] at h
          have e : x⁻¹ * (c * x * c⁻¹) = x⁻¹ * c * x * c⁻¹ := by group
          rw [e]
          exact h
    have hcQ' : c ∈ Q := hNRchar ⟨mem_sup_left hcN, mem_centralizer_iff.2 fun x hx =>
      (hcQ x hx).symm⟩
    exact eq_one_of_isPGroup_of_odd hQ2 hcQ' hodd
  have hNRU : (N ⊔ R) ⊓ centralizer (U : Set G) = Q := by
    rw [← inf_eq_left.2 hNRH, inf_assoc, hCU, inf_comm, ← hQeq]
  have hRU : R ⊓ centralizer (U : Set G) = Q := by
    refine le_antisymm ?_ (le_inf hQR (hQP₀.trans hP₀U))
    rw [← hNRU]
    exact inf_le_inf_right _ le_sup_right
  have hred : IsTwoReducedIn H U := by
    refine ⟨hUQ.trans (hQNR.trans hNRH), hHU, hUea, fun D hDH hHD hD => ?_⟩
    have hD2 : IsPGroup 2 D := by
      intro d
      obtain ⟨k, hk⟩ := hD d d.2
      have hkP : (d : G) ^ 2 ^ k ∈ P₀ := by
        rw [← hCU]
        exact ⟨H.pow_mem (hDH d.2) _, hk⟩
      obtain ⟨m, hm⟩ := C1.exists_pow_eq_one_of_isPGroup hP₀2 hkP
      refine ⟨k + m, Subtype.ext ?_⟩
      rw [coe_pow, pow_add, pow_mul, hm, coe_one]
    exact (C1.le_pCoreOf_of_normalized hDH hHD hD2).trans hP₀U
  refine ⟨hNeq, hQeq, hQ1, hU1, hUea, hHU, hUW, (centerTorsion_le 2 Q).trans hQR, hUN, hCU, hNRU,
    hRU, hred, fun i t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := hmap i t⁻¹ (T.inv_mem ht)
  exact ⟨h1, h2, h3, h4⟩

end CFSG.Quasithin.H13.QRC
