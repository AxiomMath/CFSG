module

import CFSG.Walter.W67.W2Basic
import CFSG.Walter.W67.Prop23
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
public import CFSG.Walter.W67.Interface
import CFSG.Walter.W67.Lemma22

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem exists_conj_J_of_commutator
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hq : 3 < h.q) : ∃ y ∈ commutator G, ∃ t ∈ fr.T, y * t * y⁻¹ = h.J := by
  have hKD : h.K ≤ commutator G :=
    calc h.K = ⁅h.K, h.K⁆ := (PSL2Sub.commutator_eq h.iso h.f_pos hq).symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (commutator_def G).symm
  set D := commutator G
  have hDn : D.Normal := inferInstance
  obtain ⟨z, hzK, -, hzN, hzC⟩ :=
    PSL2Sub.exists_three h.iso h.odd_p h.f_pos h.mod_eight fr.T_le_K fr.isKleinFour_T
  obtain ⟨t, htT, hzt⟩ : ∃ t ∈ fr.T, z * t * z⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * z = (z * x * z⁻¹) * z := by rw [hcon x hx]
      _ = z * x := by group
  have ht1 : t ≠ 1 := fun h1 => hzt (by rw [h1]; group)
  obtain ⟨n₀, hn₀, hn₀J⟩ :=
    fr.exists_conj_of_mem_S hidx fr.J_mem h.J_ne_one (fr.T_le_S htT) ht1
  set NS := Subgroup.normalizer ((fr.S : Subgroup G) : Set G)
  have hzNS : z ∈ NS := by
    have : z ∈ h.H ⊓ Subgroup.normalizer (fr.T : Set G) := ⟨h.K_le_H hzK, hzN⟩
    rw [← fr.normalizer_S_inf_H] at this
    exact this.1
  set w := n₀⁻¹ * z * n₀
  have hwD : w ∈ D := by
    have := hDn.conj_mem z (hKD hzK) n₀⁻¹
    simpa [w] using this
  have hwNS : w ∈ NS := NS.mul_mem (NS.mul_mem (NS.inv_mem hn₀) hzNS) hn₀
  have hwH : w ∉ h.H := by
    intro hwH
    apply hzt
    have h1 : w * h.J * w⁻¹ = h.J := by rw [h.commute_J hwH, mul_inv_cancel_right]
    have h2 : z * (n₀ * h.J * n₀⁻¹) * z⁻¹ = n₀ * h.J * n₀⁻¹ := by
      calc z * (n₀ * h.J * n₀⁻¹) * z⁻¹ = n₀ * (w * h.J * w⁻¹) * n₀⁻¹ := by simp only [w]; group
        _ = n₀ * h.J * n₀⁻¹ := by rw [h1]
    rwa [hn₀J] at h2
  set St := NS ⊓ h.H
  set N' := NS ⊓ D
  have h7 := fr.relIndex_normalizer_S_inf_H hidx
  have hmul := Subgroup.relIndex_mul_relIndex St (N' ⊔ St) NS le_sup_right
    (sup_le inf_le_left inf_le_left)
  rw [h7] at hmul
  have hne : St.relIndex (N' ⊔ St) ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hwH (h1 (Subgroup.mem_sup_left ⟨hwNS, hwD⟩)).2
  have h1 : (N' ⊔ St).relIndex NS = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp (Dvd.intro _ hmul) with h | h
    · exact absurd h hne
    · rw [h] at hmul
      omega
  rw [Subgroup.relIndex_eq_one] at h1
  have hSt : St ≤ Subgroup.normalizer (N' : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxN, hxD⟩
      exact ⟨NS.mul_mem (NS.mul_mem he.1 hxN) (NS.inv_mem he.1), hDn.conj_mem x hxD e⟩
    · rintro ⟨hxN, hxD⟩
      refine ⟨?_, ?_⟩
      · have := NS.mul_mem (NS.mul_mem (NS.inv_mem he.1) hxN) he.1
        simpa [mul_assoc] using this
      · have := hDn.conj_mem _ hxD e⁻¹
        simpa [mul_assoc] using this
  obtain ⟨k, hk, e, he, hke⟩ := (mem_sup_iff_of_le_normalizer hSt).mp (h1 hn₀)
  refine ⟨k⁻¹, D.inv_mem hk.2, t, htT, ?_⟩
  have heJ : e * h.J * e⁻¹ = h.J := by rw [h.commute_J he.2, mul_inv_cancel_right]
  rw [← hn₀J, ← hke]
  calc k⁻¹ * (k * e * h.J * (k * e)⁻¹) * k⁻¹⁻¹ = e * h.J * e⁻¹ := by group
    _ = h.J := heJ

end Frame

theorem prop_2_5 :
    ∀ (G : Type) [Group G] [Finite G] (m : MinCE G), 3 < m.q → JFacts → RFacts →
      commutator G = ⊤ := by
  intro G _ _ m hq hJ hR
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨fr⟩ := Frame.nonempty G m.toHyp
  have hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := fun N hN h2 =>
    m.not_case1 (case1_of_sup G m.toHyp (prop_2_3 G m.toHyp ⟨N, hN, h2⟩))
  have hodd := odd_index_commutator hidx
  have hKcomm := PSL2Sub.commutator_eq m.iso m.f_pos hq
  have hKD : m.K ≤ commutator G :=
    calc m.K = ⁅m.K, m.K⁆ := hKcomm.symm
      _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (commutator_def G).symm
  set D := commutator G
  have hDn : D.Normal := inferInstance
  have hSD : (fr.S : Subgroup G) ≤ D := fun x hx => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp fr.S.isPGroup') ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    exact mem_of_odd_index' hDn hodd hk
  obtain ⟨y, hyD, t, htT, hyt⟩ := fr.exists_conj_J_of_commutator hidx hq
  have hTD : fr.T ≤ ⁅D, D⁆ :=
    fr.T_le_K.trans (hKcomm.symm.le.trans (Subgroup.commutator_mono hKD hKD))
  have hidxD := index_ne_two_of_sylow_le_commutator fr.S
    (fr.S_le_commutator hTD (Subgroup.le_normalizer hyD) htT hyt)
  have hM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ D := ⟨fr.S, hSD⟩
  have hJD : m.J ∈ D := hSD fr.J_mem
  have hKn : ∀ x ∈ D, x * m.J = m.J * x → ∀ k ∈ m.K, x * k * x⁻¹ ∈ m.K :=
    fun x _ hx k hk => m.conj_mem_K (m.mem_H_iff.mpr hx) hk
  let hD : Hyp D := m.ofSubgroup hM hJD m.orderOf_J hKD m.le_centralizer hKn m.p m.f m.p_ne_two
    m.f_pos m.iso
  rcases m.ih D hD (card_lt_of_ne_top hne) with hc | hc
  · obtain ⟨N, hN, h2⟩ := hD.exists_normal_index_two_of_case1 hc
    exact index_ne_two_subtype hidxD N hN h2
  obtain ⟨L, hLD, hLn, hLodd, -, ⟨K'', hK''L, hJK'', hCL, ⟨eK''⟩⟩, h8⟩ :=
    m.case2_ofSubgroup hM hJD m.orderOf_J hKD m.le_centralizer hKn m.p m.f m.p_ne_two m.f_pos
      m.iso hc
  have hSL : (fr.S : Subgroup G) ≤ L := le_of_odd_relIndex hLn hLodd hSD fr.S.isPGroup'
  have hKL : m.K ≤ L := by
    have := PSL2Sub.isSimpleGroup m.iso m.f_pos hq
    have hn : (L.subgroupOf m.K).Normal := by
      refine ⟨fun x hx k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := hLn.conj_mem ⟨x, hKD x.2⟩ hx ⟨k, hKD k.2⟩
      exact this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf m.K) with hb | ht
    · exfalso
      have hT : fr.T ≤ L ⊓ m.K := le_inf (fr.T_le_S.trans hSL) fr.T_le_K
      have hdisj : Disjoint L m.K := Subgroup.subgroupOf_eq_bot.mp hb
      have hT1 : fr.T = ⊥ := eq_bot_iff.mpr (hT.trans (disjoint_iff.mp hdisj).le)
      have := fr.isKleinFour_T.card_four
      rw [hT1, Subgroup.card_bot] at this
      omega
    · exact Subgroup.subgroupOf_eq_top.mp ht
  have hTL : fr.T ≤ ⁅L, L⁆ :=
    fr.T_le_K.trans (hKcomm.symm.le.trans (Subgroup.commutator_mono hKL hKL))
  have hyL : y ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hLn.conj_mem ⟨x, hLD hx⟩ hx ⟨y, hyD⟩
    · intro hx
      have h1 : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ ∈ L :=
        hLn.conj_mem ⟨y * x * y⁻¹, hLD hx⟩ hx ⟨y⁻¹, D.inv_mem hyD⟩
      simpa [mul_assoc] using h1
  have hLidx := index_ne_two_of_sylow_le_commutator fr.S (fr.S_le_commutator hTL hyL htT hyt)
  have hJR : IsJRSubgroup L m.J K'' m.p m.f :=
    ⟨hSL fr.J_mem, m.orderOf_J, hK''L, hJK'', hCL, ⟨eK''⟩, hLidx,
      ⟨fr.S, hSL, fr.isElementaryAbelian_S, fr.card_S⟩⟩
  obtain ⟨hL', hp, hf, -, -⟩ := IsJRSubgroup.nonempty_jrGroup G m.p_ne_two m.f_pos hJR
  have hqL : hL'.q = m.q := by rw [JRGroup.q, hp, hf]; rfl
  have hsimp : IsSimpleGroup L ∧ OutCyclic L := by
    by_cases h5 : hL'.q = 5
    · obtain ⟨⟨hs, -⟩, -, -, -, hout⟩ := hJ L hL' h5
      exact ⟨hs, hout⟩
    · obtain ⟨⟨-, -, hs, -⟩, -, -, -, -, -, hout⟩ := hR L hL' h5
      exact ⟨hs (hqL ▸ hq), hout (hqL ▸ hq)⟩
  have := hsimp.1
  have hLG : L.Normal := by
    set I := Subgroup.normalClosure ((fr.S : Subgroup G) : Set G)
    have hIL : I ≤ L := (Subgroup.closure_le L).mpr fun x hx => by
      obtain ⟨s, hs, hsx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp fr.S.isPGroup') ⟨s, hs⟩
      rw [Subgroup.orderOf_mk] at hk
      have hxo : orderOf x = 2 ^ k := by rw [← hsx.orderOf_eq, hk]
      exact mem_of_odd_relIndex hLn hLodd (mem_of_odd_index' hDn hodd hxo) hxo
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (I.subgroupOf L) with hb | ht
    · exfalso
      have hJI : m.J ∈ I := Subgroup.subset_normalClosure fr.J_mem
      have hdisj : Disjoint I L := Subgroup.subgroupOf_eq_bot.mp hb
      exact m.J_ne_one ((Subgroup.disjoint_def.mp hdisj) hJI (hSL fr.J_mem))
    · have hLI : L ≤ I := Subgroup.subgroupOf_eq_top.mp ht
      have hIeq : I = L := le_antisymm hIL hLI
      rw [← hIeq]
      exact Subgroup.normalClosure_normal
  apply m.not_case2
  refine ⟨L, hLG, ?_, exists_zpowers_sup_of_outCyclic hsimp.2,
    ⟨K'', hK''L, hJK'', hCL, ⟨eK''⟩⟩, h8⟩
  rw [← Subgroup.relIndex_mul_index hLD]
  exact hLodd.mul hodd

end CFSG.Walter.W67
