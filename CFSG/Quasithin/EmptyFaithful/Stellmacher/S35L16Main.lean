module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16R
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Rk
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L16Rank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L16

open S35.Std S35.Fin S35.At S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim16a_II (hS : Sit H M S) : Claim16a H M := by
  intro β α' hL
  have hRk := rkZvEq_of_sit hS
  obtain ⟨hp, hnZ⟩ := hL
  have hZβ : Zv β ⊓ Vn α' = ⊥ := inf_eq_bot_of_card_two (hS.cardZ5 β hp.vδ) hnZ
  by_contra hno
  obtain ⟨ca⟩ := exists_chart2 hS hp.vδ'
  obtain ⟨cb⟩ := exists_chart2 hS hp.vδ
  have hle1 : Vn β ≤ stab α' := (PD_Vn_le_stab hS hp).1
  have hle2 : Vn α' ≤ stab β := (PD_Vn_le_stab hS hp).2
  have hnoswap : ∀ v ∈ Vn β, ∀ hvs : v ∈ stab α', ¬ (ca.θ ⟨v, hvs⟩).IsSwap := by
    intro v hv hvs hsw
    refine hno ⟨v, hv, hvs, ?_⟩
    rw [secIdx_Zv_eq_idx hRk ca hp.vδ' hvs]
    exact (idx_orth_eq_two_iff _).mpr hsw
  have hAb := isElemAb_bar2 ca (Vn_isElemAbelian hS β)
  have hAq := isQuad_bar2 ca hle1 (PD_quadratic hS hp).1
  obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hp.not_le
  have hvs : v ∈ stab α' := hle1 hv
  have hg1 : ca.θ ⟨v, hvs⟩ ≠ 1 := fun h => hvQ ((ca.ker_iff hS hp.vδ' _).mp h)
  have hgA : ca.θ ⟨v, hvs⟩ ∈ ca.bar (Vn β) := ca.mem_bar_of_mem hv hvs
  have hgg : ca.θ ⟨v, hvs⟩ * ca.θ ⟨v, hvs⟩ = 1 := hAb.1 _ hgA
  have hcard : Nat.card (ca.bar (Vn β)) ≤ 2 := by
    rcases (isQuad_elemAb_iff hAb).mp hAq with h0 | ⟨x, -, hxx, hAx⟩ | ⟨s, t, -, -, hs, -, hAst⟩
    · exact absurd (Subgroup.mem_bot.mp (h0 ▸ hgA)) hg1
    · rw [hAx, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hxx)
    · exfalso
      have hsA : s ∈ ca.bar (Vn β) := hAst ▸ Subgroup.subset_closure (by simp)
      obtain ⟨u, hu, hθ⟩ := ca.mem_bar_iff.mp hsA
      exact hnoswap u hu u.2 (by rw [show (⟨(u : G), u.2⟩ : ↥(stab α')) = u from rfl, hθ]; exact hs)
  have hgd : IsDoubleSwap (ca.θ ⟨v, hvs⟩) := by
    have h2 : ca.θ ⟨v, hvs⟩ ^ 2 = 1 := by rw [pow_two]; exact hgg
    refine ⟨hg1, h2, ?_⟩
    by_contra hsg
    refine hnoswap v hv hvs ((idx_orth_eq_two_iff _).mp ?_)
    rw [idx_orth]
    simp [hg1, h2, hsg]
  have hidx : idx orth (ca.θ ⟨v, hvs⟩) = 4 := idx_orth_doubleSwap hgd
  have h4 : 4 ≤ (Qv β).relIndex (Vn α') := by
    have := card_commW_le_relIndex hS hp ca hv hvs (comm_Qv_eq_one hS hp hZβ v hv)
    rwa [card_commW_of_double hgd] at this
  obtain ⟨D', hD', hbar⟩ := exists_That_bar2 hS hp cb h4
  have hAb' := isElemAb_bar2 cb (Vn_isElemAbelian hS α')
  have hAq' := isQuad_bar2 cb hle2 (PD_quadratic hS hp).2
  have hc4 : Nat.card (cb.bar (Vn α')) = 4 := by rw [hbar]; exact card_That hD'
  obtain ⟨s, t, hs, ht, hst, hc, hAst⟩ : ∃ s t : Perm (Fin 5), s.IsSwap ∧ t.IsSwap ∧ s ≠ t ∧
      s * t = t * s ∧ cb.bar (Vn α') = Subgroup.closure ({s, t} : Set (Perm (Fin 5))) := by
    rcases (isQuad_elemAb_iff hAb').mp hAq' with
      h0 | ⟨x, -, hxx, hAx⟩ | ⟨s, t, hst, hc, hs, ht, hAst⟩
    · rw [h0, Subgroup.card_bot] at hc4; omega
    · rw [hAx, Nat.card_zpowers] at hc4
      have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hxx
      have := orderOf_le_of_pow_eq_one (by norm_num) hx2
      omega
    · exact ⟨s, t, hs, ht, hst, hc, hAst⟩
  have hsA : s ∈ cb.bar (Vn α') := hAst ▸ Subgroup.subset_closure (by simp)
  have htA : t ∈ cb.bar (Vn α') := hAst ▸ Subgroup.subset_closure (by simp)
  have hs2 : s * s = 1 := hAb'.1 s hsA
  have ht2 : t * t = 1 := hAb'.1 t htA
  have hR := card_R_le_four hS hRk hp hZβ cb hs2 ht2 hc hs ht hAst
  have hRZ := inf_comm_eq_bot hS hRk hp ca hv hvs hidx hR
  have hY : Vn β ⊓ Qv α' ≤ fixSecIn (Vn α') (Cb β) (Vn β) := by
    intro y hy
    rw [F53B3.N37.mem_fixSecIn_iff cb.le cb.Vn_le_normalizer_Cb]
    refine ⟨hy.1, fun u hu => ?_⟩
    have h2 : ⁅u, y⁆ ∈ ⁅Vn α', Qv α'⁆ := Subgroup.commutator_mem_commutator hu hy.2
    rw [comm_Vn_Qv hS hp.vδ'] at h2
    have h3 : ⁅u, y⁆ ∈ ⁅Vn β, Vn α'⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hu hy.1
    have : ⁅u, y⁆ ∈ Zv α' ⊓ ⁅Vn β, Vn α'⁆ := ⟨h2, h3⟩
    rw [hRZ, Subgroup.mem_bot] at this
    rw [commutatorElement_def] at this
    rw [this]
    exact (Cb β).one_mem
  have hF : (fixSecIn (Vn α') (Cb β) (Vn β)).relIndex (Vn β) = 4 := by
    rw [cb.relIndex_fixSecIn hle2, hbar]
    exact index_fixW_That hD'
  have hFV : fixSecIn (Vn α') (Cb β) (Vn β) ≤ Vn β := Chart2.fixSecIn_le_Vn _
  have hge : 4 ≤ (Vn β ⊓ Qv α').relIndex (Vn β) := by
    have := Subgroup.relIndex_mul_relIndex (Vn β ⊓ Qv α') _ (Vn β) hY hFV
    rw [hF] at this
    have hpos : 0 < ((Vn β ⊓ Qv α').relIndex (fixSecIn (Vn α') (Cb β) (Vn β))) :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  rw [relIndex_Vn_inf_Qv2 hS hp ca] at hge
  omega

end S35.L16

end F53.Stellmacher

end CFSG.Quasithin
