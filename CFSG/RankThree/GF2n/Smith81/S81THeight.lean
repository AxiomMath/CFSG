module

public import CFSG.RankThree.GF2n.Smith81.S81TFin

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [CharP K 2]

open _root_.Classical in
private noncomputable def aux_ht_m (s : V K) : ℤ :=
  if h : s.support.Nonempty then s.support.inf' h (fun a => pr a rho2) else 0

private theorem aux_ht_m_eq {s : V K} (hn : s.support.Nonempty) :
    aux_ht_m s = s.support.inf' hn (fun a => pr a rho2) := by
  unfold aux_ht_m
  rw [dif_pos hn]

private theorem aux_ht_m_le {s : V K} {a : Fin e7Data.d} (ha : s a ≠ 0) :
    aux_ht_m s ≤ pr a rho2 := by
  have hn : s.support.Nonempty := ⟨a, Finsupp.mem_support_iff.2 ha⟩
  rw [aux_ht_m_eq hn]
  exact Finset.inf'_le (fun a => pr a rho2) (Finsupp.mem_support_iff.2 ha)

private theorem aux_ht_m_lt {s t : V K} (ht : t ≠ 0)
    (h : ∀ b, t b ≠ 0 → aux_ht_m s + 1 ≤ pr b rho2) :
    aux_ht_m s + 1 ≤ aux_ht_m t := by
  have hn : t.support.Nonempty := Finsupp.support_nonempty_iff.2 ht
  rw [aux_ht_m_eq hn]
  exact (Finset.le_inf'_iff hn _).2 fun b hb => h b (Finsupp.mem_support_iff.1 hb)

theorem exists_mem_ker_rootOps [Finite K] (S' : AddSubgroup (V K)) (hne : S' ≠ ⊥) (A2 : List Rt)
    (hroot : ∀ α ∈ A2, IsRoot .E7 α) (hpos : ∀ α ∈ A2, 0 < MinData.toWeight α ⬝ᵥ rho2)
    (hstab : ∀ α ∈ A2, ∀ s ∈ S', e7Data.rootOp K α s ∈ S') :
    ∃ s ∈ S', s ≠ 0 ∧ ∀ α ∈ A2, e7Data.rootOp K α s = 0 := by
  haveI : Finite (V K) := Finite.of_equiv (Fin e7Data.d → K) Finsupp.equivFunOnFinite.symm
  obtain ⟨s₀, hs₀S, hs₀0⟩ : ∃ s₀ ∈ S', s₀ ≠ 0 := by
    obtain ⟨⟨s₀, hs₀S⟩, hs₀0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hne
    exact ⟨s₀, hs₀S, fun h => hs₀0 (Subtype.ext h)⟩
  have hfin : ({s : V K | s ∈ S' ∧ s ≠ 0} : Set (V K)).Finite := Set.toFinite _
  have hTne : hfin.toFinset.Nonempty := ⟨s₀, hfin.mem_toFinset.2 ⟨hs₀S, hs₀0⟩⟩
  obtain ⟨s, hsT, hmax⟩ := Finset.exists_max_image hfin.toFinset aux_ht_m hTne
  obtain ⟨hsS, hs0⟩ := hfin.mem_toFinset.1 hsT
  refine ⟨s, hsS, hs0, fun α hα => ?_⟩
  by_contra hcon
  have htS : e7Data.rootOp K α s ∈ S' := hstab α hα s hsS
  have key : aux_ht_m s + 1 ≤ aux_ht_m (e7Data.rootOp K α s) := by
    apply aux_ht_m_lt hcon
    intro b hb
    rw [rootOp_apply (hroot α hα)] at hb
    by_cases h1 : pr b α = 1
    · rw [if_pos h1] at hb
      have ha : pr (shift (-α) b) α = -1 := pr_shift_neg (hroot α hα) h1
      have hbα : shift α (shift (-α) b) = b := shift_shift_neg (hroot α hα) h1
      have h2 : aux_ht_m s ≤ pr (shift (-α) b) rho2 := aux_ht_m_le hb
      have h3 := pr_shift (hroot α hα) ha rho2
      rw [hbα] at h3
      have h4 := hpos α hα
      omega
    · rw [if_neg h1] at hb
      exact absurd rfl hb
  have hle := hmax (e7Data.rootOp K α s) (hfin.mem_toFinset.2 ⟨htS, hcon⟩)
  omega

end CFSG.RankThree.GF2n.Smith81.MinuscT
