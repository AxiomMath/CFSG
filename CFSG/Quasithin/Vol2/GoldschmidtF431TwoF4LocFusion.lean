module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocChain
public import Certificates.Certificate7050Base

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem locFixOK_spec {pts : Array ℕ} {G Gi : Array (Array ℕ)} {zA tA z1 z2 : Array ℕ}
    (h : locFixOK pts G Gi zA tA z1 z2 = true) : ∀ k < (locFix tA).length,
    wordOK locWords[k]! = true ∧ (wArr G Gi locWords[k]!)[0]! = (locFix tA)[k]! ∧
      isInvA 1755 (wArr G Gi locWords[k]!) (invCand 1755 (wArr G Gi locWords[k]!)) = true ∧
      (eqA 1755 (locConj (wArr G Gi locWords[k]!) zA) zA = true ∨
        eqA 1755 (locConj (wArr G Gi locWords[k]!) zA) z1 = true ∨
        eqA 1755 (locConj (wArr G Gi locWords[k]!) zA) z2 = true ∨
        (fixesS pts (locConj (wArr G Gi locWords[k]!) zA) = true ∧ fixesS pts tA = true ∧
          locChainOK pts G Gi zA (locConj (wArr G Gi locWords[k]!) zA) tA locChains[k]! =
            true)) := by
  intro k hk
  have := allLt_spec h hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨h1, h2, h3, ?_⟩
  rcases h4 with ((h | h) | h) | ⟨⟨h5, h6⟩, h7⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨h5, h6, h7⟩))

theorem mem_locFix_iff {tA : Array ℕ} {n : ℕ} : n ∈ locFix tA ↔ n < 1755 ∧ tA[n]! = n := by
  simp [locFix, List.mem_filter, List.mem_range]

theorem fusion_model : ∀ u ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M), IsConj zM u →
    u ∈ VM ∨ ∃ n ∈ twoF4M2, ∃ a ∈ twoF4TT, ∃ b ∈ twoF4TT, u = n * a * n⁻¹ ∧ tM = n * b * n⁻¹ ∧
      ∃ b' ∈ twoF4TT, Relation.ReflTransGen (PairLink twoF4TT twoF4M1 twoF4M2) (a, b) (zM, b') ∧
        ∀ h ∈ twoF4M1, h * tM * h⁻¹ ≠ b' := by
  intro u hu hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hut : u * tM = tM * u := Subgroup.mem_centralizer_singleton_iff.1 hu
  have hcz : g⁻¹ * tM * g ∈ twoF4M1 := by
    rw [← cent_z_model]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc g⁻¹ * tM * g * zM = g⁻¹ * (tM * (g * zM * g⁻¹)) * g := by group
      _ = g⁻¹ * (tM * u) * g := by rw [hg]
      _ = g⁻¹ * (u * tM) * g := by rw [hut]
      _ = zM * (g⁻¹ * tM * g) := by rw [← hg]; group
  have ht0 := (mem_twoF4M1_iff _).1 hcz
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq] at ht0
  have htp : tEl.1 (g.1 0) = g.1 0 := ht0
  have hpm : (g.1 0).1 ∈ locFix (tArr titsGenArrs gInv) := by
    rw [mem_locFix_iff]
    refine ⟨(g.1 0).2, ?_⟩
    rw [rep_tEl (g.1 0), htp]
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.1 hpm
  obtain ⟨hw, hm0, hinv, hcase⟩ := locFixOK_spec locParts.2.2.2.2.2 k hk
  have hrep : Rep 1755 (wArr titsGenArrs gInv locWords[k]!) (wEl locWords[k]!).1 :=
    rep_wEl hw invsOK_gInv
  have hmi := rep_inv_of_isInvA hrep hinv
  set mM : ↥twoF4M := ⟨(wEl locWords[k]!).1, mem_twoF4M_of_mem_A (wEl locWords[k]!).2⟩ with hmM
  have hkp' : (wArr titsGenArrs gInv locWords[k]!)[0]! = ((g.1 0 : Fin 1755) : ℕ) := by
    generalize locFix (tArr titsGenArrs gInv) = L at hk hkp hm0
    rw [hm0, getElem!_pos _ k hk, hkp]
  have hm : mM.1 0 = g.1 0 := by
    apply Fin.ext
    rw [← hkp']
    exact (hrep 0).symm
  have hu_eq : u = mM * zM * mM⁻¹ := by
    rw [← hg]
    exact zP_eq hm.symm
  have huRep : Rep 1755 (locConj (wArr titsGenArrs gInv locWords[k]!) titsZArr) u.1 := by
    rw [hu_eq]
    exact rep_compA (rep_compA hrep rep_zM) hmi
  rcases hcase with h | h | h | ⟨hS, hSt, hchain⟩
  · left
    have : u = zM := Subtype.ext (eq_of_eqA huRep rep_zM h)
    rw [this]
    exact mem_VM.2 (Or.inr (Or.inl rfl))
  · left
    have : u = z1M := Subtype.ext (eq_of_eqA huRep rep_z1 h)
    rw [this]
    exact mem_VM.2 (Or.inr (Or.inr (Or.inl rfl)))
  · left
    have : u = z2M := Subtype.ext (eq_of_eqA huRep rep_z2 h)
    rw [this]
    exact mem_VM.2 (Or.inr (Or.inr (Or.inr rfl)))
  · right
    have huT : u ∈ twoF4TT :=
      Subgroup.mem_subgroupOf.2 (mem_twoF4S_of_inS (g := ⟨u.1, mem_A u⟩) huRep hS)
    have htT : tM ∈ twoF4TT := twoF4_F431LieI.t_mem
    obtain ⟨b', hb', hq, hch⟩ := locChain_spec _ _ _ u tM huRep rep_tEl huT htT hchain
    exact ⟨1, Subgroup.one_mem _, u, huT, tM, htT, by simp, by simp, b', hb', hch,
      hne_of_col hq⟩

end CFSG.Quasithin.H13.F431.TwoF4
