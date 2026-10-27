module

public import CFSG.Quasithin.H13.LocDblOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListMain

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)

variable {Γ : Type} [Group Γ]

theorem card_dvd_of_sylow_overgroups [Finite Γ] {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤)
    {L : List ℕ} (hL : ∀ Z : Subgroup Γ, S ≤ Z → Z ≠ ⊤ → ∃ N ∈ L, Nat.card Z ∣ N)
    {R Y : Subgroup Γ} (hR : IsSylowTwoOf R ⊤) (hRY : R ≤ Y) (hY : Y ≠ ⊤) :
    ∃ N ∈ L, Nat.card Y ∣ N := by
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS hR
  set e : Γ ≃* Γ := MulAut.conj g with he
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rwa [map_map_symm_self, Subgroup.map_top_of_surjective _ e.surjective] at this
  have hSY : S ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_symm_map_self e S]
    refine Subgroup.map_mono ?_
    rw [show S.map e.toMonoidHom = R from hg]
    exact hRY
  obtain ⟨N, hN, hd⟩ := hL _ hSY hY'
  refine ⟨N, hN, ?_⟩
  rwa [Subgroup.card_map_of_injective e.symm.injective] at hd

theorem oddIndexBound_of_sylow_overgroups [Finite Γ] {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤)
    {L : List ℕ} (hL : ∀ Z : Subgroup Γ, S ≤ Z → Z ≠ ⊤ → ∃ N ∈ L, Nat.card Z ∣ N) :
    OddIndexBound Γ L := fun Y hY hne => by
  obtain ⟨R, hR, hRY⟩ := exists_isSylowTwoOf_le_of_odd_index hY
  exact card_dvd_of_sylow_overgroups hS hL hR hRY hne

theorem sylowNoDouble_of_sylow_overgroups [Finite Γ] {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤)
    {L : List ℕ} (hL : ∀ Z : Subgroup Γ, S ≤ Z → Z ≠ ⊤ → ∃ N ∈ L, Nat.card Z ∣ N)
    (hsq : ∀ N ∈ L, N ≠ 0 ∧ (N.primeFactors.filter fun r => r ^ 2 ∣ N).card ≤ 2) :
    SylowNoDouble Γ :=
  sylowNoDouble_of_sylow hS fun Y hSY hY => by
    obtain ⟨N, hN, hd⟩ := hL Y hSY hY
    exact noIsoDouble_of_card_dvd (hsq N hN).1 hd (hsq N hN).2

section HS

variable [HSLat]

theorem hs_overgroups : ∀ Z : Subgroup (J hsData), hsCtx.S ≤ Z → Z ≠ ⊤ →
    ∃ N ∈ [7680, 10752], Nat.card Z ∣ N := by
  intro Z hSZ hZ
  obtain ⟨j, hj, rfl⟩ := hs_complete Z hSZ
  have hj5 : j < 5 := by
    by_contra h
    apply hZ
    simp [memberOrTop, h]
  have e : memberOrTop 5 hsCtx.Y j = hsCtx.Y j := by simp [memberOrTop, hj5]
  rw [e, hs_member_card j hj5]
  interval_cases j
  · exact ⟨7680, by simp, by norm_num⟩
  · exact ⟨7680, by simp, by norm_num⟩
  · exact ⟨10752, by simp, by norm_num⟩
  · exact ⟨7680, by simp, by norm_num⟩
  · exact ⟨7680, by simp, by norm_num⟩

theorem oddIndexBound_HS_lat : OddIndexBound ↥(J hsData) [7680, 10752] :=
  oddIndexBound_of_sylow_overgroups hs_S_sylow hs_overgroups

theorem sylowNoDouble_HS_lat : SylowNoDouble ↥(J hsData) :=
  sylowNoDouble_of_sylow_overgroups hs_S_sylow hs_overgroups (by
    intro N hN
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
    rcases hN with rfl | rfl <;> refine ⟨by norm_num, ?_⟩ <;> simp [Nat.primeFactors] <;> decide)

end HS

end CFSG.Quasithin.H13.LocDbl
