module

public import CFSG.Quasithin.H13.LocDblOdd

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc

variable {Γ : Type} [Group Γ]

theorem sylowNoDouble_of_overgroups [Finite Γ] {R : Subgroup Γ} (hR : IsSylowTwoOf R ⊤)
    {L : List ℕ} (hL : ∀ N ∈ L, N ≠ 0 ∧ (N.primeFactors.filter fun r => r ^ 2 ∣ N).card ≤ 2)
    (h : ∀ Y : Subgroup Γ, R ≤ Y → Y ≠ ⊤ → ∃ N ∈ L, Nat.card Y ∣ N) : SylowNoDouble Γ := by
  refine sylowNoDouble_of_sylow hR fun Y hRY hY => ?_
  obtain ⟨N, hN, hdvd⟩ := h Y hRY hY
  exact noIsoDouble_of_card_dvd (hL N hN).1 hdvd (hL N hN).2

theorem oddIndexBound_of_overgroups [Finite Γ] {R : Subgroup Γ} (hR : IsSylowTwoOf R ⊤)
    {L : List ℕ} (h : ∀ Y : Subgroup Γ, R ≤ Y → Y ≠ ⊤ → ∃ N ∈ L, Nat.card Y ∣ N) :
    OddIndexBound Γ L := by
  classical
  intro Y hYodd hYne
  obtain ⟨R', hR'syl, hR'Y⟩ := exists_isSylowTwoOf_le_of_odd_index hYodd
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hR hR'syl
  set e : Γ ≃* Γ := MulAut.conj g with he
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hYne
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rwa [map_map_symm_self, Subgroup.map_top_of_surjective _ e.surjective] at this
  have hg' : R.map e.toMonoidHom = R' := hg
  have hRY : R ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_symm_map_self e R]
    refine Subgroup.map_mono ?_
    rw [hg']
    exact hR'Y
  obtain ⟨N, hN, hdvd⟩ := h _ hRY hY'
  refine ⟨N, hN, ?_⟩
  rwa [Subgroup.card_map_of_injective e.symm.injective] at hdvd

end CFSG.Quasithin.H13.LocDbl

end
