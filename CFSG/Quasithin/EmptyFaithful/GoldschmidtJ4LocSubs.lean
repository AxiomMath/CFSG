module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocFix
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem nodup_of_pairwise_lt {B : List ℕ} (h : B.Pairwise (· < ·)) : B.Nodup :=
  h.imp fun hab => ne_of_lt hab

theorem subs_complete
    (hF : J4Facts) {A : Subgroup J} (hAE : A ≤ Eg uJ 11)
    (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A) : ∃ B ∈ subs, MaskList A B := by
  have hM := hF.mat
  classical
  let 𝒮 : Finset (List ℕ) := subs.toFinset.filter fun B => ∀ c ∈ B, eta uJ 11 c ∈ A
  have h0 : ([0] : List ℕ) ∈ 𝒮 := by
    refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 subs_zero_mem, ?_⟩
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    rw [eta_zero]
    exact A.one_mem
  obtain ⟨B, hB𝒮, hmax⟩ := Finset.exists_max_image 𝒮 List.length ⟨[0], h0⟩
  obtain ⟨hBs', hBA⟩ := Finset.mem_filter.1 hB𝒮
  have hBs : B ∈ subs := List.mem_toFinset.1 hBs'
  obtain ⟨hlt, hpw, hz, hxor, hinv⟩ := subs_prop hBs
  refine ⟨B, hBs, fun c => ⟨fun hc => ⟨hlt c hc, hBA c hc⟩, fun ⟨hc, hcA⟩ => ?_⟩⟩
  by_contra hcB
  have hK : ∀ x, x ∈ maskSub B ↔ ∃ c ∈ B, x = eta uJ 11 c := fun x => mem_maskSub_iff hM hz hxor
  have hKA : maskSub B ≤ A := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hK x).1 hx
    exact hBA c hc
  have hKE : maskSub B ≤ Eg uJ 11 := maskSub_le_Eg B
  have hmemK : ∀ c, c < 2048 → eta uJ 11 c ∈ maskSub B → c ∈ B := by
    intro c hc hcK
    obtain ⟨c', hc', hcc'⟩ := (hK _).1 hcK
    have := eta_inj' hM hc (hlt c' hc') hcc'
    rw [this]
    exact hc'
  have hKn : ∀ g ∈ P0, ∀ x ∈ maskSub B, g * x * g⁻¹ ∈ maskSub B := by
    intro g hg x hx
    refine (normalized_of_gens hM hKE (fun i hi c hc hcK => ?_) g hg x hx).1
    have hcB' := hmemK c hc hcK
    obtain ⟨h1, h2⟩ := hinv i hi c hcB'
    exact ⟨(hK _).2 ⟨_, h1, rfl⟩, (hK _).2 ⟨_, h2, rfl⟩⟩
  have hne : maskSub B ≠ A := by
    intro heq
    apply hcB
    refine hmemK c hc ?_
    rw [heq]
    exact hcA
  obtain ⟨m, hmA, hmK, hfix⟩ :=
    exists_fixed_mod (isPGroup_P0 hF) hKA (hAE.trans Eg_le_P0) hne hKn hn
  obtain ⟨v, hv, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hAE hmA)
  have hv' : v < 2048 := hv
  have hvB : v ∉ B := fun hvB => hmK ((hK _).2 ⟨v, hvB, rfl⟩)
  have hfixv : ∀ i < 4, (actT (kTab i) v ^^^ v) ∈ B := by
    intro i hi
    have h1 := hfix (kJ i) (kJ_mem_P0 hi)
    have h2 := (Acts_kJ hM hi).2 v hv
    rw [h2, eta_inv hM, eta_mul_eta hM] at h1
    have hlt1 : actT (kTab i) v ^^^ v < 2048 :=
      Nat.xor_lt_two_pow (actT_lt (Acts_kJ hM hi).1 v) hv
    exact hmemK _ hlt1 h1
  obtain ⟨B', hB's, hsub, hvB', hB'⟩ := subs_chain hBs hv' hvB hfixv
  have hB'𝒮 : B' ∈ 𝒮 := by
    refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 hB's, fun y hy => ?_⟩
    rcases hB' y hy with hy | ⟨x, hx, rfl⟩
    · exact hBA y hy
    · rw [← eta_mul_eta hM]
      exact A.mul_mem (hBA x hx) hmA
  have hnd : B.Nodup := nodup_of_pairwise_lt hpw
  have hnd' : B'.Nodup := nodup_of_pairwise_lt (subs_prop hB's).2.1
  have hlen : B.length < B'.length := by
    rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup hnd']
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsup => hvB ?_⟩
    · exact List.mem_toFinset.2 (hsub x (List.mem_toFinset.1 hx))
    · exact List.mem_toFinset.1 (hsup (List.mem_toFinset.2 hvB'))
  exact absurd (hmax B' hB'𝒮) (not_le.2 hlen)

end CFSG.Quasithin.J4Loc
