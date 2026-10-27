module

public import CFSG.RankThree.PartOne.SEITZ6.G2Big

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

section Main

variable [Finite K] [CharP K 2]

theorem subfieldPairG2Big_odd (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) (h4 : 4 ∣ Nat.card (fixSubfield σ)) (g : adjointGroup .G2 K)
    (hne : ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map
        (MulAut.conj g).toMonoidHom ≠ (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) :
    Subgroup.closure
      ((((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) : Subgroup (adjointGroup .G2 K)) :
          Set (adjointGroup .G2 K)) ∪
        ((((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map
          (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
          Set (adjointGroup .G2 K))) = ⊤ := by
  set R : Subgroup (adjointGroup .G2 K) := (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)
    with hRdef
  set k : Subfield K := fixSubfield σ with hkdef
  have hKcard : Nat.card K = Nat.card k ^ p := by
    have := card_eq_card_fixSubfield_pow σ
    rwa [hσ] at this
  have hkpos : 0 < Nat.card k := Nat.card_pos
  have hk4 : 4 ≤ Nat.card k := Nat.le_of_dvd hkpos h4
  have hR : ∀ q < 12, ∀ c ∈ k, xp q c ∈ R := fun q hq c hc =>
    mem_rat_of_entrywise_fixed σ (xp_entrywise_fixed σ hq ((mem_fixSubfield σ).1 hc))
  have hRent : ∀ x : adjointGroup .G2 K, EntriesIn k x → x ∈ R := fun x hx =>
    mem_rat_of_entrywise_fixed σ (entriesIn_entrywise_fixed σ hx)
  have hg : ¬ EntriesIn k g := fun hg => hne (map_conj_eq_self (hRent g hg))
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry k hk4 hR g hg
  set H : Subgroup (adjointGroup .G2 K) :=
    Subgroup.closure ((R : Set (adjointGroup .G2 K)) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K))) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : R.map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hH1 : ∀ c ∈ k, xp 7 c ∈ H := fun c hc => hRH (hR 7 (by norm_num) c hc)
  have hH2 : ∀ c ∈ k, (r * g * r') * xp 7 c * (r * g * r')⁻¹ ∈ H := by
    intro c hc
    have h1 : r' * xp 7 c * r'⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem hr' (hR 7 (by norm_num) c hc)) (R.inv_mem hr')
    have h2 : g * (r' * xp 7 c * r'⁻¹) * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 : r * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hr) (hRgH h2)) (H.inv_mem (hRH hr))
    have e : (r * g * r') * xp 7 c * (r * g * r')⁻¹ =
        r * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r⁻¹ := by group
    rw [e]
    exact h3
  have h7 : Full H 7 :=
    full_seven_of_pair k hp hp2 hKcard h4 (r * g * r') hH1 hH2 hbad
  obtain ⟨t₁, t₂, t₃, h12, h13, h23, h1, h2, h3⟩ := exists_three_nonzero k hk4
  have hex : ∃ t : k, t ≠ 0 ∧ t ≠ 1 := by
    by_cases ht : t₁ = 1
    · exact ⟨t₂, h2, fun e => h12 (ht.trans e.symm)⟩
    · exact ⟨t₁, h1, ht⟩
  obtain ⟨t, ht0, ht1⟩ := hex
  exact eq_top_of_subfield k (t := (t : K)) t.2 (fun e => ht0 (Subtype.ext e))
    (fun e => ht1 (Subtype.ext e)) (fun q hq c hc => hRH (hR q hq c hc)) h7

end Main

end CFSG.RankThree.PartTwo.Sec4.E27
