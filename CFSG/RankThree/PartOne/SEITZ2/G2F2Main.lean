module

public import CFSG.RankThree.PartOne.SEITZ2.G2OuterBig
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Cases
public import CFSG.RankThree.PartOne.SEITZ2.G2F2NF
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Entry

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6

theorem subfieldPairG2F2 : SubfieldPairG2F2 := by
  intro K _ _ hchar σ hσ h2 g hne
  have : CharP K 2 := hchar
  set R : Subgroup (adjointGroup .G2 K) := g2Fixed σ with hRdef
  set k : Subfield K := fixSubfield σ with hkdef
  have hKcard : Nat.card K = Nat.card k ^ 7 := by
    have := card_eq_card_fixSubfield_pow σ
    rwa [hσ] at this
  have hR : ∀ q < 12, ∀ c ∈ k, xp q c ∈ R := fun q hq c hc =>
    mem_rat_of_entrywise_fixed σ (xp_entrywise_fixed σ hq ((mem_fixSubfield σ).1 hc))
  have hRent : ∀ x : adjointGroup .G2 K, EntriesIn k x → x ∈ R := fun x hx =>
    mem_rat_of_entrywise_fixed σ (entriesIn_entrywise_fixed σ hx)
  have hg : ¬ EntriesIn k g := fun hg => hne (map_conj_eq_self (hRent g hg))
  obtain ⟨r, hr, r', hr', hbad⟩ := exists_bad_entry_f2 k hR g hg
  set H : Subgroup (adjointGroup .G2 K) :=
    Subgroup.closure ((R : Set (adjointGroup .G2 K)) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K))) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : R.map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hH2 : (r * g * r') * xp 7 1 * (r * g * r')⁻¹ ∈ H := by
    have h1 : r' * xp 7 1 * r'⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem hr' (hR 7 (by norm_num) 1 k.one_mem)) (R.inv_mem hr')
    have h2 : g * (r' * xp 7 1 * r'⁻¹) * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 : r * (g * (r' * xp 7 1 * r'⁻¹) * g⁻¹) * r⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hr) (hRgH h2)) (H.inv_mem (hRH hr))
    have e : (r * g * r') * xp 7 1 * (r * g * r')⁻¹ =
        r * (g * (r' * xp 7 1 * r'⁻¹) * g⁻¹) * r⁻¹ := by group
    rw [e]
    exact h3
  have hne0 : coordAt (rt 10) ((r * g * r') • rootVec .G2 K (rt 7)) ≠ 0 := fun h =>
    hbad (h ▸ k.zero_mem)
  obtain ⟨c, μ, hc1, hμ, hy⟩ := normal_form (r * g * r') hne0
  have hμk : μ ∉ k := by
    rw [hμ]
    exact hbad
  have hyH : ordProd c * xp 10 μ * (ordProd c)⁻¹ ∈ H := by
    have h := hH2
    rw [hy 1, mul_one] at h
    exact h
  exact core_cases h2 (by norm_num : (7 : ℕ).Prime) (by norm_num) hKcard
    (fun p hp c hc => hRH (hR p hp c hc)) hc1 hμk hyH

end CFSG.RankThree.PartOne.SEITZ2
