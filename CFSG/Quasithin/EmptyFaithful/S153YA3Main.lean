module

public import CFSG.Quasithin.EmptyFaithful.S153YA3Cfg
public import CFSG.Quasithin.EmptyFaithful.S153YA5Main

public section

namespace CFSG.Quasithin.YG

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem iSup_fin_two' (K : Fin 2 → Subgroup G) : (⨆ i, K i) = K 0 ⊔ K 1 :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp) (sup_le (le_iSup K 0) (le_iSup K 1))

theorem blockProduct_two_data {I S : Subgroup G} {K : Fin 2 → Subgroup G}
    (hbp : IsBlockProduct I S 2 K) (h3 : ∀ i, IsAltType (K i) 3) :
    K 0 ≠ K 1 ∧ (∀ a ∈ K 0, ∀ b ∈ K 1, a * b = b * a) ∧ I = S ⊔ (K 0 ⊔ K 1) ∧
      (∀ s ∈ S, B6.conjSub s (K 0) = K 0 ∨ B6.conjSub s (K 0) = K 1) ∧
      (∀ s ∈ S, B6.conjSub s (K 1) = K 0 ∨ B6.conjSub s (K 1) = K 1) ∧
      ∃ t ∈ S, B6.conjSub t (K 0) = K 1 := by
  have h01 : ⁅K 0, K 1⁆ = ⊥ := hbp.2.2.2.1 0 1 (by decide)
  have hne : K 0 ≠ K 1 := by
    intro h
    have hc : ⁅K 0, K 0⁆ = ⊥ := by simpa [← h] using h01
    have hA4 := DoubleA3.IsA4Block.of_alt3 (hbp.2.2.1 0).1.1 (h3 0)
    have hbot : K 0 = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => hA4.center_L g hg fun l hl => ?_
      have h1 : ⁅g, l⁆ ∈ ⁅K 0, K 0⁆ := Subgroup.commutator_mem_commutator hg hl
      rw [hc, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have h12 := hA4.card_L
    rw [hbot, Subgroup.card_bot] at h12
    omega
  refine ⟨hne, ?_, ?_, ?_, ?_, hbp.2.2.2.2.2.1 0 1⟩
  · intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅K 0, K 1⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h01, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · rw [← iSup_fin_two']
    exact hbp.2.2.2.2.1
  · intro s hs
    obtain ⟨j, hj⟩ := hbp.2.2.2.2.2.2 s hs 0
    fin_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (by simpa using hj)
  · intro s hs
    obtain ⟨j, hj⟩ := hbp.2.2.2.2.2.2 s hs 1
    fin_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (by simpa using hj)

theorem a3A3_of_blockProduct_two {I S Iz : Subgroup G} {K : Fin 2 → Subgroup G} (hchar : CharTwo I)
    (hmp : MinParabolic I S Iz) (hbp : IsBlockProduct I S 2 K) (h3 : ∀ i, IsAltType (K i) 3)
    (hth : ⁅K 0, thompsonJ S⁆ = K 0) : ∃ t : G, DoubleA3.A3A3 I S (K 0) t := by
  obtain ⟨hne, hcomm, hgen, hperm₀, hperm₁, t, htS, htK⟩ := blockProduct_two_data hbp h3
  have hK1 : K 1 = (K 0).map (MulAut.conj t).toMonoidHom := htK.symm
  have hjoin : conjJoin S (K 0) = K 0 ⊔ K 1 := by
    refine le_antisymm (iSup_le fun s => ?_) (sup_le ?_ ?_)
    · have h' : (K 0).map (MulAut.conj (s : G)).toMonoidHom = K 0 ∨
          (K 0).map (MulAut.conj (s : G)).toMonoidHom = K 1 := hperm₀ (s : G) s.2
      rcases h' with h | h
      · rw [h]
        exact le_sup_left
      · rw [h]
        exact le_sup_right
    · exact C56.le_conjJoin (K 0) S.one_mem
    · rw [hK1]
      exact le_iSup (fun s : S => (K 0).map (MulAut.conj (s : G)).toMonoidHom) ⟨t, htS⟩
  have hK0K1 : ⁅K 0, K 1⁆ = ⊥ := hbp.2.2.2.1 0 1 (by decide)
  have hne' : (K 0).map (MulAut.conj t).toMonoidHom ≠ K 0 := by
    rw [← hK1]
    exact hne.symm
  have hjoin' : conjJoin S (K 0) = K 0 ⊔ (K 0).map (MulAut.conj t).toMonoidHom := by
    rw [← hK1]
    exact hjoin
  have hcomm' : ⁅K 0, (K 0).map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    rw [← hK1]
    exact hK0K1
  have hcs : WGen I S (K 0) :=
    ⟨hchar, hmp.isSylow, hbp.2.2.1 0, hth, by rw [hjoin, hgen, sup_comm],
      Or.inr ⟨t, htS, hne', hjoin', hcomm'⟩, minParabolic_exists_iff.1 ⟨Iz, hmp⟩⟩
  have hct : conjR (K 0) t⁻¹ = (K 0).map (MulAut.conj t).toMonoidHom := by simp [conjR]
  exact ⟨t⁻¹, hcs, h3 0, S.inv_mem htS, by rw [hct]; exact hne', by rw [hct]; exact hjoin',
    by rw [hct]; exact hcomm'⟩

theorem card_le_a3_pair_of_thompson {I S Iz : Subgroup G} {K : Fin 2 → Subgroup G} {ρ : G}
    (hchar : CharTwo I) (hmp : MinParabolic I S Iz) (hbp : IsBlockProduct I S 2 K)
    (h3 : ∀ i, IsAltType (K i) 3) (hth : ⁅K 0, thompsonJ S⁆ = K 0)
    (hρN : ρ ∈ Subgroup.normalizer (S : Set G)) (hρS : ρ ∉ S) (hρ2 : ρ ^ 2 ∈ S)
    (hb : ∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) :
    Nat.card S ≤ 2 ^ 9 := by
  obtain ⟨t, hA3⟩ := a3A3_of_blockProduct_two hchar hmp hbp h3 hth
  obtain ⟨C⟩ := AppD.exists_gcfg hA3
  exact (gmate_of_zpowers hρN hρS hρ2 hb).card_S_le C

end CFSG.Quasithin.YG
