module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxD4Cen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.S63
  CFSG.Quasithin.ZPInv

namespace GoldC3

@[expose] def Cent9Data (Γ : Type) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    Nat.card (centerOf P) = 2 ∧ 9 ∣ Nat.card (Subgroup.centralizer (centerOf P : Set Γ))

theorem Cent9Data.of_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] (h : Cent9Data Γ)
    (φ : Γ ≃* Γ') : Cent9Data Γ' := by
  intro P' hP2 hPi
  have hP2' : IsPGroup 2 ↥(P'.map φ.symm.toMonoidHom) :=
    hP2.of_equiv (Subgroup.equivMapOfInjective P' φ.symm.toMonoidHom φ.symm.injective)
  have hPi' : ¬ 2 ∣ (P'.map φ.symm.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective φ.symm.bijective]
    exact hPi
  obtain ⟨h1, h9⟩ := h _ hP2' hPi'
  have hmap : (P'.map φ.symm.toMonoidHom).map φ.toMonoidHom = P' := by
    rw [Subgroup.map_map]
    ext x
    simp
  have hc : centerOf P' = (centerOf (P'.map φ.symm.toMonoidHom)).map φ.toMonoidHom := by
    rw [← centerOf_map_equiv φ, hmap]
  refine ⟨?_, ?_⟩
  · rw [hc, Subgroup.card_map_of_injective φ.injective]
    exact h1
  · rw [hc, centralizer_map_equiv φ, Subgroup.card_map_of_injective φ.injective]
    exact h9

theorem cent9Data_trialityGroup8 :
    Cent9Data trialityGroup8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite trialityGroup8 := d4_finite
  intro P hP hPi
  have hcard := d4_card_sylow hP hPi
  have : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨c, hc, hc2, hc1⟩ := GoldCMax.exists_involution_centerOf hP
  obtain ⟨g, hg⟩ := d4_conj_z0 hP hPi hc hc2 hc1
  set Pg : Subgroup trialityGroup8 := P.map (MulAut.conj g⁻¹).toMonoidHom with hPg
  have hPg2 : IsPGroup 2 ↥Pg := hP.map _
  have hPgi : ¬ 2 ∣ Pg.index := by
    rwa [hPg, Subgroup.index_map_of_bijective (MulAut.conj g⁻¹).bijective]
  have hz : d4z ∈ centerOf Pg := (mem_centerOf_map_conj P g⁻¹ d4z).2 (by simpa [hg] using hc)
  have hcen : centerOf P = Subgroup.zpowers c := by
    apply le_antisymm
    · intro d hd
      by_cases hd1 : d = 1
      · rw [hd1]
        exact Subgroup.one_mem _
      · have hd' : g⁻¹ * d * g ∈ centerOf Pg := by
          refine (mem_centerOf_map_conj P g⁻¹ _).2 ?_
          have e : g⁻¹⁻¹ * (g⁻¹ * d * g) * g⁻¹ = d := by group
          rw [e]
          exact hd
        have h := d4_core hPg2 hPgi hz hd' (fun h1 => hd1 (by
          calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
            _ = 1 := by rw [h1]; group))
        have : d = c := by
          calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
            _ = g * d4z * g⁻¹ := by rw [h]
            _ = c := hg.symm
        rw [this]
        exact Subgroup.mem_zpowers c
    · rw [Subgroup.zpowers_le]
      exact hc
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  refine ⟨?_, ?_⟩
  · rw [hcen, Nat.card_zpowers, hord]
  ·
    have hLle : d4L.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer (centerOf P : Set trialityGroup8) := by
      rw [hcen, centralizer_zpowers_eq]
      rintro _ ⟨l, hl, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hg]
      have h := Subgroup.mem_centralizer_singleton_iff.mp (d4L_le_centralizer hl)
      show g * l * g⁻¹ * (g * d4z * g⁻¹) = g * d4z * g⁻¹ * (g * l * g⁻¹)
      calc g * l * g⁻¹ * (g * d4z * g⁻¹) = g * (l * d4z) * g⁻¹ := by group
        _ = g * (d4z * l) * g⁻¹ := by rw [h]
        _ = g * d4z * g⁻¹ * (g * l * g⁻¹) := by group
    have h504 : Nat.card (d4L.map (MulAut.conj g).toMonoidHom) = 504 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_d4L]
    exact (Nat.dvd_trans (by norm_num : 9 ∣ 504) (h504 ▸ Subgroup.card_dvd_of_le hLle))

theorem cent9Data_of_trialityD4
    {X : Type} [Group X] (h : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 1) :
    Cent9Data X := by
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 X (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  exact cent9Data_trialityGroup8.of_mulEquiv e.symm

end GoldC3

end CFSG.Quasithin
