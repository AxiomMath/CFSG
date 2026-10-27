module

public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvD4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.S63
  CFSG.Quasithin.ZPInv

namespace GoldCMax

@[expose] def Cent3Data (Γ : Type) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    Nat.card (centerOf P) = 2 ∧ 3 ∣ Nat.card (Subgroup.centralizer (centerOf P : Set Γ))

theorem Cent3Data.of_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] (h : Cent3Data Γ)
    (φ : Γ ≃* Γ') : Cent3Data Γ' := by
  intro P' hP2 hPi
  have hP2' : IsPGroup 2 ↥(P'.map φ.symm.toMonoidHom) :=
    hP2.of_equiv (Subgroup.equivMapOfInjective P' φ.symm.toMonoidHom φ.symm.injective)
  have hPi' : ¬ 2 ∣ (P'.map φ.symm.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective φ.symm.bijective]
    exact hPi
  obtain ⟨h1, h3⟩ := h _ hP2' hPi'
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
    exact h3

theorem exists_involution_centerOf {Γ : Type} [Group Γ] {P : Subgroup Γ} [Finite P]
    (hP : IsPGroup 2 ↥P) [Nontrivial ↥P] : ∃ c ∈ centerOf P, c ^ 2 = 1 ∧ c ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nontrivial (Subgroup.center ↥P) := hP.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥P) := hP.to_subgroup _
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card ↥(Subgroup.center ↥P) := Finite.one_lt_card
    rw [hn] at h1
    simp at h1
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥P) := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx2 : (x : ↥P) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : (x : ↥P) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  refine ⟨((x : ↥P) : Γ), ⟨(x : ↥P).2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩)
  · exact congrArg Subtype.val hx2
  · exact fun h => hx1 (Subtype.ext h)

theorem cent3Data_trialityGroup8 :
    Cent3Data trialityGroup8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite trialityGroup8 := d4_finite
  intro P hP hPi
  have hcard := d4_card_sylow hP hPi
  have : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨c, hc, hc2, hc1⟩ := exists_involution_centerOf hP
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
    exact (Nat.dvd_trans (by norm_num : 3 ∣ 504) (h504 ▸ Subgroup.card_dvd_of_le hLle))

theorem cent3Data_of_trialityD4
    {X : Type} [Group X] (h : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 1) :
    Cent3Data X := by
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 X (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  exact cent3Data_trialityGroup8.of_mulEquiv e.symm

end GoldCMax

end CFSG.Quasithin
