module

public import CFSG.Quasithin.Vol2.E2SevenPair
public import CFSG.Quasithin.Recognition.M12AscTrans
public import CFSG.Adapters.Involutions
public import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Facts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem prop1_inverts_odd {x : G} (hx : orderOf x = 2) (hxO : x ∉ CFSG.pCore 2 G) :
    ∃ y : G, y ≠ 1 ∧ Odd (orderOf y) ∧ x * y * x⁻¹ = y⁻¹ := by
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact this
  obtain ⟨c, p, hp, hp2, hc, hinv⟩ :=
    CFSG.Quasithin.E2.exists_inverted_of_not_mem_pCore hx2 hx1 hxO
  exact ⟨c, by rintro rfl; rw [orderOf_one] at hc; exact hp.ne_one hc.symm,
    by rw [hc]; exact hp.odd_of_ne_two hp2, hinv⟩

theorem prop2_eq_centralizer_mul_oddCore {x : G} (hx : orderOf x = 2)
    (hiso : ∀ g : G, (g * x * g⁻¹) * x = x * (g * x * g⁻¹) → g * x * g⁻¹ = x) :
    Subgroup.centralizer ({x} : Set G) ⊔ pPrimeCore 2 G = ⊤ := by
  let : Fintype G := Fintype.ofFinite G
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, sq] at this
    exact this
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G x hx1 hx2 hiso
  have hNK : N ≤ oddCore G := le_sSup ⟨hNn, hNodd⟩
  have hcen : (QuotientGroup.mk x : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := hNK (hN g⁻¹)
    rw [inv_inv, ← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one] at h1
    calc (QuotientGroup.mk g : G ⧸ oddCore G) * QuotientGroup.mk x
        = QuotientGroup.mk g * ((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk x *
            QuotientGroup.mk g) := by rw [h1]
      _ = QuotientGroup.mk x * QuotientGroup.mk g := by group
  have htop : Subgroup.centralizer ({x} : Set G) ⊔ oddCore G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hc, k, hk, rfl⟩ := CFSG.Adapters.eq_centralizer_mul_oddCore hx2 hcen g
    exact Subgroup.mul_mem_sup hc hk
  simpa [CFSG.Holt.StarLemma26.oddCore_eq_pPrimeCore_two G] using htop

theorem prop2_conj_centralizer {x : G} (hx : orderOf x = 2)
    (hne : Subgroup.centralizer ({x} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤) :
    ∃ y : G, (∃ g : G, g * x * g⁻¹ = y) ∧ orderOf y = 2 ∧
      y ∈ Subgroup.centralizer ({x} : Set G) ∧ y ∉ Subgroup.zpowers x := by
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  by_contra hcon
  apply hne
  apply prop2_eq_centralizer_mul_oddCore hx
  intro g hcomm
  by_contra hne'
  apply hcon
  refine ⟨g * x * g⁻¹, ⟨g, rfl⟩, ?_, ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  · intro hmem
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hx hmem with h | h
    · exfalso
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact hne' h

theorem prop3_index_two (S : Sylow 2 G) {S0 : Subgroup G}
    (hindex : S0.relIndex (S : Subgroup G) = 2) {x : G} (hx : x * x = 1)
    (hxS : x ∈ (S : Subgroup G)) (hxS0 : x ∉ S0)
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ S0) :
    ∃ G0 : Subgroup G, G0.Normal ∧ G0.index = 2 ∧ x ∉ G0 := by
  obtain ⟨G0, hGn, hidx, hxG0, -⟩ :=
    CFSG.Quasithin.thompson_transfer_index_two S hindex hx hxS hconj
  exact ⟨G0, hGn, hidx, hxG0⟩

end CFSG.RankThree.GF2n.Parrott
