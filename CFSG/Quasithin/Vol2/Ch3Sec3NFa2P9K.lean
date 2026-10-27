module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KAct
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs2

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

theorem leaf_P9K_of
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Leaf_P9K := by
  intro G _ _ T M L D H K q c
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  obtain ⟨a, haK, haO, ha2, hxa, hact⟩ :=
    c.exists_involution h5 h7 h9 h128 h37 h38 h39 hxY hxK hx3
  have hOR : pCoreOf 2 K ≤ a2R H := c.pCoreOf_K_le_R h37 h38
  refine ⟨a, x, haK, ha2, haO, hxY, hxK, hx3, hxa, hOR, ?_⟩
  intro w hwK hwa
  have key : ∀ r ∈ a2R H, r * w * r⁻¹ * w⁻¹ ∈ pCoreOf 2 K := by
    intro r hr
    rcases hact r hr with h1 | h2
    · exact h1 w hwK
    · have h3 := h2 w hwK
      have h4 : a * w * a⁻¹ * w⁻¹ ∈ pCoreOf 2 K := by
        have := (pCoreOf 2 K).inv_mem hwa
        simpa [commutatorElement_def, mul_assoc] using this
      have e : r * w * r⁻¹ * w⁻¹ =
          (r * w * r⁻¹ * (a * w * a⁻¹)⁻¹) * (a * w * a⁻¹ * w⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 K).mul_mem h3 h4
  have hw1 : ∀ r ∈ a2R H, w * r * w⁻¹ ∈ a2R H := by
    intro r hr
    have h1 := key r⁻¹ ((a2R H).inv_mem hr)
    have h3 : r⁻¹ * w * r * w⁻¹ ∈ a2R H := by simpa using hOR h1
    rw [show w * r * w⁻¹ = r * (r⁻¹ * (w * r * w⁻¹)) by group]
    refine (a2R H).mul_mem hr ?_
    rw [show r⁻¹ * (w * r * w⁻¹) = r⁻¹ * w * r * w⁻¹ by group]
    exact h3
  have hmap : (a2R H).map (MulAut.conj w).toMonoidHom ≤ a2R H := by
    rintro _ ⟨r, hr, rfl⟩
    exact hw1 r hr
  have heq : (a2R H).map (MulAut.conj w).toMonoidHom = a2R H :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Nat.card_congr (Subgroup.equivMapOfInjective (a2R H) (MulAut.conj w).toMonoidHom
        (MulAut.conj w).injective).toEquiv])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end CFSG.Quasithin.H13.NFa2
