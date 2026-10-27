module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Conj
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryAut
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryO

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem exists_aut_of_nearSimple
    (h : NearSimple p X) : ∃ f : MulAut X, orderOf f = p := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    obtain ⟨f', hf'⟩ := exists_aut_psl2Even h.prime hcop
    exact ⟨MulAut.congr e.symm f', by rw [orderOf_congr, hf']⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    obtain ⟨f', hf'⟩ := exists_aut_psl2Three h.prime hcop
    exact ⟨MulAut.congr e.symm f', by rw [orderOf_congr, hf']⟩
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    obtain ⟨f', hf'⟩ := exists_aut_sz h.prime hcop
    exact ⟨MulAut.congr e.symm f', by rw [orderOf_congr, hf']⟩
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    obtain ⟨f', hf'⟩ := exists_aut_psu3 h.prime hcop
    exact ⟨MulAut.congr e.symm f', by rw [orderOf_congr, hf']⟩

theorem frame_of_nearSimple
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    ∃ ℓ, Frame p ℓ f := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ⟨3, Frame.of_model e (fun f' hf' => frame_psl2Even h.prime hcop f' hf') hf⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ⟨2, Frame.of_model e (fun f' hf' => frame_psl2Three h.prime hcop f' hf') hf⟩
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    exact ⟨5, Frame.of_model e (fun f' hf' => frame_sz h.prime hcop hY f' hf') hf⟩
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    exact ⟨3, Frame.of_model e (fun f' hf' => frame_psu3 h.prime hcop hY f' hf') hf⟩

omit [Finite X] in
theorem itemC_of_nearSimple
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    ItemC p f := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemC.of_model e (fun f' hf' => itemC_psl2Even h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemC.of_model e (fun f' hf' => itemC_psl2Three h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemC.of_model e (fun f' hf' => itemC_sz h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemC.of_model e (fun f' hf' => itemC_psu3 h.prime hcop f' hf') hf

omit [Finite X] in
theorem itemG_of_nearSimple
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    ItemG p f := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemG.of_model e (fun f' hf' => itemG_psl2Even h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemG.of_model e (fun f' hf' => itemG_psl2Three h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    exact ItemG.of_model e (fun f' hf' => itemG_sz h.prime hcop hY f' hf') hf
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemG.of_model e (fun f' hf' => itemG_psu3 h.prime hcop f' hf') hf

theorem itemO_of_nearSimple
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    ItemO f := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemO.of_model e (fun f' hf' => itemO_psl2Even h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    exact ItemO.of_model e (fun f' hf' => itemO_psl2Three h.prime hcop f' hf') hf
  · have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    exact ItemO.of_model e (fun f' hf' => itemO_sz h.prime hcop hY f' hf') hf
  · have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]; exact h.coprime
    have hY := TransportA.nearPSolvable_of_mulEquiv e h.nearPSolvable
    exact ItemO.of_model e (fun f' hf' => itemO_psu3 h.prime hcop hY f' hf') hf

end CFSG.SignalizerFunctorTheorem.McBride
