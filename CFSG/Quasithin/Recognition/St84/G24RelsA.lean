module

public import CFSG.Quasithin.Recognition.St84.G24Checks
public import CFSG.Certificates.WordPresentation
import CFSG.Quasithin.Recognition.St84.G24Tools

public section

namespace CFSG.Quasithin.St84

theorem signedProd_relsA {X : Type*} [Group X] {a b k : X} (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 5 = 1) (hk : k ^ 3 = 1) (hak : a * k = k * a) (hbk : b * k = k * b) :
    ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd ![a, b, k] w = 1 := by
  intro w hw
  simp only [G24Pc.relsA, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [CFSG.Certificates.signedProd, pow_two] using ha
  · simpa [CFSG.Certificates.signedProd, pow_succ', pow_two] using hb
  · simpa [CFSG.Certificates.signedProd, pow_succ, pow_two, mul_assoc] using hab
  · simpa [CFSG.Certificates.signedProd, pow_succ', pow_two] using hk
  · have h : a * (k * (a⁻¹ * k⁻¹)) = 1 := by
      rw [← mul_assoc, hak]
      group
    simpa [CFSG.Certificates.signedProd] using h
  · have h : b * (k * (b⁻¹ * k⁻¹)) = 1 := by
      rw [← mul_assoc, hbk]
      group
    simpa [CFSG.Certificates.signedProd] using h

theorem exists_mulEquiv_relsA {X X' : Type*} [Group X]
    [Group X'] (f : Fin 3 → X) (f' : Fin 3 → X')
    (hf : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd f w = 1)
    (hf' : ∀ w ∈ CFSG.Quasithin.St84.G24Pc.relsA, CFSG.Certificates.signedProd f' w = 1)
    (hgen : Subgroup.closure (Set.range f) = ⊤) (hgen' : Subgroup.closure (Set.range f') = ⊤)
    (hcard : Nat.card X = 180) (hcard' : Nat.card X' = 180) :
    ∃ e : X ≃* X', ∀ j, e (f j) = f' j := by
  refine ⟨(pcIso pc_checkA f hf hgen hcard).symm.trans
    (pcIso pc_checkA f' hf' hgen' hcard'), fun j => ?_⟩
  rw [MulEquiv.trans_apply, ← pcIso_of pc_checkA f hf hgen hcard j,
    MulEquiv.symm_apply_apply, pcIso_of pc_checkA f' hf' hgen' hcard' j]

end CFSG.Quasithin.St84
