module

public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Model

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.NearModels

theorem sz_card_pSubgroup_dvd (n : ℕ) (hp : (2 * n + 1).Prime)
    (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (P : Subgroup (MulAut (Sz n))) (hP : IsPGroup (2 * n + 1) P) : Nat.card P ∣ 2 * n + 1 := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_prime_one hp)
  obtain ⟨E⟩ := Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  have hK : Nat.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) :=
    GaloisField.card 2 (2 * n + 1) (by omega)
  have h := Suzuki.suzukiGroup_card_pSubgroup_dvd hn hK hp (by rwa [← Nat.card_congr E.toEquiv])
    (P.map (MulAut.congr E).toMonoidHom) (hP.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr E).injective] at h

theorem sz_fixedSubgroup_mulEquiv (n : ℕ) (hp : (2 * n + 1).Prime)
    (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (f : MulAut (Sz n)) (hf : orderOf f = 2 * n + 1) :
    Nonempty (signalizerFixedSubgroup f ≃* Sz 0) := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_prime_one hp)
  obtain ⟨E⟩ := Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  obtain ⟨e₀⟩ := Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
  have hK : Nat.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) :=
    GaloisField.card 2 (2 * n + 1) (by omega)
  obtain ⟨e⟩ := Suzuki.nonempty_fixedSubgroup_suzukiGroup hn hK hp
    (by rwa [← Nat.card_congr E.toEquiv]) (MulAut.congr E f)
    ((orderOf_injective (MulAut.congr E).toMonoidHom (MulAut.congr E).injective f).trans hf)
  exact ⟨((Suzuki.fixedEquivOfMulEquiv E f).trans e).trans e₀⟩

end CFSG.SignalizerFunctorTheorem.NearModels
