module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover CFSG.Assembly
  CFSG.Assembly.RankThreeEven

theorem torus_central_cover_witness {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    {T : Type*} [Group T] (φ : Y →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (θ : Multiplicative (Fin m → ZMod p) →* T) (hθ : Function.Injective θ)
    (hswap : ∀ i j : Fin m, i ≠ j → ∃ g : T,
      g * θ (Multiplicative.ofAdd (Pi.single i 1)) * g⁻¹ =
          θ (Multiplicative.ofAdd (Pi.single j 1)) ∧
        g * θ (Multiplicative.ofAdd (Pi.single j 1)) * g⁻¹ =
          θ (Multiplicative.ofAdd (Pi.single i 1)))
    (E : Subgroup (Multiplicative (Fin m → ZMod p))) {k : ℕ} (hE : p ^ k ≤ Nat.card E) {z : T}
    (hz : orderOf z = 2) (hzE : ∀ a ∈ E, Commute z (θ a)) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ k ∧ k ≤ localRank p G := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : NeZero p := ⟨hp.ne_zero⟩
  set D := θ.range with hD
  have hbasis : ∀ i j, liftComm φ hφ (θ (Multiplicative.ofAdd (Pi.single i 1)))
      (θ (Multiplicative.ofAdd (Pi.single j 1))) = 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact liftComm_self hφ _
    obtain ⟨g, hg1, hg2⟩ := hswap i j hij
    exact liftComm_eq_one_of_conj_swap hφ hker hodd ((Commute.all _ _).map θ)
      (by rw [← map_pow, pow_eq_one_of_zmod, map_one]) g hg1 hg2
  have hall : ∀ a b, liftComm φ hφ (θ a) (θ b) = 1 :=
    liftComm_eq_one_of_closure hφ hker θ closure_range_single_eq_top (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hbasis i j)
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_liftComm_eq_one hφ hker (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact hall a b) hx hy
  have hDp : ∀ x ∈ E.map θ, x ^ p = 1 := by
    rintro _ ⟨a, -, rfl⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  have hle : E.map θ ≤ D := Subgroup.map_le_range _ _
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
    central_cover_involution_witness Y hφ hker hp hp2 (D := E.map θ) hDp
      (fun x hx y hy => hF x (Subgroup.comap_mono hle hx) y (Subgroup.comap_mono hle hy))
      (by rw [Subgroup.card_map_of_injective hθ]; exact hE) hz (by
        rintro _ ⟨a, ha, rfl⟩
        exact hzE a ha)
  exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank⟩

end CFSG.RankThree.PartOne.KCSymplectic
