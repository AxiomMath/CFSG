module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoSys
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoCard

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W}

theorem exists_arc_card3 [Nonempty W] (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) :
    ∀ n : ℕ, Nonempty (Arc Γ n)
  | 0 => ⟨⟨fun _ => Classical.arbitrary W, fun i hi => by omega, fun i hi => by omega⟩⟩
  | n + 1 => by
    obtain ⟨a⟩ := exists_arc_card3 hcard n
    obtain ⟨w, hw1, hw2⟩ := exists_mem_extSet hcard a
    exact ⟨snocArc a w hw1 hw2⟩

variable {H : Type} [Group H] [MulAction H W] {s : ℕ}

theorem isTutteSys_of_regData [Nonempty W] (R : RegData Γ H s) (hs : 2 ≤ s) :
    ∃ (r l ξ : H) (Hs : ℕ → Subgroup H), IsTutteSys s r l ξ Hs := by
  obtain ⟨a⟩ := exists_arc_card3 (Γ := Γ) R.card3 s
  obtain ⟨r, l, hr, hl, hne, hcases⟩ := R.exists_rl hs a
  obtain ⟨ξ, hξ, hξ2⟩ := R.exists_xi a
  have C : Config a r l ξ := ⟨hr, hl, hne, hcases, hξ, hξ2⟩
  refine ⟨r, l, ξ, chain a H, ?_⟩
  exact
  { one_le := by omega
    zero := chain_zero R a
    mono := fun i _ => chain_mono a i
    card_lt := R.card_chain_lt a
    card_s := R.card_chain_s a
    x_mem := fun i hi => mem_chain.2 fun j hj => RegData.tx_smul_vert C hi hj
    x_not_mem := fun i hi1 his h =>
      R.tx_smul_vert_ne C hi1 his (mem_chain.1 h (s - i + 1) (by omega))
    xs_sq_not_mem := R.xs_sq_not_mem hs C
    xs_cube_mem := R.xs_cube_mem hs C
    xi_sq := hξ2
    xi_case := RegData.xi_case C
    rel := R.rel hs C
    inter := fun i hi => R.inter C hi }

theorem regData_of_regular (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) (H₀ : Type) [Group H₀]
    [MulAction H₀ W] (hadj : ∀ (h : H₀) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (s : ℕ) (hs : 1 ≤ s)
    (htrans : ∀ P Q : Arc Γ s, ∃ h : H₀, ∀ i, i ≤ s → h • P.vert i = Q.vert i)
    (hfaith : ∀ (P : Arc Γ s) (h : H₀), (∀ i, i ≤ s → h • P.vert i = P.vert i) →
      ∀ w : W, h • w = w) :
    RegData Γ (MulAction.toPermHom H₀ W).range s where
  one_le := hs
  card3 := hcard
  adj := by
    rintro ⟨g, h, rfl⟩ u v
    simpa using hadj h u v
  trans := by
    intro P Q
    obtain ⟨h, hh⟩ := htrans P Q
    exact ⟨⟨MulAction.toPermHom H₀ W h, h, rfl⟩, fun i hi => by simpa using hh i hi⟩
  faith := by
    rintro P ⟨g, h, rfl⟩ hg
    refine Subtype.ext (Equiv.ext fun w => ?_)
    have := hfaith P h (fun i hi => by simpa using hg i hi) w
    simpa using this

theorem tutte_regular_of_calculus (hC : TutteCalculus) : TutteRegular := by
  intro W Γ htree hcard H _ _ hadj s hs htrans hfaith
  by_cases h5 : s ≤ 5
  · exact h5
  · have : Nonempty W := htree.connected.nonempty
    obtain ⟨r, l, ξ, Hs, hsys⟩ := isTutteSys_of_regData
      (regData_of_regular hcard H hadj s hs htrans hfaith) (by omega)
    exact hC _ s r l ξ Hs hsys

end CFSG.Quasithin.Fan86.Tutte.Geo
