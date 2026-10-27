module

public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C126NatDSL2
public import CFSG.Quasithin.Background.C126NatDProd

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure NatCtx (H T M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hV))) ) : Prop where
  min : MinParabolic H T M
  charTwo : CharTwo H
  red : IsTwoReducedIn H V
  hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  kj : twoResidual H ≤ thompsonJ H
  card : I.card = 1 ∨ I.card = 2
  jeq : autI hV (thompsonJ H) = ⨆ L ∈ I, L
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  ind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  trans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L'
  nat : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n
  sbj : autI hV (baum T) = autI hV (thompsonJ T)
  sylJ : IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H))
  syl : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)

omit [Finite G] in
theorem exists_natCtx {H T M V : Subgroup G} {hV : IsElemAbelian 2 V} (hmin : MinParabolic H T M)
    (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hNat : NatCase H T V hV) :
    ∃ I, NatCtx H T M V hV I := by
  obtain ⟨hKJ, I, hFam, hn2⟩ := hNat
  obtain ⟨hcard, hJeq, hcomm, hind, htrans, -, -, -, h2, -⟩ := hFam
  obtain ⟨hsb, hsylJ, hsyl, -⟩ := h2 fun L hL => (hn2 L hL).imp fun n h => h.2
  exact ⟨I, ⟨hmin, hF, hred, hJ, hKJ, hcard, hJeq, hcomm, hind, htrans, hn2, hsb, hsylJ, hsyl⟩⟩

namespace NatCtx

variable {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtx H T M V hV I)

omit [Finite G] in
include c in
theorem hHN : H ≤ Subgroup.normalizer (V : Set G) := c.red.2.1

omit [Finite G] in
include c in
theorem not_le_centralizer : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun hle =>
  c.hJ ((B6.thompsonJ_le T).trans (c.min.isSylow.1.trans hle))

include c in
theorem cent_le_M : H ⊓ Subgroup.centralizer (V : Set G) ≤ M :=
  (c.min.inf_centralizer_le_kerIn c.red c.not_le_centralizer).trans kerIn_le

omit [Finite G] in
include c in
theorem sylow_star : IsSylowTwoOf (autI hV (baum T)) (⨆ L ∈ I, L) := by
  have h := c.sylJ
  rw [c.jeq, ← c.sbj] at h
  exact h

include c in
theorem rho_le {P : Subgroup G} (hPK : P ≤ twoResidual H ⊔ baum T) :
    autI hV P ≤ ⨆ L ∈ I, L := by
  have hTH := c.min.isSylow.1
  have hSN : baum T ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_left.trans hTH).trans c.hHN
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := (twoResidual_le H).trans c.hHN
  calc autI hV P ≤ autI hV (twoResidual H ⊔ baum T) := autI_mono hV hPK
    _ = autI hV (twoResidual H) ⊔ autI hV (baum T) := autI_sup hV hKN hSN
    _ ≤ autI hV (thompsonJ H) := by
      refine sup_le (autI_mono hV c.kj) ?_
      rw [c.sbj]
      exact autI_mono hV (B6.thompsonJ_le_of_sylow c.min.isSylow)
    _ = ⨆ L ∈ I, L := c.jeq

include c in
theorem not_le_rho_M : ∀ L ∈ I, ¬ L ≤ autI hV M := by
  intro L hL hLM
  have hall : ⨆ L' ∈ I, L' ≤ autI hV M := by
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨t, ht, hLt⟩ := c.trans L hL L' hL'
    rw [← hLt]
    intro x hx
    have h1 := hLM (B1.mem_conjAut.1 hx)
    have htM : t ∈ autI hV M := autI_mono hV c.min.le ht
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ ∈ autI hV M :=
      (autI hV M).mul_mem ((autI hV M).mul_mem htM h1) ((autI hV M).inv_mem htM)
    simpa [mul_assoc] using h2
  have hKM : twoResidual H ≤ M := by
    intro k hk
    have hkH : k ∈ H := twoResidual_le H hk
    have hmem : convI hV ⟨k, c.hHN hkH⟩ ∈ autI hV M :=
      hall (c.jeq ▸ autI_mono hV c.kj (convI_mem_autI hV hk (c.hHN hkH)))
    obtain ⟨m, hm, hconv⟩ := (mem_autI hV).1 hmem
    have h1 : convI hV (⟨k, c.hHN hkH⟩ * m⁻¹) = 1 := by rw [map_mul, map_inv, hconv, mul_inv_cancel]
    have h2 : k * (m : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hmH : (m : G) ∈ H := c.min.maximal.1.le (hm : (m : G) ∈ M)
    have h3 : k * (m : G)⁻¹ ∈ M :=
      c.cent_le_M ⟨H.mul_mem hkH (H.inv_mem hmH), h2⟩
    have := M.mul_mem h3 hm
    simpa using this
  have hH : H ≤ M := by
    rw [← sup_twoResidual_eq c.min.isSylow]
    exact sup_le c.min.le hKM
  exact absurd (lt_of_le_of_lt hH c.min.maximal.1) (lt_irrefl _)

omit [Finite G] in
theorem exists_equiv_sl2 {L : Subgroup (MulAut (IntMod V hV))} {C : Subgroup (IntMod V hV)}
    {n : ℕ} (h : IsL2Natural L C n) :
    1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L ≃* SL(2, F)) := by
  obtain ⟨hn, F, iF, iFin, hF, e, -⟩ := h
  exact ⟨hn, F, iF, Finite.of_fintype F, by rw [Nat.card_eq_fintype_card]; exact hF, ⟨e⟩⟩

include c in
theorem le_normalizer_star {X : Subgroup (MulAut (IntMod V hV))} (hX : X ≤ ⨆ L ∈ I, L)
    (hSX : autI hV (baum T) ≤ X) (hno : ∀ L ∈ I, ¬ L ≤ X) :
    X ≤ Subgroup.normalizer
      ((autI hV (baum T) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
  classical
  have hS := c.sylow_star
  rcases c.card with h1 | h2
  · obtain ⟨L, hIL⟩ := Finset.card_eq_one.1 h1
    subst hIL
    have hLI : L ∈ ({L} : Finset (Subgroup (MulAut (IntMod V hV)))) := Finset.mem_singleton_self L
    have hsup : (⨆ L' ∈ ({L} : Finset (Subgroup (MulAut (IntMod V hV)))), L') = L := by simp
    rw [hsup] at hS hX
    obtain ⟨n, -, hnat⟩ := c.nat L hLI
    obtain ⟨hn, F, iF, iFin, hF, ⟨e⟩⟩ := exists_equiv_sl2 hnat
    rcases sylow_dichotomy_of_equiv_sl2 hn hF e hS hX hSX with h | h
    · exact absurd (h ▸ le_rfl) (hno L hLI)
    · exact h
  · obtain ⟨L₁, L₂, hne, hIL⟩ := Finset.card_eq_two.1 h2
    subst hIL
    have hm₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
    have hm₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
    have hsup : (⨆ L ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))), L) = L₁ ⊔ L₂ := by
      apply le_antisymm
      · refine iSup₂_le fun L hL => ?_
        rcases Finset.mem_insert.1 hL with rfl | hL
        · exact le_sup_left
        · rw [Finset.mem_singleton.1 hL]
          exact le_sup_right
      · exact sup_le (le_iSup₂_of_le L₁ hm₁ le_rfl) (le_iSup₂_of_le L₂ hm₂ le_rfl)
    have hcomm := c.comm L₁ hm₁ L₂ hm₂ hne
    have hdisj : L₁ ⊓ L₂ = ⊥ := by
      refine le_bot_iff.1 ((inf_le_inf_left L₁ ?_).trans (c.ind L₁ hm₁).le)
      exact le_iSup₂_of_le L₂ hm₂ (le_iSup (fun _ : L₂ ≠ L₁ => L₂) hne.symm)
    rw [hsup] at hS hX
    obtain ⟨n₁, -, hnat₁⟩ := c.nat L₁ hm₁
    obtain ⟨n₂, -, hnat₂⟩ := c.nat L₂ hm₂
    obtain ⟨hn₁, F₁, iF₁, iFin₁, hF₁, ⟨e₁⟩⟩ := exists_equiv_sl2 hnat₁
    obtain ⟨hn₂, F₂, iF₂, iFin₂, hF₂, ⟨e₂⟩⟩ := exists_equiv_sl2 hnat₂
    exact le_normalizer_of_two_factors hcomm hdisj hS hX hSX
      (fun Z hZ hSZ => sylow_dichotomy_of_equiv_sl2 hn₁ hF₁ e₁
        (isSylowTwoOf_inf_left hcomm hS) hZ hSZ)
      (fun Z hZ hSZ => sylow_dichotomy_of_equiv_sl2 hn₂ hF₂ e₂
        (isSylowTwoOf_inf_right hcomm hS) hZ hSZ)
      (hno L₁ hm₁) (hno L₂ hm₂)

end NatCtx

end CFSG.Quasithin.C126.Nat
