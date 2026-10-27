module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312G
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313He
public import CFSG.Quasithin.Vol2.Ch3Sec3L2pSylowNorm
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native (A36StrongCat)
open scoped Pointwise

namespace L3312

@[expose] def Fact3312Nonquasi : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B L : Subgroup X), B ≤ L → A312Nonquasi B L →
    A36StrongCat L → Type3312R (ModO2 B) → OddNorm ↥L (B.subgroupOf L)

structure Facts3312 : Prop where
  j1 : FactJ1Norm3312
  j2 : FactJ2Norm3312
  lie2 : FactLie2Norm3312
  l3eps : FactL3EpsNorm3312
  nonquasi : Fact3312Nonquasi
  l42 : FactAutSylowL42
  l52 : FactAutSylowL52
  a7 : FactAutSylowA7
  l2sq : FactAutSylowL2Sq
  l2four : FactL2pSylowFour
  l2outer : FactAutL2pOuter
  m11 : FactAutSylowM11
  m22 : FactAutSylowM22
  m23 : FactAutSylowM23
  m24 : FactAutSylowM24
  j4 : FactAutSylowJ4
  hs : FactAutSylowHS
  he : FactAutHeSylow
  ru : FactAutSylowRu

namespace Type3312R

theorem false_of_card {X : Type} [Group X] [Finite X] (h : Type3312R (X ⧸ CFSG.pCore 2 X))
    {N : ℕ} (hN : N = 360 ∨ N = 1080) (hX : Nat.card X = N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X)
  rw [hk, hX] at h1
  exact h.false_of_two_pow_mul hN (by rw [mul_comm]; exact h1.symm)

theorem false_of_isAlt_six {X : Type} [Group X] [Finite X]
    (h : Type3312R (X ⧸ CFSG.pCore 2 X)) (hX : IsAlt 6 X) : False := by
  obtain ⟨e⟩ := hX
  refine h.false_of_card (Or.inl rfl) ?_
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem false_of_isHat_six {X : Type} [Group X] [Finite X]
    (h : Type3312R (X ⧸ CFSG.pCore 2 X)) (hX : IsHat X (alternatingGroup (Fin 6))) : False := by
  obtain ⟨-, h3, ⟨e⟩⟩ := hX
  refine h.false_of_card (Or.inr rfl) ?_
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 6),
    Fintype.card_fin, h3] at h1
  rw [h1]
  decide

end Type3312R

theorem oddNorm_or_j1 (hF : Facts3312)
    {X : Type} [Group X] [Finite X] {B L : Subgroup X} (hBL : B ≤ L)
    (htype : Type3312R (ModO2 B)) (hL36 : A36StrongCat L)
    (h : B = L ∨ A312Case B L ∨ A312Nonquasi B L) :
    A312C15 B L ∨ OddNorm ↥L (B.subgroupOf L) := by
  have eB : ↥B ≃* ↥(B.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hBL).symm
  rcases h with rfl | h | h
  · right
    rw [Subgroup.subgroupOf_self]
    exact oddNorm_top _
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    ·
      exact Or.inr (oddNorm_lie2 hF.lie2 h)
    ·
      obtain ⟨f, hf, -⟩ := h
      exact (htype.not_isSz hf).elim
    ·
      obtain ⟨-, hL, -⟩ := h
      rcases hL with hL | hL
      · exact Or.inr (AutSylowSelfNorm.oddNorm (hF.l42 _ hL) _)
      · exact Or.inr (AutSylowSelfNorm.oddNorm (hF.l52 _ hL) _)
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.l52 _ h.2.1) _)
    ·
      rcases h.2 with hL | hL
      · exact Or.inr (AutSylowSelfNorm.oddNorm (hF.a7 _ hL) _)
      · exact Or.inr (oddNorm_of_isHat hL (fun W _ _ e => hF.a7 W e) _)
    ·
      rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
      · exact Or.inr (AutSylowSelfNorm.oddNorm (hF.a7 _ hL) _)
      · exact Or.inr (oddNorm_of_isHat hL (fun W _ _ e => hF.a7 W e) _)
    ·
      rcases h with ⟨p, hp, hp3, -, hL⟩ | ⟨hB5, p, hp, hL, h5, h8⟩
      · exact Or.inr (AutSylowSelfNorm.oddNorm (hF.l2sq p hp hp3 _ hL) _)
      · have hp3 : 3 < p := by
          by_contra hle
          push Not at hle
          interval_cases p <;> omega
        exact Or.inr (oddNorm_psl2_alt5 factL2pSylowNorm_holds hF.l2four hF.l2outer hp hp3 h8 hL
          (IsAlt.of_mulEquiv eB hB5))
    ·
      rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB6, -⟩ | ⟨hB6, -⟩
      · right
        intro A S hA hS hSB d hd hodd
        exact hF.l3eps p hp hp3 s _ hL A S _ hA hS (IsSL2.of_mulEquiv eB hB) hSB d hd hodd
      · exact (Type3312R.false_of_isAlt_six htype hB6).elim
      · exact (Type3312R.false_of_isHat_six htype hB6).elim
    ·
      obtain ⟨p, hp, hp3, hext, -⟩ := h
      exact (Type3312R.not_isExt_elemAbelian htype hp (by omega) hext).elim
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.m11 _ h.2) _)
    ·
      rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
      · exact Or.inr (AutSylowSelfNorm.oddNorm (hF.m22 _ hL) _)
      · exact Or.inr (oddNorm_of_isHat hL (fun W _ _ e => hF.m22 W e) _)
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.m23 _ h.2) _)
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.m24 _ h.2) _)
    ·
      exact Or.inl h
    ·
      right
      intro A S hA hS hSB d hd hodd
      exact hF.j2 _ h.2 A S _ hA hS
        (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsExtraspecial2.of_mulEquiv e h)
          (fun _ _ _ _ e h => IsAlt.of_mulEquiv e h) eB h.1) hSB d hd hodd
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.j4 _ h.1) _)
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.hs _ h.2) _)
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.he _ h.2) _)
    ·
      exact Or.inr (AutSylowSelfNorm.oddNorm (hF.ru _ h.2.2) _)
  · exact Or.inr (hF.nonquasi X B L hBL h hL36 htype)

end L3312

end CFSG.Quasithin.H13
