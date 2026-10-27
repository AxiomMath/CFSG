module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.EmptyFaithful.LRed4Orth
public import CFSG.Quasithin.Background.FLc2Cases
public import CFSG.Quasithin.Background.FLcAutMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.G11.P4InspOrth

section Split

variable {V : Type} [CommGroup V]

theorem eq_bot_or_eq_of_irrPlus {Λ : Subgroup (MulAut V)} {U : Subgroup V} (h : U ∈ IrrPlus Λ ⊤)
    (hfix : fixV Λ ⊓ U = ⊥) {J : Subgroup V} (hJ : ∀ a ∈ Λ, ∀ l ∈ J, (a : MulAut V) l ∈ J) (hJU : J ≤ U) :
    J = ⊥ ∨ J = U := by
  obtain ⟨-, -, -, -, hirr⟩ := h
  have hfx : XMod.fixed ↥Λ U = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    have : l ∈ fixV Λ ⊓ U := ⟨fun a ha => hl.2 ⟨a, ha⟩, hl.1⟩
    rw [hfix] at this
    exact this
  have := hirr J (fun a l hl => hJ a a.2 l hl) (by rw [hfx]; exact bot_le) hJU
  rw [hfx] at this
  exact this

theorem card_altDn_eight_mod :
    Nat.card (↥(FFModel.altDn 8).sec ⧸ (FFModel.altDn 8).ker.subgroupOf (FFModel.altDn 8).sec) = 2 ^ 6 := by
  have h1 : Nat.card (↥(FFModel.symDn 8).sec ⧸ (FFModel.symDn 8).ker.subgroupOf (FFModel.symDn 8).sec) =
      Nat.card (Multiplicative p4insporth_V8) := Nat.card_congr LRed4.thetaEquiv.toEquiv
  have h2 : Nat.card (Multiplicative p4insporth_V8) = Nat.card p4insporth_V8 :=
    Nat.card_congr Multiplicative.toAdd
  exact h1.trans (h2.trans LRed4.card_V8)

theorem card_of_alternatingNatural_eight [Finite V] {Λ : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : AlternatingNatural Λ U Z 8) : Nat.card ↥U = 64 * Nat.card ↥Z := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨-, hZU, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk]
    exact Iff.rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  have h2 : Nat.card (↥U ⧸ β.ker) = 2 ^ 6 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv).trans
      card_altDn_eight_mod
  have h3 : Nat.card ↥β.ker = Nat.card ↥Z := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  rw [h1, h2, h3]
  norm_num

theorem not_naturalList2_card [Finite V] {Λ : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hΛ : Nat.card ↥Λ = 20160) (hU : Nat.card ↥U ≠ 64 * Nat.card ↥Z) : ¬ B51NaturalList2 Λ U Z := by
  have hN : Nat.card ↥Λ = 20160 ∨ Nat.card ↥Λ = 9999360 := Or.inl hΛ
  rintro (⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h)
  · exact not_binaryNaturalSL_two1527d hN h
  · exact not_binaryNaturalSp4_1527d hN h
  · exact not_g2Natural1527d hN h
  · refine not_alternatingNatural1527d (n := 6) (by norm_num) ?_ h
    rw [hΛ]
    norm_num [Nat.factorial]
  · exact hU (card_of_alternatingNatural_eight h)
  · exact not_g2NaturalDerived_one1527d hN h
  · exact not_binaryNaturalSL_three1527d hN h

theorem isIntDirect_nd [Finite V] {Λ : Subgroup (MulAut V)}
    (hp2 : ¬ IsIntDirect (commV Λ) (fixV Λ) ⊤ → commV Λ ∈ IrrPlus Λ ⊤ ∧
      B51NaturalList2 Λ (commV Λ) (fixV Λ ⊓ commV Λ))
    (hnd : SumNatDual Λ (commV Λ) 4) (hfix : fixV Λ ⊓ commV Λ = ⊥) :
    IsIntDirect (commV Λ) (fixV Λ) ⊤ := by
  by_contra hn
  obtain ⟨hirr, -⟩ := hp2 hn
  obtain ⟨-, π, U₁, U₂, hdir, hr₁, hr₂⟩ := hnd
  have hinv₁ : ∀ a ∈ Λ, ∀ l ∈ U₁, (a : MulAut V) l ∈ U₁ := fun a ha l hl => hr₁.2.2.2.1 ⟨a, ha⟩ l hl
  have hne₁ : U₁ ≠ ⊥ := by
    obtain ⟨β, hβs, -⟩ := vmodel_of_realizes (natAct (StatedSL 4 (ZMod 2))) hr₁
    obtain ⟨a, ha⟩ := exists_ne_one_nat (n := 4) (by norm_num)
    exact ne_bot_of_surj β hβs a ha
  have hne₂ : U₂ ≠ ⊥ := by
    obtain ⟨β, hβs, -⟩ := vmodel_of_realizes (dualNatAct (StatedSL 4 (ZMod 2))) hr₂
    obtain ⟨a, ha⟩ := exists_ne_one_nat (n := 4) (by norm_num)
    exact ne_bot_of_surj β hβs a ha
  have hU₁ : U₁ ≤ commV Λ := hdir.1 ▸ le_sup_left
  rcases eq_bot_or_eq_of_irrPlus hirr hfix hinv₁ hU₁ with h | h
  · exact hne₁ h
  · apply hne₂
    have h2 : U₂ ≤ U₁ := h ▸ (hdir.1 ▸ le_sup_right)
    rw [eq_bot_iff, ← hdir.2]
    exact le_inf h2 le_rfl

theorem isIntDirect_iso [Finite V] {Λ : Subgroup (MulAut V)} {k : ℕ} (hΛ : Nat.card ↥Λ = 20160) (hk : 1 ≤ k)
    (hp2 : ¬ IsIntDirect (commV Λ) (fixV Λ) ⊤ → commV Λ ∈ IrrPlus Λ ⊤ ∧
      B51NaturalList2 Λ (commV Λ) (fixV Λ ⊓ commV Λ))
    (hdir : DirectSumOfCopies Λ (commV Λ) ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k)
    (hfix : fixV Λ ⊓ commV Λ = ⊥) : IsIntDirect (commV Λ) (fixV Λ) ⊤ := by
  by_contra hn
  obtain ⟨hirr, hlist⟩ := hp2 hn
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hdir
  have hne : ∀ j, I j ≠ ⊥ := by
    intro j
    obtain ⟨β, hβs, -⟩ := vmodel_of_realizes (natAct (StatedSL 4 (ZMod 2))) (hreal j)
    obtain ⟨a, ha⟩ := exists_ne_one_nat (n := 4) (by norm_num)
    exact ne_bot_of_surj β hβs a ha
  have hinv : ∀ j, ∀ a ∈ Λ, ∀ l ∈ I j, (a : MulAut V) l ∈ I j := fun j a ha l hl =>
    (hreal j).2.2.2.1 ⟨a, ha⟩ l hl
  have hIU : ∀ j, I j ≤ commV Λ := fun j => by
    rw [← hsup, bot_sup_eq]
    exact le_iSup I j
  by_cases hk1 : k = 1
  · subst hk1
    have hU : commV Λ = I ⟨0, hk⟩ := by
      rw [← hsup, bot_sup_eq]
      apply le_antisymm
      · exact iSup_le fun j => by
          have : j = ⟨0, hk⟩ := Subsingleton.elim _ _
          rw [this]
      · exact le_iSup I _
    rw [hfix] at hlist
    refine not_naturalList2_card hΛ ?_ hlist
    obtain ⟨β, hβs, hβk, -⟩ := vmodel_of_realizes (natAct (StatedSL 4 (ZMod 2))) (hreal ⟨0, hk⟩)
    have hβi : Function.Injective β :=
      (injective_iff_map_eq_one β).2 fun u hu => Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
    have h16 : Nat.card ↥(I ⟨0, hk⟩) = 2 ^ 4 :=
      (Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)).trans (card_multiplicative_Vt 4)
    rw [hU, h16, Subgroup.card_bot]
    norm_num
  · have hk2 : 2 ≤ k := by omega
    have h0 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) (by norm_num)
    rcases eq_bot_or_eq_of_irrPlus hirr hfix (hinv ⟨0, by omega⟩) (hIU _) with h | h
    · exact hne _ h
    · have h1 : I ⟨1, by omega⟩ ≤ I ⟨0, by omega⟩ := h ▸ hIU _
      have h2 := hind ⟨1, by omega⟩
      have h3 : I ⟨0, by omega⟩ ≤ ⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ ⟨1, by omega⟩), I j :=
        le_sup_of_le_right (le_iSup₂_of_le ⟨0, by omega⟩ h0 le_rfl)
      exact hne _ (eq_bot_iff.2 (h2 ▸ le_inf le_rfl (h1.trans h3)))

end Split

end CFSG.Quasithin.A38c10
