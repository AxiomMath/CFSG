module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tf
public import CFSG.Quasithin.Vol2.Ch10SecK2Ti
public import CFSG.Quasithin.Vol2.Ch10SecK2Tj
public import CFSG.Quasithin.Vol2.Ch10SecK2Tk
public import CFSG.Quasithin.Vol2.Ch11SecAKB1
public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecAKC2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA

section Data

variable {W : Type} [CommGroup W] [Finite W]

structure TorusData (H : Subgroup (MulAut W)) (Z : Subgroup W) (q : ℕ) : Prop where
  hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z
  flag : ∀ {Pst : Subgroup ↥H}, IsMaxParabolic2 ⊤ Pst → ∀ {S₀ : Subgroup ↥H},
    IsSylowTwoOf S₀ ⊤ → Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst →
    ∃ (U : Subgroup W) (i : ℕ), (i = 1 ∨ i = 2) ∧ IsFlagW H (S₀.map H.subtype) Z q i U ∧
      (perfectCore Pst).map H.subtype = perfectCore (H ⊓ stabW U)
  radical : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ U : Subgroup W,
    IsFlagW H S Z q 1 U → RadicalFixes H Z U
  point : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ U : Subgroup W,
    IsFlagW H S Z q 1 U → ∀ h ∈ perfectCore (H ⊓ stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z
  line : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ U : Subgroup W,
    IsFlagW H S Z q 2 U → LineFacts H Z U
  torus : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ U : Subgroup W,
    IsFlagW H S Z q 2 U → LineTorusFacts H S Z U q
  levi : ∀ S : Subgroup (MulAut W), IsSylowTwoOf S H → ∀ (i : ℕ) (U : Subgroup W),
    (i = 1 ∨ i = 2) → IsFlagW H S Z q i U → ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q ∧ Nonempty (↥(perfectCore (H ⊓ stabW U)) ⧸
        CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ≃* Matrix.SpecialLinearGroup (Fin 2) K)

variable {H : Subgroup (MulAut W)} {Z : Subgroup W} {q : ℕ}

structure ValidM (S L : Subgroup (MulAut W)) (q : ℕ) (M : Subgroup W) : Prop where
  hS : ∀ s ∈ S, ∀ x ∈ M, s x ∈ M
  hL : ∀ s ∈ L, ∀ x ∈ M, s x ∈ M
  hc : M ≤ commS L M
  hO : ∀ x : ↥L, x ∈ CFSG.pCore 2 ↥L → ∀ m ∈ M, (x : MulAut W) m = m
  hcard : (fixV L ⊓ M).relIndex M ≤ q ^ 2

theorem line_of_data (hW : ∀ w : W, w ^ 2 = 1) (hD : TorusData H Z q) {Pst : Subgroup ↥H}
    (hPst : IsMaxParabolic2 ⊤ Pst) {S₀ : Subgroup ↥H} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hPS : Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst) {M₀ : Subgroup W}
    (hM₀ : ValidM (S₀.map H.subtype) ((perfectCore Pst).map H.subtype) q M₀) (hM₀ne : M₀ ≠ ⊥) :
    ∃ U : Subgroup W, IsFlagW H (S₀.map H.subtype) Z q 2 U ∧
      (perfectCore Pst).map H.subtype = perfectCore (H ⊓ stabW U) ∧ LineFacts H Z U ∧
      LineTorusFacts H (S₀.map H.subtype) Z U q ∧
      ∀ M : Subgroup W, ValidM (S₀.map H.subtype) ((perfectCore Pst).map H.subtype) q M →
        M ≠ ⊥ → M = commS (perfectCore (H ⊓ stabW U)) U := by
  obtain ⟨U, i, hi, hU, hL⟩ := hD.flag hPst hS₀ hPS
  have hS : IsSylowTwoOf (S₀.map H.subtype) H := isSylowTwoOf_map_subtype hS₀
  rw [hL] at hM₀ ⊢
  rcases hi with rfl | rfl
  ·
    exfalso
    have hMU : M₀ ≤ U := fun m hm => hD.radical _ hS U hU m fun x hx => by
      rw [hM₀.hO x hx m hm, mul_inv_cancel]
      exact Z.one_mem
    have hfix := KGNat.fix_of_perfect (perfectCore_perfect (H ⊓ stabW U))
      (fun h hh z hz => hD.hZ h ((perfectCore_le _ hh).1) z hz) (hD.point _ hS U hU)
    apply hM₀ne
    refine eq_bot_iff.mpr (le_trans hM₀.hc ((Subgroup.closure_le _).mpr ?_))
    rintro _ ⟨s, hs, m, hm, rfl⟩
    rw [hfix s hs m (hMU hm), mul_inv_cancel]
    exact Subgroup.one_mem _
  ·
    have hLF := hD.line _ hS U hU
    have hLT := hD.torus _ hS U hU
    exact ⟨U, hU, rfl, hLF, hLT, fun M hM hMne =>
      eq_commS_of_line hW hD.hZ hS hU hLF hLT hM.hS hM.hL hM.hc hM.hcard hMne⟩

omit [Finite W] in
theorem levi_of_data (hD : TorusData H Z q) {Pst : Subgroup ↥H} (hPst : IsMaxParabolic2 ⊤ Pst)
    {S₀ : Subgroup ↥H} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hPS : Subgroup.normalizer (S₀ : Set ↥H) ≤ Pst) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nonempty (↥((perfectCore Pst).map H.subtype) ⧸
        CFSG.pCore 2 ↥((perfectCore Pst).map H.subtype) ≃*
          Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨U, i, hi, hU, hL⟩ := hD.flag hPst hS₀ hPS
  rw [hL]
  exact hD.levi _ (isSylowTwoOf_map_subtype hS₀) i U hi hU

end Data

section Families

variable {K : Type} [Field K] [Finite K] {m : ℕ} {W : Type} [CommGroup W] [Finite W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W}

theorem torusData_SL3 (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (hW2 : ∀ w : W, w ^ 2 = 1)
    {π : ↥(Assembly.LowTwoRank.StatedSL 3 K) →* ↥H}
    (hR : (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)).RealizesVia H ⊤ Z π)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) : TorusData H Z (2 ^ m) :=
  ⟨hHZ, fun hPst _ hS₀ hPS => perfectCore_eq_flag_SL3 hm hK hW2 hR hHZ hPst hS₀ hPS,
    fun S hS U hU => KGNat.factRadicalFixedSL3_holds K m hm hK W hW2 H Z π hR S hS U hU,
    fun S hS U hU => KGNat.factPointSL3_holds K m hm hK W hW2 H Z π hR S hS U hU,
    fun S hS U hU => KGNat.factLineSL3_holds K m hm hK W hW2 H Z π hR hHZ S hS U hU,
    fun _ hS _ hU => lineTorusFacts_SL3 hm hK hW2 hR hS hU,
    fun S hS i U hi hU => ⟨K, inferInstance, inferInstance, hK,
      KGNat.factLeviSL3_holds K m hm hK W hW2 H Z π hR S hS i U hi hU⟩⟩

theorem torusData_Sp4 (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (hW2 : ∀ w : W, w ^ 2 = 1)
    {π : ↥(Assembly.LowTwoRank.StatedSp 2 K) →* ↥H}
    (hR : (FFModel.nat (Assembly.LowTwoRank.StatedSp 2 K)).RealizesVia H ⊤ Z π)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) : TorusData H Z (2 ^ m) :=
  ⟨hHZ, fun hPst _ hS₀ hPS => perfectCore_eq_flag_Sp4 hm hK hW2 hR hHZ hPst hS₀ hPS,
    fun S hS U hU => KGNat.factRadicalFixedSp4_holds K m hm hK W hW2 H Z π hR S hS U hU,
    fun S hS U hU => KGNat.factPointSp4_holds K m hm hK W hW2 H Z π hR S hS U hU,
    fun S hS U hU => (KGNat.factLineSp4_holds K m hm hK W hW2 H Z π hR hHZ S hS U hU).1,
    fun _ hS _ hU => lineTorusFacts_Sp4 hm hK hW2 hR hS hU,
    fun S hS i U hi hU => ⟨K, inferInstance, inferInstance, hK,
      KGNat.factLeviSp4_holds K m hm hK W hW2 H Z π hR S hS i U hi hU⟩⟩

theorem torusData_G2 (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (hW2 : ∀ w : W, w ^ 2 = 1)
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H}
    (hR : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) : TorusData H Z (2 ^ m) :=
  ⟨hHZ, fun hPst _ hS₀ hPS => perfectCore_eq_flag_G2 hm hK hW2 hR hHZ hPst hS₀ hPS,
    fun S hS U hU => factRadicalFixedG2_holds K m hm hK W hW2 H Z π hR S hS U hU,
    fun S hS U hU => Ch11.G2Q8.factPointG2A_holds K m hm hK W hW2 H Z π hR S hS U hU,
    fun S hS U hU => (factLineG2_holds K m hm hK W hW2 H Z π hR hHZ S hS U hU).1,
    fun _ hS _ hU => lineTorusFacts_G2 hm hK hW2 hR hS hU,
    fun S hS i U hi hU => ⟨K, inferInstance, inferInstance, hK,
      Ch11.G2Q8.factLeviG2_holds K m hm hK W hW2 H Z π hR S hS i U hi hU⟩⟩

end Families

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
