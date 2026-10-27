module

public import CFSG.Quasithin.EmptyFaithful.S153LNdTrans
public import CFSG.Quasithin.EmptyFaithful.S153LNdNat
public import CFSG.Quasithin.EmptyFaithful.S153LNdD8
public import CFSG.Quasithin.Background.S1549EA
public import CFSG.Quasithin.Background.FLcLnSetup
public import CFSG.Quasithin.EmptyFaithful.S151ZQ

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.FLc

namespace S153L

theorem lnSumNatDual_holds (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) :
    S1549E.LnSumNatDual := by
  intro V _ _ hV X L S P₀ z hiso hLX hLn hS hXLS hne hO2 hB51hyp hpar hP₀n hmax hSz hgen hCz
  have hXn : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_conj_mem hLn
  have hBL : IsSylowTwoOf (S ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLX hXn
  obtain ⟨iso⟩ := hiso
  have hL : Nat.card ↥L = 20160 := by
    rw [Nat.card_congr iso.toEquiv]
    exact card_statedSL_four_zmod1527d
  obtain ⟨D, hBP₀, hP₀L, x₀, hx₀, hx₀P, hx₀u⟩ := FLc.ln_setup (n := 4) (by norm_num)
    (iso.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm)
    hLX hLn hS hpar hP₀n
  have hP₀card : Nat.card ↥P₀ = 192 := by
    have hmodel : D.model P₀ = FLc.QI 4 (D.cutsOf P₀) :=
      FLc.eq_QI_cuts ((D.Ut_le_model_iff inf_le_right).2 hBP₀)
    have hcuts : D.cutsOf P₀ = FLc.nodeSet 4 \ {x₀} := by
      ext y
      simp only [Set.mem_sdiff, FLc.mem_nodeSet, Set.mem_singleton_iff]
      constructor
      · intro hy
        exact ⟨D.isNode_of_mem_cutsOf hy, fun h => hx₀P (h ▸ hy)⟩
      · rintro ⟨hyn, hyx⟩
        by_contra hy
        exact hyx (hx₀u y hyn hy)
    have hidx := FLc.index_single (n := 4) hx₀
    have hUt : Nat.card ↥(FLc.Ut 4) = 64 := by
      have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular (K := ZMod 2) 4
      rw [Nat.card_zmod] at this
      simpa using this
    have hUle : FLc.Ut 4 ≤ D.model P₀ := (D.Ut_le_model_iff inf_le_right).2 hBP₀
    have h1 := Subgroup.relIndex_mul_card (FLc.Ut 4) (D.model P₀)
    rw [inf_of_le_left hUle, hmodel, hcuts, hidx, hUt] at h1
    rw [← D.card_model hP₀L, hmodel, hcuts, ← h1]
  have hLP₀ : ∀ g ∈ L, g ∈ P₀ ⊔ S → g ∈ P₀ := by
    intro l hl hlPS
    obtain ⟨p, hp, t, ht, rfl⟩ := FLc.mem_sup_prod_of_conj hP₀n l hlPS
    have htL : t ∈ L := by
      have := L.mul_mem (L.inv_mem (hP₀L hp)) hl
      simpa [mul_assoc] using this
    exact P₀.mul_mem hp (hBP₀ ⟨ht, htL⟩)
  obtain ⟨u, w, hzuw, hu, hw, hSu⟩ := exists_split_of_fixed hV hLX hLn hS hXLS hSz
  have hCu : ∀ g ∈ L, (g : MulAut V) u = u → g ∈ P₀ := fun g hg hgu =>
    hLP₀ g hg (hCz g (hLX hg) (by rw [hzuw, map_mul, hgu, hw g (hLX hg)]))
  have hnone : ∀ H : Subgroup (MulAut V), H ≤ L → (∀ g ∈ H, (g : MulAut V) u = u) →
      Nat.card ↥H ≤ 192 := by
    intro H hHL hHu
    have : H ≤ P₀ := fun g hg => hCu g (hHL hg) (hHu g hg)
    rw [← hP₀card]
    exact Subgroup.card_le_of_le this
  have hBu : ∀ b ∈ S ⊓ L, (b : MulAut V) u = u := fun b hb => hSu b hb.1
  have hnat : ∀ {U : Subgroup V} {k : ℕ},
      DirectSumOfCopies L U ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k → u ∈ U → False := by
    intro U k hdir huU
    obtain ⟨H, hHL, hHu, hH⟩ := natSum_stab hL hBL hdir u huU hBu
    have := hnone H hHL hHu
    omega
  obtain ⟨hp1, hp2, -⟩ := h51 V hV (ffJ X) L hB51hyp
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  ·
    exfalso
    obtain ⟨hirr, hpair, -⟩ := hi
    have hN : Nat.card ↥L = 20160 ∨ Nat.card ↥L = 9999360 := Or.inl hL
    have huU : u ∈ commV L := hu
    rcases hpair with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
    · exact not_binaryNaturalSL_two1527d hN h
    · exact not_binaryNaturalSL_three1527d hN h
    · exact not_binaryNaturalSp4_1527d hN h
    · exact not_g2Natural1527d hN h
    · exact not_g2NaturalDerived_one1527d hN h
    · refine not_alternatingNatural1527d (n := 5) (by norm_num) ?_ h
      rw [hL]
      norm_num [Nat.factorial]
    · refine not_alternatingNatural1527d (n := 6) (by norm_num) ?_ h
      rw [hL]
      norm_num [Nat.factorial]
    · refine not_alternatingNatural1527d (n := 7) (by norm_num) ?_ h
      rw [hL]
      norm_num [Nat.factorial]
    · exact not_a7Four1527d hN h
    · exact not_tripleA6Six1527d hN h
    ·
      have hZ := hI16 V hV L hirr (Or.inr (Or.inl h))
      obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      rw [hZ] at hπ
      exact hnat (directSumOfCopies_one1527d hπ) huU
    ·
      have hZ := hI16 V hV L hirr (Or.inr (Or.inr h))
      obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      rw [hZ] at hπ
      have := card_eq_of_nat_realizes1527d hπ
      rw [hL, card_statedSL_five_zmod1527d] at this
      omega
    ·
      obtain ⟨H, hHL, hHu, hH⟩ := d8_stab hL le_rfl (hA8 V hV L hirr h) h u huU
      have := hnone H hHL hHu
      omega
    ·
      obtain ⟨π, hπ⟩ := h
      have hs : IsSimpleGroup (FFModel.extSq (ZMod 2) 5).Gam :=
        CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) (by norm_num)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
      · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
        have : Nat.card ↥(StatedSL 5 (ZMod 2)) = Nat.card ↥L :=
          Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
        rw [card_statedSL_five_zmod1527d] at this
        omega
      · have hsub : Subsingleton ↥L := ⟨fun a b => by
          obtain ⟨x, rfl⟩ := hπ.1 a
          obtain ⟨y, rfl⟩ := hπ.1 b
          have hx : x ∈ π.ker := by rw [htop]; trivial
          have hy : y ∈ π.ker := by rw [htop]; trivial
          rw [MonoidHom.mem_ker.1 hx, MonoidHom.mem_ker.1 hy]⟩
        have := Nat.card_of_subsingleton (1 : ↥L)
        omega
  ·
    exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -⟩ := hii
    exact ne_card_sl3_1527d hF (N := Nat.card ↥L) (Or.inl hL)
      (card_eq_of_nat_realizes1527d (hreal 0)).symm
  ·
    obtain ⟨hG, hsum⟩ := hiii
    rcases hsum.1 with rfl | rfl
    · exact ⟨hG, hsum⟩
    · exfalso
      obtain ⟨-, π, U₁, U₂, -, h₁, -⟩ := hsum
      have := card_eq_of_nat_realizes1527d h₁
      rw [hL, card_statedSL_five_zmod1527d] at this
      omega
  ·
    exfalso
    obtain ⟨-, n, hn, k, hk1, hkn, hdir⟩ := hiv
    rcases hn with rfl | rfl
    · exact hnat hdir hu
    · obtain ⟨I, π, -, -, -, hreal⟩ := hdir
      have := card_eq_of_nat_realizes1527d (hreal ⟨0, by omega⟩)
      rw [hL, card_statedSL_five_zmod1527d] at this
      omega

end S153L

end CFSG.Quasithin
