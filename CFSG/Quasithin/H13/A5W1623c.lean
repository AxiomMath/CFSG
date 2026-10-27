module

public import CFSG.Quasithin.H13.A5W1622s
public import CFSG.Quasithin.H13.A5W1622u
public import CFSG.Quasithin.H13.A5W1623a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.A5Model
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def End1367L4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) → S.Lv ≤ K →
      Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) →
      ∀ t ∈ S.Tv, ∀ Y : Subgroup G, Y ≤ K → S.Tv ⊓ K ≤ Y →
        K ⊓ Subgroup.centralizer (S.WK K : Set G) ≤ Y → t ∈ Subgroup.normalizer (Y : Set G)

theorem card_sl45_two {m : ℕ} (hm : m = 4 ∨ m = 5) :
    Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) = 20160 ∨
      Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) = 9999360 := by
  rcases hm with rfl | rfl
  · left
    rw [card_SL_eq (by norm_num), Ln2P.card_zmod_two]
    decide
  · right
    rw [card_SL_eq (by norm_num), Ln2P.card_zmod_two]
    decide

theorem sl45_card_ne_sl2 {N : ℕ} (hN : N = 20160 ∨ N = 9999360) {p c : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (h : N * c = p * (p ^ 2 - 1)) : False := by
  have hpN : p ∣ N * c := ⟨p ^ 2 - 1, h⟩
  have hpc : ¬ p ∣ c := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hpN' : p ∣ N := ((Nat.Prime.dvd_mul hp).mp hpN).resolve_right hpc
  have hpq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
  have hpow : ∀ q k : ℕ, q.Prime → p ∣ q ^ k → p = q := fun q k hq hd =>
    hpq q hq (hp.dvd_of_dvd_pow hd)
  have key : p = 5 ∨ p = 7 ∨ p = 31 := by
    rcases hN with rfl | rfl
    · have e : (20160 : ℕ) = 2 ^ 6 * (3 ^ 2 * (5 * 7)) := by norm_num
      rw [e] at hpN'
      rcases (Nat.Prime.dvd_mul hp).mp hpN' with h2 | h2
      · have := hpow 2 6 Nat.prime_two h2
        omega
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := hpow 3 2 Nat.prime_three h3
        omega
      rcases (Nat.Prime.dvd_mul hp).mp h3 with h5 | h7
      · exact Or.inl (hpq 5 (by norm_num) h5)
      · exact Or.inr (Or.inl (hpq 7 (by norm_num) h7))
    · have e : (9999360 : ℕ) = 2 ^ 10 * (3 ^ 2 * (5 * (7 * 31))) := by norm_num
      rw [e] at hpN'
      rcases (Nat.Prime.dvd_mul hp).mp hpN' with h2 | h2
      · have := hpow 2 10 Nat.prime_two h2
        omega
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := hpow 3 2 Nat.prime_three h3
        omega
      rcases (Nat.Prime.dvd_mul hp).mp h3 with h5 | h3
      · exact Or.inl (hpq 5 (by norm_num) h5)
      rcases (Nat.Prime.dvd_mul hp).mp h3 with h7 | h31
      · exact Or.inr (Or.inl (hpq 7 (by norm_num) h7))
      · exact Or.inr (Or.inr (hpq 31 (by norm_num) h31))
  rcases key with rfl | rfl | rfl <;> rcases hN with rfl | rfl <;> omega

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_isQuasisimple_of_sl (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (e : ↥(S.plus K) ≃* SpecialLinearGroup (Fin m) (ZMod 2)) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus h1222 h517 hF hYz.1 hT hLv
  have hq := S.isQuasisimple_plus h1222 h517 hF hYz hT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image Gv K) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  let πX : ↥(modO2Image Gv K) →* ↥(S.plus K) := π.comp eX.symm.toMonoidHom
  have hπX : Function.Surjective πX := hπ.comp eX.symm.surjective
  have : IsSimpleGroup (SpecialLinearGroup (Fin m) (ZMod 2)) :=
    sl_isSimple_of_card_two Ln2P.card_zmod_two (by omega)
  have hsP : IsSimpleGroup ↥(S.plus K) := e.isSimpleGroup
  have hZP := center_eq_bot_of_isSimple_of_isQuasisimple hsP hq
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 20160 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 9999360 := by
    rw [Nat.card_congr (quotCenterEquivOfEqBot hZP).toEquiv, Nat.card_congr e.toEquiv]
    exact card_sl45_two hm
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot h1222 h517 hF) hK
  rcases hA with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
  · exact (isQuasisimple_congr eX).mpr hcomp.1
  · exact (isQuasisimple_congr eX).mpr hcomp.1
  · exfalso
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    exact sl45_card_ne_sl2 hN hp hp5 hc1 hc2 hcard
  · exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gv K)))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image Gv K) := by
      ext x
      simp [ψ₄]
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    exact sl45_card_ne_sl2 hN Nat.prime_five le_rfl hc1 hc2 hcard

end Setting

end CFSG.Quasithin.H13.A5
