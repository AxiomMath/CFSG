module

public import CFSG.RankThree.PartOne.SLB4B.ModelSp
public import CFSG.RankThree.PartOne.SLB4B.Cover
public import CFSG.RankThree.PartOne.SRC.CentralizerGen
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix Subgroup CFSG CFSG.RankThree.PartOne.SRC CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

theorem coprime_card_center_of_pow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ z ∈ Subgroup.center G, z ^ p = 1 → z = 1) : Nat.Coprime p (Nat.card (center G)) := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center G) p hdvd
  have h1 : (x : G) ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have h2 : (x : G) = 1 := h _ x.2 h1
  have h3 : x = 1 := Subtype.ext h2
  rw [h3, orderOf_one] at hx
  exact hp.one_lt.ne hx

section Cover

variable {K : Type} [Field K] [Finite K]

@[expose] def symMap : (K × K × K) →+ Matrix (Fin 2) (Fin 2) K where
  toFun w := !![w.1, w.2.2; w.2.2, w.2.1]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem symMap_symm (w : K × K × K) : (symMap w)ᵀ = symMap w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMap]

theorem symMap_injective : Function.Injective (symMap (K := K)) := by
  intro a b h
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  have e01 := congrFun (congrFun h 0) 1
  simp [symMap] at e00 e11 e01
  exact Prod.ext e00 (Prod.ext e11 e01)

@[expose] noncomputable def siegelSp : Multiplicative (K × K × K) →* StatedSp 2 K where
  toFun w := ⟨siegelGL (symMap w.toAdd), siegelGL_mem_statedSp (symMap_symm _)⟩
  map_one' := Subtype.ext (by
    change siegelGL (symMap (Multiplicative.toAdd 1)) = 1
    rw [toAdd_one, map_zero, siegelGL_zero])
  map_mul' a b := Subtype.ext (by
    change siegelGL (symMap (Multiplicative.toAdd (a * b))) =
      siegelGL (symMap (Multiplicative.toAdd a)) * siegelGL (symMap (Multiplicative.toAdd b))
    rw [toAdd_mul, map_add, siegelGL_add])

theorem siegelSp_injective : Function.Injective (siegelSp (K := K)) := by
  intro a b h
  have h' := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  exact Multiplicative.toAdd.injective (symMap_injective (siegelMat_injective h'))

theorem two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h0
  have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem sp4_quasisimple (h4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple (StatedSp 2 K) :=
  CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr h4))

theorem sp4_coprime_center {p : ℕ} [Fact p.Prime] [CharP K p] :
    Nat.Coprime p (Nat.card (center (StatedSp 2 K))) :=
  coprime_card_center_of_pow Fact.out
    (CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_statedSp 2 K)

theorem planeInvolution_noncentral {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    (planeInvolution 2 K : StatedSp 2 K) ∉ center (StatedSp 2 K) := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq]
  exact planeInvolution_not_mem (two_ne_zero_of_charP hp2) le_rfl

theorem planeInvolution_coprime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.Coprime (orderOf (planeInvolution 2 K : StatedSp 2 K)) p := by
  have hdvd : orderOf (planeInvolution 2 K : StatedSp 2 K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one planeInvolution_sq
  exact Nat.Coprime.coprime_dvd_left hdvd
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))

theorem sp4_closed (h5 : 5 ≤ Nat.card K) {p : ℕ} :
    ∀ (W : Type) [Group W] [Finite W] (π : W →* StatedSp 2 K), Function.Surjective π →
      π.ker ≤ Subgroup.center W → IsPGroup p π.ker →
        ∃ s : StatedSp 2 K →* W, ∀ g, π (s g) = g :=
  fun _ _ _ _ hπ hcen _ =>
    CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central (by norm_num) h5 hπ
      hcen

theorem isElementaryAbelian_siegelSp {p : ℕ} [Fact p.Prime] [CharP K p] :
    IsElementaryAbelian p (siegelSp (K := K)).range := by
  have hW : ∀ w : K × K × K, p • w = 0 := fun w => by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [← Nat.cast_smul_eq_nsmul K]
  have hpow : ∀ a : Multiplicative (K × K × K), a ^ p = 1 := fun a =>
    Multiplicative.toAdd.injective (by rw [toAdd_pow, toAdd_one]; exact hW _)
  exact CFSG.RankThree.PartOne.SRC.isElementaryAbelian_range siegelSp hpow

theorem card_siegelSp_range {p e : ℕ} (hK : Nat.card K = p ^ e) :
    Nat.card (siegelSp (K := K)).range = p ^ (3 * e) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective siegelSp_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, hK]
  ring

theorem pow_four_dvd_card_sp4 {p e : ℕ} (hK : Nat.card K = p ^ e) (he : 1 ≤ e) :
    p ^ 4 ∣ Nat.card (StatedSp 2 K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, ← pow_mul]
  exact Dvd.dvd.mul_right (pow_dvd_pow p (by nlinarith)) _

theorem cover_sp4 {p e : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ e) (hp2 : p ≠ 2)
    (he : 2 ≤ e) (W : Type) [Group W] [Finite W] (ρ : W →* StatedSp 2 K)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have hp : p.Prime := Fact.out
  have h9 : 9 ≤ Nat.card K := by
    rw [hK]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 2
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  exact rank_four_of_cover_quasisimple hp2 (sp4_quasisimple (by omega)) sp4_coprime_center _
    (planeInvolution_noncentral hp2) (planeInvolution_coprime hp2) (sp4_closed (by omega))
    isElementaryAbelian_siegelSp (k := 3 * e) (by omega) (card_siegelSp_range hK) ρ hρ hker

theorem rankFourCover_psp6 {p e : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = p ^ e)
    (hp2 : p ≠ 2) (he : 2 ≤ e) : RankFourCover p (StatedProj (StatedSp 3 K)) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  exact rankFourCover_of_cover_ker hp hp2
    (fun W _ _ ρ hρ hker => cover_sp4 hK hp2 he W ρ hρ hker) (sp4Emb6 (K := K))
    (fun A hA => by rw [sp4Emb6_injective (hA.trans (map_one _).symm), one_pow])
    (orderOf_sp6Invol h2) sp4Emb6_comm

end Cover

end CFSG.RankThree.PartOne.SLB4B
