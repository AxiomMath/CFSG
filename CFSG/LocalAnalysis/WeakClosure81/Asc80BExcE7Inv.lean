module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcKilled
import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagKill
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
import CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialTwo
import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE
import CFSG.RankThree.PartOne.CTP.StrongPG2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.LieType.SeitzGeneration.ExcHighThree
open scoped commutatorElement
open CFSG.LieType.SeitzGeneration.ExcWideThree

private lemma rootChar_eq_one_of_two_dvd
    {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} {k : Fin τ.rank → ℕ} (hak : ∀ i, a i = (-1 : Lˣ) ^ k i)
    {α : Fin τ.rank → ℤ} (hd : (2 : ℤ) ∣ ∑ i, α i * (k i : ℤ)) : rootChar a α = 1 := by
  obtain ⟨m, hm⟩ := hd
  have h1 : rootChar a α = (-1 : Lˣ) ^ (∑ i, α i * (k i : ℤ)) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum_of_group]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hak i, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h1, hm, zpow_mul]
  have h2 : (-1 : Lˣ) ^ (2 : ℤ) = 1 := by norm_num
  rw [h2, one_zpow]


theorem exists_rElement_commute_toral_pair_e7 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {x₁ x₂ : ModGL .E7 K} (h₁ : x₁ ^ 2 = 1) (h₂ : x₂ ^ 2 = 1)
    {g : ModGL .E7 (AlgebraicClosure K)} (hg : g ∈ adjointGroup .E7 (AlgebraicClosure K))
    (hg₁ : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x₁ * g ∈
      torusGroup .E7 (AlgebraicClosure K))
    (hg₂ : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x₂ * g ∈
      torusGroup .E7 (AlgebraicClosure K)) :
    ∃ u : ↥(adjointGroup .E7 K), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      Commute (u : ModGL .E7 K) x₁ ∧ Commute (u : ModGL .E7 K) x₂ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hfpos : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι : K →+* L := algebraMap K L with hι
  have hℓ2 : ℓ ≠ 2 := by rw [hℓdef]; exact hK
  have hpq : Nat.Coprime 2 (ℓ ^ (f : ℕ)) := by
    have hcop : Nat.Coprime 2 ℓ :=
      (Nat.coprime_primes Nat.prime_two hℓ).2 (by omega)
    exact hcop.pow_right f
  have hcomm : x₁ * x₂ = x₂ * x₁ := by
    have ht₁ : g⁻¹ * baseChangeGL ι x₁ * g ∈ torusGroup .E7 L := hg₁
    have ht₂ : g⁻¹ * baseChangeGL ι x₂ * g ∈ torusGroup .E7 L := hg₂
    obtain ⟨a₁, ha₁⟩ := exists_rootDiagUnit_of_mem_torusGroup ht₁
    obtain ⟨a₂, ha₂⟩ := exists_rootDiagUnit_of_mem_torusGroup ht₂
    have hprod : (g⁻¹ * baseChangeGL ι x₁ * g) * (g⁻¹ * baseChangeGL ι x₂ * g) =
        (g⁻¹ * baseChangeGL ι x₂ * g) * (g⁻¹ * baseChangeGL ι x₁ * g) := by
      rw [← ha₁, ← ha₂]
      exact rootDiagUnit_mul_comm_of_mem_torusGroup a₁ (ha₂ ▸ ht₂)
    have hconj : g⁻¹ * baseChangeGL ι (x₁ * x₂) * g =
        g⁻¹ * baseChangeGL ι (x₂ * x₁) * g := by
      rw [map_mul, map_mul]
      calc g⁻¹ * (baseChangeGL ι x₁ * baseChangeGL ι x₂) * g
          = (g⁻¹ * baseChangeGL ι x₁ * g) * (g⁻¹ * baseChangeGL ι x₂ * g) := by group
        _ = (g⁻¹ * baseChangeGL ι x₂ * g) * (g⁻¹ * baseChangeGL ι x₁ * g) := hprod
        _ = g⁻¹ * (baseChangeGL ι x₂ * baseChangeGL ι x₁) * g := by group
    refine baseChangeGL_injective ι ?_
    calc baseChangeGL ι (x₁ * x₂)
        = g * (g⁻¹ * baseChangeGL ι (x₁ * x₂) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * baseChangeGL ι (x₂ * x₁) * g) * g⁻¹ := by rw [hconj]
      _ = baseChangeGL ι (x₂ * x₁) := by group
  set A : Subgroup (ModGL .E7 K) := Subgroup.closure {x₁, x₂} with hA
  have hpair : ({x₁, x₂} : Set (ModGL .E7 K)).Pairwise Commute := by
    intro a ha b hb hne
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _
  have : IsMulCommutative A := isMulCommutative_closure hpair
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hAexp : ∀ x ∈ A, x ^ 2 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y ^ 2 = 1) ?_ ?_ ?_ ?_ hx
    · rintro y (rfl | rfl)
      · exact h₁
      · exact h₂
    · simp
    · intro a b ha hb ha2 hb2
      have hc : a * b = b * a := hAcomm a ha b hb
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
        _ = a * (a * b) * b := by rw [← hc]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [← pow_two, ← pow_two, ha2, hb2]; group
    · intro a ha ha2
      rw [inv_pow, ha2, inv_one]
  set AL : Subgroup (ModGL .E7 L) := A.map (baseChangeGL ι) with hAL
  have hALexp : ∀ y ∈ AL, y ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hAexp x hx, map_one]
  have hFix : ∀ y : ModGL .E7 K,
      entrywiseFrobGL .E7 L ℓ (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hFixAL : ∀ y ∈ AL, entrywiseFrobGL .E7 L ℓ (f : ℕ) y = y := by
    rintro _ ⟨x, hx, rfl⟩
    exact hFix x
  have hgAL : ∀ y ∈ AL, g⁻¹ * y * g ∈ torusGroup .E7 L := by
    have hle : A ≤ (torusGroup .E7 L).comap
        ((MulAut.conj g⁻¹).toMonoidHom.comp (baseChangeGL ι)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro y (rfl | rfl)
      · simpa [MulAut.conj_apply] using hg₁
      · simpa [MulAut.conj_apply] using hg₂
    rintro _ ⟨x, hx, rfl⟩
    exact hle hx
  obtain ⟨w, g0, hg0C, hg0F, hTor⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus
      (τ := .E7) (L := L) (ℓ := ℓ) (f : ℕ) hfpos hpq hALexp hFixAL hg hgAL
  let D : CFSG.LieType.SeitzGeneration.ExcWideThree.LangGLData .E7 K A :=
    { w := w
      Fr := iterateFrobenius L ℓ (f : ℕ)
      hFr := by
        intro c
        rw [iterateFrobenius_def, hq]
      g0 := g0
      hg0C := hg0C
      hg0 := hg0F
      c := 1
      hcN := one_mem _
      hc := by
        intro x hx
        have hxAL : baseChangeGL ι x ∈ AL := Subgroup.mem_map_of_mem (baseChangeGL ι) hx
        simpa using hTor (baseChangeGL ι x) hxAL }
  have hpow : ∀ b : Lˣ, b ^ 2 = 1 → ∃ k : ℕ, b = (-1 : Lˣ) ^ k := by
    intro b hb
    have hb' : (b : L) ^ 2 = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) hb
      simpa using this
    rcases (sq_eq_one_iff (R := L)).1 hb' with h | h
    · exact ⟨0, Units.ext (by simpa using h)⟩
    · exact ⟨1, Units.ext (by simpa using h)⟩
  have hdiag : ∀ x ∈ A, ∃ a : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 a = D.g0⁻¹ * baseChangeGL ι (D.c * x * D.c⁻¹) * D.g0 ∧
        ∀ i, a i ^ 2 = 1 := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := D.hc x hx
    have htor : t ∈ torusGroup .E7 L := (Subgroup.mem_inf.1 ht).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup htor
    have hte' : D.g0 * t * D.g0⁻¹ = baseChangeGL ι (D.c * x * D.c⁻¹) := by
      simpa [MulAut.conj_apply] using hte
    have hDt : rootDiagUnit .E7 a = D.g0⁻¹ * baseChangeGL ι (D.c * x * D.c⁻¹) * D.g0 := by
      rw [ha, ← hte']
      group
    refine ⟨a, hDt, fun i => ?_⟩
    have hB2 : (baseChangeGL ι (D.c * x * D.c⁻¹)) ^ 2 = 1 := by
      have hx2 : x ^ 2 = 1 := hAexp x hx
      have hcc : (D.c * x * D.c⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hx2]
        group
      rw [← map_pow, hcc, map_one]
    have htB : t = D.g0⁻¹ * baseChangeGL ι (D.c * x * D.c⁻¹) * D.g0 := by
      rw [← hte']
      group
    have ht2 : t ^ 2 = 1 := by
      rw [htB]
      calc (D.g0⁻¹ * baseChangeGL ι (D.c * x * D.c⁻¹) * D.g0) *
            (D.g0⁻¹ * baseChangeGL ι (D.c * x * D.c⁻¹) * D.g0)
          = D.g0⁻¹ * (baseChangeGL ι (D.c * x * D.c⁻¹) *
              baseChangeGL ι (D.c * x * D.c⁻¹)) * D.g0 := by group
        _ = 1 := by rw [← pow_two, hB2]; group
    have h2 : rootDiagUnit .E7 (a ^ 2) = rootDiagUnit .E7 1 := by
      rw [← rootDiagUnit_pow, ha, ht2, rootDiagUnit_one]
    have h4 : a ^ 2 = 1 := rootDiagUnit_injective h2
    simpa using congrFun h4 i
  obtain ⟨a₁, ha₁, hc₁⟩ := hdiag x₁ (Subgroup.subset_closure (by simp))
  obtain ⟨a₂, ha₂, hc₂⟩ := hdiag x₂ (Subgroup.subset_closure (by simp))
  choose k₁ hk₁ using fun i => hpow (a₁ i) (hc₁ i)
  choose k₂ hk₂ using fun i => hpow (a₂ i) (hc₂ i)
  obtain ⟨α, hα, hd₁, hd₂⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_root_kills_two (τ := .E7)
      (Or.inr (Or.inr (Or.inl rfl))) k₁ k₂
  have hKills : D.Kills α := by
    set Sg : Subgroup (ModGL .E7 K) :=
      ((rootCharHom (L := L) α).ker.map (rootDiagUnitHom .E7 L)).comap (diagMapGL D) with hSg
    have hr₁ : rootChar a₁ α = 1 := rootChar_eq_one_of_two_dvd hk₁ hd₁
    have hr₂ : rootChar a₂ α = 1 := rootChar_eq_one_of_two_dvd hk₂ hd₂
    have hmemS : ∀ (x : ModGL .E7 K) (a : Fin Tag.E7.rank → Lˣ),
        rootDiagUnit .E7 a = diagMapGL D x → rootChar a α = 1 → x ∈ Sg := by
      intro x a hax hα1
      refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, ?_, ?_⟩)
      · exact hα1
      · exact hax
    have hx₁S : x₁ ∈ Sg :=
      hmemS x₁ a₁ ha₁ hr₁
    have hx₂S : x₂ ∈ Sg :=
      hmemS x₂ a₂ ha₂ hr₂
    have hAS : A ≤ Sg := by
      rw [hA]
      refine (Subgroup.closure_le Sg).2 ?_
      rintro y (rfl | rfl)
      · exact hx₁S
      · exact hx₂S
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hx))
    exact ⟨a, hax, ha⟩
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.kill_core_gl (τ := .E7)
      (Or.inr (Or.inr (Or.inl rfl))) K A D α hα hKills
  have hodd : Odd (Nat.card K) → Odd (orderOf uL) := by
    intro hKodd
    rw [orderOf_eq_prime huLp huL1]
    rw [hq] at hKodd
    exact Odd.of_dvd_nat hKodd (dvd_pow_self ℓ (by omega : (f : ℕ) ≠ 0))
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E7
      D.Fr D.hFr huLad huLF hodd)
  obtain ⟨u, hu_mem, hu1, ⟨n, hun⟩, hcommA⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.finish_gl K A D.c D.hcN u' hu'mem uL hu'eq
      huL1 huLp huLc
  refine ⟨⟨u, hu_mem⟩, ?_, ⟨n, ?_⟩, ?_, ?_⟩
  · intro h
    exact hu1 (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hun)
  · exact hcommA x₁ (Subgroup.subset_closure (by simp))
  · exact hcommA x₂ (Subgroup.subset_closure (by simp))

theorem exists_rElement_commute_inndiag_inv_e7 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (g : ↥(adjointGroup .E7 K)) (a : Fin Tag.E7.rank → Kˣ)
    (ht : ((g : ModGL .E7 K) * rootDiagUnit .E7 a) ^ 2 = 1) :
    ∃ u : ↥(adjointGroup .E7 K), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      Commute (u : ModGL .E7 K) ((g : ModGL .E7 K) * rootDiagUnit .E7 a) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι : K →+* L := algebraMap K L with hι
  have hℓ2 : ℓ ≠ 2 := by rw [hℓdef]; exact hK
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L ℓ]; exact hℓ2
  set t : ModGL .E7 K := (g : ModGL .E7 K) * rootDiagUnit .E7 a with htdef
  set x : ModGL .E7 L := baseChangeGL ι t with hxdef
  have hx2 : x ^ 2 = 1 := by rw [hxdef, ← map_pow, ht, map_one]
  have hdaL : rootDiagUnit .E7 (fun i => Units.map ι.toMonoidHom (a i)) ∈ adjointGroup .E7 L :=
    (exceptional_Lang_adjoint_diagonal_lift .E7 L (fun i => Units.map ι.toMonoidHom (a i))).1
  have hxmem : x ∈ adjointGroup .E7 L := by
    rw [hxdef, htdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup ι g.2) hdaL
  set B : Subgroup (ModGL .E7 L) := Subgroup.zpowers x with hB
  have hBle : B ≤ adjointGroup .E7 L := (Subgroup.zpowers_le.2 hxmem)
  have : Finite ↥B := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hB, Nat.card_zpowers]
    exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_iff_pow_eq_one.2 hx2) (by norm_num)).ne'
  have hBfin : (B : Set (ModGL .E7 L)).Finite := Set.toFinite _
  have hBexp : ∀ y ∈ B, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    calc (x ^ n) ^ 2 = x ^ n * x ^ n := pow_two _
      _ = x ^ (n + n) := (zpow_add x n n).symm
      _ = x ^ (n * 2) := by rw [show n + n = n * 2 by ring]
      _ = x ^ (2 * n) := by rw [mul_comm n 2]
      _ = (x ^ (2 : ℤ)) ^ n := zpow_mul x 2 n
      _ = 1 := by rw [zpow_ofNat, hx2, one_zpow]
  obtain ⟨c, hcC, hcn⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_le_monomial_bar (τ := .E7)
      (L := L) (ℓ := ℓ) (p := 2) hℓ2
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K ℓ)
      hBle hBfin hBexp
  have hn : c * x * c⁻¹ ∈ monomialSubgroup .E7 L :=
    hcn x (Subgroup.mem_zpowers x)
  have hnp : (c * x * c⁻¹) ^ 2 = 1 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.conj_pow_eq_one' c hx2
  obtain ⟨g', hg'C, hg'T⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_mem_torusGroup_of_mem_monomial
      (τ := .E7)
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_two (τ := .E7)) hL2 hn hnp
  have hconj : (g' * c) * x * (g' * c)⁻¹ = g' * (c * x * c⁻¹) * g'⁻¹ := by group
  have hg : (g' * c)⁻¹ ∈ adjointGroup .E7 L := inv_mem (mul_mem hg'C hcC)
  have hgT : ((g' * c)⁻¹)⁻¹ * x * (g' * c)⁻¹ ∈ torusGroup .E7 L := by
    rw [inv_inv, hconj]
    exact hg'T
  obtain ⟨u, hu1, ⟨n, hun⟩, hucomm⟩ :=
    exists_rElement_commute_toral_pair_e7 hK ht ht hg hgT hgT
  exact ⟨u, hu1, ⟨n, hun⟩, hucomm.1⟩

theorem exists_fixed_rElement_involution_e7 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {β : MulAut ↥(adjointGroup .E7 K)} (hβ : β ^ 2 = 1) :
    ∃ y : ↥(adjointGroup .E7 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧ β y = y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hodd : Odd (Nat.card K) := by
    rw [hq]
    exact (hℓ.eq_two_or_odd'.resolve_left (by rw [hℓdef]; exact hK)).pow
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hgaσ hβ
  by_cases hσ1 : σ = 1
  ·
    subst hσ1
    set t : ModGL .E7 K := (g : ModGL .E7 K) * rootDiagUnit .E7 a with htdef
    have h1m : ∀ x : ModGL .E7 K,
        Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x := by
      intro x
      have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      rw [e1]
      exact Units.ext (entrywise_id (τ := .E7) (R := K)
        (x : Module.End K (RootModule .E7 K)))
    have hβeq : ∀ h : ↥(adjointGroup .E7 K),
        (β h : ModGL .E7 K) = t * (h : ModGL .E7 K) * t⁻¹ := by
      intro h
      have h := hgaσ h
      rw [show exactQ .E7 K ε = 1 from rfl, h1m, htdef] at h
      rw [htdef]
      simpa [mul_assoc] using h
    have ht2comm : ∀ h : ↥(adjointGroup .E7 K),
        (t ^ 2) * (h : ModGL .E7 K) = (h : ModGL .E7 K) * (t ^ 2) := by
      intro h
      have h1 : (β (β h) : ModGL .E7 K) = (h : ModGL .E7 K) := by
        have := congrArg (fun φ : MulAut ↥(adjointGroup .E7 K) =>
          (φ h : ModGL .E7 K)) (show β * β = 1 by rw [← sq]; exact hβ)
        simpa using this
      rw [hβeq (β h), hβeq h] at h1
      have h3 : t ^ 2 * (h : ModGL .E7 K) * (t ^ 2)⁻¹ = (h : ModGL .E7 K) := by
        calc t ^ 2 * (h : ModGL .E7 K) * (t ^ 2)⁻¹ =
            t * (t * (h : ModGL .E7 K) * t⁻¹) * t⁻¹ := by
              rw [pow_two, mul_inv_rev]; group
          _ = (h : ModGL .E7 K) := h1
      calc t ^ 2 * (h : ModGL .E7 K) =
            (t ^ 2 * (h : ModGL .E7 K) * (t ^ 2)⁻¹) * t ^ 2 := by
              rw [pow_two, mul_inv_rev]; group
        _ = (h : ModGL .E7 K) * t ^ 2 := by rw [h3]
    set L := AlgebraicClosure K with hLdef
    have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
    set ι : K →+* L := algebraMap K L with hι
    have hdaL :
        rootDiagUnit .E7 (fun i => Units.map ι.toMonoidHom (a i)) ∈ adjointGroup .E7 L :=
      (exceptional_Lang_adjoint_diagonal_lift .E7 L
        (fun i => Units.map ι.toMonoidHom (a i))).1
    have hzAdj : baseChangeGL ι (t ^ 2) ∈ adjointGroup .E7 L := by
      rw [map_pow]
      refine pow_mem ?_ 2
      rw [htdef, map_mul, baseChangeGL_rootDiagUnit]
      exact mul_mem (baseChangeGL_mem_adjointGroup ι g.2) hdaL
    obtain ⟨-, -, hfaith, -⟩ :=
      exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L ι
    have hz1 : baseChangeGL ι (t ^ 2) = 1 := by
      refine hfaith _ hzAdj ?_
      intro h hh
      obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.1 hh
      rw [← map_mul, ← map_mul, ht2comm ⟨h', hh'⟩]
    have ht2eq : t ^ 2 = 1 :=
      baseChangeGL_injective ι (by rw [hz1, map_one])
    obtain ⟨u, hu1, ⟨n, hun⟩, hucomm⟩ :=
      exists_rElement_commute_inndiag_inv_e7 hK g a (by rw [← htdef]; exact ht2eq)
    refine ⟨u, hu1, ⟨n, hun⟩, ?_⟩
    apply Subtype.ext
    rw [hβeq u]
    have hu' : t * (u : ModGL .E7 K) = (u : ModGL .E7 K) * t := hucomm.eq.symm
    calc t * (u : ModGL .E7 K) * t⁻¹ = ((u : ModGL .E7 K) * t) * t⁻¹ := by rw [hu']
      _ = (u : ModGL .E7 K) := by group
  ·
    obtain ⟨hev, hσc, -⟩ :=
      hquad (ringChar K) (f : ℕ) hℓ f.pos hq σ hσ2 hσ1
    have hKe : Nat.card K = (ringChar K ^ ((f : ℕ) / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hq]
    have he : 1 ≤ (f : ℕ) / 2 :=
      Nat.div_pos (Nat.le_of_dvd f.pos (even_iff_two_dvd.1 hev)) (by norm_num)
    obtain ⟨hfield, -, -, -⟩ :=
      exceptional_Lang_quadratic_field_coset_conjugacy hℓ he K hKe σ.toRingHom hσc
    have hβform : ∀ u : ↥(adjointGroup .E7 K), (β u : ModGL .E7 K) =
        (g : ModGL .E7 K) * rootDiagUnit .E7 a *
          Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E7 K) *
            (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹ := by
      intro u
      have h := hgaσ u
      rw [show exactQ .E7 K ε = 1 from rfl] at h
      simpa [mul_assoc] using h
    obtain ⟨_, -, hβα⟩ := hfield .E7
    obtain ⟨-, hconj⟩ := hβα g a
    obtain ⟨ψ, hψ, -⟩ := hconj β hβform hβ
    let i : Fin Tag.E7.rank := ⟨0, by decide⟩
    let y₀ : ↥(adjointGroup .E7 K) := ⟨xUnit .E7 K i 1, xUnit_mem_adjointGroup i 1⟩
    have hy₀ne : y₀ ≠ 1 := by
      intro hc
      have hc' : (xUnit .E7 K i 1 : ModGL .E7 K) = 1 := congrArg Subtype.val hc
      have h2 : xOp .E7 K i (1 : K) = xOp .E7 K i (0 : K) := by
        have h3 := congrArg (fun z : ModGL .E7 K =>
          (z : Module.End K (RootModule .E7 K))) hc'
        simpa only [coe_xUnit, xOp_zero, Units.val_one] using h3
      exact one_ne_zero (xOp_injective i h2)
    have hy₀pow : y₀ ^ (ringChar K ^ 1) = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      simpa using CFSG.RankThree.PartOne.StrongP.xUnit_pow_char
        (K := K) (p := ringChar K) .E7 i
    have hy₀field : Units.map (entrywiseHom σ.toRingHom) (y₀ : ModGL .E7 K) =
        (y₀ : ModGL .E7 K) := by
      refine Units.ext ?_
      change entrywise (τ := .E7) σ.toRingHom (xOp .E7 K i 1) = xOp .E7 K i 1
      rw [entrywise_xOp, map_one]
    have key : ∀ (ψ : MulAut ↥(adjointGroup .E7 K)),
        (ψ * β * ψ⁻¹) y₀ = y₀ →
        ∃ y : ↥(adjointGroup .E7 K), y ≠ 1 ∧
          (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧ β y = y := by
      intro ψ hψy
      refine ⟨ψ⁻¹ y₀, ?_, ⟨1, ?_⟩, ?_⟩
      · intro h1
        apply hy₀ne
        have h : ψ (ψ⁻¹ y₀) = 1 := by rw [h1, map_one]
        rwa [show ψ (ψ⁻¹ y₀) = y₀ from MulEquiv.apply_symm_apply ψ y₀] at h
      · apply ψ.injective
        rw [map_pow, show ψ (ψ⁻¹ y₀) = y₀ from MulEquiv.apply_symm_apply ψ y₀,
          hy₀pow, map_one]
      · apply ψ.injective
        rw [show ψ (ψ⁻¹ y₀) = y₀ from MulEquiv.apply_symm_apply ψ y₀]
        simpa only [MulAut.mul_apply] using hψy
    refine key ψ ?_
    exact Subtype.ext ((hψ y₀).trans hy₀field)

theorem exists_fixed_rElement_field_comm_e7 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) (hσ : σ ^ 2 = 1) {β : MulAut ↥(adjointGroup .E7 K)}
    (hβ : β ^ 2 = 1) (hβσ : β * entrywiseAdjointAut .E7 σ = entrywiseAdjointAut .E7 σ * β) :
    ∃ y : ↥(adjointGroup .E7 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      entrywiseAdjointAut .E7 σ y = y ∧ β y = y := by
  classical
  have hσ2 : σ * σ = 1 := by rw [← sq]; exact hσ
  set Γ : Subgroup (ModGL .E7 K) := entrywiseFixedGroup .E7 σ with hΓdef
  set J : Subgroup (ModGL .E7 K) := fixedFieldImage .E7 σ with hJdef
  obtain ⟨-, -, -, hJΓ, -, -, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure .E7 K hK σ
  rw [← hΓdef, ← hJdef] at hJΓ hder
  have hJC : J ≤ adjointGroup .E7 K := hJΓ.trans inf_le_left
  have hΓC : Γ ≤ adjointGroup .E7 K := inf_le_left
  set ΓC : Subgroup ↥(adjointGroup .E7 K) :=
    Γ.subgroupOf (adjointGroup .E7 K) with hΓCdef
  set JC : Subgroup ↥(adjointGroup .E7 K) :=
    J.subgroupOf (adjointGroup .E7 K) with hJCdef
  have hderC : ⁅ΓC, ΓC⁆ = JC := by
    have hmap : (⁅ΓC, ΓC⁆ : Subgroup ↥(adjointGroup .E7 K)).map
        (adjointGroup .E7 K).subtype =
        JC.map (adjointGroup .E7 K).subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hΓC,
        Subgroup.map_subgroupOf_eq_of_le hJC, hder]
    exact Subgroup.map_injective (f := (adjointGroup .E7 K).subtype)
      (adjointGroup .E7 K).subtype_injective hmap
  have hβΓ_le : ΓC.map β.toMonoidHom ≤ ΓC := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_subgroupOf.2 ?_
    have hgΓ : (g : ModGL .E7 K) ∈ Γ := Subgroup.mem_subgroupOf.1 hg
    refine mem_entrywiseFixedGroup.2 ⟨(β g).2, ?_⟩
    have hgfix : Units.map (entrywiseHom σ.toRingHom) (g : ModGL .E7 K) =
        (g : ModGL .E7 K) := (mem_entrywiseFixedGroup.1 hgΓ).2
    have hσg : entrywiseAdjointAut .E7 σ g = g := by
      apply Subtype.ext
      rw [coe_entrywiseAdjointAut]
      exact hgfix
    have hcommg : β (entrywiseAdjointAut .E7 σ g) = entrywiseAdjointAut .E7 σ (β g) := by
      have := congrArg (fun φ : MulAut ↥(adjointGroup .E7 K) => φ g) hβσ
      simpa only [MulAut.mul_apply] using this
    rw [hσg] at hcommg
    rw [← coe_entrywiseAdjointAut]
    exact congrArg Subtype.val hcommg.symm
  have hβ2g : ∀ g : ↥(adjointGroup .E7 K), β (β g) = g := by
    intro g
    have := congrArg (fun φ : MulAut ↥(adjointGroup .E7 K) => φ g) hβ
    simpa [pow_two] using this
  have hβΓ : ΓC.map β.toMonoidHom = ΓC := by
    refine le_antisymm hβΓ_le ?_
    intro g hg
    refine Subgroup.mem_map.2 ⟨β g, hβΓ_le (Subgroup.mem_map_of_mem β.toMonoidHom hg), ?_⟩
    show β (β g) = g
    exact hβ2g g
  have hβJ : JC.map β.toMonoidHom = JC := by
    rw [← hderC, Subgroup.map_commutator, hβΓ]
  have hβJ_le : JC.map β.toMonoidHom ≤ JC := hβJ.le
  let βJ : MulAut ↥JC :=
    { toFun := fun j => ⟨β j, hβJ_le (Subgroup.mem_map_of_mem β.toMonoidHom j.2)⟩
      invFun := fun j => ⟨β j, hβJ_le (Subgroup.mem_map_of_mem β.toMonoidHom j.2)⟩
      left_inv := fun j => Subtype.ext (hβ2g (j : ↥(adjointGroup .E7 K)))
      right_inv := fun j => Subtype.ext (hβ2g (j : ↥(adjointGroup .E7 K)))
      map_mul' := fun a b => Subtype.ext (map_mul β (a : ↥(adjointGroup .E7 K))
        (b : ↥(adjointGroup .E7 K))) }
  have hβJ2 : βJ * βJ = 1 := by
    refine MulEquiv.ext fun j => ?_
    apply Subtype.ext
    change β (β (j : ↥(adjointGroup .E7 K))) = (j : ↥(adjointGroup .E7 K))
    exact hβ2g (j : ↥(adjointGroup .E7 K))
  have hβJpoint : ∀ j : ↥JC, βJ (βJ j) = j := by
    intro j
    have := congrArg (fun f : MulAut ↥JC => f j) hβJ2
    simpa using this
  let φ : ↥JC ≃* adjointGroup .E7 ↥(fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv (τ := .E7) σ).symm
  let β₀ : MulAut (adjointGroup .E7 ↥(fixSubfield σ)) := (φ.symm.trans βJ).trans φ
  have hβ02 : β₀ ^ 2 = 1 := by
    rw [pow_two]
    refine MulEquiv.ext fun y => ?_
    show β₀ (β₀ y) = y
    show φ (βJ (φ.symm (φ (βJ (φ.symm y))))) = y
    rw [show φ.symm (φ (βJ (φ.symm y))) = βJ (φ.symm y) from
      MulEquiv.symm_apply_apply φ (βJ (φ.symm y))]
    rw [hβJpoint]
    exact MulEquiv.apply_symm_apply φ y
  have hchar : ringChar ↥(fixSubfield σ) = ringChar K := by
    have : CharP K (ringChar K) := ringChar.charP K
    have : CharP ↥(fixSubfield σ) (ringChar K) :=
      (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective
        (ringChar K)).mpr inferInstance
    exact ringChar.eq _ _
  have : Finite ↥(fixSubfield σ) := Subtype.finite
  obtain ⟨y₀, hy₀1, ⟨n, hy₀n⟩, hy₀fix⟩ :=
    exists_fixed_rElement_involution_e7 (K := ↥(fixSubfield σ))
      (by rw [hchar]; exact hK) hβ02
  set y : ↥(adjointGroup .E7 K) :=
    ((φ.symm y₀ : ↥JC) : ↥(adjointGroup .E7 K)) with hydef
  have hβJy : βJ (φ.symm y₀) = φ.symm y₀ := by
    have h2 : φ (βJ (φ.symm y₀)) = y₀ := hy₀fix
    have h3 : φ.symm (φ (βJ (φ.symm y₀))) = φ.symm y₀ := congrArg φ.symm h2
    rwa [show φ.symm (φ (βJ (φ.symm y₀))) = βJ (φ.symm y₀) from
      MulEquiv.symm_apply_apply φ (βJ (φ.symm y₀))] at h3
  have hy1 : y ≠ 1 := by
    intro h
    apply hy₀1
    have h1 : (φ.symm y₀ : ↥JC) = 1 := by
      apply Subtype.ext
      simpa [hydef] using h
    calc y₀ = φ (φ.symm y₀) := (MulEquiv.apply_symm_apply φ y₀).symm
      _ = φ 1 := by rw [h1]
      _ = 1 := map_one φ
  have hβy : β y = y := by
    apply Subtype.ext
    have hh : ((βJ (φ.symm y₀) : ↥JC) : ModGL .E7 K) =
        (β ((φ.symm y₀ : ↥JC) : ↥(adjointGroup .E7 K)) : ModGL .E7 K) := rfl
    calc (β y : ModGL .E7 K) = β ((φ.symm y₀ : ↥JC) : ↥(adjointGroup .E7 K)) := by
          rw [hydef]
      _ = ((βJ (φ.symm y₀) : ↥JC) : ↥(adjointGroup .E7 K)) := hh.symm
      _ = ((φ.symm y₀ : ↥JC) : ↥(adjointGroup .E7 K)) := by rw [hβJy]
      _ = (y : ModGL .E7 K) := by rw [hydef]
  have hσy : entrywiseAdjointAut .E7 σ y = y := by
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    have hyΓ : (y : ModGL .E7 K) ∈ Γ := by
      rw [hydef]
      exact hJΓ (Subgroup.mem_subgroupOf.1 (φ.symm y₀).2)
    exact (mem_entrywiseFixedGroup.1 hyΓ).2
  have hy_pow : y ^ (ringChar K ^ n) = 1 := by
    have hφpow : (φ.symm y₀) ^ (ringChar ↥(fixSubfield σ) ^ n) = 1 := by
      rw [← map_pow, hy₀n, map_one]
    have hcast := congrArg (fun z : ↥JC => ((z : ↥(adjointGroup .E7 K)) : ModGL .E7 K)) hφpow
    rw [hchar] at hcast
    apply Subtype.ext
    simpa [hydef] using hcast
  exact ⟨y, hy1, ⟨n, hy_pow⟩, hσy, hβy⟩

theorem exists_fixed_rElement_four_e7_of_not_inndiag {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(adjointGroup .E7 K)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hout : ¬ E ≤ CFSG.StandardType.LayerSixE.inndiagAut .E7 K) :
    ∃ y : ↥(adjointGroup .E7 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  obtain ⟨x, hxE, hxout⟩ : ∃ x ∈ E,
      x ∉ CFSG.StandardType.LayerSixE.inndiagAut .E7 K := by
    by_contra hcon
    apply hout
    intro e he
    by_contra hne
    exact hcon ⟨e, he, hne⟩
  have hx1 : x ≠ 1 := fun h => hxout (h ▸ Subgroup.one_mem _)
  have hx2 : x ^ 2 = 1 := hE.2 x hxE
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF x
  have hσ2 : σ ^ 2 = 1 := hsq x g a σ ε hgaσ hx2
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    apply hxout
    have h1m : ∀ y : ModGL .E7 K,
        Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) y = y := by
      intro y
      have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      rw [e1]
      exact Units.ext (entrywise_id (τ := .E7) (R := K)
        (y : Module.End K (RootModule .E7 K)))
    have hxeq : x = MulAut.conj g * rootDiagAutHom .E7 K a := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      change (x h : ModGL .E7 K) =
        (g : ModGL .E7 K) * (rootDiagUnit .E7 a * (h : ModGL .E7 K) *
          (rootDiagUnit .E7 a)⁻¹) * (g : ModGL .E7 K)⁻¹
      have h := hgaσ h
      rw [hσ1, show exactQ .E7 K ε = 1 from rfl, h1m] at h
      simpa [mul_assoc] using h
    rw [hxeq, CFSG.StandardType.LayerSixE.inndiagAut]
    exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have : Finite (ModGL .E7 K) := finite_modGL
  have : Finite ↥(adjointGroup .E7 K) := Subtype.finite
  have : Finite (MulAut ↥(adjointGroup .E7 K)) :=
    Finite.of_injective (fun e : MulAut ↥(adjointGroup .E7 K) => (e : _ → _))
      DFunLike.coe_injective
  have : Finite ↥E := Subtype.finite
  have : Fintype ↥E := Fintype.ofFinite _
  let xE : ↥E := ⟨x, hxE⟩
  have hcard2 : ({1, xE} : Finset ↥E).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]
    intro h
    exact hx1 (congrArg Subtype.val h).symm
  have hlt : ({1, xE} : Finset ↥E).card < (Finset.univ : Finset ↥E).card := by
    rw [hcard2, Finset.card_univ, ← Nat.card_eq_fintype_card, h4]
    norm_num
  obtain ⟨βE, -, hβnmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hβE : (βE : MulAut ↥(adjointGroup .E7 K)) ∈ E := βE.2
  have hβne1 : (βE : MulAut ↥(adjointGroup .E7 K)) ≠ 1 := by
    intro h
    apply hβnmem
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl (Subtype.ext h)
  have hβnex : (βE : MulAut ↥(adjointGroup .E7 K)) ≠ x := by
    intro h
    apply hβnmem
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Subtype.ext h)
  set β : MulAut ↥(adjointGroup .E7 K) := (βE : MulAut ↥(adjointGroup .E7 K)) with hβdef
  have hβE' : β ∈ E := hβE
  have hβ2 : β ^ 2 = 1 := hE.2 β hβE'
  have hxβ : x * β = β * x :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hxE⟩ : ↥E) (⟨β, hβE'⟩ : ↥E))
  obtain ⟨hev, hσc, -⟩ :=
    hquad (ringChar K) (f : ℕ) hℓ f.pos hq σ hσ2 hσ1
  have hKe : Nat.card K = (ringChar K ^ ((f : ℕ) / 2)) ^ 2 := by
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hq]
  have he : 1 ≤ (f : ℕ) / 2 :=
    Nat.div_pos (Nat.le_of_dvd f.pos (even_iff_two_dvd.1 hev)) (by norm_num)
  obtain ⟨hfield, -, -, -⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy hℓ he K hKe σ.toRingHom hσc
  have hxform : ∀ u : ↥(adjointGroup .E7 K), (x u : ModGL .E7 K) =
      (g : ModGL .E7 K) * rootDiagUnit .E7 a *
        Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E7 K) *
          (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹ := by
    intro u
    have h := hgaσ u
    rw [show exactQ .E7 K ε = 1 from rfl] at h
    simpa [mul_assoc] using h
  obtain ⟨_, -, hβα⟩ := hfield .E7
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, hψ, -⟩ := hconj x hxform hx2
  have hψx : ψ * x * ψ⁻¹ = entrywiseAdjointAut .E7 σ := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    show ((ψ * x * ψ⁻¹) u : ModGL .E7 K) = (entrywiseAdjointAut .E7 σ u : ModGL .E7 K)
    rw [hψ u, coe_entrywiseAdjointAut]
  set β' : MulAut ↥(adjointGroup .E7 K) := ψ * β * ψ⁻¹ with hβ'def
  have hβ'2 : β' ^ 2 = 1 := by
    rw [hβ'def, pow_two]
    calc (ψ * β * ψ⁻¹) * (ψ * β * ψ⁻¹) = ψ * (β * β) * ψ⁻¹ := by group
      _ = 1 := by rw [show β * β = 1 by rw [← pow_two]; exact hβ2]; group
  have hβ'σ : β' * entrywiseAdjointAut .E7 σ = entrywiseAdjointAut .E7 σ * β' := by
    rw [← hψx]
    calc (ψ * β * ψ⁻¹) * (ψ * x * ψ⁻¹) = ψ * (β * x) * ψ⁻¹ := by group
      _ = ψ * (x * β) * ψ⁻¹ := by rw [← hxβ]
      _ = (ψ * x * ψ⁻¹) * (ψ * β * ψ⁻¹) := by group
  obtain ⟨y', hy'1, ⟨n, hy'n⟩, hσy', hβ'y'⟩ :=
    exists_fixed_rElement_field_comm_e7 hK σ hσ2 hβ'2 hβ'σ
  have hxy : x (ψ⁻¹ y') = ψ⁻¹ y' := by
    have hxeq : x = ψ⁻¹ * entrywiseAdjointAut .E7 σ * ψ := by
      rw [← hψx]
      group
    rw [hxeq, MulAut.mul_apply, MulAut.mul_apply,
      show ψ (ψ⁻¹ y') = y' from MulEquiv.apply_symm_apply ψ y', hσy']
  have hβy : β (ψ⁻¹ y') = ψ⁻¹ y' := by
    have hβeq : β = ψ⁻¹ * β' * ψ := by
      rw [hβ'def]
      group
    rw [hβeq, MulAut.mul_apply, MulAut.mul_apply,
      show ψ (ψ⁻¹ y') = y' from MulEquiv.apply_symm_apply ψ y', hβ'y']
  have hy1 : ψ⁻¹ y' ≠ 1 := by
    intro h
    apply hy'1
    have h2 : ψ (ψ⁻¹ y') = ψ 1 := by rw [h]
    rwa [show ψ (ψ⁻¹ y') = y' from MulEquiv.apply_symm_apply ψ y', map_one ψ] at h2
  have hy_pow : (ψ⁻¹ y') ^ (ringChar K ^ n) = 1 := by
    rw [← map_pow, hy'n, map_one]
  have hx2sq : x * x = 1 := by rw [← sq]; exact hx2
  have hβ2sq : β * β = 1 := by rw [← sq]; exact hβ2
  obtain ⟨hmem, -, -, hcard⟩ :=
    CFSG.GH74.GLS.Stage1.Main.four_of_invols hx2sq hβ2sq hxβ hx1 hβne1 hβnex.symm
  have hEeq : Subgroup.zpowers x ⊔ Subgroup.zpowers β = E :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hβE')) (by rw [hcard, h4])
  refine ⟨ψ⁻¹ y', hy1, ⟨n, hy_pow⟩, fun e he => ?_⟩
  rw [← hEeq] at he
  rcases hmem e he with rfl | rfl | rfl | rfl
  · rfl
  · exact hxy
  · exact hβy
  · rw [MulAut.mul_apply, hβy, hxy]

end CFSG.LocalAnalysis.WeakClosure81
