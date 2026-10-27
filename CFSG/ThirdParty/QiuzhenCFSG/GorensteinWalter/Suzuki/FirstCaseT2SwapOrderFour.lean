module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.SylowThreeJoin
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.SwappedLinesInvertedLine
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCardThreeTransferNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The Sylow-two subgroup of `N_G(P)` contains an order-four element that
swaps the two conjugates of `U` in `P`; consequently this Sylow-two subgroup
is cyclic. -/
public theorem firstCase_exists_t2_order_four_swap
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (P : Sylow 3 G) (hPU : c.U ≤ (P : Subgroup G))
    (T2 : Sylow 2 (↥(Subgroup.normalizer (P : Set G)))) :
    let NP : Subgroup G := Subgroup.normalizer (P : Set G)
    let Tg : Subgroup G := (T2 : Subgroup (↥NP)).map NP.subtype
    ∃ a : G, a ∈ Tg ∧ a ∉ c.Hhat ∧ orderOf a = 4 ∧
      Subgroup.zpowers a = Tg ∧
      a ^ 2 ∈ Tg ⊓ c.Hhat ∧ a ^ 2 ≠ 1 ∧
      conjugateSubgroup c.U a ≤ (P : Subgroup G) ∧
      conjugateSubgroup c.U a ≠ c.U := by
  classical
  intro NP Tg
  have hP9 : Nat.card (P : Subgroup G) = 9 := firstCase_sylow3_card_nine c d P
  have hP9' : Nat.card (P : Subgroup G) = 3 ^ 2 := by simpa using hP9
  have : IsMulCommutative (P : Subgroup G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9'
  have hcommP : ∀ x y : G, x ∈ (P : Subgroup G) → y ∈ (P : Subgroup G) →
      x * y = y * x := by
    intro x y hx hy
    exact congrArg Subtype.val
      (((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9').is_comm).comm
        ⟨x, hx⟩ ⟨y, hy⟩)
  have hPH : (P : Subgroup G) ≤ c.Hhat :=
    (firstCase_sylow3_le_hhat_iff_contains_U hmin c hfirst d P hPU P).mpr hPU
  have hconjmul : ∀ (H : Subgroup G) (g h : G),
      conjugateSubgroup (conjugateSubgroup H h) g = conjugateSubgroup H (g * h) := by
    intro H g h
    ext x
    simp [conjugateSubgroup, Subgroup.map_map]
  obtain ⟨U1, U2, hU1neU2, hU1le, hU2le, hU1conj, hU2conj, honly⟩ :=
    firstCase_sylow3_UConjugates_inside_eq hmin c hfirst d P
  have hU1eq : U1 = c.U ∨ U2 = c.U := by
    have hUconj : ∃ g : G, c.U = conjugateSubgroup c.U g := by
      refine ⟨1, ?_⟩
      rw [conjugateSubgroup]
      have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [h1]
      exact (Subgroup.map_id c.U).symm
    exact (honly c.U hUconj hPU).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  let U : Subgroup G := if h : U1 = c.U then U1 else U2
  let W : Subgroup G := if h : U1 = c.U then U2 else U1
  have hUeq : U = c.U := by
    by_cases h : U1 = c.U
    · simpa [U, h]
    · rcases hU1eq with h1 | h2
      · exact False.elim (h h1)
      · simpa [U, h]
  have hUle : U ≤ (P : Subgroup G) := by
    rw [hUeq]
    exact hPU
  have hWle : W ≤ (P : Subgroup G) := by
    by_cases h : U1 = c.U <;> simp [W, h, hU1le, hU2le]
  have hUneW : U ≠ W := by
    by_cases h : U1 = c.U
    · simpa [U, W, h] using hU1neU2
    · simpa [U, W, h] using hU1neU2.symm
  have hUconj : ∃ g : G, U = conjugateSubgroup c.U g := by
    by_cases h : U1 = c.U
    · simpa [U, h] using hU1conj
    · simpa [U, h] using hU2conj
  have hWconj : ∃ g : G, W = conjugateSubgroup c.U g := by
    by_cases h : U1 = c.U
    · simpa [W, h] using hU2conj
    · simpa [W, h] using hU1conj
  have honlyUW : ∀ V : Subgroup G, (∃ g : G, V = conjugateSubgroup c.U g) →
      V ≤ (P : Subgroup G) → V = U ∨ V = W := by
    intro V hVc hVle
    rcases honly V hVc hVle with h1 | h2
    · by_cases h : U1 = c.U
      · exact Or.inl (by simpa [U, h] using h1)
      · exact Or.inr (by simpa [W, h] using h1)
    · by_cases h : U1 = c.U
      · exact Or.inr (by simpa [W, h] using h2)
      · exact Or.inl (by simpa [U, h] using h2)
  have hTg4 : Nat.card Tg = 4 := by
    have hfac : (36 : ℕ).factorization 2 = 2 := by
      rw [show (36 : ℕ) = 2 ^ 2 * 9 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self]
      exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (9 : ℕ))
    have hT := T2.card_eq_multiplicity
    have hNPcard : Nat.card (↥NP) = 36 :=
      firstCase_normalizer_sylow3_card hmin c hfirst d P
    rw [hNPcard, hfac] at hT
    norm_num at hT
    calc
      Nat.card Tg = Nat.card (T2 : Subgroup (↥NP)) := by
        exact (Nat.card_congr
          (Subgroup.equivMapOfInjective (T2 : Subgroup (↥NP)) NP.subtype
            NP.subtype_injective).toEquiv).symm
      _ = 4 := hT
  have hTg2 : Nat.card ↥(Tg ⊓ c.Hhat) = 2 := by
    simpa [NP, Tg] using firstCase_normalizer_sylow3_sylow2_inter_hhat_card_two
      hmin c hfirst d P hPU T2
  have hTgNP : Tg ≤ NP := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    exact z.2
  have hnotle : ¬ Tg ≤ c.Hhat := by
    intro hle
    have hinf : Tg ⊓ c.Hhat = Tg := inf_eq_left.mpr hle
    rw [hinf, hTg4] at hTg2
    omega
  obtain ⟨a, haTg, haH⟩ := Set.not_subset.mp hnotle
  have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
    have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    intro hbot
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    have hfour : Nat.card (twoCoreOf c.Hhat) = 4 :=
      (firstCase_klein_V_klein c hklein).card_four
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hO2 hUne
  have haUle : conjugateSubgroup U a ≤ (P : Subgroup G) := by
    have haNP : a ∈ NP := hTgNP haTg
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    change a * u * a⁻¹ ∈ (P : Subgroup G)
    exact (Subgroup.mem_normalizer_iff.mp haNP u).1 (hUle hu)
  have haUconj : ∃ g : G, conjugateSubgroup U a = conjugateSubgroup c.U g := by
    rcases hUconj with ⟨g, hUg⟩
    refine ⟨a * g, ?_⟩
    calc
      conjugateSubgroup U a = conjugateSubgroup (conjugateSubgroup c.U g) a := by rw [hUg]
      _ = conjugateSubgroup c.U (a * g) := hconjmul c.U a g
  have haUneU : conjugateSubgroup U a ≠ U := by
    intro hfix
    apply haH
    rw [← hNormU]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change c.U.map (MulAut.conj a) = c.U
    rw [← hUeq]
    simpa [conjugateSubgroup] using hfix
  have haU : conjugateSubgroup U a = W := by
    rcases honlyUW (conjugateSubgroup U a) haUconj haUle with h | h
    · exact False.elim (haUneU h)
    · exact h
  have ht : ∃ t : G, t ∈ Tg ⊓ c.Hhat ∧ t ≠ 1 := by
    let A := Tg ⊓ c.Hhat
    have hgt : 1 < Nat.card A := by rw [hTg2]; norm_num
    have hnt : Nontrivial A := (Finite.one_lt_card_iff_nontrivial).mp hgt
    rcases exists_ne (1 : A) with ⟨t, ht⟩
    exact ⟨(t : G), t.2, fun h => ht (Subtype.ext h)⟩
  rcases ht with ⟨t, ht, htne⟩
  have ht2 : t ^ 2 = 1 := by
    have hd := Subgroup.orderOf_dvd_natCard (Tg ⊓ c.Hhat) ht
    rw [hTg2, orderOf_dvd_iff_pow_eq_one] at hd
    exact hd
  have hTg4sq : Nat.card Tg = 2 ^ 2 := by rw [hTg4]; norm_num
  have : IsMulCommutative Tg :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hTg4sq
  have hatcomm : a * t = t * a := congrArg Subtype.val
    (((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hTg4sq).is_comm).comm
      ⟨a, haTg⟩ ⟨t, ht.1⟩)
  have htInvP : ∀ p : G, p ∈ (P : Subgroup G) → t * p * t⁻¹ = p⁻¹ :=
    firstCase_t2_inter_hhat_inverts_P hmin c hfirst d P hPU T2 t ht htne
  have haord2 : orderOf a ≠ 2 := by
    intro haord
    have ha2 : a ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      rw [haord]
    obtain ⟨X, hX3, hXleP, haInvX⟩ :=
      exists_order_three_line_inverted_of_swap U W (P : Subgroup G) a
        (by simpa [hUeq] using firstCase_U_card_three hmin c hfirst d)
        hUle hWle hUneW ha2 haU hcommP
    have hXne : X ≠ ⊥ := by
      intro hbot
      rw [hbot] at hX3
      simp at hX3
    have hXleH : X ≤ c.Hhat := hXleP.trans hPH
    let s : G := a * t
    have hsne : s ≠ 1 := by
      intro hs1
      change a * t = 1 at hs1
      have htinv : t⁻¹ = t :=
        inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using ht2)
      have hat : a = t := by
        calc
          a = (a * t) * t⁻¹ := by group
          _ = t⁻¹ := by rw [hs1]; simp
          _ = t := htinv
      exact haH (hat ▸ ht.2)
    have hs2 : s ^ 2 = 1 := by
      dsimp [s]
      rw [pow_two]
      calc
        (a * t) * (a * t) = a * (t * a) * t := by group
        _ = a * (a * t) * t := by rw [hatcomm.symm]
        _ = (a * a) * (t * t) := by group
        _ = 1 := by rw [← pow_two, ha2, ← pow_two, ht2]; simp
    have hsCent : s ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have haix := haInvX x hx
      have htix := htInvP x (hXleP hx)
      have hainv : a⁻¹ = a :=
        inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using ha2)
      have htinv : t⁻¹ = t :=
        inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using ht2)
      have hsconj : s * x * s⁻¹ = x := by
        dsimp [s]
        rw [mul_inv_rev]
        calc
          a * t * x * (t⁻¹ * a⁻¹) = a * (t * x * t⁻¹) * a⁻¹ := by group
          _ = a * x⁻¹ * a⁻¹ := by rw [htix]
          _ = (a * x * a⁻¹)⁻¹ := by group
          _ = x := by rw [haix]; simp
      have hsInv : s⁻¹ = s :=
        inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hs2)
      have hsx : s * x = x * s := by
        calc
          s * x = (s * x * s⁻¹) * s := by group
          _ = x * s := by rw [hsconj]
      exact hsx.symm
    have hsord : orderOf s = 2 := orderOf_eq_prime hs2 hsne
    have hCentEven : Even (Nat.card (Subgroup.centralizer (X : Set G))) := by
      rw [even_iff_two_dvd]
      have hle : Subgroup.zpowers s ≤ Subgroup.centralizer (X : Set G) :=
        Subgroup.zpowers_le.mpr hsCent
      have hd := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hsord] at hd
    let n := firstCaseCosetInvolutions c a
    have haI : IsInvolution a := by
      refine ⟨?_, ha2⟩
      intro h
      apply haH
      rw [h]
      exact c.Hhat.one_mem
    have haJ : a ∈ firstCaseJ c n := by
      change IsInvolution a ∧ a ∉ c.Hhat ∧ firstCaseCosetInvolutions c a = n
      exact ⟨haI, haH, rfl⟩
    have hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat a := by
      intro x hx
      exact ⟨hXleH hx, haInvX x hx⟩
    have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
    have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    obtain ⟨g, _hgH, hXgU, _hNX⟩ :=
      firstCase_klein_card_three_transfer_normalizer hmin c hfirst hklein
        haJ hXne hXleH hX3 hXinv hCentEven hU3
    have hXconj : ∃ g : G, X = conjugateSubgroup c.U g := by
      refine ⟨g⁻¹, ?_⟩
      calc
        X = conjugateSubgroup (conjugateSubgroup X g) g⁻¹ := by
          rw [hconjmul X g⁻¹ g]
          ext x
          simp [conjugateSubgroup]
        _ = conjugateSubgroup c.U g⁻¹ := by rw [hXgU]
    have haFixX : conjugateSubgroup X a = X := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
        change a * x * a⁻¹ ∈ X
        rw [haInvX x hx]
        exact X.inv_mem hx
      · have hcard : Nat.card (conjugateSubgroup X a) = Nat.card X := by
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective X (MulAut.conj a).toMonoidHom
              (MulAut.conj a).injective).toEquiv.symm
        rw [hcard]
    rcases honlyUW X hXconj hXleP with hXU | hXW
    · have : conjugateSubgroup U a = U := by simpa [hXU] using haFixX
      exact hUneW (this.symm.trans haU)
    · have haW : conjugateSubgroup W a = U := by
        calc
          conjugateSubgroup W a = conjugateSubgroup (conjugateSubgroup U a) a := by rw [haU]
          _ = conjugateSubgroup U (a * a) := hconjmul U a a
          _ = U := by
            rw [← pow_two, ha2]
            ext x
            simp [conjugateSubgroup]
      have : conjugateSubgroup W a = W := by simpa [hXW] using haFixX
      exact hUneW (haW.symm.trans this)
  have haord1 : orderOf a ≠ 1 := by
    intro h1
    apply haH
    simpa [orderOf_eq_one_iff.mp h1] using c.Hhat.one_mem
  have haDvd4 : orderOf a ∣ 4 := by
    have hd := Subgroup.orderOf_dvd_natCard Tg haTg
    rwa [hTg4] at hd
  have haord4 : orderOf a = 4 := by
    have hpos : 0 < orderOf a := orderOf_pos a
    have hle : orderOf a ≤ 4 := Nat.le_of_dvd (by norm_num) haDvd4
    have haord3 : orderOf a ≠ 3 := by
      intro h3
      rw [h3] at haDvd4
      norm_num at haDvd4
    omega
  have hgen : Subgroup.zpowers a = Tg := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr haTg
    · rw [Nat.card_zpowers, haord4, hTg4]
  have hinterIndex : ((Tg ⊓ c.Hhat).subgroupOf Tg).index = 2 := by
    have hm := ((Tg ⊓ c.Hhat).subgroupOf Tg).index_mul_card
    have hsubcard : Nat.card ↥((Tg ⊓ c.Hhat).subgroupOf Tg) = 2 := by
      exact (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : Tg ⊓ c.Hhat ≤ Tg)).toEquiv).trans hTg2
    rw [hsubcard, hTg4] at hm
    omega
  have ha2mem : a ^ 2 ∈ Tg ⊓ c.Hhat := by
    have hmem : (⟨a, haTg⟩ : Tg) ^ 2 ∈ (Tg ⊓ c.Hhat).subgroupOf Tg :=
      Subgroup.sq_mem_of_index_two hinterIndex ⟨a, haTg⟩
    exact Subgroup.mem_subgroupOf.mp hmem
  have ha2ne : a ^ 2 ≠ 1 := by
    intro ha2
    have hd : orderOf a ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact ha2
    rw [haord4] at hd
    norm_num at hd
  refine ⟨a, haTg, haH, haord4, hgen, ha2mem, ha2ne, ?_, ?_⟩
  · simpa [hUeq] using haUle
  · intro hfix
    apply hUneW
    calc
      U = c.U := hUeq
      _ = conjugateSubgroup c.U a := hfix.symm
      _ = conjugateSubgroup U a := by rw [hUeq]
      _ = W := haU

end CFSG.GorensteinWalter
