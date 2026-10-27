module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitSLNatural
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitAltNatural
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitA7Four
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.H13.VolIAltCoverEight
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Orbit

namespace Lem16

theorem exists_eq_zpowers_of_card_two {X : Type*} [Group X] {Z : Subgroup X}
    (hZ : Nat.card Z = 2) : ∃ z : X, z ≠ 1 ∧ Z = Subgroup.zpowers z := by
  have hne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  refine ⟨z, hz1', ?_⟩
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have hle : Subgroup.zpowers z ≤ Z := (Subgroup.zpowers_le).mpr hz
  have hdvd : orderOf z ∣ 2 := hZ ▸ Subgroup.orderOf_dvd_natCard Z hz
  have hord : orderOf z = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1'
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hord, hZ]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] def OrbitCase (L V : Subgroup G) [IsMulCommutative ↥V] : Prop :=
  OrbitsSeparated (autOn L V) ∨
    ∃ z : ↥V, z ≠ 1 ∧ fixV (autOn L V) = Subgroup.zpowers z ∧
      ((altCoreModel 6).Realizes (autOn L V) ⊤ ⊥ ∨ (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥ ∨
        G2WeylDerived (autOn L V))

omit [Finite G] in
theorem indecomposable_autOn [IsMulCommutative ↥V] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hind : IsIndecomposableUnder L V) :
    ∀ A B : Subgroup ↥V, (∀ h ∈ autOn L V, ∀ a ∈ A, (h : MulAut ↥V) a ∈ A) →
      (∀ h ∈ autOn L V, ∀ b ∈ B, (h : MulAut ↥V) b ∈ B) → A ⊓ B = ⊥ → A ⊔ B = ⊤ →
        A = ⊥ ∨ B = ⊥ := by
  intro A B hA hB hAB hAB'
  have hinf : A.map V.subtype ⊓ B.map V.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ V.subtype V.subtype_injective, hAB, Subgroup.map_bot]
  have hsup : A.map V.subtype ⊔ B.map V.subtype = V := by
    rw [← Subgroup.map_sup, hAB', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rcases hind.2 _ _ (Subgroup.map_subtype_le A) (Subgroup.map_subtype_le B)
      (le_normalizer_map_of_invariant hLV hA) (le_normalizer_map_of_invariant hLV hB) hinf hsup with
    h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp h)
  · exact Or.inr ((Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp h)

omit [Finite G] in
theorem irreducible_autOn [IsMulCommutative ↥V] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hirr : IsIrreducibleUnder L V) :
    ∀ W : Subgroup ↥V, (∀ h ∈ autOn L V, ∀ w ∈ W, (h : MulAut ↥V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  rcases hirr.2 _ (Subgroup.map_subtype_le W) (le_normalizer_map_of_invariant hLV hW) with h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp h)
  · right
    rw [eq_top_iff]
    intro w _
    have hw : (w : G) ∈ W.map V.subtype := by rw [h]; exact w.2
    obtain ⟨w', hw', hw'w⟩ := hw
    rwa [show w' = w from Subtype.ext hw'w] at hw'

omit [Finite G] in
theorem orbitCase_of_card_two [IsMulCommutative ↥V] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hZ : Nat.card ((Subgroup.centralizer (L : Set G)).subgroupOf V) = 2)
    (hcases : (altCoreModel 6).Realizes (autOn L V) ⊤ ⊥ ∨
      (altCoreModel 8).Realizes (autOn L V) ⊤ ⊥ ∨ G2WeylDerived (autOn L V)) :
    OrbitCase L V := by
  obtain ⟨z, hz1, hzZ⟩ := exists_eq_zpowers_of_card_two hZ
  exact Or.inr ⟨z, hz1, (fixV_autOn_eq hLV).trans hzZ, hcases⟩

theorem orbitCase_of_modules (hL52 : OrbitL52Ten) (hL32 : OrbitL32Four) (hHat : OrbitHatA6Six)
    (hG2c : G2NaturalCover) (hH : Hyp1223 G T L V) [IsMulCommutative ↥V]
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) (hmod : Modules12_2_2 L V) :
    OrbitCase L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  have hc := commutator_eq_of_hyp1223 hH
  have hsq := sq_eq_one_of_hyp1223 hH hred
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hne := not_le_centralizer_of_hyp1223 hH
  have hcomm := commV_autOn_eq_top hLV hc
  have hfix := fixV_autOn_eq hLV
  rcases hmod with ⟨n, hn, -, hnat⟩ | ⟨he, hcard, hind⟩ | ⟨he, hcard, hirr⟩ |
      ⟨n, hn5, hn8, -, halt⟩ | ⟨hcard, φ, hφ, hker⟩ | ⟨-, hG2⟩ | ⟨hq, hZ3, he6, hCO, hcard, -⟩
  ·
    exact Or.inl (orbitSLNatural ↥V (autOn L V) n hn hnat).2
  ·
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by norm_num)
    obtain ⟨eH⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
    exact Or.inl (hL32 ↥V hsq hcard (autOn L V) ⟨eH⟩ hcomm
      (fun W hW hinv => irreducible_autOn_of_hyp1223 hH W hW hinv)
      (indecomposable_autOn hLV hind)).2
  ·
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by norm_num)
    obtain ⟨eH⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 hne e
    exact Or.inl (hL52 ↥V hsq hcard (autOn L V) ⟨eH⟩ (irreducible_autOn hLV hirr)).2
  ·
    set Z := (Subgroup.centralizer (L : Set G)).subgroupOf V with hZdef
    have hZfix : Z ≤ fixV (autOn L V) := hfix.symm.le
    by_cases hZ : Z = ⊥
    · rw [hZ] at halt
      left
      interval_cases n
      · exact (orbitAltNaturalFive ↥V (autOn L V) halt).2
      · exact (orbitAltNaturalSix ↥V (autOn L V) halt).2
      · exact (orbitAltNaturalSeven ↥V (autOn L V) halt).2
      · exact (orbitAltNaturalEight ↥V (autOn L V) halt).2
    · interval_cases n
      · exact absurd (VolI.altNaturalCoverFive_holds ↥V hsq (autOn L V) Z hZfix hcomm halt) hZ
      · rcases VolI.altNaturalCoverSix_holds ↥V hsq (autOn L V) Z hZfix hcomm halt with
          h | ⟨hZ2, -, hE⟩
        · exact absurd h hZ
        · exact orbitCase_of_card_two hLV hZ2 (Or.inl hE)
      · exact absurd (VolI.altNaturalCoverSeven_holds ↥V hsq (autOn L V) Z hZfix hcomm halt) hZ
      · rcases VolI.altNaturalCoverEight_holds ↥V hsq (autOn L V) Z hZfix hcomm halt with
          h | ⟨hZ2, -, hE⟩
        · exact absurd h hZ
        · exact orbitCase_of_card_two hLV hZ2 (Or.inr (Or.inl hE))
  ·
    have hsurj := autOnSurj_surjective hLV
    let e₁ : ↥L ⧸ (autOnSurj hLV).ker ≃* ↥(autOn L V) :=
      QuotientGroup.quotientKerEquivOfSurjective _ hsurj
    let e₂ : ↥L ⧸ φ.ker ≃* ↥(alternatingGroup (Fin 7)) :=
      QuotientGroup.quotientKerEquivOfSurjective _ hφ
    have hkk : (autOnSurj hLV).ker = φ.ker := by rw [ker_autOnSurj, hker]
    let e : ↥(autOn L V) ≃* ↥(alternatingGroup (Fin 7)) :=
      (e₁.symm.trans (QuotientGroup.quotientMulEquivOfEq hkk)).trans e₂
    exact Or.inl (orbitA7Four ↥V hsq hcard (autOn L V) ⟨e⟩).2
  ·
    set Z := (Subgroup.centralizer (L : Set G)).subgroupOf V with hZdef
    have hZfix : Z ≤ fixV (autOn L V) := hfix.symm.le
    by_cases hZ : Z = ⊥
    · rw [hZ] at hG2
      exact Or.inl (orbitG2Natural ↥V (autOn L V) hG2).2
    · rcases hG2c ↥V hsq (autOn L V) Z hZfix hcomm hG2 with h | ⟨hZ2, -, hW⟩
      · exact absurd h hZ
      · exact orbitCase_of_card_two hLV hZ2 (Or.inr (Or.inr hW))
  ·
    obtain ⟨e6⟩ := he6
    have hinj : Function.Injective (autOnQuot hLV hO2) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H l =>
        rw [autOnQuot_mk] at hx
        have h1 : (l : G) ∈ Subgroup.centralizer (V : Set G) :=
          (mem_ker_autOnSurj hLV l).mp (MonoidHom.mem_ker.mpr hx)
        have h2 : (l : G) ∈ pCoreOf 2 L := by
          rw [← hCO]
          exact ⟨l.2, h1⟩
        rw [QuotientGroup.eq_one_iff]
        obtain ⟨l', hl', hl'l⟩ := h2
        rwa [show l' = l from Subtype.ext hl'l] at hl'
    let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L V) :=
      MulEquiv.ofBijective _ ⟨hinj, autOnQuot_surjective hLV hO2⟩
    have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := hq.1
    have hperf : Group.IsPerfect ↥(autOn L V) :=
      Group.IsPerfect.ofSurjective (autOnQuot_surjective hLV hO2)
    have hZ3' : Nat.card (Subgroup.center ↥(autOn L V)) = 3 := by
      rw [← Nat.card_congr (Subgroup.centerCongr eQ).toEquiv]
      exact hZ3
    let e6' : ↥(autOn L V) ⧸ Subgroup.center ↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6)) :=
      (QuotientGroup.congr (Subgroup.center ↥(autOn L V)) (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
        eQ.symm (Subgroup.map_center_eq eQ.symm)).trans e6
    exact Or.inl (hHat ↥V hsq hcard (autOn L V) hperf hZ3' ⟨e6'⟩).2

end Lem16

end CFSG.Quasithin.H13
