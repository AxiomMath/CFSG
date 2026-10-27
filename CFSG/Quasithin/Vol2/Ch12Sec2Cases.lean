module

public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec2Models
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.H13.FiveAltCover
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem alt12_2_2_of_alt12_2_2Lie {G : Type} [Group G] (h : Alt12_2_2Lie G) : Alt12_2_2 G := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem one_le_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    omega
  · exact h

section Cases

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem le_sup_of_hyp1223 (hH : Hyp1223 G T L V) : V ≤ L ⊔ T :=
  hH.irrPlus.1.trans (Subgroup.map_subtype_le _)

theorem le_normalizer_of_hyp1223 (hH : Hyp1223 G T L V) : L ≤ Subgroup.normalizer (V : Set G) :=
  hH.irrPlus.2.2.1

theorem commutator_eq_of_hyp1223 (hH : Hyp1223 G T L V) : ⁅V, L⁆ = V :=
  hH.irrPlus.2.2.2.1

theorem not_le_centralizer_of_hyp1223 (hH : Hyp1223 G T L V) :
    ¬ L ≤ Subgroup.centralizer (V : Set G) := by
  intro h
  apply hH.irrPlus.2.1
  rw [← commutator_eq_of_hyp1223 hH]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)

theorem pCoreOf_le_centralizer_of_hyp1223 (hH : Hyp1223 G T L V)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
  pCoreOf_le_centralizer_of_isPrimeReduced_sup hH.normalizes (le_sup_of_hyp1223 hH) hred

theorem sq_eq_one_of_hyp1223 (hH : Hyp1223 G T L V)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) : ∀ v : ↥V, v ^ 2 = 1 := by
  intro v
  have := hred.isElementaryAbelian
  have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
    (⟨v, le_sup_of_hyp1223 hH v.2⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr v.2)
  exact Subtype.ext (by simpa using congrArg Subtype.val h2)

theorem irreducible_of_hyp1223 (hH : Hyp1223 G T L V) :
    ∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) → J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V :=
  hH.irrPlus.2.2.2.2.2.1

omit [Finite G] in
theorem ker_comp_autOnSurj (hLV : L ≤ Subgroup.normalizer (V : Set G)) {X : Type*} [Group X]
    (e : ↥(autOn L V) ≃* X) :
    (e.toMonoidHom.comp (autOnSurj hLV)).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
  rw [CFSG.SectionRank.ker_mulEquiv_comp, ker_autOnSurj]

theorem irreducible_autOn_of_hyp1223 [IsMulCommutative ↥V] (hH : Hyp1223 G T L V)
    (W : Subgroup ↥V) (hW : fixV (autOn L V) ≤ W)
    (hinv : ∀ h ∈ autOn L V, ∀ w ∈ W, (h : MulAut ↥V) w ∈ W) :
    W = fixV (autOn L V) ∨ W = ⊤ := by
  have hLV := le_normalizer_of_hyp1223 hH
  rw [fixV_autOn_eq hLV] at hW ⊢
  have hJ1 : V ⊓ Subgroup.centralizer (L : Set G) ≤ W.map V.subtype := by
    rintro x ⟨hxV, hxC⟩
    exact ⟨⟨x, hxV⟩, hW (Subgroup.mem_subgroupOf.mpr hxC), rfl⟩
  rcases irreducible_of_hyp1223 hH _ hJ1 (Subgroup.map_subtype_le W)
      (le_normalizer_map_of_invariant hLV hinv) with h | h
  · left
    ext w
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hw
      have hw' : (w : G) ∈ W.map V.subtype := ⟨w, hw, rfl⟩
      rw [h] at hw'
      exact hw'.2
    · intro hw
      have hw' : (w : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨w.2, hw⟩
      rw [← h] at hw'
      obtain ⟨w', hw'W, hw'eq⟩ := hw'
      rwa [show w' = w from Subtype.ext hw'eq] at hw'W
  · right
    rw [eq_top_iff]
    intro w _
    have hw' : (w : G) ∈ W.map V.subtype := by rw [h]; exact w.2
    obtain ⟨w', hw'W, hw'eq⟩ := hw'
    rwa [show w' = w from Subtype.ext hw'eq] at hw'W

theorem isIrreducibleUnder_of_hyp1223 (hH : Hyp1223 G T L V)
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : IsIrreducibleUnder L V := by
  refine ⟨hH.irrPlus.2.1, fun W hWV hLW => ?_⟩
  have := irreducible_of_hyp1223 hH W (hC ▸ bot_le) hWV hLW
  rwa [hC] at this

theorem false_of_concl328_one
    (h6220 : Stmt6_2_20) (hNat : NaturalSL24NotA5Sum)
    (hH : Hyp1223 G T L V) [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hM : quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G)))
    (h : ∃ n : ℕ, LieModel ↥(autOn L V) .PSL 2 2 n ∧
      BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V)
        2 n) :
    False := by
  obtain ⟨n, hLie, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hc := commutator_eq_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  obtain ⟨-, hn1, -, hne, -⟩ := hadm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    subst hn
    exact hne (by norm_num)
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  have e' : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.trans (QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (n := 2) le_rfl e'
  have hLieQ : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eQ.trans e'.symm).symm hLie
  rcases h6220 G T (Subgroup.normalizer (L : Set G)) L V n hH.simple hH.nonabelian hH.qtke
      hH.sylow hM hH.normalizes hH.maximal hH.faithful Subgroup.le_normalizer le_rfl hn2 hLieQ
      (le_sup_of_hyp1223 hH) hred (by rw [hc]; exact hH.irrPlus.2.1) with
    ⟨rfl, hA5, -⟩ | hLie2 | hM22 | hM23
  · rw [hc] at hA5
    exact hNat G L V hLV hnat (irreducible_of_hyp1223 hH) hA5
  · exact hH.notAlt (alt12_2_2_of_alt12_2_2Lie hLie2)
  · exact hH.notAlt (Or.inr (Or.inr (Or.inl hM22)))
  · exact hH.notAlt (Or.inr (Or.inr (Or.inr (Or.inl hM23))))

theorem modules_of_concl328_two_a
    (h1101 : Stmt11_0_1) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
      BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 n) :
    Modules12_2_2 L V := by
  obtain ⟨n, K, _, _, hK, ⟨e⟩, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (n := 3) (by norm_num) e
  have hn1 := one_le_of_card_eq_two_pow hK
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact absurd ⟨n, h1, Or.inl ⟨K, inferInstance, inferInstance, hK, ⟨eQ⟩⟩⟩
      (h1101 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful)
  · have hn : n = 1 := by omega
    subst hn
    rw [pow_one] at hK
    exact Or.inl ⟨3, Or.inl rfl, ⟨eQ.trans (slCongr (ringEquivZModTwo hK))⟩, hnat⟩

theorem modules_of_concl328_two_b
    (hInd : L32FourIndecomposable) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      Nat.card V = 2 ^ 4 ∧
      BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V)
        3 1) :
    Modules12_2_2 L V := by
  obtain ⟨⟨e⟩, hcard, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (K := ZMod 2) (n := 3)
    (by norm_num) e
  exact Or.inr (Or.inl ⟨⟨eQ⟩, hcard, hInd G L V hLV (commutator_eq_of_hyp1223 hH)
    hH.irrPlus.2.1 hcard hnat (irreducible_of_hyp1223 hH)⟩)

theorem false_of_concl328_three
    (h1101 : Stmt11_0_1) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) ∧
      BinaryNaturalSp4 (V := ↥V) (autOn L V) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) n) :
    False := by
  obtain ⟨n, K, _, _, hK, ⟨e⟩, -⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hnc := not_le_centralizer_of_hyp1223 hH
  have hqV := isQuasisimple_autOn_of_pCoreOf_le hLV hH.quasisimple hO2 hnc
  have hn1 := one_le_of_card_eq_two_pow hK
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
    obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hH.quasisimple
    set φ := e.toMonoidHom.comp (autOnQuot hLV hO2) with hφ
    have hφs : Function.Surjective φ := e.surjective.comp (autOnQuot_surjective hLV hO2)
    obtain ⟨a, ha⟩ := exists_ne_one_autOn hLV hnc
    have hinj := injective_of_quasisimple_of_split hH.quasisimple hodd φ hφs
      ⟨e a, fun h => ha (e.injective (h.trans (map_one e).symm))⟩ fun hcen hoddk => by
        obtain ⟨σ, -, -, e₂, -⟩ :=
          CFSG.SectionRank.EvenCover.even_symplectic_central_odd_extension_splitting 2 hφs hcen
            hoddk
        exact ⟨σ.range, ⟨e₂⟩⟩
    exact h1101 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful
      ⟨n, h1, Or.inr (Or.inr (Or.inl (lieModel_psp_of_mulEquiv_statedSp h1 hK
        (MulEquiv.ofBijective φ ⟨hinj, hφs⟩))))⟩
  · have hn : n = 1 := by omega
    subst hn
    rw [pow_one] at hK
    have : Group.IsPerfect ↥(autOn L V) := hqV.1
    exact not_isPerfect_statedSp_of_card_two hK
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem modules_of_concl328_four (h1101 : Stmt11_0_1) (hG2 : G2ZornQuotientModel)
    (hH : Hyp1223 G T L V) [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
      G2NaturalDerived (V := ↥V) (autOn L V) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) n) :
    Modules12_2_2 L V := by
  obtain ⟨n, K, _, _, hK, ⟨e⟩, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hn1 := one_le_of_card_eq_two_pow hK
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hH.quasisimple
  obtain ⟨hU, hG⟩ := hG2 _ hH.quasisimple hodd K n hK hn1 (e.toMonoidHom.comp (autOnQuot hLV hO2))
    (e.surjective.comp (autOnQuot_surjective hLV hO2))
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact absurd ⟨n, h1, Or.inr (Or.inr (Or.inr (hG h1)))⟩
      (h1101 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful)
  · have hn : n = 1 := by omega
    subst hn
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hU rfl, hnat⟩)))))

theorem modules_of_alternatingNatural_odd (hH : Hyp1223 G T L V) [IsMulCommutative ↥V] {n : ℕ}
    (hn : n = 5 ∨ n = 7) (e : ↥(autOn L V) ≃* alternatingGroup (Fin n))
    (halt : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ n) : Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  have hodd : Odd n := by rcases hn with rfl | rfl <;> decide
  have hfix := fixV_eq_bot_of_alternatingNatural hodd (by omega) halt
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf V = ⊥ :=
    (fixV_autOn_eq hLV).symm.trans hfix
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, by omega, by omega,
    ⟨e.toMonoidHom.comp (autOnSurj hLV), e.surjective.comp (autOnSurj_surjective hLV),
      ker_comp_autOnSurj hLV e⟩, ?_⟩)))
  rw [hZ]
  exact halt

theorem modules_of_concl328_six (hH : Hyp1223 G T L V) [IsMulCommutative ↥V]
    (e : ↥(autOn L V) ≃* alternatingGroup (Fin 6))
    (halt : AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) 6) : Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨6, by norm_num, by norm_num,
    ⟨e.toMonoidHom.comp (autOnSurj hLV), e.surjective.comp (autOnSurj_surjective hLV),
      ker_comp_autOnSurj hLV e⟩, halt⟩)))

theorem modules_of_concl328_seven (hH : Hyp1223 G T L V) [IsMulCommutative ↥V]
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (e : ↥(autOn (L ⊔ T) V) ≃* alternatingGroup (Fin 7)) (hcard : Nat.card V = 2 ^ 4) :
    Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have heq := autOn_eq_autOn_sup_of_isSimpleGroup hLV hTV hH.normalizes e.isSimpleGroup
    (autOn_ne_bot_of_not_le_centralizer hLV (not_le_centralizer_of_hyp1223 hH))
  set e' : ↥(autOn L V) ≃* alternatingGroup (Fin 7) := (MulEquiv.subgroupCongr heq).trans e
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcard, e'.toMonoidHom.comp (autOnSurj hLV),
    e'.surjective.comp (autOnSurj_surjective hLV), ker_comp_autOnSurj hLV e'⟩))))

theorem modules_of_concl328_eight (hHat : HatA6SixIrreducible) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hperf : Group.IsPerfect ↥(autOn L V)) (hZ3 : Nat.card (Subgroup.center ↥(autOn L V)) = 3)
    (e : ↥(autOn L V) ⧸ Subgroup.center ↥(autOn L V) ≃* alternatingGroup (Fin 6))
    (hcard : Nat.card V = 2 ^ 6) : Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hq := hH.quasisimple
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
  set ψ := autOnQuot hLV hO2 with hψ
  have hψs : Function.Surjective ψ := autOnQuot_surjective hLV hO2
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [card_alternatingGroup_fin 6 (by norm_num)]
    decide
  have hcardH : Nat.card ↥(autOn L V) = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(autOn L V)),
      Nat.card_congr e.toEquiv, hA6, hZ3]
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  obtain ⟨-, eQ, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
    (alternatingGroup_nonabelian (by norm_num))
    (e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥(autOn L V))).comp ψ))
    (e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hψs))
  obtain ⟨-, hB, -⟩ :=
    five_alternating_small_central_cover_reduction hq hodd (n := 6) (by norm_num) eQ
  obtain ⟨hZ13, -, -⟩ := hB (Or.inl rfl)
  have hcardQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      360 * Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)), Nat.card_congr eQ.toEquiv, hA6]
  have hle : Nat.card ↥(autOn L V) ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Nat.card_le_card_of_surjective ψ hψs
  have hZQ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := by
    rcases hZ13 with h | h
    · rw [hcardQ, h, hcardH] at hle
      omega
    · exact h
  have hψb : Function.Bijective ψ :=
    Function.Surjective.bijective_of_nat_card_le hψs (by rw [hcardQ, hZQ, hcardH])
  have hCV : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L := by
    refine le_antisymm ?_ (le_inf (Subgroup.map_subtype_le _) hO2)
    rintro x ⟨hxL, hxC⟩
    have h1 : ψ (QuotientGroup.mk ⟨x, hxL⟩) = 1 := by
      rw [hψ, autOnQuot_mk]
      exact MonoidHom.mem_ker.mp ((mem_ker_autOnSurj hLV ⟨x, hxL⟩).mpr hxC)
    have h2 : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      hψb.1 (h1.trans (map_one ψ).symm)
    rw [QuotientGroup.eq_one_iff] at h2
    exact ⟨⟨x, hxL⟩, h2, rfl⟩
  obtain ⟨hfix, hirr⟩ := hHat ↥V (sq_eq_one_of_hyp1223 hH hred) hcard (autOn L V) hperf hZ3 ⟨e⟩
  have hirrL : IsIrreducibleUnder L V := by
    refine ⟨hH.irrPlus.2.1, fun W hWV hLW => ?_⟩
    rcases hirr (W.subgroupOf V) (invariant_subgroupOf_of_le_normalizer hLV hLW) with h | h
    · left
      rwa [Subgroup.subgroupOf_eq_bot, disjoint_of_le_iff_left_eq_bot hWV] at h
    · right
      exact le_antisymm hWV (Subgroup.subgroupOf_eq_top.mp h)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, hZQ, ⟨eQ⟩, hCV, hcard,
    hirrL⟩)))))

theorem modules_of_concl328_nine
    (hH : Hyp1223 G T L V) [IsMulCommutative ↥V]
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ↥(autOn (L ⊔ T) V) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ n 1) : Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have := isSimpleGroup_sl_zmodTwo (n := n) (by omega)
  have heq := autOn_eq_autOn_sup_of_isSimpleGroup hLV hTV hH.normalizes e.isSimpleGroup
    (autOn_ne_bot_of_not_le_centralizer hLV (not_le_centralizer_of_hyp1223 hH))
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (K := ZMod 2)
    (n := n) (by omega) ((MulEquiv.subgroupCongr heq).trans e)
  exact Or.inl ⟨n, by omega, ⟨eQ⟩, hnat⟩

theorem modules_of_concl328_ten (hExt : ExtSqFourAltEight) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (e : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hext : SLExteriorTwo (V := ↥V) (autOn L V) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) 4) : Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  obtain ⟨e₈⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    ↥(autOn L V)).mp (lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) e)
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨8, by norm_num, le_rfl,
    ⟨e₈.toMonoidHom.comp (autOnSurj hLV), e₈.surjective.comp (autOnSurj_surjective hLV),
      ker_comp_autOnSurj hLV e₈⟩,
    hExt ↥V (sq_eq_one_of_hyp1223 hH hred) (autOn L V) ⊤ _ hext⟩)))

theorem modules_of_concl328_eleven
    (hL52 : L52TenFixedPointFree) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (e : ↥(autOn (L ⊔ T) V) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hcard : Nat.card V = 2 ^ 10) : Modules12_2_2 L V := by
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have := isSimpleGroup_sl_zmodTwo (n := 5) (by norm_num)
  have heq := autOn_eq_autOn_sup_of_isSimpleGroup hLV hTV hH.normalizes e.isSimpleGroup
    (autOn_ne_bot_of_not_le_centralizer hLV (not_le_centralizer_of_hyp1223 hH))
  set e' := (MulEquiv.subgroupCongr heq).trans e
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (K := ZMod 2)
    (n := 5) (by norm_num) e'
  have hfix := hL52 ↥V (sq_eq_one_of_hyp1223 hH hred) hcard (autOn L V) ⟨e'⟩
    (commV_autOn_eq_top hLV (commutator_eq_of_hyp1223 hH)) (irreducible_autOn_of_hyp1223 hH)
  have hC := (fixV_autOn_eq_bot_iff hLV).mp hfix
  exact Or.inr (Or.inr (Or.inl ⟨⟨eQ⟩, hcard, isIrreducibleUnder_of_hyp1223 hH hC⟩))

theorem false_of_concl701_orth
    (h6220 : Stmt6_2_20) (hH : Hyp1223 G T L V) [IsMulCommutative ↥V]
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hM : quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G))) {n : ℕ} (hn : 1 < n)
    (h : BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ n) : False := by
  obtain ⟨K, _, _, _, hK, π, hπ, -⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hnc := not_le_centralizer_of_hyp1223 hH
  have : Fintype K := Fintype.ofFinite K
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    QuasithinUnique.AppE.sl2_isSimpleGroup (n := 2 * n) (by omega)
      (by rw [← Nat.card_eq_fintype_card, hK])
  have hsimple' : IsSimpleGroup ↥(Assembly.LowTwoRank.StatedSL 2 K) :=
    (specialLinearGroupEquivStatedSL 2 K).symm.isSimpleGroup
  have : IsSimpleGroup (FFModel.twistTensor n (Assembly.LowTwoRank.StatedSL 2 K)).Gam := hsimple'
  obtain ⟨eA⟩ := nonempty_mulEquiv_of_surjective_of_isSimpleGroup (exists_ne_one_autOn hLV hnc) π hπ
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (n := 2) le_rfl
    (eA.trans (specialLinearGroupEquivStatedSL 2 K).symm)
  set eS := eQ.trans (specialLinearGroupEquivStatedSL 2 K)
  have : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := eS.toEquiv.nontrivial
  have hLieQ : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * n) :=
    lieModel_psl_two_of_mulEquiv hH.quasisimple.1 hK eS
  rcases h6220 G T (Subgroup.normalizer (L : Set G)) L V (2 * n) hH.simple hH.nonabelian hH.qtke
      hH.sylow hM hH.normalizes hH.maximal hH.faithful Subgroup.le_normalizer le_rfl (by omega)
      hLieQ (le_sup_of_hyp1223 hH) hred
      (by rw [commutator_eq_of_hyp1223 hH]; exact hH.irrPlus.2.1) with
    ⟨h2, -⟩ | hLie2 | hM22 | hM23
  · omega
  · exact hH.notAlt (alt12_2_2_of_alt12_2_2Lie hLie2)
  · exact hH.notAlt (Or.inr (Or.inr (Or.inl hM22)))
  · exact hH.notAlt (Or.inr (Or.inr (Or.inr (Or.inl hM23))))

end Cases

end CFSG.Quasithin.H13
