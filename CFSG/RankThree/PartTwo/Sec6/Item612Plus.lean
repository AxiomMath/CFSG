module

import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
public import CFSG.RankThree.PartTwo.Sec6.Item612Fitting
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.normal_subgroupOf_of_normalizes N (X ⊔ N)
      (sup_le hXN Subgroup.le_normalizer)
  have : (N.subgroupOf X).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.normal_subgroupOf_of_normalizes N X hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem not_dvd_card_sup {q : ℕ} (hq : q.Prime) {K N : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hK : ¬ q ∣ Nat.card K) (hN : ¬ q ∣ Nat.card N) :
    ¬ q ∣ Nat.card (K ⊔ N : Subgroup G) := by
  intro h
  have h1 := card_sup_mul_card_inf hKN
  have h2 : q ∣ Nat.card K * Nat.card N := h1 ▸ h.mul_right _
  rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
  · exact hK h3
  · exact hN h3

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three {d : G} (hd3 : d ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers d) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show orderOf d ∣ 3 ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hd3)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

theorem le_inf_centralizer_sup_theta {L : Subgroup G} {d : G}
    (hd : d ∈ thetaQuotCentralizer L) (hd3 : d ^ 3 = 1) :
    L ≤ (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set D := Subgroup.zpowers d with hD
  have hD3 : IsPGroup 3 D := isPGroup_zpowers_of_pow_three hd3
  have hDC : D ≤ thetaQuotCentralizer L := Subgroup.zpowers_le.mpr hd
  have hθ3 : ¬ 3 ∣ Nat.card θL := (theta_solvable_and_not_dvd L).2
  intro l hl
  set α : D →* MulAut G := MulAut.conj.comp D.subtype
  obtain ⟨y, hy, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hD3 α θL
    hθ3 l).2 (by
      intro a x hx
      change l⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ θL
      have ha := hDC a.2
      have h1 : l⁻¹ * ((a : G) * l * (a : G)⁻¹) ∈ θL := (mem_thetaQuotCentralizer_iff.mp ha).2 l hl
      have h2 : (a : G) * (l⁻¹ * x) * (a : G)⁻¹ ∈ θL :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_theta L
          (thetaQuotCentralizer_le_normalizer L ha)) _).mp hx
      have h3 := θL.mul_mem h1 h2
      rwa [show l⁻¹ * ((a : G) * l * (a : G)⁻¹) * ((a : G) * (l⁻¹ * x) * (a : G)⁻¹) =
        l⁻¹ * ((a : G) * x * (a : G)⁻¹) by group] at h3)
  have hyL : y ∈ L := by
    have := L.mul_mem hl (theta_le L hy)
    simpa using this
  have hyd : y ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : d * y * d⁻¹ = y := hyfix ⟨d, Subgroup.mem_zpowers d⟩
    calc y * d = (d * y * d⁻¹) * d := by rw [h1]
      _ = d * y := by group
  rw [show l = y * (y⁻¹ * l) by group]
  refine Subgroup.mul_mem_sup ⟨hyL, hyd⟩ ?_
  have := inv_mem hy
  simpa using this

theorem le_inSubgroup_perfectResidual_of_isPerfect {P X : Subgroup G} (hP : Group.IsPerfect P)
    (hPX : P ≤ X) : P ≤ inSubgroup perfectResidual X := by
  have hP' : Group.IsPerfect (P.subgroupOf X) := by
    have := hP
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have h := (perfect_residual_transport (MonoidHom.id X)).2.2 _ hP'
  intro x hx
  exact ⟨⟨x, hPX hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem inSubgroup_perfectResidual_mono {X Y : Subgroup G} (hXY : X ≤ Y) :
    inSubgroup perfectResidual X ≤ inSubgroup perfectResidual Y :=
  le_inSubgroup_perfectResidual_of_isPerfect (isPerfect_inSubgroup_perfectResidual X)
    ((Subgroup.map_subtype_le _).trans hXY)

theorem le_perfectResidual_sup {L X N : Subgroup G} (hLp : Group.IsPerfect L)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hLXN : L ≤ X ⊔ N) :
    L ≤ inSubgroup perfectResidual X ⊔ N := by
  have key : ∀ n : ℕ, L ≤ (derivedSeries X n).map X.subtype ⊔ N := by
    intro n
    induction n with
    | zero => rwa [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    | succ n ih =>
      have hDn : (derivedSeries X n).map X.subtype ≤ Subgroup.normalizer (N : Set G) :=
        (Subgroup.map_subtype_le _).trans hXN
      calc L = ⁅L, L⁆ := (commutator_self_eq_of_isPerfect hLp).symm
        _ ≤ ⁅(derivedSeries X n).map X.subtype ⊔ N, (derivedSeries X n).map X.subtype ⊔ N⁆ :=
          Subgroup.commutator_mono ih ih
        _ ≤ ⁅(derivedSeries X n).map X.subtype, (derivedSeries X n).map X.subtype ⊔ N⁆ ⊔ N :=
          commutator_sup_le_of_le_normalizer hDn (sup_le hDn Subgroup.le_normalizer)
        _ ≤ ⁅(derivedSeries X n).map X.subtype, (derivedSeries X n).map X.subtype⁆ ⊔ N := by
          refine sup_le ?_ le_sup_right
          rw [Subgroup.commutator_comm]
          exact commutator_sup_le_of_le_normalizer hDn hDn
        _ = (derivedSeries X (n + 1)).map X.subtype ⊔ N := by
          rw [derivedSeries_succ, Subgroup.map_commutator]
  obtain ⟨⟨n, hn, -⟩, -⟩ := perfect_residual_characterization (G := X)
  rw [inSubgroup, hn]
  exact key n

theorem inf_theta_centralizer_le_theta {L : Subgroup G} {d : G}
    (hd : d ∈ thetaQuotCentralizer L) (hd3 : d ^ 3 = 1) :
    L ⊓ Subgroup.centralizer ({d} : Set G) ⊓
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set H := Subgroup.centralizer ({d} : Set G) with hH
  set θH := inSubgroup (aschbacherSolvableCore 3) H with hθH
  set M := L ⊓ H with hM
  set N0 := M ⊓ θH with hN0
  have hLcov := le_inf_centralizer_sup_theta hd hd3
  have hθHH : θH ≤ H := theta_le H
  have hHθ : H ≤ Subgroup.normalizer (θH : Set G) := le_normalizer_theta H
  have hMN0 : M ≤ Subgroup.normalizer (N0 : Set G) :=
    (le_inf Subgroup.le_normalizer (inf_le_right.trans hHθ)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  set W := N0 ⊔ θL with hW
  have hWL : W ≤ L := sup_le (inf_le_left.trans inf_le_left) (theta_le L)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine hLcov.trans (sup_le ?_ ?_)
    · apply le_normalizer_sup_of_conj
      · intro m hm x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hMN0 hm) x).mp hx)
      · intro m hm x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_theta L hm.1) x).mp hx)
    · apply le_normalizer_sup_of_conj
      · intro t ht x hx
        have htL := theta_le L ht
        have hxL : x ∈ L := hx.1.1
        have h1 : x⁻¹ * t * x⁻¹⁻¹ ∈ θL :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L (inv_mem hxL)) t).mp ht
        rw [show t * x * t⁻¹ = x * ((x⁻¹ * t * x⁻¹⁻¹) * t⁻¹) by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (θL.mul_mem h1 (inv_mem ht)))
      · intro t ht x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_theta L (theta_le L ht)) x).mp hx)
  have hN0θ : N0 ≤ Subgroup.normalizer (θL : Set G) :=
    (inf_le_left.trans inf_le_left).trans (le_normalizer_theta L)
  have hWsol : Group.IsSolvable W := by
    have : Group.IsSolvable θH := (theta_solvable_and_not_dvd H).1
    have hN0sol : Group.IsSolvable N0 :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_right : N0 ≤ θH))
        (Subgroup.inclusion_injective _)
    have h1 := isSolvable_sup_of_le_normalizer hN0θ (theta_solvable_and_not_dvd L).1 hN0sol
    rwa [sup_comm] at h1
  have hW3 : ¬ 3 ∣ Nat.card W := by
    have hN03 : ¬ 3 ∣ Nat.card N0 := fun h =>
      (theta_solvable_and_not_dvd H).2 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact not_dvd_card_sup Nat.prime_three hN0θ hN03 (theta_solvable_and_not_dvd L).2
  have := le_theta_of_normal hWL hLW hWsol hW3
  exact le_sup_left.trans this


theorem card_thetaQuot_lt {L K X Y : Subgroup G} (hXL : X ≤ L)
    (hLX : L ≤ X ⊔ inSubgroup (aschbacherSolvableCore 3) L) (hXY : X ≤ Y) (hYK : Y ≤ K)
    (hXθ : X ⊓ inSubgroup (aschbacherSolvableCore 3) K ≤ inSubgroup (aschbacherSolvableCore 3) L)
    (hYθ : ¬ K ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) K) :
    Nat.card (L ⧸ aschbacherSolvableCore 3 L) < Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  set μL := Nat.card (L ⧸ aschbacherSolvableCore 3 L)
  set μK := Nat.card (K ⧸ aschbacherSolvableCore 3 K)
  have hcL : Nat.card L = μL * Nat.card θL := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 L), hθL,
      inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  have hcK : Nat.card K = μK * Nat.card θK := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 K), hθK,
      inSubgroup, Subgroup.card_map_of_injective K.subtype_injective]
  have hXLθ : X ⊔ θL = L := le_antisymm (sup_le hXL (theta_le L)) hLX
  have hpL := card_sup_mul_card_inf (X := X) (N := θL) (hXL.trans (le_normalizer_theta L))
  rw [hXLθ, hcL] at hpL
  have hθLpos : 0 < Nat.card θL := Nat.card_pos
  have hθKpos : 0 < Nat.card θK := Nat.card_pos
  have h1 : μL * Nat.card (X ⊓ θL : Subgroup G) = Nat.card X := by
    have : (μL * Nat.card (X ⊓ θL : Subgroup G)) * Nat.card θL = Nat.card X * Nat.card θL := by
      rw [← hpL]; ring
    exact Nat.eq_of_mul_eq_mul_right hθLpos this
  have hpK := card_sup_mul_card_inf (X := X) (N := θK)
    ((hXY.trans hYK).trans (le_normalizer_theta K))
  have h2 : Nat.card (X ⊔ θK : Subgroup G) ≤ Nat.card (Y ⊔ θK : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le_sup_right hXY θK)
  have h3 : Nat.card (Y ⊔ θK : Subgroup G) < Nat.card K := by
    have hle : Y ⊔ θK ≤ K := sup_le hYK (theta_le K)
    by_contra h
    push Not at h
    exact hYθ (Subgroup.eq_of_le_of_card_ge hle h).ge
  have hXθKpos : 0 < Nat.card (X ⊓ θK : Subgroup G) := Nat.card_pos
  have h4 : Nat.card X * Nat.card θK < (μK * Nat.card (X ⊓ θK : Subgroup G)) * Nat.card θK := by
    rw [← hpK]
    calc Nat.card (X ⊔ θK : Subgroup G) * Nat.card (X ⊓ θK : Subgroup G)
        < Nat.card K * Nat.card (X ⊓ θK : Subgroup G) :=
          Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt h2 h3) hXθKpos
      _ = (μK * Nat.card (X ⊓ θK : Subgroup G)) * Nat.card θK := by rw [hcK]; ring
  have h5 : Nat.card X < μK * Nat.card (X ⊓ θK : Subgroup G) := Nat.lt_of_mul_lt_mul_right h4
  have h6 : Nat.card (X ⊓ θK : Subgroup G) ≤ Nat.card (X ⊓ θL : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hXθ)
  have h7 : μL * Nat.card (X ⊓ θK : Subgroup G) < μK * Nat.card (X ⊓ θK : Subgroup G) :=
    lt_of_le_of_lt ((Nat.mul_le_mul_left μL h6).trans h1.le) h5
  exact Nat.lt_of_mul_lt_mul_right h7


theorem commutator_inf_props {A E U F : Subgroup G} (hE : E ∈ collectionIn (partTwoE G) A)
    (hU : U ∈ fourGroups E) (hFE : F ≤ E) {c : G} (hcE : c ∈ E) :
    IsPGroup 2 (⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, F⁆ : Subgroup G) ∧
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c}, F⁆ ≤
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c} ∧
    E ≤ Subgroup.normalizer ((⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, F⁆ : Subgroup G) : Set G) ∧
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c}, F⁆ =
      ⁅⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c},
        F⁆, F⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEab := hE.1.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  set S := Q ⊓ Subgroup.centralizer {c} with hS
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hS2 : IsPGroup 2 S := hQ2.to_le inf_le_left
  have hEc : E ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))
  obtain ⟨hEU, -, -⟩ := mem_fourGroups_iff.mp hU
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := fun e he =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 (Subgroup.centralizer (U : Set G))) (Source.mem_normalizer_centralizer (hEU he))
  have hES : E ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf hEQ (hEc.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hFS : F ≤ Subgroup.normalizer (S : Set G) := hFE.trans hES
  have hVS : ⁅S, F⁆ ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hFS
  have hEF : E ≤ Subgroup.centralizer (F : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun f hf =>
      congrArg Subtype.val (hEab.1.is_comm.comm ⟨f, hFE hf⟩ ⟨e, he⟩)
  have hcop : (Nat.card F).Coprime (Nat.card S) := by
    obtain ⟨a, ha⟩ := (hE3.to_le hFE).exists_card_eq
    obtain ⟨b, hb⟩ := hS2.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b (by norm_num)
  exact ⟨hS2.to_le hVS, hVS, fun e he => Source.mem_normalizer_commutator (hES he)
    (Subgroup.centralizer_le_normalizer _ (hEF he)),
    (CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S F hcop hFS).symm⟩


theorem commutator_centralizer_not_le {L E V D : Subgroup G} (hV2 : IsPGroup 2 V)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVE : V = ⁅V, E⁆)
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hVC : ¬ V ≤ thetaQuotCentralizer L) (hD3 : IsPGroup 3 D) (hDE : D ≤ E)
    (hDC : D ≤ thetaQuotCentralizer L) :
    ¬ ⁅V ⊓ Subgroup.centralizer (D : Set G), E⁆ ≤ thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := thetaQuotCentralizer L with hC
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  set W := V ⊓ C with hW
  have hDV : D ≤ Subgroup.normalizer (V : Set G) := hDE.trans hEV
  have hDW : D ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf hDV (hDC.trans ((thetaQuotCentralizer_le_normalizer L).trans hCN))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hW3 : ¬ 3 ∣ Nat.card W :=
    Source.not_three_dvd_card_of_isPGroup_two (hV2.to_le inf_le_left)
  intro hV₀C
  apply hVC
  have hdec : ∀ v ∈ V, ∃ x ∈ V ⊓ Subgroup.centralizer (D : Set G), x⁻¹ * v ∈ W := by
    intro v hv
    set α : D →* MulAut G := MulAut.conj.comp D.subtype
    obtain ⟨x, hx, hxfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hD3 α W
      hW3 v).2 (by
        intro a y hy
        change v⁻¹ * ((a : G) * y * (a : G)⁻¹) ∈ W
        have ha := hDC a.2
        have h1 : v⁻¹ * ((a : G) * v * (a : G)⁻¹) ∈ W := by
          refine ⟨V.mul_mem (inv_mem hv) ((Subgroup.mem_normalizer_iff.mp (hDV a.2) v).mp hv), ?_⟩
          have h2 := conj_mem_thetaQuotCentralizer ha (inv_mem (hVL hv))
          have h3 := C.mul_mem h2 (inv_mem ha)
          rwa [show v⁻¹ * (a : G) * v⁻¹⁻¹ * (a : G)⁻¹ = v⁻¹ * ((a : G) * v * (a : G)⁻¹) by group]
            at h3
        have h2 : (a : G) * (v⁻¹ * y) * (a : G)⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hDW a.2) _).mp hy
        have h3 := W.mul_mem h1 h2
        rwa [show v⁻¹ * ((a : G) * v * (a : G)⁻¹) * ((a : G) * (v⁻¹ * y) * (a : G)⁻¹) =
          v⁻¹ * ((a : G) * y * (a : G)⁻¹) by group] at h3)
    have hxV : x ∈ V := by
      have := V.mul_mem hv hx.1
      simpa using this
    have hxD : x ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 : d * x * d⁻¹ = x := hxfix ⟨d, hd⟩
      calc d * x = (d * x * d⁻¹) * d := by group
        _ = x * d := by rw [h1]
    refine ⟨x, ⟨hxV, hxD⟩, ?_⟩
    have := inv_mem hx
    simpa using this
  rw [hVE, Subgroup.commutator_le]
  intro v hv e he
  obtain ⟨x, hx, hxw⟩ := hdec v hv
  set w := x⁻¹ * v
  have hvx : v = x * w := by simp [w]
  have hwe : ⁅w, e⁆ ∈ C := by
    rw [commutatorElement_def, show w * e * w⁻¹ * e⁻¹ = w * (e * w⁻¹ * e⁻¹) by group]
    exact C.mul_mem hxw.2 (by simpa using conj_mem_thetaQuotCentralizer (inv_mem hxw.2) (hEL he))
  have hxe : ⁅x, e⁆ ∈ C := hV₀C (Subgroup.commutator_mem_commutator hx he)
  rw [hvx, show ⁅x * w, e⁆ = (x * ⁅w, e⁆ * x⁻¹) * ⁅x, e⁆ by
    simp only [commutatorElement_def]; group]
  exact C.mul_mem (conj_mem_thetaQuotCentralizer hwe (hVL hx.1)) hxe


theorem step_of_fourGroupsPlus (hG : PartTwoStanding G) (h45 : Sec4.Item4_5)
    {A E U : Subgroup G} (hA : A ∈ partTwoS G) (hE : E ∈ collectionIn (partTwoE G) A)
    (hU : U ∈ fourGroups E) {c : G} (hcE : c ∈ E) (hc1 : c ≠ 1) {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c)
    (hVL : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, E⁆ ≤ Subgroup.normalizer (L : Set G))
    (hLV : ¬ ⁅L, ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c}, E⁆⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L)
    (hDE : A ⊓ thetaQuotCentralizer L ≤ E) {c₀ : G} (hc₀ : c₀ ∈ A ⊓ thetaQuotCentralizer L)
    (hc₀1 : c₀ ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c₀)
    (hYK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {c₀}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {c₀})) < K) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c₀},
      E⁆ ≤ Subgroup.normalizer (K : Set G) ∧
    ¬ ⁅K, ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
      Subgroup.centralizer {c₀}, E⁆⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K ∧
    Nat.card (L ⧸ aschbacherSolvableCore 3 L) < Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hAab := hA.1.1
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) with hQ
  set V := ⁅Q ⊓ Subgroup.centralizer {c}, E⁆ with hVdef
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  set C := thetaQuotCentralizer L with hC
  set D := A ⊓ C with hD
  set H₀ := Subgroup.centralizer ({c₀} : Set G) with hH₀
  obtain ⟨hV2, hVS, hEV, hVE⟩ := commutator_inf_props (F := E) ⟨hEmem, hEA⟩ hU le_rfl hcE
  have hLp := isPerfect_of_mem_thetaComponentsAt hL
  have hKp := isPerfect_of_mem_thetaComponentsAt hK
  have hc₀3 : c₀ ^ 3 = 1 := hAab.2 c₀ hc₀.1
  have hc₀E : c₀ ∈ E := hDE hc₀
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans (hAL L hL)
  have hD3 : IsPGroup 3 D :=
    Sec5.isPGroup_of_isElemAbelian (Sec5.isElemAbelian_of_le hAab inf_le_left)
  have hVC : ¬ V ≤ C := fun h => hLV ((commutator_le_theta_iff hVL).mpr h)
  set V₀ := ⁅V ⊓ Subgroup.centralizer (D : Set G), E⁆ with hV₀
  have hV₀C : ¬ V₀ ≤ C := commutator_centralizer_not_le hV2 hEV hVE hVL hEL hVC hD3 hDE inf_le_right
  have hV₀V : V₀ ≤ V := (Subgroup.commutator_mono inf_le_left le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hEV)
  have hV₀L : V₀ ≤ Subgroup.normalizer (L : Set G) := hV₀V.trans hVL
  have hcD : Subgroup.centralizer (D : Set G) ≤ H₀ :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc₀)
  have hEH₀ : E ≤ H₀ := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hEmem.1.1.is_comm.comm ⟨x, hx⟩ ⟨c₀, hc₀E⟩))
  have hV₀V₀' : V₀ ≤ ⁅Q ⊓ H₀, E⁆ :=
    Subgroup.commutator_mono (le_inf ((inf_le_left.trans hVS).trans inf_le_left)
      (inf_le_right.trans hcD)) le_rfl
  have hV₀H₀ : V₀ ≤ H₀ := (Subgroup.commutator_mono (inf_le_right.trans hcD) hEH₀).trans
    (Subgroup.commutator_le_self _)
  have hAK := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab hc₀.1 hc₀1
  have hV₀'K : ⁅Q ⊓ H₀, E⁆ ≤ Subgroup.normalizer (K : Set G) :=
    commutator_le_normalizer_of_mem_thetaComponentsAt (X := Q ⊓ H₀) inf_le_right
      (fun L' hL' => hEA.trans (hAK L' hL')) hK
  set M := L ⊓ H₀ with hM
  set Minf := inSubgroup perfectResidual M with hMinf
  set Y := inSubgroup perfectResidual (M ⊔ inSubgroup (aschbacherSolvableCore 3) H₀) with hY
  have hMinfM : Minf ≤ M := Subgroup.map_subtype_le _
  have hMinfY : Minf ≤ Y := inSubgroup_perfectResidual_mono le_sup_left
  have hYKle : Y ≤ K := hYK.le
  have hLcov := le_inf_centralizer_sup_theta hc₀.2 hc₀3
  have hLMinf : L ≤ Minf ⊔ θL :=
    le_perfectResidual_sup hLp (inf_le_left.trans (le_normalizer_theta L)) hLcov
  have hT := inf_theta_centralizer_le_theta hc₀.2 hc₀3
  have hθK : θK ≤ inSubgroup (aschbacherSolvableCore 3) H₀ := by
    rw [hθK, theta_eq_inf_of_mem_thetaComponentsAt hK]
    exact inf_le_right
  have hMinfθ : Minf ⊓ θK ≤ θL := (inf_le_inf hMinfM hθK).trans hT
  have hKV₀ : ¬ ⁅K, V₀⁆ ≤ θK := by
    intro hK0
    have hV₀M : V₀ ≤ Subgroup.normalizer (M : Set G) :=
      (le_inf hV₀L (hV₀H₀.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have : (perfectResidual M).Characteristic := (perfect_residual_characterization (G := M)).2.1
    have hV₀Minf : V₀ ≤ Subgroup.normalizer (Minf : Set G) := fun v hv =>
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (perfectResidual M)
        (hV₀M hv)
    have h1 : ⁅Minf, V₀⁆ ≤ θL := by
      have ha : ⁅Minf, V₀⁆ ≤ M :=
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hV₀Minf).trans hMinfM
      have hb : ⁅Minf, V₀⁆ ≤ inSubgroup (aschbacherSolvableCore 3) H₀ :=
        (Subgroup.commutator_mono (hMinfY.trans hYKle) le_rfl).trans (hK0.trans hθK)
      exact (le_inf ha hb).trans hT
    apply hV₀C
    rw [← commutator_le_theta_iff hV₀L]
    calc ⁅L, V₀⁆ ≤ ⁅Minf ⊔ θL, V₀⁆ := Subgroup.commutator_mono hLMinf le_rfl
      _ ≤ ⁅Minf, V₀⁆ ⊔ θL := commutator_sup_le_of_le_normalizer
          ((hMinfM.trans inf_le_left).trans (le_normalizer_theta L))
          (hV₀L.trans (normalizer_le_normalizer_theta L))
      _ ≤ θL := sup_le h1 le_rfl
  refine ⟨hV₀'K, fun h => hKV₀ ((Subgroup.commutator_mono le_rfl hV₀V₀').trans h), ?_⟩
  refine card_thetaQuot_lt (X := Minf) (Y := Y) (hMinfM.trans inf_le_left) hLMinf hMinfY hYKle
    hMinfθ fun hKY => ?_
  have hKW : K ≤ M ⊔ inSubgroup (aschbacherSolvableCore 3) H₀ :=
    hKY.trans (sup_le (Subgroup.map_subtype_le _) (hθK.trans le_sup_right))
  exact (lt_irrefl K) (lt_of_le_of_lt (le_inSubgroup_perfectResidual_of_isPerfect hKp hKW) hYK)

end CFSG.RankThree.PartTwo.Sec6
