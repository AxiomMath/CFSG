module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HNAOuter
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4
public import CFSG.RankThree.PartTwo.KFacts.KS222U4Even
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Gen
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Tor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Open (StatedProj StatedSU)

section Gen

theorem three_dvd_two_pow_add_one {k : ℕ} (hk : Odd k) : 3 ∣ 2 ^ k + 1 := by
  obtain ⟨m, rfl⟩ := hk
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  rw [h2, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, h4]

theorem center_eq_bot_of_simple_nonabelian {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ Subgroup.center S := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem le_inSubgroup_perfectResidual {G : Type} [Group G] {K C : Subgroup G} (hKC : K ≤ C)
    (hK : ⁅K, K⁆ = K) : K ≤ inSubgroup perfectResidual C := by
  set L' := K.subgroupOf C with hL'def
  have hL' : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hL'def, Subgroup.map_subgroupOf_eq_of_le hKC, hK]
  have h1 : ∀ k : ℕ, L' ≤ derivedSeries ↥C k := by
    intro k
    induction k with
    | zero => rw [derivedSeries_zero]; exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hL']
      exact Subgroup.commutator_mono ih ih
  have h2 : L' ≤ perfectResidual ↥C := le_iInf h1
  intro x hx
  exact ⟨⟨x, hKC hx⟩, h2 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end Gen

section Torus

open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagUHom diagU_injective)

theorem isElemAbelian_torusSU (F : Type) [Field F] :
    CFSG.Assembly.IsElemAbelian 3 (torusSU 3 4 F) := by
  refine isElemAbelian_map diagUHom ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun d hd => ?_⟩
  funext i
  rw [Pi.pow_apply, hd.1 i, Pi.one_apply]

theorem card_torusSU_three_four {F : Type} [Field F] [Finite F]
    (hζ : ∃ ζ : Fˣ, IsPrimitiveRoot ζ 3) : Nat.card (torusSU 3 4 F) = 27 := by
  rw [CFSG.RankThree.PartOne.KFU.torusSU, Subgroup.card_map_of_injective diagU_injective,
    CFSG.RankThree.PartOne.KFU.card_torusVec_eq (by norm_num) hζ 3]
  norm_num

theorem exists_unit_cube_root {k : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 k F)
    (h3 : 3 ∣ 2 ^ k + 1) : ∃ ζ : Fˣ, IsPrimitiveRoot ζ 3 := by
  obtain ⟨z, hz⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h Nat.prime_three h3
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

theorem exists_e27_unitarySU {k : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 k F)
    (h3 : 3 ∣ 2 ^ k + 1) : ∃ E : Subgroup (unitarySU 2 k F 4), Late.IsE27 E := by
  haveI := h.finite
  have hle : torusSU 3 4 F ≤ unitarySU 2 k F 4 :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU h h3
  refine ⟨(torusSU 3 4 F).subgroupOf (unitarySU 2 k F 4),
    isElemAbelian_comap _ (unitarySU 2 k F 4).subtype_injective (isElemAbelian_torusSU F), ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_torusSU_three_four (exists_unit_cube_root h h3)]

end Torus

section One


theorem rowOf425_projSU_four_two_one : RowOf425 (projSU 4 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 3 ⟨2, 1, Fact.out, Nat.one_pos⟩).Valid :=
    Ronan148L.valid_twistedA (by norm_num) (by omega)
  refine Ronan148L.rowOf425_of_lie_card ⟨_, hv⟩
    ⟨(Census.typeTwistedAGroupEquivProjSU 3 ⟨2, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩
    (M := 25920) (B := 30) (fun S _ _ ⟨e⟩ => ?_) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSU_four_two]

end One

section Even

theorem noCC425_of_projSU_four_even {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (e : S ≃* projSU 4 2 n) : NoCC425 S := by
  intro s K hcc
  have hs1 : s ≠ 1 := by
    intro h
    have := hcc.orderOf_eq
    rw [h, orderOf_one] at this
    norm_num at this
  have hℓ : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hcc.orderOf_eq]
  have hC : (⊤ : Subgroup S) ⊓
      Subgroup.centralizer ((Subgroup.zpowers s : Subgroup S) : Set S) =
        Subgroup.centralizer {s} := by
    rw [top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hJ := Sec21.ks222U4Even S ⊤ (Subgroup.zpowers s) n (by omega) he
    ⟨Subgroup.topEquiv.trans e⟩ le_top hℓ
  rw [hC] at hJ
  set C := Subgroup.centralizer ({s} : Set S) with hCdef
  set J := inSubgroup perfectResidual C with hJdef
  have hcard : ∀ m : ℕ, 1 ≤ m → 2 ≤ m → Nat.card (GaloisField 2 m) ≠ 2 ∧
      Nat.card (GaloisField 2 m) ≠ 3 := by
    intro m hm1 hm2
    rw [GaloisField.card 2 m (by omega)]
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    constructor <;> omega
  have hJs : IsSimpleGroup J := by
    rcases hJ with hJ1 | hJ2
    · obtain ⟨eJ⟩ := hJ1
      obtain ⟨h2, h3⟩ := hcard n (by omega) hn
      haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 n) le_rfl
        (Or.inr h2) (Or.inr h3)
      exact eJ.isSimpleGroup
    · obtain ⟨eJ⟩ := hJ2
      obtain ⟨h2, h3⟩ := hcard (2 * n) (by omega) (by omega)
      haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 (2 * n)) le_rfl
        (Or.inr h2) (Or.inr h3)
      exact eJ.isSimpleGroup
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hcc.isQuasisimple.1
  have hKJ : K ≤ J := le_inSubgroup_perfectResidual hcc.le_centralizer hperf
  have hJC : J ≤ C := Subgroup.map_subtype_le _
  have hsub : (K.subgroupOf J).IsSubnormal := by
    have h := hcc.isSubnormal.comap (Subgroup.inclusion hJC)
    have heq : (K.subgroupOf C).comap (Subgroup.inclusion hJC) = K.subgroupOf J := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h
  have hsJ : s ∈ J := hKJ hcc.mem
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hJs hsub with h | h
  · apply hs1
    have hmem : (⟨s, hsJ⟩ : J) ∈ K.subgroupOf J := Subgroup.mem_subgroupOf.mpr hcc.mem
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · have hJK : J ≤ K := fun y hy => by
      have hmem : (⟨y, hy⟩ : J) ∈ K.subgroupOf J := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hsZ : (⟨s, hsJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hcc.le_centralizer (hJK y.2)))
    haveI := hJs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hZ | hZ
    · apply hs1
      rw [hZ, Subgroup.mem_bot] at hsZ
      exact congrArg Subtype.val hsZ
    ·
      apply hs1
      have hKab : ⁅K, K⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyZ : (⟨y, hKJ hy⟩ : J) ∈ Subgroup.center J := hZ ▸ Subgroup.mem_top _
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨x, hKJ hx⟩)).symm
      rw [hperf] at hKab
      have := hcc.mem
      rw [hKab, Subgroup.mem_bot] at this
      exact this


theorem rowOf425_projSU_four_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    RowOf425 (projSU 4 2 n) :=
  rowOf425_of_noCC fun _ _ _ _ _ ⟨e⟩ => noCC425_of_projSU_four_even hn he e

end Even

section Odd

open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagUHom diagU_injective permGL symAct)

variable {S : Type} [Group S] [Finite S]

theorem nonempty_quotCenter_mulEquiv {n : ℕ} (hZ : Subgroup.center S = ⊥)
    (e : S ≃* projSU 4 2 n) [Fact (Nat.Prime 2)] :
    Nonempty (S ⧸ Subgroup.center S ≃* StatedProj (StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n)))) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (e.trans (CFSG.PGLModel.projSUEquivStatedProj 4 2 n))⟩

theorem exists_e27_of_projSU_four_odd (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) (e : S ≃* projSU 4 2 n) :
    ∃ E : Subgroup S, Late.IsE27 E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have hpq := three_dvd_two_pow_add_one hodd
  have hZ := center_eq_bot_of_simple_nonabelian hs hna
  obtain ⟨eS⟩ := nonempty_quotCenter_mulEquiv hZ e
  obtain ⟨ψ, -⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso_le hn hK Nat.prime_three hpq hZ eS
    ⊥ (fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow])
    (fun x hx y hy => by rw [Subgroup.mem_bot.mp hx, one_mul, mul_one])
  obtain ⟨E, hE⟩ := exists_e27_unitarySU hU hpq
  exact ⟨E.map ψ.toMonoidHom, isElemAbelian_map _ hE.1, by
    rw [Subgroup.card_map_of_injective ψ.injective, hE.2]⟩

theorem e27Move_of_projSU_four_odd (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) (e : S ≃* projSU 4 2 n) : Ronan148L.E27Move S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 (2 * n) with hKdef
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have hpq := three_dvd_two_pow_add_one hodd
  have hζ := exists_unit_cube_root hU hpq
  have hZ := center_eq_bot_of_simple_nonabelian hs hna
  obtain ⟨eS⟩ := nonempty_quotCenter_mulEquiv hZ e
  intro E hE s hsE hs1
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso hn hK Nat.prime_three hpq hZ eS E
    (fun x hx => hE.1.2 x hx)
    (fun x hx y hy => congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (by rw [hE.2]; norm_num)
  set g₀ := ψ.symm s with hg₀
  have hψg₀ : ψ g₀ = s := MulEquiv.apply_symm_apply ψ s
  have hg₀T : (g₀ : GL (Fin 4) K) ∈ torusSU 3 4 K := (hψ g₀).mp (by rw [hψg₀]; exact hsE)
  obtain ⟨d, hd3, hdprod, hdg⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hg₀T
  set dv : torusVec 3 4 K := ⟨d, hd3, hdprod⟩ with hdv
  have hdv1 : dv ≠ 1 := by
    intro h
    apply hs1
    have hd1 : d = 1 := congrArg Subtype.val h
    have hg1 : g₀ = 1 := by
      apply Subtype.ext
      rw [← hdg, hd1, CFSG.RankThree.PartOne.KFU.diagU_one]
      rfl
    rw [← hψg₀, hg1, map_one]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 4), symAct 3 K σ dv ∉ Subgroup.zpowers dv := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ σ : Equiv.Perm (Fin 4), ∀ x ∈ Subgroup.zpowers dv,
        symAct 3 K σ x ∈ Subgroup.zpowers dv := by
      intro σ x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [map_zpow]
      exact Subgroup.zpow_mem _ (hcon σ) k
    rcases CFSG.RankThree.PartOne.KFU.eq_bot_or_eq_top_of_symInvariant Nat.prime_three
        (by norm_num) (by norm_num) _ hinv with h | h
    · exact hdv1 (Subgroup.zpowers_eq_bot.mp h)
    · have hdv3 : dv ^ 3 = 1 := by
        apply Subtype.ext
        funext i
        exact hd3 i
      have hc1 : Nat.card (Subgroup.zpowers dv) ≤ 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) hdv3
      have hc2 : Nat.card (⊤ : Subgroup (torusVec 3 4 K)) = 27 := by
        rw [Subgroup.card_top, CFSG.RankThree.PartOne.KFU.card_torusVec_eq (by norm_num) hζ 3]
        norm_num
      rw [h] at hc1
      omega
  set P : unitarySU 2 n K 4 := ⟨permGL σ, CFSG.RankThree.PartOne.KFU.permGL_mem_unitarySU hU σ⟩
    with hP
  have hPconj : ∀ x : GL (Fin 4) K, x ∈ torusSU 3 4 K ↔
      permGL σ * x * (permGL σ)⁻¹ ∈ torusSU 3 4 K := by
    intro x
    constructor
    · exact (CFSG.RankThree.PartOne.KFU.normPerm_permGL (p := 3) σ).1 x
    · intro hx
      have h := (CFSG.RankThree.PartOne.KFU.normPerm_permGL (p := 3) σ⁻¹).1 _ hx
      have heq : (permGL σ)⁻¹ * (permGL σ * x * (permGL σ)⁻¹) * ((permGL σ)⁻¹)⁻¹ = x := by
        group
      rwa [map_inv, heq] at h
  refine ⟨ψ P, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← MulEquiv.apply_symm_apply ψ h, ← map_inv, ← map_mul, ← map_mul, hψ, hψ]
    exact hPconj _
  · intro hmem
    have hs' : ψ P * s * (ψ P)⁻¹ ∈ Subgroup.zpowers s :=
      (Subgroup.mem_normalizer_iff.mp hmem s).mp (Subgroup.mem_zpowers s)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs'
    have hk' : g₀ ^ k = P * g₀ * P⁻¹ := by
      apply ψ.injective
      rw [map_zpow, map_mul, map_mul, map_inv, hψg₀, hk]
    have hk'' : (g₀ : GL (Fin 4) K) ^ k = permGL σ * (g₀ : GL (Fin 4) K) * (permGL σ)⁻¹ := by
      have h := congrArg (fun x : unitarySU 2 n K 4 => (x : GL (Fin 4) K)) hk'
      simpa [hP] using h
    rw [← hdg, CFSG.RankThree.PartOne.KFU.permGL_conj_diagU] at hk''
    have hdk : d ^ k = d ∘ σ.symm := by
      apply diagU_injective
      rw [← hk'']
      exact map_zpow diagUHom d k
    apply hσ
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_zpow]
    exact hdk


theorem noThreeCover_projSU_four_two {n : ℕ} (hn : 2 ≤ n) : NoThreeCover (projSU 4 2 n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 2 n :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  have hSU := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _)
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine Ronan148L.noThreeCover_of_table ?_ ?_
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row hSU (by decide) (Or.inl h4)).2
  · have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    have hg : Nat.gcd 4 (2 ^ n + 1) = 1 :=
      (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ 2) _)
    simp [CFSG.Blueprint.Multiplier.genericOrders, hg]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rfl


theorem outerCubeE27_projSU_four {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) :
    OuterCubeE27 (projSU 4 2 n) := by
  intro τ hτ hout
  obtain ⟨k, rfl, hk, F, _, h₀, ⟨eF⟩⟩ :=
    RonanK429Lie.exists_autFix_mulEquiv_unitarySU_four hn hτ hout
  have hkodd : Odd k := (Nat.odd_mul.mp hodd).2
  obtain ⟨E, hE⟩ := exists_e27_unitarySU h₀ (three_dvd_two_pow_add_one hkodd)
  refine ⟨(E.map eF.symm.toMonoidHom).map (autFix τ).subtype,
    ⟨isElemAbelian_map _ (isElemAbelian_map _ hE.1), ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective (autFix τ).subtype_injective,
      Subgroup.card_map_of_injective eF.symm.injective, hE.2]
  · rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact mem_autFix.mp (eF.symm y).2

theorem rowOf425_projSU_four_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    RowOf425 (projSU 4 2 n) := fun S _ _ hs hna ⟨e⟩ =>
  row425_of_e27Move_outer (NoThreeCover.of_mulEquiv e (noThreeCover_projSU_four_two (by omega)))
    ((outerCubeE27_projSU_four (by omega) hodd).of_mulEquiv e)
    (exists_e27_of_projSU_four_odd hs hna (by omega) hodd e)
    (e27Move_of_projSU_four_odd hs hna (by omega) hodd e)

end Odd

section Row


theorem rowOf425_projSU_four_two (n : ℕ) (hn : 1 ≤ n) : RowOf425 (projSU 4 2 n) := by
  rcases Nat.even_or_odd n with he | hodd
  · exact rowOf425_projSU_four_even (by obtain ⟨m, rfl⟩ := he; omega) he
  · rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 1 := by obtain ⟨m, rfl⟩ := hodd; omega
      exact rowOf425_projSU_four_two_one
    · exact rowOf425_projSU_four_odd h hodd

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
