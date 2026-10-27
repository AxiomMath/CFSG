module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCU
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup conjAut fieldAut
  dualAut mem_linearAutGroup_iff conjAut_mem_linearAutGroup automorphism_generation)
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (finite_mulAut_projectiveSL)
open CFSG.LocalAnalysis.ComponentInitial (card_ringAut_and_isCyclic)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open Matrix

namespace ProofKSL3Two

open ProofHess

theorem mem_of_pow_mem_of_coprime {M : Type*} [Group M] (H : Subgroup M) {x : M} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at h
  have hx : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add,
      ← h, zpow_one]
  rw [hx]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem eq_one_of_pow_two_pow_of_odd {M : Type*} [Group M] [Finite M] (hM : Odd (Nat.card M))
    {a : M} {k : ℕ} (ha : a ^ 2 ^ k = 1) : a = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card M) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hM)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha)
    (orderOf_dvd_natCard a))

theorem false_of_elemAbelian_section {G Q : Type*} [Group G] [Group Q] [Finite G]
    {U E N : Subgroup G} (Ψ : ↥U →* Q) (hΨ : Function.Injective Ψ) (F : Subgroup Q) [F.Normal]
    (hF : IsCyclic F) [Finite (Q ⧸ F)] (hQF : Nat.card (Q ⧸ F) ≤ 2) (hEU : E ≤ U)
    (hN : (N.subgroupOf E).Normal) (hel : IsElementaryAbelian 2 (↥E ⧸ N.subgroupOf E))
    (hc : Nat.card (↥E ⧸ N.subgroupOf E) = 2 ^ 4) : False := by
  set χ : ↥E →* Q ⧸ F := (QuotientGroup.mk' F).comp (Ψ.comp (Subgroup.inclusion hEU)) with hχ
  set C := χ.ker with hC
  have hCF : ∀ c : C, Ψ (Subgroup.inclusion hEU (c : ↥E)) ∈ F := fun c =>
    (QuotientGroup.eq_one_iff _).mp c.2
  set ι : C →* F := (Ψ.comp ((Subgroup.inclusion hEU).comp C.subtype)).codRestrict F hCF with hι
  have hιinj : Function.Injective ι := by
    intro c c' hcc
    have h1 := congrArg Subtype.val hcc
    simp only [hι] at h1
    exact Subtype.ext (Subgroup.inclusion_injective hEU (hΨ h1))
  have hCcyc : IsCyclic C := isCyclic_of_injective ι hιinj
  have hCidx : C.index ≤ 2 := by
    rw [hC, Subgroup.index_ker]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hQF
  set π := QuotientGroup.mk' (N.subgroupOf E) with hπ
  set C' := C.map π with hC'
  have hC'cyc : IsCyclic C' :=
    isCyclic_of_surjective (π.subgroupMap C) (MonoidHom.subgroupMap_surjective _ _)
  have hexp : Monoid.exponent C' ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p _
  have hC'2 : Nat.card C' ≤ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have hidx : C'.index ≤ 2 := by
    have h1 := Subgroup.index_map_dvd C (QuotientGroup.mk'_surjective (N.subgroupOf E))
    have h2 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1).trans hCidx
  have hmul := Subgroup.card_mul_index C'
  rw [hc] at hmul
  nlinarith

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem eq_one_of_commute_two_pow_model (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) (hodd : Odd (Nat.card Kˣ)) {y : GL (Fin 3) K}
    (hy : y ∈ slPi π 3 (p ^ f) K) (hy3 : ProjGenLinGroup.mk y ^ 3 = 1)
    (hy1 : ProjGenLinGroup.mk y ≠ 1) {x : ProjGenLinGroup (Fin 3) K}
    (hx : x ∈ projImage (slPi π 3 (p ^ f) K))
    (hxy : x * ProjGenLinGroup.mk y = ProjGenLinGroup.mk y * x) {k : ℕ} (hxk : x ^ 2 ^ k = 1) :
    x = 1 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ := type1_of_lift hK hq h9 hy hy3 hy1
  have hzs : z ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hxo : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hxcop : Nat.Coprime 3 (orderOf x) :=
    Nat.Coprime.coprime_dvd_right hxo (Nat.Coprime.pow_right k (by norm_num))
  obtain ⟨s, hs, rfl, hso⟩ := exists_lift_pow_eq_one hK hx hxcop
  have hsk : s ^ 2 ^ k = 1 := by
    obtain ⟨m, hm⟩ := hxo
    rw [hm, pow_mul, hso, one_pow]
  have hsy : s * y = y * s := commute_of_mk_commute hK hs hy hxy.symm hxcop.symm hso
  have hsz : s * z = z * s := commute_of_mem_statedScalars hzs s
  have hs' : g⁻¹ * s * g ∈ slPi π 3 (p ^ f) K := by
    have h := conj_mem_slPi hπ (inv_mem hg) hs
    rwa [inv_inv] at h
  have hs'D : g⁻¹ * s * g ∈ Subgroup.centralizer {diagTau hτ} := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hD]
    calc g⁻¹ * s * g * (g⁻¹ * (y * z) * g) = g⁻¹ * ((s * y) * z) * g := by group
      _ = g⁻¹ * ((y * s) * z) * g := by rw [hsy]
      _ = g⁻¹ * (y * (s * z)) * g := by group
      _ = g⁻¹ * (y * (z * s)) * g := by rw [hsz]
      _ = g⁻¹ * (y * z) * g * (g⁻¹ * s * g) := by group
  have hmem : g⁻¹ * s * g ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} :=
    ⟨hs', hs'D⟩
  rw [centralizer_diagTau_eq hK hq hτ hτ1] at hmem
  obtain ⟨⟨a, b⟩, hab⟩ := hmem
  change torusHom ((a : Kˣ), (b : Kˣ)) = g⁻¹ * s * g at hab
  have hconj : (g⁻¹ * s * g) ^ 2 ^ k = g⁻¹ * s ^ 2 ^ k * g := by
    rw [show g⁻¹ * s * g = (MulAut.conj g⁻¹) s by simp, ← map_pow]
    simp
  have hab' : torusHom (((a : Kˣ), (b : Kˣ)) ^ 2 ^ k) = 1 := by
    rw [map_pow, hab, hconj, hsk]
    group
  have hab1 : ((a : Kˣ), (b : Kˣ)) ^ 2 ^ k = 1 := torusHom_injective (by rw [hab', map_one])
  have ha1 : (a : Kˣ) = 1 := eq_one_of_pow_two_pow_of_odd hodd (congrArg Prod.fst hab1)
  have hb1 : (b : Kˣ) = 1 := eq_one_of_pow_two_pow_of_odd hodd (congrArg Prod.snd hab1)
  have hs1 : g⁻¹ * s * g = 1 := by
    rw [← hab, ha1, hb1]
    exact map_one torusHom
  have : s = 1 := by
    calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      _ = 1 := by rw [hs1]; group
  rw [this, map_one]

theorem odd_card_units_of_piField (hK : PiField π 2 f K) : Odd (Nat.card Kˣ) := by
  have := hK.finite
  have hf : 1 ≤ f := hK.one_le
  rw [Nat.card_units, hK.card]
  have h2f : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h1f : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  cases π
  · change Odd ((2 ^ f) ^ 2 - 1)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (Nat.even_pow.mpr ⟨h2f, two_ne_zero⟩)
      odd_one
  · change Odd (2 ^ f - 1)
    exact Nat.Even.sub_odd h1f h2f odd_one

theorem eq_one_of_commute_two_pow {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hn3 : ¬ 3 ∣ n) (hX : Sec4.IsoLThreePi X 2 n) {d x : X} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hxd : x * d = d * x) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hn hX
  have h9K := not_nine_dvd_card_sub_one hK (not_two_pow_mod_nine hn3)
  set ψ : X →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (2 ^ n) K)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  obtain ⟨y, hyS, hy⟩ := (φ d).2
  have hψd : ψ d = ProjGenLinGroup.mk y := hy.symm
  have hy3 : ProjGenLinGroup.mk y ^ 3 = 1 := by rw [← hψd, ← map_pow, hd3, map_one]
  have hy1 : ProjGenLinGroup.mk y ≠ 1 := by
    rw [← hψd]
    exact fun h => hd1 (hψinj (by rw [h, map_one]))
  have h := eq_one_of_commute_two_pow_model hK hq h9K (odd_card_units_of_piField hK) hyS hy3 hy1
    (φ x).2 (x := ψ x) (by rw [← hψd, ← map_mul, ← map_mul, hxd]) (k := k)
    (by rw [← map_pow, hxk, map_one])
  exact hψinj (by rw [h, map_one])

theorem isInnerAut_of_mem_linearAutGroup {K : Type} [Field K] [Finite K]
    (_hodd : Odd (Nat.card Kˣ)) {τ : MulAut (projectiveSL 3 K)} (hτ : τ ∈ linearAutGroup 3 K)
    {k : ℕ} (hτk : τ ^ 2 ^ k = 1) : KFacts.IsInnerAut τ :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_range_conj_of_mem_linearAutGroup_of_coprime
    hτ (Nat.Coprime.pow_left k (by norm_num)) hτk

theorem isInnerAut_of_mem_psuConj_range {K : Type} [Field K] {p f : ℕ}
    {h : UnitaryFieldData p f K} (_hodd : Odd (p ^ f + 1)) {τ : MulAut (unitaryPSU h 3)}
    (hτ : τ ∈ (KFacts.psuConj h).range) {k : ℕ} (hτk : τ ^ 2 ^ k = 1) : KFacts.IsInnerAut τ :=
  CFSG.RankThree.PartTwo.KFacts.mem_range_conj_of_mem_psuConj_range_of_coprime hτ
    (Nat.Coprime.pow_left k (by norm_num)) hτk

theorem quotient_linearAutGroup_comm {K : Type} [Field K] [Finite K]
    [(linearAutGroup 3 K).Normal] (a b : MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H α =>
  induction b using QuotientGroup.induction_on with
  | H β =>
  obtain ⟨A, r, hr, rfl⟩ := KFacts.exists_conjAut_mul_mem_standardFieldGraph (by norm_num) α
  obtain ⟨B, r', hr', rfl⟩ := KFacts.exists_conjAut_mul_mem_standardFieldGraph (by norm_num) β
  have hA : (QuotientGroup.mk (conjAut 3 K A) : MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) =
      1 := (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A)
  have hB : (QuotientGroup.mk (conjAut 3 K B) : MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) =
      1 := (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup B)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hA, hB, one_mul, one_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, (KFacts.standardFieldGraph_commute hr hr').eq]

theorem card_quotient_field_le_two {K : Type} [Field K] [Finite K]
    [(linearAutGroup 3 K).Normal]
    (F : Subgroup (MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K)) [F.Normal]
    (hF : ∀ σ : K ≃+* K, (QuotientGroup.mk (fieldAut 3 K σ) :
      MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) ∈ F) :
    Nat.card ((MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) ⧸ F) ≤ 2 := by
  have : Finite (MulAut (projectiveSL 3 K)) := finite_mulAut_projectiveSL 3
  have hsurj : Function.Surjective (fun i : Fin 2 =>
      QuotientGroup.mk' F (QuotientGroup.mk' (linearAutGroup 3 K) (dualAut 3 K)) ^ (i : ℕ)) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective F x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (linearAutGroup 3 K) a
    obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 3) (by norm_num)
    obtain ⟨A, σ, ε, hε, rfl⟩ := hform α
    refine ⟨⟨ε, by omega⟩, ?_⟩
    have hA : QuotientGroup.mk' (linearAutGroup 3 K) (conjAut 3 K A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A)
    have hσ : QuotientGroup.mk' F (QuotientGroup.mk' (linearAutGroup 3 K) (fieldAut 3 K σ)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hF σ)
    simp only [map_mul, map_pow, hA, hσ, one_mul]
  exact (Nat.card_le_card_of_surjective _ hsurj).trans (by simp)

end ProofKSL3Two

open ProofKSL3Two ProofHess in
theorem kS1619CUL : KS1619CUL := by
  intro G _ _ L D U n hLs hn hn3 hiso hDL hD hD9 hU2 hUN hDU hsec hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := Proof1617.isoLThreePi_of_isSimpleGroup hLs hn hiso
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    subst hn1
    rcases hX with ⟨h3, -⟩ | ⟨-, ⟨φ⟩⟩
    · norm_num at h3
    · have : Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 2 1) :=
        Sec13.isSolvable_projSU_two
      have : Group.IsSolvable ↥L :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have hcomm : commutator ↥L = ⊥ := by
        have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
        · exact h
        · exact absurd h hlt.ne
      have hab : ∀ a b : ↥L, a * b = b * a := by
        intro a b
        have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [← commutator_def]; exact hcomm) (Subgroup.mem_top a)
        exact (Subgroup.mem_centralizer_iff.mp h1 b (Subgroup.mem_top b)).symm
      let _ : CommGroup ↥L := { mul_comm := hab }
      have hp := IsSimpleGroup.prime_card (α := ↥L)
      have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
      norm_num at hc
      rw [Nat.card_congr φ.toEquiv] at hp
      have h72 : Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 2 1) = 72 := by omega
      rw [h72] at hp
      norm_num at hp
  have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
  have hZ : Subgroup.center ↥L = ⊥ := by
    obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := exists_projImage_model hn hX
    exact Sec13.center_eq_bot_of_mulEquiv φ (center_projImage_slPi hKf hq hq2)
  set ρ : ↥U →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hUN) with hρ
  have hρapp : ∀ (u : ↥U) (l : ↥L), ((ρ u l : ↥L) : G) = (u : G) * l * (u : G)⁻¹ :=
    fun u l => rfl
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have huC : (u : G) ∈ U ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨u.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have h1 := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) hu
      simp only [hρapp, MulAut.one_apply] at h1
      calc l * u = (u : G) * l * (u : G)⁻¹ * u := by rw [h1]
        _ = u * l := by group
    rw [hbot, Subgroup.mem_bot] at huC
    exact Subtype.ext huC
  set W : Subgroup ↥U := (MulAut.conj : ↥L →* MulAut ↥L).range.comap ρ with hW
  set XG : Subgroup G := W.map U.subtype with hXG
  have hXGU : XG ≤ U := Subgroup.map_subtype_le W
  have hconjρ : ∀ (u : ↥U) (d : G) (hd : d ∈ D) (hdu : d * u * d⁻¹ ∈ U),
      ρ ⟨d * u * d⁻¹, hdu⟩ = MulAut.conj (⟨d, hDL hd⟩ : ↥L) * ρ u *
        MulAut.conj (⟨d, hDL hd⟩ : ↥L)⁻¹ := by
    intro u d hd hdu
    ext l
    simp only [MulAut.mul_apply, MulAut.conj_apply, hρapp]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρapp]
    group
  have hDX : D ≤ Subgroup.normalizer (XG : Set G) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := hx
    have hdu : d * (u : G) * d⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hDU hd) u).mp u.2
    refine ⟨⟨d * u * d⁻¹, hdu⟩, ?_, rfl⟩
    show ρ ⟨d * u * d⁻¹, hdu⟩ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range
    rw [hconjρ u d hd hdu]
    obtain ⟨l, hl⟩ := hu
    rw [← hl, ← map_mul, ← map_mul]
    exact ⟨_, rfl⟩
  have hXG2 : IsPGroup 2 XG := hU2.to_le hXGU
  have hXGcop : Nat.Coprime 3 (Nat.card XG) := by
    obtain ⟨k, hk⟩ := hXG2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hDel : CFSG.Open.IsElemAbelian 3 D := ⟨hD.1, hD.2⟩
  have hgen := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_three
    hDel (by rw [hD9]; norm_num) hDX hXGcop
  have hXGbot : XG = ⊥ := by
    rw [← hgen]
    refine iSup_eq_bot.mpr fun a => iSup_eq_bot.mpr fun haD => iSup_eq_bot.mpr fun ha1 => ?_
    rw [eq_bot_iff]
    rintro x ⟨⟨u, hu, rfl⟩, hxa⟩
    obtain ⟨l, hl⟩ := hu
    have hua : (u : G) * a = a * u := Subgroup.mem_centralizer_singleton_iff.mp hxa
    set a' : ↥L := ⟨a, hDL haD⟩ with ha'
    have hla : l * a' = a' * l := by
      have h1 : MulAut.conj l a' = ρ u a' := by rw [hl]
      have h2 : ((ρ u a' : ↥L) : G) = a := by
        rw [hρapp, show ((a' : ↥L) : G) = a from rfl, hua, mul_inv_cancel_right]
      have h3 : l * a' * l⁻¹ = a' := by
        rw [← MulAut.conj_apply, h1]
        exact Subtype.ext h2
      calc l * a' = l * a' * l⁻¹ * l := by group
        _ = a' * l := by rw [h3]
    obtain ⟨k, hk⟩ := hU2 u
    have hlk : l ^ 2 ^ k = 1 := by
      have h1 : MulAut.conj (l ^ 2 ^ k) = 1 := by rw [map_pow, hl, ← map_pow, hk, map_one]
      have h2 : l ^ 2 ^ k ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro m
        have h3 := congrArg (fun σ : MulAut ↥L => σ m) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc m * l ^ 2 ^ k = l ^ 2 ^ k * m * (l ^ 2 ^ k)⁻¹ * l ^ 2 ^ k := by rw [h3]
          _ = l ^ 2 ^ k * m := by group
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2
    have ha'3 : a' ^ 3 = 1 := Subtype.ext (by simpa [ha'] using hD.2 a haD)
    have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hl1 := eq_one_of_commute_two_pow hn hn3 hX ha'3 ha'1 hla hlk
    have hρu : ρ u = 1 := by rw [← hl, hl1, map_one]
    rw [hρinj (hρu.trans (map_one ρ).symm)]
    exact Subgroup.one_mem _
  have hinn : ∀ u : ↥U, KFacts.IsInnerAut (ρ u) → u = 1 := by
    intro u hu
    have hmem : (u : G) ∈ XG := ⟨u, hu, rfl⟩
    rw [hXGbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have h2el : ∀ u : ↥U, ∃ k : ℕ, ρ u ^ 2 ^ k = 1 := by
    intro u
    obtain ⟨k, hk⟩ := hU2 u
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨E, N, -, hEU, hNn, hel, hc⟩ := hsec
  have : Finite (MulAut ↥L) := Finite.of_injective (fun σ : MulAut ↥L => (σ : ↥L → ↥L))
    fun _ _ h => MulEquiv.ext (congrFun h)
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  ·
    set K := GaloisField 2 n with hKdef
    have hKc : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
    have hodd : Odd (Nat.card Kˣ) := by
      rw [Nat.card_units, hKc]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    obtain ⟨ψ⟩ := KFacts.nonempty_projSL_mulEquiv 3 K
    set e' : ↥L ≃* projectiveSL 3 K := e.trans ψ with he'
    have : (linearAutGroup 3 K).Normal := (KFacts.stdPinnedPSL_stable (by norm_num)).normal
    set Q := MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K with hQ
    have : Finite (MulAut (projectiveSL 3 K)) := finite_mulAut_projectiveSL 3
    set Ψ : ↥U →* Q :=
      (QuotientGroup.mk' (linearAutGroup 3 K)).comp ((MulAut.congr e').toMonoidHom.comp ρ) with hΨ
    have hΨinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker, hΨ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hu
      obtain ⟨k, hk⟩ := h2el u
      have h1 : MulAut.congr e' (ρ u) ^ 2 ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      have h2 := isInnerAut_of_mem_linearAutGroup hodd hu h1
      exact (Subgroup.mem_bot).mpr (hinn u ((KFacts.isInnerAut_congr e' (ρ u)).mp h2))
    set F : Subgroup Q := ((QuotientGroup.mk' (linearAutGroup 3 K)).comp (fieldAut 3 K)).range
      with hF
    have hcomm := quotient_linearAutGroup_comm (K := K)
    have : F.Normal := ⟨fun x hx g => by rw [hcomm g x, mul_inv_cancel_right]; exact hx⟩
    have hFcyc : IsCyclic F := by
      have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic Nat.prime_two K hKc).2
      exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have hFmem : ∀ σ : K ≃+* K, (QuotientGroup.mk (fieldAut 3 K σ) : Q) ∈ F :=
      fun σ => ⟨σ, rfl⟩
    exact false_of_elemAbelian_section Ψ hΨinj F hFcyc (card_quotient_field_le_two F hFmem) hEU
      hNn hel hc
  ·
    set K := GaloisField 2 (2 * n) with hKdef
    have hU : UnitaryFieldData 2 n K :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    have := hU.finite
    obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
    set e' : ↥L ≃* unitaryPSU hU 3 := e.trans ψ.symm with he'
    have : ((KFacts.psuConj hU).range).Normal := (KFacts.stdPinnedPSU3_stable hq2).normal
    set Q := MulAut (unitaryPSU hU 3) ⧸ (KFacts.psuConj hU).range with hQ
    have : Finite (MulAut (unitaryPSU hU 3)) :=
      Finite.of_injective (fun σ : MulAut (unitaryPSU hU 3) => (σ : unitaryPSU hU 3 → _))
        fun _ _ h => MulEquiv.ext (congrFun h)
    have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    set Ψ : ↥U →* Q := (QuotientGroup.mk' (KFacts.psuConj hU).range).comp
      ((MulAut.congr e').toMonoidHom.comp ρ) with hΨ
    have hΨinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker, hΨ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hu
      obtain ⟨k, hk⟩ := h2el u
      have h1 : MulAut.congr e' (ρ u) ^ 2 ^ k = 1 := by
        rw [← map_pow, hk, map_one]
      have h2 := isInnerAut_of_mem_psuConj_range hodd hu h1
      exact (Subgroup.mem_bot).mpr (hinn u ((KFacts.isInnerAut_congr e' (ρ u)).mp h2))
    have hQcyc : IsCyclic Q := by
      have : IsCyclic (K ≃+* K) :=
        (card_ringAut_and_isCyclic Nat.prime_two K (GaloisField.card 2 _ (by omega))).2
      refine isCyclic_of_surjective ((QuotientGroup.mk' (KFacts.psuConj hU).range).comp
        (KFacts.psuField hU)) fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H α =>
      obtain ⟨A, σ, rfl⟩ := KFacts.exists_psuConj_mul_psuField hq2 α
      refine ⟨σ, ?_⟩
      have hA1 : (QuotientGroup.mk (KFacts.psuConj hU A) : Q) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨A, rfl⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, hA1, one_mul]
    have hcard : Nat.card (Q ⧸ (⊤ : Subgroup Q)) ≤ 2 := by
      rw [← Subgroup.index, Subgroup.index_top]
      norm_num
    exact false_of_elemAbelian_section Ψ hΨinj ⊤ inferInstance hcard hEU hNn hel hc

theorem step1619CU_proved (h138 : Item138N) : Step1619CU :=
  step1619CU_of h138 kS1619CUL

end CFSG.RankThree.PartTwo.Sec16
