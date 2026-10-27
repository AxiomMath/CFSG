module

public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Local
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofTwo
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGHeisCase
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylComp
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType.NbrU63

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType CFSG.SectionRank.OddCover
  CFSG.StandardType.Line63.H5

variable {F : Type} [Field F] {n : ℕ} {G : Type} [Group G] [Finite G]

theorem card_range_ggBeta_eq {K Bs : Subgroup G} (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (ggBeta K θ hN).range = Nat.card (ggGamma K hN).range := by
  have hker : (ggBeta K θ hN).ker = (ggGamma K hN).ker := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ggGamma_eq_one_iff, ggBeta_eq]
    exact ⟨fun h => mem_centralizer_of_ggLAut_eq_one K θ hK h,
      fun h => ggLAut_eq_one_of_mem_centralizer K θ h⟩
  have h1 := TableB.card_range_mul_card_ker (ggBeta K θ hN)
  have h2 := TableB.card_range_mul_card_ker (ggGamma K hN)
  rw [hker] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem all_inner_of_rank (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1)
    {K Bs : Subgroup G} (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (unitarySU 2 n F 6))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥K)) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hrank : LargeEvenTwoLocalRank 3 G ≤ 4) {y : G}
    (hyBs : y ∈ Bs) (hy1 : y ≠ 1) (hyC : ∀ k ∈ K, y * k = k * y) (hyK : y ∉ K) :
    ∀ (b : G) (hb : b ∈ Bs), ∃ (M : GL (Fin 6) F) (hMgu : M ∈ LargeEvenGUSet (Fin 6) F (2 ^ n)),
      IsInner n M ∧ ggLAut K θ ⟨b, hN hb⟩ = TableB.projConj (unitarySU 2 n F 6)
        ⟨M, TableBUE.gu_subset_normalizer (d := 6) hKd hMgu⟩ := by
  haveI : Finite F := hKd.finite
  classical
  intro b hb
  obtain ⟨A, hA, hgraph⟩ := ggLAut_mem_of_induces K θ hN hBI hb
  have hAN : A ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd hA
  have hac0 : ggLAut K θ ⟨b, hN hb⟩ = TableB.projConj (unitarySU 2 n F 6) ⟨A, hAN⟩ := by
    ext r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective r
    exact (hgraph s (conjN A hAN s) rfl).trans (projConj_mk_eq A hAN s).symm
  refine ⟨A, hA, ?_, hac0⟩
  by_contra hMn
  obtain ⟨u, hu⟩ := CFSG.StandardType.TableBU63.exists_unitary_of_gu hKd hA
  have hgn : ¬ IsInner n (GeneralLinearGroup.scalar (Fin 6) u * A) :=
    fun h => hMn ((isInner_scalar_mul_iff u A).mp h)
  have hgN : GeneralLinearGroup.scalar (Fin 6) u * A ∈
      Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd
      (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hu)
  have hac : ggLAut K θ ⟨b, hN hb⟩ = TableB.projConj (unitarySU 2 n F 6)
      ⟨GeneralLinearGroup.scalar (Fin 6) u * A, hgN⟩ := by
    rw [hac0]
    have hu' : GeneralLinearGroup.scalar (Fin 6) u ∈ LargeEvenScalars (Fin 6) F := ⟨u, rfl⟩
    have : (⟨GeneralLinearGroup.scalar (Fin 6) u * A, hgN⟩ :
        ↥(Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))) =
        ⟨GeneralLinearGroup.scalar (Fin 6) u, TableB.scalar_mem_normalizer _ hu'⟩ * ⟨A, hAN⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, TableB.projConj_of_scalar _ hu', one_mul]
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hya : y * b = b * y := CFSG.StandardType.TableB.IsElemAbelian.comm hBs hyBs hb
  have h5 := five_le_twoLocalRank_of_outer hKd hpq hK θ hZ2 (hN hb) (hBs.2 b hb) hu hgn hac hy3
    hy1 hyC hya hyK
  omega

theorem card_le_of_center_two (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1)
    {K Bs : Subgroup G} (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (unitarySU 2 n F 6))
    (hZ2 : IsPGroup 2 (Subgroup.center ↥K)) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hrank : LargeEvenTwoLocalRank 3 G ≤ 4)
    (hA27 : Nat.card (ggGamma K hN).range = 3 ^ 3) :
    Nat.card Bs ≤ 3 ^ 4 := by
  classical
  haveI : Finite F := hKd.finite
  have h2 : IsPGroup 2 (ggQuotHom θ).ker := by rw [ker_ggQuotHom θ]; exact hZ2
  obtain ⟨U, E, hU, hU2, hEU, hE, hEc⟩ :=
    exists_twoLocal_three_of_quot hKd hpq (ggQuotHom θ) (ggQuotHom_surjective θ) h2
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G) with hCdef
  have hC : CFSG.Open.IsElemAbelian 3 C := CFSG.StandardType.TableB.isElemAbelian_mono hBs
    inf_le_left
  have hCf : ∀ g ∈ C, ∀ k : ↥K, K.subtype k * g = g * K.subtype k := fun g hg k =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 k k.2
  have hEZ : E ⊓ Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heE, heZ⟩
    obtain ⟨k, hk⟩ := hZ2 ⟨e, heZ⟩
    have ho3 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 e heE)
    have ho2 : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    have hg : orderOf e ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd ho3 ho2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num))] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  have hle := card_mul_pow_le_of_normalizes Nat.prime_three K.subtype K.subtype_injective hC hCf
    hU hU2 hEU hE hEZ hEc
  have h1 : Nat.card C * 3 ^ 3 ≤ 3 ^ 4 :=
    hle.trans (Nat.pow_le_pow_right (by norm_num) hrank)
  have hcard := card_range_ggGamma_mul_card_inf hN
  rw [hA27, ← hCdef] at hcard
  norm_num at h1 hcard ⊢
  omega

theorem not_ggFixCompCyclic_of_heisTriple (hKd : UnitaryFieldData 2 n F) (hpq : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n F 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : Nat.card A = 27) {x y z : GL (Fin 6) F}
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))
    (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))
    (hxu : x ∈ primeFormUnitary hKd (idGram F 6)) (hyu : y ∈ primeFormUnitary hKd (idGram F 6))
    (hzu : z ∈ primeFormUnitary hKd (idGram F 6)) {ζ : Fˣ}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hζ : IsPrimitiveRoot ζ 3)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hzs : z ∉ LargeEvenScalars (Fin 6) F)
    (hxA : TableB.projConj (unitarySU 2 n F 6) ⟨x, hxN⟩ ∈ TypeA.inducedSub ψ A)
    (hyA : TableB.projConj (unitarySU 2 n F 6) ⟨y, hyN⟩ ∈ TypeA.inducedSub ψ A)
    (hzA : TableB.projConj (unitarySU 2 n F 6) ⟨z, hzN⟩ ∈ TypeA.inducedSub ψ A) :
    ∀ a₀ ∈ A, a₀ ≠ 1 → ¬ GGFixCompCyclic 3 a₀ := by
  haveI : Finite F := hKd.finite
  have hAbcard : Nat.card (TypeA.inducedSub ψ A) = 27 := by
    rw [TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)]
    exact hcard
  intro a₀ ha₀ ha₀1 hcyc
  obtain ⟨x₀, -, hx₀⟩ := hAI a₀ ha₀
  have hx₀Ab : x₀ ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a₀, ha₀, hx₀⟩
  obtain ⟨i, j, k, hM, hi, hj, hk, hx₀eq⟩ := exists_mono_of_card hKd hpq hAbcard hxN hyN
    hzN hζ hxA hyA hzA hxy hxz hyz hz3 hzs x₀ hx₀Ab
  have hc : ∀ l, TableB.projConj (unitarySU 2 n F 6) ⟨x ^ i * y ^ j * z ^ k, hM⟩ (ψ l) =
      ψ (a₀ l) := fun l => by rw [← hx₀eq]; exact hx₀ l
  by_cases hij : i ≠ 0 ∨ j ≠ 0
  · exact UnitSixThreeKG.not_ggFixCompCyclic_of_shapeBad hKd hpq hψ hker hM
      (UnitSixThreeKG.shapeBad_of_mono hKd hpq hxu hyu hzu hx3 hz3 hζ hxy hxz hyz (Or.inr hy3)
        hij hi hj k) hc hcyc
  · push Not at hij
    obtain ⟨rfl, rfl⟩ := hij
    by_cases hk0 : k = 0
    · subst hk0
      have h1 : ∀ l, ψ (a₀ l) = ψ l := fun l => by
        rw [← hc l]
        have e : (⟨x ^ 0 * y ^ 0 * z ^ 0, hM⟩ : Subgroup.normalizer
            (unitarySU 2 n F 6 : Set (GL (Fin 6) F))) = 1 := by
          apply Subtype.ext
          simp
        rw [e, map_one]
        rfl
      exact ha₀1 (TypeA.mulAut_eq_of_forall ψ hker hperf (a := a₀) (b := 1) h1)
    · have hzk : z ^ k ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
        pow_mem hzN k
      have e : (⟨x ^ 0 * y ^ 0 * z ^ k, hM⟩ : Subgroup.normalizer
          (unitarySU 2 n F 6 : Set (GL (Fin 6) F))) = ⟨z ^ k, hzk⟩ := by
        apply Subtype.ext
        simp
      rw [e] at hc
      exact UnitSixThreeKG.not_ggFixCompCyclic_of_shapeBad hKd hpq hψ hker hzk
        (UnitSixThreeKG.shapeBad_of_central_pow hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs hk hk0)
        hc hcyc

theorem center_two_and_frame
    (hKd : UnitaryFieldData 2 n F) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hpq : 3 ∣ 2 ^ n + 1) {K Bs : Subgroup G} (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (unitarySU 2 n F 6))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hz : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z ^ 3 = 1 → z = 1) :
    IsPGroup 2 (Subgroup.center ↥K) ∧
      ∀ (_ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
        (_ : Nat.card Bs ≤ 3 ^ 4) {P : GL (Fin 6) F} (_ : P ∈ primeFormUnitary hKd (idGram F 6)),
        (∀ (b : G) (hb : b ∈ Bs), ∃ (M : GL (Fin 6) F)
          (hM : M ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F))),
          ggLAut K θ ⟨b, hN hb⟩ = TableB.projConj (unitarySU 2 n F 6) ⟨M, hM⟩ ∧
            ((P⁻¹ * M * P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag) →
        ∀ g ∈ Bs, g ∈ K := by
  haveI : Finite F := hKd.finite
  classical
  by_cases hn1 : n = 1
  · subst hn1
    have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
    have hZ2 := isPGroup_two_center (LineU.unitaryCoverOddAt_six_two F hF4) hKd hpq hK θ hz
    exact ⟨hZ2, fun hSC hBcard P hP hdiag =>
      le_of_frame_two hKd hpq θ hZ2 hN hBcard hSC hP hdiag⟩
  · have hn2 : 2 ≤ n := by have := hKd.one_le; omega
    have hcov : UnitaryCoverAt n 6 F :=
      unitaryUniversalCover_holds n 6 F hF (by norm_num) (by
        intro h
        have := congrArg Prod.snd h
        simp only at this
        omega)
    obtain ⟨φ, hφL, hφs, hφZ, hψ, hact⟩ := exists_cover_actsAs hKd hcov hK θ hN hBI
    have hZ1 : ∀ z : ↥K, z ∈ Subgroup.center ↥K → z = 1 := by
      intro z hz'
      obtain ⟨s, hs⟩ := hφs z z.2
      have hcomm : ∀ l ∈ K, φ s * l = l * φ s := by
        intro l hl
        rw [hs]
        have := Subgroup.mem_center_iff.mp hz' ⟨l, hl⟩
        exact congrArg Subtype.val this.symm
      obtain ⟨c, hc3, hc⟩ := exists_scalar_of_proj_eq_one hKd hpq ((hφZ s).mp hcomm)
      have hφ3 : (φ s) ^ 3 = 1 := by
        rw [← map_pow]
        have : s ^ 3 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
          rfl
        rw [this, map_one]
      have := hz (φ s) (hφL s) hcomm hφ3
      exact Subtype.ext (by rw [← hs]; exact this)
    refine ⟨fun z => ⟨0, by
      have := hZ1 z z.2
      exact Subtype.ext (by simpa using congrArg Subtype.val this)⟩, ?_⟩
    intro hSC hBcard P hP hdiag g hg
    have hker : ∀ s, φ s = 1 → LargeEvenProjMk (unitarySU 2 n F 6) s = 1 := fun s hs =>
      (hφZ s).mp fun l _ => by rw [hs, one_mul, mul_one]
    have hN' := TableBUE.gu_subset_normalizer (d := 6) hKd
    obtain ⟨s, hs⟩ := le_range_of_frame hKd hpq φ hker hBcard hSC hP (fun b hb => by
      obtain ⟨M, hMgu, hMact⟩ := hact b hb
      obtain ⟨M₀, hM₀N, hM₀eq, hM₀d⟩ := hdiag b hb
      have hρ : TableB.projConj (unitarySU 2 n F 6) ⟨M, hN' hMgu⟩ =
          TableB.projConj (unitarySU 2 n F 6) ⟨M₀, hM₀N⟩ := by
        rw [← ggLAut_eq_projConj_of_actsAs θ hφL hψ (hN hb) hMact (hN' hMgu), hM₀eq]
      obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq hKd hF hpq (hN' hMgu) hM₀N hρ
      refine ⟨M, hMact, ?_⟩
      rw [hc]
      exact isDiag_conj_mul_scalar c hM₀d) g hg
    rw [← hs]
    exact hφL s

theorem nbrU63_stepTwo
    (hL : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hpJ : 3 ∣ Nat.card J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hM : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K)
    (hlt : Nat.card (ggGamma K hN).range < 3 ^ 4)
    (hz : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z ^ 3 = 1 → z = 1) : False := by
  classical
  obtain ⟨hK, n, F, _, _, hF, hn, hpq, θ, -, hBI⟩ :=
    config_marking_data (innerDiagOnLab_of_label hM)
  have hKd : UnitaryFieldData 2 n F := CFSG.StandardType.TableBU.unitaryFieldData_of_card hF hn
  obtain ⟨-, hrank, hA27⟩ := card_rank_of_lt hcfg hnb hN hlt
  obtain ⟨-, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSHat 3 B y K := hnb.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hS.2.1
  have hy1 : y ≠ 1 := hS.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hyC : ∀ k ∈ K, y * k = k * y := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)).symm
  have hyK : y ∉ K := fun h => hy1 (hz y h hyC hy3)
  obtain ⟨hZ2, hframe⟩ := center_two_and_frame hKd hF hpq hK θ hN hBI hz
  have hinner := all_inner_of_rank hKd hpq hK θ hZ2 hN hBI hBs hrank hyBs hy1 hyC hyK
  have hBs81 := card_le_of_center_two hKd hpq θ hZ2 hN hBs hrank hA27
  have hN' := TableBUE.gu_subset_normalizer (d := 6) hKd
  set Ab := (ggBeta K θ hN).range with hAb
  have hAbab : CFSG.Open.IsElemAbelian 3 Ab := isElemAbelian_range_ggBeta θ hBs hN
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, card_range_ggBeta_eq hK θ hN, hA27]
    norm_num
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)) := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem K θ hN hBI b
  by_cases hfr : ∃ P ∈ primeFormUnitary hKd (idGram F 6), ∀ a ∈ Ab, ∃ (M : GL (Fin 6) F)
      (hM : M ∈ LargeEvenGUSet (Fin 6) F (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n F 6) ⟨M, hN' hM⟩
  ·
    obtain ⟨P, hP, hPd⟩ := hfr
    exact hyK (hframe hSC hBs81 hP (fun b hb => by
      obtain ⟨M₀, hM₀gu, hM₀d, hM₀eq⟩ := hPd (ggBeta K θ hN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
      exact ⟨M₀, hN' hM₀gu, by rw [← ggBeta_eq K θ hN ⟨b, hb⟩]; exact hM₀eq, hM₀d⟩) y hyBs)
  · rcases TableBU63.fieldType_or_heis hKd hF hpq hAbab hAbI (by rw [hAb27]; norm_num) hfr with
      ⟨M, hMN, l, -, hM3, hl, hMA⟩ | hheis
    ·
      obtain ⟨⟨b, hb⟩, hbeq⟩ := hMA
      obtain ⟨M', hM'gu, hM'in, hM'eq⟩ := hinner b hb
      have hρ : TableB.projConj (unitarySU 2 n F 6) ⟨M, hMN⟩ =
          TableB.projConj (unitarySU 2 n F 6) ⟨M', hN' hM'gu⟩ := by
        rw [← hM'eq, ← ggBeta_eq K θ hN ⟨b, hb⟩]
        exact hbeq.symm
      obtain ⟨c, hc⟩ := exists_scalar_of_projConj_eq hKd hF hpq hMN (hN' hM'gu) hρ
      have hMin : IsInner n M := by
        rw [hc, ← (TypeA.PGLTor.commute_scalar c M').eq]
        exact (isInner_scalar_mul_iff c M').mpr hM'in
      exact not_isInner_of_pow_three_eq_scalar hKd hM3 hl hMin
    ·
      obtain ⟨x', y', z', hx'N, hy'N, hz'N, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3m, hz3, hζ3, hζ1,
        hxy, hxz, hyz, hzs⟩ := hheis
      have hyA' := hyA
      obtain ⟨⟨b, hb⟩, hbeq⟩ := hyA
      obtain ⟨M', hM'gu, hM'in, hM'eq⟩ := hinner b hb
      have hρ : TableB.projConj (unitarySU 2 n F 6) ⟨y', hy'N⟩ =
          TableB.projConj (unitarySU 2 n F 6) ⟨M', hN' hM'gu⟩ := by
        rw [← hM'eq, ← ggBeta_eq K θ hN ⟨b, hb⟩]
        exact hbeq.symm
      obtain ⟨c₀, hc₀⟩ := exists_scalar_of_projConj_eq hKd hF hpq hy'N (hN' hM'gu) hρ
      have hy'in : IsInner n y' := by
        rw [hc₀, ← (TypeA.PGLTor.commute_scalar c₀ M').eq]
        exact (isInner_scalar_mul_iff c₀ M').mpr hM'in
      have hy'cube : ∃ w : Fˣ, y' ^ 3 = GeneralLinearGroup.scalar (Fin 6) w := by
        have hmem : y' ^ 3 ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
          Subgroup.pow_mem _ hy'N 3
        have hρ3 : TableB.projConj (unitarySU 2 n F 6) ⟨y' ^ 3, hmem⟩ =
            TableB.projConj (unitarySU 2 n F 6) ⟨1, Subgroup.one_mem _⟩ := by
          have h1 : (⟨y' ^ 3, hmem⟩ : ↥(Subgroup.normalizer
              (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))) = ⟨y', hy'N⟩ ^ 3 := rfl
          have h2 : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer
              (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))) = 1 := rfl
          rw [h1, h2, map_pow, map_one]
          exact hAbab.2 _ hyA'
        obtain ⟨w, hw⟩ := exists_scalar_of_projConj_eq hKd hF hpq hmem (Subgroup.one_mem _) hρ3
        exact ⟨w, by rw [hw, one_mul]⟩
      obtain ⟨w, hw⟩ := hy'cube
      obtain ⟨c, hc⟩ := exists_pow_three_eq_one_of_isInner hKd hpq hy'in hw
      have hsN : GeneralLinearGroup.scalar (Fin 6) c ∈
          Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
        TableB.scalar_mem_normalizer _ ⟨c, rfl⟩
      have hy''N : GeneralLinearGroup.scalar (Fin 6) c * y' ∈
          Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) := mul_mem hsN hy'N
      have hy''u : GeneralLinearGroup.scalar (Fin 6) c * y' ∈
          primeFormUnitary hKd (idGram F 6) :=
        TableBUD.mem_primeFormUnitary_of_pow_eq_one hKd hpq (by norm_num)
          (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hyu) (c := (c : F))
          (by rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
            TableBUD.scalar_mul_eq_smul]) hc
      have hy''A : TableB.projConj (unitarySU 2 n F 6) ⟨GeneralLinearGroup.scalar (Fin 6) c * y',
          hy''N⟩ ∈ Ab := by
        have : (⟨GeneralLinearGroup.scalar (Fin 6) c * y', hy''N⟩ :
            ↥(Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)))) =
            ⟨GeneralLinearGroup.scalar (Fin 6) c, hsN⟩ * ⟨y', hy'N⟩ := rfl
        rw [this, map_mul, TableB.projConj_of_scalar _ ⟨c, rfl⟩, one_mul]
        exact hyA'
      have hxy' : x' * (GeneralLinearGroup.scalar (Fin 6) c * y') =
          GeneralLinearGroup.scalar (Fin 6) ζ *
            ((GeneralLinearGroup.scalar (Fin 6) c * y') * x') := by
        calc x' * (GeneralLinearGroup.scalar (Fin 6) c * y')
            = GeneralLinearGroup.scalar (Fin 6) c * (x' * y') := by
              rw [← mul_assoc, ← mul_assoc, (TypeA.PGLTor.commute_scalar c x').eq.symm]
          _ = GeneralLinearGroup.scalar (Fin 6) c *
                (GeneralLinearGroup.scalar (Fin 6) ζ * (y' * x')) := by rw [hxy]
          _ = (GeneralLinearGroup.scalar (Fin 6) c * GeneralLinearGroup.scalar (Fin 6) ζ) *
                (y' * x') := by rw [mul_assoc]
          _ = (GeneralLinearGroup.scalar (Fin 6) ζ * GeneralLinearGroup.scalar (Fin 6) c) *
                (y' * x') := by
              rw [(TypeA.PGLTor.commute_scalar c (GeneralLinearGroup.scalar (Fin 6) ζ)).eq]
          _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                ((GeneralLinearGroup.scalar (Fin 6) c * y') * x') := by
              rw [mul_assoc, mul_assoc]
      have hy''z : (GeneralLinearGroup.scalar (Fin 6) c * y') * z' =
          z' * (GeneralLinearGroup.scalar (Fin 6) c * y') := by
        rw [mul_assoc, hyz, ← mul_assoc, ← mul_assoc, (TypeA.PGLTor.commute_scalar c z').eq]
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hζ : IsPrimitiveRoot ζ 3 := by
        have := IsPrimitiveRoot.orderOf ζ
        rwa [orderOf_eq_prime hζ3 hζ1] at this
      have hAI : ∀ a ∈ (ggGamma K hN).range, ∃ x ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (unitarySU 2 n F 6)) (LargeEvenGUSet (Fin 6) F (2 ^ n)),
          ∀ l : ↥K, x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
        rintro _ ⟨b, rfl⟩
        exact ⟨ggBeta K θ hN b, ggBeta_mem K θ hN hBI b, fun l => ggBeta_ggQuotHom K hN θ b l⟩
      have hAbA : ∀ a ∈ Ab, a ∈ TypeA.inducedSub (ggQuotHom θ) (ggGamma K hN).range := by
        rintro _ ⟨b, rfl⟩
        exact TypeA.mem_inducedSub.mpr
          ⟨ggGamma K hN b, ⟨b, rfl⟩, fun l => ggBeta_ggQuotHom K hN θ b l⟩
      have hx1 : ggGamma K hN ⟨x, hxBs⟩ ≠ 1 := by
        intro h
        rw [ggGamma_eq_one_iff] at h
        refine hnb.2.2.2 (le_trans ?_ bot_le)
        rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact Commute.zpow_left (Subgroup.mem_centralizer_iff.mp h k hk).symm m
      exact not_ggFixCompCyclic_of_heisTriple hKd hpq (ggQuotHom_surjective θ)
        (by rw [ker_ggQuotHom]) hK hAI (by rw [hA27]; norm_num) hx'N hy''N hz'N hxu hy''u hzu
        hx3m hc hz3 hζ hxy' hxz hy''z hzs (hAbA _ hxA) (hAbA _ hy''A) (hAbA _ hzA) _
        ⟨⟨x, hxBs⟩, rfl⟩ hx1 (ggFixCompCyclic_ggGamma_x hL hcfg hpJ hnb hN hxBs)

end CFSG.StandardType.NbrU63

end
