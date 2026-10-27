module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail24Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] noncomputable def KS1624Para : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (m' : ℕ), 1 ≤ m' →
    Nonempty (↥L ≃* projSL 3 (GaloisField 2 m')) →
    ∀ (b : G) (m p : ℕ) (P V X : Subgroup G), p.Prime → 3 < p → Data1623 L b m p P V X →
      IsShort (kPara1623 L V) ∧ IsTypeScriptL (kPara1623 L V) ∧
      (∀ N : Subgroup G, N ≤ kPara1623 L V →
        kPara1623 L V ≤ Subgroup.normalizer (N : Set G) → X ≤ N → N = kPara1623 L V) ∧
      (∀ R : Subgroup G, R ≤ L → IsPGroup 2 R →
        kPara1623 L V ≤ Subgroup.normalizer (R : Set G) → R ≤ V) ∧
      (∀ Y : Subgroup G, kPara1623 L V ≤ Y → Y ≤ L → Y ≠ L →
        inSubgroup perfectResidual Y = kPara1623 L V)

@[expose] noncomputable def Step1624KDThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ (m : ℕ) (V X : Subgroup G), Data1623 L b m p P V X →
      ∀ M : Subgroup G, CFSG.IsMaximalTwoLocal M → kPara1623 L V ≤ M → c ∈ M →
        (∀ S : Sylow 3 ↥(normalClosureSub M (Subgroup.zpowers c)),
          IsCyclic ↥(S : Subgroup ↥(normalClosureSub M (Subgroup.zpowers c)))) →
        ⁅kPara1623 L V, normalClosureSub M (Subgroup.zpowers c)⁆ ≤
          pPrimeCoreOf 3 (normalClosureSub M (Subgroup.zpowers c))

@[expose] noncomputable def Step1624KDTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (n p : ℕ) (P : Subgroup G), Data1619 A c L b n p P →
      ∀ (m : ℕ) (V X : Subgroup G), Data1623 L b m p P V X →
      (∀ d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b, d ∉ Subgroup.zpowers c →
        ∀ U : Subgroup G, U ≤ Subgroup.centralizer ({d} : Set G) → IsPGroup 2 U → U ≠ ⊥ →
          U ≠ ⁅U, X⁆) →
      ∀ M : Subgroup G, CFSG.IsMaximalTwoLocal M → kPara1623 L V ≤ M → c ∈ M →
        CFSG.Open.pCoreOf 2 M ≤ Subgroup.normalizer (kPara1623 L V : Set G) →
        ⁅kPara1623 L V, normalClosureSub M (Subgroup.zpowers c)⁆ ≤
            pPrimeCoreOf 3 (normalClosureSub M (Subgroup.zpowers c)) →
          ⁅kPara1623 L V, normalClosureSub M (Subgroup.zpowers c)⁆ ≤ CFSG.Open.pCoreOf 2 M

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Proof1624

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.GH74.GLS CFSG.QuasithinUnique
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem rank3II_16_24_of {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {b : G} {n p : ℕ}
    {P : Subgroup G} (hD : Data1619 A c L b n p P) {m : ℕ} {V X : Subgroup G}
    (hVX : Data1623 L b m p P V X) (h1622 : Step1622) (h316 : Sec19.Item316)
    (h1623 : Step1623) (hPara : KS1624Para) (hKD3 : Step1624KDThree)
    (hKD2 : Step1624KDTwo) :
    ∃ d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b, d ∉ Subgroup.zpowers c ∧
      ∃ U : Subgroup G, U ≤ Subgroup.centralizer ({d} : Set G) ∧ IsPGroup 2 U ∧
        U ≠ ⊥ ∧ U = ⁅U, X⁆ := by
  by_contra hcon
  have hneg : ∀ d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b, d ∉ Subgroup.zpowers c →
      ∀ U : Subgroup G, U ≤ Subgroup.centralizer ({d} : Set G) → IsPGroup 2 U → U ≠ ⊥ →
        U ≠ ⁅U, X⁆ :=
    fun d hd hdc U hU hU2 hU1 hUX => hcon ⟨d, hd, hdc, U, hU, hU2, hU1, hUX⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hD.prime⟩
  have hp3 : 3 < p := hD.three_lt
  set K := kPara1623 L V with hK
  obtain ⟨m', hm', ⟨φL⟩⟩ := h1623 G A c L h
  obtain ⟨hshort, htype, hgen, hR2, hover⟩ :=
    hPara G L m' hm' ⟨φL⟩ b m p P V X hD.prime hp3 hVX
  have hLsimp : IsSimpleGroup ↥L := by
    have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 m')
    exact φL.isSimpleGroup
  have h3L : 3 ∣ Nat.card L := (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi
    hD.isZ3.1 hD.isZ3.2.1).trans (Subgroup.card_quotient_dvd_card _)
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Sec17.Sec15R.centralizer_le_normalizer_L h.toSec15R h3L
  have hHL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L
  have hKL : K ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXK : X ≤ K := hVX.le_K
  have hXL : X ≤ L := hXK.trans hKL
  have hVK : V ≤ K := hVX.le_V
  have hVL : V ≤ L := hVX.le_L
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := by
    obtain ⟨hn, -⟩ := hVX.quot
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).mp hn
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.le_centralizer
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKL.trans hLc
  have hXc : X ≤ Subgroup.centralizer ({c} : Set G) := hXL.trans hLc
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) :=
    hVX.le_P.trans (hD.mem_Q.1.2.trans inf_le_right)
  have hbK : b ∈ K := hVX.mem_K
  have hXp : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [hVX.card_X, pow_one])
  have hKperf : Group.IsPerfect K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have : IsCyclic ↥X := isCyclic_of_prime_card hVX.card_X
  obtain ⟨⟨x, hxX⟩, hgx⟩ := IsCyclic.exists_generator (α := ↥X)
  have hXx : X = Subgroup.zpowers x := by
    refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hxX)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgx ⟨y, hy⟩)
    have hk' : x ^ k = y := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩
  set E := Subgroup.zpowers c ⊔ Subgroup.zpowers b with hE
  have hEA : E ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr hD.mem_A)
  have hEel : CFSG.Assembly.IsElemAbelian 3 E :=
    Proof169.isElemAbelian_of_le h.isElemAbelian hEA
  have hE9 : 9 ≤ Nat.card E := by
    refine Proof169.nine_le_card_of_lt hEA h.card_eq h.card_zpowers
      (lt_of_le_of_ne le_sup_left fun heq => hD.not_mem ?_)
    rw [heq]
    exact (le_sup_right : Subgroup.zpowers b ≤ E) (Subgroup.mem_zpowers b)
  have hXd : ∀ d ∈ E, X ≤ Subgroup.centralizer ({d} : Set G) := fun d hd =>
    (le_inf hXc hXb).trans (Proof169.inf_centralizer_le_of_mem_sup hd)
  set Q₀ := CFSG.Open.pCoreOf 2 K with hQ₀
  have hQ₀1 : Q₀ ≠ ⊥ := by
    intro hbot
    have h1 := hshort.blockZ_lt_blockU
    have hU : blockU K = ⊥ := by
      change ⁅CFSG.Open.pCoreOf 2 K, K⁆ = ⊥
      rw [← hQ₀, hbot, Subgroup.commutator_bot_left]
    rw [hU] at h1
    exact not_lt_bot h1
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hKQ₀ : K ≤ Subgroup.normalizer (Q₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hcQ₀ : c ∈ Subgroup.normalizer (Q₀ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hKc (CFSG.LieType.BorelTits.pCoreOf_le 2 K hy))
  have hloc : CFSG.IsPLocal 2 (Subgroup.normalizer (Q₀ : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hQ₀2 hQ₀1
  obtain ⟨M, hNM, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hKM : K ≤ M := hKQ₀.trans hNM
  have hcM : c ∈ M := hNM hcQ₀
  have hMtop : M ≠ ⊤ := by
    obtain ⟨R, hR1, hR2', hMR⟩ := hM.1
    rw [hMR]
    exact Sec14.normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hR1 hR2'
  set O₂ := CFSG.Open.pCoreOf 2 M with hO₂
  have hO₂M : O₂ ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hO₂2 : IsPGroup 2 O₂ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
  have hMO₂ : M ≤ Subgroup.normalizer (O₂ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  set Q := ⁅O₂, X⁆ with hQ
  have hXO₂ : X ≤ Subgroup.normalizer (O₂ : Set G) := hXK.trans (hKM.trans hMO₂)
  have hQO₂ : Q ≤ O₂ := Subgroup.le_normalizer_iff_commutator_le_left.mp hXO₂
  have hQ2 : IsPGroup 2 Q := hO₂2.to_le hQO₂
  have hO₂p : ¬ p ∣ Nat.card O₂ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO₂2
    rw [hk]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) (hD.prime.dvd_of_dvd_pow hdvd)
    omega
  have hQQX : ⁅Q, X⁆ = Q :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hD.prime X O₂
      hXp hO₂p hXO₂
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := Subgroup.normalizer_commutator_ge_right O₂ X
  have hnormQ : ∀ g : G, g ∈ Subgroup.normalizer (O₂ : Set G) →
      g ∈ Subgroup.normalizer (X : Set G) → g ∈ Subgroup.normalizer (Q : Set G) := by
    intro g hgO hgX
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hQ, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgO,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgX]
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr (hnormQ c (hMO₂ hcM) ?_))
      (Subgroup.zpowers_le.mpr (hnormQ b (hMO₂ (hKM hbK)) ?_))
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hXc hy))
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hXb hy))
  have hcent : ∀ d ∈ E, d ∉ Subgroup.zpowers c →
      Q ⊓ Subgroup.centralizer ({d} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro d hd hdc
    set Qd := Q ⊓ Subgroup.centralizer ({d} : Set G) with hQd
    have hXQd : X ≤ Subgroup.normalizer (Qd : Set G) :=
      Proof169.le_normalizer_inf hXQ ((hXd d hd).trans Subgroup.le_normalizer)
    have hQdp : ¬ p ∣ Nat.card Qd := fun hdvd =>
      hO₂p (hdvd.trans (Subgroup.card_dvd_of_le (inf_le_left.trans hQO₂)))
    set U := ⁅Qd, X⁆ with hUdef
    have hUQd : U ≤ Qd := Subgroup.le_normalizer_iff_commutator_le_left.mp hXQd
    have hUU : ⁅U, X⁆ = U :=
      CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hD.prime X Qd
        hXp hQdp hXQd
    have hU : U = ⊥ := by
      by_contra hU1
      exact hneg d hd hdc U (hUQd.trans inf_le_right) (hQ2.to_le (hUQd.trans inf_le_left)) hU1
        hUU.symm
    have hQdX : Qd ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU
    exact hQdX.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxX))
  have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hXQ hxX
  have hQQx : Q = ⁅Q, Subgroup.zpowers x⁆ := by rw [← hXx, hQQX]
  have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_coprime hQ2 hxQ hQQx hEel hE9 hEQ h.card_zpowers hcent
  have hQL : Q ≤ L := by
    rw [← hQQX, Subgroup.commutator_le]
    intro q hq y hy
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hCL (hQc hq)) y).mp (hXL hy))
      (inv_mem (hXL hy))
  have hO₂L : L ⊓ O₂ ≤ V := hR2 (L ⊓ O₂) inf_le_left (hO₂2.to_le inf_le_right)
    (Proof169.le_normalizer_inf (hKL.trans Subgroup.le_normalizer) (hKM.trans hMO₂))
  have hQV : Q ≤ V := (le_inf hQL hQO₂).trans hO₂L
  have hO₂K : O₂ ≤ Subgroup.normalizer (K : Set G) := by
    let N : Subgroup G :=
      { carrier := {k | k ∈ K ∧ ∀ t ∈ O₂, t * k * t⁻¹ * k⁻¹ ∈ V}
        one_mem' := ⟨one_mem K, fun t _ => by simp⟩
        mul_mem' := by
          rintro k₁ k₂ ⟨hk₁, h₁⟩ ⟨hk₂, h₂⟩
          refine ⟨mul_mem hk₁ hk₂, fun t ht => ?_⟩
          have hv := (Subgroup.mem_normalizer_iff.mp (hKV hk₁) _).mp (h₂ t ht)
          have heq : t * (k₁ * k₂) * t⁻¹ * (k₁ * k₂)⁻¹ =
              (t * k₁ * t⁻¹ * k₁⁻¹) * (k₁ * (t * k₂ * t⁻¹ * k₂⁻¹) * k₁⁻¹) := by group
          rw [heq]
          exact mul_mem (h₁ t ht) hv
        inv_mem' := by
          rintro k ⟨hk, h₁⟩
          refine ⟨inv_mem hk, fun t ht => ?_⟩
          have hv := (Subgroup.mem_normalizer_iff.mp (hKV (inv_mem hk)) _).mp
            (inv_mem (h₁ t ht))
          have heq : t * k⁻¹ * t⁻¹ * k⁻¹⁻¹ = k⁻¹ * (t * k * t⁻¹ * k⁻¹)⁻¹ * k⁻¹⁻¹ := by group
          rw [heq]
          exact hv }
    have hNK : N ≤ K := fun k hk => hk.1
    have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
      intro g hg
      refine Subgroup.mem_normalizer_fintype fun k hk => ⟨?_, fun t ht => ?_⟩
      · exact mul_mem (mul_mem hg hk.1) (inv_mem hg)
      · have ht' : g⁻¹ * t * g ∈ O₂ := by
          have := (Subgroup.mem_normalizer_iff.mp (hKM.trans hMO₂ (inv_mem hg)) t).mp ht
          simpa using this
        have hv := (Subgroup.mem_normalizer_iff.mp (hKV hg) _).mp (hk.2 _ ht')
        have heq : t * (g * k * g⁻¹) * t⁻¹ * (g * k * g⁻¹)⁻¹ =
            g * ((g⁻¹ * t * g) * k * (g⁻¹ * t * g)⁻¹ * k⁻¹) * g⁻¹ := by group
        rw [heq]
        exact hv
    have hXN : X ≤ N := by
      intro y hy
      refine ⟨hXK hy, fun t ht => hQV ?_⟩
      have := Subgroup.commutator_mem_commutator ht hy
      rwa [commutatorElement_def] at this
    have hNeq := hgen N hNK hKN hXN
    intro t ht
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have hkN : k ∈ N := hNeq ▸ hk
    have heq : t * k * t⁻¹ = (t * k * t⁻¹ * k⁻¹) * k := by group
    rw [heq]
    exact mul_mem (hVK (hkN.2 t ht)) hk
  set D := normalClosureSub M (Subgroup.zpowers c) with hDdef
  have hcyc := h1622 G A c L h M hcM hMtop
  have hKD3' := hKD3 G A c L h b n p P hD m V X hVX M hM hKM hcM hcyc
  have hKDO := hKD2 G A c L h b n p P hD m V X hVX hneg M hM hKM hcM hO₂K hKD3'
  obtain ⟨hcD', hDM, hMD⟩ := Proof169.normalClosureSub_spec (Subgroup.zpowers_le.mpr hcM)
  have hcD : c ∈ D := hcD' (Subgroup.mem_zpowers c)
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
    intro d hd
    have hle : K.map (MulAut.conj d).toMonoidHom ≤ K ⊔ O₂ := by
      rintro _ ⟨k, hk, rfl⟩
      have hw : ⁅k⁻¹, d⁆ ∈ O₂ := hKDO (Subgroup.commutator_mem_commutator (inv_mem hk) hd)
      have heq : (MulAut.conj d).toMonoidHom k = k * ⁅k⁻¹, d⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [heq]
      exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hw)
    have hperf : Group.IsPerfect (K.map (MulAut.conj d).toMonoidHom) :=
      Group.IsPerfect.map _
    have h1 := le_of_isPerfect_of_le_sup hO₂K hO₂2 hperf hle
    exact Subgroup.mem_normalizer_fintype fun k hk => h1 ⟨k, hk, rfl⟩
  have hLM : ¬ L ≤ M := by
    intro hLM
    have h1 : Q ≤ O₂ ⊓ L := le_inf hQO₂ (hQV.trans hVL)
    have hn : ((O₂ ⊓ L).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        (Proof169.le_normalizer_inf (hLM.trans hMO₂) Subgroup.le_normalizer)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O₂ ⊓ L).subgroupOf L) with hbot | htop
    · have hOL : O₂ ⊓ L = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hy' : (⟨y, hy.2⟩ : L) ∈ (O₂ ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
        rw [hbot, Subgroup.mem_bot] at hy'
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy')
      have hQ1 : ⁅X, O₂⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact le_bot_iff.mp (hOL ▸ h1)
      have hXC : X ≤ Subgroup.centralizer (O₂ : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQ1
      have hXO : X ≤ O₂ := fun y hy => h.charTwoType M hM.1 ⟨hKM (hXK hy), hXC hy⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hO₂2.to_le hXO)
      rw [hVX.card_X] at hk
      have hpd : p ∣ 2 ^ k := by rw [← hk]
      have := Nat.le_of_dvd (by norm_num) (hD.prime.dvd_of_dvd_pow hpd)
      omega
    · have hLO : L ≤ O₂ := by
        intro y hy
        have hy' : (⟨y, hy⟩ : L) ∈ (O₂ ⊓ L).subgroupOf L := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy')).1
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hO₂2.to_le hLO)
      rw [hk] at h3L
      have := Nat.prime_three.dvd_of_dvd_pow h3L
      omega
  have hLMne : L ⊓ M ≠ L := fun heq => hLM (heq ▸ inf_le_right)
  have hKres := hover (L ⊓ M) (le_inf hKL hKM) inf_le_left hLMne
  have hHK : M ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    rintro g ⟨hgM, hgH⟩
    have hg : g ∈ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) :=
      Proof169.le_normalizer_inf (Subgroup.zpowers_le.mpr (hHL hgH))
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hgM)) (Subgroup.mem_zpowers g)
    have h2 : g ∈ Subgroup.normalizer
        ((inSubgroup perfectResidual (L ⊓ M) : Subgroup G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains (L ⊓ M) hg
    rwa [hKres] at h2
  have hMK : M ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_frattini hcD hDM hMD h.orderOf_eq hcyc hDK hHK
  have hblock : IsScriptLBlock M K := by
    refine ⟨⟨hshort, hKM, ?_⟩, htype⟩
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK).isSubnormal
  exact h.not_inCatalog
    (h316 G h.isSimpleGroup h.nonabelian h.kProper h.charTwoType h.evenRank_eq M K hM hblock)

end CFSG.RankThree.PartTwo.Sec16.Proof1624

namespace CFSG.RankThree.PartTwo.Sec16

theorem step1624_of (h1622 : Step1622) (h316 : Sec19.Item316) (h1623 : Step1623)
    (hPara : KS1624Para) (hKD3 : Step1624KDThree) (hKD2 : Step1624KDTwo) : Step1624 :=
  fun _ _ _ _ _ _ h _ _ _ _ hD _ _ _ hVX =>
    Proof1624.rank3II_16_24_of h hD hVX h1622 h316 h1623 hPara hKD3 hKD2

end CFSG.RankThree.PartTwo.Sec16
