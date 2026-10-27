module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofQL
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofLA7
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def KS163U35NoIndex25 : Prop :=
  ∀ (_ : Fact (Nat.Prime 5)) (H : Subgroup ↥(projSU 3 5 1)), Nat.card H ≠ 5040

@[expose] def KS163U35CentA7 : Prop :=
  ∀ (_ : Fact (Nat.Prime 5)) (K : Subgroup ↥(projSU 3 5 1)),
    Nonempty (↥K ≃* alternatingGroup (Fin 7)) →
      ∀ σ : MulAut ↥(projSU 3 5 1), (∀ k ∈ K, σ k = k) → σ = 1

@[expose] def KS163U35Fusion : Prop :=
  ∀ (_ : Fact (Nat.Prime 5)) (E : Subgroup ↥(projSU 3 5 1)), Nat.card E = 9 →
    ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 →
      ∃ u ∈ Subgroup.normalizer (E : Set ↥(projSU 3 5 1)), u * x * u⁻¹ = y

namespace Res163

section A7

open CFSG.RankThree.PartTwo.KFacts.KP2 Equiv

theorem pow_three_of_even_centralizer_cOne_cTwo : ∀ (i j : Fin 3) (b : Bool),
    Perm.sign (eNineF i j * (if b then tauOne else 1)) = 1 →
      (eNineF i j * (if b then tauOne else 1)) ^ 3 = 1 := by
  decide +kernel

theorem exists_pair_alt7 (E : Subgroup (alternatingGroup (Fin 7))) (hE9 : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧
      (∃ S : Subgroup (alternatingGroup (Fin 7)), S ≠ ⊥ ∧ IsPGroup 2 S ∧
        S ≤ Subgroup.centralizer {x} ∧
        E ≤ Subgroup.normalizer (S : Set (alternatingGroup (Fin 7)))) ∧
      ∀ z : alternatingGroup (Fin 7), z * y = y * z → z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hE'9 : Nat.card (eNine.subgroupOf (alternatingGroup (Fin 7))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv,
      card_eNine]
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hE'p : IsPGroup 3 (eNine.subgroupOf (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (n := 2) (by rw [hE'9]; norm_num)
  have hEi : ¬ 3 ∣ E.index := by
    have h := E.index_mul_card
    rw [hE9, hcard] at h
    omega
  have hE'i : ¬ 3 ∣ (eNine.subgroupOf (alternatingGroup (Fin 7))).index := by
    have h := (eNine.subgroupOf (alternatingGroup (Fin 7))).index_mul_card
    rw [hE'9, hcard] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hEp.toSylow hEi)
    (hE'p.toSylow hE'i)
  have hiff : ∀ x : alternatingGroup (Fin 7), x ∈ E ↔
      g * x * g⁻¹ ∈ eNine.subgroupOf (alternatingGroup (Fin 7)) := by
    intro x
    have h1 : g * x * g⁻¹ ∈ ((g • hEp.toSylow hEi : Sylow 3 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) ↔ x ∈ E := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
        group
      rw [this, IsPGroup.toSylow_coe]
    rw [← h1, hg, IsPGroup.toSylow_coe]
  let ψ : alternatingGroup (Fin 7) →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (MulAut.conj g).toMonoidHom
  have hψ : ∀ x : alternatingGroup (Fin 7), ψ x = ((g * x * g⁻¹ : alternatingGroup (Fin 7)) :
      Perm (Fin 7)) := fun x => rfl
  have hψinj : Function.Injective ψ :=
    (alternatingGroup (Fin 7)).subtype_injective.comp (MulAut.conj g).injective
  have hrange : ψ.range = alternatingGroup (Fin 7) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hc1 : cOne ∈ alternatingGroup (Fin 7) := eNine_le_alternatingGroup cOne_mem_eNine
  have hc12 : cOne * cTwo ∈ alternatingGroup (Fin 7) :=
    eNine_le_alternatingGroup (eNine.mul_mem cOne_mem_eNine cTwo_mem_eNine)
  set x₁ : alternatingGroup (Fin 7) := ⟨cOne, hc1⟩ with hx₁
  set y₁ : alternatingGroup (Fin 7) := ⟨cOne * cTwo, hc12⟩ with hy₁
  refine ⟨g⁻¹ * x₁ * g, ?_, g⁻¹ * y₁ * g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hiff, show g * (g⁻¹ * x₁ * g) * g⁻¹ = x₁ by group]
    exact cOne_mem_eNine
  · rw [hiff, show g * (g⁻¹ * y₁ * g) * g⁻¹ = y₁ by group]
    exact eNine.mul_mem cOne_mem_eNine cTwo_mem_eNine
  · intro h1
    have h2 : x₁ = 1 := by
      calc x₁ = g * (g⁻¹ * x₁ * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h3 : cOne = 1 := congrArg Subtype.val h2
    exact absurd h3 (by decide +kernel)
  · intro h1
    have h2 : y₁ = 1 := by
      calc y₁ = g * (g⁻¹ * y₁ * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h3 : cOne * cTwo = 1 := congrArg Subtype.val h2
    exact absurd h3 (by decide +kernel)
  ·
    have hV2 : IsPGroup 2 vOne := IsPGroup.of_card (n := 2) (by rw [card_vOne]; norm_num)
    have hvA : vOne ≤ alternatingGroup (Fin 7) := fun v hv => (vOne_le_centOne hv).2
    have hcardS : Nat.card (vOne.comap ψ) = 4 := by
      rw [← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq, hrange,
        inf_eq_right.mpr hvA, card_vOne]
    refine ⟨vOne.comap ψ, fun h0 => ?_, hV2.comap_of_injective ψ hψinj, fun s hs => ?_,
      fun z hz => ?_⟩
    · rw [h0, Subgroup.card_bot] at hcardS
      omega
    ·
      have hs1 : ψ s ∈ centOne := vOne_le_centOne hs
      have hcomm : ψ s * cOne = cOne * ψ s :=
        Subgroup.mem_centralizer_singleton_iff.mp hs1.1
      have hx : ψ (g⁻¹ * x₁ * g) = cOne := by
        rw [hψ, show g * (g⁻¹ * x₁ * g) * g⁻¹ = x₁ by group]
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hψinj
      rw [map_mul ψ s (g⁻¹ * x₁ * g), map_mul ψ (g⁻¹ * x₁ * g) s, hx]
      exact hcomm
    ·
      have hzE : ψ z ∈ eNine := Subgroup.mem_subgroupOf.mp ((hiff z).mp hz)
      exact Subgroup.le_normalizer_comap ψ
        (mem_normalizer_of_le_of_normal_perm_seven vOne_le_centOne vOne_normal
          (eNine_le_centOne hzE))
  ·
    intro z hz
    have hy : ψ (g⁻¹ * y₁ * g) = cOne * cTwo := by
      rw [hψ, show g * (g⁻¹ * y₁ * g) * g⁻¹ = y₁ by group]
    have hcomm : ψ z * (cOne * cTwo) = cOne * cTwo * ψ z := by
      have h1 := congrArg ψ hz
      rw [map_mul ψ z (g⁻¹ * y₁ * g), map_mul ψ (g⁻¹ * y₁ * g) z, hy] at h1
      exact h1
    obtain ⟨i, j, b, hb⟩ :
        ∃ i j : Fin 3, ∃ b : Bool, ψ z = eNineF i j * (if b then tauOne else 1) := by
      by_contra hne
      exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne_cTwo (ψ z)
        ⟨hcomm, hne⟩
    have hsign : Perm.sign (ψ z) = 1 := by
      rw [hψ z]
      exact (g * z * g⁻¹).2
    rw [hb] at hsign
    have h3 := pow_three_of_even_centralizer_cOne_cTwo i j b hsign
    rw [← hb, ← map_pow] at h3
    exact hψinj (by rw [h3, map_one])

end A7

section Group

variable {G : Type} [Group G]

@[expose] def conjAut (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    MulAut ↥L where
  toFun l := ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp l.2⟩
  invFun l := ⟨g⁻¹ * l * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp l.2
    rwa [inv_inv] at h⟩
  left_inv l := Subtype.ext (by simp only; group)
  right_inv l := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjAut_apply (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (l : ↥L) : ((conjAut L hg l : ↥L) : G) = g * l * g⁻¹ :=
  rfl

theorem center_eq_bot_of_isQuasisimple_quot {L : Type*} [Group L] (hs : IsSimpleGroup L)
    (N : Subgroup L) [N.Normal] (hq : IsQuasisimple (L ⧸ N)) : Subgroup.center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a]

theorem nonempty_mulEquiv_of_isSimpleGroup [Finite G] {L : Subgroup G} {X : Type*} [Group X]
    [Nontrivial X] (hL : IsSimpleGroup ↥L) (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* X) :
    Nonempty (↥L ≃* X) := by
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥L).Normal := by
    have := hθ.2.1
    infer_instance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with h | h
  · exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).trans
      φ⟩
  · exfalso
    have : Subsingleton (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton X φ.surjective.subsingleton

end Group

section Finite

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_a7_of_cover {L Y : Subgroup G} (hL : Nat.card L = 126000)
    (h5040 : ∀ H : Subgroup ↥L, Nat.card H ≠ 5040)
    (φY : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))
    (hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y) :
    Nonempty (↥(Y ⊓ L) ≃* alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Y ⊓ L with hKdef
  set P := CFSG.pCore 2 ↥Y with hP
  have hKY : K ≤ Y := inf_le_left
  set f : ↥K →* ↥Y ⧸ P := (QuotientGroup.mk' P).comp (Subgroup.inclusion hKY) with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    have hy : (y : G) ∈ ((K ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := hcov.le y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _
      (hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
    obtain ⟨l, hl, o, ho, hlo⟩ := hy
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp
      (show o ∈ (CFSG.Open.pCore 2 ↥Y).map Y.subtype from ho)
    have ho'P : o' ∈ P := by rwa [hP]
    have hy' : y = Subgroup.inclusion hKY ⟨l, hl⟩ * o' := Subtype.ext hlo.symm
    have h1 : QuotientGroup.mk' P o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'P
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hy', hf, MonoidHom.comp_apply, map_mul, h1, mul_one]
  have hker2 : IsPGroup 2 f.ker := by
    intro x
    have hx : Subgroup.inclusion hKY (x : ↥K) ∈ P := by
      have hx1 : QuotientGroup.mk' P (Subgroup.inclusion hKY (x : ↥K)) = 1 :=
        MonoidHom.mem_ker.mp x.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨_, hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥P => ((z : ↥Y) : G)) hn
    simpa using this
  have hrange : Nat.card f.range = 2520 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr φY.toEquiv,
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  have hK : Nat.card K = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker2
  have hdvd : Nat.card K ∣ 126000 := hL ▸ Subgroup.card_dvd_of_le inf_le_right
  rw [hK, hrange, hn] at hdvd
  have hn1 : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 2520 * 2 ^ 2 ∣ 2520 * 2 ^ n := Nat.mul_dvd_mul_left _ (Nat.pow_dvd_pow 2 hlt)
    have := Nat.dvd_trans h4 hdvd
    norm_num at this
  have hn0 : n = 0 := by
    interval_cases n
    · rfl
    · exfalso
      apply h5040 (K.subgroupOf L)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hK, hrange, hn]
      norm_num
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply Subgroup.eq_bot_of_card_eq
    rw [hn, hn0, pow_zero]
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).trans φY⟩

theorem exists_inner_of_cent {L K : Subgroup G} (hKL : K ≤ L)
    (hK7 : Nonempty (↥K ≃* alternatingGroup (Fin 7)))
    (hcent : ∀ σ : MulAut ↥L, (∀ l : ↥L, (l : G) ∈ K → σ l = l) → σ = 1)
    {a : G} (haL : a ∈ Subgroup.normalizer (L : Set G))
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1) :
    ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨-, -, hinner, -, -⟩ := KFacts.KS14.a7_facts ↥K hK7
  set τ := conjAut K haK with hτ
  have hτ3 : τ ^ 3 = 1 := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, hτ, conjAut_apply,
      conjAut_apply, conjAut_apply]
    calc a * (a * (a * (k : G) * a⁻¹) * a⁻¹) * a⁻¹ = a ^ 3 * (k : G) * (a ^ 3)⁻¹ := by
          simp only [pow_three, mul_inv_rev, mul_assoc]
      _ = k := by rw [ha3]; group
  obtain ⟨x, hx⟩ := hinner τ ⟨1, by rw [pow_one]; exact hτ3⟩
  have hkL : (x : G) ∈ L := hKL x.2
  have hg : (x : G)⁻¹ * a ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hkL)) haL
  have hσ : conjAut L hg = 1 := hcent _ fun l hlK => by
    apply Subtype.ext
    rw [conjAut_apply]
    have h1 : ((τ ⟨l, hlK⟩ : ↥K) : G) = (x : G) * l * (x : G)⁻¹ := by
      rw [hx, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hτ, conjAut_apply] at h1
    calc (x : G)⁻¹ * a * l * ((x : G)⁻¹ * a)⁻¹ = (x : G)⁻¹ * (a * l * a⁻¹) * x := by group
      _ = (x : G)⁻¹ * ((x : G) * l * (x : G)⁻¹) * x := by rw [← h1]
      _ = l := by group
  refine ⟨x, x.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have h1 := congrArg (fun σ' : MulAut ↥L => ((σ' ⟨l, hl⟩ : ↥L) : G)) hσ
  simp only [MulAut.one_apply, conjAut_apply] at h1
  calc l * ((x : G)⁻¹ * a) = ((x : G)⁻¹ * a * l * ((x : G)⁻¹ * a)⁻¹) * ((x : G)⁻¹ * a) := by
        rw [h1]
    _ = (x : G)⁻¹ * a * l := by group

theorem inner_facts {A L K : Subgroup G} {c : G} (h : Sec15R G A c L) (hKL : K ≤ L)
    (hinner : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (L : Set G))
    (hZ : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set G) → z = 1) :
    (∀ a ∈ A, ∃ k ∈ A ⊓ L, k⁻¹ * a ∈ Subgroup.centralizer (L : Set G)) ∧ A ⊓ L ≤ K ∧
      Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hD := h.toSec13Data
  have hcomm : ∀ {g l : G}, g ∈ Subgroup.centralizer (L : Set G) → l ∈ L → g * l = l * g :=
    fun hg hl => (Subgroup.mem_centralizer_iff.mp hg _ hl).symm
  have hkA : ∀ a ∈ A, ∀ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (L : Set G) → k ∈ A := by
    intro a ha k hk hka
    set g := k⁻¹ * a with hg
    have hkL : k ∈ L := hKL hk
    have hag : a = k * g := by rw [hg]; group
    have hkC : A ≤ Subgroup.centralizer ({k} : Set G) := by
      intro b hb
      obtain ⟨k', hk', hk'b⟩ := hinner b hb
      set g' := k'⁻¹ * b with hg'
      have hk'L : k' ∈ L := hKL hk'
      have hbg : b = k' * g' := by rw [hg']; group
      have hab := hD.commute ha hb
      rw [hag, hbg] at hab
      have hz : (k' * k)⁻¹ * (k * k') = g' * g * (g * g')⁻¹ := by
        have e1 : k * g * (k' * g') = k * k' * (g * g') := by
          rw [show k * g * (k' * g') = k * (g * k') * g' by group, hcomm hka hk'L]; group
        have e2 : k' * g' * (k * g) = k' * k * (g' * g) := by
          rw [show k' * g' * (k * g) = k' * (g' * k) * g by group, hcomm hk'b hkL]; group
        rw [e1, e2] at hab
        calc (k' * k)⁻¹ * (k * k') = (k' * k)⁻¹ * (k * k' * (g * g')) * (g * g')⁻¹ := by group
          _ = (k' * k)⁻¹ * (k' * k * (g' * g)) * (g * g')⁻¹ := by rw [hab]
          _ = g' * g * (g * g')⁻¹ := by group
      have hzL : (k' * k)⁻¹ * (k * k') ∈ L :=
        mul_mem (inv_mem (mul_mem hk'L hkL)) (mul_mem hkL hk'L)
      have hzC : g' * g * (g * g')⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
        mul_mem (mul_mem hk'b hka) (inv_mem (mul_mem hka hk'b))
      have h1 := hZ _ hzL (hz ▸ hzC)
      have hkk' : k * k' = k' * k := by
        calc k * k' = (k' * k) * ((k' * k)⁻¹ * (k * k')) := by group
          _ = k' * k := by rw [h1, mul_one]
      rw [Subgroup.mem_centralizer_singleton_iff, hbg]
      calc k' * g' * k = k' * (g' * k) := by group
        _ = k' * (k * g') := by rw [hcomm hk'b hkL]
        _ = k * k' * g' := by rw [← mul_assoc, ← hkk']
        _ = k * (k' * g') := by group
    have hk3 : k ^ 3 = 1 := by
      have ha3 : a ^ 3 = 1 := hD.isElemAbelian.2 a ha
      have hkg : Commute k g := (hcomm hka hkL).symm
      rw [hag, hkg.mul_pow] at ha3
      have h1 : k ^ 3 = (g ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left ha3
      exact hZ _ (pow_mem hkL 3) (h1 ▸ inv_mem (pow_mem hka 3))
    exact mem_of_mem_partTwoF hD.mem_partTwoF hk3 hkC
  have hin : ∀ a ∈ A, ∃ k ∈ A ⊓ L, k⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    obtain ⟨k, hk, hka⟩ := hinner a ha
    exact ⟨k, ⟨hkA a ha k hk hka, hKL hk⟩, hka⟩
  have hTK : A ⊓ L ≤ K := by
    intro t ht
    obtain ⟨k, hk, hkt⟩ := hinner t ht.1
    have h1 := hZ _ (mul_mem (inv_mem (hKL hk)) ht.2) hkt
    have : t = k := by
      calc t = k * (k⁻¹ * t) := by group
        _ = k := by rw [h1, mul_one]
    exact this ▸ hk
  have hAcL : A ≤ Subgroup.zpowers c ⊔ L := by
    intro a ha
    obtain ⟨k, hk, hka⟩ := hin a ha
    have hgA : k⁻¹ * a ∈ A := mul_mem (inv_mem hk.1) ha
    have hgsc : k⁻¹ * a ∈ Late.sectionCentralizer A L
        ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨hgA, fun l hl => ?_⟩
      have : k⁻¹ * a * l * (k⁻¹ * a)⁻¹ * l⁻¹ = 1 := by
        rw [hcomm hka hl]
        group
      rw [this]
      exact one_mem _
    rw [hD.sectionCentralizer_eq] at hgsc
    have hae : a = k * (k⁻¹ * a) := by group
    rw [hae]
    exact mul_mem (Subgroup.mem_sup_right hk.2) (Subgroup.mem_sup_left hgsc)
  have hcL : c ∉ L := fun hc => hD.ne_one (hZ c hc (Subgroup.mem_centralizer_iff.mpr fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)))
  refine ⟨hin, hTK, Proof1511.card_inf_eq_nine_of_le_sup hD.le_normalizer
    (hD.le_normalizer hD.mem_A) hD.card_eq hAcL hD.orderOf_eq hcL hD.mem_A⟩

theorem exists_fusion {L T : Subgroup G} {U : Type*} [Group U] (ψ : ↥L ≃* U)
    (hF : ∀ E : Subgroup U, Nat.card E = 9 → ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 →
      ∃ u ∈ Subgroup.normalizer (E : Set U), u * x * u⁻¹ = y)
    (hTL : T ≤ L) (hT9 : Nat.card T = 9) {x y : G} (hx : x ∈ T) (hy : y ∈ T) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) :
    ∃ w ∈ L, w ∈ Subgroup.normalizer (T : Set G) ∧ w * x * w⁻¹ = y := by
  set E := (T.subgroupOf L).map ψ.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hT9]
  set x' : ↥L := ⟨x, hTL hx⟩ with hx'
  set y' : ↥L := ⟨y, hTL hy⟩ with hy'
  have hx'E : ψ x' ∈ E := ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hy'E : ψ y' ∈ E := ⟨y', Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hne : ∀ {z : ↥L}, (z : G) ≠ 1 → ψ z ≠ 1 := fun hz h1 =>
    hz (congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm)))
  obtain ⟨u, hu, hux⟩ := hF E hE9 _ hx'E _ hy'E (hne hx1) (hne hy1)
  set w : ↥L := ψ.symm u with hw
  have hψw : ψ w = u := ψ.apply_symm_apply u
  refine ⟨(w : G), w.2, Subgroup.mem_normalizer_fintype fun t ht => ?_, ?_⟩
  · have h1 : ψ ⟨t, hTL ht⟩ ∈ E := ⟨⟨t, hTL ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have h2 : u * ψ ⟨t, hTL ht⟩ * u⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hu _).mp h1
    obtain ⟨s, hs, hst⟩ := h2
    have hs' : s = w * ⟨t, hTL ht⟩ * w⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, hψw]
      exact hst
    have hsT : ((w * ⟨t, hTL ht⟩ * w⁻¹ : ↥L) : G) ∈ T := hs' ▸ Subgroup.mem_subgroupOf.mp hs
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe] using hsT
  · have h1 : w * x' * w⁻¹ = y' := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, hψw]
      exact hux
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2

end Finite

end Res163

open Res163

theorem step163U35K_of (hF1 : KS163U35NoIndex25) (hF2 : KS163U35CentA7) (hF3 : KS163U35Fusion) :
    Step163U35K := by
  intro G _ _ A c L h Y hY _ hcase
  obtain ⟨⟨inst5, ⟨φU⟩⟩, ⟨φY⟩, hcov, -, -, hLs, -⟩ := hcase
  have hD := h.toSec13Data
  set U := ↥(projSU 3 5 1) with hUdef
  have hUcard : Nat.card U = 126000 := Proof1515.card_projSU_three_five
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; norm_num)
  have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; norm_num)
  obtain ⟨ψ⟩ := nonempty_mulEquiv_of_isSimpleGroup hLs φU
  have hLcard : Nat.card L = 126000 := by rw [Nat.card_congr ψ.toEquiv, hUcard]
  have h5040 : ∀ H : Subgroup ↥L, Nat.card H ≠ 5040 := fun H hH =>
    hF1 inst5 (H.map ψ.toMonoidHom) (by rw [Subgroup.card_map_of_injective ψ.injective]; exact hH)
  set K := Y ⊓ L with hKdef
  have hKL : K ≤ L := inf_le_right
  obtain ⟨φK⟩ := nonempty_mulEquiv_a7_of_cover hLcard h5040 φY hcov
  have hcent : ∀ σ : MulAut ↥L, (∀ l : ↥L, (l : G) ∈ K → σ l = l) → σ = 1 := by
    intro σ hσ
    set K' := (K.subgroupOf L).map ψ.toMonoidHom with hK'
    have hK'7 : Nonempty (↥K' ≃* alternatingGroup (Fin 7)) :=
      ⟨((Subgroup.equivMapOfInjective _ _ ψ.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hKL)).trans φK⟩
    have h1 := hF2 inst5 K' hK'7 ((ψ.symm.trans σ).trans ψ) (by
      rintro _ ⟨k, hk, rfl⟩
      show ψ (σ (ψ.symm (ψ k))) = ψ k
      rw [MulEquiv.symm_apply_apply, hσ k (Subgroup.mem_subgroupOf.mp hk)])
    refine MulEquiv.ext fun l => ?_
    have h2 := congrArg (fun τ : MulAut U => τ (ψ l)) h1
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    exact ψ.injective h2
  have hZ : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set G) → z = 1 := by
    intro z hzL hzC
    have hc := center_eq_bot_of_isQuasisimple_quot hLs (aschbacherSolvableCore 3 ↥L)
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt)
    have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC l l.2)
    rw [hc, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAY ha, hD.le_normalizer ha⟩
  obtain ⟨hin, hTK, hT9⟩ := inner_facts h hKL (fun a ha => exists_inner_of_cent hKL ⟨φK⟩ hcent
    (hD.le_normalizer ha) (hAK ha) (hD.isElemAbelian.2 a ha)) hZ
  set T := A ⊓ L with hTdef
  set E := (T.subgroupOf K).map φK.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective φK.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hT9]
  obtain ⟨xb, hxE, yb, hyE, hx1, hy1, ⟨S, hS1, hS2, hSC, hES⟩, hexp⟩ := exists_pair_alt7 E hE9
  obtain ⟨t, htT, htx⟩ := hxE
  obtain ⟨t', ht'T, ht'y⟩ := hyE
  set b := (t : G) with hb
  set b' := (t' : G) with hb'
  have hbT : b ∈ T := Subgroup.mem_subgroupOf.mp htT
  have hb'T : b' ∈ T := Subgroup.mem_subgroupOf.mp ht'T
  have hne : ∀ {z : ↥K} {zb : alternatingGroup (Fin 7)}, φK z = zb → zb ≠ 1 → (z : G) ≠ 1 :=
    fun {z} {_} hz hzb h1 => hzb (by rw [← hz, show z = 1 from Subtype.ext h1, map_one])
  have hb1 : b ≠ 1 := hne htx hx1
  have hb'1 : b' ≠ 1 := hne ht'y hy1
  have hkey : ∀ z ∈ K, z * b' = b' * z → ∀ n : ℕ, z ^ 2 ^ n = 1 → z = 1 := by
    intro z hz hzb n hzn
    set z' : ↥K := ⟨z, hz⟩ with hz'
    have hc : φK z' * yb = yb * φK z' := by
      rw [← ht'y]
      change φK.toMonoidHom z' * φK.toMonoidHom t' = φK.toMonoidHom t' * φK.toMonoidHom z'
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hzb)
    have h3 : z' ^ 3 = 1 := φK.injective (by rw [map_pow, hexp _ hc, map_one])
    have h3' : z ^ 3 = 1 := by
      have := congrArg Subtype.val h3
      simpa using this
    exact Step163Alt.eq_one_of_two_three (m := n) (n := 1) hzn (by simpa using h3')
  obtain ⟨w, hwL, hwT, hwb⟩ := exists_fusion ψ (hF3 inst5) inf_le_right hT9 hb'T hbT hb'1 hb1
  have hb'w : b' = w⁻¹ * b * w := by rw [← hwb]; group
  have hcommL : ∀ {g l : G}, g ∈ Subgroup.centralizer (L : Set G) → l ∈ L → g * l = l * g :=
    fun hg hl => (Subgroup.mem_centralizer_iff.mp hg _ hl).symm
  set R := (S.comap φK.toMonoidHom).map K.subtype with hR
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRb : R ≤ Subgroup.centralizer ({b} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : φK k ∈ Subgroup.centralizer {xb} := hSC hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hk' ⊢
    rw [← htx] at hk'
    have h1 : k * t = t * k := φK.injective (by
      change φK.toMonoidHom (k * t) = φK.toMonoidHom (t * k)
      rw [map_mul, map_mul]
      exact hk')
    exact congrArg Subtype.val h1
  have hR2 : IsPGroup 2 R := (hS2.comap_of_injective φK.toMonoidHom φK.injective).map _
  have hRne : R ≠ ⊥ := by
    intro h0
    apply hS1
    rw [hR, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h0
    have := Subgroup.map_comap_eq_self_of_surjective (f := φK.toMonoidHom) φK.surjective S
    rw [h0, Subgroup.map_bot] at this
    exact this.symm
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    obtain ⟨k, hk, hka⟩ := hin a ha
    have hkK : k ∈ K := hTK hk
    have hkN : k ∈ Subgroup.normalizer (R : Set G) := by
      have h1 : (⟨k, hkK⟩ : ↥K) ∈ Subgroup.normalizer ((S.comap φK.toMonoidHom : Subgroup ↥K) :
          Set ↥K) :=
        Subgroup.le_normalizer_comap _ (hES ⟨⟨k, hkK⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩)
      exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype h1)
    have hgN : k⁻¹ * a ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (hRK.trans hKL) hka)
    have hae : a = k * (k⁻¹ * a) := by group
    rw [hae]
    exact mul_mem hkN hgN
  refine ⟨w, ⟨Subgroup.mem_normalizer_fintype fun a ha => ?_, hwL⟩, fun hwK => ?_, b, hbT, hb1,
    ⟨R, ⟨le_inf (hRK.trans le_rfl) hRb, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, hAR⟩,
      hRne⟩, fun R' hR' => ?_⟩
  ·
    obtain ⟨k, hk, hka⟩ := hin a ha
    have hgA : k⁻¹ * a ∈ A := mul_mem (inv_mem hk.1) ha
    have hwk : w * k * w⁻¹ ∈ A := ((Subgroup.mem_normalizer_iff.mp hwT k).mp hk).1
    have he : w * a * w⁻¹ = (w * k * w⁻¹) * (k⁻¹ * a) := by
      calc w * a * w⁻¹ = w * k * (k⁻¹ * a) * w⁻¹ := by group
        _ = w * k * ((k⁻¹ * a) * w⁻¹) := by group
        _ = w * k * (w⁻¹ * (k⁻¹ * a)) := by rw [hcommL hka (inv_mem hwL)]
        _ = (w * k * w⁻¹) * (k⁻¹ * a) := by group
    rw [he]
    exact mul_mem hwk hgA
  ·
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
    obtain ⟨n, hn⟩ := hR2 r
    have hrK : (r : G) ∈ K := hRK r.2
    have hzK : w⁻¹ * r * w⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (inv_mem hwK) r).mp hrK
    have hzb : (w⁻¹ * r * w) * b' = b' * (w⁻¹ * r * w) := by
      rw [hb'w]
      have hrb : (r : G) * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp (hRb r.2)
      calc w⁻¹ * r * w * (w⁻¹ * b * w) = w⁻¹ * (r * b) * w := by group
        _ = w⁻¹ * (b * r) * w := by rw [hrb]
        _ = w⁻¹ * b * w * (w⁻¹ * r * w) := by group
    have hzn : (w⁻¹ * r * w) ^ 2 ^ n = 1 := by
      have hrn : (r : G) ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      rw [show w⁻¹ * (r : G) * w = w⁻¹ * r * w⁻¹⁻¹ by rw [inv_inv], conj_pow, hrn]
      group
    have h1 := hkey _ (by simpa using hzK) hzb n hzn
    apply hr1
    apply Subtype.ext
    calc (r : G) = w * (w⁻¹ * r * w) * w⁻¹ := by group
      _ = 1 := by rw [h1]; group
  ·
    obtain ⟨hR'le, hR'2, -⟩ := hR'
    have hR'p : IsPGroup 2 R' := (isPiSubgroup_piOf_iff Nat.prime_two R').mp hR'2
    refine (Subgroup.eq_bot_iff_forall R').mpr fun r hr => ?_
    obtain ⟨⟨hrY, hrL⟩, hrb⟩ := hR'le hr
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hrY
    have hyr' : y = w⁻¹ * r * w := by
      rw [← hyr]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hyL : y ∈ L := by
      rw [hyr']
      exact mul_mem (mul_mem (inv_mem hwL) hrL) hwL
    have hzb : y * b' = b' * y := by
      rw [hyr', hb'w]
      have hrb' : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp hrb
      calc w⁻¹ * r * w * (w⁻¹ * b * w) = w⁻¹ * (r * b) * w := by group
        _ = w⁻¹ * (b * r) * w := by rw [hrb']
        _ = w⁻¹ * b * w * (w⁻¹ * r * w) := by group
    obtain ⟨n, hn⟩ := hR'p ⟨r, hr⟩
    have hrn : r ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hyn : y ^ 2 ^ n = 1 := by
      rw [hyr', show w⁻¹ * r * w = w⁻¹ * r * w⁻¹⁻¹ by rw [inv_inv], conj_pow, hrn]
      group
    have h1 := hkey y ⟨hy, hyL⟩ hzb n hyn
    calc r = w * (w⁻¹ * r * w) * w⁻¹ := by group
      _ = 1 := by rw [← hyr', h1]; group

end CFSG.RankThree.PartTwo.Sec16
