module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Main148

theorem three_dvd_card_of_isLThreeEpsAt148 {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (h : IsLThreeEpsAt X p f) : 3 ∣ Nat.card X := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ
  · exact KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ

theorem three_dvd_card_of_isoLThreePi148 {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) : 3 ∣ Nat.card X := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ
  · exact KFacts.three_dvd_card_of_mulEquiv_projSU (by omega) φ

theorem three_dvd_card_of_types136 {X : Type} [Group X]
    (hT : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨ IsLThreePi X ∨
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    3 ∣ Nat.card X := by
  rcases hT with ⟨⟨φ⟩⟩ | ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  · exact three_dvd_card_of_isoLThreePi148 he hiso
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num

omit [Finite G] in
theorem card_img148_dvd {A Y : Subgroup G} [(ker148 A Y).Normal] {X : Subgroup G}
    (hX : X ≤ Y ⊔ A) : Nat.card (img148 A Y X) ∣ Nat.card X := by
  have h1 := Subgroup.card_map_dvd (X.subgroupOf (Y ⊔ A)) (QuotientGroup.mk' (ker148 A Y))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv] at h1

omit [Finite G] in
theorem card_sup_dvd_of_le_normalizer148 (N I : Subgroup G)
    (hI : I ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2

omit [Finite G] in
@[expose] def sectionCentralizerSubgroup148 (A X N : Subgroup G)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup G where
  carrier := Late.sectionCentralizer A X N
  mul_mem' := by
    rintro z₁ z₂ ⟨h₁A, h₁⟩ ⟨h₂A, h₂⟩
    refine ⟨A.mul_mem h₁A h₂A, fun y hy => ?_⟩
    have e : z₁ * z₂ * y * (z₁ * z₂)⁻¹ * y⁻¹ =
        z₁ * (z₂ * y * z₂⁻¹ * y⁻¹) * z₁⁻¹ * (z₁ * y * z₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN h₁A) _).mp (h₂ y hy)) (h₁ y hy)
  one_mem' := ⟨A.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro z ⟨hzA, hz⟩
    refine ⟨A.inv_mem hzA, fun y hy => ?_⟩
    have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hAX (A.inv_mem hzA)) y).mp hy
    have h1 := N.inv_mem (hz _ hy')
    have e : (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ = z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ := by
      group
    rwa [e] at h1

theorem isHyperplane_closure_pair148 {A : Subgroup G} (hA : Late.IsE27 A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    IsHyperplane A (Subgroup.closure {x, y}) := by
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hox : orderOf x = 3 := orderOf_eq_prime (hA.1.2 x hx) hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime (hA.1.2 y hy) hy1
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
      rw [← hoy, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hoy])
      exact hyx ((heq ▸ Subgroup.mem_zpowers y : y ∈ _) |> Subgroup.mem_inf.mp).1
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers x)
    (Subgroup.zpowers y) fun u hu v hv =>
      hcomm u ((Subgroup.zpowers_le.mpr hx) hu) v ((Subgroup.zpowers_le.mpr hy) hv)
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hox, hoy] at hcard
  have hcl : Subgroup.closure {x, y} = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [show ({x, y} : Set G) = {x} ∪ {y} from rfl, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hx, hy]
  · rw [hA.2, hcl, hcard]

theorem sectionCentralizer_eq_zpowers148 {A Y K : Subgroup G} {e : G} (hA : Late.IsE27 A)
    (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    (heA : e ∈ A) (he1 : e ≠ 1) (hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G))
    (hKΔ : K = deltaZero A (lB A) K) (h3 : 3 ∣ Nat.card K) :
    Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) := by
  set N := pPrimeCoreOf 3 Y with hNdef
  have hAc : IsMulCommutative A := hA.1.1
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.1.2 g g.2)⟩
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hKΔ
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hYA.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hKe : ∀ k ∈ K, e * k = k * e := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKY hk).2).symm
  ext x
  constructor
  · rintro ⟨hxA, hxK⟩
    by_contra hxe
    have hxe' : x ∉ Subgroup.zpowers e := hxe
    set S := sectionCentralizerSubgroup148 A K N hAK hAN
    have heS : e ∈ S := by
      refine ⟨heA, fun k hk => ?_⟩
      rw [hKe k hk, mul_inv_cancel_right, mul_inv_cancel]
      exact N.one_mem
    have hxS : x ∈ S := ⟨hxA, hxK⟩
    set B₀ := Subgroup.closure ({e, x} : Set G) with hB₀def
    have hB₀ : IsHyperplane A B₀ := isHyperplane_closure_pair148 hA heA hxA he1 hxe'
    have hB₀S : B₀ ≤ S := by
      rw [hB₀def, Subgroup.closure_le]
      rintro z (rfl | rfl)
      exacts [heS, hxS]
    have hB₀p : IsPGroup 3 B₀ := hAp.to_le hB₀.1
    have hAB₀ : A ≤ Subgroup.centralizer (B₀ : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb =>
        congrArg Subtype.val (hAc.is_comm.comm ⟨b, hB₀.1 hb⟩ ⟨a, ha⟩)
    set M := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B₀ : Set G)) with hMdef
    have hQle : ∀ Q ∈ collectionIn (scriptQZero A (lB A)) K, Q ≤ N ⊔ M := by
      rintro Q ⟨hQ, hQK⟩
      have hQ3 : ¬ 3 ∣ Nat.card Q := fun h => (hQ.1.1.2.1 ⟨3, Nat.prime_three⟩ h) rfl
      have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.1.2.2
      have hdec := CFSG.LargeEvenClassification.Helpers.coprime_normalized_fixed_decomposition
        Nat.prime_three B₀ Q hB₀p hQ3 (hB₀.1.trans hAQ)
      have hQB : ⁅Q, B₀⁆ ≤ N := by
        rw [Subgroup.commutator_le]
        intro q hq b hb
        have h1 := (hB₀S hb).2 q (hQK hq)
        have e1 : ⁅q, b⁆ = (b * q * b⁻¹ * q⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e1]
        exact N.inv_mem h1
      set Q₀ := Q ⊓ Subgroup.centralizer (B₀ : Set G) with hQ₀def
      have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) := fun a ha =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hAQ ha, Subgroup.le_normalizer (hAB₀ ha)⟩
      have hQ₀3 : ¬ 3 ∣ Nat.card Q₀ := fun h =>
        hQ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
      set Q₁ := ⁅Q₀, A⁆ with hQ₁def
      have hQ₁Q₀ : Q₁ ≤ Q₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hAQ₀
      have hAQ₁ : A ≤ Subgroup.normalizer (Q₁ : Set G) :=
        Subgroup.normalizer_commutator_ge_right Q₀ A
      have hQ₁0 : Q₁ ∈ scriptQZero A (lB A) :=
        ⟨mem_scriptQ_of_le hQ.1 (hQ₁Q₀.trans inf_le_left) hAQ₁,
          (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
            Nat.prime_three A Q₀ hAp hQ₀3 hAQ₀).symm⟩
      have hQ₁Y : Q₁ ≤ Y ⊓ Subgroup.centralizer (B₀ : Set G) :=
        le_inf (hQ₁Q₀.trans (inf_le_left.trans (hQK.trans (hKY.trans inf_le_left))))
          (hQ₁Q₀.trans inf_le_right)
      have hQ₁M : Q₁ ≤ M := (le_deltaZero hQ₁0 hQ₁Y).trans (hYB B₀ hB₀)
      have hQNQ₁ : Q ≤ N ⊔ Q₁ := by
        calc Q = ⁅Q, A⁆ := hQ.2
          _ ≤ N ⊔ Q₁ := by
            rw [Subgroup.commutator_le]
            intro q hq a ha
            obtain ⟨f, hf, t, ht, hft⟩ := hdec ⟨q, hq⟩
            have hq' : q = (f : G) * t := congrArg Subtype.val hft.symm
            have htN : (t : G) ∈ N := hQB ht
            have e2 : ⁅q, a⁆ = ((f : G) * ((t : G) * (a * (t : G)⁻¹ * a⁻¹)) * (f : G)⁻¹) *
                ⁅(f : G), a⁆ := by
              rw [hq', commutatorElement_def, commutatorElement_def]
              group
            rw [e2]
            refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
            · have h1 : (t : G) * (a * (t : G)⁻¹ * a⁻¹) ∈ N :=
                N.mul_mem htN ((Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (N.inv_mem htN))
              have hfY : (f : G) ∈ Y := hKY.trans inf_le_left (hQK f.2)
              exact (Subgroup.mem_normalizer_iff.mp (hYN hfY) _).mp h1
            · exact Subgroup.commutator_mem_commutator ⟨f.2, hf⟩ ha
      exact hQNQ₁.trans (sup_le_sup_left hQ₁M N)
    have hKNM : K ≤ N ⊔ M := by
      calc K = deltaZero A (lB A) K := hKΔ
        _ ≤ N ⊔ M := sSup_le hQle
    have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans inf_le_left).trans hYN
    have hdvd := card_sup_dvd_of_le_normalizer148 N M hMN
    have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
      Nat.prime_three.coprime_iff_not_dvd.mp (coprime_card_pPrimeCoreOf 3 Y) h
    have hM3 : ¬ 3 ∣ Nat.card M := fun h =>
      Nat.prime_three.coprime_iff_not_dvd.mp (coprime_card_pPrimeCoreOf 3 _) h
    have hNM3 : ¬ 3 ∣ Nat.card N * Nat.card M := fun h =>
      ((Nat.Prime.dvd_mul Nat.prime_three).mp h).elim hN3 hM3
    exact hNM3 ((h3.trans (Subgroup.card_dvd_of_le hKNM)).trans hdvd)
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨A.zpow_mem heA n, fun k hk => ?_⟩
    have hc : e ^ n * k = k * e ^ n := (Commute.zpow_left (hKe k hk) n).eq
    rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    exact (pPrimeCoreOf 3 Y).one_mem

theorem not_isTripleCover_of_mem_lA148
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {e : G} {Le : Subgroup G} (he : Subgroup.zpowers e ∈ omegaA A)
    (hLe : Le ∈ lA A e) {X : Type*} [Group X] :
    ¬ Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) X := by
  rintro ⟨h3, -⟩
  rw [Sec15.center_eq_bot_of_types hLe.1 (h.chosen136.2 e he Le hLe).1, Subgroup.card_bot] at h3
  omega

theorem three_dvd_card_img148_of_types {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} [(ker148 A Y).Normal] {e : G} {K Le : Subgroup G}
    (ht : (Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
        (Nonempty (↥(img148 A Y K) ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
          ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
            Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7))) ∨
          (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
            Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
            IsLThreeEpsAt ↥(img148 A Y K) p f))) ∨
      (Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON ∧
        (Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y K) ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))))) :
    3 ∣ Nat.card (img148 A Y K) := by
  have hA7 : 3 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    norm_num
  rcases ht with ⟨he, hLe, ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hL3⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact three_dvd_card_of_types136 (h.chosen136.2 e he Le hLe).1
  · rw [Nat.card_congr φ.toEquiv]
    exact hA7
  · exact three_dvd_card_of_isLThreeEpsAt148 hf hL3
  · rw [Nat.card_congr φ.toEquiv]
    exact hA7
  · exact KFacts.three_dvd_card_of_mulEquiv_projSL φ

end Main148

open Main148

@[expose] def Step148KTypeOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        Nonempty (↥(img148 A Y K) ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
          ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
            Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7))) ∨
          (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
            Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
            IsLThreeEpsAt ↥(img148 A Y K) p f)

@[expose] def Step148KTypeON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → c' ∈ B →
        L' ∈ lA A c' →
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        IsThreeCentralIn L' e →
        Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON →
        letI := ker148_normal hY.2
        Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y K) ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))

theorem step148KType_of (hΩ : Step148KTypeOmega) (hON : Step148KTypeON) : Step148KType := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP
  let := ker148_normal hY.2
  obtain ⟨hB, -, -, heB, he1, hK, hKΔ, -, -, halt⟩ := id hP
  have ht : (Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
        (Nonempty (↥(img148 A Y K) ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
          ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
            Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7))) ∨
          (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
            Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
            IsLThreeEpsAt ↥(img148 A Y K) p f))) ∨
      (Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON ∧
        (Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y K) ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))) := by
    rcases halt with ⟨he, hLe⟩ | ⟨c', L', hc', hc'B, hL', hJ2, hd, hON3⟩
    · exact Or.inl ⟨he, hLe, hΩ G A c L h Y hY hs hYB B Q e K Le hP he hLe⟩
    · exact Or.inr ⟨hON3, hON G A c L h Y hY hs hYB B Q e K Le hP c' L' hc' hc'B hL' hJ2 hd hON3⟩
  refine ⟨?_, ht⟩
  have hKY := le_of_mem_thetaComponentsIn hK
  have h3 : 3 ∣ Nat.card K := (three_dvd_card_img148_of_types h ht).trans
    (card_img148_dvd (hKY.trans (inf_le_left.trans le_sup_left)))
  exact sectionCentralizer_eq_zpowers148 h.isE27 hY.2 hYB (hB.1 heB) he1 hKY hKΔ h3

theorem step148KTypeOmega_of_step148KType
    (hKT : Step148KType) :
    Step148KTypeOmega := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP he hLe
  rcases (hKT G A c L h Y hY hs hYB B Q e K Le hP).2 with ⟨-, -, ht⟩ | ⟨hON3, -⟩
  · exact ht
  · exact absurd hON3 (not_isTripleCover_of_mem_lA148 h he hLe)

theorem step148KTypeON_of_step148KType
    (hKT : Step148KType) :
    Step148KTypeON := by
  intro G _ _ A c L h Y hY hs hYB B Q e K Le hP _ _ _ _ _ _ _ hON3
  rcases (hKT G A c L h Y hY hs hYB B Q e K Le hP).2 with ⟨he, hLe, -⟩ | ⟨-, ht⟩
  · exact absurd hON3 (not_isTripleCover_of_mem_lA148 h he hLe)
  · exact ht

end CFSG.RankThree.PartTwo.Sec14
