module

public import CFSG.RankThree.Theta.TwoPlaneStar
public import CFSG.RankThree.GroupTheory.SteinbergBMAlphaProductStructure
public import CFSG.SignalizerFunctorTheorem.SolvableTheorem

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThreeEvenClassification.Helpers Subgroup

@[expose] def twoActorSignalizer {X : Type*} [Group X] (A : Subgroup X) (x : X) : Subgroup X :=
  ⁅inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set X)), A⁆ ⊔
    inSubgroup (CFSG.pCore 2) (centralizer (A : Set X))

@[expose] def twoCompletion {X : Type*} [Group X] (A : Subgroup X) : Subgroup X :=
  ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), twoActorSignalizer A a

variable {X : Type*} [Group X]

namespace TwoPlane

theorem not_three_dvd_card_of_isPGroup_two [Finite X] {S : Subgroup X} (hS : IsPGroup 2 S) :
    ¬ 3 ∣ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
  rw [hn] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

theorem centralizer_le_normalizer_commutator {A : Subgroup X} {x : X} (hx : x ∈ A) :
    centralizer (A : Set X) ≤ normalizer
      ((⁅inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set X)), A⁆ : Subgroup X) : Set X) :=
  normalizes_commutator_of_normalizes_both _ _ _
    ((centralizer_actor_le_element_centralizer A x hx).trans
      (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _))
    (centralizer_le_normalizer _)

theorem le_normalizer_commutator {A : Subgroup X} {x : X} (hx : x ∈ A) :
    inSubgroup (CFSG.pCore 2) (centralizer (A : Set X)) ≤ normalizer
      ((⁅inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set X)), A⁆ : Subgroup X) : Set X) :=
  (SteinbergBY.inSubgroup_pCore_le 2 _).trans (centralizer_le_normalizer_commutator hx)

theorem commutator_le_inSubgroup_pCore {A : Subgroup X} (hA : IsMulCommutative A) {x : X}
    (hx : x ∈ A) :
    ⁅inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set X)), A⁆ ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set X)) :=
  le_normalizer_iff_commutator_le_left.mp
    ((commutative_plane_le_element_centralizer A hA x hx).trans
      (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _))

theorem isPGroup_twoActorSignalizer {A : Subgroup X} (hA : IsMulCommutative A) {x : X}
    (hx : x ∈ A) : IsPGroup 2 (twoActorSignalizer A x) :=
  IsPGroup.to_sup_of_normal_left'
    ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le (commutator_le_inSubgroup_pCore hA hx))
    (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) (le_normalizer_commutator hx)

theorem twoActorSignalizer_le_centralizer {A : Subgroup X} (hA : IsMulCommutative A) {x : X}
    (hx : x ∈ A) : twoActorSignalizer A x ≤ centralizer ({x} : Set X) :=
  sup_le ((commutator_le_inSubgroup_pCore hA hx).trans (SteinbergBY.inSubgroup_pCore_le 2 _))
    ((SteinbergBY.inSubgroup_pCore_le 2 _).trans (centralizer_actor_le_element_centralizer A x hx))

theorem le_normalizer_twoActorSignalizer (A : Subgroup X) (x : X) :
    A ≤ normalizer (twoActorSignalizer A x : Set X) :=
  (le_inf (normalizer_commutator_ge_right _ A)
    ((le_centralizer_iff.mpr (SteinbergBY.inSubgroup_pCore_le 2 _)).trans
      (centralizer_le_normalizer _))).trans (inf_normalizer_le_normalizer_sup _ _)

theorem commutator_inf_centralizer_le {A : Subgroup X} (hA : IsMulCommutative A) {x : X}
    (hx : x ∈ A) :
    ⁅inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set X)), A⁆ ⊓ centralizer (A : Set X) ≤
      inSubgroup (CFSG.pCore 2) (centralizer (A : Set X)) :=
  SteinbergBY.le_inSubgroup_pCore
    ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le
      (inf_le_left.trans (commutator_le_inSubgroup_pCore hA hx)))
    inf_le_right
    (normalizes_inf_of_normalizes_both _ _ _ (centralizer_le_normalizer_commutator hx)
      le_normalizer)

theorem twoActorSignalizer_inf_centralizer {A : Subgroup X} (hA : IsMulCommutative A) {x : X}
    (hx : x ∈ A) :
    twoActorSignalizer A x ⊓ centralizer (A : Set X) =
      inSubgroup (CFSG.pCore 2) (centralizer (A : Set X)) := by
  rw [twoActorSignalizer, normalized_sup_centralizer_eq _ _ A (le_normalizer_commutator hx)
    (SteinbergBY.inSubgroup_pCore_le 2 _)]
  exact sup_eq_right.mpr (commutator_inf_centralizer_le hA hx)

theorem twoActorSignalizer_balance [Finite X] {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {c d : X} (hc : c ∈ A) (hd : d ∈ A)
    (hmix : ⁅inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) ⊓ centralizer ({c} : Set X),
      A⁆ ≤ inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X))) :
    twoActorSignalizer A d ⊓ centralizer ({c} : Set X) ≤ twoActorSignalizer A c := by
  have hp3 : IsPGroup 3 A := isElemAbelian_isPGroup 3 A hA
  set U := inSubgroup (CFSG.pCore 2) (centralizer (A : Set X)) with hU
  set J := ⁅inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)), A⁆ with hJ
  set F := J ⊓ centralizer ({c} : Set X) with hF
  set Y := twoActorSignalizer A d ⊓ centralizer ({c} : Set X) with hY
  have hUc : U ≤ centralizer ({c} : Set X) :=
    (SteinbergBY.inSubgroup_pCore_le 2 _).trans (centralizer_actor_le_element_centralizer A c hc)
  have hUJ : U ≤ normalizer (J : Set X) := le_normalizer_commutator hd
  have hUF : U ≤ normalizer (F : Set X) :=
    normalizes_inf_of_normalizes_both _ _ _ hUJ (hUc.trans le_normalizer)
  have hYeq : Y = F ⊔ U := by
    have h := normalized_sup_centralizer_eq J U (closure ({c} : Set X)) hUJ
      (by rwa [centralizer_closure])
    rwa [centralizer_closure] at h
  have hAc : A ≤ normalizer (centralizer ({c} : Set X) : Set X) :=
    (commutative_plane_le_element_centralizer A hA.1 c hc).trans le_normalizer
  have hAF : A ≤ normalizer (F : Set X) :=
    normalizes_inf_of_normalizes_both _ _ _ (normalizer_commutator_ge_right _ A) hAc
  have hAY : A ≤ normalizer (Y : Set X) :=
    normalizes_inf_of_normalizes_both _ _ _ (le_normalizer_twoActorSignalizer A d) hAc
  have hJle := commutator_le_inSubgroup_pCore hA.1 hd
  have hF3 : ¬ 3 ∣ Nat.card F := not_three_dvd_card_of_isPGroup_two
    ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le (inf_le_left.trans hJle))
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_card_of_isPGroup_two
    ((isPGroup_twoActorSignalizer hA.1 hd).to_le inf_le_left)
  have hFle : F ≤ inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) ⊓
      centralizer ({c} : Set X) := le_inf (inf_le_left.trans hJle) inf_le_right
  have hFA : ⁅F, A⁆ ≤ ⁅inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X)), A⁆ := by
    rw [← coprime_commutator_idempotent 3 Nat.prime_three A F hp3 hF3 hAF]
    exact commutator_mono ((commutator_mono hFle le_rfl).trans hmix) le_rfl
  have hYA : ⁅Y, A⁆ = ⁅F, A⁆ := by
    rw [hYeq]
    exact normalized_sup_commutator_eq_of_fixed F U A hUF (SteinbergBY.inSubgroup_pCore_le 2 _)
  have hYfix : Y ⊓ centralizer (A : Set X) ≤ U :=
    (inf_le_inf_right _ inf_le_left).trans (twoActorSignalizer_inf_centralizer hA.1 hd).le
  rw [coprime_commutator_centralizer_factorization 3 Nat.prime_three A Y hp3 hY3 hAY, hYA]
  exact sup_le_sup hFA hYfix

end TwoPlane

theorem two_actor_signalizer [Finite X] {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hmix : TwoMixedBalance A) :
    CFSG.Open.IsSolvableSignalizerFunctor 3 A (twoActorSignalizer A) where
  le_centralizer _ ha _ := TwoPlane.twoActorSignalizer_le_centralizer hA.1 ha
  coprime _ ha _ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (TwoPlane.not_three_dvd_card_of_isPGroup_two (TwoPlane.isPGroup_twoActorSignalizer hA.1 ha))
  invariant a _ _ x hx :=
    SteinbergBY.map_conj_eq_of_mem_normalizer (TwoPlane.le_normalizer_twoActorSignalizer A a hx)
  balance a ha ha1 b hb hb1 := TwoPlane.twoActorSignalizer_balance hA hb ha (hmix b hb hb1 a ha ha1)
  solvable _ ha _ := by
    have := (TwoPlane.isPGroup_twoActorSignalizer hA.1 ha).isNilpotent
    infer_instance

theorem two_completion_isPGroup {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hmix : TwoMixedBalance A) :
    IsPGroup 2 (twoCompletion A) ∧
      ∀ a ∈ A, a ≠ 1 → twoActorSignalizer A a = twoCompletion A ⊓ centralizer ({a} : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsig := two_actor_signalizer hA hmix
  obtain ⟨hcop, hsolv, hcent⟩ :=
    SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor X 3 Nat.prime_three A hA.1
      hA.2 (by rw [hAcard]; norm_num) (twoActorSignalizer A) hsig
  refine ⟨?_, hcent⟩
  have hW : SignalizerCompatible 3 A (twoActorSignalizer A)
      (signalizerGenerated A (twoActorSignalizer A)) :=
    { normalized := signalizerGenerated_normalized 3 A (twoActorSignalizer A) hsig
      solvable := hsolv
      primeComplement := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
      fixed_le := fun a ha ha1 => (hcent a ha ha1).symm.le }
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 3 (n := 2)
    (by rw [hAcard]; norm_num)
  set B := K.map A.subtype with hB
  have hBA : B ≤ A := map_subtype_le K
  have hBcard : Nat.card B = 3 ^ 2 := by
    rw [hB, card_map_of_injective A.subtype_injective, hK]
  have hBpow : ∀ member : B, member ^ 3 = 1 := fun x =>
    Subtype.ext (by simpa using hA.2 x (hBA x.2))
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro q hq hdiv
  obtain ⟨-, a, ha, -, hqa⟩ := SignalizerCompatible.prime_dvd_mem_spectrum 3 Nat.prime_three A B
    (twoActorSignalizer A) (isElemAbelian_isPGroup 3 A hA) hBA hBpow hBcard _ hW q hq hdiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (TwoPlane.isPGroup_twoActorSignalizer hA.1 ha)
  rw [hn] at hqa
  exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqa)

theorem twoAlpha_le_twoCompletion [Finite X] {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {D : Subgroup X} (hDA : D ≤ A) (hD : D ≠ ⊥) :
    twoAlpha D ≤ twoCompletion A := by
  have hp3 : IsPGroup 3 A := isElemAbelian_isPGroup 3 A hA
  have hle : ∀ a ∈ A, a ≠ 1 → twoActorSignalizer A a ≤ twoCompletion A := fun a ha ha1 =>
    signalizer_value_le_generated A (twoActorSignalizer A) a ha ha1
  refine sup_le ?_ ?_
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    exact (commutator_mono le_rfl hDA).trans (le_sup_left.trans (hle b (hDA hb) hb1))
  · obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := ne_bot_iff_exists_ne_one.mp hD
    have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
    obtain ⟨-, -, -, -, hCX, -, -⟩ := SteinbergBM.alpha_product_structure hD
    have hTR : twoT D ≤ inSubgroup (CFSG.pCore 2) (centralizer ({b₀} : Set X)) := fun x hx =>
      mem_twoCoreX_iff.mp hx b₀ hb₀ hb₀1'
    have hT2 : IsPGroup 2 (twoT D) := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hTR
    have hCD : centralizer (A : Set X) ≤ centralizer (D : Set X) := centralizer_le hDA
    have hAD : A ≤ centralizer (D : Set X) := fun x hx => mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hDA hy⟩ ⟨x, hx⟩)
    have hAT : A ≤ normalizer (twoT D : Set X) := hAD.trans hCX
    rw [coprime_commutator_centralizer_factorization 3 Nat.prime_three A (twoT D) hp3
      (TwoPlane.not_three_dvd_card_of_isPGroup_two hT2) hAT]
    refine sup_le ?_ ?_
    · exact (commutator_mono hTR le_rfl).trans (le_sup_left.trans (hle b₀ (hDA hb₀) hb₀1'))
    · refine le_trans ?_ (le_sup_right.trans (hle b₀ (hDA hb₀) hb₀1'))
      exact SteinbergBY.le_inSubgroup_pCore (hT2.to_le inf_le_left) inf_le_right
        (normalizes_inf_of_normalizes_both _ _ _ (hCD.trans hCX) le_normalizer)

theorem isPGroup_twoAlpha {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hmix : TwoMixedBalance A) {D : Subgroup X} (hDA : D ≤ A) (hD : D ≠ ⊥) :
    IsPGroup 2 (twoAlpha D) :=
  (two_completion_isPGroup hA hAcard hmix).1.to_le (twoAlpha_le_twoCompletion hA hDA hD)

end CFSG.RankThree.Theta
