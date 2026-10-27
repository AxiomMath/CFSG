module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofStar
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Blueprint
open Item211Res2Proof
open scoped commutatorElement

@[expose] def IsExc211 (X : Type) [Group X] : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    (ChevalleyExceptionalModel X .G2 p 1 ∨ Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))

@[expose] def threeGen {M : Type*} [Group M] (H : Subgroup M) : Subgroup M :=
  Subgroup.closure {h | h ∈ H ∧ ∃ n : ℕ, h ^ (3 ^ n) = 1}

@[expose] def conjClosure {M : Type*} [Group M] (D H : Subgroup M) : Subgroup M :=
  Subgroup.closure {y | ∃ g ∈ H, ∃ x ∈ D, y = g * x * g⁻¹}

@[expose] def KS211ExcInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsExc211 X →
    Subgroup.center X = ⊥ ∧ ∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range

@[expose] def KS211ExcPlus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsExc211 X →
    ∀ D : Subgroup (MulAut X), D ≤ (MulAut.conj : X →* MulAut X).range → IsElemAbelian 3 D →
      Nat.card D = 9 → ∀ d ∈ D, d ≠ 1 → ∀ T : Subgroup (MulAut X), IsPGroup 2 T →
        T ≤ Subgroup.centralizer (D : Set (MulAut X)) →
        D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
          (conjClosure D ((MulAut.conj : X →* MulAut X).range ⊓
            Subgroup.centralizer ({d} : Set (MulAut X))) ⊓
              Subgroup.centralizer (T : Set (MulAut X))) : Subgroup (MulAut X)) : Set (MulAut X))

@[expose] def KS211ExcMinus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsExc211 X →
    ∀ D T : Subgroup (MulAut X), D ≤ (MulAut.conj : X →* MulAut X).range →
      T ≤ (MulAut.conj : X →* MulAut X).range → IsElemAbelian 3 D → Nat.card D = 9 →
      IsElemAbelian 2 T → Nat.card T = 4 → D ≤ Subgroup.normalizer (T : Set (MulAut X)) →
      ⁅T, D⁆ = T → ∀ u ∈ T, u ≠ 1 →
        D ⊓ Subgroup.centralizer (T : Set (MulAut X)) ≤ Subgroup.centralizer ((inSubgroup
          (CFSG.pCore 2) (threeGen ((MulAut.conj : X →* MulAut X).range ⊓
            Subgroup.centralizer ({u} : Set (MulAut X))) ⊓
              Subgroup.centralizer (T : Set (MulAut X))) : Subgroup (MulAut X)) : Set (MulAut X))

namespace Item211LieProof

variable {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}

theorem inf_inSubgroup_pCore_le {M : Type*} [Group M] [Finite M] {H K : Subgroup M} (hHK : H ≤ K) :
    inSubgroup (CFSG.pCore 2) K ⊓ H ≤ inSubgroup (CFSG.pCore 2) H := by
  refine le_inSubgroup_pCore inf_le_right (((CFSG.pCore_isPGroup).map K.subtype).to_le inf_le_left)
    fun g hg => Subgroup.mem_normalizer_fintype fun x hx => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 K (hHK hg)) x).mp
        (Subgroup.mem_inf.mp hx).1
  · exact H.mul_mem (H.mul_mem hg (Subgroup.mem_inf.mp hx).2) (H.inv_mem hg)

theorem exc_setup (hI : KS211ExcInner) (h : PairFacts A E U c L) (hX : IsExc211 (lBar L)) :
    Odd (Nat.card (Subgroup.center (lBar L))) ∧
      barImage L E ≤ (MulAut.conj : lBar L →* MulAut (lBar L)).range := by
  obtain ⟨hZ, hinn⟩ := hI (lBar L) h.q hX
  exact ⟨by rw [hZ, Subgroup.card_bot]; exact odd_one, fun τ hτ =>
    hinn τ ((isElemAbelian_barImage_E h).2 τ hτ)⟩

end Item211LieProof

open Item211LieProof

section Certs

theorem item211LieMinusExc_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hI : KS211ExcInner) (hK : KS211ExcMinus) : Item211LieMinusExc := by
  intro G _ _ A E U c L hpair _ hM hcase
  obtain ⟨-, p, hp, hp3, hmodel⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have hX : IsExc211 (lBar L) := ⟨p, hp, hp3, hmodel⟩
  obtain ⟨hZodd, hEi⟩ := exc_setup hI h hX
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  set B := E ⊓ Subgroup.centralizer (U : Set G) with hB
  set V := lThreeV E U c with hV
  have hBi : barImage L B ≤ Inn := barImage_B_le_E.trans hEi
  have hUeq := barImage_U_eq_comm_of_minus h hM
  have hUi : barImage L U ≤ Inn := by
    rw [hUeq]
    exact commutator_le_range_conj _ _ hEi
  have hVeq := barImage_V_comm_B h
  have hVi : barImage L V ≤ Inn := by
    rw [← hVeq]
    exact commutator_le_range_conj _ _ hBi
  have hO2 := starO2 hpair.mem_S h hZodd hBi hVi
  obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (barImage_U_ne_bot h)
  have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  set Δ := threeGen (Inn ⊓ Subgroup.centralizer ({u} : Set (MulAut (lBar L)))) with hΔ
  have hKf := hK (lBar L) h.q hX (barImage L E) (barImage L U) hEi hUi
    (isElemAbelian_barImage_E h) (card_barImage_E h) (isElemAbelian_barImage_U h)
    (card_barImage_U_of_minus h hM) (barImage_E_le_normalizer_U h) hUeq.symm u huU hu1'
  have hVΔ : barImage L V ≤ Δ := by
    rw [← hVeq, Subgroup.commutator_le]
    intro v hv b hb
    have hb3 : b ^ 3 = 1 := (isElemAbelian_barImage_E h).2 b (barImage_B_le_E hb)
    have hbu : b ∈ Inn ⊓ Subgroup.centralizer ({u} : Set (MulAut (lBar L))) :=
      Subgroup.mem_inf.mpr ⟨hBi hb, Subgroup.mem_centralizer_singleton_iff.mpr
        (barImage_U_comm_B u huU b hb).symm⟩
    have hvu : v ∈ Inn ⊓ Subgroup.centralizer ({u} : Set (MulAut (lBar L))) :=
      Subgroup.mem_inf.mpr ⟨hVi hv, Subgroup.mem_centralizer_singleton_iff.mpr
        (barImage_U_comm_V h u huU v hv).symm⟩
    set H := Inn ⊓ Subgroup.centralizer ({u} : Set (MulAut (lBar L)))
    rw [commutatorElement_def]
    refine Δ.mul_mem (Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hvu hbu) (H.inv_mem hvu),
      1, ?_⟩) (Δ.inv_mem (Subgroup.subset_closure ⟨hbu, 1, by rw [pow_one, hb3]⟩))
    rw [pow_one, conj_pow, hb3, mul_one, mul_inv_cancel]
  have hΔInn : Δ ≤ Inn := (Subgroup.closure_le _).mpr fun x hx => (Subgroup.mem_inf.mp hx.1).1
  have hVO : barImage L V ≤ inSubgroup (CFSG.pCore 2)
      (Δ ⊓ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L)))) := by
    intro v hv
    refine inf_inSubgroup_pCore_le (inf_le_inf_right _ hΔInn)
      (Subgroup.mem_inf.mpr ⟨hO2 hv, Subgroup.mem_inf.mpr ⟨hVΔ hv,
        Subgroup.mem_centralizer_iff.mpr fun x hx => barImage_U_comm_V h x hx v hv⟩⟩)
  apply barImage_V_ne_bot h
  rw [← hVeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbC : b ∈ barImage L E ⊓ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) :=
    Subgroup.mem_inf.mpr ⟨barImage_B_le_E hb, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      barImage_U_comm_B x hx b hb⟩
  exact (Subgroup.mem_centralizer_iff.mp (hKf hbC) v (hVO hv)).symm

theorem item211LiePlusExc_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hI : KS211ExcInner) (hK : KS211ExcPlus) : Item211LiePlusExc := by
  intro G _ _ A E U c L hpair _ hP hcase
  obtain ⟨-, p, hp, hp3, hmodel⟩ := hcase
  have h := pairFacts h45 h66 hpair
  have hX : IsExc211 (lBar L) := ⟨p, hp, hp3, hmodel⟩
  obtain ⟨hZodd, hEi⟩ := exc_setup hI h hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Inn := (MulAut.conj : lBar L →* MulAut (lBar L)).range with hInn
  set V := lThreeV E U c with hV
  have hBE : E ⊓ Subgroup.centralizer (U : Set G) = E :=
    inf_eq_left.mpr (mem_fourGroupsPlus_iff.mp hP).2
  have hBi : barImage L (E ⊓ Subgroup.centralizer (U : Set G)) ≤ Inn :=
    barImage_B_le_E.trans hEi
  have hVeq : ⁅barImage L V, barImage L E⁆ = barImage L V := by
    have := barImage_V_comm_B h
    rwa [hBE] at this
  have hVi : barImage L V ≤ Inn := by
    rw [← hVeq]
    exact commutator_le_range_conj _ _ hEi
  have hO2 := starO2 hpair.mem_S h hZodd hBi hVi
  have hE3 : IsPGroup 3 (barImage L E) := fun g =>
    ⟨1, Subtype.ext (by simpa using (isElemAbelian_barImage_E h).2 _ g.2)⟩
  have hV2 := isPGroup_barImage_V h
  have hnot3 : ∀ {Y : Subgroup (MulAut (lBar L))}, IsPGroup 2 Y → ¬ 3 ∣ Nat.card Y := by
    intro Y hY h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_three
    (isElemAbelian_barImage_E h) (by rw [card_barImage_E h]; norm_num)
    (barImage_E_le_normalizer_V h)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hnot3 hV2))
  obtain ⟨d, hdE, hd1, hZne⟩ : ∃ d ∈ barImage L E, d ≠ 1 ∧
      ⁅barImage L V ⊓ Subgroup.centralizer ({d} : Set (MulAut (lBar L))), barImage L E⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply barImage_V_ne_bot h
    rw [← hVeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [← hgen]
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon d hd hd1)
  set X := barImage L V ⊓ Subgroup.centralizer ({d} : Set (MulAut (lBar L))) with hXdef
  set Z := ⁅X, barImage L E⁆ with hZdef
  have hX2 : IsPGroup 2 X := hV2.to_le inf_le_left
  have hEcomm : ∀ e ∈ barImage L E, e * d = d * e := fun e he =>
    congrArg Subtype.val ((isElemAbelian_barImage_E h).1.is_comm.comm ⟨e, he⟩ ⟨d, hdE⟩)
  have hEX : barImage L E ≤ Subgroup.normalizer (X : Set (MulAut (lBar L))) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (barImage_E_le_normalizer_V h he) x).mp
        (Subgroup.mem_inf.mp hx).1
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hxd := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
      have hed := hEcomm e he
      calc e * x * e⁻¹ * d = e * x * (e⁻¹ * d) := by group
        _ = e * x * (d * e⁻¹) := by
            rw [(Commute.inv_left (show Commute e d from hed)).eq]
        _ = e * (x * d) * e⁻¹ := by group
        _ = e * (d * x) * e⁻¹ := by rw [hxd]
        _ = (e * d) * x * e⁻¹ := by group
        _ = d * (e * x * e⁻¹) := by rw [hed]; group
  have hZZ : ⁅Z, barImage L E⁆ = Z :=
    CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent Nat.prime_three
      (barImage L E) X hE3 (hnot3 hX2) hEX
  set Γ := conjClosure (barImage L E) (Inn ⊓ Subgroup.centralizer ({d} : Set (MulAut (lBar L))))
    with hΓ
  have hZΓ : Z ≤ Γ := by
    rw [hZdef, Subgroup.commutator_le]
    intro x hx f hf
    have hxH : x ∈ Inn ⊓ Subgroup.centralizer ({d} : Set (MulAut (lBar L))) :=
      Subgroup.mem_inf.mpr ⟨hVi (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
    rw [commutatorElement_def]
    refine Γ.mul_mem (Subgroup.subset_closure ⟨x, hxH, f, hf, rfl⟩)
      (Γ.inv_mem (Subgroup.subset_closure ⟨1, Subgroup.one_mem _, f, hf, by group⟩))
  have hZV : Z ≤ barImage L V := by
    rw [hZdef, Subgroup.commutator_le]
    intro x hx f hf
    have hxV := (Subgroup.mem_inf.mp hx).1
    rw [commutatorElement_def]
    have h1 : f * x⁻¹ * f⁻¹ ∈ barImage L V :=
      (Subgroup.mem_normalizer_iff.mp (barImage_E_le_normalizer_V h hf) _).mp
        (Subgroup.inv_mem _ hxV)
    have e : x * f * x⁻¹ * f⁻¹ = x * (f * x⁻¹ * f⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxV h1
  have hΓInn : Γ ≤ Inn := by
    rw [hΓ, conjClosure, Subgroup.closure_le]
    rintro y ⟨g, hg, x, hx, rfl⟩
    exact Inn.mul_mem (Inn.mul_mem (Subgroup.mem_inf.mp hg).1 (hEi hx))
      (Inn.inv_mem (Subgroup.mem_inf.mp hg).1)
  have hZO : Z ≤ inSubgroup (CFSG.pCore 2)
      (Γ ⊓ Subgroup.centralizer (barImage L U : Set (MulAut (lBar L)))) := fun z hz =>
    inf_inSubgroup_pCore_le (inf_le_inf_right _ hΓInn) (Subgroup.mem_inf.mpr ⟨hO2 (hZV hz),
      Subgroup.mem_inf.mpr ⟨hZΓ hz, Subgroup.mem_centralizer_iff.mpr fun x hx =>
        barImage_U_comm_V h x hx z (hZV hz)⟩⟩)
  have hUC : barImage L U ≤ Subgroup.centralizer (barImage L E : Set (MulAut (lBar L))) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (barImage_U_comm_E_of_plus hP a ha e he).symm
  have hKf := hK (lBar L) h.q hX (barImage L E) hEi (isElemAbelian_barImage_E h)
    (card_barImage_E h) d hdE hd1 (barImage L U) (isPGroup_barImage_U h) hUC
  apply hZne
  rw [← hZZ, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact (Subgroup.mem_centralizer_iff.mp (hKf hf) z (hZO hz)).symm

end Certs

end CFSG.RankThree.PartTwo.Sec21
