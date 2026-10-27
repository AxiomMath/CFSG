module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Tools
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofCasesB
import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofTwoInner
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def KS154J2Four : Prop :=
  ∀ (Γ : Type) [Group Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E K R : Subgroup Γ, IsPGroup 3 E → 9 ≤ Nat.card E → K ≠ ⊥ → Group.IsPerfect K →
      E ≤ Subgroup.normalizer (K : Set Γ) → R ≠ ⊥ → IsPGroup 2 R →
        E ≤ Subgroup.normalizer (R : Set Γ) → K ≤ Subgroup.normalizer (R : Set Γ) →
          Nat.card R = 4 ∧ ∀ r ∈ R, r ^ 2 = 1

@[expose] def KS154J2PerfNorm : Prop :=
  ∀ (Γ : Type) [Group Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E K R : Subgroup Γ, IsPGroup 3 E → 9 ≤ Nat.card E → K ≠ ⊥ → Group.IsPerfect K →
      E ≤ Subgroup.normalizer (K : Set Γ) → R ≠ ⊥ → IsPGroup 2 R →
        E ≤ Subgroup.normalizer (R : Set Γ) → K ≤ Subgroup.normalizer (R : Set Γ) →
          Nat.card R = 4 ∧ (∀ r ∈ R, r ^ 2 = 1) ∧
            Nonempty (K ≃* alternatingGroup (Fin 5)) ∧
            ∀ e ∈ E, ∀ r ∈ R, r ≠ 1 → e * r = r * e → e ∈ K

section Reduction


theorem ks154J2PerfNorm_of_four (h : KS154J2Four) : KS154J2PerfNorm := by
  intro Γ _ hΓ E K R hE3 hE9 hK1 hKp hEK hR1 hR2 hER hKR
  obtain ⟨hR4, hRexp⟩ := h Γ hΓ E K R hE3 hE9 hK1 hKp hEK hR1 hR2 hER hKR
  have hKC : K ≤ Subgroup.centralizer (R : Set Γ) :=
    Proof155w3.le_centralizer_of_isPerfect_of_card_four hKp hKR hR4
  obtain ⟨φ⟩ := AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 Γ hΓ R hR4 hRexp
    ⟨K, hK1, hKp, hKC⟩
  set C := Subgroup.centralizer (R : Set Γ) with hCdef
  set V := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  set f : C →* V := (MonoidHom.fst V (alternatingGroup (Fin 5))).comp φ.toMonoidHom with hf
  set N := f.ker with hN
  set g : N →* alternatingGroup (Fin 5) :=
    (MonoidHom.snd V (alternatingGroup (Fin 5))).comp (φ.toMonoidHom.comp N.subtype) with hg
  have hgi : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : f x = 1 := x.2
    have h2 : φ x = 1 := Prod.ext h1 hx
    have h3 : (x : C) = 1 := by
      rw [← φ.map_one] at h2
      exact φ.injective h2
    exact Subtype.ext h3
  have hgs : Function.Surjective g := by
    intro a
    refine ⟨⟨φ.symm (1, a), ?_⟩, ?_⟩
    · show f (φ.symm (1, a)) = 1
      simp [hf]
    · simp [hg]
  set eN : N ≃* alternatingGroup (Fin 5) := MulEquiv.ofBijective g ⟨hgi, hgs⟩ with heN
  set K' := K.subgroupOf C with hK'
  have hK'p : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hK'N : K' ≤ N := by
    intro x hx
    have := eq_one_of_isPerfect (H := K') (f.comp K'.subtype) ⟨x, hx⟩
    exact this
  have hK'1 : K' ≠ ⊥ := by
    intro hbot
    apply hK1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hKC hx⟩ : C) ∈ K' := Subgroup.mem_subgroupOf.mpr hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hT : K'.subgroupOf N = ⊤ := by
    refine Proof15Res8Diag.eq_top_of_isPerfect_five eN ?_ ?_
    · exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hK'N).symm.toMonoidHom) (MulEquiv.surjective _)
    · intro hbot
      apply hK'1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hK'N hx⟩ : N) ∈ K'.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hNK' : N ≤ K' := by
    intro x hx
    have : (⟨x, hx⟩ : N) ∈ K'.subgroupOf N := hT ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hK'eq : K' = N := le_antisymm hK'N hNK'
  refine ⟨hR4, hRexp, ⟨((Subgroup.subgroupOfEquivOfLe hKC).symm.trans
    (MulEquiv.subgroupCongr hK'eq)).trans eN⟩, ?_⟩
  intro e he r hr hr1 her
  obtain ⟨k, hk⟩ := hE3 ⟨e, he⟩
  have hek : e ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have heC : e ∈ C := mem_centralizer_of_fix hR4 hRexp hek (hER he) hr hr1 her
  have hfe : f ⟨e, heC⟩ = 1 := by
    have h2 : f ⟨e, heC⟩ ^ 2 = 1 := by
      have : ∀ v : V, v ^ 2 = 1 := by
        rintro ⟨a, b⟩
        refine Prod.ext ?_ ?_
        · change a ^ 2 = 1
          rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
          exact congrArg Multiplicative.ofAdd (by decide +revert)
        · change b ^ 2 = 1
          rw [← ofAdd_toAdd b, ← ofAdd_nsmul]
          exact congrArg Multiplicative.ofAdd (by decide +revert)
      exact this _
    have h3 : f ⟨e, heC⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨e, heC⟩ : C) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hek)
      rw [this, map_one]
    have hco : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have hd2 := orderOf_dvd_of_pow_eq_one h2
    have hd3 := orderOf_dvd_of_pow_eq_one h3
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco hd2 hd3)
  have : (⟨e, heC⟩ : C) ∈ K' := hNK' hfe
  exact Subgroup.mem_subgroupOf.mp this

end Reduction

variable {G : Type} [Group G] [Finite G]

section J2


theorem exists_card_nine_map_conj_le_of_j2 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hYO : CFSG.Open.pCoreOf 2 Y ≠ ⊥)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ E : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y), Nat.card E = 9 ∧
      E.map (MulAut.conj : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≤
        (A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (Sec17.Proof17Res6.actQ Y) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φJ⟩ := hJ
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  set Jb := ↥Y ⧸ CFSG.pCore 2 ↥Y
  set N := Subgroup.normalizer (Y : Set G) with hNdef
  have hZ : Subgroup.center Jb = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φJ⟩
  have hconj : Function.Injective (MulAut.conj : Jb →* MulAut Jb) := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center Jb := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut Jb => σ z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  obtain ⟨E₉, hE₉e, hE₉c⟩ := Proof155w3.exists_elemAbelian_nine_of_j2 ⟨φJ⟩
  set Ab := (A.subgroupOf N).map (Sec17.Proof17Res6.actQ Y) with hAb
  have hA9 : 9 ≤ Nat.card Ab := Proof155w3.nine_le_card_map_actQ h hYO hAY hZ hE₉e hE₉c
  have hAinner : Ab ≤ (MulAut.conj : Jb →* MulAut Jb).range := by
    rintro _ ⟨a, ha, rfl⟩
    refine Proof155w3.mem_range_conj_of_pow_three ⟨φJ⟩ ?_
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [ha3, map_one]
  set E' := Ab.comap (MulAut.conj : Jb →* MulAut Jb) with hE'
  have hE'map : E'.map (MulAut.conj : Jb →* MulAut Jb) = Ab := Subgroup.map_comap_eq_self hAinner
  have hE'card : Nat.card E' = Nat.card Ab := by
    rw [← hE'map, Subgroup.card_map_of_injective hconj]
  have hAb3 : IsPGroup 3 Ab := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, ha3, map_one]
  have hE'3 : IsPGroup 3 E' := hAb3.of_equiv
    ((Subgroup.equivMapOfInjective E' _ hconj).trans (MulEquiv.subgroupCongr hE'map)).symm
  have h9E' : 3 ^ 2 ∣ Nat.card E' := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE'3
    rw [hk]
    refine pow_dvd_pow 3 ?_
    by_contra hk2
    push Not at hk2
    have : Nat.card E' ≤ 3 := by
      rw [hk]
      interval_cases k <;> norm_num
    omega
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9E'
  refine ⟨E₀.map E'.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E'.subtype_injective, hE₀]
    norm_num
  · rw [← hE'map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)

theorem abar_le_innQ_of_j2 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {Y : Subgroup G}
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    (A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (Sec17.Proof17Res6.actQ Y) ≤
      innQ Y := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  rintro _ ⟨a, ha, rfl⟩
  refine Proof155w3.mem_range_conj_of_pow_three hJ ?_
  rw [← map_pow]
  have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
  rw [ha3, map_one]


theorem barR_le_innQ_of_j2 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y R : Subgroup G} (hYO : CFSG.Open.pCoreOf 2 Y ≠ ⊥)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : barR Y R ≤ innQ Y := by
  classical
  obtain ⟨E, hE9, hEA⟩ := exists_card_nine_map_conj_le_of_j2 h hYO hAY hJ
  have hR2' : IsPGroup 2 (R.subgroupOf (Subgroup.normalizer (Y : Set G))) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  have hbar2 : IsPGroup 2 (barR Y R) := hR2'.map _
  have hAN : (A.subgroupOf (Subgroup.normalizer (Y : Set G))).map (Sec17.Proof17Res6.actQ Y) ≤
      Subgroup.normalizer (barR Y R : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    exact actQ_mem_normalizer_barR a.2 (hAR (Subgroup.mem_subgroupOf.mp ha))
  exact Sec16.ks162J2TwoInner _ hJ E hE9 (barR Y R) hbar2 (hEA.trans hAN)


theorem hj_branch (hKf : KS154J2PerfNorm) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {X Y R : Subgroup G} (hYO : CFSG.Open.pCoreOf 2 Y ≠ ⊥)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hXY : X ≤ Y) (hXp : Group.IsPerfect ↥X) (hX1 : X ≠ ⊥)
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hXR : X ≤ Subgroup.normalizer (R : Set G)) :
    ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨
      (Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∧
        (centralizerSection Y (CFSG.Open.pCoreOf 2 Y)).relIndex R = 4 ∧
        (∀ r ∈ R, r ^ 2 ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) ∧
        ∀ d ∈ A, d ∉ centralizerSection Y (CFSG.Open.pCoreOf 2 Y) →
          (∀ x ∈ X, ⁅x, d⁆ ∈ CFSG.Open.pCoreOf 2 X) →
            R ⊓ Subgroup.centralizer ({d} : Set G) ≤
              centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinn := barR_le_innQ_of_j2 h hYO hAY hJ hRY hR2 hAR
  by_cases hbot : barR Y R = ⊥
  · exact Or.inl (commutator_le_pCoreOf_of_barR_eq_bot hRY hbot)
  right
  obtain ⟨φJ⟩ := hJ
  set Q := ↥Y ⧸ CFSG.pCore 2 ↥Y
  set N := Subgroup.normalizer (Y : Set G) with hNdef
  set C := centralizerSection Y (CFSG.Open.pCoreOf 2 Y) with hCdef
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hκ
  have hZ : Subgroup.center Q = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φJ⟩
  have hconj := conj_injective_of_center_eq_bot hZ
  set Rs := (barR Y R).comap (MulAut.conj : Q →* MulAut Q) with hRsdef
  have hRsmap : Rs.map (MulAut.conj : Q →* MulAut Q) = barR Y R :=
    Subgroup.map_comap_eq_self hinn
  have hRscard : Nat.card Rs = Nat.card (barR Y R) := by
    rw [← hRsmap, Subgroup.card_map_of_injective hconj]
  have hR2' : IsPGroup 2 (R.subgroupOf N) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  have hbar2 : IsPGroup 2 (barR Y R) := hR2'.map _
  have hRs2 : IsPGroup 2 Rs := hbar2.of_equiv
    ((Subgroup.equivMapOfInjective Rs _ hconj).trans (MulEquiv.subgroupCongr hRsmap)).symm
  have hRs1 : Rs ≠ ⊥ := by
    intro h1
    apply hbot
    rw [← hRsmap, h1, Subgroup.map_bot]
  set Ab := (A.subgroupOf N).map (Sec17.Proof17Res6.actQ Y) with hAb
  have hAinn : Ab ≤ innQ Y := abar_le_innQ_of_j2 h ⟨φJ⟩
  obtain ⟨E₉, hE₉e, hE₉c⟩ := Proof155w3.exists_elemAbelian_nine_of_j2 ⟨φJ⟩
  have hA9 : 9 ≤ Nat.card Ab := Proof155w3.nine_le_card_map_actQ h hYO hAY hZ hE₉e hE₉c
  set E := Ab.comap (MulAut.conj : Q →* MulAut Q) with hEdef
  have hEmap : E.map (MulAut.conj : Q →* MulAut Q) = Ab := Subgroup.map_comap_eq_self hAinn
  have hEcard : Nat.card E = Nat.card Ab := by
    rw [← hEmap, Subgroup.card_map_of_injective hconj]
  have hAb3 : IsPGroup 3 Ab := by
    have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, ha3, map_one]
  have hE3 : IsPGroup 3 E := hAb3.of_equiv
    ((Subgroup.equivMapOfInjective E _ hconj).trans (MulEquiv.subgroupCongr hEmap)).symm
  have hEN : E ≤ Subgroup.normalizer (Rs : Set Q) := by
    intro e he
    refine mem_normalizer_comap_conj ?_
    obtain ⟨a, ha, hae⟩ := (Subgroup.mem_comap.mp he : MulAut.conj e ∈ Ab)
    rw [← hae]
    exact actQ_mem_normalizer_barR a.2 (hAR (Subgroup.mem_subgroupOf.mp ha))
  set K := (X.subgroupOf Y).map κ with hKdef
  have hKN : K ≤ Subgroup.normalizer (Rs : Set Q) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_normalizer_comap_conj ?_
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    rw [← Sec17.Proof17Res6.actQ_of_mem]
    exact actQ_mem_normalizer_barR (Y.le_normalizer x.2) (hXR hxX)
  have hKp : Group.IsPerfect K := by
    have hXp' : Group.IsPerfect (X.subgroupOf Y) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXY).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.ofSurjective (f := κ.subgroupMap (X.subgroupOf Y))
      (κ.subgroupMap_surjective _)
  have hK1 : K ≠ ⊥ := by
    intro hK
    apply hX1
    have hX2 : IsPGroup 2 ↥X := by
      intro x
      have h1 : κ ⟨x, hXY x.2⟩ = 1 := by
        have : κ ⟨x, hXY x.2⟩ ∈ K := ⟨⟨x, hXY x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
        rw [hK, Subgroup.mem_bot] at this
        exact this
      rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y)) ⟨_, h1⟩
      have hn1 := congrArg Subtype.val hn
      have hn2 := congrArg Subtype.val hn1
      exact ⟨n, Subtype.ext (by simpa using hn2)⟩
    by_contra hne
    have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
    have : Group.IsNilpotent ↥X := hX2.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥X inferInstance
  have hEK : E ≤ Subgroup.normalizer (K : Set Q) := by
    intro e he
    obtain ⟨a, ha, hae⟩ := (Subgroup.mem_comap.mp he : MulAut.conj e ∈ Ab)
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨x, hx, rfl⟩ := hk
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have h1 : e * κ x * e⁻¹ = Sec17.Proof17Res6.actQ Y a (κ x) := by
      rw [hae, MulAut.conj_apply]
    rw [h1, hκ, Sec17.Proof17Res6.actQ_mk]
    refine ⟨Y.normalizerMonoidHom a x, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAX haA) x).mp hxX
  obtain ⟨hRs4, hRsexp, ⟨eK⟩, hfix⟩ :=
    hKf Q ⟨φJ⟩ E K Rs hE3 (hEcard ▸ hA9) hK1 hKp hEK hRs1 hRs2 hEN hKN
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hA5not2 : ¬ IsPGroup 2 (alternatingGroup (Fin 5)) := by
    intro h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hA5card] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  obtain ⟨hO2le, hXbar⟩ := pCoreOf_le_and_nonempty_quot_equiv hXY hA5not2 eK
  refine ⟨hXbar, ?_, ?_, ?_⟩
  ·
    rw [← card_barR_eq_relIndex hRY, ← hRscard, hRs4]
  ·
    intro r hr
    have hmem : Sec17.Proof17Res6.actQ Y ⟨r, hRY hr⟩ ∈ barR Y R := mem_barR hr (hRY hr)
    rw [← hRsmap] at hmem
    obtain ⟨s, hs, hse⟩ := hmem
    have h1 : Sec17.Proof17Res6.actQ Y (⟨r, hRY hr⟩ ^ 2) = 1 := by
      rw [map_pow, ← hse, ← map_pow, hRsexp s hs, map_one]
    exact (actQ_eq_one_iff _).mp h1
  ·
    intro d hd hdC hdX r ⟨hr, hrd⟩
    have hdN : d ∈ N := hAY hd
    have hdA : Sec17.Proof17Res6.actQ Y ⟨d, hdN⟩ ∈ Ab :=
      ⟨⟨d, hdN⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    obtain ⟨e, he⟩ := hAinn hdA
    have heE : e ∈ E := by
      show MulAut.conj e ∈ Ab
      rw [he]
      exact hdA
    have heK : e ∉ K := by
      intro heK
      have hfixK : ∀ k ∈ K, e * k * e⁻¹ = k := by
        rintro _ ⟨x, hx, rfl⟩
        have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
        have h1 : MulAut.conj e (κ x) = κ x := by
          rw [he, hκ, Sec17.Proof17Res6.actQ_mk]
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
            ← CFSG.mem_openPCoreOf_iff]
          have h2 := hO2le (hdX _ (X.inv_mem hxX))
          have e2 : (((Y.normalizerMonoidHom ⟨d, hdN⟩ x)⁻¹ * x : ↥Y) : G) =
              (⁅(x : G)⁻¹, d⁆)⁻¹ := by
            change (d * x * d⁻¹)⁻¹ * x = _
            rw [commutatorElement_def]
            group
          rw [e2]
          exact inv_mem h2
        simpa [MulAut.conj_apply] using h1
      have heZ : (⟨e, heK⟩ : K) ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        have := hfixK k k.2
        simp only [Subgroup.coe_mul]
        calc (k : Q) * e = e * (e⁻¹ * k * e) := by group
          _ = e * k := by
            congr 1
            have h3 := hfixK (e⁻¹ * k * e) (by
              have := K.mul_mem (K.mul_mem (K.inv_mem heK) k.2) heK
              simpa [mul_assoc] using this)
            calc e⁻¹ * (k : Q) * e = e * (e⁻¹ * k * e) * e⁻¹ := h3.symm
              _ = k := by group
      have hZK : Subgroup.center K = ⊥ := by
        have hZA : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
          alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
        have hmap := Subgroup.map_center_eq eK
        rw [hZA] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).mp hmap
      rw [hZK, Subgroup.mem_bot] at heZ
      have he1 : e = 1 := congrArg Subtype.val heZ
      apply hdC
      refine (actQ_eq_one_iff ⟨d, hdN⟩).mp ?_
      rw [← he, he1, map_one]
    have hmem : Sec17.Proof17Res6.actQ Y ⟨r, hRY hr⟩ ∈ barR Y R := mem_barR hr (hRY hr)
    rw [← hRsmap] at hmem
    obtain ⟨s, hs, hse⟩ := hmem
    have hcomm : e * s = s * e := by
      apply hconj
      rw [map_mul, map_mul, hse, he, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hrd).symm
    have hs1 : s = 1 := by
      by_contra hs1
      exact heK (hfix e heE s hs hs1 hcomm)
    refine (actQ_eq_one_iff ⟨r, hRY hr⟩).mp ?_
    rw [← hse, hs1, map_one]

end J2

end CFSG.RankThree.PartTwo.Sec15.Wales154
