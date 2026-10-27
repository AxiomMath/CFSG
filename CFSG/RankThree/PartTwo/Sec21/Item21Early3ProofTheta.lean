module

public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item21Early3Proof

open Item21EarlyProof

section General

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem zpowers_normal_of_mem_center {z : L} (hz : z ∈ Subgroup.center L) :
    (Subgroup.zpowers z).Normal := by
  constructor
  intro n hn g
  have hnc : n ∈ Subgroup.center L := (Subgroup.zpowers_le.mpr hz) hn
  rw [(Subgroup.mem_center_iff.mp hnc g), mul_inv_cancel_right]
  exact hn

theorem isTwoCover_quot_oddCore [hLp : Group.IsPerfect L] (T : Subgroup L) [T.Normal]
    [hsimp : IsSimpleGroup (L ⧸ centerPre T)] (hTs : Group.IsSolvable T)
    (hTL : ⁅T, (⊤ : Subgroup L)⁆ ≤ CFSG.oddCore L) (hTe : Even (Nat.card T)) :
    Sec4.Census.IsTwoCover (L ⧸ CFSG.oddCore L) (L ⧸ centerPre T) := by
  set M := CFSG.oddCore L with hMdef
  set K₀ := centerPre T with hK₀def
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have hModd : Odd (Nat.card M) := CFSG.ABGDGroups.odd_card_oddCore L
  have hMK : M ≤ K₀ := by
    by_contra h
    have htop : M = ⊤ := Sec4.Census.eq_top_of_not_le hK₀s h
    have hdvd : Nat.card T ∣ Nat.card M := by
      rw [htop, Subgroup.card_top]
      exact Subgroup.card_subgroup_dvd_card T
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hModd hdvd)) hTe
  set π := QuotientGroup.mk' M with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective M
  have hQp : Group.IsPerfect (L ⧸ M) := Group.IsPerfect.ofSurjective (f := π) hπs
  set Z₁ := K₀.map π with hZ₁
  have hZ₁n : Z₁.Normal := Subgroup.Normal.map inferInstance π hπs
  have hTZ : ∀ t ∈ T, π t ∈ Subgroup.center (L ⧸ M) := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := hπs q
    have h1 : ⁅t, l⁆ ∈ M := hTL (Subgroup.commutator_mem_commutator ht (Subgroup.mem_top l))
    have h2 : π ⁅t, l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have hZ₁c : Z₁ ≤ Subgroup.center (L ⧸ M) := by
    refine le_center_of_commutator_le ?_
    rw [Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ q -
    obtain ⟨l, rfl⟩ := hπs q
    rw [← map_commutatorElement]
    refine hTZ _ ?_
    have hk' : QuotientGroup.mk' T k ∈ Subgroup.center (L ⧸ T) := hk
    rw [← QuotientGroup.ker_mk' T, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hk' _).symm
  let e₁ : (L ⧸ M) ⧸ Z₁ ≃* L ⧸ K₀ := QuotientGroup.quotientQuotientEquivQuotient M K₀ hMK
  have : IsSimpleGroup ((L ⧸ M) ⧸ Z₁) := e₁.isSimpleGroup
  have hLKp : Group.IsPerfect (L ⧸ K₀) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' K₀) (QuotientGroup.mk'_surjective K₀)
  have hnc : ∃ a b : (L ⧸ M) ⧸ Z₁, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hsol : Group.IsSolvable (L ⧸ K₀) := Group.isSolvable_of_comm fun a b => by
      have := h (e₁.symm a) (e₁.symm b)
      simpa using congrArg e₁ this
    exact Group.IsPerfect.not_isSolvable (L ⧸ K₀) hsol
  have hq : IsQuasisimple (L ⧸ M) := isQuasisimple_of_le_center hnc hZ₁c
  have hZeq : Subgroup.center (L ⧸ M) = Z₁ := by
    refine le_antisymm ?_ hZ₁c
    have hMn : ((Subgroup.center (L ⧸ M)).map (QuotientGroup.mk' Z₁)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z₁)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Subgroup.center (L ⧸ M)).map (QuotientGroup.mk' Z₁)) with h | h
    · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hb : b ∈ (Subgroup.center (L ⧸ M)).map (QuotientGroup.mk' Z₁) := h ▸ Subgroup.mem_top b
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z₁ a
      apply hab
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz a]
  have hcardK : Nat.card K₀ = Nat.card M * Nat.card Z₁ := by
    have h : Nat.card (Z₁.comap (QuotientGroup.mk' M)) = Nat.card M * Nat.card Z₁ :=
      QuotientGroup.card_preimage_mk M Z₁
    have hc : Z₁.comap (QuotientGroup.mk' M) = K₀ := by
      rw [hZ₁, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hMK]
    rwa [hc] at h
  have hZ2 : IsPGroup 2 (Subgroup.center (L ⧸ M)) := by
    have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.center (L ⧸ M)) → r = 2 := by
      intro r hr hrd
      by_contra hr2
      have : Fact r.Prime := ⟨hr⟩
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (L ⧸ M)) r hrd
      have hzc : (z : L ⧸ M) ∈ Subgroup.center (L ⧸ M) := z.2
      have hzo : orderOf (z : L ⧸ M) = r := by rw [Subgroup.orderOf_coe]; exact hz
      have : (Subgroup.zpowers (z : L ⧸ M)).Normal := zpowers_normal_of_mem_center hzc
      set P := (Subgroup.zpowers (z : L ⧸ M)).comap π with hP
      have hPn : P.Normal := Subgroup.Normal.comap inferInstance π
      have hPc : Nat.card P = Nat.card M * r := by
        have h : Nat.card ((Subgroup.zpowers (z : L ⧸ M)).comap (QuotientGroup.mk' M)) =
            Nat.card M * Nat.card (Subgroup.zpowers (z : L ⧸ M)) :=
          QuotientGroup.card_preimage_mk M ((Subgroup.zpowers (z : L ⧸ M) : Set (L ⧸ M)))
        rw [hP, hπ, h, Nat.card_zpowers, hzo]
      have hrodd : Odd r := hr.odd_of_ne_two hr2
      have hPo : Odd (Nat.card P) := by rw [hPc]; exact hModd.mul hrodd
      have hPM : P ≤ M := le_sSup ⟨hPn, hPo⟩
      obtain ⟨g, hgz⟩ := hπs (z : L ⧸ M)
      have hg : g ∈ P := by
        rw [hP, Subgroup.mem_comap, hgz]
        exact Subgroup.mem_zpowers _
      have h1 : π g = 1 := (QuotientGroup.eq_one_iff _).mpr (hPM hg)
      rw [← hgz, h1, orderOf_one] at hzo
      exact hr.one_lt.ne hzo
    have hne : Nat.card (Subgroup.center (L ⧸ M)) ≠ 0 := Nat.card_pos.ne'
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hne
      (fun {d} hd hdd => hprime d hd hdd))
  have hZnt : Nontrivial (Subgroup.center (L ⧸ M)) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have h1 : Nat.card Z₁ = 1 := by rw [← hZeq, hbot, Subgroup.card_bot]
    rw [h1, mul_one] at hcardK
    have hdvd : Nat.card T ∣ Nat.card K₀ := Subgroup.card_dvd_of_le (le_centerPre T)
    rw [hcardK] at hdvd
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hModd hdvd)) hTe
  exact ⟨hq, hZ2, hZnt, ⟨(QuotientGroup.quotientMulEquivOfEq hZeq).trans e₁⟩⟩

end General

variable {G : Type} [Group G] [Finite G]

theorem theta_commutator_le_oddCore (h45 : Sec4.Item4_5) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) :
    ⁅aschbacherSolvableCore 3 L, (⊤ : Subgroup L)⁆ ≤ CFSG.oddCore L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hTs, hTch, -, -, -, -, -⟩ := solvable_prime_complement_core_characterization
    (H := L) Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  have hTn : T.Normal := Subgroup.normal_of_characteristic T
  set N : Subgroup L := (CFSG.pPrimeCore 2 T).map T.subtype with hN
  have hNn : N.Normal := inferInstance
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective T.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hNM : N ≤ CFSG.oddCore L := le_sSup ⟨hNn, hNodd⟩
  set TG : Subgroup G := T.map L.subtype with hTG
  have hAT : A ≤ Subgroup.normalizer (TG : Set G) :=
    hAL.trans (SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic L T)
  have hodd := hpair.mem_S.2.1 c hcA hc1
  have hTθ : TG ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) :=
    theta_le_theta_centralizer hLc
  have hSodd : Odd (Nat.card (⁅TG, A⁆ : Subgroup G)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hTθ le_rfl))
  have hSle : ⁅TG, A⁆ ≤ TG := Subgroup.le_normalizer_iff_commutator_le_left.mp hAT
  have hTSn : TG ≤ Subgroup.normalizer ((⁅TG, A⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left TG A
  set S' : Subgroup T := ((⁅TG, A⁆ : Subgroup G).comap L.subtype).comap T.subtype with hS'
  have hS'n : S'.Normal := by
    constructor
    intro s hs t
    rw [hS', Subgroup.mem_comap, Subgroup.mem_comap] at hs ⊢
    have ht : ((t : L) : G) ∈ TG := ⟨t, t.2, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hTSn ht) _).mp hs
    simpa using this
  have hS'odd : Odd (Nat.card S') := by
    have hinj : Function.Injective (L.subtype.comp T.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    rw [← Subgroup.card_map_of_injective hinj]
    refine Odd.of_dvd_nat hSodd (Subgroup.card_dvd_of_le ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  have hS'le : S' ≤ CFSG.pPrimeCore 2 T := le_sSup ⟨hS'n, Nat.coprime_two_left.mpr hS'odd⟩
  set φ : ∀ a : G, a ∈ A → MulAut L := fun a ha => L.normalizerMonoidHom ⟨a, hAL ha⟩ with hφ
  have hφapply : ∀ (a : G) (ha : a ∈ A) (l : L), ((φ a ha l : L) : G) = a * l * a⁻¹ :=
    fun a ha l => rfl
  have hφT : ∀ (a : G) (ha : a ∈ A) (t : L), t ∈ T → φ a ha t ∈ T := by
    intro a ha t ht
    have h1 : a * (t : G) * a⁻¹ ∈ TG :=
      (Subgroup.mem_normalizer_iff.mp (hAT ha) _).mp ⟨t, ht, rfl⟩
    obtain ⟨t', ht', he⟩ := h1
    have : t' = φ a ha t := Subtype.ext (by rw [hφapply a ha]; exact he)
    rw [← this]
    exact ht'
  have hφN : ∀ (a : G) (ha : a ∈ A) (t : L), t ∈ T → φ a ha t * t⁻¹ ∈ N := by
    intro a ha t ht
    have hmem : (⟨φ a ha t * t⁻¹, T.mul_mem (hφT a ha t ht) (T.inv_mem ht)⟩ : T) ∈ S' := by
      rw [hS', Subgroup.mem_comap, Subgroup.mem_comap]
      change ((φ a ha t : L) : G) * ((t : L) : G)⁻¹ ∈ ⁅TG, A⁆
      rw [hφapply a ha, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ha ⟨t, ht, rfl⟩
    exact ⟨_, hS'le hmem, rfl⟩
  set πN := QuotientGroup.mk' N with hπN
  have hTNn : (T.map πN).Normal := Subgroup.Normal.map hTn πN (QuotientGroup.mk'_surjective N)
  set C : Subgroup L := (Subgroup.centralizer ((T.map πN : Subgroup (L ⧸ N)) : Set (L ⧸ N))).comap
    πN with hC
  have hCn : C.Normal := Subgroup.Normal.comap Subgroup.normal_centralizer πN
  have hLAC : ∀ (l : L) (a : G) (ha : a ∈ A), l⁻¹ * φ a ha l ∈ C := by
    intro l a ha
    rw [hC, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have hfix : ∀ s : L, s ∈ T → πN (φ a ha s) = πN s := by
      intro s hs
      have h0 : πN (φ a ha s * s⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr (hφN a ha s hs)
      rwa [map_mul, map_inv, mul_inv_eq_one] at h0
    have h1 : πN (φ a ha t) = πN t := hfix t ht
    have hlt : l * t * l⁻¹ ∈ T := hTn.conj_mem t ht l
    have h2 : πN (φ a ha l) * πN t * (πN (φ a ha l))⁻¹ = πN l * πN t * (πN l)⁻¹ := by
      have h3 := hfix _ hlt
      have e1 : φ a ha (l * t * l⁻¹) = φ a ha l * φ a ha t * (φ a ha l)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [e1, map_mul, map_mul, map_inv, h1, map_mul, map_mul, map_inv] at h3
      exact h3
    rw [map_mul, map_inv]
    set u := πN t
    set a' := πN l
    set b' := πN (φ a ha l)
    calc u * (a'⁻¹ * b') = a'⁻¹ * (a' * u * a'⁻¹) * b' := by group
      _ = a'⁻¹ * (b' * u * b'⁻¹) * b' := by rw [h2]
      _ = a'⁻¹ * b' * u := by group
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have : Group.IsPerfect (lBar L) := hLq.1
  have hCK : ¬ C ≤ K₀ := by
    intro hCK
    have hσ : ∀ (a : G) (ha : a ∈ A), ∀ l : L,
        (((φ a ha l : L) : lBar L)) = (l : lBar L) := by
      intro a ha
      set σ := Sec4.thetaQuotMulAut L (φ a ha) with hσ
      have hid :=
        CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        σ.toMonoidHom (by
          intro z
          obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
          change ((l : lBar L))⁻¹ * σ (l : lBar L) ∈ Subgroup.center (lBar L)
          rw [hσ, Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          exact hCK (hLAC l a ha))
      intro l
      have := congrArg (fun ψ : lBar L →* lBar L => ψ (l : lBar L)) hid
      simpa [hσ, Sec4.thetaQuotMulAut_mk] using this
    obtain ⟨E', -, hE'A, hLE'⟩ := mem_lZeroUnion_iff.mp hpairs.2.2.1.2.1
    obtain ⟨-, U', hU', hnot⟩ := hLE'
    apply hnot
    rw [Subgroup.commutator_le]
    intro u hu e he
    have hul : u ∈ L := hU'.1 hu
    have h := hσ e (hE'A he) ⟨u, hul⟩⁻¹
    rw [eq_comm, QuotientGroup.eq] at h
    refine ⟨_, h, ?_⟩
    simp [hφapply, commutatorElement_def, mul_assoc]
  have hCtop : C = ⊤ := Sec4.Census.eq_top_of_not_le hK₀s hCK
  refine le_trans ?_ hNM
  rw [Subgroup.commutator_le]
  intro t ht l _
  have hl : l ∈ C := hCtop ▸ Subgroup.mem_top l
  rw [hC, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hl
  have h1 := hl (πN t) ⟨t, ht, rfl⟩
  have h2 : πN ⁅t, l⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1
  exact (QuotientGroup.eq_one_iff _).mp h2

end Item21Early3Proof

end CFSG.RankThree.PartTwo.Sec21
