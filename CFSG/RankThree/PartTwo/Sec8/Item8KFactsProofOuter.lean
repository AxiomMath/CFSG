module

public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofField
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2Two
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9
import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Open
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item8KFactsOuter

theorem mk_eq_one_of_mem_theta {G : Type} [Group G] [Finite G] {L K : Subgroup G} (hKL : K ≤ L)
    (hθ : NoThetaNormal (imageModTheta L K)) {t : K}
    (ht : t ∈ aschbacherSolvableCore 3 K) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hKL t) = 1 := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ : K →* imageModTheta L K :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL)).codRestrict
      (imageModTheta L K) (fun k => ⟨Subgroup.inclusion hKL k,
        Subgroup.mem_subgroupOf.mpr k.2, rfl⟩) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact ⟨⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩, rfl⟩
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 K).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := hθ M hMn hMs hM3
  have : ρ t ∈ M := Subgroup.mem_map_of_mem ρ ht
  rw [hM1, Subgroup.mem_bot, Subtype.ext_iff] at this
  exact this

theorem inducesOuterTheta_mul_inv_of_mem {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {a k' : G} (ha : Sec4.InducesOuterTheta a L) (hk'L : k' ∈ L) :
    Sec4.InducesOuterTheta (a * k'⁻¹) L := by
  obtain ⟨haN, hout⟩ := ha
  have hk'N : k' ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hk'L
  have ha'N : a * k'⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ haN (Subgroup.inv_mem _ hk'N)
  refine ⟨ha'N, fun hin => hout ?_⟩
  obtain ⟨z, hz⟩ := hin
  have hsplit : (⟨a * k'⁻¹, ha'N⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨a, haN⟩ * (⟨k', hk'N⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
  rw [hsplit, map_mul, map_mul, map_inv, map_inv, KFacts.thetaQuotMulAut_compAction_of_mem hk'L
    hk'N] at hz
  refine ⟨z * QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨k', hk'L⟩, ?_⟩
  rw [map_mul, hz]
  group

theorem not_mem_inndiag_mul_inv {M N : Type*} [Group M] [Group N] {P : KFacts.PinnedAut N}
    (hsep : P.Separated) (Φ : MulAut M →* MulAut N) (hΦ : ∀ y : M, Φ (MulAut.conj y) ∈ P.inndiag)
    {α : MulAut M} (hα : P.IsField (Φ α)) (y : M) : Φ (α * (MulAut.conj y)⁻¹) ∉ P.inndiag := by
  intro hmem
  apply hsep.not_mem_inndiag_of_isField hα
  have h : Φ α = Φ (α * (MulAut.conj y)⁻¹) * Φ (MulAut.conj y) := by
    rw [← map_mul]
    group
  rw [h]
  exact mul_mem hmem (hΦ y)

theorem exists_twist_of_not_outer {G : Type} [Group G] [Finite G] {L : Subgroup G} {a d : G}
    {n : ℕ} (hn1 : 1 ≤ n) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (haK : a ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) : Set G))
    (ha3 : a ^ 3 = 1)
    (eK : imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n)))
    (hnot : ¬ Sec4.InducesOuterTheta a
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))) :
    ∃ k' : G, k' ∈ L ∧ k' * a = a * k' ∧ k' ^ 3 = 1 ∧
      imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≤
        barCentralizer (Subgroup.zpowers (a * k'⁻¹)) L := by
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  set τ := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) with hτ
  have hin : τ ∈ (MulAut.conj : K ⧸ aschbacherSolvableCore 3 K →*
      MulAut (K ⧸ aschbacherSolvableCore 3 K)).range := by
    by_contra hc
    exact hnot ⟨haK, hc⟩
  obtain ⟨k, hk⟩ := hin
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_psl2 hn1 eK
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd eQ.symm (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  have hkfix : k ∈ barCentralizer (Subgroup.zpowers a) K := by
    rw [KFacts.mem_barCentralizer_zpowers_iff haK, ← hτ, ← hk]
    simp
  have hτ3 : τ ^ 3 = 1 := by
    have h1 : (⟨a, haK⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact ha3)
    rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hk3 : k ^ 3 = 1 := by
    have h1 : MulAut.conj (k ^ 3) = 1 := by rw [map_pow, hk, hτ3]
    have h2 : k ^ 3 ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (K ⧸ aschbacherSolvableCore 3 K) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * k ^ 3 = k ^ 3 * g * (k ^ 3)⁻¹ * k ^ 3 := by rw [this]
        _ = k ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hkp : ∀ y ∈ Subgroup.zpowers k, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk3, one_zpow]
  obtain ⟨E, hEK, hEa, -, himg, -, hinj⟩ := KFacts.exists_lift_of_le_barCentralizer (L := K) haK
    ⟨1, by rw [pow_one]; exact ha3⟩ (Item8KFactsProof.isPGroup_of_pow_three hkp)
    ((Subgroup.zpowers_le).mpr hkfix)
  have hkE : k ∈ imageModTheta K E := by
    rw [himg]
    exact Subgroup.mem_zpowers k
  obtain ⟨x, hxE, hxk⟩ := hkE
  have hxE' : ((x : K) : G) ∈ E := Subgroup.mem_subgroupOf.mp hxE
  set k' : G := ((x : K) : G) with hk'
  have hk'L : k' ∈ L := hKL x.2
  have hk'a : k' * a = a * k' := by
    have := hEa hxE'
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hk'3 : k' ^ 3 = 1 := by
    have h1 : ((x ^ 3 : K) : G) ∈ E := by
      rw [SubgroupClass.coe_pow]
      exact pow_mem hxE' 3
    have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (x ^ 3) = 1 := by
      rw [map_pow, hxk, hk3]
    have h3 := hinj (x ^ 3) h1 h2
    rw [hk', ← SubgroupClass.coe_pow, h3, OneMemClass.coe_one]
  refine ⟨k', hk'L, hk'a, hk'3, ?_⟩
  have ha'N : a * k'⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ haL (Subgroup.inv_mem _ (Subgroup.le_normalizer hk'L))
  have hθ : NoThetaNormal (imageModTheta L K) :=
    Item87Proof.NoThetaNormal.of_mulEquiv eK (Item87Proof.noThetaNormal_projSL_two (by omega))
  rintro _ ⟨w, hw, rfl⟩
  have hyK : (w : G) ∈ K := Subgroup.mem_subgroupOf.mp hw
  rw [KFacts.mem_barCentralizer_zpowers_iff ha'N, QuotientGroup.mk'_apply,
    Sec4.thetaQuotMulAut_mk]
  have hconj : ∀ z : K, QuotientGroup.mk' (aschbacherSolvableCore 3 K)
      (Sec4.compAction K ⟨a, haK⟩ z) =
      k * QuotientGroup.mk' (aschbacherSolvableCore 3 K) z * k⁻¹ := by
    intro z
    have := congrArg (fun φ : MulAut (K ⧸ aschbacherSolvableCore 3 K) =>
      φ (QuotientGroup.mk' (aschbacherSolvableCore 3 K) z)) hk
    simp only [MulAut.conj_apply] at this
    rw [this, hτ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  set w' : K := x⁻¹ * ⟨(w : G), hyK⟩ * x with hw'
  have h1 := hconj w'
  have hmk : QuotientGroup.mk' (aschbacherSolvableCore 3 K) w' =
      k⁻¹ * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨(w : G), hyK⟩ * k := by
    rw [hw', map_mul, map_mul, map_inv, hxk]
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 K)
      (Sec4.compAction K ⟨a, haK⟩ w') =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨(w : G), hyK⟩ := by
    rw [h1, hmk]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
  have h3 := mk_eq_one_of_mem_theta hKL hθ h2
  rw [map_mul, map_mul, map_inv, map_inv] at h3
  have h3' := inv_mul_eq_one.mp h3
  have he1 : Subgroup.inclusion hKL (Sec4.compAction K ⟨a, haK⟩ w') =
      Sec4.compAction L ⟨a * k'⁻¹, ha'N⟩ w := by
    apply Subtype.ext
    change a * (((x : G))⁻¹ * (w : G) * (x : G)) * a⁻¹ =
      (a * k'⁻¹) * (w : G) * (a * k'⁻¹)⁻¹
    rw [hk']
    group
  have he2 : Subgroup.inclusion hKL (⟨(w : G), hyK⟩ : K) = w := Subtype.ext rfl
  rw [he1, he2] at h3'
  exact h3'

theorem false_of_le_of_iso {X : Type} [Group X] [Finite X] {Kb C : Subgroup X} {n : ℕ}
    (hn : Odd n) (hle : Kb ≤ C) (eK : Kb ≃* projSL 2 (GaloisField 2 (3 * n)))
    (hC : IsoGTwoEven C n ∨ IsoPGUThree C (2 ^ n) ∨ IsoSUThree C (2 ^ n) ∨
      Nonempty (C ≃* projSp 2 (GaloisField 2 n))) : False := by
  have hn1 : 1 ≤ n := hn.pos
  have hdvd : Nat.card Kb ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  have h3n : 2 ≤ 3 * n := by omega
  have h3n6 : 3 * n ≠ 6 := by
    obtain ⟨t, rfl⟩ := hn
    omega
  have hU : UnitarySig C n → False :=
    fun hS => false_of_profile_dvd (profile_projSL_two (by omega) eK) hS.profile hdvd h3n
      h3n6 (zA_one_self _) (by
        have h := not_zU_mid (n := 2) (g := n) (t := 1) (Or.inl rfl) le_rfl (by omega)
        rwa [show n * (2 * 1 + 1) = 3 * n by ring] at h)
  rcases hC with ⟨F, _, _, hF, ⟨e⟩⟩ | hPGU | hSU | hSp
  · have hH := kF83IndepGTwo_holds F n hn hF ((Kb.subgroupOf C).map e.toMonoidHom)
    exact hH.false ((((Kb.subgroupOf C).equivMapOfInjective _ e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hle)).trans eK)
  · exact hU (unitarySig_of_isoPGUThree hn1 hPGU)
  · exact hU (unitarySig_of_isoSUThree hn1 hSU)
  · obtain ⟨eC⟩ := hSp
    refine false_of_profile_dvd (profile_projSL_two (by omega) eK) (profile_of_projSp_two hn1 eC)
      hdvd h3n h3n6 (zA_one_self _) ?_
    rw [zBC_two_iff]
    intro h
    have h' : 3 * n ∣ n * 4 - 3 * n := Nat.dvd_sub h dvd_rfl
    exact false_of_dvd_of_lt h' (by omega) (by omega)

end Item8KFactsOuter

open Item8KFactsOuter

namespace Item8KFactsOuter

theorem false_of_twist
    (h47 : Sec4.Inputs47ClassesD4) {G : Type} [Group G] [Finite G] {L : Subgroup G} {a k' : G}
    {n : ℕ} (hn : Odd n)
    (hkind : KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField)
    (ha3 : a ^ 3 = 1) (hk'L : k' ∈ L) (hk'a : k' * a = a * k') (hk'3 : k' ^ 3 = 1)
    {Kb : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (eK : Kb ≃* projSL 2 (GaloisField 2 (3 * n)))
    (hle : Kb ≤ barCentralizer (Subgroup.zpowers (a * k'⁻¹)) L)
    (hL : (IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∨
        IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n)) ∨
      IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * n)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * n)))) :
    False := by
  have hn1 : 1 ≤ n := hn.pos
  have hn0 : n ≠ 0 := by omega
  have haN : a ∈ Subgroup.normalizer (L : Set G) := by
    rcases hkind with hk | hk
    · exact hk.mem_normalizer
    · exact hk.mem_normalizer
  have hout : Sec4.InducesOuterTheta a L := by
    rcases hkind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  have hk'N : k' ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hk'L
  have ha'N : a * k'⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ haN (Subgroup.inv_mem _ hk'N)
  have ha'3 : (a * k'⁻¹) ^ 3 = 1 := by
    have hc : Commute a k'⁻¹ := (Commute.symm hk'a).inv_right
    rw [hc.mul_pow, ha3, inv_pow, hk'3, inv_one, one_mul]
  have hout' : Sec4.InducesOuterTheta (a * k'⁻¹) L :=
    inducesOuterTheta_mul_inv_of_mem hout hk'L
  have hsplit : (⟨a * k'⁻¹, ha'N⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨a, haN⟩ * (⟨k', hk'N⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
  have hind : ∀ {M : Type} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M),
      KFacts.inducedAutHom L e ⟨a * k'⁻¹, ha'N⟩ = KFacts.inducedAutHom L e ⟨a, haN⟩ *
        (MulAut.conj (e (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨k', hk'L⟩)))⁻¹ := by
    intro M _ e
    rw [hsplit, map_mul, map_inv, KFacts.inducedAutHom_eq_conj_of_mem e hk'L hk'N]
  have h3n : 2 ^ (3 * n) % 3 = 2 :=
    Sec8.Item8KFactsProof.two_pow_mod_three_of_odd (Odd.mul (by decide) hn)
  refine false_of_le_of_iso hn hle eK ?_
  rcases hL with hLt | hLSU | hLU | hLSp
  · rcases hLt with hD4 | ⟨F, _, _, hF, ⟨e⟩⟩
    ·
      obtain ⟨q, hv, hq2, hqe, ⟨e₁⟩⟩ := hD4
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hK : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ TwistTag.D4.order := by
        rw [GaloisField.card 2 (3 * n) (by omega), ← pow_mul, mul_comm]
        rfl
      obtain ⟨σ, hσ, -, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hn1
        (GaloisField 2 (3 * n)) hK
      have hKq : Nat.card (GaloisField 2 (3 * n)) = q.card ^ TwistTag.D4.order := by
        rw [TauCeti.PrimePower.card_def, hq2, hqe]
        exact hK
      obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 _ hKq
        σ.toRingHom (fun x => by rw [TauCeti.PrimePower.card_def, hq2, hqe]; exact hσ x)
      have e₃ := CFSG.TauCetiBridge.Twisted.nativeEquiv (t := TwistTag.D4)
        (σ := σ.toRingHom) Nat.prime_two hn1 hK hσ
      set e := e₁.trans (e₂.symm.trans e₃) with he
      have hK3 : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ 3 := hK
      set α := KFacts.inducedAutHom L e ⟨a * k'⁻¹, ha'N⟩ with hα
      have hα3 : α ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L e ha'N ha'3
      have hαin : ¬ KFacts.IsInnerAut α :=
        (KFacts.not_isInnerAut_inducedAutHom_iff L e ha'N).mpr hout'
      rcases h47 n hn _ σ hK3 hσ α hα3 hαin with ⟨β, hβ⟩ | ⟨γ, y, -, -, -, -, hPGU⟩
      · exact Or.inl (KFacts.isoGTwoEven_barCentralizer_of_conj_fieldActor hn1 hK3 hσ e ha'N β hβ)
      · refine Or.inr (Or.inl ?_)
        obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := hPGU
        have hbar := Sec4.barCentralizer_zpowers_eq_autFix ha'N
        have hαe : α = MulAut.congr e
            (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a * k'⁻¹, ha'N⟩)) :=
          KFacts.inducedAutHom_apply L e _
        exact ⟨F, inferInstance, inferInstance, hF, ⟨(MulEquiv.subgroupCongr hbar).trans
          ((Sec4.autFixCongrEquiv e _).symm.trans
            ((MulEquiv.subgroupCongr (congrArg Sec4.autFix hαe)).symm.trans φ))⟩⟩
    ·
      obtain ⟨-, k, _, _, hk, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_g2 hn0 hF ha'3 hout' e
      exact Or.inl ⟨k, inferInstance, inferInstance, hk, ⟨ι⟩⟩
  ·
    have hm3 : 3 ≤ 3 * n := by omega
    have hm3' : 3 ∣ 2 ^ (3 * n) + 1 := by omega
    have hkf : KFacts.InducesStdKind L a .field := by
      rcases hkind with hk | hk
      · exact hk
      · exact (KFacts.not_inducesStdKind_graphField_of_isoSUThree hm3 hm3' hLSU hk).elim
    obtain ⟨K₁, _, h₁, hq₁, e₁, hN₁, hk₁⟩ :=
      KFacts.inducesKindSU3_of_inducesStdKind hm3 hm3' hLSU hkf
    set Φ : MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (3 * n) K₁ 3) →*
        MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h₁ 3) :=
      (MulAut.congr (KFacts.suCenterEquiv h₁ hq₁)).toMonoidHom.comp (KFacts.centerDescend _)
      with hΦ
    have hΦconj : ∀ y, Φ (MulAut.conj y) ∈ (KFacts.stdPinnedPSU3 h₁).inndiag := by
      intro y
      apply (KFacts.stdPinnedPSU3 h₁).inn_le
      refine ⟨KFacts.suCenterEquiv h₁ hq₁ (y : _ ⧸ Subgroup.center _), ?_⟩
      rw [hΦ, MonoidHom.comp_apply, KFacts.centerDescend_conj, MulEquiv.coe_toMonoidHom,
        KFacts.congr_mulAutConj]
    have hsep := KFacts.stdPinnedPSU3_separated (h := h₁)
    have hfa : (KFacts.stdPinnedPSU3 h₁).IsField (Φ (KFacts.inducedAutHom L e₁ ⟨a, haN⟩)) := hk₁
    rcases KFacts.inducesKindSU3_inner_or_diagonal_or_field (h := h₁) L hq₁ ha'N ha'3 e₁ with
      hi | hdg | hf
    · exfalso
      have hin : KFacts.IsInnerAut (KFacts.inducedAutHom L e₁ ⟨a * k'⁻¹, ha'N⟩) :=
        (KFacts.isInnerAut_congr_centerDescend_iff h₁ hq₁).mp hi
      exact (KFacts.not_isInnerAut_inducedAutHom_iff L e₁ ha'N).mpr hout' hin
    · exfalso
      apply not_mem_inndiag_mul_inv hsep Φ hΦconj hfa
        (e₁ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨k', hk'L⟩))
      rw [← hind e₁]
      exact hdg.1
    · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoSUThree_barCentralizer_of_field hq₁ ha'3 ⟨e₁, ha'N, hf⟩
      obtain rfl : f₀ = n := by omega
      exact Or.inr (Or.inr (Or.inl hC))
  ·
    obtain ⟨eL⟩ := hLU
    have hmo : Odd (3 * n) := Odd.mul (by decide) hn
    have hm2 : 2 ≤ 3 * n := by omega
    have hU := Sec4.unitaryFieldData_galoisField 2 (3 * n) (by omega)
    have hq2 : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordTwistedA 2 (2 ^ (3 * n)) :=
      (Nat.card_congr eL.toEquiv).trans (KFacts.card_projSU_three_two (by omega))
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd (eL.trans (Sec4.projSUEquivUnitaryPSU 2 _ hU)).symm
        (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
    have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU hm2 eL
    have hkU : ∃ (K₁ : Type) (_ : Field K₁)
        (h₁ : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * n) K₁)
        (_ : 2 < 2 ^ (3 * n)), KFacts.InducesKindPSU3 h₁ L a .field := by
      rcases hkind with hk | hk
      · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo hcard hZ hk with h' | hO
        · exact h'
        · exact (hodd hO).elim
      · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo hcard hZ hk with
          ⟨K₁, _, h₁, -, hk₁⟩ | hO
        · exact (KFacts.not_inducesKindPSU3_graphField h₁ hk₁).elim
        · exact (hodd hO).elim
    obtain ⟨K₁, _, h₁, hq₁, E₁, hN₁, hk₁⟩ := hkU
    have hsep := KFacts.stdPinnedPSU3_separated (h := h₁)
    have hfa : (KFacts.stdPinnedPSU3 h₁).IsField
        ((MonoidHom.id _) (KFacts.inducedAutHom L E₁ ⟨a, haN⟩)) := hk₁
    rcases KFacts.inducesKindPSU3_diagonal_or_field (h := h₁) L hq₁ ha'3 hout' E₁ with
      ⟨hx, hdg⟩ | hf
    · exfalso
      apply not_mem_inndiag_mul_inv hsep (MonoidHom.id _)
        (fun y => (KFacts.stdPinnedPSU3 h₁).inn_le ⟨y, rfl⟩) hfa
        (E₁ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨k', hk'L⟩))
      rw [MonoidHom.id_apply, ← hind E₁]
      exact hdg.1
    · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq₁ ha'3 ⟨E₁, hf⟩
      obtain rfl : f₀ = n := by omega
      exact Or.inr (Or.inl hC)
  ·
    exact Or.inr (Or.inr (Or.inr (KFacts.barCentralizer_mulEquiv_projSp hn0 ha'3 hout' hLSp).2))

end Item8KFactsOuter

theorem kF84OuterL2_of
    (h47 : Sec4.Inputs47ClassesD4) : KF84OuterL2 := by
  intro G _ _ A c L a A₀ d n h hA hd heK
  obtain ⟨eK⟩ := heK
  have hn := hd.odd
  have hn1 : 1 ≤ n := hn.pos
  have ha3 := pow_three_of_data83 hd
  by_contra hnot
  obtain ⟨k', hk'L, hk'a, hk'3, hle⟩ := exists_twist_of_not_outer hn1 h.a_mem_normalizer
    (mem_normalizer_residual_of_data83 h hd) ha3 eK hnot
  have hT := false_of_twist h47 hn h.inducesStdKind ha3 hk'L hk'a hk'3 eK hle
  rcases hd.cases with ⟨hLt, -, -⟩ | ⟨-, -, hSU⟩ | ⟨hLSU, -, -⟩ | ⟨hLU, -, -⟩ | ⟨hLSp, -, -⟩
  · exact hT (Or.inl hLt)
  ·
    have hS := unitarySig_of_isoSUThree (g := 3 * n) (by omega) hSU
    refine false_of_profile_dvd hS.profile (profile_projSL_two (by omega) eK) dvd_rfl
      (k := 6 * (3 * n)) (by omega) (by omega) hS.top ?_
    intro hz
    have := zA_le (by omega) hz
    omega
  · exact hT (Or.inr (Or.inl hLSU))
  · exact hT (Or.inr (Or.inr (Or.inl hLU)))
  · exact hT (Or.inr (Or.inr (Or.inr hLSp)))

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
