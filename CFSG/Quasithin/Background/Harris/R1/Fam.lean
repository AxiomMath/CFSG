module

public import CFSG.Quasithin.Background.Harris.R1.AutBound
public import CFSG.Quasithin.Background.Harris.R1.Assembly
public import CFSG.Quasithin.Background.Harris.R1.GramAbel
public import CFSG.Quasithin.Background.Harris.R1.AbelIndexMain

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.LieType.BorelTits
  CFSG.GH74.Uniqueness.Bender

section Abstract


variable {H K : Type} [Group H] [Group K]

theorem mem_normalizer_of_map (Qs : Sylow 2 H) (ψ : H →* K)
    (hY : ψ.ker ≤ Subgroup.normalizer ((Qs : Subgroup H) : Set H)) {h : H}
    (hh : ψ h ∈ Subgroup.normalizer (((Qs : Subgroup H).map ψ : Subgroup K) : Set K)) :
    h ∈ Subgroup.normalizer ((Qs : Subgroup H) : Set H) := by
  refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
  have hR : ((h • Qs : Sylow 2 H) : Subgroup H) ≤
      Subgroup.normalizer ((Qs : Subgroup H) : Set H) := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have hq' : ψ (MulAut.conj h q) ∈ (Qs : Subgroup H).map ψ := by
      have := (Subgroup.mem_normalizer_iff.mp hh (ψ q)).mp ⟨q, hq, rfl⟩
      simpa using this
    obtain ⟨q', hq', hqq'⟩ := hq'
    have hk : q'⁻¹ * MulAut.conj h q ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqq', inv_mul_cancel]
    have hn := hY hk
    have hq'n : q' ∈ Subgroup.normalizer ((Qs : Subgroup H) : Set H) :=
      Subgroup.le_normalizer hq'
    have := Subgroup.mul_mem _ hq'n hn
    simpa using this
  have hle : ((h • Qs : Sylow 2 H) : Subgroup H) ≤ (Qs : Subgroup H) := by
    have := (h • Qs).isPGroup'.inf_normalizer_sylow Qs
    intro x hx
    have hx' : x ∈ ((h • Qs : Sylow 2 H) : Subgroup H) ⊓ Subgroup.normalizer (Qs : Set H) := ⟨hx, hR hx⟩
    rw [this] at hx'
    exact hx'.2
  exact Sylow.ext ((h • Qs).is_maximal' Qs.isPGroup' hle).symm

theorem exists_action [Finite H]
    (Qs : Sylow 2 H) (ψ : H →* K) (hψ : Function.Surjective ψ)
    (hY : ψ.ker ≤ Subgroup.normalizer ((Qs : Subgroup H) : Set H))
    {n i e : ℕ} (hB : BenderType K n i e) :
    ∃ (Ω : Type) (_ : Fintype Ω) (act : H →* Equiv.Perm Ω) (pt : Ω),
      (∀ ω, ∃ h, act h pt = ω) ∧
      (∀ h, act h pt = pt ↔ h ∈ Subgroup.normalizer ((Qs : Subgroup H) : Set H)) ∧
      (∀ {a b c d : Ω}, a ≠ b → c ≠ d → ∃ h, act h a = c ∧ act h b = d) ∧
      Fintype.card Ω = (2 ^ n) ^ i + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Finite.of_surjective ψ hψ
  let Qt : Sylow 2 K := Qs.mapSurjective hψ
  obtain ⟨t, hcore⟩ := hB.exists_benderCore Qt
  have hQt : (Qt : Subgroup K) = (Qs : Subgroup H).map ψ := rfl
  let Ω := K ⧸ borel (Qt : Subgroup K)
  let _ : Fintype Ω := Fintype.ofFinite Ω
  refine ⟨Ω, inferInstance, (MulAction.toPermHom K Ω).comp ψ, ((1 : K) : Ω), ?_, ?_, ?_, ?_⟩
  · intro ω
    induction ω using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨h, rfl⟩ := hψ k
      exact ⟨h, by simp [Ω]⟩
  · intro h
    have e1 : ((MulAction.toPermHom K Ω).comp ψ) h ((1 : K) : Ω) = ((1 : K) : Ω) ↔
        ψ h ∈ borel (Qt : Subgroup K) := by
      show ((ψ h • ((1 : K) : Ω)) = ((1 : K) : Ω)) ↔ _
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simp
    rw [e1]
    constructor
    · intro hh
      refine mem_normalizer_of_map Qs ψ hY ?_
      rw [← hQt]; exact hh
    · intro hh
      have : ψ h ∈ Subgroup.normalizer (((Qs : Subgroup H).map ψ : Subgroup K) : Set K) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · rintro ⟨q, hq, rfl⟩
          have := (Subgroup.mem_normalizer_iff.mp hh q).mp hq
          exact ⟨_, this, by simp⟩
        · rintro ⟨q, hq, hqx⟩
          have hq2 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hh) q).mp hq
          rw [inv_inv] at hq2
          refine ⟨h⁻¹ * q * h, hq2, ?_⟩
          have : x = (ψ h)⁻¹ * (ψ h * x * (ψ h)⁻¹) * ψ h := by group
          rw [this, ← hqx]; simp
      rw [← hQt] at this; exact this
  · intro a b c d hab hcd
    have h2 := hcore.isMultiplyPretransitive
    rw [MulAction.is_two_pretransitive_iff] at h2
    obtain ⟨k, hk1, hk2⟩ := h2 hab hcd
    obtain ⟨h, rfl⟩ := hψ k
    exact ⟨h, hk1, hk2⟩
  · rw [← Nat.card_eq_fintype_card]
    exact hcore.index_eq


end Abstract

section Action

variable {G : Type} [Group G] [Finite G] {K1 S : Subgroup G}

omit [Finite G] in
theorem mem_borelOf_iff_mem_normalizer (k : ↥K1) :
    (k : G) ∈ borelOf K1 S ↔
      k ∈ Subgroup.normalizer (((S ⊓ K1).subgroupOf K1 : Subgroup ↥K1) : Set ↥K1) := by
  rw [borelOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨-, hk⟩ x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hk x
  · intro hk
    refine ⟨k.2, fun g => ?_⟩
    constructor
    · intro hg
      have hgK : g ∈ K1 := hg.2
      have := (hk ⟨g, hgK⟩).mp hg
      exact this
    · intro hg
      have hgK : g ∈ K1 := by
        have h1 : (k : G)⁻¹ * ((k : G) * g * (k : G)⁻¹) * (k : G) ∈ K1 :=
          K1.mul_mem (K1.mul_mem (K1.inv_mem k.2) hg.2) k.2
        simpa [mul_assoc] using h1
      exact (hk ⟨g, hgK⟩).mpr hg

theorem exists_famData {K : Type} [Group K]
    (hSyl : IsSylowTwoOf (S ⊓ K1) K1)
    (ψ : OTwoQuot K1 →* K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (OTwoQuot K1)) {n i e : ℕ} (hB : BenderType K n i e) :
    ∃ (Ω : Type) (_ : Fintype Ω) (D : SzR1.FamData K1 S Ω),
      (∀ {a b c d : Ω}, a ≠ b → c ≠ d → ∃ k : ↥K1, D.act k a = c ∧ D.act k b = d) ∧
      Fintype.card Ω = (2 ^ n) ^ i + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ((S ⊓ K1).subgroupOf K1) := hSyl.2.1.comap_subtype
  let Qs : Sylow 2 ↥K1 := hP.toSylow hSyl.2.2
  have hQs : (Qs : Subgroup ↥K1) = (S ⊓ K1).subgroupOf K1 := rfl
  let π : ↥K1 →* OTwoQuot K1 := QuotientGroup.mk' _
  have hO2 : CFSG.Open.pCore 2 ↥K1 ≤ (Qs : Subgroup ↥K1) := by
    intro x hx
    rw [hQs, Subgroup.mem_subgroupOf]
    exact isSylowTwoOf_pCoreOf_le hSyl ⟨x, hx, rfl⟩
  have hconj : ∀ y ∈ (ψ.comp π).ker, ∀ q ∈ (Qs : Subgroup ↥K1), y * q * y⁻¹ ∈ (Qs : Subgroup ↥K1) := by
    intro y hy q hq
    have hc : π y ∈ Subgroup.center (OTwoQuot K1) := hker hy
    have h1 : π (y * q * y⁻¹) = π q := by
      rw [map_mul, map_mul, map_inv]
      have := Subgroup.mem_center_iff.mp hc (π q)
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have h2 : (y * q * y⁻¹)⁻¹ * q ∈ CFSG.Open.pCore 2 ↥K1 := QuotientGroup.eq.mp h1
    have h3 := hO2 h2
    have e : y * q * y⁻¹ = q * ((y * q * y⁻¹)⁻¹ * q)⁻¹ := by group
    rw [e]
    exact Qs.mul_mem hq (Qs.inv_mem h3)
  have hY : (ψ.comp π).ker ≤ Subgroup.normalizer ((Qs : Subgroup ↥K1) : Set ↥K1) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hconj y hy x hx, fun hx => by
      have := hconj y⁻¹ ((ψ.comp π).ker.inv_mem hy) _ hx
      simpa [mul_assoc] using this⟩
  obtain ⟨Ω, fin, act, pt, htr, hst, h2, hcard⟩ :=
    exists_action Qs (ψ.comp π) (hψ.comp (QuotientGroup.mk'_surjective _)) hY hB
  refine ⟨Ω, fin, ⟨act, pt, htr, fun k => ?_⟩, h2, hcard⟩
  rw [hst, mem_borelOf_iff_mem_normalizer]
  rfl

end Action

section Main

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem commutator_vBeta_eq (h : R1SettingLegacyBare K1 L2 S Zs)
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = Zs := by
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hS := F112J2.isNaturalS3_of_setting hRO h
  have hb := F112J2.critDist_eq_two_of_setting hRO h hna
  have hcard : Nat.card ↥(conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G)) = 2 :=
    F112W.card_inf_centralizer_T hyp hS
  have hle : Zs ≤ conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) :=
    le_inf (le_conjClosure Zs L2) h.Z_cent_S
  have hZ : conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) = Zs :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_Z])).symm
  have hN : K1 ⊔ S ≤ Subgroup.normalizer
      ((conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
    rw [hZ]
    exact (sup_le h.K1_cent_Z (F112J2.S_le_centralizer_Z h)).trans
      (Subgroup.centralizer_le_normalizer _)
  exact (F112W.commutator_conjClosure_self hyp hS hb hN).trans hZ

theorem odd_pow_add_one {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) : Odd ((2 ^ n) ^ i + 1) := by
  have : Even ((2 ^ n) ^ i) := by
    rw [← pow_mul]
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩)
  exact this.add_one

theorem famStmt_holds : FamStmt := by
  intro G _ _ K1 L2 S Zs h n hn hX hna
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  have hR := F112J2.hyp111R_of_setting hRO h
  have hcomm := commutator_vBeta_eq h hna
  have hSyl : IsSylowTwoOf (S ⊓ K1) K1 := h.hyp.h1.sylow
  have key : ∃ (Ω : Type) (_ : Fintype Ω) (D : SzR1.FamData K1 S Ω),
      (∀ {a b c d : Ω}, a ≠ b → c ≠ d → ∃ k : ↥K1, D.act k a = c ∧ D.act k b = d) ∧
      Odd (Fintype.card Ω) ∧
      (IsL2Quot n (OTwoQuot K1) → Fintype.card Ω = 2 ^ n + 1) ∧
      (¬ IsL2Quot n (OTwoQuot K1) → (2 ^ n) ^ 2 + 1 ≤ Fintype.card Ω) := by
    by_cases hL : IsL2Quot n (OTwoQuot K1)
    · obtain ⟨e⟩ := hL
      obtain ⟨Ω, fin, D, h2, hcard⟩ := exists_famData (S := S) hSyl (MonoidHom.id _)
        Function.surjective_id (by simp) (BenderType.linear n hn e)
      refine ⟨Ω, fin, D, h2, ?_, fun _ => by simpa using hcard, fun hh => (hh ⟨e⟩).elim⟩
      rw [hcard]; exact odd_pow_add_one (by omega) le_rfl
    · have hcase : ∃ (K : Type) (_ : Group K) (ψ : OTwoQuot K1 →* K) (e i : ℕ),
          Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center (OTwoQuot K1) ∧
          BenderType K n i e ∧ 2 ≤ i := by
        rcases hX with ⟨e⟩ | ⟨a, rfl, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
        · exact (hL e).elim
        · exact ⟨OTwoQuot K1, inferInstance, MonoidHom.id _, 1, 2, Function.surjective_id,
            by simp,
            BenderType.suzuki a (by omega)
              (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)), le_rfl⟩
        · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
          refine ⟨StatedProj (StatedSU 3 (2 ^ n) F), inferInstance,
            (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))).comp
              e.toMonoidHom, e', 3, (QuotientGroup.mk'_surjective _).comp e.surjective, ?_, hB,
            by omega⟩
          intro x hx
          have hx' : e x ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) :=
            (QuotientGroup.eq_one_iff (e x)).mp (MonoidHom.mem_ker.mp hx)
          have hc : e x ∈ Subgroup.center (StatedSU 3 (2 ^ n) F) := statedSU_scalars_le_center hx'
          rw [Subgroup.mem_center_iff] at hc ⊢
          intro g
          apply e.injective
          rw [map_mul, map_mul]
          exact hc (e g)
        · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
          exact ⟨_, inferInstance, e.toMonoidHom, e', 3, e.surjective, by
            intro x hx
            have : x = 1 := e.injective (by simpa using hx)
            rw [this]; exact Subgroup.one_mem _, hB, by omega⟩
      obtain ⟨K, _, ψ, e, i, hψ, hker, hB, hi⟩ := hcase
      obtain ⟨Ω, fin, D, h2, hcard⟩ := exists_famData (S := S) hSyl ψ hψ hker hB
      refine ⟨Ω, fin, D, h2, ?_, fun hh => (hL hh).elim, fun _ => ?_⟩
      · rw [hcard]; exact odd_pow_add_one (by omega) (by omega)
      · rw [hcard]
        have : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ i := Nat.pow_le_pow_right (by positivity) hi
        omega
  obtain ⟨Ω, fin, D, h2, hodd, c1, c2⟩ := key
  exact ⟨Ω, fin, ⟨h, hR, D, h2, hcomm⟩, hodd, c1, c2⟩

theorem nonab_holds : NonabStmt :=
    nonab_of gramAbel_holds abelIndex_holds famStmt_holds autBound_holds

end Main

end CFSG.Quasithin.Background.Harris.R1
