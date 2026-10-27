module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4314R
public import CFSG.Quasithin.Vol2.Ch4Sec3L4314Row
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Vol2.Ch4Sec3L4313

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_modO2_modO2Image {H B : Subgroup G} (hBH : B ≤ H) :
    Nonempty (ModO2 (modO2Image H B) ≃* ModO2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set N := CFSG.pCore 2 ↥H with hN
  set Bb := modO2Image H B with hBb
  let φ : ↥B →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hBH)
  have hrange : φ.range = Bb := by
    rw [hBb]
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let φ' : ↥B →* ↥Bb := φ.codRestrict Bb fun b => by
    rw [← hrange]
    exact ⟨b, rfl⟩
  have hφ' : Function.Surjective φ' := by
    rintro ⟨x, hx⟩
    rw [← hrange] at hx
    obtain ⟨b, rfl⟩ := hx
    exact ⟨b, rfl⟩
  have hker2 : IsPGroup 2 φ'.ker := by
    intro x
    have hx : Subgroup.inclusion hBH (x : ↥B) ∈ N := by
      have h1 : φ' x = 1 := x.2
      have h2 : φ (x : ↥B) = 1 := congrArg Subtype.val h1
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (Subgroup.inclusion hBH (x : ↥B)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (Subgroup.inclusion_injective hBH) (by simpa using h1)
  have hMn : (CFSG.pCore 2 ↥Bb).Normal := CFSG.pCore_normal
  let ψ : ↥B →* ModO2 Bb := (QuotientGroup.mk' (CFSG.pCore 2 ↥Bb)).comp φ'
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ'
  have hker : ψ.ker = CFSG.pCore 2 ↥B := by
    apply le_antisymm
    · have hp : IsPGroup 2 ψ.ker := by
        intro x
        have hx : φ' (x : ↥B) ∈ CFSG.pCore 2 ↥Bb := by
          have := x.2
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at this
          exact this
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Bb)) ⟨_, hx⟩
        have hk' : φ' ((x : ↥B) ^ 2 ^ k) = 1 := by
          rw [map_pow]
          exact congrArg Subtype.val hk
        obtain ⟨j, hj⟩ := hker2 ⟨_, hk'⟩
        refine ⟨k + j, Subtype.ext ?_⟩
        have hj' : ((x : ↥B) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [pow_add, pow_mul]
        exact hj'
      exact le_sSup ⟨inferInstance, hp⟩
    · intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have hn : ((CFSG.pCore 2 ↥B).map φ').Normal :=
        (CFSG.pCore_normal : (CFSG.pCore 2 ↥B).Normal).map _ hφ'
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥B).map φ') :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map _
      exact (le_sSup ⟨hn, hp⟩ : (CFSG.pCore 2 ↥B).map φ' ≤ CFSG.pCore 2 ↥Bb) ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem a312SL3Data_modO2Image {H₁ : Subgroup G} (hKH₁ : K ≤ H₁) :
    A312SL3Data (modO2Image H₁ K) m := by
  refine ⟨s.two_le, F, inferInstance, inferInstance, s.card_F, ?_⟩
  obtain ⟨e⟩ := nonempty_modO2_modO2Image hKH₁
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq s.modO2.2.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α s.modO2.1))⟩

theorem pCoreOf_K_ne_bot (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : pCoreOf 2 K ≠ ⊥ := by
  intro h
  apply s.ZS_ne_bot
  rw [eq_bot_iff]
  have hUQ : u4311 I K ≤ q4311 I K := inf_le_left
  have := (s.ZS_le_U.trans hUQ).trans (s.pCoreOf_K_eq h135 hR hC h37 h38 h39).ge
  rwa [h] at this

theorem normalizer_K_le (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Subgroup.normalizer (K : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 K : Set G)) :=
    ⟨_, s.pCoreOf_K_ne_bot h135 hR hC h37 h38 h39, pCoreOf_isPGroup 2 K, rfl⟩
  have hle := normalizer_le_normalizer_pCoreOf 2 K
  have heq := s.sk.base.inM.1.2 _ hloc ((s.H_le_normalizer_K hR hC h37 h38 h39).trans hle)
  rw [heq] at hle
  exact hle

theorem setting432_of_inM {H₁ : Subgroup G} (hH₁ : InM (K ⊔ T ⊓ H) H₁) :
    Setting432 G T M L n I H₁ ∧ T ⊓ H₁ = T ⊓ H := by
  have hKH : K ≤ H := le_of_mem_cComp s.sk.cComp
  have hKH₁ : K ≤ H₁ := le_sup_left.trans hH₁.2
  have hSH₁ : T ⊓ H ≤ H₁ := le_sup_right.trans hH₁.2
  have hIH₁ : I ≤ H₁ := by
    rw [← s.sk.base.sup_pCoreOf]
    exact _root_.sup_le (s.sk.L_le_K.trans hKH₁) (s.sk.base.pCoreOf_le_S.trans hSH₁)
  have hinM₁ : InM I H₁ := ⟨hH₁.1, hIH₁⟩
  have hne₁ : H₁ ≠ M := by
    rintro rfl
    exact s.sk.not_le (le_inf hKH hKH₁)
  have hS₁le : Nat.card ↥(T ⊓ H₁) ≤ Nat.card ↥(T ⊓ H) :=
    s.sk.base.card_S_le I H₁ s.sk.base.cand rfl hinM₁ hne₁
  have hSS₁ : T ⊓ H ≤ T ⊓ H₁ := le_inf inf_le_left hSH₁
  have hSeq : T ⊓ H₁ = T ⊓ H := (Subgroup.eq_of_le_of_card_ge hSS₁ hS₁le).symm
  have hcard : Nat.card ↥(T ⊓ H) ≤ Nat.card ↥(T ⊓ H₁) := by rw [hSeq]
  exact ⟨⟨s.sk.base.hyp, s.sk.base.cand, s.sk.base.card_le, hinM₁, hne₁,
    fun I' H' hI' hc hH' hne' => (s.sk.base.card_S_le I' H' hI' hc hH' hne').trans hcard⟩, hSeq⟩

theorem mem_cComp_of_inM
    (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    {H₁ : Subgroup G} (hH₁ : InM (K ⊔ T ⊓ H) H₁) (hS₁ : IsSylowTwoOf (T ⊓ H) H₁) :
    K ∈ cComp H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH₁ : K ≤ H₁ := le_sup_left.trans hH₁.2
  have hH₁loc : pCoreOf 2 H₁ ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hH₁.1.1
  have hK : K ∈ lFamily (T ⊓ H) :=
    cComp_subset_lFamily le_sup_right (mem_cComp_sup s.sk.cComp s.sk.S_le_normalizer)
  have hyp := s.sk.base.hyp
  obtain ⟨K', hK', hKK'⟩ :=
    lemma_1_2_4_exists hyp.qtke hyp.simple hyp.nonabelian h37 h39 hH₁loc hS₁ hKH₁ hK
  have hlist := lemma_1_2_4_list hyp.qtke hyp.simple hyp.nonabelian h312 hH₁loc hS₁ hKH₁ hK hK'
    hKK'
  have hD := s.a312SL3Data_modO2Image hKH₁
  have hbar : modO2Image H₁ K = modO2Image H₁ K' := by
    rcases hlist with h | h | h
    · exact h
    · exact absurd h (not_a312Case_of_sl3 hD)
    · exact absurd h (not_a312Nonquasi_of_sl3 hD (Subgroup.map_mono fun x hx => hKK' hx))
  have hO₁ : pCoreOf 2 H₁ ≤ K := by
    have h1 : pCoreOf 2 H₁ ≤ T ⊓ H := pCoreOf_two_le_of_isSylowTwoOf hS₁
    have h2 : pCoreOf 2 H₁ ≤ pCoreOf 2 (K ⊔ T ⊓ H) :=
      le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (hH₁.2.trans (le_normalizer_pCoreOf 2 H₁)) (pCoreOf_isPGroup 2 H₁)
    rw [s.pCoreOf_sup_eq h135 hR hC h37 h38 h39] at h2
    exact h2.trans s.q4311_le_K
  have hK'H₁ : K' ≤ H₁ := le_of_mem_cComp hK'
  have hK'K : K' ≤ K := by
    intro x hx
    have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥H₁) ⟨x, hK'H₁ hx⟩ ∈ modO2Image H₁ K := by
      rw [hbar]
      exact ⟨⟨x, hK'H₁ hx⟩, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hxb
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hzx
    have hq : (z : G)⁻¹ * x ∈ K := hO₁ ((mem_pCoreOf_iff' _).mpr hzx)
    have e : x = (z : G) * ((z : G)⁻¹ * x) := by group
    rw [e]
    exact K.mul_mem hz hq
  have hKeq : K' = K := le_antisymm hK'K hKK'
  rw [← hKeq]
  exact hK'

theorem isUniqueM_KS
    (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) :
    IsUniqueM (K ⊔ T ⊓ H) H := by
  have hKSH : K ⊔ T ⊓ H ≤ H := _root_.sup_le (le_of_mem_cComp s.sk.cComp) inf_le_right
  have hHmax : quasithinIsMaxTwoLocal H := s.sk.base.inM.1
  refine ⟨⟨hHmax, hKSH⟩, fun H₁ hH₁ => ?_⟩
  obtain ⟨s₁, hSeq⟩ := s.setting432_of_inM hH₁
  have hS₁ : IsSylowTwoOf (T ⊓ H) H₁ := by
    have := s₁.isSylowTwoOf_S_H hR hC h37 h38 h39
    rwa [hSeq] at this
  have hK₁ := s.mem_cComp_of_inM h135 hR hC h37 h38 h39 h312 hH₁ hS₁
  have hSK : T ⊓ H₁ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hSeq]
    exact s.sk.S_le_normalizer
  have hH₁N : H₁ ≤ Subgroup.normalizer (K : Set G) :=
    s₁.le_normalizer_of_cComp hR hC h37 h38 h39 hK₁ hSK
  exact (hH₁.1.2 H hHmax.1 (hH₁N.trans (s.normalizer_K_le h135 hR hC h37 h38 h39))).symm

end Setting4311

end CFSG.Quasithin.H13.Ch4
