module

public import CFSG.Quasithin.Background.C48SporCoverZ4
public import CFSG.Quasithin.Background.C31SporL
public import CFSG.Quasithin.Background.C48PfFourModPfGrp
public import CFSG.Sporadic.Recognition.HSMultiplierCert

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_ker_of_imageModCenter [Finite G] {K M₀ : Subgroup G} (hM₀K : M₀ ≤ K)
    (hZ : IsPGroup 2 ↥(centerOf K)) {E : Subgroup ↥(imageModCenter K M₀)} [E.Normal]
    (hE : IsPGroup 2 ↥E) :
    IsPGroup 2 ((QuotientGroup.mk' E).comp (C31Spor.toImageModCenter hM₀K)).ker := by
  rintro ⟨m, hm⟩
  have hmE : C31Spor.toImageModCenter hM₀K m ∈ E := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hm
    exact hm
  obtain ⟨a, ha⟩ := hE ⟨_, hmE⟩
  have hφa : m ^ 2 ^ a ∈ (C31Spor.toImageModCenter hM₀K).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val ha
  rw [C31Spor.mem_ker_toImageModCenter] at hφa
  have hZm : ((m ^ 2 ^ a : ↥M₀) : G) ∈ centerOf K := ⟨hM₀K (m ^ 2 ^ a).2, hφa⟩
  obtain ⟨b, hb⟩ := hZ ⟨_, hZm⟩
  refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hb
  simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

theorem c48SporCoverHS_holds
    (H R M L V K : Subgroup G) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hc : C31Conclusion H R M L V K) (h7 : C31Case7 H R M L V K) (hpsl : IsPSL 3 2 1 (ModO2 L)) :
    V ⊓ centerOf K = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLM₀, -, hM₀K, -, hZ, -⟩ := hc
  set M₀ := conjClosure L M with hM₀
  rw [hLM₀] at hpsl
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using h.V_elem.2 x x.2)⟩
  have hVO₂ : V ≤ pCoreOf 2 M₀ :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V M₀ h.V_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.V_le).mpr
        (C48Spor.M0_le_normalizer_V h)) hV2
  have hcard168 : Nat.card (ModO2 M₀) = 168 :=
    (C48Pf.FMod.card_of_isPSL_two_one (Or.inl rfl) hpsl).1 rfl
  obtain ⟨hs, hext | hext⟩ := h7
  swap
  ·
    exfalso
    obtain ⟨E, hE, hE16, h6⟩ := hext
    have hE2 : IsPGroup 2 ↥E := C48Spor.isPGroup_of_isE2 hE16
    set φ := (QuotientGroup.mk' E).comp (C31Spor.toImageModCenter hM₀K) with hφ
    have hφs : Function.Surjective φ :=
      (QuotientGroup.mk'_surjective E).comp (C31Spor.toImageModCenter_surjective hM₀K)
    have hker := isPGroup_ker_of_imageModCenter hM₀K hZ hE2
    obtain ⟨e6⟩ := h6
    have hcard360 : Nat.card (↥(imageModCenter K M₀) ⧸ E) = 360 := by
      rw [Nat.card_congr e6.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have h1 : Nat.card ↥M₀ = 360 * Nat.card φ.ker := by
      rw [← hcard360, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have h2 : Nat.card ↥M₀ = 168 * Nat.card (CFSG.pCore 2 ↥M₀) := by
      rw [← hcard168, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    obtain ⟨a, ha⟩ := hker.exists_card_eq
    have h3 : 7 ∣ 15 * 2 ^ a := by
      refine ⟨Nat.card (CFSG.pCore 2 ↥M₀), ?_⟩
      have := h1.symm.trans h2
      rw [ha] at this
      omega
    have h4 : 7 ∣ 2 ^ a := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((by norm_num : (7 : ℕ).Prime).dvd_of_dvd_pow h4)
    omega
  set Mb := imageModCenter K M₀ with hMb
  obtain ⟨N₀, hN₀, ⟨e₀⟩, hY⟩ := hext
  have hYs : IsSimpleGroup (↥Mb ⧸ N₀) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hY).2
  have hcardY : Nat.card (↥Mb ⧸ N₀) = 168 :=
    (C48Pf.FMod.card_of_isPSL_two_one (Or.inl rfl) hY).1 rfl
  have hN₀4 : ∀ n ∈ N₀, n ^ 4 = 1 := by
    intro n hn
    have h1 := Z4C.pow_four (e₀ ⟨n, hn⟩)
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hN₀c : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    intro a ha b hb
    have h1 : e₀ ⟨a, ha⟩ * e₀ ⟨b, hb⟩ = e₀ ⟨b, hb⟩ * e₀ ⟨a, ha⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e₀.injective h1)
  set N : Subgroup (↥K ⧸ Subgroup.center ↥K) := N₀.map Mb.subtype with hN
  let e : ↥N ≃* Z4C := (N₀.equivMapOfInjective Mb.subtype Mb.subtype_injective).symm.trans e₀
  set O := N.comap (QuotientGroup.mk' (Subgroup.center ↥K)) with hO
  set M₀' := M₀.subgroupOf K with hM₀'
  set V' := V.subgroupOf K with hV'
  have hZ2 : Nat.card (Subgroup.center ↥K) ≤ 2 := by
    obtain ⟨eH⟩ := hs
    exact CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate
      (Group.isPerfect_def.mpr hK.2.2.1) eH
  have hmkMb : ∀ m ∈ M₀', QuotientGroup.mk' (Subgroup.center ↥K) m ∈ Mb := fun m hm =>
    Subgroup.mem_map_of_mem _ hm
  have hNnorm : ∀ g ∈ Mb, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    rintro g hg _ ⟨n₀, hn₀, rfl⟩
    exact ⟨⟨g, hg⟩ * n₀ * ⟨g, hg⟩⁻¹, hN₀.conj_mem n₀ hn₀ _, rfl⟩
  have hM₀O : M₀' ≤ Subgroup.normalizer (O : Set ↥K) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hm1 := hmkMb m hm
    constructor
    · intro hx
      show QuotientGroup.mk' _ (m * x * m⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNnorm _ hm1 _ hx
    · intro hx
      have hx' : QuotientGroup.mk' _ (m * x * m⁻¹) ∈ N := hx
      rw [map_mul, map_mul, map_inv] at hx'
      have := hNnorm _ (Mb.inv_mem hm1) _ hx'
      show QuotientGroup.mk' _ x ∈ N
      simpa [mul_assoc] using this
  set φ := (QuotientGroup.mk' N₀).comp (C31Spor.toImageModCenter hM₀K) with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective N₀).comp (C31Spor.toImageModCenter_surjective hM₀K)
  have hq := C31Spor.quasiNoTwo_L32 hY
  have hPφ : (CFSG.Open.pCore 2 ↥M₀).map φ = ⊥ :=
    hq.2 _ ((CFSG.LieType.BorelTits.pCore_normal 2).map φ hφs)
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map φ)
  have hVO : V' ≤ O := by
    intro v hv
    obtain ⟨y, hy, hyv⟩ := hVO₂ hv
    have h1 : φ y = 1 := by
      have : φ y ∈ (CFSG.Open.pCore 2 ↥M₀).map φ := Subgroup.mem_map_of_mem φ hy
      rwa [hPφ, Subgroup.mem_bot] at this
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine ⟨_, h1, ?_⟩
    show QuotientGroup.mk' _ (Subgroup.inclusion hM₀K y) = QuotientGroup.mk' _ v
    congr 1
    exact Subtype.ext hyv
  have hV2' : ∀ v ∈ V', v ^ 2 = 1 := fun v hv =>
    Subtype.ext (by simpa using h.V_elem.2 _ hv)
  have hVM' : ⁅V', M₀'⁆ = V' := by
    rw [hV', hM₀', ← C48Spor.commutator_subgroupOf_of_le (h.V_le.trans hM₀K) hM₀K, h.V_comm]
  have ht : ∃ t ∈ M₀', t ^ 7 ∈ Subgroup.center ↥K ∧
      ∃ x ∈ O, (t * x * t⁻¹)⁻¹ * x ∉ Subgroup.center ↥K := by
    by_contra hcon
    push Not at hcon
    have h7 : 7 ∣ Nat.card ↥Mb := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₀, hcardY]
      exact Dvd.dvd.mul_right (by norm_num) _
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' 7 h7
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp y.2
    have ht7 : t ^ 7 ∈ Subgroup.center ↥K := by
      have h1 : y ^ 7 = 1 := hy7 ▸ pow_orderOf_eq_one y
      have h2 : QuotientGroup.mk' (Subgroup.center ↥K) (t ^ 7) = 1 := by
        rw [map_pow, hty]
        exact congrArg Subtype.val h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have hyc : ∀ n ∈ N₀, y * n = n * y := by
      intro n hn
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) (n : ↥K ⧸ _)
      have hxO : x ∈ O := by
        show QuotientGroup.mk' _ x ∈ N
        rw [hx]
        exact ⟨n, hn, rfl⟩
      have h1 := hcon t ht ht7 x hxO
      have h2 : QuotientGroup.mk' (Subgroup.center ↥K) (t * x * t⁻¹) =
          QuotientGroup.mk' (Subgroup.center ↥K) x :=
        QuotientGroup.eq.mpr h1
      rw [map_mul, map_mul, map_inv, hty, hx] at h2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact mul_inv_eq_iff_eq_mul.mp h2
    set C₀ := Subgroup.centralizer (N₀ : Set ↥Mb) with hC₀
    have hyC : y ∈ C₀ := Subgroup.mem_centralizer_iff.mpr fun n hn => (hyc n hn).symm
    have : (C₀.map (QuotientGroup.mk' N₀)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N₀)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C₀.map (QuotientGroup.mk' N₀)) with hb | ht'
    ·
      have h1 : QuotientGroup.mk' N₀ y = 1 := by
        have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N₀) hyC
        rwa [hb, Subgroup.mem_bot] at this
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 := orderOf_dvd_of_pow_eq_one (hN₀4 y h1)
      rw [hy7] at h2
      omega
    ·
      have hcen : ∀ g : ↥Mb, ∀ n ∈ N₀, g * n = n * g := by
        intro g n hn
        obtain ⟨c, hc, hcg⟩ : QuotientGroup.mk' N₀ g ∈ C₀.map (QuotientGroup.mk' N₀) := by
          rw [ht']
          trivial
        have hk : c⁻¹ * g ∈ N₀ := QuotientGroup.eq.mp hcg
        have hg : g = c * (c⁻¹ * g) := by group
        rw [hg, mul_assoc, hN₀c _ hk n hn, ← mul_assoc,
          (Subgroup.mem_centralizer_iff.mp hc n hn).symm, mul_assoc]
      apply h.V_ne
      have hVZ : V ≤ centerOf K := by
        rw [← h.V_comm, Subgroup.commutator_le]
        intro v hv m hm
        have hvK : v ∈ K := hM₀K (h.V_le hv)
        have hmK : m ∈ K := hM₀K hm
        obtain ⟨n, hn, hnv⟩ := hVO (show (⟨v, hvK⟩ : ↥K) ∈ V' from hv)
        have hmMb : QuotientGroup.mk' (Subgroup.center ↥K) ⟨m, hmK⟩ ∈ Mb :=
          hmkMb ⟨m, hmK⟩ hm
        have h1 : QuotientGroup.mk' (Subgroup.center ↥K) ⁅(⟨v, hvK⟩ : ↥K), ⟨m, hmK⟩⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          have h2 := hcen ⟨_, hmMb⟩ n hn
          have h3 := congrArg Subtype.val h2
          simp only [Subgroup.coe_mul] at h3
          rw [show (Mb.subtype n) = (n : ↥K ⧸ _) from rfl] at hnv
          rw [← hnv]
          exact h3.symm
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        refine ⟨K.mul_mem (K.mul_mem (K.mul_mem hvK hmK) (K.inv_mem hvK)) (K.inv_mem hmK),
          Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨k, hk⟩)
      rw [eq_bot_iff, ← h.V_comm, Subgroup.commutator_le]
      intro v hv m hm
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hVZ hv).2 m (hM₀K hm)).symm
  obtain ⟨t, ht, ht7, htN⟩ := ht
  have hcore := inf_center_eq_bot_of_z4c hZ2 e hM₀O ht ht7 htN hVO hV2' hVM'
  rw [eq_bot_iff]
  rintro x ⟨hxV, hxK, hxC⟩
  have hx1 : (⟨x, hxK⟩ : ↥K) ∈ V' ⊓ Subgroup.center ↥K :=
    ⟨hxV, Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp hxC g g.2)⟩
  rw [hcore, Subgroup.mem_bot] at hx1
  exact congrArg Subtype.val hx1

end CFSG.Quasithin.C48Cover
