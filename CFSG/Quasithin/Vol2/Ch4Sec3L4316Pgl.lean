module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316L34
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

namespace L4316

theorem card_of_isPSL_three_two_two {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_statedProj_top_GL3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) = 60480 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  set Z' := (StatedScalars (Fin 3) K).subgroupOf (⊤ : Subgroup (GL (Fin 3) K)) with hZ'
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
  have hGL : Nat.card ↥(⊤ : Subgroup (GL (Fin 3) K)) = 181440 := by
    rw [Subgroup.card_top, Matrix.card_GL_field, hK', Fin.prod_univ_three]
    norm_num
  have hinj :
      Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
    intro a b h
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map] at this
    exact Units.ext this
  have hZ : Nat.card Z' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, StatedScalars,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hK]
  rw [hGL, hZ] at h1
  change Nat.card (↥(⊤ : Subgroup (GL (Fin 3) K)) ⧸ Z') = 60480
  omega

theorem nonempty_statedProj_mulEquiv {K F : Type} [Field K] [Finite K] [Field F] [Fintype F]
    (hK : Nat.card K = 4) (hF : Fintype.card F = 4) :
    Nonempty (StatedProj (⊤ : Subgroup (GL (Fin 3) K)) ≃*
      GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = Fintype.card F := by rw [← Nat.card_eq_fintype_card, hK, hF]
  let φ : K ≃+* F := FiniteField.ringEquivOfCardEq hKF
  let eGL : GL (Fin 3) K ≃* GL (Fin 3) F :=
    { toFun := Matrix.GeneralLinearGroup.map (φ : K →+* F)
      invFun := Matrix.GeneralLinearGroup.map (φ.symm : F →+* K)
      left_inv := fun g => by
        ext i j
        simp [Matrix.GeneralLinearGroup.map]
      right_inv := fun g => by
        ext i j
        simp [Matrix.GeneralLinearGroup.map]
      map_mul' := map_mul _ }
  have hsc : StatedScalars (Fin 3) K = Subgroup.center (GL (Fin 3) K) := by
    rw [StatedScalars, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have e₁ : StatedProj (⊤ : Subgroup (GL (Fin 3) K)) ≃*
      GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K) := by
    refine QuotientGroup.congr _ _ Subgroup.topEquiv ?_
    rw [hsc]
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      exact ⟨⟨g, Subgroup.mem_top g⟩, hg, rfl⟩
  have e₂ : GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K) ≃*
      GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F) :=
    QuotientGroup.congr _ _ eGL (Subgroup.map_center_eq eGL)
  exact ⟨e₁.trans e₂⟩

theorem conj_mem_oPrimeResidualOf_top {H : Type} [Group H] {p : ℕ} (g : H) {x : H}
    (hx : x ∈ oPrimeResidualOf p (⊤ : Subgroup H)) :
    g * x * g⁻¹ ∈ oPrimeResidualOf p (⊤ : Subgroup H) := by
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨-, k, hk⟩ := hz
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, k, ?_⟩
    have : orderOf (MulAut.conj g z) = orderOf z :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    rw [MulAut.conj_apply] at this
    rw [this, hk]
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  | inv a _ ih =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ih

theorem card_sup_eq_mul {G : Type} [Group G] [Finite G] {N H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hinf : N ⊓ H = ⊥) :
    Nat.card ↥(N ⊔ H) = Nat.card N * Nat.card H := by
  classical
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N H hHN
  have hmem : ∀ p : ↥N × ↥H, (p.1 : G) * p.2 ∈ N ⊔ H := fun p => by
    have : (p.1 : G) * p.2 ∈ ((N : Set G) * (H : Set G)) := Set.mul_mem_mul p.1.2 p.2.2
    rw [← hset] at this
    exact this
  let f : ↥N × ↥H → ↥(N ⊔ H) := fun p => ⟨(p.1 : G) * p.2, hmem p⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ N ⊓ H :=
        ⟨N.mul_mem (N.inv_mem a'.2) a.2, h2 ▸ H.mul_mem b'.2 (H.inv_mem b.2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp h3).symm
      subst ha
      have hb : b = b' := Subtype.ext (mul_left_cancel h1)
      rw [hb]
    · rintro ⟨x, hx⟩
      have : x ∈ ((N : Set G) * (H : Set G)) := by
        rw [← hset]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := this
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem ker_starImage (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hSK : IsSimpleGroup ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))))
    (hZ : Subgroup.center (ModO2 KZ) = ⊥) (k : ↥KZ) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.normalizer (ZS : Set G)))
        ⟨k, le_of_mem_cComp s.KZ_mem k.2⟩ = 1 ↔ (k : G) ∈ pCoreOf 2 KZ := by
  classical
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp s.KZ_mem
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
  set ψ : ↥KZ →* PStar 3 ↥GZ := π.comp (Subgroup.inclusion hKZGZ) with hψ
  have hO : ∀ k : ↥KZ, (k : G) ∈ pCoreOf 2 KZ → ψ k = 1 := fun k hk =>
    (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥GZ) (⟨k, hKZGZ k.2⟩ : ↥GZ)).mpr
      (Setting436Sp4.pCoreOf_subgroupOf_le_pPrimeCore (x := ⟨k, hKZGZ k.2⟩) hKZGZ s.KZ_normal hk)
  refine ⟨fun h => ?_, hO k⟩
  have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
  have hNn : (CFSG.pCore 2 ↥KZ).Normal := CFSG.pCore_normal
  have hkn : (ψ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ))).Normal :=
    (MonoidHom.normal_ker ψ).map (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ))
      (QuotientGroup.mk'_surjective _)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
    (ψ.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ))) with hc | htop
  · have hk : QuotientGroup.mk' (CFSG.pCore 2 ↥KZ) k ∈ Subgroup.center (ModO2 KZ) :=
      hc ⟨k, h, rfl⟩
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact (mem_pCoreOf_iff' k).mpr hk
  · exfalso
    have hψ1 : ∀ k : ↥KZ, ψ k = 1 := by
      intro k
      obtain ⟨k', hk', hk'e⟩ := htop ▸ Subgroup.mem_top (QuotientGroup.mk' (CFSG.pCore 2 ↥KZ) k)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'e
      have h1 := hO _ ((mem_pCoreOf_iff' _).mpr hk'e)
      have e : k = k' * (k'⁻¹ * k) := by group
      rw [e, map_mul, MonoidHom.mem_ker.mp hk', h1, one_mul]
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(starImage 3 (KZ.subgroupOf GZ))
    apply hab
    have hall : ∀ x : ↥(starImage 3 (KZ.subgroupOf GZ)), x = 1 := by
      rintro ⟨_, g, hg, rfl⟩
      apply Subtype.ext
      exact hψ1 ⟨g, hg⟩
    rw [hall a, hall b]

theorem card_starImage (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hSK : IsSimpleGroup ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))))
    (hZ : Subgroup.center (ModO2 KZ) = ⊥) (hL : IsPSL 3 2 2 (ModO2 KZ)) :
    Nat.card ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))) = 20160 := by
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp s.KZ_mem
  set ψ₀ : ↥KZ →* PStar 3 ↥GZ :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ)).comp (Subgroup.inclusion hKZGZ) with hψ₀
  have hrange : ψ₀.range = starImage 3 (KZ.subgroupOf GZ) := by
    rw [hψ₀, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ψ₀.ker = CFSG.pCore 2 ↥KZ := by
    ext k
    rw [MonoidHom.mem_ker, ← mem_pCoreOf_iff' k]
    exact s.ker_starImage h135 hR hC h36 h37 h38 h39 hSK hZ k
  rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ₀).toEquiv,
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv]
  exact L4316.card_of_isPSL_three_two_two hL

omit s [Finite G] in
theorem isPGLEps3_oPrimeResidual
    (hA : A318Case2 (starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))))
    (hcard : Nat.card ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))) = 20160) :
    IsPGLEps3 true 4 ↥(oPrimeResidualOf 3
      (⊤ : Subgroup (PStar 3 ↥(Subgroup.normalizer (ZS : Set G))))) := by
  obtain ⟨s', q, -, hpslq, hcase⟩ := hA
  obtain ⟨hq2, hcq⟩ := CFSG.Quasithin.H13.L34.card_of_isPSLEps3q hpslq
  rw [hcard] at hcq
  have hbig : ∀ q : ℕ, 5 ≤ q → 20160 < CFSG.Quasithin.H13.L34.pslOrd q ∧
      20160 < CFSG.Quasithin.H13.L34.psuOrd q := by
    intro q hq
    have h3 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have hg1 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hg2 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hg1p : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hg2p : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hN1 : 372000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
      calc 372000 = 125 * (24 * 124) := by norm_num
        _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
          Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
    have hN2 : 372000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
      calc 372000 ≤ 125 * (24 * 126) := by norm_num
        _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
          Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
    constructor
    · rw [CFSG.Quasithin.H13.L34.pslOrd, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hg1p]
      calc (20160 + 1) * Nat.gcd 3 (q - 1) ≤ (20160 + 1) * 3 := Nat.mul_le_mul_left _ hg1
        _ ≤ 372000 := by norm_num
        _ ≤ _ := hN1
    · rw [CFSG.Quasithin.H13.L34.psuOrd, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hg2p]
      calc (20160 + 1) * Nat.gcd 3 (q + 1) ≤ (20160 + 1) * 3 := Nat.mul_le_mul_left _ hg2
        _ ≤ 372000 := by norm_num
        _ ≤ _ := hN2
  have hq : s' = true ∧ q = 4 := by
    by_cases h5 : 5 ≤ q
    · exfalso
      obtain ⟨h1, h2⟩ := hbig q h5
      cases s' <;> simp at hcq <;> omega
    · have hq' : q = 2 ∨ q = 3 ∨ q = 4 := by omega
      cases s' <;> rcases hq' with rfl | rfl | rfl <;> simp at hcq <;>
        first | exact ⟨rfl, rfl⟩ | (revert hcq; decide)
  obtain ⟨rfl, rfl⟩ := hq
  rcases hcase with h | ⟨m', hm', -⟩
  · exact h
  · exfalso
    have : (2 : ℕ) ^ 2 = 2 ^ (3 * m') := by rw [← hm']; norm_num
    have := Nat.pow_right_injective (le_refl 2) this
    omega

theorem Γ_le_GZ : KZ ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (ZS : Set G) :=
  _root_.sup_le (le_of_mem_cComp s.KZ_mem) s.Y_le_normalizer_ZS

theorem mem_KZ_of_mem_pPrimeCore (hm : m = 2) {γ : G} (hγ : γ ∈ KZ ⊔ Subgroup.zpowers y)
    (h3 : (⟨γ, s.Γ_le_GZ hγ⟩ : ↥(Subgroup.normalizer (ZS : Set G))) ∈
      CFSG.pPrimeCore 3 ↥(Subgroup.normalizer (ZS : Set G))) : γ ∈ KZ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYN : Subgroup.zpowers y ≤ Subgroup.normalizer (KZ : Set G) :=
    s.Y_le_normalizer_ZS.trans s.KZ_normal
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left KZ (Subgroup.zpowers y) hYN
  have hγ' : γ ∈ ((KZ : Set G) * (Subgroup.zpowers y : Set G)) := by
    rw [← hset]
    exact hγ
  obtain ⟨k, hk, w, hw, rfl⟩ := hγ'
  have hstep : ∀ (a b c : G) (i : ℕ), a ^ (i + 1) * c * (a ^ (i + 1))⁻¹ =
      a * (a ^ i * c * (a ^ i)⁻¹) * a⁻¹ := by
    intro a b c i
    rw [pow_succ', mul_inv_rev]
    group
  have hact : ∀ i : ℕ, ∀ z ∈ ZS, (k * w) ^ i * z * ((k * w) ^ i)⁻¹ = w ^ i * z * (w ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro z _; simp
    | succ i ih =>
      intro z hz
      have hwi : w ^ (i + 1) ∈ Subgroup.normalizer (ZS : Set G) :=
        Subgroup.pow_mem _ (s.Y_le_normalizer_ZS hw) _
      have hmem : w ^ (i + 1) * z * (w ^ (i + 1))⁻¹ ∈ ZS :=
        (Subgroup.mem_normalizer_iff.mp hwi z).mp hz
      have hkc := Subgroup.mem_centralizer_iff.mp (s.KZ_cent hk) _ hmem
      rw [hstep (k * w) 1 z i, ih z hz]
      calc k * w * (w ^ i * z * (w ^ i)⁻¹) * (k * w)⁻¹
          = k * (w * (w ^ i * z * (w ^ i)⁻¹) * w⁻¹) * k⁻¹ := by group
        _ = k * (w ^ (i + 1) * z * (w ^ (i + 1))⁻¹) * k⁻¹ := by rw [hstep w 1 z i]
        _ = w ^ (i + 1) * z * (w ^ (i + 1))⁻¹ := by
          rw [← hkc]
          group
  set r := orderOf (k * w) with hr
  have hrcop : Nat.Coprime 3 r := by
    have h1 := Subgroup.orderOf_dvd_natCard _ h3
    rw [Subgroup.orderOf_mk] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hwr : w ^ r = 1 := by
    apply s.Y_faithful (Subgroup.pow_mem _ hw r)
    intro z hz
    rw [← hact r z hz, hr, pow_orderOf_eq_one]
    group
  have hwo : orderOf w ∣ 3 := by
    have h1 := orderOf_dvd_of_mem_zpowers hw
    rwa [s.orderOf_y, hm] at h1
  have hw1 : w = 1 := by
    have h2 := orderOf_dvd_of_pow_eq_one hwr
    have h3' : orderOf w = 1 := Nat.eq_one_of_dvd_coprimes hrcop hwo h2
    exact orderOf_eq_one_iff.mp h3'
  rw [hw1]
  simpa using hk

theorem exists_alpha_of (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hm : m = 2)
    (hA : A318Case2 (starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))))
    (hQL : IsPSL 3 2 2 (ModO2 KZ)) :
    ∃ α' : ↥(KZ ⊔ Subgroup.zpowers y) →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F),
      Function.Surjective α' ∧ ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  set Γ := KZ ⊔ Subgroup.zpowers y with hΓ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp s.KZ_mem
  have hSK : IsSimpleGroup ↥(starImage 3 (KZ.subgroupOf GZ)) := by
    obtain ⟨s', q, -, hpslq, -⟩ := hA
    exact L436.isSimpleGroup_of_isPSLEps3q hpslq
  have hZ := s.center_modO2_eq_bot h135 hR hC h36 h37 h38 h39 hSK
  have hcardS := s.card_starImage h135 hR hC h36 h37 h38 h39 hSK hZ hQL
  set O := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 ↥GZ)) with hO
  obtain ⟨K', _, _, hK', ⟨eO⟩⟩ := isPGLEps3_oPrimeResidual hA hcardS
  obtain ⟨eP⟩ := L4316.nonempty_statedProj_mulEquiv hK' (by rw [s.card_F, hm]; norm_num :
    Fintype.card F = 4)
  have hcardO : Nat.card ↥O = 60480 := by
    rw [Nat.card_congr eO.toEquiv]
    exact L4316.card_statedProj_top_GL3 hK'
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
  set ψ : ↥Γ →* PStar 3 ↥GZ := π.comp (Subgroup.inclusion s.Γ_le_GZ) with hψ
  have hKZO : starImage 3 (KZ.subgroupOf GZ) ≤ O := by
    have := hSK
    set SK := starImage 3 (KZ.subgroupOf GZ) with hSKdef
    have hn : (O.subgroupOf SK).Normal :=
      ⟨fun x hx g => L4316.conj_mem_oPrimeResidualOf_top (g : PStar 3 ↥GZ) hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf SK) with h | h
    · exfalso
      have : Fintype ↥SK := Fintype.ofFinite _
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥SK) 3 (by
        rw [← Nat.card_eq_fintype_card, hcardS]
        norm_num)
      have hxO : (x : PStar 3 ↥GZ) ∈ O :=
        Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [Subgroup.orderOf_coe, hx, pow_one]⟩
      have h1 : x ∈ O.subgroupOf SK := hxO
      rw [h, Subgroup.mem_bot] at h1
      rw [h1, orderOf_one] at hx
      omega
    · intro x hx
      have h1 : (⟨x, hx⟩ : ↥SK) ∈ O.subgroupOf SK := h ▸ Subgroup.mem_top _
      exact h1
  have hψO : ∀ γ : ↥Γ, ψ γ ∈ O := by
    have hle : Γ ≤ (O.comap π).map GZ.subtype := by
      refine _root_.sup_le (fun k hk => ⟨⟨k, hKZGZ hk⟩, hKZO ⟨⟨k, hKZGZ hk⟩, hk, rfl⟩, rfl⟩) ?_
      rw [Subgroup.zpowers_le]
      refine ⟨⟨y, s.Y_le_normalizer_ZS (Subgroup.mem_zpowers y)⟩, ?_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf (π ⟨y, s.Y_le_normalizer_ZS (Subgroup.mem_zpowers y)⟩) =
          3 ^ k := by
        have h1 := orderOf_map_dvd π ⟨y, s.Y_le_normalizer_ZS (Subgroup.mem_zpowers y)⟩
        have h3 : 2 ^ m - 1 = 3 := by rw [hm]; norm_num
        rw [Subgroup.orderOf_mk, s.orderOf_y, h3] at h1
        rcases (Nat.dvd_prime Nat.prime_three).mp (by simpa using h1) with h | h
        · exact ⟨0, by rw [h, pow_zero]⟩
        · exact ⟨1, by rw [h, pow_one]⟩
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, k, hk⟩
    intro γ
    obtain ⟨g, hg, hge⟩ := hle γ.2
    have : ψ γ = π g := by
      rw [hψ, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hge.symm
    rw [this]
    exact hg
  set ψ' : ↥Γ →* ↥O := ψ.codRestrict O hψO with hψ'
  have hker : ∀ γ : ↥Γ, ψ γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ := by
    intro γ
    constructor
    · intro h
      have h3 : (⟨γ, s.Γ_le_GZ γ.2⟩ : ↥GZ) ∈ CFSG.pPrimeCore 3 ↥GZ :=
        (QuotientGroup.eq_one_iff _).mp h
      have hγK := s.mem_KZ_of_mem_pPrimeCore hm γ.2 h3
      exact (s.ker_starImage h135 hR hC h36 h37 h38 h39 hSK hZ ⟨γ, hγK⟩).mp h
    · intro h
      exact (s.ker_starImage h135 hR hC h36 h37 h38 h39 hSK hZ ⟨γ, pCoreOf_le 2 KZ h⟩).mpr h
  have hYN : Subgroup.zpowers y ≤ Subgroup.normalizer (KZ : Set G) :=
    s.Y_le_normalizer_ZS.trans s.KZ_normal
  have hinf : KZ ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwK, hwY⟩
    rw [Subgroup.mem_bot]
    exact s.Y_faithful hwY fun z hz => by
      rw [(Subgroup.mem_centralizer_iff.mp (s.KZ_cent hwK) z hz).symm, mul_inv_cancel_right]
  have hcardΓ : Nat.card ↥Γ = Nat.card ↥KZ * 3 := by
    rw [L4316.card_sup_eq_mul hYN hinf, s.card_Y, hm]
    norm_num
  have hcardKZ : Nat.card ↥KZ = 20160 * Nat.card ↥(pCoreOf 2 KZ) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥KZ)
    rw [L4316.card_of_isPSL_three_two_two hQL] at h1
    rw [h1, pCoreOf, Subgroup.card_map_of_injective KZ.subtype_injective]
  have hkerψ' : Nat.card ψ'.ker = Nat.card ↥(pCoreOf 2 KZ) := by
    have hle : pCoreOf 2 KZ ≤ Γ := (pCoreOf_le 2 KZ).trans le_sup_left
    have hk : ψ'.ker = (pCoreOf 2 KZ).subgroupOf Γ := by
      ext γ
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker γ]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  have hsurj : Function.Surjective ψ' := by
    have h1 := Subgroup.card_ker_mul_card_range ψ'
    rw [hkerψ', hcardΓ, hcardKZ] at h1
    have hpos : 0 < Nat.card ↥(pCoreOf 2 KZ) := Nat.card_pos
    have h2 : Nat.card ψ'.range = 60480 := by
      have : Nat.card ↥(pCoreOf 2 KZ) * Nat.card ψ'.range =
          Nat.card ↥(pCoreOf 2 KZ) * 60480 := by
        rw [h1]
        ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have h3 : ψ'.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h2, hcardO])
    exact MonoidHom.range_eq_top.mp h3
  refine ⟨(eO.trans eP).toMonoidHom.comp ψ', (eO.trans eP).surjective.comp hsurj, fun γ => ?_⟩
  rw [← hker γ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Setting4315

end CFSG.Quasithin.H13.Ch4
