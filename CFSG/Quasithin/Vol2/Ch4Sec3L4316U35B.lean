module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316L34
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Y

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat Vol2.Ch11.SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL uSL_mul uSL_inv uSL_zero
  uSL_injective)
open scoped MatrixGroups Matrix Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem coprime_card_ker_starHom (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Nat.Coprime 5 (Nat.card (s.starHom s.KZ_le_G₀).ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (s.starHom s.KZ_le_G₀).ker with hN
  let φ : ↥N →* ↥(Subgroup.center (ModO2 KZ)) :=
    { toFun := fun k => ⟨QuotientGroup.mk (k : ↥KZ), (s.starHom_KZ_eq_one_iff k).mp k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcard : Nat.card N = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have hker2 : IsPGroup 2 ↥φ.ker := by
    intro k
    have h1 : ((k : ↥N) : ↥KZ) ∈ CFSG.pCore 2 ↥KZ := by
      have h2 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
      exact (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥KZ) ⟨_, h1⟩
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥KZ) => (x : ↥KZ)) ha
    simpa using this
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hker2
  have hdvd : Nat.card φ.range ∣ Nat.card (Subgroup.center (ModO2 KZ)) :=
    Subgroup.card_subgroup_dvd_card _
  have hr : Nat.Coprime 5 (Nat.card φ.range) := by
    rcases s.card_center_modO2 h135 hR hC h36 h37 h38 h39 with h | h <;> rw [h] at hdvd
    · rw [Nat.dvd_one.mp hdvd]
      norm_num
    · rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h' <;> rw [h'] <;> norm_num
  rw [hcard, he]
  exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num)) hr

theorem card_U : Nat.card ↥(u4311 I K) = Fintype.card F ^ 3 := by
  rw [Nat.card_congr (Equiv.ofBijective _ s.β_bij)]
  change Nat.card (Fin 3 → F) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Nat.card ↥R₂ = Nat.card ↥(q4311 I K) * Fintype.card F ^ 2 := by
  have hQR := s.q4311_le_R₂ h135 hR hC h37 h38 h39
  let φ₂ : ↥R₂ →* ↥(radE0 F) := (α.comp (Subgroup.inclusion s.R₂_le_K)).codRestrict (radE0 F)
    fun r => s.α_mem_radE0 r.2
  have hφ₂ : Function.Surjective φ₂ := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := s.modO2.1 x
    have hkR : (k : G) ∈ R₂ :=
      s.mem_R₂_of k.2 (by rw [show (⟨(k : G), k.2⟩ : ↥K) = k from rfl, hk]; exact hx)
    exact ⟨⟨k, hkR⟩, Subtype.ext hk⟩
  have hker : φ₂.ker = (q4311 I K).subgroupOf R₂ := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      s.mem_q4311_iff h135 hR hC h37 h38 h39 (s.R₂_le_K r.2)]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hbij : Function.Bijective (fun p : F × F =>
      (⟨specialLinearGroupEquivStatedSL 3 F (uSL p.1 p.2 0),
        SL3Pt.mem_radE0_iff.mpr ⟨p.1, p.2, rfl⟩⟩ : ↥(radE0 F))) := by
    constructor
    · intro p p' h
      have h1 := (specialLinearGroupEquivStatedSL 3 F).injective (congrArg Subtype.val h)
      obtain ⟨h2, h3, -⟩ := uSL_injective h1
      exact Prod.ext h2 h3
    · rintro ⟨x, hx⟩
      obtain ⟨a, b, rfl⟩ := SL3Pt.mem_radE0_iff.mp hx
      exact ⟨(a, b), rfl⟩
  have hrad : Nat.card ↥(radE0 F) = Fintype.card F ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_eq_fintype_card,
      sq]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ₂.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ₂ hφ₂).toEquiv, hrad, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv, mul_comm]

theorem card_R₂_le (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) {k₁ : G}
    (hk₁ : k₁ ∈ K₂) (ho : orderOf k₁ = 5) (hkK : k₁ ∈ K)
    (hrow : (![1, 0, 0] : Fin 3 → F) ᵥ* (((α ⟨k₁, hkK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ![1, 0, 0]) :
    Nat.card ↥R₂ ≤ 2 ^ 16 * Nat.card ↥(R₂ ⊓ Subgroup.centralizer ({k₁} : Set G)) := by
  classical
  have hF4 : Fintype.card F = 4 := by rw [s.card_F, hm]; norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hKQ, hUQ, βQ, hβs, hβk, hβa⟩ := s.dualQ
  have hQR := s.q4311_le_R₂ h135 hR hC h37 h38 h39
  have hcardQ : Nat.card ↥(q4311 I K) = Nat.card ↥(u4311 I K) * Fintype.card F ^ 6 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup βQ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective βQ hβs).toEquiv, hβk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv, mul_comm]
    congr 1
    change Nat.card (Fin 2 → Fin 3 → F) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, ← pow_mul]
  set gk : GL (Fin 3) F := ((α ⟨k₁, hkK⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) with hgk
  have hfixdual : ∀ c : F, moduleAct true gk *ᵥ (c • ![1, 0, 0]) = c • ![(1 : F), 0, 0] := by
    intro c
    rw [Matrix.mulVec_smul]
    congr 1
    change ((gk⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ ![1, 0, 0] = ![1, 0, 0]
    rw [Matrix.mulVec_transpose]
    conv_lhs => rw [← hrow]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have hcoset : ∀ q : ↥(q4311 I K), (∀ i, ∃ c : F, Multiplicative.toAdd (βQ q) i =
      c • ![1, 0, 0]) → ∀ n : ℕ, (q : G)⁻¹ * (k₁ ^ n * q * (k₁ ^ n)⁻¹) ∈ u4311 I K := by
    intro q hq n
    have hU1 : (q : G)⁻¹ * (k₁ * q * k₁⁻¹) ∈ u4311 I K := by
      have hmem : k₁ * q * k₁⁻¹ ∈ q4311 I K :=
        (Subgroup.mem_normalizer_iff.mp (hKQ hkK) q).mp q.2
      have h1 := hβa ⟨k₁, hkK⟩ q ⟨_, hmem⟩ rfl
      have h2 : βQ ⟨_, hmem⟩ = βQ q := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [h1 i]
        obtain ⟨c, hc⟩ := hq i
        rw [hc]
        exact hfixdual c
      have h3 : q⁻¹ * ⟨_, hmem⟩ ∈ βQ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
      rw [hβk] at h3
      exact h3
    induction n with
    | zero => simp
    | succ n ih =>
      have hkU : k₁ ∈ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) := s.K_U hkK
      have e : (q : G)⁻¹ * (k₁ ^ (n + 1) * q * (k₁ ^ (n + 1))⁻¹) =
          ((q : G)⁻¹ * (k₁ * q * k₁⁻¹)) *
            (k₁ * ((q : G)⁻¹ * (k₁ ^ n * q * (k₁ ^ n)⁻¹)) * k₁⁻¹) := by
        rw [pow_succ']
        group
      rw [e]
      exact (u4311 I K).mul_mem hU1 ((Subgroup.mem_normalizer_iff.mp hkU _).mp ih)
  have hX : IsPGroup 5 ↥(Subgroup.zpowers k₁) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, ho]
    exact ⟨1, by norm_num⟩
  have hU5 : ¬ 5 ∣ Nat.card ↥(u4311 I K) := by
    rw [s.card_U, hF4]
    norm_num
  have hXU : Subgroup.zpowers k₁ ≤ Subgroup.normalizer ((u4311 I K : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr (s.K_U hkK)
  have hfix : ∀ v : Fin 2 → F, ∃ f ∈ q4311 I K, f ∈ Subgroup.centralizer ({k₁} : Set G) ∧
      ∀ hf : f ∈ q4311 I K, βQ ⟨f, hf⟩ = Multiplicative.ofAdd (fun i => v i • ![1, 0, 0]) := by
    intro v
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (fun i => v i • ![1, 0, 0]))
    have hq' : ∀ i, ∃ c : F, Multiplicative.toAdd (βQ q) i = c • ![1, 0, 0] :=
      fun i => ⟨v i, by rw [hq]; rfl⟩
    obtain ⟨b, hb, hbfix⟩ := exists_mul_fixed_of_isPGroup hX hU5 hXU (a := (q : G)) fun x hx => by
      obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ((mem_powers_iff_mem_zpowers).mpr hx)
      exact hcoset q hq' j
    have hbQ : b ∈ q4311 I K := hUQ hb
    refine ⟨(q : G) * b, (q4311 I K).mul_mem q.2 hbQ, ?_, fun hf => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have := hbfix k₁ (Subgroup.mem_zpowers k₁)
      calc k₁ * (q * b) = k₁ * (q * b) * k₁⁻¹ * k₁ := by group
        _ = q * b * k₁ := by rw [this]
    · have hb1 : βQ ⟨b, hbQ⟩ = 1 := by
        have : (⟨b, hbQ⟩ : ↥(q4311 I K)) ∈ βQ.ker := by
          rw [hβk]
          exact hb
        exact this
      have e : (⟨(q : G) * b, hf⟩ : ↥(q4311 I K)) = q * ⟨b, hbQ⟩ := rfl
      rw [e, map_mul, hb1, mul_one, hq]
  choose f hfQ hfC hfβ using hfix
  have hZS : ∀ d : F, ∃ z ∈ ZS, ∀ hz : z ∈ u4311 I K, β ⟨z, hz⟩ =
      Multiplicative.ofAdd (d • ![1, 0, 0]) := by
    intro d
    obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd (d • ![1, 0, 0]))
    refine ⟨u, (s.ZS_iff u).mpr ⟨d, by rw [hu]; rfl⟩, fun hz => ?_⟩
    rw [← hu]
  choose z hzZ hzβ using hZS
  have hzU : ∀ d, z d ∈ u4311 I K := fun d => s.ZS_le_U (hzZ d)
  have hzC : ∀ d, z d ∈ Subgroup.centralizer ({k₁} : Set G) := by
    intro d
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (Subgroup.mem_centralizer_iff.mp (s.K₂_le_centralizer hk₁) (z d) (hzZ d)).symm
  let ι : F × (Fin 2 → F) → ↥(q4311 I K ⊓ Subgroup.centralizer ({k₁} : Set G)) := fun p =>
    ⟨z p.1 * f p.2, ⟨(q4311 I K).mul_mem (hUQ (hzU p.1)) (hfQ p.2),
      Subgroup.mul_mem _ (hzC p.1) (hfC p.2)⟩⟩
  have hβzf : ∀ d v, βQ ⟨z d * f v, (q4311 I K).mul_mem (hUQ (hzU d)) (hfQ v)⟩ =
      Multiplicative.ofAdd (fun i => v i • ![1, 0, 0]) := by
    intro d v
    have e : (⟨z d * f v, (q4311 I K).mul_mem (hUQ (hzU d)) (hfQ v)⟩ : ↥(q4311 I K)) =
        ⟨z d, hUQ (hzU d)⟩ * ⟨f v, hfQ v⟩ := rfl
    have hz1 : βQ ⟨z d, hUQ (hzU d)⟩ = 1 := by
      have h' : (⟨z d, hUQ (hzU d)⟩ : ↥(q4311 I K)) ∈ βQ.ker := by
        rw [hβk]
        exact hzU d
      exact h'
    rw [e, map_mul, hfβ v (hfQ v), hz1, one_mul]
  have hinj : Function.Injective ι := by
    intro p p' h
    have h1 : z p.1 * f p.2 = z p'.1 * f p'.2 := congrArg Subtype.val h
    have h2 := congrArg (fun x => Multiplicative.toAdd (βQ x))
      (Subtype.ext h1 : (⟨z p.1 * f p.2, (q4311 I K).mul_mem (hUQ (hzU p.1)) (hfQ p.2)⟩ :
        ↥(q4311 I K)) = ⟨z p'.1 * f p'.2, (q4311 I K).mul_mem (hUQ (hzU p'.1)) (hfQ p'.2)⟩)
    simp only [hβzf, toAdd_ofAdd] at h2
    have hv : p.2 = p'.2 := by
      funext i
      have := congrFun (congrFun h2 i) 0
      simpa using this
    have hd : z p.1 = z p'.1 := by
      rw [hv] at h1
      exact mul_right_cancel h1
    have h3 := congrArg (fun x => Multiplicative.toAdd (β x))
      (Subtype.ext hd : (⟨z p.1, hzU p.1⟩ : ↥(u4311 I K)) = ⟨z p'.1, hzU p'.1⟩)
    simp only [hzβ, toAdd_ofAdd] at h3
    have hd' : p.1 = p'.1 := by
      have := congrFun h3 0
      simpa using this
    exact Prod.ext hd' hv
  have hcardC : Fintype.card F ^ 3 ≤
      Nat.card ↥(q4311 I K ⊓ Subgroup.centralizer ({k₁} : Set G)) := by
    have := Nat.card_le_card_of_injective ι hinj
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Fin 2 → F),
      Fintype.card_fun, Fintype.card_fin] at this
    calc Fintype.card F ^ 3 = Fintype.card F * Fintype.card F ^ 2 := by ring
      _ ≤ _ := this
  have hle : Nat.card ↥(q4311 I K ⊓ Subgroup.centralizer ({k₁} : Set G)) ≤
      Nat.card ↥(R₂ ⊓ Subgroup.centralizer ({k₁} : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hQR)
  have hR₂card : Nat.card ↥R₂ = 4 ^ 11 := by
    rw [s.card_R₂ h135 hR hC h37 h38 h39, hcardQ, s.card_U, hF4]
    norm_num
  rw [hF4] at hcardC
  rw [hR₂card]
  calc (4 : ℕ) ^ 11 = 2 ^ 16 * 4 ^ 3 := by norm_num
    _ ≤ 2 ^ 16 * Nat.card ↥(R₂ ⊓ Subgroup.centralizer ({k₁} : Set G)) :=
      Nat.mul_le_mul_left _ (hcardC.trans hle)

end Setting4315

end CFSG.Quasithin.H13.Ch4
