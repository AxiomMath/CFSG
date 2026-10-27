module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXCyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace L45RankX

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_normalized_max {p : ℕ} [Fact p.Prime] (L B : Subgroup G)
    (hBp : IsPGroup p B) (hBL : B ≤ Subgroup.normalizer (L : Set G)) :
    ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup p Q ∧ B ≤ Subgroup.normalizer (Q : Set G) ∧
      ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ L → IsPGroup p Q' → Q' = Q := by
  classical
  let φ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  let _ : MulDistribMulAction B L := MulDistribMulAction.compHom L φ
  let _ : MulAction B (Sylow p L) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow p L) := by
    intro h
    have h1 := card_sylow_modEq_one p L
    have h2 : Nat.card (Sylow p L) % p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, h2, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at h1
    exact zero_ne_one h1
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p L) hcard
  refine ⟨(Q₀ : Subgroup L).map L.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _, ?_,
    fun Q' hQQ' hQ'L hQ'p => ?_⟩
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (Q₀ : Subgroup L) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q₀ : Subgroup L) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((L.normalizerMonoidHom) (Subgroup.inclusion hBL ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  · have hp' : IsPGroup p (Q'.subgroupOf L) :=
      hQ'p.of_equiv (Subgroup.subgroupOfEquivOfLe hQ'L).symm
    have hle : (Q₀ : Subgroup L) ≤ Q'.subgroupOf L := fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hQQ' ⟨y, hy, rfl⟩)
    have heq := Q₀.is_maximal' hp' hle
    refine le_antisymm (fun g hg => ?_) hQQ'
    have hg' : (⟨g, hQ'L hg⟩ : L) ∈ Q'.subgroupOf L := Subgroup.mem_subgroupOf.mpr hg
    rw [heq] at hg'
    exact ⟨_, hg', rfl⟩

end Sylow

section Lift

variable {G : Type*} [Group G] {K : Subgroup G} {R : Type} [Group R]
  {θ : K ⧸ Subgroup.center K ≃* R}

theorem exists_lift_of_coprime {p : ℕ} (hp : p.Prime)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) {r : R} {m : ℕ} (hr : r ^ p ^ m = 1) :
    ∃ k : K, k ^ p ^ m = 1 ∧ θ (k : K ⧸ Subgroup.center K) = r := by
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H k₀ =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨1, one_pow _, ?_⟩
      rw [pow_zero, pow_one] at hr
      rw [hr, QuotientGroup.mk_one, map_one]
    set N := Nat.card (Subgroup.center K) with hN
    have hcop : Nat.Coprime N (p ^ m) := (Nat.Coprime.pow_left m hZ).symm
    obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
      (Nat.one_lt_pow hm.ne' hp.one_lt)
    have h1 : k₀ ^ p ^ m ∈ Subgroup.center K := by
      have : ((k₀ : K ⧸ Subgroup.center K)) ^ p ^ m = 1 :=
        θ.injective (by rw [map_pow, hr, map_one])
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
      exact this
    have h2 : (k₀ ^ p ^ m) ^ N = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨_, h1⟩)
      exact congrArg Subtype.val this
    refine ⟨k₀ ^ (N * j), ?_, ?_⟩
    · calc (k₀ ^ (N * j)) ^ p ^ m = ((k₀ ^ p ^ m) ^ N) ^ j := by
            rw [← pow_mul, ← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [h2, one_pow]
    · rw [QuotientGroup.mk_pow, map_pow]
      exact pow_eq_self_of_mod_eq_one hr hj

theorem conj_mem_of_mk_eq {p : ℕ} (hZ : Nat.Coprime p (Nat.card (Subgroup.center K)))
    {S : Subgroup G} (hSK : S ≤ K) (hSp : IsPGroup p S) {k s s' : G} (hk : k ∈ K)
    (hkp : ∃ a : ℕ, k ^ p ^ a = 1) (hs : s ∈ S) (hs' : s' ∈ S)
    (heq : ((⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩ : K) :
        K ⧸ Subgroup.center K) = ((⟨s', hSK hs'⟩ : K) : K ⧸ Subgroup.center K)) :
    k * s * k⁻¹ ∈ S := by
  obtain ⟨a, -⟩ := hkp
  obtain ⟨b, hb⟩ := hSp ⟨s, hs⟩
  obtain ⟨c, hc⟩ := hSp ⟨s', hs'⟩
  have hb' : s ^ p ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hc' : s' ^ p ^ c = 1 := by simpa using congrArg Subtype.val hc
  set z : K := (⟨s', hSK hs'⟩ : K)⁻¹ * ⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩
    with hz
  have hzZ : z ∈ Subgroup.center K := by
    have := QuotientGroup.eq.mp heq.symm
    simpa [hz] using this
  have hzc : ∀ w : K, w * z = z * w := fun w => (Subgroup.mem_center_iff.mp hzZ w)
  have hzp : z ^ p ^ (b + c) = 1 := by
    have e : z ^ p ^ (b + c) = ((⟨s', hSK hs'⟩ : K)⁻¹) ^ p ^ (b + c) *
        (⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩ : K) ^ p ^ (b + c) := by
      rw [hz]
      refine Commute.mul_pow ?_ _
      have h1 : (⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩ : K) =
          ⟨s', hSK hs'⟩ * z := by rw [hz, mul_inv_cancel_left]
      rw [h1]
      exact (Commute.mul_right (Commute.refl _) (hzc _)).inv_left
    rw [e]
    have h2 : ((⟨s', hSK hs'⟩ : K)⁻¹) ^ p ^ (b + c) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, InvMemClass.coe_inv, Subgroup.coe_one, inv_pow]
      rw [pow_add, pow_mul', hc', one_pow, inv_one]
    have h3 : (⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩ : K) ^ p ^ (b + c) =
        1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [conj_pow, pow_add, pow_mul, hb', one_pow]
      group
    rw [h2, h3, one_mul]
  have hzN : z ^ Nat.card (Subgroup.center K) = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨z, hzZ⟩)
    exact congrArg Subtype.val this
  have hz1 : z = 1 := by
    have hd1 := orderOf_dvd_of_pow_eq_one hzp
    have hd2 := orderOf_dvd_of_pow_eq_one hzN
    have hcop : Nat.Coprime (p ^ (b + c)) (Nat.card (Subgroup.center K)) :=
      Nat.Coprime.pow_left _ hZ
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have : (⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩ : K) = ⟨s', hSK hs'⟩ := by
    have h1 : (⟨k * s * k⁻¹, mul_mem (mul_mem hk (hSK hs)) (inv_mem hk)⟩ : K) =
        ⟨s', hSK hs'⟩ * z := by rw [hz, mul_inv_cancel_left]
    rw [h1, hz1, mul_one]
  have h := congrArg Subtype.val this
  simp only at h
  rw [h]
  exact hs'

theorem conj_comm_eq {R : Type*} [Group R] (q : R) (ψ : MulAut R) :
    MulAut.conj q * ψ * (MulAut.conj q)⁻¹ * ψ⁻¹ = MulAut.conj (q * (ψ q)⁻¹) := by
  have h := D4Rank.mulAut_mul_conj ψ q⁻¹
  calc MulAut.conj q * ψ * (MulAut.conj q)⁻¹ * ψ⁻¹
      = MulAut.conj q * ((ψ * MulAut.conj q⁻¹) * ψ⁻¹) := by rw [map_inv]; group
    _ = MulAut.conj q * MulAut.conj (ψ q⁻¹) := by rw [h, mul_inv_cancel_right]
    _ = MulAut.conj (q * (ψ q)⁻¹) := by rw [← map_mul, map_inv]

end Lift

end L45RankX

@[expose] def GGRawFieldCommRank (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ f ∈ F, orderOf f = p → ∀ u ∈ I, ∀ E : Subgroup (MulAut R), IsElemAbelian p E →
      p ^ 2 ≤ Nat.card E → (∀ e ∈ E, e ∈ I) → (∀ e ∈ E, e * (u * f * u⁻¹) = u * f * u⁻¹ * e) →
      (∀ r : R, MulAut.conj r ^ p = 1 → (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) →
        MulAut.conj r * (u * f * u⁻¹) = u * f * u⁻¹ * MulAut.conj r → MulAut.conj r ∈ E) →
      ∀ Q : Subgroup R, IsPGroup p Q →
        (∀ q ∈ Q, ∀ e ∈ E, MulAut.conj q * e = e * MulAut.conj q) →
        (∀ q ∈ Q, (u * f * u⁻¹) q ∈ Q) →
        (∀ r : R, (∃ k : ℕ, r ^ p ^ k = 1) →
          (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) → (∀ q ∈ Q, r * q * r⁻¹ ∈ Q) →
          r ∈ Q) →
        ∃ q₁ ∈ Q, ∃ q₂ ∈ Q,
          (q₁ * ((u * f * u⁻¹)⁻¹ q₁)⁻¹) ^ p = 1 ∧ (q₂ * ((u * f * u⁻¹)⁻¹ q₂)⁻¹) ^ p = 1 ∧
          ∀ i j : ℕ, (q₁ * ((u * f * u⁻¹)⁻¹ q₁)⁻¹) ^ i * (q₂ * ((u * f * u⁻¹)⁻¹ q₂)⁻¹) ^ j = 1 →
            p ∣ i ∧ p ∣ j

@[expose] def GGL45RankXKGLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank)

@[expose] def GGRawFieldCommRankOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S lab →
    LargeEvenLabelAll lab (GGRawFieldCommRank p)

@[expose] def GGL45RankXRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ →
    (¬ Nat.Coprime p (Nat.card (Subgroup.center K)) ∨
      LargeEvenMarking K (fun lab _ _ I F θ => ¬ GGL45RankXKGLabel lab ∧
        (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
          LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
        ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
          LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))) →
      ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁,
        (a₁ * x * a₁⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        (a₂ * x * a₂⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
        ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j ∈
          U ⊓ Subgroup.centralizer (K : Set G) → p ∣ i ∧ p ∣ j

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.rankX_of_commRank (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcent : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d)
    (hZ : Nat.Coprime p (Nat.card (Subgroup.center K))) {R : Type} [Group R]
    {I F : Set (MulAut R)} (θ : K ⧸ Subgroup.center K ≃* R) (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) (hRIF : GGRawInnField p R I F)
    (hKG : GGRawFieldCommRank p R I F)
    (hB₁I : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
      LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ)
    (hxF : ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
      LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))
    (hiff : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G),
      (u ∈ U₁ ↔ ggLAut K θ ⟨u, hu⟩ ∈ I)) :
    ∃ a₁ ∈ U₁, ∃ a₂ ∈ U₁,
      (a₁ * x * a₁⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
      (a₂ * x * a₂⁻¹ * x⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) ∧
      ∀ i j : ℕ, (a₁ * x * a₁⁻¹ * x⁻¹) ^ i * (a₂ * x * a₂⁻¹ * x⁻¹) ^ j ∈
        U ⊓ Subgroup.centralizer (K : Set G) → p ∣ i ∧ p ∣ j := by
  have hp : p.Prime := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  have hUK := hcfg.le_normalizer
  have hBsU := hcfg.bs_le
  have hKp : commutator K = ⊤ := hcfg.2.2.2.2.2.2.2.1.2.2.1
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  obtain ⟨f, hf, u, hu, hord, hxind⟩ := hxF
  obtain ⟨-, -, hinn, -⟩ := hRIF hs hna
  have hinj := L45RankX.conj_injective_of_simple hs hna
  have hxU : x ∈ U := hBsU hcfg.x_mem
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hUK hxU
  have hψ : u * f * u⁻¹ = ggLAut K θ ⟨x⁻¹, inv_mem hxN⟩ := eq_ggLAut_of_induces K θ hxN hxind
  have hψx : ggLAut K θ ⟨x, hxN⟩ = (u * f * u⁻¹)⁻¹ := by
    rw [hψ, ← map_inv]
    congr 1
    exact Subtype.ext (inv_inv x).symm
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hB₁N : B₁ ≤ Subgroup.normalizer (K : Set G) := fun b hb => hUK (hBsU hb.1)
  set β : B₁ →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hB₁N) with hβ
  set E : Subgroup (MulAut R) := β.range with hEdef
  have hmemE : ∀ e ∈ E, ∃ b ∈ B₁, ∃ hb : b ∈ Subgroup.normalizer (K : Set G),
      ggLAut K θ ⟨b, hb⟩ = e := by
    rintro e ⟨b, rfl⟩
    exact ⟨b, b.2, hB₁N b.2, rfl⟩
  have hEmem : ∀ b ∈ B₁, ∀ hb : b ∈ Subgroup.normalizer (K : Set G), ggLAut K θ ⟨b, hb⟩ ∈ E :=
    fun b hb _ => ⟨⟨b, hb⟩, rfl⟩
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨b₁, hb₁, hb₁N, hab⟩ := hmemE a a.2
      obtain ⟨b₂, hb₂, hb₂N, hbb⟩ := hmemE b b.2
      show (a : MulAut R) * b = b * a
      rw [← hab, ← hbb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian hb₁.1 hb₂.1)
    · obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
      have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
        Subtype.ext (by simpa using hcfg.isElemAbelian.2 b hb.1)
      rw [← map_pow, h1, map_one]
  have hEI : ∀ e ∈ E, e ∈ I := by
    intro e he
    obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
    exact ggLAut_mem_of_induces K θ hB₁N hB₁I hb
  have hEψ : ∀ e ∈ E, e * (u * f * u⁻¹) = u * f * u⁻¹ * e := by
    intro e he
    obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
    rw [hψ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian hb.1
      (inv_mem hcfg.x_mem))
  have hE2 : p ^ 2 ≤ Nat.card E := by
    have hI := hcfg.1.1.1
    have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.2.1.1.2.1
    have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.1.2.2.2
    have hB4 : p ^ 4 ≤ Nat.card Bs := by
      calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.1.1.2.1.1
    have h43 : GGL43 Bs x X := hcfg.2.2.1
    have hx1 : x ≠ 1 := fun h => h43.1 (h ▸ one_mem _)
    have hle := card_bstar_le_of_ggL43 hcfg.isElemAbelian hcfg.x_mem hx1 h43
    have hker : Nat.card β.ker ≤ p := by
      have hle' : β.ker.map B₁.subtype ≤ Subgroup.zpowers d := by
        rintro _ ⟨b, hb, rfl⟩
        refine hcent ⟨b.2, ?_⟩
        have hb' : ggLAut K θ ⟨b, hB₁N b.2⟩ = 1 := hb
        exact mem_centralizer_of_ggLAut_eq_one K θ hKp hb'
      calc Nat.card β.ker = Nat.card (β.ker.map B₁.subtype) :=
            (Subgroup.card_map_of_injective B₁.subtype_injective).symm
        _ ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_of_le hle'
        _ = p := by rw [Nat.card_zpowers, orderOf_eq_prime hcfg.d_pow hcfg.d_ne]
    have hcard := Subgroup.card_ker_mul_card_range β
    have hp1 := hp.one_lt
    have h3 : p ^ 3 ≤ Nat.card B₁ := by
      have : p ^ 4 ≤ Nat.card B₁ * p := hB4.trans hle
      have e : p ^ 4 = p ^ 3 * p := by ring
      rw [e] at this
      exact Nat.le_of_mul_le_mul_right this (by omega)
    by_contra hlt
    push Not at hlt
    have h4 : Nat.card B₁ ≤ p * Nat.card E := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ hker
    have h5 : p * Nat.card E < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hp.pos
    have e : p * p ^ 2 = p ^ 3 := by ring
    omega
  have hH2 : ∀ r : R, MulAut.conj r ^ p = 1 →
      (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) →
      MulAut.conj r * (u * f * u⁻¹) = u * f * u⁻¹ * MulAut.conj r → MulAut.conj r ∈ E := by
    intro r hrp hrE hrψ
    have hrp' : r ^ p ^ 1 = 1 := by
      rw [pow_one]
      apply hinj
      rw [map_pow, hrp, map_one]
    obtain ⟨k, hkp, hkr⟩ := L45RankX.exists_lift_of_coprime (θ := θ) hp hZ hrp'
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have hρk : ggLAut K θ ⟨k, hkN⟩ = MulAut.conj r := by
      rw [← hkr]
      exact ggLAut_mk_self K θ k
    have hkp' : (k : G) ^ p = 1 := by simpa using congrArg Subtype.val hkp
    have hcomm : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)),
        ggLAut K θ ⟨g, hg⟩ * MulAut.conj r = MulAut.conj r * ggLAut K θ ⟨g, hg⟩ →
        g ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
      intro g hg h
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine commute_of_ggLAut_commute (θ := θ) hKp hZ k.2 hkp' hg ?_
      rw [hρk]
      exact h
    have hB₁k : B₁ ≤ Subgroup.centralizer ({(k : G)} : Set G) :=
      fun b hb => hcomm b (hB₁N hb) (hrE _ (hEmem b hb (hB₁N hb))).symm
    have hxk : x ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
      refine hcomm x hxN ?_
      rw [hψx]
      exact ((Commute.inv_right hrψ).eq).symm
    have hBsk : Bs ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
      rw [hcfg.2.2.1.2]
      exact sup_le hB₁k (Subgroup.zpowers_le.mpr hxk)
    have hkC : (k : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hBsk hb)
    have hkBs : (k : G) ∈ Bs := hcfg.bstar_max k hkC hkp'
    have hkU₁ : (k : G) ∈ U₁ := (hiff k (hBsU hkBs) hkN).mpr (by rw [hρk]; exact hinn _)
    have hkB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hkBs, hkU₁⟩
    rw [← hρk]
    exact hEmem k hkB₁ hkN
  set H₀ : Subgroup G := K ⊓ Subgroup.centralizer (B₁ : Set G) with hH₀
  have hUC := hcfg.le_centralizer
  have hUH₀ : U ≤ Subgroup.normalizer (H₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hK, hC⟩
      have hgC : g ∈ Subgroup.centralizer (B₁ : Set G) := hUC hg
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hUK hg) h).mp hK,
        (Subgroup.centralizer (B₁ : Set G)).mul_mem
          ((Subgroup.centralizer (B₁ : Set G)).mul_mem hgC hC)
          ((Subgroup.centralizer (B₁ : Set G)).inv_mem hgC)⟩
    · rintro ⟨hK, hC⟩
      have hgC : g ∈ Subgroup.centralizer (B₁ : Set G) := hUC hg
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hUK hg) h).mpr hK, ?_⟩
      have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [e]
      exact (Subgroup.centralizer (B₁ : Set G)).mul_mem
        ((Subgroup.centralizer (B₁ : Set G)).mul_mem
          ((Subgroup.centralizer (B₁ : Set G)).inv_mem hgC) hC) hgC
  obtain ⟨S, hSH₀, hSp, hUS, hSmax⟩ :=
    L45RankX.exists_sylow_normalized_max H₀ U hcfg.isPGroup hUH₀
  have hSK : S ≤ K := fun s hs => (hSH₀ hs).1
  have hSU : S ≤ U := by
    have hsup : IsPGroup p (U ⊔ S : Subgroup G) := hcfg.isPGroup.to_sup_of_normal_right' hSp hUS
    have hsupC : U ⊔ S ≤ Subgroup.centralizer (B₁ : Set G) :=
      sup_le hUC fun s hs => (hSH₀ hs).2
    have h := hcfg.2.2.2.2.2.2.1.2.2.1 (U ⊔ S) hsupC hsup le_sup_left
    rw [← h]
    exact le_sup_right
  have hSU₁ : ∀ s ∈ S, s ∈ U₁ := fun s hs => by
    refine (hiff s (hSU hs) (hUK (hSU hs))).mpr ?_
    have e := ggLAut_mk_self K θ ⟨s, hSK hs⟩
    rw [e]
    exact hinn _
  set Q : Subgroup R :=
    (S.subgroupOf K).map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) with hQ
  have hmemQ : ∀ q ∈ Q, ∃ s ∈ S, ∃ hsK : s ∈ K,
      θ ((⟨s, hsK⟩ : K) : K ⧸ Subgroup.center K) = q := by
    rintro q ⟨k, hk, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mp hk, k.2, rfl⟩
  have hQmem : ∀ s ∈ S, ∀ hsK : s ∈ K, θ ((⟨s, hsK⟩ : K) : K ⧸ Subgroup.center K) ∈ Q :=
    fun s hs hsK => ⟨⟨s, hsK⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hQp : IsPGroup p Q :=
    (hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm).map _
  have hQE : ∀ q ∈ Q, ∀ e ∈ E, MulAut.conj q * e = e * MulAut.conj q := by
    intro q hq e he
    obtain ⟨s, hs, hsK, rfl⟩ := hmemQ q hq
    obtain ⟨b, hb, hbN, rfl⟩ := hmemE e he
    rw [← ggLAut_mk_self K θ ⟨s, hsK⟩, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hSH₀ hs).2 b hb).symm
  have hQψ : ∀ q ∈ Q, (u * f * u⁻¹) q ∈ Q := by
    intro q hq
    obtain ⟨s, hs, hsK, rfl⟩ := hmemQ q hq
    have hs' : x⁻¹ * s * x⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hUS (inv_mem hxU)) s).mp hs
    rw [hψ, ggLAut_apply]
    exact hQmem _ hs' _
  have hQsyl : ∀ r : R, (∃ k : ℕ, r ^ p ^ k = 1) →
      (∀ e ∈ E, MulAut.conj r * e = e * MulAut.conj r) → (∀ q ∈ Q, r * q * r⁻¹ ∈ Q) →
      r ∈ Q := by
    rintro r ⟨m, hrm⟩ hrE hrQ
    obtain ⟨k, hkp, hkr⟩ := L45RankX.exists_lift_of_coprime (θ := θ) hp hZ hrm
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have hρk : ggLAut K θ ⟨k, hkN⟩ = MulAut.conj r := by
      rw [← hkr]
      exact ggLAut_mk_self K θ k
    have hkp' : (k : G) ^ p ^ m = 1 := by simpa using congrArg Subtype.val hkp
    have hkC : (k : G) ∈ Subgroup.centralizer (B₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      refine commute_of_ggLAut_commute (θ := θ) hKp (Nat.Coprime.pow_left m hZ) k.2 hkp'
        (hB₁N hb) ?_
      rw [hρk]
      exact (hrE _ (hEmem b hb (hB₁N hb))).symm
    have hconj : ∀ s ∈ S, (k : G) * s * (k : G)⁻¹ ∈ S := by
      intro s hs
      obtain ⟨s', hs', hs'K, heq⟩ := hmemQ _ (hrQ _ (hQmem s hs (hSK hs)))
      refine L45RankX.conj_mem_of_mk_eq hZ hSK hSp k.2 ⟨m, hkp'⟩ hs hs' ?_
      apply θ.injective
      have e : (⟨(k : G) * s * (k : G)⁻¹, mul_mem (mul_mem k.2 (hSK hs)) (inv_mem k.2)⟩ : K) =
          k * ⟨s, hSK hs⟩ * k⁻¹ := Subtype.ext rfl
      rw [e, heq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
        map_mul, map_inv, hkr]
    have hkS : (k : G) ∈ Subgroup.normalizer (S : Set G) := by
      have h := mem_normalizer_of_forall_conj_mem (W := S) (g := (k : G)⁻¹) fun s hs => by
        rw [inv_inv]
        exact hconj s hs
      simpa using inv_mem h
    have hkzp : IsPGroup p (Subgroup.zpowers (k : G)) :=
      IsPGroup.of_card_dvd_pow (n := m) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hkp')
    have hsup : IsPGroup p (Subgroup.zpowers (k : G) ⊔ S : Subgroup G) :=
      hkzp.to_sup_of_normal_right' hSp (Subgroup.zpowers_le.mpr hkS)
    have hle : Subgroup.zpowers (k : G) ⊔ S ≤ H₀ :=
      sup_le (Subgroup.zpowers_le.mpr ⟨k.2, hkC⟩) hSH₀
    have heqS := hSmax _ le_sup_right hle hsup
    have hkS' : (k : G) ∈ S := by
      rw [← heqS]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    rw [← hkr]
    exact hQmem _ hkS' k.2
  obtain ⟨q₁, hq₁, q₂, hq₂, hc₁, hc₂, hind⟩ :=
    hKG hs hna f hf hord u hu E hEab hE2 hEI hEψ hH2 Q hQp hQE hQψ hQsyl
  obtain ⟨s₁, hs₁, hs₁K, rfl⟩ := hmemQ q₁ hq₁
  obtain ⟨s₂, hs₂, hs₂K, rfl⟩ := hmemQ q₂ hq₂
  have hwU : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ U := fun s hs =>
    mul_mem (mul_mem (mul_mem (hSU hs) hxU) (inv_mem (hSU hs))) (inv_mem hxU)
  have hρw : ∀ (s : G) (hsS : s ∈ S) (hsK : s ∈ K),
      ggLAut K θ ⟨s * x * s⁻¹ * x⁻¹, hUK (hwU s hsS)⟩ =
        MulAut.conj (θ ((⟨s, hsK⟩ : K) : K ⧸ Subgroup.center K) *
          ((u * f * u⁻¹)⁻¹ (θ ((⟨s, hsK⟩ : K) : K ⧸ Subgroup.center K)))⁻¹) := by
    intro s hsS hsK
    have e : (⟨s * x * s⁻¹ * x⁻¹, hUK (hwU s hsS)⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨s, Subgroup.le_normalizer hsK⟩ * ⟨x, hxN⟩ *
          (⟨s, Subgroup.le_normalizer hsK⟩ : Subgroup.normalizer (K : Set G))⁻¹ *
          (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ggLAut_mk_self K θ ⟨s, hsK⟩, hψx]
    exact L45RankX.conj_comm_eq _ _
  have hC : ∀ (s : G) (hsS : s ∈ S) (hsK : s ∈ K) (n : ℕ),
      ggLAut K θ ⟨(s * x * s⁻¹ * x⁻¹) ^ n, hUK (pow_mem (hwU s hsS) n)⟩ =
        MulAut.conj ((θ ((⟨s, hsK⟩ : K) : K ⧸ Subgroup.center K) *
          ((u * f * u⁻¹)⁻¹ (θ ((⟨s, hsK⟩ : K) : K ⧸ Subgroup.center K)))⁻¹) ^ n) := by
    intro s hsS hsK n
    have e : (⟨(s * x * s⁻¹ * x⁻¹) ^ n, hUK (pow_mem (hwU s hsS) n)⟩ :
        Subgroup.normalizer (K : Set G)) = ⟨s * x * s⁻¹ * x⁻¹, hUK (hwU s hsS)⟩ ^ n :=
      Subtype.ext (by simp)
    rw [e, map_pow, hρw s hsS hsK, map_pow]
  refine ⟨s₁, hSU₁ s₁ hs₁, s₂, hSU₁ s₂ hs₂, ?_, ?_, fun i j hij => hind i j ?_⟩
  · refine ⟨pow_mem (hwU s₁ hs₁) p, mem_centralizer_of_ggLAut_eq_one K θ hKp
      (g := ⟨_, hUK (pow_mem (hwU s₁ hs₁) p)⟩) ?_⟩
    rw [hC s₁ hs₁ hs₁K p, hc₁, map_one]
  · refine ⟨pow_mem (hwU s₂ hs₂) p, mem_centralizer_of_ggLAut_eq_one K θ hKp
      (g := ⟨_, hUK (pow_mem (hwU s₂ hs₂) p)⟩) ?_⟩
    rw [hC s₂ hs₂ hs₂K p, hc₂, map_one]
  · apply hinj
    have h1 : ggLAut K θ ⟨(s₁ * x * s₁⁻¹ * x⁻¹) ^ i * (s₂ * x * s₂⁻¹ * x⁻¹) ^ j, hUK hij.1⟩ = 1 :=
      ggLAut_of_mem_centralizer_outdiag K θ hij.2
    have e : (⟨(s₁ * x * s₁⁻¹ * x⁻¹) ^ i * (s₂ * x * s₂⁻¹ * x⁻¹) ^ j, hUK hij.1⟩ :
        Subgroup.normalizer (K : Set G)) =
        ⟨(s₁ * x * s₁⁻¹ * x⁻¹) ^ i, hUK (pow_mem (hwU s₁ hs₁) i)⟩ *
          ⟨(s₂ * x * s₂⁻¹ * x⁻¹) ^ j, hUK (pow_mem (hwU s₂ hs₂) j)⟩ := Subtype.ext rfl
    rw [e, map_mul, hC s₁ hs₁ hs₁K i, hC s₂ hs₂ hs₂K j, ← map_mul] at h1
    rw [h1, map_one]

end Config

theorem ggL45RankXInput_of_commRank (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hKG : GGRawFieldCommRankOn GGL45RankXKGLabel)
    (hres : GGL45RankXRestInput) : GGL45RankXInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  by_cases hZ : Nat.Coprime p (Nat.card (Subgroup.center K))
  · obtain ⟨hperf, lab, hlab, hraw1⟩ := hcfg.2.2.2.2.2.1.2.2.2.2
    by_cases hlabKG : GGL45RankXKGLabel lab
    · have hM0 : LargeEvenMarking K (fun lab _ _ I F θ => GGL45RankXKGLabel lab ∧
          (Bs ≤ Subgroup.normalizer (K : Set G) ∧
            (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
              LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
            ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
              LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))) :=
        ⟨hperf, lab, hlab, largeEvenRawDatum_mono
          (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hlabKG, hP⟩) hraw1⟩
      have hM1 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
        (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hM0
      have hM1' := largeEvenMarking_and_labelAll (S := GGL45RankXKGLabel)
        (P' := GGRawFieldCommRank p) (fun lab hl hS => hKG p hp hp2 lab hl hS)
        (fun _ _ _ _ _ _ h => h.1.1) hM1
      have hM1'' := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
        (P' := GGRawInndiagIso) (fun lab hl _ => hiso lab hl) (fun _ _ _ _ _ _ _ => trivial) hM1'
      obtain ⟨-, lab₁, -, hraw₁⟩ := hM1''
      obtain ⟨R, _, I, F, hs, hna, θ, ⟨⟨⟨-, -, hB₁I, hxF⟩, hRIF⟩, hCR⟩, hisoR⟩ :=
        largeEvenRawDatum_exists hraw₁
      have hpart := hcfg.2.2.2.2.2.2.2.1
      have hM2 := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
        (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hpart.2.2
      obtain ⟨-, lab', hlab', hraw2⟩ := hM2
      obtain ⟨R', _, I', F', ⟨hs', hna', θ', hU₁iff, hR'⟩, hisoRR'⟩ :=
        largeEvenRawDatum_exists (hisoR lab' hlab' _ hraw2)
      obtain ⟨hmul, hinv, hinn, -⟩ := hRIF hs hna
      obtain ⟨hmul', hinv', hinn', -⟩ := hR' hs' hna'
      refine hcfg.rankX_of_commRank hraw hiso (hcent G p B Bs x L D J X B₂ d y K U U₁ hcfg) hZ θ
        hs hna hRIF hCR hB₁I hxF fun u hu huN => ?_
      rw [hU₁iff u hu, ggL45_exists_induces_iff hinv' huN,
        ← ggL45_mem_ggInndiag_iff hmul' hinv' hinn', ← ggL45_mem_ggInndiag_iff hmul hinv hinn,
        hisoRR' hs' hna' (θ.symm.trans θ'), ← ggLAut_congr]
    · exact hres G p B Bs x L D J X B₂ d y K U U₁ hcfg (Or.inr ⟨hperf, lab, hlab,
        largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _, hB₁I, hxF⟩ =>
          ⟨hs, hna, θ, hlabKG, hB₁I, hxF⟩) hraw1⟩)
  · exact hres G p B Bs x L D J X B₂ d y K U U₁ hcfg (Or.inl hZ)

end CFSG.StandardType
