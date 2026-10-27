module

public import CFSG.Quasithin.H13.A5S1521a
public import CFSG.Quasithin.H13.A5S1521b
public import CFSG.Quasithin.H13.A5S1521r
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.A3StructureBasic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.InternalSec
open scoped commutatorElement

section Coprime

variable {W : Type} [CommGroup W]

theorem fix_of_odd_of_fix_comm (hW : ∀ w : W, w ^ 2 = 1) {z : MulAut W} {m : ℕ} (hm : Odd m)
    (hzm : z ^ m = 1) {w : W} (h : z (z w * w⁻¹) = z w * w⁻¹) : z w = w := by
  set d := z w * w⁻¹ with hd
  have hzw : z w = d * w := by rw [hd, inv_mul_cancel_right]
  have hn : ∀ n : ℕ, (z ^ n) w = d ^ n * w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, h, hzw, ← mul_assoc, ← pow_succ]
  have h1 : d ^ m = 1 := by
    have := hn m
    rw [hzm, MulAut.one_apply] at this
    exact mul_eq_right.mp this.symm
  have h2 : d = 1 := by
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, hW d, one_pow, one_mul] at h1
    exact h1
  rw [hzw, h2, one_mul]

variable [Finite W]

@[expose] noncomputable def normZ (Z : Subgroup (MulAut W)) [Fintype ↥Z] : W →* W where
  toFun w := ∏ z : ↥Z, (z : MulAut W) w
  map_one' := by simp
  map_mul' a c := by simp only [map_mul, Finset.prod_mul_distrib]

omit [Finite W] in
theorem normZ_apply (Z : Subgroup (MulAut W)) [Fintype ↥Z] (w : W) :
    normZ Z w = ∏ z : ↥Z, (z : MulAut W) w := rfl

omit [Finite W] in
theorem normZ_comm (Z : Subgroup (MulAut W)) [Fintype ↥Z] {z : MulAut W} (hz : z ∈ Z)
    (w : W) : normZ Z (z w * w⁻¹) = 1 := by
  rw [map_mul, map_inv, mul_inv_eq_one, normZ_apply, normZ_apply]
  exact Fintype.prod_equiv (Equiv.mulRight ⟨z, hz⟩) _ _ (fun x => by simp [MulAut.mul_apply])

omit [Finite W] in
theorem normZ_of_fix (Z : Subgroup (MulAut W)) [Fintype ↥Z] {w : W}
    (hw : ∀ z ∈ Z, z w = w) : normZ Z w = w ^ Fintype.card ↥Z := by
  rw [normZ_apply]
  have : ∀ z : ↥Z, (z : MulAut W) w = w := fun z => hw z z.2
  simp only [this, Finset.prod_const, Finset.card_univ]

theorem eq_one_of_mem_commSubOf_of_fix (hW : ∀ w : W, w ^ 2 = 1) (Z : Subgroup (MulAut W))
    (hZ : Odd (Nat.card ↥Z)) {w : W} (hw : w ∈ commSubOf ⊤ Z) (hfix : ∀ z ∈ Z, z w = w) :
    w = 1 := by
  classical
  have := Fintype.ofFinite ↥Z
  have h1 : commSubOf ⊤ Z ≤ (normZ Z).ker := by
    rw [commSubOf, Subgroup.closure_le]
    rintro _ ⟨z, hz, u, -, rfl⟩
    exact normZ_comm Z hz u
  have h2 := h1 hw
  rw [MonoidHom.mem_ker, normZ_of_fix Z hfix] at h2
  rw [Nat.card_eq_fintype_card] at hZ
  obtain ⟨k, hk⟩ := hZ
  rw [hk, pow_succ, pow_mul, hW w, one_pow, one_mul] at h2
  exact h2

omit [Finite W] in
theorem eq_bot_of_fix_commSubOf (hW : ∀ w : W, w ^ 2 = 1) (Z : Subgroup (MulAut W))
    (hZ : Odd (Nat.card ↥Z)) (hfix : ∀ z ∈ Z, ∀ u ∈ commSubOf ⊤ Z, z u = u) : Z = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzm : z ^ Nat.card ↥Z = 1 := by
    have := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val this
  ext w
  rw [MulAut.one_apply]
  exact fix_of_odd_of_fix_comm hW hZ hzm (hfix z hz _ (mem_commSubOf hz (Subgroup.mem_top w)))

end Coprime


theorem eq_zero_or_eq_one_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (x : F) : x = 0 ∨ x = 1 := by
  set e := G64.ringEquivZModTwo F hF
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h (e x) with h0 | h1
  · left
    rw [← e.symm_apply_apply x, h0, map_zero]
  · right
    rw [← e.symm_apply_apply x, h1, map_one]

theorem center_sl_card_two (n : ℕ) [NeZero n] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hn : Fintype.card (Fin n) ≠ 0 := Fintype.card_pos.ne'
  have hr1 : r = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hF r with h0 | h1
    · rw [h0, zero_pow hn] at hr
      exact absurd hr zero_ne_one
    · exact h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have h2 : (Matrix.scalar (Fin n) r : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [hr1, map_one]
  exact hA'.symm.trans h2

theorem isSimpleGroup_statedSL_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := by
  have h := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega)
    (Or.inl le_rfl)).2.1
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (QuotientGroup.quotientMulEquivOfEq (center_sl_card_two 3 hF)).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) F) := e.symm.isSimpleGroup
  exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.isSimpleGroup

theorem injective_of_surjective_of_simple' {Γ H : Type} [Group Γ] [Group H] [IsSimpleGroup Γ]
    [Nontrivial H] (π : Γ →* H) (hπ : Function.Surjective π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · have h1 : g ∈ π.ker := hg
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (1 : H)
    obtain ⟨x, rfl⟩ := hπ a
    exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))

theorem isSimpleGroup_of_surjective {Γ H : Type} [Group Γ] [Group H] [IsSimpleGroup Γ]
    [Nontrivial H] (π : Γ →* H) (hπ : Function.Surjective π) : IsSimpleGroup H :=
  (MulEquiv.ofBijective π ⟨injective_of_surjective_of_simple' π hπ, hπ⟩).symm.isSimpleGroup

theorem Outcome1321.isSimpleGroup (hR : FactRankRows1321) {V : Type}
    [CommGroup V] [Finite V] (hV : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hB4 : B4Hyp G L) (h : Outcome1321 G L) : IsSimpleGroup ↥L := by
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hB4.2.2.1
  rcases h with ⟨π, hπ⟩ | ⟨F, _, _, hF2, π, hπ⟩ | ⟨A, hA⟩
  · have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact isSimpleGroup_of_surjective π hπ
  · have := isSimpleGroup_statedSL_three hF2
    exact isSimpleGroup_of_surjective π hπ
  · exact (hR V hV G L A hB4 hA).1


theorem odd_card_center {K : Type} [Group K] [Finite K] (hO : CFSG.Open.pCore 2 K = ⊥) :
    Odd (Nat.card (Subgroup.center K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (Subgroup.center K) := by omega
  have := Fintype.ofFinite ↥(Subgroup.center K)
  rw [Nat.card_eq_fintype_card] at h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hzc : (z : K) ∈ Subgroup.center K := z.2
  have hnorm : (Subgroup.zpowers (z : K)).Normal := ⟨fun n hn g => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzc i) g
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ i⟩
  have hp : IsPGroup 2 (Subgroup.zpowers (z : K)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
  have := CFSG.LieType.BorelTits.le_pCore 2 hnorm hp (Subgroup.mem_zpowers (z : K))
  rw [hO, Subgroup.mem_bot] at this
  have h1 : orderOf z = 1 := by
    rw [orderOf_eq_one_iff]
    exact Subtype.ext this
  rw [hz] at h1
  exact absurd h1 (by norm_num)

section Pkg

variable (Y : Type) [Group Y] [Finite Y] (W : Type) [CommGroup W] [Finite W]

structure Hyp1321 where
  ρ : Y →* MulAut W
  inj : Function.Injective ρ
  sq : ∀ w : W, w ^ 2 = 1
  sqtk : SQTKHyp Y
  K : Subgroup Y
  comp : IsComponentOf K ⊤
  b : Y
  b2 : b * b = 1
  bN : b ∈ Subgroup.normalizer (K : Set Y)
  bc : ∃ k ∈ K, k * b ≠ b * k
  D : Subgroup W
  hD : ∀ w : W, ρ b w * w⁻¹ ∈ D
  hD4 : Nat.card D ≤ 4
  syl : ∃ S : Subgroup Y, IsSylowTwoOf S K ∧ ∀ s ∈ S, s * b = b * s
  pair : ∀ x : Y, (∃ k : ℕ, (b * (x * b * x⁻¹)) ^ 2 ^ k = 1) ∨ (b * (x * b * x⁻¹)) ^ 3 = 1

variable {Y W}

namespace Hyp1321

variable (P : Hyp1321 Y W)
include P

omit [Finite Y] [Finite W] in
theorem quasi : CFSG.IsQuasisimple ↥P.K := (isComponent_of_isComponentOf_top P.comp).1

omit [Finite Y] [Finite W] in
theorem pCore_K : CFSG.Open.pCore 2 ↥P.K = ⊥ := by
  have h := P.sqtk.pCoreOf_two_of_subnormal P.comp.2.1
  rw [pCoreOf] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ P.K.subtype_injective).mp h

omit [Finite W] in
theorem sqtkK : SQTKGroup ↥P.K := sqtkGroup_subgroup ⟨P.sqtk.sqt, P.sqtk.kgroup⟩ P.K

theorem chief
    {U0 : Subgroup W} (hU0 : ∀ x ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U0, P.ρ x u ∈ U0)
    (hU0K : ∃ k ∈ P.K, ∃ u ∈ U0, P.ρ k u ≠ u) :
    ∃ (U1 U2 : Subgroup W) (h1 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U1, P.ρ y u ∈ U1)
      (h2 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U2, P.ρ y u ∈ U2),
      U2 < U1 ∧ U1 ≤ U0 ∧ (∀ k ∈ P.K, ∀ u ∈ U2, P.ρ k u = u) ∧
      commSubOf U1 (P.K.map P.ρ) = U1 ∧
      (∀ J : Subgroup W, (∀ k ∈ P.K, ∀ u ∈ J, P.ρ k u ∈ J) → U2 ≤ J → J ≤ U1 →
        J = U2 ∨ J = U1) ∧
      B4Hyp (secAct P.ρ _ h1 h2).range
        ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2)) ∧
      Cond1321 (secAct P.ρ _ h1 h2).range
        ((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2))
        (secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩) :=
  exists_chief_b4 P.ρ P.inj P.sq P.quasi P.pCore_K P.sqtkK P.b2 P.bN P.bc P.hD P.hD4 P.syl
    (fun x _ => P.pair x) hU0 hU0K


omit [Finite Y] [Finite W] in
theorem chiefSec_sq (U1 U2 : Subgroup W) (w : ChiefSec U1 U2) : w ^ 2 = 1 := by
  obtain ⟨u, rfl⟩ := chiefQ_surjective U1 U2 w
  rw [← map_pow]
  have : u ^ 2 = 1 := Subtype.ext (by simpa using P.sq u)
  rw [this, map_one]

theorem center_eq_bot
    (hF : Facts1321) (hR : FactRankRows1321) :
    Subgroup.center ↥P.K = ⊥ := by
  classical
  by_contra hZ
  set f : ↥P.K →* MulAut W := P.ρ.comp P.K.subtype with hf
  have hinj : Function.Injective f := P.inj.comp P.K.subtype_injective
  set Z : Subgroup (MulAut W) := (Subgroup.center ↥P.K).map f with hZdef
  have hZodd' := odd_card_center P.pCore_K
  have hZodd : Odd (Nat.card ↥Z) := by
    rw [hZdef, Subgroup.card_map_of_injective hinj]
    exact hZodd'
  have hZne : Z ≠ ⊥ := fun h => hZ ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h)
  have hK'N : P.K ⊔ Subgroup.zpowers P.b ≤ Subgroup.normalizer (P.K : Set Y) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr P.bN)
  have hZn : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ z ∈ Z, P.ρ y * z * (P.ρ y)⁻¹ ∈ Z := by
    rintro y hy _ ⟨c, hc, rfl⟩
    have hyK : y * (c : Y) * y⁻¹ ∈ P.K :=
      (Subgroup.mem_normalizer_iff.mp (hK'N hy) c).mp c.2
    refine ⟨⟨_, hyK⟩, ?_, ?_⟩
    · show (⟨_, hyK⟩ : ↥P.K) ∈ Subgroup.center ↥P.K
      rw [Subgroup.mem_center_iff]
      intro g
      have hg' : y⁻¹ * (g : Y) * y ∈ P.K := by
        have := (Subgroup.mem_normalizer_iff.mp (hK'N (Subgroup.inv_mem _ hy)) g).mp g.2
        simpa using this
      have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨_, hg'⟩)
      simp only [Subgroup.coe_mul] at hcomm
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (g : Y) * (y * c * y⁻¹) = y * ((y⁻¹ * g * y) * c) * y⁻¹ := by group
        _ = y * (c * (y⁻¹ * g * y)) * y⁻¹ := by rw [hcomm]
        _ = y * c * y⁻¹ * g := by group
    · simp [hf, map_mul, map_inv]
  set U0 : Subgroup W := commSubOf ⊤ Z with hU0
  have hU0X : ∀ x ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U0, P.ρ x u ∈ U0 := fun x hx =>
    maps_commSubOf (hZn x hx) (fun u _ => Subgroup.mem_top _)
  have hU0K : ∃ k ∈ P.K, ∃ u ∈ U0, P.ρ k u ≠ u := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hZne
    refine eq_bot_of_fix_commSubOf P.sq Z hZodd fun z hz u hu => ?_
    obtain ⟨c, -, rfl⟩ := hz
    exact hall c c.2 u hu
  obtain ⟨U1, U2, h1, h2, hU21, hU1U0, hfix, -, -, hB4, hc⟩ := P.chief hU0X hU0K
  obtain ⟨c, hcZ, hc1⟩ : ∃ c : ↥P.K, c ∈ Subgroup.center ↥P.K ∧
      secAct P.ρ _ h1 h2 ⟨c, Subgroup.mem_sup_left c.2⟩ ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hU1 : ∀ u ∈ U1, u = 1 := by
      intro u hu
      refine eq_one_of_mem_commSubOf_of_fix P.sq Z hZodd (hU1U0 hu) ?_
      rintro _ ⟨c, hc, rfl⟩
      have h := (secAct_eq_one_iff P.ρ _ h1 h2 _).mp (hall c hc) u hu
      have hodd : Odd (orderOf c) := by
        have h1 : orderOf (⟨c, hc⟩ : ↥(Subgroup.center ↥P.K)) ∣
            Nat.card ↥(Subgroup.center ↥P.K) := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hZodd' h1
      have hpow : (P.ρ c) ^ orderOf c = 1 := by
        rw [← map_pow, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
      exact fix_of_odd_of_fix_comm P.sq hodd hpow (hfix c c.2 _ h)
    obtain ⟨u, hu1, hu2⟩ : ∃ u ∈ U1, u ∉ U2 := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      exact absurd (lt_of_lt_of_le hU21 h) (lt_irrefl _)
    exact hu2 (by rw [hU1 u hu1]; exact U2.one_mem)
  have hsimp := Outcome1321.isSimpleGroup hR (chiefSec_sq P U1 U2) hB4
    (rows1321 hF (chiefSec_sq P U1 U2) hB4 hc)
  set ψ := secAct P.ρ _ h1 h2 with hψ
  have hcL : ψ ⟨c, Subgroup.mem_sup_left c.2⟩ ∈
      (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ := ⟨_, c.2, rfl⟩
  have hcen : (⟨_, hcL⟩ : ↥((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ)) ∈
      Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    apply Subtype.ext
    have hk' : (k : Y) ∈ P.K := hk
    have hkc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨k, hk'⟩)
    show ψ k * ψ ⟨c, Subgroup.mem_sup_left c.2⟩ = ψ ⟨c, Subgroup.mem_sup_left c.2⟩ * ψ k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hkc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center
    ↥((P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ)) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact hc1 (congrArg Subtype.val hcen)
  · obtain ⟨-, -, a, a', haa⟩ := hB4.2.2.1
    apply haa
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [h]
    exact Subgroup.mem_top _

end Hyp1321

end Pkg

end CFSG.Quasithin.H13.A5
