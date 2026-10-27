module

public import CFSG.Walter.W67.Section5.P56Series
public import CFSG.Walter.W67.Section5.Free
public import CFSG.Walter.Bender1970.S1.FixedPointFree
public import CFSG.GroupTheory.SolvableHallNodes
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Walter.W67

namespace Sec56

variable {Γ N : Type} [Group Γ] [Group N] [MulDistribMulAction Γ N]

@[reducible, expose] def restrictAct (R : Subgroup Γ) (A : Subgroup N)
    (hA : ∀ g : Γ, ∀ a ∈ A, g • a ∈ A) : MulDistribMulAction R A where
  smul r a := ⟨(r : Γ) • (a : N), hA r a a.2⟩
  one_smul a := Subtype.ext (one_smul Γ (a : N))
  mul_smul r s a := Subtype.ext (mul_smul (r : Γ) (s : Γ) (a : N))
  smul_mul r a b := Subtype.ext (smul_mul' (r : Γ) (a : N) (b : N))
  smul_one r := Subtype.ext (smul_one (r : Γ))

variable [Finite Γ] [Finite N]

theorem eq_one_of_fixed_factor (A B : Subgroup N) [(B.subgroupOf A).Normal] (hBA : B ≤ A)
    (hA : ∀ g : Γ, ∀ a ∈ A, g • a ∈ A) (hB : ∀ g : Γ, ∀ b ∈ B, g • b ∈ B)
    (hB3 : IsPGroup 3 B) (R : Subgroup Γ) (hR3 : ¬ 3 ∣ Nat.card R)
    (hfixR : ∀ a ∈ A, (∀ r ∈ R, r • a = a) → a = 1)
    (v : A ⧸ B.subgroupOf A) (hv : ∀ r ∈ R, Free.actQuot A B hA hB r v = v) : v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let := restrictAct R A hA
  have hinv : CFSG.IsInvariant R A (B.subgroupOf A) := ⟨fun r a => by
    constructor
    · intro h
      exact hB r a h
    · intro h
      have h1 := hB (r : Γ)⁻¹ _ h
      change (r : Γ)⁻¹ • ((r : Γ) • (a : N)) ∈ B at h1
      rwa [inv_smul_smul] at h1⟩
  have hB'3 : IsPGroup 3 (B.subgroupOf A) :=
    IsPGroup.of_equiv hB3 (Subgroup.subgroupOfEquivOfLe hBA).symm
  have hsolv : Group.IsSolvable (B.subgroupOf A) := by
    have := hB'3.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card R) (Nat.card (B.subgroupOf A)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB'3
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3)))
  have key := SolvableHall.coprime_solvable_kernel_fixed_point_lifting (G := A) (A := R)
    (B.subgroupOf A) hinv hsolv hcop
  let : MulDistribMulAction R (A ⧸ B.subgroupOf A) :=
    quotientMulDistribMulAction (A := R) (G := A) (B.subgroupOf A) hinv
  let : MulAction.QuotientAction R (B.subgroupOf A) :=
    quotientAction_of_isInvariant (A := R) (B.subgroupOf A) hinv
  have hvfix : v ∈ fixedPointSubgroup R (A ⧸ B.subgroupOf A) := by
    induction v using QuotientGroup.induction_on with
    | H a =>
      rw [FixedPoints.mem_subgroup]
      intro r
      have h1 := hv r r.2
      rw [Free.actQuot_mk] at h1
      rw [MulAction.Quotient.smul_coe]
      exact h1
  rw [key] at hvfix
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hvfix
  have ha1 : (a : N) = 1 := hfixR a a.2 fun r hr =>
    congrArg Subtype.val ((FixedPoints.mem_subgroup R A a).mp ha ⟨r, hr⟩)
  have : a = 1 := Subtype.ext ha1
  rw [this, map_one]

theorem mem_zpowers_of_ne_one {x r : Γ} (hx : orderOf x = 3) (hr : r ∈ Subgroup.zpowers x)
    (hr1 : r ≠ 1) : x ∈ Subgroup.zpowers r := by
  have hle : Subgroup.zpowers r ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hr
  have hdvd : Nat.card (Subgroup.zpowers r) ∣ 3 := by
    rw [← hx, ← Nat.card_zpowers x]
    exact Subgroup.card_dvd_of_le hle
  have hcard : Nat.card (Subgroup.zpowers r) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
      exact hr1 h
    · exact h
  have heq : Subgroup.zpowers r = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hx])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem card_fixQuot_pow_three (A B : Subgroup N) [(B.subgroupOf A).Normal] (hBA : B ≤ A)
    (hA : ∀ g : Γ, ∀ a ∈ A, g • a ∈ A) (hB : ∀ g : Γ, ∀ b ∈ B, g • b ∈ B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) (helem : ∀ a ∈ A, a ^ 3 ∈ B)
    (hB3 : IsPGroup 3 B) {x : Γ} (hx : orderOf x = 3) (N₀ : Subgroup Γ)
    (hN₀ab : IsMulCommutative N₀) (hN₀3 : ¬ 3 ∣ Nat.card N₀)
    (hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set Γ)) (hxfpf : ∀ n ∈ N₀, x * n * x⁻¹ = n → n = 1)
    (hfix : ∀ a ∈ A, (∀ r ∈ N₀, r • a = a) → a = 1) :
    Nat.card (Free.fixQuot A B hA hB (Subgroup.zpowers x)) ^ 3 =
      Nat.card (A ⧸ B.subgroupOf A) := by
  let := Free.factorCommGroup A B hcomm
  have hV3 : ∀ v : Additive (A ⧸ B.subgroupOf A), 3 • v = 0 := by
    intro v
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul ((a : A ⧸ B.subgroupOf A)) := by rw [ha]; rfl
    rw [hv, ← ofMul_pow, ← QuotientGroup.mk_pow]
    change Additive.ofMul (((a ^ 3 : A) : A ⧸ B.subgroupOf A)) = Additive.ofMul 1
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact helem a a.2
  let : Module (ZMod 3) (Additive (A ⧸ B.subgroupOf A)) := AddCommGroup.zmodModule hV3
  let ρ : Representation (ZMod 3) Γ (Additive (A ⧸ B.subgroupOf A)) :=
    { toFun := fun g => (Free.factorRep A B hA hB hcomm g).toAddMonoidHom.toZModLinearMap 3
      map_one' := LinearMap.ext fun v => by
        change Free.factorRep A B hA hB hcomm 1 v = v
        rw [map_one]
        rfl
      map_mul' := fun g h => LinearMap.ext fun v => by
        change Free.factorRep A B hA hB hcomm (g * h) v =
          Free.factorRep A B hA hB hcomm g (Free.factorRep A B hA hB hcomm h v)
        rw [map_mul]
        rfl }
  have hρ : ∀ g : Γ, ∀ a : A, ρ g (Additive.ofMul (a : A ⧸ B.subgroupOf A)) =
      Additive.ofMul (Free.actQuot A B hA hB g (a : A ⧸ B.subgroupOf A)) := fun _ _ => rfl
  set R := Subgroup.zpowers x with hRdef
  have hRN : R ≤ Subgroup.normalizer (N₀ : Set Γ) := Subgroup.zpowers_le.mpr hxN₀
  have hRfpf : ∀ r ∈ R, r ≠ 1 → ∀ n ∈ N₀, r * n * r⁻¹ = n → n = 1 := by
    intro r hr hr1 n hn hrn
    apply hxfpf n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_ne_one hx hr hr1)
    have hc : Commute r n := by
      calc r * n = r * n * r⁻¹ * r := by group
        _ = n * r := by rw [hrn]
    rw [(Commute.zpow_left hc k).eq, mul_inv_cancel_right]
  have hNchar : ((Nat.card N₀ : ℕ) : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hN₀3
  have hCN : ∀ v : Additive (A ⧸ B.subgroupOf A), (∀ n ∈ N₀, ρ n v = v) → v = 0 := by
    intro v hv
    have h1 := eq_one_of_fixed_factor A B hBA hA hB hB3 N₀ hN₀3 hfix (Additive.toMul v)
      (fun r hr => by
        induction v using Additive.rec with
        | ofMul q =>
          induction q using QuotientGroup.induction_on with
          | H a =>
            have := hv r hr
            rw [hρ] at this
            exact congrArg Additive.toMul this)
    change Additive.ofMul (Additive.toMul v) = Additive.ofMul 1
    rw [h1]
  have hbender := bender1970_1_5_finrank_eq ρ N₀ R hN₀ab hRN hRfpf hNchar hCN
  have hR3 : Nat.card R = 3 := by rw [hRdef, Nat.card_zpowers, hx]
  rw [hR3] at hbender
  have hcardV : Nat.card (Additive (A ⧸ B.subgroupOf A)) =
      3 ^ Module.finrank (ZMod 3) (Additive (A ⧸ B.subgroupOf A)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  have hcardI : Nat.card (Representation.invariants (ρ.comp R.subtype)) =
      3 ^ Module.finrank (ZMod 3) (Representation.invariants (ρ.comp R.subtype)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  have hfixI : Nat.card (Free.fixQuot A B hA hB R) =
      Nat.card (Representation.invariants (ρ.comp R.subtype)) := by
    refine Nat.card_congr
      { toFun := fun q => ⟨Additive.ofMul (q : A ⧸ B.subgroupOf A), fun r => ?_⟩
        invFun := fun v => ⟨Additive.toMul (v : Additive (A ⧸ B.subgroupOf A)), fun r hr => ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · obtain ⟨q, hq⟩ := q
      induction q using QuotientGroup.induction_on with
      | H a =>
        change ρ r (Additive.ofMul (a : A ⧸ B.subgroupOf A)) = _
        rw [hρ]
        exact congrArg Additive.ofMul (hq r r.2)
    · obtain ⟨v, hv⟩ := v
      have := (Representation.mem_invariants _ v).mp hv ⟨r, hr⟩
      induction v using Additive.rec with
      | ofMul q =>
        induction q using QuotientGroup.induction_on with
        | H a =>
          change ρ r (Additive.ofMul (a : A ⧸ B.subgroupOf A)) = _ at this
          rw [hρ] at this
          exact congrArg Additive.toMul this
  rw [hfixI, hcardI, ← pow_mul, mul_comm, ← hbender]
  exact hcardV.symm

theorem card_fix_pow_three_and_lift (hN : IsPGroup 3 N) {x : Γ} (hx : orderOf x = 3)
    (N₀ : Subgroup Γ) (hN₀ab : IsMulCommutative N₀) (hN₀3 : ¬ 3 ∣ Nat.card N₀)
    (hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set Γ)) (hxfpf : ∀ n ∈ N₀, x * n * x⁻¹ = n → n = 1)
    (hfix : ∀ a : N, (∀ r ∈ N₀, r • a = a) → a = 1) :
    {n : N | x • n = n}.ncard ^ 3 = Nat.card N ∧
      ∀ i, ∀ n ∈ lpc 3 N i, n⁻¹ * (x • n) ∈ lpc 3 N (i + 1) →
        ∃ a ∈ lpc 3 N i, x • a = a ∧ ∃ b ∈ lpc 3 N (i + 1), n = a * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers x with hXdef
  let : MulDistribMulAction X N := MulDistribMulAction.compHom N X.subtype
  have hXcard : Nat.card X = 3 := by rw [hXdef, Nat.card_zpowers, hx]
  have : Fact (Nat.card X).Prime := ⟨by rw [hXcard]; exact Nat.prime_three⟩
  have hinvΓ : ∀ g : Γ, ∀ i, ∀ n ∈ lpc 3 N i, g • n ∈ lpc 3 N i := by
    intro g i n hn
    rw [← map_lpc (MulDistribMulAction.toMulEquiv N g) 3 i]
    exact ⟨n, hn, rfl⟩
  obtain ⟨k, hk⟩ := exists_lpc_eq_bot hN
  have hfree : ∀ i < k, ∀ Y : Subgroup X,
      (relFix Y (lpc 3 N i) (lpc 3 N (i + 1))).ncard ^ Nat.card Y =
        Nat.card (lpc 3 N i) * Nat.card (lpc 3 N (i + 1)) ^ (Nat.card Y - 1) := by
    intro i _ Y
    rcases Y.eq_bot_or_eq_top_of_prime_card with rfl | rfl
    · have hset : relFix (⊥ : Subgroup X) (lpc 3 N i) (lpc 3 N (i + 1)) =
          (lpc 3 N i : Set N) := by
        ext n
        simp only [relFix, Set.mem_ofPred_eq, Subgroup.mem_bot, SetLike.mem_coe]
        constructor
        · exact fun h => h.1
        · intro hn
          refine ⟨hn, fun y hy => ?_⟩
          subst hy
          show n⁻¹ * ((1 : X) • n) ∈ _
          rw [one_smul X n, inv_mul_cancel]
          exact Subgroup.one_mem _
      rw [hset, ← Nat.card_coe_set_eq, Subgroup.card_bot, pow_one, Nat.sub_self, pow_zero,
        mul_one]
      rfl
    · set A := lpc 3 N i
      set B := lpc 3 N (i + 1)
      have hBA : B ≤ A := lpc_succ_le 3 i
      have hA : ∀ y : X, ∀ a ∈ A, y • a ∈ A := fun y a ha => hinvΓ y i a ha
      have hB : ∀ y : X, ∀ b ∈ B, y • b ∈ B := fun y b hb => hinvΓ y (i + 1) b hb
      have hAΓ : ∀ g : Γ, ∀ a ∈ A, g • a ∈ A := fun g => hinvΓ g i
      have hBΓ : ∀ g : Γ, ∀ b ∈ B, g • b ∈ B := fun g => hinvΓ g (i + 1)
      have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B := fun a _ b hb =>
        commutator_lpc_le 3 i (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hb)
      have helem : ∀ a ∈ A, a ^ 3 ∈ B := fun a ha => pow_mem_lpc_succ 3 i ha
      have hB3 : IsPGroup 3 B := hN.to_subgroup B
      have hfixA : ∀ a ∈ A, (∀ r ∈ N₀, r • a = a) → a = 1 := fun a _ h =>
        hfix a fun r hr => h r hr
      have hrel := Free.card_relFix A B hA hB hBA ⊤
      have hact : ∀ y : X, ∀ q : A ⧸ B.subgroupOf A,
          Free.actQuot A B hA hB y q = Free.actQuot A B hAΓ hBΓ (y : Γ) q := by
        intro y q
        induction q using QuotientGroup.induction_on with
        | H a => rfl
      have heq : Free.fixQuot A B hA hB (⊤ : Subgroup X) =
          Free.fixQuot A B hAΓ hBΓ (Subgroup.zpowers x) := by
        ext q
        change (∀ y ∈ (⊤ : Subgroup X), _ = _) ↔ (∀ g ∈ Subgroup.zpowers x, _ = _)
        constructor
        · intro h g hg
          have := h ⟨g, hg⟩ (Subgroup.mem_top _)
          rwa [hact] at this
        · intro h y _
          rw [hact]
          exact h y y.2
      have hbend := card_fixQuot_pow_three A B hBA hAΓ hBΓ hcomm helem hB3 hx N₀ hN₀ab hN₀3
        hxN₀ hxfpf hfixA
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
      have hB' : Nat.card (B.subgroupOf A) = Nat.card B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
      rw [hB'] at h3
      rw [hrel, Subgroup.card_top, hXcard, mul_pow, heq, hbend, h3]
      ring
  have h55 := lemma_5_5 (p := 3) (X := X) (N := N) hN k (lpc 3 N) rfl hk
    (fun i => lpc_succ_le 3 i) (fun i => commutator_lpc_le 3 i)
    (fun i y n hn => hinvΓ (y : Γ) i n hn) (fun i n hn => pow_mem_lpc_succ 3 i hn) hfree
  obtain ⟨hlift, h⟩ := h55
  refine ⟨?_, ?_⟩
  · rw [hXcard] at h
    rw [← h]
    congr 2
    ext n
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hn y
      have hst : X ≤ MulAction.stabilizer Γ n :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hn)
      exact MulAction.mem_stabilizer_iff.mp (hst y.2)
    · intro h
      exact h ⟨x, Subgroup.mem_zpowers x⟩
  · intro i n hn hxn
    by_cases hik : i < k
    ·
      set B := lpc 3 N (i + 1) with hBdef
      have hBΓ : ∀ g : Γ, ∀ b ∈ B, g • b ∈ B := fun g => hinvΓ g (i + 1)
      let St : Subgroup Γ :=
        { carrier := {g | n⁻¹ * (g • n) ∈ B}
          mul_mem' := fun {g h} hg hh => by
            change n⁻¹ * ((g * h) • n) ∈ B
            have : n⁻¹ * ((g * h) • n) = (n⁻¹ * (g • n)) * (g • (n⁻¹ * (h • n))) := by
              rw [smul_mul', smul_inv', mul_smul]
              group
            rw [this]
            exact B.mul_mem hg (hBΓ g _ hh)
          one_mem' := by
            change n⁻¹ * ((1 : Γ) • n) ∈ B
            rw [one_smul, inv_mul_cancel]
            exact B.one_mem
          inv_mem' := fun {g} hg => by
            change n⁻¹ * (g⁻¹ • n) ∈ B
            have : n⁻¹ * (g⁻¹ • n) = g⁻¹ • (n⁻¹ * (g • n))⁻¹ := by
              rw [smul_inv', smul_mul', smul_inv', inv_smul_smul]
              group
            rw [this]
            exact hBΓ g⁻¹ _ (B.inv_mem hg) }
      have hXSt : X ≤ St := Subgroup.zpowers_le.mpr hxn
      have hrel : n ∈ relFix (⊤ : Subgroup X) (lpc 3 N i) B :=
        ⟨hn, fun y _ => hXSt y.2⟩
      rw [hlift i hik] at hrel
      obtain ⟨a, ha, hafix, b, hb, rfl⟩ := hrel
      exact ⟨a, ha, hafix ⟨x, Subgroup.mem_zpowers x⟩, b, hb, rfl⟩
    · have hbot : lpc 3 N i = ⊥ := by
        rw [eq_bot_iff, ← hk]
        exact lpc_antitone (N := N) 3 (by omega)
      rw [hbot, Subgroup.mem_bot] at hn
      subst hn
      exact ⟨1, Subgroup.one_mem _, smul_one x, 1, Subgroup.one_mem _, by rw [mul_one]⟩

theorem card_fix_pow_three (hN : IsPGroup 3 N) {x : Γ} (hx : orderOf x = 3) (N₀ : Subgroup Γ)
    (hN₀ab : IsMulCommutative N₀) (hN₀3 : ¬ 3 ∣ Nat.card N₀)
    (hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set Γ)) (hxfpf : ∀ n ∈ N₀, x * n * x⁻¹ = n → n = 1)
    (hfix : ∀ a : N, (∀ r ∈ N₀, r • a = a) → a = 1) :
    {n : N | x • n = n}.ncard ^ 3 = Nat.card N :=
  (card_fix_pow_three_and_lift hN hx N₀ hN₀ab hN₀3 hxN₀ hxfpf hfix).1

end Sec56

end CFSG.Walter.W67
