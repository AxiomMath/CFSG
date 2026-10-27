module

public import CFSG.Walter.W67.Section5.Prop56N
public import CFSG.Walter.W67.Section6.Core64B

public section

namespace CFSG.Walter.W67

namespace Sec64

open Sec56

variable {Γ N : Type} [Group Γ] [Group N] [MulDistribMulAction Γ N] [Finite Γ] [Finite N]

omit [MulDistribMulAction Γ N] [Finite N] in
theorem mem_zpowers_of_ne_one' {x r : Γ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hx : orderOf x = ℓ)
    (hr : r ∈ Subgroup.zpowers x) (hr1 : r ≠ 1) : x ∈ Subgroup.zpowers r := by
  have hle : Subgroup.zpowers r ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hr
  have hdvd : Nat.card (Subgroup.zpowers r) ∣ ℓ := by
    rw [← hx, ← Nat.card_zpowers x]
    exact Subgroup.card_dvd_of_le hle
  have hcard : Nat.card (Subgroup.zpowers r) = ℓ := by
    rcases (Nat.dvd_prime hℓ).mp hdvd with h | h
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
      exact hr1 h
    · exact h
  have heq : Subgroup.zpowers r = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hx])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem card_fixQuot_pow_seven (A B : Subgroup N) [(B.subgroupOf A).Normal] (hBA : B ≤ A)
    (hA : ∀ g : Γ, ∀ a ∈ A, g • a ∈ A) (hB : ∀ g : Γ, ∀ b ∈ B, g • b ∈ B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) (helem : ∀ a ∈ A, a ^ 3 ∈ B)
    (hB3 : IsPGroup 3 B) {x : Γ} (hx : orderOf x = 7) (N₀ : Subgroup Γ)
    (hN₀ab : IsMulCommutative N₀) (hN₀3 : ¬ 3 ∣ Nat.card N₀)
    (hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set Γ)) (hxfpf : ∀ n ∈ N₀, x * n * x⁻¹ = n → n = 1)
    (hfix : ∀ a ∈ A, (∀ r ∈ N₀, r • a = a) → a = 1) :
    Nat.card (Free.fixQuot A B hA hB (Subgroup.zpowers x)) ^ 7 =
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
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_ne_one' (by norm_num) hx hr hr1)
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
  have hbender := CFSG.Walter.bender1970_1_5_finrank_eq ρ N₀ R hN₀ab hRN hRfpf hNchar hCN
  have hR7 : Nat.card R = 7 := by rw [hRdef, Nat.card_zpowers, hx]
  rw [hR7] at hbender
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

theorem card_fix_pow_seven (hN : IsPGroup 3 N) {x : Γ} (hx : orderOf x = 7)
    (N₀ : Subgroup Γ) (hN₀ab : IsMulCommutative N₀) (hN₀3 : ¬ 3 ∣ Nat.card N₀)
    (hxN₀ : x ∈ Subgroup.normalizer (N₀ : Set Γ)) (hxfpf : ∀ n ∈ N₀, x * n * x⁻¹ = n → n = 1)
    (hfix : ∀ a : N, (∀ r ∈ N₀, r • a = a) → a = 1) :
    {n : N | x • n = n}.ncard ^ 7 = Nat.card N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers x with hXdef
  let : MulDistribMulAction X N := MulDistribMulAction.compHom N X.subtype
  have hXcard : Nat.card X = 7 := by rw [hXdef, Nat.card_zpowers, hx]
  have : Fact (Nat.card X).Prime := ⟨by rw [hXcard]; norm_num⟩
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
      have hbend := card_fixQuot_pow_seven A B hBA hAΓ hBΓ hcomm helem hB3 hx N₀ hN₀ab hN₀3
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
  obtain ⟨-, h⟩ := h55
  rw [hXcard] at h
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

end Sec64

namespace Sec6

variable {G : Type} [Group G] [Finite G] {s : Std G}

namespace Sol

variable (σ : Sol s)
include σ

theorem card_B (f5 : Frame5 s) : Nat.card f5.B = 1093 := by
  have h := f5.card_B
  rw [σ.q_eq] at h
  omega

theorem card_inf_centralizer_pow_seven
    (f5 : Frame5 s) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {g : G} (hgE : g ∈ s.fr.E)
    (hg7 : orderOf g = 7) :
    Nat.card (Q ⊓ Subgroup.centralizer ({g} : Set G) : Subgroup G) ^ 7 = Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfpf := f5.fpf_of_isPGroup lemma_2_2 lemma_2_6_i σ.p3 hQ hBQ hEQ
  set Γ := Subgroup.normalizer (Q : Set G) with hΓdef
  let := JT.conjAct Γ Q le_rfl
  have hgΓ : g ∈ Γ := hEQ hgE
  set g' : Γ := ⟨g, hgΓ⟩ with hg'def
  have hg'o : orderOf g' = 7 := by rw [hg'def, Subgroup.orderOf_mk, hg7]
  have hgB : g ∈ Subgroup.normalizer (f5.B : Set G) := f5.E_le_normalizer_B hgE
  set N₀ := f5.B.subgroupOf Γ with hN₀def
  have hmemN₀ : ∀ n : Γ, n ∈ N₀ ↔ (n : G) ∈ f5.B := fun n => Subgroup.mem_subgroupOf
  have hN₀ab : IsMulCommutative N₀ := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (f5.B_comm _ ((hmemN₀ a).mp a.2) _ ((hmemN₀ b).mp b.2)))⟩⟩
  have hN₀card : Nat.card N₀ = Nat.card f5.B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
    rw [hN₀card, σ.card_B f5]
    norm_num
  have hgN₀ : g' ∈ Subgroup.normalizer (N₀ : Set Γ) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro n hn
    rw [hmemN₀] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp hgB n).mp hn
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg7
    norm_num at hg7
  obtain ⟨b₀, hb₀, hb₀g⟩ := f5.exists_not_comm_B lemma_2_6_i hgE hg1
  have hCB : f5.B ⊓ Subgroup.centralizer ({g} : Set G) = ⊥ := by
    have hdvd : Nat.card ↥(f5.B ⊓ Subgroup.centralizer ({g} : Set G)) ∣ 1093 :=
      σ.card_B f5 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 1093)).mp hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : f5.B ⊓ Subgroup.centralizer ({g} : Set G) = f5.B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, σ.card_B f5])
      have hb₀C : b₀ ∈ f5.B ⊓ Subgroup.centralizer ({g} : Set G) := by rw [heq]; exact hb₀
      exact hb₀g (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hb₀C).2).symm
  have hgfpf : ∀ n ∈ N₀, g' * n * g'⁻¹ = n → n = 1 := by
    intro n hn hgn
    have hgn' : g * (n : G) * g⁻¹ = n := congrArg Subtype.val hgn
    have hnC : (n : G) ∈ f5.B ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(hmemN₀ n).mp hn, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (n : G) * g = g * n * g⁻¹ * g := by rw [hgn']
        _ = g * n := by group
    rw [hCB, Subgroup.mem_bot] at hnC
    exact Subtype.ext hnC
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    exact hb₀g (by group)
  have hfix : ∀ a : Q, (∀ r ∈ N₀, r • a = a) → a = 1 := by
    intro a ha
    have h1 := ha ⟨b₀, hBQ hb₀⟩ ((hmemN₀ _).mpr hb₀)
    have h2 : b₀ * (a : G) * b₀⁻¹ = a := congrArg Subtype.val h1
    apply Subtype.ext
    apply hfpf b₀ hb₀ hb₀1 a a.2
    calc b₀ * (a : G) = b₀ * (a : G) * b₀⁻¹ * b₀ := by group
      _ = a * b₀ := by rw [h2]
  have key := Sec64.card_fix_pow_seven hQ hg'o N₀ hN₀ab hN₀3 hgN₀ hgfpf hfix
  rw [← key]
  congr 1
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, Subtype.ext (by
        have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
        change g * (y : G) * g⁻¹ = y
        rw [← this, mul_inv_cancel_right])⟩
      invFun := fun y => ⟨y.1, Subgroup.mem_inf.mpr ⟨y.1.2, by
        have h1 : g * (y.1 : G) * g⁻¹ = y.1 := congrArg Subtype.val y.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (y.1 : G) * g = g * (y.1 : G) * g⁻¹ * g := by rw [h1]
          _ = g * y.1 := by group⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Sol

end Sec6

end CFSG.Walter.W67
