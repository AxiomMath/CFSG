module

public import CFSG.RankThree.GF2n.Basic
import CFSG.GroupTheory.ThompsonAxB
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GH74.EvenRank

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.RankThree.GF2n

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_mem_commutator_mem {p : ℕ} [Fact p.Prime] {P B N : Subgroup G}
    (hP : IsPGroup p P) (hBN : B < N) (hNP : N ≤ P) (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) :
    ∃ d ∈ N, d ∉ B ∧ ∀ x ∈ P, ⁅d, x⁆ ∈ B := by
  have hBP : B ≤ P := hBN.le.trans hNP
  have hB'n : (B.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPB
  have hN'n : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hQ : IsPGroup p (P ⧸ B.subgroupOf P) := hP.to_quotient _
  have hQnil : Group.IsNilpotent (P ⧸ B.subgroupOf P) := hQ.isNilpotent
  set N' := (N.subgroupOf P).map (QuotientGroup.mk' (B.subgroupOf P)) with hN'
  have hN'nn : N'.Normal := hN'n.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hnN, hnB⟩ := IsConcreteLE.exists_of_lt hBN
  have hN'ne : N' ≠ ⊥ := by
    intro h
    have hmem : (QuotientGroup.mk' (B.subgroupOf P) ⟨n, hNP hnN⟩) ∈ N' :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnN)
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hnB hmem
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne)
  obtain ⟨hyN, hyZ⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨d, hdN, rfl⟩ := Subgroup.mem_map.mp hyN
  refine ⟨d, Subgroup.mem_subgroupOf.mp hdN, ?_, ?_⟩
  · intro hdB
    apply hy1
    apply Subtype.ext
    simp only [QuotientGroup.mk'_apply, OneMemClass.coe_one]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hdB)
  · intro x hx
    have hc := Subgroup.mem_center_iff.mp hyZ (QuotientGroup.mk' (B.subgroupOf P) ⟨x, hx⟩)
    have h1 : QuotientGroup.mk' (B.subgroupOf P) (⁅d, ⟨x, hx⟩⁆) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have e : ((⁅d, ⟨x, hx⟩⁆ : P) : G) = ⁅(d : G), x⁆ := by
      simp [commutatorElement_def]
    rw [e] at h1
    exact h1

theorem inSubgroup_frattini_le_of_sq {P K : Subgroup G} (hP : IsPGroup 2 P)
    (hsq : ∀ x ∈ P, x ^ 2 ∈ K) (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ K) :
    inSubgroup frattini P ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have h : frattini P ≤ K.comap P.subtype := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · have hx' : P.subtype x ∈ ⁅P, P⁆ := by
        have : P.subtype x ∈ (commutator P).map P.subtype := Subgroup.mem_map_of_mem _ hx
        rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at this
      exact (Subgroup.commutator_le.mpr hcomm) hx'
    · exact hsq y y.2
  rintro _ ⟨y, hy, rfl⟩
  exact h hy

theorem commute_of_thompson_A_times_B {Q B : Subgroup G} {c : G} (hQ : IsPGroup 2 Q)
    (hB : IsPGroup 2 B) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hc : Odd (orderOf c))
    (hcB : ∀ b ∈ B, c * b = b * c)
    (hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → c * q = q * c) :
    ∀ q ∈ Q, c * q = q * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.zpowers c with hAdef
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hcQ
  let α : A →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ)
  let β : B →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hBQ)
  have hα : ∀ (a : A) (q : Q), ((α a q : Q) : G) = (a : G) * q * (a : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (q : Q), ((β b q : Q) : G) = (b : G) * q * (b : G)⁻¹ := fun _ _ => rfl
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAdef, Nat.card_zpowers]
    exact Nat.odd_iff.mp hc |> fun h => by omega
  have hab : ∀ (a : A) (b : B), (a : G) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hcB b hb) k).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext q
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    calc (a : G) * ((b : G) * q * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * q * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * q * ((b : G) * a)⁻¹ := by rw [hab a b]
      _ = (b : G) * ((a : G) * q * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hrB : ∀ b ∈ B, (r : G) * b = b * r := by
      intro b hb
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc (r : G) * b = b * r * b⁻¹ * b := by rw [h]
        _ = b * r := by group
    have hcr := hfix r r.2 hrB
    apply Subtype.ext
    rw [hα]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have : Commute (c ^ k) (r : G) := Commute.zpow_left hcr k
    change c ^ k * r * (c ^ k)⁻¹ = r
    rw [this.eq]
    group
  have h := CFSG.GroupTheory.thompson_A_times_B hQ hA2 hB α β hcomm hfix'
  intro q hq
  have hq' := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : G))
    (h ⟨c, Subgroup.mem_zpowers c⟩)
  rw [hα] at hq'
  change c * q * c⁻¹ = ((1 : MulAut Q) ⟨q, hq⟩ : G) at hq'
  rw [MulAut.one_apply] at hq'
  calc c * q = c * q * c⁻¹ * c := by group
    _ = q * c := by rw [hq']

theorem inf_centralizer_le_of_generalizedFitting_eq {M : Subgroup G}
    (hF : generalizedFitting M = pCore 2 M) :
    M ⊓ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) ≤ inSubgroup (pCore 2) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : IsCharacteristicP 2 M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore M 2).mpr hF
  exact (CFSG.GH74.inf_centralizer_map_subtype_le_iff M (pCore 2 M)).mpr hchar

omit [Finite G] in
theorem le_inSubgroup_pCore {M B : Subgroup G} (hBM : B ≤ M)
    (hMB : M ≤ Subgroup.normalizer (B : Set G)) (hB2 : IsPGroup 2 B) :
    B ≤ inSubgroup (pCore 2) M := by
  have hn : (B.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBM).mpr hMB
  have hp : IsPGroup 2 (B.subgroupOf M) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm
  have hle : B.subgroupOf M ≤ pCore 2 M := le_sSup ⟨hn, hp⟩
  intro b hb
  exact ⟨⟨b, hBM hb⟩, hle (Subgroup.mem_subgroupOf.mpr hb), rfl⟩


omit [Finite G] in
theorem eq_one_of_odd_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hodd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩))

theorem exists_odd_orderOf_pow (x : G) :
    ∃ a : ℕ, Odd (orderOf (x ^ 2 ^ a)) ∧ (x ^ 2 ^ a = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x)
    (orderOf_pos x).ne'
  refine ⟨a, ?_, fun h => ⟨a, h⟩⟩
  rw [orderOf_pow' x (by positivity), hn, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
    (by positivity)]
  exact hm

theorem le_of_isMulCommutative_normal {M B : Subgroup G} (hF : generalizedFitting M = pCore 2 M)
    (hBM : B ≤ M) (hMB : M ≤ Subgroup.normalizer (B : Set G)) (hBc : IsMulCommutative B) :
    B ≤ inSubgroup (pCore 2) M := by
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hCQ := inf_centralizer_le_of_generalizedFitting_eq hF
  have hBc' : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hodd : ∀ b ∈ B, Odd (orderOf b) → b = 1 := by
    intro b hb hbo
    let K : Subgroup G :=
      { carrier := {x | x ∈ B ∧ Odd (orderOf x)}
        one_mem' := ⟨B.one_mem, by rw [orderOf_one]; exact odd_one⟩
        mul_mem' := by
          rintro x y ⟨hxB, hxo⟩ ⟨hyB, hyo⟩
          refine ⟨B.mul_mem hxB hyB, ?_⟩
          have hdvd := (Commute.orderOf_mul_dvd_lcm (hBc' x hxB y hyB)).trans
            (Nat.lcm_dvd_mul _ _)
          exact Odd.of_dvd_nat (Odd.mul hxo hyo) hdvd
        inv_mem' := by
          rintro x ⟨hxB, hxo⟩
          exact ⟨B.inv_mem hxB, by rw [orderOf_inv]; exact hxo⟩ }
    have hKQ : ∀ x ∈ K, ∀ q ∈ Q, x * q = q * x := by
      intro x hx q hq
      have hxM : x ∈ M := hBM hx.1
      have hqM : q ∈ M := hQM hq
      have h1 : x * q * x⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMQ hxM) q).mp hq) (Q.inv_mem hq)
      have h2 : x * q * x⁻¹ * q⁻¹ ∈ K := by
        have hqx : q * x⁻¹ * q⁻¹ ∈ K := by
          refine ⟨(Subgroup.mem_normalizer_iff.mp (hMB hqM) x⁻¹).mp (B.inv_mem hx.1), ?_⟩
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv]
          exact hx.2
        have := K.mul_mem hx hqx
        simpa [mul_assoc] using this
      have h3 : x * q * x⁻¹ * q⁻¹ = 1 :=
        eq_one_of_odd_of_isPGroup hQ2 h1 h2.2
      calc x * q = x * q * x⁻¹ * q⁻¹ * (q * x) := by group
        _ = q * x := by rw [h3, one_mul]
    have hbQ : b ∈ Q := hCQ ⟨hBM hb, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (hKQ b ⟨hb, hbo⟩ q hq).symm⟩
    exact eq_one_of_odd_of_isPGroup hQ2 hbQ hbo
  have hB2 : IsPGroup 2 B := by
    intro b
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (b : G)
    refine ⟨a, Subtype.ext ?_⟩
    simpa using hodd _ (B.pow_mem b.2 _) ha
  exact le_inSubgroup_pCore hBM hMB hB2

theorem tim78_2_9_alpha {M B P : Subgroup G} (hF : generalizedFitting M = pCore 2 M)
    (hBM : B ≤ M) (hMB : M ≤ Subgroup.normalizer (B : Set G)) (hBc : IsMulCommutative B)
    (hP : P = inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (B : Set G)) :
    M ⊓ Subgroup.centralizer (P : Set G) = P ⊓ Subgroup.centralizer (P : Set G) := by
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hCQ := inf_centralizer_le_of_generalizedFitting_eq hF
  have hBQ : B ≤ Q := le_of_isMulCommutative_normal hF hBM hMB hBc
  have hBc' : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBP : B ≤ P := by
    rw [hP]
    exact le_inf hBQ fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => hBc' a ha b hb
  have hPQ : P ≤ Q := hP ▸ inf_le_left
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => by
    rw [hP]
    exact mem_normalizer_inf (hMQ hm) (mem_normalizer_centralizer (hMB hm))
  set C := M ⊓ Subgroup.centralizer (P : Set G) with hCdef
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := fun m hm =>
    mem_normalizer_inf (Subgroup.le_normalizer hm) (mem_normalizer_centralizer (hMP hm))
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (c : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    set c' := (c : G) ^ 2 ^ a with hc'
    have hc'C : c' ∈ C := C.pow_mem c.2 _
    have hc'B : ∀ b ∈ B, c' * b = b * c' := fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hc'C.2 b (hBP hb)).symm
    have hc'Q := commute_of_thompson_A_times_B hQ2 (hQ2.to_le hBQ) (hMQ hc'C.1)
      (fun b hb => hMQ (hBM hb)) ha hc'B (fun q hq hqB => by
        have hqP : q ∈ P := by
          rw [hP]
          exact ⟨hq, Subgroup.mem_centralizer_iff.mpr fun b hb => (hqB b hb).symm⟩
        exact (Subgroup.mem_centralizer_iff.mp hc'C.2 q hqP).symm)
    have hc'Qmem : c' ∈ Q := hCQ ⟨hc'C.1, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (hc'Q q hq).symm⟩
    exact eq_one_of_odd_of_isPGroup hQ2 hc'Qmem ha
  have hCQ' : C ≤ Q := le_inSubgroup_pCore inf_le_left hMC hC2
  apply le_antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [hP]
    refine ⟨hCQ' hx, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hx.2 b (hBP hb)
  · exact inf_le_inf_right _ (hPQ.trans hQM)


theorem tim78_2_9_beta_of_elementary {M B P : Subgroup G}
    (hF : generalizedFitting M = pCore 2 M)
    (hmax : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      IsMulCommutative W) B)
    (hB2 : ∀ x ∈ B, x ^ 2 = 1)
    (hP : P = inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (B : Set G)) :
    inSubgroup frattini P ≤ B ∧ B = P ⊓ Subgroup.centralizer (P : Set G) := by
  obtain ⟨hBM, hMB, hBc⟩ := hmax.prop
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hBQ : B ≤ Q := le_of_isMulCommutative_normal hF hBM hMB hBc
  have hBc' : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBP : B ≤ P := by
    rw [hP]
    exact le_inf hBQ fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => hBc' a ha b hb
  have hPQ : P ≤ Q := hP ▸ inf_le_left
  have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
  have hPM : P ≤ M := hPQ.trans hQM
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => by
    rw [hP]
    exact mem_normalizer_inf (hMQ hm) (mem_normalizer_centralizer (hMB hm))
  have hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p := by
    intro p hp b hb
    rw [hP] at hp
    exact (Subgroup.mem_centralizer_iff.mp hp.2 b hb).symm
  have hPBn : P ≤ Subgroup.normalizer (B : Set G) := fun p hp => hMB (hPM hp)
  have hZ : B = P ⊓ Subgroup.centralizer (P : Set G) := by
    have hBZ : B ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf hBP fun b hb => Subgroup.mem_centralizer_iff.mpr fun p hp => hPB p hp b hb
    have hZc : IsMulCommutative (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      show (x : G) * y = y * x
      exact Subgroup.mem_centralizer_iff.mp y.2.2 x x.2.1
    have hZM : M ≤ Subgroup.normalizer
        ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := fun m hm =>
      mem_normalizer_inf (hMP hm) (mem_normalizer_centralizer (hMP hm))
    exact le_antisymm hBZ (hmax.le_of_ge ⟨inf_le_left.trans hPM, hZM, hZc⟩ hBZ)
  refine ⟨?_, hZ⟩
  by_contra hFB
  set F := inSubgroup frattini P with hFdef
  have hFP : F ≤ P := Subgroup.map_subtype_le _
  set N := F ⊔ B with hNdef
  have hBN : B < N := lt_of_le_of_ne le_sup_right fun h => hFB (h ▸ le_sup_left)
  have hNP : N ≤ P := sup_le hFP hBP
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := fun p hp =>
    mem_normalizer_sup (mem_normalizer_inSubgroup_frattini (Subgroup.le_normalizer hp)) (hPBn hp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d₀, hd₀N, hd₀B, hd₀c⟩ := exists_mem_not_mem_commutator_mem hP2 hBN hNP hPBn hPN
  have hcen : ∀ c ∈ B, ∀ p ∈ P, p * c = c * p := fun c hc p hp => hPB p hp c hc
  let E₀ : Subgroup G :=
    { carrier := {e | e ∈ P ∧ ∀ x ∈ P, ⁅e, x⁆ ∈ B}
      one_mem' := ⟨P.one_mem, fun x _ => by rw [commutatorElement_one_left]; exact B.one_mem⟩
      mul_mem' := by
        rintro e f ⟨heP, he⟩ ⟨hfP, hf⟩
        refine ⟨P.mul_mem heP hfP, fun x hx => ?_⟩
        have e1 : ⁅e * f, x⁆ = e * ⁅f, x⁆ * e⁻¹ * ⁅e, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e1, hcen _ (hf x hx) e heP, mul_inv_cancel_right]
        exact B.mul_mem (hf x hx) (he x hx)
      inv_mem' := by
        rintro e ⟨heP, he⟩
        refine ⟨P.inv_mem heP, fun x hx => ?_⟩
        have e1 : ⁅e⁻¹, x⁆ = e⁻¹ * ⁅e, x⁆⁻¹ * e := by
          simp only [commutatorElement_def]; group
        rw [e1, hcen _ (B.inv_mem (he x hx)) e⁻¹ (P.inv_mem heP), inv_mul_cancel_right]
        exact B.inv_mem (he x hx) }
  have hd₀E₀ : d₀ ∈ E₀ := ⟨hNP hd₀N, hd₀c⟩
  let E : Subgroup G :=
    { carrier := {e | e ∈ P ∧ (∀ x ∈ P, ⁅e, x⁆ ∈ B) ∧ e ^ 2 ∈ B}
      one_mem' := ⟨P.one_mem, fun x _ => by rw [commutatorElement_one_left]; exact B.one_mem,
        by rw [one_pow]; exact B.one_mem⟩
      mul_mem' := by
        rintro e f ⟨heP, he, he2⟩ ⟨hfP, hf, hf2⟩
        refine ⟨P.mul_mem heP hfP, (E₀.mul_mem ⟨heP, he⟩ ⟨hfP, hf⟩).2, ?_⟩
        set c := ⁅f, e⁆ with hc
        have hcB : c ∈ B := hf e heP
        have hfe : f * e = c * e * f := by rw [hc, commutatorElement_def]; group
        have : (e * f) ^ 2 = c * (e ^ 2 * f ^ 2) := by
          calc (e * f) ^ 2 = e * (f * e) * f := by rw [sq]; group
            _ = e * (c * e * f) * f := by rw [hfe]
            _ = (e * c) * e * f * f := by group
            _ = (c * e) * e * f * f := by rw [hcen c hcB e heP]
            _ = c * (e ^ 2 * f ^ 2) := by rw [sq, sq]; group
        rw [this]
        exact B.mul_mem hcB (B.mul_mem he2 hf2)
      inv_mem' := by
        rintro e ⟨heP, he, he2⟩
        exact ⟨P.inv_mem heP, (E₀.inv_mem ⟨heP, he⟩).2, by rw [inv_pow]; exact B.inv_mem he2⟩ }
  set D := E ⊓ N with hDdef
  have hex : ∃ j : ℕ, d₀ ^ 2 ^ (j + 1) ∈ B := by
    obtain ⟨k, hk⟩ := hP2 ⟨d₀, hNP hd₀N⟩
    refine ⟨k, ?_⟩
    have hk' : d₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [pow_succ, pow_mul, hk', one_pow]
    exact B.one_mem
  classical
  set j := Nat.find hex with hjdef
  set d := d₀ ^ 2 ^ j with hddef
  have hdB : d ∉ B := by
    rcases hj : j with _ | j'
    · rw [hddef, hj, pow_zero, pow_one]
      exact hd₀B
    · have hmin := Nat.find_min hex (show j' < j by omega)
      rw [hddef, hj]
      exact hmin
  have hd2 : d ^ 2 ∈ B := by
    rw [hddef, ← pow_mul, ← pow_succ]
    exact Nat.find_spec hex
  have hdD : d ∈ D := ⟨⟨hNP (N.pow_mem hd₀N _), (E₀.pow_mem hd₀E₀ _).2, hd2⟩, N.pow_mem hd₀N _⟩
  have hDc : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ * d₂ = d₂ * d₁ := by
    intro d₁ hd₁ d₂ hd₂
    obtain ⟨⟨hd₁P, hd₁c, -⟩, -⟩ := hd₁
    have hK : F ≤ P ⊓ Subgroup.centralizer ({d₁} : Set G) := by
      refine inSubgroup_frattini_le_of_sq hP2 (fun x hx => ?_) (fun x hx y hy => ?_)
      · refine ⟨P.pow_mem hx 2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        set c := ⁅d₁, x⁆ with hc
        have hcB : c ∈ B := hd₁c x hx
        have hdx : d₁ * x * d₁⁻¹ = c * x := by rw [hc, commutatorElement_def]; group
        have : d₁ * x ^ 2 * d₁⁻¹ = x ^ 2 := by
          calc d₁ * x ^ 2 * d₁⁻¹ = (d₁ * x * d₁⁻¹) * (d₁ * x * d₁⁻¹) := by rw [sq]; group
            _ = c * x * (c * x) := by rw [hdx]
            _ = c * (x * c) * x := by group
            _ = c * (c * x) * x := by rw [hcen c hcB x hx]
            _ = c ^ 2 * x ^ 2 := by rw [sq, sq]; group
            _ = x ^ 2 := by rw [hB2 c hcB, one_mul]
        calc x ^ 2 * d₁ = d₁ * x ^ 2 * d₁⁻¹ * d₁ := by rw [this]
          _ = d₁ * x ^ 2 := by group
      · refine ⟨P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy),
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hdx : d₁ * x * d₁⁻¹ = ⁅d₁, x⁆ * x := by rw [commutatorElement_def]; group
        have hdy : d₁ * y * d₁⁻¹ = ⁅d₁, y⁆ * y := by rw [commutatorElement_def]; group
        have hcx := hd₁c x hx
        have hcy := hd₁c y hy
        have : d₁ * ⁅x, y⁆ * d₁⁻¹ = ⁅x, y⁆ := by
          have e1 : d₁ * ⁅x, y⁆ * d₁⁻¹ =
              ⁅d₁ * x * d₁⁻¹, d₁ * y * d₁⁻¹⁆ := by simp only [commutatorElement_def]; group
          rw [e1, hdx, hdy]
          simp only [commutatorElement_def]
          have h1 := hcen _ hcx x hx
          have h2 := hcen _ hcy y hy
          have h3 := hcen _ hcx y hy
          have h4 := hcen _ hcy x hx
          have h5 : ⁅d₁, x⁆ * ⁅d₁, y⁆ = ⁅d₁, y⁆ * ⁅d₁, x⁆ := hBc' _ hcx _ hcy
          calc ⁅d₁, x⁆ * x * (⁅d₁, y⁆ * y) * (⁅d₁, x⁆ * x)⁻¹ * (⁅d₁, y⁆ * y)⁻¹
              = ⁅d₁, x⁆ * (x * ⁅d₁, y⁆) * y * x⁻¹ * ⁅d₁, x⁆⁻¹ * y⁻¹ * ⁅d₁, y⁆⁻¹ := by group
            _ = ⁅d₁, x⁆ * (⁅d₁, y⁆ * x) * y * x⁻¹ * ⁅d₁, x⁆⁻¹ * y⁻¹ * ⁅d₁, y⁆⁻¹ := by rw [h4]
            _ = ⁅d₁, x⁆ * ⁅d₁, y⁆ * (x * y * x⁻¹ * ⁅d₁, x⁆⁻¹) * y⁻¹ * ⁅d₁, y⁆⁻¹ := by group
            _ = ⁅d₁, x⁆ * ⁅d₁, y⁆ * (⁅d₁, x⁆⁻¹ * (x * y * x⁻¹)) * y⁻¹ * ⁅d₁, y⁆⁻¹ := by
                rw [hcen _ (B.inv_mem hcx) _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx))]
            _ = ⁅d₁, y⁆ * (x * y * x⁻¹ * y⁻¹) * ⁅d₁, y⁆⁻¹ := by rw [h5]; group
            _ = (x * y * x⁻¹ * y⁻¹) * ⁅d₁, y⁆ * ⁅d₁, y⁆⁻¹ := by
                rw [hcen _ hcy _ (P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx))
                  (P.inv_mem hy))]
            _ = x * y * x⁻¹ * y⁻¹ := by group
        calc ⁅x, y⁆ * d₁ = d₁ * ⁅x, y⁆ * d₁⁻¹ * d₁ := by rw [this]
          _ = d₁ * ⁅x, y⁆ := by group
    have hBF : B ≤ Subgroup.normalizer (F : Set G) := fun b hb =>
      mem_normalizer_inSubgroup_frattini (Subgroup.le_normalizer (hBP hb))
    obtain ⟨f, hf, b, hb, rfl⟩ := exists_mul_of_mem_sup hBF hd₂.2
    have hfd : f * d₁ = d₁ * f := Subgroup.mem_centralizer_singleton_iff.mp (hK hf).2
    calc d₁ * (f * b) = (d₁ * f) * b := by group
      _ = f * d₁ * b := by rw [hfd]
      _ = f * (b * d₁) := by rw [mul_assoc, ← hcen b hb d₁ hd₁P]
      _ = f * b * d₁ := by group
  have hDM : D ≤ M := fun x hx => hPM hx.1.1
  have hMD : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    have hEm : m ∈ Subgroup.normalizer (E : Set G) := by
      have key : ∀ c : G, c ∈ M → ∀ e ∈ E, c * e * c⁻¹ ∈ E := by
        intro c hc e he
        obtain ⟨heP, hec, he2⟩ := he
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hMP hc) e).mp heP, fun x hx => ?_, ?_⟩
        · have hx' : c⁻¹ * x * c ∈ P := by
            have := (Subgroup.mem_normalizer_iff.mp (hMP (M.inv_mem hc)) x).mp hx
            simpa using this
          have e1 : ⁅c * e * c⁻¹, x⁆ = c * ⁅e, c⁻¹ * x * c⁆ * c⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e1]
          exact (Subgroup.mem_normalizer_iff.mp (hMB hc) _).mp (hec _ hx')
        · rw [conj_pow]
          exact (Subgroup.mem_normalizer_iff.mp (hMB hc) _).mp he2
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key m hm x, fun hx => ?_⟩
      have := key m⁻¹ (M.inv_mem hm) _ hx
      simpa [mul_assoc] using this
    exact mem_normalizer_inf hEm (mem_normalizer_sup
      (mem_normalizer_inSubgroup_frattini (hMP hm)) (hMB hm))
  have hDab : IsMulCommutative D := ⟨⟨fun x y => Subtype.ext (hDc x x.2 y y.2)⟩⟩
  have hBD : B ≤ D := fun b hb => ⟨⟨hBP hb, fun x hx => by
      have : b * x * b⁻¹ * x⁻¹ = 1 := by rw [← hcen b hb x hx]; group
      rw [commutatorElement_def, this]
      exact B.one_mem,
    by rw [hB2 b hb]; exact B.one_mem⟩, (le_sup_right : B ≤ N) hb⟩
  exact hdB (hmax.le_of_ge ⟨hDM, hMD, hDab⟩ hBD hdD)

end CFSG.RankThree.GF2n.Tim78
