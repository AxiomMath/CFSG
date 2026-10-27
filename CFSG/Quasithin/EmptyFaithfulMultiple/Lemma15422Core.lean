module

public import Certificates.Certificate4952

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6
open scoped commutatorElement

namespace L15422

variable {H : Type*} [Group H] [Finite H]

theorem le_of_central_of_odd_relIndex {R S : Subgroup H} [hR : R.Normal] (hSR : S ≤ R)
    (hS2 : IsPGroup 2 S) (hScen : ∀ s ∈ S, ∀ r ∈ R, s * r = r * s)
    (hodd : ¬ 2 ∣ S.relIndex R)
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥) : R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := S.subgroupOf R
  have hS'n : S'.Normal := ⟨fun s hs r => by
    have hc : (r : H) * s * (r : H)⁻¹ = s := by
      rw [(hScen s hs r r.2).symm]
      group
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc]
    exact hs⟩
  have hS'2 : IsPGroup 2 S' := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSR).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS'2
  have hcop : Nat.Coprime (Nat.card S') S'.index := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by
      have : ¬ 2 ∣ S'.index := hodd
      omega)))
  obtain ⟨B', hB'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hB'odd : Odd (Nat.card B') := by
    have h1 := hB'.card_mul_card
    have h2 := S'.card_mul_index
    have : Nat.card B' = S'.index := by
      have hpos : 0 < Nat.card S' := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [this]
    exact Nat.odd_iff.mpr (by have : ¬ 2 ∣ S'.index := hodd; omega)
  have hmem : ∀ r : R, Odd (orderOf r) → r ∈ B' := by
    intro r hr
    obtain ⟨⟨⟨s, hs⟩, ⟨b, hb⟩⟩, hsb⟩ := hB'.2 r
    simp only at hsb
    have hsr : s * b = b * s := by
      have := hScen s hs b b.2
      exact Subtype.ext this
    set m := orderOf r
    have hm : (s * b) ^ m = 1 := by rw [hsb]; exact pow_orderOf_eq_one r
    rw [Commute.mul_pow hsr] at hm
    have hsm : s ^ m ∈ S' ⊓ B' := by
      refine ⟨S'.pow_mem hs m, ?_⟩
      have : s ^ m = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm
      rw [this]
      exact B'.inv_mem (B'.pow_mem hb m)
    rw [hB'.disjoint.eq_bot, Subgroup.mem_bot] at hsm
    obtain ⟨j, hj⟩ := hS'2 ⟨s, hs⟩
    have hj' : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 : orderOf s ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have h2 : orderOf s ∣ m := orderOf_dvd_of_pow_eq_one hsm
    have hcop' : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hr)
    have hs1 : s = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' h1 h2)
    rw [← hsb, hs1, one_mul]
    exact hb
  set B := B'.map R.subtype
  have hBodd : Odd (Nat.card B) := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hB'odd
  have hBmem : ∀ x : H, x ∈ B ↔ x ∈ R ∧ Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.2, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      have h := orderOf_dvd_natCard (⟨b, hb⟩ : B')
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hB'odd h
    · rintro ⟨hxR, hxo⟩
      refine ⟨⟨x, hxR⟩, hmem ⟨x, hxR⟩ ?_, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact hxo
  have hBn : B.Normal := ⟨fun x hx g => by
    rw [hBmem] at hx ⊢
    refine ⟨hR.conj_mem x hx.1 g, ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx.2⟩
  have hB : B = ⊥ := hO B hBn hBodd
  have hB'b : B' = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have : (b : H) ∈ B := ⟨b, hb, rfl⟩
    rw [hB, Subgroup.mem_bot] at this
    exact Subtype.ext this
  intro r hr
  obtain ⟨⟨⟨s, hs⟩, ⟨b, hb⟩⟩, hsb⟩ := hB'.2 ⟨r, hr⟩
  simp only at hsb
  have hb1 : b = 1 := by
    have hb' : b ∈ B' := hb
    rw [hB'b] at hb'
    exact Subgroup.mem_bot.mp hb'
  rw [hb1, mul_one] at hsb
  have := congrArg Subtype.val hsb
  simp only at this
  rw [← this]
  exact Subgroup.mem_subgroupOf.mp hs

theorem centralizer_inf_le {N : Subgroup H} [hN : N.Normal]
    (hQN : IsSylowIn 2 (Open.pCore 2 H) N)
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥) :
    Subgroup.centralizer (Open.pCore 2 H : Set H) ⊓ N ≤ Open.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := Open.pCore 2 H
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hCn : (Subgroup.centralizer (Q : Set H)).Normal := inferInstance
  set R := Subgroup.centralizer (Q : Set H) ⊓ N
  have hRn : R.Normal := Subgroup.normal_inf_normal _ _
  have hRN : (R.subgroupOf N).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hRn.conj_mem _ hx g⟩
  have hsyl : IsSylowIn 2 (Q ⊓ R) R := hQN.inf_normal inf_le_right hRN
  have hle := le_of_central_of_odd_relIndex (R := R) (S := Q ⊓ R) inf_le_right hsyl.isPGroup
    (fun s hs r hr => ((Subgroup.mem_centralizer_iff.mp hr.1) s hs.1))
    hsyl.not_dvd_relIndex hO
  exact hle.trans inf_le_left

omit [Finite H] in
theorem map_centralizer_ne_bot {N : Subgroup H} [N.Normal]
    (hle : Subgroup.centralizer (Open.pCore 2 H : Set H) ⊓ N ≤ Open.pCore 2 H)
    (hnc : ¬ Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ Open.pCore 2 H) :
    (Subgroup.centralizer (Open.pCore 2 H : Set H)).map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro h
  apply hnc
  have hCN : Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ N := by
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff]
    exact h
  exact (le_inf le_rfl hCN).trans hle

private theorem cycThree_sign : Equiv.Perm.sign cycThree = 1 :=
  Certificates.certificate4952.1

private theorem cycFive_sign : Equiv.Perm.sign cycFive = 1 :=
  Certificates.certificate4952.2.1

private theorem eq_one_of_commute_cyc : ∀ σ : Equiv.Perm (Fin 6), σ * cycThree = cycThree * σ →
    σ * cycFive = cycFive * σ → σ = 1 :=
  Certificates.certificate4952.2.2

theorem perm_six_eq_one_of_forall_commute {σ : Equiv.Perm (Fin 6)}
    (h : ∀ τ ∈ alternatingGroup (Fin 6), σ * τ = τ * σ) : σ = 1 :=
  eq_one_of_commute_cyc σ (h _ (Equiv.Perm.mem_alternatingGroup.mpr cycThree_sign))
    (h _ (Equiv.Perm.mem_alternatingGroup.mpr cycFive_sign))

theorem alternatingGroup_le_of_normal {M : Subgroup (Equiv.Perm (Fin 6))} [hM : M.Normal]
    (hne : M ≠ ⊥) : alternatingGroup (Fin 6) ≤ M := by
  set A := alternatingGroup (Fin 6)
  have hA : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have hMA : M ⊓ A ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro m hm
    have hcomm : ∀ a ∈ A, m * a = a * m := by
      intro a ha
      have h1 : m * a * m⁻¹ * a⁻¹ ∈ M ⊓ A := by
        refine ⟨?_, ?_⟩
        · have : a * m⁻¹ * a⁻¹ ∈ M := hM.conj_mem _ (M.inv_mem hm) a
          have e : m * a * m⁻¹ * a⁻¹ = m * (a * m⁻¹ * a⁻¹) := by group
          rw [e]
          exact M.mul_mem hm this
        · have : m * a * m⁻¹ ∈ A :=
            (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a ha m
          exact A.mul_mem this (A.inv_mem ha)
      rw [hbot, Subgroup.mem_bot] at h1
      calc m * a = m * a * m⁻¹ * a⁻¹ * (a * m) := by group
        _ = a * m := by rw [h1, one_mul]
    exact eq_one_of_commute_cyc m (hcomm _ (Equiv.Perm.mem_alternatingGroup.mpr cycThree_sign))
      (hcomm _ (Equiv.Perm.mem_alternatingGroup.mpr cycFive_sign))
  have hn : ((M ⊓ A).subgroupOf A).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hM.conj_mem _ hx.1 g, A.mul_mem (A.mul_mem g.2 hx.2) (A.inv_mem g.2)⟩⟩
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    apply hMA
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : A) ∈ (M ⊓ A).subgroupOf A := hx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · intro a ha
    have : (⟨a, ha⟩ : A) ∈ (M ⊓ A).subgroupOf A := by rw [h]; exact Subgroup.mem_top _
    exact this.1

theorem commute_of_normal_of_card_prime {G : Type*} [Group G] {Y A : Subgroup G} [hY : Y.Normal]
    {q : ℕ} [Fact q.Prime] (hYq : Nat.card Y = q) (hA : ⁅A, A⁆ = A) {a : G} (ha : a ∈ A)
    {y : G} (hy : y ∈ Y) : a * y = y * a := by
  have : IsCyclic Y := isCyclic_of_prime_card hYq
  let ψ : G →* MulAut Y := MulAut.conjNormal
  have hcomm : ∀ x z : MulAut Y, x * z = z * x := fun x z => by
    apply (IsCyclic.mulAutMulEquiv Y).injective
    rw [map_mul, map_mul, mul_comm]
  have hle : ⁅A, A⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro x _ z _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [hcomm (ψ x) (ψ z)]
    group
  have ha' : ψ a = 1 := (hA ▸ hle) ha
  have h1 : (ψ a) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [ha']; rfl
  have h2 : a * y * a⁻¹ = y := congrArg Subtype.val h1
  calc a * y = a * y * a⁻¹ * a := by group
    _ = y * a := by rw [h2]

theorem false_of_isHatSym {N : Subgroup H} [hN : N.Normal]
    (hQN : IsSylowIn 2 (Open.pCore 2 H) N)
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥)
    (hnc : ¬ Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ Open.pCore 2 H)
    (hhat : IsHatSym 6 (H ⧸ N)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ, hY3, hÂ⟩ := hhat
  set Q := Open.pCore 2 H
  set C := Subgroup.centralizer (Q : Set H)
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hCn : C.Normal := inferInstance
  set π := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hle := centralizer_inf_le hQN hO
  have hne := map_centralizer_ne_bot hle hnc
  set Cs := C.map π
  have hCsn : Cs.Normal := hCn.map π hπ
  set Y := φ.ker
  set Â := (alternatingGroup (Fin 6)).comap φ
  have hÂp : ⁅Â, Â⁆ = Â := by
    have h1 := hÂ.1.1
    have h2 : (commutator Â).map Â.subtype = (⊤ : Subgroup Â).map Â.subtype := by rw [h1]
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    exact h2
  have hYÂ : Y ≤ Â := fun y hy => by
    change φ y ∈ alternatingGroup (Fin 6)
    rw [MonoidHom.mem_ker.mp hy]
    exact Subgroup.one_mem _
  have hcomm : ∀ a ∈ Â, ∀ y ∈ Y, a * y = y * a := fun a ha y hy =>
    commute_of_normal_of_card_prime hY3 hÂp ha hy
  have hYC : Y ≤ Cs := by
    by_cases hφC : Cs.map φ = ⊥
    · have hCsY : Cs ≤ Y := by rw [← Subgroup.map_eq_bot_iff]; exact hφC
      have hcard : Nat.card Y ≤ Nat.card Cs := by
        rw [hY3]
        have hdvd : Nat.card Cs ∣ 3 := hY3 ▸ Subgroup.card_dvd_of_le hCsY
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (Subgroup.card_eq_one.mp h) hne
        · omega
      exact (Subgroup.eq_of_le_of_card_ge hCsY hcard).ge
    · have hφn : (Cs.map φ).Normal := hCsn.map φ hφ
      have hA6 := alternatingGroup_le_of_normal hφC
      have hdec : ∀ x ∈ Â, ∃ c ∈ Cs ⊓ Â, ∃ y ∈ Y, x = c * y := by
        intro x hx
        obtain ⟨c, hc, hcx⟩ := hA6 hx
        refine ⟨c, ⟨hc, ?_⟩, c⁻¹ * x, ?_, by group⟩
        · change φ c ∈ alternatingGroup (Fin 6)
          rw [hcx]
          exact hx
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
      have hÂC : Â ≤ Cs := by
        rw [← hÂp, Subgroup.commutator_le]
        intro x hx z hz
        obtain ⟨c, hc, y, hy, rfl⟩ := hdec x hx
        obtain ⟨d, hd, w, hw, rfl⟩ := hdec z hz
        have h1 : ⁅c * y, d * w⁆ = ⁅c, d⁆ := by
          have hcy : y * d = d * y := (hcomm d hd.2 y hy).symm
          have hcw : w * c = c * w := (hcomm c hc.2 w hw).symm
          have hyw : y * w = w * y := (hcomm y (hYÂ hy) w hw)
          have hdw : w * d = d * w := (hcomm d hd.2 w hw).symm
          have hcy' : y * c = c * y := (hcomm c hc.2 y hy).symm
          rw [commutatorElement_def, commutatorElement_def]
          calc c * y * (d * w) * (c * y)⁻¹ * (d * w)⁻¹
              = c * (y * d) * w * y⁻¹ * c⁻¹ * w⁻¹ * d⁻¹ := by group
            _ = c * d * (y * w) * y⁻¹ * c⁻¹ * w⁻¹ * d⁻¹ := by rw [hcy]; group
            _ = c * d * w * c⁻¹ * w⁻¹ * d⁻¹ := by rw [hyw]; group
            _ = c * d * (w * c⁻¹) * w⁻¹ * d⁻¹ := by group
            _ = c * d * c⁻¹ * d⁻¹ := by
              have : w * c⁻¹ = c⁻¹ * w := by
                calc w * c⁻¹ = c⁻¹ * (c * w) * c⁻¹ := by group
                  _ = c⁻¹ * (w * c) * c⁻¹ := by rw [hcw]
                  _ = c⁻¹ * w := by group
              rw [this]
              group
        rw [h1]
        exact Cs.mul_mem (Cs.mul_mem (Cs.mul_mem hc.1 hd.1) (Cs.inv_mem hc.1)) (Cs.inv_mem hd.1)
      exact hYÂ.trans hÂC
  set C₂ := C ⊓ Y.comap π
  have hC₂n : C₂.Normal := Subgroup.normal_inf_normal _ _
  have hNY : N ≤ Y.comap π := fun n hn => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker,
      show π n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, map_one]
  have hQN' : Q ≤ N := hQN.le
  have hSC₂ : C ⊓ Q ≤ C₂ := le_inf inf_le_left (inf_le_right.trans (hQN'.trans hNY))
  have hS : C₂ ⊓ N = C ⊓ Q := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left)
        (le_trans (inf_le_inf_right N inf_le_left) hle)
    · exact le_inf hSC₂ (inf_le_right.trans hQN')
  have hmap : C₂.map π = Y := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hc.2
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := hYC hy
      exact ⟨c, ⟨hc, hy⟩, rfl⟩
  have hidx : (C ⊓ Q).relIndex C₂ = 3 := by
    rw [← hS, Subgroup.inf_relIndex_left, ← F6.card_map_mk C₂ N]
    change Nat.card (C₂.map π) = 3
    rw [hmap, hY3]
  have hC₂S := le_of_central_of_odd_relIndex (R := C₂) (S := C ⊓ Q) hSC₂
    ((CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le inf_le_right)
    (fun s hs r hr => ((Subgroup.mem_centralizer_iff.mp hr.1) s hs.2))
    (by rw [hidx]; decide) hO
  have hbot : C₂.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hC₂S.trans (inf_le_right.trans hQN')
  rw [hmap] at hbot
  rw [hbot, Subgroup.card_bot] at hY3
  omega

theorem exists_layer {N : Subgroup H} [hN : N.Normal] (hQN : IsSylowIn 2 (Open.pCore 2 H) N)
    (hO : ∀ B : Subgroup H, B.Normal → Odd (Nat.card B) → B = ⊥)
    (hnc : ¬ Subgroup.centralizer (Open.pCore 2 H : Set H) ≤ Open.pCore 2 H)
    (hQD : Open.pCore 2 (H ⧸ N) = ⊥) {N₀ : Subgroup (H ⧸ N)} (hN₀i : N₀.index = 2)
    (hN₀s : IsSimpleGroup N₀) (hN₀nab : ∃ a b : N₀, a * b ≠ b * a) :
    ∃ K : Subgroup H, K.Normal ∧ K.map (QuotientGroup.mk' N) = N₀ ∧
      K ⊓ N ≤ Open.pCore 2 H ∧ K ≤ Subgroup.centralizer (Open.pCore 2 H : Set H) ∧
      ⁅K, K⁆ = K ∧ N ≤ Subgroup.centralizer (K : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := Open.pCore 2 H
  set C := Subgroup.centralizer (Q : Set H)
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hCn : C.Normal := inferInstance
  set π := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hle := centralizer_inf_le hQN hO
  have hne := map_centralizer_ne_bot hle hnc
  set Cs := C.map π
  have hCsn : Cs.Normal := hCn.map π hπ
  have hN₀n : N₀.Normal := Subgroup.normal_of_index_eq_two hN₀i
  have hN₀C : N₀ ≤ Cs := by
    have hn : ((Cs ⊓ N₀).subgroupOf N₀).Normal :=
      ⟨fun x hx g => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact ⟨hCsn.conj_mem _ hx.1 g, N₀.mul_mem (N₀.mul_mem g.2 hx.2) (N₀.inv_mem g.2)⟩⟩
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      have hbot : Cs ⊓ N₀ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx.2⟩ : N₀) ∈ (Cs ⊓ N₀).subgroupOf N₀ := hx
        rw [h, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      have hcard : Nat.card Cs ∣ 2 := by
        have h1 : N₀.relIndex Cs ∣ N₀.index := Subgroup.relIndex_dvd_index_of_normal N₀ Cs
        rw [← Subgroup.inf_relIndex_right, inf_comm, hbot, Subgroup.relIndex_bot_left,
          hN₀i] at h1
        exact h1
      have hcard' : Nat.card Cs ∣ 2 ^ 1 := by rw [pow_one]; exact hcard
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcard'
      have hCs2 : IsPGroup 2 Cs := IsPGroup.of_card hm
      have : Cs ≤ Open.pCore 2 (H ⧸ N) := CFSG.LieType.BorelTits.le_pCore 2 hCsn hCs2
      rw [hQD, le_bot_iff] at this
      exact hne this
    · intro x hx
      have : (⟨x, hx⟩ : N₀) ∈ (Cs ⊓ N₀).subgroupOf N₀ := by rw [h]; exact Subgroup.mem_top _
      exact this.1
  set C₁ := C ⊓ N₀.comap π
  have hC₁n : C₁.Normal := Subgroup.normal_inf_normal _ _
  have hC₁map : C₁.map π = N₀ := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hc.2
    · intro n hn
      obtain ⟨c, hc, rfl⟩ := hN₀C hn
      exact ⟨c, ⟨hc, hn⟩, rfl⟩
  have hN₀p : ⁅N₀, N₀⁆ = N₀ := by
    have hcn : (commutator N₀).Normal := inferInstance
    rcases hcn.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hN₀nab
      apply hab
      have : ⁅a, b⁆ = 1 := by
        have hm : ⁅a, b⁆ ∈ commutator N₀ := Subgroup.commutator_mem_commutator
          (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at hm
        exact hm
      rw [commutatorElement_def] at this
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [this, one_mul]
    · have h2 : (commutator N₀).map N₀.subtype = (⊤ : Subgroup N₀).map N₀.subtype := by rw [h]
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h2
      exact h2
  set K := ⁅C₁, C₁⁆
  have hKn : K.Normal := inferInstance
  have hKC₁ : K ≤ C₁ := Subgroup.commutator_le_left C₁ C₁
  have hKmap : K.map π = N₀ := by
    rw [Subgroup.map_commutator, hC₁map, hN₀p]
  have hKN : K ⊓ N ≤ Q :=
    le_trans (inf_le_inf_right N (hKC₁.trans inf_le_left)) hle
  have hKC : K ≤ C := hKC₁.trans inf_le_left
  have hKp : ⁅K, K⁆ = K := by
    apply le_antisymm (Subgroup.commutator_le_left K K)
    have hdec : ∀ c ∈ C₁, ∃ k ∈ K, ∃ z ∈ C ⊓ Q, c = k * z := by
      intro c hc
      have : π c ∈ K.map π := hKmap ▸ hc.2
      obtain ⟨k, hk, hkc⟩ := this
      have hz : k⁻¹ * c ∈ C ⊓ N := by
        refine ⟨C.mul_mem (C.inv_mem (hKC hk)) hc.1, (QuotientGroup.eq_one_iff _).mp ?_⟩
        change π (k⁻¹ * c) = 1
        rw [map_mul, map_inv, hkc, inv_mul_cancel]
      exact ⟨k, hk, k⁻¹ * c, ⟨hz.1, hle hz⟩, by group⟩
    rw [Subgroup.commutator_le]
    intro c hc d hd
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec c hc
    obtain ⟨k', hk', z', hz', rfl⟩ := hdec d hd
    have hkz : z * k = k * z := (Subgroup.mem_centralizer_iff.mp (hKC hk)) z hz.2
    have hk'z : z * k' = k' * z := (Subgroup.mem_centralizer_iff.mp (hKC hk')) z hz.2
    have hkz' : z' * k = k * z' := (Subgroup.mem_centralizer_iff.mp (hKC hk)) z' hz'.2
    have hzz' : z' * z = z * z' := (Subgroup.mem_centralizer_iff.mp hz.1) z' hz'.2
    have h1 : ⁅k * z, k' * z'⁆ = ⁅k, k'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc k * z * (k' * z') * (k * z)⁻¹ * (k' * z')⁻¹
          = k * (z * k') * z' * z⁻¹ * k⁻¹ * z'⁻¹ * k'⁻¹ := by group
        _ = k * k' * (z * z') * z⁻¹ * k⁻¹ * z'⁻¹ * k'⁻¹ := by rw [hk'z]; group
        _ = k * k' * z' * k⁻¹ * z'⁻¹ * k'⁻¹ := by rw [← hzz']; group
        _ = k * k' * (z' * k⁻¹) * z'⁻¹ * k'⁻¹ := by group
        _ = k * k' * k⁻¹ * k'⁻¹ := by
          rw [show z' * k⁻¹ = k⁻¹ * z' from by
            calc z' * k⁻¹ = k⁻¹ * (k * z') * k⁻¹ := by group
              _ = k⁻¹ * (z' * k) * k⁻¹ := by rw [hkz']
              _ = k⁻¹ * z' := by group]
          group
    rw [h1]
    exact Subgroup.commutator_mem_commutator hk hk'
  have hKNc : ⁅K, N⁆ ≤ K ⊓ N := Subgroup.commutator_le_inf K N
  have h3 : ⁅⁅K, N⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hKC hk)) x (hKN (hKNc hx))).symm
  have h4 : ⁅⁅N, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm N K]; exact h3
  have h5 : ⁅⁅K, K⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h3 h4
  rw [hKp] at h5
  refine ⟨K, hKn, hKmap, hKN, hKC, hKp, ?_⟩
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact h5

end L15422

end CFSG.Quasithin.EmptyFaithfulMultiple
