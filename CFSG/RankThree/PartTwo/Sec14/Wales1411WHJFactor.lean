module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJFactor

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv

variable {M : Type} [Group M] [Finite M]

theorem le_centralizer_of_inf_eq_bot {V S : Subgroup M} {e : M} (hS2 : IsPGroup 2 S)
    (he3 : e ^ 3 = 1) (heS : e ∈ Subgroup.normalizer (S : Set M))
    (hSV : S ≤ Subgroup.normalizer (V : Set M)) (heV : V ≤ Subgroup.centralizer ({e} : Set M))
    (hSe : S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥) :
    S ≤ Subgroup.centralizer (V : Set M) := by
  classical
  intro s hs
  set K : Subgroup M := S ⊓ Subgroup.centralizer (V : Set M) with hK
  have hev : ∀ v ∈ V, e * v = v * e := fun v hv =>
    (Subgroup.mem_centralizer_singleton_iff.mp (heV hv)).symm
  have heS' : ∀ y ∈ S, e * y * e⁻¹ ∈ S := fun y hy => (Subgroup.mem_normalizer_iff.mp heS y).mp hy
  have heCV : e ∈ Subgroup.centralizer (V : Set M) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hev v hv).symm
  have heC : ∀ k ∈ Subgroup.centralizer (V : Set M), e * k * e⁻¹ ∈
      Subgroup.centralizer (V : Set M) := fun k hk => mul_mem (mul_mem heCV hk) (inv_mem heCV)
  have hk0 : s⁻¹ * e * s * e⁻¹ ∈ Subgroup.centralizer (V : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : e * (s * v * s⁻¹) = (s * v * s⁻¹) * e := by
      apply hev
      have := (Subgroup.mem_normalizer_iff.mp (hSV hs) v).mp hv
      exact this
    have h2 : e⁻¹ * v = v * e⁻¹ := by
      have := hev v hv
      calc e⁻¹ * v = e⁻¹ * (v * e) * e⁻¹ := by group
        _ = e⁻¹ * (e * v) * e⁻¹ := by rw [this]
        _ = v * e⁻¹ := by group
    calc v * (s⁻¹ * e * s * e⁻¹) = s⁻¹ * (s * v * s⁻¹) * e * s * e⁻¹ := by group
      _ = s⁻¹ * (e * (s * v * s⁻¹)) * s * e⁻¹ := by rw [h1]; group
      _ = s⁻¹ * e * s * (v * e⁻¹) := by group
      _ = s⁻¹ * e * s * (e⁻¹ * v) := by rw [h2]
      _ = (s⁻¹ * e * s * e⁻¹) * v := by group
  have hmap : ∀ k ∈ K, s⁻¹ * (e * (s * k) * e⁻¹) ∈ K := by
    intro k hk
    have h : s⁻¹ * (e * (s * k) * e⁻¹) = (s⁻¹ * e * s * e⁻¹) * (e * k * e⁻¹) := by group
    rw [h]
    obtain ⟨hkS, hkC⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨mul_mem ?_ (heS' k hkS), mul_mem hk0 (heC k hkC)⟩
    have h' : s⁻¹ * e * s * e⁻¹ = s⁻¹ * (e * s * e⁻¹) := by group
    rw [h']
    exact mul_mem (inv_mem hs) (heS' s hs)
  let f : Function.End ↥K := fun k => ⟨s⁻¹ * (e * (s * k) * e⁻¹), hmap k k.2⟩
  have hf : ∀ (n : ℕ) (k : ↥K), ((f ^ n) k : M) = s⁻¹ * (e ^ n * (s * k) * (e ^ n)⁻¹) := by
    intro n
    induction n with
    | zero =>
      intro k
      show (k : M) = s⁻¹ * (e ^ 0 * (s * k) * (e ^ 0)⁻¹)
      group
    | succ n ih =>
      intro k
      rw [pow_succ']
      show s⁻¹ * (e * (s * ((f ^ n) k : M)) * e⁻¹) = _
      rw [ih k, pow_succ']
      group
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext k
    apply Subtype.ext
    rw [pow_one, hf 3 k, he3]
    show s⁻¹ * (1 * (s * (k : M)) * 1⁻¹) = (k : M)
    group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hcard := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  have hK2 : IsPGroup 2 K := hS2.to_le inf_le_left
  obtain ⟨m, hm⟩ := hK2.exists_card_eq
  have hK3 : ¬ 3 ∣ Fintype.card ↥K := by
    rw [← Nat.card_eq_fintype_card, hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    norm_num at this
  have hfix : 0 < Fintype.card (Function.fixedPoints f) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (Function.fixedPoints f)) with h | h
    · rw [h] at hcard
      exact absurd (Nat.modEq_zero_iff_dvd.mp hcard) hK3
    · exact h
  obtain ⟨⟨k, hkf⟩⟩ := Fintype.card_pos_iff.mp hfix
  have hk : s⁻¹ * (e * (s * k) * e⁻¹) = k := congrArg Subtype.val hkf
  have hsk : s * (k : M) ∈ S ⊓ Subgroup.centralizer ({e} : Set M) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hs (Subgroup.mem_inf.mp k.2).1,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have : e * (s * k) * e⁻¹ = s * k := by
      calc e * (s * k) * e⁻¹ = s * (s⁻¹ * (e * (s * k) * e⁻¹)) := by group
        _ = s * k := by rw [hk]
    calc s * k * e = e * (s * k) * e⁻¹ * e := by rw [this]
      _ = e * (s * k) := by group
  rw [hSe, Subgroup.mem_bot] at hsk
  have hs' : s = (k : M)⁻¹ := eq_inv_of_mul_eq_one_left hsk
  rw [hs']
  exact inv_mem (Subgroup.mem_inf.mp k.2).2

theorem mem_centralizer_of_mul {V K T : Subgroup M} (hKV : K ≤ Subgroup.centralizer (V : Set M))
    (hTK : T ≤ Subgroup.normalizer (K : Set M)) (hT2 : IsPGroup 2 T) {k t : M} (hk : k ∈ K)
    (ht : t ∈ T) (h3 : (k * t) ^ 3 ∈ K) : k * t ∈ Subgroup.centralizer (V : Set M) := by
  have hconj : ∀ y ∈ K, t * y * t⁻¹ ∈ K := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hTK ht) y).mp hy
  have hk1 := hconj k hk
  have hk2 := hconj _ hk1
  have h3' : k * t * (k * t) * (k * t) ∈ K := by
    have := h3
    rw [pow_succ, pow_succ, pow_one] at this
    exact this
  have ht3 : t ^ 3 ∈ K := by
    have h : t ^ 3 = (k * (t * k * t⁻¹) * (t * (t * k * t⁻¹) * t⁻¹))⁻¹ *
        (k * t * (k * t) * (k * t)) := by group
    rw [h]
    exact mul_mem (inv_mem (mul_mem (mul_mem hk hk1) hk2)) h3'
  obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
  have htm : t ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.gcd 3 (2 ^ m) = 1 :=
    Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)
  have hbez : (1 : ℤ) = 3 * Nat.gcdA 3 (2 ^ m) + 2 ^ m * Nat.gcdB 3 (2 ^ m) := by
    have := Nat.gcd_eq_gcd_ab 3 (2 ^ m)
    rw [hcop] at this
    push_cast at this
    exact this
  have htK : t ∈ K := by
    have h : t = (t ^ 3) ^ (Nat.gcdA 3 (2 ^ m)) * (t ^ (2 ^ m)) ^ (Nat.gcdB 3 (2 ^ m)) := by
      rw [← zpow_natCast t 3, ← zpow_natCast t (2 ^ m), ← zpow_mul, ← zpow_mul, ← zpow_add]
      push_cast
      rw [← hbez, zpow_one]
    rw [h, htm, one_zpow, mul_one]
    exact zpow_mem ht3 _
  exact mul_mem (hKV hk) (hKV htK)

theorem false_of_factor {Ybar Abar V S T : Subgroup M} (hVY : V ≤ Ybar)
    (hYV : Ybar ≤ Subgroup.normalizer (V : Set M)) {x : M} (hxV : x ∈ V)
    (hx3 : x ^ 3 ∈ Subgroup.centralizer (V : Set M))
    (hxc : ¬ V ≤ Subgroup.centralizer ({x} : Set M)) {e : M} (heA : e ∈ Abar) (he3 : e ^ 3 = 1)
    (heV : V ≤ Subgroup.centralizer ({e} : Set M)) (hS : InvTwo Abar Ybar S)
    (hT : InvTwo Abar Ybar T) (hST : S ⊔ T = Ybar)
    (hsupp : S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥ ∨
      T ⊓ Subgroup.centralizer ({e} : Set M) = ⊥) : False := by
  have key : ∀ S T : Subgroup M, InvTwo Abar Ybar S → InvTwo Abar Ybar T → S ⊔ T = Ybar →
      S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥ → False := by
    intro S T hS hT hST hSe
    obtain ⟨hSY, hAS, hS2⟩ := hS
    obtain ⟨hTY, -, hT2⟩ := hT
    have hSC := le_centralizer_of_inf_eq_bot hS2 he3 (hAS heA) (hSY.trans hYV) heV hSe
    set K : Subgroup M := Ybar ⊓ Subgroup.centralizer (V : Set M) with hK
    have hTK : T ≤ Subgroup.normalizer (K : Set M) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have htY : t ∈ Ybar := hTY ht
      have htV := hYV htY
      constructor
      · intro hy
        obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
        refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem htY hyY) (inv_mem htY), ?_⟩
        rw [Subgroup.mem_centralizer_iff] at hyC ⊢
        intro v hv
        have hv' : t⁻¹ * v * t ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem htV) v).mp hv
          simpa using this
        have := hyC _ hv'
        calc v * (t * y * t⁻¹) = t * ((t⁻¹ * v * t) * y) * t⁻¹ := by group
          _ = t * (y * (t⁻¹ * v * t)) * t⁻¹ := by rw [this]
          _ = t * y * t⁻¹ * v := by group
      · intro hy'
        obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy'
        have hy : y = t⁻¹ * (t * y * t⁻¹) * t := by group
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [hy]
          exact mul_mem (mul_mem (inv_mem htY) hyY) htY
        · rw [Subgroup.mem_centralizer_iff] at hyC ⊢
          intro v hv
          have hv' : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp htV v).mp hv
          have := hyC _ hv'
          calc v * y = t⁻¹ * ((t * v * t⁻¹) * (t * y * t⁻¹)) * t := by group
            _ = t⁻¹ * ((t * y * t⁻¹) * (t * v * t⁻¹)) * t := by rw [this]
            _ = y * v := by group
    have hx : x ∈ K ⊔ T := by
      have hle : S ⊔ T ≤ K ⊔ T := sup_le_sup_right (le_inf hSY hSC) T
      exact hle (hST ▸ hVY hxV)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hx
    obtain ⟨k, hk, t, ht, hkt⟩ := hx
    change k * t = x at hkt
    have hxC := mem_centralizer_of_mul (inf_le_right : K ≤ _) hTK hT2 hk ht
      (by rw [hkt]; exact Subgroup.mem_inf.mpr ⟨pow_mem (hVY hxV) 3, hx3⟩)
    rw [hkt] at hxC
    exact hxc fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hxC v hv)
  rcases hsupp with h | h
  · exact key S T hS hT hST h
  · exact key T S hT hS (by rw [sup_comm]; exact hST) h

theorem a5_three_noncomm : ∃ σ τ : alternatingGroup (Fin 5), orderOf σ = 3 ∧ orderOf τ = 3 ∧
    σ * τ ≠ τ * σ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (swap (0 : Fin 5) 1 * swap 0 2) ∈ alternatingGroup (Fin 5) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  have h2 : (swap (0 : Fin 5) 1 * swap 0 3) ∈ alternatingGroup (Fin 5) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, ?_, ?_, fun h => ?_⟩
  · refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
    · show (swap (0 : Fin 5) 1 * swap 0 2) ^ 3 = 1
      decide
    · have h' : (swap (0 : Fin 5) 1 * swap 0 2) = 1 := congrArg Subtype.val h
      exact absurd h' (by decide)
  · refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
    · show (swap (0 : Fin 5) 1 * swap 0 3) ^ 3 = 1
      decide
    · have h' : (swap (0 : Fin 5) 1 * swap 0 3) = 1 := congrArg Subtype.val h
      exact absurd h' (by decide)
  · have h' : (swap (0 : Fin 5) 1 * swap 0 2) * (swap 0 1 * swap 0 3) =
        (swap 0 1 * swap 0 3) * (swap 0 1 * swap 0 2) := congrArg Subtype.val h
    exact absurd h' (by decide)

theorem a5_factor {Ybar Abar Xbar Rbar : Subgroup M} {abar : M}
    (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) {V : Subgroup M} (hVY : V ≤ Ybar)
    (hV : Nonempty (↥V ≃* alternatingGroup (Fin 5)))
    (hAV : Abar ≤ Subgroup.normalizer (V : Set M)) :
    (∃ e ∈ Abar, V ≤ Subgroup.centralizer ({e} : Set M) ∧ e ∉ Subgroup.zpowers abar) ∧
      ∃ c ∈ Abar, c ∈ V ∧ orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ⟩ := hV
  have hcenV : Function.Injective (MulAut.conj : ↥V →* MulAut ↥V) :=
    HJProd.conj_injective_of_mulEquiv ψ HJProd.a5_facts.1
  have hinnV : ∀ α : MulAut ↥V, α ^ 3 = 1 → α ∈ (MulAut.conj : ↥V →* MulAut ↥V).range :=
    HJProd.mem_range_conj_of_mulEquiv ψ HJProd.a5_facts.2
  set κ : ↥Abar →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hAV) with hκ
  have hκapp : ∀ (ε : ↥Abar) (v : ↥V), ((κ ε v : ↥V) : M) = (ε : M) * v * (ε : M)⁻¹ :=
    fun ε v => rfl
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hrange : κ.range ≤ (MulAut.conj : ↥V →* MulAut ↥V).range := by
    rintro _ ⟨ε, rfl⟩
    apply hinnV
    rw [← map_pow]
    have h : ε ^ 3 = 1 := Subtype.ext (by simpa using hA3 ε ε.2)
    rw [h, map_one]
  set W : Subgroup ↥V := κ.range.comap (MulAut.conj : ↥V →* MulAut ↥V) with hW
  have hWmap : W.map (MulAut.conj : ↥V →* MulAut ↥V) = κ.range := by
    rw [hW, Subgroup.map_comap_eq, inf_eq_right.mpr hrange]
  have hWcard : Nat.card W = Nat.card κ.range := by
    rw [← hWmap, Subgroup.card_map_of_injective hcenV]
  have hV60 : Nat.card ↥V = 60 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have hW3 : Nat.card W ∣ 3 := by
    have h1 : Nat.card W ∣ 60 := hV60 ▸ Subgroup.card_subgroup_dvd_card W
    have h2 : Nat.card W ∣ 27 := by
      rw [hWcard, ← hset.card_A]
      exact Subgroup.card_range_dvd κ
    have h := Nat.dvd_gcd h1 h2
    norm_num at h
    exact h
  have hker := Subgroup.card_ker_mul_card_range κ
  rw [← hWcard, hset.card_A] at hker
  have hkerC : ∀ ε ∈ κ.ker, V ≤ Subgroup.centralizer ({(ε : M)} : Set M) := by
    intro ε hε v hv
    have h := congrArg (fun α : MulAut ↥V => ((α ⟨v, hv⟩ : ↥V) : M)) (MonoidHom.mem_ker.mp hε)
    simp only [MulAut.one_apply] at h
    rw [hκapp] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc v * ε = (ε : M) * v * (ε : M)⁻¹ * ε := by rw [h]
      _ = ε * v := by group
  refine ⟨?_, ?_⟩
  ·
    set Kr : Subgroup M := κ.ker.map Abar.subtype with hKr
    have hKr9 : 9 ≤ Nat.card Kr := by
      rw [hKr, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      rcases (Nat.dvd_prime Nat.prime_three).mp hW3 with h | h <;> rw [h] at hker <;> omega
    have hnle : ¬ Kr ≤ Subgroup.zpowers abar := fun hle => by
      have h := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, orderOf_eq_prime (hA3 abar hset.mem_A) hset.ne_one] at h
      omega
    obtain ⟨e, ⟨ε, hε, rfl⟩, he⟩ := SetLike.not_le_iff_exists.mp hnle
    exact ⟨ε, ε.2, hkerC ε hε, he⟩
  ·
    have hWne : W ≠ ⊥ := by
      intro hWb
      rw [hWb, Subgroup.card_bot] at hker
      have hkt : κ.ker = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hset.card_A]
        omega
      obtain ⟨σ, τ, hσ, hτ, hστ⟩ := a5_three_noncomm
      have hmem : ∀ x : alternatingGroup (Fin 5), orderOf x = 3 →
          ((ψ.symm x : ↥V) : M) ∈ Abar := by
        intro x hx
        refine hset.mem_A_of_three _ (hVY (ψ.symm x).2) ?_ ?_
        · rw [Subgroup.mem_centralizer_iff]
          intro g hg
          have := hkerC ⟨g, hg⟩ (hkt ▸ Subgroup.mem_top _) (ψ.symm x).2
          exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
        · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
      have hc := congrArg Subtype.val
        (hset.isElemAbelian.1.is_comm.comm ⟨_, hmem σ hσ⟩ ⟨_, hmem τ hτ⟩)
      apply hστ
      apply ψ.symm.injective
      apply Subtype.ext
      simpa using hc
    have hW3' : Nat.card W = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hW3 with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hWne
      · exact h
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have hwo : orderOf w = 3 := by
      refine orderOf_eq_prime ?_ hw1
      rw [← hW3']
      exact pow_card_eq_one'
    have hWz : W = Subgroup.zpowers (w : ↥V) := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr w.2) ?_).symm
      rw [hW3', Nat.card_zpowers, Subgroup.orderOf_coe, hwo]
    refine ⟨((w : ↥V) : M), ?_, (w : ↥V).2, ?_⟩
    · refine hset.mem_A_of_three _ (hVY (w : ↥V).2) ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        obtain ⟨w', hw', hw'κ⟩ : κ ⟨g, hg⟩ ∈ W.map (MulAut.conj : ↥V →* MulAut ↥V) :=
          hWmap ▸ ⟨⟨g, hg⟩, rfl⟩
        rw [hWz] at hw'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
        have h := congrArg (fun α : MulAut ↥V => ((α (w : ↥V) : ↥V) : M)) hw'κ
        simp only [MonoidHom.coe_coe, MulAut.conj_apply] at h
        rw [hκapp] at h
        have hc : ((w : ↥V) ^ n * (w : ↥V) * ((w : ↥V) ^ n)⁻¹ : ↥V) = w := by group
        rw [hc] at h
        calc g * ((w : ↥V) : M) = g * ((w : ↥V) : M) * g⁻¹ * g := by group
          _ = (w : M) * g := by rw [← h]
      · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hwo]
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hwo]

end CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJFactor
