module

public import CFSG.Quasithin.H13.U3S1347W

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6 CFSG.LieType.BorelTits

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem map_inf_quotient {N : Subgroup D} [N.Normal] (hN : N ≤ G₁ ⊓ G₂) :
    (G₁ ⊓ G₂).map (QuotientGroup.mk' N) =
      G₁.map (QuotientGroup.mk' N) ⊓ G₂.map (QuotientGroup.mk' N) := by
  refine le_antisymm (map_inf_le _ _ _) ?_
  rintro _ ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, he⟩⟩
  have hk : g₂⁻¹ * g₁ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have he' : (QuotientGroup.mk g₂ : D ⧸ N) = QuotientGroup.mk g₁ := he
    rw [he', inv_mul_cancel]
  have hg₁₂ : g₁ ∈ G₂ := by
    have := mul_mem hg₂ (hN hk).2
    rwa [mul_inv_cancel_left] at this
  exact ⟨g₁, mem_inf.2 ⟨hg₁, hg₁₂⟩, rfl⟩

theorem goldschmidtTriple_map_quotient (h : IsGoldschmidtTriple G₁ G₂) (N : Subgroup D) [N.Normal]
    (hN2 : IsPGroup 2 ↥N) (hN : N ≤ G₁ ⊓ G₂) :
    IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' N)) (G₂.map (QuotientGroup.mk' N)) where
  gen := by
    rw [← Subgroup.map_sup, h.gen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  quotient₁ := by
    have hker : IsPGroup 2 ↥(toMapMk G₁ N).ker := by
      rw [ker_toMapMk]
      exact hN2.of_equiv (subgroupOfEquivOfLe (hN.trans inf_le_left)).symm
    exact gold_isoS3_of_surjective_kernel _ (toMapMk_surjective G₁ N) hker h.quotient₁.some
  quotient₂ := by
    have hker : IsPGroup 2 ↥(toMapMk G₂ N).ker := by
      rw [ker_toMapMk]
      exact hN2.of_equiv (subgroupOfEquivOfLe (hN.trans inf_le_right)).symm
    exact gold_isoS3_of_surjective_kernel _ (toMapMk_surjective G₂ N) hker h.quotient₂.some
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hT⟩ := h.sylow
    refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective N), ?_⟩
    rw [Sylow.coe_mapSurjective, hT, map_inf_quotient hN]

omit [Finite D] in
theorem mem_normalizer_inf_u3 {A B : Subgroup D} {g : D} (hA : g ∈ normalizer (A : Set D))
    (hB : g ∈ normalizer (B : Set D)) : g ∈ normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [mem_inf] at hA hB ⊢
  rw [hA x, hB x]

theorem pCoreOf_map_quotient {G N : Subgroup D} [N.Normal] (hN2 : IsPGroup 2 ↥N) :
    pCoreOf 2 (G.map (QuotientGroup.mk' N)) = (pCoreOf 2 G).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := QuotientGroup.mk' N with hf
  apply le_antisymm
  ·
    set P := G ⊓ (pCoreOf 2 (G.map f)).comap f with hP
    have hPn : G ≤ normalizer (P : Set D) := by
      intro g hg
      refine mem_normalizer_inf_u3 (le_normalizer hg) ?_
      rw [mem_normalizer_iff]
      intro x
      simp only [mem_comap, map_mul, map_inv]
      exact mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (G.map f) ⟨g, hg, rfl⟩) (f x)
    have hP2 : IsPGroup 2 ↥P := by
      rintro ⟨x, hxG, hxP⟩
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (G.map f)) ⟨f x, hxP⟩
      have hk' : f (x ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      obtain ⟨m, hm⟩ := hN2 ⟨_, (QuotientGroup.eq_one_iff _).1 hk'⟩
      refine ⟨k + m, Subtype.ext ?_⟩
      have hm' : (x ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [pow_add, pow_mul, hm']
    have hPO : P ≤ pCoreOf 2 G := le_pCoreOf_of_le_normalizer 2 inf_le_left hPn hP2
    intro y hy
    obtain ⟨g, hg, rfl⟩ := (pCoreOf_le 2 (G.map f)) hy
    exact ⟨g, hPO (mem_inf.2 ⟨hg, hy⟩), rfl⟩
  ·
    refine le_pCoreOf_of_le_normalizer 2 (map_mono (pCoreOf_le 2 G)) ?_
      ((pCoreOf_isPGroup 2 G).map f)
    exact (map_mono (le_normalizer_pCoreOf 2 G)).trans (le_normalizer_map f)

theorem pCore_quotient_pCore_eq_bot' :
    Open.pCore 2 (D ⧸ Open.pCore 2 D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Open.pCore 2 D with hN
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set K := (Open.pCore 2 (D ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := (CFSG.LieType.BorelTits.pCore_normal (G := D ⧸ N) 2).comap _
  have hK2 : IsPGroup 2 ↥K := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := D ⧸ N) 2) ⟨_, hx⟩
    have hk' : QuotientGroup.mk' N (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := D) 2)
      ⟨_, (QuotientGroup.eq_one_iff _).1 hk'⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : (x ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hm']
  have hKN : K ≤ N := le_pCore 2 hKn hK2
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hKN hy

theorem card_le_of_elem_quotient {N : Subgroup D} [N.Normal] (hN2 : IsPGroup 2 ↥N) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hr : ∀ A : Subgroup D, IsElemAbelian p A → Nat.card A ≤ p ^ 2)
    (A : Subgroup (D ⧸ N)) (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 2 := by
  set f := QuotientGroup.mk' N with hf
  set W := A.comap f with hW
  have hNW : N ≤ W := fun n hn => by
    show f n ∈ A
    rw [hf, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn]
    exact one_mem A
  have hmapW : W.map f = A := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) A
  have hkerf : f.ker = N := QuotientGroup.ker_mk' N
  have hcardW : Nat.card W = Nat.card A * Nat.card N := by
    have h1 := relIndex_mul_card f.ker W
    rw [relIndex_ker, hmapW, hkerf, inf_eq_left.2 hNW] at h1
    exact h1.symm
  have hAp : IsPGroup p ↥A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥W) p (n := k) (by
    rw [hcardW, hk]
    exact dvd_mul_right _ _)
  set K := K₀.map W.subtype with hKdef
  have hKc : Nat.card K = p ^ k := by rw [card_map_of_injective W.subtype_injective, hK₀]
  have hKW : K ≤ W := map_subtype_le K₀
  have hKp : IsPGroup p ↥K := IsPGroup.of_card hKc
  have hKN : ∀ x ∈ K, f x = 1 → x = 1 := by
    intro x hx hfx
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 hfx
    obtain ⟨a, ha⟩ := hKp ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hN2 ⟨x, hxN⟩
    have ha' : x ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hb' : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hcop : Nat.Coprime (p ^ a) (2 ^ b) := Nat.Coprime.pow a b
      ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha')
      (orderOf_dvd_of_pow_eq_one hb'))
  have hinj : ∀ x ∈ K, ∀ y ∈ K, f x = f y → x = y := by
    intro x hx y hy hxy
    have := hKN (x * y⁻¹) (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    rwa [mul_inv_eq_one] at this
  have hKe : IsElemAbelian p K := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj _ (mul_mem a.2 b.2) _ (mul_mem b.2 a.2) ?_)⟩⟩,
      fun x hx => hinj _ (pow_mem hx p) _ (one_mem K) ?_⟩
    · show f ((a : D) * b) = f ((b : D) * a)
      rw [map_mul, map_mul]
      have hc := hA.1.is_comm.comm ⟨f a, hKW a.2⟩ ⟨f b, hKW b.2⟩
      exact congrArg Subtype.val hc
    · rw [map_pow, map_one]
      exact hA.2 _ (hKW hx)
  have hle := hr K hKe
  rw [hKc] at hle
  rw [hk]
  exact hle

theorem le_centralizer_opResidual_three {X : Subgroup D} (hO2 : Open.pCore 2 D = ⊥)
    (hX : ∀ p : ℕ, p.Prime → 5 ≤ p → X ≤ centralizer (Open.pCore p D : Set D)) :
    X ≤ centralizer (opResidual 3 (genFittingFitting D) : Set D) := by
  have hFnil : Group.IsNilpotent ↥(genFittingFitting D) := CFSG.fittingSubgroup_nilpotent
  have hFn : (genFittingFitting D).Normal := CFSG.fittingSubgroup_normal
  have hpel : ∀ p : ℕ, p.Prime → ∀ x ∈ genFittingFitting D, ∀ e : ℕ, x ^ p ^ e = 1 →
      x ∈ Open.pCore p D := by
    intro p hp x hx e he
    have : Fact p.Prime := ⟨hp⟩
    set P := pCoreOf p (genFittingFitting D) with hPdef
    have hPn : P.Normal := by
      refine ⟨fun y hy g => ?_⟩
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup p (genFittingFitting D)) ⟨y, hy⟩
      have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine mem_pCoreOf_of_isNilpotent (hFn.conj_mem y (pCoreOf_le p _ hy) g) (e := k) ?_
      rw [conj_pow, hk', mul_one, mul_inv_cancel]
    exact le_pCore p hPn (pCoreOf_isPGroup p _) (mem_pCoreOf_of_isNilpotent hx he)
  have key : ∀ n : ℕ, ∀ x ∈ genFittingFitting D, orderOf x = n → (orderOf x).Coprime 3 →
      ∀ y ∈ X, y * x = x * y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn hx3 y hy
      by_cases h1 : orderOf x = 1
      · rw [orderOf_eq_one_iff.1 h1, mul_one, one_mul]
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨a, b, rfl, hab, ⟨e, he⟩, hb, haz, hbz⟩ := exists_mul_eq_pPart hp x
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (Nat.Coprime.symm hx3) hpd
      have haF : a ∈ genFittingFitting D := (zpowers_le.2 hx) haz
      have hbF : b ∈ genFittingFitting D := (zpowers_le.2 hx) hbz
      have haO := hpel p hp a haF e he
      have hya : y * a = a * y := by
        rcases eq_or_ne p 2 with rfl | hp2
        · rw [hO2, mem_bot] at haO
          rw [haO, mul_one, one_mul]
        · have hp5 : 5 ≤ p := by
            have := hp.two_le
            rcases Nat.lt_or_ge p 5 with h | h
            · interval_cases p <;> simp_all (config := { decide := true })
            · exact h
          exact (mem_centralizer_iff.1 (hX p hp hp5 hy) a haO).symm
      have hbd : orderOf b ∣ orderOf (a * b) := orderOf_dvd_of_mem_zpowers hbz
      have hblt : orderOf b < n := by
        rw [← hxn]
        refine lt_of_le_of_ne (Nat.le_of_dvd (orderOf_pos _) hbd) fun heq => ?_
        rw [heq] at hb
        exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.symm hb) hpd
      have hyb := ih _ hblt b hbF rfl (Nat.Coprime.coprime_dvd_left hbd hx3) y hy
      calc y * (a * b) = (y * a) * b := by group
        _ = a * (y * b) := by rw [hya]; group
        _ = a * (b * y) := by rw [hyb]
        _ = a * b * y := by group
  intro y hy
  rw [mem_centralizer_iff]
  intro z hz
  have hle : opResidual 3 (genFittingFitting D) ≤ centralizer ({y} : Set D) := by
    rw [opResidual, closure_le]
    rintro x ⟨hxF, hx3⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (key _ x hxF rfl hx3 y hy).symm
  exact mem_centralizer_singleton_iff.1 (hle hz)

theorem prime_dvd_quot_pCore {D₀ : Type} [Group D₀] [Finite D₀] {G₁ G₂ : Subgroup D₀}
    (h : IsGoldschmidtTriple G₁ G₂) (hsolv : Group.IsSolvable D₀)
    (hsq : SQTKTauCeti.StronglyQuasithin D₀)
    (hT : Nat.card ↥(G₁ ⊓ G₂) ≤ 4 * Nat.card ↥(Open.pCore 2 D₀))
    (hQ : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) {q : ℕ} (hq : q.Prime)
    (hqd : q ∣ Nat.card (D₀ ⧸ Open.pCore 2 D₀)) : q = 2 ∨ q = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Open.pCore 2 D₀ with hNdef
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hNT : N ≤ G₁ ⊓ G₂ := h.pCore_le_inf
  set f := QuotientGroup.mk' N with hf
  have h' := goldschmidtTriple_map_quotient h N hN2 hNT
  have hT' : Nat.card ↥(G₁.map f ⊓ G₂.map f) ≤ 4 := by
    rw [← map_inf_quotient hNT]
    have h1 := relIndex_mul_card f.ker (G₁ ⊓ G₂)
    rw [relIndex_ker, hf, QuotientGroup.ker_mk', inf_eq_left.2 hNT] at h1
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    have h2 : Nat.card ↥((G₁ ⊓ G₂).map (QuotientGroup.mk' N)) * Nat.card ↥N ≤ 4 * Nat.card ↥N := by
      rw [h1]
      exact hT
    exact Nat.le_of_mul_le_mul_right h2 hpos
  have hNQ : ∀ {G : Subgroup D₀}, N ≤ G → N ≤ pCoreOf 2 G := fun hNG =>
    le_pCoreOf_of_le_normalizer 2 hNG (fun g _ => (normalizer_eq_top_iff.mpr hNn).ge (mem_top g))
      hN2
  have hQ' : pCoreOf 2 (G₁.map f) ≠ pCoreOf 2 (G₂.map f) := by
    rw [pCoreOf_map_quotient hN2, pCoreOf_map_quotient hN2]
    intro he
    apply hQ
    have hk : ∀ {G : Subgroup D₀}, N ≤ G → f.ker ≤ pCoreOf 2 G := fun hNG => by
      rw [hf, QuotientGroup.ker_mk']
      exact hNQ hNG
    rw [← comap_map_eq_self (hk (hNT.trans inf_le_left)), he,
      comap_map_eq_self (hk (hNT.trans inf_le_right))]
  have hr : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ A : Subgroup (D₀ ⧸ N), IsElemAbelian p A →
      Nat.card A ≤ p ^ 2 := by
    intro p hp hp2 A hA
    have : Fact p.Prime := ⟨hp⟩
    refine card_le_of_elem_quotient hN2 hp2 (fun A' hA' => ?_) A hA
    have hA'p : IsPGroup p ↥A' := fun a => ⟨1, Subtype.ext (by simpa using hA'.2 a a.2)⟩
    obtain ⟨k, hk⟩ := hA'p.exists_card_eq
    have h1 := le_pRank hp le_top hA' hk
    have h2 := hsq p hp hp2
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (h1.trans h2)
  have hcent : ∀ p : ℕ, p.Prime → 5 ≤ p → twoResidual (⊤ : Subgroup (D₀ ⧸ N)) ≤
      centralizer (Open.pCore p (D₀ ⧸ N) : Set (D₀ ⧸ N)) := by
    intro p hp hp5
    have : Fact p.Prime := ⟨hp⟩
    have : (Open.pCore p (D₀ ⧸ N)).Normal := CFSG.LieType.BorelTits.pCore_normal p
    exact twoResidual_le_centralizer_of_isCyclic h'
      (isCyclic_pCore_of_goldschmidt h' hT' hQ' hp5 (hr p hp (by omega)))
  have hL : twoResidual (G₁.map f) ≤
      centralizer (opResidual 3 (genFittingFitting (D₀ ⧸ N)) : Set (D₀ ⧸ N)) :=
    (twoResidual_mono le_top).trans (le_centralizer_opResidual_three
      pCore_quotient_pCore_eq_bot' fun p hp hp5 => hcent p hp hp5)
  have hsolv' : Group.IsSolvable (D₀ ⧸ N) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)
  exact prime_eq_two_or_three_of_pRank_le_two h' hsolv' f (QuotientGroup.mk'_surjective N)
    (hsq 3 Nat.prime_three (by norm_num)) (Or.inl hL) hq hqd

end CFSG.Quasithin.H13.U3
