module

public import CFSG.Quasithin.Vol2.Ch12Sec9List
public import CFSG.Quasithin.Vol2.Ch11SecBL2UBase
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases1
public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped Matrix

variable {Q : Type} [Group Q]

@[expose] def DynkinPair1293 (B K : Subgroup Q) : Prop :=
  (IsPSL 2 7 1 ↥B ∧ IsPSL 2 7 2 ↥K) ∨
    (IsSL2 7 ↥B ∧ ∃ s : Bool, IsPSLEps3 s 7 1 ↥K ∨ IsSLEps3 s 7 ↥K)

@[expose] def DynkinFact1293 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B K S : Subgroup X), B ≤ K → DynkinPair1293 B K →
    QuasithinUnique.IsSylowTwoOf S K → S ≤ Subgroup.normalizer (B : Set X) →
    ∃ s ∈ S, KbarInducesOuter B s

structure Data1293 (B : Subgroup Q) (k c : ℕ) : Prop where
  kc : (k = 3 ∧ c = 168) ∨ (k = 4 ∧ c = 20160)
  iso : Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin k) (ZMod 2))
  cardQ : Nat.card (ModO2 B) = c
  card : ∃ a, Nat.card ↥B = 2 ^ a * c
  dvd : ∀ V : Subgroup ↥B, V.Normal → IsPGroup 2 ↥V → c ∣ Nat.card (↥B ⧸ V)
  odd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card N) → N = ⊥

theorem data1293_of [Finite Q] {B : Subgroup Q} {k : ℕ} (hk : k = 3 ∨ k = 4)
    (e : ModO2 B ≃* Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) :
    Data1293 B k (Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, -⟩ := isSimpleGroup_sl_zmod_two (m := k) (by omega)
  have hs : IsSimpleGroup (ModO2 B) := e.isSimpleGroup
  have hcQ : Nat.card (ModO2 B) = Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) :=
    Nat.card_congr e.toEquiv
  have hkc : (k = 3 ∧ Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) = 168) ∨
      (k = 4 ∧ Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) = 20160) := by
    rcases hk with rfl | rfl
    · exact Or.inl ⟨rfl, card_sl_three_zmod_two⟩
    · exact Or.inr ⟨rfl, card_sl_four_zmod_two⟩
  have hceven : 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) := by
    rcases hkc with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> norm_num
  have hB : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  refine ⟨hkc, ⟨e⟩, hcQ, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
    exact ⟨a, by rw [hB, ha, hcQ, mul_comm]⟩
  · intro V hVn hV2
    have hle : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hV2⟩
    obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hle
    have h1 := V.card_eq_card_quotient_mul_card_subgroup
    refine ⟨t, ?_⟩
    have hV0 : 0 < Nat.card ↥V := Nat.card_pos
    have h2 : Nat.card (↥B ⧸ V) * Nat.card ↥V =
        (Nat.card (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) * t) * Nat.card ↥V := by
      rw [← h1, hB, ht, hcQ]
      ring
    exact Nat.eq_of_mul_eq_mul_right hV0 h2
  · intro N hN hodd
    have hNn : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))).Normal :=
      Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))) with hbot | htop
    · have hle : N ≤ CFSG.pCore 2 ↥B := by
        intro x hx
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥B) x ∈
            N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) := ⟨x, hx, rfl⟩
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp ((CFSG.pCore_isPGroup (p := 2) (G := ↥B)).to_le hle)
      rw [hm] at hodd
      have hm0 : m = 0 := by
        by_contra hm0
        exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hm0).mpr even_two)
      rw [hm0, pow_zero] at hm
      exact Subgroup.eq_bot_of_card_eq _ hm
    · exfalso
      have h1 := Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
      rw [htop, Subgroup.card_top, hcQ] at h1
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hceven.trans h1))

namespace Data1293

variable {B : Subgroup Q} {k c : ℕ}

theorem c_eq (hD : Data1293 B k c) : c = 168 ∨ c = 20160 := by
  rcases hD.kc with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem k_eq_three (hD : Data1293 B k c) (hc : c = 168) : k = 3 := by
  rcases hD.kc with ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · omega

theorem seven_dvd (hD : Data1293 B k c) : 7 ∣ c := by
  rcases hD.c_eq with rfl | rfl <;> norm_num

theorem three_dvd (hD : Data1293 B k c) : 3 ∣ c := by
  rcases hD.c_eq with rfl | rfl <;> norm_num

theorem dvd_card (hD : Data1293 B k c) : c ∣ Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hD.card
  exact ⟨2 ^ a, by rw [ha, mul_comm]⟩

theorem false_of_dvd (hD : Data1293 B k c) {m : ℕ} (h : c ∣ m) (h7 : ¬ 7 ∣ m) : False :=
  h7 (hD.seven_dvd.trans h)

theorem false_of_card (hD : Data1293 B k c) {m : ℕ} (h : Nat.card ↥B = m) (h7 : ¬ 7 ∣ m) :
    False :=
  hD.false_of_dvd (h ▸ hD.dvd_card) h7

theorem k_eq_three_of_dvd (hD : Data1293 B k c) (h : c ∣ 168) : k = 3 := by
  refine hD.k_eq_three ?_
  rcases hD.c_eq with rfl | rfl
  · rfl
  · exact absurd h (by norm_num)

theorem dvd_of_isExt [Finite Q] (hD : Data1293 B k c) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ m, Nat.card V = 2 ^ m) :
    ∃ (V : Subgroup ↥B) (_ : V.Normal), PY (↥B ⧸ V) ∧ c ∣ Nat.card (↥B ⧸ V) := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  obtain ⟨m, hm⟩ := hPV _ hpv
  exact ⟨V, hVn, hpy, hD.dvd V hVn (IsPGroup.of_card hm)⟩

theorem isSL2_of_imgOdd [Finite Q] (hD : Data1293 B k c) {K : Subgroup Q} (hBK : B ≤ K) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hM : IsSL2 r ↥(A313.imgOdd (B.subgroupOf K))) :
    IsSL2 r ↥B := by
  let eB : ↥(B.subgroupOf K) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBK
  let e : (↥(B.subgroupOf K) ⧸ CFSG.oddCore ↥(B.subgroupOf K)) ≃* (↥B ⧸ CFSG.oddCore ↥B) :=
    QuotientGroup.congr _ _ eB (A313.oddCore_map_mulEquiv eB)
  have h1 := IsSL2.of_mulEquiv e (A314.isSL2_quotient_oddCore hr hr5 hM)
  have hO : CFSG.oddCore ↥B = ⊥ := hD.odd _ inferInstance (A37.odd_card_oddCore _)
  exact IsSL2.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
    h1

end Data1293

theorem five_or_seven_of_dvd {p c : ℕ} (hc : c = 168 ∨ c = 20160) (hp : p.Prime) (hp3 : 3 < p)
    (h : p ∣ c) : p = 5 ∨ p = 7 := by
  have hdvd : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 :=
    h.trans (by rcases hc with rfl | rfl <;> norm_num)
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

theorem dvd_of_dvd_two_pow_mul {p b c : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ 2 ^ b * c) :
    p ∣ c :=
  Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.Coprime.pow_right b ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))) h

theorem eq_seven_of_card {p b c : ℕ} (hc : c = 168 ∨ c = 20160) (hp : p.Prime) (hp3 : 3 < p)
    (h : p * (p ^ 2 - 1) = 2 ^ b * c) : p = 7 ∧ c = 168 := by
  have hpc : p ∣ c := dvd_of_dvd_two_pow_mul hp hp3 (h ▸ dvd_mul_right p _)
  have hx : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rcases five_or_seven_of_dvd hc hp hp3 hpc with rfl | rfl
  · exfalso
    norm_num at h
    generalize 2 ^ b = x at h hx
    rcases hc with rfl | rfl <;> omega
  · refine ⟨rfl, ?_⟩
    norm_num at h
    generalize 2 ^ b = x at h hx
    rcases hc with rfl | rfl <;> omega

theorem false_of_card_ext_sl2 {p b c : ℕ} (hc : c = 168 ∨ c = 20160) (hp : p.Prime)
    (hp3 : 3 < p) (h : p * (p ^ 2 - 1) * p ^ 2 = 2 ^ b * c) : False := by
  have hp3c : p ^ 3 ∣ c := by
    have h1 : p ^ 3 ∣ 2 ^ b * c := h ▸ ⟨p ^ 2 - 1, by ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow 3 b ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))) h1
  have hpc : p ∣ c := (dvd_pow_self p (by norm_num)).trans hp3c
  rcases five_or_seven_of_dvd hc hp hp3 hpc with rfl | rfl <;>
    rcases hc with rfl | rfl <;> norm_num at hp3c

section Orders

variable {X : Type} [Group X]

theorem card_alt_five (h : IsAlt 5 X) : Nat.card X = 60 := by
  rw [Vol2.Ch11.SecA.card_of_isAlt (by norm_num) h]
  decide

theorem card_alt_six (h : IsAlt 6 X) : Nat.card X = 360 := by
  rw [Vol2.Ch11.SecA.card_of_isAlt (by norm_num) h]
  decide

theorem card_alt_seven (h : IsAlt 7 X) : Nat.card X = 2520 := by
  rw [Vol2.Ch11.SecA.card_of_isAlt (by norm_num) h]
  decide

theorem card_hat_six (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  rw [Vol2.Ch11.SecA.card_of_isHat h, Vol2.Ch11.SecB.card_alt (by norm_num)]
  decide

theorem card_elemAbelian_two {p : ℕ} (h : IsElemAbelianOfRank p 2 X) : Nat.card X = p ^ 2 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 2 → ZMod p) = p ^ 2
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem nonempty_mulEquiv_sl_of_isPSL {m : ℕ} (h : IsPSL m 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two m K
    (by rw [hK, pow_one]))⟩

theorem isPSL_sl_zmod_two {m : ℕ} (hm : 3 ≤ m) :
    IsPSL m 2 1 (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => ?_, fun h => ?_⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two m (ZMod 2)
      (Nat.card_zmod 2)).symm⟩⟩
  · have := congrArg Prod.fst h
    simp only at this
    omega
  · have := congrArg Prod.fst h
    simp only at this
    omega

end Orders

section Lists

variable {X Y : Type} [Group X] [Group Y]

theorem IsSL27OverE49.of_mulEquiv (e : X ≃* Y) (h : IsSL27OverE49 X) : IsSL27OverE49 Y := by
  obtain ⟨E, ⟨hc, hp⟩, hcard, hcent, hn, ⟨f⟩⟩ := h
  have hn' : (E.map e.toMonoidHom).Normal := hn.map _ e.surjective
  refine ⟨E.map e.toMonoidHom, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_, hn',
    ⟨(QuotientGroup.congr E (E.map e.toMonoidHom) e rfl).symm.trans f⟩⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨z, hz, hzb⟩ := b.2
    have hxz : (⟨x, hx⟩ : ↥E) * ⟨z, hz⟩ = ⟨z, hz⟩ * ⟨x, hx⟩ := hc.is_comm.comm _ _
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hzb]
    change e x * e z = e z * e x
    rw [← map_mul, ← map_mul]
    exact congrArg (fun w : ↥E => e (w : X)) hxz
  · obtain ⟨x, hx, rfl⟩ := hy
    change e x ^ 7 = 1
    rw [← map_pow, hp x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · ext y
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hy
      have h1 : e.symm y ∈ Subgroup.centralizer (E : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have := hy (e x) ⟨x, hx, rfl⟩
        apply e.injective
        rw [map_mul, map_mul, e.apply_symm_apply]
        exact this
      rw [hcent] at h1
      exact ⟨e.symm y, h1, e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩ w hw
      obtain ⟨z, hz, rfl⟩ := hw
      have h1 : x ∈ Subgroup.centralizer (E : Set X) := by rw [hcent]; exact hx
      change e z * e x = e x * e z
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp h1 z hz]

theorem IsList1293Two.of_mulEquiv (e : X ≃* Y) (h : IsList1293Two X) : IsList1293Two Y := by
  rcases h with h | h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr ⟨e.symm.trans f⟩)

theorem IsList1293Three.of_mulEquiv (e : X ≃* Y) (h : IsList1293Three X) :
    IsList1293Three Y := by
  rcases h with h | h | h | h | h | h | h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv e h)))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩)))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩)))))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (IsSL27OverE49.of_mulEquiv e h)))))))

theorem isSL27OverE49_of_case3 [Finite X]
    (hE : IsElemAbelianOfRank 7 2 ↥(CFSG.fittingSubgroup X))
    (hN : NaturalSL2Action 7 X (CFSG.fittingSubgroup X)) : IsSL27OverE49 X := by
  obtain ⟨e⟩ := hE
  obtain ⟨e', ψ, hψ, hker, hact⟩ := hN
  have hcomm : ∀ a b : ↥(CFSG.fittingSubgroup X), a * b = b * a := fun a b =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  refine ⟨CFSG.fittingSubgroup X, ⟨⟨⟨hcomm⟩⟩, fun x hx => ?_⟩, ?_, ?_, inferInstance,
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩⟩
  · have h1 : e (⟨x, hx⟩ ^ 7) = 1 := by
      rw [map_pow]
      generalize e ⟨x, hx⟩ = w
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((7 : ℕ) : ZMod 7) = 0 from rfl, zero_mul]
    have h2 : (⟨x, hx⟩ : ↥(CFSG.fittingSubgroup X)) ^ 7 = 1 :=
      e.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  · rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → ZMod 7) = 49
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  · refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff] at hx
      have hfix : ∀ v : Fin 2 → ZMod 7, (ψ x : Matrix (Fin 2) (Fin 2) (ZMod 7)) *ᵥ v = v := by
        intro v
        obtain ⟨f, hf⟩ := e'.surjective (Multiplicative.ofAdd v)
        have h1 := hact x f
        have h2 : MulAut.conjNormal x f = f := by
          apply Subtype.ext
          rw [MulAut.conjNormal_apply, ← hx (f : X) f.2]
          group
        rw [h2, hf] at h1
        have h3 := congrArg Multiplicative.toAdd h1
        simpa using h3.symm
      have hψ1 : ψ x = 1 := by
        apply Subtype.ext
        ext i j
        have h1 := congrFun (hfix (Pi.single j 1)) i
        rw [Matrix.mulVec_single_one] at h1
        rw [Matrix.SpecialLinearGroup.coe_one]
        simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1
      rw [← hker]
      exact hψ1
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hcomm ⟨h, hh⟩ ⟨x, hx⟩)

end Lists

variable [Finite Q] {B K : Subgroup Q} {k c : ℕ}

namespace Data1293

omit [Finite Q] in
theorem not_c2 (hD : Data1293 B k c) (h : A312C2 B K) : False := by
  obtain ⟨⟨m, hm⟩, -, -⟩ := h
  obtain ⟨hm1, hcard⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hm
  rw [hD.cardQ] at hcard
  have ho := Vol2.Ch11.SecA.odd_oSL2 hm1
  rcases hD.kc with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Vol2.Ch11.SecA.oSL2_ne_21 (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq ho (by decide)
      (hcard.symm.trans (show (168 : ℕ) = 2 ^ 3 * 21 by norm_num)))
  · exact Vol2.Ch11.SecA.oSL2_ne_315 (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq ho (by decide)
      (hcard.symm.trans (show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num)))

omit [Finite Q] in
theorem not_c3 (hD : Data1293 B k c) (h : A312C3 B K) : False := by
  obtain ⟨f, hf, -⟩ := h
  have h3 := Vol2.Ch11.SecA.not_three_dvd_card_of_isSz hf
  rw [hD.cardQ] at h3
  exact h3 hD.three_dvd

omit [Finite Q] in
theorem list_c4 (hD : Data1293 B k c) (h : A312C4 B K) :
    IsList1293Two ↥K ∨ (k = 3 ∧ IsList1293Three ↥K) := by
  obtain ⟨hB, hK, -⟩ := h
  have hc : c = 168 := hD.cardQ.symm.trans (Vol2.Ch11.SecB.card_isPSL_three_two_one hB)
  rcases hK with hK | hK
  · exact Or.inr ⟨hD.k_eq_three hc, Or.inl (nonempty_mulEquiv_sl_of_isPSL hK)⟩
  · exact Or.inl (Or.inl (nonempty_mulEquiv_sl_of_isPSL hK))

omit [Finite Q] in
theorem list_c6 (hD : Data1293 B k c) (h : A312C6 B K) : k = 3 ∧ IsList1293Three ↥K := by
  obtain ⟨hB, hK⟩ := h
  have hk : k = 3 := by
    rcases hB with hB | hB
    · exact (hD.false_of_card (card_alt_five hB) (by norm_num)).elim
    · exact hD.k_eq_three_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hB ▸ hD.dvd_card)
  refine ⟨hk, ?_⟩
  rcases hK with hK | hK
  · exact Or.inr (Or.inl hK)
  · exact Or.inr (Or.inr (Or.inl hK))

omit [Finite Q] in
theorem not_c7 (hD : Data1293 B k c) (h : A312C7 B K) : False := by
  rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
  · exact hD.false_of_card (card_alt_six hB) (by norm_num)
  · exact hD.false_of_card (card_hat_six hB) (by norm_num)

omit [Finite Q] in
theorem not_c8 (hD : Data1293 B k c) (hDyn : ¬ DynkinPair1293 B K) (h : A312C8 B K) : False := by
  rcases h with ⟨p, hp, hp3, hB, hK⟩ | ⟨hB, -⟩
  · have h2 := Vol2.Ch11.SecA.two_mul_card_of_isPSL_two hp (by omega) hB
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨rfl, -⟩ := eq_seven_of_card hD.c_eq hp hp3 (b := a + 1)
      (by rw [← h2, ha, pow_succ]; ring)
    exact hDyn (Or.inl ⟨hB, hK⟩)
  · exact hD.false_of_card (card_alt_five hB) (by norm_num)

omit [Finite Q] in
theorem not_c9 (hD : Data1293 B k c) (hDyn : ¬ DynkinPair1293 B K) (h : A312C9 B K) : False := by
  rcases h with ⟨s, p, hp, hp3, hB, hK⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · obtain ⟨a, ha⟩ := hD.card
    obtain ⟨rfl, -⟩ := eq_seven_of_card hD.c_eq hp hp3
      ((Vol2.Ch11.SecA.card_of_isSL2 hp hB).symm.trans ha)
    exact hDyn (Or.inr ⟨hB, s, hK⟩)
  · exact hD.false_of_card (card_alt_six hB) (by norm_num)
  · exact hD.false_of_card (card_hat_six hB) (by norm_num)

omit [Finite Q] in
theorem not_c10 (hD : Data1293 B k c) (h : A312C10 B K) : False := by
  obtain ⟨p, hp, hp3, ⟨V, hVn, hV, hY⟩, -⟩ := h
  obtain ⟨a, ha⟩ := hD.card
  have h1 := V.card_eq_card_quotient_mul_card_subgroup
  rw [card_elemAbelian_two hV, Vol2.Ch11.SecA.card_of_isSL2 hp hY, ha] at h1
  exact false_of_card_ext_sl2 hD.c_eq hp hp3 h1.symm

omit [Finite Q] in
theorem not_c11 (hD : Data1293 B k c) (h : A312C11 B K) : False :=
  hD.false_of_card (card_alt_six h.1) (by norm_num)

theorem not_c12 (hD : Data1293 B k c) (h : A312C12 B K) : False := by
  have hE : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → ∃ m, Nat.card V = 2 ^ m :=
    fun V _ _ h => ⟨4, Vol2.Ch11.SecA.card_isE2 h⟩
  rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE
    exact hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE
    exact hD.false_of_dvd (card_alt_six hY ▸ hdvd) (by norm_num)
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE
    exact hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE
    exact hD.false_of_dvd (card_hat_six hY ▸ hdvd) (by norm_num)

omit [Finite Q] in
theorem not_psl34 (hD : Data1293 B k c) (hk : k = 4)
    (hB : IsPSL 3 2 2 ↥B) : False := by
  subst hk
  obtain ⟨e⟩ := hD.iso
  have hc : c = 20160 := by
    rcases hD.kc with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  have hcB := Vol2.Ch11.SecB.card_isPSL_three_two_two hB
  have h1 : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  rw [hcB, hD.cardQ, hc] at h1
  have h2 : Nat.card (CFSG.pCore 2 ↥B) = 1 := by omega
  have hbot : CFSG.pCore 2 ↥B = ⊥ := Subgroup.eq_bot_of_card_eq _ h2
  let f : ↥B ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e
  exact l34NotL42Fact1515e_of_cert ↥B hB
    (isPSL_of_mulEquiv1515e f (isPSL_sl_zmod_two (by norm_num)))

theorem list_c13 (hD : Data1293 B k c) (h : A312C13 B K) :
    k = 3 ∧ IsList1293Three ↥K := by
  obtain ⟨hB, hK⟩ := h
  refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl hK)))⟩
  by_contra hk3
  have hk : k = 4 := by rcases hD.kc with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hc : c = 20160 := by
    rcases hD.kc with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  subst hc
  have hE4 : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → ∃ m, Nat.card V = 2 ^ m :=
    fun V _ _ h => ⟨4, Vol2.Ch11.SecA.card_isE2 h⟩
  have hE3 : ∀ (V : Type) [Group V] [Finite V], IsE2 3 V → ∃ m, Nat.card V = 2 ^ m :=
    fun V _ _ h => ⟨3, Vol2.Ch11.SecA.card_isE2 h⟩
  rcases hB with hM | hB | hB | hB | hB | hB | hB
  ·
    obtain ⟨eM⟩ := hM
    obtain ⟨a, ha⟩ := hD.card
    have h11 : 11 ∣ Nat.card ↥B := by
      rw [Nat.card_congr eM.toEquiv]
      exact Vol2.Ch11.SecA.eleven_dvd_card_M22
    rw [ha] at h11
    have := dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h11
    norm_num at this
  · exact hD.not_psl34 hk hB
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE4
    rw [card_alt_seven hY] at hdvd
    norm_num at hdvd
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE4
    rw [Vol2.Ch11.SecB.card_isPSL_three_two_one hY] at hdvd
    norm_num at hdvd
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE3
    rw [Vol2.Ch11.SecB.card_isPSL_three_two_one hY] at hdvd
    norm_num at hdvd
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE4
    rw [card_alt_six hY] at hdvd
    norm_num at hdvd
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB hE4
    rw [card_alt_five hY] at hdvd
    norm_num at hdvd

omit [Finite Q] in
theorem not_c15 (hD : Data1293 B k c) (h : A312C15 B K) : False :=
  hD.false_of_card (card_alt_five h.1) (by norm_num)

theorem not_c16 (hD : Data1293 B k c) (h : A312C16 B K) : False := by
  obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt h.1
    (fun V _ _ h => ⟨1 + 2 * 2, Vol2.Ch11.SecA.card_isExtraspecial2 h⟩)
  exact hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)

theorem list_c18 (hD : Data1293 B k c) (h : A312C18 B K) : k = 3 ∧ IsList1293Three ↥K := by
  obtain ⟨hB, hK⟩ := h
  refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK))))⟩
  rcases hB with hB | hB
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB
      (fun V _ _ h => Vol2.Ch11.SecA.card_isZ4StarExtra2 h)
    exact (hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)).elim
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB
      (fun V _ _ h => ⟨6, Vol2.Ch11.SecA.card_isZ4Cubed h⟩)
    exact hD.k_eq_three_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd)

theorem list_c19 (hD : Data1293 B k c) (h : A312C19 B K) : k = 3 ∧ IsList1293Three ↥K := by
  obtain ⟨hB, hK⟩ := h
  refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK)))))⟩
  rcases hB with hB | hB
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB
      (fun V _ _ h => ⟨1 + 2 * 3, Vol2.Ch11.SecA.card_isExtraspecial2 h⟩)
    exact hD.k_eq_three_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd)
  · obtain ⟨V, hVn, hY, hdvd⟩ := hD.dvd_of_isExt hB
      (fun V _ _ h => ⟨6, Vol2.Ch11.SecA.card_isE2 h⟩)
    exact (hD.false_of_dvd (card_hat_six hY ▸ hdvd) (by norm_num)).elim

omit [Finite Q] in
theorem list_c20 (hD : Data1293 B k c) (h : A312C20 B K) : k = 3 ∧ IsList1293Three ↥K := by
  obtain ⟨hB, -, hK⟩ := h
  refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK))))))⟩
  rcases hB with hB | hB
  · have h60 : c = 60 := hD.cardQ.symm.trans (card_alt_five hB)
    exact (hD.false_of_dvd (m := 60) (by rw [h60]) (by norm_num)).elim
  · exact hD.k_eq_three (hD.cardQ.symm.trans (Vol2.Ch11.SecB.card_isPSL_three_two_one hB))

theorem list_of_case
    (hD : Data1293 B k c) (hDyn : ¬ DynkinPair1293 B K) (h : A312Case B K) :
    IsList1293Two ↥K ∨ (k = 3 ∧ IsList1293Three ↥K) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.not_c2 h).elim
  · exact (hD.not_c3 h).elim
  · exact hD.list_c4 h
  · exact Or.inl (Or.inl (nonempty_mulEquiv_sl_of_isPSL h.2.1))
  · exact Or.inr (hD.list_c6 h)
  · exact (hD.not_c7 h).elim
  · exact (hD.not_c8 hDyn h).elim
  · exact (hD.not_c9 hDyn h).elim
  · exact (hD.not_c10 h).elim
  · exact (hD.not_c11 h).elim
  · exact (hD.not_c12 h).elim
  · exact Or.inr (hD.list_c13 h)
  · exact Or.inl (Or.inr (Or.inl h.2))
  · exact (hD.not_c15 h).elim
  · exact (hD.not_c16 h).elim
  · exact Or.inl (Or.inr (Or.inr h.1))
  · exact Or.inr (hD.list_c18 h)
  · exact Or.inr (hD.list_c19 h)
  · exact Or.inr (hD.list_c20 h)

theorem list_of_nonquasi (hD : Data1293 B k c) (hBK : B ≤ K) (h36 : A36Strong K)
    (h : A312Nonquasi B K) : k = 3 ∧ IsSL27OverE49 ↥K := by
  have hnq := A312.not_quasisimple_of_nonquasi h
  obtain ⟨p₀, hp₀, hp₀3, hΛ⟩ := A312.exists_isSL2_oddCore h36 hnq
  obtain ⟨hconc, hcom, -⟩ := h36
  have hF : CFSG.fittingSubgroup ↥K = CFSG.oddCore ↥K := hcom.1
  have hcase : ∀ p : ℕ, IsSL2 p (↥K ⧸ CFSG.fittingSubgroup ↥K) →
      IsSL2 p (↥K ⧸ CFSG.oddCore ↥K) := fun p h =>
    IsSL2.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hF) h
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hKB, -⟩ | ⟨-, -, N, hNn, hNeq, hN5⟩
  · have htop : A313.imgOdd (B.subgroupOf K) = ⊤ := (A313.imgOdd_eq_top_iff hBK).mpr hKB
    have hM : IsSL2 p₀ ↥(A313.imgOdd (B.subgroupOf K)) :=
      IsSL2.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hΛ
    have hB := hD.isSL2_of_imgOdd hBK hp₀ (A313.five_le_of_prime hp₀ hp₀3) hM
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨rfl, hc⟩ := eq_seven_of_card hD.c_eq hp₀ hp₀3
      ((Vol2.Ch11.SecA.card_of_isSL2 hp₀ hB).symm.trans ha)
    refine ⟨hD.k_eq_three hc, ?_⟩
    rcases hconc with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨p, hp, -, -, hE, hN⟩ | h4
    · exact absurd hc.1 hnq
    · exact absurd hc.1 hnq
    · have h1 : p * (p ^ 2 - 1) = 7 * (7 ^ 2 - 1) :=
        (Vol2.Ch11.SecA.card_of_isSL2 hp
          (hcase p (Vol2.Ch11.SecA.isSL2_of_naturalSL2Action hN))).symm.trans
          (Vol2.Ch11.SecA.card_of_isSL2 hp₀ hΛ)
      have hp7 : p = 7 :=
        Vol2.Ch11.SecA.eq_of_mul_sq_sub_one hp.one_lt.le (by norm_num) h1
      subst hp7
      exact isSL27OverE49_of_case3 hE hN
    · exfalso
      obtain ⟨-, -, h5, -⟩ := h4
      have h1 := (Vol2.Ch11.SecA.card_of_isSL2 Nat.prime_five (hcase 5 h5)).symm.trans
        (Vol2.Ch11.SecA.card_of_isSL2 hp₀ hΛ)
      norm_num at h1
  · exfalso
    subst hNeq
    have hM : IsSL2 5 ↥(A313.imgOdd (B.subgroupOf K)) :=
      IsSL2.of_mulEquiv (A312.quotEquivImage hBK) hN5
    have hB := hD.isSL2_of_imgOdd hBK Nat.prime_five le_rfl hM
    exact hD.false_of_card (Vol2.Ch11.SecA.card_of_isSL2 Nat.prime_five hB) (by norm_num)

end Data1293

end CFSG.Quasithin.H13
