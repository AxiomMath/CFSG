module

public import CFSG.Quasithin.Vol2.Ch11SecGOdd3
public import CFSG.Quasithin.Vol2.Ch11SecG556Odd1
public import CFSG.Quasithin.Vol2.Ch11SecGTMain
public import CFSG.Quasithin.Vol2.Ch11SecDFacts5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom
open scoped MatrixGroups

namespace Bar

variable {G : Type} [Group G]

theorem commute_of_odd {K L₁ : Subgroup G} (hL : L₁ ≤ K) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* SL(2, F)) {M : Subgroup (KBar K)}
    (hMn : ∀ l : ↥L₁, ∀ m ∈ M, rhoL hL l * m * (rhoL hL l)⁻¹ ∈ M)
    (hMr : ∀ m ∈ M, ∀ l : ↥L₁, m * rhoL hL l * m⁻¹ ∈ (rhoL hL).range)
    (hodd : ∀ m ∈ M, ∃ n : ℕ, Odd n ∧ m ^ n = 1) {m : KBar K} (hm : m ∈ M) (l : ↥L₁) :
    m * rhoL hL l = rhoL hL l * m := by
  have hbot : M ⊓ (rhoL hL).range = ⊥ := by
    refine eq_bot_of_odd_of_le_range hL hF e inf_le_right ?_ ?_
    · intro l' x hx
      exact ⟨hMn l' x hx.1, (rhoL hL).range.mul_mem
        ((rhoL hL).range.mul_mem ⟨l', rfl⟩ hx.2) ((rhoL hL).range.inv_mem ⟨l', rfl⟩)⟩
    · intro x hx
      exact hodd x hx.1
  have hc : m * rhoL hL l * m⁻¹ * (rhoL hL l)⁻¹ ∈ M ⊓ (rhoL hL).range := by
    refine ⟨?_, (rhoL hL).range.mul_mem (hMr m hm l) ((rhoL hL).range.inv_mem ⟨l, rfl⟩)⟩
    have h1 := M.mul_mem hm (hMn l _ (M.inv_mem hm))
    simpa [mul_assoc] using h1
  rw [hbot, Subgroup.mem_bot] at hc
  calc m * rhoL hL l = (m * rhoL hL l * m⁻¹ * (rhoL hL l)⁻¹) * (rhoL hL l * m) := by group
    _ = rhoL hL l * m := by rw [hc, one_mul]

end Bar

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem primeAct_of (hAct : SecD.FactCase1PrimeAct) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hne : KOf L V₁ V₁ ≠ LOf L V₁) {p : ℕ} (hp : p.Prime) (hK1 : Case11_1_2One (KOf L V₁ V₁))
    (hPQ : ¬ oTwoPrime (KOf L V₁ V₁) p ≤ pCoreOf 2 (KOf L V₁ V₁)) :
    (∀ y ∈ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁,
      (∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) →
        y ∈ oTwoPrime (KOf L V₁ V₁) p) ∧
    ∀ a : G, a ∈ Subgroup.normalizer (KOf L V₁ V₁ : Set G) → (∃ e : ℕ, a ^ 2 ^ e = 1) →
      (∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, ∀ l ∈ LOf L V₁,
        (a * x * a⁻¹ * x⁻¹) * l * (a * x * a⁻¹ * x⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) →
      ∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁) := by
  set K := KOf L V₁ V₁ with hKdef
  have hTN := SecA.IsVi.le_normalizer hV₁
  have hsylN : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (Subgroup.normalizer (V₁ : Set G)) := by
    rw [inf_eq_left.mpr hTN]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
  obtain ⟨K', hLK', hK', hNK', hcase'⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
    (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsylN⟩)
  have hKK' : K = K' := SecD.kOf_eq_of_cComp hLK' hK' hNK' (SecD.lOf_ne_bot h1110 h hV₁)
  rw [← hKK'] at hcase'
  have hlist : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) n ∨
      (n = 2 ∧ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rcases hcase' with heq | h2 | h3
    · exact absurd heq.symm hne
    · exact Or.inl h2
    · exact Or.inr h3
  exact hAct G K (LOf L V₁) n p hlist hK1 (SecD.conjClosure_perfect (perfectCore_perfect _))
    (le_conjClosure _ _) (perfectCore_perfect _) ((h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁)
    hp hPQ

theorem false_of_transv_prime (hAct : SecD.FactCase1PrimeAct) (hCard : SecD.CardVFact)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1112 : Stmt11_1_2) (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1) (h1151 : Stmt11_5_1)
    (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₃ : IsVi T L I n 3 V₃) (hne : KOf L V₁ V₁ ≠ LOf L V₁) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK1 : Case11_1_2One (KOf L V₁ V₁))
    (hPQ : ¬ oTwoPrime (KOf L V₁ V₁) p ≤ pCoreOf 2 (KOf L V₁ V₁)) {A : Subgroup G}
    (hAH : A ≤ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) (hA2 : IsPGroup 2 A)
    (hAO : ¬ A ≤ pCoreOf 2 (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T))
    (hAY : E3.mQuot (conjClosure V₃ (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T))
      (conjClosure V₃ (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) ⊓
        Subgroup.centralizer (A : Set G)) ≤ 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set L₁ := LOf L V₁ with hL₁def
  set P := oTwoPrime K p with hPdef
  set Q := pCoreOf 2 K with hQdef
  set H₁ := P ⊔ L₁ ⊔ T with hH₁def
  set UH := conjClosure V₃ H₁ with hUHdef
  have hp2 : p ≠ 2 := by omega
  have hLK : L₁ ≤ K := le_conjClosure _ _
  have hPK : P ≤ K := SecD.oTwoPrime_le K p
  have hH₁K := h1p_le_normalizer hV₁ p
  have hH₁P : H₁ ≤ Subgroup.normalizer (P : Set G) :=
    hH₁K.trans (SecD.normalizer_le_normalizer_oTwoPrime K p)
  have hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le ((kOne_le L V₁ p).trans (SecD.kOf_le_normalizer (SecD.lOf_le_normalizer L V₁)))
      (SecA.IsVi.le_normalizer hV₁)
  have hV₃V := SecA.IsVi.le_fsuV hV₃
  have hY : IsElemAbelian 2 UH :=
    F7.isElemAbelian_mono (isElemAbelian_U_of_le h1157 h hV₁ hH₁N) (conjClosure_mono hV₃V le_rfl)
  have hHY : H₁ ≤ Subgroup.normalizer (UH : Set G) := le_normalizer_conjClosure _ _
  have hCY := inf_centralizer_le_of_le hCard h331 h1102 h1110 h1122 h1141 h1151 h hV₁ hV₃
    (le_conjClosure V₃ H₁)
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hn2 : n = 2 := by
    obtain ⟨K'', hLK'', hK'', hNK'', -, hor⟩ :=
      h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
    have hKK'' := SecD.kOf_eq_of_cComp hLK'' hK'' hNK'' (SecD.lOf_ne_bot h1110 h hV₁)
    rcases hor with heq | ⟨-, hn2, -⟩
    · exact absurd (hKK''.trans heq.symm) hne
    · exact hn2
  obtain ⟨hF2, hF1⟩ := primeAct_of hAct h1110 h1111 h hV₁ hne hp hK1 hPQ
  have hL₁q := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hL₁q
  have hF4 : Nat.card F = 4 := by rw [hFc, hn2]; norm_num
  obtain ⟨a, haA, haO⟩ := IsConcreteLE.not_le_iff_exists.mp hAO
  have ha : a ∈ H₁ := hAH haA
  obtain ⟨m, hm⟩ := hA2 ⟨a, haA⟩
  have ham : a ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hm' : E3.mQuot UH (UH ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 1 := by
    refine le_trans (mQuot_anti_right (F7.isPGroup_of_isElemAbelian hY) ?_) hAY
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  obtain ⟨y₀, hy₀, htr⟩ := exists_transv_of_mQuot hY (hHY ha) hm'
  have ha2 := sq_mem_centralizer_of_transv hY hy₀ htr
  have haK : a ∈ Subgroup.normalizer (K : Set G) := hH₁K ha
  set N : Subgroup (Bar.KBar K) :=
    ((P ⊓ Subgroup.centralizer (UH : Set G)).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hNdef
  have hNcomm : ∀ c ∈ N, ∀ l : ↥L₁, c * Bar.rhoL hLK l = Bar.rhoL hLK l * c := by
    intro c hc l
    refine Bar.commute_of_odd hLK hF4 e (M := N) ?_ ?_ ?_ hc l
    · rintro l' _ ⟨x, hx, rfl⟩
      have hL₁H : L₁ ≤ H₁ := le_sup_right.trans le_sup_left
      have hl'H : (l' : G) ∈ H₁ := hL₁H l'.2
      refine ⟨⟨_, hLK l'.2⟩ * x * (⟨_, hLK l'.2⟩ : ↥K)⁻¹, ⟨?_, ?_⟩, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hH₁P hl'H) x).mp hx.1
      · exact conj_mem_centralizer (hHY hl'H) hx.2
      · simp [Bar.rhoL_apply]
    · rintro _ ⟨x, hx, rfl⟩ l'
      have hxL : (x : G) ∈ Subgroup.normalizer (L₁ : Set G) := hCY ⟨hPK hx.1, hx.2⟩
      have hl' : (x : G) * l' * (x : G)⁻¹ ∈ L₁ :=
        (Subgroup.mem_normalizer_iff.mp hxL l').mp l'.2
      refine ⟨⟨_, hl'⟩, ?_⟩
      rw [Bar.rhoL_apply, Bar.rhoL_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := SecD.exists_pow_mem_pCoreOf_of_mem_oTwoPrime hx.1
      refine ⟨p ^ k, (Nat.Prime.odd_of_ne_two hp hp2).pow, ?_⟩
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow]
      exact (mem_pCoreOf_iff_mk_eq_one (x ^ p ^ k)).mp (by simpa using hk)
  have hcomm : ∀ x ∈ P, ∀ l ∈ L₁,
      (a * x * a⁻¹ * x⁻¹) * l * (a * x * a⁻¹ * x⁻¹)⁻¹ * l⁻¹ ∈ Q := by
    intro x hx l hl
    have hPH : P ≤ H₁ := le_sup_left.trans le_sup_left
    have hxH : x ∈ H₁ := hPH hx
    have hcP : a * x * a⁻¹ * x⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hH₁P ha) x).mp hx) (P.inv_mem hx)
    have hcY : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.normalizer (UH : Set G) :=
      mul_mem (mul_mem (mul_mem (hHY ha) (hHY hxH)) (inv_mem (hHY ha))) (inv_mem (hHY hxH))
    obtain ⟨k, hk⟩ := SecD.exists_pow_mem_pCoreOf_of_mem_oTwoPrime hcP
    have hprimes : ∀ r : ℕ, r.Prime → r ∣ p ^ k → 5 ≤ r := fun r hr hrp =>
      ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrp)) ▸ hp5
    obtain ⟨j, hj⟩ := exists_two_pow_mem_centralizer hY (hHY ha) hy₀ htr (pow_pos hp.pos k)
      hprimes (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hcY hk
      (inv_mem_centralizer_commutator' (hHY ha) (hHY hxH) ha2)
    set c : ↥K := ⟨a * x * a⁻¹ * x⁻¹, hPK hcP⟩ with hc
    have hcN : (c : Bar.KBar K) ∈ N := by
      have h1 : (c : Bar.KBar K) ^ 2 ^ j ∈ N := by
        rw [← QuotientGroup.mk_pow]
        exact ⟨c ^ 2 ^ j, ⟨P.pow_mem hcP _, by simpa using hj⟩, rfl⟩
      have h2 : (c : Bar.KBar K) ^ p ^ k ∈ N := by
        rw [← QuotientGroup.mk_pow, (mem_pCoreOf_iff_mk_eq_one (c ^ p ^ k)).mp (by simpa using hk)]
        exact one_mem _
      have h3 := pow_gcd_mem h1 h2
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow j k
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))), pow_one] at h3
    have h4 := hNcomm _ hcN ⟨l, hl⟩
    rw [Bar.rhoL_apply] at h4
    set kl : ↥K := ⟨l, hLK hl⟩ with hkl
    have h5 : ((c * kl * c⁻¹ * kl⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := by
      apply (mem_pCoreOf_iff_mk_eq_one (c * kl * c⁻¹ * kl⁻¹)).mpr
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, h4]
      group
    exact h5
  exact haO (mem_pCoreOf_prime h hV₁ hp hp2 hF2 ha ham (hF1 a haK ⟨m, ham⟩ hcomm))

end CFSG.Quasithin.Vol2.Ch11.SecG
