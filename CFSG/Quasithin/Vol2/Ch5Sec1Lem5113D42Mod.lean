module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D42Type
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113ModOrth

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

section Char

variable {G : Type} [Group G]
variable {L T W : Subgroup G} {F : Type} [Field F]
variable (hLW : L ≤ Subgroup.normalizer (W : Set G)) (ψ : ↥(autOn L W) ≃* SL(2, F))
  (hP : ∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn (T ⊓ L) W ↔ ∃ b : F, ψ x = unipSL b)

include hLW ψ hP in
theorem le_inf_of_inverts_d42 [Finite G] [Finite F] [CharP F 2] {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    {D K Dm : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hDm : Dm ≤ D)
    (hDme : ∀ x ∈ Dm, x ^ (2 ^ m + 1) = 1) {t d : G} (ht : t ∈ T) (hd : d ∈ D) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1) (htd : t * d * t⁻¹ = d⁻¹) (htK : t ∈ K)
    (hDmK : Dm ≤ Subgroup.normalizer (K : Set G))
    (hSK : T ⊓ L ≤ Subgroup.normalizer (K : Set G)) :
    Dm ≤ D ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCL : L ⊓ Subgroup.centralizer (W : Set G) ≤ T := fun x hx =>
    hC ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  set B := borelL T L with hBdef
  set P := T ⊓ L with hPdef
  have hPB : P ≤ B := Hyp5_0_1.inf_le_borel T L
  have hBN : B ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hSB : IsSylowTwoOf P B := A4.isSylowTwoOf_mono hS hPB inf_le_left
  have hP2 : IsPGroup 2 P := hS.2.1
  have hDodd : Odd (Nat.card D) := hD.2.1
  have hDB : D ≤ B := hD.1
  have hBodd : Odd (P.relIndex B) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSB.2.2)
  have hBDP : P ⊔ D = B := by
    rw [sup_comm]
    exact sup_eq_of_isHall_isSylow hD hSB
  have hPt : t ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTL ht⟩
  have hconjB : ∀ b ∈ B, t * b * t⁻¹ ∈ B := fun b hb =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hTL ht) b).mp hb.1, Subgroup.mul_mem _
      (Subgroup.mul_mem _ hPt hb.2) (Subgroup.inv_mem _ hPt)⟩
  have hn : 1 ≤ 2 * m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have := Finite.one_lt_card (α := F)
      rw [hcard] at this
      norm_num at this
    · omega
  obtain ⟨σ, hσ⟩ := exists_borelChar_conj hLW ψ hP hn hcard hTL hTW ht
  obtain ⟨j, hj⟩ := exists_eq_pow_two_pow hcard σ
  have hσc : ∀ (b : G) (hb : b ∈ B) (hb' : t * b * t⁻¹ ∈ B),
      borelChar hLW ψ hP ⟨t * b * t⁻¹, hb'⟩ = borelChar hLW ψ hP ⟨b, hb⟩ ^ 2 ^ j :=
    fun b hb hb' => by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hσ b hb hb', hj]
  have hχ1 : ∀ (s : G) (hs : s ∈ P) (hsB : s ∈ B), borelChar hLW ψ hP ⟨s, hsB⟩ = 1 :=
    fun s hs hsB => borelChar_eq_one hLW ψ hP hs hsB
  have hχinj : ∀ δ ∈ D, ∀ (hδB : δ ∈ B), borelChar hLW ψ hP ⟨δ, hδB⟩ = 1 → δ = 1 :=
    fun δ hδ hδB h1 => eq_one_of_borelChar hLW ψ hP hCL hP2 hDodd hδ hδB h1
  set χ := borelChar hLW ψ hP with hχ
  have hdB : d ∈ B := hDB hd
  have hjodd : Odd j := by
    have hc1 : χ ⟨d, hdB⟩ ≠ 1 := fun h1 => hd1 (hχinj d hd hdB h1)
    have hc3 : χ ⟨d, hdB⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have e : (⟨d, hdB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [e, map_one]
    have hcinv : χ ⟨t * d * t⁻¹, hconjB d hdB⟩ = χ ⟨d, hdB⟩ ^ 2 := by
      have e : (⟨t * d * t⁻¹, hconjB d hdB⟩ : ↥B) = (⟨d, hdB⟩ : ↥B)⁻¹ := Subtype.ext htd
      rw [e, map_inv]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hc3)
    have h1 := hσc d hdB (hconjB d hdB)
    rw [hcinv] at h1
    exact odd_of_pow_two_pow_eq_sq hc3 hc1 h1.symm
  set Q := K ⊓ B with hQdef
  have hQB : Q ≤ B := inf_le_right
  have hQK : Q ≤ K := inf_le_left
  set P' := P ⊓ Q with hP'def
  have hP'Q : P' ≤ Q := inf_le_right
  have hQN : Q ≤ Subgroup.normalizer (P' : Set G) := fun _ hq =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hBN (hQB hq), Subgroup.le_normalizer hq⟩
  have hPQodd : Odd (P.relIndex Q) := by
    have h1 : P.relIndex (Q ⊔ P) = P.relIndex Q := by
      have hA := hQB.trans hBN
      have := Subgroup.normal_subgroupOf_of_le_normalizer hA
      have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
      exact Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient Q P hA).toEquiv.symm
    have h2 := Subgroup.relIndex_mul_relIndex P (Q ⊔ P) B le_sup_right (sup_le hQB hPB)
    rw [← h1]
    exact hBodd.of_dvd_nat (Dvd.intro _ h2)
  have hP'relQ : P'.relIndex Q = P.relIndex Q := Subgroup.inf_relIndex_right P Q
  have hcop : Nat.Coprime (Nat.card P') (P'.relIndex Q) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hP2.to_le (inf_le_left : P' ≤ P))
    rw [hk, hP'relQ]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hPQodd)
  obtain ⟨E, hEQ, -, hP'E, hEcard, -⟩ := exists_complement_of_coprime hP'Q hQN hcop
  have hEodd : Odd (Nat.card E) := by
    rw [hEcard, hP'relQ]
    exact hPQodd
  set Y₀ := P ⊔ E with hY₀
  have hEB : E ≤ B := hEQ.trans hQB
  have hY₀B : Y₀ ≤ B := sup_le hPB hEB
  have hY₀odd : Odd (P.relIndex Y₀) := by
    have h2 := Subgroup.relIndex_mul_relIndex P Y₀ B le_sup_left hY₀B
    exact hBodd.of_dvd_nat (Dvd.intro _ h2)
  have hPE : P ⊓ E = ⊥ := inf_eq_bot_of_odd_of_isPGroup hP2 hEodd
  have hPD1 : P ⊓ (D ⊓ Y₀) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [← inf_eq_bot_of_odd_of_isPGroup hP2 hDodd]
    exact ⟨hy.1, hy.2.1⟩
  have hPD2 : P ⊔ (D ⊓ Y₀) = Y₀ := by
    apply le_antisymm (sup_le le_sup_left inf_le_right)
    have h1 := inf_sup_le_sup_inf (le_sup_left : P ≤ Y₀) (hDB.trans hBN)
    rw [hBDP, inf_eq_left.mpr hY₀B] at h1
    rw [inf_comm]
    exact h1
  obtain ⟨x, hxP, hEx⟩ := exists_mem_conj_of_complements (le_sup_left : P ≤ Y₀) (hY₀B.trans hBN)
    hP2 hY₀odd inf_le_right hPD1 hPD2 (le_sup_right : E ≤ Y₀) hPE rfl
  have hE1K : D ⊓ Y₀ ≤ D ⊓ K := by
    intro e he
    refine ⟨he.1, ?_⟩
    have hxe : x * e * x⁻¹ ∈ E := by
      rw [hEx]
      exact ⟨e, he, rfl⟩
    have h2 : x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hSK (P.inv_mem hxP)) _).mp (hQK (hEQ hxe))
    have e2 : x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e := by group
    rwa [e2] at h2
  have hDmB : ∀ z ∈ Dm, z ∈ B := fun z hz => hDB (hDm hz)
  have hkey : ∀ z : ↥Dm, ∃ e : ↥(D ⊓ K), χ ⟨e, hDB e.2.1⟩ =
      χ ⟨z, hDmB z z.2⟩ ^ 2 ^ j * (χ ⟨z, hDmB z z.2⟩)⁻¹ := by
    rintro ⟨z, hz⟩
    have hzB := hDmB z hz
    have hkB : t * z * t⁻¹ * z⁻¹ ∈ B := B.mul_mem (hconjB z hzB) (B.inv_mem hzB)
    have hkK : t * z * t⁻¹ * z⁻¹ ∈ K := by
      have h1 : z * t⁻¹ * z⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hDmK hz) _).mp (K.inv_mem htK)
      have e : t * z * t⁻¹ * z⁻¹ = t * (z * t⁻¹ * z⁻¹) := by group
      rw [e]
      exact K.mul_mem htK h1
    have hχk : χ ⟨t * z * t⁻¹ * z⁻¹, hkB⟩ = χ ⟨z, hzB⟩ ^ 2 ^ j * (χ ⟨z, hzB⟩)⁻¹ := by
      have e : (⟨t * z * t⁻¹ * z⁻¹, hkB⟩ : ↥B) =
          ⟨t * z * t⁻¹, hconjB z hzB⟩ * (⟨z, hzB⟩ : ↥B)⁻¹ := rfl
      rw [e, map_mul, map_inv, hσc z hzB (hconjB z hzB)]
    have hk' : t * z * t⁻¹ * z⁻¹ ∈ ((P' ⊔ E : Subgroup G) : Set G) := by
      rw [hP'E]
      exact ⟨hkK, hkB⟩
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P' E (hEQ.trans hQN)] at hk'
    obtain ⟨p, hp, e', he', hpe⟩ := hk'
    rw [hEx] at he'
    obtain ⟨e, he, hee⟩ := he'
    refine ⟨⟨e, hE1K he⟩, ?_⟩
    show χ ⟨e, hDB (hE1K he).1⟩ = χ ⟨z, hzB⟩ ^ 2 ^ j * (χ ⟨z, hzB⟩)⁻¹
    rw [← hχk]
    have hpB : p ∈ B := hPB hp.1
    have hxB : x ∈ B := hPB hxP
    have heB : e ∈ B := hDB he.1
    have e2 : (⟨t * z * t⁻¹ * z⁻¹, hkB⟩ : ↥B) =
        ⟨p, hpB⟩ * (⟨x, hxB⟩ * ⟨e, heB⟩ * (⟨x, hxB⟩ : ↥B)⁻¹) := by
      apply Subtype.ext
      show t * z * t⁻¹ * z⁻¹ = p * (x * e * x⁻¹)
      rw [← hpe, ← hee]
      simp [MulAut.conj_apply]
    rw [e2, map_mul, map_mul, map_mul, map_inv, hχ1 p hp.1 hpB, hχ1 x hxP hxB]
    simp
  choose f hf using hkey
  have hfinj : Function.Injective f := by
    intro z z' hzz'
    have hzz : χ ⟨z, hDmB z z.2⟩ ^ 2 ^ j * (χ ⟨z, hDmB z z.2⟩)⁻¹ =
        χ ⟨z', hDmB z' z'.2⟩ ^ 2 ^ j * (χ ⟨z', hDmB z' z'.2⟩)⁻¹ := by
      rw [← hf z, ← hf z', hzz']
    have hwDm : (z : G) * (z' : G)⁻¹ ∈ Dm := Dm.mul_mem z.2 (Dm.inv_mem z'.2)
    have hwB := hDmB _ hwDm
    have hχw : χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ = χ ⟨z, hDmB z z.2⟩ * (χ ⟨z', hDmB z' z'.2⟩)⁻¹ := by
      have e : (⟨(z : G) * (z' : G)⁻¹, hwB⟩ : ↥B) =
          ⟨z, hDmB z z.2⟩ * (⟨z', hDmB z' z'.2⟩ : ↥B)⁻¹ := rfl
      rw [e, map_mul, map_inv]
    have hfix : χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ ^ 2 ^ j = χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ := by
      rw [hχw, ← div_eq_mul_inv, div_pow, div_eq_div_iff_mul_eq_mul]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at hzz
      rw [hzz, mul_comm]
    have hw1 : (χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ : F) = 1 := by
      refine eq_one_of_pow_add_one hcard hjodd ?_ ?_
      · rw [← Units.val_pow_eq_pow_val, ← map_pow]
        have e : (⟨(z : G) * (z' : G)⁻¹, hwB⟩ : ↥B) ^ (2 ^ m + 1) = 1 :=
          Subtype.ext (by simpa using hDme _ hwDm)
        rw [e, map_one, Units.val_one]
      · rw [← Units.val_pow_eq_pow_val, hfix]
    have hw : (z : G) * (z' : G)⁻¹ = 1 :=
      hχinj _ (hDm hwDm) hwB (Units.ext (by rw [hw1, Units.val_one]))
    exact Subtype.ext (mul_inv_eq_one.mp hw)
  have hχD : ∀ a ∈ D, ∀ b ∈ D, ∀ (ha : a ∈ B) (hb : b ∈ B), χ ⟨a, ha⟩ = χ ⟨b, hb⟩ → a = b := by
    intro a haD b hbD ha hb hab
    have hw : a * b⁻¹ ∈ D := D.mul_mem haD (D.inv_mem hbD)
    have h1 : χ ⟨a * b⁻¹, B.mul_mem ha (B.inv_mem hb)⟩ = 1 := by
      have e : (⟨a * b⁻¹, B.mul_mem ha (B.inv_mem hb)⟩ : ↥B) = ⟨a, ha⟩ * (⟨b, hb⟩ : ↥B)⁻¹ := rfl
      rw [e, map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hχinj _ hw _ h1)
  have hgz : ∀ z : ↥Dm, (z : G) ^ 2 ^ j * (z : G)⁻¹ ∈ Dm := fun z =>
    Dm.mul_mem (Dm.pow_mem z.2 _) (Dm.inv_mem z.2)
  have hfz : ∀ z : ↥Dm, (f z : G) = (z : G) ^ 2 ^ j * (z : G)⁻¹ := by
    intro z
    refine hχD _ (f z).2.1 _ (hDm (hgz z)) (hDB (f z).2.1) (hDmB _ (hgz z)) ?_
    rw [hf z]
    have e : (⟨(z : G) ^ 2 ^ j * (z : G)⁻¹, hDmB _ (hgz z)⟩ : ↥B) =
        (⟨z, hDmB z z.2⟩ : ↥B) ^ 2 ^ j * (⟨z, hDmB z z.2⟩ : ↥B)⁻¹ := by
      apply Subtype.ext
      simp
    rw [e, map_mul, map_pow, map_inv]
  let g : ↥Dm → ↥Dm := fun z => ⟨(z : G) ^ 2 ^ j * (z : G)⁻¹, hgz z⟩
  have hginj : Function.Injective g := fun z z' h =>
    hfinj (Subtype.ext (by rw [hfz, hfz]; exact congrArg Subtype.val h))
  have hgsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hginj
  intro y hy
  obtain ⟨z, hz⟩ := hgsurj ⟨y, hy⟩
  have hzy : (f z : G) = y := by
    rw [hfz]
    exact congrArg Subtype.val hz
  rw [← hzy]
  exact (f z).2

include hLW ψ hP in
theorem le_one_of_dMinus_d42 [Finite G] [Finite F] [CharP F 2] {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    {D K Dm : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hDm : Dm ≤ D)
    (hDmc : Nat.card Dm = 2 ^ m + 1) {t d : G} (ht : t ∈ T) (hd : d ∈ D) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1) (htd : t * d * t⁻¹ = d⁻¹) (htK : t ∈ K)
    (hDmK : Dm ≤ Subgroup.normalizer (K : Set G))
    (hSK : T ⊓ L ≤ Subgroup.normalizer (K : Set G)) (hDK9 : ¬ 9 ∣ Nat.card ↥(D ⊓ K))
    (hDKc : Nat.card ↥(D ⊓ K) ∣ 211341312) : m ≤ 1 := by
  have hDme : ∀ x ∈ Dm, x ^ (2 ^ m + 1) = 1 := fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥Dm) ^ Nat.card Dm = 1 := pow_card_eq_one'
    rw [hDmc] at h1
    simpa using congrArg Subtype.val h1
  have hle := le_inf_of_inverts_d42 hLW ψ hP hcard hTL hTW hC hS hD hDm hDme ht hd hd1 hd3 htd
    htK hDmK hSK
  have h1 : 2 ^ m + 1 ∣ Nat.card ↥(D ⊓ K) := hDmc ▸ Subgroup.card_dvd_of_le hle
  have h2 : 2 ^ m + 1 ∣ 211341312 := h1.trans hDKc
  by_contra hm
  have hm2 : 2 ≤ m := by omega
  have hle' : 2 ^ m + 1 ≤ 211341312 := Nat.le_of_dvd (by norm_num) h2
  have hm28 : m < 28 := by
    by_contra h28
    have : 2 ^ 28 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m
  all_goals first
    | (norm_num at h1; exact hDK9 h1)
    | (norm_num at h2)


end Char

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem mod_orth_d42 (h513 : Stmt5_1_3) (h432 : Stmt4_3_2)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hty : Type3D4 T D X (conjClosure Kh₁ T) (oTwoUpper H))
    (hX : X = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) {k : ℕ} (hk2 : 2 ≤ k)
    (hVo : IsOrthCh5 L V (2 * k)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hN := m.nota
  have hV := m.module
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Main513.T_le_centralizer_omega T
  have hTX : T ≤ X := hX ▸ hTZ
  have hKh₁X : Kh₁ ≤ X := A3.subnormal_le m.hat.1.2.2.1
  have hKhX : conjClosure Kh₁ T ≤ X := conjClosure_le fun t ht y hy =>
    X.mul_mem (X.mul_mem (hTX ht) (hKh₁X hy)) (X.inv_mem (hTX ht))
  obtain ⟨-, hKhres, D₃, hD₃, hD₃3, -, hDK9, hDKc, t, htTK, htinv⟩ := id hty
  obtain ⟨d, hdD₃, hd1⟩ : ∃ d ∈ D₃, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have hb : D₃ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [hb, Subgroup.card_bot] at hD₃3
    omega
  have hdL : d ∈ L := (hN.2.1.1 (hD₃ hdD₃).1).1
  have hd3 : d ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨d, hdD₃⟩ : ↥D₃)
    rw [hD₃3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdZ : d ∈ Subgroup.centralizer (Z : Set G) := by
    have := hKhX (hD₃ hdD₃).2
    rw [hX] at this
    exact this
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  have hKZ : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
    (m.lt.le.trans hKhX).trans hX.le
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := hKT ▸ sup_le hKZ hTZ
  have hZL := m.inf_centralizer_eq_bot h432 hHZ
  have hred := hV.isTwoReducedIn
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hS := h.isSylowTwoOf_inf
  have hD := hN.2.1
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T :=
    (h.setting516 hD hV).sup_inf_centralizer_le hred.2.1 fun hle => hV.2.2
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle))
  obtain ⟨F, _, _, _, hF, ψ, -, -, -, -, -, hP⟩ := hVo.exists_sylowCoord hS
  have hn : n = 2 * k := by
    have h1 := (h.isCyclic_card_of_isHall l2TorusFact hD).2
    have h2 := card_hall_eq_card_units hLV ψ hP hCV hS hD
    rw [Nat.card_units, hF, h1] at h2
    have h3 : 2 ^ n = 2 ^ (2 * k) := by
      have := Nat.one_le_two_pow (n := n)
      have := Nat.one_le_two_pow (n := 2 * k)
      omega
    exact Nat.pow_right_injective le_rfl h3
  have hn2 : n ≠ 2 := by omega
  set R := reducedAggregate (L ⊔ T) with hRdef
  have hR : IsCh5Module T L R := hV.isCh5Module_reducedAggregate
  have hredR := hR.isTwoReducedIn
  have hRel : IsElemAbelian 2 R := hredR.2.2.1
  have hRT : R ≤ T := h.V_le_T hR
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hredR.2.1
  have hRne : R ≠ ⊥ := fun hb => hR.2.2 (by rw [hb]; exact Subgroup.commutator_bot_left L)
  rcases h513 G T M L R n h hR with ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ |
    ⟨hn2', -, -⟩ | h3 | h4 | ⟨-, h5', -⟩
  ·
    obtain ⟨z, hzR, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hRel le_rfl hRT hTR hRne
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hRel.1.is_comm.comm ⟨a, hsup ▸ Subgroup.mem_sup_left ha⟩
        ⟨b, hsup ▸ Subgroup.mem_sup_right hb⟩ |> congrArg Subtype.val
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hzR)
    have hfix : d * (a * b) * d⁻¹ = a * b := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ (a * b) hzZ, mul_inv_cancel_right]
    have hda : d * a * d⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hdL) a).mp ha
    have hdb : d * b * d⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hdL) b).mp hb
    have hab := eq_of_mul_eq hdisj hda ha hdb hb
      (by rw [← hfix]; group)
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun hb1 => hz1 (by rw [ha1, hb1, mul_one])
      exact h.conj_ne_of_isNatModCh5 hW₂ hdL hd3 hd1 hb hb1 hab.2
    · exact h.conj_ne_of_isNatModCh5 hW₁ hdL hd3 hd1 ha ha1 hab.1
  · exact hn2 hn2'
  ·
    set N := ⁅R, L⁆ with hNdef
    have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hredR.2.1
    have hNR : N ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hLR
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_commutator_of hTR h.T_le_normalizer
    obtain ⟨F', _, _, _, -, ψ', Y', hc⟩ := h3.exists_qcoord hS
    have hNL : ⁅N, L⁆ ≠ ⊥ := fun hb =>
      hc.not_le_centralizer (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
    have hCL := h.inf_centralizer_le hc.le_normalizer hNL
    have hNne : N ≠ ⊥ := hR.2.2
    obtain ⟨z, hzN, hz1, hzZ⟩ :=
      exists_mem_omegaOneCenter hT2 hRel hNR hRT hTN hNne
    have hzC : z ∉ Subgroup.centralizer (L : Set G) := fun hzC => hz1 (by
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzC⟩
      rwa [hZL, Subgroup.mem_bot] at hmem)
    have hY : Y' ⟨z, hzN⟩ ≠ 1 := fun hY => hzC ((hc.ker _).mp hY)
    have hfix : d * z * d⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ z hzZ, mul_inv_cancel_right]
    exact hd1 (hc.eq_one_of_fix_three hCL hdL hd3 hY hfix)
  ·
    obtain ⟨Dm, hDmD, hDmc⟩ := exists_dMinus hLV ψ hP hF hCV hS hD
    have hker := orthKernelFact G L R (T ⊓ L) Dm k (hn ▸ h4) hS (hDmD.trans hD.1) hDmc
    have hZC := h.omega_le_inf_centralizer
    have hDmZ : Dm ≤ Subgroup.centralizer (Z : Set G) := fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hker (hZC hz)) x hx).symm
    have hXK : X ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) := by
      rw [hKhres]
      exact le_normalizer_oThreePrimeResidual X
    have hle := le_one_of_dMinus_d42 hLV ψ hP hF h.T_le_normalizer hTV hCV hS hD hDmD hDmc
      htTK.1 (hD₃ hdD₃).1 hd1 hd3 (htinv d hdD₃) htTK.2 ((hX ▸ hDmZ).trans hXK)
      ((inf_le_left.trans hTX).trans hXK) hDK9 hDKc
    omega
  ·
    exact hn2 (h.n_eq_two_of_isBarS5 hR h5')


theorem mod_d42 (h513 : Stmt5_1_3) (h432 : Stmt4_3_2)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hty : Type3D4 T D X (conjClosure Kh₁ T) (oTwoUpper H))
    (hX : X = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    n = 2 ∧ IsA5ModuleSum L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hN := m.nota
  have hV := m.module
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Main513.T_le_centralizer_omega T
  have hTX : T ≤ X := hX ▸ hTZ
  have hKh₁X : Kh₁ ≤ X := A3.subnormal_le m.hat.1.2.2.1
  have hKhX : conjClosure Kh₁ T ≤ X := conjClosure_le fun t ht y hy =>
    X.mul_mem (X.mul_mem (hTX ht) (hKh₁X hy)) (X.inv_mem (hTX ht))
  obtain ⟨-, -, D₃, hD₃, hD₃3, -, -⟩ := id hty
  obtain ⟨d, hdD₃, hd1⟩ : ∃ d ∈ D₃, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have hb : D₃ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [hb, Subgroup.card_bot] at hD₃3
    omega
  have hdL : d ∈ L := (hN.2.1.1 (hD₃ hdD₃).1).1
  have hd3 : d ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨d, hdD₃⟩ : ↥D₃)
    rw [hD₃3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hdZ : d ∈ Subgroup.centralizer (Z : Set G) := by
    have := hKhX (hD₃ hdD₃).2
    rw [hX] at this
    exact this
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  have hKZ : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
    (m.lt.le.trans hKhX).trans hX.le
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := hKT ▸ sup_le hKZ hTZ
  have hZL := m.inf_centralizer_eq_bot h432 hHZ
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hVT : V ≤ T := h.V_le_T hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVne : V ≠ ⊥ := fun hb => hV.2.2 (by rw [hb]; exact Subgroup.commutator_bot_left L)
  have hS := h.isSylowTwoOf_inf
  rcases h513 G T M L V n h hV with ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ |
    ⟨hn2, -, h2⟩ | h3 | h4 | ⟨h5, h5', h5''⟩
  ·
    exfalso
    obtain ⟨z, hzV, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT2 hVel le_rfl hVT hTV hVne
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hVel.1.is_comm.comm ⟨a, hsup ▸ Subgroup.mem_sup_left ha⟩
        ⟨b, hsup ▸ Subgroup.mem_sup_right hb⟩ |> congrArg Subtype.val
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hzV)
    have hfix : d * (a * b) * d⁻¹ = a * b := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ (a * b) hzZ, mul_inv_cancel_right]
    have hda : d * a * d⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hdL) a).mp ha
    have hdb : d * b * d⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hdL) b).mp hb
    have hab := eq_of_mul_eq hdisj hda ha hdb hb
      (by rw [← hfix]; group)
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun hb1 => hz1 (by rw [ha1, hb1, mul_one])
      exact h.conj_ne_of_isNatModCh5 hW₂ hdL hd3 hd1 hb hb1 hab.2
    · exact h.conj_ne_of_isNatModCh5 hW₁ hdL hd3 hd1 ha ha1 hab.1
  ·
    exact ⟨hn2, isA5ModuleSum_of_s5 (Or.inr h2) h.commutator_eq hT2 h.T_le_normalizer⟩
  ·
    exfalso
    set N := ⁅V, L⁆ with hNdef
    have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
    have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
      le_normalizer_commutator_of hTV h.T_le_normalizer
    obtain ⟨F, _, _, _, -, ψ, Y, hc⟩ := h3.exists_qcoord hS
    have hNL : ⁅N, L⁆ ≠ ⊥ := fun hb =>
      hc.not_le_centralizer (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
    have hCL := h.inf_centralizer_le hc.le_normalizer hNL
    have hNne : N ≠ ⊥ := hV.2.2
    obtain ⟨z, hzN, hz1, hzZ⟩ :=
      exists_mem_omegaOneCenter hT2 hVel hNV hVT hTN hNne
    have hzC : z ∉ Subgroup.centralizer (L : Set G) := fun hzC => hz1 (by
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzC⟩
      rwa [hZL, Subgroup.mem_bot] at hmem)
    have hY : Y ⟨z, hzN⟩ ≠ 1 := fun hY => hzC ((hc.ker _).mp hY)
    have hfix : d * z * d⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hdZ z hzZ, mul_inv_cancel_right]
    exact hd1 (hc.eq_one_of_fix_three hCL hdL hd3 hY hfix)
  ·
    obtain ⟨k, hk, -⟩ := id h4
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by have := h.two_le; omega
      subst hk1
      have hn2 : n = 2 := by omega
      subst hn2
      exact ⟨rfl, Or.inl h4.isA5ModuleUnder⟩
    · exact (m.mod_orth_d42 h513 h432 hty hX hk2 (hk ▸ h4)).elim
  ·
    have hC : V ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxZ : x ∈ Z := mem_quasithinOmegaOneCenter_iff.mpr ⟨hVT hx.1,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hx.2,
        hVel.2 x hx.1⟩
      have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hx.2
      have hmem : x ∈ Z ⊓ Subgroup.centralizer (L : Set G) := ⟨hxZ, hxL⟩
      rwa [hZL] at hmem
    have hVeq : ⁅V, L⁆ = V := by
      have := h5.2
      rwa [hC, sup_bot_eq] at this
    refine ⟨h.n_eq_two_of_isBarS5 hV h5', Or.inl ?_⟩
    rw [← hVeq]
    exact isA5ModuleUnder_of_isS5ModCh5 h5'' h.commutator_eq hT2 h.T_le_normalizer

end Main513

end CFSG.Quasithin.H13
