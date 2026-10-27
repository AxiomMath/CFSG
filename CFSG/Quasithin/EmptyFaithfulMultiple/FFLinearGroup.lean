module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearNat
public import CFSG.Quasithin.Background.G64Case1Pre
public import CFSG.Quasithin.Background.B19Setup
import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.FFL

open CFSG.Open (pCoreOf quasithinGenFitting)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

@[expose] def IsFFLType (X : Type) [Group X] : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSL 3 F))) ∨
    Nonempty (X ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nonempty (X ≃* ↥(StatedSL 5 (ZMod 2)))

@[expose] def IsFFLOrder (N : ℕ) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ N = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∨
    N = 20160 ∨ N = 9999360

theorem isQuasisimple_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y :=
  h.of_mulEquiv e.symm

theorem isQuasisimple_statedSL {m : ℕ} (hm : 2 ≤ m) (K : Type) [Field K] :
    CFSG.IsQuasisimple ↥(StatedSL (m + 1) K) :=
  CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le hm K

theorem IsFFLType.isQuasisimple {X : Type} [Group X] (h : IsFFLType X) :
    CFSG.IsQuasisimple X := by
  rcases h with ⟨n, F, _, _, -, ⟨e⟩⟩ | h | h
  · exact isQuasisimple_of_mulEquiv e.symm (isQuasisimple_statedSL (m := 2) le_rfl F)
  · obtain ⟨e⟩ := h
    exact isQuasisimple_of_mulEquiv e.symm (isQuasisimple_statedSL (m := 3) (by norm_num) _)
  · obtain ⟨e⟩ := h
    exact isQuasisimple_of_mulEquiv e.symm (isQuasisimple_statedSL (m := 4) (by norm_num) _)

theorem card_statedSL_three (F : Type) [Field F] [Fintype F] :
    Nat.card ↥(StatedSL 3 F) =
      Fintype.card F ^ 3 * (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 3 - 1) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv, Matrix.card_SL_field,
    Fin.prod_univ_three]
  set q := Fintype.card F with hq
  have hq2 : 1 < q := Fintype.one_lt_card
  have hq1 : 1 ≤ q := hq2.le
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have h3 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  have h4 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  have key : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q - 1) := by
    zify [hq1, h1, h2, h3, h4]
    ring
  rw [key, Nat.mul_div_cancel _ (by omega)]

theorem card_statedSL_two (F : Type) [Field F] [Fintype F] :
    Nat.card ↥(StatedSL 2 F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv, Matrix.card_SL_field,
    Fin.prod_univ_two]
  set q := Fintype.card F with hq
  have hq2 : 1 < q := Fintype.one_lt_card
  have hq1 : 1 ≤ q := hq2.le
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h3 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have key : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    zify [hq1, h1, h3]
    ring
  rw [key, Nat.mul_div_cancel _ (by omega)]

theorem card_statedSL_four : Nat.card ↥(StatedSL 4 (ZMod 2)) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_zmod_two

theorem card_statedSL_five : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem IsFFLType.card {X : Type} [Group X] (h : IsFFLType X) : IsFFLOrder (Nat.card X) := by
  rcases h with ⟨n, F, _, _, hF, ⟨e⟩⟩ | h | h
  · left
    refine ⟨n, ?_, ?_⟩
    · by_contra h0
      have : n = 0 := by omega
      rw [this, pow_zero] at hF
      have : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    · rw [Nat.card_congr e.toEquiv, card_statedSL_three, hF]
  · obtain ⟨e⟩ := h
    right; left
    rw [Nat.card_congr e.toEquiv, card_statedSL_four]
  · obtain ⟨e⟩ := h
    right; right
    rw [Nat.card_congr e.toEquiv, card_statedSL_five]

theorem card_sl3_cases {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) = 168 ∨
      60480 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    have : n = 1 := by omega
    subst this
    norm_num
  · right
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 4 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 4 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
    calc 60480 = 4 ^ 3 * (4 ^ 2 - 1) * (4 ^ 3 - 1) := by norm_num
      _ ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1))
          (Nat.sub_le_sub_right h1 1)

theorem IsFFLOrder.six_lt {N : ℕ} (h : IsFFLOrder N) : 6 < N := by
  rcases h with ⟨n, hn, rfl⟩ | rfl | rfl
  · rcases card_sl3_cases hn with h | h <;> omega
  · norm_num
  · norm_num

theorem IsFFLOrder.ne_small {N : ℕ} (h : IsFFLOrder N)
    (hN : N = 60 ∨ N = 360 ∨ N = 1080 ∨ N = 2520 ∨ N = 6048) : False := by
  rcases h with ⟨n, hn, rfl⟩ | rfl | rfl
  · rcases card_sl3_cases hn with h | h <;> omega
  · omega
  · omega

theorem two_pow_mul_odd_inj {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  rcases le_total a b with hab | hab
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases k with _ | k
    · simpa using h'
    · exfalso
      rw [h', pow_succ, mul_comm (2 ^ k) 2, mul_assoc] at hx
      exact Nat.not_even_iff_odd.mpr hx (even_two_mul _)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
    rcases k with _ | k
    · simpa using h'.symm
    · exfalso
      rw [h', pow_succ, mul_comm (2 ^ k) 2, mul_assoc] at hy
      exact Nat.not_even_iff_odd.mpr hy (even_two_mul _)

theorem odd_two_pow_pow_sub_one {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) : Odd ((2 ^ m) ^ k - 1) := by
  have h : Even ((2 ^ m) ^ k) := by
    rw [← pow_mul]
    exact (Nat.even_pow' (Nat.mul_ne_zero (by omega) (by omega))).mpr even_two
  have h1 : 1 ≤ (2 ^ m) ^ k := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd h1 h odd_one

theorem IsFFLOrder.ne_sl2 {N : ℕ} (h : IsFFLOrder N) {m : ℕ} (hm : 1 ≤ m)
    (hN : N = 2 ^ m * ((2 ^ m) ^ 2 - 1)) : False := by
  have hodd := odd_two_pow_pow_sub_one hm (le_of_lt one_lt_two)
  rcases h with ⟨n, hn, rfl⟩ | rfl | rfl
  · have ho : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      (odd_two_pow_pow_sub_one hn (by norm_num)).mul (odd_two_pow_pow_sub_one hn (by norm_num))
    have hN' : 2 ^ m * ((2 ^ m) ^ 2 - 1) =
        2 ^ (3 * n) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [← hN, pow_mul', mul_assoc]
    obtain ⟨hmn, hodd'⟩ := two_pow_mul_odd_inj hodd ho hN'
    subst hmn
    set q := 2 ^ n with hq
    have hq2 : 2 ≤ q := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [pow_mul', ← hq] at hodd'
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e : ((q : ℤ) ^ 3) ^ 2 - 1 = ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 - 1) := by
      have := hodd'
      zify [h1, h2, h3] at this
      exact this
    have hq2' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq2
    have h5 : (32 : ℤ) ≤ (q : ℤ) ^ 5 := by
      calc (32 : ℤ) = 2 ^ 5 := by norm_num
        _ ≤ (q : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) hq2' 5
    have h6 : 2 * (q : ℤ) ^ 5 ≤ (q : ℤ) ^ 6 := by
      rw [show (q : ℤ) ^ 6 = q * q ^ 5 by ring]
      exact mul_le_mul_of_nonneg_right hq2' (by positivity)
    have h7 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
    have h8 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := by positivity
    have e' : (q : ℤ) ^ 6 + (q : ℤ) ^ 3 + (q : ℤ) ^ 2 = (q : ℤ) ^ 5 + 2 := by linear_combination e
    linarith
  · have h20160 : 20160 = 2 ^ 6 * 315 := by norm_num
    rw [h20160] at hN
    obtain ⟨rfl, h⟩ := two_pow_mul_odd_inj (by decide) hodd hN
    norm_num at h
  · have h9999360 : 9999360 = 2 ^ 10 * 9765 := by norm_num
    rw [h9999360] at hN
    obtain ⟨rfl, h⟩ := two_pow_mul_odd_inj (by decide) hodd hN
    norm_num at h

variable {V : Type} [CommGroup V]

theorem center_eq_bot {Γ L : Subgroup (MulAut V)} (hLΓ : L ≤ Γ)
    (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥) : Subgroup.center ↥L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hmem : (z : MulAut V) ∈ Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) := by
    refine ⟨hLΓ z.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have := Subgroup.mem_center_iff.mp hz ⟨l, hl⟩
    exact congrArg Subtype.val this
  rw [hC, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (Subtype.ext hmem)

theorem le_normalizer_of_normal {Γ L : Subgroup (MulAut V)} (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) : Γ ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  rw [Subgroup.normal_subgroupOf_iff hLΓ] at hn
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => hn l g hl hg, fun hl => ?_⟩
  have := hn _ g⁻¹ hl (Γ.inv_mem hg)
  simpa [mul_assoc] using this

theorem le_or_eq_bot {Γ L H : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L)
    (hZ : Subgroup.center ↥L = ⊥)
    (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥) (hHΓ : H ≤ Γ)
    (hLH : L ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hHL : H ≤ Subgroup.normalizer (L : Set (MulAut V))) : L ≤ H ∨ H = ⊥ := by
  have hN : (H.subgroupOf L).Normal := by
    constructor
    intro n hn l
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hLH l.2) n).mp hn
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (H.subgroupOf L) with
    h | h
  · right
    rw [hZ, le_bot_iff] at h
    rw [eq_bot_iff, ← hC]
    intro x hx
    refine ⟨hHΓ hx, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h1 : l * x * l⁻¹ * x⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hHL hx) l⁻¹).mp (L.inv_mem hl)
      rw [show l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) by group]
      exact L.mul_mem hl this
    have h2 : l * x * l⁻¹ * x⁻¹ ∈ H :=
      H.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLH hl) x).mp hx) (H.inv_mem hx)
    have h3 : (⟨_, h1⟩ : ↥L) ∈ H.subgroupOf L := h2
    rw [h, Subgroup.mem_bot] at h3
    have h4 : l * x * l⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
    calc l * x = l * x * l⁻¹ * x⁻¹ * (x * l) := by group
      _ = x * l := by rw [h4, one_mul]
  · left
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ H.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this

theorem nontrivial_of_isQuasisimple {X : Type*} [Group X] (h : CFSG.IsQuasisimple X) :
    Nontrivial X := by
  obtain ⟨x, y, hxy⟩ := G64.IsQuasisimple.exists_ne h
  refine ⟨⟨x * y, y * x, hxy⟩⟩

theorem ffJ_le (X : Subgroup (MulAut V)) : ffJ X ≤ X :=
  iSup₂_le fun _ hA => hA.1

theorem le_normalizer_ffJ (X : Subgroup (MulAut V)) :
    X ≤ Subgroup.normalizer (ffJ X : Set (MulAut V)) := by
  have key : ∀ g ∈ X, ∀ j ∈ ffJ X, g * j * g⁻¹ ∈ ffJ X := by
    intro g hg j hj
    have hle : (ffJ X).map (MulAut.conj g).toMonoidHom ≤ ffJ X := by
      unfold ffJ
      rw [Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hA => ?_
      rintro _ ⟨a, ha, rfl⟩
      refine B19.le_ffJ (B1.isFFStarOffender_conjAut hA hg) (B1.mem_conjAut.mpr ?_)
      simpa [MulAut.conj_apply, mul_assoc] using ha
    have := hle ⟨j, hj, rfl⟩
    simpa [MulAut.conj_apply] using this
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨key g hg j, fun h => ?_⟩
  have := key g⁻¹ (X.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem ffJ_ffJ (X : Subgroup (MulAut V)) : ffJ (ffJ X) = ffJ X := by
  refine le_antisymm (ffJ_le _) (iSup₂_le fun A hA => ?_)
  exact le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : IsFFStarOffender (ffJ X) B) => B)
    A ⟨B19.le_ffJ hA, hA.2⟩ le_rfl

theorem b53Hyp_ffJ [Finite V] {Γ L : Subgroup (MulAut V)} (hQ : G64.IsQuotientOfSQTKCat ↥Γ)
    (hq : CFSG.IsQuasisimple ↥L) (hZ : Subgroup.center ↥L = ⊥)
    (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥) (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) :
    L ≤ ffJ Γ ∧ B53Hyp (ffJ Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΓL := le_normalizer_of_normal hLΓ hn
  have hJΓ := ffJ_le Γ
  have hLJ : L ≤ ffJ Γ := by
    rcases le_or_eq_bot hq hZ hC hJΓ (hLΓ.trans (le_normalizer_ffJ Γ)) (hJΓ.trans hΓL) with
      h | h
    · exact h
    · exfalso
      obtain ⟨A, hA⟩ := hoff
      exact hA.2.1 (le_bot_iff.mp (h ▸ B19.le_ffJ hA))
  refine ⟨hLJ, ?_, (ffJ_ffJ Γ).symm, ?_⟩
  · have hP := pCoreOf_le 2 (ffJ Γ)
    rcases le_or_eq_bot hq hZ hC (hP.trans hJΓ) (hLJ.trans (le_normalizer_pCoreOf 2 _))
      ((hP.trans hJΓ).trans hΓL) with h | h
    · exfalso
      have hL2 : IsPGroup 2 ↥L := (pCoreOf_isPGroup 2 (ffJ Γ)).to_le h
      have : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
      have hc := hL2.center_nontrivial
      rw [hZ] at hc
      exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl
    · exact h
  · obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := G64.isQuotientOfSQTKCat_of_le hJΓ hQ
    exact ⟨Y, inferInstance, inferInstance, N, inferInstance, G64.sqtkGroup_of_isSQTKCat hY, ⟨e⟩⟩

theorem nontrivial_statedSL {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] :
    Nontrivial ↥(StatedSL n K) := by
  refine ⟨⟨slT (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) (1 : K), 1,
    fun h => ?_⟩⟩
  have := congrArg (fun g => slMat g ⟨0, by omega⟩ ⟨1, by omega⟩) h
  simp [slMat_slT, slMat_one, Matrix.transvection] at this

theorem ne_bot_of_mulEquiv {X : Type*} [Group X] [Nontrivial X] {H : Subgroup (MulAut V)}
    (e : ↥H ≃* X) : H ≠ ⊥ := by
  intro h
  subst h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact hxy (e.symm.injective (Subsingleton.elim _ _))

theorem ne_bot_of_factorList {H : Subgroup (MulAut V)} (h : B56FactorList ↥H) : H ≠ ⊥ := by
  rcases h with ⟨n, K, _, _, -, -, ⟨e⟩⟩ | h | ⟨m, K, _, _, -, -, -, ⟨e⟩⟩
  · have := nontrivial_statedSL le_rfl K
    exact ne_bot_of_mulEquiv e
  · obtain ⟨e⟩ := h
    exact ne_bot_of_mulEquiv e
  · have := nontrivial_statedSL (n := 3) (by norm_num) K
    exact ne_bot_of_mulEquiv e

theorem sup_le_normalizer {G₁ G₂ : Subgroup (MulAut V)}
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    G₁ ⊔ G₂ ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← hc a ha b hb, mul_inv_cancel_right]
    exact ha
  · intro ha
    have h1 : b * a * b⁻¹ * b = b * (b * a * b⁻¹) := hc _ ha b hb
    rw [inv_mul_cancel_right] at h1
    rw [mul_left_cancel h1]
    exact ha

theorem false_of_case2 [Finite V] {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hL : 6 < Nat.card L) (h : B56Case2 G) : False := by
  obtain ⟨⟨e⟩, -, -⟩ := h
  have h6 : Nat.card G = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have := Subgroup.card_le_of_le hLG
  omega

theorem false_of_case3 {G L : Subgroup (MulAut V)} (hL : L ≠ ⊥)
    (hdich : ∀ H ≤ G, G ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ H = ⊥)
    (h : B56Case3 G) : False := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, h₁, h₂, -⟩ := h
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hn₁ : G ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
    hsup.symm.le.trans (sup_le_normalizer hcomm)
  have hn₂ : G ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
    hsup.symm.le.trans ((sup_comm G₁ G₂).le.trans (sup_le_normalizer hcomm'))
  rcases hdich G₁ (le_sup_left.trans hsup.le) hn₁ with hL₁ | hb₁
  · rcases hdich G₂ (le_sup_right.trans hsup.le) hn₂ with hL₂ | hb₂
    · exact hL (le_bot_iff.mp (hinf ▸ le_inf hL₁ hL₂))
    · exact ne_bot_of_factorList h₂ hb₂
  · exact ne_bot_of_factorList h₁ hb₁

theorem false_of_case4 [Finite V] {G L : Subgroup (MulAut V)} (hL : 6 < Nat.card L)
    (hdich : ∀ H ≤ G, G ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ H = ⊥)
    (h : B56Case4 G) : False := by
  obtain ⟨G₁, G₂, t, hG, -, hcomm, -, hc3, -, -, -, -, -, -, ht₂, -, -⟩ := h
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hG₂ : G₂ ≤ G := (le_sup_right.trans le_sup_left).trans hG.symm.le
  have hn : G ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
    rw [hG]
    refine sup_le (sup_le (le_sup_right.trans (sup_le_normalizer hcomm'))
      Subgroup.le_normalizer) ?_
    rw [Subgroup.zpowers_le]
    exact ht₂
  rcases hdich G₂ hG₂ hn with hL₂ | hb
  · have := Subgroup.card_le_of_le hL₂
    omega
  · rw [hb, Subgroup.card_bot] at hc3
    omega

theorem false_of_case5 {G L : Subgroup (MulAut V)} (hL : L ≠ ⊥)
    (hdich : ∀ H ≤ G, G ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ H = ⊥)
    (h : B56Case5 G) : False := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e₁⟩, -, -, h₂⟩ := h
  have hb₁ : G₁ ≠ ⊥ := by
    have := nontrivial_statedSL (n := 3) (by norm_num) (ZMod 2)
    exact ne_bot_of_mulEquiv e₁
  have hb₂ : G₂ ≠ ⊥ := by
    rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, _, _, -, π, hπ⟩
    · have := nontrivial_statedSL (n := 3) (by norm_num) (ZMod 2)
      exact ne_bot_of_mulEquiv e₂
    · have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
      have := nontrivial_statedSL le_rfl K
      intro hb
      subst hb
      obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(StatedSL 2 K)
      exact hxy (hinj (Subsingleton.elim _ _))
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hn₁ : G ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
    hsup.symm.le.trans (sup_le_normalizer hcomm)
  have hn₂ : G ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
    hsup.symm.le.trans ((sup_comm G₁ G₂).le.trans (sup_le_normalizer hcomm'))
  rcases hdich G₁ (le_sup_left.trans hsup.le) hn₁ with hL₁ | h
  · rcases hdich G₂ (le_sup_right.trans hsup.le) hn₂ with hL₂ | h
    · exact hL (le_bot_iff.mp (hinf ▸ le_inf hL₁ hL₂))
    · exact hb₂ h
  · exact hb₁ h

theorem eq_of_isQuasisimple {L F : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L)
    (hqF : CFSG.IsQuasisimple ↥F) (hLF : L ≤ F)
    (hFL : F ≤ Subgroup.normalizer (L : Set (MulAut V))) : F = L := by
  have hN : (L.subgroupOf F).Normal := by
    constructor
    intro n hn f
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hFL f.2) n).mp hn
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqF (L.subgroupOf F) with
    h | h
  · exfalso
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := G64.IsQuasisimple.exists_ne hq
    apply hxy
    have hxc : (⟨x, hLF hx⟩ : ↥F) ∈ Subgroup.center ↥F :=
      h (show (⟨x, hLF hx⟩ : ↥F) ∈ L.subgroupOf F from hx)
    have := Subgroup.mem_center_iff.mp hxc ⟨y, hLF hy⟩
    exact Subtype.ext (congrArg Subtype.val this).symm
  · refine le_antisymm (fun f hf => ?_) hLF
    have : (⟨f, hf⟩ : ↥F) ∈ L.subgroupOf F := h ▸ Subgroup.mem_top _
    exact this

end CFSG.Quasithin.EmptyFaithfulMultiple.FFL
