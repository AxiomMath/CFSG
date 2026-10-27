module

public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Quasithin.Vol2.Ch12Sec6L26p
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.Quasithin.H13

namespace L211L

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Matrix
open scoped MatrixGroups

section Model

local instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

abbrev P : Type := PSL2 (ZMod 11)

theorem hK11 : IsOddPrimePower (Nat.card (ZMod 11)) :=
  ⟨11, 1, by norm_num, by decide, le_rfl, by simp⟩

theorem card_P : Nat.card P = 660 := by
  rw [psl2_card_formula (ZMod 11) hK11]
  simp

abbrev mkP (A : SL(2, ZMod 11)) : P := QuotientGroup.mk A

theorem mkP_neg_one : mkP (-1) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (by simp)

theorem mkP_ne_one {A : SL(2, ZMod 11)}
    (h : (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 1 ≠ 0 ∨
      (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 0 ≠ (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 1) :
    mkP A ≠ 1 := by
  intro h1
  rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h1
  obtain ⟨r, -, hr⟩ := h1
  rcases h with h | h
  · apply h
    rw [← hr]
    simp
  · apply h
    rw [← hr]
    simp

def sx : SL(2, ZMod 11) := ⟨!![0, 10; 1, 10], by rw [Matrix.det_fin_two_of]; decide⟩
def sj0 : SL(2, ZMod 11) := ⟨!![1, 4; 5, 10], by rw [Matrix.det_fin_two_of]; decide⟩
def sy : SL(2, ZMod 11) := ⟨!![3, 0; 0, 4], by rw [Matrix.det_fin_two_of]; decide⟩
def sj1 : SL(2, ZMod 11) := ⟨!![0, 1; 10, 0], by rw [Matrix.det_fin_two_of]; decide⟩
def sc : SL(2, ZMod 11) := ⟨!![2, 2; 3, 9], by rw [Matrix.det_fin_two_of]; decide⟩

theorem sx_cube : sx ^ 3 = 1 := Subtype.ext (by decide)
theorem sj0_sq : sj0 * sj0 = -1 := Subtype.ext (by decide)
theorem sj0_sx : sj0 * sx = sx * sx * sj0 := Subtype.ext (by decide)
theorem sy_five : sy ^ 5 = 1 := Subtype.ext (by decide)
theorem sj1_sq : sj1 * sj1 = -1 := Subtype.ext (by decide)
theorem sj1_sy : sj1 * sy = sy ^ 4 * sj1 := Subtype.ext (by decide)
theorem sc_sq : sc * sc = -1 := Subtype.ext (by decide)
theorem sab_cube : (sj1 * sj0) ^ 3 = -1 := Subtype.ext (by decide)
theorem sbc_five : (sj0 * sc) ^ 5 = -1 := Subtype.ext (by decide)
theorem sabc_eleven : (sj1 * sj0 * sc) ^ 11 = 1 := Subtype.ext (by decide)

theorem mkP_pow (A : SL(2, ZMod 11)) (n : ℕ) : mkP A ^ n = mkP (A ^ n) :=
  (map_pow (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 11)))) A n).symm

theorem x0_cube : mkP sx ^ 3 = 1 := by rw [mkP_pow, sx_cube]; rfl
theorem x0_ne : mkP sx ≠ 1 := mkP_ne_one (Or.inl (by decide))
theorem j0_sq : mkP sj0 ^ 2 = 1 := by
  rw [sq, ← QuotientGroup.mk_mul, sj0_sq]
  exact mkP_neg_one
theorem j0_ne : mkP sj0 ≠ 1 := mkP_ne_one (Or.inl (by decide))
theorem j0_inv : mkP sj0 * mkP sx * (mkP sj0)⁻¹ = (mkP sx)⁻¹ := by
  have h1 : mkP sj0 * mkP sx = mkP sx * mkP sx * mkP sj0 := by
    rw [← QuotientGroup.mk_mul, sj0_sx]; rfl
  have h3 : mkP sx * mkP sx * mkP sx = 1 := by rw [← sq, ← pow_succ, x0_cube]
  rw [h1, mul_inv_cancel_right, eq_inv_iff_mul_eq_one, h3]
theorem y0_five : mkP sy ^ 5 = 1 := by rw [mkP_pow, sy_five]; rfl
theorem y0_ne : mkP sy ≠ 1 := mkP_ne_one (Or.inr (by decide))
theorem j1_sq : mkP sj1 ^ 2 = 1 := by
  rw [sq, ← QuotientGroup.mk_mul, sj1_sq]
  exact mkP_neg_one
theorem j1_ne : mkP sj1 ≠ 1 := mkP_ne_one (Or.inl (by decide))
theorem j1_inv : mkP sj1 * mkP sy * (mkP sj1)⁻¹ = (mkP sy)⁻¹ := by
  have h1 : mkP sj1 * mkP sy = mkP sy ^ 4 * mkP sj1 := by
    rw [mkP_pow, ← QuotientGroup.mk_mul, sj1_sy]; rfl
  have h5 : mkP sy ^ 4 * mkP sy = 1 := by rw [← pow_succ, y0_five]
  rw [h1, mul_inv_cancel_right, eq_inv_iff_mul_eq_one, h5]
theorem c_sq : mkP sc ^ 2 = 1 := by
  rw [sq, ← QuotientGroup.mk_mul, sc_sq]
  exact mkP_neg_one
theorem c_ne : mkP sc ≠ 1 := mkP_ne_one (Or.inl (by decide))
theorem ab_ord : orderOf (mkP sj1 * mkP sj0) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_mul, mkP_pow, sab_cube]
    exact mkP_neg_one
  · rw [← QuotientGroup.mk_mul]; exact mkP_ne_one (Or.inl (by decide))
theorem bc_ord : orderOf (mkP sj0 * mkP sc) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_mul, mkP_pow, sbc_five]
    exact mkP_neg_one
  · rw [← QuotientGroup.mk_mul]; exact mkP_ne_one (Or.inl (by decide))
theorem abc_ord : orderOf (mkP sj1 * mkP sj0 * mkP sc) = 11 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mkP_pow, sabc_eleven]; rfl
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]; exact mkP_ne_one (Or.inl (by decide))

end Model

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem fz3 : (660 : ℕ).factorization 3 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  rw [show (660 : ℕ) = 3 ^ 1 * 220 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem fz5 : (660 : ℕ).factorization 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num : Nat.Prime 5)]
  rw [show (660 : ℕ) = 5 ^ 1 * 132 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_pow {r : ℕ} [Fact r.Prime] (hr : (Nat.card X).factorization r = 1)
    {x x₀ : X} (hx : orderOf x = r) (hx₀ : orderOf x₀ = r) :
    ∃ g : X, ∃ n : ℤ, x = g * x₀ ^ n * g⁻¹ := by
  let S : Sylow r X := Sylow.ofCard (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx, hr, pow_one])
  let S₀ : Sylow r X :=
    Sylow.ofCard (Subgroup.zpowers x₀) (by rw [Nat.card_zpowers, hx₀, hr, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ S
  have hxS : x ∈ (S : Subgroup X) := Subgroup.mem_zpowers x
  rw [← hg, Sylow.coe_subgroup_smul] at hxS
  obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hxS
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨g, n, by simp [MulAut.smul_def, MulAut.conj_apply]⟩

end Abstract

section Clauses

local instance fact11' : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem isInv {k : P} (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) :
    CFSG.BenderSuzuki.PFAppendixIII.IsInvolution k := ⟨hk1, hk2⟩

theorem conj_inv {k t : P} (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ g : P, g * k * g⁻¹ = t :=
  psl2_involutions_conjugate_of_odd_prime_power (ZMod 11) hK11 k t (isInv hk2 hk1) (isInv ht2 ht1)

theorem conj_inverts {j x : P} (hj : j * x * j⁻¹ = x⁻¹) (g : P) (n : ℤ) :
    (g * j * g⁻¹) * (g * x ^ n * g⁻¹) * (g * j * g⁻¹)⁻¹ = (g * x ^ n * g⁻¹)⁻¹ := by
  have h1 : j * x ^ n * j⁻¹ = (x ^ n)⁻¹ := by
    rw [← conj_zpow, hj, _root_.inv_zpow]
  calc (g * j * g⁻¹) * (g * x ^ n * g⁻¹) * (g * j * g⁻¹)⁻¹ = g * (j * x ^ n * j⁻¹) * g⁻¹ := by
        group
    _ = (g * x ^ n * g⁻¹)⁻¹ := by rw [h1]; group

theorem clause3 : ∀ k x : P, k ^ 2 = 1 → k ≠ 1 → (orderOf x = 3 ∨ orderOf x = 5) →
    ∃ g : P, (g * k * g⁻¹) * x * (g * k * g⁻¹)⁻¹ = x⁻¹ := by
  intro k x hk2 hk1 hx
  obtain ⟨t, ht2, ht1, htx⟩ : ∃ t : P, t ^ 2 = 1 ∧ t ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
    rcases hx with hx | hx
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hx0 : orderOf (mkP sx) = 3 := orderOf_eq_prime x0_cube x0_ne
      obtain ⟨g, n, rfl⟩ := exists_conj_pow (by rw [card_P]; exact fz3) hx hx0
      refine ⟨g * mkP sj0 * g⁻¹, ?_, ?_, conj_inverts j0_inv g n⟩
      · rw [conj_pow, j0_sq]; group
      · intro h
        apply j0_ne
        calc mkP sj0 = g⁻¹ * (g * mkP sj0 * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hy0 : orderOf (mkP sy) = 5 := orderOf_eq_prime y0_five y0_ne
      obtain ⟨g, n, rfl⟩ := exists_conj_pow (by rw [card_P]; exact fz5) hx hy0
      refine ⟨g * mkP sj1 * g⁻¹, ?_, ?_, conj_inverts j1_inv g n⟩
      · rw [conj_pow, j1_sq]; group
      · intro h
        apply j1_ne
        calc mkP sj1 = g⁻¹ * (g * mkP sj1 * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
  obtain ⟨g, hg⟩ := conj_inv hk2 hk1 ht2 ht1
  exact ⟨g, by rw [hg]; exact htx⟩

theorem closure_abc (hs : IsSimpleGroup P) :
    Subgroup.closure {mkP sj1, mkP sj0, mkP sc} = ⊤ := by
  set S := Subgroup.closure ({mkP sj1, mkP sj0, mkP sc} : Set P) with hS
  have ha : mkP sj1 ∈ S := Subgroup.subset_closure (by simp)
  have hb : mkP sj0 ∈ S := Subgroup.subset_closure (by simp)
  have hc : mkP sc ∈ S := Subgroup.subset_closure (by simp)
  have hdvd : ∀ y ∈ S, orderOf y ∣ Nat.card S := fun y hy => Subgroup.orderOf_dvd_natCard S hy
  have h2 : 2 ∣ Nat.card S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ho := orderOf_eq_prime j1_sq j1_ne
    have hd := hdvd _ ha
    rwa [ho] at hd
  have h3 : 3 ∣ Nat.card S := by
    have hd := hdvd _ (S.mul_mem ha hb)
    rwa [ab_ord] at hd
  have h5 : 5 ∣ Nat.card S := by
    have hd := hdvd _ (S.mul_mem hb hc)
    rwa [bc_ord] at hd
  have h11 : 11 ∣ Nat.card S := by
    have hd := hdvd _ (S.mul_mem (S.mul_mem ha hb) hc)
    rwa [abc_ord] at hd
  have h330 : 330 ∣ Nat.card S := by
    have h6 : 6 ∣ Nat.card S := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    have h30 : 30 ∣ Nat.card S := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h30 h11
  have hci : Nat.card S * S.index = 660 := S.card_mul_index.trans card_P
  obtain ⟨m, hm⟩ := h330
  have hmi : m * S.index = 2 := by
    rw [hm, mul_assoc] at hci
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 330) (hci.trans (by norm_num))
  have hidx : S.index = 1 ∨ S.index = 2 := by
    have h1 : S.index ∣ 2 := Dvd.intro_left m hmi
    exact (Nat.dvd_prime Nat.prime_two).mp h1
  rcases hidx with h | h
  · exact Subgroup.index_eq_one.mp h
  · have : S.Normal := Subgroup.normal_of_index_eq_two h
    have := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h' | h'
    · exfalso
      rw [h', Subgroup.mem_bot] at ha
      exact j1_ne ha
    · exact h'

theorem clause4 (hs : IsSimpleGroup P) : ∀ k : P, k ^ 2 = 1 → k ≠ 1 → ∃ g h : P,
    Subgroup.closure {k, g * k * g⁻¹, h * k * h⁻¹} = ⊤ := by
  intro k hk2 hk1
  obtain ⟨u, hu⟩ := conj_inv j1_sq j1_ne hk2 hk1
  obtain ⟨v₁, hv₁⟩ := conj_inv j1_sq j1_ne j0_sq j0_ne
  obtain ⟨v₂, hv₂⟩ := conj_inv j1_sq j1_ne c_sq c_ne
  refine ⟨u * v₁ * u⁻¹, u * v₂ * u⁻¹, ?_⟩
  have e1 : (u * v₁ * u⁻¹) * k * (u * v₁ * u⁻¹)⁻¹ = u * mkP sj0 * u⁻¹ := by
    rw [← hu, ← hv₁]; group
  have e2 : (u * v₂ * u⁻¹) * k * (u * v₂ * u⁻¹)⁻¹ = u * mkP sc * u⁻¹ := by
    rw [← hu, ← hv₂]; group
  rw [e1, e2, ← hu]
  have hmap : Subgroup.closure ({u * mkP sj1 * u⁻¹, u * mkP sj0 * u⁻¹, u * mkP sc * u⁻¹} : Set P) =
      (Subgroup.closure ({mkP sj1, mkP sj0, mkP sc} : Set P)).map (MulAut.conj u).toMonoidHom := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, MulAut.conj_apply]
  rw [hmap, closure_abc hs, Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)]

theorem normalizer_zpowers {k x : P} (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) (hx : orderOf x = 3)
    (hxk : x * k = k * x) :
    Subgroup.normalizer (Subgroup.zpowers x : Set P) = Subgroup.centralizer {k} := by
  refine psl2_odd_centralizer_normalizer hK11 (isInv hk2 hk1) _ ?_ ?_ ?_
  · intro h
    have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · intro y hy
    have h1 : orderOf y ∣ 3 := by
      rw [← hx]
      exact orderOf_dvd_of_mem_zpowers hy
    exact Odd.of_dvd_nat (by decide) h1
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hxk

theorem clause5 : ∀ k x : P, k ^ 2 = 1 → k ≠ 1 → orderOf x = 3 → x * k = k * x →
    ∀ Y : Subgroup P, IsPGroup 2 Y → Y ≤ Subgroup.centralizer {k} →
      x ∈ Subgroup.normalizer (Y : Set P) → Y ≤ Subgroup.centralizer {x} := by
  intro k x hk2 hk1 hx hxk Y hY2 hYk hxY y hy
  have hN := normalizer_zpowers hk2 hk1 hx hxk
  have hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set P) := hN ▸ hYk hy
  have h1 : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hyN x).mp (Subgroup.mem_zpowers x))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have h2 : y * x * y⁻¹ * x⁻¹ ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp hxY y⁻¹).mp (Y.inv_mem hy)
    have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
    rw [e]
    exact Y.mul_mem hy this
  obtain ⟨n, hn⟩ := hY2 ⟨_, h2⟩
  have h3 : (y * x * y⁻¹ * x⁻¹) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
  have h4 : (y * x * y⁻¹ * x⁻¹) ^ 3 = 1 := by
    rw [← hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hx,
      pow_orderOf_eq_one, _root_.one_zpow]
  have h5 : y * x * y⁻¹ * x⁻¹ = 1 := S126L26.eq_one_of_two_three' h3 h4
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * x = y * x * y⁻¹ * x⁻¹ * x * y := by group
    _ = x * y := by rw [h5]; group

theorem clause6 : ∀ k x y : P, k ^ 2 = 1 → k ≠ 1 → orderOf x = 3 → orderOf y = 3 →
    x * k = k * x → y * k = k * y → y ∈ Subgroup.zpowers x := by
  intro k x y hk2 hk1 hx hy hxk hyk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := normalizer_zpowers hk2 hk1 hx hxk
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set P) := by
    rw [Subgroup.zpowers_le, hN, Subgroup.mem_centralizer_singleton_iff]
    exact hyk
  have hpx : IsPGroup 3 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hpy : IsPGroup 3 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hsup := IsPGroup.to_sup_of_normal_right' hpy hpx hyN
  have hle := S126C.card_le_three_of_isPGroup card_P hsup
  have heq : Subgroup.zpowers x = Subgroup.zpowers y ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, hx]; exact hle)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

end Clauses

section Aut

local instance fact11'' : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem ringEquiv_eq_one (σ : ZMod 11 ≃+* ZMod 11) : σ = 1 := by
  have h := RingHom.ext_zmod σ.toRingHom (RingHom.id (ZMod 11))
  ext x
  exact congrArg (fun f : ZMod 11 →+* ZMod 11 => f x) h

theorem exists_pgl (α : MulAut P) : ∃ g : PGL2 (ZMod 11), pglAction (ZMod 11) g = α := by
  obtain ⟨γ, hγ⟩ := semilinearAction_surjective (ZMod 11) α
  refine ⟨γ.left, ?_⟩
  rw [← hγ]
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ]
  rw [map_mul, semilinearAction_inl, semilinearAction_inr, ringEquiv_eq_one γ.right, map_one,
    mul_one]

theorem pglAction_injective : Function.Injective (pglAction (ZMod 11)) :=
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective (ZMod 11)

abbrev H₂ : Subgroup (PGL2 (ZMod 11)) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod 11)).range

theorem inner_of_mem {g : PGL2 (ZMod 11)} (hg : g ∈ H₂) :
    pglAction (ZMod 11) g ∈ (MulAut.conj : P →* MulAut P).range := by
  obtain ⟨y, rfl⟩ := hg
  exact ⟨y, (pglAction_toPGL (ZMod 11) y).symm⟩

theorem clause1 : ∀ α : MulAut P, Odd (orderOf α) → α ∈ (MulAut.conj : P →* MulAut P).range := by
  intro α hα
  obtain ⟨g, rfl⟩ := exists_pgl α
  rw [orderOf_injective _ pglAction_injective g] at hα
  by_cases hg : g ∈ H₂
  · exact inner_of_mem hg
  · exfalso
    apply hg
    obtain ⟨m, hm⟩ := hα
    have h1 : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
    have h2 : g = (g ^ (m + 1)) ^ 2 := by
      rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by ring, pow_succ, h1, one_mul]
    rw [h2]
    exact Subgroup.sq_mem_of_index_two (pgl2_psl2Range_index_eq_two (ZMod 11) hK11) _

end Aut

section Outer

local instance fact11c : Fact (Nat.Prime 11) := ⟨by norm_num⟩

def dGL : GL (Fin 2) (ZMod 11) := ⟨!![1, 0; 0, 10], !![1, 0; 0, 10], by decide, by decide⟩

abbrev g0 : PGL2 (ZMod 11) := Matrix.ProjGenLinGroup.mk dGL

theorem dGL_sq : dGL * dGL = 1 := Units.ext (by decide)

theorem g0_sq : g0 ^ 2 = 1 := by
  rw [sq, ← map_mul, dGL_sq, map_one]

theorem g0_ne : g0 ≠ 1 := by
  intro h
  rw [← map_one Matrix.ProjGenLinGroup.mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h00 := congrArg
    (fun A : GL (Fin 2) (ZMod 11) => (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 0) hu
  have h11 := congrArg
    (fun A : GL (Fin 2) (ZMod 11) => (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 1) hu
  simp [dGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  rw [h00] at h11
  exact absurd h11 (by decide)

theorem g0_not_mem : g0 ∉ H₂ := by
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
  rintro ⟨r, hr⟩
  have hdet : ((Matrix.GeneralLinearGroup.det dGL : (ZMod 11)ˣ) : ZMod 11) = 10 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show Matrix.det !![(1 : ZMod 11), 0; 0, 10] = 10
    rw [Matrix.det_fin_two_of]
    decide
  rw [hdet] at hr
  revert r
  decide

theorem diag_cube : ∀ a d : ZMod 11, a * d = 1 →
    (!![a, 0; 0, d] ^ 3 = (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) ∨
      !![a, 0; 0, d] ^ 3 = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 11))) →
    (a = 1 ∧ d = 1) ∨ (a = 10 ∧ d = 10) := by decide

theorem anti_sq : ∀ b c : ZMod 11, 0 * 0 - b * c = 1 →
    !![0, b; c, 0] ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by decide

theorem eq_zero_L1 : ∀ b u : ZMod 11, u = 1 → b * 10 * u = b → b = 0 := by decide

theorem eq_zero_L2 : ∀ c u : ZMod 11, u = 1 → 10 * c * u = c → c = 0 := by decide

theorem eq_zero_L3 : ∀ a u : ZMod 11, u ≠ 1 → a * u = a → a = 0 := by decide

theorem eq_zero_L4 : ∀ d u : ZMod 11, u ≠ 1 → 10 * d * 10 * u = d → d = 0 := by decide

theorem sq_eq_one : ∀ r : ZMod 11, r ^ 2 = 1 → r = 1 ∨ r = 10 := by decide

end Outer

section NoFix

local instance fact11d : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem scalar_fin_two (r : ZMod 11) :
    Matrix.scalar (Fin 2) r = !![r, 0; 0, r] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mem_center_of_val {A : SL(2, ZMod 11)}
    (h : (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) = 1 ∨
      (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) = -1) :
    A ∈ Subgroup.center (SL(2, ZMod 11)) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rcases h with h | h
  · exact ⟨1, by simp, by rw [h]; simp⟩
  · refine ⟨-1, by decide, ?_⟩
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> decide

theorem g0_no_fix (x : P) (hx : orderOf x = 3) : pglAction (ZMod 11) g0 x ≠ x := by
  intro hfix
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  have hx3 : mkP A ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  have hx1 : mkP A ≠ 1 := fun h => by
    rw [show (QuotientGroup.mk A : P) = mkP A from rfl, h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  set a := (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 1 with hd
  have hA : (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdet : a * d - b * c = 1 := by
    have := A.2
    rw [hA, Matrix.det_fin_two_of] at this
    exact this
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hfix
  rw [toPGL_pglAction, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] at h1
  have h2 : Matrix.ProjGenLinGroup.mk (dGL * Matrix.SpecialLinearGroup.toGL A * dGL⁻¹) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) := by
    rw [map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h2
  have hmat := congrArg (fun B : GL (Fin 2) (ZMod 11) => (B : Matrix (Fin 2) (Fin 2) (ZMod 11))) hu
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA, scalar_fin_two] at hmat
  have hinv : ((dGL⁻¹ : GL (Fin 2) (ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
      !![1, 0; 0, 10] := rfl
  have hval : ((dGL : GL (Fin 2) (ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) =
      !![1, 0; 0, 10] := rfl
  rw [hinv, hval] at hmat
  simp only [Matrix.mul_fin_two] at hmat
  have e00 := congrFun (congrFun hmat 0) 0
  have e01 := congrFun (congrFun hmat 0) 1
  have e10 := congrFun (congrFun hmat 1) 0
  have e11 := congrFun (congrFun hmat 1) 1
  simp at e00 e01 e10 e11
  have hpow1 : ∀ n : ℕ, (!![a, b; c, d] ^ n = (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) ∨
      !![a, b; c, d] ^ n = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 11))) → mkP A ^ n = 1 := by
    intro n hn
    rw [mkP_pow, QuotientGroup.eq_one_iff]
    apply mem_center_of_val
    rw [Matrix.SpecialLinearGroup.coe_pow, hA]
    exact hn
  have hcube : !![a, b; c, d] ^ 3 = (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) ∨
      !![a, b; c, d] ^ 3 = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
    have h3 := hx3
    rw [mkP_pow, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h3
    obtain ⟨r, hr2, hr⟩ := h3
    have hr' : (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) ^ 3 = Matrix.scalar (Fin 2) r := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr]
    rw [hA] at hr'
    rw [Fintype.card_fin] at hr2
    rcases sq_eq_one r hr2 with rfl | rfl
    · left; rw [hr']; simp
    · right; rw [hr', scalar_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> decide
  by_cases hu1 : (u : ZMod 11) = 1
  · have hb0 := eq_zero_L1 b u hu1 e01
    have hc0 := eq_zero_L2 c u hu1 e10
    rw [hb0, hc0] at hcube hdet
    have had : a * d = 1 := by linear_combination hdet
    rcases diag_cube a d had hcube with ⟨ha1, hd1⟩ | ⟨ha1, hd1⟩
    · apply hx1
      have := hpow1 1 (Or.inl (by rw [ha1, hb0, hc0, hd1]; decide))
      simpa using this
    · apply hx1
      have := hpow1 1 (Or.inr (by rw [ha1, hb0, hc0, hd1]; decide))
      simpa using this
  · have ha0 := eq_zero_L3 a u hu1 e00
    have hd0 := eq_zero_L4 d u hu1 e11
    rw [ha0, hd0] at hdet
    have hsq := anti_sq b c hdet
    have h2 : mkP A ^ 2 = 1 := hpow1 2 (Or.inr (by rw [ha0, hd0]; exact hsq))
    have h3 : orderOf (mkP A) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf (mkP A) = 3 := hx
    rw [h4] at h3
    exact absurd h3 (by norm_num)


end NoFix

section Clause2

local instance fact11e : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem clause2 : ∀ α : MulAut P, α ^ 2 = 1 → (∃ x : P, orderOf x = 3 ∧ α x = x) →
    α ∈ (MulAut.conj : P →* MulAut P).range := by
  rintro α hα2 ⟨x, hx, hαx⟩
  obtain ⟨g, rfl⟩ := exists_pgl α
  by_cases hg : g ∈ H₂
  · exact inner_of_mem hg
  · exfalso
    have hg2 : g ^ 2 = 1 := pglAction_injective (by rw [map_pow, hα2, map_one])
    have hg1 : g ≠ 1 := fun h => hg (h ▸ H₂.one_mem)
    have h3 : 3 < Nat.card (ZMod 11) := by simp
    have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three (ZMod 11) hK11 h3
    obtain ⟨c, hc⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate (ZMod 11) hK11 h3
      ⟨hg1, hg2⟩ ⟨g0_ne, g0_sq⟩ (by rw [hcomm]; exact hg) (by rw [hcomm]; exact g0_not_mem))
    apply g0_no_fix (pglAction (ZMod 11) c x) (by rw [MulEquiv.orderOf_eq]; exact hx)
    rw [← hc, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.inv_apply_self, hαx]

end Clause2

section Fact

local instance fact11f : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem nonempty_equiv {X : Type} [Group X] (hX : IsPSL 2 11 1 X) : Nonempty (X ≃* P) := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 11) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod 11 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e₀.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)))⟩

end Fact

end L211L

open L211L in
theorem factL211Loc12626_holds : FactL211Loc12626 := by
  intro X _ _ hX
  obtain ⟨e⟩ := nonempty_equiv hX
  have hcard : Nat.card X = 660 := (Nat.card_congr e.toEquiv).trans card_P
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 11 1 hX).2
  have hsP : IsSimpleGroup P := by
    have := hs
    exact e.symm.isSimpleGroup
  have hcongr : ∀ y : P, MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y := by
    intro y
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hinner : ∀ α : MulAut X, MulAut.congr e α ∈ (MulAut.conj : P →* MulAut P).range →
      α ∈ (MulAut.conj : X →* MulAut X).range := by
    rintro α ⟨y, hy⟩
    refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
    rw [hcongr, hy]
  have hord : ∀ x : X, orderOf (e x) = orderOf x := fun x => MulEquiv.orderOf_eq e x
  have he1 : ∀ x : X, e x = 1 ↔ x = 1 := fun x => by
    rw [← map_one e, e.injective.eq_iff]
  have hesq : ∀ k : X, k ^ 2 = 1 → (e k) ^ 2 = 1 := fun k hk => by rw [← map_pow, hk, map_one]
  refine ⟨⟨hcard, hs⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro α hα
    apply hinner
    apply clause1
    rw [MulEquiv.orderOf_eq]
    exact hα
  ·
    rintro α hα2 ⟨x, hx, hαx⟩
    apply hinner
    refine clause2 _ (by rw [← map_pow, hα2, map_one]) ⟨e x, by rw [hord]; exact hx, ?_⟩
    simp [MulAut.congr_apply, hαx]
  ·
    intro k x hk2 hk1 hx
    obtain ⟨g, hg⟩ := clause3 (e k) (e x) (hesq k hk2) (fun h => hk1 ((he1 k).mp h))
      (by rw [hord]; exact hx)
    refine ⟨e.symm g, e.injective ?_⟩
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  ·
    intro k hk2 hk1
    obtain ⟨g, h, hgh⟩ := clause4 hsP (e k) (hesq k hk2) (fun h => hk1 ((he1 k).mp h))
    refine ⟨e.symm g, e.symm h, ?_⟩
    have hmap : (Subgroup.closure ({k, e.symm g * k * (e.symm g)⁻¹, e.symm h * k * (e.symm h)⁻¹} :
        Set X)).map e.toMonoidHom = ⊤ := by
      rw [MonoidHom.map_closure, ← hgh]
      congr 1
      simp [Set.image_insert_eq]
    rw [eq_top_iff]
    intro z _
    have : e z ∈ (Subgroup.closure ({k, e.symm g * k * (e.symm g)⁻¹,
        e.symm h * k * (e.symm h)⁻¹} : Set X)).map e.toMonoidHom := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwe⟩ := this
    rwa [show w = z from e.injective hwe] at hw
  ·
    intro k x hk2 hk1 hx hxk Y hY2 hYk hxY y hy
    have hY2' : IsPGroup 2 ↥(Y.map e.toMonoidHom) := hY2.map e.toMonoidHom
    have hYk' : Y.map e.toMonoidHom ≤ Subgroup.centralizer {e k} := by
      rintro _ ⟨z, hz, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp (hYk hz)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change e z * e k = e k * e z
      rw [← map_mul, ← map_mul, this]
    have hxY' : e x ∈ Subgroup.normalizer ((Y.map e.toMonoidHom : Subgroup P) : Set P) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      obtain ⟨z, rfl⟩ := e.surjective w
      have h1 := Subgroup.mem_normalizer_iff.mp hxY z
      constructor
      · rintro ⟨z', hz', hz'e⟩
        have hzz : z' = z := e.injective hz'e
        subst hzz
        exact ⟨_, h1.mp hz', by simp⟩
      · rintro ⟨z', hz', hz'e⟩
        have hzz : z' = x * z * x⁻¹ := e.injective (by
          rw [show e z' = e x * e z * (e x)⁻¹ from hz'e]
          simp)
        subst hzz
        exact ⟨z, h1.mpr hz', rfl⟩
    have hxk' : e x * e k = e k * e x := by rw [← map_mul, ← map_mul, hxk]
    have h := clause5 (e k) (e x) (hesq k hk2) (fun h => hk1 ((he1 k).mp h))
      (by rw [hord]; exact hx) hxk' _ hY2' hYk' hxY' ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    apply e.injective
    simpa using h
  ·
    intro k x y hk2 hk1 hx hy hxk hyk
    have h := clause6 (e k) (e x) (e y) (hesq k hk2) (fun h => hk1 ((he1 k).mp h))
      (by rw [hord]; exact hx) (by rw [hord]; exact hy) (by rw [← map_mul, ← map_mul, hxk])
      (by rw [← map_mul, ← map_mul, hyk])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, e.injective (by rw [map_zpow, hn])⟩

end CFSG.Quasithin.H13
