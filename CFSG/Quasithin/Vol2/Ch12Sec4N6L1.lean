module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Q
public import CFSG.Quasithin.Vol2.Ch12Sec4N6L3b

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => ⟨(hA x).1 hx.1, (hB x).1 hx.2⟩, fun hx => ⟨(hA x).2 hx.1, (hB x).2 hx.2⟩⟩

omit [Finite G] in
theorem pow_four_pow_eq {M : Type*} [Monoid M] {x : M} (hx : x * x * x = 1) (k : ℕ) :
    x ^ 4 ^ k = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, pow_three', hx, one_mul]

omit [Finite G] in
theorem odd_orderOf_of_cube {x : G} (hx : x * x * x = 1) : Odd (orderOf x) := by
  have h3 : x ^ 3 = 1 := by rw [pow_three', hx]
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

abbrev L1 (_ : Ctx T L V E z v) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.centralizer (E : Set G))

theorem L1_le : c.L1 ≤ L ⊓ Subgroup.centralizer (E : Set G) := oTwoUpper_le _

theorem CE_le_M : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  rw [c.M_eq]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 c.facts4.1)

omit [Finite G] [IsMulCommutative ↥V] c in
theorem mem_N_CLE {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) :
    x ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf hxL (F7.normalizer_le_normalizer_centralizer E hxE)

theorem mem_N_L1 {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) : x ∈ Subgroup.normalizer (c.L1 : Set G) :=
  normalizer_le_normalizer_oTwoUpper _ (mem_N_CLE hxL hxE)

theorem CE_le_N_L1 : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (c.L1 : Set G) :=
  fun _ hx => c.mem_N_L1 (c.CE_le_M hx) (Subgroup.centralizer_le_normalizer (E : Set G) hx)

theorem two_elt {x : G} (hxL : x ∈ L) (hxV : x ∈ Subgroup.centralizer (V : Set G)) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ⟨x, c.inf_centralizer_le_pCore ⟨hxL, hxV⟩⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem two_elt_of_sq {x : G} (hxL : x ∈ L) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (h2 : conjAct V ⟨x, hxN⟩ * conjAct V ⟨x, hxN⟩ = 1) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have hxx : x * x ∈ Subgroup.centralizer (V : Set G) := by
    have hN : x * x ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hxN hxN
    have : conjAct V ⟨x * x, hN⟩ = 1 := by
      have e : (⟨x * x, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨x, hxN⟩ * ⟨x, hxN⟩ := rfl
      rw [e, map_mul, h2]
    exact A4.conjAct_eq_one_iff.1 this
  obtain ⟨k, hk⟩ := c.two_elt (L.mul_mem hxL hxL) hxx
  refine ⟨k + 1, ?_⟩
  rw [pow_succ, pow_mul, ← hk, ← pow_two, ← pow_mul, ← pow_mul, mul_comm]

theorem rho_v_of_not_odd (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {γ : Γ}
    (hγ : act γ (c.cv D) = c.cv D) (hodd : ¬ OddAt (c.cv D) γ) :
    D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩ := by
  obtain ⟨x, hxc, hx3, hx3'⟩ := prodThree_of_not_odd _ γ ⟨c.cv_ne D, hγ, hodd⟩
  have hxc' : act (x⁻¹ * γ) (c.cv D) = c.cv D := by
    rw [act_mul, hγ]
    conv_lhs => rw [← hxc]
    exact act_inv_act x _
  have : γ = x * (x⁻¹ * γ) := by group
  rw [this, map_mul, MulAut.mul_apply, c.rho_v_of_three D hxc' hx3', c.rho_v_of_three D hxc hx3]

theorem exists_tau (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) :
    ∃ τ : Γ, act τ (c.cv D) = c.cv D ∧ OddAt (c.cv D) τ ∧
      D.rho τ (⟨v, c.EV c.vE⟩ : ↥V) ≠ ⟨v, c.EV c.vE⟩ := by
  obtain ⟨t₀, ht₀, ht₀v⟩ := c.exists_t0
  have ht₀N : t₀ ∈ Subgroup.normalizer (V : Set G) := c.f.T_le ht₀
  have ht₀L : conjAct V ⟨t₀, ht₀N⟩ ∈ autOn L V := by
    have : conjAct V ⟨t₀, ht₀N⟩ ∈ autOn T V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht₀)
    rw [c.Tbar] at this
    exact c.Tsyl.1 this
  obtain ⟨τ, hτ⟩ := D.exists_rho ht₀L
  have hτc : act τ (c.cv D) = c.cv D := c.act_cv_of_normalizes D ht₀N (c.TE ht₀) hτ
  have hτv : D.rho τ (⟨v, c.EV c.vE⟩ : ↥V) ≠ ⟨v, c.EV c.vE⟩ := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [hτ, conjAct_coe] at h1
    exact c.vz_ne_v (ht₀v.symm.trans h1)
  refine ⟨τ, hτc, ?_, hτv⟩
  by_contra hτo
  exact hτv (c.rho_v_of_not_odd D hτc hτo)

theorem image_CLE (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {x : G}
    (hx : x ∈ L ⊓ Subgroup.centralizer (E : Set G)) :
    ∃ γ : Γ, D.rho γ = conjAct V ⟨x, c.f.normalizes hx.1⟩ ∧ act γ (c.cv D) = c.cv D ∧
      γ * γ * γ ∈ AS {0, c.cv D} := by
  have hxN := c.f.normalizes hx.1
  obtain ⟨γ, hγ⟩ := D.exists_rho (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx.1) :
    conjAct V ⟨x, hxN⟩ ∈ autOn L V)
  have hγc := c.act_cv_of_normalizes D hxN (Subgroup.centralizer_le_normalizer (E : Set G) hx.2) hγ
  refine ⟨γ, hγ, hγc, ?_⟩
  have hfix : D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) = ⟨v, c.EV c.vE⟩ := by
    apply Subtype.ext
    rw [hγ, conjAct_coe]
    have := Subgroup.mem_centralizer_iff.1 hx.2 v c.vE
    simp only
    rw [← this, mul_inv_cancel_right]
  by_contra hodd
  have hodd' : OddAt (c.cv D) γ := hodd
  obtain ⟨τ, hτc, hτodd, hτv⟩ := c.exists_tau D
  have heven := not_odd_mul _ τ γ ⟨c.cv_ne D, hτc, hγc, hτodd, hodd'⟩
  have hτγc : act (τ⁻¹ * γ) (c.cv D) = c.cv D := by
    rw [act_mul, hγc]
    conv_lhs => rw [← hτc]
    exact act_inv_act τ _
  have h1 := c.rho_v_of_not_odd D hτγc heven
  have h2 : D.rho γ (⟨v, c.EV c.vE⟩ : ↥V) = D.rho τ (⟨v, c.EV c.vE⟩ : ↥V) := by
    conv_lhs => rw [show γ = τ * (τ⁻¹ * γ) by group]
    rw [map_mul, MulAut.mul_apply, h1]
  exact hτv (h2.symm.trans hfix)

theorem exists_a : ∃ a ∈ c.L1, a * a * a = 1 ∧ a ∉ Subgroup.centralizer (V : Set G) := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  obtain ⟨δ, hδc, hδ3, hδ1⟩ := exists_three (c.cv D) (c.cv_ne D)
  obtain ⟨l, hlL, hlN, hl⟩ := Ctx.exists_of_mem_autOn (D.rho_mem δ)
  have key : ∀ w : ↥V, D.rho δ w = w → (w : G) * l = l * w := by
    intro w hw
    have h1 := congrArg Subtype.val hw
    rw [← hl, conjAct_coe] at h1
    calc (w : G) * l = l * w * l⁻¹ * l := by rw [h1]
      _ = l * w := by group
  have hlE : l ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    have hz := key _ (c.rho_z D δ)
    have hv := key _ (c.rho_v_of_three D hδc hδ3)
    intro e he
    rcases c.mem_E he with h | h | h | h <;> rw [h]
    · simp
    · exact hz
    · exact hv
    · calc v * z * l = v * (z * l) := by group
        _ = v * (l * z) := by rw [hz]
        _ = (v * l) * z := by group
        _ = l * v * z := by rw [hv]
        _ = l * (v * z) := by group
  have hlll : l * l * l ∈ Subgroup.centralizer (V : Set G) := by
    have hN : l * l * l ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hlN) hlN
    have : conjAct V ⟨l * l * l, hN⟩ = 1 := by
      have e : (⟨l * l * l, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨l, hlN⟩ * ⟨l, hlN⟩ * ⟨l, hlN⟩ := rfl
      rw [e, map_mul, map_mul, hl, ← map_mul, ← map_mul, hδ3, map_one]
    exact A4.conjAct_eq_one_iff.1 this
  obtain ⟨k, hk⟩ := c.two_elt (L.mul_mem (L.mul_mem hlL hlL) hlL) hlll
  have hlCLE : l ∈ L ⊓ Subgroup.centralizer (E : Set G) := ⟨hlL, hlE⟩
  have h3 : l ^ 4 ^ k * l ^ 4 ^ k * l ^ 4 ^ k = 1 := by
    have e1 : (l * l * l) ^ 4 ^ k = l ^ 4 ^ k * l ^ 4 ^ k * l ^ 4 ^ k := by
      rw [((Commute.refl l).mul_left (Commute.refl l)).mul_pow, (Commute.refl l).mul_pow]
    rw [← e1, show (4 : ℕ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num, pow_mul, hk,
      one_pow]
  refine ⟨l ^ 4 ^ k, mem_oTwoUpper_of_odd (Subgroup.pow_mem _ hlCLE _)
    (odd_orderOf_of_cube h3), h3, fun hV => ?_⟩
  have hN : l ^ 4 ^ k ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hlN _
  have h1 : conjAct V ⟨l ^ 4 ^ k, hN⟩ = 1 := A4.conjAct_eq_one_iff.2 hV
  have e : (⟨l ^ 4 ^ k, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨l, hlN⟩ ^ 4 ^ k := rfl
  rw [e, map_pow, hl, ← map_pow, pow_four_pow_eq hδ3] at h1
  exact hδ1 (D.rho_injective (h1.trans (map_one _).symm))

theorem L1_gen (D : L3Data (autOn L V) ⊤ (fixV (autOn L V))) {x : G}
    (hx : x ∈ L ⊓ Subgroup.centralizer (E : Set G)) (hx3 : x * x * x = 1)
    (hx1 : x ∉ Subgroup.centralizer (V : Set G)) {l : G}
    (hl : l ∈ L ⊓ Subgroup.centralizer (E : Set G)) :
    ∃ i : ℕ, ∃ k : ℕ, (x⁻¹ ^ i * l) ^ 2 ^ k = 1 := by
  obtain ⟨γx, hγx, hγxc, -⟩ := c.image_CLE D hx
  obtain ⟨γl, hγl, hγlc, hγl3⟩ := c.image_CLE D hl
  have hxN := c.f.normalizes hx.1
  have hlN := c.f.normalizes hl.1
  have hγx3 : γx * γx * γx = 1 := by
    apply D.rho_injective
    rw [map_mul, map_mul, hγx, ← map_mul, ← map_mul, map_one]
    exact A4.conjAct_eq_one_iff.2 (by
      show x * x * x ∈ Subgroup.centralizer (V : Set G)
      rw [hx3]; exact Subgroup.one_mem _)
  have hγx1 : γx ≠ 1 := fun h => hx1 (A4.conjAct_eq_one_iff.1 (by rw [← hγx, h, map_one]))
  have himg : ∀ i : ℕ, ∀ hN : x⁻¹ ^ i * l ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨x⁻¹ ^ i * l, hN⟩ = D.rho (γx⁻¹ ^ i * γl) := by
    intro i hN
    have e : (⟨x⁻¹ ^ i * l, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ ^ i * ⟨l, hlN⟩ := rfl
    rw [e, map_mul, map_pow, map_inv, ← hγx, ← hγl, map_mul, map_pow, map_inv]
  have hcase : ∀ i : ℕ, (γx⁻¹ ^ i * γl) * (γx⁻¹ ^ i * γl) = 1 →
      ∃ i : ℕ, ∃ k : ℕ, (x⁻¹ ^ i * l) ^ 2 ^ k = 1 := by
    intro i hi
    have hmem : x⁻¹ ^ i * l ∈ L := L.mul_mem (L.pow_mem (L.inv_mem hx.1) i) hl.1
    have hN : x⁻¹ ^ i * l ∈ Subgroup.normalizer (V : Set G) := c.f.normalizes hmem
    obtain ⟨k, hk⟩ := c.two_elt_of_sq hmem hN (by rw [himg i hN, ← map_mul, hi, map_one])
    exact ⟨i, k, hk⟩
  rcases a4_gen _ (c.cv_ne D) γx γl hγxc hγx3 hγx1 hγlc hγl3 with h | h | h
  · exact hcase 0 (by simpa using h)
  · exact hcase 1 (by simpa using h)
  · exact hcase 2 (by simpa [pow_two, mul_assoc] using h)

theorem L1_le_of_mem {N : Subgroup G}
    (hN : L ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (N : Set G)) {x : G}
    (hx : x ∈ L ⊓ Subgroup.centralizer (E : Set G)) (hxN : x ∈ N) (hx3 : x * x * x = 1)
    (hx1 : x ∉ Subgroup.centralizer (V : Set G)) : c.L1 ≤ N := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  refine oTwoUpper_le_of_pow_mem fun l hl => ?_
  obtain ⟨i, k, hk⟩ := c.L1_gen D hx hx3 hx1 hl
  have hw : x⁻¹ ^ i * l ∈ Subgroup.normalizer (N : Set G) :=
    hN (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.inv_mem _ hx) i) hl)
  obtain ⟨x', hx', h⟩ := A4.exists_pow_mul_eq (Subgroup.pow_mem _ hxN i) hw (2 ^ k)
  refine ⟨k, ?_⟩
  have e : l = x ^ i * (x⁻¹ ^ i * l) := by rw [inv_pow, mul_inv_cancel_left]
  rw [e, h, hk, mul_one]
  exact hx'

theorem oTwoUpper_CV_le (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) :
    oTwoUpper (Subgroup.centralizer (V : Set G)) ≤ Subgroup.centralizer (L : Set G) := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro y ⟨hyV, hyodd⟩
  have hyM : y ∈ Subgroup.normalizer (L : Set G) := by
    rw [c.M_eq]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 c.f.mem_zV.1) hyV
  set P₀ : Subgroup G := L ⊓ pCoreOf 2 (L ⊔ T) with hP₀
  have hVP : V ≤ P₀ := le_inf c.V_le_L c.V_le_Q
  have hpL : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ P₀ := by
    intro l hl
    have h1 : y * l * y⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.1 hyM l).1 hl) (L.inv_mem hl)
    refine ⟨h1, c.CV_le_Q ⟨Subgroup.mem_sup_left h1,
      Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩⟩
    have hlN := c.f.normalizes hl
    have hw' : l⁻¹ * w * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hlN) w).1 hw
      simpa using this
    have hyw : y * w = w * y := (Subgroup.mem_centralizer_iff.1 hyV w hw).symm
    have hyw' : y * (l⁻¹ * w * l) = (l⁻¹ * w * l) * y :=
      (Subgroup.mem_centralizer_iff.1 hyV _ hw').symm
    have hX : (l⁻¹ * w * l) * y⁻¹ = y⁻¹ * (l⁻¹ * w * l) :=
      ((Commute.inv_left (hyw' : Commute y (l⁻¹ * w * l))).eq).symm
    calc w * (y * l * y⁻¹ * l⁻¹) = (w * y) * l * y⁻¹ * l⁻¹ := by group
      _ = (y * w) * l * y⁻¹ * l⁻¹ := by rw [hyw]
      _ = y * l * ((l⁻¹ * w * l) * y⁻¹) * l⁻¹ := by group
      _ = y * l * (y⁻¹ * (l⁻¹ * w * l)) * l⁻¹ := by rw [hX]
      _ = (y * l * y⁻¹ * l⁻¹) * w := by group
  have hPL : ∀ u ∈ P₀, ∀ l ∈ L, l * u * l⁻¹ * u⁻¹ ∈ V := fun u hu l hl =>
    comm_mem hcomm hu.2 hl
  have hVn : (V.subgroupOf P₀).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have hbN : (b : G) ∈ Subgroup.normalizer (V : Set G) := c.f.normalizes b.2.1
    simpa using (Subgroup.mem_normalizer_iff.1 hbN a).1 ha
  let pf : ↥L → ↥P₀ := fun l => ⟨y * l * y⁻¹ * (l : G)⁻¹, hpL l l.2⟩
  have hmk : ∀ a b : ↥P₀, (a : G)⁻¹ * b ∈ V →
      (QuotientGroup.mk a : ↥P₀ ⧸ V.subgroupOf P₀) = QuotientGroup.mk b := by
    intro a b hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  have hcommQ : ∀ a b : ↥P₀ ⧸ V.subgroupOf P₀, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        apply hmk
        have h1 := hPL (a : G)⁻¹ (P₀.inv_mem a.2) (b : G)⁻¹ (L.inv_mem b.2.1)
        have e : ((a * b : ↥P₀) : G)⁻¹ * ((b * a : ↥P₀) : G) =
            (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
        rw [e]
        exact h1
  let Φ : ↥L →* ↥P₀ ⧸ V.subgroupOf P₀ :=
    MonoidHom.mk' (fun l => QuotientGroup.mk (pf l)) (by
      intro a b
      rw [← QuotientGroup.mk_mul]
      apply hmk
      have h1 := hPL (pf b : G)⁻¹ (P₀.inv_mem (pf b).2) (a : G) a.2
      have e : ((pf (a * b) : ↥P₀) : G)⁻¹ * ((pf a * pf b : ↥P₀) : G) =
          (a : G) * (pf b : G)⁻¹ * (a : G)⁻¹ * (pf b : G)⁻¹⁻¹ := by
        simp only [pf, Subgroup.coe_mul]
        group
      rw [e]
      exact h1)
  have hker : ∀ l : ↥L, Φ l = 1 := by
    have hLL : L ≤ (Φ.ker).map L.subtype := by
      conv_lhs => rw [← perfect_of_mem_cComp c.comp]
      rw [Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆, MonoidHom.mem_ker.2 ?_, rfl⟩
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcommQ _ _
    intro l
    obtain ⟨l', hl', hl'l⟩ := hLL l.2
    have : l' = l := Subtype.ext hl'l
    rw [← this]
    exact hl'
  have hpV : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ V := by
    intro l hl
    have h1 := hker ⟨l, hl⟩
    have h2 : (QuotientGroup.mk (pf ⟨l, hl⟩) : ↥P₀ ⧸ V.subgroupOf P₀) = 1 := h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  show y ∈ Subgroup.centralizer (L : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  set p := y * l * y⁻¹ * l⁻¹ with hp
  have hpv := hpV l hl
  have hyp : y * p = p * y := (Subgroup.mem_centralizer_iff.1 hyV p hpv).symm
  have hiter : ∀ n : ℕ, y ^ n * l * (y ^ n)⁻¹ = p ^ n * l := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hyp' : y * p ^ n = p ^ n * y := (Commute.pow_right hyp n).eq
      calc y ^ (n + 1) * l * (y ^ (n + 1))⁻¹ = y * (y ^ n * l * (y ^ n)⁻¹) * y⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = y * (p ^ n * l) * y⁻¹ := by rw [ih]
        _ = p ^ n * (y * l * y⁻¹) := by rw [← mul_assoc, hyp']; group
        _ = p ^ n * (p * l) := by rw [hp]; group
        _ = p ^ (n + 1) * l := by rw [pow_succ]; group
  have h1 := hiter (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hpn : p ^ orderOf y = 1 := by
    have := congrArg (· * l⁻¹) h1
    simp only [mul_inv_cancel, mul_inv_cancel_right] at this
    exact this.symm
  have hp2 : p ^ 2 = 1 := c.f.sq p hpv
  obtain ⟨m, hm⟩ := hyodd
  have hp1 : p = 1 := by
    rw [hm, pow_succ, pow_mul, hp2, one_pow, one_mul] at hpn
    exact hpn
  have : y * l * y⁻¹ = l := by
    calc y * l * y⁻¹ = p * l := by rw [hp]; group
      _ = l := by rw [hp1, one_mul]
  calc l * y = (y * l * y⁻¹) * y := by rw [this]
    _ = y * l := by group

end Ctx

end N1246

end CFSG.Quasithin.H13
