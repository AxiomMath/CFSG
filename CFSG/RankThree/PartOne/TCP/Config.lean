module

public import CFSG.RankThree.PartOne.TCP.Block
public import CFSG.RankThree.PartOne.TCP.Unip
public import CFSG.RankThree.PartOne.S11d.PSLRankTwoLow

public section

namespace CFSG.RankThree.PartOne.TCP

open CFSG.GroupTheory.WeirSylow Module
open CFSG.Assembly.LowTwoRank (StatedSp)

section Helpers

variable {F : Type} [Field F]

theorem form_zero_left {S : FormSpace F F} (hS : IsSymplecticSpace S) (y : S.V) : S.F 0 y = 0 := by
  obtain ⟨B, hBF, -, -⟩ := hS
  rw [hBF, map_zero, LinearMap.zero_apply]

theorem form_span_singleton {S : FormSpace F F} (hS : IsSymplecticSpace S) (w : S.V) :
    ∀ x ∈ Submodule.span F {w}, ∀ y ∈ Submodule.span F {w}, S.F x y = 0 := by
  obtain ⟨B, hBF, hBa, -⟩ := hS
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [hBF]
  simp [hBa w]

theorem zpow_apply_mem {V : Type*} [AddCommGroup V] [Module F V] (c : V ≃ₗ[F] V)
    (hc : IsOfFinOrder c) (W : Submodule F V) (h : ∀ w ∈ W, c w ∈ W) (i : ℤ) :
    ∀ w ∈ W, (c ^ i) w ∈ W := by
  have hnat : ∀ k : ℕ, ∀ w ∈ W, (c ^ k) w ∈ W := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ]
      exact ih _ (h w hw)
  have hpos : 0 < orderOf c := hc.orderOf_pos
  have h2 : 0 ≤ i % (orderOf c : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h2
  rw [← zpow_mod_orderOf, hk, zpow_natCast]
  exact hnat k

end Helpers

section RankTwo

variable {Y X : Type*} [Group Y] [Group X]

theorem comm_of_mem_zpowers {c a b : Y} (ha : a ∈ Subgroup.zpowers c)
    (hb : b ∈ Subgroup.zpowers c) : a * b = b * a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ((Commute.refl c).zpow_zpow i j).eq

theorem pow_eq_one_of_mem_zpowers {c a : Y} (ha : a ∈ Subgroup.zpowers c) :
    a ^ orderOf c = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
    one_zpow]

theorem rank_two_range {p : ℕ} (c : Y) (hc : orderOf c = p) (Φ : Y × Y →* X)
    (hΦ : Function.Injective Φ) :
    CFSG.IsElementaryAbelian p ((((Subgroup.zpowers c).prod (Subgroup.zpowers c)).map Φ)) ∧
      Nat.card (((Subgroup.zpowers c).prod (Subgroup.zpowers c)).map Φ) = p ^ 2 := by
  refine ⟨?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro a b
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      show (a : X) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_prod.mp hy
      exact Prod.ext (comm_of_mem_zpowers hx1 hy1) (comm_of_mem_zpowers hx2 hy2)
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      apply Subtype.ext
      show (a : X) ^ p = 1
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
      rw [← hxa, ← map_pow]
      have : x ^ p = 1 := by
        rw [← hc]
        exact Prod.ext (pow_eq_one_of_mem_zpowers hx1) (pow_eq_one_of_mem_zpowers hx2)
      rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hΦ, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, Nat.card_zpowers, hc, sq]

end RankTwo

section Config

variable {F : Type} [Field F]

abbrev cfgSpace (Sb S₃ : FormSpace F F) : FormSpace F F := (Sb.prod Sb).prod S₃

@[expose] noncomputable def cfgHom (Sb S₃ : FormSpace F F) :
    Sb.isom × Sb.isom →* (cfgSpace Sb S₃).isom :=
  ((prodIsometryHom F (Sb.prod Sb).F S₃.F).comp (MonoidHom.inl _ _)).comp
    (prodIsometryHom F Sb.F Sb.F)

theorem cfgHom_apply (Sb S₃ : FormSpace F F) (g : Sb.isom × Sb.isom) (x₁ x₂ : Sb.V)
    (x₃ : S₃.V) :
    ((cfgHom Sb S₃ g : (cfgSpace Sb S₃).isom) :
      (cfgSpace Sb S₃).V ≃ₗ[F] (cfgSpace Sb S₃).V) ((x₁, x₂), x₃) =
      ((g.1.1 x₁, g.2.1 x₂), x₃) := rfl

theorem cfgHom_injective (Sb S₃ : FormSpace F F) : Function.Injective (cfgHom Sb S₃) := by
  intro a b h
  have h1 : ((prodIsometryHom F Sb.F Sb.F a, 1) : (Sb.prod Sb).isom × S₃.isom) =
      (prodIsometryHom F Sb.F Sb.F b, 1) := prodIsometryHom_injective F (Sb.prod Sb).F S₃.F h
  exact prodIsometryHom_injective F Sb.F Sb.F (Prod.ext_iff.mp h1).1

def cfgSub (Sb S₃ : FormSpace F F) (W₁ : Submodule F Sb.V) (W₃ : Submodule F S₃.V) :
    Submodule F (cfgSpace Sb S₃).V :=
  (W₁.prod ⊥).prod W₃

theorem mem_cfgSub {Sb S₃ : FormSpace F F} {W₁ : Submodule F Sb.V} {W₃ : Submodule F S₃.V}
    {x : (cfgSpace Sb S₃).V} :
    x ∈ cfgSub Sb S₃ W₁ W₃ ↔ x.1.1 ∈ W₁ ∧ x.1.2 = 0 ∧ x.2 ∈ W₃ := by
  change (x.1 ∈ W₁.prod ⊥ ∧ x.2 ∈ W₃) ↔ _
  rw [Submodule.mem_prod, Submodule.mem_bot, and_assoc]

theorem cfgSub_iso {Sb S₃ : FormSpace F F} (hSb : IsSymplecticSpace Sb) (W₁ : Submodule F Sb.V)
    (W₃ : Submodule F S₃.V) (h₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, Sb.F x y = 0)
    (h₃ : ∀ x ∈ W₃, ∀ y ∈ W₃, S₃.F x y = 0) :
    ∀ x ∈ cfgSub Sb S₃ W₁ W₃, ∀ y ∈ cfgSub Sb S₃ W₁ W₃, (cfgSpace Sb S₃).F x y = 0 := by
  intro x hx y hy
  obtain ⟨hx1, hx2, hx3⟩ := mem_cfgSub.mp hx
  obtain ⟨hy1, hy2, hy3⟩ := mem_cfgSub.mp hy
  change Sb.F x.1.1 y.1.1 + Sb.F x.1.2 y.1.2 + S₃.F x.2 y.2 = 0
  rw [hx2, hy2, form_zero_left hSb, h₁ _ hx1 _ hy1, h₃ _ hx3 _ hy3]
  simp

theorem cfgSub_inv {Sb S₃ : FormSpace F F} (Z : Subgroup Sb.isom) (W₁ : Submodule F Sb.V)
    (W₃ : Submodule F S₃.V) (hinv : ∀ g ∈ Z, ∀ w ∈ W₁, (g : Sb.V ≃ₗ[F] Sb.V) w ∈ W₁) :
    ∀ r ∈ (Z.prod Z).map (cfgHom Sb S₃), ∀ w ∈ cfgSub Sb S₃ W₁ W₃,
      ((r : (cfgSpace Sb S₃).isom) : (cfgSpace Sb S₃).V ≃ₗ[F] (cfgSpace Sb S₃).V) w ∈
        cfgSub Sb S₃ W₁ W₃ := by
  rintro r ⟨g, hg, rfl⟩ ⟨⟨w1, w2⟩, w3⟩ hw
  obtain ⟨hw1, hw2, hw3⟩ := mem_cfgSub.mp hw
  have hw2' : w2 = 0 := hw2
  rw [cfgHom_apply]
  refine mem_cfgSub.mpr ⟨hinv _ (Subgroup.mem_prod.mp hg).1 _ hw1, ?_, hw3⟩
  show g.2.1 w2 = 0
  rw [hw2', map_zero]

end Config

theorem exists_psp_config {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F) {n : ℕ} (hn : blockDim (orderOf (Nat.card F : ZMod p)) ≤ n) :
    ∃ R : Subgroup ↥(StatedSp n F), CFSG.IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
      ((Even (orderOf (Nat.card F : ZMod p)) → orderOf (Nat.card F : ZMod p) < n) →
        ∃ U : Subgroup ↥(StatedSp n F), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
          R ≤ Subgroup.normalizer (U : Set ↥(StatedSp n F))) := by
  classical
  obtain ⟨Sb, hSb, hdimb, c, hcord, hWb⟩ := exists_block F hp hpF
  set e := orderOf (Nat.card F : ZMod p) with he
  set bd := blockDim e with hbd
  let S₃ : FormSpace F F := stdSympSpace F (n - bd)
  have hS₃ : IsSymplecticSpace S₃ := isSymplecticSpace_stdSympSpace _
  have hS₃dim : finrank F S₃.V = 2 * (n - bd) := finrank_stdSympSpace _
  have hS : IsSymplecticSpace (cfgSpace Sb S₃) :=
    isSymplecticSpace_prod _ _ (isSymplecticSpace_prod _ _ hSb hSb) hS₃
  have hdim : finrank F (cfgSpace Sb S₃).V = 2 * n := by
    rw [FormSpace.finrank_prod, FormSpace.finrank_prod, hS₃dim, hdimb]
    omega
  obtain ⟨ψ, hψ⟩ := exists_injective_isom_statedSp (cfgSpace Sb S₃) hS hdim
  set Z := Subgroup.zpowers c with hZ
  let Ψ : Sb.isom × Sb.isom →* ↥(StatedSp n F) := ψ.comp (cfgHom Sb S₃)
  have hΨ : Function.Injective Ψ := hψ.comp (cfgHom_injective Sb S₃)
  obtain ⟨hRe, hRc⟩ := rank_two_range c hcord Ψ hΨ
  refine ⟨(Z.prod Z).map Ψ, hRe, hRc, fun hcond => ?_⟩
  obtain ⟨W₁, W₃, hW₁inv, hW₁iso, hW₃iso, hnb⟩ : ∃ (W₁ : Submodule F Sb.V)
      (W₃ : Submodule F S₃.V), (∀ g ∈ Z, ∀ w ∈ W₁, (g : Sb.V ≃ₗ[F] Sb.V) w ∈ W₁) ∧
      (∀ x ∈ W₁, ∀ y ∈ W₁, Sb.F x y = 0) ∧ (∀ x ∈ W₃, ∀ y ∈ W₃, S₃.F x y = 0) ∧
      (W₁ ≠ ⊥ ∨ W₃ ≠ ⊥) := by
    by_cases hev : Even e
    · have hen : e < n := hcond hev
      have hbde : bd = e := by rw [hbd]; exact ite_eq_left_iff.mpr (fun h => absurd hev h)
      have hpos : 0 < finrank F S₃.V := by rw [hS₃dim]; omega
      have : Nontrivial S₃.V := Module.finrank_pos_iff.mp hpos
      obtain ⟨w₃, hw₃⟩ := exists_ne (0 : S₃.V)
      refine ⟨⊥, Submodule.span F {w₃}, ?_, ?_, form_span_singleton hS₃ w₃, Or.inr ?_⟩
      · intro g _ w hw
        rw [Submodule.mem_bot] at hw ⊢
        rw [hw, map_zero]
      · intro x hx y hy
        rw [Submodule.mem_bot] at hx hy
        rw [hx, hy, form_zero_left hSb]
      · rw [Ne, Submodule.span_singleton_eq_bot]
        exact hw₃
    · obtain ⟨W, hW0, hWiso, hWinv⟩ := hWb hev
      refine ⟨W, ⊥, ?_, hWiso, ?_, Or.inl hW0⟩
      · intro g hg w hw
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hfin : IsOfFinOrder (c : Sb.V ≃ₗ[F] Sb.V) := by
          refine isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, ?_⟩
          have := congrArg (fun x : Sb.isom => (x : Sb.V ≃ₗ[F] Sb.V)) (hcord ▸ pow_orderOf_eq_one c)
          simpa using this
        have := zpow_apply_mem (c : Sb.V ≃ₗ[F] Sb.V) hfin W hWinv i w hw
        simpa using this
      · intro x hx y hy
        rw [Submodule.mem_bot] at hx hy
        rw [hx, hy, form_zero_left hS₃]
  have hW0 : cfgSub Sb S₃ W₁ W₃ ≠ ⊥ := by
    rcases hnb with h | h
    · obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp h
      refine (Submodule.ne_bot_iff _).mpr ⟨((w, 0), 0), mem_cfgSub.mpr ⟨hw, rfl, ?_⟩, ?_⟩
      · exact W₃.zero_mem
      · intro h0
        exact hw0 (congrArg (fun x => x.1.1) h0)
    · obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp h
      refine (Submodule.ne_bot_iff _).mpr ⟨((0, 0), w), mem_cfgSub.mpr ⟨W₁.zero_mem, rfl, hw⟩, ?_⟩
      intro h0
      exact hw0 (congrArg (fun x => x.2) h0)
  obtain ⟨U, hU0, hU2, hUN⟩ := exists_unip_of_isotropic (S := cfgSpace Sb S₃) hS hW0
    (cfgSub_iso hSb W₁ W₃ hW₁iso hW₃iso) (R := (Z.prod Z).map (cfgHom Sb S₃))
    (cfgSub_inv Z W₁ W₃ hW₁inv)
  obtain ⟨hRe', hRc'⟩ := rank_two_range c hcord (cfgHom Sb S₃) (cfgHom_injective Sb S₃)
  obtain ⟨-, -, h3, h4, h5⟩ := rankTwoCfg_map ψ ((Z.prod Z).map (cfgHom Sb S₃)) U
    (fun x _ y _ h => hψ h) (fun x _ h => hψ (by simpa using h)) hRe' hRc' hU0 hU2 hUN
  refine ⟨U.map ψ, h3, h4, ?_⟩
  rwa [Subgroup.map_map] at h5

end CFSG.RankThree.PartOne.TCP
