module

public import CFSG.Quasithin.H13.NQS1312L
public import CFSG.Quasithin.H13.NQS1312K
public import CFSG.Quasithin.Vol2.Ch3zSetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SteinbergCB
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem two_pow_good {m : ℕ} (h3 : 2 ^ m % 3 = 1) (h4 : 2 ^ m ≠ 4) : 2 ^ m = 1 ∨ 16 ≤ 2 ^ m := by
  rcases Nat.lt_or_ge m 4 with hm | hm
  · interval_cases m <;> simp_all
  · right
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem chief_good_line (hU33 : U33CommDimFact) {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6} (hLV : L ≤ normalizer (V : Set G))
    (hCL : L ⊓ centralizer (V : Set G) = pCoreOf 2 L)
    (hΦL : ∀ (l : G) (hl : l ∈ L), tau Φ ⟨l, hLV hl⟩ ∈ J6)
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), tau Φ ⟨l, hLV hl⟩ = j)
    {k₁ : G} (hk₁L : k₁ ∈ L) (hk₁3 : k₁ ^ 3 = 1) (hk₁τ : tau Φ ⟨k₁, hLV hk₁L⟩ = kGL)
    (A B : Subgroup G) (hAB : A ≤ normalizer (B : Set G)) (hlt : B < A) (hA : IsPGroup 2 A)
    (hLA : L ≤ normalizer (A : Set G)) (hLB : L ≤ normalizer (B : Set G))
    (hab : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) (hsq : ∀ a ∈ A, a ^ 2 ∈ B)
    (hirr : ∀ C : Subgroup G, B ≤ C → C ≤ A → L ≤ normalizer (C : Set G) → C = B ∨ C = A) :
    (fixSub A B k₁ hAB).relIndex A = 1 ∨ 16 ≤ (fixSub A B k₁ hAB).relIndex A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := Ch3z.chiefMod B A with hWdef
  set ι := Ch3z.chiefIota hAB with hιdef
  have hι : Function.Surjective ι := Ch3z.chiefIota_surjective hAB
  have hι1 : ∀ a : ↥A, ι a = 1 ↔ (a : G) ∈ B := Ch3z.chiefIota_eq_one_iff hAB
  have hcomm : ∀ x y : ↥W, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := hι x
    obtain ⟨b, rfl⟩ := hι y
    have h1 : ι (a * b * a⁻¹ * b⁻¹) = 1 := (hι1 _).2 (hab a a.2 b b.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ι a * ι b = (ι a * ι b * (ι a)⁻¹ * (ι b)⁻¹) * (ι b * ι a) := by group
      _ = ι b * ι a := by rw [h1, one_mul]
  let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hcomm }
  have hexp : ∀ w : ↥W, w ^ 2 = 1 := by
    intro w
    obtain ⟨a, rfl⟩ := hι w
    rw [← map_pow]
    exact (hι1 _).2 (by simpa using hsq a a.2)
  set ψ := Ch3z.chiefPsi hLB hLA with hψdef
  have hψι : ∀ (l : ↥L) (a : ↥A) (h : (l : G) * a * (l : G)⁻¹ ∈ A),
      ψ l (ι a) = ι ⟨(l : G) * a * (l : G)⁻¹, h⟩ := fun l a h =>
    Ch3z.chiefPsi_iota hLB hLA hAB l a h
  have hO2 := commutator_le_of_irreducible (X := L) (W := A) (W₁ := B) (P := pCoreOf 2 L)
    (pCoreOf_isPGroup 2 L) (pCoreOf_le 2 L) hLA hLB (le_normalizer_pCoreOf 2 L) hlt.le hA hAB hirr
  have hψO : ∀ l : ↥L, (l : G) ∈ pCoreOf 2 L → ψ l = 1 := by
    intro l hl
    ext w
    obtain ⟨a, rfl⟩ := hι w
    have h : (l : G) * a * (l : G)⁻¹ ∈ A := (mem_normalizer_iff.1 (hLA l.2) a).1 a.2
    rw [hψι l a h, MulAut.one_apply]
    have h1 : ι (⟨(l : G) * a * (l : G)⁻¹, h⟩ * a⁻¹) = 1 := (hι1 _).2 (hO2 l hl a a.2)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1]
  set τL : ↥L →* ↥J6 := ((tau Φ).comp (Subgroup.inclusion hLV)).codRestrict J6
    (fun l => hΦL l l.2) with hτL
  have hτs : Function.Surjective τL := by
    rintro ⟨j, hj⟩
    obtain ⟨l, hl, hlj⟩ := hΦLs j hj
    exact ⟨⟨l, hl⟩, Subtype.ext hlj⟩
  have hτker : τL.ker ≤ ψ.ker := by
    intro l hl
    have h1 : tau Φ ⟨l, hLV l.2⟩ = 1 := congrArg Subtype.val hl
    have h2 : (l : G) ∈ L ⊓ centralizer (V : Set G) := ⟨l.2, tau_eq_one_iff.1 h1⟩
    rw [hCL] at h2
    exact hψO l h2
  set ρ : ↥J6 →* MulAut ↥W := (QuotientGroup.lift τL.ker ψ hτker).comp
    (QuotientGroup.quotientKerEquivOfSurjective τL hτs).symm.toMonoidHom with hρdef
  have hρτ : ∀ l : ↥L, ρ (τL l) = ψ l := by
    intro l
    rw [hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : (QuotientGroup.quotientKerEquivOfSurjective τL hτs).symm (τL l) =
        (QuotientGroup.mk l : ↥L ⧸ τL.ker) :=
      (MulEquiv.symm_apply_eq _).2 rfl
    rw [this, QuotientGroup.lift_mk]
  have hρirr : ∀ U : Subgroup ↥W, (∀ (g : ↥J6), ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hUL : ∀ l : ↥L, ∀ u ∈ U, ψ l u ∈ U := fun l u hu => by
      rw [← hρτ]
      exact hU _ u hu
    have hLpre : L ≤ normalizer (Ch3z.chiefPre hAB U : Set G) := by
      have key : ∀ l ∈ L, ∀ x ∈ Ch3z.chiefPre hAB U, l * x * l⁻¹ ∈ Ch3z.chiefPre hAB U := by
        intro l hl x hx
        obtain ⟨hxA, hxU⟩ := (Ch3z.mem_chiefPre hAB U).1 hx
        have h : l * x * l⁻¹ ∈ A := (mem_normalizer_iff.1 (hLA hl) x).1 hxA
        refine (Ch3z.mem_chiefPre hAB U).2 ⟨h, ?_⟩
        rw [← hψι ⟨l, hl⟩ ⟨x, hxA⟩ h]
        exact hUL _ _ hxU
      intro l hl
      rw [mem_normalizer_iff]
      intro x
      refine ⟨key l hl x, fun hx => ?_⟩
      have := key l⁻¹ (L.inv_mem hl) _ hx
      simpa [mul_assoc] using this
    rcases hirr _ (Ch3z.le_chiefPre hAB hlt.le U) (Ch3z.chiefPre_le hAB U) hLpre with h | h
    · exact Or.inl (Ch3z.eq_bot_of_chiefPre_eq hAB U h)
    · exact Or.inr (Ch3z.eq_top_of_chiefPre_eq hAB U h)
  set σ := ψ ⟨k₁, hk₁L⟩ with hσdef
  have hτk : τL ⟨k₁, hk₁L⟩ = ⟨kGL, kGL_mem_J6⟩ := Subtype.ext hk₁τ
  have hσρ : ρ ⟨kGL, kGL_mem_J6⟩ = σ := by rw [← hτk, hρτ]
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσdef, ← map_pow]
    have : (⟨k₁, hk₁L⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hk₁3)
    rw [this, map_one]
  let f : ↥W →* ↥W :=
    { toFun := fun w => σ w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        rw [map_mul, mul_inv_rev]
        rw [mul_comm w⁻¹ v⁻¹]
        rw [mul_assoc, ← mul_assoc (σ w), mul_comm (σ w) v⁻¹]
        group }
  have hf : ∀ w, f w = σ w * w⁻¹ := fun w => rfl
  have hcomap : (fixSub A B k₁ hAB).subgroupOf A = f.ker.comap ι := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.mem_ker, hf, mul_inv_eq_one, hσdef]
    have h : k₁ * (a : G) * k₁⁻¹ ∈ A := (mem_normalizer_iff.1 (hLA hk₁L) a).1 a.2
    rw [hψι ⟨k₁, hk₁L⟩ a h]
    constructor
    · rintro ⟨-, ha⟩
      have h1 : ι (⟨k₁ * (a : G) * k₁⁻¹, h⟩ * a⁻¹) = 1 := by
        refine (hι1 _).2 ?_
        have e : k₁ * (a : G) * k₁⁻¹ * (a : G)⁻¹ =
            (a : G) * ((a : G)⁻¹ * (k₁ * a * k₁⁻¹)) * (a : G)⁻¹ := by group
        show k₁ * (a : G) * k₁⁻¹ * (a : G)⁻¹ ∈ B
        rw [e]
        exact (mem_normalizer_iff.1 (hAB a.2) _).1 ha
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    · intro h1
      refine ⟨a.2, ?_⟩
      have h2 : ι (⟨k₁ * (a : G) * k₁⁻¹, h⟩ * a⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := (hι1 _).1 h2
      have e : (a : G)⁻¹ * (k₁ * a * k₁⁻¹) =
          (a : G)⁻¹ * (k₁ * (a : G) * k₁⁻¹ * (a : G)⁻¹) * (a : G)⁻¹⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 (hAB (A.inv_mem a.2)) _).1 h3
  have hidx : (fixSub A B k₁ hAB).relIndex A = Nat.card f.range := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hι, Subgroup.index_ker]
  have hne4 : Nat.card f.range ≠ 4 := by
    intro h4
    have hcard : Nat.card (Set.range fun w : ↥W => ρ ⟨kGL, kGL_mem_J6⟩ w * w⁻¹) = 4 := by
      rw [hσρ, ← h4]
      rfl
    have htriv := hU33 ↥W hexp ρ hρirr hcard
    have hσ1 : σ = 1 := by rw [← hσρ]; exact htriv _
    have hf1 : ∀ w, f w = 1 := fun w => by rw [hf, hσ1, MulAut.one_apply, mul_inv_cancel]
    have : Nat.card f.range = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
      obtain ⟨_, ⟨v, rfl⟩⟩ := x
      obtain ⟨_, ⟨w, rfl⟩⟩ := y
      exact Subtype.ext (show f v = f w by rw [hf1, hf1])
    omega
  have hmod : Nat.card f.range % 3 = 1 := by
    have hσf : ∀ w, σ (f w) = f (σ w) := fun w => by rw [hf, hf, map_mul, map_inv]
    let φ : Function.End ↥f.range := fun r => ⟨σ r, by
      obtain ⟨w, hw⟩ := r.2
      exact ⟨σ w, by rw [← hσf, hw]⟩⟩
    have hφ3 : φ ^ 3 = 1 := by
      funext r
      apply Subtype.ext
      show σ (σ (σ r)) = r
      have := congrArg (fun τ : MulAut ↥W => τ r) hσ3
      simpa [pow_succ] using this
    have hfix : ∀ r : ↥f.range, φ r = r → r = 1 := by
      rintro ⟨_, w, rfl⟩ hr
      have h1 : σ (f w) = f w := congrArg Subtype.val hr
      rw [hf, map_mul, map_inv] at h1
      have h2 : σ (σ w) = w := by
        have e1 := hexp (σ w)
        have e2 := hexp w
        calc σ (σ w) = σ (σ w) * (σ w)⁻¹ * σ w := by group
          _ = σ w * w⁻¹ * σ w := by rw [h1]
          _ = (σ w) ^ 2 * w⁻¹ := by rw [pow_two]; exact (mul_right_comm _ _ _)
          _ = w := by rw [e1, one_mul, inv_eq_of_mul_eq_one_left (by rw [← pow_two, e2])]
      have h3 : σ w = w := by
        have := congrArg (fun τ : MulAut ↥W => τ w) hσ3
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at this
        rw [h2] at this
        exact this
      exact Subtype.ext (show f w = 1 by rw [hf, h3, mul_inv_cancel])
    have : Fintype ↥f.range := Fintype.ofFinite _
    have hcong := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := φ)
      (by simpa using hφ3)
    have hfp : Nat.card (Function.fixedPoints φ) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ((hfix x x.2).trans (hfix y y.2).symm)⟩, ⟨⟨1, ?_⟩⟩⟩
      show φ 1 = 1
      apply Subtype.ext
      show σ 1 = 1
      exact map_one σ
    have hcong' : Nat.card ↥f.range ≡ Nat.card (Function.fixedPoints φ) [MOD 3] := by
      convert hcong using 1 <;> exact Nat.card_eq_fintype_card
    rw [hfp] at hcong'
    exact hcong'
  have hW2 : IsPGroup 2 ↥W := by
    intro w
    obtain ⟨a, rfl⟩ := hι w
    obtain ⟨m, hm⟩ := hA a
    exact ⟨m, by rw [← map_pow, hm, map_one]⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (hW2.to_subgroup f.range)
  rw [hidx, hm]
  rw [hm] at hmod hne4
  exact two_pow_good hmod hne4

end CFSG.Quasithin.H13.U3.NLine
