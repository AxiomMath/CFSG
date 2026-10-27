module

public import CFSG.LocalAnalysis.SteinbergSFOneAxisRadicalFusion
public import CFSG.LocalAnalysis.SteinbergCDQuadraticGraphTranslations

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisSecond

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD
open scoped Matrix Pointwise

section Quotient

variable {G : Type*} [Group G]

theorem exists_quotient_mulEquiv_quotient {D B A U : Subgroup G} {t : G}
    [(B.subgroupOf D).Normal] [(U.subgroupOf A).Normal]
    (hA : ∀ d ∈ D, t⁻¹ * (d⁻¹ * t * d) ∈ A)
    (hmul : ∀ d ∈ D, ∀ d' ∈ D, (t⁻¹ * ((d * d')⁻¹ * t * (d * d')))⁻¹ *
      (t⁻¹ * (d⁻¹ * t * d) * (t⁻¹ * (d'⁻¹ * t * d'))) ∈ U)
    (hker : ∀ d ∈ D, t⁻¹ * (d⁻¹ * t * d) ∈ U ↔ d ∈ B)
    (hsurj : ∀ a ∈ A, ∃ d ∈ D, (t⁻¹ * (d⁻¹ * t * d))⁻¹ * a ∈ U) :
    ∃ e : (↥D ⧸ B.subgroupOf D) ≃* (↥A ⧸ U.subgroupOf A),
      ∀ d : D, e d = ((⟨t⁻¹ * ((d : G)⁻¹ * t * d), hA d d.2⟩ : A) : ↥A ⧸ U.subgroupOf A) := by
  let θ : D →* ↥A ⧸ U.subgroupOf A :=
    { toFun := fun d => ((⟨t⁻¹ * ((d : G)⁻¹ * t * d), hA d d.2⟩ : A) : ↥A ⧸ U.subgroupOf A)
      map_one' := by
        rw [← QuotientGroup.mk_one]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun d d' => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        exact hmul d d.2 d' d'.2 }
  have hθker : θ.ker = B.subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hker d d.2]
    change ((⟨_, _⟩ : A) : ↥A ⧸ U.subgroupOf A) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hθsurj : Function.Surjective θ := fun q => by
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨d, hd, hda⟩ := hsurj a a.2
      exact ⟨⟨d, hd⟩, QuotientGroup.eq.mpr (mem_subgroupOf.mpr hda)⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj), fun d => rfl⟩

end Quotient

section Coord

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def coord (φ : L ≃* antiSp K) (t : G) (e : QGSpace K) : G :=
  t ^ e.1.val * ((φ.symm (aElt ![e.2.1, e.2.2.1] (e.2.2.2 + e.2.1 * e.2.2.1)) : L) : G)

variable (φ : L ≃* antiSp K) {t : G}

theorem zmod_two_cases (ε : ZMod 2) : ε = 0 ∨ ε = 1 := by
  revert ε
  decide

theorem pow_val_add (htt : t * t = 1) (ε ε' : ZMod 2) :
    t ^ (ε + ε').val = t ^ ε.val * t ^ ε'.val := by
  rcases zmod_two_cases ε with rfl | rfl <;> rcases zmod_two_cases ε' with rfl | rfl
  · simp
  · simp
  · simp
  · rw [zmod_two_one_add_one]
    simp [ZMod.val_one, htt]

theorem pow_val_mem_L_iff (htL : t ∉ L) (ε : ZMod 2) : t ^ ε.val ∈ L ↔ ε = 0 := by
  rcases zmod_two_cases ε with rfl | rfl
  · simp
  · simp only [ZMod.val_one, pow_one, one_ne_zero, iff_false]
    exact htL

theorem coord_add (htt : t * t = 1) (hc : ∀ x ∈ L, t * x = x * t) (e e' : QGSpace K) :
    coord φ t (e + e') = coord φ t e * coord φ t e' := by
  obtain ⟨ε, x, y, z⟩ := e
  obtain ⟨ε', x', y', z'⟩ := e'
  have hcomm : ∀ (j : ℕ) (w : antiSp K), t ^ j * ((φ.symm w : L) : G) =
      ((φ.symm w : L) : G) * t ^ j := fun j w =>
    (Commute.pow_left (hc _ (φ.symm w).2) j).eq
  simp only [coord, Prod.mk_add_mk]
  set A : G := ((φ.symm (aElt ![x, y] (z + x * y)) : L) : G) with hA
  set B : G := ((φ.symm (aElt ![x', y'] (z' + x' * y')) : L) : G) with hB
  have key : ((φ.symm (aElt ![x + x', y + y'] (z + z' + (x + x') * (y + y'))) : L) : G) =
      A * B := by
    rw [hA, hB, ← coe_mul, ← map_mul, aElt_mul]
    congr 3
    · ext i
      fin_cases i <;> simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
  rw [pow_val_add htt, key]
  have h1 : t ^ ε'.val * A = A * t ^ ε'.val := hcomm _ _
  calc t ^ ε.val * t ^ ε'.val * (A * B) = t ^ ε.val * (t ^ ε'.val * A) * B := by group
    _ = t ^ ε.val * (A * t ^ ε'.val) * B := by rw [h1]
    _ = t ^ ε.val * A * (t ^ ε'.val * B) := by group

theorem coord_zero : coord φ t 0 = 1 := by
  simp [coord, vec_zero_two, aElt_zero_zero]

theorem qg_add_self (e : QGSpace K) : e + e = 0 := by
  obtain ⟨ε, x, y, z⟩ := e
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rcases zmod_two_cases ε with rfl | rfl
    · rfl
    · exact zmod_two_one_add_one
  · exact CharTwo.add_self_eq_zero x
  · exact CharTwo.add_self_eq_zero y
  · exact CharTwo.add_self_eq_zero z

theorem vec_add_self (v : Fin 2 → K) : v + v = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (v i)

theorem aElt_eq_one_iff {v : Fin 2 → K} {c : K} : aElt v c = 1 ↔ v = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [← aElt_zero_zero, aElt, aElt] at h
    obtain ⟨h1, h0, hc, -⟩ := uElt_inj h
    refine ⟨?_, hc⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1
  · rintro ⟨rfl, rfl⟩
    exact aElt_zero_zero

theorem coord_eq_one_iff (htL : t ∉ L) {e : QGSpace K} : coord φ t e = 1 ↔ e = 0 := by
  constructor
  · intro h
    obtain ⟨ε, x, y, z⟩ := e
    simp only [coord] at h
    have hε : ε = 0 := (pow_val_mem_L_iff htL ε).mp (by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem (φ.symm _).2)
    subst hε
    simp only [ZMod.val_zero, pow_zero, one_mul] at h
    have h1 : aElt ![x, y] (z + x * y) = 1 :=
      φ.symm.map_eq_one_iff.mp (Subtype.ext h)
    obtain ⟨hv, hc⟩ := aElt_eq_one_iff.mp h1
    have hx : x = 0 := congrFun hv 0
    have hy : y = 0 := congrFun hv 1
    subst hx hy
    simp only [mul_zero, add_zero] at hc
    subst hc
    rfl
  · rintro rfl
    exact coord_zero φ

theorem coord_mul_self (htt : t * t = 1) (hc : ∀ x ∈ L, t * x = x * t) (e : QGSpace K) :
    coord φ t e * coord φ t e = 1 := by
  rw [← coord_add φ htt hc, qg_add_self, coord_zero]

theorem coord_injective (htt : t * t = 1) (hc : ∀ x ∈ L, t * x = x * t) (htL : t ∉ L) :
    Function.Injective (coord φ t) := by
  intro e e' h
  have h1 : coord φ t (e + e') = 1 := by
    rw [coord_add φ htt hc, h, coord_mul_self φ htt hc]
  have h2 := (coord_eq_one_iff φ htL).mp h1
  rw [add_eq_zero_iff_eq_neg] at h2
  rw [h2]
  exact neg_eq_of_add_eq_zero_right (qg_add_self e')

theorem coord_mem (e : QGSpace K) : coord φ t e ∈ zpowers t ⊔ pull φ (rootA K Axis.two) :=
  mul_mem (mem_sup_left (pow_mem (mem_zpowers t) _))
    (mem_sup_right (symm_mem_pull.mpr (aElt_mem_radA2 _ _)))

theorem exists_symm_aElt_eq {a : G} (ha : a ∈ pull φ (rootA K Axis.two)) :
    ∃ x y z : K, ((φ.symm (aElt ![x, y] (z + x * y)) : L) : G) = a := by
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp ha'
  refine ⟨v 0, v 1, c + v 0 * v 1, ?_⟩
  have hv : (![v 0, v 1] : Fin 2 → K) = v := by
    ext i
    fin_cases i <;> rfl
  rw [hv, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem exists_coord_eq (htt : t * t = 1) (hc : ∀ x ∈ L, t * x = x * t) {b : G}
    (hb : b ∈ zpowers t ⊔ pull φ (rootA K Axis.two)) : ∃ e, coord φ t e = b := by
  rcases (mem_zpowers_sup_iff htt fun w hw => hc w (pull_le φ _ hw)).mp hb with h | h
  · obtain ⟨x, y, z, hxyz⟩ := exists_symm_aElt_eq φ h
    refine ⟨(0, x, y, z), ?_⟩
    simp only [coord, ZMod.val_zero, pow_zero, one_mul]
    exact hxyz
  · obtain ⟨x, y, z, hxyz⟩ := exists_symm_aElt_eq φ h
    refine ⟨(1, x, y, z), ?_⟩
    simp only [coord, ZMod.val_one, pow_one]
    rw [hxyz, ← mul_assoc, htt, one_mul]

theorem coord_qgPoint (v : Fin 2 → K) :
    coord φ t (qgPoint v) = t * ((φ.symm (aElt v 0) : L) : G) := by
  have hv : (![v 0, v 1] : Fin 2 → K) = v := by
    ext i
    fin_cases i <;> rfl
  simp only [coord, qgPoint, ZMod.val_one, pow_one]
  rw [hv, CharTwo.add_self_eq_zero]

theorem coord_qgT : coord φ t (qgT K) = t := by
  rw [← qgPoint_zero, coord_qgPoint, aElt_zero_zero, map_one, coe_one, mul_one]

theorem coord_mem_A_iff (htL : t ∉ L) {e : QGSpace K} :
    coord φ t e ∈ pull φ (rootA K Axis.two) ↔ e ∈ qgW K := by
  obtain ⟨ε, x, y, z⟩ := e
  change _ ↔ ε = 0
  rw [← pow_val_mem_L_iff htL ε]
  constructor
  · intro h
    have h1 := mul_mem (pull_le φ _ h) (inv_mem (φ.symm (aElt ![x, y] (z + x * y))).2)
    simp only [coord, mul_inv_cancel_right] at h1
    exact h1
  · intro h
    rcases zmod_two_cases ε with rfl | rfl
    · simp only [coord, ZMod.val_zero, pow_zero, one_mul]
      exact symm_mem_pull.mpr (aElt_mem_radA2 _ _)
    · simp only [ZMod.val_one, pow_one] at h
      exact absurd h htL

theorem coord_mem_U_iff (htL : t ∉ L) {e : QGSpace K} :
    coord φ t e ∈ pull φ (rootU K Axis.two) ↔ e ∈ qgZ K := by
  constructor
  · intro h
    have hW := (coord_mem_A_iff φ htL).mp (pull_mono φ rootU₂_le_radA2 h)
    obtain ⟨ε, x, y, z⟩ := e
    change ε = 0 at hW
    subst hW
    simp only [coord, ZMod.val_zero, pow_zero, one_mul] at h
    obtain ⟨c, hc⟩ := symm_mem_pull.mp h
    obtain ⟨hy, hx, -, -⟩ := uElt_inj hc
    exact ⟨rfl, hx, hy⟩
  · intro h
    obtain ⟨ε, x, y, z⟩ := e
    obtain ⟨h1, h2, h3⟩ := h
    simp only at h1 h2 h3
    subst h1 h2 h3
    simp only [coord, ZMod.val_zero, pow_zero, one_mul]
    exact symm_mem_pull.mpr ⟨z + 0 * 0, rfl⟩

theorem coord_mem_omega_iff (htt : t * t = 1) (hc : ∀ x ∈ L, t * x = x * t) (htL : t ∉ L)
    {e : QGSpace K} :
    coord φ t e ∈ {x : G | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} ↔
      e ∈ qgOmega K := by
  constructor
  · rintro ⟨a, b, h⟩
    have h1 : coord φ t e = coord φ t (qgPoint ![b, a]) := by
      rw [h, coord_qgPoint]
      rfl
    rw [coord_injective φ htt hc htL h1]
    exact qgPoint_mem _
  · intro h
    obtain ⟨v, rfl⟩ := mem_qgOmega_iff_exists.mp h
    exact ⟨v 1, v 0, coord_qgPoint φ v⟩

end Coord

section Action

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  (φ : L ≃* antiSp K) {t : G}

local notation "𝐁" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
local notation "𝐍" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)

@[expose] noncomputable def conjFun (t g : G) (e : QGSpace K) : QGSpace K :=
  Function.invFun (coord φ t) (g * coord φ t e * g⁻¹)

theorem coord_conjFun (hS : TwoCoreSetup L K n t) {g : G} (hg : g ∈ 𝐍) (e : QGSpace K) :
    coord φ t (conjFun φ t g e) = g * coord φ t e * g⁻¹ :=
  Function.invFun_eq (exists_coord_eq φ hS.t_mul_t (fun _ hx => hS.comm hx)
    ((mem_normalizer_iff.mp hg _).mp (coord_mem φ e)))

theorem conjFun_mul (hS : TwoCoreSetup L K n t) {g g' : G} (hg : g ∈ 𝐍) (hg' : g' ∈ 𝐍)
    (e : QGSpace K) : conjFun φ t (g * g') e = conjFun φ t g (conjFun φ t g' e) := by
  apply coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem
  rw [coord_conjFun φ hS (mul_mem hg hg'), coord_conjFun φ hS hg, coord_conjFun φ hS hg']
  group

theorem conjFun_one (hS : TwoCoreSetup L K n t) (e : QGSpace K) : conjFun φ t 1 e = e := by
  apply coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem
  rw [coord_conjFun φ hS (one_mem _)]
  group

theorem conjFun_add (hS : TwoCoreSetup L K n t) {g : G} (hg : g ∈ 𝐍) (e e' : QGSpace K) :
    conjFun φ t g (e + e') = conjFun φ t g e + conjFun φ t g e' := by
  have hc : ∀ x ∈ L, t * x = x * t := fun _ hx => hS.comm hx
  apply coord_injective φ hS.t_mul_t hc hS.t_not_mem
  rw [coord_add φ hS.t_mul_t hc, coord_conjFun φ hS hg, coord_conjFun φ hS hg,
    coord_conjFun φ hS hg, coord_add φ hS.t_mul_t hc]
  group

@[expose] noncomputable def conjAut (hS : TwoCoreSetup L K n t) (g : 𝐍) :
    AddAut (QGSpace K) where
  toFun := conjFun φ t g
  invFun := conjFun φ t (g : G)⁻¹
  left_inv e := by
    rw [← conjFun_mul φ hS (inv_mem g.2) g.2, inv_mul_cancel, conjFun_one φ hS]
  right_inv e := by
    rw [← conjFun_mul φ hS g.2 (inv_mem g.2), mul_inv_cancel, conjFun_one φ hS]
  map_add' := conjFun_add φ hS g.2

@[expose] noncomputable def conjRep (hS : TwoCoreSetup L K n t) : 𝐍 →* QGAut K where
  toFun g := Multiplicative.ofAdd (conjAut φ hS g)
  map_one' := Multiplicative.toAdd.injective (AddEquiv.ext fun e => conjFun_one φ hS e)
  map_mul' g g' :=
    Multiplicative.toAdd.injective (AddEquiv.ext fun e => conjFun_mul φ hS g.2 g'.2 e)

theorem coord_toAdd_conjRep (hS : TwoCoreSetup L K n t) (g : 𝐍) (e : QGSpace K) :
    coord φ t (Multiplicative.toAdd (conjRep φ hS g) e) = g * coord φ t e * (g : G)⁻¹ :=
  coord_conjFun φ hS g.2 e

theorem toAdd_conjRep_eq_iff (hS : TwoCoreSetup L K n t) (g : 𝐍) {e e' : QGSpace K} :
    Multiplicative.toAdd (conjRep φ hS g) e = e' ↔ g * coord φ t e * (g : G)⁻¹ = coord φ t e' := by
  rw [← coord_toAdd_conjRep φ hS g e]
  exact (coord_injective φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem).eq_iff.symm

theorem conjRep_qgT_iff (hS : TwoCoreSetup L K n t) (g : 𝐍) :
    Multiplicative.toAdd (conjRep φ hS g) (qgT K) = qgT K ↔ (g : G) * t = t * g := by
  rw [toAdd_conjRep_eq_iff, coord_qgT]
  constructor
  · intro h
    calc (g : G) * t = (g * t * (g : G)⁻¹) * g := by group
      _ = t * g := by rw [h]
  · intro h
    rw [h, mul_inv_cancel_right]

theorem conjRep_eq_one_iff (hS : TwoCoreSetup L K n t) (g : 𝐍) :
    conjRep φ hS g = 1 ↔ (g : G) ∈ centralizer (𝐁 : Set G) := by
  have hc : ∀ x ∈ L, t * x = x * t := fun _ hx => hS.comm hx
  rw [mem_centralizer_iff]
  constructor
  · intro h b hb
    obtain ⟨e, rfl⟩ := exists_coord_eq φ hS.t_mul_t hc hb
    have h1 := coord_toAdd_conjRep φ hS g e
    rw [h] at h1
    change coord φ t e = _ at h1
    calc coord φ t e * g = (g * coord φ t e * (g : G)⁻¹) * g := by rw [← h1]
      _ = g * coord φ t e := by group
  · intro h
    apply Multiplicative.toAdd.injective
    refine AddEquiv.ext fun e => coord_injective φ hS.t_mul_t hc hS.t_not_mem ?_
    rw [coord_toAdd_conjRep]
    change _ = coord φ t e
    rw [← h _ (coord_mem φ e), mul_inv_cancel_right]

theorem conjRep_mem_qgStab [Finite K] (hS : TwoCoreSetup L K n t)
    (hfus : {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁} =
      {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)}) (g : 𝐍) :
    conjRep φ hS g ∈ qgStab K := by
  have hΩ : ∀ e, e ∈ qgOmega K ↔
      coord φ t e ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁} := fun e => by
    rw [hfus, coord_mem_omega_iff φ hS.t_mul_t (fun _ hx => hS.comm hx) hS.t_not_mem]
  refine mem_qgStab_of_mapsTo fun e he => ?_
  rw [hΩ] at he ⊢
  obtain ⟨⟨k, hk⟩, hB⟩ := he
  rw [coord_toAdd_conjRep]
  exact ⟨⟨k * (g : G)⁻¹, by rw [hk]; group⟩, (mem_normalizer_iff.mp g.2 _).mp hB⟩

theorem B_comm (hS : TwoCoreSetup L K n t) {x y : G} (hx : x ∈ 𝐁) (hy : y ∈ 𝐁) :
    x * y = y * x := by
  have hc : ∀ x ∈ L, t * x = x * t := fun _ hx => hS.comm hx
  obtain ⟨e, rfl⟩ := exists_coord_eq φ hS.t_mul_t hc hx
  obtain ⟨e', rfl⟩ := exists_coord_eq φ hS.t_mul_t hc hy
  rw [← coord_add φ hS.t_mul_t hc, ← coord_add φ hS.t_mul_t hc, add_comm]

theorem centralizer_B_eq [Finite K] (hS : TwoCoreSetup L K n t) :
    centralizer (𝐁 : Set G) = 𝐁 := by
  refine le_antisymm (fun g hg => ?_)
    fun b hb => mem_centralizer_iff.mpr fun x hx => B_comm φ hS hx hb
  have hV : zpowers t ⊔ pull φ (rootU K Axis.two) ≤ 𝐁 :=
    sup_le_sup_left (pull_mono φ rootU₂_le_radA2) _
  have hgK : g ∈ centralizer ((zpowers t ⊔ pull φ (rootU K Axis.two) : Subgroup G) : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.mpr hV) hg
  obtain ⟨τ, hτ, c, hc, rfl⟩ := (hS.mem_K_iff φ Axis.two).mp hgK
  obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
  obtain ⟨v, c₀, M, rfl⟩ := exists_aElt_mul_sElt hc'
  have key : ∀ w : Fin 2 → K, (M : Matrix (Fin 2) (Fin 2) K) *ᵥ w = w := by
    intro w
    have hw : ((φ.symm (aElt w 0) : L) : G) ∈ 𝐁 :=
      mem_sup_right (symm_mem_pull.mpr (aElt_mem_radA2 w 0))
    have h1 := mem_centralizer_iff.mp hg _ hw
    have hτw := hS.zpowers_comm hτ (φ.symm (aElt w 0)).2
    have h2 : ((φ.symm (aElt w 0) : L) : G) * ((φ.symm (aElt v c₀ * sElt M) : L) : G) =
        ((φ.symm (aElt v c₀ * sElt M) : L) : G) * ((φ.symm (aElt w 0) : L) : G) := by
      calc ((φ.symm (aElt w 0) : L) : G) * ((φ.symm (aElt v c₀ * sElt M) : L) : G)
          = τ⁻¹ * (τ * ((φ.symm (aElt w 0) : L) : G)) *
              ((φ.symm (aElt v c₀ * sElt M) : L) : G) := by group
        _ = τ⁻¹ * (((φ.symm (aElt w 0) : L) : G) *
              (τ * ((φ.symm (aElt v c₀ * sElt M) : L) : G))) := by rw [hτw]; group
        _ = τ⁻¹ * ((τ * ((φ.symm (aElt v c₀ * sElt M) : L) : G)) *
              ((φ.symm (aElt w 0) : L) : G)) := by rw [h1]
        _ = _ := by group
    have h3 : aElt w 0 * (aElt v c₀ * sElt M) = (aElt v c₀ * sElt M) * aElt w 0 := by
      apply φ.symm.injective
      apply Subtype.ext
      rw [map_mul φ.symm (aElt w 0) (aElt v c₀ * sElt M),
        map_mul φ.symm (aElt v c₀ * sElt M) (aElt w 0), coe_mul, coe_mul]
      exact h2
    have h4 : sElt M * aElt w 0 = aElt w 0 * sElt M := by
      have e1 : aElt w 0 * (aElt v c₀ * sElt M) = aElt v c₀ * (aElt w 0 * sElt M) := by
        rw [← mul_assoc, aElt_comm w v 0 c₀, mul_assoc]
      rw [e1, mul_assoc] at h3
      exact (mul_left_cancel h3).symm
    rw [sElt_mul_aElt] at h4
    have h5 := congrArg vecOf₂ (mul_right_cancel h4)
    rwa [vecOf₂_aElt, vecOf₂_aElt] at h5
  have hM : M = 1 := by
    have k0 := key ![1, 0]
    have k1 := key ![0, 1]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun k0 0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun k1 0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun k0 1
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun k1 1
  subst hM
  rw [sElt_one, mul_one]
  exact mul_mem (mem_sup_left hτ) (mem_sup_right (symm_mem_pull.mpr (aElt_mem_radA2 v c₀)))

theorem exists_lin [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (M : GL (Fin 2) K) :
    ∃ g ∈ 𝐍, g * t = t * g ∧ ∀ v, g * coord φ t (qgPoint v) * g⁻¹ =
      coord φ t (qgPoint ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  obtain ⟨y, hy⟩ := exists_sq_eq (M : Matrix (Fin 2) (Fin 2) K).det
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hy]
    ring
  set l : Kˣ := Units.mk0 y hy0
  let M' : SL₂ K := ⟨y⁻¹ • (M : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hy, inv_mul_cancel₀ hdet]⟩
  set g : G := ((φ.symm (dElt l * sElt M') : L) : G) with hg
  have hgL : g ∈ L := (φ.symm _).2
  have hgt : g * t = t * g := (hS.comm hgL).symm
  have hgN : g ∈ 𝐍 := by
    rw [hS.mem_normalizer_zpowers_sup_iff (hS.L_le hgL) (pull_le φ _)]
    exact symm_mem_normalizer_pull
      (mem_normalizer_radA2_iff.mpr ((firstCol_dElt l).mul (firstCol_sElt M')))
  refine ⟨g, hgN, hgt, fun v => ?_⟩
  have h1 : (dElt l * sElt M') * aElt v 0 * (dElt l * sElt M')⁻¹ =
      aElt ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0 := by
    have h := conj_aElt_normalForm 0 0 l M' v 0
    rw [aElt_zero_zero, one_mul] at h
    rw [h, mul_zero]
    congr 1
    change y • ((y⁻¹ • (M : Matrix (Fin 2) (Fin 2) K)) *ᵥ v) = _
    rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hy0, one_smul]
  rw [coord_qgPoint, coord_qgPoint]
  calc g * (t * ((φ.symm (aElt v 0) : L) : G)) * g⁻¹
      = (g * t) * ((φ.symm (aElt v 0) : L) : G) * g⁻¹ := by group
    _ = t * (g * ((φ.symm (aElt v 0) : L) : G) * g⁻¹) := by rw [hgt]; group
    _ = _ := by rw [hg, symm_conj_eq, h1]

theorem conjRep_lin [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (M : GL (Fin 2) K) :
    ∃ h ∈ (conjRep φ hS).range, Multiplicative.toAdd h (qgT K) = qgT K ∧
      ∀ v, Multiplicative.toAdd h (qgPoint v) = qgPoint ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
  obtain ⟨g, hg, hgt, hgv⟩ := exists_lin φ hS M
  exact ⟨conjRep φ hS ⟨g, hg⟩, ⟨_, rfl⟩, (conjRep_qgT_iff φ hS _).mpr hgt,
    fun v => (toAdd_conjRep_eq_iff φ hS _).mpr (hgv v)⟩

theorem conjRep_transitive [Finite G] [Finite K] (hS : TwoCoreSetup L K n t)
    (hfus : {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁} =
      {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)})
    (hmove : ∃ g ∈ 𝐍, g * t ≠ t * g) :
    ∀ e ∈ qgOmega K, ∀ e' ∈ qgOmega K,
      ∃ h ∈ (conjRep φ hS).range, Multiplicative.toAdd h e = e' := by
  obtain ⟨g, hg, hgt⟩ := hmove
  have hρg := conjRep_mem_qgStab φ hS hfus ⟨g, hg⟩
  set v₀ := qgInduced (conjRep φ hS ⟨g, hg⟩) 0 with hv₀def
  have hv₀ : Multiplicative.toAdd (conjRep φ hS ⟨g, hg⟩) (qgT K) = qgPoint v₀ := by
    rw [← qgPoint_zero, hv₀def, qgPoint_qgInduced hρg]
  have hv₀0 : v₀ ≠ 0 := by
    intro h0
    apply hgt
    rw [← conjRep_qgT_iff φ hS ⟨g, hg⟩, hv₀, h0, qgPoint_zero]
  have step : ∀ w, ∃ h ∈ (conjRep φ hS).range,
      Multiplicative.toAdd h (qgT K) = qgPoint w := by
    intro w
    by_cases hw : w = 0
    · exact ⟨1, one_mem _, by rw [hw, qgPoint_zero]; rfl⟩
    · obtain ⟨C, hC⟩ := exists_GL_mulVec_eq hv₀0 hw
      obtain ⟨g', hg', -, hg'v⟩ := exists_lin φ hS C
      refine ⟨conjRep φ hS ⟨g', hg'⟩ * conjRep φ hS ⟨g, hg⟩, mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
      change Multiplicative.toAdd (conjRep φ hS ⟨g', hg'⟩)
        (Multiplicative.toAdd (conjRep φ hS ⟨g, hg⟩) (qgT K)) = qgPoint w
      rw [hv₀, toAdd_conjRep_eq_iff, hg'v, hC]
  intro e he e' he'
  obtain ⟨v, rfl⟩ := mem_qgOmega_iff_exists.mp he
  obtain ⟨w, rfl⟩ := mem_qgOmega_iff_exists.mp he'
  obtain ⟨h₁, hh₁, h1⟩ := step v
  obtain ⟨h₂, hh₂, h2⟩ := step w
  refine ⟨h₂ * h₁⁻¹, mul_mem hh₂ (inv_mem hh₁), ?_⟩
  change Multiplicative.toAdd h₂ (Multiplicative.toAdd h₁⁻¹ (qgPoint v)) = qgPoint w
  have hinv : Multiplicative.toAdd h₁⁻¹ (Multiplicative.toAdd h₁ (qgT K)) = qgT K :=
    AddAut.neg_apply_self _ _ _
  rw [← h1, hinv, h2]

end Action

structure SecondHyp {G : Type*} [Group G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2]
    (n : ℕ) (φ : L ≃* antiSp K) (t : G) : Prop where
  two : TwoCoreSetup L K n t
  fus : {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ zpowers t ⊔ pull φ (rootA K Axis.two)} =
    {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)}
  move : ∃ g ∈ normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G),
    g * t ≠ t * g

namespace SecondHyp

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀" => pull φ (rootA K Axis.two)
local notation "𝐔" => pull φ (rootU K Axis.two)
local notation "𝐁" => (zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G)
local notation "𝐍" => normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem comm (h : SecondHyp L K n φ t) : ∀ x ∈ L, t * x = x * t := fun _ hx => h.two.comm hx

theorem range_le [Finite K] (h : SecondHyp L K n φ t) : (conjRep φ h.two).range ≤ qgStab K := by
  rintro _ ⟨g, rfl⟩
  exact conjRep_mem_qgStab φ h.two h.fus g

theorem qg_transl [Finite G] [Finite K] (h : SecondHyp L K n φ t) :
    (∀ x ∈ CFSG.pCore 2 (conjRep φ h.two).range, ∃ u : Fin 2 → K, ∀ v,
      Multiplicative.toAdd (x : QGAut K) (qgPoint v) = qgPoint (v + u)) ∧
    ∀ u : Fin 2 → K, ∃ x ∈ CFSG.pCore 2 (conjRep φ h.two).range, ∀ v,
      Multiplicative.toAdd (x : QGAut K) (qgPoint v) = qgPoint (v + u) := by
  obtain ⟨-, -, -, -, -, -, hH⟩ :=
    characteristic_two_quadratic_graph_affine_semilinear_translations K
  obtain ⟨h1, h2, -⟩ := hH _ h.range_le (conjRep_transitive φ h.two h.fus h.move)
    (conjRep_lin φ h.two)
  exact ⟨h1, h2⟩

theorem B_le_N : 𝐁 ≤ 𝐍 := le_normalizer

theorem t_mem_B : t ∈ 𝐁 := mem_sup_left (mem_zpowers t)

theorem B_le_C (h : SecondHyp L K n φ t) : 𝐁 ≤ 𝐂 := fun _ hb =>
  mem_centralizer_singleton_iff.mpr (B_comm φ h.two hb t_mem_B)

theorem isPGroup_B [Finite K] (h : SecondHyp L K n φ t) : IsPGroup 2 𝐁 :=
  TwoCoreSetup.isPGroup_B φ Axis.two h.two

theorem pCore_eq [Finite K] (h : SecondHyp L K n φ t) :
    𝐃 = ((CFSG.pCore 2 (conjRep φ h.two).range).comap
      (conjRep φ h.two).rangeRestrict).map 𝐍.subtype := by
  apply pCore_map_eq (map_subtype_le _)
  · rintro g hg _ ⟨s, hs, rfl⟩
    refine ⟨⟨g, hg⟩ * s * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact CFSG.pCore_normal.conj_mem _ hs _
  · rintro ⟨_, s, hs, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) ⟨_, hs⟩
    have hk1 : (conjRep φ h.two) (s ^ 2 ^ k) = 1 := by
      have h1 := congrArg (fun x => ((x : (conjRep φ h.two).range) : QGAut K))
        (congrArg Subtype.val hk)
      simpa [map_pow] using h1
    have hB : ((s ^ 2 ^ k : 𝐍) : G) ∈ 𝐁 :=
      (centralizer_B_eq φ h.two).le ((conjRep_eq_one_iff φ h.two _).mp hk1)
    obtain ⟨m, hm⟩ := h.isPGroup_B ⟨_, hB⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hm' ⊢
    rw [pow_add, pow_mul]
    exact hm'
  · intro R hRN hRn hR2
    have hn : (R.subgroupOf 𝐍).Normal := ⟨fun x hx g => mem_subgroupOf.mpr
      (hRn g g.2 x (mem_subgroupOf.mp hx))⟩
    have hR' : (R.subgroupOf 𝐍).map (conjRep φ h.two).rangeRestrict ≤
        CFSG.pCore 2 (conjRep φ h.two).range :=
      le_sSup ⟨hn.map _ (conjRep φ h.two).rangeRestrict_surjective,
        (hR2.of_equiv (subgroupOfEquivOfLe hRN).symm).map _⟩
    intro r hr
    exact ⟨⟨r, hRN hr⟩, hR' ⟨⟨r, hRN hr⟩, mem_subgroupOf.mpr hr, rfl⟩, rfl⟩

theorem mem_D_iff [Finite K] (h : SecondHyp L K n φ t) {d : G} :
    d ∈ 𝐃 ↔ ∃ hd : d ∈ 𝐍, (conjRep φ h.two).rangeRestrict ⟨d, hd⟩ ∈
      CFSG.pCore 2 (conjRep φ h.two).range := by
  rw [h.pCore_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hd, hs⟩
    exact ⟨⟨d, hd⟩, hs, rfl⟩

theorem D_le_N : 𝐃 ≤ 𝐍 := map_subtype_le _

theorem D_transl [Finite G] [Finite K] (h : SecondHyp L K n φ t) {d : G} (hd : d ∈ 𝐃) :
    ∃ u : Fin 2 → K, ∀ v, d * coord φ t (qgPoint v) * d⁻¹ = coord φ t (qgPoint (v + u)) := by
  obtain ⟨hdN, hdP⟩ := h.mem_D_iff.mp hd
  obtain ⟨u, hu⟩ := h.qg_transl.1 _ hdP
  exact ⟨u, fun v => (toAdd_conjRep_eq_iff φ h.two ⟨d, hdN⟩).mp (hu v)⟩

theorem exists_D_transl [Finite G] [Finite K] (h : SecondHyp L K n φ t) (u : Fin 2 → K) :
    ∃ d ∈ 𝐃, ∀ v, d * coord φ t (qgPoint v) * d⁻¹ = coord φ t (qgPoint (v + u)) := by
  obtain ⟨x, hx, hxu⟩ := h.qg_transl.2 u
  obtain ⟨m, hm⟩ := (conjRep φ h.two).rangeRestrict_surjective x
  refine ⟨m, h.mem_D_iff.mpr ⟨m.2, ?_⟩, fun v => ?_⟩
  · change (conjRep φ h.two).rangeRestrict m ∈ _
    rw [hm]
    exact hx
  · apply (toAdd_conjRep_eq_iff φ h.two m).mp
    rw [← hxu v, ← hm]
    rfl

theorem conj_t_eq [Finite G] [Finite K] (h : SecondHyp L K n φ t) {d : G} (hd : d ∈ 𝐃) :
    ∃ u : Fin 2 → K, d⁻¹ * t * d = t * ((φ.symm (aElt u 0) : L) : G) ∧
      ∀ v, d⁻¹ * coord φ t (qgPoint v) * d = coord φ t (qgPoint (v + u)) := by
  obtain ⟨u, hu⟩ := h.D_transl (inv_mem hd)
  refine ⟨u, ?_, fun v => by simpa using hu v⟩
  have h1 := hu 0
  rw [qgPoint_zero, coord_qgT, inv_inv, zero_add, coord_qgPoint] at h1
  exact h1

theorem mem_fus_iff (h : SecondHyp L K n φ t) {x : G} :
    x ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁} ↔ ∃ v, x = coord φ t (qgPoint v) := by
  rw [h.fus]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨![b, a], by rw [coord_qgPoint]; rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, coord_qgPoint φ v⟩

theorem mem_B_of_fix [Finite K] (h : SecondHyp L K n φ t) {g : G} (hg : g ∈ 𝐍)
    (hfix : ∀ v, g * coord φ t (qgPoint v) * g⁻¹ = coord φ t (qgPoint v)) : g ∈ 𝐁 := by
  have hρ := conjRep_mem_qgStab φ h.two h.fus ⟨g, hg⟩
  have h1 : conjRep φ h.two ⟨g, hg⟩ = 1 := eq_one_of_qgInduced hρ fun v => qgPoint_injective (by
    rw [qgPoint_qgInduced hρ]
    exact (toAdd_conjRep_eq_iff φ h.two ⟨g, hg⟩).mpr (hfix v))
  exact (centralizer_B_eq φ h.two).le ((conjRep_eq_one_iff φ h.two _).mp h1)

theorem B_le_D [Finite K] (h : SecondHyp L K n φ t) : 𝐁 ≤ 𝐃 := by
  intro b hb
  refine h.mem_D_iff.mpr ⟨B_le_N hb, ?_⟩
  have h1 : conjRep φ h.two ⟨b, B_le_N hb⟩ = 1 :=
    (conjRep_eq_one_iff φ h.two _).mpr (mem_centralizer_iff.mpr fun x hx => B_comm φ h.two hx hb)
  have h2 : (conjRep φ h.two).rangeRestrict ⟨b, B_le_N hb⟩ = 1 := Subtype.ext h1
  rw [h2]
  exact one_mem _

theorem conj_mem_A [Finite K] (h : SecondHyp L K n φ t) {g : G} (hg : g ∈ 𝐍) {a : G}
    (ha : a ∈ 𝐀) : g * a * g⁻¹ ∈ 𝐀 := by
  obtain ⟨e, rfl⟩ := exists_coord_eq φ h.two.t_mul_t h.comm (mem_sup_right ha : a ∈ 𝐁)
  have he := (coord_mem_A_iff φ h.two.t_not_mem).mp ha
  rw [show g * coord φ t e * g⁻¹ = coord φ t (Multiplicative.toAdd (conjRep φ h.two ⟨g, hg⟩) e)
    from (coord_toAdd_conjRep φ h.two ⟨g, hg⟩ e).symm]
  exact (coord_mem_A_iff φ h.two.t_not_mem).mpr
    (toAdd_mem_qgW (conjRep_mem_qgStab φ h.two h.fus _) he)

theorem conj_mem_U [Finite K] (h : SecondHyp L K n φ t) {g : G} (hg : g ∈ 𝐍) {u : G}
    (hu : u ∈ 𝐔) : g * u * g⁻¹ ∈ 𝐔 := by
  have huB : u ∈ 𝐁 := mem_sup_right (pull_mono φ rootU₂_le_radA2 hu)
  obtain ⟨e, rfl⟩ := exists_coord_eq φ h.two.t_mul_t h.comm huB
  have he := (coord_mem_U_iff φ h.two.t_not_mem).mp hu
  rw [show g * coord φ t e * g⁻¹ = coord φ t (Multiplicative.toAdd (conjRep φ h.two ⟨g, hg⟩) e)
    from (coord_toAdd_conjRep φ h.two ⟨g, hg⟩ e).symm]
  exact (coord_mem_U_iff φ h.two.t_not_mem).mpr
    (toAdd_mem_qgZ (conjRep_mem_qgStab φ h.two h.fus _) he)

theorem orbit_eq [Finite G] [Finite K] (h : SecondHyp L K n φ t) :
    {x : G | ∃ m ∈ 𝐍, x = m⁻¹ * t * m} = {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁} := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, rfl⟩, (mem_normalizer_iff''.mp hm t).mp t_mem_B⟩
  · intro hx
    obtain ⟨v, rfl⟩ := h.mem_fus_iff.mp hx
    obtain ⟨d, hd, hdv⟩ := h.exists_D_transl v
    refine ⟨d⁻¹, inv_mem (D_le_N hd), ?_⟩
    have h1 := hdv 0
    rw [qgPoint_zero, coord_qgT, zero_add] at h1
    rw [inv_inv, h1]

theorem mul_eq [Finite G] [Finite K] (h : SecondHyp L K n φ t) :
    (𝐃 : Set G) * ((𝐂 ⊓ 𝐍 : Subgroup G) : Set G) = 𝐍 := by
  ext m
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨d, hd, c, hc, rfl⟩
    exact mul_mem (D_le_N hd) hc.2
  · intro hm
    have hx : m * t * m⁻¹ ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁} :=
      ⟨⟨m⁻¹, by group⟩, (mem_normalizer_iff.mp hm t).mp t_mem_B⟩
    obtain ⟨u, hu⟩ := h.mem_fus_iff.mp hx
    obtain ⟨d, hd, hdu⟩ := h.exists_D_transl u
    have hdt : d * t * d⁻¹ = m * t * m⁻¹ := by
      have h1 := hdu 0
      rw [qgPoint_zero, coord_qgT, zero_add] at h1
      rw [h1, hu]
    refine ⟨d, hd, d⁻¹ * m, mem_inf.mpr ⟨?_, mul_mem (inv_mem (D_le_N hd)) hm⟩, by group⟩
    rw [mem_centralizer_singleton_iff]
    calc d⁻¹ * m * t = d⁻¹ * (m * t * m⁻¹) * m := by group
      _ = d⁻¹ * (d * t * d⁻¹) * m := by rw [hdt]
      _ = t * (d⁻¹ * m) := by group

theorem inf_eq [Finite G] [Finite K] (h : SecondHyp L K n φ t) : 𝐃 ⊓ (𝐂 ⊓ 𝐍) = 𝐁 := by
  apply le_antisymm
  · rintro d ⟨hd, hdC, hdN⟩
    obtain ⟨u, hu⟩ := h.D_transl hd
    have hu0 : u = 0 := by
      have h1 := hu 0
      rw [qgPoint_zero, coord_qgT, zero_add, mem_centralizer_singleton_iff.mp hdC,
        mul_inv_cancel_right] at h1
      have h2 : coord φ t (qgPoint 0) = coord φ t (qgPoint u) := by
        rw [qgPoint_zero, coord_qgT]
        exact h1
      exact (qgPoint_injective (coord_injective φ h.two.t_mul_t h.comm h.two.t_not_mem h2)).symm
    exact h.mem_B_of_fix hdN fun v => by rw [hu v, hu0, add_zero]
  · intro b hb
    exact ⟨h.B_le_D hb, h.B_le_C hb, B_le_N hb⟩

theorem symm_inv_mul_mem (v : Fin 2 → K) (c c' : K) :
    ((φ.symm (aElt v c) : L) : G)⁻¹ * ((φ.symm (aElt v c') : L) : G) ∈ 𝐔 := by
  rw [← coe_inv, ← map_inv, ← coe_mul, ← map_mul, aElt_inv, aElt_mul, vec_add_self]
  exact symm_mem_pull.mpr (aElt_zero_mem_rootU₂ _)

theorem vec_conj [Finite G] [Finite K] (h : SecondHyp L K n φ t) {d : G} (hd : d ∈ 𝐃) :
    ∃ u : Fin 2 → K, t⁻¹ * (d⁻¹ * t * d) = ((φ.symm (aElt u 0) : L) : G) ∧
      ∀ v, d⁻¹ * coord φ t (qgPoint v) * d = coord φ t (qgPoint (v + u)) := by
  obtain ⟨u, hu, hv⟩ := h.conj_t_eq hd
  exact ⟨u, by rw [hu, inv_mul_cancel_left], hv⟩

theorem normal_U_A (h : SecondHyp L K n φ t) : ((𝐔).subgroupOf 𝐀).Normal :=
  ⟨fun u hu a => by
    rw [mem_subgroupOf] at hu ⊢
    have hc := B_comm φ h.two (mem_sup_right a.2 : (a : G) ∈ 𝐁)
      (mem_sup_right (pull_mono φ rootU₂_le_radA2 hu))
    rw [coe_mul, coe_mul, coe_inv, hc, mul_inv_cancel_right]
    exact hu⟩

theorem normal_B_D : (𝐁.subgroupOf 𝐃).Normal :=
  ⟨fun b hb d => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (D_le_N d.2) b).mp (mem_subgroupOf.mp hb))⟩

theorem card_quot [Finite K] [((𝐔).subgroupOf 𝐀).Normal] :
    Nat.card (↥𝐀 ⧸ (𝐔).subgroupOf 𝐀) = Nat.card K ^ 2 := by
  let f : (Fin 2 → K) → ↥𝐀 ⧸ (𝐔).subgroupOf 𝐀 := fun v =>
    ((⟨_, symm_mem_pull.mpr (aElt_mem_radA2 v 0)⟩ : 𝐀) : ↥𝐀 ⧸ (𝐔).subgroupOf 𝐀)
  have hbij : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun q => ?_⟩
    · have h1 := mem_subgroupOf.mp (QuotientGroup.eq.mp hvw)
      simp only [coe_mul, coe_inv] at h1
      rw [← coe_inv, ← map_inv, ← coe_mul, ← map_mul, symm_mem_pull, aElt_inv, aElt_mul] at h1
      have h2 := (vecOf₂_eq_zero_iff (aElt_mem_radA2 _ _)).mpr h1
      rw [vecOf₂_aElt] at h2
      rw [← sub_eq_zero, sub_eq_add_neg, ← h2, add_right_inj, neg_eq_of_add_eq_zero_right]
      exact vec_add_self w
    · induction q using QuotientGroup.induction_on with
      | H a =>
        obtain ⟨a', ha', ha⟩ := exists_eq_symm_of_mem_pull a.2
        obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp ha'
        refine ⟨v, QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)⟩
        simp only [coe_mul, coe_inv]
        rw [← ha]
        exact symm_inv_mul_mem v 0 c
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_fun, Nat.card_fin]

theorem exists_mulEquiv [Finite G] [Finite K] (h : SecondHyp L K n φ t) :
    ∃ _ : (𝐁.subgroupOf 𝐃).Normal, ∃ _ : ((𝐔).subgroupOf 𝐀).Normal,
    ∃ e : (↥𝐃 ⧸ 𝐁.subgroupOf 𝐃) ≃* (↥𝐀 ⧸ (𝐔).subgroupOf 𝐀),
      (∀ d : 𝐃, ∃ a : 𝐀, (a : G) = t⁻¹ * ((d : G)⁻¹ * t * d) ∧ e d = a) ∧
      (∀ g ∈ 𝐂 ⊓ 𝐍, ∀ d : 𝐃, ∀ a : 𝐀, e d = a → ∃ d' : 𝐃, ∃ a' : 𝐀,
        (d' : G) = g⁻¹ * d * g ∧ (a' : G) = g⁻¹ * a * g ∧ e d' = a') ∧
      Nat.card (↥𝐃 ⧸ 𝐁.subgroupOf 𝐃) = Nat.card K ^ 2 ∧
      IsElementaryAbelian 2 (↥𝐃 ⧸ 𝐁.subgroupOf 𝐃) := by
  have := normal_B_D (φ := φ) (t := t)
  have := h.normal_U_A
  have hA : ∀ d ∈ 𝐃, t⁻¹ * (d⁻¹ * t * d) ∈ 𝐀 := fun d hd => by
    obtain ⟨u, hu, -⟩ := h.vec_conj hd
    rw [hu]
    exact symm_mem_pull.mpr (aElt_mem_radA2 u 0)
  have hmul : ∀ d ∈ 𝐃, ∀ d' ∈ 𝐃, (t⁻¹ * ((d * d')⁻¹ * t * (d * d')))⁻¹ *
      (t⁻¹ * (d⁻¹ * t * d) * (t⁻¹ * (d'⁻¹ * t * d'))) ∈ 𝐔 := by
    intro d hd d' hd'
    obtain ⟨u, hu, hu'⟩ := h.vec_conj hd
    obtain ⟨u', hv, hv'⟩ := h.vec_conj hd'
    have h1 : t⁻¹ * ((d * d')⁻¹ * t * (d * d')) = ((φ.symm (aElt (u + u') 0) : L) : G) := by
      have e1 := hu' 0
      rw [qgPoint_zero, coord_qgT, zero_add] at e1
      have e2 : (d * d')⁻¹ * t * (d * d') = d'⁻¹ * (d⁻¹ * t * d) * d' := by group
      rw [e2, e1, hv', coord_qgPoint, inv_mul_cancel_left]
    rw [h1, hu, hv, ← coe_mul, ← map_mul, aElt_mul, zero_add, zero_add]
    exact symm_inv_mul_mem _ _ _
  have hker : ∀ d ∈ 𝐃, t⁻¹ * (d⁻¹ * t * d) ∈ 𝐔 ↔ d ∈ 𝐁 := by
    intro d hd
    obtain ⟨u, hu, -⟩ := h.vec_conj hd
    rw [hu, symm_mem_pull]
    have hU : aElt u 0 ∈ rootU K Axis.two ↔ u = 0 := by
      change aElt u 0 ∈ rootU₂ K ↔ u = 0
      rw [← vecOf₂_eq_zero_iff (aElt_mem_radA2 u 0), vecOf₂_aElt]
    rw [hU]
    constructor
    · rintro rfl
      rw [← h.inf_eq]
      refine ⟨hd, mem_inf.mpr ⟨?_, D_le_N hd⟩⟩
      rw [aElt_zero_zero, map_one, coe_one] at hu
      have hu2 : d⁻¹ * t * d = t := (inv_mul_eq_one.mp hu).symm
      rw [mem_centralizer_singleton_iff]
      calc d * t = d * (d⁻¹ * t * d) := by rw [hu2]
        _ = t * d := by group
    · intro hb
      have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp (h.B_le_C hb)
      have h1 : ((φ.symm (aElt u 0) : L) : G) = 1 := by
        rw [← hu, mul_assoc d⁻¹, ← hdt, inv_mul_cancel_left, inv_mul_cancel]
      exact (aElt_eq_one_iff.mp (φ.symm.map_eq_one_iff.mp (Subtype.ext h1))).1
  have hsurj : ∀ a ∈ 𝐀, ∃ d ∈ 𝐃, (t⁻¹ * (d⁻¹ * t * d))⁻¹ * a ∈ 𝐔 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
    obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp ha'
    obtain ⟨m, hm, hmv⟩ := h.exists_D_transl v
    refine ⟨m⁻¹, inv_mem hm, ?_⟩
    have h1 := hmv 0
    rw [qgPoint_zero, coord_qgT, zero_add, coord_qgPoint] at h1
    rw [inv_inv, h1, inv_mul_cancel_left]
    exact symm_inv_mul_mem v 0 c
  obtain ⟨e, he⟩ := exists_quotient_mulEquiv_quotient hA hmul hker hsurj
  have hcomm : ∀ x y : ↥𝐀 ⧸ (𝐔).subgroupOf 𝐀, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext (B_comm φ h.two (mem_sup_right a.2) (mem_sup_right b.2)))
  have hsq : ∀ x : ↥𝐀 ⧸ (𝐔).subgroupOf 𝐀, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
      refine congrArg _ (Subtype.ext ?_)
      obtain ⟨e', he'⟩ := exists_coord_eq φ h.two.t_mul_t h.comm (mem_sup_right a.2 : (a : G) ∈ 𝐁)
      rw [SubgroupClass.coe_pow, pow_two, ← he', coord_mul_self φ h.two.t_mul_t h.comm, coe_one]
  refine ⟨inferInstance, inferInstance, e, fun d => ⟨_, rfl, he d⟩, ?_, ?_, ?_⟩
  · rintro g ⟨hgC, hgN⟩ d a hda
    have hgt : g * t = t * g := mem_centralizer_singleton_iff.mp hgC
    have hd' : g⁻¹ * d * g ∈ 𝐃 := by
      obtain ⟨p, hp, hpd⟩ := d.2
      refine ⟨⟨g, hgN⟩⁻¹ * p * ⟨g, hgN⟩, ?_, by rw [← hpd]; rfl⟩
      simpa using CFSG.pCore_normal.conj_mem p hp ⟨g, hgN⟩⁻¹
    have ha' : g⁻¹ * a * g ∈ 𝐀 := by
      simpa using h.conj_mem_A (inv_mem hgN) a.2
    refine ⟨⟨_, hd'⟩, ⟨_, ha'⟩, rfl, rfl, ?_⟩
    rw [he] at hda ⊢
    have h1 := mem_subgroupOf.mp (QuotientGroup.eq.mp hda)
    simp only [coe_mul, coe_inv] at h1
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)
    simp only [coe_mul, coe_inv]
    have h2 := h.conj_mem_U (inv_mem hgN) h1
    have hgt' : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgt]
        _ = t * g⁻¹ := by group
    have e2 : (t⁻¹ * ((g⁻¹ * d * g)⁻¹ * t * (g⁻¹ * d * g)))⁻¹ * (g⁻¹ * a * g) =
        g⁻¹ * ((t⁻¹ * ((d : G)⁻¹ * t * d))⁻¹ * a) * g⁻¹⁻¹ := by
      have e3 : (g⁻¹ * d * g)⁻¹ * t * (g⁻¹ * d * g) = g⁻¹ * ((d : G)⁻¹ * t * d) * g := by
        calc (g⁻¹ * d * g)⁻¹ * t * (g⁻¹ * d * g) = g⁻¹ * (d : G)⁻¹ * (g * t * g⁻¹) * d * g := by
              group
          _ = g⁻¹ * ((d : G)⁻¹ * t * d) * g := by rw [hgt, mul_inv_cancel_right]; group
      rw [e3]
      calc (t⁻¹ * (g⁻¹ * ((d : G)⁻¹ * t * d) * g))⁻¹ * (g⁻¹ * a * g)
          = (g⁻¹ * ((d : G)⁻¹ * t * d) * g)⁻¹ * (t * (g⁻¹ * a * g)) := by group
        _ = (g⁻¹ * ((d : G)⁻¹ * t * d) * g)⁻¹ * ((t * g⁻¹) * a * g) := by group
        _ = (g⁻¹ * ((d : G)⁻¹ * t * d) * g)⁻¹ * ((g⁻¹ * t) * a * g) := by rw [hgt']
        _ = _ := by group
    rw [e2]
    exact h2
  · exact (Nat.card_congr e.toEquiv).trans card_quot
  · refine { is_comm := ⟨fun a b => e.injective ?_⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => e.injective ?_ }
    · rw [map_mul, map_mul]
      exact hcomm _ _
    · rw [map_pow, map_one]
      exact hsq _

theorem transitive_D [Finite G] [Finite K] (h : SecondHyp L K n φ t) :
    ∀ x ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁},
      ∀ y ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁}, ∃ d ∈ 𝐃, d⁻¹ * x * d = y := by
  intro x hx y hy
  obtain ⟨v, rfl⟩ := h.mem_fus_iff.mp hx
  obtain ⟨w, rfl⟩ := h.mem_fus_iff.mp hy
  obtain ⟨m, hm, hmv⟩ := h.exists_D_transl (v + w)
  refine ⟨m⁻¹, inv_mem hm, ?_⟩
  rw [inv_inv, hmv, ← add_assoc, vec_add_self, zero_add]

theorem free_D [Finite G] [Finite K] (h : SecondHyp L K n φ t) :
    ∀ x ∈ {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ 𝐁}, ∀ d d' : 𝐃,
      (d : G)⁻¹ * x * d = (d' : G)⁻¹ * x * d' → (d : ↥𝐃 ⧸ 𝐁.subgroupOf 𝐃) = d' := by
  intro x hx d d' hdd'
  obtain ⟨v, rfl⟩ := h.mem_fus_iff.mp hx
  have hk : (d' : G) * (d : G)⁻¹ ∈ 𝐃 := mul_mem d'.2 (inv_mem d.2)
  have hkx : ((d' : G) * (d : G)⁻¹)⁻¹ * coord φ t (qgPoint v) * ((d' : G) * (d : G)⁻¹) =
      coord φ t (qgPoint v) := by
    calc ((d' : G) * (d : G)⁻¹)⁻¹ * coord φ t (qgPoint v) * ((d' : G) * (d : G)⁻¹)
        = d * ((d' : G)⁻¹ * coord φ t (qgPoint v) * d') * (d : G)⁻¹ := by group
      _ = d * ((d : G)⁻¹ * coord φ t (qgPoint v) * d) * (d : G)⁻¹ := by rw [hdd']
      _ = coord φ t (qgPoint v) := by group
  obtain ⟨u, -, hu⟩ := h.conj_t_eq hk
  have hu0 : u = 0 := by
    have h1 := hu v
    rw [hkx] at h1
    have h2 := qgPoint_injective (coord_injective φ h.two.t_mul_t h.comm h.two.t_not_mem h1)
    have h3 : v + u = v + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel h3
  have hkB : ((d' : G) * (d : G)⁻¹)⁻¹ ∈ 𝐁 := h.mem_B_of_fix (inv_mem (D_le_N hk)) fun w => by
    rw [inv_inv, hu w, hu0, add_zero]
  have hkB' : (d' : G) * (d : G)⁻¹ ∈ 𝐁 := by simpa using inv_mem hkB
  have h1 := (mem_normalizer_iff''.mp (D_le_N d.2) _).mp hkB'
  rw [QuotientGroup.eq, mem_subgroupOf]
  simp only [coe_mul, coe_inv]
  convert h1 using 1
  group

end SecondHyp

end OneAxisSecond

open Subgroup GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_one_axis_second_radical_two_core
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let C := centralizer ({(t : G)} : Set G)
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype
    let A₂ := ((rootA K Axis.two).comap φ.toMonoidHom).map L.subtype
    let B₂ := zpowers (t : G) ⊔ A₂
    let N₂ := normalizer (B₂ : Set G)
    let D₂ := (CFSG.pCore 2 N₂).map N₂.subtype
    let Ω := {x : G | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ B₂}
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
      centralizer (B₂ : Set G) = B₂ ∧
      (A₂ ≤ N₂ ∧ (A₂.subgroupOf N₂).Normal) ∧ (U₂ ≤ N₂ ∧ (U₂.subgroupOf N₂).Normal) ∧
      {x : G | ∃ m ∈ N₂, x = m⁻¹ * t * m} = Ω ∧
      Ω = {x | ∃ a b : K, x = t * ((φ.symm (uElt a b 0 0) : L) : G)} ∧
      (D₂ : Set G) * ((C ⊓ N₂ : Subgroup G) : Set G) = N₂ ∧
      D₂ ⊓ (C ⊓ N₂) = B₂ ∧
      ∃ _ : (B₂.subgroupOf D₂).Normal, ∃ _ : (U₂.subgroupOf A₂).Normal,
      ∃ e : (↥D₂ ⧸ B₂.subgroupOf D₂) ≃* (↥A₂ ⧸ U₂.subgroupOf A₂),
        (∀ d : D₂, ∃ a : A₂, (a : G) = (t : G)⁻¹ * ((d : G)⁻¹ * t * d) ∧ e d = a) ∧
        (∀ h ∈ C ⊓ N₂, ∀ d : D₂, ∀ a : A₂, e d = a → ∃ d' : D₂, ∃ a' : A₂,
          (d' : G) = h⁻¹ * d * h ∧ (a' : G) = h⁻¹ * a * h ∧ e d' = a') ∧
        Nat.card (↥D₂ ⧸ B₂.subgroupOf D₂) = (2 ^ n) ^ 2 ∧
        IsElementaryAbelian 2 (↥D₂ ⧸ B₂.subgroupOf D₂) ∧
        (∀ x ∈ Ω, ∀ y ∈ Ω, ∃ d ∈ D₂, d⁻¹ * x * d = y) ∧
        ∀ x ∈ Ω, ∀ d d' : D₂, (d : G)⁻¹ * x * d = (d' : G)⁻¹ * x * d' →
          (d : ↥D₂ ⧸ B₂.subgroupOf D₂) = d' := by
  intro C TG PG Q U₁ U₂ A₂ B₂ N₂ D₂ Ω hone
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hT' := hS.T_eq_zpowers hO hLn
  have hS2 : TwoCoreSetup L K n (t : G) :=
    { two_le := hn
      card_K := hK
      t_mul_t := hS.t_mul_t
      L_le := hS.L_le
      cent_le := hS.cent_le
      cent_inf := hS.cent_inf.trans hT'
      not_conj := hS.conj_not_mem_L hO hLn }
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hQ : Q = pull φ (antiUnipotent K) ⊔ TG := by
    show PG ⊔ TG = _
    rw [hPG]
  have hH : Hyp L K n φ TG t := ⟨hS, hS2, hT', by rw [← hQ]; exact hone⟩
  have hNQ := hH.normalizer_Q_le
  have hNC := (hS.orbits hO hLn).2.2.2.2
  have hmove : ∃ g ∈ N₂, g * t ≠ t * g := by
    obtain ⟨m, hm, hmC⟩ := Set.not_subset.mp hNC
    exact ⟨m, (hNQ hm).2, fun hmt => hmC (mem_centralizer_singleton_iff.mpr hmt)⟩
  have h2 : SecondHyp L K n φ (t : G) := ⟨hS2, hH.fus_two.1, hmove⟩
  obtain ⟨hBD, hUA, e, he1, he2, he3, he4⟩ := h2.exists_mulEquiv
  have hAN : A₂ ≤ N₂ := le_sup_right.trans SecondHyp.B_le_N
  have hUN : U₂ ≤ N₂ := (pull_mono φ rootU₂_le_radA2).trans hAN
  refine ⟨centralizer_B_eq φ hS2, ⟨hAN, ⟨fun x hx g => mem_subgroupOf.mpr
    (h2.conj_mem_A g.2 (mem_subgroupOf.mp hx))⟩⟩, ⟨hUN, ⟨fun x hx g => mem_subgroupOf.mpr
    (h2.conj_mem_U g.2 (mem_subgroupOf.mp hx))⟩⟩, h2.orbit_eq, hH.fus_two.1, h2.mul_eq,
    h2.inf_eq, hBD, hUA, e, he1, he2, he3.trans (by rw [hK]), he4, h2.transitive_D,
    h2.free_D⟩

end CFSG.LocalAnalysis.SymplecticFourStandard
