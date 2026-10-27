module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaCoordinates

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace TwD7Q

variable {G : Type} [Group G]

abbrev cen (β : G) : Subgroup G := centralizer ({β} : Set G)

abbrev zb (β : G) : Subgroup ↥(cen β) := (zpowers β).subgroupOf (cen β)

theorem mem_cen_iff {β g : G} : g ∈ cen β ↔ g * β = β * g :=
  mem_centralizer_singleton_iff

theorem self_mem_cen (β : G) : β ∈ cen β := mem_cen_iff.mpr rfl

theorem zpowers_le_cen (β : G) : zpowers β ≤ cen β := zpowers_le.mpr (self_mem_cen β)

theorem zb_le_center (β : G) : zb β ≤ center ↥(cen β) := by
  intro x hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp hx)
  have hy : Commute (y : G) β := mem_cen_iff.mp y.2
  change (y : G) * x = x * y
  rw [← hn]
  exact (hy.zpow_right n).eq

instance zb_normal (β : G) : (zb β).Normal := normal_of_le_center (zb_le_center β)

abbrev Q (β : G) : Type := ↥(cen β) ⧸ zb β

abbrev pr (β : G) : ↥(cen β) →* Q β := QuotientGroup.mk' (zb β)

abbrev img (β : G) (X : Subgroup G) : Subgroup (Q β) := (X.subgroupOf (cen β)).map (pr β)

theorem pr_surjective (β : G) : Function.Surjective (pr β) := QuotientGroup.mk'_surjective _

theorem pr_eq_one_iff {β : G} (x : ↥(cen β)) : pr β x = 1 ↔ (x : G) ∈ zpowers β := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact mem_subgroupOf

theorem pr_eq_pr_iff {β : G} (x y : ↥(cen β)) :
    pr β x = pr β y ↔ (x : G)⁻¹ * y ∈ zpowers β := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem pr_mem_img {β : G} {X : Subgroup G} {x : ↥(cen β)} (hx : (x : G) ∈ X) :
    pr β x ∈ img β X :=
  mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem mem_img_iff {β : G} {X : Subgroup G} {q : Q β} :
    q ∈ img β X ↔ ∃ x : ↥(cen β), (x : G) ∈ X ∧ pr β x = q := by
  simp only [img, mem_map, mem_subgroupOf]

theorem img_mono {β : G} {X Y : Subgroup G} (h : X ≤ Y) : img β X ≤ img β Y := by
  rintro _ ⟨x, hx, rfl⟩
  exact pr_mem_img (h (mem_subgroupOf.mp hx))

theorem mem_of_pr_mem_img {β : G} {X : Subgroup G} (hβX : β ∈ X) {x : ↥(cen β)}
    (hx : pr β x ∈ img β X) : (x : G) ∈ X := by
  obtain ⟨y, hyX, hy⟩ := mem_img_iff.mp hx
  have hz : (y : G)⁻¹ * x ∈ X := zpowers_le.mpr hβX ((pr_eq_pr_iff y x).mp hy)
  have hxy : (x : G) = y * ((y : G)⁻¹ * x) := by group
  rw [hxy]
  exact X.mul_mem hyX hz

theorem pr_mem_img_iff {β : G} {X : Subgroup G} (hβX : β ∈ X) {x : ↥(cen β)} :
    pr β x ∈ img β X ↔ (x : G) ∈ X :=
  ⟨mem_of_pr_mem_img hβX, pr_mem_img⟩

theorem pr_mem_normalizer_img_iff {β : G} {X : Subgroup G} (hβX : β ∈ X) (hX : X ≤ cen β)
    {g : ↥(cen β)} :
    pr β g ∈ normalizer (img β X : Set (Q β)) ↔ (g : G) ∈ normalizer (X : Set G) := by
  have key : ∀ g : ↥(cen β), pr β g ∈ normalizer (img β X : Set (Q β)) →
      ∀ x ∈ X, (g : G) * x * (g : G)⁻¹ ∈ X := by
    intro g hg x hx
    have h1 : pr β (g * ⟨x, hX hx⟩ * g⁻¹) ∈ img β X := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hg _).mp (pr_mem_img hx)
    exact mem_of_pr_mem_img hβX h1
  constructor
  · intro hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have h2 := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using h2
  · intro hg
    rw [mem_normalizer_iff]
    intro q
    obtain ⟨x, rfl⟩ := pr_surjective β q
    rw [← map_inv, ← map_mul, ← map_mul, pr_mem_img_iff hβX, pr_mem_img_iff hβX]
    exact (mem_normalizer_iff.mp hg (x : G))

end TwD7Q

namespace Basis3

open TwD7Q

variable {G : Type} [Group G] {k : ℕ}

theorem b_mem_cen (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) (i : Fin (k + 1)) :
    B.b i ∈ cen β := by
  subst hβ
  exact mem_cen_iff.mpr (B.comm i 0).eq

theorem span_le_cen (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) : B.span ≤ cen β := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨i, rfl⟩
  exact B.b_mem_cen hβ i

private theorem coe_list_prod_ofFn {H : Subgroup G} {n : ℕ} (f : Fin n → ↥H) :
    (((List.ofFn f).prod : ↥H) : G) = (List.ofFn fun i => (f i : G)).prod := by
  rw [SubmonoidClass.coe_list_prod, List.map_ofFn]
  rfl

@[expose] def toCen (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) :
    Basis3 ↥(cen β) (k + 1) where
  b i := ⟨B.b i, B.b_mem_cen hβ i⟩
  comm i j := show (_ : ↥(cen β)) * _ = _ * _ from Subtype.ext (B.comm i j).eq
  ord i := by rw [Subgroup.orderOf_mk]; exact B.ord i
  indep e he := B.indep e (by
    have h := congrArg Subtype.val he
    rw [coe_list_prod_ofFn] at h
    exact h)

theorem coe_toCen_vec (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) (e : Coords (k + 1)) :
    ((B.toCen hβ).vec e : G) = B.vec e :=
  coe_list_prod_ofFn _

private theorem vec_nsmul' (B : Basis3 G k) (n : ℕ) (e : Coords k) :
    B.vec (n • e) = B.vec e ^ n := by
  induction n with
  | zero => rw [zero_nsmul, B.vec_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, B.vec_add, ih, pow_succ]

private theorem tail_eq_zero_of_vec_mem (B : Basis3 G (k + 1)) {e : Coords (k + 1)}
    (he : B.vec e ∈ zpowers (B.b 0)) (i : Fin k) : e i.succ = 0 := by
  classical
  have hfin : IsOfFinOrder (B.b 0) := orderOf_pos_iff.mp (by rw [B.ord 0]; norm_num)
  obtain ⟨n, -, hn⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp he)
  have h : B.vec (n • Pi.single 0 1) = B.vec e := by
    rw [vec_nsmul', B.vec_single]
    exact hn
  rw [← congrFun (B.vec_injective h) i.succ, Pi.smul_apply,
    Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero]

private theorem vec_cons (B : Basis3 G (k + 1)) (a : ZMod 3) (e : Coords k) :
    B.vec (Fin.cons a e) =
      B.b 0 ^ a.val * (List.ofFn fun i : Fin k => B.b i.succ ^ (e i).val).prod := by
  simp only [vec, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

@[expose] def quotHeadB (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) (i : Fin k) : Q β :=
  pr β ((B.toCen hβ).b i.succ)

private theorem pr_toCen_vec_cons (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β)
    (a : ZMod 3) (e : Coords k) :
    pr β ((B.toCen hβ).vec (Fin.cons a e)) =
      (List.ofFn fun i => B.quotHeadB hβ i ^ (e i).val).prod := by
  rw [vec_cons, map_mul, map_list_prod, List.map_ofFn, map_pow]
  have h0 : pr β ((B.toCen hβ).b 0) = 1 := by
    rw [pr_eq_one_iff]
    show B.b 0 ∈ zpowers β
    rw [hβ]
    exact mem_zpowers β
  rw [h0, one_pow, one_mul]
  simp only [Function.comp_def, map_pow]
  rfl

@[expose] def quotHead (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) : Basis3 (Q β) k where
  b := B.quotHeadB hβ
  comm i j := ((B.toCen hβ).comm i.succ j.succ).map (pr β)
  ord i := by
    apply orderOf_eq_prime
    · have hx : (B.toCen hβ).b i.succ ^ 3 = 1 := by
        rw [← (B.toCen hβ).ord i.succ]
        exact pow_orderOf_eq_one _
      rw [quotHeadB, ← map_pow, hx, map_one]
    · intro h
      have h1 := (pr_eq_one_iff _).mp h
      change B.b i.succ ∈ zpowers β at h1
      rw [← B.vec_single i.succ, ← hβ] at h1
      have h2 := B.tail_eq_zero_of_vec_mem h1 i
      simp at h2
  indep e he := by
    have h1 := (pr_eq_one_iff _).mp ((B.pr_toCen_vec_cons hβ 0 e).trans he)
    rw [coe_toCen_vec, ← hβ] at h1
    funext i
    have h2 := B.tail_eq_zero_of_vec_mem h1 i
    rwa [Fin.cons_succ] at h2

theorem quotHead_vec (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) (a : ZMod 3)
    (e : Coords k) : pr β ((B.toCen hβ).vec (Fin.cons a e)) = (B.quotHead hβ).vec e :=
  B.pr_toCen_vec_cons hβ a e

theorem pr_vec_cons (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) (a : ZMod 3)
    (e : Coords k) (h : B.vec (Fin.cons a e) ∈ cen β) :
    pr β ⟨B.vec (Fin.cons a e), h⟩ = (B.quotHead hβ).vec e := by
  rw [← B.quotHead_vec hβ a e]
  congr 1
  exact Subtype.ext (B.coe_toCen_vec hβ _).symm

theorem quotHead_span (B : Basis3 G (k + 1)) {β : G} (hβ : B.b 0 = β) :
    (B.quotHead hβ).span = img β B.span := by
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact pr_mem_img (B.b_mem_span i.succ)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ := B.exists_vec_eq (mem_subgroupOf.mp hx)
    have hx' : x = (B.toCen hβ).vec v := Subtype.ext (by rw [coe_toCen_vec]; exact hv.symm)
    rw [hx', ← Fin.cons_self_tail v, quotHead_vec]
    exact (B.quotHead hβ).vec_mem_span _

@[expose] def quotCoords (e : Coords 8) : Coords 7 :=
  Fin.cons (e 0 - e 1) fun j : Fin 6 => e j.succ.succ

@[expose] def twD7Quot (B : Basis3 G 8) : Basis3 (Q (B.b 0 * B.b 1)) 7 :=
  B.twD7Beta.quotHead B.twD7Beta_b_zero

theorem vec_mem_cen_twD7 (B : Basis3 G 8) (e : Coords 8) : B.vec e ∈ cen (B.b 0 * B.b 1) := by
  have h := B.twD7Beta.span_le_cen B.twD7Beta_b_zero
  rw [B.twD7Beta_span] at h
  exact h (B.vec_mem_span e)

theorem b_mem_cen_twD7 (B : Basis3 G 8) (i : Fin 8) : B.b i ∈ cen (B.b 0 * B.b 1) := by
  rw [← B.vec_single i]
  exact B.vec_mem_cen_twD7 _

theorem pr_vec_twD7Quot (B : Basis3 G 8) (e : Coords 8) (h : B.vec e ∈ cen (B.b 0 * B.b 1)) :
    pr _ ⟨B.vec e, h⟩ = B.twD7Quot.vec (quotCoords e) := by
  have hT : twD7BetaCoordinates.symm e = Fin.cons (-e 0 - e 1) (quotCoords e) := by
    ext i
    fin_cases i <;> rfl
  have hv : B.vec e = B.twD7Beta.vec (Fin.cons (-e 0 - e 1) (quotCoords e)) := by
    rw [twD7Beta, vec_rebase, ← hT, LinearEquiv.apply_symm_apply]
  have hmem : B.twD7Beta.vec (Fin.cons (-e 0 - e 1) (quotCoords e)) ∈ cen (B.b 0 * B.b 1) :=
    hv ▸ h
  rw [show (⟨B.vec e, h⟩ : ↥(cen (B.b 0 * B.b 1))) = ⟨_, hmem⟩ from Subtype.ext hv]
  exact B.twD7Beta.pr_vec_cons B.twD7Beta_b_zero _ _ hmem

theorem pr_b_zero_twD7Quot (B : Basis3 G 8) :
    pr _ ⟨B.b 0, B.b_mem_cen_twD7 0⟩ = B.twD7Quot.b 0 := by
  have h := B.pr_vec_twD7Quot (Pi.single 0 1) (B.vec_mem_cen_twD7 _)
  have hc : quotCoords (Pi.single 0 1) = Pi.single 0 1 := by decide +kernel
  rw [hc, B.twD7Quot.vec_single] at h
  rw [← h]
  congr 1
  exact Subtype.ext (B.vec_single 0).symm

theorem pr_b_one_twD7Quot (B : Basis3 G 8) :
    pr _ ⟨B.b 1, B.b_mem_cen_twD7 1⟩ = (B.twD7Quot.b 0)⁻¹ := by
  have h := B.pr_vec_twD7Quot (Pi.single 1 1) (B.vec_mem_cen_twD7 _)
  have hc : quotCoords (Pi.single 1 1) = -Pi.single 0 1 := by decide +kernel
  have hneg : B.twD7Quot.vec (-Pi.single 0 1) = (B.twD7Quot.b 0)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← B.twD7Quot.vec_single 0, ← B.twD7Quot.vec_add, neg_add_cancel, B.twD7Quot.vec_zero]
  rw [hc, hneg] at h
  rw [← h]
  congr 1
  exact Subtype.ext (B.vec_single 1).symm

theorem pr_b_succ_succ_twD7Quot (B : Basis3 G 8) (j : Fin 6) :
    pr _ ⟨B.b j.succ.succ, B.b_mem_cen_twD7 _⟩ = B.twD7Quot.b j.succ := by
  have hc : quotCoords (Pi.single j.succ.succ 1) = Pi.single j.succ 1 := by
    revert j
    decide +kernel
  have h := B.pr_vec_twD7Quot (Pi.single j.succ.succ 1) (B.vec_mem_cen_twD7 _)
  rw [hc, B.twD7Quot.vec_single] at h
  rw [← h]
  congr 1
  exact Subtype.ext (B.vec_single _).symm

theorem twD7Quot_span (B : Basis3 G 8) : B.twD7Quot.span = img (B.b 0 * B.b 1) B.span := by
  rw [twD7Quot, quotHead_span, twD7Beta_span]

end Basis3

end CFSG.StandardType.FrameRoute.FS81
