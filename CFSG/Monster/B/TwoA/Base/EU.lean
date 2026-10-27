
module

public import CFSG.Monster.B.TwoA.Base.PsiV
public import CFSG.Monster.B.TwoA.Base.ElemAut

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem xhat_pow_val_zero : xhat ^ (0 : ZMod 2).val = 1 := pow_zero _

theorem xhat_pow_val_one : xhat ^ (1 : ZMod 2).val = xhat := pow_one _

theorem xhat_pow_val_add (s t : ZMod 2) :
    xhat ^ (s + t).val = xhat ^ s.val * xhat ^ t.val := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · rw [add_zero, xhat_pow_val_zero, mul_one]
  · rw [zero_add, xhat_pow_val_zero, one_mul]
  · rw [add_zero, xhat_pow_val_zero, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, xhat_pow_val_zero, xhat_pow_val_one, xhat_mul_self]

theorem xhat_pow_val_eq_one_iff (t : ZMod 2) : xhat ^ t.val = 1 ↔ t = 0 := by
  rcases zmod2_cases t with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => xhat_pow_val_zero⟩
  · rw [xhat_pow_val_one]
    exact ⟨fun h => absurd h xhat_ne_one, fun h => absurd h (by decide)⟩

theorem xhat_pow_val_injective {s t : ZMod 2} (h : xhat ^ s.val = xhat ^ t.val) : s = t := by
  have h1 : xhat ^ (s + t).val = 1 := by
    rw [xhat_pow_val_add, h, ← xhat_pow_val_add, show t + t = 0 by
      rcases zmod2_cases t with rfl | rfl <;> rfl, xhat_pow_val_zero]
  have h2 := (xhat_pow_val_eq_one_iff _).1 h1
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · rfl
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · rfl

theorem xhat_pow_comm_of_mem_Jhat
    {g : Dfull} (hg : g ∈ Jhat) (t : ZMod 2) :
    g * xhat ^ t.val = xhat ^ t.val * g :=
  ((Commute.pow_right (xhat_comm_of_mem_Jhat hg) t.val)).eq

theorem conj_Ehat (a e : Ehat) :
    (e : Dfull)⁻¹ * a * e = a * xhat ^ (bV (psiW a) (psiW e)).val := by
  rw [mul_assoc, Ehat_comm a e, mul_assoc, inv_mul_cancel_left]

theorem fiber_cases {a b : Ehat} (h : psiW a = psiW b) :
    (a : Dfull) = b ∨ (a : Dfull) = b * xhat := by
  have h1 : psiW (a * b⁻¹) = 0 := by rw [psiW_mul, psiW_inv, h, add_neg_cancel]
  rcases (psiW_eq_zero_iff _).1 h1 with h2 | h2
  · left
    have := congrArg Subtype.val h2
    change (a : Dfull) * (b : Dfull)⁻¹ = 1 at this
    exact mul_inv_eq_one.1 this
  · right
    have := congrArg Subtype.val h2
    change (a : Dfull) * (b : Dfull)⁻¹ = xhat at this
    rw [mul_inv_eq_iff_eq_mul] at this
    rw [this, xhat_comm_of_mem_Jhat (Ehat_le_Jhat b.2)]

variable (U : Submodule (ZMod 2) (Wv v0))

@[expose] def uMul : Subgroup (Multiplicative (Wv v0)) := AddSubgroup.toSubgroup U.toAddSubgroup

@[expose] def psiSub : Subgroup Ehat := (uMul U).comap psiE

@[expose] def EU : Subgroup Dfull := (psiSub U).map Ehat.subtype

variable {U}

theorem mem_psiSub {e : Ehat} : e ∈ psiSub U ↔ psiW e ∈ U := Iff.rfl

theorem mem_EU {d : Dfull} : d ∈ EU U ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ ∈ U := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, he⟩
  · rintro ⟨h, hU⟩
    exact ⟨⟨d, h⟩, hU, rfl⟩

theorem EU_le_Ehat : EU U ≤ Ehat := fun _ h => (mem_EU.1 h).1

theorem EU_le_Jhat : EU U ≤ Jhat := EU_le_Ehat.trans Ehat_le_Jhat

theorem mem_EU_of {e : Ehat} (h : psiW e ∈ U) : (e : Dfull) ∈ EU U := ⟨e, h, rfl⟩

theorem xhat_mem_EU : xhat ∈ EU U :=
  mem_EU_of (e := xhatE) (by rw [psiW_xhatE]; exact U.zero_mem)

theorem EU_mono {U' : Submodule (ZMod 2) (Wv v0)} (h : U ≤ U') : EU U ≤ EU U' := fun _ hd => by
  obtain ⟨hd', hdU⟩ := mem_EU.1 hd
  exact mem_EU.2 ⟨hd', h hdU⟩

theorem exists_EU_of_mem
    {x : Wv v0} (hx : x ∈ U) :
    ∃ e : Ehat, psiW e = x ∧ (e : Dfull) ∈ EU U := by
  obtain ⟨e, rfl⟩ := psiW_surjective x
  exact ⟨e, rfl, mem_EU_of hx⟩

theorem natCard_uMul : Nat.card (uMul U) = Nat.card U :=
  Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem natCard_EU : Nat.card (EU U) = 2 * Nat.card U := by
  rw [EU, ← Nat.card_congr ((psiSub U).equivMapOfInjective Ehat.subtype
      Subtype.coe_injective).toEquiv,
    psiSub, natCard_comap_of_surjective psiE_surjective, natCard_ker_psiE, natCard_uMul]

theorem bV_eq_zero_of_singular (hU : ∀ x ∈ U, qV x = 0) {x y : Wv v0} (hx : x ∈ U)
    (hy : y ∈ U) : bV x y = 0 := by
  have h := qV_add x y
  rw [hU _ (U.add_mem hx hy), hU x hx, hU y hy, zero_add, zero_add] at h
  exact h.symm

theorem EU_comm (hU : ∀ x ∈ U, qV x = 0) {a b : Dfull} (ha : a ∈ EU U) (hb : b ∈ EU U) :
    a * b = b * a := by
  obtain ⟨ha', hau⟩ := mem_EU.1 ha
  obtain ⟨hb', hbu⟩ := mem_EU.1 hb
  have h := Ehat_comm ⟨a, ha'⟩ ⟨b, hb'⟩
  rw [bV_eq_zero_of_singular hU hau hbu, ZMod.val_zero, pow_zero, mul_one] at h
  exact h

theorem EU_mul_self (hU : ∀ x ∈ U, qV x = 0) {a : Dfull} (ha : a ∈ EU U) : a * a = 1 := by
  obtain ⟨ha', hau⟩ := mem_EU.1 ha
  exact Ehat_mul_self ⟨a, ha'⟩ (hU _ hau)

theorem isElementaryAbelian_EU (hU : ∀ x ∈ U, qV x = 0) : CFSG.IsElementaryAbelian 2 (EU U) where
  is_comm := ⟨fun a b => Subtype.ext (EU_comm hU a.2 b.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, pow_two, OneMemClass.coe_one]
    exact EU_mul_self hU a.2)

theorem conj_mem_EU
    {g : Dfull} (hg : g ∈ Jhat) (hk : jhatToKv0 ⟨g, hg⟩ ∈ wSetStab U)
    {a : Dfull} (ha : a ∈ EU U) : g⁻¹ * a * g ∈ EU U := by
  obtain ⟨ha', hau⟩ := mem_EU.1 ha
  refine mem_EU.2 ⟨conj_mem_Ehat hg ha', ?_⟩
  rw [psiW_conj hg ha']
  exact hk _ hau

theorem mem_normalizer_EU_iff
    {g : Dfull} (hg : g ∈ Jhat) :
    g ∈ Subgroup.normalizer (EU U : Set Dfull) ↔ jhatToKv0 ⟨g, hg⟩ ∈ wSetStab U := by
  constructor
  · intro hn x hx
    obtain ⟨e, rfl, he⟩ := exists_EU_of_mem hx
    have h1 := (Subgroup.mem_normalizer_iff''.1 hn e).1 he
    obtain ⟨h2, h3⟩ := mem_EU.1 h1
    have h4 := psiW_conj hg e.2
    have h5 : psiW ⟨g⁻¹ * e * g, h2⟩ = psiW ⟨g⁻¹ * e * g, conj_mem_Ehat hg e.2⟩ := rfl
    rw [h5, h4] at h3
    exact h3
  · intro hk
    rw [← Subgroup.inv_mem_iff]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [inv_inv]
    exact conj_mem_EU hg hk hn

theorem Ehat_le_normalizer_EU :
    Ehat ≤ Subgroup.normalizer (EU U : Set Dfull) := fun e he => by
  rw [mem_normalizer_EU_iff (Ehat_le_Jhat he), jhatToKv0_eq_one_of_mem_Ehat _ he]
  exact (wSetStab U).one_mem

theorem centralizer_EU_le_Jhat :
    Subgroup.centralizer (EU U : Set Dfull) ≤ Jhat := by
  intro g hg
  rw [← centralizer_xhat]
  exact Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 hg) xhat xhat_mem_EU).symm

theorem jhatToKv0_mem_wFix
    {g : Dfull} (hg : g ∈ Jhat)
    (hc : g ∈ Subgroup.centralizer (EU U : Set Dfull)) :
    jhatToKv0 ⟨g, hg⟩ ∈ wFix (U : Set (Wv v0)) := by
  rw [mem_wFix]
  intro x hx
  obtain ⟨e, rfl, he⟩ := exists_EU_of_mem hx
  have h1 : g⁻¹ * e * g = e := by
    rw [mul_assoc, (Subgroup.mem_centralizer_iff.1 hc) e he, inv_mul_cancel_left]
  have h2 := psiW_conj hg e.2
  have h3 : (⟨g⁻¹ * e * g, conj_mem_Ehat hg e.2⟩ : Ehat) = e := Subtype.ext h1
  rw [h3] at h2
  exact h2.symm

theorem conj_fix_iff_of_fiber
    {g : Dfull} (hg : g ∈ Jhat) {a b : Ehat} (h : psiW a = psiW b) :
    g⁻¹ * a * g = a ↔ g⁻¹ * b * g = b := by
  rcases fiber_cases h with h1 | h1
  · rw [h1]
  · rw [h1]
    have e : g⁻¹ * (b * xhat) * g = g⁻¹ * b * g * xhat := by
      calc g⁻¹ * ((b : Dfull) * xhat) * g = g⁻¹ * b * (xhat * g) := by simp only [mul_assoc]
        _ = g⁻¹ * b * (g * xhat) := by rw [xhat_comm_of_mem_Jhat hg]
        _ = g⁻¹ * b * g * xhat := by simp only [mul_assoc]
    rw [e]
    exact ⟨mul_right_cancel, fun h2 => by rw [h2]⟩

theorem conj_cases_of_wFix {g : Dfull} (hg : g ∈ Jhat)
    (hk : jhatToKv0 ⟨g, hg⟩ ∈ wFix (U : Set (Wv v0))) {a : Ehat} (ha : psiW a ∈ U) :
    g⁻¹ * a * g = a ∨ g⁻¹ * a * g = a * xhat := by
  have h1 := psiW_conj hg a.2
  rw [(mem_wFix.1 hk) _ ha] at h1
  exact fiber_cases (a := ⟨g⁻¹ * a * g, conj_mem_Ehat hg a.2⟩) h1

theorem exists_mul_mem_centralizer
    {g : Dfull} (hg : g ∈ Jhat)
    (hk : jhatToKv0 ⟨g, hg⟩ ∈ wFix (U : Set (Wv v0))) :
    ∃ e : Ehat, g * e ∈ Subgroup.centralizer (EU U : Set Dfull) := by
  classical
  let lift : Wv v0 → Ehat := Function.surjInv psiW_surjective
  have hlift : ∀ x, psiW (lift x) = x := Function.surjInv_eq psiW_surjective
  let t : Wv v0 → ZMod 2 := fun x => if g⁻¹ * lift x * g = lift x then 0 else 1
  have key : ∀ a : Ehat, psiW a ∈ U → g⁻¹ * a * g = a * xhat ^ (t (psiW a)).val := by
    intro a ha
    have hiff := conj_fix_iff_of_fiber hg (hlift (psiW a))
    by_cases hc : g⁻¹ * lift (psiW a) * g = lift (psiW a)
    · have ht : t (psiW a) = 0 := ite_eq_left hc
      rw [ht, xhat_pow_val_zero, mul_one]
      exact hiff.1 hc
    · have ht : t (psiW a) = 1 := ite_eq_right hc
      rw [ht, xhat_pow_val_one]
      rcases conj_cases_of_wFix hg hk ha with h | h
      · exact absurd (hiff.2 h) hc
      · exact h
  have tadd : ∀ x ∈ U, ∀ y ∈ U, t (x + y) = t x + t y := by
    intro x hx y hy
    have h1 := key (lift x * lift y) (by rw [psiW_mul, hlift, hlift]; exact U.add_mem hx hy)
    rw [psiW_mul, hlift, hlift] at h1
    have h2 : g⁻¹ * ((lift x : Dfull) * lift y) * g =
        (g⁻¹ * lift x * g) * (g⁻¹ * lift y * g) := by group
    have h3 := key (lift x) (by rw [hlift]; exact hx)
    have h4 := key (lift y) (by rw [hlift]; exact hy)
    rw [hlift] at h3 h4
    rw [Subgroup.coe_mul, h2, h3, h4] at h1
    have hc := xhat_pow_comm_of_mem_Jhat (Ehat_le_Jhat (lift y).2) (t x)
    have h5 : (lift x : Dfull) * xhat ^ (t x).val * ((lift y : Dfull) * xhat ^ (t y).val) =
        (lift x : Dfull) * lift y * xhat ^ (t x + t y).val := by
      rw [xhat_pow_val_add]
      calc (lift x : Dfull) * xhat ^ (t x).val * ((lift y : Dfull) * xhat ^ (t y).val)
          = (lift x : Dfull) * (xhat ^ (t x).val * lift y) * xhat ^ (t y).val := by
            simp only [mul_assoc]
        _ = (lift x : Dfull) * (lift y * xhat ^ (t x).val) * xhat ^ (t y).val := by rw [← hc]
        _ = (lift x : Dfull) * lift y * (xhat ^ (t x).val * xhat ^ (t y).val) := by
            simp only [mul_assoc]
    rw [h5] at h1
    exact (xhat_pow_val_injective (mul_left_cancel h1)).symm
  have t0 : t 0 = 0 := by
    have h1 := key 1 (by rw [psiW_one]; exact U.zero_mem)
    rw [psiW_one, OneMemClass.coe_one, mul_one, inv_mul_cancel, one_mul] at h1
    exact (xhat_pow_val_eq_one_iff _).1 h1.symm
  let lam : U →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => t x
      map_add' := fun x y => tadd x x.2 y y.2
      map_smul' := fun c x => by
        change t ((c • x : U) : Wv v0) = c • t x
        rcases zmod2_cases c with rfl | rfl
        · rw [zero_smul, Submodule.coe_zero, t0, zero_smul]
        · rw [one_smul, one_smul] }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend lam
  set y := (bV.toDual bV_nondegenerate).symm Λ with hy
  have hby : ∀ m, bV y m = Λ m := fun m => by
    rw [← LinearMap.BilinForm.toDual_def bV_nondegenerate, hy, LinearEquiv.apply_symm_apply]
  have hbt : ∀ x ∈ U, bV x y = t x := fun x hx => by
    rw [bV_comm, hby]
    exact LinearMap.congr_fun hΛ ⟨x, hx⟩
  refine ⟨lift y, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
  obtain ⟨ha', hau⟩ := mem_EU.1 ha
  have h1 : g⁻¹ * a * g = a * xhat ^ (t (psiW ⟨a, ha'⟩)).val := key ⟨a, ha'⟩ hau
  have h2 : ((lift y : Dfull))⁻¹ * a * lift y = a * xhat ^ (t (psiW ⟨a, ha'⟩)).val := by
    have h := conj_Ehat ⟨a, ha'⟩ (lift y)
    rw [hlift, hbt _ hau] at h
    exact h
  have hc := xhat_pow_comm_of_mem_Jhat (Ehat_le_Jhat (lift y).2) (t (psiW ⟨a, ha'⟩))
  have htt : t (psiW ⟨a, ha'⟩) + t (psiW ⟨a, ha'⟩) = 0 := by
    rcases zmod2_cases (t (psiW ⟨a, ha'⟩)) with h | h <;> rw [h] <;> rfl
  have h3 : (g * lift y)⁻¹ * a * (g * lift y) = a := by
    calc (g * lift y)⁻¹ * a * (g * lift y)
        = ((lift y : Dfull))⁻¹ * (g⁻¹ * a * g) * lift y := by group
      _ = ((lift y : Dfull))⁻¹ * a * (xhat ^ (t (psiW ⟨a, ha'⟩)).val * lift y) := by
          rw [h1]; simp only [mul_assoc]
      _ = ((lift y : Dfull))⁻¹ * a * (lift y * xhat ^ (t (psiW ⟨a, ha'⟩)).val) := by rw [← hc]
      _ = (((lift y : Dfull))⁻¹ * a * lift y) * xhat ^ (t (psiW ⟨a, ha'⟩)).val := by
          simp only [mul_assoc]
      _ = a * (xhat ^ (t (psiW ⟨a, ha'⟩)).val * xhat ^ (t (psiW ⟨a, ha'⟩)).val) := by
          rw [h2, mul_assoc]
      _ = a := by rw [← xhat_pow_val_add, htt, xhat_pow_val_zero, mul_one]
  calc a * (g * lift y) = (g * lift y) * ((g * lift y)⁻¹ * a * (g * lift y)) := by group
    _ = (g * lift y) * a := by rw [h3]

theorem Ehat_inf_centralizer_EU :
    Ehat ⊓ Subgroup.centralizer (EU U : Set Dfull) = EU (bV.orthogonal U) := by
  ext d
  constructor
  · rintro ⟨hd, hc⟩
    refine mem_EU.2 ⟨hd, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    obtain ⟨a, rfl, ha⟩ := exists_EU_of_mem hx
    have h1 := Ehat_comm a ⟨d, hd⟩
    have h2 : (a : Dfull) * d = d * a := (Subgroup.mem_centralizer_iff.1 hc) a ha
    have h3 : d * (a : Dfull) * xhat ^ (bV (psiW a) (psiW ⟨d, hd⟩)).val = d * a * 1 := by
      rw [mul_one, ← h1, h2]
    exact (xhat_pow_val_eq_one_iff _).1 (mul_left_cancel h3)
  · intro hd
    obtain ⟨hd', hdU⟩ := mem_EU.1 hd
    refine ⟨hd', Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    obtain ⟨ha', haU⟩ := mem_EU.1 ha
    have h1 := Ehat_comm ⟨a, ha'⟩ ⟨d, hd'⟩
    have h0 : bV (psiW ⟨a, ha'⟩) (psiW ⟨d, hd'⟩) = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hdU) _ haU
    rw [h0, ZMod.val_zero, pow_zero, mul_one] at h1
    exact h1

theorem natCard_submodule
    (U' : Submodule (ZMod 2) (Wv v0)) :
    Nat.card U' = 2 ^ Module.finrank (ZMod 2) U' :=
  (FiniteField.pow_finrank_eq_natCard 2 U').symm

theorem natCard_Ehat_inf_centralizer_EU :
    Nat.card ↥(Ehat ⊓ Subgroup.centralizer (EU U : Set Dfull)) =
      2 * 2 ^ (22 - Module.finrank (ZMod 2) U) := by
  rw [Ehat_inf_centralizer_EU, natCard_EU, natCard_submodule,
    LinearMap.BilinForm.finrank_orthogonal bV_nondegenerate, Co2.finrank_W]

variable (U)

@[expose] def HU : Subgroup Dfull := Jhat ⊓ Subgroup.normalizer (EU U : Set Dfull)

@[expose] def KU : Subgroup Dfull := Subgroup.normalizer (EU U : Set Dfull)

@[expose] def ZU : Subgroup Dfull := Subgroup.centralizer (EU U : Set Dfull)

variable {U}

theorem HU_le_KU : HU U ≤ KU U := inf_le_right

theorem HU_le_Jhat : HU U ≤ Jhat := inf_le_left

theorem ZU_le_Jhat : ZU U ≤ Jhat := centralizer_EU_le_Jhat

theorem ZU_le_KU : ZU U ≤ KU U := Subgroup.centralizer_le_normalizer _

theorem ZU_le_HU :
    ZU U ≤ HU U := fun _ h => ⟨ZU_le_Jhat h, ZU_le_KU h⟩

theorem HU_subgroupOf_eq :
    (HU U).subgroupOf Jhat = (wSetStab U).comap jhatToKv0 := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, HU, Subgroup.mem_inf]
  exact ⟨fun h => (mem_normalizer_EU_iff g.2).1 h.2,
    fun h => ⟨g.2, (mem_normalizer_EU_iff g.2).2 h⟩⟩

theorem natCard_ker_jhatToKv0 : Nat.card jhatToKv0.ker = 2 ^ 23 := by
  rw [ker_jhatToKv0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ehat_le_Jhat).toEquiv,
    natCard_Ehat]

theorem natCard_HU :
    Nat.card (HU U) = 2 ^ 23 * Nat.card (wSetStab U) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe HU_le_Jhat).toEquiv, HU_subgroupOf_eq,
    natCard_comap_of_surjective jhatToKv0_surjective, natCard_ker_jhatToKv0]

theorem ZU_subgroupOf_le
    (U : Submodule (ZMod 2) (Wv v0)) :
    (ZU U).subgroupOf Jhat ≤ (wFix (U : Set (Wv v0))).comap jhatToKv0 :=
  fun g hg => jhatToKv0_mem_wFix g.2 hg

@[expose] def zuProj
    (U : Submodule (ZMod 2) (Wv v0)) : ZU U →* wFix (U : Set (Wv v0)) :=
  (comapRestrict jhatToKv0 (wFix (U : Set (Wv v0)))).comp
    ((Subgroup.inclusion (ZU_subgroupOf_le U)).comp
      (Subgroup.subgroupOfEquivOfLe ZU_le_Jhat).symm.toMonoidHom)

theorem coe_zuProj
    (g : ZU U) :
    ((zuProj U g : wFix (U : Set (Wv v0))) : Kstab v0) = jhatToKv0 ⟨g, ZU_le_Jhat g.2⟩ := rfl

theorem zuProj_surjective :
    Function.Surjective (zuProj U) := by
  intro k
  obtain ⟨g, hg⟩ := jhatToKv0_surjective k
  have hk : jhatToKv0 ⟨(g : Dfull), g.2⟩ ∈ wFix (U : Set (Wv v0)) := by
    change jhatToKv0 g ∈ _
    rw [hg]
    exact k.2
  obtain ⟨e, he⟩ := exists_mul_mem_centralizer g.2 hk
  refine ⟨⟨_, he⟩, Subtype.ext ?_⟩
  rw [coe_zuProj]
  have e1 : (⟨(g : Dfull) * e, ZU_le_Jhat he⟩ : Jhat) = g * ⟨e, Ehat_le_Jhat e.2⟩ := rfl
  rw [e1, map_mul, jhatToKv0_eq_one_of_mem_Ehat _ e.2, mul_one, hg]

theorem ker_zuProj :
    (zuProj U).ker = (Ehat ⊓ ZU U).subgroupOf (ZU U) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 : jhatToKv0 ⟨g, ZU_le_Jhat g.2⟩ = 1 := congrArg Subtype.val h
    rw [← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf] at h1
    exact ⟨h1, g.2⟩
  · intro h
    exact Subtype.ext (jhatToKv0_eq_one_of_mem_Ehat _ h.1)

theorem natCard_ZU :
    Nat.card (ZU U) =
    2 * 2 ^ (22 - Module.finrank (ZMod 2) U) * Nat.card (wFix (U : Set (Wv v0))) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zuProj U).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ zuProj_surjective).toEquiv,
    ker_zuProj, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Ehat ⊓ ZU U ≤ ZU U)).toEquiv] at h1
  have h2 : Nat.card ↥(Ehat ⊓ ZU U) = 2 * 2 ^ (22 - Module.finrank (ZMod 2) U) :=
    natCard_Ehat_inf_centralizer_EU
  rw [h2] at h1
  rw [h1, mul_comm]

@[expose] def xyE :
    Ehat := xhatE * yhatE

theorem coe_xyE :
    (xyE : Dfull) = iotaD ybar := xhat_mul_yhat

theorem psiW_xyE :

    psiW xyE = wFr := by rw [xyE, psiW_mul, psiW_xhatE, psiW_yhat, zero_add]

theorem exists_bV_eq_one
    {x : Wv v0} (hx : x ≠ 0) : ∃ e : Ehat, bV x (psiW e) = 1 := by
  obtain ⟨z, hz⟩ : ∃ z, bV x z ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (bV_nondegenerate.1 x h)
  obtain ⟨e, rfl⟩ := psiW_surjective z
  refine ⟨e, ?_⟩
  rcases zmod2_cases (bV x (psiW e)) with h | h
  · exact absurd h hz
  · exact h

theorem tauhat_mem_Shat : tauhat ∈ Shat := ⟨taubar, rfl⟩

theorem exists_HU_conj_xy
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) {a : Dfull} (ha : a ∈ EU U)
    (ha1 : a ≠ 1) (hax : a ≠ xhat) : ∃ h ∈ HU U, h * iotaD ybar * h⁻¹ = a := by
  obtain ⟨ha', hau⟩ := mem_EU.1 ha
  have hne : psiW ⟨a, ha'⟩ ≠ 0 := by
    intro h0
    rcases (psiW_eq_zero_iff _).1 h0 with h | h
    · exact ha1 (congrArg Subtype.val h)
    · exact hax (congrArg Subtype.val h)
  obtain ⟨k, hk, hkw⟩ := htr _ hau hne
  obtain ⟨h₀, hh₀⟩ := jhatToKv0_surjective k
  have hN : (h₀ : Dfull) ∈ Subgroup.normalizer (EU U : Set Dfull) := by
    rw [mem_normalizer_EU_iff h₀.2]
    change jhatToKv0 h₀ ∈ wSetStab U
    rw [hh₀]
    exact hk
  have hH : (h₀ : Dfull)⁻¹ ∈ HU U := ⟨Jhat.inv_mem h₀.2, Subgroup.inv_mem _ hN⟩
  have h1 := psiW_conj h₀.2 xyE.2
  have hh₀' : jhatToKv0 ⟨(h₀ : Dfull), h₀.2⟩ = k := hh₀
  rw [hh₀', show (⟨(xyE : Dfull), xyE.2⟩ : Ehat) = xyE from rfl, psiW_xyE, hkw] at h1
  rcases fiber_cases (a := ⟨(h₀ : Dfull)⁻¹ * xyE * h₀, conj_mem_Ehat h₀.2 xyE.2⟩)
    (b := ⟨a, ha'⟩) h1 with h2 | h2
  · refine ⟨(h₀ : Dfull)⁻¹, hH, ?_⟩
    rw [inv_inv, ← coe_xyE]
    exact h2
  · obtain ⟨e, he⟩ := exists_bV_eq_one hne
    have h3 := conj_Ehat ⟨a, ha'⟩ e
    rw [he, xhat_pow_val_one] at h3
    refine ⟨(e : Dfull) * (h₀ : Dfull)⁻¹,
      (HU U).mul_mem ⟨Ehat_le_Jhat e.2, Ehat_le_normalizer_EU e.2⟩ hH, ?_⟩
    have e1 : (e : Dfull) * (h₀ : Dfull)⁻¹ * iotaD ybar * ((e : Dfull) * (h₀ : Dfull)⁻¹)⁻¹ =
        e * ((h₀ : Dfull)⁻¹ * (xyE : Dfull) * h₀) * (e : Dfull)⁻¹ := by
      rw [coe_xyE]
      group
    have h2' : (h₀ : Dfull)⁻¹ * (xyE : Dfull) * h₀ = a * xhat := h2
    have h3' : (e : Dfull)⁻¹ * a * e = a * xhat := h3
    rw [e1, h2', ← h3']
    group

theorem exists_conj_xhat
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) {a : Dfull} (ha : a ∈ EU U)
    (ha1 : a ≠ 1) :
    ∃ g ∈ Subgroup.closure (insert tauhat (HU U : Set Dfull)), g * xhat * g⁻¹ = a := by
  by_cases hax : a = xhat
  · exact ⟨1, Subgroup.one_mem _, by rw [hax, one_mul, inv_one, mul_one]⟩
  obtain ⟨h, hh, hxa⟩ := exists_HU_conj_xy htr ha ha1 hax
  refine ⟨h * tauhat, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ hh))
    (Subgroup.subset_closure (Set.mem_insert _ _)), ?_⟩
  rw [← hxa, ← tauhat_conj_xhat]
  group

theorem closure_le_KU (htau : tauhat ∈ Subgroup.normalizer (EU U : Set Dfull)) :
    Subgroup.closure (insert tauhat (HU U : Set Dfull)) ≤ KU U := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | h)
  · exact htau
  · exact HU_le_KU h

theorem KU_eq_closure
    (htau : tauhat ∈ Subgroup.normalizer (EU U : Set Dfull))
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) :
    KU U = Subgroup.closure (insert tauhat (HU U : Set Dfull)) := by
  refine le_antisymm (fun g hg => ?_) (closure_le_KU htau)
  have hgx : g * xhat * g⁻¹ ∈ EU U := conj_mem_of_normalizer hg xhat_mem_EU
  have hgx1 : g * xhat * g⁻¹ ≠ 1 := fun h => xhat_ne_one (by
    have := congrArg (fun d => g⁻¹ * d * g) h
    simpa [mul_assoc] using this)
  obtain ⟨g', hg', hg'x⟩ := exists_conj_xhat htr hgx hgx1
  have hJ : g'⁻¹ * g ∈ Jhat := by
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
    calc g'⁻¹ * g * xhat = g'⁻¹ * (g * xhat * g⁻¹) * g := by group
      _ = g'⁻¹ * (g' * xhat * g'⁻¹) * g := by rw [hg'x]
      _ = xhat * (g'⁻¹ * g) := by group
  have hK : g'⁻¹ * g ∈ KU U := (KU U).mul_mem ((KU U).inv_mem (closure_le_KU htau hg')) hg
  have : g = g' * (g'⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem _ hg' (Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨hJ, hK⟩))

theorem KU_le_Shat
    (htau : tauhat ∈ Subgroup.normalizer (EU U : Set Dfull))
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) : KU U ≤ Shat := by
  rw [KU_eq_closure htau htr, Subgroup.closure_le]
  rintro _ (rfl | h)
  · exact tauhat_mem_Shat
  · exact Jhat_le_Shat (HU_le_Jhat h)

@[expose, instance_reducible] noncomputable def kuAction (U : Submodule (ZMod 2) (Wv v0)) :
    MulAction (KU U) (Esharp (EU U)) :=
  sharpAction (EU U)

attribute [local instance] kuAction

@[expose] def xSharp (U : Submodule (ZMod 2) (Wv v0)) : Esharp (EU U) :=
  ⟨xhat, xhat_mem_EU, xhat_ne_one⟩

theorem stabilizer_xSharp :
    MulAction.stabilizer (KU U) (xSharp U) = (HU U).subgroupOf (KU U) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, HU, Subgroup.mem_inf,
    ← Subtype.coe_inj]
  change (g : Dfull) * xhat * (g : Dfull)⁻¹ = xhat ↔ _
  rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩

theorem index_HU_KU
    (htau : tauhat ∈ Subgroup.normalizer (EU U : Set Dfull))
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) :
    ((HU U).subgroupOf (KU U)).index = Nat.card (EU U) - 1 := by
  rw [← stabilizer_xSharp, MulAction.index_stabilizer, ← natCard_Esharp]
  have horb : MulAction.orbit (KU U) (xSharp U) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro v
    obtain ⟨g, hg, hgx⟩ := exists_conj_xhat htr v.2.1 v.2.2
    rw [← KU_eq_closure htau htr] at hg
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  rw [horb, Set.ncard_univ]

theorem natCard_KU
    (htau : tauhat ∈ Subgroup.normalizer (EU U : Set Dfull))
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) :
    Nat.card (KU U) = (Nat.card (EU U) - 1) * Nat.card (HU U) := by
  have h := ((HU U).subgroupOf (KU U)).card_mul_index
  rw [index_HU_KU htau htr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe HU_le_KU).toEquiv] at h
  rw [← h, mul_comm]

end CFSG.Monster.B.TwoA
