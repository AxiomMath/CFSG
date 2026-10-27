module

public import CFSG.RankThree.PartOne.S12.InputsTable
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.Sec12Three

open CFSG CFSG.RankThree.PartOne.Planes CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def conjAut (E X : Subgroup G) (hX : X ≤ Subgroup.normalizer (E : Set G)) :
    X →* MulAut E :=
  E.normalizerMonoidHom.comp (Subgroup.inclusion hX)

theorem coe_conjAut_apply (E X : Subgroup G) (hX : X ≤ Subgroup.normalizer (E : Set G)) (y : X)
    (e : E) : (((conjAut E X hX y) e : E) : G) = y * e * (y : G)⁻¹ := rfl

theorem conjAut_eq_one_iff (E X : Subgroup G) (hX : X ≤ Subgroup.normalizer (E : Set G)) (y : X) :
    conjAut E X hX y = 1 ↔ ∀ e ∈ E, (y : G) * e * (y : G)⁻¹ = e := by
  constructor
  · intro h e he
    have := congrArg (fun φ : MulAut E => ((φ ⟨e, he⟩ : E) : G)) h
    simpa [coe_conjAut_apply] using this
  · intro h
    ext e
    exact h e e.2

theorem torusImage_eq_range {E Y X : Subgroup G} (hX : X ≤ Subgroup.normalizer (E : Set G))
    (hXY : Y ⊓ Subgroup.normalizer (E : Set G) = X) :
    torusImage E Y = (conjAut E X hX).range := by
  ext φ
  simp only [torusImage, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : (x : G) ∈ Y ⊓ Subgroup.normalizer (E : Set G) := Subgroup.mem_inf.2 ⟨hx, x.2⟩
    rw [hXY] at hmem
    exact ⟨⟨x.1, hmem⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hmem : (y : G) ∈ Y ⊓ Subgroup.normalizer (E : Set G) := by rw [hXY]; exact y.2
    exact ⟨Subgroup.inclusion hX y, (Subgroup.mem_inf.1 hmem).1, rfl⟩

theorem mem_torusImage_iff {E Y : Subgroup G} {φ : MulAut E} :
    φ ∈ torusImage E Y ↔ ∃ (x : G) (_ : x ∈ Y) (hx : x ∈ Subgroup.normalizer (E : Set G)),
      E.normalizerMonoidHom ⟨x, hx⟩ = φ := by
  simp only [torusImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, x.2, rfl⟩
  · rintro ⟨x, hxY, hx, rfl⟩
    exact ⟨⟨x, hx⟩, hxY, rfl⟩

theorem mem_normalizer_inf {E L : Subgroup G} {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) :
    y ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hyL hyE ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hyE h, hyL h]

theorem coe_normalizerMonoidHom_restrict {E F : Subgroup G} (hFE : F ≤ E) {y : G}
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (f : F) :
    ((F.normalizerMonoidHom ⟨y, hyF⟩ f : F) : G) =
      ((E.normalizerMonoidHom ⟨y, hyE⟩ ⟨f, hFE f.2⟩ : E) : G) := rfl

theorem rowWeylIso_of_mulEquiv {X X' : Subgroup G} {Γ : Subgroup (MulAut X)}
    {Γ' : Subgroup (MulAut X')} (e : Γ ≃* Γ') {r : ℕ} (h : RowWeylIso X' Γ' r) :
    RowWeylIso X Γ r := by
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
  · exact h.elim
  all_goals first | exact h.elim | exact h.map (e.trans ·)

theorem nontrivial_of_rowWeylIso {X : Subgroup G} {Γ : Subgroup (MulAut X)} {r : ℕ}
    (h : RowWeylIso X Γ r) : Nontrivial Γ := by
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
  · exact h.elim
  all_goals first | exact h.elim | exact (h.elim fun e => e.symm.injective.nontrivial)

theorem rowRank_eq_two {r : ℕ} (h1 : 1 ≤ r) (h8 : r ≤ 8) : RowRank r = 2 := by
  interval_cases r <;> rfl

theorem rowRank_eq_three {r : ℕ} (h9 : 9 ≤ r) (h12 : r ≤ 12) (h11 : r ≠ 11) : RowRank r = 3 := by
  interval_cases r <;> first | rfl | exact absurd rfl h11

theorem exists_mulEquiv_of_ker_eq {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : X →* Z) {Γ₁ : Subgroup Y} {Γ₂ : Subgroup Z} (h₁ : Γ₁ = f.range)
    (h₂ : Γ₂ = g.range) (hker : f.ker = g.ker) :
    ∃ e : Γ₁ ≃* Γ₂, ∀ (γ : Γ₁) (x : X), f x = γ.1 → (e γ).1 = g x := by
  subst h₁ h₂
  refine ⟨(QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange g)),
    fun γ x hx => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivRange f).symm γ = (x : X ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hx.symm
  show ((QuotientGroup.quotientKerEquivRange g)
    (QuotientGroup.quotientMulEquivOfEq hker ((QuotientGroup.quotientKerEquivRange f).symm γ))).1
      = g x
  rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem eq_closure_of_mulEquiv {M M' : Type*} [Group M] [Group M'] {H : Subgroup M}
    {H' : Subgroup M'} (e : H ≃* H') {P : M → Prop} {P' : M' → Prop}
    (hP : ∀ h : H, P h.1 ↔ P' (e h).1)
    (h' : H' = Subgroup.closure {t | t ∈ H' ∧ P' t}) :
    H = Subgroup.closure {t | t ∈ H ∧ P t} := by
  refine le_antisymm (fun x hx => ?_) ((Subgroup.closure_le H).2 fun t ht => ht.1)
  have key : ∀ y ∈ Subgroup.closure {t | t ∈ H' ∧ P' t}, ∃ hy : y ∈ H',
      (e.symm ⟨y, hy⟩).1 ∈ Subgroup.closure {t | t ∈ H ∧ P t} := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      refine ⟨hy.1, Subgroup.subset_closure ⟨(e.symm ⟨y, hy.1⟩).2, ?_⟩⟩
      rw [hP, MulEquiv.apply_symm_apply]
      exact hy.2
    | one =>
      refine ⟨H'.one_mem, ?_⟩
      have : (⟨1, H'.one_mem⟩ : H') = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul y z _ _ hy hz =>
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨hz1, hz2⟩ := hz
      refine ⟨H'.mul_mem hy1 hz1, ?_⟩
      have : (⟨y * z, H'.mul_mem hy1 hz1⟩ : H') = ⟨y, hy1⟩ * ⟨z, hz1⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ hy2 hz2
    | inv y _ hy =>
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨H'.inv_mem hy1, ?_⟩
      have : (⟨y⁻¹, H'.inv_mem hy1⟩ : H') = (⟨y, hy1⟩ : H')⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ hy2
  obtain ⟨hy, hmem⟩ := key (e ⟨x, hx⟩).1 (h' ▸ (e ⟨x, hx⟩).2)
  have : e.symm ⟨(e ⟨x, hx⟩).1, hy⟩ = ⟨x, hx⟩ := e.symm_apply_apply ⟨x, hx⟩
  rw [this] at hmem
  exact hmem

theorem autMovedInG_eq_closure (E : Subgroup G) (φ : MulAut E) :
    autMovedInG E φ =
      Subgroup.closure (Set.range fun e : E => ((φ e : E) : G) * (e : G)⁻¹) := by
  unfold autMovedInG autMoved
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem natCard_autMovedInG (E : Subgroup G) (φ : MulAut E) :
    Nat.card (autMovedInG E φ) = Nat.card (autMoved E φ) :=
  (Nat.card_congr (Subgroup.equivMapOfInjective _ _ E.subtype_injective).toEquiv).symm

theorem autMovedInG_normalizerMonoidHom_le {E F : Subgroup G} (hFE : F ≤ E) {y : G}
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    autMovedInG F (F.normalizerMonoidHom ⟨y, hyF⟩) ≤
      autMovedInG E (E.normalizerMonoidHom ⟨y, hyE⟩) := by
  rw [autMovedInG_eq_closure, autMovedInG_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro g ⟨f, rfl⟩
  exact ⟨⟨f, hFE f.2⟩, rfl⟩

structure Restr (c : G) (L E F : Subgroup G) : Prop where
  F_eq : F = E ⊓ L
  E_eq : E = F ⊔ Subgroup.zpowers c
  comm : ∀ l ∈ L, c * l = l * c

namespace Restr

variable {c : G} {L E F : Subgroup G}

theorem F_le_E (R : Restr c L E F) : F ≤ E := by rw [R.F_eq]; exact inf_le_left

theorem F_le_L (R : Restr c L E F) : F ≤ L := by rw [R.F_eq]; exact inf_le_right

theorem zpowers_le (R : Restr c L E F) : Subgroup.zpowers c ≤ E := by
  rw [R.E_eq]; exact le_sup_right

theorem c_mem (R : Restr c L E F) : c ∈ E := R.zpowers_le (Subgroup.mem_zpowers c)

theorem commute_zpow (R : Restr c L E F) {x : G} (hx : x ∈ L) (i : ℤ) :
    x * c ^ i = c ^ i * x :=
  (Commute.zpow_right (R.comm x hx).symm i).eq

theorem exists_mul_zpow (R : Restr c L E F) {e : G} (he : e ∈ E) :
    ∃ f ∈ F, ∃ i : ℤ, e = f * c ^ i := by
  have hcomm : ∀ k ∈ F, ∀ l ∈ Subgroup.zpowers c, k * l = l * k := by
    intro k hk l hl
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    exact R.commute_zpow (R.F_le_L hk) i
  have : e ∈ F ⊔ Subgroup.zpowers c := by rw [← R.E_eq]; exact he
  obtain ⟨f, hf, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm this
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨f, hf, i, rfl⟩

theorem mul_zpow_mem (R : Restr c L E F) {f : G} (hf : f ∈ F) (i : ℤ) : f * c ^ i ∈ E :=
  E.mul_mem (R.F_le_E hf) (E.zpow_mem R.c_mem i)

theorem conj_zpow (R : Restr c L E F) {x : G} (hx : x ∈ L) (i : ℤ) :
    x * c ^ i * x⁻¹ = c ^ i := by
  rw [R.commute_zpow hx i]; group

theorem inf_normalizer_le (R : Restr c L E F) :
    L ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (F : Set G) := by
  refine le_normalizer_of_forall (fun r hr f hf => ?_)
  have hrE := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hr).2 f
  have hrL := (Subgroup.mem_inf.1 hr).1
  rw [R.F_eq] at hf ⊢
  obtain ⟨hfE, hfL⟩ := Subgroup.mem_inf.1 hf
  exact Subgroup.mem_inf.2 ⟨hrE.1 hfE, L.mul_mem (L.mul_mem hrL hfL) (L.inv_mem hrL)⟩

theorem inf_normalizer_ge (R : Restr c L E F) :
    L ⊓ Subgroup.normalizer (F : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  refine le_normalizer_of_forall (fun r hr e he => ?_)
  obtain ⟨f, hf, i, rfl⟩ := R.exists_mul_zpow he
  have hrL := (Subgroup.mem_inf.1 hr).1
  have hrF := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hr).2 f
  have h1 : r * (f * c ^ i) * r⁻¹ = (r * f * r⁻¹) * (r * c ^ i * r⁻¹) := by group
  rw [h1, R.conj_zpow hrL i]
  exact R.mul_zpow_mem (hrF.1 hf) i

theorem inf_normalizer_eq (R : Restr c L E F) :
    L ⊓ Subgroup.normalizer (E : Set G) = L ⊓ Subgroup.normalizer (F : Set G) :=
  le_antisymm (le_inf inf_le_left R.inf_normalizer_le) (le_inf inf_le_left R.inf_normalizer_ge)

theorem inf_torusNormalizer_eq (R : Restr c L E F) :
    L ⊓ torusNormalizer E = L ⊓ torusNormalizer F :=
  R.inf_normalizer_eq

theorem torusInvariant_iff (R : Restr c L E F) {B : Subgroup G} :
    torusInvariant E L B ↔ torusInvariant F L B := by
  unfold torusInvariant
  rw [R.inf_torusNormalizer_eq]

theorem ker_conjAut_eq (R : Restr c L E F) {X : Subgroup G} (hXL : X ≤ L)
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hXF : X ≤ Subgroup.normalizer (F : Set G)) :
    (conjAut E X hXE).ker = (conjAut F X hXF).ker := by
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, conjAut_eq_one_iff, conjAut_eq_one_iff]
  constructor
  · intro h f hf
    exact h f (R.F_le_E hf)
  · intro h e he
    obtain ⟨f, hf, i, rfl⟩ := R.exists_mul_zpow he
    have h1 : (y : G) * (f * c ^ i) * (y : G)⁻¹ =
        ((y : G) * f * (y : G)⁻¹) * ((y : G) * c ^ i * (y : G)⁻¹) := by group
    rw [h1, R.conj_zpow (hXL y.2) i, h f hf]

theorem exists_resE (R : Restr c L E F) :
    ∃ e : torusImage E L ≃* torusImage F L, ∀ γ : torusImage E L,
      ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G))
        (hxF : x ∈ Subgroup.normalizer (F : Set G)),
        (γ : MulAut E) = E.normalizerMonoidHom ⟨x, hxE⟩ ∧
          ((e γ : torusImage F L) : MulAut F) = F.normalizerMonoidHom ⟨x, hxF⟩ := by
  set X : Subgroup G := L ⊓ Subgroup.normalizer (E : Set G) with hX
  have hXE : X ≤ Subgroup.normalizer (E : Set G) := inf_le_right
  have hXF : X ≤ Subgroup.normalizer (F : Set G) := R.inf_normalizer_le
  have hXL : X ≤ L := inf_le_left
  have h1 : torusImage E L = (conjAut E X hXE).range := torusImage_eq_range hXE rfl
  have h2 : torusImage F L = (conjAut F X hXF).range :=
    torusImage_eq_range hXF R.inf_normalizer_eq.symm
  obtain ⟨e, he⟩ := exists_mulEquiv_of_ker_eq (conjAut E X hXE) (conjAut F X hXF) h1 h2
    (R.ker_conjAut_eq hXL hXE hXF)
  refine ⟨e, fun γ => ?_⟩
  obtain ⟨y, hy⟩ : (γ : MulAut E) ∈ (conjAut E X hXE).range := h1 ▸ γ.2
  exact ⟨y, hXL y.2, hXE y.2, hXF y.2, hy.symm, he γ y hy⟩

theorem autMovedInG_eq (R : Restr c L E F) {y : G} (hyc : y * c = c * y)
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    autMovedInG E (E.normalizerMonoidHom ⟨y, hyE⟩) =
      autMovedInG F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  refine le_antisymm ?_ (autMovedInG_normalizerMonoidHom_le R.F_le_E hyE hyF)
  rw [autMovedInG_eq_closure, autMovedInG_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro g ⟨e, rfl⟩
  obtain ⟨f, hf, i, hfi⟩ := R.exists_mul_zpow e.2
  refine ⟨⟨f, hf⟩, ?_⟩
  have hz : y * c ^ i * y⁻¹ = c ^ i := by
    rw [(Commute.zpow_right hyc i).eq]; group
  have he : (e : G) = f * c ^ i := hfi
  show y * f * y⁻¹ * f⁻¹ = y * (e : G) * y⁻¹ * (e : G)⁻¹
  rw [he]
  calc y * f * y⁻¹ * f⁻¹ = (y * f * y⁻¹) * (y * c ^ i * y⁻¹) * (c ^ i)⁻¹ * f⁻¹ := by
        rw [hz]; group
    _ = y * (f * c ^ i) * y⁻¹ * (f * c ^ i)⁻¹ := by group

theorem exists_resE_isAutReflection (p : ℕ) (R : Restr c L E F) :
    ∃ e : torusImage E L ≃* torusImage F L, ∀ γ : torusImage E L,
      IsAutReflection p E (γ : MulAut E) ↔
        IsAutReflection p F ((e γ : torusImage F L) : MulAut F) := by
  obtain ⟨e, he⟩ := R.exists_resE
  refine ⟨e, fun γ => ?_⟩
  obtain ⟨x, hxL, hxE, hxF, h1, h2⟩ := he γ
  have hmoved : autMovedInG E (γ : MulAut E) =
      autMovedInG F ((e γ : torusImage F L) : MulAut F) := by
    rw [h1, h2]
    exact R.autMovedInG_eq (R.comm x hxL).symm hxE hxF
  have hcard : Nat.card (autMoved E (γ : MulAut E)) =
      Nat.card (autMoved F ((e γ : torusImage F L) : MulAut F)) := by
    rw [← natCard_autMovedInG, ← natCard_autMovedInG, hmoved]
  have hord : orderOf (γ : MulAut E) = orderOf ((e γ : torusImage F L) : MulAut F) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  unfold IsAutReflection
  rw [hord, hcard]

theorem torusImage_eq_closure_reflections (p : ℕ) (R : Restr c L E F)
    (h : torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t}) :
    torusImage E L = Subgroup.closure {t | t ∈ torusImage E L ∧ IsAutReflection p E t} := by
  obtain ⟨e, he⟩ := R.exists_resE_isAutReflection p
  exact eq_closure_of_mulEquiv e he h

theorem rowWeylIso (R : Restr c L E F) {r : ℕ} (h : RowWeylIso F (torusImage F L) r) :
    RowWeylIso E (torusImage E L) r := by
  obtain ⟨e, -⟩ := R.exists_resE
  exact rowWeylIso_of_mulEquiv e h

end Restr

theorem commutator_le_left (E L : Subgroup G) : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E := by
  rw [Subgroup.commutator_le]
  intro e he w hw
  have hwE : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
  have h1 := (Subgroup.mem_normalizer_iff.1 hwE e⁻¹).1 (E.inv_mem he)
  have h2 := E.mul_mem he h1
  simpa [commutatorElement_def, mul_assoc] using h2

theorem torusInvariant_commutator (E L : Subgroup G) :
    torusInvariant E L ⁅E, L ⊓ torusNormalizer E⁆ := by
  intro w hw b hb
  have hwE : w ∈ Subgroup.normalizer (E : Set G) := (Subgroup.mem_inf.1 hw).2
  have key : ⁅E, L ⊓ torusNormalizer E⁆ ≤
      (⁅E, L ⊓ torusNormalizer E⁆).comap (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro e he w' hw'
    rw [Subgroup.mem_comap]
    have h1 : (MulAut.conj w).toMonoidHom ⁅e, w'⁆ = ⁅w * e * w⁻¹, w * w' * w⁻¹⁆ := by
      simp only [commutatorElement_def]
      simp [MulAut.conj_apply]
      group
    rw [h1]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hwE e).1 he)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hw') (Subgroup.inv_mem _ hw))
  have := key hb
  simpa [MulAut.conj_apply] using this

theorem exists_moved_of_torusImage_ne_bot {E L : Subgroup G} (h : torusImage E L ≠ ⊥) :
    ∃ w ∈ L ⊓ torusNormalizer E, ∃ e ∈ E, w * e * w⁻¹ ≠ e := by
  obtain ⟨⟨φ, hφ⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  obtain ⟨x, hxL, hxE, rfl⟩ := mem_torusImage_iff.1 hφ
  by_contra hcon
  refine hne (Subtype.ext (MulEquiv.ext fun e => Subtype.ext ?_))
  by_contra hne'
  exact hcon ⟨x, Subgroup.mem_inf.2 ⟨hxL, hxE⟩, e, e.2, hne'⟩

theorem commutator_ne_bot_of_moved {E L : Subgroup G}
    (h : ∃ w ∈ L ⊓ torusNormalizer E, ∃ e ∈ E, w * e * w⁻¹ ≠ e) :
    ⁅E, L ⊓ torusNormalizer E⁆ ≠ ⊥ := by
  obtain ⟨w, hw, e, he, hne⟩ := h
  intro hbot
  have hmem := Subgroup.commutator_mem_commutator he hw
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hne (by rw [← hmem]; group)

theorem zpowers_inf_eq_bot [Finite G] {p : ℕ} (hp : p.Prime) {c : G} (hc : orderOf c = p)
    {K : Subgroup G} (hcK : c ∉ K) : Subgroup.zpowers c ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyc, hyK⟩ := Subgroup.mem_inf.1 hy
  by_contra hne
  have hz := zpowers_eq_of_mem_of_ne_one hp hc hyc (by simpa using hne)
  refine hcK (Subgroup.zpowers_le.2 hyK ?_)
  rw [hz]
  exact Subgroup.mem_zpowers c

namespace Restr

variable {c : G} {L E F : Subgroup G}

theorem card_E [Finite G] {p : ℕ} (R : Restr c L E F) (hp : p.Prime) (hc : orderOf c = p)
    (hcL : c ∉ L) : Nat.card E = Nat.card F * p := by
  have hcF : c ∉ F := fun h => hcL (R.F_le_L h)
  have hfp : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
  have := card_sup_zpowers hp F hfp hcF fun f hf => (R.comm f (R.F_le_L hf)).symm
  rw [← R.E_eq] at this
  exact this

theorem commutator_le_F (R : Restr c L E F) : ⁅E, L ⊓ torusNormalizer E⁆ ≤ F := by
  rw [Subgroup.commutator_le]
  intro e he w hw
  obtain ⟨f, hf, i, rfl⟩ := R.exists_mul_zpow he
  have hwL := (Subgroup.mem_inf.1 hw).1
  have hwF : w ∈ Subgroup.normalizer (F : Set G) :=
    R.inf_normalizer_le (Subgroup.mem_inf.2 ⟨hwL, (Subgroup.mem_inf.1 hw).2⟩)
  have hzw : c ^ i * w * (c ^ i)⁻¹ = w := by
    rw [← R.commute_zpow hwL i]; group
  have h1 : ⁅f * c ^ i, w⁆ = f * (w * f⁻¹ * w⁻¹) := by
    calc ⁅f * c ^ i, w⁆ = f * (c ^ i * w * (c ^ i)⁻¹) * f⁻¹ * w⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = f * (w * f⁻¹ * w⁻¹) := by rw [hzw]; group
  rw [h1]
  exact F.mul_mem hf ((Subgroup.mem_normalizer_iff.1 hwF f⁻¹).1 (F.inv_mem hf))

theorem commutator_eq_F (R : Restr c L E F)
    (hirr : ∀ B : Subgroup G, B ≤ F → torusInvariant F L B → B = ⊥ ∨ B = F)
    (hnt : torusImage F L ≠ ⊥) : ⁅E, L ⊓ torusNormalizer E⁆ = F := by
  rcases hirr _ R.commutator_le_F
    (R.torusInvariant_iff.1 (torusInvariant_commutator E L)) with h | h
  · exfalso
    obtain ⟨w, hw, f, hf, hne⟩ := exists_moved_of_torusImage_ne_bot hnt
    refine commutator_ne_bot_of_moved ⟨w, ?_, f, R.F_le_E hf, hne⟩ h
    rw [R.inf_torusNormalizer_eq]
    exact hw
  · exact h

theorem node124_generic [Finite G] {p : ℕ} (R : Restr c L E F) (hp : p.Prime) (hc : orderOf c = p)
    (hcL : c ∉ L) (hpow : ∀ x ∈ E, x ^ p = 1)
    (hirr : ∀ B : Subgroup G, B ≤ F → torusInvariant F L B → B = ⊥ ∨ B = F)
    (hnt : torusImage F L ≠ ⊥) (hFcard : p ^ 2 ≤ Nat.card F) :
    (∀ B : Subgroup G, B ≤ E → torusInvariant E L B → B ≠ ⊥ → B ≠ E →
      B = Subgroup.zpowers c ∨ B = ⁅E, L ⊓ torusNormalizer E⁆) ∧
    (E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ ∧
      Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥) := by
  have hM := R.commutator_eq_F hirr hnt
  rw [hM]
  have hcF : c ∉ F := fun h => hcL (R.F_le_L h)
  refine ⟨fun B hBE hB hB0 hBne => ?_, by rw [sup_comm]; exact R.E_eq,
    zpowers_inf_eq_bot hp hc hcF⟩
  have hB'inv : torusInvariant F L (B ⊓ F) := by
    intro w hw b hb
    have hwE : w ∈ L ⊓ torusNormalizer E := by rw [R.inf_torusNormalizer_eq]; exact hw
    obtain ⟨hb1, hb2⟩ := Subgroup.mem_inf.1 hb
    have hwF : w ∈ Subgroup.normalizer (F : Set G) := (Subgroup.mem_inf.1 hw).2
    exact Subgroup.mem_inf.2 ⟨hB w hwE b hb1, (Subgroup.mem_normalizer_iff.1 hwF b).1 hb2⟩
  rcases hirr (B ⊓ F) inf_le_right hB'inv with h0 | hFB
  · left
    have hBc : ∀ b ∈ B, b ∈ Subgroup.zpowers c := by
      intro b hb
      obtain ⟨f, hf, i, rfl⟩ := R.exists_mul_zpow (hBE hb)
      have hfix : ∀ w ∈ L ⊓ torusNormalizer F, w * f * w⁻¹ = f := by
        intro w hw
        have hwE : w ∈ L ⊓ torusNormalizer E := by rw [R.inf_torusNormalizer_eq]; exact hw
        have hwL := (Subgroup.mem_inf.1 hw).1
        have hwF : w ∈ Subgroup.normalizer (F : Set G) := (Subgroup.mem_inf.1 hw).2
        have h1 : w * (f * c ^ i) * w⁻¹ * (f * c ^ i)⁻¹ ∈ B :=
          B.mul_mem (hB w hwE _ hb) (B.inv_mem hb)
        have h2 : w * (f * c ^ i) * w⁻¹ * (f * c ^ i)⁻¹ = (w * f * w⁻¹) * f⁻¹ := by
          have h3 : w * (f * c ^ i) * w⁻¹ = (w * f * w⁻¹) * (w * c ^ i * w⁻¹) := by group
          rw [h3, R.conj_zpow hwL i]
          group
        have h3 : (w * f * w⁻¹) * f⁻¹ ∈ F :=
          F.mul_mem ((Subgroup.mem_normalizer_iff.1 hwF f).1 hf) (F.inv_mem hf)
        have h4 : (w * f * w⁻¹) * f⁻¹ ∈ B ⊓ F := Subgroup.mem_inf.2 ⟨h2 ▸ h1, h3⟩
        rw [h0, Subgroup.mem_bot] at h4
        exact mul_inv_eq_one.1 h4
      have hinv : torusInvariant F L (Subgroup.zpowers f) := by
        intro w hw b hb'
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
        have : w * f ^ k * w⁻¹ = f ^ k := by
          rw [← _root_.conj_zpow (a := w) (b := f) (i := k), hfix w hw]
        rw [this]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers f) k
      have hf1 : f = 1 := by
        rcases hirr (Subgroup.zpowers f) (Subgroup.zpowers_le.2 hf) hinv with h | h
        · exact Subgroup.zpowers_eq_bot.1 h
        · exfalso
          have hfp : f ^ p = 1 := hpow f (R.F_le_E hf)
          have h1 : Nat.card F ≤ p := by
            rw [← h, Nat.card_zpowers]
            exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hfp)
          have h2 : p < p ^ 2 := by nlinarith [hp.one_lt]
          omega
      rw [hf1, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i
    have hle : B ≤ Subgroup.zpowers c := hBc
    have hdvd : Nat.card B ∣ p := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hc] at this
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq B h1) hB0
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hc, h1])
  · right
    have hFB' : F ≤ B := inf_eq_right.1 hFB
    have hcardE := R.card_E hp hc hcL
    have hn : 0 < Nat.card F := Nat.card_pos
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hFB'
    have hBdvd : Nat.card B ∣ Nat.card E := Subgroup.card_dvd_of_le hBE
    rw [hk, hcardE] at hBdvd
    have hkp : k ∣ p := Nat.dvd_of_mul_dvd_mul_left hn hBdvd
    rcases (Nat.dvd_prime hp).1 hkp with h | h
    · rw [h, mul_one] at hk
      exact (Subgroup.eq_of_le_of_card_ge hFB' hk.le).symm
    · rw [h] at hk
      exact absurd (Subgroup.eq_of_le_of_card_ge hBE (by rw [hk, hcardE])) hBne

end Restr

theorem pow_eq_one_of_commutator_le {p : ℕ} {c : G} {L E : Subgroup G} (hcp : c ^ p = 1)
    (hcL : ∀ l ∈ L, c * l = l * c) (hX : ⁅E, L ⊓ torusNormalizer E⁆ ≤ Subgroup.zpowers c) :
    ∀ γ ∈ torusImage E L, γ ^ p = 1 := by
  intro γ hγ
  obtain ⟨x, hxL, hxE, rfl⟩ := mem_torusImage_iff.1 hγ
  have hxc : ∀ n ∈ Subgroup.zpowers c, x * n * x⁻¹ = n := by
    intro n hn
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : x * c ^ j = c ^ j * x := (Commute.zpow_right (hcL x hxL).symm j).eq
    rw [this]; group
  have claim : ∀ (e n : G), n ∈ Subgroup.zpowers c → x * e * x⁻¹ = n * e →
      ∀ k : ℕ, x ^ k * e * (x ^ k)⁻¹ = n ^ k * e := by
    intro e n hn hxe k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * e * (x ^ (k + 1))⁻¹ = x * (x ^ k * e * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * (n ^ k * e) * x⁻¹ := by rw [ih]
        _ = (x * n ^ k * x⁻¹) * (x * e * x⁻¹) := by group
        _ = n ^ k * (n * e) := by rw [hxc _ (Subgroup.pow_mem _ hn k), hxe]
        _ = n ^ (k + 1) * e := by rw [pow_succ, mul_assoc]
  have key : ∀ e ∈ E, ∃ n ∈ Subgroup.zpowers c, ∀ k : ℕ, x ^ k * e * (x ^ k)⁻¹ = n ^ k * e := by
    intro e he
    have hn : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers c := by
      have h1 := hX (Subgroup.commutator_mem_commutator he (Subgroup.mem_inf.2 ⟨hxL, hxE⟩))
      have h2 := Subgroup.inv_mem _ h1
      rwa [commutatorElement_def, ← commutatorElement_def, commutatorElement_inv] at h2
    exact ⟨_, hn, claim e _ hn (by group)⟩
  have hnp : ∀ n ∈ Subgroup.zpowers c, n ^ p = 1 := fun n hn =>
    orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_mem_zpowers hn).trans (orderOf_dvd_of_pow_eq_one hcp))
  have hp1 : (E.normalizerMonoidHom ⟨x, hxE⟩) ^ p = E.normalizerMonoidHom (⟨x, hxE⟩ ^ p) :=
    (map_pow _ _ _).symm
  rw [hp1]
  refine MulEquiv.ext fun e => Subtype.ext ?_
  obtain ⟨n, hn, h1⟩ := key e e.2
  show ((⟨x, hxE⟩ ^ p : Subgroup.normalizer (E : Set G)) : G) * e *
    ((⟨x, hxE⟩ ^ p : Subgroup.normalizer (E : Set G)) : G)⁻¹ = e
  rw [Subgroup.coe_pow, h1 p, hnp n hn, one_mul]

theorem not_commutator_le_zpowers_of_perm_five {c : G} {L E : Subgroup G} (hcp : c ^ 5 = 1)
    (hcL : ∀ l ∈ L, c * l = l * c) (hW : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 5))) :
    ¬ ⁅E, L ⊓ torusNormalizer E⁆ ≤ Subgroup.zpowers c := by
  intro hX
  obtain ⟨e⟩ := hW
  set γ := e.symm (Equiv.swap 0 1) with hγ
  have h1 := pow_eq_one_of_commutator_le hcp hcL hX γ γ.2
  have h2 : γ ^ 5 = 1 := Subtype.ext (by simpa using h1)
  have h3 : (Equiv.swap (0 : Fin 5) 1) ^ 5 = 1 := by
    have := congrArg e h2
    rwa [map_pow, hγ, MulEquiv.apply_symm_apply, map_one] at this
  revert h3
  decide

end CFSG.RankThree.PartOne.Sec12Three
