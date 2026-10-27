module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15419
public import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.Background.B2Factorization
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf [Finite G] {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' (D := K) (T := H) hHK
  have h2 := Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
  have h3 := Subgroup.relIndex_mul_card (H := K) (K := H)
  rw [inf_eq_left.mpr le_sup_right, h1] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem centralizer_sup_eq (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))) ?_
  rw [Subgroup.le_centralizer_iff]
  exact sup_le (Subgroup.le_centralizer_iff.mp inf_le_left)
    (Subgroup.le_centralizer_iff.mp inf_le_right)

theorem eq_bot_or_eq_of_card_eq_four [Finite G] {U D X : Subgroup G} (hU : Nat.card U = 4)
    (hDU : D ≤ U) (hDX : X ≤ Subgroup.normalizer (D : Set G))
    (hfix : U ⊓ Subgroup.centralizer (X : Set G) = ⊥) : D = ⊥ ∨ D = U := by
  have hdvd : Nat.card D ∣ 4 := hU ▸ Subgroup.card_dvd_of_le hDU
  have hle : Nat.card D ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card D := Nat.card_pos
  interval_cases hc : Nat.card D
  · exact Or.inl (Subgroup.card_eq_one.mp hc)
  · exfalso
    have hDC : D ≤ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      intro x hx
      exact mem_centralizer_of_card_eq_two hc (hDX hx)
    have hbot : D = ⊥ := le_bot_iff.mp (hfix ▸ le_inf hDU hDC)
    rw [hbot, Subgroup.card_bot] at hc
    omega
  · norm_num at hdvd
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hDU (by rw [hU, hc]))

theorem eq_or_eq_of_le_sup [Finite G] {U₁ U₂ W X₁ : Subgroup G}
    (hcomm : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a) (h₁ : Nat.card U₁ = 4) (h₂ : Nat.card U₂ = 4)
    (hN₁ : X₁ ≤ Subgroup.normalizer (U₁ : Set G)) (hC₁ : X₁ ≤ Subgroup.centralizer (U₂ : Set G))
    (hF₁ : U₁ ⊓ Subgroup.centralizer (X₁ : Set G) = ⊥) (hW : W ≤ U₁ ⊔ U₂)
    (hW4 : Nat.card W = 4) (hWN : X₁ ≤ Subgroup.normalizer (W : Set G)) : W = U₁ ∨ W = U₂ := by
  have hN : X₁ ≤ Subgroup.normalizer ((W ⊓ U₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hWN hx, hN₁ hx⟩
  rcases eq_bot_or_eq_of_card_eq_four h₁ inf_le_right hN hF₁ with hbot | heq
  · right
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [h₂, hW4])
    intro w hw
    have hU₂N : U₂ ≤ Subgroup.normalizer (U₁ : Set G) := by
      intro b hb
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    have hw' : w ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := hW hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U₁ U₂ hU₂N] at hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
    have hfix : a ∈ U₁ ⊓ Subgroup.centralizer (X₁ : Set G) := by
      refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hxb : x * b * x⁻¹ = b := by
        have hbx := Subgroup.mem_centralizer_iff.mp (hC₁ hx) b hb
        calc x * b * x⁻¹ = b * x * x⁻¹ := by rw [hbx]
          _ = b := by group
      have hxa : x * a * x⁻¹ ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hN₁ hx) a).mp ha
      have hxw : x * (a * b) * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWN hx) _).mp hw
      have hd : x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * x⁻¹ * a⁻¹ := by
        calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) * b⁻¹ * a⁻¹ := by
              group
          _ = x * a * x⁻¹ * a⁻¹ := by rw [hxb]; group
      have hmem : x * a * x⁻¹ * a⁻¹ ∈ W ⊓ U₁ :=
        ⟨hd ▸ W.mul_mem hxw (W.inv_mem hw), U₁.mul_mem hxa (U₁.inv_mem ha)⟩
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      calc x * a = x * a * x⁻¹ * x := by group
        _ = a * x := by rw [hmem]
    rw [hF₁, Subgroup.mem_bot] at hfix
    rw [hfix, one_mul]
    exact hb
  · left
    exact (Subgroup.eq_of_le_of_card_ge (heq ▸ inf_le_left) (by rw [h₁, hW4])).symm

theorem exists_mem_omegaOneCenter_of_le [Finite G] {T D : Subgroup G} (hT : IsPGroup 2 T)
    (hDT : D ≤ T) (hTD : T ≤ Subgroup.normalizer (D : Set G)) (hD2 : ∀ d ∈ D, d ^ 2 = 1)
    (hD : D ≠ ⊥) : ∃ d ∈ D, d ≠ 1 ∧ d ∈ quasithinOmegaOneCenter T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 2 D := hT.to_le hDT
  have h2 : 2 ∣ Nat.card D := by
    obtain ⟨k, hk⟩ := hDp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hD (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨d, hd, hd1, hdC⟩ := exists_ne_one_mem_centralizer_of_isPGroup hT hTD h2
  exact ⟨d, hd, hd1, mem_quasithinOmegaOneCenter_iff.mpr ⟨hDT hd, hdC, hD2 d hd⟩⟩

theorem isElemAbelian_of_le' {p : ℕ} {A B : Subgroup G} (hB : IsElemAbelian p B) (hAB : A ≤ B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem sup_eq_of_relIndex_eq_two [Finite G] {A B C : Subgroup G} (hAB : A ≤ B)
    (hidx : A.relIndex B = 2) (hCB : C ≤ B) (hCA : ¬ C ≤ A) : A ⊔ C = B := by
  have h1 : A.relIndex (A ⊔ C) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hCA (le_sup_right.trans h)
  have htower := Subgroup.relIndex_mul_relIndex A (A ⊔ C) B le_sup_left (sup_le hAB hCB)
  rw [hidx] at htower
  have h2 : (A ⊔ C).relIndex B = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨_, htower.symm⟩ with h | h
    · exact absurd h h1
    · rw [h] at htower
      omega
  exact le_antisymm (sup_le hAB hCB) (Subgroup.relIndex_eq_one.mp h2)

theorem mem_normalizer_map_conj {H : Subgroup G} {t g : G}
    (h : t⁻¹ * g * t ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h ⊢
  have e : (MulAut.conj g).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (MulAut.conj (t⁻¹ * g * t)).toMonoidHom := by
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    group
  change ((H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom) = _
  rw [Subgroup.map_map, e, ← Subgroup.map_map]
  congr 1

end General

section Family

variable {G : Type*} [Group G] {T Y : Subgroup G}

theorem IsYFamily.le_normalizer (hY : IsYFamily T Y) : T ≤ Subgroup.normalizer (Y : Set G) := by
  rcases hY.1 with h | h
  · exact h.2.1
  · exact h.2.1

theorem IsYFamily.eq_oTwoUpper (hY : IsYFamily T Y) : Y = oTwoUpper Y := by
  rcases hY.1 with h | h
  · exact h.1
  · exact h.1

theorem IsYFamily.pCoreOf_sup_ne_bot (hY : IsYFamily T Y) : pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
  rcases hY.1 with h | h
  · exact h.2.2.1
  · exact h.2.2.1.2

theorem IsYFamily.exists_inM {G : Type} [Group G] [Finite G] {T Y : Subgroup G}
    (hY : IsYFamily T Y) : ∃ M : Subgroup G, InM T M ∧ Y ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge
    (⟨_, hY.pCoreOf_sup_ne_bot, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Y ⊔ T), rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Y ⊔ T) : Set G)))
  have hle := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T)).trans hNM
  exact ⟨M, ⟨hM, le_sup_right.trans hle⟩, le_sup_left.trans hle⟩

end Family

structure Hyp15418 (G : Type) [Group G] [Finite G] (T : Subgroup G) : Prop where
  hyp : MultipleCentralizerHypothesis G T
  hnot : ¬ IsLThreeTwoOrASix G
  h8 : Stmt1548 G T
  h12 : Stmt15412 G T
  h14 : Stmt15414 G T
  h16 : Stmt15416 G T
  h17 : Stmt15417 G T

structure Config15418 (G : Type) [Group G] (T : Subgroup G) where
  M₁ : Subgroup G
  M₂ : Subgroup G
  Y : Subgroup G
  X : Subgroup G
  X₁ : Subgroup G
  X₂ : Subgroup G
  inM₁ : InM T M₁
  inM₂ : InM T M₂
  ne : M₁ ≠ M₂
  famY : IsYFamily T Y
  le_Y : Y ≤ M₁
  three : (pCoreOf 2 Y).relIndex Y = 3
  famX : IsYFamily T X
  le_X : X ≤ M₂
  dataX : IsSixTwoData T M₂ X X₁ X₂

section ESection

variable {G : Type*} [Group G]

theorem eOf_le_centerOf_thompsonJ (T : Subgroup G) : eOf T ≤ centerOf (thompsonJ T) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem eOf_mul_comm {T : Subgroup G} {a b : G} (ha : a ∈ eOf T) (hb : b ∈ eOf T) :
    a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (eOf_le_centerOf_thompsonJ T ha).2 b
    (eOf_le_centerOf_thompsonJ T hb).1).symm

theorem eOf_sq_eq_one {T : Subgroup G} {a : G} (ha : a ∈ eOf T) : a ^ 2 = 1 := by
  have ha' := ha
  unfold eOf omegaOneCenterOf omegaOneOf at ha'
  induction ha' using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := eOf_mul_comm hx hy
    rw [Commute.mul_pow hxy, ihx hx, ihy hy, mul_one]
  | inv x hx ih => rw [inv_pow, ih hx, inv_one]

theorem eOf_le (T : Subgroup G) : eOf T ≤ T :=
  (eOf_le_centerOf_thompsonJ T).trans (inf_le_left.trans (thompsonJ_le_self T))

theorem eOf_le_baum (T : Subgroup G) : eOf T ≤ baum T := fun _ ha =>
  ⟨eOf_le T ha, Subgroup.mem_centralizer_iff.mpr fun _ hb => eOf_mul_comm hb ha⟩

theorem normalizer_le_normalizer_eOf (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (eOf T : Set G) :=
  (normalizer_le_normalizer_thompsonJ T).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ T))

theorem le_normalizer_eOf (T : Subgroup G) : T ≤ Subgroup.normalizer (eOf T : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_eOf T)

theorem thompsonJ_le_baum (T : Subgroup G) : thompsonJ T ≤ baum T := fun _ hx =>
  ⟨thompsonJ_le_self T hx, Subgroup.mem_centralizer_iff.mpr fun _ hb =>
    (Subgroup.mem_centralizer_iff.mp (eOf_le_centerOf_thompsonJ T hb).2 _ hx).symm⟩

variable [Finite G]

theorem thompsonJ_baum (T : Subgroup G) : thompsonJ (baum T) = thompsonJ T :=
  (thompsonJ_eq_of_le (thompsonJ_le_baum T) inf_le_left).symm

theorem eOf_baum (T : Subgroup G) : eOf (baum T) = eOf T := by
  unfold eOf
  rw [thompsonJ_baum]

theorem normalizer_baum_le_normalizer_eOf (T : Subgroup G) :
    Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (eOf T : Set G) := by
  rw [← eOf_baum T]
  exact normalizer_le_normalizer_eOf (baum T)

theorem omegaOneCenter_le_eOf' (T : Subgroup G) : quasithinOmegaOneCenter T ≤ eOf T := by
  rw [eOf, ← (omegaOne_centralizer_thompsonJ T).1]
  refine Subgroup.closure_mono ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  exact ⟨⟨hzT, Subgroup.centralizer_le (thompsonJ_le_self T) hzC⟩, hz2⟩

end ESection

theorem le_centralizer_omegaOneCenter {G : Type*} [Group G] (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  intro z hz
  exact (mem_quasithinOmegaOneCenter_iff.mp hz).2.1

theorem relIndex_ne_zero' {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 := fun h =>
  (Nat.card_pos (α := K)).ne' (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_card H K))

namespace Config15418

variable {G : Type} [Group G] {T : Subgroup G}

@[expose] def E₁ (c : Config15418 G T) : Subgroup G :=
  eOf T ⊓ Subgroup.centralizer (c.Y : Set G)

@[expose] def E₂ (c : Config15418 G T) : Subgroup G :=
  eOf T ⊓ Subgroup.centralizer (c.X₁ : Set G)

@[expose] def E₃ (c : Config15418 G T) : Subgroup G :=
  eOf T ⊓ Subgroup.centralizer (c.X₂ : Set G)

@[expose] def EX (c : Config15418 G T) : Subgroup G :=
  eOf T ⊓ Subgroup.centralizer (c.X : Set G)

@[expose] def E₀ (c : Config15418 G T) : Subgroup G := c.E₁ ⊓ c.E₂

variable (c : Config15418 G T)

theorem le_normalizer_Y : T ≤ Subgroup.normalizer (c.Y : Set G) := c.famY.le_normalizer

theorem le_normalizer_X : T ≤ Subgroup.normalizer (c.X : Set G) := c.famX.le_normalizer

theorem X₁_le : c.X₁ ≤ c.X := c.dataX.1 ▸ le_sup_left

theorem X₂_le : c.X₂ ≤ c.X := c.dataX.1 ▸ le_sup_right

theorem T_le_M₂ : T ≤ c.M₂ := c.inM₂.2

theorem X₁_ne_X₂ : c.X₁ ≠ c.X₂ := by
  intro h
  obtain ⟨-, -, -, -, -, -, hinf, h4, -⟩ := c.dataX
  rw [h, inf_idem] at hinf
  rw [h, hinf, Subgroup.card_bot] at h4
  omega

theorem X_le_normalizer_V₂ : c.X ≤ Subgroup.normalizer (VZ T c.M₂ : Set G) :=
  c.le_X.trans (le_normalizer_conjClosure _ _)

variable [Finite G]

section Hyp

variable (H : Hyp15418 G T)
include H

theorem M₁_eq : c.M₁ = Subgroup.normalizer (c.Y : Set G) :=
  ((H.h12 c.M₁ c.inM₁).2 c.Y c.famY c.le_Y).2.1

theorem uniqueY : IsUniqueM (c.Y ⊔ T) c.M₁ :=
  ((H.h12 c.M₁ c.inM₁).2 c.Y c.famY c.le_Y).2.2.1

theorem M₂_eq : c.M₂ = Subgroup.normalizer (c.X : Set G) :=
  ((H.h12 c.M₂ c.inM₂).2 c.X c.famX c.le_X).2.1

theorem uniqueX : IsUniqueM (c.X ⊔ T) c.M₂ :=
  ((H.h12 c.M₂ c.inM₂).2 c.X c.famX c.le_X).2.2.1

theorem eX_decomp :
    eOf T = eCentOf T c.X ⊔ (⁅VZ T c.M₂, c.X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ∧
      eCentOf T c.X ⊓ (⁅VZ T c.M₂, c.X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥ :=
  ⟨((H.h12 c.M₂ c.inM₂).2 c.X c.famX c.le_X).2.2.2.2.2.1.2.2.1,
    ((H.h12 c.M₂ c.inM₂).2 c.X c.famX c.le_X).2.2.2.2.2.1.2.2.2⟩

theorem relIndex_E₁ : c.E₁.relIndex (eOf T) = 2 := by
  have h6 := ((H.h12 c.M₁ c.inM₁).2 c.Y c.famY c.le_Y).2.2.2.2.2.2.1
  rcases h6 with ⟨-, -, h⟩ | ⟨h9, -⟩
  · exact h
  · rw [c.three] at h9
    omega

theorem isElemAbelian_V₂ : IsElemAbelian 2 (VZ T c.M₂) := isElemAbelian_VZ_of_inM H.hyp c.inM₂

theorem normalizer_le_M₁ {R : Subgroup G} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hYR : c.Y ⊔ T ≤ Subgroup.normalizer (R : Set G)) : Subgroup.normalizer (R : Set G) ≤ c.M₁ := by
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge
    (⟨R, hR, hR2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (R : Set G)))
  have := (c.uniqueY H).2 M ⟨hM, hYR.trans hNM⟩
  exact this ▸ hNM

theorem not_X₁_le_M₁ : ¬ c.X₁ ≤ c.M₁ :=
  not_le_of_sixTwoData c.inM₁ c.ne (c.uniqueX H) c.dataX (Or.inl rfl)

theorem not_Y_le_M₂ : ¬ c.Y ≤ c.M₂ := fun h =>
  c.ne ((c.uniqueY H).2 c.M₂ ⟨c.inM₂.1, sup_le h c.inM₂.2⟩).symm

theorem eq_bot_of_le_normalizer {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hYR : c.Y ⊔ T ≤ Subgroup.normalizer (R : Set G))
    (hXR : c.X₁ ≤ Subgroup.normalizer (R : Set G)) : R = ⊥ := by
  by_contra hR
  exact c.not_X₁_le_M₁ H (hXR.trans (c.normalizer_le_M₁ H hR hR2 hYR))

theorem card_Z : Nat.card (quasithinOmegaOneCenter T) = 4 := (H.h14 H.hnot).2

theorem card_Z_inf {W : Subgroup G} (hW : IsYFamily T W) :
    Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (W : Set G)) = 2 := by
  have h := Subgroup.relIndex_mul_card
    (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (W : Set G)) (quasithinOmegaOneCenter T)
  rw [(H.h14 H.hnot).1 W hW, inf_eq_left.mpr inf_le_left, card_Z H] at h
  omega

omit H in
theorem Z_le_T : quasithinOmegaOneCenter T ≤ T :=
  (omegaOneCenter_le_eOf' T).trans (eOf_le T)

omit [Finite G] H in
theorem le_normalizer_centralizer {W : Subgroup G} (hW : T ≤ Subgroup.normalizer (W : Set G)) :
    T ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
  hW.trans (B2F.normalizer_le_normalizer_centralizer W)

theorem false_of_le_normalizer {R : Subgroup G} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hYR : c.Y ⊔ T ≤ Subgroup.normalizer (R : Set G))
    (hXR : c.X ⊔ T ≤ Subgroup.normalizer (R : Set G)) : False := by
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge
    (⟨R, hR, hR2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (R : Set G)))
  have h₁ := (c.uniqueY H).2 M ⟨hM, hYR.trans hNM⟩
  have h₂ := (c.uniqueX H).2 M ⟨hM, hXR.trans hNM⟩
  exact c.ne (h₁.symm.trans h₂)

theorem Z_inf_X_inf_Y : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G) ⊓
    Subgroup.centralizer (c.Y : Set G) = ⊥ := by
  by_contra hR
  set R := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G) ⊓
    Subgroup.centralizer (c.Y : Set G) with hRdef
  have hR2 : IsPGroup 2 R := H.hyp.sylow.1.to_le (inf_le_left.trans (inf_le_left.trans Z_le_T))
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := by
    intro u hu
    have hZ : u ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.centralizer_le_normalizer _ (le_centralizer_omegaOneCenter T hu)
    have hX := le_normalizer_centralizer c.le_normalizer_X hu
    have hY := le_normalizer_centralizer c.le_normalizer_Y hu
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hZ, hX⟩, hY⟩
  have hYR : c.Y ≤ Subgroup.normalizer (R : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_right
  have hXR : c.X ≤ Subgroup.normalizer (R : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_left.trans inf_le_right
  exact c.false_of_le_normalizer H hR hR2 (sup_le hYR hTR) (sup_le hXR hTR)

theorem EX_inf_E₁ : c.EX ⊓ c.E₁ = ⊥ := by
  by_contra hD
  have hDT : c.EX ⊓ c.E₁ ≤ T := inf_le_left.trans (inf_le_left.trans (eOf_le T))
  have hTD : T ≤ Subgroup.normalizer ((c.EX ⊓ c.E₁ : Subgroup G) : Set G) := by
    intro u hu
    have hE := le_normalizer_eOf T hu
    have hX := le_normalizer_centralizer c.le_normalizer_X hu
    have hY := le_normalizer_centralizer c.le_normalizer_Y hu
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hE, hX⟩,
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hE, hY⟩⟩
  obtain ⟨d, hdD, hd1, hdZ⟩ := exists_mem_omegaOneCenter_of_le H.hyp.sylow.1 hDT hTD
    (fun d hd => eOf_sq_eq_one hd.1.1) hD
  have hmem : d ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G) ⊓
      Subgroup.centralizer (c.Y : Set G) := ⟨⟨hdZ, hdD.1.2⟩, hdD.2.2⟩
  rw [c.Z_inf_X_inf_Y H, Subgroup.mem_bot] at hmem
  exact hd1 hmem

theorem EX_eq : c.EX = quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G) ∧
    Nat.card c.EX = 2 := by
  have hle : Nat.card c.EX ≤ 2 := by
    have h0 : c.EX ⊓ c.E₁ = ⊥ := c.EX_inf_E₁ H
    have hEX : c.EX ≤ eOf T := inf_le_left
    have h1 : c.E₁.relIndex c.EX ≤ c.E₁.relIndex (eOf T) :=
      Subgroup.relIndex_le_of_le_right hEX (by rw [c.relIndex_E₁ H]; norm_num)
    rw [← Subgroup.inf_relIndex_right, inf_comm, h0, Subgroup.relIndex_bot_left,
      c.relIndex_E₁ H] at h1
    exact h1
  have hZX : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X : Set G) ≤ c.EX :=
    inf_le_inf_right _ (omegaOneCenter_le_eOf' T)
  have h2 := card_Z_inf H c.famX
  have heq := Subgroup.eq_of_le_of_card_ge hZX (by rw [h2]; exact hle)
  exact ⟨heq.symm, heq ▸ h2⟩

include c in
theorem card_E : Nat.card (eOf T) = 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -, -⟩ := c.dataX
  have h := Subgroup.relIndex_mul_card c.EX (eOf T)
  have hidx' : c.EX.relIndex (eOf T) = 4 := hidx
  rw [hidx', inf_eq_left.mpr (show c.EX ≤ eOf T from inf_le_left), (c.EX_eq H).2] at h
  omega

theorem relIndex_E₂ : c.E₂.relIndex (eOf T) = 2 :=
  relIndex_eOf_inf_centralizer_eq_two_of_sixTwoData H.hyp.sylow.1 c.inM₂.2 c.le_X
    (c.isElemAbelian_V₂ H) (c.eX_decomp H).1 (c.eX_decomp H).2 c.dataX

theorem relIndex_E₃ : c.E₃.relIndex (eOf T) = 2 :=
  relIndex_eOf_inf_centralizer_eq_two_of_sixTwoData H.hyp.sylow.1 c.inM₂.2 c.le_X
    (c.isElemAbelian_V₂ H) (c.eX_decomp H).1 (c.eX_decomp H).2 c.dataX.symm

include c in
theorem card_of_relIndex_eq_two {A : Subgroup G} (hA : A ≤ eOf T) (h : A.relIndex (eOf T) = 2) :
    Nat.card A = 4 := by
  have h1 := Subgroup.relIndex_mul_card A (eOf T)
  rw [h, inf_eq_left.mpr hA, c.card_E H] at h1
  omega

omit [Finite G] H in
theorem E₂_inf_E₃ : c.E₂ ⊓ c.E₃ = c.EX := by
  unfold E₂ E₃ EX
  rw [c.dataX.1, centralizer_sup_eq]
  ext x
  simp only [Subgroup.mem_inf]
  tauto

omit [Finite G] H in
theorem EX_le_E₂ : c.EX ≤ c.E₂ := (c.E₂_inf_E₃).ge.trans inf_le_left

omit [Finite G] H in
theorem EX_le_E₃ : c.EX ≤ c.E₃ := (c.E₂_inf_E₃).ge.trans inf_le_right

omit [Finite G] H in
theorem Z_inf_X₁_le : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.X₁ : Set G) ≤
    Subgroup.centralizer (c.X : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨t, ht, ht₂⟩, -, -, -⟩ := c.dataX
  rintro z ⟨hzZ, hzC⟩
  have hzt : z * t = t * z :=
    Subgroup.mem_centralizer_iff.mp (le_centralizer_omegaOneCenter T ht) z hzZ
  have hzX₂ : z ∈ Subgroup.centralizer (c.X₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [ht₂] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxz := Subgroup.mem_centralizer_iff.mp hzC x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have c1 : Commute z t := hzt
    have c2 : Commute z x := (show Commute x z from hxz).symm
    exact (((c1.mul_right c2).mul_right c1.inv_right).symm : _)
  rw [c.dataX.1, centralizer_sup_eq]
  exact ⟨hzC, hzX₂⟩

theorem E₀_inf_Z : c.E₀ ⊓ quasithinOmegaOneCenter T = ⊥ := by
  rw [eq_bot_iff, ← c.Z_inf_X_inf_Y H]
  rintro w ⟨⟨hw₁, hw₂⟩, hwZ⟩
  exact ⟨⟨hwZ, c.Z_inf_X₁_le ⟨hwZ, hw₂.2⟩⟩, hw₁.2⟩

theorem card_E₀ : Nat.card c.E₀ = 2 := by
  have hE₁ : Nat.card c.E₁ = 4 :=
    c.card_of_relIndex_eq_two H (show c.E₁ ≤ eOf T from inf_le_left) (c.relIndex_E₁ H)
  have hE₂ : Nat.card c.E₂ = 4 :=
    c.card_of_relIndex_eq_two H (show c.E₂ ≤ eOf T from inf_le_left) (c.relIndex_E₂ H)
  have hE₀E : c.E₀ ≤ eOf T := inf_le_left.trans inf_le_left
  have hidx : c.E₀.relIndex (eOf T) ≤ 4 := by
    have h := Subgroup.relIndex_inf_le (H := c.E₁) (K := c.E₂) (L := eOf T)
    rw [c.relIndex_E₁ H, c.relIndex_E₂ H] at h
    exact h
  have hmul := Subgroup.relIndex_mul_card c.E₀ (eOf T)
  rw [inf_eq_left.mpr hE₀E, c.card_E H] at hmul
  have hdvd : Nat.card c.E₀ ∣ 4 := hE₁ ▸ Subgroup.card_dvd_of_le inf_le_left
  have h4 : Nat.card c.E₀ ≠ 4 := by
    intro h
    have heq : c.E₀ = c.E₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hE₁])
    have hle : c.E₁ ≤ c.E₂ := heq ▸ inf_le_right
    have heq' : c.E₁ = c.E₂ := Subgroup.eq_of_le_of_card_ge hle (by rw [hE₁, hE₂])
    have hbot : c.EX = ⊥ := by
      rw [eq_bot_iff, ← c.EX_inf_E₁ H]
      exact le_inf le_rfl (heq' ▸ c.EX_le_E₂)
    have := (c.EX_eq H).2
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card c.E₀ := Nat.card_pos
  interval_cases hc : Nat.card c.E₀
  · omega
  · rfl
  · norm_num at hdvd
  · exact absurd rfl h4

theorem E₀_ne_bot : c.E₀ ≠ ⊥ := fun h => by
  have := c.card_E₀ H
  rw [h, Subgroup.card_bot] at this
  omega

theorem eOf_eq_sup : eOf T = quasithinOmegaOneCenter T ⊔ c.E₀ := by
  have hZE := omegaOneCenter_le_eOf' T
  have hE₀E : c.E₀ ≤ eOf T := inf_le_left.trans inf_le_left
  have hZidx : (quasithinOmegaOneCenter T).relIndex (eOf T) = 2 := by
    have h := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (eOf T)
    rw [inf_eq_left.mpr hZE, card_Z H, c.card_E H] at h
    omega
  have h1 : (quasithinOmegaOneCenter T).relIndex (quasithinOmegaOneCenter T ⊔ c.E₀) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact c.E₀_ne_bot H (le_bot_iff.mp (c.E₀_inf_Z H ▸ le_inf le_rfl (le_sup_right.trans hle)))
  have htower := Subgroup.relIndex_mul_relIndex (quasithinOmegaOneCenter T)
    (quasithinOmegaOneCenter T ⊔ c.E₀) (eOf T) le_sup_left (sup_le hZE hE₀E)
  rw [hZidx] at htower
  have h0 := relIndex_ne_zero' (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T ⊔ c.E₀)
  have h2 : (quasithinOmegaOneCenter T ⊔ c.E₀).relIndex (eOf T) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨_, htower.symm⟩ with h | h
    · exact absurd h h1
    · rw [h] at htower
      omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) (sup_le hZE hE₀E)

theorem T_inf_centralizer_E₀ : T ⊓ Subgroup.centralizer (c.E₀ : Set G) = baum T := by
  apply le_antisymm
  · rintro u ⟨huT, huC⟩
    refine ⟨huT, ?_⟩
    have : eOf T = quasithinOmegaOneCenter T ⊔ c.E₀ := c.eOf_eq_sup H
    change u ∈ Subgroup.centralizer (eOf T : Set G)
    rw [this, centralizer_sup_eq]
    exact ⟨le_centralizer_omegaOneCenter T huT, huC⟩
  · exact le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (inf_le_left.trans inf_le_left))))

theorem baum_eq : baum T = T ⊓ Subgroup.normalizer (c.X₁ : Set G) := by
  apply le_antisymm
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hS₁, -⟩ := c.dataX
    exact le_inf inf_le_left hS₁
  · rw [← c.T_inf_centralizer_E₀ H]
    rintro u ⟨huT, huN⟩
    refine ⟨huT, mem_centralizer_of_card_eq_two (c.card_E₀ H) ?_⟩
    have hE := le_normalizer_eOf T huT
    have hY := le_normalizer_centralizer c.le_normalizer_Y huT
    have hX : u ∈ Subgroup.normalizer (Subgroup.centralizer (c.X₁ : Set G) : Set G) :=
      B2F.normalizer_le_normalizer_centralizer c.X₁ huN
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hE, hY⟩,
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hE, hX⟩⟩

theorem mem_E₁_not_mem_Z {e₀ z₁ w : G} (he₀ : ∀ y ∈ c.E₀, y = 1 ∨ y = e₀)
    (hz₁ : ∀ y ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.Y : Set G), y = 1 ∨ y = z₁)
    (hw : w ∈ c.E₁) (hwZ : w ∉ quasithinOmegaOneCenter T) : w = e₀ ∨ w = e₀ * z₁ := by
  set Zy := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.Y : Set G)
  have hZyE₁ : Zy ≤ c.E₁ := inf_le_inf_right _ (omegaOneCenter_le_eOf' T)
  have hE₀E₁ : c.E₀ ≤ c.E₁ := inf_le_left
  have hcard : Nat.card ↥(Zy ⊔ c.E₀) = 4 := by
    have hN : Zy ≤ Subgroup.normalizer (c.E₀ : Set G) := by
      intro a ha
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
      exact eOf_mul_comm (hE₀E₁ hb).1 (hZyE₁ ha).1
    have h := card_sup_mul_card_inf hN
    have hinf : Zy ⊓ c.E₀ = ⊥ := by
      rw [eq_bot_iff, ← c.E₀_inf_Z H]
      exact le_inf inf_le_right (inf_le_left.trans inf_le_left)
    rw [hinf, Subgroup.card_bot, mul_one, card_Z_inf H c.famY, c.card_E₀ H] at h
    exact h
  have hE₁4 : Nat.card c.E₁ = 4 :=
    c.card_of_relIndex_eq_two H (show c.E₁ ≤ eOf T from inf_le_left) (c.relIndex_E₁ H)
  have heq : Zy ⊔ c.E₀ = c.E₁ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZyE₁ hE₀E₁) (by rw [hcard, hE₁4])
  have hw' : w ∈ ((Zy ⊔ c.E₀ : Subgroup G) : Set G) := heq ▸ hw
  have hN' : c.E₀ ≤ Subgroup.normalizer (Zy : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
    exact eOf_mul_comm (hZyE₁ ha).1 (hE₀E₁ hb).1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Zy c.E₀ hN'] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
  rcases he₀ b hb with rfl | rfl
  · exact absurd (by rw [mul_one]; exact ha.1) hwZ
  · rcases hz₁ a ha with rfl | rfl
    · left; rw [one_mul]
    · right; exact eOf_mul_comm (hZyE₁ ha).1 (hE₀E₁ hb).1

include c in
theorem relIndex_baum : (baum T).relIndex T = 2 := by
  obtain ⟨⟨e₀, he₀E⟩, he₀1, he₀u⟩ := (Nat.card_eq_two_iff' (1 : c.E₀)).mp (c.card_E₀ H)
  have he₀ : ∀ y ∈ c.E₀, y = 1 ∨ y = e₀ := by
    intro y hy
    by_cases h : (⟨y, hy⟩ : c.E₀) = 1
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val (he₀u _ h))
  have he₀1' : e₀ ≠ 1 := fun h => he₀1 (Subtype.ext h)
  obtain ⟨⟨z₁, hz₁Z⟩, hz₁1, hz₁u⟩ := (Nat.card_eq_two_iff'
    (1 : ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.Y : Set G)))).mp
    (card_Z_inf H c.famY)
  have hz₁ : ∀ y ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.Y : Set G),
      y = 1 ∨ y = z₁ := by
    intro y hy
    by_cases h : (⟨y, hy⟩ : ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (c.Y : Set G))) = 1
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val (hz₁u _ h))
  have hz₁1' : z₁ ≠ 1 := fun h => hz₁1 (Subtype.ext h)
  have hz₁T : ∀ u ∈ T, u * z₁ * u⁻¹ = z₁ := fun u hu => by
    rw [(Subgroup.mem_centralizer_iff.mp (le_centralizer_omegaOneCenter T hu) z₁ hz₁Z.1).symm,
      mul_inv_cancel_right]
  have he₀Z : e₀ ∉ quasithinOmegaOneCenter T := fun h => he₀1' (by
    have hmem : e₀ ∈ c.E₀ ⊓ quasithinOmegaOneCenter T := ⟨he₀E, h⟩
    rwa [c.E₀_inf_Z H, Subgroup.mem_bot] at hmem)
  have hS : ∀ u ∈ T, u ∈ baum T ↔ u * e₀ * u⁻¹ = e₀ := by
    intro u hu
    rw [← c.T_inf_centralizer_E₀ H]
    constructor
    · rintro ⟨-, huC⟩
      rw [← Subgroup.mem_centralizer_iff.mp huC e₀ he₀E, mul_inv_cancel_right]
    · intro h
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rcases he₀ y hy with rfl | rfl
      · simp
      · calc y * u = u * y * u⁻¹ * u := by rw [h]
          _ = u * y := by group
  have hconj : ∀ u ∈ T, u * e₀ * u⁻¹ = e₀ ∨ u * e₀ * u⁻¹ = e₀ * z₁ := by
    intro u hu
    refine c.mem_E₁_not_mem_Z H he₀ hz₁ ?_ ?_
    · have huE := le_normalizer_eOf T hu
      have huY := le_normalizer_centralizer c.le_normalizer_Y hu
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨huE, huY⟩) e₀).mp he₀E.1
    · intro h
      apply he₀Z
      have := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.centralizer_le_normalizer _ (le_centralizer_omegaOneCenter T (T.inv_mem hu)))
        _).mp h
      simpa [mul_assoc] using this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨t, ht, ht₂⟩, -, -, -⟩ := c.dataX
  have htS : t ∉ baum T := by
    intro htS
    have htN : t ∈ Subgroup.normalizer (c.X₁ : Set G) := ((c.baum_eq H).le htS).2
    apply c.X₁_ne_X₂
    rw [ht₂]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp htN).symm
  have hte : t * e₀ * t⁻¹ = e₀ * z₁ := by
    rcases hconj t ht with h | h
    · exact absurd ((hS t ht).mpr h) htS
    · exact h
  have hz₁sq : z₁ * z₁ = 1 := by
    rw [← sq]
    exact (mem_quasithinOmegaOneCenter_iff.mp hz₁Z.1).2.2
  have hne : e₀ * z₁ ≠ e₀ := fun h => hz₁1' (by simpa using h)
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, ht, fun b hb => ?_⟩
  have hbt : b * t * e₀ * (b * t)⁻¹ = b * e₀ * b⁻¹ * z₁ := by
    calc b * t * e₀ * (b * t)⁻¹ = b * (t * e₀ * t⁻¹) * b⁻¹ := by group
      _ = b * e₀ * b⁻¹ * (b * z₁ * b⁻¹) := by rw [hte]; group
      _ = b * e₀ * b⁻¹ * z₁ := by rw [hz₁T b hb]
  rw [hS (b * t) (T.mul_mem hb ht), hS b hb, hbt]
  rcases hconj b hb with h | h
  · rw [h]
    exact Or.inr ⟨rfl, hne⟩
  · rw [h, mul_assoc, hz₁sq, mul_one]
    exact Or.inl ⟨rfl, h ▸ hne⟩

end Hyp

end Config15418

end CFSG.Quasithin.EmptyFaithfulMultiple
