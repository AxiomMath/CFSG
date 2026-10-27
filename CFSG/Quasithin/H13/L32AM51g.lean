module

public import CFSG.Quasithin.H13.L32AM51b
public import CFSG.Quasithin.H13.L32AM51c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm
open scoped IsMulCommutative

namespace Split

variable {M : Type} [CommGroup M] [Finite M]

omit [Finite M] in
theorem card_sup {A B : Subgroup M} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm, h, Subgroup.card_bot, mul_one] at h2
  rw [← h1, h2]

omit [Finite M] in
theorem eq_of_mul_eq {J J' : Subgroup M} (h : J ⊓ J' = ⊥) {a a' b b' : M} (ha : a ∈ J)
    (hb : b ∈ J) (ha' : a' ∈ J') (hb' : b' ∈ J') (he : a * a' = b * b') : a = b ∧ a' = b' := by
  have h1 : a * b⁻¹ = b' * a'⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, mul_comm b' b]
    exact he
  have hm : a * b⁻¹ ∈ J ⊓ J' :=
    ⟨J.mul_mem ha (J.inv_mem hb), h1 ▸ J'.mul_mem hb' (J'.inv_mem ha')⟩
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hm
  subst hm
  exact ⟨rfl, mul_left_cancel he⟩

theorem card_mul_relIndex_le {J J' : Subgroup M} (hinf : J ⊓ J' = ⊥) (hsup : J ⊔ J' = ⊤)
    {E E₀ : Subgroup (MulAut M)} (hE₀E : E₀ ≤ E) (hE₀J : ∀ e ∈ E₀, ∀ v ∈ J, e v ∈ J)
    (hE₀J' : ∀ e ∈ E₀, ∀ v ∈ J', e v ∈ J') {b : MulAut M} (hb : b ∈ E)
    (hbJ : ∀ v ∈ J, b v ∈ J') (hbJ' : ∀ v ∈ J', b v ∈ J) :
    Nat.card J * (J ⊓ fixV E₀).relIndex J ≤ (fixV E).index := by
  set F := fixV E₀ with hF
  set C₀ := fixV E with hC₀
  set FJ := J ⊓ F with hFJ
  set FJ' := J' ⊓ F with hFJ'
  have hcomp : ∀ c ∈ F, ∀ j ∈ J, ∀ j' ∈ J', c = j * j' → j ∈ FJ ∧ j' ∈ FJ' := by
    intro c hc j hj j' hj' hcj
    have key : ∀ e ∈ E₀, e j = j ∧ e j' = j' := by
      intro e he
      have h1 : e j * e j' = j * j' := by
        rw [← map_mul, ← hcj]
        exact hc e he
      exact eq_of_mul_eq hinf (hE₀J e he j hj) hj (hE₀J' e he j' hj') hj' h1
    exact ⟨⟨hj, fun e he => (key e he).1⟩, ⟨hj', fun e he => (key e he).2⟩⟩
  have hC₀F : C₀ ≤ F := fun c hc e he => hc e (hE₀E he)
  have hC₀le : C₀ ⊔ FJ' ≤ FJ ⊔ FJ' := by
    refine sup_le (fun c hc => ?_) le_sup_right
    have hcM : c ∈ J ⊔ J' := by
      rw [hsup]
      exact Subgroup.mem_top c
    obtain ⟨j, hj, j', hj', rfl⟩ := Subgroup.mem_sup.mp hcM
    obtain ⟨h1, h2⟩ := hcomp _ (hC₀F hc) j hj j' hj' rfl
    exact Subgroup.mul_mem_sup h1 h2
  have hC₀J' : C₀ ⊓ FJ' = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hc, hcJ', -⟩
    have h1 : c ∈ J ⊓ J' := ⟨(hc b hb) ▸ hbJ' c hcJ', hcJ'⟩
    rwa [hinf] at h1
  have hFF : FJ ⊓ FJ' = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨⟨hcJ, -⟩, hcJ', -⟩
    have h1 : c ∈ J ⊓ J' := ⟨hcJ, hcJ'⟩
    rwa [hinf] at h1
  have hcard1 : Nat.card C₀ * Nat.card FJ' ≤ Nat.card FJ * Nat.card FJ' := by
    rw [← card_sup hC₀J', ← card_sup hFF]
    exact Subgroup.card_le_of_le hC₀le
  have hC₀le' : Nat.card C₀ ≤ Nat.card FJ := Nat.le_of_mul_le_mul_right hcard1 Nat.card_pos
  have hJJ' : Nat.card J' = Nat.card J := by
    apply le_antisymm
    · refine Nat.card_le_card_of_injective (fun v : J' => (⟨b v, hbJ' v v.2⟩ : J)) ?_
      intro x y hxy
      exact Subtype.ext (b.injective (congrArg Subtype.val hxy))
    · refine Nat.card_le_card_of_injective (fun v : J => (⟨b v, hbJ v v.2⟩ : J')) ?_
      intro x y hxy
      exact Subtype.ext (b.injective (congrArg Subtype.val hxy))
  have hM : Nat.card M = Nat.card J * Nat.card J := by
    rw [← Subgroup.card_top, ← hsup, card_sup hinf, hJJ']
  have hidx := Subgroup.card_mul_index C₀
  have hrel := Subgroup.relIndex_mul_card (H := FJ) (K := J)
  rw [inf_eq_left.mpr inf_le_left] at hrel
  have h3 : Nat.card J * FJ.relIndex J * Nat.card FJ ≤ C₀.index * Nat.card FJ := by
    calc Nat.card J * FJ.relIndex J * Nat.card FJ = Nat.card J * Nat.card J := by
          rw [mul_assoc, hrel]
      _ = Nat.card C₀ * C₀.index := by rw [hidx, hM]
      _ ≤ Nat.card FJ * C₀.index := Nat.mul_le_mul_right _ hC₀le'
      _ = C₀.index * Nat.card FJ := mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos

omit [Finite M] in
theorem mem_sup_of_maps {A B : Subgroup M} {f : MulAut M} (hA : ∀ v ∈ A, f v ∈ A ⊔ B)
    (hB : ∀ v ∈ B, f v ∈ A ⊔ B) {v : M} (hv : v ∈ A ⊔ B) : f v ∈ A ⊔ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul]
  exact mul_mem (hA a ha) (hB b hb)

end Split

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top51

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 8)} (C : Top51 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]

structure SplitData (J J' : Subgroup (Hat V H W)) : Prop where
  inv : ∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J
  inv' : ∀ l ∈ C.autK, ∀ v ∈ J', l v ∈ J'
  inf : J ⊓ J' = ⊥
  sup : J ⊔ J' = ⊤
  min : ∀ J₂ : Subgroup (Hat V H W), J₂ ≤ J → (∀ l ∈ C.autK, ∀ v ∈ J₂, l v ∈ J₂) →
    J₂ = ⊥ ∨ J₂ = J
  min' : ∀ J₂ : Subgroup (Hat V H W), J₂ ≤ J' → (∀ l ∈ C.autK, ∀ v ∈ J₂, l v ∈ J₂) →
    J₂ = ⊥ ∨ J₂ = J'
  swap : ∀ y ∈ C.act.range, y ∉ C.autK → (∀ v ∈ J, y v ∈ J') ∧ (∀ v ∈ J', y v ∈ J)

include C

theorem card_range : Nat.card C.act.range = 40320 := by
  rw [Nat.card_congr C.embEquiv.toEquiv, Alt8.card_perm8]

theorem card_autK : Nat.card C.autK = 20160 := by
  rw [Nat.card_congr C.iota.toEquiv, Alt8.card_alt8]

theorem relIndex_autK : C.autK.relIndex C.act.range = 2 := by
  have h := Subgroup.relIndex_mul_card (H := C.autK) (K := C.act.range)
  rw [inf_eq_left.mpr C.autK_le, C.card_range, C.card_autK] at h
  omega

theorem odd_cases {y₀ y : MulAut (Hat V H W)} (hy₀ : y₀ ∈ C.act.range) (hy₀K : y₀ ∉ C.autK)
    (hy : y ∈ C.act.range) : y ∈ C.autK ∨ y₀⁻¹ * y ∈ C.autK := by
  obtain ⟨h₀, rfl⟩ := hy₀
  obtain ⟨h, rfl⟩ := hy
  by_cases hh : C.act h ∈ C.autK
  · exact Or.inl hh
  · right
    rw [← map_inv, ← map_mul, C.act_mem_autK_iff]
    rw [C.act_mem_autK_iff, mem_alternatingGroup] at hy₀K hh
    rw [mem_alternatingGroup, map_mul, map_inv, map_mul, map_inv]
    rcases Int.units_eq_one_or (sign (π h₀)) with h1 | h1
    · exact absurd h1 hy₀K
    rcases Int.units_eq_one_or (sign (π h)) with h2 | h2
    · exact absurd h2 hh
    rw [h1, h2]
    decide

theorem isSimpleGroup_autK : IsSimpleGroup ↥C.autK := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := Alt8.isSimpleGroup
  exact C.iota.isSimpleGroup

theorem exists_split (hnirr : ¬ C.IrrK) : ∃ J J' : Subgroup (Hat V H W), C.SplitData J J' := by
  classical
  set 𝒮 : Set (Subgroup (Hat V H W)) := {J | J ≠ ⊥ ∧ ∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J} with h𝒮
  have htop : (⊤ : Subgroup (Hat V H W)) ∈ 𝒮 :=
    ⟨C.top_ne_bot, fun _ _ _ _ => Subgroup.mem_top _⟩
  obtain ⟨J, ⟨hJ0, hJinv⟩, hJmin⟩ := 𝒮.toFinite.exists_minimal ⟨_, htop⟩
  have hmin : ∀ J₂ : Subgroup (Hat V H W), J₂ ≤ J →
      (∀ l ∈ C.autK, ∀ v ∈ J₂, l v ∈ J₂) → J₂ = ⊥ ∨ J₂ = J := by
    intro J₂ hJ₂ hinv
    by_cases h0 : J₂ = ⊥
    · exact Or.inl h0
    · exact Or.inr (le_antisymm hJ₂ (hJmin ⟨h0, hinv⟩ hJ₂))
  have hJtop : J ≠ ⊤ := by
    rintro rfl
    exact hnirr fun J₂ hinv => hmin J₂ le_top hinv
  obtain ⟨h₀, hh₀⟩ := C.exists_act_not_mem
  set b := C.act h₀ with hb
  have hbR : b ∈ C.act.range := ⟨h₀, rfl⟩
  have hbiR : b⁻¹ ∈ C.act.range := inv_mem hbR
  have hconj : ∀ l ∈ C.autK, b⁻¹ * l * b ∈ C.autK := fun l hl => by
    have := C.autK_normal b⁻¹ hbiR l hl
    rwa [inv_inv] at this
  have hconj' : ∀ l ∈ C.autK, b * l * b⁻¹ ∈ C.autK := fun l hl => C.autK_normal b hbR l hl
  have hb2 : b * b ∈ C.autK := by
    have := C.sq_mem b hbR
    rwa [pow_two] at this
  set J' : Subgroup (Hat V H W) := J.map (b : MulAut (Hat V H W)).toMonoidHom with hJ'
  have hmemJ' : ∀ {x : Hat V H W}, x ∈ J' ↔ ∃ y ∈ J, b y = x := fun {x} => Subgroup.mem_map
  have hbJ : ∀ v ∈ J, b v ∈ J' := fun v hv => hmemJ'.mpr ⟨v, hv, rfl⟩
  have hbJ' : ∀ v ∈ J', b v ∈ J := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hmemJ'.mp hv
    have := hJinv _ hb2 y hy
    rwa [MulAut.mul_apply] at this
  have hJ'inv : ∀ l ∈ C.autK, ∀ v ∈ J', l v ∈ J' := by
    intro l hl v hv
    obtain ⟨y, hy, rfl⟩ := hmemJ'.mp hv
    refine hmemJ'.mpr ⟨(b⁻¹ * l * b) y, hJinv _ (hconj l hl) y hy, ?_⟩
    simp only [MulAut.mul_apply, MulAut.apply_inv_self]
  have hswap : ∀ y ∈ C.act.range, y ∉ C.autK → (∀ v ∈ J, y v ∈ J') ∧ (∀ v ∈ J', y v ∈ J) := by
    intro y hy hyK
    rcases C.odd_cases hbR hh₀ hy with h | h
    · exact absurd h hyK
    have e : ∀ v, y v = b ((b⁻¹ * y) v) := fun v => by
      simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    exact ⟨fun v hv => (e v) ▸ hbJ _ (hJinv _ h v hv),
      fun v hv => (e v) ▸ hbJ' _ (hJ'inv _ h v hv)⟩
  have hHinv : ∀ X : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ X, l v ∈ X) →
      (∀ v ∈ X, b v ∈ X) → ∀ h : ↥H, ∀ v ∈ X, C.act h v ∈ X := by
    intro X hXa hXb h v hv
    rcases C.odd_cases hbR hh₀ ⟨h, rfl⟩ with h1 | h1
    · exact hXa _ h1 v hv
    · have e : C.act h v = b ((b⁻¹ * C.act h) v) := by
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      rw [e]
      exact hXb _ (hXa _ h1 v hv)
  have hcardJ' : Nat.card J' = Nat.card J :=
    Subgroup.card_map_of_injective (b : MulAut (Hat V H W)).injective
  have hinf : J ⊓ J' = ⊥ := by
    rcases hmin (J ⊓ J') inf_le_left (fun l hl v hv => ⟨hJinv l hl v hv.1, hJ'inv l hl v hv.2⟩)
      with h | h
    · exact h
    · exfalso
      have hJJ : J ≤ J' := h ▸ inf_le_right
      have hJeq : J = J' := Subgroup.eq_of_le_of_card_ge hJJ hcardJ'.le
      rcases C.irr J (hHinv J hJinv fun v hv => hJeq ▸ hbJ v hv) with h1 | h1
      · exact hJ0 h1
      · exact hJtop h1
  have hsup : J ⊔ J' = ⊤ := by
    have hYa : ∀ l ∈ C.autK, ∀ v ∈ J ⊔ J', l v ∈ J ⊔ J' := fun l hl v hv =>
      Split.mem_sup_of_maps (fun x hx => Subgroup.mem_sup_left (hJinv l hl x hx))
        (fun x hx => Subgroup.mem_sup_right (hJ'inv l hl x hx)) hv
    have hYb : ∀ v ∈ J ⊔ J', b v ∈ J ⊔ J' := fun v hv =>
      Split.mem_sup_of_maps (fun x hx => Subgroup.mem_sup_right (hbJ x hx))
        (fun x hx => Subgroup.mem_sup_left (hbJ' x hx)) hv
    rcases C.irr (J ⊔ J') (hHinv _ hYa hYb) with h | h
    · exact absurd (eq_bot_iff.mpr (h ▸ le_sup_left)) hJ0
    · exact h
  have hmin' : ∀ J₂ : Subgroup (Hat V H W), J₂ ≤ J' →
      (∀ l ∈ C.autK, ∀ v ∈ J₂, l v ∈ J₂) → J₂ = ⊥ ∨ J₂ = J' := by
    intro J₂ hJ₂ hinv
    set J₃ := J₂.map (b⁻¹ : MulAut (Hat V H W)).toMonoidHom with hJ₃
    have hJ₃J : J₃ ≤ J := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hmemJ'.mp (hJ₂ hx)
      show b⁻¹ (b y) ∈ J
      rwa [MulAut.inv_apply_self]
    have hJ₃inv : ∀ l ∈ C.autK, ∀ v ∈ J₃, l v ∈ J₃ := by
      rintro l hl _ ⟨x, hx, rfl⟩
      refine ⟨(b * l * b⁻¹) x, hinv _ (hconj' l hl) x hx, ?_⟩
      show b⁻¹ ((b * l * b⁻¹) x) = l (b⁻¹ x)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rcases hmin J₃ hJ₃J hJ₃inv with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _
        (b⁻¹ : MulAut (Hat V H W)).injective).mp h
    · right
      refine le_antisymm hJ₂ fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hmemJ'.mp hx
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hzy' : b⁻¹ z = y := hzy
      rw [← hzy', MulAut.apply_inv_self]
      exact hz
  exact ⟨J, J', hJinv, hJ'inv, hinf, hsup, hmin, hmin', hswap⟩

namespace SplitData

variable {C} {J J' : Subgroup (Hat V H W)} (S : C.SplitData J J')
include S

theorem symm : C.SplitData J' J :=
  ⟨S.inv', S.inv, by rw [inf_comm, S.inf], by rw [sup_comm, S.sup], S.min', S.min,
    fun y hy hyK => ⟨(S.swap y hy hyK).2, (S.swap y hy hyK).1⟩⟩

theorem card_eq : Nat.card J' = Nat.card J := by
  obtain ⟨h₀, hh₀⟩ := C.exists_act_not_mem
  obtain ⟨h1, h2⟩ := S.swap _ ⟨h₀, rfl⟩ hh₀
  apply le_antisymm
  · refine Nat.card_le_card_of_injective (fun v : J' => (⟨C.act h₀ v, h2 v v.2⟩ : J)) ?_
    intro x y hxy
    exact Subtype.ext ((C.act h₀).injective (congrArg Subtype.val hxy))
  · refine Nat.card_le_card_of_injective (fun v : J => (⟨C.act h₀ v, h1 v v.2⟩ : J')) ?_
    intro x y hxy
    exact Subtype.ext ((C.act h₀).injective (congrArg Subtype.val hxy))

theorem nt : ∃ l ∈ C.autK, ∃ v ∈ J, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₀, hh₀⟩ := C.exists_act_not_mem
  set b := C.act h₀ with hb
  have hbR : b ∈ C.act.range := ⟨h₀, rfl⟩
  have hbiK : b⁻¹ ∉ C.autK := fun h => hh₀ (by simpa using inv_mem h)
  have hall : ∀ l ∈ C.autK, l = 1 := by
    intro l hl
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ J ⊔ J' := by
      rw [S.sup]
      exact Subgroup.mem_top v
    obtain ⟨j, hj, j', hj', rfl⟩ := Subgroup.mem_sup.mp hv
    have hj'b : b j' ∈ J := (S.swap b hbR hh₀).2 j' hj'
    have h1 : l j' = j' := by
      have := hcon _ (C.autK_normal b hbR l hl) _ hj'b
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
      exact b.injective this
    rw [map_mul, hcon l hl j hj, h1, MulAut.one_apply]
  have h1 : Nat.card C.autK = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ((hall x x.2).trans (hall y y.2).symm)⟩, ⟨1⟩⟩
  rw [C.card_autK] at h1
  omega

theorem eight_le : 8 ≤ Nat.card J := by
  have hinj := resAut_injective C.autK J S.inv C.isSimpleGroup_autK S.nt
  have h1 : Nat.card C.autK ≤ Nat.card (MulAut ↥J) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (MulAut ↥J) ≤ Nat.card (Equiv.Perm ↥J) :=
    Nat.card_le_card_of_injective (fun f : MulAut ↥J => f.toEquiv) fun f g h =>
      MulEquiv.ext fun x => congrFun (congrArg DFunLike.coe h) x
  rw [Nat.card_perm, C.card_autK] at *
  by_contra hlt
  push Not at hlt
  have h3 : (Nat.card ↥J).factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
  have h4 : (7 : ℕ).factorial = 5040 := by decide
  omega

theorem offender {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    ∃ E₁ : Subgroup (MulAut (Hat V H W)), E₁ ≤ C.autK ∧ E₁ ≠ ⊥ ∧ IsElemAbelian2 E₁ ∧
      (J ⊓ fixV E₁).relIndex J ≤ Nat.card E₁ ^ 2 := by
  set E := C.autE B with hE
  obtain ⟨hER, hE1, hEab⟩ := C.isA2_autE hB
  have hidx := C.index_fixV_autE_le hB
  rw [← hE] at hidx
  by_cases hEK : E ≤ C.autK
  · refine ⟨E, hEK, hE1, hEab, ?_⟩
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal _ _)).trans hidx
  · obtain ⟨b, hbE, hbK⟩ := Set.not_subset.mp hEK
    set E₁ := E ⊓ C.autK with hE₁
    have hE₁ab : IsElemAbelian2 E₁ :=
      ⟨fun x hx y hy => hEab.1 x hx.1 y hy.1, fun x hx => hEab.2 x hx.1⟩
    have hsw := S.swap b (hER hbE) hbK
    have key := Split.card_mul_relIndex_le S.inf S.sup (E := E) (E₀ := E₁) inf_le_left
      (fun e he v hv => S.inv e he.2 v hv) (fun e he v hv => S.inv' e he.2 v hv) hbE hsw.1 hsw.2
    have hEE : Nat.card E ≤ 2 * Nat.card E₁ := by
      have h1 := Subgroup.relIndex_mul_card (H := E₁) (K := E)
      rw [inf_eq_left.mpr inf_le_left] at h1
      have h2 : E₁.relIndex E = C.autK.relIndex E := by
        rw [hE₁, inf_comm, Subgroup.inf_relIndex_right]
      have h3 : C.autK.relIndex E ≤ 2 := by
        rw [← C.relIndex_autK]
        exact Subgroup.relIndex_le_of_le_right hER (by rw [C.relIndex_autK]; norm_num)
      rw [← h1, h2]
      exact Nat.mul_le_mul_right _ h3
    have h8 := S.eight_le
    have hr : 0 < (J ⊓ fixV E₁).relIndex J := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hsq : Nat.card E ^ 2 ≤ 4 * Nat.card E₁ ^ 2 := by
      have := Nat.pow_le_pow_left hEE 2
      rw [mul_pow] at this
      simpa using this
    have h8r : 8 * (J ⊓ fixV E₁).relIndex J ≤ Nat.card J * (J ⊓ fixV E₁).relIndex J :=
      Nat.mul_le_mul_right _ h8
    refine ⟨E₁, inf_le_right, fun h => ?_, hE₁ab, by omega⟩
    rw [h, Subgroup.card_bot] at hsq
    omega

end SplitData

end Top51

end CFSG.Quasithin.H13.L32A.C
