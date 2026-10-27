module

public import CFSG.Quasithin.EmptyFaithful.E22QWr
public import CFSG.Quasithin.EmptyFaithful.E22QLift
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

section Aux

variable {G : Type} [Group G]

theorem typeIII_exists_mul_of_mem_sup {P Q : Subgroup G}
    (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G} (hx : x ∈ P ⊔ Q) :
    ∃ a ∈ P, ∃ b ∈ Q, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, Q.one_mem, by simp⟩
    · exact ⟨1, P.one_mem, x, hx, by simp⟩
  · exact ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, P.mul_mem ha₁ ha₂, b₁ * b₂, Q.mul_mem hb₁ hb₂, ?_⟩
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hc a₂ ha₂ b₁ hb₁]
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact hc _ (P.inv_mem ha) _ (Q.inv_mem hb)

theorem typeIII_exists_mul_of_le_normalizer {D R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (D : Set G)) {x : G} (hx : x ∈ D ⊔ R) :
    ∃ d ∈ D, ∃ r ∈ R, d * r = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, R.one_mem, by simp⟩
    · exact ⟨1, D.one_mem, x, hx, by simp⟩
  · exact ⟨1, D.one_mem, 1, R.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨d₁, hd₁, r₁, hr₁, rfl⟩ ⟨d₂, hd₂, r₂, hr₂, rfl⟩
    refine ⟨d₁ * (r₁ * d₂ * r₁⁻¹),
      D.mul_mem hd₁ ((Subgroup.mem_normalizer_iff.mp (hR hr₁) d₂).mp hd₂), r₁ * r₂,
      R.mul_mem hr₁ hr₂, ?_⟩
    group
  · rintro _ _ ⟨d, hd, r, hr, rfl⟩
    refine ⟨r⁻¹ * d⁻¹ * r, ?_, r⁻¹, R.inv_mem hr, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (hR (R.inv_mem hr)) d⁻¹).mp (D.inv_mem hd)
    simpa using this

theorem typeIII_comm_of_mem {A : Subgroup G} {q : ℕ} (hA : IsElemAbelian q A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hA ha hb

end Aux

section Twist

variable {G : Type} [Group G]

structure TypeIIITwist (J₁ J₂ : Subgroup G) (z : G) : Prop where
  comm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a
  disj : J₁ ⊓ J₂ = ⊥
  sq : z * z = 1
  swap : conjSub z J₁ = J₂

@[expose] def typeIII_diag (J₁ J₂ : Subgroup G) (z : G) : Subgroup G :=
  (J₁ ⊔ J₂) ⊓ Subgroup.centralizer ({z} : Set G)

@[expose] def typeIII_tw (z x : G) : G := x * (z * x * z⁻¹)

namespace TypeIIITwist

variable {J₁ J₂ : Subgroup G} {z : G}

theorem inv_eq (d : TypeIIITwist J₁ J₂ z) : z⁻¹ = z := inv_eq_of_mul_eq_one_right d.sq

theorem swap' (d : TypeIIITwist J₁ J₂ z) : conjSub z J₂ = J₁ := by
  rw [← d.swap, ← conjSub_mul, d.sq, conjSub_one]

theorem conj_mem₁ (d : TypeIIITwist J₁ J₂ z) {x : G} (hx : x ∈ J₁) : z * x * z⁻¹ ∈ J₂ := by
  rw [← d.swap]
  exact mem_conjSub_of_mem hx

theorem conj_mem₂ (d : TypeIIITwist J₁ J₂ z) {x : G} (hx : x ∈ J₂) : z * x * z⁻¹ ∈ J₁ := by
  rw [← d.swap']
  exact mem_conjSub_of_mem hx

theorem eq_of_mul_eq (d : TypeIIITwist J₁ J₂ z) {a a' b b' : G} (ha : a ∈ J₁) (ha' : a' ∈ J₁)
    (hb : b ∈ J₂) (hb' : b' ∈ J₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ J₁ ⊓ J₂ := by
    refine ⟨J₁.mul_mem (J₁.inv_mem ha') ha, ?_⟩
    rw [h1]
    exact J₂.mul_mem hb' (J₂.inv_mem hb)
  rw [d.disj, Subgroup.mem_bot] at h2
  have h3 : a = a' := (inv_mul_eq_one.mp h2).symm
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel h

theorem tw_one (z : G) : typeIII_tw z 1 = 1 := by simp [typeIII_tw]

theorem tw_mul (d : TypeIIITwist J₁ J₂ z) {x y : G} (hx : x ∈ J₁) (hy : y ∈ J₁) :
    typeIII_tw z (x * y) = typeIII_tw z x * typeIII_tw z y := by
  have hc := d.comm y hy _ (d.conj_mem₁ hx)
  unfold typeIII_tw
  calc x * y * (z * (x * y) * z⁻¹) = x * (y * (z * x * z⁻¹)) * (z * y * z⁻¹) := by group
    _ = x * ((z * x * z⁻¹) * y) * (z * y * z⁻¹) := by rw [hc]
    _ = x * (z * x * z⁻¹) * (y * (z * y * z⁻¹)) := by group

theorem tw_inj (d : TypeIIITwist J₁ J₂ z) {x y : G} (hx : x ∈ J₁) (hy : y ∈ J₁)
    (h : typeIII_tw z x = typeIII_tw z y) : x = y := by
  have h1 : y⁻¹ * x = (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ := by
    unfold typeIII_tw at h
    calc y⁻¹ * x = y⁻¹ * (x * (z * x * z⁻¹)) * (z * x * z⁻¹)⁻¹ := by group
      _ = y⁻¹ * (y * (z * y * z⁻¹)) * (z * x * z⁻¹)⁻¹ := by rw [h]
      _ = (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ := by group
  have h2 : y⁻¹ * x ∈ J₁ ⊓ J₂ := by
    refine ⟨J₁.mul_mem (J₁.inv_mem hy) hx, ?_⟩
    rw [h1]
    exact J₂.mul_mem (d.conj_mem₁ hy) (J₂.inv_mem (d.conj_mem₁ hx))
  rw [d.disj, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.mp h2).symm

theorem tw_mem_diag (d : TypeIIITwist J₁ J₂ z) {x : G} (hx : x ∈ J₁) :
    typeIII_tw z x ∈ typeIII_diag J₁ J₂ z := by
  rw [typeIII_diag, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨Subgroup.mul_mem_sup hx (d.conj_mem₁ hx), ?_⟩
  have hc := d.comm x hx _ (d.conj_mem₁ hx)
  unfold typeIII_tw
  calc x * (z * x * z⁻¹) * z = x * z * x := by group
    _ = x * z⁻¹ * x := by rw [d.inv_eq]
    _ = (z * z) * x * z⁻¹ * x := by rw [d.sq, one_mul]
    _ = z * ((z * x * z⁻¹) * x) := by group
    _ = z * (x * (z * x * z⁻¹)) := by rw [← hc]

theorem exists_tw (d : TypeIIITwist J₁ J₂ z) {δ : G} (hδ : δ ∈ typeIII_diag J₁ J₂ z) :
    ∃ x ∈ J₁, typeIII_tw z x = δ := by
  rw [typeIII_diag, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hδ
  obtain ⟨hX, hδz⟩ := hδ
  obtain ⟨a, ha, b, hb, rfl⟩ := typeIII_exists_mul_of_mem_sup d.comm hX
  have h1 : z * b * z⁻¹ ∈ J₁ := d.conj_mem₂ hb
  have h2 : z * a * z⁻¹ ∈ J₂ := d.conj_mem₁ ha
  have h3 : (z * b * z⁻¹) * (z * a * z⁻¹) = a * b := by
    calc (z * b * z⁻¹) * (z * a * z⁻¹) = (z * a * z⁻¹) * (z * b * z⁻¹) := d.comm _ h1 _ h2
      _ = z * (a * b) * z⁻¹ := by group
      _ = a * b := by rw [← hδz]; group
  have h4 := (d.eq_of_mul_eq h1 ha h2 hb h3).2
  exact ⟨a, ha, by unfold typeIII_tw; rw [h4]⟩

theorem tw_comm (d : TypeIIITwist J₁ J₂ z) {x y : G} (hx : x ∈ J₁) (hy : y ∈ J₁)
    (h : x * y = y * x) :
    typeIII_tw z x * typeIII_tw z y = typeIII_tw z y * typeIII_tw z x := by
  rw [← d.tw_mul hx hy, ← d.tw_mul hy hx, h]

theorem tw_conj {a : G} (haz : a * z = z * a) (x : G) :
    a * typeIII_tw z x * a⁻¹ = typeIII_tw z (a * x * a⁻¹) := by
  unfold typeIII_tw
  calc a * (x * (z * x * z⁻¹)) * a⁻¹ = (a * x * a⁻¹) * ((a * z) * x * (a * z)⁻¹) := by group
    _ = (a * x * a⁻¹) * ((z * a) * x * (z * a)⁻¹) := by rw [haz]
    _ = (a * x * a⁻¹) * (z * (a * x * a⁻¹) * z⁻¹) := by group

theorem mem_of_tw_mem (d : TypeIIITwist J₁ J₂ z) {S : Subgroup G}
    (hS : S ⊓ (J₁ ⊔ J₂) ≤ (S ⊓ J₁) ⊔ (S ⊓ J₂)) {x : G} (hx : x ∈ J₁)
    (hxS : typeIII_tw z x ∈ S) : x ∈ S := by
  have h1 : typeIII_tw z x ∈ S ⊓ (J₁ ⊔ J₂) := ⟨hxS, (d.tw_mem_diag hx).1⟩
  obtain ⟨a, ha, b, hb, hab⟩ := typeIII_exists_mul_of_mem_sup (P := S ⊓ J₁) (Q := S ⊓ J₂)
    (fun a ha b hb => d.comm a ha.2 b hb.2) (hS h1)
  have h2 := (d.eq_of_mul_eq ha.2 hx hb.2 (d.conj_mem₁ hx) hab).1
  rw [← h2]
  exact ha.1

theorem conj_mem_diag (hX : (J₁ ⊔ J₂).Normal) {g δ : G} (hg : g * z = z * g)
    (hδ : δ ∈ typeIII_diag J₁ J₂ z) : g * δ * g⁻¹ ∈ typeIII_diag J₁ J₂ z := by
  rw [typeIII_diag, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hδ ⊢
  refine ⟨hX.conj_mem δ hδ.1 g, ?_⟩
  have hg' : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hg)).eq
  calc g * δ * g⁻¹ * z = g * δ * (g⁻¹ * z) := by group
    _ = g * δ * (z * g⁻¹) := by rw [hg']
    _ = g * (δ * z) * g⁻¹ := by group
    _ = g * (z * δ) * g⁻¹ := by rw [hδ.2]
    _ = (g * z) * δ * g⁻¹ := by group
    _ = z * g * δ * g⁻¹ := by rw [hg]
    _ = z * (g * δ * g⁻¹) := by group

theorem mem_normalizer_diag (hX : (J₁ ⊔ J₂).Normal) {g : G} (hg : g * z = z * g) :
    g ∈ Subgroup.normalizer (typeIII_diag J₁ J₂ z : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro δ
  refine ⟨fun hδ => conj_mem_diag hX hg hδ, fun hδ => ?_⟩
  have hg' : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hg)).eq
  have e : g⁻¹ * (g * δ * g⁻¹) * g⁻¹⁻¹ = δ := by group
  have := conj_mem_diag hX hg' hδ
  rwa [e] at this

@[expose] def hom (d : TypeIIITwist J₁ J₂ z) : ↥J₁ →* G where
  toFun x := typeIII_tw z (x : G)
  map_one' := tw_one z
  map_mul' x y := d.tw_mul x.2 y.2

theorem hom_apply (d : TypeIIITwist J₁ J₂ z) (x : ↥J₁) : d.hom x = typeIII_tw z (x : G) :=
  rfl

theorem hom_injective (d : TypeIIITwist J₁ J₂ z) : Function.Injective d.hom :=
  fun x y h => Subtype.ext (d.tw_inj x.2 y.2 h)

noncomputable def equiv (d : TypeIIITwist J₁ J₂ z) : ↥J₁ ≃* ↥(typeIII_diag J₁ J₂ z) :=
  MulEquiv.ofBijective (d.hom.codRestrict _ fun x => d.tw_mem_diag x.2)
    ⟨fun x y h => d.hom_injective (congrArg Subtype.val h), fun δ => by
      obtain ⟨x, hx, hxδ⟩ := d.exists_tw δ.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxδ⟩⟩

theorem map_top (d : TypeIIITwist J₁ J₂ z) :
    (⊤ : Subgroup ↥J₁).map d.hom = typeIII_diag J₁ J₂ z := by
  ext δ
  constructor
  · rintro ⟨x, -, rfl⟩
    exact d.tw_mem_diag x.2
  · intro hδ
    obtain ⟨x, hx, rfl⟩ := d.exists_tw hδ
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

theorem map_inf_subgroupOf (d : TypeIIITwist J₁ J₂ z) {T : Subgroup G} (hzT : z ∈ T)
    (hS : T ⊓ (J₁ ⊔ J₂) ≤ (T ⊓ J₁) ⊔ (T ⊓ J₂)) :
    ((T ⊓ J₁).subgroupOf J₁).map d.hom = T ⊓ typeIII_diag J₁ J₂ z := by
  ext δ
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxT : (x : G) ∈ T := (Subgroup.mem_subgroupOf.mp hx).1
    exact ⟨T.mul_mem hxT (T.mul_mem (T.mul_mem hzT hxT) (T.inv_mem hzT)), d.tw_mem_diag x.2⟩
  · rintro ⟨hδT, hδ⟩
    obtain ⟨x, hx, rfl⟩ := d.exists_tw hδ
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr ⟨d.mem_of_tw_mem hS hx hδT, hx⟩, rfl⟩

theorem eq_one_of_centralizes_diag (d : TypeIIITwist J₁ J₂ z)
    (hcent : Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) = ⊥) {a : G}
    (haN : a ∈ Subgroup.normalizer (J₁ : Set G)) (haz : a * z = z * a)
    (hc : ∀ δ ∈ typeIII_diag J₁ J₂ z, δ * a = a * δ) : a = 1 := by
  have h1 : ∀ x ∈ J₁, x * a = a * x := by
    intro x hx
    have hax : a * x * a⁻¹ ∈ J₁ := (Subgroup.mem_normalizer_iff.mp haN x).mp hx
    have hconj := tw_conj haz x
    have hcomm := hc _ (d.tw_mem_diag hx)
    have h2 : typeIII_tw z (a * x * a⁻¹) = typeIII_tw z x := by
      rw [← hconj]
      calc a * typeIII_tw z x * a⁻¹ = (a * typeIII_tw z x) * a⁻¹ := rfl
        _ = (typeIII_tw z x * a) * a⁻¹ := by rw [hcomm]
        _ = typeIII_tw z x := by group
    have h3 := d.tw_inj hax hx h2
    calc x * a = (a * x * a⁻¹) * a := by rw [h3]
      _ = a * x := by group
  have h2 : ∀ y ∈ J₂, y * a = a * y := by
    intro y hy
    obtain ⟨x, hxdef⟩ : ∃ x, x = z * y * z⁻¹ := ⟨_, rfl⟩
    have hxJ : x ∈ J₁ := by rw [hxdef]; exact d.conj_mem₂ hy
    have hx : x * a = a * x := h1 x hxJ
    have haz' : a * z⁻¹ = z⁻¹ * a := (Commute.inv_right (show Commute a z from haz)).eq
    have hy' : y = z⁻¹ * x * z := by rw [hxdef]; group
    rw [hy']
    calc z⁻¹ * x * z * a = z⁻¹ * x * (z * a) := by group
      _ = z⁻¹ * x * (a * z) := by rw [haz]
      _ = z⁻¹ * (x * a) * z := by group
      _ = z⁻¹ * (a * x) * z := by rw [hx]
      _ = (z⁻¹ * a) * x * z := by group
      _ = (a * z⁻¹) * x * z := by rw [haz']
      _ = a * (z⁻¹ * x * z) := by group
  have h3 : a ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := typeIII_exists_mul_of_mem_sup d.comm hg
    calc x * y * a = x * (y * a) := by group
      _ = x * (a * y) := by rw [h2 y hy]
      _ = (x * a) * y := by group
      _ = (a * x) * y := by rw [h1 x hx]
      _ = a * (x * y) := by group
  rw [hcent, Subgroup.mem_bot] at h3
  exact h3

end TypeIIITwist

end Twist

section Config

variable {G : Type} [Group G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ z : G}

theorem typeIII_zD_comm_of_mem (h : Wr p T M J₁ J₂ z₁) (d : TypeIIITwist J₁ J₂ z)
    (hzT : z ∈ T) {r : G} (hrT : r ∈ T) (hrz : r * z = z * r) :
    typeIII_tw z z₁ * r = r * typeIII_tw z z₁ := by
  have hrc : Commute r z := hrz
  by_cases hrN : r ∈ Subgroup.normalizer (J₁ : Set G)
  · have c1 : Commute r z₁ := (h.z₁_central r ⟨hrT, hrN⟩).symm
    have c3 : Commute r (z * z₁ * z⁻¹) := (hrc.mul_right c1).mul_right hrc.inv_right
    exact (c1.mul_right c3).eq.symm
  · have hrz' : r * z⁻¹ = z⁻¹ * r := hrc.inv_right.eq
    have hrJ : conjSub r J₁ = J₂ :=
      (h.perm r hrT).resolve_left fun h' => hrN (conjSub_eq_iff_mem_normalizer.mp h')
    have hzrN : z⁻¹ * r ∈ Subgroup.normalizer (J₁ : Set G) := by
      rw [← conjSub_eq_iff_mem_normalizer, conjSub_mul, hrJ, d.inv_eq, d.swap']
    have hzrT : z⁻¹ * r ∈ T := T.mul_mem (T.inv_mem hzT) hrT
    have h1 : z₁ * (z⁻¹ * r) = (z⁻¹ * r) * z₁ := h.z₁_central _ ⟨hzrT, hzrN⟩
    have E1 : r * z₁ = (z * z₁ * z⁻¹) * r := by
      calc r * z₁ = z * ((z⁻¹ * r) * z₁) := by group
        _ = z * (z₁ * (z⁻¹ * r)) := by rw [h1]
        _ = (z * z₁ * z⁻¹) * r := by group
    have E2 : r * (z * z₁ * z⁻¹) = z₁ * r := by
      calc r * (z * z₁ * z⁻¹) = (r * z) * z₁ * z⁻¹ := by group
        _ = (z * r) * z₁ * z⁻¹ := by rw [hrz]
        _ = z * (r * z₁) * z⁻¹ := by group
        _ = z * ((z * z₁ * z⁻¹) * r) * z⁻¹ := by rw [E1]
        _ = z * (z * z₁ * z⁻¹) * (r * z⁻¹) := by group
        _ = z * (z * z₁ * z⁻¹) * (z⁻¹ * r) := by rw [hrz']
        _ = (z * z) * z₁ * (z * z)⁻¹ * r := by group
        _ = z₁ * r := by rw [d.sq]; group
    have hc : (z * z₁ * z⁻¹) ∈ J₂ := d.conj_mem₁ h.z₁_mem
    have hcomm : z₁ * (z * z₁ * z⁻¹) = (z * z₁ * z⁻¹) * z₁ := d.comm _ h.z₁_mem _ hc
    unfold typeIII_tw
    calc z₁ * (z * z₁ * z⁻¹) * r = (z * z₁ * z⁻¹) * z₁ * r := by rw [hcomm]
      _ = (z * z₁ * z⁻¹) * (z₁ * r) := by group
      _ = (z * z₁ * z⁻¹) * (r * (z * z₁ * z⁻¹)) := by rw [E2]
      _ = ((z * z₁ * z⁻¹) * r) * (z * z₁ * z⁻¹) := by group
      _ = (r * z₁) * (z * z₁ * z⁻¹) := by rw [← E1]
      _ = r * (z₁ * (z * z₁ * z⁻¹)) := by group

theorem typeIII_comm_of_mem_M (h : Wr p T M J₁ J₂ z₁) (d : TypeIIITwist J₁ J₂ z)
    (hzT : z ∈ T) {g : G} (hgM : g ∈ M)
    (hgN : g ∈ Subgroup.normalizer (typeIII_diag J₁ J₂ z : Set G)) :
    g * typeIII_tw z z₁ = typeIII_tw z z₁ * g := by
  have hzM : z ∈ M := h.T_le hzT
  have hzD : typeIII_tw z z₁ ∈ typeIII_diag J₁ J₂ z := d.tw_mem_diag h.z₁_mem
  have hy' : g * typeIII_tw z z₁ * g⁻¹ ∈ typeIII_diag J₁ J₂ z :=
    (Subgroup.mem_normalizer_iff.mp hgN _).mp hzD
  obtain ⟨x', hx'J, hx'⟩ := d.exists_tw hy'
  have key : ∀ x ∈ J₁, x * z₁ = z₁ * x → x * x' = x' * x := by
    intro x hxJ hxz
    have hxM : x ∈ M := by
      have : x ∈ M ⊓ J₁ := by
        rw [h.M_J₁]
        exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxz, hxJ⟩
      exact this.1
    have hπM : typeIII_tw z x ∈ M :=
      M.mul_mem hxM (M.mul_mem (M.mul_mem hzM hxM) (M.inv_mem hzM))
    have hgi : g⁻¹ ∈ Subgroup.normalizer (typeIII_diag J₁ J₂ z : Set G) :=
      (Subgroup.normalizer _).inv_mem hgN
    have hcD : g⁻¹ * typeIII_tw z x * g⁻¹⁻¹ ∈ typeIII_diag J₁ J₂ z :=
      (Subgroup.mem_normalizer_iff.mp hgi _).mp (d.tw_mem_diag hxJ)
    have hcM : g⁻¹ * typeIII_tw z x * g⁻¹⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.inv_mem hgM) hπM) (by simpa using hgM)
    obtain ⟨x'', hx''J, hx''⟩ := d.exists_tw hcD
    have hx''M : x'' ∈ M := d.mem_of_tw_mem h.M_X hx''J (by rw [hx'']; exact hcM)
    have hx''z : x'' * z₁ = z₁ * x'' := by
      have : x'' ∈ M ⊓ J₁ := ⟨hx''M, hx''J⟩
      rw [h.M_J₁] at this
      exact Subgroup.mem_centralizer_singleton_iff.mp this.1
    have hc1 := d.tw_comm hx''J h.z₁_mem hx''z
    rw [hx''] at hc1
    have h5 : typeIII_tw z x * typeIII_tw z x' = typeIII_tw z x' * typeIII_tw z x := by
      rw [hx']
      calc typeIII_tw z x * (g * typeIII_tw z z₁ * g⁻¹)
          = g * (g⁻¹ * typeIII_tw z x * g⁻¹⁻¹ * typeIII_tw z z₁) * g⁻¹ := by group
        _ = g * (typeIII_tw z z₁ * (g⁻¹ * typeIII_tw z x * g⁻¹⁻¹)) * g⁻¹ := by rw [hc1]
        _ = (g * typeIII_tw z z₁ * g⁻¹) * typeIII_tw z x := by group
    have h6 : typeIII_tw z (x * x') = typeIII_tw z (x' * x) := by
      rw [d.tw_mul hxJ hx'J, d.tw_mul hx'J hxJ]
      exact h5
    exact d.tw_inj (J₁.mul_mem hxJ hx'J) (J₁.mul_mem hx'J hxJ) h6
  rcases h.cen_fact x' hx'J key with hx1 | hx1
  · exfalso
    rw [hx1, TypeIIITwist.tw_one] at hx'
    have h1 : typeIII_tw z z₁ = 1 := by
      calc typeIII_tw z z₁ = g⁻¹ * (g * typeIII_tw z z₁ * g⁻¹) * g := by group
        _ = 1 := by rw [← hx']; group
    have h2 := d.tw_inj h.z₁_mem J₁.one_mem (h1.trans (TypeIIITwist.tw_one z).symm)
    have h3 := h.z₁_ord
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  · rw [hx1] at hx'
    calc g * typeIII_tw z z₁ = (g * typeIII_tw z z₁ * g⁻¹) * g := by group
      _ = typeIII_tw z z₁ * g := by rw [← hx']

theorem typeIII_sylow_diag [Finite G] (h : Wr p T M J₁ J₂ z₁) (d : TypeIIITwist J₁ J₂ z)
    (hzT : z ∈ T) : IsSylowIn 2 (T ⊓ typeIII_diag J₁ J₂ z) (typeIII_diag J₁ J₂ z) := by
  have hP : IsSylowIn 2 ((T ⊓ J₁).subgroupOf J₁) (⊤ : Subgroup ↥J₁) := by
    have := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ J₁) (K := J₁) (H := J₁)
      inf_le_right le_rfl).mpr h.sylow_J₁
    rwa [Subgroup.subgroupOf_self] at this
  have := (E1.isSylowIn_map_of_injective (p := 2) d.hom_injective).mpr hP
  rwa [d.map_inf_subgroupOf hzT h.TX_eq.le, d.map_top] at this

end Config


theorem typeIII {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (WL : WitnessL2 p) (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} {z : G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hzA : z ∈ A) (hzS : z ∉ Subgroup.normalizer (J₁ : Set G))
    (hV : A ⊓ Subgroup.normalizer (J₁ : Set G) ≠ ⊥) :
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧ ¬ K ≤ M := by
  have hzT : z ∈ T := hAT hzA
  have hz2 : z * z = 1 := by
    have := hAab.2 z hzA
    rwa [pow_two] at this
  have hswap : conjSub z J₁ = J₂ :=
    (h.perm z hzT).resolve_left fun h' => hzS (conjSub_eq_iff_mem_normalizer.mp h')
  have d : TypeIIITwist J₁ J₂ z := ⟨h.comm, h.disj, hz2, hswap⟩
  set D : Subgroup G := typeIII_diag J₁ J₂ z with hDdef
  set R : Subgroup G := T ⊓ Subgroup.centralizer (A : Set G) with hRdef
  set Q : Subgroup G := D ⊔ R with hQdef
  have hRT : R ≤ T := inf_le_left
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    (Subgroup.mem_centralizer_iff.mp hr.2 z hzA).symm
  have hRN : R ≤ Subgroup.normalizer (D : Set G) := fun r hr =>
    TypeIIITwist.mem_normalizer_diag h.normal_X (hRz r hr)
  have hDQ : D ≤ Q := le_sup_left
  have hRQ : R ≤ Q := le_sup_right
  have hQN : Q ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hRN
  have hDn : (D.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr hQN
  have hDp : IsPSL 2 p 1 ↥D := CFSG.SectionRank.statedClassicalModel_of_mulEquiv d.equiv.symm h.psl₁
  have hDs : IsSimpleGroup ↥D := by
    have := h.simple₁
    exact d.equiv.symm.isSimpleGroup
  have hDnc : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.nonab₁
    refine ⟨d.equiv a, d.equiv b, fun hc => hab (d.equiv.injective ?_)⟩
    rw [map_mul, map_mul]
    exact hc
  have hDTQ : D ⊔ (T ⊓ Q) = Q :=
    le_antisymm (sup_le hDQ inf_le_right) (sup_le le_sup_left (le_sup_of_le_right (le_inf hRT hRQ)))
  have hTQ : IsSylowIn 2 (T ⊓ Q) Q := by
    have h1 : IsSylowIn 2 ((T ⊓ Q) ⊓ D) D := by
      have e : (T ⊓ Q) ⊓ D = T ⊓ D := by rw [inf_assoc, inf_eq_right.mpr hDQ]
      rw [e]
      exact typeIII_sylow_diag h d hzT
    have h2 := E1.isSylowIn_two_of_sup_inf (inf_le_right.trans hQN)
      (h.sylow.isPGroup.to_le inf_le_left) h1
    rwa [hDTQ] at h2
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ Q := by
    rw [h.tau_eq A]
    exact le_inf hRT hRQ
  have hAQ : A ≤ Q := fun a ha =>
    hRQ ⟨hAT ha, Subgroup.mem_centralizer_iff.mpr fun b hb => typeIII_comm_of_mem hAab hb ha⟩
  have hAD : ¬ A ≤ Subgroup.centralizer (D : Set G) := by
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A ⊓ Subgroup.normalizer (J₁ : Set G), a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hV (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hcon a ha))
    intro hAc
    refine ha1 (d.eq_one_of_centralizes_diag h.cent ha.2 (typeIII_comm_of_mem hAab ha.1 hzA) ?_)
    intro δ hδ
    exact Subgroup.mem_centralizer_iff.mp (hAc ha.1) δ hδ
  have hzD : typeIII_tw z z₁ ∈ D := d.tw_mem_diag h.z₁_mem
  have hzD2 : orderOf (typeIII_tw z z₁) = 2 := by
    have h1 : orderOf (d.hom ⟨z₁, h.z₁_mem⟩) = orderOf (⟨z₁, h.z₁_mem⟩ : ↥J₁) :=
      orderOf_injective d.hom d.hom_injective _
    rw [Subgroup.orderOf_mk, h.z₁_ord] at h1
    exact h1
  have hzc : ∀ x ∈ T ⊓ Q, typeIII_tw z z₁ * x = x * typeIII_tw z z₁ := by
    intro x hx
    obtain ⟨δ, hδ, r, hr, rfl⟩ := typeIII_exists_mul_of_le_normalizer hRN hx.2
    have hδT : δ ∈ T := by
      have := T.mul_mem hx.1 (T.inv_mem hr.1)
      simpa using this
    obtain ⟨x₀, hx₀J, rfl⟩ := d.exists_tw hδ
    have hx₀T : x₀ ∈ T := d.mem_of_tw_mem h.TX_eq.le hx₀J hδT
    have h1 : z₁ * x₀ = x₀ * z₁ := h.z₁_central x₀ ⟨hx₀T, Subgroup.le_normalizer hx₀J⟩
    have hc1 : typeIII_tw z z₁ * typeIII_tw z x₀ = typeIII_tw z x₀ * typeIII_tw z z₁ :=
      d.tw_comm h.z₁_mem hx₀J h1
    have hc2 := typeIII_zD_comm_of_mem h d hzT hr.1 (hRz r hr)
    calc typeIII_tw z z₁ * (typeIII_tw z x₀ * r) = (typeIII_tw z z₁ * typeIII_tw z x₀) * r := by
          group
      _ = (typeIII_tw z x₀ * typeIII_tw z z₁) * r := by rw [hc1]
      _ = typeIII_tw z x₀ * (typeIII_tw z z₁ * r) := by group
      _ = typeIII_tw z x₀ * (r * typeIII_tw z z₁) := by rw [hc2]
      _ = typeIII_tw z x₀ * r * typeIII_tw z z₁ := by group
  obtain ⟨J, hJQ, hJE, hJz⟩ := local_witness WL h.sylow hAT hAab hDQ hDn hDp hDs hDnc hTQ hDTQ hτ
    hAQ hAD hzD hzD2 hzc
  refine ⟨J, hJE, fun hJM => hJz fun g hg => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact typeIII_comm_of_mem_M h d hzT (hJM hg) (hQN (hJQ hg))

end CFSG.Quasithin.E2.E22N
