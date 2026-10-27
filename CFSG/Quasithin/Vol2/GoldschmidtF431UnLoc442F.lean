module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442E
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Quasithin

section Gen

variable {G H : Type*} [Group G] [Group H] {N : Subgroup G} {b : ↥N →* H} {A : Subgroup G}

theorem subImg_comm (h : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a) :
    ∀ x ∈ subImg b A, ∀ y ∈ subImg b A, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, haN, haA, rfl⟩ := mem_subImg.mp hx
  obtain ⟨c, hcN, hcA, rfl⟩ := mem_subImg.mp hy
  rw [← map_mul, ← map_mul]
  exact congrArg b (Subtype.ext (h a haA c hcA))

theorem subImg_sq (h : ∀ a ∈ A, a ^ 2 = 1) : ∀ x ∈ subImg b A, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨a, haN, haA, rfl⟩ := mem_subImg.mp hx
  rw [← map_pow, ← map_one b]
  exact congrArg b (Subtype.ext (h a haA))

end Gen

section Normalizer

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem {W : Subgroup G} {g : G} (h1 : ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (h2 : ∀ w ∈ W, g⁻¹ * w * g ∈ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h1 w, fun hw => ?_⟩
  have := h2 _ hw
  rwa [show g⁻¹ * (g * w * g⁻¹) * g = w by group] at this

theorem le_normalizer_of_comm {S W : Subgroup G} (h : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s) :
    S ≤ Subgroup.normalizer (W : Set G) :=
  le_normalizer_of_conj fun s hs w hw => by
    rw [h s hs w hw]
    simpa using hw

theorem le_nS_of_comm {S W A : Subgroup G} (hAS : A ≤ S)
    (h : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) : A ≤ nS S W :=
  fun _ ha => ⟨le_normalizer_of_comm h ha, hAS ha⟩

theorem le_nS {S W : Subgroup G} (hWS : W ≤ S) : W ≤ nS S W :=
  fun _ hw => ⟨Subgroup.le_normalizer hw, hWS hw⟩

theorem normal_subgroupOf_nS {S W : Subgroup G} (hWS : W ≤ S) :
    (W.subgroupOf (nS S W)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_nS hWS)).2 inf_le_left

end Normalizer

section Quot

variable {G : Type} [Group G] {N W : Subgroup G} [(W.subgroupOf N).Normal]

@[expose] def qmk (N W : Subgroup G) [(W.subgroupOf N).Normal] :
    ↥N →* ↥N ⧸ W.subgroupOf N :=
  QuotientGroup.mk' (W.subgroupOf N)

@[expose] def qimg (N W : Subgroup G) [(W.subgroupOf N).Normal] (A : Subgroup G) :
    Subgroup (↥N ⧸ W.subgroupOf N) :=
  subImg (qmk N W) A

theorem qmk_eq_iff {a b : G} (ha : a ∈ N) (hb : b ∈ N) :
    qmk N W ⟨a, ha⟩ = qmk N W ⟨b, hb⟩ ↔ a⁻¹ * b ∈ W := by
  unfold qmk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf

theorem qmk_eq_one_iff {a : G} (ha : a ∈ N) : qmk N W ⟨a, ha⟩ = 1 ↔ a ∈ W := by
  unfold qmk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

theorem qmk_surj (q : ↥N ⧸ W.subgroupOf N) : ∃ (a : G) (ha : a ∈ N), qmk N W ⟨a, ha⟩ = q := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨a, ha, rfl⟩

theorem qmk_mem_qimg_iff {A : Subgroup G} (hWA : W ≤ A) {a : G} (ha : a ∈ N) :
    qmk N W ⟨a, ha⟩ ∈ qimg N W A ↔ a ∈ A := by
  constructor
  · intro h
    obtain ⟨x, hxN, hxA, hx⟩ := mem_subImg.mp h
    have h2 : x⁻¹ * a ∈ A := hWA ((qmk_eq_iff hxN ha).mp hx)
    simpa using A.mul_mem hxA h2
  · exact fun h => mem_subImg_of_mem _ ha h

theorem qmk_mul (a b : G) (ha : a ∈ N) (hb : b ∈ N) (hab : a * b ∈ N) :
    qmk N W ⟨a * b, hab⟩ = qmk N W ⟨a, ha⟩ * qmk N W ⟨b, hb⟩ :=
  map_mul (qmk N W) ⟨a, ha⟩ ⟨b, hb⟩

theorem qmk_inv (a : G) (ha : a ∈ N) (hai : a⁻¹ ∈ N) :
    qmk N W ⟨a⁻¹, hai⟩ = (qmk N W ⟨a, ha⟩)⁻¹ :=
  map_inv (qmk N W) ⟨a, ha⟩

theorem qmk_one (h : (1 : G) ∈ N) : qmk N W ⟨1, h⟩ = 1 := map_one (qmk N W)

theorem qmk_conj (a b : G) (ha : a ∈ N) (hb : b ∈ N) (h : a * b * a⁻¹ ∈ N) :
    qmk N W ⟨a * b * a⁻¹, h⟩ = qmk N W ⟨a, ha⟩ * qmk N W ⟨b, hb⟩ * (qmk N W ⟨a, ha⟩)⁻¹ := by
  rw [qmk_mul _ _ (N.mul_mem ha hb) (N.inv_mem ha) h, qmk_mul _ _ ha hb (N.mul_mem ha hb),
    qmk_inv _ ha (N.inv_mem ha)]

theorem qmk_conj_inv (g v : G) (hg : g ∈ N) (hv : v ∈ N) (h : g⁻¹ * v * g ∈ N) :
    qmk N W ⟨g⁻¹ * v * g, h⟩ = (qmk N W ⟨g, hg⟩)⁻¹ * qmk N W ⟨v, hv⟩ * qmk N W ⟨g, hg⟩ := by
  rw [qmk_mul _ _ (N.mul_mem (N.inv_mem hg) hv) hg h,
    qmk_mul _ _ (N.inv_mem hg) hv (N.mul_mem (N.inv_mem hg) hv), qmk_inv _ hg (N.inv_mem hg)]

end Quot

end CFSG.Quasithin.H13.F431.Un
