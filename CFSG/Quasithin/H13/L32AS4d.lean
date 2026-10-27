module

public import CFSG.Quasithin.H13.L32ANotation
public import CFSG.Quasithin.EmptyFaithful.S153Q4Aa

public section

namespace CFSG.Quasithin.H13.L32A

variable {G : Type} [Group G]

namespace IsElemSection

variable {X Y : Subgroup G}

theorem le (h : IsElemSection X Y) : Y ≤ X := h.1

theorem comm (h : IsElemSection X Y) {a b : G} (ha : a ∈ X) (hb : b ∈ X) :
    a * b * a⁻¹ * b⁻¹ ∈ Y := (h.2 a ha b hb).1

theorem sq (h : IsElemSection X Y) {a : G} (ha : a ∈ X) : a ^ 2 ∈ Y := (h.2 a ha a ha).2

theorem conj_mem (h : IsElemSection X Y) {a y : G} (ha : a ∈ X) (hy : y ∈ Y) :
    a * y * a⁻¹ ∈ Y := by
  have e : a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
  rw [e]
  exact mul_mem (h.comm ha (h.le hy)) hy

theorem normal (h : IsElemSection X Y) : (Y.subgroupOf X).Normal :=
  ⟨fun n hn x => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.conj_mem x.2 hn⟩

end IsElemSection

@[expose] def SecW (X Y : Subgroup G) (_h : IsElemSection X Y) : Type := ↥X ⧸ Y.subgroupOf X

namespace SecW

variable {X Y : Subgroup G} (h : IsElemSection X Y)

@[reducible] noncomputable def instGroup : Group (SecW X Y h) :=
  haveI := h.normal
  inferInstanceAs (Group (↥X ⧸ Y.subgroupOf X))

noncomputable instance instCommGroup : CommGroup (SecW X Y h) :=
  { instGroup h with
    mul_comm := fun a b => by
      have := h.normal
      induction a using QuotientGroup.induction_on with
      | H x =>
      induction b using QuotientGroup.induction_on with
      | H x' =>
      show (QuotientGroup.mk (x * x') : ↥X ⧸ Y.subgroupOf X) = QuotientGroup.mk (x' * x)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := h.comm x'.2 x.2
      have e : ((x : G) * x')⁻¹ * ((x' : G) * x) =
          (x : G)⁻¹ * ((x' : G)⁻¹ * ((x' : G) * x * (x' : G)⁻¹ * (x : G)⁻¹) * x') * x := by
        group
      rw [e]
      have h1 := h.conj_mem (inv_mem x'.2) this
      rw [inv_inv] at h1
      have h2 := h.conj_mem (inv_mem x.2) h1
      rwa [inv_inv] at h2 }

instance instFinite [Finite G] : Finite (SecW X Y h) :=
  haveI := h.normal
  inferInstanceAs (Finite (↥X ⧸ Y.subgroupOf X))

noncomputable def mk : ↥X →* SecW X Y h :=
  haveI := h.normal
  QuotientGroup.mk' (Y.subgroupOf X)

theorem mk_surjective : Function.Surjective (mk h) := by
  have := h.normal
  exact QuotientGroup.mk'_surjective _

theorem mk_eq_mk_iff (x x' : ↥X) : mk h x = mk h x' ↔ (x : G)⁻¹ * x' ∈ Y := by
  have := h.normal
  show (QuotientGroup.mk x : ↥X ⧸ Y.subgroupOf X) = QuotientGroup.mk x' ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mk_eq_one_iff (x : ↥X) : mk h x = 1 ↔ (x : G) ∈ Y := by
  have := h.normal
  show (QuotientGroup.mk x : ↥X ⧸ Y.subgroupOf X) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mul_self (w : SecW X Y h) : w * w = 1 := by
  obtain ⟨x, rfl⟩ := mk_surjective h w
  rw [← map_mul, mk_eq_one_iff]
  simpa [sq] using h.sq x.2

theorem card [Finite G] : Nat.card (SecW X Y h) = Y.relIndex X := rfl

@[expose] def conjX {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G)) : ↥X ≃* ↥X where
  toFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha x).mp x.2⟩
  invFun x := ⟨a⁻¹ * x * a, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x x' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjX {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    ((conjX ha x : ↥X) : G) = a * x * a⁻¹ := rfl

theorem map_conjX {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G))
    (ha' : a ∈ Subgroup.normalizer (Y : Set G)) :
    (Y.subgroupOf X).map (conjX ha).toMonoidHom = Y.subgroupOf X := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ha' _).mp hx'
  · intro hx
    refine ⟨(conjX ha).symm x, ?_, (conjX ha).apply_symm_apply x⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha') _).mp hx
    rw [inv_inv] at this
    exact this

noncomputable def actAut {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G))
    (ha' : a ∈ Subgroup.normalizer (Y : Set G)) : MulAut (SecW X Y h) :=
  haveI := h.normal
  QuotientGroup.congr (Y.subgroupOf X) (Y.subgroupOf X) (conjX ha) (map_conjX ha ha')

theorem actAut_mk {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G))
    (ha' : a ∈ Subgroup.normalizer (Y : Set G)) (x : ↥X) :
    actAut h ha ha' (mk h x) = mk h (conjX ha x) := by
  have := h.normal
  rfl

noncomputable def act (A : Subgroup G) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) : ↥A →* MulAut (SecW X Y h) where
  toFun a := actAut h (hAX a.2) (hAY a.2)
  map_one' := by
    ext w
    obtain ⟨x, rfl⟩ := mk_surjective h w
    rw [actAut_mk, MulAut.one_apply]
    congr 1
    exact Subtype.ext (by simp [coe_conjX])
  map_mul' a b := by
    ext w
    obtain ⟨x, rfl⟩ := mk_surjective h w
    rw [MulAut.mul_apply, actAut_mk, actAut_mk, actAut_mk]
    congr 1
    exact Subtype.ext (by simp only [coe_conjX, Subgroup.coe_mul]; group)

variable {A : Subgroup G} {hAX : A ≤ Subgroup.normalizer (X : Set G)}
  {hAY : A ≤ Subgroup.normalizer (Y : Set G)}

theorem act_mk (a : ↥A) (x : ↥X) :
    act h A hAX hAY a (mk h x) = mk h ⟨a * x * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAX a.2) x).mp x.2⟩ :=
  actAut_mk h (hAX a.2) (hAY a.2) x

theorem act_mk_eq_mk_iff (a : ↥A) (x : ↥X) :
    act h A hAX hAY a (mk h x) = mk h x ↔ (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ ∈ Y := by
  rw [act_mk, mk_eq_mk_iff]
  show ((a : G) * x * (a : G)⁻¹)⁻¹ * x ∈ Y ↔ _
  constructor
  · intro h1
    have h2 := h.conj_mem x.2 (Y.inv_mem h1)
    have e : (x : G) * (((a : G) * x * (a : G)⁻¹)⁻¹ * x)⁻¹ * (x : G)⁻¹ =
        (a : G) * x * (a : G)⁻¹ * (x : G)⁻¹ := by group
    rwa [e] at h2
  · intro h1
    have h2 := h.conj_mem (inv_mem x.2) h1
    have e : (x : G)⁻¹ * ((a : G) * x * (a : G)⁻¹ * (x : G)⁻¹) * (x : G)⁻¹⁻¹ =
        (((a : G) * x * (a : G)⁻¹)⁻¹ * x)⁻¹ := by group
    rw [e] at h2
    simpa using Y.inv_mem h2

theorem act_eq_one_iff (a : ↥A) :
    act h A hAX hAY a = 1 ↔ ∀ x ∈ X, (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ Y := by
  constructor
  · intro h1 x hx
    have := congrArg (fun φ : MulAut (SecW X Y h) => φ (mk h ⟨x, hx⟩)) h1
    simp only [MulAut.one_apply] at this
    exact (act_mk_eq_mk_iff h a ⟨x, hx⟩).mp this
  · intro h1
    ext w
    obtain ⟨x, rfl⟩ := mk_surjective h w
    rw [MulAut.one_apply]
    exact (act_mk_eq_mk_iff h a x).mpr (h1 x x.2)

noncomputable def img (F : Subgroup G) : Subgroup (SecW X Y h) := (F.subgroupOf X).map (mk h)

theorem mk_mem_img {F : Subgroup G} {x : ↥X} (hx : (x : G) ∈ F) : mk h x ∈ img h F :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)

theorem card_img [Finite G] {F : Subgroup G} (hFX : F ≤ X) : Nat.card (img h F) = Y.relIndex F := by
  set φ : ↥F →* SecW X Y h := (mk h).comp (Subgroup.inclusion hFX) with hφ
  have hr : φ.range = img h F := by
    rw [hφ, MonoidHom.range_comp, img]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨f, rfl⟩
      exact f.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hk : φ.ker = Y.subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, mk_eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  rw [← hr, ← Subgroup.index_ker, hk]
  rfl


theorem mem_img_iff {F : Subgroup G} (hYF : Y ≤ F) {x : ↥X} : mk h x ∈ img h F ↔ (x : G) ∈ F := by
  refine ⟨fun hx => ?_, mk_mem_img h⟩
  obtain ⟨x', hx', he⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_subgroupOf] at hx'
  have h1 := (mk_eq_mk_iff h x' x).mp he
  have e : (x : G) = x' * ((x' : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem hx' (hYF h1)

theorem img_eq_bot_iff {F : Subgroup G} (hFX : F ≤ X) : img h F = ⊥ ↔ F ≤ Y := by
  constructor
  · intro hb f hf
    have : mk h ⟨f, hFX hf⟩ ∈ img h F := mk_mem_img h hf
    rw [hb, Subgroup.mem_bot, mk_eq_one_iff] at this
    exact this
  · intro hFY
    refine eq_bot_iff.mpr fun w hw => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    exact (Subgroup.mem_bot).mpr ((mk_eq_one_iff h x).mpr (hFY (Subgroup.mem_subgroupOf.mp hx)))

theorem img_eq_top_iff {F : Subgroup G} (hYF : Y ≤ F) (hFX : F ≤ X) :
    img h F = ⊤ ↔ F = X := by
  constructor
  · intro ht
    refine le_antisymm hFX fun x hx => ?_
    have : mk h ⟨x, hx⟩ ∈ img h F := ht ▸ Subgroup.mem_top _
    exact (mem_img_iff h hYF).mp this
  · rintro rfl
    refine eq_top_iff.mpr fun w _ => ?_
    obtain ⟨x, rfl⟩ := mk_surjective h w
    exact mk_mem_img h x.2

theorem act_mem_img {F : Subgroup G} (a : ↥A) (ha : (a : G) ∈ Subgroup.normalizer (F : Set G))
    {w : SecW X Y h} (hw : w ∈ img h F) : act h A hAX hAY a w ∈ img h F := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
  rw [act_mk]
  exact mk_mem_img h ((Subgroup.mem_normalizer_iff.mp ha x).mp (Subgroup.mem_subgroupOf.mp hx))

noncomputable def pre (W : Subgroup (SecW X Y h)) : Subgroup G := (W.comap (mk h)).map X.subtype

theorem mem_pre {W : Subgroup (SecW X Y h)} {g : G} :
    g ∈ pre h W ↔ ∃ hg : g ∈ X, mk h ⟨g, hg⟩ ∈ W := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hgW⟩
    exact ⟨⟨g, hg⟩, hgW, rfl⟩

theorem pre_le (W : Subgroup (SecW X Y h)) : pre h W ≤ X := fun _ hg => ((mem_pre h).mp hg).1

theorem le_pre (W : Subgroup (SecW X Y h)) : Y ≤ pre h W := fun y hy =>
  (mem_pre h).mpr ⟨h.le hy, by rw [(mk_eq_one_iff h ⟨y, h.le hy⟩).mpr hy]; exact W.one_mem⟩

theorem img_pre (W : Subgroup (SecW X Y h)) : img h (pre h W) = W := by
  ext w
  obtain ⟨x, rfl⟩ := mk_surjective h w
  rw [mem_img_iff h (le_pre h W), mem_pre]
  exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨x.2, hx⟩⟩

theorem relIndex_pre [Finite G] (W : Subgroup (SecW X Y h)) :
    Y.relIndex (pre h W) = Nat.card W := by
  rw [← card_img h (pre_le h W), img_pre]

end SecW

section Fix

variable {W : Type} [CommGroup W]

@[expose] def fixSub (y : MulAut W) : Subgroup W where
  carrier := {w | y w = w}
  one_mem' := map_one y
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {y : MulAut W} {w : W} : w ∈ fixSub y ↔ y w = w := Iff.rfl

theorem card_fixSub_le_four [Finite W] (hW2 : ∀ w : W, w * w = 1) {c y : MulAut W}
    (hc3 : c ^ 3 = 1) (hfpf : ∀ w : W, c w = w → w = 1) (hyc : y * c = c * y) (hy4 : y ^ 4 = 1)
    (hy2 : y ^ 2 ≠ 1) (hcard : Nat.card W = 64) : Nat.card (fixSub y) ≤ 4 := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
  have hcomm : ∀ w : W, y (c w) = c (y w) := fun w => by
    rw [← MulAut.mul_apply, hyc, MulAut.mul_apply]
  have hcF : ∀ x ∈ fixSub y, c x ∈ fixSub y := fun x hx => by
    rw [mem_fixSub] at hx ⊢
    rw [hcomm, hx]
  have hmod := S153Q.Q4A.card_mod_three hc3 hfpf hcF
  have hdvd : Nat.card (fixSub y) ∣ 64 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hcases : Nat.card (fixSub y) ∈ ({1, 2, 4, 8, 16, 32, 64} : Finset ℕ) := by
    have : Nat.card (fixSub y) ∈ Nat.divisors 64 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    exact this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  rcases hcases with h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  ·
    exfalso
    let δ : W →* W :=
      { toFun := fun w => w * (y w)⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [map_mul, mul_inv_rev]
          rw [mul_comm (y b)⁻¹ (y a)⁻¹]
          ac_rfl }
    have hδ : ∀ w, δ w = w * (y w)⁻¹ := fun _ => rfl
    have hker : δ.ker = fixSub y := by
      ext w
      rw [MonoidHom.mem_ker, hδ, mem_fixSub, mul_inv_eq_one, eq_comm]
    have hD4 : Nat.card δ.range = 4 := by
      have h1 := Subgroup.card_ker_mul_card_range δ
      rw [hker, h, hcard] at h1
      omega
    have hcD : ∀ x ∈ δ.range, c x ∈ δ.range := by
      rintro _ ⟨w, rfl⟩
      refine ⟨c w, ?_⟩
      rw [hδ, hδ, map_mul, map_inv, hcomm]
    have hyD : ∀ x ∈ δ.range, y x ∈ δ.range := by
      rintro _ ⟨w, rfl⟩
      exact ⟨y w, by rw [hδ, hδ, map_mul, map_inv]⟩
    have hfix := S153Q.Q4A.fix_of_stable hc3 hfpf hyc (c := δ.range) ⟨hD4, hcD⟩ hyD
      (m := 4) (by norm_num) hy4
    apply hy2
    ext w
    have h1 := hfix (δ w) ⟨w, rfl⟩
    rw [hδ, map_mul, map_inv] at h1
    rw [sq, MulAut.mul_apply, MulAut.one_apply]
    have h2 : (y (y w))⁻¹ = (y w)⁻¹ * (w * (y w)⁻¹) := by
      rw [← h1, inv_mul_cancel_left]
    simp only [hinv] at h2
    calc y (y w) = y w * (w * y w) := h2
      _ = w * (y w * y w) := by ac_rfl
      _ = w := by rw [hW2, mul_one]
  · omega
  ·
    exfalso
    apply hy2
    have htop : fixSub y = ⊤ := Subgroup.eq_top_of_card_eq _ (h.trans hcard.symm)
    ext w
    have : w ∈ fixSub y := htop ▸ Subgroup.mem_top w
    rw [sq, MulAut.mul_apply, mem_fixSub.mp this, mem_fixSub.mp this, MulAut.one_apply]

end Fix

end CFSG.Quasithin.H13.L32A
