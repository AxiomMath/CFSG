module

public import CFSG.Quasithin.Background.RonanF95Ebar
public import CFSG.Quasithin.Background.RonanF95Abstract

public section

namespace CFSG.Quasithin.RonanF95

variable {G : Type*} [Group G]

namespace FormHyp

variable {V₁ P : Subgroup G} [(V₁.subgroupOf P).Normal]

abbrev actGroup (V₁ P : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (P : Set G) ⊓ Subgroup.centralizer (V₁ : Set G)

theorem actGroup_conj (w : actGroup V₁ P) {p : G} (hp : p ∈ P) : (w : G) * p * (w : G)⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp w.2.1 p).mp hp

theorem actGroup_conj' (w : actGroup V₁ P) {p : G} (hp : p ∈ P) : (w : G)⁻¹ * p * (w : G) ∈ P := by
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (P : Set G)).inv_mem w.2.1) p).mp hp
  simpa using this

theorem actGroup_cent (w : actGroup V₁ P) {z : G} (hz : z ∈ V₁) : (w : G) * z * (w : G)⁻¹ = z := by
  have := Subgroup.mem_centralizer_iff.mp w.2.2 z hz
  rw [← this]
  group

noncomputable def conjA (hP : FormHyp V₁ P) (w : actGroup V₁ P) : Ebar V₁ P ≃* Ebar V₁ P :=
  hP.conjE (w : G) (fun _ hp => actGroup_conj w hp) (fun _ hp => actGroup_conj' w hp)
    (fun _ hz => actGroup_cent w hz)

theorem conjA_mk (hP : FormHyp V₁ P) (w : actGroup V₁ P) (p : ↥P) :
    hP.conjA w (QuotientGroup.mk p) =
      QuotientGroup.mk ⟨(w : G) * p * (w : G)⁻¹, actGroup_conj w p.2⟩ :=
  hP.conjE_mk _ _ _ _ p

theorem conjA_one (hP : FormHyp V₁ P) : hP.conjA 1 = MulEquiv.refl _ := by
  ext x
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [conjA_mk]
  show QuotientGroup.mk _ = QuotientGroup.mk p
  congr 1
  exact Subtype.ext (by simp)

theorem conjA_mul (hP : FormHyp V₁ P) (w₁ w₂ : actGroup V₁ P) :
    hP.conjA (w₁ * w₂) = (hP.conjA w₂).trans (hP.conjA w₁) := by
  ext x
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [conjA_mk]
  show QuotientGroup.mk _ = hP.conjA w₁ (hP.conjA w₂ (QuotientGroup.mk p))
  rw [conjA_mk, conjA_mk]
  congr 1
  exact Subtype.ext (by simp [mul_assoc])

noncomputable def conjHom (hP : FormHyp V₁ P) : actGroup V₁ P →* MulAut (Ebar V₁ P) where
  toFun := hP.conjA
  map_one' := hP.conjA_one
  map_mul' := hP.conjA_mul

theorem conjHom_apply_mk (hP : FormHyp V₁ P) (w : actGroup V₁ P) (p : ↥P) :
    hP.conjHom w (QuotientGroup.mk p) =
      QuotientGroup.mk ⟨(w : G) * p * (w : G)⁻¹, actGroup_conj w p.2⟩ :=
  hP.conjA_mk w p

theorem conjHom_eq_one_iff (hP : FormHyp V₁ P) (w : actGroup V₁ P) :
    hP.conjHom w = 1 ↔ ∀ p ∈ P, (w : G) * p * (w : G)⁻¹ * p⁻¹ ∈ V₁ := by
  constructor
  · intro h p hp
    have h1 := congrArg (fun f : MulAut (Ebar V₁ P) => f (QuotientGroup.mk ⟨p, hp⟩)) h
    simp only [conjHom_apply_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq_iff_div_mem.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [div_eq_mul_inv] using h2
  · intro h
    ext x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [conjHom_apply_mk, MulAut.one_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv] using h p p.2

theorem qf_conjHom (hP : FormHyp V₁ P) (w : actGroup V₁ P) (x : Ebar V₁ P) :
    hP.qf (hP.conjHom w x) = hP.qf x :=
  hP.qf_conjE (w : G) (fun _ hp => actGroup_conj w hp) (fun _ hp => actGroup_conj' w hp)
    (fun _ hz => actGroup_cent w hz) x

end FormHyp

theorem mem_actGroup_of {V₁ P : Subgroup G} {w : G} (hw : ∀ p ∈ P, w * p * w⁻¹ ∈ P)
    (hw' : ∀ p ∈ P, w⁻¹ * p * w ∈ P) (hw₁ : ∀ z ∈ V₁, w * z * w⁻¹ = z) :
    w ∈ FormHyp.actGroup V₁ P := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨hw p, fun hp => ?_⟩
    have := hw' _ hp
    simpa [mul_assoc] using this
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (mul_inv_eq_iff_eq_mul.mp (hw₁ z hz)).symm

theorem ggt_main_proof [Finite G] {V₁ P Xg Yg : Subgroup G} {v i : G} (hcard : Nat.card V₁ = 2)
    (hV₁P : V₁ ≤ P) (hcen : ∀ z ∈ V₁, ∀ p ∈ P, p * z = z * p)
    (hsq : ∀ p ∈ P, p * p ∈ V₁) (hcomm : ∀ p ∈ P, ∀ r ∈ P, p * r * p⁻¹ * r⁻¹ ∈ V₁)
    (hvN : ∀ p ∈ P, v * p * v⁻¹ ∈ P) (hvN' : ∀ p ∈ P, v⁻¹ * p * v ∈ P)
    (hiN : ∀ p ∈ P, i * p * i⁻¹ ∈ P) (hiN' : ∀ p ∈ P, i⁻¹ * p * i ∈ P)
    (hv₁ : ∀ z ∈ V₁, v * z * v⁻¹ = z) (hi₁ : ∀ z ∈ V₁, i * z * i⁻¹ = z)
    (hv2 : v * v = 1) (hi2 : i * i = 1) (hXP : Xg ≤ P) (hYP : Yg ≤ P) (hV₁X : V₁ ≤ Xg)
    (hV₁Y : V₁ ≤ Yg)
    (hX1 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Xg) (hX2 : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Xg)
    (hY1 : ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Yg) (hY2 : ∀ p ∈ P, i * p * i⁻¹ * p⁻¹ ∈ Yg)
    (hXY : Xg ⊓ Yg = V₁) (hXYs : Xg ⊔ Yg = P)
    (hXe : ∀ x ∈ Xg, x * x = 1) (hXc : ∀ x ∈ Xg, ∀ x' ∈ Xg, x * x' = x' * x)
    (hYe : ∀ y ∈ Yg, y * y = 1) (hYc : ∀ y ∈ Yg, ∀ y' ∈ Yg, y * y' = y' * y)
    (hXYcard : Nat.card Xg = Nat.card Yg)
    (hnd : ∀ p ∈ P, (∀ r ∈ P, p * r = r * p) → p ∈ V₁)
    (hX : Nat.card Xg = 2 ^ 3 ∨ Nat.card Xg = 2 ^ 5) :
    (∃ p ∈ P, (v * i) ^ 2 * p * ((v * i) ^ 2)⁻¹ * p⁻¹ ∉ V₁) ∧
      ((∀ p ∈ P, (v * i) ^ 3 * p * ((v * i) ^ 3)⁻¹ * p⁻¹ ∈ V₁) ∨
        (Nat.card Xg = 2 ^ 5 ∧
          ((∀ p ∈ P, (v * i) ^ 5 * p * ((v * i) ^ 5)⁻¹ * p⁻¹ ∈ V₁) ∨
            (∀ p ∈ P, (v * i) ^ 6 * p * ((v * i) ^ 6)⁻¹ * p⁻¹ ∈ V₁)))) := by
  have hP : FormHyp V₁ P := ⟨hcard, hV₁P, hcen, hsq, hcomm⟩
  haveI : (V₁.subgroupOf P).Normal := hP.normal
  letI : CommGroup (Ebar V₁ P) := hP.commGroup
  haveI : Finite (Ebar V₁ P) := hP.finite
  let v' : FormHyp.actGroup V₁ P := ⟨v, mem_actGroup_of hvN hvN' hv₁⟩
  let i' : FormHyp.actGroup V₁ P := ⟨i, mem_actGroup_of hiN hiN' hi₁⟩
  let a : Ebar V₁ P ≃* Ebar V₁ P := hP.conjHom v'
  let b : Ebar V₁ P ≃* Ebar V₁ P := hP.conjHom i'
  have hk : ∀ k : ℕ, (a * b) ^ k = 1 ↔
      ∀ p ∈ P, (v * i) ^ k * p * ((v * i) ^ k)⁻¹ * p⁻¹ ∈ V₁ := by
    intro k
    have e : (a * b) ^ k = hP.conjHom ((v' * i') ^ k) := by
      rw [map_pow, map_mul]
    rw [e, hP.conjHom_eq_one_iff]
    simp [v', i']
  have hndE : ∀ x : Ebar V₁ P, (∀ y, hP.bf x y = 0) → x = 1 := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    refine (QuotientGroup.eq_one_iff p).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    refine hnd p p.2 fun r hr => ?_
    have h1 := hx (QuotientGroup.mk ⟨r, hr⟩)
    rw [hP.bf_mk] at h1
    have h2 : (p : G) * r * (p : G)⁻¹ * r⁻¹ = 1 := by
      by_contra hc
      simp [hc] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
  have hinv : ∀ w : G, w * w = 1 → ∀ p : G, w * (w * p * w⁻¹) * w⁻¹ = p := by
    intro w hw p
    calc w * (w * p * w⁻¹) * w⁻¹ = (w * w) * p * (w * w)⁻¹ := by group
      _ = p := by rw [hw]; group
  have haa : ∀ x : Ebar V₁ P, a (a x) = x := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    show hP.conjHom v' (hP.conjHom v' (QuotientGroup.mk p)) = QuotientGroup.mk p
    rw [hP.conjHom_apply_mk, hP.conjHom_apply_mk]
    congr 1
    exact Subtype.ext (hinv v hv2 p)
  have hbb : ∀ x : Ebar V₁ P, b (b x) = x := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    show hP.conjHom i' (hP.conjHom i' (QuotientGroup.mk p)) = QuotientGroup.mk p
    rw [hP.conjHom_apply_mk, hP.conjHom_apply_mk]
    congr 1
    exact Subtype.ext (hinv i hi2 p)
  have hqa : ∀ x : Ebar V₁ P, hP.qf (a x) = hP.qf x := fun x => hP.qf_conjHom v' x
  have hqb : ∀ x : Ebar V₁ P, hP.qf (b x) = hP.qf x := fun x => hP.qf_conjHom i' x
  have hXa : ∀ x : Ebar V₁ P, x ∈ FormHyp.imgE V₁ P Xg ↔ a x = x := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [FormHyp.mem_imgE hV₁X p]
    show _ ↔ hP.conjHom v' (QuotientGroup.mk p) = QuotientGroup.mk p
    rw [hP.conjHom_apply_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf,
      ← hX1 p p.2]
    simp [v', div_eq_mul_inv]
  have hYb : ∀ y : Ebar V₁ P, y ∈ FormHyp.imgE V₁ P Yg ↔ b y = y := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [FormHyp.mem_imgE hV₁Y p]
    show _ ↔ hP.conjHom i' (QuotientGroup.mk p) = QuotientGroup.mk p
    rw [hP.conjHom_apply_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf,
      ← hY1 p p.2]
    simp [i', div_eq_mul_inv]
  have haX : ∀ x : Ebar V₁ P, a x * x ∈ FormHyp.imgE V₁ P Xg := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    show hP.conjHom v' (QuotientGroup.mk p) * QuotientGroup.mk p ∈ _
    rw [hP.conjHom_apply_mk, ← QuotientGroup.mk_mul, FormHyp.mem_imgE hV₁X]
    have h1 := hX2 p p.2
    have h2 : (p : G) * p ∈ V₁ := hsq p p.2
    have e : (v * p * v⁻¹) * p = (v * p * v⁻¹ * (p : G)⁻¹) * (p * p) := by group
    show v * p * v⁻¹ * p ∈ Xg
    rw [e]
    exact Xg.mul_mem h1 (hV₁X h2)
  have hbY : ∀ y : Ebar V₁ P, b y * y ∈ FormHyp.imgE V₁ P Yg := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    show hP.conjHom i' (QuotientGroup.mk p) * QuotientGroup.mk p ∈ _
    rw [hP.conjHom_apply_mk, ← QuotientGroup.mk_mul, FormHyp.mem_imgE hV₁Y]
    have h1 := hY2 p p.2
    have h2 : (p : G) * p ∈ V₁ := hsq p p.2
    have e : (i * p * i⁻¹) * p = (i * p * i⁻¹ * (p : G)⁻¹) * (p * p) := by group
    show i * p * i⁻¹ * p ∈ Yg
    rw [e]
    exact Yg.mul_mem h1 (hV₁Y h2)
  have hsup : FormHyp.imgE V₁ P (Xg ⊔ Yg) = FormHyp.imgE V₁ P Xg ⊔ FormHyp.imgE V₁ P Yg := by
    unfold FormHyp.imgE
    rw [Subgroup.subgroupOf_sup hXP hYP, Subgroup.map_sup]
  have hXYc : IsCompl (FormHyp.imgE V₁ P Xg) (FormHyp.imgE V₁ P Yg) := by
    constructor
    · rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
      have h1 := (FormHyp.mem_imgE hV₁X p).mp hx.1
      have h2 := (FormHyp.mem_imgE hV₁Y p).mp hx.2
      have h3 : (p : G) ∈ V₁ := by
        rw [← hXY]
        exact ⟨h1, h2⟩
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h3)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
      have h1 : (QuotientGroup.mk p : Ebar V₁ P) ∈ FormHyp.imgE V₁ P (Xg ⊔ Yg) :=
        (FormHyp.mem_imgE (hV₁X.trans le_sup_left) p).mpr (by rw [hXYs]; exact p.2)
      rwa [hsup] at h1
  have hqX : ∀ x ∈ FormHyp.imgE V₁ P Xg, hP.qf x = 0 := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := (FormHyp.mem_imgE hV₁X p).mp hx
    rw [hP.qf_mk]
    simp [hXe _ h1]
  have hqY : ∀ y ∈ FormHyp.imgE V₁ P Yg, hP.qf y = 0 := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := (FormHyp.mem_imgE hV₁Y p).mp hx
    rw [hP.qf_mk]
    simp [hYe _ h1]
  have hcardX := hP.card_imgE hV₁X hXP
  have hd : Nat.card (FormHyp.imgE V₁ P Xg) = 4 ∨ Nat.card (FormHyp.imgE V₁ P Xg) = 16 := by
    rcases hX with h | h <;> rw [h] at hcardX <;> omega
  obtain ⟨k2, k3⟩ := order_of_two_involutions (A := Ebar V₁ P) hP.exp hP.qf hP.bf hP.bf_left
    hP.bf_right hP.qf_mul hP.bf_alt hndE a b haa hbb hqa hqb (FormHyp.imgE V₁ P Xg)
    (FormHyp.imgE V₁ P Yg) hXa hYb haX hbY hXYc hqX hqY hd
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    exact k2 ((hk 2).mpr hcon)
  · rcases k3 with h3 | ⟨h16, h56⟩
    · exact Or.inl ((hk 3).mp h3)
    · refine Or.inr ⟨by omega, ?_⟩
      rcases h56 with h5 | h6
      · exact Or.inl ((hk 5).mp h5)
      · exact Or.inr ((hk 6).mp h6)

end CFSG.Quasithin.RonanF95
