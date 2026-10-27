module

public import CFSG.Quasithin.Recognition.G23Ctx.HStructure
public import CFSG.Quasithin.Recognition.G23Ctx.MSide

public section

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {G : Type} [Group G] {H H₁ H₂ M : Subgroup G}

@[expose] def Inner (X : Subgroup G) (w : G) : Prop :=
  ∃ s ∈ X, ∀ x ∈ X, w * x * w⁻¹ = s * x * s⁻¹

@[expose] def Inverts (X : Subgroup G) (w : G) : Prop :=
  ∀ x ∈ X, (w * x * w⁻¹ * x) ^ 4 = 1

theorem inner_of_mem_sup (hH : G23One H H₁ H₂) {k : G} (hk : k ∈ H₁ ⊔ H₂) :
    Inner H₁ k ∧ Inner H₂ k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (G23One.mem_sup_iff hH).mp hk
  refine ⟨⟨a, ha, fun x hx => ?_⟩, ⟨b, hb, fun x hx => ?_⟩⟩
  · have hbx : b * x = x * b := (G23One.comm_one_two hH hx hb).symm
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
      _ = a * x * a⁻¹ := by group
  · have hxa : a * (b * x * b⁻¹) = (b * x * b⁻¹) * a :=
      G23One.comm_one_two hH ha (H₂.mul_mem (H₂.mul_mem hb hx) (H₂.inv_mem hb))
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = ((b * x * b⁻¹) * a) * a⁻¹ := by rw [hxa]
      _ = b * x * b⁻¹ := by group

theorem Inner.mul {X : Subgroup G} {u v : G} (hu : Inner X u) (hv : Inner X v)
    (hX : ∀ x ∈ X, v * x * v⁻¹ ∈ X) : Inner X (u * v) := by
  obtain ⟨s, hs, hsu⟩ := hu
  obtain ⟨t, ht, htv⟩ := hv
  refine ⟨s * t, X.mul_mem hs ht, fun x hx => ?_⟩
  calc u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
    _ = s * (v * x * v⁻¹) * s⁻¹ := hsu _ (hX x hx)
    _ = s * (t * x * t⁻¹) * s⁻¹ := by rw [htv x hx]
    _ = s * t * x * (s * t)⁻¹ := by group

private def conjAut (X : Subgroup G) (w : G) (hw : ∀ x, x ∈ X ↔ w * x * w⁻¹ ∈ X) :
    ↥X ≃* ↥X where
  toFun x := ⟨w * x * w⁻¹, (hw x).mp x.2⟩
  invFun x := ⟨w⁻¹ * x * w, (hw _).mpr (by simpa [mul_assoc] using x.2)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem inner_or_inverts₁ (hH : G23One H H₁ H₂) {w : G} (hw : w ∈ H) :
    Inner H₁ w ∨ (Inverts H₁ w ∧ ∃ q ∈ H₁, q ^ 4 = 1 ∧ w * q * w⁻¹ ≠ q) := by
  have hn : ∀ x, x ∈ H₁ ↔ w * x * w⁻¹ ∈ H₁ := fun x =>
    Subgroup.mem_normalizer_iff.mp (hH.normal_one hw) x
  rcases sl23_aut_dichotomy hH.iso_one (conjAut H₁ w hn) with ⟨s, hs⟩ | ⟨hinv, q, hq4, hq⟩
  · left
    refine ⟨(s : G), s.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (hs ⟨x, hx⟩)
    simpa [conjAut] using this
  · right
    refine ⟨fun x hx => ?_, (q : G), q.2, ?_, ?_⟩
    · have := congrArg Subtype.val (hinv ⟨x, hx⟩)
      have h4 : (((conjAut H₁ w hn) ⟨x, hx⟩ * ⟨x, hx⟩ : ↥H₁) ^ 4 : ↥H₁) = 1 := hinv ⟨x, hx⟩
      simpa [conjAut] using congrArg Subtype.val h4
    · simpa using congrArg Subtype.val hq4
    · intro h
      apply hq
      exact Subtype.ext (by simpa [conjAut] using h)

theorem inner_or_inverts₂ (hH : G23One H H₁ H₂) {w : G} (hw : w ∈ H) :
    Inner H₂ w ∨ (Inverts H₂ w ∧ ∃ q ∈ H₂, q ^ 4 = 1 ∧ w * q * w⁻¹ ≠ q) :=
  inner_or_inverts₁ (g23One_symm hH) hw

theorem not_inner_of_inverts₁ (hH : G23One H H₁ H₂) {w : G} (hw : w ∈ H)
    (h : Inverts H₁ w) : ¬ Inner H₁ w := by
  rintro ⟨s, hs, hsx⟩
  obtain ⟨x, hx⟩ := sl23_inner_not_inverts hH.iso_one ⟨s, hs⟩
  apply hx
  apply Subtype.ext
  have := h x x.2
  rw [hsx x x.2] at this
  simpa using this

theorem fitting_le_sup [Finite G] (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z)
    (hM : G23Two M) (hzV : z ∈ quasithinGenFitting M) :
    quasithinGenFitting M ≤ H₁ ⊔ H₂ := by
  obtain ⟨a, b, y, h, haV, hbV, ha1, haz, hb1, hbz, hab1, habz, hgen, hyM, hy3, hyz, hya, hyb,
    -, -, -, -⟩ := exists_basis_act hM hzV hz.ne_one
  have hzK : z ∈ H₁ ⊔ H₂ := (le_sup_left : H₁ ≤ H₁ ⊔ H₂) hz.mem_left
  have haH : a ∈ H := mem_H_of_comm hH hz (G23Two.fitting_comm hM haV hzV)
  have hbH : b ∈ H := mem_H_of_comm hH hz (G23Two.fitting_comm hM hbV hzV)
  have hyH : y ∈ H := mem_H_of_comm hH hz (by
    have := hyz
    rwa [mul_inv_eq_iff_eq_mul] at this)
  have hyK : y ∈ H₁ ⊔ H₂ := mem_sup_of_odd hH hyH (n := 3) ⟨1, rfl⟩ hy3
  have hb2 : b * b = 1 := G23Two.sq_fitting hM hbV
  have ha2 : a * a = 1 := G23Two.sq_fitting hM haV
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have habK : a * b ∈ H₁ ⊔ H₂ := by
    have h1 := commutator_mem_sup hH haH hyH
    have e : a * y * a⁻¹ * y⁻¹ = a * (y * a * y⁻¹)⁻¹ := by group
    rw [e, hya, hbi] at h1
    exact h1
  have haK : a ∈ H₁ ⊔ H₂ := by
    have h1 := commutator_mem_sup hH hbH hyH
    have e : b * y * b⁻¹ * y⁻¹ = b * (y * b * y⁻¹)⁻¹ := by group
    rw [e, hyb] at h1
    have e2 : b * (a * b)⁻¹ = a⁻¹ := by group
    rw [e2] at h1
    simpa using (H₁ ⊔ H₂).inv_mem h1
  have hbK : b ∈ H₁ ⊔ H₂ := by
    have := (H₁ ⊔ H₂).mul_mem ((H₁ ⊔ H₂).inv_mem haK) habK
    simpa using this
  intro v hv
  refine (Subgroup.closure_le (H₁ ⊔ H₂)).mpr ?_ (hgen v hv)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hzK
  · exact haK
  · exact hbK

theorem component_conj (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {h c₁ c₂ d₁ d₂ : G}
    (hh : h ∈ H) (hc₁ : c₁ ∈ H₁) (hc₂ : c₂ ∈ H₂) (hd₁ : d₁ ∈ H₁) (hd₂ : d₂ ∈ H₂)
    (hrel : h * (c₁ * c₂) * h⁻¹ = d₁ * d₂) :
    h * c₁ * h⁻¹ = d₁ ∨ h * c₁ * h⁻¹ = d₁ * z := by
  have hp : h * c₁ * h⁻¹ ∈ H₁ := (Subgroup.mem_normalizer_iff.mp (hH.normal_one hh) c₁).mp hc₁
  have hq : h * c₂ * h⁻¹ ∈ H₂ := (Subgroup.mem_normalizer_iff.mp (hH.normal_two hh) c₂).mp hc₂
  have hpq : (h * c₁ * h⁻¹) * (h * c₂ * h⁻¹) = d₁ * d₂ := by rw [← hrel]; group
  have ht1 : d₁⁻¹ * (h * c₁ * h⁻¹) ∈ H₁ := H₁.mul_mem (H₁.inv_mem hd₁) hp
  have ht2 : d₁⁻¹ * (h * c₁ * h⁻¹) = d₂ * (h * c₂ * h⁻¹)⁻¹ := by
    calc d₁⁻¹ * (h * c₁ * h⁻¹)
        = d₁⁻¹ * ((h * c₁ * h⁻¹) * (h * c₂ * h⁻¹)) * (h * c₂ * h⁻¹)⁻¹ := by group
      _ = d₁⁻¹ * (d₁ * d₂) * (h * c₂ * h⁻¹)⁻¹ := by rw [hpq]
      _ = d₂ * (h * c₂ * h⁻¹)⁻¹ := by group
  have ht : d₁⁻¹ * (h * c₁ * h⁻¹) ∈ H₁ ⊓ H₂ :=
    ⟨ht1, by rw [ht2]; exact H₂.mul_mem hd₂ (H₂.inv_mem hq)⟩
  have e : h * c₁ * h⁻¹ = d₁ * (d₁⁻¹ * (h * c₁ * h⁻¹)) := by group
  rcases hz.uniq _ ht with h0 | h0
  · left; rw [e, h0, mul_one]
  · right; rw [e, h0]

theorem comp_ne (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {u u₁ u₂ : G} (hu₂ : u₂ ∈ H₂)
    (hue : u = u₁ * u₂) (hu₁ : u₁ ∈ H₁) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    u₁ ≠ 1 ∧ u₁ ≠ z := by
  have key : u₁ = 1 ∨ u₁ = z → False := by
    intro h
    have hu₁₂ : u₁ ∈ H₂ := by
      rcases h with rfl | rfl
      · exact H₂.one_mem
      · exact hz.mem_right
    have : u ∈ H₂ := by rw [hue]; exact H₂.mul_mem hu₁₂ hu₂
    rcases invol_mem_right hH hz this hu2 with h' | h'
    exacts [hu1 h', huz h']
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem comp_ne_comp (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {a₁ a₂ b₁ b₂ : G}
    (ha₁ : a₁ ∈ H₁) (ha₂ : a₂ ∈ H₂) (hb₁ : b₁ ∈ H₁) (hb₂ : b₂ ∈ H₂) (hb₁4 : b₁ ^ 4 = 1)
    (hab2 : (a₁ * a₂ * (b₁ * b₂)) * (a₁ * a₂ * (b₁ * b₂)) = 1)
    (hab1 : a₁ * a₂ * (b₁ * b₂) ≠ 1) (habz : a₁ * a₂ * (b₁ * b₂) ≠ z) :
    a₁ ≠ b₁ ∧ a₁ ≠ b₁ * z := by
  have hb₁H : b₁ ∈ H := hH.le_one hb₁
  have hbb : b₁ * b₁ ∈ H₁ := H₁.mul_mem hb₁ hb₁
  have hbb2 : (b₁ * b₁) * (b₁ * b₁) = 1 := by
    have : b₁ ^ 4 = (b₁ * b₁) * (b₁ * b₁) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]; exact hb₁4
  have hbbz : b₁ * b₁ = 1 ∨ b₁ * b₁ = z := invol_mem_left hH hz hbb hbb2
  have hzz : z * z = 1 := hz.mul_self
  have hcomm : b₁ * a₂ = a₂ * b₁ := G23One.comm_one_two hH hb₁ ha₂
  have key : ∀ t : G, (t = 1 ∨ t = z) → a₁ = b₁ * t → False := by
    intro t ht hat
    have hbt : t * b₁ = b₁ * t := by
      rcases ht with rfl | rfl
      · simp
      · exact (IsZ.comm hH hz hb₁H).symm
    have hs : a₁ * b₁ = (b₁ * b₁) * t := by
      rw [hat]
      calc b₁ * t * b₁ = b₁ * (t * b₁) := by rw [mul_assoc]
        _ = b₁ * (b₁ * t) := by rw [hbt]
        _ = (b₁ * b₁) * t := by rw [mul_assoc]
    have hs₂ : a₁ * b₁ ∈ H₂ := by
      rw [hs]
      have h1 : b₁ * b₁ ∈ H₂ := by
        rcases hbbz with h | h
        · rw [h]; exact H₂.one_mem
        · rw [h]; exact hz.mem_right
      have h2 : t ∈ H₂ := by
        rcases ht with h | h
        · rw [h]; exact H₂.one_mem
        · rw [h]; exact hz.mem_right
      exact H₂.mul_mem h1 h2
    have hab : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
      calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [← hcomm]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
    have hmem : a₁ * a₂ * (b₁ * b₂) ∈ H₂ := by
      rw [hab]; exact H₂.mul_mem hs₂ (H₂.mul_mem ha₂ hb₂)
    rcases invol_mem_right hH hz hmem hab2 with h | h
    exacts [hab1 h, habz h]
  exact ⟨fun h => key 1 (Or.inl rfl) (by rw [mul_one]; exact h),
    fun h => key z (Or.inr rfl) h⟩

theorem not_inner_one_of_swap (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z)
    {h a b a₁ a₂ b₁ b₂ : G} (hhH : h ∈ H) (ha₁ : a₁ ∈ H₁) (ha₂ : a₂ ∈ H₂) (hb₁ : b₁ ∈ H₁)
    (hb₂ : b₂ ∈ H₂) (hae : a = a₁ * a₂) (hbe : b = b₁ * b₂) (ha₁4 : a₁ ^ 4 = 1)
    (hb₁4 : b₁ ^ 4 = 1) (hab : h * a * h⁻¹ = b) (hba : h * b * h⁻¹ = a) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hab2 : (a * b) * (a * b) = 1) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1)
    (hbz : b ≠ z) (hab1 : a * b ≠ 1) (habz : a * b ≠ z) : ¬ Inner H₁ h := by
  rintro ⟨s, hs, hsx⟩
  have h1 := component_conj hH hz hhH ha₁ ha₂ hb₁ hb₂ (by rw [← hae, ← hbe]; exact hab)
  have h2 := component_conj hH hz hhH hb₁ hb₂ ha₁ ha₂ (by rw [← hae, ← hbe]; exact hba)
  obtain ⟨ha₁1, ha₁z⟩ := comp_ne hH hz ha₂ hae ha₁ ha2 ha1 haz
  obtain ⟨hb₁1, hb₁z⟩ := comp_ne hH hz hb₂ hbe hb₁ hb2 hb1 hbz
  have hab2' : (a₁ * a₂ * (b₁ * b₂)) * (a₁ * a₂ * (b₁ * b₂)) = 1 := by
    rw [← hae, ← hbe]; exact hab2
  obtain ⟨hne1, hne2⟩ := comp_ne_comp hH hz ha₁ ha₂ hb₁ hb₂ hb₁4 hab2'
    (by rw [← hae, ← hbe]; exact hab1) (by rw [← hae, ← hbe]; exact habz)
  have hz2 : (⟨z, hz.mem_left⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hz.mul_self)
  have hz1 : (⟨z, hz.mem_left⟩ : ↥H₁) ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  refine sl23_not_inner_swap hH.iso_one hz2 hz1 ⟨s, hs⟩ ⟨a₁, ha₁⟩ ⟨b₁, hb₁⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
  · exact Subtype.ext (by simpa using ha₁4)
  · exact Subtype.ext (by simpa using hb₁4)
  · exact fun h => ha₁1 (congrArg Subtype.val h)
  · exact fun h => ha₁z (congrArg Subtype.val h)
  · exact fun h => hb₁1 (congrArg Subtype.val h)
  · exact fun h => hb₁z (congrArg Subtype.val h)
  · exact fun h => hne1 (congrArg Subtype.val h)
  · exact fun h => hne2 (congrArg Subtype.val h)
  · rcases h1 with h | h
    · left; apply Subtype.ext; show s * a₁ * s⁻¹ = b₁; rw [← hsx a₁ ha₁]; exact h
    · right; apply Subtype.ext; show s * a₁ * s⁻¹ = b₁ * z; rw [← hsx a₁ ha₁]; exact h
  · rcases h2 with h | h
    · left; apply Subtype.ext; show s * b₁ * s⁻¹ = a₁; rw [← hsx b₁ hb₁]; exact h
    · right; apply Subtype.ext; show s * b₁ * s⁻¹ = a₁ * z; rw [← hsx b₁ hb₁]; exact h

theorem not_inner_two_of_swap (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z)
    {h a b a₁ a₂ b₁ b₂ : G} (hhH : h ∈ H) (ha₁ : a₁ ∈ H₁) (ha₂ : a₂ ∈ H₂) (hb₁ : b₁ ∈ H₁)
    (hb₂ : b₂ ∈ H₂) (hae : a = a₁ * a₂) (hbe : b = b₁ * b₂) (ha₂4 : a₂ ^ 4 = 1)
    (hb₂4 : b₂ ^ 4 = 1) (hab : h * a * h⁻¹ = b) (hba : h * b * h⁻¹ = a) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hab2 : (a * b) * (a * b) = 1) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1)
    (hbz : b ≠ z) (hab1 : a * b ≠ 1) (habz : a * b ≠ z) : ¬ Inner H₂ h := by
  have hae' : a = a₂ * a₁ := by rw [hae]; exact G23One.comm_one_two hH ha₁ ha₂
  have hbe' : b = b₂ * b₁ := by rw [hbe]; exact G23One.comm_one_two hH hb₁ hb₂
  have hab2' : (a * b) * (a * b) = 1 := hab2
  exact not_inner_one_of_swap (g23One_symm hH) hz.symm hhH ha₂ ha₁ hb₂ hb₁ hae' hbe' ha₂4 hb₂4
    hab hba ha2 hb2 hab2' ha1 haz hb1 hbz hab1 habz

theorem inverts_of_not_mem_sup [Finite G] (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z)
    (hM : G23Two M) (hzV : z ∈ quasithinGenFitting M) {w : G} (hw : w ∈ H)
    (hwK : w ∉ H₁ ⊔ H₂) : Inverts H₁ w ∧ Inverts H₂ w := by
  obtain ⟨a, b, y, h, haV, hbV, ha1, haz, hb1, hbz, hab1, habz, hgen, -, -, -, -, -, hhM, hhz,
    hha, hhb⟩ := exists_basis_act hM hzV hz.ne_one
  have hVK := fitting_le_sup hH hz hM hzV
  have hhH : h ∈ H := mem_H_of_comm hH hz (by
    have := hhz
    rwa [mul_inv_eq_iff_eq_mul] at this)
  have hb2 : b * b = 1 := G23Two.sq_fitting hM hbV
  have ha2 : a * a = 1 := G23Two.sq_fitting hM haV
  have hab2 : (a * b) * (a * b) = 1 :=
    G23Two.sq_fitting hM ((quasithinGenFitting M).mul_mem haV hbV)
  obtain ⟨a₁, ha₁, a₂, ha₂, haeq, ha₁4, ha₂4⟩ := split_invol hH hz (hVK haV) ha2
  obtain ⟨b₁, hb₁, b₂, hb₂, hbeq, hb₁4, hb₂4⟩ := split_invol hH hz (hVK hbV) hb2
  have hnot1 : ¬ Inner H₁ h :=
    not_inner_one_of_swap hH hz hhH ha₁ ha₂ hb₁ hb₂ haeq hbeq ha₁4 hb₁4 hha hhb ha2 hb2 hab2
      ha1 haz hb1 hbz hab1 habz
  have hnot2 : ¬ Inner H₂ h :=
    not_inner_two_of_swap hH hz hhH ha₁ ha₂ hb₁ hb₂ haeq hbeq ha₂4 hb₂4 hha hhb ha2 hb2 hab2
      ha1 haz hb1 hbz hab1 habz
  have hhK : h ∉ H₁ ⊔ H₂ := fun hk => hnot1 (inner_of_mem_sup hH hk).1
  have hwh : w * h⁻¹ ∈ H₁ ⊔ H₂ := mul_inv_mem_sup hH hw hhH hwK hhK
  have hkinv : (w * h⁻¹)⁻¹ ∈ H₁ ⊔ H₂ := (H₁ ⊔ H₂).inv_mem hwh
  have e : (w * h⁻¹)⁻¹ * w = h := by group
  have hnw1 : ¬ Inner H₁ w := by
    intro hin
    apply hnot1
    have := Inner.mul (inner_of_mem_sup hH hkinv).1 hin
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hH.normal_one hw) x).mp hx)
    rwa [e] at this
  have hnw2 : ¬ Inner H₂ w := by
    intro hin
    apply hnot2
    have := Inner.mul (inner_of_mem_sup hH hkinv).2 hin
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hH.normal_two hw) x).mp hx)
    rwa [e] at this
  refine ⟨?_, ?_⟩
  · rcases inner_or_inverts₁ hH hw with h1 | ⟨h1, -⟩
    · exact absurd h1 hnw1
    · exact h1
  · rcases inner_or_inverts₂ hH hw with h1 | ⟨h1, -⟩
    · exact absurd h1 hnw2
    · exact h1

theorem inv_field (hH : G23One H H₁ H₂) {w : G} (hw : w ∈ H) (h₁ : Inverts H₁ w)
    (h₂ : Inverts H₂ w) : ∀ x ∈ H₁ ⊔ H₂, w * x * w⁻¹ * x ∈ pCoreOf 2 H := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (G23One.mem_sup_iff hH).mp hx
  have hwa : w * a * w⁻¹ ∈ H₁ := (Subgroup.mem_normalizer_iff.mp (hH.normal_one hw) a).mp ha
  have hwb : w * b * w⁻¹ ∈ H₂ := (Subgroup.mem_normalizer_iff.mp (hH.normal_two hw) b).mp hb
  have hc : a * (w * b * w⁻¹) = (w * b * w⁻¹) * a := G23One.comm_one_two hH ha hwb
  have e : w * (a * b) * w⁻¹ * (a * b) =
      (w * a * w⁻¹ * a) * (w * b * w⁻¹ * b) := by
    calc w * (a * b) * w⁻¹ * (a * b) = (w * a * w⁻¹) * (w * b * w⁻¹) * a * b := by group
      _ = (w * a * w⁻¹) * ((w * b * w⁻¹) * a) * b := by group
      _ = (w * a * w⁻¹) * (a * (w * b * w⁻¹)) * b := by rw [hc]
      _ = (w * a * w⁻¹ * a) * (w * b * w⁻¹ * b) := by group
  rw [e]
  refine (pCoreOf 2 H).mul_mem ?_ ?_
  · exact pow4_mem_pCoreOf hH (H₁.mul_mem hwa ha) (h₁ a ha)
  · exact pow4_mem_pCoreOf (g23One_symm hH) (H₂.mul_mem hwb hb) (h₂ b hb)

end CFSG.Quasithin.G23Type.Ctx
