module

public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank

public section

namespace CFSG.RankThree.PartTwo.KFacts

private theorem ks12lift_eq_one_of_sq_cube {X : Type} [Group X] {u : X} (h2 : u * u = 1)
    (h3 : u ^ 3 = 1) : u = 1 := by
  calc u = u * (u * u) := by rw [h2, mul_one]
    _ = u ^ 3 := (pow_three u).symm
    _ = 1 := h3

private theorem ks12lift_exists_mem_eq_mul {X : Type} [Group X] {Z : Subgroup X} {a b : X}
    (h : (a : X ⧸ Z) = b) : ∃ z ∈ Z, b = a * z :=
  ⟨a⁻¹ * b, QuotientGroup.eq.mp h, (mul_inv_cancel_left a b).symm⟩

private theorem ks12lift_defect_eq_one {X : Type} [Group X] {s w u : X} (hs : s ^ 2 = 1)
    (hu : ∀ g : X, g * u = u * g) (hu3 : u ^ 3 = 1) (h : w * s = s * w * u) : u = 1 := by
  have hss : s * s = 1 := by rw [← pow_two]; exact hs
  have h1 : s * w * s = w * u := by
    calc s * w * s = s * (w * s) := mul_assoc _ _ _
      _ = s * (s * w * u) := by rw [h]
      _ = s * s * w * u := by simp only [mul_assoc]
      _ = w * u := by rw [hss, one_mul]
  have h2 : s * w = w * s * u := by
    calc s * w = s * w * s * s := by rw [mul_assoc (s * w) s s, hss, mul_one]
      _ = w * u * s := by rw [h1]
      _ = w * (s * u) := by rw [mul_assoc, hu s]
      _ = w * s * u := (mul_assoc _ _ _).symm
  have h3 : w * s * 1 = w * s * (u * u) := by
    calc w * s * 1 = s * w * u := by rw [mul_one]; exact h
      _ = w * s * u * u := by rw [h2]
      _ = w * s * (u * u) := by simp only [mul_assoc]
  exact ks12lift_eq_one_of_sq_cube (mul_left_cancel h3).symm hu3

private theorem ks12lift_commute_of_mk {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZc : ∀ z ∈ Z, ∀ g : X, g * z = z * g) (hZexp : ∀ z ∈ Z, z ^ 3 = 1) {s w : X}
    (hs : s ^ 2 = 1) (hw : (s : X ⧸ Z) * (w : X ⧸ Z) = (w : X ⧸ Z) * (s : X ⧸ Z)) :
    s * w = w * s := by
  have hm : ((s * w : X) : X ⧸ Z) = ((w * s : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hw
  obtain ⟨u, hu, hwu⟩ := ks12lift_exists_mem_eq_mul hm
  have hu1 : u = 1 := ks12lift_defect_eq_one hs (fun g => hZc u hu g) (hZexp u hu) hwu
  rw [hu1, mul_one] at hwu
  exact hwu.symm

private theorem ks12lift_commutator_eq_one {X : Type} [Group X] {a b c g z₁ z₂ : X}
    (hcen : ∀ h : X, h * c = c * h) (hz₁ : ∀ h : X, h * z₁ = z₁ * h)
    (hz₂ : ∀ h : X, h * z₂ = z₂ * h) (hc3 : c ^ 3 = 1) (hc : b * a = a * b * c)
    (ha : g * a * g⁻¹ = a⁻¹ * z₁) (hb : g * b * g⁻¹ = b * z₂) : c = 1 := by
  have hgc : g * c * g⁻¹ = c := by
    rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (b * z₂) * (a⁻¹ * z₁) = (a⁻¹ * z₁) * (b * z₂) * c := by
    calc (b * z₂) * (a⁻¹ * z₁) = (g * b * g⁻¹) * (g * a * g⁻¹) := by rw [hb, ha]
      _ = g * (b * a) * g⁻¹ := by group
      _ = g * (a * b * c) * g⁻¹ := by rw [hc]
      _ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by group
      _ = (a⁻¹ * z₁) * (b * z₂) * c := by rw [ha, hb, hgc]
  have hL : (b * z₂) * (a⁻¹ * z₁) = b * a⁻¹ * (z₁ * z₂) := by
    calc (b * z₂) * (a⁻¹ * z₁) = b * (z₂ * a⁻¹) * z₁ := by group
      _ = b * (a⁻¹ * z₂) * z₁ := by rw [← hz₂ a⁻¹]
      _ = b * a⁻¹ * (z₂ * z₁) := by group
      _ = b * a⁻¹ * (z₁ * z₂) := by rw [hz₁ z₂]
  have hR : (a⁻¹ * z₁) * (b * z₂) = a⁻¹ * b * (z₁ * z₂) := by
    calc (a⁻¹ * z₁) * (b * z₂) = a⁻¹ * (z₁ * b) * z₂ := by group
      _ = a⁻¹ * (b * z₁) * z₂ := by rw [hz₁ b]
      _ = a⁻¹ * b * (z₁ * z₂) := by group
  rw [hL, hR] at hconj
  have hcancel : b * a⁻¹ = a⁻¹ * b * c := by
    apply mul_right_cancel (b := z₁ * z₂)
    calc b * a⁻¹ * (z₁ * z₂) = a⁻¹ * b * (z₁ * z₂) * c := hconj
      _ = a⁻¹ * b * ((z₁ * z₂) * c) := by group
      _ = a⁻¹ * b * (c * (z₁ * z₂)) := by rw [hcen (z₁ * z₂)]
      _ = a⁻¹ * b * c * (z₁ * z₂) := by group
  have hW : c = b⁻¹ * a * b * a⁻¹ := by
    calc c = (a⁻¹ * b)⁻¹ * (a⁻¹ * b * c) := by group
      _ = (a⁻¹ * b)⁻¹ * (b * a⁻¹) := by rw [← hcancel]
      _ = b⁻¹ * a * b * a⁻¹ := by group
  have hcinv : c⁻¹ = c := by
    calc c⁻¹ = (b * a)⁻¹ * (a * b) := by rw [hc]; group
      _ = a⁻¹ * (b⁻¹ * a * b * a⁻¹) * a := by group
      _ = a⁻¹ * c * a := by rw [hW]
      _ = c := by rw [hcen a⁻¹]; group
  have hsq : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [hcinv]
      _ = 1 := mul_inv_cancel c
  exact ks12lift_eq_one_of_sq_cube hsq hc3

private theorem ks12lift_cube_eq_one {X : Type} [Group X] {a g z : X}
    (hcen : ∀ h : X, h * a ^ 3 = a ^ 3 * h) (hz : ∀ h : X, h * z = z * h) (hz3 : z ^ 3 = 1)
    (hA3 : (a ^ 3) ^ 3 = 1) (ha : g * a * g⁻¹ = a⁻¹ * z) : a ^ 3 = 1 := by
  have hc : Commute a⁻¹ z := hz a⁻¹
  have h1 : g * a ^ 3 * g⁻¹ = (a ^ 3)⁻¹ := by
    rw [← conj_pow, ha, hc.mul_pow, hz3, mul_one, inv_pow]
  have h2 : g * a ^ 3 * g⁻¹ = a ^ 3 := by
    rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : a ^ 3 * a ^ 3 = 1 := by
    calc a ^ 3 * a ^ 3 = a ^ 3 * (g * a ^ 3 * g⁻¹) := by rw [h2]
      _ = a ^ 3 * (a ^ 3)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  exact ks12lift_eq_one_of_sq_cube h3 hA3

private theorem ks12lift_closure_props {X : Type} [Group X] {S : Set X} {s : X}
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSe : ∀ a ∈ S, a ^ 3 = 1)
    (hSs : ∀ a ∈ S, s * a = a * s) :
    IsMulCommutative (Subgroup.closure S) ∧ (∀ w ∈ Subgroup.closure S, w ^ 3 = 1) ∧
      Subgroup.closure S ≤ Subgroup.centralizer ({s} : Set X) := by
  have hpair : S.Pairwise Commute := fun a ha b hb _ => hSc a ha b hb
  have hcomm : ∀ u ∈ Subgroup.closure S, ∀ v ∈ Subgroup.closure S, u * v = v * u := by
    intro u hu v hv
    exact congrArg Subtype.val
      ((Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  refine ⟨Subgroup.isMulCommutative_closure hpair, ?_, ?_⟩
  · intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact hSe x hx
    | one => exact one_pow 3
    | mul x y hx hy hxe hye =>
      rw [(show Commute x y from hcomm x hx y hy).mul_pow, hxe, hye, one_mul]
    | inv x _ hxe => rw [inv_pow, hxe, inv_one]
  · rw [Subgroup.closure_le]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hSs a ha).symm

private theorem ks12lift_map_closure {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    {a b : X} :
    (Subgroup.closure (({a, b} : Set X) ∪ (Z : Set X))).map (QuotientGroup.mk' Z) =
      Subgroup.closure ({(a : X ⧸ Z), (b : X ⧸ Z)} : Set (X ⧸ Z)) := by
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have h1 : QuotientGroup.mk' Z s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
      rw [h1]
      exact Subgroup.one_mem _
  · apply Subgroup.closure_mono
    rintro _ (rfl | rfl)
    · exact ⟨a, Or.inl (Or.inl rfl), rfl⟩
    · exact ⟨b, Or.inl (Or.inr rfl), rfl⟩

private theorem ks12lift_card_of_map {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZ3 : Nat.card Z = 3) {E : Subgroup X} (hZE : Z ≤ E) {P : Subgroup (X ⧸ Z)}
    (hP : E.map (QuotientGroup.mk' Z) = P) (hP9 : Nat.card P = 9) : Nat.card E = 3 ^ 3 := by
  obtain ⟨f, hf⟩ : ∃ f : E →* X ⧸ Z, f = (QuotientGroup.mk' Z).comp E.subtype := ⟨_, rfl⟩
  have hrange : f.range = P := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hP]
  have hker_map : f.ker.map E.subtype = Z := by
    ext w
    constructor
    · intro hw
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hw
      have he' : ((e : X) : X ⧸ Z) = 1 := by
        have h1 := MonoidHom.mem_ker.mp he
        rw [hf] at h1
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp he'
    · intro hw
      refine Subgroup.mem_map.mpr ⟨⟨w, hZE hw⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      rw [hf]
      exact (QuotientGroup.eq_one_iff w).mpr hw
  have hker : Nat.card f.ker = 3 := by
    have h := Subgroup.card_map_of_injective (K := f.ker) (f := E.subtype)
      (Subgroup.subtype_injective E)
    rw [hker_map, hZ3] at h
    exact h.symm
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, hrange, hP9] at h1
  calc Nat.card E = 3 * 9 := h1.symm
    _ = 3 ^ 3 := by norm_num

private theorem ks12lift_elementary {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g) (hZexp : ∀ z ∈ Z, z ^ 3 = 1)
    (hZ3 : Nat.card Z = 3) {a b s : X} (hs2 : s ^ 2 = 1) (hab : a * b = b * a)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hsa : s * a = a * s) (hsb : s * b = b * s)
    (h9 : Nat.card (Subgroup.closure ({(a : X ⧸ Z), (b : X ⧸ Z)} : Set (X ⧸ Z))) = 9) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ w ∈ E, w ^ 3 = 1) ∧
      E ≤ Subgroup.centralizer ({s} : Set X) ∧ Nat.card E = 3 ^ 3 := by
  have hZE : Z ≤ Subgroup.closure (({a, b} : Set X) ∪ (Z : Set X)) := fun w hw =>
    Subgroup.subset_closure (Or.inr hw)
  have hSc : ∀ u ∈ (({a, b} : Set X) ∪ (Z : Set X)), ∀ v ∈ (({a, b} : Set X) ∪ (Z : Set X)),
      u * v = v * u := by
    intro u hu v hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hab
      · exact hab.symm
      · rfl
    · exact hZcen v hv u
    · exact (hZcen u hu v).symm
    · exact (hZcen u hu v).symm
  have hSe : ∀ u ∈ (({a, b} : Set X) ∪ (Z : Set X)), u ^ 3 = 1 := by
    intro u hu
    rcases hu with hu | hu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact ha3
      · exact hb3
    · exact hZexp u hu
  have hSs : ∀ u ∈ (({a, b} : Set X) ∪ (Z : Set X)), s * u = u * s := by
    intro u hu
    rcases hu with hu | hu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hsa
      · exact hsb
    · exact hZcen u hu s
  obtain ⟨hEc, hEp, hEx⟩ := ks12lift_closure_props hSc hSe hSs
  exact ⟨Subgroup.closure (({a, b} : Set X) ∪ (Z : Set X)), hEc, hEp, hEx,
    ks12lift_card_of_map hZ3 hZE ks12lift_map_closure h9⟩

theorem three_le_localRank_of_quotient_config {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {t x y g h : X ⧸ Z} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (htx : t * x = x * t) (hty : t * y = y * t)
    (h9 : Nat.card (Subgroup.closure ({x, y} : Set (X ⧸ Z))) = 9)
    (hgx : g * x * g⁻¹ = x⁻¹) (hgy : g * y * g⁻¹ = y) (hhx : h * x * h⁻¹ = x)
    (hhy : h * y * h⁻¹ = y⁻¹) :
    3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 X := by
  have hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZc hz) g
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z))
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨t₀, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective h
  have ht₀sq : t₀ ^ 2 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z t₀ 2).trans ht2)
  have hmk_t₀3 : ((t₀ ^ 3 : X) : X ⧸ Z) = (t₀ : X ⧸ Z) := by
    rw [QuotientGroup.mk_pow, pow_succ, ht2, one_mul]
  have ht₁sq0 : (t₀ ^ 3) ^ 2 = 1 := by
    have e : (t₀ ^ 3) ^ 2 = (t₀ ^ 2) ^ 3 := by group
    rw [e]
    exact hZexp _ ht₀sq
  obtain ⟨t₁, ht₁lift, ht₁sq⟩ : ∃ t₁ : X, ((t₁ : X ⧸ Z) = (t₀ : X ⧸ Z)) ∧ t₁ ^ 2 = 1 :=
    ⟨t₀ ^ 3, hmk_t₀3, ht₁sq0⟩
  have ht₁ne : t₁ ≠ 1 := by
    intro h1
    apply ht1
    rw [← ht₁lift, h1, QuotientGroup.mk_one]
  have htx' : t₁ * x₀ = x₀ * t₁ :=
    ks12lift_commute_of_mk hZcen hZexp ht₁sq (by rw [ht₁lift]; exact htx)
  have hty' : t₁ * y₀ = y₀ * t₁ :=
    ks12lift_commute_of_mk hZcen hZexp ht₁sq (by rw [ht₁lift]; exact hty)
  have hm_xy : ((x₀ * y₀ : X) : X ⧸ Z) = ((y₀ * x₀ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hxy
  obtain ⟨c, hcZ, hc⟩ := ks12lift_exists_mem_eq_mul hm_xy
  have hm1 : ((g₀ * x₀ * g₀⁻¹ : X) : X ⧸ Z) = ((x₀⁻¹ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hgx
  obtain ⟨z₁, hz₁, hgx'⟩ := ks12lift_exists_mem_eq_mul hm1.symm
  have hm2 : ((g₀ * y₀ * g₀⁻¹ : X) : X ⧸ Z) = ((y₀ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hgy
  obtain ⟨z₂, hz₂, hgy'⟩ := ks12lift_exists_mem_eq_mul hm2.symm
  have hm3 : ((h₀ * y₀ * h₀⁻¹ : X) : X ⧸ Z) = ((y₀⁻¹ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hhy
  obtain ⟨z₃, hz₃, hhy'⟩ := ks12lift_exists_mem_eq_mul hm3.symm
  have hc1 : c = 1 :=
    ks12lift_commutator_eq_one (hZcen c hcZ) (hZcen z₁ hz₁) (hZcen z₂ hz₂) (hZexp c hcZ) hc
      hgx' hgy'
  have hcomm : x₀ * y₀ = y₀ * x₀ := by
    rw [hc1, mul_one] at hc
    exact hc.symm
  have hx3Z : x₀ ^ 3 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z x₀ 3).trans hx3)
  have hy3Z : y₀ ^ 3 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z y₀ 3).trans hy3)
  have hx3eq : x₀ ^ 3 = 1 :=
    ks12lift_cube_eq_one (hZcen _ hx3Z) (hZcen z₁ hz₁) (hZexp z₁ hz₁) (hZexp _ hx3Z) hgx'
  have hy3eq : y₀ ^ 3 = 1 :=
    ks12lift_cube_eq_one (hZcen _ hy3Z) (hZcen z₃ hz₃) (hZexp z₃ hz₃) (hZexp _ hy3Z) hhy'
  obtain ⟨E, hEc, hEp, hEx, hcard⟩ :=
    ks12lift_elementary hZcen hZexp hZ3 ht₁sq hcomm hx3eq hy3eq htx' hty' h9
  exact CFSG.RankThree.PartTwo.Sec3.le_localRank_of_commute_involution (by norm_num) ht₁ne ht₁sq
    hEc hEp hEx hcard

private theorem ks12lift_card_eq_three_mul {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZ3 : Nat.card Z = 3) {E : Subgroup X} (hZE : Z ≤ E) {P : Subgroup (X ⧸ Z)}
    (hP : E.map (QuotientGroup.mk' Z) = P) : Nat.card E = 3 * Nat.card P := by
  obtain ⟨f, hf⟩ : ∃ f : E →* X ⧸ Z, f = (QuotientGroup.mk' Z).comp E.subtype := ⟨_, rfl⟩
  have hrange : f.range = P := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hP]
  have hker_map : f.ker.map E.subtype = Z := by
    ext w
    constructor
    · intro hw
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hw
      have he' : ((e : X) : X ⧸ Z) = 1 := by
        have h1 := MonoidHom.mem_ker.mp he
        rw [hf] at h1
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp he'
    · intro hw
      refine Subgroup.mem_map.mpr ⟨⟨w, hZE hw⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      rw [hf]
      exact (QuotientGroup.eq_one_iff w).mpr hw
  have hker : Nat.card f.ker = 3 := by
    have h := Subgroup.card_map_of_injective (K := f.ker) (f := E.subtype)
      (Subgroup.subtype_injective E)
    rw [hker_map, hZ3] at h
    exact h.symm
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, hrange] at h1
  exact h1.symm

private theorem ks12lift_card_map_of_inf {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    {C : Subgroup X} (hCZ : C ⊓ Z = ⊥) :
    Nat.card (C.map (QuotientGroup.mk' Z)) = Nat.card C := by
  obtain ⟨f, hf⟩ : ∃ f : C →* X ⧸ Z, f = (QuotientGroup.mk' Z).comp C.subtype := ⟨_, rfl⟩
  have hrange : f.range = C.map (QuotientGroup.mk' Z) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro a b hab
    have h1 : ((a : X) : X ⧸ Z) = ((b : X) : X ⧸ Z) := by
      rw [hf] at hab
      exact hab
    have h2 : (a : X)⁻¹ * (b : X) ∈ C ⊓ Z :=
      Subgroup.mem_inf.mpr ⟨C.mul_mem (C.inv_mem a.2) b.2, QuotientGroup.eq.mp h1⟩
    rw [hCZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, Subgroup.card_bot, one_mul, hrange] at h1
  exact h1

private theorem ks12lift_mem_iff {X : Type} [Group X] {Z : Subgroup X} [Z.Normal]
    (hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g) (hZexp : ∀ z ∈ Z, z ^ 3 = 1)
    {P C : Subgroup X} {N : ℕ} (hcop : Nat.Coprime 3 N) (hCN : ∀ c ∈ C, c ^ N = 1)
    (hsurj : ∀ q ∈ P, ∃ c ∈ C, ∃ z ∈ Z, q = c * z) (hCP : C ≤ P) (q : X) :
    q ∈ C ↔ q ∈ P ∧ q ^ N = 1 := by
  constructor
  · intro hq
    exact ⟨hCP hq, hCN q hq⟩
  · rintro ⟨hqP, hqN⟩
    obtain ⟨c, hcC, z, hzZ, hqe⟩ := hsurj q hqP
    have hcz : Commute c z := hZcen z hzZ c
    have hzN : z ^ N = 1 := by
      rw [hqe, hcz.mul_pow, hCN c hcC, one_mul] at hqN
      exact hqN
    have hz1 : z = 1 := by
      have h : z ^ Nat.gcd 3 N = 1 := pow_gcd_eq_one.mpr ⟨hZexp z hzZ, hzN⟩
      rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
      exact h
    rw [hqe, hz1, mul_one]
    exact hcC

public theorem exists_e9_le_e27_of_lifts {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {x₀ y₀ : X} (hcomm : x₀ * y₀ = y₀ * x₀) (hx3 : x₀ ^ 3 = 1) (hy3 : y₀ ^ 3 = 1)
    (h9 : Nat.card (Subgroup.closure ({QuotientGroup.mk x₀, QuotientGroup.mk y₀} :
      Set (X ⧸ Z))) = 9)
    {T : Subgroup (X ⧸ Z)} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hxT : QuotientGroup.mk x₀ ∈ Subgroup.normalizer (T : Set (X ⧸ Z))) :
    ∃ E F T' : Subgroup X, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
      Nat.card F = 27 ∧ T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ E ≤ Subgroup.normalizer (T' : Set X) := by
  have hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZc hz) g
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z))
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  have hx3Z : x₀ ^ 3 ∈ Z := by
    rw [hx3]
    exact Z.one_mem
  have hy3Z : y₀ ^ 3 ∈ Z := by
    rw [hy3]
    exact Z.one_mem
  have hx3Q : (QuotientGroup.mk x₀ : X ⧸ Z) ^ 3 = 1 :=
    (QuotientGroup.mk_pow Z x₀ 3).symm.trans ((QuotientGroup.eq_one_iff _).mpr hx3Z)
  have hy3Q : (QuotientGroup.mk y₀ : X ⧸ Z) ^ 3 = 1 :=
    (QuotientGroup.mk_pow Z y₀ 3).symm.trans ((QuotientGroup.eq_one_iff _).mpr hy3Z)
  have hZF : Z ≤ Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X)) := fun w hw =>
    Subgroup.subset_closure (Or.inr hw)
  have hSc : ∀ u ∈ (({x₀, y₀} : Set X) ∪ (Z : Set X)), ∀ v ∈ (({x₀, y₀} : Set X) ∪ (Z : Set X)),
      u * v = v * u := by
    intro u hu v hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hcomm
      · exact hcomm.symm
      · rfl
    · exact hZcen v hv u
    · exact (hZcen u hu v).symm
    · exact (hZcen u hu v).symm
  have hSe : ∀ u ∈ (({x₀, y₀} : Set X) ∪ (Z : Set X)), u ^ 3 = 1 := by
    intro u hu
    rcases hu with hu | hu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hx3
      · exact hy3
    · exact hZexp u hu
  obtain ⟨hFc, hFp, -⟩ := ks12lift_closure_props (s := 1) hSc hSe
    (fun u _ => by rw [one_mul, mul_one])
  have hFcard : Nat.card (Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X))) = 3 ^ 3 :=
    ks12lift_card_of_map hZ3 hZF ks12lift_map_closure h9
  have hFcard' : Nat.card (Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X))) = 27 :=
    hFcard.trans (by norm_num)
  have hZE : Z ≤ Subgroup.closure (({x₀} : Set X) ∪ (Z : Set X)) := fun w hw =>
    Subgroup.subset_closure (Or.inr hw)
  have hx₀1 : (QuotientGroup.mk x₀ : X ⧸ Z) ≠ 1 := by
    intro h1
    rw [h1] at h9
    have hle : Subgroup.closure ({1, (QuotientGroup.mk y₀ : X ⧸ Z)} : Set (X ⧸ Z)) ≤
        Subgroup.zpowers (QuotientGroup.mk y₀ : X ⧸ Z) := by
      rw [Subgroup.closure_le]
      intro w hw
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hc := Subgroup.card_le_of_le hle
    rw [h9, Nat.card_zpowers] at hc
    have hd : orderOf (QuotientGroup.mk y₀ : X ⧸ Z) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3Q
    have hle3 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hEmap : (Subgroup.closure (({x₀} : Set X) ∪ (Z : Set X))).map (QuotientGroup.mk' Z) =
      Subgroup.zpowers (QuotientGroup.mk x₀ : X ⧸ Z) := by
    have h := ks12lift_map_closure (Z := Z) (a := x₀) (b := x₀)
    simp only [Set.pair_eq_singleton] at h
    rw [h, Subgroup.zpowers_eq_closure]
  have hEcard : Nat.card (Subgroup.closure (({x₀} : Set X) ∪ (Z : Set X))) = 9 := by
    have hord : Nat.card (Subgroup.zpowers (QuotientGroup.mk x₀ : X ⧸ Z)) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hx3Q hx₀1
    have h := ks12lift_card_eq_three_mul hZ3 hZE hEmap
    rw [hord] at h
    omega
  have hEF : Subgroup.closure (({x₀} : Set X) ∪ (Z : Set X)) ≤
      Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X)) :=
    Subgroup.closure_mono (Set.union_subset_union
      (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) subset_rfl)
  obtain ⟨P, hP⟩ : ∃ P : Subgroup X, P = T.comap (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  have hmemP : ∀ n : X, n ∈ P ↔ (QuotientGroup.mk n : X ⧸ Z) ∈ T := fun n => by
    rw [hP]
    exact Iff.rfl
  have hZP : Z ≤ P := fun z hz => (hmemP z).mpr (by
    rw [(QuotientGroup.eq_one_iff z).mpr hz]
    exact T.one_mem)
  have hPT : P.map (QuotientGroup.mk' Z) = T := by
    rw [hP]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) T
  have hPcard : Nat.card P = 3 * Nat.card T := ks12lift_card_eq_three_mul hZ3 hZP hPT
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card T = 2 ^ a := IsPGroup.iff_card.mp hT2
  have hdvd : 2 ^ a ∣ Nat.card P := by
    rw [hPcard, ha]
    exact dvd_mul_left _ _
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : Subgroup P, Nat.card C₀ = 2 ^ a :=
    Sylow.exists_subgroup_card_pow_prime 2 hdvd
  obtain ⟨C, hC⟩ : ∃ C : Subgroup X, C = C₀.map P.subtype := ⟨_, rfl⟩
  have hCP : C ≤ P := by
    rw [hC]
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hCcard : Nat.card C = 2 ^ a := by
    rw [hC, Subgroup.card_map_of_injective (Subgroup.subtype_injective P), hC₀]
  have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have hCZ : C ⊓ Z = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    have h1 : Nat.card (C ⊓ Z : Subgroup X) ∣ 2 ^ a := by
      have := Subgroup.card_dvd_of_le (inf_le_left : C ⊓ Z ≤ C)
      rwa [hCcard] at this
    have h2 : Nat.card (C ⊓ Z : Subgroup X) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : C ⊓ Z ≤ Z)
      rwa [hZ3] at this
    have h3 := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    exact Nat.dvd_one.mp h3
  have hTC : C.map (QuotientGroup.mk' Z) = T := by
    have hle : C.map (QuotientGroup.mk' Z) ≤ T := by
      rw [Subgroup.map_le_iff_le_comap, ← hP]
      exact hCP
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    rw [ks12lift_card_map_of_inf hCZ, hCcard, ha]
  have hCpow : ∀ c ∈ C, c ^ (2 ^ a) = 1 := by
    intro c hc
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ : C))
    rw [hCcard] at h
    simpa using congrArg Subtype.val h
  have hsurj : ∀ q ∈ P, ∃ c ∈ C, ∃ z ∈ Z, q = c * z := by
    intro q hq
    have hqT : (QuotientGroup.mk q : X ⧸ Z) ∈ C.map (QuotientGroup.mk' Z) := by
      rw [hTC]
      exact (hmemP q).mp hq
    obtain ⟨c, hcC, hc⟩ := Subgroup.mem_map.mp hqT
    obtain ⟨z, hzZ, hqe⟩ := ks12lift_exists_mem_eq_mul (a := c) (b := q) hc
    exact ⟨c, hcC, z, hzZ, hqe⟩
  have hchar := ks12lift_mem_iff hZcen hZexp hcop hCpow hsurj hCP
  have hconj1 : ∀ a b : X, a * b * a⁻¹ = 1 ↔ b = 1 := by
    intro a b
    constructor
    · intro hab
      have hb : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [hb, hab]
      group
    · rintro rfl
      group
  have hPconj : ∀ n : X, x₀ * n * x₀⁻¹ ∈ P ↔ n ∈ P := by
    intro n
    rw [hmemP, hmemP, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxT (QuotientGroup.mk n : X ⧸ Z)).symm
  have hx₀N : x₀ ∈ Subgroup.normalizer (C : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe, hchar, hPconj, conj_pow, hconj1]
  have hZN : ∀ z ∈ Z, z ∈ Subgroup.normalizer (C : Set X) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hzn : z * n * z⁻¹ = n := by
      rw [← hZcen z hz n, mul_inv_cancel_right]
    rw [hzn]
  have hEN : Subgroup.closure (({x₀} : Set X) ∪ (Z : Set X)) ≤
      Subgroup.normalizer (C : Set X) := by
    rw [Subgroup.closure_le]
    rintro w (hw | hw)
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hx₀N
    · exact hZN w hw
  have hCne : C ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hCcard]
    have hTone := (Subgroup.one_lt_card_iff_ne_bot T).mpr hT1
    rwa [ha] at hTone
  have hCp2 : IsPGroup 2 C := IsPGroup.iff_card.mpr ⟨a, hCcard⟩
  exact ⟨Subgroup.closure (({x₀} : Set X) ∪ (Z : Set X)),
    Subgroup.closure (({x₀, y₀} : Set X) ∪ (Z : Set X)), C, hEF, ⟨hFc, hFp⟩, hEcard,
    hFcard', hCne, hCp2, hEN⟩

theorem exists_e9_le_e27_of_quotient_config {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3)
    {x y g h : X ⧸ Z} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (h9 : Nat.card (Subgroup.closure ({x, y} : Set (X ⧸ Z))) = 9)
    (hgx : g * x * g⁻¹ = x⁻¹) (hgy : g * y * g⁻¹ = y) (hhy : h * y * h⁻¹ = y⁻¹)
    {T : Subgroup (X ⧸ Z)} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hxT : x ∈ Subgroup.normalizer (T : Set (X ⧸ Z))) :
    ∃ E F T' : Subgroup X, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
      Nat.card F = 27 ∧ T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ E ≤ Subgroup.normalizer (T' : Set X) := by
  have hZcen : ∀ z ∈ Z, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZc hz) g
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z))
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective h
  have hm_xy : ((x₀ * y₀ : X) : X ⧸ Z) = ((y₀ * x₀ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hxy
  obtain ⟨c, hcZ, hc⟩ := ks12lift_exists_mem_eq_mul hm_xy
  have hm1 : ((g₀ * x₀ * g₀⁻¹ : X) : X ⧸ Z) = ((x₀⁻¹ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hgx
  obtain ⟨z₁, hz₁, hgx'⟩ := ks12lift_exists_mem_eq_mul hm1.symm
  have hm2 : ((g₀ * y₀ * g₀⁻¹ : X) : X ⧸ Z) = ((y₀ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hgy
  obtain ⟨z₂, hz₂, hgy'⟩ := ks12lift_exists_mem_eq_mul hm2.symm
  have hm3 : ((h₀ * y₀ * h₀⁻¹ : X) : X ⧸ Z) = ((y₀⁻¹ : X) : X ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    exact hhy
  obtain ⟨z₃, hz₃, hhy'⟩ := ks12lift_exists_mem_eq_mul hm3.symm
  have hc1 : c = 1 :=
    ks12lift_commutator_eq_one (hZcen c hcZ) (hZcen z₁ hz₁) (hZcen z₂ hz₂) (hZexp c hcZ) hc
      hgx' hgy'
  have hcomm : x₀ * y₀ = y₀ * x₀ := by
    rw [hc1, mul_one] at hc
    exact hc.symm
  have hx3Z : x₀ ^ 3 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z x₀ 3).trans hx3)
  have hy3Z : y₀ ^ 3 ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp ((QuotientGroup.mk_pow Z y₀ 3).trans hy3)
  have hx3eq : x₀ ^ 3 = 1 :=
    ks12lift_cube_eq_one (hZcen _ hx3Z) (hZcen z₁ hz₁) (hZexp z₁ hz₁) (hZexp _ hx3Z) hgx'
  have hy3eq : y₀ ^ 3 = 1 :=
    ks12lift_cube_eq_one (hZcen _ hy3Z) (hZcen z₃ hz₃) (hZexp z₃ hz₃) (hZexp _ hy3Z) hhy'
  exact exists_e9_le_e27_of_lifts Z hZc hZ3 hcomm hx3eq hy3eq h9 hT2 hT1 hxT

end CFSG.RankThree.PartTwo.KFacts
