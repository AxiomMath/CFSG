module

public import CFSG.Quasithin.EmptyFaithful.S152Y28
public import CFSG.Quasithin.EmptyFaithful.S152Y11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

theorem model_line : ∀ ρ : D33, ρ * ρ = 1 → (∃ a : D33, a ^ 3 = 1 ∧ ρ * a * ρ⁻¹ ≠ a) →
    ∃ α : D33, α ^ 3 = 1 ∧ ρ * α * ρ⁻¹ ≠ α ∧
      ∀ t : D33, t * t = 1 → t * ρ = ρ * t → t * α * t⁻¹ = α ∨ t * α * t⁻¹ = α⁻¹ := by
  decide +kernel

theorem exists_invariant_line {B : Type*} [Group B] (X : Subgroup B) (e : ↥X ≃* D33)
    {ρ : B} (hρX : ρ ∈ X) (hρ2 : ρ * ρ = 1) (hact : ∃ a ∈ oTwoUpper X, ρ * a * ρ⁻¹ ≠ a) :
    ∃ α : B, α ∈ oTwoUpper X ∧ α ^ 3 = 1 ∧ ρ * α * ρ⁻¹ ≠ α ∧
      ∀ t ∈ X, t * t = 1 → t * ρ = ρ * t → t * α * t⁻¹ = α ∨ t * α * t⁻¹ = α⁻¹ := by
  have hφ := omshφ_inj X e
  obtain ⟨a, haX, hρa⟩ := hact
  obtain ⟨a₀, ha₀3, rfl⟩ := (omsh_mem_O X e).mp haX
  have hdρ : omshφ X e (e ⟨ρ, hρX⟩) = ρ := omshφ_eq X e hρX
  have hd2 : e ⟨ρ, hρX⟩ * e ⟨ρ, hρX⟩ = 1 := hφ (by rw [map_mul, map_one, hdρ]; exact hρ2)
  obtain ⟨α₀, hα3, hα, hall⟩ := model_line (e ⟨ρ, hρX⟩) hd2 ⟨a₀, ha₀3, fun h => hρa (by
    have := congrArg (omshφ X e) h
    rwa [map_mul, map_mul, map_inv, hdρ] at this)⟩
  refine ⟨omshφ X e α₀, (omsh_mem_O X e).mpr ⟨α₀, hα3, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_pow, hα3, map_one]
  · intro h
    apply hα
    apply hφ
    rw [map_mul, map_mul, map_inv, hdρ]
    exact h
  · intro t htX ht2 htρ
    obtain ⟨dt, rfl⟩ := omsh_exists_elt X e htX
    have hdt2 : dt * dt = 1 := hφ (by rw [map_mul, map_one]; exact ht2)
    have hcomm : dt * e ⟨ρ, hρX⟩ = e ⟨ρ, hρX⟩ * dt := hφ (by rw [map_mul, map_mul, hdρ]; exact htρ)
    rcases hall dt hdt2 hcomm with h | h
    · left
      rw [← map_inv, ← map_mul, ← map_mul, h]
    · right
      rw [← map_inv, ← map_mul, ← map_mul, h, map_inv]

namespace S152Y

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

@[expose] def starPre (M : Subgroup G) (W : Subgroup (OTwoQuot M)) : Subgroup G :=
  (W.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))).map M.subtype

omit [Finite G] in
theorem mem_starPre {W : Subgroup (OTwoQuot M)} {x : G} :
    x ∈ starPre M W ↔ ∃ hx : x ∈ M, (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M) ∈ W := by
  unfold starPre
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hW⟩
    exact ⟨⟨x, hx⟩, hW, rfl⟩

omit [Finite G] in
theorem imageOTwoQuot_inf_starPre {X : Subgroup G} {W : Subgroup (OTwoQuot M)} :
    imageOTwoQuot M (X ⊓ starPre M W) = imageOTwoQuot M X ⊓ W := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hxM, ⟨hxX, hxP⟩, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨hx', hxW⟩ := mem_starPre.mp hxP
    exact ⟨mem_imageOTwoQuot_iff.mpr ⟨x, hxM, hxX, rfl⟩, hxW⟩
  · rintro ⟨hu, huW⟩
    obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact mem_imageOTwoQuot_iff.mpr ⟨x, hxM, ⟨hxX, mem_starPre.mpr ⟨hxM, huW⟩⟩, rfl⟩

omit [Finite G] in
theorem mk_conj_eq {t x : G} (htM : t ∈ M) (hxM : x ∈ M) (hcM : t * x * t⁻¹ ∈ M) :
    (QuotientGroup.mk ⟨t * x * t⁻¹, hcM⟩ : OTwoQuot M) =
      QuotientGroup.mk ⟨t, htM⟩ * QuotientGroup.mk ⟨x, hxM⟩ * (QuotientGroup.mk ⟨t, htM⟩)⁻¹ := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
theorem le_normalizer_starPre {T : Subgroup G} (hTM : T ≤ M) {W : Subgroup (OTwoQuot M)}
    (hT : imageOTwoQuot M T ≤ Subgroup.normalizer (W : Set (OTwoQuot M))) :
    T ≤ Subgroup.normalizer (starPre M W : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have htM := hTM ht
  have hmt : (QuotientGroup.mk ⟨t, htM⟩ : OTwoQuot M) ∈ Subgroup.normalizer (W : Set (OTwoQuot M)) :=
    hT (mem_imageOTwoQuot_iff.mpr ⟨t, htM, ht, rfl⟩)
  rw [mem_starPre, mem_starPre]
  constructor
  · rintro ⟨hxM, hxW⟩
    have hcM : t * x * t⁻¹ ∈ M := M.mul_mem (M.mul_mem htM hxM) (M.inv_mem htM)
    refine ⟨hcM, ?_⟩
    rw [mk_conj_eq htM hxM hcM]
    exact (Subgroup.mem_normalizer_iff.mp hmt _).mp hxW
  · rintro ⟨hcM, hcW⟩
    have hxM : x ∈ M := by
      have := M.mul_mem (M.mul_mem (M.inv_mem htM) hcM) htM
      simpa [mul_assoc] using this
    refine ⟨hxM, ?_⟩
    rw [mk_conj_eq htM hxM hcM] at hcW
    exact (Subgroup.mem_normalizer_iff.mp hmt _).mpr hcW

theorem oTwoUpper_eq_self_of_odd {B : Type*} [Group B] {X : Subgroup B}
    (h : ∀ x ∈ X, Odd (orderOf x)) : oTwoUpper X = X :=
  le_antisymm (oTwoUpper_le X) fun x hx => mem_oTwoUpper_of_odd hx (h x hx)

theorem exists_Abar (h : Data T Mc M) (c3 : Lemma15203Concl T Mc M)
    (hThree : Case1517Three M (V154 T Mc M) (mBar0 T Mc M))
    (e : ↥(mBar0 T Mc M) ≃* D33) (sh : OmShape (mBar0 T Mc M))
    (hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M)) :
    ∃ A₀ : Subgroup (MulAut (V154 T Mc M)), A₀ ≤ autOn (yOf152 T Mc M) (V154 T Mc M) ∧
      Nat.card A₀ = 3 ∧ (∀ t ∈ autOn T (V154 T Mc M), ∀ a ∈ A₀, t * a * t⁻¹ ∈ A₀) ∧
      (∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ A₀, r * a * r⁻¹ ≠ a) := by
  have hA : autOn M (V154 T Mc M) = mBar0 T Mc M := hThree.2.1
  have hTb : autOn T (V154 T Mc M) ≤ mBar0 T Mc M := hA ▸ Tb_le h
  have hRT : autOn (rcOf Mc M) (V154 T Mc M) ≤ autOn T (V154 T Mc M) := A4.autOn_mono h.rc_le_T
  have hT2 : IsPGroup 2 (autOn T (V154 T Mc M)) := (isSylowTwoOf_Tb h).2.1
  have hsqT : ∀ x ∈ autOn T (V154 T Mc M), x * x = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
    exact sh.two_elements x (hTb hx) ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcommT : ∀ x ∈ autOn T (V154 T Mc M), ∀ y ∈ autOn T (V154 T Mc M), x * y = y * x := by
    intro x hx y hy
    have hxy := hsqT (x * y) ((autOn T (V154 T Mc M)).mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsqT x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsqT y hy)
    calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy
      _ = y * x := by rw [mul_inv_rev, hx', hy']
  obtain ⟨r, hr, a, ha, hra⟩ := exists_nontrivial_action_of_comm_eq c3
  have hrT : r ∈ autOn T (V154 T Mc M) := hRT hr
  obtain ⟨α, hαE, hα3, hρα, hall⟩ := exists_invariant_line (mBar0 T Mc M) e (hTb hrT)
    (hsqT r hrT) ⟨a, by rw [← hYb]; exact ha, hra⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    apply hρα
    simp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  refine ⟨Subgroup.zpowers α, ?_, ?_, ?_, ⟨r, hr, α, Subgroup.mem_zpowers α, hρα⟩⟩
  · rw [Subgroup.zpowers_le, hYb]
    exact hαE
  · rw [Nat.card_zpowers, hord]
  · intro t ht x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    rcases hall t (hTb ht) (hsqT t ht) (hcommT t ht r hrT) with h1 | h1
    · rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers α) k
    · rw [h1, inv_zpow]
      exact (Subgroup.zpowers α).inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers α) k)

theorem exists_Y1_of_line (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205)
    (hexp : ∀ x ∈ Ys T Mc M, x ^ 3 = 1) {A₀ : Subgroup (MulAut (V154 T Mc M))}
    (hA₀Y : A₀ ≤ autOn (yOf152 T Mc M) (V154 T Mc M)) (hcard : Nat.card A₀ = 3)
    (hinvT : ∀ t ∈ autOn T (V154 T Mc M), ∀ a ∈ A₀, t * a * t⁻¹ ∈ A₀)
    (hact : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ A₀, r * a * r⁻¹ ≠ a)
    (hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1) :
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀cyc : IsCyclic ↥A₀ := isCyclic_of_prime_card hcard
  set Ks : Subgroup (OTwoQuot M) := Ys T Mc M ⊓ (piStar h).ker with hKs
  set Ws : Subgroup (OTwoQuot M) := Ys T Mc M ⊓ A₀.comap (piStar h) with hWs
  have hKW : Ks ≤ Ws := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    show piStar h u ∈ A₀
    rw [MonoidHom.mem_ker.mp hu.2]
    exact A₀.one_mem
  have hKcentral : ∀ k ∈ Ks, ∀ x ∈ Ys T Mc M, x * k = k * x := fun k hk x hx =>
    Data.K_central h k hk x (Data.Ys_le_Ls h hx)
  have hWY : Ws ≤ Ys T Mc M := fun u hu => hu.1
  have hWab : ∀ x ∈ Ws, ∀ y ∈ Ws, x * y = y * x := by
    let f : ↥Ws →* ↥A₀ :=
      MonoidHom.codRestrict ((piStar h).comp Ws.subtype) A₀ (fun u => u.2.2)
    have hf : f.ker ≤ Subgroup.center ↥Ws := by
      intro u hu
      rw [Subgroup.mem_center_iff]
      intro g
      have hu1 : piStar h (u : OTwoQuot M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
      have hmem : (u : OTwoQuot M) ∈ Ks := ⟨hWY u.2, hu1⟩
      exact Subtype.ext (hKcentral _ hmem (g : OTwoQuot M) (hWY g.2))
    intro a ha b hb
    have : IsMulCommutative ↥Ws := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hf
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥Ws) ⟨b, hb⟩)
  have hTsY : imageOTwoQuot M T ≤ Subgroup.normalizer (Ys T Mc M : Set (OTwoQuot M)) :=
    imageOTwoQuot_le_normalizer (T_le_normalizer_yOf T Mc M)
  have hTsK : imageOTwoQuot M T ≤ Subgroup.normalizer (Ks : Set (OTwoQuot M)) := by
    intro u hu
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hTsY hu, Subgroup.le_normalizer_of_normal hu⟩
  have hTsW : imageOTwoQuot M T ≤ Subgroup.normalizer (Ws : Set (OTwoQuot M)) := by
    intro u hu
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hTsY hu) w).mp hw.1, ?_⟩
    show piStar h (u * w * u⁻¹) ∈ A₀
    rw [map_mul, map_mul, map_inv]
    have hπu : piStar h u ∈ autOn T (V154 T Mc M) := by
      rw [← map_piStar_imageOTwoQuot h h.T_le]
      exact ⟨u, hu, rfl⟩
    exact hinvT _ hπu _ hw.2
  have hT2G : IsPGroup 2 T := (isSylowTwoOf_of_le151 h.qtfe.sylow h.T_le).2.1
  have hTs2 : IsPGroup 2 (imageOTwoQuot M T) := imageOTwoQuot_isPGroup h.T_le hT2G
  obtain ⟨W', -, hW'W, hTsW', hsup, hinf⟩ := B6.exists_isCompl_of_coprime_section (p := 3)
    (by norm_num) (K := Ws) (Φ := ⊥) (W := Ks) (T := imageOTwoQuot M T) bot_le hKW
    (fun x hx => by rw [hexp x (hWY hx)]; exact Subgroup.one_mem _)
    (by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hWab a ha b hb)
    hTsW (Subgroup.le_normalizer_of_normal) hTsK hTs2
  have hW'Ys : W' ≤ Ys T Mc M := hW'W.trans hWY
  have hW'odd : ∀ u ∈ W', Odd (orderOf u) := fun u hu =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (hexp u (hW'Ys hu)))
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Subgroup G, Y₀ = yOf152 T Mc M ⊓ starPre M W' := ⟨_, rfl⟩
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₀ := ⟨_, rfl⟩
  have hY₀Y : Y₀ ≤ yOf152 T Mc M := by rw [hY₀]; exact inf_le_left
  have hY₀M : Y₀ ≤ M := hY₀Y.trans h.yOf_le_M
  have hY₁Y₀ : Y₁ ≤ Y₀ := by rw [hY₁]; exact oTwoUpper_le _
  have hY₁Y : Y₁ ≤ yOf152 T Mc M := hY₁Y₀.trans hY₀Y
  have hY₁M : Y₁ ≤ M := hY₁Y.trans h.yOf_le_M
  have himg₀ : imageOTwoQuot M Y₀ = W' := by
    rw [hY₀, imageOTwoQuot_inf_starPre]
    exact inf_eq_right.mpr hW'Ys
  have himg₁ : imageOTwoQuot M Y₁ = W' := by
    rw [hY₁, imageOTwoQuot_oTwoUpper hY₀M, himg₀]
    exact oTwoUpper_eq_self_of_odd hW'odd
  have hTY₀ : T ≤ Subgroup.normalizer (Y₀ : Set G) := by
    rw [hY₀]
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨T_le_normalizer_yOf T Mc M ht, le_normalizer_starPre h.T_le hTsW' ht⟩
  have hTY₁ : T ≤ Subgroup.normalizer (Y₁ : Set G) := by
    rw [hY₁]
    exact hTY₀.trans (normalizer_le_normalizer_oTwoUpper _)
  have hRY₁ : rcOf Mc M ≤ Subgroup.normalizer (Y₁ : Set G) := h.rc_le_T.trans hTY₁
  have hK : imageOTwoQuot M Y₁ ⊓ (piStar h).ker = ⊥ := by
    rw [himg₁, eq_bot_iff]
    intro u hu
    have : u ∈ Ks ⊓ W' := ⟨⟨hW'Ys hu.1, hu.2⟩, hu.1⟩
    rw [hinf] at this
    exact this
  have hodd : ∀ u ∈ imageOTwoQuot M Y₁, Odd (orderOf u) := by
    rw [himg₁]
    exact hW'odd
  have hW'normK : W' ≤ Subgroup.normalizer (Ks : Set (OTwoQuot M)) := by
    intro w hw
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    have := hKcentral k hk w (hW'Ys hw)
    have h2 : w * k * w⁻¹ = k := by
      calc w * k * w⁻¹ = k * w * w⁻¹ := by rw [this]
        _ = k := by group
    rw [h2]
    exact hk
  have hautY₁ : autOn Y₁ (V154 T Mc M) = A₀ := by
    rw [← map_piStar_imageOTwoQuot h hY₁M, himg₁]
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact (hW'W hu).2
    · intro a₀ ha₀
      have hmem : a₀ ∈ (Ys T Mc M).map (piStar h) := by
        rw [h.map_Ys]
        exact hA₀Y ha₀
      obtain ⟨u, hu, rfl⟩ := hmem
      have huW : u ∈ Ws := ⟨hu, ha₀⟩
      rw [← hsup, sup_comm] at huW
      have hmul := Subgroup.coe_mul_of_left_le_normalizer_right W' Ks hW'normK
      have huW' : u ∈ ((W' ⊔ Ks : Subgroup (OTwoQuot M)) : Set (OTwoQuot M)) := huW
      rw [hmul] at huW'
      obtain ⟨w, hw, k, hk, rfl⟩ := Set.mem_mul.mp huW'
      refine ⟨w, hw, ?_⟩
      have hk1 : piStar h k = 1 := MonoidHom.mem_ker.mp hk.2
      rw [map_mul, hk1, mul_one]
  have hcardY₁ : Nat.card (autOn Y₁ (V154 T Mc M)) = 3 := by
    rw [hautY₁]
    exact hcard
  have hactY₁ : ∃ r ∈ autOn (rcOf Mc M) (V154 T Mc M), ∃ a ∈ autOn Y₁ (V154 T Mc M),
      r * a * r⁻¹ ≠ a := by
    rw [hautY₁]
    exact hact
  obtain ⟨e⟩ := quot_dihedral_of_star h hY₁M hRY₁ (p := 3) (by norm_num) hK hcardY₁ hRe hactY₁
  obtain ⟨d⟩ := S152N2.nonempty_d3_equiv_perm
  have hunique := isUniqueM_of_five h h5 hs hY₁M
    (not_le_Mc hRY₁ hodd (exists_nontrivial_action h hY₁M hactY₁))
  exact ⟨Y₁, isY1_of_star h hY₁Y hTY₁ (by rw [hY₁]; exact (A4.oTwoUpper_oTwoUpper Y₀).symm)
    (Or.inl ⟨e.trans d⟩) hK hodd hunique⟩

end S152Y

end CFSG.Quasithin
