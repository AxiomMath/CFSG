module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthB5False
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthFixedFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private lemma ct_j2_iota_zpowers_mem_span
    {G : Type} [Group G] {Bs : Subgroup G} {x : G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hx : x ∈ Bs) {b : ↥Bs}
    (hb : (b : G) ∈ Subgroup.zpowers x) :
    ι (Additive.ofMul b) ∈ Submodule.span (ZMod 3) {ι (Additive.ofMul ⟨x, hx⟩)} := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
  set w0 : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) with hw0
  have hb' : b = (⟨x, hx⟩ : ↥Bs) ^ n := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hn.symm
  have hw : ι (Additive.ofMul b) = n • w0 := by
    rw [hb', ofMul_zpow, map_zsmul, ← hw0]
  rw [hw, Submodule.mem_span_singleton]
  exact ⟨(n : ZMod 3), Int.cast_smul_eq_zsmul (ZMod 3) n w0⟩

private lemma ct_j2_mem_zpowers_of_iota_mem_span
    {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hx : x ∈ Bs) (hy : y ∈ Bs)
    (hmem : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) ∈
      Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))}) :
    x ∈ Subgroup.zpowers y := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by
    have : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = 2 := by decide
    exact this c
  rcases hcases with rfl | rfl | rfl
  · have h := congrArg ι.symm hc
    simp only [zero_smul, map_zero] at h
    have h1 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      simpa [ofMul_one] using h.symm
    have h1g : x = 1 := by simpa using congrArg Subtype.val h1
    rw [h1g]
    exact Subgroup.one_mem _
  · have h := congrArg ι.symm hc
    simp only [one_smul, AddEquiv.symm_apply_apply] at h
    have h1 : (⟨x, hx⟩ : ↥Bs) = ⟨y, hy⟩ := by
      apply Additive.ofMul.injective
      simpa using h.symm
    have h1g : x = y := by simpa using congrArg Subtype.val h1
    rw [h1g]
    exact Subgroup.mem_zpowers y
  · have h := congrArg ι.symm hc
    rw [two_smul] at h
    simp only [map_add, AddEquiv.symm_apply_apply] at h
    have h1 : (⟨x, hx⟩ : ↥Bs) = ⟨y, hy⟩ ^ 2 := by
      apply Additive.ofMul.injective
      rw [ofMul_pow, two_nsmul]
      exact h.symm
    have h1g : x = y ^ 2 := by
      simpa [Subgroup.coe_pow] using congrArg Subtype.val h1
    rw [h1g]
    exact Subgroup.npow_mem_zpowers y 2

private lemma ct_j2_closure_range_map
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) {κ : Type} (M : CoxeterMatrix κ) (W : Subgroup (MulAut ↥Bs))
    (e : M.Group ≃* ↥W) :
    Subgroup.closure (Set.range (fun i : κ =>
        ggLin (p := 3) ι ((e (M.simple i) : ↥W) : MulAut ↥Bs))) =
      W.map (ggLin (p := 3) ι) := by
  have hgen : W = Subgroup.closure (Set.range (fun i : κ => W.subtype (e (M.simple i)))) := by
    have h1 : Set.range (fun i : κ => W.subtype (e (M.simple i))) =
        W.subtype '' (Set.range (fun i : κ => (e (M.simple i) : ↥W))) := by
      ext y
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e (M.simple i), ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [h1, ← MonoidHom.map_closure W.subtype]
    have h2 : Subgroup.closure (Set.range (fun i : κ => (e (M.simple i) : ↥W))) = ⊤ := by
      have h3 : Set.range (fun i : κ => (e (M.simple i) : ↥W)) =
          (e : M.Group →* ↥W) '' Set.range M.simple := by
        ext y
        simp only [Set.mem_range, Set.mem_image]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      rw [h3, ← MonoidHom.map_closure,
        show Subgroup.closure (Set.range M.simple) = ⊤ from
          M.toCoxeterSystem.subgroup_closure_range_simple,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [hgen]
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨W.subtype (e (M.simple i)), ⟨i, rfl⟩, hi⟩
  · rintro ⟨z, ⟨j, hj⟩, hz⟩
    rw [← hj] at hz
    exact ⟨j, hz⟩

private lemma ct_j2_automizer_fixes
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {z : G} (hzBs : z ∈ Bs)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer X Bs) :
    φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
  have hzfix : z ∈ ggFixG Bs φ := mem_ggFixG_of_mem_ggAutomizer hzBs hXz hφ
  rw [ggFixG, Subgroup.mem_map] at hzfix
  obtain ⟨b, hb, hbval⟩ := hzfix
  have hbeq : b = ⟨z, hzBs⟩ := Subtype.ext hbval
  rw [← hbeq]
  exact mem_ggFix.mp hb

theorem ggOrthD4_rankFour_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hFix : GGSecFiveFixInput) (hd : Module.finrank (ZMod 3) V = 5)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hKfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hrank : GGWeylOfType 3 (CoxeterMatrix.B 4) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
      GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    False := by
  classical
  have : Finite ↥Bs := by infer_instance
  have : Finite V := Finite.of_injective (⇑ι.symm) ι.symm.injective
  have : FiniteDimensional (ZMod 3) V :=
    (Module.finite_iff_finite (R := ZMod 3) (M := V)).mpr inferInstance
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  obtain ⟨hp, habel, hxBs, -, -⟩ := (S.cfg.1.1).tableB_facts
  have hBBs : B ≤ Bs := S.cfg.1.1.2.1.1
  have hDB : D ≤ B := S.cfg.1.1.2.2.1.1
  have hx3 : x ^ 3 = 1 := habel.2 x hxBs
  have hx1 : x ≠ 1 := (S.cfg.1.1).1.2.2.2.2.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := S.cfg.1.1.tableB_facts.2.2.2.1
  have hyD : y ∈ D := hnb.2.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hDB hyD
  have hyBs : y ∈ Bs := hBBs hyB
  have hyne : y ≠ 1 := hnb.1.2.2.1
  have hy3 : y ^ 3 = 1 := hnb.1.1.1.2 y hyB
  have hKz : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hxzy : x ∉ Subgroup.zpowers y := by
    intro hxzy
    have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hyne
    have hzxy : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hxzy
    have hzyx : Subgroup.zpowers x = Subgroup.zpowers y := by
      apply Subgroup.eq_of_le_of_card_ge hzxy
      rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy]
    have hcent : Subgroup.centralizer ({y} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x) := by
      rw [← Subgroup.centralizer_closure ({y} : Set G), ← Subgroup.zpowers_eq_closure y, hzyx]
    exact hnb.2.2.2 (by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcent ▸ hKz)]
      exact bot_le)
  have hxy' : ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∉
      Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
    intro hmem
    exact hxzy (ct_j2_mem_zpowers_of_iota_mem_span ι hxBs hyBs hmem)
  let W : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let AL : Subgroup (V ≃ₗ[ZMod 3] V) := (ggAutomizer L Bs).map (ggLin (p := 3) ι)
  let AK : Subgroup (V ≃ₗ[ZMod 3] V) := (ggAutomizer K Bs).map (ggLin (p := 3) ι)
  have hFixL' : ∀ v : V, (∀ a ∈ AL, a v = v) →
      v ∈ Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))} := by
    intro v hv
    set b : ↥Bs := Additive.toMul (ι.symm v) with hbdef
    have hbv : ι (Additive.ofMul b) = v := by
      rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hfix : ∀ φ ∈ ggAutomizer L Bs, φ b = b := by
      intro φ hφ
      rw [ggLin_fix_iff (p := 3) ι φ b, hbv]
      exact hv (ggLin (p := 3) ι φ) (Subgroup.mem_map_of_mem (ggLin (p := 3) ι) hφ)
    have hb : (b : G) ∈ Subgroup.zpowers x :=
      hFix G 3 B Bs x L D J 𝒦 S.cfg S.split b hfix
    rw [← hbv]
    exact ct_j2_iota_zpowers_mem_span ι hxBs hb
  have hFixK' : ∀ v : V, (∀ a ∈ AK, a v = v) →
      v ∈ Submodule.span (ZMod 3) {ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} := by
    intro v hv
    set b : ↥Bs := Additive.toMul (ι.symm v) with hbdef
    have hbv : ι (Additive.ofMul b) = v := by
      rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hfix : ∀ φ ∈ ggAutomizer K Bs, φ b = b := by
      intro φ hφ
      rw [ggLin_fix_iff (p := 3) ι φ b, hbv]
      exact hv (ggLin (p := 3) ι φ) (Subgroup.mem_map_of_mem (ggLin (p := 3) ι) hφ)
    have hb : (b : G) ∈ Subgroup.zpowers y := hKfix b hfix
    rw [← hbv]
    exact ct_j2_iota_zpowers_mem_span ι hyBs hb
  have key : ∀ (M : CoxeterMatrix (Fin 4)) (e : M.Group ≃* ↥W)
      (he : ∀ i, GGIsReflection 3 ((e (M.simple i) : ↥W) : MulAut ↥Bs)), False := by
    intro M e he
    let r : Fin 4 → (V ≃ₗ[ZMod 3] V) :=
      fun i => ggLin (p := 3) ι ((e (M.simple i) : ↥W) : MulAut ↥Bs)
    have hclosure : Subgroup.closure (Set.range r) = W.map (ggLin (p := 3) ι) :=
      ct_j2_closure_range_map ι M W e
    have hr : ∀ i, Module.finrank (ZMod 3)
        (LinearMap.range ((r i).toLinearMap - LinearMap.id)) = 1 := by
      intro i
      exact ((ggIsReflection_iff_ggLinRefl (p := 3) hp2 ι
        ((e (M.simple i) : ↥W) : MulAut ↥Bs)).mp (he i)).2
    have hKW : AK ≤ Subgroup.closure (Set.range r) := by
      rw [hclosure]
      exact Subgroup.map_mono (le_sup_right : ggAutomizer K Bs ≤ W)
    have hLW : AL ≤ Subgroup.closure (Set.range r) := by
      rw [hclosure]
      exact Subgroup.map_mono (le_sup_left : ggAutomizer L Bs ≤ W)
    exact ggOrth_rankFour_false hd r hr hKW hLW hxy' hFixL' hFixK'
  rcases hrank with h | h
  · obtain ⟨e, he⟩ := h
    exact key (CoxeterMatrix.B 4) e he
  · obtain ⟨e, he⟩ := h
    exact key CoxeterMatrix.F₄ e he

theorem ggOrthD4_b5_false
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hd : Module.finrank (ZMod 3) V = 5)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hKinf : ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J)
    (hD : GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs))
    (hKB : GGWeylOfType 3 (CoxeterMatrix.B 4) (ggAutomizer K Bs))
    (hstar : ∀ φ : ↥(ggAutomizer K Bs), GGIsReflection 3 (φ : MulAut ↥Bs) →
      Nat.card {ψ : ↥(ggAutomizer K Bs) // IsConj φ ψ} = 4 →
      ∀ hx : x ∈ Bs, (φ : MulAut ↥Bs) ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    (hB5 : GGWeylOfType 3 (CoxeterMatrix.B 5) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    False := by
  classical
  have : Finite ↥Bs := by infer_instance
  have : Finite V := Finite.of_injective (⇑ι.symm) ι.symm.injective
  have : FiniteDimensional (ZMod 3) V :=
    (Module.finite_iff_finite (R := ZMod 3) (M := V)).mpr inferInstance
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  obtain ⟨hp, habel, hxBs, -, -⟩ := (S.cfg.1.1).tableB_facts
  have hBBs : B ≤ Bs := S.cfg.1.1.2.1.1
  have hDB : D ≤ B := S.cfg.1.1.2.2.1.1
  have hx3 : x ^ 3 = 1 := habel.2 x hxBs
  have hx1 : x ≠ 1 := (S.cfg.1.1).1.2.2.2.2.2.2.1.2.2.1
  have hLxcent : L ≤ Subgroup.centralizer ({x} : Set G) := S.cfg.1.1.tableB_facts.2.2.2.1
  have hyD : y ∈ D := hnb.2.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hDB hyD
  have hyBs : y ∈ Bs := hBBs hyB
  have hyne : y ≠ 1 := hnb.1.2.2.1
  have hy3 : y ^ 3 = 1 := hnb.1.1.1.2 y hyB
  have hKz : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hxzy : x ∉ Subgroup.zpowers y := by
    intro hxzy
    have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hyne
    have hzxy : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hxzy
    have hzyx : Subgroup.zpowers x = Subgroup.zpowers y := by
      apply Subgroup.eq_of_le_of_card_ge hzxy
      rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy]
    have hcent : Subgroup.centralizer ({y} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x) := by
      rw [← Subgroup.centralizer_closure ({y} : Set G), ← Subgroup.zpowers_eq_closure y, hzyx]
    exact hnb.2.2.2 (by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcent ▸ hKz)]
      exact bot_le)
  let W : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let AL : Subgroup (V ≃ₗ[ZMod 3] V) := (ggAutomizer L Bs).map (ggLin (p := 3) ι)
  let AK : Subgroup (V ≃ₗ[ZMod 3] V) := (ggAutomizer K Bs).map (ggLin (p := 3) ι)
  let xV : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  let yV : V := ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
  have hW_le : W ≤ ggAInf 3 B Bs x L D J := sup_le le_sup_left hKinf
  have hxy : xV ∉ Submodule.span (ZMod 3) {yV} := by
    intro hmem
    exact hxzy (ct_j2_mem_zpowers_of_iota_mem_span ι hxBs hyBs (by simpa [xV, yV] using hmem))
  have hx0 : xV ≠ 0 := by
    intro h
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := ι.injective (by simpa [xV] using h)
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hx1 (by simpa using congrArg Subtype.val h2)
  have hy0 : yV ≠ 0 := by
    intro h
    have h1 : Additive.ofMul (⟨y, hyBs⟩ : ↥Bs) = 0 := ι.injective (by simpa [yV] using h)
    have h2 : (⟨y, hyBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hyne (by simpa using congrArg Subtype.val h2)
  have hKy : ∀ a ∈ AK, a yV = yV := by
    rintro a ⟨φ, hφ, rfl⟩
    change ggLin (p := 3) ι φ (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = _
    rw [ggLin_apply_ofMul, ct_j2_automizer_fixes hyBs hKz hφ]
  have hLxV : ∀ a ∈ AL, a xV = xV := by
    rintro a ⟨φ, hφ, rfl⟩
    change ggLin (p := 3) ι φ (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = _
    rw [ggLin_apply_ofMul, ct_j2_automizer_fixes hxBs hLxcent hφ]
  have hB5card : Nat.card (CoxeterMatrix.B 5).Group = 3840 := by
    refine le_antisymm (card_coxeterB_le 5) ?_
    have h := CFSG.StandardType.SpFrame.card_coxeterB_ge 5 (by norm_num)
    norm_num at h ⊢
    exact h
  have hB4card : Nat.card (CoxeterMatrix.B 4).Group = 384 := by
    refine le_antisymm (card_coxeterB_le 4) ?_
    have h := CFSG.StandardType.SpFrame.card_coxeterB_ge 4 (by norm_num)
    norm_num at h ⊢
    exact h
  have hDcard : Nat.card (ggCoxeterMatrixD 4).Group = 192 := by
    rw [card_coxeterD_eq 4 le_rfl]
    norm_num [Nat.factorial]
  have hKcard : Nat.card ↥AK = 384 := by
    change Nat.card ↥((ggAutomizer K Bs).map (ggLin (p := 3) ι)) = 384
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer K Bs)
      (ggLin (p := 3) ι) (ggLin_injective (p := 3) ι)).toEquiv]
    obtain ⟨eK, -⟩ := hKB
    rw [← Nat.card_congr eK.toEquiv]
    exact hB4card
  have hLcard : Nat.card ↥AL = 192 := by
    change Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := 3) ι)) = 192
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer L Bs)
      (ggLin (p := 3) ι) (ggLin_injective (p := 3) ι)).toEquiv]
    obtain ⟨eL, -⟩ := hD
    rw [← Nat.card_congr eL.toEquiv]
    exact hDcard
  obtain ⟨e, he⟩ := hB5
  let r : Fin 5 → (V ≃ₗ[ZMod 3] V) :=
    fun i => ggLin (p := 3) ι ((e ((CoxeterMatrix.B 5).simple i) : ↥W) : MulAut ↥Bs)
  have hclosure : Subgroup.closure (Set.range r) = W.map (ggLin (p := 3) ι) :=
    ct_j2_closure_range_map ι (CoxeterMatrix.B 5) W e
  have hcard : Nat.card ↥(Subgroup.closure (Set.range r)) = 3840 := by
    rw [hclosure, ← Nat.card_congr (Subgroup.equivMapOfInjective W
      (ggLin (p := 3) ι) (ggLin_injective (p := 3) ι)).toEquiv]
    rw [← Nat.card_congr e.toEquiv]
    exact hB5card
  have hKW : AK ≤ Subgroup.closure (Set.range r) := by
    rw [hclosure]
    exact Subgroup.map_mono (le_sup_right : ggAutomizer K Bs ≤ W)
  have hLW : AL ≤ Subgroup.closure (Set.range r) := by
    rw [hclosure]
    exact Subgroup.map_mono (le_sup_left : ggAutomizer L Bs ≤ W)
  have hrefl : ∀ i, ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c (r i) := by
    intro i
    have hiso : r i ∈ QuadraticMap.orthogonalGroup Q := by
      refine QuadraticMap.mem_orthogonalGroup_iff.mpr ?_
      exact (S.orth (r i)).mp ⟨((e ((CoxeterMatrix.B 5).simple i) : ↥W) : MulAut ↥Bs),
        hW_le (e ((CoxeterMatrix.B 5).simple i)).2, rfl⟩
    have hlin : GGLinRefl (r i) :=
      (ggIsReflection_iff_ggLinRefl (p := 3) hp2 ι
        ((e ((CoxeterMatrix.B 5).simple i) : ↥W) : MulAut ↥Bs)).mp (he i)
    exact (linRefl_iff_orthRefl S.nondeg hiso).mp hlin
  have hord : ∀ i j, i ≠ j → orderOf (r i * r j) = (CoxeterMatrix.B 5).M i j := by
    intro i j hij
    let Φ : (CoxeterMatrix.B 5).Group →* (V ≃ₗ[ZMod 3] V) :=
      (ggLin (p := 3) ι).comp (W.subtype.comp (e : (CoxeterMatrix.B 5).Group →* ↥W))
    have hΦinj : Function.Injective Φ :=
      (ggLin_injective (p := 3) ι).comp ((Subgroup.subtype_injective W).comp e.injective)
    have hprod : r i * r j =
        Φ ((CoxeterMatrix.B 5).simple i * (CoxeterMatrix.B 5).simple j) := by
      simp only [Φ, r, MonoidHom.comp_apply, map_mul]
      rfl
    rw [hprod, orderOf_injective Φ hΦinj]
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterMatrix.B 5).toCoxeterSystem.orderOf_simple_mul_simple i j
  have hstar' : ∀ φ : ↥AK, ((φ : V ≃ₗ[ZMod 3] V) * (φ : V ≃ₗ[ZMod 3] V) = 1 ∧
      Module.finrank (ZMod 3) (LinearMap.range
        ((φ : V ≃ₗ[ZMod 3] V).toLinearMap - LinearMap.id)) = 1) →
      Nat.card {ψ : ↥AK // IsConj φ ψ} = 4 → (φ : V ≃ₗ[ZMod 3] V) xV ≠ xV := by
    intro φ hrefl hclass
    let eK : ↥(ggAutomizer K Bs) ≃* ↥AK :=
      Subgroup.equivMapOfInjective (ggAutomizer K Bs) (ggLin (p := 3) ι)
        (ggLin_injective (p := 3) ι)
    let φ₀ : ↥(ggAutomizer K Bs) := eK.symm φ
    have hgg : ggLin (p := 3) ι (φ₀ : MulAut ↥Bs) = (φ : V ≃ₗ[ZMod 3] V) := by
      change (eK φ₀ : V ≃ₗ[ZMod 3] V) = (φ : V ≃ₗ[ZMod 3] V)
      exact congrArg (fun x : ↥AK => (x : V ≃ₗ[ZMod 3] V))
        (show eK φ₀ = φ from
          Equiv.apply_symm_apply (eK : ↥(ggAutomizer K Bs) ≃ ↥AK) φ)
    have hrefl₀ : GGIsReflection 3 (φ₀ : MulAut ↥Bs) := by
      rw [ggIsReflection_iff_ggLinRefl (p := 3) hp2 ι (φ₀ : MulAut ↥Bs), hgg]
      exact hrefl
    have hisconj : ∀ a b : ↥(ggAutomizer K Bs), IsConj (eK a) (eK b) ↔ IsConj a b := by
      intro a b
      refine ⟨fun h => ?_, fun h => MonoidHom.map_isConj (eK : ↥(ggAutomizer K Bs) →* ↥AK) h⟩
      have h' := MonoidHom.map_isConj (eK.symm : ↥AK →* ↥(ggAutomizer K Bs)) h
      simpa using h'
    have hclass₀ : Nat.card {ψ : ↥(ggAutomizer K Bs) // IsConj φ₀ ψ} = 4 := by
      rw [← hclass]
      refine Nat.card_congr (Equiv.subtypeEquiv eK.toEquiv (fun ψ => ?_))
      have h := hisconj φ₀ ψ
      rw [show eK φ₀ = φ from
        Equiv.apply_symm_apply (eK : ↥(ggAutomizer K Bs) ≃ ↥AK) φ] at h
      exact h.symm
    intro hfix
    exact hstar φ₀ hrefl₀ hclass₀ hxBs
      ((ggLin_fix_iff (p := 3) ι (φ₀ : MulAut ↥Bs) ⟨x, hxBs⟩).mpr (by rw [hgg]; exact hfix))
  exact ggOrthB5_false hd r hrefl hord hcard hKW hLW hKcard hLcard hx0 hy0 hxy hKy hLxV hstar'

end CFSG.StandardType.OrthF3

end
