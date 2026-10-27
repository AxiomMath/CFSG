module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFivePrime

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Five

section Mod

variable {G : Type*} [Group G]

theorem exists_quotConjAut {U Z : Subgroup G} [(Z.subgroupOf U).Normal] {x : G}
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) :
    ∃ θ : (↥U ⧸ Z.subgroupOf U) ≃* (↥U ⧸ Z.subgroupOf U), ∀ u : ↥U,
      θ (QuotientGroup.mk u) = QuotientGroup.mk (conjAut U x hxU u) := by
  have he : (Z.subgroupOf U).map (conjAut U x hxU).toMonoidHom = Z.subgroupOf U := by
    ext u
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hxZ _).mp hw
    · intro hu
      refine ⟨(conjAut U x hxU).symm u, ?_, by simp⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hxZ
        (((conjAut U x hxU).symm u : ↥U) : G)).mpr
      refine h1 ?_
      have : x * (((conjAut U x hxU).symm u : ↥U) : G) * x⁻¹ = (u : G) := by
        have := congrArg Subtype.val ((conjAut U x hxU).apply_symm_apply u)
        exact this
      rw [this]
      exact hu
  refine ⟨QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) (conjAut U x hxU) he,
    fun u => rfl⟩

theorem exists_vecFunMod {K K₁ U Z : Subgroup G} [(Z.subgroupOf U).Normal] {v : G}
    (hU : ∀ k ∈ K, k * v * k⁻¹ ∈ U) (hZK : K ≤ Subgroup.normalizer (Z : Set G))
    (hK₁ : ∀ k ∈ K₁, v⁻¹ * (k * v * k⁻¹) ∈ Z) :
    ∃ f : Cosets K K₁ → ↥U ⧸ Z.subgroupOf U, ∀ k : ↥K,
      f (QuotientGroup.mk k) = QuotientGroup.mk ⟨k * v * k⁻¹, hU k k.2⟩ := by
  refine ⟨Quotient.lift (fun k : ↥K => (QuotientGroup.mk ⟨k * v * k⁻¹, hU k k.2⟩ :
      ↥U ⧸ Z.subgroupOf U)) (fun x y hxy => ?_), fun k => rfl⟩
  have h' := QuotientGroup.leftRel_apply.mp hxy
  rw [Subgroup.mem_subgroupOf] at h'
  have h1 := hK₁ _ h'
  change (QuotientGroup.mk _ : ↥U ⧸ Z.subgroupOf U) = QuotientGroup.mk _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h2 := (Subgroup.mem_normalizer_iff.mp (hZK x.2) _).mp h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv] at h2 ⊢
  convert h2 using 1
  group

end Mod

section Main

variable {G : Type*} [Group G] [Finite G]

theorem five_conjugates_mod {V K N T R A U : Subgroup G} (D : FiveData V K N T R A U)
    {Z : Subgroup G} (hZK : K ≤ Subgroup.normalizer (Z : Set G))
    (hZA : A ≤ Subgroup.normalizer (Z : Set G)) {v : G} (hvV : v ∈ V)
    (hK₁ : ∀ k ∈ K ⊓ Subgroup.normalizer (V : Set G), v⁻¹ * (k * v * k⁻¹) ∈ Z)
    (hA : ∀ a ∈ A, v⁻¹ * (a * v * a⁻¹) ∈ Z) :
    ∀ k ∈ K, v⁻¹ * (k * v * k⁻¹) ∈ Z := by
  classical
  set K₁ : Subgroup G := K ⊓ Subgroup.normalizer (V : Set G) with hK₁def
  have S : FiveSetup K K₁ N := D.setup
  haveI : Fintype (Cosets K K₁) := Fintype.ofFinite _
  have hcard : Fintype.card (Cosets K K₁) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.card_cosets
  letI : CommGroup ↥U := { (inferInstance : Group ↥U) with
    mul_comm := fun x y => Subtype.ext (D.u_comm x x.2 y y.2) }
  haveI : (Z.subgroupOf U).Normal := inferInstance
  have hU : ∀ k ∈ K, k * v * k⁻¹ ∈ U := fun k hk => D.u_gen k hk v hvV
  obtain ⟨f, hf⟩ := exists_vecFunMod (K₁ := K₁) (U := U) (Z := Z) hU hZK hK₁
  have hW2 : ∀ w : ↥U ⧸ Z.subgroupOf U, w * w = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H u =>
      have : u * u = 1 := Subtype.ext (D.u_sq u u.2)
      rw [← QuotientGroup.mk_mul, this]
      rfl
  set ω₁ : Cosets K K₁ := QuotientGroup.mk 1 with hω₁
  have htrans : ∀ ω₀ : Cosets K K₁,
      ∃ (φ : (↥U ⧸ Z.subgroupOf U) ≃* (↥U ⧸ Z.subgroupOf U))
        (π : Equiv.Perm (Cosets K K₁)), π ω₁ = ω₀ ∧ ∀ ω, f (π ω) = φ (f ω) := by
    intro ω₀
    induction ω₀ using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨φ, hφ⟩ := exists_quotConjAut (Z := Z) (D.u_normK g.2) (hZK g.2)
      refine ⟨φ, MulAction.toPerm g, ?_, ?_⟩
      · change (QuotientGroup.mk (g * 1) : Cosets K K₁) = QuotientGroup.mk g
        simp
      · intro ω
        induction ω using QuotientGroup.induction_on with
        | H k =>
          change f (QuotientGroup.mk (g * k)) = φ (f (QuotientGroup.mk k))
          rw [hf, hf, hφ]
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv, Subtype.coe_mk,
            coe_conjAut]
          convert Z.one_mem using 1
          group
  obtain ⟨a, haA, ha1, b, hbA, hb1, hab⟩ := exists_two_ne_one D.a_card
  have haK := D.a_normK haA
  have hbK := D.a_normK hbA
  have haK₁ := mem_normalizer_inf_normalizer haK (D.a_normV haA)
  have hbK₁ := mem_normalizer_inf_normalizer hbK (D.a_normV hbA)
  have habA : a * b ∈ A := A.mul_mem haA hbA
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    calc a = a * (b * b) := by rw [D.a_sq b hbA, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have habK := D.a_normK habA
  have habK₁ := mem_normalizer_inf_normalizer habK (D.a_normV habA)
  have hmul := conjPerm_mul (K := K) (K₁ := K₁) a b haK haK₁ hbK hbK₁ habK habK₁
  have hcomm : conjPerm K K₁ a haK haK₁ * conjPerm K K₁ b hbK hbK₁ =
      conjPerm K K₁ b hbK hbK₁ * conjPerm K K₁ a haK haK₁ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk _
      congr 1
      ext
      change a * (b * (g : G) * b⁻¹) * a⁻¹ = b * (a * (g : G) * a⁻¹) * b⁻¹
      have hba : b * a = a * b := (D.a_comm b hbA a haA)
      calc a * (b * (g : G) * b⁻¹) * a⁻¹ = (a * b) * (g : G) * (a * b)⁻¹ := by group
        _ = (b * a) * (g : G) * (b * a)⁻¹ := by rw [hba]
        _ = b * (a * (g : G) * a⁻¹) * b⁻¹ := by group
  have hsq : conjPerm K K₁ a haK haK₁ * conjPerm K K₁ a haK haK₁ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk g
      congr 1
      ext
      change a * (a * (g : G) * a⁻¹) * a⁻¹ = g
      calc a * (a * (g : G) * a⁻¹) * a⁻¹ = (a * a) * (g : G) * (a * a)⁻¹ := by group
        _ = g := by rw [D.a_sq a haA]; group
  have hfix1 : ∀ (c : G) (hcK : c ∈ Subgroup.normalizer (K : Set G))
      (hcK₁ : c ∈ Subgroup.normalizer (K₁ : Set G)), conjPerm K K₁ c hcK hcK₁ ω₁ = ω₁ := by
    intro c hcK hcK₁
    change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk 1
    congr 1
    ext
    change c * (1 : G) * c⁻¹ = 1
    group
  have hua : ∀ ω, conjPerm K K₁ a haK haK₁ ω = ω → ω = ω₁ := fun ω hω =>
    D.unique_fixed haA ha1 ω hω
  have hub : ∀ ω, conjPerm K K₁ b hbK hbK₁ ω = ω → ω = ω₁ := fun ω hω =>
    D.unique_fixed hbA hb1 ω hω
  have huab : ∀ ω, (conjPerm K K₁ a haK haK₁ * conjPerm K K₁ b hbK hbK₁) ω = ω → ω = ω₁ :=
    fun ω hω => D.unique_fixed habA hab1 ω (by rw [hmul]; exact hω)
  obtain ⟨θa, hθa⟩ := exists_quotConjAut (Z := Z) (D.u_normA haA) (hZA haA)
  obtain ⟨θb, hθb⟩ := exists_quotConjAut (Z := Z) (D.u_normA hbA) (hZA hbA)
  have hfa : ∀ ω, f (conjPerm K K₁ a haK haK₁ ω) = θa (f ω) := by
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H k =>
      rw [conjPerm_mk, hf, hf, hθa]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hk' : a * (k : G) * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haK k).1 k.2
      have h2 := (Subgroup.mem_normalizer_iff.mp (hZK hk') (v⁻¹ * (a * v * a⁻¹))).mp
        (hA a haA)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv, Subtype.coe_mk,
        coe_conjAut] at h2 ⊢
      convert h2 using 1
      group
  have hfb : ∀ ω, f (conjPerm K K₁ b hbK hbK₁ ω) = θb (f ω) := by
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H k =>
      rw [conjPerm_mk, hf, hf, hθb]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hk' : b * (k : G) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbK k).1 k.2
      have h2 := (Subgroup.mem_normalizer_iff.mp (hZK hk') (v⁻¹ * (b * v * b⁻¹))).mp
        (hA b hbA)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv, Subtype.coe_mk,
        coe_conjAut] at h2 ⊢
      convert h2 using 1
      group
  have hfixed : ∀ ω, θb (f ω * θa (f ω)) = f ω * θa (f ω) := by
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H k =>
      set y : ↥U := ⟨k * v * k⁻¹, hU k k.2⟩ with hy
      set y' : ↥U := conjAut U a (D.u_normA haA) y with hy'
      set c : ↥U := y * y' with hc
      have haca : a * (c : G) * a⁻¹ = (c : G) := by
        have ha2 := D.a_sq a haA
        have hcy : (c : G) = (y : G) * (y' : G) := rfl
        have hy'v : (y' : G) = a * (y : G) * a⁻¹ := rfl
        rw [hcy, hy'v]
        calc a * ((y : G) * (a * (y : G) * a⁻¹)) * a⁻¹
            = (a * (y : G) * a⁻¹) * ((a * a) * (y : G) * (a * a)⁻¹) := by group
          _ = (a * (y : G) * a⁻¹) * (y : G) := by rw [ha2]; group
          _ = (y : G) * (a * (y : G) * a⁻¹) := by
                have hcomm := D.u_comm y y.2 y' y'.2
                rw [hy'v] at hcomm
                exact hcomm.symm
      have hc_centa : (c : G) ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        calc a * (c : G) = (a * (c : G) * a⁻¹) * a := by group
          _ = (c : G) * a := by rw [haca]
      have hcentA : (c : G) ∈ U ⊓ Subgroup.centralizer (A : Set G) := by
        rw [D.u_cent a haA ha1]
        exact Subgroup.mem_inf.mpr ⟨c.2, hc_centa⟩
      have hbc : b * (c : G) = (c : G) * b :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcentA).2 b hbA
      rw [hf k, hθa y, ← QuotientGroup.mk_mul, hθb c]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hbcc : b * (c : G) * b⁻¹ = (c : G) := by
        calc b * (c : G) * b⁻¹ = (c : G) * b * b⁻¹ := by rw [hbc]
          _ = (c : G) := by group
      change (b * (c : G) * b⁻¹)⁻¹ * (c : G) ∈ Z
      rw [hbcc]
      simpa using Z.one_mem
  have key := five_point_const' (Ω := Cosets K K₁) (W := ↥U ⧸ Z.subgroupOf U) hcard hW2 f
    ω₁ htrans (conjPerm K K₁ a haK haK₁) (conjPerm K K₁ b hbK hbK₁) θa θb hfa hfb hsq hcomm
    (hfix1 a haK haK₁) (hfix1 b hbK hbK₁) hua hub huab hfixed
  intro k hk
  have h1 := key (QuotientGroup.mk ⟨k, hk⟩)
  rw [hf, hf] at h1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv, Subtype.coe_mk] at h1
  have h2 : ((k * v * k⁻¹)⁻¹ * (1 * v * 1⁻¹))⁻¹ ∈ Z := Z.inv_mem h1
  have h3 : ((k * v * k⁻¹)⁻¹ * (1 * v * 1⁻¹))⁻¹ = v⁻¹ * (k * v * k⁻¹) := by group
  rwa [h3] at h2

end Main

end CFSG.LocalAnalysis.WeakClosure81.Five

end
