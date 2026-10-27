module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Pre
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

namespace SmD4Five

section Groups

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_or_inverts {R : Subgroup G} {p : ℕ} (hp : p.Prime) (hR : Nat.card R = p)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) {a : G} (ha : a * a = 1)
    (hnorm : ∀ x ∈ R, a * x * a⁻¹ ∈ R) :
    (∀ x ∈ R, a * x * a⁻¹ = x) ∨ (∀ x ∈ R, a * x * a⁻¹ = x⁻¹) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hC : Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G)) ∣ p := by
    rw [← hR]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hC with h1 | hp'
  · right
    have hbot : R ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := Subgroup.card_eq_one.1 h1
    intro x hx
    have hy : a * x * a⁻¹ ∈ R := hnorm x hx
    have hu : x * (a * x * a⁻¹) ∈ R ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine ⟨R.mul_mem hx hy, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      set y := a * x * a⁻¹ with hydef
      have hyx : y * x = x * y := hcomm y hy x hx
      have e1 : a * x = y * a := by rw [hydef]; group
      have e2 : a * y = x * a := by
        rw [hydef, hai, ← mul_assoc, ← mul_assoc, ha, one_mul]
      calc a * (x * y) = (a * x) * y := (mul_assoc a x y).symm
        _ = (y * a) * y := by rw [e1]
        _ = y * (a * y) := mul_assoc y a y
        _ = y * (x * a) := by rw [e2]
        _ = (y * x) * a := (mul_assoc y x a).symm
        _ = (x * y) * a := by rw [hyx]
    rw [hbot, Subgroup.mem_bot] at hu
    exact eq_inv_of_mul_eq_one_right hu
  · left
    have heq : R ⊓ Subgroup.centralizer ({a} : Set G) = R :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hR])
    intro x hx
    have hx' : x ∈ R ⊓ Subgroup.centralizer ({a} : Set G) := by rw [heq]; exact hx
    have := Subgroup.mem_centralizer_iff.1 hx'.2 a rfl
    rw [mul_inv_eq_iff_eq_mul]
    exact this

end Groups

section Linear

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem five_inv_subspace (hV : Module.finrank (ZMod 2) V = 4) {c : V ≃ₗ[ZMod 2] V} (hc5 : c ^ 5 = 1)
    (hc0 : ∀ v, c v = v → v = 0) (U : Submodule (ZMod 2) V) (hU : ∀ u ∈ U, c u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hdvd := cyclic_dvd_two_pow Nat.prime_five c hc5 U hU (fun t _ ht => hc0 t ht)
  have hle : Module.finrank (ZMod 2) U ≤ 4 := hV ▸ Submodule.finrank_le U
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  generalize hk : Module.finrank (ZMod 2) U = k at hdvd hle
  interval_cases k
  · exact Or.inl (Submodule.finrank_eq_zero.1 hk)
  · norm_num at hdvd
  · norm_num at hdvd
  · norm_num at hdvd
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (hk.trans hV.symm))

theorem five_free (hV : Module.finrank (ZMod 2) V = 4) {c : V ≃ₗ[ZMod 2] V} (hc5 : c ^ 5 = 1)
    (hc0 : ∀ v, c v = v → v = 0) {z : V ≃ₗ[ZMod 2] V} (hz : z * c = c * z) (hz1 : z ≠ 1) :
    ∀ v, z v = v → v = 0 := by
  have hU : ∀ u ∈ fixSp V z ⊤, c u ∈ fixSp V z ⊤ := by
    intro u hu
    rw [CntLin.mem_fixSp] at hu ⊢
    refine ⟨trivial, ?_⟩
    have := DFunLike.congr_fun hz u
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    rw [this, hu.2]
  rcases five_inv_subspace hV hc5 hc0 _ hU with h | h
  · intro v hv
    have : v ∈ fixSp V z ⊤ := CntLin.mem_fixSp.2 ⟨trivial, hv⟩
    rw [h] at this
    simpa using this
  · exfalso
    apply hz1
    refine LinearEquiv.ext fun u => ?_
    have : u ∈ fixSp V z ⊤ := by rw [h]; trivial
    exact (CntLin.mem_fixSp.1 this).2

theorem two_le_finrank_fixSp (hV : Module.finrank (ZMod 2) V = 4) {a : V ≃ₗ[ZMod 2] V}
    (ha : a * a = 1) : 2 ≤ Module.finrank (ZMod 2) ↥(fixSp V a ⊤) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set f : V →ₗ[ZMod 2] V := (a : V →ₗ[ZMod 2] V) - 1 with hf
  have hff : ∀ v, f (f v) = 0 := by
    intro v
    have h1 : a (a v) = v := by rw [← LinearEquiv.mul_apply, ha]; rfl
    show a (a v - v) - (a v - v) = 0
    rw [map_sub, h1]
    calc v - a v - (a v - v) = (v + v) - (a v + a v) := by abel
      _ = 0 := by rw [CntLin.zmod2_add_self, CntLin.zmod2_add_self, sub_zero]
  have hrange : LinearMap.range f ≤ LinearMap.ker f :=
    LinearMap.range_le_ker_iff.2 (LinearMap.ext hff)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hmono := Submodule.finrank_mono hrange
  have hfix : fixSp V a ⊤ = LinearMap.ker f := top_inf_eq _
  rw [hfix]
  omega

theorem five_invol (hV : Module.finrank (ZMod 2) V = 4) {c : V ≃ₗ[ZMod 2] V} (hc5 : c ^ 5 = 1)
    (hc0 : ∀ v, c v = v → v = 0) {b : V ≃ₗ[ZMod 2] V} (hb : b * b = 1) (hbc : b * c = c * b) :
    b = 1 := by
  by_contra hb1
  have hfree := five_free hV hc5 hc0 hbc hb1
  have h2 := two_le_finrank_fixSp hV hb
  have hpos : 0 < Module.finrank (ZMod 2) ↥(fixSp V b ⊤) := by omega
  obtain ⟨⟨v, hv⟩, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  exact hvne (Subtype.ext (hfree v (CntLin.mem_fixSp.1 hv).2))

omit [Module (ZMod 2) V] in
theorem card_nonzero_of_card_sixteen (hV : Nat.card V = 16) : Nat.card {v : V // v ≠ 0} = 15 := by
  have h1 : Nat.card {v : V // v ≠ 0} = (({0} : Set V)ᶜ).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h1, Set.ncard_compl, Set.ncard_singleton, hV]

theorem five_dihedral (hV : Module.finrank (ZMod 2) V = 4) {c a b : V ≃ₗ[ZMod 2] V}
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hc0 : ∀ v, c v = v → v = 0) (ha : a * a = 1) (hb : b * b = 1)
    (hac : a * c * a⁻¹ = c⁻¹) (hbc : b * c * b⁻¹ = c⁻¹) : a * b ∈ Subgroup.zpowers c := by
  by_contra hzn
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hzc' : (a * b) * c * (a * b)⁻¹ = c := by
    calc (a * b) * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
      _ = a * c⁻¹ * a⁻¹ := by rw [hbc]
      _ = (a * c * a⁻¹)⁻¹ := by group
      _ = c := by rw [hac, inv_inv]
  have hzc : (a * b) * c = c * (a * b) := mul_inv_eq_iff_eq_mul.1 hzc'
  have hza : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, hai, hbi]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  set z : V ≃ₗ[ZMod 2] V := a * b with hz
  set H : Subgroup (V ≃ₗ[ZMod 2] V) := Subgroup.closure ({c, z} : Set (V ≃ₗ[ZMod 2] V)) with hH
  have hcH : c ∈ H := Subgroup.subset_closure (by simp)
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  have hgen : ∀ x ∈ ({c, z} : Set (V ≃ₗ[ZMod 2] V)), ∀ y ∈ ({c, z} : Set (V ≃ₗ[ZMod 2] V)),
      x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact hzc.symm
    · exact hzc
  have hpair : ({c, z} : Set (V ≃ₗ[ZMod 2] V)).Pairwise Commute := fun x hx y hy _ =>
    (commute_iff_eq x y).2 (hgen x hx y hy)
  have hcommH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy =>
    Set.centralizer_centralizer_comm_of_comm hpair x
      (Subgroup.closure_le_centralizer_centralizer _ hx) y
      (Subgroup.closure_le_centralizer_centralizer _ hy)
  have hinvH : ∀ x ∈ H, a * x * a⁻¹ = x⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact hac
      · rw [hx]
        exact hza
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hx' : x ∈ H := hx
      have hy' : y ∈ H := hy
      rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group, ihx, ihy, mul_inv_rev]
      exact ((commute_iff_eq x y).2 (hcommH x hx' y hy')).inv_inv.eq
    | inv x hx ih =>
      rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group, ih]
  have hfreeH : ∀ x ∈ H, x ≠ 1 → ∀ v : V, x v = v → v = 0 := fun x hx hx1 =>
    five_free hV hc5 hc0 (hcommH x hx c hcH) hx1
  have hV16 := card_eq_sixteen hV
  have hdvd : Nat.card H ∣ 15 := by
    have h := card_dvd_of_free H hfreeH
    rw [hV16] at h
    exact h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hzp : Nat.card (Subgroup.zpowers c) = 5 := by rw [Nat.card_zpowers, hord]
  have hzpH : Subgroup.zpowers c ≤ H := (Subgroup.zpowers_le).2 hcH
  have h5 : 5 ∣ Nat.card H := hzp ▸ Subgroup.card_dvd_of_le hzpH
  have hgt : 5 < Nat.card H := by
    by_contra hle
    push Not at hle
    have := Subgroup.eq_of_le_of_card_ge hzpH (by rw [hzp]; exact hle)
    exact hzn (this ▸ hzH)
  have hH15 : Nat.card H = 15 := by
    obtain ⟨k, hk⟩ := h5
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rw [hk] at hdvd hgt hle ⊢
    have hk2 : 2 ≤ k := by omega
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    · omega
    · rfl
  have hfix2 := two_le_finrank_fixSp hV ha
  obtain ⟨v₀, hv₀S, hv₀0⟩ : ∃ v ∈ fixSp V a ⊤, v ≠ 0 := by
    have hpos : 0 < Module.finrank (ZMod 2) ↥(fixSp V a ⊤) := by omega
    obtain ⟨⟨v, hv⟩, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    exact ⟨v, hv, fun h => hvne (Subtype.ext h)⟩
  obtain ⟨v₁, hv₁S, hv₁0, hv₁ne⟩ : ∃ v ∈ fixSp V a ⊤, v ≠ 0 ∧ v ≠ v₀ := by
    by_contra hcon
    push Not at hcon
    have hle : fixSp V a ⊤ ≤ Submodule.span (ZMod 2) {v₀} := by
      intro v hv
      by_cases hv0 : v = 0
      · rw [hv0]
        exact Submodule.zero_mem _
      · rw [hcon v hv hv0]
        exact Submodule.mem_span_singleton_self v₀
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv₀0] at this
    omega
  have hv₀a : a v₀ = v₀ := (CntLin.mem_fixSp.1 hv₀S).2
  have hv₁a : a v₁ = v₁ := (CntLin.mem_fixSp.1 hv₁S).2
  let ι : H → {v : V // v ≠ 0} := fun h =>
    ⟨(h : V ≃ₗ[ZMod 2] V) v₀, fun h0 => hv₀0 ((LinearEquiv.map_eq_zero_iff _).1 h0)⟩
  have hinj : Function.Injective ι := by
    intro h h' hh
    have hvv : (h : V ≃ₗ[ZMod 2] V) v₀ = (h' : V ≃ₗ[ZMod 2] V) v₀ := congrArg Subtype.val hh
    have hmem : (h' : V ≃ₗ[ZMod 2] V)⁻¹ * (h : V ≃ₗ[ZMod 2] V) ∈ H :=
      H.mul_mem (H.inv_mem h'.2) h.2
    by_contra hne
    have hne1 : (h' : V ≃ₗ[ZMod 2] V)⁻¹ * (h : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h1 =>
      hne (Subtype.ext (inv_mul_eq_one.1 h1).symm)
    exact hv₀0 (hfreeH _ hmem hne1 v₀ (by
      rw [LinearEquiv.mul_apply, hvv]
      exact CntLin.inv_apply_apply _ _))
  have hbij : Function.Bijective ι := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [card_nonzero_of_card_sixteen hV16, hH15]
  obtain ⟨h, hh⟩ := hbij.2 ⟨v₁, hv₁0⟩
  have hhv : (h : V ≃ₗ[ZMod 2] V) v₀ = v₁ := congrArg Subtype.val hh
  have hah : a * (h : V ≃ₗ[ZMod 2] V) = (h : V ≃ₗ[ZMod 2] V)⁻¹ * a := by
    have := hinvH _ h.2
    exact mul_inv_eq_iff_eq_mul.1 this
  have h1 : (h : V ≃ₗ[ZMod 2] V)⁻¹ v₀ = v₁ := by
    have := DFunLike.congr_fun hah v₀
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhv, hv₀a, hv₁a] at this
    exact this.symm
  have hsq : ((h : V ≃ₗ[ZMod 2] V) * (h : V ≃ₗ[ZMod 2] V)) v₀ = v₀ := by
    rw [LinearEquiv.mul_apply, hhv, ← h1, CntLin.apply_inv_apply]
  have hhh : (h : V ≃ₗ[ZMod 2] V) * (h : V ≃ₗ[ZMod 2] V) = 1 := by
    by_contra hne
    exact hv₀0 (hfreeH _ (H.mul_mem h.2 h.2) hne v₀ hsq)
  have h11 : (h : V ≃ₗ[ZMod 2] V) = 1 :=
    five_invol hV hc5 hc0 hhh (hcommH _ h.2 c hcH)
  rw [h11] at hhv
  exact hv₁ne (by rw [← hhv]; rfl)

end Linear

theorem nonempty_closure_pair_mulEquiv_dihedral {G : Type*} [Group G] [Finite G] {ρ σ : G}
    (hσ : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ Subgroup.zpowers ρ) :
    Nonempty (Subgroup.closure ({ρ, σ} : Set G) ≃* DihedralGroup (orderOf ρ)) := by
  have hρH : ρ ∈ Subgroup.closure ({ρ, σ} : Set G) := Subgroup.subset_closure (by simp)
  have hσH : σ ∈ Subgroup.closure ({ρ, σ} : Set G) := Subgroup.subset_closure (by simp)
  have hgen : (⊤ : Subgroup (Subgroup.closure ({ρ, σ} : Set G))) =
      Subgroup.zpowers ⟨ρ, hρH⟩ ⊔ Subgroup.zpowers ⟨σ, hσH⟩ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      ← Subgroup.closure_closure_coe_preimage (k := ({ρ, σ} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem
    (D := Subgroup.closure ({ρ, σ} : Set G)) ⟨ρ, hρH⟩ ⟨σ, hσH⟩ hgen
    (Subtype.ext (by simpa using hσ)) (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ (by
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hmem
      exact (Subgroup.mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h

section Case

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_generator_five {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hV : Module.finrank (ZMod 2) V = 4) (hRne : pCoreOf 5 Γ ≠ ⊥) :
    Nat.card (pCoreOf 5 Γ) = 5 ∧ ∃ c : GLV V, c ∈ pCoreOf 5 Γ ∧ c ≠ 1 ∧ c ^ 5 = 1 ∧
      orderOf c = 5 ∧ pCoreOf 5 Γ = Subgroup.zpowers c ∧ ∀ v, c v = v → v = 0 := by
  have := finite_linearEquiv_zmod2 V
  set R := pCoreOf 5 Γ with hRdef
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hR5 : Nat.card R = 5 := by
    have hdvd := card_dvd_five_of_isPGroup_five hV (isPGroup_pCoreOf 5 Γ)
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hRne
    · exact h
  refine ⟨hR5, ?_⟩
  obtain ⟨c', hc'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hRne
  set c : GLV V := (c' : GLV V) with hcdef
  have hcR : c ∈ R := c'.2
  have hc1 : c ≠ 1 := fun h => hc'1 (Subtype.ext h)
  have hc5 : c ^ 5 = 1 := by
    have := pow_card_eq_one' (G := R) (x := c')
    rw [hR5] at this
    exact congrArg Subtype.val this
  have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hRz : R = Subgroup.zpowers c := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hcR)
    rw [hR5, Nat.card_zpowers, hord]
  refine ⟨c, hcR, hc1, hc5, hord, hRz, ?_⟩
  intro v hv
  have hF := g94_fixedSpace_pCoreOf_eq_bot hyp hRne
  have hmem : v ∈ fixedSpace R := by
    rw [hRz]
    exact mem_fixedSpace_zpowers_iff.2 hv
  rw [hF] at hmem
  simpa using hmem

theorem five_case {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hV : Module.finrank (ZMod 2) V = 4) (hm : m = 1)
    (hnot : ¬ A ≤ Subgroup.centralizer (pCoreOf 5 Γ : Set (GLV V))) :
    Nonempty (↥(normalClosure Γ A) ≃* DihedralGroup 5) ∧ 10 ∣ Nat.card ↥Γ := by
  have := finite_linearEquiv_zmod2 V
  have hRne : pCoreOf 5 Γ ≠ ⊥ := by
    intro h
    apply hnot
    rw [h]
    intro a _
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Subgroup.mem_bot.mp hg]; simp
  obtain ⟨hR5, c, hcR, hc1, hc5, hord, hRz, hc0⟩ := exists_generator_five hyp hV hRne
  set R := pCoreOf 5 Γ with hRdef
  obtain ⟨a, haA, haR⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact haR (Subgroup.one_mem _)
  have ha2 : a * a = 1 := by
    have := hyp.A_elem.2 a haA
    rwa [pow_two] at this
  have hnormR : ∀ x ∈ R, a * x * a⁻¹ ∈ R := fun x hx =>
    pCoreOf_normal_conj 5 Γ a (hyp.A_le haA) x hx
  have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    rw [hRz] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self c i j).eq
  have hinvR : ∀ x ∈ R, a * x * a⁻¹ = x⁻¹ := by
    rcases centralizes_or_inverts Nat.prime_five hR5 hcommR ha2 hnormR with h | h
    · exfalso
      apply haR
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (mul_inv_eq_iff_eq_mul.1 (h x hx)).symm
    · exact h
  have hac : a * c * a⁻¹ = c⁻¹ := hinvR c hcR
  have hAcard : Nat.card A = 2 := by rw [hyp.A_card, hm]; norm_num
  have hAeq : ∀ l ∈ A, l = 1 ∨ l = a := by
    intro l hl
    by_cases hl1 : l = 1
    · exact Or.inl hl1
    · right
      obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).1 hAcard
      have h1 := huniq ⟨l, hl⟩ (fun h => hl1 (congrArg Subtype.val h))
      have h2 := huniq ⟨a, haA⟩ (fun h => ha1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hbinv : ∀ γ ∈ Γ, (γ * a * γ⁻¹) * c * (γ * a * γ⁻¹)⁻¹ = c⁻¹ := by
    intro γ hγ
    have hmem : γ⁻¹ * c * γ ∈ R := by
      have := pCoreOf_normal_conj 5 Γ γ⁻¹ (Γ.inv_mem hγ) c hcR
      simpa using this
    have := hinvR _ hmem
    calc (γ * a * γ⁻¹) * c * (γ * a * γ⁻¹)⁻¹
        = γ * (a * (γ⁻¹ * c * γ) * a⁻¹) * γ⁻¹ := by group
      _ = γ * (γ⁻¹ * c * γ)⁻¹ * γ⁻¹ := by rw [this]
      _ = c⁻¹ := by group
  have hNle : normalClosure Γ A ≤ Subgroup.closure ({c, a} : Set (GLV V)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨γ, hγ, l, hl, rfl⟩
    rcases hAeq l hl with hl1 | hla
    · rw [hl1]
      simp only [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [hla]
      have hb2 : (γ * a * γ⁻¹) * (γ * a * γ⁻¹) = 1 := by
        calc (γ * a * γ⁻¹) * (γ * a * γ⁻¹) = γ * (a * a) * γ⁻¹ := by group
          _ = 1 := by rw [ha2]; group
      have hdih := five_dihedral hV hc5 hc1 hc0 ha2 hb2 hac (hbinv γ hγ)
      have hbeq : γ * a * γ⁻¹ = a * (a * (γ * a * γ⁻¹)) := by
        rw [← mul_assoc, ha2, one_mul]
      rw [hbeq]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) ?_
      exact (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp : c ∈ ({c, a} : Set (GLV V)))))
        hdih
  have hNge : Subgroup.closure ({c, a} : Set (GLV V)) ≤ normalClosure Γ A := by
    refine (Subgroup.closure_le _).2 ?_
    have haN : a ∈ normalClosure Γ A :=
      Subgroup.subset_closure ⟨1, Γ.one_mem, a, haA, by simp⟩
    have hcΓ : c ∈ Γ := Subgroup.map_subtype_le _ hcR
    have hcaN : c * a * c⁻¹ ∈ normalClosure Γ A :=
      Subgroup.subset_closure ⟨c, hcΓ, a, haA, rfl⟩
    have hc2 : c⁻¹ * c⁻¹ ∈ normalClosure Γ A := by
      have h1 : a * c = c⁻¹ * a := mul_inv_eq_iff_eq_mul.1 hac
      have : a * (c * a * c⁻¹) = c⁻¹ * c⁻¹ := by
        calc a * (c * a * c⁻¹) = (a * c) * a * c⁻¹ := by group
          _ = c⁻¹ * a * a * c⁻¹ := by rw [h1]
          _ = c⁻¹ * (a * a) * c⁻¹ := by group
          _ = c⁻¹ * c⁻¹ := by rw [ha2]; group
      rw [← this]
      exact Subgroup.mul_mem _ haN hcaN
    have hcN : c ∈ normalClosure Γ A := by
      have hcc : c = c⁻¹ * c⁻¹ * (c⁻¹ * c⁻¹) * c ^ 5 := by group
      rw [hc5, mul_one] at hcc
      rw [hcc]
      exact Subgroup.mul_mem _ hc2 hc2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact hcN
    · rw [hx]
      exact haN
  have hN : normalClosure Γ A = Subgroup.closure ({c, a} : Set (GLV V)) := le_antisymm hNle hNge
  have hσρ : a ∉ Subgroup.zpowers c := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcomm : a * c = c * a := by
      rw [← hk]
      exact (Commute.zpow_self c k).eq
    have h1 : a * c * a⁻¹ = c := by rw [hcomm]; group
    rw [hac] at h1
    have h2 : c ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [← h1]
      exact mul_inv_cancel c
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    omega
  have hdihedral : Nonempty (↥(Subgroup.closure ({c, a} : Set (GLV V))) ≃* DihedralGroup 5) := by
    have := nonempty_closure_pair_mulEquiv_dihedral (ρ := c) (σ := a)
      (by rw [pow_two]; exact ha2) hac hσρ
    rwa [hord] at this
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := hdihedral
    exact ⟨(MulEquiv.subgroupCongr hN).trans e⟩
  · have h5 : 5 ∣ Nat.card ↥Γ := hR5 ▸ Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
    have h2 : 2 ∣ Nat.card ↥Γ := by
      have : 2 ∣ Nat.card A := by rw [hAcard]
      exact this.trans (Subgroup.card_dvd_of_le hyp.A_le)
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 2) h5 h2
    simpa using this

end Case

end SmD4Five

end CFSG.Quasithin.SzN31
