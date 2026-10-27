module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.Stroth

open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem commutatorElement_mul_left_of_commute {a b ω : G} (hb : a * ⁅b, ω⁆ = ⁅b, ω⁆ * a)
    (hab : ⁅a, ω⁆ * ⁅b, ω⁆ = ⁅b, ω⁆ * ⁅a, ω⁆) : ⁅a * b, ω⁆ = ⁅a, ω⁆ * ⁅b, ω⁆ := by
  rw [commutatorElement_def] at hb hab ⊢
  rw [commutatorElement_def] at hab
  calc a * b * ω * (a * b)⁻¹ * ω⁻¹
      = a * (b * ω * b⁻¹ * ω⁻¹) * (ω * a⁻¹ * ω⁻¹) := by group
    _ = b * ω * b⁻¹ * ω⁻¹ * a * (ω * a⁻¹ * ω⁻¹) := by rw [hb]
    _ = (b * ω * b⁻¹ * ω⁻¹) * (a * ω * a⁻¹ * ω⁻¹) := by group
    _ = a * ω * a⁻¹ * ω⁻¹ * (b * ω * b⁻¹ * ω⁻¹) := hab.symm

@[expose] def commutatorHom {Q Z : Subgroup G} {ω : G} (hZQ : Z ≤ Q)
    (hZc : Z ≤ Subgroup.centralizer (Q : Set G)) (hcomm : ∀ x ∈ Q, ⁅x, ω⁆ ∈ Z) :
    ↥Q →* ↥Z where
  toFun x := ⟨⁅(x : G), ω⁆, hcomm x x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    have hy : ⁅(y : G), ω⁆ ∈ Z := hcomm y y.2
    have hx : ⁅(x : G), ω⁆ ∈ Z := hcomm x x.2
    simp only [Subgroup.coe_mul]
    exact commutatorElement_mul_left_of_commute
      (Subgroup.mem_centralizer_iff.mp (hZc hy) x x.2)
      (Subgroup.mem_centralizer_iff.mp (hZc hy) _ (hZQ hx))

theorem commutatorHom_apply {Q Z : Subgroup G} {ω : G} (hZQ : Z ≤ Q)
    (hZc : Z ≤ Subgroup.centralizer (Q : Set G)) (hcomm : ∀ x ∈ Q, ⁅x, ω⁆ ∈ Z) (x : ↥Q) :
    ((commutatorHom hZQ hZc hcomm x : ↥Z) : G) = ⁅(x : G), ω⁆ := rfl

theorem eq_of_commutator_le_of_fixedPointFree [Finite G] {Q Z : Subgroup G} {ω : G}
    (hQ : IsPGroup 2 Q) (hZQ : Z ≤ Q) (hZc : Z ≤ Subgroup.centralizer (Q : Set G))
    (hinv : ∀ z ∈ Q, z ∈ Subgroup.centralizer (Q : Set G) → z ^ 2 = 1 → z ∈ Z)
    (hcomm : ∀ x ∈ Q, ⁅x, ω⁆ ∈ Z) (hfree : ∀ z ∈ Z, ⁅z, ω⁆ = 1 → z = 1) : Q = Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := commutatorHom hZQ hZc hcomm with hφ
  have hker : φ.ker = ⊥ := by
    by_contra hne
    haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
    have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := φ.ker) hne
    haveI : Finite ↥(φ.ker ⊓ Subgroup.center ↥Q) := Subtype.finite
    have h2 : IsPGroup 2 ↥(φ.ker ⊓ Subgroup.center ↥Q) := hQ.to_subgroup _
    obtain ⟨u, hu⟩ : ∃ u : ↥(φ.ker ⊓ Subgroup.center ↥Q), orderOf u = 2 := by
      have hnt : Nontrivial ↥(φ.ker ⊓ Subgroup.center ↥Q) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hcen
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
      exact exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
    set v : ↥Q := (u : ↥Q) with hv
    have hvker : v ∈ φ.ker := (Subgroup.mem_inf.mp u.2).1
    have hvcen : v ∈ Subgroup.center ↥Q := (Subgroup.mem_inf.mp u.2).2
    have hvord : orderOf (v : G) = 2 := by
      rw [Subgroup.orderOf_coe, hv, Subgroup.orderOf_coe, hu]
    have hvc : (v : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp hvcen ⟨g, hg⟩
      exact congrArg Subtype.val this
    have hv2 : (v : G) ^ 2 = 1 := by rw [← hvord]; exact pow_orderOf_eq_one _
    have hvZ : (v : G) ∈ Z := hinv _ v.2 hvc hv2
    have hvω : ⁅(v : G), ω⁆ = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hvker)
      simpa [hφ, commutatorHom_apply] using h
    have := hfree _ hvZ hvω
    rw [this, orderOf_one] at hvord
    exact absurd hvord (by norm_num)
  set ψ : ↥Z →* ↥Z := φ.comp (Subgroup.inclusion hZQ) with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have h := congrArg Subtype.val hz
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfree z z.2 (by simpa [hψ, hφ, commutatorHom_apply] using h))
  have hψsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψinj
  refine le_antisymm (fun x hx => ?_) hZQ
  obtain ⟨z, hz⟩ := hψsurj (φ ⟨x, hx⟩)
  have hk : (⟨x, hx⟩ : ↥Q) * (Subgroup.inclusion hZQ z)⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : φ (Subgroup.inclusion hZQ z) = φ ⟨x, hx⟩ := hz
    rw [this, mul_inv_cancel]
  rw [hker, Subgroup.mem_bot] at hk
  have hxz : x = z := by
    have h := congrArg Subtype.val (mul_inv_eq_one.mp hk)
    simpa using h
  rw [hxz]
  exact z.2

theorem mem_conj_smul_iff' {g x : G} {R : Subgroup G} :
    x ∈ MulAut.conj g • R ↔ g⁻¹ * x * g ∈ R := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

private theorem inf_conj_mul_iff {R A Z : Subgroup G} (hZR : Z ≤ R) (hcomm : ⁅R, A⁆ ≤ Z)
    {g a x : G} (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (ha : a ∈ A) (hx : x ∈ R) :
    (g⁻¹ * (a⁻¹ * x * a) * g ∈ R ↔ g⁻¹ * x * g ∈ R) := by
  have hz : x⁻¹ * a⁻¹ * x * a ∈ Z := by
    have h : ⁅x⁻¹, a⁻¹⁆ ∈ ⁅R, A⁆ :=
      Subgroup.commutator_mem_commutator (R.inv_mem hx) (A.inv_mem ha)
    have h' := hcomm h
    rwa [commutatorElement_def, inv_inv, inv_inv] at h'
  have hz' : g⁻¹ * (x⁻¹ * a⁻¹ * x * a) * g ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgZ) _).mp hz
    rw [inv_inv] at h
    exact hZR h
  have e : g⁻¹ * (a⁻¹ * x * a) * g = (g⁻¹ * x * g) * (g⁻¹ * (x⁻¹ * a⁻¹ * x * a) * g) := by
    group
  rw [e]
  refine ⟨fun h => ?_, fun h => R.mul_mem h hz'⟩
  have h' := R.mul_mem h (R.inv_mem hz')
  rwa [mul_inv_cancel_right] at h'

theorem inf_conj_eq_iInf_of_transitive {H B S Q R A Z : Subgroup G} (hBH : B ≤ H) (hSB : S ≤ B)
    (hQS : Q ≤ S) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (htrans : ∀ g ∈ H, g ∉ B → ∀ g' ∈ H, g' ∉ B → ∃ s ∈ S, (s * g)⁻¹ * g' ∈ B)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) (hAR : A ≤ R)
    (hAQ : ∀ s ∈ S, ∃ a ∈ A, a⁻¹ * s ∈ Q) (hZR : Z ≤ R)
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) (hcomm : ⁅R, A⁆ ≤ Z)
    {g : G} (hg : g ∈ H) (hgB : g ∉ B) :
    R ⊓ (MulAut.conj g • R) = ⨅ h ∈ H, MulAut.conj h • R := by
  have hBRmem : ∀ b ∈ B, ∀ y : G, b⁻¹ * y * b ∈ R ↔ y ∈ R := by
    intro b hb y
    have h := (Subgroup.mem_normalizer_iff.mp (hBR (B.inv_mem hb))) y
    rw [inv_inv] at h
    exact h.symm
  have hsame : ∀ g' ∈ H, g' ∉ B → ∀ x ∈ R, (g'⁻¹ * x * g' ∈ R ↔ g⁻¹ * x * g ∈ R) := by
    intro g' hg' hg'B x hx
    obtain ⟨s, hs, hsb⟩ := htrans g hg hgB g' hg' hg'B
    set b := (s * g)⁻¹ * g' with hbdef
    have hg'eq : g' = s * g * b := by rw [hbdef]; group
    obtain ⟨a, ha, haq⟩ := hAQ s hs
    set q := a⁻¹ * s with hqdef
    have hseq : s = a * q := by rw [hqdef]; group
    have hq' : g⁻¹ * q * g ∈ B := by
      have h := (Subgroup.mem_normalizer_iff.mp (H.inv_mem hg |> hHQ) q).mp haq
      rw [inv_inv] at h
      exact hSB (hQS h)
    rw [hg'eq]
    have e1 : (s * g * b)⁻¹ * x * (s * g * b) = b⁻¹ * ((g⁻¹ * q * g)⁻¹ *
        (g⁻¹ * (a⁻¹ * x * a) * g) * (g⁻¹ * q * g)) * b := by
      rw [hseq]; group
    rw [e1, hBRmem b hsb, hBRmem _ hq']
    exact inf_conj_mul_iff hZR hcomm (hHZ hg) ha hx
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, mem_conj_smul_iff']
  constructor
  · rintro ⟨hx, hxg⟩ h hh
    by_cases hhB : h ∈ B
    · exact (hBRmem h hhB x).mpr hx
    · exact (hsame h hh hhB x hx).mpr hxg
  · intro hx
    have hx1 : x ∈ R := by simpa using hx 1 H.one_mem
    exact ⟨hx1, hx g hg⟩

end CFSG.Quasithin.Stroth

end
