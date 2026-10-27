module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts
open Matrix

section PglHomSub

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool} {e : L ≃* slPi π 3 (p ^ f) K} {S : Subfield K}

theorem subGL_inv_mul_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {a : G}
    {y₀ z₀ : GL (Fin 3) S} (hy : IsPGLAt e a (subGL S y₀)) (hz : IsPGLAt e a (subGL S z₀)) :
    y₀⁻¹ * z₀ ∈ StatedScalars (Fin 3) S := by
  apply mem_statedScalars_of_subGL S
  rw [map_mul, map_inv]
  exact isPGLAt_inv_mul_mem hK hq hy hz

variable (S)

@[expose] noncomputable def pglHomSub (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (A' : Subgroup G) (hA' : ∀ a ∈ A', ∃ y₀ : GL (Fin 3) S, IsPGLAt e a (subGL S y₀)) :
    A' →* GL (Fin 3) S ⧸ StatedScalars (Fin 3) S where
  toFun a :=
    ((Classical.choose (hA' a a.2) : GL (Fin 3) S) : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S)
  map_one' := by
    have h1 := Classical.choose_spec (hA' 1 A'.one_mem)
    have h2 : IsPGLAt e (1 : G) (subGL S 1) := by
      rw [map_one]
      exact isPGLAt_of_mem_centralizer e (Subgroup.one_mem _)
    have h3 := subGL_inv_mul_mem hK hq h2 h1
    rw [inv_one, one_mul] at h3
    exact (QuotientGroup.eq_one_iff _).mpr h3
  map_mul' a b := by
    have ha := Classical.choose_spec (hA' a a.2)
    have hb := Classical.choose_spec (hA' b b.2)
    have hab := Classical.choose_spec (hA' (a * b) (a * b).2)
    have h : IsPGLAt e ((a : G) * b) (subGL S (Classical.choose (hA' a a.2) *
        Classical.choose (hA' b b.2))) := by
      rw [map_mul]
      exact isPGLAt_mul e ha hb
    have h3 := subGL_inv_mul_mem hK hq h hab
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := inv_mem h3
    rwa [_root_.mul_inv_rev, inv_inv] at this

variable {S} {hK : PiField π p f K} {hq : ModThree π (p ^ f)} {A' : Subgroup G}
  {hA' : ∀ a ∈ A', ∃ y₀ : GL (Fin 3) S, IsPGLAt e a (subGL S y₀)}

theorem pglHomSub_apply (a : A') {y₀ : GL (Fin 3) S} (hy : IsPGLAt e a (subGL S y₀)) :
    pglHomSub S hK hq A' hA' a = (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) := by
  change ((Classical.choose (hA' a a.2) : GL (Fin 3) S) :
    GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) = y₀
  rw [QuotientGroup.eq]
  exact subGL_inv_mul_mem hK hq (Classical.choose_spec (hA' a a.2)) hy

theorem pglHomSub_eq_one_iff (a : A') :
    pglHomSub S hK hq A' hA' a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨y₀, hy⟩ := hA' a a.2
  rw [pglHomSub_apply a hy, QuotientGroup.eq_one_iff]
  constructor
  · intro hs
    obtain ⟨u, hu⟩ := hs
    refine mem_centralizer_of_isPGLAt_scalar hy ⟨Units.map (S.subtype : S →* K) u, ?_⟩
    rw [← subGL_scalar, hu]
  · intro hc
    have h1 : IsPGLAt e (a : G) (subGL S 1) := by
      rw [map_one]
      exact isPGLAt_of_mem_centralizer e hc
    have := subGL_inv_mul_mem hK hq h1 hy
    rwa [inv_one, one_mul] at this

theorem ker_pglHomSub :
    (pglHomSub S hK hq A' hA').ker = (Subgroup.centralizer (L : Set G)).subgroupOf A' := by
  ext a
  rw [MonoidHom.mem_ker, pglHomSub_eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_eq_card_inf_mul_card_range_sub :
    Nat.card A' = Nat.card (A' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) *
      Nat.card (pglHomSub S hK hq A' hA').range := by
  rw [← Subgroup.index_ker (pglHomSub S hK hq A' hA'),
    ← Subgroup.card_mul_index (pglHomSub S hK hq A' hA').ker,
    ker_pglHomSub, ← Subgroup.inf_subgroupOf_left]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem range_pglHomSub_comm (hcomm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) :
    ∀ x ∈ (pglHomSub S hK hq A' hA').range, ∀ y ∈ (pglHomSub S hK hq A' hA').range,
      x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm a a.2 b b.2)

theorem range_pglHomSub_pow (h3 : ∀ a ∈ A', a ^ 3 = 1) :
    ∀ x ∈ (pglHomSub S hK hq A' hA').range, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h3 a a.2, Subgroup.coe_one])
  rw [this, map_one]

theorem mk_mem_range_pglHomSub {a : G} (ha : a ∈ A') {y₀ : GL (Fin 3) S}
    (hy : IsPGLAt e a (subGL S y₀)) :
    (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) ∈ (pglHomSub S hK hq A' hA').range :=
  ⟨⟨a, ha⟩, pglHomSub_apply ⟨a, ha⟩ hy⟩

theorem exists_of_mk_mem_range_pglHomSub {y₀ : GL (Fin 3) S}
    (hmem : (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) ∈ (pglHomSub S hK hq A' hA').range) :
    ∃ a ∈ A', ∃ z₀ : GL (Fin 3) S, IsPGLAt e a (subGL S z₀) ∧ ∃ u : Sˣ,
      y₀ = z₀ * GeneralLinearGroup.scalar (Fin 3) u := by
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨z₀, hz⟩ := hA' a a.2
  rw [pglHomSub_apply a hz, QuotientGroup.eq] at ha
  obtain ⟨u, hu⟩ := ha
  exact ⟨a, a.2, z₀, hz, u, by rw [hu]; group⟩

theorem mk_subGL_mem_range_pglHom {hA'' : ∀ a ∈ A', ∃ y, IsPGLAt e a y} {y₀ : GL (Fin 3) S}
    (hmem : (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) ∈ (pglHomSub S hK hq A' hA').range) :
    ((subGL S y₀ : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHom hK hq A' hA'').range := by
  obtain ⟨a, ha, z₀, hz, u, rfl⟩ := exists_of_mk_mem_range_pglHomSub hmem
  refine ⟨⟨a, ha⟩, ?_⟩
  rw [pglHom_apply ⟨a, ha⟩ hz, QuotientGroup.eq, map_mul, subGL_scalar]
  refine ⟨Units.map (S.subtype : S →* K) u, ?_⟩
  group

end PglHomSub

section Small

variable {K : Type} [Field K]

theorem frob_eq_of_cube {π : Bool} {q₀ : ℕ} (hq₀ : ModThree π q₀) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard π q₀) {τ : K} (hτ : τ ^ 3 = 1) : φ τ = τ := by
  have hr : piCard π q₀ % 3 = 1 := by
    cases π
    · change q₀ % 3 = 2 at hq₀
      change q₀ ^ 2 % 3 = 1
      rw [Nat.pow_mod, hq₀]
    · exact hq₀
  rw [hφ, ← Nat.div_add_mod (piCard π q₀) 3, hr, pow_add, pow_mul, hτ, one_pow, one_mul,
    pow_one]

theorem frobGL_diagTau {ψ : K ≃+* K} {τ : K} (hτ : τ ^ 3 = 1) (hψτ : ψ τ = τ) :
    frobGL ψ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_frobGL, coe_diagTau_eq_diagonal, diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [hψτ]

theorem diagTau_offdiag {τ : K} (hτ : τ ^ 3 = 1) :
    ∀ i j, i ≠ j → ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  intro i j hij
  rw [coe_diagTau_eq_diagonal, diagonal_apply_ne _ hij]

theorem diagTau_not_mem_statedScalars {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagTau hτ ∉ StatedScalars (Fin 3) K := by
  rintro ⟨t, ht⟩
  have h00 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) ht
  have h22 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) ht
  simp only [coe_diagTau_eq_diagonal, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h00 h22
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h00 h22
  exact hτ1 (h00.symm.trans h22)

end Small

section FourHeis

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_mem_centralizer_sigma {c : G} (hc3 : orderOf c = 3) (hcL : c ∈ L)
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) {B : Subgroup G} {σ : G}
    (hσB : ∀ b ∈ B, b * σ = σ * b)
    (hU27 : Nat.card ((B ⊔ L) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = 27) :
    ∃ u ∈ (B ⊔ L) ⊓ Subgroup.centralizer (L : Set G), u ∉ Subgroup.zpowers c ∧
      u * σ = σ * u := by
  classical
  set U := (B ⊔ L) ⊓ Subgroup.centralizer (L : Set G) with hU
  have hχmem : ∀ u ∈ U, σ * u * σ⁻¹ * u⁻¹ ∈ Subgroup.zpowers c := by
    intro u hu
    rw [← hLC]
    obtain ⟨b, hb, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (Subgroup.mem_inf.mp hu).1
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e1 : σ * (b * l) * σ⁻¹ * (b * l)⁻¹ = b * ((σ * l * σ⁻¹) * l⁻¹) * b⁻¹ := by
        calc σ * (b * l) * σ⁻¹ * (b * l)⁻¹ = (σ * b) * l * σ⁻¹ * l⁻¹ * b⁻¹ := by group
          _ = (b * σ) * l * σ⁻¹ * l⁻¹ * b⁻¹ := by rw [hσB b hb]
          _ = _ := by group
      rw [e1]
      exact hLn.conj_mem _ (mul_mem (hLn.conj_mem l hl σ) (inv_mem hl)) b
    · have hC : (Subgroup.centralizer (L : Set G)).Normal := inferInstance
      have huC := (Subgroup.mem_inf.mp hu).2
      exact mul_mem (hC.conj_mem _ huC σ) (inv_mem huC)
  have hcL' : Subgroup.zpowers c ≤ L := Subgroup.zpowers_le.mpr hcL
  have hcomm : ∀ u ∈ U, ∀ x ∈ Subgroup.zpowers c, u * x = x * u := fun u hu x hx =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2) x (hcL' hx)).symm
  let χ : U →* G :=
    { toFun := fun u => σ * u * σ⁻¹ * (u : G)⁻¹
      map_one' := by simp
      map_mul' := fun u u' => by
        have h := hcomm u u.2 _ (hχmem u' u'.2)
        simp only [Subgroup.coe_mul]
        obtain ⟨a, ha⟩ : ∃ a : G, a = u := ⟨_, rfl⟩
        obtain ⟨b, hb⟩ : ∃ b : G, b = u' := ⟨_, rfl⟩
        rw [← ha, ← hb] at h ⊢
        calc σ * (a * b) * σ⁻¹ * (a * b)⁻¹ =
            σ * a * σ⁻¹ * (a⁻¹ * (a * (σ * b * σ⁻¹ * b⁻¹))) * a⁻¹ := by group
          _ = σ * a * σ⁻¹ * (a⁻¹ * ((σ * b * σ⁻¹ * b⁻¹) * a)) * a⁻¹ := by rw [h]
          _ = σ * a * σ⁻¹ * a⁻¹ * (σ * b * σ⁻¹ * b⁻¹) := by group }
  have hker : ∀ x : U, x ∈ χ.ker ↔ (x : G) * σ = σ * x := by
    intro x
    rw [MonoidHom.mem_ker]
    change σ * (x : G) * σ⁻¹ * (x : G)⁻¹ = 1 ↔ _
    constructor
    · intro h
      calc (x : G) * σ = (σ * x * σ⁻¹ * (x : G)⁻¹)⁻¹ * σ * x := by group
        _ = σ * x := by rw [h, inv_one, one_mul]
    · intro h
      rw [← h]
      group
  have hrange : Nat.card χ.range ≤ 3 := by
    have hle : χ.range ≤ Subgroup.zpowers c := by
      rintro _ ⟨x, rfl⟩
      exact hχmem x x.2
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hc3] at this
  have hcard := Subgroup.card_mul_index χ.ker
  rw [Subgroup.index_ker, hU27] at hcard
  by_contra hne
  push Not at hne
  have hinj : Nat.card χ.ker ≤ 3 := by
    have hmem : ∀ x : χ.ker, ((x : U) : G) ∈ Subgroup.zpowers c := by
      intro x
      by_contra hx
      exact hx.elim (by
        have := hne ((x : U) : G) (x : U).2 hx
        exact absurd ((hker x).mp x.2) this)
    have h := Nat.card_le_card_of_injective (fun x : χ.ker => (⟨((x : U) : G), hmem x⟩ :
      Subgroup.zpowers c)) (fun x y hxy => Subtype.ext (Subtype.ext (by
        simpa using congrArg Subtype.val hxy)))
    rwa [Nat.card_zpowers, hc3] at h
  have : Nat.card χ.ker * Nat.card χ.range ≤ 3 * 3 := Nat.mul_le_mul hinj hrange
  omega

end FourHeis

section FourHeisMain

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite G] in
theorem isElemAbelian_bot : CFSG.Assembly.IsElemAbelian 3 (⊥ : Subgroup G) :=
  ⟨⟨⟨fun x y => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩

theorem fieldFour_heis (hG : SectionFourHyp G) (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    {σ : G} (hσA : σ ∈ A) (hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    (hB27 : Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) = 27)
    (hBc : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers c)
    (hpglB : ∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)), ∃ y, IsPGLAt e b y)
    {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq _ hpglB).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq _ hpglB).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    p = 2 ∧ π = false ∧
      IsHeisCentral ↥(A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ L) ↥L := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hq₀ : ModThree π (p ^ f₀) :=
    modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  have hψτ : ψ τ = τ :=
    (fixed_iff_of_sq hφ3 hψ τ).mpr (frob_eq_of_cube hq₀ hφ hτ)
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B := A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) with hBdef
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => hAcomm a ha.1 b hb.1
  have hBel : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hBcomm x x.2 y y.2)⟩⟩, fun x hx => hA.1.2 x hx.1⟩
  have hBL : B ⊓ L ≤ Subgroup.zpowers c := by
    intro b hb
    obtain ⟨hbB, hbL⟩ := Subgroup.mem_inf.mp hb
    have hs := mem_statedScalars_of_commute_lifts hK hq hy₁ hy₂ hζ1 hζ
      (r := ((e ⟨b, hbL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) (fun a ha => by
        obtain ⟨z, hz⟩ := hpglB a ha
        exact ⟨z, hz, (isPGLAt_commute_of_mem hbL (hBcomm a ha b hbB) hz).symm⟩)
    rw [← hBc]
    exact ⟨hbB, mem_centralizer_of_scalar hbL hs⟩
  have h1 : ∀ a ∈ B, a ∉ Subgroup.centralizer (L : Set G) → ∀ y, IsPGLAt e a y →
      Type123 π (p ^ f) K y 1 := by
    intro a ha haC y hy
    rcases type13_of_heis hK hq hBcomm hy₁ hy₂ hζ1 hζ ha haC (hA.1.2 a ha.1) hy with h | h
    · exact h
    · exact absurd ha.2 (not_mem_sup_centralizer_of_type3 hK hq hy h)
  obtain ⟨hU27, hU3, hUinf, hHeis⟩ :=
    heis_of_type1 hK hq e hBel hB27 hc3 hcL hLC hBc hpglB hBL hy₁ hy₂ hζ1 hζ h1
  obtain ⟨u, huU, huc, huσ⟩ := exists_mem_centralizer_sigma hc3 hcL hLC (B := B)
    (fun b hb => hAcomm b hb.1 σ hσA) hU27
  have huC : u ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp huU).2
  have huL : u ∉ L := fun h => huc (by rw [← hUinf]; exact ⟨huU, h⟩)
  have hu3 : u ^ 3 = 1 := hU3 u huU
  obtain ⟨w, hw⟩ : ∃ w : L, w = e.symm ⟨diagTau hτ, diagTau_mem_slPi hπ hq' hτ⟩ := ⟨_, rfl⟩
  have hew : ((e w : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = diagTau hτ := by
    rw [hw, MulEquiv.apply_symm_apply]
  have hw3 : (w : G) ^ 3 = 1 := by
    have : e w ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hew, diagTau_pow_three hτ]
      rfl)
    rw [← map_pow, map_eq_one_iff _ e.injective] at this
    exact congrArg Subtype.val this
  have hwC : (w : G) ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have hs := mem_statedScalars_of_mem_inf hK hq (e := e) h
    rw [hew] at hs
    exact diagTau_not_mem_statedScalars hτ hτ1 hs
  have hwσ : σ * (w : G) = w * σ := by
    rw [hw]
    apply commute_of_slAct_eq
    apply Subtype.ext
    rw [hσψ]
    exact frobGL_diagTau hτ hψτ
  set E₁ : Subgroup G := ⊥ ⊔ Subgroup.zpowers c with hE₁
  set E₂ : Subgroup G := E₁ ⊔ Subgroup.zpowers (w : G) with hE₂
  set E₃ : Subgroup G := E₂ ⊔ Subgroup.zpowers u with hE₃
  set E₄ : Subgroup G := E₃ ⊔ Subgroup.zpowers σ with hE₄
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hE₁L : E₁ ≤ L := sup_le bot_le (Subgroup.zpowers_le.mpr hcL)
  have hE₂L : E₂ ≤ L := sup_le hE₁L (Subgroup.zpowers_le.mpr w.2)
  have hE₃LC : E₃ ≤ L ⊔ Subgroup.centralizer (L : Set G) :=
    sup_le (hE₂L.trans le_sup_left) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right huC))
  have hcE : ∀ a ∈ (⊥ : Subgroup G), a * c = c * a := fun a ha => by
    rw [Subgroup.mem_bot.mp ha, one_mul, mul_one]
  have hwE : ∀ a ∈ E₁, a * (w : G) = w * a := by
    refine commute_sup_of_commute (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_bot.mp ha, one_mul, mul_one]
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left
        ((Subgroup.mem_centralizer_iff.mp hcAC.2 w w.2).symm) k).eq
  have huE : ∀ a ∈ E₂, a * u = u * a := fun a ha =>
    ((Subgroup.mem_centralizer_iff.mp huC) a (hE₂L ha))
  have hσE : ∀ a ∈ E₃, a * σ = σ * a := by
    refine commute_sup_of_commute (commute_sup_of_commute (commute_sup_of_commute ?_ ?_) ?_) ?_
    · intro a ha
      rw [Subgroup.mem_bot.mp ha, one_mul, mul_one]
    · intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (hAcomm c hcAC.1 σ hσA) k).eq
    · intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute (w : G) σ from hwσ.symm) k).eq
    · intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute u σ from huσ) k).eq
  have hcnot : c ∉ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot]
    intro h
    rw [h, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)
  have hwnot : (w : G) ∉ E₁ := by
    intro h
    apply hwC
    have hle : E₁ ≤ Subgroup.centralizer (L : Set G) :=
      sup_le bot_le (Subgroup.zpowers_le.mpr hcAC.2)
    exact hle h
  have hunot : u ∉ E₂ := fun h => huL (hE₂L h)
  have hσnot : σ ∉ E₃ := fun h => hσB (hE₃LC h)
  have hel₁ := isElemAbelian_sup_zpowers isElemAbelian_bot hc3' hcE
  have hel₂ := isElemAbelian_sup_zpowers hel₁ hw3 hwE
  have hel₃ := isElemAbelian_sup_zpowers hel₂ hu3 huE
  have hel₄ := isElemAbelian_sup_zpowers hel₃ (hA.1.2 σ hσA) hσE
  have hcard₁ := card_sup_zpowers_of_not_mem hc3' hcE hcnot
  have hcard₂ := card_sup_zpowers_of_not_mem hw3 hwE hwnot
  have hcard₃ := card_sup_zpowers_of_not_mem hu3 huE hunot
  have hcard₄ := card_sup_zpowers_of_not_mem (hA.1.2 σ hσA) hσE hσnot
  rw [Subgroup.card_bot] at hcard₁
  have hE81 : Nat.card E₄ = 81 := by
    rw [hE₄, hcard₄, hE₃, hcard₃, hE₂, hcard₂, hE₁, hcard₁]
  have hgen : E₄ ≤ Subgroup.closure (diagOrFrob e σ) := by
    have hone : ∀ i j : Fin 3, i ≠ j → ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
      fun i j hij => by rw [Units.val_one, Matrix.one_apply_ne hij]
    refine sup_le (sup_le (sup_le (sup_le bot_le ?_) ?_) ?_) ?_ <;>
      rw [Subgroup.zpowers_le] <;> apply Subgroup.subset_closure
    · exact Or.inl ⟨1, isPGLAt_of_mem_centralizer e hcAC.2, hone⟩
    · refine Or.inl ⟨diagTau hτ, ?_, diagTau_offdiag hτ⟩
      have := isPGLAt_of_mem e hπ w.2
      rwa [show (⟨(w : G), w.2⟩ : L) = w from rfl, hew] at this
    · exact Or.inl ⟨1, isPGLAt_of_mem_centralizer e huC, hone⟩
    · exact Or.inr rfl
  obtain ⟨hp2, hπf⟩ := two_and_unitary_of_rank_four hG hK e hσψ hel₄ hE81 hgen
  exact ⟨hp2, hπf, hHeis⟩

end FourHeisMain

section FrameTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite G] in
theorem isPGLAt_trans_conjSL (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) {e : L ≃* slPi π 3 (p ^ f) K} {a : G} {y : GL (Fin 3) K}
    (hy : IsPGLAt e a y) : IsPGLAt (e.trans (conjSL hπ hh)) a (h⁻¹ * y * h) := by
  refine ⟨mul_mem (mul_mem (inv_mem hh) hy.1) hh, fun s => ?_⟩
  have h1 := hy.2 ((conjSL hπ hh).symm s)
  rw [slAct_apply] at h1 ⊢
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, coe_conjSL]
  rw [h1, coe_conjSL_symm]
  group

omit [Finite G] in
theorem slAct_trans_conjSL_of_fixed (hπ : π = false → UnitaryFieldData p f K)
    {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) {e : L ≃* slPi π 3 (p ^ f) K} {σ : G}
    {ψ : K ≃+* K}
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    (hhψ : frobGL ψ h = h) (s : slPi π 3 (p ^ f) K) :
    ((slAct (e.trans (conjSL hπ hh)) ⟨σ, mem_normalizer_of_normal σ⟩ s :
      slPi π 3 (p ^ f) K) : GL (Fin 3) K) = frobGL ψ s := by
  have h1 := hσψ ((conjSL hπ hh).symm s)
  rw [slAct_apply] at h1 ⊢
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, coe_conjSL]
  rw [h1, coe_conjSL_symm, map_mul, map_mul, map_inv, hhψ]
  group

theorem offdiag_eq_zero_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M : GL (Fin 3) K} (h : M * diagTau hτ = diagTau hτ * M) :
    ∀ i j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hdinj : Function.Injective (![τ, τ ^ 2, 1] : Fin 3 → K) := by
    have hv : (![τ, τ ^ 2, 1] : Fin 3 → K) = fun i => τ ^ ((i + 1 : Fin 3) : ℕ) := by
      funext i
      fin_cases i <;> simp
    rw [hv]
    exact (tau_pow_injective hτ hτ1).comp (add_left_injective 1)
  intro i j hij
  have h1 : ((M : Matrix (Fin 3) (Fin 3) K) *
      ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i j =
      (((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (M : Matrix (Fin 3) (Fin 3) K)) i j := by
    rw [← Units.val_mul, ← Units.val_mul, h]
  rw [coe_diagTau_eq_diagonal, mul_diagonal, diagonal_mul] at h1
  have hne : (![τ, τ ^ 2, 1] : Fin 3 → K) j - ![τ, τ ^ 2, 1] i ≠ 0 :=
    sub_ne_zero.mpr fun h' => hij (hdinj h').symm
  have h2 : (M : Matrix (Fin 3) (Fin 3) K) i j * ((![τ, τ ^ 2, 1] : Fin 3 → K) j -
      ![τ, τ ^ 2, 1] i) = 0 := by
    rw [mul_sub, h1]
    ring
  exact (mul_eq_zero.mp h2).resolve_right hne

theorem subGL_mulVec {S : Subfield K} (B : GL (Fin 3) S) (v : Fin 3 → S) :
    ((subGL S B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun r => (v r : K)) =
      fun r => (((B : Matrix (Fin 3) (Fin 3) S) *ᵥ v) r : K) := by
  rw [coe_subGL]
  funext r
  exact (RingHom.map_mulVec S.subtype _ v r).symm

theorem linearIndependent_subtype_of {S : Subfield K} {b : Fin 3 → (Fin 3 → S)}
    (hb : LinearIndependent S b) :
    LinearIndependent K (fun i => fun r => (b i r : K)) := by
  classical
  set P : Matrix (Fin 3) (Fin 3) S := Matrix.of fun r k => b k r with hP
  have hPu : IsUnit P := by
    have hcol : P.col = b := by
      funext i r
      rfl
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := P)).mp (hcol ▸ hb)
  have hPK : IsUnit (P.map S.subtype) := by
    rw [Matrix.isUnit_iff_isUnit_det] at hPu ⊢
    have hdet : (P.map S.subtype).det = S.subtype P.det := by
      rw [RingHom.map_det]
      rfl
    rw [hdet]
    exact hPu.map _
  have hcol : (P.map S.subtype).col = fun i => fun r => (b i r : K) := by
    funext i r
    rfl
  rw [← hcol]
  exact (Matrix.linearIndependent_cols_iff_isUnit).mpr hPK

omit [Finite G] hLn in
theorem card_le_nine_of_frame_sub (hK : PiField π p f K) (e : L ≃* slPi π 3 (p ^ f) K)
    {X : Subgroup G} (hXL : X ≤ L) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    {fr : Fin 3 → (Fin 3 → K)} (hfrli : LinearIndependent K fr)
    (hframe : ∀ x (hx : x ∈ X), ∀ i, ∃ c : K,
      ((e ⟨x, hXL hx⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = c • fr i) :
    Nat.card X ≤ 9 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hev : ∀ a : X, ∃ d : Fin 3 → K, ∀ i,
      ((e ⟨a, hXL a.2⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = d i • fr i := by
    intro a
    choose d hd using hframe a a.2
    exact ⟨d, hd⟩
  choose d hd using hev
  have hd3 : ∀ a i, d a i ^ 3 = 1 := by
    intro a i
    have h1 := pow_mulVec_of_eigen (hd a i) 3
    have h2 : ((e ⟨a, hXL a.2⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨a, hXL a.2⟩ : L) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, hX3 a a.2]; rfl)
      rw [this, map_one, Subgroup.coe_one, Units.val_one]
    rw [h2, Matrix.one_mulVec] at h1
    have := smul_left_injective K (hfrli.ne_zero i)
      (show (1 : K) • fr i = d a i ^ 3 • fr i by rw [one_smul]; exact h1)
    exact this.symm
  have hdet : ∀ a, d a 0 * d a 1 * d a 2 = 1 := by
    intro a
    rw [← det_eq_prod_of_eigen hfrli (hd a)]
    exact ((mem_slPi_iff hπ).mp (e ⟨a, hXL a.2⟩).2).2
  have hd0 : ∀ a i, d a i ≠ 0 := fun a i h0 => by
    have := hd3 a i
    rw [h0] at this
    norm_num at this
  let F : X → rootsOfUnity 3 K × rootsOfUnity 3 K := fun a =>
    (⟨Units.mk0 (d a 0) (hd0 a 0), (mem_rootsOfUnity 3 _).mpr (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd3, Units.val_one]))⟩,
    ⟨Units.mk0 (d a 1) (hd0 a 1), (mem_rootsOfUnity 3 _).mpr (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd3, Units.val_one]))⟩)
  have hFinj : Function.Injective F := by
    intro a a' haa'
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at haa'
    obtain ⟨h0, h1⟩ := haa'
    have e0 : d a 0 = d a' 0 := congrArg Units.val h0
    have e1 : d a 1 = d a' 1 := congrArg Units.val h1
    have e2 : d a 2 = d a' 2 := by
      have h01 : d a 0 * d a 1 ≠ 0 := mul_ne_zero (hd0 a 0) (hd0 a 1)
      have h' := hdet a'
      rw [← e0, ← e1] at h'
      exact mul_left_cancel₀ h01 ((hdet a).trans h'.symm)
    have hall : ∀ i, d a i = d a' i := by
      intro i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
    have heq := eq_of_mulVec_eq_of_linearIndependent hfrli (M := ((e ⟨a, hXL a.2⟩ :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (N := ((e ⟨a', hXL a'.2⟩ :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) fun i => by rw [hd, hd, hall i]
    have h3 : e ⟨a, hXL a.2⟩ = e ⟨a', hXL a'.2⟩ := Subtype.ext (Units.ext heq)
    have h4 : (a : G) = a' := congrArg (fun x : L => (x : G)) (e.injective h3)
    exact Subtype.ext h4
  have hle := Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_prod] at hle
  have h3 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
  have : Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) ≤ 9 :=
    (Nat.mul_le_mul h3 h3).trans (by norm_num)
  omega

omit [Finite G] in
theorem isTypeCOnSL_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A' : Subgroup G} (hpgl : ∀ a ∈ A', ∃ y, IsPGLAt e a y)
    (hexp : ∀ a ∈ A', a ^ 3 = 1) (hE9 : Nat.card (pglHom hK hq A' hpgl).range = 9)
    {fr : Fin 3 → (Fin 3 → K)} (hfrli : LinearIndependent K fr)
    (hframe : ∀ a ∈ A', ∀ y, IsPGLAt e a y → ∀ i, ∃ c : K,
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = c • fr i) : IsTypeCOnSL A' L := by
  set E := (pglHom hK hq A' hpgl).range with hEdef
  set D : Subgroup (GL (Fin 3) K) :=
    E.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hD
  have hDmap : D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = E := by
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      exact hd.1
    · rintro _ ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hpgl a a.2
      refine ⟨y, ⟨?_, hy.1⟩, ?_⟩
      · change (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E
        exact mk_mem_range_pglHom a.2 hy
      · rw [QuotientGroup.mk'_apply, pglHom_apply a hy]
  have hTC : IsTypeC π (p ^ f) K D := by
    refine ⟨inf_le_right, fun d hd => pow_three_mem_of_mk (range_pglHom_pow hexp _ hd.1), ?_,
      fr, hfrli, fun d hd i => ?_⟩
    · rw [hDmap]
      exact hE9
    · obtain ⟨a, ha, hy⟩ := exists_isPGLAt_of_mk_mem hd.2 hd.1
      exact hframe a ha d hy i
  refine ⟨fun x _ => mem_normalizer_of_normal x, π, p, f, K, inferInstance, hK, hq, e, D, hTC,
    fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy⟩ := hpgl x x.2
    refine ⟨y, ⟨mk_mem_range_pglHom x.2 hy, hy.1⟩, fun z => ?_⟩
    have := hy.2 (e z)
    rw [slAct_apply, MulEquiv.symm_apply_apply] at this
    exact this
  · obtain ⟨a, ha, hya⟩ := exists_isPGLAt_of_mk_mem hy.2 hy.1
    refine ⟨⟨a, ha⟩, fun z => ?_⟩
    have := hya.2 (e z)
    rw [slAct_apply, MulEquiv.symm_apply_apply] at this
    exact this

end FrameTools

section FourFrame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem subGL_diagTau {S : Subfield K} {τ₀ : S} (hτ₀ : τ₀ ^ 3 = 1) (hτ : (τ₀ : K) ^ 3 = 1) :
    subGL S (diagTau hτ₀) = diagTau hτ := by
  apply Units.ext
  rw [coe_subGL, coe_diagTau_eq_diagonal, coe_diagTau_eq_diagonal, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp

theorem fieldFour_frame (hG : SectionFourHyp G) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) {σ : G}
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    (hA81 : Nat.card A = 81)
    (hAeq : A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ)
    (hB27 : Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) = 27)
    (hBc : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers c)
    (hpglB : ∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)), ∃ y, IsPGLAt e b y)
    {S : Subfield K} (hS : ∀ c, c ∈ S ↔ φ c = c) (hS₀ : PiField π p f₀ S)
    (hfixB₀ : ∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)),
      ∃ y₀ : GL (Fin 3) S, IsPGLAt e b (subGL S y₀))
    {b₀ : Fin 3 → (Fin 3 → S)} (hb₀ : LinearIndependent S b₀)
    (hframe₀ : ∀ y₀ : GL (Fin 3) S, (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) ∈
      (pglHomSub S hK hq _ hfixB₀).range →
        ∀ i, ∃ c' : S, (y₀ : Matrix (Fin 3) (Fin 3) S) *ᵥ b₀ i = c' • b₀ i)
    {z₀ : GL (Fin 3) S}
    (hz₀ : (z₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) ∈ (pglHomSub S hK hq _ hfixB₀).range)
    {d : Fin 3 → S} (hd : Function.Injective d)
    (hz₀b : ∀ i, (z₀ : Matrix (Fin 3) (Fin 3) S) *ᵥ b₀ i = d i • b₀ i) :
    p = 2 ∧ π = false ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      IsTypeCOnSL (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) L := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hq₀ : ModThree π (p ^ f₀) :=
    modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  have hπ₀ : π = false → UnitaryFieldData p f₀ S := fun h => by subst h; exact hS₀.unitary
  have hq₀' : π = false → ModThree false (p ^ f₀) := fun h => by subst h; exact hq₀
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hS₀ hq₀
  have hSψ : ∀ c, c ∈ S ↔ ψ c = c := fun c => (hS c).trans (fixed_iff_of_sq hφ3 hψ c).symm
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B := A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) with hBdef
  set fr : Fin 3 → (Fin 3 → K) := fun i r => (b₀ i r : K) with hfr
  have hfrli : LinearIndependent K fr := linearIndependent_subtype_of hb₀
  have hframeK₀ : ∀ y₀ : GL (Fin 3) S, (y₀ : GL (Fin 3) S ⧸ StatedScalars (Fin 3) S) ∈
      (pglHomSub S hK hq B hfixB₀).range → ∀ i, ∃ c' : K,
        ((subGL S y₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = c' • fr i := by
    intro y₀ hy₀ i
    obtain ⟨c', hc'⟩ := hframe₀ y₀ hy₀ i
    refine ⟨(c' : K), ?_⟩
    rw [hfr, subGL_mulVec, hc']
    funext r
    simp
  have hframeK : ∀ b ∈ B, ∀ y, IsPGLAt e b y → ∀ i, ∃ c' : K,
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ fr i = c' • fr i := by
    intro b hb y hy i
    obtain ⟨y₀, hy₀⟩ := hfixB₀ b hb
    obtain ⟨c', hc'⟩ := hframeK₀ y₀ (mk_mem_range_pglHomSub hb hy₀) i
    obtain ⟨μ, hμ⟩ := isPGLAt_inv_mul_mem hK hq hy₀ hy
    have hyμ : y = subGL S y₀ * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
    refine ⟨c' * μ, ?_⟩
    rw [hyμ, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, hc', smul_smul, mul_comm]
  obtain ⟨b', hb'B, y₀', hy₀', u, hz₀eq⟩ := exists_of_mk_mem_range_pglHomSub hz₀
  have hy₀'z : y₀' = z₀ * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
    rw [hz₀eq, map_inv]
    group
  have hy₀'b : ∀ i, (y₀' : Matrix (Fin 3) (Fin 3) S) *ᵥ b₀ i =
      (((u⁻¹ : Sˣ) : S) * d i) • b₀ i := by
    intro i
    rw [hy₀'z, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, hz₀b, smul_smul]
  have hd' : Function.Injective fun i => ((u⁻¹ : Sˣ) : S) * d i := fun i j h =>
    hd (mul_left_cancel₀ (Units.ne_zero _) h)
  have hy₀'H : y₀' ∈ glPi π 3 (p ^ f₀) S := (subGL_mem_glPi_iff hK hf hφ hS hS₀ _).mp hy₀'.1
  have hy₀'3 : y₀' ^ 3 ∈ zPi π 3 (p ^ f₀) S := by
    rw [zPi_eq hπ₀ hq₀' hτ₀ hτ₀1]
    refine Subgroup.mem_inf.mpr ⟨pow_mem hy₀'H 3, mem_statedScalars_of_subGL S ?_⟩
    rw [map_pow]
    exact mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPi hK hq (hA.1.2 b' hb'B.1) hy₀')
  obtain ⟨τ₁, hτ₁, hτ₁1, w₀, hw₀, g₀, hg₀, hD⟩ :=
    type1_of_regular hS₀ hq₀ hy₀'H hy₀'3 hb₀ hd' hy₀'b
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, l₀ = y₀' * w₀ := ⟨_, rfl⟩
  have hl₀eq : l₀ = g₀ * diagTau hτ₁ * g₀⁻¹ := by rw [hl₀]; exact eq_conj_of_inv_conj hD
  have hl₀L : l₀ ∈ slPi π 3 (p ^ f₀) S := by
    rw [hl₀eq]
    exact conj_mem_slPi hπ₀ hg₀ (diagTau_mem_slPi hπ₀ hq₀' hτ₁)
  have hl₀3 : l₀ ^ 3 = 1 := by
    rw [hl₀eq, conj_pow, diagTau_pow_three hτ₁, mul_one, mul_inv_cancel]
  obtain ⟨μ₀, hμ₀⟩ := mem_statedScalars_of_mem_zPi hS₀ hq₀ hτ₀ hτ₀1 hw₀
  have hl₀b : ∀ i, (l₀ : Matrix (Fin 3) (Fin 3) S) *ᵥ b₀ i =
      ((((u⁻¹ : Sˣ) : S) * d i) * μ₀) • b₀ i := by
    intro i
    rw [hl₀, ← hμ₀, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, hy₀'b, smul_smul,
      mul_comm _ (μ₀ : S)]
  have hcommB : ∀ b ∈ B, ∀ y₀ : GL (Fin 3) S, IsPGLAt e b (subGL S y₀) → y₀ * l₀ = l₀ * y₀ := by
    intro b hb y₀ hy₀
    choose cc hcc using hframe₀ y₀ (mk_mem_range_pglHomSub hb hy₀)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_eigen hb₀ hcc hl₀b
  have hlL : subGL S l₀ ∈ slPi π 3 (p ^ f) K := (subGL_mem_slPi_iff hK hf hφ hS hS₀ _).mpr hl₀L
  obtain ⟨v, hv⟩ : ∃ v : L, v = e.symm ⟨subGL S l₀, hlL⟩ := ⟨_, rfl⟩
  have hev : ((e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = subGL S l₀ := by
    rw [hv, MulEquiv.apply_symm_apply]
  have hvσ : σ * (v : G) = v * σ := by
    rw [hv]
    apply commute_of_slAct_eq
    apply Subtype.ext
    rw [hσψ]
    exact frobGL_subGL hSψ l₀
  have hvB : ∀ b ∈ B, b * (v : G) = v * b := by
    intro b hb
    obtain ⟨y₀, hy₀⟩ := hfixB₀ b hb
    rw [hv]
    apply commute_of_slAct_eq
    apply Subtype.ext
    rw [hy₀.2]
    change subGL S y₀ * subGL S l₀ * (subGL S y₀)⁻¹ = subGL S l₀
    rw [← map_mul, ← map_inv, ← map_mul, hcommB b hb y₀ hy₀, mul_inv_cancel_right]
  have hvA : ∀ a ∈ A, a * (v : G) = v * a := by
    intro a ha
    have ha' : a ∈ B ⊔ Subgroup.zpowers σ := hAeq ▸ ha
    refine commute_sup_of_commute hvB (fun x hx => ?_) a ha'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute σ (v : G) from hvσ) k).eq
  have hv3 : (v : G) ^ 3 = 1 := by
    have : e v ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hev, ← map_pow, hl₀3, map_one]
      rfl)
    rw [← map_pow, map_eq_one_iff _ e.injective] at this
    exact congrArg Subtype.val this
  have hvAm : (v : G) ∈ A := mem_of_maximal_of_commute hA hv3 hvA
  have hvc : (v : G) ∉ Subgroup.zpowers c := by
    intro h
    have hvC : (v : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [← hLC] at h
      exact h.2
    have hs := mem_statedScalars_of_mem_inf hK hq (e := e) hvC
    rw [hev] at hs
    obtain ⟨t, ht⟩ := mem_statedScalars_of_subGL S hs
    apply diagTau_not_mem_statedScalars hτ₁ hτ₁1
    refine ⟨t, ?_⟩
    have hct := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t g₀⁻¹).eq
    calc GeneralLinearGroup.scalar (Fin 3) t =
        GeneralLinearGroup.scalar (Fin 3) t * g₀⁻¹ * g₀ := by group
      _ = g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) t * g₀ := by rw [← hct]
      _ = g₀⁻¹ * l₀ * g₀ := by rw [ht]
      _ = diagTau hτ₁ := by rw [hl₀eq]; group
  have hcv9 := card_zpowers_sup_zpowers hv3 hc3 hvc
    ((Subgroup.mem_centralizer_iff.mp hcAC.2) v v.2)
  have hcvle : Subgroup.zpowers c ⊔ Subgroup.zpowers (v : G) ≤ A ⊓ L :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hcAC.1, hcL⟩) (Subgroup.zpowers_le.mpr ⟨hvAm, v.2⟩)
  have hALle : Nat.card (A ⊓ L : Subgroup G) ≤ 9 :=
    card_le_nine_of_frame_sub hK e (X := A ⊓ L) inf_le_right (fun x hx => hA.1.2 x hx.1) hfrli
      (fun x hx i => hframeK x ⟨hx.1, Subgroup.mem_sup_left hx.2⟩ _
        (isPGLAt_of_mem e hπ hx.2) i)
  have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    le_antisymm hALle (hcv9 ▸ Subgroup.card_le_of_le hcvle)
  have hcardB := card_eq_card_inf_mul_card_range (L := L) (e := e) (hK := hK) (hq := hq)
    (A' := B) (hA' := hpglB)
  rw [hBc, Nat.card_zpowers, hc3, hB27] at hcardB
  have hE9 : Nat.card (pglHom hK hq B hpglB).range = 9 := by omega
  have hTC := isTypeCOnSL_of_frame hK hq e hpglB (fun b hb => hA.1.2 b hb.1) hE9 hfrli hframeK
  have hgK : subGL S g₀ ∈ glPi π 3 (p ^ f) K := (subGL_mem_glPi_iff hK hf hφ hS hS₀ _).mpr hg₀
  have hσψ' := slAct_trans_conjSL_of_fixed hπ hgK hσψ (frobGL_subGL hSψ g₀)
  have hτK : ((τ₁ : S) : K) ^ 3 = 1 := by
    rw [← SubmonoidClass.coe_pow, hτ₁]
    rfl
  have hτK1 : ((τ₁ : S) : K) ≠ 1 := fun h => hτ₁1 (Subtype.val_injective h)
  have hD' : diagTau hτK = (subGL S g₀)⁻¹ * subGL S l₀ * subGL S g₀ := by
    rw [← subGL_diagTau hτ₁ hτK, hl₀eq, map_mul, map_mul, map_inv]
    group
  have hgen : A ≤ Subgroup.closure (diagOrFrob (e.trans (conjSL hπ hgK)) σ) := by
    calc A = B ⊔ Subgroup.zpowers σ := hAeq
      _ ≤ _ := by
        refine sup_le (fun b hb => Subgroup.subset_closure (Or.inl ?_))
          (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr rfl)))
        obtain ⟨y₀, hy₀⟩ := hfixB₀ b hb
        refine ⟨(subGL S g₀)⁻¹ * subGL S y₀ * subGL S g₀, isPGLAt_trans_conjSL hπ hgK hy₀, ?_⟩
        apply offdiag_eq_zero_of_commute_diagTau hτK hτK1
        rw [hD']
        have hc0 : subGL S y₀ * subGL S l₀ = subGL S l₀ * subGL S y₀ := by
          rw [← map_mul, ← map_mul, hcommB b hb y₀ hy₀]
        calc (subGL S g₀)⁻¹ * subGL S y₀ * subGL S g₀ *
              ((subGL S g₀)⁻¹ * subGL S l₀ * subGL S g₀) =
            (subGL S g₀)⁻¹ * (subGL S y₀ * subGL S l₀) * subGL S g₀ := by group
          _ = (subGL S g₀)⁻¹ * (subGL S l₀ * subGL S y₀) * subGL S g₀ := by rw [hc0]
          _ = _ := by group
  obtain ⟨hp2, hπf⟩ := two_and_unitary_of_rank_four hG hK _ hσψ' hA.1 hA81 hgen
  exact ⟨hp2, hπf, hAL9, hTC⟩

end FourFrame

section FourMain

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem alt411_field_four (hG : SectionFourHyp G) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) [Group.IsPerfect L]
    (hθ : aschbacherSolvableCore 3 L = ⊥) {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    {σ : G} (hσA : σ ∈ A) (hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσkind : InducesStdKind L σ .field)
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    (hA81 : Nat.card A = 81) : Alt411 L A c := by
  classical
  obtain ⟨hfixB, hAeq, -, hcard, hBc, -⟩ :=
    fieldB_structure hK hq hq2 hθ hf hφ hφ3 hψ e hA hc3 hAc hσA hσB hσψ
  set B := A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) with hBdef
  have hB27 : Nat.card B = 27 := by omega
  obtain ⟨S, hS, hScard⟩ := exists_fixedField hK hf hφ3
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have hS₀ : PiField π p f₀ S := ⟨hK.prime, hf₀, hScard⟩
  have hq₀ : ModThree π (p ^ f₀) :=
    modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hS₀ hq₀
  have h3₀ := hS₀.three_ne_zero hq₀
  have hpglB : ∀ b ∈ B, ∃ y, IsPGLAt e b y := fun b hb =>
    ⟨_, (hfixB b hb).choose_spec.1⟩
  have hfixB₀ : ∀ b ∈ B, ∃ y₀ : GL (Fin 3) S, IsPGLAt e b (subGL S y₀) := by
    intro b hb
    obtain ⟨y, hy, hyψ⟩ := hfixB b hb
    have hyφ : frobGL φ y = y := by
      apply Units.ext
      have := congrArg Units.val hyψ
      rw [coe_frobGL] at this ⊢
      ext i k
      have h := congrFun (congrFun this i) k
      simp only [Matrix.map_apply] at h ⊢
      exact (fixed_iff_of_sq hφ3 hψ _).mp h
    obtain ⟨y₀, rfl⟩ := exists_subGL_eq hS hyφ
    exact ⟨y₀, hy⟩
  have hcardB := card_eq_card_inf_mul_card_range_sub (S := S) (L := L) (e := e) (hK := hK)
    (hq := hq) (A' := B) (hA' := hfixB₀)
  rw [hBc, Nat.card_zpowers, hc3, hB27] at hcardB
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
  rcases frame_or_heis h3₀ hτ₀ hτ₀1 (pglHomSub S hK hq B hfixB₀).range
      (range_pglHomSub_comm hBcomm) (range_pglHomSub_pow fun b hb => hA.1.2 b hb.1)
      (by omega) with
    ⟨b₀, hb₀, hframe₀, z₀, hz₀, d, hd, hz₀b⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ₀, hζ1, hζ⟩
  · obtain ⟨hp2, hπf, hAL9, hTC⟩ := fieldFour_frame hG hK hq hf hφ hφ3 hψ e hA hc3 hAc hσψ
      hA81 hAeq hB27 hBc hpglB hS hS₀ hfixB₀ hb₀ hframe₀ hz₀ hd hz₀b
    subst hp2
    subst hπf
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hA81, σ, hσA, hσkind,
      ⟨f, odd_of_two_pow_mod_three hq, K, inferInstance, hK.finite, hK.card, ⟨e⟩⟩, hB27,
      Or.inl ⟨hAL9, hTC⟩⟩))))
  · have hY₁ := mk_subGL_mem_range_pglHom (hA'' := hpglB) hy₁
    have hY₂ := mk_subGL_mem_range_pglHom (hA'' := hpglB) hy₂
    have hζK : (Units.map (S.subtype : S →* K) ζ₀) ≠ 1 := by
      intro h
      apply hζ1
      apply Units.ext
      have := congrArg Units.val h
      exact Subtype.val_injective (by simpa using this)
    have hζ' : subGL S y₁ * subGL S y₂ * (subGL S y₁)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) (Units.map (S.subtype : S →* K) ζ₀) * subGL S y₂ := by
      rw [← map_inv, ← map_mul, ← map_mul, hζ, map_mul, subGL_scalar]
    obtain ⟨hp2, hπf, hHeis⟩ := fieldFour_heis hG hK hq hf hφ hφ3 hψ e hA hc3 hAc hσA hσB hσψ
      hB27 hBc hpglB hY₁ hY₂ hζK hζ'
    subst hp2
    subst hπf
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hA81, σ, hσA, hσkind,
      ⟨f, odd_of_two_pow_mod_three hq, K, inferInstance, hK.finite, hK.card, ⟨e⟩⟩, hB27,
      Or.inr hHeis⟩))))

end FourMain

end CFSG.RankThree.PartTwo.Sec4
