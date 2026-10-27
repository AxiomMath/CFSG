module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeB

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nBL_scale_lin {p : ℕ} [Fact p.Prime] {E V : Type} [Group E] [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive E ≃+ V) (φ : MulAut E) (α : Module.Dual (ZMod p) V)
    (h : V) (μ : (ZMod p)ˣ)
    (hlin : ∀ v, ggLin (p := p) ι φ v = v - α v • h) (v : V) :
    ggLin (p := p) ι φ v = v - ((↑(μ⁻¹) : ZMod p) • α) v • ((μ : ZMod p) • h) := by
  rw [hlin v]
  congr 1
  rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  calc α v = α v * 1 := (mul_one _).symm
    _ = α v * ((↑(μ⁻¹) : ZMod p) * (μ : ZMod p)) := by rw [Units.inv_mul, mul_one]
    _ = ((↑(μ⁻¹) : ZMod p) * α v) * (μ : ZMod p) := by ring

theorem l05nBL_pair_inl_inr {p : ℕ} [Fact p.Prime] {Jn La : Type} [Fintype Jn]
    [DecidableEq Jn] [Fintype La] [DecidableEq La] {MK : CoxeterMatrix (Jn ⊕ La)}
    {CK0 : Matrix (Jn ⊕ La) (Jn ⊕ La) ℤ} (hCKK : GGIntCartan MK CK0)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {αL : Jn → Module.Dual (ZMod p) V}
    {αK : Jn ⊕ La → Module.Dual (ZMod p) V} {hK : Jn ⊕ La → V} {cc : Jn → (ZMod p)ˣ}
    (hαK : ∀ j, αK (Sum.inl j) = (↑((cc j)⁻¹) : ZMod p) • αL j)
    (hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p))
    {μ : La → (ZMod p)ˣ}
    (hμ : ∀ a j, MK.M (Sum.inr a) (Sum.inl j) ≠ 2 → μ a = (cc j)⁻¹)
    (i : Jn) (a : La) :
    αL i ((μ a : ZMod p) • hK (Sum.inr a)) =
      (CK0 (Sum.inl i) (Sum.inr a) : ZMod p) := by
  have h1 : αK (Sum.inl i) (hK (Sum.inr a)) = (CK0 (Sum.inl i) (Sum.inr a) : ZMod p) :=
    hpairK _ _
  rw [hαK i, LinearMap.smul_apply, smul_eq_mul] at h1
  rw [map_smul, smul_eq_mul]
  by_cases hm : MK.M (Sum.inl i) (Sum.inr a) = 2
  · have h0 : CK0 (Sum.inl i) (Sum.inr a) = 0 :=
      (l05nBL_cartan_eq_zero_iff hCKK (by simp)).2 hm
    have hx : αL i (hK (Sum.inr a)) = 0 := by
      rw [h0, Int.cast_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero ((cc i)⁻¹))
    rw [hx, mul_zero, h0, Int.cast_zero]
  · have hm' : MK.M (Sum.inr a) (Sum.inl i) ≠ 2 := by
      rwa [MK.symmetric (Sum.inr a) (Sum.inl i)]
    rw [hμ a i hm']
    exact h1

theorem l05nBL_pair_inr_inl {p : ℕ} [Fact p.Prime] {Jn La : Type} [Fintype Jn]
    [DecidableEq Jn] [Fintype La] [DecidableEq La] {MK : CoxeterMatrix (Jn ⊕ La)}
    {CK0 : Matrix (Jn ⊕ La) (Jn ⊕ La) ℤ} (hCKK : GGIntCartan MK CK0)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {hL : Jn → V}
    {αK : Jn ⊕ La → Module.Dual (ZMod p) V} {hK : Jn ⊕ La → V} {cc : Jn → (ZMod p)ˣ}
    (hhK : ∀ j, hK (Sum.inl j) = (cc j : ZMod p) • hL j)
    (hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p))
    {μ : La → (ZMod p)ˣ}
    (hμ : ∀ a j, MK.M (Sum.inr a) (Sum.inl j) ≠ 2 → μ a = (cc j)⁻¹)
    (a : La) (j : Jn) :
    ((↑((μ a)⁻¹) : ZMod p) • αK (Sum.inr a)) (hL j) =
      (CK0 (Sum.inr a) (Sum.inl j) : ZMod p) := by
  have h1 : αK (Sum.inr a) (hK (Sum.inl j)) =
      (CK0 (Sum.inr a) (Sum.inl j) : ZMod p) := hpairK _ _
  rw [hhK j, map_smul, smul_eq_mul] at h1
  rw [LinearMap.smul_apply, smul_eq_mul]
  by_cases hm : MK.M (Sum.inr a) (Sum.inl j) = 2
  · have h0 : CK0 (Sum.inr a) (Sum.inl j) = 0 :=
      (l05nBL_cartan_eq_zero_iff hCKK (by simp)).2 hm
    have hx : αK (Sum.inr a) (hL j) = 0 := by
      rw [h0, Int.cast_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero (cc j))
    rw [hx, mul_zero, h0, Int.cast_zero]
  · rw [hμ a j hm]
    simpa using h1

theorem l05nBL_pair_inr_inr {p : ℕ} [Fact p.Prime] {Jn La : Type} [Fintype Jn]
    [DecidableEq Jn] [Fintype La] [DecidableEq La] {MK : CoxeterMatrix (Jn ⊕ La)}
    {CK0 : Matrix (Jn ⊕ La) (Jn ⊕ La) ℤ} (hCKK : GGIntCartan MK CK0)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {αK : Jn ⊕ La → Module.Dual (ZMod p) V} {hK : Jn ⊕ La → V}
    (hpairK : ∀ o o', αK o (hK o') = (CK0 o o' : ZMod p))
    {μ : La → (ZMod p)ˣ}
    (hμa : ∀ a a', a ≠ a' → MK.M (Sum.inr a) (Sum.inr a') ≠ 2 → μ a = μ a')
    (a a' : La) :
    ((↑((μ a)⁻¹) : ZMod p) • αK (Sum.inr a)) ((μ a' : ZMod p) • hK (Sum.inr a')) =
      (CK0 (Sum.inr a) (Sum.inr a') : ZMod p) := by
  rw [LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul]
  have h1 := hpairK (Sum.inr a) (Sum.inr a')
  by_cases haa : a = a'
  · subst haa
    rw [← mul_assoc, Units.inv_mul, one_mul]
    exact h1
  · by_cases hm : MK.M (Sum.inr a) (Sum.inr a') = 2
    · have h0 : CK0 (Sum.inr a) (Sum.inr a') = 0 :=
        (l05nBL_cartan_eq_zero_iff hCKK (by simpa using haa)).2 hm
      rw [h0, Int.cast_zero] at h1 ⊢
      rw [h1, mul_zero, mul_zero]
    · rw [hμa a a' haa hm]
      rw [← mul_assoc, Units.inv_mul, one_mul]
      exact h1

@[expose] def l05nBL_DatumK {G : Type} [Group G] (k : ℕ) (p : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (S : Finset Λ) (Λa : Type) (_ : Fintype Λa)
    (_ : DecidableEq Λa) (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V) (α : Λ ⊕ Λa → Module.Dual (ZMod p) V),
    2 ≤ S.card ∧ S.card ≤ 3 ∧ Nat.card Λa = k ∧
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
      (∀ o, GGIsReflection p (φ o)) ∧
      (∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p)) ∧
      (∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
        α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i)) ∧
      (∃ fK : MK.Group ≃* ↥(ggAutomizer K Bs),
        ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id)) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
          Set.range fun a : Λa => φ (Sum.inr a)) ∧
      GGDeletedConnectedS ML S ∧
      ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))

theorem l05nBL_DatumK.toDatum {G : Type} [Group G] {k : ℕ} {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (hD : l05nBL_DatumK k p Bs L J K) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS1, hS2, hcard, hWML, hCLL, hWMK, hCKK, hlin, hrefl, hpairLL, hpairCK, hfL, hfK,
    hclosL, hclosK, hdel, hclosJL⟩ := hD
  refine ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS1, hS2, ?_, ?_, hWML, hCLL, hWMK, hCKK, trivial, hlin, hrefl, hpairLL, hpairCK, trivial,
    hfL, hfK, hclosL, hclosK, hdel, hclosJL⟩
  · omega
  · omega

theorem l05nBL_datum {G : Type} [Group G] [Finite G] {k : ℕ} {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (D : l05nBL_Al k p Bs L J K) :
    l05nBL_DatumK k p Bs L J K := by
  letI := D.fin
  letI := D.dec
  letI := D.fina
  letI := D.deca
  letI := D.acg
  letI := D.mod
  obtain ⟨μ, hμJ, hμa⟩ :=
    l05nBL_mu (U := (ZMod p)ˣ) (M := D.MK) (C := D.CK0)
      D.hWMK D.hCKK (by
        intro i j
        simpa only [D.hMJL, D.hord] using ggRC_weyl_connected D.hWMJL i j)
      D.cc
  let CK : Matrix ({i : D.Λ // i ∉ D.S} ⊕ D.Λa)
      ({i : D.Λ // i ∉ D.S} ⊕ D.Λa) ℤ :=
    fun o o' => match o, o' with
      | Sum.inl i, Sum.inl j => D.CL i.1 j.1
      | _, _ => D.CK0 o o'
  let φ : D.Λ ⊕ D.Λa → MulAut ↥Bs := fun o =>
    match o with
    | Sum.inl i => D.φL i
    | Sum.inr a => D.φK (Sum.inr a)
  let h : D.Λ ⊕ D.Λa → D.V := fun o =>
    match o with
    | Sum.inl i => D.hL i
    | Sum.inr a => (μ a : ZMod p) • D.hK (Sum.inr a)
  let α : D.Λ ⊕ D.Λa → Module.Dual (ZMod p) D.V := fun o =>
    match o with
    | Sum.inl i => D.αL i
    | Sum.inr a => (↑((μ a)⁻¹) : ZMod p) • D.αK (Sum.inr a)
  have hCK : GGIntCartan D.MK CK := by
    constructor
    · intro o
      cases o with
      | inl i => exact D.hCLL.1 i.1
      | inr a => exact D.hCKK.1 (Sum.inr a)
    · intro o o' hne
      cases o with
      | inl i =>
        cases o' with
        | inl j =>
          have hij : i ≠ j := fun h => hne (by rw [h])
          have h := D.hCLL.2 i.1 j.1 (fun hh => hij (Subtype.ext hh))
          rw [show D.MK.M (Sum.inl i) (Sum.inl j) = D.ML.M i.1 j.1 from D.hord i j]
          exact h
        | inr a => exact D.hCKK.2 (Sum.inl i) (Sum.inr a) (by simp)
      | inr a =>
        cases o' with
        | inl j => exact D.hCKK.2 (Sum.inr a) (Sum.inl j) (by simp)
        | inr a' => exact D.hCKK.2 (Sum.inr a) (Sum.inr a') (by simpa using hne)
  have hlin : ∀ o w, ggLin (p := p) D.ι (φ o) w = w - α o w • h o := by
    intro o w
    cases o with
    | inl i => exact D.hlinL i w
    | inr a =>
      exact l05nBL_scale_lin (p := p) D.ι (D.φK (Sum.inr a)) (D.αK (Sum.inr a))
        (D.hK (Sum.inr a)) (μ a) (D.hlinK (Sum.inr a)) w
  have hrefl : ∀ o, GGIsReflection p (φ o) := by
    intro o
    cases o with
    | inl i => exact D.hreflL i
    | inr a => exact D.hreflK (Sum.inr a)
  have hpairLL : ∀ i j : D.Λ, α (Sum.inl i) (h (Sum.inl j)) = (D.CL i j : ZMod p) :=
    fun i j => D.hpairL i j
  have hpairCK : ∀ o o' : {i : D.Λ // i ∉ D.S} ⊕ D.Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p) := by
    intro o o'
    cases o with
    | inl i =>
      cases o' with
      | inl j => exact D.hpairL i.1 j.1
      | inr a => exact l05nBL_pair_inl_inr D.hCKK D.hαK D.hpairK hμJ i a
    | inr a =>
      cases o' with
      | inl j => exact l05nBL_pair_inr_inl D.hCKK D.hhK D.hpairK hμJ a j
      | inr a' => exact l05nBL_pair_inr_inr D.hCKK D.hpairK hμa a a'
  have hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : D.Λ // j ∉ D.S} => φ (Sum.inl j)) ∪
        Set.range fun a : D.Λa => φ (Sum.inr a)) := by
    rw [D.hclosK]
    congr 1
    ext γ
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, (D.hφK j).symm⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, D.hφK j⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hdel : GGDeletedConnectedS D.ML D.S := by
    intro i j
    simpa only [D.hMJL] using ggRC_weyl_connected D.hWMJL i j
  have hfK' : ∀ o : {i : D.Λ // i ∉ D.S} ⊕ D.Λa,
      (D.fK (D.MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id) := by
    intro o
    rw [D.hfK o]
    cases o with
    | inl j => rw [D.hφK j]; rfl
    | inr a => rfl
  refine ⟨D.Λ, D.fin, D.dec, D.S, D.Λa, D.fina, D.deca, D.ML, D.CL, D.MK, CK,
    D.V, D.acg, D.mod, D.ι, φ, h, α, D.hS1, D.hS2, D.hk, D.hWML, D.hCLL, D.hWMK, hCK,
    hlin, hrefl, hpairLL, hpairCK, ⟨D.fL, fun i => D.hfL i⟩,
    ⟨D.fK, hfK'⟩, D.hclosL, hclosK, hdel, D.hclosJL⟩

end CFSG.StandardType

end
