module

public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQ2P3HeartSel {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs L : Subgroup G)
    (x : G) : Prop :=
  ∃ M : GGQ2LDatum p Bs L x, M.xV ∉ M.coSpan ∧
    M.coSpan ⊔ Submodule.span (ZMod p) {M.xV} = ⊤ ∧
    ∀ g ∈ Subgroup.normalizer (Bs : Set G),
      ∃ r ∈ Subgroup.closure {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ},
        ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧ ∀ φ ρ : MulAut ↥Bs, GGQ2Ind Bs g φ → GGQ2Ind Bs r ρ →
          ∀ h ∈ M.coSpan, ggLin (p := p) M.model φ h = ε • ggLin (p := p) M.model ρ h

@[expose] def GGQ2P3OffI1RestInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      4 ∣ Nat.card (ggAutomizer J Bs) → ¬ GGQ2ReflAbsIrred p Bs →
      ¬ GGQ2P3HeartSel p Bs L x → GGQ2P3 p Bs x

@[expose] def GGQ2P3OffI1HeartCell : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      4 ∣ Nat.card (ggAutomizer J Bs) → ¬ GGQ2ReflAbsIrred p Bs →
      GGQ2P3HeartSel p Bs L x → GGQ2P3 p Bs x

private structure GGQ2P3HeartData (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] where
  three : (3 : K) = 0
  two_ne : (2 : K) ≠ 0
  units : ∀ a : K, a ≠ 0 → a = 1 ∨ a = -1
  H : Submodule K V
  x : V
  hxH : x ∉ H
  hsplit : H ⊔ Submodule.span K {x} = ⊤
  P : (V ≃ₗ[K] V) → Prop
  P_mul : ∀ S T, P S → P T → P (S * T)
  P_inv : ∀ T, P T → P T⁻¹
  noTv : ∀ T, P T → ∀ (f : Module.Dual K V) (w : V), w ≠ 0 → f ≠ 0 → f w = 0 →
    ¬ ∀ v, T v = v + f v • w
  s : ι → (V ≃ₗ[K] V)
  P_s : ∀ i, P (s i)
  α : ι → Module.Dual K V
  c : ι → V
  c_mem : ∀ i, c i ∈ H
  α_c : ∀ i, α i (c i) = 2
  s_apply : ∀ i v, s i v = v - α i v • c i
  s_x : ∀ i, s i x = x
  fix : ∀ z, (∀ i, s i z = z) → z ∈ Submodule.span K {x}

section Core

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]

private theorem ggQ2p3h_apply_inv (T : V ≃ₗ[K] V) (v : V) : T (T⁻¹ v) = v := by
  simp

private theorem ggQ2p3h_inv_apply (T : V ≃ₗ[K] V) (v : V) : T⁻¹ (T v) = v := by
  simp

private theorem ggQ2p3h_c_ne (D : GGQ2P3HeartData K V ι) (i : ι) : D.c i ≠ 0 := by
  intro h
  have h2 := D.α_c i
  rw [h, map_zero] at h2
  exact D.two_ne h2.symm

private theorem ggQ2p3h_s_s (D : GGQ2P3HeartData K V ι) (i : ι) (v : V) :
    D.s i (D.s i v) = v := by
  have h1 := D.s_apply i v
  have h2 := D.s_apply i (D.s i v)
  have h3 : D.α i (D.s i v) = -D.α i v := by
    rw [h1, map_sub, map_smul, D.α_c, smul_eq_mul]
    ring
  rw [h2, h3]
  nth_rewrite 1 [h1]
  module

private theorem ggQ2p3h_s_inv (D : GGQ2P3HeartData K V ι) (i : ι) (v : V) :
    (D.s i)⁻¹ v = D.s i v := by
  have h := ggQ2p3h_inv_apply (D.s i) (D.s i v)
  rwa [ggQ2p3h_s_s D i v] at h

private theorem ggQ2p3h_s_mem (D : GGQ2P3HeartData K V ι) (i : ι) {h : V} (hh : h ∈ D.H) :
    D.s i h ∈ D.H := by
  rw [D.s_apply]
  exact D.H.sub_mem hh (D.H.smul_mem _ (D.c_mem i))

private theorem ggQ2p3h_proj (D : GGQ2P3HeartData K V ι) :
    ∃ π : Module.Dual K V, π D.x = 1 ∧ (∀ h ∈ D.H, π h = 0) ∧ ∀ v, v - π v • D.x ∈ D.H := by
  obtain ⟨f, hfx, hfH⟩ := Submodule.exists_le_ker_of_notMem D.hxH
  refine ⟨(f D.x)⁻¹ • f, ?_, ?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfx]
  · intro h hh
    have : f h = 0 := LinearMap.mem_ker.mp (hfH hh)
    rw [LinearMap.smul_apply, this, smul_zero]
  · intro v
    have hv : v ∈ D.H ⊔ Submodule.span K {D.x} := by rw [D.hsplit]; trivial
    obtain ⟨h, hh, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hfh : f h = 0 := LinearMap.mem_ker.mp (hfH hh)
    have hπ : ((f D.x)⁻¹ • f) (h + c • D.x) = c := by
      have e : f (h + c • D.x) = c * f D.x := by
        rw [map_add, map_smul, hfh, zero_add, smul_eq_mul]
      rw [LinearMap.smul_apply, e, smul_eq_mul, mul_comm c, inv_mul_cancel_left₀ hfx]
    rw [hπ]
    simpa using hh

private theorem ggQ2p3h_k0a (D : GGQ2P3HeartData K V ι) {T : V ≃ₗ[K] V} (hT : D.P T)
    (hH : ∀ h ∈ D.H, T h = h) {b : V} (hb : b ∈ D.H) (hx : T D.x = D.x + b) : b = 0 := by
  by_contra hb0
  obtain ⟨π, hπx, hπH, hπv⟩ := ggQ2p3h_proj D
  have hform : ∀ v, T v = v + π v • b := by
    intro v
    have e : T (v - π v • D.x) = v - π v • D.x := hH _ (hπv v)
    have e2 : T v = T (v - π v • D.x) + π v • T D.x := by
      calc T v = T ((v - π v • D.x) + π v • D.x) := by rw [sub_add_cancel]
        _ = T (v - π v • D.x) + π v • T D.x := by rw [map_add, map_smul]
    rw [e2, e, hx]
    module
  refine D.noTv T hT π b hb0 ?_ (hπH b hb) hform
  intro h0
  rw [h0] at hπx
  simp at hπx

private theorem ggQ2p3h_k0 (D : GGQ2P3HeartData K V ι) {T : V ≃ₗ[K] V} (hT : D.P T)
    (hH : ∀ h ∈ D.H, T h = h) : T D.x = D.x ∨ T D.x = -D.x := by
  obtain ⟨π, hπx, hπH, hπv⟩ := ggQ2p3h_proj D
  set l := π (T D.x) with hl
  set b := T D.x - l • D.x with hb
  have hbH : b ∈ D.H := hπv _
  have hTx : T D.x = l • D.x + b := by rw [hb]; abel
  have hTb : T b = b := hH b hbH
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hTx
    have hxb : D.x = b := T.injective (by rw [hTx, hTb])
    exact D.hxH (hxb ▸ hbH)
  rcases D.units l hl0 with h1 | h1
  · left
    rw [h1, one_smul] at hTx
    have hb0 := ggQ2p3h_k0a D hT hH hbH hTx
    rw [hTx, hb0, add_zero]
  · right
    rw [h1] at hTx
    replace hTx : T D.x = -D.x + b := by rw [hTx]; module
    have hsb : ∀ i, D.s i b = b := by
      intro i
      have hk : D.P (D.s i * T * (D.s i)⁻¹ * T⁻¹) :=
        D.P_mul _ _ (D.P_mul _ _ (D.P_mul _ _ (D.P_s i) hT) (D.P_inv _ (D.P_s i)))
          (D.P_inv _ hT)
      have hkH : ∀ h ∈ D.H, (D.s i * T * (D.s i)⁻¹ * T⁻¹) h = h := by
        intro h hh
        have e1 : T⁻¹ h = h := by
          have h0 := ggQ2p3h_inv_apply T h
          rwa [hH h hh] at h0
        have e2 : T (D.s i h) = D.s i h := hH _ (ggQ2p3h_s_mem D i hh)
        show D.s i (T ((D.s i)⁻¹ (T⁻¹ h))) = h
        rw [e1, ggQ2p3h_s_inv, e2, ggQ2p3h_s_s]
      have hbs : b - D.s i b ∈ D.H := D.H.sub_mem hbH (ggQ2p3h_s_mem D i hbH)
      have hTinv : T⁻¹ D.x = b - D.x := by
        have h0 : T (b - D.x) = D.x := by
          rw [map_sub, hTb, hTx]; abel
        have h1 := ggQ2p3h_inv_apply T (b - D.x)
        rwa [h0] at h1
      have hkx : (D.s i * T * (D.s i)⁻¹ * T⁻¹) D.x = D.x + (b - D.s i b) := by
        show D.s i (T ((D.s i)⁻¹ (T⁻¹ D.x))) = _
        have e1 : (D.s i)⁻¹ (T⁻¹ D.x) = D.s i b - D.x := by
          rw [hTinv, ggQ2p3h_s_inv D i, map_sub, D.s_x]
        have e2 : T (D.s i b - D.x) = D.s i b + D.x - b := by
          rw [map_sub, hH _ (ggQ2p3h_s_mem D i hbH), hTx]; abel
        rw [e1, e2, map_sub, map_add, ggQ2p3h_s_s D i b, D.s_x]
        abel
      have := ggQ2p3h_k0a D hk hkH hbs hkx
      exact (sub_eq_zero.mp this).symm
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (D.fix b hsb)
    have hμ0 : μ = 0 := by
      by_contra hμ0
      apply D.hxH
      have : D.x = μ⁻¹ • b := by rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      rw [this]
      exact D.H.smul_mem _ hbH
    rw [hμ0, zero_smul] at hμ
    rw [hTx, ← hμ, add_zero]

private theorem ggQ2p3h_claim (D : GGQ2P3HeartData K V ι) {T : V ≃ₗ[K] V} (hT : D.P T) {ε : K}
    (hε : ε = 1 ∨ ε = -1) (hH : ∀ h ∈ D.H, T h = ε • h) :
    T D.x ∈ Submodule.span K {D.x} := by
  rcases hε with rfl | rfl
  · have h1 : ∀ h ∈ D.H, T h = h := fun h hh => by simpa using hH h hh
    rcases ggQ2p3h_k0 D hT h1 with h | h
    · rw [h]; exact Submodule.mem_span_singleton_self _
    · rw [h]; exact (Submodule.span K {D.x}).neg_mem (Submodule.mem_span_singleton_self _)
  · set z := T⁻¹ D.x with hz
    have hTz : T z = D.x := ggQ2p3h_apply_inv T D.x
    have hTc : ∀ h ∈ D.H, T h = -h := fun h hh => by simpa using hH h hh
    have hαz : ∀ i, D.α i z = 0 := by
      intro i
      have hk : D.P (T * D.s i * T⁻¹ * (D.s i)⁻¹) :=
        D.P_mul _ _ (D.P_mul _ _ (D.P_mul _ _ hT (D.P_s i)) (D.P_inv _ hT))
          (D.P_inv _ (D.P_s i))
      have hkH : ∀ h ∈ D.H, (T * D.s i * T⁻¹ * (D.s i)⁻¹) h = h := by
        intro h hh
        have hsh : D.s i h ∈ D.H := ggQ2p3h_s_mem D i hh
        have e1 : T⁻¹ (D.s i h) = -D.s i h := by
          have h0 : T (-D.s i h) = D.s i h := by rw [hTc _ (D.H.neg_mem hsh), neg_neg]
          have h1 := ggQ2p3h_inv_apply T (-D.s i h)
          rwa [h0] at h1
        show T (D.s i (T⁻¹ ((D.s i)⁻¹ h))) = h
        rw [ggQ2p3h_s_inv, e1, map_neg, ggQ2p3h_s_s, hTc _ (D.H.neg_mem hh), neg_neg]
      have hkx : (T * D.s i * T⁻¹ * (D.s i)⁻¹) D.x = D.x + D.α i z • D.c i := by
        show T (D.s i (T⁻¹ ((D.s i)⁻¹ D.x))) = _
        rw [ggQ2p3h_s_inv, D.s_x, ← hz, D.s_apply, map_sub, hTz, map_smul,
          hTc _ (D.c_mem i)]
        module
      rcases ggQ2p3h_k0 D hk hkH with h | h
      · rw [hkx] at h
        have h0 : D.α i z • D.c i = 0 := by simpa using h
        rcases smul_eq_zero.mp h0 with h0 | h0
        · exact h0
        · exact absurd h0 (ggQ2p3h_c_ne D i)
      · exfalso
        rw [hkx] at h
        have e : (-2 : K) = 1 := by linear_combination (-1 : K) * D.three
        have h2 : D.α i z • D.c i = D.x :=
          calc D.α i z • D.c i = -D.x - D.x := eq_sub_of_add_eq' h
            _ = (-2 : K) • D.x := by module
            _ = D.x := by rw [e, one_smul]
        exact D.hxH (h2 ▸ D.H.smul_mem _ (D.c_mem i))
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp
      (D.fix z fun i => by rw [D.s_apply, hαz i, zero_smul, sub_zero])
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hμ
      have hx0 : D.x = 0 := by rw [← hTz, ← hμ, map_zero]
      exact D.hxH (hx0 ▸ D.H.zero_mem)
    have hx : D.x = μ • T D.x :=
      calc D.x = T z := hTz.symm
        _ = T (μ • D.x) := by rw [hμ]
        _ = μ • T D.x := map_smul T μ D.x
    have hTx : T D.x = μ⁻¹ • D.x :=
      calc T D.x = μ⁻¹ • (μ • T D.x) := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        _ = μ⁻¹ • D.x := by rw [← hx]
    rw [hTx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Core

private noncomputable def ggQ2p3h_data {G : Type} [Group G] (Bs L : Subgroup G) (x : G)
    (M : GGQ2LDatum 3 Bs L x) (hNT : GGNoTransvection 3 Bs) (hxM : M.xV ∉ M.coSpan)
    (hsplit : M.coSpan ⊔ Submodule.span (ZMod 3) {M.xV} = ⊤) :
    GGQ2P3HeartData (ZMod 3) M.V M.Λ where
  three := by decide
  two_ne := by decide
  units := by decide
  H := M.coSpan
  x := M.xV
  hxH := hxM
  hsplit := hsplit
  P := fun T => ∃ φ : MulAut ↥Bs, φ ∈ ggInducedSubgroup ⊤ Bs ∧ ggLin (p := 3) M.model φ = T
  P_mul := by
    rintro S T ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ * ψ, Subgroup.mul_mem _ hφ hψ, map_mul _ _ _⟩
  P_inv := by
    rintro T ⟨φ, hφ, rfl⟩
    exact ⟨φ⁻¹, Subgroup.inv_mem _ hφ, map_inv _ _⟩
  noTv := by
    rintro T ⟨φ, hφ, rfl⟩ f w hw hf hfw h
    exact hNT φ hφ (ggIsTransvection_of_apply M.model hw hf hfw h)
  s := fun i => ggLin (p := 3) M.model (M.simple i)
  P_s := fun i => by
    have h1 : M.simple i ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp h1
    exact ⟨M.simple i, ⟨g, Subgroup.mem_top g, hgN, hg⟩, rfl⟩
  α := M.root
  c := M.coroot
  c_mem := fun i => Submodule.subset_span ⟨i, rfl⟩
  α_c := fun i => by
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  s_apply := fun i v => M.simple_apply i v
  s_x := fun i => by
    have hx : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.mem_span_singleton_self _
    have h1 : M.simple i ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact mem_ggFixedSubmodule_iff.mp hx _ h1
  fix := fun z hz => by
    have hzF : z ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      rw [M.automizer_L] at hφ
      refine Subgroup.closure_induction (p := fun φ _ => ggLin (p := 3) M.model φ z = z)
        ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨i, rfl⟩
        exact hz i
      · simp
      · intro a b _ _ ha hb
        rw [map_mul, LinearEquiv.mul_apply, hb, ha]
      · intro a _ ha
        rw [map_inv]
        have h0 := ggQ2p3h_inv_apply (ggLin (p := 3) M.model a) z
        rwa [ha] at h0
    rwa [M.fixed_x] at hzF

theorem ggQ2_p3_heartCell : GGQ2P3OffI1HeartCell := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ hCav hAbs hsel
  subst hp
  obtain ⟨M, hxM, hsplit, hN⟩ := hsel
  have hNT : GGNoTransvection 3 Bs := hS.1.2.2.2.1
  intro g hg
  obtain ⟨r, hr, ε, hε, hNr⟩ := hN g hg
  have hrN : r ∈ Subgroup.normalizer (Bs : Set G) :=
    (Subgroup.closure_le (Subgroup.normalizer (Bs : Set G))).mpr
      (fun h hh => by obtain ⟨φ, hφ, -⟩ := hh; exact hφ.1) hr
  refine ⟨r, hr, ?_⟩
  let φ : MulAut ↥Bs := ggConjAut Bs hg
  let ρ : MulAut ↥Bs := ggConjAut Bs hrN
  have hφI : φ ∈ ggInducedSubgroup ⊤ Bs := ggConjAut_mem_ggInduced (Subgroup.mem_top g) hg
  have hρI : ρ ∈ ggInducedSubgroup ⊤ Bs := ggConjAut_mem_ggInduced (Subgroup.mem_top r) hrN
  have hψI : ρ⁻¹ * φ ∈ ggInducedSubgroup ⊤ Bs :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hρI) hφI
  have hP : (ggQ2p3h_data Bs L x M hNT hxM hsplit).P (ggLin (p := 3) M.model (ρ⁻¹ * φ)) :=
    ⟨_, hψI, rfl⟩
  have hHψ : ∀ h ∈ (ggQ2p3h_data Bs L x M hNT hxM hsplit).H,
      ggLin (p := 3) M.model (ρ⁻¹ * φ) h = ε • h := by
    intro h hh
    have e : ggLin (p := 3) M.model φ h = ε • ggLin (p := 3) M.model ρ h :=
      hNr φ ρ ⟨hg, fun _ => rfl⟩ ⟨hrN, fun _ => rfl⟩ h hh
    rw [map_mul, LinearEquiv.mul_apply, e, map_inv, map_smul]
    congr 1
    exact ggQ2p3h_inv_apply _ _
  have hmem := ggQ2p3h_claim (ggQ2p3h_data Bs L x M hNT hxM hsplit) hP hε hHψ
  change ggLin (p := 3) M.model (ρ⁻¹ * φ) M.xV ∈ Submodule.span (ZMod 3) {M.xV} at hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  let b0 : ↥Bs := ⟨x, M.hx⟩
  have key : (ρ⁻¹ * φ) b0 = b0 ^ a.val := by
    apply Additive.ofMul.injective
    apply M.model.injective
    have h1 : ggLin (p := 3) M.model (ρ⁻¹ * φ) (M.model (Additive.ofMul b0)) =
        M.model (Additive.ofMul ((ρ⁻¹ * φ) b0)) := ggLin_apply_ofMul M.model _ b0
    have h2 : ggLin (p := 3) M.model (ρ⁻¹ * φ) (M.model (Additive.ofMul b0)) =
        a • M.model (Additive.ofMul b0) := ha.symm
    rw [← h1, h2, ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3),
      ZMod.natCast_zmod_val]
  have hG : r⁻¹ * (g * x * g⁻¹) * r = x ^ a.val := by
    have h1 : (((ρ⁻¹ * φ) b0 : ↥Bs) : G) = r⁻¹ * (g * x * g⁻¹) * r := by
      rw [MulAut.mul_apply, inv_apply_of_forall (φ := ρ) (h := r) (fun _ => rfl)]
      rfl
    rw [← h1, key]
    exact Subgroup.coe_pow Bs b0 a.val
  have hconj : g * x * g⁻¹ = (r * x * r⁻¹) ^ a.val := by
    rw [conj_pow, ← hG]
    group
  have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ Subgroup.zpowers (r * x * r⁻¹) := by
    rw [Subgroup.zpowers_le, hconj]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers]
  have o1 : orderOf (g * x * g⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  have o2 : orderOf (r * x * r⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective x
  rw [o1, o2]

theorem ggQ2_p3_of_rest_cell (hr : GGQ2P3OffI1RestInput) (hc : GGQ2P3OffI1HeartCell) :
    GGQ2P3OffI1Input := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ hCav hAbs
  by_cases hsel : GGQ2P3HeartSel p Bs L x
  · exact hc hS hp hI1 hCav hAbs hsel
  · exact hr hS hp hI1 hCav hAbs hsel

end CFSG.StandardType

end
