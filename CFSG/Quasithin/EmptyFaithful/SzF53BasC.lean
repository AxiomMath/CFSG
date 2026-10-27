module

public import CFSG.Quasithin.Recognition.F112WKernel
public import CFSG.Quasithin.EmptyFaithful.SzF53BasA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G]

open CosetGeom

variable {H M S : Subgroup G}

@[expose] def Qv (δ : Geo H M) : Subgroup G := pCoreOf 2 (stab δ)

@[expose] def Zv (δ : Geo H M) : Subgroup G :=
  ⨆ (T : Subgroup G) (_ : IsSylowTwoOf T (stab δ)), quasithinOmegaOneCenter T

@[expose] def Vn (δ : Geo H M) : Subgroup G := ⨆ (μ : Geo H M) (_ : μ ∈ nbrs δ), Zv μ

@[expose] noncomputable def bAt (δ : Geo H M) : ℕ :=
  sInf {n : ℕ | ∃ μ : Geo H M, dist δ μ = n ∧ ¬ Zv δ ≤ Qv μ}

@[expose] noncomputable def bMin (H M : Subgroup G) : ℕ := sInf (Set.range (bAt (H := H) (M := M)))

structure IsCritData (α β α' : Geo H M) : Prop where
  adj : (graph (H ⊔ M) H M).Adj α β
  bAt_eq : bAt α = bMin H M
  dist_eq : dist α α' = bMin H M
  dist_eq' : dist β α' + 1 = bMin H M
  not_le : ¬ Zv α ≤ Qv α'

@[expose] def IsCritPair₁ (δ δ' : Geo H M) : Prop := ¬ Zv δ ≤ Qv δ' ∧ dist δ δ' = bMin H M

omit [Finite G] in
theorem conjSub_omegaOneCenter (g : G) (T : Subgroup G) :
    conjSub g (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter (conjSub g T) := by
  unfold quasithinOmegaOneCenter
  rw [conjSub_closure]
  congr 1
  ext y
  have hZ : conjSub g (T ⊓ Subgroup.centralizer (T : Set G)) =
      conjSub g T ⊓ Subgroup.centralizer ((conjSub g T : Subgroup G) : Set G) := by
    rw [conjSub_inf, conjSub_centralizer]
  constructor
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have hx' : x ∈ T ⊓ Subgroup.centralizer (T : Set G) := hx
      have := mul_mem_conjSub (g := g) hx'
      rw [hZ] at this
      exact this
    · show (g * x * g⁻¹) ^ 2 = 1
      rw [conj_pow, hx2]
      group
  · rintro ⟨hy, hy2⟩
    have hy' : y ∈ conjSub g (T ⊓ Subgroup.centralizer (T : Set G)) := by
      rw [hZ]; exact hy
    refine ⟨g⁻¹ * y * g, ⟨mem_conjSub.mp hy', ?_⟩, by group⟩
    have h2 := conj_pow (a := g⁻¹) (b := y) (i := 2)
    simp only [inv_inv] at h2
    show (g⁻¹ * y * g) ^ 2 = 1
    rw [h2, hy2]
    group

omit [Finite G] in
theorem Qv_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Qv (g • δ) = conjSub (g : G) (Qv δ) := by
  unfold Qv
  rw [stab_smul, pCoreOf_conjSub]

omit [Finite G] in
theorem Zv_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Zv (g • δ) = conjSub (g : G) (Zv δ) := by
  unfold Zv
  rw [stab_smul]
  apply le_antisymm
  · refine iSup₂_le fun T hT => ?_
    have hT' : IsSylowTwoOf (conjSub (g : G)⁻¹ T) (stab δ) := by
      have := isSylowTwoOf_conj hT (g : G)⁻¹
      rwa [conjSub_conjSub_inv] at this
    have e : quasithinOmegaOneCenter T =
        conjSub (g : G) (quasithinOmegaOneCenter (conjSub (g : G)⁻¹ T)) := by
      rw [conjSub_omegaOneCenter, conjSub_inv_conjSub]
    rw [e]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (T : Subgroup G)
      (_ : IsSylowTwoOf T (stab δ)) => quasithinOmegaOneCenter T) (conjSub (g : G)⁻¹ T) hT' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun T hT => ?_
    rw [← conjSub_le_iff, conjSub_omegaOneCenter]
    exact le_iSup₂_of_le (f := fun (T : Subgroup G)
      (_ : IsSylowTwoOf T (conjSub (g : G) (stab δ))) => quasithinOmegaOneCenter T)
      (conjSub (g : G) T) (isSylowTwoOf_conj hT (g : G)) le_rfl

omit [Finite G] in
theorem conjSub_le_conjSub_iff' (g : G) {A B : Subgroup G} :
    conjSub g A ≤ conjSub g B ↔ A ≤ B := by
  rw [conjSub_le_iff, conjSub_conjSub_inv]

omit [Finite G] in
theorem bAt_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : bAt (g • δ) = bAt δ := by
  have key : ∀ (g : ↥(H ⊔ M)) (δ : Geo H M) (n : ℕ),
      (∃ μ : Geo H M, dist δ μ = n ∧ ¬ Zv δ ≤ Qv μ) →
      (∃ μ : Geo H M, dist (g • δ) μ = n ∧ ¬ Zv (g • δ) ≤ Qv μ) := by
    intro g δ n ⟨μ, hμ, hnle⟩
    refine ⟨g • μ, ?_, ?_⟩
    · rw [CosetGeom.dist_smul]; exact hμ
    · rw [Zv_smul, Qv_smul, conjSub_le_conjSub_iff']; exact hnle
  unfold bAt
  congr 1
  ext n
  constructor
  · intro h
    have := key g⁻¹ (g • δ) n h
    simpa using this
  · exact key g δ n

omit [Finite G] in
theorem Vn_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Vn (g • δ) = conjSub (g : G) (Vn δ) := by
  unfold Vn
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => ?_
    obtain ⟨μ', rfl⟩ : ∃ μ', μ = g • μ' := ⟨g⁻¹ • μ, by simp⟩
    have hμ' : μ' ∈ nbrs δ := (smul_adj g).mp hμ
    rw [Zv_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs δ) => Zv μ)
      μ' hμ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun μ hμ => ?_
    rw [← conjSub_le_iff, ← Zv_smul]
    exact le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs (g • δ)) => Zv μ)
      (g • μ) ((smul_adj g).mpr hμ) le_rfl

theorem Qv_eq_ballStab_one (hA : F53Amalgam H M S) (δ : Geo H M) : ballStab 1 δ = Qv δ := by
  have hB : IsPGroup 2 ↥(H ⊓ M) := by
    rw [hA.inf_eq]; exact hA.amalgam.sylow₁.2.1
  have h0 : ballStab 1 (γ₀ (H ⊔ M) H M) = Qv (γ₀ (H ⊔ M) H M) := by
    unfold Qv
    rw [stab_γ₀ hA.amalgam.le₁, F112W.kerα_eq_ballStab hA.amalgam.gen,
      F112W.kerα_eq_of_isPGroup_inf hA.amalgam hB]
  have h1 : ballStab 1 (γ₁ (H ⊔ M) H M) = Qv (γ₁ (H ⊔ M) H M) := by
    unfold Qv
    rw [stab_γ₁ hA.amalgam.le₂, F112W.kerβ_eq_ballStab hA.amalgam.gen,
      F112W.kerβ_eq_of_isPGroup_inf hA.amalgam hB]
  cases hv : vtype δ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    rw [hg, ballStab_smul, Qv_smul, h0]
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    rw [hg, ballStab_smul, Qv_smul, h1]

private theorem eq_bot_core (hA : F53Amalgam H M S) {α β : Geo H M} (g : ↥(H ⊔ M))
    (hg0 : g • γ₀ (H ⊔ M) H M = α) (hg1 : g • γ₁ (H ⊔ M) H M = β)
    {U : Subgroup G} (hU : U ≤ stab α ⊓ stab β)
    (hα : ∀ ε ∈ nbrs α, ∀ ε' ∈ nbrs α, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • α = α ∧ x • ε = ε')
    (hβ : ∀ ε ∈ nbrs β, ∀ ε' ∈ nbrs β, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • β = β ∧ x • ε = ε') : U = ⊥ := by
  have h₁ := hA.amalgam.le₁
  have h₂ := hA.amalgam.le₂
  have hadj : (graph (H ⊔ M) H M).Adj α β := by
    rw [← hg0, ← hg1]; exact (smul_adj g).mpr adj_γ₀_γ₁
  set U' : Subgroup G := conjSub (g : G)⁻¹ U with hU'def
  have hU' : U' ≤ H ⊓ M := by
    have e : stab α ⊓ stab β = conjSub (g : G) (H ⊓ M) := by
      rw [conjSub_inf, ← hg0, ← hg1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂]
    rw [hU'def, conjSub_le_iff, inv_inv, ← e]
    exact hU
  have hnorm : ∀ x : ↥(H ⊔ M), (x : G) ∈ Subgroup.normalizer (U : Set G) →
      ((g⁻¹ * x * g : ↥(H ⊔ M)) : G) ∈ Subgroup.normalizer (U' : Set G) := by
    intro x hx
    rw [hU'def, conjSub_normalizer, mem_conjSub]
    have : ((g : G)⁻¹)⁻¹ * ((g⁻¹ * x * g : ↥(H ⊔ M)) : G) * (g : G)⁻¹ = (x : G) := by
      simp [mul_assoc]
    rw [this]; exact hx
  have hN₁ : ∀ h ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (U' : Set G), n⁻¹ * h ∈ M := by
    intro h hh
    set hh' : ↥(H ⊔ M) := ⟨h, h₁ hh⟩ with hhdef
    have hfix : hh' • γ₀ (H ⊔ M) H M = γ₀ (H ⊔ M) H M := smul_γ₀_of_mem h₁ hh
    have hn1 : hh' • γ₁ (H ⊔ M) H M ∈ nbrs (γ₀ (H ⊔ M) H M) := by
      have := (smul_adj hh').mpr (adj_γ₀_γ₁ (G₀ := H ⊔ M) (G₁ := H) (G₂ := M))
      rwa [hfix] at this
    have hn2 : g • (hh' • γ₁ (H ⊔ M) H M) ∈ nbrs α := by
      have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj (γ₀ (H ⊔ M) H M)
        (hh' • γ₁ (H ⊔ M) H M) from hn1)
      rwa [hg0] at this
    obtain ⟨x, hxN, hxα, hxβ⟩ := hα β hadj _ hn2
    refine ⟨((g⁻¹ * x * g : ↥(H ⊔ M)) : G), ⟨?_, hnorm x hxN⟩, ?_⟩
    · have : (g⁻¹ * x * g) • γ₀ (H ⊔ M) H M = γ₀ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg0, hxα, ← hg0, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₀ h₁] at this
    · have hn : (g⁻¹ * x * g) • γ₁ (H ⊔ M) H M = hh' • γ₁ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg1, hxβ, inv_smul_smul]
      have : ((g⁻¹ * x * g)⁻¹ * hh') • γ₁ (H ⊔ M) H M = γ₁ (H ⊔ M) H M := by
        rw [mul_smul, ← hn, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₁ h₂] at this
  have hN₂ : ∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer (U' : Set G), n⁻¹ * m ∈ H := by
    intro m hm
    set mm' : ↥(H ⊔ M) := ⟨m, h₂ hm⟩ with hmdef
    have hfix : mm' • γ₁ (H ⊔ M) H M = γ₁ (H ⊔ M) H M := smul_γ₁_of_mem h₂ hm
    have hn1 : mm' • γ₀ (H ⊔ M) H M ∈ nbrs (γ₁ (H ⊔ M) H M) := by
      have := (smul_adj mm').mpr (adj_γ₀_γ₁ (G₀ := H ⊔ M) (G₁ := H) (G₂ := M)).symm
      rwa [hfix] at this
    have hn2 : g • (mm' • γ₀ (H ⊔ M) H M) ∈ nbrs β := by
      have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj (γ₁ (H ⊔ M) H M)
        (mm' • γ₀ (H ⊔ M) H M) from hn1)
      rwa [hg1] at this
    obtain ⟨x, hxN, hxβ, hxα⟩ := hβ α hadj.symm _ hn2
    refine ⟨((g⁻¹ * x * g : ↥(H ⊔ M)) : G), ⟨?_, hnorm x hxN⟩, ?_⟩
    · have : (g⁻¹ * x * g) • γ₁ (H ⊔ M) H M = γ₁ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg1, hxβ, ← hg1, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₁ h₂] at this
    · have hn : (g⁻¹ * x * g) • γ₀ (H ⊔ M) H M = mm' • γ₀ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg0, hxα, inv_smul_smul]
      have : ((g⁻¹ * x * g)⁻¹ * mm') • γ₀ (H ⊔ M) H M = γ₀ (H ⊔ M) H M := by
        rw [mul_smul, ← hn, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₀ h₁] at this
  have := F112W.eq_bot_of_normalizer_transitive hA.amalgam hU' hN₁ hN₂
  rwa [hU'def, conjSub_eq_bot_iff] at this

theorem eq_bot_of_normalizer_transitive_vertex (hA : F53Amalgam H M S) {α β : Geo H M}
    (hαβ : (graph (H ⊔ M) H M).Adj α β) {U : Subgroup G} (hU : U ≤ stab α ⊓ stab β)
    (hα : ∀ ε ∈ nbrs α, ∀ ε' ∈ nbrs α, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • α = α ∧ x • ε = ε')
    (hβ : ∀ ε ∈ nbrs β, ∀ ε' ∈ nbrs β, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • β = β ∧ x • ε = ε') : U = ⊥ := by
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hαβ
  · exact eq_bot_core hA g hg0 hg1 hU hα hβ
  · exact eq_bot_core hA g hg0 hg1 (by rwa [inf_comm]) hβ hα

theorem sup_sylow_eq_of_normal_not_le {X C T : Subgroup G} {n : ℕ} (hn : n = 3 ∨ n = 5)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin n))) (hT : IsSylowTwoOf T X)
    (hCX : C ≤ X) (hC : X ≤ Subgroup.normalizer (C : Set G)) (hCQ : ¬ C ≤ pCoreOf 2 X) :
    X ≤ C ⊔ T := by
  obtain ⟨e⟩ := hq
  let φ : ↥X →* Equiv.Perm (Fin n) :=
    (e : OTwoQuot X →* Equiv.Perm (Fin n)).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))
  have hφs : Function.Surjective φ := fun p => by
    obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hφker : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
    intro x
    have hx : φ x = e (QuotientGroup.mk x) := rfl
    rw [hx, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]
  set C' : Subgroup ↥X := C.subgroupOf X with hC'def
  have hC'n : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hC
  set N : Subgroup (Equiv.Perm (Fin n)) := C'.map φ with hNdef
  have hNn : N.Normal := Subgroup.Normal.map hC'n φ hφs
  have hNb : N ≠ ⊥ := by
    intro hb
    apply hCQ
    intro c hc
    have hmem : φ ⟨c, hCX hc⟩ ∈ N := ⟨⟨c, hCX hc⟩, hc, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact (hφker _).mp hmem
  have hA : alternatingGroup (Fin n) ≤ N := by
    have := hNn
    rcases hn with rfl | rfl
    · exact normal_ge_alt3 N hNb
    · exact normal_ge_alt5 N hNb
  have hodd : ∃ t : ↥X, (t : G) ∈ T ∧ Equiv.Perm.sign (φ t) = -1 := by
    by_contra hcon
    push Not at hcon
    have : Nontrivial (Fin n) := by
      rcases hn with rfl | rfl <;> infer_instance
    let ψ : ↥X →* ℤˣ := Equiv.Perm.sign.comp φ
    have hψs : Function.Surjective ψ := (Equiv.Perm.sign_surjective (Fin n)).comp hφs
    have hidx : ψ.ker.index = 2 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψs]
      simp
    have hle : T.subgroupOf X ≤ ψ.ker := by
      intro t ht
      have := hcon t ht
      rw [MonoidHom.mem_ker]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (φ t)) with h | h
      · exact h
      · exact absurd h this
    have h2 : 2 ∣ (T.subgroupOf X).index := by
      rw [← Subgroup.relIndex_mul_index hle, hidx]
      exact dvd_mul_left 2 _
    exact hT.2.2 h2
  obtain ⟨t, htT, ht⟩ := hodd
  have hsup : N ⊔ (T.subgroupOf X).map φ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
    · exact Subgroup.mem_sup_left (hA (by rwa [Equiv.Perm.mem_alternatingGroup]))
    · have hg : g * (φ t)⁻¹ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, h, ht]
        simp
      have : g = (g * (φ t)⁻¹) * φ t := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hA hg))
        (Subgroup.mem_sup_right ⟨t, htT, rfl⟩)
  have hX' : C' ⊔ T.subgroupOf X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ (C' ⊔ T.subgroupOf X).map φ := by
      rw [Subgroup.map_sup, ← hNdef, hsup]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    have hk : y⁻¹ * x ∈ T.subgroupOf X := by
      have h1 : φ (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
      exact isSylowTwoOf_pCoreOf_le hT ((hφker _).mp h1)
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ hy (Subgroup.mem_sup_right hk)
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥X) ∈ C' ⊔ T.subgroupOf X := by rw [hX']; exact Subgroup.mem_top _
  have h2 : x ∈ (C' ⊔ T.subgroupOf X).map X.subtype := ⟨_, h1, rfl⟩
  rw [Subgroup.map_sup, hC'def, Subgroup.map_subgroupOf_eq_of_le hCX,
    Subgroup.map_subgroupOf_eq_of_le hT.1] at h2
  exact h2

theorem exists_smul_eq_of_normal_not_le (hA : F53Amalgam H M S) {δ μ μ' : Geo H M}
    (hμ : μ ∈ nbrs δ) (hμ' : μ' ∈ nbrs δ) {C : Subgroup G} (hCX : C ≤ stab δ)
    (hC : stab δ ≤ Subgroup.normalizer (C : Set G)) (hCQ : ¬ C ≤ pCoreOf 2 (stab δ)) :
    ∃ c : ↥(H ⊔ M), (c : G) ∈ C ∧ c • μ = μ' := by
  have hT := sylow_stab_inf_left hA hμ
  have hn : ∃ n, (n = 3 ∨ n = 5) ∧ Nonempty (OTwoQuot (stab δ) ≃* Equiv.Perm (Fin n)) := by
    cases hv : vtype δ with
    | false => exact ⟨5, Or.inr rfl, quot_stab_five hA hv⟩
    | true => exact ⟨3, Or.inl rfl, quot_stab_three hA hv⟩
  obtain ⟨n, hn3, hq⟩ := hn
  have hsup := sup_sylow_eq_of_normal_not_le hn3 hq hT hCX hC hCQ
  obtain ⟨x, hx, hxμ⟩ := stab_transitive_on_nbrs hμ hμ'
  have hTN : stab δ ⊓ stab μ ≤ Subgroup.normalizer (C : Set G) := inf_le_left.trans hC
  obtain ⟨c, hc, t, ht, hct⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTN).mp (hsup hx)
  have hcX : c ∈ H ⊔ M := stab_le δ (hCX hc)
  have htX : t ∈ H ⊔ M := stab_le δ (ht.1)
  refine ⟨⟨c, hcX⟩, hc, ?_⟩
  have htfix : (⟨t, htX⟩ : ↥(H ⊔ M)) • μ = μ := smul_eq_of_mem_stab ht.2
  have : x = ⟨c, hcX⟩ * ⟨t, htX⟩ := Subtype.ext hct
  rw [← hxμ, this, mul_smul, htfix]

theorem Zv_eq_conjClosure {δ : Geo H M} {T : Subgroup G} (hT : IsSylowTwoOf T (stab δ)) :
    Zv δ = conjClosure (quasithinOmegaOneCenter T) (stab δ) := by
  apply le_antisymm
  · refine iSup₂_le fun T' hT' => ?_
    obtain ⟨x, hx, hle⟩ := isSylowTwoOf_exists_conj_le hT hT'.1 hT'.2.1
    have hS : IsSylowTwoOf (conjSub x T) (stab δ) := by
      have := isSylowTwoOf_conj hT x
      rwa [conjSub_eq_of_mem hx] at this
    have heq : T' = conjSub x T := F1.eq_of_isSylowTwoOf_le hT' hS.1 hS.2.1 hle
    rw [heq, ← conjSub_omegaOneCenter]
    intro y hy
    have hy' := mem_conjSub.mp hy
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact mem_conjClosure hx hy'
  · refine conjClosure_le fun h hh z hz => ?_
    have hS : IsSylowTwoOf (conjSub h T) (stab δ) := by
      have := isSylowTwoOf_conj hT h
      rwa [conjSub_eq_of_mem hh] at this
    have hmem : h * z * h⁻¹ ∈ quasithinOmegaOneCenter (conjSub h T) := by
      rw [← conjSub_omegaOneCenter]
      exact mul_mem_conjSub hz
    exact (le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab δ)) =>
      quasithinOmegaOneCenter T) (conjSub h T) hS le_rfl) hmem

theorem stab_le_normalizer_Zv (hA : F53Amalgam H M S) (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Zv δ : Set G) := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  rw [Zv_eq_conjClosure (sylow_stab_inf_left hA (show μ ∈ nbrs δ from hμ))]
  exact le_normalizer_conjClosure _ _

theorem Zv_le_centerOf_Qv (hA : F53Amalgam H M S) (δ : Geo H M) : Zv δ ≤ centerOf (Qv δ) := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hT := sylow_stab_inf_left hA (show μ ∈ nbrs δ from hμ)
  rw [Zv_eq_conjClosure hT]
  exact (conjClosure_le_centerOf_pCoreOf_of_sylowIn hT.1 hT.2.1 hT.2.2 (charTwo_stab hA δ)
    (Z := quasithinOmegaOneCenter _) le_rfl).1

theorem isElemAbelian_Zv (hA : F53Amalgam H M S) (δ : Geo H M) : IsElemAbelian 2 (Zv δ) := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hT := sylow_stab_inf_left hA (show μ ∈ nbrs δ from hμ)
  rw [Zv_eq_conjClosure hT]
  exact (conjClosure_le_centerOf_pCoreOf_of_sylowIn hT.1 hT.2.1 hT.2.2 (charTwo_stab hA δ)
    (Z := quasithinOmegaOneCenter _) le_rfl).2

theorem Zv_le_Qv (hA : F53Amalgam H M S) (δ : Geo H M) : Zv δ ≤ Qv δ :=
  (Zv_le_centerOf_Qv hA δ).trans inf_le_left

theorem Qv_le_stab_of_mem_nbrs (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    Qv δ ≤ stab μ := by
  have h1 := pCoreOf_stab_le_ballStab_one hA.amalgam δ
  exact h1.trans (ballStab_le_stab_of_dist_le
    (dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj δ μ from h)).le)

theorem omegaOneCenter_le_Zv (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    quasithinOmegaOneCenter (stab δ) ≤ quasithinOmegaOneCenter (stab δ ⊓ stab μ) ∧
      quasithinOmegaOneCenter (stab δ ⊓ stab μ) ≤ Zv δ ∧
      quasithinOmegaOneCenter (stab δ ⊓ stab μ) ≤ Zv μ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold quasithinOmegaOneCenter
    refine Subgroup.closure_mono ?_
    rintro z ⟨hz, hz2⟩
    refine ⟨⟨⟨hz.1, ?_⟩, ?_⟩, hz2⟩
    ·
      have hzQ : z ∈ pCoreOf 2 (stab δ) := by
        refine charTwo_stab hA δ ⟨hz.1, ?_⟩
        exact Subgroup.centralizer_le (pCoreOf_le 2 (stab δ)) hz.2
      exact Qv_le_stab_of_mem_nbrs hA h hzQ
    · exact Subgroup.centralizer_le (inf_le_left : stab δ ⊓ stab μ ≤ stab δ) hz.2
  · exact le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab δ)) =>
      quasithinOmegaOneCenter T) (stab δ ⊓ stab μ) (sylow_stab_inf_left hA h) le_rfl
  · exact le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab μ)) =>
      quasithinOmegaOneCenter T) (stab δ ⊓ stab μ) (sylow_stab_inf_right hA h) le_rfl

theorem card_oTwoQuot_le (X : Subgroup G) : Nat.card (OTwoQuot X) ≤ Nat.card X :=
  Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective

theorem stab_ne_bot (hA : F53Amalgam H M S) (δ : Geo H M) : stab δ ≠ ⊥ := by
  intro h
  have h1 : Nat.card (stab δ) = 1 := by rw [h, Subgroup.card_bot]
  have h2 := card_oTwoQuot_le (stab δ)
  rw [h1] at h2
  cases hv : vtype δ with
  | false =>
    obtain ⟨φ⟩ := quot_stab_five hA hv
    rw [Nat.card_congr φ.toEquiv, S152Fin.card_Perm_five] at h2
    omega
  | true =>
    obtain ⟨φ⟩ := quot_stab_three hA hv
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm] at h2
    simp [Nat.factorial] at h2

theorem Qv_ne_bot (hA : F53Amalgam H M S) (δ : Geo H M) : Qv δ ≠ ⊥ := by
  intro h
  apply stab_ne_bot hA δ
  have h1 : stab δ ⊓ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) ≤ pCoreOf 2 (stab δ) :=
    charTwo_stab hA δ
  have h2 : pCoreOf 2 (stab δ) = ⊥ := h
  rw [h2] at h1
  rw [eq_bot_iff]
  intro x hx
  have hc : x ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Subgroup.mem_bot.mp hg]
    simp
  exact h1 ⟨hx, hc⟩

theorem inf_stab_ne_bot (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    stab δ ⊓ stab μ ≠ ⊥ := by
  intro hb
  have hS := sylow_stab_inf_left hA h
  have hQ : pCoreOf 2 (stab δ) ≤ ⊥ := hb ▸ isSylowTwoOf_pCoreOf_le hS
  have hcent : stab δ ⊓ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) ≤ pCoreOf 2 (stab δ) :=
    charTwo_stab hA δ
  have hQb : pCoreOf 2 (stab δ) = ⊥ := le_bot_iff.mp hQ
  rw [hQb] at hcent
  have : stab δ ≤ ⊥ := by
    intro x hx
    apply hcent
    refine ⟨hx, ?_⟩
    show x ∈ Subgroup.centralizer (((⊥ : Subgroup G)) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    rw [hy1]; simp
  exact stab_ne_bot hA δ (le_bot_iff.mp this)

theorem Zv_ne_bot (hA : F53Amalgam H M S) (δ : Geo H M) : Zv δ ≠ ⊥ := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hm : μ ∈ nbrs δ := hμ
  have hS := sylow_stab_inf_left hA hm
  have h1 := quasithinOmegaOneCenter_ne_bot hS.2.1 (inf_stab_ne_bot hA hm)
  intro h
  apply h1
  exact le_bot_iff.mp ((omegaOneCenter_le_Zv hA hm).2.1.trans h.le)

theorem exists_not_le_Qv (hA : F53Amalgam H M S) (δ : Geo H M) : ∃ μ : Geo H M, ¬ Zv δ ≤ Qv μ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, -, hn⟩ := exists_ballStab_eq_bot hA.amalgam
  apply Zv_ne_bot hA δ
  have : Zv δ ≤ ballStab n δ := fun x hx =>
    mem_ballStab.mpr fun μ _ => (pCoreOf_le 2 (stab μ)) (hcon μ hx)
  rw [hn] at this
  exact le_bot_iff.mp this

theorem bAt_spec (hA : F53Amalgam H M S) (δ : Geo H M) :
    ∃ μ : Geo H M, dist δ μ = bAt δ ∧ ¬ Zv δ ≤ Qv μ := by
  have hne : {n : ℕ | ∃ μ : Geo H M, dist δ μ = n ∧ ¬ Zv δ ≤ Qv μ}.Nonempty := by
    obtain ⟨μ, hμ⟩ := exists_not_le_Qv hA δ
    exact ⟨_, μ, rfl, hμ⟩
  exact Nat.sInf_mem hne

omit [Finite G] in
theorem Zv_le_Qv_of_dist_lt {δ μ : Geo H M} (h : dist δ μ < bAt δ) : Zv δ ≤ Qv μ := by
  by_contra hc
  exact Nat.notMem_of_lt_sInf h ⟨μ, rfl, hc⟩

theorem bAt_pos (hA : F53Amalgam H M S) (δ : Geo H M) : 1 ≤ bAt δ := by
  by_contra h
  have h0 : bAt δ = 0 := by omega
  obtain ⟨μ, hμ, hn⟩ := bAt_spec hA δ
  rw [h0] at hμ
  have : δ = μ := (dist_eq_zero_iff hA.amalgam.gen).mp hμ
  subst this
  exact hn (Zv_le_Qv hA δ)

theorem Zv_le_stab_of_dist_le (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : dist δ μ ≤ bAt δ) :
    Zv δ ≤ stab μ := by
  rcases h.lt_or_eq with hlt | heq
  · exact (Zv_le_Qv_of_dist_lt hlt).trans (pCoreOf_le 2 _)
  · have hb := bAt_pos hA δ
    obtain ⟨μ', hμ', hd⟩ := exists_adj_dist_eq hA.amalgam.gen (α := δ) (δ := μ)
      (d := bAt δ - 1) (by omega)
    have h1 : Zv δ ≤ Qv μ' := Zv_le_Qv_of_dist_lt (by omega)
    exact h1.trans (Qv_le_stab_of_mem_nbrs hA (show μ ∈ nbrs μ' from hμ'.symm))

omit [Finite G] in
theorem bMin_le_bAt (δ : Geo H M) : bMin H M ≤ bAt δ := Nat.sInf_le ⟨δ, rfl⟩

theorem exists_bAt_eq_bMin (_hA : F53Amalgam H M S) : ∃ δ : Geo H M, bAt δ = bMin H M := by
  have hne : (Set.range (bAt (H := H) (M := M))).Nonempty := ⟨_, γ₀ (H ⊔ M) H M, rfl⟩
  exact Nat.sInf_mem hne

theorem bMin_pos (hA : F53Amalgam H M S) : 1 ≤ bMin H M := by
  obtain ⟨δ, hδ⟩ := exists_bAt_eq_bMin hA
  rw [← hδ]; exact bAt_pos hA δ

omit [Finite G] in
theorem bAt_eq_of_vtype_eq {δ δ' : Geo H M} (h : vtype δ = vtype δ') : bAt δ = bAt δ' := by
  cases hv : vtype δ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    obtain ⟨g', hg'⟩ := exists_smul_eq_γ₀ (h ▸ hv)
    rw [hg, hg', bAt_smul, bAt_smul]
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    obtain ⟨g', hg'⟩ := exists_smul_eq_γ₁ (h ▸ hv)
    rw [hg, hg', bAt_smul, bAt_smul]

theorem exists_critData (hA : F53Amalgam H M S) {α β : Geo H M} (hα : bAt α = bMin H M)
    (hαβ : (graph (H ⊔ M) H M).Adj α β) : ∃ α' : Geo H M, IsCritData α β α' := by
  obtain ⟨μ, hd, hn⟩ := bAt_spec hA α
  have hb := bAt_pos hA α
  obtain ⟨β₀, hβ₀, hdβ₀⟩ := exists_adj_dist_eq hA.amalgam.gen (α := μ) (δ := α)
    (d := bAt α - 1) (by rw [CosetGeom.dist_comm]; omega)
  obtain ⟨g, hgα, hgβ⟩ := exists_stab_smul_eq hβ₀ hαβ
  refine ⟨g • μ, hαβ, hα, ?_, ?_, ?_⟩
  · have e : dist α (g • μ) = dist α μ := by
      conv_lhs => rw [← hgα]
      exact CosetGeom.dist_smul g α μ
    rw [e, hd, hα]
  · have e : dist β (g • μ) = dist β₀ μ := by
      conv_lhs => rw [← hgβ]
      exact CosetGeom.dist_smul g β₀ μ
    rw [e, CosetGeom.dist_comm, hdβ₀]
    omega
  · intro hle
    apply hn
    have h1 : Zv α = conjSub (g : G) (Zv α) := by
      conv_lhs => rw [← hgα]
      exact Zv_smul g α
    have hle' : conjSub (g : G) (Zv α) ≤ conjSub (g : G) (Qv μ) := by
      rw [← h1]; rwa [Qv_smul] at hle
    exact (conjSub_le_conjSub_iff' _).mp hle'

end F53

end CFSG.Quasithin
