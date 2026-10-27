module

public import CFSG.RankThree.PartOne.KE.E7ThreeLayers
public import CFSG.RankThree.PartOne.KE.E7ThreeA1
public import CFSG.RankThree.PartOne.KE.E7ThreeA2
public import CFSG.RankThree.PartOne.KE.E7ThreeA5
public import CFSG.RankThree.PartOne.KE.E7ThreeD4
public import CFSG.RankThree.PartOne.KE.E7ThreeCertSound
public import CFSG.RankThree.PartOne.KE.E7ThreeFrame
public import CFSG.RankThree.PartOne.KE.E7ThreeLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

section Helpers

variable {L : Type} [Field L]

theorem weyl_smul_zsmul_pm (g : WeylGroup Tag.E7) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (x : Fin Tag.E7.rank → ℤ) : g • (ε • x) = ε • (g • x) := by
  rcases hε with rfl | rfl
  · simp
  · rw [neg_one_smul, neg_one_smul, smul_neg]

theorem e7T3_conj_eps {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {n : ModGL Tag.E7 L}
    {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) (v : WeylGroup Tag.E7)
    (α : Fin Tag.E7.rank → ℤ) :
    (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α =
      ε • ((v⁻¹ * (coxeterSystem Tag.E7).wordProd e7T3Word * v) • α) := by
  have h1 : ∀ x, weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • x =
      ε • ((coxeterSystem Tag.E7).wordProd e7T3Word • x) := fun x => by
    rw [hnW, e7T3_weylImage, Matrix.smul_mulVec]
  rw [mul_smul, mul_smul, mul_smul, mul_smul, h1, weyl_smul_zsmul_pm _ hε]

theorem e7T3_comp_eps {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {n : ModGL Tag.E7 L}
    {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) :
    (coxeterSystem Tag.E7).wordProd cm.u ∈ parabolicWeylGroup Tag.E7 (e7T3J cm.kind) ∧
      ∀ α ∈ parabolicRoots Tag.E7 (e7T3J cm.kind),
        (((coxeterSystem Tag.E7).wordProd w)⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ *
          (coxeterSystem Tag.E7).wordProd w) • α =
          ε • ((coxeterSystem Tag.E7).wordProd cm.u • permLattice (e7T3Beta cm.kind cm.rot) α) := by
  obtain ⟨hg, hact⟩ := comp_action h
  exact ⟨hg, fun α hα => by rw [e7T3_conj_eps hε hnW, hact α hα]⟩

theorem sigmaFactor_toSigma_E7
    {n : ModGL Tag.E7 L} {Fr : L →+* L} {S : Set (Fin Tag.E7.rank → ℤ)}
    (hS : ∀ r ∈ S, IsRoot Tag.E7 r) {P : Subgroup (ModGL Tag.E7 L)}
    (h : SigmaFactor n Fr S (fun _ : Unit => P)
      (Subgroup.normalizer (rootSpan Tag.E7 L S : Set (ModGL Tag.E7 L)))) :
    IsSigmaFamily n Fr S (fun _ : Unit => P) :=
  h.toSigma (sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)
    Subgroup.le_normalizer)

theorem sigmaFactor_union_E7 {S₁ S₂ : Set (Fin Tag.E7.rank → ℤ)}
    (hS₁ : ∀ r ∈ S₁, IsRoot Tag.E7 r) (hS₂ : ∀ r ∈ S₂, IsRoot Tag.E7 r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, iform (τ := Tag.E7) α β = 0)
    {n : ModGL Tag.E7 L} {Fr : L →+* L} {P₁ P₂ : Subgroup (ModGL Tag.E7 L)}
    (h₁ : SigmaFactor n Fr S₁ (fun _ : Unit => P₁)
      (Subgroup.normalizer (rootSpan Tag.E7 L S₁ : Set (ModGL Tag.E7 L))))
    (h₂ : SigmaFactor n Fr S₂ (fun _ : Unit => P₂)
      (Subgroup.normalizer (rootSpan Tag.E7 L S₂ : Set (ModGL Tag.E7 L)))) :
    IsSigmaFamily n Fr (S₁ ∪ S₂) (Sum.elim (fun _ : Unit => P₁) (fun _ : Unit => P₂)) := by
  have horth' : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 :=
    fun α hα β hβ => by
      rw [dotProduct_mulVec_eq_iform]
      exact horth α hα β hβ
  have hU := SigmaFactor.union (Or.inr (Or.inr (Or.inl rfl))) hS₁ hS₂ horth' h₁ h₂
  exact hU.toSigma (torus_sup_union_le_normalizers (Or.inr (Or.inr (Or.inl rfl))) hS₁ hS₂ horth')

theorem isRoot_image_parabolicRoots (v : WeylGroup Tag.E7) (J : Set (Fin Tag.E7.rank)) :
    ∀ r ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 J, IsRoot Tag.E7 r := by
  rintro _ ⟨α, hα, rfl⟩
  exact IsRoot.smul hα.1 v

end Helpers

section RootSets

theorem e7T3_rootSet_single
    {c : E7T3Cert} {cm : E7T3Comp} (hc : c.comps = [cm]) (hk : cm.kind < 4) :
    {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} =
      (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
        parabolicRoots Tag.E7 (e7T3J cm.kind) := by
  ext α
  have hk' : ∀ cm' ∈ c.comps, cm'.kind < 4 := by
    rw [hc]
    intro cm' hcm'
    rw [List.mem_singleton.1 hcm']
    exact hk
  refine (mem_rootList_iff hk' α).trans ?_
  rw [hc]
  constructor
  · rintro ⟨cm', hcm', γ, hγ, rfl⟩
    rw [List.mem_singleton.1 hcm'] at hγ
    exact ⟨γ, hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨cm, List.mem_singleton_self _, γ, hγ, rfl⟩

theorem e7T3_rootSet_two
    {c : E7T3Cert} {cm₀ cm₁ : E7T3Comp} (hc : c.comps = [cm₀, cm₁]) (hk₀ : cm₀.kind < 4)
    (hk₁ : cm₁.kind < 4) :
    {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} =
      (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm₀.kind) ∪
        (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm₁.kind) := by
  ext α
  have hk' : ∀ cm' ∈ c.comps, cm'.kind < 4 := by
    rw [hc]
    intro cm' hcm'
    rcases List.mem_cons.1 hcm' with rfl | h
    · exact hk₀
    · rw [List.mem_singleton.1 h]
      exact hk₁
  refine (mem_rootList_iff hk' α).trans ?_
  rw [hc]
  constructor
  · rintro ⟨cm', hcm', γ, hγ, rfl⟩
    rcases List.mem_cons.1 hcm' with rfl | h
    · exact Or.inl ⟨γ, hγ, rfl⟩
    · rw [List.mem_singleton.1 h] at hγ
      exact Or.inr ⟨γ, hγ, rfl⟩
  · rintro (⟨γ, hγ, rfl⟩ | ⟨γ, hγ, rfl⟩)
    · exact ⟨cm₀, List.mem_cons_self, γ, hγ, rfl⟩
    · exact ⟨cm₁, List.mem_cons_of_mem _ (List.mem_singleton_self _), γ, hγ, rfl⟩

theorem e7_e0_eq_toVec : (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) =
    toVec Tag.E7.rank [1, 0, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> rfl

theorem e7_e0_not_mem_of_kind_one {c : E7T3Cert}
    (hc : c ∈ e7T3Certs) (hgood : c.Good) (hk : c.comps.map E7T3Comp.kind = [1]) :
    (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) ∉
      {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} := by
  rintro ⟨l, hl, he⟩
  rw [e7_e0_eq_toVec] at he
  have hlen : l.length = Tag.E7.rank := length_of_mem_artifactRoots (hgood.2.2.1 l hl)
  have hlen' : ([1, 0, 0, 0, 0, 0, 0] : List ℤ).length = Tag.E7.rank := rfl
  have hl1 : ([1, 0, 0, 0, 0, 0, 0] : List ℤ) = l := toVec_injective_of_length hlen' hlen he
  exact e7T3_cert_e0 hc hk (by rw [hl1]; exact hl)

end RootSets

section Kinds

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7T3_layer_A2 (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 0) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
            parabolicRoots Tag.E7 (e7T3J cm.kind)) : Set (ModGL Tag.E7 L))) ∧
      ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L (e7Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps hε hnW h
  have hg' : (coxeterSystem Tag.E7).wordProd cm.u ∈ parabolicWeylGroup Tag.E7 support13 := by
    rw [hkind] at hg
    exact hg
  obtain ⟨P, -, hfac, h₀, hh₀⟩ := e7_a2_factor hf hk hε hq2 ((coxeterSystem Tag.E7).wordProd w) n
    hnm ((coxeterSystem Tag.E7).wordProd cm.u) hg' (fun α hα => by
      have h1 := hact α (by rw [hkind]; exact hα)
      rw [h1, hkind]
      simp [e7T3Beta, permLattice_one])
  rw [hkind]
  exact ⟨P, hfac, h₀, hh₀⟩

theorem e7T3_layer_A1 (hf : 1 ≤ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 1) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
            parabolicRoots Tag.E7 (e7T3J cm.kind)) : Set (ModGL Tag.E7 L))) := by
  obtain ⟨-, hact⟩ := e7T3_comp_eps hε hnW h
  have hu : cm.u = [] := h.2.2.1 hkind
  rw [hkind]
  exact e7_a1_factor hf hε ((coxeterSystem Tag.E7).wordProd w) n hnm cm.rot (fun α hα => by
    have h1 := hact α (by rw [hkind]; exact hα)
    rw [h1, hu, hkind]
    cases cm.rot <;> simp [e7T3Beta])

theorem e7T3_layer_A5 (hA5 : A5Layer Tag.E7) (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L]
    [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnC : n ∈ adjointGroup Tag.E7 L)
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 3) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
            parabolicRoots Tag.E7 (e7T3J cm.kind)) : Set (ModGL Tag.E7 L))) ∧
      ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L (e7Index 3)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps hε hnW h
  have hg' : (coxeterSystem Tag.E7).wordProd cm.u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7) := by
    rw [hkind] at hg
    exact hg
  rw [hkind]
  exact e7_a5_factor hA5 hf hk hε hq2 ((coxeterSystem Tag.E7).wordProd w) n hnm hnC
    ⟨(coxeterSystem Tag.E7).wordProd cm.u, hg', fun α hα => by
      have h1 := hact α (by rw [hkind]; exact hα)
      rw [h1, hkind, weyl_smul_zsmul_pm _ hε]
      simp [e7T3Beta, permLattice_one]⟩

theorem e7T3NegD4_nodes : ∀ x ∈ e7T3NegD4, x.val ∈ e7T3Nodes 2 := by
  decide

theorem e7T3_layer_D4 (hD4 : D4TrialityLayer Tag.E7) (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {n : ModGL Tag.E7 L} {hnm : n ∈ monomialSubgroup Tag.E7 L}
    (hnC : n ∈ adjointGroup Tag.E7 L)
    (hnW : ∀ u : Fin Tag.E7.rank → ℤ,
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) {cm : E7T3Comp}
    {w : List (Fin Tag.E7.rank)} (h : cm.Good e7T3Word w) (hkind : cm.kind = 2)
    (hneg : ε = -1 → ∀ l ∈ e7StdRoots (e7T3Nodes 2),
      lmulVec 7 (e7wl (e7T3NegD4 ++ cm.u)) (e7T3Perm 2 cm.rot l) =
        vneg 7 (lmulVec 7 (e7wl cm.u) (e7T3Perm 2 cm.rot l))) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm.kind)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => (coxeterSystem Tag.E7).wordProd w • γ) ''
            parabolicRoots Tag.E7 (e7T3J cm.kind)) : Set (ModGL Tag.E7 L))) ∧
      ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L (e7Index 3)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨hg, hact⟩ := e7T3_comp_eps hε hnW h
  have hu : ∀ x ∈ cm.u, x ∈ d4Nodes Tag.E7 := fun x hx => by
    have := (mem_e7T3J_iff (by omega : cm.kind < 4) x).2 (h.1 x hx)
    rw [hkind] at this
    exact this
  have hcertD4 : ∃ u ∈ parabolicWeylGroup Tag.E7 (d4Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7),
        (((coxeterSystem Tag.E7).wordProd w)⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ *
          (coxeterSystem Tag.E7).wordProd w) • α =
          u • permLattice (e7T3Beta cm.kind cm.rot) α := by
    rcases hε with rfl | rfl
    · refine ⟨(coxeterSystem Tag.E7).wordProd cm.u, ?_, fun α hα => ?_⟩
      · rw [hkind] at hg
        exact hg
      · rw [hact α (by rw [hkind]; exact hα), one_smul]
    · refine ⟨(coxeterSystem Tag.E7).wordProd (e7T3NegD4 ++ cm.u), ?_, fun α hα => ?_⟩
      · refine wordProd_mem_parabolicWeylGroup fun x hx => ?_
        rcases List.mem_append.1 hx with hx | hx
        · exact (mem_e7T3J_iff (by norm_num : (2 : ℕ) < 4) x).2 (e7T3NegD4_nodes x hx)
        · exact hu x hx
      · have hα' : α ∈ parabolicRoots Tag.E7 (e7T3J 2) := hα
        rw [parabolicRoots_e7T3J (by norm_num : (2 : ℕ) < 4)] at hα'
        obtain ⟨l, hl, rfl⟩ := hα'
        have h1 := hact (toVec Tag.E7.rank l) (by
          rw [hkind, parabolicRoots_e7T3J (by norm_num : (2 : ℕ) < 4)]
          exact ⟨l, hl, rfl⟩)
        have hneg' : lmulVec Tag.E7.rank (e7wl (e7T3NegD4 ++ cm.u)) (e7T3Perm 2 cm.rot l) =
            vneg Tag.E7.rank (lmulVec Tag.E7.rank (e7wl cm.u) (e7T3Perm 2 cm.rot l)) :=
          hneg rfl l hl
        rw [h1, hkind, e7T3_permLattice (by norm_num : (2 : ℕ) < 4),
          wordProd_smul_toVec7 cm.u, wordProd_smul_toVec7 (e7T3NegD4 ++ cm.u), hneg',
          toVec_vneg, neg_one_smul]
  rw [hkind] at hcertD4 ⊢
  rcases hr : cm.rot with _ | _
  · have hβ : e7T3Beta 2 cm.rot = List.formPerm [(1 : Fin Tag.E7.rank), 2, 4] := by
      rw [hr]
      rfl
    rw [hβ] at hcertD4
    obtain ⟨P, -, hfac, hsl⟩ := e7_d4_factor hD4 hf hk ((coxeterSystem Tag.E7).wordProd w) n hnm
      hnC 1 2 4 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hcertD4
    exact ⟨P, hfac, hsl⟩
  · have hβ : e7T3Beta 2 cm.rot = List.formPerm [(1 : Fin Tag.E7.rank), 4, 2] := by
      rw [hr]
      rfl
    rw [hβ] at hcertD4
    obtain ⟨P, -, hfac, hsl⟩ := e7_d4_factor hD4 hf hk ((coxeterSystem Tag.E7).wordProd w) n hnm
      hnC 1 4 2 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hcertD4
    exact ⟨P, hfac, hsl⟩

end Kinds

section Main

theorem e7T3_orth_A2_A1 :
    ∀ l ∈ e7StdRoots (e7T3Nodes 0), ∀ l' ∈ e7StdRoots (e7T3Nodes 1),
      iform (τ := Tag.E7) (toVec Tag.E7.rank l) (toVec Tag.E7.rank l') = 0 := by
  decide +kernel

theorem e7ThreeLayers (hD4 : D4TrialityLayer Tag.E7)
    (hA5 : A5Layer Tag.E7) : E7ThreeLayers := by
  classical
  intro L _ _ ℓ f _ _ hf k _ _ _ hk ε hε hq2 n hnm hnC hnW c hc hgood
  have hcomps := hgood.1
  have hkinds := e7T3_cert_kinds hc
  have hlt : ∀ cm ∈ c.comps, cm.kind < 4 := fun cm hcm => (hcomps cm hcm).2.1
  rcases hcc : c.comps with _ | ⟨cm₀, _ | ⟨cm₁, _ | ⟨cm₂, rest⟩⟩⟩
  · rw [hcc] at hkinds
    simp at hkinds
  · rw [hcc] at hkinds hcomps hlt
    have hg₀ : cm₀.Good e7T3Word c.w := hcomps cm₀ (List.mem_singleton_self _)
    have hk₀ : cm₀.kind < 4 := hlt cm₀ (List.mem_singleton_self _)
    have hset := e7T3_rootSet_single hcc hk₀
    have hkind : cm₀.kind = 0 ∨ cm₀.kind = 1 ∨ cm₀.kind = 2 ∨ cm₀.kind = 3 := by
      simpa using hkinds
    rcases hkind with h0 | h1 | h2 | h3
    · obtain ⟨P, hfac, h₀, hh₀⟩ := e7T3_layer_A2 hf hk hε hq2 hnW hg₀ h0
      rw [hset]
      exact ⟨Unit, fun _ => P, sigmaFactor_toSigma_E7 (isRoot_image_parabolicRoots _ _) hfac,
        fun _ => ⟨(), e7Index 0, h₀, hh₀⟩⟩
    · obtain ⟨P, hfac⟩ := e7T3_layer_A1 hf hε hnW hg₀ h1
      have hnot := e7_e0_not_mem_of_kind_one hc hgood (by rw [hcc]; simp [h1])
      rw [hset] at hnot ⊢
      exact ⟨Unit, fun _ => P, sigmaFactor_toSigma_E7 (isRoot_image_parabolicRoots _ _) hfac,
        fun he => absurd he hnot⟩
    · obtain ⟨P, hfac, h₀, hh₀⟩ := e7T3_layer_D4 hD4 hf hk hε hnC hnW hg₀ h2 (fun _ =>
        e7T3_cert_negD4 hc (by rw [hcc]; exact List.mem_singleton_self _) h2)
      rw [hset]
      exact ⟨Unit, fun _ => P, sigmaFactor_toSigma_E7 (isRoot_image_parabolicRoots _ _) hfac,
        fun _ => ⟨(), e7Index 3, h₀, hh₀⟩⟩
    · obtain ⟨P, hfac, h₀, hh₀⟩ := e7T3_layer_A5 hA5 hf hk hε hq2 hnC hnW hg₀ h3
      rw [hset]
      exact ⟨Unit, fun _ => P, sigmaFactor_toSigma_E7 (isRoot_image_parabolicRoots _ _) hfac,
        fun _ => ⟨(), e7Index 3, h₀, hh₀⟩⟩
  · rw [hcc] at hkinds hcomps hlt
    have hg₀ : cm₀.Good e7T3Word c.w := hcomps cm₀ (List.mem_cons_self)
    have hg₁ : cm₁.Good e7T3Word c.w :=
      hcomps cm₁ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have hk₀ : cm₀.kind < 4 := hlt cm₀ (List.mem_cons_self)
    have hk₁ : cm₁.kind < 4 := hlt cm₁ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have hkk : cm₀.kind = 0 ∧ cm₁.kind = 1 := by simpa using hkinds
    obtain ⟨P₀, hfac₀, h₀, hh₀⟩ := e7T3_layer_A2 hf hk hε hq2 hnW hg₀ hkk.1
    obtain ⟨P₁, hfac₁⟩ := e7T3_layer_A1 hf hε hnW hg₁ hkk.2
    rw [e7T3_rootSet_two hcc hk₀ hk₁]
    have horth : ∀ α ∈ (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm₀.kind),
        ∀ β ∈ (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
          parabolicRoots Tag.E7 (e7T3J cm₁.kind), iform (τ := Tag.E7) α β = 0 := by
      rintro _ ⟨α', hα', rfl⟩ _ ⟨β', hβ', rfl⟩
      rw [iform_smul]
      rw [hkk.1, parabolicRoots_e7T3J (by norm_num : (0 : ℕ) < 4)] at hα'
      rw [hkk.2, parabolicRoots_e7T3J (by norm_num : (1 : ℕ) < 4)] at hβ'
      obtain ⟨l, hl, rfl⟩ := hα'
      obtain ⟨l', hl', rfl⟩ := hβ'
      exact e7T3_orth_A2_A1 l hl l' hl'
    exact ⟨Unit ⊕ Unit, Sum.elim (fun _ => P₀) (fun _ => P₁),
      sigmaFactor_union_E7 (isRoot_image_parabolicRoots _ _) (isRoot_image_parabolicRoots _ _)
        horth hfac₀ hfac₁, fun _ => ⟨Sum.inl (), e7Index 0, h₀, hh₀⟩⟩
  · rw [hcc] at hkinds
    simp at hkinds

end Main

end CFSG.RankThree.PartOne.KE
