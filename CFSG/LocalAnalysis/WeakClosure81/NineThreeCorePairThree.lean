module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairBrThree
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairHp
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairInj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_pair_three (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) (hUS : ¬ U ≤ S) {w : G} (hw : w ∈ U ⊓ pCoreOf 2 K)
    (hcard : Nat.card ↥(nineDelta V S) = 3) :
    ∀ h ∈ nineH V K, ⁅h, g⁻¹ * w * g⁆ ∈ nineI V K := by
  classical
  obtain ⟨n, B, σ, bb, _hn, hΔ, he⟩ := nine3_pair_exists_enum hc h35
  have hn2 : n = 2 := by omega
  subst n
  let T₁ : Subgroup G := U ⊓ pCoreOf 2 K
  let T₂ : Subgroup G := conjSubgroup T₁ g
  let W : Subgroup G := nineW V S
  let P : Fin 3 → Subgroup G := nine3_pair_P V K g B
  let φ : Fin 3 → G → G := fun k i => ⁅i, bb k⁆
  let ψ : Fin 3 → G → G := fun l j => ⁅g⁻¹ * bb (σ.symm l) * g, j⁆
  let β : G → G → G := fun i j => ⁅i, j⁆
  have hT₁le : T₁ ≤ nineI V K := le_iSup₂_of_le U hU le_rfl
  have hT₂le : T₂ ≤ conjSubgroup (nineI V K) g := E3.conjSubgroup_mono_left g hT₁le
  have hT₂leU : T₂ ≤ conjSubgroup U g := E3.conjSubgroup_mono_left g (inf_le_left : T₁ ≤ U)
  have hIabelian' : IsElemAbelian 2 (conjSubgroup (nineI V K) g) :=
    isElemAbelian_conjSubgroup' hI.abelian g
  have hT₁ : ∀ a ∈ T₁, ∀ b ∈ T₁, a * b = b * a := fun a ha b hb =>
    CFSG.Open.IsElemAbelian.comm hI.abelian (hT₁le ha) (hT₁le hb)
  have hT₁sq : ∀ a ∈ T₁, a * a = 1 := fun a ha => by
    have h := hI.abelian.2 a (hT₁le ha)
    simpa [pow_two] using h
  have hT₂ : ∀ a ∈ T₂, ∀ b ∈ T₂, a * b = b * a := fun a ha b hb =>
    CFSG.Open.IsElemAbelian.comm hIabelian' (hT₂le ha) (hT₂le hb)
  have hT₂sq : ∀ a ∈ T₂, a * a = 1 := fun a ha => by
    have h := hIabelian'.2 a (hT₂le ha)
    simpa [pow_two] using h
  have hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    hc.core.nineW_mul_comm ha hb
  have hWsq : ∀ a ∈ W, a * a = 1 := fun a ha => by
    have h := hc.core.nineW_isElemAbelian.2 a ha
    simpa [pow_two] using h
  have hPW : ∀ k, P k ≤ W := fun k => nine3_pair_P_le_W hc he.mem k
  have hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥ :=
    nine3_pair_P_disjoint hc he.B0 he.inj he.mem
  have hβ : ∀ i ∈ T₁, ∀ j ∈ T₂, β i j ∈ W := fun i hi j hj =>
    nine3_pair_beta_mem hc hc' hI (hT₁le hi) (hT₂le hj)
  have hφmul : ∀ k, ∀ i ∈ T₁, ∀ i' ∈ T₁, φ k (i * i') = φ k i * φ k i' := by
    intro k i hi i' hi'
    have hk : bb k ∈ K := by
      by_cases hk0 : k = 0
      · rw [hk0, he.bb0]; exact K.one_mem
      · exact ((he.mem k).2.trans hc.core.S_le_K) (he.bb_mem k hk0).1
    exact nine3_pair_phi_mul hI (hT₁le hi) (hT₁le hi') hk
  have hψmul : ∀ l, ∀ j ∈ T₂, ∀ j' ∈ T₂, ψ l (j * j') = ψ l j * ψ l j' := by
    intro l j hj j' hj'
    have hk : bb (σ.symm l) ∈ K := by
      by_cases hl : σ.symm l = 0
      · rw [hl, he.bb0]; exact K.one_mem
      · exact ((he.mem (σ.symm l)).2.trans hc.core.S_le_K)
          (he.bb_mem (σ.symm l) hl).1
    exact nine3_pair_psi_mul hI hk (hT₂le hj) (hT₂le hj')
  have hφ0 : ∀ i ∈ T₁, φ 0 i = 1 := by
    intro i _
    change ⁅i, bb 0⁆ = 1
    rw [he.bb0, commutatorElement_one_right]
  have hψ1 : ∀ j ∈ T₂, ψ 1 j = 1 := by
    intro j _
    have hσ : σ.symm 1 = 0 := by
      rw [Equiv.symm_apply_eq]; exact he.σ0.symm
    have h1 : g⁻¹ * bb (σ.symm 1) * g = 1 := by rw [hσ, he.bb0]; group
    change ⁅g⁻¹ * bb (σ.symm 1) * g, j⁆ = 1
    rw [h1, commutatorElement_one_left]
  have hφP : ∀ k, ∀ i ∈ T₁, φ k i ∈ P k := fun k i hi =>
    nine3_pair_phi_mem hI he (hT₁le hi) k
  have hψP : ∀ l, ∀ j ∈ T₂, ψ l j ∈ P l := fun l j hj =>
    nine3_pair_psi_mem hc hI he (hT₂le hj) l
  have iφ : ∀ k, k ≠ 0 → ∀ i ∈ T₁, i ≠ 1 → φ k i ≠ 1 := by
    intro k hk i hi hi1
    exact nine3_pair_phi_inj hc he hU hUS ((inf_le_left : T₁ ≤ U) hi) hi1 hk
  have iψ : ∀ l, l ≠ 1 → ∀ j ∈ T₂, j ≠ 1 → ψ l j ≠ 1 := by
    intro l hl j hj hj1
    exact nine3_pair_psi_inj hc he hU hUS (hT₂leU hj) hj1 hl
  have hnt : ∃ i ∈ T₁, i ≠ 1 := by
    obtain ⟨i₁, _i₂, hi₁, _hi₂, _hi₁₂⟩ := nine3_pair_rank hc hU
    exact ⟨(i₁ : G), i₁.2, fun h => hi₁ (Subtype.ext h)⟩
  have hrank : ∃ j₁ ∈ T₂, ∃ j₂ ∈ T₂, j₁ ≠ 1 ∧ j₂ ≠ 1 ∧ j₁ ≠ j₂ := by
    obtain ⟨i₁, i₂, hi₁, hi₂, hi₁₂⟩ := nine3_pair_rank hc hU
    let j₁ : G := g⁻¹ * (i₁ : G) * g
    let j₂ : G := g⁻¹ * (i₂ : G) * g
    have hj₁T : j₁ ∈ T₂ := by
      rw [mem_conjSubgroup_iff]
      have h : g * j₁ * g⁻¹ = (i₁ : G) := by simp only [j₁]; group
      rw [h]; exact i₁.2
    have hj₂T : j₂ ∈ T₂ := by
      rw [mem_conjSubgroup_iff]
      have h : g * j₂ * g⁻¹ = (i₂ : G) := by simp only [j₂]; group
      rw [h]; exact i₂.2
    have hj₁ne : j₁ ≠ 1 := by
      intro h
      apply hi₁
      apply Subtype.ext
      calc (i₁ : G) = g * j₁ * g⁻¹ := by simp only [j₁]; group
        _ = g * 1 * g⁻¹ := by rw [h]
        _ = 1 := by group
    have hj₂ne : j₂ ≠ 1 := by
      intro h
      apply hi₂
      apply Subtype.ext
      calc (i₂ : G) = g * j₂ * g⁻¹ := by simp only [j₂]; group
        _ = g * 1 * g⁻¹ := by rw [h]
        _ = 1 := by group
    have hj₁₂ : j₁ ≠ j₂ := by
      intro h
      apply hi₁₂
      apply Subtype.ext
      calc (i₁ : G) = g * j₁ * g⁻¹ := by simp only [j₁]; group
        _ = g * j₂ * g⁻¹ := by rw [h]
        _ = (i₂ : G) := by simp only [j₂]; group
    exact ⟨j₁, hj₁T, j₂, hj₂T, hj₁ne, hj₂ne, hj₁₂⟩
  have hs : ∀ j ∈ T₂, ∃ ε : Fin 3 → Bool, ∀ i ∈ T₁,
      β i j = ((List.finRange 3).map fun k => if ε k then φ k i else 1).prod := by
    intro j hj
    obtain ⟨b, _hbZ, ε, _hε0, ⟨_j₀, _hj₀I, _hb_eq⟩, _hbH, _hbI, hexp⟩ :=
      nine3_pair_hs hc hc' hI h35 he.Ω he.surj he.bb_mem he.bb0 (hT₂le hj)
    exact ⟨ε, fun i hi => hexp i (hT₁le hi)⟩
  have hp : ∀ i ∈ T₁, ∃ π : Fin 3 → Bool, ∀ j ∈ T₂,
      β i j = ((List.finRange 3).map fun l => if π l then ψ l j else 1).prod := by
    intro i hi
    obtain ⟨π, hπ⟩ := nine3_pair_hp hc hc' hI h35 he (hT₁le hi)
    exact ⟨π, fun j hj => hπ j (hT₂le hj)⟩
  have hbridge := nine3_bridge_three (T₁ := T₁) (T₂ := T₂) (W := W)
    hT₁ hT₁sq hT₂ hT₂sq hW hWsq P hPW hP φ ψ hφmul hψmul hφ0 hψ1 hφP hψP
    iφ iψ hnt hrank β hβ hs hp
  intro h hh
  let j : G := g⁻¹ * w * g
  have hjT₂ : j ∈ T₂ := by
    rw [mem_conjSubgroup_iff]
    have hgw : g * j * g⁻¹ = w := by simp only [j]; group
    rw [hgw]; exact hw
  obtain ⟨b, hbZ, ε, hε0, ⟨j₀, hj₀I, hb_eq⟩, hbH, _hbI, hexp⟩ :=
    nine3_pair_hs hc hc' hI h35 he.Ω he.surj he.bb_mem he.bb0 (hT₂le hjT₂)
  have hrep : ∀ i ∈ T₁, β i j =
      ((List.finRange 3).map fun k => if ε k then φ k i else 1).prod :=
    fun i hi => hexp i (hT₁le hi)
  have hbε := hbridge j hjT₂ ε hrep
  have hεall : ∀ k : Fin 3, ε k = false := by
    intro k
    fin_cases k
    · exact hε0
    · exact hbε.1
    · exact hbε.2
  have hprod1 : ((List.finRange (2 + 1)).map fun k => if ε k then bb k else 1).prod = 1 :=
    List.prod_eq_one fun x hx => by
      obtain ⟨k, _hk, rfl⟩ := List.mem_map.mp hx
      rw [hεall k]
      simp
  have hb_mem_I : b ∈ nineI V K := by
    rw [hb_eq, hprod1, mul_one]
    exact hj₀I
  have hHK : nineH V K ≤ K := iSup₂_le fun _ hU => hU.2
  have hb : ∀ h ∈ nineH V K, ⁅b, h⁆ ∈ nineI V K := by
    intro h hh
    have hhK : h ∈ K := hHK hh
    have hconj : h * b * h⁻¹ ∈ nineI V K := by
      have hx : b ∈ conjSubgroup (nineI V K) h := by
        rw [Nine3Core.conjSubgroup_nineI hhK]; exact hb_mem_I
      exact mem_conjSubgroup_iff.mp hx
    have hinv : h * b⁻¹ * h⁻¹ ∈ nineI V K := by
      simpa [mul_inv_rev, inv_inv, mul_assoc] using (nineI V K).inv_mem hconj
    have hprod := (nineI V K).mul_mem hb_mem_I hinv
    simpa [commutatorElement_def, mul_assoc] using hprod
  have hZK : nineZ V K S ≤ K := iSup₂_le fun B hB => hc.core.nineOmegaIn_le_K hB
  have hbK : b ∈ K := hZK hbZ
  have hjK : j ∈ K := hc.core.S_le_K (hc'.conj_nineI_le_S hI (hT₂le hjT₂))
  exact nine3_pair_final hbK hjK hb hbH h hh

end CFSG.LocalAnalysis.WeakClosure81
