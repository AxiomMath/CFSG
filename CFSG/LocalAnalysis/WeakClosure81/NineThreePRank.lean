module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeRank
public import CFSG.LocalAnalysis.WeakClosure81.NineThreePFix
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_conj_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

theorem conjSubgroup_nineD (K A : Subgroup G) (x : G) {r : G} (hr : r ∈ pCoreOf 2 K) :
    conjSubgroup (nineD K A x) r = nineD K A x := by
  have hle : ∀ s ∈ pCoreOf 2 K, conjSubgroup (nineD K A x) s ≤ nineD K A x := by
    intro s hs
    have hsK : s ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hs
    unfold nineD
    rw [E3.conjSubgroup_inf, nineThree_conj_iSup, Nine3Core.conjSubgroup_pCoreOf K hsK]
    refine le_inf (inf_le_left.trans ?_) inf_le_right
    refine iSup_le fun r' => ?_
    rw [nineThree_conj_iSup]
    refine iSup_le fun hr' => ?_
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
    refine le_iSup₂_of_le (r' * s) ((pCoreOf 2 K).mul_mem hr' hs) ?_
    exact le_of_eq (by rw [show (x * r') * s = x * (r' * s) by group])
  refine le_antisymm (hle r hr) ?_
  calc nineD K A x = conjSubgroup (conjSubgroup (nineD K A x) r⁻¹) r :=
        (nineThree_conj_inv' (nineD K A x) r).symm
    _ ≤ conjSubgroup (nineD K A x) r :=
        E3.conjSubgroup_mono_left r (hle r⁻¹ ((pCoreOf 2 K).inv_mem hr))

namespace Nine3Core

theorem mul_mem_nineDp (h : Nine3Core V T A K S X p) (hx : x ∈ X) {B₁ B₂ : Subgroup G}
    (hB₁ : B₁ ∈ nineOmegaIn V K S) (hB₂ : B₂ ∈ nineOmegaIn V K S) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂) (hb₁R : b₁ ∉ pCoreOf 2 K) (hb₂R : b₂ ∉ pCoreOf 2 K) :
    b₁ * b₂ ∈ nineDp K A x := by
  rw [h.nineDp_eq hx]
  refine ⟨?_, ?_⟩
  · have h₁ : b₁ ∈ nineZ V K S :=
      (le_iSup₂_of_le (f := fun B (_ : B ∈ nineOmegaIn V K S) => B) B₁ hB₁ le_rfl) hb₁
    have h₂ : b₂ ∈ nineZ V K S :=
      (le_iSup₂_of_le (f := fun B (_ : B ∈ nineOmegaIn V K S) => B) B₂ hB₂ le_rfl) hb₂
    exact (nineZ V K S).mul_mem h₁ h₂
  · have hb₁iR : b₁⁻¹ ∉ pCoreOf 2 K :=
      fun hh => hb₁R (by simpa using (pCoreOf 2 K).inv_mem hh)
    have h1 := h.nineOmegaIn_inv_mul_mem_cross hB₁ hB₂ (B₁.inv_mem hb₁) hb₂ hb₁iR hb₂R
    simpa using h1

end Nine3Core

namespace Nine3Choice

theorem commutator_nineDp_nineD_mem (hc : Nine3Choice V T A K S X p g x) {d' d : G}
    (hd' : d' ∈ nineDp K A x) (hd : d ∈ nineD K A x) :
    d' * d * d'⁻¹ * d⁻¹ ∈ nineD K A x ⊓ nineDp K A x := by
  have hd'R : d' ∈ pCoreOf 2 K := ((hc.core.nineDp_eq hc.x_mem).symm ▸ hd').2
  have hmemD : d' * d * d'⁻¹ ∈ nineD K A x := by
    have hconj := conjSubgroup_nineD K A x hd'R
    have : d ∈ conjSubgroup (nineD K A x) d' := by rw [hconj]; exact hd
    exact mem_conjSubgroup_iff.mp this
  refine ⟨(nineD K A x).mul_mem hmemD ((nineD K A x).inv_mem hd), ?_⟩
  have hmemD' : d * d'⁻¹ * d⁻¹ ∈ nineDp K A x :=
    (Subgroup.mem_normalizer_iff.mp (hc.nineD_le_normalizer_nineDp hd) d'⁻¹).mp
      ((nineDp K A x).inv_mem hd')
  rw [show d' * d * d'⁻¹ * d⁻¹ = d' * (d * d'⁻¹ * d⁻¹) by group]
  exact (nineDp K A x).mul_mem hd' hmemD'

end Nine3Choice

theorem nineThree_exists_four {Ω₀ : Set (Subgroup G)} {D : Subgroup G}
    (htrans : ∀ B ∈ Ω₀, ∀ B' ∈ Ω₀, ∃ d ∈ D, B' = conjSubgroup B d)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hsq : ∀ a ∈ D, a * a = 1)
    (h3 : 3 ≤ Nat.card Ω₀) :
    ∃ d ∈ D, ∃ B₁ ∈ Ω₀, ∃ B₂ ∈ Ω₀, B₁ ≠ B₂ ∧ B₁ ≠ conjSubgroup B₁ d ∧
      B₁ ≠ conjSubgroup B₂ d ∧ B₂ ≠ conjSubgroup B₁ d ∧ B₂ ≠ conjSubgroup B₂ d ∧
      conjSubgroup B₁ d ≠ conjSubgroup B₂ d := by
  classical
  have h3' : 3 ≤ Ω₀.ncard := by simpa using h3
  have hcard : 2 < Ω₀.ncard := by omega
  obtain ⟨B₁, hB₁, B', hB', B₂, hB₂, hB₁B', hB₁B₂, hB'B₂⟩ :=
    (Set.two_lt_ncard (s := Ω₀)).mp hcard
  obtain ⟨d, hd, hdB'⟩ := htrans B₁ hB₁ B' hB'
  have hdd : ∀ B ∈ Ω₀, conjSubgroup (conjSubgroup B d) d = B := by
    intro B _
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, hsq d hd,
      CFSG.Quasithin.conjSubgroup_one]
  have hfix : ∀ B ∈ Ω₀, conjSubgroup B d ≠ B := by
    intro B hB hBd
    obtain ⟨e, he, heB⟩ := htrans B₁ hB₁ B hB
    have h1 : conjSubgroup (conjSubgroup B₁ e) d = conjSubgroup B₁ e := by
      rw [← heB]; exact hBd
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup] at h1
    have h2 := congrArg (fun C => conjSubgroup C e⁻¹) h1
    rw [nineThree_conj_inv, CFSG.Quasithin.conjSubgroup_conjSubgroup] at h2
    have hee : (e * d) * e⁻¹ = d := by rw [hcomm e he d hd]; group
    rw [hee, ← hdB'] at h2
    exact hB₁B' h2.symm
  refine ⟨d, hd, B₁, hB₁, B₂, hB₂, hB₁B₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hdB']; exact hB₁B'
  · intro h
    have h2 : B₂ = B' := by
      have := hdd B₂ hB₂
      rw [this.symm, ← h, hdB']
    exact hB'B₂ h2.symm
  · rw [← hdB']; exact hB'B₂.symm
  · exact (hfix B₂ hB₂).symm
  · intro h
    exact hB₁B₂ (nineThree_conj_injective h)

namespace Nine3Choice

theorem card_nineDelta_le_five (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    Nat.card ↥(nineDelta V S) ≤ 5 := by
  classical
  by_contra hle
  push Not at hle
  obtain ⟨n, hΩ, hΔ⟩ := hc.core.card_nineOmegaIn
  have hxX := hc.x_mem
  have h25 : 5 ≤ 2 ^ n := by
    rw [hΔ] at hle
    omega
  have hn3 : 3 ≤ n := by
    by_contra h
    have hlt : n < 3 := by omega
    interval_cases n <;> omega
  have hΩ3 : 3 ≤ Nat.card ↥(nineOmegaIn V K S) := by
    rw [hΩ]
    exact le_trans (by norm_num : 3 ≤ 2 ^ 3)
      (pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hn3)
  have hΔ3 : 3 ≤ Nat.card ↥(nineDelta V S) := by
    rw [hΔ]; omega
  have h6 : 6 ≤ Nat.card ↥(nineDelta V S) := by omega
  have hW₀W : nineW0 V K S g ≤ nineW V S := hc.nineW0_le_nineW
  have hDab : IsElemAbelian 2 (nineD K A x) := hc.core.nineD_isElemAbelian hxX
  have hDcomm : ∀ a ∈ nineD K A x, ∀ b ∈ nineD K A x, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsqD : ∀ a ∈ nineD K A x, a * a = 1 := by
    intro a ha
    have := hDab.2 a ha
    rwa [pow_two] at this
  obtain ⟨d, hd, B₁, hB₁, B₂, hB₂, h₁₂, h₁B₁d, h₁B₂d, h₂B₁d, h₂B₂d, hB₁dB₂d⟩ :=
    nineThree_exists_four (Ω₀ := nineOmegaIn V K S) (D := nineD K A x)
      (fun B hB B' hB' => hc.core.nineD_transitive hxX hc.x_ne_one hB hB')
      hDcomm hsqD hΩ3
  have hdR : d ∈ pCoreOf 2 K := Nine3Core.nineD_le_pCoreOf hd
  have hB₂dΩ : conjSubgroup B₂ d ∈ nineOmegaIn V K S :=
    hc.core.conjSubgroup_mem_nineOmegaIn hB₂ hdR
  have hB₁dΩ : conjSubgroup B₁ d ∈ nineOmegaIn V K S :=
    hc.core.conjSubgroup_mem_nineOmegaIn hB₁ hdR
  have hB₁Δ : B₁ ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hB₁)
  have hB₂Δ : B₂ ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hB₂)
  have hB₃Δ : conjSubgroup B₂ d ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hB₂dΩ)
  have hB₄Δ : conjSubgroup B₁ d ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hB₁dΩ)
  have hB₁V : B₁ ≠ V := fun h => hc.core.V_not_mem_nineOmegaIn (h ▸ hB₁)
  have hB₂V : B₂ ≠ V := fun h => hc.core.V_not_mem_nineOmegaIn (h ▸ hB₂)
  have hB₃V : conjSubgroup B₂ d ≠ V := fun h => hc.core.V_not_mem_nineOmegaIn (h ▸ hB₂dΩ)
  have hB₄V : conjSubgroup B₁ d ≠ V := fun h => hc.core.V_not_mem_nineOmegaIn (h ▸ hB₁dΩ)
  obtain ⟨b₁, hb₁, hb₁R⟩ := hc.core.exists_not_mem_pCoreOf hB₁
  obtain ⟨b₂, hb₂, hb₂R⟩ := hc.core.exists_not_mem_pCoreOf hB₂
  let c₃ := d⁻¹ * b₂⁻¹ * d
  let c₄ := d⁻¹ * b₁⁻¹ * d
  have hc₃ : c₃ ∈ conjSubgroup B₂ d := by
    rw [mem_conjSubgroup_iff]
    have h : d * c₃ * d⁻¹ = b₂⁻¹ := by simp only [c₃]; group
    rw [h]; exact B₂.inv_mem hb₂
  have hc₄ : c₄ ∈ conjSubgroup B₁ d := by
    rw [mem_conjSubgroup_iff]
    have h : d * c₄ * d⁻¹ = b₁⁻¹ := by simp only [c₄]; group
    rw [h]; exact B₁.inv_mem hb₁
  have hc₃R : c₃ ∉ pCoreOf 2 K := by
    intro h
    apply hb₂R
    have h' : d * c₃ * d⁻¹ = b₂⁻¹ := by simp only [c₃]; group
    have hm : d * c₃ * d⁻¹ ∈ pCoreOf 2 K :=
      (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).mul_mem hdR h) ((pCoreOf 2 K).inv_mem hdR)
    rw [h'] at hm
    simpa using (pCoreOf 2 K).inv_mem hm
  have hc₄R : c₄ ∉ pCoreOf 2 K := by
    intro h
    apply hb₁R
    have h' : d * c₄ * d⁻¹ = b₁⁻¹ := by simp only [c₄]; group
    have hm : d * c₄ * d⁻¹ ∈ pCoreOf 2 K :=
      (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).mul_mem hdR h) ((pCoreOf 2 K).inv_mem hdR)
    rw [h'] at hm
    simpa using (pCoreOf 2 K).inv_mem hm
  have hb₁W : b₁ ∉ nineW0 V K S g := fun h => hb₁R (hc.nineW0_le_pCoreOf h)
  have hb₂W : b₂ ∉ nineW0 V K S g := fun h => hb₂R (hc.nineW0_le_pCoreOf h)
  have hc₃W : c₃ ∉ nineW0 V K S g := fun h => hc₃R (hc.nineW0_le_pCoreOf h)
  have hc₄W : c₄ ∉ nineW0 V K S g := fun h => hc₄R (hc.nineW0_le_pCoreOf h)
  have hmemD' : b₁ * b₂ ∈ nineDp K A x :=
    hc.core.mul_mem_nineDp hxX hB₁ hB₂ hb₁ hb₂ hb₁R hb₂R
  have hcommD' : b₁ * b₂ * d⁻¹ * (b₁ * b₂)⁻¹ * d ∈ nineD K A x ⊓ nineDp K A x := by
    have := commutator_nineDp_nineD_mem hc hmemD' ((nineD K A x).inv_mem hd)
    simpa only [commutatorElement_def, inv_inv] using this
  have hyD : b₁ * b₂ * c₃ * c₄ ∈ nineD K A x := by
    have hcomm' : b₁ * b₂ * d⁻¹ * (b₁ * b₂)⁻¹ * d = b₁ * b₂ * c₃ * c₄ := by
      simp only [c₃, c₄]; group
    rw [← hcomm']
    exact hcommD'.1
  have hycomm : ∀ q ∈ nineD K A x, ⁅b₁ * b₂ * c₃ * c₄, q⁆ = 1 := by
    intro q hq
    rw [commutatorElement_def, hDcomm _ hyD q hq]
    group
  obtain ⟨q, hqQ, hqW⟩ := nineThree_group_not_fixed (W := nineW V S) (W₀ := nineW0 V K S g)
    (L := nineL K A x g) (Q := nineD K A x) (V := V) (Δ := nineDelta V S)
    hc.core.nineW_isElemAbelian hW₀W hc.nineL_le_normalizer_nineW
    (hc.nineL_le_normalizer_nineW0 hI) (fun B hB => le_iSup₂_of_le B hB le_rfl) rfl
    (fun B hB l hl => (mem_nineDeltaStab.mp (hc.nineL_le_nineDeltaStab hl) B).mp hB)
    (hc.odd_card_nineDelta hΔ3) (hc.nineL_transitive hΔ3)
    (fun B hB => hc.relIndex_inf_nineW0 hI hB)
    ⟨A, hc.core.A_mem_nineDelta, V, hc.core.V_mem_nineDelta, hc.not_A_le_sup hI⟩
    hc.core.V_mem_nineDelta le_sup_left (B2F.isPGroup_of_isElemAbelian hDab)
    (fun q hq' => conjSubgroup_eq_iff_mem_normalizer.mpr
      (Subgroup.centralizer_le_normalizer _ (hc.core.nineD_le_centralizer hxX hq')))
    (fun B hB hBV B' hB' hB'V => by
      obtain ⟨d', hd', hdB⟩ := hc.core.nineD_transitive hxX hc.x_ne_one
        ((hc.core.mem_nineDelta_iff.mp hB).resolve_left hBV)
        ((hc.core.mem_nineDelta_iff.mp hB').resolve_left hB'V)
      exact ⟨d', hd', hdB.symm⟩)
    h6
    hB₁Δ hB₂Δ hB₃Δ hB₄Δ
    hB₁V hB₂V hB₃V hB₄V
    h₁₂ h₁B₂d h₁B₁d h₂B₂d h₂B₁d hB₁dB₂d.symm
    hb₁ hb₂ hc₃ hc₄
    hb₁W hb₂W hc₃W hc₄W
  exact hqW (by rw [hycomm q hqQ]; exact Subgroup.one_mem _)

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
