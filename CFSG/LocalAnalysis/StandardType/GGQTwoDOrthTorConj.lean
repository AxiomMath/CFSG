module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthRealize
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorConjAux
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsMoves
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open TauCeti.QuadraticMap
open CFSG.StandardType.QTwo
open scoped commutatorElement

section Conj

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X)
theorem OrthFrameCore.torStruct_of_conj {t μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))} (hμ : μ ∈ orthogonalGroup Φ.Q)
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) (hws : w ∈ omSigned p Φ.r)
    (h : Φ.TorStruct (μ * t * μ⁻¹)) : Φ.TorStruct t := by
  obtain ⟨P₀', P₁', hP₀'C', hP₁'C', hN₀', hN₁', hcomm', hperf', hTF₀', hTF₁'⟩ := h
  have hC' : (Φ.torC t).map (MulAut.conj μ).toMonoidHom = Φ.torC (μ * t * μ⁻¹) :=
    plh_torC_conj (Φ := Φ) hμ
  have hP₀C : P₀'.map (MulAut.conj μ⁻¹).toMonoidHom ≤ Φ.torC t := by
    intro a ha
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp ha
    have hx : (MulAut.conj μ) a ∈ Φ.torC (μ * t * μ⁻¹) := by
      rw [← haeq]
      change (MulAut.conj μ) ((MulAut.conj μ⁻¹) a') ∈ Φ.torC (μ * t * μ⁻¹)
      rw [show (MulAut.conj μ) ((MulAut.conj μ⁻¹) a') = a' by
        rw [MulAut.conj_apply, MulAut.conj_apply]; group]
      exact hP₀'C' ha'
    rw [← hC'] at hx
    exact (Subgroup.mem_map_iff_mem (f := (MulAut.conj μ).toMonoidHom)
      (MulAut.conj μ).injective).mp hx
  have hP₁C : P₁'.map (MulAut.conj μ⁻¹).toMonoidHom ≤ Φ.torC t := by
    intro a ha
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp ha
    have hx : (MulAut.conj μ) a ∈ Φ.torC (μ * t * μ⁻¹) := by
      rw [← haeq]
      change (MulAut.conj μ) ((MulAut.conj μ⁻¹) a') ∈ Φ.torC (μ * t * μ⁻¹)
      rw [show (MulAut.conj μ) ((MulAut.conj μ⁻¹) a') = a' by
        rw [MulAut.conj_apply, MulAut.conj_apply]; group]
      exact hP₁'C' ha'
    rw [← hC'] at hx
    exact (Subgroup.mem_map_iff_mem (f := (MulAut.conj μ).toMonoidHom)
      (MulAut.conj μ).injective).mp hx
  refine ⟨P₀'.map (MulAut.conj μ⁻¹).toMonoidHom, P₁'.map (MulAut.conj μ⁻¹).toMonoidHom,
    hP₀C, hP₁C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hP₀C]
    intro h k hh hk
    rw [Subgroup.mem_map] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    have hk' : (MulAut.conj μ) k ∈ Φ.torC (μ * t * μ⁻¹) := by
      rw [← hC']
      exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have hconj : (MulAut.conj μ) k * h' * ((MulAut.conj μ) k)⁻¹ ∈ P₀' :=
      (Subgroup.normal_subgroupOf_iff hP₀'C').mp hN₀' h' ((MulAut.conj μ) k) hh' hk'
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj μ) k * h' * ((MulAut.conj μ) k)⁻¹, hconj, ?_⟩
    change (MulAut.conj μ)⁻¹ ((MulAut.conj μ) k * h' * ((MulAut.conj μ) k)⁻¹) =
      k * ((MulAut.conj μ)⁻¹ h') * k⁻¹
    have hkμ : (MulAut.conj μ)⁻¹ ((MulAut.conj μ) k) = k := by
      rw [MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [map_mul, map_mul, map_inv, hkμ]
  · rw [Subgroup.normal_subgroupOf_iff hP₁C]
    intro h k hh hk
    rw [Subgroup.mem_map] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    have hk' : (MulAut.conj μ) k ∈ Φ.torC (μ * t * μ⁻¹) := by
      rw [← hC']
      exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have hconj : (MulAut.conj μ) k * h' * ((MulAut.conj μ) k)⁻¹ ∈ P₁' :=
      (Subgroup.normal_subgroupOf_iff hP₁'C').mp hN₁' h' ((MulAut.conj μ) k) hh' hk'
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj μ) k * h' * ((MulAut.conj μ) k)⁻¹, hconj, ?_⟩
    change (MulAut.conj μ)⁻¹ ((MulAut.conj μ) k * h' * ((MulAut.conj μ) k)⁻¹) =
      k * ((MulAut.conj μ)⁻¹ h') * k⁻¹
    have hkμ : (MulAut.conj μ)⁻¹ ((MulAut.conj μ) k) = k := by
      rw [MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rw [map_mul, map_mul, map_inv, hkμ]
  · intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    show (MulAut.conj μ⁻¹) a' * (MulAut.conj μ⁻¹) b' =
      (MulAut.conj μ⁻¹) b' * (MulAut.conj μ⁻¹) a'
    rw [← map_mul, ← map_mul, hcomm' a' ha' b' hb']
  · intro K hK hperf
    have hK' : K.map (MulAut.conj μ).toMonoidHom ≤ Φ.torC (μ * t * μ⁻¹) := by
      rw [← hC']
      exact Subgroup.map_mono hK
    have hperfmap : ⁅K.map (MulAut.conj μ).toMonoidHom,
        K.map (MulAut.conj μ).toMonoidHom⁆ = K.map (MulAut.conj μ).toMonoidHom := by
      rw [← Subgroup.map_commutator, hperf]
    have h2 : (K.map (MulAut.conj μ).toMonoidHom).map (MulAut.conj μ⁻¹).toMonoidHom ≤
        (P₀' ⊔ P₁').map (MulAut.conj μ⁻¹).toMonoidHom :=
      Subgroup.map_mono (hperf' (K.map (MulAut.conj μ).toMonoidHom) hK' hperfmap)
    have hcomp : (MulAut.conj μ⁻¹).toMonoidHom.comp (MulAut.conj μ).toMonoidHom =
        MonoidHom.id (Φ.V ≃ₗ[Φ.F] Φ.V) := by
      ext z
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [Subgroup.map_map, hcomp, Subgroup.map_id, Subgroup.map_sup] at h2
    exact h2
  · exact plh_torFactor_map_conj (Φ := Φ) hμ hw hws hTF₀'
  · exact plh_torFactor_map_conj (Φ := Φ) hμ hw hws hTF₁'

theorem OrthFrameCore.exists_std_conj [Fact p.Prime] (hF : Nat.card Φ.F = 2)
    {t : Φ.V ≃ₗ[Φ.F] Φ.V} (ht : t ∈ Φ.A) :
    ∃ (a₀ : ℕ) (μ : Φ.V ≃ₗ[Φ.F] Φ.V) (w : MulAut (Fin Φ.r → Multiplicative (ZMod p))),
      a₀ ≤ Φ.r ∧ μ ∈ orthogonalGroup Φ.Q ∧ w ∈ omSigned p Φ.r ∧
        (∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) ∧
          μ * t * μ⁻¹ = Φ.Δ.τ (torStd p Φ.r a₀) := by
  classical
  have hp3 : p = 3 := Φ.p_eq_three hF
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (by rw [Φ.Δ.τ_range]; exact ht)
  let S : Finset (Fin Φ.r) := Finset.univ.filter (fun i => g i ≠ 1)
  let a₀ : ℕ := Φ.r - S.card
  let ε : Fin Φ.r → ZMod p := fun i => if Multiplicative.toAdd (g i) = -1 then -1 else 1
  have hε : ∀ i, ε i * ε i = 1 := by
    intro i
    dsimp only [ε]
    split_ifs <;> ring
  have hε' : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    dsimp only [ε]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hw₁ : SpCoord.diagAut ε hε ∈ omSigned p Φ.r := by
    refine SpCoord.mem_of_diag (H := omSigned p Φ.r)
      (fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)) Finset.univ
      (SpCoord.diagAut ε hε) ε hε' (fun i hi => absurd (Finset.mem_univ i) hi) (fun f i => ?_)
    rw [SpCoord.diagAut_apply, toAdd_ofAdd]
  let g' : Fin Φ.r → Multiplicative (ZMod p) := SpCoord.diagAut ε hε g
  have hg'_toAdd : ∀ i, Multiplicative.toAdd (g' i) =
      if Multiplicative.toAdd (g i) = 0 then 0 else 1 := by
    intro i
    show Multiplicative.toAdd (SpCoord.diagAut ε hε g i) = _
    rw [SpCoord.diagAut_apply, toAdd_ofAdd]
    exact plh_zmod_sign_three hp3 (Multiplicative.toAdd (g i))
  have hS : ∀ i, i ∈ S ↔ Multiplicative.toAdd (g i) ≠ 0 := by
    intro i
    show i ∈ Finset.univ.filter (fun i => g i ≠ 1) ↔ _
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h h0
      exact h ((plh_toAdd_eq_zero_iff (g i)).mp h0)
    · intro h h1
      exact h ((plh_toAdd_eq_zero_iff (g i)).mpr h1)
  let tgt : Finset (Fin Φ.r) := Finset.univ.filter (fun i => a₀ ≤ i.val)
  have htgt_card : tgt.card = Φ.r - a₀ := by
    show (Finset.univ.filter (fun i : Fin Φ.r => a₀ ≤ i.val)).card = Φ.r - a₀
    exact plh_card_filter_fin_le Φ.r a₀
  have hSle : S.card ≤ Φ.r := by
    show (Finset.univ.filter (fun i : Fin Φ.r => g i ≠ 1)).card ≤ Φ.r
    simpa using Finset.card_le_card (Finset.filter_subset (fun i => g i ≠ 1)
      (Finset.univ : Finset (Fin Φ.r)))
  have hcard : S.card = tgt.card := by
    rw [htgt_card]
    dsimp only [a₀]
    omega
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S tgt hcard
  let w : MulAut (Fin Φ.r → Multiplicative (ZMod p)) :=
    SpCoord.permAut σ * SpCoord.diagAut ε hε
  have hw : w ∈ omSigned p Φ.r :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)) hw₁
  have hwg : w g = torStd p Φ.r a₀ := by
    funext j
    apply Multiplicative.toAdd.injective
    have hmem : σ⁻¹ j ∈ S ↔ j ∈ tgt := by
      rw [← hσ]
      constructor
      · intro hj
        exact Finset.mem_map.mpr ⟨σ⁻¹ j, hj, by simp⟩
      · intro hj
        obtain ⟨x, hx, hxj⟩ := Finset.mem_map.mp hj
        rw [← hxj]
        simpa using hx
    have htj : j ∈ tgt ↔ a₀ ≤ j.val := by
      show j ∈ Finset.univ.filter (fun i : Fin Φ.r => a₀ ≤ i.val) ↔ a₀ ≤ j.val
      rw [Finset.mem_filter]
      simp
    have hwj : Multiplicative.toAdd ((w g) j) = (if σ⁻¹ j ∈ S then 1 else 0) := by
      dsimp only [w]
      rw [MulAut.mul_apply, SpCoord.permAut_apply, Function.comp_apply,
        SpCoord.diagAut_apply, toAdd_ofAdd]
      dsimp only [ε]
      rw [plh_zmod_sign_three hp3]
      by_cases h : σ⁻¹ j ∈ S
      · have hne : Multiplicative.toAdd (g (σ⁻¹ j)) ≠ 0 := (hS (σ⁻¹ j)).mp h
        rw [if_neg hne, if_pos h]
      · have h0 : Multiplicative.toAdd (g (σ⁻¹ j)) = 0 := by
          by_contra hne
          exact h ((hS _).mpr hne)
        rw [if_pos h0, if_neg h]
    rw [hwj, plh_toAdd_torStd]
    by_cases h : σ⁻¹ j ∈ S
    · have hj : a₀ ≤ j.val := htj.mp (hmem.mp h)
      rw [if_pos h, if_neg (by omega)]
    · have hj : ¬ a₀ ≤ j.val := fun ha => h (hmem.mpr (htj.mpr ha))
      rw [if_neg h, if_pos (by omega)]
  obtain ⟨μ, hμ, hμw⟩ := Φ.exists_realize hF hw
  refine ⟨a₀, μ, w, by dsimp only [a₀]; exact Nat.sub_le _ _, hμ, hw, hμw, ?_⟩
  rw [← hg, hμw g, hwg]

theorem OrthFrameCore.torStruct_of_std [Fact p.Prime] (hF : Nat.card Φ.F = 2)
    (h : ∀ a₀ : ℕ, a₀ ≤ Φ.r → Φ.TorStruct (Φ.Δ.τ (torStd p Φ.r a₀)))
    {t : Φ.V ≃ₗ[Φ.F] Φ.V} (ht : t ∈ Φ.A) : Φ.TorStruct t := by
  obtain ⟨a₀, μ, w, ha, hμ, hw, hμw, hμt⟩ := Φ.exists_std_conj hF ht
  exact Φ.torStruct_of_conj (t := t) (μ := μ) (w := w) hμ hμw hw (by rw [hμt]; exact h a₀ ha)

end Conj

end OrthTorus

end CFSG.StandardType

end
