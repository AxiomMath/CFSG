module

public import CFSG.Quasithin.EmptyFaithful.S146zNKer
public import CFSG.Quasithin.EmptyFaithful.S146zNTwoA
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.Quasithin.EmptyFaithful.S146C5
public import CFSG.Quasithin.EmptyFaithful.S146zGNum
public import CFSG.Quasithin.EmptyFaithful.S146zNBrG

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Rank4

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem a6rk_rank4 (hA6 : A6Amt) (S : Setting146 G T M) {K U₁ U₂ : Subgroup G} {s u : G}
    (hctx : Ctx24 T M K U₁ U₂ s u) (hKA : KbarIsA6 K) (hKeq : K = perfectCore (mcOf T))
    (h4 : mIdx U₁ Zz = 4 ∧ IsIrredOnSection K U₁ Zz ∧ ⁅U₁, K⁆ ⊔ Zz = U₁)
    {X : Subgroup G} (hX : QCrit Zz (VZ T M) (mcOf T) X) :
    2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) =
        mIdx (conjClosure (VZ T M) (mcOf T))
          (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) X) ∧
      ∃ x ∈ X, mIdx X (X ⊓ pCoreOf 2 (mcOf T)) + 2 ≤
        mIdx (conjClosure (VZ T M) (mcOf T))
          (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) (Subgroup.zpowers x)) := by
  classical
  obtain ⟨c19, -, c23, hKc, -, -, hdec, -⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hKc
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hTH : T ≤ mcOf T := hG.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hHKT : mcOf T = K ⊔ T := by
    rw [hKeq]
    exact c23.1.2
  have hKH : K ≤ mcOf T := le_of_mem_cComp hKc
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun x hx => S.normalizer_Z.ge hx
  have hHU : mcOf T ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hUN : conjClosure (VZ T M) (mcOf T) ≤ Subgroup.normalizer (Zz : Set G) :=
    S.conjClosure_le_normalizer_Z hG
  have hZU : Zz ≤ conjClosure (VZ T M) (mcOf T) := Z_le_conjClosure_VZ T M (mcOf T)
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) := isPGroup_of_isElemAbelian hUab
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hUKU : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
    S145.commutator_le_of_le_normalizer (hKH.trans hHU)
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G,
      E = ⁅conjClosure (VZ T M) (mcOf T), K⁆ ⊔ Zz := ⟨_, rfl⟩
  have hEU : E ≤ conjClosure (VZ T M) (mcOf T) := hEdef ▸ sup_le hUKU hZU
  have hZE : Zz ≤ E := hEdef ▸ le_sup_right
  have hHE : mcOf T ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEdef]
    exact fun h hh => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨F9.le_normalizer_commutator_of_le hHU hKn hh, hHZ hh⟩
  have hsup : U₁ ⊔ U₂ = E := by
    rw [hEdef]
    exact hdec.sup.symm
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hdec.mem.2
  have hsH : s ∈ mcOf T := hTH hdec.mem.1
  have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) := h4.2.1.2.1
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hdec.conj]
    exact le_normalizer_conjSub hsK hKU₁
  have hf : KbarFusesThrees K s := by
    rcases hdec.dynkin with ⟨hL3, -⟩ | ⟨-, hf⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hKA).elim
    · exact hf
  have hnt : ∃ k ∈ K, ∃ e ∈ E, k * e * k⁻¹ * e⁻¹ ∉ Zz := by
    by_contra hcon
    push Not at hcon
    have h1 : ⁅U₁, K⁆ ≤ Zz := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      have hU₁E : U₁ ≤ E := hsup ▸ le_sup_left
      have := hcon k hk a (hU₁E ha)
      have e : ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.inv_mem _ this
    have h2 : U₁ ≤ Zz := calc U₁ = ⁅U₁, K⁆ ⊔ Zz := h4.2.2.symm
      _ ≤ Zz := sup_le h1 le_rfl
    have h3 : (quasithinOmegaOneCenter T).relIndex U₁ = 1 := Subgroup.relIndex_eq_one.mpr h2
    have h5 := h4.1
    unfold mIdx at h5
    rw [h3] at h5
    simp at h5
  have hQE : ∀ p ∈ pCoreOf 2 K, ∀ e ∈ E, p * e * p⁻¹ * e⁻¹ ∈ Zz := fun p hp e he =>
    S.comm_mem_Z hG (hEU he) (hQK hp)
  have hker : centralizerMod Zz K E = pCoreOf 2 K := by
    refine le_antisymm (a6k_centralizerMod_le (hKH.trans hHZ) (hKH.trans hHE) hsimple hQE hnt) ?_
    intro p hp
    exact ⟨pCoreOf_le 2 K hp, hHZ (hKH (pCoreOf_le 2 K hp)), fun e he => hQE p hp e he⟩
  have hQ : centralizerMod Zz (mcOf T) E = pCoreOf 2 (mcOf T) := by
    refine le_antisymm (a6k_centralizerMod_H_le hKc hsimple hKn hT2 hHKT hHZ hHE
      (hker ▸ hQK)) ?_
    rw [← S.lemma_14_5_15_four hG]
    exact centralizerMod_anti_right (mcOf T) hEU
  obtain ⟨hXH, hXab, hXnt, hquad, hidx⟩ := hX
  have hCU : mIdx (conjClosure (VZ T M) (mcOf T))
      (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) X) ≤
      2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) := by
    have hXp : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp, HypF98.relIndex_eq_two_pow_mIdx hXp, ← pow_mul,
      mul_comm] at hidx
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hidx
  have hr : mIdx E (centralizerMod Zz E X) ≤ 2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) :=
    (a6k_mIdx_centralizerMod_le hUp hEU).trans hCU
  obtain ⟨hc1, x, hxX, hc2⟩ := a6amt_group hA6 hUab hZE hEU hHZ hHE hKH hXH hKn hsH hQ hker
    hdec.Z₁ hsup hdec.conj hKU₁ hKU₂ h4.1 h4.2.1.2.2.2 hKA hf hXab hXnt
    (fun b₁ hb₁ b₂ hb₂ e he => hquad b₁ hb₁ b₂ hb₂ e (hEU he)) hr
  have hle : 2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) ≤
      mIdx (conjClosure (VZ T M) (mcOf T))
        (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) X) := by
    have := a6k_mIdx_centralizerMod_le (Z₀ := Zz) (X := X) hUp hEU
    omega
  exact ⟨le_antisymm hle hCU, x, hxX, hc2.trans (a6k_mIdx_centralizerMod_le hUp hEU)⟩

end Rank4

end CFSG.Quasithin
