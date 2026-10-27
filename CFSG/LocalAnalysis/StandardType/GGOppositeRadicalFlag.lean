module

public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerRadical
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.StandardType

namespace GGOppRad

open CFSG.Open CFSG.LieType.BorelTits

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type*} [Group H] (ρ : H →* Module.End K V)

theorem rep_apply_rep_inv (g : H) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rep_inv_apply_rep (g : H) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rep_conj_apply (g h : H) (v : V) :
    ρ (MulAut.conj g h) v = ρ g (ρ h (ρ g⁻¹ v)) := by
  simp only [MulAut.conj_apply, map_mul, Module.End.mul_apply]

@[expose] def flagMap (g : H) (F : ℕ → Submodule K V) : ℕ → Submodule K V :=
  fun k => (F k).map (ρ g)

theorem mem_flagMap {g : H} {F : ℕ → Submodule K V} {k : ℕ} {v : V} :
    v ∈ flagMap ρ g F k ↔ ρ g⁻¹ v ∈ F k := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [rep_inv_apply_rep]
  · intro hv
    exact ⟨ρ g⁻¹ v, hv, rep_apply_rep_inv ρ g v⟩

theorem conj_mem_flagStab_flagMap {g h : H} {F : ℕ → Submodule K V} (hh : h ∈ flagStab ρ F) :
    MulAut.conj g h ∈ flagStab ρ (flagMap ρ g F) := by
  intro k v hv
  rw [mem_flagMap] at hv
  refine ⟨?_, ?_⟩
  · rw [mem_flagMap, rep_conj_apply, rep_inv_apply_rep]
    exact (hh k _ hv).1
  · rw [mem_flagMap, ← map_inv, rep_conj_apply, rep_inv_apply_rep]
    exact (hh k _ hv).2

theorem conj_mem_flagKernel_flagMap {g h : H} {F : ℕ → Submodule K V}
    (hh : h ∈ flagKernel ρ F) : MulAut.conj g h ∈ flagKernel ρ (flagMap ρ g F) := by
  refine ⟨conj_mem_flagStab_flagMap ρ hh.1, fun k v hv => ?_⟩
  rw [mem_flagMap] at hv ⊢
  rw [map_sub, rep_conj_apply, rep_inv_apply_rep]
  exact hh.2 k _ hv

theorem flagMap_flagMap (g g' : H) (F : ℕ → Submodule K V) :
    flagMap ρ g (flagMap ρ g' F) = flagMap ρ (g * g') F := by
  funext k
  ext v
  simp only [mem_flagMap, mul_inv_rev, map_mul, Module.End.mul_apply]

theorem flagMap_one (F : ℕ → Submodule K V) : flagMap ρ 1 F = F := by
  funext k
  ext v
  simp only [mem_flagMap, inv_one, map_one, Module.End.one_apply]

theorem flagKernel_flagMap (g : H) (F : ℕ → Submodule K V) :
    flagKernel ρ (flagMap ρ g F) = (flagKernel ρ F).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm (fun h hh => ?_) ?_
  · refine ⟨MulAut.conj g⁻¹ h, ?_, ?_⟩
    · have := conj_mem_flagKernel_flagMap ρ (g := g⁻¹) hh
      rwa [flagMap_flagMap, inv_mul_cancel, flagMap_one] at this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_flagKernel_flagMap ρ hh

theorem flagStab_flagMap (g : H) (F : ℕ → Submodule K V) :
    flagStab ρ (flagMap ρ g F) = (flagStab ρ F).map (MulAut.conj g).toMonoidHom := by
  refine le_antisymm (fun h hh => ?_) ?_
  · refine ⟨MulAut.conj g⁻¹ h, ?_, ?_⟩
    · have := conj_mem_flagStab_flagMap ρ (g := g⁻¹) hh
      rwa [flagMap_flagMap, inv_mul_cancel, flagMap_one] at this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_flagStab_flagMap ρ hh

theorem eq_flagKernel_of_pCoreOf [Finite H] [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : Function.Injective ρ) {Q : Subgroup H}
    (hQ : pCoreOf p (Subgroup.normalizer (Q : Set H)) = Q) :
    Q = flagKernel ρ (fixFlag ρ Q) ∧
      Subgroup.normalizer (Q : Set H) = flagStab ρ (fixFlag ρ Q) := by
  have hQp : IsPGroup p Q := by
    rw [← hQ]
    exact pCoreOf_isPGroup p _
  obtain ⟨m, hm⟩ := exists_fixFlag_eq_top ρ p Q hQp
  have hker : flagKernel ρ (fixFlag ρ Q) ≤ pCoreOf p (flagStab ρ (fixFlag ρ Q)) :=
    flagKernel_le_pCoreOf ρ p hρ (fixFlag_zero ρ Q) hm
  have hNP := normalizer_le_flagStab_fixFlag ρ Q
  have hQR : Q ≤ pCoreOf p (flagStab ρ (fixFlag ρ Q)) := (le_flagKernel_fixFlag ρ Q).trans hker
  have hRp := pCoreOf_isPGroup p (flagStab ρ (fixFlag ρ Q))
  have hRN : pCoreOf p (flagStab ρ (fixFlag ρ Q)) ⊓ Subgroup.normalizer (Q : Set H) ≤ Q := by
    refine le_trans ?_ hQ.le
    refine le_pCoreOf_of_le_normalizer p inf_le_right (fun g hg => ?_) (hRp.to_le inf_le_left)
    exact GGTwoSig.mem_normalizer_inf_normalizer (le_normalizer_pCoreOf p _ (hNP hg)) hg
  have hQeq : Q = pCoreOf p (flagStab ρ (fixFlag ρ Q)) :=
    hQR.eq_or_lt.resolve_right fun hlt =>
      (CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hRp hlt).not_ge hRN
  refine ⟨le_antisymm (le_flagKernel_fixFlag ρ Q) (hker.trans hQeq.ge), le_antisymm hNP ?_⟩
  have h := le_normalizer_pCoreOf p (flagStab ρ (fixFlag ρ Q))
  rwa [← hQeq] at h

theorem eq_flagKernel_of_radical [Finite H] [Finite V] [CharP K 2] (hρ : Function.Injective ρ)
    {Q : Subgroup H} (hQ : GGRadicalTwo ⊤ Q) :
    Q = flagKernel ρ (fixFlag ρ Q) ∧
      (⊤ : Subgroup H) ⊓ Subgroup.normalizer (Q : Set H) = flagStab ρ (fixFlag ρ Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : pCoreOf 2 ((⊤ : Subgroup H) ⊓ Subgroup.normalizer (Q : Set H)) = Q := hQ
  rw [top_inf_eq] at hQ'
  rw [top_inf_eq]
  exact eq_flagKernel_of_pCoreOf ρ 2 hρ hQ'

theorem exists_isCompl_of_inf_flagStab_eq_bot (htr : ContainsTransvections ρ)
    {A F' : ℕ → Submodule K V}
    (hA : Monotone A) (hA0 : A 0 = ⊥) {M : ℕ} (hAM : A M = ⊤) (hF' : Monotone F')
    (hbot : flagKernel ρ F' ⊓ flagStab ρ A = ⊥) (j : ℕ) : ∃ k, IsCompl (A k) (F' j) := by
  classical
  by_cases hB : F' j = ⊥
  · exact ⟨M, by rw [hAM, hB]; exact isCompl_top_bot⟩
  have hAM1 : A (M + 1) = ⊤ := top_le_iff.mp ((le_of_eq hAM.symm).trans (hA (Nat.le_succ M)))
  have hex : ∃ k, A (k + 1) ⊓ F' j ≠ ⊥ := ⟨M, by rw [hAM1, top_inf_eq]; exact hB⟩
  set k := Nat.find hex with hk
  have hk1 : A (k + 1) ⊓ F' j ≠ ⊥ := Nat.find_spec hex
  have hk0 : A k ⊓ F' j = ⊥ := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, hA0, bot_inf_eq]
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rwa [not_not, Nat.sub_add_cancel hpos] at this
  refine ⟨k, ⟨disjoint_iff.mpr hk0, codisjoint_iff.mpr ?_⟩⟩
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ A k ⊔ F' j := by
    by_contra h
    exact hne (eq_top_iff.mpr fun v _ => by
      by_contra hv
      exact h ⟨v, hv⟩)
  obtain ⟨φ, hφw, hφ⟩ := exists_dual_eq_one_of_notMem hw
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk1
  have hxj : x ∈ F' j := (Submodule.mem_inf.mp hx).2
  have hxA : x ∈ A (k + 1) := (Submodule.mem_inf.mp hx).1
  have hφj : ∀ v ∈ F' j, φ v = 0 := fun v hv => hφ v (Submodule.mem_sup_right hv)
  have hφA : ∀ v ∈ A k, φ v = 0 := fun v hv => hφ v (Submodule.mem_sup_left hv)
  obtain ⟨t, ht⟩ := htr x φ (hφj x hxj)
  have htK : t ∈ flagKernel ρ F' := mem_flagKernel_of_transvection ρ hF' hxj hφj ht
  have hmem : ∀ i, ∀ v ∈ A i, φ v • x ∈ A i := by
    intro i v hv
    rcases Nat.lt_or_ge k i with hki | hik
    · exact Submodule.smul_mem _ _ (hA hki hxA)
    · rw [hφA v (hA hik hv), zero_smul]
      exact zero_mem _
  have htS : t ∈ flagStab ρ A := by
    intro i v hv
    refine ⟨?_, ?_⟩
    · rw [ht]
      exact add_mem hv (hmem i v hv)
    · rw [apply_inv_of_transvection ρ (hφj x hxj) ht]
      exact sub_mem hv (hmem i v hv)
  have ht1 : t = 1 := by
    have : t ∈ flagKernel ρ F' ⊓ flagStab ρ A := ⟨htK, htS⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h1 : ρ t w = w := by rw [ht1, map_one, Module.End.one_apply]
  rw [ht w, hφw, one_smul] at h1
  exact hx0 (by simpa using h1)

end GGOppRad

end CFSG.StandardType
