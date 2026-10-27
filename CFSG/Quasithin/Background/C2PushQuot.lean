module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.C2Push

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem isPGroup_iSup_of_pairwise_commute {p : ℕ} {ι : Type*} [Finite ι] (A : ι → Subgroup X)
    (hA : ∀ i, IsPGroup p (A i)) (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥) :
    IsPGroup p (⨆ i, A i : Subgroup X) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, IsPGroup p (⨆ i ∈ s, A i : Subgroup X) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset ι), A i : Subgroup X) = ⊥ := by simp
      rw [h0]
      exact IsPGroup.of_bot
    | insert a s ha ih =>
      rw [Finset.iSup_insert]
      have hcent : A a ≤ Subgroup.centralizer ((⨆ i ∈ s, A i : Subgroup X) : Set X) := by
        rw [Subgroup.le_centralizer_iff]
        refine iSup₂_le fun i hi => ?_
        have hne : a ≠ i := fun h => ha (h ▸ hi)
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hc a i hne
      exact (hA a).to_sup_of_normal_right' ih (hcent.trans (Subgroup.centralizer_le_normalizer _))
  have hall := key Finset.univ
  have h : (⨆ i ∈ (Finset.univ : Finset ι), A i : Subgroup X) = ⨆ i, A i := by simp
  rwa [h] at hall

theorem le_normalizer_of_forall_conj_mem {N S : Subgroup X}
    (h : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) : N ≤ Subgroup.normalizer (S : Set X) := fun n hn =>
  Subgroup.mem_normalizer_iff.mpr fun s =>
    ⟨h n hn s, fun hs => by
      have h1 := h n⁻¹ (N.inv_mem hn) _ hs
      simpa [mul_assoc] using h1⟩

theorem map_conj_inf_of_mem {H K : Subgroup X} {g : X} (hg : g ∈ H) :
    (K ⊓ H).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj g).toMonoidHom ⊓ H := by
  rw [Subgroup.map_inf K H _ (MulAut.conj g).injective]
  congr 1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)

theorem pCoreOf_inf_le_pCoreOf_of_isComponent [Finite X] {K : Subgroup X} (H : Subgroup X)
    (hK : CFSG.IsComponent K) : pCoreOf 2 (K ⊓ H) ≤ pCoreOf 2 H := by
  set A : {K : Subgroup X // CFSG.IsComponent K} → Subgroup X :=
    fun K => pCoreOf 2 (K.1 ⊓ H) with hAdef
  set P : Subgroup X := ⨆ K, A K with hP
  have hA2 : ∀ K, IsPGroup 2 (A K) := fun K => pCoreOf_isPGroup 2 _
  have hAle : ∀ K, A K ≤ K.1 := fun K => (pCoreOf_le 2 _).trans inf_le_left
  have hcomm : ∀ K K', K ≠ K' → ⁅A K, A K'⁆ = ⊥ := by
    intro K K' hne
    rcases CFSG.LocalCores.distinct_components_commute K.2 K'.2 with h | h
    · exact absurd (Subtype.ext h) hne
    · exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono (hAle K) (hAle K'))
  have hP2 : IsPGroup 2 P := isPGroup_iSup_of_pairwise_commute A hA2 hcomm
  have hPH : P ≤ H := iSup_le fun K => (pCoreOf_le 2 _).trans inf_le_right
  have hconj : ∀ g ∈ H, P.map (MulAut.conj g).toMonoidHom ≤ P := by
    intro g hg
    rw [hP, Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    have hK' : CFSG.IsComponent (K.1.map (MulAut.conj g).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) K.2
    have : (A K).map (MulAut.conj g).toMonoidHom =
        A ⟨K.1.map (MulAut.conj g).toMonoidHom, hK'⟩ := by
      simp only [hAdef]
      rw [← pCoreOf_map_mulEquiv 2 (MulAut.conj g) (K.1 ⊓ H), map_conj_inf_of_mem hg]
    rw [this]
    exact le_iSup A _
  have hHP : H ≤ Subgroup.normalizer (P : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj g hg ⟨x, hx, by simp⟩
    · intro hx
      have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ P :=
        hconj g⁻¹ (H.inv_mem hg) ⟨g * x * g⁻¹, hx, by simp⟩
      simpa [mul_assoc] using h1
  exact le_trans (le_iSup A ⟨K, hK⟩) (le_pCoreOf_of_le_normalizer 2 hPH hHP hP2)

theorem commutator_inf_le_of_not_le_normalizer [Finite X] {R H K : Subgroup X}
    (hH : H ≤ Subgroup.normalizer (R : Set X)) (hK : CFSG.IsComponent K)
    (hmove : ¬ R ≤ Subgroup.normalizer (K : Set X)) : ⁅K ⊓ H, K ⊓ H⁆ ≤ R ⊓ K := by
  obtain ⟨r, hrR, hrK⟩ : ∃ r ∈ R, r ∉ Subgroup.normalizer (K : Set X) := by
    by_contra h
    exact hmove fun r hr => by_contra fun hr' => h ⟨r, hr, hr'⟩
  set K' : Subgroup X := K.map (MulAut.conj r).toMonoidHom with hK'def
  have hK' : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj r) hK
  have hne : K ≠ K' := by
    intro h
    apply hrK
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
  have hcomm : ⁅K, K'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hne
  refine Subgroup.commutator_le.mpr fun y hy x hx => ?_
  set x' : X := r * x * r⁻¹ with hx'def
  have hx' : x' ∈ K' := Subgroup.mem_map.mpr ⟨x, hx.1, by simp [hx'def]⟩
  have hyx' : Commute y x' := by
    have h1 : ⁅y, x'⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hy.1 hx'
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  set e : X := x * r * x⁻¹ * r⁻¹ with hedef
  have heR : e ∈ R := by
    have h1 : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hH hx.2) r).mp hrR
    exact R.mul_mem h1 (R.inv_mem hrR)
  have heq : e = x * x'⁻¹ := by simp only [hedef, hx'def]; group
  have hyeR : y * e * y⁻¹ * e⁻¹ ∈ R := by
    have h1 : y * e * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hH hy.2) e).mp heR
    exact R.mul_mem h1 (R.inv_mem heR)
  have hcalc : y * e * y⁻¹ * e⁻¹ = y * x * y⁻¹ * x⁻¹ := by
    have hinv : y⁻¹ * x'⁻¹ = x'⁻¹ * y⁻¹ := (Commute.inv_inv hyx').eq
    calc y * e * y⁻¹ * e⁻¹ = y * x * (x'⁻¹ * y⁻¹) * (x' * x⁻¹) := by rw [heq]; group
      _ = y * x * (y⁻¹ * x'⁻¹) * (x' * x⁻¹) := by rw [← hinv]
      _ = y * x * y⁻¹ * x⁻¹ := by group
  refine ⟨?_, ?_⟩
  · have : y * x * y⁻¹ * x⁻¹ ∈ R := hcalc ▸ hyeR
    exact this
  · exact K.mul_mem (K.mul_mem (K.mul_mem hy.1 hx.1) (K.inv_mem hy.1)) (K.inv_mem hx.1)

theorem isSylowTwoOf_inf_pCoreOf_of_not_le_normalizer [Finite X] {H K T : Subgroup X}
    (hK : CFSG.IsComponent K) (hmove : ¬ pCoreOf 2 H ≤ Subgroup.normalizer (K : Set X))
    (hT : IsSylowTwoOf T K) (hTH : T ≤ H) : IsSylowTwoOf (pCoreOf 2 H ⊓ K) K := by
  set R : Subgroup X := pCoreOf 2 H with hR
  set N : Subgroup X := K ⊓ H with hN
  set P : Subgroup X := R ⊓ K with hP
  have hHR : H ≤ Subgroup.normalizer (R : Set X) := le_normalizer_pCoreOf 2 H
  have hRH : R ≤ H := pCoreOf_le 2 H
  have hNK : N ≤ K := inf_le_left
  have hPN : P ≤ N := le_inf inf_le_right (inf_le_left.trans hRH)
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hcomm : ⁅N, N⁆ ≤ P := commutator_inf_le_of_not_le_normalizer hHR hK hmove
  have hOle : pCoreOf 2 N ≤ P :=
    le_inf (pCoreOf_inf_le_pCoreOf_of_isComponent H hK) ((pCoreOf_le 2 N).trans hNK)
  have hPsyl : IsSylowTwoOf P N := by
    rw [A4.isSylowTwoOf_iff_maximal]
    refine ⟨hPN, hP2, fun P' hP'N hP'2 hPP' => ?_⟩
    have hconj : ∀ n ∈ N, ∀ p ∈ P', n * p * n⁻¹ ∈ P' := by
      intro n hn p hp
      have h1 : ⁅n, p⁆ ∈ P' := hPP' (hcomm (Subgroup.commutator_mem_commutator hn (hP'N hp)))
      have h2 : ⁅n, p⁆ * p ∈ P' := P'.mul_mem h1 hp
      have e : ⁅n, p⁆ * p = n * p * n⁻¹ := by simp only [commutatorElement_def]; group
      rwa [e] at h2
    have hnorm : N ≤ Subgroup.normalizer (P' : Set X) := le_normalizer_of_forall_conj_mem hconj
    exact (le_pCoreOf_of_le_normalizer 2 hP'N hnorm hP'2).trans hOle
  refine ⟨inf_le_right, hP2, ?_⟩
  change ¬ 2 ∣ P.relIndex K
  have h1 : P.relIndex N * N.relIndex K = P.relIndex K :=
    Subgroup.relIndex_mul_relIndex P N K hPN hNK
  have hTN : T ≤ N := le_inf hT.1 hTH
  have h2 : T.relIndex N * N.relIndex K = T.relIndex K :=
    Subgroup.relIndex_mul_relIndex T N K hTN hNK
  have hNodd : ¬ 2 ∣ N.relIndex K := fun hd' => by
    have : 2 ∣ T.relIndex K := h2 ▸ Dvd.dvd.mul_left hd' _
    exact hT.2.2 this
  have hPodd : ¬ 2 ∣ P.relIndex N := hPsyl.2.2
  intro hd
  rw [← h1] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · exact hPodd h
  · exact hNodd h

end CFSG.Quasithin.C2Push
