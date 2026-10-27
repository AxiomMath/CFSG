module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmCompTwisted

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth TypeBDatum TypeDDatum CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private theorem tbjF_coord_of_fixed [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hA : A ≤ orthDerived Q) {f₀ : Fin r → Multiplicative (ZMod p)}
    {J : Subgroup ↥(orthDerived Q)} {P : Fin r → Prop}
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f)
    {σ : MulAut (Fin r → Multiplicative (ZMod p))} (hσ : σ ∈ Δ.torusAut hA J)
    {π : Equiv.Perm (Fin r)} {ε : Fin r → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (σ f (π i)) = ε i * toAdd (f i))
    {i : Fin r} (hi : ¬ P i) : π i = i ∧ ε i = 1 := by
  classical
  obtain ⟨n, hnJ, hn⟩ := hσ
  set f : Fin r → Multiplicative (ZMod p) := Pi.mulSingle i (ofAdd 1) with hf
  have hfP : ∀ k, P k → f k = 1 := by
    intro k hk
    apply toAdd.injective
    rw [hf, toAdd_mulSingle]
    have hki : k ≠ i := fun h => hi (h ▸ hk)
    rw [if_neg hki, toAdd_one]
  have hcf : ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f :=
    hcent f ⟨0, fun k hk => by rw [hfP k hk, toAdd_one, zero_mul]⟩
  have hconj : n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA f := by
    rw [← hcf n hnJ]; group
  have hσf : σ f = f :=
    tbjA_tauOmega_injective Δ hA (by rw [← hn f, hconj])
  have hfi : toAdd (f i) = 1 := by
    rw [hf, toAdd_mulSingle, if_pos rfl]
  have h1 : toAdd (f (π i)) = ε i := by
    have h := hu f i
    rw [hσf, hfi, mul_one] at h
    exact h
  rw [hf, toAdd_mulSingle] at h1
  by_cases hπ : π i = i
  · refine ⟨hπ, ?_⟩
    rw [if_pos hπ] at h1
    exact h1.symm
  · exfalso
    rw [if_neg hπ] at h1
    rcases hε i with h | h
    · exact zero_ne_one (h1.trans h)
    · exact (neg_ne_zero.mpr one_ne_zero) ((h1.trans h).symm)

private theorem tbjF_mem_signedSupportedAut_of_fixed [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hA : A ≤ orthDerived Q) {f₀ : Fin r → Multiplicative (ZMod p)}
    {J : Subgroup ↥(orthDerived Q)} {P : Fin r → Prop} [DecidablePred P]
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f)
    {σ : MulAut (Fin r → Multiplicative (ZMod p))} (hσ : σ ∈ Δ.torusAut hA J) :
    σ ∈ signedSupportedAut r p (Finset.univ.filter P) := by
  obtain ⟨π, ε, hε, hu⟩ := tbjA_isSignedPerm_of_induced Δ hA hσ
  refine tbjA_mem_signedSupportedAut_of _ hε ?_ ?_ hu
  · intro i hi
    have hiP : ¬ P i := fun hPi => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPi⟩)
    exact (tbjF_coord_of_fixed Δ hA hcent hσ hε hu hiP).1
  · intro i hi
    have hiP : ¬ P i := fun hPi => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPi⟩)
    exact (tbjF_coord_of_fixed Δ hA hcent hσ hε hu hiP).2

private theorem tbjF_supported_le_torusAut (Δ : TBJOmData Q p A r) (hA : A ≤ orthDerived Q)
    {f₀ : Fin r → Multiplicative (ZMod p)} {J : Subgroup ↥(orthDerived Q)} {P : Fin r → Prop}
    [DecidablePred P]
    (hP0 : ∀ i, P i → toAdd (f₀ i) = 0)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) f))
    (hsign : ∀ i, P i → ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (sgnAut i f)) :
    signedSupportedAut r p (Finset.univ.filter P) ≤ Δ.torusAut hA J := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro σ (⟨i, hiS, rfl⟩ | ⟨a, haS, b, hbS, hab, rfl⟩)
  · exact hsign i (Finset.mem_filter.mp hiS).2
  · refine hswap a b hab (Finset.mem_filter.mp haS).2 (Finset.mem_filter.mp hbS).2 ?_
    rw [hP0 a (Finset.mem_filter.mp haS).2, hP0 b (Finset.mem_filter.mp hbS).2]

private theorem tbjF_card_class_le_one_of_one_active
    {f0 : Fin r → Multiplicative (ZMod p)} {j : Fin r}
    (hf : ∀ i, i ≠ j → f0 i = 1) {P : Fin r → Prop} {a : ZMod p} (ha : a ≠ 0)
    (hP : ∀ i, P i → toAdd (f0 i) = a ∨ toAdd (f0 i) = -a) :
    Nat.card {i : Fin r // P i} ≤ 1 := by
  classical
  have hPj : ∀ i, P i → i = j := by
    intro i hi
    by_contra hij
    have hfi : f0 i = 1 := hf i hij
    have hzero : toAdd (f0 i) = 0 := by rw [hfi, toAdd_one]
    rcases hP i hi with h | h
    · exact ha (h ▸ hzero)
    · exact ha (neg_eq_zero.mp (h ▸ hzero))
  have hsub : Finset.univ.filter P ⊆ ({j} : Finset (Fin r)) := by
    intro i hi
    rw [Finset.mem_singleton]
    exact hPj i (Finset.mem_filter.mp hi).2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter P).card ≤ ({j} : Finset (Fin r)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton j

theorem TBJOmData.torusAut_component_fixed [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hA : A ≤ orthDerived Q)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v)
    {f₀ : Fin r → Multiplicative (ZMod p)} (hf₀ : f₀ ≠ 1) {J : Subgroup ↥(orthDerived Q)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({Δ.τΩ hA f₀} : Set ↥(orthDerived Q))))
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f} ≤ p ^ r) :
    ∃ S : Finset (Fin r),
      (∀ f : Fin r → Multiplicative (ZMod p), (∀ σ ∈ Δ.torusAut hA J, σ f = f) →
        ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f) ∧
      ((2 ≤ S.card ∧ S ≠ Finset.univ ∧ Δ.torusAut hA J = signedSupportedAut r p S) ∨
        ∃ (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1), 3 ≤ S.card ∧
          Δ.torusAut hA J = twistedPermAut r p S s hs) := by
  classical
  have hJ' : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({Δ.τΩ hA f₀} : Set ↥(orthDerived Q))) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ
  obtain ⟨a, P, hP, hswap, hmixed, hsign, hcent⟩ :=
    Δ.blockData hp2 hQ hT hA hW f₀ hJ'
  have hJc : J ≤ Subgroup.centralizer ({Δ.τΩ hA f₀} : Set ↥(orthDerived Q)) := hJ.1
  by_cases ha : a = 0
  ·
    have hP0 : ∀ i, P i → toAdd (f₀ i) = 0 := by
      intro i hi
      rcases hP i hi with h | h
      · rw [h, ha]
      · rw [h, ha, neg_zero]
    have h2 : 2 ≤ Nat.card {i : Fin r // P i} :=
      tbjA_two_le_card_class_of_centralizer (Fact.out : p.Prime) (Δ.τΩ hA) f₀ J P hcent hcount
    let S : Finset (Fin r) := Finset.univ.filter P
    have hS_card : 2 ≤ S.card := by
      have h := h2
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      simpa [S] using h
    have hEq : Δ.torusAut hA J = signedSupportedAut r p S := by
      refine le_antisymm ?_ ?_
      · intro σ hσ
        exact tbjF_mem_signedSupportedAut_of_fixed Δ hA hcent hσ
      · exact tbjF_supported_le_torusAut Δ hA hP0 hswap (hsign ha h2)
    have hS_ne_univ : S ≠ Finset.univ := by
      intro hSU
      apply hf₀
      refine eq_of_toAdd_eq fun i => ?_
      have hiP : P i := by
        have hiS : i ∈ S := by rw [hSU]; exact Finset.mem_univ i
        simpa [S] using hiS
      simpa [hP0 i hiP]
    have hclause : ∀ f : Fin r → Multiplicative (ZMod p),
        (∀ σ ∈ Δ.torusAut hA J, σ f = f) →
          ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f := by
      intro f hf j hj
      refine hcent f ⟨0, fun i hi => ?_⟩ j hj
      have hfix : ∀ σ ∈ signedSupportedAut r p S, σ f = f := by
        intro σ hσ
        exact hf σ (by rw [hEq]; exact hσ)
      have h1 := tbjA_fixed_of_mem_signedSupportedAut hp2 hfix i (by simpa [S] using hi)
      simpa [h1]
    exact ⟨S, hclause, Or.inl ⟨by omega, hS_ne_univ, hEq⟩⟩
  ·
    obtain ⟨S, s, hs, hS3, hEq, hfix⟩ :=
      Δ.torusAut_twisted_of_blockData hp2 hA hJc ha hP hswap (hmixed ha) hcent hcount
    exact ⟨S, hfix, Or.inr ⟨s, hs, hS3, hEq⟩⟩

theorem TBJOmData.component_eq_supportedFixedDerived_one_active [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) (hr : 3 ≤ r)
    {f0 : Fin r → Multiplicative (ZMod p)} {j : Fin r}
    (hj : f0 j ≠ 1) (hf : ∀ i, i ≠ j → f0 i = 1)
    {J : Subgroup ↥(orthDerived Q)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({Δ.τΩ hA f0} : Set ↥(orthDerived Q))))
    (hcount : p ^ (r - 1) * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ z ∈ J, Δ.τΩ hA f * z = z * Δ.τΩ hA f} ≤ p ^ r) :
    J = (supportedFixedDerived Q (Δ.τ f0)).subgroupOf (orthDerived Q) := by
  classical
  have hx : OddOrderIsometry Q p
      ((Δ.τΩ hA f0 : ↥(orthDerived Q)) : V ≃ₗ[K] V) :=
    Δ.oddOrderIsometry hp2 hQ hA f0
  rcases component_cases hQ (Fact.out : p.Prime) hp2 hx hJ with
    ⟨h, hh, hX, hJeq⟩ | ⟨F, -, hFle, -, hdim, hJeq⟩
  ·
    obtain ⟨a, P, ha, hP, -, -, hcent⟩ :=
      Δ.blockG_orthDerived hp2 hQ hA f0 hh hX
    have hcount' : p ^ (r - 1) * Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ z ∈ (specialBlock Q (Δ.τ f0) h).subgroupOf (orthDerived Q),
          Δ.τΩ hA f * z = z * Δ.τΩ hA f} ≤ p ^ r := by
      rwa [hJeq] at hcount
    have h2 := tbjA_le_card_class_of_centralizer (Fact.out : p.Prime) (Δ.τΩ hA) f0
      ((specialBlock Q (Δ.τ f0) h).subgroupOf (orthDerived Q)) P hcent hcount'
    have h1 := tbjF_card_class_le_one_of_one_active hf ha hP
    omega
  ·
    by_cases hFeq : F = supportedFixedDerived Q (Δ.τ f0)
    · rw [hJeq, hFeq]
    · exfalso
      have h2 : 2 ≤ Nat.card {i : Fin r // toAdd (f0 i) = 0} := by
        have hzero : Finset.univ.filter (fun i : Fin r => toAdd (f0 i) = 0) =
            Finset.univ.filter (fun i : Fin r => i ≠ j) := by
          apply Finset.filter_congr
          intro i _
          constructor
          · intro hi
            rintro rfl
            exact hj (toAdd.injective (hi.trans toAdd_one.symm))
          · intro hij
            rw [hf i hij, toAdd_one]
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hzero, Finset.filter_ne',
          Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
        omega
      have h5 : 4 < finrank K (fixedSpace (Δ.τ f0)) :=
        (Δ.blockZ hp2 hQ hA hW f0).2.2.2 h2
      rcases hdim with hdim | hdim
      · exact absurd h5 (not_lt.mpr hdim)
      · exact hFeq hdim

end OrthTorus

end CFSG.StandardType

end
