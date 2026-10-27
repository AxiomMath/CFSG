module

public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.ARS.Sec12Center

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

namespace CaseM

theorem commute_of_isNaturalModule {K : Type*} [Field K] {G : Type*} [Group G] {X : Subgroup G}
    [CharP K 2] {φ : ↥X ≃* SpecialLinearGroup (Fin 2) K}
    {θ : (Fin 2 → K) → G} (hθ : IsNaturalModule φ θ) {z : G} (hzX : ∀ x ∈ X, Commute z x)
    (hzN : ∀ v, ∃ w, z * θ v * z⁻¹ = θ w) (hz2 : z * z = 1) (v : Fin 2 → K) :
    Commute z (θ v) := by
  choose ψ hψ using hzN
  have key : ∀ (g : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      ψ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ψ v := by
    intro g v
    apply hθ.injective
    have h1 := hθ.map_mulVec (φ.symm g) v
    have h2 := hθ.map_mulVec (φ.symm g) (ψ v)
    rw [MulEquiv.apply_symm_apply] at h1 h2
    rw [← hψ, h1, h2, ← hψ]
    have hc := hzX _ (φ.symm g).2
    calc z * ((φ.symm g : G) * θ v * (φ.symm g : G)⁻¹) * z⁻¹
        = (φ.symm g : G) * (z * θ v * z⁻¹) * (φ.symm g : G)⁻¹ := by
          rw [show z * ((φ.symm g : G) * θ v * (φ.symm g : G)⁻¹) * z⁻¹ =
            (z * (φ.symm g : G)) * θ v * (z * (φ.symm g : G))⁻¹ * (z * z⁻¹) by group]
          rw [hc.eq]
          group
      _ = _ := rfl
  have hadd : ∀ v w, ψ (v + w) = ψ v + ψ w := fun v w => hθ.injective (by
    rw [← hψ, hθ.map_add, hθ.map_add, ← hψ, ← hψ]
    group)
  have hψ0 : ψ 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have h01 : ψ ![1, 0] 1 = 0 := by
    have := congrFun (key (upperElt K 1) ![1, 0]) 0
    rw [upperElt_mulVec, upperElt_mulVec] at this
    simpa using this
  have hc0 : ∀ c : K, ψ ![c, 0] = ![c * ψ ![1, 0] 0, 0] := by
    intro c
    by_cases hc : c = 0
    · rw [hc, zero_mul]
      have : (![0, 0] : Fin 2 → K) = 0 := by ext i; fin_cases i <;> rfl
      rw [this, hψ0]
    · have := key (diagElt (Units.mk0 c hc)) ![1, 0]
      rw [diagElt_mulVec, diagElt_mulVec] at this
      simp only [Units.val_mk0, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
        mul_zero] at this
      rw [this, h01, mul_zero]
  have h0c : ∀ c : K, ψ ![0, c] = ![0, c * ψ ![1, 0] 0] := by
    intro c
    have := key (weylElt K) ![c, 0]
    rw [FrameSL3.weylElt_mulVec, hc0, FrameSL3.weylElt_mulVec] at this
    simpa using this
  have hlin : ∀ v : Fin 2 → K, ψ v = ψ ![1, 0] 0 • v := by
    intro v
    have hv : v = ![v 0, 0] + ![0, v 1] := by ext i; fin_cases i <;> simp
    rw [hv, hadd, hc0, h0c]
    ext i; fin_cases i <;> simp [mul_comm]
  have hψψ : ∀ v, ψ (ψ v) = v := fun v => hθ.injective (by
    rw [← hψ, ← hψ]
    calc z * (z * θ v * z⁻¹) * z⁻¹ = (z * z) * θ v * (z * z)⁻¹ := by group
      _ = θ v := by rw [hz2, one_mul, inv_one, mul_one])
  have hl : ψ ![1, 0] 0 = 1 := by
    have h1 := congrFun (hψψ ![1, 0]) 0
    rw [hlin (ψ ![1, 0]), Pi.smul_apply, smul_eq_mul] at h1
    have h2 : ψ ![1, 0] 0 * ψ ![1, 0] 0 = 1 := by simpa using h1
    have h3 : (ψ ![1, 0] 0 + 1) * (ψ ![1, 0] 0 + 1) = 0 := by
      have e : (ψ ![1, 0] 0 + 1) * (ψ ![1, 0] 0 + 1) =
          (ψ ![1, 0] 0 * ψ ![1, 0] 0 + 1) + (ψ ![1, 0] 0 + ψ ![1, 0] 0) := by ring
      rw [e, h2, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have h4 := mul_self_eq_zero.1 h3
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact h4
  have hfix : z * θ v * z⁻¹ = θ v := by rw [hψ, hlin, hl, one_smul]
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  exact hfix

end CaseM

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem conjSub_eq_of_deltaSet_subset {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) {z : G}
    (hz : z ∈ levi R A A₀) (hz2 : z * z = 1)
    (h : ∀ X ∈ deltaSet R A A₀ B, conjSub X z ∈ deltaSet R A A₀ B) : conjSub B z = B := by
  have hR := hS.hyp.root
  have hzz : ∀ H : Subgroup G, conjSub (conjSub H z) z = H := fun H => by
    rw [← conjSub_mul, hz2, conjSub_one]
  refine hS.eq_of_deltaSet_eq (conjSub_mem_lambdaStar_of_mem_levi hR hB hz) hB ?_
  ext X
  constructor
  · rintro ⟨hX, hXB⟩
    have h1 : conjSub X z ∈ deltaSet R A A₀ B := by
      refine ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX hz, ?_⟩
      have := conjSub_mem_lambdaSet hR hXB z
      rwa [hzz] at this
    have := h _ h1
    rwa [hzz] at this
  · intro hX
    have h1 := h X hX
    refine ⟨hX.1, ?_⟩
    have := conjSub_mem_lambdaSet hR h1.2 z
    rwa [hzz] at this

theorem commute_of_conjSub_eq_of_pair {B P' Q' : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hP' : P' ∈ leviSet R A A₀) (hQ' : Q' ∈ leviSet R A A₀) (hPQ : Opposite P' Q')
    (hQB : Commuting Q' B) {z : G} (hzB : conjSub B z = B) (hzP : ∀ p ∈ P', Commute z p)
    (hzQ : ∀ q ∈ Q', Commute z q) (hz2 : z * z = 1) : ∀ b ∈ B, Commute z b := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hBR : B ∈ R := hB.1.1.1
  have hQR : Q' ∈ R := hQ'.1.1
  have hPR : P' ∈ R := hP'.1.1
  have hs : Special R P' B := hS.special_of_commuting_of_opposite hB hP' hQ' hPQ hQB
  have hBQ : B ∈ lambdaSet R Q' := hS.mem_lambdaSet_of_commuting hB hQ' hQB.symm
  obtain ⟨n, hn, -, φ, hφ, -⟩ := hPQ.symm.exists_mulEquiv_SL2' hR hQR
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hBR
  obtain ⟨θ, hθ, hrange, -⟩ := Sec3.exists_isNaturalModule hR hiso hQR hPR hPQ.symm hBQ
    ⟨hBR, hs⟩ φ hφ hw hw1
  have hzX : ∀ x ∈ Q' ⊔ P', Commute z x := by
    intro x hx
    have hle : Q' ⊔ P' ≤ Subgroup.centralizer ({z} : Set G) := sup_le
      (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hzQ q hq).symm)
      (fun p hp => Subgroup.mem_centralizer_singleton_iff.2 (hzP p hp).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hzN : ∀ v, ∃ w, z * θ v * z⁻¹ = θ w := by
    intro v
    have hv : θ v ∈ B ⊔ ⁅P', B⁆ := by
      rw [← SetLike.mem_coe, ← hrange]
      exact ⟨v, rfl⟩
    have hzN' : conjSub (B ⊔ ⁅P', B⁆) z = B ⊔ ⁅P', B⁆ := by
      have e : conjSub (B ⊔ ⁅P', B⁆) z = conjSub B z ⊔ ⁅conjSub P' z, conjSub B z⁆ := by
        simp only [conjSub, Subgroup.map_sup, Subgroup.map_commutator]
      rw [e, hzB, conjSub_of_forall_commute hzP]
    have hmem : z * θ v * z⁻¹ ∈ B ⊔ ⁅P', B⁆ := by
      rw [← hzN']
      exact conj_mem_conjSub z hv
    rw [← SetLike.mem_coe, ← hrange] at hmem
    obtain ⟨w', hw'⟩ := hmem
    exact ⟨w', hw'.symm⟩
  intro b hb
  have hb' : b ∈ B ⊔ ⁅P', B⁆ := Subgroup.mem_sup_left hb
  rw [← SetLike.mem_coe, ← hrange] at hb'
  obtain ⟨v, rfl⟩ := hb'
  exact CaseM.commute_of_isNaturalModule hθ hzX hzN hz2 v

end Sec12

namespace CaseM

variable {K : Type} [Field K]

noncomputable abbrev diffElt {a b : Fin 3} (hab : a ≠ b) (c : K) : StatedSp 3 K :=
  SpExtras.elt (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference a b hab) c

theorem mat_diffElt {a b : Fin 3} (hab : a ≠ b) (c : K) :
    SpExtras.mat 3 K (diffElt hab c) =
      1 + c • (single (Sum.inl a) (Sum.inl b) 1 - single (Sum.inr b) (Sum.inr a) 1) := by
  rw [diffElt, SpExtras.mat_elt]
  rfl

theorem diffElt_mul_self [CharP K 2] {a b : Fin 3} (hab : a ≠ b) (c : K) :
    diffElt hab c * diffElt hab c = 1 := by
  rw [diffElt, ← SpExtras.elt_add, CharTwo.add_self_eq_zero, SpExtras.elt_zero]

theorem diffElt_mulVec_apply {a b : Fin 3} (hab : a ≠ b) (c : K) (v : Fin 3 ⊕ Fin 3 → K)
    (x : Fin 3 ⊕ Fin 3) :
    (SpExtras.mat 3 K (diffElt hab c) *ᵥ v) x =
      v x + c * ((if x = Sum.inl a then v (Sum.inl b) else 0) -
        (if x = Sum.inr b then v (Sum.inr a) else 0)) := by
  rw [mat_diffElt]
  simp only [add_mulVec, one_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    sub_mulVec, Pi.sub_apply, single_mulVec, one_mul]
  congr 2
  simp [Function.update_apply]

theorem spForm_single_inr (v : Fin 3 ⊕ Fin 3 → K) (k : Fin 3) :
    spForm v (Pi.single (Sum.inr k) 1) = v (Sum.inl k) := by
  simp [spForm, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply,
    Pi.single_apply]

theorem spForm_single_inl (v : Fin 3 ⊕ Fin 3 → K) (k : Fin 3) :
    spForm v (Pi.single (Sum.inl k) 1) = -v (Sum.inr k) := by
  simp [spForm, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply,
    Pi.single_apply]

theorem spForm_of_inl_eq_zero {v w : Fin 3 ⊕ Fin 3 → K} (hv : ∀ k, v (Sum.inl k) = 0)
    (hw : ∀ k, w (Sum.inl k) = 0) : spForm v w = 0 := by
  simp [spForm, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, hv, hw]

theorem spForm_of_inr_eq_zero {v w : Fin 3 ⊕ Fin 3 → K} (hv : ∀ k, v (Sum.inr k) = 0)
    (hw : ∀ k, w (Sum.inr k) = 0) : spForm v w = 0 := by
  simp [spForm, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, hv, hw]

theorem IsTransGroup.commute_of_mulVec_eq {v : Fin 3 ⊕ Fin 3 → K} {X : Subgroup (StatedSp 3 K)}
    (h : IsTransGroup v X) {s : StatedSp 3 K} (hs : SpExtras.mat 3 K s *ᵥ v = v) :
    ∀ x ∈ X, Commute s x := by
  intro x hx
  obtain ⟨c, hc⟩ := (h.1 x).1 hx
  have h1 := mat_conj_of_mat_eq hc s
  rw [hs, ← hc] at h1
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  exact SpExtras.mat_injective h1

theorem mem_rootGroup_diff_iff {a b : Fin 3} (hab : a ≠ b) {γ : Fin 3 → ℤ}
    (hγ : toStd 3 γ = Pi.single a 1 - Pi.single b 1) (x : StatedSp 3 K) :
    x ∈ Symplectic.rootGroup 3 K γ ↔ ∃ c, x = diffElt hab c :=
  SpExtras.mem_rootGroup_iff (r := .difference a b hab) hγ.symm

theorem diffElt_mulVec_single {a b t : Fin 3} (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) (c : K)
    (x : Fin 3 ⊕ Fin 3) (hx : x = Sum.inl t ∨ x = Sum.inr t) :
    SpExtras.mat 3 K (diffElt hab c) *ᵥ Pi.single x 1 = Pi.single x 1 := by
  funext y
  rw [diffElt_mulVec_apply]
  rcases hx with rfl | rfl <;> simp [Pi.single_apply, Ne.symm hta, Ne.symm htb]

theorem diffElt_mulVec_inl {a b : Fin 3} (hab : a ≠ b) (c : K) {v : Fin 3 ⊕ Fin 3 → K}
    (hv : ∀ k, v (Sum.inl k) = 0) (k : Fin 3) :
    (SpExtras.mat 3 K (diffElt hab c) *ᵥ v) (Sum.inl k) = 0 := by
  rw [diffElt_mulVec_apply]
  simp [hv]

theorem diffElt_mulVec_inr {a b : Fin 3} (hab : a ≠ b) (c : K) {v : Fin 3 ⊕ Fin 3 → K}
    (hv : ∀ k, v (Sum.inr k) = 0) (k : Fin 3) :
    (SpExtras.mat 3 K (diffElt hab c) *ᵥ v) (Sum.inr k) = 0 := by
  rw [diffElt_mulVec_apply]
  simp [hv]

theorem exists_isTransGroup_of_mem {X₀ : Subgroup (StatedSp 3 K)}
    (hX₀ : X₀ = Symplectic.rootGroup 3 K (Pi.single 2 1)) (g : StatedSp 3 K) :
    ∃ v : Fin 3 ⊕ Fin 3 → K, v ≠ 0 ∧ IsTransGroup v (conjSub X₀ g) := by
  have he0 : (Pi.single (Sum.inl 2) 1 : Fin 3 ⊕ Fin 3 → K) ≠ 0 := fun h0 => by
    have := congrFun h0 (Sum.inl 2)
    simp at this
  have hX : IsTransGroup (Pi.single (Sum.inl 2) 1) X₀ := by
    rw [hX₀, ← longC3_two]
    exact isTransGroup_pos 2
  exact ⟨_, mat_mulVec_ne_zero g he0, hX.conjSub g⟩

end CaseM

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem conjSub_eq_of_preserves {K : Type} [Field K] (Φ : StatedSp 3 K →* G)
    (hΦ : Function.Injective Φ) (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g).map Φ)
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) {u : Fin 3 → Fin 3 ⊕ Fin 3 → K}
    {Y : Fin 3 → Subgroup (StatedSp 3 K)} (hY : ∀ k, CaseM.IsTransGroup (u k) (Y k))
    (hYB : ∀ k, (Y k).map Φ ∈ deltaSet R A A₀ B) (W : (Fin 3 ⊕ Fin 3 → K) → Prop)
    (hWu : ∀ v, (∀ k, CaseM.spForm v (u k) = 0) → W v) (hWsmul : ∀ k (c : K), W (c • u k))
    (hWform : ∀ v w, W v → W w → CaseM.spForm v w = 0) {s : StatedSp 3 K} (hs2 : s * s = 1)
    (hsW : ∀ v, W v → W (SpExtras.mat 3 K s *ᵥ v)) : conjSub B (Φ s) = B := by
  have hR := hS.hyp.root
  have hz : Φ s ∈ levi R A A₀ := hrange ▸ ⟨s, rfl⟩
  have hz2 : Φ s * Φ s = 1 := by rw [← map_mul, hs2, map_one]
  have hvec : ∀ {X : Subgroup G}, X ∈ deltaSet R A A₀ B → ∀ {g : StatedSp 3 K},
      X = (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g).map Φ →
      ∀ {v : Fin 3 ⊕ Fin 3 → K}, v ≠ 0 →
      CaseM.IsTransGroup v (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g) → W v := by
    intro X hX g hXg v hv hvT
    by_cases hall : ∀ k, CaseM.spForm v (u k) = 0
    · exact hWu v hall
    push Not at hall
    obtain ⟨k, hk⟩ := hall
    have hc : Commuting X ((Y k).map Φ) := hS.commuting_of_mem_deltaSet' hB hX (hYB k)
    rw [hXg] at hc
    rcases hvT.spForm_eq_zero (hY k) hv ((CaseM.commuting_map_iff hΦ).1 hc) with h0 | ⟨l, hl⟩
    · exact absurd h0 hk
    · have hl0 : l ≠ 0 := fun h0 => by
        rw [h0, zero_smul] at hl
        rw [hl] at hk
        exact hk (by simp [CaseM.spForm])
      have : v = l⁻¹ • u k := by rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul]
      rw [this]
      exact hWsmul k l⁻¹
  refine hS.conjSub_eq_of_deltaSet_subset hB hz hz2 fun X hX => ?_
  obtain ⟨g, hXg⟩ := (hΔ X).1 hX.1
  obtain ⟨v, hv0, hvT⟩ := CaseM.exists_isTransGroup_of_mem (K := K) rfl g
  have hWv := hvec hX hXg hv0 hvT
  have hXz : conjSub X (Φ s) =
      (conjSub (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g) s).map Φ := by
    rw [hXg, map_conjSub_eq]
  have hzT := hvT.conjSub s
  refine hS.mem_deltaSet_of_forall_commuting hB
    (Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hz) fun Y' hY' => ?_
  obtain ⟨g', hY'g⟩ := (hΔ Y').1 hY'.1
  obtain ⟨w, hw0, hwT⟩ := CaseM.exists_isTransGroup_of_mem (K := K) rfl g'
  have hWw := hvec hY' hY'g hw0 hwT
  rw [hXz, hY'g]
  exact (CaseM.commuting_map_iff hΦ).2 (hzT.commuting hwT (hWform _ _ (hsW v hWv) hWw))

theorem commuting_diffRoot_sp {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {K : Type} [Field K] [CharP K 2] (Φ : StatedSp 3 K →* G)
    (hΦ : Function.Injective Φ) (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g).map Φ)
    (hP : ∀ i, (Symplectic.rootGroup 3 K (CaseM.longC3 i)).map Φ = P i)
    (hQ : ∀ i, (Symplectic.rootGroup 3 K (-CaseM.longC3 i)).map Φ = Q i)
    {a b : Fin 3} (hab : a ≠ b) {γ : Fin 3 → ℤ} (hγ : toStd 3 γ = Pi.single a 1 - Pi.single b 1) :
    Commuting ((Symplectic.rootGroup 3 K γ).map Φ) E ∧
      Commuting ((Symplectic.rootGroup 3 K γ).map Φ) ⁅A₀, C⁆ := by
  have hA := hS.mem
  have hthird : ∀ a b : Fin 3, a ≠ b → ∃ t : Fin 3, t ≠ a ∧ t ≠ b := by decide
  obtain ⟨t, hta, htb⟩ := hthird a b hab
  have hz2 : ∀ c : K, Φ (CaseM.diffElt hab c) * Φ (CaseM.diffElt hab c) = 1 := fun c => by
    rw [← map_mul, CaseM.diffElt_mul_self, map_one]
  have hzP : ∀ c : K, ∀ p ∈ P t, Commute (Φ (CaseM.diffElt hab c)) p := by
    intro c p hp
    rw [← hP t] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact (((CaseM.isTransGroup_pos t).commute_of_mulVec_eq
      (CaseM.diffElt_mulVec_single hab hta htb c _ (Or.inl rfl))) x hx).map Φ
  have hzQ : ∀ c : K, ∀ q ∈ Q t, Commute (Φ (CaseM.diffElt hab c)) q := by
    intro c q hq
    rw [← hQ t] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact (((CaseM.isTransGroup_neg t).commute_of_mulVec_eq
      (CaseM.diffElt_mulVec_single hab hta htb c _ (Or.inr rfl))) x hx).map Φ
  constructor
  ·
    rintro _ ⟨x, hx, rfl⟩ e he
    obtain ⟨c, rfl⟩ := (CaseM.mem_rootGroup_diff_iff hab hγ x).1 hx
    have hzE : conjSub E (Φ (CaseM.diffElt hab c)) = E :=
      hS.conjSub_eq_of_preserves Φ hΦ hrange hΔ hfr.memE (u := fun k => Pi.single (Sum.inr k) 1)
        (Y := fun k => Symplectic.rootGroup 3 K (-CaseM.longC3 k)) CaseM.isTransGroup_neg
        (fun k => by rw [hQ k]; exact hfr.memQ k) (fun v => ∀ k, v (Sum.inl k) = 0)
        (fun v hv k => by rw [← CaseM.spForm_single_inr v k]; exact hv k)
        (fun k c j => by simp) (fun v w hv hw => CaseM.spForm_of_inl_eq_zero hv hw)
        (CaseM.diffElt_mul_self hab c) (fun v hv => CaseM.diffElt_mulVec_inl hab c hv)
    exact hS.commute_of_conjSub_eq_of_pair hfr.memE (hfr.memP t).1 (hfr.memQ t).1 (hfr.opposite t)
      (hfr.memQ t).2.1.2.2.symm hzE (hzP c) (hzQ c) (hz2 c) e he
  ·
    rintro _ ⟨x, hx, rfl⟩ e he
    obtain ⟨c, rfl⟩ := (CaseM.mem_rootGroup_diff_iff hab hγ x).1 hx
    have hS₀ : Sec12 R A₀ A := hS.of_mem_omegaSet hS.opp.1 ⟨hA, hS.opp.2.symm⟩
    have hlevi : leviSet R A₀ A = leviSet R A A₀ := Set.inter_comm _ _
    have hlevi' : levi R A₀ A = levi R A A₀ := by simp only [levi, hlevi]
    obtain ⟨hF, -, -, hYF⟩ := CaseD4.commutator_props hS.hyp hA hS.opp hfr.memC
    have hPF : ∀ k, Commuting (P k) ⁅A₀, C⁆ := fun k =>
      hYF (P k) (hfr.memP k).1 (hfr.memP k).2.1.2.2.symm
    have hzF : conjSub ⁅A₀, C⁆ (Φ (CaseM.diffElt hab c)) = ⁅A₀, C⁆ :=
      hS₀.conjSub_eq_of_preserves Φ hΦ (hrange.trans hlevi'.symm)
        (fun X => by rw [hlevi]; exact hΔ X) hF (u := fun k => Pi.single (Sum.inl k) 1)
        (Y := fun k => Symplectic.rootGroup 3 K (CaseM.longC3 k)) CaseM.isTransGroup_pos
        (fun k => by
          rw [hP k]
          exact hS₀.mem_deltaSet_of_commuting hF (hlevi ▸ (hfr.memP k).1) (hPF k).symm)
        (fun v => ∀ k, v (Sum.inr k) = 0)
        (fun v hv k => by
          have := hv k
          rwa [CaseM.spForm_single_inl, neg_eq_zero] at this)
        (fun k c j => by simp) (fun v w hv hw => CaseM.spForm_of_inr_eq_zero hv hw)
        (CaseM.diffElt_mul_self hab c) (fun v hv => CaseM.diffElt_mulVec_inr hab c hv)
    exact hS₀.commute_of_conjSub_eq_of_pair hF (hlevi ▸ (hfr.memQ t).1) (hlevi ▸ (hfr.memP t).1)
      (hfr.opposite t).symm (hPF t) hzF (hzQ c) (hzP c) (hz2 c) e he

theorem exists_aligned_sp_dict {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {K : Type} [Field K] (Φ : StatedSp 3 K →* G)
    (hΦ : Function.Injective Φ) (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g).map Φ) :
    ∃ Φ' : StatedSp 3 K →* G, Function.Injective Φ' ∧ Φ'.range = levi R A A₀ ∧
      (∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
        ∃ g, X = (conjSub (Symplectic.rootGroup 3 K (Pi.single 2 1)) g).map Φ') ∧
      (∀ i, (Symplectic.rootGroup 3 K (CaseM.longC3 i)).map Φ' = P i) ∧
      (∀ i, (Symplectic.rootGroup 3 K (-CaseM.longC3 i)).map Φ' = Q i) := by
  obtain ⟨g, hg⟩ := hS.exists_aligned_sp hfr Φ hΦ hΔ
  have e : ∀ (X₀ : Subgroup (StatedSp 3 K)) (g' : StatedSp 3 K),
      (conjSub X₀ g').map (Φ.comp (MulAut.conj g).toMonoidHom) = (conjSub X₀ (g * g')).map Φ :=
    fun X₀ g' => by rw [← Subgroup.map_map, conjSub_mul]
  refine ⟨Φ.comp (MulAut.conj g).toMonoidHom, hΦ.comp (MulAut.conj g).injective, ?_,
    fun X => ?_, fun i => (hg i).1, fun i => (hg i).2⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj g).surjective,
      ← MonoidHom.range_eq_map, hrange]
  · rw [hΔ X]
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g⁻¹ * g', by rw [e, mul_inv_cancel_left]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g * g', by rw [e]⟩

end Sec12

end CFSG.Timmesfeld.ARS
