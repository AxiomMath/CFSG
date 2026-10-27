module

public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdModel
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdRoot
public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  UCoord SpCoord

private def ggUdF_root {d p : ℕ} (i j : Fin d) : Fin d → Multiplicative (ZMod p) :=
  (UCoord.rootV (p := p) i j : Fin d → Multiplicative (ZMod p))

private theorem ggUdF_root_apply {d p : ℕ} (i j k : Fin d) :
    ggUdF_root (p := p) i j k =
      Multiplicative.ofAdd ((if k = i then (1 : ZMod p) else 0) -
        (if k = j then 1 else 0)) :=
  rfl

private theorem ggUdF_root_mem_sumZero {d p : ℕ} (i j : Fin d) :
    ggUdF_root (p := p) i j ∈ UCoord.sumZero d p :=
  (UCoord.rootV i j).2

private theorem ggUdF_root_self {d p : ℕ} {i j : Fin d} (hij : i ≠ j) :
    ggUdF_root (p := p) i j i = Multiplicative.ofAdd (1 : ZMod p) := by
  rw [ggUdF_root_apply, if_pos rfl, if_neg hij, sub_zero]

private theorem ggUdF_root_of_ne {d p : ℕ} {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) :
    ggUdF_root (p := p) i j k = 1 := by
  rw [ggUdF_root_apply, if_neg hki, if_neg hkj, sub_self]
  rfl

private theorem ggUdF_permAut_root {d p : ℕ} (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    permAut (p := p) σ (ggUdF_root (p := p) i j) =
      ggUdF_root (p := p) (σ i) (σ j) := by
  have h := congrArg (fun f : ↥(UCoord.sumZero d p) =>
    (f : Fin d → Multiplicative (ZMod p))) (UCoord.permAutV_rootV (p := p) σ i j)
  exact h

private theorem ggUdF_ggConjAut_congr {G : Type} [Group G] {Bs : Subgroup G} {g : G}
    (h₁ h₂ : g ∈ Subgroup.normalizer (Bs : Set G)) : ggConjAut Bs h₁ = ggConjAut Bs h₂ := by
  have _ : g ∈ Subgroup.normalizer (Bs : Set G) := h₁
  have _ : g ∈ Subgroup.normalizer (Bs : Set G) := h₂
  rfl

private theorem ggUdF_root_pow_ratio {d p : ℕ} [NeZero p] {i j : Fin d} (hij : i ≠ j)
    {f : Fin d → Multiplicative (ZMod p)} {m : ℕ}
    (hm : (m : ZMod p) * (Multiplicative.toAdd (f j) - Multiplicative.toAdd (f i)) = 1) :
    (permAut (p := p) (Equiv.swap i j) f * f⁻¹) ^ m = ggUdF_root (p := p) i j := by
  funext k
  apply Multiplicative.toAdd.injective
  have hk : (permAut (Equiv.swap i j) f * f⁻¹) k = f ((Equiv.swap i j) k) * (f k)⁻¹ := by
    rw [Pi.mul_apply, Pi.inv_apply, permAut_apply, Function.comp_apply, Equiv.swap_inv]
  rw [Pi.pow_apply, hk, toAdd_pow, toAdd_mul, toAdd_inv, nsmul_eq_mul, ggUdF_root_apply]
  have hroot : Multiplicative.toAdd
      (Multiplicative.ofAdd ((if k = i then 1 else 0) - (if k = j then 1 else 0) : ZMod p))
      = (if k = i then 1 else 0) - (if k = j then 1 else 0) := rfl
  rw [hroot]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, if_pos rfl, if_neg hij, sub_zero]
    rw [← sub_eq_add_neg]
    exact hm
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right, if_neg (Ne.symm hij), if_pos rfl, zero_sub]
      calc (↑m : ZMod p) * (Multiplicative.toAdd (f i) + -Multiplicative.toAdd (f j))
          = -((↑m : ZMod p) *
              (Multiplicative.toAdd (f j) + -Multiplicative.toAdd (f i))) := by ring
        _ = -1 := by rw [← sub_eq_add_neg, hm]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, if_neg hki, if_neg hkj]
      ring

private theorem ggUdF_permAut_eq_one_of_root {d p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 5 ≤ d)
    {σ : Equiv.Perm (Fin d)}
    (h : ∀ i j : Fin d, i ≠ j → ∃ c : Multiplicative (ZMod p),
      permAut (p := p) σ (ggUdF_root (p := p) i j) *
        (ggUdF_root (p := p) i j)⁻¹ = fun _ => c) :
    σ = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨j, hji⟩ : ∃ j : Fin d, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  have hij : i ≠ j := hji.symm
  obtain ⟨c, hc⟩ := h i j hij
  obtain ⟨k, hk⟩ : ∃ k : Fin d, k ≠ σ i ∧ k ≠ σ j ∧ k ≠ i ∧ k ≠ j := by
    have hcard : ({σ i, σ j, i, j} : Finset (Fin d)).card ≤ 4 := by
      have h1 : ({σ i, σ j, i, j} : Finset (Fin d)).card ≤
          ({σ j, i, j} : Finset (Fin d)).card + 1 := Finset.card_insert_le _ _
      have h2 : ({σ j, i, j} : Finset (Fin d)).card ≤
          ({i, j} : Finset (Fin d)).card + 1 := Finset.card_insert_le _ _
      have h3 : ({i, j} : Finset (Fin d)).card ≤ ({j} : Finset (Fin d)).card + 1 :=
        Finset.card_insert_le _ _
      have h4 : ({j} : Finset (Fin d)).card = 1 := Finset.card_singleton j
      omega
    have hlt : ({σ i, σ j, i, j} : Finset (Fin d)).card <
        (Finset.univ : Finset (Fin d)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact ⟨k, hk⟩
  have hc1 : c = 1 := by
    have hk' := congrFun hc k
    rw [Pi.mul_apply, Pi.inv_apply] at hk'
    have hki : σ⁻¹ k ≠ i := by
      intro hh
      apply hk.1
      calc k = σ (σ⁻¹ k) := by simp
        _ = σ i := by rw [hh]
    have hkj : σ⁻¹ k ≠ j := by
      intro hh
      apply hk.2.1
      calc k = σ (σ⁻¹ k) := by simp
        _ = σ j := by rw [hh]
    have h1 : permAut (p := p) σ (ggUdF_root (p := p) i j) k = 1 := by
      rw [permAut_apply, Function.comp_apply, ggUdF_root_of_ne hki hkj]
    have h2 : ggUdF_root (p := p) i j k = 1 := ggUdF_root_of_ne hk.2.2.1 hk.2.2.2
    rw [h1, h2, inv_one, mul_one] at hk'
    exact hk'.symm
  have hsi : σ i = i := by
    have hk' := congrFun hc (σ i)
    rw [hc1, Pi.mul_apply, Pi.inv_apply] at hk'
    have h1 : permAut (p := p) σ (ggUdF_root (p := p) i j) (σ i) =
        ggUdF_root (p := p) i j i := by
      rw [permAut_apply, Function.comp_apply]
      simp
    rw [h1, ggUdF_root_self hij, ggUdF_root_apply] at hk'
    have hx : ((if σ i = i then (1 : ZMod p) else 0) - (if σ i = j then 1 else 0)) = 1 := by
      have h' := congrArg Multiplicative.toAdd hk'
      simp only [toAdd_mul, toAdd_inv, toAdd_one, toAdd_ofAdd] at h'
      have h'' : (1 : ZMod p) -
          ((if σ i = i then (1 : ZMod p) else 0) - (if σ i = j then 1 else 0)) = 0 := by
        simpa [sub_eq_add_neg] using h'
      exact (sub_eq_zero.mp h'').symm
    by_cases hii : σ i = i
    · simpa using hii
    · exfalso
      by_cases hjj : σ i = j
      · rw [if_neg hii, if_pos hjj] at hx
        have h2 : (2 : ZMod p) = 0 := by
          have h3 : (-1 : ZMod p) = 1 := by simpa using hx
          linear_combination -h3
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        have hpge : 2 ≤ p := hp.two_le
        omega
      · rw [if_neg hii, if_neg hjj] at hx
        have h1 : ((1 : ℕ) : ZMod p) = 0 := by simpa using hx.symm
        have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp h1
        have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
        have hpge : 2 ≤ p := hp.two_le
        omega
  simpa using hsi

theorem ggUdTB_frame
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 2) ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    GGWeylFrame p A (CoxeterMatrix.A (d - 1)) ∧
      ∀ N : Subgroup (MulAut ↥A),
        N ≤ ggAutomizer (MulAut.conj : L' →* MulAut L').range A →
        (∀ g ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ m ∈ N,
          g * m * g⁻¹ ∈ N) →
        N ≠ ⊥ → ∀ v : ↥A, (∀ m ∈ N, m v = v) → v = 1 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hmd : m + 1 - 1 = m := Nat.add_sub_cancel m 1
  rw [hmd]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  have hd3 : 3 ≤ m + 1 := by omega
  have hK' : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK (by omega)
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  obtain ⟨φ, hφs, hφker, hdiag, S, Θ, hS_or, hΘs, hΘker, hnorm, hperm⟩ :=
    ggKGTAU_permModel hK hn hd hp hpq hpd hψ hker hperf hA hAI hcard hsc
  have hmem : ∀ (σ : Equiv.Perm (Fin (m + 1))) {f : Fin (m + 1) →
      Multiplicative (ZMod p)}, f ∈ S → permAut σ f ∈ S := by
    intro σ f hf
    rcases hS_or with h | h
    · rw [h]
      exact Subgroup.mem_top _
    · rw [h] at hf ⊢
      exact UCoord.permAut_mem_sumZero σ hf
  have hroot_mem : ∀ i j : Fin (m + 1), ggUdF_root i j ∈ S := by
    intro i j
    rcases hS_or with h | h
    · rw [h]
      exact Subgroup.mem_top _
    · rw [h]
      exact ggUdF_root_mem_sumZero i j
  let mk : Equiv.Perm (Fin (m + 1)) → ↥S → ↥S := fun σ f =>
    ⟨permAut σ (f : Fin (m + 1) → Multiplicative (ZMod p)), hmem σ f.2⟩
  let rootS : (i j : Fin (m + 1)) → ↥S := fun i j => ⟨ggUdF_root i j, hroot_mem i j⟩
  let hn : ∀ σ : Equiv.Perm (Fin (m + 1)),
      MulAut.conj (φ (LineU.permSU hK' σ)) ∈
        Subgroup.normalizer (A : Set (MulAut L')) := fun σ =>
    SuDvdRootGen.conj_permSU_mem_normalizer hK' hpq hd3 hφs hφker hdiag hAp hsc σ
  let Φf : Equiv.Perm (Fin (m + 1)) → MulAut ↥A := fun σ => ggConjAut A (hn σ)
  have hΦ_apply : ∀ (σ : Equiv.Perm (Fin (m + 1))) (f : ↥S),
      Φf σ (Θ f) = Θ (mk σ f) := fun σ f => hperm hK' σ (hn σ) f (mk σ f) rfl
  have hΦ_mul : ∀ σ τ : Equiv.Perm (Fin (m + 1)), Φf σ * Φf τ = Φf (σ * τ) := by
    intro σ τ
    refine MulEquiv.ext fun b => ?_
    obtain ⟨f, rfl⟩ := hΘs b
    rw [MulAut.mul_apply, hΦ_apply τ f, hΦ_apply σ (mk τ f), hΦ_apply (σ * τ) f]
    congr 1
  have hΦ_one : Φf 1 = 1 := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨f, rfl⟩ := hΘs b
    rw [hΦ_apply]
    have h1 : mk 1 f = f := by
      refine Subtype.ext ?_
      show permAut (1 : Equiv.Perm (Fin (m + 1)))
          (f : Fin (m + 1) → Multiplicative (ZMod p)) =
        (f : Fin (m + 1) → Multiplicative (ZMod p))
      funext k
      simp [permAut_apply]
    rw [h1]
    rfl
  let Φ : Equiv.Perm (Fin (m + 1)) →* MulAut ↥A :=
    { toFun := Φf, map_one' := hΦ_one, map_mul' := fun σ τ => (hΦ_mul σ τ).symm }
  have hΦ_apply' : ∀ (σ : Equiv.Perm (Fin (m + 1))) (f : ↥S),
      Φ σ (Θ f) = Θ (mk σ f) := hΦ_apply
  have hrange : Φ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨σ, rfl⟩
      exact ggConjAut_mem_ggAutomizer
        (MonoidHom.mem_range.mpr ⟨φ (LineU.permSU hK' σ), rfl⟩) (hn σ)
    · intro v hv
      obtain ⟨g, hg, hgN, hgv⟩ := mem_ggAutomizer_iff.mp hv
      obtain ⟨mm, rfl⟩ := MonoidHom.mem_range.mp hg
      have hveq : v = ggConjAut A hgN :=
        MulEquiv.ext fun b => Subtype.ext ((hgv b).trans (ggConjAut_apply A hgN b).symm)
      obtain ⟨π, hπ⟩ := hnorm mm hgN
      refine MonoidHom.mem_range.mpr ⟨π, ?_⟩
      rw [hveq]
      refine MulEquiv.ext fun b => ?_
      obtain ⟨f, rfl⟩ := hΘs b
      rw [hΦ_apply']
      exact (hπ f (mk π f) rfl).symm
  have hkerΦ : ∀ σ : Equiv.Perm (Fin (m + 1)), Φ σ = 1 → σ = 1 := by
    intro σ hσ
    apply ggUdF_permAut_eq_one_of_root hp hp2 (by omega : 5 ≤ m + 1)
    intro i j hij
    have h1 : Θ (mk σ (rootS i j)) = Θ (rootS i j) := by
      rw [← hΦ_apply']
      have h' := congrArg (fun x : MulAut ↥A => x (Θ (rootS i j))) hσ
      simpa only [MulAut.one_apply] using h'
    have h2 : Θ (mk σ (rootS i j) * (rootS i j)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      simp
    obtain ⟨c, hc⟩ := (hΘker _).mp h2
    exact ⟨c, hc⟩
  have hΦ_inj : Function.Injective Φ := by
    intro σ τ hστ
    have h1 : Φ (σ * τ⁻¹) = 1 := by
      rw [map_mul, hστ, map_inv, mul_inv_cancel]
    have h2 := hkerΦ (σ * τ⁻¹) h1
    rwa [mul_inv_eq_one] at h2
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm m
  let W : Subgroup (MulAut ↥A) := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  let eΦ : Equiv.Perm (Fin (m + 1)) ≃* ↥W :=
    (MonoidHom.ofInjective hΦ_inj).trans (MulEquiv.subgroupCongr hrange)
  let e : (CoxeterMatrix.A m).Group ≃* ↥W := e0.trans eΦ
  have hgen : ∀ σ : Equiv.Perm (Fin (m + 1)), ((eΦ σ : ↥W) : MulAut ↥A) = Φ σ := by
    intro σ
    dsimp only [eΦ]
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  let nw : Fin m → L' := fun k => φ (LineU.permSU hK' (Equiv.swap k.castSucc k.succ))
  have hnw : ∀ k : Fin m,
      MulAut.conj (nw k) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun k => hn (Equiv.swap k.castSucc k.succ)
  have hweyl : ∀ k : Fin m, GGTorusWeylElt p A (nw k) := fun k =>
    SuDvdRootGen.ggTorusWeylElt_permSU hK' hd3 hφker hdiag hAp
      (Equiv.swap k.castSucc k.succ)
  have hrefl : ∀ k : Fin m, GGIsReflection p (ggConjAut A (hnw k)) := fun k =>
    SuDvdRootGen.isReflection_permSU_swap hK' hp hpq hd3 hφs hφker hdiag hAp hsc
      (Fin.castSucc_lt_succ).ne (hnw k)
  have he : ∀ k : Fin m,
      (e ((CoxeterMatrix.A m).simple k) : MulAut ↥A) = ggConjAut A (hnw k) := by
    intro k
    have hfk : (e ((CoxeterMatrix.A m).simple k) : ↥W) =
        eΦ (Equiv.swap k.castSucc k.succ) := by
      dsimp only [e]
      rw [MulEquiv.trans_apply, he0 k]
    rw [hfk, hgen]
    exact ggUdF_ggConjAut_congr (hn (Equiv.swap k.castSucc k.succ)) (hnw k)
  refine ⟨⟨nw, hnw, hweyl, hrefl, e, he⟩, ?_⟩
  intro N hNW hNnorm hNne v hv
  obtain ⟨f, rfl⟩ := hΘs v
  by_cases hconst : ∃ c : Multiplicative (ZMod p),
      (f : Fin (m + 1) → Multiplicative (ZMod p)) = fun _ => c
  · exact (hΘker f).mpr hconst
  · exfalso
    let T : Subgroup ↥S :=
      { carrier := {g | ∀ n ∈ N, n (Θ g) = Θ g}
        mul_mem' := by
          intro g h hg hh n hn
          rw [map_mul, map_mul, hg n hn, hh n hn]
        one_mem' := by
          intro n hn
          simp
        inv_mem' := by
          intro g hg n hn
          rw [map_inv, map_inv, hg n hn] }
    have hfT : f ∈ T := hv
    have hTinv : ∀ (g : ↥S), g ∈ T → ∀ σ : Equiv.Perm (Fin (m + 1)),
        mk σ g ∈ T := by
      intro g hg σ n hn
      have hw : Φ σ⁻¹ ∈ W := by
        have h' : Φ σ⁻¹ ∈ Φ.range := MonoidHom.mem_range.mpr ⟨σ⁻¹, rfl⟩
        rwa [hrange] at h'
      have hnorm : Φ σ⁻¹ * n * (Φ σ⁻¹)⁻¹ ∈ N := hNnorm _ hw n hn
      have hfix : (Φ σ⁻¹ * n * (Φ σ⁻¹)⁻¹) (Θ g) = Θ g := hg _ hnorm
      have hΦinv : (Φ σ⁻¹)⁻¹ = Φ σ := by rw [map_inv, inv_inv]
      have h1 : (Φ σ⁻¹ * n * (Φ σ⁻¹)⁻¹) (Θ g) = Φ σ⁻¹ (n (Φ σ (Θ g))) := by
        rw [hΦinv, MulAut.mul_apply, MulAut.mul_apply]
      rw [h1] at hfix
      have h2 : n (Φ σ (Θ g)) = Φ σ (Θ g) := by
        have h3 := congrArg (Φ σ) hfix
        rwa [map_inv, MulAut.apply_inv_self] at h3
      rw [← hΦ_apply' σ g]
      exact h2
    obtain ⟨i, j, hfij⟩ : ∃ i j : Fin (m + 1),
        (f : Fin (m + 1) → Multiplicative (ZMod p)) i ≠
          (f : Fin (m + 1) → Multiplicative (ZMod p)) j := by
      by_contra h
      push Not at h
      exact hconst ⟨(f : Fin (m + 1) → Multiplicative (ZMod p)) ⟨0, by omega⟩,
        funext fun k => h k ⟨0, by omega⟩⟩
    have hij : i ≠ j := fun h => hfij (by rw [h])
    have hc0 : (Multiplicative.toAdd ((f : Fin (m + 1) → Multiplicative (ZMod p)) j) -
        Multiplicative.toAdd ((f : Fin (m + 1) → Multiplicative (ZMod p)) i)) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hfij (Multiplicative.toAdd.injective h).symm)
    obtain ⟨q, hq⟩ : ∃ q : ℕ,
        (q : ZMod p) * (Multiplicative.toAdd
          ((f : Fin (m + 1) → Multiplicative (ZMod p)) j) -
          Multiplicative.toAdd
            ((f : Fin (m + 1) → Multiplicative (ZMod p)) i)) = 1 := by
      refine ⟨((Multiplicative.toAdd ((f : Fin (m + 1) → Multiplicative (ZMod p)) j) -
        Multiplicative.toAdd ((f : Fin (m + 1) → Multiplicative (ZMod p)) i))⁻¹).val, ?_⟩
      rw [ZMod.natCast_zmod_val]
      exact inv_mul_cancel₀ hc0
    have hpowS : ((⟨permAut (Equiv.swap i j)
        (f : Fin (m + 1) → Multiplicative (ZMod p)) *
        ((f : Fin (m + 1) → Multiplicative (ZMod p)))⁻¹,
        S.mul_mem (hmem _ f.2) (S.inv_mem f.2)⟩ : ↥S)) ^ q = rootS i j := by
      refine Subtype.ext ?_
      show (permAut (Equiv.swap i j) (f : Fin (m + 1) → Multiplicative (ZMod p)) *
        ((f : Fin (m + 1) → Multiplicative (ZMod p)))⁻¹) ^ q = ggUdF_root i j
      exact ggUdF_root_pow_ratio hij hq
    have hrootT_ij : rootS i j ∈ T := by
      rw [← hpowS]
      exact T.pow_mem (T.mul_mem (hTinv f hfT (Equiv.swap i j)) (T.inv_mem hfT)) q
    have hrootT : ∀ k l : Fin (m + 1), k ≠ l → rootS k l ∈ T := by
      intro k l hkl
      obtain ⟨σ, hσk, hσl⟩ : ∃ σ : Equiv.Perm (Fin (m + 1)), σ i = k ∧ σ j = l := by
        by_cases h : Equiv.swap i k j = l
        · exact ⟨Equiv.swap i k, Equiv.swap_apply_left i k, h⟩
        · have hkm : k ≠ Equiv.swap i k j := by
            intro hh
            have h2 : Equiv.swap i k j = Equiv.swap i k i :=
              hh.symm.trans (Equiv.swap_apply_left i k).symm
            exact hij ((Equiv.swap i k).injective h2).symm
          refine ⟨Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k, ?_, ?_⟩
          · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
            exact Equiv.swap_apply_of_ne_of_ne hkm hkl
          · rw [Equiv.Perm.mul_apply]
            exact Equiv.swap_apply_left _ _
      have himg : mk σ (rootS i j) = rootS k l := by
        refine Subtype.ext ?_
        show permAut σ (ggUdF_root i j) = ggUdF_root k l
        rw [ggUdF_permAut_root, hσk, hσl]
      rw [← himg]
      exact hTinv _ hrootT_ij σ
    have hNbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro n hn
      have hnW : n ∈ W := hNW hn
      have hnW' : n ∈ Φ.range := by rwa [hrange]
      obtain ⟨π, hπn⟩ := MonoidHom.mem_range.mp hnW'
      have hπ1 : π = 1 := by
        apply ggUdF_permAut_eq_one_of_root hp hp2 (by omega : 5 ≤ m + 1)
        intro k l hkl
        have hfix : n (Θ (rootS k l)) = Θ (rootS k l) := (hrootT k l hkl) n hn
        rw [← hπn] at hfix
        have hfix' : Θ (mk π (rootS k l)) = Θ (rootS k l) := by
          rw [← hΦ_apply']
          exact hfix
        have h1 : Θ (mk π (rootS k l) * (rootS k l)⁻¹) = 1 := by
          rw [map_mul, map_inv, hfix']
          simp
        obtain ⟨c, hc⟩ := (hΘker _).mp h1
        exact ⟨c, hc⟩
      rw [← hπn, hπ1, map_one]
      exact Subgroup.mem_bot.mpr rfl
    exact hNne hNbot

end CFSG.StandardType

end
