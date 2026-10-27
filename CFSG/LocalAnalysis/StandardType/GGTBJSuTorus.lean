module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuCore
public import CFSG.LocalAnalysis.StandardType.GGTBJSuModel
public import CFSG.LocalAnalysis.StandardType.GGTBJLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial UCoord UModel CFSG.HardMathSupport.Solomon.Coordinator

theorem ggTBJ_su_torusJNoncomm
    {K : Type} [Field K] [Finite K] {n d p r : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 4 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    {I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) I L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let hU : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK (by omega)
  obtain ⟨u, hu, huq, hord, ψP, σ, Θ, hψPsurj, hkerP, hψσ, hΘ, hWeyl⟩ :=
    ggTBJ_su_stdModel (p := p) (r := r) (I := I) (L' := L') (h := hU)
      hK (by omega) hd hp hp2 hpq hpd hIp ψ₀ A hA
  let f₀ : ↥(sumZero d p) := Θ.symm ⟨y, hy⟩
  have hΘf₀ : Θ f₀ = ⟨y, hy⟩ := MulEquiv.apply_symm_apply Θ _
  have hy_eq : y = MulAut.conj (σ f₀) := by
    have h := hΘ f₀
    rw [hΘf₀] at h
    exact h
  have hfix : fixSubgroup y = Subgroup.centralizer ({σ f₀} : Set L') := by
    rw [hy_eq]; exact ggTBJ_fixSubgroup_conj (σ f₀)
  have hJcent : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')) := by
    rw [hfix] at hJ
    exact hJ
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (σ f₀))) := by
    rw [ggTBJ_fixSubgroup_conj]
    exact hJcent
  have hJgg : CFSG.Assembly.IsComponentOf J (ggFix (MulAut.conj (σ f₀))) :=
    (isComponentOf_iff_open).mpr hJ'
  have hc : ∀ l : L', MulAut.conj (ψ₀ (σ f₀)) (ψ₀ l) = ψ₀ (MulAut.conj (σ f₀) l) := by
    intro l
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hSfix : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (fixSubgroup (MulAut.conj (ψ₀ (σ f₀)))) :=
    USixTwo.isComponentOf_map_fix hA.1 hA.2.1 hc hJgg
  have hScent : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (Subgroup.centralizer ({ψP (ggTBJSuD hU hu huq hord f₀)} :
        Set (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) := by
    have h := hSfix
    rw [ggTBJ_fixSubgroup_conj, hψσ f₀] at h
    exact h
  have hJR : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (ψP.range ⊓ Subgroup.centralizer ({ψP (ggTBJSuD hU hu huq hord f₀)} :
        Set (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) := by
    rw [MonoidHom.range_eq_top.mpr hψPsurj, top_inf_eq]
    exact hScent
  let B : Subgroup (MulAut L') := A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')
  have hcardB : Nat.card ↥B = Nat.card {f : ↥(sumZero d p) //
      ∀ j ∈ J, σ f * j = j * σ f} := by
    refine Nat.card_congr ?_
    let toF : ↥B → {f : ↥(sumZero d p) // ∀ j ∈ J, σ f * j = j * σ f} := fun b =>
      let f : ↥(sumZero d p) := Θ.symm ⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩
      ⟨f, by
        intro j hj
        have hbj : (b : MulAut L') j = j := by
          have h := MulAction.mem_stabilizer_iff.mp
            (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp b.2).2 ⟨j, hj⟩)
          simpa [MulAut.smul_def] using h
        have hbf : (b : MulAut L') = MulAut.conj (σ f) := by
          have hfA : Θ f = (⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩ : ↥A) :=
            MulEquiv.apply_symm_apply Θ _
          rw [← hΘ f]
          exact (congrArg Subtype.val hfA).symm
        rw [hbf, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hbj
        exact hbj⟩
    let toG : {f : ↥(sumZero d p) // ∀ j ∈ J, σ f * j = j * σ f} → ↥B :=
      fun c => ⟨((Θ c.1 : ↥A) : MulAut L'), by
        refine Subgroup.mem_inf.mpr ⟨(Θ c.1).2, ?_⟩
        rw [Subgroup.mem_iInf]
        intro j
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hΘ, MulAut.conj_apply]
        have hcomm := c.2 j j.2
        rw [hcomm]
        group⟩
    refine ⟨toF, toG, ?_, ?_⟩
    · intro b
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.apply_symm_apply]
    · intro c
      apply Subtype.ext
      simp only [toF, toG]
      rw [MulEquiv.symm_apply_eq]
  have hcardA : Nat.card ↥A = p ^ (d - 1) := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact ggTBRowPerm_card_sumZero' d p
  have hcount' : p ^ 2 * Nat.card {f : ↥(sumZero d p) //
      ∀ j ∈ J, σ f * j = j * σ f} ≤ p ^ (d - 1) := by
    rw [← hcardB, ← hcardA]
    exact hcount
  have hiff : ∀ f : ↥(sumZero d p),
      (∀ j ∈ J, σ f * j = j * σ f) ↔
        (∀ j₀ ∈ J.map ψ₀, ψP (ggTBJSuD hU hu huq hord f) * j₀ =
          j₀ * ψP (ggTBJSuD hU hu huq hord f)) := by
    intro f
    have hJperf : ⁅J, J⁆ = J := by
      rw [← Subgroup.map_subtype_commutator, hJgg.2.2.1, Subgroup.map_top,
        Subgroup.range_subtype]
    constructor
    · intro h s hs
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hs
      rw [← hψσ f, ← map_mul, ← map_mul, h j hj]
    · intro h j hj
      have hker : ∀ t ∈ J, MulAut.conj (σ f) t * t⁻¹ ∈ ψ₀.ker := by
        intro t ht
        rw [MonoidHom.mem_ker]
        have htS : ψ₀ t ∈ J.map ψ₀ := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
        have hcomm : ψ₀ t * ψ₀ (σ f) = ψ₀ (σ f) * ψ₀ t := by
          have h' := (h (ψ₀ t) htS).symm
          rw [← hψσ f] at h'
          exact h'
        rw [MulAut.conj_apply]
        rw [map_mul, map_inv, map_mul, map_mul, map_inv]
        calc ψ₀ (σ f) * ψ₀ t * (ψ₀ (σ f))⁻¹ * (ψ₀ t)⁻¹
            = ψ₀ t * ψ₀ (σ f) * (ψ₀ (σ f))⁻¹ * (ψ₀ t)⁻¹ := by rw [← hcomm]
          _ = 1 := by group
      have hfixj := USixTwo.fix_of_perfect hA.2.1 hJperf hker j hj
      rw [MulAut.conj_apply] at hfixj
      exact mul_inv_eq_iff_eq_mul.mp hfixj
  have hPQ : Nat.card {f : ↥(sumZero d p) //
        ∀ j₀ ∈ J.map ψ₀, ψP (ggTBJSuD hU hu huq hord f) * j₀ =
          j₀ * ψP (ggTBJSuD hU hu huq hord f)} =
      Nat.card {f : ↥(sumZero d p) // ∀ j ∈ J, σ f * j = j * σ f} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => (hiff f).symm)
  have hcount_core : p ^ 2 * Nat.card {f : ↥(sumZero d p) //
      ∀ j₀ ∈ J.map ψ₀, ψP (ggTBJSuD hU hu huq hord f) * j₀ =
        j₀ * ψP (ggTBJSuD hU hu huq hord f)} ≤ p ^ (d - 1) := by
    rw [hPQ]
    exact hcount'
  obtain ⟨n₁, n₂, s₁, s₂, hn₁, hn₂, hform₁, hform₂, hs₁, hs₂, hfix₁, hfix₂, hne⟩ :=
    ggTBJ_su_core hU hK hn hp hp2 hpq hd hpd hu huq hord ψP hkerP f₀ hJR hcount_core
  obtain ⟨l₁, hl₁J, hl₁eq⟩ := Subgroup.mem_map.mp hn₁
  obtain ⟨l₂, hl₂J, hl₂eq⟩ := Subgroup.mem_map.mp hn₂
  have hψform₁ : ∀ f, ψ₀ l₁ * ψ₀ (σ f) * (ψ₀ l₁)⁻¹ = ψ₀ (σ (s₁ f)) := by
    intro f
    rw [hl₁eq, hψσ f, hψσ (s₁ f)]
    exact hform₁ f
  have hψform₂ : ∀ f, ψ₀ l₂ * ψ₀ (σ f) * (ψ₀ l₂)⁻¹ = ψ₀ (σ (s₂ f)) := by
    intro f
    rw [hl₂eq, hψσ f, hψσ (s₂ f)]
    exact hform₂ f
  obtain ⟨hn₁', heq₁⟩ := exists_ggConjAut_eq_congr (V := ↥(sumZero d p))
    (ψ := ψ₀) (A := A) (σ := σ) hA.2.1 Θ hΘ (n := l₁) (s := s₁) hψform₁
  obtain ⟨hn₂', heq₂⟩ := exists_ggConjAut_eq_congr (V := ↥(sumZero d p))
    (ψ := ψ₀) (A := A) (σ := σ) hA.2.1 Θ hΘ (n := l₂) (s := s₂) hψform₂
  have hcardV : Nat.card ↥(sumZero d p) = p ^ (d - 1) := ggTBRowPerm_card_sumZero' d p
  have hfixV₁ : Nat.card {f : ↥(sumZero d p) // s₁ f = f} * p =
      Nat.card ↥(sumZero d p) := by
    rw [hcardV]; exact hfix₁
  have hfixV₂ : Nat.card {f : ↥(sumZero d p) // s₂ f = f} * p =
      Nat.card ↥(sumZero d p) := by
    rw [hcardV]; exact hfix₂
  have hrefl₁ : GGIsReflection p (MulAut.congr Θ s₁) :=
    ⟨by rw [← map_pow, hs₁, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₁) hfixV₁).2⟩
  have hrefl₂ : GGIsReflection p (MulAut.congr Θ s₂) :=
    ⟨by rw [← map_pow, hs₂, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₂) hfixV₂).2⟩
  have hrefl₁' : GGIsReflection p (ggConjAut A hn₁') := by rw [heq₁]; exact hrefl₁
  have hrefl₂' : GGIsReflection p (ggConjAut A hn₂') := by rw [heq₂]; exact hrefl₂
  have hne' : MulAut.congr Θ s₁ * MulAut.congr Θ s₂ ≠
      MulAut.congr Θ s₂ * MulAut.congr Θ s₁ := by
    intro h
    apply hne
    apply (MulAut.congr Θ).injective
    rw [map_mul, map_mul]
    exact h
  have hconjne : ggConjAut A hn₁' * ggConjAut A hn₂' ≠
      ggConjAut A hn₂' * ggConjAut A hn₁' := by
    rw [heq₁, heq₂]
    exact hne'
  exact ⟨l₁, l₂, hn₁', hn₂', hl₁J, hl₂J, hWeyl l₁ hn₁', hWeyl l₂ hn₂',
    hrefl₁', hrefl₂', hconjne⟩

end CFSG.StandardType

end
