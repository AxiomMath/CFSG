module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17Defs

public section

namespace CFSG.Quasithin

namespace S1421QA17

variable {A B : Type} [Group A] [Group B]

theorem mulEquiv_mem_map_iff (e : A ≃* B) (K : Subgroup A) (x : A) :
    e x ∈ K.map e.toMonoidHom ↔ x ∈ K := by
  rw [Subgroup.mem_map_equiv, e.symm_apply_apply]

theorem mulEquiv_map_centralizer_singleton (e : A ≃* B) (j : A) :
    (Subgroup.centralizer ({j} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e j} : Set B) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    show e x * e j = e j * e x
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

theorem mulEquiv_map_inf_centralizer_singleton (e : A ≃* B) (T : Subgroup A) (j : A) :
    T.map e.toMonoidHom ⊓ Subgroup.centralizer ({e j} : Set B) =
      (T ⊓ Subgroup.centralizer ({j} : Set A)).map e.toMonoidHom := by
  rw [Subgroup.map_inf _ _ _ e.injective, mulEquiv_map_centralizer_singleton]

noncomputable def infCentralizerMulEquiv (e : A ≃* B) (T : Subgroup A) (j : A) :
    ↥(T ⊓ Subgroup.centralizer ({j} : Set A)) ≃*
      ↥(T.map e.toMonoidHom ⊓ Subgroup.centralizer ({e j} : Set B)) :=
  (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (mulEquiv_map_inf_centralizer_singleton e T j).symm)

theorem exists_injective_hom_of_mulEquiv {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂]
    [Group H₁] [Group H₂] (eG : G₁ ≃* G₂) (eH : H₁ ≃* H₂)
    (h : ∃ f : G₂ →* H₂, Function.Injective f) : ∃ f : G₁ →* H₁, Function.Injective f := by
  obtain ⟨f, hf⟩ := h
  exact ⟨(eH.symm : H₂ →* H₁).comp (f.comp (eG : G₁ →* G₂)),
    eH.symm.injective.comp (hf.comp eG.injective)⟩

theorem OuterInvolutionData.map (e : A ≃* B) {T N : Subgroup A}
    (h : OuterInvolutionData T N) :
    OuterInvolutionData (T.map e.toMonoidHom) (N.map e.toMonoidHom) := by
  obtain ⟨j, hjT, hjN, hj2, hjc, hw, hP, hE⟩ := h
  refine ⟨e j, (mulEquiv_mem_map_iff e T j).mpr hjT,
    fun hj => hjN ((mulEquiv_mem_map_iff e N j).mp hj), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hj2, map_one]
  · rw [mulEquiv_map_inf_centralizer_singleton, Subgroup.card_map_of_injective e.injective]
    exact hjc
  · intro w hwT hwc hw1
    obtain ⟨w0, hw0T, hw0⟩ := Subgroup.mem_map.mp hwT
    have hw0' : e w0 = w := hw0
    subst hw0'
    have hc : ∀ t ∈ T, t * w0 = w0 * t := fun t ht => e.injective (by
      rw [map_mul, map_mul]
      exact hwc (e t) ((mulEquiv_mem_map_iff e T t).mpr ht))
    have h1 : w0 ≠ 1 := fun h => hw1 (by rw [h, map_one])
    obtain ⟨⟨y, hy, hy2⟩, hx⟩ := hw w0 hw0T hc h1
    refine ⟨⟨e y, ?_, ?_⟩, ?_⟩
    · rw [mulEquiv_map_inf_centralizer_singleton]
      exact (mulEquiv_mem_map_iff e _ y).mpr hy
    · rw [← map_pow, hy2]
    · intro x hxm hx2 hxsq
      rw [mulEquiv_map_inf_centralizer_singleton] at hxm
      obtain ⟨x0, hx0, hx0e⟩ := Subgroup.mem_map.mp hxm
      have hx0' : e x0 = x := hx0e
      subst hx0'
      obtain ⟨z, hzm, hz2⟩ := hxsq
      rw [mulEquiv_map_inf_centralizer_singleton] at hzm
      obtain ⟨z0, hz0, hz0e⟩ := Subgroup.mem_map.mp hzm
      have hz0' : e z0 = z := hz0e
      subst hz0'
      have hx02 : x0 ^ 2 = 1 := e.injective (by rw [map_pow, map_one]; exact hx2)
      have hz02 : z0 ^ 2 = x0 := e.injective (by rw [map_pow]; exact hz2)
      rcases hx x0 hx0 hx02 ⟨z0, hz0, hz02⟩ with h | h
      · left
        rw [h, map_one]
      · right
        rw [h]
  · intro P hPc hP2
    have hP0c : P.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({j} : Set A) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPc hp)
      apply e.injective
      show e (e.symm p * j) = e (j * e.symm p)
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact h1
    calc Nat.card P = Nat.card (P.map e.symm.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.symm.injective).symm
      _ ≤ 32 := hP _ hP0c (hP2.map _)
  · intro u' hu' hu2 hu1
    obtain ⟨hu'T, hu'N⟩ := hu'
    obtain ⟨u, huT, hu⟩ := Subgroup.mem_map.mp hu'T
    have hu'' : e u = u' := hu
    subst hu''
    have huN : u ∈ N := (mulEquiv_mem_map_iff e N u).mp hu'N
    have hu2' : u ^ 2 = 1 := e.injective (by rw [map_pow, map_one]; exact hu2)
    have hu1' : u ≠ 1 := fun h => hu1 (by rw [h, map_one])
    intro hf
    exact hE u ⟨huT, huN⟩ hu2' hu1'
      (exists_injective_hom_of_mulEquiv (infCentralizerMulEquiv e T u)
        (infCentralizerMulEquiv e T j) hf)

theorem OuterInvolutionData.mono {T N N' : Subgroup A} (h : OuterInvolutionData T N)
    (hN : N' ≤ N) : OuterInvolutionData T N' := by
  obtain ⟨j, hjT, hjN, hj2, hjc, hw, hP, hE⟩ := h
  exact ⟨j, hjT, fun hj => hjN (hN hj), hj2, hjc, hw, hP,
    fun u hu => hE u ⟨hu.1, hN hu.2⟩⟩

end S1421QA17

end CFSG.Quasithin
