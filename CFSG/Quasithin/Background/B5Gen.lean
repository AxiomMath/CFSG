module

public import CFSG.Quasithin.Background.B5IrrA
public import CFSG.Quasithin.Background.B5Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section Generation

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem eq_of_offenders_le (h : B51Hyp G L) {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G)
    (hle : ∀ A, IsFFStarOffender G A → A ≤ T → A ≤ L) : G = L := by
  apply le_antisymm _ (le_G h)
  have hJ : G = ffJ G := h.2.2.2.2.2
  rw [hJ]
  refine iSup_le fun A => iSup_le fun hA => ?_
  obtain ⟨x, hxG, hA', hA'T⟩ := exists_offender_le_sylow hT hA
  have hA'L := hle _ hA' hA'T
  intro a ha
  have h1 : x⁻¹ * a * x ∈ B1.conjAut x⁻¹ A := by
    rw [B1.mem_conjAut]
    have e : x⁻¹⁻¹ * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rw [e]
    exact ha
  have h2 : x⁻¹ * a * x ∈ L := hA'L h1
  have h3 := normal_L h x hxG _ h2
  simpa [mul_assoc] using h3


omit [Finite V] in
@[expose] def conjAct (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) : ↥G →* MulAut ↥L where
  toFun g :=
    { toFun := fun x => ⟨(g : MulAut V) * x * (g : MulAut V)⁻¹, hn g g.2 x x.2⟩
      invFun := fun x => ⟨(g : MulAut V)⁻¹ * x * (g : MulAut V), by
        have := hn (g⁻¹ : ↥G) (G.inv_mem g.2) x x.2
        simpa using this⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp
  map_mul' g h := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp [mul_assoc]

omit [Finite V] in
theorem conjAct_apply (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (g : ↥G) (x : ↥L) :
    ((conjAct hn g x : ↥L) : MulAut V) = (g : MulAut V) * x * (g : MulAut V)⁻¹ := rfl

section OutAb

variable (h : B51Hyp G L)
include h

theorem commutator_mem_fstar (hOut : OutAbelian ↥L) {g k : MulAut V} (hg : g ∈ G) (hk : k ∈ G) :
    ⁅g, k⁆ ∈ quasithinGenFitting G := by
  have hn := normal_L h
  have hLG := le_G h
  obtain ⟨l, hl⟩ := hOut (conjAct hn ⟨g, hg⟩) (conjAct hn ⟨k, hk⟩)
  have hcG : ⁅g, k⁆ ∈ G := G.mul_mem (G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg)) (G.inv_mem hk)
  have hconj : ∀ x : ↥L, (l : MulAut V) * x * (l : MulAut V)⁻¹ = ⁅g, k⁆ * x * ⁅g, k⁆⁻¹ := by
    intro x
    have h1 : conjAct hn ⟨⁅g, k⁆, hcG⟩ = ⁅conjAct hn ⟨g, hg⟩, conjAct hn ⟨k, hk⟩⁆ := by
      have := map_commutatorElement (conjAct hn) (⟨g, hg⟩ : ↥G) ⟨k, hk⟩
      exact this
    have h3 : conjAct hn ⟨⁅g, k⁆, hcG⟩ = MulAut.conj l := h1.trans hl.symm
    have h2 := congrArg (fun φ : MulAut ↥L => ((φ x : ↥L) : MulAut V)) h3
    simp only [conjAct_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact h2.symm
  obtain ⟨d, hd⟩ : ∃ d : MulAut V, d = (l : MulAut V)⁻¹ * ⁅g, k⁆ := ⟨_, rfl⟩
  have hdG : d ∈ G := by
    rw [hd]; exact G.mul_mem (G.inv_mem (hLG l.2)) hcG
  have hdc : ∀ x ∈ L, d * x = x * d := by
    intro x hx
    have h1 := hconj ⟨x, hx⟩
    have key : ⁅g, k⁆ * x = (l : MulAut V) * x * (l : MulAut V)⁻¹ * ⁅g, k⁆ := by
      calc ⁅g, k⁆ * x = (⁅g, k⁆ * x * ⁅g, k⁆⁻¹) * ⁅g, k⁆ := by group
        _ = ((l : MulAut V) * x * (l : MulAut V)⁻¹) * ⁅g, k⁆ := by rw [← h1]
    rw [hd]
    calc (l : MulAut V)⁻¹ * ⁅g, k⁆ * x = (l : MulAut V)⁻¹ * (⁅g, k⁆ * x) := by rw [mul_assoc]
      _ = (l : MulAut V)⁻¹ * ((l : MulAut V) * x * (l : MulAut V)⁻¹ * ⁅g, k⁆) := by rw [key]
      _ = x * ((l : MulAut V)⁻¹ * ⁅g, k⁆) := by group
  have hdF : d ∈ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    obtain ⟨l', hl', z, hz, rfl⟩ := (mem_fstar_iff h).1 hf
    have h1 : l' * d = d * l' := (hdc l' hl').symm
    have h2 : z * d = d * z := central_comm G z hz d hdG
    calc l' * z * d = l' * (z * d) := by rw [mul_assoc]
      _ = l' * (d * z) := by rw [h2]
      _ = (l' * d) * z := by rw [mul_assoc]
      _ = (d * l') * z := by rw [h1]
      _ = d * (l' * z) := by rw [mul_assoc]
  have hdF' : d ∈ quasithinGenFitting G := centralizer_quasithinGenFitting_le G ⟨hdG, hdF⟩
  have hlF : (l : MulAut V) ∈ quasithinGenFitting G := by
    rw [fstar_eq h]; exact Subgroup.mem_sup_left l.2
  have : ⁅g, k⁆ = (l : MulAut V) * d := by rw [hd]; group
  rw [this]
  exact (quasithinGenFitting G).mul_mem hlF hdF'


theorem eq_sup_of_outAbelian (hOut : OutAbelian ↥L) {T : Subgroup (MulAut V)}
    (hT : IsSylowTwoOf T G) : G = L ⊔ T := by
  have hn := normal_L h
  have hLG := le_G h
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hF := fstar_eq h
  have hFG : quasithinGenFitting G ≤ G := quasithinGenFitting_le G
  set N : Subgroup (MulAut V) := quasithinGenFitting G ⊔ T with hN
  have hNG : N ≤ G := sup_le hFG hTG
  have hNn : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    intro g hg x hx
    have h1 : ⁅g, x⁆ ∈ quasithinGenFitting G := commutator_mem_fstar h hOut hg (hNG hx)
    have h2 : g * x * g⁻¹ = ⁅g, x⁆ * x := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact N.mul_mem (Subgroup.mem_sup_left h1) hx
  have hM : ∀ A, IsFFStarOffender G A → A ≤ L ⊔ T := by
    intro A hA
    obtain ⟨x, hxG, hA', hA'T⟩ := exists_offender_le_sylow hT hA
    have hAN : A ≤ N := by
      intro a ha
      have h1 : x⁻¹ * a * x ∈ B1.conjAut x⁻¹ A := by
        rw [B1.mem_conjAut]
        have e : x⁻¹⁻¹ * (x⁻¹ * a * x) * x⁻¹ = a := by group
        rw [e]; exact ha
      have h2 : x⁻¹ * a * x ∈ N := Subgroup.mem_sup_right (hA'T h1)
      have h3 := hNn x hxG _ h2
      simpa [mul_assoc] using h3
    intro a ha
    have haN : a ∈ (L ⊔ T) ⊔ centerOf G := by
      have := hAN ha
      rw [hN, hF, sup_right_comm] at this
      exact this
    have hZn : centerOf G ≤ Subgroup.normalizer ((L ⊔ T : Subgroup (MulAut V)) : Set (MulAut V)) := by
      intro z hz
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (central_comm G z hz m (sup_le hLG hTG hm)).symm
    obtain ⟨m, hm, z, hz, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZn).1 haN
    obtain ⟨k, hk⟩ := hA.2.2.1.isPGroup ⟨m * z, ha⟩
    have hk' : (m * z) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hcomm : Commute m z := (central_comm G z hz m (sup_le hLG hTG hm)).symm
    have hzm : z ^ 2 ^ k ∈ L ⊔ T := by
      have h1 : m ^ 2 ^ k * z ^ 2 ^ k = 1 := by rw [← hcomm.mul_pow]; exact hk'
      have h2 : z ^ 2 ^ k = (m ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact (L ⊔ T).inv_mem ((L ⊔ T).pow_mem hm _)
    have hzc : z ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (central_comm G z hz l (hLG hl)).symm
    have hzodd : Odd (orderOf z) := odd_orderOf_of_mem_centralizer h hz.1 hzc
    exact (L ⊔ T).mul_mem hm (B1Red.mem_of_two_pow_mem_of_odd hzm hzodd)
  apply le_antisymm _ (sup_le hLG hTG)
  have hJ : G = ffJ G := h.2.2.2.2.2
  rw [hJ]
  exact iSup_le fun A => iSup_le fun hA => hM A hA

end OutAb

end Generation

end B5

end CFSG.Quasithin
