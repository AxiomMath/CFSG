module

public import CFSG.Monster.GMS.CoTwoAutPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open CFSG.Sporadic.Co1.Module.CoTwoAut
open CFSG.Sporadic.Co2Rank3 (co2Graph co2Aut mem_co2Aut)
open CoTwoAutPerm

@[expose] def Co2NormalizerFact : Prop :=
  ∀ v ∈ co1Orbit 0, ∀ f : (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2),
    (∀ a b, bil₀ a v = 0 → bil₀ b v = 0 → f (a + b) = f a + f b) →
    (∀ w, bil₀ w v = 0 → bil₀ (f w) v = 0) →
    (∀ a b, bil₀ a v = 0 → bil₀ b v = 0 → f a = f b → a = b) →
    f v = v →
    (∀ g ∈ co1Stab v, ∃ h ∈ co1Stab v, ∀ w, bil₀ w v = 0 → f (co1Act g w) = co1Act h (f w)) →
    (∀ h ∈ co1Stab v, ∃ g ∈ co1Stab v, ∀ w, bil₀ w v = 0 → f (co1Act g w) = co1Act h (f w)) →
    ∃ h ∈ co1Stab v, ∀ w, bil₀ w v = 0 → f w + co1Act h w = 0 ∨ f w + co1Act h w = v

namespace CoTwoAutNorm

@[expose] def kOrb (w : Fin 24 → ZMod 2) : Set (Fin 24 → ZMod 2) :=
  {y | ∃ g ∈ co1Stab v₂, co1Act g w = y}

theorem kOrb_perp
    {w y : Fin 24 → ZMod 2} (hw : bil₀ w v₂ = 0) (hy : y ∈ kOrb w) :
    bil₀ y v₂ = 0 := by
  obtain ⟨g, hg, rfl⟩ := hy
  exact CoTwoAutKer.co1Act_perp hg hw

theorem add01_of_class {A B a : Fin 24 → ZMod 2} (hA : A = a ∨ A = v₂ + a)
    (hB : B = a ∨ B = v₂ + a) : A + B = 0 ∨ A + B = v₂ := by
  rcases hA with rfl | rfl <;> rcases hB with h | h
  · left
    rw [h, vec_add_self]
  · right
    rw [h, add_comm v₂, ← add_assoc, vec_add_self, zero_add]
  · right
    rw [h, add_assoc, vec_add_self, add_zero]
  · left
    rw [h, vec_add_self]

theorem normalizer_fact_v₂
    (f : (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2))
    (hadd : ∀ a b, bil₀ a v₂ = 0 → bil₀ b v₂ = 0 → f (a + b) = f a + f b)
    (hperp : ∀ w, bil₀ w v₂ = 0 → bil₀ (f w) v₂ = 0)
    (hinj : ∀ a b, bil₀ a v₂ = 0 → bil₀ b v₂ = 0 → f a = f b → a = b)
    (hfv : f v₂ = v₂)
    (hf1 : ∀ g ∈ co1Stab v₂, ∃ h ∈ co1Stab v₂,
      ∀ w, bil₀ w v₂ = 0 → f (co1Act g w) = co1Act h (f w))
    (hf2 : ∀ h ∈ co1Stab v₂, ∃ g ∈ co1Stab v₂,
      ∀ w, bil₀ w v₂ = 0 → f (co1Act g w) = co1Act h (f w)) :
    ∃ h ∈ co1Stab v₂, ∀ w, bil₀ w v₂ = 0 → f w + co1Act h w = 0 ∨ f w + co1Act h w = v₂ := by
  have himage : ∀ w, bil₀ w v₂ = 0 → f '' kOrb w = kOrb (f w) := by
    intro w hw
    ext y
    constructor
    · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨h, hh, hfg⟩ := hf1 g hg
      exact ⟨h, hh, (hfg w hw).symm⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨g, hg, hfg⟩ := hf2 h hh
      exact ⟨co1Act g w, ⟨g, hg, rfl⟩, hfg w hw⟩
  have hncard : ∀ w, bil₀ w v₂ = 0 → (kOrb (f w)).ncard = (kOrb w).ncard := by
    intro w hw
    rw [← himage w hw]
    refine Set.InjOn.ncard_image fun a ha b hb hab => ?_
    exact hinj a b (kOrb_perp hw ha) (kOrb_perp hw hb) hab
  have hf_cls : ∀ ω ∈ Pairs.cls 3, f ω ∈ Pairs.cls 3 := by
    intro ω hω
    have hP := cls_three_perp hω
    have h4600 : (kOrb (f ω)).ncard = 4600 := by
      rw [hncard ω hP]
      exact ncard_orbitSet_cls_three hω
    rcases classify_perp (hperp ω hP) with h | h | h | h | h
    · rw [h] at h4600
      have := ncard_orbitSet_zero
      exact absurd (h4600.symm.trans this) (by norm_num)
    · rw [h] at h4600
      have := ncard_orbitSet_v₂
      exact absurd (h4600.symm.trans this) (by norm_num)
    · exact h
    · have := ncard_orbitSet_Tadj h
      exact absurd (h4600.symm.trans this) (by norm_num)
    · exact absurd (h4600 ▸ h) (by norm_num)
  have hf_Tadj : ∀ u ∈ Tadj, f u ∈ Tadj := by
    intro u hu
    have hP := Tadj_perp hu
    have h46575 : (kOrb (f u)).ncard = 46575 := by
      rw [hncard u hP]
      exact ncard_orbitSet_Tadj hu
    rcases classify_perp (hperp u hP) with h | h | h | h | h
    · rw [h] at h46575
      have := ncard_orbitSet_zero
      exact absurd (h46575.symm.trans this) (by norm_num)
    · rw [h] at h46575
      have := ncard_orbitSet_v₂
      exact absurd (h46575.symm.trans this) (by norm_num)
    · have := ncard_orbitSet_cls_three h
      exact absurd (h46575.symm.trans this) (by norm_num)
    · exact h
    · exact absurd (h46575 ▸ h) (by norm_num)
  have hf_Tadj_surj : ∀ u ∈ Tadj, ∃ u' ∈ Tadj, f u' = u := by
    have hsub : f '' Tadj ⊆ Tadj := by
      rintro _ ⟨u, hu, rfl⟩
      exact hf_Tadj u hu
    have hcard : Tadj.ncard ≤ (f '' Tadj).ncard := by
      rw [Set.InjOn.ncard_image]
      intro a ha b hb hab
      exact hinj a b (Tadj_perp ha) (Tadj_perp hb) hab
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard
    intro u hu
    rw [← heq] at hu
    obtain ⟨u', hu', hu'e⟩ := hu
    exact ⟨u', hu', hu'e⟩
  have hf_add : ∀ w, bil₀ w v₂ = 0 → f (v₂ + w) = v₂ + f w := fun w hw => by
    rw [hadd v₂ w (bil₀_self _) hw, hfv]
  set σf : Fin 2300 → Fin 2300 := fun i => idx (f (vtx i)) with hσf
  have hvperp : ∀ i, bil₀ (vtx i) v₂ = 0 := fun i => cls_three_perp (vtx_mem_cls_three i)
  have hσspec : ∀ i, f (vtx i) = vtx (σf i) ∨ f (vtx i) = v₂ + vtx (σf i) := fun i =>
    idx_spec (hf_cls _ (vtx_mem_cls_three i))
  have hσinj : Function.Injective σf := by
    intro i j hij
    have hclass : f (vtx i) = f (vtx j) ∨ f (vtx i) = f (v₂ + vtx j) := by
      have h1 := hσspec i
      have h2 := hσspec j
      rw [hij] at h1
      rw [hf_add _ (hvperp j)]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · left; rw [h1, h2]
      · right; rw [h1, h2, v₂_add_v₂_add]
      · right; rw [h1, h2]
      · left; rw [h1, h2]
    rcases hclass with h | h
    · exact vtx_injective (hinj _ _ (hvperp i) (hvperp j) h)
    · exfalso
      have hv := hinj _ _ (hvperp i) (by
        rw [Leech.bil₀_add_left, bil₀_self, hvperp j, add_zero]) h
      apply vtx_add_ne_v₂ i j
      rw [hv, add_assoc, vec_add_self, add_zero]
  have hσbij : Function.Bijective σf := Finite.injective_iff_bijective.1 hσinj
  set σ : Equiv.Perm (Fin 2300) := Equiv.ofBijective σf hσbij with hσ
  have hσaut : σ ∈ co2Aut := by
    refine mem_co2Aut.2 fun x y => ?_
    have hσx : σ x = σf x := rfl
    have hσy : σ y = σf y := rfl
    rw [adj_iff_vtx_add_mem, adj_iff_vtx_add_mem, hσx, hσy]
    have h := add_class_aux (hσspec x) (hσspec y)
    have hxy : bil₀ (vtx x + vtx y) v₂ = 0 := by
      rw [Leech.bil₀_add_left, hvperp x, hvperp y, add_zero]
    rw [← Tadj_class h, ← hadd _ _ (hvperp x) (hvperp y)]
    constructor
    · intro hfT
      obtain ⟨u', hu', hu'e⟩ := hf_Tadj_surj _ hfT
      have := hinj u' _ (Tadj_perp hu') hxy hu'e
      rw [← this]
      exact hu'
    · intro hT
      exact hf_Tadj _ hT
  obtain ⟨g, hg⟩ := exists_kHom_eq hσaut
  have hkperm : ∀ i, kperm g i = σf i := fun i => by
    have h := congrArg (fun τ : Equiv.Perm (Fin 2300) => τ i) hg
    have e : σ i = σf i := rfl
    simp only [kHom_apply, e] at h
    exact h
  refine ⟨g, g.2, ?_⟩
  have hF := perp_forall_of_cls (F := fun w => f w + co1Act g w)
    (fun a b ha hb => by
      show f (a + b) + co1Act g (a + b) = (f a + co1Act g a) + (f b + co1Act g b)
      rw [hadd a b ha hb, map_add, add_add_add_comm])
    (fun ω hω => by
      obtain ⟨i, hi | hi⟩ := exists_vtx_of_mem_cls_three hω
      · rw [hi]
        have e := kperm_spec g.2 i
        rw [hkperm i] at e
        exact add01_of_class (hσspec i) e
      · rw [hi]
        show f (v₂ + vtx i) + co1Act g (v₂ + vtx i) = 0 ∨ _
        rw [hf_add _ (hvperp i), map_add, show co1Act g v₂ = v₂ from g.2,
          add_add_add_comm, vec_add_self, zero_add]
        have e := kperm_spec g.2 i
        rw [hkperm i] at e
        exact add01_of_class (hσspec i) e)
    (Or.inl (by
      show f v₂ + co1Act g v₂ = 0
      rw [hfv, show co1Act g v₂ = v₂ from g.2]
      exact vec_add_self v₂))
  exact hF

theorem conj_inv_mem {c h : Co1} (hh : h ∈ co1Stab (co1Act c v₂)) : c⁻¹ * h * c ∈ co1Stab v₂ := by
  show co1Act (c⁻¹ * h * c) v₂ = v₂
  rw [CoTwoModule.co1Act_mul_apply, CoTwoModule.co1Act_mul_apply, show co1Act h (co1Act c v₂) =
    co1Act c v₂ from hh, CoTwoModule.co1Act_inv_apply]

theorem conj_mem {c h : Co1} (hh : h ∈ co1Stab v₂) : c * h * c⁻¹ ∈ co1Stab (co1Act c v₂) :=
  CoTwoModule.conj_mem_co1Stab hh c

end CoTwoAutNorm

theorem co2NormalizerFact :
    Co2NormalizerFact := by
  intro v hv f hadd hperp hinj hfv hf1 hf2
  obtain ⟨c, rfl⟩ := CoTwoModule.exists_co1Act_eq_v₂ hv
  have hinv : ∀ w, co1Act c⁻¹ (co1Act c w) = w := CoTwoModule.co1Act_inv_apply c
  have happ : ∀ w, co1Act c (co1Act c⁻¹ w) = w := CoTwoModule.co1Act_apply_inv c
  have hbil : ∀ a b, bil₀ (co1Act c a) (co1Act c b) = bil₀ a b := Leech.bil₀_co1Act c
  have hbil' : ∀ a b, bil₀ (co1Act c⁻¹ a) (co1Act c⁻¹ b) = bil₀ a b := Leech.bil₀_co1Act c⁻¹
  have hP : ∀ w, bil₀ w v₂ = 0 → bil₀ (co1Act c w) (co1Act c v₂) = 0 := fun w hw => by
    rw [hbil, hw]
  set f₂ : (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2) := fun w => co1Act c⁻¹ (f (co1Act c w)) with hf₂
  have hf₂c : ∀ w, f (co1Act c w) = co1Act c (f₂ w) := fun w => by
    show f (co1Act c w) = co1Act c (co1Act c⁻¹ (f (co1Act c w)))
    rw [happ]
  obtain ⟨h₂, hh₂, hh₂w⟩ := CoTwoAutNorm.normalizer_fact_v₂ f₂
    (fun a b ha hb => by
      show co1Act c⁻¹ (f (co1Act c (a + b))) = co1Act c⁻¹ (f (co1Act c a)) +
        co1Act c⁻¹ (f (co1Act c b))
      rw [map_add, hadd _ _ (hP a ha) (hP b hb), map_add])
    (fun w hw => by
      show bil₀ (co1Act c⁻¹ (f (co1Act c w))) v₂ = 0
      have h := hbil' (f (co1Act c w)) (co1Act c v₂)
      rw [hinv] at h
      rw [h]
      exact hperp _ (hP w hw))
    (fun a b ha hb hab => by
      have h1 : f (co1Act c a) = f (co1Act c b) := by rw [hf₂c, hf₂c, hab]
      exact CoTwoModule.co1Act_injective c (hinj _ _ (hP a ha) (hP b hb) h1))
    (by
      show co1Act c⁻¹ (f (co1Act c v₂)) = v₂
      rw [hfv, hinv])
    (fun g hg => by
      obtain ⟨h', hh', hh'e⟩ := hf1 (c * g * c⁻¹) (CoTwoAutNorm.conj_mem hg)
      refine ⟨c⁻¹ * h' * c, CoTwoAutNorm.conj_inv_mem hh', fun w hw => ?_⟩
      have e1 : co1Act (c * g * c⁻¹) (co1Act c w) = co1Act c (co1Act g w) := by
        rw [CoTwoModule.co1Act_mul_apply, CoTwoModule.co1Act_mul_apply, hinv]
      show co1Act c⁻¹ (f (co1Act c (co1Act g w))) =
        co1Act (c⁻¹ * h' * c) (co1Act c⁻¹ (f (co1Act c w)))
      rw [← e1, hh'e _ (hP w hw), CoTwoModule.co1Act_mul_apply, CoTwoModule.co1Act_mul_apply,
        happ])
    (fun h hh => by
      obtain ⟨g', hg', hg'e⟩ := hf2 (c * h * c⁻¹) (CoTwoAutNorm.conj_mem hh)
      refine ⟨c⁻¹ * g' * c, CoTwoAutNorm.conj_inv_mem hg', fun w hw => ?_⟩
      have e1 : co1Act (c⁻¹ * g' * c) w = co1Act c⁻¹ (co1Act g' (co1Act c w)) := by
        rw [CoTwoModule.co1Act_mul_apply, CoTwoModule.co1Act_mul_apply]
      show co1Act c⁻¹ (f (co1Act c (co1Act (c⁻¹ * g' * c) w))) =
        co1Act h (co1Act c⁻¹ (f (co1Act c w)))
      rw [e1, happ, hg'e _ (hP w hw), CoTwoModule.co1Act_mul_apply,
        CoTwoModule.co1Act_mul_apply, hinv])
  refine ⟨c * h₂ * c⁻¹, CoTwoAutNorm.conj_mem hh₂, fun w' hw' => ?_⟩
  have hw : bil₀ (co1Act c⁻¹ w') v₂ = 0 := by
    have h := hbil' w' (co1Act c v₂)
    rw [hinv] at h
    rw [h]
    exact hw'
  have e1 : f w' = co1Act c (f₂ (co1Act c⁻¹ w')) := by
    rw [← hf₂c, happ]
  have e2 : co1Act (c * h₂ * c⁻¹) w' = co1Act c (co1Act h₂ (co1Act c⁻¹ w')) := by
    rw [CoTwoModule.co1Act_mul_apply, CoTwoModule.co1Act_mul_apply]
  rw [e1, e2, ← map_add]
  rcases hh₂w _ hw with h | h
  · left
    rw [h, map_zero]
  · right
    rw [h]

end CFSG.Monster.GMS
