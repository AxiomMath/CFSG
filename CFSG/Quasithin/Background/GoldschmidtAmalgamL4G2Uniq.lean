module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Ext
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Uniq

public section

namespace CFSG.Quasithin.F6.GoldAmL4

variable {D E : Type*} [Group D] [Group E]

structure RhoRel (a b s ρ : D) : Prop where
  hρ : ρ * ρ = 1
  hρa : ρ * a * ρ = a⁻¹
  hρb : ρ * b * ρ = b⁻¹
  hρs : ρ * s * ρ = s

structure ARho (a b s x ρ : D) : Prop extends RhoRel a b s ρ where
  hρx : ρ * x * ρ = x

structure BRho (a b s y ρ : D) : Prop extends RhoRel a b s ρ where
  hρy : ρ * y * ρ = a * b⁻¹ * y

theorem isAmalgamIso_of_agree {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E} (φ₁ : ↥H₁ ≃* ↥K₁)
    (φ₂ : ↥H₂ ≃* ↥K₂)
    (hag : ∀ (x : D) (hx₁ : x ∈ H₁) (hx₂ : x ∈ H₂),
      ((φ₁ ⟨x, hx₁⟩ : ↥K₁) : E) = ((φ₂ ⟨x, hx₂⟩ : ↥K₂) : E))
    (hsurj : ∀ y : E, y ∈ K₁ → y ∈ K₂ →
      ∃ (x : D) (hx₁ : x ∈ H₁), x ∈ H₂ ∧ ((φ₁ ⟨x, hx₁⟩ : ↥K₁) : E) = y) :
    IsAmalgamIso H₁ H₂ K₁ K₂ := by
  refine ⟨φ₁, φ₂, hag, fun y hy₁ hy₂ => ?_⟩
  obtain ⟨x, hx₁, hx₂, hxy⟩ := hsurj y hy₁ hy₂
  have e₁ : φ₁.symm ⟨y, hy₁⟩ = ⟨x, hx₁⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hxy.symm
  have e₂ : φ₂.symm ⟨y, hy₂⟩ = ⟨x, hx₂⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext ((hag x hx₁ hx₂).symm.trans hxy).symm
  rw [e₁, e₂]

theorem closure_abs_rho {a b s ρ : D} (h : RhoRel a b s ρ) :
    ∃ hn : ∀ g ∈ Subgroup.closure ({a, b, s} : Set D),
        ρ * g * ρ ∈ Subgroup.closure ({a, b, s} : Set D),
      Subgroup.closure ({a, b, s, ρ} : Set D) =
        twoExt (Subgroup.closure ({a, b, s} : Set D)) ρ h.hρ hn := by
  have hn : ∀ g ∈ Subgroup.closure ({a, b, s} : Set D),
      ρ * g * ρ ∈ Subgroup.closure ({a, b, s} : Set D) := by
    refine normalizes_of_gens rfl h.hρ ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [h.hρa]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [h.hρb]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [h.hρs]
      exact Subgroup.subset_closure (by simp)
  refine ⟨hn, ?_⟩
  rw [← closure_union_eq h.hρ hn, ← closure_union_closure]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem exists_vertex_ext_rho {a b s v w : D} {a' b' s' v' w' : E} {ρ : D} {ρ' : E}
    (h : RhoRel a b s ρ) (h' : RhoRel a' b' s' ρ') (hvw : ρ * v * ρ = w)
    (hvw' : ρ' * v' * ρ' = w') (hwB : w ∈ Subgroup.closure ({a, b, s, v} : Set D))
    (hwB' : w' ∈ Subgroup.closure ({a', b', s', v'} : Set E))
    (hρ : ρ ∉ Subgroup.closure ({a, b, s, v} : Set D))
    (hρ' : ρ' ∉ Subgroup.closure ({a', b', s', v'} : Set E))
    (φ : ↥(Subgroup.closure ({a, b, s, v} : Set D)) ≃*
      ↥(Subgroup.closure ({a', b', s', v'} : Set E)))
    (ha : ((φ ⟨a, Subgroup.subset_closure (by simp)⟩ :
      ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) = a')
    (hb : ((φ ⟨b, Subgroup.subset_closure (by simp)⟩ :
      ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) = b')
    (hs : ((φ ⟨s, Subgroup.subset_closure (by simp)⟩ :
      ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) = s')
    (hv : ((φ ⟨v, Subgroup.subset_closure (by simp)⟩ :
      ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) = v')
    (hw : ((φ ⟨w, hwB⟩ : ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) = w') :
    ∃ Φ : ↥(Subgroup.closure ((Subgroup.closure ({a, b, s, v} : Set D) : Set D) ∪ {ρ})) ≃*
        ↥(Subgroup.closure ((Subgroup.closure ({a', b', s', v'} : Set E) : Set E) ∪ {ρ'})),
      (∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, v} : Set D)),
        ((Φ ⟨g, Subgroup.subset_closure (Or.inl hg)⟩ :
          ↥(Subgroup.closure ((Subgroup.closure ({a', b', s', v'} : Set E) : Set E) ∪ {ρ'}))) :
            E) = ((φ ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E)) ∧
      ((Φ ⟨ρ, Subgroup.subset_closure (Or.inr rfl)⟩ :
        ↥(Subgroup.closure ((Subgroup.closure ({a', b', s', v'} : Set E) : Set E) ∪ {ρ'}))) :
          E) = ρ' := by
  have haB : a ∈ Subgroup.closure ({a, b, s, v} : Set D) := Subgroup.subset_closure (by simp)
  have hbB : b ∈ Subgroup.closure ({a, b, s, v} : Set D) := Subgroup.subset_closure (by simp)
  have hsB : s ∈ Subgroup.closure ({a, b, s, v} : Set D) := Subgroup.subset_closure (by simp)
  have haB' : a' ∈ Subgroup.closure ({a', b', s', v'} : Set E) := Subgroup.subset_closure (by simp)
  have hbB' : b' ∈ Subgroup.closure ({a', b', s', v'} : Set E) := Subgroup.subset_closure (by simp)
  have hsB' : s' ∈ Subgroup.closure ({a', b', s', v'} : Set E) := Subgroup.subset_closure (by simp)
  have hgen : ∀ g ∈ ({a, b, s, v} : Set D),
      ρ * g * ρ ∈ Subgroup.closure ({a, b, s, v} : Set D) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg <;> subst g
    · rw [h.hρa]; exact Subgroup.inv_mem _ haB
    · rw [h.hρb]; exact Subgroup.inv_mem _ hbB
    · rw [h.hρs]; exact hsB
    · rw [hvw]; exact hwB
  have hgen' : ∀ g ∈ ({a', b', s', v'} : Set E),
      ρ' * g * ρ' ∈ Subgroup.closure ({a', b', s', v'} : Set E) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg <;> subst g
    · rw [h'.hρa]; exact Subgroup.inv_mem _ haB'
    · rw [h'.hρb]; exact Subgroup.inv_mem _ hbB'
    · rw [h'.hρs]; exact hsB'
    · rw [hvw']; exact hwB'
  have hn := normalizes_of_gens (S := ({a, b, s, v} : Set D)) rfl h.hρ hgen
  have hinv : ∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, v} : Set D)),
      ((φ ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) =
        ((φ ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E)⁻¹ := by
    intro g hg
    rw [show (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : ↥(Subgroup.closure ({a, b, s, v} : Set D))) =
      (⟨g, hg⟩ : ↥(Subgroup.closure ({a, b, s, v} : Set D)))⁻¹ from rfl, map_inv,
      Subgroup.coe_inv]
  have hφ : ∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, v} : Set D)),
      g ∈ ({a, b, s, v} : Set D) →
      ((φ ⟨ρ * g * ρ, normalizes_of_gens (S := ({a, b, s, v} : Set D)) rfl h.hρ hgen g hg⟩ :
        ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) =
        ρ' * ((φ ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', v'} : Set E))) : E) * ρ' := by
    intro g hg hgS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgS
    rcases hgS with hgS | hgS | hgS | hgS <;> subst g
    · exact compat_gen_aux hn φ hg (Subgroup.inv_mem _ hg) h.hρa ha
        ((hinv _ hg).trans (by rw [ha])) h'.hρa
    · exact compat_gen_aux hn φ hg (Subgroup.inv_mem _ hg) h.hρb hb
        ((hinv _ hg).trans (by rw [hb])) h'.hρb
    · exact compat_gen_aux hn φ hg hg h.hρs hs hs h'.hρs
    · exact compat_gen_aux hn φ hg hwB hvw hv hw hvw'
  exact exists_vertex_ext (S := ({a, b, s, v} : Set D)) (S' := ({a', b', s', v'} : Set E))
    rfl rfl h.hρ h'.hρ hgen hgen' hρ hρ' φ hφ

theorem mem_closure_abs_rho_iff {a b s ρ : D} (h : RhoRel a b s ρ) (g : D) :
    g ∈ Subgroup.closure ({a, b, s, ρ} : Set D) ↔
      g ∈ Subgroup.closure ({a, b, s} : Set D) ∨ g * ρ ∈ Subgroup.closure ({a, b, s} : Set D) := by
  obtain ⟨hn, e⟩ := closure_abs_rho h
  rw [e]
  exact Iff.rfl

theorem mem_closure_four_a (a b s v : D) : a ∈ Subgroup.closure ({a, b, s, v} : Set D) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_closure_four_b (a b s v : D) : b ∈ Subgroup.closure ({a, b, s, v} : Set D) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem mem_closure_four_s (a b s v : D) : s ∈ Subgroup.closure ({a, b, s, v} : Set D) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

theorem mem_closure_four_v (a b s v : D) : v ∈ Subgroup.closure ({a, b, s, v} : Set D) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem closure_five_eq (a b s v ρ : D) :
    Subgroup.closure ({a, b, s, v, ρ} : Set D) =
      Subgroup.closure ((Subgroup.closure ({a, b, s, v} : Set D) : Set D) ∪ {ρ}) := by
  rw [← closure_union_closure]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem closure_three_le_four (a b s v : D) :
    Subgroup.closure ({a, b, s} : Set D) ≤ Subgroup.closure ({a, b, s, v} : Set D) := by
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  tauto

theorem closure_four_le_five (a b s v ρ : D) :
    Subgroup.closure ({a, b, s, v} : Set D) ≤ Subgroup.closure ({a, b, s, v, ρ} : Set D) := by
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  tauto

theorem mem_closure_five_rho (a b s v ρ : D) : ρ ∈ Subgroup.closure ({a, b, s, v, ρ} : Set D) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))

theorem iso_value_mul {U : Subgroup D} {U' : Subgroup E} {ρ : D} (Φ : ↥U ≃* ↥U') {g u : D}
    (hg : g ∈ U) (hu : u ∈ U) (hρU : ρ ∈ U) (e : g = u * ρ) :
    ((Φ ⟨g, hg⟩ : ↥U') : E) = ((Φ ⟨u, hu⟩ : ↥U') : E) * ((Φ ⟨ρ, hρU⟩ : ↥U') : E) := by
  have : (⟨g, hg⟩ : ↥U) = ⟨u, hu⟩ * ⟨ρ, hρU⟩ := Subtype.ext e
  rw [this, map_mul, Subgroup.coe_mul]

theorem isAmalgamIso_of_rho_tuples {a b s x y ρ : D} {a' b' s' x' y' ρ' : E}
    (hA : ARel a b s x) (hB : BRel a b s y) (hA' : ARel a' b' s' x') (hB' : BRel a' b' s' y')
    (hAρ : ARho a b s x ρ) (hBρ : BRho a b s y ρ) (hAρ' : ARho a' b' s' x' ρ')
    (hBρ' : BRho a' b' s' y' ρ')
    (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set D)) = 32)
    (hcard' : Nat.card (Subgroup.closure ({a', b', s'} : Set E)) = 32)
    (hρA : ρ ∉ Subgroup.closure ({a, b, s, x} : Set D))
    (hρB : ρ ∉ Subgroup.closure ({a, b, s, y} : Set D))
    (hρA' : ρ' ∉ Subgroup.closure ({a', b', s', x'} : Set E))
    (hρB' : ρ' ∉ Subgroup.closure ({a', b', s', y'} : Set E))
    (hinf : Subgroup.closure ({a, b, s, y, ρ} : Set D) ⊓
      Subgroup.closure ({a, b, s, x, ρ} : Set D) = Subgroup.closure ({a, b, s, ρ} : Set D))
    (hinf' : Subgroup.closure ({a', b', s', y', ρ'} : Set E) ⊓
      Subgroup.closure ({a', b', s', x', ρ'} : Set E) =
        Subgroup.closure ({a', b', s', ρ'} : Set E)) :
    IsAmalgamIso (Subgroup.closure ({a, b, s, y, ρ} : Set D))
      (Subgroup.closure ({a, b, s, x, ρ} : Set D))
      (Subgroup.closure ({a', b', s', y', ρ'} : Set E))
      (Subgroup.closure ({a', b', s', x', ρ'} : Set E)) := by
  obtain ⟨φ₁, φ₂, hv₁, hv₂, hφy, hφx⟩ := exists_vertex_isos hA hB hA' hB' hcard hcard'
  have hT := hA.toTRel
  have hT' := hA'.toTRel
  have haB := mem_closure_four_a a b s y
  have hbB := mem_closure_four_b a b s y
  have hsB := mem_closure_four_s a b s y
  have hyB := mem_closure_four_v a b s y
  have haA := mem_closure_four_a a b s x
  have hbA := mem_closure_four_b a b s x
  have hsA := mem_closure_four_s a b s x
  have hxA := mem_closure_four_v a b s x
  have key₁ : ∀ (w : Tc) (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, y} : Set D)),
      g = hT.emb w →
      ((φ₁ ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', y'} : Set E))) : E) = hT'.emb w := by
    intro w g hg hge
    subst hge
    exact hv₁ w hg
  have key₂ : ∀ (w : Tc) (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, x} : Set D)),
      g = hT.emb w →
      ((φ₂ ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', x'} : Set E))) : E) = hT'.emb w := by
    intro w g hg hge
    subst hge
    exact hv₂ w hg
  have ha₁ := (key₁ tA a haB hT.emb_tA.symm).trans hT'.emb_tA
  have hb₁ := (key₁ tB b hbB hT.emb_tB.symm).trans hT'.emb_tB
  have hs₁ := (key₁ tS s hsB hT.emb_tS.symm).trans hT'.emb_tS
  have ha₂ := (key₂ tA a haA hT.emb_tA.symm).trans hT'.emb_tA
  have hb₂ := (key₂ tB b hbA hT.emb_tB.symm).trans hT'.emb_tB
  have hs₂ := (key₂ tS s hsA hT.emb_tS.symm).trans hT'.emb_tS
  have hwB : a * b⁻¹ * y ∈ Subgroup.closure ({a, b, s, y} : Set D) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ haB (Subgroup.inv_mem _ hbB)) hyB
  have hwB' : a' * b'⁻¹ * y' ∈ Subgroup.closure ({a', b', s', y'} : Set E) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_closure_four_a a' b' s' y')
      (Subgroup.inv_mem _ (mem_closure_four_b a' b' s' y'))) (mem_closure_four_v a' b' s' y')
  have hw₁ : ((φ₁ ⟨a * b⁻¹ * y, hwB⟩ : ↥(Subgroup.closure ({a', b', s', y'} : Set E))) : E) =
      a' * b'⁻¹ * y' := by
    have e : (⟨a * b⁻¹ * y, hwB⟩ : ↥(Subgroup.closure ({a, b, s, y} : Set D))) =
        ⟨a, haB⟩ * (⟨b, hbB⟩ : ↥(Subgroup.closure ({a, b, s, y} : Set D)))⁻¹ * ⟨y, hyB⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ha₁, hb₁, hφy]
  obtain ⟨ΦB, hΦB, hΦBρ⟩ := exists_vertex_ext_rho hBρ.toRhoRel hBρ'.toRhoRel hBρ.hρy hBρ'.hρy
    hwB hwB' hρB hρB' φ₁ ha₁ hb₁ hs₁ hφy hw₁
  obtain ⟨ΦA, hΦA, hΦAρ⟩ := exists_vertex_ext_rho hAρ.toRhoRel hAρ'.toRhoRel hAρ.hρx hAρ'.hρx
    hxA (mem_closure_four_v a' b' s' x') hρA hρA' φ₂ ha₂ hb₂ hs₂ hφx hφx
  have eB := closure_five_eq a b s y ρ
  have eA := closure_five_eq a b s x ρ
  have eB' := closure_five_eq a' b' s' y' ρ'
  have eA' := closure_five_eq a' b' s' x' ρ'
  have hBB := closure_three_le_four a b s y
  have hAA := closure_three_le_four a b s x
  have hB5 := closure_four_le_five a b s y ρ
  have hA5 := closure_four_le_five a b s x ρ
  have hρB5 := mem_closure_five_rho a b s y ρ
  have hρA5 := mem_closure_five_rho a b s x ρ
  have hR := hBρ.toRhoRel
  have hR' := hBρ'.toRhoRel
  let φB : ↥(Subgroup.closure ({a, b, s, y, ρ} : Set D)) ≃*
      ↥(Subgroup.closure ({a', b', s', y', ρ'} : Set E)) :=
    (MulEquiv.subgroupCongr eB).trans (ΦB.trans (MulEquiv.subgroupCongr eB'.symm))
  let φA : ↥(Subgroup.closure ({a, b, s, x, ρ} : Set D)) ≃*
      ↥(Subgroup.closure ({a', b', s', x', ρ'} : Set E)) :=
    (MulEquiv.subgroupCongr eA).trans (ΦA.trans (MulEquiv.subgroupCongr eA'.symm))
  have valB : ∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, y, ρ} : Set D)) (w : Tc),
      g = hT.emb w → ((φB ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', y', ρ'} : Set E))) : E) =
        hT'.emb w := by
    intro g hg w hw
    have hgB : g ∈ Subgroup.closure ({a, b, s, y} : Set D) := by
      rw [hw]; exact hBB (by rw [← hT.emb_range]; exact ⟨w, rfl⟩)
    exact (hΦB g hgB).trans (key₁ w g hgB hw)
  have valA : ∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, x, ρ} : Set D)) (w : Tc),
      g = hT.emb w → ((φA ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', x', ρ'} : Set E))) : E) =
        hT'.emb w := by
    intro g hg w hw
    have hgA : g ∈ Subgroup.closure ({a, b, s, x} : Set D) := by
      rw [hw]; exact hAA (by rw [← hT.emb_range]; exact ⟨w, rfl⟩)
    exact (hΦA g hgA).trans (key₂ w g hgA hw)
  have valBρ : ∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, y, ρ} : Set D)) (w : Tc),
      g * ρ = hT.emb w → ((φB ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', y', ρ'} : Set E))) : E) =
        hT'.emb w * ρ' := by
    intro g hg w hw
    have hu : g * ρ ∈ Subgroup.closure ({a, b, s, y, ρ} : Set D) := by
      rw [hw]; exact hB5 (hBB (by rw [← hT.emb_range]; exact ⟨w, rfl⟩))
    have e : ((φB ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', y', ρ'} : Set E))) : E) =
        ((φB ⟨g * ρ, hu⟩ : ↥(Subgroup.closure ({a', b', s', y', ρ'} : Set E))) : E) *
          ((φB ⟨ρ, hρB5⟩ : ↥(Subgroup.closure ({a', b', s', y', ρ'} : Set E))) : E) :=
      iso_value_mul φB hg hu hρB5 (by rw [mul_assoc, hR.hρ, mul_one])
    rw [e, valB (g * ρ) hu w hw]
    congr 1
  have valAρ : ∀ (g : D) (hg : g ∈ Subgroup.closure ({a, b, s, x, ρ} : Set D)) (w : Tc),
      g * ρ = hT.emb w → ((φA ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', x', ρ'} : Set E))) : E) =
        hT'.emb w * ρ' := by
    intro g hg w hw
    have hu : g * ρ ∈ Subgroup.closure ({a, b, s, x, ρ} : Set D) := by
      rw [hw]; exact hA5 (hAA (by rw [← hT.emb_range]; exact ⟨w, rfl⟩))
    have e : ((φA ⟨g, hg⟩ : ↥(Subgroup.closure ({a', b', s', x', ρ'} : Set E))) : E) =
        ((φA ⟨g * ρ, hu⟩ : ↥(Subgroup.closure ({a', b', s', x', ρ'} : Set E))) : E) *
          ((φA ⟨ρ, hρA5⟩ : ↥(Subgroup.closure ({a', b', s', x', ρ'} : Set E))) : E) :=
      iso_value_mul φA hg hu hρA5 (by rw [mul_assoc, hR.hρ, mul_one])
    rw [e, valA (g * ρ) hu w hw]
    congr 1
  refine isAmalgamIso_of_agree φB φA ?_ ?_
  · intro g hg₁ hg₂
    have hgT : g ∈ Subgroup.closure ({a, b, s, ρ} : Set D) := by
      rw [← hinf]; exact ⟨hg₁, hg₂⟩
    rcases (mem_closure_abs_rho_iff hR g).1 hgT with hg | hg
    · obtain ⟨w, hw⟩ : g ∈ hT.emb.range := by rw [hT.emb_range]; exact hg
      rw [valB g hg₁ w hw.symm, valA g hg₂ w hw.symm]
    · obtain ⟨w, hw⟩ : g * ρ ∈ hT.emb.range := by rw [hT.emb_range]; exact hg
      rw [valBρ g hg₁ w hw.symm, valAρ g hg₂ w hw.symm]
  · intro y₀ hy₁ hy₂
    have hyT : y₀ ∈ Subgroup.closure ({a', b', s', ρ'} : Set E) := by
      rw [← hinf']; exact ⟨hy₁, hy₂⟩
    have hTmem : ∀ w : Tc, hT.emb w ∈ Subgroup.closure ({a, b, s} : Set D) := fun w => by
      rw [← hT.emb_range]; exact ⟨w, rfl⟩
    rcases (mem_closure_abs_rho_iff hR' y₀).1 hyT with hy | hy
    · obtain ⟨w, hw⟩ : y₀ ∈ hT'.emb.range := by rw [hT'.emb_range]; exact hy
      have hxB : hT.emb w ∈ Subgroup.closure ({a, b, s, y, ρ} : Set D) :=
        hB5 (hBB (hTmem w))
      have hxA : hT.emb w ∈ Subgroup.closure ({a, b, s, x, ρ} : Set D) :=
        hA5 (hAA (hTmem w))
      exact ⟨hT.emb w, hxB, hxA, (valB _ hxB w rfl).trans hw⟩
    · obtain ⟨w, hw⟩ : y₀ * ρ' ∈ hT'.emb.range := by rw [hT'.emb_range]; exact hy
      have hxB : hT.emb w * ρ ∈ Subgroup.closure ({a, b, s, y, ρ} : Set D) :=
        Subgroup.mul_mem _ (hB5 (hBB (hTmem w))) hρB5
      have hxA : hT.emb w * ρ ∈ Subgroup.closure ({a, b, s, x, ρ} : Set D) :=
        Subgroup.mul_mem _ (hA5 (hAA (hTmem w))) hρA5
      refine ⟨hT.emb w * ρ, hxB, hxA, ?_⟩
      rw [valBρ (hT.emb w * ρ) hxB w (by rw [mul_assoc, hR.hρ, mul_one]), hw, mul_assoc,
        hR'.hρ, mul_one]

end CFSG.Quasithin.F6.GoldAmL4
