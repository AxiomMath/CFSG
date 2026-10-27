module

public import CFSG.SignalizerFunctorTheorem.Inheritance.HypB
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type u} [Group Γ]

section Components

variable [Finite Γ] {E Y : Subgroup Γ}

omit [Finite Γ] in
theorem eq_one_of_forall_commute {J : Subgroup Γ} (hJ : IsSimpleGroup J)
    (hnc : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) {x : Γ} (hx : x ∈ J)
    (h : ∀ y ∈ J, y * x = x * y) : x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with hc | hc
  · have hx' : (⟨x, hx⟩ : J) ∈ Subgroup.center J :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h g g.2)
    rw [hc, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have : (⟨a, ha⟩ : J) ∈ Subgroup.center J := hc ▸ Subgroup.mem_top _
    exact hab (congrArg Subtype.val (Subgroup.mem_center_iff.mp this ⟨b, hb⟩).symm)

omit [Finite Γ] in
theorem map_conj_mem_simpleComponents {e : Γ} (he : e ∈ Subgroup.normalizer (Y : Set Γ))
    {J : Subgroup Γ} (hJ : J ∈ simpleComponents Y) :
    J.map (MulAut.conj e).toMonoidHom ∈ simpleComponents Y := by
  obtain ⟨hJY, hJn, hJs, x₀, hx₀, y₀, hy₀, hxy₀⟩ := hJ
  have hconj : ∀ g ∈ Y, e * g * e⁻¹ ∈ Y := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp he g).mp hg
  have hconj' : ∀ g ∈ Y, e⁻¹ * g * e ∈ Y := fun g hg => by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem he) g).mp hg
  have hle : J.map (MulAut.conj e).toMonoidHom ≤ Y := by
    rintro _ ⟨j, hj, rfl⟩
    exact hconj j (hJY hj)
  refine ⟨hle, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ k ⟨j, hj, rfl⟩ hk
    refine ⟨(e⁻¹ * k * e) * j * (e⁻¹ * k * e)⁻¹, ?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff hJY).mp hJn j _ hj (hconj' k hk)
    · change e * ((e⁻¹ * k * e) * j * (e⁻¹ * k * e)⁻¹) * e⁻¹ = k * (e * j * e⁻¹) * k⁻¹
      group
  · have := hJs
    exact (J.equivMapOfInjective (MulAut.conj e).toMonoidHom
      (MulAut.conj e).injective).symm.isSimpleGroup
  · refine ⟨e * x₀ * e⁻¹, ⟨x₀, hx₀, rfl⟩, e * y₀ * e⁻¹, ⟨y₀, hy₀, rfl⟩, fun h => hxy₀ ?_⟩
    have h' : e * (x₀ * y₀) * e⁻¹ = e * (y₀ * x₀) * e⁻¹ := by
      calc e * (x₀ * y₀) * e⁻¹ = e * x₀ * e⁻¹ * (e * y₀ * e⁻¹) := by group
        _ = e * y₀ * e⁻¹ * (e * x₀ * e⁻¹) := h
        _ = e * (y₀ * x₀) * e⁻¹ := by group
    simpa using h'

theorem isDirectProduct_simpleComponents (hA : IsASimple E Y) :
    IsDirectProduct (simpleComponents Y) Y where
  commute J hJ L hL hne x hx y hy :=
    (Subgroup.mem_centralizer_iff.mp ((hA.components_commute hJ hL hne).1 hx) y hy).symm
  indep J hJ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxJ, hxP⟩ := Subgroup.mem_inf.mp hx
    have hPc : sSup (simpleComponents Y \ {J}) ≤ Subgroup.centralizer (J : Set Γ) :=
      sSup_le fun L hL => (hA.components_commute hL.1 hJ hL.2).1
    have hxc := Subgroup.mem_centralizer_iff.mp (hPc hxP)
    exact Subgroup.mem_bot.mpr (eq_one_of_forall_commute hJ.2.2.1 hJ.2.2.2 hxJ fun y hy =>
      hxc y hy)
  sSup_eq := by rw [sSup_eq_iSup]; exact hA.iSup_components

theorem hypA_of_mem_simpleComponents {p : ℕ} {T : Subgroup Γ}
    (hY : signalizerMcBrideHypothesisB p Y) (hT : T ∈ simpleComponents Y) :
    signalizerMcBrideHypothesisA p ↥T := by
  obtain ⟨hTY, -, hTs, a, ha, b, hb, hab⟩ := hT
  have := hTs
  refine signalizerMcBrideHypothesisA_of_isSectionOf hY ?_
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  exact (IsSectionOf.refl ↥T).of_injective (Subgroup.inclusion hTY)
    (Subgroup.inclusion_injective hTY)

end Components

theorem exists_aut_of_cyclic_pSubgroups {p : ℕ} (hp : p.Prime) {T B : Subgroup Γ}
    (hBp : ∀ b ∈ B, b ^ p = 1) (hBT : B ≤ Subgroup.normalizer (T : Set Γ))
    (hcyc : ∀ P : Subgroup (MulAut ↥T), IsPGroup p P → IsCyclic P) :
    ∃ f : MulAut ↥T, (f = 1 ∨ orderOf f = p) ∧
      ∀ t : ↥T, (∀ b ∈ B, (b : Γ) * t * (b : Γ)⁻¹ = t) ↔ f t = t := by
  let ρ : ↥B →* MulAut ↥T := T.normalizerMonoidHom.comp (Subgroup.inclusion hBT)
  have hρ : ∀ (b : B) (t : T), ((ρ b t : T) : Γ) = b * t * (b : Γ)⁻¹ := fun b t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe T (Subgroup.inclusion hBT b) t
  have hpow : ∀ b : B, b ^ p = 1 := fun b => Subtype.ext (hBp b b.2)
  have hRp : IsPGroup p ρ.range :=
    IsPGroup.of_surjective (fun b : B => ⟨1, by simpa using hpow b⟩) ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  have := hcyc ρ.range hRp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥ρ.range)
  have hgp : (g : MulAut ↥T) ^ p = 1 := by
    obtain ⟨b, hb⟩ := g.2
    rw [← hb, ← map_pow, hpow b, map_one]
  refine ⟨(g : MulAut ↥T), ?_, fun t => ⟨fun h => ?_, fun h b hb => ?_⟩⟩
  · rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hgp) with h | h
    · exact Or.inl (orderOf_eq_one_iff.mp h)
    · exact Or.inr h
  · obtain ⟨b, hb⟩ := g.2
    rw [← hb]
    exact Subtype.ext (by rw [hρ]; exact h b b.2)
  · have hmem : (g : MulAut ↥T) ∈ MulAction.stabilizer (MulAut ↥T) t :=
      MulAction.mem_stabilizer_iff.mpr h
    have hle : Subgroup.zpowers (g : MulAut ↥T) ≤ MulAction.stabilizer (MulAut ↥T) t :=
      Subgroup.zpowers_le.mpr hmem
    have hρb : ρ ⟨b, hb⟩ ∈ Subgroup.zpowers (g : MulAut ↥T) := by
      obtain ⟨k, hk⟩ := hg ⟨ρ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have := MulAction.mem_stabilizer_iff.mp (hle hρb)
    have h2 := congrArg (fun z : T => (z : Γ)) this
    simpa [hρ] using h2

section Embedding

variable [Finite Γ] {E Y : Subgroup Γ}

omit [Finite Γ] in
theorem map_conj_map_conj (g h : Γ) (X : Subgroup Γ) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite Γ] in
theorem map_conj_one (X : Subgroup Γ) : X.map (MulAut.conj (1 : Γ)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map]

omit [Finite Γ] in
theorem mem_normalizer_of_map_conj_eq {T J J' : Subgroup Γ} {a a' e : Γ}
    (hJ : J = T.map (MulAut.conj a).toMonoidHom) (hJ' : J' = T.map (MulAut.conj a').toMonoidHom)
    (he : J.map (MulAut.conj e).toMonoidHom = J') :
    a'⁻¹ * e * a ∈ Subgroup.normalizer (T : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, mul_assoc]
  change T.map (MulAut.conj (a'⁻¹ * (e * a))).toMonoidHom = T
  rw [← map_conj_map_conj, ← map_conj_map_conj, ← hJ, he, hJ', map_conj_map_conj, inv_mul_cancel,
    map_conj_one]

theorem exists_injective_fixed_hom (hA : IsASimple E Y) {T : Subgroup Γ}
    (hT : T ∈ simpleComponents Y) :
    ∃ φ : ↥(T ⊓ Subgroup.centralizer ((E ⊓ Subgroup.normalizer (T : Set Γ) : Subgroup Γ) :
        Set Γ)) →* ↥(Y ⊓ Subgroup.centralizer (E : Set Γ)), Function.Injective φ := by
  classical
  have hK : IsDirectProduct (simpleComponents Y) Y := isDirectProduct_simpleComponents hA
  have hEY : E ≤ Subgroup.normalizer (Y : Set Γ) := hA.1
  have hperm : ∀ e ∈ E, ∀ J ∈ simpleComponents Y,
      J.map (MulAut.conj e).toMonoidHom ∈ simpleComponents Y := fun e he J hJ =>
    map_conj_mem_simpleComponents (hEY he) hJ
  have hex : ∀ J : simpleComponents Y,
      ∃ a ∈ E, (J : Subgroup Γ) = T.map (MulAut.conj a).toMonoidHom := fun J =>
    hA.components_transitive hT J.2
  choose a haE haJ using hex
  set E₁ : Subgroup Γ := E ⊓ Subgroup.normalizer (T : Set Γ) with hE₁
  set Tf : Subgroup Γ := T ⊓ Subgroup.centralizer (E₁ : Set Γ) with hTf
  let c : (J : simpleComponents Y) → (↥Tf →* ↥(J : Subgroup Γ)) := fun J =>
    ((MulAut.conj (a J)).toMonoidHom.comp Tf.subtype).codRestrict (J : Subgroup Γ) (fun t => by
      rw [haJ J]
      exact ⟨t, (Subgroup.mem_inf.mp t.2).1, rfl⟩)
  let z : ↥Tf →* ((J : simpleComponents Y) → (J : Subgroup Γ)) := MonoidHom.pi c
  let φ₁ : ↥Tf →* ↥Y := hK.equiv.toMonoidHom.comp z
  have hcoord : ∀ (t : ↥Tf) (J : Subgroup Γ) (hJ : J ∈ simpleComponents Y),
      ((hK.coord hJ (φ₁ t) : ↥J) : Γ) = a ⟨J, hJ⟩ * (t : Γ) * (a ⟨J, hJ⟩)⁻¹ := fun t J hJ =>
    congrArg Subtype.val (hK.coord_equiv hJ (z t))
  have hfix : ∀ (t : ↥Tf) (e : Γ), e ∈ E → e * ((φ₁ t : ↥Y) : Γ) * e⁻¹ = (φ₁ t : Γ) := by
    intro t e he
    have he' := hperm e he
    have hy' : e * ((φ₁ t : ↥Y) : Γ) * e⁻¹ ∈ Y := hK.conj_mem he' (φ₁ t).2
    have heq : (⟨e * ((φ₁ t : ↥Y) : Γ) * e⁻¹, hy'⟩ : ↥Y) = φ₁ t := by
      apply hK.ext_coord
      intro J' hJ'
      have hJ : J'.map (MulAut.conj e⁻¹).toMonoidHom ∈ simpleComponents Y :=
        hperm e⁻¹ (inv_mem he) J' hJ'
      have hJJ' : (J'.map (MulAut.conj e⁻¹).toMonoidHom).map (MulAut.conj e).toMonoidHom = J' := by
        rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
      have h1 := hK.coord_conj he' hJ (φ₁ t).2
      have h2 := hK.coord_val_congr (he' _ hJ) hJ' hJJ' ⟨e * ((φ₁ t : ↥Y) : Γ) * e⁻¹, hy'⟩
      apply Subtype.ext
      rw [← h2, h1, hcoord t _ hJ, hcoord t J' hJ']
      set J := J'.map (MulAut.conj e⁻¹).toMonoidHom with hJdef
      have hb : (a ⟨J', hJ'⟩)⁻¹ * e * a ⟨J, hJ⟩ ∈ E₁ :=
        Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem (haE _)) he) (haE _),
          mem_normalizer_of_map_conj_eq (haJ ⟨J, hJ⟩) (haJ ⟨J', hJ'⟩) hJJ'⟩
      have hbt := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp t.2).2 _ hb
      set a₁ := a ⟨J', hJ'⟩
      set a₂ := a ⟨J, hJ⟩
      set t' : Γ := (t : Γ)
      calc e * (a₂ * t' * a₂⁻¹) * e⁻¹ = (e * a₂) * t' * (e * a₂)⁻¹ := by group
        _ = a₁ * (a₁⁻¹ * e * a₂ * t') * (e * a₂)⁻¹ := by group
        _ = a₁ * (t' * (a₁⁻¹ * e * a₂)) * (e * a₂)⁻¹ := by rw [hbt]
        _ = a₁ * t' * a₁⁻¹ := by group
    exact congrArg Subtype.val heq
  have hmem : ∀ t : ↥Tf, ((φ₁ t : ↥Y) : Γ) ∈ Y ⊓ Subgroup.centralizer (E : Set Γ) := fun t =>
    Subgroup.mem_inf.mpr ⟨(φ₁ t).2, Subgroup.mem_centralizer_iff.mpr fun e he =>
      mul_inv_eq_iff_eq_mul.mp (hfix t e he)⟩
  refine ⟨(Y.subtype.comp φ₁).codRestrict _ hmem, ?_⟩
  rw [injective_iff_map_eq_one]
  intro t ht
  have h1' : ((φ₁ t : ↥Y) : Γ) = 1 := congrArg Subtype.val ht
  have h1 : φ₁ t = 1 := Subtype.ext h1'
  have h2 := hcoord t T hT
  rw [h1] at h2
  have hT' : (T : Subgroup Γ) = T.map (MulAut.conj (a ⟨T, hT⟩)).toMonoidHom := haJ ⟨T, hT⟩
  have haT : a ⟨T, hT⟩ ∈ E₁ :=
    Subgroup.mem_inf.mpr ⟨haE _, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hT'.symm⟩
  have hct := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp t.2).2 _ haT
  have h3 : (1 : Γ) = a ⟨T, hT⟩ * (t : Γ) * (a ⟨T, hT⟩)⁻¹ := by simpa using h2
  have h4 : a ⟨T, hT⟩ * (t : Γ) * (a ⟨T, hT⟩)⁻¹ = (t : Γ) := by rw [hct]; group
  exact Subtype.ext (by rw [← h4]; exact h3.symm)

theorem exists_fixed_embedding {p : ℕ} (hp : p.Prime) (hE : IsElemAbelian p E)
    (hA : IsASimple E Y) (hY : signalizerMcBrideHypothesisB p Y) {T : Subgroup Γ}
    (hT : T ∈ simpleComponents Y) :
    ∃ f : MulAut ↥T, (f = 1 ∨ orderOf f = p) ∧
      ∃ φ : ↥(signalizerFixedSubgroup f) →* ↥(Y ⊓ Subgroup.centralizer (E : Set Γ)),
        Function.Injective φ := by
  obtain ⟨f, hf, hfix⟩ := exists_aut_of_cyclic_pSubgroups hp (T := T)
    (B := E ⊓ Subgroup.normalizer (T : Set Γ))
    (fun b hb => hE.2 b (Subgroup.mem_inf.mp hb).1) inf_le_right
    (hypA_of_mem_simpleComponents hY hT).2.2.2.2.1
  obtain ⟨φ, hφ⟩ := exists_injective_fixed_hom hA hT
  have hmem : ∀ t : ↥(signalizerFixedSubgroup f), (((t : ↥T)) : Γ) ∈
      T ⊓ Subgroup.centralizer ((E ⊓ Subgroup.normalizer (T : Set Γ) : Subgroup Γ) : Set Γ) :=
    fun t => Subgroup.mem_inf.mpr ⟨(t : ↥T).2, Subgroup.mem_centralizer_iff.mpr fun b hb =>
      mul_inv_eq_iff_eq_mul.mp (((hfix t).mpr t.2) b hb)⟩
  let ι : ↥(signalizerFixedSubgroup f) →* ↥(T ⊓ Subgroup.centralizer
      ((E ⊓ Subgroup.normalizer (T : Set Γ) : Subgroup Γ) : Set Γ)) :=
    (T.subtype.comp (signalizerFixedSubgroup f).subtype).codRestrict _ hmem
  refine ⟨f, hf, φ.comp ι, hφ.comp fun x y h => ?_⟩
  have h' : ((x : ↥T) : Γ) = ((y : ↥T) : Γ) :=
    congrArg (fun z : ↥(T ⊓ Subgroup.centralizer
      ((E ⊓ Subgroup.normalizer (T : Set Γ) : Subgroup Γ) : Set Γ)) => (z : Γ)) h
  exact Subtype.ext (Subtype.ext h')

end Embedding

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
