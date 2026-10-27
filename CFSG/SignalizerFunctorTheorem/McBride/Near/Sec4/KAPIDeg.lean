module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Degree
public import CFSG.GroupTheory.PerfectResidualNodes

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.KAPI

variable {A B : Type*} [Group A] [Group B]

theorem isSolvable_comap_of_ker {f : A →* B} {N : Subgroup B} [Group.IsSolvable N]
    (hk : Group.IsSolvable f.ker) : Group.IsSolvable (N.comap f) := by
  have hle : f.ker ≤ N.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) (f.subgroupComap N)
    fun x hx => ?_
  have hx1 : f (x : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact ⟨⟨x, MonoidHom.mem_ker.mpr hx1⟩, rfl⟩

theorem map_solvableRadical_le [Finite A] {f : A →* B} (hf : Function.Surjective f) :
    (CFSG.solvableRadical A).map f ≤ CFSG.solvableRadical B := by
  have : Group.IsSolvable (CFSG.solvableRadical A) := isSolvable_solvableRadical
  exact le_solvableRadical (Subgroup.Normal.map inferInstance f hf)
    (Group.isSolvable_of_surjective (f.subgroupMap_surjective _))

theorem comap_solvableRadical_eq [Finite A] {f : A →* B} (hf : Function.Surjective f)
    (hk : Group.IsSolvable f.ker) :
    (CFSG.solvableRadical B).comap f = CFSG.solvableRadical A := by
  have : Finite B := Finite.of_surjective f hf
  have hs : Group.IsSolvable (CFSG.solvableRadical B) := isSolvable_solvableRadical
  refine le_antisymm ?_ (Subgroup.map_le_iff_le_comap.mp (map_solvableRadical_le hf))
  exact le_solvableRadical (Subgroup.Normal.comap inferInstance f) (isSolvable_comap_of_ker hk)

noncomputable def solQuotEquiv [Finite A] {f : A →* B} (hf : Function.Surjective f)
    (hk : Group.IsSolvable f.ker) :
    A ⧸ CFSG.solvableRadical A ≃* B ⧸ CFSG.solvableRadical B :=
  have hker : ((QuotientGroup.mk' (CFSG.solvableRadical B)).comp f).ker =
      CFSG.solvableRadical A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact comap_solvableRadical_eq hf hk
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (CFSG.solvableRadical B)).comp f)
      ((QuotientGroup.mk'_surjective _).comp hf))

theorem deg_eq_of_surjective [Finite A] {f : A →* B} (hf : Function.Surjective f)
    (hk : Group.IsSolvable f.ker) : deg A = deg B := by
  have : Finite B := Finite.of_surjective f hf
  exact permDeg_congr (solQuotEquiv hf hk)

theorem deg_congr [Finite A] (e : A ≃* B) : deg A = deg B :=
  deg_eq_of_surjective (f := e.toMonoidHom) e.surjective (by
    have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    rw [this]
    infer_instance)

theorem permDeg_eq_zero_of_subsingleton (H : Type*) [Group H] [Subsingleton H] :
    permDeg H = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨1, fun a b _ => Subsingleton.elim a b⟩

theorem deg_eq_zero_of_isSolvable [Finite A] (h : Group.IsSolvable A) : deg A = 0 := by
  have hs : CFSG.solvableRadical A = ⊤ :=
    top_le_iff.mp (le_solvableRadical inferInstance
      (Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup A).subtype)
        Subtype.val_injective))
  have : Subsingleton (A ⧸ CFSG.solvableRadical A) := by
    rw [hs]
    exact QuotientGroup.subsingleton_quotient_top
  exact permDeg_eq_zero_of_subsingleton _

theorem permDeg_le_of_injective_hom [Finite B] {f : A →* B} (hf : Function.Injective f) :
    permDeg A ≤ permDeg B := by
  obtain ⟨g, hg⟩ := exists_injective_permDeg (H := B)
  have : Finite A := Finite.of_injective f hf
  have := permDeg_le_of_injective (g.comp f) (hg.comp hf)
  simpa using this

theorem three_le_permDeg {J : Type*} [Group J] [Finite J] (hnc : ¬ IsMulCommutative J) :
    3 ≤ permDeg J := by
  by_contra hlt
  push Not at hlt
  obtain ⟨f, hf⟩ := exists_injective_permDeg (H := J)
  apply hnc
  refine ⟨⟨fun a b => hf ?_⟩⟩
  have hcomm : ∀ p q : Equiv.Perm (Fin (permDeg J)), p * q = q * p := by
    generalize permDeg J = k at hlt f hf
    interval_cases k
    · intro p q
      exact Subsingleton.elim _ _
    · intro p q
      exact Subsingleton.elim _ _
    · decide
  rw [map_mul, map_mul]
  exact hcomm _ _

theorem isSolvable_of_perfectResidual_le {W Z : Type*} [Group W] [Finite W] [Group Z]
    (θ : W →* Z) (hθ : Function.Surjective θ) (h : CFSG.perfectResidual W ≤ θ.ker) :
    Group.IsSolvable Z := by
  have hs : Group.IsSolvable (W ⧸ θ.ker) :=
    ((CFSG.perfect_residual_characterization (G := W)).2.2.2.2.1 θ.ker).mpr h
  exact Group.isSolvable_of_surjective
    (f := (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toMonoidHom)
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ).surjective

theorem oStar_eq_top_iff [Finite A] :
    oStar A = ⊤ ↔ CFSG.layer (A ⧸ CFSG.solvableRadical A) = ⊤ := by
  rw [oStar_eq_comap_layer]
  constructor
  · intro h
    have := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical A))) h
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  · intro h
    rw [h, Subgroup.comap_top]

theorem oStar_eq_top_of_surjective [Finite A] (hA : oStar A = ⊤) {f : A →* B}
    (hf : Function.Surjective f) : oStar B = ⊤ := by
  have : Finite B := Finite.of_surjective f hf
  rw [oStar_eq_top_iff] at hA ⊢
  have hle : CFSG.solvableRadical A ≤ (CFSG.solvableRadical B).comap f :=
    Subgroup.map_le_iff_le_comap.mp (map_solvableRadical_le hf)
  let g : A ⧸ CFSG.solvableRadical A →* B ⧸ CFSG.solvableRadical B :=
    QuotientGroup.map _ _ f hle
  have hg : Function.Surjective g :=
    QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective _).comp hf) hle
  exact CFSG.LocalCores.layer_eq_top_of_surjective hA g hg

@[expose] def DirFac (Q : Type*) [Group Q] : Prop :=
  ∀ N : Subgroup Q, N.Normal →
    N ⊓ Subgroup.centralizer (N : Set Q) = ⊥ ∧ N ⊔ Subgroup.centralizer (N : Set Q) = ⊤

theorem dirFac_of_oStar_eq_top [Finite A] (hA : oStar A = ⊤) :
    DirFac (A ⧸ CFSG.solvableRadical A) := by
  have hlayer : CFSG.layer (A ⧸ CFSG.solvableRadical A) = ⊤ := oStar_eq_top_iff.mp hA
  have hss : IsSemisimple (⊤ : Subgroup (A ⧸ CFSG.solvableRadical A)) := by
    have := isSemisimple_layer (solvableRadical_quotient (G := A))
    rwa [hlayer] at this
  intro N hN
  have hp := hss.isDirectPair_of_normal (le_top : N ≤ ⊤) Subgroup.normal_subgroupOf
  rw [top_inf_eq] at hp
  exact ⟨hp.inf_eq_bot, hp.sup_eq⟩

theorem DirFac.normal_of_conj_closed {Q : Type*} [Group Q] (hQ : DirFac Q) {N M : Subgroup Q}
    [N.Normal] (hMN : M ≤ N) (h : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) : M.Normal := by
  refine ⟨fun m hm g => ?_⟩
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Subgroup.mem_sup_of_normal_left.mp ((hQ N inferInstance).2 ▸ Subgroup.mem_top g)
  have hzm : m * z = z * m := Subgroup.mem_centralizer_iff.mp hz m (hMN hm)
  have e : g * m * g⁻¹ = y * m * y⁻¹ := by
    rw [← hyz]
    calc y * z * m * (y * z)⁻¹ = y * (z * m) * z⁻¹ * y⁻¹ := by group
      _ = y * (m * z) * z⁻¹ * y⁻¹ := by rw [hzm]
      _ = y * m * y⁻¹ := by group
  rw [e]
  exact h y hy m hm

theorem isSolvable_subgroupOf (R H : Subgroup A) [Group.IsSolvable R] :
    Group.IsSolvable (R.subgroupOf H) :=
  Group.isSolvable_of_isSolvable_injective (f := H.subtype.subgroupComap R)
    (MonoidHom.subgroupComap_injective _ _ H.subtype_injective)

theorem oStar_eq_top_of_normal [Finite A] (hA : oStar A = ⊤) (N : Subgroup A) [N.Normal] :
    oStar N = ⊤ := by
  set R := CFSG.solvableRadical A with hR
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical
  have hlayer : CFSG.layer (A ⧸ R) = ⊤ := oStar_eq_top_iff.mp hA
  have hD := dirFac_of_oStar_eq_top hA
  set π := QuotientGroup.mk' R with hπ
  set Nb : Subgroup (A ⧸ R) := N.map π with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  obtain ⟨h1, h2⟩ := hD Nb hNbn
  set C := Subgroup.centralizer (Nb : Set (A ⧸ R)) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  let e : Nb →* (A ⧸ R) ⧸ C := (QuotientGroup.mk' C).comp Nb.subtype
  have hinj : Function.Injective e := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxC : (x : A ⧸ R) ∈ C := by
      have := MonoidHom.mem_ker.mp hx
      simpa [e] using (QuotientGroup.eq_one_iff (x : A ⧸ R)).mp this
    have : (x : A ⧸ R) ∈ Nb ⊓ C := ⟨x.2, hxC⟩
    rw [h1, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hsurj : Function.Surjective e := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C q
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp (h2 ▸ Subgroup.mem_top y)
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [e, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have : a⁻¹ * y = b := by rw [← hab]; group
    rw [this]
    exact hb
  let eNb : Nb ≃* (A ⧸ R) ⧸ C := MulEquiv.ofBijective e ⟨hinj, hsurj⟩
  have hlayerNb : CFSG.layer Nb = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective
      (CFSG.LocalCores.layer_eq_top_of_surjective hlayer (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C)) (f := eNb.symm.toMonoidHom) eNb.symm.surjective
  let ρ : N →* Nb := π.subgroupMap N
  have hρ : Function.Surjective ρ := π.subgroupMap_surjective N
  have hk : Group.IsSolvable ρ.ker := by
    let g : ρ.ker →* R := ((N.subtype).comp ρ.ker.subtype).codRestrict R (fun x => by
      have hx := MonoidHom.mem_ker.mp x.2
      have := congrArg Subtype.val hx
      change π (x.1 : A) = 1 at this
      exact (QuotientGroup.eq_one_iff _).mp this)
    refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have hlayer2 : CFSG.layer (Nb ⧸ CFSG.solvableRadical Nb) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hlayerNb (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hlayer3 : CFSG.layer (N ⧸ CFSG.solvableRadical N) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hlayer2
      (solQuotEquiv hρ hk).symm.toMonoidHom (solQuotEquiv hρ hk).symm.surjective
  exact oStar_eq_top_iff.mpr hlayer3

theorem deg_le_of_injective [Finite B] (hA : oStar A = ⊤) {f : A →* B}
    (hf : Function.Injective f) : deg A ≤ deg B := by
  have : Finite A := Finite.of_injective f hf
  set g : A →* B ⧸ CFSG.solvableRadical B := (QuotientGroup.mk' _).comp f with hg
  have hker : Group.IsSolvable g.ker := by
    have hRs : Group.IsSolvable (CFSG.solvableRadical B) := isSolvable_solvableRadical
    let h : g.ker →* CFSG.solvableRadical B :=
      (f.comp g.ker.subtype).codRestrict _ (fun x => by
        have := MonoidHom.mem_ker.mp x.2
        exact (QuotientGroup.eq_one_iff _).mp this)
    refine Group.isSolvable_of_isSolvable_injective (f := h) ?_
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  have h1 : deg A = deg g.range :=
    deg_eq_of_surjective g.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  have h2 : oStar g.range = ⊤ := oStar_eq_top_of_surjective hA g.rangeRestrict_surjective
  have : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have h3 : deg g.range ≤ permDeg g.range := deg_le_permDeg h2
  have h4 : permDeg g.range ≤ permDeg (B ⧸ CFSG.solvableRadical B) :=
    permDeg_le_of_injective_hom g.range.subtype_injective
  exact h1.le.trans (h3.trans h4)

theorem deg_perfectResidual [Finite A] (hA : oStar A = ⊤) :
    deg (CFSG.perfectResidual A) = deg A := by
  have h := deg_add hA (CFSG.perfectResidual A)
  have hs : Group.IsSolvable (A ⧸ CFSG.perfectResidual A) :=
    (CFSG.perfect_residual_characterization (G := A)).2.2.2.1
  rw [deg_eq_zero_of_isSolvable hs, add_zero] at h
  exact h.symm

theorem deg_le_deg_inf_add [Finite A] (hA : oStar A = ⊤) (D₁ D₂ : Subgroup A) [D₁.Normal]
    [D₂.Normal] : deg D₁ ≤ deg ↥(D₁ ⊓ D₂) + deg (A ⧸ D₂) := by
  have hD₁ : oStar D₁ = ⊤ := oStar_eq_top_of_normal hA D₁
  have hNn : (D₂.subgroupOf D₁).Normal := Subgroup.normal_subgroupOf
  have h1 := deg_add hD₁ (D₂.subgroupOf D₁)
  have h2 : deg ↥(D₂.subgroupOf D₁) = deg ↥(D₁ ⊓ D₂) := by
    have e1 : deg ↥(D₂.subgroupOf D₁) = deg ↥((D₂.subgroupOf D₁).map D₁.subtype) :=
      deg_congr (Subgroup.equivMapOfInjective _ D₁.subtype D₁.subtype_injective)
    rw [e1]
    have : (D₂.subgroupOf D₁).map D₁.subtype = D₂ ⊓ D₁ := Subgroup.subgroupOf_map_subtype D₂ D₁
    rw [this, inf_comm]
  have hle : D₂.subgroupOf D₁ ≤ D₂.comap D₁.subtype := fun x hx => hx
  let ι : D₁ ⧸ D₂.subgroupOf D₁ →* A ⧸ D₂ := QuotientGroup.map _ D₂ D₁.subtype hle
  have hι : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff]
    show (QuotientGroup.map _ D₂ D₁.subtype hle).ker = ⊥
    rw [QuotientGroup.ker_map]
    exact QuotientGroup.map_mk'_self _
  have hrange : ι.range.Normal := by
    have : ι.range = D₁.map (QuotientGroup.mk' D₂) := by
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨d, d.2, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨QuotientGroup.mk ⟨d, hd⟩, rfl⟩
    rw [this]
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hAD : oStar (A ⧸ D₂) = ⊤ :=
    oStar_eq_top_of_surjective hA (QuotientGroup.mk'_surjective D₂)
  have h3 := deg_add hAD ι.range
  have h4 : deg (D₁ ⧸ D₂.subgroupOf D₁) = deg ι.range :=
    deg_congr (MonoidHom.ofInjective hι)
  rw [h1, h2, h4]
  omega

theorem deg_two_normal [Finite A] (hA : oStar A = ⊤) (D₁ D₂ : Subgroup A) [D₁.Normal]
    [D₂.Normal] {a₁ a₂ : ℕ} (h₁ : deg A ≤ deg D₁ + a₁) (h₂ : deg A ≤ deg D₂ + a₂) :
    deg A ≤ deg ↥(D₁ ⊓ D₂) + (a₁ + a₂) ∧
      (deg A = deg ↥(D₁ ⊓ D₂) + (a₁ + a₂) → deg A = deg D₁ + a₁ ∧ deg A = deg D₂ + a₂) := by
  have e1 := deg_add hA D₁
  have e2 := deg_add hA D₂
  have s1 := deg_le_deg_inf_add hA D₁ D₂
  have s2 := deg_le_deg_inf_add hA D₂ D₁
  rw [inf_comm] at s2
  refine ⟨by omega, fun h => ⟨by omega, by omega⟩⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.KAPI
