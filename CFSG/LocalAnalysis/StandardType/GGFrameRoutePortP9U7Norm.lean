module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U7

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.LineU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {L : Type} [Group L] {F : Type} [Field F] {m : ℕ}

private lemma p9u7a_glAut_inv_apply (τ : F ≃+* F) (X : GL (Fin m) F) :
    glAut τ (glAut τ⁻¹ X) = X := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private lemma p9u7a_mul_glAut_conj (g : GL (Fin m) F) (τ : F ≃+* F)
    (E X : GL (Fin m) F) :
    (g * glAut τ E * g⁻¹) * (g * glAut τ X * g⁻¹) * (g * glAut τ E * g⁻¹)⁻¹ =
      g * glAut τ (E * X * E⁻¹) * g⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

private lemma p9u7a_inv_mul_glAut_conj (g : GL (Fin m) F) (τ : F ≃+* F)
    (E : GL (Fin m) F) :
    (g * glAut τ E * g⁻¹)⁻¹ = g * glAut τ E⁻¹ * g⁻¹ := by
  calc (g * glAut τ E * g⁻¹)⁻¹ = g * (glAut τ E)⁻¹ * g⁻¹ := by group
    _ = g * glAut τ E⁻¹ * g⁻¹ := by rw [← map_inv]

private lemma p9u7a_exists_glAut_preimage (h : UnitaryFieldData 2 1 F)
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m)) (τ : F ≃+* F)
    (v : ↥(unitarySU 2 1 F m)) :
    ∃ u : ↥(unitarySU 2 1 F m),
      (u : GL (Fin m) F) = glAut τ⁻¹ (g⁻¹ * (v : GL (Fin m) F) * g) ∧
      glAut τ (u : GL (Fin m) F) = g⁻¹ * (v : GL (Fin m) F) * g := by
  have hg1 : g⁻¹ ∈ primeFormUnitary h (idGram F m) := Subgroup.inv_mem _ hg
  have hx : g⁻¹ * (v : GL (Fin m) F) * g ∈ unitarySU 2 1 F m := by
    have := InndiagSU.semilin_mem h hg1 (1 : F ≃+* F) v
    simpa only [map_one, MulAut.one_apply, inv_inv] using this
  have hmem : glAut τ⁻¹ (g⁻¹ * (v : GL (Fin m) F) * g) ∈ unitarySU 2 1 F m := by
    have := InndiagSU.semilin_mem h (Subgroup.one_mem _) τ⁻¹ ⟨_, hx⟩
    simpa using this
  refine ⟨⟨glAut τ⁻¹ (g⁻¹ * (v : GL (Fin m) F) * g), hmem⟩, rfl, ?_⟩
  exact p9u7a_glAut_inv_apply τ (g⁻¹ * (v : GL (Fin m) F) * g)

private lemma p9u7a_conj_mem_of_mem (h : UnitaryFieldData 2 1 F)
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m))
    {τ : F ≃+* F} {D : GL (Fin m) F}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)))
    {v : GL (Fin m) F} (hv : v ∈ unitarySU 2 1 F m) :
    (g * glAut τ D * g⁻¹) * v * (g * glAut τ D * g⁻¹)⁻¹ ∈ unitarySU 2 1 F m := by
  let M : GL (Fin m) F := g * glAut τ D * g⁻¹
  change M * v * M⁻¹ ∈ unitarySU 2 1 F m
  obtain ⟨u, -, hgu⟩ := p9u7a_exists_glAut_preimage h hg τ ⟨v, hv⟩
  have hv' : (v : GL (Fin m) F) = g * glAut τ (u : GL (Fin m) F) * g⁻¹ := by
    rw [hgu]; group
  have hDu : D * (u : GL (Fin m) F) * D⁻¹ ∈ unitarySU 2 1 F m :=
    (Subgroup.mem_normalizer_iff.mp hD (u : GL (Fin m) F)).mp u.2
  have hSU := InndiagSU.semilin_mem h hg τ ⟨_, hDu⟩
  have hMv : M * v * M⁻¹ =
      g * glAut τ (D * (u : GL (Fin m) F) * D⁻¹) * g⁻¹ := by
    rw [hv']
    change (g * glAut τ D * g⁻¹) * (g * glAut τ (u : GL (Fin m) F) * g⁻¹) *
      (g * glAut τ D * g⁻¹)⁻¹ = _
    exact p9u7a_mul_glAut_conj g τ D (u : GL (Fin m) F)
  rw [hMv]
  exact hSU

private lemma p9u7a_glAut_conj_mem_normalizer (h : UnitaryFieldData 2 1 F)
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m))
    {τ : F ≃+* F} {D : GL (Fin m) F}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F))) :
    g * glAut τ D * g⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)) := by
  let M : GL (Fin m) F := g * glAut τ D * g⁻¹
  change M ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F))
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact p9u7a_conj_mem_of_mem h hg hD
  · intro hv
    have hDinv : D⁻¹ ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)) :=
      Subgroup.inv_mem _ hD
    have hw := p9u7a_conj_mem_of_mem (τ := τ) h hg hDinv hv
    have hM' : g * glAut τ D⁻¹ * g⁻¹ = M⁻¹ :=
      (p9u7a_inv_mul_glAut_conj g τ D).symm
    rw [hM', inv_inv] at hw
    have hMv : M⁻¹ * (M * v * M⁻¹) * M = v := by group
    rwa [hMv] at hw

private lemma p9u7a_transport (h : UnitaryFieldData 2 1 F)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    {β : MulAut L} {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m))
    {τ : F ≃+* F} (hβg : InndiagSU.IsSemilin φ β g τ)
    {a : MulAut L} {t : Fin m → F} {D : GL (Fin m) F}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)))
    (hDt : (D : Matrix (Fin m) (Fin m) F) = diagonal t)
    (hact : ∀ s : ↥(unitarySU 2 1 F m), a (φ s) = φ (conjN D hD s)) :
    ∃ (M : GL (Fin m) F)
      (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F))),
      (M : Matrix (Fin m) (Fin m) F) =
        (g : Matrix (Fin m) (Fin m) F) * (D : Matrix (Fin m) (Fin m) F).map τ *
          ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) ∧
      ∀ v : ↥(unitarySU 2 1 F m), (β * a * β⁻¹) (φ v) = φ (conjN M hM v) := by
  let M : GL (Fin m) F := g * glAut τ D * g⁻¹
  have hMnorm : M ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)) :=
    p9u7a_glAut_conj_mem_normalizer h hg hD
  refine ⟨M, hMnorm, ?_, ?_⟩
  · change ((g * glAut τ D * g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = _
    rw [Units.val_mul, Units.val_mul, coe_glAut]
  · intro v
    obtain ⟨u, -, hgu⟩ := p9u7a_exists_glAut_preimage h hg τ v
    have hv' : (v : GL (Fin m) F) = g * glAut τ (u : GL (Fin m) F) * g⁻¹ := by
      rw [hgu]; group
    have hβinv : β⁻¹ (φ v) = φ u := by
      rw [← hβg u v hv', MulAut.inv_apply_self]
    have hMv : ((conjN M hMnorm v : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
        g * glAut τ ((conjN D hD u : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) * g⁻¹ := by
      rw [coe_conjN, coe_conjN]
      change (g * glAut τ D * g⁻¹) * (v : GL (Fin m) F) * (g * glAut τ D * g⁻¹)⁻¹ = _
      rw [hv']
      exact p9u7a_mul_glAut_conj g τ D (u : GL (Fin m) F)
    calc (β * a * β⁻¹) (φ v)
        = β (a (β⁻¹ (φ v))) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = β (a (φ u)) := by rw [hβinv]
      _ = β (φ (conjN D hD u)) := by rw [hact u]
      _ = φ (conjN M hMnorm v) := hβg (conjN D hD u) (conjN M hMnorm v) hMv

private lemma p9u7a_diagonal_of_normalizes (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {b : MulAut L} {tb : Fin m → F} {Db : GL (Fin m) F}
    (hDb : Db ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)))
    (hDbt : (Db : Matrix (Fin m) (Fin m) F) = diagonal tb)
    (hbact : ∀ s : ↥(unitarySU 2 1 F m), b (φ s) = φ (conjN Db hDb s))
    {M : GL (Fin m) F}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)))
    (hactM : ∀ v : ↥(unitarySU 2 1 F m), b (φ v) = φ (conjN M hM v)) :
    ∃ c : F, (M : Matrix (Fin m) (Fin m) F) = diagonal (fun i => tb i * c) := by
  let N : GL (Fin m) F := Db⁻¹ * M
  have hN : ∀ s ∈ unitarySU 2 1 F m, ∃ c : F,
      ((N * s * N⁻¹ * s⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        diagonal (fun _ => c) := by
    intro s hs
    let sSU : ↥(unitarySU 2 1 F m) := ⟨s, hs⟩
    let g1 : ↥(unitarySU 2 1 F m) := conjN M hM sSU
    let g2 : ↥(unitarySU 2 1 F m) := conjN Db hDb sSU
    have hg1g2 : φ (g1 * g2⁻¹) = 1 := by
      rw [map_mul, map_inv, (hactM sSU).symm, (hbact sSU).symm, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hφker (g1 * g2⁻¹) hg1g2
    refine ⟨c, ?_⟩
    have hunit : N * s * N⁻¹ * s⁻¹ =
        Db⁻¹ * ((g1 * g2⁻¹ : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) * Db := by
      change (Db⁻¹ * M) * (sSU : GL (Fin m) F) * (Db⁻¹ * M)⁻¹ * (sSU : GL (Fin m) F)⁻¹ =
        Db⁻¹ * (((conjN M hM sSU) * (conjN Db hDb sSU)⁻¹ :
          ↥(unitarySU 2 1 F m)) : GL (Fin m) F) * Db
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN, coe_conjN]
      group
    rw [hunit]
    rw [Units.val_mul, Units.val_mul, hc]
    have hcomm : (diagonal (fun _ => c) : Matrix (Fin m) (Fin m) F) *
        (Db : Matrix (Fin m) (Fin m) F) =
        (Db : Matrix (Fin m) (Fin m) F) * diagonal (fun _ => c) := by
      simpa only [Matrix.scalar_apply] using
        Matrix.scalar_comm c (fun r => mul_comm c r) (Db : Matrix (Fin m) (Fin m) F)
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul]
  obtain ⟨c, hcN⟩ := P9_U7a_eq_scalar_of_comm h hm N hN
  refine ⟨c, ?_⟩
  have hM_eq : M = Db * N := by
    change M = Db * (Db⁻¹ * M)
    group
  rw [hM_eq, Units.val_mul, hDbt, hcN, Matrix.diagonal_mul_diagonal]

private lemma p9u7a_exists_diag_rep_mul_scalar {φ : ↥(unitarySU 2 1 F m) →* L}
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    {a : ↥A} {t : Fin m → Fˣ} (hιa : ι a = QuotientGroup.mk t) :
    ∃ (d : Fˣ) (Da : GL (Fin m) F)
      (hDa : Da ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F))),
      (Da : Matrix (Fin m) (Fin m) F) = diagonal (fun i => (t i : F) * (d : F)) ∧
      ∀ s : ↥(unitarySU 2 1 F m), (a : MulAut L) (φ s) = φ (conjN Da hDa s) := by
  obtain ⟨ta, hta⟩ := hdiag (a : MulAut L) a.2
  obtain ⟨Da, hDa, hDat, hacta⟩ := hta
  let ua : Fin m → Fˣ := fun i => Units.mk0 (ta i) (diag_ne_zero_of_eq hDat i)
  have hfun : (fun i => (ua i : F)) = ta := by
    funext i
    simp [ua, Units.val_mk0]
  have hUa : ActsDiagU φ (a : MulAut L) (fun i => (ua i : F)) := by
    rw [hfun]
    exact ⟨Da, hDa, hDat, hacta⟩
  have ha_ua : ι a = QuotientGroup.mk ua := hι a ua hUa
  have hmk_eq : (QuotientGroup.mk ua : UTorus.Proj F m) =
      (QuotientGroup.mk t : UTorus.Proj F m) := by rw [← ha_ua, hιa]
  obtain ⟨c, hc⟩ := (QuotientGroup.eq).mp hmk_eq
  have hc' : ∀ i, (ua i)⁻¹ * t i = c := by
    intro i
    simpa using (congrFun hc i).symm
  let d : Fˣ := c⁻¹
  have hta_eq : ta = fun i => (t i : F) * (d : F) := by
    funext i
    have hci : (ua i)⁻¹ * t i = c := hc' i
    have hu_eq : ua i = t i * c⁻¹ := by
      calc ua i = ua i * ((ua i)⁻¹ * t i) * c⁻¹ := by rw [hci]; group
        _ = t i * c⁻¹ := by group
    have hval := congrArg Units.val hu_eq
    simpa only [ua, d, Units.val_mul, Units.val_mk0] using hval
  exact ⟨d, Da, hDa, by rw [hDat, hta_eq], hacta⟩

private lemma p9u7a_diag_of_detOne_tau (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    (hinner : UTorus.inner F m ≤ ι.range)
    {β : MulAut L} (hβ : β ∈ Subgroup.normalizer (A : Set (MulAut L)))
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m)) {τ : F ≃+* F}
    (hβg : InndiagSU.IsSemilin φ β g τ)
    {u : Fin m → Fˣ} (hu : u ∈ UTorus.detOne F m) :
    ((g : Matrix (Fin m) (Fin m) F) * diagonal (fun i => τ ((u i : F))) *
      ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).IsDiag := by
  have hu_inner : QuotientGroup.mk u ∈ UTorus.inner F m := by
    rw [UTorus.inner]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (UTorus.scalars F m)) hu
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hinner hu_inner)
  obtain ⟨d, Da, hDa, hDat, hacta⟩ := p9u7a_exists_diag_rep_mul_scalar hdiag ι hι ha
  let b : MulAut L := β * (a : MulAut L) * β⁻¹
  have hbA : b ∈ A := (Subgroup.mem_normalizer_iff.mp hβ (a : MulAut L)).mp a.2
  obtain ⟨tb, htb⟩ := hdiag b hbA
  obtain ⟨Db, hDb, hDbt, hbact⟩ := htb
  obtain ⟨M, hM, hMmat, hactM⟩ := p9u7a_transport h hg hβg hDa hDat hacta
  obtain ⟨c2, hMdiag⟩ := p9u7a_diagonal_of_normalizes h hm hφker hDb hDbt hbact hM hactM
  have hM_eq : (M : Matrix (Fin m) (Fin m) F) =
      ((g : Matrix (Fin m) (Fin m) F) * diagonal (fun i => τ ((u i : F))) *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) *
      diagonal (fun _ => τ (d : F)) := by
    rw [hMmat, hDat]
    simp only [Matrix.diagonal_map, map_zero, map_mul]
    rw [← Matrix.diagonal_mul_diagonal]
    have hcomm : diagonal (fun _ => τ (d : F)) *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
          diagonal (fun _ => τ (d : F)) := by
      simpa only [Matrix.scalar_apply] using
        Matrix.scalar_comm (τ (d : F)) (fun r => mul_comm (τ (d : F)) r)
          ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
    rw [← Matrix.mul_assoc, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]
  intro i j hij
  have hMij : (M : Matrix (Fin m) (Fin m) F) i j = 0 := by
    rw [hMdiag]
    simp [Matrix.diagonal_apply, hij]
  rw [hM_eq, Matrix.mul_diagonal] at hMij
  have hτd : τ (d : F) ≠ 0 := by
    simpa using (τ.injective.ne (by simp [d]))
  exact (mul_eq_zero.mp hMij).resolve_right hτd

private lemma p9u7a_all_detOne (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    (hinner : UTorus.inner F m ≤ ι.range)
    {β : MulAut L} (hβ : β ∈ Subgroup.normalizer (A : Set (MulAut L)))
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m)) {τ : F ≃+* F}
    (hβg : InndiagSU.IsSemilin φ β g τ) :
    ∀ t ∈ UTorus.detOne F m,
      ((g : Matrix (Fin m) (Fin m) F) * diagonal (fun i => (t i : F)) *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).IsDiag := by
  intro t ht
  let u : Fin m → Fˣ := fun i => Units.map (τ⁻¹).toMonoidHom (t i)
  have hu : u ∈ UTorus.detOne F m := by
    rw [UTorus.mem_detOne] at ht ⊢
    change (∏ i, Units.map (τ⁻¹).toMonoidHom (t i)) = 1
    rw [← map_prod (Units.map (τ⁻¹).toMonoidHom) (fun i => t i) Finset.univ]
    rw [ht, map_one]
  have hdiag := p9u7a_diag_of_detOne_tau h hm hφker hdiag ι hι hinner hβ hg hβg hu
  have hτu : (fun i => τ ((u i : F))) = fun i => (t i : F) := by
    funext i
    simp [u, Units.coe_map]
  rwa [hτu] at hdiag

private lemma p9u7a_exists_diag_scalar_of_transport (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    {β : MulAut L} (hβ : β ∈ Subgroup.normalizer (A : Set (MulAut L)))
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m)) {τ : F ≃+* F}
    (hβg : InndiagSU.IsSemilin φ β g τ)
    {a : ↥A} {t : Fin m → Fˣ} {d : Fˣ} {Da : GL (Fin m) F}
    (hDa : Da ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F)))
    (hDat : (Da : Matrix (Fin m) (Fin m) F) = diagonal (fun i => (t i : F) * (d : F)))
    (hacta : ∀ s : ↥(unitarySU 2 1 F m), (a : MulAut L) (φ s) = φ (conjN Da hDa s))
    {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ u : Fin m → F,
      ((g : Matrix (Fin m) (Fin m) F) * diagonal u *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) =
        diagonal (fun i => u (σ.symm i))) :
    ∃ (tb : Fin m → F) (Db : GL (Fin m) F)
      (hDb : Db ∈ Subgroup.normalizer (unitarySU 2 1 F m : Set (GL (Fin m) F))) (e : Fˣ),
      (Db : Matrix (Fin m) (Fin m) F) = diagonal tb ∧
      (∀ s : ↥(unitarySU 2 1 F m),
        ((ggConjAut A hβ a : ↥A) : MulAut L) (φ s) = φ (conjN Db hDb s)) ∧
      (∀ i, tb i = τ ((t (σ.symm i) : F)) * (e : F)) := by
  let b : ↥A := ggConjAut A hβ a
  obtain ⟨tb, htb⟩ := hdiag (b : MulAut L) b.2
  obtain ⟨Db, hDb, hDbt, hbact⟩ := htb
  obtain ⟨M, hM, hMmat, hactM⟩ := p9u7a_transport h hg hβg hDa hDat hacta
  obtain ⟨c2, hMdiag⟩ := p9u7a_diagonal_of_normalizes h hm hφker hDb hDbt hbact hM hactM
  have hM_mono : (M : Matrix (Fin m) (Fin m) F) =
      diagonal (fun i => τ ((t (σ.symm i) : F) * (d : F))) := by
    rw [hMmat, hDat]
    simp only [Matrix.diagonal_map, map_zero]
    simpa using hσ (fun i => τ ((t i : F) * (d : F)))
  have htb_eq : ∀ i, tb i * c2 = τ ((t (σ.symm i) : F) * (d : F)) := by
    intro i
    have hdiag_eq : diagonal (fun j => tb j * c2) =
        diagonal (fun j => τ ((t (σ.symm j) : F) * (d : F))) := by
      rw [← hMdiag, hM_mono]
    exact congrFun (Matrix.diagonal_injective hdiag_eq) i
  have hc2 : c2 ≠ 0 := by
    intro hc
    have h0 := diag_ne_zero_of_eq hMdiag (⟨0, by omega⟩ : Fin m)
    exact h0 (by rw [hc, mul_zero])
  have hτd : τ (d : F) ≠ 0 := by simpa using (τ.injective.ne (by simp [d]))
  let eF : F := τ (d : F) * c2⁻¹
  have heF : eF ≠ 0 := by
    change τ (d : F) * c2⁻¹ ≠ 0
    exact mul_ne_zero hτd (inv_ne_zero hc2)
  let e : Fˣ := Units.mk0 eF heF
  have htb_unit : ∀ i, tb i = τ ((t (σ.symm i) : F)) * (e : F) := by
    intro i
    have h1 := htb_eq i
    rw [map_mul] at h1
    apply mul_right_cancel₀ hc2
    rw [h1]
    have he_mul : (e : F) * c2 = τ (d : F) := by
      change (τ (d : F) * c2⁻¹) * c2 = τ (d : F)
      rw [mul_assoc, inv_mul_cancel₀ hc2, mul_one]
    rw [mul_assoc, he_mul]
  exact ⟨tb, Db, hDb, e, hDbt, hbact, htb_unit⟩

private lemma p9u7a_final_step (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    (hinner : UTorus.inner F m ≤ ι.range)
    {β : MulAut L} (hβ : β ∈ Subgroup.normalizer (A : Set (MulAut L)))
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m)) {τ : F ≃+* F}
    (hβg : InndiagSU.IsSemilin φ β g τ)
    {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ u : Fin m → F,
      ((g : Matrix (Fin m) (Fin m) F) * diagonal u *
        ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) =
        diagonal (fun i => u (σ.symm i))) :
    ∀ (a : ↥A) (t : Fin m → Fˣ), ι a = QuotientGroup.mk t →
      ι (ggConjAut A hβ a) =
        QuotientGroup.mk (fun i => Units.map τ.toMonoidHom (t (σ.symm i))) := by
  intro a t hιa
  obtain ⟨d, Da, hDa, hDat, hacta⟩ := p9u7a_exists_diag_rep_mul_scalar hdiag ι hι hιa
  obtain ⟨tb, Db, hDb, e, hDbt, hbact, htb_unit⟩ :=
    p9u7a_exists_diag_scalar_of_transport h hm hφker hdiag hβ hg hβg hDa hDat hacta hσ
  let b : ↥A := ggConjAut A hβ a
  let ub : Fin m → Fˣ := fun i => Units.mk0 (tb i) (diag_ne_zero_of_eq hDbt i)
  have hUb : ActsDiagU φ (b : MulAut L) (fun i => (ub i : F)) := by
    have hfunb : (fun i => (ub i : F)) = tb := by
      funext i
      simp [ub, Units.val_mk0]
    rw [hfunb]
    exact ⟨Db, hDb, hDbt, hbact⟩
  have hb_ub : ι b = QuotientGroup.mk ub := hι b ub hUb
  have hmk_ub : (QuotientGroup.mk ub : UTorus.Proj F m) =
      (QuotientGroup.mk (fun i => Units.map τ.toMonoidHom (t (σ.symm i))) :
        UTorus.Proj F m) := by
    rw [QuotientGroup.eq]
    refine UTorus.mem_scalars.mpr ⟨e⁻¹, ?_⟩
    intro i
    change (ub i)⁻¹ * Units.map τ.toMonoidHom (t (σ.symm i)) = e⁻¹
    apply Units.ext
    simp only [ub, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mul, Units.coe_map]
    rw [htb_unit i]
    have ht_ne : τ ((t (σ.symm i) : F)) ≠ 0 := by
      simpa using (τ.injective.ne (Units.ne_zero (t (σ.symm i))))
    have he_ne : (e : F) ≠ 0 := Units.ne_zero e
    field_simp [ht_ne, he_ne]
    rfl
  change ι b = QuotientGroup.mk (fun i => Units.map τ.toMonoidHom (t (σ.symm i)))
  rw [hb_ub, hmk_ub]

theorem P9_U7a_perm_of_normalizes (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    (hinner : UTorus.inner F m ≤ ι.range)
    {β : MulAut L} (hβ : β ∈ Subgroup.normalizer (A : Set (MulAut L)))
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h (idGram F m)) {τ : F ≃+* F}
    (hβg : InndiagSU.IsSemilin φ β g τ) :
    ∃ σ : Equiv.Perm (Fin m), ∀ (a : ↥A) (t : Fin m → Fˣ), ι a = QuotientGroup.mk t →
      ι (ggConjAut A hβ a) =
        QuotientGroup.mk (fun i => Units.map τ.toMonoidHom (t (σ.symm i))) := by
  obtain ⟨σ, hσ⟩ := P9_U7a_exists_perm_of_conj_diag h hm g
    (p9u7a_all_detOne h hm hφker hdiag ι hι hinner hβ hg hβg)
  exact ⟨σ, p9u7a_final_step h hm hφker hdiag ι hι hinner hβ hg hβg hσ⟩

end CFSG.StandardType.FrameRoute

end
