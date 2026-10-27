module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212

variable {Γ : Type*} [Group Γ]

theorem mem_map_conj_iff (J : Subgroup Γ) (a x : Γ) :
    x ∈ J.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ J := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map_conj_inv (J : Subgroup Γ) (a : Γ) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = J := by
  rw [Thm210.map_conj_map_conj, inv_mul_cancel, Thm210.map_conj_one]

theorem map_conj_comm_of_commute (J : Subgroup Γ) {a d : Γ} (h : a * d = d * a) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj d).toMonoidHom =
      (J.map (MulAut.conj d).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Thm210.map_conj_map_conj, Thm210.map_conj_map_conj, h]

theorem mem_normalizer_iff_map_conj (J : Subgroup Γ) (g : Γ) :
    g ∈ Subgroup.normalizer (J : Set Γ) ↔ J.map (MulAut.conj g).toMonoidHom = J :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem mem_normalizer_map_conj_iff_of_commute {J : Subgroup Γ} {a d : Γ} (h : a * d = d * a) :
    a ∈ Subgroup.normalizer ((J.map (MulAut.conj d).toMonoidHom : Subgroup Γ) : Set Γ) ↔
      a ∈ Subgroup.normalizer (J : Set Γ) := by
  rw [mem_normalizer_iff_map_conj, mem_normalizer_iff_map_conj, map_conj_comm_of_commute J h.symm]
  exact (Subgroup.map_injective (MulAut.conj d).injective).eq_iff

theorem mem_centralizer_map_conj_iff_of_commute {J : Subgroup Γ} {a d : Γ} (h : a * d = d * a) :
    a ∈ Subgroup.centralizer ((J.map (MulAut.conj d).toMonoidHom : Subgroup Γ) : Set Γ) ↔
      a ∈ Subgroup.centralizer (J : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc j hj
    have h1 := hc (d * j * d⁻¹)
      ((mem_map_conj_iff J d _).mpr (by rwa [show d⁻¹ * (d * j * d⁻¹) * d = j by group]))
    have h2 : j * a = a * j := by
      have h3 : d * (j * a) * d⁻¹ = d * (a * j) * d⁻¹ := by
        calc d * (j * a) * d⁻¹ = (d * j * d⁻¹) * (d * a * d⁻¹) := by group
          _ = (d * j * d⁻¹) * a := by rw [← h]; group
          _ = a * (d * j * d⁻¹) := h1
          _ = (d * a * d⁻¹) * (d * j * d⁻¹) := by rw [← h]; group
          _ = d * (a * j) * d⁻¹ := by group
      simpa using h3
    exact h2
  · intro hc x hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' := hc j hj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc d * j * d⁻¹ * a = d * (j * (d⁻¹ * a)) := by group
      _ = d * (j * (a * d⁻¹)) := by
        congr 2
        calc d⁻¹ * a = d⁻¹ * a * d * d⁻¹ := by group
          _ = d⁻¹ * (a * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * a) * d⁻¹ := by rw [h]
          _ = a * d⁻¹ := by group
      _ = d * ((j * a) * d⁻¹) := by group
      _ = d * ((a * j) * d⁻¹) := by rw [hj']
      _ = a * (d * j * d⁻¹) := by
        calc d * (a * j * d⁻¹) = (d * a) * j * d⁻¹ := by group
          _ = (a * d) * j * d⁻¹ := by rw [h]
          _ = a * (d * j * d⁻¹) := by group

theorem orbitClosure_eq_sSup (J A : Subgroup Γ) :
    orbitClosure J A = sSup {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} := by
  refine le_antisymm (orbitClosure_le fun a ha => le_sSup ⟨a, ha, rfl⟩) (sSup_le ?_)
  rintro K ⟨a, ha, rfl⟩
  exact map_conj_le_orbitClosure J ha

theorem le_normalizer_orbitClosure (J A : Subgroup Γ) :
    A ≤ Subgroup.normalizer (orbitClosure J A : Set Γ) := by
  refine Thm210.le_normalizer_of_conj_mem fun c hc x hx => ?_
  have hle : orbitClosure J A ≤ (orbitClosure J A).comap (MulAut.conj c).toMonoidHom := by
    refine orbitClosure_le fun a ha => ?_
    rw [← Subgroup.map_le_iff_le_comap, Thm210.map_conj_map_conj]
    exact map_conj_le_orbitClosure J (mul_mem hc ha)
  simpa using hle hx

theorem orbitClosure_le_of_normalizer {J Y A : Subgroup Γ} (hJY : J ≤ Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set Γ)) : orbitClosure J A ≤ Y := by
  refine orbitClosure_le fun a ha x hx => ?_
  obtain ⟨j, hj, rfl⟩ := hx
  exact (Subgroup.mem_normalizer_iff.mp (hAY ha) j).mp (hJY hj)

theorem orbitClosure_map_conj_of_commute (J B : Subgroup Γ) {d : Γ}
    (hd : ∀ b ∈ B, b * d = d * b) :
    (orbitClosure J B).map (MulAut.conj d).toMonoidHom =
      orbitClosure (J.map (MulAut.conj d).toMonoidHom) B := by
  unfold orbitClosure
  rw [Subgroup.map_iSup]
  refine iSup_congr fun b => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hb => map_conj_comm_of_commute J (hd b hb).symm ▸ rfl

theorem map_conj_centralizer_of_commute (B : Subgroup Γ) {d : Γ} (hd : ∀ b ∈ B, b * d = d * b) :
    (Subgroup.centralizer (B : Set Γ)).map (MulAut.conj d).toMonoidHom =
      Subgroup.centralizer (B : Set Γ) := by
  ext x
  rw [mem_map_conj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine forall₂_congr fun b hb => ?_
  have hbd : Commute b d := hd b hb
  have h1 : b * d⁻¹ = d⁻¹ * b := hbd.inv_right.eq
  have h2 : b * (d⁻¹ * x * d) = d⁻¹ * (b * x) * d := by
    calc b * (d⁻¹ * x * d) = (b * d⁻¹) * x * d := by group
      _ = d⁻¹ * (b * x) * d := by rw [h1]; group
  have h3 : d⁻¹ * x * d * b = d⁻¹ * (x * b) * d := by
    calc d⁻¹ * x * d * b = d⁻¹ * x * (d * b) := by group
      _ = d⁻¹ * x * (b * d) := by rw [hbd.eq.symm]
      _ = d⁻¹ * (x * b) * d := by group
  rw [h2, h3]
  constructor
  · intro h
    simpa using h
  · intro h
    rw [h]

theorem smear_map_conj_of_commute (J B : Subgroup Γ) {d : Γ}
    (hd : ∀ b ∈ B, b * d = d * b) :
    (smear J B).map (MulAut.conj d).toMonoidHom = smear (J.map (MulAut.conj d).toMonoidHom) B := by
  unfold smear
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d).injective, orbitClosure_map_conj_of_commute J B hd,
    map_conj_centralizer_of_commute B hd]

theorem orbitClosure_map_conj_of_mem (J : Subgroup Γ) {A : Subgroup Γ} {a : Γ} (ha : a ∈ A) :
    orbitClosure (J.map (MulAut.conj a).toMonoidHom) A = orbitClosure J A := by
  have key : ∀ (J : Subgroup Γ) {a : Γ}, a ∈ A →
      orbitClosure (J.map (MulAut.conj a).toMonoidHom) A ≤ orbitClosure J A := by
    intro J a ha
    refine orbitClosure_le fun b hb => ?_
    rw [Thm210.map_conj_map_conj]
    exact map_conj_le_orbitClosure J (mul_mem hb ha)
  refine le_antisymm (key J ha) ?_
  have := key (J.map (MulAut.conj a).toMonoidHom) (inv_mem ha)
  rwa [map_conj_map_conj_inv] at this

theorem commute_sSup_sSup {S T₁ T₂ : Set (Subgroup Γ)} {K : Subgroup Γ} (hK : IsDirectProduct S K)
    (hd : Disjoint T₁ T₂) (h₁ : T₁ ⊆ S) (h₂ : T₂ ⊆ S) :
    ∀ x ∈ sSup T₁, ∀ y ∈ sSup T₂, Commute x y := by
  have step : ∀ J₁ ∈ T₁, ∀ x ∈ J₁, ∀ y ∈ sSup T₂, Commute x y := by
    intro J₁ hJ₁ x hx y hy
    have : sSup T₂ ≤ Subgroup.centralizer ({x} : Set Γ) := by
      refine sSup_le fun J₂ hJ₂ z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hne : J₁ ≠ J₂ := fun h => Set.disjoint_left.mp hd hJ₁ (h ▸ hJ₂)
      exact (hK.commute J₂ (h₂ hJ₂) J₁ (h₁ hJ₁) hne.symm z hz x hx).eq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm
  intro x hx y hy
  have : sSup T₁ ≤ Subgroup.centralizer ({y} : Set Γ) := by
    refine sSup_le fun J₁ hJ₁ z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (step J₁ hJ₁ z hz y hy).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)

theorem exists_complement_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A F : Subgroup Γ}
    (hA : IsElemAbelian p A) (hFA : F ≤ A) :
    ∃ C : Subgroup Γ, C ≤ A ∧ F ⊓ C = ⊥ ∧ F ⊔ C = A := by
  have : IsMulCommutative A := hA.1
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  obtain ⟨C', hC'⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists p hp A
    (fun x => Subtype.ext (by simpa using hA.2 x x.2)) (F.subgroupOf A)
  refine ⟨C'.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, c, hc, rfl⟩ := Subgroup.mem_inf.mp hx
    have hcF : c ∈ F.subgroupOf A := hxF
    have : c ∈ F.subgroupOf A ⊓ C' := Subgroup.mem_inf.mpr ⟨hcF, hc⟩
    rw [hC'.disjoint.eq_bot, Subgroup.mem_bot] at this
    simp [this]
  · refine le_antisymm (sup_le hFA (Subgroup.map_subtype_le _)) fun a ha => ?_
    have h1 : (⟨a, ha⟩ : A) ∈ F.subgroupOf A ⊔ C' := by
      rw [hC'.sup_eq_top]
      trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp h1
    have : a = (x : Γ) * (y : Γ) := by
      have := congrArg Subtype.val hxy
      exact this.symm
    rw [this]
    exact Subgroup.mul_mem_sup hx ⟨y, hy, rfl⟩

theorem normalizer_le_normalizer_map_subtype {Y : Subgroup Γ} (P : Subgroup ↥Y)
    [P.Characteristic] :
    Subgroup.normalizer (Y : Set Γ) ≤
      Subgroup.normalizer ((P.map Y.subtype : Subgroup Γ) : Set Γ) := by
  have key : ∀ {g : Γ}, g ∈ Subgroup.normalizer (Y : Set Γ) → ∀ {x : Γ},
      x ∈ P.map Y.subtype → g * x * g⁻¹ ∈ P.map Y.subtype := by
    intro g hg x hx
    let φ : MulAut ↥Y := Y.normalizerMonoidHom ⟨g, hg⟩
    have hφ : ∀ t : Y, ((φ t : Y) : Γ) = g * t * g⁻¹ := fun t =>
      Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨g, hg⟩ t
    have hchar : P.map φ.toMonoidHom = P :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance φ
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨φ t, ?_, (hφ t).symm ▸ rfl⟩
    rw [← hchar]
    exact ⟨t, ht, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hg hx, fun hx => ?_⟩
  simpa [mul_assoc] using key (inv_mem hg) hx

theorem normalizer_le_normalizer_sol (X : Subgroup Γ) [Finite Γ] :
    Subgroup.normalizer (X : Set Γ) ≤ Subgroup.normalizer (sol X : Set Γ) :=
  normalizer_le_normalizer_map_subtype (CFSG.solvableRadical ↥X)

theorem map_conj_mem_of_mem_sup {Ω : Set (Subgroup Γ)} {X Y : Subgroup Γ}
    (hX : ∀ g ∈ X, ∀ J ∈ Ω, J.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (hY : ∀ g ∈ Y, ∀ J ∈ Ω, J.map (MulAut.conj g).toMonoidHom ∈ Ω) {g : Γ} (hg : g ∈ X ⊔ Y) :
    ∀ J ∈ Ω, J.map (MulAut.conj g).toMonoidHom ∈ Ω := by
  have key : ∀ g ∈ X ⊔ Y, ∀ J ∈ Ω,
      J.map (MulAut.conj g).toMonoidHom ∈ Ω ∧ J.map (MulAut.conj g⁻¹).toMonoidHom ∈ Ω := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ J ∈ Ω,
      J.map (MulAut.conj g).toMonoidHom ∈ Ω ∧ J.map (MulAut.conj g⁻¹).toMonoidHom ∈ Ω)
      (fun x hx J hJ => ?_) (fun J hJ => ?_) (fun x y _ _ hx hy J hJ => ?_)
      (fun x _ hx J hJ => ?_) hg
    · rcases hx with hx | hx
      · exact ⟨hX x hx J hJ, hX x⁻¹ (inv_mem hx) J hJ⟩
      · exact ⟨hY x hx J hJ, hY x⁻¹ (inv_mem hx) J hJ⟩
    · rw [inv_one, Thm210.map_conj_one]
      exact ⟨hJ, hJ⟩
    · refine ⟨?_, ?_⟩
      · rw [← Thm210.map_conj_map_conj]
        exact (hx _ (hy J hJ).1).1
      · rw [mul_inv_rev, ← Thm210.map_conj_map_conj]
        exact (hy _ (hx J hJ).2).2
    · rw [inv_inv]
      exact ⟨(hx J hJ).2, (hx J hJ).1⟩
  exact fun J hJ => (key g hg J hJ).1

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212
