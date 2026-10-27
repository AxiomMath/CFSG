module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M3

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T614

section Basic

variable {Γ : Type*} [Group Γ]

theorem conj_comm_iff (g j y : Γ) :
    (g * j * g⁻¹) * y = y * (g * j * g⁻¹) ↔ j * (g⁻¹ * y * g) = (g⁻¹ * y * g) * j := by
  constructor
  · intro h
    calc j * (g⁻¹ * y * g) = g⁻¹ * ((g * j * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * j * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * y * g) * j := by group
  · intro h
    calc (g * j * g⁻¹) * y = g * (j * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * j) * g⁻¹ := by rw [h]
      _ = y * (g * j * g⁻¹) := by group

theorem conj_mem_iff {X : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (X : Set Γ)) (y : Γ) :
    g⁻¹ * y * g ∈ X ↔ y ∈ X := by
  have := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)
  simpa [mul_assoc] using this

theorem exists_mul_of_mem_sup_of_le_normalizer {H B : Subgroup Γ}
    (hBH : B ≤ Subgroup.normalizer (H : Set Γ)) {x : Γ} (hx : x ∈ H ⊔ B) :
    ∃ h ∈ H, ∃ b ∈ B, x = h * b := by
  have hx' : x ∈ ((H ⊔ B : Subgroup Γ) : Set Γ) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H B hBH] at hx'
  obtain ⟨h, hh, b, hb, rfl⟩ := hx'
  exact ⟨h, hh, b, hb, rfl⟩

end Basic

section Finite

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem mem_jTilde_iff {H J : Subgroup Γ} (hsol : sol H = ⊥) (hJ : J ∈ lcal H) {x : Γ} :
    x ∈ jTilde H J ↔ x ∈ H ∧ ∀ J' ∈ lcal H, J' ≠ J → ∀ j ∈ J', x * j = j * x := by
  have hK := kOf_inf_centralizer_eq_sSup_diff hsol hJ
  unfold jTilde
  rw [hK, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxH, hx⟩
    refine ⟨hxH, fun J' hJ' hne j hj => ?_⟩
    have hmem : j ∈ sSup (lcal H \ {J}) := (le_sSup ⟨hJ', hne⟩ : J' ≤ sSup (lcal H \ {J})) hj
    exact (Subgroup.mem_centralizer_iff.mp hx j hmem).symm
  · rintro ⟨hxH, hx⟩
    refine ⟨hxH, ?_⟩
    have hle : sSup (lcal H \ {J}) ≤ Subgroup.centralizer ({x} : Set Γ) :=
      sSup_le fun J' hJ' j hj => Subgroup.mem_centralizer_singleton_iff.mpr
        (hx J' hJ'.1 hJ'.2 j hj).symm
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hm)

theorem jTilde_ne {H J J' : Subgroup Γ} (hsol : sol H = ⊥) (hJ : J ∈ lcal H) (hJ' : J' ∈ lcal H)
    (hne : J ≠ J') : jTilde H J ≠ jTilde H J' := by
  intro h
  have hK := isDirectProduct_lcal_kOf hsol
  have hle : J ≤ jTilde H J := fun j hj => by
    refine (mem_jTilde_iff hsol hJ).mpr
      ⟨(mem_lcal_iff.mp hJ).1 hj, fun J'' hJ'' hne'' j'' hj'' => ?_⟩
    exact (hK.commute J hJ J'' hJ'' (Ne.symm hne'') j hj j'' hj'').eq
  have hcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := fun x hx y hy =>
    ((mem_jTilde_iff hsol hJ').mp (h ▸ hle hx)).2 J hJ hne y hy
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  exact hnc (isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a a.2 b b.2))

theorem map_conj_jTilde {H : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (H : Set Γ))
    (J : Subgroup Γ) :
    (jTilde H J).map (MulAut.conj g).toMonoidHom =
      jTilde H (J.map (MulAut.conj g).toMonoidHom) := by
  have hgK : g ∈ Subgroup.normalizer (kOf H : Set Γ) := mem_normalizer_kOf_of_mem_normalizer hg
  have hmem : ∀ y : Γ, y ∈ kOf H ⊓ Subgroup.centralizer
      ((J.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ) ↔
        g⁻¹ * y * g ∈ kOf H ⊓ Subgroup.centralizer (J : Set Γ) := by
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, conj_mem_iff hgK y]
    refine and_congr Iff.rfl ?_
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy j hj
      have := hy (g * j * g⁻¹) ⟨j, hj, by simp [MulAut.conj_apply]⟩
      exact (conj_comm_iff g j y).mp this
    · rintro hy _ ⟨j, hj, rfl⟩
      exact (conj_comm_iff g j y).mpr (hy j hj)
  ext x
  rw [L514.mem_map_conj_iff]
  unfold jTilde
  rw [Subgroup.mem_inf, Subgroup.mem_inf, conj_mem_iff hg x]
  refine and_congr Iff.rfl ?_
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have := hx _ ((hmem y).mp hy)
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group
  · intro hx y hy
    have := hx (g * y * g⁻¹) ((hmem (g * y * g⁻¹)).mpr (by simpa [mul_assoc] using hy))
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * x * g) * y := by group

end Finite

end T614

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem exists_isWreath_E
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥)
    (hW : wTilde θ E B = thetaOf θ E) :
    ∃ L : Subgroup G, IsWreath (thetaOf θ E ⊔ A) L A E E ∧
      Nonempty (↥L ≃* ↥(thetaOf θ A)) := by
  classical
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 S.mem
  have hsol : sol (thetaOf θ E) = ⊥ := h.sol_thetaOf S.mem.1 hE0
  have hAN : A ≤ Subgroup.normalizer (thetaOf θ E : Set G) :=
    h.isFunctor.normalizes_thetaOf S.mem.1
  have hHE := h.normalizes_of_mem_lcal_thetaOf S.mem.1 hE0
  obtain ⟨-, -, hdp⟩ := h.wTilde_properties S hB hEB
  rw [hW] at hdp
  have hjle : ∀ J : Subgroup G, jTilde (thetaOf θ E) J ≤ thetaOf θ E := fun J => inf_le_left
  have hS0 : IsDirectProduct {Y | ∃ J ∈ lcal (thetaOf θ E), Y = jTilde (thetaOf θ E) J}
      (thetaOf θ E) := by
    have hset : {Y | ∃ J ∈ lcal (thetaOf θ E), Y = thetaOf θ E ⊓ jTilde (thetaOf θ E) J} =
        {Y | ∃ J ∈ lcal (thetaOf θ E), Y = jTilde (thetaOf θ E) J} :=
      Set.ext fun Y => ⟨fun ⟨J, hJ, hY⟩ => ⟨J, hJ, hY.trans (inf_eq_right.mpr (hjle J))⟩,
        fun ⟨J, hJ, hY⟩ => ⟨J, hJ, hY.trans (inf_eq_right.mpr (hjle J)).symm⟩⟩
    rwa [hset] at hdp
  obtain ⟨J₀, hJ₀⟩ := h.lcal_thetaOf_nonempty S.mem.1 hE0
  set L := jTilde (thetaOf θ E) J₀ with hL
  have htransA : ∀ J ∈ lcal (thetaOf θ E), ∃ a ∈ A, J = J₀.map (MulAut.conj a).toMonoidHom :=
    fun J hJ => h.exists_conj_eq_of_mem_lcal S.mem.1 hE0 hJ₀ hJ
  have hN : ∀ J ∈ lcal (thetaOf θ E), A ⊓ Subgroup.normalizer (J : Set G) = E := fun J hJ =>
    ((h.lemma_6_9_b S.mem.1 hE0 J hJ).symm.trans S.bN_E)
  have hNL : A ⊓ Subgroup.normalizer (L : Set G) = E := by
    ext a
    constructor
    · rintro ⟨haA, haL⟩
      have h1 := L69.map_conj_eq_self_iff.mpr haL
      rw [hL, T614.map_conj_jTilde (hAN haA)] at h1
      have hJa : J₀.map (MulAut.conj a).toMonoidHom ∈ lcal (thetaOf θ E) :=
        map_conj_mem_lcal hJ₀ (hAN haA)
      have h2 : J₀.map (MulAut.conj a).toMonoidHom = J₀ := by
        by_contra hne
        exact T614.jTilde_ne hsol hJa hJ₀ hne h1
      rw [← hN J₀ hJ₀]
      exact ⟨haA, L69.map_conj_eq_self_iff.mp h2⟩
    · intro ha
      have haJ : a ∈ A ⊓ Subgroup.normalizer (J₀ : Set G) := (hN J₀ hJ₀).symm ▸ ha
      refine ⟨haJ.1, L69.map_conj_eq_self_iff.mp ?_⟩
      rw [hL, T614.map_conj_jTilde (hAN haJ.1), L69.map_conj_eq_self_iff.mpr haJ.2]
  have hconjA : ∀ a ∈ A, L.map (MulAut.conj a).toMonoidHom =
      jTilde (thetaOf θ E) (J₀.map (MulAut.conj a).toMonoidHom) := fun a ha =>
    T614.map_conj_jTilde (hAN ha) J₀
  have hset : {K | ∃ g ∈ thetaOf θ E ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} =
      {Y | ∃ J ∈ lcal (thetaOf θ E), Y = jTilde (thetaOf θ E) J} := by
    ext K
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx, a, ha, rfl⟩ := T614.exists_mul_of_mem_sup_of_le_normalizer hAN hg
      have hJa : J₀.map (MulAut.conj a).toMonoidHom ∈ lcal (thetaOf θ E) :=
        map_conj_mem_lcal hJ₀ (hAN ha)
      refine ⟨J₀.map (MulAut.conj a).toMonoidHom, hJa, ?_⟩
      rw [← T517.map_conj_map_conj, hconjA a ha,
        T614.map_conj_jTilde (Subgroup.le_normalizer hx),
        L69.map_conj_eq_self_iff.mpr (hHE x hx _ hJa)]
    · rintro ⟨J, hJ, rfl⟩
      obtain ⟨a, ha, rfl⟩ := htransA J hJ
      exact ⟨a, Subgroup.mem_sup_right ha, (hconjA a ha).symm⟩
  have hsupr : (⨆ g ∈ thetaOf θ E ⊔ A, L.map (MulAut.conj g).toMonoidHom) =
      thetaOf θ E := by
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      have hmem : L.map (MulAut.conj g).toMonoidHom ∈
          {K | ∃ g ∈ thetaOf θ E ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} := ⟨g, hg, rfl⟩
      rw [hset] at hmem
      obtain ⟨J, -, hJ⟩ := hmem
      rw [hJ]
      exact hjle J
    · calc thetaOf θ E = sSup {Y | ∃ J ∈ lcal (thetaOf θ E), Y = jTilde (thetaOf θ E) J} :=
            hS0.sSup_eq.symm
        _ ≤ _ := by
          refine sSup_le ?_
          rintro _ ⟨J, hJ, rfl⟩
          have hmem : jTilde (thetaOf θ E) J ∈
              {K | ∃ g ∈ thetaOf θ E ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} := by
            rw [hset]
            exact ⟨J, hJ, rfl⟩
          obtain ⟨g, hg, hgJ⟩ := hmem
          rw [hgJ]
          exact le_iSup₂_of_le g hg le_rfl
  have hLE : E ≤ A ⊓ Subgroup.centralizer (L : Set G) := fun e he => by
    refine ⟨S.mem.1 he, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hlc : l ∈ Subgroup.centralizer (E : Set G) :=
      h.isFunctor.thetaOf_le_centralizer S.mem.1 ((hjle J₀) hl)
    exact (Subgroup.mem_centralizer_iff.mp hlc e he).symm
  refine ⟨L, ⟨h.elemAbelian.1, le_sup_right, (hjle J₀).trans le_sup_left, ?_, ?_, hNL.symm, ?_⟩,
    ?_⟩
  · refine le_antisymm (sup_le_sup_right (hjle J₀) A) (sup_le ?_ le_sup_right)
    rw [← hS0.sSup_eq]
    refine sSup_le ?_
    rintro _ ⟨J, hJ, rfl⟩
    obtain ⟨a, ha, rfl⟩ := htransA J hJ
    rw [← hconjA a ha]
    rintro x ⟨y, hy, rfl⟩
    show a * y * a⁻¹ ∈ L ⊔ A
    exact mul_mem (mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hy))
      (inv_mem (Subgroup.mem_sup_right ha))
  · rw [hsupr, hset]
    exact hS0
  · refine le_antisymm hLE ?_
    rw [← hNL]
    exact inf_le_inf_left A (Subgroup.centralizer_le_normalizer _)
  · have hker : A ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.centralizer (L : Set G) := by
      rw [hNL]
      exact fun x hx => (hLE hx).2
    have hper : ∀ b ∈ A, ∀ J ∈ {Y | ∃ J ∈ lcal (thetaOf θ E), Y = jTilde (thetaOf θ E) J},
        J.map (MulAut.conj b).toMonoidHom ∈
          {Y | ∃ J ∈ lcal (thetaOf θ E), Y = jTilde (thetaOf θ E) J} := by
      rintro b hb _ ⟨J, hJ, rfl⟩
      exact ⟨J.map (MulAut.conj b).toMonoidHom, map_conj_mem_lcal hJ (hAN hb),
        T614.map_conj_jTilde (hAN hb) J⟩
    obtain ⟨e⟩ := T614.nonempty_mulEquiv_inf_centralizer hS0 hper ⟨J₀, hJ₀, rfl⟩
      (fun K ⟨J, hJ, hK⟩ => by
        obtain ⟨a, ha, rfl⟩ := htransA J hJ
        exact ⟨a, ha, hK.trans (hconjA a ha).symm⟩)
      hker
    have hD : thetaOf θ E ⊓ Subgroup.centralizer (A : Set G) = thetaOf θ A :=
      h.thetaOf_inf_centralizer S.mem.1 hE0
    exact ⟨e.symm.trans (MulEquiv.subgroupCongr hD)⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
