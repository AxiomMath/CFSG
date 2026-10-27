module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Comm
public import CFSG.Quasithin.Vol2.Ch10Reselect.Model
public import CFSG.Quasithin.Vol2.Ch10Reselect.Commutant
public import CFSG.Quasithin.Vol2.Ch10Reselect.H2Pure

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

abbrev fsuML (T L : Subgroup G) : Subgroup G :=
  fsuM T L ⊓ Subgroup.normalizer (L : Set G)

theorem L_le_fsuML : L ≤ fsuML T L :=
  le_inf ((le_fsuL0 T L).trans (fsuL0_le_fsuM T L)) Subgroup.le_normalizer

private lemma normU_of_mem_fsuML {s : G} (hs : s ∈ fsuML T L) :
    s ∈ Subgroup.normalizer (fsuUL T L I : Set G) := by
  obtain ⟨hsM, hsL⟩ := Subgroup.mem_inf.mp hs
  rw [← conjugate_eq_self_iff, conjugate_commutator_fsuVM hsM, conjugate_eq_self_iff.mpr hsL]

private lemma conj_mem_centralizer' {X : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (x : G) :
    t * x * t⁻¹ ∈ Subgroup.centralizer (X : Set G) ↔ x ∈ Subgroup.centralizer (X : Set G) := by
  have hX : ∀ a : G, a ∈ X ↔ t * a * t⁻¹ ∈ X := fun a => Subgroup.mem_normalizer_iff.mp ht a
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy b hb
    have h := hy _ ((hX b).mp hb)
    have h2 : t * (b * x) * t⁻¹ = t * (x * b) * t⁻¹ := by
      calc t * (b * x) * t⁻¹ = t * b * t⁻¹ * (t * x * t⁻¹) := by group
        _ = t * x * t⁻¹ * (t * b * t⁻¹) := h
        _ = t * (x * b) * t⁻¹ := by group
    have h3 := congrArg (fun y => t⁻¹ * y * t) h2
    simpa [mul_assoc] using h3
  · intro hx b hb
    have hb' : t⁻¹ * b * t ∈ X := (hX _).mpr (by simpa [mul_assoc] using hb)
    have h1 := hx _ hb'
    calc b * (t * x * t⁻¹) = t * (t⁻¹ * b * t * x) * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * b * t)) * t⁻¹ := by rw [h1]
      _ = t * x * t⁻¹ * b := by group

private lemma normZ_of_mem_fsuML {s : G} (hs : s ∈ fsuML T L) :
    s ∈ Subgroup.normalizer ((fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :
      Subgroup G) : Set G) := by
  obtain ⟨hsM, -⟩ := Subgroup.mem_inf.mp hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp (normU_of_mem_fsuML hs) h)
    (conj_mem_centralizer' (X := fsuL0 T L) hsM h).symm

private lemma conj_mem_L (s : ↥(fsuML T L)) (l : ↥L) : (s : G) * (l : G) * (s : G)⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp s.2).2 (l : G)).mp l.2

private lemma conj_mem_U_L (l : ↥L) (u : ↥(fsuUL T L I)) :
    (l : G) * (u : G) * (l : G)⁻¹ ∈ fsuUL T L I :=
  (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_fsuUL T L I l.2) (u : G)).mp u.2

private lemma conj_mem_U_M (s : ↥(fsuML T L)) (u : ↥(fsuUL T L I)) :
    (s : G) * (u : G) * (s : G)⁻¹ ∈ fsuUL T L I :=
  (Subgroup.mem_normalizer_iff.mp (normU_of_mem_fsuML s.2) (u : G)).mp u.2

theorem mem_acting_of_mem_fsuML {s : G} (hs : s ∈ fsuML T L) :
    s ∈ UModel.acting (fsuUL T L I)
      (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
  unfold UModel.acting
  exact Subgroup.mem_inf.mpr ⟨normU_of_mem_fsuML hs, normZ_of_mem_fsuML hs⟩

abbrev RModel (T L I : Subgroup G) (K : Type) [Field K] : Type :=
  UModel (fsuVM T L I) (fsuUL T L I)
    (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) L K

variable {K : Type} [Field K]

@[expose] noncomputable def actML (M : RModel T L I K) : ↥(fsuML T L) →* Equiv.Perm (UTilde K) :=
  UModel.actHom M |>.comp (Subgroup.inclusion fun _ hs => mem_acting_of_mem_fsuML hs)

private theorem gamma_conj_eq (M : RModel T L I K) (s : ↥(fsuML T L)) (l : ↥L)
    (hc : ⁅(s : G), (l : G)⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    M.γ ⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩ = M.γ l := by
  have hc' : ((⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩ * l⁻¹ : ↥L) : G) ∈
      Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [commutatorElement_def] at hc
    exact hc
  have h1 : M.γ (⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩ * l⁻¹) = 1 :=
    (M.γ_ker _).mpr hc'
  calc M.γ ⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩
      = M.γ (⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩ * l⁻¹) * M.γ l := by
        rw [← map_mul, inv_mul_cancel_right]
    _ = M.γ l := by rw [h1, one_mul]

theorem actML_ψ (M : RModel T L I K) (s : ↥(fsuML T L)) (u : ↥(fsuUL T L I))
    (hu : (s : G) * (u : G) * (s : G)⁻¹ ∈ fsuUL T L I) :
    Multiplicative.toAdd (M.ψ ⟨(s : G) * (u : G) * (s : G)⁻¹, hu⟩) =
      actML M s (Multiplicative.toAdd (M.ψ u)) :=
  UModel.actHom_ψ M ⟨(s : G), mem_acting_of_mem_fsuML s.2⟩ u hu

theorem actML_add (M : RModel T L I K) (s : ↥(fsuML T L)) (p q : UTilde K) :
    actML M s (p + q) = actML M s p + actML M s q :=
  UModel.actHom_add M ⟨(s : G), mem_acting_of_mem_fsuML s.2⟩ p q

theorem actML_conj_rho (M : RModel T L I K) (s : ↥(fsuML T L)) (l l' : ↥L)
    (h : (l' : G) = (s : G) * (l : G) * (s : G)⁻¹) :
    actML M s * rhoSL K (M.γ l) = rhoSL K (M.γ l') * actML M s := by
  refine Equiv.ext fun p => ?_
  obtain ⟨u, hu⟩ := M.surj (Multiplicative.ofAdd p)
  have hp : Multiplicative.toAdd (M.ψ u) = p := congrArg Multiplicative.toAdd hu
  rw [← hp]
  show actML M s (rhoSL K (M.γ l) (Multiplicative.toAdd (M.ψ u))) =
    rhoSL K (M.γ l') (actML M s (Multiplicative.toAdd (M.ψ u)))
  have hlu : (l : G) * (u : G) * (l : G)⁻¹ ∈ fsuUL T L I := conj_mem_U_L l u
  have hsu : (s : G) * (u : G) * (s : G)⁻¹ ∈ fsuUL T L I := conj_mem_U_M s u
  have hsl : (s : G) * ((l : G) * (u : G) * (l : G)⁻¹) * (s : G)⁻¹ ∈ fsuUL T L I :=
    conj_mem_U_M s ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩
  have hl' : (l' : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (l' : G)⁻¹ ∈ fsuUL T L I :=
    conj_mem_U_L l' ⟨(s : G) * (u : G) * (s : G)⁻¹, hsu⟩
  have e1 : rhoSL K (M.γ l) (Multiplicative.toAdd (M.ψ u)) =
      Multiplicative.toAdd (M.ψ ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩) :=
    (congrArg Multiplicative.toAdd (M.equiv l u hlu)).symm
  have e2 : actML M s (Multiplicative.toAdd (M.ψ ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩)) =
      Multiplicative.toAdd (M.ψ ⟨(s : G) * ((l : G) * (u : G) * (l : G)⁻¹) * (s : G)⁻¹, hsl⟩) :=
    (actML_ψ M s ⟨(l : G) * (u : G) * (l : G)⁻¹, hlu⟩ hsl).symm
  have e3 : actML M s (Multiplicative.toAdd (M.ψ u)) =
      Multiplicative.toAdd (M.ψ ⟨(s : G) * (u : G) * (s : G)⁻¹, hsu⟩) :=
    (actML_ψ M s u hsu).symm
  have e4 : rhoSL K (M.γ l') (Multiplicative.toAdd (M.ψ ⟨(s : G) * (u : G) * (s : G)⁻¹, hsu⟩)) =
      Multiplicative.toAdd (M.ψ ⟨(l' : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (l' : G)⁻¹, hl'⟩) :=
    (congrArg Multiplicative.toAdd (M.equiv l' ⟨(s : G) * (u : G) * (s : G)⁻¹, hsu⟩ hl')).symm
  have e5 : M.ψ ⟨(s : G) * ((l : G) * (u : G) * (l : G)⁻¹) * (s : G)⁻¹, hsl⟩ =
      M.ψ ⟨(l' : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (l' : G)⁻¹, hl'⟩ := by
    congr 1
    apply Subtype.ext
    show (s : G) * ((l : G) * (u : G) * (l : G)⁻¹) * (s : G)⁻¹ =
      (l' : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (l' : G)⁻¹
    rw [h]
    group
  rw [e1, e2, e3, e4, e5]

theorem actML_hnorm (M : RModel T L I K) (s : ↥(fsuML T L))
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) K,
      actML M s * rhoSL K g = rhoSL K g' * actML M s := by
  obtain ⟨l, hl⟩ := M.γ_surj g
  refine ⟨M.γ ⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩, ?_⟩
  rw [← hl]
  exact actML_conj_rho M s l ⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩ rfl

theorem actML_mem_centralizerSL2 (M : RModel T L I K) (s : ↥(fsuML T L))
    (h : ∀ l ∈ L, ⁅(s : G), l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    actML M s ∈ centralizerSL2 K := by
  refine ⟨fun v w => actML_add M s v w, fun g v => ?_⟩
  obtain ⟨l, hl⟩ := M.γ_surj g
  have hcomm : actML M s * rhoSL K (M.γ l) = rhoSL K (M.γ l) * actML M s := by
    rw [actML_conj_rho M s l ⟨(s : G) * (l : G) * (s : G)⁻¹, conj_mem_L s l⟩ rfl,
      gamma_conj_eq M s l (h (l : G) l.2)]
  have key := congrArg (fun φ : Equiv.Perm (UTilde K) => φ v) hcomm
  simp only [Equiv.Perm.mul_apply, rhoSL_apply] at key
  rw [← hl]
  exact key

theorem commutator_mem_centralizer_of_actML (M : RModel T L I K) (s : ↥(fsuML T L))
    (h : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      actML M s * rhoSL K g = rhoSL K g * actML M s) :
    ∀ l ∈ L, ⁅(s : G), l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  intro l hl
  have h1 := actML_conj_rho M s ⟨l, hl⟩ ⟨(s : G) * l * (s : G)⁻¹, conj_mem_L s ⟨l, hl⟩⟩ rfl
  have h2 := h (M.γ ⟨l, hl⟩)
  rw [h1] at h2
  have h3 : rhoSL K (M.γ ⟨(s : G) * l * (s : G)⁻¹, conj_mem_L s ⟨l, hl⟩⟩) =
      rhoSL K (M.γ ⟨l, hl⟩) := mul_right_cancel h2
  have h4 : M.γ ⟨(s : G) * l * (s : G)⁻¹, conj_mem_L s ⟨l, hl⟩⟩ = M.γ ⟨l, hl⟩ :=
    rhoSL_injective h3
  have h5 : M.γ (⟨(s : G) * l * (s : G)⁻¹, conj_mem_L s ⟨l, hl⟩⟩ * ⟨l, hl⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h4, mul_inv_cancel]
  have h6 := (M.γ_ker _).mp h5
  have h7 : ((⟨(s : G) * l * (s : G)⁻¹, conj_mem_L s ⟨l, hl⟩⟩ * ⟨l, hl⟩⁻¹ : ↥L) : G) =
      ⁅(s : G), l⁆ := by
    show (s : G) * l * (s : G)⁻¹ * l⁻¹ = ⁅(s : G), l⁆
    rw [commutatorElement_def]
  rw [h7] at h6
  exact h6

theorem actML_eq_one_of_mem_centralizer (M : RModel T L I K) (s : ↥(fsuML T L))
    (hs : (s : G) ∈ Subgroup.centralizer (fsuVM T L I : Set G)) : actML M s = 1 := by
  have h : M.actHom ⟨(s : G), mem_acting_of_mem_fsuML s.2⟩ = 1 := by
    rw [UModel.actHom_eq_one_iff]
    intro u hu
    have hcomm : (u : G) * (s : G) = (s : G) * u :=
      Subgroup.mem_centralizer_iff.mp hs u (fsuUL_le_fsuVM T L I hu)
    have e : (s : G) * u * (s : G)⁻¹ * u⁻¹ = 1 := by
      rw [← hcomm]
      group
    show (s : G) * u * (s : G)⁻¹ * u⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)
    rw [e]
    exact one_mem _
  exact h

theorem actML_of_mem_L (M : RModel T L I K) (l : ↥L) :
    actML M ⟨(l : G), L_le_fsuML l.2⟩ = rhoSL K (M.γ l) :=
  UModel.actHom_of_mem_L M ⟨(l : G), mem_acting_of_mem_fsuML (L_le_fsuML l.2)⟩ l.2

theorem card_SL_dvd_card_L (M : RModel T L I K) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ∣ Nat.card L := by
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = M.γ.ker.index := by
    rw [Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective M.γ M.γ_surj).toEquiv.symm
  rw [h1]
  exact Subgroup.index_dvd_card _

end CFSG.Quasithin.Vol2.Ch10Reselect
