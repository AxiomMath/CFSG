module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML2
public import CFSG.Quasithin.Vol2.Ch10Reselect.GLemma

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

private theorem h2_conj_mem_centralizer {X : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) {x : G}
    (hx : x ∈ Subgroup.centralizer (X : Set G)) :
    n * x * n⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro b hb
  have hb' : n⁻¹ * b * n ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * b * n)).mpr (by
      rw [show n * (n⁻¹ * b * n) * n⁻¹ = b by group]
      exact hb)
  have h1 := hx (n⁻¹ * b * n) hb'
  calc b * (n * x * n⁻¹) = n * (n⁻¹ * b * n * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * b * n)) * n⁻¹ := by rw [h1]
    _ = n * x * n⁻¹ * b := by group

private theorem h2_mem_normalizer_centralizer {X : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    n ∈ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hc
    exact h2_conj_mem_centralizer hn hc
  · intro hc
    have h' := h2_conj_mem_centralizer (Subgroup.inv_mem _ hn) hc
    rwa [show n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h by group] at h'

theorem pow_eq_one_of_corrector (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) [Finite K]
    (hL3 : ∀ k ∈ fsuM T L, (∀ l ∈ fsuL0 T L,
        ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) →
      k ∈ Subgroup.centralizer (fsuVM T L I : Set G))
    (M : RModel T L I K) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {z : G} (hz : z ∈ fsuML T L) {σ : RingAut K} {B B₂ : GL (Fin 2) K}
    (h1 : actML M ⟨z, hz⟩ = bPerm K B)
    (h2 : actML M ⟨t * z * t⁻¹, conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hz⟩ =
      phi K 1 σ B₂) :
    z ^ orderOf σ ∈ Subgroup.centralizer (fsuVM T L I : Set G) ∧ B ^ orderOf σ = 1 := by
  set m := orderOf σ with hm
  have hσm : σ ^ m = 1 := pow_orderOf_eq_one σ
  have hz_fsuM : z ∈ fsuM T L := (Subgroup.mem_inf.mp hz).1
  have hzm : z ^ m ∈ fsuML T L := Subgroup.pow_mem _ hz m
  have hzm_fsuM : z ^ m ∈ fsuM T L := Subgroup.pow_mem _ hz_fsuM m
  have hφzm : actML M ⟨z ^ m, hzm⟩ = bPerm K (B ^ m) := by
    have e : (⟨z ^ m, hzm⟩ : ↥(fsuML T L)) = (⟨z, hz⟩ : ↥(fsuML T L)) ^ m := rfl
    rw [e, map_pow, h1, bPerm_pow]
  have hcomm_zm : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      actML M ⟨z ^ m, hzm⟩ * rhoSL K g = rhoSL K g * actML M ⟨z ^ m, hzm⟩ := by
    intro g
    rw [hφzm]
    exact bPerm_comm_rhoSL (B ^ m) g
  have hL1 : ∀ l ∈ L, ⁅z ^ m, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    commutator_mem_centralizer_of_actML M ⟨z ^ m, hzm⟩ hcomm_zm
  have hts : t * z * t⁻¹ ∈ fsuML T L := conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hz
  have hs' : t * z ^ m * t⁻¹ ∈ fsuML T L := by
    rw [show t * z ^ m * t⁻¹ = (t * z * t⁻¹) ^ m from conj_pow.symm]
    exact Subgroup.pow_mem _ hts m
  obtain ⟨B', hB'⟩ := phi_one_pow σ B₂ m
  have hφs' : actML M ⟨t * z ^ m * t⁻¹, hs'⟩ = bPerm K B' := by
    have e : (⟨t * z ^ m * t⁻¹, hs'⟩ : ↥(fsuML T L)) =
        (⟨t * z * t⁻¹, hts⟩ : ↥(fsuML T L)) ^ m :=
      Subtype.ext conj_pow.symm
    rw [e, map_pow, h2, hB', hσm, bPerm_eq_phi]
  have hcomm_s' : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      actML M ⟨t * z ^ m * t⁻¹, hs'⟩ * rhoSL K g =
        rhoSL K g * actML M ⟨t * z ^ m * t⁻¹, hs'⟩ := by
    intro g
    rw [hφs']
    exact bPerm_comm_rhoSL B' g
  have hL1' : ∀ l ∈ L, ⁅t * z ^ m * t⁻¹, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    commutator_mem_centralizer_of_actML M ⟨t * z ^ m * t⁻¹, hs'⟩ hcomm_s'
  have htC : t⁻¹ ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    Subgroup.inv_mem _ (fsuM_le_normalizer_fsuVM T L I (le_fsuM T L ht))
  have hQ2 : ∀ l' ∈ CFSG.conjugate L t,
      ⁅z ^ m, l'⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro l' hl'
    have hl : t * l' * t⁻¹ ∈ L := mul_mem_L_of_mem_conjugate hl'
    have e : ⁅z ^ m, l'⁆ = t⁻¹ * ⁅t * z ^ m * t⁻¹, t * l' * t⁻¹⁆ * t⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h2_conj_mem_centralizer htC (hL1' _ hl)
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans ((fsuL0_le_fsuM T L).trans (fsuM_le_normalizer_fsuVM T L I))
  have hLQN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (conjugate_le_fsuL0 ht).trans ((fsuL0_le_fsuM T L).trans (fsuM_le_normalizer_fsuVM T L I))
  have hPN : L ≤ Subgroup.normalizer ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) :
      Set G) := fun x hx => h2_mem_normalizer_centralizer (hLN hx)
  have hQN : CFSG.conjugate L t ≤
      Subgroup.normalizer ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
    fun x hx => h2_mem_normalizer_centralizer (hLQN hx)
  have hL0 : ∀ x ∈ L ⊔ CFSG.conjugate L t,
      ⁅z ^ m, x⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    commutator_mem_sup hPN hQN hL1 hQ2
  have hL0' : ∀ l ∈ fsuL0 T L, ⁅z ^ m, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro l hl
    rw [fsuL0_eq_sup_of_fsu h37 h38 hfsu (not_le_normalizer_of_lt hlt) ht htn] at hl
    exact hL0 l hl
  have hC : z ^ m ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    hL3 (z ^ m) hzm_fsuM hL0'
  have hone : actML M ⟨z ^ m, hzm⟩ = 1 := actML_eq_one_of_mem_centralizer M ⟨z ^ m, hzm⟩ hC
  exact ⟨hC, eq_one_of_bPerm_eq_one (hφzm.symm.trans hone)⟩

end CFSG.Quasithin.Vol2.Ch10Reselect
