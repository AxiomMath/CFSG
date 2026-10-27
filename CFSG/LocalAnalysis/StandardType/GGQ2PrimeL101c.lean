module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeDeltaCent
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeX101Conj
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeX101Cent
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeX101Cover
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoT
public import CFSG.Models.Transport

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT conj_mem_T46_iff)

private theorem l101c_centralizer_zpow {s : Equiv.Perm (Fin 693)} {k : ℤ} (hk : k = 1 ∨ k = -1) :
    centralizer ({s ^ k} : Set (Equiv.Perm (Fin 693))) =
      centralizer ({s} : Set (Equiv.Perm (Fin 693))) := by
  rcases hk with rfl | rfl
  · rw [zpow_one]
  · rw [zpow_neg_one]
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    show Commute c s⁻¹ ↔ Commute c s
    exact Commute.inv_right_iff

private theorem l101c_map_conj_inf_centralizer
    {P : Equiv.Perm (Fin 693)} (hP : P ∈ autT) (t : Equiv.Perm (Fin 693)) :
    (T46 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 693)))).map (MulAut.conj P).toMonoidHom =
      T46 ⊓ centralizer ({P * t * P⁻¹} : Set (Equiv.Perm (Fin 693))) := by
  ext d
  constructor
  · intro hd
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hd
    obtain ⟨hcT, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcC' : Commute c t := Subgroup.mem_centralizer_singleton_iff.1 hcC
    refine Subgroup.mem_inf.2 ⟨(conj_mem_T46_iff hP).2 hcT, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcC'.map (MulAut.conj P))
  · intro hd
    obtain ⟨hdT, hdC⟩ := Subgroup.mem_inf.1 hd
    have hdC' : Commute d (P * t * P⁻¹) := Subgroup.mem_centralizer_singleton_iff.1 hdC
    refine Subgroup.mem_map.2 ⟨P⁻¹ * d * P⁻¹⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact (conj_mem_T46_iff (inv_mem hP)).2 hdT
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 := hdC'.map (MulAut.conj P⁻¹)
      have e : (MulAut.conj P⁻¹) (P * t * P⁻¹) = t := by
        show P⁻¹ * (P * t * P⁻¹) * P⁻¹⁻¹ = t
        group
      rw [e] at h1
      exact h1
    · show P * (P⁻¹ * d * P⁻¹⁻¹) * P⁻¹ = d
      group

theorem lemma101cInput_holds :
    Lemma101cInput := by
  unfold Lemma101cInput
  intro G _ _ B Bs x L A κ m n g h hn hg hl
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 h.setting.model
  obtain ⟨ρ, hρ⟩ := exists_rhoTSpec e
  have hzBs : g * x * g⁻¹ ∈ Bs := (mem_normalizer_iff.1 hg x).1 h.coords.x_mem
  have hz : g * x * g⁻¹ ∈ normalizer (L : Set G) := h.setting.Bs_norm hzBs
  obtain ⟨y, k, hk, hzρ⟩ := exists_rhoT_eq_conj_deltaGU h hn hg hl hρ hz
  have hC : LieModel ↥(T46 ⊓ centralizer {ρ ⟨_, hz⟩}) .PSU 5 2 1 := by
    have hP : piGU y ∈ autT := piGU_mem_autT y
    have hρz : ρ ⟨_, hz⟩ = piGU y * piGU deltaGU ^ k * (piGU y)⁻¹ := by
      rw [hzρ, map_mul, map_mul, map_zpow, map_inv]
    have hmap : (T46 ⊓ centralizer {piGU deltaGU}).map (MulAut.conj (piGU y)).toMonoidHom =
        T46 ⊓ centralizer {ρ ⟨_, hz⟩} := by
      rw [hρz, ← l101c_centralizer_zpow (s := piGU deltaGU) hk,
        l101c_map_conj_inf_centralizer hP]
    have E := (Subgroup.equivMapOfInjective (T46 ⊓ centralizer {piGU deltaGU})
      (MulAut.conj (piGU y)).toMonoidHom (MulAut.conj (piGU y)).injective).trans
      (MulEquiv.subgroupCongr hmap)
    exact CFSG.Models.LieModel.of_mulEquiv E lieModel_inf_centralizer_piGU_deltaGU
  obtain ⟨X, hX, hXz', hprod, hXs⟩ := exists_lieModel_inf_centralizer_of_rhoT hρ hz hC
  have hXL : X ≤ L := fun a ha => (Subgroup.mem_inf.1 (hXz' ha)).1
  have hXz : X ≤ centralizer {g * x * g⁻¹} := fun a ha => (Subgroup.mem_inf.1 (hXz' ha)).2
  exact ⟨X, hX, hXz', hprod, le_map_conj_of_lieModel h.setting g hX hXz,
    inf_centralizer_eq_closure h hg hρ hz hk hzρ hXL hXz hXs⟩

end CFSG.GGQ2Prime
