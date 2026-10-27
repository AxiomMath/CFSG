module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML
public import CFSG.Quasithin.Vol2.Ch10Reselect.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

private theorem ml2_pCoreOf_le (p : ℕ) {H : Subgroup G} : pCoreOf p H ≤ H := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem conjugate_le_fsuML (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L t ≤ fsuML T L := by
  have hN : CFSG.conjugate L t ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((commutator_conjugate_le_of_fsu h37 hfsu ht htn).trans
        (inf_le_left.trans (ml2_pCoreOf_le 2)))
  exact le_inf ((conjugate_le_fsuL0 ht).trans (fsuL0_le_fsuM T L)) hN

theorem fsuL0_le_fsuML (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) :
    fsuL0 T L ≤ fsuML T L := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  rw [fsuL0_eq_sup_of_fsu h37 h38 hfsu (not_le_normalizer_of_lt hlt) ht htn]
  exact sup_le L_le_fsuML (conjugate_le_fsuML h37 h38 hfsu hlt ht htn)

theorem actML_eq_one_of_mem_conjugate
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) (hA : Concl326A T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) (M : RModel T L I K) {b : G}
    (hb : b ∈ CFSG.conjugate L t) :
    actML M ⟨b, conjugate_le_fsuML h37 h38 hfsu hlt ht htn hb⟩ = 1 := by
  have hU : fsuUL T L I ≤ Subgroup.centralizer ((CFSG.conjugate L t : Subgroup G) : Set G) :=
    (hA t ht htn).2.2
  change UModel.actHom M
    ⟨b, mem_acting_of_mem_fsuML (conjugate_le_fsuML h37 h38 hfsu hlt ht htn hb)⟩ = 1
  rw [UModel.actHom_eq_one_iff]
  intro u hu
  have hcomm : b * u = u * b := Subgroup.mem_centralizer_iff.mp (hU hu) b hb
  show b * u * b⁻¹ * u⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)
  rw [hcomm]
  have e : u * b * b⁻¹ * u⁻¹ = 1 := by group
  rw [e]
  exact Subgroup.one_mem _

theorem exists_rho_of_mem_fsuL0 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) (M : RModel T L I K) {x : G} (hx : x ∈ fsuL0 T L) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
      actML M ⟨x, fsuL0_le_fsuML h37 h38 hfsu hlt hx⟩ = rhoSL K g := by
  have hnn := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  let S : Subgroup G :=
    { carrier := {y | ∃ h : y ∈ fsuL0 T L, ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
        actML M ⟨y, fsuL0_le_fsuML h37 h38 hfsu hlt h⟩ = rhoSL K g}
      one_mem' := ⟨(fsuL0 T L).one_mem, 1, by
        show actML M 1 = rhoSL K 1
        rw [map_one, map_one]⟩
      mul_mem' := by
        rintro a b ⟨ha, g, hga⟩ ⟨hb, g', hgb⟩
        refine ⟨(fsuL0 T L).mul_mem ha hb, g * g', ?_⟩
        show actML M (⟨a, fsuL0_le_fsuML h37 h38 hfsu hlt ha⟩ *
          ⟨b, fsuL0_le_fsuML h37 h38 hfsu hlt hb⟩) = rhoSL K (g * g')
        rw [map_mul, hga, hgb, map_mul]
      inv_mem' := by
        rintro a ⟨ha, g, hga⟩
        refine ⟨(fsuL0 T L).inv_mem ha, g⁻¹, ?_⟩
        show actML M ((⟨a, fsuL0_le_fsuML h37 h38 hfsu hlt ha⟩ :
          ↥(fsuML T L))⁻¹) = rhoSL K g⁻¹
        rw [map_inv, hga, map_inv] }
  have hS : fsuL0 T L ≤ S := by
    rw [fsuL0_eq_sup_of_fsu h37 h38 hfsu hnn ht htn]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · show ∃ h : y ∈ fsuL0 T L, ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
        actML M ⟨y, fsuL0_le_fsuML h37 h38 hfsu hlt h⟩ = rhoSL K g
      exact ⟨le_fsuL0 T L hy, M.γ ⟨y, hy⟩, actML_of_mem_L M ⟨y, hy⟩⟩
    · show ∃ h : y ∈ fsuL0 T L, ∃ g : Matrix.SpecialLinearGroup (Fin 2) K,
        actML M ⟨y, fsuL0_le_fsuML h37 h38 hfsu hlt h⟩ = rhoSL K g
      refine ⟨conjugate_le_fsuL0 ht hy, 1, ?_⟩
      rw [map_one]
      exact actML_eq_one_of_mem_conjugate h37 h38 hfsu hlt hA ht htn M hy
  obtain ⟨_, g, hg⟩ := hS hx
  exact ⟨g, hg⟩

theorem conj_mem_fsuML (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) {m s : G}
    (hm : m ∈ fsuM T L) (hs : s ∈ fsuML T L) : m * s * m⁻¹ ∈ fsuML T L := by
  have hnn := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  have hc := conjugate_eq_or_of_fsu h37 h38 hfsu hnn ht htn hm
  have key : ∀ s' ∈ fsuML T L, ∀ x ∈ L, m * s' * m⁻¹ * x * (m * s' * m⁻¹)⁻¹ ∈ L := by
    intro s' hs' x hx
    have hs'M : s' ∈ fsuM T L := (Subgroup.mem_inf.mp hs').1
    have hs'N : s' ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_inf.mp hs').2
    have hs'L' := mem_normalizer_conjugate_of_mem_normalizer h37 h38 hfsu hlt ht htn hs'M hs'N
    have hB : ∀ y ∈ CFSG.conjugate L m, s' * y * s'⁻¹ ∈ CFSG.conjugate L m := by
      intro y hy
      rcases hc with h | h
      · rw [h] at hy ⊢
        exact (Subgroup.mem_normalizer_iff.mp hs'N y).mp hy
      · rw [h] at hy ⊢
        exact (Subgroup.mem_normalizer_iff.mp hs'L' y).mp hy
    have hA' : m⁻¹ * x * m ∈ CFSG.conjugate L m := by
      rw [mem_conjugate_iff]
      have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
      rw [e]
      exact hx
    have hz := mem_conjugate_iff.mp (hB _ hA')
    have e : m * (s' * (m⁻¹ * x * m) * s'⁻¹) * m⁻¹ = m * s' * m⁻¹ * x * (m * s' * m⁻¹)⁻¹ := by
      group
    rwa [e] at hz
  refine Subgroup.mem_inf.mpr ⟨(fsuM T L).mul_mem ((fsuM T L).mul_mem hm
    (Subgroup.mem_inf.mp hs).1) ((fsuM T L).inv_mem hm), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key s hs x hx
  · intro hx
    have h2 := key s⁻¹ ((fsuML T L).inv_mem hs) _ hx
    have e2 : m * s⁻¹ * m⁻¹ * (m * s * m⁻¹ * x * (m * s * m⁻¹)⁻¹) * (m * s⁻¹ * m⁻¹)⁻¹ = x := by
      group
    rwa [e2] at h2

theorem mul_mem_conjugate_of_mem (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {a : G} (ha : a ∈ L) :
    t * a * t⁻¹ ∈ CFSG.conjugate L t := by
  have htt := mul_self_mem_normalizer_of_fsu h37 h38 hfsu (not_le_normalizer_of_lt hlt) ht htn
  rw [mem_conjugate_iff]
  have e : t * (t * a * t⁻¹) * t⁻¹ = t * t * a * (t * t)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp htt a).mp ha

theorem mul_mem_L_of_mem_conjugate {t b : G} (hb : b ∈ CFSG.conjugate L t) : t * b * t⁻¹ ∈ L := by
  exact mem_conjugate_iff.mp hb

end CFSG.Quasithin.Vol2.Ch10Reselect
