module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tc
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem isSylowTwoOf_of_le' {T M : Subgroup Y} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M) :
    IsSylowTwoOf T M := by
  refine ⟨hTM, hT.2.1, fun h2 => hT.2.2 ?_⟩
  change 2 ∣ T.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact h2.trans (Subgroup.relIndex_dvd_index_of_le hTM)

omit [Finite Y] in
theorem isSylowTwoOf_map_of_surjective {B : Type} [Group B] {f : Y →* B}
    (hf : Function.Surjective f) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map f) ⊤ := by
  obtain ⟨-, hS2, hSi⟩ := hS
  have hmapS : S.map f = (S ⊔ f.ker).map f := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  refine ⟨le_top, hS2.map f, ?_⟩
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hSi
  rw [show ((S.map f).subgroupOf ⊤).index = (S.map f).index from
    Subgroup.relIndex_top_right _, hmapS, Subgroup.index_map_eq _ hf le_sup_right]
  exact fun h => hSi (h.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem normalizer_perfectCore_eq (hq : CFSG.IsQuasisimple Y) {P : Subgroup Y}
    (hP : IsMaxParabolic2 ⊤ P) (hne : perfectCore P ≠ ⊤) (hbot : perfectCore P ≠ ⊥) :
    Subgroup.normalizer (perfectCore P : Set Y) = P := by
  obtain ⟨⟨-, S, hS, hSP⟩, -, hmax⟩ := hP
  have hPN : P ≤ Subgroup.normalizer (perfectCore P : Set Y) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P)
  have hpar : IsParabolic2 ⊤ (Subgroup.normalizer (perfectCore P : Set Y)) :=
    ⟨le_top, S, hS, hSP.trans hPN⟩
  refine hmax _ hpar (fun htop => ?_) hPN
  have hn : (perfectCore P).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with h | h
  · exact hne h
  · apply hbot
    rw [← perfectCore_perfect P, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b _
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp (h ha) b).symm)]
    exact Subgroup.one_mem _

theorem normalizer_sylow_le {P : Subgroup Y} (hP : IsParabolic2 ⊤ P) {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hTP : T ≤ P) : Subgroup.normalizer (T : Set Y) ≤ P := by
  obtain ⟨-, S, hS, hSP⟩ := hP
  have hSP' : S ≤ P := fun s hs => hSP ⟨Subgroup.mem_top s, Subgroup.le_normalizer hs⟩
  obtain ⟨h, hhP, rfl⟩ :=
    (isSylowTwoOf_of_le' hS hSP').exists_conj (isSylowTwoOf_of_le' hT hTP)
  intro x hx
  have hmem : ∀ u : Y, u ∈ S.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * u * h ∈ S := by
    intro u
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [mul_assoc] using hs
    · intro hu
      exact ⟨h⁻¹ * u * h, hu, by simp [mul_assoc]⟩
  have hy : h⁻¹ * x * h ∈ Subgroup.normalizer (S : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have h1 := (Subgroup.mem_normalizer_iff.mp hx) (h * s * h⁻¹)
    rw [hmem, hmem] at h1
    have e1 : h⁻¹ * (h * s * h⁻¹) * h = s := by group
    have e2 : h⁻¹ * (x * (h * s * h⁻¹) * x⁻¹) * h = h⁻¹ * x * h * s * (h⁻¹ * x * h)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have := P.mul_mem (P.mul_mem hhP (hSP ⟨Subgroup.mem_top _, hy⟩)) (P.inv_mem hhP)
  simpa [mul_assoc] using this

theorem parabolic_transfer {B : Type} [Group B] [Finite B] {f : Y →* B}
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card f.ker))
    (hq : CFSG.IsQuasisimple Y) {P : Subgroup Y} (hP : IsMaxParabolic2 ⊤ P)
    (hne : perfectCore P ≠ ⊤) (hbot : perfectCore P ≠ ⊥) {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ Subgroup.normalizer (perfectCore P : Set Y)) :
    IsMaxParabolic2 ⊤ (P.map f) ∧ perfectCore (P.map f) = (perfectCore P).map f ∧
      IsSylowTwoOf (T.map f) ⊤ ∧
        Subgroup.normalizer ((T.map f : Subgroup B) : Set B) ≤ P.map f := by
  have hTP : T ≤ P := hTN.trans (normalizer_perfectCore_eq hq hP hne hbot).le
  have hNT := normalizer_sylow_le hP.1 hT hTP
  refine ⟨isMaxParabolic2_map hf hker hodd hP, (map_perfectCore f P).symm,
    isSylowTwoOf_map_of_surjective hf hT, fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := hf x
  exact ⟨a, hNT (mem_normalizer_of_map hker hodd hT.2.1 hx), rfl⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
