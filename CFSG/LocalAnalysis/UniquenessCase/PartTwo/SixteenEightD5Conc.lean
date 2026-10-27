module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Conj
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

theorem s16e_d5_conc_span (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) (i : Fin 4) :
    (⨆ X ∈ conjSubs A (commSub ⊤ (Subgroup.zpowers (a i))), X) = ⊤ := by
  rw [s16e_d5_conj_blocks hfr hLn htr hfam i, iSup_range]
  exact hfr.Z_top

theorem s16e_d5_conc_comm (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W))) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) (i : Fin 4) :
    ∀ g ∈ A, g ∉ Subgroup.normalizer ((Subgroup.zpowers (a i) : Subgroup (MulAut W)) :
        Set (MulAut W)) →
      ⁅Subgroup.zpowers (a i), (Subgroup.zpowers (a i)).map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        commSub (commSub ⊤ (Subgroup.zpowers (a i)))
          ((Subgroup.zpowers (a i)).map (MulAut.conj g).toMonoidHom) = ⊥ := by
  intro g hgA hgn
  obtain ⟨j, hj⟩ := hfr.perm (hLn g hgA) i
  have hconj : (Subgroup.zpowers (a i)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (a j) :=
    s16e_d5_conj_zpowers hfr hLn hfam hgA hj
  have hji : j ≠ i := by
    rintro rfl
    exact hgn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using hconj))
  have h41 : Commute (a i) (a j) :=
    s16e_d5_cent_comm hfr (hfam.mem_cent i) (hfam.mem_cent j)
  refine ⟨?_, ?_⟩
  · rw [hconj, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (h41.zpow_zpow m n).eq.symm
  · rw [hconj, s16e_d5_commSub_zpowers hfr (hfam.mem_cent i) (hfam.off i) (hfam.ne_one i),
      commSub_eq_bot_iff]
    intro z hz
    rw [mem_fixV]
    intro y hy
    have hle : Subgroup.zpowers (a j) ≤ fixingSubgroup (MulAut W) (Z i : Set W) :=
      Subgroup.zpowers_le.mpr (by
        rw [mem_fixingSubgroup_iff]
        intro z' hz'
        simpa [MulAut.smul_def] using hfam.off j i hji.symm z' hz')
    have hy' := hle hy
    rw [mem_fixingSubgroup_iff] at hy'
    simpa [MulAut.smul_def] using hy' z hz

theorem s16e_d5_zpowers_le_pCore (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W))) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) (i : Fin 4) :
    Subgroup.zpowers (a i) ≤ pCoreOf 3 A := by
  let B : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (L : Set (MulAut W))
  have hconj_mem : ∀ g ∈ A, ∀ x ∈ B, g * x * g⁻¹ ∈ B := by
    intro g hgA x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hgA hxA) (A.inv_mem hgA), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hgy : g⁻¹ * y * g ∈ L :=
      ((Subgroup.mem_normalizer_iff''.mp (hLn g hgA)) y).mp hy
    have hcomm : (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g) :=
      (Subgroup.mem_centralizer_iff.mp hxC) (g⁻¹ * y * g) hgy
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * x * g⁻¹) * y := by group
  have hBnorm : (B.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro g hgA
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj_mem g hgA x hx
    · intro hx
      have hx' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ B :=
        hconj_mem g⁻¹ (A.inv_mem hgA) (g * x * g⁻¹) hx
      rw [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at hx'
      exact hx'
  have hBp : IsPGroup 3 ↥B := by
    refine IsPGroup.of_card_dvd_pow (n := 4) ?_
    have h1 : Nat.card ↥B ∣ Nat.card ↥(Subgroup.centralizer (L : Set (MulAut W))) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥(Subgroup.centralizer (L : Set (MulAut W))) ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = 81 by norm_num]
      exact s16e_d5_card_cent_dvd hfr
    exact h1.trans h2
  have hleB : Subgroup.zpowers (a i) ≤ B :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hfam.mem_A i, hfam.mem_cent i⟩)
  exact hleB.trans
    (CFSG.LocalAnalysis.UniquenessCase.UCK.le_pCoreOf_of_normal inf_le_left hBnorm hBp)

theorem s16e_d5_conc_133 (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) {t : MulAut W} (i : Fin 4) (hi : a i * t ≠ t * a i) :
    Conc4_133 A t (Subgroup.zpowers (a i)) := by
  refine ⟨3, Nat.prime_three, s16e_d5_zpowers_le_pCore hfr hLn hfam i, ?_, ?_, ?_⟩
  · rintro hbot
    have hle : Subgroup.zpowers (a i) ≤
        Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (MulAut W)) : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hcomm : t * a i = a i * t :=
      (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_zpowers (a i)))) t
        (Subgroup.mem_zpowers t)
    exact hi hcomm.symm
  · rw [s16e_d5_conj_blocks hfr hLn htr hfam i]
    exact hfr.Z_indep.sSupIndep_range
  · left
    refine ⟨⟨Subgroup.isCyclic_zpowers (a i), ?_⟩, ?_⟩
    · rw [Nat.card_zpowers,
        s16e_d5_orderOf_cent hfr (hfam.mem_cent i) (hfam.ne_one i)]
    · left
      rw [s16e_d5_commSub_zpowers hfr (hfam.mem_cent i) (hfam.off i) (hfam.ne_one i)]
      exact hfr.Z_rk i

theorem s16e_d5_conc (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j) {a : Fin 4 → MulAut W}
    (hfam : s16e_d5_CoordFam A L Z a) {t : MulAut W} (i : Fin 4) (hi : a i * t ≠ t * a i) :
    Conc4_136W A t (Subgroup.zpowers (a i)) :=
  ⟨s16e_d5_conc_span hfr hLn htr hfam i, s16e_d5_conc_comm hfr hLn hfam i,
    Or.inl (s16e_d5_conc_133 hfr hLn htr hfam i hi)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
