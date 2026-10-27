module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot

open AChief

variable {Γ : Type u} [Group Γ] {R : Subgroup Γ}

structure QSetting (p : ℕ) (R A G : Subgroup Γ) : Prop where
  prime : p.Prime
  solvable : Group.IsSolvable R
  elemAbelian : IsElemAbelian p A
  normalizes : A ≤ Subgroup.normalizer (G : Set Γ)
  coprime : Nat.Coprime p (Nat.card G)
  le_nrm_G : G ≤ nrm R
  le_nrm_A : A ≤ nrm R

variable {p : ℕ} {A G M : Subgroup Γ}

theorem orbitClosure_le_of_normalizes {M G A : Subgroup Γ} (hM : M ≤ G)
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) : orbitClosure M A ≤ G :=
  orbitClosure_le fun a ha => by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAG ha) x).mp (hM hx)

theorem le_normalizer_orbitClosure [Finite Γ] (M A : Subgroup Γ) :
    A ≤ Subgroup.normalizer (orbitClosure M A : Set Γ) := by
  intro b hb
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : orbitClosure M A ≤ (orbitClosure M A).comap (MulAut.conj b).toMonoidHom :=
    orbitClosure_le fun a ha => by
      rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
      have hcomp : (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (b * a)).toMonoidHom := by
        ext x
        simp [mul_assoc]
      rw [hcomp]
      exact map_conj_le_orbitClosure M (mul_mem hb ha)
  exact hle hx

theorem qimg_orbitClosure {M A : Subgroup Γ} (hM : M ≤ nrm R) (hA : A ≤ nrm R) :
    qimg R (orbitClosure M A) = orbitClosure (qimg R M) (qimg R A) := by
  have hconj : ∀ a ∈ A, M.map (MulAut.conj a).toMonoidHom ≤ nrm R := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (hA ha) (hM hx)) (inv_mem (hA ha))
  apply le_antisymm
  · rw [qimg_le_iff (orbitClosure_le hconj)]
    refine orbitClosure_le fun a ha => ?_
    rw [← qimg_le_iff (hconj a ha), qimg_map_conj (hA ha)]
    exact map_conj_le_orbitClosure _ ((mem_qimg_iff R A _).mpr ⟨⟨a, hA ha⟩, ha, rfl⟩)
  · refine orbitClosure_le fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := (mem_qimg_iff R A b).mp hb
    rw [← qimg_map_conj a.2]
    exact qimg_mono (map_conj_le_orbitClosure M ha)

variable [Finite Γ]

theorem qimg_smear (h : QSetting p R A G) (hM : M ≤ G) :
    qimg R (smear M A) = smear (qimg R M) (qimg R A) := by
  have hOG := orbitClosure_le_of_normalizes hM h.normalizes
  have hcop : Nat.Coprime p (Nat.card (orbitClosure M A)) :=
    h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hOG)
  unfold smear
  rw [qimg_inf_centralizer h.prime h.elemAbelian (le_normalizer_orbitClosure M A) h.le_nrm_A
    (hOG.trans h.le_nrm_G) hcop, qimg_orbitClosure (hM.trans h.le_nrm_G) h.le_nrm_A]

omit [Finite Γ] in
theorem smear_le_nrm (h : QSetting p R A G) (hM : M ≤ G) : smear M A ≤ nrm R :=
  (smear_le_orbitClosure M A).trans
    ((orbitClosure_le_of_normalizes hM h.normalizes).trans h.le_nrm_G)

theorem isSolvable_smear_qimg_iff (h : QSetting p R A G) (hM : M ≤ G) :
    Group.IsSolvable (smear (qimg R M) (qimg R A)) ↔ Group.IsSolvable (smear M A) := by
  rw [← qimg_smear h hM]
  exact isSolvable_qimg_iff h.solvable (smear_le_nrm h hM)

theorem mem_mcalA_qimg_iff (h : QSetting p R A G) (hM : M ∈ mcal G) :
    qimg R M ∈ mcalA (qimg R G) (qimg R A) ↔ M ∈ mcalA G A := by
  show (qimg R M ∈ mcal (qimg R G) ∧ ¬ Group.IsSolvable (smear (qimg R M) (qimg R A))) ↔
    (M ∈ mcal G ∧ ¬ Group.IsSolvable (smear M A))
  rw [qimg_mem_mcal_iff h.solvable h.le_nrm_G hM.1 hM.2.1, isSolvable_smear_qimg_iff h hM.1]

theorem bijOn_mcalA (h : QSetting p R A G) :
    Set.BijOn (qimg R) (mcalA G A) (mcalA (qimg R G) (qimg R A)) := by
  refine ⟨fun M hM => (mem_mcalA_qimg_iff h hM.1).mpr hM,
    (injOn_mcal h.solvable h.le_nrm_G).mono (mcalA_subset G A), fun M' hM' => ?_⟩
  obtain ⟨M, hM, rfl⟩ := (bijOn_mcal h.solvable h.le_nrm_G).surjOn hM'.1
  exact ⟨M, (mem_mcalA_qimg_iff h hM).mp hM', rfl⟩

theorem kUp_qimg (h : QSetting p R A G) : kUp (qimg R G) (qimg R A) = qimg R (kUp G A) := by
  unfold kUp
  rw [← (bijOn_mcalA h).image_eq, iSup_image]
  exact (qimg_biSup fun M hM => ((mcalA_subset G A hM).1).trans h.le_nrm_G).symm

omit [Finite Γ] in
theorem kUp_le_nrm (h : QSetting p R A G) : kUp G A ≤ nrm R := (kUp_le G A).trans h.le_nrm_G

theorem kDown_qimg (h : QSetting p R A G) (hRG : R ≤ sol G) :
    kDown (qimg R G) (qimg R A) = qimg R (kDown G A) := by
  have hsol : sol (qimg R G) = qimg R (sol G) := sol_qimg h.solvable h.le_nrm_G
  have hkUp := kUp_qimg h
  have hcomm : ∀ y k : ↥(nrm R), ⁅qmap R y, qmap R k⁆ = qmap R ⁅y, k⁆ := fun y k =>
    (map_commutatorElement _ _ _).symm
  ext z
  constructor
  · intro hz
    obtain ⟨hzG, hz⟩ := mem_kDown_iff.mp hz
    obtain ⟨y, hyG, rfl⟩ := (mem_qimg_iff R G z).mp hzG
    refine (mem_qimg_iff R _ _).mpr ⟨y, mem_kDown_iff.mpr ⟨hyG, fun k hk => ?_⟩, rfl⟩
    have hkN : k ∈ nrm R := kUp_le_nrm h hk
    have hkbar : qmap R ⟨k, hkN⟩ ∈ kUp (qimg R G) (qimg R A) := by
      rw [hkUp]
      exact (mem_qimg_iff R _ _).mpr ⟨⟨k, hkN⟩, hk, rfl⟩
    have h1 := hz _ hkbar
    rw [hsol, hcomm] at h1
    have h2 : ((⁅y, ⟨k, hkN⟩⁆ : ↥(nrm R)) : Γ) ∈ qpre R (qimg R (sol G)) :=
      mem_qpre_iff.mpr ⟨(⁅y, ⟨k, hkN⟩⁆ : ↥(nrm R)).2, h1⟩
    rw [qpre_qimg ((sol_le G).trans h.le_nrm_G), sup_eq_left.mpr hRG] at h2
    exact h2
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R _ z).mp hz
    obtain ⟨hyG, hy'⟩ := mem_kDown_iff.mp hy
    refine mem_kDown_iff.mpr ⟨(mem_qimg_iff R G _).mpr ⟨y, hyG, rfl⟩, fun k hk => ?_⟩
    rw [hkUp] at hk
    obtain ⟨k', hk', rfl⟩ := (mem_qimg_iff R _ _).mp hk
    rw [hsol, hcomm]
    exact (mem_qimg_iff R _ _).mpr ⟨⁅y, k'⁆, hy' k' hk', rfl⟩

theorem kDown_eq_qpre (h : QSetting p R A G) (hRG : R ≤ sol G) :
    kDown G A = qpre R (kDown (qimg R G) (qimg R A)) := by
  rw [kDown_qimg h hRG, qpre_qimg ((kDown_le G A).trans h.le_nrm_G),
    sup_eq_left.mpr (hRG.trans (sol_le_kDown G A))]

theorem le_kDown_of_qimg_le (h : QSetting p R A G) (hRG : R ≤ sol G) {X : Subgroup Γ}
    (hX : X ≤ G) (hle : qimg R X ≤ kDown (qimg R G) (qimg R A)) : X ≤ kDown G A := by
  rw [kDown_eq_qpre h hRG]
  exact (qimg_le_iff (hX.trans h.le_nrm_G)).mp hle

omit [Finite Γ] in
theorem QSetting.inf_eq_bot (h : QSetting p R A G) (hRG : R ≤ G) : A ⊓ R = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hxA, hxR⟩ := Subgroup.mem_inf.mp hx
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (h.elemAbelian.2 x hxA)
  have h2 : orderOf x ∣ Nat.card G := Subgroup.orderOf_dvd_natCard G (hRG hxR)
  have h3 : orderOf x ∣ Nat.gcd p (Nat.card G) := Nat.dvd_gcd h1 h2
  rw [h.coprime.gcd_eq_one] at h3
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

omit [Finite Γ] in
theorem QSetting.card_qimg (h : QSetting p R A G) (hRG : R ≤ G) :
    Nat.card (qimg R A) = Nat.card A := by
  have hker : (qres R A h.le_nrm_A).ker = ⊥ := by
    rw [ker_qres, eq_bot_iff]
    intro x hx
    have hxA : (x : Γ) ∈ A ⊓ R := Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [h.inf_eq_bot hRG, Subgroup.mem_bot] at hxA
    exact Subgroup.mem_bot.mpr (Subtype.ext hxA)
  have hinj : Function.Injective (qres R A h.le_nrm_A) := (MonoidHom.ker_eq_bot_iff _).mp hker
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, qres_surjective h.le_nrm_A⟩)).symm

omit [Finite Γ] in
theorem QSetting.qmap_ne_one (h : QSetting p R A G) (hRG : R ≤ G) {a : Γ} (ha : a ∈ A)
    (ha1 : a ≠ 1) : qmap R ⟨a, h.le_nrm_A ha⟩ ≠ 1 := by
  intro h1
  have haR : a ∈ R := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have : a ∈ A ⊓ R := Subgroup.mem_inf.mpr ⟨ha, haR⟩
  rw [h.inf_eq_bot hRG, Subgroup.mem_bot] at this
  exact ha1 this

omit [Finite Γ] in
theorem QSetting.mono_left (h : QSetting p R A G) {A' : Subgroup Γ} (hA' : A' ≤ A) :
    QSetting p R A' G where
  prime := h.prime
  solvable := h.solvable
  elemAbelian := CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.elemAbelian hA'
  normalizes := hA'.trans h.normalizes
  coprime := h.coprime
  le_nrm_G := h.le_nrm_G
  le_nrm_A := hA'.trans h.le_nrm_A

theorem le_normalizer_kUp_iff (h : QSetting p R A G) {X : Subgroup Γ} (hX : X ≤ G) :
    qimg R X ≤ Subgroup.normalizer (kUp (qimg R G) (qimg R A) : Set (QG R)) ↔
      X ≤ Subgroup.normalizer (kUp G A : Set Γ) := by
  rw [kUp_qimg h]
  by_cases hne : (mcalA G A).Nonempty
  · obtain ⟨M, hM⟩ := hne
    have hRM : G ⊓ R ≤ kUp G A :=
      (inf_le_sol h.solvable h.le_nrm_G).trans (hM.1.2.1.trans (le_iSup₂_of_le M hM le_rfl))
    exact qimg_le_normalizer_iff (kUp_le G A) hRM h.le_nrm_G hX
  · have hbot : kUp G A = ⊥ := by
      unfold kUp
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
    have h1 : Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    have h2 : Subgroup.normalizer ((⊥ : Subgroup (QG R)) : Set (QG R)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [hbot, qimg_bot, h1, h2]
    exact iff_of_true le_top le_top

theorem exists_mem_kUp_of_qimg (h : QSetting p R A G) (hRG : R ≤ sol G) {X : Subgroup Γ}
    (hX : X ≤ G)
    (hbar : ∀ z ∈ qimg R X, ∃ w ∈ kUp (qimg R G) (qimg R A),
      w⁻¹ * z ∈ kDown (qimg R G) (qimg R A)) :
    ∀ x ∈ X, ∃ y ∈ kUp G A, y⁻¹ * x ∈ kDown G A := by
  intro x hx
  have hxN : x ∈ nrm R := h.le_nrm_G (hX hx)
  obtain ⟨w, hw, hwz⟩ :=
    hbar (qmap R ⟨x, hxN⟩) ((mem_qimg_iff R X _).mpr ⟨⟨x, hxN⟩, hx, rfl⟩)
  rw [kUp_qimg h] at hw
  obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R _ w).mp hw
  refine ⟨y, hy, ?_⟩
  rw [kDown_eq_qpre h hRG]
  refine mem_qpre_iff.mpr ⟨mul_mem (inv_mem y.2) hxN, ?_⟩
  have hyx : (⟨(y : Γ)⁻¹ * x, mul_mem (inv_mem y.2) hxN⟩ : ↥(nrm R)) = y⁻¹ * ⟨x, hxN⟩ := rfl
  rw [hyx, map_mul, map_inv]
  exact hwz

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
