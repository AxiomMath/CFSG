module

public import CFSG.Quasithin.Vol2.Ch10SecABasicL0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjugate_commutator (A B : Subgroup G) (s : G) :
    CFSG.conjugate ⁅A, B⁆ s = ⁅CFSG.conjugate A s, CFSG.conjugate B s⁆ :=
  Subgroup.map_commutator A B _

theorem le_normalizer_commutator {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) :=
  fun x hx => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)]

theorem commutator_sup_left_of_le {N H K X : Subgroup G} (hN : N ≤ X) (hH : H ≤ X) (hK : K ≤ X)
    (hX : X ≤ Subgroup.normalizer (N : Set G)) : ⁅N, H ⊔ K⁆ = ⁅N, H⁆ ⊔ ⁅N, K⁆ := by
  have : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hX
  have h := congrArg (Subgroup.map X.subtype)
    (Subgroup.commutator_sup_left (N.subgroupOf X) (H.subgroupOf X) (K.subgroupOf X))
  simpa only [Subgroup.map_commutator, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hN, inf_eq_left.mpr hH, inf_eq_left.mpr hK] using h

variable {T L I : Subgroup G}

theorem le_sup_of_fsu [Finite G] (hfsu : FSU G T L I) : I ≤ L ⊔ T :=
  hfsu.irrPlus.1.trans (Subgroup.map_subtype_le _)

theorem fsuV_le_sup [Finite G] (hfsu : FSU G T L I) : fsuV T I ≤ L ⊔ T :=
  conjClosure_le fun _ ht _ hi =>
    (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (le_sup_of_fsu hfsu hi))
      ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))

theorem fsuV_le_fsuM [Finite G] (hfsu : FSU G T L I) : fsuV T I ≤ fsuM T L :=
  (fsuV_le_sup hfsu).trans (sup_le_fsuM T L)

theorem fsuVM_le_fsuM [Finite G] (hfsu : FSU G T L I) : fsuVM T L I ≤ fsuM T L :=
  conjClosure_le fun _ hm _ hv =>
    (fsuM T L).mul_mem ((fsuM T L).mul_mem hm (fsuV_le_fsuM hfsu hv)) ((fsuM T L).inv_mem hm)

theorem fsuM_le_normalizer_fsuVM (T L I : Subgroup G) :
    fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  le_normalizer_conjClosure _ _

theorem le_normalizer_fsuVM (T L I : Subgroup G) : T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  (le_fsuM T L).trans (fsuM_le_normalizer_fsuVM T L I)

theorem fsuL0_le_normalizer_fsuVM (T L I : Subgroup G) :
    fsuL0 T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
  (fsuL0_le_fsuM T L).trans (fsuM_le_normalizer_fsuVM T L I)

theorem fsuV_le_fsuVM (T L I : Subgroup G) : fsuV T I ≤ fsuVM T L I :=
  le_conjClosure _ _

theorem le_fsuVM (T L I : Subgroup G) : I ≤ fsuVM T L I :=
  (le_conjClosure I T).trans (fsuV_le_fsuVM T L I)

theorem conjugate_fsuVM {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate (fsuVM T L I) s = fsuVM T L I :=
  conjugate_eq_self_iff.mpr (fsuM_le_normalizer_fsuVM T L I hs)

theorem conjugate_commutator_fsuVM {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate ⁅fsuVM T L I, L⁆ s = ⁅fsuVM T L I, CFSG.conjugate L s⁆ := by
  rw [conjugate_commutator, conjugate_fsuVM hs]

variable [Finite G]

theorem isElemAbelian_fsuVM (hyp : Ch10.Hyp10 G T L I) : IsElemAbelian 2 (fsuVM T L I) := by
  obtain ⟨_, h, -⟩ := hyp.three
  exact h

theorem isPGroup_fsuVM (hyp : Ch10.Hyp10 G T L I) : IsPGroup 2 (fsuVM T L I) :=
  fun x => ⟨1, by simpa using Subtype.ext ((isElemAbelian_fsuVM hyp).2 x x.2)⟩

theorem fsuVM_le_T (hyp : Ch10.Hyp10 G T L I) : fsuVM T L I ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : ((fsuVM T L I).subgroupOf (fsuM T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fsuVM_le_fsuM hyp.fsu)).mpr
      (fsuM_le_normalizer_fsuVM T L I)
  have hp : IsPGroup 2 ((fsuVM T L I).subgroupOf (fsuM T L)) :=
    (isPGroup_fsuVM hyp).comap_of_injective _ (Subgroup.subtype_injective _)
  have hT : IsPGroup 2 (T.subgroupOf (fsuM T L)) :=
    hyp.fsu.sylow.1.comap_of_injective _ (Subgroup.subtype_injective _)
  have hle := hp.le_sylow_of_normal (hT.toSylow (not_two_dvd_index_of_le hyp.fsu.sylow
    (le_fsuM T L)))
  intro v hv
  have h1 := hle (show (⟨v, fsuVM_le_fsuM hyp.fsu hv⟩ : ↥(fsuM T L)) ∈
    (fsuVM T L I).subgroupOf (fsuM T L) from hv)
  rw [IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem fsuVM_eq_commutator (hfsu : FSU G T L I) :
    fsuVM T L I = ⁅fsuVM T L I, fsuL0 T L⁆ := by
  have hN : fsuM T L ≤
      Subgroup.normalizer ((⁅fsuVM T L I, fsuL0 T L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator (fsuM_le_normalizer_fsuVM T L I) le_rfl
  have hI : I ≤ ⁅fsuVM T L I, fsuL0 T L⁆ := by
    calc I = ⁅I, fsuL0 T L⁆ := hfsu.irrPlus.2.2.2.1.symm
      _ ≤ ⁅fsuVM T L I, fsuL0 T L⁆ := Subgroup.commutator_mono (le_fsuVM T L I) le_rfl
  refine le_antisymm (conjClosure_le fun m hm x hx => ?_) ?_
  · have hx' : x ∈ ⁅fsuVM T L I, fsuL0 T L⁆ :=
      conjClosure_le (fun s hs i hi =>
        (Subgroup.mem_normalizer_iff.mp (hN (le_fsuM T L hs)) i).mp (hI hi)) hx
    exact (Subgroup.mem_normalizer_iff.mp (hN hm) x).mp hx'
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (fsuL0_le_normalizer_fsuVM T L I)

theorem fsuVM_eq_sup (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuVM T L I = ⁅fsuVM T L I, L⁆ ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  conv_lhs => rw [fsuVM_eq_commutator hyp.fsu, fsuL0_eq_sup h37 h38 hyp ht htn]
  exact commutator_sup_left_of_le (fsuVM_le_fsuM hyp.fsu)
    ((le_fsuL0 T L).trans (fsuL0_le_fsuM T L))
    ((conjugate_le_fsuL0 ht).trans (fsuL0_le_fsuM T L)) (fsuM_le_normalizer_fsuVM T L I)

theorem commutator_fsuVM_ne_bot (hfsu : FSU G T L I) : ⁅fsuVM T L I, L⁆ ≠ ⊥ := by
  intro h
  have hC : fsuL0 T L ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine conjClosure_le fun s hs l hl => ?_
    have hs' : s⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem (le_fsuM T L hs)
    have hcomm : ⁅fsuVM T L I, CFSG.conjugate L s⁻¹⁆ = ⊥ := by
      rw [← conjugate_commutator_fsuVM hs', h]
      ext x
      simp [CFSG.conjugate]
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((Subgroup.commutator_comm _ _).trans hcomm)
    apply hle
    rw [mem_conjugate_iff]
    simpa [mul_assoc] using hl
  have hV := fsuVM_eq_commutator hfsu
  rw [(Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((Subgroup.le_centralizer_iff).mp hC))] at hV
  exact hfsu.irrPlus.2.1 (le_bot_iff.mp (hV ▸ le_fsuVM T L I))

theorem fsuVM_ne_bot (hfsu : FSU G T L I) : fsuVM T L I ≠ ⊥ :=
  fun h => hfsu.irrPlus.2.1 (le_bot_iff.mp (h ▸ le_fsuVM T L I))

theorem normalizer_fsuVM_eq (hyp : Ch10.Hyp10 G T L I)
    (hmax : quasithinIsMaxTwoLocal (fsuM T L)) :
    Subgroup.normalizer (fsuVM T L I : Set G) = fsuM T L :=
  hmax.2 _ ⟨fsuVM T L I, fsuVM_ne_bot hyp.fsu, isPGroup_fsuVM hyp, rfl⟩
    (fsuM_le_normalizer_fsuVM T L I)

end CFSG.Quasithin.Vol2.Ch10.SecA
