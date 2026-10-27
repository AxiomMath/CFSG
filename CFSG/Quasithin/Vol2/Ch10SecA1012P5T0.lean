module

public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixParAux
public import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem T0_le_sup
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    T0 T L ≤ (T ⊓ L) ⊔ (T ⊓ CFSG.conjugate L t) ⊔ pCoreOf 2 (fsuL0 T L) := by
  have hloc := hyp.fsu.maximal.1
  obtain ⟨φ, -, hφk, hφL, hφLt⟩ := exists_fsuL0_prod h37 h38 hyp ht htn
  set S₁ := ((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hS₁
  set S₂ := ((T ⊓ CFSG.conjugate L t).subgroupOf (CFSG.conjugate L t)).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.conjugate L t))) with hS₂
  have hL0syl : IsSylowTwoOf (T0 T L) (fsuL0 T L) :=
    B6.isSylowTwoOf_inf_normal ⟨le_sup_right, hloc.1, hloc.2.2.1⟩ (fsuL0_le_sup T L)
      (sup_le ((le_fsuL0 T L).trans Subgroup.le_normalizer) (le_fsuM T L))
  have hsyl₁ : IsSylowTwoOf S₁ ⊤ :=
    isSylowTwoOf_map_of_surjective (isSylowTwoOf_inf hloc) _ (QuotientGroup.mk'_surjective _)
  have hTLt : IsSylowTwoOf (T ⊓ CFSG.conjugate L t) (CFSG.conjugate L t) := by
    have h := B6.isSylowTwoOf_inf_normal hL0syl (conjugate_le_fsuL0 ht)
      (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht))
    rwa [inf_assoc, inf_eq_right.mpr (conjugate_le_fsuL0 ht)] at h
  have hsyl₂ : IsSylowTwoOf S₂ ⊤ :=
    isSylowTwoOf_map_of_surjective hTLt _ (QuotientGroup.mk'_surjective _)
  have hφT0 : ((T0 T L).subgroupOf (fsuL0 T L)).map φ = S₁.prod S₂ := by
    refine (eq_of_isSylowTwoOf_le ?_ ?_ ?_).symm
    · refine ⟨le_top, ?_, ?_⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩⟩
        obtain ⟨i, hi⟩ := hsyl₁.2.1 ⟨a, ha⟩
        obtain ⟨j, hj⟩ := hsyl₂.2.1 ⟨b, hb⟩
        refine ⟨i + j, Subtype.ext (Prod.ext ?_ ?_)⟩
        · have h1 : a ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
          simp [pow_add, pow_mul, h1]
        · have h2 : b ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
          simp [pow_add, pow_mul', h2]
      · rw [show ((S₁.prod S₂).subgroupOf ⊤).index = (S₁.prod S₂).index from
          Subgroup.relIndex_top_right _, Subgroup.index_prod]
        have h1 := hsyl₁.2.2
        have h2 := hsyl₂.2.2
        rw [show (S₁.subgroupOf ⊤).index = S₁.index from Subgroup.relIndex_top_right _] at h1
        rw [show (S₂.subgroupOf ⊤).index = S₂.index from Subgroup.relIndex_top_right _] at h2
        exact fun h => ((Nat.Prime.dvd_mul Nat.prime_two).mp h).elim h1 h2
    · exact (hL0syl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hL0syl.1).symm).map φ
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      obtain ⟨⟨s, hs⟩, hsT, rfl⟩ := ha
      obtain ⟨⟨s', hs'⟩, hs'T, rfl⟩ := hb
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hsT hs'T
      have hm1 : φ ⟨s, le_fsuL0 T L hs⟩ ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map φ :=
        ⟨⟨s, le_fsuL0 T L hs⟩, Subgroup.mem_subgroupOf.mpr ⟨hsT.1, le_fsuL0 T L hs⟩, rfl⟩
      have hm2 : φ ⟨s', conjugate_le_fsuL0 ht hs'⟩ ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map φ :=
        ⟨⟨s', conjugate_le_fsuL0 ht hs'⟩,
          Subgroup.mem_subgroupOf.mpr ⟨hs'T.1, conjugate_le_fsuL0 ht hs'⟩, rfl⟩
      convert Subgroup.mul_mem _ hm1 hm2 using 1
      rw [hφL s hs, hφLt s' hs']
      simp
  intro x hx
  have hmem : φ ⟨x, hx.2⟩ ∈ S₁.prod S₂ := by
    rw [← hφT0]
    exact ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨⟨⟨s, hsL⟩, hsT, hse⟩, ⟨⟨s', hs'L⟩, hs'T, hs'e⟩⟩ := Subgroup.mem_prod.mp hmem
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hsT hs'T
  have he : φ (⟨s, le_fsuL0 T L hsL⟩ * ⟨s', conjugate_le_fsuL0 ht hs'L⟩) = φ ⟨x, hx.2⟩ := by
    rw [map_mul, hφL s hsL, hφLt s' hs'L]
    refine Prod.ext ?_ ?_
    · simpa using hse
    · simpa using hs'e
  have hk : (⟨s, le_fsuL0 T L hsL⟩ * ⟨s', conjugate_le_fsuL0 ht hs'L⟩ : ↥(fsuL0 T L))⁻¹ *
      ⟨x, hx.2⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [hφk, Subgroup.mem_subgroupOf] at hk
  have hx' : x = s * s' * ((s * s')⁻¹ * x) := by group
  rw [hx']
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left hsT)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right hs'T)))
    (Subgroup.mem_sup_right ?_)
  simpa using hk

theorem pCoreOf_fsuL0_le_centralizer (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    pCoreOf 2 (fsuL0 T L) ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨hVM, hR⟩ := h322 G T L I hyp.fsu
  exact InternalSec.pCoreOf_le_centralizer_of_isPrimeReduced hVM hR (subnormal_fsuL0 T L)

theorem T0_le_centralizer
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    T0 T L ≤ Subgroup.centralizer ((fsuVM T L I ⊓ Subgroup.centralizer
      ((T ⊓ L ⊔ T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  refine (T0_le_sup h37 h38 hyp ht htn).trans (sup_le (sup_le ?_ ?_) ?_)
  · intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp hw.2 s (Subgroup.mem_sup_left hs)).symm
  · intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp hw.2 s (Subgroup.mem_sup_right hs)).symm
  · intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (pCoreOf_fsuL0_le_centralizer h322 hyp ho) w hw.1

end CFSG.Quasithin.Vol2.Ch10.SecA
