module

public import CFSG.Quasithin.MS93.S5ASp
public import CFSG.Quasithin.MS93.S5A54Sp
public import CFSG.Quasithin.MS93.S5ABase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5

variable {G : Type} [Group G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def liftT (T : Subgroup G) (a : ↥M →* ↥(StatedSp 2 F)) (A : Subgroup ↥(StatedSp 2 F)) :
    Subgroup G :=
  T ⊓ (A.comap a).map M.subtype

theorem liftT_le (A : Subgroup ↥(StatedSp 2 F)) : liftT T a A ≤ T := inf_le_left

theorem mem_liftT {A : Subgroup ↥(StatedSp 2 F)} {t : G} :
    t ∈ liftT T a A ↔ t ∈ T ∧ ∃ ht : t ∈ M, a ⟨t, ht⟩ ∈ A := by
  constructor
  · rintro ⟨htT, ⟨m, hm, rfl⟩⟩
    exact ⟨htT, m.2, hm⟩
  · rintro ⟨htT, htM, hA⟩
    exact ⟨htT, ⟨⟨t, htM⟩, hA, rfl⟩⟩

theorem mem_imSp {E : Subgroup G} {x : ↥(StatedSp 2 F)} :
    x ∈ imSp a E ↔ ∃ e ∈ E, ∃ he : e ∈ M, a ⟨e, he⟩ = x := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, m.2, rfl⟩
  · rintro ⟨e, he, heM, rfl⟩
    exact ⟨⟨e, heM⟩, he, rfl⟩

theorem imSp_liftT {A : Subgroup ↥(StatedSp 2 F)} (hA : A ≤ imSp a T) :
    imSp a (liftT T a A) = A := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    exact (mem_liftT.1 hm).2.2
  · intro x hx
    obtain ⟨t, htT, htM, rfl⟩ := mem_imSp.1 (hA hx)
    exact mem_imSp.2 ⟨t, mem_liftT.2 ⟨htT, htM, hx⟩, htM, rfl⟩

namespace NatVec

variable [Finite G] (nv : NatVec M T L a)
include nv

theorem card_eq_mul_relIndex (hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G))
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    {E : Subgroup G} (hE : E ≤ M) :
    Nat.card (MSP.V4 F) = Nat.card (MSP.fixSp (imSp a E)) *
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
  have hCE : (Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L) =
      (AddSubgroup.toSubgroup (MSP.fixSp (imSp a E)).toAddSubgroup).comap nv.toVec := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap,
      nv.mem_centralizer_iff_vec_mem_fixSp hMU hlift hE u]
    rfl
  have hker : nv.toVec.ker = (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    ext u
    rw [MonoidHom.mem_ker, nv.ker_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hkerle : nv.toVec.ker ≤
      (AddSubgroup.toSubgroup (MSP.fixSp (imSp a E)).toAddSubgroup).comap nv.toVec :=
    fun u hu => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hu]
      exact Subgroup.one_mem _
  have h1 := Subgroup.relIndex_mul_card nv.toVec.ker
    ((AddSubgroup.toSubgroup (MSP.fixSp (imSp a E)).toAddSubgroup).comap nv.toVec)
  rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective nv.surj,
    inf_eq_left.2 hkerle] at h1
  have hScard : Nat.card (AddSubgroup.toSubgroup (MSP.fixSp (imSp a E)).toAddSubgroup) =
      Nat.card (MSP.fixSp (imSp a E)) := rfl
  have hCcard : Nat.card nv.toVec.ker =
      Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hker, card_subgroupOf, inf_comm]
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Uq M T L)
  rw [← card_subgroupOf, hCE, ← h1, hScard, hCcard] at h2
  have h3 := nv.card_Uq
  have hC : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have key : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) * Nat.card (MSP.V4 F) =
      Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) *
        (Nat.card (MSP.fixSp (imSp a E)) *
          (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L)) := by
    rw [← h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left hC key

end NatVec

namespace IsSp4Data

variable [Finite G] [Fintype F] (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
include hd h

theorem pCoreOf_le_liftT (A : Subgroup ↥(StatedSp 2 F)) : pCoreOf 2 M ≤ liftT T a A := by
  intro x hx
  obtain ⟨hxM, h1⟩ := (mem_kerG a).1 (hd.pCoreOf_le_kerG h hx)
  refine mem_liftT.2 ⟨h.pCore_le hx, hxM, ?_⟩
  rw [h1]
  exact A.one_mem

theorem liftT_imSp {E : Subgroup G} (hQE : pCoreOf 2 M ≤ E) (hET : E ≤ T) :
    liftT T a (imSp a E) = E := by
  apply le_antisymm
  · intro t ht
    obtain ⟨htT, htM, hx⟩ := mem_liftT.1 ht
    obtain ⟨e, he, heM, hea⟩ := mem_imSp.1 hx
    have hk : e⁻¹ * t ∈ T ⊓ kerG a := by
      refine ⟨T.mul_mem (T.inv_mem (hET he)) htT,
        (mem_kerG a).2 ⟨M.mul_mem (M.inv_mem heM) htM, ?_⟩⟩
      have e1 : (⟨e⁻¹ * t, M.mul_mem (M.inv_mem heM) htM⟩ : ↥M) =
          (⟨e, heM⟩ : ↥M)⁻¹ * ⟨t, htM⟩ := rfl
      rw [e1, map_mul, map_inv, hea, inv_mul_cancel]
    rw [hd.inf_kerG h] at hk
    have := E.mul_mem he (hQE hk)
    simpa using this
  · intro e he
    exact mem_liftT.2 ⟨hET he, hET.trans h.le he, mem_imSp.2 ⟨e, he, hET.trans h.le he, rfl⟩⟩

theorem card_liftT {A : Subgroup ↥(StatedSp 2 F)} (hA : A ≤ imSp a T) :
    Nat.card (liftT T a A) = Nat.card (pCoreOf 2 M) * Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 M) (liftT T a A)
  rw [inf_eq_left.2 (hd.pCoreOf_le_liftT h A), ← hd.card_imSp h (liftT_le A),
    imSp_liftT hA] at h1
  rw [← h1, mul_comm]

theorem card_le_mul_card_imSp {E : Subgroup G} (hET : E ≤ T) :
    Nat.card E ≤ Nat.card (pCoreOf 2 M) * Nat.card (imSp a E) := by
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 M) E
  rw [← hd.card_imSp h hET] at h1
  calc Nat.card E = Nat.card (imSp a E) * Nat.card ↥(pCoreOf 2 M ⊓ E) := h1.symm
    _ ≤ Nat.card (imSp a E) * Nat.card (pCoreOf 2 M) := Nat.mul_le_mul_left _
      (Subgroup.card_le_of_le (inf_le_left : pCoreOf 2 M ⊓ E ≤ pCoreOf 2 M))
    _ = _ := mul_comm _ _

theorem pCoreOf_le_of_card {E : Subgroup G} (hET : E ≤ T)
    (hcard : Nat.card (pCoreOf 2 M) * Nat.card (imSp a E) ≤ Nat.card E) : pCoreOf 2 M ≤ E := by
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 M) E
  rw [← hd.card_imSp h hET] at h1
  have hpos : 0 < Nat.card (imSp a E) := Nat.card_pos
  have h2 : Nat.card (pCoreOf 2 M) ≤ Nat.card ↥(pCoreOf 2 M ⊓ E) := by
    rw [← h1, mul_comm] at hcard
    exact (Nat.mul_le_mul_left_iff hpos).1 hcard
  have := Subgroup.eq_of_le_of_card_ge inf_le_left h2
  exact inf_eq_left.1 this

omit [Fintype F] hd in
theorem isPGroup_imSp : IsPGroup 2 (imSp a T) :=
  (h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm).map a

variable (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
  m * u * m⁻¹ = u)
include hlift

omit h in
theorem card_eq_mul_relIndex {E : Subgroup G} (hE : E ≤ M) :
    Nat.card (MSP.V4 F) = Nat.card (MSP.fixSp (imSp a E)) *
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) :=
  hd.nonempty_natVec.some.card_eq_mul_relIndex hd.nat.1 hlift hE

theorem isOffCandM_iff {E : Subgroup G} (hET : E ≤ T) :
    IsOffCandM M T L (2 ^ k) E ↔ IsCandSp (imSp a T) (imSp a E) := by
  have hV := hd.card_eq_mul_relIndex hlift (hET.trans h.le)
  have hfix : 0 < Nat.card (MSP.fixSp (imSp a E)) := Nat.card_pos
  rw [IsOffCandM, IsCandSp, hd.card_imSp h hET, ← hd.nat_card_eq, hV,
    Nat.mul_le_mul_left_iff hfix, Nat.mul_le_mul_left_iff hfix]
  exact and_congr_left' ⟨fun _ => imSp_mono a hET, fun _ => hET⟩

theorem pCoreOf_le_of_mem_offSetM {E : Subgroup G} (hE : E ∈ offSetM M T L (2 ^ k)) :
    pCoreOf 2 M ≤ E := by
  have hET := hE.1.1
  have hc := (hd.isOffCandM_iff h hlift hET).1 hE.1
  have hc' : IsOffCandM M T L (2 ^ k) (liftT T a (imSp a E)) := by
    rw [hd.isOffCandM_iff h hlift (liftT_le _), imSp_liftT hc.1]
    exact hc
  have hle := hE.2 _ hc'
  rw [hd.card_liftT h hc.1] at hle
  exact hd.pCoreOf_le_of_card h hET hle

theorem mem_offSetM_iff {E : Subgroup G} :
    E ∈ offSetM M T L (2 ^ k) ↔
      pCoreOf 2 M ≤ E ∧ E ≤ T ∧ imSp a E ∈ candMax (imSp a T) := by
  constructor
  · intro hE
    have hQE := hd.pCoreOf_le_of_mem_offSetM h hlift hE
    have hET := hE.1.1
    refine ⟨hQE, hET, (hd.isOffCandM_iff h hlift hET).1 hE.1, fun B hB => ?_⟩
    have hB' : IsOffCandM M T L (2 ^ k) (liftT T a B) := by
      rw [hd.isOffCandM_iff h hlift (liftT_le _), imSp_liftT hB.1]
      exact hB
    have h1 := hE.2 _ hB'
    rw [hd.card_liftT h hB.1, ← hd.liftT_imSp h hQE hET,
      hd.card_liftT h (imSp_mono a hET)] at h1
    exact (Nat.mul_le_mul_left_iff Nat.card_pos).1 h1
  · rintro ⟨hQE, hET, hA, hmax⟩
    refine ⟨(hd.isOffCandM_iff h hlift hET).2 hA, fun E' hE' => ?_⟩
    have h1 := hd.card_le_mul_card_imSp h hE'.1
    have h2 := hmax _ ((hd.isOffCandM_iff h hlift hE'.1).1 hE')
    calc Nat.card E' ≤ Nat.card (pCoreOf 2 M) * Nat.card (imSp a E') := h1
      _ ≤ Nat.card (pCoreOf 2 M) * Nat.card (imSp a E) := Nat.mul_le_mul_left _ h2
      _ = Nat.card E := by
        rw [← hd.card_liftT h (imSp_mono a hET), hd.liftT_imSp h hQE hET]

theorem liftT_mem_offSetM {A : Subgroup ↥(StatedSp 2 F)} (hA : A ∈ candMax (imSp a T)) :
    liftT T a A ∈ offSetM M T L (2 ^ k) := by
  rw [hd.mem_offSetM_iff h hlift, imSp_liftT hA.1.1]
  exact ⟨hd.pCoreOf_le_liftT h A, liftT_le A, hA⟩

theorem card_offSetM :
    Nat.card (offSetM M T L (2 ^ k)) = Nat.card (candMax (imSp a T)) := by
  refine Nat.card_congr
    { toFun := fun E => ⟨imSp a E, ((hd.mem_offSetM_iff h hlift).1 E.2).2.2⟩
      invFun := fun A => ⟨liftT T a A, hd.liftT_mem_offSetM h hlift A.2⟩
      left_inv := fun E => ?_
      right_inv := fun A => ?_ }
  · obtain ⟨hQE, hET, -⟩ := (hd.mem_offSetM_iff h hlift).1 E.2
    exact Subtype.ext (hd.liftT_imSp h hQE hET)
  · exact Subtype.ext (imSp_liftT A.2.1.1)

theorem jOffM_eq_of_candMax_eq {A₀ : Subgroup ↥(StatedSp 2 F)}
    (hA : candMax (imSp a T) = {A₀}) : jOffM M T L (2 ^ k) = liftT T a A₀ := by
  have hA₀ : A₀ ∈ candMax (imSp a T) := hA ▸ rfl
  apply le_antisymm
  · refine iSup₂_le fun E hE => ?_
    obtain ⟨hQE, hET, hEA⟩ := (hd.mem_offSetM_iff h hlift).1 hE
    rw [hA] at hEA
    rw [← hd.liftT_imSp h hQE hET, show imSp a E = A₀ from hEA]
  · exact le_iSup₂_of_le (liftT T a A₀) (hd.liftT_mem_offSetM h hlift hA₀) le_rfl

theorem jOffM_eq_of_iSup (hT : (⨆ A ∈ candMax (imSp a T), A) = imSp a T) :
    jOffM M T L (2 ^ k) = T := by
  have hJT : jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  obtain ⟨A₀, hA₀⟩ := candMax_nonempty (imSp a T)
  have hQJ : pCoreOf 2 M ≤ jOffM M T L (2 ^ k) :=
    (hd.pCoreOf_le_liftT h A₀).trans
      (le_iSup₂_of_le (liftT T a A₀) (hd.liftT_mem_offSetM h hlift hA₀) le_rfl)
  have himJ : imSp a (jOffM M T L (2 ^ k)) = imSp a T := by
    refine le_antisymm (imSp_mono a hJT) ?_
    rw [← hT]
    refine iSup₂_le fun A hA => ?_
    rw [← imSp_liftT hA.1.1]
    exact imSp_mono a (le_iSup₂_of_le (liftT T a A) (hd.liftT_mem_offSetM h hlift hA) le_rfl)
  rw [← hd.liftT_imSp h hQJ hJT, himJ, hd.liftT_imSp h h.pCore_le le_rfl]

end IsSp4Data

end S5

end CFSG.Quasithin.MS93
