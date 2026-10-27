module

public import CFSG.RankThree.Asc83Table.M23
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Vol2.Ch11SecA02Recog2
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedScalars specialLinearGroupEquivStatedSL)

theorem factM23Simple :
    ∀ (X : Type) [Group X], IsSporadic .M23 X → IsSimpleGroup X :=
  fun _ _ hX => by
  obtain ⟨e⟩ := hX
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2 e

variable {G : Type} [Group G] [Finite G]

theorem nonempty_quot_mulEquiv_autOn (h8 : Ch10.TmpL6_3_2_2_eight) {T L I : Subgroup G}
    (hfsu : FSU G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (fsuV T I))) := by
  have hL0 : fsuL0 T L = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L T)
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    have hLI : L ≤ Subgroup.normalizer (I : Set G) :=
      (le_conjClosure L T).trans hfsu.irrPlus.2.2.1
    exact le_normalizer_conjClosure_of_le' hLI hTL
  have hO : pCoreOf 2 (autOn L (fsuV T I)) = ⊥ := by
    obtain ⟨hVX, hR, -⟩ := h8 G T L I hfsu
    rw [hL0] at hVX hR
    have h1 := InternalSec.pCoreOf_autOn_eq_bot_of_isPrimeReduced hVX hR
    have h2 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2
      (autOn L (fsuV T I)) (autOn (L ⊔ T) (fsuV T I))
      (Subgroup.map_mono fun _ hx => Subgroup.mem_sup_left hx)
      (autOn_normal_subgroupOf (sup_le Subgroup.le_normalizer hTL))
    rw [h1] at h2
    exact le_bot_iff.mp h2
  have hnt : ¬ L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    intro hL
    have hlt := hfsu.irrPlus.2.2.2.2.1
    rw [show conjClosure L T = L from hL0] at hlt
    have hI : I ≤ Subgroup.centralizer (L : Set G) :=
      (le_conjClosure I T).trans (Subgroup.le_centralizer_iff.mp hL)
    exact lt_irrefl I (lt_of_le_of_lt (le_inf le_rfl hI) hlt)
  have hle := InternalSec.pCore_le_ker_autOnHom hLV hO
  set f := QuotientGroup.lift _ (InternalSec.autOnHom hLV) hle
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLV y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : f.ker ≠ ⊤ := by
    intro htop
    apply InternalSec.ker_autOnHom_ne_top hLV hnt
    rw [eq_top_iff]
    intro l _
    have : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ f.ker := by rw [htop]; trivial
    exact this
  have hbot : f.ker = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker).resolve_right hker
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hbot, hf⟩⟩

structure TypeData (Y : Type) [Group Y] : Prop where
  card : Nat.card Y = 2 ^ 6 * 315 ∨ Nat.card Y = 2 ^ 7 * 79695
  simple : IsSimpleGroup Y
  notSL4 : ¬ Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))

theorem typeData_of_isPSL (hL34 : FactL34) {Y : Type} [Group Y] (h : IsPSL 3 2 2 Y) :
    TypeData Y := by
  refine ⟨Or.inl (card_L34 h), (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).2, ?_⟩
  rintro ⟨e⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  refine hL34 K hK4 (((e.toMonoidHom.comp e'.symm.toMonoidHom).comp
    (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)))).comp
    (specialLinearGroupEquivStatedSL 3 K).toMonoidHom) ?_
  exact e.surjective.comp (e'.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (specialLinearGroupEquivStatedSL 3 K).surjective))

theorem typeData_of_M23
    {Y : Type} [Group Y] (h : IsSporadic .M23 Y) : TypeData Y := by
  obtain ⟨e⟩ := h
  have hc : Nat.card Y = 2 ^ 7 * 79695 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.Asc83Table.M23.card_M23.trans (by norm_num)
  refine ⟨Or.inr hc, factM23Simple Y ⟨e⟩, ?_⟩
  rintro ⟨e'⟩
  have := (Nat.card_congr e'.toEquiv).trans card_SL_four_two
  rw [hc] at this
  norm_num at this

end CFSG.Quasithin.Vol2.Ch11.SecS
