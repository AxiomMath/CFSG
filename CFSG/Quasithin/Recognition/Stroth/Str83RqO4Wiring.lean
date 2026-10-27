module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzEnd
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Window
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4NaturalModule
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4L2Cover
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzCover
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzPushingUp
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzPair
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4LocalStructure
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Class
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

private theorem wr_centerOf_subgroupOf_eq_center (H : Subgroup G) :
    (centerOf H).subgroupOf H = Subgroup.center H := by
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro hh k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hh.2 k k.2)
  · intro hh
    refine ⟨h.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    exact congrArg Subtype.val (hh ⟨k, hk⟩)

private theorem wr_ne_bot_of_sz {a : ℕ} {H T : Subgroup G}
    (hSz : Nonempty (oTwoQuot ↥H ≃* Sz a)) (hT : IsSylowTwoOf T H) : T ≠ ⊥ := by
  rintro rfl
  obtain ⟨e⟩ := hSz
  apply hT.2.2
  have h2 : 2 ∣ Nat.card (oTwoQuot ↥H) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a]
    have h2 : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
  have hdvd : Nat.card (oTwoQuot ↥H) ∣ Nat.card ↥H := Subgroup.card_quotient_dvd_card _
  rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
  exact h2.trans hdvd

theorem not_noCharNormal_of_sz {a : ℕ} (ha : 1 ≤ a)
    {H T : Subgroup G} (hSz : Nonempty (oTwoQuot ↥H ≃* Sz a)) (hC : CharTwo H)
    (hT : IsSylowTwoOf T H) : ¬ NoCharNormal T H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hnc
  have hT1 := wr_ne_bot_of_sz hSz hT
  have hTp : IsPGroup 2 T := hT.2.1
  rcases Stroth.le_normalizer_centerOf_or_le_normalizer_thompsonJ ha hSz hC hT with h | h
  · refine hnc (centerOf T) inf_le_left ?_ ?_ h
    · intro hbot
      haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
      haveI := hTp.center_nontrivial
      obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥T)
      apply hz
      have hz' : (z : ↥T) ∈ (centerOf T).subgroupOf T := by
        rw [wr_centerOf_subgroupOf_eq_center]
        exact z.2
      rw [hbot, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hz'
      exact Subtype.ext hz'
    · rw [wr_centerOf_subgroupOf_eq_center]
      infer_instance
  · exact hnc (thompsonJ T) (B6.thompsonJ_le T) (Setup.thompsonJ_ne_bot hTp hT1)
      (Setup.characteristic_thompsonJ T) h

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {X : Subgroup G}

theorem ArcSzMax.noCharNormal_of_frame
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcSzMax X) :
    NoCharNormal (t.Qv 1 ⊓ t.MX X 0) (t.MX X 0) :=
  ArcSzMax.noCharNormal t hfr hX fun _ hKR ⟨_, hs, hs2⟩ =>
    t.pair_or_le_sup_Qv_one hfr inf_le_right (le_inf hKR (t.K_le_Gv 1)) hs hs2.1

theorem not_arcSz_QT_of_frame
    {a f : ℕ} (hfr : Frame L1 L2 S a f) : ¬ t.ArcSz t.QT := by
  intro hQ
  refine Track.not_arcSz_QT t (a := a) (f := f) hQ
    (fun Y hY => ArcSzMax.noCharNormal_of_frame t hfr hY) (fun Y hY => ?_)
    (fun Y hY hY2 hcov => ArcSz.structure_LX_zero t hfr hY hY2 hcov)
    (fun H T hSz hC hT => not_noCharNormal_of_sz hfr.ha hSz hC hT)
  calc L1 ≤ L1 ⊔ t.Qv 0 := le_sup_left
    _ = t.LX Y 0 ⊔ t.Qv 0 := (Track.ArcSz.LX_sup_Qv_zero_eq t hfr hY).symm
    _ ≤ t.MX Y 0 ⊔ t.Qv 0 := sup_le_sup_right (oTwoPrime_le _) _

theorem arcL_QT_of_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.QT ≠ ⊥) : t.ArcL t.QT := by
  have hSz : (∀ g ∈ t.MX t.QT 0, g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨ t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨
      L1 ≤ t.MX t.QT 0 ⊔ t.Qv 0 :=
    t.pair_or_le_sup_Qv_zero hfr inf_le_right
      (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv 0))
      ⟨t.x₁_mem_normalizer_pCoreOf_GT, t.x₁_mem_Gv_zero⟩ (by simp)
  have hL : (∀ g ∈ t.MX t.QT 1, g ∈ t.Gv 0 ⊓ t.Gv 2 ∨ t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨
      L2 ≤ t.MX t.QT 1 ⊔ t.Qv 1 :=
    t.pair_or_le_sup_Qv_one hfr inf_le_right
      (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv 1))
      ⟨t.x₂_mem_normalizer_pCoreOf_GT, t.x₂_mem_Gv_one⟩ (by simpa using (t.Gv 0).one_mem)
  exact (Track.arcL_or_arcSz_QT t hfr hQ hSz hL).resolve_right (t.not_arcSz_QT_of_frame hfr)

theorem ArcLMax.noCharNormal_of_frame
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X) :
    NoCharNormal (t.PX X) (t.MX X 1) :=
  ArcLMax.noCharNormal t hfr hX fun _ hKR ⟨_, hs, hsx⟩ =>
    t.pair_or_le_sup_Qv_zero hfr inf_le_right (le_inf hKR (t.K_le_Gv 0)) hs hsx

theorem ArcLMax.pX_ne_Qv_zero_of_frame
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X) :
    t.PX X ≠ t.Qv 0 :=
  ArcLMax.pX_ne_Qv_zero t hfr hX (Track.ArcL.isL2Quot_LX_one t hfr hX.1)
    (Track.ArcL.charTwo_LX_one t hfr hX.1 hX.2.1) (ArcL.isSylowTwoOf_pX_LX_one t hfr hX.1)
    (ArcL.noCharNormal_pX_LX_one t hfr hX.1 (ArcLMax.noCharNormal_of_frame t hfr hX))
    (Track.ArcL.pCoreOf_LX_one t hfr hX.1) (Track.ArcL.L2_le_LX_sup_Qv_one t hfr hX.1)

end Track

end CFSG.Quasithin.Stroth.Rq

end
