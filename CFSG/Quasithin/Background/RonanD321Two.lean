module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithB51P2Coh
public import CFSG.Quasithin.Background.SmithD321Q
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearModel

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD391 CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

theorem fixV_inf_biSup_eq_bot {ι : Type*} [DecidableEq ι] {L : Subgroup (MulAut W)}
    (I : ι → Subgroup W) (hind : ∀ i, I i ⊓ ⨆ (j) (_ : j ≠ i), I j = ⊥)
    (hLI : ∀ i, ∀ g ∈ L, ∀ w ∈ I i, g w ∈ I i) (hfix : ∀ i, fixV L ⊓ I i = ⊥)
    (s : Finset ι) : fixV L ⊓ ⨆ i ∈ s, I i = ⊥ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.iSup_insert]
    refine B5.P2.fixV_inf_sup ?_ (hLI a) (fun g hg w hw => ?_) (hfix a) ih
    · rw [eq_bot_iff, ← hind a]
      refine inf_le_inf_left _ (iSup₂_le fun j hj => ?_)
      exact le_iSup₂_of_le (f := fun (j : ι) (_ : j ≠ a) => I j) j (fun h => has (h ▸ hj))
        le_rfl
    · exact EmptyFaithfulMultiple.FFL.apply_mem_iSup (fun i => i ∈ s)
        (fun i _ w hw => hLI i g hg w hw) hw

theorem inf_fixV_eq_bot_of_directSumOfCopies {L : Subgroup (MulAut W)} {U : Subgroup W} {d : ℕ}
    (hd : 2 ≤ d) {K : Type} [Field K] {k : ℕ}
    (h : DirectSumOfCopies L U ⊥ (FFModel.nat (StatedSL d K)) k) : U ⊓ fixV L = ⊥ := by
  classical
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := h
  have h1 := fixV_inf_biSup_eq_bot I (fun i => by simpa using hind i)
    (fun i g hg w hw => (hreal i).2.2.2.1 ⟨g, hg⟩ w hw)
    (fun i => FFC.fixV_inf_eq_bot_of_nat hd (hreal i)) Finset.univ
  rw [← hsup, bot_sup_eq, inf_comm]
  simpa using h1

variable [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

theorem isIntDirect_of_d321Two (hB : D321Base M Mp T L V t) (h2 : D321Two L)
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤) :
    IsIntDirect (commV L) ((commV L).map t.toMonoidHom) ⊤ := by
  refine ⟨hB.commV_sup_map, ?_⟩
  rw [eq_bot_iff, ← inf_fixV_eq_bot_of_directSumOfCopies (by norm_num) h2.2]
  refine le_inf inf_le_left ?_
  calc commV L ⊓ (commV L).map t.toMonoidHom
      ≤ (commV L ⊔ fixV Mp) ⊓ ((commV L).map t.toMonoidHom ⊔ fixV Mp) :=
        inf_le_inf le_sup_left le_sup_left
    _ ≤ fixV Mp := hsum.2
    _ ≤ fixV L := SmithD321.fixV_anti hB.L_le_Mp

theorem commV_eq_fixV_of_d321Two (hB : D321Base M Mp T L V t) (h2 : D321Two L)
    (hle : commV L ≤ fixV (conjAutSub t L)) : commV L = fixV (conjAutSub t L) := by
  refine le_antisymm hle fun w hw => ?_
  have hw' : w ∈ commV L ⊔ (commV L).map t.toMonoidHom := by
    rw [hB.commV_sup_map]
    exact Subgroup.mem_top w
  obtain ⟨u, hu, _, ⟨u₀, hu₀, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hw'
  have h1 : t.toMonoidHom u₀ ∈ (fixV L).map t.toMonoidHom := by
    rw [map_fixV_conjAutSub]
    have := (fixV (conjAutSub t L)).mul_mem ((fixV (conjAutSub t L)).inv_mem (hle hu)) hw
    simpa using this
  obtain ⟨y, hy, hyu⟩ := h1
  have hy₀ : y = u₀ := t.injective hyu
  subst hy₀
  have h3 : y ∈ commV L ⊓ fixV L := ⟨hu₀, hy⟩
  rw [inf_fixV_eq_bot_of_directSumOfCopies (by norm_num) h2.2, Subgroup.mem_bot] at h3
  subst h3
  simpa using hu

end CFSG.Quasithin.RonanD321
