module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

private theorem ggPhanAux_mem_hyperplane {G : Type} [Group G] {Bs : Subgroup G}
    {r : MulAut ↥Bs} {z : G} :
    z ∈ ggHyperplane Bs r ↔ ∃ b : ↥Bs, r b = b ∧ (b : G) = z := by
  rw [ggHyperplane, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hbz⟩
    exact ⟨b, hb, hbz⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem ggPhan_card_bstar_le_of_genL
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hgen : L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
      ggRankOneIn L Bs r)
    (R : Finset (MulAut ↥Bs)) (hR : ∀ r ∈ R, GGIsReflection p r)
    (hcl : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      r ∈ Subgroup.closure (R : Set (MulAut ↥Bs))) :
    Nat.card Bs ≤ p ^ (R.card + 1) := by
  classical
  let F : MulAut ↥Bs → Subgroup G := fun r => ggHyperplane Bs r
  let K : Subgroup G := R.inf F
  let H : Subgroup G := Bs ⊓ K
  have hHBs : H ≤ Bs := inf_le_left
  have hHK : H ≤ K := inf_le_right
  have hHgen : ∀ r ∈ R, H ≤ F r := fun r hr => hHK.trans (Finset.inf_le (f := F) hr)
  have hFix1 : ggHyperplane Bs (1 : MulAut ↥Bs) = Bs := by
    ext z
    rw [ggPhanAux_mem_hyperplane]
    constructor
    · rintro ⟨b, -, rfl⟩; exact b.2
    · intro hz; exact ⟨⟨z, hz⟩, rfl, rfl⟩
  have hFixmul : ∀ x y : MulAut ↥Bs, H ≤ F x → H ≤ F y → H ≤ F (x * y) := by
    intro x y hx hy z hz
    obtain ⟨b, hb, hbz⟩ := (ggPhanAux_mem_hyperplane).1 (hx hz)
    obtain ⟨c, hc, hcz⟩ := (ggPhanAux_mem_hyperplane).1 (hy hz)
    have hbc : b = c := Subtype.ext (hbz.trans hcz.symm)
    refine (ggPhanAux_mem_hyperplane).2 ⟨b, ?_, hbz⟩
    have hyb : y b = b := by rw [hbc]; exact hc
    rw [MulAut.mul_apply, hyb, hb]
  have hFixinv : ∀ x : MulAut ↥Bs, H ≤ F x → H ≤ F x⁻¹ := by
    intro x hx z hz
    obtain ⟨b, hb, hbz⟩ := (ggPhanAux_mem_hyperplane).1 (hx hz)
    refine (ggPhanAux_mem_hyperplane).2 ⟨b, ?_, hbz⟩
    have h1 : x⁻¹ (x b) = x⁻¹ b := congrArg (fun w => x⁻¹ w) hb
    simpa using h1.symm
  have hHclos : ∀ r ∈ Subgroup.closure (R : Set (MulAut ↥Bs)), H ≤ F r := by
    intro r hr
    refine Subgroup.closure_induction (p := fun r _ => H ≤ F r) ?_ ?_ ?_ ?_ hr
    · intro x hx; exact hHgen x hx
    · change H ≤ ggHyperplane Bs (1 : MulAut ↥Bs)
      rw [hFix1]
      exact inf_le_left
    · intro x y _ _ hx hy; exact hFixmul x y hx hy
    · intro x _ hx; exact hFixinv x hx
  have hLc : L ≤ Subgroup.centralizer (H : Set G) := by
    rw [hgen]
    refine iSup_le fun r => iSup_le fun hr => ?_
    have hHr : H ≤ ggHyperplane Bs r := hHclos r (hcl r hr.1 hr.2)
    rw [ggRankOneIn]
    exact (ggOTwoPrime_le _).trans (le_trans inf_le_right (Subgroup.centralizer_le hHr))
  have hHc : H ≤ Subgroup.centralizer (L : Set G) := Subgroup.le_centralizer_iff.mp hLc
  have hHinf : H ≤ Bs ⊓ Subgroup.centralizer (L : Set G) := le_inf hHBs hHc
  have hHcard : Nat.card ↥H ≤ p :=
    (Subgroup.card_le_of_le hHinf).trans (GGConfig.card_bstar_centralizer_le hcfg.1.1)
  have hrel : ∀ r ∈ R, (ggHyperplane Bs r).relIndex Bs = p := fun r hr =>
    GGDichotomy.relIndex_ggFixG (hR r hr)
  have hKrel : K.relIndex Bs ≤ p ^ R.card := by
    have key : ∀ S : Finset (MulAut ↥Bs), S ⊆ R → (S.inf F).relIndex Bs ≤ p ^ S.card := by
      intro S
      induction S using Finset.induction with
      | empty =>
          intro _
          rw [Finset.inf_empty, Subgroup.relIndex_top_left]
          exact le_of_eq (Nat.pow_zero p).symm
      | insert a s ha ih =>
          intro hSR
          have haR : a ∈ R := hSR (Finset.mem_insert_self a s)
          have hsR : s ⊆ R := fun x hx => hSR (Finset.mem_insert_of_mem hx)
          rw [Finset.inf_insert, Finset.card_insert_of_notMem ha]
          calc (F a ⊓ s.inf F).relIndex Bs
              ≤ (F a).relIndex Bs * (s.inf F).relIndex Bs := Subgroup.relIndex_inf_le
            _ ≤ p * p ^ s.card := Nat.mul_le_mul (le_of_eq (hrel a haR)) (ih hsR)
            _ = p ^ (s.card + 1) := by rw [pow_succ, Nat.mul_comm]
    exact key R (fun _ h => h)
  have hHrel : H.relIndex Bs ≤ K.relIndex Bs := by
    have h := Subgroup.relIndex_inf_le (H := Bs) (K := K) (L := Bs)
    rw [Subgroup.relIndex_self, one_mul] at h
    exact h
  have hcardBs : Nat.card Bs = H.relIndex Bs * Nat.card ↥H := by
    have h := Subgroup.relIndex_mul_card H Bs
    rw [inf_eq_left.mpr hHBs] at h
    exact h.symm
  rw [hcardBs]
  calc H.relIndex Bs * Nat.card ↥H ≤ p ^ R.card * p :=
        Nat.mul_le_mul (hHrel.trans hKrel) hHcard
    _ = p ^ (R.card + 1) := by rw [pow_succ, Nat.mul_comm]


theorem ggPhan_card_bstar_le
    (hGen : GGSecFiveGenPhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (R : Finset (MulAut ↥Bs)) (hR : ∀ r ∈ R, GGIsReflection p r)
    (hcl : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      r ∈ Subgroup.closure (R : Set (MulAut ↥Bs))) :
    Nat.card Bs ≤ p ^ (R.card + 1) := by
  exact ggPhan_card_bstar_le_of_genL hcfg
    (hGen G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) hns) R hR hcl

end CFSG.StandardType

end
