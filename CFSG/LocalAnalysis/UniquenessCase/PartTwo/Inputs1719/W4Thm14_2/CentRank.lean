module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L3AutRankHolds
public import CFSG.Quasithin.EmptyFaithful.S145Cop
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem fixV_eq_bot_of_center (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hB : IsBasicModule Y) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hZ : Subgroup.center ↥L ≠ ⊥) (hZodd : Odd (Nat.card (Subgroup.center ↥L))) :
    fixV L = ⊥ := by
  classical
  haveI : Finite (MulAut W) := inferInstanceAs (Finite (W ≃* W))
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let X : Subgroup (MulAut W) := Z.map L.subtype
  have hXodd : Odd (Nat.card X) := by
    show Odd (Nat.card (Z.map L.subtype))
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hZodd
  have hcompl := isCompl_fixV_commV_of_odd X hXodd hW
  have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hconj : ∀ u ∈ Y, ∀ x ∈ X, u * x * u⁻¹ ∈ X := by
    intro u hu x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr
      ⟨⟨u * (z : MulAut W) * u⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hYnorm hu) (z : MulAut W)).mp z.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro l
    have hul : u⁻¹ * (l : MulAut W) * u ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hYnorm (Y.inv_mem hu)) (l : MulAut W)).mp l.2
    have hzc : (u⁻¹ * (l : MulAut W) * u) * (z : MulAut W) =
        (z : MulAut W) * (u⁻¹ * (l : MulAut W) * u) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz
        ⟨u⁻¹ * (l : MulAut W) * u, hul⟩)
    apply Subtype.ext
    change (l : MulAut W) * (u * (z : MulAut W) * u⁻¹) =
      (u * (z : MulAut W) * u⁻¹) * (l : MulAut W)
    calc (l : MulAut W) * (u * (z : MulAut W) * u⁻¹)
        = u * ((u⁻¹ * (l : MulAut W) * u) * (z : MulAut W)) * u⁻¹ := by group
      _ = u * ((z : MulAut W) * (u⁻¹ * (l : MulAut W) * u)) * u⁻¹ := by rw [hzc]
      _ = (u * (z : MulAut W) * u⁻¹) * (l : MulAut W) := by group
  have hXnorm : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj u hu x
    · intro hx
      have h := hconj u⁻¹ (Y.inv_mem hu) (u * x * u⁻¹) hx
      have h' : u⁻¹ * (u * x * u⁻¹) * u = x := by group
      simpa [h'] using h
  have hstableFix : StableUnder Y (fixV X) := fun u hu w hw =>
    CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hXnorm hu) hw
  have hstableComm : StableUnder Y (commV X) := fun u hu w hw =>
    CFSG.Quasithin.commV_apply_mem_of_mem_normalizer (hXnorm hu) hw
  have hXne : X ≠ ⊥ := by
    intro hbot
    exact hZ ((Subgroup.map_eq_bot_iff_of_injective Z L.subtype_injective).1 hbot)
  have hfix_ne_top : fixV X ≠ ⊤ := by
    intro htop
    apply hXne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    ext w
    have hw : w ∈ fixV X := htop ▸ Subgroup.mem_top w
    simpa using (mem_fixV.mp hw) x hx
  have hfix_eq_bot : fixV X = ⊥ := by
    rcases hB.1 (fixV X) (commV X) hstableFix hstableComm hcompl.sup_eq_top with
      htop | hcomm
    · exact absurd htop hfix_ne_top
    · rw [eq_bot_iff]
      intro w hw
      have hw' : w ∈ fixV X ⊓ commV X := ⟨hw, hcomm ▸ Subgroup.mem_top w⟩
      rwa [hcompl.disjoint.eq_bot] at hw'
  have hXL : X ≤ L := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  have hfix_le : fixV L ≤ fixV X := by
    intro w hw
    rw [mem_fixV] at hw ⊢
    intro x hx
    exact hw x (hXL hx)
  rw [eq_bot_iff]
  intro w hw
  have hwX : w ∈ fixV X := hfix_le hw
  simpa [hfix_eq_bot] using hwX

theorem pRank_le_one_of_centralizer_pow_six {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hL : UC22.IsSL3 ↥L 2)
    (hc : ∀ c : MulAut W, (∀ l ∈ L, c * l = l * c) → c ^ 6 = 1) :
    ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ 1 := by
  classical
  haveI : Finite (MulAut W) := inferInstanceAs (Finite (W ≃* W))
  intro p hp hp3
  let K : Subgroup ↥Y := L.subgroupOf Y
  haveI : K.Normal := hLn
  let e : ↥K ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  haveI : Finite (MulAut ↥K) := inferInstanceAs (Finite (↥K ≃* ↥K))
  haveI : Finite (MulAut ↥L) := inferInstanceAs (Finite (↥L ≃* ↥L))
  have hcent : CFSG.Open.pRank p (⊤ ⊓ Subgroup.centralizer (K : Set ↥Y)) = 0 := by
    rw [top_inf_eq]
    by_contra hne
    have h1 : 1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (K : Set ↥Y)) := by
      omega
    obtain ⟨c, hcH, hcord⟩ :=
      CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hp h1
    have h6 : c ^ 6 = 1 := by
      apply Y.subtype_injective
      rw [map_pow, map_one]
      apply hc (c : MulAut W)
      intro l hl
      have hk : (⟨l, hLY hl⟩ : ↥Y) ∈ K := by
        simpa [K, Subgroup.mem_subgroupOf] using hl
      have hcommY : (⟨l, hLY hl⟩ : ↥Y) * c = c * ⟨l, hLY hl⟩ :=
        Subgroup.mem_centralizer_iff.mp hcH ⟨l, hLY hl⟩ hk
      have hcommW : (l : MulAut W) * (c : MulAut W) = (c : MulAut W) * l := by
        simpa using congrArg (fun z : ↥Y => (z : MulAut W)) hcommY
      exact hcommW.symm
    have hdvd : orderOf c ∣ 6 := orderOf_dvd_of_pow_eq_one h6
    rw [hcord] at hdvd
    have hdvd23 : p ∣ 2 * 3 := by
      rw [show (2 : ℕ) * 3 = 6 by norm_num]
      exact hdvd
    have h23 : p = 2 ∨ p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvd23 with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h)
    rcases h23 with rfl | rfl <;> omega
  have himg : CFSG.Open.pRank p ((⊤ : Subgroup ↥Y).map (MulAut.conjNormal (H := K))) ≤ 1 := by
    calc CFSG.Open.pRank p ((⊤ : Subgroup ↥Y).map (MulAut.conjNormal (H := K)))
        ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) :=
          CFSG.SectionRank.pRank_mono hp.one_lt le_top
      _ = CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L)) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)
      _ ≤ 1 := by
          rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
          have hp5 : 5 ≤ p :=
            Nat.Prime.five_le_of_ne_two_of_ne_three hp (by omega) (by omega)
          exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.k_L34AutRank_holds
            ↥L hL.1 hL.2 p hp hp5
  have hmain := CFSG.AGLEmbedding.pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal
    (G := ↥Y) hp K ⊤
  have hle : CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ 0 + 1 :=
    hmain.trans (add_le_add (le_of_eq hcent) himg)
  simpa using hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
