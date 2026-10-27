module

public import CFSG.LocalAnalysis.StandardType.SpFixedSpaceIota
public import CFSG.LocalAnalysis.StandardType.SpFixedSpaceSmall
public import CFSG.LocalAnalysis.StandardType.SpWeightFixes
public import CFSG.LocalAnalysis.StandardType.SpSimpleOrder
public import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverOrder
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem false_of_fixes_ker (D : Subgroup (StatedSp n F)) [Fintype D] (hodd : Odd (Fintype.card D))
    {J : Subgroup (StatedSp n F)}
    (hJ : CFSG.Assembly.IsSubnormal J (Subgroup.centralizer (D : Set (StatedSp n F))))
    (hA : IsAlternatingEightCover ↥J)
    (hfix : ∀ g ∈ J, ∀ v : Fin n ⊕ Fin n → F, fixedNorm D *ᵥ v = 0 → matHom F n g *ᵥ v = v) :
    False := by
  classical
  obtain ⟨m, res, ι, hresι, hιres⟩ := exists_res_iota D hodd
  let C : Subgroup (StatedSp n F) := Subgroup.centralizer (D : Set (StatedSp n F))
  have hJC : J ≤ C := hJ.le
  have hJ' : CFSG.Assembly.IsSubnormal J C := hJ
  haveI : Finite (StatedSp n F) := inferInstance
  haveI : Finite ↥J := inferInstance
  have hinj : ∀ g (hg : g ∈ J), res ⟨g, hJC hg⟩ = 1 → g = 1 := by
    intro g hg hres1
    have h := hιres ⟨g, hJC hg⟩ (hfix g hg)
    rw [hres1, map_one] at h
    exact Subtype.ext_iff.mp h.symm
  have hkill_false : (∀ g (hg : g ∈ J), res ⟨g, hJC hg⟩ = 1) → False := by
    intro hkill
    have hbot : J = ⊥ := by
      refine le_antisymm (fun g hg => ?_) bot_le
      rw [Subgroup.mem_bot]
      exact hinj g hg (hkill g hg)
    haveI : Subsingleton ↥J := by
      rw [hbot]
      infer_instance
    obtain ⟨a, b, hab⟩ := (CFSG.StandardType.IsAlternatingEightCover.nontrivial hA).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  by_cases hm : m ≤ 2
  ·
    apply hkill_false
    intro g hg
    have h1 : res (Subgroup.inclusion hJC ⟨g, hg⟩) = 1 := by
      have h := CFSG.StandardType.SpFixed.IsAlternatingEightCover.statedSp_map_eq_one hA hm
        (res.comp (Subgroup.inclusion hJC)) ⟨g, hg⟩
      simpa using h
    have heq : Subgroup.inclusion hJC ⟨g, hg⟩ = (⟨g, hJC hg⟩ : ↥C) := Subtype.ext rfl
    rw [heq] at h1
    exact h1
  ·
    have hm3 : 3 ≤ m := by omega
    haveI : IsSimpleGroup (StatedSp m F) := isSimpleGroup_statedSp hm3
    have hsurj : Function.Surjective res := fun M => ⟨ι M, hresι M⟩
    have hK : CFSG.Assembly.IsSubnormal (J.subgroupOf C) ⊤ :=
      CFSG.Assembly.IsSubnormal.of_mathlib (CFSG.Assembly.IsSubnormal.subgroupOf hJ')
    have hKmap : CFSG.Assembly.IsSubnormal ((J.subgroupOf C).map res) ⊤ := by
      have h := CFSG.Assembly.IsSubnormal.map res hK
      rwa [Subgroup.map_top_of_surjective res hsurj] at h
    rcases CFSG.Assembly.IsSubnormal.eq_bot_or_top hKmap with hbot | htop
    · apply hkill_false
      intro g hg
      have hmem : (⟨g, hJC hg⟩ : ↥C) ∈ J.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        exact hg
      have hmap : res ⟨g, hJC hg⟩ ∈ (J.subgroupOf C).map res :=
        Subgroup.mem_map_of_mem res hmem
      rw [hbot] at hmap
      simpa using hmap
    ·
      let φ : ↥J →* StatedSp m F := res.comp (Subgroup.inclusion hJC)
      have hinjφ : Function.Injective φ := by
        rw [injective_iff_map_eq_one]
        intro x hx
        apply Subtype.ext
        have hx' : res (Subgroup.inclusion hJC x) = 1 := by simpa [φ] using hx
        have heq : Subgroup.inclusion hJC x = (⟨x, hJC x.2⟩ : ↥C) := Subtype.ext rfl
        rw [heq] at hx'
        exact hinj x x.2 hx'
      have hsurjφ : Function.Surjective φ := by
        intro s
        have hmem : s ∈ (J.subgroupOf C).map res := by
          rw [htop]
          exact Subgroup.mem_top s
        rw [Subgroup.mem_map] at hmem
        obtain ⟨k, hk, hks⟩ := hmem
        refine ⟨⟨k, hk⟩, ?_⟩
        show res (Subgroup.inclusion hJC (⟨k, hk⟩ : ↥J)) = s
        have heq : Subgroup.inclusion hJC (⟨k, hk⟩ : ↥J) = k := Subtype.ext rfl
        rw [heq]
        exact hks
      have hcard : Nat.card ↥J = Nat.card (StatedSp m F) :=
        Nat.card_congr (Equiv.ofBijective φ ⟨hinjφ, hsurjφ⟩)
      have h27 : 27 ∣ Nat.card ↥J := by
        rw [hcard]
        exact twentySeven_dvd_card_statedSp hm3
      exact CFSG.StandardType.IsAlternatingEightCover.not_dvd_card_twentySeven hA h27

theorem false_of_isSubnormal_centralizer_eightCover (hn : n ≤ 4 ∨ (n = 5 ∧ 3 ∣ Nat.card F + 1))
    (D : Subgroup (StatedSp n F)) (hDc : Nat.card D = 9)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hexp : ∀ a ∈ D, a ^ 3 = 1)
    {J : Subgroup (StatedSp n F)}
    (hJ : CFSG.Assembly.IsSubnormal J (Subgroup.centralizer (D : Set (StatedSp n F))))
    (hA : IsAlternatingEightCover ↥J) : False := by
  classical
  haveI : Fintype D := Fintype.ofFinite D
  have hDc' : Fintype.card D = 9 := by rw [← Nat.card_eq_fintype_card]; exact hDc
  have hodd : Odd (Fintype.card D) := by rw [hDc']; decide
  exact false_of_fixes_ker D hodd hJ hA (fixes_of_ker hn D hDc' hcomm hexp hJ.le hA)

end SpFixed

end CFSG.StandardType
