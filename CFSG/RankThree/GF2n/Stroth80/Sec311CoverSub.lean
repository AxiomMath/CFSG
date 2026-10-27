module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Griess

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem iSup_conj_subtype_eq_top (R L : Subgroup G) (hLR : L ≤ R)
    (hgen : R ≤ ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L) :
    ⨆ g : ↥R, conjSubgroup g (L.subgroupOf R) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : G) ∈ ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L := hgen x.2
  have key : ∀ y : G, y ∈ ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L →
      ∃ hy : y ∈ R, (⟨y, hy⟩ : ↥R) ∈ ⨆ g : ↥R, conjSubgroup g (L.subgroupOf R) := by
    intro y hy
    refine Subgroup.iSup_induction (fun h : G => ⨆ (_ : h ∈ R), conjSubgroup h L)
      (C := fun y => ∃ hy : y ∈ R,
        (⟨y, hy⟩ : ↥R) ∈ ⨆ g : ↥R, conjSubgroup g (L.subgroupOf R)) hy ?_ ?_ ?_
    · intro h y hy
      refine Subgroup.iSup_induction (fun (_ : h ∈ R) => conjSubgroup h L)
        (C := fun y => ∃ hy : y ∈ R,
          (⟨y, hy⟩ : ↥R) ∈ ⨆ g : ↥R, conjSubgroup g (L.subgroupOf R)) hy ?_ ?_ ?_
      · intro hh y hyc
        have hl : h⁻¹ * y * h ∈ L := mem_conjSubgroup.mp hyc
        have hyR : y ∈ R := by
          have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
          rw [this]
          exact R.mul_mem (R.mul_mem hh (hLR hl)) (R.inv_mem hh)
        refine ⟨hyR, ?_⟩
        refine Subgroup.mem_iSup_of_mem (⟨h, hh⟩ : ↥R) ?_
        rw [mem_conjSubgroup]
        show (⟨h⁻¹ * y * h, _⟩ : ↥R) ∈ L.subgroupOf R
        exact hl
      · exact ⟨R.one_mem, Subgroup.one_mem _⟩
      · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨R.mul_mem ha hb, Subgroup.mul_mem _ ha' hb'⟩
    · exact ⟨R.one_mem, Subgroup.one_mem _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨R.mul_mem ha hb, Subgroup.mul_mem _ ha' hb'⟩
  obtain ⟨hy, hmem⟩ := key (x : G) hx
  simpa using hmem

theorem le_of_perfect_cover_sub [Finite G] (R N N₀ L : Subgroup G) (hNR : N ≤ R) (hN₀N : N₀ ≤ N)
    (hLR : L ≤ R) (hN₀norm : ∀ r ∈ R, ∀ n ∈ N₀, r * n * r⁻¹ ∈ N₀)
    (hgen : R ≤ ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L)
    (hcomm : ∀ h ∈ R, ∀ n ∈ N, ∀ l ∈ conjSubgroup h L, ⁅n, l⁆ ∈ N₀) (hLN : L ⊓ N ≤ N₀)
    (hab : ∀ l ∈ L, ∀ l' ∈ L, ⁅l, l'⁆ ∈ N ∧ l ^ 2 ∈ N) {τ : G} (hτR : τ ∈ R)
    (hτL : τ ∈ Subgroup.normalizer (L : Set G)) (hτ : ∀ l ∈ L, ⁅τ, l⁆ ∈ N → l ∈ N)
    (hnorm : ∀ r ∈ R, r ∈ Subgroup.normalizer ((L ⊔ N : Subgroup G) : Set G) →
      r ∈ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ↥R →* GL ι K)
    (hker : φ.ker = N.subgroupOf R) (b : ℕ)
    (hP : ∀ (E : Type) [Group E] [Finite E] (Y : Subgroup E) (π : E →* GL ι K),
      π.range = φ.range → π.ker = Y → Y ≤ Subgroup.center E → commutator E = ⊤ →
      ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
        (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
          e ∈ Subgroup.normalizer (A : Set E)) → b ≤ Nat.card A → Y = ⊥)
    (hb : b ≤ Nat.card ((L.subgroupOf R).map φ)) : N ≤ N₀ := by
  classical
  haveI hN₀normal : (N₀.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN₀norm g g.2 n hn⟩
  have hgen' := iSup_conj_subtype_eq_top R L hLR hgen
  have key := le_of_perfect_cover (N.subgroupOf R) (N₀.subgroupOf R) (L.subgroupOf R)
    (fun x hx => hN₀N hx) hgen'
    (fun g n hn l hl => by
      have h1 : g⁻¹ * l * g ∈ L.subgroupOf R := mem_conjSubgroup.mp hl
      have hl' : (l : G) ∈ conjSubgroup (g : G) L :=
        mem_conjSubgroup.mpr (Subgroup.mem_subgroupOf.mp h1)
      exact hcomm g g.2 n hn l hl')
    (fun x hx => hLN hx)
    (fun l hl l' hl' => ⟨(hab l hl l' hl').1, (hab l hl l' hl').2⟩)
    (τ := ⟨τ, hτR⟩)
    (Subgroup.mem_normalizer_iff.mpr fun x => by
      have := Subgroup.mem_normalizer_iff.mp hτL (x : G)
      exact this)
    (fun l hl h => hτ l hl h)
    (fun r hr => by
      have hsup : (L.subgroupOf R ⊔ N.subgroupOf R : Subgroup ↥R) = (L ⊔ N).subgroupOf R :=
        (Subgroup.subgroupOf_sup hLR hNR).symm
      rw [hsup] at hr
      have hrG : (r : G) ∈ Subgroup.normalizer ((L ⊔ N : Subgroup G) : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        have hxR : x ∈ R := (sup_le hLR hNR) hx
        have h1 := (Subgroup.mem_normalizer_iff.mp hr ⟨x, hxR⟩).mp
          (show (⟨x, hxR⟩ : ↥R) ∈ (L ⊔ N).subgroupOf R from hx)
        exact h1
      have hrL := hnorm r r.2 hrG
      refine Subgroup.mem_normalizer_fintype fun a ha => ?_
      have h2 := Subgroup.mem_normalizer_iff.mp hrL (a : G)
      exact h2.mp ha)
    φ hker b hP hb
  intro n hn
  exact key (show (⟨n, hNR hn⟩ : ↥R) ∈ N.subgroupOf R from hn)

end CFSG.RankThree.GF2n.Stroth80
