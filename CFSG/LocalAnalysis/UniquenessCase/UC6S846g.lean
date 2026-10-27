module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846f
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

noncomputable def bar2Equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ CFSG.pCore 2 A) ≃* (B ⧸ CFSG.pCore 2 B) :=
  QuotientGroup.congr (CFSG.pCore 2 A) (CFSG.pCore 2 B) e (CFSG.pCore_map_iso 2 e)

theorem mem_normalizer_iff_map_conj {L : Subgroup G} {g : G} :
    g ∈ normalizer (L : Set G) ↔ L.map (MulAut.conj g).toMonoidHom = L := by
  constructor
  · intro hg
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) x).1 hx
      simpa using this
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h1
      rw [← this]
      exact hy

theorem calC_map (M : Subgroup G) (f : MulAut G) (hM : M.map f.toMonoidHom = M) {L : Subgroup G}
    (hL : L ∈ calC M) : L.map f.toMonoidHom ∈ calC M := by
  obtain ⟨hsn, hp, hq⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · have := hsn.map f.toMonoidHom
    rwa [hM] at this
  · rw [← Subgroup.map_commutator, hp]
  · let e : ↥L ≃* ↥(L.map f.toMonoidHom) :=
      Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
    exact hq.of_mulEquiv (bar2Equiv e).symm

theorem card_center_bar2_map (f : MulAut G) (L : Subgroup G) :
    Nat.card (center (Bar2 (L.map f.toMonoidHom))) = Nat.card (center (Bar2 L)) := by
  let e : ↥L ≃* ↥(L.map f.toMonoidHom) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  exact (Nat.card_congr (Subgroup.centerCongr (bar2Equiv e)).toEquiv).symm

theorem calC_subgroupOf {M L : Subgroup G} (hL : L ∈ calC M) :
    CFSG.Open.IsSubnormal (L.subgroupOf M) ⊤ ∧ ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M ∧
      CFSG.Open.IsQuasisimple (↥(L.subgroupOf M) ⧸ CFSG.pCore 2 ↥(L.subgroupOf M)) ∧
      Nat.card (center (↥(L.subgroupOf M) ⧸ CFSG.pCore 2 ↥(L.subgroupOf M))) =
        Nat.card (center (Bar2 L)) := by
  obtain ⟨hsn, hp, hq⟩ := hL
  have hLM : L ≤ M := hsn.le
  let e : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLM
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hsn.comap M.subtype
    rwa [show M.comap M.subtype = ⊤ from Subgroup.subgroupOf_self M] at this
  · apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLM, hp]
  · exact hq.of_mulEquiv (bar2Equiv e)
  · exact Nat.card_congr (Subgroup.centerCongr (bar2Equiv e)).toEquiv

theorem calCRankTwice (M : Subgroup G) : CalCRankTwice M := by
  intro L hL hnN q hq hq2 hZ E hEL hEel a hEc
  obtain ⟨m, hmM, hmN⟩ : ∃ m ∈ M, m ∉ normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hnN h
  let f : MulAut G := MulAut.conj m
  have hM : M.map f.toMonoidHom = M :=
    mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hL' : L.map f.toMonoidHom ∈ calC M := calC_map M f hM hL
  have hne : L ≠ L.map f.toMonoidHom := fun h => hmN (mem_normalizer_iff_map_conj.2 h.symm)
  obtain ⟨hsn, hp, hqs, hcen⟩ := calC_subgroupOf hL
  obtain ⟨hsn', hp', hqs', hcen'⟩ := calC_subgroupOf hL'
  have hLM : L ≤ M := hL.1.le
  have hL'M : L.map f.toMonoidHom ≤ M := hL'.1.le
  have hne' : L.subgroupOf M ≠ (L.map f.toMonoidHom).subgroupOf M := by
    intro h
    apply hne
    have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hLM, Subgroup.map_subgroupOf_eq_of_le hL'M] at this
  have hEL' : E.map f.toMonoidHom ≤ L.map f.toMonoidHom := Subgroup.map_mono hEL
  have hE'el : IsElemAbelian q (E.map f.toMonoidHom) := hEel.map _
  have hE'c : Nat.card (E.map f.toMonoidHom) = q ^ a := by
    rw [Subgroup.card_map_of_injective f.injective, hEc]
  have hE'M : E.map f.toMonoidHom ≤ M := hEL'.trans hL'M
  have hEM : E ≤ M := hEL.trans hLM
  obtain ⟨W, hWel, hWcard⟩ := rank_add_of_ne (A := L.subgroupOf M) (A' := (L.map f.toMonoidHom).subgroupOf M)
    (E := E.subgroupOf M) (E' := (E.map f.toMonoidHom).subgroupOf M) hq hq2 hsn hp hqs hsn' hp' hqs' hne'
    (by rw [hcen]; exact hZ) (fun x hx => hEL hx) (fun x hx => hEL' hx)
    (hEel.subgroupOf M) (hE'el.subgroupOf M)
    (by rw [← hEc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv)
    (by rw [← hE'c]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M).toEquiv)
  have hW := le_pRank' hq (E := W.map M.subtype) (H := M) (Subgroup.map_subtype_le W)
    (hWel.map _) (by rw [Subgroup.card_map_of_injective M.subtype_injective, hWcard])
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
