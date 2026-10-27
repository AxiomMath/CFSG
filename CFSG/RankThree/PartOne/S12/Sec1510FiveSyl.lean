module

public import CFSG.RankThree.PartOne.S12.Sec159FiveSyl
public import CFSG.RankThree.PartOne.S12.Sec1510FiveDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.RankThree.PartOne.S12.Sec12FusChoice
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec1510Five

variable {G : Type} [Group G]

theorem isElementaryAbelian_of_le' {p : ℕ} {A K : Subgroup G} (hA : IsElementaryAbelian p ↥A)
    (hKA : K ≤ A) : IsElementaryAbelian p ↥K := CFSG.IsElementaryAbelian.of_le hA hKA

end Sec1510Five

namespace Sec1510Five

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_cent {p : ℕ} (hp : p.Prime) (h155 : Node155) {A E : Subgroup G} {c : G}
    {L : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {e : G} (heE : e ∈ E)
    (hcen : CentralizesE p E e) :
    ∃ P : Subgroup G, IsSylowOf p P (Subgroup.centralizer ({e} : Set G)) ∧ E ≤ P ∧
      P ≤ torusNormalizer E ∧ omegaOne p P = E ∧ ∀ x ∈ P, ∀ y ∈ E, x * y = y * x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h := h15.h12
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEp : IsPGroup p ↥E := hEel.isPGroup p ↥E
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hEC : E ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨e, heE⟩))
  have hle : E ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.normalizer (E : Set G) :=
    le_inf hEC Subgroup.le_normalizer
  obtain ⟨Q₀, hQ0, hEQ⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hle hEp
  have hQM : IsSylowOf p Q₀ (Subgroup.centralizer ({e} : Set G)) :=
    Sec15FA.sylow_of_torus_normalizer hJ hQ0 hEQ
  have hQW : Q₀ ≤ Subgroup.normalizer (E : Set G) := hQ0.1.trans inf_le_right
  have hQC : Q₀ ≤ Subgroup.centralizer ({e} : Set G) := hQ0.1.trans inf_le_left
  have hQp : IsPGroup p ↥Q₀ := hQ0.2.1
  have hPc : ∀ x ∈ Q₀, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := hQp ⟨x, hx⟩
    have hxk : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact hcen x (hQC hx) (hQW hx) ⟨k, hxk⟩ y hy
  obtain ⟨PW, hPW, hQPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hQW hQp
  refine ⟨Q₀, hQM, hEQ, hQW, ?_, hPc⟩
  refine le_antisymm ?_ ?_
  swap
  · exact fun x hx => Subgroup.subset_closure ⟨hEQ hx, hexp x hx⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro y ⟨hyQ, hyp⟩
  rcases h155 G p A c L E h15 hF hout' PW hPW with hΩ | ⟨h5, hp5, hF3, hJX⟩
  · have : y ∈ omegaOne p PW := Subgroup.subset_closure ⟨hQPW hyQ, hyp⟩
    rw [hΩ] at this
    exact this
  · by_contra hyE
    have hy1 : y ≠ 1 := fun h1 => hyE (h1 ▸ E.one_mem)
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p
      (show p ^ 2 ∣ Nat.card ↥E from ⟨p ^ 2, by rw [hEcard]; ring⟩)
    set E₂ : Subgroup G := K.map E.subtype with hE₂
    have hE₂E : E₂ ≤ E := by
      rintro _ ⟨k, -, rfl⟩
      exact k.2
    have hE₂card : Nat.card ↥E₂ = p ^ 2 := by
      rw [hE₂, Subgroup.card_map_of_injective E.subtype_injective]
      exact hK
    have hE₂el : IsElementaryAbelian p ↥E₂ := isElementaryAbelian_of_le' hEel hE₂E
    have hyE₂ : y ∉ E₂ := fun hy' => hyE (hE₂E hy')
    have hdisj : Disjoint (Subgroup.zpowers y) E₂ :=
      Sec159Five.disjoint_zpowers_of_not_mem hyp hy1 hyE₂
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer (E₂ : Set G) := by
      refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (hPc y hyQ g (hE₂E hg)).symm
    have hFcard : Nat.card ↥(E₂ ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 3 := by
      rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
        (hyc.trans (Subgroup.centralizer_le_normalizer _)) hdisj.symm, hE₂card, Nat.card_zpowers,
        orderOf_eq_prime hyp hy1]
      ring
    have hFel : IsElementaryAbelian p ↥(E₂ ⊔ Subgroup.zpowers y : Subgroup G) := by
      have h2 : IsElementaryAbelian p ↥(Subgroup.zpowers y) :=
        IsElementaryAbelian.zpowers_of_pow_eq_one hyp
      exact IsElementaryAbelian.sup_of_le_centralizer (E := E₂) (C := Subgroup.zpowers y) hyc
    have hFQ : E₂ ⊔ Subgroup.zpowers y ≤ Q₀ :=
      sup_le (hE₂E.trans hEQ) (Subgroup.zpowers_le.2 hyQ)
    have hFE := hF3 _ (hFQ.trans hQPW) hFel hFcard
    exact hyE (hFE (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

end Sec1510Five

end CFSG.RankThree.PartOne
