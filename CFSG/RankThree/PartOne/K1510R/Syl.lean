module

public import CFSG.RankThree.PartOne.S12.Sec159FiveSyl
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.RankThree.PartOne.S12.Sec12FusChoice

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec159Five

variable {G : Type} [Group G]

theorem exists_sylow5' {p : ℕ} (hp : p.Prime) [Finite G] (h155 : Node155) {A E X : Subgroup G}
    {c : G} {L : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hxX : ∀ y ∈ X, x * y = y * x) (hxnot : x ∉ X) (hEX : E ≤ Subgroup.normalizer (X : Set G)) :
    ∃ P : Subgroup G, IsSylowOf p P (X ⊔ E) ∧ E ≤ P ∧ P ≤ torusNormalizer E ∧ omegaOne p P = E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h := h15.h12
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEp : IsPGroup p ↥E := hEel.isPGroup p ↥E
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hle : E ≤ (X ⊔ E) ⊓ Subgroup.normalizer (E : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  obtain ⟨Q₀, hQ0, hEQ⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hle hEp
  have hQM : IsSylowOf p Q₀ (X ⊔ E) := Sec15FA.sylow_of_torus_normalizer hJ hQ0 hEQ
  have hQW : Q₀ ≤ Subgroup.normalizer (E : Set G) := hQ0.1.trans inf_le_right
  have hQsup : Q₀ ≤ X ⊔ E := hQ0.1.trans inf_le_left
  obtain ⟨PW, hPW, hQPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hQW hQ0.2.1
  refine ⟨Q₀, hQM, hEQ, hQW, le_antisymm ?_ ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyQ, hyp⟩
    rcases h155 G p A c L E h15 hF hout' PW hPW with hΩ | ⟨h5, hp5, hF3, hJX⟩
    · have : y ∈ omegaOne p PW := Subgroup.subset_closure ⟨hQPW hyQ, hyp⟩
      rw [hΩ] at this
      exact this
    · by_contra hyE
      have hy1 : y ≠ 1 := fun h1 => hyE (h1 ▸ E.one_mem)
      have hQnorm : Q₀ ≤ Subgroup.normalizer (X : Set G) :=
        hQsup.trans (sup_le Subgroup.le_normalizer hEX)
      have hxQ : x ∈ Q₀ := hEQ (hxE)
      obtain ⟨k, hk, e, he, hke⟩ : ∃ k ∈ X, ∃ e ∈ E, k * e = y := by
        have hy' : y ∈ ((X ⊔ E : Subgroup G) : Set G) := hQsup hyQ
        rw [Subgroup.coe_mul_of_right_le_normalizer_left X E hEX] at hy'
        obtain ⟨k, hk, e, he, hke⟩ := hy'
        exact ⟨k, hk, e, he, hke⟩
      have hxy : x * y = y * x := by
        rw [← hke]
        calc x * (k * e) = (x * k) * e := by group
          _ = (k * x) * e := by rw [hxX k hk]
          _ = k * (x * e) := by group
          _ = k * (e * x) := by
              rw [show x * e = e * x from
                congrArg Subtype.val (hEel.is_comm.comm ⟨x, hxE⟩ ⟨e, he⟩)]
          _ = (k * e) * x := by group
      by_cases hT : Q₀ ⊓ X = ⊥
      · have hk1 : k = 1 := by
          have hkQ : k ∈ Q₀ ⊓ X := ⟨by
            have : k = y * e⁻¹ := by rw [← hke]; group
            rw [this]; exact Q₀.mul_mem hyQ (Q₀.inv_mem (hEQ he)), hk⟩
          rw [hT, Subgroup.mem_bot] at hkQ
          exact hkQ
        rw [hk1, one_mul] at hke
        exact hyE (hke ▸ he)
      · obtain ⟨z, hzQX, hz1, hzp, hzc⟩ :=
          exists_central_of_normal (p := p) hQ0.2.1 hQnorm hT
        have hzQ : z ∈ Q₀ := hzQX.1
        have hzX : z ∈ X := hzQX.2
        have hzE : z ∈ E := by
          have hzel : IsElementaryAbelian p ↥(Subgroup.zpowers z) :=
            IsElementaryAbelian.zpowers_of_pow_eq_one hzp
          have hzcent : Subgroup.zpowers z ≤ Subgroup.centralizer (E : Set G) := by
            refine Subgroup.zpowers_le.2 ?_
            rw [Subgroup.mem_centralizer_iff]
            intro e' he'
            exact hzc e' (hEQ he')
          have : IsElementaryAbelian p ↥E := hEel
          have hF₂ : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers z : Subgroup G) :=
            IsElementaryAbelian.sup_of_le_centralizer (E := E) (C := Subgroup.zpowers z) hzcent
          have hF₂A : E ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (A : Set G) := by
            refine sup_le h.E_le (Subgroup.zpowers_le.2 ?_)
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            exact hzc a (hEQ (h.A_le_E ha))
          have heq := h.E_max _ hF₂ hF₂A le_sup_left
          rw [← heq]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
        have hxp : x ^ p = 1 := hexp x (hxE)
        have hxz : x * z = z * x := hzc x hxQ
        have hyz : y * z = z * y := hzc y hyQ
        have hZ₀ : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ E :=
          sup_le (Subgroup.zpowers_le.2 (hxE)) (Subgroup.zpowers_le.2 hzE)
        have hdisj₁ : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers z) :=
          disjoint_zpowers_of_not_mem hxp hx1 (K := Subgroup.zpowers z) (fun hx' =>
            hxnot (Subgroup.zpowers_le.2 hzX hx'))
        have hZ₀card : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) = p ^ 2 := by
          rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
            (zpowers_le_normalizer_of_commute hxz) hdisj₁, Nat.card_zpowers, Nat.card_zpowers,
            orderOf_eq_prime hxp hx1, orderOf_eq_prime hzp hz1]
          ring
        have hZ₀el : IsElementaryAbelian p ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) := by
          have h1 : IsElementaryAbelian p ↥(Subgroup.zpowers x) :=
            IsElementaryAbelian.zpowers_of_pow_eq_one hxp
          have h2 : IsElementaryAbelian p ↥(Subgroup.zpowers z) :=
            IsElementaryAbelian.zpowers_of_pow_eq_one hzp
          have hcz : Subgroup.zpowers z ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
            refine Subgroup.zpowers_le.2 ?_
            rw [Subgroup.mem_centralizer_iff]
            intro g hg
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
            exact ((Commute.zpow_left (show Commute x z from hxz) n)).eq
          exact IsElementaryAbelian.sup_of_le_centralizer (E := Subgroup.zpowers x)
            (C := Subgroup.zpowers z) hcz
        have hyp' : y ^ p = 1 := hyp
        have hyZ₀ : y ∉ (Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) := fun hy' => hyE (hZ₀ hy')
        have hdisj₂ : Disjoint (Subgroup.zpowers x ⊔ Subgroup.zpowers z) (Subgroup.zpowers y) :=
          (disjoint_zpowers_of_not_mem hyp' hy1 hyZ₀).symm
        have hyc : Subgroup.zpowers y ≤
            Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
          have : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
              Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
            refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
            · rw [Subgroup.mem_centralizer_iff]
              intro g hg
              obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
              exact ((Commute.zpow_left (show Commute y x from hxy.symm) n)).eq
            · rw [Subgroup.mem_centralizer_iff]
              intro g hg
              obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
              exact ((Commute.zpow_left (show Commute y z from hyz) n)).eq
          exact Subgroup.le_centralizer_iff.1 this
        have hFcard : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers y :
            Subgroup G) = p ^ 3 := by
          rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
            (hyc.trans (Subgroup.centralizer_le_normalizer _)) hdisj₂, hZ₀card, Nat.card_zpowers,
            orderOf_eq_prime hyp' hy1]
          ring
        have hFel : IsElementaryAbelian p
            ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers y : Subgroup G) := by
          have h2 : IsElementaryAbelian p ↥(Subgroup.zpowers y) :=
            IsElementaryAbelian.zpowers_of_pow_eq_one hyp'
          exact IsElementaryAbelian.sup_of_le_centralizer (E := Subgroup.zpowers x ⊔ Subgroup.zpowers z)
            (C := Subgroup.zpowers y) hyc
        have hFQ : Subgroup.zpowers x ⊔ Subgroup.zpowers z ⊔ Subgroup.zpowers y ≤ Q₀ :=
          sup_le (sup_le (Subgroup.zpowers_le.2 hxQ) (Subgroup.zpowers_le.2 hzQ))
            (Subgroup.zpowers_le.2 hyQ)
        have hFE := hF3 _ (hFQ.trans hQPW) hFel hFcard
        exact hyE (hFE (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
  · exact fun e he => Subgroup.subset_closure ⟨hEQ he, hexp e he⟩

end CFSG.RankThree.PartOne.K1510R
