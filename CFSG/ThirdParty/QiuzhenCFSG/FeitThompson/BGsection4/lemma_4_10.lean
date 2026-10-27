module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_b

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints

/-! # Infrastructure for Lemma 4.10 from BG Section 4 -/

section Main

open scoped FixedPoints
public theorem CFSG.natCard_omega₁_cyclic_quotient_eq_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] (hcyc : IsCyclic G) [Nontrivial G] :
    Nat.card (omega₁ (G := G) (p := p)) = p := by
  classical
  letI : IsCyclic G := hcyc
  letI : CommGroup G := hcyc.commGroup
  have hOmega_eq_ker : omega₁ (G := G) (p := p) = (powMonoidHom p : G →* G).ker := by
    apply le_antisymm
    · rw [omega₁, omega]
      refine (Subgroup.closure_le (K := (powMonoidHom p : G →* G).ker)).2 ?_
      intro x hx
      change x ^ (p ^ 1) = 1 at hx
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
    · intro x hx
      change x ∈ Subgroup.closure {y : G | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
  obtain ⟨n, hn_pos, hcardG⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := G) (hG := Fact.out)).mp inferInstance
  calc
    Nat.card (omega₁ (G := G) (p := p))
        = Nat.card ((powMonoidHom p : G →* G).ker) := by rw [hOmega_eq_ker]
    _ = (Nat.card G).gcd p := IsCyclic.card_powMonoidHom_ker (G := G) p
    _ = p := by
      rw [hcardG]
      exact Nat.gcd_eq_right_iff_dvd.mpr (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos))

public theorem CFSG.omega₁_map_subtype_le
    {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) :
    (omega₁ (G := H) (p := p)).map H.subtype ≤ omega₁ (G := G) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := omega₁ (G := G) (p := p))).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.subset_closure ?_
  simpa [pow_one] using congrArg H.subtype hx

public theorem CFSG.omega₁_map_subtype_le_map_subtype_of_le
    {G : Type*} [Group G] {p : ℕ} {H K : Subgroup G} (hHK : H ≤ K) :
    (omega₁ (G := H) (p := p)).map H.subtype ≤
      (omega₁ (G := K) (p := p)).map K.subtype := by
  rw [omega₁, omega, MonoidHom.map_closure]
  refine (Subgroup.closure_le (K := (omega₁ (G := K) (p := p)).map K.subtype)).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  let xK : K := ⟨(x : G), hHK x.2⟩
  have hxG : (x : G) ^ p = 1 := by
    simpa using congrArg H.subtype hx
  have hxΩK : xK ∈ omega₁ (G := K) (p := p) := by
    change xK ∈ Subgroup.closure {y : K | y ^ (p ^ 1) = 1}
    exact Subgroup.subset_closure (by simpa [xK, pow_one] using hxG)
  exact Subgroup.mem_map_of_mem K.subtype hxΩK


private theorem CFSG.omega₁_le_map_subtype_of_forall_pow_eq_one_mem
    {G : Type*} [Group G] {p : ℕ} (H : Subgroup G)
    (hmem : ∀ x : G, x ^ p = 1 → x ∈ H) :
    omega₁ (G := G) (p := p) ≤ (omega₁ (G := H) (p := p)).map H.subtype := by
  rw [omega₁, omega]
  refine (Subgroup.closure_le (K := (omega₁ (G := H) (p := p)).map H.subtype)).2 ?_
  intro x hx
  have hxH : x ∈ H := hmem x (by simpa [pow_one] using hx)
  have hxOmegaH : ⟨x, hxH⟩ ∈ omega₁ (G := H) (p := p) := by
    change ⟨x, hxH⟩ ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hx
  exact Subgroup.mem_map_of_mem H.subtype hxOmegaH

public theorem CFSG.omega₁_preimage_eq_map_omega₁
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (T : Subgroup R)
    (hOmegaR_le_T : omega₁ (G := R) (p := p) ≤ T) :
    (omega₁ (G := T) (p := p)).map T.subtype = omega₁ (G := R) (p := p) := by
  apply le_antisymm
  · exact omega₁_map_subtype_le T
  · exact omega₁_le_map_subtype_of_forall_pow_eq_one_mem T (fun x hx => hOmegaR_le_T <| by
      exact Subgroup.subset_closure (by simpa [pow_one] using hx))

end Main

/-! # Lemma 4.10 from BG Section 4 -/

section Main

open scoped FixedPoints
public theorem CFSG.lemma_4_10 {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (hmeta : IsMetacyclic R) (hncyc : ¬ IsCyclic R) :
    Nat.card (omega₁ (G := R) (p := p)) = p ^ 2 ∧
      IsElementaryAbelian p (omega₁ (G := R) (p := p)) := by
  classical
  obtain ⟨S, hS_normal, hS_cyclic, hquot_cyclic⟩ := hmeta
  letI : S.Normal := hS_normal
  letI : IsCyclic S := hS_cyclic
  let q : R →* R ⧸ S := QuotientGroup.mk' S
  let Tbar : Subgroup (R ⧸ S) := omega₁ (G := R ⧸ S) (p := p)
  let T : Subgroup R := Tbar.comap q
  have hS_ne_top : S ≠ ⊤ := by
    intro hStop
    have hcycR : IsCyclic R := by
      have hcyc_top : IsCyclic (⊤ : Subgroup R) := by
        exact (MulEquiv.subgroupCongr hStop).isCyclic.1 hS_cyclic
      exact (Subgroup.topEquiv.isCyclic).1 hcyc_top
    exact hncyc hcycR
  have hRquot_p : IsPGroup p (R ⧸ S) := (Fact.out : IsPGroup p R).to_quotient S
  letI : Fact (IsPGroup p (R ⧸ S)) := ⟨hRquot_p⟩
  have hquot_nontriv : Nontrivial (R ⧸ S) :=
    (QuotientGroup.nontrivial_iff (G := R) (N := S)).2 hS_ne_top
  letI : Nontrivial (R ⧸ S) := hquot_nontriv
  have hTbar_char : Tbar.Characteristic := by
    simpa [Tbar] using omega₁_characteristic (G := R ⧸ S) (p := p)
  letI : Tbar.Characteristic := hTbar_char
  have hTbar_normal : Tbar.Normal := by infer_instance
  have hT_normal : T.Normal := by
    exact hTbar_normal.comap q
  letI : T.Normal := hT_normal
  have hTbar_card : Nat.card Tbar = p :=
    natCard_omega₁_cyclic_quotient_eq_prime (G := R ⧸ S) (p := p) hquot_cyclic
  have hS_le_T : S ≤ T := by
    intro x hxS
    exact (Subgroup.ker_le_comap (f := q) (H := Tbar)) <| by
      simpa [q, QuotientGroup.ker_mk'] using hxS
  have hOmegaR_le_T : omega₁ (G := R) (p := p) ≤ T := by
    rw [omega₁, omega]
    refine (Subgroup.closure_le (K := T)).2 ?_
    intro x hx
    change q x ∈ Subgroup.closure {y : R ⧸ S | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [q, Tbar] using congrArg q hx
  have hOmega_eq :
      (omega₁ (G := T) (p := p)).map T.subtype = omega₁ (G := R) (p := p) :=
    omega₁_preimage_eq_map_omega₁ (R := R) (p := p) T hOmegaR_le_T
  have hT_quot_card : Nat.card (T ⧸ S.subgroupOf T) = p := by
    simpa [T, Tbar, q] using
        (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective S)
          (H := Tbar)).trans hTbar_card
  have hS_subT_card : Nat.card (S.subgroupOf T) = Nat.card S := by
    exact natCard_subgroupOf_eq S T hS_le_T
  have hT_not_cyclic : ¬ IsCyclic T := by
    intro hTcyc
    have hOmegaT_card : Nat.card (omega₁ (G := T) (p := p)) = p := by
      have hTquot_nontriv : Nontrivial (T ⧸ S.subgroupOf T) := by
        have hcard_gt : 1 < Nat.card (T ⧸ S.subgroupOf T) := by
          rw [hT_quot_card]
          exact (Fact.out : Nat.Prime p).one_lt
        exact (Finite.one_lt_card_iff_nontrivial).1 hcard_gt
      letI : Nontrivial (T ⧸ S.subgroupOf T) := hTquot_nontriv
      have hT_nontriv : Nontrivial T := (QuotientGroup.mk'_surjective (S.subgroupOf T)).nontrivial
      letI : Nontrivial T := hT_nontriv
      have hTp : IsPGroup p T := (Fact.out : IsPGroup p R).to_subgroup T
      letI : Fact (IsPGroup p T) := ⟨hTp⟩
      exact natCard_omega₁_cyclic_quotient_eq_prime (G := T) (p := p) hTcyc
    have hOmegaR_card_eq : Nat.card (omega₁ (G := R) (p := p)) = p := by
      calc
        Nat.card (omega₁ (G := R) (p := p))
            = Nat.card ((omega₁ (G := T) (p := p)).map T.subtype) := by rw [← hOmega_eq]
        _ = Nat.card (omega₁ (G := T) (p := p)) :=
          Subgroup.card_map_of_injective (K := omega₁ (G := T) (p := p))
            (f := T.subtype) T.subtype_injective
        _ = p := hOmegaT_card
    have hOmegaR_card_le : Nat.card (omega₁ (G := R) (p := p)) ≤ p := by
      rw [hOmegaR_card_eq]
    obtain ⟨A, hA_normal, hA_card, hA_elem⟩ := lemma_4_5_a (R := R) (p := p) hpodd hncyc
    have hA_le_OmegaR : A ≤ omega₁ (G := R) (p := p) := elementaryAbelian_le_omega₁
    have hA_card_le : Nat.card A ≤ Nat.card (omega₁ (G := R) (p := p)) :=
      Subgroup.card_le_of_le hA_le_OmegaR
    have hp_sq_le_p : p ^ 2 ≤ p := by
      simpa [hA_card] using le_trans hA_card_le hOmegaR_card_le
    have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
    exact (not_le_of_gt hp_lt_sq) hp_sq_le_p
  have hindex : ∃ U : Subgroup T, IsCyclic U ∧ Nat.card (T ⧸ U) = p := by
    refine ⟨S.subgroupOf T, ?_, hT_quot_card⟩
    exact (Subgroup.subgroupOfEquivOfLe (H := S) (K := T) hS_le_T).isCyclic.2
      hS_cyclic
  have hTp : IsPGroup p T := (Fact.out : IsPGroup p R).to_subgroup T
  letI : Fact (IsPGroup p T) := ⟨hTp⟩
  obtain ⟨hOmegaT_card_sq, hOmegaT_elem⟩ :=
    lemma_4_5_b (R := T) (p := p) hpodd hT_not_cyclic hindex
  constructor
  · calc
      Nat.card (omega₁ (G := R) (p := p))
          = Nat.card ((omega₁ (G := T) (p := p)).map T.subtype) := by rw [← hOmega_eq]
      _ = Nat.card (omega₁ (G := T) (p := p)) :=
        Subgroup.card_map_of_injective (K := omega₁ (G := T) (p := p))
          (f := T.subtype) T.subtype_injective
      _ = p ^ 2 := hOmegaT_card_sq
  · let e : omega₁ (G := T) (p := p) ≃* (omega₁ (G := T) (p := p)).map T.subtype :=
      Subgroup.equivMapOfInjective (omega₁ (G := T) (p := p)) T.subtype T.subtype_injective
    letI : IsElementaryAbelian p (omega₁ (G := T) (p := p)) := hOmegaT_elem
    have hElem_map : IsElementaryAbelian p ((omega₁ (G := T) (p := p)).map T.subtype) := by
      refine {
        toIsMulCommutative := inferInstance
        exponent_dvd_p := ?_
      }
      rw [← Monoid.exponent_eq_of_mulEquiv e]
      exact IsElementaryAbelian.exponent_dvd_p p (omega₁ (G := T) (p := p))
    exact hOmega_eq ▸ hElem_map

end Main
