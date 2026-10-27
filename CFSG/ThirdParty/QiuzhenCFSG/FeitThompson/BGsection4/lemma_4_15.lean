module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Infrastructure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 4.15 from BG Section 4 -/

open scoped commutatorElement IsMulCommutative

section Main

public theorem CFSG.lemma_4_15 {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (S : Subgroup R) [IsExtraspecial p S]
    (hcomm : ⁅S, (⊤ : Subgroup R)⁆ ≤ (derivedSubgroup S).map S.subtype) :
    S ⊔ Subgroup.centralizer (S : Set R) = ⊤ := by
  classical
  have hS_normal : S.Normal := by
    refine ⟨?_⟩
    intro s hs r
    have hcomm_mem :
        ⁅r, s⁆ ∈ (derivedSubgroup S).map S.subtype := by
      have hcomm_mem' :
          ⁅s, r⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ := by
        exact Subgroup.commutator_mem_commutator
          (H₁ := S) (H₂ := (⊤ : Subgroup R)) hs (by simp)
      have hcomm_inv :
          ⁅r, s⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ := by
        simpa [commutatorElement_inv] using
          (⁅S, (⊤ : Subgroup R)⁆).inv_mem hcomm_mem'
      exact hcomm hcomm_inv
    rcases Subgroup.mem_map.mp hcomm_mem with ⟨c, hc, hc_eq⟩
    have hconj : r * s * r⁻¹ = c * s := by
      calc
        r * s * r⁻¹ = ⁅r, s⁆ * s := conjugate_eq_commutator_mul r s
        _ = (c : R) * s := by
          rw [← hc_eq]
          rfl
    exact hconj ▸ S.mul_mem c.property hs
  letI : S.Normal := hS_normal
  let ZS : Subgroup R := (Subgroup.center S).map S.subtype
  have hZS_normal : ZS.Normal := by
    letI : (Subgroup.center S).Characteristic := Subgroup.centerCharacteristic
    dsimp [ZS]
    exact ConjAct.normal_of_characteristic_of_normal
  letI : ZS.Normal := hZS_normal
  have hder_le_ZS : (derivedSubgroup S).map S.subtype ≤ ZS := by
    exact Subgroup.map_mono (commutator_le_center_of_isExtraspecial_local (q := p) (K := S))
  have hZS_card : Nat.card ZS = p := by
    calc
      Nat.card ZS = Nat.card (Subgroup.center S) := by
        exact Subgroup.card_map_of_injective (K := Subgroup.center S) (f := S.subtype)
          S.subtype_injective
      _ = p := IsExtraspecial.center_order_p p S
  have hZS_le_centerR : ZS ≤ Subgroup.center R :=
    normal_subgroup_card_eq_prime_le_center (G := R) (p := p) (N := ZS) hZS_card
  have hcenter_le_der : Subgroup.center S ≤ derivedSubgroup S := by
    have hder_ne_bot : derivedSubgroup S ≠ ⊥ := by
      intro hder_bot
      have hcomm_le_bot : commutator S ≤ (⊥ : Subgroup S) := by
        have hcomm_eq_bot : commutator S = (⊥ : Subgroup S) := by
          rw [← derivedSeries_one]
          exact hder_bot
        exact hcomm_eq_bot.le
      have hcommS : IsMulCommutative S := by
        refine ⟨⟨?_⟩⟩
        intro x y
        have hxy_mem : ⁅x, y⁆ ∈ (commutator S) :=
          Subgroup.commutator_mem_commutator
            (H₁ := (⊤ : Subgroup S)) (H₂ := (⊤ : Subgroup S)) (by simp) (by simp)
        have hxy_bot : ⁅x, y⁆ ∈ (⊥ : Subgroup S) := hcomm_le_bot hxy_mem
        have hxy_one : ⁅x, y⁆ = 1 := by simpa using hxy_bot
        exact commutatorElement_eq_one_iff_mul_comm.mp hxy_one
      have hcenter_top : Subgroup.center S = ⊤ := by
        ext x
        constructor
        · intro _; simp
        · intro _
          rw [Subgroup.mem_center_iff]
          intro y
          exact (mul_comm x y).symm
      have hquot_subsingleton : Subsingleton (S ⧸ Subgroup.center S) := by
        exact (QuotientGroup.subsingleton_iff (N := Subgroup.center S)).2 hcenter_top
      exact not_nontrivial_iff_subsingleton.mpr hquot_subsingleton
        (IsExtraspecial.quotient_nontrivial p S)
    exact center_le_of_le_center_ne_bot_of_prime_center_local
      (K := S) (q := p) (hcenter := IsExtraspecial.center_order_p p S)
      (commutator_le_center_of_isExtraspecial_local (q := p) (K := S))
      hder_ne_bot
  have hZS_le_der : ZS ≤ (derivedSubgroup S).map S.subtype := by
    exact Subgroup.map_mono hcenter_le_der
  have hder_eq_ZS : (derivedSubgroup S).map S.subtype = ZS :=
    le_antisymm hder_le_ZS hZS_le_der
  apply (Subgroup.eq_top_iff' (H := S ⊔ Subgroup.centralizer (S : Set R))).2
  intro r
  let α : MulAut S := MulAut.conjNormal (H := S) r
  have hαZ : ∀ z : Subgroup.center S, α z = z := by
    intro z
    apply Subtype.ext
    have hzR : ((z : S) : R) ∈ ZS := Subgroup.mem_map_of_mem S.subtype z.property
    have hzcentR : ((z : S) : R) ∈ Subgroup.center R := hZS_le_centerR hzR
    have hcommR : r * ((z : S) : R) = ((z : S) : R) * r :=
      (Subgroup.mem_center_iff.mp hzcentR) r
    have hconj : r * ((z : S) : R) * r⁻¹ = (z : S) := by
      calc
        r * ((z : S) : R) * r⁻¹ = (((z : S) : R) * r) * r⁻¹ := by rw [hcommR]
        _ = (z : S) := by simp [mul_assoc]
    simpa [α, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj
  have hαQ : ∀ x : S,
      (QuotientGroup.mk (α x) : S ⧸ Subgroup.center S) = QuotientGroup.mk x := by
    intro x
    apply (QuotientGroup.eq_iff_div_mem).2
    have hcomm_mem :
        ⁅r, ((x : S) : R)⁆ ∈ (derivedSubgroup S).map S.subtype := by
      have hcomm_mem' :
          ⁅((x : S) : R), r⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ := by
        exact Subgroup.commutator_mem_commutator
          (H₁ := S) (H₂ := (⊤ : Subgroup R)) x.property (by simp)
      have hcomm_inv :
          ⁅r, ((x : S) : R)⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ := by
        simpa [commutatorElement_inv] using
          (⁅S, (⊤ : Subgroup R)⁆).inv_mem hcomm_mem'
      exact hcomm hcomm_inv
    rcases Subgroup.mem_map.mp hcomm_mem with ⟨d, hd_der, hd_eq⟩
    have hd_center : d ∈ Subgroup.center S :=
      commutator_le_center_of_isExtraspecial_local (q := p) (K := S) hd_der
    have hconj : (α x : S) = d * x := by
      apply Subtype.ext
      calc
        ((α x : S) : R) = r * (x : S) * r⁻¹ := by rfl
        _ = ⁅r, ((x : S) : R)⁆ * (x : S) :=
          conjugate_eq_commutator_mul r ((x : S) : R)
        _ = (d : R) * (x : S) := by simpa using congrArg (fun t : R => t * (x : S)) hd_eq.symm
    rw [div_eq_mul_inv, hconj]
    simpa [mul_assoc] using hd_center
  obtain ⟨s, hs⟩ :=
    exists_inner_of_fix_center_and_quotient_of_isExtraspecial_local
      (q := p) (K := S) α hαZ hαQ
  have hrs : r ∈ S ⊔ Subgroup.centralizer (S : Set R) := by
    let c : R := s⁻¹ * r
    have hsS : (s : R) ∈ S := s.property
    have hc_cent : c ∈ Subgroup.centralizer (S : Set R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hhs := hs ⟨x, hx⟩
      have hhsR : r * x * r⁻¹ = (s : R) * x * (s : R)⁻¹ := by
        simpa [α, MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hhs
      have hmul := congrArg (fun t : R => (s : R)⁻¹ * t * r) hhsR
      simpa [c, mul_assoc] using hmul.symm
    exact (Subgroup.mem_sup_of_normal_left (s := S) (t := Subgroup.centralizer (S : Set R))).2
      ⟨s, hsS, c, hc_cent, by simp [c]⟩
  simpa using hrs
