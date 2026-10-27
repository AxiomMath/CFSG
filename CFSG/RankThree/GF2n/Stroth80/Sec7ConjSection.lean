module

public import CFSG.RankThree.GF2n.Stroth80.Sec7SecModEmbed
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_conj_section_data (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) (hx2 : x ^ 2 ∈ Q) :
    ∃ (Md : Type) (_ : AddCommGroup Md) (_ : DistribMulAction ↥(Rt M (LB M Q B) t) Md)
      (κ : ↥(Wt Q (Vt M (LB M Q B) B Z t)) →* Multiplicative Md)
      (_ : IsSecMod (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
        (Vt M (LB M Q B) B Z t) Md κ) (S : Md →+ Md),
      (∀ (r : ↥(Rt M (LB M Q B) t)) (a : Md), S (r • a) = r • S a) ∧ (∀ a : Md, S (S a) = a) ∧
      ∀ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)), ∃ w' : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
        (w' : G) = x * w * x⁻¹ ∧ κ w' = Multiplicative.ofAdd (S (Multiplicative.toAdd (κ w))) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  set V := Vt M (LB M Q B) B Z t with hVdef
  set W := Wt Q V with hWdef
  set R := Rt M (LB M Q B) t with hRdef
  have hVW : V ≤ W := sec7_V_le_W h310chi hc hs
  have hWQ : W ≤ Q := inf_le_left
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : R ≤ M := hc.Rt_le_M t
  have hxVn : x ∈ Subgroup.normalizer (V : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
  have hxQn : x ∈ Subgroup.normalizer (Q : Set G) := hQM hxM
  have hnormW : ∀ l, l ∈ Subgroup.normalizer (Q : Set G) →
      l ∈ Subgroup.normalizer (V : Set G) → l ∈ Subgroup.normalizer (W : Set G) :=
    fun l hlQ hlV => Subgroup.mem_normalizer_fintype fun w hw => conj_mem_Wt hlQ hlV hw
  let R' : Subgroup G := Subgroup.normalizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G)
  have hsec : SecHyp R' W V :=
    ⟨hVW, fun a ha b hb => hZV (hc.hyp.toHyp79.comm_mem_V (hWQ ha) (hWQ hb)),
      fun a ha => hZV (hc.hyp.toHyp79.sq_mem_V (hWQ ha)),
      fun r hr a ha => (Subgroup.mem_normalizer_iff.mp hr.1 a).mp ha,
      fun r hr a ha => (Subgroup.mem_normalizer_iff.mp hr.2 a).mp ha⟩
  have hRR' : ∀ r ∈ R, r ∈ R' := fun r hr => by
    have hrV : r ∈ Subgroup.normalizer (V : Set G) := hc.Rt_normalizes_Vt ht hr
    exact ⟨hnormW r (hQM (hRM hr)) hrV, hrV⟩
  have hxR' : x ∈ R' := ⟨hnormW x hxQn hxVn, hxVn⟩
  obtain ⟨Md, iD, iA, κ, hκ⟩ := exists_sectionModule hsec
  let xR : ↥R' := ⟨x, hxR'⟩
  have hNtriv : ∀ k : ↥R', (k : G) ∈ hc.CN t → ∀ b : Md, k • b = b := by
    intro k hk b
    obtain ⟨w, rfl⟩ : ∃ w : ↥W, Multiplicative.toAdd (κ w) = b := by
      obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd b)
      exact ⟨w, by rw [hw]; rfl⟩
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp k.2.1 w).mp w.2
    have h1 := hκ.act k w ⟨(k : G) * w * (k : G)⁻¹, hkw⟩ rfl
    have h2 : κ ⟨(k : G) * w * (k : G)⁻¹, hkw⟩ = κ w := by
      rw [hκ.eq_iff]
      have e : (k : G) * w * (k : G)⁻¹ * (w : G)⁻¹ = ⁅(k : G), (w : G)⁆ := by
        simp only [commutatorElement_def]
      show (k : G) * w * (k : G)⁻¹ * (w : G)⁻¹ ∈ V
      rw [e]
      exact hWN _ hk _ w.2
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at h3
    exact h3.symm
  have hRle : R ≤ R' := fun r hr => hRR' r hr
  let S : Md →+ Md := DistribSMul.toAddMonoidHom Md xR
  have hSa : ∀ a, S a = xR • a := fun a => rfl
  have hS2 : ∀ a : Md, S (S a) = a := by
    intro a
    obtain ⟨w, rfl⟩ : ∃ w : ↥W, Multiplicative.toAdd (κ w) = a := by
      obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
      exact ⟨w, by rw [hw]; rfl⟩
    have hxw : x * w * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn w.2
    have hxw' : x * (x * w * x⁻¹) * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn hxw
    have h1 := hκ.act xR w ⟨x * w * x⁻¹, hxw⟩ rfl
    have h2 := hκ.act xR ⟨x * w * x⁻¹, hxw⟩ ⟨x * (x * w * x⁻¹) * x⁻¹, hxw'⟩ rfl
    have h3 : κ ⟨x * (x * w * x⁻¹) * x⁻¹, hxw'⟩ = κ w := by
      rw [hκ.eq_iff]
      show x * (x * w * x⁻¹) * x⁻¹ * (w : G)⁻¹ ∈ V
      have e : x * (x * (w : G) * x⁻¹) * x⁻¹ * (w : G)⁻¹ = ⁅x ^ 2, (w : G)⁆ := by
        simp only [commutatorElement_def]
        rw [pow_two]
        group
      rw [e]
      exact hZV (hc.hyp.toHyp79.comm_mem_V hx2 (hWQ w.2))
    rw [hSa, hSa, ← toAdd_ofAdd (xR • Multiplicative.toAdd (κ w)), ← h1, ← toAdd_ofAdd (xR •
      Multiplicative.toAdd (κ ⟨x * w * x⁻¹, hxw⟩)), ← h2, h3]
  have hScomm : ∀ (r : G) (hr : r ∈ R) (a : Md),
      S ((⟨r, hRR' r hr⟩ : ↥R') • a) = (⟨r, hRR' r hr⟩ : ↥R') • S a := by
    intro r hr a
    have hcn : ⁅r, x⁆ ∈ hc.CN t := comm_mem_CN_of_vanish hc hs hxM hxt hxV hr
    have hcR' : ⁅r, x⁆ ∈ R' := hRR' _ (Ctx.mem_CN.mp hcn).1
    have hrel : (⟨⁅r, x⁆, hcR'⟩ : ↥R') * (xR * ⟨r, hRR' r hr⟩) = ⟨r, hRR' r hr⟩ * xR := by
      apply Subtype.ext
      show ⁅r, x⁆ * (x * r) = r * x
      simp only [commutatorElement_def]
      group
    have h1 : (⟨r, hRR' r hr⟩ : ↥R') • xR • a = xR • (⟨r, hRR' r hr⟩ : ↥R') • a := by
      rw [← mul_smul, ← hrel, mul_smul, hNtriv _ hcn, mul_smul]
    rw [hSa, hSa]
    exact h1.symm
  have hSw : ∀ w : ↥W, ∃ w' : ↥W, (w' : G) = x * w * x⁻¹ ∧
      κ w' = Multiplicative.ofAdd (S (Multiplicative.toAdd (κ w))) := by
    intro w
    have hxw : x * w * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn w.2
    exact ⟨⟨x * w * x⁻¹, hxw⟩, rfl, hκ.act xR w ⟨x * w * x⁻¹, hxw⟩ rfl⟩
  refine ⟨Md, iD, DistribMulAction.compHom Md (Subgroup.inclusion hRle), κ,
    isSecMod_restrict hRle hκ, S, ?_, hS2, hSw⟩
  intro r a
  exact hScomm (r : G) r.2 a

end CFSG.RankThree.GF2n.Stroth80
