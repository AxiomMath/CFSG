module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93SLElat
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec312SLData
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec57B

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

section Action

variable {m : ℕ} {K : Type} [Field K] {G : Type} [Group G] {R X : Subgroup G}

@[expose] noncomputable def actLin (hXR : X ≤ R) (φ : ↥R →* GL (Fin m) K) :
    ↥X →* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
  matToLin.toMonoidHom.comp (φ.comp (Subgroup.inclusion hXR))

theorem actLin_apply (hXR : X ≤ R) (φ : ↥R →* GL (Fin m) K) (s : ↥X) (v : Fin m → K) :
    actLin hXR φ s v = (φ (Subgroup.inclusion hXR s) : Matrix (Fin m) (Fin m) K) *ᵥ v :=
  matToLin_apply _ v

theorem actLin_elation {L : Subgroup G} (hXR : X ≤ R) (hLX : L ≤ X) (φ : ↥R →* GL (Fin m) K)
    (u : Fin m → K)
    (hel : ∀ l : ↥R, (l : G) ∈ L → ∃ f : Fin m → K, f ⬝ᵥ u = 0 ∧
      (φ l : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u f)
    (hfull : ∀ f : Fin m → K, f ⬝ᵥ u = 0 → ∃ l : ↥R, (l : G) ∈ L ∧
      (φ l : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u f) :
    (∀ (l : G) (hl : l ∈ L), ∃ f : Module.Dual K (Fin m → K), f u = 0 ∧
      ∀ v, actLin hXR φ ⟨l, hLX hl⟩ v = v + f v • u) ∧
    (∀ f : Module.Dual K (Fin m → K), f u = 0 → ∃ (l : G) (hl : l ∈ L),
      ∀ v, actLin hXR φ ⟨l, hLX hl⟩ v = v + f v • u) := by
  classical
  refine ⟨fun l hl => ?_, fun g hg => ?_⟩
  · obtain ⟨f, hf0, hf⟩ := hel ⟨l, hXR (hLX hl)⟩ hl
    refine ⟨dotProductEquiv K (Fin m) f, by simpa using hf0, fun v => ?_⟩
    rw [actLin_apply]
    show (φ ⟨l, hXR (hLX hl)⟩ : Matrix (Fin m) (Fin m) K) *ᵥ v = _
    rw [hf, mulVec_one_add_vecMulVec]
    simp
  · obtain ⟨f, rfl⟩ := (dotProductEquiv K (Fin m)).surjective g
    obtain ⟨l, hl, hφ⟩ := hfull f (by simpa using hg)
    refine ⟨(l : G), hl, fun v => ?_⟩
    rw [actLin_apply]
    show (φ l : Matrix (Fin m) (Fin m) K) *ᵥ v = _
    rw [hφ, mulVec_one_add_vecMulVec]
    simp

end Action

theorem slPair_quotSat (h34 : Stroth34Statement)
    (ha : Stroth311aStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
      Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
      ∀ (t : G), t ∈ LB M Q B → t ∉ Q →
      ∀ (L₁ L₂ : Subgroup G), (∃ m ∈ M, L₁ = conjSubgroup m (LB M Q B)) →
        (∃ m ∈ M, L₂ = conjSubgroup m (LB M Q B)) → t ∈ L₁ → t ∈ L₂ → L₁ ≠ L₂ → SLNat hc t →
        QuotSat (L₁ ⊔ L₂) (inSubgroup (pCore 2) (L₁ ⊔ L₂)) (IsSLModel 2 (Nat.card Z)) := by
  classical
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ L₁ L₂ ⟨m₁, hm₁, hL₁⟩ ⟨m₂, hm₂, hL₂⟩ ht₁ ht₂ h12
    hSL
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  subst hL₁ hL₂
  have hLR₁ : conjSubgroup m₁ (LB M Q B) ≤ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm₁ ht₁
  have hLR₂ : conjSubgroup m₂ (LB M Q B) ≤ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm₂ ht₂
  have hXR : conjSubgroup m₁ (LB M Q B) ⊔ conjSubgroup m₂ (LB M Q B) ≤ Rt M (LB M Q B) t :=
    sup_le hLR₁ hLR₂
  have hR : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro hRL
    apply h12
    have c₁ : Nat.card (conjSubgroup m₁ (LB M Q B)) = Nat.card (LB M Q B) :=
      card_conjSubgroup _ _
    have c₂ : Nat.card (conjSubgroup m₂ (LB M Q B)) = Nat.card (LB M Q B) :=
      card_conjSubgroup _ _
    have e₁ : conjSubgroup m₁ (LB M Q B) = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge (hLR₁.trans hRL.le) c₁.ge
    have e₂ : conjSubgroup m₂ (LB M Q B) = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge (hLR₂.trans hRL.le) c₂.ge
    exact e₁.trans e₂.symm
  have hV : Vt M (LB M Q B) B Z t ≤ QB B := stroth310SL_of_34 h34 G M Q Z B hc n t hs hSL
  have hN2 : IsPGroup 2 ↥(hc.CN t) :=
    hc.isPGroup_CN_of_311 h34 hs (ha G M Q Z B hc n hw hn hno hgen t ht htQ hR)
  obtain ⟨K, fK, finK, chK, hK, m, hm, φ, hker, -, -, u, hu, hcross⟩ :=
    stroth310SLTransvConj_of_34 h34 G M Q Z B hc n t hs hR hV
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨hu₁0, hel₁, hfull₁⟩ := hu m₁ hm₁ ht₁
  obtain ⟨hu₂0, hel₂, hfull₂⟩ := hu m₂ hm₂ ht₂
  have hind : LinearIndependent K ![u m₁, u m₂] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    by_cases hc0 : c = 0
    · subst hc0
      rw [zero_smul, add_zero] at hac
      exact ⟨(smul_eq_zero.mp hac).resolve_right hu₁0, rfl⟩
    · exfalso
      apply h12
      refine hcross m₁ hm₁ m₂ hm₂ ht₁ ht₂ ⟨-(c⁻¹ * a), ?_⟩
      have h2 : c • u m₂ = -(a • u m₁) := eq_neg_of_add_eq_zero_right hac
      calc u m₂ = c⁻¹ • (c • u m₂) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = (-(c⁻¹ * a)) • u m₁ := by rw [h2, smul_neg, neg_smul, mul_smul]
  obtain ⟨hA₁, hB₁⟩ := actLin_elation hXR le_sup_left φ (u m₁) hel₁ hfull₁
  obtain ⟨hA₂, hB₂⟩ := actLin_elation hXR le_sup_right φ (u m₂) hel₂ hfull₂
  have hQS := elatPair_quotSat (K := K) (conjSubgroup m₁ (LB M Q B)) (conjSubgroup m₂ (LB M Q B))
    hq4 (u m₁) (u m₂) hind (actLin hXR φ) hA₁ hA₂ hB₁ hB₂ (fun s hs1 => by
      have h1 : φ (Subgroup.inclusion hXR s) = 1 := by
        apply matToLin.injective
        rw [map_one]
        exact hs1
      have h2 : Subgroup.inclusion hXR s ∈ φ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      obtain ⟨j, hj⟩ := hN2 ⟨((Subgroup.inclusion hXR s : ↥(Rt M (LB M Q B) t)) : G), h2⟩
      refine ⟨j, Subtype.ext ?_⟩
      have hj' : (((s : G)) ^ 2 ^ j) = 1 := by
        simpa using congrArg (fun z : ↥(hc.CN t) => (z : G)) hj
      simpa using hj')
  rwa [hK] at hQS

end HS9

theorem step93SLCase_of (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) : Step93SLCaseStatement := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg x hxK hxQ hSL
  left
  have hxL : x ∈ LB M Q B := (Subgroup.mem_inf.mp hxK).1
  have hxLh : x ∈ conjSubgroup h (LB M Q B) := (Subgroup.mem_inf.mp hxK).2
  exact HS9.slPair_quotSat h34 h311a G M Q Z B hc n cfg.hs.toSec5.width cfg.hs.toSec5.n_gt
    cfg.hs.toSec5.noA2 cfg.hs.toSec5.gen x hxL hxQ (LB M Q B) (conjSubgroup h (LB M Q B))
    ⟨1, Subgroup.one_mem M, (conjSubgroup_one (LB M Q B)).symm⟩ ⟨h, cfg.hh, rfl⟩ hxL hxLh cfg.hne
    hSL

end CFSG.RankThree.GF2n.Stroth80
