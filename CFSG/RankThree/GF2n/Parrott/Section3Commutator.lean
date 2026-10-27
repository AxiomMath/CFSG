module

public import CFSG.RankThree.GF2n.Parrott.Section3Lift
public import CFSG.RankThree.GF2n.Parrott.InvariantComplement
public import CFSG.RankThree.GF2n.Parrott.CentralizerP
public import CFSG.RankThree.GF2n.Parrott.Section1Extraspecial

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

namespace GenericInvariantComplement

open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {σ : ↥(H z)}
variable [Fact (orderOf σ = 3)] [Fact (conjZ z σ = 1)]
variable {T F : Subgroup G}

theorem sigma_commute_of_mem_centerIn {y : G}
    (hy : y ∈ centerIn (J z)) : Commute (σ : G) y := by
  have hmem := centerIn_le_centralizer_of_conjZ_eq_one (z := z)
    (Fact.out : conjZ z σ = 1) hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm

theorem mul_self_eq_one_of_card_two (hT : Nat.card T = 2) (x : T) : x * x = 1 := by
  have h := pow_card_eq_one' (x := x)
  rw [hT] at h
  simpa [pow_two] using h

noncomputable def conjF (σ : ↥(H z)) (hsup : T ⊔ F = J z) : F →* J z :=
  (conjJ' z (σ)).toMonoidHom.comp (Subgroup.inclusion (F_le_J_of_sup hsup))

noncomputable def tMap (σ : ↥(H z)) (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) : F →* T :=
  (prT hdisj hcomm hsup).comp (conjF σ hsup)

noncomputable def phi (σ : ↥(H z)) (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) : F →* F :=
  (prF hdisj hcomm hsup).comp (conjF σ hsup)

noncomputable def psi (σ : ↥(H z)) (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) : F →* T :=
  (tMap σ hdisj hcomm hsup).comp (phi σ hdisj hcomm hsup)

theorem conjJ'_sigma_inclusion_T (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (t : T) :
    conjJ' z (σ) (Subgroup.inclusion (T_le_J_of_sup hsup) t) =
      Subgroup.inclusion (T_le_J_of_sup hsup) t := by
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  change (σ : G) * (t : G) * (σ : G)⁻¹ = (t : G)
  have hc : Commute (σ : G) (t : G) :=
    sigma_commute_of_mem_centerIn
      (T_le_centerIn_of_decomposition hT hcomm hsup t.2)
  rw [hc.eq]
  group

theorem conjJ'_sigma_pow_three :
    (conjJ' z (σ)) ^ 3 = 1 := by
  have h3 : σ ^ 3 = 1 := by
    rw [← (Fact.out : orderOf σ = 3)]
    exact pow_orderOf_eq_one _
  calc (conjJ' z (σ)) ^ 3
      = conjJ' z ((σ) ^ 3) := (map_pow (conjJ' z) (σ) 3).symm
    _ = conjJ' z 1 := by rw [h3]
    _ = 1 := map_one (conjJ' z)

theorem conjJ'_sigma_inclusion_F (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (f : F) :
    conjJ' z (σ) (Subgroup.inclusion (F_le_J_of_sup hsup) f) =
      Subgroup.inclusion (T_le_J_of_sup hsup) (tMap σ hdisj hcomm hsup f) *
        Subgroup.inclusion (F_le_J_of_sup hsup) (phi σ hdisj hcomm hsup f) := by
  exact Subtype.ext
    (prT_mul_prF hdisj hcomm hsup (conjF σ hsup f)).symm

theorem conjJ'_sigma_sq_inclusion_F (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    conjJ' z (σ)
        (conjJ' z (σ) (Subgroup.inclusion (F_le_J_of_sup hsup) f)) =
      Subgroup.inclusion (T_le_J_of_sup hsup) (tMap σ hdisj hcomm hsup f) *
        (Subgroup.inclusion (T_le_J_of_sup hsup)
            (tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) *
          Subgroup.inclusion (F_le_J_of_sup hsup)
            (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f))) := by
  rw [conjJ'_sigma_inclusion_F (σ := σ) hdisj hcomm hsup f, map_mul,
    conjJ'_sigma_inclusion_T  h hT hcomm hsup
      (tMap σ hdisj hcomm hsup f),
    conjJ'_sigma_inclusion_F (σ := σ) hdisj hcomm hsup
      (phi σ hdisj hcomm hsup f)]

theorem conjJ'_sigma_cube_inclusion_F (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    conjJ' z (σ)
        (conjJ' z (σ)
          (conjJ' z (σ) (Subgroup.inclusion (F_le_J_of_sup hsup) f))) =
      Subgroup.inclusion (T_le_J_of_sup hsup) (tMap σ hdisj hcomm hsup f) *
        (Subgroup.inclusion (T_le_J_of_sup hsup)
            (tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) *
          (Subgroup.inclusion (T_le_J_of_sup hsup)
              (tMap σ hdisj hcomm hsup
                (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f))) *
            Subgroup.inclusion (F_le_J_of_sup hsup)
              (phi σ hdisj hcomm hsup
                (phi σ hdisj hcomm hsup
                  (phi σ hdisj hcomm hsup f))))) := by
  rw [conjJ'_sigma_sq_inclusion_F  h hT hdisj hcomm hsup f, map_mul, map_mul,
    conjJ'_sigma_inclusion_T  h hT hcomm hsup
      (tMap σ hdisj hcomm hsup f),
    conjJ'_sigma_inclusion_T  h hT hcomm hsup
      (tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)),
    conjJ'_sigma_inclusion_F (σ := σ) hdisj hcomm hsup
      (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f))]

theorem phi_phi_phi (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    phi σ hdisj hcomm hsup
      (phi σ hdisj hcomm hsup
        (phi σ hdisj hcomm hsup f)) = f := by
  have hcube := conjJ'_sigma_cube_inclusion_F (σ := σ) h hT hdisj hcomm hsup f
  have hfix : conjJ' z (σ)
      (conjJ' z (σ)
        (conjJ' z (σ) (Subgroup.inclusion (F_le_J_of_sup hsup) f))) =
      Subgroup.inclusion (F_le_J_of_sup hsup) f := by
    have h := congrArg (fun e : MulAut (J z) =>
      e (Subgroup.inclusion (F_le_J_of_sup hsup) f)) (conjJ'_sigma_pow_three (σ := σ))
    simpa [pow_succ, pow_one, MulAut.mul_apply] using h
  have hEq : Subgroup.inclusion (F_le_J_of_sup hsup) f =
      Subgroup.inclusion (T_le_J_of_sup hsup) (tMap σ hdisj hcomm hsup f) *
        (Subgroup.inclusion (T_le_J_of_sup hsup)
            (tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) *
          (Subgroup.inclusion (T_le_J_of_sup hsup)
              (tMap σ hdisj hcomm hsup
                (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f))) *
            Subgroup.inclusion (F_le_J_of_sup hsup)
              (phi σ hdisj hcomm hsup
                (phi σ hdisj hcomm hsup
                  (phi σ hdisj hcomm hsup f))))) := by
    rw [← hfix]
    exact hcube
  have h := congrArg (prF hdisj hcomm hsup) hEq
  simp only [map_mul, prF_inclusion_T, prF_inclusion_F, one_mul, mul_one] at h
  exact h.symm

theorem tMap_cocycle (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    tMap σ hdisj hcomm hsup f *
      tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) *
        tMap σ hdisj hcomm hsup
          (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) = 1 := by
  have hcube := conjJ'_sigma_cube_inclusion_F (σ := σ) h hT hdisj hcomm hsup f
  have hfix : conjJ' z (σ)
      (conjJ' z (σ)
        (conjJ' z (σ) (Subgroup.inclusion (F_le_J_of_sup hsup) f))) =
      Subgroup.inclusion (F_le_J_of_sup hsup) f := by
    have h := congrArg (fun e : MulAut (J z) =>
      e (Subgroup.inclusion (F_le_J_of_sup hsup) f)) (conjJ'_sigma_pow_three (σ := σ))
    simpa [pow_succ, pow_one, MulAut.mul_apply] using h
  have hEq : Subgroup.inclusion (F_le_J_of_sup hsup) f =
      Subgroup.inclusion (T_le_J_of_sup hsup) (tMap σ hdisj hcomm hsup f) *
        (Subgroup.inclusion (T_le_J_of_sup hsup)
            (tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) *
          (Subgroup.inclusion (T_le_J_of_sup hsup)
              (tMap σ hdisj hcomm hsup
                (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f))) *
            Subgroup.inclusion (F_le_J_of_sup hsup)
              (phi σ hdisj hcomm hsup
                (phi σ hdisj hcomm hsup
                  (phi σ hdisj hcomm hsup f))))) := by
    rw [← hfix]
    exact hcube
  rw [phi_phi_phi (σ := σ) h hT hdisj hcomm hsup f] at hEq
  have h := congrArg (prT hdisj hcomm hsup) hEq
  simp only [map_mul, prT_inclusion_T, prT_inclusion_F, one_mul, mul_one] at h
  rw [mul_assoc]
  exact h.symm

theorem psi_phi_eq (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    psi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) =
      tMap σ hdisj hcomm hsup f * psi σ hdisj hcomm hsup f := by
  have hc := tMap_cocycle (σ := σ) h hT hdisj hcomm hsup f
  have hcb : tMap σ hdisj hcomm hsup
      (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) =
      tMap σ hdisj hcomm hsup f *
        tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) := by
    have h := congrArg (fun x : T => x * tMap σ hdisj hcomm hsup
      (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f))) hc
    have h' : tMap σ hdisj hcomm hsup f *
        tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) =
        tMap σ hdisj hcomm hsup
          (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) := by
      simpa [mul_assoc,
        mul_self_eq_one_of_card_two (T := T) hT
          (tMap σ hdisj hcomm hsup
            (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)))] using h
    exact h'.symm
  calc
    psi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) =
        tMap σ hdisj hcomm hsup
          (phi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f)) := rfl
    _ = tMap σ hdisj hcomm hsup f *
          tMap σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) := hcb
    _ = tMap σ hdisj hcomm hsup f * psi σ hdisj hcomm hsup f := rfl

theorem psi_phi_eq_comm (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    psi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) =
      psi σ hdisj hcomm hsup f * tMap σ hdisj hcomm hsup f := by
  rw [psi_phi_eq (σ := σ) h hT hdisj hcomm hsup f]
  apply Subtype.ext
  exact (CFSG.commute_of_mem_of_isMulCommutative
    (CFSG.isMulCommutative_of_card_two T hT)
    (tMap σ hdisj hcomm hsup f).2
    (psi σ hdisj hcomm hsup f).2).eq

noncomputable def tau (σ : ↥(H z)) (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) : F →* G where
  toFun f := ((psi σ hdisj hcomm hsup f : T) : G) * (f : G)
  map_one' := by
    simp
  map_mul' f₁ f₂ := by
    have hcomm' : Commute
        (((psi σ hdisj hcomm hsup f₂ : T) : G)) ((f₁ : G)) :=
      hcomm _ (psi σ hdisj hcomm hsup f₂).2 _ f₁.2
    calc
      ((psi σ hdisj hcomm hsup (f₁ * f₂) : T) : G) * ((f₁ * f₂ : F) : G)
          = (((psi σ hdisj hcomm hsup f₁ : T) : G) *
              ((psi σ hdisj hcomm hsup f₂ : T) : G)) *
              ((f₁ : G) * (f₂ : G)) := by
            rw [map_mul]
            rfl
      _ = ((psi σ hdisj hcomm hsup f₁ : T) : G) *
            (((psi σ hdisj hcomm hsup f₂ : T) : G) * (f₁ : G)) * (f₂ : G) := by
            group
      _ = ((psi σ hdisj hcomm hsup f₁ : T) : G) *
            ((f₁ : G) * ((psi σ hdisj hcomm hsup f₂ : T) : G)) * (f₂ : G) := by
            rw [hcomm'.eq]
      _ = (((psi σ hdisj hcomm hsup f₁ : T) : G) * (f₁ : G)) *
            (((psi σ hdisj hcomm hsup f₂ : T) : G) * (f₂ : G)) := by
            group

noncomputable def invariantComplement (σ : ↥(H z)) (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) : Subgroup G :=
  (tau σ hdisj hcomm hsup).range

theorem invariantComplement_le_J (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    invariantComplement σ hdisj hcomm hsup ≤ J z := by
  rintro x ⟨f, rfl⟩
  exact (J z).mul_mem (T_le_J_of_sup hsup (psi σ hdisj hcomm hsup f).2)
    (F_le_J_of_sup hsup f.2)

theorem invariantComplement_inf_T (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    invariantComplement σ hdisj hcomm hsup ⊓ T = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hxK, hxT⟩ := hx
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hxK
  have hfT : (f : G) ∈ T := by
    have hmem : ((psi σ hdisj hcomm hsup f : T) : G)⁻¹ *
        (((psi σ hdisj hcomm hsup f : T) : G) * (f : G)) ∈ T :=
      T.mul_mem (T.inv_mem (psi σ hdisj hcomm hsup f).2) hxT
    simpa using hmem
  have hfbot : (f : G) ∈ (⊥ : Subgroup G) := by
    rw [← hdisj]
    exact ⟨hfT, f.2⟩
  have hf1 : f = 1 := Subtype.ext (Subgroup.mem_bot.mp hfbot)
  rw [hf1]
  simp

theorem invariantComplement_sup_T (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    invariantComplement σ hdisj hcomm hsup ⊔ T = J z := by
  apply le_antisymm
  · exact sup_le (invariantComplement_le_J  hdisj hcomm hsup)
      (T_le_J_of_sup hsup)
  · intro x hxJ
    have hx : x ∈ T ⊔ F := by
      rw [hsup]
      exact hxJ
    obtain ⟨t, ht, f, hf, htf⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
    have hmemT : t * ((psi σ hdisj hcomm hsup ⟨f, hf⟩ : T) : G)⁻¹ ∈ T :=
      T.mul_mem ht (T.inv_mem (psi σ hdisj hcomm hsup ⟨f, hf⟩).2)
    have hmemK : ((psi σ hdisj hcomm hsup ⟨f, hf⟩ : T) : G) * f ∈
        invariantComplement σ hdisj hcomm hsup :=
      MonoidHom.mem_range.mpr ⟨⟨f, hf⟩, rfl⟩
    have hxeq : x = (t * ((psi σ hdisj hcomm hsup ⟨f, hf⟩ : T) : G)⁻¹) *
        (((psi σ hdisj hcomm hsup ⟨f, hf⟩ : T) : G) * f) := by
      rw [← htf]
      group
    rw [hxeq, sup_comm]
    exact Subgroup.mul_mem_sup hmemT hmemK

theorem tau_injective (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    Function.Injective (tau σ hdisj hcomm hsup) := by
  intro f₁ f₂ h
  have hval : ((psi σ hdisj hcomm hsup f₁ : T) : G) * (f₁ : G) =
      ((psi σ hdisj hcomm hsup f₂ : T) : G) * (f₂ : G) := h
  have h' : ((psi σ hdisj hcomm hsup f₁ : T) : G)⁻¹ *
      ((psi σ hdisj hcomm hsup f₂ : T) : G) =
      (f₁ : G) * (f₂ : G)⁻¹ := by
    calc
      ((psi σ hdisj hcomm hsup f₁ : T) : G)⁻¹ *
          ((psi σ hdisj hcomm hsup f₂ : T) : G)
          = ((psi σ hdisj hcomm hsup f₁ : T) : G)⁻¹ *
              (((psi σ hdisj hcomm hsup f₂ : T) : G) * (f₂ : G)) *
                (f₂ : G)⁻¹ := by group
      _ = ((psi σ hdisj hcomm hsup f₁ : T) : G)⁻¹ *
              (((psi σ hdisj hcomm hsup f₁ : T) : G) * (f₁ : G)) *
                (f₂ : G)⁻¹ := by rw [← hval]
      _ = (f₁ : G) * (f₂ : G)⁻¹ := by group
  have hmemT : (f₁ : G) * (f₂ : G)⁻¹ ∈ T :=
    h' ▸ T.mul_mem (T.inv_mem (psi σ hdisj hcomm hsup f₁).2)
      (psi σ hdisj hcomm hsup f₂).2
  have hmemF : (f₁ : G) * (f₂ : G)⁻¹ ∈ F :=
    F.mul_mem f₁.2 (F.inv_mem f₂.2)
  have hbot : (f₁ : G) * (f₂ : G)⁻¹ = 1 := by
    have hmem : (f₁ : G) * (f₂ : G)⁻¹ ∈ T ⊓ F := ⟨hmemT, hmemF⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact Subtype.ext (mul_inv_eq_one.mp hbot)

theorem card_invariantComplement (hFc : Nat.card F = 2 ^ 9)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) :
    Nat.card (invariantComplement σ hdisj hcomm hsup) = 2 ^ 9 := by
  have hinj := tau_injective (σ := σ) hdisj hcomm hsup
  have hker : (tau σ hdisj hcomm hsup).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff (tau σ hdisj hcomm hsup)).mpr hinj
  have hcard := Subgroup.card_ker_mul_card_range (tau σ hdisj hcomm hsup)
  rw [hker, Subgroup.card_bot, one_mul] at hcard
  change Nat.card (tau σ hdisj hcomm hsup).range = 2 ^ 9
  rw [hcard, hFc]

theorem conjJ'_sigma_tau_apply (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (f : F) :
    (σ : G) * (tau σ hdisj hcomm hsup f : G) *
        (σ : G)⁻¹ =
      (tau σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) : G) := by
  change (σ : G) *
      (((psi σ hdisj hcomm hsup f : T) : G) * (f : G)) * (σ : G)⁻¹ =
    ((psi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) : T) : G) *
      (phi σ hdisj hcomm hsup f : F)
  have h1 : (σ : G) * ((psi σ hdisj hcomm hsup f : T) : G) *
      (σ : G)⁻¹ = ((psi σ hdisj hcomm hsup f : T) : G) := by
    have hc : Commute (σ : G) ((psi σ hdisj hcomm hsup f : T) : G) :=
      sigma_commute_of_mem_centerIn
        (T_le_centerIn_of_decomposition hT hcomm hsup
          (psi σ hdisj hcomm hsup f).2)
    rw [hc.eq]
    group
  have h2 : (σ : G) * (f : G) * (σ : G)⁻¹ =
      ((tMap σ hdisj hcomm hsup f : T) : G) *
        ((phi σ hdisj hcomm hsup f : F) : G) := by
    have h := congrArg (fun x : J z => (x : G))
      (conjJ'_sigma_inclusion_F (σ := σ) hdisj hcomm hsup f)
    rwa [conjJ'_apply_coe] at h
  calc
    (σ : G) *
        (((psi σ hdisj hcomm hsup f : T) : G) * (f : G)) * (σ : G)⁻¹
        = ((σ : G) * ((psi σ hdisj hcomm hsup f : T) : G) *
            (σ : G)⁻¹) *
            ((σ : G) * (f : G) * (σ : G)⁻¹) := by group
    _ = ((psi σ hdisj hcomm hsup f : T) : G) *
          (((tMap σ hdisj hcomm hsup f : T) : G) *
            ((phi σ hdisj hcomm hsup f : F) : G)) := by rw [h1, h2]
    _ = (((psi σ hdisj hcomm hsup f : T) : G) *
          ((tMap σ hdisj hcomm hsup f : T) : G)) *
            ((phi σ hdisj hcomm hsup f : F) : G) := by group
    _ = ((psi σ hdisj hcomm hsup (phi σ hdisj hcomm hsup f) : T) : G) *
          ((phi σ hdisj hcomm hsup f : F) : G) := by
        have hcoe : ((psi σ hdisj hcomm hsup f : T) : G) *
            ((tMap σ hdisj hcomm hsup f : T) : G) =
            ((psi σ hdisj hcomm hsup
              (phi σ hdisj hcomm hsup f) : T) : G) := by
          simpa only [Subgroup.coe_mul] using
            congrArg (fun x : T => (x : G))
              (psi_phi_eq_comm  h hT hdisj hcomm hsup f).symm
        rw [hcoe]

theorem invariantComplement_conj (h : Tim79a.ParrottHyp z) (hT : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) :
    ∀ k ∈ invariantComplement σ hdisj hcomm hsup,
      (σ : G) * k * (σ : G)⁻¹ ∈
        invariantComplement σ hdisj hcomm hsup := by
  intro k hk
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hk
  exact MonoidHom.mem_range.mpr
    ⟨phi σ hdisj hcomm hsup f,
      (conjJ'_sigma_tau_apply  h hT hdisj hcomm hsup f).symm⟩

theorem isExtraspecial2_invariantComplement (h : Tim79a.ParrottHyp z)
    (hT : Nat.card T = 2) (hFc : Nat.card F = 2 ^ 9)
    (hdisj : T ⊓ F = ⊥) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) :
    IsExtraspecial2 (invariantComplement σ hdisj hcomm hsup) := by
  refine isExtraspecial2_of_complement h hT ?_ ?_ ?_ ?_
  · rw [sup_comm]
    exact invariantComplement_sup_T  hdisj hcomm hsup
  · rw [inf_comm]
    exact invariantComplement_inf_T  hdisj hcomm hsup
  · exact central_in_J_of_decomposition hT hcomm hsup
  · exact card_invariantComplement hFc hdisj hcomm hsup

theorem exists_invariant_complement_of_decomposition (h : Tim79a.ParrottHyp z)
    {T F : Subgroup G} (hT : Nat.card T = 2) (_hF : IsExtraspecial2 F)
    (hFc : Nat.card F = 2 ^ 9) (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    ∃ K : Subgroup G,
      IsExtraspecial2 K ∧ Nat.card K = 2 ^ 9 ∧ K ⊓ T = ⊥ ∧ K ⊔ T = J z ∧
        (∀ k ∈ K, (σ : G) * k * (σ : G)⁻¹ ∈ K) := by
  refine ⟨invariantComplement σ hdisj hcomm hsup, ?_, ?_, ?_, ?_, ?_⟩
  · exact isExtraspecial2_invariantComplement h hT hFc hdisj hcomm hsup
  · exact card_invariantComplement hFc hdisj hcomm hsup
  · exact invariantComplement_inf_T  hdisj hcomm hsup
  · exact invariantComplement_sup_T  hdisj hcomm hsup
  · exact invariantComplement_conj  h hT hdisj hcomm hsup

theorem exists_invariant_complement (h : Tim79a.ParrottHyp z) :
    ∃ T F K : Subgroup G,
      Nat.card T = 2 ∧ IsExtraspecial2 F ∧ Nat.card F = 2 ^ 9 ∧ T ⊓ F = ⊥ ∧
        (∀ t ∈ T, ∀ f ∈ F, Commute t f) ∧ T ⊔ F = J z ∧
          IsExtraspecial2 K ∧ Nat.card K = 2 ^ 9 ∧ K ⊓ T = ⊥ ∧ K ⊔ T = J z ∧
            (∀ k ∈ K, (σ : G) * k * (σ : G)⁻¹ ∈ K) := by
  obtain ⟨T, F, hT, hF, hFc, hdisj, hcomm, hsup⟩ := exists_decomposition h
  obtain ⟨K, hKext, hKcard, hKinf, hKsup, hKconj⟩ :=
    exists_invariant_complement_of_decomposition (σ := σ) h hT hF hFc hdisj hcomm hsup
  exact ⟨T, F, K, hT, hF, hFc, hdisj, hcomm, hsup, hKext, hKcard, hKinf, hKsup, hKconj⟩

end GenericInvariantComplement

section PartA

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem map_zpowers_sigma_eq {σ : ↥(H z)} :
    (Subgroup.zpowers σ).map (H z).subtype = Subgroup.zpowers (σ : G) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem isPGroup_zpowers_sigma_of {σ : ↥(H z)} (hσ : orderOf σ = 3) :
    IsPGroup 3 (Subgroup.zpowers (σ : G)) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hσ]
  norm_num

theorem zpowers_sigma_le_normalizer_J_of {σ : ↥(H z)} :
    Subgroup.zpowers (σ : G) ≤ Subgroup.normalizer (J z : Set G) := by
  have hH : Subgroup.zpowers (σ : G) ≤ H z := by
    rw [Subgroup.zpowers_le]
    exact σ.2
  exact hH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (J_le_H (z := z))).mp hN)

theorem J_eq_sup_centralizer_commutator_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    J z = (J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G)) ⊔
      ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hle : J z ≤ (J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G)) ⊔
      ⁅J z, Subgroup.zpowers (σ : G)⁆ :=
    le_sup_centralizer_commutator (p := 3) (Y := J z)
      (B := Subgroup.zpowers (σ : G)) (isPGroup_zpowers_sigma_of hσ)
      (zpowers_sigma_le_normalizer_J_of (z := z)) (by rw [card_J h]; norm_num)
  have hsup : J z = (J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G)) ⊔
      ⁅J z, Subgroup.zpowers (σ : G)⁆ := by
    apply le_antisymm
    · exact hle
    · exact sup_le inf_le_left
        (commutator_le_of_normalizer (zpowers_sigma_le_normalizer_J_of (z := z)))
  calc
    J z = (J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G)) ⊔
        ⁅J z, Subgroup.zpowers (σ : G)⁆ := hsup
    _ = (J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G)) ⊔
        ⁅Subgroup.zpowers (σ : G), J z⁆ := by rw [Subgroup.commutator_comm]
    _ = (J z ⊓ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G)) ⊔
        ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by rw [map_zpowers_sigma_eq]

theorem commutator_le_J_of {σ : ↥(H z)} :
    ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ≤ J z := by
  rw [map_zpowers_sigma_eq (z := z), Subgroup.commutator_comm]
  exact commutator_le_of_normalizer (X := G) (Y := J z)
    (B := Subgroup.zpowers (σ : G)) (zpowers_sigma_le_normalizer_J_of (z := z))

section PartA2

variable {σ : ↥(H z)}

theorem sigma_commute_of_mem_centerIn_of (hZ : conjZ z σ = 1)
    {y : G} (hy : y ∈ centerIn (J z)) : Commute (σ : G) y := by
  have hmem := centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZ hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm

theorem centralizerJ_ne_top_of_conjV_ne_one (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hV : conjV h σ ≠ 1) : centralizerJ σ ≠ ⊤ := by
  intro htop
  apply hV
  have hconjJ : conjJ' z σ = 1 := by
    apply MulEquiv.ext
    intro j
    have hj : j ∈ centralizerJ σ := by rw [htop]; trivial
    rw [mem_centralizerJ_iff] at hj
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    calc (σ : G) * (j : G) * (σ : G)⁻¹ = (j : G) * (σ : G) * (σ : G)⁻¹ := by
          rw [← hj]
      _ = (j : G) := by group
  rw [conjV_eq_congr, hconjJ]
  have hq : quotientAut (1 : MulAut (J z)) = 1 := by
    ext x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (J z)) x
    rw [quotientAut_mk]
    simp
  rw [hq, map_one]

private theorem centralizerJ_eq_top_of_commutes_of {T K : Subgroup G}
    (hsup : T ⊔ K = J z)
    (hcent : ∀ t ∈ T, ∀ x ∈ J z, Commute t x)
    (hTσ : ∀ t ∈ T, Commute t (σ : G))
    (hKσ : ∀ k ∈ K, Commute (σ : G) k) :
    centralizerJ σ = ⊤ := by
  have hKJ : K ≤ J z := by
    rw [← hsup]
    exact le_sup_right
  have hcommTK : ∀ t ∈ T, ∀ k ∈ K, Commute t k :=
    fun t ht k hk => hcent t ht k (hKJ hk)
  rw [Subgroup.eq_top_iff']
  intro j
  rw [mem_centralizerJ_iff]
  have hj : (j : G) ∈ T ⊔ K := by
    rw [hsup]
    exact j.2
  obtain ⟨t, ht, k, hk, htk⟩ := (CFSG.mem_sup_of_commute hcommTK).mp hj
  calc
    (j : G) * (σ : G) = (t * k) * (σ : G) := by rw [← htk]
    _ = t * (k * (σ : G)) := by group
    _ = t * ((σ : G) * k) := by rw [(hKσ k hk).eq.symm]
    _ = (t * (σ : G)) * k := by group
    _ = ((σ : G) * t) * k := by rw [(hTσ t ht).eq]
    _ = (σ : G) * (t * k) := by group
    _ = (σ : G) * (j : G) := by rw [← htk]

private lemma mem_normalizer_of_pow_three_eq_one {K : Subgroup G} {g : G}
    (hg : g ^ 3 = 1) (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact h k
  · intro hk
    have h2 : g * (g * k * g⁻¹) * g⁻¹ ∈ K := h _ hk
    have h3 : g * (g * (g * k * g⁻¹) * g⁻¹) * g⁻¹ ∈ K := h _ h2
    have hggg : g * g * g = 1 := by
      rw [← pow_three']
      exact hg
    have h3' : (g * g * g) * k * (g * g * g)⁻¹ ∈ K := by
      convert h3 using 1
      group
    rw [hggg] at h3'
    simpa using h3'

private lemma commute_of_commutator_mem_center {g k c : G}
    (hg : g ^ 3 = 1) (hc : c = ⁅g, k⁆) (hgc : Commute g c) (hc2 : c * c = 1) :
    Commute g k := by
  have hgk : g * k * g⁻¹ = c * k := by
    rw [hc, commutatorElement_def]
    group
  have hgc' : g * c * g⁻¹ = c := by
    rw [hgc.eq]
    group
  have hggg : g * g * g = 1 := by
    rw [← pow_three']
    exact hg
  have h2 : (g * g) * k * (g * g)⁻¹ = k := by
    calc
      (g * g) * k * (g * g)⁻¹ = g * (g * k * g⁻¹) * g⁻¹ := by group
      _ = g * (c * k) * g⁻¹ := by rw [hgk]
      _ = (g * c * g⁻¹) * (g * k * g⁻¹) := by group
      _ = c * (c * k) := by rw [hgc', hgk]
      _ = k := by rw [← mul_assoc, hc2, one_mul]
  have h1 : g * k * g⁻¹ = k := by
    calc
      g * k * g⁻¹ = g * ((g * g) * k * (g * g)⁻¹) * g⁻¹ := by rw [h2]
      _ = (g * g * g) * k * (g * g * g)⁻¹ := by group
      _ = k := by rw [hggg]; group
  calc
    g * k = (g * k * g⁻¹) * g := by group
    _ = k * g := by rw [h1]

private lemma mul_self_eq_one_of_mem_zpowers_of_order_two {c : G}
    (h : c ∈ Subgroup.zpowers z) (hz : orderOf z = 2) : c * c = 1 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz]
  have hdvd : orderOf c ∣ 2 := by
    have h' := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) h
    rwa [hcard] at h'
  have hpow : c ^ 2 = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
      rw [hc1]
      simp
    · rw [← h1]
      exact pow_orderOf_eq_one c
  simpa [pow_two] using hpow

theorem isExtraspecial2_commutator_of_K (h : Tim79a.ParrottHyp z)
    {σ : ↥(H z)} (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) (hV : conjV h σ ≠ 1)
    {T K : Subgroup G} (hT : Nat.card T = 2)
    (hsup : T ⊔ K = J z) (hinf : T ⊓ K = ⊥)
    (hcent : ∀ t ∈ T, ∀ x ∈ J z, Commute t x)
    (hK : IsExtraspecial2 K)
    (hKinv : ∀ k ∈ K, (σ : G) * k * (σ : G)⁻¹ ∈ K) :
    IsExtraspecial2 ⁅(Subgroup.zpowers σ).map (H z).subtype, K⁆ := by
  classical
  set s : G := (σ : G) with hs
  set B : Subgroup G := Subgroup.zpowers s with hB
  have hord : orderOf s = 3 := by
    rw [hs, Subgroup.orderOf_coe, hσ]
  have hs3 : s ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one s
  have hB_eq : (Subgroup.zpowers σ).map (H z).subtype = Subgroup.zpowers s := by
    rw [hs, map_zpowers_sigma_eq]
  have hP : IsPGroup 3 B := by
    rw [hB]
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord]
    norm_num
  have hPne : B ≠ ⊥ := by
    intro hbot
    have hsB : s ∈ B := by
      rw [hB]
      exact Subgroup.mem_zpowers s
    rw [hbot] at hsB
    have hs1 : s = 1 := Subgroup.mem_bot.mp hsB
    have h1 : orderOf s = 1 := orderOf_eq_one_iff.mpr hs1
    omega
  have hNP : B ≤ Subgroup.normalizer (K : Set G) := by
    rw [hB, Subgroup.zpowers_le]
    exact mem_normalizer_of_pow_three_eq_one hs3 hKinv
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hc, -, -⟩ := h
    simpa [J, H] using hc
  have hKJ : K ≤ J z := by
    rw [← hsup]
    exact le_sup_right
  have hKK_le : ⁅K, K⁆ ≤ Subgroup.zpowers z := by
    calc
      ⁅K, K⁆ ≤ ⁅J z, J z⁆ := Subgroup.commutator_mono hKJ hKJ
      _ = Subgroup.zpowers z := hJcomm
  have hcardZ : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, h.1]
  have hKK_eq : ⁅K, K⁆ = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hKK_le (by rw [hcardZ, hK.2.2])
  have hZeq : (Subgroup.center K).map K.subtype = Subgroup.zpowers z := by
    rw [← hK.2.1]
    exact hKK_eq
  have hTσ : ∀ t ∈ T, Commute t s := by
    intro t ht
    have htJ : t ∈ J z := by
      rw [← hsup]
      exact Subgroup.mem_sup_left ht
    have htZ : t ∈ centerIn (J z) := by
      refine ⟨htJ, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      exact (hcent t ht x hx).eq.symm
    have hmem : t ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' : t * (σ : G) = (σ : G) * t :=
        (sigma_commute_of_mem_centerIn_of (z := z) hZ htZ).eq.symm
      simpa only [hs] using h'
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  have hprop := prop5_commutator_corrected (H := G) (p := 3) (by norm_num) (by norm_num)
    (J := K) (P := B) hK hP hPne hNP
  have hcontra : ∀ (_ : ∀ k ∈ K, Commute s k), False := by
    intro hKσ
    exact centralizerJ_ne_top_of_conjV_ne_one (z := z) h hV
      (centralizerJ_eq_top_of_commutes_of (z := z) (σ := σ) hsup hcent hTσ hKσ)
  rcases hprop with hext | hcenter | hbot
  · rw [hB_eq]
    simpa only [hB] using hext
  · exfalso
    have hKσ : ∀ k ∈ K, Commute s k := by
      intro k hk
      have hcommZ : ⁅B, K⁆ = Subgroup.zpowers z := hcenter.trans hZeq
      have hmem : ⁅s, k⁆ ∈ Subgroup.zpowers z := by
        rw [← hcommZ]
        exact Subgroup.commutator_mem_commutator
          (by rw [hB]; exact Subgroup.mem_zpowers s) hk
      have hgc : Commute s ⁅s, k⁆ := by
        have hcenterIn : ⁅s, k⁆ ∈ centerIn (J z) :=
          Subgroup.zpowers_le_of_mem (H := centerIn (J z))
            ⟨z_mem_J h, z_centralizes_J h⟩ hmem
        have h' := sigma_commute_of_mem_centerIn_of (z := z) hZ hcenterIn
        simpa only [hs] using h'
      have hc2 : ⁅s, k⁆ * ⁅s, k⁆ = 1 :=
        mul_self_eq_one_of_mem_zpowers_of_order_two hmem h.1
      exact commute_of_commutator_mem_center hs3 rfl hgc hc2
    exact hcontra hKσ
  · exfalso
    have hKσ : ∀ k ∈ K, Commute s k := by
      intro k hk
      have hle : B ≤ Subgroup.centralizer (K : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hsB : s ∈ B := by
        rw [hB]
        exact Subgroup.mem_zpowers s
      exact (Subgroup.mem_centralizer_iff.mp (hle hsB) k hk).symm
    exact hcontra hKσ

theorem commutator_J_eq_commutator_K_of (h : Tim79a.ParrottHyp z)
    {σ : ↥(H z)} (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1)
    {T K : Subgroup G} (hsup : T ⊔ K = J z)
    (hcent : ∀ t ∈ T, ∀ x ∈ J z, Commute t x)
    (hKinv : ∀ k ∈ K, (σ : G) * k * (σ : G)⁻¹ ∈ K) :
    ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ =
      ⁅(Subgroup.zpowers σ).map (H z).subtype, K⁆ := by
  classical
  set s : G := (σ : G) with hs
  set B : Subgroup G := (Subgroup.zpowers σ).map (H z).subtype with hB
  have hB_eq : B = Subgroup.zpowers s := by
    rw [hB, hs, map_zpowers_sigma_eq]
  have hKJ : K ≤ J z := by rw [← hsup]; exact le_sup_right
  have hTJ : T ≤ J z := by rw [← hsup]; exact le_sup_left
  have hcommTK : ∀ t ∈ T, ∀ k ∈ K, Commute t k :=
    fun t ht k hk => hcent t ht k (hKJ hk)
  have hKinv_s : ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
    intro k hk
    simpa only [hs] using hKinv k hk
  have hTs : ∀ t ∈ T, Commute t s := by
    intro t ht
    have htZ : t ∈ centerIn (J z) := by
      refine ⟨hTJ ht, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      exact (hcent t ht x hx).eq.symm
    have hmem : t ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' : t * (σ : G) = (σ : G) * t :=
        (sigma_commute_of_mem_centerIn_of (z := z) hZ htZ).eq.symm
      simpa only [hs] using h'
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  have hs3 : s ^ 3 = 1 := by
    have hord : orderOf s = 3 := by
      rw [hs, Subgroup.orderOf_coe, hσ]
    rw [← hord]
    exact pow_orderOf_eq_one s
  have hσN : s ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hKinv_s k hk
    · intro hk
      have hs2 : s ^ 2 = s⁻¹ := by
        rw [pow_two]
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_three', hs3]
      have h2 : s ^ 2 * k * (s ^ 2)⁻¹ ∈ K := by
        convert hKinv_s (s * k * s⁻¹) hk using 1
        rw [pow_two]
        group
      rw [hs2] at h2
      have h3 : s⁻¹ * k * s ∈ K := by simpa using h2
      have h4 : s * (s⁻¹ * k * s) * s⁻¹ ∈ K := hKinv_s _ h3
      convert h4 using 1
      group
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    rw [hB_eq, Subgroup.zpowers_le]
    exact hσN
  have hBK : ⁅B, K⁆ ≤ K :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hBN
  have hBT : B ≤ Subgroup.centralizer (T : Set G) := by
    rw [hB_eq, Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun t ht => (hTs t ht).eq
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro b hb x hx
    have hx' : x ∈ T ⊔ K := by rw [hsup]; exact hx
    obtain ⟨t, ht, k, hk, htk⟩ := (CFSG.mem_sup_of_commute hcommTK).mp hx'
    have hbt : Commute b t :=
      (Subgroup.mem_centralizer_iff.mp (hBT hb) t ht).symm
    have hbkK : ⁅b, k⁆ ∈ K := (Subgroup.commutator_le.mp hBK) b hb k hk
    have htbk : Commute t ⁅b, k⁆ := hcent t ht ⁅b, k⁆ (hKJ hbkK)
    rw [← htk]
    have hEq : ⁅b, t * k⁆ = ⁅b, k⁆ := by
      calc
        ⁅b, t * k⁆ = ⁅b, t⁆ * t * ⁅b, k⁆ * t⁻¹ :=
          commutatorElement_mul_right_eq_mul_conj b t k
        _ = 1 * t * ⁅b, k⁆ * t⁻¹ := by rw [hbt.commutator_eq]
        _ = t * ⁅b, k⁆ * t⁻¹ := by rw [one_mul]
        _ = ⁅b, k⁆ * t * t⁻¹ := by rw [htbk.eq]
        _ = ⁅b, k⁆ := by rw [mul_inv_cancel_right]
    rw [hEq]
    exact Subgroup.commutator_mem_commutator hb hk
  · exact Subgroup.commutator_mono_right hKJ

theorem isExtraspecial2_commutator_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) (hV : conjV h σ ≠ 1) :
    IsExtraspecial2 ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by
  haveI : Fact (orderOf σ = 3) := ⟨hσ⟩
  haveI : Fact (conjZ z σ = 1) := ⟨hZ⟩
  obtain ⟨T, F, K, hT, hF, hFc, hdisj, hcomm, hsup, hK, hKcard, hKinf, hKsup, hKconj⟩ :=
    GenericInvariantComplement.exists_invariant_complement (σ := σ) h
  have hcent : ∀ t ∈ T, ∀ x ∈ J z, Commute t x :=
    central_in_J_of_decomposition hT hcomm hsup
  have hsup' : T ⊔ K = J z := by rw [sup_comm]; exact hKsup
  have hKinf' : T ⊓ K = ⊥ := by rw [inf_comm]; exact hKinf
  rw [commutator_J_eq_commutator_K_of (z := z) h hσ hZ hsup' hcent hKconj]
  exact isExtraspecial2_commutator_of_K (z := z) h hσ hZ hV hT hsup' hKinf' hcent hK hKconj

end PartA2

section PartA3

theorem centerIn_commutator_eq_zpowers_z_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) (hV : conjV h σ ≠ 1) :
    centerIn ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ = Subgroup.zpowers z := by
  let P : Subgroup G := ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆
  have hPext : IsExtraspecial2 P := isExtraspecial2_commutator_of h hσ hZ hV
  obtain ⟨hP2, hPcomm, hPcard⟩ := hPext
  have hPJ : P ≤ J z := commutator_le_J_of (z := z)
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    simpa [J, H] using h.2.2.1
  have hder : ⁅P, P⁆ ≤ Subgroup.zpowers z := by
    rw [← hJcomm]
    exact Subgroup.commutator_mono hPJ hPJ
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, h.1]
  have heq : ⁅P, P⁆ = Subgroup.zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge hder
    rw [hPcard, hzcard]
  change centerIn P = Subgroup.zpowers z
  rw [CFSG.centerIn_eq_map_center, ← hPcomm]
  exact heq

theorem z1_not_mem_commutator_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) (hV : conjV h σ ≠ 1)
    {z1 : G} (hz1 : z1 ∈ centerIn (J z)) (hz1ne : z1 ∉ Subgroup.zpowers z) :
    z1 ∉ ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by
  intro hz1P
  let P : Subgroup G := ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆
  have hcenter : centerIn P = Subgroup.zpowers z :=
    centerIn_commutator_eq_zpowers_z_of h hσ hZ hV
  have hPJ : P ≤ J z := commutator_le_J_of (z := z)
  have hz1Z : z1 ∈ centerIn P := by
    refine ⟨hz1P, ?_⟩
    change z1 ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hz1.2) y (hPJ hy)
  rw [hcenter] at hz1Z
  exact hz1ne hz1Z

theorem commutator_inf_centerIn_eq_zpowers_z_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) (hV : conjV h σ ≠ 1) :
    ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ⊓ centerIn (J z) =
      Subgroup.zpowers z := by
  let P : Subgroup G := ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆
  have hcenterP : centerIn P = Subgroup.zpowers z :=
    centerIn_commutator_eq_zpowers_z_of h hσ hZ hV
  obtain ⟨z1, hz1eq, hz1ne, hz1ord⟩ := exists_z1 h
  have hzP : z ∈ P := by
    have hz : z ∈ centerIn P := by rw [hcenterP]; exact Subgroup.mem_zpowers z
    exact hz.1
  have hzZ : z ∈ centerIn (J z) := by
    have hJ'le : ⁅J z, J z⁆ ≤ centerIn (J z) := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact commutator_mem_centerIn_J h hx hy
    have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
      simpa [J, H] using h.2.2.1
    have hzJ' : z ∈ ⁅J z, J z⁆ := by
      rw [hJcomm]
      exact Subgroup.mem_zpowers z
    exact hJ'le hzJ'
  have hle : Subgroup.zpowers z ≤ P ⊓ centerIn (J z) :=
    le_inf ((Subgroup.zpowers_le).mpr hzP) ((Subgroup.zpowers_le).mpr hzZ)
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, h.1]
  have hZcard : Nat.card ↥(centerIn (J z)) = 4 := by
    rw [CFSG.centerIn_eq_map_center]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective (s := J z))]
    exact card_center_subgroupOf_J (z := z) h
  have hdvd : Nat.card ↥(P ⊓ centerIn (J z)) ∣ 4 := by
    rw [← hZcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hge2 : 2 ≤ Nat.card ↥(P ⊓ centerIn (J z)) := by
    rw [← hzcard]
    have hinj : Function.Injective (fun x : ↥(Subgroup.zpowers z) =>
        (⟨x.1, hle x.2⟩ : ↥(P ⊓ centerIn (J z)))) := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun y : ↥(P ⊓ centerIn (J z)) => (y : G)) hab
    exact Nat.card_le_card_of_injective _ hinj
  have hne4 : Nat.card ↥(P ⊓ centerIn (J z)) ≠ 4 := by
    intro h4
    have heq : P ⊓ centerIn (J z) = centerIn (J z) := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_right
      rw [h4, hZcard]
    have hz1Z : z1 ∈ centerIn (J z) := by
      rw [hz1eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z1)
    have hz1P : z1 ∈ P := by
      have := heq ▸ hz1Z
      exact this.1
    exact z1_not_mem_commutator_of h hσ hZ hV hz1Z hz1ne hz1P
  have hcard2 : Nat.card ↥(P ⊓ centerIn (J z)) = 2 := by
    have hle4 : Nat.card ↥(P ⊓ centerIn (J z)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card ↥(P ⊓ centerIn (J z)) <;> omega
  change P ⊓ centerIn (J z) = Subgroup.zpowers z
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hzcard])).symm

end PartA3

section PartA5Split

variable {σ : ↥(H z)}

@[expose] noncomputable def VComplementHom (h : Tim79a.ParrottHyp z) (σ : ↥(H z)) :
    QuotientV.V z →* QuotientV.V z where
  toFun v := v * conjV h σ v
  map_one' := by simp
  map_mul' v w := by
    letI : CommGroup (QuotientV.V z) := commGroupV h
    simp [map_mul, mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem VComplementHom_apply (h : Tim79a.ParrottHyp z) (σ : ↥(H z))
    (v : QuotientV.V z) :
    VComplementHom h σ v = v * conjV h σ v := rfl

theorem conjV_alpha_three_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (v : QuotientV.V z) :
    conjV h σ (conjV h σ (conjV h σ v)) = v := by
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσ, pow_orderOf_eq_one]
  have hσ3' : conjV h σ ^ 3 = 1 := by
    rw [← map_pow, hσ3, map_one]
  have h := congrArg (fun f : MulAut (QuotientV.V z) => f v) hσ3'
  simpa [pow_succ, pow_two] using h

theorem disjoint_ker_range_VComplementHom (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    (VComplementHom h σ).ker ⊓ (VComplementHom h σ).range = ⊥ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  rw [Subgroup.mem_inf] at hv
  obtain ⟨hvker, hvrange⟩ := hv
  rw [MonoidHom.mem_ker] at hvker
  rw [MonoidHom.mem_range] at hvrange
  obtain ⟨w, hw⟩ := hvrange
  have hvv : ∀ x : QuotientV.V z, x * x = 1 := by
    intro x
    simpa [pow_two] using QuotientV.pow_two_eq_one_V h x
  have hvker' : v * conjV h σ v = 1 := by
    simpa only [VComplementHom_apply] using hvker
  have hvfix : conjV h σ v = v := by
    calc conjV h σ v = 1 * conjV h σ v := (one_mul _).symm
      _ = (v * v) * conjV h σ v := by rw [hvv v]
      _ = v * (v * conjV h σ v) := by rw [mul_assoc]
      _ = v * 1 := by rw [hvker']
      _ = v := mul_one v
  have hwT : v = w * conjV h σ w := by
    rw [← hw]
    rfl
  have hvα : conjV h σ v =
      conjV h σ w * conjV h σ (conjV h σ w) := by
    rw [hwT, map_mul]
  have hcancel : w = conjV h σ (conjV h σ w) := by
    have h1 : w * conjV h σ w =
        conjV h σ w * conjV h σ (conjV h σ w) := by
      calc w * conjV h σ w = v := hwT.symm
        _ = conjV h σ v := hvfix.symm
        _ = conjV h σ w * conjV h σ (conjV h σ w) := hvα
    have h1' : w * conjV h σ w =
        conjV h σ (conjV h σ w) * conjV h σ w := by
      rw [h1, mul_comm]
    exact mul_right_cancel h1'
  have hwfix : conjV h σ w = w := by
    have hcongr := congrArg (fun x => conjV h σ x) hcancel
    simpa [conjV_alpha_three_of h hσ] using hcongr
  calc v = w * conjV h σ w := hwT
    _ = w * w := by rw [hwfix]
    _ = 1 := hvv w

theorem fixSubmodule_eq_ker_VComplementHom (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    fixSubmodule h σ =
      ((VComplementHom h σ).ker.toAddSubgroup).toZModSubmodule 2 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  rw [mem_fixSubmodule_iff, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup,
    MonoidHom.mem_ker, VComplementHom_apply]
  constructor
  · intro hfix
    rw [mem_autFixedSubgroup] at hfix
    rw [hfix]
    simpa [pow_two] using QuotientV.pow_two_eq_one_V h (Additive.toMul v)
  · intro hker
    rw [mem_autFixedSubgroup]
    have hv2 : Additive.toMul v * Additive.toMul v = 1 := by
      simpa [pow_two] using QuotientV.pow_two_eq_one_V h (Additive.toMul v)
    calc conjV h σ (Additive.toMul v) = 1 * conjV h σ (Additive.toMul v) :=
          (one_mul _).symm
      _ = (Additive.toMul v * Additive.toMul v) * conjV h σ (Additive.toMul v) := by
          rw [hv2]
      _ = Additive.toMul v * (Additive.toMul v * conjV h σ (Additive.toMul v)) := by
          rw [mul_assoc]
      _ = Additive.toMul v * 1 := by rw [hker]
      _ = Additive.toMul v := mul_one _

@[expose] noncomputable def commutatorV (h : Tim79a.ParrottHyp z) (σ : ↥(H z)) :
    Subgroup (QuotientV.V z) :=
  let P : Subgroup G := ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆
  (P.subgroupOf (J z)).map (QuotientV.pi z)

theorem range_le_commutatorV (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    (VComplementHom h σ).range ≤ commutatorV h σ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  rintro w ⟨v, rfl⟩
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
  let B : Subgroup G := (Subgroup.zpowers σ).map (H z).subtype
  let P : Subgroup G := ⁅B, J z⁆
  have hσB : (σ : G) ∈ B := by
    simp only [B, Subgroup.mem_map]
    exact ⟨σ, Subgroup.mem_zpowers σ, rfl⟩
  let c : J z := conjJ' z σ j * j⁻¹
  have hcP : (c : G) ∈ P := by
    have hc_coe : (c : G) = ⁅(σ : G), (j : G)⁆ := by
      simp [c, conjJ'_apply_coe, commutatorElement_def, mul_assoc]
    rw [hc_coe]
    exact Subgroup.commutator_mem_commutator hσB j.2
  have hmem : QuotientV.pi z c ∈ (P.subgroupOf (J z)).map (QuotientV.pi z) :=
    Subgroup.mem_map.mpr ⟨c, Subgroup.mem_subgroupOf.mpr hcP, rfl⟩
  rw [pi_conjJ'_mul_inv (z := z) h σ j] at hmem
  have hv2 : QuotientV.pi z j * QuotientV.pi z j = 1 := by
    simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z j)
  have hT : conjV h σ (QuotientV.pi z j) * (QuotientV.pi z j)⁻¹ =
      VComplementHom h σ (QuotientV.pi z j) := by
    rw [VComplementHom_apply]
    calc conjV h σ (QuotientV.pi z j) * (QuotientV.pi z j)⁻¹ =
        conjV h σ (QuotientV.pi z j) * QuotientV.pi z j := by
          rw [inv_eq_of_mul_eq_one_right hv2]
      _ = QuotientV.pi z j * conjV h σ (QuotientV.pi z j) := mul_comm _ _
  rwa [hT] at hmem

theorem commutatorV_le_range (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    commutatorV h σ ≤ (VComplementHom h σ).range := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  let B : Subgroup G := (Subgroup.zpowers σ).map (H z).subtype
  let P : Subgroup G := ⁅B, J z⁆
  have hBP : B = Subgroup.zpowers (σ : G) := map_zpowers_sigma_eq (z := z)
  have hBleH : B ≤ H z := by
    rw [hBP]
    exact Subgroup.zpowers_le.mpr σ.2
  have hP : P ≤ ((VComplementHom h σ).range.comap (QuotientV.pi z)).map (J z).subtype := by
    rw [show P = ⁅B, J z⁆ from rfl, Subgroup.commutator_le]
    intro b hb j hj
    have hbH : b ∈ H z := hBleH hb
    let bH : H z := ⟨b, hbH⟩
    let jJ : J z := ⟨j, hj⟩
    have hbzp : b ∈ Subgroup.zpowers (σ : G) := by
      rwa [← hBP]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbzp
    let c : J z := conjJ' z bH jJ * jJ⁻¹
    have hc_coe : (c : G) = ⁅b, (j : G)⁆ := by
      simp [c, jJ, bH, conjJ'_apply_coe, commutatorElement_def, mul_assoc]
    refine Subgroup.mem_map.mpr ⟨c, ?_, hc_coe⟩
    rw [Subgroup.mem_comap]
    rw [pi_conjJ'_mul_inv (z := z) h bH jJ]
    have hord : orderOf (σ : G) = 3 := by
      rw [Subgroup.orderOf_coe, hσ]
    have hkmod : (σ : G) ^ (k % 3) = b := by
      rw [← hk]
      have h := zpow_mod_orderOf (σ : G) k
      rwa [hord] at h
    have hbH_eq : bH = σ ^ (k % 3 : ℤ) := by
      apply Subtype.ext
      simpa using hkmod.symm
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
      have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
      have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
      omega
    rcases hr with h0 | h1 | h2
    · rw [hbH_eq, h0]
      simp
    · rw [hbH_eq, h1, zpow_one]
      refine ⟨QuotientV.pi z jJ, ?_⟩
      rw [VComplementHom_apply]
      have hv2 : QuotientV.pi z jJ * QuotientV.pi z jJ = 1 := by
        simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z jJ)
      rw [inv_eq_of_mul_eq_one_right hv2, mul_comm]
    · rw [hbH_eq, h2]
      refine ⟨QuotientV.pi z jJ * conjV h σ (QuotientV.pi z jJ), ?_⟩
      have hv2 : QuotientV.pi z jJ * QuotientV.pi z jJ = 1 := by
        simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z jJ)
      have hσv2 : conjV h σ (QuotientV.pi z jJ) * conjV h σ (QuotientV.pi z jJ) = 1 := by
        simpa [pow_two] using
          QuotientV.pow_two_eq_one_V h (conjV h σ (QuotientV.pi z jJ))
      have hσ2 : (σ : H z) ^ (2 : ℤ) = σ * σ := by
        simp [zpow_natCast, pow_two]
      rw [hσ2, map_mul]
      simp only [VComplementHom_apply, map_mul]
      rw [inv_eq_of_mul_eq_one_right hv2]
      calc
        (QuotientV.pi z jJ * conjV h σ (QuotientV.pi z jJ)) *
            (conjV h σ (QuotientV.pi z jJ) *
              conjV h σ (conjV h σ (QuotientV.pi z jJ))) =
            QuotientV.pi z jJ * (conjV h σ (QuotientV.pi z jJ) *
              conjV h σ (QuotientV.pi z jJ)) *
              conjV h σ (conjV h σ (QuotientV.pi z jJ)) := by
              group
        _ = QuotientV.pi z jJ * conjV h σ (conjV h σ (QuotientV.pi z jJ)) := by
              rw [hσv2, mul_one]
        _ = conjV h σ (conjV h σ (QuotientV.pi z jJ)) * QuotientV.pi z jJ :=
              mul_comm _ _
  intro x hx
  obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hx
  have hy : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hyP
  have hy' : (y : G) ∈ ((VComplementHom h σ).range.comap
      (QuotientV.pi z)).map (J z).subtype := hP hy
  obtain ⟨w, hwRange, hwy⟩ := Subgroup.mem_map.mp hy'
  rw [Subgroup.mem_comap] at hwRange
  have hwy' : w = y := Subgroup.subtype_injective (J z) hwy
  rw [← hyx, ← hwy']
  exact hwRange

theorem commutatorV_eq_range (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    commutatorV h σ = (VComplementHom h σ).range :=
  le_antisymm (commutatorV_le_range h hσ) (range_le_commutatorV h hσ)

end PartA5Split

theorem ker_VComplementHom_eq_autFixedSubgroup (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    (VComplementHom h σ).ker = autFixedSubgroup (conjV h σ) := by
  ext v
  rw [MonoidHom.mem_ker, VComplementHom_apply, mem_autFixedSubgroup]
  constructor
  · intro hker
    have hv2 : v * v = 1 := by
      simpa [pow_two] using QuotientV.pow_two_eq_one_V h v
    calc conjV h σ v = 1 * conjV h σ v := (one_mul _).symm
      _ = (v * v) * conjV h σ v := by rw [hv2]
      _ = v * (v * conjV h σ v) := by rw [mul_assoc]
      _ = v * 1 := by rw [hker]
      _ = v := mul_one v
  · intro hfix
    rw [hfix]
    simpa [pow_two] using QuotientV.pow_two_eq_one_V h v

theorem centralizer_commutator_le_inf_centerIn_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) :
    Subgroup.centralizer ({(σ : G)} : Set G) ⊓
        ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ≤
      ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ⊓ centerIn (J z) := by
  let B : Subgroup G := (Subgroup.zpowers σ).map (H z).subtype
  let P : Subgroup G := ⁅B, J z⁆
  intro x hx
  obtain ⟨hxC, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxJ : x ∈ J z := commutator_le_J_of (z := z) hxP
  let xJ : J z := ⟨x, hxJ⟩
  have hxcomm : x * (σ : G) = (σ : G) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hfix : conjV h σ (QuotientV.pi z xJ) = QuotientV.pi z xJ := by
    rw [conjV_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    calc (σ : G) * (xJ : G) * (σ : G)⁻¹ =
        (xJ : G) * (σ : G) * (σ : G)⁻¹ := by rw [hxcomm]
      _ = (xJ : G) := by group
  have hmemker : QuotientV.pi z xJ ∈ (VComplementHom h σ).ker := by
    rw [MonoidHom.mem_ker, VComplementHom_apply, hfix]
    simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z xJ)
  have hmemrange : QuotientV.pi z xJ ∈ (VComplementHom h σ).range := by
    rw [← commutatorV_eq_range (z := z) h hσ]
    exact Subgroup.mem_map.mpr
      ⟨xJ, Subgroup.mem_subgroupOf.mpr (show (xJ : G) ∈ P from hxP), rfl⟩
  have hmem : QuotientV.pi z xJ ∈
      (VComplementHom h σ).ker ⊓ (VComplementHom h σ).range :=
    Subgroup.mem_inf.mpr ⟨hmemker, hmemrange⟩
  rw [disjoint_ker_range_VComplementHom (z := z) h hσ] at hmem
  have hpi_one : QuotientV.pi z xJ = 1 := Subgroup.mem_bot.mp hmem
  have hxker : xJ ∈ (QuotientV.pi z).ker := MonoidHom.mem_ker.mpr hpi_one
  rw [QuotientV.pi_ker] at hxker
  exact Subgroup.mem_inf.mpr
    ⟨hxP, Subgroup.mem_subgroupOf.mp hxker⟩

theorem inf_centerIn_le_centralizer_commutator_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hZ : conjZ z σ = 1) :
    ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ⊓ centerIn (J z) ≤
      Subgroup.centralizer ({(σ : G)} : Set G) ⊓
        ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by
  intro x hx
  obtain ⟨hxP, hxZ⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_inf.mpr
    ⟨centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZ hxZ, hxP⟩

theorem centralizer_commutator_eq_inf_centerIn_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) :
    Subgroup.centralizer ({(σ : G)} : Set G) ⊓
        ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ =
      ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ⊓ centerIn (J z) :=
  le_antisymm (centralizer_commutator_le_inf_centerIn_of h hσ)
    (inf_centerIn_le_centralizer_commutator_of h hZ)

theorem centralizer_commutator_eq_zpowers_z_of (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ : orderOf σ = 3) (hZ : conjZ z σ = 1) (hV : conjV h σ ≠ 1) :
    Subgroup.centralizer ({(σ : G)} : Set G) ⊓
        ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ = Subgroup.zpowers z :=
  (centralizer_commutator_eq_inf_centerIn_of h hσ hZ).trans
    (commutator_inf_centerIn_eq_zpowers_z_of h hσ hZ hV)

end PartA

section PartB

theorem centralizer_zpowers_eq_centralizer_singleton (x : G) :
    Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact Subgroup.mem_zpowers x)
  · intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hxy : Commute y x := (Subgroup.mem_centralizer_singleton_iff.mp hy)
    exact (hxy.zpow_right k).eq.symm

theorem J_eq_sup_centralizer_commutator_singleton_of (h : Tim79a.ParrottHyp z)
    {σ : ↥(H z)} (hσ : orderOf σ = 3) :
    J z = (J z ⊓ Subgroup.centralizer ({(σ : G)} : Set G)) ⊔
      ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by
  rw [← centralizer_zpowers_eq_centralizer_singleton (σ : G)]
  exact J_eq_sup_centralizer_commutator_of (z := z) h hσ

theorem J_eq_sup_centralizer_commutator_sigma1Nine (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    J z = (J z ⊓ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G)) ⊔
      ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ := by
  rw [← centralizer_zpowers_eq_centralizer_singleton (sigma1Nine D : G)]
  exact J_eq_sup_centralizer_commutator_of (z := z) h (sigma1Nine_order D)

theorem commutator_sigma1Nine_inf_centerIn_eq_zpowers_z (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ ⊓ centerIn (J z) =
      Subgroup.zpowers z :=
  commutator_inf_centerIn_eq_zpowers_z_of (z := z) h (sigma1Nine_order D)
    (conjZ_sigma1Nine h D)
    (conjV_ne_one_of_order_three h (sigma1Nine_order D) (conjZ_sigma1Nine h D))

theorem commutator_le_J_sigma1Nine (D : QuotientData (z := z) hN) :
    (⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ : Subgroup G) ≤ J z :=
  commutator_le_J_of (z := z)

theorem centralizer_commutator_sigma1Nine_eq_zpowers_z (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    Subgroup.centralizer ({(sigma1Nine D : G)} : Set G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ =
      Subgroup.zpowers z :=
  centralizer_commutator_eq_zpowers_z_of (z := z) h
    (sigma1Nine_order D) (conjZ_sigma1Nine h D)
    (conjV_ne_one_of_order_three h (sigma1Nine_order D) (conjZ_sigma1Nine h D))

end PartB

section PartC

theorem J_eq_centralizer_commutator_sigma1Nine (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    J z = ((J z) ⊓ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G)) ⊔
      ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ :=
  J_eq_sup_centralizer_commutator_sigma1Nine h D

theorem centralizer_inf_commutator_eq_sigma1Nine (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    ((J z) ⊓ Subgroup.centralizer ({(sigma1Nine D : G)} : Set G)) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ = Subgroup.zpowers z := by
  rw [inf_assoc,
    inf_eq_right.mpr (le_trans inf_le_right (commutator_le_J_of (z := z)))]
  exact centralizer_commutator_sigma1Nine_eq_zpowers_z h D

end PartC

end CFSG.RankThree.GF2n.Parrott
