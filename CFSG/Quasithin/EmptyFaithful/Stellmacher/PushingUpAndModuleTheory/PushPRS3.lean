module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRNat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRCore
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreS3

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod
open scoped commutatorElement

theorem perm3_inv_of_involution : ∀ t c : Equiv.Perm (Fin 3), t * t = 1 → t ≠ 1 → c ^ 3 = 1 →
    c ≠ 1 → t * c * t⁻¹ = c⁻¹ := by decide

variable {G : Type} [Group G] [Finite G] {X P Z : Subgroup G}

theorem s3_irr (h : PushHyp X P Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hZ0 : (zZero X Z).relIndex Z = 4) :
    ∀ W : Subgroup G, W ≤ Z → X ≤ Subgroup.normalizer (W : Set G) →
      W ≤ zZero X Z ∨ Z ≤ W ⊔ zZero X Z := by
  intro W hWZ hXW
  by_cases hW : W ≤ zZero X Z
  · exact Or.inl hW
  right
  obtain ⟨w, hwW, hwZ₀⟩ := IsConcreteLE.not_le_iff_exists.mp hW
  have hwZ : w ∈ Z := hWZ hwW
  have hwc : w ∉ Subgroup.centralizer (pResidualOf 2 X : Set G) := fun hc => hwZ₀ ⟨hwZ, hc⟩
  rw [Subgroup.mem_centralizer_iff] at hwc
  push Not at hwc
  obtain ⟨l, hl, hlw⟩ := hwc
  have hlX : l ∈ X := pResidualOf_le_self X hl
  have hl3 : l ^ 3 ∈ pCoreOf 2 X := by
    obtain ⟨hlX', hsgn⟩ := sign_toS3_of_mem_pResidualOf e hl
    have h3 := perm3_pow_three_of_sign _ hsgn
    have hl3X : l ^ 3 ∈ X := X.pow_mem hlX 3
    rw [← toS3_eq_one_iff e hl3X]
    have : (⟨l ^ 3, hl3X⟩ : ↥X) = ⟨l, hlX'⟩ ^ 3 := rfl
    rw [this, map_pow, h3]
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWn : ∀ g ∈ X, ∀ z ∈ W, g * z * g⁻¹ ∈ W := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (hXW hg) z).mp hz
  have hMZ : W ⊔ zZero X Z ≤ Z := sup_le hWZ inf_le_left
  by_contra hZM
  have hmul := Subgroup.relIndex_mul_relIndex (zZero X Z) (W ⊔ zZero X Z) Z le_sup_right hMZ
  rw [hZ0] at hmul
  have hM1 : (W ⊔ zZero X Z).relIndex Z ≠ 1 := fun h1 => hZM (Subgroup.relIndex_eq_one.mp h1)
  have hZ01 : (zZero X Z).relIndex (W ⊔ zZero X Z) ≠ 1 := fun h1 =>
    hwZ₀ (Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_left hwW))
  have hp1 := relIndex_pos (zZero X Z) (W ⊔ zZero X Z)
  have hp2 := relIndex_pos (W ⊔ zZero X Z) Z
  have h2 : (zZero X Z).relIndex (W ⊔ zZero X Z) = 2 := by
    have hle : (zZero X Z).relIndex (W ⊔ zZero X Z) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmul)
    interval_cases hh : (zZero X Z).relIndex (W ⊔ zZero X Z) <;> omega
  have hidx : (((zZero X Z).subgroupOf (W ⊔ zZero X Z))).index = 2 := h2
  set a' : G := l * w * l⁻¹ with ha'
  have ha'W : a' ∈ W := hWn l hlX w hwW
  have ha'Z : a' ∈ Z := hWZ ha'W
  have hZ₀c : ∀ k ∈ zZero X Z, l * k = k * l := fun k hk =>
    Subgroup.mem_centralizer_iff.mp hk.2 l hl
  have ha'Z₀ : a' ∉ zZero X Z := by
    intro hk
    apply hwZ₀
    have h1 := hZ₀c a' hk
    have : w = a' := by
      calc w = l⁻¹ * a' * l := by rw [ha']; group
        _ = l⁻¹ * (a' * l) := by group
        _ = l⁻¹ * (l * a') := by rw [h1]
        _ = a' := by group
    rw [this]; exact hk
  have hprod := (Subgroup.mul_mem_iff_of_index_two hidx
    (a := (⟨w, Subgroup.mem_sup_left hwW⟩ : ↥(W ⊔ zZero X Z)))
    (b := (⟨a', Subgroup.mem_sup_left ha'W⟩ : ↥(W ⊔ zZero X Z)))).mpr
    (iff_of_false (fun hh => hwZ₀ (Subgroup.mem_subgroupOf.mp hh))
      (fun hh => ha'Z₀ (Subgroup.mem_subgroupOf.mp hh)))
  have ht : w * a' ∈ zZero X Z := Subgroup.mem_subgroupOf.mp hprod
  have htc := hZ₀c _ ht
  have hb : l * a' * l⁻¹ = w := by
    have e1 : l * (w * a') * l⁻¹ = a' * (l * a' * l⁻¹) := by rw [ha']; group
    have e2 : l * (w * a') * l⁻¹ = w * a' := by rw [htc]; group
    have e3 : a' * (l * a' * l⁻¹) = a' * w := by rw [← e1, e2, hZc w hwZ a' ha'Z]
    exact mul_left_cancel e3
  have hl3c : l ^ 3 * w = w * l ^ 3 := (h.commute_Z_core hwZ hl3).symm
  have e4 : l * l * a' * l⁻¹ * l⁻¹ = l * (l * a' * l⁻¹) * l⁻¹ := by group
  have e5 : l * l * a' * l⁻¹ * l⁻¹ = w := by
    have : l * l * a' * l⁻¹ * l⁻¹ = l ^ 3 * w * (l ^ 3)⁻¹ := by
      rw [ha', show l ^ 3 = l * l * l by rw [pow_succ, pow_two]]; group
    rw [this, hl3c]; group
  rw [e4, hb] at e5
  exact hlw (by
    have : l * w * l⁻¹ = w := e5
    calc l * w = (l * w * l⁻¹) * l := by group
      _ = w * l := by rw [this])

theorem s3_tr (h : PushHyp X P Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    ∀ x ∈ P, x ∉ pCoreOf 2 X →
      (pCoreOf 2 X).relIndex P ≤ (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).relIndex Z := by
  intro x hxP hxQ
  rw [relIndex_core_sylow h e]
  by_contra hlt
  push Not at hlt
  have hpos := relIndex_pos (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z) Z
  have h1 : (fixSecIn (Subgroup.zpowers x) (zZero X Z) Z).relIndex Z = 1 := by omega
  have hZC := Subgroup.relIndex_eq_one.mp h1
  have hxX : x ∈ X := h.le_self hxP
  have hxN : x ∈ Subgroup.normalizer (zZero X Z : Set G) := h.le_normalizer_Z0 hxX
  have hx : ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ ∈ zZero X Z := fun z hz => by
    have := hZC hz
    rw [mem_fixSecIn_zpowers_iff h.Z_le_normalizer_zZero hxN] at this
    exact this.2
  obtain ⟨d, hdL, hdX, hd1, hd3⟩ := exists_three_elt e
  set t := toS3 e ⟨x, hxX⟩ with ht
  have ht1 : t ≠ 1 := fun h' => hxQ ((toS3_eq_one_iff e hxX).mp h')
  obtain ⟨k, hk⟩ := toS3_pow_two_pow_eq_one h e hxP
  have htt : t * t = 1 := (perm3_eq_one_or_involution hk).resolve_left ht1
  set c := toS3 e ⟨d, hdX⟩ with hc
  have hxx : x * x ∈ pCoreOf 2 X := by
    have hxxX : x * x ∈ X := X.mul_mem hxX hxX
    rw [← toS3_eq_one_iff e hxxX]
    have : (⟨x * x, hxxX⟩ : ↥X) = ⟨x, hxX⟩ * ⟨x, hxX⟩ := rfl
    rw [this, map_mul, htt]
  have hd3Q : d ^ 3 ∈ pCoreOf 2 X := by
    have hd3X : d ^ 3 ∈ X := X.pow_mem hdX 3
    rw [← toS3_eq_one_iff e hd3X]
    have : (⟨d ^ 3, hd3X⟩ : ↥X) = ⟨d, hdX⟩ ^ 3 := rfl
    rw [this, map_pow, hd3]
  have hqQ : x * d * x⁻¹ * d ∈ pCoreOf 2 X := by
    have hqX : x * d * x⁻¹ * d ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hxX hdX) (X.inv_mem hxX)) hdX
    rw [← toS3_eq_one_iff e hqX]
    have : (⟨x * d * x⁻¹ * d, hqX⟩ : ↥X) = ⟨x, hxX⟩ * ⟨d, hdX⟩ * ⟨x, hxX⟩⁻¹ * ⟨d, hdX⟩ := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv]
    rw [perm3_inv_of_involution t c htt ht1 hd3 hd1]
    exact inv_mul_cancel c
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hZe : ∀ a ∈ Z, a * a = 1 := fun z hz => by
    have := h.elemAbelian.2 z hz
    simpa [pow_two] using this
  have hcen := s3_alg (Z := Z) (Z₀ := zZero X Z) inf_le_left hZc hZe (h.normal hdX) (h.normal hxX)
    (fun k hk => by
      have : d * k = k * d := Subgroup.mem_centralizer_iff.mp hk.2 d hdL
      rw [this]; group)
    hx (fun z hz => (h.commute_Z_core hz hxx).symm)
    (fun z hz => (h.commute_Z_core hz hd3Q).symm) (fun z hz => (h.commute_Z_core hz hqQ).symm)
  apply hd1
  rw [toS3_eq_one_iff e hdX]
  refine h.mem_core_of_centralizes hdX (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
  exact (hcen z hz).symm

theorem natFacts_of_s3 (h : PushHyp X P Z) (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hnc : NoCharNormal P X) : NatFacts X P Z := by
  have hQP2 : (pCoreOf 2 X).relIndex P = 2 := relIndex_core_sylow h e
  have hP0 : P ≠ ⊥ := by
    intro hP
    have h1 : (pCoreOf 2 X).relIndex P = 1 :=
      Subgroup.relIndex_eq_one.mpr (by rw [hP]; exact bot_le)
    omega
  have hZ0 : (zZero X Z).relIndex Z = 4 := (pu1_s3_of_noCharNormal h ⟨e⟩ hP0 hnc).2.2
  refine ⟨exists_odd_notin_core h (fun n hn => ?_), s3_irr h e hZ0, s3_tr h e⟩
  rw [relIndex_core_eq_six e] at hn
  rcases n with _ | _ | _ | n
  · simp at hn
  · simp at hn
  · simp at hn
  · have : 2 ^ (n + 3) = 8 * 2 ^ n := by ring
    rw [this] at hn
    omega

end CFSG.Quasithin.F53Push
