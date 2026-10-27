module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212

variable {Γ : Type*} [Group Γ] {p : ℕ} {A B G : Subgroup Γ}

structure Hyp (p : ℕ) (A G : Subgroup Γ) : Prop where
  near : NearAsolvAction p A G
  sol_eq : sol G = ⊥
  min : IsChiefFactorOf (G ⊔ A) (layerIn G) ⊥
  prod : (layerIn G : Set Γ) * (cenIn G A : Set Γ) = G

structure GoodB (A B G : Subgroup Γ) : Prop where
  le : B ≤ A
  trans : ∀ J ∈ lcal G, ∀ a ∈ A, ∃ b ∈ B,
    J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom
  free : ∀ J ∈ lcal G, B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)

theorem ne_bot_of_mem_lcal {X J : Subgroup Γ} (hJ : J ∈ lcal X) : J ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  exact hnc inferInstance

theorem perm_lcal {X : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (X : Set Γ))
    {J : Subgroup Γ} (hJ : J ∈ lcal X) : J.map (MulAut.conj g).toMonoidHom ∈ lcal X :=
  map_conj_mem_lcal hJ hg

namespace Hyp

variable [Finite Γ] (H : Hyp p A G)

include H

omit [Finite Γ] in
theorem comm {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have := H.near.elemAbelian.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

omit [Finite Γ] in
theorem isPGroup : IsPGroup p A :=
  CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A H.near.elemAbelian

omit [Finite Γ] in
theorem coprime : Nat.Coprime p (Nat.card G) := H.near.nearPSolvable.1

theorem layerIn_eq : layerIn G = kOf G := (kOf_eq_map_layer H.sol_eq).symm

theorem hK : IsDirectProduct (lcal G) (kOf G) := isDirectProduct_lcal_kOf H.sol_eq

theorem GA_le_normalizer : G ⊔ A ≤ Subgroup.normalizer (kOf G : Set Γ) := by
  have := H.min.2.1.2
  rwa [H.layerIn_eq] at this

theorem A_le_normalizer : A ≤ Subgroup.normalizer (kOf G : Set Γ) :=
  le_sup_right.trans H.GA_le_normalizer

theorem G_le_normalizer : G ≤ Subgroup.normalizer (kOf G : Set Γ) :=
  le_sup_left.trans H.GA_le_normalizer

theorem kOf_ne_bot : kOf G ≠ ⊥ := by
  have := H.min.2.2.1
  rw [H.layerIn_eq] at this
  exact this.ne'

theorem exists_lcal : ∃ J, J ∈ lcal G := by
  by_contra hcon
  push Not at hcon
  have : lcal G = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
  apply H.kOf_ne_bot
  rw [← H.hK.sSup_eq, this, sSup_empty]

omit [Finite Γ] in
theorem A_perm_lcal {a : Γ} (ha : a ∈ A) {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    J.map (MulAut.conj a).toMonoidHom ∈ lcal G :=
  perm_lcal (H.near.admits ha) hJ

theorem kOf_le_normalizer_of_mem_lcal {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    kOf G ≤ Subgroup.normalizer (J : Set Γ) :=
  H.hK.le_normalizer hJ

theorem lcal_kOf : lcal (kOf G) = lcal G := by
  have hss : IsSemisimple (kOf G) := isSemisimple_kOf H.sol_eq
  rw [hss.lcal_eq, simpleComponents_kOf H.sol_eq]

theorem transitive {J₁ J₂ : Subgroup Γ} (h₁ : J₁ ∈ lcal G) (h₂ : J₂ ∈ lcal G) :
    ∃ a ∈ A, ∃ d ∈ cenIn G A,
      J₂ = J₁.map (MulAut.conj (a * d)).toMonoidHom := by
  have hK := H.hK
  have hGA : G ⊔ A ≤ Subgroup.normalizer (G : Set Γ) :=
    sup_le Subgroup.le_normalizer H.near.admits
  have hNK : orbitClosure J₁ (G ⊔ A) ≤ kOf G :=
    orbitClosure_le_of_normalizer (hK.le h₁) H.GA_le_normalizer
  have hNnorm : G ⊔ A ≤ Subgroup.normalizer (orbitClosure J₁ (G ⊔ A) : Set Γ) :=
    le_normalizer_orbitClosure J₁ (G ⊔ A)
  have hNeq : orbitClosure J₁ (G ⊔ A) = kOf G := by
    have hNG : orbitClosure J₁ (G ⊔ A) ≤ G ⊔ A := hNK.trans ((kOf_le G).trans le_sup_left)
    rcases H.min.2.2.2 (orbitClosure J₁ (G ⊔ A)) ⟨hNG, hNnorm⟩ bot_le
      (by rw [H.layerIn_eq]; exact hNK) with h | h
    · exact absurd (eq_bot_iff.mpr ((le_orbitClosure J₁ (G ⊔ A)).trans h.le))
        (ne_bot_of_mem_lcal h₁)
    · rwa [H.layerIn_eq] at h
  have hmem : ∃ g ∈ G ⊔ A, J₂ = J₁.map (MulAut.conj g).toMonoidHom := by
    by_contra hcon
    push Not at hcon
    have hT : orbitClosure J₁ (G ⊔ A) ≤ sSup (lcal G \ {J₂}) := by
      rw [orbitClosure_eq_sSup]
      refine sSup_le ?_
      rintro K ⟨g, hg, rfl⟩
      exact le_sSup ⟨perm_lcal (hGA hg) h₁, fun hK2 =>
        hcon g hg (Set.mem_singleton_iff.mp hK2).symm⟩
    have hle : J₂ ≤ sSup (lcal G \ {J₂}) := ((hK.le h₂).trans hNeq.ge).trans hT
    have := (hK.indep h₂).eq_bot_of_le hle
    exact ne_bot_of_mem_lcal h₂ this
  obtain ⟨g, hg, rfl⟩ := hmem
  have hset : ((G ⊔ A : Subgroup Γ) : Set Γ) = (G : Set Γ) * A :=
    Subgroup.coe_mul_of_right_le_normalizer_left G A H.near.admits
  have hg' : g ∈ ((G ⊔ A : Subgroup Γ) : Set Γ) := hg
  rw [hset] at hg'
  obtain ⟨x, hx, a, ha, rfl⟩ := hg'
  obtain ⟨e, he, d, hd, rfl⟩ : x ∈ (layerIn G : Set Γ) * (cenIn G A : Set Γ) := H.prod ▸ hx
  refine ⟨a, ha, d, hd, ?_⟩
  have hdA : a * d = d * a := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 a ha
  have hda : d * a ∈ Subgroup.normalizer (G : Set Γ) :=
    mul_mem (Subgroup.le_normalizer (Subgroup.mem_inf.mp hd).1) (H.near.admits ha)
  have hJ : J₁.map (MulAut.conj (d * a)).toMonoidHom ∈ lcal G := perm_lcal hda h₁
  have he' : e ∈ Subgroup.normalizer (J₁.map (MulAut.conj (d * a)).toMonoidHom : Set Γ) := by
    rw [H.layerIn_eq] at he
    exact H.kOf_le_normalizer_of_mem_lcal hJ he
  rw [mem_normalizer_iff_map_conj, Thm210.map_conj_map_conj] at he'
  change J₁.map (MulAut.conj (e * d * a)).toMonoidHom = J₁.map (MulAut.conj (a * d)).toMonoidHom
  rw [mul_assoc, he', hdA]

theorem norm_iff {J₁ J₂ : Subgroup Γ} (h₁ : J₁ ∈ lcal G) (h₂ : J₂ ∈ lcal G) {x : Γ} (hx : x ∈ A) :
    x ∈ Subgroup.normalizer (J₂ : Set Γ) ↔ x ∈ Subgroup.normalizer (J₁ : Set Γ) := by
  obtain ⟨a, ha, d, hd, rfl⟩ := H.transitive h₁ h₂
  have hxd : x * d = d * x := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 x hx
  have hcomm : x * (a * d) = (a * d) * x := by
    rw [← mul_assoc, H.comm hx ha, mul_assoc, hxd, ← mul_assoc]
  exact mem_normalizer_map_conj_iff_of_commute hcomm

theorem cent_iff {J₁ J₂ : Subgroup Γ} (h₁ : J₁ ∈ lcal G) (h₂ : J₂ ∈ lcal G) {x : Γ} (hx : x ∈ A) :
    x ∈ Subgroup.centralizer (J₂ : Set Γ) ↔ x ∈ Subgroup.centralizer (J₁ : Set Γ) := by
  obtain ⟨a, ha, d, hd, rfl⟩ := H.transitive h₁ h₂
  have hxd : x * d = d * x := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 x hx
  have hcomm : x * (a * d) = (a * d) * x := by
    rw [← mul_assoc, H.comm hx ha, mul_assoc, hxd, ← mul_assoc]
  exact mem_centralizer_map_conj_iff_of_commute hcomm

theorem semisimpleAction : SemisimpleAction p A (kOf G) where
  prime := H.near.prime
  odd := H.near.odd
  elemAbelian := H.near.elemAbelian
  admits := H.A_le_normalizer
  nearPSolvable := signalizerNearPSolvable_of_le (kOf_le G) H.near.nearPSolvable
  solvable_cen := by
    have : Group.IsSolvable ↥(G ⊓ Subgroup.centralizer (A : Set Γ)) := H.near.solvable_cen
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_inf_right _ (kOf_le G) :
        kOf G ⊓ Subgroup.centralizer (A : Set Γ) ≤ G ⊓ Subgroup.centralizer (A : Set Γ)))
  semisimple := isSemisimple_kOf H.sol_eq
  ne_bot := H.kOf_ne_bot

theorem exists_generator {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    ∃ a ∈ A ⊓ Subgroup.normalizer (J : Set Γ), a ∉ Subgroup.centralizer (J : Set Γ) ∧
      ∀ b ∈ A ⊓ Subgroup.normalizer (J : Set Γ),
        b ∈ (A ⊓ Subgroup.centralizer (J : Set Γ)) ⊔ Subgroup.zpowers a := by
  have hJ' : J ∈ lcal (kOf G) := H.lcal_kOf ▸ hJ
  obtain ⟨a, f, ha, hf, hord, hpow, -⟩ := H.semisimpleAction.exists_frame hJ'
  have hp := H.near.prime
  have hfk : ∀ k : ℕ, ∀ x : ↥J, (((f ^ k) x : ↥J) : Γ) = a ^ k * x * (a ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (f x), hf x]
      group
  refine ⟨a, ha, fun hac => ?_, fun b hb => ?_⟩
  · have hf1 : f = 1 := by
      ext x
      rw [hf x, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.mp hac x x.2
      rw [← this]
      group
    rw [hf1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  · obtain ⟨k, hk⟩ := hpow b hb
    have hbA : b ∈ A := (Subgroup.mem_inf.mp hb).1
    have haA : a ∈ A := (Subgroup.mem_inf.mp ha).1
    have hc : (a ^ k)⁻¹ * b ∈ Subgroup.centralizer (J : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hk ⟨x, hx⟩
      rw [hfk k ⟨x, hx⟩] at h1
      have h2 : b * x * b⁻¹ = a ^ k * x * (a ^ k)⁻¹ := h1
      calc x * ((a ^ k)⁻¹ * b) = (a ^ k)⁻¹ * (a ^ k * x * (a ^ k)⁻¹) * b := by group
        _ = (a ^ k)⁻¹ * (b * x * b⁻¹) * b := by rw [h2]
        _ = (a ^ k)⁻¹ * b * x := by group
    have hcA : (a ^ k)⁻¹ * b ∈ A := mul_mem (inv_mem (pow_mem haA k)) hbA
    have : b = a ^ k * ((a ^ k)⁻¹ * b) := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k)
      (Subgroup.mem_inf.mpr ⟨hcA, hc⟩)

theorem exists_B : ∃ B : Subgroup Γ, GoodB A B G ∧ CyclicMod A B := by
  obtain ⟨J₀, hJ₀⟩ := H.exists_lcal
  obtain ⟨a, haF, haC, hgen⟩ := H.exists_generator hJ₀
  have hFA : A ⊓ Subgroup.normalizer (J₀ : Set Γ) ≤ A := inf_le_left
  obtain ⟨C, hCA, hFC, hFCA⟩ :=
    exists_complement_of_isElemAbelian H.near.prime H.near.elemAbelian hFA
  have hA₀F : A ⊓ Subgroup.centralizer (J₀ : Set Γ) ≤ A ⊓ Subgroup.normalizer (J₀ : Set Γ) :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer (J₀ : Set Γ))
  have hcomm : ∀ {X Y : Subgroup Γ}, X ≤ A → Y ≤ A → ∀ x ∈ X, ∀ y ∈ Y, Commute x y :=
    fun hX hY x hx y hy => H.comm (hX hx) (hY hy)
  refine ⟨(A ⊓ Subgroup.centralizer (J₀ : Set Γ)) ⊔ C, ⟨sup_le inf_le_left hCA, ?_, ?_⟩, ?_⟩
  · intro J hJ a' ha'
    rw [← hFCA] at ha'
    obtain ⟨f, hf, c, hc, rfl⟩ :=
      (mem_sup_iff_of_commute (hcomm hFA hCA)).mp ha'
    refine ⟨c, Subgroup.mem_sup_right hc, ?_⟩
    have hfJ : f ∈ Subgroup.normalizer (J : Set Γ) :=
      (H.norm_iff hJ₀ hJ (Subgroup.mem_inf.mp hf).1).mpr (Subgroup.mem_inf.mp hf).2
    have hfc : c * f = f * c := (H.comm (hCA hc) (Subgroup.mem_inf.mp hf).1)
    rw [← Thm210.map_conj_map_conj, map_conj_comm_of_commute J hfc,
      (mem_normalizer_iff_map_conj J f).mp hfJ]
  · intro J hJ x hx
    obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxA : x ∈ A := sup_le inf_le_left hCA hxB
    obtain ⟨a₀, ha₀, c, hc, rfl⟩ := (mem_sup_iff_of_commute
      (hcomm inf_le_left hCA)).mp hxB
    have hxF : a₀ * c ∈ A ⊓ Subgroup.normalizer (J₀ : Set Γ) :=
      Subgroup.mem_inf.mpr ⟨hxA, (H.norm_iff hJ₀ hJ hxA).mp hxN⟩
    have hcF : c ∈ A ⊓ Subgroup.normalizer (J₀ : Set Γ) := by
      have : c = a₀⁻¹ * (a₀ * c) := by group
      rw [this]
      exact mul_mem (inv_mem (hA₀F ha₀)) hxF
    have hc1 : c = 1 := by
      have : c ∈ (A ⊓ Subgroup.normalizer (J₀ : Set Γ)) ⊓ C := Subgroup.mem_inf.mpr ⟨hcF, hc⟩
      rw [hFC, Subgroup.mem_bot] at this
      exact this
    rw [hc1, mul_one]
    obtain ⟨ha₀A, ha₀C⟩ := Subgroup.mem_inf.mp ha₀
    exact (H.cent_iff hJ₀ hJ ha₀A).mpr ha₀C
  · refine ⟨a, (Subgroup.mem_inf.mp haF).1, ?_⟩
    calc A = (A ⊓ Subgroup.normalizer (J₀ : Set Γ)) ⊔ C := hFCA.symm
      _ ≤ ((A ⊓ Subgroup.centralizer (J₀ : Set Γ)) ⊔ Subgroup.zpowers a) ⊔ C :=
        sup_le_sup_right (fun b hb => hgen b hb) C
      _ = ((A ⊓ Subgroup.centralizer (J₀ : Set Γ)) ⊔ C) ⊔ Subgroup.zpowers a :=
        sup_right_comm _ _ _

end Hyp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212
