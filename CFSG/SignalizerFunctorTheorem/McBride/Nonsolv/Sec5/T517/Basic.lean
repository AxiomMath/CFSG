module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AutProd
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.PermutationAction
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517

variable {Γ : Type*} [Group Γ]

theorem map_conj_map_conj (J : Subgroup Γ) (a b : Γ) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem mem_centralizer_sSup {T : Set (Subgroup Γ)} {x : Γ}
    (h : ∀ J ∈ T, ∀ j ∈ J, x * j = j * x) :
    x ∈ Subgroup.centralizer ((sSup T : Subgroup Γ) : Set Γ) := by
  have hle : sSup T ≤ Subgroup.centralizer ({x} : Set Γ) := sSup_le fun J hJ j hj =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h J hJ j hj).symm
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hm)

theorem mem_projIn_of_free [Finite Γ] {S : Set (Subgroup Γ)} {L A : Subgroup Γ}
    (hL : IsDirectProduct S L) (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ≠ J) {J : Subgroup Γ}
    (hJ : J ∈ S) {j : Γ} (hj : j ∈ J) :
    j ∈ projIn S J (L ⊓ Subgroup.centralizer (A : Set Γ)) := by
  have hN : A ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
    by_contra h1
    exact hfree a haA (by simpa using h1) J hJ (Subgroup.mem_normalizer_iff_map_conj_eq.mp haN)
  rw [projIn_centralizer_eq hL hA hJ, hN]
  refine Subgroup.mem_inf.mpr ⟨hj, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
  have : h = 1 := by simpa using hh
  simp [this]

theorem centralizes_of_centralizes_inf [Finite Γ] {S : Set (Subgroup Γ)} {L A : Subgroup Γ}
    (hL : IsDirectProduct S L) (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ≠ J) {x : Γ}
    (hx : ∀ J ∈ S, x ∈ Subgroup.normalizer (J : Set Γ))
    (hxc : ∀ m ∈ L ⊓ Subgroup.centralizer (A : Set Γ), x * m = m * x) :
    ∀ J ∈ S, ∀ j ∈ J, x * j = j * x := by
  intro J hJ j hj
  obtain ⟨y, hyX, hyj⟩ := (hL.mem_projIn_iff hJ).mp (mem_projIn_of_free hL hA hfree hJ hj)
  obtain ⟨hy', hcoord⟩ := hL.coord_conj_of_normalizes hx hJ y.2
  have hxy : x * (y : Γ) * x⁻¹ = y := by
    rw [hxc y hyX]
    group
  have hyy : (⟨x * (y : Γ) * x⁻¹, hy'⟩ : L) = y := Subtype.ext hxy
  rw [hyy, hyj] at hcoord
  calc x * j = (x * j * x⁻¹) * x := by group
    _ = j * x := by rw [← hcoord]

theorem mem_normalizer_sSup_of_normalizes {T : Set (Subgroup Γ)} {v : Γ}
    (hv : ∀ K ∈ T, v ∈ Subgroup.normalizer (K : Set Γ)) :
    v ∈ Subgroup.normalizer ((sSup T : Subgroup Γ) : Set Γ) := by
  have key : ∀ w : Γ, (∀ K ∈ T, w ∈ Subgroup.normalizer (K : Set Γ)) →
      ∀ y ∈ sSup T, w * y * w⁻¹ ∈ sSup T := by
    intro w hw
    have : sSup T ≤ (sSup T).comap (MulAut.conj w).toMonoidHom :=
      sSup_le fun K hK z hz => le_sSup hK ((Subgroup.mem_normalizer_iff.mp (hw K hK) z).mp hz)
    exact fun y hy => this hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key v hv y, fun hy => ?_⟩
  have := key v⁻¹ (fun K hK => inv_mem (hv K hK)) _ hy
  rwa [show v⁻¹ * (v * y * v⁻¹) * v⁻¹⁻¹ = y by group] at this

theorem mem_normalizer_inf {X Y : Subgroup Γ} {g : Γ}
    (hX : g ∈ Subgroup.normalizer (X : Set Γ)) (hY : g ∈ Subgroup.normalizer (Y : Set Γ)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX x, hY x]

theorem mem_normalizer_centralizer_of_commute {E : Subgroup Γ} {v : Γ}
    (hv : ∀ a ∈ E, v * a = a * v) :
    v ∈ Subgroup.normalizer ((Subgroup.centralizer (E : Set Γ) : Subgroup Γ) : Set Γ) := by
  have key : ∀ w : Γ, (∀ a ∈ E, w * a = a * w) →
      ∀ c ∈ Subgroup.centralizer (E : Set Γ), w * c * w⁻¹ ∈ Subgroup.centralizer (E : Set Γ) := by
    intro w hw c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have hwa : Commute a w := (hw a ha).symm
    have hca : Commute a c := hc a ha
    exact ((hwa.mul_right hca).mul_right hwa.inv_right).eq
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key v hv c, fun hc => ?_⟩
  have hv' : ∀ a ∈ E, v⁻¹ * a = a * v⁻¹ := fun a ha => by
    have := hv a ha
    calc v⁻¹ * a = v⁻¹ * (a * v) * v⁻¹ := by group
      _ = v⁻¹ * (v * a) * v⁻¹ := by rw [this]
      _ = a * v⁻¹ := by group
  have := key v⁻¹ hv' _ hc
  rwa [show v⁻¹ * (v * c * v⁻¹) * v⁻¹⁻¹ = c by group] at this

variable [Finite Γ] {p : ℕ} {H B : Subgroup Γ} {θ : Γ → Subgroup Γ}

theorem mem_normalizer_kOf {H : Subgroup Γ} {x : Γ} (hx : x ∈ H) :
    x ∈ Subgroup.normalizer ((kOf H : Subgroup Γ) : Set Γ) := by
  have hN := normal_kOf_subgroupOf H
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact hN.conj_mem ⟨k, kOf_le H hk⟩ hk ⟨x, hx⟩
  · intro hk
    have h : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ ∈ kOf H :=
      hN.conj_mem ⟨x * k * x⁻¹, kOf_le H hk⟩ hk ⟨x⁻¹, inv_mem hx⟩
    have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
    rwa [e] at h

structure Setting (p : ℕ) (H B : Subgroup Γ) (θ : Γ → Subgroup Γ) : Prop where
  prime : p.Prime
  elemAbelian : IsElemAbelian p B
  card : Nat.card B = p ^ 2
  le : B ≤ H
  sol_eq_bot : sol H = ⊥
  trans : ∀ J ∈ lcal H, ∀ J' ∈ lcal H, ∃ b ∈ B, J' = J.map (MulAut.conj b).toMonoidHom
  free : ∀ J ∈ lcal H, ∀ b ∈ B, b ≠ 1 → J.map (MulAut.conj b).toMonoidHom ≠ J
  functor : IsFunctor p B θ
  le_H : ∀ b ∈ B, b ≠ 1 → θ b ≤ H
  hypB : ∀ b ∈ B, b ≠ 1 → signalizerMcBrideHypothesisB p (θ b)
  kOf_inf_le : ∀ b ∈ B, b ≠ 1 → kOf H ⊓ Subgroup.centralizer {b} ≤ θ b
  iso : ∀ b ∈ B, b ≠ 1 → Nonempty ((Fin p → ↥(thetaOf θ B)) ≃* ↥(θ b))

namespace Setting

variable (S : Setting p H B θ)

include S

theorem exists_ne_one : ∃ b ∈ B, b ≠ 1 := by
  by_contra h
  push Not at h
  have hB : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr h
  have h1 := S.card
  rw [hB, Subgroup.card_bot] at h1
  have := Nat.one_lt_pow (two_ne_zero) S.prime.one_lt
  omega

theorem ne_bot : B ≠ ⊥ := by
  obtain ⟨b, hb, hb1⟩ := S.exists_ne_one
  intro h
  rw [h] at hb
  exact hb1 (Subgroup.mem_bot.mp hb)

theorem isPGroup : IsPGroup p B := IsPGroup.of_card S.card

theorem hK : IsDirectProduct (lcal H) (kOf H) := isDirectProduct_lcal_kOf S.sol_eq_bot

theorem nonempty : (lcal H).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hK : kOf H = ⊥ := by rw [← S.hK.sSup_eq, h, sSup_empty]
  have h1 := centralizer_kOf_eq_bot S.sol_eq_bot
  rw [hK] at h1
  obtain ⟨b, hb, hb1⟩ := S.exists_ne_one
  have : b ∈ H ⊓ Subgroup.centralizer (((⊥ : Subgroup Γ) : Subgroup Γ) : Set Γ) :=
    ⟨S.le hb, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      have : h = 1 := by simpa using hh
      simp [this]⟩
  rw [h1] at this
  exact hb1 (Subgroup.mem_bot.mp this)

theorem map_conj_mem {b : Γ} (hb : b ∈ B) {J : Subgroup Γ} (hJ : J ∈ lcal H) :
    J.map (MulAut.conj b).toMonoidHom ∈ lcal H :=
  map_conj_mem_lcal hJ (Subgroup.le_normalizer (S.le hb))

theorem normalizes_of_coprime {X : Subgroup Γ} (hXH : X ≤ H)
    (hBX : B ≤ Subgroup.normalizer (X : Set Γ)) (hX : Nat.Coprime p (Nat.card X)) :
    ∀ x ∈ X, ∀ J ∈ lcal H, x ∈ Subgroup.normalizer (J : Set Γ) :=
  normalizes_of_isPGroup_transitive_conj S.prime S.isPGroup hX hBX
    (fun _ hg _ hJ => map_conj_mem_lcal hJ (Subgroup.le_normalizer ((sup_le hXH S.le) hg)))
    S.trans

theorem thetaOf_le_H : thetaOf θ B ≤ H := by
  obtain ⟨b, hb, hb1⟩ := S.exists_ne_one
  exact (thetaOf_le_apply hb hb1).trans (S.le_H b hb hb1)

theorem thetaOf_le_centralizer : thetaOf θ B ≤ Subgroup.centralizer (B : Set Γ) :=
  S.functor.thetaOf_le_centralizer le_rfl

theorem coprime_thetaOf : Nat.Coprime p (Nat.card (thetaOf θ B)) :=
  S.functor.coprime_thetaOf le_rfl S.ne_bot

theorem normalizes_thetaOf : B ≤ Subgroup.normalizer (thetaOf θ B : Set Γ) :=
  S.functor.normalizes_thetaOf le_rfl

theorem thetaOf_normalizes : ∀ x ∈ thetaOf θ B, ∀ J ∈ lcal H, x ∈ Subgroup.normalizer (J : Set Γ) :=
  S.normalizes_of_coprime S.thetaOf_le_H S.normalizes_thetaOf S.coprime_thetaOf

theorem apply_normalizes {b : Γ} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ∀ x ∈ θ b, ∀ J ∈ lcal H, x ∈ Subgroup.normalizer (J : Set Γ) :=
  S.normalizes_of_coprime (S.le_H b hb hb1) (S.functor.normalized b hb hb1)
    (S.functor.coprime b hb hb1)

theorem eq_one_of_centralizes {x : Γ} (hxH : x ∈ H)
    (hx : ∀ J ∈ lcal H, ∀ j ∈ J, x * j = j * x) : x = 1 := by
  have h1 : x ∈ Subgroup.centralizer ((kOf H : Subgroup Γ) : Set Γ) := by
    rw [← S.hK.sSup_eq]
    exact mem_centralizer_sSup hx
  have h2 : x ∈ H ⊓ Subgroup.centralizer ((kOf H : Subgroup Γ) : Set Γ) := ⟨hxH, h1⟩
  rw [centralizer_kOf_eq_bot S.sol_eq_bot] at h2
  exact Subgroup.mem_bot.mp h2

theorem eq_one_of_centralizes_one {x : Γ} (hxH : x ∈ H)
    (hxB : x ∈ Subgroup.centralizer (B : Set Γ)) {J : Subgroup Γ} (hJ : J ∈ lcal H)
    (hx : ∀ j ∈ J, x * j = j * x) : x = 1 := by
  refine S.eq_one_of_centralizes hxH fun J' hJ' j' hj' => ?_
  obtain ⟨b, hb, rfl⟩ := S.trans J hJ J' hJ'
  obtain ⟨j, hj, rfl⟩ := hj'
  have hxb : Commute x b := (Subgroup.mem_centralizer_iff.mp hxB b hb).symm
  have hxj : Commute x j := hx j hj
  exact ((hxb.mul_right hxj).mul_right hxb.inv_right).eq

theorem kOf_inf_centralizer_le_thetaOf :
    kOf H ⊓ Subgroup.centralizer (B : Set Γ) ≤ thetaOf θ B := by
  rw [le_thetaOf_iff]
  intro b hb hb1
  exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))).trans
    (S.kOf_inf_le b hb hb1)

theorem center_thetaOf : Subgroup.center ↥(thetaOf θ B) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : ∀ w ∈ thetaOf θ B, (z : Γ) * w = w * z := fun w hw =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨w, hw⟩)).symm
  have hz1 : (z : Γ) = 1 := S.eq_one_of_centralizes (S.thetaOf_le_H z.2)
    (centralizes_of_centralizes_inf S.hK (fun a ha J hJ => S.map_conj_mem ha hJ)
      (fun a ha ha1 J hJ => S.free J hJ a ha ha1) (S.thetaOf_normalizes z z.2)
      fun m hm => hzc m (S.kOf_inf_centralizer_le_thetaOf hm))
  exact Subtype.ext hz1

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T517
