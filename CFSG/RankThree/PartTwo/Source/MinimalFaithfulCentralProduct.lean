module

public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
import CFSG.GroupTheory.ThompsonAxB

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Source

variable {G : Type*} [Group G]

theorem exists_minimal_subgroup [Finite G] (P : Subgroup G → Prop) {H : Subgroup G} (hH : P H) :
    ∃ S, P S ∧ ∀ S' ≤ S, P S' → S' = S := by
  classical
  have hex : ∃ m, ∃ S : Subgroup G, P S ∧ Nat.card S = m := ⟨_, H, hH, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hS, fun S' hle hS' => Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [hcard]
  exact Nat.find_min' hex ⟨S', hS', rfl⟩

theorem not_two_dvd_card_of_isPGroup_three [Finite G] {R : Subgroup G} (hR : IsPGroup 3 R) :
    ¬ 2 ∣ Nat.card R := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  rw [hk]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  omega

theorem mem_normalizer_centralizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G), ∀ c ∈ Subgroup.centralizer (H : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    have hh' : g⁻¹ * h * g⁻¹⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    have := hc _ hh'
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * h := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

theorem mem_normalizer_commutator {g : G} {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G), g ∈ Subgroup.normalizer (K : Set G) →
      ∀ c ∈ ⁅H, K⁆, g * c * g⁻¹ ∈ ⁅H, K⁆ := by
    intro g hgH hgK c hc
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp hgH a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hgK b).mp hb)
    exact hle hc
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hH hK c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hH) (inv_mem hK) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

theorem le_normalizer_iSup {ι : Sort*} {X : Subgroup G} {S : ι → Subgroup G}
    (h : ∀ i, X ≤ Subgroup.normalizer (S i : Set G)) :
    X ≤ Subgroup.normalizer ((⨆ i, S i : Subgroup G) : Set G) := by
  have key : ∀ g ∈ X, ∀ c ∈ ⨆ i, S i, g * c * g⁻¹ ∈ ⨆ i, S i := by
    intro g hg c hc
    have hle : (⨆ i, S i) ≤ (⨆ i, S i).comap (MulAut.conj g).toMonoidHom := by
      refine iSup_le fun i => ?_
      intro d hd
      rw [Subgroup.mem_comap]
      exact le_iSup S i ((Subgroup.mem_normalizer_iff.mp (h i hg) d).mp hd)
    exact hle hc
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

theorem inf_centralizer_eq_of_eq_bot {X H : Subgroup G} (hH : H = ⊥) :
    X ⊓ Subgroup.centralizer (H : Set G) = X := by
  subst hH
  refine inf_of_le_left fun x _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
  rw [hh, one_mul, mul_one]

theorem centralizer_sup_eq (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
  · intro g hg
    have h1 : Subgroup.zpowers g ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.zpowers_le.mpr hg.1
    have h2 : Subgroup.zpowers g ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hg.2
    have h3 : H ⊔ K ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) :=
      sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
    exact Subgroup.zpowers_le.mp (Subgroup.le_centralizer_iff.mp h3)

theorem eq_of_le_of_le_of_card_mul_three [Finite G] {Y Y' X : Subgroup G} (h1 : Y ≤ Y')
    (h2 : Y' ≤ X) (hne : Y' ≠ X) (hY : Nat.card Y * 3 = Nat.card X) : Y = Y' := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le h1
  have hdvd : Nat.card Y * m ∣ Nat.card Y * 3 := by
    rw [← hm, hY]
    exact Subgroup.card_dvd_of_le h2
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h | h
  · exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hm, h, mul_one])
  · exact absurd (Subgroup.eq_of_le_of_card_ge h2 (by rw [hm, h, hY])) hne

theorem card_le_card_inf_mul_three [Finite G] {A Y X : Subgroup G} (hAX : A ≤ X) (hYX : Y ≤ X)
    (hY : Nat.card Y * 3 = Nat.card X) : Nat.card A ≤ Nat.card (A ⊓ Y : Subgroup G) * 3 := by
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have hrel : Y.relIndex X = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Y) (K := X)
    rw [inf_of_le_left hYX] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (by rw [← hY, mul_comm]))
  have hle : Y.relIndex A ≤ 3 :=
    hrel ▸ Subgroup.relIndex_le_of_le_right hAX (by rw [hrel]; norm_num)
  have h := Subgroup.relIndex_mul_card (H := Y) (K := A)
  rw [inf_comm] at h
  calc Nat.card A = Y.relIndex A * Nat.card (A ⊓ Y : Subgroup G) := h.symm
    _ ≤ 3 * Nat.card (A ⊓ Y : Subgroup G) := Nat.mul_le_mul_right _ hle
    _ = Nat.card (A ⊓ Y : Subgroup G) * 3 := mul_comm _ _

theorem card_inf_mul_three_eq [Finite G] {A Y X : Subgroup G} {n : ℕ}
    (hXn : Nat.card X = 3 ^ n) (hAX : A ≤ X) (hYX : Y ≤ X) (hY : Nat.card Y * 3 = Nat.card X)
    (hAY : ¬ A ≤ Y) : Nat.card (A ⊓ Y : Subgroup G) * 3 = Nat.card A := by
  have hle := card_le_card_inf_mul_three hAX hYX hY
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ Y ≤ A)
  have hpos : 0 < Nat.card (A ⊓ Y : Subgroup G) := Nat.card_pos
  have hm3 : m ≤ 3 := by
    rw [hm] at hle
    exact Nat.le_of_mul_le_mul_left hle hpos
  have hm1 : m ≠ 1 := by
    intro h
    apply hAY
    have : A ⊓ Y = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm, h, mul_one])
    rw [← this]
    exact inf_le_right
  have hmdvd : m ∣ 3 ^ n := by
    rw [← hXn]
    exact (Dvd.intro_left _ hm.symm).trans (Subgroup.card_dvd_of_le hAX)
  have hm2 : m ≠ 2 := by
    rintro rfl
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hmdvd
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (Nat.card_pos (α := A)).ne' hm
  have : m = 3 := by omega
  rw [hm, this]

theorem le_centralizer_of_le_centralizer_inf_centralizer [Finite G] {p : ℕ} [Fact p.Prime]
    {T K B : Subgroup G} (hT : IsPGroup p T) (hK : ¬ p ∣ Nat.card K) (hBT : B ≤ T)
    (hKT : K ≤ Subgroup.normalizer (T : Set G)) (hKB : K ≤ Subgroup.centralizer (B : Set G))
    (hfix : K ≤ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G)) :
    K ≤ Subgroup.centralizer (T : Set G) := by
  have hBN : B ≤ Subgroup.normalizer (T : Set G) := hBT.trans Subgroup.le_normalizer
  let α : K →* MulAut T := T.normalizerMonoidHom.comp (Subgroup.inclusion hKT)
  let β : B →* MulAut T := T.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (a : K) (t : T), ((α a t : T) : G) = a * t * a⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (t : T), ((β b t : T) : G) = b * t * b⁻¹ := fun _ _ => rfl
  have key := CFSG.GroupTheory.thompson_A_times_B (p := p) hT hK (hT.to_le hBT) α β ?_ ?_
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : a * t * a⁻¹ = t :=
      congrArg Subtype.val (DFunLike.congr_fun (key ⟨a, ha⟩) (⟨t, ht⟩ : T))
    calc t * a = a * t * a⁻¹ * a := by rw [h1]
      _ = a * t := by group
  · intro a b
    ext t
    have hab : (a : G) * b = b * a :=
      (Subgroup.mem_centralizer_iff.mp (hKB a.2) b b.2).symm
    change ((a : G) * ((b : G) * t * (b : G)⁻¹) * (a : G)⁻¹) =
      (b : G) * ((a : G) * t * (a : G)⁻¹) * (b : G)⁻¹
    calc (a : G) * ((b : G) * t * (b : G)⁻¹) * (a : G)⁻¹ =
        ((a : G) * b) * t * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * t * ((b : G) * a)⁻¹ := by rw [hab]
      _ = (b : G) * ((a : G) * t * (a : G)⁻¹) * (b : G)⁻¹ := by group
  · intro a t ht
    have htB : (t : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : b * (t : G) * b⁻¹ = t := congrArg Subtype.val (ht ⟨b, hb⟩)
      calc b * (t : G) = b * t * b⁻¹ * b := by group
        _ = t * b := by rw [h1]
    have hta := Subgroup.mem_centralizer_iff.mp (hfix a.2) t ⟨t.2, htB⟩
    apply Subtype.ext
    rw [hα]
    calc (a : G) * t * (a : G)⁻¹ = t * a * (a : G)⁻¹ := by rw [hta]
      _ = t := by group

theorem commutatorElement_mem_of_mem_sup {g : G} {S O : Subgroup G}
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hgO : g ∈ Subgroup.centralizer (O : Set G))
    (hO : O ≤ Subgroup.normalizer (S : Set G)) {t : G} (ht : t ∈ S ⊔ O) : ⁅g, t⁆ ∈ S := by
  let N : Subgroup G :=
    { carrier := {t | t ∈ Subgroup.normalizer (S : Set G) ∧ ⁅g, t⁆ ∈ S}
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact S.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haN, haS⟩ ⟨hbN, hbS⟩
        refine ⟨mul_mem haN hbN, ?_⟩
        have h1 : a * ⁅g, b⁆ * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp haN _).mp hbS
        have h2 : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [h2]
        exact S.mul_mem haS h1
      inv_mem' := by
        rintro a ⟨haN, haS⟩
        refine ⟨inv_mem haN, ?_⟩
        have h1 : a⁻¹ * ⁅g, a⁆⁻¹ * a⁻¹⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (inv_mem haN) _).mp (S.inv_mem haS)
        have h2 : ⁅g, a⁻¹⁆ = a⁻¹ * ⁅g, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h2]
        exact h1 }
  have hSN : S ≤ N := by
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, ?_⟩
    rw [commutatorElement_def]
    exact S.mul_mem ((Subgroup.mem_normalizer_iff.mp hgS s).mp hs) (S.inv_mem hs)
  have hON : O ≤ N := by
    intro o ho
    refine ⟨hO ho, ?_⟩
    have hgo : o * g = g * o := Subgroup.mem_centralizer_iff.mp hgO o ho
    have : ⁅g, o⁆ = 1 := by
      rw [commutatorElement_def]
      calc g * o * g⁻¹ * o⁻¹ = o * g * g⁻¹ * o⁻¹ := by rw [hgo]
        _ = 1 := by group
    rw [this]
    exact S.one_mem
  exact (sup_le hSN hON ht).2

@[expose] def IsCommutatorPiece (X T S : Subgroup G) : Prop :=
  S ≤ T ∧ ⁅S, X⁆ = S ∧ S ≠ ⊥ ∧ (∀ S' ≤ S, ⁅S', X⁆ = S' → S' ≠ ⊥ → S' = S) ∧
    Nat.card (X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) * 3 = Nat.card X

theorem IsCommutatorPiece.kleinFour_or_quaternion [Finite G] {X T S : Subgroup G}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hT : IsPGroup 2 T) (hS : IsCommutatorPiece X T S) :
    IsKleinFour S ∨ Nonempty (S ≃* QuaternionGroup 2) := by
  obtain ⟨hST, hSX, hSbot, hmin, hcard⟩ := hS
  set Y := X ⊓ Subgroup.centralizer (S : Set G) with hY_def
  have hXS : X ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hSX.le
  have hYc : Y ≤ Subgroup.centralizer (S : Set G) := inf_le_right
  obtain ⟨x, hxX, hxY⟩ : ∃ x ∈ X, x ∉ Y := by
    by_contra h
    push Not at h
    have hle : X ≤ Y := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card Y := Nat.card_pos
    omega
  have hx3 : x ^ 3 = 1 := hX.2 x hxX
  have hx1 : x ≠ 1 := fun h => hxY (h ▸ Y.one_mem)
  have hordx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  set Z := Subgroup.zpowers x with hZ_def
  have hZ3 : Nat.card Z = 3 := by rw [Nat.card_zpowers, hordx]
  have hZX : Z ≤ X := Subgroup.zpowers_le.mpr hxX
  have hYZ : X ≤ Y ⊔ Z := by
    have hle : Y ⊔ Z ≤ X := sup_le inf_le_left hZX
    by_contra hnot
    have hne : Y ⊔ Z ≠ X := fun h => hnot h.ge
    have := eq_of_le_of_le_of_card_mul_three le_sup_left hle hne hcard
    exact hxY (this.ge (le_sup_right (a := Y) (Subgroup.mem_zpowers x)))
  have hnorm : ∀ R ≤ S, Z ≤ Subgroup.normalizer (R : Set G) →
      X ≤ Subgroup.normalizer (R : Set G) := by
    intro R hRS hZR
    refine hYZ.trans (sup_le ?_ hZR)
    intro y hy
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRS) (hYc hy))
  have hZmin : ∀ S' ≤ S, ⁅S', Z⁆ = S' → S' ≠ ⊥ → S' = S := by
    intro S' hS'S hS'Z hS'bot
    have hZS' : Z ≤ Subgroup.normalizer (S' : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr hS'Z.le
    have hXS' := hnorm S' hS'S hZS'
    refine hmin S' hS'S (le_antisymm
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hXS') ?_) hS'bot
    calc S' = ⁅S', Z⁆ := hS'Z.symm
      _ ≤ ⁅S', X⁆ := Subgroup.commutator_mono le_rfl hZX
  have hZ3' : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hSZ : ⁅S, Z⁆ = S := by
    have hZS : Z ≤ Subgroup.normalizer (S : Set G) := hZX.trans hXS
    have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
      Nat.prime_three Z S hZ3' (not_three_dvd_card_of_isPGroup_two (hT.to_le hST)) hZS
    refine hZmin _ (Subgroup.le_normalizer_iff_commutator_le_left.mp hZS) hidem ?_
    intro hbot
    apply hSbot
    rw [← hSX, Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact Subgroup.le_centralizer_iff.mp
      (hYZ.trans (sup_le hYc (Subgroup.le_centralizer_iff.mp hbot)))
  exact kleinFour_or_quaternion_of_minimal_commutator hZ3 (hT.to_le hST) hSZ hSbot hZmin

theorem exists_commutatorPiece_le_centralizer [Finite G] {X T B : Subgroup G}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hX3 : IsPGroup 3 X) (hT : IsPGroup 2 T)
    (hXT : X ≤ Subgroup.normalizer (T : Set G))
    (hfaith : X ⊓ Subgroup.centralizer (T : Set G) = ⊥) (hBT : B ≤ T)
    (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (hA : X ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) :
    ∃ S, IsCommutatorPiece X T S ∧ S ≤ Subgroup.centralizer (B : Set G) ∧
      ¬ X ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (S : Set G) := by
  set A := X ⊓ Subgroup.centralizer (B : Set G) with hA_def
  set C := T ⊓ Subgroup.centralizer (B : Set G) with hC_def
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXT hx, mem_normalizer_centralizer (hXB hx)⟩
  have hC2 : IsPGroup 2 C := hT.to_le inf_le_left
  have hXne : X ≠ ⊥ := fun h => hA (by rw [hA_def, h, bot_inf_eq])
  have hcop : Nat.Coprime 3 (Nat.card C) := by
    obtain ⟨k, hk⟩ := hC2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_hyperplane_generation 3
    Nat.prime_three X C hX hXne hXC hcop
  obtain ⟨Y, hYX, hY3, hAW⟩ : ∃ Y : Subgroup G, Y ≤ X ∧ (Y.subgroupOf X).index = 3 ∧
      ¬ A ≤ Subgroup.centralizer
        ((C ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
    by_contra hcon
    push Not at hcon
    have hCA : C ≤ Subgroup.centralizer (A : Set G) := by
      rw [← hgen]
      refine iSup_le fun Y => iSup_le fun hYX => iSup_le fun hY3 => ?_
      exact Subgroup.le_centralizer_iff.mp (hcon Y hYX hY3)
    have hAT := le_centralizer_of_le_centralizer_inf_centralizer (p := 2) hT
      (not_two_dvd_card_of_isPGroup_three (hX3.to_le inf_le_left)) hBT
      (inf_le_left.trans hXT) inf_le_right (Subgroup.le_centralizer_iff.mp hCA)
    apply hA
    rw [eq_bot_iff, ← hfaith]
    exact le_inf inf_le_left hAT
  set W := C ⊓ Subgroup.centralizer (Y : Set G) with hW_def
  have hXY : X ≤ Subgroup.centralizer (Y : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hX.1.is_comm.comm ⟨y, hYX hy⟩ ⟨x, hx⟩)
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXC hx,
      mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ (hXY hx))⟩
  have hW2 : IsPGroup 2 W := hC2.to_le inf_le_left
  set U := ⁅W, X⁆ with hU_def
  have hUW : U ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hXW
  have hUX : ⁅U, X⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three X W
      hX3 (not_three_dvd_card_of_isPGroup_two hW2) hXW
  have hUbot : U ≠ ⊥ := by
    intro h
    apply hAW
    rw [hU_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact inf_le_left.trans (Subgroup.le_centralizer_iff.mp h)
  obtain ⟨S, ⟨hSU, hSX, hSbot⟩, hSmin⟩ := exists_minimal_subgroup
    (fun S' => S' ≤ U ∧ ⁅S', X⁆ = S' ∧ S' ≠ ⊥) ⟨le_rfl, hUX, hUbot⟩
  have hSW : S ≤ W := hSU.trans hUW
  have hSC : S ≤ C := hSW.trans inf_le_left
  have hYS : Y ≤ X ⊓ Subgroup.centralizer (S : Set G) :=
    le_inf hYX (Subgroup.le_centralizer_iff.mp (hSW.trans inf_le_right))
  have hYcard : Nat.card Y * 3 = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := Y) (K := X)
    rw [inf_of_le_left hYX] at h
    rw [← h, Subgroup.relIndex, hY3, mul_comm]
  have hSne : X ⊓ Subgroup.centralizer (S : Set G) ≠ X := by
    intro h
    apply hSbot
    rw [← hSX, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hXc : X ≤ Subgroup.centralizer (S : Set G) := by
      rw [← h]
      exact inf_le_right
    exact Subgroup.le_centralizer_iff.mp hXc
  have hYeq := eq_of_le_of_le_of_card_mul_three hYS inf_le_left hSne hYcard
  refine ⟨S, ⟨hSC.trans inf_le_left, hSX, hSbot, ?_, ?_⟩, hSC.trans inf_le_right, ?_⟩
  · intro S' hS'S hS'X hS'bot
    exact hSmin S' hS'S ⟨hS'S.trans hSU, hS'X, hS'bot⟩
  · rw [← hYeq]
    exact hYcard
  · intro hAS
    apply hAW
    have hAY : A ≤ Y := by
      rw [hYeq]
      exact le_inf inf_le_left hAS
    exact hAY.trans (Subgroup.le_centralizer_iff.mp inf_le_right)

theorem exists_commutatorPieces [Finite G] {X T : Subgroup G} {n : ℕ}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hXn : Nat.card X = 3 ^ n) (hT : IsPGroup 2 T)
    (hXT : X ≤ Subgroup.normalizer (T : Set G))
    (hfaith : X ⊓ Subgroup.centralizer (T : Set G) = ⊥) :
    ∀ k ≤ n, ∃ S : ℕ → Subgroup G, (∀ j < k, IsCommutatorPiece X T (S j)) ∧
      (∀ i < k, ∀ j < k, i ≠ j → S i ≤ Subgroup.centralizer (S j : Set G)) ∧
      Nat.card (X ⊓ Subgroup.centralizer ((⨆ j < k, S j : Subgroup G) : Set G) :
        Subgroup G) * 3 ^ k = Nat.card X := by
  have hX3 : IsPGroup 3 X := IsPGroup.of_card hXn
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => ⊥, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    have h0 : (⨆ j < 0, (fun _ : ℕ => (⊥ : Subgroup G)) j) = ⊥ := by simp
    rw [h0, inf_centralizer_eq_of_eq_bot rfl, pow_zero, mul_one]
  | succ k ih =>
    intro hk
    obtain ⟨S, hpiece, hcomm, hcard⟩ := ih (Nat.le_of_succ_le hk)
    set B := ⨆ j < k, S j with hB_def
    have hBT : B ≤ T := iSup₂_le fun j hj => (hpiece j hj).1
    have hXB : X ≤ Subgroup.normalizer (B : Set G) :=
      le_normalizer_iSup fun j => le_normalizer_iSup fun hj =>
        Subgroup.le_normalizer_iff_commutator_le_left.mpr (hpiece j hj).2.1.le
    have hAne : X ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot, one_mul, hXn] at hcard
      have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hcard
      omega
    obtain ⟨Snew, hSpiece, hSB, hAS⟩ :=
      exists_commutatorPiece_le_centralizer hX hX3 hT hXT hfaith hBT hXB hAne
    refine ⟨fun j => if j < k then S j else Snew, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j < k
      · simp only [hjk, ↓reduceIte]
        exact hpiece j hjk
      · simp only [hjk, ↓reduceIte]
        exact hSpiece
    · intro i hi j hj hij
      have hSiB : ∀ i < k, S i ≤ B := fun i hi => le_iSup₂_of_le i hi le_rfl
      by_cases hik : i < k <;> by_cases hjk : j < k
      · simp only [hik, hjk, ↓reduceIte]
        exact hcomm i hik j hjk hij
      · simp only [hik, hjk, ↓reduceIte]
        exact Subgroup.le_centralizer_iff.mp
          (hSB.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hSiB i hik))))
      · simp only [hik, hjk, ↓reduceIte]
        exact hSB.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hSiB j hjk)))
      · exfalso
        omega
    · have hsup : (⨆ j < k + 1, (fun j => if j < k then S j else Snew) j) = B ⊔ Snew := by
        rw [Nat.iSup_lt_succ]
        congr 1
        · exact iSup_congr fun j => iSup_congr fun hj => by simp only [hj, ↓reduceIte]
        · simp only [lt_irrefl, ↓reduceIte]
      rw [hsup, centralizer_sup_eq, inf_inf_distrib_left, pow_succ', ← mul_assoc]
      have hAY : ¬ X ⊓ Subgroup.centralizer (B : Set G) ≤
          X ⊓ Subgroup.centralizer (Snew : Set G) := fun h => hAS (h.trans inf_le_right)
      rw [card_inf_mul_three_eq hXn inf_le_left inf_le_left hSpiece.2.2.2.2 hAY]
      exact hcard

theorem three_le_card_inf_centralizer_iSup_ne [Finite G] {X : Subgroup G} {S : ℕ → Subgroup G}
    {n i : ℕ} (hXn : Nat.card X = 3 ^ n) (hi : i < n)
    (hY : ∀ j < n, Nat.card (X ⊓ Subgroup.centralizer (S j : Set G) : Subgroup G) * 3 =
      Nat.card X) :
    3 ≤ Nat.card (X ⊓ Subgroup.centralizer
      ((⨆ j < n, ⨆ (_ : j ≠ i), S j : Subgroup G) : Set G) : Subgroup G) := by
  have key : ∀ m ≤ n, Nat.card X * (if i < m then 3 else 1) ≤
      Nat.card (X ⊓ Subgroup.centralizer
        ((⨆ j < m, ⨆ (_ : j ≠ i), S j : Subgroup G) : Set G) : Subgroup G) * 3 ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⨆ j < 0, ⨆ (_ : j ≠ i), S j) = ⊥ := by simp
      rw [h0, inf_centralizer_eq_of_eq_bot rfl]
      simp
    | succ m ih =>
      intro hm
      have ih' := ih (Nat.le_of_succ_le hm)
      rw [Nat.iSup_lt_succ, pow_succ']
      by_cases hmi : m = i
      · subst hmi
        have hbot : (⨆ (_ : m ≠ m), S m) = ⊥ := iSup_neg (fun h => h rfl)
        rw [hbot, sup_bot_eq]
        simp only [lt_irrefl, ↓reduceIte, mul_one] at ih'
        simp only [Nat.lt_succ_self, ↓reduceIte]
        nlinarith [ih']
      · have hS : (⨆ (_ : m ≠ i), S m) = S m := iSup_pos hmi
        rw [hS, centralizer_sup_eq, inf_inf_distrib_left]
        have hc : (if i < m + 1 then 3 else 1) = (if i < m then 3 else 1) := by
          by_cases h : i < m
          · simp [h, Nat.lt_succ_of_lt h]
          · have : ¬ i < m + 1 := by omega
            simp [h, this]
        rw [hc]
        have h3 := card_le_card_inf_mul_three (A := X ⊓ Subgroup.centralizer
          ((⨆ j < m, ⨆ (_ : j ≠ i), S j : Subgroup G) : Set G))
          (Y := X ⊓ Subgroup.centralizer (S m : Set G)) inf_le_left inf_le_left (hY m (by omega))
        exact ih'.trans (le_of_le_of_eq (Nat.mul_le_mul_right (3 ^ m) h3) (by ring))
  have h := key n le_rfl
  simp only [hi, ↓reduceIte] at h
  rw [hXn] at h
  have hpos : 0 < 3 ^ n := by positivity
  have h' : 3 * 3 ^ n ≤ Nat.card (X ⊓ Subgroup.centralizer
      ((⨆ j < n, ⨆ (_ : j ≠ i), S j : Subgroup G) : Set G) : Subgroup G) * 3 ^ n := by
    rw [mul_comm 3]
    exact h
  exact Nat.le_of_mul_le_mul_right h' hpos

theorem minimal_faithful_central_product [Finite G] {X T : Subgroup G} {n : ℕ}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hXn : Nat.card X = 3 ^ n) (hT : IsPGroup 2 T)
    (hXT : X ≤ Subgroup.normalizer (T : Set G))
    (hfaith : X ⊓ Subgroup.centralizer (T : Set G) = ⊥)
    (hmin : ∀ T' ≤ T, X ≤ Subgroup.normalizer (T' : Set G) →
      X ⊓ Subgroup.centralizer (T' : Set G) = ⊥ → T' = T) :
    ∃ Xs : Fin n → Subgroup G, (∀ i, Xs i ≤ X ∧ Nat.card (Xs i) = 3) ∧ iSupIndep Xs ∧
      (⨆ i, Xs i) = X ∧
      (∀ i, IsKleinFour (⁅Xs i, T⁆ : Subgroup G) ∨
        Nonempty ((⁅Xs i, T⁆ : Subgroup G) ≃* QuaternionGroup 2)) ∧
      (∀ i j, i ≠ j → ⁅⁅Xs i, T⁆, ⁅Xs j, T⁆⁆ = ⊥) ∧ (⨆ i, ⁅Xs i, T⁆) = T ∧
      (∀ i, X ≤ Subgroup.normalizer ((⁅Xs i, T⁆ : Subgroup G) : Set G)) ∧
      (∀ i j, i ≠ j → Xs i ≤ Subgroup.centralizer ((⁅Xs j, T⁆ : Subgroup G) : Set G)) := by
  have hX3 : IsPGroup 3 X := IsPGroup.of_card hXn
  obtain ⟨S, hpiece, hcomm, hcard⟩ := exists_commutatorPieces hX hXn hT hXT hfaith n le_rfl
  set B := ⨆ j < n, S j with hB_def
  have hBT : B ≤ T := iSup₂_le fun j hj => (hpiece j hj).1
  have hXS : ∀ j < n, X ≤ Subgroup.normalizer (S j : Set G) := fun j hj =>
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hpiece j hj).2.1.le
  have hXB : X ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_iSup fun j => le_normalizer_iSup fun hj => hXS j hj
  have hAB : X ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
    rw [hXn] at hcard
    have hpos : 0 < 3 ^ n := by positivity
    have h1 : Nat.card (X ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) = 1 :=
      Nat.eq_of_mul_eq_mul_right hpos (hcard.trans (one_mul _).symm)
    exact Subgroup.card_eq_one.mp h1
  have hBeq : B = T := hmin B hBT hXB hAB
  set O : ℕ → Subgroup G := fun i => ⨆ j < n, ⨆ (_ : j ≠ i), S j with hO_def
  set Xs : ℕ → Subgroup G := fun i => X ⊓ Subgroup.centralizer (O i : Set G) with hXs_def
  have hXsX : ∀ i, Xs i ≤ X := fun i => inf_le_left
  have hTsplit : ∀ i < n, T ≤ S i ⊔ O i := by
    intro i hi
    rw [← hBeq]
    refine iSup₂_le fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj (le_iSup_of_le hji le_rfl))
  have hOc : ∀ i < n, O i ≤ Subgroup.centralizer (S i : Set G) := fun i hi =>
    iSup₂_le fun j hj => iSup_le fun hji => hcomm j hj i hi hji
  have hXsS : ∀ i < n, Xs i ⊓ Subgroup.centralizer (S i : Set G) = ⊥ := by
    intro i hi
    rw [eq_bot_iff, ← hfaith]
    rintro g ⟨⟨hgX, hgO⟩, hgS⟩
    refine ⟨hgX, ?_⟩
    have hg : g ∈ Subgroup.centralizer ((S i ⊔ O i : Subgroup G) : Set G) := by
      rw [centralizer_sup_eq]
      exact ⟨hgS, hgO⟩
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hTsplit i hi)) hg
  have hXscard : ∀ i < n, Nat.card (Xs i) = 3 := by
    intro i hi
    apply le_antisymm
    · have h3 := card_le_card_inf_mul_three (A := Xs i)
        (Y := X ⊓ Subgroup.centralizer (S i : Set G)) (hXsX i) inf_le_left
        (hpiece i hi).2.2.2.2
      have hbot : Xs i ⊓ (X ⊓ Subgroup.centralizer (S i : Set G)) = ⊥ :=
        eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (hXsS i hi).le)
      rw [hbot, Subgroup.card_bot, one_mul] at h3
      exact h3
    · exact three_le_card_inf_centralizer_iSup_ne hXn hi fun j hj => (hpiece j hj).2.2.2.2
  have hcommT : ∀ i < n, ⁅Xs i, T⁆ = S i := by
    intro i hi
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg t ht
      exact commutatorElement_mem_of_mem_sup (hXS i hi (hXsX i hg)) hg.2
        ((hOc i hi).trans (Subgroup.centralizer_le_normalizer _)) (hTsplit i hi ht)
    · set R := ⁅S i, Xs i⁆ with hR_def
      have hXsN : Xs i ≤ Subgroup.normalizer (S i : Set G) := (hXsX i).trans (hXS i hi)
      have hRS : R ≤ S i := Subgroup.le_normalizer_iff_commutator_le_left.mp hXsN
      have hS2 : IsPGroup 2 (S i) := hT.to_le (hpiece i hi).1
      have hXsC : X ≤ Subgroup.centralizer (Xs i : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (hX.1.is_comm.comm ⟨y, hXsX i hy⟩ ⟨x, hx⟩)
      have hXR : X ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
        mem_normalizer_commutator (hXS i hi hx) (Subgroup.centralizer_le_normalizer _ (hXsC hx))
      have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
        Nat.prime_three (Xs i) (S i) (hX3.to_le (hXsX i)) (not_three_dvd_card_of_isPGroup_two hS2)
        hXsN
      rcases commutator_eq_bot_or_eq_of_minimal hX3 hS2 (hpiece i hi).2.2.2.1 hRS hXR with h | h
      · exfalso
        have hidem' : ⁅R, Xs i⁆ = R := hidem
        have hRbot : R = ⊥ := by
          rw [← hidem']
          exact eq_bot_iff.mpr ((Subgroup.commutator_mono le_rfl (hXsX i)).trans h.le)
        rw [hR_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hRbot
        have hle : Xs i ≤ Xs i ⊓ Subgroup.centralizer (S i : Set G) :=
          le_inf le_rfl (Subgroup.le_centralizer_iff.mp hRbot)
        rw [hXsS i hi] at hle
        have := hXscard i hi
        rw [le_bot_iff.mp hle, Subgroup.card_bot] at this
        omega
      · calc S i = R := h.symm
          _ ≤ ⁅T, Xs i⁆ := Subgroup.commutator_mono (hpiece i hi).1 le_rfl
          _ = ⁅Xs i, T⁆ := Subgroup.commutator_comm _ _
  have hind : iSupIndep fun i : Fin n => Xs i := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff, ← hXsS i i.2]
    refine inf_le_inf_left _ (iSup₂_le fun j hji => ?_)
    refine inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ?_))
    exact le_iSup₂_of_le i.val i.2 (le_iSup_of_le (fun h => hji (Fin.ext h).symm) le_rfl)
  have hsupX : (⨆ i : Fin n, Xs i) = X := by
    have hcommX : Pairwise fun i j : Fin n => ∀ x y : G, x ∈ Xs i → y ∈ Xs j → Commute x y := by
      intro i j _ x y hx hy
      exact congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hXsX i hx⟩ ⟨y, hXsX j hy⟩)
    have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcommX) hind
    have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcommX)
    have hcardsup : Nat.card (⨆ i : Fin n, Xs i : Subgroup G) = 3 ^ n := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi,
        Finset.prod_congr rfl (fun (i : Fin n) _ => hXscard i i.2), Finset.prod_const,
        Finset.card_univ,
        Fintype.card_fin]
    exact Subgroup.eq_of_le_of_card_ge (iSup_le fun i => hXsX i) (by rw [hcardsup, hXn])
  refine ⟨fun i => Xs i, fun i => ⟨hXsX i, hXscard i i.2⟩, hind, hsupX, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show IsKleinFour (⁅Xs i, T⁆ : Subgroup G) ∨
      Nonempty ((⁅Xs i, T⁆ : Subgroup G) ≃* QuaternionGroup 2)
    rw [hcommT i i.2]
    exact (hpiece i i.2).kleinFour_or_quaternion hX hT
  · intro i j hij
    show ⁅⁅Xs i, T⁆, ⁅Xs j, T⁆⁆ = ⊥
    rw [hcommT i i.2, hcommT j j.2]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcomm i i.2 j j.2 (fun h => hij (Fin.ext h)))
  · calc (⨆ i : Fin n, ⁅Xs i, T⁆) = ⨆ i : Fin n, S i := iSup_congr fun i => hcommT i i.2
      _ = B := le_antisymm (iSup_le fun i => le_iSup₂_of_le i.val i.2 le_rfl)
          (iSup₂_le fun j hj => le_iSup_of_le ⟨j, hj⟩ le_rfl)
      _ = T := hBeq
  · intro i
    show X ≤ Subgroup.normalizer ((⁅Xs i, T⁆ : Subgroup G) : Set G)
    rw [hcommT i i.2]
    exact hXS i i.2
  · intro i j hij
    show Xs i ≤ Subgroup.centralizer ((⁅Xs j, T⁆ : Subgroup G) : Set G)
    rw [hcommT j j.2]
    refine inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ?_))
    exact le_iSup₂_of_le j.val j.2 (le_iSup_of_le (fun h => hij (Fin.ext h).symm) le_rfl)

end CFSG.RankThree.PartTwo.Source
