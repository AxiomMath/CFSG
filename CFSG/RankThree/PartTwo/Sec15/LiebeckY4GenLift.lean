module

import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4.Gen

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_scriptQZero_lift {A B C YB : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hCdef : C = Subgroup.centralizer (B : Set G))
    (hYBC : YB ≤ C) (hAYB : A ≤ Subgroup.normalizer (YB : Set G))
    (hYBle : YB ≤ pPrimeCoreOf 3 C ⊔ lB A B)
    {Qt : Type*} [Group Qt] [Finite Qt] (π : ↥C →* Qt)
    (hker : ∀ c, π c = 1 → (c : G) ∈ pPrimeCoreOf 3 C)
    (hπB : ∀ b c : ↥C, (b : G) ∈ B → π b * π c = π c * π b)
    (a₀ : ↥C) (ha₀A : (a₀ : G) ∈ A) (ha₀B : (a₀ : G) ∉ B)
    (V : Subgroup Qt) (hVYB : V ≤ (YB.subgroupOf C).map π)
    (hV3 : ¬ 3 ∣ Nat.card V) (hxV : π a₀ ∈ Subgroup.normalizer (V : Set Qt))
    (hVfix : ∀ v ∈ V, v * π a₀ = π a₀ * v → v = 1) :
    ∃ Q ∈ scriptQZero A (lB A), Q ≤ YB ∧ V ≤ (Q.subgroupOf C).map π := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ C := fun x hx => hCdef ▸
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hB.1 hy) x hx
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 g g.2)⟩
  have hN3 : Nat.Coprime 3 (Nat.card (pPrimeCoreOf 3 C)) := coprime_card_pPrimeCoreOf 3 C
  let f : ↥YB →* Qt := π.comp (Subgroup.inclusion hYBC)
  set R₁ : Subgroup G := (V.comap f).map YB.subtype with hR₁
  have hR₁YB : R₁ ≤ YB := Subgroup.map_subtype_le _
  have hker3 : ¬ 3 ∣ Nat.card f.ker := by
    intro h3
    have hle : f.ker.map YB.subtype ≤ pPrimeCoreOf 3 C := by
      rintro _ ⟨y, hy, rfl⟩
      exact hker _ (MonoidHom.mem_ker.mp hy)
    have h3' : 3 ∣ Nat.card (pPrimeCoreOf 3 C) := by
      refine h3.trans ?_
      rw [← Subgroup.card_map_of_injective YB.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 h3'
  have hR₁3 : ¬ 3 ∣ Nat.card R₁ := by
    rw [hR₁, Subgroup.card_map_of_injective YB.subtype_injective]
    exact Item148HJ.not_dvd_card_comap f hV3 hker3
  have hπA : ∀ (a : G) (ha : a ∈ C), a ∈ A → π ⟨a, ha⟩ ∈ Subgroup.normalizer (V : Set Qt) := by
    set S : Subgroup G := ((Subgroup.normalizer (V : Set Qt)).comap π).map C.subtype with hS
    have hmemS : ∀ (a : G) (ha : a ∈ C),
        a ∈ S ↔ π ⟨a, ha⟩ ∈ Subgroup.normalizer (V : Set Qt) := by
      intro a ha
      constructor
      · rintro ⟨c, hc, hca⟩
        have : c = ⟨a, ha⟩ := Subtype.ext hca
        exact this ▸ hc
      · intro hh
        exact ⟨⟨a, ha⟩, hh, rfl⟩
    have hBS : B ≤ S := by
      intro b hb
      have hbC : b ∈ C := hAC (hB.1 hb)
      rw [hmemS b hbC]
      refine Item148HJ.mem_normalizer_of_conj_mem fun v hv => ?_
      obtain ⟨y₀, -, rfl⟩ := hVYB hv
      have := hπB ⟨b, hbC⟩ y₀ hb
      rw [this, mul_inv_cancel_right]
      exact hv
    have ha₀S : Subgroup.zpowers (a₀ : G) ≤ S :=
      Subgroup.zpowers_le.mpr ((hmemS a₀ a₀.2).mpr hxV)
    have hAS : A ≤ S := (le_sup_zpowers_of_not_mem h.isE27' hB ha₀A ha₀B).trans
      (sup_le hBS ha₀S)
    intro a ha haA
    exact (hmemS a ha).mp (hAS haA)
  have hAR : A ≤ Subgroup.normalizer (R₁ : Set G) := by
    intro a ha
    refine Item148HJ.mem_normalizer_of_conj_mem fun u hu => ?_
    obtain ⟨y, hy, rfl⟩ := hu
    have haC : a ∈ C := hAC ha
    have hay : a * (y : G) * a⁻¹ ∈ YB := (Subgroup.mem_normalizer_iff.mp (hAYB ha) y).mp y.2
    refine ⟨⟨a * y * a⁻¹, hay⟩, ?_, rfl⟩
    have hf : f ⟨a * (y : G) * a⁻¹, hay⟩ = π ⟨a, haC⟩ * f y * (π ⟨a, haC⟩)⁻¹ := by
      show π (Subgroup.inclusion hYBC ⟨a * (y : G) * a⁻¹, hay⟩) = _
      have : Subgroup.inclusion hYBC ⟨a * (y : G) * a⁻¹, hay⟩ =
          ⟨a, haC⟩ * Subgroup.inclusion hYBC y * ⟨a, haC⟩⁻¹ := Subtype.ext (by simp)
      rw [this, map_mul, map_mul, map_inv]
      rfl
    show f ⟨_, hay⟩ ∈ V
    rw [hf]
    exact (Subgroup.mem_normalizer_iff.mp (hπA a haC ha) (f y)).mp hy
  set Q : Subgroup G := ⁅R₁, A⁆ with hQ
  have hQR : Q ≤ R₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hAR
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.normalizer_commutator_ge_right R₁ A
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => hR₁3 (h3.trans (Subgroup.card_dvd_of_le hQR))
  have hQcomm : Q = ⁅Q, A⁆ :=
    (CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three A
      R₁ hA3 hAR ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR₁3)).symm
  have hQY : Q ≤ YB := hQR.trans hR₁YB
  have hqB : ∀ B', IsHyperplane A B' →
      Q ⊓ Subgroup.centralizer (B' : Set G) ≤ qBound A (lB A) B' := by
    intro B' hB'
    by_cases hBB' : B' = B
    · have hq : qBound A (lB A) B = pPrimeCoreOf 3 C ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ lB A B := by
        rw [qBound, hCdef]
      rw [hBB', ← hCdef, hq]
      calc Q ⊓ C ≤ Q := inf_le_left
        _ ≤ YB := hQY
        _ ≤ pPrimeCoreOf 3 C ⊔ lB A B := hYBle
        _ ≤ _ := sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · have hnle : ¬ B' ≤ B := fun hle => hBB' (Subgroup.eq_of_le_of_card_ge hle (by
        have h1 := hB.2
        have h2 := hB'.2
        omega))
      obtain ⟨d', hd'B', hd'B⟩ := SetLike.not_le_iff_exists.mp hnle
      have hAB : A ≤ B ⊔ Subgroup.zpowers d' :=
        le_sup_zpowers_of_not_mem h.isE27' hB (hB'.1 hd'B') hd'B
      intro x hx
      have hxd' : x ∈ Subgroup.centralizer ({d'} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hx.2 d' hd'B').symm
      have hxA : x ∈ Subgroup.centralizer (A : Set G) :=
        mem_centralizer_of_le_sup hAB (hCdef ▸ hYBC (hQY hx.1)) hxd'
      have hqb : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ qBound A (lB A) B' :=
        le_sup_right.trans le_sup_left
      exact hqb (inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian h) hQ3 ⟨hx.1, hxA⟩)
  refine ⟨Q, ⟨mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ, hqB⟩,
    hQcomm⟩, hQY, ?_⟩
  intro v hv
  set x := π a₀ with hx
  have hxV' : ∀ w ∈ V, x * w * x⁻¹ ∈ V := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hxV w).mp hw
  let ψ : V → V := fun w => ⟨(w : Qt) * x * (w : Qt)⁻¹ * x⁻¹, by
      have h1 : x * (w : Qt)⁻¹ * x⁻¹ ∈ V := hxV' _ (V.inv_mem w.2)
      have := V.mul_mem w.2 h1
      simpa [mul_assoc] using this⟩
  have hψ : Function.Injective ψ := by
    intro w w' hww'
    have h1 : (w : Qt) * x * (w : Qt)⁻¹ * x⁻¹ = (w' : Qt) * x * (w' : Qt)⁻¹ * x⁻¹ :=
      congrArg Subtype.val hww'
    have h2 : (w : Qt) * x * (w : Qt)⁻¹ = (w' : Qt) * x * (w' : Qt)⁻¹ := mul_right_cancel h1
    have hu : ((w' : Qt)⁻¹ * w) * x = x * ((w' : Qt)⁻¹ * w) := by
      calc (w' : Qt)⁻¹ * w * x = (w' : Qt)⁻¹ * ((w : Qt) * x * (w : Qt)⁻¹) * w := by group
        _ = (w' : Qt)⁻¹ * ((w' : Qt) * x * (w' : Qt)⁻¹) * w := by rw [h2]
        _ = x * ((w' : Qt)⁻¹ * w) := by group
    have hu1 : (w' : Qt)⁻¹ * w = 1 := hVfix _ (V.mul_mem (V.inv_mem w'.2) w.2) hu
    exact Subtype.ext (inv_mul_eq_one.mp hu1).symm
  obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.mp hψ ⟨v, hv⟩
  obtain ⟨y₀, hy₀, hy₀w⟩ := hVYB w.2
  have hy₀YB : (y₀ : G) ∈ YB := Subgroup.mem_subgroupOf.mp hy₀
  have hy₀R : (y₀ : G) ∈ R₁ := ⟨⟨y₀, hy₀YB⟩, by
    show π y₀ ∈ V
    rw [hy₀w]; exact w.2, rfl⟩
  have hqQ : ⁅(y₀ : G), (a₀ : G)⁆ ∈ Q := Subgroup.commutator_mem_commutator hy₀R ha₀A
  refine ⟨⁅y₀, a₀⁆, Subgroup.mem_subgroupOf.mpr hqQ, ?_⟩
  rw [map_commutatorElement, hy₀w]
  have := congrArg Subtype.val hw
  simpa [commutatorElement_def] using this

private theorem map_conj_eq_self {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

private theorem map_conj_mem_thetaComponentsIn {M : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (M : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaComponentsIn M) :
    X.map (MulAut.conj a).toMonoidHom ∈ thetaComponentsIn M := by
  have hM : M.map (MulAut.conj a).toMonoidHom = M := map_conj_eq_self ha
  set σ : ↥M ≃* ↥M := ((MulAut.conj a).subgroupMap M).trans (MulEquiv.subgroupCongr hM)
  obtain ⟨X', hX', rfl⟩ := hX
  refine ⟨X'.map σ.toMonoidHom, map_mulEquiv_mem_thetaComponents Nat.prime_three σ hX', ?_⟩
  change (X'.map σ.toMonoidHom).map M.subtype = (X'.map M.subtype).map (MulAut.conj a).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem aschbacherSolvableCore_le_pPrimeCore {H : Type*} [Group H] [Finite H] :
    aschbacherSolvableCore 3 H ≤ CFSG.pPrimeCore 3 H := by
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have : (aschbacherSolvableCore 3 H).Normal := Subgroup.normal_of_characteristic _
  exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩

private theorem le_of_le_sup_of_le_sup {YB YB' O θ Q : Subgroup G}
    (hYBO : YB ≤ Subgroup.normalizer (O : Set G)) (hYB'O : YB' ≤ Subgroup.normalizer (O : Set G))
    (hcomm : ⁅YB, YB'⁆ ≤ O) (hθO : θ ≤ O) (hYBθ : YB ⊓ O ≤ θ)
    (hZ : ∀ y ∈ YB, (∀ z ∈ YB, ⁅y, z⁆ ∈ θ) → y ^ 3 ∈ θ)
    (hQ1 : Q ≤ YB ⊔ O) (hQ2 : Q ≤ YB' ⊔ O) (hQ3 : ¬ 3 ∣ Nat.card Q) : Q ≤ O := by
  intro q hq
  have hq1 : q ∈ ((YB : Set G) * (O : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right YB O hYBO]; exact hQ1 hq
  have hq2 : q ∈ ((YB' : Set G) * (O : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right YB' O hYB'O]; exact hQ2 hq
  obtain ⟨y, hy, o, ho, rfl⟩ := Set.mem_mul.mp hq1
  obtain ⟨y', hy', o', ho', hyo⟩ := Set.mem_mul.mp hq2
  have hu : y⁻¹ * y' ∈ O := by
    have : y⁻¹ * y' = o * o'⁻¹ := by
      calc y⁻¹ * y' = y⁻¹ * (y' * o') * o'⁻¹ := by group
        _ = y⁻¹ * (y * o) * o'⁻¹ := by rw [hyo]
        _ = o * o'⁻¹ := by group
    rw [this]
    exact O.mul_mem ho (O.inv_mem ho')
  have hconjO : ∀ g ∈ YB, ∀ u ∈ O, g * u * g⁻¹ ∈ O := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (hYBO hg) u).mp hu
  have hyc : ∀ z ∈ YB, ⁅y, z⁆ ∈ O := by
    intro z hz
    set u := y⁻¹ * y' with hu_def
    have hy'eq : y' = y * u := by rw [hu_def]; group
    have h1 : ⁅y', z⁆ ∈ O := by
      have : ⁅z, y'⁆ ∈ O := hcomm (Subgroup.commutator_mem_commutator hz hy')
      rw [← commutatorElement_inv]
      exact O.inv_mem this
    have h2 : ⁅u, z⁆ ∈ O := by
      rw [commutatorElement_def]
      have := hconjO z hz u⁻¹ (O.inv_mem hu)
      have e : u * z * u⁻¹ * z⁻¹ = u * (z * u⁻¹ * z⁻¹) := by group
      rw [e]
      exact O.mul_mem hu this
    have h3 : y * ⁅u, z⁆ * y⁻¹ ∈ O := hconjO y hy _ h2
    have key : ⁅y, z⁆ = (y * ⁅u, z⁆ * y⁻¹)⁻¹ * ⁅y', z⁆ := by
      rw [hy'eq]
      simp only [commutatorElement_def]
      group
    rw [key]
    exact O.mul_mem (O.inv_mem h3) h1
  have hy3 : y ^ 3 ∈ θ := hZ y hy fun z hz => hYBθ ⟨
    YB.mul_mem (YB.mul_mem (YB.mul_mem hy hz) (YB.inv_mem hy)) (YB.inv_mem hz), hyc z hz⟩
  have hq3 : (y * o) ^ 3 ∈ O := by
    have hy2 : (y⁻¹ * y⁻¹) ∈ YB := YB.mul_mem (YB.inv_mem hy) (YB.inv_mem hy)
    have e : (y * o) ^ 3 =
        y ^ 3 * ((y⁻¹ * y⁻¹) * o * (y⁻¹ * y⁻¹)⁻¹) * (y⁻¹ * o * y⁻¹⁻¹) * o := by
      rw [pow_succ, pow_two]; group
    rw [e]
    exact O.mul_mem (O.mul_mem (O.mul_mem (hθO hy3) (hconjO _ hy2 o ho))
      (hconjO _ (YB.inv_mem hy) o ho)) ho
  have hcop : Nat.Coprime 3 (orderOf (y * o)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Q hq)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact pow_mem hq3 j

private theorem exists_theta_facts {Y YB : Subgroup G} (hYB : YB ∈ thetaComponentsIn Y)
    (hcen3 : ∀ z ∈ Subgroup.center (↥YB ⧸ aschbacherSolvableCore 3 ↥YB), z ^ 3 = 1)
    (h3 : 3 ∣ Nat.card (↥YB ⧸ aschbacherSolvableCore 3 ↥YB)) :
    ∃ θ : Subgroup G, θ ≤ pPrimeCoreOf 3 Y ∧ YB ⊓ pPrimeCoreOf 3 Y ≤ θ ∧
      ∀ y ∈ YB, (∀ z ∈ YB, ⁅y, z⁆ ∈ θ) → y ^ 3 ∈ θ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L, hL, rfl⟩ := hYB
  set e : ↥L ≃* ↥(L.map Y.subtype) := L.equivMapOfInjective Y.subtype Y.subtype_injective with he
  set ē := quotThetaEquiv e with hē
  set θL := aschbacherSolvableCore 3 ↥L with hθL
  refine ⟨(θL.map L.subtype).map Y.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have h1 : (l : ↥Y) ∈ aschbacherSolvableCore 3 ↥Y := by
      have hl' : l ∈ (aschbacherSolvableCore 3 ↥Y).subgroupOf L := by
        rw [← aschbacherSolvableCore_eq_subgroupOf (H := ↥Y) Nat.prime_three hL.2.1]
        exact hl
      exact Subgroup.mem_subgroupOf.mp hl'
    exact ⟨(l : ↥Y), aschbacherSolvableCore_le_pPrimeCore h1, rfl⟩
  ·
    have hS3 : ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 ↥Y).subgroupOf L) := by
      intro h3'
      have hdvd : Nat.card ((CFSG.pPrimeCore 3 ↥Y).subgroupOf L) ∣
          Nat.card (CFSG.pPrimeCore 3 ↥Y) := by
        let f : (CFSG.pPrimeCore 3 ↥Y).subgroupOf L →* CFSG.pPrimeCore 3 ↥Y :=
          { toFun := fun x => ⟨((x : ↥L) : ↥Y), x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        refine Subgroup.card_dvd_of_injective f fun x y hxy => ?_
        have h := congrArg (fun z : CFSG.pPrimeCore 3 ↥Y => (z : ↥Y)) hxy
        exact Subtype.ext (Subtype.ext h)
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y)) (h3'.trans hdvd)
    have hq : IsQuasisimple (↥L ⧸ θL) := hL.2.2
    have hcenL : IsPGroup 3 (Subgroup.center (↥L ⧸ θL)) := fun z => ⟨1, by
      have hzc : ē (z : ↥L ⧸ θL) ∈ Subgroup.center (↥(L.map Y.subtype) ⧸
          aschbacherSolvableCore 3 ↥(L.map Y.subtype)) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨w', rfl⟩ := ē.surjective w
        have := Subgroup.mem_center_iff.mp z.2 w'
        rw [← map_mul, ← map_mul, this]
      have := hcen3 _ hzc
      apply Subtype.ext
      apply ē.injective
      simpa [map_pow] using this⟩
    have h3L : 3 ∣ Nat.card (↥L ⧸ θL) := by
      rw [Nat.card_congr ē.toEquiv]; exact h3
    have hSnorm : (((CFSG.pPrimeCore 3 ↥Y).subgroupOf L).map (QuotientGroup.mk' θL)).Normal :=
      Subgroup.Normal.map Subgroup.normal_subgroupOf _ (QuotientGroup.mk'_surjective θL)
    have hS3' : ¬ 3 ∣ Nat.card
        (((CFSG.pPrimeCore 3 ↥Y).subgroupOf L).map (QuotientGroup.mk' θL)) :=
      fun h' => hS3 (h'.trans (Subgroup.card_map_dvd _ _))
    have hbot := Item148HJ.eq_bot_of_normal_of_quasisimple' hq hcenL h3L hSnorm hS3'
    have hSθ : (CFSG.pPrimeCore 3 ↥Y).subgroupOf L ≤ θL := by
      intro l hl
      have : QuotientGroup.mk' θL l ∈ ((CFSG.pPrimeCore 3 ↥Y).subgroupOf L).map
          (QuotientGroup.mk' θL) := ⟨l, hl, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff l).mp this
    rintro _ ⟨⟨l, hl, rfl⟩, ⟨p, hp, hpl⟩⟩
    have hpl' : p = l := Subtype.ext hpl
    refine ⟨l, ⟨⟨l, hl⟩, hSθ (by
      show l ∈ CFSG.pPrimeCore 3 ↥Y
      exact hpl' ▸ hp), rfl⟩, rfl⟩
  · intro y hy hc
    obtain ⟨l, hl, rfl⟩ := hy
    have hmemθ : ∀ t : ↥L, ((t : ↥Y) : G) ∈ (θL.map L.subtype).map Y.subtype ↔ t ∈ θL := fun t =>
      (Subgroup.mem_map_iff_mem Y.subtype_injective).trans
        (Subgroup.mem_map_iff_mem L.subtype_injective)
    set l' : ↥L := ⟨l, hl⟩ with hl'
    have hcen : (QuotientGroup.mk l' : ↥L ⧸ θL) ∈ Subgroup.center (↥L ⧸ θL) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
      have h1 : ⁅(l : G), (((m : ↥L) : ↥Y) : G)⁆ ∈ (θL.map L.subtype).map Y.subtype :=
        hc _ ⟨(m : ↥Y), m.2, rfl⟩
      have h2 : ⁅l', m⁆ ∈ θL := (hmemθ ⁅l', m⁆).mp h1
      have h3 : QuotientGroup.mk' θL ⁅l', m⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h2
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3.symm
    have hcube : (QuotientGroup.mk l' : ↥L ⧸ θL) ^ 3 = 1 := by
      apply ē.injective
      rw [map_pow, map_one]
      apply hcen3
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := ē.surjective w
      have := Subgroup.mem_center_iff.mp hcen w'
      rw [← map_mul, ← map_mul, this]
    have : l' ^ 3 ∈ θL := by
      rw [← QuotientGroup.mk_pow] at hcube
      exact (QuotientGroup.eq_one_iff _).mp hcube
    exact (hmemθ (l' ^ 3)).mpr this

theorem normalizes_of_le_sup {A Y YB : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYB : YB ∈ thetaComponentsIn Y)
    (hcen3 : ∀ z ∈ Subgroup.center (↥YB ⧸ aschbacherSolvableCore 3 ↥YB), z ^ 3 = 1)
    (h3 : 3 ∣ Nat.card (↥YB ⧸ aschbacherSolvableCore 3 ↥YB))
    (hle : deltaZero A LB Y ≤ pPrimeCoreOf 3 Y ⊔ YB)
    (hnot : ¬ deltaZero A LB Y ≤ pPrimeCoreOf 3 Y) :
    A ≤ Subgroup.normalizer (YB : Set G) := by
  intro a ha
  by_contra hna
  obtain ⟨θ, hθO, hYBθ, hZ⟩ := exists_theta_facts hYB hcen3 h3
  have haY : a ∈ Subgroup.normalizer (Y : Set G) := hAY ha
  have hYB' := map_conj_mem_thetaComponentsIn haY hYB
  have hne : YB.map (MulAut.conj a).toMonoidHom ≠ YB := by
    intro h
    apply hna
    refine Item148HJ.mem_normalizer_of_conj_mem fun u hu => ?_
    rw [← h]
    exact Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hu
  have hcomm : ⁅YB, YB.map (MulAut.conj a).toMonoidHom⁆ ≤ pPrimeCoreOf 3 Y := by
    obtain ⟨L, hL, hLe⟩ := hYB
    obtain ⟨L', hL', hL'e⟩ := hYB'
    have hne' : L ≠ L' := fun h => hne (by rw [← hL'e, ← h, hLe])
    have := Item148HJ.commutator_le_of_mem_thetaComponents_of_ne hL hL' hne'
    rw [← hL'e, ← hLe, ← Subgroup.map_commutator]
    exact (Subgroup.map_mono this).trans
      (Subgroup.map_mono aschbacherSolvableCore_le_pPrimeCore)
  have hYBY : YB ≤ Y := le_of_mem_thetaComponentsIn hYB
  have hYB'Y : YB.map (MulAut.conj a).toMonoidHom ≤ Y := le_of_mem_thetaComponentsIn hYB'
  have hQO : ∀ Q ∈ collectionIn (scriptQZero A LB) Y, Q ≤ pPrimeCoreOf 3 Y := by
    rintro Q ⟨hQ0, hQY⟩
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ0.1.1.2.1
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ0.1.1.2.2
    have hQle : Q ≤ deltaZero A LB Y := le_deltaZero hQ0 hQY
    have hQ1 : Q ≤ YB ⊔ pPrimeCoreOf 3 Y := by
      rw [sup_comm]
      exact hQle.trans hle
    have hQ2 : Q ≤ YB.map (MulAut.conj a).toMonoidHom ⊔ pPrimeCoreOf 3 Y := by
      have h1 : Q.map (MulAut.conj a).toMonoidHom = Q := map_conj_eq_self (hAQ ha)
      have h2 : (pPrimeCoreOf 3 Y ⊔ YB).map (MulAut.conj a).toMonoidHom =
          pPrimeCoreOf 3 Y ⊔ YB.map (MulAut.conj a).toMonoidHom := by
        rw [Subgroup.map_sup, map_conj_eq_self (normalizer_le_normalizer_pPrimeCoreOf 3 Y haY)]
      calc Q = Q.map (MulAut.conj a).toMonoidHom := h1.symm
        _ ≤ (pPrimeCoreOf 3 Y ⊔ YB).map (MulAut.conj a).toMonoidHom :=
          Subgroup.map_mono (hQle.trans hle)
        _ = pPrimeCoreOf 3 Y ⊔ YB.map (MulAut.conj a).toMonoidHom := h2
        _ = _ := sup_comm _ _
    exact le_of_le_sup_of_le_sup (hYBY.trans (le_normalizer_pPrimeCoreOf 3 Y))
      (hYB'Y.trans (le_normalizer_pPrimeCoreOf 3 Y)) hcomm hθO hYBθ hZ hQ1 hQ2 hQ3
  exact hnot (sSup_le hQO)

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4.Gen
