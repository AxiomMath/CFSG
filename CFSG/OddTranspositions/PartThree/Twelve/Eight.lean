module

public import CFSG.OddTranspositions.PartThree.Twelve.EightModel
public import CFSG.OddTranspositions.PartThree.Twelve.SixComponent
import CFSG.OddTranspositions.PartThree.Twelve.Six
import CFSG.OddTranspositions.PartThree.Twelve.Four
import CFSG.OddTranspositions.PartThree.Twelve.FourU
import CFSG.OddTranspositions.SevenFourEight.SevenSix
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import CFSG.ClassicalInvolution.Asc77.AscSCH03
import CFSG.RankThree.CentralLift.ClassicalScalarCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

section EdgeCount

variable {G : Type} [Group G] {D : Set G}

theorem conj_mem_compSet_of_commute (hN : IsNormalSet D) {g u z e x : G} (hg : Commute g u)
    (hx : x ∈ compSet D u z e) :
    g * x * g⁻¹ ∈ compSet D u (g * z * g⁻¹) (g * e * g⁻¹) := by
  have hmaps : ∀ y ∈ commSet D u ∩ commSet D z,
      g * y * g⁻¹ ∈ commSet D u ∩ commSet D (g * z * g⁻¹) := fun y hy =>
    ⟨conj_mem_commSet_of_commute hN hg hy.1, conj_mem_commSet hN g hy.2⟩
  have h := reach_map_of_mapsTo (MulAut.conj g).toMonoidHom
    (E' := commSet D u ∩ commSet D (g * z * g⁻¹)) (fun y hy => by simpa using hmaps y hy) hx.2
  exact ⟨hmaps x hx.1, by simpa using h⟩

theorem image_conj_compSet (hN : IsNormalSet D) {g u : G} (hg : Commute g u) (z e : G) :
    (fun x => g * x * g⁻¹) '' compSet D u z e = compSet D u (g * z * g⁻¹) (g * e * g⁻¹) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact conj_mem_compSet_of_commute hN hg hx
  · intro hy
    have hg' : Commute g⁻¹ u := hg.inv_left
    have h1 := conj_mem_compSet_of_commute hN hg' hy
    refine ⟨g⁻¹ * y * g⁻¹⁻¹, ?_, by group⟩
    convert h1 using 2 <;> group

theorem commSet_inter_conj_self (u z : G) :
    commSet D u ∩ commSet D (u * z * u⁻¹) = commSet D u ∩ commSet D z := by
  ext x
  constructor
  · rintro ⟨hxu, hxz⟩
    refine ⟨hxu, hxz.1, ?_, fun h => hxz.2.2 ?_⟩
    · have h1 := (Commute.conj_iff u⁻¹).2 hxz.2.1
      have hx : u⁻¹ * x * u⁻¹⁻¹ = x := by
        rw [inv_inv, mul_assoc, hxu.2.1.eq, ← mul_assoc, inv_mul_cancel, one_mul]
      rwa [hx, show u⁻¹ * (u * z * u⁻¹) * u⁻¹⁻¹ = z by group] at h1
    · rw [h]
      have hzu : Commute z u := by rw [← h]; exact hxu.2.1
      rw [← hzu.eq, mul_inv_cancel_right]
  · rintro ⟨hxu, hxz⟩
    refine ⟨hxu, hxz.1, ?_, fun h => hxz.2.2 ?_⟩
    · have h1 := (Commute.conj_iff u).2 hxz.2.1
      have hx : u * x * u⁻¹ = x := by rw [hxu.2.1.symm.eq, mul_inv_cancel_right]
      rwa [hx] at h1
    · have hx : u * x * u⁻¹ = x := by rw [hxu.2.1.symm.eq, mul_inv_cancel_right]
      have h2 : u * x * u⁻¹ = u * z * u⁻¹ := by rw [hx, h]
      simpa using h2

theorem compSet_conj_self (u z e : G) : compSet D u (u * z * u⁻¹) e = compSet D u z e := by
  unfold compSet
  rw [commSet_inter_conj_self]

theorem compSet_eq_of_mem {x z e y : G} (hy : y ∈ compSet D x z e) :
    compSet D x z e = compSet D x z y := by
  ext a
  exact ⟨fun ha => ⟨ha.1, reach_trans (reach_symm hy.2) ha.2⟩,
    fun ha => ⟨ha.1, reach_trans hy.2 ha.2⟩⟩

theorem not_commute_conj_of_commute {g u w : G} (hg : Commute g u) (hwu : ¬ Commute w u) :
    ¬ Commute (g * w * g⁻¹) u := by
  intro h
  apply hwu
  have h1 := (Commute.conj_iff g⁻¹).2 h
  have hu : g⁻¹ * u * g⁻¹⁻¹ = u := by
    rw [inv_inv, mul_assoc, ← hg.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rwa [hu, show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at h1

theorem two_mul_ncard_mul_ncard_le [Finite G] (hN : IsNormalSet D) {u w d : G} (hw : w ∈ D)
    (hwu : ¬ Commute w u) (H : Subgroup G) (hH : ∀ h ∈ H, Commute h u) :
    2 * ({Ω' : Set G | ∃ h ∈ H, Ω' = (fun x => h * x * h⁻¹) '' compSet D u w d}.ncard *
      (compSet D u w d).ncard) ≤
      {p : G × G | p.1 ∈ commSet D u ∧ p.2 ∈ D ∧ ¬ Commute p.2 u ∧ Commute p.1 p.2}.ncard := by
  classical
  set Ω := compSet D u w d with hΩ
  set C := {Ω' : Set G | ∃ h ∈ H, Ω' = (fun x => h * x * h⁻¹) '' Ω} with hC
  set P := {p : G × G | p.1 ∈ commSet D u ∧ p.2 ∈ D ∧ ¬ Commute p.2 u ∧ Commute p.1 p.2}
    with hP
  have hch : ∀ Ω' : Set G, ∃ h : G, Ω' ∈ C → h ∈ H ∧ Ω' = (fun x => h * x * h⁻¹) '' Ω := by
    intro Ω'
    by_cases hΩ' : Ω' ∈ C
    · obtain ⟨h, hh, he⟩ := hΩ'
      exact ⟨h, fun _ => ⟨hh, he⟩⟩
    · exact ⟨1, fun h => absurd h hΩ'⟩
  choose c hc using hch
  let zz : Set G → Bool → G := fun Ω' b =>
    if b then c Ω' * w * (c Ω')⁻¹ else u * (c Ω' * w * (c Ω')⁻¹) * u⁻¹
  let Φ : (Set G × Bool) × G → G × G := fun p => (c p.1.1 * p.2 * (c p.1.1)⁻¹, zz p.1.1 p.1.2)
  have hcomp : ∀ Ω' ∈ C, ∀ b : Bool, Ω' = compSet D u (zz Ω' b) (c Ω' * d * (c Ω')⁻¹) := by
    intro Ω' hΩ' b
    obtain ⟨hh, he⟩ := hc Ω' hΩ'
    have e1 := he.trans (image_conj_compSet hN (hH _ hh) w d)
    cases b
    · exact e1.trans (compSet_conj_self u _ _).symm
    · exact e1
  have hmemΩ : ∀ Ω' ∈ C, ∀ b : Bool, ∀ x ∈ Ω,
      c Ω' * x * (c Ω')⁻¹ ∈ compSet D u (zz Ω' b) (c Ω' * d * (c Ω')⁻¹) := by
    intro Ω' hΩ' b x hx
    have hmem : c Ω' * x * (c Ω')⁻¹ ∈ Ω' := (Set.ext_iff.1 (hc Ω' hΩ').2 _).2 ⟨x, hx, rfl⟩
    exact (Set.ext_iff.1 (hcomp Ω' hΩ' b) _).1 hmem
  have hzD : ∀ Ω' ∈ C, ∀ b : Bool, zz Ω' b ∈ D := by
    intro Ω' hΩ' b
    cases b
    · exact hN _ _ (hN _ _ hw)
    · exact hN _ _ hw
  have hz1 : ∀ Ω' ∈ C, ¬ Commute (c Ω' * w * (c Ω')⁻¹) u := fun Ω' hΩ' =>
    not_commute_conj_of_commute (hH _ (hc Ω' hΩ').1) hwu
  have hzu : ∀ Ω' ∈ C, ∀ b : Bool, ¬ Commute (zz Ω' b) u := by
    intro Ω' hΩ' b
    cases b
    · exact not_commute_conj_of_commute (Commute.refl u) (hz1 Ω' hΩ')
    · exact hz1 Ω' hΩ'
  have hzne : ∀ Ω' ∈ C, zz Ω' true ≠ zz Ω' false := by
    intro Ω' hΩ' h
    apply hz1 Ω' hΩ'
    change c Ω' * w * (c Ω')⁻¹ = u * (c Ω' * w * (c Ω')⁻¹) * u⁻¹ at h
    have h2 : c Ω' * w * (c Ω')⁻¹ * u = u * (c Ω' * w * (c Ω')⁻¹) := by
      conv_lhs => rw [h]
      group
    exact h2
  have hmaps : Set.MapsTo Φ ((C ×ˢ Set.univ) ×ˢ Ω) P := by
    rintro ⟨⟨Ω', b⟩, x⟩ ⟨⟨hΩ', -⟩, hx⟩
    have hy := hmemΩ Ω' hΩ' b x hx
    exact ⟨(compSet_subset D u _ _ hy).1, hzD Ω' hΩ' b, hzu Ω' hΩ' b,
      ((compSet_subset D u _ _ hy).2).2.1⟩
  have hinj : Set.InjOn Φ ((C ×ˢ Set.univ) ×ˢ Ω) := by
    rintro ⟨⟨Ω₁, b₁⟩, x₁⟩ ⟨⟨hΩ₁, -⟩, hx₁⟩ ⟨⟨Ω₂, b₂⟩, x₂⟩ ⟨⟨hΩ₂, -⟩, hx₂⟩ hΦ
    simp only [Φ, Prod.mk.injEq] at hΦ
    obtain ⟨hy, hz⟩ := hΦ
    have hy₁ := hmemΩ Ω₁ hΩ₁ b₁ x₁ hx₁
    have hy₂ := hmemΩ Ω₂ hΩ₂ b₂ x₂ hx₂
    have hΩeq : Ω₁ = Ω₂ := by
      rw [hcomp Ω₁ hΩ₁ b₁, compSet_eq_of_mem hy₁, hcomp Ω₂ hΩ₂ b₂, compSet_eq_of_mem hy₂, hy, hz]
    subst hΩeq
    have hx : x₁ = x₂ := by simpa using hy
    subst hx
    have hb : b₁ = b₂ := by
      cases b₁ <;> cases b₂
      · rfl
      · exact absurd hz.symm (hzne Ω₁ hΩ₁)
      · exact absurd hz (hzne Ω₁ hΩ₁)
      · rfl
    rw [hb]
  have h1 := Set.ncard_le_ncard_of_injOn Φ hmaps hinj (Set.toFinite P)
  rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_bool] at h1
  linarith

end EdgeCount

theorem ncard_le_ncard_image_mul_ncard {K β : Type} [Group K] [Finite K] (φ : K → β)
    (S T : Set K) (hS : ∀ k ∈ T, ∀ k' ∈ T, φ k = φ k' → k⁻¹ * k' ∈ S) :
    T.ncard ≤ (φ '' T).ncard * S.ncard := by
  classical
  have hch : ∀ b : β, ∃ k : K, b ∈ φ '' T → k ∈ T ∧ φ k = b := by
    intro b
    by_cases hb : b ∈ φ '' T
    · obtain ⟨k, hk, rfl⟩ := hb
      exact ⟨k, fun _ => ⟨hk, rfl⟩⟩
    · exact ⟨1, fun h => absurd h hb⟩
  choose r hr using hch
  have hmaps : Set.MapsTo (fun k => (φ k, (r (φ k))⁻¹ * k)) T ((φ '' T) ×ˢ S) := by
    intro k hk
    have h1 := hr (φ k) ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk, rfl⟩, hS _ h1.1 _ hk h1.2⟩
  have hinj : Set.InjOn (fun k => (φ k, (r (φ k))⁻¹ * k)) T := by
    intro k _ k' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1] at h2
    exact mul_left_cancel h2
  have h := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
  rwa [Set.ncard_prod] at h

theorem natCard_SUid_four {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    Nat.card (SUid (unitaryInvolution F 2 f) 4) =
      (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) := by
  rw [SUid_eq_statedSU hF 4]
  exact CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩

section UFour

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem image_conj_image_conj (a b : G) (S : Set G) :
    (fun x => a * x * a⁻¹) '' ((fun x => b * x * b⁻¹) '' S) =
      (fun x => (a * b) * x * (a * b)⁻¹) '' S := by
  rw [Set.image_image]
  congr 1
  funext x
  group

theorem natCard_SUid_le_of_marked {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (H : Subgroup G)
    (ρ : H →* SUid (unitaryInvolution F 2 f) 4) (hρ : Function.Surjective ρ)
    {U : AddSubgroup (Fin 4 → F)} {Q : (Fin 4 → F) → F}
    (hU : IsFixedQuadForm (unitaryInvolution F 2 f) U Q) {Ω : Set G}
    (hρΩ : ∀ g, (∃ x : H, (x : G) ∈ Ω ∧ ρ x = g) ↔
      ∃ a ∈ U, Q a = 1 ∧ g = suTv (isUnitaryInvolution_unitaryInvolution hF) a 1) :
    Nat.card (SUid (unitaryInvolution F 2 f) 4) ≤
      2 * (2 ^ f * ((2 ^ f) ^ 2 - 1)) *
        ({Ω' : Set G | ∃ h ∈ H, Ω' = (fun x => h * x * h⁻¹) '' Ω}.ncard * Ω.ncard) := by
  classical
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨lam, hlam, hlam0, hlam1⟩ := exists_unitaryInvolution_eq_self_ne_zero_ne_one hF hf
  have hscal : ∀ l : F, unitaryInvolution F 2 f l * l = 1 → l ^ 4 = 1 → l = 1 := fun l _ h => by
    have h2 : l ^ 2 = 1 := frobenius_inj F 2 (by
      rw [frobenius_def, frobenius_def, ← pow_mul, one_pow]; exact h)
    exact frobenius_inj F 2 (by rw [frobenius_def, frobenius_def, h2, one_pow])
  have hq : Nat.card {c : F // unitaryInvolution F 2 f c = c} = 2 ^ f := by
    rw [← natCard_trace_eq hF (t := 0) (map_zero _)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro h
      rw [h]
      exact CharTwo.add_self_eq_zero x
    · intro h
      have e : unitaryInvolution F 2 f x = -x := by linear_combination h
      rw [e, CharTwo.neg_eq]
  set X := fixedQuadSubgroup (unitaryInvolution F 2 f) U Q with hXdef
  set cj : H → Set G := fun h => (fun x => (h : G) * x * (h : G)⁻¹) '' Ω with hcj
  set Stab : Set H := {h | cj h = Ω} with hStab
  set C := {Ω' : Set G | ∃ h ∈ H, Ω' = (fun x => h * x * h⁻¹) '' Ω} with hC
  set Vset : Set (Fin 4 → F) := {v | v ∈ U ∧ Q v = 1} with hV
  have hcj_mul : ∀ a b : H, cj (a * b) = (fun x => (a : G) * x * (a : G)⁻¹) '' cj b :=
    fun a b => (image_conj_image_conj (a : G) (b : G) Ω).symm
  have hcj1 : cj 1 = Ω := by simp [hcj]
  have hC1 : Nat.card H ≤ C.ncard * Stab.ncard := by
    have h := ncard_le_ncard_image_mul_ncard cj Stab Set.univ (fun k _ k' _ hkk' => by
      show cj (k⁻¹ * k') = Ω
      rw [hcj_mul, ← hkk', ← hcj_mul, inv_mul_cancel, hcj1])
    rw [Set.ncard_univ] at h
    have hCeq : cj '' Set.univ = C := by
      ext Ω'
      constructor
      · rintro ⟨h, -, rfl⟩
        exact ⟨h, h.2, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨⟨h, hh⟩, trivial, rfl⟩
    rwa [hCeq] at h
  have hkey : ∀ h ∈ Stab, ∀ x ∈ U, ρ h • x ∈ U ∧ Q (ρ h • x) = Q x := by
    intro h hh
    have hh' : cj h = Ω := hh
    refine hU.mapsTo_of_conj hσ hlam hlam0 hlam1 hscal (ρ h) fun v hv hQv => ?_
    obtain ⟨x, hxΩ, hx⟩ := (hρΩ (suTv hσ v 1)).mpr ⟨v, hv, hQv, rfl⟩
    have hmem : ((h * x * h⁻¹ : H) : G) ∈ Ω := by
      have h1 : ((h * x * h⁻¹ : H) : G) ∈ cj h := ⟨x, hxΩ, rfl⟩
      rwa [hh'] at h1
    obtain ⟨a, ha, hQa, heq⟩ := (hρΩ (ρ (h * x * h⁻¹))).mp ⟨_, hmem, rfl⟩
    refine ⟨a, ha, hQa, ?_⟩
    rw [← hx, ← heq, map_mul, map_mul, map_inv]
  have hStab_inv : ∀ h ∈ Stab, h⁻¹ ∈ Stab := by
    intro h hh
    have hh' : cj h = Ω := hh
    show cj h⁻¹ = Ω
    calc cj h⁻¹ = (fun x => ((h⁻¹ : H) : G) * x * ((h⁻¹ : H) : G)⁻¹) '' Ω := rfl
      _ = (fun x => ((h⁻¹ : H) : G) * x * ((h⁻¹ : H) : G)⁻¹) '' cj h := by rw [hh']
      _ = cj (h⁻¹ * h) := (hcj_mul _ _).symm
      _ = Ω := by rw [inv_mul_cancel, hcj1]
  have hsub : ρ '' Stab ⊆ (X : Set (SUid (unitaryInvolution F 2 f) 4)) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [SetLike.mem_coe, hXdef, mem_fixedQuadSubgroup]
    refine ⟨fun x => ⟨fun hx => ?_, fun hx => (hkey h hh x hx).1⟩,
      fun x hx => (hkey h hh x hx).2⟩
    have h2 := (hkey h⁻¹ (hStab_inv h hh) _ hx).1
    rwa [map_inv, inv_smul_smul] at h2
  have hC2 : Stab.ncard ≤ Nat.card X * Nat.card ρ.ker := by
    have h := ncard_le_ncard_image_mul_ncard ρ (ρ.ker : Set H) Stab (fun k _ k' _ hkk' => by
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hkk', inv_mul_cancel])
    calc Stab.ncard ≤ (ρ '' Stab).ncard * (ρ.ker : Set H).ncard := h
      _ ≤ (X : Set (SUid (unitaryInvolution F 2 f) 4)).ncard * (ρ.ker : Set H).ncard :=
        Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub (Set.toFinite _))
      _ = Nat.card X * Nat.card ρ.ker := by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        rfl
  obtain ⟨v₀, hv₀, hQv₀⟩ : ∃ v ∈ U, Q v = 1 := by
    obtain ⟨b, hbU, hdet, -⟩ := hU.exists_basis
    have hb0 : b 0 ≠ 0 := fun h0 => hdet (Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by
      simp [h0])
    exact hU.exists_Q_eq_one (hbU 0) hb0
  have hC3 : Nat.card X ≤ Vset.ncard * (2 * (2 ^ f * ((2 ^ f) ^ 2 - 1))) := by
    have h := ncard_le_ncard_image_mul_ncard
      (fun g : X => (g : SUid (unitaryInvolution F 2 f) 4) • v₀)
      {g : X | (g : SUid (unitaryInvolution F 2 f) 4) • v₀ = v₀} Set.univ (fun k _ k' _ hkk' => by
        show ((k⁻¹ * k' : X) : SUid (unitaryInvolution F 2 f) 4) • v₀ = v₀
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← hkk', inv_smul_smul])
    rw [Set.ncard_univ] at h
    have himg : (fun g : X => (g : SUid (unitaryInvolution F 2 f) 4) • v₀) '' Set.univ ⊆ Vset := by
      rintro _ ⟨g, -, rfl⟩
      have hg := (mem_fixedQuadSubgroup (σ := unitaryInvolution F 2 f)).mp
        (show (g : SUid (unitaryInvolution F 2 f) 4) ∈
          fixedQuadSubgroup (unitaryInvolution F 2 f) U Q from g.2)
      exact ⟨(hg.1 v₀).mpr hv₀, by rw [hg.2 v₀ hv₀, hQv₀]⟩
    have hstab := hU.natCard_stabilizer_le hσ hq hv₀ hQv₀
    calc Nat.card X ≤ _ := h
      _ ≤ Vset.ncard * (2 * (2 ^ f * ((2 ^ f) ^ 2 - 1))) := by
        apply Nat.mul_le_mul (Set.ncard_le_ncard himg (Set.toFinite _))
        rw [← Nat.card_coe_set_eq]
        exact hstab
  have hC4 : Vset.ncard ≤ Ω.ncard := by
    have hmaps : Set.MapsTo (fun v => suTv hσ v 1) Vset (ρ '' {x : H | (x : G) ∈ Ω}) := by
      rintro v ⟨hv, hQv⟩
      obtain ⟨x, hx, hxv⟩ := (hρΩ (suTv hσ v 1)).mpr ⟨v, hv, hQv, rfl⟩
      exact ⟨x, hx, hxv⟩
    calc Vset.ncard ≤ (ρ '' {x : H | (x : G) ∈ Ω}).ncard :=
          Set.ncard_le_ncard_of_injOn _ hmaps (hU.suTv_injOn hσ) (Set.toFinite _)
      _ ≤ {x : H | (x : G) ∈ Ω}.ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ Ω.ncard := by
        rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
        exact Set.ncard_le_ncard (fun _ ⟨x, hx, e⟩ => e ▸ hx) (Set.toFinite _)
  have hC5 : Nat.card H = Nat.card (SUid (unitaryInvolution F 2 f) 4) * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv]
  have hk : 0 < Nat.card ρ.ker := Nat.card_pos
  have hmain : Nat.card (SUid (unitaryInvolution F 2 f) 4) * Nat.card ρ.ker ≤
      (2 * (2 ^ f * ((2 ^ f) ^ 2 - 1)) * (C.ncard * Ω.ncard)) * Nat.card ρ.ker := by
    rw [← hC5]
    calc Nat.card H ≤ C.ncard * Stab.ncard := hC1
      _ ≤ C.ncard * (Nat.card X * Nat.card ρ.ker) := Nat.mul_le_mul_left _ hC2
      _ ≤ C.ncard * ((Vset.ncard * (2 * (2 ^ f * ((2 ^ f) ^ 2 - 1)))) * Nat.card ρ.ker) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hC3)
      _ ≤ C.ncard * ((Ω.ncard * (2 * (2 ^ f * ((2 ^ f) ^ 2 - 1)))) * Nat.card ρ.ker) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC4))
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmain hk

end UFour


theorem ncard_le_ncard_mul_of_fibres {α β : Type} [Finite α] [Finite β] (P : Set (α × β))
    (S : Set α) (c : ℕ) (hPS : ∀ p ∈ P, p.1 ∈ S) (hfib : ∀ x ∈ S, {z | (x, z) ∈ P}.ncard ≤ c) :
    P.ncard ≤ S.ncard * c := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [Set.ncard_eq_toFinset_card' P, Set.ncard_eq_toFinset_card' S, mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst) (fun p hp => ?_) c
    (fun x hx => ?_)
  · rw [Set.mem_toFinset] at hp ⊢
    exact hPS p hp
  · rw [Set.mem_toFinset] at hx
    calc (P.toFinset.filter fun p => p.1 = x).card ≤ {z | (x, z) ∈ P}.toFinset.card := by
          refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp p' hp' h => ?_)
          · rw [Finset.mem_coe, Finset.mem_filter, Set.mem_toFinset] at hp
            rw [Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf_eq, ← hp.2]
            exact hp.1
          · rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
            exact Prod.ext (hp.2.trans hp'.2.symm) h
      _ = {z | (x, z) ∈ P}.ncard := (Set.ncard_eq_toFinset_card' _).symm
      _ ≤ c := hfib x hx

section PairCount

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ncard_not_commute_eq {u x : G} (hu : u ∈ D) (hx : x ∈ commSet D u)
    (hk : (commSet D x).ncard = (commSet D u).ncard) :
    {z | z ∈ D ∧ ¬ Commute z u ∧ Commute x z}.ncard =
      {y | y ∈ commSet D u ∧ ¬ Commute y x}.ncard := by
  set A := {z | z ∈ D ∧ ¬ Commute z u ∧ Commute x z} with hAdef
  set B := {y | y ∈ commSet D u ∧ ¬ Commute y x} with hBdef
  set I := commSet D x ∩ commSet D u with hIdef
  have hxu : Commute x u := hx.2.1
  have hxne : x ≠ u := hx.2.2
  have hA : commSet D x = A ∪ insert u I := by
    ext z
    constructor
    · rintro ⟨hzD, hzx, hzne⟩
      by_cases hzu : Commute z u
      · by_cases hzu' : z = u
        · exact Or.inr (Or.inl hzu')
        · exact Or.inr (Or.inr ⟨⟨hzD, hzx, hzne⟩, ⟨hzD, hzu, hzu'⟩⟩)
      · exact Or.inl ⟨hzD, hzu, hzx.symm⟩
    · rintro (⟨hzD, hzu, hxz⟩ | rfl | ⟨hz, -⟩)
      · exact ⟨hzD, hxz.symm, fun h => hzu (by rw [h]; exact hxu)⟩
      · exact ⟨hu, hxu.symm, hxne.symm⟩
      · exact hz
  have hB : commSet D u = B ∪ insert x I := by
    ext y
    constructor
    · rintro ⟨hyD, hyu, hyne⟩
      by_cases hyx : Commute y x
      · by_cases hyx' : y = x
        · exact Or.inr (Or.inl hyx')
        · exact Or.inr (Or.inr ⟨⟨hyD, hyx, hyx'⟩, ⟨hyD, hyu, hyne⟩⟩)
      · exact Or.inl ⟨⟨hyD, hyu, hyne⟩, hyx⟩
    · rintro (⟨hy, -⟩ | rfl | ⟨-, hy⟩)
      · exact hy
      · exact hx
      · exact hy
  have huI : u ∉ I := fun h => h.2.2.2 rfl
  have hxI : x ∉ I := fun h => h.1.2.2 rfl
  have hdA : Disjoint A (insert u I) := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hzu, -⟩ (rfl | ⟨-, hz⟩)
    · exact hzu (Commute.refl _)
    · exact hzu hz.2.1
  have hdB : Disjoint B (insert x I) := by
    rw [Set.disjoint_left]
    rintro y ⟨-, hyx⟩ (rfl | ⟨hy, -⟩)
    · exact hyx (Commute.refl _)
    · exact hyx hy.2.1
  rw [hA, hB, Set.ncard_union_eq hdA, Set.ncard_union_eq hdB, Set.ncard_insert_of_notMem huI,
    Set.ncard_insert_of_notMem hxI] at hk
  omega

omit [Finite G] in
theorem ncard_commSet_conj (hN : IsNormalSet D) (g u : G) :
    (commSet D (g * u * g⁻¹)).ncard = (commSet D u).ncard := by
  have h : commSet D (g * u * g⁻¹) = (fun x => g * x * g⁻¹) '' commSet D u := by
    ext y
    constructor
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by group⟩
      have h1 := conj_mem_commSet hN g⁻¹ hy
      have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
      rwa [e, inv_inv] at h1
    · rintro ⟨x, hx, rfl⟩
      exact conj_mem_commSet hN g hx
  rw [h, Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)]

theorem ncard_commSet_of_isUnitaryTransvection_four (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {f : ℕ}
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s)
    {x : G} (hx : x ∈ commSet D hC.d) :
    (commSet D hC.d).ncard = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) * ((2 ^ f) ^ 3 + 1) ∧
      {y | y ∈ commSet D hC.d ∧ ¬ Commute y x}.ncard = (2 ^ f - 1) * (2 ^ f) ^ 5 := by
  classical
  set π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) with hπ
  have hstar := DalphaStar_eq_commSet_of_alpha_eq hC hα
  have hZ := center_Hbar_eq_bot hC
  have hcls := imageClass_isClass hC
  obtain ⟨-, hne⟩ := subset_rootBlock_and_ne_of_isUnitaryTransvection hcls hZ hs le_rfl hU
  have hinj : Set.InjOn π (DstarH hC) := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  obtain ⟨hE, hEnc⟩ := ncard_of_isUnitaryTransvection_four hcls hZ hs hU
  have hmemH : ∀ {y : G}, y ∈ commSet D hC.d → y ∈ Halpha D hC.alpha := fun hy =>
    Subgroup.subset_closure (by rw [hstar]; exact hy)
  have hmemD : ∀ {y : Halpha D hC.alpha}, (y : G) ∈ commSet D hC.d → y ∈ DstarH hC :=
    fun hy => by
      show _ ∈ DalphaStar D hC.alpha
      rw [hstar]
      exact hy
  have hval : Subtype.val '' DstarH hC = commSet D hC.d := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hstar]
      exact hy
    · intro hy
      exact ⟨⟨y, hmemH hy⟩, hmemD hy, rfl⟩
  set x' : Halpha D hC.alpha := ⟨x, hmemH hx⟩ with hx'def
  have hx' : x' ∈ DstarH hC := hmemD hx
  refine ⟨?_, ?_⟩
  · rw [← hval, Set.ncard_image_of_injective _ Subtype.val_injective,
      ← hinj.ncard_image]
    exact hE
  set B' : Set (Halpha D hC.alpha) := {y | y ∈ DstarH hC ∧ ¬ Commute y x'} with hB'
  have hvalB : Subtype.val '' B' = {y | y ∈ commSet D hC.d ∧ ¬ Commute y x} := by
    ext y
    constructor
    · rintro ⟨y, ⟨hy, hyx⟩, rfl⟩
      refine ⟨?_, fun h => hyx (Subtype.ext h)⟩
      rw [← hstar]
      exact hy
    · rintro ⟨hy, hyx⟩
      exact ⟨⟨y, hmemH hy⟩, ⟨hmemD hy, fun h => hyx (congrArg Subtype.val h)⟩, rfl⟩
  have hπB : π '' B' = {t | t ∈ imageClass hC ∧ ¬ Commute t (π x')} := by
    ext t
    constructor
    · rintro ⟨y, ⟨hy, hyx⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, fun h => hyx (commute_of_commute_mk_of_le_center hC hMZ hy hx' h)⟩
    · rintro ⟨⟨y, hy, rfl⟩, hyx⟩
      exact ⟨y, ⟨hy, fun h => hyx (h.map π)⟩, rfl⟩
  obtain ⟨d₀, hd₀⟩ := hcls
  have hsx : IsConj s (π x') := by
    have h1 : IsConj d₀ s := by
      rw [hd₀] at hs
      exact hs
    have h2 : π x' ∈ imageClass hC := ⟨x', hx', rfl⟩
    rw [hd₀] at h2
    exact h1.symm.trans h2
  obtain ⟨c, hc⟩ := isConj_iff.mp hsx
  have hconj : {t | t ∈ imageClass hC ∧ ¬ Commute t (π x')} =
      (fun t => c * t * c⁻¹) '' {t | t ∈ imageClass hC ∧ ¬ Commute t s} := by
    rw [← hc]
    ext t
    constructor
    · rintro ⟨ht, htc⟩
      refine ⟨c⁻¹ * t * c, ⟨?_, fun h => htc ?_⟩, by group⟩
      · simpa using imageClass_isNormalSet hC c⁻¹ t ht
      · have h1 := (Commute.conj_iff c).2 h
        rwa [show c * (c⁻¹ * t * c) * c⁻¹ = t by group] at h1
    · rintro ⟨t, ⟨ht, hts⟩, rfl⟩
      exact ⟨imageClass_isNormalSet hC c t ht, fun h => hts ((Commute.conj_iff c).1 h)⟩
  rw [← hvalB, Set.ncard_image_of_injective _ Subtype.val_injective,
    ← (hinj.mono fun y hy => hy.1).ncard_image, hπB, hconj,
    Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)]
  exact hEnc

theorem ncard_pairs_le_of_isUnitaryTransvection_four (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {f : ℕ}
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) :
    {p : G × G | p.1 ∈ commSet D hC.d ∧ p.2 ∈ D ∧ ¬ Commute p.2 hC.d ∧ Commute p.1 p.2}.ncard ≤
      (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f - 1) * (2 ^ f) ^ 5) := by
  obtain ⟨x₀, hx₀⟩ : (commSet D hC.d).Nonempty := by
    obtain ⟨y, hy⟩ := DstarH_nonempty hC
    refine ⟨y, ?_⟩
    rw [← DalphaStar_eq_commSet_of_alpha_eq hC hα]
    exact hy
  rw [← (ncard_commSet_of_isUnitaryTransvection_four hC hMZ hα hs hU hx₀).1]
  refine ncard_le_ncard_mul_of_fibres _ _ _ (fun p hp => hp.1) fun x hx => le_of_eq ?_
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx.1)
  have hk : (commSet D x).ncard = (commSet D hC.d).ncard := by
    rw [← hg]
    exact ncard_commSet_conj hC.setup.normal g hC.d
  rw [← (ncard_commSet_of_isUnitaryTransvection_four hC hMZ hα hs hU hx).2,
    ← ncard_not_commute_eq hC.hd hx hk]
  congr 1
  ext z
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

theorem false_of_twelveEight_counts {q N : ℕ} (hq : 2 ≤ q)
    (h1 : q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) ≤ 2 * (q * (q ^ 2 - 1)) * N)
    (h2 : 2 * N ≤ (q - 1) * (q ^ 2 + 1) * (q ^ 3 + 1) * ((q - 1) * q ^ 5)) : False := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (r + 1) ^ 4 - 1 = r * (r + 2) * ((r + 1) ^ 2 + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : r + 1 - 1 = r := by omega
  rw [e1, e2] at h1
  rw [e3] at h2
  set R := (r + 1) * (r * (r + 2)) * (r * ((r + 1) ^ 2 + 1) * ((r + 1) ^ 3 + 1) * (r * (r + 1) ^ 5))
    with hR
  have h3 : (r + 1) ^ 6 * (r * (r + 2)) * ((r + 1) ^ 3 + 1) * (r * (r + 2) * ((r + 1) ^ 2 + 1)) ≤
      R := by
    refine h1.trans ?_
    calc 2 * ((r + 1) * (r * (r + 2))) * N = (r + 1) * (r * (r + 2)) * (2 * N) := by ring
      _ ≤ R := Nat.mul_le_mul_left _ h2
  have key : (r + 1) ^ 6 * (r * (r + 2)) * ((r + 1) ^ 3 + 1) * (r * (r + 2) * ((r + 1) ^ 2 + 1)) *
      r = R * (r + 2) := by
    rw [hR]
    ring
  have hRpos : 0 < R := by positivity
  have h4 : R * (r + 2) ≤ R * r := by
    rw [← key]
    exact Nat.mul_le_mul_right r h3
  have := Nat.le_of_mul_le_mul_left h4 hRpos
  omega

theorem twelveEight_of_marked (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {f : ℕ} (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s)
    {w d' : G} (hw : w ∈ D) (hwu : ¬ Commute w hC.d)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (ρ : Halpha D hC.alpha →* SUid (unitaryInvolution F 2 f) 4) (hρ : Function.Surjective ρ)
    {U : AddSubgroup (Fin 4 → F)} {Q : (Fin 4 → F) → F}
    (hUQ : IsFixedQuadForm (unitaryInvolution F 2 f) U Q)
    (hρΩ : ∀ g, (∃ x : Halpha D hC.alpha, (x : G) ∈ compSet D hC.d w d' ∧ ρ x = g) ↔
      ∃ a ∈ U, Q a = 1 ∧ g = suTv (isUnitaryInvolution_unitaryInvolution hF) a 1) :
    False := by
  have hN : IsNormalSet D := hC.setup.normal
  have hH : ∀ h ∈ Halpha D hC.alpha, Commute h hC.d := fun h hh =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Halpha_le_centralizer_of_mem_alpha hC (by rw [hα]; rfl) hh))
  have hedge := two_mul_ncard_mul_ncard_le (d := d') hN hw hwu (Halpha D hC.alpha) hH
  have hbound := natCard_SUid_le_of_marked hF hf (Halpha D hC.alpha) ρ hρ hUQ hρΩ
  rw [natCard_SUid_four hF (by omega)] at hbound
  have hpairs := ncard_pairs_le_of_isUnitaryTransvection_four hC hMZ hα hs hU
  exact false_of_twelveEight_counts (q := 2 ^ f)
    (by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ f); simpa using this)
    hbound (hedge.trans hpairs)

theorem kFactsSuProj_injective_four {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : Function.Injective (kFactsSuProj hF 4) := by
  intro g g' h
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF g g').mp h
  have hg : (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det = 1 := g.2.1
  have hg' : (((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det = 1 := g'.2.1
  have h4 : (u : F) ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hg, hg',
      one_mul] at h1
    exact h1.symm
  have h2 : (u : F) ^ 2 = 1 := frobenius_inj F 2 (by
    rw [frobenius_def, frobenius_def, ← pow_mul, one_pow]; exact h4)
  have h1 : (u : F) = 1 := frobenius_inj F 2 (by rw [frobenius_def, frobenius_def, h2, one_pow])
  apply Subtype.ext
  apply Units.ext
  rw [hu, h1, one_smul, Matrix.mul_one]

@[expose] def IsMarkedComponentU (hC : HypothesisC D) (f : ℕ) (Ω : Set G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (hF : Nat.card F = (2 ^ f) ^ 2)
    (e : ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ⧸
        Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) ≃*
      StatedProj (StatedSU 4 (2 ^ f) F))
    (U : AddSubgroup (Fin 4 → F)) (Q : (Fin 4 → F) → F),
    IsFixedQuadForm (unitaryInvolution F 2 f) U Q ∧
      (fun x : Halpha D hC.alpha => e (QuotientGroup.mk (QuotientGroup.mk x))) ''
          {x | (x : G) ∈ Ω} =
        {y | ∃ a ∈ U, Q a = 1 ∧ y = kFactsSuProjTv hF 4 a 1}

theorem twelveEight (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {f : ℕ} (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s)
    {w d' : G} (hw : w ∈ D) (hwu : ¬ Commute w hC.d)
    (hmark : IsMarkedComponentU hC f (compSet D hC.d w d')) : False := by
  obtain ⟨F, _, _, _, hF, e, U, Q, hUQ, himg⟩ := hmark
  set π := MulEquiv.ofBijective (kFactsSuProj hF 4)
    ⟨kFactsSuProj_injective_four hF, kFacts_suProj_surjective hF 4⟩ with hπ
  set ρ : Halpha D hC.alpha →* SUid (unitaryInvolution F 2 f) 4 :=
    π.symm.toMonoidHom.comp (e.toMonoidHom.comp
      ((QuotientGroup.mk' _).comp (QuotientGroup.mk' _))) with hρdef
  have hρ : Function.Surjective ρ :=
    π.symm.surjective.comp (e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)))
  refine twelveEight_of_marked (d' := d') hC hMZ hα hs hf hU hw hwu hF ρ hρ hUQ fun g => ?_
  have key : ∀ x : Halpha D hC.alpha, ρ x = g ↔
      e (QuotientGroup.mk (QuotientGroup.mk x)) = kFactsSuProj hF 4 g := by
    intro x
    show π.symm (e (QuotientGroup.mk (QuotientGroup.mk x))) = g ↔ _
    rw [MulEquiv.symm_apply_eq]
    rfl
  have himg' := Set.ext_iff.mp himg
  constructor
  · rintro ⟨x, hx, hxg⟩
    obtain ⟨a, ha, hQa, hea⟩ :=
      (himg' (e (QuotientGroup.mk (QuotientGroup.mk x)))).mp ⟨x, hx, rfl⟩
    refine ⟨a, ha, hQa, kFactsSuProj_injective_four hF ?_⟩
    rw [← (key x).mp hxg, hea]
    rfl
  · rintro ⟨a, ha, hQa, rfl⟩
    obtain ⟨x, hx, hex⟩ := (himg' (kFactsSuProjTv hF 4 a 1)).mpr ⟨a, ha, hQa, rfl⟩
    exact ⟨x, hx, (key x).mpr hex⟩

end PairCount

end CFSG.OddTranspositions.PartThree

end
