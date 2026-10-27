module

public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofOrbit
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.KFacts.KP2
open Equiv

namespace Step163Alt

variable {G : Type} [Group G] [Finite G]

theorem omega_transitive_of_ten {A Y : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAY : A ≤ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) (hΩ3 : (omegaA A).ncard = 3) :
    ∀ F ∈ omegaA A, ∀ F' ∈ omegaA A, ∃ y ∈ Y ⊓ Subgroup.normalizer (A : Set G),
      F' = F.map (MulAut.conj y).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set κ : ↥Y →* Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp (φ.toMonoidHom.comp π) with hκ
  have hκker : ∀ y : ↥Y, κ y = 1 → y ∈ N := by
    intro y hy
    have h1 : φ (π y) = 1 := Subtype.ext (by simpa [hκ] using hy)
    rw [← map_one φ] at h1
    have h2 : π y = 1 := φ.injective h1
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hker2 : IsPGroup 2 κ.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨y, hκker y hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hκrange : ∀ σ ∈ alternatingGroup (Fin 10), σ ∈ κ.range := by
    intro σ hσ
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (φ.symm ⟨σ, hσ⟩)
    refine ⟨y, ?_⟩
    change ((φ (π y) : alternatingGroup (Fin 10)) : Perm (Fin 10)) = σ
    rw [show π y = φ.symm ⟨σ, hσ⟩ from hy, MulEquiv.apply_symm_apply]
  set A' := A.subgroupOf Y with hA'
  have hAmap : A'.map Y.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAY]
  have hA'el : CFSG.Assembly.IsElemAbelian 3 A' :=
    Step163Alt.isElemAbelian_of_map_hom Y.subtype
      (fun b _ hb => Y.subtype_injective (by rw [hb, map_one]))
      (by rw [hAmap]; exact hA)
  have hA'3 : IsPGroup 3 A' := fun b => ⟨1, Subtype.ext (by simpa using hA'el.2 b b.2)⟩
  have hinj : ∀ b ∈ A', κ b = 1 → b = 1 := by
    intro b hb hb1
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨b, hκker b hb1⟩
    have h2 : b ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact Step163Alt.eq_one_of_two_three h2 (by rw [pow_one]; exact hA'el.2 b hb)
  set E := A'.map κ with hE
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := Step163Alt.isElemAbelian_map_hom κ hA'el
  have hEcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hE27 : Nat.card E = 27 := by
    set κ' : ↥A' →* Perm (Fin 10) := κ.comp A'.subtype with hκ'
    have hκ'inj : Function.Injective κ' := by
      intro a b hab
      have hab' : κ a = κ b := hab
      have := hinj _ (A'.mul_mem a.2 (A'.inv_mem b.2))
        (by rw [map_mul, map_inv, hab', mul_inv_cancel])
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have hrange : κ'.range = E := by
      rw [hκ', MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Nat.card_congr (MonoidHom.ofInjective hκ'inj).toEquiv
    rw [hrange] at h1
    rw [← h1, hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hA27]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.K412.exists_conj_eq_eTwentySeven hE27 hEcomm
  have hmemE : ∀ z : Perm (Fin 10), z ∈ E ↔ g * z * g⁻¹ ∈ eTwentySeven := by
    intro z
    rw [← hg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      show g⁻¹ * (g * z * g⁻¹) * g = z by group]
  have key : ∀ h ∈ normAlt, ∃ y : ↥Y, y ∈ Subgroup.normalizer (A' : Set ↥Y) ∧
      ∀ b ∈ A', κ (y * b * y⁻¹) = (g⁻¹ * h * g) * κ b * (g⁻¹ * h * g)⁻¹ := by
    intro h hh
    have hhA : g⁻¹ * h * g ∈ alternatingGroup (Fin 10) := by
      have := (alternatingGroup.normal (α := Fin 10)).conj_mem h (Subgroup.mem_inf.mp hh).2 g⁻¹
      rwa [inv_inv] at this
    have hhN : g⁻¹ * h * g ∈ Subgroup.normalizer ((E : Subgroup (Perm (Fin 10))) :
        Set (Perm (Fin 10))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [hmemE, hmemE,
        show g * (g⁻¹ * h * g * z * (g⁻¹ * h * g)⁻¹) * g⁻¹ = h * (g * z * g⁻¹) * h⁻¹ by group]
      exact Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hh).1 _
    exact Step163Alt.exists_normalizer_lift κ hker2 hA'3 hEcomm (hκrange _ hhA) hhN
  choose! yf hyN hyκ using key
  have hyNG : ∀ h ∈ normAlt, (yf h : G) ∈ Subgroup.normalizer (A : Set G) := by
    intro h hh
    have := Subgroup.le_normalizer_map Y.subtype ⟨yf h, hyN h hh, rfl⟩
    rwa [hAmap] at this
  obtain ⟨F₀, hF₀⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hΩ3]; norm_num :
    (omegaA A).ncard ≠ 0)
  obtain ⟨hF₀A, hF₀3, a₀, hF₀a, -⟩ := id hF₀
  have ha₀A : a₀ ∈ A := hF₀A (hF₀a ▸ Subgroup.mem_zpowers a₀)
  set a₀' : ↥Y := ⟨a₀, hAY ha₀A⟩ with ha₀'
  have ha₀'A' : a₀' ∈ A' := ha₀A
  have ha₀1 : a₀' ≠ 1 := by
    intro h1
    have h1' : a₀ = 1 := congrArg Subtype.val h1
    rw [hF₀a, h1', Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hF₀3
    omega
  set x := g * κ a₀' * g⁻¹ with hx
  have hxE : x ∈ eTwentySeven := (hmemE _).mp ⟨a₀', ha₀'A', rfl⟩
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hx, conj_eq_one_iff] at h1
    exact ha₀1 (hinj _ ha₀'A' h1)
  set Fh : Perm (Fin 10) → Subgroup G :=
    fun h => Subgroup.zpowers ((yf h : G) * a₀ * (yf h : G)⁻¹) with hFh
  have hFh_mem : ∀ h ∈ normAlt, Fh h ∈ omegaA A := by
    intro h hh
    have h1 := (map_conj_mem_omegaA_iff (hyNG h hh)).mpr hF₀
    rw [hF₀a, MonoidHom.map_zpowers] at h1
    exact h1
  have himg : ∀ h ∈ normAlt, g * κ (yf h * a₀' * (yf h)⁻¹) * g⁻¹ = h * x * h⁻¹ := by
    intro h hh
    rw [hyκ h hh a₀' ha₀'A', hx]
    group
  have hdist : ∀ h₁ ∈ normAlt, ∀ h₂ ∈ normAlt, h₂ * x * h₂⁻¹ ≠ h₁ * x * h₁⁻¹ →
      h₂ * x * h₂⁻¹ ≠ (h₁ * x * h₁⁻¹)⁻¹ → Fh h₁ ≠ Fh h₂ := by
    intro h₁ hh₁ h₂ hh₂ hne hne' heq
    have hmem : (yf h₂ : G) * a₀ * (yf h₂ : G)⁻¹ ∈ Fh h₁ := heq ▸ Subgroup.mem_zpowers _
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have ht' : (yf h₁ * a₀' * (yf h₁)⁻¹) ^ t = yf h₂ * a₀' * (yf h₂)⁻¹ :=
      Subtype.ext (by simpa using ht)
    have hu3 : (h₁ * x * h₁⁻¹) ^ 3 = 1 := by
      obtain ⟨i, j, k, hijk⟩ := hxE
      rw [conj_pow, hijk, eTwentySevenF_pow_three, mul_one, mul_inv_cancel]
    have hv1 : h₂ * x * h₂⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
    refine Step163Alt.not_mem_zpowers_of_ne hu3 hv1 hne hne'
      (Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩)
    rw [← himg h₁ hh₁, ← himg h₂ hh₂, conj_zpow, ← map_zpow, ht']
  obtain ⟨i, j, k, hxijk⟩ := hxE
  by_cases hax : ∃ a : Fin 6, eTwentySevenF i j k = axisElt a
  ·
    obtain ⟨a, ha⟩ := hax
    set hs : Fin 3 → Perm (Fin 10) := fun n => wCycle ^ (n : ℕ) with hhs
    have hsmem : ∀ n, hs n ∈ normAlt := fun n => pow_mem wCycle_mem_normAlt _
    set Fm : Fin 3 → Subgroup G := fun n => Fh (hs n) with hFm
    have hFinj : Function.Injective Fm := by
      intro m n hmn
      by_contra hne
      obtain ⟨h1, h2⟩ := Step163Alt.axis_conj_distinct a m n hne
      rw [← ha, ← hxijk] at h1 h2
      exact hdist _ (hsmem m) _ (hsmem n) h1 h2 hmn
    have hsub : Set.range Fm ⊆ omegaA A := by
      rintro _ ⟨n, rfl⟩
      exact hFh_mem _ (hsmem n)
    have hcard : (Set.range Fm).ncard = 3 := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hFinj, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have heq : Set.range Fm = omegaA A :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hΩ3, hcard]) (Set.toFinite _)
    intro F hF F' hF'
    rw [← heq] at hF hF'
    obtain ⟨m, rfl⟩ := hF
    obtain ⟨n, rfl⟩ := hF'
    refine ⟨(yf (hs n) : G) * (yf (hs m) : G)⁻¹,
      Subgroup.mem_inf.mpr ⟨Y.mul_mem (yf (hs n)).2 (Y.inv_mem (yf (hs m)).2),
        mul_mem (hyNG _ (hsmem n)) (inv_mem (hyNG _ (hsmem m)))⟩, ?_⟩
    simp only [hFm, hFh, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    congr 1
    group
  ·
    exfalso
    have hx1' : eTwentySevenF i j k ≠ 1 := hxijk ▸ hx1
    set Fm : Fin 4 → Subgroup G :=
      fun m => Fh (monoRep (Step163Alt.orbitTab i j k m).1 (Step163Alt.orbitTab i j k m).2)
      with hFm
    have hFinj : Function.Injective Fm := by
      intro m n hmn
      by_contra hne
      obtain ⟨h1, h2⟩ := Step163Alt.orbitTab_distinct i j k hx1' hax m n hne
      rw [← hxijk] at h1 h2
      exact hdist _ (Step163Alt.orbitTab_mem i j k m) _ (Step163Alt.orbitTab_mem i j k n) h1 h2
        hmn
    have hsub : Set.range Fm ⊆ omegaA A := by
      rintro _ ⟨n, rfl⟩
      exact hFh_mem _ (Step163Alt.orbitTab_mem i j k n)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hFinj, Nat.card_eq_fintype_card,
      Fintype.card_fin, hΩ3] at hle
    omega

end Step163Alt

theorem step163A10_of : Step163A10 := by
  intro G _ _ A c L h _ _ _ hT Y hY _ hY10 F hF F' hF'
  obtain ⟨φ⟩ := hY10
  have hD := h.toSec13Data
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      B = E := fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hAleY : A ≤ Y := Step163Alt.le_of_alternating_ten hmax hD.isElemAbelian hAY hO φ
  exact Step163Alt.omega_transitive_of_ten hD.isElemAbelian hD.card_eq hAleY φ hT.1 F hF F' hF'

end CFSG.RankThree.PartTwo.Sec16
