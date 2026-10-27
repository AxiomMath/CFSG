module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Vol2.Ch11SecBNPSec

public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G]

theorem commutator_le_self (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

structure SemiFam (𝒟 : Set (Subgroup G)) : Prop where
  simple : ∀ D ∈ 𝒟, IsSimpleGroup ↥D
  nonabelian : ∀ D ∈ 𝒟, ∃ a b : ↥D, a * b ≠ b * a
  comm : ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, D ≠ D' → ∀ x ∈ D, ∀ y ∈ D', x * y = y * x

namespace SemiFam

variable {𝒟 : Set (Subgroup G)} {D : Subgroup G}

theorem le_normalizer (h : SemiFam 𝒟) (hD : D ∈ 𝒟) :
    sSup 𝒟 ≤ Subgroup.normalizer (D : Set G) := by
  refine sSup_le fun D' hD' => ?_
  by_cases hDD : D' = D
  · rw [hDD]
    exact Subgroup.le_normalizer
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc : ∀ z ∈ D, y * z * y⁻¹ = z := fun z hz => by
      rw [h.comm D' hD' D hD hDD y hy z hz, mul_inv_cancel_right]
    constructor
    · intro hx
      rw [hc x hx]
      exact hx
    · intro hx
      have h2 := h.comm D' hD' D hD hDD y hy _ hx
      have h3 : x = y * x * y⁻¹ := by
        calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h2]
          _ = y * x * y⁻¹ := by group
      rw [h3]
      exact hx

theorem normal (h : SemiFam 𝒟) (hD : D ∈ 𝒟) : (D.subgroupOf (sSup 𝒟)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sSup hD)).mpr (h.le_normalizer hD)

theorem pairwise (h : SemiFam 𝒟) :
    Pairwise fun i j : ↥𝒟 => ∀ x y : G, x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) →
      Commute x y :=
  fun i j hij x y hx hy => h.comm i i.2 j j.2 (fun e => hij (Subtype.ext e)) x hx y hy

theorem iSupIndep (h : SemiFam 𝒟) : _root_.iSupIndep fun i : ↥𝒟 => (i : Subgroup G) := by
  intro i
  set D := (i : Subgroup G)
  set N := ⨆ (j : ↥𝒟) (_ : j ≠ i), (j : Subgroup G)
  have hND : N ≤ Subgroup.centralizer (D : Set G) := iSup₂_le fun j hj y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h.comm i i.2 j j.2 (fun e => hj (Subtype.ext e.symm)) x hx y hy
  have := h.simple D i.2
  have hn : ((D ⊓ N).subgroupOf D).Normal := by
    refine ⟨fun k hk s => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨(s * k * s⁻¹).2, ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hND hk.2) (s : G) s.2
    have : ((s * k * s⁻¹ : ↥D) : G) = k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc, mul_inv_cancel_right]
    rw [this]
    exact hk.2
  rw [disjoint_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D ⊓ N).subgroupOf D) with h1 | h1
  · rw [Subgroup.subgroupOf_eq_bot] at h1
    exact le_bot_iff.mp fun x hx => (Subgroup.disjoint_def.mp h1) hx hx.1
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h1
    obtain ⟨a, b, hab⟩ := h.nonabelian D i.2
    apply hab
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (hND (h1 b.2).2) (a : G) a.2
    simpa using this

section Finite

variable [Finite G]

omit [Finite G] in
theorem card_eq (h : SemiFam 𝒟) [Fintype ↥𝒟] :
    Nat.card ↥(sSup 𝒟) = ∏ i : ↥𝒟, Nat.card ↥(i : Subgroup G) := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := h.pairwise) h.iSupIndep
  have hr : (Subgroup.noncommPiCoprod h.pairwise).range = sSup 𝒟 := by
    rw [Subgroup.noncommPiCoprod_range, sSup_eq_iSup']
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]

omit [Finite G] in
theorem exists_proj (h : SemiFam 𝒟) [Fintype ↥𝒟] :
    ∃ π : (i : ↥𝒟) → ↥(sSup 𝒟) →* ↥(i : Subgroup G),
      (∀ i, Function.Surjective (π i)) ∧ ∀ x : ↥(sSup 𝒟), (∀ i, π i x = 1) → x = 1 := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := h.pairwise) h.iSupIndep
  have hr : (Subgroup.noncommPiCoprod h.pairwise).range = sSup 𝒟 := by
    rw [Subgroup.noncommPiCoprod_range, sSup_eq_iSup']
  set e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  refine ⟨fun i => (Pi.evalMonoidHom (fun j : ↥𝒟 => ↥(j : Subgroup G)) i).comp
    e.symm.toMonoidHom, fun i y => ?_, fun x hx => ?_⟩
  · classical
    refine ⟨e (Pi.mulSingle i y), ?_⟩
    simp
  · have : e.symm x = 1 := funext hx
    simpa using congrArg e this

theorem eq_bot_of_isSolvable (h : SemiFam 𝒟) {N : Subgroup G} (hNE : N ≤ sSup 𝒟)
    (hN : sSup 𝒟 ≤ Subgroup.normalizer (N : Set G)) (hs : Group.IsSolvable ↥N) : N = ⊥ := by
  classical
  let _ : Fintype ↥𝒟 := Fintype.ofFinite _
  obtain ⟨π, hπs, hπ⟩ := h.exists_proj
  set N' : Subgroup ↥(sSup 𝒟) := N.subgroupOf (sSup 𝒟)
  have hN' : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr hN
  have hs' : Group.IsSolvable ↥N' :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNE).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNE).injective
  have hbot : ∀ i, N'.map (π i) = ⊥ := by
    intro i
    have := h.simple _ i.2
    have hn : (N'.map (π i)).Normal := hN'.map (π i) (hπs i)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map (π i)) with h1 | h1
    · exact h1
    · exfalso
      have hsol : Group.IsSolvable ↥(N'.map (π i)) := by
        have := hs'
        exact Group.isSolvable_of_surjective ((π i).subgroupMap_surjective N')
      rw [h1] at hsol
      have : Group.IsSolvable ↥(i : Subgroup G) := by
        have := hsol
        exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup ↥(i : Subgroup G)).subtype)
          fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
      exact not_nonabelian_of_isSolvable this (h.nonabelian _ i.2)
  refine le_bot_iff.mp fun x hx => ?_
  have h1 := hπ ⟨x, hNE hx⟩ fun i => by
    have : π i ⟨x, hNE hx⟩ ∈ N'.map (π i) := ⟨⟨x, hNE hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rwa [hbot i, Subgroup.mem_bot] at this
  simpa using congrArg Subtype.val h1

omit [Finite G] in
theorem commutator_eq (h : SemiFam 𝒟) : ⁅sSup 𝒟, sSup 𝒟⁆ = sSup 𝒟 := by
  refine le_antisymm (commutator_le_self _) (sSup_le fun D hD => ?_)
  have := h.simple D hD
  have hle : ⁅D, D⁆ ≤ D := commutator_le_self D
  have hn : ((⁅D, D⁆ : Subgroup G).subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left D D)
  have hDD : D ≤ ⁅D, D⁆ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅D, D⁆ : Subgroup G).subgroupOf D) with
      h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := h.nonabelian D hD
      apply hab
      apply Subtype.ext
      have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ ⁅D, D⁆ :=
        Subgroup.commutator_mem_commutator a.2 b.2
      rw [Subgroup.subgroupOf_eq_bot] at h1
      have h0 := (Subgroup.disjoint_def.mp h1) hc (hle hc)
      have : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ * b * a = b * a := by rw [h0, one_mul]
      simpa [mul_assoc] using this
    · exact Subgroup.subgroupOf_eq_top.mp h1
  exact hDD.trans (Subgroup.commutator_mono (le_sSup hD) (le_sSup hD))

theorem isSylowIn (h : SemiFam 𝒟) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hT : ∀ D ∈ 𝒟, IsSylowIn 2 (T ⊓ D) D) : IsSylowIn 2 (T ⊓ sSup 𝒟) (sSup 𝒟) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype ↥𝒟 := Fintype.ofFinite _
  set K : ↥𝒟 → Subgroup G := fun i => T ⊓ (i : Subgroup G) with hK
  have hKc : Pairwise fun i j : ↥𝒟 => ∀ x y : G, x ∈ K i → y ∈ K j → Commute x y :=
    fun i j hij x y hx hy => h.pairwise hij x y hx.2 hy.2
  have hKi : _root_.iSupIndep K := h.iSupIndep.mono fun i => inf_le_right
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hKc) hKi
  set P := ⨆ i, K i with hP
  have hcardP : Nat.card ↥P = ∏ i : ↥𝒟, Nat.card ↥(K i) := by
    rw [hP, ← Subgroup.noncommPiCoprod_range (hcomm := hKc),
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
  have hPE : P ≤ sSup 𝒟 := iSup_le fun i => inf_le_right.trans (le_sSup i.2)
  have hPT : P ≤ T := iSup_le fun i => inf_le_left
  have hSyl : IsSylowIn 2 P (sSup 𝒟) := by
    refine isSylowIn_of_card_eq hPE ?_
    rw [hcardP, h.card_eq, Nat.factorization_prod fun i _ => Nat.card_pos.ne']
    rw [Finset.sum_apply', ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => (hT i i.2).card_eq
  refine ⟨inf_le_right, hT2.to_le inf_le_left, fun h2 => hSyl.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P (T ⊓ sSup 𝒟) (sSup 𝒟) (le_inf hPT hPE) inf_le_right]
  exact Dvd.dvd.mul_left h2 _

end Finite

end SemiFam

end CFSG.Quasithin.E2.E22N.E111R
