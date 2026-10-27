module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenCore
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp1510

variable {M V₀ V U S H P : Subgroup G}

theorem exists_oddCore (hI : NamedInputs15 G) (hW : W15Eight1 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    ∃ Q₀ : Subgroup G, OddCore15 V₀ U H Q₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIH : iHull15 V₀ U H ≤ H := (hP.iHull15_le_P h).trans hP.P_le
  haveI hIn : ((iHull15 V₀ U H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2 (le_normalizer_iHull15 V₀ U H)
  let Hs := ↥H ⧸ (iHull15 V₀ U H).subgroupOf H
  let π : ↥H →* Hs := QuotientGroup.mk' ((iHull15 V₀ U H).subgroupOf H)
  haveI : Finite Hs := Finite.of_surjective π (QuotientGroup.mk'_surjective _)
  let Ps : Subgroup Hs := (P.subgroupOf H).map π
  have hPs2 : IsPGroup 2 Ps := by
    have h1 : IsPGroup 2 (P.subgroupOf H) :=
      hP.sylow.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.P_le).symm
    exact h1.map π
  have hPsidx : ¬ 2 ∣ Ps.index := by
    have hker : π.ker ≤ P.subgroupOf H := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_mono H (hP.iHull15_le_P h)
    have h1 : Ps.index = (P.subgroupOf H).index :=
      Subgroup.index_map_eq (P.subgroupOf H)
        (QuotientGroup.mk'_surjective ((iHull15 V₀ U H).subgroupOf H)) hker
    rw [h1]
    exact hP.sylow.not_dvd_relIndex
  let S : Sylow 2 Hs := hPs2.toSylow hPsidx
  have hS_coe : (S : Subgroup Hs) = Ps := rfl
  obtain ⟨v, hvV₀, hvI⟩ := SetLike.not_le_iff_exists.1 (hP.not_V₀_le_iHull15 h)
  have hvH : v ∈ H := hP.V₀_le_H hvV₀
  set t₀ : Hs := π ⟨v, hvH⟩ with ht0_def
  have ht0_ne : t₀ ≠ 1 := by
    intro h1
    apply hvI
    have h2 : π (⟨v, hvH⟩ : ↥H) = 1 := by rw [← ht0_def]; exact h1
    have h3 : (⟨v, hvH⟩ : ↥H) ∈ (iHull15 V₀ U H).subgroupOf H := by
      rw [show (iHull15 V₀ U H).subgroupOf H = π.ker from
        (QuotientGroup.ker_mk' (N := (iHull15 V₀ U H).subgroupOf H)).symm]
      exact MonoidHom.mem_ker.2 h2
    exact Subgroup.mem_subgroupOf.1 h3
  have hv2 : v ^ 2 = 1 := h.hyp.elemAbelian₀.2 v hvV₀
  have ht0_sq : t₀ ^ 2 = 1 := by
    have h1 : (⟨v, hvH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [ht0_def, ← map_pow, h1, map_one]
  have ht0_mul : t₀ * t₀ = 1 := by rw [← pow_two]; exact ht0_sq
  have ht0_inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht0_mul
  have ht0_ord : orderOf t₀ = 2 := orderOf_eq_prime ht0_sq ht0_ne
  have ht0_ps : t₀ ∈ Ps := by
    rw [ht0_def]
    refine Subgroup.mem_map.2 ⟨⟨v, hP.V₀_le_H hvV₀⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (hP.V₀_le hvV₀)
    · exact congrArg π (Subtype.ext rfl)
  let t : (S : Subgroup Hs) := ⟨t₀, by rw [hS_coe]; exact ht0_ps⟩
  have hz : orderOf t = 2 := by
    have h1 : orderOf t = orderOf t₀ := Subgroup.orderOf_mk t₀ _
    rw [h1, ht0_ord]
  have hK : ∀ (g : ↥H), ((g : G)⁻¹ * v * (g : G)) ∈ V₀ →
      π (g⁻¹ * ⟨v, hvH⟩ * g) = t₀ := by
    intro g hgV
    have hnotI : (g : G)⁻¹ * v * (g : G) ∉ iHull15 V₀ U H := by
      intro hmem
      apply hvI
      have h1 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_iHull15 V₀ U H g.2) ((g : G)⁻¹ * v * (g : G))).1 hmem
      simpa [mul_assoc] using h1
    have hgV₁ : (g : G)⁻¹ * v * (g : G) ∉ v1Sub15 V₀ U :=
      fun hx => hnotI (v1Sub15_le_iHull15 V₀ U H hx)
    have hvV₁ : v ∉ v1Sub15 V₀ U := fun hx => hvI (v1Sub15_le_iHull15 V₀ U H hx)
    have hw : ((g : G)⁻¹ * v * (g : G))⁻¹ * v ∈ v1Sub15 V₀ U :=
      inv_mul_mem_of_relIndex_eq_two (hW.relIndex_eq_two hS h) hgV hvV₀ hgV₁ hvV₁
    rw [ht0_def]
    refine QuotientGroup.eq.2 ?_
    exact Subgroup.mem_subgroupOf.2 (v1Sub15_le_iHull15 V₀ U H hw)
  have hK' : ∀ (x : ↥H), (x : G) ∈ P → π (x * ⟨v, hvH⟩ * x⁻¹) = t₀ := by
    intro x hxP
    have hconjV : (x : G) * v * (x : G)⁻¹ ∈ V₀ := by
      have hxM : (x : G) ∈ M := hP.le_M hI hS h hxP
      have hxN : (x : G) ∈ normalizer (V₀ : Set G) := by rwa [h.hyp.normalizer₀]
      exact (Subgroup.mem_normalizer_iff.1 hxN v).1 hvV₀
    have h1 := hK x⁻¹ (by simpa using hconjV)
    simpa using h1
  have hzZ : t ∈ Subgroup.center (S : Subgroup Hs) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : Hs) * t₀ = t₀ * (y : Hs)
    obtain ⟨x, hxP, hxy⟩ := Subgroup.mem_map.1 (show (y : Hs) ∈ Ps from y.2)
    have hxG_P : (x : G) ∈ P := Subgroup.mem_subgroupOf.1 hxP
    have key : (y : Hs) * t₀ * (y : Hs)⁻¹ = t₀ := by
      rw [← hxy]
      have h1 : π x * t₀ * (π x)⁻¹ = π (x * ⟨v, hvH⟩ * x⁻¹) := by
        simp only [ht0_def, map_mul, map_inv]
      rw [h1]
      exact hK' x hxG_P
    calc (y : Hs) * t₀ = ((y : Hs) * t₀ * (y : Hs)⁻¹) * (y : Hs) := by group
      _ = t₀ * (y : Hs) := by rw [key]
  have hwc : ∀ g' : Hs, g'⁻¹ * t₀ * g' ∈ Ps → g'⁻¹ * t₀ * g' = t₀ := by
    intro g' hg'
    obtain ⟨g, hg_eq⟩ := QuotientGroup.mk'_surjective ((iHull15 V₀ U H).subgroupOf H) g'
    subst hg_eq
    change (π g)⁻¹ * t₀ * π g ∈ Ps at hg'
    change (π g)⁻¹ * t₀ * π g = t₀
    have hg'' : π (g⁻¹ * ⟨v, hvH⟩ * g) ∈ Ps := by
      convert hg' using 1
      simp only [ht0_def, map_mul, map_inv]
    obtain ⟨x, hxP, hxeq⟩ := Subgroup.mem_map.1 hg''
    have hmem : (x : G)⁻¹ * ((g : G)⁻¹ * v * (g : G)) ∈ iHull15 V₀ U H :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxeq)
    have hgvP : (g : G)⁻¹ * v * (g : G) ∈ P := by
      have h1 : (x : G) * ((x : G)⁻¹ * ((g : G)⁻¹ * v * (g : G))) ∈ P :=
        P.mul_mem (Subgroup.mem_subgroupOf.1 hxP) (hP.iHull15_le_P h hmem)
      simpa [mul_assoc] using h1
    have hleP : ∀ z ∈ V₀, (g : G)⁻¹ * z * (g : G) ∈ P := by
      intro z hz
      by_cases hzI : z ∈ iHull15 V₀ U H
      · have hgin : (g : G)⁻¹ * z * (g : G) ∈ iHull15 V₀ U H := by
          have h1 := (Subgroup.mem_normalizer_iff.1
            (le_normalizer_iHull15 V₀ U H (H.inv_mem g.2)) z).1 hzI
          simpa using h1
        exact hP.iHull15_le_P h hgin
      · have hzV₁ : z ∉ v1Sub15 V₀ U := fun hx => hzI (v1Sub15_le_iHull15 V₀ U H hx)
        have hvV₁ : v ∉ v1Sub15 V₀ U := fun hx => hvI (v1Sub15_le_iHull15 V₀ U H hx)
        have hw : v⁻¹ * z ∈ v1Sub15 V₀ U :=
          inv_mul_mem_of_relIndex_eq_two (hW.relIndex_eq_two hS h) hvV₀ hz hvV₁ hzV₁
        have hgin : (g : G)⁻¹ * (v⁻¹ * z) * (g : G) ∈ iHull15 V₀ U H := by
          have h1 := (Subgroup.mem_normalizer_iff.1
            (le_normalizer_iHull15 V₀ U H (H.inv_mem g.2)) (v⁻¹ * z)).1
            (v1Sub15_le_iHull15 V₀ U H hw)
          simpa using h1
        have hdecomp : (g : G)⁻¹ * z * (g : G) =
            ((g : G)⁻¹ * v * (g : G)) * ((g : G)⁻¹ * (v⁻¹ * z) * (g : G)) := by group
        rw [hdecomp]
        exact P.mul_mem hgvP (hP.iHull15_le_P h hgin)
    have hle : conjSubgroup V₀ (g : G) ≤ M := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have h1 := hleP ((g : G) * y * (g : G)⁻¹) hy
      have h2 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) = y := by group
      rw [h2] at h1
      exact (hP.le_M hI hS h) h1
    have hgM : (g : G) ∈ M := hP.fam.weakly_closed hI hS h g.2 hle
    have hgvV₀ : (g : G)⁻¹ * v * (g : G) ∈ V₀ := by
      have hgN : (g : G) ∈ normalizer (V₀ : Set G) := by rwa [h.hyp.normalizer₀]
      have hgNi : (g : G)⁻¹ ∈ normalizer (V₀ : Set G) :=
        (normalizer (V₀ : Set G)).inv_mem hgN
      have h1 := (Subgroup.mem_normalizer_iff.1 hgNi v).1 hvV₀
      simpa using h1
    have h1 : (π g)⁻¹ * t₀ * π g = π (g⁻¹ * ⟨v, hvH⟩ * g) := by
      simp only [ht0_def, map_mul, map_inv]
    rw [h1]
    exact hK g hgvV₀
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar S t hzZ hz hwc
  let N : Subgroup Hs := CFSG.oddCore Hs
  haveI hNnormal : N.Normal := by change (CFSG.oddCore Hs).Normal; infer_instance
  have hNodd : Odd (Nat.card N) := by
    change Odd (Nat.card (CFSG.oddCore Hs))
    exact CFSG.ComponentClassification.OddCore.odd_card Hs
  have hcen' : (QuotientGroup.mk t₀ : Hs ⧸ N) ∈ Subgroup.center (Hs ⧸ N) := hcen
  have hconjN : ∀ g' : Hs, g' * t₀ * g'⁻¹ * t₀ ∈ N := by
    intro g'
    have h := Subgroup.mem_center_iff.mp hcen' (QuotientGroup.mk g')
    have h' : ((g' * t₀ * g'⁻¹ : Hs) : Hs ⧸ N) = (t₀ : Hs ⧸ N) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      calc ((g' : Hs ⧸ N) * (t₀ : Hs ⧸ N)) * (g' : Hs ⧸ N)⁻¹
          = ((t₀ : Hs ⧸ N) * (g' : Hs ⧸ N)) * (g' : Hs ⧸ N)⁻¹ := by rw [h]
        _ = (t₀ : Hs ⧸ N) := by group
    have h2 : (g' * t₀ * g'⁻¹)⁻¹ * t₀ ∈ N := QuotientGroup.eq.mp h'
    have h2' : (g' * t₀ * g'⁻¹)⁻¹ * t₀ = g' * t₀ * g'⁻¹ * t₀ := by
      rw [mul_inv_rev, mul_inv_rev, ht0_inv, inv_inv]
      group
    rwa [h2'] at h2
  let Q₀ : Subgroup G := kHull15 V₀ H ⊓ (N.comap π).map H.subtype
  have hQH : Q₀ ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hQ_N : ∀ {x : G}, x ∈ Q₀ → ∃ hxH : x ∈ H, π ⟨x, hxH⟩ ∈ N := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx.2
    refine ⟨hyx ▸ y.2, ?_⟩
    have hψx : π (⟨x, hyx ▸ y.2⟩ : ↥H) = π y :=
      congrArg π (Subtype.ext hyx.symm)
    rw [hψx]
    exact Subgroup.mem_comap.1 hy
  have hQ_mem : ∀ {x : G} (hxK : x ∈ kHull15 V₀ H) (hxH : x ∈ H),
      π ⟨x, hxH⟩ ∈ N → x ∈ Q₀ := by
    intro x hxK hxH hxN
    exact Subgroup.mem_inf.2
      ⟨hxK, Subgroup.mem_map.2 ⟨⟨x, hxH⟩, Subgroup.mem_comap.2 hxN, rfl⟩⟩
  have hI_le_Q : iHull15 V₀ U H ≤ Q₀ := by
    intro x hx
    refine hQ_mem (Hyp1510.iHull15_le_kHull15 V₀ U H hx) (hIH hx) ?_
    have h1 : π (⟨x, hIH hx⟩ : ↥H) = 1 :=
      (QuotientGroup.eq_one_iff (⟨x, hIH hx⟩ : ↥H)).2 (Subgroup.mem_subgroupOf.2 hx)
    rw [h1]
    exact N.one_mem
  have hconj : ∀ {g : G}, g ∈ H → ∀ {x : G}, x ∈ Q₀ → g * x * g⁻¹ ∈ Q₀ := by
    intro g hg x hx
    obtain ⟨hxH, hxN⟩ := hQ_N hx
    have hxK : x ∈ kHull15 V₀ H := hx.1
    have hxK' : g * x * g⁻¹ ∈ kHull15 V₀ H :=
      (Subgroup.mem_normalizer_iff.1 (Hyp1510.le_normalizer_kHull15 V₀ H hg) x).1 hxK
    have hgxH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg)
    refine hQ_mem hxK' hgxH ?_
    have he : π (⟨g * x * g⁻¹, hgxH⟩ : ↥H) =
        π (⟨g, hg⟩ : ↥H) * π (⟨x, hxH⟩ : ↥H) * (π (⟨g, hg⟩ : ↥H))⁻¹ := by
      have hge : (⟨g * x * g⁻¹, hgxH⟩ : ↥H) =
          (⟨g, hg⟩ : ↥H) * ⟨x, hxH⟩ * (⟨g, hg⟩ : ↥H)⁻¹ := Subtype.ext rfl
      rw [hge]
      simp only [map_mul, map_inv]
    rw [he]
    exact hNnormal.conj_mem (π ⟨x, hxH⟩) hxN (π ⟨g, hg⟩)
  let ψ : ↥Q₀ →* Hs := π.comp (Subgroup.inclusion hQH)
  have hψN : ∀ x : ↥Q₀, ψ x ∈ N := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 x.2.2
    have hψx : ψ x = π y :=
      congrArg π (Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hyx.symm))
    rw [hψx]
    exact Subgroup.mem_comap.1 hy
  let f : ↥Q₀ →* ↥N := ψ.codRestrict N hψN
  have hker : f.ker = (iHull15 V₀ U H).subgroupOf Q₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx1 : ψ x = 1 := by
        have := congrArg (fun y : ↥N => (y : N)) hx
        simpa [f] using this
      have hx2 : π (Subgroup.inclusion hQH x) = 1 := by simpa [ψ] using hx1
      have hx3 : Subgroup.inclusion hQH x ∈ (iHull15 V₀ U H).subgroupOf H :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hQH x)).1 hx2
      have hx4 : ((Subgroup.inclusion hQH x : ↥H) : G) ∈ iHull15 V₀ U H :=
        Subgroup.mem_subgroupOf.1 hx3
      simpa [Subgroup.coe_inclusion] using hx4
    · intro hx
      apply Subtype.ext
      have hx' : ((Subgroup.inclusion hQH x : ↥H) : G) ∈ iHull15 V₀ U H := by
        simpa [Subgroup.coe_inclusion] using hx
      have hx2 : π (Subgroup.inclusion hQH x) = 1 :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hQH x)).2 (Subgroup.mem_subgroupOf.2 hx')
      have hfx : (f x : N) = ψ x := rfl
      rw [hfx]
      simpa [ψ] using hx2
  haveI hQ0normal : ((iHull15 V₀ U H).subgroupOf Q₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hI_le_Q).2
      (hQH.trans (le_normalizer_iHull15 V₀ U H))
  let Φ : ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀ →* ↥N :=
    QuotientGroup.lift ((iHull15 V₀ U H).subgroupOf Q₀) f (by rw [hker])
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | @H a =>
      induction b using QuotientGroup.induction_on with
      | @H b =>
        have hab' : f a = f b := by
          have h1 : Φ (QuotientGroup.mk a) = f a := rfl
          have h2 : Φ (QuotientGroup.mk b) = f b := rfl
          rw [h1, h2] at hab
          exact hab
        have hmem : a * b⁻¹ ∈ (iHull15 V₀ U H).subgroupOf Q₀ := by
          rw [← hker]
          exact MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hab', mul_inv_cancel])
        have hmem' : a⁻¹ * b ∈ (iHull15 V₀ U H).subgroupOf Q₀ := by
          have h3 : b * a⁻¹ ∈ (iHull15 V₀ U H).subgroupOf Q₀ := by
            simpa using (Subgroup.inv_mem _ hmem)
          have h4 := hQ0normal.conj_mem (b * a⁻¹) h3 a⁻¹
          simpa [mul_assoc] using h4
        exact QuotientGroup.eq.2 hmem'
  have hOddQuot : Odd (Nat.card (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀)) :=
    hNodd.of_dvd_nat (card_dvd_of_injective Φ hΦinj)
  have hsup_le : Q₀ ⊔ V₀ ≤ kHull15 V₀ H :=
    sup_le inf_le_left (Hyp1510.V₀_le_kHull15 V₀ H)
  have hsup_ge : kHull15 V₀ H ≤ Q₀ ⊔ V₀ := by
    rw [kHull15]
    refine conjClosure_le fun g hg z hz => ?_
    by_cases hzI : z ∈ iHull15 V₀ U H
    · have hgzI : g * z * g⁻¹ ∈ iHull15 V₀ U H :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_iHull15 V₀ U H hg) z).1 hzI
      exact Subgroup.mem_sup_left (hI_le_Q hgzI)
    · have hzV₁ : z ∉ v1Sub15 V₀ U := fun hx => hzI (v1Sub15_le_iHull15 V₀ U H hx)
      have hvV₁ : v ∉ v1Sub15 V₀ U := fun hx => hvI (v1Sub15_le_iHull15 V₀ U H hx)
      have hw : v⁻¹ * z ∈ v1Sub15 V₀ U :=
        inv_mul_mem_of_relIndex_eq_two (hW.relIndex_eq_two hS h) hvV₀ hz hvV₁ hzV₁
      have hgwI : g * (v⁻¹ * z) * g⁻¹ ∈ iHull15 V₀ U H :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_iHull15 V₀ U H hg) (v⁻¹ * z)).1
          (v1Sub15_le_iHull15 V₀ U H hw)
      have hyK : v⁻¹ * (g * v * g⁻¹) ∈ kHull15 V₀ H :=
        (kHull15 V₀ H).mul_mem ((kHull15 V₀ H).inv_mem (Hyp1510.V₀_le_kHull15 V₀ H hvV₀))
          ((Subgroup.mem_normalizer_iff.1 (Hyp1510.le_normalizer_kHull15 V₀ H hg) v).1
            (Hyp1510.V₀_le_kHull15 V₀ H hvV₀))
      have hyH : v⁻¹ * (g * v * g⁻¹) ∈ H :=
        H.mul_mem (H.inv_mem (hP.V₀_le_H hvV₀))
          (H.mul_mem (H.mul_mem hg (hP.V₀_le_H hvV₀)) (H.inv_mem hg))
      have hyN : π (⟨v⁻¹ * (g * v * g⁻¹), hyH⟩ : ↥H) ∈ N := by
        have hπy : π (⟨v⁻¹ * (g * v * g⁻¹), hyH⟩ : ↥H) =
            t₀ * (π (⟨g, hg⟩ : ↥H) * t₀ * (π (⟨g, hg⟩ : ↥H))⁻¹) := by
          have hy_eq : (⟨v⁻¹ * (g * v * g⁻¹), hyH⟩ : ↥H) =
              (⟨v, hvH⟩ : ↥H)⁻¹ *
                ((⟨g, hg⟩ : ↥H) * ⟨v, hvH⟩ * (⟨g, hg⟩ : ↥H)⁻¹) := Subtype.ext rfl
          rw [hy_eq]
          simp only [map_mul, map_inv, ← ht0_def, ht0_inv]
        rw [hπy]
        have h1 : (π ⟨g, hg⟩)⁻¹ * t₀ * π ⟨g, hg⟩ * t₀ ∈ N := by
          have h1' := hconjN (π ⟨g, hg⟩)⁻¹
          rwa [inv_inv] at h1'
        have h2 := hNnormal.conj_mem
          ((π ⟨g, hg⟩)⁻¹ * t₀ * π ⟨g, hg⟩ * t₀) h1 (π ⟨g, hg⟩)
        have he : π ⟨g, hg⟩ * ((π ⟨g, hg⟩)⁻¹ * t₀ * π ⟨g, hg⟩ * t₀) *
            (π ⟨g, hg⟩)⁻¹ = t₀ * (π ⟨g, hg⟩ * t₀ * (π ⟨g, hg⟩)⁻¹) := by group
        rwa [he] at h2
      have hyQ : v⁻¹ * (g * v * g⁻¹) ∈ Q₀ := hQ_mem hyK hyH hyN
      have hdecomp : g * z * g⁻¹ =
          v * (v⁻¹ * (g * v * g⁻¹)) * (g * (v⁻¹ * z) * g⁻¹) := by group
      rw [hdecomp]
      exact (Q₀ ⊔ V₀).mul_mem
        ((Q₀ ⊔ V₀).mul_mem (Subgroup.mem_sup_right hvV₀) (Subgroup.mem_sup_left hyQ))
        (Subgroup.mem_sup_left (hI_le_Q hgwI))
  have hsup_eq : Q₀ ⊔ V₀ = kHull15 V₀ H := le_antisymm hsup_le hsup_ge
  refine ⟨Q₀, ?_⟩
  refine ⟨hI_le_Q, inf_le_left, ?_, ?_, hsup_eq⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj hg, fun hx => by
      have h1 := hconj (H.inv_mem hg) hx
      simpa [mul_assoc] using h1⟩
  · exact hOddQuot

end Hyp1510

end CFSG.LocalAnalysis.WeakClosure81
