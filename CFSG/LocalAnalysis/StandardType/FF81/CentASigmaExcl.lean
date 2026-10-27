module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelSymp
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip
import CFSG.LocalAnalysis.StandardType.FF81.CentAO2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin CFSG.Open

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

theorem false_of_sigma (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ) {σ : G}
    (hσH : σ ∈ Subgroup.centralizer ({t} : Set G)) (hσ2 : σ * σ = 1)
    (hσY : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y)
    (hσφ : ∀ y : ↥Y, φ ⟨σ * (y : G) * σ⁻¹, hσY (y : G) y.2⟩ = sigmaStd m (φ y))
    (hHσ : ∀ h ∈ Subgroup.centralizer ({t} : Set G), h ∈ Y ∨ h * σ ∈ Y) : False := by
  have hm1 : 1 ≤ m := by
    rcases hS.m_cases with rfl | rfl <;> norm_num
  have hm2 : 2 ≤ m := by
    rcases hS.m_cases with rfl | rfl <;> norm_num
  have hσne : σ ≠ 1 := by
    intro hσ1
    have hfix : ∀ g : GL (BlkIdx 1 m) (ZMod 2), sigmaStd m g = g := by
      intro g
      obtain ⟨y, rfl⟩ := φ.surjective g
      have hy : (⟨σ * (y : G) * σ⁻¹, hσY (y : G) y.2⟩ : ↥Y) = y := by
        apply Subtype.ext
        simp [hσ1]
      have h := hσφ y
      rw [hy] at h
      exact h.symm
    have hu12 : uOne m ≤ uTwo m := by
      intro u hu
      have hmem : sigmaStd m u ∈ (uOne m).map (sigmaStd m).toMonoidHom :=
        Subgroup.mem_map_of_mem (sigmaStd m).toMonoidHom hu
      rw [sigmaStd_map_uOne m] at hmem
      simpa [hfix u] using hmem
    exact (not_uOne_le_uTwo hm1) hu12
  let Cσ : Subgroup G := Subgroup.centralizer ({σ} : Set G)
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let W : Subgroup G := pCoreOf 2 Cσ
  have hWleC : W ≤ Cσ := by
    have h : pCoreOf 2 Cσ ≤ Cσ := Subgroup.map_subtype_le _
    simpa [W] using h
  have hW2 : IsPGroup 2 W := by
    have h : IsPGroup 2 (pCoreOf 2 Cσ) :=
      IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥Cσ)) Cσ.subtype
    simpa [W] using h
  have hWn : (W.subgroupOf Cσ).Normal := by
    have hEq : W.subgroupOf Cσ = pCore 2 ↥Cσ := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      change (x : G) ∈ (pCore 2 ↥Cσ).map Cσ.subtype ↔ x ∈ pCore 2 ↥Cσ
      exact Subgroup.mem_map_iff_mem Cσ.subtype_injective
    rw [hEq]
    exact pCore_normal
  have hCσN : Cσ ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWleC).mp hWn
  have hσ2loc : IsTwoLocal Cσ := by
    change IsTwoLocal (Subgroup.centralizer ({σ} : Set G))
    exact isTwoLocal_centralizer_of_mul_self hσne hσ2
  let K : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) :=
    ((W ⊓ Y).subgroupOf Y).map φ.toMonoidHom
  have hKfixed : ∀ k ∈ K, sigmaStd m k = k := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
    have hyWY : (y : G) ∈ W ⊓ Y := Subgroup.mem_subgroupOf.mp hy
    have hyW : (y : G) ∈ W := hyWY.1
    have hyC : (y : G) ∈ Cσ := hWleC hyW
    have hyσ : (y : G) * σ = σ * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hyfix : σ * (y : G) * σ⁻¹ = (y : G) := by
      rw [← hyσ]
      group
    have hyEq : (⟨σ * (y : G) * σ⁻¹, hσY (y : G) y.2⟩ : ↥Y) = y := by
      apply Subtype.ext
      exact hyfix
    have h := hσφ y
    rw [hyEq] at h
    exact h.symm
  have hK2 : IsPGroup 2 K := by
    have h1 : IsPGroup 2 ((W ⊓ Y).subgroupOf Y) :=
      (hW2.to_le (H := W ⊓ Y) (K := W) inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := W ⊓ Y) (K := Y) inf_le_right).symm
    exact h1.map φ.toMonoidHom
  have hKnorm : ∀ g, sigmaStd m g = g → ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
    have hyWY : (y : G) ∈ W ⊓ Y := Subgroup.mem_subgroupOf.mp hy
    have hyW : (y : G) ∈ W := hyWY.1
    have hyY : (y : G) ∈ Y := hyWY.2
    let y' : ↥Y := φ.symm g
    have hφy' : φ y' = g := φ.apply_symm_apply g
    have hσy' : σ * (y' : G) * σ⁻¹ = (y' : G) := by
      have h1 : φ ⟨σ * (y' : G) * σ⁻¹, hσY (y' : G) y'.2⟩ = φ y' := by
        calc
          φ ⟨σ * (y' : G) * σ⁻¹, hσY (y' : G) y'.2⟩ =
              sigmaStd m (φ y') := hσφ y'
          _ = sigmaStd m g := by rw [hφy']
          _ = g := hg
          _ = φ y' := hφy'.symm
      exact congrArg Subtype.val (φ.injective h1)
    have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
    have hy'σ : (y' : G) * σ = σ * (y' : G) := by
      calc
        (y' : G) * σ = (y' : G) * σ⁻¹ := by rw [hσinv]
        _ = σ⁻¹ * (y' : G) := by
          have h := congrArg (fun x => σ⁻¹ * x) hσy'
          simpa [mul_assoc] using h
        _ = σ * (y' : G) := by rw [hσinv]
    have hy'C : (y' : G) ∈ Cσ :=
      Subgroup.mem_centralizer_singleton_iff.mpr hy'σ
    have hy'nW : (y' : G) ∈ Subgroup.normalizer (W : Set G) := hCσN hy'C
    have hconjW : (y' : G) * (y : G) * (y' : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hy'nW (y : G)).mp hyW
    have hconjY : (y' : G) * (y : G) * (y' : G)⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem y'.2 hyY) (Y.inv_mem y'.2)
    have hcalc : g * φ y * g⁻¹ =
        φ ⟨(y' : G) * (y : G) * (y' : G)⁻¹, hconjY⟩ := by
      calc
        g * φ y * g⁻¹ = φ y' * φ y * (φ y')⁻¹ := by rw [hφy']
        _ = φ (y' * y * (y')⁻¹) := by
          rw [← map_mul, ← map_inv, ← map_mul]
        _ = φ ⟨(y' : G) * (y : G) * (y' : G)⁻¹, hconjY⟩ :=
          congrArg φ (Subtype.ext rfl)
    change g * φ y * g⁻¹ ∈ K
    rw [hcalc]
    exact Subgroup.mem_map.mpr
      ⟨⟨(y' : G) * (y : G) * (y' : G)⁻¹, hconjY⟩,
        Subgroup.mem_subgroupOf.mpr ⟨hconjW, hconjY⟩, rfl⟩
  have hKbot : K = ⊥ :=
    eq_bot_of_isPGroup_of_normal_sigmaFixed hS.m_cases K hKfixed hK2 hKnorm
  have hWY : W ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y := hx.2
    have hxK : φ ⟨x, hxY⟩ ∈ K := by
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hKbot] at hxK
    have hx1 : φ ⟨x, hxY⟩ = 1 := Subgroup.mem_bot.mp hxK
    have hy1 : (⟨x, hxY⟩ : ↥Y) = 1 := φ.injective (by simpa using hx1)
    simpa using congrArg Subtype.val hy1
  have hpair : ∀ w ∈ W ⊓ H, w ≠ 1 → ∀ w' ∈ W ⊓ H, w' ≠ 1 → w = w' := by
    intro w hw hw1 w' hw' hw'1
    have hwW : w ∈ W := hw.1
    have hwH : w ∈ H := hw.2
    have hw'W : w' ∈ W := hw'.1
    have hw'H : w' ∈ H := hw'.2
    have hwH' : w ∈ Subgroup.centralizer ({t} : Set G) := by simpa [H] using hwH
    have hw'H' : w' ∈ Subgroup.centralizer ({t} : Set G) := by simpa [H] using hw'H
    have hw_notY : w ∉ Y := by
      intro hwY
      have hmem : w ∈ W ⊓ Y := ⟨hwW, hwY⟩
      rw [hWY] at hmem
      exact hw1 (Subgroup.mem_bot.mp hmem)
    have hw'_notY : w' ∉ Y := by
      intro hw'Y
      have hmem : w' ∈ W ⊓ Y := ⟨hw'W, hw'Y⟩
      rw [hWY] at hmem
      exact hw'1 (Subgroup.mem_bot.mp hmem)
    have hwσY : w * σ ∈ Y := (hHσ w hwH').resolve_left hw_notY
    have hw'σY : w' * σ ∈ Y := (hHσ w' hw'H').resolve_left hw'_notY
    have hprodW : w * w'⁻¹ ∈ W := W.mul_mem hwW (W.inv_mem hw'W)
    have hprodY : w * w'⁻¹ ∈ Y := by
      have heq : (w * σ) * (w' * σ)⁻¹ = w * w'⁻¹ := by group
      rw [← heq]
      exact Y.mul_mem hwσY (Y.inv_mem hw'σY)
    have hprod : w * w'⁻¹ ∈ W ⊓ Y := ⟨hprodW, hprodY⟩
    rw [hWY] at hprod
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hprod)
  let yq : ↥Y := φ.symm (qStd m)
  let q : G := (yq : G)
  have hφq : φ yq = qStd m := φ.apply_symm_apply (qStd m)
  have hqY : q ∈ Y := yq.2
  have hqmem : q ∈ liftSub φ (Cent 1 m) := by
    rw [mem_liftSub]
    refine ⟨hqY, ?_⟩
    change φ yq ∈ Cent 1 m
    rw [hφq]
    exact qStd_mem_cent m
  have hqH : q ∈ H := by
    have h := (mem_liftSub_cent hS).mp hqmem
    simpa [H] using Subgroup.mem_centralizer_singleton_iff.mpr h.2
  have hqσ : q * σ = σ * q := by
    have hσq : σ * q * σ⁻¹ = q := by
      have h1 : φ ⟨σ * (yq : G) * σ⁻¹, hσY (yq : G) yq.2⟩ = φ yq := by
        rw [hσφ yq, hφq, sigmaStd_qStd]
      have h2 := φ.injective h1
      simpa using congrArg Subtype.val h2
    calc
      q * σ = (σ * q * σ⁻¹) * σ := by rw [hσq]
      _ = σ * q := by group
  have hqCσ : q ∈ Cσ := Subgroup.mem_centralizer_singleton_iff.mpr hqσ
  have horder_q : orderOf q = 3 := by
    change orderOf ((φ.symm (qStd m) : ↥Y) : G) = 3
    rw [Subgroup.orderOf_coe, (φ.symm).orderOf_eq (qStd m), orderOf_qStd hm2]
  have hfix : W ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers q : Set G) := by
    intro w hw
    have hwW : w ∈ W := hw.1
    have hwH : w ∈ H := by
      have h := hw.2
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
      simpa [H] using h
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    rcases eq_or_ne w 1 with rfl | hwne
    · simp
    · have hqWnorm : q ∈ Subgroup.normalizer (W : Set G) := hCσN hqCσ
      have hconjW : q * w * q⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp hqWnorm w).mp hwW
      have hconjH : q * w * q⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hqH hwH) (H.inv_mem hqH)
      have hconj_ne : q * w * q⁻¹ ≠ 1 := by
        intro h
        apply hwne
        have := congrArg (fun x => q⁻¹ * x * q) h
        simpa [mul_assoc] using this
      have heq : q * w * q⁻¹ = w :=
        hpair (q * w * q⁻¹) ⟨hconjW, hconjH⟩ hconj_ne w ⟨hwW, hwH⟩ hwne
      have hcomm : q * w = w * q := by
        have := congrArg (fun x => x * q) heq
        simpa [mul_assoc] using this
      exact hcomm.symm
  have htCσ : t ∈ Cσ := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hσH).symm
  have hPp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
    have ht2 : t * t = 1 := by
      have h1 : φ (⟨t, hS.t_mem⟩ * ⟨t, hS.t_mem⟩) = 1 := by
        rw [map_mul, hS.φ_t, jGL_mul_self]
      have h2 : (⟨t, hS.t_mem⟩ * ⟨t, hS.t_mem⟩ : ↥Y) = 1 :=
        φ.injective (by simpa using h1)
      simpa using congrArg Subtype.val h2
    simpa [pow_two] using ht2
  have hQcop : Nat.Coprime 2 (Nat.card (Subgroup.zpowers q)) := by
    rw [Nat.card_zpowers, horder_q]
    norm_num
  have hPB : Subgroup.zpowers t ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.zpowers_le_of_mem (hCσN htCσ)
  have hQB : Subgroup.zpowers q ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.zpowers_le_of_mem (hCσN hqCσ)
  have hqH' : q ∈ Subgroup.centralizer ({t} : Set G) := by simpa [H] using hqH
  have hPQ : ⁅Subgroup.zpowers t, Subgroup.zpowers q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.zpowers_le]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hqH').symm
  have hthom : ⁅W, Subgroup.zpowers q⁆ = ⊥ :=
    CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q (p := 2)
      (Subgroup.zpowers t) (Subgroup.zpowers q) W hPp hW2 hQcop hPB hQB hPQ hfix
  have hqCentW : q ∈ Subgroup.centralizer (W : Set G) := by
    have hWleCQ : W ≤ Subgroup.centralizer (Subgroup.zpowers q : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hthom
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWleCQ hw) q (Subgroup.mem_zpowers q)).symm
  have hq_inf : q ∈ Cσ ⊓ Subgroup.centralizer (W : Set G) := ⟨hqCσ, hqCentW⟩
  have hqW : q ∈ W := hchar Cσ hσ2loc hq_inf
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hW2) ⟨q, hqW⟩
  have hn' : orderOf q = 2 ^ n := (Subgroup.orderOf_coe ⟨q, hqW⟩).trans hn
  have h3 : 3 ∣ orderOf q := by
    simpa [horder_q] using dvd_refl 3
  have h32 : 3 ∣ 2 := by
    refine Nat.Prime.dvd_of_dvd_pow (p := 3) (m := 2) (n := n) (by norm_num) ?_
    rwa [hn'] at h3
  norm_num at h32


end CFSG.StandardType.FF81.CentA

end
