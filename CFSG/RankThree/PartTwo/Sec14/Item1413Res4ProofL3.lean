module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofL3
import CFSG.RankThree.PartTwo.Sec14.Item1413Res4ProofL3Model
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofSignal
import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

namespace Proof1413Res4

section Abstract

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normalizer_le_normalizer_centralizer (R : Subgroup X) :
    Subgroup.normalizer (R : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ g ∈ Subgroup.normalizer (R : Set X), ∀ x ∈ Subgroup.centralizer (R : Set X),
      g * x * g⁻¹ ∈ Subgroup.centralizer (R : Set X) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro r hr
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) r).mp hr
      simpa using this
    have h1 := hx _ hr'
    calc r * (g * x * g⁻¹) = g * ((g⁻¹ * r * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * r := by group
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem card_inf_centralizer_eq_three_of_points {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hH1 : ∀ x ∈ E, x ≠ 1 → ∀ e ∈ E, e ∉ Subgroup.zpowers x → ∀ t : X,
      t * x = x * t → t ^ 2 = 1 → t ≠ 1 → e * t ≠ t * e)
    (hH2 : ∀ x ∈ E, x ≠ 1 → ∀ s t : X, s * x = x * s → t * x = x * t → s ^ 2 = 1 →
      t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s ≠ t → ∀ y : X, y * s = s * y → y * t = t * y →
        y * x = x * y)
    {R : Subgroup X} (hR2 : IsPGroup 2 R) (hR0 : R ≠ ⊥)
    (hER : E ≤ Subgroup.normalizer (R : Set X)) :
    Nat.card (E ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := R ⊓ Subgroup.centralizer (R : Set X) with hZ
  have hZ0 : Z ≠ ⊥ := by
    have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR0
    have : Nontrivial (Subgroup.center ↥R) := hR2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥R)
    intro h0
    apply hz
    have hzZ : ((z : ↥R) : X) ∈ Z := by
      refine ⟨(z : ↥R).2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have := Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩
      exact congrArg Subtype.val this
    rw [h0, Subgroup.mem_bot] at hzZ
    exact Subtype.ext (Subtype.ext hzZ)
  have hZ2 : IsPGroup 2 Z := hR2.to_le inf_le_left
  have hEZ : E ≤ Subgroup.normalizer (Z : Set X) :=
    Late.le_normalizer_inf hER (hER.trans (normalizer_le_normalizer_centralizer R))
  have hZ3 : ¬ 3 ∣ Nat.card Z := Proof1413Res3.not_three_dvd_of_isPGroup_two hZ2
  have : CFSG.IsElementaryAbelian 3 ↥E := Proof1413Res2.isElementaryAbelian_of_isElemAbelian hE
  have : Nontrivial ↥E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE9]
    norm_num
  have hgen := PartOne.KE8F.le_iSup_hyperplane_centralizers hEZ hZ3
  obtain ⟨B, hB, hZB⟩ : ∃ B : Subgroup ↥E, B.index = 3 ∧
      Z ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup X) : Set X) ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hZ0
    rw [eq_bot_iff]
    exact hgen.trans (iSup₂_le fun B hB => (hall B hB).le)
  have hB3 : Nat.card B = 3 := by
    have h := Subgroup.index_mul_card B
    rw [hB, Nat.card_congr (Equiv.refl _), show Nat.card ↥E = 9 from hE9] at h
    omega
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hall
    rw [this, Subgroup.card_bot] at hB3
    omega
  set x : X := (b : X) with hxdef
  have hxE : x ∈ E := b.2
  have hx1 : x ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hxB : x ∈ B.map E.subtype := ⟨b, hbB, rfl⟩
  have hCx : Subgroup.centralizer ((B.map E.subtype : Subgroup X) : Set X) ≤
      Subgroup.centralizer ({x} : Set X) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxB)
  obtain ⟨s, hsZ, hsx, hs2, hs1⟩ : ∃ s ∈ Z, s * x = x * s ∧ s ^ 2 = 1 ∧ s ≠ 1 := by
    set V := Z ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup X) : Set X) with hV
    have hV2 : IsPGroup 2 V := hZ2.to_le inf_le_left
    have hVnt : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hZB
    obtain ⟨n, hn0, hn⟩ := hV2.nontrivial_iff_card.mp hVnt
    have h2 : 2 ∣ Nat.card V := hn ▸ dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn0)
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 h2
    refine ⟨(v : X), v.2.1, ?_, ?_, ?_⟩
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hCx v.2.2))
    · have := pow_orderOf_eq_one v
      rw [hv] at this
      exact congrArg Subtype.val this
    · intro h
      have : v = 1 := Subtype.ext h
      rw [this, orderOf_one] at hv
      omega
  obtain ⟨e, heE, hex⟩ : ∃ e ∈ E, e ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have hle : E ≤ Subgroup.zpowers x := fun y hy => hall y hy
    have h1 := Subgroup.card_le_of_le hle
    rw [hE9, Nat.card_zpowers, orderOf_eq_prime (hE.2 x hxE) hx1] at h1
    omega
  have hcommE : ∀ y ∈ E, ∀ z ∈ E, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hsR : s ∈ R := hsZ.1
  have hsC : s ∈ Subgroup.centralizer (R : Set X) := hsZ.2
  have hne : ¬ E ≤ Subgroup.centralizer (R : Set X) := by
    intro hle
    exact hH1 x hxE hx1 e heE hex s hsx hs2 hs1
      (Subgroup.mem_centralizer_iff.mp (hle heE) s hsR).symm
  set s' := e * s * e⁻¹ with hs'
  have hs'Z : s' ∈ Z := (Subgroup.mem_normalizer_iff.mp (hEZ heE) s).mp hsZ
  have hex' : e * x = x * e := hcommE e heE x hxE
  have hs'x : s' * x = x * s' := by
    calc s' * x = e * (s * (e⁻¹ * x * e)) * e⁻¹ := by rw [hs']; group
      _ = e * (s * x) * e⁻¹ := by
          rw [show e⁻¹ * x * e = x by
            calc e⁻¹ * x * e = e⁻¹ * (x * e) := by group
              _ = e⁻¹ * (e * x) := by rw [hex']
              _ = x := by group]
      _ = e * (x * s) * e⁻¹ := by rw [hsx]
      _ = (e * x) * s * e⁻¹ := by group
      _ = (x * e) * s * e⁻¹ := by rw [hex']
      _ = x * s' := by rw [hs']; group
  have hs'2 : s' ^ 2 = 1 := by
    rw [hs', conj_pow, hs2, mul_one, mul_inv_cancel]
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hs1
    have := congrArg (fun y => e⁻¹ * y * e) h
    simpa [hs', mul_assoc] using this
  have hss' : s ≠ s' := by
    intro h
    apply hH1 x hxE hx1 e heE hex s hsx hs2 hs1
    calc e * s = e * s * e⁻¹ * e := by group
      _ = s * e := by rw [← hs', ← h]
  have hxR : x ∈ Subgroup.centralizer (R : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : r * s = s * r := Subgroup.mem_centralizer_iff.mp hsC r hr
    have h2 : r * s' = s' * r := Subgroup.mem_centralizer_iff.mp hs'Z.2 r hr
    exact hH2 x hxE hx1 s s' hsx hs'x hs2 hs'2 hs1 hs'1 hss' r h1 h2
  have hxC : x ∈ E ⊓ Subgroup.centralizer (R : Set X) := ⟨hxE, hxR⟩
  have hdvd : Nat.card (E ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hE9]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exfalso
    have h0 : E ⊓ Subgroup.centralizer (R : Set X) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (by simpa using hk')
    rw [h0, Subgroup.mem_bot] at hxC
    exact hx1 hxC
  · simpa using hk'
  · exfalso
    apply hne
    have h1 : E ⊓ Subgroup.centralizer (R : Set X) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hE9]; norm_num)
    rw [← h1]
    exact inf_le_right

end Abstract

end Proof1413Res4

open Proof1413Res4 in
theorem ks1419LThreePi : KS1419LThreePi := by
  intro X _ _ hX E hE hE9 htr R hR2 hR0 hER
  obtain ⟨π, p, f, K, _, hK, hq, ⟨ψ⟩⟩ := Proof142Res.exists_model_of_isLThreePi hX
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hlift : ∀ z : X, ∃ m ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk m = ((ψ z : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) := fun z => Subgroup.mem_map.mp (ψ z).2
  have hcoe_mul : ∀ a b : X, (((ψ (a * b)) : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = ((ψ a : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) * ((ψ b : projImage (slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) := fun a b => by rw [map_mul, Subgroup.coe_mul]
  have hcomm : ∀ a b : X, a * b = b * a →
      ((ψ a : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
          ((ψ b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((ψ b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
          ((ψ a : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
    intro a b h
    rw [← hcoe_mul, ← hcoe_mul, h]
  have hcomm' : ∀ a b : X,
      ((ψ a : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
          ((ψ b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((ψ b : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
          ((ψ a : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) →
      a * b = b * a := by
    intro a b h
    apply ψ.injective
    apply Subtype.ext
    rw [hcoe_mul, hcoe_mul, h]
  have hcoe_pow : ∀ (a : X) (n : ℕ), ((ψ (a ^ n) : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = ((ψ a : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) ^ n := fun a n => by rw [map_pow, Subgroup.coe_pow]
  have hcoe_one : ∀ a : X, a ≠ 1 → ((ψ a : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro a ha h
    apply ha
    apply ψ.injective
    apply Subtype.ext
    rw [h, map_one, Subgroup.coe_one]
  have hlift3 : ∀ y ∈ E, y ≠ 1 → ∃ m ∈ slPi π 3 (p ^ f) K, m ^ 3 = 1 ∧
      m ∉ StatedScalars (Fin 3) K ∧ ProjGenLinGroup.mk m =
        ((ψ y : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
    intro y hyE hy1
    obtain ⟨w, -, hw⟩ := htr y hyE hy1 y⁻¹ (inv_mem hyE) (inv_ne_one.mpr hy1)
    obtain ⟨m, hm, hmy⟩ := hlift y
    obtain ⟨h, -, hhw⟩ := hlift w
    have hdet : GeneralLinearGroup.det m = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact ((mem_slPi_iff hπ).mp hm).2)
    have hm3S : m ^ 3 ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hmy, ← hcoe_pow, hE.2 y hyE, map_one,
        Subgroup.coe_one]
    have hconj : h * m * h⁻¹ * m ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, hmy, hhw]
      have e1 : w * y * w⁻¹ * y = 1 := by rw [hw, inv_mul_cancel]
      have e2 := congrArg (fun z => ((ψ z : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K)) e1
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, map_one,
        Subgroup.coe_one] using e2
    refine ⟨m, hm, Proof142Res.pow_three_eq_one_of_conj_inv hdet hm3S hconj, fun hS => ?_, hmy⟩
    apply hcoe_one y hy1
    rw [← hmy, mk_eq_one_iff_mem_statedScalars]
    exact hS
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine card_inf_centralizer_eq_three_of_points hE hE9 ?_ ?_ hR2 hR0 hER
  ·
    intro x hxE hx1 e heE hex t htx ht2 ht1 het
    obtain ⟨g, hg, hg3, hgS, hgx⟩ := hlift3 x hxE hx1
    have he1 : e ≠ 1 := fun h => hex (h ▸ Subgroup.one_mem _)
    obtain ⟨me, hme, hme3, -, hmee⟩ := hlift3 e heE he1
    obtain ⟨mt, hmt, hmtt⟩ := hlift t
    refine not_commute_of_point hK hq hτ hτ1 hg hg3 hgS hme hme3 ?_ ?_ hmt ?_ ?_ ?_ ?_
    · rw [hmee, hgx]
      exact hcomm e x (hcommE e heE x hxE)
    · rw [hmee, hgx]
      intro hmem
      apply hex
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ψ.injective (Subtype.ext ?_)⟩
      rw [map_zpow, Subgroup.coe_zpow]
      exact hn
    · rw [hmtt, hgx]
      exact hcomm t x htx
    · rw [hmtt, ← hcoe_pow, ht2, map_one, Subgroup.coe_one]
    · rw [hmtt]
      exact hcoe_one t ht1
    · rw [hmee, hmtt]
      exact hcomm e t het
  ·
    intro x hxE hx1 s t hsx htx hs2 ht2 hs1 ht1 hst y hys hyt
    obtain ⟨g, hg, hg3, hgS, hgx⟩ := hlift3 x hxE hx1
    obtain ⟨ms, hms, hmss⟩ := hlift s
    obtain ⟨mt, hmt, hmtt⟩ := hlift t
    obtain ⟨my, -, hmyy⟩ := hlift y
    apply hcomm' y x
    rw [← hmyy, ← hgx]
    refine commute_of_two_involutions hK hq hτ hτ1 hg hg3 hgS hms hmt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hmss, hgx]
      exact hcomm s x hsx
    · rw [hmtt, hgx]
      exact hcomm t x htx
    · rw [hmss, ← hcoe_pow, hs2, map_one, Subgroup.coe_one]
    · rw [hmtt, ← hcoe_pow, ht2, map_one, Subgroup.coe_one]
    · rw [hmss]
      exact hcoe_one s hs1
    · rw [hmtt]
      exact hcoe_one t ht1
    · rw [hmss, hmtt]
      intro h
      exact hst (ψ.injective (Subtype.ext h))
    · rw [hmyy, hmss]
      exact hcomm y s hys
    · rw [hmyy, hmtt]
      exact hcomm y t hyt

end CFSG.RankThree.PartTwo.Sec14
