module

public import CFSG.LocalAnalysis.UniquenessCase.UC6AutLbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Mz614


variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem Z_le_normalizer_OL : m.Z ≤ normalizer (m.OL : Set G) := by
  intro z hz
  have hc : ∀ z' ∈ m.Z, ∀ o' ∈ m.OL, z' * o' * z'⁻¹ = o' := by
    intro z' hz' o' ho'
    have h1 : o' ∈ centralizer (m.Z : Set G) := m.L_le_H (m.OL_le_L ho')
    have h2 := (Subgroup.mem_centralizer_iff.1 h1) z' hz'
    rw [h2]; group
  rw [Subgroup.mem_normalizer_iff]
  intro o
  constructor
  · intro ho
    rw [hc z hz o ho]; exact ho
  · intro ho
    have h3 := hc z⁻¹ (inv_mem hz) _ ho
    have h4 : z⁻¹ * (z * o * z⁻¹) * z⁻¹⁻¹ = o := by group
    rw [h4] at h3
    exact h3.symm ▸ ho

theorem E_le_normalizer_OL (h620 : m.C620) : m.E ≤ normalizer (m.OL : Set G) := by
  intro e he
  have hZL : e ∈ m.Z ⊔ m.L := h620.1 (m.E_le_A he)
  exact (sup_le m.Z_le_normalizer_OL m.L_le_normalizer_OL) hZL

theorem OL_le_M_of_E (h620 : m.C620) : m.OL ≤ m.M := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity m.hr
    (A := m.E) (X := m.OL) m.d.E_el (by rw [m.d.E_card]) (m.E_le_normalizer_OL h620)
    m.coprime_card_OL
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
  intro x hx
  have hzp : zpowers a ≤ m.E := Subgroup.zpowers_le.2 haE
  have hzne : zpowers a ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.1 h)
  have hxN : x ∈ normalizer ((zpowers a : Subgroup G) : Set G) :=
    centralizer_singleton_le_normalizer_zpowers a hx.2
  exact m.d.E_gamma (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 m.r m.E (zpowers a) hzp
    (one_le_pRank_of_ne_bot m.hr ((IsElemAbelian.isPGroup m.d.E_el).to_le hzp) hzne) hxN)

theorem OL_le_gammaL_E (h620 : m.C620) : m.OL ≤ gammaL m.L m.r m.E := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity m.hr
    (A := m.E) (X := m.OL) m.d.E_el (by rw [m.d.E_card]) (m.E_le_normalizer_OL h620)
    m.coprime_card_OL
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
  intro x hx
  have hzp : zpowers a ≤ m.E := Subgroup.zpowers_le.2 haE
  have hzne : zpowers a ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.1 h)
  have hxN : x ∈ normalizer ((zpowers a : Subgroup G) : Set G) :=
    centralizer_singleton_le_normalizer_zpowers a hx.2
  have hpr : 1 ≤ CFSG.Open.pRank m.r (zpowers a) :=
    one_le_pRank_of_ne_bot m.hr ((IsElemAbelian.isPGroup m.d.E_el).to_le hzp) hzne
  exact Subgroup.mem_iSup_of_mem (zpowers a) (Subgroup.mem_iSup_of_mem hzp
    (Subgroup.mem_iSup_of_mem hpr
      (show x ∈ m.L ⊓ normalizer ((zpowers a : Subgroup G) : Set G) from ⟨m.OL_le_L hx.1, hxN⟩)))

theorem not_dvd_card_OL_of_sigma (h619 : m.C619) (h620 : m.C620) {p : ℕ}
    (hp : p ∈ uniqueFourSigma m.M) : ¬ p ∣ Nat.card m.OL := by
  intro hdvd
  have hpp : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf p m.OL
  have hTne : T ≠ ⊥ := by
    intro hTb
    have hc := hT.card_eq
    rw [hTb, Subgroup.card_bot] at hc
    have hf : 1 ≤ (Nat.card m.OL).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpp Nat.card_pos.ne').1 hdvd
    have h3 : p ^ 1 ≤ p ^ (Nat.card m.OL).factorization p := Nat.pow_le_pow_right hpp.pos hf
    rw [← hc, pow_one] at h3
    have := hpp.one_lt
    omega
  have hstrong : IsStronglyPEmbedded p m.M :=
    isStronglyPEmbedded_of_sigmaOne m.hU m.S.maxLocal hp (m.hσ1 hp)
  have hTM : T ≤ m.M := hT.le.trans (m.OL_le_M_of_E h620)
  have hNle : normalizer (T : Set G) ≤ m.M := hstrong.normalizer_le hTne hT.isPGroup hTM
  have hfr := frattini_of_isSylowOf m.OL_le_L m.L_le_normalizer_OL hT
  exact m.not_L_le_M h619 ((le_of_eq hfr).trans
    (sup_le (m.OL_le_M_of_E h620) (fun x hx => hNle hx.2)))

theorem exists_mem_centralizer_L_mod_OL {p : ℕ} [Fact p.Prime] (hpO : ¬ p ∣ Nat.card m.OL) {y : G}
    (hy : y ∈ normalizer (m.L : Set G)) (hyp : IsPGroup p (zpowers y)) (l₀ : ↥m.L)
    (hfix : y * (l₀ : G) * y⁻¹ * (l₀ : G)⁻¹ ∈ m.OL) :
    ∃ l : ↥m.L, (l : G) ∈ centralizer ({y} : Set G) ∧ (l : G)⁻¹ * (l₀ : G) ∈ m.OL := by
  classical
  set Kc : Subgroup G := m.L ⊔ zpowers y with hKc
  have hyO : y ∈ normalizer (m.OL : Set G) := m.mem_normalizer_OL hy
  have hOKc : m.OL ≤ Kc := (m.OL_le_L).trans le_sup_left
  have hKcN : Kc ≤ normalizer (m.OL : Set G) :=
    sup_le m.L_le_normalizer_OL (Subgroup.zpowers_le.2 hyO)
  set M' : Subgroup Kc := m.OL.subgroupOf Kc with hM'
  haveI hMn : M'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOKc).2 hKcN
  set T' : Subgroup Kc := (zpowers y).subgroupOf Kc with hT'
  haveI : Fact (IsPGroup p T') := ⟨hyp.comap_subtype⟩
  have hcop : Nat.Coprime p (Nat.card M') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKc).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpO
  have hyKc : y ∈ Kc := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hl₀Kc : (l₀ : G) ∈ Kc := Subgroup.mem_sup_left l₀.2
  set y₁ : Kc := ⟨y, hyKc⟩ with hy₁
  set l₁ : Kc := ⟨(l₀ : G), hl₀Kc⟩ with hl₁
  set q : Kc →* Kc ⧸ M' := QuotientGroup.mk' M' with hq
  have hy₁T : y₁ ∈ T' := Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers y)
  have hcomm : q y₁ * q l₁ = q l₁ * q y₁ := by
    have h1 : y₁ * l₁ * y₁⁻¹ * l₁⁻¹ ∈ M' := hfix
    have h2 : q (y₁ * l₁ * y₁⁻¹ * l₁⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc q y₁ * q l₁ = (q y₁ * q l₁ * (q y₁)⁻¹ * (q l₁)⁻¹) * (q l₁ * q y₁) := by group
      _ = q l₁ * q y₁ := by rw [h2, one_mul]
  have hcent : q l₁ ∈ Subgroup.centralizer ((T'.map q : Subgroup (Kc ⧸ M')) : Set (Kc ⧸ M')) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 ht)
    have htj : t = y₁ ^ j := Subtype.ext (by simpa [hy₁] using hj.symm)
    rw [htj, map_zpow]
    exact ((Commute.zpow_left (show Commute (q y₁) (q l₁) from hcomm) j)).eq
  have key := CFSG.centralizer_map_quotient_eq_map_centralizer p T' M' hMn hcop
  simp only at key
  rw [key] at hcent
  obtain ⟨g, hg, hgl⟩ := Subgroup.mem_map.1 hcent
  have hgl' : (g : G)⁻¹ * (l₀ : G) ∈ m.OL := by
    have : g⁻¹ * l₁ ∈ M' := (QuotientGroup.eq).1 hgl
    exact this
  have hgL : (g : G) ∈ m.L := by
    have h3 : (g : G) = (l₀ : G) * ((g : G)⁻¹ * (l₀ : G))⁻¹ := by group
    rw [h3]
    exact m.L.mul_mem l₀.2 (m.L.inv_mem (m.OL_le_L hgl'))
  refine ⟨⟨(g : G), hgL⟩, ?_, hgl'⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := (Subgroup.mem_centralizer_iff.1 hg) y₁ hy₁T
  exact (congrArg Subtype.val this).symm

theorem exists_mem_normalizer_E_mk_eq (h620 : m.C620) (hEL : m.E ≤ m.L) {n : m.Lbar}
    (hn : n ∈ normalizer (m.Ebar : Set m.Lbar)) :
    ∃ l : ↥m.L, (l : G) ∈ normalizer (m.E : Set G) ∧ (QuotientGroup.mk l : m.Lbar) = n := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hEeq : m.EL = m.E := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf (m.E_le_A) hEL) ?_).symm
    rw [m.card_A_inf_L h620, m.d.E_card]
  set N : Subgroup ↥m.L := CFSG.pPrimeCore m.r ↥m.L with hN
  haveI hNn : N.Normal := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.L)
  set T : Subgroup ↥m.L := m.E.subgroupOf m.L with hT
  haveI : Fact (IsPGroup m.r T) := ⟨(IsElemAbelian.isPGroup m.d.E_el).comap_subtype⟩
  have hcop : Nat.Coprime m.r (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have key := CFSG.normalizer_map_quotient_eq_map_normalizer m.r T N hNn hcop
  simp only at key
  have hEb : m.Ebar = T.map (QuotientGroup.mk' N) := by
    ext x
    rw [m.mem_Ebar_iff, hEeq]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  rw [hEb, key] at hn
  obtain ⟨t, ht, htn⟩ := Subgroup.mem_map.1 hn
  refine ⟨t, ?_, htn⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.1 ht ⟨g, hEL hg⟩).1 (Subgroup.mem_subgroupOf.2 hg)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hg
    have hgL : g ∈ m.L := by
      have h3 : g = (t : G)⁻¹ * ((t : G) * g * (t : G)⁻¹) * (t : G) := by group
      rw [h3]
      exact m.L.mul_mem (m.L.mul_mem (m.L.inv_mem t.2) (hEL hg)) t.2
    have h1 := (Subgroup.mem_normalizer_iff.1 ht ⟨g, hgL⟩).2
      (Subgroup.mem_subgroupOf.2 (show (t : G) * g * (t : G)⁻¹ ∈ m.E from hg))
    exact Subgroup.mem_subgroupOf.1 h1

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
