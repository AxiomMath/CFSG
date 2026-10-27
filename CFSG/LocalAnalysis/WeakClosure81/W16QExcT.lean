module

public import CFSG.LocalAnalysis.WeakClosure81.W16QExcSyl
public import CFSG.LocalAnalysis.WeakClosure81.W16QExcMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Exc1616

variable {M V₀ V U S H : Subgroup G}
  {φ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))}

private theorem w16q_conjSubgroup_iSub16_eq {M V₀ V U S H : Subgroup G}
    (c : Cfg1616 M V₀ V U S H) {g : G} (hg : g ∈ conjClosure V H) :
    conjSubgroup (iSub16 V H) g = iSub16 V H := by
  rw [conjSubgroup_eq_iff_mem_normalizer]
  have hnorm : H ≤ normalizer (iSub16 V H : Set G) := by
    rw [iSub16]
    exact le_normalizer_conjClosure _ _
  exact hnorm (c.conjClosure_le_H hg)

private theorem w16q_conjClosure_le_normalizer_iSub16 {M V₀ V U S H : Subgroup G}
    (c : Cfg1616 M V₀ V U S H) :
    conjClosure V H ≤ normalizer (iSub16 V H : Set G) :=
  c.conjClosure_le_H.trans (by
    rw [iSub16]
    exact le_normalizer_conjClosure _ _)

private theorem w16q_mem_centralizer_sup {A B : Subgroup G} {y : G}
    (hA : y ∈ centralizer (A : Set G)) (hB : y ∈ centralizer (B : Set G)) :
    y ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h1 : (A ⊔ B : Subgroup G) ≤ centralizer ({y} : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hA a ha
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hB b hb
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact Subgroup.mem_centralizer_singleton_iff.1 (h1 hz)

private theorem w16q_conj_comm_mem {M V₀ V U S H : Subgroup G}
    (c : Cfg1616 M V₀ V U S H) {g : G} (hg : g ∈ conjClosure V H) {i u : G}
    (hi : i ∈ iSub16 V H) (hu : u ∈ conjSubgroup V g) :
    i * u * i⁻¹ * u⁻¹ ∈ conjSubgroup V₀ g := by
  rw [mem_conjSubgroup_iff]
  have hgH : g ∈ H := c.conjClosure_le_H hg
  have hnorm : H ≤ normalizer (iSub16 V H : Set G) := by
    rw [iSub16]
    exact le_normalizer_conjClosure _ _
  have hjI : g * i * g⁻¹ ∈ iSub16 V H :=
    (Subgroup.mem_normalizer_iff.1 (hnorm hgH) i).1 hi
  have hjS : g * i * g⁻¹ ∈ S := (c.iSub16_le_tSub16 hjI).1
  have hyV : g * u * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hu
  have hcomm := c.cex.comm_mem_V₀ hjS hyV
  have heq : g * (i * u * i⁻¹ * u⁻¹) * g⁻¹ =
      (g * i * g⁻¹) * (g * u * g⁻¹) * (g * i * g⁻¹)⁻¹ * (g * u * g⁻¹)⁻¹ := by
    group
  rw [heq]
  exact hcomm

theorem exists_conj_eq (e : Exc1616 M V₀ V U S H φ) {k : G} (g : Gen1616 M V₀ V U S H k)
    {k₂ : G} (hk₂ : k₂ ∈ conjClosure V H) (hk₂M : k₂ ∉ M) :
    ∃ v ∈ V, conjSubgroup V₀ k₂ = conjSubgroup V₀ (k * v) := by
  have c := e.cfg
  obtain ⟨v, hv, hsup⟩ := e.exists_sup_eq g.mem hk₂ g.not_mem hk₂M
  have hv'K : k * v ∈ conjClosure V H :=
    (conjClosure V H).mul_mem g.mem (le_conjClosure V H hv)
  have hv'M : k * v ∉ M := by
    intro hm
    apply g.not_mem
    have hk : k = (k * v) * v⁻¹ := by group
    rw [hk]
    exact M.mul_mem hm (M.inv_mem (c.cex.hyp.h6.le_M hv))
  refine ⟨v, hv, ?_⟩
  have hI : IsElemAbelian 2 (iSub16 V H) :=
    Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hne : conjSubgroup V₀ k₂ ⊓ conjSubgroup V₀ (k * v) ≠ ⊥ := by
    obtain ⟨i, hi, u, hu, hne1⟩ :
        ∃ i ∈ iSub16 V H, ∃ u ∈ conjSubgroup V k₂, i * u * i⁻¹ * u⁻¹ ≠ 1 := by
      by_contra hcon
      have hcomm : ∀ i ∈ iSub16 V H, ∀ u ∈ conjSubgroup V k₂,
          i * u * i⁻¹ * u⁻¹ = 1 := by
        intro i hi u hu
        by_contra hne1
        exact hcon ⟨i, hi, u, hu, hne1⟩
      have hVC : conjSubgroup V k₂ ≤ centralizer (iSub16 V H : Set G) := by
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro i hi
        have h := hcomm i hi u hu
        have h' : i * u * i⁻¹ = u := by
          have h2 := congrArg (fun z => z * u) h
          simpa using h2
        calc i * u = (i * u * i⁻¹) * i := by group
          _ = u * i := by rw [h']
      have hVI : V ≤ centralizer (iSub16 V H : Set G) := by
        have h := E3.conjSubgroup_mono_left k₂⁻¹ hVC
        rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
          E3.conjSubgroup_centralizer,
          w16q_conjSubgroup_iSub16_eq c ((conjClosure V H).inv_mem hk₂)] at h
      have hVle : V ≤ U ⊔ V₀ := by
        have h := le_inf (le_refl V) hVI
        rwa [Cex16.inf_centralizer_iSub16_eq c.one c.five c.std c.cex c.min.fam16 c.not_le] at h
      have hZ₀ : U ⊔ V₀ ≤ pCoreOf 2 H :=
        (Cex16.inf_pCoreOf_eq c.one c.five c.std c.cex c.min.fam16 c.not_le).symm.le.trans
          inf_le_right
      exact c.not_le (hVle.trans hZ₀)
    have ha1 : i * u * i⁻¹ * u⁻¹ ∈ conjSubgroup V₀ k₂ := w16q_conj_comm_mem c hk₂ hi hu
    have huI : u ∈ conjSubgroup V (k * v) ⊔ iSub16 V H := by
      rw [← hsup]
      exact Subgroup.mem_sup_left hu
    have hWK : conjSubgroup V (k * v) ≤ conjClosure V H := by
      have hK : conjSubgroup (conjClosure V H) (k * v) = conjClosure V H := by
        rw [conjSubgroup_eq_iff_mem_normalizer]
        exact le_normalizer_conjClosure V H (c.conjClosure_le_H hv'K)
      have h := E3.conjSubgroup_mono_left (k * v) (le_conjClosure V H)
      rwa [hK] at h
    have hWnorm : conjSubgroup V (k * v) ≤ normalizer (iSub16 V H : Set G) :=
      hWK.trans (w16q_conjClosure_le_normalizer_iSub16 c)
    have hcoec : ((conjSubgroup V (k * v) ⊔ iSub16 V H : Subgroup G) : Set G) =
        (conjSubgroup V (k * v) : Set G) * (iSub16 V H : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hWnorm
    have hprod : u ∈ (conjSubgroup V (k * v) : Set G) * (iSub16 V H : Set G) := by
      rw [← hcoec]
      exact huI
    obtain ⟨a, ha, j, hj, rfl⟩ := hprod
    have ha2 : i * (a * j) * i⁻¹ * (a * j)⁻¹ ∈ conjSubgroup V₀ (k * v) := by
      have hkey : i * (a * j) * i⁻¹ * (a * j)⁻¹ = i * a * i⁻¹ * a⁻¹ := by
        have hcommij : j * i = i * j := B2F.isElemAbelian_comm hI hj hi
        have hcommij' : i⁻¹ * j = j * i⁻¹ := by
          calc i⁻¹ * j = i⁻¹ * (j * i) * i⁻¹ := by group
            _ = i⁻¹ * (i * j) * i⁻¹ := by rw [hcommij]
            _ = j * i⁻¹ := by group
        calc i * (a * j) * i⁻¹ * (a * j)⁻¹
            = i * a * (j * i⁻¹) * (j⁻¹ * a⁻¹) := by group
          _ = i * a * (i⁻¹ * j) * (j⁻¹ * a⁻¹) := by rw [hcommij']
          _ = i * a * i⁻¹ * a⁻¹ := by group
      rw [hkey]
      exact w16q_conj_comm_mem c hv'K hi ha
    intro hbot
    have hmem : i * (a * j) * i⁻¹ * (a * j)⁻¹ ∈ conjSubgroup V₀ k₂ ⊓
        conjSubgroup V₀ (k * v) := ⟨ha1, ha2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne1 hmem
  by_contra hEq
  have hb : conjSubgroup (conjSubgroup V₀ k₂ ⊓ conjSubgroup V₀ (k * v)) (k * v)⁻¹ =
      conjSubgroup V₀ (k₂ * (k * v)⁻¹) ⊓ V₀ := by
    rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      mul_inv_cancel, conjSubgroup_one]
  have hne' : conjSubgroup (conjSubgroup V₀ k₂ ⊓ conjSubgroup V₀ (k * v)) (k * v)⁻¹ ≠ ⊥ := by
    intro hbot
    apply hne
    have h2 := congrArg (fun A : Subgroup G => conjSubgroup A (k * v)) hbot
    rw [E3.conjSubgroup_bot, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
    exact h2
  by_cases hdM : k₂ * (k * v)⁻¹ ∈ M
  · have hdV : conjSubgroup V₀ (k₂ * (k * v)⁻¹) = V₀ := by
      rw [conjSubgroup_eq_iff_mem_normalizer, c.cex.hyp.normalizer₀]
      exact hdM
    have hsplit : (k₂ * (k * v)⁻¹) * (k * v) = k₂ := by group
    refine hEq ?_
    calc conjSubgroup V₀ k₂ = conjSubgroup V₀ ((k₂ * (k * v)⁻¹) * (k * v)) := by rw [hsplit]
      _ = conjSubgroup (conjSubgroup V₀ (k₂ * (k * v)⁻¹)) (k * v) :=
          (conjSubgroup_conjSubgroup V₀ (k₂ * (k * v)⁻¹) (k * v)).symm
      _ = conjSubgroup V₀ (k * v) := by rw [hdV]
  · exact hne' (by
      rw [hb]
      exact c.cex.hyp.conj_inf_eq_bot hdM)

theorem exists_mul_qSub16 (e : Exc1616 M V₀ V U S H φ) {t : G} (ht : t ∈ tSub16 V₀ S) :
    ∃ v ∈ V, v⁻¹ * t ∈ qSub16 V₀ V S H := by
  have c := e.cfg
  obtain ⟨k, g⟩ := e.exists_gen
  have htH : t ∈ H := c.min.fam16.1 ht.1
  have htM : t ∈ M := c.cex.S_le_M ht.1
  have hk₂K : t⁻¹ * k * t ∈ conjClosure V H := by
    have hconjK : conjSubgroup (conjClosure V H) t⁻¹ = conjClosure V H := by
      rw [conjSubgroup_eq_iff_mem_normalizer]
      exact (normalizer (conjClosure V H : Set G)).inv_mem
        (le_normalizer_conjClosure V H htH)
    have hmem : k ∈ conjSubgroup (conjClosure V H) t⁻¹ := by
      rw [hconjK]
      exact g.mem
    have := mem_conjSubgroup_iff.1 hmem
    simpa using this
  have hk₂M : t⁻¹ * k * t ∉ M := by
    intro hm
    apply g.not_mem
    have h1 : t * (t⁻¹ * k * t) * t⁻¹ = k := by group
    rw [← h1]
    exact M.mul_mem (M.mul_mem htM hm) (M.inv_mem htM)
  obtain ⟨v, hv, hconj⟩ := e.exists_conj_eq g hk₂K hk₂M
  set y : G := t * v⁻¹ with hy_def
  have htV₀ : conjSubgroup V₀ t = V₀ := by
    rw [conjSubgroup_eq_iff_mem_normalizer, c.cex.hyp.normalizer₀]
    exact htM
  have ht'V₀ : conjSubgroup V₀ t⁻¹ = V₀ := by
    rw [conjSubgroup_eq_iff_mem_normalizer, c.cex.hyp.normalizer₀]
    exact M.inv_mem htM
  have hconjW : conjSubgroup (conjSubgroup V₀ k) t =
      conjSubgroup (conjSubgroup V₀ k) v := by
    have e1 : conjSubgroup (conjSubgroup V₀ k) t = conjSubgroup V₀ (t⁻¹ * k * t) := by
      have h : conjSubgroup V₀ (t⁻¹ * k * t) = conjSubgroup (conjSubgroup V₀ k) t := by
        rw [show t⁻¹ * k * t = t⁻¹ * (k * t) by group]
        calc conjSubgroup V₀ (t⁻¹ * (k * t))
            = conjSubgroup (conjSubgroup V₀ t⁻¹) (k * t) :=
              (conjSubgroup_conjSubgroup V₀ t⁻¹ (k * t)).symm
          _ = conjSubgroup V₀ (k * t) := by rw [ht'V₀]
          _ = conjSubgroup (conjSubgroup V₀ k) t := (conjSubgroup_conjSubgroup V₀ k t).symm
      exact h.symm
    have e2 : conjSubgroup V₀ (k * v) = conjSubgroup (conjSubgroup V₀ k) v :=
      (conjSubgroup_conjSubgroup V₀ k v).symm
    rw [e1, hconj, e2]
  have hyN : y ∈ normalizer (conjSubgroup V₀ k : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    rw [hy_def, ← conjSubgroup_conjSubgroup, hconjW, conjSubgroup_conjSubgroup,
      mul_inv_cancel, conjSubgroup_one]
  have hyT : y ∈ tSub16 V₀ S := by
    rw [hy_def]
    exact (tSub16 V₀ S).mul_mem ht ((tSub16 V₀ S).inv_mem (c.V_le_tSub16 hv))
  have hyC : y ∈ centralizer (conjSubgroup V₀ k : Set G) :=
    g.mem_centralizer_of_mem_normalizer_conj hyT hyN
  have hyU : y ∈ centralizer (U : Set G) := c.cex.S_le_centralizer hyT.1
  have hyV₀ : y ∈ centralizer (V₀ : Set G) := hyT.2
  have hyCI : y ∈ centralizer (iSub16 V H : Set G) := by
    have hUV₀ : y ∈ centralizer ((U ⊔ V₀ : Subgroup G) : Set G) :=
      w16q_mem_centralizer_sup hyU hyV₀
    have hsup : y ∈ centralizer (((U ⊔ V₀) ⊔ conjSubgroup V₀ k : Subgroup G) : Set G) :=
      w16q_mem_centralizer_sup hUV₀ hyC
    exact Subgroup.centralizer_le g.iSub16_le_sup hsup
  have hyQ : y ∈ qSub16 V₀ V S H := e.tSub16_inf_centralizer_le ⟨hyT, hyCI⟩
  refine ⟨v, hv, ?_⟩
  have ht_eq : t = y * v := by rw [hy_def]; group
  have hvH : v ∈ H := c.min.fam16.1 (c.V_le_tSub16 hv).1
  have hconjQ : v⁻¹ * y * v ∈ qSub16 V₀ V S H := by
    have h := (Subgroup.mem_normalizer_iff.1
      ((normalizer (qSub16 V₀ V S H : Set G)).inv_mem (c.le_normalizer_qSub16 hvH)) y).1 hyQ
    simpa using h
  rw [show v⁻¹ * t = v⁻¹ * y * v by rw [ht_eq]; group]
  exact hconjQ

theorem inf_centralizer_le_sup (e : Exc1616 M V₀ V U S H φ) :
    qSub16 V₀ V S H ⊓ centralizer (V : Set G) ≤
      iSub16 V H ⊔ (tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G)) := by
  have c := e.cfg
  obtain ⟨k, g⟩ := e.exists_gen
  intro x hx
  have hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S := e.qSub16_le_tSub16
  have hxT : x ∈ tSub16 V₀ S := hQT hx.1
  have hxCI : x ∈ centralizer (iSub16 V H : Set G) :=
    c.qSub16_le_centralizer hQT hx.1
  have hI := Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  have hδI : k * x * k⁻¹ * x⁻¹ ∈ iSub16 V H := e.comm_mem_qSub16 hx.1 g.mem
  have hWleI : conjSubgroup V₀ k⁻¹ ≤ iSub16 V H := g.inv.conjSubgroup_le_iSub16
  have hUV₀leI : U ⊔ V₀ ≤ iSub16 V H := c.le_iSub16
  have hUV₀C : U ⊔ V₀ ≤ centralizer (conjSubgroup V₀ k⁻¹ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (B2F.isElemAbelian_comm hI (hUV₀leI ha) (hWleI hb)).symm
  have hUV₀N : U ⊔ V₀ ≤ normalizer (conjSubgroup V₀ k⁻¹ : Set G) :=
    hUV₀C.trans (Subgroup.centralizer_le_normalizer _)
  have hcoec : (((U ⊔ V₀) ⊔ conjSubgroup V₀ k⁻¹ : Subgroup G) : Set G) =
      ((U ⊔ V₀ : Subgroup G) : Set G) * (conjSubgroup V₀ k⁻¹ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUV₀N
  have hprod : k * x * k⁻¹ * x⁻¹ ∈
      ((U ⊔ V₀ : Subgroup G) : Set G) * (conjSubgroup V₀ k⁻¹ : Set G) := by
    rw [← hcoec]
    exact g.inv.iSub16_le_sup hδI
  obtain ⟨z₁, hz₁, b₁, hb₁, hδeq⟩ := hprod
  have hwV₀ : k⁻¹ * b₁ * k ∈ V₀ := by
    have := mem_conjSubgroup_iff.1 hb₁
    simpa using this
  set w : G := k⁻¹ * b₁ * k with hw_def
  have hwV : w ∈ V := c.cex.hyp.h6.le hwV₀
  have hwI : w ∈ iSub16 V H := c.le_iSub16 (Subgroup.mem_sup_right hwV₀)
  have hzV : z₁ ∈ V := (sup_le c.cex.le c.cex.hyp.h6.le) hz₁
  set c' : G := x * w⁻¹ with hc'_def
  have hc'T : c' ∈ tSub16 V₀ S :=
    (tSub16 V₀ S).mul_mem hxT ((tSub16 V₀ S).inv_mem (c.V_le_tSub16 hwV))
  have hwCV : w ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hv hwV
  have hc'V : c' ∈ centralizer (V : Set G) :=
    (centralizer (V : Set G)).mul_mem hx.2 ((centralizer (V : Set G)).inv_mem hwCV)
  have hwCI : w ∈ centralizer (iSub16 V H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm hI hy hwI
  have hc'I : c' ∈ centralizer (iSub16 V H : Set G) :=
    (centralizer (iSub16 V H : Set G)).mul_mem hxCI
      ((centralizer (iSub16 V H : Set G)).inv_mem hwCI)
  have hkc' : k * c' * k⁻¹ ∈ centralizer (V : Set G) := by
    have hkx : k * x * k⁻¹ = z₁ * b₁ * x := by
      calc k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
        _ = (z₁ * b₁) * x := by rw [← hδeq]
    have hkw : k * w * k⁻¹ = b₁ := by rw [hw_def]; group
    have hx_b : b₁ * x = x * b₁ :=
      Subgroup.mem_centralizer_iff.1 hxCI b₁ (hWleI hb₁)
    have h1 : k * c' * k⁻¹ = z₁ * x := by
      have step : k * c' * k⁻¹ = (z₁ * b₁ * x) * b₁⁻¹ := by
        calc k * c' * k⁻¹ = (k * x * k⁻¹) * (k * w⁻¹ * k⁻¹) := by rw [hc'_def]; group
          _ = (z₁ * b₁ * x) * (k * w⁻¹ * k⁻¹) := by rw [hkx]
          _ = (z₁ * b₁ * x) * b₁⁻¹ := by
              rw [show k * w⁻¹ * k⁻¹ = (k * w * k⁻¹)⁻¹ by group, hkw]
      rw [step]
      have hconj_b : b₁ * x * b₁⁻¹ = x := by rw [hx_b]; group
      calc (z₁ * b₁ * x) * b₁⁻¹ = z₁ * (b₁ * x * b₁⁻¹) := by group
        _ = z₁ * x := by rw [hconj_b]
    rw [h1, Subgroup.mem_centralizer_iff]
    intro v hv
    have hzv : z₁ * v = v * z₁ :=
      B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hzV hv
    have hxv : v * x = x * v := Subgroup.mem_centralizer_iff.1 hx.2 v hv
    calc v * (z₁ * x) = (v * z₁) * x := by group
      _ = (z₁ * v) * x := by rw [← hzv]
      _ = z₁ * (v * x) := by group
      _ = z₁ * (x * v) := by rw [hxv]
      _ = (z₁ * x) * v := by group
  have hc'Vk : c' ∈ centralizer (conjSubgroup V k : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hvV : k * u * k⁻¹ ∈ V := mem_conjSubgroup_iff.1 hu
    have hcomm := Subgroup.mem_centralizer_iff.1 hkc' (k * u * k⁻¹) hvV
    have hconj : k * (u * c') * k⁻¹ = k * (c' * u) * k⁻¹ := by
      calc k * (u * c') * k⁻¹ = (k * u * k⁻¹) * (k * c' * k⁻¹) := by group
        _ = (k * c' * k⁻¹) * (k * u * k⁻¹) := hcomm
        _ = k * (c' * u) * k⁻¹ := by group
    have := congrArg (fun z => k⁻¹ * z * k) hconj
    simpa using this
  have hc'K : c' ∈ centralizer (conjClosure V H : Set G) := by
    have hsup : c' ∈ centralizer (((V ⊔ conjSubgroup V k) ⊔ iSub16 V H : Subgroup G) :
        Set G) :=
      w16q_mem_centralizer_sup (w16q_mem_centralizer_sup hc'V hc'Vk) hc'I
    exact Subgroup.centralizer_le g.gen hsup
  have hx_eq : x = c' * w := by rw [hc'_def]; group
  rw [hx_eq]
  exact (iSub16 V H ⊔ (tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G))).mul_mem
    (Subgroup.mem_sup_right ⟨hc'T, hc'K⟩) (Subgroup.mem_sup_left hwI)

theorem mul_self_eq_one_of_mem (e : Exc1616 M V₀ V U S H φ) {x : G}
    (hx : x ∈ tSub16 V₀ S ⊓ centralizer (conjClosure V H : Set G)) : x * x = 1 := by
  have c := e.cfg
  let D : Subgroup G := tSub16 V₀ S ⊓ centralizer (V : Set G)
  have hxD : x ∈ D := ⟨hx.1, (Subgroup.centralizer_le (le_conjClosure V H)) hx.2⟩
  have hex : ∀ d ∈ D, ∃ v ∈ V, ∃ q ∈ qSub16 V₀ V S H,
      q ∈ centralizer (V : Set G) ∧ d = v * q := by
    intro d hd
    obtain ⟨v, hv, hqQ⟩ := e.exists_mul_qSub16 hd.1
    have hVleC : V ≤ centralizer (V : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr c.cex.hyp.h6.elemAbelian.1
    exact ⟨v, hv, v⁻¹ * d, hqQ,
      (centralizer (V : Set G)).mul_mem (hVleC (V.inv_mem hv)) hd.2, by group⟩
  have hsqC : ∀ d ∈ D, d * d ∈ centralizer (conjClosure V H : Set G) := by
    intro d hd
    obtain ⟨v, hv, q, hqQ, hqC, hd_eq⟩ := hex d hd
    have hcomm_vq : v * q = q * v := (Subgroup.mem_centralizer_iff.1 hqC) v hv
    have hvv : v * v = 1 := by
      simpa [pow_two] using c.cex.hyp.h6.elemAbelian.2 v hv
    have hsq : d * d = q * q := by
      rw [hd_eq]
      calc (v * q) * (v * q) = v * (q * v) * q := by group
        _ = v * (v * q) * q := by rw [← hcomm_vq]
        _ = (v * v) * (q * q) := by group
        _ = q * q := by rw [hvv, one_mul]
    rw [hsq]
    exact e.mul_self_mem_centralizer hqQ
  let Y : Subgroup G := Subgroup.closure {y : G | ∃ d ∈ D, y = d * d}
  have hYC : Y ≤ centralizer (conjClosure V H : Set G) :=
    (Subgroup.closure_le _).2 (by rintro y ⟨d, hd, rfl⟩; exact hsqC d hd)
  have hYD : Y ≤ D :=
    (Subgroup.closure_le _).2 (by rintro y ⟨d, hd, rfl⟩; exact D.mul_mem hd hd)
  have hYS : Y ≤ S := hYD.trans (inf_le_left.trans inf_le_left)
  have hY2 : IsPGroup 2 Y := c.cex.sylow.isPGroup.to_le hYS
  have hNY : normalizer (D : Set G) ≤ normalizer (Y : Set G) := by
    have key : ∀ n ∈ normalizer (D : Set G), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
      intro n hn y hy
      have hmap : Y ≤ Y.comap (MulAut.conj n).toMonoidHom := by
        refine (Subgroup.closure_le _).2 ?_
        rintro y ⟨d, hd, rfl⟩
        have hnd : n * d * n⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hn d).1 hd
        have hsq : n * (d * d) * n⁻¹ = (n * d * n⁻¹) * (n * d * n⁻¹) := by group
        change (MulAut.conj n) (d * d) ∈ Y
        rw [show (MulAut.conj n) (d * d) = n * (d * d) * n⁻¹ from rfl, hsq]
        exact Subgroup.subset_closure ⟨n * d * n⁻¹, hnd, rfl⟩
      simpa [MulAut.conj_apply] using Subgroup.mem_comap.1 (hmap hy)
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key n hn y hy, fun hy => ?_⟩
    have h := key n⁻¹ ((normalizer (D : Set G)).inv_mem hn) (n * y * n⁻¹) hy
    have h2 : n⁻¹ * (n * y * n⁻¹) * (n⁻¹)⁻¹ = y := by group
    rwa [h2] at h
  have hYbot : Y = ⊥ := by
    by_contra hYne
    have hSylD : IsSylowIn 2 D (M ⊓ centralizer (V : Set G)) :=
      Cex16.isSylowIn_tSub16_inf c.cex
    have hU : UniqueMax M (M ⊓ normalizer (D : Set G)) := c.cex.hyp.qclause D hSylD
    have hNMD : M ⊓ normalizer (D : Set G) ≤ normalizer (Y : Set G) :=
      inf_le_right.trans hNY
    have hNYM : normalizer (Y : Set G) ≤ M :=
      normalizer_le_of_inCalU hU hNMD hYne hY2
    exact c.not_conjClosure_le fun k hk =>
      hNYM ((Subgroup.centralizer_le_normalizer (Y : Set G))
        ((Subgroup.le_centralizer_iff.mp hYC) hk))
  have hD_sq : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    have hmem : d * d ∈ Y := Subgroup.subset_closure ⟨d, hd, rfl⟩
    rw [hYbot, Subgroup.mem_bot] at hmem
    exact hmem
  exact hD_sq x hxD

end Exc1616

end CFSG.LocalAnalysis.WeakClosure81

end
