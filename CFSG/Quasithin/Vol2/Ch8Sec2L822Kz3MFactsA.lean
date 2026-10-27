module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Facts
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Quot
public import CFSG.Quasithin.AppendixH.H12.OvergroupsLat

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.Quasithin.AppendixH.H12 (card_Ugrp)

private lemma sizes_getD_eq_5760_kz3 {j : ℕ} (hj : j < 6) (h : cert.sizes.getD j 0 = 5760) :
    j = 3 := by
  rw [show cert.sizes = [128, 384, 1920, 5760, 443520, 384] from rfl] at h
  interval_cases j <;> simp_all

theorem mgrp_sub5760_model_kz3 (Y : Subgroup ↥Mgrp) (hY : Ugrp ≤ Y)
    (hcard : Nat.card Y = 5760) :
    Group.IsPerfect ↥Y ∧ ∃ φ : ↥Y →* alternatingGroup (Fin 6), Function.Surjective φ ∧
      ∀ x : ↥Y, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  obtain ⟨j, hj, hLM, hYeq, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck Y hY
  have hYc : Nat.card Y = cert.sizes.getD j 0 := by
    rw [hYeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj]
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  have hj6 : j < 6 := by rwa [hlen] at hj
  have hj3 : j = 3 := sizes_getD_eq_5760_kz3 hj6 (by rw [← hYc]; exact hcard)
  subst hj3
  have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
  have ha := List.all_eq_true.mp incl6 3 (by simp)
  simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
  have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
  have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
  have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
      Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
    rw [Subgroup.closure_le]
    intro g hg
    have := List.all_eq_true.mp ha g hg
    rw [List.getD_eq_getElem _ _ hlen3] at this
    exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
      (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
  obtain ⟨hAcard, V, hVn, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext6
  have hLA : Subgroup.closure {g | g ∈ l6Gens} =
      Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} :=
    Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, h5760, hAcard])
  have hLM' : Subgroup.closure {g | g ∈ l6Gens} ≤ Mgrp := hLA.le.trans hLM
  have hYeq' : Y = (Subgroup.closure {g | g ∈ l6Gens}).subgroupOf Mgrp := by
    rw [hLA]; exact hYeq
  let eY : ↥Y ≃* ↥(Subgroup.closure {g | g ∈ l6Gens}) :=
    (MulEquiv.subgroupCongr hYeq').trans (Subgroup.subgroupOfEquivOfLe hLM')
  have hperf : ⁅Subgroup.closure {g | g ∈ l6Gens}, Subgroup.closure {g | g ∈ l6Gens}⁆ =
      Subgroup.closure {g | g ∈ l6Gens} := perfect_of_perfOK (rawIsEnc 22) perf6_ok
  haveI hP : Group.IsPerfect ↥(Subgroup.closure {g | g ∈ l6Gens}) :=
    Subgroup.isPerfect_iff.mpr hperf
  haveI hPY : Group.IsPerfect ↥Y :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  let φ : ↥Y →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' V).comp eY.toMonoidHom)
  refine ⟨hPY, φ, ?_, ?_⟩
  · exact e.surjective.comp ((QuotientGroup.mk'_surjective V).comp eY.surjective)
  · intro x hx
    have hx' : e (QuotientGroup.mk' V (eY x)) = 1 := hx
    have h1 : (QuotientGroup.mk' V) (eY x) = 1 := e.injective (hx'.trans e.map_one.symm)
    have h2 : (eY x : ↥(Subgroup.closure {g | g ∈ l6Gens})) ∈ V :=
      (QuotientGroup.eq_one_iff _).mp h1
    refine ⟨1, eY.injective ?_⟩
    rw [map_pow, map_one]
    simpa [pow_two] using hVsq _ h2

private theorem exists_conj_map_eq_of_sylow_kz3 {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl⟩

theorem sub5760_conj_kz3 {Q : Type} [Group Q] [Finite Q]
    (ι : Q ≃* ↥Mgrp) (W : Subgroup Q) (hW : Nat.card W = 5760) :
    ∃ Y : Subgroup ↥Mgrp, Ugrp ≤ Y ∧ Nat.card Y = 5760 ∧ Nonempty (↥W ≃* ↥Y) := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hMgrp : Nat.card ↥Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  let W' : Subgroup ↥Mgrp := W.map ι.toMonoidHom
  let eW : ↥W ≃* ↥W' := Subgroup.equivMapOfInjective W ι.toMonoidHom ι.injective
  have hW'card : Nat.card W' = 5760 := by rw [← Nat.card_congr eW.toEquiv]; exact hW
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥W') 2 (n := 7)
    (by rw [hW'card]; norm_num)
  let K : Subgroup ↥Mgrp := K'.map W'.subtype
  have hKcard : Nat.card K = 128 := by
    change Nat.card (K'.map W'.subtype) = 128
    rw [Subgroup.card_map_of_injective W'.subtype_injective, hK']; norm_num
  have hKle : K ≤ W' := Subgroup.map_subtype_le K'
  have hKP : IsPGroup 2 K := IsPGroup.of_card (n := 7) (by rw [hKcard]; norm_num)
  have hidxK : K.index = 3465 := by
    have h := Subgroup.card_mul_index K
    rw [hKcard, hMgrp] at h; omega
  let P : Sylow 2 ↥Mgrp := IsPGroup.toSylow (P := K) hKP (by rw [hidxK]; norm_num)
  have hPU : IsPGroup 2 Ugrp := IsPGroup.of_card (n := 7) (by rw [card_Ugrp]; norm_num)
  have hidxU : Ugrp.index = 3465 := by
    have h := Subgroup.card_mul_index Ugrp
    rw [card_Ugrp, hMgrp] at h; omega
  let S : Sylow 2 ↥Mgrp := IsPGroup.toSylow (P := Ugrp) hPU (by rw [hidxU]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_sylow_kz3 P S
  have hS : (S : Subgroup ↥Mgrp) = Ugrp := rfl
  have hP : (P : Subgroup ↥Mgrp) = K := rfl
  rw [hS, hP] at hg
  refine ⟨W'.map (MulAut.conj g).toMonoidHom, ?_, ?_,
    ⟨eW.trans (Subgroup.equivMapOfInjective W' (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)⟩⟩
  · rw [hg]; exact Subgroup.map_mono hKle
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective W' (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv]
    exact hW'card

private theorem card_alt6_kz3 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  omega

private theorem pCore_alt6_eq_bot_kz3 : CFSG.pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 (alternatingGroup (Fin 6))) with
    h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (CFSG.pCore 2 (alternatingGroup (Fin 6))) := CFSG.pCore_isPGroup
    rw [h] at hp
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hp
    have h360 : 2 ^ n = 360 := by rw [← hn, Subgroup.card_top, card_alt6_kz3]
    have h3 : 3 ∣ 2 ^ n := by rw [h360]; norm_num
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem kzM22Sub5760_kz3_proved : KzM22Sub5760_kz3 := by
  intro Q _ _ hQ W hW
  obtain ⟨e⟩ := hQ
  let e' : Q ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  let ι : Q ≃* ↥Mgrp := e'.trans (MulEquiv.subgroupCongr mGens_closure).symm
  obtain ⟨Y, hUY, hYcard, ⟨eY⟩⟩ := sub5760_conj_kz3 ι W hW
  obtain ⟨hperfY, φ, hφs, hφk⟩ := mgrp_sub5760_model_kz3 Y hUY hYcard
  haveI hperfW : Group.IsPerfect ↥W :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  refine ⟨Subgroup.isPerfect_iff.mp hperfW, ?_⟩
  let ψ : ↥W →* alternatingGroup (Fin 6) := φ.comp eY.toMonoidHom
  have hψs : Function.Surjective ψ := hφs.comp eY.surjective
  have hψk : ∀ x : ↥W, ψ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hφk (eY x) hx
    exact ⟨k, eY.injective (by rw [map_pow, hk, map_one])⟩
  obtain ⟨e2⟩ := pCore_quot_equiv_kz3 ψ hψs hψk
  exact Nonempty.intro
    (e2.trans ((QuotientGroup.quotientMulEquivOfEq pCore_alt6_eq_bot_kz3).trans
      QuotientGroup.quotientBot))

end CFSG.Quasithin.H13
