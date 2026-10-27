module

public import CFSG.Quasithin.EmptyFaithful.A38c14CentralLift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.Quasithin.A38c14

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem isSylowTwoOf_Ugrp : IsSylowTwoOf Ugrp ⊤ :=
  cert.isSylowTwoOf_top (rawIsEnc 22) cert_check (k := 7) (m := 3465) (by decide) (by decide)
    (by omega)

theorem card_Mgrp : Nat.card Mgrp = 443520 :=
  cert.card_m (rawIsEnc 22) (LatCert.closedOK_of_check cert_check)
    (LatCert.sizesOK_of_check cert_check)

theorem m22_types (hq : CFSG.IsQuasisimple ↥Mgrp)
    {B : Subgroup ↥Mgrp} (hB : B ∈ lFamily Ugrp) (hBtop : B ≠ ⊤) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) ∨
      IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 6 Y) := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hB' : B ∈ cComp (B ⊔ Ugrp) := hB
  have hPne : B ⊔ Ugrp ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hPns : ¬ Group.IsSolvable ↥(B ⊔ Ugrp) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ Ugrp))
        (Subgroup.inclusion_injective _))
  obtain ⟨j, hj, hLM, hPL, hcardj⟩ :=
    cert.overgroup_cases_idx (rawIsEnc 22) hck (B ⊔ Ugrp) le_sup_right
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [hlen] at hj
  have hM : Nat.card Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  interval_cases j
  ·
    have h128 : cert.sizes.getD 0 0 = 128 := rfl
    rw [h128] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 0) (by rw [hcardj]; norm_num)
  ·
    have h384 : cert.sizes.getD 1 0 = 384 := rfl
    rw [h384] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 1) (by rw [hcardj]; norm_num)
  ·
    have h1920 : cert.sizes.getD 2 0 = 1920 := rfl
    rw [h1920] at hcardj
    have ha := List.all_eq_true.mp incl5 2 (by simp)
    simp only [h1920, bne_self_eq_false, Bool.false_or] at ha
    have hlen2 : 2 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[2] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen2
    have hAL : Subgroup.closure {g | g ∈ p5Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen2] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext5
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]}⁆ ≤
          Subgroup.closure {g | g ∈ p5Gens} :=
      commutator_le_of_card_eq_two_mul hAL (by rw [hcardj, hAcard])
    have hperf : ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ =
        Subgroup.closure {g | g ∈ p5Gens} := perfect_of_perfOK (rawIsEnc 22) perf5_ok
    have hsimple := Seven.alt5_simple
    have hext := isExt_of_perfectCore_ext (M := Mgrp) hB hAL hLM hcomm hperf hPL
      Seven.alt5_nonabelian V hVc hVsq hVcard e
    exact Or.inl hext
  ·
    have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
    rw [h5760] at hcardj
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
    have hLA := Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, hAcard])
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]}⁆ ≤
          Subgroup.closure {g | g ∈ l6Gens} := by
      rw [← hLA]
      exact commutator_self_le _
    have hperf : ⁅Subgroup.closure {g | g ∈ l6Gens}, Subgroup.closure {g | g ∈ l6Gens}⁆ =
        Subgroup.closure {g | g ∈ l6Gens} := perfect_of_perfOK (rawIsEnc 22) perf6_ok
    have hsimple := Seven.alt6_simple
    have hext := isExt_of_perfectCore_ext (M := Mgrp) hB hAL hLM hcomm hperf hPL
      Seven.alt6_nonabelian V hVc hVsq hVcard e
    exact Or.inr hext
  ·
    have h443520 : cert.sizes.getD 4 0 = 443520 := rfl
    rw [h443520] at hcardj
    exfalso
    apply hPne
    have heq := Subgroup.eq_of_le_of_card_ge hLM (by rw [hM]; exact hcardj.symm.le)
    rw [hPL]
    exact (congrArg (fun K => K.subgroupOf Mgrp) heq).trans (Subgroup.subgroupOf_self Mgrp)
  ·
    have h384 : cert.sizes.getD 5 0 = 384 := rfl
    rw [h384] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 1) (by rw [hcardj]; norm_num)

theorem card_of_isE2 {V : Type} [Group V] {n : ℕ} (h : IsE2 n V) : Nat.card V = 2 ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n →
    ZMod 2) ≃ (Fin n → ZMod 2)), Nat.card_pi]
  simp

theorem card_of_isExt_alt {B : Type} [Group B] {n c : ℕ}
    (hn : Nat.card (alternatingGroup (Fin n)) = c)
    (h : IsExt B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt n Y)) : Nat.card B = c * 2 ^ 4 := by
  obtain ⟨V, hV, hE, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, Nat.card_congr e.toEquiv, hn,
    card_of_isE2 hE]


theorem hatM22 : FamHatM22 := by
  intro X _ _ hq hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLhat : IsHat ↥(⊤ : Subgroup X) (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    IsHat.of_mulEquiv Subgroup.topEquiv.symm hhat
  obtain ⟨-, hZ3, ⟨e⟩⟩ := hhat
  let e1 : X ⧸ Subgroup.center X ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  let e2 : X ⧸ Subgroup.center X ≃* ↥Mgrp :=
    e1.trans (MulEquiv.subgroupCongr mGens_closure.symm)
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hq.1
  let π : X →* ↥Mgrp := e2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := e2.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    change e2 (QuotientGroup.mk x) = 1 ↔ _
    rw [e2.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hk3 : Nat.card π.ker = 3 := by rw [hker]; exact hZ3
  have hkerc : π.ker ≤ Subgroup.center X := hker.le
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have : IsSimpleGroup ↥Mgrp := e2.symm.isSimpleGroup
  have hna : ∃ a b : ↥Mgrp, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e2 a, e2 b, fun h => hab (e2.injective (by simpa using h))⟩
  have hqM : CFSG.IsQuasisimple ↥Mgrp := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1
  have hXcard : Nat.card X = 27 * 49280 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [hZ3, Nat.card_congr e2.toEquiv, card_Mgrp] at h
    omega
  obtain ⟨T₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT₀ : IsSylowTwoOf (T₀ : Subgroup X) ⊤ := isSylowTwoOf_top_of_sylow T₀
  have hTb0 : IsSylowTwoOf ((T₀ : Subgroup X).map π) ⊤ := A312.isSylowTwoOf_top_map π hπ hT₀
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hTb0 isSylowTwoOf_Ugrp
  obtain ⟨g', rfl⟩ := hπ g
  let T : Subgroup X := (T₀ : Subgroup X).map (MulAut.conj g').toMonoidHom
  have hT : IsSylowTwoOf T ⊤ :=
    A312.isSylowTwoOf_top_map (MulAut.conj g').toMonoidHom (MulAut.conj g').surjective hT₀
  have hTmap : T.map π = Ugrp := by
    rw [← hg]
    show ((T₀ : Subgroup X).map (MulAut.conj g').toMonoidHom).map π = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [π]
  refine A312For.of_sylow T hT fun B hB hBtop => ?_
  have hBbar : B.map π ∈ lFamily Ugrp := by
    have := map_mem_lFamily π hkerc hB
    rwa [hTmap] at this
  have hBne : B.map π ≠ ⊤ := map_ne_top_of_central π hkerc hperf hBtop
  have hBperf : commutator ↥B = ⊤ := commutator_eq_top_of_lFamily hB
  have hc5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hc6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hE4 : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsE2 4 V → IsE2 4 W :=
    fun V W _ _ e h => IsE2.of_mulEquiv e h
  rcases m22_types hqM hBbar hBne with hE5 | hE6
  ·
    have hc : Nat.card ↥(B.map π) = 3 * 320 := by
      have := card_of_isExt_alt hc5 hE5
      omega
    have hinf : B ⊓ π.ker = ⊥ :=
      inf_ker_eq_bot_of_card π hkerc hk3 hBperf (m := 320) (by norm_num) hc
    have hext : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) :=
      A312.isExt_of_mulEquiv hE4 (fun V W _ _ e h => IsAlt.of_mulEquiv e h)
        (mapEquivOfInfKerEqBot π hinf).symm hE5
    iterate 10 right
    left
    exact Or.inr ⟨Or.inl hext, hLhat⟩
  ·
    have hc : Nat.card ↥(B.map π) = 9 * 640 := by
      have := card_of_isExt_alt hc6 hE6
      omega
    have hkerB : π.ker ≤ B :=
      ker_le_of_card_nine π hkerc hk3 hperf (m' := 49280) (by norm_num) hXcard (m := 640)
        (by norm_num) hc
    obtain ⟨Vb, hVbn, hVb, ⟨e6⟩⟩ := hE6
    have := alt6_simple
    let f : ↥B →* ↥(B.map π) := π.subgroupMap B
    have hf : Function.Surjective f := π.subgroupMap_surjective B
    have hfc : f.ker ≤ Subgroup.center ↥B := by
      intro x hx
      rw [Subgroup.ker_subgroupMap] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hkerc hx)) y.1)
    have hfk3 : Nat.card f.ker = 3 := by
      rw [Subgroup.ker_subgroupMap, ← hk3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerB).toEquiv
    obtain ⟨V, hVn, ⟨eV⟩, hHat⟩ := isExt_hat_of_central_cover alt6_nonabelian hBperf f hf hfc hfk3
      Vb (k := 4) (card_of_isE2 hVb) e6
    have hext : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) :=
      ⟨V, hVn, IsE2.of_mulEquiv eV.symm hVb, hHat⟩
    iterate 10 right
    left
    exact Or.inr ⟨Or.inr hext, hLhat⟩

end CFSG.Quasithin.A38c14
