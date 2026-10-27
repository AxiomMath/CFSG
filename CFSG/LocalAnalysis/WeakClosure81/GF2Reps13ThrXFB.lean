module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXF
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

private theorem w16g_odd_card_of_isElemAbelian_p37 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Finite X := inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 (x : MulAut W) x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn]
  exact Odd.pow (hp.odd_of_ne_two hp2)

private theorem w16g_map_sup {s : MulAut W} (S : Finset (Subgroup W)) :
    (S.sup id).map s.toMonoidHom = S.sup (fun U => U.map s.toMonoidHom) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert U S _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, Subgroup.map_sup, ih]
      rfl

private theorem w16g_image_map_eq_self {s : MulAut W} {S : Finset (Subgroup W)}
    [DecidableEq (Subgroup W)] (hsS : ∀ U ∈ S, U.map s.toMonoidHom ∈ S) :
    S.image (fun U => U.map s.toMonoidHom) = S := by
  classical
  have hinj : Function.Injective (fun U : Subgroup W => U.map s.toMonoidHom) :=
    Subgroup.map_injective s.injective
  have hsub : S.image (fun U => U.map s.toMonoidHom) ⊆ S := by
    intro V hV
    rcases Finset.mem_image.mp hV with ⟨U, hU, rfl⟩
    exact hsS U hU
  have hcard : (S.image (fun U => U.map s.toMonoidHom)).card = S.card :=
    Finset.card_image_of_injective S hinj
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

private theorem w16g_sup_stable {s : MulAut W} {S : Finset (Subgroup W)}
    [DecidableEq (Subgroup W)] (hsS : ∀ U ∈ S, U.map s.toMonoidHom ∈ S) :
    ∀ u ∈ S.sup id, s u ∈ S.sup id := by
  have himage := w16g_image_map_eq_self hsS
  have hmap := w16g_map_sup (s := s) S
  have hsup : S.sup (fun U => U.map s.toMonoidHom) = S.sup id := by
    have h1 : (S.image (fun U => U.map s.toMonoidHom)).sup id =
        S.sup (fun U => U.map s.toMonoidHom) := by
      rw [Finset.sup_image]
      rfl
    rw [← h1, himage]
  have hfix : (S.sup id).map s.toMonoidHom = S.sup id := hmap.trans hsup
  intro u hu
  have : s u ∈ (S.sup id).map s.toMonoidHom := Subgroup.mem_map_of_mem s.toMonoidHom hu
  rwa [hfix] at this

theorem s13_cost_eq (hW : ∀ w : W, w * w = 1) (hp : p = 3 ∨ p = 7) (hX : IsElemAbelian p X)
    {s : MulAut W} (hs2 : s * s = 1) (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X) {S : Set (Subgroup W)}
    (hS : S ⊆ s13IsoComps X) (hsS : ∀ U ∈ S, U.map s.toMonoidHom ∈ S)
    (hfix : ∀ U ∈ S, U.map s.toMonoidHom = U →
      p = 3 ∧ ∀ x ∈ X, s * x * s⁻¹ * x ∈ s13KerOn X U) :
    2 * rk ↥(commSub (⨆ U ∈ S, U) (Subgroup.zpowers s)) = ∑ᶠ U ∈ S, rk ↥U := by
  classical
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  have hp' : p.Prime := by rcases hp with h | h <;> (rw [h]; norm_num)
  have hp2 : p ≠ 2 := by rcases hp with h | h <;> (rw [h]; norm_num)
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian_p37 hp' hp2 hX
  have main : ∀ T : Finset (Subgroup W),
      (∀ U ∈ T, U ∈ s13IsoComps X) →
      (∀ U ∈ T, U.map s.toMonoidHom ∈ T) →
      (∀ U ∈ T, U.map s.toMonoidHom = U →
        p = 3 ∧ ∀ x ∈ X, s * x * s⁻¹ * x ∈ s13KerOn X U) →
      2 * rk ↥(commSub (T.sup id) (Subgroup.zpowers s)) = ∑ U ∈ T, rk ↥U := by
    intro T
    refine Finset.strongInductionOn T ?_
    intro T ih hS hsS hfix
    by_cases hTempty : T = ∅
    · subst hTempty
      rw [Finset.sup_empty, Finset.sum_empty]
      have hbot : commSub (⊥ : Subgroup W) (Subgroup.zpowers s) = ⊥ :=
        commSub_eq_bot_iff.mpr bot_le
      rw [hbot, rk_bot]
      ring
    · obtain ⟨U, hU⟩ := Finset.nonempty_iff_ne_empty.mpr hTempty
      have hSupIndep : T.SupIndep id := by
        have h1 : sSupIndep ((T : Set (Subgroup W))) :=
          (s13IsoComps_sSupIndep hW hodd).mono (fun V hV => hS V hV)
        have h2 : iSupIndep ((↑) : T → Subgroup W) := (sSupIndep_iff _).mp h1
        have h3 : iSupIndep ((fun U : Subgroup W => U) ∘ ((↑) : T → Subgroup W)) := by
          change iSupIndep ((↑) : T → Subgroup W)
          exact h2
        exact (iSupIndep_comp_coe_iff_supIndep).mp h3
      by_cases hfixU : U.map s.toMonoidHom = U
      ·
        set T' := T.erase U with hT'def
        have hT'sub : T' ⊆ T := by rw [hT'def]; exact Finset.erase_subset _ _
        have hT'card : T'.card < T.card := by
          rw [hT'def]; exact Finset.card_erase_lt_of_mem hU
        have hT'ssub : T' ⊂ T :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨hT'sub, fun h => hT'card.ne (congrArg Finset.card h)⟩
        have hT'mem : ∀ V ∈ T', V ∈ s13IsoComps X := fun V hV => hS V (hT'sub hV)
        have hUnotT' : U ∉ T' := by rw [hT'def]; exact Finset.notMem_erase U T
        have hsT' : ∀ V ∈ T', V.map s.toMonoidHom ∈ T' := by
          intro V hV
          have hVT : V ∈ T := hT'sub hV
          have hVne : V ≠ U := by
            intro hVU; rw [hVU] at hV; exact hUnotT' hV
          have hmap : V.map s.toMonoidHom ∈ T := hsS V hVT
          rw [hT'def, Finset.mem_erase]
          refine ⟨?_, hmap⟩
          intro hVmapU
          apply hVne
          have h1 : (V.map s.toMonoidHom).map s.toMonoidHom = V := by
            rw [Subgroup.map_map]
            have hcomp : s.toMonoidHom.comp s.toMonoidHom = MonoidHom.id W := by
              ext x; change s (s x) = x
              rw [← MulAut.mul_apply, hs2, MulAut.one_apply]
            rw [hcomp, Subgroup.map_id]
          rw [hVmapU, hfixU] at h1
          exact h1.symm
        have hfixT' : ∀ V ∈ T', V.map s.toMonoidHom = V →
            p = 3 ∧ ∀ x ∈ X, s * x * s⁻¹ * x ∈ s13KerOn X V :=
          fun V hV => hfix V (hT'sub hV)
        have ihT' := ih T' hT'ssub hT'mem hsT' hfixT'
        have hdisjU : Disjoint U (T'.sup id) := by
          rw [hT'def]
          exact (Finset.supIndep_iff_disjoint_erase.mp hSupIndep) U hU
        have hT_eq : T = insert U T' := by
          rw [hT'def]; exact (Finset.insert_erase hU).symm
        rw [hT_eq, Finset.sup_insert, Finset.sum_insert hUnotT']
        let F : Fin 2 → Subgroup W := fun i => if i = 0 then U else T'.sup id
        have hF0 : F 0 = U := by simp [F]
        have hF1 : F 1 = T'.sup id := by simp [F]
        have hF_indep : iSupIndep F := by
          apply (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
            (fun k => by fin_cases k <;> simp)).mpr
          rw [hF0, hF1]
          exact hdisjU
        have hF_stable : ∀ i, ∀ u ∈ F i, s u ∈ F i := by
          intro i
          fin_cases i
          · change ∀ u ∈ F 0, s u ∈ F 0
            rw [hF0]
            intro u hu
            have h1 : s u ∈ U.map s.toMonoidHom := Subgroup.mem_map_of_mem s.toMonoidHom hu
            rwa [hfixU] at h1
          · change ∀ u ∈ F 1, s u ∈ F 1
            rw [hF1]
            exact w16g_sup_stable hsT'
        have hsum := rk_commSub_iSup_eq_sum hW s F hF_indep hF_stable
        rw [Fin.sum_univ_two, hF0, hF1] at hsum
        have hFsup : (⨆ i, F i) = U ⊔ T'.sup id := by
          rw [← Finset.sup_univ_eq_iSup,
            show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
          rw [Finset.sup_insert, Finset.sup_singleton, hF0, hF1]
        rw [hFsup] at hsum
        have hUcost : 2 * rk ↥(commSub U (Subgroup.zpowers s)) = rk ↥U := by
          obtain ⟨hp3, hinv⟩ := hfix U hU hfixU
          have hX3 : IsElemAbelian 3 X := hp3 ▸ hX
          have hsU : ∀ u ∈ U, s u ∈ U := by
            intro u hu
            have h1 : s u ∈ U.map s.toMonoidHom := Subgroup.mem_map_of_mem s.toMonoidHom hu
            rwa [hfixU] at h1
          exact rk_commSub_fixed_inverted hW hX3 hs2 hsX (hS U hU) hsU hinv
        change 2 * rk ↥(commSub (U ⊔ T'.sup id) (Subgroup.zpowers s)) =
          rk ↥U + ∑ x ∈ T', rk ↥x
        rw [hsum, mul_add, hUcost, ihT']
      ·
        set U' := U.map s.toMonoidHom with hU'def
        have hU'mem : U' ∈ T := hsS U hU
        have hU'ne : U' ≠ U := hfixU
        have hmap_invol : ∀ V : Subgroup W, (V.map s.toMonoidHom).map s.toMonoidHom = V := by
          intro V
          rw [Subgroup.map_map]
          have hcomp : s.toMonoidHom.comp s.toMonoidHom = MonoidHom.id W := by
            ext x; change s (s x) = x
            rw [← MulAut.mul_apply, hs2, MulAut.one_apply]
          rw [hcomp, Subgroup.map_id]
        have hU'maps : U'.map s.toMonoidHom = U := by
          rw [show U' = U.map s.toMonoidHom from rfl, hmap_invol U]
        have hU'in : U' ∈ T.erase U := Finset.mem_erase.mpr ⟨hU'ne, hU'mem⟩
        set T' := (T.erase U).erase U' with hT'def
        have hT'sub : T' ⊆ T := by
          rw [hT'def]
          exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
        have hT'card : T'.card < T.card := by
          rw [hT'def]
          have h1 : ((T.erase U).erase U').card < (T.erase U).card :=
            Finset.card_erase_lt_of_mem hU'in
          have h2 : (T.erase U).card < T.card := Finset.card_erase_lt_of_mem hU
          omega
        have hT'ssub : T' ⊂ T :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨hT'sub, fun h => hT'card.ne (congrArg Finset.card h)⟩
        have hT'mem : ∀ V ∈ T', V ∈ s13IsoComps X := fun V hV => hS V (hT'sub hV)
        have hU'_notT' : U' ∉ T' := by rw [hT'def]; exact Finset.notMem_erase U' (T.erase U)
        have hsT' : ∀ V ∈ T', V.map s.toMonoidHom ∈ T' := by
          intro V hV
          have hV' : V ∈ (T.erase U).erase U' := by rwa [hT'def] at hV
          have hVT : V ∈ T := hT'sub hV
          have hVneU : V ≠ U := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hV')
          have hVneU' : V ≠ U' := Finset.ne_of_mem_erase hV'
          have hmap : V.map s.toMonoidHom ∈ T := hsS V hVT
          rw [hT'def, Finset.mem_erase, Finset.mem_erase]
          refine ⟨?_, ?_, hmap⟩
          · intro hVmapU'
            apply hVneU
            have h2 : (V.map s.toMonoidHom).map s.toMonoidHom = U := by
              rw [hVmapU', show U' = U.map s.toMonoidHom from rfl, hmap_invol U]
            rwa [hmap_invol V] at h2
          · intro hVmapU
            apply hVneU'
            have h2 : (V.map s.toMonoidHom).map s.toMonoidHom = U' := by
              rw [hVmapU]
            rwa [hmap_invol V] at h2
        have hfixT' : ∀ V ∈ T', V.map s.toMonoidHom = V →
            p = 3 ∧ ∀ x ∈ X, s * x * s⁻¹ * x ∈ s13KerOn X V :=
          fun V hV => hfix V (hT'sub hV)
        have ihT' := ih T' hT'ssub hT'mem hsT' hfixT'
        have hT_eq : T = insert U (insert U' T') := by
          rw [hT'def]
          calc T = insert U (T.erase U) := (Finset.insert_erase hU).symm
            _ = insert U (insert U' ((T.erase U).erase U')) := by
                  rw [Finset.insert_erase hU'in]
        have hU_not : U ∉ insert U' T' := by
          rw [Finset.mem_insert]
          intro h
          rcases h with h | h
          · exact hU'ne h.symm
          · have h' : U ∈ (T.erase U).erase U' := by rwa [hT'def] at h
            exact (Finset.notMem_erase U T)
              (Finset.mem_of_mem_erase (a := U') (s := T.erase U) h')
        have hUU'_disj : U ⊓ U' = ⊥ := by
          have h := (Finset.supIndep_iff_disjoint_erase.mp hSupIndep) U hU
          exact disjoint_iff.mp (h.mono_right (Finset.le_sup (f := id) hU'in))
        have hU_T' : Disjoint U (T'.sup id) := by
          have h := (Finset.supIndep_iff_disjoint_erase.mp hSupIndep) U hU
          have hsub : T' ⊆ T.erase U := by rw [hT'def]; exact Finset.erase_subset _ _
          exact h.mono_right (Finset.sup_mono hsub)
        have hU'_T' : Disjoint U' (T'.sup id) := by
          have h := (Finset.supIndep_iff_disjoint_erase.mp hSupIndep) U' hU'mem
          have hsub : T' ⊆ T.erase U' := by
            rw [Finset.subset_erase]
            exact ⟨hT'sub, hU'_notT'⟩
          exact h.mono_right (Finset.sup_mono hsub)
        have hU_notT' : U ∉ T' := by
          rw [hT'def]
          exact fun h => (Finset.notMem_erase U T)
            (Finset.mem_of_mem_erase (a := U') (s := T.erase U) h)
        have hUU'_T' : Disjoint (U ⊔ U') (T'.sup id) := by
          have hu : ({U, U'} : Finset (Subgroup W)) ⊆ T := by
            intro V hV
            rw [Finset.mem_insert, Finset.mem_singleton] at hV
            rcases hV with rfl | rfl
            · exact hU
            · exact hU'mem
          have huv : Disjoint ({U, U'} : Finset (Subgroup W)) T' := by
            rw [Finset.disjoint_left]
            intro V hV hVT'
            rw [Finset.mem_insert, Finset.mem_singleton] at hV
            rcases hV with rfl | rfl
            · exact hU_notT' hVT'
            · exact hU'_notT' hVT'
          have h := Finset.SupIndep.disjoint_sup_sup hSupIndep hu hT'sub huv
          simpa using h
        rw [hT_eq, Finset.sup_insert, Finset.sup_insert, Finset.sum_insert hU_not,
          Finset.sum_insert hU'_notT']
        let F : Fin 2 → Subgroup W := fun i => if i = 0 then U ⊔ U' else T'.sup id
        have hF0 : F 0 = U ⊔ U' := by simp [F]
        have hF1 : F 1 = T'.sup id := by simp [F]
        have hF_indep : iSupIndep F := by
          apply (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
            (fun k => by fin_cases k <;> simp)).mpr
          rw [hF0, hF1]
          exact hUU'_T'
        have hU_U'_stable : ∀ u ∈ U ⊔ U', s u ∈ U ⊔ U' := by
          intro u hu
          rcases Subgroup.mem_sup.mp hu with ⟨a, ha, b, hb, rfl⟩
          have hsa : s a ∈ U ⊔ U' := by
            have h1 : s a ∈ U.map s.toMonoidHom := Subgroup.mem_map_of_mem s.toMonoidHom ha
            rw [show U.map s.toMonoidHom = U' from rfl] at h1
            exact Subgroup.mem_sup_right h1
          have hsb : s b ∈ U ⊔ U' := by
            have h1 : s b ∈ U'.map s.toMonoidHom := Subgroup.mem_map_of_mem s.toMonoidHom hb
            rw [hU'maps] at h1
            exact Subgroup.mem_sup_left h1
          rw [map_mul]
          exact Subgroup.mul_mem _ hsa hsb
        have hF_stable : ∀ i, ∀ u ∈ F i, s u ∈ F i := by
          intro i
          fin_cases i
          · change ∀ u ∈ F 0, s u ∈ F 0
            rw [hF0]; exact hU_U'_stable
          · change ∀ u ∈ F 1, s u ∈ F 1
            rw [hF1]; exact w16g_sup_stable hsT'
        have hsum := rk_commSub_iSup_eq_sum hW s F hF_indep hF_stable
        rw [Fin.sum_univ_two, hF0, hF1] at hsum
        have hFsup : (⨆ i, F i) = (U ⊔ U') ⊔ T'.sup id := by
          rw [← Finset.sup_univ_eq_iSup,
            show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
          rw [Finset.sup_insert, Finset.sup_singleton, hF0, hF1]
        rw [hFsup] at hsum
        have hUU'cost : rk ↥(commSub (U ⊔ U') (Subgroup.zpowers s)) = rk ↥U :=
          (rk_commSub_swap hW hs2 rfl hUU'_disj).2
        have hUU'rank : rk ↥U' = rk ↥U := (rk_commSub_swap hW hs2 rfl hUU'_disj).1
        change 2 * rk ↥(commSub (U ⊔ (U' ⊔ T'.sup id)) (Subgroup.zpowers s)) =
          rk ↥U + (rk ↥U' + ∑ x ∈ T', rk ↥x)
        rw [← sup_assoc, hsum, mul_add, hUU'cost, ihT', hUU'rank]
        ring
  haveI : Fintype S := Fintype.ofFinite S
  let Sf : Finset (Subgroup W) := S.toFinset
  have hSf : (Sf : Set (Subgroup W)) = S := Set.coe_toFinset S
  have hSf_mem : ∀ U ∈ Sf, U ∈ s13IsoComps X := by
    intro U hU
    exact hS (hSf ▸ (Finset.mem_coe.mpr hU))
  have hsSf_mem : ∀ U ∈ Sf, U.map s.toMonoidHom ∈ Sf := by
    intro U hU
    have h1 : U ∈ S := hSf ▸ (Finset.mem_coe.mpr hU)
    have h2 : U.map s.toMonoidHom ∈ S := hsS U h1
    exact Finset.mem_coe.mp (hSf.symm ▸ h2)
  have hfixSf : ∀ U ∈ Sf, U.map s.toMonoidHom = U →
      p = 3 ∧ ∀ x ∈ X, s * x * s⁻¹ * x ∈ s13KerOn X U := by
    intro U hU
    exact hfix U (hSf ▸ (Finset.mem_coe.mpr hU))
  rw [← hSf, finsum_mem_coe_finset]
  have hsup : (⨆ U ∈ (Sf : Set (Subgroup W)), U) = Sf.sup id := by
    rw [Finset.sup_eq_iSup]
    simp only [id_eq]
    rfl
  rw [hsup]
  exact main Sf hSf_mem hsSf_mem hfixSf

theorem cost_commSub_Q (h : HAb A X Q t p) :
    2 * rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) = rk ↥(commSub ⊤ Q) ∧
      rk ↥(commSub ⊤ Q) ≤ 6 := by
  have hp' : p.Prime := by rcases h.hp with hp | hp <;> (rw [hp]; norm_num)
  have hp2 : p ≠ 2 := by rcases h.hp with hp | hp <;> (rw [hp]; norm_num)
  have ht2' : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx => h.hXA t h.htA x hx
  have htX' : ∀ x ∈ X, t⁻¹ * x * t ∈ X := by
    intro x hx
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
    simpa only [htinv] using htX x hx
  have htQ : Q.map (MulAut.conj t).toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro q ⟨q₀, hq₀, rfl⟩
      change MulAut.conj t q₀ ∈ Q
      rw [MulAut.conj_apply, h.hQinv q₀ hq₀]
      exact Q.inv_mem hq₀
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hQone : Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom = Q := by
    have h1 : MulAut.conj (1 : MulAut W) = 1 := by ext x; simp [MulAut.conj_apply]
    rw [h1]
    exact Subgroup.map_id Q
  have hsS : ∀ U ∈ s13Supp X Q, U.map t.toMonoidHom ∈ s13Supp X Q := by
    have hsupp := s13Supp_conj (X := X) (L := Q) (g := t) htX htX'
    rw [htQ] at hsupp
    intro U hU
    rw [hsupp]
    exact ⟨U, hU, rfl⟩
  have hfix : ∀ U ∈ s13Supp X Q, U.map t.toMonoidHom = U →
      p = 3 ∧ ∀ x ∈ X, t * x * t⁻¹ * x ∈ s13KerOn X U := by
    intro U hU hfixU
    rcases h.hp with hp3 | hp7
    · subst hp3
      have hU' : U ∈ s13Supp X (Q.map (MulAut.conj (1 : MulAut W)).toMonoidHom) := by
        rwa [hQone]
      have h1 := fixed_comp_inverted h (a := 1) A.one_mem (U := U) hU'
        (by simpa using hfixU)
      exact ⟨rfl, by simpa using h1⟩
    · subst hp7
      exact absurd hfixU
        (not_fixed_comp h (a := 1) A.one_mem (by rwa [hQone]))
  have hcost := s13_cost_eq h.hW h.hp h.hXe ht2' htX (fun U hU => hU.1) hsS hfix
  have hsupp_eq := commSub_top_eq_iSup_s13Supp h.hW hp' hp2 h.hXe h.hQX
  have hrk_eq := rk_commSub_top_eq_sum h.hW hp' hp2 h.hXe h.hQX
  have hfirst : 2 * rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) =
      rk ↥(commSub ⊤ Q) := by
    calc 2 * rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t))
        = 2 * rk ↥(commSub (⨆ U ∈ s13Supp X Q, U) (Subgroup.zpowers t)) := by
            rw [hsupp_eq]
      _ = ∑ᶠ U ∈ s13Supp X Q, rk ↥U := hcost
      _ = rk ↥(commSub ⊤ Q) := hrk_eq.symm
  refine ⟨hfirst, ?_⟩
  rw [← hfirst]
  have hle : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
    rk_mono (commSub_mono le_top le_rfl)
  have h3 : rk ↥(commSub (commSub ⊤ Q) (Subgroup.zpowers t)) ≤ 3 := le_trans hle h.hrk
  omega

theorem exists_conj_supp (h : HAb A X Q t p) {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    ∃ a ∈ A, U ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
  have hp' : p.Prime := by rcases h.hp with hp | hp <;> (rw [hp]; norm_num)
  have hp2 : p ≠ 2 := by rcases h.hp with hp | hp <;> (rw [hp]; norm_num)
  have hneU : commSub U X ≠ ⊥ := by
    obtain ⟨U₀, hIrr, hne₀, hUeq⟩ := hU
    intro hbot
    apply hne₀
    have hle : commSub U₀ X ≤ commSub U X := by
      rw [hUeq]
      exact commSub_mono (w16g_le_s13IsoSum_self hIrr) le_rfl
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  by_contra hcon
  push Not at hcon
  have hker : ∀ a ∈ A, Q.map (MulAut.conj a).toMonoidHom ≤ s13KerOn X U := by
    intro a ha
    have hQaX : Q.map (MulAut.conj a).toMonoidHom ≤ X := by
      rintro q ⟨q₀, hq₀, rfl⟩
      change MulAut.conj a q₀ ∈ X
      rw [MulAut.conj_apply]
      exact h.hXA a ha q₀ (h.hQX hq₀)
    have hcomm : commSub U (Q.map (MulAut.conj a).toMonoidHom) = ⊥ := by
      by_contra hc
      exact hcon a ha ⟨hU, hc⟩
    by_contra hnot
    have h2 := (s13IsoComps_commSub_eq h.hW hp' hp2 h.hXe hQaX hU).2 hnot
    rw [h2] at hcomm
    exact hneU (by rw [hcomm]; exact commSub_eq_bot_iff.mpr bot_le)
  have hXle : X ≤ s13KerOn X U := by
    conv_lhs => rw [h.hXgen, conjClosure]
    rw [Subgroup.closure_le]
    rintro x ⟨a, ha, q, hq, rfl⟩
    exact hker a ha (Subgroup.mem_map.mpr ⟨q, hq, MulAut.conj_apply a q⟩)
  have hXcent : X ≤ centSub U := fun x hx => (Subgroup.mem_inf.mp (hXle hx)).2
  have hfixV : U ≤ fixV X := by
    intro u hu
    rw [mem_fixV]
    intro x hx
    exact mem_centSub.mp (hXcent hx) u hu
  exact hneU (commSub_eq_bot_iff.mpr hfixV)

theorem rk_s13IsoComps_le_six (h : HAb A X Q t p) {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    rk ↥U ≤ 6 := by
  have hp' : p.Prime := by rcases h.hp with hp | hp <;> (rw [hp]; norm_num)
  have hp2 : p ≠ 2 := by rcases h.hp with hp | hp <;> (rw [hp]; norm_num)
  obtain ⟨a, ha, hUa⟩ := exists_conj_supp h hU
  have hconj := HAb.conj h ha
  have hle : U ≤ commSub ⊤ (Q.map (MulAut.conj a).toMonoidHom) := by
    rw [commSub_top_eq_iSup_s13Supp hconj.hW hp' hp2 hconj.hXe hconj.hQX]
    exact le_iSup₂
      (f := fun V (_ : V ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) => V) U hUa
  exact le_trans (rk_mono hle) (cost_commSub_Q hconj).2

theorem rk_s13IsoComps_eq_three (h : HAb A X Q t 7) {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    rk ↥U = 3 := by
  have hp' : Nat.Prime 7 := by norm_num
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  obtain ⟨a, ha, hUa⟩ := exists_conj_supp h hU
  have hconj := HAb.conj h ha
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian_p37 hp' hp2 hconj.hXe
  have hsX : ∀ x ∈ X, (a * t * a⁻¹) * x * (a * t * a⁻¹)⁻¹ ∈ X :=
    hconj.hXA (a * t * a⁻¹) hconj.htA
  have hsX' : ∀ x ∈ X, (a * t * a⁻¹)⁻¹ * x * (a * t * a⁻¹) ∈ X := by
    intro x hx
    have h2 : (a * t * a⁻¹) * (a * t * a⁻¹) = 1 := by
      rw [← pow_two]; exact hconj.ht2
    have hsinv : (a * t * a⁻¹)⁻¹ = a * t * a⁻¹ := inv_eq_of_mul_eq_one_right h2
    simpa only [hsinv] using hsX x hx
  have hQsm : (Q.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (a * t * a⁻¹)).toMonoidHom = Q.map (MulAut.conj a).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro q ⟨q₀, hq₀, rfl⟩
      obtain ⟨q₁, hq₁, hq₁eq⟩ := Subgroup.mem_map.mp hq₀
      change MulAut.conj (a * t * a⁻¹) q₀ ∈ Q.map (MulAut.conj a).toMonoidHom
      rw [MulAut.conj_apply, hconj.hQinv q₀ hq₀, ← hq₁eq]
      exact Subgroup.mem_map.mpr ⟨q₁⁻¹, Q.inv_mem hq₁, (MulAut.conj a).map_inv q₁⟩
    · exact le_of_eq (Subgroup.card_map_of_injective
        (K := Q.map (MulAut.conj a).toMonoidHom)
        (f := (MulAut.conj (a * t * a⁻¹)).toMonoidHom)
        (MulAut.conj (a * t * a⁻¹)).injective).symm
  have hsupp := s13Supp_conj (X := X) (L := Q.map (MulAut.conj a).toMonoidHom)
    (g := a * t * a⁻¹) hsX hsX'
  rw [hQsm] at hsupp
  have hsUa : U.map (a * t * a⁻¹).toMonoidHom ∈
      s13Supp X (Q.map (MulAut.conj a).toMonoidHom) := by
    rw [hsupp]
    exact ⟨U, hUa, rfl⟩
  have hnotfix : U.map (a * t * a⁻¹).toMonoidHom ≠ U :=
    not_fixed_comp h (a := a) ha hUa
  have hdisj : U ⊓ U.map (a * t * a⁻¹).toMonoidHom = ⊥ := by
    have hind : sSupIndep (s13IsoComps X) := s13IsoComps_sSupIndep hconj.hW hodd
    exact disjoint_iff.mp (hind.pairwiseDisjoint hU hsUa.1 (fun hh => hnotfix hh.symm))
  have hrank : rk ↥(U ⊔ U.map (a * t * a⁻¹).toMonoidHom) = 2 * rk ↥U := by
    have h := rk_sup_add_rk_inf U (U.map (a * t * a⁻¹).toMonoidHom)
    rw [hdisj, rk_bot, add_zero] at h
    rw [h]
    have hmap : rk ↥(U.map (a * t * a⁻¹).toMonoidHom) = rk ↥U := by
      unfold rk
      rw [Subgroup.card_map_of_injective (a * t * a⁻¹).injective]
    rw [hmap]
    ring
  have hle6 : rk ↥(U ⊔ U.map (a * t * a⁻¹).toMonoidHom) ≤ 6 := by
    have hsup_le : U ⊔ U.map (a * t * a⁻¹).toMonoidHom ≤
        commSub ⊤ (Q.map (MulAut.conj a).toMonoidHom) := by
      rw [commSub_top_eq_iSup_s13Supp hconj.hW hp' hp2 hconj.hXe hconj.hQX]
      exact sup_le
        (le_iSup₂
          (f := fun V (_ : V ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) => V) U hUa)
        (le_iSup₂
          (f := fun V (_ : V ∈ s13Supp X (Q.map (MulAut.conj a).toMonoidHom)) => V)
          (U.map (a * t * a⁻¹).toMonoidHom) hsUa)
    exact le_trans (rk_mono hsup_le) (cost_commSub_Q hconj).2
  have hle3 : rk ↥U ≤ 3 := by
    have h := hle6
    rw [hrank] at h
    omega
  have hdvd : 3 ∣ rk ↥U := by
    have hd := dParam_dvd_rk_s13IsoComps hconj.hW hp' hp2 hconj.hXe hU
    have hd7 : dParam 7 = 3 := by
      rw [dParam]
      exact orderOf_eq_prime (by decide) (by decide)
    rwa [hd7] at hd
  have hpos : 0 < rk ↥U := by
    have hne : U ≠ ⊥ := (s13IsoComps_le_commSub hconj.hW hodd hU).1
    by_contra h0
    exact hne ((rk_eq_zero_iff (fun v => by rw [pow_two]; exact hconj.hW v)).mp
      (Nat.eq_zero_of_not_pos h0))
  omega

end CFSG.LocalAnalysis.WeakClosure81
