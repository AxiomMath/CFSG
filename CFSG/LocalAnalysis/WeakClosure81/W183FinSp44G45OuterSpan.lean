module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Model
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataPhi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.GH74.KGroups CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.QuasithinUnique.Setup.X7b
open scoped List

private lemma w183finSp44_memK_sound {L : List El} {x : El} (h : memK L x = true) : x ∈ L := by
  rw [memK] at h
  obtain ⟨a, ha, hax⟩ := List.any_eq_true.mp h
  exact beq_iff_eq.mp hax ▸ ha

private lemma w183finSp44_oneE_mem_foldl (gens A : List El) (hA : oneE ∈ A) :
    oneE ∈ gens.foldl (fun l g => l ++ l.map fun x => gmulE x g) A := by
  induction gens generalizing A with
  | nil => simpa using hA
  | cons g gs ih =>
      rw [List.foldl_cons]
      exact ih _ (by simp [hA])

private lemma w183finSp44_oneE_mem_span2 (gens : List El) : oneE ∈ span2 gens := by
  simpa [span2] using w183finSp44_oneE_mem_foldl gens [oneE] (by simp)

private lemma w183finSp44_foldl_subset_of_closed (gens A : List El) (S : Finset El)
    (hA : ∀ x ∈ A, x ∈ S) (hcl : ∀ x ∈ S, ∀ y ∈ S, gmulE x y ∈ S)
    (hg : ∀ g ∈ gens, g ∈ S) :
    ∀ x ∈ gens.foldl (fun l g => l ++ l.map fun x => gmulE x g) A, x ∈ S := by
  induction gens generalizing A with
  | nil => simpa using hA
  | cons g gs ih =>
      rw [List.foldl_cons]
      refine ih _ ?_ (fun h hh => hg h (List.mem_cons_of_mem g hh))
      intro x hx
      rcases List.mem_append.mp hx with hxA | hxmap
      · exact hA x hxA
      · rcases List.mem_map.mp hxmap with ⟨a, ha, rfl⟩
        exact hcl a (hA a ha) g (hg g (by simp))

private lemma w183finSp44_span2_subset_of_closed (gens : List El) (S : Finset El)
    (h1 : oneE ∈ S) (hcl : ∀ x ∈ S, ∀ y ∈ S, gmulE x y ∈ S)
    (hg : ∀ g ∈ gens, g ∈ S) : ∀ x ∈ span2 gens, x ∈ S := by
  simpa [span2] using w183finSp44_foldl_subset_of_closed gens [oneE] S
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact h1) hcl hg

private theorem w183finSp44_sc_exp_lt (x : El) (hx : x ∈ SClist) : x.2 < 4 := by
  have h : SClist.all (fun y => decide (y.2 < 4)) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp h) x hx)

private lemma w183finSp44_mem_I2 {x : El} :
    x ∈ I2 ↔ x ∈ SClist ∧ x.2 = 0 ∧ x ≠ oneE ∧ gmulE x x = oneE := by
  simp only [I2, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  tauto

private theorem w183finSp44_row_gens_mem_span2 :
    phiRows.all (fun r => r.1.all (fun g => memK (span2 r.1) g)) = true := by
  decide +kernel

private lemma w183finSp44_row_gen_mem_span2 {r : List El × Nat × El} (hr : r ∈ phiRows)
    {g : El} (hg : g ∈ r.1) : g ∈ span2 r.1 :=
  w183finSp44_memK_sound ((List.all_eq_true.mp ((List.all_eq_true.mp
    w183finSp44_row_gens_mem_span2) r hr)) g hg)

private lemma w183finSp44_exp_of_mem (K : Finset El) (hinv : ∀ x ∈ K, gmulE x x = oneE)
    (hSC : ∀ x ∈ K, x ∈ SClist) {x : El} (hx : x ∈ K) : x.2 = 0 ∨ x.2 = 2 := by
  have hlt : x.2 < 4 := w183finSp44_sc_exp_lt x (hSC x hx)
  have hmod : (x.2 + x.2) % 4 = 0 := by
    have := congrArg Prod.snd (hinv x hx)
    simpa [gmulE, oneE] using this
  omega

noncomputable def outerRep (c : Nat) : Subgroup (MulAut S4) :=
  Subgroup.closure (autOf '' {x | x ∈ outerRepGens.getD c []})

theorem phi_rows_complete_codes (K : Finset El) (hSC : ∀ x ∈ K, x ∈ SClist)
    (hinv : ∀ x ∈ K, gmulE x x = oneE) (hcomm : ∀ x ∈ K, ∀ y ∈ K, gmulE x y = gmulE y x)
    (hcl : ∀ x ∈ K, ∀ y ∈ K, gmulE x y ∈ K) (hφ : phiE ∈ K) (h8 : 8 ≤ K.card) :
    ∃ r ∈ phiRows, ∀ x, x ∈ K ↔ x ∈ span2 (phiE :: r.1) := by
  classical
  let E : Finset El := K.filter (fun x => x.2 = 0)
  have hEmem : ∀ x, x ∈ E ↔ x ∈ K ∧ x.2 = 0 := by
    intro x; simp only [E, Finset.mem_filter]
  have hEK : E ⊆ K := fun x hx => ((hEmem x).mp hx).1
  have hphiK : phiE ∈ K := hφ
  have h1K : oneE ∈ K := by
    have h := hcl phiE hφ phiE hφ
    rwa [hinv phiE hφ] at h
  have h1E : oneE ∈ E := (hEmem oneE).mpr ⟨h1K, rfl⟩
  have hEcl : ∀ x ∈ E, ∀ y ∈ E, gmulE x y ∈ E := by
    intro x hx y hy
    have hxK := (hEmem x).mp hx
    have hyK := (hEmem y).mp hy
    refine (hEmem _).mpr ⟨hcl x hxK.1 y hyK.1, ?_⟩
    simp [gmulE, hxK.2, hyK.2]
  have hEinv : ∀ x ∈ E, gmulE x x = oneE := fun x hx => hinv x ((hEmem x).mp hx).1
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, gmulE x y = gmulE y x :=
    fun x hx y hy => hcomm x ((hEmem x).mp hx).1 y ((hEmem y).mp hy).1
  have hESC : ∀ x ∈ E, x ∈ SClist := fun x hx => hSC x ((hEmem x).mp hx).1
  have mem_K_iff : ∀ x, x ∈ K ↔ x ∈ E ∨ ∃ e ∈ E, x = gmulE phiE e := by
    intro x
    constructor
    · intro hxK
      rcases w183finSp44_exp_of_mem K hinv hSC hxK with hx0 | hx2
      · exact Or.inl ((hEmem x).mpr ⟨hxK, hx0⟩)
      · right
        have hpm := phi_mul_involutive x (hSC x hxK)
        have hz : (gmulE phiE x).2 = 0 := by rw [hpm.2.2.1, hx2]
        exact ⟨gmulE phiE x, (hEmem _).mpr ⟨hcl phiE hφ x hxK, hz⟩, hpm.1.symm⟩
    · rintro (hxE | ⟨e, heE, rfl⟩)
      · exact hEK hxE
      · exact hcl phiE hφ e (hEK heE)
  let imgE : Finset El := E.image (fun e => gmulE phiE e)
  have hKsub : K ⊆ E ∪ imgE := by
    intro x hx
    rcases (mem_K_iff x).mp hx with hxE | ⟨e, heE, rfl⟩
    · exact Finset.mem_union_left _ hxE
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heE, rfl⟩)
  have hEcard : 4 ≤ E.card := by
    have h1 : K.card ≤ (E ∪ imgE).card := Finset.card_le_card hKsub
    have h2 : (E ∪ imgE).card ≤ E.card + imgE.card := Finset.card_union_le E imgE
    have h3 : imgE.card ≤ E.card := Finset.card_image_le
    omega
  have hcardErase : 1 < (E.erase oneE).card := by
    rw [Finset.card_erase_of_mem h1E]; omega
  obtain ⟨u, huErase, v, hvErase, huv⟩ := Finset.one_lt_card.mp hcardErase
  have huE : u ∈ E := (Finset.mem_erase.mp huErase).2
  have hune : u ≠ oneE := (Finset.mem_erase.mp huErase).1
  have hvE : v ∈ E := (Finset.mem_erase.mp hvErase).2
  have hvne : v ≠ oneE := (Finset.mem_erase.mp hvErase).1
  have huI2 : u ∈ I2 := (w183finSp44_mem_I2).mpr
    ⟨hESC u huE, (hEmem u).mp huE |>.2, hune, hEinv u huE⟩
  have hvI2 : v ∈ I2 := (w183finSp44_mem_I2).mpr
    ⟨hESC v hvE, (hEmem v).mp hvE |>.2, hvne, hEinv v hvE⟩
  have hcUV : gmulE u v = gmulE v u := hEcomm u huE v hvE
  obtain ⟨r, hr, hlen2, hkleinSub, hspanKlein⟩ := E4_complete u huI2 v hvI2 huv hcUV
  have hkleinE : ∀ x ∈ klein u v, x ∈ E := by
    intro x hx
    simp only [klein, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1E
    · exact huE
    · exact hvE
    · exact hEcl u huE v hvE
  have hspanE : ∀ x ∈ span2 r.1, x ∈ E := fun x hx => hkleinE x (hspanKlein x hx)
  have key : ∀ r ∈ phiRows, (∀ x, x ∈ E ↔ x ∈ span2 r.1) →
      ∀ x, x ∈ K ↔ x ∈ span2 (phiE :: r.1) := by
    intro r hr hEr x
    have hrok := rows_ok r hr
    constructor
    · intro hxK
      rcases (mem_K_iff x).mp hxK with hxE | ⟨e, heE, rfl⟩
      · exact (hrok.2.2.2.2.2.1 x ((hEr x).mp hxE)).1
      · exact (hrok.2.2.2.2.2.1 e ((hEr e).mp heE)).2
    · intro hx
      rcases hrok.2.2.2.2.2.2 x hx with hxr | ⟨e, he, rfl⟩
      · exact (mem_K_iff x).mpr (Or.inl ((hEr x).mpr hxr))
      · exact (mem_K_iff (gmulE phiE e)).mpr (Or.inr ⟨e, (hEr e).mpr he, rfl⟩)
  by_cases hEsub : ∀ x ∈ E, x ∈ span2 r.1
  · exact ⟨r, hr, key r hr fun x => ⟨fun hx => hEsub x hx, fun hx => hspanE x hx⟩⟩
  · obtain ⟨w, hw⟩ := not_forall.mp hEsub
    rw [not_imp] at hw
    obtain ⟨hwE, hwNotSpan⟩ := hw
    have hwne : w ≠ oneE := by
      intro hw1
      exact hwNotSpan (by rw [hw1]; exact w183finSp44_oneE_mem_span2 r.1)
    have hwI2 : w ∈ I2 := (w183finSp44_mem_I2).mpr
      ⟨hESC w hwE, (hEmem w).mp hwE |>.2, hwne, hEinv w hwE⟩
    have hwcommR : ∀ g ∈ r.1, gmulE g w = gmulE w g := fun g hg =>
      hEcomm g (hspanE g (w183finSp44_row_gen_mem_span2 hr hg)) w hwE
    obtain ⟨r', hr', hlen3, hspanSub, hspanSub'⟩ :=
      E8_complete r hr hlen2 w hwI2 hwNotSpan hwcommR
    have hgenE : ∀ g ∈ r.1 ++ [w], g ∈ E := by
      intro g hg
      rcases List.mem_append.mp hg with hgr | hgw
      · exact hspanE g (w183finSp44_row_gen_mem_span2 hr hgr)
      · rw [List.mem_singleton.mp hgw]; exact hwE
    have hspanRsub : ∀ x ∈ span2 (r.1 ++ [w]), x ∈ E :=
      w183finSp44_span2_subset_of_closed (r.1 ++ [w]) E h1E hEcl hgenE
    have hspanR'E : ∀ x ∈ span2 r'.1, x ∈ E := fun x hx => hspanRsub x (hspanSub' x hx)
    by_cases hEsub' : ∀ x ∈ E, x ∈ span2 r'.1
    · exact ⟨r', hr', key r' hr' fun x => ⟨fun hx => hEsub' x hx, fun hx => hspanR'E x hx⟩⟩
    · obtain ⟨w', hw'⟩ := not_forall.mp hEsub'
      rw [not_imp] at hw'
      obtain ⟨hw'E, hw'NotSpan⟩ := hw'
      have hw'ne : w' ≠ oneE := by
        intro hw'1
        exact hw'NotSpan (by rw [hw'1]; exact w183finSp44_oneE_mem_span2 r'.1)
      have hw'I2 : w' ∈ I2 := (w183finSp44_mem_I2).mpr
        ⟨hESC w' hw'E, (hEmem w').mp hw'E |>.2, hw'ne, hEinv w' hw'E⟩
      obtain ⟨g, hg, hgne⟩ := noE16 r' hr' hlen3 w' hw'I2 hw'NotSpan
      exact absurd (hEcomm g (hspanR'E g (w183finSp44_row_gen_mem_span2 hr' hg)) w' hw'E) hgne

private theorem w183finSp44_validB_oneE : validB oneE = true := by
  decide +kernel

private theorem w183finSp44_gmulE_oneE : gmulE oneE oneE = oneE := by
  decide +kernel

private lemma w183finSp44_commInv_inv {gens : List El} (hg : commInv gens = true) :
    ∀ g ∈ gens, gmulE g g = oneE := by
  intro g hgmem
  have h2 := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hg).1) g hgmem
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h2).2

private lemma w183finSp44_commInv_comm {gens : List El} (hg : commInv gens = true) :
    ∀ g ∈ gens, ∀ h ∈ gens, gmulE g h = gmulE h g := by
  intro g hgmem h hhmem
  have h2 := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hg).2) g hgmem
  exact beq_iff_eq.mp ((List.all_eq_true.mp h2) h hhmem)

private theorem w183finSp44_autOf_inj {x y : El} (hx : validB x = true) (hy : validB y = true)
    (h : autOf x = autOf y) : x = y := by
  have hx1 : x.1 < 4294967296 := (validB_iff.mp hx).1
  have hy1 : y.1 < 4294967296 := (validB_iff.mp hy).1
  have hx2 : x.2 < 4 := (validB_iff.mp hx).2.2
  have hy2 : y.2 < 4 := (validB_iff.mp hy).2.2
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data (K := GF4) (n := 2) (by norm_num) (by
    rw [Nat.card_eq_fintype_card]; decide)
  have hstruct := SpChain.exceptionalAut_structure (K := GF4) (f := 2) (by norm_num) hFr hord hzp
  have huniq := hstruct.2.1
  have hc : autCongr GF4 (autOf x) = autCongr GF4 (autOf y) := by rw [h]
  have hxr : autCongr GF4 (autOf x) =
      SpChain.spInner 2 GF4 (SpChain.antiSpEquiv GF4 (toS4 x.1 (validB_symp hx))) *
        SpChain.exceptionalAut GF4 ^ x.2 := by
    rw [autOf, dif_pos hx, map_mul, autCongr_conj, autCongr_pow, autCongr_minorAut]
  have hyr : autCongr GF4 (autOf y) =
      SpChain.spInner 2 GF4 (SpChain.antiSpEquiv GF4 (toS4 y.1 (validB_symp hy))) *
        SpChain.exceptionalAut GF4 ^ y.2 := by
    rw [autOf, dif_pos hy, map_mul, autCongr_conj, autCongr_pow, autCongr_minorAut]
  let qx : StatedSp 2 GF4 × Fin (2 * 2) :=
    (SpChain.antiSpEquiv GF4 (toS4 x.1 (validB_symp hx)), ⟨x.2, by omega⟩)
  let qy : StatedSp 2 GF4 × Fin (2 * 2) :=
    (SpChain.antiSpEquiv GF4 (toS4 y.1 (validB_symp hy)), ⟨y.2, by omega⟩)
  have hqx : autCongr GF4 (autOf x) =
      SpChain.spInner 2 GF4 qx.1 * SpChain.exceptionalAut GF4 ^ (qx.2 : ℕ) := by
    rw [hxr]
  have hqy : autCongr GF4 (autOf y) =
      SpChain.spInner 2 GF4 qy.1 * SpChain.exceptionalAut GF4 ^ (qy.2 : ℕ) := by
    rw [hyr]
  obtain ⟨p, -, huniqp⟩ := huniq (autCongr GF4 (autOf x))
  have hqxy : qx = qy := (huniqp qx hqx).trans (huniqp qy (hc.trans hqy)).symm
  have h1 : qx.1 = qy.1 := congrArg Prod.fst hqxy
  have h2fin : qx.2 = qy.2 := congrArg Prod.snd hqxy
  have h2 : x.2 = y.2 := by simpa [qx, qy] using congrArg Fin.val h2fin
  have htoS4 : toS4 x.1 (validB_symp hx) = toS4 y.1 (validB_symp hy) :=
    (SpChain.antiSpEquiv GF4).injective (by simpa [qx, qy] using h1)
  have hmat : decodeM x.1 = decodeM y.1 := by
    have hz := congrArg (fun z : S4 => ((z : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4)) htoS4
    simpa only [toS4_val] using hz
  exact Prod.ext (decodeM_inj hx1 hy1 hmat) h2

private lemma w183finSp44_gmulE_one_left {x : El} (hx : validB x = true) :
    gmulE oneE x = x := by
  refine w183finSp44_autOf_inj (validB_gmulE w183finSp44_validB_oneE hx) hx ?_
  rw [autOf_gmulE w183finSp44_validB_oneE hx, autOf_oneE, one_mul]

private lemma w183finSp44_gmulE_one_right {x : El} (hx : validB x = true) :
    gmulE x oneE = x := by
  refine w183finSp44_autOf_inj (validB_gmulE hx w183finSp44_validB_oneE) hx ?_
  rw [autOf_gmulE hx w183finSp44_validB_oneE, autOf_oneE, mul_one]

private lemma w183finSp44_gmulE_assoc {x y z : El} (hx : validB x = true)
    (hy : validB y = true) (hz : validB z = true) :
    gmulE (gmulE x y) z = gmulE x (gmulE y z) := by
  refine w183finSp44_autOf_inj (validB_gmulE (validB_gmulE hx hy) hz)
    (validB_gmulE hx (validB_gmulE hy hz)) ?_
  rw [autOf_gmulE (validB_gmulE hx hy) hz, autOf_gmulE hx hy,
    autOf_gmulE hx (validB_gmulE hy hz), autOf_gmulE hy hz, mul_assoc]

private def w183finSp44_Good (A : List El) : Prop :=
  (∀ x ∈ A, validB x = true) ∧
    (∀ x ∈ A, gmulE x x = oneE) ∧
      (∀ x ∈ A, ∀ y ∈ A, gmulE x y = gmulE y x) ∧
        ∀ x ∈ A, ∀ y ∈ A, gmulE x y ∈ A

private lemma w183finSp44_good_step (A : List El) (g : El) (hA : w183finSp44_Good A)
    (hAg : ∀ x ∈ A, gmulE x g = gmulE g x) (hgv : validB g = true)
    (hgi : gmulE g g = oneE) :
    w183finSp44_Good (A ++ A.map (fun x => gmulE x g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hxA | hxmap
    · exact hA.1 x hxA
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
      exact validB_gmulE (hA.1 a ha) hgv
  · intro x hx
    rcases List.mem_append.mp hx with hxA | hxmap
    · exact hA.2.1 x hxA
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
      have ha1 := hA.1 a ha
      calc
        gmulE (gmulE a g) (gmulE a g)
            = gmulE a (gmulE g (gmulE a g)) :=
              w183finSp44_gmulE_assoc ha1 hgv (validB_gmulE ha1 hgv)
        _ = gmulE a (gmulE (gmulE g a) g) := by
              rw [w183finSp44_gmulE_assoc hgv ha1 hgv]
        _ = gmulE a (gmulE (gmulE a g) g) := by rw [hAg a ha]
        _ = gmulE a (gmulE a (gmulE g g)) := by
              rw [← w183finSp44_gmulE_assoc ha1 hgv hgv]
        _ = gmulE a (gmulE a oneE) := by rw [hgi]
        _ = gmulE a a := by rw [w183finSp44_gmulE_one_right ha1]
        _ = oneE := hA.2.1 a ha
  · intro x hx y hy
    rcases List.mem_append.mp hx with hxA | hxmap
    · rcases List.mem_append.mp hy with hyA | hymap
      · exact hA.2.2.1 x hxA y hyA
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hymap
        have hb1 := hA.1 b hb
        calc
          gmulE x (gmulE b g) = gmulE (gmulE x b) g :=
            (w183finSp44_gmulE_assoc (hA.1 x hxA) hb1 hgv).symm
          _ = gmulE (gmulE b x) g := by rw [hA.2.2.1 x hxA b hb]
          _ = gmulE b (gmulE x g) := w183finSp44_gmulE_assoc hb1 (hA.1 x hxA) hgv
          _ = gmulE b (gmulE g x) := by rw [hAg x hxA]
          _ = gmulE (gmulE b g) x := (w183finSp44_gmulE_assoc hb1 hgv (hA.1 x hxA)).symm
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
      rcases List.mem_append.mp hy with hyA | hymap
      · have ha1 := hA.1 a ha
        calc
          gmulE (gmulE a g) y = gmulE a (gmulE g y) :=
            w183finSp44_gmulE_assoc ha1 hgv (hA.1 y hyA)
          _ = gmulE a (gmulE y g) := by rw [hAg y hyA]
          _ = gmulE (gmulE a y) g := (w183finSp44_gmulE_assoc ha1 (hA.1 y hyA) hgv).symm
          _ = gmulE (gmulE y a) g := by rw [hA.2.2.1 a ha y hyA]
          _ = gmulE y (gmulE a g) := w183finSp44_gmulE_assoc (hA.1 y hyA) ha1 hgv
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hymap
        have ha1 := hA.1 a ha
        have hb1 := hA.1 b hb
        calc
          gmulE (gmulE a g) (gmulE b g)
              = gmulE a (gmulE g (gmulE b g)) :=
                w183finSp44_gmulE_assoc ha1 hgv (validB_gmulE hb1 hgv)
          _ = gmulE a (gmulE (gmulE g b) g) := by
                rw [w183finSp44_gmulE_assoc hgv hb1 hgv]
          _ = gmulE a (gmulE (gmulE b g) g) := by rw [hAg b hb]
          _ = gmulE a (gmulE b (gmulE g g)) := by
                rw [← w183finSp44_gmulE_assoc hb1 hgv hgv]
          _ = gmulE a (gmulE b oneE) := by rw [hgi]
          _ = gmulE a b := by rw [w183finSp44_gmulE_one_right hb1]
          _ = gmulE b a := hA.2.2.1 a ha b hb
          _ = gmulE b (gmulE a oneE) := by rw [w183finSp44_gmulE_one_right ha1]
          _ = gmulE b (gmulE a (gmulE g g)) := by rw [hgi]
          _ = gmulE b (gmulE (gmulE a g) g) := by
                rw [← w183finSp44_gmulE_assoc ha1 hgv hgv]
          _ = gmulE b (gmulE (gmulE g a) g) := by rw [hAg a ha]
          _ = gmulE b (gmulE g (gmulE a g)) := by
                rw [w183finSp44_gmulE_assoc hgv ha1 hgv]
          _ = gmulE (gmulE b g) (gmulE a g) :=
                (w183finSp44_gmulE_assoc hb1 hgv (validB_gmulE ha1 hgv)).symm
  · intro x hx y hy
    rcases List.mem_append.mp hx with hxA | hxmap
    · rcases List.mem_append.mp hy with hyA | hymap
      · exact List.mem_append.mpr (Or.inl (hA.2.2.2 x hxA y hyA))
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hymap
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨gmulE x b, hA.2.2.2 x hxA b hb,
            w183finSp44_gmulE_assoc (hA.1 x hxA) (hA.1 b hb) hgv⟩))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
      rcases List.mem_append.mp hy with hyA | hymap
      · have ha1 := hA.1 a ha
        have hy1 := hA.1 y hyA
        have heq : gmulE (gmulE a g) y = gmulE (gmulE a y) g := by
          calc
            gmulE (gmulE a g) y = gmulE a (gmulE g y) :=
              w183finSp44_gmulE_assoc ha1 hgv hy1
            _ = gmulE a (gmulE y g) := by rw [hAg y hyA]
            _ = gmulE (gmulE a y) g := (w183finSp44_gmulE_assoc ha1 hy1 hgv).symm
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨gmulE a y, hA.2.2.2 a ha y hyA, heq.symm⟩))
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hymap
        have ha1 := hA.1 a ha
        have hb1 := hA.1 b hb
        have heq : gmulE (gmulE a g) (gmulE b g) = gmulE a b := by
          calc
            gmulE (gmulE a g) (gmulE b g)
                = gmulE a (gmulE g (gmulE b g)) :=
                  w183finSp44_gmulE_assoc ha1 hgv (validB_gmulE hb1 hgv)
            _ = gmulE a (gmulE (gmulE g b) g) := by
                  rw [w183finSp44_gmulE_assoc hgv hb1 hgv]
            _ = gmulE a (gmulE (gmulE b g) g) := by rw [hAg b hb]
            _ = gmulE a (gmulE b (gmulE g g)) := by
                  rw [← w183finSp44_gmulE_assoc hb1 hgv hgv]
            _ = gmulE a (gmulE b oneE) := by rw [hgi]
            _ = gmulE a b := by rw [w183finSp44_gmulE_one_right hb1]
        exact List.mem_append.mpr (Or.inl (by rw [heq]; exact hA.2.2.2 a ha b hb))

private lemma w183finSp44_foldl_mono (l : List El) :
    ∀ A B : List El, A ⊆ B →
      l.foldl (fun L g => L ++ L.map fun x => gmulE x g) A ⊆
        l.foldl (fun L g => L ++ L.map fun x => gmulE x g) B := by
  induction l with
  | nil => intro A B h; simpa
  | cons g gs ih =>
      intro A B h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ fun x hx =>
        match List.mem_append.mp hx with
        | Or.inl hxA => List.mem_append.mpr (Or.inl (h hxA))
        | Or.inr hxmap =>
            match List.mem_map.mp hxmap with
            | ⟨a, ha, hfa⟩ => List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨a, h ha, hfa⟩))

private lemma w183finSp44_subset_foldl (l : List El) (A : List El) :
    A ⊆ l.foldl (fun L g => L ++ L.map fun x => gmulE x g) A := by
  induction l generalizing A with
  | nil => exact fun _ hx => hx
  | cons g gs ih =>
      rw [List.foldl_cons]
      exact fun x hx => ih (A ++ A.map (fun x => gmulE x g))
        (List.mem_append.mpr (Or.inl hx))

private lemma w183finSp44_foldl_good (gens A : List El) (hA : w183finSp44_Good A)
    (hcommA : ∀ x ∈ A, ∀ g ∈ gens, gmulE x g = gmulE g x)
    (hvalid : ∀ g ∈ gens, validB g = true)
    (hinv : ∀ g ∈ gens, gmulE g g = oneE)
    (hcomm : ∀ g ∈ gens, ∀ h ∈ gens, gmulE g h = gmulE h g) :
    w183finSp44_Good (gens.foldl (fun l g => l ++ l.map fun x => gmulE x g) A) := by
  induction gens generalizing A with
  | nil => simpa using hA
  | cons g gs ih =>
      rw [List.foldl_cons]
      apply ih
      · exact w183finSp44_good_step A g hA (fun x hx => hcommA x hx g (by simp))
          (hvalid g (by simp)) (hinv g (by simp))
      · intro x hx h hgs
        rcases List.mem_append.mp hx with hxA | hxmap
        · exact hcommA x hxA h (List.mem_cons_of_mem g hgs)
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
          have ha1 := hA.1 a ha
          have hgv := hvalid g (by simp)
          have hhv := hvalid h (List.mem_cons_of_mem g hgs)
          calc
            gmulE (gmulE a g) h = gmulE a (gmulE g h) :=
              w183finSp44_gmulE_assoc ha1 hgv hhv
            _ = gmulE a (gmulE h g) := by
              rw [hcomm g (by simp) h (List.mem_cons_of_mem g hgs)]
            _ = gmulE (gmulE a h) g := (w183finSp44_gmulE_assoc ha1 hhv hgv).symm
            _ = gmulE (gmulE h a) g := by
              rw [hcommA a ha h (List.mem_cons_of_mem g hgs)]
            _ = gmulE h (gmulE a g) := w183finSp44_gmulE_assoc hhv ha1 hgv
      · exact fun h hh => hvalid h (List.mem_cons_of_mem g hh)
      · exact fun h hh => hinv h (List.mem_cons_of_mem g hh)
      · exact fun h hh k hk => hcomm h (List.mem_cons_of_mem g hh) k (List.mem_cons_of_mem g hk)

private lemma w183finSp44_span2_good (gens : List El)
    (hvalid : ∀ g ∈ gens, validB g = true)
    (hinv : ∀ g ∈ gens, gmulE g g = oneE)
    (hcomm : ∀ g ∈ gens, ∀ h ∈ gens, gmulE g h = gmulE h g) :
    w183finSp44_Good (span2 gens) := by
  have h0 : w183finSp44_Good [oneE] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx; rw [List.mem_singleton.mp hx]; exact w183finSp44_validB_oneE
    · intro x hx; rw [List.mem_singleton.mp hx]; exact w183finSp44_gmulE_oneE
    · intro x hx y hy; rw [List.mem_singleton.mp hx, List.mem_singleton.mp hy]
    · intro x hx y hy; rw [List.mem_singleton.mp hx, List.mem_singleton.mp hy]
      exact List.mem_singleton_self oneE
  have hcommA : ∀ x ∈ [oneE], ∀ g ∈ gens, gmulE x g = gmulE g x := by
    intro x hx g hg
    rw [List.mem_singleton.mp hx, w183finSp44_gmulE_one_left (hvalid g hg),
      w183finSp44_gmulE_one_right (hvalid g hg)]
  simpa [span2] using w183finSp44_foldl_good gens [oneE] h0 hcommA hvalid hinv hcomm

private lemma w183finSp44_mem_span2_self {gens : List El} (hvalid : ∀ g ∈ gens, validB g = true)
    {g : El} (hg : g ∈ gens) : g ∈ span2 gens := by
  induction gens with
  | nil => simp at hg
  | cons h hs ih =>
      rw [span2, List.foldl_cons]
      rcases List.mem_cons.mp hg with hgh | hg'
      · rw [hgh]
        refine w183finSp44_subset_foldl hs ([oneE] ++ [oneE].map (fun x => gmulE x h)) ?_
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨oneE, by simp, by rw [w183finSp44_gmulE_one_left (hvalid h (by simp))]⟩))
      · exact w183finSp44_foldl_mono hs [oneE] ([oneE] ++ [oneE].map (fun x => gmulE x h))
          (fun x hx => List.mem_append.mpr (Or.inl hx))
          (by simpa [span2] using ih (fun x hx => hvalid x (by simp [hx])) hg')

private lemma w183finSp44_foldl_autOf_mem (gens A : List El) (H : Subgroup (MulAut S4))
    (hA : ∀ x ∈ A, autOf x ∈ H) (hAvalid : ∀ x ∈ A, validB x = true)
    (hgH : ∀ g ∈ gens, autOf g ∈ H) (hgvalid : ∀ g ∈ gens, validB g = true)
    (hcommgens : ∀ g ∈ gens, ∀ h ∈ gens, gmulE g h = gmulE h g)
    (hcommA : ∀ x ∈ A, ∀ g ∈ gens, gmulE x g = gmulE g x) :
    ∀ x ∈ gens.foldl (fun l g => l ++ l.map fun x => gmulE x g) A, autOf x ∈ H := by
  induction gens generalizing A with
  | nil => simpa using hA
  | cons g gs ih =>
      rw [List.foldl_cons]
      apply ih
      · intro x hx
        rcases List.mem_append.mp hx with hxA | hxmap
        · exact hA x hxA
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
          rw [autOf_gmulE (hAvalid a ha) (hgvalid g (by simp))]
          exact H.mul_mem (hA a ha) (hgH g (by simp))
      · intro x hx
        rcases List.mem_append.mp hx with hxA | hxmap
        · exact hAvalid x hxA
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
          exact validB_gmulE (hAvalid a ha) (hgvalid g (by simp))
      · exact fun h hh => hgH h (List.mem_cons_of_mem g hh)
      · exact fun h hh => hgvalid h (List.mem_cons_of_mem g hh)
      · exact fun h hh k hk => hcommgens h (List.mem_cons_of_mem g hh) k
          (List.mem_cons_of_mem g hk)
      · intro x hx h hgs
        rcases List.mem_append.mp hx with hxA | hxmap
        · exact hcommA x hxA h (List.mem_cons_of_mem g hgs)
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hxmap
          have ha1 := hAvalid a ha
          have hgv := hgvalid g (by simp)
          have hhv := hgvalid h (List.mem_cons_of_mem g hgs)
          calc
            gmulE (gmulE a g) h = gmulE a (gmulE g h) :=
              w183finSp44_gmulE_assoc ha1 hgv hhv
            _ = gmulE a (gmulE h g) := by
              rw [hcommgens g (by simp) h (List.mem_cons_of_mem g hgs)]
            _ = gmulE (gmulE a h) g := (w183finSp44_gmulE_assoc ha1 hhv hgv).symm
            _ = gmulE (gmulE h a) g := by
              rw [hcommA a ha h (List.mem_cons_of_mem g hgs)]
            _ = gmulE h (gmulE a g) := w183finSp44_gmulE_assoc hhv ha1 hgv

private lemma w183finSp44_span2_autOf_mem {gens : List El} (hg : commInv gens = true)
    (hv : ∀ x ∈ gens, validB x = true) {x : El} (hx : x ∈ span2 gens) :
    autOf x ∈ Subgroup.closure (autOf '' {y | y ∈ gens}) := by
  refine w183finSp44_foldl_autOf_mem gens [oneE]
    (Subgroup.closure (autOf '' {y | y ∈ gens}))
    (by intro z hz; rw [List.mem_singleton.mp hz, autOf_oneE]; exact one_mem _)
    (by intro z hz; rw [List.mem_singleton.mp hz]; exact w183finSp44_validB_oneE)
    (fun g hgmem => Subgroup.subset_closure (Set.mem_image_of_mem autOf hgmem)) hv
    (w183finSp44_commInv_comm hg)
    (by intro z hz g hgmem; rw [List.mem_singleton.mp hz,
      w183finSp44_gmulE_one_left (hv g hgmem), w183finSp44_gmulE_one_right (hv g hgmem)])
    x (by simpa [span2] using hx)

theorem mem_closure_autOf_iff {gens : List El} (hg : commInv gens = true)
    (hv : ∀ x ∈ gens, validB x = true) (α : MulAut S4) :
    α ∈ Subgroup.closure (autOf '' {x | x ∈ gens}) ↔ ∃ x ∈ span2 gens, autOf x = α := by
  have hgood := w183finSp44_span2_good gens hv (w183finSp44_commInv_inv hg)
    (w183finSp44_commInv_comm hg)
  constructor
  · intro hα
    refine Subgroup.closure_induction (p := fun α _ => ∃ x ∈ span2 gens, autOf x = α)
      ?_ ?_ ?_ ?_ hα
    · intro a ha
      obtain ⟨g, hgmem, rfl⟩ := ha
      exact ⟨g, w183finSp44_mem_span2_self hv hgmem, rfl⟩
    · exact ⟨oneE, w183finSp44_oneE_mem_span2 gens, autOf_oneE⟩
    · intro a b ha hb pa pb
      obtain ⟨x, hx, rfl⟩ := pa
      obtain ⟨y, hy, rfl⟩ := pb
      exact ⟨gmulE x y, hgood.2.2.2 x hx y hy,
        autOf_gmulE (hgood.1 x hx) (hgood.1 y hy)⟩
    · intro a ha pa
      obtain ⟨x, hx, rfl⟩ := pa
      refine ⟨x, hx, ?_⟩
      have h2 : autOf x * autOf x = 1 := by
        rw [← autOf_gmulE (hgood.1 x hx) (hgood.1 x hx), hgood.2.1 x hx, autOf_oneE]
      rw [inv_eq_of_mul_eq_one_right h2]
  · rintro ⟨x, hx, rfl⟩
    exact w183finSp44_span2_autOf_mem hg hv hx

theorem mem_outerRep_iff {c : Nat} (hc : c < 4) (α : MulAut S4) :
    α ∈ outerRep c ↔ ∃ x ∈ span2 (outerRepGens.getD c []), autOf x = α :=
  mem_closure_autOf_iff (reps_commInv c hc).1 (reps_commInv c hc).2 α

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
