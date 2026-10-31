
module

public import CFSG.Quasithin.H13.HSLocEnum
public import CFSG.RankThree.Native.HSMcLSmall

@[expose] public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native

abbrev PG : Type := ↥hs100P

theorem mem_hs100A : hs100A ∈ hs100P := by
  unfold hs100P
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_hs100B : hs100B ∈ hs100P := by
  unfold hs100P
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

noncomputable def ga : PG := ⟨hs100A, mem_hs100A⟩

noncomputable def gb : PG := ⟨hs100B, mem_hs100B⟩

theorem size_hs100Arr (k : ℕ) : (hs100Arr k).size = 100 := by
  simp [hs100Arr, CFSG.Monster.B.Fischer.hexTable3]

theorem T_eq_of_smul {Γ : Type} [Group Γ] [MulAction Γ (Fin 100)] [FaithfulSMul Γ (Fin 100)] {g : Γ}
    {t : Array ℕ}
    (ht : t.size = 100) (hg : ∀ i : Fin 100, t[(i : ℕ)]! = ((g • i : Fin 100) : ℕ)) : T g = t := by
  apply Array.ext
  · rw [T_size, ht]
  · intro i h1 h2
    have hi : i < 100 := by rwa [T_size] at h1
    have hrep := hg ⟨i, hi⟩
    rw [getElem!_pos t i h2] at hrep
    rw [T_getElem g h1]
    exact (act_eq g ⟨i, hi⟩).trans hrep.symm

theorem T_ga : T ga = ta := by
  refine T_eq_of_smul (size_hs100Arr 0) fun i => ?_
  rw [Subgroup.smul_def, show ((ga : PG) : Equiv.Perm (Fin 100)) = hs100A from rfl,
    Equiv.Perm.smul_def]
  exact rep_hs100A i

theorem T_gb : T gb = tb := by
  refine T_eq_of_smul (size_hs100Arr 1) fun i => ?_
  rw [Subgroup.smul_def, show ((gb : PG) : Equiv.Perm (Fin 100)) = hs100B from rfl,
    Equiv.Perm.smul_def]
  exact rep_hs100B i

theorem AB_get0 : AB.getD 0 #[] = ta := rfl

theorem AB_get1 : AB.getD 1 #[] = tb := rfl

theorem AB_get2 : AB.getD 2 #[] = invT ta := rfl

theorem AB_get3 : AB.getD 3 #[] = invT tb := rfl

theorem ABOK_ab : ABOK 100 AB ga gb := by
  intro l hl q hq
  have hl4 : l < 4 := hl
  interval_cases l
  · have h := img_T ga q
    rw [T_ga] at h
    rw [AB_get0]
    exact h
  · have h := img_T gb q
    rw [T_gb] at h
    rw [AB_get1]
    exact h
  · have h := img_T ga⁻¹ q
    rw [T_inv, T_ga] at h
    rw [AB_get2]
    exact h
  · have h := img_T gb⁻¹ q
    rw [T_inv, T_gb] at h
    rw [AB_get3]
    exact h

theorem T_wAB {w : List ℕ} (hw : ∀ l ∈ w, l < 4) :
    T (wAB ga gb w) = tabW 100 AB w := by
  symm
  apply eq_T_of_img
  · simp [tabW]
  · intro q hq
    rw [img_tabW AB w hq, act_wAB ABOK_ab hw hq]

noncomputable def gensOf (ws : List (List ℕ)) : List PG := ws.map (wAB ga gb)

theorem subSpec_words {ws : List (List ℕ)}
    (hws : ∀ w ∈ ws, ∀ l ∈ w, l < 4) {cap N : ℕ} (h : subEnumOK 100 B100 N cap (tabsOf ws) = true) :
    SubSpec (Subgroup.closure {x | x ∈ gensOf ws})
      (enumTabs (tabsOf ws) (bfsEnumL 100 B100 (tabsOf ws) cap) N) N := by
  apply subSpec_of_enum _ _ h
  · simp [gensOf, tabsOf]
  · intro t ht p hp
    have ht' : t < ws.length := by simpa [tabsOf] using ht
    have hw := hws ws[t] (List.getElem_mem ht')
    have e1 : (tabsOf ws).getD t #[] = tabW 100 AB ws[t] := by
      simp [tabsOf, Array.getD_eq_getD_getElem?, ht']
    have e2 : (gensOf ws).getD t 1 = wAB ga gb ws[t] := by
      simp [gensOf, List.getD_eq_getElem?_getD, ht']
    rw [e1, e2, ← T_wAB hw, img_T]

noncomputable def Sg : Subgroup PG := Subgroup.closure {x | x ∈ gensOf sWords}

noncomputable def S5g : Subgroup PG := Subgroup.closure {x | x ∈ gensOf s5Words}

noncomputable def Mg : Subgroup PG := Subgroup.closure {x | x ∈ gensOf mWords}

theorem sWords_lt : ∀ w ∈ sWords, ∀ l ∈ w, l < 4 := by decide +kernel

theorem s5Words_lt : ∀ w ∈ s5Words, ∀ l ∈ w, l < 4 := by decide +kernel

theorem mWords_lt : ∀ w ∈ mWords, ∀ l ∈ w, l < 4 := by decide +kernel

theorem kWords_lt : ∀ w ∈ kWords, ∀ l ∈ w, l < 4 := by decide +kernel

theorem act_val (z : PG) (q : Fin 100) : act 100 z q.val = ((z : Equiv.Perm (Fin 100)) q).val :=
  act_eq z q

theorem fixF0_iff_perm {E : Subgroup PG} {X : PG} :
    (∀ q < 100, ((∀ z ∈ E, act 100 z q = q) ↔ q ∈ F0.map (act 100 X))) ↔
      ∀ q : Fin 100, (∀ z ∈ E.map hs100P.subtype, z q = q) ↔
        ∃ f : Fin 100, (f : ℕ) ∈ F0 ∧ (X : Equiv.Perm (Fin 100)) f = q := by
  have hF : ∀ f ∈ F0, f < 100 := by decide
  have h1 : ∀ q : Fin 100, (∀ z ∈ E, act 100 z q.val = q.val) ↔
      ∀ z ∈ E.map hs100P.subtype, z q = q := by
    intro q
    constructor
    · intro h z hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      exact Fin.ext ((act_val z' q).symm.trans (h z' hz'))
    · intro h z hz
      rw [act_val]
      exact congrArg Fin.val (h _ (Subgroup.mem_map_of_mem _ hz))
  have h2 : ∀ q : Fin 100, q.val ∈ F0.map (act 100 X) ↔
      ∃ f : Fin 100, (f : ℕ) ∈ F0 ∧ (X : Equiv.Perm (Fin 100)) f = q := by
    intro q
    rw [List.mem_map]
    constructor
    · rintro ⟨f, hf, he⟩
      refine ⟨⟨f, hF f hf⟩, hf, Fin.ext ?_⟩
      rw [← he]
      exact (act_val X ⟨f, hF f hf⟩).symm
    · rintro ⟨f, hf, he⟩
      exact ⟨f, hf, by rw [act_val, he]⟩
  constructor
  · intro h q
    rw [← h1, ← h2]
    exact h q.val q.isLt
  · intro h q hq
    have := h ⟨q, hq⟩
    rw [← h1, ← h2] at this
    exact this

end CFSG.Quasithin.H13.LocDbl.HSLoc
