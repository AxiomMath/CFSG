module

public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.ChainArrays

abbrev GJ : Type := ↥CFSG.ComponentClassification.J2Cover.P

abbrev jBase : Array ℕ := (([0, 4, 3] : List (Fin 315)).map Fin.val).toArray

theorem jBase_eq : jBase = autBase := autBase_eq

theorem chainArrays_aut : ChainArrays autChain (autStrong.extract 0 2) autStrong jBase autWords :=
  ofArrays_chainArrays autChain_ok

theorem chainFacts_aut :
    ChainCheckFacts 315 (autStrong.extract 0 2) autStrong jBase autWords 4 :=
  chainCheckFacts autChain_ok

theorem baseCount_aut : autChain.baseCount = 3 := rfl

theorem autLevels_eq : autLevels = rawLevels 315 autStrong jBase := by
  rw [autLevels, jBase_eq]

theorem lev_sizes : (lev 315 autStrong jBase 0).pts.size = 315 ∧
    (lev 315 autStrong jBase 1).pts.size = 160 ∧ (lev 315 autStrong jBase 2).pts.size = 12 := by
  have h := autChain_check.2
  rw [rawOrbitSizes, ← jBase_eq] at h
  have hsz : (rawLevels 315 autStrong jBase).size = 3 := by
    have := congrArg List.length h
    simpa using this
  have hg : ∀ i (hi : i < 3), (lev 315 autStrong jBase i).pts.size =
      ([315, 160, 12] : List ℕ)[i] := by
    intro i hi
    have := congrArg (fun L : List ℕ => L[i]?) h
    simp only [List.getElem?_map, Array.getElem?_toList] at this
    rw [lev, getElem!_pos _ i (by omega)]
    rw [Array.getElem?_eq_getElem (by omega)] at this
    simp only [Option.map_some] at this
    rw [List.getElem?_eq_getElem (by simp; omega)] at this
    exact Option.some_injective _ this
  exact ⟨hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num)⟩

@[expose] noncomputable def cperm (a b c : ℕ) : Equiv.Perm (Fin 315) :=
  levT 315 autStrong jBase 0 a * levT 315 autStrong jBase 1 b * levT 315 autStrong jBase 2 c

theorem rep_prod3 {a b c : ℕ} (ha : a < 315) (hb : b < 160) (hc : c < 12) :
    Rep 315 (prod3 315 autLevels a b c) (cperm a b c) := by
  intro p
  rw [prod3, getElem!_ofFn_nat _ p.2, autLevels_eq]
  exact (chainArrays_aut.prod3_apply chainFacts_aut (by rw [baseCount_aut])
    (by rw [lev_sizes.1]; exact ha) (by rw [lev_sizes.2.1]; exact hb)
    (by rw [lev_sizes.2.2]; exact hc) p).symm

theorem exists_cperm (g : GJ) : ∃ a < 315, ∃ b < 160, ∃ c < 12, cperm a b c = g.1 := by
  have hg : (g : Equiv.Perm (Fin 315)) ∈ autChain.originalSubgroup := by
    rw [autChain_originalSubgroup]
    exact g.2
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := chainArrays_aut.exists_prod3 (by norm_num) autChain_ok
    (by rw [baseCount_aut]) (fun i hi hi' => by rw [baseCount_aut] at hi'; omega) hg
  rw [lev_sizes.1] at ha
  rw [lev_sizes.2.1] at hb
  rw [lev_sizes.2.2] at hc
  exact ⟨a, ha, b, hb, c, hc, h⟩

theorem exists_rep_of_check {pr : Array ℕ → Bool}
    (h : allLt 315 (fun a => allLt 160 fun b => allLt 12 fun c =>
      pr (prod3 315 autLevels a b c)) = true) (g : GJ) :
    ∃ t, Rep 315 t g.1 ∧ pr t = true := by
  obtain ⟨a, ha, b, hb, c, hc, hg⟩ := exists_cperm g
  exact ⟨prod3 315 autLevels a b c, hg ▸ rep_prod3 ha hb hc,
    allLt_spec (allLt_spec (allLt_spec h ha) hb) hc⟩

@[expose] noncomputable def elA (t : Array ℕ) (h : validA 315 t = true ∧ inP t = true) : GJ :=
  ⟨permOfArr 315 t, (mem_P_iff (rep_of_validA h.1)).1 h.2⟩

theorem rep_elA {t : Array ℕ} (h : validA 315 t = true ∧ inP t = true) :
    Rep 315 t (elA t h).1 :=
  rep_of_validA h.1

theorem elA_eq_iff {t : Array ℕ} (h : validA 315 t = true ∧ inP t = true) {g : GJ}
    (hg : Rep 315 t g.1) : elA t h = g :=
  Subtype.ext ((rep_elA h).unique hg)

@[expose] noncomputable def subOf (gs : Array (Array ℕ)) : Subgroup GJ :=
  (Subgroup.closure (permsA 315 gs)).subgroupOf CFSG.ComponentClassification.J2Cover.P

theorem mem_subOf {gs : Array (Array ℕ)} {g : GJ} :
    g ∈ subOf gs ↔ (g : Equiv.Perm (Fin 315)) ∈ Subgroup.closure (permsA 315 gs) :=
  Subgroup.mem_subgroupOf

theorem closure_le_P {gs : Array (Array ℕ)}
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) :
    Subgroup.closure (permsA 315 gs) ≤ CFSG.ComponentClassification.J2Cover.P := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (mem_P_iff (rep_of_validA (h k hk).1)).1 (h k hk).2

theorem card_subOf {gs : Array (Array ℕ)} {ps : List ℕ} {c : CFSG.Monster.B.Fischer.ArrCert}
    (hps : ∀ p ∈ ps, p < 315) (henum : enumOK 315 gs ps c = true)
    (h : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true) :
    Nat.card (subOf gs) = c.pts.size := by
  rw [subOf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (closure_le_P h)).toEquiv]
  exact (enumOK_spec hps henum).2.1

theorem mem_subOf_of_any {gs : Array (Array ℕ)} {ps : List ℕ} {c : CFSG.Monster.B.Fischer.ArrCert}
    (hps : ∀ p ∈ ps, p < 315) (henum : enumOK 315 gs ps c = true) {t : Array ℕ} {g : GJ}
    (ht : Rep 315 t g.1) (hany : c.pts.toList.any (eqA 315 t) = true) : g ∈ subOf gs :=
  mem_subOf.2 (enumOK_mem_of_any hps henum ht hany)

theorem exists_rep_subOf {gs : Array (Array ℕ)} {ps : List ℕ} {c : CFSG.Monster.B.Fischer.ArrCert}
    (hps : ∀ p ∈ ps, p < 315) (henum : enumOK 315 gs ps c = true) {g : GJ}
    (hg : g ∈ subOf gs) : ∃ i < c.pts.size, Rep 315 c.pts[i]! g.1 :=
  enumOK_exists_rep hps henum (mem_subOf.1 hg)

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
