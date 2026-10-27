module

public import CFSG.Monster.B.E6.StdF4HeckePanel
public import CFSG.Monster.B.E6.StdF4Points
public import Certificates.Certificate16029
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

open _root_.Classical in
@[expose] def panelRest
    (i : Fin 4) (a : stdChamber) : Finset stdChamber :=
  have : Fintype stdChamber := Fintype.ofFinite _
  Finset.univ.filter fun c => c ∈ panel ncs stdDistance i a ∧ c ≠ a

theorem mem_panelRest
    {i : Fin 4} {a c : stdChamber} :
    c ∈ panelRest i a ↔ c ∈ panel ncs stdDistance i a ∧ c ≠ a := by
  classical
  simp [panelRest]

theorem card_panelRest
    (i : Fin 4) (a : stdChamber) :
    (panelRest i a).card = E6Folded.letterWeight i := by
  have hfin : (panel ncs stdDistance i a).Finite := Set.toFinite _
  have hcoe : (panelRest i a : Set stdChamber) = panel ncs stdDistance i a \ {a} := by
    ext c
    simp [mem_panelRest]
  have h' : ((panel ncs stdDistance i a).ncard : ℕ∞) = E6Folded.letterWeight i + 1 := by
    rw [hfin.cast_ncard_eq, hpanel]
  have h'' : (panel ncs stdDistance i a).ncard = E6Folded.letterWeight i + 1 := by
    exact_mod_cast h'
  have ha : a ∈ panel ncs stdDistance i a := self_mem_residue _ _
  rw [← Set.ncard_coe_finset, hcoe, Set.ncard_sdiff_singleton_of_mem ha, h'',
    Nat.add_sub_cancel]

theorem hStep_getD (k : Fin 4) (F : List ℕ) {γ : ℕ} (hγ : γ < 24) :
    (hStep k F).getD γ 0 =
      if E6Folded.gidx k γ = γ then E6Folded.letterWeight k * F.getD γ 0
      else if plen (E6Folded.gidx k γ) = plen γ + 1 then
        E6Folded.letterWeight k * F.getD (E6Folded.gidx k γ) 0
      else F.getD (E6Folded.gidx k γ) 0 + (E6Folded.letterWeight k - 1) * F.getD γ 0 := by
  rw [hStep, List.getD_eq_getElem _ _ (by simp [hγ]), List.getElem_map, List.getElem_range]

theorem sum_panel_rho
    (F : List ℕ) (a b : stdChamber) (i : Fin 4) :
    ∑ c ∈ panelRest i a, F.getD (rho c b) 0 = (hStep i F).getD (rho a b) 0 := by
  classical
  obtain ⟨hfix, hnear, hfar⟩ := rho_panel a b i
  rw [hStep_getD i F (rho a b).2]
  have hcard := card_panelRest i a
  rcases plen_trichotomy i (rho a b) (rho a b).2 with h | h | h
  · rw [ite_eq_left h, Finset.sum_congr rfl fun c hc => by
      rw [hfix h c (mem_panelRest.1 hc).1], Finset.sum_const, hcard, smul_eq_mul]
  · have hne : E6Folded.gidx i (rho a b) ≠ rho a b := fun e => by rw [e] at h; omega
    rw [ite_eq_right hne, ite_eq_left h, Finset.sum_congr rfl fun c hc => by
      rw [hnear hne h c (mem_panelRest.1 hc).1 (mem_panelRest.1 hc).2], Finset.sum_const, hcard,
      smul_eq_mul]
  · have hne : E6Folded.gidx i (rho a b) ≠ rho a b := fun e => by rw [e] at h; omega
    have hne' : ¬plen (E6Folded.gidx i (rho a b)) = plen (rho a b) + 1 := by omega
    rw [ite_eq_right hne, ite_eq_right hne']
    obtain ⟨c₀, hc₀, hc₀a, hρ₀, hoth⟩ := hfar hne h
    have hmem : c₀ ∈ panelRest i a := mem_panelRest.2 ⟨hc₀, hc₀a⟩
    rw [← Finset.add_sum_erase _ _ hmem, hρ₀, Finset.sum_congr rfl fun c hc => by
      rw [hoth c (mem_panelRest.1 (Finset.mem_of_mem_erase hc)).1
        (mem_panelRest.1 (Finset.mem_of_mem_erase hc)).2 (Finset.ne_of_mem_erase hc)],
      Finset.sum_const, Finset.card_erase_of_mem hmem, hcard, smul_eq_mul]

open _root_.Classical in
@[expose] def ptChamber
    (z : stdGroup) : stdChamber :=
  if h : z ∈ rootClass then (((mem_rootClass_iff z).1 h).choose : stdChamber) else c₀

theorem chamberRoot_ptChamber
    {z : stdGroup} (hz : z ∈ rootClass) :
    chamberRoot (ptChamber z) = z := by
  rw [ptChamber, dite_eq_left hz, chamberRoot_mk]
  exact ((mem_rootClass_iff z).1 hz).choose_spec

theorem chamberRoot_mem_rootClass
    (c : stdChamber) : chamberRoot c ∈ rootClass := by
  induction c using QuotientGroup.induction_on with
  | H g => exact (mem_rootClass_iff _).2 ⟨g, rfl⟩

theorem mem_residue_of_chamberRoot_eq
    {c d : stdChamber} (h : chamberRoot c = chamberRoot d) :
    c ∈ residue ncs stdDistance firstJ d := by
  rw [← (chamberRoot_eq_iff c d).1 h]
  exact self_mem_residue _ _

@[expose] def rhoPt
    (x : stdChamber) (z : stdGroup) : Fin 24 := rho x (ptChamber z)

theorem rhoPt_eq
    {x c : stdChamber} {z : stdGroup} (hz : z ∈ rootClass)
    (hc : chamberRoot c = z) : rhoPt x z = rho x c :=
  (rho_eq_of_mem_residue (mem_residue_of_chamberRoot_eq
    (hc.trans (chamberRoot_ptChamber hz).symm))).symm

@[expose] def relPt
    (y z : stdGroup) : ℕ := lidx (rhoPt (ptChamber y) z)

theorem relPt_eq
    {y z : stdGroup} (hy : y ∈ rootClass) (hz : z ∈ rootClass) {c d : stdChamber}
    (hc : chamberRoot c = y) (hd : chamberRoot d = z) : relPt y z = lidx (rho c d) := by
  rw [relPt, rhoPt_eq hz hd]
  exact lidx_rho_eq_of_mem_residue (mem_residue_of_chamberRoot_eq
    ((chamberRoot_ptChamber hy).trans hc.symm))

theorem rhoPt_eq_23_iff
    (x : stdChamber) {z : stdGroup} (hz : z ∈ rootClass) :
    (rhoPt x z : ℕ) = 23 ↔ z = chamberRoot x := by
  rw [rhoPt, rho_eq_23_iff]
  constructor
  · intro h
    rw [← chamberRoot_ptChamber hz]
    exact (chamberRoot_eq_iff _ _).2 (residue_eq_of_mem hδ h)
  · intro h
    have e : chamberRoot (ptChamber z) = chamberRoot x := (chamberRoot_ptChamber hz).trans h
    rw [(chamberRoot_eq_iff _ _).1 e.symm]
    exact self_mem_residue _ _

theorem plen_eq_zero_iff : ∀ β < 24, plen β = 0 → β = 23 :=
  Certificates.certificate16029

theorem gidx_ne_of_plen {k : Fin 4} {β : ℕ} (h : plen (E6Folded.gidx k β) + 1 = plen β) :
    E6Folded.gidx k β ≠ β := fun e => by rw [e] at h; omega

open _root_.Classical in
theorem ncard_rhoPt_eq_sum
    (a : stdChamber) {k : Fin 4} {β : ℕ} (hβ : β < 24)
    (hlen : plen (E6Folded.gidx k β) + 1 = plen β) (C : stdGroup → Prop) :
    {z | z ∈ rootClass ∧ (rhoPt a z : ℕ) = β ∧ C z}.ncard =
      ∑ c ∈ panelRest k a,
        {z | z ∈ rootClass ∧ (rhoPt c z : ℕ) = E6Folded.gidx k β ∧ C z}.ncard := by
  have : Fintype stdGroup := Fintype.ofFinite _
  set β' := E6Folded.gidx k β with hβ'
  have hne : β' ≠ β := gidx_ne_of_plen hlen
  have hββ : E6Folded.gidx k β' = β := gidx_gidx k β hβ
  let f : stdGroup → stdChamber := fun z =>
    if h : ∃ c, c ∈ panelRest k a ∧ (rhoPt c z : ℕ) = β' then h.choose else a
  have hfar : ∀ z, (rhoPt a z : ℕ) = β → ∃ c₀ ∈ panel ncs stdDistance k a, c₀ ≠ a ∧
      (rhoPt c₀ z : ℕ) = β' ∧ ∀ c ∈ panel ncs stdDistance k a, c ≠ a → c ≠ c₀ →
        rhoPt c z = rhoPt a z := by
    intro z hz
    have h1 : E6Folded.gidx k (rhoPt a z) ≠ rhoPt a z := by rw [hz]; exact hne
    have h2 : plen (E6Folded.gidx k (rhoPt a z)) + 1 = plen (rhoPt a z) := by rw [hz]; exact hlen
    obtain ⟨c₀, hc₀, hc₀a, hρ, hoth⟩ := (rho_panel a (ptChamber z) k).2.2 h1 h2
    exact ⟨c₀, hc₀, hc₀a, by rw [rhoPt, hρ]; exact congrArg _ hz, hoth⟩
  have hf : ∀ z, (rhoPt a z : ℕ) = β → f z ∈ panelRest k a ∧ (rhoPt (f z) z : ℕ) = β' := by
    intro z hz
    obtain ⟨c₀, hc₀, hc₀a, hρ, -⟩ := hfar z hz
    have hex : ∃ c, c ∈ panelRest k a ∧ (rhoPt c z : ℕ) = β' :=
      ⟨c₀, mem_panelRest.2 ⟨hc₀, hc₀a⟩, hρ⟩
    simp only [f, dite_eq_left hex]
    exact hex.choose_spec
  have huniq : ∀ z c, (rhoPt a z : ℕ) = β → c ∈ panelRest k a → (rhoPt c z : ℕ) = β' →
      c = f z := by
    intro z c hz hc hcz
    obtain ⟨c₀, hc₀, hc₀a, hρ, hoth⟩ := hfar z hz
    have key : ∀ c', c' ∈ panelRest k a → (rhoPt c' z : ℕ) = β' → c' = c₀ := by
      intro c' hc' hc'z
      by_contra hne'
      have := hoth c' (mem_panelRest.1 hc').1 (mem_panelRest.1 hc').2 hne'
      rw [this, hz] at hc'z
      exact hne hc'z.symm
    rw [key c hc hcz, key (f z) (hf z hz).1 (hf z hz).2]
  have hconv : ∀ z c, c ∈ panelRest k a → (rhoPt c z : ℕ) = β' → (rhoPt a z : ℕ) = β := by
    intro z c hc hcz
    obtain ⟨hcP, hca⟩ := mem_panelRest.1 hc
    have h1 : E6Folded.gidx k (rhoPt c z) ≠ rhoPt c z := by rw [hcz, hββ]; exact hne.symm
    have h2 : plen (E6Folded.gidx k (rhoPt c z)) = plen (rhoPt c z) + 1 := by
      rw [hcz, hββ]; omega
    have haP : a ∈ panel ncs stdDistance k c := mem_residue_symm hδ hcP
    have := (rho_panel c (ptChamber z) k).2.1 h1 h2 a haP (Ne.symm hca)
    have hcz' : (rho c (ptChamber z) : ℕ) = β' := hcz
    change (rhoPt a z : ℕ) = _ at this
    rw [this, hcz', hββ]
  rw [Set.ncard_eq_toFinset_card']
  have hS : (Set.toFinset {z | z ∈ rootClass ∧ (rhoPt a z : ℕ) = β ∧ C z}) =
      Finset.univ.filter fun z => z ∈ rootClass ∧ (rhoPt a z : ℕ) = β ∧ C z := by
    ext z
    simp
  rw [hS, Finset.card_eq_sum_card_fiberwise (f := f) (t := panelRest k a)
    (fun z hz => (hf z (Finset.mem_filter.1 hz).2.2.1).1)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hz, hza, hC⟩, rfl⟩
    exact ⟨hz, (hf z hza).2, hC⟩
  · rintro ⟨hz, hcz, hC⟩
    have hza := hconv z c hc hcz
    exact ⟨⟨hz, hza, hC⟩, (huniq z c hza hc hcz).symm⟩

theorem hInit_getD (j : ℕ) {γ : ℕ} (hγ : γ < 24) :
    (hInit j).getD γ 0 = if lidx γ = j then 1 else 0 := by
  rw [hInit, List.getD_eq_getElem _ _ (by simp [hγ]), List.getElem_map, List.getElem_range]

theorem ncard_rhoPt_relPt
    {S : stdGroup} (hS : S ∈ rootClass) (j : ℕ) :
    ∀ n, ∀ β < 24, plen β = n → ∀ a : stdChamber,
      {z | z ∈ rootClass ∧ (rhoPt a z : ℕ) = β ∧ relPt z S = j}.ncard =
        (hVec j β).getD (rhoPt a S) 0 := by
  intro n
  induction n with
  | zero =>
    intro β hβ hn a
    obtain rfl := plen_eq_zero_iff β hβ hn
    rw [hVec_23, hInit_getD j (rhoPt a S).2]
    have hrel : relPt (chamberRoot a) S = lidx (rhoPt a S) := by
      rw [relPt_eq (chamberRoot_mem_rootClass a) hS rfl (chamberRoot_ptChamber hS)]
      rfl
    have hset : {z | z ∈ rootClass ∧ (rhoPt a z : ℕ) = 23 ∧ relPt z S = j} =
        if lidx (rhoPt a S) = j then {chamberRoot a} else ∅ := by
      ext z
      constructor
      · rintro ⟨hz, h23, hj⟩
        have e := (rhoPt_eq_23_iff a hz).1 h23
        rw [e, hrel] at hj
        rw [ite_eq_left hj, e]
        rfl
      · intro h
        split_ifs at h with hj
        · rw [Set.mem_singleton_iff] at h
          rw [h]
          exact ⟨chamberRoot_mem_rootClass a,
            (rhoPt_eq_23_iff a (chamberRoot_mem_rootClass a)).2 rfl, hrel.trans hj⟩
        · exact absurd h (Set.notMem_empty z)
    rw [hset]
    split_ifs <;> simp
  | succ n ih =>
    intro β hβ hn a
    have hβ23 : β ≠ 23 := fun h => by rw [h, plen_23] at hn; omega
    obtain ⟨k, -, hlen, hvec⟩ := hVec_cons hβ hβ23
    rw [ncard_rhoPt_eq_sum a hβ hlen, hvec j]
    have hlt : E6Folded.gidx k β < 24 := E6Folded.gidx_lt k hβ
    rw [Finset.sum_congr rfl fun c _ => ih _ hlt (by omega) c]
    exact sum_panel_rho _ a (ptChamber S) k

theorem ncard_relPt_relPt
    {y S : stdGroup} (hy : y ∈ rootClass) (hS : S ∈ rootClass) {k j : ℕ}
    (hk : k < 5) (hj : j < 5) :
    {z | z ∈ rootClass ∧ relPt y z = k ∧ relPt z S = j}.ncard =
      ((hMat.getD k []).getD (relPt y S) []).getD j 0 := by
  classical
  have : Fintype stdGroup := Fintype.ofFinite _
  set a := ptChamber y
  have hay : chamberRoot a = y := chamberRoot_ptChamber hy
  have hrel : ∀ z, z ∈ rootClass → relPt y z = lidx (rhoPt a z) := fun z hz => by
    rw [relPt_eq hy hz hay (chamberRoot_ptChamber hz)]
    rfl
  have hset : ∀ β : ℕ, {z | z ∈ rootClass ∧ (rhoPt a z : ℕ) = β ∧ relPt z S = j}.ncard =
      (Finset.univ.filter fun z => z ∈ rootClass ∧ (rhoPt a z : ℕ) = β ∧ relPt z S = j).card := by
    intro β
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext z
    simp
  rw [Set.ncard_eq_toFinset_card']
  have hT : (Set.toFinset {z | z ∈ rootClass ∧ relPt y z = k ∧ relPt z S = j}) =
      Finset.univ.filter fun z => z ∈ rootClass ∧ relPt y z = k ∧ relPt z S = j := by
    ext z
    simp
  rw [hT, Finset.card_eq_sum_card_fiberwise (f := fun z => (rhoPt a z : ℕ))
    (t := Finset.range 24) (fun z _ => Finset.mem_range.2 (rhoPt a z).2)]
  have hfib : ∀ β ∈ Finset.range 24,
      ((Finset.univ.filter fun z => z ∈ rootClass ∧ relPt y z = k ∧ relPt z S = j).filter
        fun z => (rhoPt a z : ℕ) = β).card =
      if lidx β = k then (hVec j β).getD (rhoPt a S) 0 else 0 := by
    intro β hβ
    rw [Finset.mem_range] at hβ
    split_ifs with hβk
    · rw [← ncard_rhoPt_relPt hS j _ β hβ rfl a, hset]
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hz, -, hzS⟩, hzβ⟩
        exact ⟨hz, hzβ, hzS⟩
      · rintro ⟨hz, hzβ, hzS⟩
        exact ⟨⟨hz, by rw [hrel z hz, hzβ, hβk], hzS⟩, hzβ⟩
    · rw [Finset.card_eq_zero]
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      rintro ⟨hz, hzk, -⟩ hzβ
      rw [hrel z hz, hzβ] at hzk
      exact hβk hzk
  rw [Finset.sum_congr rfl hfib]
  have hhS := hSum_eq hk hj (rhoPt a S).2
  rw [hSum] at hhS
  rw [hhS, hrel S hS]

end CFSG.Monster.B.E6.StdF4
