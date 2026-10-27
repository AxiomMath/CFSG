module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.ShapeBlocks
import CFSG.OddTranspositions.PartFour.LineTransport
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D}


private theorem twoOddCore_conj_mem_DalphaStar (hC : HypothesisC D) {x : G}
    (hx : x ∈ DalphaStar D hC.alpha) {k : Halpha D hC.alpha}
    (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha)) :
    (k : G) * x * (k : G)⁻¹ ∈ DalphaStar D hC.alpha := by
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  have hmem : k * xH * k⁻¹ ∈ DstarH hC :=
    DstarH_conj_mem hC (x := xH) ((mem_DstarH_iff hC).mpr hx)
  simpa [xH, Subgroup.coe_mul] using (mem_DstarH_iff hC).mp hmem

private theorem exists_witness_core (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : v ∈ β) :
    ∃ (g : G) (k : Halpha D hC.alpha) (u' : G),
      β = cimg g hC.alpha ∧
      k ∈ EightOne.twoOddCore (Halpha D hC.alpha) ∧
      g⁻¹ * hC.d * g ∈ DalphaStar D hC.alpha ∧
      u' = g * ((k : G) * (g⁻¹ * hC.d * g) * (k : G)⁻¹) * g⁻¹ ∧
      u' ∈ DalphaStar D β ∧ ¬ Commute hC.d u' ∧ u' ∉ hC.alpha ∧ Commute u' v := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
  have hαDβ : hC.alpha ∈ Dalpha D β :=
    mem_Dalpha_symm hβ hC.isBlock_alpha.subset
  let α₀ : Set G := cimg g⁻¹ hC.alpha
  have hβα : (fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' β = hC.alpha := by
    rw [hg]
    exact cimg_inv_cimg g hC.alpha
  have hα₀ : α₀ ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hαDβ g⁻¹
    rw [hβα] at h
    simpa [α₀, cimg] using h
  let u₀ : G := g⁻¹ * hC.d * g
  have hu₀α₀ : u₀ ∈ α₀ := by
    change u₀ ∈ cimg g⁻¹ hC.alpha
    refine ⟨hC.d, hC.d_mem_alpha, ?_⟩
    show g⁻¹ * hC.d * (g⁻¹)⁻¹ = g⁻¹ * hC.d * g
    group
  obtain ⟨k, hk, hnc, hnot⟩ := MainHyp.exists_conj_not_commute h hα₀ hu₀α₀
  let b : G := (k : G) * u₀ * (k : G)⁻¹
  let u' : G := g * b * g⁻¹
  have hu₀Star : u₀ ∈ DalphaStar D hC.alpha := subset_DalphaStar hα₀ hu₀α₀
  have hbStar : b ∈ DalphaStar D hC.alpha := by
    simpa [b, u₀] using twoOddCore_conj_mem_DalphaStar hC hu₀Star hk
  have hu'β : u' ∈ DalphaStar D β := by
    have h := DalphaStar.conj hC.setup.normal hbStar g
    rw [← hg] at h
    simpa [u', b] using h
  have hgud : g * u₀ * g⁻¹ = hC.d := by
    show g * (g⁻¹ * hC.d * g) * g⁻¹ = hC.d
    group
  have hnc' : ¬ Commute hC.d u' := by
    intro hc
    apply hnc
    have h : Commute (g * u₀ * g⁻¹) (g * b * g⁻¹) := by
      rw [hgud]
      simpa [u'] using hc
    exact (Commute.conj_iff g).mp h
  have hnotα : u' ∉ hC.alpha := by
    intro hu'α
    apply hnot
    have hbα₀ : b ∈ cimg g⁻¹ hC.alpha := by
      rw [mem_cimg]
      simpa [u', inv_inv] using hu'α
    simpa [α₀, cimg] using hbα₀
  have huv : Commute u' v := by
    obtain ⟨δ, hδ, hu'δ⟩ := hu'β
    exact ((mem_Dalpha_iff.mp hδ).2.2.2 v hv u' hu'δ).symm
  exact ⟨g, k, u', hg, hk, hu₀Star, rfl, hu'β, hnc', hnotα, huv⟩

private theorem commute_witness_of_mem_E (h : MainHyp hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : v ∈ β)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {g : G}
    (hg : β = cimg g hC.alpha) {k : Halpha D hC.alpha}
    (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (hu₀E : g⁻¹ * hC.d * g ∈ DalphaStar D hC.alpha)
    {u' : G}
    (hu' : u' = g * ((k : G) * (g⁻¹ * hC.d * g) * (k : G)⁻¹) * g⁻¹)
    {q : G} (hq : q ∈ DalphaStar D hC.alpha) (hqv : q ≠ v)
    (hcomm : Commute v q) : Commute u' q := by
  classical
  let u₀ : G := g⁻¹ * hC.d * g
  let q₀ : G := g⁻¹ * q * g
  obtain ⟨γ, hγ, hqγ⟩ := hq
  have hγDβ : γ ∈ Dalpha D β :=
    MainHyp.mem_Dalpha_of_mem_of_commute h hβ hγ hv hqγ hqv.symm hcomm
  have hqβ : q ∈ DalphaStar D β := subset_DalphaStar hγDβ hqγ
  have hq' : q ∈ DalphaStar D hC.alpha := ⟨γ, hγ, hqγ⟩
  have hq₀ : q₀ ∈ DalphaStar D hC.alpha := by
    have hβα : (fun x => g⁻¹ * x * (g⁻¹)⁻¹) '' β = hC.alpha := by
      rw [hg]
      exact cimg_inv_cimg g hC.alpha
    have h := DalphaStar.conj hC.setup.normal hqβ g⁻¹
    rw [hβα] at h
    simpa [q₀] using h
  have hqE : q ∈ hC.E := by rwa [← hC.DalphaStar_alpha]
  have hdE : hC.d ∉ hC.E := by
    rw [← hC.DalphaStar_alpha]
    exact fun hd => Set.disjoint_left.mp (disjoint_alpha_DalphaStar hC.isBlock_alpha)
      hC.d_mem_alpha hd
  have hdq : hC.d ≠ q := fun h => hdE (h ▸ hqE)
  have hu₀q₀ : u₀ ≠ q₀ := by
    intro h
    apply hdq
    have hu₀eq : g * u₀ * g⁻¹ = hC.d := by
      show g * (g⁻¹ * hC.d * g) * g⁻¹ = hC.d
      group
    have hq₀eq : g * q₀ * g⁻¹ = q := by
      show g * (g⁻¹ * q * g) * g⁻¹ = q
      group
    calc hC.d = g * u₀ * g⁻¹ := hu₀eq.symm
      _ = g * q₀ * g⁻¹ := by rw [h]
      _ = q := hq₀eq
  have hcomm0 : Commute u₀ q₀ := by
    have h := (Commute.conj_iff g⁻¹).mpr ((hC.DalphaStar_subset_commute hq').2.symm)
    simpa [u₀, q₀] using h
  have hkK : (k : G) ∈ kBlock D hC.alpha :=
    Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have hbq₀ : Commute ((k : G) * u₀ * (k : G)⁻¹) q₀ :=
    commute_conj_of_mem_dalphaStar hC hQ1 (by simpa [u₀] using hu₀E) hq₀ hu₀q₀ hcomm0 hkK
  have h := (Commute.conj_iff g).mpr hbq₀
  have hq₀eq : g * q₀ * g⁻¹ = q := by
    show g * (g⁻¹ * q * g) * g⁻¹ = q
    group
  rw [hq₀eq, ← hu'] at h
  exact h

private theorem commute_of_four_point_at_gamma {U : Type} [Group U] [Finite U]
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha) ≃*
      Multiplicative (ZMod 2) × U)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {γc : Set G} {gc : G}
    (hgc : γc = cimg gc hC.alpha) {u u' v b : G}
    (hu : u ∈ DalphaStar D γc) (hu' : u' ∈ DalphaStar D γc)
    (hv : v ∈ DalphaStar D γc) (hb : b ∈ DalphaStar D γc)
    (huv : Commute u v) (hu'v : Commute u' v) (hub : Commute u b)
    (huu' : ¬ Commute u u') (hvb : ¬ Commute v b) :
    Commute u' b := by
  have hγcα : (fun x => gc⁻¹ * x * (gc⁻¹)⁻¹) '' γc = hC.alpha := by
    rw [hgc]
    exact cimg_inv_cimg gc hC.alpha
  have hmem : ∀ x ∈ DalphaStar D γc, gc⁻¹ * x * gc ∈ DalphaStar D hC.alpha := by
    intro x hx
    have h := DalphaStar.conj hC.setup.normal hx gc⁻¹
    rw [hγcα] at h
    simpa using h
  have hfour := commute_of_four_point_dalphaStar hC hU φ hQ1
    (hmem u hu) (hmem u' hu') (hmem v hv) (hmem b hb)
    (by simpa using (Commute.conj_iff gc⁻¹).mpr huv)
    (by simpa using (Commute.conj_iff gc⁻¹).mpr hu'v)
    (by simpa using (Commute.conj_iff gc⁻¹).mpr hub)
    (fun h => huu' ((Commute.conj_iff gc⁻¹).mp (by simpa only [inv_inv] using h)))
    (fun h => hvb ((Commute.conj_iff gc⁻¹).mp (by simpa only [inv_inv] using h)))
  have h := (Commute.conj_iff gc).mpr hfour
  have hu'eq : gc * (gc⁻¹ * u' * gc) * gc⁻¹ = u' := by group
  have hbeq : gc * (gc⁻¹ * b * gc) * gc⁻¹ = b := by group
  rwa [hu'eq, hbeq] at h

private theorem mem_DalphaStar_gamma_of_witness (h : MainHyp hC) {β γc : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγc : γc ∈ Dalpha D hC.alpha)
    {v c : G} (hv : v ∈ β) (hcγc : c ∈ γc) (hvc : v ≠ c) (hcomm : Commute v c)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {k : Halpha D hC.alpha}
    (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (hbne : (k : G) * v * (k : G)⁻¹ ≠ v)
    {u' : G} (hu'β : u' ∈ DalphaStar D β) (hu'c : Commute u' c)
    (hu'notE : u' ∉ hC.E) :
    hC.d ∈ DalphaStar D γc ∧ v ∈ DalphaStar D γc ∧
      (k : G) * v * (k : G)⁻¹ ∈ DalphaStar D γc ∧ u' ∈ DalphaStar D γc := by
  have hvStar : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  have hkK : (k : G) ∈ kBlock D hC.alpha := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
  have hncvb : ¬ Commute v ((k : G) * v * (k : G)⁻¹) :=
    not_commute_conj_of_mem_dalphaStar hC hQ1 hvStar hkK hbne
  have hβDγ : β ∈ Dalpha D γc :=
    MainHyp.mem_Dalpha_of_mem_of_commute h hγc hβ hcγc hv hvc.symm hcomm.symm
  have huγ : hC.d ∈ DalphaStar D γc :=
    subset_DalphaStar (mem_Dalpha_symm hγc hC.isBlock_alpha.subset) hC.d_mem_alpha
  have hvγ : v ∈ DalphaStar D γc := subset_DalphaStar hβDγ hv
  have hblockDα : cimg (k : G) β ∈ Dalpha D hC.alpha :=
    smul_mem_Dalpha_of_mem_Halpha hC k.2 hβ
  have hbκ : (k : G) * v * (k : G)⁻¹ ∈ cimg (k : G) β := ⟨v, hv, rfl⟩
  have hbc : (k : G) * v * (k : G)⁻¹ ≠ c := by
    intro hbc
    exact hncvb (by rwa [← hbc] at hcomm)
  have hcommbc : Commute ((k : G) * v * (k : G)⁻¹) c :=
    commute_conj_of_mem_dalphaStar hC hQ1 hvStar ⟨γc, hγc, hcγc⟩ hvc hcomm hkK
  have hγDblock : γc ∈ Dalpha D (cimg (k : G) β) :=
    MainHyp.mem_Dalpha_of_mem_of_commute h hblockDα hγc hbκ hcγc hbc hcommbc
  have hblockDγ : cimg (k : G) β ∈ Dalpha D γc :=
    mem_Dalpha_symm hγDblock (Dalpha.subset hblockDα)
  have hbγ : (k : G) * v * (k : G)⁻¹ ∈ DalphaStar D γc :=
    subset_DalphaStar hblockDγ hbκ
  obtain ⟨δ', hδ'Dβ, hu'δ'⟩ := hu'β
  have hδ'neγ : δ' ≠ γc := by
    intro hδγ
    apply hu'notE
    rw [← hC.DalphaStar_alpha]
    exact subset_DalphaStar hγc (hδγ ▸ hu'δ')
  have hδ'class : δ' ∈ blockClass hC.alpha := by
    rw [← blockClass_eq_of_mem hβ.1]
    exact hδ'Dβ.1
  have hγDδ' : γc ∈ Dalpha D δ' :=
    PartThree.mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
      hδ'class hγc.1 hδ'neγ hu'δ' hcγc hu'c
  have hδ'Dγ : δ' ∈ Dalpha D γc :=
    mem_Dalpha_symm hγDδ' (Dalpha.subset hδ'Dβ)
  exact ⟨huγ, hvγ, hbγ, subset_DalphaStar hδ'Dγ hu'δ'⟩

private theorem commute_kConj_of_witness (h : MainHyp hC) {U : Type} [Group U] [Finite U]
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha) ≃*
      Multiplicative (ZMod 2) × U)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {v c : G} (hv : v ∈ β)
    (hc : c ∈ DalphaStar D hC.alpha) (hvc : v ≠ c) (hcomm : Commute v c)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {u' : G}
    (hu'β : u' ∈ DalphaStar D β) (hu'v : Commute u' v) (hu'c : Commute u' c)
    (hu'notE : u' ∉ hC.E) (hnc : ¬ Commute hC.d u') :
    ∀ κ ∈ kBlock D hC.alpha, Commute u' (κ * v * κ⁻¹) := by
  intro κ hκ
  by_cases hfix : κ * v * κ⁻¹ = v
  · simpa [hfix] using hu'v
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hκ
  have hbne : (k : G) * v * (k : G)⁻¹ ≠ v := by simpa using hfix
  obtain ⟨γc, hγc, hcγc⟩ := hc
  obtain ⟨huγ, hvγ, hbγ, hu'γ⟩ :=
    mem_DalphaStar_gamma_of_witness h hβ hγc hv hcγc hvc hcomm hQ1 hk hbne
      hu'β hu'c hu'notE
  have hvStar : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  have hbStar : (k : G) * v * (k : G)⁻¹ ∈ DalphaStar D hC.alpha :=
    twoOddCore_conj_mem_DalphaStar hC hvStar hk
  obtain ⟨gc, hgc⟩ := mem_blockClass_iff.mp hγc.1
  refine commute_of_four_point_at_gamma hU φ hQ1 hgc huγ hu'γ hvγ hbγ
    ((mem_Dalpha_iff.mp hβ).2.2.2 hC.d hC.d_mem_alpha v hv) hu'v
    ((hC.DalphaStar_subset_commute hbStar).2).symm hnc ?_
  exact not_commute_conj_of_mem_dalphaStar hC hQ1 hvStar hκ hbne

theorem MainHyp.exists_witness (h : MainHyp hC) {U : Type} [Group U] [Finite U]
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha) ≃*
      Multiplicative (ZMod 2) × U)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {v c : G} (hv : v ∈ β) (hc : c ∈ DalphaStar D hC.alpha) (hvc : v ≠ c)
    (hcomm : Commute v c) :
    ∃ u' ∈ DalphaStar D β, ¬ Commute hC.d u' ∧ u' ∉ hC.alpha ∧ Commute u' v ∧
      (∀ q ∈ DalphaStar D hC.alpha, q ≠ v → Commute v q → Commute u' q) ∧
      ∀ κ ∈ kBlock D hC.alpha, Commute u' (κ * v * κ⁻¹) := by
  obtain ⟨g, k, u', hg, hk, hu₀E, hu', hu'β, hnc, hu'notα, hu'v⟩ :=
    exists_witness_core (hC := hC) h hβ hv
  have hu'notE : u' ∉ hC.E := by
    rw [← hC.DalphaStar_alpha]
    intro hE
    exact hnc ((hC.DalphaStar_subset_commute hE).2.symm)
  have hu'c : Commute u' c :=
    commute_witness_of_mem_E (hC := hC) h hβ hv hQ1 hg hk hu₀E hu' hc hvc.symm hcomm
  refine ⟨u', hu'β, hnc, hu'notα, hu'v, ?_, ?_⟩
  · intro q hq hqv hcommq
    exact commute_witness_of_mem_E (hC := hC) h hβ hv hQ1 hg hk hu₀E hu' hq hqv hcommq
  · exact commute_kConj_of_witness (hC := hC) h hU φ hβ hv hc hvc hcomm hQ1 hu'β hu'v
      hu'c hu'notE hnc

end CFSG.OddTranspositions.PartThree.ElevenThree
