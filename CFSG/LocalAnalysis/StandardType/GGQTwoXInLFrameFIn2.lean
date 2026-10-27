module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem not_three_dvd_card_center_ggG0 {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(ggG0 3 B x L D J)) := by
  let G0 : Subgroup G := ggG0 3 B x L D J
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have h3C : ¬ 3 ∣ Nat.card (Subgroup.centralizer (G0 : Set G)) :=
    not_dvd_card_centralizer_ggG0_of_stdSub hp hSstar hst hDJ
  intro h
  apply h3C
  have hle : (Subgroup.center ↥G0).map G0.subtype ≤
      Subgroup.centralizer (G0 : Set G) := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hdvd : Nat.card ((Subgroup.center ↥G0).map G0.subtype) ∣
      Nat.card (Subgroup.centralizer (G0 : Set G)) := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (K := Subgroup.center ↥G0) G0.subtype_injective] at hdvd
  exact h.trans hdvd

theorem le_ggG0_of_marking {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hInn : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (θ : ↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J) ≃* R)
    (hperf : commutator ↥(ggG0 3 B x L D J) = ⊤)
    (hBs : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Bs ≤ ggG0 3 B x L D J := by
  let G0 : Subgroup G := ggG0 3 B x L D J
  let π : ↥G0 →* R := ggMarkHom θ
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  obtain ⟨hp, hBsElem, -, -, -⟩ := hcfg.tableB_facts
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hBsG0 : Bs ≤ Subgroup.normalizer (G0 : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.2.2
  have h3C : ¬ 3 ∣ Nat.card (Subgroup.centralizer (G0 : Set G)) :=
    not_dvd_card_centralizer_ggG0_of_stdSub hp hSstar hst hDJ
  have hkerπ : π.ker = Subgroup.center ↥G0 := by
    rw [show π = ggQuotHom (L := G0) θ from rfl, ker_ggQuotHom]
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥G0))
  have hperfG0 : Group.IsPerfect ↥G0 := ⟨hperf⟩
  intro b hb
  obtain ⟨φ, hφI, hφind⟩ := hBs b hb
  obtain ⟨r, hφ⟩ := hInn φ hφI
  obtain ⟨g, hg⟩ := hπsurj r
  have hbN : b ∈ Subgroup.normalizer (G0 : Set G) := hBsG0 hb
  have hbconj_mem : ∀ l : ↥G0, b⁻¹ * (l : G) * b ∈ G0 := by
    intro l
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) (l : G)).mp l.2
  have hconj : ∀ l : ↥G0, π ⟨b⁻¹ * (l : G) * b, hbconj_mem l⟩ = π (g * l * g⁻¹) := by
    intro l
    let l' : ↥G0 := ⟨b⁻¹ * (l : G) * b, hbconj_mem l⟩
    have h1 : φ (π l) = π l' := hφind l l' rfl
    have h2 : φ (π l) = π g * π l * (π g)⁻¹ := by
      rw [hφ, MulAut.conj_apply, ← hg]
    calc π l' = φ (π l) := h1.symm
      _ = π g * π l * (π g)⁻¹ := h2
      _ = π (g * l * g⁻¹) := by simp only [map_mul, map_inv]
  let h : G := g⁻¹ * b⁻¹
  have hhN : h ∈ Subgroup.normalizer (G0 : Set G) := by
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer g.2))
      (Subgroup.inv_mem _ hbN)
  have hhC : h ∈ Subgroup.centralizer (G0 : Set G) := by
    refine CFSG.mem_centralizer_of_commutator_mem_center hperfG0 hhN ?_
    intro l hl
    let lG0 : ↥G0 := ⟨l, hl⟩
    let l' : ↥G0 := ⟨b⁻¹ * l * b, hbconj_mem lG0⟩
    have h1 : h * l * h⁻¹ = g⁻¹ * (l' : G) * g := by
      simp only [h, l', Subgroup.coe_inv]
      group
    have hzmem : h * l * h⁻¹ * l⁻¹ ∈ G0 := by
      rw [h1]
      exact G0.mul_mem (G0.mul_mem (G0.mul_mem (G0.inv_mem g.2) (hbconj_mem lG0)) g.2)
        (G0.inv_mem hl)
    let z : ↥G0 := ⟨h * l * h⁻¹ * l⁻¹, hzmem⟩
    have hzker : π z = 1 := by
      have hz_eq : z = g⁻¹ * l' * g * lG0⁻¹ := by
        apply Subtype.ext
        change h * l * h⁻¹ * l⁻¹ = (g⁻¹ * (l' : G) * g) * (lG0 : G)⁻¹
        simp only [h, l', lG0, Subgroup.coe_inv]
        group
      rw [hz_eq]
      simp only [map_mul, map_inv]
      rw [hconj lG0]
      simp only [map_mul, map_inv]
      group
    have hzcenter : z ∈ Subgroup.center ↥G0 := by
      rw [← hkerπ]
      exact MonoidHom.mem_ker.mpr hzker
    exact Subgroup.mem_map.mpr ⟨z, hzcenter, rfl⟩
  have hcomm_hg : (g : G) * h = h * (g : G) :=
    Subgroup.mem_centralizer_iff.mp hhC g g.2
  have hbg : b * (g : G) = (g : G) * b := by
    have h1 : (g : G)⁻¹ * b⁻¹ * (g : G) = b⁻¹ := by
      have h' := hcomm_hg
      rw [show h = (g : G)⁻¹ * b⁻¹ from rfl] at h'
      group at h'
      simpa using h'.symm
    have h2 : (g : G)⁻¹ * b * (g : G) = b := by
      have hinv := congrArg Inv.inv h1
      calc (g : G)⁻¹ * b * (g : G) = ((g : G)⁻¹ * b⁻¹ * (g : G))⁻¹ := by group
        _ = (b⁻¹)⁻¹ := by rw [hinv]
        _ = b := inv_inv b
    calc b * (g : G) = (g : G) * ((g : G)⁻¹ * b * (g : G)) := by group
      _ = (g : G) * b := by rw [h2]
  have hb3 : b ^ 3 = 1 := hBsElem.2 b hb
  have hh3 : h ^ 3 = ((g : G)⁻¹) ^ 3 := by
    have hcommgb : Commute ((g : G)⁻¹) (b⁻¹) :=
      (show Commute (g : G) b from hbg.symm).inv_left.inv_right
    rw [show h = (g : G)⁻¹ * b⁻¹ from rfl, hcommgb.mul_pow 3,
      show (b⁻¹) ^ 3 = 1 by rw [inv_pow, hb3, inv_one], mul_one]
  have hcop : Nat.Coprime 3 (orderOf h) := by
    have hdvd : orderOf h ∣ Nat.card (Subgroup.centralizer (G0 : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hhC
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h3d => h3C (h3d.trans hdvd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 3) (x := h) hcop
  have hh3G0 : h ^ 3 ∈ G0 := by
    rw [hh3]
    exact G0.pow_mem (G0.inv_mem g.2) 3
  have hhG0 : h ∈ G0 := by
    rw [← hm]
    exact G0.pow_mem hh3G0 m
  have hb_eq : b = h⁻¹ * g⁻¹ := by
    rw [show h = g⁻¹ * b⁻¹ from rfl]
    group
  rw [hb_eq]
  exact G0.mul_mem (G0.inv_mem hhG0) (G0.inv_mem g.2)

end CFSG.StandardType

end
