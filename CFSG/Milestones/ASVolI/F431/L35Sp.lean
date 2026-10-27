module

import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.AInvSpAll
public import CFSG.Milestones.ASVolI.F431.L39Two

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F435Sp

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_false_of_oPPrime_le (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    (hLM : oPPrime 2 (Gp ⊓ M₁) ≤ Gp ⊓ M₂) : False := by
  haveI := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSyl, hB⟩ := burnsideF4j_sylow_data hyp
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  have hgen := burnsideF4j_parabolics_gen hP
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSL : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ oPPrime 2 (Gp ⊓ M₁) :=
    burnsideF4d_Z1_le_oPPrime hSyl.2.1
      (le_inf (hSB.trans inf_le_left) (hSB.trans (inf_le_right.trans inf_le_left)))
  have P1 : ∀ y ∈ Gp, conjSub y (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ≤ Gp ⊓ M₂ → y ∈ M₂ := by
    intro y hy hyS
    have hS2 : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (Gp ⊓ M₂) :=
      F7.isSylowTwoOf_mono_right hSyl
        (le_inf (hSB.trans inf_le_left) (hSB.trans (inf_le_right.trans inf_le_right)))
        inf_le_left
    have hyS2 : ChF.IsSylowOf 2 (conjSub y (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (Gp ⊓ M₂) :=
      F7.isSylowTwoOf_mono_right (burnsideF4ja_isSylowOf_conjSub hSyl hy) hyS inf_le_left
    obtain ⟨m, hm, hmeq⟩ := burnsideF4ja_sylow_conj hyS2 hS2
    have hN : m⁻¹ * y ∈
        Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
      apply burnsideF4ja_mem_normalizer_of_conjSub_eq
      rw [conjSub_mul, hmeq, conjSub_conjSub_inv]
    have hmy : m⁻¹ * y ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hB]
      exact ⟨Gp.mul_mem (Gp.inv_mem hm.1) hy, hN⟩
    have h1 := M₂.mul_mem hm.2 hmy.2.2
    simpa using h1
  have h1M : Gp ⊓ M₁ ≤ M₂ := by
    intro x hx
    refine P1 x hx.1 fun y hy => ?_
    rw [mem_conjSub] at hy
    have hxN := burnsideF4d_le_normalizer_oPPrime (Gp ⊓ M₁) hx
    have h2 : x * (x⁻¹ * y * x) * x⁻¹ ∈ oPPrime 2 (Gp ⊓ M₁) :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (hSL hy)
    have h3 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [h3] at h2
    exact hLM h2
  obtain ⟨-, -, -, hmax⟩ := hP
  have hne := ((hmax (Gp ⊓ M₂)).mpr (Or.inr rfl)).2.2.1
  apply hne
  apply le_antisymm inf_le_left
  calc Gp = (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) := hgen.symm
    _ ≤ Gp ⊓ M₂ := sup_le (le_inf inf_le_left h1M) le_rfl

theorem burnsideF4m_Z1_inf_Z2 (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) {w : E}
    (hw1 : w ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hw2 : w ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) : w = 1 := by
  by_contra hw
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := burnsideF4j_bOne_injective hyp
  have hb2 : Function.Injective (burnsideF4d_bTwo β ε) := burnsideF4j_bTwo_injective hyp
  have hwM1 : w ∈ M₁ := ((burnsideF4d_oPPrime_le _) hw1.1).2
  have hwM2 : w ∈ M₂ := ((burnsideF4d_oPPrime_le _) hw2.1).2
  have hc : Subgroup.centralizer ({burnsideF4d_bTwo β ε ⟨w, hwM2⟩} : Set M) ≤ MiTwo β ε := by
    refine (hyp.hc rfl).1 _ ?_ ?_
    · rw [burnsideF4j_Z2_eq hyp]
      exact mem_subImg_of_mem _ hwM2 hw2
    · intro h
      exact hw (congrArg Subtype.val (hb2 (h.trans (map_one _).symm)))
  have hinter := burnsideF4d_inter_eq β hyp.faithful ε hyp.inj
  apply burnsideF4m_false_of_oPPrime_le hyp.amalgam
  intro y hy
  have hyG : y ∈ Gp ⊓ M₁ := burnsideF4d_oPPrime_le _ hy
  have hyc : y * w = w * y := Subgroup.mem_centralizer_iff.mp hw1.2 y hy
  have hmem : burnsideF4d_bOne β ε ⟨y, hyG.2⟩ ∈ MiOne β ε ⊓ MiTwo β ε := by
    refine ⟨?_, hc ?_⟩
    · rw [burnsideF4d_MiOne_eq]
      exact mem_subImg_of_mem _ hyG.2 hyG.2
    · rw [Subgroup.mem_centralizer_singleton_iff, ← burnsideF4m_bOne_eq_bTwo β ε w hwM1 hwM2]
      exact (commute_iff_of_injective hb1 hwM1 hyG.2).mpr hyc
  rw [hinter] at hmem
  exact ⟨hyG.1, ((mem_subImg_iff_of_injective hb1 hyG.2).mp hmem).2⟩

theorem burnsideF4m_conj_mem_Zj (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {h : E} (hh : h ∈ M₁ ⊓ M₂) :
    (∀ x, x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) → h * x * h⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x, x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) → h * x * h⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  haveI := hyp.normal
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hN := burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime
      (burnsideF4j_le_normalizer_inf hyp.normal M₁ hh.1))
    exact (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  · have hN := burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime
      (burnsideF4j_le_normalizer_inf hyp.normal M₂ hh.2))
    exact (Subgroup.mem_normalizer_iff.mp hN x).mp hx

theorem burnsideF4m_sp4_conj_of_type (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂)
    (hZ12 : ∀ w, w ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) → w ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) → w = 1)
    {z₁ z₂ : E} (hz₁ : z₁ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hz₁S : z₁ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))))
    (hz₁1 : z₁ ≠ 1) (hz₁2 : z₁ * z₁ = 1) (hz₂ : z₂ ∈ ctr (oPPrime 2 (Gp ⊓ M₂)))
    (hz₂S : z₂ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (hz₂1 : z₂ ≠ 1) (hz₂2 : z₂ * z₂ = 1)
    {x y : E} (hxS : x ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))))
    (hyS : y ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (hx1 : x ≠ 1) (hx2 : x * x = 1) (hy1 : y ≠ 1)
    (hy2 : y * y = 1) (h1 : x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) ↔ y ∈ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (h2 : x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) ↔ y ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) :
    ∃ g ∈ Gp, g * x * g⁻¹ = y := by
  haveI := hyp.finite
  by_cases hx₁ : x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))
  · obtain ⟨m, hm, hmx⟩ := burnsideF4j_Z1_conj hyp (by decide) (by decide) hx₁ hx1 (h1.mp hx₁) hy1
    exact ⟨m, hm.1, hmx⟩
  by_cases hx₂ : x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))
  · obtain ⟨m, hm, hmx⟩ := (burnsideF4jb_Z2_conj hyp).2 x hx₂ hx1 y (h2.mp hx₂) hy1
    exact ⟨m, hm.1, hmx⟩
  have hy₁ : y ∉ ctr (oPPrime 2 (Gp ⊓ M₁)) := fun h => hx₁ (h1.mpr h)
  have hy₂ : y ∉ ctr (oPPrime 2 (Gp ⊓ M₂)) := fun h => hx₂ (h2.mpr h)
  obtain ⟨hSyl, hB⟩ := burnsideF4j_sylow_data hyp
  have htype : ∀ a b : E, a ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) →
      b ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → (∃ g ∈ Gp, g * a * g⁻¹ = b) →
      (a ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) → b ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
      (a ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) → b ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
    rintro a b ha hb ⟨g, hg, rfl⟩
    obtain ⟨c, hc, hca⟩ := burnsideF4m_burnside hSyl ha hg hb
    have hc' : c ∈ Gp ⊓ (M₁ ⊓ M₂) := by rw [hB]; exact hc
    have hc12 : c ∈ M₁ ⊓ M₂ := hc'.2
    have hZ := burnsideF4m_conj_mem_Zj hyp hc12
    rw [← hca]
    exact ⟨hZ.1 a, hZ.2 a⟩
  have hmemI : ∀ (a : E) (ha : a ∈ Gp), a ≠ 1 → a * a = 1 →
      ConjClasses.mk (⟨a, ha⟩ : ↥Gp) ∈ InvClasses ↥Gp := fun a ha ha1 ha2 =>
    ⟨⟨a, ha⟩, ConjClasses.mem_carrier_mk, fun h => ha1 (congrArg Subtype.val h),
      Subtype.ext ha2⟩
  have hSG : ∀ a, a ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → a ∈ Gp := fun a ha =>
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) ha.1).1
  have hmk : ∀ (a b : E) (ha : a ∈ Gp) (hb : b ∈ Gp),
      ConjClasses.mk (⟨a, ha⟩ : ↥Gp) = ConjClasses.mk (⟨b, hb⟩ : ↥Gp) → ∃ g ∈ Gp, g * a * g⁻¹ = b := by
    intro a b ha hb h
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
    exact ⟨(c : E), c.2, congrArg Subtype.val hc⟩
  set C₁ := ConjClasses.mk (⟨z₁, hSG z₁ hz₁S⟩ : ↥Gp) with hC₁
  set C₂ := ConjClasses.mk (⟨z₂, hSG z₂ hz₂S⟩ : ↥Gp) with hC₂
  set Cx := ConjClasses.mk (⟨x, hSG x hxS⟩ : ↥Gp) with hCx
  set Cy := ConjClasses.mk (⟨y, hSG y hyS⟩ : ↥Gp) with hCy
  have hz₂n1 : z₂ ∉ ctr (oPPrime 2 (Gp ⊓ M₁)) := fun h => hz₂1 (hZ12 z₂ h hz₂)
  have h12 : C₁ ≠ C₂ := fun h =>
    hz₂n1 ((htype z₁ z₂ hz₁S hz₂S (hmk z₁ z₂ (hSG z₁ hz₁S) (hSG z₂ hz₂S) h)).1 hz₁)
  have hx1C : Cx ≠ C₁ := fun h =>
    hx₁ ((htype z₁ x hz₁S hxS (hmk z₁ x (hSG z₁ hz₁S) (hSG x hxS) h.symm)).1 hz₁)
  have hx2C : Cx ≠ C₂ := fun h =>
    hx₂ ((htype z₂ x hz₂S hxS (hmk z₂ x (hSG z₂ hz₂S) (hSG x hxS) h.symm)).2 hz₂)
  have hy1C : Cy ≠ C₁ := fun h =>
    hy₁ ((htype z₁ y hz₁S hyS (hmk z₁ y (hSG z₁ hz₁S) (hSG y hyS) h.symm)).1 hz₁)
  have hy2C : Cy ≠ C₂ := fun h =>
    hy₂ ((htype z₂ y hz₂S hyS (hmk z₂ y (hSG z₂ hz₂S) (hSG y hyS) h.symm)).2 hz₂)
  have hcard : Set.ncard (InvClasses ↥Gp) = 3 :=
    ((burnsideF4ja_lie_facts hyp (by decide) (by decide)).2.2 rfl).1
  refine hmk x y (hSG x hxS) (hSG y hyS) ?_
  by_contra hxy
  have hsub : ({C₁, C₂, Cx, Cy} : Set (ConjClasses ↥Gp)) ⊆ InvClasses ↥Gp := by
    intro D hD
    rcases hD with rfl | rfl | rfl | hD
    · exact hmemI _ _ hz₁1 hz₁2
    · exact hmemI _ _ hz₂1 hz₂2
    · exact hmemI _ _ hx1 hx2
    · rw [Set.mem_singleton_iff] at hD
      rw [hD]
      exact hmemI _ _ hy1 hy2
  have h4 : Set.ncard ({C₁, C₂, Cx, Cy} : Set (ConjClasses ↥Gp)) = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair (show Cx ≠ Cy from hxy)]
    · rintro (h | h)
      · exact hx2C h.symm
      · exact hy2C (Set.mem_singleton_iff.mp h).symm
    · rintro (h | h | h)
      · exact h12 h
      · exact hx1C h.symm
      · exact hy1C (Set.mem_singleton_iff.mp h).symm
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem burnsideF4m_mem_of_commute_sylow {G : Type} [Group G] [Finite G] {S H : Subgroup G}
    (hS : IsSylowTwoOf S H) {x : G} (hxH : x ∈ H) (hx2 : x * x = 1)
    (hc : ∀ s ∈ S, s * x = x * s) : x ∈ S := by
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have e : x * s * x⁻¹ = s := by
        calc x * s * x⁻¹ = s * x * x⁻¹ := by rw [hc s hs]
          _ = s := by group
      rw [e]
      exact hs
    · intro hs
      have h := hc _ hs
      have e' : s = x * s * x⁻¹ := by
        calc s = x⁻¹ * ((x * s * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * s * x⁻¹)) := by rw [h]
          _ = x * s * x⁻¹ := by group
      rw [e']
      exact hs
  have hP : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ S) :=
    (burnsideF4ja_isPGroup_zpowers hx2).to_sup_of_normal_right' hS.2.1 hzN
  have hle : Subgroup.zpowers x ⊔ S ≤ H := sup_le ((Subgroup.zpowers_le).mpr hxH) hS.1
  have heq := burnsideF4m_eq_of_sylow_le hS hP le_sup_right hle
  rw [← heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

theorem burnsideF4m_mem_ctr_S (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {X : Subgroup E}
    (hX : M₁ ⊓ M₂ ≤ X) {x : E} (hx : x ∈ ctr (oPPrime 2 (Gp ⊓ X))) (hx2 : x * x = 1) :
    x ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
  haveI := hyp.finite
  obtain ⟨hSyl, -⟩ := burnsideF4j_sylow_data hyp
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ X :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_inf_left Gp hX)
  have hSL : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ oPPrime 2 (Gp ⊓ X) :=
    burnsideF4d_Z1_le_oPPrime hSyl.2.1 hSB
  have hc : ∀ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), s * x = x * s := fun s hs =>
    Subgroup.mem_centralizer_iff.mp hx.2 s (hSL hs)
  have hxG : x ∈ Gp := ((burnsideF4d_oPPrime_le _) hx.1).1
  refine ⟨burnsideF4m_mem_of_commute_sylow hSyl hxG hx2 hc, ?_⟩
  show x ∈ Subgroup.centralizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E)
  rw [Subgroup.mem_centralizer_iff]
  exact hc

theorem burnsideF4m_Z2_sq (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) {w : E}
    (hw : w ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) : w * w = 1 := by
  obtain ⟨K, fK, finK, chK, θ, hθ, -, -, h2⟩ := burnsideF4m_sp4_model hyp
  letI := fK
  haveI := finK
  haveI := chK
  rw [h2, burnsideF4d_oPPrime_map θ hθ, burnsideF4jb_ctr_map θ hθ,
    burnsideF4jb_ctr_oPPrime_Q2_one] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xs.1 hy
  rw [← map_mul, burnsideF4gSpInv_xs_sq, map_one]

theorem burnsideF4m_sp4_z12 (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) :
    (∃ z₁ ∈ ctr (oPPrime 2 (Gp ⊓ M₁)), z₁ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧ z₁ ≠ 1 ∧
      z₁ * z₁ = 1) ∧
    (∃ z₂ ∈ ctr (oPPrime 2 (Gp ⊓ M₂)), z₂ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧ z₂ ≠ 1 ∧
      z₂ * z₂ = 1) := by
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := burnsideF4j_bOne_injective hyp
  refine ⟨?_, ?_⟩
  · have hz := hyp.z_mem.1 (by decide)
    rw [burnsideF4j_Z1_eq hyp] at hz
    obtain ⟨z₀, hz₀M, hz₀Z, hz₀⟩ := mem_subImg.mp hz
    have hz1 : z₀ ≠ 1 := by
      rintro rfl
      apply hyp.z_inv.1
      rw [← hz₀]
      exact map_one _
    have hz2 : z₀ * z₀ = 1 := by
      have h := hyp.z_inv.2
      rw [← hz₀, ← map_mul] at h
      exact congrArg Subtype.val (hb1 (h.trans (map_one _).symm))
    exact ⟨z₀, hz₀Z, burnsideF4m_mem_ctr_S hyp.amalgam inf_le_left hz₀Z hz2, hz1, hz2⟩
  · obtain ⟨⟨w, hw, hw1⟩, -⟩ := burnsideF4jb_Z2_conj hyp.amalgam
    have hw2 := burnsideF4m_Z2_sq hyp.amalgam hw
    exact ⟨w, hw, burnsideF4m_mem_ctr_S hyp.amalgam inf_le_right hw hw2, hw1, hw2⟩

theorem burnsideF4m_F_4_35_Sp4_core (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z)
    (hT : IsSylowTwoOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ⊤)
    (hNT : ∀ n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup M) : Set M),
      n ∈ MiOne β ε ∧ n ∈ MiTwo β ε)
    (i j : ↥(M₁ ⊓ M₂)) (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hi1 : i ≠ 1) (hj1 : j ≠ 1) (hi2 : i * i = 1)
    (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  refine ⟨burnsideF4j_F_4_35_forward hyp i j hi hj, fun h => ?_⟩
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := burnsideF4j_bOne_injective hyp
  have hSM : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hSM1 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ := hSM.trans inf_le_left
  obtain ⟨⟨z₁, hz₁, hz₁S, hz₁1, hz₁2⟩, ⟨z₂, hz₂, hz₂S, hz₂1, hz₂2⟩⟩ := burnsideF4m_sp4_z12 hyp
  obtain ⟨-, hconjZ⟩ := (burnsideF4ja_lie_facts hyp.amalgam (by decide) (by decide)).2.2 rfl
  have hiG : (i : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hi).1
  have hjG : (j : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hj).1
  have hi1E : (i : E) ≠ 1 := fun h0 => hi1 (Subtype.ext h0)
  have hj1E : (j : E) ≠ 1 := fun h0 => hj1 (Subtype.ext h0)
  have hi2E : (i : E) * i = 1 := congrArg Subtype.val hi2
  have hj2E : (j : E) * j = 1 := congrArg Subtype.val hj2
  obtain ⟨gi, hgi, hgiZ⟩ := hconjZ i hiG hi1E hi2E
  obtain ⟨gj, hgj, hgjZ⟩ := hconjZ j hjG hj1E hj2E
  have hinvol : ∀ (g a : E), a ≠ 1 → a * a = 1 → g * a * g⁻¹ ≠ 1 ∧
      g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    intro g a ha1 ha2
    refine ⟨fun h0 => ha1 ?_, ?_⟩
    · calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
    · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [ha2]; group
  obtain ⟨hx1, hx2⟩ := hinvol gi i hi1E hi2E
  obtain ⟨hy1, hy2⟩ := hinvol gj j hj1E hj2E
  have hxM : gi * (i : E) * gi⁻¹ ∈ M₁ ⊓ M₂ := hSM hgiZ.1
  have hyM : gj * (j : E) * gj⁻¹ ∈ M₁ ⊓ M₂ := hSM hgjZ.1
  have hix := burnsideF4j_F_4_35_forward hyp i ⟨_, hxM⟩ hi hgiZ.1 ⟨gi, hgi, rfl⟩
  have hjy := burnsideF4j_F_4_35_forward hyp j ⟨_, hyM⟩ hj hgjZ.1 ⟨gj, hgj, rfl⟩
  have hxy := (hix.symm.trans h).trans hjy
  have hZT : ∀ (a : E) (ha : a ∈ M₁ ⊓ M₂), a ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) →
      bM β ε ⟨a, ha⟩ ∈ centerOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) := by
    intro a ha haZ
    show burnsideF4d_bOne β ε ⟨a, ha.1⟩ ∈ _
    rw [subImg_centerOf hb1 hSM1]
    exact mem_subImg_of_mem _ ha.1 haZ
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  obtain ⟨n, hn, hnxy⟩ := exists_normalizer_conj_of_central hT (hZT _ hxM hgiZ)
    (hZT _ hyM hgjZ) hc
  obtain ⟨hn1, hn2⟩ := hNT n hn
  have hn12 : n ∈ MiOne β ε ⊓ MiTwo β ε := ⟨hn1, hn2⟩
  rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj] at hn12
  obtain ⟨n₀, hn₀M, hn₀12, rfl⟩ := mem_subImg.mp hn12
  have hn₀xy : n₀ * (gi * (i : E) * gi⁻¹) * n₀⁻¹ = gj * (j : E) * gj⁻¹ := by
    have hmem : n₀ * (gi * (i : E) * gi⁻¹) * n₀⁻¹ ∈ M₁ :=
      M₁.mul_mem (M₁.mul_mem hn₀M hxM.1) (M₁.inv_mem hn₀M)
    have e : burnsideF4d_bOne β ε ⟨_, hmem⟩ = burnsideF4d_bOne β ε ⟨_, hyM.1⟩ := by
      have e1 : (⟨_, hmem⟩ : ↥M₁) = ⟨n₀, hn₀M⟩ * ⟨_, hxM.1⟩ * ⟨n₀, hn₀M⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
      exact hnxy
    exact congrArg Subtype.val (hb1 e)
  have hZ := burnsideF4m_conj_mem_Zj hyp.amalgam hn₀12
  have hZ' := burnsideF4m_conj_mem_Zj hyp.amalgam
    (show n₀⁻¹ ∈ M₁ ⊓ M₂ from (M₁ ⊓ M₂).inv_mem hn₀12)
  have hback : n₀⁻¹ * (gj * (j : E) * gj⁻¹) * n₀⁻¹⁻¹ = gi * (i : E) * gi⁻¹ := by
    rw [← hn₀xy]
    group
  have ht1 : gi * (i : E) * gi⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) ↔
      gj * (j : E) * gj⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) :=
    ⟨fun ha => hn₀xy ▸ hZ.1 _ ha, fun hb => hback ▸ hZ'.1 _ hb⟩
  have ht2 : gi * (i : E) * gi⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) ↔
      gj * (j : E) * gj⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) :=
    ⟨fun ha => hn₀xy ▸ hZ.2 _ ha, fun hb => hback ▸ hZ'.2 _ hb⟩
  obtain ⟨g, hg, hgxy⟩ := burnsideF4m_sp4_conj_of_type hyp.amalgam
    (fun w hw1 hw2 => burnsideF4m_Z1_inf_Z2 hyp hw1 hw2) hz₁ hz₁S hz₁1 hz₁2 hz₂ hz₂S hz₂1 hz₂2
    hgiZ hgjZ hx1 hx2 hy1 hy2 ht1 ht2
  refine ⟨gj⁻¹ * g * gi, Gp.mul_mem (Gp.mul_mem (Gp.inv_mem hgj) hg) hgi, ?_⟩
  calc gj⁻¹ * g * gi * (i : E) * (gj⁻¹ * g * gi)⁻¹
      = gj⁻¹ * (g * (gi * (i : E) * gi⁻¹) * g⁻¹) * gj := by group
    _ = gj⁻¹ * (gj * (j : E) * gj⁻¹) * gj := by rw [hgxy]
    _ = j := by group

theorem burnsideF4m_subImg_psi {K' : Type} [Group K'] (θ : E ≃* K') {N : Subgroup K'}
    {P : Subgroup E} (h : ∀ e, θ e ∈ N ↔ e ∈ P) (b : ↥P →* M) (X : Subgroup E) (hX : X ≤ P) :
    subImg (b.comp (burnsideF4m_psi θ h)) (X.map θ.toMonoidHom) = subImg b X := by
  ext g
  rw [mem_subImg, mem_subImg]
  constructor
  · rintro ⟨x, hxN, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨e, hX he, he, ?_⟩
    show b ⟨e, _⟩ = b (burnsideF4m_psi θ h ⟨θ e, hxN⟩)
    congr 1
    exact Subtype.ext (by rw [burnsideF4m_psi_apply]; simp)
  · rintro ⟨e, heP, heX, rfl⟩
    refine ⟨θ e, (h e).2 heP, ⟨e, heX, rfl⟩, ?_⟩
    show b (burnsideF4m_psi θ h ⟨θ e, _⟩) = b ⟨e, heP⟩
    congr 1
    exact Subtype.ext (by rw [burnsideF4m_psi_apply]; simp)

theorem burnsideF4m_sp4_NT_K {K' : Type} [Group K'] [Finite K']
    (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (hZ1 : burnsideF4m_Core1 Gp M₁)
    (hZ2 : burnsideF4m_Core2 .Sp4 Gp M₂) (hQ1 : pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁))
    (hQ2 : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂))
    (hQ12 : pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (θ : E ≃* K') {N1 N2 : Subgroup K'} (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁)
    (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) {T : Subgroup K'} {I : Finset K'} (L : F431SpLie T N1 N2 I) :
    ∀ n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup M) : Set M),
      n ∈ MiOne β ε ∧ n ∈ MiTwo β ε := by
  haveI := hyp.finite_M
  have hS := burnsideF4m_spGSetup hyp hZ1 hZ2 hQ1 hQ2 hQ12 θ h1 h2
  have hN1 : M₁.map θ.toMonoidHom = N1 := burnsideF4m_map_eq_of_iff θ h1
  have hN2 : M₂.map θ.toMonoidHom = N2 := burnsideF4m_map_eq_of_iff θ h2
  have hT : (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))).map θ.toMonoidHom = T := by
    rw [← L.O2N12, ← hN1, ← hN2, ← Subgroup.map_inf_eq _ _ θ.toMonoidHom θ.injective, ← hQ12]
    exact (burnsideF4j_pCoreOf_map θ.toMonoidHom θ.injective _).symm
  have e := burnsideF4m_subImg_psi θ h1 (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans inf_le_left))
  rw [hT] at e
  intro n hn
  rw [← e] at hn
  exact hS.normalizer_le L hn

theorem burnsideF4m_sp4_T_data_lie (hcore : burnsideF4m_LieCoreSp)
    (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) :
    IsSylowTwoOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ⊤ ∧
    ∀ n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup M) : Set M),
      n ∈ MiOne β ε ∧ n ∈ MiTwo β ε := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hodd := burnsideF4m_odd_index_Sp4_of hcore hyp hf
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT⟩ := burnsideF4j_exists_sylow (MiOne β ε ⊓ MiTwo β ε)
    have h38 := burnsideF4j_F_4_38_inst hyp hodd
      (burnsideF4j_genByTwo burnsideF4m_genByTwoRest hyp.amalgam hyp.not_G2d) hT
    have hTM := burnsideF4m_F_4_33 .Sp4 f E Gp M₁ M₂ Y β M ε z hyp T hT
    rw [h38.1, burnsideF4d_SinM_eq] at hTM
    exact hTM
  · obtain ⟨hZ1, hZ2, hQ1, hQ2, hQ12⟩ := hcore f E Gp M₁ M₂ hyp.amalgam hf
    obtain ⟨marking, h1m, h2m⟩ := burnsideF4g_marking (c := .Sp4) hyp.amalgam.toHypF_4_4g
    obtain ⟨TD, hTD⟩ := burnsideF4g_yamSp4 hf marking
    rw [← h1m, ← h2m] at hTD
    have hmodel := burnsideF4g_lieModel_Sp4 hf hyp.amalgam.model
    obtain ⟨θ, h1, h2⟩ := burnsideF4m_exists_theta hyp.amalgam hTD
    haveI : Finite ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hTD).K :=
      Finite.of_equiv E θ.toEquiv
    obtain ⟨T, I, L⟩ := f431SpLieProp f ↥Gp hmodel
      (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hTD).toLieAmalgamExt
      (burnsideF4m_odd_of hyp.amalgam hTD hodd)
    exact burnsideF4m_sp4_NT_K hyp hZ1 hZ2 hQ1 hQ2 hQ12 θ h1 h2 L

theorem burnsideF4m_sp4_T_data_two (hfacts : burnsideF4m_Sp2Facts) (htop : burnsideF4m_TopSp2)
    (hyp : HypF_4_31 .Sp4 1 Gp M₁ M₂ β ε z) :
    IsSylowTwoOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ⊤ ∧
    ∀ n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup M) : Set M),
      n ∈ MiOne β ε ∧ n ∈ MiTwo β ε := by
  have hGp := htop E Gp M₁ M₂ hyp.amalgam
  subst hGp
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  simp only [top_inf_eq]
  obtain ⟨hsh, -, -, -⟩ := hfacts E M₁ M₂ hyp.amalgam
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := burnsideF4j_bOne_injective hyp
  have hb2 : Function.Injective (burnsideF4d_bTwo β ε) := burnsideF4j_bTwo_injective hyp
  have hSM1 : pCoreOf 2 (M₁ ⊓ M₂) ≤ M₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hQ1S : pCoreOf 2 M₁ ≤ pCoreOf 2 (M₁ ⊓ M₂) := hsh.Q_le 0
  have hQ2S : pCoreOf 2 M₂ ≤ pCoreOf 2 (M₁ ⊓ M₂) := hsh.Q_le 1
  have hshM := burnsideF4m_spShape_subImg hb1 hsh hSM1
  have hT : IsSylowTwoOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (M₁ ⊓ M₂))) ⊤ := by
    have hS0 := (burnsideF4j_sylow_data hyp.amalgam).1
    simp only [top_inf_eq] at hS0
    have hS1 : IsSylowTwoOf (pCoreOf 2 (M₁ ⊓ M₂)) (M₁ ⊓ M₂) :=
      F7.isSylowTwoOf_mono_right hS0 (CFSG.LieType.BorelTits.pCoreOf_le 2 _) le_top
    have hS2 := (burnsideF4j_isSylow_subImg_iff (burnsideF4d_bOne β ε) hb1 hSM1
      inf_le_left).mpr hS1
    rw [← burnsideF4d_inter_eq β hyp.faithful ε hyp.inj] at hS2
    exact burnsideF4m_F_4_33 .Sp4 1 E ⊤ M₁ M₂ Y β M ε z hyp _ hS2
  have hN1 : Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) : Subgroup M) : Set M) = MiOne β ε := by
    have e : ctr (pCoreOf 2 (GiOne ⊤ β ε)) = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) := by
      rw [burnsideF4d_GiOne_eq, top_inf_eq, subImg_pCoreOf hb1 le_rfl]
      show centerOf _ = _
      rw [subImg_centerOf hb1 (hQ1S.trans hSM1),
        centerOf_eq_of_abelian (X := pCoreOf 2 M₁) (hsh.Q_abel 0)]
    rw [← e]
    exact (hyp.ha (Or.inl rfl)).1
  have hag : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂),
      burnsideF4d_bOne β ε ⟨g, h1⟩ = burnsideF4d_bTwo β ε ⟨g, h2⟩ :=
    fun g h1 h2 => burnsideF4m_bOne_eq_bTwo β ε g h1 h2
  have hN2 : Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) : Subgroup M) : Set M) = MiTwo β ε := by
    have e : ctr (pCoreOf 2 (GiTwo ⊤ β ε)) = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) := by
      rw [burnsideF4d_GiTwo_eq, top_inf_eq, subImg_pCoreOf hb2 le_rfl]
      show centerOf _ = _
      rw [subImg_centerOf hb2 (CFSG.LieType.BorelTits.pCoreOf_le 2 _),
        centerOf_eq_of_abelian (X := pCoreOf 2 M₂) (hsh.Q_abel 1)]
      exact (subImg_eq_of_agree hag (hQ2S.trans hSM1) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm
    rw [← e]
    exact (hyp.ha (Or.inl rfl)).2
  refine ⟨hT, fun n hn => ?_⟩
  have h0 : n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₁) : Subgroup M) : Set M) :=
    hshM.normalizer_le hT hn 0
  have h1 : n ∈ Subgroup.normalizer
      ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 M₂) : Subgroup M) : Set M) :=
    hshM.normalizer_le hT hn 1
  rw [hN1] at h0
  rw [hN2] at h1
  exact ⟨h0, h1⟩

theorem burnsideF4m_F_4_35_Sp4 (hcore : burnsideF4m_LieCoreSp) (hfacts : burnsideF4m_Sp2Facts)
    (htop : burnsideF4m_TopSp2) (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (i j : ↥(M₁ ⊓ M₂))
    (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hi1 : i ≠ 1) (hj1 : j ≠ 1) (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
  have hdata : IsSylowTwoOf (subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) ⊤ ∧
      ∀ n ∈ Subgroup.normalizer
        ((subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup M) : Set M),
        n ∈ MiOne β ε ∧ n ∈ MiTwo β ε := by
    by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_sp4_T_data_lie hcore hyp hf2
    · have hf : f = 1 := by omega
      subst hf
      exact burnsideF4m_sp4_T_data_two hfacts htop hyp
  exact burnsideF4m_F_4_35_Sp4_core hyp hdata.1 hdata.2 i j hi hj hi1 hj1 hi2 hj2

end F435Sp

end CFSG.ASVolI
