module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Wrap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47GapAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Mod
import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
import CFSG.Quasithin.Vol2.Ch12Sec2Lem22C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_t_data (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hne : V₀ ≠ ⊥) :
    ∃ t ∈ V₀, t ≠ 1 ∧ t ∈ centralizer (D.T : Set G) ∧ centralizer ({t} : Set G) ≤ D.M := by
  classical
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hV₀M : V₀ ≤ D.M := hP.le.trans hP.le_M
  have hV₀pg : IsPGroup 2 V₀ := hP.elemAbelian₀.isPGroup
  have hV₀T : V₀ ≤ D.T := uc22p22na_le_sylow_of_normal D.sylowM hV₀M hP.le_normalizer₀ hV₀pg
  have hT₀ : D.T ≤ normalizer (V₀ : Set G) := D.sylowM.le.trans hP.le_normalizer₀
  obtain ⟨a, haV₀, ha1, haT⟩ :=
    CFSG.Quasithin.H13.Lem22.exists_ne_one_mem_centralizer D.sylowM.isPGroup hV₀T hT₀ hne
  refine ⟨a, haV₀, ha1, haT, ?_⟩
  rcases hS.setting.hyp151.hyp125.1 with ⟨-, hbot⟩ | ⟨-, hcu, -⟩
  · exact absurd hbot hne
  · exact (hcu a (hV₀T haV₀) (fun t ht => ((Subgroup.mem_centralizer_iff.1 haT) t ht).symm)
      ha1).1

theorem s16c1_G47_mem_M_of_conj (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {t : G} (htV₀ : t ∈ V₀) (ht1 : t ≠ 1) {h : G}
    (hht : h * t * h⁻¹ ∈ V₀) : h ∈ D.M := by
  have hne : V₀ ≠ ⊥ := by
    intro hb
    rw [hb] at htV₀
    exact ht1 (Subgroup.mem_bot.1 htV₀)
  have hmem : t ∈ V₀ ⊓ conjSubgroup V₀ h :=
    Subgroup.mem_inf.2 ⟨htV₀, mem_conjSubgroup_iff.2 hht⟩
  have hne2 : V₀ ⊓ conjSubgroup V₀ h ≠ ⊥ := fun hb => ht1 (Subgroup.mem_bot.1 (hb ▸ hmem))
  have hconj : conjSubgroup V₀ h = V₀ := s16c1_ti_V₀ hS hne h hne2
  have hnorm : h ∈ normalizer (V₀ : Set G) :=
    (conjSubgroup_eq_iff_mem_normalizer (A := V₀) (g := h)).1 hconj
  rwa [normalizer_eq_of_inCalV D (s16c1_inCalV0_of_sect16 hS hne).1] at hnorm

theorem s16c1_G47_gap_ne (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M)
    (ctx : G47Ctx D V₀ V L hV x) (h46 : Concl1646 L x.val) (h47 : Concl1647 V x.val)
    (hne : V₀ ≠ ⊥) (h47a : Concl1647aNe D V₀ V x.val) : False := by
  classical
  have hS := ctx.sect
  have hSt := G47Star.of_ctx hsp hL ctx h46.2.2.1
  have hEcent : eTwo D V₀ x.val ≤
      centralizer (pCoreOf 2 (centralizer ({x.val} : Set G)) : Set G) :=
    s16c1_eTwo_le_centralizer D ctx.sylow
  have hEinv : ∀ h ∈ centralizer ({x.val} : Set G),
      conjSubgroup (eTwo D V₀ x.val) h = eTwo D V₀ x.val := fun h hh => by
    simpa only [eTwo] using s16c1_conjSubgroup_hConjClosure (z := x.val)
      (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G)) hh
  have hHE : centralizer ({x.val} : Set G) ≤ normalizer (eTwo D V₀ x.val : Set G) :=
    fun h hh => (conjSubgroup_eq_iff_mem_normalizer (A := eTwo D V₀ x.val) (g := h)).1
      (hEinv h hh)
  obtain ⟨ρ, hρ⟩ := s16c1_G47_exists_action hHE hEcent
  have hE : ∀ e : ↥(eTwo D V₀ x.val), e * e = 1 := fun e =>
    Subtype.ext (by simpa [pow_two] using h47a.1.2 (e : G) e.2)
  obtain ⟨t, htV₀, ht1, htT, htM⟩ := s16c1_G47_t_data D hS hne
  have htE : t ∈ eTwo D V₀ x.val :=
    s16c1_G47_le_hConjClosure x.val _ (Subgroup.mem_inf.2 ⟨htV₀, Subgroup.mem_centralizer_iff.2
      fun s hs => (Subgroup.mem_centralizer_iff.1 htT) s (Subgroup.mem_inf.1 hs).1⟩)
  have htU : t ∈ uTwo D V₀ x.val := Subgroup.mem_inf.2 ⟨htV₀, htE⟩
  have hδ : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, ∀ e : ↥(eTwo D V₀ x.val),
      ((ρ u e * e : ↥(eTwo D V₀ x.val)) : G) ∈ uTwo D V₀ x.val := by
    intro u hu e
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hu
    have hcomm : ⁅(w : G), (e : G)⁆ ∈ uTwo D V₀ x.val :=
      h47a.2.2 (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hw) e.2)
    have he : (e : G)⁻¹ = (e : G) :=
      inv_eq_of_mul_eq_one_right (by simpa using congrArg Subtype.val (hE e))
    rw [Subgroup.coe_mul, hρ w e]
    rw [commutatorElement_def, he] at hcomm
    exact hcomm
  have hkerB : ∀ v : Bar2 (centralizer ({x.val} : Set G)), ρ v = 1 →
      v ∈ starImg (centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G) ⊓ D.M) := by
    intro v hv
    obtain ⟨y, rfl⟩ :=
      QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) v
    have h1 := congrArg
      (fun f : MulAut ↥(eTwo D V₀ x.val) => ((f ⟨t, htE⟩ : ↥(eTwo D V₀ x.val)) : G)) hv
    simp only [MulAut.one_apply] at h1
    rw [hρ y ⟨t, htE⟩] at h1
    have hyc : (y : G) ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun a ha => by
        rw [Set.mem_singleton_iff.1 ha]
        exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨y.2, htM hyc⟩), rfl⟩
  have hD : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, u ≠ 1 → ∃ e : ↥(eTwo D V₀ x.val),
      ρ u e * e ≠ 1 := by
    intro u hu hu1
    by_contra hall
    push Not at hall
    exact hu1 (s16c1_G47_ker_conj ρ hE hkerB (fun b hb => s16c1_G47_conj_eq_of_two hu1
      (s16c1_G47_two_elems h47.1 hu hu1) (hSt.conj_B b hb u hu)) hall hSt.pCore_bot (hSt.sq u hu))
  have hTI : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, u ≠ 1 →
      ∀ r : Bar2 (centralizer ({x.val} : Set G)), r * u * r⁻¹ ≠ u → ∀ e e' : ↥(eTwo D V₀ x.val),
        ρ r (ρ u e * e) = ρ u e' * e' → ρ u e * e = 1 := by
    intro u hu hu1 r hr e e' hee'
    obtain ⟨h, rfl⟩ :=
      QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) r
    have hd := hδ u hu e
    have hd' : (h : G) * ((ρ u e * e : ↥(eTwo D V₀ x.val)) : G) * (h : G)⁻¹ ∈ uTwo D V₀ x.val := by
      have h1 := hδ u hu e'
      rw [← hee', hρ h (ρ u e * e)] at h1
      exact h1
    rcases h47a.2.1 (h : G) h.2 with hconj | hbot
    · exfalso
      have hht : (h : G) * t * (h : G)⁻¹ ∈ uTwo D V₀ x.val :=
        mem_conjSubgroup_iff.1 (by rw [hconj]; exact htU)
      have hM : (h : G) ∈ D.M := s16c1_G47_mem_M_of_conj D hS htV₀ ht1 (hht.1 : _ ∈ V₀)
      have hB : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G))) h ∈
          starImg (centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G) ⊓ D.M) :=
        Subgroup.mem_map.2 ⟨h, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h.2, hM⟩), rfl⟩
      exact hr (s16c1_G47_conj_eq_of_two hu1 (s16c1_G47_two_elems h47.1 hu hu1)
        (hSt.conj_B _ hB u hu))
    · apply Subtype.ext
      have hmem : ((ρ u e * e : ↥(eTwo D V₀ x.val)) : G) ∈
          uTwo D V₀ x.val ⊓ conjSubgroup (uTwo D V₀ x.val) (h : G) :=
        Subgroup.mem_inf.2 ⟨hd, mem_conjSubgroup_iff.2 hd'⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
  have hSc : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, u ≠ 1 →
      ∀ c : Bar2 (centralizer ({x.val} : Set G)), ∀ q : ℕ, q.Prime → 5 ≤ q → orderOf c = q →
        c * u = u * c →
        (∀ y ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val), c * y = y * c) →
          ∀ e : ↥(eTwo D V₀ x.val), ρ c (ρ u e * e) = ρ u e * e := by
    intro u hu hu1 c q hq h5 hcq hcu _ e
    have hiter : ∀ n : ℕ, ∀ y : ↥(eTwo D V₀ x.val), (⇑(ρ c))^[n] y = ρ (c ^ n) y := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih =>
          intro y
          rw [Function.iterate_succ_apply', ih, pow_succ', map_mul, MulAut.mul_apply]
    have hcq1 : c ^ q = 1 := hcq ▸ pow_orderOf_eq_one c
    have hfq : ∀ y : ↥(eTwo D V₀ x.val), (⇑(ρ c))^[q] y = y := by
      intro y
      rw [hiter, hcq1, map_one, MulAut.one_apply]
    let S : Set ↥(eTwo D V₀ x.val) := Set.range fun e' => ρ u e' * e'
    have hmaps : ∀ y ∈ S, ρ c y ∈ S := by
      rintro _ ⟨e', rfl⟩
      refine ⟨ρ c e', ?_⟩
      have h1 : ρ u (ρ c e') = ρ c (ρ u e') := by
        have h2 : ρ (u * c) e' = ρ (c * u) e' := by rw [hcu]
        simpa only [map_mul, MulAut.mul_apply] using h2
      show ρ u (ρ c e') * ρ c e' = ρ c (ρ u e' * e')
      rw [map_mul, h1]
    have hS4 : S.ncard ≤ 4 := by
      have hsub : Subtype.val '' S ⊆ (V₀ : Set G) := by
        rintro _ ⟨_, ⟨e', rfl⟩, rfl⟩
        exact (Subgroup.mem_inf.1 (hδ u hu e')).1
      have h1 : (Subtype.val '' S).ncard = S.ncard :=
        Set.ncard_image_of_injective S Subtype.val_injective
      have h2 : (Subtype.val '' S).ncard ≤ (V₀ : Set G).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : (V₀ : Set G).ncard = Nat.card ↥V₀ := (Nat.card_coe_set_eq (V₀ : Set G)).symm
      have h4 : Nat.card ↥V₀ ≤ 4 := Sixteen21.card_le_four_of_hyp16 hS.setting.hyp16
      omega
    exact s16c1_G47_fix_of_prime_iterate (f := (ρ c : ↥(eTwo D V₀ x.val) → ↥(eTwo D V₀ x.val)))
      hS4 (Set.toFinite S) hq h5 hfq hmaps _ ⟨e, rfl⟩
  exact s16c1_G47_wrap hsp hL ctx h46 h47 hE ρ hD hTI hSc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
