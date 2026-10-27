module

public import CFSG.RankThree.GF2n.Stroth80.Sec311ConjSL
public import CFSG.RankThree.GF2n.Stroth80.Sec311OmegaTrans
public import CFSG.RankThree.GF2n.Stroth80.Sec311SpTrans
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClCaseQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClData
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec311Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth311Conj_of_theoremX (h34 : Stroth34Statement) (hX : Classify.TheoremXStatement) :
    Stroth311ConjStatement := by
  classical
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  have hRt : Rt M (LB M Q B) t = ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)),
      conjSubgroup m (LB M Q B) := rfl
  suffices key : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m (LB M Q B) = conjSubgroup r (LB M Q B) by
    refine le_trans (le_of_eq hRt) (iSup₂_le fun m hm => iSup_le fun htm => ?_)
    obtain ⟨r, hr, heq⟩ := key m hm htm
    rw [heq]
    exact le_iSup₂_of_le r hr le_rfl
  intro m hm htm
  by_cases hV : Vt M (LB M Q B) B Z t ≤ QB B
  · exact hc.exists_conj_of_SL h34 hs hR hV hm htm
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c _ he => hc.smul_mem_img_Vt h t c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hs hV h hS
  have hSymp := sympRep_two_of_not_le_QB h34 hc hs hV
    (stroth310SympForm_of_34 h34 G M Q Z B hc n t hs hR hV)
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hq4 : 4 ≤ Nat.card (GaloisField 2 n') := by
    rw [hKZ]
    exact hc.hyp.q4
  have hdim : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) := by
    obtain ⟨K₁, _, _, hK₁, m₁', hm₁', φ₁, -, -, hsec⟩ := hSymp
    have hcardV := card_eq_of_sectionAct
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hsec
    have hcardM := M₀.card_eq (hc.Vt_le_Q t)
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
    have hfin : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
        Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_imgSub.symm)
    have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) =
        Nat.card (GaloisField 2 n') ^ Module.finrank (GaloisField 2 n')
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Module.natCard_eq_pow_finrank (K := GaloisField 2 n')
        (V := ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    rw [hcardV, hfin] at hcardM
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardM
    simp only [Fintype.card_sum, Fintype.card_fin] at h2
    rw [hK₁, hpow, hKZ] at h2
    have h3 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have h4 := Nat.pow_right_injective h3 h2
    omega
  have hH : D.ρ.range ≤ Classify.sympSubgroup D.F := by
    rintro _ ⟨r, rfl⟩
    exact D.isom r
  have hex : ∀ (m : G) (hm : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)),
      ∃ e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS), e ≠ 0 ∧
        (∀ v : M₀.E, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : GaloisField 2 n', v = s • (e : M₀.E)) ∧
        ((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ ≤
          Classify.pointRadSubgroup D.F e ∧
        Classify.ElationFull D.F
          ((((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ :
            Subgroup _) : Set _) e := fun m hm ht => D.elation_data h34 hs h hdim hm ht
  choose e he0 heB hepr heful using hex
  have h1M : (1 : G) ∈ M := M.one_mem
  have h1t : t ∈ conjSubgroup (1 : G) (LB M Q B) := by rw [conjSubgroup_one]; exact ht
  have heB1 : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : GaloisField 2 n', v = s • (e 1 h1M h1t : M₀.E) := by
    have := heB 1 h1M h1t
    rwa [conjSubgroup_one] at this
  have htrans : ∃ g ∈ D.ρ.range, ∃ c : GaloisField 2 n', c ≠ 0 ∧
      g (e 1 h1M h1t) = c • e m hm htm := by
    obtain ⟨P, hP0, hPspan, hPful, hPgen⟩ := hc.theoremX_data h34 hs h D hdim
    rcases hX (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) D.F hq4 D.nondeg D.alt
        hdim D.ρ.range hH P hP0 hPspan hPful hPgen with hsp | ⟨Qf, hQf, hΩ⟩
    · obtain ⟨g, hg, hge⟩ := Classify.exists_symp_apply_eq D.nondeg D.alt (he0 1 h1M h1t)
        (he0 m hm htm)
      exact ⟨g, hsp ▸ hg, 1, one_ne_zero, by rw [hge, one_smul]⟩
    · have hcomm : ⁅Classify.orthSubgroup Qf, Classify.orthSubgroup Qf⁆ ≤
          Classify.orthSubgroup Qf :=
        Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
            (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
      have hHQ : D.ρ.range ≤ Classify.orthSubgroup Qf := by rw [hΩ]; exact hcomm
      have hsing : ∀ (m' : G) (hm' : m' ∈ M) (ht' : t ∈ conjSubgroup m' (LB M Q B)),
          Qf (e m' hm' ht') = 0 := by
        intro m' hm' ht'
        obtain ⟨f₀, hf₀⟩ : ∃ f₀, D.F (e m' hm' ht') f₀ ≠ 0 := by
          by_contra hcon
          exact he0 m' hm' ht' (D.nondeg.1 _ fun y => by_contra fun hy => hcon ⟨y, hy⟩)
        obtain ⟨f, hef⟩ : ∃ f, D.F (e m' hm' ht') f = 1 :=
          ⟨(D.F (e m' hm' ht') f₀)⁻¹ • f₀, by
            rw [map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hf₀⟩
        exact Classify.quad_eq_zero_of_orth D.nondeg D.alt (by omega) hef (heful m' hm' ht') hQf
          (le_trans (Subgroup.map_le_range _ _) hHQ)
      set Pe : Set ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
        {x | ∃ (m' : G) (hm' : m' ∈ M) (ht' : t ∈ conjSubgroup m' (LB M Q B)),
          x = e m' hm' ht'} with hPe
      have hPe0 : ∀ x ∈ Pe, x ≠ 0 := by
        rintro x ⟨m', hm', ht', rfl⟩
        exact he0 m' hm' ht'
      have hPesing : ∀ x ∈ Pe, Qf x = 0 := by
        rintro x ⟨m', hm', ht', rfl⟩
        exact hsing m' hm' ht'
      have hPespan : Submodule.span (GaloisField 2 n') Pe = ⊤ := by
        rw [eq_top_iff]
        intro w _
        have hw : (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) := mem_imgSub.mp w.2
        rw [hc.img_Vt_eq t M₀] at hw
        have key : (⨆ (m' : G) (_ : m' ∈ M) (_ : t ∈ conjSubgroup m' (LB M Q B)),
            M₀.img (conjSubgroup m' B)) ≤ (Submodule.span (GaloisField 2 n')
              ((Subtype.val : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) → M₀.E) '' Pe)).toAddSubgroup
            := by
          refine iSup_le fun m' => iSup_le fun hm' => iSup_le fun ht' => ?_
          intro v hv
          obtain ⟨s, rfl⟩ := (heB m' hm' ht' v).mp hv
          exact Submodule.smul_mem _ s (Submodule.subset_span ⟨e m' hm' ht', ⟨m', hm', ht', rfl⟩,
            rfl⟩)
        exact (Submodule.apply_mem_span_image_iff_mem_span (f := (imgSub M₀
          (Vt M (LB M Q B) B Z t) hS).subtype) Subtype.val_injective).mp (key hw)
      have hPefull : ∀ x ∈ Pe, Classify.ElationFull D.F
          ((D.ρ.range : Set _) ∩ Classify.pointRad D.F x) x := by
        rintro x ⟨m', hm', ht', rfl⟩ φ hφ
        obtain ⟨g, hg, hgφ⟩ := heful m' hm' ht' φ hφ
        exact ⟨g, ⟨(Subgroup.map_le_range D.ρ _) hg, hepr m' hm' ht' hg⟩, hgφ⟩
      have hex1 : e 1 h1M h1t ∈ Pe := ⟨1, h1M, h1t, rfl⟩
      have hexm : e m hm htm ∈ Pe := ⟨m, hm, htm, rfl⟩
      obtain ⟨g, hgH, c, hc0, hgc⟩ := Classify.orbit_transitive_omega D.F D.nondeg D.alt hdim hQf
        D.ρ.range hHQ Pe hPe0 hPesing hPespan hPefull hex1 hexm
      exact ⟨g, hgH, c, hc0, hgc⟩
  obtain ⟨g, hg, c, hc0, hgc⟩ := htrans
  obtain ⟨r, rfl⟩ := hg
  refine ⟨r, r.2, hc.conj_LB_eq_of_img_eq (M₀ := M₀) hm (hc.Rt_le_M t r.2) fun v => ?_⟩
  rw [heB m hm htm, hc.img_conj_Rt_eq hs h D (e 1 h1M h1t) heB1 r v, hgc]
  have hv : ((c • e m hm htm : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) : M₀.E) =
      c • (e m hm htm : M₀.E) := rfl
  rw [hv]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s * c⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s * c, by rw [smul_smul]⟩

end CFSG.RankThree.GF2n.Stroth80
