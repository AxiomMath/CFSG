module

public import CFSG.RankThree.GF2n.Stroth80.Sec311SL
public import CFSG.RankThree.GF2n.Stroth80.Sec311SpTorus
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClCaseQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClData
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem torus_finish (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    (e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    (heB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • (e : M₀.E))
    (hepr : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map D.ρ ≤
      Classify.pointRadSubgroup D.F e)
    (a : K) (τ : ↥(Rt M (LB M Q B) t)) (hτe : D.ρ τ e = a • e)
    (hfree : ∀ g ∈ Classify.pointRadSubgroup D.F e, D.ρ τ * g = g * D.ρ τ → g = 1) :
    (τ : G) ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
      ∀ l ∈ LB M Q B, ⁅(τ : G), l⁆ ∈ hc.CN t → l ∈ hc.CN t := by
  classical
  have hτM : (τ : G) ∈ M := hc.Rt_le_M t τ.2
  have hτH : (τ : G) ∈ H0 M Z := hc.Rt_le_H0 t τ.2
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  refine ⟨?_, ?_⟩
  · refine (hc.mem_normalizer_LB_iff' hs.width hs.n_gt hs.noA2 hτM).mpr ?_
    have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hu))
    have hZn : ∀ a ∈ M, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a ha z hz =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha) z).mp hz
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
    have e1 : (τ : G) * (u * z) * (τ : G)⁻¹ =
        ((τ : G) * u * (τ : G)⁻¹) * ((τ : G) * z * (τ : G)⁻¹) := by group
    rw [e1]
    refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right (hZn _ hτM z hz))
    have huQ : u ∈ Q := hc.le hu
    have huV : u ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.mem hu
    have hw : M₀.π u ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS :=
      mem_imgSub.mpr (M₀.pi_mem_img huV huQ)
    obtain ⟨s, hs'⟩ := (heB _).mp (M₀.pi_mem_img hu huQ)
    obtain ⟨hw', hρ⟩ := D.ρ_apply τ (φ₀ ⟨τ, hτH⟩) (fun x hx => hφπ ⟨τ, hτH⟩ x hx)
      ⟨M₀.π u, hw⟩
    have hwe : (⟨M₀.π u, hw⟩ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) = s • e :=
      Subtype.ext hs'
    have h2 : ((D.ρ τ ⟨M₀.π u, hw⟩ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) : M₀.E) =
        (φ₀ ⟨τ, hτH⟩) (M₀.π u) := by rw [hρ]
    have h3 : D.ρ τ ⟨M₀.π u, hw⟩ = (s * a) • e := by
      rw [hwe, map_smul, hτe, smul_smul]
    rw [h3] at h2
    have h4 : M₀.π ((τ : G) * u * (τ : G)⁻¹) = (s * a) • (e : M₀.E) := by
      rw [hφπ ⟨τ, hτH⟩ u huQ, ← h2]
      rfl
    have hxQ : (τ : G) * u * (τ : G)⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hτM).1 u huQ
    exact (M₀.mem_img_iff (le_sup_right : Z ≤ B ⊔ Z) hxQ).mp
      (M₀.img_mono le_sup_left ((heB _).mpr ⟨s * a, h4⟩))
  · intro l hl hcomm
    have hl' : (⟨l, hLR hl⟩ : ↥(Rt M (LB M Q B) t)) ∈
        (LB M Q B).subgroupOf (Rt M (LB M Q B) t) := Subgroup.mem_subgroupOf.mpr hl
    have hmem : D.ρ ⟨l, hLR hl⟩ ∈ Classify.pointRadSubgroup D.F e := hepr ⟨_, hl', rfl⟩
    have hc1 : ⁅τ, (⟨l, hLR hl⟩ : ↥(Rt M (LB M Q B) t))⁆ ∈ D.ρ.ker := by
      rw [D.ker, Subgroup.mem_subgroupOf]
      exact hcomm
    have hc2 : ⁅D.ρ τ, D.ρ ⟨l, hLR hl⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hc1
    have hc3 : D.ρ τ * D.ρ ⟨l, hLR hl⟩ = D.ρ ⟨l, hLR hl⟩ * D.ρ τ :=
      commutatorElement_eq_one_iff_mul_comm.mp hc2
    have h1 : D.ρ ⟨l, hLR hl⟩ = 1 := hfree _ hmem hc3
    have h2 : (⟨l, hLR hl⟩ : ↥(Rt M (LB M Q B) t)) ∈ D.ρ.ker := h1
    rw [D.ker, Subgroup.mem_subgroupOf] at h2
    exact h2

theorem stroth311Torus_of_theoremX (h34 : Stroth34Statement) (hX : Classify.TheoremXStatement) :
    Stroth311TorusStatement := by
  classical
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR hnot
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c _ he => hc.smul_mem_img_Vt h t c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hs hnot h hS
  have hSymp := sympRep_two_of_not_le_QB h34 hc hs hnot
    (stroth310SympForm_of_34 h34 G M Q Z B hc n t hs hR hnot)
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hq4 : 4 ≤ Nat.card (GaloisField 2 n') := by
    rw [hKZ]
    exact hc.hyp.q4
  have hdim : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) := by
    obtain ⟨K₁, _, _, hK₁, m₁, hm₁, φ₁, -, -, hsec⟩ := hSymp
    have hcardV := card_eq_of_sectionAct (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
      hsec
    have hcardM := M₀.card_eq (hc.Vt_le_Q t) (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B)
      (t := t))
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
  obtain ⟨P, hP0, hPspan, hPful, hPgen⟩ := hc.theoremX_data h34 hs h D hdim
  have hH : D.ρ.range ≤ Classify.sympSubgroup D.F := by
    rintro _ ⟨r, rfl⟩
    exact D.isom r
  obtain ⟨e, he0, heB, hepr, heful⟩ := D.elation_data h34 hs h hdim (m := 1) M.one_mem
    (by rw [conjSubgroup_one]; exact ht)
  rw [conjSubgroup_one] at heB hepr heful
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, D.F e f₀ ≠ 0 := by
    by_contra hcon
    exact he0 (D.nondeg.1 e fun y => by_contra fun hy => hcon ⟨y, hy⟩)
  obtain ⟨f, hef⟩ : ∃ f, D.F e f = 1 :=
    ⟨(D.F e f₀)⁻¹ • f₀, by rw [map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hf₀⟩
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_one_of_four_le_card hq4
  rcases hX (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) D.F hq4 D.nondeg D.alt
      hdim D.ρ.range hH P hP0 hPspan hPful hPgen with hsp | ⟨Qf, hQf, hΩ⟩
  · obtain ⟨τb, hiso, hτe, hfree⟩ := Classify.exists_torus_symp D.nondeg D.alt hef ha0 ha1
    have hτr : τb ∈ D.ρ.range := by
      rw [hsp]
      exact hiso
    obtain ⟨τ, hτ⟩ := hτr
    obtain ⟨hnorm, hfix⟩ := torus_finish h34 hs h D e heB hepr a τ (by rw [hτ]; exact hτe)
      (by rw [hτ]; exact hfree)
    exact ⟨τ, τ.2, hnorm, hfix⟩
  · have hnd' : Qf.polarBilin.Nondegenerate := hQf ▸ D.nondeg
    have hcomm : ⁅Classify.orthSubgroup Qf, Classify.orthSubgroup Qf⁆ ≤
        Classify.orthSubgroup Qf :=
      Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
          (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
    have hAQ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map D.ρ ≤
        Classify.orthSubgroup Qf := by
      intro g hg
      have hg' : g ∈ D.ρ.range := (Subgroup.map_le_range D.ρ _) hg
      rw [hΩ] at hg'
      exact hcomm hg'
    have hQe : Qf e = 0 :=
      Classify.quad_eq_zero_of_orth D.nondeg D.alt (by omega) hef heful hQf hAQ
    have hfe : D.F f e = 1 := by
      rw [← Classify.form_comm D.alt e f]
      exact hef
    have hQf' : Qf (f + Qf f • e) = 0 := by
      rw [Classify.qf_add hQf, Classify.qf_smul, hQe, map_smul, smul_eq_mul, hfe]
      linear_combination (Qf f) * (Classify.two_eq_zero_K (K := GaloisField 2 n'))
    have hef' : Qf.polarBilin e (f + Qf f • e) = 1 := by
      rw [hQf, map_add, map_smul, hef, Classify.form_self D.alt e]
      simp
    obtain ⟨τb, hτo, hτe, hfree⟩ := Classify.exists_torus_orth hnd' hQe hQf' hef' ha0 ha1
    rw [hQf] at hfree
    have hτr : τb ∈ D.ρ.range := by
      rw [hΩ]
      exact hτo
    obtain ⟨τ, hτ⟩ := hτr
    obtain ⟨hnorm, hfix⟩ := torus_finish h34 hs h D e heB hepr a τ (by rw [hτ]; exact hτe)
      (by rw [hτ]; exact hfree)
    exact ⟨τ, τ.2, hnorm, hfix⟩

end CFSG.RankThree.GF2n.Stroth80
