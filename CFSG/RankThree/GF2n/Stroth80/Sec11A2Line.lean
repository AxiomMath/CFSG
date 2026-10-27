module

public import CFSG.RankThree.GF2n.Stroth80.Sec114
public import CFSG.RankThree.GF2n.Smith81.LinTLCentralizer
public import CFSG.RankThree.GF2n.Smith81.LinSetup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section LinAlg

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem exists_fixed_not_perp (M₀ : Tim79.QuadModel Q Z K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e) {b : M₀.E}
    (hb : b ∉ LinearMap.range (T - 1)) : ∃ f₀, T f₀ = f₀ ∧ M₀.B f₀ b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hrefl : M₀.B.IsRefl := fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hnd : M₀.B.Nondegenerate :=
    ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  apply hb
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl (LinearMap.range (T - 1))]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro f hf
  have hfix : T f = f := by
    have hsa : ∀ e, M₀.B e (T f) = M₀.B (T e) f := fun e => by
      have := Tim79.QuadModel.B_iso hT e (T f)
      rw [hT2] at this
      exact this.symm
    have h0 : ∀ e, M₀.B (T f - f) e = 0 := fun e => by
      have h1 : M₀.B (T e - e) f = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hf) (T e - e) ⟨e, by
          simp [LinearMap.sub_apply]⟩
      rw [map_sub, LinearMap.sub_apply] at h1
      rw [Tim79.QuadModel.B_comm, map_sub, hsa e]
      linear_combination -h1
    exact sub_eq_zero.mp (M₀.nondeg _ h0)
  exact hcon f hfix

end LinAlg

section A2Line

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.B_le_commutator_of_a2 (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z := by
  classical
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, hb0, hbs, hBline, hcent, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have hLH : ∀ t ∈ LB M Q B, t ∈ H0 M Z := fun t ht => hc.LB_le_H0 ht
  let Tl : ↥(LB M Q B) → (M₀.E ≃ₗ[K] M₀.E) := fun t => φ ⟨t, hLH t t.2⟩
  have hTπ : ∀ (t : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((t : G) * x * (t : G)⁻¹) = Tl t (M₀.π x) :=
    fun t x hx => hφπ ⟨t, hLH t t.2⟩ x hx
  have hQn : ∀ t : G, t ∈ LB M Q B → ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.LB_le_M ht)) x).mp hx
  have hQn' : ∀ t : G, t ∈ LB M Q B → ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := fun t ht x hx => by
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (M.inv_mem (hc.LB_le_M ht))) x).mp hx
    simpa using this
  have hcomm : ∀ (s t : ↥(LB M Q B)) (e : M₀.E), Tl s (Tl t e) = Tl t (Tl s e) := by
    intro s t e
    have h1 : φ ⁅(⟨s, hLH s s.2⟩ : ↥(H0 M Z)), ⟨t, hLH t t.2⟩⁆ = 1 := by
      rw [hφker]
      show ⁅(s : G), (t : G)⁆ ∈ Q
      exact Subgroup.commutator_le.mp hc.commutator_LB_le_Q _ s.2 _ t.2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) h1
    simpa [LinearEquiv.mul_apply] using this
  set a' : ↥(LB M Q B) := ⟨a, ha⟩ with ha'
  have hT2 : ∀ e, Tl a' (Tl a' e) = e := by
    intro e
    have h1 : φ ((⟨a, hLH a ha⟩ : ↥(H0 M Z)) * ⟨a, hLH a ha⟩) = 1 := by
      rw [hφker]
      show a * a ∈ Q
      have := hc.sq_mem_Q_of_mem_LB ha
      rwa [pow_two] at this
    rw [map_mul] at h1
    have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) h1
    simpa [LinearEquiv.mul_apply] using this
  have hfix : ∀ t : ↥(LB M Q B), Tl t b = b ∧
      ∀ e ∈ M₀.img (Q ⊓ QB B), ∃ c : K, Tl t e - e = c • b :=
    fun t => hc.LB_act_fix_line h hBline t.2 (T := (Tl t : M₀.E →ₗ[K] M₀.E)) (hTπ t)
  have hperp : ∀ (t : ↥(LB M Q B)) (f : M₀.E), M₀.B f b = 0 →
      Tl t f - f ∈ M₀.img (Q ⊓ QB B) := by
    intro t f hf
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj f
    have hyC : y ∈ Subgroup.centralizer (B : Set G) := (hcent y hyQ).mpr hf
    have hd : ⁅(t : G), y⁆ ∈ Q ⊓ QB B := hc.comm_mem_inf_of_mem_LB t.2 ⟨hyQ, hyC⟩
    have hdQ : ⁅(t : G), y⁆ ∈ Q := (Subgroup.mem_inf.mp hd).1
    have hkd : ⁅(t : G), y⁆ * y = (t : G) * y * (t : G)⁻¹ := by
      rw [commutatorElement_def]; group
    have h2 := M₀.π_mul _ hdQ _ hyQ
    rw [hkd, hTπ t y hyQ] at h2
    have h3 : M₀.π ⁅(t : G), y⁆ = Tl t (M₀.π y) - M₀.π y := eq_sub_of_add_eq h2.symm
    rw [← h3]
    exact M₀.pi_mem_img hd hdQ
  have hbW : b ∈ LinearMap.range ((Tl a' : M₀.E →ₗ[K] M₀.E) - 1) := by
    by_contra hbW
    obtain ⟨f₀, hf₀, hf₀b⟩ := exists_fixed_not_perp M₀ (T := (Tl a' : M₀.E →ₗ[K] M₀.E))
      (fun e => hφiso ⟨a, hLH a ha⟩ e) hT2 hbW
    have hf₀' : Tl a' f₀ = f₀ := hf₀
    have hDW : ∀ e, Tl a' e - e ∈ M₀.img (Q ⊓ QB B) := by
      intro e
      set c : K := M₀.B e b / M₀.B f₀ b with hc_def
      have hef : M₀.B (e - c • f₀) b = 0 := by
        rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hc_def,
          div_mul_cancel₀ _ hf₀b, sub_self]
      have h1 := hperp a' _ hef
      have h2 : Tl a' e - e = Tl a' (e - c • f₀) - (e - c • f₀) := by
        simp only [map_sub, map_smul, hf₀']
        abel
      rwa [h2]
    have hW0 : ∀ (t : ↥(LB M Q B)) (e : M₀.E), Tl t (Tl a' e - e) = Tl a' e - e := by
      intro t e
      obtain ⟨c, hc'⟩ := (hfix t).2 _ (hDW e)
      have hmem : Tl t (Tl a' e - e) - (Tl a' e - e) ∈
          LinearMap.range ((Tl a' : M₀.E →ₗ[K] M₀.E) - 1) := by
        refine ⟨Tl t e - e, ?_⟩
        have e1 : ((Tl a' : M₀.E →ₗ[K] M₀.E) - 1) (Tl t e - e) =
            Tl a' (Tl t e) - Tl a' e - (Tl t e - e) := by
          simp only [LinearMap.sub_apply, map_sub, Module.End.one_apply, LinearEquiv.coe_coe]
          abel
        rw [e1, hcomm a' t e, map_sub]
        abel
      have hc0 : c = 0 := by
        by_contra hc0
        apply hbW
        have h4 : c • b ∈ LinearMap.range ((Tl a' : M₀.E →ₗ[K] M₀.E) - 1) := hc' ▸ hmem
        have h5 := Submodule.smul_mem _ c⁻¹ h4
        rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h5
      rw [hc0, zero_smul, sub_eq_zero] at hc'
      exact hc'
    have hcomQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hyM : a ^ k ∈ M := M.zpow_mem (hc.LB_le_M ha) k
      have e : ⁅x, a ^ k⁆ = x * ((a ^ k) * x⁻¹ * (a ^ k)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) x⁻¹).mp
        (Q.inv_mem hx))
    have hY : ⁅Q, Subgroup.zpowers a⁆ ⊔ Z ≤ B ⊔ Z := by
      intro y hy
      obtain ⟨hyQ, hyimg⟩ := stroth_sup_le_lift h hcomQ hy
      have hyW : M₀.π y ∈ LinearMap.range ((Tl a' : M₀.E →ₗ[K] M₀.E) - 1) :=
        (Tim79.QuadModel.mem_img_commutator_zpowers (Tl a') (hQn a ha) (hQn' a ha)
          (hTπ a')).mp hyimg
      obtain ⟨e, he⟩ := hyW
      have he' : M₀.π y = Tl a' e - e := by
        rw [← he]; simp [LinearMap.sub_apply]
      have hyD : M₀.π y ∈ M₀.img (Q ⊓ QB B) := by
        rw [he']; exact hDW e
      have hyQB : y ∈ Q ⊓ QB B :=
        (M₀.mem_img_iff (le_inf hc.Z_le_Q hc.Z_le_QB.1) hyQ).mp hyD
      refine hc.mem_sup_of_comm_LB_mem_Z' hyQB fun l hl => ?_
      have hfixy : Tl ⟨l, hl⟩ (M₀.π y) = M₀.π y := by
        rw [he']; exact hW0 ⟨l, hl⟩ e
      have h1 : ⁅l, y⁆ ∈ Z := (M₀.comm_mem_iff hyQ (hQn l hl y hyQ)).mpr
        ((hTπ ⟨l, hl⟩ y hyQ).trans hfixy)
      rw [← commutatorElement_inv l y]
      exact Z.inv_mem h1
    have hBn : B ≤ Subgroup.normalizer (Z : Set G) :=
      le_trans hc.le (Smith81.Q_le_normalizer_of_Z_le hc.hyp le_rfl hc.Z_le_Q)
    have hBcard : Nat.card ↥B = Nat.card ↥Z := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup]
    have hcardBZ : Nat.card ↥(B ⊔ Z) = Nat.card ↥Z ^ 2 := by
      have h5 := Smith81.card_sup_mul_card_inf_of_normalizer hBn
      rw [hc.inf_eq_bot, Subgroup.card_bot, mul_one, hBcard, sup_comm] at h5
      rw [h5, sq]
    have hq1 : 1 < Nat.card ↥Z := by
      have := hc.hyp.q4
      omega
    have hle := Subgroup.card_le_of_le hY
    rw [hA.2.2.2.1, hcardBZ] at hle
    have := (Nat.pow_le_pow_iff_right hq1).mp hle
    omega
  intro u hu
  have huQ : u ∈ Q := hc.le hu
  obtain ⟨s, hs⟩ := (hBline _).mp (M₀.pi_mem_img hu huQ)
  have hW : M₀.π u ∈ LinearMap.range ((Tl a' : M₀.E →ₗ[K] M₀.E) - 1) := by
    rw [hs]
    exact Submodule.smul_mem _ s hbW
  have h1 : M₀.π u ∈ M₀.img ⁅Q, Subgroup.zpowers a⁆ :=
    (Tim79.QuadModel.mem_img_commutator_zpowers (Tl a') (hQn a ha) (hQn' a ha)
      (hTπ a')).mpr hW
  exact (M₀.mem_img_iff (le_sup_right : Z ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z) huQ).mp
    (M₀.img_mono le_sup_left h1)

theorem strothA2Line_holds : StrothA2LineStatement := by
  intro G _ _ M Q Z B hc n _ _ a ha hA
  exact hc.B_le_commutator_of_a2 ha hA

theorem stroth114_holds : Stroth114Statement := stroth114_of_line strothA2Line_holds

end A2Line

end CFSG.RankThree.GF2n.Stroth80
