module

public import CFSG.Quasithin.H13.L32NLem14324t
public import CFSG.Quasithin.H13.L32NM22Facts
public import CFSG.Quasithin.Background.HM22Recog
public import CFSG.Quasithin.Background.G11FixHolds
public import CFSG.Milestones.ASVolI.G11

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

theorem false_of_concl13S_of_card {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (h13 : G11.SzG11S.G112Concl13S Γ) (hXΓ : X ≤ Γ)
    (hsq : ∀ x ∈ X, x * x = 1) (hX : 64 ≤ Nat.card X) : False := by
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.Mathieu.M22Link.exists_linearEquiv_m22_of_normal
    h13.1.1 h13.1.2 h13.2.2
  have hf : Function.Injective (L14411.matOfN e) := L14411.matOfN_injective e
  have hY : X.map (L14411.matOfN e) ≤ L1442M.m22 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ, hxγ⟩ := (he x).1 (hXΓ hx)
    rw [(L14411.matOfN_eq_iff e x γ).2 hxγ]
    exact hγ
  have hYsq : ∀ y ∈ X.map (L14411.matOfN e), y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  have hcard := M22Facts.m22_card_le hY hYsq
  rw [Subgroup.card_map_of_injective hf] at hcard
  norm_num at hcard
  omega

theorem isG2NaturalModule_gf21_of_zmod2 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G11.IsG2NaturalModule H (quasithinG2 (ZMod 2))) :
    G11.IsG2NaturalModule H (quasithinG2 (GaloisField 2 1)) := by
  obtain ⟨φ, π, h1, h2, h3⟩ := h
  let e : ZMod 2 ≃+* GaloisField 2 1 := (GaloisField.equivZmodP 2).toRingEquiv.symm
  have hdec : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let L₀ : quasithinZorn (GaloisField 2 1) →+ quasithinZorn (ZMod 2) :=
    AddMonoidHom.mk' (JonesParshall.zornMap e.symm) (JonesParshall.zornMap_add e.symm)
  let L : quasithinZorn (GaloisField 2 1) →ₗ[ZMod 2] quasithinZorn (ZMod 2) :=
    { L₀ with
      map_smul' := fun c x => by
        rcases hdec c with rfl | rfl <;> simp }
  have hL : ∀ x, L x = JonesParshall.zornMap e.symm x := fun _ => rfl
  have htr : ∀ {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') (x : quasithinZorn F),
      x.1 + x.2.2.2 = 0 → (JonesParshall.zornMap σ x).1 + (JonesParshall.zornMap σ x).2.2.2 = 0 :=
    fun σ x hx => by
      change σ x.1 + σ x.2.2.2 = 0
      rw [← map_add, hx, map_zero]
  have hscal : ∀ {F F' : Type} [Field F] [Field F'] (σ : F ≃+* F') (c : F),
      JonesParshall.zornMap σ ((c, 0, 0, c) : quasithinZorn F) = (σ c, 0, 0, σ c) :=
    fun σ c => Prod.ext rfl (Prod.ext (funext fun _ => map_zero σ)
      (Prod.ext (funext fun _ => map_zero σ) rfl))
  let Φ : ↥(quasithinG2 (ZMod 2)) ≃* ↥(quasithinG2 (GaloisField 2 1)) :=
    (MulEquiv.subgroupCongr (G11.P3G2.quasithinG2_eq_cayleyGroup (K := ZMod 2))).trans
      (((JonesParshall.zornConj e).subgroupMap _).trans
        (MulEquiv.subgroupCongr ((JonesParshall.map_cayleyGroup e).trans
          (G11.P3G2.quasithinG2_eq_cayleyGroup (K := GaloisField 2 1)).symm)))
  have hΦ : ∀ g : ↥(quasithinG2 (ZMod 2)),
      ((Φ g : ↥(quasithinG2 (GaloisField 2 1))) :
          quasithinZorn (GaloisField 2 1) ≃ₗ[GaloisField 2 1] quasithinZorn (GaloisField 2 1)) =
        JonesParshall.zornConj e
          ((g : ↥(quasithinG2 (ZMod 2))) :
            quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :=
    fun _ => rfl
  have key : ∀ (g : ↥(quasithinG2 (ZMod 2))) (y : quasithinZorn (GaloisField 2 1)),
      L (((Φ g : ↥(quasithinG2 (GaloisField 2 1))) :
          quasithinZorn (GaloisField 2 1) ≃ₗ[GaloisField 2 1] quasithinZorn (GaloisField 2 1)) y) =
        ((g : ↥(quasithinG2 (ZMod 2))) :
          quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) (L y) := by
    intro g y
    rw [hL, hL, hΦ, JonesParshall.zornConj_apply, JonesParshall.zornMap_symm_apply]
  refine ⟨φ.trans Φ, π ∘ₗ L, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨x, hx, hπx⟩ := h1 v
    refine ⟨JonesParshall.zornMap e x, htr e x hx, ?_⟩
    change π (L (JonesParshall.zornMap e x)) = v
    rw [hL, JonesParshall.zornMap_symm_apply, hπx]
  · intro x' hx'
    have hx : (JonesParshall.zornMap e.symm x').1 + (JonesParshall.zornMap e.symm x').2.2.2 = 0 :=
      htr e.symm x' hx'
    change π (L x') = 0 ↔ _
    rw [hL, h2 _ hx]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨e c, ?_⟩
      rw [← JonesParshall.zornMap_apply_symm e x', hc, hscal e c]
    · rintro ⟨c, rfl⟩
      exact ⟨e.symm c, hscal e.symm c⟩
  · intro k x' hx'
    have hx : (JonesParshall.zornMap e.symm x').1 + (JonesParshall.zornMap e.symm x').2.2.2 = 0 :=
      htr e.symm x' hx'
    show π (L (((Φ (φ k) : ↥(quasithinG2 (GaloisField 2 1))) :
      quasithinZorn (GaloisField 2 1) ≃ₗ[GaloisField 2 1] quasithinZorn (GaloisField 2 1)) x')) =
        (k : V ≃ₗ[ZMod 2] V) (π (L x'))
    rw [key]
    exact h3 k _ hx

theorem card_derived_zmod2_eq :
    Nat.card ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ = 6048 := by
  rw [Nat.card_congr (VolI.g2DerivedFieldEquiv (GaloisField.equivZmodP 2).toRingEquiv.symm).toEquiv]
  exact G11.P3G2.card_commutatorG2

end L14324

theorem lemma14324Big_of_inputs
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12813 : Lemma12_8_13) (h14312 : Lemma14312One) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1434 : Lemma1434One) : Lemma14324Big := by
  have hFixS : G11.SzG11S.TheoremG112FixS := G11.SzG11S.theoremG112FixS_holds
  intro G _ _ T L V h hlt V₂ g hV₂ hgP hgN D hd
  obtain ⟨a, H, -, hX, -⟩ :=
    L14324.data_of h1332 h1334 h1222 h12213 h12813 h14312 hFixS h hlt hV₂ hgP hgN D
  have hXΓ : D.img (CFSG.conjugate (l32nW T V V₂) g) ≤ D.img (l32nH T V) := H.X_le
  have hsq : ∀ x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), x * x = 1 := H.X_sq
  have h6 : G112Concl6 (D.img (l32nH T V)) := by
    rcases L14324.cases_six_or_thirteen h1332 h1334 h1222 h12213 h12813 h14312 hFixS h36 h37 h38
        h39 h1434 G T L V h hlt V₂ g hV₂ hgP hgN D hd with h6 | h13
    · exact h6
    · refine (L14324.false_of_concl13S_of_card h13 hXΓ hsq ?_).elim
      have hX' := hX
      rw [h13.1.1] at hX'
      norm_num at hX'
      exact hX'
  have hfin : Module.finrank (ZMod 2) D.V = 6 := h6.1
  have hcard : Nat.card ↥(D.img (l32nH T V)) = 12096 := h6.2
  have hSQ : IsQuotientOfSQTKTauCeti ↥(D.img (l32nH T V)) := by
    have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
    have hV := stmtL32NModule_of_inputs h1332 h1334
    have hs := h.setting1282One h13322 hV hV₂
    exact L128P.isQuotientOfSQTK_img hs D
  have hG : CFSG.ASVolI.G_11_2 := CFSG.ASVolI.as_G_11_2
  have hF := hG D.V D.B (D.img (l32nH T V)) (D.π a) (D.hat (l32nE T V V₂ g))
    (D.img (CFSG.conjugate (l32nW T V V₂) g)) (D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
    H hSQ
  have hmod : G11.IsG2NaturalModule (D.img (l32nH T V)) (quasithinG2 (GaloisField 2 1)) := by
    have hX8 : 8 ≤ Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := by
      have hX' := hX
      rw [hfin] at hX'
      norm_num at hX'
      exact hX'
    obtain ⟨k, hk₀⟩ := H.toG101Hyp.exists_card_X
    have hk : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ k := hk₀
    have hXel := H.toG101Hyp.X_isElemAbelian
    have hO2 := H.toG101Hyp.g10_3_pCoreOf_eq_bot
    rcases hF with ((h1 | h2 | h3 | h4 | h5 | h6m | h7 | h8 | h8' | h9 | h10 | h11 | h12 | h13') | hU)
    · have := h1.1; omega
    · have := h2.1; omega
    · have := L14324.card_le_four_of_concl3 hXΓ hXel hk hO2 h3; omega
    · have := L14324.card_le_four_of_concl4 H h4; omega
    · exact (L14324.false_of_concl5 h1332 h1334 h1222 h12213 h12813 h14312 hFixS h36 h37 h38 h39
        h1434 h hlt hV₂ hgP hgN D h5).elim
    · exact L14324.isG2NaturalModule_gf21_of_zmod2 h6m.2
    · have := h7.1; omega
    · have := h8.1; omega
    · have := h8'.1; omega
    · have := h9.1; omega
    · have := h10.1; omega
    · have := h11.1; omega
    · have := h12.1; omega
    · have := h13'.1; omega
    · obtain ⟨-, hUm⟩ := hU
      obtain ⟨φU, -⟩ := hUm
      have h12 : (12096 : ℕ) = 6048 :=
        hcard.symm.trans ((Nat.card_congr φU.toEquiv).trans L14324.card_derived_zmod2_eq)
      omega
  exact And.intro h6 hmod

end CFSG.Quasithin.H13

