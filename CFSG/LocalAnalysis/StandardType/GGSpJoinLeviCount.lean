module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrCentralizer
public import CFSG.LocalAnalysis.StandardType.GGSpJoinMaxElemRank
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSingleSupport
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviOfComponent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic CFSG.Open
  CFSG.StandardType.SpJoin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

section Neighbour

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_x_not_mem_centralizer {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G}
    {K : Subgroup G} (hnbr : GGNbr p B x D J y K) : x ∉ Subgroup.centralizer (K : Set G) := by
  intro hx
  apply hnbr.2.2.2
  have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hx
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
  exact bot_le

theorem ggNbr_y_not_mem_centralizer_left {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hnbr : GGNbr p B x D J y K) :
    y ∉ Subgroup.centralizer (L : Set G) := by
  intro hy
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hnbr.1.2.1
  have hxCent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxC : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hcfg.2.1.1 hxB, hxCent⟩
  have hyC : y ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hcfg.2.1.1 hyB, hy⟩
  have hDle : D ≤ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hnbr.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hxC
    · exact hyC
  have hcard := Subgroup.card_le_of_le hDle
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hcentcard := hcfg.card_bstar_centralizer_le
  have hp2 : p ^ 2 ≤ p := by rw [← hDcard]; exact hcard.trans hcentcard
  have : p ≤ 1 := by
    by_contra hlt
    push Not at hlt
    nlinarith [hp.two_le]
  exact hp.one_lt.not_ge this

theorem ne_bot_of_isQuasisimple {J : Subgroup G} (hJ : CFSG.Assembly.IsQuasisimple ↥J) : J ≠ ⊥ := by
  intro h
  have hsub : Subsingleton ↥J := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : (a : G) ∈ (⊥ : Subgroup G) := by
      rw [← h]
      exact a.2
    have hb : (b : G) ∈ (⊥ : Subgroup G) := by
      rw [← h]
      exact b.2
    rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb]
  haveI := hJ.2
  have hq : Subsingleton (↥J ⧸ Subgroup.center ↥J) :=
    (QuotientGroup.mk_surjective :
      Function.Surjective (QuotientGroup.mk : ↥J → ↥J ⧸ Subgroup.center ↥J)).subsingleton
  exact not_subsingleton (↥J ⧸ Subgroup.center ↥J) hq

theorem GGConfig.stdSub_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    J ≤ L ∧ J ≤ ⁅J, J⁆ ∧ J ≠ ⊥ ∧ J ≤ Subgroup.centralizer (D : Set G) ∧
      CFSG.Assembly.IsSubnormal J (L ⊓ Subgroup.centralizer (D : Set G)) ∧ x ∈ D := by
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  refine ⟨hJcomp.1.trans inf_le_left, ?_, ne_bot_of_isQuasisimple hJcomp.2.2,
    hJcomp.1.trans inf_le_right, hJcomp.2.1, hcfg.2.2.1.2.2.2.1⟩
  have h := Subgroup.map_subtype_commutator J
  rw [hJcomp.2.2.1, Subgroup.map_top, Subgroup.range_subtype] at h
  exact h.le

theorem commute_left_of_mul_eq {u c z j : G} (hz : z = u * c) (hjz : j * z = z * j)
    (hjc : j * c = c * j) : j * u = u * j := by
  apply mul_right_cancel (b := c)
  calc j * u * c = j * (u * c) := mul_assoc _ _ _
    _ = j * z := by rw [← hz]
    _ = z * j := hjz
    _ = (u * c) * j := by rw [hz]
    _ = u * (c * j) := mul_assoc _ _ _
    _ = u * (j * c) := by rw [hjc]
    _ = u * j * c := (mul_assoc _ _ _).symm

end Neighbour

section Counting

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_lam_zero_mul_of_configuration {F : Type} [Field F] [Finite F] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) (h2 : (2 : F) = 0) {B Bs X Y : Subgroup G}
    (hBs : GGBstar p B Bs) (φ' : StatedSp (m + 1) F →* G) (hinj : Function.Injective φ')
    (hrange : φ'.range = X) (hNX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : p ^ (m + 1 + 1) ≤ Nat.card Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) A) (hXA : ggAutomizer X Bs ≤ A)
    (hYA : ggAutomizer Y Bs ≤ A)
    (hY : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer Y Bs)) {z : G} (hz : z ∈ Bs)
    (hzY : z ∈ Subgroup.centralizer (Y : Set G)) (hzX : z ∉ Subgroup.centralizer (X : Set G)) :
    ∃ (ψ : StatedSp (m + 1) F →* G) (g : SpecialLinearGroup (Fin 2) F) (c : G),
      Function.Injective ψ ∧ ψ.range = X ∧ (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 ∧
        c ∈ Subgroup.centralizer (X : Set G) ∧ z = ψ (lam (0 : Fin (m + 1)) g) * c := by
  classical
  have hZ : Subgroup.center X = ⊥ := by
    haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
    have := center_range_statedSp_eq_bot φ' hinj
    rwa [hrange] at this
  obtain ⟨ζ, φ, hl⟩ :=
    exists_plane_torus_lift_of_range hp hp2 h2 φ' hinj hBs hrange hNX hinner hcent hrank
  obtain ⟨u, hu, c, hc, hzuc⟩ := ggBstar_split_of_inner hBs hZ hNX hinner z hz
  have hu' : u ∈ (φ.comp (spPlaneTorus (m + 1) ζ)).range := by
    rw [hl.torus_range]
    exact hu
  obtain ⟨v, hv⟩ := hu'
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hzX
    have hu1 : u = 1 := by rw [← hv, map_one]
    rw [hzuc, hu1, one_mul]
    exact hc.2
  have hzv : z = (φ.comp (spPlaneTorus (m + 1) ζ)) v * c := by
    rw [hv]
    exact hzuc
  obtain ⟨ψ, g, hψinj, hψrange, htr, hψval⟩ :=
    exists_lift_lam_zero_of_orbit hp hp2 hm h2 hl hA hXA hYA hY hz hzY hc.2 hzv hv1
  exact ⟨ψ, g, c, hψinj, hψrange, htr, hc.2, by rw [hψval]; exact hzv⟩

end Counting

theorem ggSpLeviInputAtL_of_inputs (hMp : GGInnerDiagMpInput) (hlift : GGSpLiftInput) :
    GGSpLeviInputAtL := by
  intro G _ _ p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN φ₀ hφ₀inj hφ₀range
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hm3 : 3 ≤ m := by
    have := hN.2.1
    omega
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hnbr : GGNbr p B x D J y K := hN.2.2.2.1
  have hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    hN.2.2.2.2.2
  have hrank : p ^ (m + 1 + 1) ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_B hp hp2 hBs.2.1 (by omega) hA
  have hinnerL : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by omega) hN.1.1 hInn.1 φ₀ hφ₀inj hφ₀range
  have hnormL : Bs ≤ Subgroup.normalizer (L : Set G) := hInn.1.le_normalizer
  have hcentL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    hcfg.card_bstar_centralizer_le
  have hmarkK : GGInnerDiagOn Bs K := hInn.2 y K hnbr
  obtain ⟨φK, hφKinj, hφKrange⟩ := hlift G K (m + 1) f hN.2.1 hmarkK.1 hN.2.2.2.2.1
  have hinnerK : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by omega) hN.1.1 hmarkK φK hφKinj hφKrange
  have hnormK : Bs ≤ Subgroup.normalizer (K : Set G) := hmarkK.le_normalizer
  have hZL : Subgroup.center L = ⊥ := by
    have := center_range_statedSp_eq_bot φ₀ hφ₀inj
    rwa [hφ₀range] at this
  have hZK : Subgroup.center K = ⊥ := by
    have := center_range_statedSp_eq_bot φK hφKinj
    rwa [hφKrange] at this
  have hcentK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    card_bstar_centralizer_le_of_lifts hp hp2 (Nat.succ_pos m) hBs φ₀ hφ₀inj hφ₀range hZL hnormL
      hinnerL φK hφKinj hφKrange hZK hnormK hinnerK hcentL hrank
  have hY : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer K Bs) :=
    two_pow_mul_factorial_le_card_ggAutomizer_of_lift hp hp2 h2 φK hφKinj hBs hφKrange hnormK
      hinnerK hcentK hrank
  have hyBs : y ∈ Bs := hBs.1 hnbr.1.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  have hyL : y ∉ Subgroup.centralizer (L : Set G) := ggNbr_y_not_mem_centralizer_left hcfg hnbr
  obtain ⟨ψ, g, c, hψinj, hψrange, htr, hc, hyuc⟩ :=
    exists_lift_lam_zero_mul_of_configuration hp hp2 hm3 h2 hBs φ₀ hφ₀inj hφ₀range hnormL
      hinnerL hcentL hrank hA le_sup_left le_sup_right hY hyBs hyK hyL
  obtain ⟨hJL, hperf, hJne, hJD, hJsub, hxD⟩ := hcfg.stdSub_facts
  have hyD : y ∈ D := by
    rw [hnbr.2.1]
    exact Subgroup.subset_closure (by simp)
  have hJX : J ≤ ψ.range := hψrange ▸ hJL
  have hJu : ∀ j ∈ J, j * ψ (lam (0 : Fin (m + 1)) g) = ψ (lam (0 : Fin (m + 1)) g) * j := by
    intro j hj
    have hjy : j * y = y * j := (Subgroup.mem_centralizer_iff.mp (hJD hj) y hyD).symm
    have hjc : j * c = c * j := Subgroup.mem_centralizer_iff.mp hc j (hJL hj)
    exact commute_left_of_mul_eq hyuc hjy hjc
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hSC : (ψ.comp (spLeviBlock m (GaloisField 2 f))).range ≤
      L ⊓ Subgroup.centralizer (D : Set G) := by
    intro s hs
    have hsψ : s ∈ ψ.range := by
      rw [MonoidHom.range_comp] at hs
      exact Subgroup.map_le_range _ _ hs
    have hsL : s ∈ L := hψrange ▸ hsψ
    obtain ⟨t, rfl⟩ := hs
    have hsc : (ψ.comp (spLeviBlock m (GaloisField 2 f))) t * c =
        c * (ψ.comp (spLeviBlock m (GaloisField 2 f))) t :=
      Subgroup.mem_centralizer_iff.mp hc _ hsL
    have hsu : ψ (lam (0 : Fin (m + 1)) g) * (ψ.comp (spLeviBlock m (GaloisField 2 f))) t =
        (ψ.comp (spLeviBlock m (GaloisField 2 f))) t * ψ (lam (0 : Fin (m + 1)) g) :=
      ((lam_zero_commute_spLeviBlock g t).map ψ).eq
    have hD' : D ≤ Subgroup.centralizer
        ({(ψ.comp (spLeviBlock m (GaloisField 2 f))) t} : Set G) := by
      rw [hnbr.2.1, Subgroup.closure_le]
      intro z hz
      rcases hz with hzx | hzy
      · rw [hzx, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hLx hsL)).symm
      · rw [Set.mem_singleton_iff] at hzy
        rw [hzy, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hyuc]
        calc ψ (lam (0 : Fin (m + 1)) g) * c * (ψ.comp (spLeviBlock m (GaloisField 2 f))) t
            = ψ (lam (0 : Fin (m + 1)) g) *
              (c * (ψ.comp (spLeviBlock m (GaloisField 2 f))) t) := mul_assoc _ _ _
          _ = ψ (lam (0 : Fin (m + 1)) g) *
              ((ψ.comp (spLeviBlock m (GaloisField 2 f))) t * c) := by rw [hsc]
          _ = (ψ (lam (0 : Fin (m + 1)) g) * (ψ.comp (spLeviBlock m (GaloisField 2 f))) t) * c :=
              (mul_assoc _ _ _).symm
          _ = ((ψ.comp (spLeviBlock m (GaloisField 2 f))) t * ψ (lam (0 : Fin (m + 1)) g)) * c := by
              rw [hsu]
          _ = (ψ.comp (spLeviBlock m (GaloisField 2 f))) t *
              (ψ (lam (0 : Fin (m + 1)) g) * c) := mul_assoc _ _ _
    have hsD : (ψ.comp (spLeviBlock m (GaloisField 2 f))) t ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mp (hD' hd)
    exact ⟨hsL, hsD⟩
  exact ⟨ψ, hψinj, hψrange,
    range_comp_spLeviBlock_eq_of_isSubnormal hm3 hψinj htr hperf hJne hJX hJu hJsub hSC⟩

theorem ggSpLeviInputAtNbr_of (hMp : GGInnerDiagMpInput) (hlift : GGSpLiftInput)
    (hsub : GGNbrSubcomponentInput) (hL : GGSpLeviInputAtL) : GGSpLeviInputAtNbr := by
  intro G _ _ p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN y' K' hnbr' hA' φ₀ hφ₀inj hφ₀range
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hm3 : 3 ≤ m := by
    have := hN.2.1
    omega
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    hN.2.2.2.2.2
  have hrank : p ^ (m + 1 + 1) ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_B hp hp2 hBs.2.1 (by omega) hA
  have hat : GGSpNbrAt p B Bs x L D J m f y K y' K' := ⟨hcfg, hOp, hInn, hNoTr, hN, hnbr', hA'⟩
  have hcentK' : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) ≤ p :=
    ggSpNbrCentralizerInput_of_atL hMp hlift hsub hL G p B Bs x L D J m f y K y' K' hat
  have hmarkK' : GGInnerDiagOn Bs K' := hInn.2 y' K' hnbr'
  have hinnerK' : ∀ b ∈ Bs, ∃ g ∈ K', ∀ k ∈ K', b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by omega) hN.1.1 hmarkK' φ₀ hφ₀inj hφ₀range
  have hnormK' : Bs ≤ Subgroup.normalizer (K' : Set G) := hmarkK'.le_normalizer
  obtain ⟨φL, hφLinj, hφLrange⟩ := hlift G L (m + 1) f hN.2.1 hInn.1.1 hN.1
  have hinnerL : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by omega) hN.1.1 hInn.1 φL hφLinj hφLrange
  have hnormL : Bs ≤ Subgroup.normalizer (L : Set G) := hInn.1.le_normalizer
  have hcentL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    hcfg.card_bstar_centralizer_le
  have hY : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer L Bs) :=
    two_pow_mul_factorial_le_card_ggAutomizer_of_lift hp hp2 h2 φL hφLinj hBs hφLrange hnormL
      hinnerL hcentL hrank
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hxBs : x ∈ Bs := hBs.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxK' : x ∉ Subgroup.centralizer (K' : Set G) := ggNbr_x_not_mem_centralizer hnbr'
  obtain ⟨ψ, g, c, hψinj, hψrange, htr, hc, hxuc⟩ :=
    exists_lift_lam_zero_mul_of_configuration hp hp2 hm3 h2 hBs φ₀ hφ₀inj hφ₀range hnormK'
      hinnerK' hcentK' hrank hA hA' le_sup_left hY hxBs hxL hxK'
  obtain ⟨hJL, hperf, hJne, hJD, hJsub, hxD⟩ := hcfg.stdSub_facts
  have hJK' : J ≤ K' := hsub G p B x L D J hcfg.1 hcfg.2.2 y' K' hnbr'
  have hJX : J ≤ ψ.range := hψrange ▸ hJK'
  have hJu : ∀ j ∈ J, j * ψ (lam (0 : Fin (m + 1)) g) = ψ (lam (0 : Fin (m + 1)) g) * j := by
    intro j hj
    have hjx : j * x = x * j := (Subgroup.mem_centralizer_iff.mp (hJD hj) x hxD).symm
    have hjc : j * c = c * j := Subgroup.mem_centralizer_iff.mp hc j (hJK' hj)
    exact commute_left_of_mul_eq hxuc hjx hjc
  obtain ⟨φL', hφL'inj, -, hφL'levi⟩ :=
    hL G p B Bs x L D J m f y K hcfg hOp hInn hNoTr hN φL hφLinj hφLrange
  have hcardJ : Nat.card (StatedSp m (GaloisField 2 f)) ≤ Nat.card J := by
    have hinj : Function.Injective (φL'.comp (spLeviBlock m (GaloisField 2 f))) :=
      hφL'inj.comp spLeviBlock_injective
    rw [← hφL'levi]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).le
  exact ⟨ψ, hψinj, hψrange,
    range_comp_spLeviBlock_eq_of_card_le hψinj htr hperf hJX hJu hcardJ⟩

end CFSG.StandardType
