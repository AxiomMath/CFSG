module

public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCData
import CFSG.RankThree.GF2n.Smith81.OrthE1Small
import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaC
import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalarsPlusTwo

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.Adapters.RankTwoModelTransports (glCongr)
open CFSG.ClassicalInvolution.Upgrade
  (map_statedOmega glCongr_mulVec statedQuadPlus_comp statedQuadMinus_comp irreducible_map)


namespace NtLine

section Transfer

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem xpre_le_rt (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) :
    E1Xpre M Q B t ≤ Rt M (LB M Q B) t :=
  sup_le (Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) (hc.Q_le_Rt ht)

theorem exists_ne_zero_one_of_four_le {K' : Type} [Field K'] [Finite K'] (h : 4 ≤ Nat.card K') :
    ∃ c : K', c ≠ 0 ∧ c ≠ 1 := by
  by_contra hne
  push Not at hne
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K') else 0) := by
    intro c
    by_cases h0 : c = 0
    · exact ⟨false, by simp [h0]⟩
    · exact ⟨true, by simp [hne c h0]⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  have h2 : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

theorem natural_transfer_core (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = Nat.card Z) {f' : (ι → K') → K'}
    (hcomm : AddCommutantScalar (StatedOmega f'))
    (hnat : NaturalRep K' (StatedOmega f') (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hH.ctx.CN t)) :
    ∃ (σ : K' ≃+* AM.K) (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
      (φ' : ↥(Rt M (LB M Q B) t) →* GL ι K'), φ'.range = StatedOmega f' ∧
        φ'.ker = (hH.ctx.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
        ∀ (y : ↥(H0 M Z)) (hy : (y : G) ∈ Rt M (LB M Q B) t) (a : ↥(AM.Vsp hH.ctx t))
          (ha : AM.φ y a ∈ AM.Vsp hH.ctx t),
          c ⟨AM.φ y a, ha⟩ =
            ((glCongr σ (φ' ⟨y, hy⟩) : GL ι AM.K) : Matrix ι ι AM.K) *ᵥ c a := by
  classical
  have hc := hH.ctx
  have ht : t ∈ LB M Q B := hH.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hRV : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht
  obtain ⟨φ', hφ'r, hφ'k, hRV', hZn, ψ, hψ⟩ := hnat
  obtain ⟨m, φK, hn, ψK, c₀, hkerK, hψK, -, hcoordK, hSeqK⟩ :=
    exists_natural_data_of_subspace hc.hyp hVQ hZV hRH hRV (fun _ => Ctx.mem_CN (hc := hc))
      AM.glob (fun c _ he => hc.smul_mem_img_Vt AM.glob t c he)
  haveI := hn
  haveI := hZn
  let Θ : (Fin m → AM.K) ≃+ (ι → K') := AddEquiv.toMultiplicative.symm (ψK.symm.trans ψ)
  have hΘ_apply : ∀ z : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t),
      Θ (Multiplicative.toAdd (ψK z)) = Multiplicative.toAdd (ψ z) := by
    intro z
    show Multiplicative.toAdd
      ((ψK.symm.trans ψ) (Multiplicative.ofAdd (Multiplicative.toAdd (ψK z)))) = _
    simp
  have hΘ : ∀ (s : ↥(Rt M (LB M Q B) t)) (u : Fin m → AM.K),
      Θ ((φK s : Matrix (Fin m) (Fin m) AM.K) *ᵥ u) = (φ' s : Matrix ι ι K') *ᵥ Θ u := by
    intro s u
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψK.symm (Multiplicative.ofAdd u))
    have hu : u = Multiplicative.toAdd (ψK (QuotientGroup.mk v)) := by
      rw [hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hsv : (s : G) * v * (s : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hRV s.2) v).mp v.2
    have h1 := hψK s v ⟨(s : G) * v * (s : G)⁻¹, hsv⟩ rfl
    have h2 := hψ s v ⟨(s : G) * v * (s : G)⁻¹, hsv⟩ rfl
    rw [hu, ← h1, hΘ_apply, h2, hΘ_apply]
  have hcomm' : ∀ (c : AM.K), ∀ B ∈ StatedOmega f', ∀ v : ι → K',
      Θ (c • Θ.symm ((B : Matrix ι ι K') *ᵥ v)) = (B : Matrix ι ι K') *ᵥ Θ (c • Θ.symm v) := by
    intro c B hB v
    rw [← hφ'r] at hB
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hB
    have h1 : Θ.symm ((φ' s : Matrix ι ι K') *ᵥ v) =
        (φK s : Matrix (Fin m) (Fin m) AM.K) *ᵥ Θ.symm v := by
      apply Θ.injective
      rw [AddEquiv.apply_symm_apply, hΘ, AddEquiv.apply_symm_apply]
    rw [h1, ← Matrix.mulVec_smul, hΘ]
  have hcard : Nat.card AM.K = Nat.card K' := by rw [AM.glob.card, hK']
  obtain ⟨σ', hσ'⟩ := exists_ringEquiv_of_scalar_commutant hcard hcomm Θ hcomm'
  let σ : K' ≃+* AM.K := σ'.symm
  let c₁ : (Fin m → AM.K) ≃ₗ[AM.K] (ι → AM.K) :=
    { toFun := fun u i => σ (Θ u i)
      map_add' := fun u w => by
        ext i
        simp [map_add]
      map_smul' := fun c u => by
        ext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [hσ' c u, Pi.smul_apply, smul_eq_mul, map_mul]
        congr 1
        exact σ'.symm_apply_apply c
      invFun := fun w => Θ.symm (fun i => σ' (w i))
      left_inv := fun u => by
        have : (fun i => σ' (σ (Θ u i))) = Θ u := funext fun i => σ'.apply_symm_apply _
        simp only [this, AddEquiv.symm_apply_apply]
      right_inv := fun w => by
        ext i
        simp only [AddEquiv.apply_symm_apply]
        exact σ'.symm_apply_apply (w i) }
  refine ⟨σ, c₀.trans c₁, φ', hφ'r, hφ'k, ?_⟩
  intro y hy a ha
  have h1 := hSeqK ⟨(y : G), hy⟩ (AM.φ y) (fun x hx => AM.φ_π y x hx) a ha
  show c₁ (c₀ ⟨AM.φ y a, ha⟩) = _
  rw [h1]
  funext i
  have h2 := congrFun (glCongr_mulVec σ (φ' ⟨(y : G), hy⟩) (Θ (c₀ a))) i
  show σ (Θ ((φK ⟨(y : G), hy⟩ : Matrix (Fin m) (Fin m) AM.K) *ᵥ c₀ a) i) = _
  rw [hΘ]
  exact h2.symm

theorem vsp_stable (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) (AM : ActionModel M Q Z)
    (y : ↥(H0 M Z)) (hy : (y : G) ∈ Rt M (LB M Q B) t) (e : AM.M₀.E)
    (he : e ∈ AM.Vsp hc t) : AM.φ y e ∈ AM.Vsp hc t := by
  obtain ⟨w, hwV, hwQ, rfl⟩ := mem_imgSub.mp he
  rw [← AM.φ_π y w hwQ]
  exact AM.M₀.pi_mem_img ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) w).mp hwV)
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2.1) w).mp hwQ)

theorem mem_CN_of_fix (hc : Ctx M Q Z B) (AM : ActionModel M Q Z) (y : ↥(H0 M Z))
    (hy : (y : G) ∈ Rt M (LB M Q B) t)
    (hfix : ∀ e ∈ AM.Vsp hc t, AM.φ y e = e) : (y : G) ∈ hc.CN t := by
  refine Ctx.mem_CN.mpr ⟨hy, fun v hv => ?_⟩
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hyvQ : (y : G) * v * (y : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2.1) v).mp hvQ
  refine (Tim79.QuadModel.comm_mem_iff (M₀ := AM.M₀) hvQ hyvQ).mpr ?_
  rw [AM.φ_π y v hvQ]
  exact hfix _ (mem_imgSub.mpr (AM.M₀.pi_mem_img hv hvQ))

theorem natural_transfer (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (hNtCN : Nt M (LB M Q B) t = hH.ctx.CN t)
    (hsup : Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t)
    (hinf : Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = Nat.card Z) {f' : (ι → K') → K'}
    (hcomm : AddCommutantScalar (StatedOmega f'))
    (hnat : NaturalRep K' (StatedOmega f') (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hH.ctx.CN t)) :
    ∃ (σ : K' ≃+* AM.K) (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K)),
      ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c
        (fun v => σ (f' (σ.symm ∘ v))) := by
  classical
  obtain ⟨σ, c, φ', hφ'r, hφ'k, hcoord⟩ := natural_transfer_core hH AM hK' hcomm hnat
  refine ⟨σ, c, ?_⟩
  have hc := hH.ctx
  have ht : t ∈ LB M Q B := hH.mem
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := xpre_le_rt hc ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hΩ : (StatedOmega f').map (glCongr σ).toMonoidHom =
      StatedOmega (fun v => σ (f' (σ.symm ∘ v))) :=
    map_statedOmega σ (fun v => by
      simp only [RingEquiv.symm_apply_apply, Function.comp_def])
  have hX : ∀ g ∈ AM.actImage (E1Xpre M Q B t), ∀ v ∈ AM.Vsp hc t, g v ∈ AM.Vsp hc t := by
    intro g hg v hv
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    exact vsp_stable hc ht AM y (hXR (Subgroup.mem_subgroupOf.mp hy)) v hv
  refine ⟨hX, ?_, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hyR : (y : G) ∈ Rt M (LB M Q B) t := hXR (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨glCongr σ (φ' ⟨(y : G), hyR⟩), ?_, fun v hv => ?_⟩
    · rw [← hΩ]
      exact Subgroup.mem_map.mpr ⟨φ' ⟨(y : G), hyR⟩, by rw [← hφ'r]; exact ⟨_, rfl⟩, rfl⟩
    · exact hcoord y hyR ⟨v, hv⟩ _
  ·
    intro A hA
    rw [← hΩ] at hA
    obtain ⟨B', hB', rfl⟩ := Subgroup.mem_map.mp hA
    rw [← hφ'r] at hB'
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hB'
    have hs : (s : G) ∈ E1Xpre M Q B t ⊔ Nt M (LB M Q B) t := by
      rw [sup_comm, hsup]
      exact s.2
    obtain ⟨x, hx, n, hn, hsxn⟩ := exists_mul_of_sup_of_le_normalizer'
      (fun r hr => rt_le_normalizer_nt M (LB M Q B) t (hXR hr)) hs
    have hxR : x ∈ Rt M (LB M Q B) t := hXR hx
    have hnR : n ∈ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t hn
    have hφn : φ' ⟨n, hnR⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hφ'k, Subgroup.mem_subgroupOf]
      exact hNtCN ▸ hn
    have hφs : φ' s = φ' ⟨x, hxR⟩ := by
      have : s = ⟨x, hxR⟩ * ⟨n, hnR⟩ := Subtype.ext hsxn
      rw [this, map_mul, hφn, mul_one]
    refine ⟨AM.φ ⟨x, hRH hxR⟩, Subgroup.mem_map.mpr ⟨⟨x, hRH hxR⟩,
      Subgroup.mem_subgroupOf.mpr hx, rfl⟩, fun v hv => ?_⟩
    rw [hφs]
    exact hcoord ⟨x, hRH hxR⟩ hxR ⟨v, hv⟩ _
  ·
    intro g hg hfix
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hyX : (y : G) ∈ E1Xpre M Q B t := Subgroup.mem_subgroupOf.mp hy
    have hyN : (y : G) ∈ Nt M (LB M Q B) t := by
      rw [hNtCN]
      exact mem_CN_of_fix hc AM y (hXR hyX) hfix
    have hyQ : (y : G) ∈ Q := by
      rw [← hinf]
      exact ⟨hyN, hyX⟩
    exact (AM.φ_ker y).mpr hyQ

end Transfer

section Line

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem fix_of_mem_CN (hc : Ctx M Q Z B) (AM : ActionModel M Q Z) (y : ↥(H0 M Z))
    (hy : (y : G) ∈ hc.CN t) (e : AM.M₀.E) (he : e ∈ AM.Vsp hc t) : AM.φ y e = e := by
  obtain ⟨w, hwV, hwQ, rfl⟩ := mem_imgSub.mp he
  have hywQ : (y : G) * w * (y : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2.1) w).mp hwQ
  rw [← AM.φ_π y w hwQ]
  exact (Tim79.QuadModel.comm_mem_iff (M₀ := AM.M₀) hwQ hywQ).mp ((Ctx.mem_CN.mp hy).2 w hwV)

theorem phi_comm_of_comm_mem (AM : ActionModel M Q Z) (a b : ↥(H0 M Z))
    (h : ⁅(a : G), (b : G)⁆ ∈ Q) : AM.φ a * AM.φ b = AM.φ b * AM.φ a := by
  have h1 : AM.φ ⁅a, b⁆ = 1 := (AM.φ_ker _).mpr (by simpa [commutatorElement_def] using h)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem phi_line (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (hNtCN : Nt M (LB M Q B) t = hH.ctx.CN t)
    (hC : ∀ r ∈ Rt M (LB M Q B) t, ∀ n ∈ Nt M (LB M Q B) t, ⁅r, n⁆ ∈ Q)
    (hU : ∀ g : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E, g ∈ AM.S.U (AM.Vsp hH.ctx t) →
      ∃ β : AM.M₀.E →ₗ[AM.K] AM.M₀.E, (∀ e, β e ∈ AM.Vsp hH.ctx t) ∧
        (∀ v ∈ AM.Vsp hH.ctx t, β v = 0) ∧ (∀ e, AM.S.B e (β e) = 0) ∧
        ∀ e, g e = e + β e)
    (D : LCData AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t))) :
    ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • D.β e := by
  intro x hx
  have hc := hH.ctx
  have ht : t ∈ LB M Q B := hH.mem
  have hxCN : (x : G) ∈ hc.CN t := hNtCN ▸ hx
  have hU' : AM.φ x ∈ AM.S.U (AM.Vsp hc t) :=
    ⟨fun e => AM.φ_Qf x e, fun v hv => fix_of_mem_CN hc AM x hxCN v hv⟩
  obtain ⟨βx, hr, hk, -, hβx⟩ := hU _ hU'
  have hcomm : ∀ (g : ↥(AM.actImage (E1Xpre M Q B t))) (e : AM.M₀.E),
      βx ((g : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) e) = (g : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) (βx e) := by
    rintro ⟨g, hg⟩ e
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hyR : (y : G) ∈ Rt M (LB M Q B) t := xpre_le_rt hc ht (Subgroup.mem_subgroupOf.mp hy)
    have h2 := LinearEquiv.congr_fun (phi_comm_of_comm_mem AM y x (hC _ hyR _ hx)) e
    simp only [LinearEquiv.mul_apply] at h2
    rw [hβx e, hβx (AM.φ y e), map_add] at h2
    exact (add_left_cancel h2).symm
  obtain ⟨c, hc'⟩ := D.schur_β βx hcomm hr hk
  exact ⟨c, fun e => by rw [hβx e, hc' e]⟩

end Line

end NtLine

section Main

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem e1NaturalK_of (hN : E1NaturalStatement) (hSplit : RtSplitStatement)
    (hNt : StrothNtStatement) (_hKF2 : NatIrredStatement) : E1NaturalKStatement := by
  intro G _ _ M Q Z B t hH AM
  classical
  have hc := hH.ctx
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hNtCN : Nt M (LB M Q B) t = hc.CN t :=
    hNt G M Q Z B hc 4 hH.case.width (by norm_num) hH.noA2 hH.gen t hH.mem hH.notQ
  obtain ⟨-, hinf, hsup, -, -, -, -, -, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨hP, hMi⟩ := hN G M Q Z B t hH
  refine ⟨fun hE => ?_, fun hE => ?_⟩
  · obtain ⟨K', hF, hFin, hK', hnat⟩ := hP hE
    haveI := hFin
    haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
    obtain ⟨σ, c, hact⟩ := NtLine.natural_transfer hH AM hNtCN hsup hinf hK'
      (addCommutantScalar_statedOmegaPlus_two
        (NtLine.exists_ne_zero_one_of_four_le (by omega))) hnat
    refine ⟨c, ?_⟩
    have hf : (fun v : Fin 2 ⊕ Fin 2 → AM.K => σ (StatedQuadPlus 2 K' (σ.symm ∘ v))) =
        StatedQuadPlus 2 AM.K := by
      funext v
      rw [← statedQuadPlus_comp σ (n := 2) (σ.symm ∘ v)]
      congr 1
      funext i
      simp
    rwa [hf] at hact
  · obtain ⟨K', hF, hFin, hK', b, c', hirr, hnat⟩ := hMi hE
    haveI := hFin
    haveI : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    obtain ⟨σ, c, hact⟩ := NtLine.natural_transfer hH AM hNtCN hsup hinf hK'
      (addCommutantScalar_statedOmegaMinus (m := 2) le_rfl hirr) hnat
    refine ⟨σ b, σ c', irreducible_map σ hirr, c, ?_⟩
    have hf : (fun v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → AM.K =>
        σ (StatedQuadMinus 2 K' b c' (σ.symm ∘ v))) = StatedQuadMinus 2 AM.K (σ b) (σ c') := by
      funext v
      rw [← statedQuadMinus_comp σ (n := 2) (b := b) (c := c') rfl rfl (σ.symm ∘ v)]
      congr 1
      funext i
      simp
    rwa [hf] at hact

theorem ntLine_of (hNt : StrothNtStatement) (hNK : E1NaturalKStatement) (hS1 : Step1Statement)
    (hC : NtCentralStatement) (hKF1 : ParabolicStatement) (hKF2 : NatIrredStatement) :
    NtLineStatement := by
  intro G _ _ M Q Z B t hH AM
  classical
  have hc := hH.ctx
  have ht : t ∈ LB M Q B := hH.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hKZ : Nat.card AM.K = Nat.card Z := AM.glob.card
  have hK4 : 4 ≤ Nat.card AM.K := by omega
  have hNtCN : Nt M (LB M Q B) t = hc.CN t :=
    hNt G M Q Z B hc 4 hH.case.width (by norm_num) hH.noA2 hH.gen t hH.mem hH.notQ
  have hCt := hC G M Q Z B t hH
  obtain ⟨h8, hhyp, hTS, h4⟩ := hS1 G M Q Z B t hH AM
  have hXO : AM.actImage (E1Xpre M Q B t) ≤ AM.S.O := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact fun e => AM.φ_Qf y e
  obtain ⟨D⟩ : Nonempty (LCData AM.S (AM.Vsp hc t) (AM.actImage (E1Xpre M Q B t))) := by
    rcases (caseE1_iff M Q Z B t).mp hH.case with hE | hE
    · obtain ⟨c, hact⟩ := (hNK G M Q Z B t hH AM).1 hE
      exact (lcData_of hKF1 hKF2 AM.K hK4 AM.S h8 hhyp _ hTS h4 _ hXO).1 c hact
    · obtain ⟨b, c', hb, c, hact⟩ := (hNK G M Q Z B t hH AM).2 hE
      exact (lcData_of hKF1 hKF2 AM.K hK4 AM.S h8 hhyp _ hTS h4 _ hXO).2 b c' hb c hact
  have hU := fun g => ((hKF1 AM.K hK4 AM.S h8 hhyp _ hTS h4).2.2.1 g).mp
  have hline := NtLine.phi_line hH AM hNtCN hCt hU D
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hNH : Nt M (LB M Q B) t ≤ H0 M Z := hNR.trans hRH
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc ht
  refine ⟨D.β, D.betaProps, ?_, hline, ?_⟩
  ·
    obtain ⟨n, hn, hnQ⟩ : ∃ n ∈ Nt M (LB M Q B) t, n ∉ Q := by
      by_contra hno
      push Not at hno
      have h1 := Subgroup.card_le_of_le (fun n hn => hno n hn)
      rw [hH.case.2.1] at h1
      have hpos : 0 < Nat.card Q := Nat.card_pos
      have h2 : Nat.card Q * 4 ≤ Nat.card Q * Nat.card Z := Nat.mul_le_mul_left _ hq4
      omega
    obtain ⟨cn, hcn⟩ := hline ⟨n, hNH hn⟩ hn
    have hcn0 : cn ≠ 0 := by
      rintro rfl
      apply hnQ
      refine (AM.φ_ker ⟨n, hNH hn⟩).mp (LinearEquiv.ext fun e => ?_)
      simp [hcn e]
    intro r hr e
    have h2 := LinearEquiv.congr_fun
      (NtLine.phi_comm_of_comm_mem AM r ⟨n, hNH hn⟩ (hCt _ hr _ hn)) e
    simp only [LinearEquiv.mul_apply] at h2
    rw [hcn e, hcn (AM.φ r e), map_add, map_smul] at h2
    exact smul_right_injective _ hcn0 (add_left_cancel h2)
  ·
    let Φ : ↥(Nt M (LB M Q B) t) →* (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) :=
      AM.φ.comp (Subgroup.inclusion hNH)
    have hker : Φ.ker = Q.subgroupOf (Nt M (LB M Q B) t) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact AM.φ_ker ⟨x, hNH x.2⟩
    have hcardK : Nat.card Φ.range = Nat.card AM.K := by
      have h1 : Nat.card ↥(Nt M (LB M Q B) t) = Nat.card Φ.ker * Nat.card Φ.range := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index]
      have h2 : Nat.card Φ.ker = Nat.card Q := by
        rw [hker]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
      rw [hH.case.2.1, h2, ← hKZ] at h1
      exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
    have hsub : (Φ.range : Set (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E)) ⊆ Set.range D.unip := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨c, hc'⟩ := hline ⟨x, hNH x.2⟩ x.2
      exact ⟨c, LinearEquiv.ext fun e => by rw [D.unip_apply]; exact (hc' e).symm⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      calc Nat.card (Set.range D.unip) ≤ Nat.card AM.K := Finite.card_range_le _
        _ = Nat.card Φ.range := hcardK.symm
        _ = Nat.card (Φ.range : Set (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E)) := rfl) (Set.toFinite _)
    intro c
    have hmem : D.unip c ∈ (Φ.range : Set (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E)) := by
      rw [heq]
      exact ⟨c, rfl⟩
    obtain ⟨x, hx⟩ := hmem
    refine ⟨⟨x, hNH x.2⟩, x.2, fun e => ?_⟩
    have := LinearEquiv.congr_fun hx e
    rw [D.unip_apply] at this
    exact this

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1
