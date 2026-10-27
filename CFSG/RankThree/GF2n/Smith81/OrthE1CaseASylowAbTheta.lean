module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbForm
public import CFSG.RankThree.GF2n.Smith81.OrthE1CtStructure
import CFSG.RankThree.GF2n.Smith81.OrthE1Small
import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Theta


theorem theta_facts {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    {β : AM.M₀.E →ₗ[AM.K] AM.M₀.E} (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hβRx : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t →
      ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hβNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t →
      ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hCN : CtNormalizesStatement) (hSplit : RtSplitStatement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Qf : QuadraticForm AM.K (ι → AM.K)}
    (hf : FormData ι AM.K Qf)
    (cV : (AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K))
    (hAN : ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) cV ⇑Qf) :
    (∀ c ∈ E1Ct hH.ctx t, ∀ e, phiG AM c (β e) = β (phiG AM c e)) ∧
    ∃ Θ : ↥(E1Ct hH.ctx t) →* GL ι AM.K,
      (∀ (c : ↥(E1Ct hH.ctx t)) (v : AM.M₀.E) (hv : v ∈ AM.Vsp hH.ctx t),
        ∃ hw : phiG AM c v ∈ AM.Vsp hH.ctx t,
          cV ⟨phiG AM c v, hw⟩ = (Θ c : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩) ∧
      (∀ c : ↥(E1Ct hH.ctx t), Θ c ∈ CFSG.MatrixModel.isometryCore ⇑Qf) ∧
      (∀ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t, Θ ⟨x, hx⟩ ∈ StatedOmega ⇑Qf) ∧
      (∀ ω ∈ StatedOmega ⇑Qf, ∃ x ∈ E1Xpre M Q B t, ∃ hx : x ∈ E1Ct hH.ctx t,
        Θ ⟨x, hx⟩ = ω) ∧
      (∀ c (hc : c ∈ E1Ct hH.ctx t), Θ ⟨c, hc⟩ = 1 → c ∈ Nt M (LB M Q B) t) := by
  revert cV hAN
  set V := AM.Vsp hH.ctx t with hVdef
  set C := E1Ct hH.ctx t with hCdef
  intro cV hAN
  have hc : Ctx M Q Z B := hH.ctx
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have htQ : t ∉ Q := hH.notQ
  have hK4 : 4 ≤ Nat.card AM.K := by
    rw [AM.glob.card]
    exact hc.hyp.q4
  have hfin8 : Module.finrank AM.K AM.M₀.E = 8 := by
    have h := AM.glob.finrank_E hH.sec.width (by omega : 1 < Nat.card AM.K)
    omega
  have hhyp : AM.S.IsHyp := AM.glob.hyperbolic
  have hQH0 : Q ≤ H0 M Z := hc.Q_le_H0
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M (LB M Q B) t
  have hNH0 : Nt M (LB M Q B) t ≤ H0 M Z := hNR.trans hRH0
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc hH.mem
  obtain ⟨-, -, hNXsup, hXnorm, hXperf, -, -, -, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨hXV, hcl1, hcl2, hcl3⟩ := hAN
  have hNcard : Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z := hH.case.2.1
  set R := Rt M (LB M Q B) t with hRdef
  set N := Nt M (LB M Q B) t with hNdef
  set X := E1Xpre M Q B t with hXdef
  have hRC : R ≤ C := fun r hr => Subgroup.mem_inf.mpr ⟨(hc.Rt_le_CommQ t) hr, hRH0 hr⟩
  have hcomR : ⁅R, R⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  have hXR : X ≤ R := sup_le hcomR (hQN.trans hNR)
  have hXC : X ≤ C := hXR.trans hRC
  have hNC : N ≤ C := hNR.trans hRC
  have hQC : Q ≤ C := hQN.trans hNC
  have hCH0 : C ≤ H0 M Z := fun c hc' => (Subgroup.mem_inf.mp hc').2
  have hCM : ∀ c ∈ C, c ∈ M := fun c hc' => (Subgroup.mem_inf.mp (hCH0 hc')).1
  have hCcomm : ∀ c ∈ C, ⁅c, t⁆ ∈ Q := fun c hc' =>
    (mem_CommQ.mp (Subgroup.mem_inf.mp hc').1).2
  have hXH0 : X ≤ H0 M Z := hXR.trans hRH0
  have hRNX : ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ X, r = n * x := fun r hr =>
    mem_sup_normalizes hNR hXnorm r (by rw [hNXsup]; exact hr)
  have hcxX : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro c hc' x hx
    have h := (hCN G M Q Z B t hH c⁻¹ (hCM _ (C.inv_mem hc')) (hCcomm _ (C.inv_mem hc'))).2.2
    have hx' : x ∈ conjSubgroup c⁻¹ X := by
      rw [h]
      exact hx
    have := mem_conjSubgroup.mp hx'
    simpa using this
  have hQnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc' q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hCM c hc')) q).mp hq
  have hψ1 : phiG AM 1 = 1 := phiG_one AM
  have hψmul : ∀ c ∈ C, ∀ d ∈ C, phiG AM (c * d) = phiG AM c * phiG AM d :=
    fun c hc' d hd => phiG_mul AM (hCH0 hc') (hCH0 hd)
  have hψO : ∀ c ∈ C, phiG AM c ∈ AM.S.O := fun c hc' => by
    rw [phiG_mem AM (hCH0 hc')]
    exact fun e => AM.φ_Qf _ e
  have hψQ : ∀ q ∈ Q, phiG AM q = 1 := fun q hq => by
    rw [phiG_mem AM (hQH0 hq)]
    exact (AM.φ_ker _).mpr hq
  have hψN : ∀ n ∈ N, ∃ l : AM.K, ∀ e, phiG AM n e = e + l • β e := fun n hn => by
    obtain ⟨l, hl⟩ := hβNx ⟨n, hNH0 hn⟩ hn
    exact ⟨l, fun e => by rw [phiG_mem AM (hNH0 hn)]; exact hl e⟩
  have hψR : ∀ r ∈ R, ∀ e, phiG AM r (β e) = β (phiG AM r e) := fun r hr e => by
    rw [phiG_mem AM (hRH0 hr)]
    exact hβRx ⟨r, hRH0 hr⟩ hr e
  obtain ⟨c₀, hc₀, hc0⟩ : ∃ c₀ : AM.K, c₀ ≠ 0 ∧ ∀ e, phiG AM t e = e + c₀ • β e := by
    obtain ⟨c₀, hc₀⟩ := hψN t htN
    refine ⟨c₀, fun h0 => htQ ?_, hc₀⟩
    apply phiG_ker AM (hNH0 htN)
    ext e
    rw [hc₀ e, h0, zero_smul, add_zero]
    rfl
  have hβc : ∀ c ∈ C, ∀ e, phiG AM c (β e) = β (phiG AM c e) := by
    intro c hc' e
    have htC : t ∈ C := hNC htN
    have hcomC : ⁅c, t⁆ ∈ C := hQC (hCcomm c hc')
    have htCc : t * c ∈ C := C.mul_mem htC hc'
    have hct : phiG AM ⁅c, t⁆ = 1 := hψQ _ (hCcomm c hc')
    have e1 : c * t = ⁅c, t⁆ * (t * c) := by
      simp only [commutatorElement_def]
      group
    have hA : phiG AM (c * t) = phiG AM c * phiG AM t := hψmul c hc' t htC
    have hB : phiG AM (c * t) = phiG AM t * phiG AM c := by
      rw [e1, hψmul _ hcomC _ htCc, hct, one_mul, hψmul t htC c hc']
    have hcomm' : phiG AM c * phiG AM t = phiG AM t * phiG AM c := by
      rw [← hA]
      exact hB
    have hpt : phiG AM c (phiG AM t e) = phiG AM t (phiG AM c e) := by
      have := congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f e) hcomm'
      simpa [LinearEquiv.mul_apply] using this
    rw [hc0 e, map_add, map_smul, hc0 (phiG AM c e)] at hpt
    exact smul_right_injective _ hc₀ (add_left_cancel hpt)
  have hV : ∀ c ∈ C, ∀ v ∈ V, phiG AM c v ∈ V := fun c hc' v hv =>
    (beta_eq_zero_iff AM.S hβ _).mp (by
      rw [← hβc c hc' v, (beta_eq_zero_iff AM.S hβ v).mpr hv, map_zero])
  have hfixN : ∀ n ∈ N, ∀ v ∈ V, phiG AM n v = v := fun n hn v hv => by
    obtain ⟨l, hl⟩ := hψN n hn
    rw [hl v, (beta_eq_zero_iff AM.S hβ v).mpr hv, smul_zero, add_zero]
  have hmemX : ∀ x ∈ X, phiG AM x ∈ AM.actImage X := fun x hx => by
    rw [phiG_mem AM (hXH0 hx)]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hV4 : Module.finrank AM.K V = 4 := by
    rw [LinearEquiv.finrank_eq cV, Module.finrank_fintype_fun_eq_card, hf.card]
  have hV0 : V ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hV4
    norm_num at hV4
  have hrange : LinearMap.range β = V := ctS_beta_range_eq AM.S hfin8 hV4 hβ
  obtain ⟨σ, hσ⟩ := beta_section AM.S hfin8 hV4 hβ
  have hβne : ∃ e, β e ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
    refine ⟨σ ⟨v, hv⟩, ?_⟩
    rw [hσ ⟨v, hv⟩]
    exact hv0
  have hββ : ∀ e, β (β e) = 0 := fun e => hβ.kills _ (hβ.range e)
  have hscal : ∀ a : AM.K, (∀ e, a • β e = 0) → a = 0 := fun a ha => by
    obtain ⟨e0, he0⟩ := hβne
    rcases smul_eq_zero.mp (ha e0) with h | h
    · exact h
    · exact absurd h he0
  have hψNex : ∀ l : AM.K, ∃ n ∈ N, ∀ e, phiG AM n e = e + l • β e := by
    have hψN' : ∀ n : ↥N, ∃ l : AM.K, ∀ e, phiG AM (n : G) e = e + l • β e :=
      fun n => hψN n n.2
    choose cf hcf using hψN'
    have hcfu : ∀ (n : ↥N) (a : AM.K), (∀ e, phiG AM (n : G) e = e + a • β e) → a = cf n := by
      intro n a ha
      have h1 : ∀ e, (a - cf n) • β e = 0 := by
        intro e
        have h2 : a • β e = cf n • β e := add_left_cancel ((ha e).symm.trans (hcf n e))
        rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp (hscal _ h1)
    have hcfmul : ∀ n m : ↥N, cf (n * m) = cf n + cf m := by
      intro n m
      symm
      apply hcfu (n * m)
      intro e
      have hnm : phiG AM ((n * m : ↥N) : G) = phiG AM (n : G) * phiG AM (m : G) :=
        hψmul _ (hNC n.2) _ (hNC m.2)
      rw [hnm, LinearEquiv.mul_apply, hcf m e, map_add, map_smul, hcf n e, hcf n (β e), hββ,
        smul_zero, add_zero, add_smul]
      abel
    have hcfQ : ∀ n : ↥N, cf n = 0 ↔ (n : G) ∈ Q := by
      intro n
      constructor
      · intro h
        apply phiG_ker AM (hNH0 n.2)
        ext e
        rw [hcf n e, h, zero_smul, add_zero]
        rfl
      · intro hq
        have h1 : phiG AM (n : G) = 1 := hψQ _ hq
        apply hscal
        intro e
        have h2 := hcf n e
        rw [h1] at h2
        have h3 : (1 : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) e = e := rfl
        rw [h3] at h2
        exact add_left_cancel (h2.symm.trans (add_zero e).symm)
    obtain ⟨cM, hcM⟩ : ∃ cM : ↥N →* Multiplicative AM.K,
        ∀ n, cM n = Multiplicative.ofAdd (cf n) :=
      ⟨{ toFun := fun n => Multiplicative.ofAdd (cf n)
         map_one' := by
           show Multiplicative.ofAdd (cf 1) = 1
           rw [ofAdd_eq_one, hcfQ 1]
           exact Q.one_mem
         map_mul' := fun n m => by
           show Multiplicative.ofAdd (cf (n * m)) =
             Multiplicative.ofAdd (cf n) * Multiplicative.ofAdd (cf m)
           rw [hcfmul, ofAdd_add] }, fun n => rfl⟩
    have hkercM : cM.ker = Q.subgroupOf N := by
      ext n
      rw [MonoidHom.mem_ker, hcM, ofAdd_eq_one, hcfQ n, Subgroup.mem_subgroupOf]
    have hQcard : Nat.card ↥(Q.subgroupOf N) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
    have hNcardM : Nat.card ↥N = Nat.card ↥(Q.subgroupOf N) * Nat.card cM.range := by
      rw [← hkercM, ← Subgroup.index_ker, Subgroup.card_mul_index]
    have hcardR : Nat.card cM.range = Nat.card AM.K := by
      rw [hQcard, hNcard] at hNcardM
      have h2 : Nat.card Z = Nat.card cM.range :=
        Nat.eq_of_mul_eq_mul_left Nat.card_pos hNcardM
      rw [AM.glob.card, h2]
    have htop : cM.range = ⊤ := Subgroup.eq_top_of_card_eq cM.range (hcardR.trans rfl)
    intro l
    have hmem : Multiplicative.ofAdd l ∈ cM.range := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
    have hxl : cf x = l := by
      rw [hcM] at hx
      exact Multiplicative.ofAdd.injective hx
    refine ⟨(x : G), x.2, fun e => ?_⟩
    rw [hcf x e, hxl]
  have hTS : AM.S.IsTS V := by
    intro v hv
    rw [← hrange] at hv
    obtain ⟨e, rfl⟩ := hv
    have hiso : AM.M₀.Qf (AM.φ ⟨t, hNH0 htN⟩ e) = AM.M₀.Qf e := AM.φ_Qf _ e
    have hφt : AM.φ ⟨t, hNH0 htN⟩ e = e + c₀ • β e := by
      rw [← phiG_mem AM (hNH0 htN)]
      exact hc0 e
    rw [hφt] at hiso
    have h1 := AM.M₀.Qf_add e (c₀ • β e)
    have h2 := AM.M₀.Qf_smul c₀ (β e)
    have h3 := hβ.alt e
    rw [h1, h2, LinearMap.map_smul, h3, smul_zero, add_zero] at hiso
    have h4 : c₀ ^ 2 * AM.M₀.Qf (β e) = 0 := by linear_combination hiso
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h5) hc₀
    · exact h5
  have hperp := (parabolic_holds AM.K hK4 AM.S hfin8 hhyp V hTS hV4).1
  have hpar := (parabolic_holds AM.K hK4 AM.S hfin8 hhyp V hTS hV4).2.2.1
  have hkerR : ∀ r ∈ R, (∀ v ∈ V, phiG AM r v = v) → r ∈ N := by
    intro r hr hfix
    obtain ⟨n, hn, y, hy, rfl⟩ := hRNX r hr
    have hyfix : ∀ v ∈ V, phiG AM y v = v := by
      intro v hv
      have h1 : phiG AM (n * y) v = phiG AM n (phiG AM y v) := by
        rw [hψmul n (hNC hn) y (hXC hy), LinearEquiv.mul_apply]
      have h2 := hfixN n hn _ (hV y (hXC hy) v hv)
      exact h2.symm.trans (h1.symm.trans (hfix v hv))
    have hyQ : y ∈ Q := phiG_ker AM (hXH0 hy) (hcl3 (phiG AM y) (hmemX y hy) hyfix)
    exact N.mul_mem hn (hQN hyQ)
  obtain ⟨Θ, hΘ⟩ := ctS_rep_exists AM.S (phiG AM) C hψ1 hψmul hV cV
  have hΘeq : ∀ (x : G) (hx : x ∈ X) (A : GL ι AM.K),
      (∀ (v : AM.M₀.E) (hv : v ∈ V),
        cV ⟨phiG AM x v, hV x (hXC hx) v hv⟩ = (A : Matrix ι ι AM.K) *ᵥ cV ⟨v, hv⟩) →
      Θ ⟨x, hXC hx⟩ = A := by
    intro x hx A hA
    apply Units.ext
    apply mat_eq_of_mulVec
    intro w
    have h1 := hΘ ⟨x, hXC hx⟩ (cV.symm w)
    have h2 := hA (cV.symm w).1 (cV.symm w).2
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [Subtype.coe_eta, LinearEquiv.apply_symm_apply] at h2
    exact h1.symm.trans h2
  have hΘX : ∀ (x : G) (hx : x ∈ X), Θ ⟨x, hXC hx⟩ ∈ StatedOmega ⇑Qf := by
    intro x hx
    obtain ⟨A, hA, hAv⟩ := hcl1 (phiG AM x) (hmemX x hx)
    rw [hΘeq x hx A hAv]
    exact hA
  have hΘX' : ∀ ω ∈ StatedOmega ⇑Qf, ∃ x : G, ∃ hx : x ∈ X, Θ ⟨x, hXC hx⟩ = ω := by
    intro ω hω
    obtain ⟨g, hg, hgv⟩ := hcl2 ω hω
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
    have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    refine ⟨y, hyX, hΘeq y hyX ω (fun v hv => ?_)⟩
    have hφ : phiG AM (y : G) v = g v := by
      rw [phiG_mem AM y.2, ← hyg]
    exact (congrArg cV (Subtype.ext hφ)).trans (hgv v hv)
  have hΘO : ∀ c : ↥C, Θ c ∈ CFSG.MatrixModel.isometryCore ⇑Qf := fun c =>
    theta_isom_of hTS hβ hσ hperp hV0 cV (phiG AM) C X hV hψO hβc hXC hcxX Θ hΘ Qf hf.natIrr
      hf.normalizer hΘX hΘX' c.1 c.2
  have hker : ∀ (c : G) (hc' : c ∈ C), Θ ⟨c, hc'⟩ = 1 → c ∈ N := by
    intro c hc' h1
    have hcfix : ∀ v ∈ V, phiG AM c v = v := by
      intro v hv
      have h2 := hΘ ⟨c, hc'⟩ ⟨v, hv⟩
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact congrArg Subtype.val (cV.injective h2)
    have hcomm := commute_of_unipotent hβ hβne (phiG AM) C R X N Q hψ1 hψmul hV hXC hXR hRC
      (le_sup_right : Q ≤ ⁅R, R⁆ ⊔ Q) hXperf hcxX hQnorm hψQ hψR hψN hkerR c hc' hcfix
    obtain ⟨l, hl⟩ := unip_line hβ hσ hTS hpar (phiG AM) C X hψO hβc hV hXC cV Θ hΘ Qf
      hf.natIrr hΘX' c hc' hcfix hcomm
    obtain ⟨n, hn, hnl⟩ := hψNex l
    have hnC : n ∈ C := hNC hn
    have hcn : phiG AM c = phiG AM n := by
      ext e
      rw [hl e, hnl e]
    have hpt : phiG AM (n⁻¹ * c) = 1 := by
      rw [hψmul n⁻¹ (C.inv_mem hnC) c hc', hcn, ← hψmul n⁻¹ (C.inv_mem hnC) n hnC,
        inv_mul_cancel, hψ1]
    have hq : n⁻¹ * c ∈ Q := phiG_ker AM (hCH0 (C.mul_mem (C.inv_mem hnC) hc')) hpt
    have hcN : c ∈ N := by
      have e : c = n * (n⁻¹ * c) := by group
      rw [e]
      exact N.mul_mem hn (hQN hq)
    exact hcN
  refine ⟨hβc, Θ, fun c v hv => ⟨hV c c.2 v hv, hΘ c ⟨v, hv⟩⟩, hΘO,
    fun x hx => ⟨hXC hx, hΘX x hx⟩, fun ω hω => ?_, hker⟩
  obtain ⟨x, hx, h⟩ := hΘX' ω hω
  exact ⟨x, hx, hXC hx, h⟩

end Theta

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
