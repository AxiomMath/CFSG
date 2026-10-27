module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappaLayer
public import CFSG.RankThree.GF2n.Stroth80.Sec7LinA0
public import CFSG.RankThree.GF2n.Stroth80.Sec7Unconditional
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommN
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerDim

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

namespace S715K

theorem nondegenerate_polarBilin_comp {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {Qf : QuadraticForm K W} (hQ : (polarBilin Qf).Nondegenerate)
    (f : V ≃ₗ[K] W) : (polarBilin (Qf.comp (f : V →ₗ[K] W))).Nondegenerate := by
  have key : ∀ x y : V, polarBilin (Qf.comp (f : V →ₗ[K] W)) x y = polarBilin Qf (f x) (f y) := by
    intro x y
    simp only [polarBilin_apply_apply, polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      map_add]
  refine ⟨fun x hx => f.injective ?_, fun y hy => f.injective ?_⟩
  · rw [map_zero]
    refine hQ.1 _ fun w => ?_
    obtain ⟨v, rfl⟩ := f.surjective w
    rw [← key]
    exact hx v
  · rw [map_zero]
    refine hQ.2 _ fun w => ?_
    obtain ⟨v, rfl⟩ := f.surjective w
    rw [← key]
    exact hy v

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E} {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {Z0 : Subgroup G} {ψ : M₀.E →ₗ[K] M₀.E}
  {φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K}
  {e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

theorem card_lt_of_rank (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZcard : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hK : KModel hS t Z0 ψ φ₈ e)
    {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (hcardV : Nat.card ↥(bar M Q Z0) = Nat.card K) {y : ↥(bar M Q (H0 M Z))}
    (hyR : (y : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t))
    (h4 : Module.finrank K (LinearMap.range ((S715L.deltaAct hS hK.mem ⟨(y : Mbar M Q), hyR⟩ :
      ↥(S715L.deltaSub hS t) →ₗ[K] ↥(S715L.deltaSub hS t)) - LinearMap.id)) = 4) :
    Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ^ 2 *
        Nat.card ↥(Subgroup.centralizer ({y} : Set ↥(bar M Q (H0 M Z))) ⊓
          (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) <
      Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) := by
  classical
  set Nh := (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) with hNh
  set C := Subgroup.centralizer ({y} : Set ↥(bar M Q (H0 M Z))) ⊓ Nh with hC
  set f := (S715L.deltaAct hS hK.mem ⟨(y : Mbar M Q), hyR⟩ :
    ↥(S715L.deltaSub hS t) →ₗ[K] ↥(S715L.deltaSub hS t)) - LinearMap.id with hf
  have hNbar : ∀ m : ↥Nh, ((m : ↥(bar M Q (H0 M Z))) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
    fun m => Subgroup.mem_subgroupOf.mp m.2
  let Δ : ↥Nh → ↥(S715L.deltaSub hS t) := fun m =>
    ⟨S714.delta hS t _ (S714.mem_bar_H0_of_CN (hNbar m)), S715L.delta_mem_deltaSub hS (hNbar m)⟩
  let F₀ : ↥Nh → ↥(LinearMap.range f) := fun m => ⟨f (Δ m), LinearMap.mem_range_self f _⟩
  have hF₀surj : Function.Surjective F₀ := by
    rintro ⟨_, D, rfl⟩
    obtain ⟨g, hg, hgD⟩ := (S715L.mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZcard
      hCRW hMp hS hs hr).mp D.2
    refine ⟨⟨⟨g, S714.mem_bar_H0_of_CN hg⟩, Subgroup.mem_subgroupOf.mpr hg⟩, ?_⟩
    apply Subtype.ext
    show f (Δ _) = f D
    congr 1
    exact Subtype.ext hgD.symm
  have hF₀c : ∀ m c : ↥Nh, (c : ↥(bar M Q (H0 M Z))) ∈
      Subgroup.centralizer ({y} : Set ↥(bar M Q (H0 M Z))) → F₀ (m * c) = F₀ m := by
    intro m c hcy
    apply Subtype.ext
    show f (Δ (m * c)) = f (Δ m)
    have hmul : Δ (m * c) = Δ m + Δ c :=
      Subtype.ext (S714.delta_mul h310chi h52a hS hs hr (hNbar m) (hNbar c))
    have hfc : f (Δ c) = 0 := by
      have hyc : (y : Mbar M Q) * ((c : ↥(bar M Q (H0 M Z))) : Mbar M Q) * (y : Mbar M Q)⁻¹ =
          ((c : ↥(bar M Q (H0 M Z))) : Mbar M Q) := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcy
        have h2 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul] at h2
        rw [← h2, mul_inv_cancel_right]
      rw [hf, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      show S715L.deltaAct hS hK.mem ⟨(y : Mbar M Q), hyR⟩ ⟨_, _⟩ = ⟨_, _⟩
      rw [S715L.deltaAct_delta hS hK.mem ⟨(y : Mbar M Q), hyR⟩ (hNbar c)]
      exact Subtype.ext (S714.delta_congr hS t hyc _ _)
    rw [hmul, map_add, hfc, add_zero]
  set C' := C.subgroupOf Nh with hC'
  let G₀ : ↥Nh ⧸ C' → ↥(LinearMap.range f) := Quotient.lift F₀ (fun a b hab => by
    have h1 : a⁻¹ * b ∈ C' := QuotientGroup.leftRel_apply.mp hab
    have h2 : ((a⁻¹ * b : ↥Nh) : ↥(bar M Q (H0 M Z))) ∈
        Subgroup.centralizer ({y} : Set ↥(bar M Q (H0 M Z))) := (Subgroup.mem_subgroupOf.mp h1).1
    have h3 := hF₀c a (a⁻¹ * b) h2
    rw [mul_inv_cancel_left] at h3
    exact h3.symm)
  have hG₀ : Function.Surjective G₀ := by
    intro x
    obtain ⟨m, rfl⟩ := hF₀surj x
    exact ⟨QuotientGroup.mk m, rfl⟩
  have hle := Nat.card_le_card_of_surjective G₀ hG₀
  rw [Module.natCard_eq_pow_finrank (K := K), h4] at hle
  have hNcard : Nat.card ↥C' * Nat.card (↥Nh ⧸ C') = Nat.card ↥Nh := C'.card_mul_index
  have hCcard : Nat.card ↥C' = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hVcard : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = Nat.card K :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.Z0_le_H0).toEquiv).trans hcardV
  rw [hVcard, ← hNcard, hCcard]
  have hq : 1 < Nat.card K := by have := hK.three_lt; omega
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hq24 : Nat.card K ^ 2 < Nat.card K ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
  calc Nat.card K ^ 2 * Nat.card ↥C < Nat.card K ^ 4 * Nat.card ↥C :=
        Nat.mul_lt_mul_of_pos_right hq24 hCpos
    _ ≤ Nat.card (↥Nh ⧸ C') * Nat.card ↥C := Nat.mul_le_mul_right _ hle
    _ = Nat.card ↥C * Nat.card (↥Nh ⧸ C') := mul_comm _ _

end S715K

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.sec715_kappa (hLS : S715L.Sec715LayerSplitStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement)
    (hZc : Sec7CentreMpStatement) (hCRW : Sec7CRWStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (hZt : Sec7ZtStatement) (hA : Sec7AExistsStatement)
    (hc : Ctx M Q Z B) {t : G} (hs : Sec7Hyp hc 16 t) (hp : OmegaPlusNat hc t 4)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZ0N : IsCentrePre Z0 (hc.CN t) Q) :
    ∀ h : ↥(bar M Q (H0 M Z)),
      (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        h * a * h⁻¹ ∈ (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))) →
      (¬ ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        h * a * h⁻¹ ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) →
      ∀ b ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), b ≠ 1 →
        (∀ x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
          ∃ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
            ⁅h * b * h⁻¹, x⁆ * z⁻¹ ∈
              conjSubgroup h ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))) ∧
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ^ 2 *
            Nat.card ↥(Subgroup.centralizer ({h * b * h⁻¹} : Set ↥(bar M Q (H0 M Z))) ⊓
              (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) <
          Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) := by
  classical
  intro h hL hout b hb hb1
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 16 t hs
  obtain ⟨K, hF, hFin, γ, M₀, ρ, b₀, hS, ψ, hψdef, hψV, hψW, hfaith, hpar, hpar'⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  obtain ⟨φ₈, e, hφr, hφk, he⟩ := S715L.exists_phi8 hS ht hp
  have hcardV : Nat.card ↥(bar M Q Z0) = Nat.card K := by
    have h1 := Tim37.card_bar_mul_card_of_le (M := M) hQZ0 hZ0M
    rw [hZcard G M Q Z B hc 16 t hs Z0 hZ0] at h1
    have h3 : Nat.card ↥(bar M Q Z0) = Nat.card Z :=
      Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (by rw [mul_comm]; exact h1)
    rw [h3, hS.card]
  have hVW : ∀ v ∈ hc.VtSub hS.model t, ψ v = 0 := by
    intro v hv
    obtain ⟨z, hz, hzx⟩ := hpar' 1
    have hzN : z ∈ bar M Q (hc.CN t) := bar_mono' (sec7ctr_Z0_le_CN hc hs hZ0) hz
    have h1 := (S714.dmap_CN_facts h310chi h52a hS hs hr hzN).1 v hv
    rw [S714.dmap, hzx, one_smul, add_sub_cancel_left] at h1
    exact h1
  have hK : S715K.KModel hS t Z0 ψ φ₈ e :=
    { mem := ht
      Z0_le_H0 := bar_mono' (hZ0.le.trans hRH)
      Z0_le_Rt := bar_mono' hZ0.le
      psi_sq := fun x => hVW _ ((hc.mem_VtSub hS.model t).mpr ((hψV _).mp
        (LinearMap.mem_range_self ψ x)))
      psi_V := fun x => (hc.mem_VtSub hS.model t).mpr ((hψV _).mp (LinearMap.mem_range_self ψ x))
      psi_V' := fun v hv => LinearMap.mem_range.mp ((hψV v).mpr ((hc.mem_VtSub hS.model t).mp hv))
      psi_W := fun x => by
        rw [S714.mem_wsub]
        constructor
        · intro hx
          obtain ⟨q, hq, rfl⟩ := M₀.π_surj x
          exact M₀.pi_mem_img ((hψW q hq).mpr hx) hq
        · intro hx
          obtain ⟨q, hqW, hqQ, rfl⟩ := M₀.mem_img.mp hx
          exact (hψW q hqQ).mp hqW
      par := hpar
      par' := hpar'
      faith := hfaith
      phi_range := hφr
      phi_ker := hφk
      phi_e := he
      three_lt := by
        rw [hS.card]
        have := hc.hyp.q4
        omega }
  obtain ⟨Tt, F⟩ := hc.sec715Frame h34 hZt hZcard hZc hZV hs hZ0 M₀ (S715L.hAct hS)
    (fun y hy x hx => S715L.hAct_compat hS y hy x hx)
  obtain ⟨u, hu0, hQu, hLu⟩ := S715K.exists_point_LB h34 hRoot hS hs φ₈ hφr hφk e he
  obtain ⟨hW, hD⟩ := hLS G M Q Z B hc 16 t hs hp rfl Z0 hZ0 hZ0N K γ M₀ ρ b₀ hS φ₈ hφr hφk e he
  obtain ⟨ho3, ho1, ho2, ho4⟩ := hK.layer_facts F hL hout hu0 hQu hLu hW hD
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨z₁, hz₁, hz₁x⟩ := hpar' 1
    have ha₁V : (⟨z₁, hK.Z0_le_H0 hz₁⟩ : ↥(bar M Q (H0 M Z))) ∈
        (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hz₁
    have hopm : opm (S715L.hAct hS ⟨z₁, hK.Z0_le_H0 hz₁⟩) = ψ := LinearMap.ext fun x => by
      rw [opm_apply, S715L.hAct_apply, hz₁x, one_smul, add_sub_cancel_left]
    have hrangeψ : LinearMap.range ψ = hc.VtSub hS.model t := by
      ext v
      exact ⟨fun ⟨x, hx⟩ => hx ▸ hK.psi_V x, fun hv => hK.psi_V' v hv⟩
    have ha₁1 : (⟨z₁, hK.Z0_le_H0 hz₁⟩ : ↥(bar M Q (H0 M Z))) ≠ 1 := by
      intro h1
      have h2 : ψ = 0 := by
        rw [← hopm, h1, map_one]
        exact LinearMap.ext fun x => by simp [opm_apply]
      have h3 : hc.VtSub hS.model t = ⊥ := by
        rw [← hrangeψ, h2, LinearMap.range_zero]
      have h4 := hK.finrank_V
      rw [h3, finrank_bot] at h4
      exact absurd h4 (by norm_num)
    have hTt1 : Tt 1 = hc.VtSub hS.model t := by
      have h1 := F.Tt_range 1 _ ha₁V ha₁1
      rw [one_mul, inv_one, mul_one, hopm, hrangeψ] at h1
      exact h1.symm
    have hparH : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), ∃ c : K,
        ∀ x, S715L.hAct hS a x = x + c • ψ x := fun a ha => by
      obtain ⟨c, hc'⟩ := hpar _ (Subgroup.mem_subgroupOf.mp ha)
      exact ⟨c, fun x => by rw [S715L.hAct_apply]; exact hc' x⟩
    have hparH' : ∀ c : K, ∃ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
        ∀ x, S715L.hAct hS a x = x + c • ψ x := fun c => by
      obtain ⟨z, hz, hzx⟩ := hpar' c
      exact ⟨⟨z, hK.Z0_le_H0 hz⟩, Subgroup.mem_subgroupOf.mpr hz,
        fun x => by rw [S715L.hAct_apply]; exact hzx x⟩
    have hRV : ∀ r' ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
        ∀ v ∈ Tt 1, S715L.hAct hS r' v ∈ Tt 1 := by
      rw [hTt1]
      intro r' hr' v hv
      rw [S715L.hAct_apply]
      exact hc.act_mem_VtSub hS ht _ (Subgroup.mem_subgroupOf.mp hr') v hv
    have hRW : ∀ r' ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
        ∀ w, ψ w = 0 → ψ (S715L.hAct hS r' w) = 0 := fun r' hr' w hw => by
      refine (hK.psi_W _).mpr ?_
      rw [S715L.hAct_apply]
      exact S714.act_mem_wsub hS ht (Subgroup.mem_subgroupOf.mp hr') ((hK.psi_W w).mp hw)
    have hdim : Module.finrank K ↥(Tt 1) = 8 := by rw [hTt1]; exact hK.finrank_V
    have hP : Module.finrank K ((Tt 1).map ((S715L.hAct hS h).conj ψ)) = 2 := by
      rw [hTt1]; exact ho3
    have hS12 : 12 ≤ Module.finrank K ↥((LinearMap.ker ψ).map ((S715L.hAct hS h).conj ψ) ⊔
        Tt 1) := by
      rw [hTt1]; exact ho1
    have hYDY : ∀ n ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w, ψ w = 0 →
        (S715L.hAct hS h).conj ψ (opm (S715L.hAct hS n) ((S715L.hAct hS h).conj ψ w)) = 0 :=
      fun n hn w hw => by
        rw [opm_apply, S715L.hAct_apply]
        exact ho2 _ (Subgroup.mem_subgroupOf.mp hn) w ((hK.psi_W w).mp hw)
    set e₈ : ↥(Tt 1) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := (LinearEquiv.ofEq _ _ hTt1).trans e with he₈
    have hQ : ∀ (r' : ↥(bar M Q (H0 M Z)))
        (hr' : r' ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) (v : ↥(Tt 1)),
        ((quadPlus 4 K).comp (e₈ : ↥(Tt 1) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)))
            ⟨S715L.hAct hS r' v, hRV r' hr' v v.2⟩ =
          ((quadPlus 4 K).comp (e₈ : ↥(Tt 1) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))) v := by
      intro r' hr' v
      have hrR : (r' : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := Subgroup.mem_subgroupOf.mp hr'
      have hv' : (v : M₀.E) ∈ hc.VtSub hS.model t := hTt1 ▸ v.2
      simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, he₈, LinearEquiv.trans_apply]
      have h1 : LinearEquiv.ofEq _ _ hTt1 ⟨S715L.hAct hS r' v, hRV r' hr' v v.2⟩ =
          ⟨(ρ ((⟨(r' : Mbar M Q), hrR⟩ : ↥(bar M Q (Rt M (LB M Q B) t))) : Mbar M Q)).toAdd
            ((⟨(v : M₀.E), hv'⟩ : ↥(hc.VtSub hS.model t)) : M₀.E),
            hc.act_mem_VtSub hS ht _ hrR _ hv'⟩ := Subtype.ext rfl
      rw [h1, hK.phi_e, hK.quad_mulVec]
      rfl
    exact S715K.kappa_of_frame F hparH hparH' (hrangeψ.trans hTt1.symm) hRV hRW hL hout hdim hP
      hS12 hYDY ((quadPlus 4 K).comp (e₈ : ↥(Tt 1) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)))
      (S715K.nondegenerate_polarBilin_comp (nondegenerate_polarBilin_quadPlus 4 K) e₈) hQ
      hK.exists_ne_zero_one b hb
  ·
    exact S715K.card_lt_of_rank h34 hRoot h310chi h51 h52a h52b hNO hZcard hCRW hZc hK hs hr
      hcardV _ (ho4 b hb hb1)

section Certs

theorem sec715Conj_of_layerSplit (hLS : S715L.Sec715LayerSplitStatement)
    (hCent : Sec715CentStatement) (h710 : Stroth710Statement) : Sec715ConjStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp hn Z0 hZ0 hZ0N hTI
  subst hn
  have h34 := stroth34Statement_unconditional
  have h311a := stroth311aStatement_unconditional
  have h51 := stroth51Statement_unconditional
  have hA := sec7AExistsStatement_unconditional
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 16 t hs
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0
    (sec7ctr_Z0_le_CN hc hs hZ0)
  have hsq : ∀ x ∈ hc.CN t, x * x ∈ Z0 := fun x hx => by
    rw [← pow_two]
    exact hopp.2.2.2.2.2.2.2.1 x hx
  have hC : CentTwoInV hc t Z0 := fun k _ hk2 hkc =>
    hCent G M Q Z B hc 16 t hs (Or.inr hp) Z0 hZ0 hZ0N k hk2 hkc
  exact hc.sec715Conj_of_kappa h34 sec7ZtStatement_holds sec7ZCardStatement_holds
    sec7CentreMpStatement_holds sec7ZVStatement_holds
    (sec7CommN_of_34 h34 stroth310Statement_unconditional h311a) h710 hs hZ0 hTI
    (sec7_CN_pgroup_bar h34 h311a hc hs) hC hsq
    (hc.sec715_kappa hLS h34 stroth310RootStatement_unconditional (stroth310Chi_of_34 h34) h51
      stroth52aStatement_holds stroth52bStatement_holds sec7NOrderStatement_holds
      sec7CentreMpStatement_holds sec7CRWStatement_holds sec7ZVStatement_holds
      sec7ZCardStatement_holds sec7ZtStatement_holds hA hs hp hZ0 hZ0N)

end Certs

end CFSG.RankThree.GF2n.Stroth80
