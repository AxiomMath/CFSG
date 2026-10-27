module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Model
public import CFSG.RankThree.GF2n.Stroth80.Sec5Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec5SLDual
import CFSG.RankThree.GF2n.Stroth80.Sec34Spure

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Model

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem B_map_eq_of_Qf (S : M₀.E ≃ₗ[K] M₀.E) (hS : ∀ e, M₀.Qf (S e) = M₀.Qf e) (e f : M₀.E) :
    M₀.B (S e) (S f) = M₀.B e f := by
  have h1 := M₀.Qf_add (S e) (S f)
  have h2 := M₀.Qf_add e f
  rw [← map_add, hS, hS e, hS f] at h1
  linear_combination h2 - h1

theorem eq_range_sub_one_of_perp {T : M₀.E →ₗ[K] M₀.E} {Vs : Submodule K M₀.E}
    (h1 : Vs ≤ LinearMap.range (T - 1)) (h2 : ∀ e, (∀ v ∈ Vs, M₀.B e v = 0) → T e = e) :
    Vs = LinearMap.range (T - 1) := by
  have hnd : M₀.B.Nondegenerate :=
    ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  have hle : M₀.B.orthogonal Vs ≤ LinearMap.ker (T - 1) := by
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    refine h2 e fun v hv => ?_
    have h : M₀.B v e = 0 := he v hv
    rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd Vs
  have hrk := LinearMap.finrank_range_add_finrank_ker (T - 1)
  have hk := Submodule.finrank_mono hle
  have hV := Submodule.finrank_mono h1
  have hVE := Submodule.finrank_le Vs
  exact Submodule.eq_of_le_of_finrank_eq h1 (by omega)

theorem exists_Vt_transport {V : Subgroup G} (hVQ : V ≤ Q) {A : Type*} [AddCommGroup A]
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative A) :
    ∃ ι : A →+ M₀.E, (∀ v : V, ι (Multiplicative.toAdd (ψ (QuotientGroup.mk v))) = M₀.π v) ∧
      ∀ u, ι u = 0 → u = 0 := by
  let f : ↥V →* Multiplicative M₀.E :=
    { toFun := fun v => Multiplicative.ofAdd (M₀.π v)
      map_one' := by simp [Tim79.QuadModel.pi_one M₀]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [M₀.π_mul x (hVQ x.2) y (hVQ y.2)]
        rfl }
  have hf : Z.subgroupOf V ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (M₀.π z) = 1
    rw [(M₀.π_ker _ (hVQ z.2)).mpr (Subgroup.mem_subgroupOf.mp hz)]
    rfl
  let F : Multiplicative A →* Multiplicative M₀.E :=
    (QuotientGroup.lift (Z.subgroupOf V) f hf).comp ψ.symm.toMonoidHom
  have hF : ∀ v : V, F (ψ (QuotientGroup.mk v)) = Multiplicative.ofAdd (M₀.π v) := fun v => by
    simp only [F, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨AddMonoidHom.mk' (fun u => Multiplicative.toAdd (F (Multiplicative.ofAdd u)))
    fun a b => by rw [ofAdd_add, map_mul, toAdd_mul], fun v => ?_, fun u hu => ?_⟩
  · show Multiplicative.toAdd (F (Multiplicative.ofAdd (Multiplicative.toAdd _))) = _
    rw [ofAdd_toAdd, hF, toAdd_ofAdd]
  · obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd u))
    have hu' : ψ (QuotientGroup.mk v) = Multiplicative.ofAdd u := by rw [hv, ψ.apply_symm_apply]
    have h1 : M₀.π (v : G) = 0 := by
      have h2 : Multiplicative.toAdd (F (Multiplicative.ofAdd u)) = 0 := hu
      rw [← hu', hF, toAdd_ofAdd] at h2
      exact h2
    have h3 : (QuotientGroup.mk v : ↥V ⧸ Z.subgroupOf V) = 1 :=
      (QuotientGroup.eq_one_iff v).mpr
        (Subgroup.mem_subgroupOf.mpr ((M₀.π_ker _ (hVQ v.2)).mp h1))
    rw [h3, map_one] at hu'
    exact ofAdd_eq_one.mp hu'.symm

theorem exists_range_pairing {T : M₀.E ≃ₗ[K] M₀.E} (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f)
    {A : Type*} [AddCommGroup A] (ι : A →+ M₀.E)
    (hι : ∀ u, ι u ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))
    (hιs : ∀ e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), ∃ u, ι u = e)
    (hιi : ∀ u, ι u = 0 → u = 0) :
    ∃ β : A →+ A →+ K,
      (∀ (g : A → A) (S : M₀.E ≃ₗ[K] M₀.E), (∀ e f, M₀.B (S e) (S f) = M₀.B e f) →
        (∀ e, S (T e) = T (S e)) → (∀ u, ι (g u) = S (ι u)) → ∀ u u', β (g u) (g u') = β u u') ∧
      ∀ u, u ≠ 0 → ∃ u', β u u' ≠ 0 := by
  set U := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)
  have hpre : ∀ y : M₀.E, ∃ z : M₀.E, y ∈ U → ((T : M₀.E →ₗ[K] M₀.E) - 1) z = y := by
    intro y
    by_cases hy : y ∈ U
    · obtain ⟨z, hz⟩ := hy
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose s hs using hpre
  have hperp : ∀ x ∈ U, ∀ z w : M₀.E,
      ((T : M₀.E →ₗ[K] M₀.E) - 1) z = ((T : M₀.E →ₗ[K] M₀.E) - 1) w → M₀.B x z = M₀.B x w := by
    intro x hx z w hzw
    have hfix : T (z - w) = z - w := by
      have h0 : ((T : M₀.E →ₗ[K] M₀.E) - 1) (z - w) = 0 := by rw [map_sub, hzw, sub_self]
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
      exact h0
    have h0 := (Tim79.QuadModel.mem_range_sub_one_iff' hTB x).mp hx _ hfix
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  let β : A →+ A →+ K := AddMonoidHom.mk'
    (fun u => AddMonoidHom.mk' (fun u' => M₀.B (ι u) (s (ι u'))) fun a b => by
      rw [← map_add (M₀.B (ι u))]
      refine hperp _ (hι u) _ _ ?_
      rw [hs _ (hι (a + b)), map_add ((T : M₀.E →ₗ[K] M₀.E) - 1), hs _ (hι a), hs _ (hι b),
        map_add ι])
    fun a b => by
      ext u'
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, LinearMap.add_apply]
  have hβ : ∀ u u', β u u' = M₀.B (ι u) (s (ι u')) := fun _ _ => rfl
  refine ⟨β, fun g S hSB hST hg u u' => ?_, fun u hu => ?_⟩
  · rw [hβ, hβ, hg, hg]
    have hSU : S (ι u') ∈ U := by rw [← hg]; exact hι _
    rw [hperp _ (by rw [← hg]; exact hι _) (s (S (ι u'))) (S (s (ι u'))) ?_, hSB]
    rw [hs _ hSU]
    have h0 := hs _ (hι u')
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply] at h0 ⊢
    rw [← hST, ← map_sub, h0]
  · by_contra hcon
    push Not at hcon
    apply hu
    apply hιi
    refine M₀.nondeg _ fun z => ?_
    obtain ⟨u', hu'⟩ := hιs _ ⟨z, rfl⟩
    have h1 : M₀.B (ι u) (s (ι u')) = 0 := hcon u'
    rw [hperp _ (hι u) z (s (ι u')) (by rw [hs _ (hι u'), hu'])]
    exact h1

end Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.smul_mem_img_Vt (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) (t : G) (c : K) {e : M₀.E}
    (he : e ∈ M₀.img (Vt M (LB M Q B) B Z t)) : c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
  set V := Vt M (LB M Q B) B Z t
  let S : AddSubgroup M₀.E :=
    { carrier := {e | ∀ c : K, c • e ∈ M₀.img V}
      add_mem' := fun {a b} ha hb c => by
        rw [smul_add]
        exact (M₀.img V).add_mem (ha c) (hb c)
      zero_mem' := fun c => by
        rw [smul_zero]
        exact (M₀.img V).zero_mem
      neg_mem' := fun {a} ha c => by
        rw [smul_neg]
        exact (M₀.img V).neg_mem (ha c) }
  have hS : ∀ e, e ∈ S ↔ ∀ c : K, c • e ∈ M₀.img V := fun e => Iff.rfl
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hle : V ≤ M₀.lift S := by
    refine sec39_Vt_le (fun z hz => ⟨hZQ hz, (hS _).mpr fun c => ?_⟩) fun m hm htm => ?_
    · rw [(M₀.π_ker z (hZQ hz)).mpr hz, smul_zero]
      exact (M₀.img V).zero_mem
    · obtain ⟨b, -, -, hB, -, -⟩ := (hc.conj_of_mem hm).dictB h
      intro x hx
      have hxQ : x ∈ Q := (hc.conj_of_mem hm).le hx
      refine ⟨hxQ, (hS _).mpr fun c => ?_⟩
      obtain ⟨s, hs⟩ := (hB _).mp (M₀.pi_mem_img hx hxQ)
      have hcx : c • M₀.π x ∈ M₀.img (conjSubgroup m B) :=
        (hB _).mpr ⟨c * s, by rw [hs, smul_smul]⟩
      exact M₀.img_mono (sec39_conjB_le_Vt hm htm) hcx
  obtain ⟨x, hxV, -, rfl⟩ := he
  exact (hS _).mp (hle hxV).2 c

theorem Ctx.Vt_eq_Ut_of_Tt_le_Z (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (htQ : t ∉ Q) (hT0 : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Z) :
    Vt M (LB M Q B) B Z t = Ut Q Z t ∧ Wt Q (Vt M (LB M Q B) B Z t) = Q1 hc t := by
  set V := Vt M (LB M Q B) B Z t
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have htM : t ∈ M := hc.LB_le_M ht
  have htH := hc.LB_le_H0 ht
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  set τ := φ ⟨t, htH⟩
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨t, htH⟩ x hx
  have hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f := B_map_eq_of_Qf τ (hφiso _)
  have hU : ∀ x ∈ Q, x ∈ Ut Q Z t ↔
      M₀.π x ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1) := fun x hx =>
    (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z t) hx).symm.trans
      (mem_img_comm_zpowers_sup_iff M₀ h.reg τ htQ1 htQ2 hτπ _)
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVU : ∀ v ∈ M₀.img V, v ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1) := by
    refine hc.img_Vt_le_of_invariant h35 h t _ ?_ fun l hl S hS _ v hv => ?_
    · intro hbot
      apply htQ
      refine (hφQ ⟨t, htH⟩).mp (LinearEquiv.ext fun e => ?_)
      have h0 : ((τ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1) e ∈
          LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1) := ⟨e, rfl⟩
      rw [hbot, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
      exact h0
    · obtain ⟨w, rfl⟩ := hv
      have hcomm := hc.hyp.comm_action (hc.Rt_le_M t hl) htM (hc.Rt_comm_mem_Q hl) hS hτπ w
      refine ⟨S w, ?_⟩
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub]
      rw [hcomm]
  have hWF : ∀ x ∈ Wt Q V, τ (M₀.π x) = M₀.π x := by
    intro x hx
    have hxT : ⁅x, t⁆ ∈ Z := hT0 (Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t)))
    have h0 := (M₀.π_ker _ (hc.comm_mem_Q htM hx.1)).mpr hxT
    rw [pi_comm_eq_sub htQ1 hτπ hx.1, sub_eq_zero] at h0
    exact h0.symm
  let Vs : Submodule (GaloisField 2 n) M₀.E :=
    imgSub M₀ V (fun c _ he => hc.smul_mem_img_Vt h t c he)
  have hEq : Vs = LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1) := by
    refine eq_range_sub_one_of_perp (fun v hv => hVU v (mem_imgSub.mp hv)) fun e he => ?_
    obtain ⟨x, hxW, -, rfl⟩ :=
      (mem_img_Wt_iff M₀ h.reg hVQ).mpr fun v hv => he v (mem_imgSub.mpr hv)
    exact hWF x hxW
  have hVeq : ∀ e, e ∈ M₀.img V ↔
      e ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1) := fun e => by
    rw [← hEq]
    exact Iff.rfl
  have hVUt : V = Ut Q Z t := by
    ext x
    constructor
    · intro hx
      exact (hU x (hVQ hx)).mpr ((hVeq _).mp (M₀.pi_mem_img hx (hVQ hx)))
    · intro hx
      have hxQ := hc.Ut_le_Q htM hx
      exact (M₀.mem_img_iff hZV hxQ).mp ((hVeq _).mpr ((hU x hxQ).mp hx))
  have hZW : Z ≤ Wt Q V := fun z hz => ⟨hc.Z_le_Q hz,
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  refine ⟨hVUt, ?_⟩
  ext x
  rw [hc.mem_Q1_iff htM]
  constructor
  · intro hx
    exact ⟨hx.1, (comm_mem_iff_fix htQ1 hτπ hx.1).mpr (hWF x hx)⟩
  · rintro ⟨hxQ, hxt⟩
    have hfix := (comm_mem_iff_fix htQ1 hτπ hxQ).mp hxt
    refine (M₀.mem_img_iff hZW hxQ).mp ((mem_img_Wt_iff M₀ h.reg hVQ).mpr fun v hv => ?_)
    rw [Tim79.QuadModel.B_comm,
      (Tim79.QuadModel.mem_range_sub_one_iff' hτB v).mp ((hVeq v).mp hv) _ hfix, neg_zero]

theorem Ctx.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (htQ : t ∉ Q) (hV : ¬ Vt M (LB M Q B) B Z t ≤ QB B) :
    Vt M (LB M Q B) B Z t = Ut Q Z t ∧ Wt Q (Vt M (LB M Q B) B Z t) = Q1 hc t := by
  rcases hc.Tt_le_Z_or_Vt_le_Tt h35 ht with hT | hVT
  · exact hc.Vt_eq_Ut_of_Tt_le_Z h35 ht htQ hT
  · exfalso
    apply hV
    have htm : t ∈ conjSubgroup 1 (LB M Q B) := by rw [conjSubgroup_one]; exact ht
    have h1 := hc.Tt_comm_le_inf_QB ht M.one_mem htm
    rw [conjSubgroup_one] at h1
    have hTle : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Q ⊓ QB B :=
      sup_le h1 (le_inf hc.Z_le_Q hc.Z_le_QB.1)
    exact hVT.trans (hTle.trans inf_le_right)

theorem Ctx.not_Tt_le_Z_of_SLNat (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) (hsl : SLNat hc t) :
    ¬ Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Z := by
  intro hT0
  have ht := hs.mem
  have htQ := hs.notQ
  obtain ⟨hVU, -⟩ := hc.Vt_eq_Ut_of_Tt_le_Z h35 ht htQ hT0
  obtain ⟨K', _, _, hK', d, hd, φ', hrange, -, hRN, hZn, ψ, hψ⟩ := hsl
  set V := Vt M (LB M Q B) B Z t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hcardQ : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card Z ^ d := by
    rw [Nat.card_congr ψ.toEquiv,
      show Nat.card (Multiplicative (Fin d → K')) = Nat.card (Fin d → K') from rfl,
      Nat.card_fun, Nat.card_fin, hK']
  have hcardZ : Nat.card (Z.subgroupOf V) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  have hcardV : Nat.card V = Nat.card Z * Nat.card Z ^ d := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V), hcardQ, hcardZ,
      mul_comm]
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  ·
    have hd2 : d = 2 := by omega
    apply hs.noA2 t ht
    refine ⟨hc.hyp.Q_normal.2 (hc.LB_le_M ht), htQ, hc.sq_mem_Q_of_mem_LB ht, ?_, ?_⟩
    · show Nat.card (Ut Q Z t) = Nat.card Z ^ 3
      rw [← hVU, hcardV, hd2]
      ring
    · exact (hc.Vt_isElemAbelian h35 ht htQ).mono
        ((le_sup_left : ⁅Q, Subgroup.zpowers t⁆ ≤ Ut Q Z t).trans hVU.ge)
  ·
    obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
    obtain ⟨φ, hφπ, -, hφiso⟩ := exists_actionHom_H0 hc.hyp h
    have htM : t ∈ M := hc.LB_le_M ht
    have htH := hc.LB_le_H0 ht
    obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
    set τ := φ ⟨t, htH⟩
    have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨t, htH⟩ x hx
    have hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f := B_map_eq_of_Qf τ (hφiso _)
    have hU : ∀ x ∈ Q, x ∈ Ut Q Z t ↔
        M₀.π x ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n'] M₀.E) - 1) := fun x hx =>
      (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z t) hx).symm.trans
        (mem_img_comm_zpowers_sup_iff M₀ h.reg τ htQ1 htQ2 hτπ _)
    obtain ⟨ι, hιπ, hιi⟩ := exists_Vt_transport (M₀ := M₀) hVQ ψ
    have hψs : ∀ u, ∃ v : V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = u := fun u => by
      obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd u))
      exact ⟨v, by rw [hv, ψ.apply_symm_apply, toAdd_ofAdd]⟩
    have hι : ∀ u, ι u ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n'] M₀.E) - 1) := by
      intro u
      obtain ⟨v, rfl⟩ := hψs u
      rw [hιπ]
      exact (hU v (hVQ v.2)).mp (hVU.le v.2)
    have hιs : ∀ e ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n'] M₀.E) - 1),
        ∃ u, ι u = e := by
      intro e he
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      have hxV : x ∈ V := hVU.ge ((hU x hxQ).mpr he)
      exact ⟨Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨x, hxV⟩)), hιπ ⟨x, hxV⟩⟩
    obtain ⟨β, hβinv, hβne⟩ := exists_range_pairing hτB ι hι hιs hιi
    have hinv : ∀ g : GL (Fin d) K', g ∈ StatedSL d K' → ∀ x y : Fin d → K',
        β ((g : Matrix (Fin d) (Fin d) K') *ᵥ x) ((g : Matrix (Fin d) (Fin d) K') *ᵥ y) =
          β x y := by
      intro g hg x y
      rw [← hrange] at hg
      obtain ⟨r, rfl⟩ := hg
      have hrM : (r : G) ∈ M := hc.Rt_le_M t r.2
      have hrH : (r : G) ∈ H0 M Z := hc.Rt_le_H0 t r.2
      refine hβinv (fun u => (φ' r : Matrix (Fin d) (Fin d) K') *ᵥ u) (φ ⟨r, hrH⟩)
        (B_map_eq_of_Qf _ (hφiso _)) (fun e => hc.hyp.comm_action hrM htM
          (hc.Rt_comm_mem_Q r.2) (hφπ ⟨r, hrH⟩) hτπ e) (fun u => ?_) x y
      obtain ⟨v, rfl⟩ := hψs u
      have hw : (r : G) * v * (r : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hRN r.2) v).mp v.2
      rw [← hψ r v ⟨_, hw⟩ rfl, hιπ, hιπ]
      exact hφπ ⟨r, hrH⟩ v (hVQ v.2)
    have h0 := biadd_eq_zero_of_SL hd3 β hinv
    have hne : (Pi.single (⟨0, by omega⟩ : Fin d) (1 : K') : Fin d → K') ≠ 0 := by
      intro h1
      have h2 := congrFun h1 ⟨0, by omega⟩
      simp at h2
    obtain ⟨u', hu'⟩ := hβne _ hne
    exact hu' (h0 _ _)

theorem Ctx.Vt_le_Tt_of_SLNat (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) (hsl : SLNat hc t) :
    Vt M (LB M Q B) B Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t :=
  (hc.Tt_le_Z_or_Vt_le_Tt h35 hs.mem).resolve_left (hc.not_Tt_le_Z_of_SLNat hs h35 hsl)

end CFSG.RankThree.GF2n.Stroth80
