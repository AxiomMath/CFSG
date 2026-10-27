module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCentre
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndMain
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Fixed

variable {E : Type*} [AddCommGroup E] [Finite E] {X : Type*} [Group X]

theorem exists_act_fixed_ne_zero (h2 : ∀ e : E, e + e = 0) (ρ : X →* Multiplicative (AddAut E))
    {T : Subgroup X} (hT : IsPGroup 2 T) (P : AddSubgroup E)
    (hP : ∀ a ∈ T, ∀ e ∈ P, (ρ a).toAdd e ∈ P) (hne : P ≠ ⊥) :
    ∃ u ∈ P, u ≠ 0 ∧ ∀ a ∈ T, (ρ a).toAdd u = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction T P :=
    { smul := fun a e => ⟨(ρ a).toAdd e, hP a a.2 e e.2⟩
      one_smul := fun e => Subtype.ext (by
        show (ρ ((1 : T) : X)).toAdd e = e
        rw [Subgroup.coe_one, map_one]
        rfl)
      mul_smul := fun a b e => Subtype.ext (by
        show (ρ ((a * b : T) : X)).toAdd e = (ρ a).toAdd ((ρ b).toAdd e)
        rw [Subgroup.coe_mul, map_mul]
        rfl) }
  obtain ⟨u0, hu0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
  have h2u : (2 : ℕ) • (u0 : E) = 0 := by
    rw [two_nsmul]
    exact h2 _
  have hord : addOrderOf u0 = 2 := by
    refine addOrderOf_eq_prime ?_ hu0
    exact Subtype.ext h2u
  have hdvd : 2 ∣ Nat.card P := hord ▸ addOrderOf_dvd_natCard u0
  obtain ⟨b, hb, hb0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := P) hdvd
    (a := (0 : P)) (by
      rw [MulAction.mem_fixedPoints]
      intro a
      exact Subtype.ext (by
        show (ρ a).toAdd (0 : E) = 0
        exact map_zero _))
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun a ha => ?_⟩
  have := MulAction.mem_fixedPoints.mp hb ⟨a, ha⟩
  exact congrArg Subtype.val this

end Fixed

section Sylow

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem normalizes_V_of_normalizes_Z0 (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {m : G}
    (hmM : m ∈ M) (hm : m ∈ Subgroup.normalizer (Z0 : Set G)) :
    m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have htQ : t ∉ Q := hs.toSec5.notQ
  have hmt : m * t * m⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hm t).mp htZ0
  have hmtQ : m * t * m⁻¹ ∉ Q := by
    intro h
    apply htQ
    have h4 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hmM)) _).mp h
    have h3 : m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t := by group
    rwa [h3] at h4
  have h1 := hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 htQ
  have h2 := hZV G M Q Z B hc n t hs Z0 hZ0 _ hmt hmtQ
  have hconj := Ut_conj_of_normalizes (hc.conj_Q_eq hmM) (hc.conj_Z_eq hmM) t
  refine conjSubgroup_eq_self_iff.mp ?_
  calc conjSubgroup m (Vt M (LB M Q B) B Z t) = conjSubgroup m (Ut Q Z t) := by rw [h1]
    _ = Ut Q Z (m * t * m⁻¹) := hconj.symm
    _ = Vt M (LB M Q B) B Z t := h2

theorem sec7_Rt_ne_LB [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) : Rt M (LB M Q B) t ≠ LB M Q B := by
  obtain ⟨S, hS, π, hπs, hπk, hSs, h16, -⟩ := endg_quot_facts hc hs (a := Nat.card Z) rfl
  intro hR
  have hbar : bar M Q (Rt M (LB M Q B) t) = bar M Q (LB M Q B) := by rw [hR]
  have hmem : ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), (x : Mbar M Q) ∈ bar M Q (LB M Q B) :=
    fun x => Eq.mp (congrArg (fun T : Subgroup (Mbar M Q) => (x : Mbar M Q) ∈ T) hbar) x.2
  haveI : IsMulCommutative S := ⟨⟨fun a b => by
    obtain ⟨x, rfl⟩ := hπs a
    obtain ⟨y, rfl⟩ := hπs b
    rw [← map_mul, ← map_mul]
    congr 1
    have h' := hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨(x : Mbar M Q), hmem x⟩
      ⟨(y : Mbar M Q), hmem y⟩
    have h2 := congrArg Subtype.val h'
    exact Subtype.ext h2⟩⟩
  have hprime := Group.is_simple_iff_prime_card.mp hSs
  rcases Nat.Prime.eq_one_or_self_of_dvd hprime 16 h16 with h | h
  · omega
  · rw [← h] at hprime
    norm_num at hprime

theorem close71Sylow_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h311a : Stroth311aStatement) (hZV : Sec7ZVStatement) (h73a : Stroth73aStatement)
    (hQ7 : Sec7Q7Statement) : Close71SylowStatement := by
  intro G _ _ M Q Z B _ hc n t hcl Z0 hZ0
  classical
  have hs : Sec7Hyp hc n t := hcl.1
  have hno : ¬ Conc71abcd hc n t := hcl.2.1
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQc : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    hQc ρ (hc.Rt_le_M t hρ) y hy
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n
    hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  haveI : Finite M₀.E := Module.finite_of_finite K
  obtain ⟨act, hactρ, -, hsemi⟩ := endg_act_data hc hS.model ρ hS.conj
  have hsemi' : ∀ g : Mbar M Q, ∃ σ : K ≃+* K, ∀ (c : K) (e : M₀.E),
      (ρ g).toAdd (c • e) = σ c • (ρ g).toAdd e := by
    intro g
    obtain ⟨σ, hσ⟩ := hsemi g
    exact ⟨σ, fun c e => by rw [← hactρ, ← hactρ]; exact hσ c e⟩
  have h2K : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hdbl : ∀ e : M₀.E, e + e = 0 := fun e => by rw [← two_smul K e, h2K, zero_smul]
  let Nz : Subgroup (Mbar M Q) :=
    Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q))
  let S0 : Subgroup (Mbar M Q) := bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t)
  have hLp : IsPGroup 2 ↥(bar M Q (LB M Q B)) :=
    CFSG.Open.IsElemAbelian.isPGroup (Ctx.isElemAbelian_bar_LB hc)
  have hRne := sec7_Rt_ne_LB hc hs
  have hN2 : IsPGroup 2 ↥(hc.CN t) := hc.isPGroup_CN_of_311 h34 hs.toSec5
    (h311a G M Q Z B hc n hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen t ht
      hs.toSec5.notQ hRne)
  have hNp : IsPGroup 2 ↥(bar M Q (hc.CN t)) := endg_N_pgroup_bar hc ht hN2
  have hS0p : IsPGroup 2 ↥S0 :=
    hLp.to_sup_of_normal_right' hNp (hc.bar_LB_le_normalizer_CN ht)
  have hbarN : ∀ S : Subgroup G, S ≤ Rt M (LB M Q B) t → bar M Q S ≤ Nz := by
    intro S hSR x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyR : (y : G) ∈ Rt M (LB M Q B) t := hSR (Subgroup.mem_subgroupOf.mp hy)
    exact mk_mem_normalizer_bar_of_normalizer hQZ0 y (hZ0.mem_normalizer hnormQ hyR)
  have hS0N : S0 ≤ Nz := sup_le (hbarN _ (le_Rt (M := M) (LB M Q B) ht))
    (hbarN _ (fun y hy => (Ctx.mem_CN.mp hy).1))
  obtain ⟨T, ⟨hTN, hTp, hS0T⟩, hTmax⟩ : ∃ T : Subgroup (Mbar M Q),
      (T ≤ Nz ∧ IsPGroup 2 ↥T ∧ S0 ≤ T) ∧ ∀ S : Subgroup (Mbar M Q), S ≤ Nz →
        IsPGroup 2 ↥S → S0 ≤ S → T ≤ S → S = T := by
    obtain ⟨T, hT, hmin⟩ := wellFounded_gt.has_min
      {S : Subgroup (Mbar M Q) | S ≤ Nz ∧ IsPGroup 2 ↥S ∧ S0 ≤ S} ⟨S0, hS0N, hS0p, le_rfl⟩
    exact ⟨T, hT, fun S hSN hSp hS0S hTS => by
      by_contra hne
      exact hmin S ⟨hSN, hSp, hS0S⟩ (lt_of_le_of_ne hTS (Ne.symm hne))⟩
  have hLT : bar M Q (LB M Q B) ≤ T := le_sup_left.trans hS0T
  have hNT : bar M Q (hc.CN t) ≤ T := le_sup_right.trans hS0T
  have hnorm : Subgroup.normalizer (T : Set (Mbar M Q)) ≤ Nz := by
    intro gb hgb
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective gb
    have hg : (g' : G) ∈ M := g'.2
    have hTV : ∀ a ∈ T, ∀ e ∈ M₀.img (Vt M (LB M Q B) B Z t),
        (ρ a).toAdd e ∈ M₀.img (Vt M (LB M Q B) B Z t) := by
      intro a ha e he
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
      have hyZ0 : (y : G) ∈ Subgroup.normalizer (Z0 : Set G) :=
        mem_normalizer_of_mk_mem_normalizer_bar hQZ0 hZ0M y (hTN ha)
      have hyV := normalizes_V_of_normalizes_Z0 hZV hc hs hZ0 y.2 hyZ0
      obtain ⟨v, hvV, hvQ, rfl⟩ := he
      rw [← hS.conj y v hvQ]
      exact M₀.pi_mem_img ((Subgroup.mem_normalizer_iff.mp hyV v).mp hvV)
        (hQc y y.2 v hvQ)
    let A : M₀.E ≃+ M₀.E := (ρ (QuotientGroup.mk g')).toAdd
    let Vg : AddSubgroup M₀.E := (M₀.img (Vt M (LB M Q B) B Z t)).map A.toAddMonoidHom
    have hVgmem : ∀ e, e ∈ Vg ↔ ∃ e₀ ∈ M₀.img (Vt M (LB M Q B) B Z t), A e₀ = e := fun e =>
      AddSubgroup.mem_map
    have hconjT : ∀ a ∈ T, (QuotientGroup.mk g' : Mbar M Q)⁻¹ * a * QuotientGroup.mk g' ∈ T := by
      intro a ha
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgb) a).mp ha
      simpa using this
    have hTVg : ∀ a ∈ T, ∀ e ∈ Vg, (ρ a).toAdd e ∈ Vg := by
      intro a ha e he
      obtain ⟨e₀, he₀, rfl⟩ := (hVgmem e).mp he
      refine (hVgmem _).mpr ⟨(ρ ((QuotientGroup.mk g' : Mbar M Q)⁻¹ * a *
        QuotientGroup.mk g')).toAdd e₀, hTV _ (hconjT a ha) e₀ he₀, ?_⟩
      show (ρ (QuotientGroup.mk g')).toAdd ((ρ ((QuotientGroup.mk g' : Mbar M Q)⁻¹ * a *
        QuotientGroup.mk g')).toAdd e₀) = (ρ a).toAdd ((ρ (QuotientGroup.mk g')).toAdd e₀)
      rw [← act_mul_apply, ← act_mul_apply]
      congr 2
      group
    have hbV : b ∈ M₀.img (Vt M (LB M Q B) B Z t) := M₀.img_mono (hc.B_le_Vt ht) hS.b_img
    have hVgne : Vg ≠ ⊥ := by
      intro hbot
      have hAb : A b ∈ Vg := (hVgmem _).mpr ⟨b, hbV, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at hAb
      exact hS.b_ne (A.injective (hAb.trans (map_zero A).symm))
    obtain ⟨u, huV, hu0, hufix⟩ := exists_act_fixed_ne_zero hdbl ρ hTp Vg hTVg hVgne
    have huspan : u ∈ Submodule.span K {b} := (hS.fix u).mp fun ℓ hℓ => hufix ℓ (hLT hℓ)
    obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp huspan
    have hu'fix : ∀ ℓ ∈ bar M Q (LB M Q B),
        (ρ ℓ).toAdd ((ρ (QuotientGroup.mk g' : Mbar M Q)⁻¹).toAdd u) =
          (ρ (QuotientGroup.mk g' : Mbar M Q)⁻¹).toAdd u := by
      intro ℓ hℓ
      have hgl : (QuotientGroup.mk g' : Mbar M Q) * ℓ * (QuotientGroup.mk g' : Mbar M Q)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp hgb ℓ).mp (hLT hℓ)
      have e1 : ℓ * (QuotientGroup.mk g' : Mbar M Q)⁻¹ = (QuotientGroup.mk g' : Mbar M Q)⁻¹ *
          ((QuotientGroup.mk g' : Mbar M Q) * ℓ * (QuotientGroup.mk g' : Mbar M Q)⁻¹) := by group
      rw [← act_mul_apply, e1, act_mul_apply, hufix _ hgl]
    have hu'span : (ρ (QuotientGroup.mk g' : Mbar M Q)⁻¹).toAdd u ∈ Submodule.span K {b} :=
      (hS.fix _).mp hu'fix
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hu'span
    obtain ⟨σ, hσ⟩ := hsemi' (QuotientGroup.mk g')
    have hAu : A ((ρ (QuotientGroup.mk g' : Mbar M Q)⁻¹).toAdd u) = u := by
      show (ρ (QuotientGroup.mk g')).toAdd ((ρ (QuotientGroup.mk g' : Mbar M Q)⁻¹).toAdd u) = u
      rw [← act_mul_apply, mul_inv_cancel, map_one]
      rfl
    have hAcb : σ c' • A b = c₁ • b := by
      have := hAu
      rw [← hc'] at this
      have h3 : A (c' • b) = σ c' • A b := hσ c' b
      rw [h3] at this
      rw [this, hc₁]
    have hσc' : σ c' ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hAcb
      apply hu0
      rw [← hc₁, ← hAcb]
    have hAb : (ρ (QuotientGroup.mk g')).toAdd b = ((σ c')⁻¹ * c₁) • b := by
      have h4 : A b = (σ c')⁻¹ • (σ c' • A b) := by
        rw [smul_smul, inv_mul_cancel₀ hσc', one_smul]
      rw [show (ρ (QuotientGroup.mk g')).toAdd b = A b from rfl, h4, hAcb, smul_smul]
    have hgN : (QuotientGroup.mk g' : Mbar M Q) ∈
        Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := hS.stab _ ⟨_, hAb⟩
    have hgNL : (g' : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      mem_normalizer_of_mk_mem_normalizer_bar hQL hc.LB_le_M g' hgN
    have hxL : (g' : G) * t * (g' : G)⁻¹ ∈ LB M Q B :=
      (Subgroup.mem_normalizer_iff.mp hgNL t).mp ht
    have hxCN := stroth72_conj_mem_CN hc hs hno hZ0 hg hxL
    have hVU : Vt M (LB M Q B) B Z t = Ut Q Z t :=
      (h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)).1
    have hVW : conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
      conj_Vt_le_Wt hc ht hVU hg (Ctx.mem_CN.mp hxCN).2
    have hZc : Z ≤ conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t) := by
      have h : conjSubgroup (g' : G) Z ≤ conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t) :=
        Subgroup.map_mono (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t))
      rwa [hc.conj_Z_eq hg] at h
    have hNn : ∀ k ∈ hc.CN t, k ∈ Subgroup.normalizer
        (conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t) : Set G) := by
      intro k hk
      have hkM : k ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hk).1
      have hkT : (QuotientGroup.mk (⟨k, hkM⟩ : ↥M) : Mbar M Q) ∈ T :=
        hNT ((mk_mem_bar_iff_sec4 (hc.Q_le_CN' ht) ⟨k, hkM⟩).mpr hk)
      refine Subgroup.mem_normalizer_fintype fun x' hx' => ?_
      have hx'' : x' ∈ conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t) := hx'
      have hv₀ : (g' : G)⁻¹ * x' * g' ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hx''
      have hvQ : (g' : G)⁻¹ * x' * g' ∈ Q := hc.Vt_le_Q t hv₀
      have hx'Q : x' ∈ Q := by
        have := hQc g' hg _ hvQ
        simpa [mul_assoc] using this
      have hπx' : M₀.π x' ∈ Vg := by
        refine (hVgmem _).mpr ⟨M₀.π ((g' : G)⁻¹ * x' * g'), M₀.pi_mem_img hv₀ hvQ, ?_⟩
        have e : M₀.π ((g' : G) * ((g' : G)⁻¹ * x' * g') * (g' : G)⁻¹) =
            (ρ (QuotientGroup.mk g')).toAdd (M₀.π ((g' : G)⁻¹ * x' * g')) :=
          hS.conj g' _ hvQ
        have e2 : (g' : G) * ((g' : G)⁻¹ * x' * g') * (g' : G)⁻¹ = x' := by group
        rw [e2] at e
        exact e.symm
      have hk' : M₀.π (k * x' * k⁻¹) ∈ Vg := by
        have e : M₀.π (k * x' * k⁻¹) = (ρ (QuotientGroup.mk (⟨k, hkM⟩ : ↥M))).toAdd (M₀.π x') :=
          hS.conj ⟨k, hkM⟩ x' hx'Q
        rw [e]
        exact hTVg _ hkT _ hπx'
      obtain ⟨e₀, he₀, hAe₀⟩ := (hVgmem _).mp hk'
      obtain ⟨v₀, hv₀V, hv₀Q, rfl⟩ := he₀
      have hgv : (g' : G) * v₀ * (g' : G)⁻¹ ∈ conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t) := by
        rw [mem_conjSubgroup]
        have e : (g' : G)⁻¹ * ((g' : G) * v₀ * (g' : G)⁻¹) * g' = v₀ := by group
        rw [e]
        exact hv₀V
      have hgvQ : (g' : G) * v₀ * (g' : G)⁻¹ ∈ Q := hQc g' hg v₀ hv₀Q
      have himg : M₀.π (k * x' * k⁻¹) ∈
          M₀.img (conjSubgroup (g' : G) (Vt M (LB M Q B) B Z t)) := by
        have e : M₀.π (k * x' * k⁻¹) = M₀.π ((g' : G) * v₀ * (g' : G)⁻¹) := by
          rw [← hAe₀]
          exact (hS.conj g' v₀ hv₀Q).symm
        rw [e]
        exact M₀.pi_mem_img hgv hgvQ
      exact (M₀.mem_img_iff hZc (hQc k hkM x' hx'Q)).mp himg
    have hVeq := hQ7 G M Q Z B hc n t hs (g' : G) hg hgNL hVW hNn
    have hgZ0 := h73a G M Q Z B hc n t hs hno Z0 hZ0 (g' : G) hg
      (conjSubgroup_eq_self_iff.mp hVeq)
    exact mk_mem_normalizer_bar_of_normalizer hQZ0 g' hgZ0
  have hmax : ∀ S : Subgroup (Mbar M Q), S ≤ Nz → IsPGroup 2 ↥S → T ≤ S → S ≤ T :=
    fun S hSN hSp hTS => (hTmax S hSN hSp (hS0T.trans hTS) hTS).le
  obtain ⟨P, hP⟩ := exists_sylow_two_of_normalizer_le hTp hTN hmax hnorm
  exact ⟨P, hP ▸ hTN⟩

end Sylow

end CFSG.RankThree.GF2n.Stroth80
