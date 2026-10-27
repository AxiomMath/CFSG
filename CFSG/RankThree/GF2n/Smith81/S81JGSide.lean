module

public import CFSG.RankThree.GF2n.Smith81.S81JLemmaJ
public import CFSG.RankThree.GF2n.Smith81.S81JGLift
public import CFSG.RankThree.GF2n.Smith81.S81BPos3
public import CFSG.RankThree.GF2n.Smith81.S81BTacitFree
public import CFSG.RankThree.GF2n.Smith81.S81BPos
public import CFSG.RankThree.GF2n.Smith81.S81JAct
public import CFSG.RankThree.GF2n.Smith81.Sec2Consequences

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.S81J Module

open scoped commutatorElement

section Basic

theorem charP_two_of_card_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (h : Nat.card K = 2 ^ n) : CharP K 2 := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hcp, m, hpp, hm⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, h] at hm
  have hdvd : p ∣ 2 ^ n := by
    rw [hm]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hpeq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd)
  subst hpeq
  exact hcp

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem finrank_E_eq_twenty (hg : GlobalModelData M Q Z γ M₀) (hZQ : Z ≤ Q)
    (hQ : Nat.card Q = Nat.card Z ^ 21) : finrank K M₀.E = 20 := by
  have himgQ : M₀.img Q = ⊤ := by
    refine le_antisymm le_top ?_
    intro e _
    obtain ⟨y, hyQ, hπ⟩ := M₀.π_surj e
    exact ⟨y, hyQ, hyQ, hπ⟩
  have hQE : Nat.card Q = Nat.card Z * Nat.card M₀.E := by
    have h := Tim79.QuadModel.card_eq M₀ (S := Q) le_rfl hZQ
    rwa [himgQ, AddSubgroup.card_top] at h
  have hE : Nat.card M₀.E = Nat.card Z ^ finrank K M₀.E := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := M₀.E), hg.card]
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have hZ2 : 2 ≤ Nat.card Z := by
    rw [← hg.card]
    omega
  have key : Nat.card Z ^ 21 = Nat.card Z ^ (finrank K M₀.E + 1) := by
    rw [← hQ, hQE, hE]
    ring
  have h21 : 21 = finrank K M₀.E + 1 := Nat.pow_right_injective hZ2 key
  omega

end Basic

section Action

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_T_Lgen (hctx : Ctx M Q Z B) (hg : GlobalModelData M Q Z γ M₀) :
    ∃ T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E),
      (∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
        M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x)) ∧
      ∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q := by
  obtain ⟨φ, h1, h2, -⟩ := exists_actionHom_H0 hctx.hyp hg
  have hle := Lgen_le_H0 hctx
  exact ⟨φ.comp (Subgroup.inclusion hle), fun s x hx => h1 ⟨(s : G), hle s.2⟩ x hx,
    fun s => h2 ⟨(s : G), hle s.2⟩⟩

theorem Lgen_le_normalizer_Q (hctx : Ctx M Q Z B) :
    Lgen M (LB M Q B) ≤ Subgroup.normalizer (Q : Set G) := by
  exact (Lgen_le hctx.LB_le_M).trans hctx.hyp.Q_normal.2

theorem exists_SLAct {Lg : Subgroup G} [(Q.subgroupOf Lg).Normal]
    (T : Lg →* (M₀.E ≃ₗ[K] M₀.E)) (hQ : ∀ s : Lg, (s : G) ∈ Q → T s = 1)
    (Θ : ↥(StatedSL 6 K) →* (↥Lg ⧸ Q.subgroupOf Lg)) (hΘ : Function.Surjective Θ) :
    ∃ A : SLAct K M₀.E,
      (∀ (h : ↥(StatedSL 6 K)) (s : Lg), Θ h = QuotientGroup.mk s → ∀ v, A.act h v = T s v) ∧
      (∀ s : Lg, ∃ h : GL (Fin 6) K, (h : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
        ∀ v, T s v = A.act h v) ∧
      (∀ h : GL (Fin 6) K, (h : Matrix (Fin 6) (Fin 6) K).det = 1 →
        ∃ s : Lg, ∀ v, T s v = A.act h v) := by
  classical
  obtain ⟨Tbar, hTbar⟩ : ∃ Tbar : (↥Lg ⧸ Q.subgroupOf Lg) →* (M₀.E ≃ₗ[K] M₀.E),
      ∀ s : Lg, Tbar (QuotientGroup.mk s) = T s :=
    ⟨QuotientGroup.lift (Q.subgroupOf Lg) T
      (fun s hs => MonoidHom.mem_ker.mpr (hQ s (Subgroup.mem_subgroupOf.mp hs))), fun s => rfl⟩
  obtain ⟨act, hact⟩ : ∃ act : GL (Fin 6) K → (M₀.E →ₗ[K] M₀.E),
      ∀ (g : GL (Fin 6) K) (hg : g ∈ StatedSL 6 K),
        act g = (Tbar (Θ ⟨g, hg⟩)).toLinearMap :=
    ⟨fun g => if hg : g ∈ StatedSL 6 K then (Tbar (Θ ⟨g, hg⟩)).toLinearMap else 1,
      fun g hg => dif_pos hg⟩
  have act_one : act 1 = 1 := by
    rw [hact 1 (one_mem _)]
    show (Tbar (Θ 1)).toLinearMap = 1
    rw [map_one, map_one]
    rfl
  have act_mul : ∀ g h : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      (h : Matrix (Fin 6) (Fin 6) K).det = 1 → act (g * h) = act g * act h := by
    intro g h hg hh
    have hg' : g ∈ StatedSL 6 K := CFSG.Open.StatedAPI.mem_statedSL_of_det hg
    have hh' : h ∈ StatedSL 6 K := CFSG.Open.StatedAPI.mem_statedSL_of_det hh
    have hgh' : g * h ∈ StatedSL 6 K := mul_mem hg' hh'
    rw [hact (g * h) hgh', hact g hg', hact h hh']
    have e : (⟨g * h, hgh'⟩ : ↥(StatedSL 6 K)) = ⟨g, hg'⟩ * ⟨h, hh'⟩ := rfl
    rw [e, map_mul, map_mul]
    rfl
  have key : ∀ (h : ↥(StatedSL 6 K)) (s : Lg), Θ h = QuotientGroup.mk s →
      ∀ v, act h v = T s v := by
    intro h s hs v
    have e1 : act (h : GL (Fin 6) K) = (Tbar (Θ h)).toLinearMap := hact h h.2
    have e2 : Tbar (Θ h) = T s := by rw [hs, hTbar s]
    rw [e1, e2]
    rfl
  refine ⟨⟨act, act_one, act_mul⟩, key, ?_, ?_⟩
  · intro s
    obtain ⟨h, hh⟩ := hΘ (QuotientGroup.mk s)
    exact ⟨(h : GL (Fin 6) K), CFSG.Open.StatedAPI.det_of_mem_statedSL h.2,
      fun v => (key h s hh v).symm⟩
  · intro g hg
    have hgS : g ∈ StatedSL 6 K := CFSG.Open.StatedAPI.mem_statedSL_of_det hg
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Θ ⟨g, hgS⟩)
    have e : Tbar (Θ ⟨g, hgS⟩) = T s := by rw [← hs, hTbar s]
    refine ⟨s, fun v => ?_⟩
    show T s v = act g v
    rw [hact g hgS, e]
    rfl

theorem gsC_mk_mul_comm {Q Lg C : Subgroup G} [(Q.subgroupOf Lg).Normal]
    (hC : ⁅C, C⁆ ≤ Q) {s t : Lg} (hs : (s : G) ∈ C) (ht : (t : G) ∈ C) :
    (QuotientGroup.mk s : ↥Lg ⧸ Q.subgroupOf Lg) * QuotientGroup.mk t =
      QuotientGroup.mk t * QuotientGroup.mk s := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hcm : ⁅(t : G)⁻¹, (s : G)⁻¹⁆ ∈ Q :=
    hC (Subgroup.commutator_mem_commutator (C.inv_mem ht) (C.inv_mem hs))
  have e : (((s * t)⁻¹ * (t * s) : Lg) : G) = ⁅(t : G)⁻¹, (s : G)⁻¹⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact hcm

theorem gsC_mk_mul_self_eq_one {Q Lg C : Subgroup G} [(Q.subgroupOf Lg).Normal]
    (hC : ∀ a ∈ C, a ^ 2 ∈ Q) {s : Lg} (hs : (s : G) ∈ C) :
    (QuotientGroup.mk s : ↥Lg ⧸ Q.subgroupOf Lg) * QuotientGroup.mk s = 1 := by
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_mul, ← pow_two]
  exact hC _ hs

theorem bar_props {A' : Subgroup G} {Lg : Subgroup G} [(Q.subgroupOf Lg).Normal]
    (hctx : Ctx M Q Z A') (hQL : Q ≤ Lg) (hLB : LB M Q A' ≤ Lg) {n : ℕ}
    (hcard : Nat.card ↥(LB M Q A') = Nat.card Q * Nat.card Z ^ n) :
    (∀ x ∈ bar Lg Q (LB M Q A'), ∀ y ∈ bar Lg Q (LB M Q A'), x * y = y * x) ∧
      (∀ x ∈ bar Lg Q (LB M Q A'), x * x = 1) ∧
      Nat.card ↥(bar Lg Q (LB M Q A')) = Nat.card Z ^ n := by
  have hmem : ∀ x ∈ bar Lg Q (LB M Q A'), ∃ s : Lg, (s : G) ∈ LB M Q A' ∧
      x = (QuotientGroup.mk s : ↥Lg ⧸ Q.subgroupOf Lg) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨s, Subgroup.mem_subgroupOf.mp hs, rfl⟩
  have hf : ∀ s : Lg, QuotientGroup.mk' (Q.subgroupOf Lg) s = 1 ↔ (s : G) ∈ Q := by
    intro s
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQS : Q ≤ LB M Q A' := le_sup_left
  have key :=
    card_eq_card_mul_card_map_of_ker (QuotientGroup.mk' (Q.subgroupOf Lg)) hf hQL hQS hLB
  have hpos : 0 < Nat.card Q := Nat.card_pos
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := hmem x hx
    obtain ⟨t, ht, rfl⟩ := hmem y hy
    exact gsC_mk_mul_comm hctx.commutator_LB_le_Q hs ht
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := hmem x hx
    exact gsC_mk_mul_self_eq_one (fun a ha => hctx.sq_mem_Q_of_mem_LB ha) hs
  · refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← hcard]
    exact key.symm

theorem exists_W_of_bar {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type} [Group X]
    (Θ : ↥(StatedSL 6 K) →* X) (hΘ : Function.Surjective Θ) (hk3 : ∀ n ∈ Θ.ker, n ^ 3 = 1)
    (hkc : ∀ n ∈ Θ.ker, ∀ x : ↥(StatedSL 6 K), n * x = x * n) (Eb : Subgroup X)
    (hc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x) (hs : ∀ x ∈ Eb, x * x = 1)
    (hcard : Nat.card Eb = Nat.card K ^ 9) :
    ∃ (W : Submodule K (Fin 6 → K)) (E : Subgroup ↥(StatedSL 6 K)), finrank K W = 3 ∧
      E.map Θ = Eb ∧
      ∀ u : GL (Fin 6) K, u ∈ UnipGL K W ↔ ∃ h ∈ E, (h : GL (Fin 6) K) = u := by
  obtain ⟨E, hinv, hcomm, hmap, hcardE⟩ := exists_lift_involutions Θ hΘ hk3 hkc Eb hc hs
  obtain ⟨EG, hEG⟩ : ∃ EG : Subgroup (GL (Fin 6) K), EG = E.map (StatedSL 6 K).subtype :=
    ⟨_, rfl⟩
  have hmemEG : ∀ x : GL (Fin 6) K, x ∈ EG ↔ ∃ h ∈ E, (h : GL (Fin 6) K) = x := by
    intro x
    rw [hEG]
    exact Subgroup.mem_map
  have hcommEG : ∀ x ∈ EG, ∀ y ∈ EG, x * y = y * x := by
    intro x hx y hy
    obtain ⟨h, hh, rfl⟩ := (hmemEG x).1 hx
    obtain ⟨h', hh', rfl⟩ := (hmemEG y).1 hy
    exact congrArg Subtype.val (hcomm h hh h' hh')
  have hsqEG : ∀ x ∈ EG, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := (hmemEG x).1 hx
    rw [pow_two]
    exact congrArg Subtype.val (hinv h hh)
  have hEA : CFSG.Open.IsElemAbelian 2 EG :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommEG (a : GL (Fin 6) K) a.2 (b : GL (Fin 6) K) b.2)⟩⟩,
      fun x hx => hsqEG x hx⟩
  have hcardEG : Nat.card EG = Nat.card E := by
    rw [hEG]
    exact Subgroup.card_map_of_injective (StatedSL 6 K).subtype_injective
  have hcard9 : Nat.card K ^ 9 ≤ Nat.card EG :=
    le_of_eq (by rw [hcardEG, hcardE, hcard])
  obtain ⟨W, hW3, hWU⟩ := CFSG.LinearAlgebra.S81JSchur.lemmaJ hEA hcard9
  refine ⟨W, E, hW3, hmap, fun u => ?_⟩
  rw [← hWU]
  exact hmemEG u

theorem fixed_iff_mem_img {A' S : Subgroup G} {Lg : Subgroup G} (hctx : Ctx M Q Z A')
    (hSM : S ≤ M) (hM : M ≤ Subgroup.normalizer (Q : Set G)) (hZQ : Z ≤ Q) (hLB : S = LB M Q A')
    (hCQt : CQt Q Z S = ((A' ⊔ Z : Subgroup G) : Set G)) (hA'Q : A' ≤ Q)
    (T : Lg →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lg) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hSL : S ≤ Lg) (v : M₀.E) :
    (∀ s : Lg, (s : G) ∈ S → T s v = v) ↔ ∃ x ∈ A', M₀.π x = v := by
  open scoped commutatorElement in
  constructor
  · intro hfix
    obtain ⟨x, hxQ, hπx⟩ := M₀.π_surj v
    have hxS : x ∈ CQt Q Z S := by
      show x ∈ Q ∧ ∀ t ∈ S, ⁅t, x⁆ ∈ Z
      refine ⟨hxQ, fun t ht => ?_⟩
      obtain ⟨s, hs⟩ : ∃ s : Lg, (s : G) = t := ⟨⟨t, hSL ht⟩, rfl⟩
      have hTs : T s v = v := hfix s (by rw [hs]; exact ht)
      have hconj : M₀.π ((s : G) * x * (s : G)⁻¹) = M₀.π x := by
        rw [hTe s x hxQ, hπx, hTs]
      rw [hs] at hconj
      have htxQ : t * x * t⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hM (hSM ht)) x).mp hxQ
      have hcomm : ⁅t, x⁆ = t * x * t⁻¹ * x⁻¹ := commutatorElement_def t x
      have hcQ : ⁅t, x⁆ ∈ Q := by
        rw [hcomm]; exact Q.mul_mem htxQ (Q.inv_mem hxQ)
      have hπc : M₀.π ⁅t, x⁆ = 0 := by
        rw [hcomm, M₀.π_mul _ htxQ x⁻¹ (Q.inv_mem hxQ), quadModel_pi_inv M₀ hxQ, hconj,
          add_neg_cancel]
      exact (M₀.π_ker _ hcQ).mp hπc
    have hxAZ : x ∈ ((A' ⊔ Z : Subgroup G) : Set G) := by
      rw [← hCQt]; exact hxS
    have hmem : (fun a : G => (LinearEquiv.refl K M₀.E) (M₀.π a)) x ∈
        (fun a : G => (LinearEquiv.refl K M₀.E) (M₀.π a)) '' ((A' ⊔ Z : Subgroup G) : Set G) :=
      Set.mem_image_of_mem _ hxAZ
    rw [psi_image_sup_Z (LinearEquiv.refl K M₀.E) hA'Q hZQ] at hmem
    obtain ⟨a, haA', hae⟩ := hmem
    simp only [LinearEquiv.refl_apply] at hae
    exact ⟨a, haA', hae.trans hπx⟩
  · rintro ⟨a, haA', hav⟩ s hs
    subst hav
    have haQ : a ∈ Q := hA'Q haA'
    have haC : a ∈ CQt Q Z S := by
      rw [hCQt]; exact SetLike.mem_coe.mpr (Subgroup.mem_sup_left haA')
    have haC' : a ∈ Q ∧ ∀ t ∈ S, ⁅t, a⁆ ∈ Z := haC
    have hcZ : ⁅(s : G), a⁆ ∈ Z := haC'.2 (s : G) hs
    have hcQ : ⁅(s : G), a⁆ ∈ Q := hZQ hcZ
    have hsa : (s : G) * a * (s : G)⁻¹ = ⁅(s : G), a⁆ * a := by
      rw [commutatorElement_def]; group
    have hpi : M₀.π ((s : G) * a * (s : G)⁻¹) = M₀.π a := by
      rw [hsa, M₀.π_mul _ hcQ a haQ, (M₀.π_ker _ hcQ).mpr hcZ, zero_add]
    rw [← hTe s a haQ]
    exact hpi

theorem LB_le_Lgen_of_point_E3L (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h3L : InCaseE3L M Q Z B)
    {C : Subgroup G} (hC : Ctx M Q Z C) : LB M Q C ≤ Lgen M (LB M Q B) := by
  obtain ⟨n, k, hw, hnk⟩ := hc.e.exists_width
  have hn : 3 ≤ n := by
    have := hnk.ten_le
    omega
  have hTac : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B' :=
    eTacitE3L_of_genByB hGen G M Q Z B IH hc h3L
  have hno : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') :=
    fun B' hB' => (hTac B' hB').1
  have h15c : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G) := fun B' hB' =>
    (stroth_3_5 h34 hB' hw (by omega) (hTac B' hB').1 (hTac B' hB').2).2.1
  have h25 := smith25_of_117 smith117Statement_holds hc.ctx hw hn hno h15c
  have hmem : C ⊔ Z ∈ {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧
      V = A ⊔ Z} := ⟨C, hC.conj, hC.le, hC.ne, rfl⟩
  rw [h25] at hmem
  obtain ⟨g, hg, hCg⟩ := hmem
  have hcg : Ctx M Q Z (conjSubgroup g B) := hc.ctx.conj_of_mem hg
  have hle : conjSubgroup g B ≤ Z ⊔ C := by
    rw [sup_comm, hCg]
    exact le_sup_left
  obtain ⟨p, hpQ, hp⟩ := hC.exists_conj_of_le_ZB hcg hle
  have hpM : p ∈ M := hc.ctx.hyp.Q_normal.1 hpQ
  have hCeq : C = conjSubgroup (p⁻¹ * g) B := by
    rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hm : p⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hpM) hg
  rw [hCeq, hc.ctx.LB_conj hm]
  exact le_iSup₂_of_le (p⁻¹ * g) hm le_rfl

theorem points_span (H : StrothHyp M Q Z) (M₀ : Tim79.QuadModel Q Z K γ) (v : M₀.E) :
    v ∈ ⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
      Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G)) := by
  set S : Submodule K M₀.E := ⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
    Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G)) with hS
  have hπ1 : M₀.π 1 = 0 := (M₀.π_ker 1 Q.one_mem).mpr Z.one_mem
  let T : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ M₀.π x ∈ S}
      mul_mem' := fun {x y} hx hy => ⟨Q.mul_mem hx.1 hy.1, by
        rw [M₀.π_mul x hx.1 y hy.1]
        exact S.add_mem hx.2 hy.2⟩
      one_mem' := ⟨Q.one_mem, by rw [hπ1]; exact S.zero_mem⟩
      inv_mem' := fun {x} hx => ⟨Q.inv_mem hx.1, by
        have h := M₀.π_mul x hx.1 x⁻¹ (Q.inv_mem hx.1)
        rw [mul_inv_cancel, hπ1] at h
        have h' : M₀.π x⁻¹ = -M₀.π x := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h.symm
        rw [h']
        exact S.neg_mem hx.2⟩ }
  have hT : Q ≤ T := by
    refine H.gen.le.trans (iSup_le fun g => iSup_le fun hg => ?_)
    intro x hx
    have hxQ : x ∈ Q := hg hx
    show x ∈ Q ∧ M₀.π x ∈ S
    refine ⟨hxQ, ?_⟩
    by_cases hgZ : conjSubgroup g Z = Z
    · have hxZ : x ∈ Z := by rwa [hgZ] at hx
      rw [(M₀.π_ker x hxQ).mpr hxZ]
      exact S.zero_mem
    · rw [hS]
      exact Submodule.mem_iSup_of_mem
        (⟨conjSubgroup g Z, ⟨g, rfl⟩, hg, hgZ⟩ :
          {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z})
        (Submodule.subset_span (Set.mem_image_of_mem (fun x : G => M₀.π x)
          (SetLike.mem_coe.mpr hx)))
  obtain ⟨x, hxQ, hx⟩ := M₀.π_surj v
  have h2 : x ∈ Q ∧ M₀.π x ∈ S := hT hxQ
  rw [hx] at h2
  exact h2.2

end Action

end CFSG.RankThree.GF2n.Smith81
