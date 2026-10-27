module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Pts
public import CFSG.RankThree.GF2n.Stroth80.Sec52aProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem centLam_of_points (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)}
    {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    {u : ι → K} (hQu : Q' u = 0) (hu0 : u ≠ 0)
    (hW : ∀ x : ι → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
      (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ polar Q' u x = 0)
    (hL : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vt M (LB M Q B) B Z t := by
  classical
  have h35 := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ := hc.Vt_le_Q t
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hZW0 : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB B := le_inf hZV hZQB
  have hW0le : Vt M (LB M Q B) B Z t ⊓ QB B ≤ Q ⊓ QB B := inf_le_inf_right _ hVQ
  have hW0el : IsElemAbelian 2 (Vt M (LB M Q B) B Z t ⊓ QB B) :=
    isElemAbelian_two_of_le hW0le hc.inf_QB_elemAbelian
  obtain ⟨A, hAW, -, hAZ, hAsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
    Nat.prime_two hW0el hZW0 (bot_le : (⊥ : Subgroup G) ≤ _) (inf_bot_eq Z)
  have hd3 : 3 ≤ Fintype.card ι := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K)]; exact h3
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hW0card : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
      Nat.card Z * Nat.card K ^ (Fintype.card ι - 1) := by
    have h1 := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left {x | polar Q' u x = 0}
      (fun x => hW x)
    rw [h1]
    congr 1
    exact card_polar_perp Q' hQ hu0
  have hAcard : Nat.card ↥A = Nat.card K ^ (Fintype.card ι - 1) := by
    have h2 := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hW0el hZW0 hAW hAZ hAsup
    rw [hW0card] at h2
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hcim := card_inf_mul_card_map hLR φ hker
  rw [hL, E.card_LomGL hQ hQu hu0, Module.finrank_fintype_fun_eq_card, h35.2.2.1, hK] at hcim
  have hE2 := hc.card_LB_inf_CN_mul hs
  rw [h35.2.2.2] at hE2
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hqpos : 0 < Nat.card Z := by omega
  have key : Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2) =
      Nat.card Z ^ (2 * n) := by
    apply Nat.eq_of_mul_eq_mul_left hQpos
    calc Nat.card Q * (Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2))
        = (Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Q) * Nat.card Z ^ (Fintype.card ι - 2) :=
          by ring
      _ = (Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (n + 1)) *
            Nat.card Z ^ (Fintype.card ι - 2) := by rw [hE2]
      _ = (Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2)) *
            Nat.card Z ^ (n + 1) := by ring
      _ = (Nat.card Q * Nat.card Z ^ (n - 1)) * Nat.card Z ^ (n + 1) := by rw [hcim]
      _ = Nat.card Q * Nat.card Z ^ (2 * n) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          have := hs.n_gt
          omega
  have hcard : Nat.card Z ^ n * Nat.card ↥(((QB B ⊓ M) ⊓ hc.CN t) ⊓ Q) ≤
      Nat.card ↥A * Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) := by
    rw [hc.inf_CN_inf_Q hs, h35.2.2.2, hAcard, hK]
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hqpos (Fintype.card ι - 2))
    refine le_of_eq ?_
    calc Nat.card Z ^ n * Nat.card Z ^ (n + 1) * Nat.card Z ^ (Fintype.card ι - 2)
        = Nat.card Z ^ (Fintype.card ι - 1) * Nat.card Z ^ (2 * n) := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1
          omega
      _ = Nat.card Z ^ (Fintype.card ι - 1) *
            (Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) * Nat.card Z ^ (Fintype.card ι - 2)) := by
          rw [key]
      _ = Nat.card Z ^ (Fintype.card ι - 1) * Nat.card ↥((QB B ⊓ M) ⊓ hc.CN t) *
            Nat.card Z ^ (Fintype.card ι - 2) := by ring
  have hAD : A ≤ Q ⊓ QB B := hAW.trans hW0le
  have hcomm : ∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ∀ a ∈ A, ⁅l, a⁆ = 1 := by
    intro l hl a ha
    have haW := hAW ha
    have hZc : ⁅l, a⁆ ∈ Z := (Ctx.mem_CN.mp hl.2).2 a haW.1
    have hBc : ⁅l, a⁆ ∈ B := hc.comm_QB_le_B hl.1.1 haW.2
    have hmem : ⁅l, a⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hZc, hBc⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  intro d hd hdz
  have hd' := Ctx.pairing_count h34 hc hs (inf_le_left : (QB B ⊓ M) ⊓ hc.CN t ≤ QB B ⊓ M) hAD
    (by rw [inf_comm]; exact hAZ) hcomm hcard d hd hdz
  rw [sup_comm, hAsup] at hd'
  exact hd'.1

theorem B_inf_QB_conj_eq_bot91 (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    B ⊓ QB (conjSubgroup r B) = ⊥ := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  obtain ⟨g, hg⟩ := hc.conj
  have hCQ : conjSubgroup r B ≤ QB B :=
    hc.hyp.le_QB_of_mem_QB (X := conjSubgroup r B) (Y := B)
      ⟨r * g, by rw [hg, conjSubgroup_mul]⟩ ⟨g, hg⟩ hb.1 hb1 hb.2
  obtain ⟨ĉ, hĉQ, hĉC, b', hb'B, hb'ne⟩ := hplane
  have hvV : ⁅ĉ, t⁆ ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs.mem hr) hĉC
  have hvQB : ⁅ĉ, t⁆ ∈ QB B := (sup_le hCQ hc.Z_le_QB.1) hĉC
  have hperp := (stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnot ⁅ĉ, t⁆ hvV).mp hvQB
    b' hb'B ĉ hĉQ (by rw [show ⁅ĉ, t⁆ * ⁅ĉ, t⁆⁻¹ = 1 by group]; exact Z.one_mem)
  exact hb'ne hperp

theorem comm_mem_Z_of_mem_CN91 (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {l : G} (hl : l ∈ (QB B ⊓ M) ⊓ hc.CN t) {d : G}
    (hdB : d ∈ QB B) (hdC : d ∈ QB (conjSubgroup r B)) (hdQ : d ∈ Q) :
    ⁅l, d⁆ ∈ Z := by
  have hlL : l ∈ LB M Q B := le_sup_right (a := Q) ⟨hl.1.1, hl.1.2⟩
  have hlN : l ∈ hc.CN t := hl.2
  have hlM : l ∈ M := hl.1.2
  have hZB : ⁅l, d⁆ ∈ (Z ⊔ B : Subgroup G) :=
    hc.comm_LB_inf_QB_mem_sup hlL ⟨hdQ, hdB⟩
  have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs hr hlN
  have hldQ : l * d * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) d).mp hdQ
  have hldQC : l * d * l⁻¹ ∈ QB (conjSubgroup r B) :=
    ((Subgroup.mem_normalizer_iff.mp hnorm d).mp ⟨hdQ, hdC⟩).2
  have hcommQC : ⁅l, d⁆ ∈ Q ⊓ QB (conjSubgroup r B) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [commutatorElement_def]
      exact Q.mul_mem hldQ (Q.inv_mem hdQ)
    · simp only [commutatorElement_def]
      exact (QB (conjSubgroup r B)).mul_mem hldQC ((QB (conjSubgroup r B)).inv_mem hdC)
  have hBinf : B ⊓ QB (conjSubgroup r B) = ⊥ :=
    B_inf_QB_conj_eq_bot91 h34 hc hs hnot hr hplane
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem (hc.Rt_le_M t hr)
  have hZQC : Z ≤ QB (conjSubgroup r B) := hcC.Z_le_QB.1
  have hZBnorm : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hb))
  have hZint : ((Z ⊔ B : Subgroup G) ⊓ QB (conjSubgroup r B)) = Z := by
    refine le_antisymm ?_ (le_inf le_sup_left hZQC)
    intro x hx
    obtain ⟨hxZB, hxQC⟩ := hx
    obtain ⟨b, hb, z, hz, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := B) (K := Z) hZBnorm
        (by rwa [sup_comm] at hxZB)
    have hzQC : z ∈ QB (conjSubgroup r B) := hZQC hz
    have hbQC : b ∈ QB (conjSubgroup r B) := by
      have e : b = (b * z) * z⁻¹ := by group
      rw [e]
      exact (QB (conjSubgroup r B)).mul_mem hxQC ((QB (conjSubgroup r B)).inv_mem hzQC)
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← hBinf]
      exact ⟨hb, hbQC⟩
    rw [Subgroup.mem_bot] at hbBot
    simpa [hbBot] using hz
  exact hZint.le ⟨hZB, hcommQC.2⟩

theorem centLam91 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := exists_pts91 h34 hs
  haveI := hn
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  exact centLam_of_points h34 hc hs.toSec5 P.card E (nondegenerate_polarBilin_quadPlus 2 K) h3 φ
    P.ker ψ P.sing P.ne_zero P.perp P.root

theorem mem_V_of_mem_QB_QB91 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) {x : G} (hxB : x ∈ QB B)
    (hxC : x ∈ QB (conjSubgroup r B)) (hxQ : x ∈ Q) : x ∈ Vt M (LB M Q B) B Z t :=
  centLam91 h34 hs x ⟨hxQ, hxB⟩
    (fun l hl => comm_mem_Z_of_mem_CN91 h34 hc hs.toSec5 (sec9_notQB h34 hs) hr hplane hl hxB hxC
      hxQ)

theorem card_inter_le_of_mem_V (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hBinf : B ⊓ QB (conjSubgroup r B) = ⊥)
    (hmemV : ∀ x, x ∈ QB B → x ∈ QB (conjSubgroup r B) → x ∈ Q →
      x ∈ Vt M (LB M Q B) B Z t)
    {m : ℕ} (hm : 2 ≤ m)
    (hVcard : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1))
    (hVQB : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m)) :
    Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) ≤ Nat.card Z ^ (2 * m - 1) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hq2 : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  have hqpos : 0 < Nat.card Z := by omega
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set W : Subgroup G := Wt Q V with hWdef
  set C : Subgroup G := conjSubgroup r B with hCdef
  set X₁ : Subgroup G := QB B ⊓ W with hX₁def
  set X₂ : Subgroup G := QB C ⊓ W with hX₂def
  set A : Subgroup G := V ⊓ QB B with hAdef
  set D : Subgroup G := V ⊓ QB C with hDdef
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hZW : Z ≤ W := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
    hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs.notQ
  have hIle : X₁ ⊓ X₂ ≤ A ⊓ D := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxB : x ∈ QB B := hx1.1
    have hxW : x ∈ W := hx1.2
    have hxC : x ∈ QB C := hx2.1
    have hxQ : x ∈ Q := hWQ hxW
    have hxV : x ∈ V := hmemV x hxB hxC hxQ
    exact ⟨⟨hxV, hxB⟩, ⟨hxV, hxC⟩⟩
  have hAV : A ≤ V := inf_le_left
  have hDV : D ≤ V := inf_le_left
  have hVconj : conjSubgroup r V = V :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr)
  have hDconj : D = conjSubgroup r A := by
    rw [hDdef, hAdef, hCdef, QB_conj, conjSubgroup_inf, hVconj]
  have hDcard : Nat.card ↥D = Nat.card Z ^ (2 * m) := by
    rw [hDconj, card_conjSubgroup, hVQB]
  have hAcard : Nat.card ↥A = Nat.card Z ^ (2 * m) := hVQB
  have hDrelV : D.relIndex V = Nat.card Z := by
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := V)
    have hDVint : D ⊓ V = D := inf_of_le_left hDV
    rw [hDVint, hDcard, hVcard] at h1
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hqpos (2 * m)) ?_
    rw [h1, pow_succ']
  have hDrelVne : D.relIndex V ≠ 0 := by rw [hDrelV]; omega
  have hrel_le : D.relIndex A ≤ Nat.card Z := by
    rw [← hDrelV]
    exact Subgroup.relIndex_le_of_le_right hAV hDrelVne
  have hBA : B ≤ A := le_inf (hc.B_le_Vt ht) hc.B_le_QB
  have hB_inf_D : B ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hbC : b ∈ QB C := (inf_le_right : D ≤ QB C) hb.2
    have hmem : b ∈ B ⊓ QB C := ⟨hb.1, hbC⟩
    rw [hBinf] at hmem
    exact hmem
  have hBcard : Nat.card ↥B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  haveI : IsMulCommutative ↥A :=
    ⟨⟨fun x y => Subtype.ext (hVcomm x.1 (hAV x.2) y.1 (hAV y.2))⟩⟩
  let f : ↥B → ↥A ⧸ (D.subgroupOf A) := fun b =>
    QuotientGroup.mk (s := D.subgroupOf A) (⟨(b : G), hBA b.2⟩ : ↥A)
  have hf_inj : Function.Injective f := by
    intro b1 b2 h
    have hmem : (⟨(b1 : G), hBA b1.2⟩ : ↥A) / ⟨(b2 : G), hBA b2.2⟩ ∈ D.subgroupOf A :=
      (QuotientGroup.eq_iff_div_mem).mp h
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmemB : (b1 : G) * (b2 : G)⁻¹ ∈ B := B.mul_mem b1.2 (B.inv_mem b2.2)
    have hmemD : (b1 : G) * (b2 : G)⁻¹ ∈ D := by
      simpa only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    have hbot : (b1 : G) * (b2 : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hB_inf_D]
      exact ⟨hmemB, hmemD⟩
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  have hrel_ge : Nat.card Z ≤ D.relIndex A := by
    have h1 := Nat.card_le_card_of_injective f hf_inj
    have h2 : Nat.card (↥A ⧸ (D.subgroupOf A)) = D.relIndex A := rfl
    rwa [hBcard, h2] at h1
  have hrel_eq : D.relIndex A = Nat.card Z := le_antisymm hrel_le hrel_ge
  have hADcard : Nat.card ↥(A ⊓ D) = Nat.card Z ^ (2 * m - 1) := by
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := A)
    rw [hrel_eq, hAcard] at h1
    have h2 : Nat.card Z * Nat.card ↥(A ⊓ D) = Nat.card Z * Nat.card Z ^ (2 * m - 1) := by
      rw [inf_comm] at h1
      rw [h1, ← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
    exact Nat.eq_of_mul_eq_mul_left hqpos h2
  have hIupper : Nat.card ↥(X₁ ⊓ X₂) ≤ Nat.card Z ^ (2 * m - 1) :=
    (Subgroup.card_le_of_le hIle).trans_eq hADcard
  exact hIupper

theorem hboxB91 (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t)
    (hmemV : ∀ x, x ∈ QB B → x ∈ QB (conjSubgroup r B) → x ∈ Q →
      x ∈ Vt M (LB M Q B) B Z t) :
    ⁅QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q B ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t := by
  refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
  have ht : t ∈ LB M Q B := hs.mem
  have hxQ : x ∈ Q := (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hx.2
  have hlM : l ∈ M := hc.LB_le_M hl.1
  have hlxB : ⁅l, x⁆ ∈ QB B :=
    comm_LB_Wt_mem_QB hc (hc.B_le_Vt ht) hl.1 hx.2
  have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs hr hl.2
  have hldQC : l * x * l⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) :=
    (Subgroup.mem_normalizer_iff.mp hnorm x).mp ⟨hxQ, hx.1⟩
  have hlxQC : ⁅l, x⁆ ∈ QB (conjSubgroup r B) := by
    simpa only [commutatorElement_def] using
      (QB (conjSubgroup r B)).mul_mem hldQC.2 ((QB (conjSubgroup r B)).inv_mem hx.1)
  have hlxQ : ⁅l, x⁆ ∈ Q := by
    have h1 : l * x * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) x).mp hxQ
    simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem hxQ)
  have hlxV : ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t :=
    hmemV _ hlxB hlxQC hlxQ
  rw [← commutatorElement_inv]
  exact (Vt M (LB M Q B) B Z t).inv_mem hlxV

theorem hboxC91 (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t)
    (hmemV : ∀ x, x ∈ QB B → x ∈ QB (conjSubgroup r B) → x ∈ Q →
      x ∈ Vt M (LB M Q B) B Z t) :
    ⁅QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      LB M Q (conjSubgroup r B) ⊓ hc.CN t⁆ ≤ Vt M (LB M Q B) B Z t := by
  refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
  have ht : t ∈ LB M Q B := hs.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup r B ≤ conjSubgroup r B ⊔ Z).trans
      (hc.conj_Rt_le_Vt ht hr)
  have hxQ : x ∈ Q := (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hx.2
  have hlxC : ⁅l, x⁆ ∈ QB (conjSubgroup r B) :=
    comm_LB_Wt_mem_QB hcC hCV hl.1 hx.2
  have hnormB := sec52a_QB_inf_normalizes_of_mem_CN hc hs (r := 1)
    (Subgroup.one_mem (Rt M (LB M Q B) t)) hl.2
  have hnormB' : l ∈ Subgroup.normalizer ((Q ⊓ QB B : Subgroup G) : Set G) := by
    simpa [conjSubgroup_one] using hnormB
  have hldQB : l * x * l⁻¹ ∈ Q ⊓ QB B :=
    (Subgroup.mem_normalizer_iff.mp hnormB' x).mp ⟨hxQ, hx.1⟩
  have hlxB : ⁅l, x⁆ ∈ QB B := by
    simpa only [commutatorElement_def] using
      (QB B).mul_mem hldQB.2 ((QB B).inv_mem hx.1)
  have hlxQ : ⁅l, x⁆ ∈ Q := by
    have hlM : l ∈ M := hcC.LB_le_M hl.1
    have h1 : l * x * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) x).mp hxQ
    simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem hxQ)
  have hlxV : ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t :=
    hmemV _ hlxB hlxC hlxQ
  rw [← commutatorElement_inv]
  exact (Vt M (LB M Q B) B Z t).inv_mem hlxV

end HS9


theorem step91Inter_of (h34 : Stroth34Statement) : Step91InterStatement := by
  intro G _ _ M Q Z B hc n t hs r hr V W hV hW
  subst hV hW
  have hs5 := hs.toSec5
  have hrR := hr.mem
  have hBinf := HS9.B_inf_QB_conj_eq_bot91 h34 hc hs5 (sec9_notQB h34 hs) hrR hr.plane
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have h := HS9.card_inter_le_of_mem_V h34 hc hs5 hrR hBinf
    (fun x hxB hxC hxQ => HS9.mem_V_of_mem_QB_QB91 h34 hs hrR hr.plane hxB hxC hxQ)
    (m := 2) le_rfl hs.card_V (HS9.card_Vt_inf_QB_plus4 P)
  have e : QB (conjSubgroup r B) ⊓ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) =
      (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
        (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) := by
    ext x
    constructor
    · rintro ⟨⟨hA, hB⟩, hxW⟩
      exact ⟨⟨hB, hxW⟩, hA, hxW⟩
    · rintro ⟨⟨hB, hxW⟩, hA, -⟩
      exact ⟨⟨hA, hB⟩, hxW⟩
  rw [e]
  simpa using h

theorem step91MixedComm_of (h34 : Stroth34Statement) : Step91MixedCommStatement := by
  intro G _ _ M Q Z B hc n t hs r hr V W hV hW
  subst hV hW
  have hs5 := hs.toSec5
  have hrR := hr.mem
  have hmemV : ∀ x, x ∈ QB B → x ∈ QB (conjSubgroup r B) → x ∈ Q →
      x ∈ Vt M (LB M Q B) B Z t := fun x hxB hxC hxQ =>
    HS9.mem_V_of_mem_QB_QB91 h34 hs hrR hr.plane hxB hxC hxQ
  refine ⟨fun s hs' x hx => ?_, fun s hs' x hx => ?_⟩
  · have := Subgroup.commutator_le.mp (HS9.hboxB91 hc hs5 hrR hmemV) x hx s hs'
    rw [← commutatorElement_inv]
    exact (Vt M (LB M Q B) B Z t).inv_mem this
  · have := Subgroup.commutator_le.mp (HS9.hboxC91 hc hs5 hrR hmemV) x hx s hs'
    rw [← commutatorElement_inv]
    exact (Vt M (LB M Q B) B Z t).inv_mem this

end CFSG.RankThree.GF2n.Stroth80
