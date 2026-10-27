module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec83Vec
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsPoints

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_natdata (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {m : ℕ}
    (hmSp : SpMNat hc t m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin m ⊕ Fin m → K)) (u u' : Fin m ⊕ Fin m → K),
      Sec8Pts hc t r m K φ u u' ∧
      (∀ r' : ↥(Rt M (LB M Q B) t),
        (HypPlane Q Z B (conjSubgroup (r' : G) B) t ↔
          spForm m K u ((φ r' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0)) ∧
      (∀ x : Fin m ⊕ Fin m → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      ∃ (nn : ℕ) (γ : G → GaloisField 2 nn) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ)
        (_ : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K),
        ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)),
          M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v := by
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hmSp
  haveI := hn
  have hm : 2 ≤ m := by
    obtain ⟨m₀, hm₀, hsp₀⟩ := hs.sp
    have hsp : SpMNat hc t m := ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩
    rw [hsp.m_unique hsp₀]
    exact hm₀
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  obtain ⟨u, hu0, hBiff, hL, hr'⟩ := hc.sp_points_core h34 hRoot h5 hK hm φ hφ hker ψ hψ
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ :=
    hc.exists_globalRingEquiv ht hK addCommutantScalar_statedSp φ hφ ψ hψ
  have hr1 := hr' ⟨r, hr.mem⟩
  refine ⟨K, fK, finK, inferInstance, φ, hn, ψ, u,
    (φ ⟨r, hr.mem⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u,
    ⟨hm, hK, hφ, hker, ⟨hnorm, hn, ψ, hψ⟩, hr1.1.mp hr.plane, hL, hr1.2⟩,
    fun r' => (hr' r').1, hBiff, hψ, nn, γ, M₀, hglob, θ, hθ⟩

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_isSecMod_psi {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K}
    {u u' : Fin m ⊕ Fin m → K} (hpts : Sec8Pts hc t r m K φ u u')
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    @IsSecMod G _ (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (Fin m ⊕ Fin m → K) _
      hpts.vecAct
      (ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf (Vt M (LB M Q B) B Z t)))) := by
  refine @IsSecMod.mk G _ (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (Fin m ⊕ Fin m → K) _
    hpts.vecAct _ ?_ ?_ ?_ ?_
  · intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm a)
    exact ⟨x, by simp [hx]⟩
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro ρ x y hxy
    have := hψ ρ x y hxy
    refine Multiplicative.toAdd.injective ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      toAdd_ofAdd]
    exact this
  · intro a
    funext i
    simp [CharTwo.add_self_eq_zero]

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_hypPlane_iff (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    HypPlane Q Z B (conjSubgroup r B) t ↔ ¬ conjSubgroup r B ≤ QB B := by
  unfold HypPlane
  have hs5 : Sec5Hyp hc n t := hs.toSec5
  have hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs5 (Or.inl hs.spNat)
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs5 hnot
  have hV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := hc.conj_Rt_le_Vt hs5.mem hr
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  constructor
  · rintro ⟨ĉ, hĉQ, hĉC, b, hb, hne⟩ hsub
    have hwV : ⁅ĉ, t⁆ ∈ Vt M (LB M Q B) B Z t := hV hĉC
    have hsupQB : conjSubgroup r B ⊔ Z ≤ QB B := sup_le hsub hZQB
    have hwQB : ⁅ĉ, t⁆ ∈ QB B := hsupQB hĉC
    have hz : ⁅ĉ, t⁆ * ⁅ĉ, t⁆⁻¹ ∈ Z := by
      rw [mul_inv_cancel]
      exact Z.one_mem
    have hkey : ⁅b, ĉ⁆ = 1 := (hperp ⁅ĉ, t⁆ hwV).mp hwQB b hb ĉ hĉQ hz
    exact hne hkey
  · intro hnsub
    obtain ⟨d, hdC, hdQB⟩ := SetLike.not_le_iff_exists.mp hnsub
    have hdV : d ∈ Vt M (LB M Q B) B Z t := hV (Subgroup.mem_sup_left hdC)
    have hex : ¬ ∀ b ∈ B, ∀ y ∈ Q, ⁅y, t⁆ * d⁻¹ ∈ Z → ⁅b, y⁆ = 1 := fun h =>
      hdQB ((hperp d hdV).mpr h)
    push Not at hex
    obtain ⟨b, hb, y, hyQ, hyZ, hne⟩ := hex
    refine ⟨y, hyQ, ?_, b, hb, hne⟩
    have hmul : ⁅y, t⁆ = ⁅y, t⁆ * d⁻¹ * d := by simp
    rw [hmul]
    exact (conjSubgroup r B ⊔ Z).mul_mem (Subgroup.mem_sup_right hyZ)
      (Subgroup.mem_sup_left hdC)

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7A_of_hypPlane (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Sec7A hc t r := by
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hs.spNat
  obtain ⟨u, hu0, hL, hr'⟩ := hc.sp_points h34 hRoot hs.toSec5 hK hm φ hφ hker hact
  have hr1 := hr' ⟨r, hr⟩
  have hne : spForm m K u ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 :=
    hr1.1.mp hplane
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
    rw [hc.LB_conj (hc.Rt_le_M t hr)]
    exact hr1.2
  have hgen : Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ LB M Q (conjSubgroup r B)) :=
    le_sup_secSp φ hφ hker hne hL hL2
  exact ⟨hr, hplane, hc.Rt_eq_sup_of_51 h51 hs.toSec5 (Or.inl hs.spNat) hr hplane hgen⟩

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_inter_smul_closed {hc : Ctx M Q Z B} {t : G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {nn : ℕ} {γ : G → GaloisField 2 nn}
    {M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ}
    (hglob : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hθ : ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)),
      M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v)
    {V₁ : Subgroup G} (hZV₁ : Z ≤ V₁) (hV₁Q : V₁ ≤ Q)
    (hV₁ : ∀ (c : GaloisField 2 nn) (e : M₀.E), e ∈ M₀.img V₁ → c • e ∈ M₀.img V₁)
    {g : G} (hg : g ∈ M) :
    ∀ (c : K) (d : ↥(Vt M (LB M Q B) B Z t)),
      (d : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g V₁ →
      ∃ d' : ↥(Vt M (LB M Q B) B Z t), (d' : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g V₁ ∧
        secVec ψ d' = c • secVec ψ d := by
  intro c d hd
  obtain ⟨hdV, hdC⟩ := Subgroup.mem_inf.mp hd
  have hdQ : (d : G) ∈ Q := hc.Vt_le_Q t hdV
  obtain ⟨σ, -, T, hTs, hTπ, -, -⟩ := hglob.act g hg
  have hw : g⁻¹ * (d : G) * g ∈ V₁ := mem_conjSubgroup.mp hdC
  have hwQ : g⁻¹ * (d : G) * g ∈ Q := hV₁Q hw
  have hgwg : g * (g⁻¹ * (d : G) * g) * g⁻¹ = (d : G) := by group
  have hπd : M₀.π (d : G) = T (M₀.π (g⁻¹ * (d : G) * g)) := by
    rw [← hTπ _ hwQ, hgwg]
  have hσw : σ.symm (θ.symm c) • M₀.π (g⁻¹ * (d : G) * g) ∈ M₀.img V₁ :=
    hV₁ _ _ (M₀.pi_mem_img hw hwQ)
  obtain ⟨w', hw'V₁, hw'Q, hw'π⟩ := (Tim79.QuadModel.mem_img M₀).mp hσw
  have hd₁C : g * w' * g⁻¹ ∈ conjSubgroup g V₁ := by
    refine mem_conjSubgroup.mpr ?_
    have h : g⁻¹ * (g * w' * g⁻¹) * g = w' := by group
    rw [h]
    exact hw'V₁
  have hd₁Q : g * w' * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) w').mp hw'Q
  have hπd₁ : M₀.π (g * w' * g⁻¹) = θ.symm c • M₀.π (d : G) := by
    rw [hTπ w' hw'Q, hw'π, hTs, RingEquiv.apply_symm_apply, ← hπd]
  have hdmem : M₀.π (d : G) ∈ M₀.img (Vt M (LB M Q B) B Z t) := M₀.pi_mem_img hdV hdQ
  obtain ⟨d₂, hd₂V, hd₂Q, hπd₂⟩ := (Tim79.QuadModel.mem_img M₀).mp
    (hc.smul_mem_img_Vt hglob t (θ.symm c) hdmem)
  have hkey : (g * w' * g⁻¹)⁻¹ * d₂ ∈ Z :=
    (Tim79.QuadModel.pi_eq_iff M₀ hd₁Q hd₂Q).mp (hπd₁.trans hπd₂.symm)
  have hZc : ∀ z ∈ Z, z ∈ conjSubgroup g V₁ := by
    intro z hz
    have hz' : z ∈ conjSubgroup g Z := by
      rw [hc.conj_Z_eq hg]
      exact hz
    exact mem_conjSubgroup.mpr (hZV₁ (mem_conjSubgroup.mp hz'))
  have hd₂C : d₂ ∈ conjSubgroup g V₁ := by
    have h := (conjSubgroup g V₁).mul_mem hd₁C (hZc _ hkey)
    rwa [mul_inv_cancel_left] at h
  refine ⟨⟨d₂, hd₂V⟩, Subgroup.mem_inf.mpr ⟨hd₂V, hd₂C⟩, ?_⟩
  have key := hθ (θ.symm c) d ⟨d₂, hd₂V⟩ hπd₂
  rw [RingEquiv.apply_symm_apply] at key
  exact key

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_point_eq {hc : Ctx M Q Z B} {m₁ m₂ : G} (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) {d : G}
    (hd₁ : d ∈ conjSubgroup m₁ B ⊔ Z) (hd₂ : d ∈ conjSubgroup m₂ B ⊔ Z) (hdZ : d ∉ Z) :
    conjSubgroup m₁ B ⊔ Z = conjSubgroup m₂ B ⊔ Z := by
  have hc₁ : Ctx M Q Z (conjSubgroup m₁ B) := hc.conj_of_mem h₁
  have hg : m₂ * m₁⁻¹ ∈ M := M.mul_mem h₂ (M.inv_mem h₁)
  have hconj : conjSubgroup (m₂ * m₁⁻¹) (conjSubgroup m₁ B) = conjSubgroup m₂ B := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hd₂' : d ∈ conjSubgroup (m₂ * m₁⁻¹) (conjSubgroup m₁ B) ⊔ Z := by
    rw [hconj]
    exact hd₂
  have key := sec8PointTI_holds hc₁ hg ⟨d, hd₁, hd₂', hdZ⟩
  rw [hconj] at key
  exact key.symm

theorem sec8_inf_QB_eq_of_sup_eq_le_sup_comm {C C' : Subgroup G} (h : C ⊔ Z = C' ⊔ Z) :
    C' ≤ Z ⊔ C := by
  have h1 : C' ≤ C' ⊔ Z := le_sup_left
  rw [← h, sup_comm] at h1
  exact h1

theorem sec8_inf_QB_eq_of_sup_eq_comm_mem {C : Subgroup G} (hC : Ctx M Q Z C) {q x : G}
    (hq : q ∈ Q) (hx : x ∈ Q ⊓ QB C) : q * x * q⁻¹ ∈ Q ⊓ QB C := by
  obtain ⟨hxQ, -⟩ := Subgroup.mem_inf.mp hx
  have hcomm : ⁅q, x⁆ ∈ Z := hC.hyp.toHyp79.comm_mem_V hq hxQ
  have hZ : ⁅q, x⁆ ∈ Q ⊓ QB C :=
    Subgroup.mem_inf.mpr ⟨hC.hyp.Z_normal.1 hcomm, hC.Z_le_QB.1 hcomm⟩
  have e : q * x * q⁻¹ = ⁅q, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ hZ hx

theorem sec8_inf_QB_eq_of_sup_eq_normalizes {C : Subgroup G} (hC : Ctx M Q Z C) {q : G}
    (hq : q ∈ Q) : q ∈ Subgroup.normalizer ((Q ⊓ QB C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ Q ⊓ QB C := hx
    exact sec8_inf_QB_eq_of_sup_eq_comm_mem hC hq hx'
  · intro hx
    have hx' : q * x * q⁻¹ ∈ Q ⊓ QB C := hx
    have h2 := sec8_inf_QB_eq_of_sup_eq_comm_mem hC (Q.inv_mem hq) hx'
    have e : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
    rw [e] at h2
    exact h2

theorem sec8_inf_QB_eq_of_sup_eq {C C' : Subgroup G} (hC : Ctx M Q Z C) (hC' : Ctx M Q Z C')
    (h : C ⊔ Z = C' ⊔ Z) : Q ⊓ QB C = Q ⊓ QB C' := by
  obtain ⟨p, hpQ, hp⟩ :=
    hC.exists_conj_of_le_ZB hC' (sec8_inf_QB_eq_of_sup_eq_le_sup_comm h)
  subst hp
  have hpM : p ∈ M := hC.hyp.Q_normal.1 hpQ
  have hX : conjSubgroup p (Q ⊓ QB C) = Q ⊓ QB C :=
    conjSubgroup_eq_self_iff.mpr (sec8_inf_QB_eq_of_sup_eq_normalizes hC hpQ)
  rw [QB_conj]
  calc Q ⊓ QB C = conjSubgroup p (Q ⊓ QB C) := hX.symm
    _ = conjSubgroup p Q ⊓ conjSubgroup p (QB C) := CFSG.RankThree.GF2n.conjSubgroup_inf p Q (QB C)
    _ = Q ⊓ conjSubgroup p (QB C) := by rw [hC.conj_Q_eq hpM]

theorem sec8_LB_eq_of_sup_eq {C C' : Subgroup G} (hC : Ctx M Q Z C) (hC' : Ctx M Q Z C')
    (h : C ⊔ Z = C' ⊔ Z) : LB M Q C = LB M Q C' := by
  obtain ⟨p, hpQ, hp⟩ :=
    hC.exists_conj_of_le_ZB hC' (sec8_inf_QB_eq_of_sup_eq_le_sup_comm h)
  subst hp
  have hpM : p ∈ M := hC.hyp.Q_normal.1 hpQ
  have hpLB : p ∈ LB M Q C := sec39_Q_le_LB hpQ
  have hn : conjSubgroup p (LB M Q C) = LB M Q C :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpLB)
  rw [hC.LB_conj hpM, hn]

theorem sec8_le_QB_iff_of_sup_eq_imp {C C' D D' : Subgroup G} (hC : Ctx M Q Z C)
    (hC' : Ctx M Q Z C') (h : C ⊔ Z = C' ⊔ Z) (hDQ : D ≤ Q) (hD : D ⊔ Z = D' ⊔ Z)
    (hDC : D ≤ QB C) : D' ≤ QB C' := by
  have hX : Q ⊓ QB C = Q ⊓ QB C' := sec8_inf_QB_eq_of_sup_eq hC hC' h
  have hZX : Z ≤ Q ⊓ QB C := by
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨hC.hyp.Z_normal.1 hz, hC.Z_le_QB.1 hz⟩
  have hDX : D ≤ Q ⊓ QB C := by
    intro d hd
    exact Subgroup.mem_inf.mpr ⟨hDQ hd, hDC hd⟩
  have hDZ : D ⊔ Z ≤ Q ⊓ QB C := sup_le hDX hZX
  have hD'le : D' ≤ D ⊔ Z := by
    have h1 : D' ≤ D' ⊔ Z := le_sup_left
    rw [← hD] at h1
    exact h1
  calc D' ≤ D ⊔ Z := hD'le
    _ ≤ Q ⊓ QB C := hDZ
    _ = Q ⊓ QB C' := hX
    _ ≤ QB C' := inf_le_right

theorem sec8_le_QB_iff_of_sup_eq {C C' D D' : Subgroup G} (hC : Ctx M Q Z C) (hC' : Ctx M Q Z C')
    (h : C ⊔ Z = C' ⊔ Z) (hDQ : D ≤ Q) (hD'Q : D' ≤ Q) (hD : D ⊔ Z = D' ⊔ Z) :
    D ≤ QB C ↔ D' ≤ QB C' :=
  ⟨fun hDC => sec8_le_QB_iff_of_sup_eq_imp hC hC' h hDQ hD hDC,
    fun hD'C => sec8_le_QB_iff_of_sup_eq_imp hC' hC h.symm hD'Q hD.symm hD'C⟩

end

end CFSG.RankThree.GF2n.Stroth80
