module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAFix
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAMatAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714 Module
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem matAct_zero {L : Type*} [AddCommGroup L] [Module K L] (x : Fin 2 → L) :
    matAct (0 : Matrix (Fin 2) (Fin 2) K) x = 0 := by
  funext i
  simp [matAct_apply]

theorem exists_det2_ne_zero {f : Fin 2 → K} (hf : f ≠ 0) : ∃ f₂ : Fin 2 → K, det2 f₂ f ≠ 0 := by
  by_cases h0 : f 0 = 0
  · have h1 : f 1 ≠ 0 := by
      intro h1
      exact hf (funext fun i => by fin_cases i <;> simp [h0, h1])
    exact ⟨![1, 0], by simp [det2, h1]⟩
  · exact ⟨![0, 1], by simp [det2, h0]⟩

@[expose] def zStar (hS : IsTensorSetup hc n M₀ ρ b) (t g : G) : Subgroup (Mbar M Q) :=
  bar M Q (conjSubgroup g (hc.CN t)) ⊓ fixSub ρ (hc.VtSub hS.model t : Set M₀.E)

@[expose] def ActsAsRoot (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L₄ : Type} [AddCommGroup L₄]
    [Module K L₄] (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)) (f : Fin 2 → K) (zb : Mbar M Q)
    (s : K) : Prop :=
  ∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t)) (hzx : zb * x * zb⁻¹ ∈ bar M Q (hc.CN t)),
    eN ⟨delta hS t _ (mem_bar_H0_of_CN hzx), delta_mem_deltaSub hS hzx⟩ =
      eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ +
        s • matAct (rootN f) (eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩)

section Nbr

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.actsAsRoot_unique {n' : ℕ} (hs : Sec7Hyp hc n' t)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    {f : Fin 2 → K} (hf : f ≠ 0) {zb : Mbar M Q}
    (hzN : ∀ x ∈ bar M Q (hc.CN t), zb * x * zb⁻¹ ∈ bar M Q (hc.CN t)) {s s' : K}
    (h : ActsAsRoot hS t eN f zb s) (h' : ActsAsRoot hS t eN f zb s') : s = s' := by
  classical
  obtain ⟨f₂, hf₂⟩ := exists_det2_ne_zero hf
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : L₄, m₀ ≠ 0 := by
    have hpos : 0 < finrank K L₄ := by rw [D.finrank₄]; norm_num
    haveI : Nontrivial L₄ := Module.nontrivial_of_finrank_pos hpos
    exact exists_ne 0
  obtain ⟨x, hx, hxF⟩ := hSΔ _ (eN.symm (pureT f₂ m₀)).2
  have hX : eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ = pureT f₂ m₀ := by
    rw [show (⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ :
      ↥(deltaSub hS t)) = eN.symm (pureT f₂ m₀) from Subtype.ext hxF.symm,
      LinearEquiv.apply_symm_apply]
  have h1 := h x hx (hzN x hx)
  have h2 := h' x hx (hzN x hx)
  rw [hX] at h1 h2
  rw [h1] at h2
  have h3 : (s - s') • matAct (rootN f) (pureT f₂ m₀) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel h2
  rw [matAct_rootN_pureT, smul_smul] at h3
  have h4 : pureT f m₀ ≠ 0 := fun h0 => hm₀ (pureT_injective hf (h0.trans (map_zero _).symm))
  rcases smul_eq_zero.mp h3 with h5 | h5
  · exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hf₂)
  · exact absurd h5 h4

theorem ConfigAData.exists_actsAsRoot (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    (hMat : MatActProp hS t eN Z0)
    (hNormFix : ∀ (z : G) (hzH : z ∈ H0 M Z),
      (∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk (⟨z, hzH.1⟩ : ↥M))).toAdd e = e) →
        z ∈ NormH0 M Z Z0)
    {g : G} (hg : IsSymNbr hc t Z0 g) {f : Fin 2 → K} {y : L₄} (hf : f ≠ 0) (hy : y ≠ 0)
    (hl : HasLine hS t eN Z0 g f y) {zb : Mbar M Q} (hzb : zb ∈ zStar hS t g) :
    (∃ z : G, ∃ hz : z ∈ NormH0 M Z Z0, QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hz.1.1⟩ = zb ∧
      (∀ r ∈ Rt M (LB M Q B) t, ⁅z, r⁆ ∈ hc.CN t) ∧ ∃ k : ℕ, z ^ 2 ^ k ∈ Q) ∧
    (∀ x ∈ bar M Q (hc.CN t), zb * x * zb⁻¹ ∈ bar M Q (hc.CN t)) ∧
      ∃ s : K, ActsAsRoot hS t eN f zb s := by
  classical
  obtain ⟨hgM, hV', hne, hZN'⟩ := hg
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  haveI : FiniteDimensional K L₄ := Module.finite_of_finrank_pos (by rw [D.finrank₄]; norm_num)
  obtain ⟨hzN', hzV⟩ := Subgroup.mem_inf.mp hzb
  obtain ⟨m, hmN', rfl⟩ := exists_of_mem_bar hzN'
  have hmH : (m : G) ∈ H0 M Z := by
    have h1 := hc.conj_mem_H0 hgM (hc.Rt_le_H0 t (Ctx.mem_CN.mp (mem_conjSubgroup.mp hmN')).1)
    rwa [show g * (g⁻¹ * (m : G) * g) * g⁻¹ = m by group] at h1
  have hzK := hNormFix m hmH hzV
  have hzVZ : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅(m : G), v⁆ ∈ Z := by
    intro v hv
    have hvQ : v ∈ Q := hc.Vt_le_Q t hv
    refine (comm_mem_Z_iff_act_eq hS m hvQ).mpr ?_
    exact hzV _ ((hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hv hvQ))
  have hzR := comm_mem_CN_of_centralizes hZt hZcard hS hs hZ0 hzK hzVZ
  have hNn : conjSubgroup (m : G) (hc.CN t) = hc.CN t := sec7_conj_CN_eq hZt hZcard hc hs hZ0 hzK
  have hzN : ∀ x ∈ bar M Q (hc.CN t), (QuotientGroup.mk m : Mbar M Q) * x *
      (QuotientGroup.mk m : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) := by
    intro x hx
    obtain ⟨m', hm', rfl⟩ := exists_of_mem_bar hx
    have h1 : (m : G) * (m' : G) * (m : G)⁻¹ ∈ conjSubgroup (m : G) (hc.CN t) := ⟨m', hm', rfl⟩
    rw [hNn] at h1
    exact mk_mem_bar (m * m' * m⁻¹) h1
  obtain ⟨hD2, -, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hN2 : IsPGroup 2 ↥(hc.CN t) :=
    hD2.to_le (sec715_CN_le_O2NormPre h34 h51 hA hZt hZcard hc hs hZ0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (m : G) ^ 2 ^ k = 1 := by
    have hc' : g⁻¹ * (m : G) * g ∈ hc.CN t := mem_conjSubgroup.mp hmN'
    obtain ⟨k, hk⟩ := hN2 ⟨_, hc'⟩
    refine ⟨k, ?_⟩
    have h1 : (g⁻¹ * (m : G) * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have e1 : (g⁻¹ * (m : G) * g) ^ 2 ^ k = g⁻¹ * (m : G) ^ 2 ^ k * g := by
      rw [show g⁻¹ * (m : G) * g = g⁻¹ * (m : G) * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
    rw [e1] at h1
    have h2 : g * (g⁻¹ * (m : G) ^ 2 ^ k * g) * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]
    rwa [show g * (g⁻¹ * (m : G) ^ 2 ^ k * g) * g⁻¹ = (m : G) ^ 2 ^ k by group, mul_one,
      mul_inv_cancel] at h2
  refine ⟨⟨m, hzK, rfl, hzR, k, by rw [hk]; exact Q.one_mem⟩, hzN, ?_⟩
  obtain ⟨A, hAz⟩ := hMat m hzK hzR
  have hAz' : ∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t))
      (hzx : (QuotientGroup.mk m : Mbar M Q) * x * (QuotientGroup.mk m : Mbar M Q)⁻¹ ∈
        bar M Q (hc.CN t)),
      eN ⟨delta hS t _ (mem_bar_H0_of_CN hzx), delta_mem_deltaSub hS hzx⟩ =
        matAct A (eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩) :=
    fun x hx hzx => hAz x hx hzx
  obtain ⟨u, huZ, huQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  let gm : ↥M := ⟨g, hgM⟩
  let um : ↥M := ⟨u, hc.centre_le_M t hZ0 huZ⟩
  have hv₀ : (QuotientGroup.mk gm : Mbar M Q) * QuotientGroup.mk um * (QuotientGroup.mk gm)⁻¹ ∈
      bar M Q (conjSubgroup g Z0) := by
    refine mk_mem_bar (gm * um * gm⁻¹) (mem_conjSubgroup.mpr ?_)
    show g⁻¹ * (g * u * g⁻¹) * g ∈ Z0
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact huZ
  have hv₀N := bar_mono' hV' hv₀
  set v₀ := (QuotientGroup.mk gm : Mbar M Q) * QuotientGroup.mk um * (QuotientGroup.mk gm)⁻¹
    with hv₀def
  have hΔ0 : delta hS t v₀ (mem_bar_H0_of_CN hv₀N) ≠ 0 := by
    intro h0
    have hR := bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hv₀N
    have hZ := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mp h0
    have hZ' : g * u * g⁻¹ ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 (gm * um * gm⁻¹)).mp hZ
    exact hne (conjSubgroup_eq_self_iff.mpr (hTI g hgM u huZ huQ hZ'))
  obtain ⟨a₀, ha₀⟩ := hl v₀ hv₀ hv₀N
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha₀
    apply hΔ0
    have h1 := eN.map_eq_zero_iff.mp ha₀
    exact congrArg Subtype.val h1
  have hcomm : (QuotientGroup.mk m : Mbar M Q) * v₀ * (QuotientGroup.mk m : Mbar M Q)⁻¹ = v₀ := by
    have hc' : g⁻¹ * (m : G) * g ∈ hc.CN t := mem_conjSubgroup.mp hmN'
    have h1 := hZN.comm_mem huZ hc'
    have h2 : ⁅g * u * g⁻¹, (m : G)⁆ ∈ Q := by
      have h3 := hQM g hgM _ h1
      rwa [show g * ⁅u, g⁻¹ * (m : G) * g⁆ * g⁻¹ = ⁅g * u * g⁻¹, (m : G)⁆ by
        simp only [commutatorElement_def]; group] at h3
    have h4 : Commute (QuotientGroup.mk' (Q.subgroupOf M) (gm * um * gm⁻¹))
        (QuotientGroup.mk' (Q.subgroupOf M) m) :=
      (mk_commute_iff (gm * um * gm⁻¹) m).mpr h2
    rw [hv₀def]
    have h5 : (QuotientGroup.mk m : Mbar M Q) * QuotientGroup.mk (gm * um * gm⁻¹) =
        QuotientGroup.mk (gm * um * gm⁻¹) * QuotientGroup.mk m := h4.eq.symm
    show (QuotientGroup.mk m : Mbar M Q) * QuotientGroup.mk (gm * um * gm⁻¹) *
      (QuotientGroup.mk m : Mbar M Q)⁻¹ = QuotientGroup.mk (gm * um * gm⁻¹)
    rw [h5, mul_assoc, mul_inv_cancel, mul_one]
  have hAf : A *ᵥ f = f := by
    have h1 := hAz' v₀ hv₀N (by rw [hcomm]; exact hv₀N)
    have e1 : (⟨delta hS t _ (mem_bar_H0_of_CN (show (QuotientGroup.mk m : Mbar M Q) * v₀ *
        (QuotientGroup.mk m : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) by rw [hcomm]; exact hv₀N)),
        delta_mem_deltaSub hS (show (QuotientGroup.mk m : Mbar M Q) * v₀ *
        (QuotientGroup.mk m : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) by rw [hcomm]; exact hv₀N)⟩ :
        ↥(deltaSub hS t)) = ⟨delta hS t v₀ (mem_bar_H0_of_CN hv₀N), delta_mem_deltaSub hS hv₀N⟩ :=
      Subtype.ext (delta_congr hS t hcomm _ _)
    rw [e1, ha₀, map_smul, matAct_pureT] at h1
    have h2 : pureT f y = pureT (A *ᵥ f) y := by
      have h3 : a₀ • (pureT f y - pureT (A *ᵥ f) y) = 0 := by
        rw [smul_sub, sub_eq_zero]
        exact h1
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_left ha₀0)
    exact (pureT_left_injective hy h2).symm
  have hpowmem : ∀ (j : ℕ) (x : Mbar M Q), x ∈ bar M Q (hc.CN t) →
      (QuotientGroup.mk m : Mbar M Q) ^ j * x * ((QuotientGroup.mk m : Mbar M Q) ^ j)⁻¹ ∈
        bar M Q (hc.CN t) := by
    intro j x hx
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      have h1 := hzN _ ih
      rwa [show (QuotientGroup.mk m : Mbar M Q) * ((QuotientGroup.mk m : Mbar M Q) ^ j * x *
        ((QuotientGroup.mk m : Mbar M Q) ^ j)⁻¹) * (QuotientGroup.mk m : Mbar M Q)⁻¹ =
          (QuotientGroup.mk m : Mbar M Q) ^ (j + 1) * x *
            ((QuotientGroup.mk m : Mbar M Q) ^ (j + 1))⁻¹ by group] at h1
  have hpow : ∀ (j : ℕ) (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t)),
      eN ⟨delta hS t _ (mem_bar_H0_of_CN (hpowmem j x hx)),
        delta_mem_deltaSub hS (hpowmem j x hx)⟩ =
          matAct (A ^ j) (eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩) := by
    intro j
    induction j with
    | zero =>
      intro x hx
      rw [show A ^ 0 = 1 from pow_zero A, matAct_one]
      congr 2
      exact delta_congr hS t (by group) _ _
    | succ j ih =>
      intro x hx
      have e1 : (QuotientGroup.mk m : Mbar M Q) ^ (j + 1) * x *
          ((QuotientGroup.mk m : Mbar M Q) ^ (j + 1))⁻¹ =
          (QuotientGroup.mk m : Mbar M Q) * ((QuotientGroup.mk m : Mbar M Q) ^ j * x *
            ((QuotientGroup.mk m : Mbar M Q) ^ j)⁻¹) * (QuotientGroup.mk m : Mbar M Q)⁻¹ := by
        group
      have h1 := hAz' _ (hpowmem j x hx) (by rw [← e1]; exact hpowmem (j + 1) x hx)
      rw [ih x hx] at h1
      rw [pow_succ' A j, matAct_mul, ← h1]
      congr 2
      exact delta_congr hS t e1 _ _
  have hAk : A ^ 2 ^ k = 1 := by
    obtain ⟨m₀, hm₀⟩ : ∃ m₀ : L₄, m₀ ≠ 0 := by
      have hpos : 0 < finrank K L₄ := by rw [D.finrank₄]; norm_num
      haveI : Nontrivial L₄ := Module.nontrivial_of_finrank_pos hpos
      exact exists_ne 0
    refine matAct_injective hm₀ fun X => ?_
    obtain ⟨x, hx, hxF⟩ := hSΔ _ (eN.symm X).2
    have hX : eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ = X := by
      rw [show (⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ :
        ↥(deltaSub hS t)) = eN.symm X from Subtype.ext hxF.symm, LinearEquiv.apply_symm_apply]
    have h1 := hpow (2 ^ k) x hx
    have hk' : (QuotientGroup.mk m : Mbar M Q) ^ 2 ^ k = 1 := by
      rw [show (QuotientGroup.mk m : Mbar M Q) ^ 2 ^ k = QuotientGroup.mk (m ^ 2 ^ k) from
        (map_pow (QuotientGroup.mk' (Q.subgroupOf M)) m _).symm]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      rw [SubmonoidClass.coe_pow, hk]
      exact Q.one_mem
    have e2 : (⟨delta hS t _ (mem_bar_H0_of_CN (hpowmem (2 ^ k) x hx)),
        delta_mem_deltaSub hS (hpowmem (2 ^ k) x hx)⟩ : ↥(deltaSub hS t)) =
        ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ :=
      Subtype.ext (delta_congr hS t (by rw [hk']; group) _ _)
    rw [e2, hX] at h1
    rw [matAct_one]
    exact h1.symm
  have hnil : (A - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute 2 k (Commute.one_right A), hAk, one_pow, sub_self]
  obtain ⟨-, s, hs⟩ := eq_one_add_smul_rootN hf (show A *ᵥ f = (1 : K) • f by rw [one_smul, hAf])
    hnil
  refine ⟨s, fun x hx hzx => ?_⟩
  rw [hAz' x hx hzx, hs, matAct_add, matAct_one, matAct_smul]

end Nbr

theorem delta_conj_of_mem_CN (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {c : Mbar M Q} (hcN : c ∈ bar M Q (hc.CN t)) {m : Mbar M Q}
    (hm : m ∈ bar M Q (hc.CN t)) (hcm : c * m * c⁻¹ ∈ bar M Q (hc.CN t)) :
    delta hS t (c * m * c⁻¹) (mem_bar_H0_of_CN hcm) = delta hS t m (mem_bar_H0_of_CN hm) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hcR : c ∈ bar M Q (Rt M (LB M Q B) t) := bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) hcN
  have h1 := deltaAct_delta hS ht ⟨c, hcR⟩ hm
  rw [deltaAct_of_mem_CN h310chi h52a hS hs hr ⟨c, hcR⟩ hcN] at h1
  exact (congrArg Subtype.val h1).symm

theorem ActsAsRoot.delta_eq {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₄ : Type}
    [AddCommGroup L₄] [Module K L₄] {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)} {f : Fin 2 → K}
    {zb : Mbar M Q} (h : ActsAsRoot hS t eN f zb 0) {x : Mbar M Q} (hx : x ∈ bar M Q (hc.CN t))
    (hzx : zb * x * zb⁻¹ ∈ bar M Q (hc.CN t)) :
    delta hS t (zb * x * zb⁻¹) (mem_bar_H0_of_CN hzx) = delta hS t x (mem_bar_H0_of_CN hx) := by
  have h1 := h x hx hzx
  rw [zero_smul, add_zero] at h1
  exact congrArg Subtype.val (eN.injective h1)



section Sigma

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.exists_card_zStar (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement)
    (hY : Sec713YStatement) (hCent : Sec715CentStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (hp : OmegaPlusNat hc t 4) (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    (hMat : MatActProp hS t eN Z0)
    (hNormFix : ∀ (z : G) (hzH : z ∈ H0 M Z),
      (∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk (⟨z, hzH.1⟩ : ↥M))).toAdd e = e) →
        z ∈ NormH0 M Z Z0)
    {g : G} (hg : IsSymNbr hc t Z0 g) {f : Fin 2 → K} {y : L₄} (hf : f ≠ 0) (hy : y ≠ 0)
    (hl : HasLine hS t eN Z0 g f y) :
    ∃ R : Subgroup (Multiplicative K),
      Nat.card (zStar hS t g) =
        Nat.card ↥(bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t))) * Nat.card R ∧
      ∀ s : K, Multiplicative.ofAdd s ∈ R → ∃ zb ∈ zStar hS t g, ActsAsRoot hS t eN f zb s := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hex := fun (zb : Mbar M Q) (hzb : zb ∈ zStar hS t g) =>
    D.exists_actsAsRoot h34 h310chi h51 h52a hA hZt hZcard hCRW hMp hs hr hZ0 hZN hTI hSΔ hMat
      hNormFix hg hf hy hl hzb
  let sp : ↥(zStar hS t g) → K := fun zb => Classical.choose (hex zb zb.2).2.2
  have hsp : ∀ zb : ↥(zStar hS t g), ActsAsRoot hS t eN f zb (sp zb) := fun zb =>
    Classical.choose_spec (hex zb zb.2).2.2
  have huniq : ∀ (zb : ↥(zStar hS t g)) (s : K), ActsAsRoot hS t eN f zb s → sp zb = s :=
    fun zb s h => D.actsAsRoot_unique hs hSΔ hf (hex zb zb.2).2.1 (hsp zb) h
  have hsp1 : sp 1 = 0 := by
    refine huniq 1 0 fun x hx hzx => ?_
    rw [zero_smul, add_zero]
    congr 1
    exact Subtype.ext (delta_congr hS t (by simp) _ _)
  have hspmul : ∀ zb zb' : ↥(zStar hS t g), sp (zb * zb') = sp zb + sp zb' := by
    intro zb zb'
    refine huniq _ _ fun x hx hzx => ?_
    have hN' := (hex zb' zb'.2).2.1
    have hN := (hex zb zb.2).2.1
    have hx' := hN' x hx
    have e1 : ((zb * zb' : ↥(zStar hS t g)) : Mbar M Q) * x *
        ((zb * zb' : ↥(zStar hS t g)) : Mbar M Q)⁻¹ =
        (zb : Mbar M Q) * ((zb' : Mbar M Q) * x * (zb' : Mbar M Q)⁻¹) * (zb : Mbar M Q)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    have e2 : (⟨delta hS t _ (mem_bar_H0_of_CN hzx), delta_mem_deltaSub hS hzx⟩ :
        ↥(deltaSub hS t)) = ⟨delta hS t _ (mem_bar_H0_of_CN (hN _ hx')),
          delta_mem_deltaSub hS (hN _ hx')⟩ := Subtype.ext (delta_congr hS t e1 _ _)
    rw [e2, hsp zb _ hx' (hN _ hx'), hsp zb' x hx hx', map_add, map_smul, ← matAct_mul,
      rootN_mul_self, matAct_zero, smul_zero, add_zero, add_smul]
    abel
  let σ : ↥(zStar hS t g) →* Multiplicative K :=
    { toFun := fun zb => Multiplicative.ofAdd (sp zb)
      map_one' := by rw [hsp1]; rfl
      map_mul' := fun zb zb' => by rw [hspmul]; rfl }
  refine ⟨σ.range, ?_, fun s hs' => ?_⟩
  ·
    set Λb := bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t)) with hΛb
    have hΛZ : Λb ≤ zStar hS t g := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, fun e he => ?_⟩
      obtain ⟨hxV, -, -⟩ := dmap_CN_facts h310chi h52a hS hs hr (Subgroup.mem_inf.mp hx).1
      rw [act_eq_add_dmap, hxV e he, add_zero]
    have hker : σ.ker = Λb.subgroupOf (zStar hS t g) := by
      ext zb
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hΛb, Subgroup.mem_inf]
      have hzbN' := (Subgroup.mem_inf.mp zb.2).1
      constructor
      · intro h1
        have h0 : sp zb = 0 := congrArg Multiplicative.toAdd h1
        have hact : ActsAsRoot hS t eN f zb 0 := h0 ▸ hsp zb
        obtain ⟨⟨z, hzK, hzeq, hzR, k, hk⟩, hzN, -⟩ := hex zb zb.2
        refine ⟨?_, hzbN'⟩
        rw [← hzeq] at hzN hact ⊢
        set zm : ↥M := ⟨z, hzK.1.1⟩ with hzm
        have hxN : ∀ m ∈ hc.CN t, ⁅z, m⁆ ∈ Z0 := by
          intro m hm
          have hmM : m ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hm).1
          let mm : ↥M := ⟨m, hmM⟩
          have hmb : (QuotientGroup.mk mm : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar mm hm
          have hfix := hact.delta_eq hmb (hzN _ hmb)
          have hinvN : (QuotientGroup.mk mm : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t) :=
            (bar M Q (hc.CN t)).inv_mem hmb
          have hd1 := delta_mul h310chi h52a hS hs hr (hzN _ hmb) hinvN
          have hd2 := delta_mul h310chi h52a hS hs hr hmb hinvN
          have hR : ⁅QuotientGroup.mk' (Q.subgroupOf M) zm, (QuotientGroup.mk mm : Mbar M Q)⁆ ∈
              bar M Q (Rt M (LB M Q B) t) :=
            bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) ((bar M Q (hc.CN t)).mul_mem
              (hzN _ hmb) hinvN)
          have h0' : delta hS t ⁅QuotientGroup.mk' (Q.subgroupOf M) zm,
              (QuotientGroup.mk mm : Mbar M Q)⁆ (mem_bar_H0_of_Rt hc hR) = 0 := by
            rw [delta_congr hS t (commutatorElement_def _ _) _
              (Subgroup.mul_mem _ (mem_bar_H0_of_CN (hzN _ hmb)) (mem_bar_H0_of_CN hinvN)),
              hd1, hfix, ← hd2, delta_congr hS t (mul_inv_cancel _) _ (Subgroup.one_mem _)]
            refine LinearMap.ext fun w => ?_
            rw [delta_apply, dmap_one, LinearMap.zero_apply]
          have hZb := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mp h0'
          rw [show ⁅QuotientGroup.mk' (Q.subgroupOf M) zm, (QuotientGroup.mk mm : Mbar M Q)⁆ =
            QuotientGroup.mk ⁅zm, mm⁆ from
            (map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) zm mm).symm] at hZb
          exact (mk_mem_bar_iff_sec4 hQZ0 ⁅zm, mm⁆).mp hZb
        have hzCN := mem_CN_of_comm_le h34 h310chi h51 hA hZt hZcard hZc hZV hCommN hY hCent hc
          hs hp hZ0 hZN hzK ⟨k, hk⟩ hxN hzR
        exact mk_mem_bar ⟨z, hzK.1.1⟩ hzCN
      · rintro ⟨hzbN, -⟩
        show Multiplicative.ofAdd (sp zb) = 1
        rw [huniq zb 0 fun x hx hzx => by
          rw [zero_smul, add_zero]
          congr 1
          exact Subtype.ext (delta_conj_of_mem_CN h310chi h52a hS hs hr hzbN hx hzx)]
        rfl
    have h1 := Subgroup.card_ker_mul_card_range σ
    rw [hker] at h1
    rw [← h1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛZ).toEquiv
  · obtain ⟨zb, hzb⟩ := hs'
    refine ⟨zb, zb.2, ?_⟩
    have h1 : sp zb = s := congrArg Multiplicative.toAdd hzb
    rw [← h1]
    exact hsp zb

end Sigma

end CFSG.RankThree.GF2n.Stroth80.S715L
