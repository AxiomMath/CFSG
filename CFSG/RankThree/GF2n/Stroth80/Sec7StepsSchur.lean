module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_Rt_eq_comm_mul_CN [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) :
    ∀ r ∈ Rt M (LB M Q B) t, ∃ a ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆,
      ∃ k ∈ hc.CN t, r = a * k := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨S, hS, π, hπs, hπk, hSs, h16, -⟩ := endg_quot_facts hc hs (a := Nat.card Z) rfl
  have hQC : Q ≤ hc.CN t := fun y hy =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hy, fun v hv => hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩
  let incl : ↥(Rt M (LB M Q B) t) →* ↥M := Subgroup.inclusion (hc.Rt_le_M t)
  let g0 : ↥(Rt M (LB M Q B) t) →* Mbar M Q := (QuotientGroup.mk' (Q.subgroupOf M)).comp incl
  have hg0 : ∀ r, g0 r ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨incl r, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  let g1 : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) := g0.codRestrict _ hg0
  let f : ↥(Rt M (LB M Q B) t) →* S := π.comp g1
  have hg1s : Function.Surjective g1 := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext rfl⟩
  have hfs : Function.Surjective f := hπs.comp hg1s
  have hfker : ∀ r, f r = 1 → (r : G) ∈ hc.CN t := by
    intro r hr
    exact (mk_mem_bar_iff_sec4 hQC (incl r)).mp ((hπk (g1 r)).mp hr)
  have hSperf : commutator S = ⊤ := by
    rcases hSs.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      haveI : IsMulCommutative S := ⟨⟨fun a b => by
        have h1 : ⁅a, b⁆ ∈ commutator S := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)⟩⟩
      have hprime := Group.is_simple_iff_prime_card.mp hSs
      rcases Nat.Prime.eq_one_or_self_of_dvd hprime 16 h16 with h' | h'
      · omega
      · rw [← h'] at hprime
        norm_num at hprime
    · exact h
  have hmap : (commutator ↥(Rt M (LB M Q B) t)).map f = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hfs,
      ← commutator_def]
    exact hSperf
  intro r hr
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ commutator ↥(Rt M (LB M Q B) t), f a = f ⟨r, hr⟩ := by
    have : f ⟨r, hr⟩ ∈ (commutator ↥(Rt M (LB M Q B) t)).map f := by
      rw [hmap]
      exact Subgroup.mem_top _
    exact Subgroup.mem_map.mp this
  have hk : f (a⁻¹ * ⟨r, hr⟩) = 1 := by rw [map_mul, map_inv, hfa, inv_mul_cancel]
  refine ⟨(a : G), ?_, ((a⁻¹ * ⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) : G), hfker _ hk, by simp⟩
  have := Subgroup.mem_map_of_mem (Rt M (LB M Q B) t).subtype ha
  rwa [Subgroup.map_subtype_commutator] at this

theorem sec7Schur_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hzcard : Sec7ZCardStatement) :
    Sec7SchurStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 w hwH hwR hwW
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQc : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, hsemi, hρinj, ψ, hψ, hkerW, hA, hSchur⟩ :=
    sec7_linModelData h34 h310chi hc hs hZ0
      (fun z hz w hw => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).2 w hw)
      (fun u hu huQ => hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ)
  have hwM : w ∈ M := hwH.1
  let wm : ↥M := ⟨w, hwM⟩
  have hwbH : (QuotientGroup.mk wm : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨wm, Subgroup.mem_subgroupOf.mpr hwH, rfl⟩
  let T : M₀.E ≃ₗ[K] M₀.E :=
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk wm)).toAdd (hS.lin _ hwbH)
  let φ : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) - 1
  have hφ : ∀ e, φ e = (ρ (QuotientGroup.mk wm)).toAdd e - e := fun e => rfl
  have hφW : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), φ (M₀.π x) = 0 := by
    intro x hx
    have h1 : M₀.π (w * x * w⁻¹) = M₀.π x :=
      (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hx.1 (hQc w hwM x hx.1)).mp (hwW x hx)
    rw [hφ, ← hS.conj wm x hx.1]
    exact sub_eq_zero.mpr h1
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro e he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    exact LinearMap.mem_ker.mpr (hφW x (hkerW x hxQ (LinearMap.mem_ker.mp he)))
  have hrefl : M₀.B.IsRefl := fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hnd : M₀.B.Nondegenerate :=
    ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  have hφP : LinearMap.range φ ≤ hc.VtSub hS.model t := by
    rintro _ ⟨e, rfl⟩
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl (hc.VtSub hS.model t),
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have huW : u ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := by
      refine (mem_img_Wt_iff M₀ hS.model.reg (hc.Vt_le_Q t)).mpr fun v hv => ?_
      have h0 : M₀.B v u = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) v ((hc.mem_VtSub hS.model t).mpr hv)
      rw [Tim79.QuadModel.B_comm, h0, neg_zero]
    obtain ⟨x, hxW, hxQ, rfl⟩ := huW
    have hfix : (ρ (QuotientGroup.mk wm)).toAdd (M₀.π x) = M₀.π x := by
      have := hφW x hxW
      rw [hφ] at this
      exact sub_eq_zero.mp this
    have h1 := hS.iso _ hwbH (M₀.π x) e
    rw [hfix] at h1
    show M₀.B (M₀.π x) (φ e) = 0
    rw [hφ, map_sub, h1, sub_self]
  have hφcomm : ∀ c : Mbar M Q, (QuotientGroup.mk wm : Mbar M Q) * c = c * QuotientGroup.mk wm →
      ∀ e, φ ((ρ c).toAdd e) = (ρ c).toAdd (φ e) := by
    intro c hcc e
    rw [hφ, hφ, map_sub, ← act_mul_apply, ← act_mul_apply, hcc]
  have hφN : ∀ k ∈ hc.CN t, ∀ (hkM : k ∈ M) (e : M₀.E),
      φ ((ρ (QuotientGroup.mk (⟨k, hkM⟩ : ↥M))).toAdd e) = φ e := by
    intro k hk hkM e
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    obtain ⟨hkR, hkV⟩ := Ctx.mem_CN.mp hk
    have hkH : k ∈ H0 M Z := hc.Rt_le_H0 t hkR
    have hcU : ⁅y, k⁆ ∈ Ut Q Z k := comm_mem_Ut hyQ
    have hcW : ⁅y, k⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
      Ut_le_Wt_of_vanish hc (hc.Vt_le_Q t) hkH hkV hcU
    have hcQ : ⁅y, k⁆ ∈ Q := hcW.1
    have hcQ' : ⁅k, y⁆ ∈ Q := by
      have := Q.inv_mem hcQ
      rwa [commutatorElement_inv] at this
    have hcW' : ⁅k, y⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have := (Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hcW
      rwa [commutatorElement_inv] at this
    have e1 : k * y * k⁻¹ = ⁅k, y⁆ * y := by rw [commutatorElement_def]; group
    have h2 : (ρ (QuotientGroup.mk (⟨k, hkM⟩ : ↥M))).toAdd (M₀.π y) =
        M₀.π ⁅k, y⁆ + M₀.π y := by
      have := hS.conj ⟨k, hkM⟩ y hyQ
      rw [← this, e1, M₀.π_mul _ hcQ' y hyQ]
    rw [h2, map_add, hφW _ hcW', zero_add]
  have hφS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
      φ ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (φ e) := by
    intro x e
    obtain ⟨xx, hxx, hx⟩ := Subgroup.mem_map.mp x.2
    have hxR : (xx : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hxx
    obtain ⟨a, ha, k, hk, hxe⟩ := sec7_Rt_eq_comm_mul_CN hc hs _ hxR
    have haM : a ∈ M := hc.Rt_le_M t (Subgroup.commutator_le_self _ ha)
    have hkM : k ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hk).1
    have hxeq : (x : Mbar M Q) = QuotientGroup.mk (⟨a, haM⟩ : ↥M) *
        QuotientGroup.mk (⟨k, hkM⟩ : ↥M) := by
      rw [← hx]
      show (QuotientGroup.mk xx : Mbar M Q) = _
      rw [← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hxe
    have hkV : ∀ v ∈ hc.VtSub hS.model t,
        (ρ (QuotientGroup.mk (⟨k, hkM⟩ : ↥M))).toAdd v = v := by
      intro v hv
      refine hc.act_CN hS ht _ ?_ v hv
      exact (mk_mem_bar_iff_sec4 (fun y hy => Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hy, fun v hv =>
        hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩) ⟨k, hkM⟩).mpr hk
    have hacomm := hφcomm (QuotientGroup.mk (⟨a, haM⟩ : ↥M))
      ((mk_commute_iff wm ⟨a, haM⟩).mpr (hwR a ha)).eq
    rw [hxeq, act_mul_apply, act_mul_apply, hacomm, hφN k hk hkM e,
      hkV _ (hφP (LinearMap.mem_range_self φ e))]
  obtain ⟨c, hc'⟩ := hSchur φ hker hφP hφS
  have hcardA : Nat.card (bar M Q Z0) = Nat.card K := by
    have h1 := bar_card_mul_card_of_le (M := M) hQZ0 hZ0M
    rw [hzcard G M Q Z B hc n t hs Z0 hZ0] at h1
    have h2 : Nat.card (bar M Q Z0) * Nat.card Q = Nat.card Z * Nat.card Q := by
      rw [h1, mul_comm]
    rw [hS.card]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  let cf : ↥(bar M Q Z0) → K := fun a => Classical.choose (hA a a.2)
  have hcf : ∀ a : ↥(bar M Q Z0), ∀ e, (ρ (a : Mbar M Q)).toAdd e = e + cf a • ψ e :=
    fun a => Classical.choose_spec (hA a a.2)
  have hcfinj : Function.Injective cf := by
    intro a a' h
    apply Subtype.ext
    apply hρinj
    intro e
    rw [hcf a e, hcf a' e, h]
  have hbij : Function.Bijective cf := hcfinj.bijective_of_nat_card_le (by rw [hcardA])
  obtain ⟨a, ha⟩ := hbij.2 c
  have hwa : (QuotientGroup.mk wm : Mbar M Q) = (a : Mbar M Q) := by
    apply hρinj
    intro e
    have h1 : (ρ (QuotientGroup.mk wm)).toAdd e = e + φ e := by rw [hφ]; abel
    rw [h1, hc' e, hcf a e, ha]
  have hmem : (QuotientGroup.mk' (Q.subgroupOf M) wm : Mbar M Q) ∈ bar M Q Z0 := by
    have : (QuotientGroup.mk wm : Mbar M Q) ∈ bar M Q Z0 := hwa ▸ a.2
    exact this
  exact (mk_mem_bar_iff_sec4 hQZ0 wm).mp hmem

end CFSG.RankThree.GF2n.Stroth80
