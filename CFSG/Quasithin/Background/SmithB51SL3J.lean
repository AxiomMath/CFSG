module

public import CFSG.Quasithin.Background.SmithB51SL3I
public import CFSG.Quasithin.Background.SmithB51SL3H

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section Split

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem NatSec.f_injective {W : Subgroup V} (c : NatSec L W ⊥ K) : Function.Injective c.f := by
  rw [injective_iff_map_eq_one]
  intro w hw
  exact Subtype.ext ((c.hfk w).1 hw)

theorem NatSec.toAdd_f_of_levi {W U : Subgroup V} (c : NatSec L W U K) (hLW : L ≤ stabSub W)
    (w : ↥W) (hw : ∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) w = w) :
    Multiplicative.toAdd (c.f w) = Pi.single 2 (Multiplicative.toAdd (c.f w) 2) := by
  apply eq_single_of_levi_fix
  intro γ hγ
  have hw' : ((c.π γ : ↥L) : MulAut V) w ∈ W := ((hLW (c.π γ).2) w).2 w.2
  have h1 := c.hfe γ w hw'
  have h2 : (⟨_, hw'⟩ : ↥W) = w := Subtype.ext (hw γ hγ)
  rw [h2] at h1
  exact (congrArg Multiplicative.toAdd h1).symm

omit [Field K] in
theorem smul_sub_single_two {K : Type} [Field K] (k : K) (w : Fin 3 → K) :
    k • w - Pi.single 2 ((k • w) 2) = k • (w - Pi.single 2 (w 2)) := by
  rw [smul_sub, Pi.smul_apply, smul_eq_mul, ← smul_eq_mul, Pi.single_smul]

theorem exists_good_lift {W I : Subgroup V} (hIW : I ≤ W) (hLW : L ≤ stabSub W)
    (hLI : L ≤ stabSub I) (e₁ : NatSec L I ⊥ K) (c : NatSec L W I K) (hπ : c.π = e₁.π)
    {A : Subgroup (MulAut V)} (hA : ∀ w : Fin 3 → K, ((c.π (xQ w) : ↥L) : MulAut V) ∈ A)
    (hquad : IsQuadratic A) (v₀ : ↥W) (hv₀ : ∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) v₀ = v₀)
    (hfv₀ : Multiplicative.toAdd (c.f v₀) = Pi.single 2 1)
    (hlevi : ∀ k : K, ∃ v₁ : ↥W, (∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) v₁ = v₁) ∧
      Multiplicative.toAdd (c.f v₁) = Pi.single 2 k) (k : K) :
    ∃ v : ↥W, (∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) v = v) ∧
      Multiplicative.toAdd (c.f v) = Pi.single 2 k ∧
      ∀ w : Fin 3 → K, w 2 = 0 → qc c.π v w = qc c.π v₀ (k • w) := by
  obtain ⟨v₁, hv₁, hfv₁⟩ := hlevi k
  set d : (Fin 3 → K) → V := fun w => qc c.π v₁ w * (qc c.π v₀ (k • w))⁻¹ with hd
  have hdW : ∀ w, d w ∈ W := fun w =>
    W.mul_mem (c.qc_mem hLW v₁ w) (W.inv_mem (c.qc_mem hLW v₀ (k • w)))
  have hdI : ∀ w, d w ∈ I := by
    intro w
    rw [← c.hfk ⟨d w, hdW w⟩]
    have e1 : (⟨d w, hdW w⟩ : ↥W) = ⟨_, c.qc_mem hLW v₁ w⟩ * ⟨_, c.qc_mem hLW v₀ (k • w)⟩⁻¹ :=
      rfl
    rw [e1, map_mul, map_inv, mul_inv_eq_one]
    apply Multiplicative.toAdd.injective
    rw [c.toAdd_f_qc hLW, c.toAdd_f_qc hLW, hfv₁, hfv₀, Pi.single_eq_same, Pi.single_eq_same,
      one_smul, smul_sub_single_two]
  set ψ : (Fin 3 → K) → (Fin 3 → K) := fun w => Multiplicative.toAdd (e₁.f ⟨d w, hdI w⟩) with hψ
  have hdadd : ∀ w w', d (w + w') = d w * d w' := by
    intro w w'
    simp only [hd]
    rw [qc_add hA hquad, smul_add, qc_add hA hquad, mul_inv]
    ac_rfl
  have hψadd : ∀ w w', ψ (w + w') = ψ w + ψ w' := by
    intro w w'
    have e1 : (⟨d (w + w'), hdI _⟩ : ↥I) = ⟨d w, hdI w⟩ * ⟨d w', hdI w'⟩ :=
      Subtype.ext (hdadd w w')
    simp only [hψ]
    rw [e1, map_mul, toAdd_mul]
  have hdlevi : ∀ g ∈ levi K, ∀ w, ((c.π g : ↥L) : MulAut V) (d w) = d (slAct g w) := by
    intro g hg w
    simp only [hd]
    rw [map_mul, map_inv, qc_levi c.π hg (hv₁ g hg), qc_levi c.π hg (hv₀ g hg), slAct_smul]
  have hψcomm : ∀ g ∈ levi K, ∀ w, ψ (slAct g w) = slAct g (ψ w) := by
    intro g hg w
    have hmem : ((e₁.π g : ↥L) : MulAut V) (d w) ∈ I := ((hLI (e₁.π g).2) _).2 (hdI w)
    have h1 := e₁.hfe g ⟨d w, hdI w⟩ hmem
    have h2 : (⟨_, hmem⟩ : ↥I) = ⟨d (slAct g w), hdI _⟩ := by
      apply Subtype.ext
      show ((e₁.π g : ↥L) : MulAut V) (d w) = d (slAct g w)
      rw [← hπ]
      exact hdlevi g hg w
    rw [h2] at h1
    simp only [hψ]
    rw [h1]
    rfl
  obtain ⟨a, ha⟩ := exists_smul_of_levi (fun w w' _ _ => hψadd w w')
    (fun g hg w _ => hψcomm g hg w)
  obtain ⟨t, ht⟩ := e₁.hfs (Multiplicative.ofAdd (Pi.single 2 a))
  have htfix : ∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) t = t := by
    intro γ hγ
    have hmem : ((e₁.π γ : ↥L) : MulAut V) t ∈ I := ((hLI (e₁.π γ).2) _).2 t.2
    have h1 := e₁.hfe γ t hmem
    rw [ht] at h1
    have h2 : e₁.f ⟨_, hmem⟩ = e₁.f t := by
      rw [h1, ht]
      apply Multiplicative.toAdd.injective
      exact slAct_single_two hγ a
    have h3 := congrArg Subtype.val (e₁.f_injective h2)
    rw [hπ]
    exact h3
  have hqct : ∀ w (h : qc c.π t w ∈ I),
      Multiplicative.toAdd (e₁.f ⟨qc c.π t w, h⟩) = a • (w - Pi.single 2 (w 2)) := by
    intro w h
    have h1 := e₁.toAdd_f_qc hLI t w
    rw [ht, toAdd_ofAdd, Pi.single_eq_same] at h1
    have e : (⟨qc c.π t w, h⟩ : ↥I) = ⟨qc e₁.π t w, e₁.qc_mem hLI t w⟩ := by
      apply Subtype.ext
      show qc c.π t w = qc e₁.π t w
      rw [hπ]
    rw [e, h1]
  have hvW : (v₁ : V) * (t : V)⁻¹ ∈ W := W.mul_mem v₁.2 (W.inv_mem (hIW t.2))
  refine ⟨⟨_, hvW⟩, fun γ hγ => ?_, ?_, fun w hw => ?_⟩
  · show ((c.π γ : ↥L) : MulAut V) ((v₁ : V) * (t : V)⁻¹) = (v₁ : V) * (t : V)⁻¹
    rw [map_mul, map_inv, hv₁ γ hγ, htfix γ hγ]
  · have htW : c.f ⟨t, hIW t.2⟩ = 1 := (c.hfk _).2 t.2
    have e1 : (⟨_, hvW⟩ : ↥W) = v₁ * ⟨t, hIW t.2⟩⁻¹ := rfl
    rw [e1, map_mul, map_inv, htW, inv_one, mul_one, hfv₁]
  ·
    have htI : qc c.π t w ∈ I := by rw [hπ]; exact e₁.qc_mem hLI t w
    have hzero : d w * (qc c.π t w)⁻¹ = 1 := by
      have hmem : d w * (qc c.π t w)⁻¹ ∈ I := I.mul_mem (hdI w) (I.inv_mem htI)
      have e1 : (⟨_, hmem⟩ : ↥I) = ⟨d w, hdI w⟩ * ⟨_, htI⟩⁻¹ := rfl
      have h1 : e₁.f ⟨_, hmem⟩ = 1 := by
        rw [e1, map_mul, map_inv, mul_inv_eq_one]
        apply Multiplicative.toAdd.injective
        have h2 := ha w hw
        have h3 := hqct w htI
        rw [hw, Pi.single_zero, sub_zero] at h3
        exact h2.trans h3.symm
      exact (e₁.hfk _).1 h1
    show qc c.π ((v₁ : V) * (t : V)⁻¹) w = qc c.π v₀ (k • w)
    rw [qc_mul, qc_inv]
    calc qc c.π v₁ w * (qc c.π t w)⁻¹
        = (d w * (qc c.π t w)⁻¹) * qc c.π v₀ (k • w) := by
          simp only [hd]
          rw [mul_right_comm (qc c.π v₁ w * (qc c.π v₀ (k • w))⁻¹) (qc c.π t w)⁻¹
            (qc c.π v₀ (k • w)), inv_mul_cancel_right]
      _ = qc c.π v₀ (k • w) := by rw [hzero, one_mul]

end Split

section Main

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem sq_eq_one_vec (s : Multiplicative (Fin 3 → K)) : s ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, two_nsmul, toAdd_one, Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]

theorem exists_equivariant_section (hV : ∀ v : V, v ^ 2 = 1) {W I : Subgroup V} (hIW : I ≤ W)
    (hLW : L ≤ stabSub W) (hLI : L ≤ stabSub I) (e₁ : NatSec L I ⊥ K) (c : NatSec L W I K)
    (hπ : c.π = e₁.π) {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hquad : IsQuadratic A)
    (hpre : c.pre A = axisSub (stdAxis K))
    (hlift : ∀ u ∈ W, (∀ a ∈ A, a u * u⁻¹ ∈ I) → ∃ u' ∈ W, u' ∈ fixV A ∧ u' * u⁻¹ ∈ I)
    (hq : 2 ∣ Nat.card K) :
    ∃ σ : Multiplicative (Fin 3 → K) →* ↥W, (∀ s, c.f (σ s) = s) ∧
      ∀ (γ : ↥(StatedSL 3 K)) (s : Multiplicative (Fin 3 → K)),
        ((c.π γ : ↥L) : MulAut V) (σ s) = σ (natAct (StatedSL 3 K) γ s) := by
  classical
  have hA : ∀ w : Fin 3 → K, ((c.π (xQ w) : ↥L) : MulAut V) ∈ A := by
    intro w
    have : xQ w ∈ c.pre A := by rw [hpre]; exact xQ_mem w
    exact this
  obtain ⟨σL, hσL⟩ := c.exists_levi_lift hV hLW hAL hpre hlift hq
  set v₀ : ↥W := σL (Multiplicative.ofAdd 1) with hv₀def
  have hv₀ := (hσL 1).1
  have hfv₀ := (hσL 1).2
  have hgood := exists_good_lift hIW hLW hLI e₁ c hπ hA hquad v₀ hv₀ hfv₀
    (fun k => ⟨σL (Multiplicative.ofAdd k), hσL k⟩)
  set X₀ := qcRange hA hquad (v₀ : V) with hX₀
  have hX₀W : X₀ ≤ W := by
    rintro _ ⟨w, rfl⟩
    exact c.qc_mem hLW v₀ w
  have hX₀A : X₀ ≤ fixV A := by
    rintro _ ⟨w, rfl⟩
    exact qc_mem_fixV hA hquad _ w
  have hX₀f : ∀ w, Multiplicative.toAdd (c.f ⟨qc c.π v₀ w, c.qc_mem hLW v₀ w⟩) =
      w - Pi.single 2 (w 2) := by
    intro w
    rw [c.toAdd_f_qc hLW, hfv₀, Pi.single_eq_same, one_smul]
  set V₀ := leviLifts c.π W X₀ with hV₀
  have hV₀W : V₀ ≤ W := fun v hv => hv.1
  have hV₀s : ∀ k : K, ∃ v : ↥W, (v : V) ∈ V₀ ∧
      Multiplicative.toAdd (c.f v) = Pi.single 2 k := by
    intro k
    obtain ⟨v, hvf, hfv, hvq⟩ := hgood k
    exact ⟨v, ⟨v.2, hvf, fun w hw => by rw [hvq w hw]; exact ⟨_, rfl⟩⟩, hfv⟩
  have hX₀I : ∀ w, c.f ⟨qc c.π v₀ w, c.qc_mem hLW v₀ w⟩ = 1 → qc c.π v₀ w = 1 := by
    intro w h
    have h1 := hX₀f w
    rw [h, toAdd_one] at h1
    unfold qc
    rw [xQ_eq_one h1.symm, map_one, Subgroup.coe_one, MulAut.one_apply, mul_inv_cancel]
  have hlevicoord : ∀ v : ↥W, (v : V) ∈ V₀ →
      Multiplicative.toAdd (c.f v) = Pi.single 2 (Multiplicative.toAdd (c.f v) 2) :=
    fun v hv => c.toAdd_f_of_levi hLW v hv.2.1
  have hV₀I : ∀ v : ↥W, (v : V) ∈ V₀ → c.f v = 1 → (v : V) = 1 := by
    intro v hv hfv
    have hvI : (v : V) ∈ I := (c.hfk v).1 hfv
    have hlev : ∀ γ ∈ levi K, ((e₁.π γ : ↥L) : MulAut V) (v : V) = v := by
      intro γ hγ
      rw [← hπ]
      exact hv.2.1 γ hγ
    have h1 := e₁.toAdd_f_of_levi hLI ⟨v, hvI⟩ hlev
    obtain ⟨w, hw⟩ := hv.2.2 (Pi.single 0 1) (by simp)
    have hqI : qc c.π v (Pi.single 0 1) ∈ I := by
      rw [hπ]
      exact e₁.qc_mem hLI ⟨v, hvI⟩ _
    have hq1 : qc c.π v (Pi.single 0 1) = 1 := by
      rw [← hw]
      apply hX₀I
      apply (c.hfk _).2
      show qc c.π v₀ w ∈ I
      rw [hw]
      exact hqI
    have h2 := e₁.toAdd_f_qc hLI ⟨v, hvI⟩ (Pi.single 0 1)
    have e2 : (⟨qc e₁.π v (Pi.single 0 1), e₁.qc_mem hLI ⟨v, hvI⟩ _⟩ : ↥I) = 1 := by
      apply Subtype.ext
      show qc e₁.π v (Pi.single 0 1) = 1
      rw [← hπ]
      exact hq1
    rw [e2, map_one, toAdd_one] at h2
    have h3 := congrFun h2 0
    simp at h3
    have h4 : e₁.f ⟨v, hvI⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h1, ← h3, Pi.single_zero, toAdd_one]
    exact (e₁.hfk _).1 h4
  set J := V₀ ⊔ X₀ with hJ
  have hJW : J ≤ W := sup_le hV₀W hX₀W
  set fJ : ↥J →* Multiplicative (Fin 3 → K) := c.f.comp (Subgroup.inclusion hJW) with hfJ
  have hfJ_apply : ∀ j : ↥J, fJ j = c.f ⟨j, hJW j.2⟩ := fun _ => rfl
  have hJinj : Function.Injective fJ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    obtain ⟨v, hv, x, ⟨w, rfl⟩, hvx⟩ := Subgroup.mem_sup.1 j.2
    have hvW : v ∈ W := hv.1
    have e1 : (⟨j, hJW j.2⟩ : ↥W) = ⟨v, hvW⟩ * ⟨qc c.π v₀ w, c.qc_mem hLW v₀ w⟩ :=
      Subtype.ext hvx.symm
    rw [hfJ_apply, e1, map_mul] at hj
    have h1 := congrArg Multiplicative.toAdd hj
    rw [toAdd_mul, toAdd_one, hlevicoord ⟨v, hvW⟩ hv, hX₀f] at h1
    have h2 := congrFun h1 2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, sub_self, add_zero,
      Pi.zero_apply] at h2
    have hfv : c.f ⟨v, hvW⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hlevicoord ⟨v, hvW⟩ hv, h2, Pi.single_zero, toAdd_one]
    have hv1 : v = 1 := hV₀I ⟨v, hvW⟩ hv hfv
    have hx1 : qc c.π v₀ w = 1 := by
      apply hX₀I
      rw [hfv, one_mul] at hj
      exact hj
    apply Subtype.ext
    rw [← hvx, hv1, hx1, one_mul]
    rfl
  have hJsurj : Function.Surjective fJ := by
    intro s
    obtain ⟨v, hv, hfv⟩ := hV₀s (Multiplicative.toAdd s 2)
    have hj : (v : V) * qc c.π v₀ (Multiplicative.toAdd s) ∈ J :=
      J.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨_, rfl⟩)
    refine ⟨⟨_, hj⟩, ?_⟩
    rw [hfJ_apply]
    have e1 : (⟨(v : V) * qc c.π v₀ (Multiplicative.toAdd s), hJW hj⟩ : ↥W) =
        v * ⟨_, c.qc_mem hLW v₀ (Multiplicative.toAdd s)⟩ := rfl
    rw [e1, map_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, hfv, hX₀f]
    abel
  set eJ := MulEquiv.ofBijective fJ ⟨hJinj, hJsurj⟩ with heJ
  set σ : Multiplicative (Fin 3 → K) →* ↥W :=
    (Subgroup.inclusion hJW).comp eJ.symm.toMonoidHom with hσ
  have hσf : ∀ s, c.f (σ s) = s := fun s => eJ.apply_symm_apply s
  have hσJ : ∀ s, ((σ s : ↥W) : V) ∈ J := fun s => (eJ.symm s).2
  have hJlevi : ∀ γ ∈ levi K, ∀ j ∈ J, ((c.π γ : ↥L) : MulAut V) j ∈ J := by
    intro γ hγ j hj
    obtain ⟨v, hv, x, ⟨w, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hj
    rw [map_mul, hv.2.1 γ hγ, qc_levi c.π hγ (hv₀ γ hγ)]
    exact J.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨_, rfl⟩)
  have hJQ : ∀ w : Fin 3 → K, w 2 = 0 → ∀ j ∈ J, ((c.π (xQ w) : ↥L) : MulAut V) j ∈ J := by
    intro w hw j hj
    obtain ⟨v, hv, x, hx, rfl⟩ := Subgroup.mem_sup.1 hj
    have hxfix : ((c.π (xQ w) : ↥L) : MulAut V) x = x := hX₀A hx _ (hA w)
    have hvq : ((c.π (xQ w) : ↥L) : MulAut V) v = qc c.π v w * v := by
      unfold qc
      group
    rw [map_mul, hxfix, hvq]
    exact J.mul_mem (J.mul_mem (Subgroup.mem_sup_right (hv.2.2 w hw))
      (Subgroup.mem_sup_left hv)) (Subgroup.mem_sup_right hx)
  have hJstab : ∀ h ∈ stabH K, ∀ j ∈ J, ((c.π h : ↥L) : MulAut V) j ∈ J := by
    intro h hh j hj
    obtain ⟨w, hw, k, hk, rfl⟩ := exists_xW_mul_levi hh
    rw [← xQ_eq hw, map_mul, Subgroup.coe_mul, MulAut.mul_apply]
    exact hJQ w hw _ (hJlevi k hk j hj)
  set ρW : ↥L →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hLW) with hρW
  set actW : ↥(StatedSL 3 K) →* MulAut ↥W := ρW.comp c.π with hactW
  have hactW_apply : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W),
      ((actW γ w : ↥W) : V) = ((c.π γ : ↥L) : MulAut V) w := fun _ _ => rfl
  have hΦ : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W),
      c.f (actW γ w) = H.natAut (StatedSL 3 K) γ (c.f w) := by
    intro γ w
    have hw : ((c.π γ : ↥L) : MulAut V) w ∈ W := ((hLW (c.π γ).2) w).2 w.2
    exact c.hfe γ w hw
  have hσQ : ∀ h ∈ stabH K, ∀ s, σ (H.natAut (StatedSL 3 K) h s) = actW h (σ s) := by
    intro h hh s
    have h1 : ((actW h (σ s) : ↥W) : V) ∈ J := by
      rw [hactW_apply]
      exact hJstab h hh _ (hσJ s)
    have h2 : fJ ⟨_, hσJ (H.natAut (StatedSL 3 K) h s)⟩ = fJ ⟨_, h1⟩ := by
      rw [hfJ_apply, hfJ_apply]
      show c.f (σ _) = c.f (actW h (σ s))
      rw [hσf, hΦ, hσf]
    have h3 := congrArg (fun j : ↥J => (j : V)) (hJinj h2)
    exact Subtype.ext h3
  obtain ⟨σ', hσ's, hσ'e⟩ := B69.avg_section actW (H.natAut (StatedSL 3 K)) c.f hΦ
    sq_eq_one_vec (stabH K) (odd_index_stabH hq) σ hσf hσQ
  refine ⟨σ', hσ's, fun γ s => ?_⟩
  exact (congrArg Subtype.val (hσ'e γ s)).symm

end Main

end B5

end CFSG.Quasithin
