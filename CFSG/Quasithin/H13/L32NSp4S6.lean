module

public import CFSG.Quasithin.H13.L32NSp4Cases

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {b : Module.Basis (Fin 4) (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}

@[expose] noncomputable def sympFourEquiv : ↥sympFour ≃* Equiv.Perm (Fin 6) :=
  MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩

theorem S6.exists_equiv {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (hΓ : Γ ≤ KGCert.spGroup B) :
    ∃ H : Subgroup (Equiv.Perm (Fin 6)), Nonempty (↥Γ ≃* ↥H) := by
  have hle := map_phi4_le b hgram hΓ
  refine ⟨((Γ.map (phi4 b)).subgroupOf sympFour).map sympFourEquiv.toMonoidHom, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective Γ (phi4 b) (phi4_injective b)).trans
    ((Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (sympFourEquiv.subgroupMap ((Γ.map (phi4 b)).subgroupOf sympFour)))

theorem S6.mulEquiv_perm {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (hΓ : Γ ≤ KGCert.spGroup B)
    (h720 : Nat.card Γ = 720) : Nonempty (↥Γ ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨H, ⟨e⟩⟩ := S6.exists_equiv hgram hΓ
  have hH : Nat.card H = 720 := by rw [← Nat.card_congr e.toEquiv, h720]
  have htop : H = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hH, Nat.card_perm, Nat.card_fin]
    decide
  exact ⟨e.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

theorem S6.mulEquiv_alt {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) (hΓ : Γ ≤ KGCert.spGroup B)
    (h360 : Nat.card Γ = 360) : Nonempty (↥Γ ≃* ↥(alternatingGroup (Fin 6))) := by
  obtain ⟨H, ⟨e⟩⟩ := S6.exists_equiv hgram hΓ
  have hH : Nat.card H = 360 := by rw [← Nat.card_congr e.toEquiv, h360]
  have hidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [hH, Nat.card_perm, Nat.card_fin] at this
    have h6 : Nat.factorial 6 = 720 := by decide
    omega
  exact ⟨e.trans (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx))⟩

@[expose] noncomputable def qCode (b : Module.Basis (Fin 4) (ZMod 2) V) (q : V → ZMod 2) : ℕ :=
  enc4 fun i => q (b i)

theorem gramOf_antidiag {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) : gramOf B b = KGCert.gram 12 := by
  ext k
  fin_cases k <;> simp [gramOf, KGCert.gram, hgram, antidiagGram] <;> decide

theorem qJ_vc {B : LinearMap.BilinForm (ZMod 2) V} (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j)
    {q : V → ZMod 2} (hq : ∀ v w, q (v + w) = q v + q w + B v w) (v : V) :
    b2z (qJ (qCode b q) (vc b v)) = q v := by
  rw [qJ, b2z_qfN, vec4_vc, qCode, vec4_enc4, q_eq_qfE hq b v, gramOf_antidiag hgram]

theorem exists_move_quad [Finite V] [Sp4Data] {s : Node}
    (hsL : s ∈ ov5K ∨ s ∈ ov9K) (h : IsNodeOf b Γ s)
    (hcase : s.mask = specK.s120.2 ∨ 360 ≤ s.els.length) {B : LinearMap.BilinForm (ZMod 2) V}
    (hgram : ∀ i j, B (b i) (b j) = antidiagGram i j) {u w : V} (hu : u ≠ 0) (hw : w ≠ 0)
    (huw : u ≠ w) (hB : B u w = 0) {q : V → ZMod 2} (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hqu : q u = 0) (hqw : q w = 0) (hquw : q (u + w) = 0) :
    ∃ γ ∈ Γ, ∃ v, q (γ v) ≠ q v := by
  have hzero : ∀ v : V, q v = 0 → qJ (qCode b q) (vc b v) = false := by
    intro v hv
    have := qJ_vc hgram hq v
    rw [hv] at this
    cases hc : qJ (qCode b q) (vc b v)
    · rfl
    · rw [hc] at this
      exact absurd this (by decide)
  have hz : ((lineOf b u w).all fun y => !qJ (qCode b q) y) = true := by
    rw [all_lineOf, hzero u hqu, hzero w hqw, hzero _ hquw]
    simp
  have hmove := quadOk_apply hsL hcase (enc4_lt _) (lineOf_mem b hgram hu hw huw hB) hz
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hmove
  obtain ⟨d, hd, v, hv, hne⟩ := hmove
  obtain ⟨γ, hγ, rfl⟩ := h.surj d hd
  set v' : V := b.equivFun.symm (vec4 v) with hv'
  have hvc : vc b v' = v := by
    apply vec4_inj (vc_lt b v') hv
    rw [vec4_vc, hv', LinearEquiv.apply_symm_apply]
  refine ⟨γ, hγ, v', fun he => hne ?_⟩
  rw [← hvc, mulVecC_cf]
  apply b2z_inj
  have e1 := qJ_vc hgram hq (γ v')
  have e2 := qJ_vc hgram hq v'
  simp only [qCode] at e1 e2
  rw [e1, e2, he]

end CFSG.Quasithin.H13.Sp4Cert
