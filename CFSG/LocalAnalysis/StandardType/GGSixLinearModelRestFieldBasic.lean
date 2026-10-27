module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelCoords

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal Matrix

namespace LinModel

theorem exists_pow_two_pow_eq {f : ℕ} (hf : f ≠ 0) (σ : GaloisField 2 f ≃+* GaloisField 2 f) :
    ∃ s < f, ∀ x, σ x = x ^ (2 ^ s) := by
  have hcomm : ∀ x : ZMod 2, σ (algebraMap (ZMod 2) (GaloisField 2 f) x) =
      algebraMap (ZMod 2) (GaloisField 2 f) x := fun x =>
    congrArg (fun φ : ZMod 2 →+* GaloisField 2 f => φ x)
      (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) (GaloisField 2 f)))
        (algebraMap (ZMod 2) (GaloisField 2 f)))
  obtain ⟨⟨s, hs⟩, hσ⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2)
    (GaloisField 2 f)).2 (AlgEquiv.ofRingEquiv hcomm)
  rw [GaloisField.finrank 2 hf] at hs
  refine ⟨s, hs, fun x => ?_⟩
  have h1 := congrArg (fun τ : GaloisField 2 f ≃ₐ[ZMod 2] GaloisField 2 f => τ x) hσ
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card,
    AlgEquiv.ofRingEquiv_apply] at h1
  exact h1.symm

theorem exists_pow_eq_of_pow_div_eq_one {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card Fˣ) {x : Fˣ} (hx : x ^ (Nat.card Fˣ / p) = 1) :
    ∃ c : Fˣ, c ^ p = x := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have htop : Subgroup.zpowers γ = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hγ])
  have hmem : x ∈ Subgroup.zpowers γ := by rw [htop]; exact Subgroup.mem_top x
  obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  have h1 : orderOf γ ∣ k * (Nat.card Fˣ / p) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hx)
  rw [hγ] at h1
  obtain ⟨N, hN⟩ := hpF
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · have : 0 < Nat.card Fˣ := Nat.card_pos
      rw [hN, h, mul_zero] at this
      omega
    · exact h
  rw [hN, Nat.mul_div_cancel_left _ hp.pos] at h1
  obtain ⟨j, rfl⟩ : p ∣ k := Nat.dvd_of_mul_dvd_mul_right hN0 h1
  exact ⟨γ ^ j, by rw [← pow_mul, mul_comm]⟩

theorem dvd_of_forall_pow_two_pow_eq {f n : ℕ} (hf : f ≠ 0)
    (h : ∀ x : GaloisField 2 f, x ^ (2 ^ n) = x) : f ∣ n := by
  have h1 : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) (GaloisField 2 f) ^ n = 1 := by
    apply AlgEquiv.ext
    intro x
    simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card,
      AlgEquiv.one_apply]
    exact h x
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rwa [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, GaloisField.finrank 2 hf] at h2

theorem dvd_two_pow_sub_one_of_fixes {F : Type} [Field F] {p s : ℕ} (hp : 0 < p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (h : ζ ^ (2 ^ s) = ζ) : p ∣ 2 ^ s - 1 := by
  apply hζ.dvd_of_pow_eq_one
  have h1 : ζ ^ (2 ^ s - 1) * ζ = 1 * ζ := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h, one_mul]
  exact mul_right_cancel₀ (hζ.ne_zero hp.ne') h1

theorem exists_pow_eq_mul_of_fixes {f : ℕ} (hf : f ≠ 0) {p : ℕ} (hp : 0 < p)
    {ζ : GaloisField 2 f} (hζ : IsPrimitiveRoot ζ p) {σ : GaloisField 2 f ≃+* GaloisField 2 f}
    (hσζ : σ ζ = ζ) (x : GaloisField 2 f) : ∃ c : GaloisField 2 f, σ x = x * c ^ p := by
  obtain ⟨s, -, hs⟩ := exists_pow_two_pow_eq hf σ
  obtain ⟨k, hk⟩ := dvd_two_pow_sub_one_of_fixes hp hζ (by rw [← hs]; exact hσζ)
  refine ⟨x ^ k, ?_⟩
  rw [hs, ← pow_mul, mul_comm k p, ← hk, ← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]

theorem exists_pow_eq_of_fixed {f p : ℕ} (hf : f ≠ 0) (hp : p.Prime) {ζ : GaloisField 2 f}
    (hζ : IsPrimitiveRoot ζ p) {σ : GaloisField 2 f ≃+* GaloisField 2 f} (hσp : σ ^ p = 1)
    (hσ1 : σ ≠ 1) {x : (GaloisField 2 f)ˣ} (hx : σ (x : GaloisField 2 f) = x) :
    ∃ c : (GaloisField 2 f)ˣ, c ^ p = x := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hFu : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by rw [Nat.card_units, hF]
  obtain ⟨s, hsf, hs⟩ := exists_pow_two_pow_eq hf σ
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hσ1 (RingEquiv.ext fun y => by rw [hs, pow_zero, pow_one]; rfl)
  have hσζ : σ ζ = ζ :=
    fieldAut_fixes_root hp hζ (k := 1) (by rw [pow_one]; exact hσp) hζ.pow_eq_one
  have hps : p ∣ 2 ^ s - 1 := dvd_two_pow_sub_one_of_fixes hp.pos hζ (by rw [← hs]; exact hσζ)
  have hpf : p ∣ 2 ^ f - 1 := by
    have hu : IsPrimitiveRoot ((hζ.isUnit hp.ne_zero).unit) p :=
      IsPrimitiveRoot.coe_units_iff.mp (by rw [IsUnit.unit_spec]; exact hζ)
    have h1 := orderOf_dvd_natCard ((hζ.isUnit hp.ne_zero).unit)
    rwa [← hu.eq_orderOf, hFu] at h1
  have hiter : ∀ (k : ℕ) (y : GaloisField 2 f), (σ ^ k) y = y ^ (2 ^ (s * k)) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', RingAut.mul_apply, ih, map_pow, hs, ← pow_mul, ← pow_add, mul_add, mul_one,
        add_comm]
  have hfsp : f ∣ s * p := dvd_of_forall_pow_two_pow_eq hf fun y => by
    rw [← hiter p y, hσp]
    rfl
  obtain ⟨s', f', hcop, hs', hf'⟩ := Nat.exists_coprime s f
  have he0 : 0 < Nat.gcd s f := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hf)
  have hf'p : f' = p := by
    have h1 : f' ∣ s' * p := by
      have h2 : f' * Nat.gcd s f ∣ s' * p * Nat.gcd s f := by
        rw [← hf', mul_right_comm, ← hs']
        exact hfsp
      exact Nat.dvd_of_mul_dvd_mul_right he0 h2
    rcases hp.eq_one_or_self_of_dvd f' (hcop.symm.dvd_of_dvd_mul_left h1) with h | h
    · exfalso
      rw [h, one_mul] at hf'
      have h3 : f ∣ s := by rw [hf']; exact Nat.gcd_dvd_left s f
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) h3) (by omega)
    · exact h
  have hxs : x ^ (2 ^ s - 1) = 1 := by
    apply Units.ext
    have h1 : (x : GaloisField 2 f) ^ (2 ^ s - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, ← hs, hx, one_mul]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ x.ne_zero h1
  have hxf : x ^ (2 ^ f - 1) = 1 := by rw [← hFu]; exact pow_card_eq_one'
  have hxe : x ^ (2 ^ Nat.gcd s f - 1) = 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact pow_gcd_eq_one.mpr ⟨hxs, hxf⟩
  have hSmul : (∑ j ∈ Finset.range p, (2 ^ Nat.gcd s f) ^ j) * (2 ^ Nat.gcd s f - 1) =
      2 ^ f - 1 := by
    rw [geom_sum_mul_of_one_le Nat.one_le_two_pow, ← pow_mul, mul_comm, ← hf'p, ← hf']
  have hpe : p ∣ 2 ^ Nat.gcd s f - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hps hpf
  have hpS : p ∣ ∑ j ∈ Finset.range p, (2 ^ Nat.gcd s f) ^ j := by
    have h1 : (2 : ZMod p) ^ Nat.gcd s f = 1 := by
      have h2 : ((2 ^ Nat.gcd s f - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpe
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, sub_eq_zero, Nat.cast_pow,
        Nat.cast_ofNat] at h2
      exact h2
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp [h1]
  obtain ⟨S', hS'⟩ := hpS
  have hdiv : Nat.card (GaloisField 2 f)ˣ / p = (2 ^ Nat.gcd s f - 1) * S' := by
    rw [hFu, ← hSmul, hS', mul_comm p S', mul_comm (S' * p), ← mul_assoc]
    exact Nat.mul_div_cancel _ hp.pos
  refine exists_pow_eq_of_pow_div_eq_one hp (by rw [hFu]; exact hpf) ?_
  rw [hdiv, pow_mul, hxe, one_pow]

section Sylow

variable {G : Type} [Group G]

theorem exists_conj_mem_normalizer [Finite G] {p : ℕ} (hp : p.Prime) {M Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsM : Bs ≤ M) (hU : GGBstarUniqueIn p M Bs) {y : G}
    (hyM : y ∈ M) (hyp : y ^ p = 1) :
    ∃ m ∈ M, m⁻¹ * y * m ∈ Subgroup.normalizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2 b b.2)⟩
  obtain ⟨Q, hQ⟩ := (hpg.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  have hyp' : IsPGroup p (Subgroup.zpowers (⟨y, hyM⟩ : M)) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hy1 : (⟨y, hyM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hyp)
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hy1, _root_.one_zpow]
    rfl
  obtain ⟨R, hR⟩ := hyp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M R Q
  set P := (Q : Subgroup ↥M).map M.subtype with hPdef
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := Q.isPGroup'.map M.subtype
  have hBsP : Bs ≤ P := fun b hb => ⟨⟨b, hBsM hb⟩, hQ hb, rfl⟩
  have hmaxM : ∀ S : Subgroup G, S ≤ M → IsPGroup p S → P ≤ S → S = P := by
    intro S hSM hSp hPS
    have hSp' : IsPGroup p (S.subgroupOf M) :=
      hSp.comap_of_injective M.subtype M.subtype_injective
    have hQS : (Q : Subgroup ↥M) ≤ S.subgroupOf M := fun q hq => hPS ⟨q, hq, rfl⟩
    have hSQ := Q.is_maximal' hSp' hQS
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hSM, hSQ]
  have hPN : P ≤ Subgroup.normalizer (Bs : Set G) := by
    intro s hs
    have hE : Bs.map (MulAut.conj s).toMonoidHom ≤ P := by
      rintro _ ⟨b, hb, rfl⟩
      exact P.mul_mem (P.mul_mem hs (hBsP hb)) (P.inv_mem hs)
    have hcard : Nat.card (Bs.map (MulAut.conj s).toMonoidHom) = Nat.card Bs :=
      Subgroup.card_map_of_injective (MulAut.conj s).injective
    have heq := (hU P hPM hPp hBsP hmaxM _ hE (isElemAbelian_map_hom hBs _)).2 hcard
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← heq]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', he⟩ := hh
      have : h' = h := by
        have he' : s * h' * s⁻¹ = s * h * s⁻¹ := he
        simpa using he'
      rwa [← this]
  have hmem : MulAut.conj g (⟨y, hyM⟩ : M) ∈ (Q : Subgroup M) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR (Subgroup.mem_zpowers _))
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, ?_⟩
  rw [inv_inv]
  exact hPN ⟨_, hmem, rfl⟩

end Sylow

section Frames

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem mem_ggInducedPairs_of_comp_conjSL_inv
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {g : G} {P A' : GL (Fin (m + 1)) F}
    (h : (g, A') ∈ LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹))) :
    (g, P⁻¹ * A' * P) ∈ LinFusion.ggInducedPairs ψ := by
  intro v
  have h1 := LinFusion.mem_ggInducedPairs.mp h (InnerDiagA.conjSL P v)
  simp only [MonoidHom.comp_apply] at h1
  rw [← LinFusion.conjSL_mul, inv_mul_cancel, LinFusion.conjSL_one, ← LinFusion.conjSL_mul,
    ← LinFusion.conjSL_mul] at h1
  exact h1

theorem ggPsiInnerDiag_of_mem_ggInducedPairs [Finite F] [CharP F 2] (hm : 2 ≤ m)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : Odd p) {c : G} {A : GL (Fin (m + 1)) F} (hcA : (c, A) ∈ LinFusion.ggInducedPairs ψ)
    (hcp : c ^ p = 1) : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c := by
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (m + 1) := ⟨2, by omega⟩ with hi₂
  have h12 : i₁ ≠ i₂ := Fin.ne_of_val_ne (by simp [hi₁, hi₂])
  have h01 : (0 : Fin (m + 1)) ≠ i₁ := Fin.ne_of_val_ne (by simp [hi₁])
  have h02 : (0 : Fin (m + 1)) ≠ i₂ := Fin.ne_of_val_ne (by simp [hi₂])
  set D : GL (Fin (m + 1)) F :=
    InnerDiagA.diagGL (Pi.mulSingle 0 (GeneralLinearGroup.det A)) with hD
  have hdet : GeneralLinearGroup.det (A⁻¹ * D) = 1 := by
    rw [map_mul, map_inv, hD, det_diagGL, Finset.prod_pi_mulSingle']
    simp
  set s : Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
    ⟨((A⁻¹ * D : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F), by
      rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩ with hs
  have hsD : Matrix.SpecialLinearGroup.toGL s = A⁻¹ * D := Units.ext rfl
  have hcs : (c * ψ s, D) ∈ LinFusion.ggInducedPairs ψ := by
    have h1 := (LinFusion.ggInducedPairs ψ).mul_mem hcA (map_toGL_mem_ggInducedPairs ψ s)
    rwa [Prod.mk_mul_mk, hsD, mul_inv_cancel_left] at h1
  have hcs' := (LinFusion.ggInducedPairs ψ).inv_mem hcs
  rw [Prod.inv_mk, hD, ← LinFusion.diagGL_inv] at hcs'
  refine HypSixTypeA.ggPsiInnerDiag_sl hm hker hp (mem_normalizer_of_mem_ggInducedPairs hcA)
    (by rw [hcp]; exact Subgroup.one_mem _) (InnerDiagA.typeARoot_mem_roots F h12) (u := 1)
    ⟨ψ s, ⟨s, rfl⟩, 1, Subgroup.one_mem _, fun z hz => ?_⟩
  have hz' : z ∈ SpecialLinear.rootSubgroup m F h12 := by
    rw [← InnerDiagA.rootGroup_typeARoot]
    exact hz
  obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup h12 z).mp hz'
  simp only [one_mul, inv_one, mul_one]
  have h1 := LinFusion.mem_ggInducedPairs.mp hcs' (Matrix.SpecialLinearGroup.transvection h12 t)
  rw [inv_inv, InnerDiagA.conjSL_diagGL_transvection] at h1
  rw [h1]
  congr 2
  simp [Pi.mulSingle_eq_of_ne' h01, Pi.mulSingle_eq_of_ne' h02]

end Frames

end LinModel

end CFSG.StandardType
