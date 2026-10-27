module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNInner
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNData
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCenter
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeLabel

public section

namespace CFSG.StandardType.E6QTwo

open CFSG CFSG.Assembly E6QTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

namespace GGQ2S08RoN

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}

theorem exists_lift_stab_diag_mem (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3n : ¬ 3 ∣ n)
    (w : Fin (n + 1)) (d : Fin (n + 1) → c.Kˣ) (hd : ∏ k, d k = 1) (hdw : d w = 1) :
    ∃ t ∈ c.compL w, c.piL t = c.fr (c.diagSU d hd) ∧ (t : G) ∈ Bs := by
  classical
  have hinj : ∀ {q q' : ↥L}, q ∈ c.compL w → q' ∈ c.compL w → c.piL q = c.piL q' → q = q' :=
    fun hq hq' h => c.piL_injOn_compL hpar h3n w hq hq' h
  obtain ⟨t, ht, htd⟩ := c.exists_mem_compL_piL_eq w ⟨c.diagSU d hd, c.diagSU_mem_stab hd hdw, rfl⟩
  refine ⟨t, ht, htd, ?_⟩
  refine c.hstar _ ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    obtain ⟨t', ht', ht'pi, ht'conj⟩ := c.exists_inner hpar h3n w ⟨b', hb'⟩
    have hcomm : t' * t = t * t' := by
      refine hinj ((c.compL w).mul_mem ht' ht) ((c.compL w).mul_mem ht ht') ?_
      rw [map_mul, map_mul, ht'pi, htd, ← map_mul, ← map_mul, c.diagSU_commute]
    have h := congrArg Subtype.val (ht'conj t ht)
    rw [e6QTwoBstarConjAction_apply c.hNL ⟨b', hb'⟩ t, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    have h2 : (t' : G) * (t : G) * (t' : G)⁻¹ = (t : G) := by
      have := congrArg Subtype.val hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
      rw [this, mul_inv_cancel_right]
    calc b' * (t : G) = (b' * (t : G) * b'⁻¹) * b' := by group
      _ = (t : G) * b' := by rw [show b' * (t : G) * b'⁻¹ = (t : G) from h.trans h2]
  · have h3 : t ^ 3 = 1 := by
      refine hinj ((c.compL w).pow_mem ht 3) (c.compL w).one_mem ?_
      have hD3 : c.diagSU d hd ^ 3 = 1 := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, coe_diagSU, Subgroup.coe_one, ← map_pow]
        have h3' : d ^ 3 = 1 := funext fun k => by rw [Pi.pow_apply, c.cube, Pi.one_apply]
        rw [h3', map_one]
      rw [map_pow, htd, ← map_pow, hD3, map_one, map_one]
    have := congrArg Subtype.val h3
    simpa using this

theorem exists_lift_diag_mem (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3n : ¬ 3 ∣ n)
    (d : Fin (n + 1) → c.Kˣ) (hd : ∏ k, d k = 1) :
    ∃ t : ↥L, c.piL t = c.fr (c.diagSU d hd) ∧ (t : G) ∈ Bs := by
  classical
  have hn := c.hn
  set i0 : Fin (n + 1) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (n + 1) := ⟨1, by omega⟩ with hi1
  set i2 : Fin (n + 1) := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [hi0, hi2, Fin.ext_iff]
  have h21 : i2 ≠ i1 := by simp [hi1, hi2, Fin.ext_iff]
  set f : Fin (n + 1) → c.Kˣ := Pi.mulSingle i0 (d i0) * Pi.mulSingle i1 (d i0)⁻¹ with hfdef
  have hf : ∏ k, f k = 1 := by
    rw [hfdef]
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
    simp
  have hf2 : f i2 = 1 := by
    rw [hfdef, Pi.mul_apply, Pi.mulSingle_eq_of_ne h20, Pi.mulSingle_eq_of_ne h21, mul_one]
  set e : Fin (n + 1) → c.Kˣ := d * f⁻¹ with hedef
  have he : ∏ k, e k = 1 := by
    rw [hedef]
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [Finset.prod_mul_distrib, hd, one_mul, Finset.prod_inv_distrib, hf, inv_one]
  have he0 : e i0 = 1 := by
    rw [hedef, Pi.mul_apply, Pi.inv_apply, hfdef, Pi.mul_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne h01, mul_one, mul_inv_cancel]
  obtain ⟨t1, -, ht1, ht1B⟩ := c.exists_lift_stab_diag_mem hpar h3n i0 e he he0
  obtain ⟨t2, -, ht2, ht2B⟩ := c.exists_lift_stab_diag_mem hpar h3n i2 f hf hf2
  refine ⟨t1 * t2, ?_, Bs.mul_mem ht1B ht2B⟩
  rw [map_mul, ht1, ht2, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_diagSU, coe_diagSU, coe_diagSU, ← map_mul]
  congr 1
  rw [hedef, inv_mul_cancel_right]

theorem prod_diag_eq_one_of_inner (c : GGQ2S08RoN n Bs L x) (h3 : 3 ∣ n + 1) {b : Bs} {l : ↥L}
    (hl : ∀ y : ↥L, c.conjB b y = l * y * l⁻¹) : ∏ k, c.diag b k = 1 := by
  classical
  have hn := c.hn
  have hact : ∀ r, c.act b r = c.piL l * r * (c.piL l)⁻¹ := by
    intro r
    obtain ⟨y, rfl⟩ := c.piL_surjective r
    rw [← piL_conjB, hl, map_mul, map_mul, map_inv]
  obtain ⟨u, hu⟩ := c.fr_surjective (c.piL l)
  set D : GL (Fin (n + 1)) c.K := diagHom (n + 1) (c.diag b) with hD
  set A : GL (Fin (n + 1)) c.K := D⁻¹ * (u : GL (Fin (n + 1)) c.K) with hA
  have hscal : ∀ v : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2), ∃ μ : c.Kˣ,
      A * (v : GL (Fin (n + 1)) c.K) * A⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * v := by
    intro v
    have hfr : c.fr (c.diagConj (c.diag b) v) = c.fr (u * v * u⁻¹) := by
      rw [← act_fr, hact, ← hu, map_mul, map_mul, map_inv]
    obtain ⟨μ, hμ⟩ := c.exists_scalar_of_fr_eq hfr
    refine ⟨μ, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_diagConj] at hμ
    rw [hA, mul_inv_rev, inv_inv]
    calc D⁻¹ * (u : GL (Fin (n + 1)) c.K) * v * ((u : GL (Fin (n + 1)) c.K)⁻¹ * D)
        = D⁻¹ * ((u : GL (Fin (n + 1)) c.K) * v * (u : GL (Fin (n + 1)) c.K)⁻¹) * D := by group
      _ = D⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * (D * v * D⁻¹)) * D := by
        rw [hμ]
      _ = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ * v := by
        rw [← mul_assoc D⁻¹, ← TypeA.PGLTor.scalar_mul_comm μ D⁻¹]
        group
  have hperf : commutator ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2) = ⊤ := by
    have hK : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
    have := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (n := n + 1) (by omega)
      (fun h => by simp at h; omega)
    exact this.commutator_eq_top
  have heq := NbrLangTypeA.eq_of_mul_mem_center hperf
    (f₁ := (LargeEvenSUGroup (Fin (n + 1)) c.K 2).subtype)
    (f₂ := (MulAut.conj A).toMonoidHom.comp (LargeEvenSUGroup (Fin (n + 1)) c.K 2).subtype)
    (fun v => by
      obtain ⟨μ, hμ⟩ := hscal v
      have : ((LargeEvenSUGroup (Fin (n + 1)) c.K 2).subtype v)⁻¹ *
          ((MulAut.conj A).toMonoidHom.comp (LargeEvenSUGroup (Fin (n + 1)) c.K 2).subtype v) =
            Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ := by
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [hμ, TypeA.PGLTor.scalar_mul_comm μ, inv_mul_cancel_left]
      rw [this, Subgroup.mem_center_iff]
      intro g
      exact (TypeA.PGLTor.scalar_mul_comm μ g).symm)
  have hcomm : ∀ v ∈ LargeEvenSUGroup (Fin (n + 1)) c.K 2,
      A * (v : GL (Fin (n + 1)) c.K) = v * A := by
    intro v hv
    have h := congrArg (fun f => f ⟨v, hv⟩) heq
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at h
    calc A * v = (A * v * A⁻¹) * A := by group
      _ = v * A := by rw [← h]
  obtain ⟨μ, hμ⟩ := ggQ2s08rN_exists_scalar_of_commute c.hK hcomm
  have hdetu : ((u : GL (Fin (n + 1)) c.K) : Matrix (Fin (n + 1)) (Fin (n + 1)) c.K).det = 1 := by
    have hU := USixTwo.fieldDataFour c.hK
    have hmem :
        (u : GL (Fin (n + 1)) c.K) ∈ ClassicalGroups.UnitaryFlag.unitarySU 2 1 c.K (n + 1) :=
      (SetLike.ext_iff.mp (suN_eq c.K) _).mp u.2
    exact ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hU).mp hmem).1
  have hu' : (u : GL (Fin (n + 1)) c.K) = D * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) μ := by
    rw [← hμ, hA, mul_inv_cancel_left]
  have hdet := congrArg (fun g : GL (Fin (n + 1)) c.K =>
    ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) c.K).det)) hu'
  simp only [hdetu, Units.val_mul, Matrix.det_mul, hD, CFSG.SectionRank.OddCover.det_diagHom,
    Matrix.GeneralLinearGroup.coe_scalar] at hdet
  have hμ3 : ((μ : c.Kˣ) : c.K) ^ (n + 1) = 1 := by
    obtain ⟨k, hk⟩ := h3
    rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, c.cube, Units.val_one, one_pow]
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hμ3, mul_one] at hdet
  apply Units.ext
  rw [Units.coe_prod, Units.val_one]
  exact hdet.symm

theorem mem_of_inner (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3 : 3 ∣ n + 1)
    (hxL : x ∈ L) {b : G} (hb : b ∈ Bs) {l : G} (hl : l ∈ L) {z : G}
    (hz : z ∈ Subgroup.centralizer (L : Set G)) (hblz : b = l * z) : b ∈ L := by
  classical
  set b' : Bs := ⟨b, hb⟩ with hb'
  have hconj : ∀ y : ↥L, c.conjB b' y = ⟨l, hl⟩ * y * (⟨l, hl⟩ : ↥L)⁻¹ := by
    intro y
    apply Subtype.ext
    rw [e6QTwoBstarConjAction_apply c.hNL b' y, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    change b * (y : G) * b⁻¹ = l * y * l⁻¹
    have hzy : (y : G) * z = z * y := Subgroup.mem_centralizer_iff.mp hz y y.2
    rw [hblz, mul_inv_rev]
    calc l * z * (y : G) * (z⁻¹ * l⁻¹) = l * (z * y) * z⁻¹ * l⁻¹ := by group
      _ = l * (y * z) * z⁻¹ * l⁻¹ := by rw [hzy]
      _ = l * y * l⁻¹ := by group
  have hprod := c.prod_diag_eq_one_of_inner h3 hconj
  obtain ⟨t, htpi, htB⟩ := c.exists_lift_diag_mem hpar (by omega) (c.diag b') hprod
  have heq := NbrLangTypeA.eq_of_mul_mem_center c.hperf (f₁ := (MulAut.conj t).toMonoidHom)
    (f₂ := (c.conjB b').toMonoidHom) (fun y => by
      rw [← c.piL_ker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
      change c.piL (t * y * t⁻¹) = c.piL (c.conjB b' y)
      rw [piL_conjB]
      obtain ⟨v, hv⟩ := c.fr_surjective (c.piL y)
      have hD : c.diagConj (c.diag b') v =
          c.diagSU (c.diag b') hprod * v * (c.diagSU (c.diag b') hprod)⁻¹ :=
        Subtype.ext (by rw [coe_diagConj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          coe_diagSU])
      rw [← hv, act_fr, hD, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, htpi, hv])
  have hcent : b * (t : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun f => f (t⁻¹ * ⟨y, hy⟩ * t)) heq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h2 := congrArg Subtype.val h
    rw [e6QTwoBstarConjAction_apply c.hNL b'] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    change (t : G) * ((t : G)⁻¹ * y * t) * (t : G)⁻¹ = b * ((t : G)⁻¹ * y * t) * b⁻¹ at h2
    calc y * (b * (t : G)⁻¹) = ((t : G) * ((t : G)⁻¹ * y * t) * (t : G)⁻¹) * (b * (t : G)⁻¹) := by
          group
      _ = (b * ((t : G)⁻¹ * y * t) * b⁻¹) * (b * (t : G)⁻¹) := by rw [h2]
      _ = b * (t : G)⁻¹ * y := by group
  have hx : b * (t : G)⁻¹ ∈ Subgroup.zpowers x := by
    rw [← c.hBL]
    exact ⟨Bs.mul_mem hb (Bs.inv_mem htB), hcent⟩
  have hxL' : b * (t : G)⁻¹ ∈ L := (Subgroup.zpowers_le.mpr hxL) hx
  have : b = (b * (t : G)⁻¹) * t := by group
  rw [this]
  exact L.mul_mem hxL' t.2

end GGQ2S08RoN

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo

theorem ggQ2s08_bigInnerPart_holds
    (hRig : GGLabelRigidInput) :
    GGQ2S08BigInnerPartInput := by
  classical
  intro G _ _ B Bs x L D J hS _ lab hmark hlab M hA hMW
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h0
    apply hSS.2.2.1
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h0)
    exact congrArg Subtype.val (ofMul_eq_zero.mp h1)
  obtain ⟨htag, h3, h12⟩ : lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 12 ≤ lab.rank + 1 := by
    rcases ggQ2s08_big_shape_label M hlab hMW hx0 (Or.inr (Or.inl hA)) with h | h
    · exact absurd hA.1 h.1.1
    · exact h.2
  have hLab : lab.tag = .twA ∧ lab.rank = lab.rank ∧ GGLabQTwo 3 lab := ⟨htag, rfl, hlab.1⟩
  have hΛ : Fintype.card M.Λ = lab.rank := by
    obtain ⟨e, -⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hMW
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hcard : Nat.card Bs = 3 ^ (lab.rank + 1) := by
    have h1 : Nat.card Bs = Nat.card M.V :=
      Nat.card_congr ((Additive.ofMul : ↥Bs ≃ Additive ↥Bs).trans M.model.toEquiv)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Finite M.V := Finite.of_equiv _ M.model.toEquiv
    have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
    rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 3) (V := M.V), Nat.card_zmod, hA.2.2.2.1, hΛ]
  have hpar : Odd lab.rank ∨ Odd (Nat.card (Subgroup.center ↥L)) := by
    rcases Nat.even_or_odd lab.rank with - | ho
    · right
      obtain ⟨K, hKf, hKfin, θ, hK, -, -⟩ := ggQ2s08rN_markingData hRig hS hmark hLab
      have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
      have hdvd := ggQ2s08bc_unitary hK' (d := lab.rank + 1) (by omega) ↥L
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)))
        (θ.surjective.comp (QuotientGroup.mk'_surjective _))
        (fun g hg => by
          have h1 : θ (QuotientGroup.mk' (Subgroup.center ↥L) g) = 1 := hg
          rwa [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1)
        hmark.1
      exact Odd.of_dvd_nat (by decide) hdvd
    · exact Or.inl ho
  obtain ⟨c⟩ := ggQ2s08rN_exists_data_of_card hRig (n := lab.rank) (by omega) hS
    (Or.inr ⟨hpar, by omega⟩) hmark hLab hcard
  rintro b hb ⟨l, hl, z, hz, hblz⟩
  exact c.mem_of_inner hpar h3 hA.1 hb hl hz hblz

end CFSG.StandardType

end
