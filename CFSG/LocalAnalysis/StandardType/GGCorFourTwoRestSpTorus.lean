module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut fieldSp fieldAut_proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace CorFourTwoSp

variable {K : Type} [Field K] {m : ℕ}

section Pow

variable {G : Type*} [Group G]

theorem pow_eq_self_of_natCast_eq_one {p n : ℕ} (hn : (n : ZMod p) = 1) {e : G}
    (he : e ^ p = 1) : e ^ n = e := by
  have h1 : n ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff, hn, Nat.cast_one]
  have h2 : n ≡ 1 [MOD orderOf e] := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one he) h1
  calc e ^ n = e ^ 1 := pow_eq_pow_iff_modEq.mpr h2
    _ = e := pow_one e

theorem exists_pow_pow_eq_of_natCast_ne_zero {p c : ℕ} (hp : p.Prime) (hc : (c : ZMod p) ≠ 0)
    {e : G} (he : e ^ p = 1) : ∃ d : ℕ, (e ^ d) ^ c = e := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((c : ZMod p)⁻¹).val, ?_⟩
  rw [← pow_mul]
  refine pow_eq_self_of_natCast_eq_one ?_ he
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hc]

end Pow

@[expose] noncomputable def fieldAutR (m : ℕ) (σ : K ≃+* K) :
    MulAut (LargeEvenProj (LargeEvenSpGroup K m)) :=
  fieldAut m K σ

theorem fieldAutR_mul (σ τ : K ≃+* K) : fieldAutR m (σ * τ) = fieldAutR m σ * fieldAutR m τ :=
  map_mul (fieldAut m K) σ τ

theorem fieldAutR_one : fieldAutR (K := K) m 1 = 1 :=
  map_one (fieldAut m K)

theorem fieldAutR_spTorus {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hζ : ζ ^ p = 1)
    (hc : σ (ζ : K) = (ζ : K) ^ c) (f : Fin m → Multiplicative (ZMod p)) :
    fieldAutR m σ (spTorus hζ f) = spTorus hζ f ^ c :=
  ReflSp.fieldAut_spTorus σ hζ hc f

theorem fieldSp_spRootSp (σ : K ≃+* K) (i₀ : Fin m) (a : Multiplicative K) :
    fieldSp m K σ (spRootSp i₀ a) =
      spRootSp i₀ (Multiplicative.ofAdd (σ (Multiplicative.toAdd a))) := by
  apply Subtype.ext
  apply Units.ext
  change ((spRootGL i₀ a : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
    ((spRootGL i₀ (Multiplicative.ofAdd (σ (Multiplicative.toAdd a))) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  rw [spRootGL_coe, spRootGL_coe, toAdd_ofAdd]
  ext y z
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem fieldAutR_spRoot (σ : K ≃+* K) (i₀ : Fin m) (a : Multiplicative K) :
    fieldAutR m σ (LargeEvenProjMk _ (spRootSp i₀ a)) =
      LargeEvenProjMk _ (spRootSp i₀ (Multiplicative.ofAdd (σ (Multiplicative.toAdd a)))) :=
  (fieldAut_proj (r := m) (K := K) σ (spRootSp i₀ a)).trans
    (congrArg (proj m K) (fieldSp_spRootSp σ i₀ a))

theorem fieldAutR_mem_spRootGroup (σ : K ≃+* K) (i₀ : Fin m)
    {v : LargeEvenProj (LargeEvenSpGroup K m)} (hv : v ∈ spRootGroup i₀) :
    fieldAutR m σ v ∈ spRootGroup i₀ := by
  obtain ⟨a, rfl⟩ := hv
  exact ⟨Multiplicative.ofAdd (σ (Multiplicative.toAdd a)), (fieldAutR_spRoot σ i₀ a).symm⟩

theorem exists_eq_conj_fieldAutR [Finite K] [CharP K 2] (hm3 : 3 ≤ m)
    (β : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :
    ∃ (s : LargeEvenProj (LargeEvenSpGroup K m)) (σ : K ≃+* K),
      β = MulAut.conj s * fieldAutR m σ := by
  obtain ⟨s, φ, ⟨σ, rfl⟩, hβ⟩ := ReflSp.exists_eq_conj_fieldAut hm3 β
  exact ⟨s, σ, MulEquiv.ext fun y => hβ y⟩

theorem fieldAutR_eq_one_of_mem [CharP K 2] [NeZero m] {σ : K ≃+* K}
    (h : fieldAutR m σ ∈ (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* _).range) :
    fieldAutR m σ = 1 := by
  obtain ⟨y, hy⟩ := h
  have hmem : fieldAut m K σ ∈
      (MulAut.conj : LowTwoRank.StatedProj (LowTwoRank.StatedSp m K) →* _).range ⊓
        AutPSp.compl (n := m) (K := K) :=
    ⟨⟨y, hy⟩, σ, rfl⟩
  exact Subgroup.mem_bot.mp ((AutPSp.inn_inf_compl (n := m) (K := K)).le hmem)

theorem mulAut_mul_conj {G : Type*} [Group G] (ψ : MulAut G) (y : G) :
    ψ * MulAut.conj y = MulAut.conj (ψ y) * ψ := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem exists_conj_mul_fieldAutR_pow (s : LargeEvenProj (LargeEvenSpGroup K m)) (σ : K ≃+* K)
    (n : ℕ) : ∃ s' : LargeEvenProj (LargeEvenSpGroup K m),
      (MulAut.conj s * fieldAutR m σ) ^ n = MulAut.conj s' * fieldAutR m (σ ^ n) := by
  induction n with
  | zero => exact ⟨1, by simp [fieldAutR_one]⟩
  | succ n ih =>
    obtain ⟨s', hs'⟩ := ih
    refine ⟨s' * fieldAutR m (σ ^ n) s, ?_⟩
    rw [pow_succ (MulAut.conj s * fieldAutR m σ) n, hs', pow_succ σ n, fieldAutR_mul, map_mul,
      mul_assoc (MulAut.conj s'), ← mul_assoc (fieldAutR m (σ ^ n)) (MulAut.conj s),
      mulAut_mul_conj]
    simp only [mul_assoc]

section Aut

variable [Finite K] [CharP K 2]

theorem exists_conj_pow_of_aut (hm3 : 3 ≤ m) {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (x : LargeEvenProj (LargeEvenSpGroup K m))
    (β : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :
    ∃ (s : LargeEvenProj (LargeEvenSpGroup K m)) (σ : K ≃+* K) (c : ℕ), c < p ∧
      σ (ζ : K) = (ζ : K) ^ c ∧ β = MulAut.conj s * fieldAutR m σ ∧
      ∀ f, β (x * spTorus hζ f * x⁻¹) =
        (s * fieldAutR m σ x * x⁻¹) * (x * spTorus hζ f * x⁻¹) ^ c *
          (s * fieldAutR m σ x * x⁻¹)⁻¹ := by
  obtain ⟨s, σ, rfl⟩ := exists_eq_conj_fieldAutR hm3 β
  obtain ⟨c, hcp, hc⟩ := ReflSp.exists_ringEquiv_eq_pow σ hζo
  refine ⟨s, σ, c, hcp, hc, rfl, fun f => ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    fieldAutR_spTorus σ hζ hc f, conj_pow]
  group

omit [Finite K] [CharP K 2] in
theorem natCast_ne_zero_of_eq_pow {p : ℕ} (hp : p.Prime) {ζ : Kˣ} (hζo : orderOf ζ = p)
    {σ : K ≃+* K} {c : ℕ} (hc : σ (ζ : K) = (ζ : K) ^ c) : (c : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨k, rfl⟩ := h0
  have hζp : (ζ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζo, pow_orderOf_eq_one, Units.val_one]
  rw [pow_mul, hζp, one_pow] at hc
  have h1 : (ζ : K) = 1 := σ.injective (by rw [hc, map_one])
  have h2 : ζ = 1 := Units.ext (by rw [h1, Units.val_one])
  rw [h2, orderOf_one] at hζo
  exact hp.one_lt.ne hζo

omit [Finite K] in
theorem natCast_eq_one_of_pow_eq_one [NeZero m] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {s : LargeEvenProj (LargeEvenSpGroup K m)}
    {σ : K ≃+* K} {c : ℕ} (hc : σ (ζ : K) = (ζ : K) ^ c)
    (h1 : (MulAut.conj s * fieldAutR m σ) ^ p = 1) : (c : ZMod p) = 1 := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s', hs'⟩ := exists_conj_mul_fieldAutR_pow s σ p
  rw [hs'] at h1
  have hF : fieldAutR m (σ ^ p) = MulAut.conj s'⁻¹ :=
    (eq_inv_of_mul_eq_one_right h1).trans (map_inv _ _).symm
  have hF1 : fieldAutR m (σ ^ p) = 1 := fieldAutR_eq_one_of_mem ⟨s'⁻¹, hF.symm⟩
  have hcp : ∀ n : ℕ, (σ ^ n) (ζ : K) = (ζ : K) ^ (c ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' σ n, RingAut.mul_apply, ih, map_pow, hc, ← pow_mul, pow_succ' c n]
  have hfix := fieldAutR_spTorus (m := m) (σ ^ p) hζ (hcp p)
    (Pi.mulSingle (0 : Fin m) (Multiplicative.ofAdd (1 : ZMod p)))
  rw [hF1, MulAut.one_apply, ← map_pow] at hfix
  have hinj := spTorus_injective (K := K) (m := m) hζ hζo (hp.odd_of_ne_two hp2) hfix
  have h2 := congrArg (fun g : Fin m → Multiplicative (ZMod p) => Multiplicative.toAdd (g 0)) hinj
  simp only [Pi.pow_apply, Pi.mulSingle_eq_same, toAdd_ofAdd, toAdd_pow, nsmul_eq_mul, mul_one,
    Nat.cast_pow] at h2
  rw [ZMod.pow_card] at h2
  exact h2.symm

end Aut

section Root

variable {p : ℕ} {ζ : Kˣ}

theorem eq_of_pairedUnits_eq [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {x y : Fin m ⊕ Fin m}
    (h : ∀ f : Fin m → Multiplicative (ZMod p),
      pairedUnits (fun i => zmodPowHom hζ (f i)) x =
        pairedUnits (fun i => zmodPowHom hζ (f i)) y) : x = y := by
  classical
  have := Fact.mk hp
  obtain ⟨t, ht⟩ : ∃ t : Kˣ, t = zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) := ⟨_, rfl⟩
  have ht1 : t ≠ 1 := by
    intro h1
    rw [ht] at h1
    have h2 := congrArg Multiplicative.toAdd ((zmodPowHom_eq_one_iff hζ hζo).mp h1)
    simp only [toAdd_ofAdd, toAdd_one] at h2
    exact one_ne_zero h2
  have ht2 : t ≠ t⁻¹ := by
    intro h2
    have h3 : zmodPowHom hζ (Multiplicative.ofAdd (2 : ZMod p)) = 1 := by
      have e : Multiplicative.ofAdd (2 : ZMod p) =
          Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 := by
        rw [← ofAdd_add, one_add_one_eq_two]
      rw [e, map_mul, ← ht]
      nth_rewrite 2 [h2]
      exact mul_inv_cancel t
    have h4 := congrArg Multiplicative.toAdd ((zmodPowHom_eq_one_iff hζ hζo).mp h3)
    simp only [toAdd_ofAdd, toAdd_one] at h4
    exact SpCoord.coord_two_ne_zero hp hp2 h4
  rcases x with a | a <;> rcases y with b | b
  · by_cases hba : b = a
    · rw [hba]
    · exfalso
      have h1 := h (Pi.mulSingle a (Multiplicative.ofAdd 1))
      simp only [pairedUnits, Sum.elim_inl, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hba,
        map_one, ← ht] at h1
      exact ht1 h1
  · exfalso
    have h1 := h (Pi.mulSingle a (Multiplicative.ofAdd 1))
    by_cases hba : b = a
    · subst hba
      simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same, ← ht] at h1
      exact ht2 h1
    · simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne hba, map_one, inv_one, ← ht] at h1
      exact ht1 h1
  · exfalso
    have h1 := h (Pi.mulSingle a (Multiplicative.ofAdd 1))
    by_cases hba : b = a
    · subst hba
      simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same, ← ht] at h1
      exact ht2 h1.symm
    · simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne hba, map_one, ← ht] at h1
      exact ht1 (inv_eq_one.mp h1)
  · by_cases hba : b = a
    · rw [hba]
    · exfalso
      have h1 := h (Pi.mulSingle a (Multiplicative.ofAdd 1))
      simp only [pairedUnits, Sum.elim_inr, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hba,
        map_one, inv_one, ← ht] at h1
      exact ht1 (inv_eq_one.mp h1)

theorem conj_mem_spRootGroup_of_commute [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {g : LargeEvenSpGroup K m}
    (hg : ∀ f : Fin m → Multiplicative (ZMod p),
      (g : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ f = spTorusGL hζ f * (g : GL (Fin m ⊕ Fin m) K))
    (i₀ : Fin m) {v : LargeEvenProj (LargeEvenSpGroup K m)} (hv : v ∈ spRootGroup i₀) :
    LargeEvenProjMk _ g * v * (LargeEvenProjMk _ g)⁻¹ ∈ spRootGroup i₀ := by
  classical
  have hdiag : ∀ h : GL (Fin m ⊕ Fin m) K,
      (∀ f : Fin m → Multiplicative (ZMod p), h * spTorusGL hζ f = spTorusGL hζ f * h) →
      (h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        Matrix.diagonal fun z => (h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) z z := by
    intro h hh
    ext y z
    by_cases hyz : y = z
    · subst hyz
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hyz]
      by_contra hne
      exact hyz (eq_of_pairedUnits_eq hp hp2 hζo hζ (x := z) (y := y) fun f =>
        ReflSp.pairedUnits_eq_of_mul_eq hζ (hh f) hne).symm
  have hginv : ∀ f : Fin m → Multiplicative (ZMod p), (g : GL (Fin m ⊕ Fin m) K)⁻¹ *
      spTorusGL hζ f = spTorusGL hζ f * (g : GL (Fin m ⊕ Fin m) K)⁻¹ := by
    intro f
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg f, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨d, hd⟩ : ∃ d : Fin m ⊕ Fin m → K,
      ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        Matrix.diagonal d := ⟨_, hdiag _ hg⟩
  obtain ⟨e, he⟩ : ∃ e : Fin m ⊕ Fin m → K,
      (((g : GL (Fin m ⊕ Fin m) K)⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal e := ⟨_, hdiag _ hginv⟩
  have hde : ∀ z, d z * e z = 1 := by
    intro z
    have h1 := congrFun (congrFun (Units.mul_inv (g : GL (Fin m ⊕ Fin m) K)) z) z
    rw [hd, he, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h1
    exact h1
  obtain ⟨a, rfl⟩ := hv
  refine ⟨Multiplicative.ofAdd (d (Sum.inl i₀) * Multiplicative.toAdd a * e (Sum.inr i₀)), ?_⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
    spRootSp_coe, spRootSp_coe, spRootGL_coe, spRootGL_coe, hd, he,
    TauCeti.diagonal_mul_transvection_mul_diagonal hde, toAdd_ofAdd]

end Root

theorem ggInnerDiagBound_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGInnerDiagBound p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro Eb Eh hEbI hEbA hr h3 hle hEhA _ _
  have : NeZero m := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hinj := mulAut_conj_injective (center_spProj_eq_bot (K := K) (m := m))
  set E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) := Eb.comap MulAut.conj with hEdef
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun e he => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEbA a.2 b.2
    · rw [map_pow, map_one]
      exact hEbA.2 _ he
  have hmap : E.map MulAut.conj = Eb := by
    rw [hEdef, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact sp_I_subset_inn (hEbI hφ)
  have hEcard : Nat.card E = Nat.card Eb := by
    rw [← hmap, Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv]
  have hrE : p ^ m ≤ Nat.card E := by
    rw [hEcard]
    exact hr
  have h3E : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact h3
  have hEm : Nat.card E ≤ p ^ m := card_le_of_isElemAbelian_spProj hp hp2 hpq hEab
  have hm3 : 3 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3E.trans hEm)
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨x, hτE, -⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hEab hrE
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  refine ⟨(spRootGroup (K := K) i₀).map (MulAut.conj x).toMonoidHom,
    fun hbot => spRootGroup_ne_bot (K := K) i₀
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x).injective).mp hbot),
    (spRootGroup_isPGroup (K := K) i₀).map _, ?_⟩
  intro φ hφ u hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have hfix : ∀ e ∈ E, φ e = e := by
    intro e he
    apply hinj
    have hc : φ * MulAut.conj e = MulAut.conj e * φ :=
      TableB.IsElemAbelian.comm hEhA hφ (hle he)
    ext y
    have h1 := congrArg (fun ψ : MulAut (LargeEvenProj (LargeEvenSpGroup K m)) => ψ (φ.symm y)) hc
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact h1
  obtain ⟨s, σ, c, -, hc, hφeq, hform⟩ := exists_conj_pow_of_aut hm3 hζo hζ x φ
  have hc1 : (c : ZMod p) = 1 := natCast_eq_one_of_pow_eq_one (m := m) hp hp2 hζo hζ hc (by
    rw [← hφeq]
    exact hEhA.2 φ hφ)
  have hrc : ∀ f, (s * fieldAutR m σ x * x⁻¹) * (x * spTorus hζ f * x⁻¹) *
      (s * fieldAutR m σ x * x⁻¹)⁻¹ = x * spTorus hζ f * x⁻¹ := by
    intro f
    have h1 := hform f
    rw [hfix _ (hτE f), pow_eq_self_of_natCast_eq_one hc1 (hEab.2 _ (hτE f))] at h1
    exact h1.symm
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin m ⊕ Fin m) K).subgroupOf (LargeEvenSpGroup K m))
    (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x)
  have hcomm : ∀ f : Fin m → Multiplicative (ZMod p), (g₀ : GL (Fin m ⊕ Fin m) K) *
      spTorusGL hζ f = spTorusGL hζ f * (g₀ : GL (Fin m ⊕ Fin m) K) := by
    intro f
    have h1 : (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x) * spTorus hζ f *
        (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x)⁻¹ = spTorus hζ f := by
      calc (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x) * spTorus hζ f *
            (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x)⁻¹ =
            x⁻¹ * ((s * fieldAutR m σ x * x⁻¹) * (x * spTorus hζ f * x⁻¹) *
              (s * fieldAutR m σ x * x⁻¹)⁻¹) * x := by group
        _ = spTorus hζ f := by
          rw [hrc f]
          group
    have h2 : g₀ * spTorusSp hζ f * g₀⁻¹ = spTorusSp hζ f := by
      apply hπi
      rw [map_mul, map_mul, map_inv]
      exact (congrArg (fun y => y * spTorus hζ f * y⁻¹) hg₀).trans h1
    have h4 := congrArg (fun y : LargeEvenSpGroup K m => (y : GL (Fin m ⊕ Fin m) K)) h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe] at h4
    calc (g₀ : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ f =
          ((g₀ : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ f * (g₀ : GL (Fin m ⊕ Fin m) K)⁻¹) *
            (g₀ : GL (Fin m ⊕ Fin m) K) := by group
      _ = spTorusGL hζ f * (g₀ : GL (Fin m ⊕ Fin m) K) := by rw [h4]
  have hu₁ := fieldAutR_mem_spRootGroup σ i₀ hu₀
  have hu₂ := conj_mem_spRootGroup_of_commute hp hp2 hζo hζ hcomm i₀ hu₁
  refine ⟨_, hu₂, ?_⟩
  have hg₀' : LargeEvenProjMk (LargeEvenSpGroup K m) g₀ =
      x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x := hg₀
  change x * (LargeEvenProjMk _ g₀ * fieldAutR m σ u₀ * (LargeEvenProjMk _ g₀)⁻¹) * x⁻¹ =
    φ (x * u₀ * x⁻¹)
  rw [hφeq, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hg₀']
  group

end CorFourTwoSp

end CFSG.StandardType

end
