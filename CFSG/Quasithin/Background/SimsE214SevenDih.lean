module

public import CFSG.Quasithin.Background.SimsE214SevenSec
public import CFSG.Quasithin.Background.SmithB45SzNat

public section

namespace CFSG.Quasithin.SimsE2

namespace E214S

open CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

theorem eq_zero_or_one_of_card_two {D : Type*} [Field D] [Finite D] (hD : Nat.card D = 2)
    (x : D) : x = 0 ∨ x = 1 := by
  classical
  by_contra hx
  push Not at hx
  have := Fintype.ofFinite D
  have h3 : ({0, 1, x} : Finset D).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hx.1.symm]), Finset.card_pair (Ne.symm hx.2)]
  have h4 := Finset.card_le_univ ({0, 1, x} : Finset D)
  rw [h3, ← Nat.card_eq_fintype_card, hD] at h4
  omega

theorem eq_of_add_eq_zero_zmod {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {x y : W}
    (h : x + y = 0) : x = y := by
  have hyy : y + y = 0 := by
    rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 by decide, zero_smul]
  calc x = x + (y + y) := by rw [hyy, add_zero]
    _ = (x + y) + y := (add_assoc _ _ _).symm
    _ = y := by rw [h, zero_add]

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem Sec.isNaturalSection_of_dih5 {I P Z J : Subgroup Γ} (hS : Sec I P Z J)
    [(Z.subgroupOf P).Normal] [(J.subgroupOf I).Normal]
    (e : ↥I ⧸ J.subgroupOf I ≃* DihedralGroup 5)
    (hfaith : ∀ x ∈ I, (∀ u ∈ P, x * u * x⁻¹ * u⁻¹ ∈ Z) → x ∈ J)
    (hcard : Z.relIndex P = 16) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)),
      Nat.card F = 4 ∧ S ≤ CFSG.Open.StatedSL 2 F ∧ Nonempty (↥S ≃* DihedralGroup 5) ∧
        IsNaturalSection I P Z J S := by
  classical
  letI : CommGroup (↥P ⧸ Z.subgroupOf P) :=
    { (inferInstance : Group (↥P ⧸ Z.subgroupOf P)) with mul_comm := hS.comm_quot }
  let ρ : DihedralGroup 5 →* MulAut (↥P ⧸ Z.subgroupOf P) := hS.starAct.comp e.symm.toMonoidHom
  have hρ : ∀ i : I, ρ (e (i : ↥I ⧸ J.subgroupOf I)) = hS.act i := by
    intro i
    show hS.starAct (e.symm (e _)) = _
    rw [MulEquiv.symm_apply_apply, hS.starAct_mk]
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨i', rfl⟩ := e.surjective d
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective i'
    rw [hρ] at hd
    have hiJ : (i : Γ) ∈ J := hfaith i i.2 ((Dih.conjSecAut_eq_one_iff i).1 hd)
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hiJ
  have hirr : ∀ Y : Subgroup (↥P ⧸ Z.subgroupOf P), (∀ γ, ∀ q ∈ Y, ρ γ q ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    refine hS.irr_quot Y fun i q hq => ?_
    rw [← hρ]
    exact hY _ q hq
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hS.sq_quot
  let π : DihedralGroup 5 →* (W ≃ₗ[ZMod 2] W) := (binPsi θ).toMonoidHom.comp ρ
  have hπ : ∀ γ w, π γ w = binPsi θ (ρ γ) w := fun _ _ => rfl
  have hπinj : Function.Injective π := (binPsi θ).injective.comp hρinj
  have hπmul : ∀ g h w, π g (π h w) = π (g * h) w := fun g h w => by rw [map_mul]; rfl
  have hirrQ : ∀ Y : Subgroup (↥P ⧸ Z.subgroupOf P), (∀ l ∈ ρ.range, ∀ v ∈ Y, l v ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ :=
    fun Y hY => hirr Y fun γ q hq => hY _ ⟨γ, rfl⟩ q hq
  have hirrW : ∀ U : Submodule (ZMod 2) W, (∀ γ, ∀ u ∈ U, repOfG π γ u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirrQ U ?_
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩ u hu
    exact hU γ u hu
  have hWQ : Nat.card W = Nat.card (↥P ⧸ Z.subgroupOf P) :=
    (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
  have hW16 : Nat.card W = 16 := hWQ.trans hcard
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hW16]; norm_num)
  have : Fact (repOfG π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOfG π)).mpr ⟨inferInstance, hirrW⟩⟩
  set R := repOfG π with hR
  have hfinD : Finite (EndRing R) := finite_endRing R
  let ω : Module.End (ZMod 2) W :=
    (π (DihedralGroup.r 1)).toLinearMap + (π (DihedralGroup.r (-1))).toLinearMap
  have hωapp : ∀ v, ω v = π (DihedralGroup.r 1) v + π (DihedralGroup.r (-1)) v := fun _ => rfl
  have hωc : ∀ g v, ω (R g v) = R g (ω v) := by
    intro g v
    show π (DihedralGroup.r 1) (π g v) + π (DihedralGroup.r (-1)) (π g v) =
      π g (π (DihedralGroup.r 1) v + π (DihedralGroup.r (-1)) v)
    rw [map_add, hπmul, hπmul, hπmul, hπmul]
    rcases g with i | i
    · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r,
        DihedralGroup.r_mul_r, add_comm (1 : ZMod 5) i, add_comm (-1 : ZMod 5) i]
    · rw [DihedralGroup.r_mul_sr, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_r, add_comm (π (DihedralGroup.sr (i - 1)) v)]
      have e1 : i - -1 = i + 1 := by ring
      have e2 : i - 1 = i + -1 := by ring
      rw [e1, e2]
  obtain ⟨ψω, hψω⟩ := (mem_endRing_iff R ω).2 hωc
  have : Module.Finite (EndRing R) W := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) (EndRing R) := Module.Finite.of_finite
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank (ZMod 2) (EndRing R) = d := ⟨_, rfl⟩
  have hDcard : Nat.card (EndRing R) = 2 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing R)
    rw [hd, Nat.card_zmod] at this
    exact this
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank (EndRing R) W = n := ⟨_, rfl⟩
  have hWD : Nat.card W = 2 ^ (d * n) := by
    rw [natCard_eq_pow_finrank (ρ := R), hDcard, hn, ← pow_mul]
  have hdn : d * n = 4 := by
    rw [hW16] at hWD
    exact Nat.pow_right_injective le_rfl (hWD.symm.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
  have hd4 : d = 1 ∨ d = 2 ∨ d = 4 := by
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨n, hdn.symm⟩
    interval_cases d <;> omega
  have hmatinj : ∀ {m : ℕ} (b : Module.Basis (Fin m) (EndRing R) W),
      Function.Injective (matRep b) := by
    intro m b g h hgh
    apply hπinj
    apply LinearEquiv.ext
    intro w
    have h0 : LinearMap.toMatrix b b (repD R g) = LinearMap.toMatrix b b (repD R h) := hgh
    have h1 : repD R g = repD R h := (LinearMap.toMatrix b b).injective h0
    have h2 := congrArg (fun f : Module.End (EndRing R) W => f w) h1
    exact h2
  rcases hd4 with h1 | h2 | h4
  ·
    exfalso
    have hD2 : Nat.card (EndRing R) = 2 := by rw [hDcard, h1, pow_one]
    rcases eq_zero_or_one_of_card_two hD2 ψω with h0 | h0
    ·
      have hω0 : ∀ v, π (DihedralGroup.r 1) v = π (DihedralGroup.r (-1)) v := by
        intro v
        have h := congrFun hψω v
        rw [h0, LinearMap.zero_apply, hωapp] at h
        exact eq_of_add_eq_zero_zmod h.symm
      have h3 := hπinj (LinearEquiv.ext hω0)
      exact absurd (DihedralGroup.r.inj h3) (by decide)
    ·
      have hω1 : ∀ v, π (DihedralGroup.r 1) v + π (DihedralGroup.r (-1)) v = v := by
        intro v
        have h := congrFun hψω v
        rw [h0, Module.End.one_apply, hωapp] at h
        exact h.symm
      have hT : ∀ (a b : ZMod 5) v, π (DihedralGroup.r a) (π (DihedralGroup.r b) v) =
          π (DihedralGroup.r (a + b)) v := fun a b v => by rw [hπmul, DihedralGroup.r_mul_r]
      have h3 : π (DihedralGroup.r 3) = π 1 := by
        have hxx : ∀ x : W, x + x = 0 := fun x => by
          rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]
        have hneg : ∀ x : W, -x = x := fun x => neg_eq_of_add_eq_zero_left (hxx x)
        have hone : ∀ x : W, (1 : W ≃ₗ[ZMod 2] W) x = x := fun _ => rfl
        apply LinearEquiv.ext
        intro v
        have ha := hω1 (π (DihedralGroup.r 1) v)
        have hb := hω1 (π (DihedralGroup.r 2) v)
        rw [hT, hT, show (1 : ZMod 5) + 1 = 2 by decide, show (-1 : ZMod 5) + 1 = 0 by decide,
          DihedralGroup.r_zero, map_one, hone] at ha
        rw [hT, hT, show (1 : ZMod 5) + 2 = 3 by decide, show (-1 : ZMod 5) + 2 = 1 by decide] at hb
        rw [map_one, hone, eq_sub_of_add_eq hb, sub_eq_add_neg, hneg, eq_sub_of_add_eq ha,
          sub_eq_add_neg, hneg, add_comm (π (DihedralGroup.r 1) v) v, add_assoc, hxx, add_zero]
      have h4 := hπinj h3
      rw [← DihedralGroup.r_zero] at h4
      exact absurd (DihedralGroup.r.inj h4) (by decide)
  ·
    have hn2 : n = 2 := by
      rw [h2] at hdn
      omega
    have hD4 : Nat.card (EndRing R) = 4 := by rw [hDcard, h2]; norm_num
    let b : Module.Basis (Fin 2) (EndRing R) W :=
      Module.finBasisOfFinrankEq (EndRing R) W (hn.trans hn2)
    have hcoord : ∀ g w, b.equivFun (π g w) = (matRep b g).mulVec (b.equivFun w) := fun g w =>
      (LinearMap.toMatrix_mulVec_repr b b (repD R g) w).symm
    let Mu : DihedralGroup 5 →* Matrix.GeneralLinearGroup (Fin 2) (EndRing R) :=
      (matRep b).toHomUnits
    have hMuinj : Function.Injective Mu := fun g h hgh =>
      hmatinj b (congrArg Units.val hgh)
    let S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (EndRing R)) := Mu.range
    have hSSL : S ≤ CFSG.Open.StatedSL 2 (EndRing R) := by
      rintro _ ⟨g, rfl⟩
      refine Subgroup.subset_closure ?_
      have hg10 : g ^ 10 = 1 := by
        have := pow_card_eq_one' (G := DihedralGroup 5) (x := g)
        rwa [DihedralGroup.nat_card] at this
      set u := Matrix.GeneralLinearGroup.det (Mu g) with hu
      have hu10 : u ^ 10 = 1 := by rw [hu, ← map_pow, ← map_pow, hg10, map_one, map_one]
      have hu3 : u ^ 3 = 1 := by
        have := pow_card_eq_one' (G := (EndRing R)ˣ) (x := u)
        rwa [Nat.card_units, hD4] at this
      have hu1 : u = 1 := by
        have := (pow_gcd_eq_one (a := u) (m := 10) (n := 3)).2 ⟨hu10, hu3⟩
        simpa using this
      have h5 := congrArg Units.val hu1
      rw [hu, Matrix.GeneralLinearGroup.val_det_apply] at h5
      exact h5
    refine ⟨EndRing R, inferInstance, inferInstance, S, hD4, hSSL,
      ⟨(MonoidHom.ofInjective hMuinj).symm⟩, ?_⟩
    let ρI : ↥I →* ↥S :=
      Mu.rangeRestrict.comp (e.toMonoidHom.comp (QuotientGroup.mk' (J.subgroupOf I)))
    have hρI : ∀ i : I, ((ρI i : ↥S) : Matrix.GeneralLinearGroup (Fin 2) (EndRing R)) =
        Mu (e (i : ↥I ⧸ J.subgroupOf I)) := fun _ => rfl
    let ψ : ↥P →* Multiplicative (Fin 2 → EndRing R) :=
      ((AddEquiv.toMultiplicative b.equivFun.toAddEquiv).toMonoidHom.comp θ.toMonoidHom).comp
        (QuotientGroup.mk' (Z.subgroupOf P))
    have hψ : ∀ u : P, ψ u =
        Multiplicative.ofAdd (b.equivFun (Multiplicative.toAdd (θ (u : ↥P ⧸ Z.subgroupOf P)))) :=
      fun _ => rfl
    refine ⟨hS.ZP, hS.JI, hS.IP, hS.IZ, ρI, ψ,
      (MonoidHom.rangeRestrict_surjective Mu).comp
        (e.surjective.comp (QuotientGroup.mk'_surjective _)), ?_, ?_, ?_, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h1 : Mu (e (x : ↥I ⧸ J.subgroupOf I)) = 1 := by
          rw [← hρI, h]
          rfl
        rw [(injective_iff_map_eq_one' Mu).1 hMuinj, MulEquiv.map_eq_one_iff,
          QuotientGroup.eq_one_iff] at h1
        exact h1
      · intro h
        apply Subtype.ext
        rw [hρI, (QuotientGroup.eq_one_iff x).2 h, map_one, map_one]
        rfl
    · intro y
      obtain ⟨q, hq⟩ := θ.surjective
        (Multiplicative.ofAdd (b.equivFun.symm (Multiplicative.toAdd y)))
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨u, ?_⟩
      rw [hψ, hq, toAdd_ofAdd, LinearEquiv.apply_symm_apply, ofAdd_toAdd]
    · ext u
      rw [MonoidHom.mem_ker, hψ, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq,
        ← map_zero b.equivFun, b.equivFun.injective.eq_iff, ← toAdd_one,
        Multiplicative.toAdd.apply_eq_iff_eq, MulEquiv.map_eq_one_iff, Sec.mk_eq_one_iff,
        Subgroup.mem_subgroupOf]
    · intro i u v huv
      have hv : v = ⟨(i : Γ) * u * (i : Γ)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hS.IP i.2) u).mp u.2⟩ := Subtype.ext huv
      have hmk : (v : ↥P ⧸ Z.subgroupOf P) =
          ρ (e (i : ↥I ⧸ J.subgroupOf I)) (u : ↥P ⧸ Z.subgroupOf P) := by
        rw [hρ, hS.act_mk, hv]
      rw [hψ, hψ, toAdd_ofAdd, hρI, hmk, ← B42L2.toAdd_binPsi θ, ← hπ, hcoord]
      rfl
  ·
    exfalso
    have hn1 : n = 1 := by
      rw [h4] at hdn
      omega
    let b : Module.Basis (Fin 1) (EndRing R) W :=
      Module.finBasisOfFinrankEq (EndRing R) W (hn.trans hn1)
    have hcomm : matRep b (DihedralGroup.r 1) * matRep b (DihedralGroup.sr 0) =
        matRep b (DihedralGroup.sr 0) * matRep b (DihedralGroup.r 1) := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
        Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]
    have h5 := hmatinj b (show matRep b (DihedralGroup.r 1 * DihedralGroup.sr 0) =
      matRep b (DihedralGroup.sr 0 * DihedralGroup.r 1) by rw [map_mul, map_mul, hcomm])
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h5
    exact absurd (DihedralGroup.sr.inj h5) (by decide)

end E214S

end CFSG.Quasithin.SimsE2
