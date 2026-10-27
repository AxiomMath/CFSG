module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDescent
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.Harris.L2.Numerics
import CFSG.Quasithin.Background.Harris.L2.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Rep

variable {H : Type} [Group H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_rank8_sl2 {X : Type} [Group X] (hL : IsL2 X 3) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2), Fintype.card F = 2 ^ 3 ∧
      Nonempty (X ≃* SL(2, F)) := by
  obtain ⟨-, F, hF1, hF2, hFcard, hchar, ⟨e⟩⟩ := uc22p22g_isL2_psl hL
  letI : Fintype F := Fintype.ofFinite F
  exact ⟨F, hF1, inferInstance, hchar, by rw [← Nat.card_eq_fintype_card, hFcard],
    ⟨e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo⟩⟩

@[expose] def uc22p22r_rank8_rep {L : Subgroup H} {W : Submodule (ZMod 2) Vmod} (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W)
    {F : Type} [Field F] (e : ↥L ≃* SL(2, F)) : Representation (ZMod 2) SL(2, F) ↥W where
  toFun g := (ρ ((e.symm g : ↥L) : H)).restrict fun w hw => hW _ (e.symm g).2 w hw
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

theorem uc22p22r_rank8_rep_apply {L : Subgroup H} {W : Submodule (ZMod 2) Vmod} (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W)
    {F : Type} [Field F] (e : ↥L ≃* SL(2, F)) (g : SL(2, F)) (w : ↥W) :
    (uc22p22r_rank8_rep ρ hW e g w : Vmod) = ρ ((e.symm g : ↥L) : H) w :=
  rfl

theorem uc22p22r_rank8_card {L : Subgroup H} {W : Submodule (ZMod 2) Vmod} (h8 : SecIrr ρ L W ⊥ 8) :
    Nat.card ↥W = 2 ^ 8 := by
  have h2 : Nat.card ↥(⊥ : Submodule (ZMod 2) Vmod) = 1 := Nat.card_unique
  rw [h8.2.2.2.1, h2, mul_one]

theorem uc22p22r_rank8_rep_irr [Finite Vmod] {L : Subgroup H} {W : Submodule (ZMod 2) Vmod} {r : ℕ}
    (hr : 1 ≤ r) (h : SecIrr ρ L W ⊥ r) {F : Type} [Field F] (e : ↥L ≃* SL(2, F)) :
    (uc22p22r_rank8_rep ρ h.1 e).IsIrreducible := by
  have h2 : Nat.card ↥(⊥ : Submodule (ZMod 2) Vmod) = 1 := Nat.card_unique
  obtain ⟨hinv, -, -, hcard, hsimple⟩ := h
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨?_, fun U hU => ?_⟩
  · apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hcard, h2, mul_one]
    exact Nat.one_lt_two_pow (by omega)
  · have hinvU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (U.map W.subtype) := by
      rintro a ha _ ⟨u, hu, rfl⟩
      refine ⟨uc22p22r_rank8_rep ρ hinv e (e ⟨a, ha⟩) u, hU _ u hu, ?_⟩
      show ρ ((e.symm (e ⟨a, ha⟩) : ↥L) : H) u = ρ a u
      rw [MulEquiv.symm_apply_apply]
    rcases hsimple _ bot_le (Submodule.map_subtype_le W U) hinvU with h0 | h0
    · exact Or.inl (Submodule.map_injective_of_injective W.injective_subtype
        (h0.trans (Submodule.map_bot _).symm))
    · exact Or.inr (Submodule.map_injective_of_injective W.injective_subtype
        (h0.trans (Submodule.map_subtype_top W).symm))

theorem uc22p22r_rank8_cent_mem {L : Subgroup H} {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H))
    {w : Vmod} (hw : w ∈ commOn ρ L ⊤) : ρ c w ∈ commOn ρ L ⊤ := by
  have hL : L.map (MulAut.conj c).toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show c * y * c⁻¹ ∈ L
      rw [← Subgroup.mem_centralizer_iff.1 hc y hy, mul_inv_cancel_right]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      show c * x * c⁻¹ = x
      rw [← Subgroup.mem_centralizer_iff.1 hc x hx, mul_inv_cancel_right]
  have := uc22p22d_apply_commOn_le ρ L c hw
  rwa [hL] at this

end Rep

section Modules

variable {F : Type} [Field F]

theorem uc22p22r_rank8_exists_ne_one {G W : Type*} [Monoid G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) G W) (hσ : σ.IsIrreducible) (hW : 2 < Nat.card W) : ∃ g, σ g ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨-, hirr⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ).1 hσ
  have hW1 : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  rcases hirr (Submodule.span (ZMod 2) {w₀}) (fun g u hu => by simpa [h g] using hu) with h0 | h0
  · exact hw₀ (Submodule.span_singleton_eq_bot.1 h0)
  · have hsurj : Function.Surjective fun a : ZMod 2 => a • w₀ := fun w =>
      Submodule.mem_span_singleton.1 (by rw [h0]; exact Submodule.mem_top)
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_zmod] at this
    omega

theorem uc22p22r_rank8_eq_zero_or_one {R : Type*} [Ring R] [Nontrivial R] [Finite R] (h : Nat.card R = 2)
    (x : R) : x = 0 ∨ x = 1 := by
  classical
  letI : Fintype R := Fintype.ofFinite R
  by_contra hx
  push Not at hx
  have h3 : ({0, 1, x} : Finset R).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hx.2.symm
    · simp [zero_ne_one, hx.1.symm]
  have := Finset.card_le_univ ({0, 1, x} : Finset R)
  rw [h3, ← Nat.card_eq_fintype_card, h] at this
  omega

theorem uc22p22r_card_endRing_rank8 [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ 3) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (hW : Nat.card W = 2 ^ 8)
    (σ : Representation (ZMod 2) SL(2, F) W) [Fact σ.IsIrreducible] : Nat.card (EndRing σ) = 2 := by
  have hnt := uc22p22r_rank8_exists_ne_one σ Fact.out (by rw [hW]; norm_num)
  obtain ⟨d, hd1, hDcard, hb⟩ := binary_SL2_irreducible_Frobenius_descent (n := 3) (by norm_num) hF σ hnt
  haveI : Finite (EndRing σ) := finite_endRing σ
  haveI : Module.Finite (EndRing σ) W := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ := hb (Module.finBasis (EndRing σ) W)
  have hfinrank : Module.finrank (ZMod 2) W = 8 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod, hW] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have h1 : Module.finrank (ZMod 2) W = d * 2 ^ J.card := by
    rw [CFSG.Quasithin.G11.Harris.L2.finrank_eq_mul_of_card hDcard, hdim]
  have hnum := CFSG.Quasithin.G11.Harris.L2.l2_numerics (n := 3) (by norm_num) hd1 hJne hJn hshift
    (by omega)
  have hd : d = 1 := by
    rcases hnum with ⟨hJ1, hd3⟩ | ⟨-, hn⟩ | ⟨-, -, hd⟩
    · rw [hJ1, hd3] at h1
      norm_num at h1
      omega
    · omega
    · exact hd
  rw [hDcard, hd]
  rfl

theorem uc22p22r_rank8_fixRoot_coord {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) SL(2, F) W) [Fact σ.IsIrreducible] {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing σ) W) :
    Nat.card {w : W // ∀ t : F, σ (uElt t) w = w} =
      Nat.card {x : Fin m → EndRing σ // ∀ t : F, (matRep b (uElt t) - 1).mulVec x = 0} := by
  refine Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv fun w => forall_congr' fun t => ?_)
  have h1 := LinearMap.toMatrix_mulVec_repr b b (repD σ (uElt t)) w
  rw [repD_apply] at h1
  have h2 : (matRep b (uElt t) - 1).mulVec (b.equivFun w) = b.equivFun (σ (uElt t) w - w) := by
    rw [map_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Module.Basis.equivFun_apply,
      Module.Basis.equivFun_apply, ← h1]
    rfl
  rw [LinearEquiv.coe_toEquiv, h2, LinearEquiv.map_eq_zero_iff, sub_eq_zero]

theorem uc22p22r_rank8_fixRoot_ext [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (σ : Representation (ZMod 2) SL(2, F) W) [Fact σ.IsIrreducible] {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing σ) W) {E : Type} [Field E] [CharP E 2] [Algebra F E]
    (ιD : EndRing σ →+* E) {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n) (Φ : (matRepE b ιD).Equiv (frobTensor F E J)) :
    Nat.card {x : Fin m → E // ∀ t : F, ((matRep b (uElt t) - 1).map ιD).mulVec x = 0} = Nat.card E := by
  have hfix : ∀ x : Fin m → E, (∀ t : F, ((matRep b (uElt t) - 1).map ιD).mulVec x = 0) ↔
      ∃ c : E, Φ x = c • baseVec := by
    intro x
    rw [← tensorRep_fixed_iff hF (fun i : J => (i : ℕ)) Subtype.val_injective (fun i => hJn i i.2) (Φ x)]
    refine forall_congr' fun t => ?_
    have h1 : Φ (matRepE b ιD (uElt t) x) = tensorRep F E (fun i : J => (i : ℕ)) (uElt t) (Φ x) :=
      equiv_apply Φ (uElt t) x
    rw [Matrix.map_sub _ (map_sub ιD), Matrix.map_one _ (map_zero ιD) (map_one ιD), Matrix.sub_mulVec,
      Matrix.one_mulVec, ← matRepE_apply, sub_eq_zero, ← h1]
    exact ⟨fun h => by rw [h], fun h => Φ.toLinearEquiv.injective h⟩
  let f : E → {x : Fin m → E // ∀ t : F, ((matRep b (uElt t) - 1).map ιD).mulVec x = 0} := fun c =>
    ⟨Φ.symm (c • baseVec), (hfix _).2 ⟨c, Representation.Equiv.apply_symm_apply Φ _⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 := congrArg (fun y => Φ y.1) h
      simp only [f, Representation.Equiv.apply_symm_apply] at h1
      have h2 := congrFun h1 (fun _ => 0)
      simpa [baseVec_apply] using h2
    · rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ := (hfix x).1 hx
      refine ⟨c, Subtype.ext ?_⟩
      show Φ.symm (c • baseVec) = x
      rw [← hc, Representation.Equiv.symm_apply_apply]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem uc22p22r_rank8_card_fixRoot [Fintype F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (σ : Representation (ZMod 2) SL(2, F) W)
    [Fact σ.IsIrreducible] (hnt : ∃ g, σ g ≠ 1) :
    Nat.card {w : W // ∀ t : F, σ (uElt t) w = w} = Nat.card (EndRing σ) := by
  obtain ⟨d, -, -, hb⟩ := binary_SL2_irreducible_Frobenius_descent hn hF σ hnt
  haveI : Finite (EndRing σ) := finite_endRing σ
  haveI : Module.Finite (EndRing σ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing σ) W
  obtain ⟨E, _, _, _, ιF, ιD, J, -, hJn, hΦ, -, -⟩ := hb b
  letI := ιF.toAlgebra
  obtain ⟨Φ⟩ := hΦ
  have hbc := natCard_common_ker_map ιD fun t : F => matRep b (uElt t) - 1
  rw [uc22p22r_rank8_fixRoot_ext hF σ b ιD hJn Φ] at hbc
  letI := ιD.toAlgebra
  haveI : Module.Finite (EndRing σ) E := Module.Finite.of_finite
  have hE : Nat.card E = Nat.card (EndRing σ) ^ Module.finrank (EndRing σ) E := Module.natCard_eq_pow_finrank
  have hr : Module.finrank (EndRing σ) E ≠ 0 := Module.finrank_pos.ne'
  rw [hE] at hbc
  rw [uc22p22r_rank8_fixRoot_coord σ b]
  exact (Nat.pow_left_injective hr hbc).symm

end Modules

section Sylow

variable {H : Type} [Group H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_rank8_fixOn_sylow [Finite H] {L : Subgroup H} {W : Submodule (ZMod 2) Vmod}
    (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W) {F : Type} [Field F] [Fintype F] [CharP F 2] (e : ↥L ≃* SL(2, F))
    {U : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U L) :
    Nat.card ↥(fixOn ρ U W) = Nat.card {w : ↥W // ∀ t : F, uc22p22r_rank8_rep ρ hW e (uElt t) w = w} := by
  obtain ⟨Q, hQ⟩ := hU
  set σ := uc22p22r_rank8_rep ρ hW e with hσ
  set P : Sylow 2 SL(2, F) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup SL(2, F)) = (Q : Subgroup ↥L).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := sylow_conj_description (p := 2) P
  have hσe : ∀ (q : ↥L) (w : ↥W), σ (e q) w = w ↔ ρ (q : H) w = w := by
    intro q w
    rw [Subtype.ext_iff, hσ, uc22p22r_rank8_rep_apply, MulEquiv.symm_apply_apply]
  have hσmul : ∀ (x y : SL(2, F)) (w : ↥W), σ (x * y) w = σ x (σ y w) := fun x y w => by
    rw [map_mul, Module.End.mul_apply]
  have hσ1 : ∀ w : ↥W, σ 1 w = w := fun w => by rw [map_one, Module.End.one_apply]
  let τ : ↥W ≃ ↥W :=
    { toFun := σ g⁻¹
      invFun := σ g
      left_inv := fun w => by rw [← hσmul, mul_inv_cancel, hσ1]
      right_inv := fun w => by rw [← hσmul, inv_mul_cancel, hσ1] }
  have hiff : ∀ w : ↥W, (∀ u ∈ U, ρ u w = w) ↔ ∀ t : F, σ (uElt t) (τ w) = τ w := by
    intro w
    constructor
    · intro hfix t
      have hx : g * uElt t * g⁻¹ ∈ (P : Subgroup SL(2, F)) := by
        rw [hg, show g⁻¹ * (g * uElt t * g⁻¹) * g = uElt t by group]
        exact (mem_upperRootGroup_iff _).2 ⟨t, rfl⟩
      rw [hP] at hx
      obtain ⟨q, hq, hqx⟩ := hx
      have hqx' : e q = g * uElt t * g⁻¹ := hqx
      have hqU : (q : H) ∈ U := by
        rw [← hQ]
        exact ⟨q, hq, rfl⟩
      have h1 : σ (e q) w = w := (hσe q w).2 (hfix _ hqU)
      show σ (uElt t) (σ g⁻¹ w) = σ g⁻¹ w
      rw [← hσmul, show uElt t * g⁻¹ = g⁻¹ * (g * uElt t * g⁻¹) by group, hσmul, ← hqx', h1]
    · intro hfix u hu
      rw [← hQ] at hu
      obtain ⟨q, hq, rfl⟩ := hu
      have hx : e q ∈ (P : Subgroup SL(2, F)) := by
        rw [hP]
        exact ⟨q, hq, rfl⟩
      obtain ⟨t, ht⟩ := (mem_upperRootGroup_iff _).1 ((hg _).1 hx)
      have he : e q = g * uElt t * g⁻¹ := by
        rw [← ht]
        group
      refine (hσe q w).1 ?_
      have h2 : σ (uElt t) (σ g⁻¹ w) = σ g⁻¹ w := hfix t
      rw [he, hσmul, hσmul, h2, ← hσmul, mul_inv_cancel, hσ1]
  calc Nat.card ↥(fixOn ρ U W) = Nat.card {w : ↥W // ∀ u ∈ U, ρ u w = w} :=
        Nat.card_congr
          { toFun := fun y => ⟨⟨y.1, (mem_fixOn.1 y.2).1⟩, (mem_fixOn.1 y.2).2⟩
            invFun := fun w => ⟨w.1.1, mem_fixOn.2 ⟨w.1.2, w.2⟩⟩
            left_inv := fun y => rfl
            right_inv := fun w => rfl }
    _ = Nat.card {w : ↥W // ∀ t : F, σ (uElt t) w = w} := Nat.card_congr (Equiv.subtypeEquiv τ hiff)

end Sylow

section Main

variable {H : Type} [Group H] [Finite H] {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
  (ρ : Representation (ZMod 2) H Vmod)

theorem uc22p22r_F1W_rank8 {L : Subgroup H} (hL : IsL2 ↥L 3) (h8 : SecIrr ρ L (commOn ρ L ⊤) ⊥ 8)
    {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) : ∀ w ∈ commOn ρ L ⊤, ρ c w = w := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := uc22p22r_rank8_sl2 hL
  set σ := uc22p22r_rank8_rep ρ h8.1 e
  haveI : Fact σ.IsIrreducible := ⟨uc22p22r_rank8_rep_irr ρ (by norm_num) h8 e⟩
  have hcard := uc22p22r_rank8_card ρ h8
  haveI : Nontrivial ↥(commOn ρ L ⊤) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  haveI : Finite (EndRing σ) := finite_endRing σ
  have hkey := uc22p22r_rank8_eq_zero_or_one (uc22p22r_card_endRing_rank8 hF hcard σ)
  let φ : Module.End (ZMod 2) ↥(commOn ρ L ⊤) := (ρ c).restrict fun w hw => uc22p22r_rank8_cent_mem ρ hc hw
  have hcomm : ∀ g v, φ (σ g v) = σ g (φ v) := by
    intro g v
    apply Subtype.ext
    show ρ c (ρ ((e.symm g : ↥L) : H) v) = ρ ((e.symm g : ↥L) : H) (ρ c v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      Subgroup.mem_centralizer_iff.1 hc _ (e.symm g).2]
  obtain ⟨ψ, hψ⟩ := (mem_endRing_iff σ φ).2 hcomm
  have hψ0 : ψ ≠ 0 := by
    intro h0
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : ↥(commOn ρ L ⊤))
    apply hw₀
    have h1 : φ w₀ = 0 := by
      rw [← hψ, h0]
      rfl
    have h3 : ρ c (w₀ : Vmod) = 0 := congrArg Subtype.val h1
    have h2 : ρ c⁻¹ (ρ c (w₀ : Vmod)) = w₀ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [h3, map_zero] at h2
    exact Subtype.ext h2.symm
  have hψ1 : ψ = 1 := (hkey ψ).resolve_left hψ0
  intro w hw
  have h1 : φ ⟨w, hw⟩ = ⟨w, hw⟩ := by
    rw [← hψ, hψ1]
    rfl
  exact congrArg Subtype.val h1

theorem uc22p22r_card_fixOn_rank8 {L : Subgroup H} (hL : IsL2 ↥L 3) (h8 : SecIrr ρ L (commOn ρ L ⊤) ⊥ 8)
    {U : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U L) : Nat.card ↥(fixOn ρ U (commOn ρ L ⊤)) = 2 := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := uc22p22r_rank8_sl2 hL
  haveI hirr : Fact (uc22p22r_rank8_rep ρ h8.1 e).IsIrreducible := ⟨uc22p22r_rank8_rep_irr ρ (by norm_num) h8 e⟩
  have hcard := uc22p22r_rank8_card ρ h8
  have hnt := uc22p22r_rank8_exists_ne_one (uc22p22r_rank8_rep ρ h8.1 e) hirr.out (by rw [hcard]; norm_num)
  rw [uc22p22r_rank8_fixOn_sylow ρ h8.1 e hU, uc22p22r_rank8_card_fixRoot (n := 3) (by norm_num) hF _ hnt,
    uc22p22r_card_endRing_rank8 hF hcard (uc22p22r_rank8_rep ρ h8.1 e)]

theorem uc22p22r_F2W_rank8 {L : Subgroup H} (hL : IsL2 ↥L 3) (h8 : SecIrr ρ L (commOn ρ L ⊤) ⊥ 8)
    {U S₂ : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U L)
    (hS₂ : S₂ ≤ Subgroup.centralizer (L : Set H)) : ¬ Nat.card ↥(fixOn ρ (U ⊔ S₂) (commOn ρ L ⊤)) ≡ 1 [MOD 3] := by
  have heq : fixOn ρ (U ⊔ S₂) (commOn ρ L ⊤) = fixOn ρ U (commOn ρ L ⊤) := by
    ext w
    rw [mem_fixOn, mem_fixOn]
    refine ⟨fun h => ⟨h.1, fun a ha => h.2 a ((le_sup_left : U ≤ U ⊔ S₂) ha)⟩, fun h => ⟨h.1, ?_⟩⟩
    have hw : w ∈ fixSub ρ (U ⊔ S₂) := by
      rw [fixSub_sup]
      exact ⟨h.2, fun s hs => uc22p22r_F1W_rank8 ρ hL h8 (hS₂ hs) w h.1⟩
    exact hw
  rw [heq, uc22p22r_card_fixOn_rank8 ρ hL h8 hU]
  decide

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
