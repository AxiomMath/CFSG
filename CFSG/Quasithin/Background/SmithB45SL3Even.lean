module

public import CFSG.Quasithin.Background.SmithB45SL3Row
public import CFSG.Quasithin.Background.SmithB45SL3Excl
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.SmithB42SL3Nat

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.H
open CFSG.Quasithin.B42SL3 (natSecOf)
open scoped Matrix

section Natural

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qOf_le_half_of_natural (hV : ∀ v : V, v ^ 2 = 1) (hLG : L ≤ G) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (π : ↥(StatedSL 3 K) →* ↥L) (hπ : Function.Surjective π)
    (e : V ≃* StdMod (Fin 3) K)
    (he : ∀ (γ : ↥(StatedSL 3 K)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 K) γ (e v)) :
    qOf G ≤ (((1 / 2 : ℚ)) : WithTop ℚ) := by
  classical
  set c := natSecOf π hπ e he with hc
  have hstab : L ≤ stabSub (⊤ : Subgroup V) := fun _ _ _ => Iff.rfl
  have hVcard : Nat.card V = Nat.card K ^ 3 := by
    rw [Nat.card_congr e.toEquiv, card_stdMod, Fintype.card_fin]
  have hfix : ∀ {B : Subgroup (MulAut V)}, B ≤ L →
      Nat.card ↥(fixV B) = Nat.card (B5.fixK (c.pre B)) := by
    intro B hBL
    rw [← c.card_inf_fixV hstab hBL, top_inf_eq]
  set D := B5.axisSub (B42SL3.plane K) with hD
  set B₀ : Subgroup (MulAut V) := D.map (L.subtype.comp π) with hB₀
  have hB₀L : B₀ ≤ L := by
    rintro _ ⟨γ, -, rfl⟩
    exact (π γ).2
  have hpre : c.pre B₀ = D := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨δ, hδ, hδγ⟩ := hγ
      have hδγ' : π δ = π γ := Subtype.ext hδγ
      have : δ = γ := c.hπ.1 hδγ'
      exact this ▸ hδ
    · intro hγ
      exact ⟨γ, hγ, rfl⟩
  have hDcard : Nat.card D = Nat.card K ^ 2 := B5.card_axisSub B42SL3.finrank_plane
  have hcardB₀ : Nat.card B₀ = Nat.card K ^ 2 := by
    rw [← c.card_pre hB₀L, hpre, hDcard]
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hcardB₀
    have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) Finite.one_lt_card
    omega
  have hB₀el : IsElemAbelian2 B₀ := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
      have := congrArg (fun g => ((π g : ↥L) : MulAut V)) (B5.axisSub_comm hγ hδ)
      simp only [map_mul, Subgroup.coe_mul] at this
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using this
    · rintro _ ⟨γ, hγ, rfl⟩
      have := congrArg (fun g => ((π g : ↥L) : MulAut V)) (B5.axisSub_mul_self hγ)
      simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at this
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [pow_two]
      exact this
  have hfixB₀ : Nat.card ↥(fixV B₀) = Nat.card K ^ 2 := by
    rw [hfix hB₀L, hpre]
    have hne : D ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hDcard
      have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) Finite.one_lt_card
      omega
    rw [B5.fixK_eq_of_le_axisSub B42SL3.finrank_plane le_rfl hne,
      Module.natCard_eq_pow_finrank (K := K) (V := B42SL3.plane K), B42SL3.finrank_plane]
  have hr : rAV B₀ = 1 / 2 := by
    have h1 := rk_add_rkIdx (fixV B₀)
    have hrkV : rk V = 3 * n := by
      unfold rk
      rw [hVcard, hK, ← pow_mul, padicValNat.prime_pow]
      ring
    have hrkF : rk ↥(fixV B₀) = 2 * n := by
      unfold rk
      rw [hfixB₀, hK, ← pow_mul, padicValNat.prime_pow]
      ring
    have hrkB : rk ↥B₀ = 2 * n := by
      unfold rk
      rw [hcardB₀, hK, ← pow_mul, padicValNat.prime_pow]
      ring
    unfold rAV
    rw [hrkB, show rkIdx (fixV B₀) = n by omega]
    have : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  have hA2 : IsA2 G B₀ := ⟨hB₀L.trans hLG, hB₀ne, hB₀el⟩
  obtain ⟨B, -, hB, hBr⟩ := exists_offender_rAV_le hV hA2 (by rw [hr]; norm_num)
  obtain ⟨A₀, hle, hmin⟩ := B1.exists_isFFStarMin_le hB
  have hquad : IsQuadratic A₀ := B1_4_3 hV hmin
  have hr0 : rAV A₀ ≤ rAV B :=
    rAV_le_of_card_le hV hB.isA2 hle.1 hle.2.2.1 (B1_4_1 hV hB) (le_of_eq hle.2.2.2.symm)
  exact qOf_le_iff.2 ⟨A₀, hmin.1.isA2, hquad, (hr0.trans hBr).trans hr.le⟩

end Natural

section Binary

open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

theorem rk_rkIdx_of_binary (θ : V ≃* Multiplicative W) (A : Subgroup (MulAut V)) {mA : ℕ}
    (hmA : Nat.card ↥(A.map (binPsi θ).toMonoidHom) = 2 ^ mA) :
    rk ↥A = mA ∧ rkIdx (fixV A) = Module.finrank (ZMod 2) W -
      Module.finrank (ZMod 2) (fixOf (A.map (binPsi θ).toMonoidHom)) := by
  have hcardA : Nat.card ↥A = 2 ^ mA := by
    rw [← hmA, Subgroup.card_map_of_injective (binPsi θ).injective]
  have hfix : Nat.card ↥(fixV A) =
      2 ^ Module.finrank (ZMod 2) (fixOf (A.map (binPsi θ).toMonoidHom)) := by
    rw [← B42SL3.card_fix_map θ A, card_fix_eq]
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) W := by
    rw [natCard_eq θ, CFSG.QuasithinUnique.Setup.X7.natCard_eq_two_pow_finrank]
  refine ⟨by unfold rk; rw [hcardA, padicValNat.prime_pow], ?_⟩
  have h := rk_add_rkIdx (fixV A)
  have hrkF : rk ↥(fixV A) = Module.finrank (ZMod 2) (fixOf (A.map (binPsi θ).toMonoidHom)) := by
    unfold rk
    rw [hfix, padicValNat.prime_pow]
  have hrkV : rk V = Module.finrank (ZMod 2) W := by
    unfold rk
    rw [hV, padicValNat.prime_pow]
  omega

end Binary

end B45SL3


open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.B45SL3 CFSG.Quasithin.H
open CFSG.Quasithin.H.L3Nine (HMod rho rhoT img norm mat)
open CFSG.Quasithin.B42SL3 (innerPart exists_lift_of_inner)
open scoped MatrixGroups Matrix

theorem asB45L3Even_holds :
    AsB45L3Even := by
  classical
  intro V _ _ hV G L hHyp hP hq1 hq2
  obtain ⟨f, hf, hmodel⟩ := hP
  obtain ⟨-, F, _, _, φ₀, hFcard, hcov⟩ := B42SL3.exists_cover hV hHyp (by omega) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set ρ := B42SL3.repOf θ φ₀ with hρ
  have hker := B42SL3.repOf_ker θ hcov
  have hirr := B42SL3.repOf_irreducible θ hirrV hcov.surjective
  have hnt : ∃ x, ρ x ≠ 1 := ⟨up3 0 0 1, fun h => by
    obtain ⟨c, -, hc⟩ := hker _ h
    exact not_scalar_up3 (F := F) ⟨(c : F), hc⟩⟩
  have hLG : L ≤ G := hHyp.2.1 ▸ quasithinGenFitting_le G
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B42L2.le_normalizer_of_b4Hyp hHyp
  let bas := Module.finBasis (ZMod 2) W
  obtain ⟨a, b, Wj, hne, hWirr, heq, -, hO, hsd⟩ := exists_label_pkg hF (by omega) ρ bas hirr hnt
  obtain ⟨e₀⟩ := heq 0
  have htrW : ∀ {B : Subgroup (MulAut V)}, IsA2 G B →
      CFSG.IsElementaryAbelian 2 ↥(B.map (binPsi θ).toMonoidHom) ∧
        B.map (binPsi θ).toMonoidHom ≠ ⊥ ∧
        ∀ x ∈ B.map (binPsi θ).toMonoidHom, ∀ y : SL(3, F), ∃ z, Intertwines ρ x y z := by
    intro B hB
    refine ⟨(isElemAbelian2_iff_map θ B).1 hB.2.2, ?_,
      B42SL3.intertwines_map θ hcov.surjective (hB.1.trans hGN)⟩
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective B (binPsi θ).injective]
    exact hB.2.1
  obtain ⟨A, hA2, -, hAr⟩ := kq_le_iff.1 hq2
  obtain ⟨hAWel, hAWne, hAWn⟩ := htrW hA2
  have h2F : Nat.card W ≤ Nat.card ↥(A.map (binPsi θ).toMonoidHom) ^ 2 *
      Nat.card {w : W // ∀ x ∈ A.map (binPsi θ).toMonoidHom, x w = w} := by
    rw [B42SL3.card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective, ← natCard_eq θ]
    exact (rAV_le_two_iff hV hA2).1 hAr
  rcases natural_or_row ρ hker _ hAWn (by omega) hF hirr hAWne h2F bas hne (Wj 0) (hWirr 0) e₀
    hO with hnat | ⟨hS, hH, hlt⟩
  ·
    exfalso
    obtain ⟨ψ, hψ, E, hE⟩ :=
      B42SL3.exists_natural_of_single hF ρ bas hirr hnat.1 hnat.2 (Wj 0) e₀
    let ε := specialLinearGroupEquivStatedSL 3 F
    let π : ↥(StatedSL 3 F) →* ↥L := φ₀.comp (ψ.comp ε.symm.toMonoidHom)
    have hπ : Function.Surjective π := by
      intro l
      obtain ⟨x, rfl⟩ := hcov.surjective l
      exact ⟨ε (ψ x), by simp [π, hψ]⟩
    let e : V ≃* H.StdMod (Fin 3) F := θ.trans (AddEquiv.toMultiplicative E)
    have he : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
        e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 F) γ (e v) := by
      intro γ v
      obtain ⟨g, rfl⟩ := ε.surjective γ
      have h1 : π (ε g) = φ₀ (ψ g) := by simp [π]
      have h2 := B42SL3.repOf_toAdd θ φ₀ (ψ g) v
      show Multiplicative.ofAdd (E (Multiplicative.toAdd (θ (((π (ε g) : ↥L) : MulAut V) v)))) =
        Multiplicative.ofAdd ((((ε g : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ E (Multiplicative.toAdd (θ v)))
      rw [h1, ← h2, hE, hψ]
      rfl
    have hq := qOf_le_half_of_natural hV hLG (by omega) hFcard π hπ e he
    have h := hq1.trans_le ((qhatOf_le_qOf G).trans hq)
    exact absurd (WithTop.coe_lt_coe.mp h) (by norm_num)
  ·
    obtain ⟨m, hm, hfm, hK, ψ, hψ, E, hE⟩ := exists_herm_of_row hF ρ bas hirr hS hH hlt (Wj 0) e₀
    have hnsd : ¬ Nonempty (ρ.Equiv ρ.dual) := fun h => not_exists_swap_of_row hS hH hlt (hsd h)
    obtain ⟨m', i, i', hfm', hii', hi', hsi, hsame, hrest⟩ := exists_row_pos hS hH hlt
    have hmm : m = m' := by omega
    subst hmm
    have hfo : f ≤ 2 * (pairOrbit f (a, b)).card := by
      have hcov' := orbit_cover (by omega) (fun x : Bool × Bool => x.1 ≠ x.2) (a, b)
        (Finset.card_pos.mp (show 0 < cntS a b by omega))
      have : (feat (fun x : Bool × Bool => x.1 ≠ x.2) (a, b)).card = 2 := hS
      rw [this] at hcov'
      linarith
    have hR : 4 * m ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) := by
      have hsum := sum_rank_le hF (by omega) ρ bas (pairOrbit f (a, b)) hO (up3 0 0 1)
      have h4 : ∀ c ∈ pairOrbit f (a, b),
          4 ≤ (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank := by
        intro c hc
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hc
        have h := dim_le_two_mul_rank_tensorRep (F := F) ((shiftPair f)^[t] (a, b)).1
          ((shiftPair f)^[t] (a, b)).2
        have e1 : cntS ((shiftPair f)^[t] (a, b)).1 ((shiftPair f)^[t] (a, b)).2 = cntS a b :=
          card_feat_iterate (fun x : Bool × Bool => x.1 ≠ x.2) (a, b) t
        have e2 : cntH ((shiftPair f)^[t] (a, b)).1 ((shiftPair f)^[t] (a, b)).2 = cntH a b :=
          card_feat_iterate (fun x : Bool × Bool => x.1 = true ∧ x.2 = true) (a, b) t
        rw [e1, e2, hS, hH] at h
        norm_num at h
        omega
      have : 4 * (pairOrbit f (a, b)).card ≤
          ∑ c ∈ pairOrbit f (a, b), (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank := by
        calc 4 * (pairOrbit f (a, b)).card = ∑ _c ∈ pairOrbit f (a, b), 4 := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum h4
      omega
    let eV : V ≃* HMod m F := θ.trans E
    have heV : ∀ (g : SL(3, F)) (v : V),
        eV (((φ₀ g : ↥L) : MulAut V) v) = rho hK (ψ g) (eV v) := by
      intro g v
      have h1 : θ (((φ₀ g : ↥L) : MulAut V) v) =
          Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (θ v))) := by
        rw [B42SL3.repOf_toAdd]
        rfl
      show E (θ _) = rho hK (ψ g) (E (θ v))
      rw [h1, hE]
      rfl
    have hrho : ∀ g : SL(3, F), rho hK g = congrHom eV ((φ₀ (ψ g) : ↥L) : MulAut V) := by
      intro g
      refine MulEquiv.ext fun X => ?_
      rw [congrHom_apply, heV, hψ, MulEquiv.apply_symm_apply]
    have himg : img hK ≤ G.map (congrHom eV) := by
      rintro _ ⟨g, rfl⟩
      exact ⟨_, hLG (φ₀ (ψ g)).2, (hrho g).symm⟩
    have hLmap : L.map (congrHom eV) = img hK := by
      refine le_antisymm ?_ (fun x hx => ?_)
      · rintro _ ⟨l, hl, rfl⟩
        obtain ⟨s, hs⟩ := hcov.surjective ⟨l, hl⟩
        refine ⟨ψ s, ?_⟩
        rw [hrho, hψ, hs]
      · obtain ⟨g, rfl⟩ := hx
        exact ⟨_, (φ₀ (ψ g)).2, (hrho g).symm⟩
    have hnorm : G.map (congrHom eV) ≤ norm hK := by
      have h1 := Subgroup.map_mono (f := congrHom eV) hGN
      rwa [Subgroup.map_equiv_normalizer_eq L (MulAut.congr eV), hLmap] at h1
    let ε := specialLinearGroupEquivStatedSL 3 F
    let π : ↥(StatedSL 3 F) →* ↥L := φ₀.comp (ψ.comp ε.symm.toMonoidHom)
    have hπ : Function.Surjective π := by
      intro l
      obtain ⟨x, rfl⟩ := hcov.surjective l
      exact ⟨ε (ψ x), by simp [π, hψ]⟩
    have hπe : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
        eV (((π γ : ↥L) : MulAut V) v) = rhoT hK (γ : GL (Fin 3) F) (eV v) := by
      intro γ v
      rw [show π γ = φ₀ (ψ (ε.symm γ)) from rfl, heV, hψ]
      show rhoT hK (Matrix.SpecialLinearGroup.toGL (ε.symm γ)) (eV v) = _
      congr 2
      apply Units.ext
      show ((ε.symm γ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
      rw [← specialLinearGroupEquivStatedSL_coe 3 F (ε.symm γ), MulEquiv.apply_symm_apply]
    have hcard2 : Nat.card F = 2 ^ (2 * m) := by rw [hFcard, hfm]
    have hBNT : BinaryNineTensor L ⊤ ⊥ m := by
      refine ⟨F, inferInstance, inferInstance, inferInstance, hcard2, π,
        B42L2.realizesVia_of_secEquiv (FFModel.twistTensor_isActionModel m (StatedSL 3 F) hcard2)
          rfl π hπ eV fun (γ : ↥(StatedSL 3 F)) v => ?_⟩
      refine (congrArg (fun X : HMod m F => (X : Multiplicative (Matrix (Fin 3) (Fin 3) F)))
        (hπe γ v)).trans ?_
      change Multiplicative.ofAdd (H.L3Nine.tw m ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          (mat (eV v))) = Multiplicative.ofAdd (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          mat (eV v) * (CFSG.Quasithin.frobPow m ((γ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F))ᵀ)
      rw [H.L3Nine.frobPow_eq_conjM]
      rfl
    have hqhat : qhatOf G = ((5 / 4 : ℚ) : WithTop ℚ) := by
      refine le_antisymm (qhatOf_le_of_model hm hK eV himg) ?_
      show ((5 / 4 : ℚ) : WithTop ℚ) ≤ kq G 3
      rw [le_kq_iff]
      intro B hB _
      obtain ⟨hBel, hBne, hBn⟩ := htrW hB
      obtain ⟨mB, hmB⟩ := IsPGroup.iff_card.mp (isPGroup_two (B.map (binPsi θ).toMonoidHom))
      have h5 := five_mul_le_four_mul_codim ρ hker _ hBn (by omega) hF hirr hnsd hBne bas hS hH
        hfo hO hmB
      obtain ⟨hrk, hidx⟩ := rk_rkIdx_of_binary θ B hmB
      have hmB1 : 0 < mB := by rw [← hrk]; exact hB.rk_pos
      unfold rAV
      rw [hrk, hidx, le_div_iff₀ (by exact_mod_cast hmB1)]
      have : (5 * mB : ℚ) ≤ 4 * ((Module.finrank (ZMod 2) W -
          Module.finrank (ZMod 2) (fixOf (B.map (binPsi θ).toMonoidHom)) : ℕ) : ℚ) := by
        exact_mod_cast h5
      linarith
    have hq : ((2 : ℚ) : WithTop ℚ) < qOf G := by
      show ((2 : ℚ) : WithTop ℚ) < kq G 2
      rw [lt_kq_iff]
      intro B hB hB2
      have hBquad : IsQuadratic B := (isQuadratic_iff_commSeries_two B).2 hB2
      obtain ⟨hBel, hBne, hBn⟩ := htrW hB
      have hquadW := B42SL3.quad_map θ hBquad
      obtain ⟨mB, hmB⟩ := IsPGroup.iff_card.mp (isPGroup_two (B.map (binPsi θ).toMonoidHom))
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
        ((isPGroup_two (B.map (binPsi θ).toMonoidHom)).to_subgroup (innerPart ρ hker _ hBn))
      obtain ⟨hkA, -, -, -, hinner, -⟩ := codim_data ρ hker _ hBn (by omega) hF hirr hmB hk
      have he : mB ≤ k + 1 := by
        have h := B42SL3.card_le_two_mul_innerPart ρ hker _ hBn (by omega) hF hirr hnsd
        rw [hmB, hk] at h
        have h2 : 2 ^ mB ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
        exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
      have hkm : k ≤ m := by
        have h := card_innerPart_le_of_row ρ hker _ hBn hF (by omega) hm hK hirr hquadW bas hii'
          hi' hsi hsame hrest (Wj 0) e₀
        rw [hk] at h
        exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
      obtain ⟨hrk, hidx⟩ := rk_rkIdx_of_binary θ B hmB
      have hmB1 : 0 < mB := by rw [← hrk]; exact hB.rk_pos
      suffices hcod : 2 * mB < Module.finrank (ZMod 2) W -
          Module.finrank (ZMod 2) (fixOf (B.map (binPsi θ).toMonoidHom)) by
        unfold rAV
        rw [hrk, hidx, lt_div_iff₀ (by exact_mod_cast hmB1)]
        exact_mod_cast hcod
      have hcU := Submodule.finrank_le (fixOf (B.map (binPsi θ).toMonoidHom))
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      ·
        have hmB1' : mB = 1 := by omega
        obtain ⟨⟨xV, hxVB⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB.2.1
        have hxV1 : xV ≠ 1 := fun h => hx1 (Subtype.ext h)
        set x' := congrHom eV xV with hx'
        have hx'n : x' ∈ norm hK := hnorm ⟨xV, hB.1 hxVB, rfl⟩
        have hx'2 : x' * x' = 1 := by
          rw [hx', ← map_mul, ← pow_two, hB.2.2.2 xV hxVB, map_one]
        have hx'1 : x' ≠ 1 := fun h => hxV1 (congrHom_injective eV (h.trans (map_one _).symm))
        have hfix := H.L3Nine.card_fixV_le_of_involution hm hK hx'n hx'2 hx'1
        have hzp : (Subgroup.zpowers xV).map (congrHom eV) = Subgroup.zpowers x' :=
          MonoidHom.map_zpowers _ _
        have hle : Nat.card ↥(fixV B) ≤ 2 ^ (6 * m) := by
          have h1 : fixV B ≤ fixV (Subgroup.zpowers xV) := fun v hv y hy =>
            hv y ((Subgroup.zpowers_le.mpr hxVB) hy)
          have h2 := Subgroup.card_le_of_le h1
          rw [← hzp, fixV_map_congrHom, Subgroup.card_map_of_injective eV.injective] at hfix
          exact h2.trans hfix
        rw [← B42SL3.card_fix_map θ B, card_fix_eq] at hle
        have hc6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
        have hW9 : Module.finrank (ZMod 2) W = 9 * m := by
          have h1 := H.L3Nine.card_HMod hm hK
          rw [← Nat.card_congr eV.toEquiv, natCard_eq θ,
            CFSG.QuasithinUnique.Setup.X7.natCard_eq_two_pow_finrank] at h1
          exact (Nat.pow_right_injective le_rfl h1)
        omega
      ·
        have hI1 : 1 < Nat.card ↥(innerPart ρ hker _ hBn) := by
          rw [hk]
          exact Nat.one_lt_two_pow (by omega)
        have : Nontrivial ↥(innerPart ρ hker _ hBn) := Finite.one_lt_card_iff_nontrivial.mp hI1
        obtain ⟨⟨b₀, hb₀I⟩, hb₀1⟩ := exists_ne (1 : ↥(innerPart ρ hker _ hBn))
        obtain ⟨t, ht2, htρ⟩ := exists_lift_of_inner ρ hker _ hBn (by omega) hFcard hirr b₀ hb₀I
        have ht1 : t ≠ 1 := by
          intro h1
          apply hb₀1
          apply Subtype.ext
          apply Subtype.ext
          refine LinearEquiv.ext fun u => ?_
          rw [htρ u, h1, map_one]
          rfl
        obtain ⟨bV, hbVB, hbV⟩ := b₀.2
        have hbVt : bV = ((φ₀ t : ↥L) : MulAut V) := by
          apply (binPsi θ).injective
          refine LinearEquiv.ext fun u => ?_
          have h1 := htρ u
          rw [← hbV] at h1
          exact h1.trans (B42SL3.repOf_apply θ φ₀ t u)
        have hall : ∀ x : ↥(B.map (binPsi θ).toMonoidHom), x ∈ innerPart ρ hker _ hBn := by
          intro x
          obtain ⟨xV, hxVB, hxV⟩ := x.2
          set x' := congrHom eV xV with hx'
          have hx'n : x' ∈ norm hK := hnorm ⟨xV, hB.1 hxVB, rfl⟩
          have hx'2 : x' * x' = 1 := by
            rw [hx', ← map_mul, ← pow_two, hB.2.2.2 xV hxVB, map_one]
          have hq' : ∀ X : HMod m F, x' (rho hK (ψ t) X * X⁻¹) = rho hK (ψ t) X * X⁻¹ := by
            intro X
            obtain ⟨v, rfl⟩ := eV.surjective X
            rw [← heV, ← map_inv, ← map_mul, hx', congrHom_apply, MulEquiv.symm_apply_apply]
            congr 1
            rw [← hbVt]
            exact hBquad (Subgroup.subset_closure ⟨bV, hbVB, v, rfl⟩) xV hxVB
          have hψt1 : ψ t ≠ 1 := fun h => ht1 (by rw [← hψ t, h, map_one])
          have hψt2 : ψ t * ψ t = 1 := by rw [← map_mul, ht2, map_one]
          obtain ⟨s, hs⟩ := mem_img_of_quadratic hm hK hψt1 hψt2 hx'n hx'2 hq'
          have hxVs : xV = ((φ₀ (ψ s) : ↥L) : MulAut V) := by
            apply congrHom_injective eV
            rw [← hrho, hs]
          refine mem_innerPart_of_eq_rep ρ hker _ hBn x (ψ s) fun u => ?_
          rw [← hxV, hxVs]
          exact B42SL3.repOf_apply θ φ₀ (ψ s) u
        have hkmB : mB = k := by
          have h1 : innerPart ρ hker _ hBn = ⊤ := eq_top_iff.mpr fun x _ => hall x
          have h2 : Nat.card ↥(innerPart ρ hker _ hBn) =
              Nat.card ↥(B.map (binPsi θ).toMonoidHom) := by
            rw [h1, Subgroup.card_top]
          rw [hk, hmB] at h2
          exact (Nat.pow_right_injective le_rfl h2).symm
        have := hinner hk1
        omega
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, hBNT, hq, hqhat⟩)))))

end CFSG.Quasithin
