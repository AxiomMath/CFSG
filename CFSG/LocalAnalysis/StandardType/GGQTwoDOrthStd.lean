module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthStdAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthWin
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthNormIso

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.Open CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.RankThree.Classical2 (orthDerived)
open Multiplicative

section Std

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

theorem qtwoOrth_std_torus (hF : Nat.card Φ.F = 2) (m : ℕ) (hm : 3 ≤ m) (hr : Φ.r = m + 1) :
    ∃ (_ : Algebra Φ.F (GaloisField 2 2))
      (E : QuadExt Φ.F (GaloisField 2 2) (unitaryInvolution (GaloisField 2 2) 2 1))
      (χ : Φ.V ≃ₗ[Φ.F] (Fin (m + 1) → GaloisField 2 2))
      (ζ : normOne (unitaryInvolution (GaloisField 2 2) 2 1)), ζ ≠ 1 ∧
      (∀ v, Qn E (m + 1) (χ v) = Φ.Q v) ∧
      (∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
        χ (Φ.Δ.τ g v) = diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) (m + 1)
          (fun i => ζ ^ (toAdd (g (Fin.cast hr.symm i))).val) (χ v)) ∧
      (∀ k : Fin Φ.r, (Φ.rank1 (omStd Φ.r (by omega) k)).map
          (LinearEquiv.autCongr χ).toMonoidHom = qtwoStdU E m hm (Fin.cast hr k)) ∧
      (∀ k k' : Fin Φ.r, ggCoxeterMatrixD (m + 1) (Fin.cast hr k) (Fin.cast hr k') = 3 →
        (Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k')).map
          (LinearEquiv.autCongr χ).toMonoidHom =
          qtwoStdW E m hm (Fin.cast hr k) (Fin.cast hr k')) := by
  classical
  obtain ⟨inst, E₀, χ₀, ζ, hζ1, hζp, hχQ, hχτ⟩ := Φ.exists_normIso hF
  letI := inst
  let K := GaloisField 2 2
  let σ : K ≃+* K := unitaryInvolution K 2 1
  have hKcard : Nat.card K = 4 := by
    change Nat.card (GaloisField 2 2) = 4
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hp3 : p = 3 := Φ.p_eq_three hF
  have hcardNorm : Nat.card (normOne σ) = p := by
    rw [hp3]
    have h := CFSG.ClassicalInvolution.Phan.card_normOne (K := K) (p := 2) (f := 1) (by
      change Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num)
    rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num] at h
    simpa only [σ] using h
  let e : Fin (m + 1) ≃ Fin Φ.r := finCongr hr.symm
  let χ : Φ.V ≃ₗ[Φ.F] (Fin (m + 1) → K) :=
    χ₀.trans (LinearEquiv.funCongrLeft Φ.F K e)
  have h_e_cast : ∀ i : Fin Φ.r, e (Fin.cast hr i) = i := by
    intro i
    apply Fin.ext
    simp only [e, finCongr_apply_coe, Fin.val_cast]
  have h_cast_e : ∀ i : Fin (m + 1), Fin.cast hr (e i) = i := by
    intro i
    apply Fin.ext
    change (e i).val = i.val
    simp only [e, finCongr_apply_coe]
  have hQn_reindex : ∀ x : Fin Φ.r → K,
      Qn E₀ (m + 1) (LinearEquiv.funCongrLeft Φ.F K e x) = Qn E₀ Φ.r x := by
    intro x
    rw [Qn_apply, Qn_apply]
    simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    exact Equiv.sum_comp e (fun j => normQuad E₀ (x j))
  have hχQ' : ∀ v, Qn E₀ (m + 1) (χ v) = Φ.Q v := by
    intro v
    change Qn E₀ (m + 1) (LinearEquiv.funCongrLeft Φ.F K e (χ₀ v)) = Φ.Q v
    rw [hQn_reindex, hχQ v]
  let reindexHom : (Fin Φ.r → Multiplicative (ZMod p)) →*
      (Fin (m + 1) → Multiplicative (ZMod p)) :=
    { toFun := fun f i => f (e i)
      map_one' := rfl
      map_mul' := fun f g => rfl }
  let powHom : (Fin (m + 1) → Multiplicative (ZMod p)) →* (Fin (m + 1) → normOne σ) :=
    (TableBSymp.zmodPowHom hζp).compLeft (Fin (m + 1))
  have hpow_eq : ∀ g : Fin Φ.r → Multiplicative (ZMod p),
      (fun i : Fin Φ.r => ζ ^ (toAdd (g i)).val) ∘ e = powHom (reindexHom g) := by
    intro g
    funext i
    change ζ ^ (toAdd (g (e i))).val = (TableBSymp.zmodPowHom hζp) (g (e i))
    rw [TableBSymp.zmodPowHom_apply]
  have hχτ' : ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
      χ (Φ.Δ.τ g v) = diagHom Φ.F σ (m + 1) (powHom (reindexHom g)) (χ v) := by
    intro g v
    change LinearEquiv.funCongrLeft Φ.F K e (χ₀ (Φ.Δ.τ g v)) =
      diagHom Φ.F σ (m + 1) (powHom (reindexHom g)) (χ v)
    rw [hχτ g v, qtwoOrthStd_funCongrLeft_diagHom, hpow_eq g]
    rfl
  have hD : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (LinearEquiv.autCongr χ) (Φ.Δ.τ f) =
        diagHom Φ.F σ (m + 1) (powHom (reindexHom f)) := by
    intro f
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.autCongr_apply_apply, hχτ' f (χ.symm v), LinearEquiv.apply_symm_apply]
  have horth_map : (TauCeti.QuadraticMap.orthogonalGroup Φ.Q).map
      (LinearEquiv.autCongr χ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (Qn E₀ (m + 1)) := by
    apply le_antisymm
    · rintro g ⟨h, hh, rfl⟩
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
      have hh' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hh
      change (Qn E₀ (m + 1)) ((LinearEquiv.autCongr χ) h v) = (Qn E₀ (m + 1)) v
      rw [LinearEquiv.autCongr_apply_apply, hχQ' (h (χ.symm v)), hh' (χ.symm v),
        ← hχQ' (χ.symm v), LinearEquiv.apply_symm_apply]
    · intro g hg
      rw [Subgroup.mem_map]
      refine ⟨(LinearEquiv.autCongr χ).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
      have hg' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
      rw [LinearEquiv.autCongr_symm_apply_apply, ← hχQ' (χ.symm (g (χ v))),
        LinearEquiv.apply_symm_apply, hg' (χ v), hχQ' v]
  have hder : (orthDerived Φ.Q).map (LinearEquiv.autCongr χ).toMonoidHom =
      orthDerived (Qn E₀ (m + 1)) := by
    rw [show orthDerived Φ.Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
        TauCeti.QuadraticMap.orthogonalGroup Φ.Q⁆ from rfl,
      show orthDerived (Qn E₀ (m + 1)) = ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E₀ (m + 1)),
        TauCeti.QuadraticMap.orthogonalGroup (Qn E₀ (m + 1))⁆ from rfl,
      Subgroup.map_commutator, horth_map]
  have hreindex_fix : ∀ a b : Fin Φ.r,
      (reflFixedCoord p Φ.r a b).map reindexHom =
        reflFixedCoord p (m + 1) (Fin.cast hr a) (Fin.cast hr b) := by
    intro a b
    apply le_antisymm
    · rintro g ⟨f, hf, rfl⟩
      have hf' : f a = f b := (qtwoOrthStd_mem_reflFixedCoord_iff f).mp hf
      rw [qtwoOrthStd_mem_reflFixedCoord_iff]
      change f (e (Fin.cast hr a)) = f (e (Fin.cast hr b))
      rw [h_e_cast a, h_e_cast b]
      exact hf'
    · intro g hg
      have hg' : g (Fin.cast hr a) = g (Fin.cast hr b) :=
        (qtwoOrthStd_mem_reflFixedCoord_iff g).mp hg
      refine Subgroup.mem_map.mpr ⟨fun k => g (Fin.cast hr k), ?_, ?_⟩
      · rw [qtwoOrthStd_mem_reflFixedCoord_iff]
        exact hg'
      · funext i
        change g (Fin.cast hr (e i)) = g i
        rw [h_cast_e i]
  have hpowHom_inj : Function.Injective powHom := by
    intro f g h
    funext i
    exact qtwoOrthStd_zmodPowHom_injective hζp (qtwoOrthStd_orderOf_eq_of_prime hζ1 hζp)
      (show (TableBSymp.zmodPowHom hζp) (f i) = (TableBSymp.zmodPowHom hζp) (g i) from
        congrFun h i)
  have hmap_tau : ∀ T : Subgroup (Fin Φ.r → Multiplicative (ZMod p)),
      (T.map Φ.Δ.τ).map (LinearEquiv.autCongr χ).toMonoidHom =
        ((T.map reindexHom).map powHom).map (diagHom Φ.F σ (m + 1)) := by
    intro T
    rw [Subgroup.map_map]
    have hcomp : (LinearEquiv.autCongr χ).toMonoidHom.comp Φ.Δ.τ =
        (diagHom Φ.F σ (m + 1)).comp (powHom.comp reindexHom) := by
      apply MonoidHom.ext
      intro f
      exact hD f
    rw [hcomp, ← MonoidHom.comp_assoc, Subgroup.map_map, Subgroup.map_map]
  have hfix_image : ∀ (a b : Fin Φ.r) (hab : a < b), b.val = a.val + 1 →
      (Φ.fixTorus (⟨(a, b), hab⟩, false)).map (LinearEquiv.autCongr χ).toMonoidHom =
        (qtwoWinTorus σ (m + 1) a.val 2).map (diagHom Φ.F σ (m + 1)) := by
    intro a b hab hbval
    unfold OrthFrameCore.fixTorus
    rw [omPlusRefl_false, qtwoOrthStd_eqLocus_permAut_swap (p := p) hab, hmap_tau, hreindex_fix a b,
      qtwoOrthStd_map_reflFixedCoord_pow hζ1 hζp hcardNorm (Fin.cast hr a) (Fin.cast hr b) (by
        rw [Fin.val_cast, Fin.val_cast, hbval])]
    rfl
  have hfix2_image : ∀ (a b c : Fin Φ.r) (hab : a < b) (hbc : b < c)
      (hbv : b.val = a.val + 1) (hcv : c.val = b.val + 1),
      ((Φ.fixTorus (⟨(a, b), hab⟩, false) ⊓
        Φ.fixTorus (⟨(b, c), hbc⟩, false)).map (LinearEquiv.autCongr χ).toMonoidHom) =
        (qtwoWinTorus σ (m + 1) a.val 3).map (diagHom Φ.F σ (m + 1)) := by
    intro a b c hab hbc hbv hcv
    unfold OrthFrameCore.fixTorus
    rw [omPlusRefl_false, omPlusRefl_false, qtwoOrthStd_eqLocus_permAut_swap (p := p) hab,
      qtwoOrthStd_eqLocus_permAut_swap (p := p) hbc,
      Subgroup.map_inf _ _ _ (LinearEquiv.autCongr χ).injective, hmap_tau, hmap_tau,
      hreindex_fix a b, hreindex_fix b c,
      ← Subgroup.map_inf _ _ _ (diagHom_injective (F := Φ.F) (σ := σ) (m + 1)),
      ← Subgroup.map_inf _ _ _ hpowHom_inj,
      qtwoOrthStd_map_inf_reflFixedCoord_pow hζ1 hζp hcardNorm (Fin.cast hr a) (Fin.cast hr b)
        (Fin.cast hr c) (by rw [Fin.val_cast, Fin.val_cast, hbv])
        (by rw [Fin.val_cast, Fin.val_cast, hcv])]
    rfl
  have hrank1_key : ∀ x : OmPlusIdx Φ.r,
      (Φ.rank1 x).map (LinearEquiv.autCongr χ).toMonoidHom =
        ggOTwoPrime (orthDerived (Qn E₀ (m + 1)) ⊓ Subgroup.centralizer
          (((Φ.fixTorus x).map (LinearEquiv.autCongr χ).toMonoidHom :
            Subgroup ((Fin (m + 1) → K) ≃ₗ[Φ.F] (Fin (m + 1) → K))) : Set _)) := by
    intro x
    rw [OrthFrameCore.rank1,
      ggOTwoPrime_map_of_injective _ (LinearEquiv.autCongr χ).injective,
      Subgroup.map_inf _ _ _ (LinearEquiv.autCongr χ).injective,
      qtwoOrthStd_map_centralizer (LinearEquiv.autCongr χ) (Φ.fixTorus x), hder]
  have hrank2_key : ∀ x y : OmPlusIdx Φ.r,
      (Φ.rank2 x y).map (LinearEquiv.autCongr χ).toMonoidHom =
        ggOTwoPrime (orthDerived (Qn E₀ (m + 1)) ⊓ Subgroup.centralizer
          ((((Φ.fixTorus x ⊓ Φ.fixTorus y : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V))).map
            (LinearEquiv.autCongr χ).toMonoidHom :
            Subgroup ((Fin (m + 1) → K) ≃ₗ[Φ.F] (Fin (m + 1) → K))) : Set _)) := by
    intro x y
    rw [OrthFrameCore.rank2,
      ggOTwoPrime_map_of_injective _ (LinearEquiv.autCongr χ).injective,
      Subgroup.map_inf _ _ _ (LinearEquiv.autCongr χ).injective,
      qtwoOrthStd_map_centralizer (LinearEquiv.autCongr χ) (Φ.fixTorus x ⊓ Φ.fixTorus y), hder]
  have hrank1_untw : ∀ (a b : Fin Φ.r) (hab : a < b), b.val = a.val + 1 →
      (Φ.rank1 (⟨(a, b), hab⟩, false)).map (LinearEquiv.autCongr χ).toMonoidHom =
        (qtwoStdWin (F := Φ.F) (K := K) m a.val 2 (by omega)).range := by
    intro a b hab hbval
    rw [hrank1_key (⟨(a, b), hab⟩, false), hfix_image a b hab hbval]
    exact qtwoOrth_win_eq E₀ hF hKcard m a.val 2 hm (by omega) (by omega)
  have hrank2_untw : ∀ (a b c : Fin Φ.r) (hab : a < b) (hbc : b < c)
      (hbv : b.val = a.val + 1) (hcv : c.val = b.val + 1),
      (Φ.rank2 (⟨(a, b), hab⟩, false) (⟨(b, c), hbc⟩, false)).map
          (LinearEquiv.autCongr χ).toMonoidHom =
        (qtwoStdWin (F := Φ.F) (K := K) m a.val 3 (by omega)).range := by
    intro a b c hab hbc hbv hcv
    rw [hrank2_key (⟨(a, b), hab⟩, false) (⟨(b, c), hbc⟩, false),
      hfix2_image a b c hab hbc hbv hcv]
    exact qtwoOrth_win_eq E₀ hF hKcard m a.val 3 hm (by omega) (by omega)
  let w : MulAut (Fin Φ.r → Multiplicative (ZMod p)) := SpCoord.sgnAut (e (Fin.last m))
  let μ : Φ.V ≃ₗ[Φ.F] Φ.V := (LinearEquiv.autCongr χ).symm (tauAt E₀ (Fin.last m))
  have hμχ : (LinearEquiv.autCongr χ) μ = tauAt E₀ (Fin.last m) :=
    MulEquiv.apply_symm_apply _ _
  have hμ_mem : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
    have hτ : (LinearEquiv.autCongr χ) μ ∈
        (TauCeti.QuadraticMap.orthogonalGroup Φ.Q).map
          (LinearEquiv.autCongr χ).toMonoidHom := by
      rw [horth_map, hμχ]
      exact tauAt_mem_orthogonalGroup E₀ (Fin.last m)
    have h2 := (Subgroup.mem_map_equiv (f := LinearEquiv.autCongr χ)).mp hτ
    rwa [MulEquiv.symm_apply_apply] at h2
  have hpow_update : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      powHom (reindexHom (w f)) =
        Function.update (powHom (reindexHom f)) (Fin.last m)
          ((powHom (reindexHom f)) (Fin.last m))⁻¹ := by
    intro f
    funext j
    have hw_def : w = SpCoord.sgnAut (e (Fin.last m)) := rfl
    rw [hw_def]
    change (TableBSymp.zmodPowHom hζp)
        ((SpCoord.sgnAut (e (Fin.last m)) f) (e j)) =
      Function.update (fun i => (TableBSymp.zmodPowHom hζp) (f (e i))) (Fin.last m)
        ((fun i => (TableBSymp.zmodPowHom hζp) (f (e i))) (Fin.last m))⁻¹ j
    by_cases hj : j = Fin.last m
    · subst hj
      rw [SpCoord.sgnAut_apply, Function.update_self, Function.update_self, map_inv]
    · have hej : e j ≠ e (Fin.last m) := fun h => hj (e.injective h)
      rw [SpCoord.sgnAut_apply, Function.update_of_ne hej, Function.update_apply, if_neg hj]
  have hμ_torus : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f) := by
    intro f
    apply (LinearEquiv.autCongr χ).injective
    rw [map_mul, map_mul, map_inv, hμχ]
    rw [hD f, hD (w f)]
    rw [qtwoOrthStd_tauAt_conj_diagHom E₀ (Fin.last m) (powHom (reindexHom f))]
    rw [hpow_update f]
  have hconj_comp : (LinearEquiv.autCongr χ).toMonoidHom.comp (MulAut.conj μ).toMonoidHom =
      (stdConj E₀ m).toMonoidHom.comp (LinearEquiv.autCongr χ).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change (LinearEquiv.autCongr χ) (μ * g * μ⁻¹) =
      stdConj E₀ m ((LinearEquiv.autCongr χ) g)
    simp only [map_mul, map_mul, map_inv, hμχ, stdConj, stdTau, MulAut.conj_apply]
  have hmap_conj : ∀ S : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V),
      (S.map (MulAut.conj μ).toMonoidHom).map (LinearEquiv.autCongr χ).toMonoidHom =
        (S.map (LinearEquiv.autCongr χ).toMonoidHom).map (stdConj E₀ m).toMonoidHom := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map, hconj_comp]
  have hw_last : w = SpCoord.sgnAut (⟨m, by omega⟩ : Fin Φ.r) := by
    change SpCoord.sgnAut (e (Fin.last m)) = SpCoord.sgnAut (⟨m, by omega⟩ : Fin Φ.r)
    congr 1
  have hchain_fwd : ∀ k k' : Fin Φ.r, k'.val = k.val + 1 → k'.val ≤ m - 1 →
      (Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k')).map
          (LinearEquiv.autCongr χ).toMonoidHom =
        qtwoStdW E₀ m hm (Fin.cast hr k) (Fin.cast hr k') := by
    intro k k' hk'v hk'm
    have hklt : k.val + 1 < Φ.r := by rw [← hk'v]; exact k'.isLt
    let b : Fin Φ.r := ⟨k.val + 1, hklt⟩
    let c : Fin Φ.r := ⟨k.val + 2, by omega⟩
    have hb_eq : b = k' := Fin.ext hk'v.symm
    have hkb : k < b := by rw [Fin.lt_def]; simp only [b]; omega
    have hbc : b < c := by rw [Fin.lt_def]; simp only [b, c]; omega
    have hbv : b.val = k.val + 1 := rfl
    have hcv : c.val = b.val + 1 := by simp only [b, c]
    have hstdk : omStd Φ.r (by omega) k = (⟨(k, b), hkb⟩, false) := by
      rw [omStd, dif_pos hklt]
    have hstdk' : omStd Φ.r (by omega) k' = (⟨(b, c), hbc⟩, false) := by
      have hlt' : k'.val + 1 < Φ.r := by rw [hk'v]; exact c.isLt
      rw [omStd, dif_pos hlt']
      refine Prod.ext (Subtype.ext (Prod.ext hb_eq.symm (Fin.ext ?_))) rfl
      simp only [c]
      omega
    rw [hstdk, hstdk', hrank2_untw k b c hkb hbc hbv hcv,
      qtwoStdW_chain E₀ m hm k.val (by omega) (Fin.cast hr k) (Fin.cast hr k') rfl
        (by rw [Fin.val_cast, hk'v])]
  have hfork_fwd : ∀ k k' : Fin Φ.r, k.val = m - 2 → k'.val = m →
      (Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k')).map
          (LinearEquiv.autCongr χ).toMonoidHom =
        qtwoStdW E₀ m hm (Fin.cast hr k) (Fin.cast hr k') := by
    intro k k' hkv hk'v
    let a : Fin Φ.r := ⟨m - 2, by omega⟩
    let b : Fin Φ.r := ⟨m - 1, by omega⟩
    let c : Fin Φ.r := ⟨m, by omega⟩
    have ha_eq : a = k := Fin.ext (by simp only [a]; omega)
    have hc_eq : c = k' := Fin.ext (by simp only [c]; omega)
    have hab : a < b := by rw [Fin.lt_def]; simp only [a, b]; omega
    have hbc : b < c := by rw [Fin.lt_def]; simp only [b, c]; omega
    have hbv : b.val = a.val + 1 := by simp only [a, b]; omega
    have hcv : c.val = b.val + 1 := by simp only [b, c]; omega
    have hw_c : w = SpCoord.sgnAut (p := p) c := by
      rw [hw_last]
    have hstdk : omStd Φ.r (by omega) k = (⟨(a, b), hab⟩, false) := by
      rw [omStd, dif_pos (by omega)]
      refine Prod.ext (Subtype.ext (Prod.ext ha_eq.symm (Fin.ext ?_))) rfl
      simp only [b]
      omega
    have hstdk' : omStd Φ.r (by omega) k' = (⟨(b, c), hbc⟩, true) := by
      rw [omStd, dif_neg (by rw [hk'v]; omega)]
      refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) rfl
      · apply Fin.ext
        simp only [b]
        omega
      · apply Fin.ext
        simp only [c]
        omega
    have hx : omPlusRefl p (⟨(a, b), hab⟩, false) =
        w * omPlusRefl p (⟨(a, b), hab⟩, false) * w⁻¹ := by
      rw [omPlusRefl_false, hw_c,
        qtwoOrthStd_sgnAut_comm_swap (p := p) (a := a) (b := b) (i := c)
          (by intro h; have := congrArg Fin.val h; simp only [a, c] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [b, c] at this; omega),
        mul_assoc, mul_inv_cancel, mul_one]
    have hy : omPlusRefl p (⟨(b, c), hbc⟩, true) =
        w * omPlusRefl p (⟨(b, c), hbc⟩, false) * w⁻¹ := by
      rw [omPlusRefl_true, omPlusRefl_false, hw_c]
      exact (qtwoOrthStd_sgnAut_conj_swap (p := p) (a := b) (b := c) (ne_of_lt hbc)).symm
    have hpair : Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k') =
        Φ.rank2 (⟨(a, b), hab⟩, false) (⟨(b, c), hbc⟩, true) := by
      simp only [hstdk, hstdk']
    rw [hpair, qtwoOrth_rank2_conj (Φ := Φ) hμ_mem hμ_torus hx hy, hmap_conj,
      hrank2_untw a b c hab hbc hbv hcv,
      qtwoStdW_fork E₀ m hm (Fin.cast hr k) (Fin.cast hr k')
        (by rw [Fin.val_cast]; exact hkv) (by rw [Fin.val_cast]; exact hk'v)]
  have hχτ'' : ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
      χ (Φ.Δ.τ g v) = diagHom Φ.F σ (m + 1)
        (fun i => ζ ^ (toAdd (g (Fin.cast hr.symm i))).val) (χ v) := by
    intro g v
    have hfun : powHom (reindexHom g) = fun i => ζ ^ (toAdd (g (Fin.cast hr.symm i))).val := by
      funext i
      change (TableBSymp.zmodPowHom hζp) (g (e i)) = _
      rw [TableBSymp.zmodPowHom_apply]
      rfl
    rw [hχτ' g v, hfun]
  refine ⟨inst, E₀, χ, ζ, hζ1, hχQ', hχτ'', ?_, ?_⟩
  · intro k
    by_cases hk : k.val + 1 < Φ.r
    · have hstd : omStd Φ.r (by omega) k =
          (⟨(k, ⟨k.val + 1, hk⟩), by rw [Fin.lt_def]; exact Nat.lt_succ_self _⟩, false) := by
        rw [omStd, dif_pos hk]
      have hpair : Φ.rank1 (omStd Φ.r (by omega) k) =
          Φ.rank1 (⟨(k, ⟨k.val + 1, hk⟩),
            by rw [Fin.lt_def]; exact Nat.lt_succ_self _⟩, false) := by
        rw [hstd]
      have hcastk : Fin.cast hr k = Fin.castSucc (⟨k.val, by omega⟩ : Fin m) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castSucc]
      rw [hpair, hrank1_untw k ⟨k.val + 1, hk⟩
        (by rw [Fin.lt_def]; exact Nat.lt_succ_self _) rfl, hcastk,
        qtwoStdU_castSucc E₀ m hm ⟨k.val, by omega⟩]
    · have hkval : k.val = m := by omega
      have hk_eq : k = ⟨m, by omega⟩ := Fin.ext hkval
      let a : Fin Φ.r := ⟨m - 1, by omega⟩
      let b : Fin Φ.r := ⟨m, by omega⟩
      have hab : a < b := by rw [Fin.lt_def]; simp only [a, b]; omega
      have hbv : b.val = a.val + 1 := by simp only [a, b]; omega
      have hw_b : w = SpCoord.sgnAut b := by
        rw [hw_last]
      have hstd : omStd Φ.r (by omega) k = (⟨(a, b), hab⟩, true) := by
        rw [omStd, dif_neg hk]
        refine Prod.ext (Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_))) rfl
        · simp only [a]; omega
        · simp only [b]; omega
      have hx : omPlusRefl p (⟨(a, b), hab⟩, true) =
          w * omPlusRefl p (⟨(a, b), hab⟩, false) * w⁻¹ := by
        rw [omPlusRefl_true, omPlusRefl_false, hw_b]
        exact (qtwoOrthStd_sgnAut_conj_swap (p := p) (a := a) (b := b) (ne_of_lt hab)).symm
      have hcast : Fin.cast hr k = Fin.last m := by
        apply Fin.ext
        rw [Fin.val_last, Fin.val_cast, hkval]
      have hpair : Φ.rank1 (omStd Φ.r (by omega) k) =
          Φ.rank1 (⟨(a, b), hab⟩, true) := by
        rw [hstd]
      rw [hpair, qtwoOrth_rank1_conj (Φ := Φ) hμ_mem hμ_torus hx, hmap_conj,
        hrank1_untw a b hab hbv, hcast, qtwoStdU_last E₀ m hm]
  · intro k k' h3
    have h3' := (qtwoLabel_three_iff hm (Fin.cast hr k) (Fin.cast hr k')).mp h3
    rcases h3' with ⟨hjv, hjm⟩ | ⟨hiv, him⟩ | ⟨him2, hjm2⟩ | ⟨hjm2, him2⟩
    ·
      have hk'v : k'.val = k.val + 1 := by
        have h := hjv
        rw [Fin.val_cast, Fin.val_cast] at h
        exact h
      have hk'm : k'.val ≤ m - 1 := by
        have h := hjm
        rw [Fin.val_cast] at h
        exact h
      exact hchain_fwd k k' hk'v hk'm
    ·
      have hkv : k.val = k'.val + 1 := by
        have h := hiv
        rw [Fin.val_cast, Fin.val_cast] at h
        exact h
      have hkm : k.val ≤ m - 1 := by
        have h := him
        rw [Fin.val_cast] at h
        exact h
      have hsymm : Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k') =
          Φ.rank2 (omStd Φ.r (by omega) k') (omStd Φ.r (by omega) k) := by
        unfold OrthFrameCore.rank2
        rw [inf_comm (Φ.fixTorus (omStd Φ.r (by omega) k))
          (Φ.fixTorus (omStd Φ.r (by omega) k'))]
      rw [hsymm, qtwoStdW_symm E₀ m hm]
      exact hchain_fwd k' k hkv hkm
    ·
      have hkv : k.val = m - 2 := by
        have h := him2
        rw [Fin.val_cast] at h
        omega
      have hk'v : k'.val = m := by
        have h := hjm2
        rw [Fin.val_cast] at h
        exact h
      exact hfork_fwd k k' hkv hk'v
    ·
      have hkv : k'.val = m - 2 := by
        have h := hjm2
        rw [Fin.val_cast] at h
        omega
      have hk'v : k.val = m := by
        have h := him2
        rw [Fin.val_cast] at h
        exact h
      have hsymm : Φ.rank2 (omStd Φ.r (by omega) k) (omStd Φ.r (by omega) k') =
          Φ.rank2 (omStd Φ.r (by omega) k') (omStd Φ.r (by omega) k) := by
        unfold OrthFrameCore.rank2
        rw [inf_comm (Φ.fixTorus (omStd Φ.r (by omega) k))
          (Φ.fixTorus (omStd Φ.r (by omega) k'))]
      rw [hsymm, qtwoStdW_symm E₀ m hm]
      exact hfork_fwd k' k hkv hk'v

end Std

end CFSG.StandardType.QTwo

end
