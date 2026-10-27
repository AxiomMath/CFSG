module

public import CFSG.GroupTheory.AutomorphismAction.MapEqOfMapsTo
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFAbs2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

private def permSet (n : ℕ) : Set ((Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :=
  {T | ∃ σ : Equiv.Perm (Fin n), ∀ v i, T v i = v (σ i)}

private noncomputable def d0 (n : ℕ) :
    (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun v i := (if i.val = 0 then (-1 : ZMod 3) else 1) * v i
  invFun v i := (if i.val = 0 then (-1 : ZMod 3) else 1) * v i
  left_inv v := by
    ext i
    by_cases h : i.val = 0 <;> simp [h]
  right_inv v := by
    ext i
    by_cases h : i.val = 0 <;> simp [h]
  map_add' v w := by
    ext i
    simp [Pi.add_apply, mul_add]
  map_smul' c v := by
    ext i
    simp [Pi.smul_apply, mul_comm]

private lemma d0_apply (n : ℕ) (v : Fin n → ZMod 3) (i : Fin n) :
    d0 n v i = (if i.val = 0 then (-1 : ZMod 3) else 1) * v i := rfl

private lemma d0_symm (n : ℕ) : (d0 n).symm = d0 n := by
  ext v i
  by_cases h : i.val = 0 <;> simp [d0, h]

private noncomputable def signedPermSet (n : ℕ) :
    Set ((Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :=
  (permSet n).image (MulAut.conj (d0 n)).toMonoidHom

private lemma funCongrLeft_sign {n : ℕ} {i₀ : Fin n} {s : Equiv.Perm (Fin n)}
    (hs : ∀ i : Fin n, (s i = i₀ ↔ i.val = 0)) (w : Fin n → ZMod 3) :
    LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) s
        (fun i => (if i = i₀ then -1 else 1) * w i) =
      d0 n (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) s w) := by
  ext i
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, d0]
  by_cases hi : i.val = 0
  · have hsi : s i = i₀ := (hs i).mpr hi
    simp [hsi, hi]
  · have hsi : s i ≠ i₀ := fun hc => hi ((hs i).mp hc)
    simp [hsi, hi]

private lemma signedPermSet_eq (n : ℕ) :
    signedPermSet n = {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
      T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
        (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} := by
  ext T
  constructor
  · rintro ⟨Q, ⟨σ, hσ⟩, rfl⟩
    refine ⟨σ, fun v i => ?_⟩
    change MulAut.conj (d0 n) Q v i = _
    rw [MulAut.conj_apply]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    rw [d0_symm]
    have hQfun : Q ((d0 n) v) = fun j => ((d0 n) v) (σ j) :=
      funext fun j => hσ ((d0 n) v) j
    rw [hQfun, d0_apply, d0_apply]
    ring
  · rintro ⟨σ, hσ⟩
    let Q : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
      LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) σ
    refine ⟨Q, ⟨σ, ?_⟩, ?_⟩
    · intro v i
      simp [Q, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    · ext v i
      change MulAut.conj (d0 n) Q v i = T v i
      rw [MulAut.conj_apply]
      simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
      rw [d0_symm]
      have hQfun : Q ((d0 n) v) = fun j => ((d0 n) v) (σ j) := by
        funext j
        simp [Q, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      rw [hQfun, d0_apply, d0_apply, hσ]
      ring

private lemma closure_signedPermSet_eq (n : ℕ) :
    Subgroup.closure (signedPermSet n) =
      (Subgroup.closure (permSet n)).map (MulAut.conj (d0 n)).toMonoidHom := by
  rw [signedPermSet, MonoidHom.map_closure]

theorem ggQTwoFRConcl_of_frame {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J) (hF : GGQTwoFRFrame E x L D J) : GGQTwoFRConcl E x L D J := by
  obtain ⟨n, hn, hxF, ι, i₀, α, hιx, hAL, hD, hJcard, hαE, hαι, hαJ⟩ := hF
  obtain ⟨hEab, hEcard, hE3, hxE, hxne, hxL, hLcomp, hEL, hEcent, hDE, hDcard, hxD,
    hJcomp, hEJ⟩ := hC
  have hfin : Finite ↥E := Nat.finite_of_card_ne_zero (by omega)
  have hmapα : E.map α.toMonoidHom = E :=
    @CFSG.GroupTheory.map_eq_of_mapsTo R _ E hfin α hαE
  let eE : ↥E ≃* ↥E :=
    (E.equivMapOfInjective α.toMonoidHom α.injective).trans (MulEquiv.subgroupCongr hmapα)
  have heE : ∀ b : ↥E, ((eE b : ↥E) : R) = α (b : R) := by
    intro b
    rfl
  have hn0 : 0 < n := by omega
  let s : Equiv.Perm (Fin n) := Equiv.swap ⟨0, hn0⟩ i₀
  have hs0 : s ⟨0, hn0⟩ = i₀ := Equiv.swap_apply_left _ _
  have hs : ∀ i : Fin n, (s i = i₀ ↔ i.val = 0) := by
    intro i
    constructor
    · intro h
      have h' : s i = s ⟨0, hn0⟩ := by rw [h, hs0]
      have hi := s.injective h'
      rw [hi]
    · intro hi
      have h0 : i = ⟨0, hn0⟩ := Fin.ext hi
      rw [h0, hs0]
  let P : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
    LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) s
  let ι' : Additive ↥E ≃+ (Fin n → ZMod 3) := ι.trans P.toAddEquiv
  have hyE : α x ∈ E := hαE x hxE
  have hiy : ι (Additive.ofMul ⟨α x, hyE⟩) =
      fun i => if i = i₀ then -1 else 1 := by
    rw [hαι x hxE hyE, hιx]
    funext i
    by_cases h : i = i₀ <;> simp [h]
  have hPmem : P ∈ permSet n := by
    refine ⟨s, ?_⟩
    intro v i
    simp [P, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hPd0 : ∀ w : Fin n → ZMod 3,
      P (fun i => (if i = i₀ then -1 else 1) * w i) = d0 n (P w) :=
    fun w => funCongrLeft_sign hs w
  have hh : ∀ b : ↥E, ι' (Additive.ofMul (eE b)) = d0 n (ι' (Additive.ofMul b)) := by
    intro b
    have hb : ((eE b : ↥E) : R) = α (b : R) := heE b
    have hbE : (eE b : ↥E) = ⟨α (b : R), hαE (b : R) b.2⟩ := Subtype.ext hb
    rw [hbE]
    change P (ι (Additive.ofMul ⟨α (b : R), hαE (b : R) b.2⟩)) =
      d0 n (P (ι (Additive.ofMul b)))
    rw [hαι (b : R) b.2 (hαE (b : R) b.2)]
    exact hPd0 (ι (Additive.ofMul b))
  have hd0 : ggLin (p := 3) ι' eE = d0 n := ggLin_eq_of_pointwise ι' eE (d0 n) hh
  have hcomp : (ggLin (p := 3) ι').comp (MulAut.congr eE).toMonoidHom =
      (MulAut.conj (d0 n)).toMonoidHom.comp (ggLin (p := 3) ι') := by
    refine MonoidHom.ext fun φ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    change ggLin (p := 3) ι' (MulAut.congr eE φ) =
      MulAut.conj (d0 n) (ggLin (p := 3) ι' φ)
    rw [ggLin_congr, hd0, MulAut.conj_apply]
  have hLimg : (ggAutomizer L E).map (ggLin (p := 3) ι') =
      Subgroup.closure (permSet n) := by
    have hconj : ggLin (p := 3) ι' =
        (MulAut.conj P).toMonoidHom.comp (ggLin (p := 3) ι) := by
      refine MonoidHom.ext fun φ => ?_
      rw [MonoidHom.comp_apply]
      change ggLin (p := 3) ι' φ = MulAut.conj P (ggLin (p := 3) ι φ)
      rw [ggLin_relabel, MulAut.conj_apply]
    rw [hconj, ← Subgroup.map_map, hAL]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (Subgroup.subset_closure hPmem))
  have hKauto : ggAutomizer (L.map α.toMonoidHom) E =
      (ggAutomizer L E).map (MulAut.congr eE).toMonoidHom := by
    have h := F4AutWeyl.ggAutomizer_map_eq (f := α.toMonoidHom) α.injective L E hmapα
    simpa [eE] using h
  have hKimg : (ggAutomizer (L.map α.toMonoidHom) E).map (ggLin (p := 3) ι') =
      (Subgroup.closure (permSet n)).map (MulAut.conj (d0 n)).toMonoidHom := by
    rw [hKauto, Subgroup.map_map, hcomp, ← Subgroup.map_map, hLimg]
  have hKcomp : IsComponentOf (L.map α.toMonoidHom)
      (Subgroup.centralizer ({α x} : Set R)) := by
    have h := CFSG.isComponentOf_map_mulEquiv α
      (CFSG.Assembly.isComponentOf_iff_open.mp hLcomp)
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv α ({x} : Set R),
      Set.image_singleton] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mpr h
  have hJle : J ≤ L.map α.toMonoidHom := by
    intro j hj
    exact Subgroup.mem_map.mpr ⟨j, (hJcomp.1 hj).1, hαJ j hj⟩
  have hiyD : α x ∈ D := by
    refine (hD (α x) hyE).mpr ⟨1, 1, ?_⟩
    rw [hiy]
    funext i
    by_cases h : i = i₀
    · subst h
      simp
      decide
    · simp [h]
  have hαα : α (α x) = x := by
    have hkey : (⟨α (α x), hαE (α x) hyE⟩ : ↥E) = ⟨x, hxE⟩ := by
      apply Additive.ofMul.injective
      apply ι.injective
      rw [hαι (α x) hyE (hαE (α x) hyE), hiy, hιx]
      funext i
      by_cases h : i = i₀ <;> simp [h]
    exact congrArg Subtype.val hkey
  have hsymm : α.symm x = α x := by
    apply α.injective
    rw [MulEquiv.apply_symm_apply]
    exact hαα.symm
  have hiy_not : α x ∉ Subgroup.zpowers x := by
    rintro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hxpow : (⟨x, hxE⟩ : ↥E) ^ k = ⟨α x, hyE⟩ := by
      apply Subtype.ext
      simpa using hk
    have hz : ι (Additive.ofMul ⟨α x, hyE⟩) =
        k • ι (Additive.ofMul (⟨x, hxE⟩ : ↥E)) := by
      rw [← hxpow, ofMul_zpow, map_zsmul]
    rw [hiy, hιx] at hz
    have hn0 : 0 < n := by omega
    let j : Fin n := if h : i₀.val = 0 then ⟨1, by omega⟩ else ⟨0, hn0⟩
    have hj : j ≠ i₀ := by
      intro he
      have hv : j.val = i₀.val := congrArg Fin.val he
      by_cases h : i₀.val = 0
      · simp [j, h] at hv
      · have hjv : j.val = 0 := by simp [j, h]
        omega
    have h1 : (-1 : ZMod 3) = k • (1 : ZMod 3) := by
      have := congrFun hz i₀
      simpa using this
    have h2 : (1 : ZMod 3) = k • (1 : ZMod 3) := by
      have := congrFun hz j
      simpa [hj] using this
    have hcontra : (-1 : ZMod 3) = 1 := h1.trans h2.symm
    exact absurd hcontra (by decide)
  have hxK : x ∉ Subgroup.centralizer (L.map α.toMonoidHom : Set R) := by
    intro hxmem
    have hyC : α x ∈ Subgroup.centralizer (L : Set R) := by
      rw [Subgroup.mem_centralizer_iff] at hxmem ⊢
      intro l hl
      have h := hxmem (α l) (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)
      have := congrArg α.symm h
      simpa [map_mul, hsymm] using this
    have hycent : α x ∈ E ⊓ Subgroup.centralizer (L : Set R) := ⟨hyE, hyC⟩
    rw [hEcent] at hycent
    exact hiy_not hycent
  have hι'x : ι' (Additive.ofMul ⟨x, hxE⟩) = (fun _ => 1) := by
    change P (ι (Additive.ofMul ⟨x, hxE⟩)) = fun _ => 1
    rw [hιx]
    funext i
    simp [P, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hι'y : ι' (Additive.ofMul ⟨α x, hyE⟩) =
      (fun i => if i.val = 0 then -1 else 1) := by
    change P (ι (Additive.ofMul ⟨α x, hyE⟩)) = _
    rw [hiy]
    funext i
    simp only [P, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    by_cases hi : i.val = 0
    · rw [if_pos ((hs i).mpr hi), if_pos hi]
    · rw [if_neg (fun hc => hi ((hs i).mp hc)), if_neg hi]
  rw [← closure_signedPermSet_eq n, signedPermSet_eq n] at hKimg
  exact ⟨n, hn, α x, L.map α.toMonoidHom, hxE, hyE, ι', hiyD, hiy_not, hJcard, hKcomp,
    hJle, hxK, hLimg, hKimg, hι'x, hι'y⟩

theorem GGQTwoFRCfg.map {R' : Type} [Group R'] (e : R ≃* R') {E : Subgroup R} {x : R}
    {L D J : Subgroup R} (hC : GGQTwoFRCfg E x L D J) :
    GGQTwoFRCfg (E.map e.toMonoidHom) (e x) (L.map e.toMonoidHom) (D.map e.toMonoidHom)
      (J.map e.toMonoidHom) := by
  obtain ⟨hEab, hEcard, hE3, hxE, hxne, hxL, hLcomp, hEL, hEcent, hDE, hDcard, hxD, hJcomp,
    hEJ⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hEab e.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hEcard
  · intro g hg hg3
    have hg' : e.symm g ∈ Subgroup.centralizer (E : Set R) := by
      intro s hs
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e s) ⟨s, hs, rfl⟩
    have hg3' : (e.symm g) ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, map_one, e.apply_symm_apply, hg3]
    exact Subgroup.mem_map.mpr ⟨e.symm g, hE3 (e.symm g) hg' hg3', by simp⟩
  · exact Subgroup.mem_map.mpr ⟨x, hxE, rfl⟩
  · intro h
    apply hxne
    apply e.injective
    rw [h, map_one]
  · exact Subgroup.mem_map.mpr ⟨x, hxL, rfl⟩
  · have h := CFSG.isComponentOf_map_mulEquiv e
      (CFSG.Assembly.isComponentOf_iff_open.mp hLcomp)
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e {x}, Set.image_singleton] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mpr h
  · have h := Subgroup.map_mono hEL (f := e.toMonoidHom)
    rwa [Subgroup.map_normalizer_eq_of_bijective L e.bijective] at h
  · rw [Subgroup.coe_map, ← CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e (L : Set R),
      ← Subgroup.map_inf _ _ e.toMonoidHom e.injective, hEcent, MonoidHom.map_zpowers]
    rfl
  · exact Subgroup.map_mono hDE
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hDcard
  · exact Subgroup.mem_map.mpr ⟨x, hxD, rfl⟩
  · have h := CFSG.isComponentOf_map_mulEquiv e
      (CFSG.Assembly.isComponentOf_iff_open.mp hJcomp)
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e (D : Set R)] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mpr h
  · rw [Subgroup.coe_map, ← CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e (J : Set R),
      ← Subgroup.map_inf _ _ e.toMonoidHom e.injective, hEJ]

theorem GGQTwoFRConcl.of_map {R' : Type} [Group R'] (e : R ≃* R') {E : Subgroup R} {x : R}
    {L D J : Subgroup R}
    (h : GGQTwoFRConcl (E.map e.toMonoidHom) (e x) (L.map e.toMonoidHom) (D.map e.toMonoidHom)
      (J.map e.toMonoidHom)) :
    GGQTwoFRConcl E x L D J := by
  obtain ⟨n, hn, y', K', hx', hy', ι', hy'D, hy'not, hJcard', hK'comp, hJ'le, hxnot',
    hLauto', hKauto', hι'x, hι'y⟩ := h
  let eE : ↥E ≃* ↥(E.map e.toMonoidHom) :=
    (E.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (rfl : E.map e.toMonoidHom = E.map e.toMonoidHom))
  let y : R := e.symm y'
  let K : Subgroup R := K'.map e.symm.toMonoidHom
  let ι : Additive ↥E ≃+ (Fin n → ZMod 3) := (MulEquiv.toAdditive eE).trans ι'
  have hx : x ∈ E := by
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hx'
    have hax : a = x := e.injective hae
    rw [← hax]
    exact ha
  have hy : y ∈ E := by
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hy'
    have hya : y = a := by simp [y, ← hae]
    rwa [hya]
  have hyD : y ∈ D := by
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hy'D
    have hya : y = a := by simp [y, ← hae]
    rwa [hya]
  have hJcard : 3 ∣ Nat.card ↥J := by
    rw [Subgroup.card_map_of_injective e.injective] at hJcard'
    exact hJcard'
  have hKcomp : IsComponentOf K (Subgroup.centralizer ({y} : Set R)) := by
    have h' := CFSG.isComponentOf_map_mulEquiv e.symm
      (CFSG.Assembly.isComponentOf_iff_open.mp hK'comp)
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e.symm ({y'} : Set R'),
      Set.image_singleton] at h'
    exact CFSG.Assembly.isComponentOf_iff_open.mpr (by simpa [K, y] using h')
  have hJle : J ≤ K := by
    intro j hj
    exact Subgroup.mem_map.mpr
      ⟨e j, hJ'le (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩), by simp⟩
  have hxnot : x ∉ Subgroup.centralizer (K : Set R) := by
    intro hxmem
    apply hxnot'
    rw [Subgroup.mem_centralizer_iff] at hxmem ⊢
    intro k' hk'
    have hk : e.symm k' ∈ K := Subgroup.mem_map.mpr ⟨k', hk', rfl⟩
    have h := hxmem (e.symm k') hk
    have := congrArg e h
    simpa using this
  have hynot : y ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hy'not
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [← map_zpow, hk]
    simp [y]
  have hcomp : (ggLin (p := 3) ι').comp (MulAut.congr eE).toMonoidHom =
      ggLin (p := 3) ι := by
    refine MonoidHom.ext fun φ => ?_
    rw [MonoidHom.comp_apply]
    change ggLin (p := 3) ι' (MulAut.congr eE φ) = ggLin (p := 3) ι φ
    exact (ggLin_trans_congr eE ι' φ).symm
  have hLmap : ggAutomizer (L.map e.toMonoidHom) (E.map e.toMonoidHom) =
      (ggAutomizer L E).map (MulAut.congr eE).toMonoidHom := by
    have h' := F4AutWeyl.ggAutomizer_map_eq (f := e.toMonoidHom) e.injective L E
      (rfl : E.map e.toMonoidHom = E.map e.toMonoidHom)
    simpa [eE] using h'
  have hKmap : K.map e.toMonoidHom = K' := by
    change (K'.map e.symm.toMonoidHom).map e.toMonoidHom = K'
    rw [Subgroup.map_map]
    simp
  have hKmapAut : ggAutomizer K' (E.map e.toMonoidHom) =
      (ggAutomizer K E).map (MulAut.congr eE).toMonoidHom := by
    rw [← hKmap]
    have h' := F4AutWeyl.ggAutomizer_map_eq (f := e.toMonoidHom) e.injective K E
      (rfl : E.map e.toMonoidHom = E.map e.toMonoidHom)
    simpa [eE] using h'
  have hLauto : (ggAutomizer L E).map (ggLin (p := 3) ι) =
      Subgroup.closure (permSet n) := by
    rw [hLmap, Subgroup.map_map, hcomp] at hLauto'
    exact hLauto'
  have hKauto : (ggAutomizer K E).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
          (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} := by
    rw [hKmapAut, Subgroup.map_map, hcomp] at hKauto'
    exact hKauto'
  have heE_x : eE ⟨x, hx⟩ = ⟨e x, hx'⟩ := by
    exact Subtype.ext rfl
  have heE_y : eE ⟨y, hy⟩ = ⟨y', hy'⟩ := by
    apply Subtype.ext
    change e (e.symm y') = y'
    simp
  have hιx : ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) := by
    change ι' (Additive.ofMul (eE ⟨x, hx⟩)) = fun _ => 1
    rw [heE_x]
    exact hι'x
  have hιy : ι (Additive.ofMul ⟨y, hy⟩) =
      (fun i => if i.val = 0 then (-1 : ZMod 3) else 1) := by
    change ι' (Additive.ofMul (eE ⟨y, hy⟩)) = _
    rw [heE_y]
    exact hι'y
  exact ⟨n, hn, y, K, hx, hy, ι, hyD, hynot, hJcard, hKcomp, hJle, hxnot, hLauto,
    hKauto, hιx, hιy⟩

end CFSG.StandardType

end
