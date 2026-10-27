module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139E
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundC

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_commutator_eq_self_of_isQuasisimple {B : Type*} [Group B]
    {K : Subgroup B} (hq : CFSG.Open.IsQuasisimple K) : ⁅K, K⁆ = K := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  exact Subgroup.commutator_eq_self

private theorem w1369_commSub_invariant_of_normalizes {V : Type*} [CommGroup V]
    {R : Subgroup (MulAut V)} {g : MulAut V} (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∀ u ∈ commSub ⊤ R, g u ∈ commSub ⊤ R := by
  intro u hu
  rw [commSub] at hu ⊢
  refine Subgroup.closure_induction (p := fun c _ =>
    g c ∈ Subgroup.closure {c | ∃ x ∈ R, ∃ w ∈ (⊤ : Subgroup V), x w * w⁻¹ = c})
    ?_ ?_ ?_ ?_ hu
  · rintro c ⟨r, hr, w, -, rfl⟩
    refine Subgroup.subset_closure ⟨g * r * g⁻¹, hg r hr, g w, Subgroup.mem_top _, ?_⟩
    rw [show (g * r * g⁻¹) (g w) = g (r w) from by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]]
    simp
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (Subgroup.closure _).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (Subgroup.closure _).inv_mem ha

private theorem w1369_conj_eq_self_of_comm {V : Type*} [CommGroup V] {a b : MulAut V}
    (h : a * b = b * a) {y : MulAut V} (hy : y ∈ Subgroup.zpowers a) : b * y * b⁻¹ = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hba : MulAut.conj b a = a := by
    rw [MulAut.conj_apply, ← h, mul_assoc, mul_inv_cancel, mul_one]
  calc b * a ^ k * b⁻¹ = MulAut.conj b (a ^ k) := (MulAut.conj_apply b _).symm
    _ = (MulAut.conj b a) ^ k := map_zpow (MulAut.conj b) a k
    _ = a ^ k := by rw [hba]

private theorem w1369_zpowers_stabilizes {V : Type*} [CommGroup V] {U : Subgroup V} {g : MulAut V}
    (hg2 : g * g = 1) (hg : ∀ u ∈ U, g u ∈ U) :
    ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U, x u ∈ U := by
  have hgU : g ∈ stabSub U := by
    rw [mem_stabSub]
    intro v
    constructor
    · intro hv
      have hgg : g (g v) = v := by
        have := congrArg (fun f : MulAut V => f v) hg2
        simpa [MulAut.mul_apply] using this
      rw [← hgg]
      exact hg (g v) hv
    · exact hg v
  have hle : Subgroup.zpowers g ≤ stabSub U := Subgroup.zpowers_le.mpr hgU
  intro x hx u hu
  exact (mem_stabSub.mp (hle hx) u).2 hu

private theorem w1369_commSub_le_fixV_of_commute {V : Type*} [CommGroup V] {s e : MulAut V}
    {U : Subgroup V} (hU : U ≤ fixV (Subgroup.zpowers s)) (hes : s * e = e * s) :
    commSub U (Subgroup.zpowers e) ≤ fixV (Subgroup.zpowers s) := by
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨y, hy, w, hw, rfl⟩
  refine mem_fixV_zpowers_iff.mpr ?_
  have hsy : s * y * s⁻¹ = y := w1369_conj_eq_self_of_comm hes.symm hy
  have hsw : s w = w := mem_fixV_zpowers_iff.mp (hU hw)
  have key : s (y w * w⁻¹) = (s * y * s⁻¹) (s w) * (s w)⁻¹ := by
    rw [map_mul, map_inv]
    congr 1
    · simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  rw [key, hsy, hsw]

private theorem w1369_norm_mul (hw2 : ∀ w : W, w ^ 2 = 1) {x : MulAut W} (hx3 : x ^ 3 = 1)
    (hfixX : fixV (Subgroup.zpowers x) = ⊥) (w : W) : (x ^ 2) w * x w = w := by
  have h := mulAut_norm_mul_eq_one hx3 hfixX w
  have h1 : (x ^ 2) w * x w = w⁻¹ := by
    simpa [pow_two] using mul_eq_one_iff_eq_inv.mp h
  rwa [inv_eq_self_of_sq_eq_one hw2 w] at h1

private theorem w1369_eq_on_of_eq_on_inf_fixV (hw2 : ∀ w : W, w ^ 2 = 1) {x s e : MulAut W}
    {V : Subgroup W} (hx3 : x ^ 3 = 1) (hfixX : fixV (Subgroup.zpowers x) = ⊥)
    (hs2 : s * s = 1) (hsx : s * x * s⁻¹ = x⁻¹) (hex : e * x = x * e)
    (hVx : ∀ u ∈ V, x u ∈ V) (hVs : ∀ u ∈ V, s u ∈ V)
    (he : ∀ u ∈ V ⊓ fixV (Subgroup.zpowers s), e u = u) : ∀ u ∈ V, e u = u := by
  have hnorm : ∀ w : W, (x ^ 2) w * x w = w := fun w => w1369_norm_mul hw2 hx3 hfixX w
  have hx2eq : x ^ 2 = x⁻¹ := by
    have h : x ^ 2 * x = 1 := by
      have h3 : x ^ 2 * x = x ^ 3 := by rw [← pow_succ]
      rw [h3, hx3]
    exact eq_inv_of_mul_eq_one_right h
  have hx2inv : (x ^ 2)⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one]
    have h3 : x ^ 2 * x = x ^ 3 := by rw [← pow_succ]
    rw [h3, hx3]
  have hsx' : s * x = x ^ 2 * s := by
    calc s * x = (s * x * s⁻¹) * s := by group
      _ = x⁻¹ * s := by rw [hsx]
      _ = x ^ 2 * s := by rw [← hx2eq]
  have hsx2' : s * x ^ 2 = x * s := by
    have h1 : s * x ^ 2 * s⁻¹ = x := by
      calc s * x ^ 2 * s⁻¹ = (s * x * s⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
        _ = (x⁻¹) ^ 2 := by rw [hsx]
        _ = (x ^ 2)⁻¹ := by rw [inv_pow]
        _ = x := hx2inv
    calc s * x ^ 2 = (s * x ^ 2 * s⁻¹) * s := by group
      _ = x * s := by rw [h1]
  have hssu : ∀ w : W, s (s w) = w := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) hs2
    simpa [MulAut.mul_apply] using h
  have hVx2 : ∀ u ∈ V, (x ^ 2) u ∈ V := by
    intro u hu
    have := hVx (x u) (hVx u hu)
    simpa [pow_two, MulAut.mul_apply] using this
  have hsx_apply : ∀ w : W, s (x w) = (x ^ 2) (s w) := by
    intro w
    calc s (x w) = (s * x) w := rfl
      _ = (x ^ 2 * s) w := by rw [hsx']
      _ = (x ^ 2) (s w) := rfl
  have hsx2_apply : ∀ w : W, s ((x ^ 2) w) = x (s w) := by
    intro w
    calc s ((x ^ 2) w) = (s * x ^ 2) w := rfl
      _ = (x * s) w := by rw [hsx2']
      _ = x (s w) := rfl
  have hex_sq : e * x ^ 2 = x ^ 2 * e := by
    calc e * x ^ 2 = (e * x) * x := by rw [pow_two]; group
      _ = (x * e) * x := by rw [hex]
      _ = x * (e * x) := by group
      _ = x * (x * e) := by rw [hex]
      _ = x ^ 2 * e := by rw [pow_two]; group
  have hex2 : ∀ w : W, e ((x ^ 2) w) = (x ^ 2) (e w) := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) hex_sq
    simpa [MulAut.mul_apply] using h
  intro u hu
  have ha : u * s u ∈ V ⊓ fixV (Subgroup.zpowers s) := by
    refine Subgroup.mem_inf.mpr ⟨V.mul_mem hu (hVs u hu), ?_⟩
    exact mem_fixV_zpowers_iff.mpr (by rw [map_mul, hssu u]; exact mul_comm (s u) u)
  have hb : x u * (x ^ 2) (s u) ∈ V ⊓ fixV (Subgroup.zpowers s) := by
    refine Subgroup.mem_inf.mpr ⟨V.mul_mem (hVx u hu) (hVx2 (s u) (hVs u hu)), ?_⟩
    exact mem_fixV_zpowers_iff.mpr
      (by rw [map_mul, hsx_apply u, hsx2_apply (s u), hssu u]; exact mul_comm _ _)
  have hcancel : (x ^ 2) (s u) * (x ^ 2) (s u) = 1 := by
    have h := hw2 ((x ^ 2) (s u))
    rwa [pow_two] at h
  have hux : u = (x ^ 2) (u * s u) * (x u * (x ^ 2) (s u)) := by
    symm
    calc (x ^ 2) (u * s u) * (x u * (x ^ 2) (s u))
        = ((x ^ 2) u * (x ^ 2) (s u)) * (x u * (x ^ 2) (s u)) := by rw [map_mul]
      _ = ((x ^ 2) u * x u) * ((x ^ 2) (s u) * (x ^ 2) (s u)) := by rw [mul_mul_mul_comm]
      _ = ((x ^ 2) u * x u) * 1 := by rw [hcancel]
      _ = (x ^ 2) u * x u := mul_one _
      _ = u := hnorm u
  calc e u = e ((x ^ 2) (u * s u) * (x u * (x ^ 2) (s u))) := by rw [← hux]
    _ = e ((x ^ 2) (u * s u)) * e (x u * (x ^ 2) (s u)) := map_mul e _ _
    _ = (x ^ 2) (e (u * s u)) * e (x u * (x ^ 2) (s u)) := by rw [hex2]
    _ = (x ^ 2) (u * s u) * (x u * (x ^ 2) (s u)) := by rw [he _ ha, he _ hb]
    _ = u := hux.symm

private theorem w1369_rk_eq_mQuot_add_rk (hw2 : ∀ w : W, w ^ 2 = 1) {U V : Subgroup W}
    (hUV : U ≤ V) : rk ↥V = E3.mQuot V U + rk ↥U := by
  have h2p : IsPGroup 2 ↥V := isPGroup_two_of_sq_eq_one fun v => Subtype.ext (hw2 (v : W))
  have hcard := E3.card_eq_two_pow_mul h2p hUV
  unfold rk
  rw [hcard, padicValNat.mul (pow_ne_zero _ (by norm_num)) (card_subgroup_pos U).ne',
    padicValNat.prime_pow]

theorem Std139.lemmaG (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    (hC : DNormComp G D) {K : Subgroup (MulAut W)} (hK : IsComponentOf K G)
    (hKD : ¬ K ≤ Subgroup.centralizer (D : Set (MulAut W))) :
    commSub ⊤ K = ⊤ ∧ fixV K = ⊥ := by
  classical
  have hKperf : ⁅K, K⁆ = K := w1369_commutator_eq_self_of_isQuasisimple hK.2.2
  have hKX : ∀ k ∈ K, ∀ x ∈ X, k * x = x * k := Std139.component_commutes_X S hK
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  haveI : Nontrivial ↥K := (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
  have hKne : K ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥K := by rw [hbot]; infer_instance
    exact false_of_nontrivial_of_subsingleton ↥K
  have hs2 : s * s = 1 := by
    have h : s ^ 2 = 1 := by rw [← S.s2]; exact pow_orderOf_eq_one s
    simpa [pow_two] using h
  have hsKmap : K.map (MulAut.conj s).toMonoidHom = K := by
    by_contra hne
    have hKscomp : IsComponentOf (K.map (MulAut.conj s).toMonoidHom) G :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK S.sG
    have hKsnotcent : ¬ K.map (MulAut.conj s).toMonoidHom ≤
        Subgroup.centralizer (D : Set (MulAut W)) := by
      intro hle
      apply hKD
      have hsd : ∀ d ∈ D, (MulAut.conj s) d = d := by
        intro d hd
        rw [MulAut.conj_apply, show s * d = d * s from (S.Dcs d hd).symm, mul_assoc,
          mul_inv_cancel, mul_one]
      have hset : (MulAut.conj s).toMonoidHom '' (D : Set (MulAut W)) = D := by
        ext x
        constructor
        · rintro ⟨d, hd, hfl⟩
          have : (MulAut.conj s).toMonoidHom d = d := by simpa using hsd d hd
          rwa [← hfl, this]
        · intro hx
          exact ⟨x, hx, by simpa using hsd x hx⟩
      have hCmap : (Subgroup.centralizer (D : Set (MulAut W))).map
          (MulAut.conj s).toMonoidHom ≤ Subgroup.centralizer (D : Set (MulAut W)) := by
        have h := Subgroup.map_centralizer_le_centralizer_image (D : Set (MulAut W))
          (MulAut.conj s).toMonoidHom
        rwa [hset] at h
      have hconj_sq : (MulAut.conj s : MulAut (MulAut W)) * (MulAut.conj s) = 1 := by
        rw [← map_mul, hs2, map_one]
      have hcomp : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          MonoidHom.id (MulAut W) := by
        ext x y
        simpa [MonoidHom.comp_apply, MonoidHom.id_apply, MulAut.mul_apply] using
          congrArg (fun f : MulAut (MulAut W) => (f x) y) hconj_sq
      have h' : (K.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom ≤
          Subgroup.centralizer (D : Set (MulAut W)) :=
        (Subgroup.map_mono hle).trans hCmap
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h'
      exact h'
    have := Std139.lemmaE hw2 S hn hC hK hKscomp hKD hKsnotcent
    exact hne this.symm
  obtain ⟨x, hxgen, hx3, hxne, hfixX, hsx⟩ := Std139.exists_gen hw2 S
  have hfixXz : fixV (Subgroup.zpowers x) = ⊥ := by rw [← hxgen]; exact hfixX
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  let U : Subgroup W := commSub ⊤ K
  let U₀ : Subgroup W := U ⊓ fixV (Subgroup.zpowers s)
  let A₀ : Subgroup W := U₀ ⊓ Y
  have hsKmem : ∀ r ∈ K, s * r * s⁻¹ ∈ K := by
    intro r hr
    have hmem : MulAut.conj s r ∈ K.map (MulAut.conj s).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hr
    have hmem' : MulAut.conj s r ∈ K := by rwa [hsKmap] at hmem
    simpa [MulAut.conj_apply] using hmem'
  have hUs : ∀ u ∈ U, s u ∈ U := w1369_commSub_invariant_of_normalizes hsKmem
  have hUX : StableUnder X U :=
    CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := K) (B := X) (M := ⊤)
      (fun y hy b hb => hKX y hy b hb) (fun b _ m _ => Subgroup.mem_top m)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hXrank : IsElemAbelianOfRank 3 1 ↥X :=
    ⟨mulEquivOfPrimeCardEq S.Xcard (by simp [Nat.card_eq_fintype_card])⟩
  have hinvX : ∀ y ∈ X, s * y * s⁻¹ = y⁻¹ := by
    have hc : MulAut.conj s x = x⁻¹ := by rw [MulAut.conj_apply, hsx]
    have hzpow : ∀ k : ℤ, s * x ^ k * s⁻¹ = (x ^ k)⁻¹ := by
      intro k
      calc s * x ^ k * s⁻¹ = MulAut.conj s (x ^ k) := (MulAut.conj_apply s _).symm
        _ = (MulAut.conj s x) ^ k := map_zpow (MulAut.conj s) x k
        _ = (x⁻¹) ^ k := by rw [hc]
        _ = (x ^ k)⁻¹ := by rw [inv_zpow]
    intro y hy
    rw [hxgen] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hzpow k
  have hcostU : rk ↥U = 2 * rk ↥(commSub U (Subgroup.zpowers s)) :=
    s13_cost_inverted (W := W) (fun w => by rw [← pow_two]; exact hw2 w) S.s2
      (p := 3) (n := 1) Nat.prime_three (by norm_num) (by norm_num)
      hXrank hinvX hUX hUs (by rw [hfixX, inf_bot_eq])
  have hstabU : ∀ y ∈ Subgroup.zpowers s, ∀ u ∈ U, y u ∈ U :=
    w1369_zpowers_stabilizes hs2 hUs
  have haddU : rk ↥(commSub U (Subgroup.zpowers s)) + rk ↥U₀ = rk ↥U :=
    CFSG.Quasithin.rk_commSub_add_rk_inf_fixV (V := W) (g := s) (W := U) hstabU
  have hrkU : rk ↥U = 2 * rk ↥U₀ := by omega
  have hDgt : 1 < Nat.card D := by
    rw [S.Dcard]
    have h2 : 2 ≤ n - 1 := by omega
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDgt
    omega
  obtain ⟨⟨e₀, he₀D⟩, he₀1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have he₀1 : e₀ ≠ 1 := fun h => he₀1sub (Subtype.ext h)
  have he₀2 : e₀ * e₀ = 1 := by rw [← pow_two]; exact S.elem.2 e₀ he₀D
  have he₀K : K.map (MulAut.conj e₀).toMonoidHom = K := hC K hK e₀ he₀D
  have hes₀ : s * e₀ = e₀ * s := (S.Dcs e₀ he₀D).symm
  have hRd0 : ⁅K, Subgroup.zpowers e₀⁆ = K := by
    have hne0 : ⁅K, Subgroup.zpowers e₀⁆ ≠ ⊥ := by
      intro hbot
      have hle : K ≤ Subgroup.centralizer (Subgroup.zpowers e₀ : Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hmem : ∀ k ∈ K, e₀ * k = k * e₀ := by
        intro k hk
        exact Subgroup.mem_centralizer_iff.mp (hle hk) e₀ (Subgroup.mem_zpowers e₀)
      exact he₀1 ((Std139.lemmaD hw2 S hn hC hK hKD).2 e₀ he₀D hmem)
    exact comm_eq_self_of_component hK he₀K hne0
  have hMeq : commSub U (Subgroup.zpowers e₀) = commSub ⊤ (Subgroup.zpowers e₀) :=
    (Std139.lemmaB hw2 S he₀D he₀1 hKX hKperf hKne he₀K hRd0).1
  have heU : ∀ e ∈ D, ∀ u ∈ U, e u ∈ U := by
    intro e he
    have heKmem : ∀ r ∈ K, e * r * e⁻¹ ∈ K := by
      intro r hr
      have hmem : MulAut.conj e r ∈ K.map (MulAut.conj e).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hr
      have hmem' : MulAut.conj e r ∈ K := by rw [hC K hK e he] at hmem; exact hmem
      simpa [MulAut.conj_apply] using hmem'
    exact w1369_commSub_invariant_of_normalizes heKmem
  have hefix : ∀ e ∈ D, ∀ u ∈ fixV (Subgroup.zpowers s), e u ∈ fixV (Subgroup.zpowers s) := by
    intro e he u hu
    rw [mem_fixV_zpowers_iff] at hu ⊢
    calc s (e u) = (s * e) u := rfl
      _ = (e * s) u := by rw [(S.Dcs e he).symm]
      _ = e (s u) := rfl
      _ = e u := by rw [hu]
  have hDstabU₀ : ∀ e ∈ D, ∀ u ∈ U₀, e u ∈ U₀ := by
    intro e he u hu
    exact ⟨heU e he u hu.1, hefix e he u hu.2⟩
  have hCUe : U₀ ⊓ fixV (Subgroup.zpowers e₀) = A₀ := by
    have hY := Std139.fixV_eq_axis hw2 S he₀D he₀1
    rw [hY]
  have hstabU₀e : ∀ y ∈ Subgroup.zpowers e₀, ∀ u ∈ U₀, y u ∈ U₀ :=
    w1369_zpowers_stabilizes he₀2 (hDstabU₀ e₀ he₀D)
  have hadd_e : rk ↥(commSub U₀ (Subgroup.zpowers e₀)) + rk ↥A₀ = rk ↥U₀ := by
    have h := CFSG.Quasithin.rk_commSub_add_rk_inf_fixV (V := W) (g := e₀) (W := U₀) hstabU₀e
    rwa [hCUe] at h
  let M : Subgroup W := commSub ⊤ (Subgroup.zpowers e₀)
  let M₀ : Subgroup W := M ⊓ fixV (Subgroup.zpowers s)
  have hMrk : rk ↥M = 2 := (Std139.commSub_axis hw2 S he₀D he₀1).1
  have hMX : StableUnder X M := (Std139.commSub_axis hw2 S he₀D he₀1).2.2
  have hMs : ∀ u ∈ M, s u ∈ M :=
    w1369_commSub_invariant_of_normalizes (R := Subgroup.zpowers e₀) (g := s)
      (fun r hr => by rw [w1369_conj_eq_self_of_comm hes₀.symm hr]; exact hr)
  have hcostM : rk ↥M = 2 * rk ↥(commSub M (Subgroup.zpowers s)) :=
    s13_cost_inverted (W := W) (fun w => by rw [← pow_two]; exact hw2 w) S.s2
      (p := 3) (n := 1) Nat.prime_three (by norm_num) (by norm_num)
      hXrank hinvX hMX hMs (by rw [hfixX, inf_bot_eq])
  have hstabMs : ∀ y ∈ Subgroup.zpowers s, ∀ u ∈ M, y u ∈ M :=
    w1369_zpowers_stabilizes hs2 hMs
  have haddM : rk ↥(commSub M (Subgroup.zpowers s)) + rk ↥M₀ = rk ↥M :=
    CFSG.Quasithin.rk_commSub_add_rk_inf_fixV (V := W) (g := s) (W := M) hstabMs
  have hrkM₀ : rk ↥M₀ = 1 := by omega
  have hleM : commSub U₀ (Subgroup.zpowers e₀) ≤ M := commSub_mono le_top le_rfl
  have hlefixs : commSub U₀ (Subgroup.zpowers e₀) ≤ fixV (Subgroup.zpowers s) :=
    w1369_commSub_le_fixV_of_commute (U := U₀) inf_le_right hes₀
  have hleM₀ : commSub U₀ (Subgroup.zpowers e₀) ≤ M₀ := le_inf hleM hlefixs
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, rk_bot] at hMrk
    omega
  have hneU₀e : commSub U₀ (Subgroup.zpowers e₀) ≠ ⊥ := by
    intro hbot
    have hU₀fix : U₀ ≤ fixV (Subgroup.zpowers e₀) := commSub_eq_bot_iff.mp hbot
    have he₀U₀ : ∀ u ∈ U₀, e₀ u = u := fun u hu => mem_fixV_zpowers_iff.mp (hU₀fix hu)
    have heqU : ∀ u ∈ U, e₀ u = u :=
      w1369_eq_on_of_eq_on_inf_fixV hw2 hx3 hfixXz hs2 hsx (S.DX e₀ he₀D x hxX)
        (fun u hu => hUX x hxX u hu) hUs he₀U₀
    have hbotU : commSub U (Subgroup.zpowers e₀) = ⊥ :=
      commSub_eq_bot_iff.mpr (fun u hu => mem_fixV_zpowers_iff.mpr (heqU u hu))
    have hbotM : commSub ⊤ (Subgroup.zpowers e₀) = ⊥ := hMeq ▸ hbotU
    exact hMne hbotM
  have hrkU₀e : rk ↥(commSub U₀ (Subgroup.zpowers e₀)) = 1 := by
    have hle1 : rk ↥(commSub U₀ (Subgroup.zpowers e₀)) ≤ 1 := by
      rw [← hrkM₀]
      exact rk_mono hleM₀
    have hpos : 0 < rk ↥(commSub U₀ (Subgroup.zpowers e₀)) := by
      rcases Nat.eq_zero_or_pos _ with h0 | h0
      · exact absurd ((rk_eq_zero_iff hw2).mp h0) hneU₀e
      · exact h0
    omega
  have hEelem : E3.mQuot U₀ A₀ = 1 := by
    have h1 := w1369_rk_eq_mQuot_add_rk hw2 (U := A₀) (V := U₀) inf_le_left
    omega
  have h1 : ∀ e ∈ D, ∀ u ∈ U₀, e u * u⁻¹ ∈ A₀ := by
    intro e he u hu
    have hleU₀ : commSub U₀ (Subgroup.zpowers e) ≤ U₀ :=
      commSub_le_of_invariant (w1369_zpowers_stabilizes (S.elem.2 e he) (hDstabU₀ e he))
    have hleY : commSub U₀ (Subgroup.zpowers e) ≤ Y := by
      rcases eq_or_ne e 1 with rfl | he1
      · have h : commSub U₀ (Subgroup.zpowers (1 : MulAut W)) = ⊥ := by
          rw [commSub_eq_bot_iff]
          intro u hu
          exact mem_fixV_zpowers_iff.mpr rfl
        rw [h]
        exact bot_le
      · exact (commSub_mono le_top le_rfl).trans (Std139.commSub_axis hw2 S he he1).2.1
    exact le_inf hleU₀ hleY (Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, u, hu, rfl⟩)
  have h2 : ∀ e ∈ D, ∀ a ∈ A₀, e a = a := by
    intro e he a ha
    rcases eq_or_ne e 1 with rfl | he1
    · rfl
    · have hY := Std139.fixV_eq_axis hw2 S he he1
      exact mem_fixV_zpowers_iff.mp (hY ▸ ha.2)
  have hfaith : ∀ e ∈ D, (∀ u ∈ U₀, e u = u) → e = 1 := by
    intro e he hfix
    by_contra he1
    have hY := Std139.fixV_eq_axis hw2 S he he1
    have hU₀le : U₀ ≤ fixV (Subgroup.zpowers e) := by
      intro u hu
      rw [mem_fixV_zpowers_iff]
      exact hfix u hu
    have hAeq : A₀ = U₀ := by
      apply le_antisymm inf_le_left
      exact le_inf le_rfl (hU₀le.trans (le_of_eq hY))
    have : E3.mQuot U₀ A₀ = 0 := by rw [hAeq, E3.mQuot_self]
    omega
  have hbound : Nat.card D ≤ Nat.card A₀ :=
    transvectionBound hw2 D U₀ A₀ inf_le_left hEelem hDstabU₀ hfaith h1 h2
  have hcardA : Nat.card A₀ = 2 ^ rk ↥A₀ := card_eq_two_pow hw2 A₀
  have hpowle : 2 ^ (n - 1) ≤ 2 ^ rk ↥A₀ := by
    rw [← S.Dcard, ← hcardA]
    exact hbound
  have hleA : n - 1 ≤ rk ↥A₀ := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpowle
  have hAne : A₀ ≠ U₀ := by
    intro h
    have : E3.mQuot U₀ A₀ = 0 := by rw [h, E3.mQuot_self]
    omega
  have hA₀U₀ : A₀ ≤ U₀ := by
    change U₀ ⊓ Y ≤ U₀
    exact inf_le_left
  have hrkA_lt : rk ↥A₀ < rk ↥U₀ := by
    rcases lt_or_eq_of_le (rk_mono (H := A₀) (K := U₀) hA₀U₀) with h | h
    · exact h
    · exact absurd (eq_of_le_of_rk_le hw2 hA₀U₀ (le_of_eq h.symm)) hAne
  have hrkW : rk ↥(⊤ : Subgroup W) = 2 * n := by
    rw [rk_top]
    unfold rk
    rw [S.card]
    have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    rw [h4, padicValNat.prime_pow]
  have hrkU₀_le : rk ↥U₀ ≤ n := by
    have htop : rk ↥U ≤ rk ↥(⊤ : Subgroup W) := rk_mono le_top
    rw [hrkU, hrkW] at htop
    omega
  have hsub : rk ↥U₀ - 1 ≤ n - 1 := Nat.sub_le_sub_right hrkU₀_le 1
  have hrkAeq : rk ↥A₀ = n - 1 := by omega
  have hrkU₀eq : rk ↥U₀ = n := by omega
  have hrkUeq : rk ↥U = 2 * n := by rw [hrkU, hrkU₀eq]
  have hUtop : U = ⊤ := by
    refine eq_of_le_of_rk_le hw2 le_top ?_
    rw [hrkW, hrkUeq]
  have hF := Std139.lemmaF hw2 S hn hC hK hKD
  refine ⟨hUtop, ?_⟩
  have hfixK : fixV K ⊓ commSub ⊤ K = ⊥ := hF.2.1
  have hUtop' : commSub ⊤ K = ⊤ := hUtop
  rw [hUtop', inf_top_eq] at hfixK
  exact hfixK

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
