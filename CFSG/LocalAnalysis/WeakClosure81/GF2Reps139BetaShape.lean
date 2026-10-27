module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_le_stabSub_of_stableUnder {K : Subgroup (MulAut W)} {M : Subgroup W}
    (h : StableUnder K M) : K ≤ stabSub M := by
  intro k hk
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by
    have h1 := h k⁻¹ (K.inv_mem hk) (k u) hu
    simpa using h1, fun hu => h k hk u hu⟩

private theorem w1369_rk_subgroupOf {H K : Subgroup W} (h : H ≤ K) :
    rk ↥(H.subgroupOf K) = rk ↥H := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

private theorem w1369_autSub_map_conj {K : Subgroup (MulAut W)} {U : Subgroup W}
    (hKU : K ≤ stabSub U) (t : ↥(stabSub U)) :
    (autSub K U).map (MulAut.conj (resHom U t)).toMonoidHom =
      autSub (K.map (MulAut.conj (t : MulAut W)).toMonoidHom) U := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgK, hgψ⟩ := mem_autSub.mp hψ
    refine mem_autSub.mpr ⟨t * g * t⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(g : MulAut W), hgK, rfl⟩
    · rw [← hgψ]
      show resHom U (t * g * t⁻¹) = resHom U t * resHom U g * (resHom U t)⁻¹
      rw [map_mul, map_mul, map_inv]
  · intro hφ
    obtain ⟨G, hGK, hGφ⟩ := mem_autSub.mp hφ
    obtain ⟨k, hkK, hkG⟩ := Subgroup.mem_map.mp hGK
    refine ⟨resHom U ⟨k, hKU hkK⟩, mem_autSub.mpr ⟨⟨k, hKU hkK⟩, hkK, rfl⟩, ?_⟩
    have hGeq : G = t * ⟨k, hKU hkK⟩ * t⁻¹ := by
      apply Subtype.ext
      rw [← hkG]
      rfl
    rw [← hGφ, hGeq]
    show resHom U t * resHom U ⟨k, hKU hkK⟩ * (resHom U t)⁻¹ =
      resHom U (t * ⟨k, hKU hkK⟩ * t⁻¹)
    rw [map_mul, map_mul, map_inv]

private theorem w1369_isIrrOn_autSub {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hKM : K ≤ stabSub M) (h : IsIrrOn K M ⊥) : IsIrrOn (autSub K M) ⊤ ⊥ := by
  refine ⟨?_, fun _ _ _ _ => Subgroup.mem_top _,
    fun φ _ u hu => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hu, map_one]), ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro htop
    have hM : M = ⊥ := by
      have hmap := congrArg (Subgroup.map M.subtype) htop
      rwa [Subgroup.map_bot, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact (ne_of_gt h.1) hM
  · intro J hJstab hbot htop
    let J' : Subgroup W := J.map M.subtype
    have hJ'stab : StableUnder K J' := by
      intro k hk w hw
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hw
      have hk' : resHom M ⟨k, hKM hk⟩ ∈ autSub K M :=
        mem_autSub.mpr ⟨⟨k, hKM hk⟩, hk, rfl⟩
      exact Subgroup.mem_map.mpr ⟨resHom M ⟨k, hKM hk⟩ j, hJstab _ hk' j hj, rfl⟩
    have hJ'M : J' ≤ M := by rintro _ ⟨j, -, rfl⟩; exact j.2
    rcases h.2.2.2 J' hJ'stab bot_le hJ'M with hJ'bot | hJ'top
    · left
      have hmap : Subgroup.map M.subtype J = ⊥ := hJ'bot
      refine Subgroup.map_injective M.subtype_injective ?_
      rw [hmap, Subgroup.map_bot]
    · right
      refine Subgroup.map_injective M.subtype_injective ?_
      rw [show Subgroup.map M.subtype J = M from hJ'top, Subgroup.map_top,
        Subgroup.range_subtype]

private noncomputable def w1369_autSubEquivOfFaithful {K : Subgroup (MulAut W)}
    {M : Subgroup W} (hKM : K ≤ stabSub M) (hfaith : K ⊓ centSub M = ⊥) :
    ↥K ≃* ↥(autSub K M) := by
  let f : ↥K →* MulAut ↥M := (resHom M).comp (Subgroup.inclusion hKM)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : f (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : ((Subgroup.inclusion hKM (a⁻¹ * b) : ↥(stabSub M)) : MulAut W) ∈ centSub M := by
      have h3 : Subgroup.inclusion hKM (a⁻¹ * b) ∈ (resHom M).ker :=
        MonoidHom.mem_ker.mpr h1
      rwa [ker_resHom, Subgroup.mem_subgroupOf] at h3
    have h4 : ((a⁻¹ * b : ↥K) : MulAut W) ∈ K ⊓ centSub M :=
      ⟨(a⁻¹ * b).2, by simpa using h2⟩
    rw [hfaith, Subgroup.mem_bot] at h4
    have h5 : a⁻¹ * b = 1 := Subtype.ext h4
    have h6 : b = a := by
      have h := congrArg (fun x : ↥K => a * x) h5
      simpa [mul_assoc] using h
    exact h6.symm
  have hrange : f.range = autSub K M := by
    ext φ
    constructor
    · intro hφ
      rw [MonoidHom.mem_range] at hφ
      obtain ⟨a, rfl⟩ := hφ
      exact mem_autSub.mpr ⟨Subgroup.inclusion hKM a, a.2, rfl⟩
    · intro hφ
      obtain ⟨g, hgK, hgφ⟩ := mem_autSub.mp hφ
      rw [MonoidHom.mem_range]
      refine ⟨⟨(g : MulAut W), hgK⟩, ?_⟩
      change resHom M (Subgroup.inclusion hKM ⟨(g : MulAut W), hgK⟩) = φ
      rw [show Subgroup.inclusion hKM ⟨(g : MulAut W), hgK⟩ = g from Subtype.ext rfl]
      exact hgφ
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)

theorem Std139.beta_shape (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K)
    (hnirr : ¬ IsIrrOn K ⊤ ⊥) : ShapeTensor K X n := by
  classical
  obtain ⟨M, x, hxX, hx1, hMirr, hint, hsum, hrk⟩ := Std139.beta_split hw2 S hn hK hnirr
  have hKstab : K ≤ stabSub M := w1369_le_stabSub_of_stableUnder hMirr.2.1
  have hDstab : D ≤ stabSub M := by
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1]; exact (stabSub M).one_mem
    · obtain ⟨hmem, -, -⟩ :=
        Std139.beta_cost hw2 S hn hK hMirr hxX hx1 hsum hint hd hd1
      rw [mem_stabSub]
      intro u
      refine ⟨fun hu => ?_, fun hu => hmem u hu⟩
      have hd2 : d ^ 2 = 1 := S.elem.2 d hd
      have hdu : d (d u) = u := by
        have h := congrArg (fun f : MulAut W => f u) hd2
        simpa [pow_two] using h
      rw [← hdu]
      exact hmem (d u) hu
  have hDfaith : ∀ d ∈ D, (∀ m ∈ M, d m = m) → d = 1 := by
    intro d hd hfix
    apply MulEquiv.ext
    intro w
    have hw : w ∈ M ⊔ M.map x.toMonoidHom := by rw [hsum]; exact Subgroup.mem_top w
    rw [Subgroup.mem_sup] at hw
    obtain ⟨m, hm, r, hr, rfl⟩ := hw
    obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hr
    have hdx : d * x = x * d := S.DX d hd x hxX
    have h1 : d (x m') = x m' := by
      have h := congrArg (fun f : MulAut W => f m') hdx
      simp only [MulAut.mul_apply] at h
      rw [h, hfix m' hm']
    calc d (m * x m') = d m * d (x m') := map_mul d m (x m')
      _ = m * d (x m') := by rw [hfix m hm]
      _ = m * x m' := by rw [h1]
  have hKfaith : ∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1 := by
    intro k hk hfix
    apply MulEquiv.ext
    intro w
    have hw : w ∈ M ⊔ M.map x.toMonoidHom := by rw [hsum]; exact Subgroup.mem_top w
    rw [Subgroup.mem_sup] at hw
    obtain ⟨m, hm, r, hr, rfl⟩ := hw
    obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hr
    have hkx : k * x = x * k := S.component_commutes_X hK.comp k hk x hxX
    have h1 : k (x m') = x m' := by
      have h := congrArg (fun f : MulAut W => f m') hkx
      simp only [MulAut.mul_apply] at h
      rw [h, hfix m' hm']
    calc k (m * x m') = k m * k (x m') := map_mul k m (x m')
      _ = m * k (x m') := by rw [hfix m hm]
      _ = m * x m' := by rw [h1]
  have hKcent : K ⊓ centSub M = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    exact hKfaith k hk.1 (fun m hm => mem_centSub.mp hk.2 m hm)
  have hDcent : D ⊓ centSub M = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    exact hDfaith d hd.1 (fun m hm => mem_centSub.mp hd.2 m hm)
  have hIso : ↥K ≃* ↥(autSub K M) := w1369_autSubEquivOfFaithful hKstab hKcent
  have hKqOpen : CFSG.Open.IsQuasisimple ↥(autSub K M) :=
    (CFSG.Open.IsQuasisimple.congr hIso).mp hK.comp.2.2
  have hKq : IsQuasisimple ↥(autSub K M) := A3.isQuasisimple_iff_open.mpr hKqOpen
  have hKperf : ⁅autSub K M, autSub K M⁆ = autSub K M := by
    haveI : Group.IsPerfect ↥(autSub K M) := hKq.1
    exact Subgroup.commutator_eq_self
  have hK1 : autSub K M ≠ ⊥ := by
    intro hbot
    have h0 : commSub M K = ⊥ := (autSub_eq_bot_iff hKstab).mp hbot
    have hMle : M ≤ fixV K := commSub_eq_bot_iff.mp h0
    have hMbot : M = ⊥ := le_bot_iff.mp (hMle.trans (le_of_eq hK.fix))
    exact (ne_of_gt hMirr.1) hMbot
  have hKirr : IsIrrOn (autSub K M) ⊤ ⊥ := w1369_isIrrOn_autSub hKstab hMirr
  have hDnorm : ∀ e ∈ autSub D M, (autSub K M).map (MulAut.conj e).toMonoidHom =
      autSub K M := by
    intro e he
    obtain ⟨g, hgD, hge⟩ := mem_autSub.mp he
    rw [← hge, w1369_autSub_map_conj hKstab g, hK.normal (g : MulAut W) (S.DG hgD)]
  have hDel : IsElemAbelian2 (autSub D M) := by
    constructor
    · intro a ha b hb
      obtain ⟨ga, hgaD, hga⟩ := mem_autSub.mp ha
      obtain ⟨gb, hgbD, hgb⟩ := mem_autSub.mp hb
      have hab : ga * gb = gb * ga :=
        Subtype.ext (S.elem.1 (ga : MulAut W) hgaD (gb : MulAut W) hgbD)
      calc a * b = resHom M ga * resHom M gb := by rw [← hga, ← hgb]
        _ = resHom M (ga * gb) := (map_mul (resHom M) ga gb).symm
        _ = resHom M (gb * ga) := by rw [hab]
        _ = resHom M gb * resHom M ga := map_mul (resHom M) gb ga
        _ = b * a := by rw [← hgb, ← hga]
    · intro a ha
      obtain ⟨ga, hgaD, hga⟩ := mem_autSub.mp ha
      have hga2 : ga ^ 2 = 1 := Subtype.ext (S.elem.2 (ga : MulAut W) hgaD)
      calc a ^ 2 = (resHom M ga) ^ 2 := by rw [← hga]
        _ = resHom M (ga * ga) := by rw [pow_two, ← map_mul]
        _ = resHom M (ga ^ 2) := by rw [pow_two]
        _ = resHom M 1 := by rw [hga2]
        _ = 1 := map_one (resHom M)
  have hD4 : 4 ≤ Nat.card ↥(autSub D M) := by
    have hcard : Nat.card ↥(autSub D M) = Nat.card ↥D := by
      have h := card_autSub_mul hDstab
      rw [hDcent, Subgroup.card_bot, mul_one] at h
      exact h
    rw [hcard, S.Dcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfix_e : ∀ d : ↥(stabSub M), (d : MulAut W) ∈ D → (d : MulAut W) ≠ 1 →
      fixV (Subgroup.zpowers (resHom M d)) = (Y ⊓ M).subgroupOf M := by
    intro d hdD hd1
    ext u
    rw [mem_fixV_zpowers_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hu
      have h1 : (u : W) ∈ fixV (Subgroup.zpowers (d : MulAut W)) := by
        rw [mem_fixV_zpowers_iff]
        have h := congrArg (fun v : ↥M => (v : W)) hu
        rwa [resHom_apply] at h
      have h2 : (u : W) ∈ Y := by
        rwa [Std139.fixV_eq_axis hw2 S hdD hd1] at h1
      exact ⟨h2, u.2⟩
    · rintro ⟨huY, -⟩
      have h1 : (u : W) ∈ fixV (Subgroup.zpowers (d : MulAut W)) := by
        rwa [Std139.fixV_eq_axis hw2 S hdD hd1]
      rw [mem_fixV_zpowers_iff] at h1
      apply Subtype.ext
      rw [resHom_apply]
      exact h1
  have hcomm_e : ∀ d : ↥(stabSub M), (d : MulAut W) ∈ D →
      commSub (⊤ : Subgroup ↥M) (Subgroup.zpowers (resHom M d)) =
        (commSub M (Subgroup.zpowers (d : MulAut W))).subgroupOf M := by
    intro d hdD
    have hstab : ∀ y ∈ Subgroup.zpowers (d : MulAut W), ∀ w ∈ M, y w ∈ M :=
      fun y hy w hw => (mem_stabSub.mp (Subgroup.zpowers_le.mpr (hDstab hdD) hy) w).2 hw
    have hle : Subgroup.map (commHom (d : MulAut W)) M ≤ M := by
      rw [← commSub_zpowers_eq_map hstab]
      exact commSub_le_of_invariant hstab
    have hstab' : ∀ y ∈ Subgroup.zpowers (resHom M d), ∀ w ∈ (⊤ : Subgroup ↥M), y w ∈ ⊤ :=
      fun y _ w _ => Subgroup.mem_top (y w)
    have hheq : (Subgroup.subtype M).comp (commHom (resHom M d)) =
        (commHom (d : MulAut W)).comp (Subgroup.subtype M) := by
      ext u
      change (((resHom M d) u * u⁻¹ : ↥M) : W) = (d : MulAut W) ((u : ↥M) : W) *
        (((u : ↥M) : W))⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv, resHom_apply]
    apply Subgroup.map_injective M.subtype_injective
    calc Subgroup.map (Subgroup.subtype M) (commSub ⊤ (Subgroup.zpowers (resHom M d)))
        = Subgroup.map (Subgroup.subtype M)
            (Subgroup.map (commHom (resHom M d)) ⊤) := by
          rw [commSub_zpowers_eq_map hstab']
      _ = Subgroup.map ((Subgroup.subtype M).comp (commHom (resHom M d))) ⊤ := by
          rw [Subgroup.map_map]
      _ = Subgroup.map ((commHom (d : MulAut W)).comp (Subgroup.subtype M)) ⊤ := by
          rw [hheq]
      _ = Subgroup.map (commHom (d : MulAut W)) M := by
          have h1 : Subgroup.map ((commHom (d : MulAut W)).comp (Subgroup.subtype M)) ⊤ =
              Subgroup.map (commHom (d : MulAut W))
                (Subgroup.map (Subgroup.subtype M) ⊤) :=
            (Subgroup.map_map (K := ⊤) (g := commHom (d : MulAut W))
              (f := Subgroup.subtype M)).symm
          have h2 : Subgroup.map (commHom (d : MulAut W))
                (Subgroup.map (Subgroup.subtype M) ⊤) =
              Subgroup.map (commHom (d : MulAut W)) M :=
            congrArg (Subgroup.map (commHom (d : MulAut W)))
              ((Subgroup.map_top (Subgroup.subtype M)).trans (Subgroup.range_subtype M))
          exact h1.trans h2
      _ = Subgroup.map (Subgroup.subtype M)
            ((commSub M (Subgroup.zpowers (d : MulAut W))).subgroupOf M) := by
          rw [Subgroup.subgroupOf_map_subtype]
          exact (commSub_zpowers_eq_map hstab).symm.trans
            (inf_of_le_left (commSub_le_of_invariant hstab)).symm
  have hrk_e : ∀ d : ↥(stabSub M), (d : MulAut W) ∈ D → (d : MulAut W) ≠ 1 →
      rk ↥(commSub (⊤ : Subgroup ↥M) (Subgroup.zpowers (resHom M d))) = 1 := by
    intro d hdD hd1
    have hstab : ∀ y ∈ Subgroup.zpowers (d : MulAut W), ∀ w ∈ M, y w ∈ M :=
      fun y hy w hw => (mem_stabSub.mp (Subgroup.zpowers_le.mpr (hDstab hdD) hy) w).2 hw
    rw [hcomm_e d hdD, w1369_rk_subgroupOf (commSub_le_of_invariant hstab)]
    exact (Std139.beta_cost hw2 S hn hK hMirr hxX hx1 hsum hint hdD hd1).2.1
  have hDtv : ∀ e ∈ autSub D M, e ≠ 1 →
      fixV (Subgroup.zpowers e) = (Y ⊓ M).subgroupOf M ∧
        rk ↥(commSub (⊤ : Subgroup ↥M) (Subgroup.zpowers e)) = 1 := by
    intro e he he1
    obtain ⟨d, hdD, hde⟩ := mem_autSub.mp he
    rw [← hde]
    have hd1 : (d : MulAut W) ≠ 1 := by
      intro h
      apply he1
      rw [← hde, show d = 1 from Subtype.ext h, map_one]
    exact ⟨hfix_e d hdD hd1, hrk_e d hdD hd1⟩
  have hDne : autSub D M ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD4
    omega
  obtain ⟨e₀, he₀1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have he₀ : (e₀ : MulAut ↥M) ∈ autSub D M := e₀.2
  have he₀1 : (e₀ : MulAut ↥M) ≠ 1 := fun h => he₀1sub (Subtype.ext h)
  obtain ⟨d₀, hd₀D, hd₀e⟩ := mem_autSub.mp he₀
  have hd₀1 : (d₀ : MulAut W) ≠ 1 := by
    intro h
    apply he₀1
    rw [← hd₀e, show d₀ = 1 from Subtype.ext h, map_one]
  have hA : rkIdx ((Y ⊓ M).subgroupOf M) = 1 := by
    have hfix₀ : fixV (Subgroup.zpowers (resHom M d₀)) = (Y ⊓ M).subgroupOf M :=
      hfix_e d₀ hd₀D hd₀1
    rw [← hfix₀, rkIdx_fixV_zpowers (resHom M d₀), commV_eq_commSub]
    exact hrk_e d₀ hd₀D hd₀1
  have hM2' : ∀ m : ↥M, m ^ 2 = 1 := fun m => Subtype.ext (by simpa using hw2 (m : W))
  obtain ⟨-, hcost₀⟩ := hDtv (e₀ : MulAut ↥M) he₀ he₀1
  have hdN₀ : (autSub K M).map (MulAut.conj (e₀ : MulAut ↥M)).toMonoidHom =
      autSub K M := hDnorm (e₀ : MulAut ↥M) he₀
  have he₀2 : (e₀ : MulAut ↥M) ^ 2 = 1 := hDel.2 (e₀ : MulAut ↥M) he₀
  have hKcentAut : Subgroup.centralizer (autSub K M : Set (MulAut ↥M)) = ⊥ :=
    centralizer_eq_bot_of_cost_one hM2' hKperf hK1 hKirr he₀2 hdN₀ hcost₀
  have hKe : ∀ e ∈ autSub D M, e ≠ 1 →
      ⁅autSub K M, Subgroup.zpowers e⁆ = autSub K M := by
    intro e he he1
    by_contra hne
    have hNnorm : Subgroup.zpowers e ≤
        Subgroup.normalizer (autSub K M : Set (MulAut ↥M)) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hDnorm e he))
    have hNle : ⁅autSub K M, Subgroup.zpowers e⁆ ≤ autSub K M :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hNnorm
    have hNnormal : ((⁅autSub K M, Subgroup.zpowers e⁆).subgroupOf (autSub K M)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (Subgroup.normalizer_commutator_ge_left (autSub K M) (Subgroup.zpowers e))
    haveI : ((⁅autSub K M, Subgroup.zpowers e⁆).subgroupOf (autSub K M)).Normal := hNnormal
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKqOpen
      ((⁅autSub K M, Subgroup.zpowers e⁆).subgroupOf (autSub K M)) with hcenter | htop
    · exfalso
      have hcenter_comm : ∀ r ∈ ⁅autSub K M, Subgroup.zpowers e⁆,
          ∀ k ∈ autSub K M, r * k = k * r := by
        intro r hr k hk
        have hrK : r ∈ autSub K M := hNle hr
        have hmem : (⟨r, hrK⟩ : ↥(autSub K M)) ∈
            (⁅autSub K M, Subgroup.zpowers e⁆).subgroupOf (autSub K M) :=
          Subgroup.mem_subgroupOf.mpr hr
        have hc := Subgroup.mem_center_iff.mp (hcenter hmem) (⟨k, hk⟩ : ↥(autSub K M))
        exact (congrArg Subtype.val hc).symm
      have hbot1 : ⁅⁅autSub K M, Subgroup.zpowers e⁆, autSub K M⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun r hr => by
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          exact (hcenter_comm r hr k hk).symm)
      have hbot2 : ⁅⁅Subgroup.zpowers e, autSub K M⁆, autSub K M⁆ = ⊥ := by
        rw [Subgroup.commutator_comm (Subgroup.zpowers e) (autSub K M)]
        exact hbot1
      have hbot3 : ⁅⁅autSub K M, autSub K M⁆, Subgroup.zpowers e⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := autSub K M)
          (H₂ := autSub K M) (H₃ := Subgroup.zpowers e) hbot1 hbot2
      rw [hKperf] at hbot3
      have hNbot' : ⁅Subgroup.zpowers e, autSub K M⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hbot3
      have hecent : e ∈ Subgroup.centralizer (autSub K M : Set (MulAut ↥M)) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hNbot') (Subgroup.mem_zpowers e)
      rw [hKcentAut, Subgroup.mem_bot] at hecent
      exact he1 hecent
    · exact hne (le_antisymm hNle (Subgroup.subgroupOf_eq_top.mp htop))
  have hn3 : 3 ≤ rk ↥M := by rw [hrk]; exact hn
  have hcore : autSub K M = ⊤ :=
    beta_core hM2' hKq hKirr hDnorm hDel hD4 ((Y ⊓ M).subgroupOf M) hA hDtv hKe hn3
  refine ⟨M, x, hxX, hx1, hMirr.2.1, hrk, hint, hsum, hKfaith, ?_⟩
  intro g
  have hg : g ∈ autSub K M := by rw [hcore]; exact Subgroup.mem_top g
  obtain ⟨gs, hgsK, hgsg⟩ := mem_autSub.mp hg
  exact ⟨(gs : MulAut W), hgsK, fun m => by rw [← hgsg, resHom_apply]⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
