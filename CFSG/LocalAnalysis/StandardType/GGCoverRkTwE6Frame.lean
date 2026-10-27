module

public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Quot
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.StandardType.E6ThreeModel CFSG.SeitzReduction.E6Pilot
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
open CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three

private lemma orderOf_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    orderOf (e g) = orderOf g := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, pow_orderOf_eq_one, map_one]
  · rw [orderOf_dvd_iff_pow_eq_one]
    have h : g ^ orderOf (e g) = e.symm ((e g) ^ orderOf (e g)) := by
      rw [map_pow, MulEquiv.symm_apply_apply]
    rw [h, pow_orderOf_eq_one, map_one]

private lemma frameMap_congr_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (f : MulAut G) (x : H) : MulAut.congr e f x = e (f (e.symm x)) := rfl

private def frameMap {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (D : FrameData R) : FrameData R' where
  H := D.H.map (MulAut.congr e)
  diag := (MulAut.congr e).toMonoidHom.comp D.diag
  Tor := D.Tor.map e
  nb := fun i => e (D.nb i)

private lemma frameMap_ad {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (D : FrameData R) (x : Fin Tag.E6.rank → ZMod 3) :
    (frameMap e D).ad x = MulAut.congr e (D.ad x) := rfl

private lemma frameMap_ad_apply {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (D : FrameData R) (x : Fin Tag.E6.rank → ZMod 3) (r : R') :
    (frameMap e D).ad x r = e (D.ad x (e.symm r)) := by
  rw [frameMap_ad, frameMap_congr_apply]

private lemma frameMap_nb {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (D : FrameData R) (i : Fin 6) : (frameMap e D).nb i = e (D.nb i) := rfl

private lemma frameMap_V0 {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (D : FrameData R) : (frameMap e D).V0 = D.V0.map e := by
  ext r
  constructor
  · rintro ⟨hrTor, v, hv, hconj⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hrTor
    change MulAut.conj (e t) = (frameMap e D).ad v at hconj
    refine Subgroup.mem_map.2 ⟨t, ⟨ht, v, hv, ?_⟩, rfl⟩
    apply (MulAut.congr e).injective
    rw [mulAut_congr_conj, hconj, ← frameMap_ad e D v]
  · rintro ⟨t, ⟨htTor, v, hv, hconj⟩, rfl⟩
    refine ⟨Subgroup.mem_map.2 ⟨t, htTor, rfl⟩, v, hv, ?_⟩
    have := congrArg (MulAut.congr e) hconj
    rw [mulAut_congr_conj, ← frameMap_ad e D v] at this
    exact this

private lemma GGNoInvFunc_map {L R R' : Type} [Group L] [Group R] [Group R']
    (e : R ≃* R') (ψ : L →* R') (N : Set L) (V : Subgroup R)
    (h : GGNoInvFunc (e.symm.toMonoidHom.comp ψ) N V) :
    GGNoInvFunc ψ N (V.map e) := by
  intro f hf
  let f' : V →* Multiplicative (ZMod 3) :=
    { toFun := fun v => f ⟨e v.1, Subgroup.mem_map.2 ⟨v.1, v.2, rfl⟩⟩
      map_one' := (congrArg f (Subtype.ext (map_one e))).trans (map_one f)
      map_mul' := fun v w =>
        (congrArg f (Subtype.ext (map_mul e v.1 w.1))).trans (map_mul f _ _) }
  have hf' : ∀ n ∈ N, ∀ v v' : V,
      (v' : R) = (e.symm.toMonoidHom.comp ψ) n * v * ((e.symm.toMonoidHom.comp ψ) n)⁻¹ →
      f' v' = f' v := by
    intro n hn v v' hv
    apply hf n hn
      (⟨e v.1, Subgroup.mem_map.2 ⟨v.1, v.2, rfl⟩⟩ : V.map e)
      (⟨e v'.1, Subgroup.mem_map.2 ⟨v'.1, v'.2, rfl⟩⟩ : V.map e)
    show e v'.1 = ψ n * e v.1 * (ψ n)⁻¹
    rw [hv, map_mul, map_mul, map_inv]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hf'1 : f' = 1 := h f' hf'
  ext w
  obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.1 w.2
  have hw : w = ⟨e v, Subgroup.mem_map.2 ⟨v, hv, rfl⟩⟩ := (Subtype.ext hveq).symm
  rw [hw]
  have := congrFun (congrArg DFunLike.coe hf'1) ⟨v, hv⟩
  simpa [f'] using this

private lemma GGNoInvAlt_map {L R R' : Type} [Group L] [Group R] [Group R']
    (e : R ≃* R') (ψ : L →* R') (N : Set L) (V : Subgroup R)
    (h : GGNoInvAlt (e.symm.toMonoidHom.comp ψ) N V) :
    GGNoInvAlt ψ N (V.map e) := by
  intro κ hκa hκb hκalt hκinv
  let κ' : V → V → Multiplicative (ZMod 3) := fun v w =>
    κ ⟨e v.1, Subgroup.mem_map.2 ⟨v.1, v.2, rfl⟩⟩ ⟨e w.1, Subgroup.mem_map.2 ⟨w.1, w.2, rfl⟩⟩
  have hκ'a : ∀ x y z, κ' (x * y) z = κ' x z * κ' y z := by
    intro x y z
    show κ ⟨e ((x * y).1), _⟩ ⟨e z.1, _⟩ =
      κ ⟨e x.1, _⟩ ⟨e z.1, _⟩ * κ ⟨e y.1, _⟩ ⟨e z.1, _⟩
    rw [show (⟨e ((x * y).1), Subgroup.mem_map.2 ⟨(x * y).1, V.mul_mem x.2 y.2, rfl⟩⟩ :
        V.map e) =
          ⟨e x.1, Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩⟩ *
            ⟨e y.1, Subgroup.mem_map.2 ⟨y.1, y.2, rfl⟩⟩ from
      Subtype.ext (map_mul e x.1 y.1), hκa]
  have hκ'b : ∀ x y z, κ' x (y * z) = κ' x y * κ' x z := by
    intro x y z
    show κ ⟨e x.1, _⟩ ⟨e ((y * z).1), _⟩ =
      κ ⟨e x.1, _⟩ ⟨e y.1, _⟩ * κ ⟨e x.1, _⟩ ⟨e z.1, _⟩
    rw [show (⟨e ((y * z).1), Subgroup.mem_map.2 ⟨(y * z).1, V.mul_mem y.2 z.2, rfl⟩⟩ :
        V.map e) =
          ⟨e y.1, Subgroup.mem_map.2 ⟨y.1, y.2, rfl⟩⟩ *
            ⟨e z.1, Subgroup.mem_map.2 ⟨z.1, z.2, rfl⟩⟩ from
      Subtype.ext (map_mul e y.1 z.1), hκb]
  have hκ'alt : ∀ x, κ' x x = 1 := fun x => hκalt _
  have hκ'inv : ∀ n ∈ N, ∀ x y x' y' : V,
      (x' : R) = (e.symm.toMonoidHom.comp ψ) n * x * ((e.symm.toMonoidHom.comp ψ) n)⁻¹ →
      (y' : R) = (e.symm.toMonoidHom.comp ψ) n * y * ((e.symm.toMonoidHom.comp ψ) n)⁻¹ →
      κ' x' y' = κ' x y := by
    intro n hn x y x' y' hx hy
    apply hκinv n hn
      (⟨e x.1, Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩⟩ : V.map e)
      (⟨e y.1, Subgroup.mem_map.2 ⟨y.1, y.2, rfl⟩⟩ : V.map e)
      (⟨e x'.1, Subgroup.mem_map.2 ⟨x'.1, x'.2, rfl⟩⟩ : V.map e)
      (⟨e y'.1, Subgroup.mem_map.2 ⟨y'.1, y'.2, rfl⟩⟩ : V.map e)
    · show e x'.1 = ψ n * e x.1 * (ψ n)⁻¹
      rw [hx, map_mul, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    · show e y'.1 = ψ n * e y.1 * (ψ n)⁻¹
      rw [hy, map_mul, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hκ'1 : ∀ x y, κ' x y = 1 := h κ' hκ'a hκ'b hκ'alt hκ'inv
  intro x y
  obtain ⟨x₀, hx₀, hxeq⟩ := Subgroup.mem_map.1 x.2
  obtain ⟨y₀, hy₀, hyeq⟩ := Subgroup.mem_map.1 y.2
  have hx : (⟨e x₀, Subgroup.mem_map.2 ⟨x₀, hx₀, rfl⟩⟩ : V.map e) = x := Subtype.ext hxeq
  have hy : (⟨e y₀, Subgroup.mem_map.2 ⟨y₀, hy₀, rfl⟩⟩ : V.map e) = y := Subtype.ext hyeq
  rw [← hx, ← hy]
  exact hκ'1 ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩

private theorem frameMap_good {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {D : FrameData R} (hD : D.Good) : (frameMap e D).Good := by
  have hφinj : Function.Injective (MulAut.congr e) := (MulAut.congr e).injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : e.symm x ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      apply e.injective
      calc e (y * e.symm x) = e y * x := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = x * e y := hx (e y)
        _ = e (e.symm x * y) := by rw [map_mul, MulEquiv.apply_symm_apply]
    rw [hD.center, Subgroup.mem_bot] at hx'
    simpa using congrArg e hx'
  · intro x y hxy
    change MulAut.congr e (D.diag x) = MulAut.congr e (D.diag y) at hxy
    exact hD.faithful (hφinj hxy)
  · intro X hX hXab hXcard
    let φ : MulAut R →* MulAut R' := (MulAut.congr e).toMonoidHom
    let X' : Subgroup (MulAut R) := X.comap φ
    have hX'H : X' ≤ D.H := by
      intro x hx
      obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.1 (hX (Subgroup.mem_comap.1 hx))
      have : h = x := hφinj hhx
      simpa [this] using hh
    have hX'ab : CFSG.Open.IsElemAbelian 3 X' := by
      constructor
      · refine IsMulCommutative.of_comm (fun a b => ?_)
        apply Subtype.ext
        apply hφinj
        show φ ((a : MulAut R) * (b : MulAut R)) = φ ((b : MulAut R) * (a : MulAut R))
        rw [map_mul, map_mul]
        exact congrArg Subtype.val
          (hXab.1.is_comm.comm ⟨φ a, Subgroup.mem_comap.1 a.2⟩ ⟨φ b, Subgroup.mem_comap.1 b.2⟩)
      · intro a ha
        apply hφinj
        show φ (a ^ 3) = φ 1
        rw [map_pow, map_one]
        exact hXab.2 (φ a) (Subgroup.mem_comap.1 ha)
    have hmapEq : X'.map φ = X := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_comap.1 hx
      · intro hy
        refine Subgroup.mem_map.2 ⟨(MulAut.congr e).symm y, ?_, ?_⟩
        · exact Subgroup.mem_comap.2 (by
            rwa [show φ ((MulAut.congr e).symm y) = y from (MulAut.congr e).apply_symm_apply y])
        · exact (MulAut.congr e).apply_symm_apply y
    have hX'card : Nat.card X' = Nat.card X := by
      rw [← hmapEq, Subgroup.card_map_of_injective hφinj]
    obtain ⟨γ', hγ', hγ'conj⟩ := hD.shape X' hX'H hX'ab (by rw [hX'card]; exact hXcard)
    have hdiagrange : (frameMap e D).diag.range = D.diag.range.map φ := by
      rw [show (frameMap e D).diag = φ.comp D.diag from rfl, MonoidHom.range_comp]
    refine ⟨φ γ', Subgroup.mem_map.2 ⟨γ', hγ', rfl⟩, ?_⟩
    intro x hx
    have hxmap : x ∈ X'.map φ := by rw [hmapEq]; exact hx
    obtain ⟨x', hx'mem, rfl⟩ := Subgroup.mem_map.1 hxmap
    have h := hγ'conj x' hx'mem
    rw [hdiagrange]
    exact Subgroup.mem_map.2 ⟨γ' * x' * γ'⁻¹, h, by rw [map_mul, map_mul, map_inv]⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro s hs t ht
      obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
      obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
      rw [← map_mul, ← map_mul, hD.torus.1 s' hs' t' ht']
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
      change Odd (orderOf (e t'))
      rw [orderOf_mulEquiv e t']
      exact hD.torus.2.1 t' ht'
    · intro x t ht
      obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
      show (frameMap e D).ad x (e t') = e t'
      rw [frameMap_ad_apply, MulEquiv.symm_apply_apply, hD.torus.2.2 x t' ht']
  · intro r
    constructor
    · intro h
      have h' : e.symm r ∈ D.Tor := (hD.cent (e.symm r)).mp (fun v hv => by
        apply e.injective
        have := h v hv
        rw [frameMap_ad_apply] at this
        rw [this, MulEquiv.apply_symm_apply])
      exact Subgroup.mem_map.2 ⟨e.symm r, h', by simp⟩
    · intro hr
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hr
      intro v hv
      show (frameMap e D).ad v (e t) = e t
      rw [frameMap_ad_apply, MulEquiv.symm_apply_apply]
      exact congrArg e ((hD.cent t).mpr ht v hv)
  · intro v hv
    obtain ⟨r, hr, hr3, hrc⟩ := hD.inner v hv
    refine ⟨e r, Subgroup.mem_map.2 ⟨r, hr, rfl⟩, ?_, ?_⟩
    · rw [← map_pow, hr3, map_one]
    · have := congrArg (MulAut.congr e) hrc
      rw [mulAut_congr_conj, ← frameMap_ad e D v] at this
      exact this
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      show e (D.nb i) * e (D.nb i) = 1
      rw [← map_mul, hD.weyl.1 i, map_one]
    · intro i t ht
      obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
      refine Subgroup.mem_map.2 ⟨D.nb i * t' * (D.nb i)⁻¹, hD.weyl.2.1 i t' ht', ?_⟩
      show e (D.nb i * t' * (D.nb i)⁻¹) = e (D.nb i) * e t' * (e (D.nb i))⁻¹
      rw [map_mul, map_mul, map_inv]
    · intro i x
      rw [frameMap_nb]
      rw [frameMap_ad e D x]
      rw [← mulAut_congr_conj e (D.nb i), ← map_inv, ← map_mul, ← map_mul]
      rw [hD.weyl.2.2.1 (i : Fin Tag.E6.rank) x]
      rfl
    · intro i x
      obtain ⟨hwTor, v, hv, hvw⟩ := hD.weyl.2.2.2 i x
      refine ⟨?_, v, hv, ?_⟩
      · refine Subgroup.mem_map.2 ⟨D.nb i * (D.ad x (D.nb i))⁻¹, hwTor, ?_⟩
        show e (D.nb i * (D.ad x (D.nb i))⁻¹) =
          e (D.nb i) * ((frameMap e D).ad x (e (D.nb i)))⁻¹
        rw [map_mul, map_inv, frameMap_ad_apply, MulEquiv.symm_apply_apply]
      · have := congrArg (MulAut.congr e) hvw
        rw [mulAut_congr_conj, ← frameMap_ad e D v] at this
        simpa only [frameMap_nb, frameMap_ad_apply, MulEquiv.symm_apply_apply, map_mul, map_inv]
          using this
  · intro L _ ψ N hN
    let ψ' : L →* R := e.symm.toMonoidHom.comp ψ
    have hN' : ∀ i, ∃ n ∈ N, ψ' n = D.nb i := by
      intro i
      obtain ⟨n, hn, hn'⟩ := hN i
      exact ⟨n, hn, by
        show e.symm (ψ n) = D.nb i
        rw [hn', frameMap_nb, MulEquiv.symm_apply_apply]⟩
    obtain ⟨h1, h2, h3⟩ := hD.modules ψ' N hN'
    refine ⟨?_, ?_, ?_⟩
    · show GGNoInvFunc ψ N (D.Tor.map e)
      exact GGNoInvFunc_map e ψ N D.Tor h1
    · show GGNoInvAlt ψ N (D.Tor.map e)
      exact GGNoInvAlt_map e ψ N D.Tor h2
    · show GGNoInvFunc ψ N (frameMap e D).V0
      rw [frameMap_V0]
      exact GGNoInvFunc_map e ψ N D.V0 h3
  · intro r S hS h
    have h' : ∀ x ∈ S, ∃ y ∈ S,
        MulAut.conj (e.symm r) * D.ad x * (MulAut.conj (e.symm r))⁻¹ = D.ad y := by
      intro x hx
      obtain ⟨y, hy, hy'⟩ := h x hx
      refine ⟨y, hy, ?_⟩
      apply hφinj
      rw [map_mul, map_mul, map_inv, mulAut_congr_conj, MulEquiv.apply_symm_apply,
        ← frameMap_ad e D x, ← frameMap_ad e D y]
      exact hy'
    obtain ⟨u, hu⟩ := hD.norm (e.symm r) S hS h'
    refine ⟨u, ?_⟩
    intro x hx
    have := congrArg (MulAut.congr e) (hu x hx)
    rw [map_mul, map_mul, map_inv, mulAut_congr_conj, MulEquiv.apply_symm_apply,
      ← frameMap_ad e D x, ← frameMap_ad e D (adAct .E6 3 u x)] at this
    exact this
  · intro α S hS h
    let α' : MulAut R := (MulAut.congr e).symm α
    have hα : MulAut.congr e α' = α := MulEquiv.apply_symm_apply _ _
    have h' : ∀ x ∈ S, ∃ y ∈ S, α' * D.ad x * α'⁻¹ = D.ad y := by
      intro x hx
      obtain ⟨y, hy, hy'⟩ := h x hx
      refine ⟨y, hy, ?_⟩
      apply hφinj
      rw [map_mul, map_mul, map_inv, hα, ← frameMap_ad e D x, ← frameMap_ad e D y]
      exact hy'
    obtain ⟨c, u, hc, hu⟩ := hD.aut α' S hS h'
    refine ⟨c, u, hc, ?_⟩
    intro x hx
    have := congrArg (MulAut.congr e) (hu x hx)
    rw [map_mul, map_mul, map_inv, hα, ← frameMap_ad e D x,
      ← frameMap_ad e D (c • adAct .E6 3 u x)] at this
    exact this

private lemma rgrpConjAut_comm
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {a b : ↥(TwistedDiag.Rgrp Ω Fr)}
    (h : (a : ModGL Tag.E6 Ω) * (b : ModGL Tag.E6 Ω) =
      (b : ModGL Tag.E6 Ω) * (a : ModGL Tag.E6 Ω)) :
    rgrpConjAut hn hK σ hσ Fr hFr a * rgrpConjAut hn hK σ hσ Fr hFr b =
      rgrpConjAut hn hK σ hσ Fr hFr b * rgrpConjAut hn hK σ hσ Fr hFr a := by
  have hab : a * b = b * a := Subtype.ext h
  have := congrArg (rgrpConjAut hn hK σ hσ Fr hFr) hab
  rwa [map_mul, map_mul] at this

theorem exists_langFrame_recipeR
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ (D : FrameData (TwE6Delta.RecipeR K n))
      (X : Subgroup (MulAut (TwE6Delta.RecipeR K n))),
      D.Good ∧ (D.H : Set (MulAut (TwE6Delta.RecipeR K n))) = TwE6Delta.RecipeI K n ∧
      Nat.card D.H = numTwistedE6 (2 ^ n) ∧ Nat.card D.H = 3 * Nat.card (TwE6Delta.RecipeR K n) ∧
      X ≤ D.H ∧ Nat.card X = (2 ^ n + 1) ^ 6 ∧
      (∀ x ∈ X, ∀ v ∈ D.diag.range, x * v = v * x) ∧
      ¬ X ≤ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range ∧
      D.diag.range ≤ D.H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have h30 : (3 : AlgebraicClosure K) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := AlgebraicClosure K) h30
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := n) hn hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0)
  have hL : IsLang Fr g := ⟨hg, hgn⟩
  obtain ⟨D₀, hD₀⟩ := exists_tFrame hn hK σ hσ Fr hFr h3 hL hζ hζo
  have hgood : D₀.Good :=
    { center := tFrame_center hn hK σ hσ
      faithful := tFrame_faithful hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      shape := tFrame_shape hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      torus := tFrame_torus hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      cent := tFrame_cent hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      inner := tFrame_inner hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      weyl := tFrame_weyl hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      modules := tFrame_modules hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      norm := tFrame_norm hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
      aut := tFrame_aut hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀ }
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  let D : FrameData (TwE6Delta.RecipeR K n) := frameMap ε D₀
  obtain ⟨hfinR, hCR, hCnorm, hCidx, hRcard⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) (f := n) hn K hK σ.toRingHom hσ h3
      (AlgebraicClosure K) Fr hFr
  have hH : (D.H : Set (MulAut (TwE6Delta.RecipeR K n))) = TwE6Delta.RecipeI K n := by
    ext y
    change y ∈ D₀.H.map (MulAut.congr ε) ↔ y ∈ TwE6Delta.RecipeI K n
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hε x).2 (by rwa [hD₀.H_eq] at hx)
    · intro hy
      refine Subgroup.mem_map.2 ⟨(MulAut.congr ε).symm y, ?_, ?_⟩
      · have h := (hε ((MulAut.congr ε).symm y)).1 (by rwa [MulEquiv.apply_symm_apply])
        rwa [hD₀.H_eq]
      · exact (MulAut.congr ε).apply_symm_apply y
  have hDH : D.H = D₀.H.map (MulAut.congr ε) := rfl
  have hDHcard : Nat.card D.H = numTwistedE6 (2 ^ n) := by
    have hmap : Nat.card D.H = Nat.card D₀.H := by
      rw [hDH, Subgroup.card_map_of_injective (MulAut.congr ε).injective]
    rw [hmap]
    have hrange : Nat.card D₀.H = Nat.card (TwistedDiag.Rgrp (AlgebraicClosure K) Fr) := by
      rw [hD₀.H_eq, ← rgrpConjAut_range hn hK σ hσ Fr hFr]
      rw [MonoidHom.range_eq_map,
        Subgroup.card_map_of_injective (rgrpConjAut_injective hn hK σ hσ Fr hFr),
        Subgroup.card_top]
    rw [hrange]
    exact hRcard
  have hD3 : Nat.card D.H = 3 * Nat.card (TwE6Delta.RecipeR K n) := by
    rw [hDHcard]
    have hC3 : Nat.card (TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K)) * 3 =
        Nat.card (TwistedDiag.Rgrp (AlgebraicClosure K) Fr) := by
      have h := Subgroup.relIndex_mul_card (TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K))
        (TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
      rw [hCidx, inf_of_le_left hCR] at h
      rw [← h, Nat.mul_comm]
    have hCgC0 : Nat.card (TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K)) =
        Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
      show Nat.card ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K)))) = _
      rw [Subgroup.card_map_of_injective (baseChangeGL_injective _)]
    have hC0R : Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =
        Nat.card (TwE6Delta.RecipeR K n) := Nat.card_congr ε.toEquiv
    calc numTwistedE6 (2 ^ n) = Nat.card (TwistedDiag.Rgrp (AlgebraicClosure K) Fr) := hRcard.symm
      _ = Nat.card (TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K)) * 3 := hC3.symm
      _ = Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) * 3 := by rw [hCgC0]
      _ = Nat.card (TwE6Delta.RecipeR K n) * 3 := by rw [hC0R]
      _ = 3 * Nat.card (TwE6Delta.RecipeR K n) := Nat.mul_comm _ _
  have htheta_sub : TwistedDiag.thetaTorus (AlgebraicClosure K) (2 ^ n) ≤
      TwistedDiag.thetaFixed Fr := by
    intro x hx
    rw [← TwistedDiag.torus_inf_thetaFixed (Fr := Fr) hFr] at hx
    exact hx.2
  let X' : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)) :=
    (TwistedDiag.thetaTorus (AlgebraicClosure K) (2 ^ n)).map (MulAut.conj g).toMonoidHom
  have hX'card : Nat.card X' = (2 ^ n + 1) ^ 6 := by
    show Nat.card ((TwistedDiag.thetaTorus (AlgebraicClosure K) (2 ^ n)).map
      (MulAut.conj g).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hq0 : ((2 ^ n : ℕ) : AlgebraicClosure K) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero (AlgebraicClosure K) 2]
      exact zero_pow (by omega : n ≠ 0)
    rw [TwistedDiag.natCard_thetaTorus (Ω := AlgebraicClosure K) hq0]
  have hX'R : X' ≤ TwistedDiag.Rgrp (AlgebraicClosure K) Fr := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact (TwistedDiag.mem_thetaFixed_iff_conj Fr hL.1 hL.2 y).1 (htheta_sub hy)
  have hX'notC : ¬ X' ≤ TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K) := by
    intro hle
    apply langTorus_not_le_cgrp hn hK σ hσ Fr hFr h3 hL hζ hζo hD₀
    intro y hy
    exact hle (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
  have hzetaT : ∀ x : Fin Tag.E6.rank → ZMod 3,
      rootDiagUnit Tag.E6 (zetaVec ζ hζ x) ∈
        TwistedDiag.thetaTorus (AlgebraicClosure K) (2 ^ n) := by
    intro x
    refine TwistedDiag.mem_thetaTorus.2 ⟨zetaVec ζ hζ x, ?_, rfl⟩
    intro i
    obtain ⟨k, hk⟩ := h3
    have hb : zetaVec ζ hζ x i ^ 3 = 1 := by
      rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [hk, pow_mul, hb, one_pow]
  have hcomm : ∀ a ∈ X', ∀ x : Fin Tag.E6.rank → ZMod 3,
      a * (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) =
      (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) * a := by
    intro a ha x
    obtain ⟨y, hy, hy_eq⟩ := Subgroup.mem_map.1 ha
    obtain ⟨c, hc, hc_eq⟩ := TwistedDiag.mem_thetaTorus.1 hy
    rw [← hy_eq, hc_eq]
    change (g * rootDiagUnit Tag.E6 c * g⁻¹) *
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) =
      (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
        (g * rootDiagUnit Tag.E6 c * g⁻¹)
    calc (g * rootDiagUnit Tag.E6 c * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹)
        = g * (rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 (zetaVec ζ hζ x)) * g⁻¹ := by
            group
      _ = g * (rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * rootDiagUnit Tag.E6 c) * g⁻¹ := by
            rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
      _ = (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
          (g * rootDiagUnit Tag.E6 c * g⁻¹) := by group
  let X₀ : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    (X'.subgroupOf (TwistedDiag.Rgrp (AlgebraicClosure K) Fr)).map
      (rgrpConjAut hn hK σ hσ Fr hFr)
  have hX₀card : Nat.card X₀ = (2 ^ n + 1) ^ 6 := by
    show Nat.card ((X'.subgroupOf (TwistedDiag.Rgrp (AlgebraicClosure K) Fr)).map
      (rgrpConjAut hn hK σ hσ Fr hFr)) = _
    rw [Subgroup.card_map_of_injective (rgrpConjAut_injective hn hK σ hσ Fr hFr)]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX'R).toEquiv]
    exact hX'card
  have hX₀H : X₀ ≤ D₀.H := by
    rw [hD₀.H_eq, ← rgrpConjAut_range hn hK σ hσ Fr hFr]
    exact Subgroup.map_le_range _ _
  have hX₀cent : ∀ a ∈ X₀, ∀ v ∈ D₀.diag.range, a * v = v * a := by
    intro a ha v hv
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨w, rfl⟩ := hv
    obtain ⟨hwr, hw_eq⟩ := hD₀.diag_eq (Multiplicative.toAdd w)
    rw [show D₀.diag w = D₀.ad (Multiplicative.toAdd w) from rfl, hw_eq]
    exact rgrpConjAut_comm hn hK σ hσ Fr hFr
      (hcomm a' (Subgroup.mem_subgroupOf.1 ha') (Multiplicative.toAdd w))
  have hInnEq :
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range =
      ((TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K)).subgroupOf
        (TwistedDiag.Rgrp (AlgebraicClosure K) Fr)).map (rgrpConjAut hn hK σ hσ Fr hFr) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨c, rfl⟩
      have hcΓ : (c : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ :=
        RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2
      set w := twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨c, hcΓ⟩ with hw
      have hwC : (w : ModGL Tag.E6 (AlgebraicClosure K)) ∈
          TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K) := by
        refine Subgroup.mem_map.2 ⟨(c : ModGL TwistTag.E6.tag K), c.2, ?_⟩
        exact (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr ⟨c, hcΓ⟩).symm
      refine Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 hwC, ?_⟩
      rw [rgrpConjAut_apply_baseChange]
      exact RecipeExcLang.twConj_of_mem_C0 σ c
    · rintro _ ⟨y, hy, rfl⟩
      have hyC : (y : ModGL Tag.E6 (AlgebraicClosure K)) ∈
          TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K) := Subgroup.mem_subgroupOf.1 hy
      obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.1 hyC
      let c₀ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨c, hc⟩
      refine ⟨c₀, ?_⟩
      have hcΓ : (c₀ : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ :=
        RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c₀.2
      have h1 : twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨c₀, hcΓ⟩ = y := by
        refine Subtype.ext ?_
        rw [twInndiagEquivRgrp_apply]
        exact hceq
      rw [← h1, rgrpConjAut_apply_baseChange]
      exact (RecipeExcLang.twConj_of_mem_C0 σ c₀).symm
  have hX₀notinn : ¬ X₀ ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := by
    intro hle
    apply hX'notC
    intro x hx
    have hxR : x ∈ TwistedDiag.Rgrp (AlgebraicClosure K) Fr := hX'R hx
    have hx₀ : rgrpConjAut hn hK σ hσ Fr hFr ⟨x, hxR⟩ ∈ X₀ :=
      Subgroup.mem_map.2 ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have hinn := hle hx₀
    rw [hInnEq] at hinn
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 hinn
    have hzC : (z : ModGL Tag.E6 (AlgebraicClosure K)) ∈
        TwistedDiag.Cgrp K σ.toRingHom (AlgebraicClosure K) := Subgroup.mem_subgroupOf.1 hz
    have hzx : (z : ModGL Tag.E6 (AlgebraicClosure K)) = x := by
      have := rgrpConjAut_injective hn hK σ hσ Fr hFr hzeq
      exact congrArg Subtype.val this
    rwa [← hzx]
  let X : Subgroup (MulAut (TwE6Delta.RecipeR K n)) := X₀.map (MulAut.congr ε)
  have hXle : X ≤ D.H := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨a, hX₀H ha, rfl⟩
  have hXcard : Nat.card X = (2 ^ n + 1) ^ 6 := by
    have hX_eq : X = X₀.map (MulAut.congr ε) := rfl
    rw [hX_eq, Subgroup.card_map_of_injective (MulAut.congr ε).injective]
    exact hX₀card
  have hXcent : ∀ y ∈ X, ∀ v ∈ D.diag.range, y * v = v * y := by
    intro y hy v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have hdiagrange : D.diag.range =
        D₀.diag.range.map (MulAut.congr ε).toMonoidHom := by
      rw [show D.diag = (MulAut.congr ε).toMonoidHom.comp D₀.diag from rfl,
        MonoidHom.range_comp]
    rw [hdiagrange] at hv
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hv
    calc MulAut.congr ε a * MulAut.congr ε b = MulAut.congr ε (a * b) :=
          (map_mul (MulAut.congr ε) a b).symm
      _ = MulAut.congr ε (b * a) := by rw [hX₀cent a ha b hb]
      _ = MulAut.congr ε b * MulAut.congr ε a := map_mul (MulAut.congr ε) b a
  have hconjR : (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)).range =
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range.map (MulAut.congr ε) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨r, rfl⟩
      refine Subgroup.mem_map.2 ⟨MulAut.conj (ε.symm r), ⟨ε.symm r, rfl⟩, ?_⟩
      change MulAut.congr ε (MulAut.conj (ε.symm r)) = MulAut.conj r
      rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨c, rfl⟩ := hb
      exact ⟨ε c, (mulAut_congr_conj ε c).symm⟩
  have hXnotinn : ¬ X ≤
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
    intro hle
    apply hX₀notinn
    intro a ha
    have haX : MulAut.congr ε a ∈ X₀.map (MulAut.congr ε) :=
      Subgroup.mem_map.2 ⟨a, ha, rfl⟩
    have h := hle haX
    rw [hconjR] at h
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.1 h
    have hba : b = a := (MulAut.congr ε).injective hbeq
    exact hba ▸ hb
  have hD₀diag_le : D₀.diag.range ≤ D₀.H := by
    intro v hv
    obtain ⟨w, rfl⟩ := hv
    obtain ⟨hx, hx_eq⟩ := hD₀.diag_eq (Multiplicative.toAdd w)
    rw [show D₀.diag w = D₀.ad (Multiplicative.toAdd w) from rfl, hx_eq]
    rw [hD₀.H_eq, ← rgrpConjAut_range hn hK σ hσ Fr hFr]
    exact ⟨⟨_, hx⟩, rfl⟩
  have hdiag_le : D.diag.range ≤ D.H := by
    have hdiagrange : D.diag.range =
        D₀.diag.range.map (MulAut.congr ε).toMonoidHom := by
      rw [show D.diag = (MulAut.congr ε).toMonoidHom.comp D₀.diag from rfl,
        MonoidHom.range_comp]
    rw [hdiagrange, hDH]
    exact Subgroup.map_mono hD₀diag_le
  exact ⟨D, X, frameMap_good ε hgood, hH, hDHcard, hD3, hXle, hXcard, hXcent, hXnotinn,
    hdiag_le⟩

end CFSG.StandardType