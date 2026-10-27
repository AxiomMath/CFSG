module

public import CFSG.RankThree.PartOne.KFOUT3.KtyGen
public import CFSG.RankThree.PartOne.KFOUT3.KtyAt
public import CFSG.RankThree.PartOne.KFOUT3.KtyRestrict
public import CFSG.RankThree.PartOne.KF.WCtx
public import CFSG.RankThree.PartOne.KF.D8Module
public import CFSG.RankThree.PartOne.N1322.Statements

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.N1322
open scoped commutatorElement

section Finite

theorem exists_conj_sr_dih {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (i j : ZMod n)
    (h : i.val % 2 = j.val % 2) :
    ∃ δ : DihedralGroup n, δ * DihedralGroup.sr i * δ⁻¹ = DihedralGroup.sr j := by
  rcases hn with rfl | rfl | rfl
  · revert i j; decide
  · revert i j; decide
  · revert i j; decide

theorem exists_conj_rep_dih {n : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (i : ZMod n) :
    ∃ δ : DihedralGroup n, (i.val % 2 = 0 → δ * DihedralGroup.sr 0 * δ⁻¹ = DihedralGroup.sr i) ∧
      (i.val % 2 = 1 → δ * DihedralGroup.sr 1 * δ⁻¹ = DihedralGroup.sr i) := by
  rcases hn with rfl | rfl | rfl
  · revert i; decide
  · revert i; decide
  · revert i; decide

end Finite

section WC

variable {G : Type} [Group G] {Γ V : Type} [Group Γ] [Group V] {act : Γ →* MulAut V}
  {L F : Subgroup G}

theorem autMoved_actF_gen (S : WCtx act L F) (γ : Γ) :
    autMoved F (S.actF γ) = (movedV (act γ)).map S.tor.toMonoidHom := by
  unfold autMoved movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨act γ d * d⁻¹, ⟨d, rfl⟩, by simp [S.actF_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.actF_apply, map_mul, map_inv]⟩

theorem actF_injective_of (S : WCtx act L F) (hinj : Function.Injective act) :
    Function.Injective S.actF := fun _ _ h => hinj ((MulAut.congr S.tor).injective h)

end WC

section Dih

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {n : ℕ} {V : Type} [Group V] {act : DihedralGroup n →* MulAut V}

omit [Finite G] in
theorem conjAut_inv_conj {E : Subgroup G} {t s : MulAut E} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G))
    (heq : conjAut E g hg * t * (conjAut E g hg)⁻¹ = s) :
    conjAut E g⁻¹ (Subgroup.inv_mem _ hg) * s * (conjAut E g⁻¹ (Subgroup.inv_mem _ hg))⁻¹ = t := by
  have h1 : conjAut E g⁻¹ (Subgroup.inv_mem _ hg) = (conjAut E g hg)⁻¹ := by
    unfold conjAut
    have : (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : Subgroup.normalizer (E : Set G)) = (⟨g, hg⟩)⁻¹ := rfl
    rw [this, map_inv]
  rw [h1, ← heq]
  group

omit [Finite G] in
theorem reflection_data_dih (hinj : Function.Injective act)
    (hrefl : ∀ γ : DihedralGroup n, γ * γ = 1 → γ ≠ 1 → Nat.card (movedV (act γ)) = p →
      ∃ i : ZMod n, γ = DihedralGroup.sr i)
    (R : Sec12Three.Restr c L E (E ⊓ L)) (S : WCtx act L (E ⊓ L)) {t : MulAut E}
    (htL : t ∈ torusImage E L) (ht : IsAutReflection p E t) :
    ∃ (i : ZMod n) (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G))
      (hxF : x ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)),
      E.normalizerMonoidHom ⟨x, hxE⟩ = t ∧
        (E ⊓ L).normalizerMonoidHom ⟨x, hxF⟩ = S.actF (DihedralGroup.sr i) := by
  obtain ⟨x, hxL, hxE, rfl⟩ := Sec12Three.mem_torusImage_iff.mp htL
  have hxF : x ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
    R.inf_normalizer_le ⟨hxL, hxE⟩
  have htF : (E ⊓ L).normalizerMonoidHom ⟨x, hxF⟩ ∈ torusImage (E ⊓ L) L :=
    Sec12Three.mem_torusImage_iff.mpr ⟨x, hxL, hxF, rfl⟩
  rw [S.torusImage_eq_range] at htF
  obtain ⟨γ, hγ⟩ := htF
  have hrefl' := (isAutReflection_restrict (p := p) R hxL hxE hxF).mp ht
  rw [← hγ] at hrefl'
  obtain ⟨hord, hcard⟩ := hrefl'
  have hinj' := actF_injective_of S hinj
  have hγ2 : γ * γ = 1 := by
    apply hinj'
    rw [map_mul, map_one, ← pow_two]
    have := pow_orderOf_eq_one (S.actF γ)
    rwa [hord] at this
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hord
    omega
  have hmov : Nat.card (movedV (act γ)) = p := by
    rw [autMoved_actF_gen S γ, Subgroup.card_map_of_injective S.tor.injective] at hcard
    exact hcard
  obtain ⟨i, rfl⟩ := hrefl γ hγ2 hγ1 hmov
  exact ⟨i, x, hxL, hxE, hxF, rfl, hγ.symm⟩

omit [Finite G] in
theorem parity_ne_of_diffClass_dih (hn : n = 4 ∨ n = 6 ∨ n = 8)
    (R : Sec12Three.Restr c L E (E ⊓ L)) (S : WCtx act L (E ⊓ L))
    {t s : MulAut E} (hts : DiffClass E L t s) {i j : ZMod n} {x y : G} (hxL : x ∈ L)
    (hyL : y ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (hxF : x ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G))
    (hyF : y ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G))
    (htx : E.normalizerMonoidHom ⟨x, hxE⟩ = t) (hsy : E.normalizerMonoidHom ⟨y, hyE⟩ = s)
    (hxi : (E ⊓ L).normalizerMonoidHom ⟨x, hxF⟩ = S.actF (DihedralGroup.sr i))
    (hyj : (E ⊓ L).normalizerMonoidHom ⟨y, hyF⟩ = S.actF (DihedralGroup.sr j)) :
    ¬ (i.val % 2 = j.val % 2) := by
  intro hpar
  obtain ⟨δ, hδ⟩ := exists_conj_sr_dih hn i j hpar
  obtain ⟨g, hgF, hgL, hgδ⟩ := S.exists_elt δ
  have hgE : g ∈ Subgroup.normalizer (E : Set G) := R.inf_normalizer_ge ⟨hgL, hgF⟩
  have hl : E.normalizerMonoidHom ⟨g, hgE⟩ ∈ torusImage E L :=
    Sec12Three.mem_torusImage_iff.mpr ⟨g, hgL, hgE, rfl⟩
  refine hts.2.2 _ hl ?_
  have hu : g * x * g⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgE hxE) (Subgroup.inv_mem _ hgE)
  have huF : g * x * g⁻¹ ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgF hxF) (Subgroup.inv_mem _ hgF)
  have huL : g * x * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hgL hxL) (L.inv_mem hgL)
  have hE : E.normalizerMonoidHom ⟨g, hgE⟩ * t * (E.normalizerMonoidHom ⟨g, hgE⟩)⁻¹ =
      E.normalizerMonoidHom ⟨g * x * g⁻¹, hu⟩ := by
    rw [← htx]
    have : (⟨g * x * g⁻¹, hu⟩ : Subgroup.normalizer (E : Set G)) =
        ⟨g, hgE⟩ * ⟨x, hxE⟩ * ⟨g, hgE⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  rw [hE, ← hsy]
  refine eq_of_F_actions R huL hyL hu hyE huF hyF ?_
  have : (⟨g * x * g⁻¹, huF⟩ : Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) =
      ⟨g, hgF⟩ * ⟨x, hxF⟩ * ⟨g, hgF⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hxi, hyj, hgδ, ← hδ, map_mul, map_mul, map_inv]
  rfl

omit [Finite G] in
theorem mem_autFixedInG_iff {E : Subgroup G} {t : MulAut E} {z : G} :
    z ∈ autFixedInG E t ↔ ∃ hz : z ∈ E, ((t ⟨z, hz⟩ : E) : G) = z := by
  unfold autFixedInG autFixed
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e.2, ?_⟩
    have hfix : t e = e := he
    exact congrArg Subtype.val hfix
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subtype.ext h, rfl⟩

theorem reflection_full_data_dih (h : Sec12Hyp G p A c L E)
    (hG : Sec12TwoGeneric p c L E) (hEA : E = A) (hF13 : Sec13Facts G p A c L E)
    (hinj : Function.Injective act)
    (hrefl : ∀ γ : DihedralGroup n, γ * γ = 1 → γ ≠ 1 → Nat.card (movedV (act γ)) = p →
      ∃ i : ZMod n, γ = DihedralGroup.sr i)
    (S : WCtx act L (E ⊓ L)) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    (htL : t ∈ torusImage E L) :
    ∃ (i : ZMod n) (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G))
      (hxF : x ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) (z : ↥L) (v : V),
      E.normalizerMonoidHom ⟨x, hxE⟩ = t ∧
      (E ⊓ L).normalizerMonoidHom ⟨x, hxF⟩ = S.actF (DihedralGroup.sr i) ∧
      autFixedInG E t = Subgroup.zpowers (z : G) ⊔ Subgroup.zpowers c ∧ (z : G) ^ p = 1 ∧
      z = Subgroup.inclusion inf_le_right (S.tor v) ∧ act (DihedralGroup.sr i) v = v ∧
      v ≠ 1 := by
  have hp := h.prime
  have R := h.restr_of_generic hG
  obtain ⟨i, x, hxL, hxE, hxF, hxt, hxi⟩ := reflection_data_dih hinj hrefl R S htL ht.1
  obtain ⟨z, hzL, hzE, hz1, hzp, hzH⟩ := exists_fixed_gen h hG hEA hF13 ht htL
  have hzF : z ∈ E ⊓ L := Subgroup.mem_inf.mpr ⟨hzE, hzL⟩
  obtain ⟨v, hv⟩ := S.tor.surjective ⟨z, hzF⟩
  have hzfix : x * z * x⁻¹ = z := by
    have hz : z ∈ autFixedInG E t := by
      rw [hzH]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    obtain ⟨hzE', hzt⟩ := mem_autFixedInG_iff.mp hz
    rw [← hxt] at hzt
    exact hzt
  have hact : S.actF (DihedralGroup.sr i) (S.tor v) = S.tor v := by
    rw [← hxi, hv]
    exact Subtype.ext hzfix
  have hvfix : act (DihedralGroup.sr i) v = v := by
    rw [S.actF_apply] at hact
    exact S.tor.injective hact
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [map_one] at hv
    exact hz1 (congrArg Subtype.val hv.symm)
  refine ⟨i, x, hxL, hxE, hxF, ⟨z, hzL⟩, v, hxt, hxi, hzH, hzp, ?_, hvfix, hv1⟩
  apply Subtype.ext
  rw [hv]
  rfl

end Dih

section Core

variable {Q : Type} [Group Q] {V : Type} [Group V] {n : ℕ} {act : DihedralGroup n →* MulAut V}
  {Temb : V →* Q}

theorem temb_conj_rep (hn : n = 4 ∨ n = 6 ∨ n = 8)
    (Hconj : ∀ γ : DihedralGroup n, ∃ m : Q, ∀ v, m * Temb v * m⁻¹ = Temb (act γ v))
    (i : ZMod n) {v : V} (hv1 : v ≠ 1) (hv : act (DihedralGroup.sr i) v = v) :
    (i.val % 2 = 0 → ∃ (m : Q) (v₀ : V), v₀ ≠ 1 ∧ act (DihedralGroup.sr 0) v₀ = v₀ ∧
      Temb v = m * Temb v₀ * m⁻¹) ∧
    (i.val % 2 = 1 → ∃ (m : Q) (v₀ : V), v₀ ≠ 1 ∧ act (DihedralGroup.sr 1) v₀ = v₀ ∧
      Temb v = m * Temb v₀ * m⁻¹) := by
  obtain ⟨δ, h0, h1⟩ := exists_conj_rep_dih hn i
  obtain ⟨m, hm⟩ := Hconj δ
  have key : ∀ e : ZMod n, δ * DihedralGroup.sr e * δ⁻¹ = DihedralGroup.sr i →
      ∃ (m : Q) (v₀ : V), v₀ ≠ 1 ∧ act (DihedralGroup.sr e) v₀ = v₀ ∧
        Temb v = m * Temb v₀ * m⁻¹ := by
    intro e he
    have hδ1 : ∀ w : V, act δ (act δ⁻¹ w) = w := fun w => by
      have h' : act δ * act δ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      exact congrArg (fun γ : MulAut V => γ w) h'
    refine ⟨m, act δ⁻¹ v, ?_, ?_, ?_⟩
    · intro h'
      apply hv1
      have := congrArg (act δ) h'
      rw [hδ1, map_one] at this
      exact this
    · have h2 : act (DihedralGroup.sr e) = act δ⁻¹ * act (DihedralGroup.sr i) * act δ := by
        rw [← map_mul, ← map_mul, ← he]
        congr 1
        group
      rw [h2]
      show act δ⁻¹ (act (DihedralGroup.sr i) (act δ (act δ⁻¹ v))) = act δ⁻¹ v
      rw [hδ1, hv]
    · rw [hm, hδ1]
  exact ⟨fun h => key 0 (h0 h), fun h => key 1 (h1 h)⟩

end Core

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {n : ℕ} {V : Type} [Group V] {act : DihedralGroup n →* MulAut V}

theorem kty_small_big_dih (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    {Q : Type} [Group Q] {ε : ↥L →* Q} (hε : IsCentralPQuot p ε) {R : ℕ → Prop}
    {t s : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L)
    (hsL : s ∈ torusImage E L) {g : G} (hg : g ∈ Subgroup.normalizer (E : Set G))
    (heq : conjAut E g hg * t * (conjAut E g hg)⁻¹ = s) {zt zs : ↥L}
    (hzt : autFixedInG E t = Subgroup.zpowers (zt : G) ⊔ Subgroup.zpowers c)
    (hzs : autFixedInG E s = Subgroup.zpowers (zs : G) ⊔ Subgroup.zpowers c) (hzsp : zs ^ p = 1)
    (hSm : SmallAt (ε zt) R) (hBig : BigAt p (ε zs) R) : False := by
  obtain ⟨S', hperf, hsimple, hSp, hSc, hSnorm, hR⟩ := hBig
  exact kty_false h hF13 hε ht htL hsL hg heq hzt hzs hzsp hperf hsimple hSp hSc hSnorm
    (fun T hT hTc hdvd => hSm T hT hTc _ hR hdvd)

theorem kty_of_dih (hn : n = 4 ∨ n = 6 ∨ n = 8) (h : Sec12Hyp G p A c L E)
    (hG : Sec12TwoGeneric p c L E) (hEA : E = A) (hF13 : Sec13Facts G p A c L E)
    (hinj : Function.Injective act)
    (hrefl : ∀ γ : DihedralGroup n, γ * γ = 1 → γ ≠ 1 → Nat.card (movedV (act γ)) = p →
      ∃ i : ZMod n, γ = DihedralGroup.sr i)
    {Q : Type} [Group Q] {ε : ↥L →* Q} (hε : IsCentralPQuot p ε) (Temb : V →* Q)
    (S : WCtx act L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = Temb d)
    (Hconj : ∀ γ : DihedralGroup n, ∃ m : Q, ∀ v, m * Temb v * m⁻¹ = Temb (act γ v))
    {R : ℕ → Prop}
    (Hsmall : ∀ v : V, v ≠ 1 → act (DihedralGroup.sr 0) v = v → SmallAt (Temb v) R)
    (Hbig : ∀ v : V, v ≠ 1 → act (DihedralGroup.sr 1) v = v → BigAt p (Temb v) R) :
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, DiffClass E L t s →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (E : Set G)),
        conjAut E g hg * t * (conjAut E g hg)⁻¹ ≠ s := by
  intro t ht s hs hts g hg heq
  have hp := h.prime
  have R' := h.restr_of_generic hG
  obtain ⟨i, xt, hxtL, hxtE, hxtF, zt, vt, hxt, hxti, hzt, hztp, hztv, hvti, hvt1⟩ :=
    reflection_full_data_dih h hG hEA hF13 hinj hrefl S ht hts.1
  obtain ⟨j, xs, hxsL, hxsE, hxsF, zs, vs, hxs, hxsj, hzs, hzsp, hzsv, hvsj, hvs1⟩ :=
    reflection_full_data_dih h hG hEA hF13 hinj hrefl S hs hts.2.1
  have hpar := parity_ne_of_diffClass_dih hn R' S hts hxtL hxsL hxtE hxsE hxtF hxsF hxt hxs hxti
    hxsj
  have hεt : ε zt = Temb vt := by rw [hztv]; exact hrel vt
  have hεs : ε zs = Temb vs := by rw [hzsv]; exact hrel vs
  have hzt' : zt ^ p = 1 := Subtype.ext (by simpa using hztp)
  have hzs' : zs ^ p = 1 := Subtype.ext (by simpa using hzsp)
  have hcases : ∀ k : ZMod n, k.val % 2 = 0 ∨ k.val % 2 = 1 := fun k => by omega
  have hBigAt : ∀ (k : ZMod n) (v : V), v ≠ 1 → act (DihedralGroup.sr k) v = v →
      k.val % 2 = 1 → BigAt p (Temb v) R := by
    intro k v hv1 hv hk
    obtain ⟨m, w, hw1, hw, hm⟩ := (temb_conj_rep hn Hconj k hv1 hv).2 hk
    rw [hm]
    exact (Hbig w hw1 hw).conj m
  have hSmallAt : ∀ (k : ZMod n) (v : V), v ≠ 1 → act (DihedralGroup.sr k) v = v →
      k.val % 2 = 0 → SmallAt (Temb v) R := by
    intro k v hv1 hv hk
    obtain ⟨m, w, hw1, hw, hm⟩ := (temb_conj_rep hn Hconj k hv1 hv).1 hk
    rw [hm]
    exact (Hsmall w hw1 hw).conj m
  rcases hcases i with hi | hi <;> rcases hcases j with hj | hj
  · exact hpar (by rw [hi, hj])
  ·
    refine kty_small_big_dih (R := R) h hF13 hε ht hts.1 hts.2.1 hg heq hzt hzs hzs' ?_ ?_
    · rw [hεt]
      exact hSmallAt i vt hvt1 hvti hi
    · rw [hεs]
      exact hBigAt j vs hvs1 hvsj hj
  ·
    refine kty_small_big_dih (R := R) h hF13 hε hs hts.2.1 hts.1 (Subgroup.inv_mem _ hg)
      (conjAut_inv_conj hg heq) hzs hzt hzt' ?_ ?_
    · rw [hεs]
      exact hSmallAt j vs hvs1 hvsj hj
    · rw [hεt]
      exact hBigAt i vt hvt1 hvti hi
  · exact hpar (by rw [hi, hj])

end Main

end CFSG.RankThree.PartOne.KFOUT3
