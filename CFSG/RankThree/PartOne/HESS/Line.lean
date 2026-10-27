module

public import CFSG.RankThree.PartOne.HESS.Root
public import CFSG.RankThree.PartOne.HESS.SL2Swap
public import CFSG.RankThree.PartOne.N143.JKt
public import CFSG.RankThree.PartOne.N143.JKt1
public import CFSG.RankThree.PartOne.N143.JDiag
public import CFSG.RankThree.PartOne.N143.QEqual

public section

namespace CFSG.RankThree.PartOne.HESS

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor rt permSL IsZeta diagSL tSep)
open scoped commutatorElement

section PiAut

variable {G : Type} [Group G]

@[expose] noncomputable def piAut (A : Subgroup G) (x : G) : MulAut A := by
  classical
  exact if h : x ∈ torusNormalizer A then conjAut A x h else 1

theorem piAut_of_mem {A : Subgroup G} {x : G} (hx : x ∈ torusNormalizer A) :
    piAut A x = conjAut A x hx := by
  classical
  unfold piAut
  simp only [hx, ↓reduceDIte]

theorem piAut_apply {A : Subgroup G} {x : G} (hx : x ∈ torusNormalizer A) (a : A) :
    ((piAut A x a : A) : G) = x * a * x⁻¹ := by
  rw [piAut_of_mem hx]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨x, hx⟩ a

theorem piAut_mul {A : Subgroup G} {x y : G} (hx : x ∈ torusNormalizer A)
    (hy : y ∈ torusNormalizer A) : piAut A (x * y) = piAut A x * piAut A y := by
  rw [piAut_of_mem hx, piAut_of_mem hy, piAut_of_mem ((torusNormalizer A).mul_mem hx hy)]
  exact map_mul A.normalizerMonoidHom (⟨x, hx⟩ : Subgroup.normalizer (A : Set G)) ⟨y, hy⟩

theorem piAut_one (A : Subgroup G) : piAut A (1 : G) = 1 := by
  rw [piAut_of_mem ((torusNormalizer A).one_mem)]
  exact map_one A.normalizerMonoidHom

theorem piAut_inv {A : Subgroup G} {x : G} (hx : x ∈ torusNormalizer A) :
    piAut A x⁻¹ = (piAut A x)⁻¹ := by
  rw [piAut_of_mem hx, piAut_of_mem ((torusNormalizer A).inv_mem hx)]
  exact map_inv A.normalizerMonoidHom (⟨x, hx⟩ : Subgroup.normalizer (A : Set G))

theorem piAut_eq_of_conj_eq {A : Subgroup G} {x y : G} (hx : x ∈ torusNormalizer A)
    (hy : y ∈ torusNormalizer A) (h : ∀ a ∈ A, x * a * x⁻¹ = y * a * y⁻¹) :
    piAut A x = piAut A y := by
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [piAut_apply hx, piAut_apply hy]
  exact h a a.2

theorem piAut_eq_one_iff {A : Subgroup G} {x : G} (hx : x ∈ torusNormalizer A) :
    piAut A x = 1 ↔ ∀ a ∈ A, x * a * x⁻¹ = a := by
  constructor
  · intro h a ha
    have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h
    simpa [piAut_apply hx] using this
  · intro h
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [piAut_apply hx]
    exact h a a.2

end PiAut


theorem swap_eq_swap_cases : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → Equiv.swap i j = Equiv.swap k l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

theorem exists_swap_of_sq_one : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
    ∃ i j, i ≠ j ∧ σ = Equiv.swap i j := by decide

theorem involution_conj : ∀ s t : Equiv.Perm (Fin 3), s * s = 1 → s ≠ 1 → t * t = 1 → t ≠ 1 →
    ∃ g, g * s * g⁻¹ = t := by decide

theorem exists_perm_zero_one : ∀ i j : Fin 3, i ≠ j → ∃ τ : Equiv.Perm (Fin 3), τ 0 = i ∧ τ 1 = j := by
  decide

section Acts

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  {ρ : SL3 K →* G}

open CFSG.RankThree.PartOne.KFOUT3 (mem_Tor_iff)

theorem conj_eq_of_actsBy (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {m m' : SL3 K}
    {σ : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ) (hm' : ActsBy p m' σ) :
    ∀ a ∈ A, ρ m * a * (ρ m)⁻¹ = ρ m' * a * (ρ m')⁻¹ := by
  intro a ha
  obtain ⟨i, d, hd, rfl⟩ := hρ.exists_decomp h ha
  rw [hρ.conj_decomp h m i d, hρ.conj_decomp h m' i d]
  obtain ⟨v, hv1, hv, rfl⟩ := mem_Tor_iff.1 hd
  rw [hm v hv hv1, hm' v hv hv1]

omit [Finite G] in
theorem actsBy_unique (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ)
    {m m' : SL3 K} {σ σ' : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ) (hm' : ActsBy p m' σ')
    (h : ∀ a ∈ A, ρ m * a * (ρ m)⁻¹ = ρ m' * a * (ρ m')⁻¹) : σ = σ' := by
  have hv0 : ∏ k, tSep ζ 0 1 k = 1 := KFU.prod_torusElt 0 1 ζ
  have hw : diagSL (tSep ζ 0 1) hv0 ∈ Tor p K := KFOUT3.tSep_mem hζ (by decide)
  have hv1 : ∀ i, tSep ζ 0 1 i ^ p = 1 := fun k =>
    (KFU.torusElt_mem (by decide : (0 : Fin 3) ≠ 1) hζ.pow :
      KFU.torusElt 0 1 ζ ∈ KFU.torusVec p 3 K).1 k
  have h1 := h (ρ (diagSL (tSep ζ 0 1) hv0)) (hρ.map_mem_A hw)
  have e : ∀ n : SL3 K, ρ n * ρ (diagSL (tSep ζ 0 1) hv0) * (ρ n)⁻¹ =
      ρ (n * diagSL (tSep ζ 0 1) hv0 * n⁻¹) := fun n => by simp [map_mul, map_inv]
  rw [e, e] at h1
  have hpow : ∀ n : SL3 K, (n * diagSL (tSep ζ 0 1) hv0 * n⁻¹) ^ p = 1 := fun n => by
    rw [conj_pow, Tor_pow_eq_one hw, mul_one, mul_inv_cancel]
  have h2 := hρ.eq_of_map_eq hp (hpow m) (hpow m') h1
  rw [hm _ hv0 hv1, hm' _ hv0 hv1] at h2
  have h3 : ∀ a, permVec σ (tSep ζ 0 1) a = permVec σ' (tSep ζ 0 1) a := by
    intro a
    have := congrArg (fun y : SL3 K => KFOUT3.ent y a a) h2
    apply Units.ext
    simpa [KFOUT3.diagSL_apply] using this
  have h4 : ∀ a, σ⁻¹ a = σ'⁻¹ a := fun a => tSep_injective hζ (h3 a)
  have h5 : σ⁻¹ = σ'⁻¹ := Equiv.ext h4
  exact inv_injective h5

theorem actsBy_one : ActsBy p (1 : SL3 K) 1 := fun v hv _ => by
  rw [one_mul, inv_one, mul_one]
  exact diagSL_congr (permVec_one v).symm _ _

end Acts


section Nodes

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {ρ : SL3 K →* G}

structure LineHyp (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G) (f : ℕ) {K : Type} [Field K]
    (ρ : SL3 K →* G) : Prop where
  good : JGood p A c J
  cover : IsPSL3Cover p A J ρ
  card : Nat.card K = 2 ^ f
  dvd : p ∣ 2 ^ f - 1

variable {f : ℕ}

omit [Finite K] [CharP K 2] in
theorem LineHyp.prime (hL : LineHyp p A c J f ρ) : p.Prime := hL.good.hyp.prime

omit [CharP K 2] in
theorem LineHyp.exists_zeta (hL : LineHyp p A c J f ρ) : ∃ ζ : Kˣ, IsZeta p ζ :=
  exists_isZeta hL.prime (Sec12Three.five_le hL.good.hyp) (by rw [hL.card]; exact hL.dvd)

omit [CharP K 2] in
theorem LineHyp.one_le (hL : LineHyp p A c J f ρ) : 1 ≤ f := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hL.card] at h1
  exact Nat.one_le_iff_ne_zero.2 (Nat.one_lt_two_pow_iff.1 h1)

omit [CharP K 2] in
theorem LineHyp.four_le (hL : LineHyp p A c J f ρ) : 4 ≤ Nat.card K := by
  have h3 := three_le_of_dvd_pred (Sec12Three.five_le hL.good.hyp) hL.one_le hL.dvd
  rw [hL.card]
  calc 4 ≤ 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3

@[expose] noncomputable def nodeOf (A : Subgroup G) (ρ : SL3 K →* G) (i j : Fin 3) : MulAut A :=
  piAut A (ρ (permSL (Equiv.swap i j)))

theorem LineHyp.permSL_mem_normalizer (hL : LineHyp p A c J f ρ) (σ : Equiv.Perm (Fin 3)) :
    ρ (permSL σ) ∈ torusNormalizer A :=
  (Subgroup.mem_inf.1 ((hL.cover.mem_inf_normalizer_iff hL.prime hL.good).2
    ⟨permSL σ, permSL_mem_normalizer_Tor σ, rfl⟩)).2

omit [Finite K] in
theorem LineHyp.permSL_mem_J (hL : LineHyp p A c J f ρ) (σ : Equiv.Perm (Fin 3)) :
    ρ (permSL σ) ∈ J := by
  rw [← hL.cover.range_eq]
  exact ⟨_, rfl⟩

theorem LineHyp.nodeOf_mem_torusImage (hL : LineHyp p A c J f ρ) (i j : Fin 3) :
    nodeOf A ρ i j ∈ torusImage A J :=
  Sec12Three.mem_torusImage_iff.2 ⟨ρ (permSL (Equiv.swap i j)), hL.permSL_mem_J _,
    hL.permSL_mem_normalizer _, (piAut_of_mem (hL.permSL_mem_normalizer _)).symm⟩

omit [Finite K] in
theorem permSL_swap_mul_self (i j : Fin 3) :
    (permSL (Equiv.swap i j) : SL3 K) * permSL (Equiv.swap i j) = 1 := by
  have h := mul_inv_cancel (permSL (Equiv.swap i j) : SL3 K)
  rwa [KFOUT3.permSL_inv, Equiv.swap_inv] at h

theorem LineHyp.nodeOf_sq (hL : LineHyp p A c J f ρ) (i j : Fin 3) :
    nodeOf A ρ i j * nodeOf A ρ i j = 1 := by
  unfold nodeOf
  rw [← piAut_mul (hL.permSL_mem_normalizer _) (hL.permSL_mem_normalizer _), ← map_mul,
    permSL_swap_mul_self, map_one, piAut_one]

theorem LineHyp.nodeOf_ne_one (hL : LineHyp p A c J f ρ) {i j : Fin 3} (hij : i ≠ j) :
    nodeOf A ρ i j ≠ 1 := by
  intro h
  obtain ⟨ζ, hζ⟩ := hL.exists_zeta
  have h1 := (piAut_eq_one_iff (hL.permSL_mem_normalizer (Equiv.swap i j))).1 h
  have h2 : Equiv.swap i j = 1 := actsBy_unique hL.prime hL.cover hζ (ActsBy.permSL _)
    actsBy_one (fun a ha => by rw [h1 a ha, map_one, one_mul, inv_one, mul_one])
  have h3 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) h2
  simp [Equiv.swap_apply_left] at h3
  exact hij h3.symm



theorem LineHyp.nodeOf_mem_reflectionSet (hL : LineHyp p A c J f ρ) {i j : Fin 3} (hij : i ≠ j) :
    nodeOf A ρ i j ∈ reflectionSet p A := by
  have hp := hL.prime
  obtain ⟨t₀, ht₀, ht₀J⟩ := hL.good.exists_reflection
  obtain ⟨e⟩ := hL.good.weyl
  have huJ := hL.nodeOf_mem_torusImage i j
  have hu2 := hL.nodeOf_sq i j
  have hu1 := hL.nodeOf_ne_one hij
  have ht₀o : orderOf t₀ = 2 := ht₀.1.1
  have ht₀2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [ht₀o, sq] at this
  have ht₀1 : t₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht₀o
    omega
  let a : ↥(torusImage A J) := ⟨t₀, ht₀J⟩
  let b : ↥(torusImage A J) := ⟨nodeOf A ρ i j, huJ⟩
  have ha2 : a * a = 1 := Subtype.ext ht₀2
  have ha1 : a ≠ 1 := fun h => ht₀1 (congrArg Subtype.val h)
  have hb2 : b * b = 1 := Subtype.ext hu2
  have hb1 : b ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hea2 : e a * e a = 1 := by rw [← map_mul, ha2, map_one]
  have hea1 : e a ≠ 1 := fun h => ha1 (e.injective (h.trans (map_one e).symm))
  have heb2 : e b * e b = 1 := by rw [← map_mul, hb2, map_one]
  have heb1 : e b ≠ 1 := fun h => hb1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := involution_conj (e a) (e b) hea2 hea1 heb2 heb1
  have hg' : e.symm g * a * (e.symm g)⁻¹ = b := by
    apply e.injective
    simp [hg]
  obtain ⟨w, hwJ, hw, hwg⟩ := Sec12Three.mem_torusImage_iff.1 (e.symm g).2
  have hmem := conj_mem_reflectionSet hp ht₀ hw
  have h1 : conjAut A w hw = ((e.symm g : ↥(torusImage A J)) : MulAut A) := hwg
  rw [h1] at hmem
  have h2 := congrArg Subtype.val hg'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rwa [show ((e.symm g : ↥(torusImage A J)) : MulAut A) * t₀ * ((e.symm g : ↥(torusImage A J)) :
    MulAut A)⁻¹ = nodeOf A ρ i j from h2] at hmem

theorem LineHyp.nodeOf_inj (hL : LineHyp p A c J f ρ) {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (h : nodeOf A ρ i j = nodeOf A ρ k l) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  obtain ⟨ζ, hζ⟩ := hL.exists_zeta
  have hs : Equiv.swap i j = Equiv.swap k l :=
    actsBy_unique hL.prime hL.cover hζ (ActsBy.permSL _) (ActsBy.permSL _) (fun a ha => by
      have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h
      simpa [nodeOf, piAut_apply (hL.permSL_mem_normalizer _)] using this)
  exact swap_eq_swap_cases i j k l hij hkl hs

theorem LineHyp.exists_nodeOf_eq (hL : LineHyp p A c J f ρ) {t : MulAut A} (ht : t ∈ torusImage A J)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ i j, i ≠ j ∧ nodeOf A ρ i j = t := by
  obtain ⟨ζ, hζ⟩ := hL.exists_zeta
  obtain ⟨x, hxJ, hxN, rfl⟩ := Sec12Three.mem_torusImage_iff.1 ht
  obtain ⟨m, hmN, hxm⟩ := (hL.cover.mem_inf_normalizer_iff hL.prime hL.good).1 ⟨hxJ, hxN⟩
  obtain ⟨σ, hσ⟩ := exists_actsBy hζ hmN
  have htx : A.normalizerMonoidHom ⟨x, hxN⟩ = piAut A x := (piAut_of_mem hxN).symm
  rw [htx] at ht2 ht1 ⊢
  have hσ2 : σ * σ = 1 := by
    have h1 : piAut A (x * x) = 1 := by rw [piAut_mul hxN hxN]; exact ht2
    have h2 := (piAut_eq_one_iff ((torusNormalizer A).mul_mem hxN hxN)).1 h1
    exact actsBy_unique hL.prime hL.cover hζ (hσ.mul hσ) actsBy_one (fun a ha => by
      rw [map_mul, hxm, h2 a ha, map_one, one_mul, inv_one, mul_one])
  have hσ1 : σ ≠ 1 := by
    intro h
    subst h
    apply ht1
    refine (piAut_eq_one_iff hxN).2 fun a ha => ?_
    have := conj_eq_of_actsBy hL.good hL.cover hσ (actsBy_one (p := p) (K := K)) a ha
    rw [hxm, map_one, one_mul, inv_one, mul_one] at this
    exact this
  obtain ⟨i, j, hij, rfl⟩ := exists_swap_of_sq_one σ hσ2 hσ1
  refine ⟨i, j, hij, ?_⟩
  show piAut A (ρ (permSL (Equiv.swap i j))) = piAut A x
  exact piAut_eq_of_conj_eq (hL.permSL_mem_normalizer _) hxN (fun a ha => by
    rw [← hxm]
    exact conj_eq_of_actsBy hL.good hL.cover (ActsBy.permSL _) hσ a ha)

theorem LineHyp.piAut_rot_nodeOf (hL : LineHyp p A c J f ρ) (i j : Fin 3) :
    piAut A (ρ (permSL (finRotate 3))) * nodeOf A ρ i j * (piAut A (ρ (permSL (finRotate 3))))⁻¹ =
      nodeOf A ρ (finRotate 3 i) (finRotate 3 j) := by
  have hr := hL.permSL_mem_normalizer (finRotate 3)
  have hs := hL.permSL_mem_normalizer (Equiv.swap i j)
  rw [← piAut_inv hr, nodeOf, ← piAut_mul hr hs,
    ← piAut_mul ((torusNormalizer A).mul_mem hr hs) ((torusNormalizer A).inv_mem hr), nodeOf]
  apply piAut_eq_of_conj_eq (((torusNormalizer A).mul_mem ((torusNormalizer A).mul_mem hr hs)
    ((torusNormalizer A).inv_mem hr))) (hL.permSL_mem_normalizer _)
  intro a ha
  have hact : ActsBy p (permSL (finRotate 3) * permSL (Equiv.swap i j) * (permSL (finRotate 3))⁻¹ :
      SL3 K) (finRotate 3 * Equiv.swap i j * (finRotate 3)⁻¹) := by
    refine ((ActsBy.permSL _).mul (ActsBy.permSL _)).mul ?_
    rw [KFOUT3.permSL_inv]
    exact ActsBy.permSL _
  have hact2 : ActsBy p (permSL (Equiv.swap (finRotate 3 i) (finRotate 3 j)) : SL3 K)
      (finRotate 3 * Equiv.swap i j * (finRotate 3)⁻¹) := by
    rw [← Equiv.swap_apply_apply]
    exact ActsBy.permSL _
  have := conj_eq_of_actsBy hL.good hL.cover hact hact2 a ha
  simpa [map_mul, map_inv] using this

theorem LineHyp.piAut_perm_nodeOf (hL : LineHyp p A c J f ρ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    piAut A (ρ (permSL σ)) * nodeOf A ρ i j * (piAut A (ρ (permSL σ)))⁻¹ =
      nodeOf A ρ (σ i) (σ j) := by
  have hr := hL.permSL_mem_normalizer σ
  have hs := hL.permSL_mem_normalizer (Equiv.swap i j)
  rw [← piAut_inv hr, nodeOf, ← piAut_mul hr hs,
    ← piAut_mul ((torusNormalizer A).mul_mem hr hs) ((torusNormalizer A).inv_mem hr), nodeOf]
  apply piAut_eq_of_conj_eq (((torusNormalizer A).mul_mem ((torusNormalizer A).mul_mem hr hs)
    ((torusNormalizer A).inv_mem hr))) (hL.permSL_mem_normalizer _)
  intro a ha
  have hact : ActsBy p (permSL σ * permSL (Equiv.swap i j) * (permSL σ)⁻¹ : SL3 K)
      (σ * Equiv.swap i j * σ⁻¹) := by
    refine ((ActsBy.permSL _).mul (ActsBy.permSL _)).mul ?_
    rw [KFOUT3.permSL_inv]
    exact ActsBy.permSL _
  have hact2 : ActsBy p (permSL (Equiv.swap (σ i) (σ j)) : SL3 K) (σ * Equiv.swap i j * σ⁻¹) := by
    rw [← Equiv.swap_apply_apply]
    exact ActsBy.permSL _
  have := conj_eq_of_actsBy hL.good hL.cover hact hact2 a ha
  simpa [map_mul, map_inv] using this

omit [Finite G] [Finite K] in
theorem nodeOf_comm (i j : Fin 3) : nodeOf A ρ i j = nodeOf A ρ j i := by
  unfold nodeOf
  rw [Equiv.swap_comm]

end Nodes


section Roots

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {ρ : SL3 K →* G} {f : ℕ}

@[expose] def rootG (ρ : SL3 K →* G) {i j : Fin 3} (h : i ≠ j) : Subgroup G :=
  (rootGrp (K := K) h).map ρ

@[expose] def RootSetJ (A J : Subgroup G) (f : ℕ) (t : MulAut A) : Set (Subgroup G) :=
  {S | S ≤ Kof A J t ∧ (∀ s ∈ S, s * s = 1) ∧ Nat.card S = 2 ^ f ∧
    ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S}

omit [Finite G] [Finite K] [CharP K 2] in
theorem blkSL_xp (c : K) :
    (blkSL (xp c) : SL3 K) = rt (show (0 : Fin 3) ≠ 1 by decide) c := by
  apply KFOUT3.ent_ext
  intro a b
  rw [KFOUT3.ent_rt]
  simp only [KFOUT3.ent, coe_blkSL]
  fin_cases a <;> fin_cases b <;> simp [blkMat, xp]

omit [Finite G] [Finite K] [CharP K 2] in
theorem blkSL_xm (c : K) :
    (blkSL (xm c) : SL3 K) = rt (show (1 : Fin 3) ≠ 0 by decide) c := by
  apply KFOUT3.ent_ext
  intro a b
  rw [KFOUT3.ent_rt]
  simp only [KFOUT3.ent, coe_blkSL]
  fin_cases a <;> fin_cases b <;> simp [blkMat, xm]

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_blkSL_Uplus : (Uplus K).map (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K) =
    rootGrp (K := K) (show (0 : Fin 3) ≠ 1 by decide) := by
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [eq_xp_of_mem_Uplus hM, blkSL_xp]
    exact rt_mem_rootGrp _ _
  · intro hx
    obtain ⟨s, rfl⟩ := (mem_rootGrp_iff _).1 hx
    exact ⟨xp s, xp_mem s, blkSL_xp s⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem map_blkSL_Uminus : (Uminus K).map (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K) =
    rootGrp (K := K) (show (1 : Fin 3) ≠ 0 by decide) := by
  ext x
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [eq_xm_of_mem_Uminus hM, blkSL_xm]
    exact rt_mem_rootGrp _ _
  · intro hx
    obtain ⟨s, rfl⟩ := (mem_rootGrp_iff _).1 hx
    exact ⟨xm s, xm_mem s, blkSL_xm s⟩

omit [Finite G] [Finite K] in
theorem rootG_eq_map_Uplus {τ : Equiv.Perm (Fin 3)} {i j : Fin 3} (hτ0 : τ 0 = i) (hτ1 : τ 1 = j)
    (hij : i ≠ j) :
    rootG ρ hij = (Uplus K).map (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)) := by
  subst hτ0 hτ1
  unfold rootG
  have e1 := map_blkSL_Uplus (K := K)
  calc (rootGrp (K := K) hij).map ρ
      = (((Uplus K).map blkSL).map (MulAut.conj (permSL τ)).toMonoidHom).map ρ := by
        rw [e1, map_conj_permSL_rootGrp]
    _ = (Uplus K).map (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)) := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl

omit [Finite G] [Finite K] in
theorem rootG_symm_eq_map_Uminus {τ : Equiv.Perm (Fin 3)} {i j : Fin 3} (hτ0 : τ 0 = i)
    (hτ1 : τ 1 = j) (hij : i ≠ j) :
    rootG ρ hij.symm = (Uminus K).map (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)) := by
  subst hτ0 hτ1
  unfold rootG
  have e1 := map_blkSL_Uminus (K := K)
  calc (rootGrp (K := K) hij.symm).map ρ
      = (((Uminus K).map blkSL).map (MulAut.conj (permSL τ)).toMonoidHom).map ρ := by
        rw [e1, map_conj_permSL_rootGrp]
    _ = (Uminus K).map (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)) := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl

omit [Finite K] [CharP K 2] in
theorem LineHyp.rootG_invariant (hL : LineHyp p A c J f ρ) {i j : Fin 3} (h : i ≠ j) :
    ∀ a ∈ A, ∀ s ∈ rootG ρ h, a * s * a⁻¹ ∈ rootG ρ h := by
  intro a ha s hs
  obtain ⟨k, d, hd, rfl⟩ := hL.cover.exists_decomp hL.good ha
  obtain ⟨y, hy, rfl⟩ := hs
  obtain ⟨v, hv1, hv, rfl⟩ := KFOUT3.mem_Tor_iff.1 hd
  obtain ⟨u, rfl⟩ := (mem_rootGrp_iff h).1 hy
  have hconj : diagSL v hv * rt h u * (diagSL v hv)⁻¹ = rt h ((v i : K) * ((v j)⁻¹ : Kˣ) * u) := by
    apply KFOUT3.ent_ext
    intro a b
    rw [KFOUT3.diagSL_conj_ent, KFOUT3.ent_rt, KFOUT3.ent_rt]
    by_cases hab : a = b
    · subst hab
      have : ¬ (i = a ∧ j = a) := fun hh => h (hh.1.trans hh.2.symm)
      simp [this]
    · by_cases hh : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hh
        simp [hab]
      · simp [hab, hh]
  have hc : ∀ x ∈ J, c ^ k * x = x * c ^ k := fun x hx =>
    (Commute.zpow_left (show Commute c x from Sec12Three.comm_c_L hL.good.hyp x hx) k).eq
  have hρJ : ∀ z : SL3 K, ρ z ∈ J := fun z => hL.cover.range_eq ▸ ⟨z, rfl⟩
  refine ⟨rt h ((v i : K) * ((v j)⁻¹ : Kˣ) * u), rt_mem_rootGrp h _, ?_⟩
  rw [← hconj, map_mul, map_mul, map_inv]
  symm
  have h1 := hc (ρ (diagSL v hv) * ρ (rt h u) * (ρ (diagSL v hv))⁻¹)
    (J.mul_mem (J.mul_mem (hρJ _) (hρJ _)) (J.inv_mem (hρJ _)))
  calc (c ^ k * ρ (diagSL v hv)) * ρ (rt h u) * (c ^ k * ρ (diagSL v hv))⁻¹
      = c ^ k * (ρ (diagSL v hv) * ρ (rt h u) * (ρ (diagSL v hv))⁻¹) * (c ^ k)⁻¹ := by group
    _ = (ρ (diagSL v hv) * ρ (rt h u) * (ρ (diagSL v hv))⁻¹) * c ^ k * (c ^ k)⁻¹ := by rw [h1]
    _ = _ := by rw [mul_inv_cancel_right]



omit [Finite G] [Finite K] in
theorem actsBy_conj_swap {τ : Equiv.Perm (Fin 3)} {i j : Fin 3} (hτ0 : τ 0 = i) (hτ1 : τ 1 = j) :
    ActsBy p ((permSL τ)⁻¹ * permSL (Equiv.swap i j) * permSL τ : SL3 K) (Equiv.swap 0 1) := by
  have h1 : ActsBy p ((permSL τ)⁻¹ * permSL (Equiv.swap i j) * permSL τ : SL3 K)
      (τ⁻¹ * Equiv.swap i j * τ) := by
    rw [KFOUT3.permSL_inv]
    exact ((ActsBy.permSL _).mul (ActsBy.permSL _)).mul (ActsBy.permSL _)
  have h2 : τ⁻¹ * Equiv.swap i j * τ = Equiv.swap 0 1 := by
    have h3 := Equiv.swap_apply_apply τ⁻¹ i j
    rw [inv_inv] at h3
    have e0 : τ⁻¹ i = 0 := by rw [← hτ0]; simp
    have e1 : τ⁻¹ j = 1 := by rw [← hτ1]; simp
    rw [← h3, e0, e1]
  rwa [h2] at h1

omit [Finite G] [Finite K] in
theorem comp_conj_permSL_apply (τ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)
      ((permSL τ)⁻¹ * permSL (Equiv.swap i j) * permSL τ) = ρ (permSL (Equiv.swap i j)) := by
  show ρ (permSL τ * ((permSL τ)⁻¹ * permSL (Equiv.swap i j) * permSL τ) * (permSL τ)⁻¹) = _
  congr 1
  group

theorem LineHyp.kof_nodeOf (hL : LineHyp p A c J f ρ) {τ : Equiv.Perm (Fin 3)} {i j : Fin 3}
    (hτ0 : τ 0 = i) (hτ1 : τ 1 = j) :
    Kof A J (nodeOf A ρ i j) = (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)).range := by
  obtain ⟨ζ, hζ⟩ := hL.exists_zeta
  have hxN := hL.permSL_mem_normalizer (Equiv.swap i j)
  have hρ' := hL.cover.conjPerm τ
  have hact := actsBy_conj_swap (p := p) (K := K) hτ0 hτ1
  have := Kof_eq_swap hL.good hL.prime hρ' hζ hL.four_le hxN
    (comp_conj_permSL_apply (ρ := ρ) τ i j) (fun v hv hv1 => hact v hv hv1)
  rw [nodeOf, piAut_of_mem hxN]
  exact this

theorem LineHyp.rootSetJ_eq (hL : LineHyp p A c J f ρ) {i j : Fin 3} (hij : i ≠ j) :
    RootSetJ A J f (nodeOf A ρ i j) = {rootG ρ hij, rootG ρ hij.symm} := by
  obtain ⟨ζ, hζ⟩ := hL.exists_zeta
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_zero_one i j hij
  have hρ'c := hL.cover.conjPerm τ
  have hker := hL.kof_nodeOf hτ0 hτ1
  have hinj : Function.Injective (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)) :=
    blkφ_injective hρ'c
  have hP := rootG_eq_map_Uplus (ρ := ρ) hτ0 hτ1 hij
  have hM := rootG_symm_eq_map_Uminus (ρ := ρ) hτ0 hτ1 hij
  set B := blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom) with hB
  have hcardK : Nat.card K = 2 ^ f := hL.card
  ext S
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hSK, hsq, hcard, hinv⟩
    rw [hker] at hSK
    let W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := S.comap B
    have hsqW : ∀ M ∈ W, M * M = 1 := by
      intro M hM
      apply hinj
      rw [map_mul, map_one]
      exact hsq _ hM
    have hnormW : ∀ M ∈ W, hmat ζ * M * (hmat ζ)⁻¹ ∈ W := by
      intro M hM
      have ha : B (hmat ζ) ∈ A := by
        rw [hB, blkφ_apply, blkSL_hmat ζ (KFU.prod_torusElt 0 1 ζ)]
        exact hρ'c.map_mem_A (KFOUT3.tSep_mem hζ (by decide))
      have := hinv _ ha _ hM
      show B (hmat ζ * M * (hmat ζ)⁻¹) ∈ S
      rwa [map_mul, map_mul, map_inv]
    have hcardW : ∀ U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), Nat.card U = 2 ^ f →
        W ≤ U → S = U.map B := by
      intro U hU hWU
      have hle : S ≤ U.map B := by
        intro s hs
        obtain ⟨M, rfl⟩ := hSK hs
        exact ⟨M, hWU hs, rfl⟩
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective hinj, hU, hcard]
    rcases sl2_two_group_cases hζ.sq hsqW hnormW with hW | hW
    · left
      rw [hP]
      exact hcardW _ (by rw [card_Uplus, hcardK]) hW
    · right
      rw [hM]
      exact hcardW _ (by rw [card_Uminus, hcardK]) hW
  · rintro (rfl | rfl)
    · rw [hP]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hker]
        rintro _ ⟨M, -, rfl⟩
        exact ⟨M, rfl⟩
      · rintro _ ⟨M, hM, rfl⟩
        rw [← map_mul, Uplus_sq hM, map_one]
      · rw [Subgroup.card_map_of_injective hinj, card_Uplus, hcardK]
      · rw [← hP]
        exact hL.rootG_invariant hij
    · rw [hM]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hker]
        rintro _ ⟨M, -, rfl⟩
        exact ⟨M, rfl⟩
      · rintro _ ⟨M, hM, rfl⟩
        rw [← map_mul, Uminus_sq hM, map_one]
      · rw [Subgroup.card_map_of_injective hinj, card_Uminus, hcardK]
      · rw [← hM]
        exact hL.rootG_invariant hij.symm

theorem LineHyp.rootG_ne (hL : LineHyp p A c J f ρ) {i j : Fin 3} (hij : i ≠ j) :
    rootG ρ hij ≠ rootG ρ hij.symm := by
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_zero_one i j hij
  have hinj := blkφ_injective (hL.cover.conjPerm τ)
  rw [rootG_eq_map_Uplus (ρ := ρ) hτ0 hτ1 hij, rootG_symm_eq_map_Uminus (ρ := ρ) hτ0 hτ1 hij]
  intro h
  exact Uplus_not_le_Uminus (Subgroup.map_injective hinj h).le

omit [Finite G] [Finite K] in
theorem conjBy_rootG (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (h : i ≠ j) :
    conjBy (ρ (permSL σ)) (rootG ρ h) = rootG ρ (σ.injective.ne h) := by
  unfold conjBy rootG
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj (ρ (permSL σ))).toMonoidHom.comp ρ =
      ρ.comp (MulAut.conj (permSL σ)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map, map_conj_permSL_rootGrp]

end Roots

end CFSG.RankThree.PartOne.HESS
