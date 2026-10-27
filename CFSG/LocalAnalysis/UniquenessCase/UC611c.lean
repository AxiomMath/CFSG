module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Wreath
public import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22q
public import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc611_fus_mem_normalizer_of_conj_le {V : Subgroup G} {b : G}
    (h : ∀ v ∈ V, b⁻¹ * v * b ∈ V) : b ∈ normalizer (V : Set G) := by
  have hle : V.map (MulAut.conj b⁻¹).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using h v hv
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj b⁻¹).injective).ge
  have hn : b⁻¹ ∈ normalizer (V : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  simpa using (normalizer (V : Set G)).inv_mem hn

theorem uc611_fusion_of_weaklyClosed {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsSylowOf p P ⊤)
    {A : Subgroup G} (hAP : A ≤ P) (hAc : IsMulCommutative A)
    (hwc : ∀ g : G, (∀ x ∈ A, g⁻¹ * x * g ∈ P) → ∀ x ∈ A, g⁻¹ * x * g ∈ A)
    {X : Subgroup G} (hXA : X ≤ A) {g : G} (hg : ∀ x ∈ X, g⁻¹ * x * g ∈ A) :
    ∃ n ∈ normalizer (A : Set G), ∀ x ∈ X, g⁻¹ * x * g = n⁻¹ * x * n := by
  have hpA : IsPGroup p A := hP.isPGroup.to_le hAP
  let H : Subgroup G := Subgroup.centralizer ((fun x => g⁻¹ * x * g) '' (X : Set G))
  have hAH : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact setLike_mul_comm (hg x hx) ha
  have hA'H : A.comap (MulAut.conj g).toMonoidHom ≤ H := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hy' : g * y * g⁻¹ ∈ A := hy
    have h := setLike_mul_comm hy' (hXA hx)
    calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [h]
      _ = y * (g⁻¹ * x * g) := by group
  obtain ⟨S, hS, hAS⟩ := UC6.exists_isSylowOf_ge (K := H) hAH hpA
  obtain ⟨k, hkH, hk⟩ := UC6.exists_conj_le_of_isSylowOf hS hA'H
    (hpA.comap_of_injective _ (MulAut.conj g).injective)
  obtain ⟨h, -, hh⟩ := UC6.exists_conj_le_of_isSylowOf hP (le_top : S ≤ ⊤) hS.isPGroup
  have h1 : h ∈ normalizer (A : Set G) :=
    uc611_fus_mem_normalizer_of_conj_le fun a ha => hwc h (fun x hx => hh x (hAS hx)) a ha
  have h2 : g * k * h ∈ normalizer (A : Set G) := by
    refine uc611_fus_mem_normalizer_of_conj_le fun a ha => ?_
    refine hwc (g * k * h) (fun x hx => ?_) a ha
    have hx' : k⁻¹ * (g⁻¹ * x * g) * k ∈ S := by
      refine hk (g⁻¹ * x * g) ?_
      show g * (g⁻¹ * x * g) * g⁻¹ ∈ A
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]
      exact hx
    have e : (g * k * h)⁻¹ * x * (g * k * h) = h⁻¹ * (k⁻¹ * (g⁻¹ * x * g) * k) * h := by group
    rw [e]
    exact hh _ hx'
  refine ⟨g * k, ?_, fun x hx => ?_⟩
  · have e : g * k = (g * k * h) * h⁻¹ := by group
    rw [e]
    exact (normalizer (A : Set G)).mul_mem h2 ((normalizer (A : Set G)).inv_mem h1)
  · have hc : g⁻¹ * x * g * k = k * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_iff.1 hkH _ ⟨x, hx, rfl⟩
    calc g⁻¹ * x * g = k⁻¹ * (k * (g⁻¹ * x * g)) := by group
      _ = k⁻¹ * (g⁻¹ * x * g * k) := by rw [hc]
      _ = (g * k)⁻¹ * x * (g * k) := by group

section L47

variable {S : Type*} [CommGroup S]

theorem uc611_l47_eq_one_of_zpow_odd (hS : IsPGroup 2 S) {u : S} {n : ℤ} (hn : Odd n)
    (h : u ^ n = 1) : u = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) u
  have hdvd : (orderOf u : ℤ) ∣ n := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [hk] at hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hk
  · exfalso
    have h2 : (2 : ℤ) ∣ n := by
      refine dvd_trans ?_ hdvd
      exact_mod_cast dvd_pow_self 2 hk0.ne'
    exact (Int.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h2)

theorem uc611_l47_apply_comm {σ τ : MulAut S} (h : Commute σ τ) (s : S) : σ (τ s) = τ (σ s) :=
  congrArg (fun f : MulAut S => f s) h.eq

theorem uc611_l47_apply_cube {σ : MulAut S} (h : σ ^ 3 = 1) (s : S) : σ (σ (σ s)) = s := by
  have h' := congrArg (fun f : MulAut S => f s) h
  simpa [pow_succ] using h'

theorem uc611_l47_exists_commutator_subgroup (w : MulAut S) :
    ∃ U : Subgroup S, ∀ u, u ∈ U ↔ ∃ s, w s * s⁻¹ = u := by
  refine ⟨(MonoidHom.mk' (fun s => w s * s⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    ac_rfl)).range, fun u => ?_⟩
  simp [MonoidHom.mem_range]

theorem uc611_l47_commutator_invariant {w σ : MulAut S} (hσ : Commute σ w) {U : Subgroup S}
    (hU : ∀ u, u ∈ U ↔ ∃ s, w s * s⁻¹ = u) {u : S} (hu : u ∈ U) : σ u ∈ U := by
  obtain ⟨s, rfl⟩ := (hU u).1 hu
  refine (hU _).2 ⟨σ s, ?_⟩
  rw [map_mul, map_inv, uc611_l47_apply_comm hσ s]

theorem uc611_l47_norm_eq_one {w : MulAut S} (hw : w ^ 3 = 1) {U : Subgroup S}
    (hU : ∀ u, u ∈ U ↔ ∃ s, w s * s⁻¹ = u) {u : S} (hu : u ∈ U) :
    u * w u * w (w u) = 1 := by
  obtain ⟨s, rfl⟩ := (hU u).1 hu
  simp only [map_mul, map_inv, uc611_l47_apply_cube hw]
  have key : ∀ a b c : S, a * c⁻¹ * (b * a⁻¹) * (c * b⁻¹) = 1 := fun a b c => by
    calc a * c⁻¹ * (b * a⁻¹) * (c * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) * (c * c⁻¹) := by ac_rfl
      _ = 1 := by simp
  exact key _ _ _

theorem uc611_l47_fixed_eq_one_of_cyclic (hS : IsPGroup 2 S) {w x : MulAut S} (hw : w ^ 3 = 1)
    (hwx : Commute w x) {U : Subgroup S} (hU : ∀ u, u ∈ U ↔ ∃ s, w s * s⁻¹ = u)
    (hcyc : IsCyclic ↥((x : S →* S).eqLocus (MonoidHom.id S))) {u : S} (hu : u ∈ U)
    (hxu : x u = u) : u = 1 := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hxg : x (g : S) = g := g.2
  have hwg : x (w (g : S)) = w (g : S) := by
    rw [← uc611_l47_apply_comm hwx, hxg]
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1
    (hg (⟨w (g : S), hwg⟩ : ↥((x : S →* S).eqLocus (MonoidHom.id S))))
  have ht' : (g : S) ^ t = w (g : S) := congrArg Subtype.val ht
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1
    (hg (⟨u, hxu⟩ : ↥((x : S →* S).eqLocus (MonoidHom.id S))))
  have hm' : (g : S) ^ m = u := congrArg Subtype.val hm
  have hwu : w u = u ^ t := by
    rw [← hm', map_zpow, ← ht', ← zpow_mul, ← zpow_mul, mul_comm]
  have hwwu : w (w u) = u ^ (t * t) := by
    rw [hwu, map_zpow, hwu, ← zpow_mul]
  have hnorm := uc611_l47_norm_eq_one hw hU hu
  rw [hwwu, hwu] at hnorm
  have hpow : u ^ (1 + t + t * t) = 1 := by
    rw [zpow_add, zpow_add, zpow_one]
    exact hnorm
  refine uc611_l47_eq_one_of_zpow_odd hS ?_ hpow
  have h1 : Even (t * (t + 1)) := Int.even_mul_succ_self t
  have h2 : 1 + t + t * t = t * (t + 1) + 1 := by ring
  rw [h2]
  exact h1.add_one

theorem uc611_l47_rel {x y w : MulAut S} (hxy : x * y * x⁻¹ * y⁻¹ = w) (hwy : Commute w y)
    (s : S) : x (y s) = y (w (x s)) := by
  have h1 : x * y = y * (w * x) :=
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = w * (y * x) := by rw [hxy]
      _ = (w * y) * x := (mul_assoc _ _ _).symm
      _ = (y * w) * x := by rw [hwy.eq]
      _ = y * (w * x) := mul_assoc _ _ _
  simpa using congrArg (fun f : MulAut S => f s) h1

end L47

theorem uc611_l47 {S : Type*} [CommGroup S] [Finite S] (hS : IsPGroup 2 S)
    (x y w : MulAut S) (hx : x ^ 3 = 1) (hw : w ^ 3 = 1) (hxy : x * y * x⁻¹ * y⁻¹ = w)
    (hwx : Commute w x) (hwy : Commute w y) (hw1 : w ≠ 1) (hind : w ∉ Subgroup.zpowers x) :
    ¬ IsCyclic ↥((x : S →* S).eqLocus (MonoidHom.id S)) := by
  have _hind := hind
  intro hcyc
  obtain ⟨U, hU⟩ := uc611_l47_exists_commutator_subgroup w
  have hfix : ∀ u ∈ U, x u = u → u = 1 := fun u hu hxu =>
    uc611_l47_fixed_eq_one_of_cyclic hS hw hwx hU hcyc hu hxu
  have hxw : ∀ a, x (w a) = w (x a) := fun a => uc611_l47_apply_comm hwx.symm a
  have hwy' : ∀ a, w (y a) = y (w a) := fun a => uc611_l47_apply_comm hwy a
  have hcx := uc611_l47_apply_cube hx
  have hcw := uc611_l47_apply_cube hw
  have hrel := uc611_l47_rel hxy hwy
  have hUinv : ∀ σ : MulAut S, Commute σ w → ∀ u ∈ U, σ u ∈ U := fun σ hσ u hu =>
    uc611_l47_commutator_invariant hσ hU hu
  have hxU : ∀ u ∈ U, x u ∈ U := fun u hu => hUinv x hwx.symm u hu
  have hwU : ∀ u ∈ U, w u ∈ U := fun u hu => hUinv w (Commute.refl w) u hu
  have hyU : ∀ u ∈ U, y u ∈ U := fun u hu => hUinv y hwy.symm u hu
  have hU1 : ∀ u ∈ U, u = 1 := by
    intro u hu
    have hp : x u ∈ U := hxU u hu
    have hq : x (x u) ∈ U := hxU _ hp
    have hnp := uc611_l47_norm_eq_one hw hU hp
    have hnq := uc611_l47_norm_eq_one hw hU hq
    have hv0 : u * x u * x (x u) = 1 := by
      refine hfix _ ((U.mul_mem (U.mul_mem hu hp) hq)) ?_
      simp only [map_mul, hcx]
      ac_rfl
    have hv1 : u * w (x u) * w (w (x (x u))) = 1 := by
      have hmem : u * w (x u) * w (w (x (x u))) ∈ U :=
        U.mul_mem (U.mul_mem hu (hwU _ hp)) (hwU _ (hwU _ hq))
      have h1 : y (u * w (x u) * w (w (x (x u)))) = 1 := by
        refine hfix _ (hyU _ hmem) ?_
        rw [hrel]
        congr 1
        simp only [map_mul, hxw, hcx, hcw]
        ac_rfl
      exact (EmbeddingLike.map_eq_one_iff).1 h1
    have hv2 : u * w (w (x u)) * w (x (x u)) = 1 := by
      have hmem : u * w (w (x u)) * w (x (x u)) ∈ U :=
        U.mul_mem (U.mul_mem hu (hwU _ (hwU _ hp))) (hwU _ hq)
      have h1 : y (y (u * w (w (x u)) * w (x (x u)))) = 1 := by
        refine hfix _ (hyU _ (hyU _ hmem)) ?_
        rw [hrel, hrel, hwy']
        congr 2
        simp only [map_mul, hxw, hcx, hcw]
        ac_rfl
      exact (EmbeddingLike.map_eq_one_iff).1 ((EmbeddingLike.map_eq_one_iff).1 h1)
    have hcube : u * u * u = 1 := by
      have hprod : (u * x u * x (x u)) * (u * w (x u) * w (w (x (x u)))) *
          (u * w (w (x u)) * w (x (x u))) =
          (u * u * u) * (x u * w (x u) * w (w (x u))) *
            (x (x u) * w (x (x u)) * w (w (x (x u)))) := by ac_rfl
      rw [hv0, hv1, hv2, hnp, hnq] at hprod
      simpa using hprod.symm
    refine uc611_l47_eq_one_of_zpow_odd hS (n := 3) (by decide) ?_
    simpa [pow_succ] using hcube
  apply hw1
  ext s
  have : w s * s⁻¹ = 1 := hU1 _ ((hU _).2 ⟨s, rfl⟩)
  simpa [mul_inv_eq_one] using this

omit [Finite G] in
theorem uc611_gl_isPGroup_pCoreOf (M : Subgroup G) : IsPGroup 2 (pCoreOf 2 M) :=
  CFSG.pCore_isPGroup.map M.subtype

theorem uc611_gl_pCoreOf_le_primeCore (M : Subgroup G) : pCoreOf 2 M ≤ rankThreePrimeCore 3 M := by
  refine le_sSup ⟨CFSG.openPCoreOf_le 2 M, ?_, ?_⟩
  · rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (uc611_gl_isPGroup_pCoreOf M)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)

omit [Finite G] in
theorem uc611_gl_le_normalizer_pCoreOf (M : Subgroup G) : M ≤ normalizer (pCoreOf 2 M : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.openPCoreOf_le 2 M)).1 (by
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal)

theorem uc611_pCoreOf_le_Q (D : Data G) {Q : Subgroup G}
    (hQ : IsSylowOf 2 Q (rankThreePrimeCore 3 D.M)) : pCoreOf 2 D.M ≤ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : rankThreePrimeCore 3 D.M ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le D.M
  have h1 := hQ.inf_of_le_normalizer (uc611_gl_pCoreOf_le_primeCore D.M)
    (hKM.trans (uc611_gl_le_normalizer_pCoreOf D.M))
  have h2 := h1.eq_of_le inf_le_right le_rfl (uc611_gl_isPGroup_pCoreOf D.M)
  intro x hx
  exact (h2 ▸ hx : x ∈ Q ⊓ pCoreOf 2 D.M).1

theorem uc611_inf_centralizer_Q (D : Data G) {P Q : Subgroup G} (hP3 : IsPGroup 3 P) (hPM : P ≤ D.M)
    (hQ : IsSylowOf 2 Q (rankThreePrimeCore 3 D.M)) : P ⊓ centralizer (Q : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNQ := uc611_pCoreOf_le_Q D hQ
  have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 D.M) hP3
    (uc611_gl_isPGroup_pCoreOf D.M)
  rw [eq_bot_iff]
  intro x hx
  have hxC : x ∈ centralizer (pCoreOf 2 D.M : Set G) := Subgroup.centralizer_le hNQ hx.2
  have hxN : x ∈ pCoreOf 2 D.M := D.standing.charTwo D.M D.maxLocal.1 ⟨hPM hx.1, hxC⟩
  exact (Subgroup.mem_bot).2 (Subgroup.disjoint_def.1 hdis hx.1 hxN)

omit [Finite G] in
theorem uc611_gl_isPGroup_of_wreath {P : Subgroup G}
    (e : ↥P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) : IsPGroup 3 P := by
  refine IsPGroup.of_card (n := 4) ?_
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
  simp

theorem uc611_gl_le_of_clauseC {M P : Subgroup G} (hc : rankThreeClauseC M P) : P ≤ M := by
  obtain ⟨-, ⟨e⟩, hΓ, -⟩ := hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 := uc611_gl_isPGroup_of_wreath e
  have hcard : 1 < Nat.card P := by
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
    simp
  haveI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.1 hcard
  haveI : Nontrivial (center P) := hP3.center_nontrivial
  have hJ3 : IsPGroup 3 (thompsonSubgroup P) := hP3.to_le (CFSG.Open.thompsonSubgroup_le_self P)
  have hJ1 : thompsonSubgroup P ≠ ⊥ := by
    intro h
    obtain ⟨z, hz⟩ := exists_ne (1 : center P)
    have hz1 : ((z : P) : G) ∈ thompsonSubgroup P :=
      uc22p22q_center_le_thompson P ⟨z, z.2, rfl⟩
    rw [h, Subgroup.mem_bot] at hz1
    exact hz (Subtype.ext (Subtype.ext hz1))
  have hrank : 1 ≤ CFSG.Open.pRank 3 (thompsonSubgroup P) :=
    (CFSG.RankThree.PartTwo.Late.one_le_pRank_three_iff hJ3).2 hJ1
  have hN := CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 (thompsonSubgroup P)
    (thompsonSubgroup P) le_rfl hrank
  exact fun x hx => hΓ (hN (CFSG.Open.normalizer_le_normalizer_thompsonSubgroup P
    (Subgroup.le_normalizer hx)))

omit [Finite G] in
theorem uc611_gl_conj_mem_centralizer {X : Subgroup G} {c z : G} (hc : ∀ x ∈ X, x * c = c * x)
    (hz : z ∈ centralizer (X : Set G)) : c * z * c⁻¹ ∈ centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro x hx
  have h1 : Commute x c := hc x hx
  have h2 : Commute x z := hz x hx
  exact ((h1.mul_right h2).mul_right h1.inv_right).eq

omit [Finite G] in
theorem uc611_gl_map_conj_centralizer {X : Subgroup G} {c : G} (hc : ∀ x ∈ X, x * c = c * x) :
    (centralizer (X : Set G)).map (MulAut.conj c).toMonoidHom = centralizer (X : Set G) := by
  refine le_antisymm ?_ fun y hy => ⟨c⁻¹ * y * c, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact uc611_gl_conj_mem_centralizer hc hz
  · have := uc611_gl_conj_mem_centralizer (c := c⁻¹)
      (fun x hx => (Commute.inv_right (hc x hx : Commute x c)).eq) hy
    simpa using this
  · show c * (c⁻¹ * y * c) * c⁻¹ = y
    group

theorem uc611_clauseC_at {M P Q X : Subgroup G} (hc : rankThreeClauseC M P)
    (hQ : IsSylowOf 2 Q (rankThreePrimeCore 3 M)) (hPQ : P ≤ normalizer (Q : Set G))
    (hXP : X ≤ P) (hX3 : Nat.card X = 3) (hXA : ¬ X ≤ thompsonSubgroup P) :
    ∃ n : ℕ, 1 ≤ n ∧ rankThreeIsQ8CentralCyclic (Q ⊓ centralizer (X : Set G)) n := by
  have hPM := uc611_gl_le_of_clauseC hc
  obtain ⟨-, ⟨e⟩, -, hall⟩ := hc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP3 := uc611_gl_isPGroup_of_wreath e
  obtain ⟨Q₀, hQ₀K, hQ₀2, hQ₀idx, hPQ₀, m, hm1, hm⟩ := hall X hXP hX3 hXA
  have hcop : ¬ 3 ∣ Nat.card ↥(rankThreePrimeCore 3 M) := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
        Nat.prime_three M) hd |>.elim
  have hPN : P ≤ normalizer ((rankThreePrimeCore 3 M : Subgroup G) : Set G) :=
    hPM.trans <| (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le M)).1
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three M)
  have hS₀ : IsSylowOf 2 Q₀ (rankThreePrimeCore 3 M) :=
    (isSylowOf_iff).2 ⟨hQ₀K, hQ₀2, hQ₀idx⟩
  obtain ⟨c, hcmem, hQc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    (r := 3) (q := 2) Nat.prime_three Nat.prime_two hP3 hcop hPN
    (CFSG.LocalAnalysis.EvenBN.Tits.N.P6.fusionIsSylowIn_of_isSylowOf hS₀)
    (CFSG.LocalAnalysis.EvenBN.Tits.N.P6.fusionIsSylowIn_of_isSylowOf hQ) hPQ₀ hPQ
  have hcP : ∀ y ∈ P, y * c = c * y := Subgroup.mem_centralizer_iff.1 hcmem.2
  have hcent := uc611_gl_map_conj_centralizer (X := X) (c := c) fun x hx => hcP x (hXP hx)
  refine ⟨m, hm1, ?_⟩
  have hinf : Q ⊓ centralizer (X : Set G) =
      (Q₀ ⊓ centralizer (X : Set G)).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hcent, hQc]
  rw [hinf]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsQ8CentralCyclic_map hm (MulAut.conj c)

end CFSG.LocalAnalysis.UniquenessCase.UC6
