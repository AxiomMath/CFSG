module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthWin

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.Open CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.RankThree.Classical2 (orthDerived)
open Multiplicative

section Aux

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)


theorem qtwoOrthStd_autCongr_eq_linConj {K : Type} [Field K] {V V' : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (e : V ≃ₗ[K] V') :
    LinearEquiv.autCongr e = CFSG.RankThree.PartOne.linConj e := by
  apply MulEquiv.ext
  intro g
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.autCongr_apply_apply, CFSG.RankThree.PartOne.linConj_apply]

theorem qtwoOrthStd_map_centralizer {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (T : Subgroup A) :
    (Subgroup.centralizer (T : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ((T.map e.toMonoidHom : Subgroup B) : Set B) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hy' : ∀ h ∈ (T : Set A), h * y = y * h := hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, hy' w hw]
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have hx' : ∀ h ∈ ((T.map e.toMonoidHom : Subgroup B) : Set B), h * x = x * h := hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hx' (e y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact h

theorem qtwoOrthStd_mem_reflFixedCoord_iff {p r : ℕ} {i j : Fin r}
    (f : Fin r → Multiplicative (ZMod p)) :
    f ∈ reflFixedCoord p r i j ↔ f i = f j := by
  rw [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply, div_eq_one]

theorem qtwoOrthStd_mem_reflFixedCoordPos_iff {p r : ℕ} {i j : Fin r}
    (f : Fin r → Multiplicative (ZMod p)) :
    f ∈ reflFixedCoordPos p r i j ↔ f i * f j = 1 := by
  rw [reflFixedCoordPos, MonoidHom.mem_ker, MonoidHom.mul_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply]

theorem qtwoOrthStd_eqLocus_permAut_swap {p r : ℕ} {i j : Fin r} (hij : i < j) :
    MonoidHom.eqLocus (SpCoord.permAut (Equiv.swap i j)).toMonoidHom (MonoidHom.id _) =
      reflFixedCoord p r i j := by
  ext f
  change (SpCoord.permAut (Equiv.swap i j)) f = f ↔ f ∈ reflFixedCoord p r i j
  rw [qtwoOrthStd_mem_reflFixedCoord_iff]
  constructor
  · intro h
    have h1 := congrFun h i
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext k
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
    by_cases hk : k = i
    · rw [hk, Equiv.swap_apply_left]; exact h.symm
    · by_cases hk' : k = j
      · rw [hk', Equiv.swap_apply_right]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hk hk']

theorem qtwoOrthStd_zmodPowHom_range_eq_top {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type} [Field K] {σ : K ≃+* K} {ζ : normOne σ}
    (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (hcard : Nat.card (normOne σ) = p) :
    (TableBSymp.zmodPowHom hζp).range = ⊤ := by
  have htop : Subgroup.zpowers ζ = ⊤ := zpowers_eq_top_of_prime_card hcard hζ1
  rw [eq_top_iff, ← htop]
  apply Subgroup.zpowers_le.mpr
  refine ⟨Multiplicative.ofAdd (1 : ZMod p), ?_⟩
  simpa using TableBSymp.zmodPowHom_natCast hζp 1

theorem qtwoOrthStd_zmodPowHom_injective {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type} [Field K] {σ : K ≃+* K} {ζ : normOne σ}
    (hζp : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (TableBSymp.zmodPowHom hζp) := by
  intro a b h
  have h1 : a * b⁻¹ = 1 :=
    (TableBSymp.zmodPowHom_eq_one_iff hζp hζo).mp
      (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.mp h1

theorem qtwoOrthStd_zmodPowHom_surjective {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type} [Field K] {σ : K ≃+* K} {ζ : normOne σ}
    (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (hcard : Nat.card (normOne σ) = p) :
    Function.Surjective (TableBSymp.zmodPowHom hζp) := by
  intro u
  have htop := qtwoOrthStd_zmodPowHom_range_eq_top hζ1 hζp hcard
  have : u ∈ (TableBSymp.zmodPowHom hζp).range := by
    rw [htop]
    exact Subgroup.mem_top u
  exact this

theorem qtwoOrthStd_orderOf_eq_of_prime {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] {σ : K ≃+* K} {ζ : normOne σ}
    (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) : orderOf ζ = p := by
  have hdvd : orderOf ζ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hζp
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf ζ) hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hζ1
  · exact h

theorem qtwoOrthStd_map_reflFixedCoord_pow {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type} [Field K] {σ : K ≃+* K} {ζ : normOne σ}
    (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (hcard : Nat.card (normOne σ) = p)
    {n : ℕ} (i j : Fin n) (hij : j.val = i.val + 1) :
    (reflFixedCoord p n i j).map ((TableBSymp.zmodPowHom hζp).compLeft (Fin n)) =
      qtwoWinTorus σ n i.val 2 := by
  have hζo := qtwoOrthStd_orderOf_eq_of_prime hζ1 hζp
  have hinj := qtwoOrthStd_zmodPowHom_injective hζp hζo
  have hsurj := qtwoOrthStd_zmodPowHom_surjective hζ1 hζp hcard
  have hmem : ∀ a : Fin n, i.val ≤ a.val → a.val < i.val + 2 → a = i ∨ a = j := by
    intro a ha1 ha2
    rcases Nat.eq_or_lt_of_le ha1 with h | h
    · left; exact Fin.ext (by omega)
    · right; exact Fin.ext (by omega)
  apply le_antisymm
  · rintro t ⟨f, hf, rfl⟩
    have hfij : f i = f j := (qtwoOrthStd_mem_reflFixedCoord_iff f).mp hf
    intro a b ha1 ha2 hb1 hb2
    rcases hmem a ha1 ha2 with ha | ha <;> rcases hmem b hb1 hb2 with hb | hb
    · rw [ha, hb]
    · rw [ha, hb]
      exact congrArg (TableBSymp.zmodPowHom hζp) hfij
    · rw [ha, hb]
      exact (congrArg (TableBSymp.zmodPowHom hζp) hfij).symm
    · rw [ha, hb]
  · intro t ht
    choose f hf using fun a => hsurj (t a)
    have hft : (TableBSymp.zmodPowHom hζp).compLeft (Fin n) f = t := by
      funext a
      exact hf a
    refine Subgroup.mem_map.mpr ⟨f, ?_, hft⟩
    rw [qtwoOrthStd_mem_reflFixedCoord_iff]
    apply hinj
    have hw := ht i j (le_refl _) (by omega) (by omega) (by omega)
    rw [hf i, hf j, hw]

theorem qtwoOrthStd_map_inf_reflFixedCoord_pow {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type} [Field K] {σ : K ≃+* K} {ζ : normOne σ}
    (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (hcard : Nat.card (normOne σ) = p)
    {n : ℕ} (i j l : Fin n) (hij : j.val = i.val + 1) (hjl : l.val = j.val + 1) :
    ((reflFixedCoord p n i j ⊓ reflFixedCoord p n j l).map
        ((TableBSymp.zmodPowHom hζp).compLeft (Fin n))) =
      qtwoWinTorus σ n i.val 3 := by
  have hζo := qtwoOrthStd_orderOf_eq_of_prime hζ1 hζp
  have hinj := qtwoOrthStd_zmodPowHom_injective hζp hζo
  have hsurj := qtwoOrthStd_zmodPowHom_surjective hζ1 hζp hcard
  have hmem : ∀ a : Fin n, i.val ≤ a.val → a.val < i.val + 3 → a = i ∨ a = j ∨ a = l := by
    intro a ha1 ha2
    rcases Nat.eq_or_lt_of_le ha1 with h | h
    · exact Or.inl (Fin.ext (by omega))
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h2 | h2
      · exact Or.inr (Or.inl (Fin.ext (by omega)))
      · exact Or.inr (Or.inr (Fin.ext (by omega)))
  apply le_antisymm
  · rintro t ⟨f, hf, rfl⟩
    have hf' : f ∈ reflFixedCoord p n i j ∧ f ∈ reflFixedCoord p n j l := hf
    have hfij : f i = f j := (qtwoOrthStd_mem_reflFixedCoord_iff f).mp hf'.1
    have hfjl : f j = f l := (qtwoOrthStd_mem_reflFixedCoord_iff f).mp hf'.2
    intro a b ha1 ha2 hb1 hb2
    rcases hmem a ha1 ha2 with ha | ha | ha <;>
      rcases hmem b hb1 hb2 with hb | hb | hb
    · rw [ha, hb]
    · rw [ha, hb]; exact congrArg (TableBSymp.zmodPowHom hζp) hfij
    · rw [ha, hb]; exact congrArg (TableBSymp.zmodPowHom hζp) (hfij.trans hfjl)
    · rw [ha, hb]; exact (congrArg (TableBSymp.zmodPowHom hζp) hfij).symm
    · rw [ha, hb]
    · rw [ha, hb]; exact congrArg (TableBSymp.zmodPowHom hζp) hfjl
    · rw [ha, hb]; exact (congrArg (TableBSymp.zmodPowHom hζp) (hfij.trans hfjl)).symm
    · rw [ha, hb]; exact (congrArg (TableBSymp.zmodPowHom hζp) hfjl).symm
    · rw [ha, hb]
  · intro t ht
    choose f hf using fun a => hsurj (t a)
    have hft : (TableBSymp.zmodPowHom hζp).compLeft (Fin n) f = t := by
      funext a
      exact hf a
    refine Subgroup.mem_map.mpr ⟨f, ?_, hft⟩
    change f ∈ reflFixedCoord p n i j ∧ f ∈ reflFixedCoord p n j l
    rw [qtwoOrthStd_mem_reflFixedCoord_iff, qtwoOrthStd_mem_reflFixedCoord_iff]
    have h1 := ht i j (le_refl _) (by omega) (by omega) (by omega)
    have h2 := ht j l (by omega) (by omega) (by omega) (by omega)
    exact ⟨hinj (by rw [hf i, hf j, h1]), hinj (by rw [hf j, hf l, h2])⟩

theorem qtwoOrthStd_sgnAut_comm {p k : ℕ} (a b : Fin k) :
    (SpCoord.sgnAut (p := p) a * SpCoord.sgnAut (p := p) b :
        MulAut (Fin k → Multiplicative (ZMod p))) =
      SpCoord.sgnAut (p := p) b * SpCoord.sgnAut (p := p) a := by
  by_cases hab : a = b
  · subst hab; rfl
  · refine MulEquiv.ext fun f => ?_
    simp only [MulAut.mul_apply, SpCoord.sgnAut_apply]
    rw [Function.update_of_ne (Ne.symm hab), Function.update_of_ne hab, Function.update_comm hab]

theorem qtwoOrthStd_sgnAut_conj_swap {p k : ℕ} {a b : Fin k} (hab : a ≠ b) :
    (SpCoord.sgnAut (p := p) b * SpCoord.permAut (p := p) (Equiv.swap a b) *
        (SpCoord.sgnAut (p := p) b)⁻¹ : MulAut (Fin k → Multiplicative (ZMod p))) =
      SpCoord.sgnAut (p := p) a * SpCoord.sgnAut (p := p) b *
        SpCoord.permAut (p := p) (Equiv.swap a b) := by
  have h := CFSG.StandardType.OrthExcEven.sgnTransp_eq (p := p) (k := k) (a := b) (b := a)
    (Ne.symm hab)
  rw [Equiv.swap_comm b a] at h
  rw [← h]
  rw [qtwoOrthStd_sgnAut_comm b a]

theorem qtwoOrthStd_sgnAut_comm_swap {p k : ℕ} {a b i : Fin k} (hia : i ≠ a) (hib : i ≠ b) :
    (SpCoord.sgnAut (p := p) i * SpCoord.permAut (p := p) (Equiv.swap a b) :
        MulAut (Fin k → Multiplicative (ZMod p))) =
      SpCoord.permAut (p := p) (Equiv.swap a b) * SpCoord.sgnAut (p := p) i := by
  have hfix : Equiv.swap a b i = i := Equiv.swap_apply_of_ne_of_ne hia hib
  have hiff : ∀ j, (Equiv.swap a b j = i) ↔ (j = i) := by
    intro j
    constructor
    · intro h
      have hh := congrArg (Equiv.swap a b) h
      rwa [Equiv.swap_apply_self, hfix] at hh
    · rintro rfl
      exact hfix
  refine MulEquiv.ext fun f => funext fun j => ?_
  simp only [MulAut.mul_apply, SpCoord.sgnAut_apply, SpCoord.permAut_apply,
    Function.comp_apply, Equiv.swap_inv, Function.update_apply, hiff, hfix]

theorem qtwoOrthStd_funCongrLeft_diagHom {F K : Type} [Field F] [Field K] [Algebra F K]
    {σ : K ≃+* K} {r n : ℕ} (e : Fin n ≃ Fin r) (t : Fin r → normOne σ) (x : Fin r → K) :
    LinearEquiv.funCongrLeft F K e (diagHom F σ r t x) =
      diagHom F σ n (t ∘ e) (LinearEquiv.funCongrLeft F K e x) := by
  funext i
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, diagHom_apply,
    Function.comp_apply]

theorem qtwoOrthStd_sigma_eq_inv {K : Type} [Field K] {σ : K ≃+* K} (u : normOne σ) :
    σ (((u : Kˣ) : K)) = (((u⁻¹ : normOne σ) : Kˣ) : K) := by
  have hu : σ (((u : Kˣ) : K)) * (((u : Kˣ) : K)) = 1 := (mem_normOne σ).1 u.2
  rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_left hu

theorem qtwoOrthStd_tauAt_conj_diagHom {F K : Type} [Field F] [Field K] [Algebra F K]
    {σ : K ≃+* K} (E : QuadExt F K σ) {n : ℕ} (i : Fin n) (t : Fin n → normOne σ) :
    tauAt E i * diagHom F σ n t * (tauAt E i)⁻¹ =
      diagHom F σ n (Function.update t i (t i)⁻¹) := by
  have hinv : (tauAt E i)⁻¹ = tauAt E i :=
    inv_eq_of_mul_eq_one_right (tauAt_mul_self E i)
  rw [hinv]
  apply LinearEquiv.ext
  intro x
  funext j
  by_cases hj : j = i
  · rw [hj]
    simp only [LinearEquiv.mul_apply, diagHom_apply, tauAt_apply, Function.update_self,
      if_true, if_pos rfl, map_mul, E.isUnitary.invol, qtwoOrthStd_sigma_eq_inv]
  · simp only [LinearEquiv.mul_apply, diagHom_apply, tauAt_apply, Function.update_of_ne hj,
      if_false, if_neg hj]

end Aux

end CFSG.StandardType.QTwo

end
