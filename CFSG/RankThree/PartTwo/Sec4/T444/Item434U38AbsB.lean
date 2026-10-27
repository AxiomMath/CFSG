module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

variable {H : Type*} [Group H] [Finite H] {Ω : Type*} [Finite Ω] [MulAction H Ω]

theorem factorization_seven : (99283968 : ℕ).factorization 7 = 1 := by
  have h7 : Nat.Prime 7 := by norm_num
  have h : (99283968 : ℕ) = 7 ^ 1 * 14183424 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    h7.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_nineteen : (99283968 : ℕ).factorization 19 = 1 := by
  have h19 : Nat.Prime 19 := by norm_num
  have h : (99283968 : ℕ) = 19 ^ 1 * 5225472 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    h19.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_eq_prime_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {K : Subgroup H}
    (hK : IsPGroup p K) (hK1 : K ≠ ⊥) (hfac : (Nat.card H).factorization p = 1) :
    Nat.card K = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  have hdvd : p ^ n ∣ Nat.card H := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card K
  have hH0 : Nat.card H ≠ 0 := (Nat.card_pos (α := H)).ne'
  have hle : n ≤ (Nat.card H).factorization p :=
    (hp.out.pow_dvd_iff_le_factorization hH0).mp hdvd
  rw [hfac] at hle
  have hK0 : Nat.card K ≠ 1 := fun h => hK1 (Subgroup.card_eq_one.mp h)
  interval_cases n
  · exact absurd (by simpa using hn) hK0
  · simpa using hn

theorem exists_conj_zpowers {p : ℕ} [hp : Fact p.Prime] {x : H} (hx : orderOf x = p)
    {K : Subgroup H} (hK : Nat.card K = p) (hfac : (Nat.card H).factorization p = 1) :
    ∃ g : H, K = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom := by
  let P : Sylow p H := Sylow.ofCard K (by rw [hK, hfac, pow_one])
  let P0 : Sylow p H := Sylow.ofCard (Subgroup.zpowers x)
    (by rw [Nat.card_zpowers, hx, hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P0 P
  refine ⟨g, ?_⟩
  have h1 : ((g • P0 : Sylow p H) : Subgroup H) = (P : Subgroup H) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
  exact h1.symm

theorem mem_zpowers_iff_of_map {x g : H} {V : Subgroup H}
    (hV : V = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom) (z : H) :
    z ∈ Subgroup.zpowers x ↔ g * z * g⁻¹ ∈ V := by
  rw [hV, Subgroup.mem_map]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    have h2 : g * y * g⁻¹ = g * z * g⁻¹ := hyz
    have hyz' : y = z := mul_left_cancel (mul_right_cancel h2)
    rw [← hyz']
    exact hy

theorem isPGroup_of_pow_eq_one {p : ℕ} {K : Subgroup H} (h : ∀ y ∈ K, y ^ p = 1) :
    IsPGroup p K :=
  fun y => ⟨1, Subtype.ext (by simpa using h y y.2)⟩

theorem card_fix_eq_two {x g : H} {V : Subgroup H}
    (hV : V = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom)
    (hxf : Nat.card {p : Ω // x • p = p} = 2) :
    Nat.card {p : Ω // ∀ v ∈ V, v • p = p} = 2 := by
  rw [← hxf]
  refine Nat.card_congr
    { toFun := fun p => ⟨g⁻¹ • p.1, ?_⟩
      invFun := fun q => ⟨g • q.1, ?_⟩
      left_inv := fun p => Subtype.ext (smul_inv_smul g p.1)
      right_inv := fun q => Subtype.ext (inv_smul_smul g q.1) }
  · have hxV : g * x * g⁻¹ ∈ V := (mem_zpowers_iff_of_map hV x).mp (Subgroup.mem_zpowers x)
    have h1 : x • g⁻¹ • p.1 = g⁻¹ • ((g * x * g⁻¹) • p.1) := by
      rw [smul_smul, smul_smul]
      congr 1
      group
    show x • g⁻¹ • p.1 = g⁻¹ • p.1
    rw [h1, p.2 _ hxV]
  · intro v hv
    have hz : g⁻¹ * v * g ∈ Subgroup.zpowers x := by
      rw [mem_zpowers_iff_of_map hV, show g * (g⁻¹ * v * g) * g⁻¹ = v by group]
      exact hv
    have hstab : Subgroup.zpowers x ≤ MulAction.stabilizer H q.1 :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr q.2)
    have hfix : (g⁻¹ * v * g) • q.1 = q.1 := MulAction.mem_stabilizer_iff.mp (hstab hz)
    calc v • g • q.1 = (g * (g⁻¹ * v * g)) • q.1 := by
          rw [smul_smul]
          congr 1
          group
      _ = g • (g⁻¹ * v * g) • q.1 := by rw [smul_smul]
      _ = g • q.1 := by rw [hfix]

theorem fixAct_mem {V E : Subgroup H} (hEV : E ≤ Subgroup.normalizer (V : Set H)) (e : E)
    (p : {p : Ω // ∀ v ∈ V, v • p = p}) : ∀ v ∈ V, v • (e : H) • p.1 = (e : H) • p.1 := by
  intro v hv
  have hw : (e : H)⁻¹ * v * (e : H) ∈ V := by
    have h := Subgroup.mem_normalizer_iff.mp (hEV e.2) ((e : H)⁻¹ * v * (e : H))
    rw [show (e : H) * ((e : H)⁻¹ * v * (e : H)) * (e : H)⁻¹ = v by group] at h
    exact h.mpr hv
  calc v • (e : H) • p.1 = (v * (e : H)) • p.1 := (mul_smul v (e : H) p.1).symm
    _ = ((e : H) * ((e : H)⁻¹ * v * (e : H))) • p.1 := by
          congr 1
          group
    _ = (e : H) • ((e : H)⁻¹ * v * (e : H)) • p.1 := mul_smul _ _ _
    _ = (e : H) • p.1 := by rw [p.2 _ hw]

abbrev fixAct (V E : Subgroup H) (hEV : E ≤ Subgroup.normalizer (V : Set H)) :
    MulAction E {p : Ω // ∀ v ∈ V, v • p = p} where
  smul e p := ⟨(e : H) • p.1, fixAct_mem hEV e p⟩
  one_smul p := Subtype.ext (one_smul H p.1)
  mul_smul e₁ e₂ p := Subtype.ext (mul_smul (e₁ : H) (e₂ : H) p.1)

theorem no_E27_normalizes_seven
    (hH : Nat.card H = 99283968)
    (hA : ∀ (E : Subgroup H), IsElemAbelian 3 E → Nat.card E = 27 → ∀ ω : Ω, ¬ ∀ e ∈ E, e • ω = ω)
    {x : H} (hx : orderOf x = 7) (hxf : Nat.card {p : Ω // x • p = p} = 2)
    {V E : Subgroup H} (hV : IsElemAbelian 7 V) (hV1 : V ≠ ⊥)
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEV : E ≤ Subgroup.normalizer (V : Set H)) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac7 : (Nat.card H).factorization 7 = 1 := by rw [hH]; exact factorization_seven
  have hV7 : Nat.card V = 7 :=
    card_eq_prime_of_isPGroup (isPGroup_of_pow_eq_one hV.2) hV1 hfac7
  obtain ⟨g, hg⟩ := exists_conj_zpowers hx hV7 hfac7
  have hcount := card_fix_eq_two hg hxf
  letI := fixAct (Ω := Ω) V E hEV
  have hmod := (isPGroup_of_pow_eq_one hE.2).card_modEq_card_fixedPoints
    {p : Ω // ∀ v ∈ V, v • p = p}
  rw [hcount] at hmod
  have hpos : 0 < Nat.card (MulAction.fixedPoints E {p : Ω // ∀ v ∈ V, v • p = p}) := by
    rcases Nat.eq_zero_or_pos
      (Nat.card (MulAction.fixedPoints E {p : Ω // ∀ v ∈ V, v • p = p})) with h0 | h0
    · rw [h0] at hmod
      norm_num [Nat.ModEq] at hmod
    · exact h0
  obtain ⟨⟨a, ha⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact hA E hE hE27 a.1
    (fun e he => congrArg Subtype.val (MulAction.mem_fixedPoints.mp ha ⟨e, he⟩))

theorem card_le_three_of_pow {G' : Type*} [Group G'] [Finite G'] [IsCyclic G']
    (R : Subgroup G') (hR : ∀ r ∈ R, r ^ 3 = 1) : Nat.card R ≤ 3 := by
  classical
  haveI : Fintype R := Fintype.ofFinite R
  have hall : ∀ a : R, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hR a a.2)
  have h := IsCyclic.card_pow_eq_one_le (α := R) (n := 3) (by norm_num)
  rw [Nat.card_eq_fintype_card]
  simpa [hall] using h

noncomputable def conjAutZ (Y : Subgroup H) (e : H) (he : e ∈ Subgroup.normalizer (Y : Set H)) :
    MulAut Y where
  toFun y := ⟨e * y * e⁻¹, (Subgroup.mem_normalizer_iff.mp he y).mp y.2⟩
  invFun y := ⟨e⁻¹ * y * e, by
    have h := Subgroup.mem_normalizer_iff.mp he (e⁻¹ * (y : H) * e)
    have h2 : e * (e⁻¹ * (y : H) * e) * e⁻¹ = y := by group
    rw [h2] at h
    exact h.mpr y.2⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

noncomputable def conjHomZ (Y E : Subgroup H) (h : E ≤ Subgroup.normalizer (Y : Set H)) :
    E →* MulAut Y where
  toFun e := conjAutZ Y e (h e.2)
  map_one' := by ext y; simp [conjAutZ]
  map_mul' a b := by ext y; simp [conjAutZ, mul_assoc]

theorem conj_normalizes {x g : H} {V E : Subgroup H}
    (hV : V = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom)
    (hEV : E ≤ Subgroup.normalizer (V : Set H)) :
    E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup H) : Set H) := by
  intro e' he'
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
  have hconj : ∀ z : H, (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g := fun z => by
    show g⁻¹ * z * g⁻¹⁻¹ = g⁻¹ * z * g
    rw [inv_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  show h ∈ Subgroup.zpowers x ↔ _
  rw [hconj e, mem_zpowers_iff_of_map hV h,
    mem_zpowers_iff_of_map hV (g⁻¹ * e * g * h * (g⁻¹ * e * g)⁻¹)]
  have hsimp : g * (g⁻¹ * e * g * h * (g⁻¹ * e * g)⁻¹) * g⁻¹ = e * (g * h * g⁻¹) * e⁻¹ := by
    group
  rw [hsimp]
  exact Subgroup.mem_normalizer_iff.mp (hEV he) (g * h * g⁻¹)

theorem exists_centralizing_nine {x : H} (hx : orderOf x = 19) {E' : Subgroup H}
    (hexp : ∀ e ∈ E', e ^ 3 = 1) (hcard : Nat.card E' = 27)
    (hN : E' ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup H) : Set H)) :
    ∃ K : Subgroup H, 9 ∣ Nat.card K ∧ K ≤ Subgroup.centralizer ({x} : Set H) := by
  have hYcard : Nat.card (Subgroup.zpowers x) = 19 := by rw [Nat.card_zpowers, hx]
  have hprime : Nat.Prime (Nat.card (Subgroup.zpowers x)) := by rw [hYcard]; norm_num
  haveI : NeZero (Nat.card (Subgroup.zpowers x)) := ⟨hprime.ne_zero⟩
  haveI : IsCyclic (ZMod (Nat.card (Subgroup.zpowers x)))ˣ := ZMod.isCyclic_units_prime hprime
  let φ : E' →* MulAut (Subgroup.zpowers x) := conjHomZ (Subgroup.zpowers x) E' hN
  let Θ : E' →* (ZMod (Nat.card (Subgroup.zpowers x)))ˣ :=
    (IsCyclic.mulAutMulEquiv (Subgroup.zpowers x)).toMonoidHom.comp φ
  have hR : ∀ r ∈ Θ.range, r ^ 3 = 1 := by
    intro r hr
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hr
    have he3 : e ^ 3 = 1 := Subtype.ext (by simpa using hexp (e : H) e.2)
    rw [← map_pow, he3, map_one]
  have hRcard : Nat.card Θ.range ≤ 3 := card_le_three_of_pow Θ.range hR
  have hsplit : Nat.card Θ.ker * Nat.card Θ.range = 27 :=
    (Subgroup.card_ker_mul_card_range Θ).trans hcard
  have hRpos : 0 < Nat.card Θ.range := Nat.card_pos
  have hK9 : 9 ∣ Nat.card Θ.ker := by
    rcases (show Nat.card Θ.range = 1 ∨ Nat.card Θ.range = 2 ∨ Nat.card Θ.range = 3 by omega)
      with h | h | h <;> rw [h] at hsplit <;> omega
  refine ⟨Θ.ker.map E'.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := E'.subtype) Subtype.val_injective]
    exact hK9
  · intro k hk
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hk
    have hΘ : Θ e = 1 := MonoidHom.mem_ker.mp he
    have hφ : φ e = 1 := by
      apply (IsCyclic.mulAutMulEquiv (Subgroup.zpowers x)).injective
      rw [map_one]
      exact hΘ
    have h1 : ((φ e) ⟨x, Subgroup.mem_zpowers x⟩ : H) = x := by
      rw [hφ]
      rfl
    have h2 : (e : H) * x * (e : H)⁻¹ = x := h1
    have h3 : (e : H) * x = x * (e : H) := mul_inv_eq_iff_eq_mul.mp h2
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact h3.symm

theorem no_E27_normalizes_nineteen
    (hH : Nat.card H = 99283968)
    {x : H} (hx : orderOf x = 19) (hC : Nat.card (Subgroup.centralizer ({x} : Set H)) ≤ 57)
    {V E : Subgroup H} (hV : IsElemAbelian 19 V) (hV1 : V ≠ ⊥)
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEV : E ≤ Subgroup.normalizer (V : Set H)) : False := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hfac19 : (Nat.card H).factorization 19 = 1 := by rw [hH]; exact factorization_nineteen
  have hV19 : Nat.card V = 19 :=
    card_eq_prime_of_isPGroup (isPGroup_of_pow_eq_one hV.2) hV1 hfac19
  obtain ⟨g, hg⟩ := exists_conj_zpowers hx hV19 hfac19
  have hinj : Function.Injective ⇑(MulAut.conj g⁻¹).toMonoidHom :=
    (MulAut.conj g⁻¹).injective
  have hE'card : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective hinj, hE27]
  have hexp : ∀ e ∈ E.map (MulAut.conj g⁻¹).toMonoidHom, e ^ 3 = 1 := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
    rw [← map_pow, hE.2 e0 he0, map_one]
  obtain ⟨K, hK9, hKC⟩ :=
    exists_centralizing_nine hx hexp hE'card (conj_normalizes hg hEV)
  have hxC : x ∈ Subgroup.centralizer ({x} : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
  have h19 : 19 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
    have hd := Subgroup.orderOf_dvd_natCard _ hxC
    rw [hx] at hd
    exact hd
  have h9 : 9 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) :=
    dvd_trans hK9 (Subgroup.card_dvd_of_le hKC)
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x} : Set H)) := Nat.card_pos
  omega

end CFSG.RankThree.PartTwo.Sec4.Item434U38
