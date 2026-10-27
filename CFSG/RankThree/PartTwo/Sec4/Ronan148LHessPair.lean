module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessTori
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Open (pCoreOf)

variable {X : Type} [Group X] [Finite X]

theorem map_centralizer_singleton_mulAut (α : MulAut X) (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map α.toMonoidHom =
      Subgroup.centralizer ({α x} : Set X) := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg α h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  · intro h
    have h' := congrArg α.symm h
    simpa only [map_mul, MulEquiv.symm_apply_apply] using h'

theorem map_hessU_mulAut (α : MulAut X) (x : X) :
    (pCoreOf 2 (Subgroup.centralizer ({x} : Set X))).map α.toMonoidHom =
      pCoreOf 2 (Subgroup.centralizer ({α x} : Set X)) := by
  rw [map_pCoreOf_mulAut, map_centralizer_singleton_mulAut]

theorem map_conj_zpowers (g y : X) :
    (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * y * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem map_mulAut_zpowers (α : MulAut X) (y : X) :
    (Subgroup.zpowers y).map α.toMonoidHom = Subgroup.zpowers (α y) := by
  rw [MonoidHom.map_zpowers]
  rfl

@[expose] def hessInv (x : X) : Set X :=
  {u | u ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) ∧ u ^ 2 = 1}

@[expose] def HessPair (E : Subgroup X) (x x' : X) : Prop :=
  ∃ n ∈ Subgroup.closure (hessInv x ∪ hessInv x') ⊓ Subgroup.normalizer (E : Set X),
    Subgroup.zpowers (n * x * n⁻¹) = Subgroup.zpowers x'

theorem hessInv_eq_of_zpowers_eq {x y : X} (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    hessInv x = hessInv y := by
  unfold hessInv
  rw [centralizer_singleton_eq_of_zpowers_eq h]

theorem image_hessInv (α : MulAut X) (x : X) : α.toMonoidHom '' hessInv x = hessInv (α x) := by
  ext u
  constructor
  · rintro ⟨v, ⟨hv, hv2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← map_hessU_mulAut]
      exact Subgroup.mem_map_of_mem _ hv
    · rw [← map_pow, hv2, map_one]
  · rintro ⟨hu, hu2⟩
    rw [← map_hessU_mulAut] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    apply α.injective
    change α (v ^ 2) = α 1
    rw [map_pow, map_one]
    exact hu2

namespace HessPair

variable {E : Subgroup X} {x x' y y' : X}

theorem congr_right (h : Subgroup.zpowers x' = Subgroup.zpowers y') (hp : HessPair E x x') :
    HessPair E x y' := by
  obtain ⟨n, hn, hnz⟩ := hp
  refine ⟨n, ?_, hnz.trans h⟩
  rwa [← hessInv_eq_of_zpowers_eq h]

theorem map (α : MulAut X) (hαE : E.map α.toMonoidHom = E) (hp : HessPair E x x') :
    HessPair E (α x) (α x') := by
  obtain ⟨n, hn', hnz⟩ := hp
  obtain ⟨hn, hnN⟩ := Subgroup.mem_inf.mp hn'
  refine ⟨α n, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · have h := Subgroup.mem_map_of_mem α.toMonoidHom hn
    rwa [MonoidHom.map_closure, Set.image_union, image_hessInv, image_hessInv] at h
  · have h := Subgroup.mem_map_of_mem α.toMonoidHom hnN
    rwa [Subgroup.map_equiv_normalizer_eq, hαE] at h
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_mulAut_zpowers, hnz, map_mulAut_zpowers]

theorem conj {w : X} (hw : w ∈ Subgroup.normalizer (E : Set X)) (hp : HessPair E x x') :
    HessPair E (w * x * w⁻¹) (w * x' * w⁻¹) := by
  have hE : E.map (MulAut.conj w).toMonoidHom = E := by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw)) y
    rw [inv_inv] at this
    exact this.symm
  exact hp.map (MulAut.conj w) hE

theorem exists_mem_layer (hp : HessPair E x x')
    (hU : ∀ a ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)),
      ∀ b ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)), a * b = b * a)
    (hU' : ∀ a ∈ pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)),
      ∀ b ∈ pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)), a * b = b * a) :
    ∃ n ∈ (layer (pCoreOf 2 (Subgroup.centralizer ({x} : Set X))) hU 1 ⊔
          layer (pCoreOf 2 (Subgroup.centralizer ({x'} : Set X))) hU' 1) ⊓
        Subgroup.normalizer (E : Set X),
      (Subgroup.zpowers x).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers x' := by
  obtain ⟨n, hn', hnz⟩ := hp
  obtain ⟨hn, hnN⟩ := Subgroup.mem_inf.mp hn'
  refine ⟨n, Subgroup.mem_inf.mpr ⟨?_, hnN⟩, by rw [map_conj_zpowers, hnz]⟩
  refine (Subgroup.closure_le _).mpr ?_ hn
  rintro u (⟨hu, hu2⟩ | ⟨hu, hu2⟩)
  · exact Subgroup.mem_sup_left (mem_layer.mpr ⟨hu, by rw [pow_one]; exact hu2⟩)
  · exact Subgroup.mem_sup_right (mem_layer.mpr ⟨hu, by rw [pow_one]; exact hu2⟩)

end HessPair

theorem exists_pow_mul_pow_of_mem_sup {d c x : X} (hdc : d * c = c * d) (hd3 : d ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hx : x ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c) :
    ∃ i j : ℕ, x = d ^ i * c ^ j := by
  have hcomm : ∀ i j : ℕ, c ^ j * d ^ i = d ^ i * c ^ j := fun i j =>
    ((Commute.pow_pow (hdc : Commute d c) i j).eq).symm
  let H : Subgroup X :=
    { carrier := {y | ∃ i j : ℕ, y = d ^ i * c ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        rw [pow_add, pow_add, mul_assoc, ← mul_assoc (c ^ j), hcomm k j]
        group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        have hd : (d ^ i)⁻¹ = d ^ (2 * i) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hd3,
            one_pow]
        have hc : (c ^ j)⁻¹ = c ^ (2 * j) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hc3,
            one_pow]
        rw [mul_inv_rev, hd, hc, hcomm] }
  have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers c ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩)
  exact hle hx

theorem exists_zpowers_eq_mul_pow {d c x : X} (hdc : d * c = c * d) (hd3 : d ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hx : x ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers c)
    (hxd : x ∉ Subgroup.zpowers d) :
    ∃ k : ℕ, Subgroup.zpowers x = Subgroup.zpowers (c * d ^ k) := by
  obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_sup hdc hd3 hc3 hx
  have hcomm : ∀ i j : ℕ, c ^ j * d ^ i = d ^ i * c ^ j := fun i j =>
    ((Commute.pow_pow (hdc : Commute d c) i j).eq).symm
  have hcj : c ^ j = c ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hc3, one_pow, one_mul]
  have hj : j % 3 = 1 ∨ j % 3 = 2 := by
    have : j % 3 ≠ 0 := by
      intro h0
      apply hxd
      rw [hcj, h0, pow_zero, mul_one]
      exact Subgroup.npow_mem_zpowers d i
    omega
  have hdc' : Commute d c := hdc
  rcases hj with h1 | h2
  · refine ⟨i, ?_⟩
    rw [hcj, h1, pow_one, (hdc'.pow_left i).eq]
  · refine ⟨2 * i, ?_⟩
    rw [hcj, h2]
    have hx3 : (d ^ i * c ^ 2) ^ 3 = 1 := by
      rw [(Commute.mul_pow (Commute.pow_pow (hdc : Commute d c) i 2) 3), ← pow_mul, ← pow_mul,
        mul_comm i 3, mul_comm 2 3, pow_mul, pow_mul, hd3, hc3, one_pow, one_pow, one_mul]
    have hsq : (d ^ i * c ^ 2) ^ 2 = c * d ^ (2 * i) := by
      rw [(Commute.mul_pow (Commute.pow_pow (hdc : Commute d c) i 2) 2), ← pow_mul, ← pow_mul,
        mul_comm i 2, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one,
        (hdc'.pow_left (2 * i)).eq]
    have hne : (d ^ i * c ^ 2) ^ 2 ≠ 1 := by
      intro h
      apply hxd
      have : d ^ i * c ^ 2 = 1 := by
        calc d ^ i * c ^ 2 = (d ^ i * c ^ 2) ^ 3 * ((d ^ i * c ^ 2) ^ 2)⁻¹ := by group
          _ = 1 := by rw [hx3, h, inv_one, one_mul]
      rw [hcj, h2, this]
      exact one_mem _
    rw [← hsq]
    exact (TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three hx3 hne
      (Subgroup.npow_mem_zpowers _ 2)).symm

theorem hessPair_of_transitive {E : Subgroup X} {d c : X} (hE : E = Subgroup.zpowers d ⊔
      Subgroup.zpowers c) (hdc : d * c = c * d) (hd3 : d ^ 3 = 1) (hc3 : c ^ 3 = 1) (hd1 : d ≠ 1)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    (hpair : ∀ k : ℕ, HessPair E d (c * d ^ k)) {b b' : X} (hbE : b ∈ E) (hb1 : b ≠ 1)
    (hb'E : b' ∈ E) (hb'1 : b' ≠ 1) (hbb' : Subgroup.zpowers b ≠ Subgroup.zpowers b') :
    HessPair E b b' := by
  have hdE : d ∈ E := hE ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  obtain ⟨w, hw, hwd⟩ := htr d hdE hd1 b hbE hb1
  set y := w⁻¹ * b' * w with hy
  have hyE : y ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) b').mp hb'E
    rwa [inv_inv] at this
  have hy1 : y ≠ 1 := by
    intro h
    apply hb'1
    calc b' = w * y * w⁻¹ := by rw [hy]; group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  have hyd : y ∉ Subgroup.zpowers d := by
    intro hmem
    apply hbb'
    have h1 : Subgroup.zpowers y = Subgroup.zpowers d :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three hd3 hy1 hmem
    rw [← hwd, ← map_conj_zpowers, ← h1, map_conj_zpowers, hy]
    congr 1
    group
  obtain ⟨k, hk⟩ := exists_zpowers_eq_mul_pow hdc hd3 hc3 (hE ▸ hyE) hyd
  have h := ((hpair k).congr_right hk.symm).conj hw
  rw [hwd] at h
  convert h using 1
  rw [hy]
  group

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
