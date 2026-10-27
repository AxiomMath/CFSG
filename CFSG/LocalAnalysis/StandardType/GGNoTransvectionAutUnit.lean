module

public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix Multiplicative TableBOrthL UCoord

namespace NoTvAut

section Coord

variable {p : ℕ}

@[expose] def ext3 (s : Fin 3 → ZMod p) : Fin 4 → ZMod p :=
  ![s 0, s 1, s 2, -(s 0 + s 1 + s 2)]

theorem sum_ext3 (s : Fin 3 → ZMod p) : ∑ k, ext3 s k = 0 := by
  simp only [ext3, Fin.sum_univ_four]
  simp

variable (p) in
@[expose] def emb4 : Multiplicative (Fin 3 → ZMod p) →* ↥(sumZero 4 p) where
  toFun s := ⟨fun k => ofAdd (ext3 (toAdd s) k), sum_ext3 (toAdd s)⟩
  map_one' := ext_crd fun k => by
    fin_cases k <;> simp [crd, ext3]
  map_mul' x y := ext_crd fun k => by
    fin_cases k <;> simp [crd, ext3]
    ring

theorem crd_emb4 (s : Fin 3 → ZMod p) (k : Fin 4) : crd (emb4 p (ofAdd s)) k = ext3 s k :=
  rfl

@[expose] def coords3 (f : ↥(sumZero 4 p)) : Fin 3 → ZMod p :=
  ![crd f 0, crd f 1, crd f 2]

theorem emb4_coords3 (f : ↥(sumZero 4 p)) : emb4 p (ofAdd (coords3 f)) = f := by
  refine ext_crd fun k => ?_
  have hs := sum_crd f
  rw [Fin.sum_univ_four] at hs
  rw [crd_emb4]
  fin_cases k
  · rfl
  · rfl
  · rfl
  · show -(crd f 0 + crd f 1 + crd f 2) = crd f 3
    linear_combination -hs

theorem coords3_emb4 (s : Fin 3 → ZMod p) : coords3 (emb4 p (ofAdd s)) = s := by
  funext i
  fin_cases i <;> rfl

theorem emb4_injective : Function.Injective (emb4 p) := fun x y h => by
  have h1 := congrArg coords3 h
  rw [show x = ofAdd (toAdd x) from rfl, show y = ofAdd (toAdd y) from rfl, coords3_emb4,
    coords3_emb4] at h1
  exact toAdd.injective h1

variable (p) in
@[expose] def cartanU4 : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  1 + Matrix.of fun _ _ => 1

theorem dot_cartanU4 (s t : Fin 3 → ZMod p) :
    s ⬝ᵥ (cartanU4 p *ᵥ t) = ∑ k, ext3 s k * ext3 t k := by
  simp only [dotProduct, mulVec, cartanU4, Fin.sum_univ_three, Fin.sum_univ_four, ext3,
    Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  simp
  ring

theorem cartanU4_transpose : (cartanU4 p)ᵀ = cartanU4 p := by
  ext i j
  simp only [cartanU4, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.of_apply]
  by_cases h : i = j
  · subst h
    rfl
  · simp [h, Ne.symm h]

theorem cartanU4_apply_self (i : Fin 3) : cartanU4 p i i = 2 := by
  simp only [cartanU4, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
  norm_num

theorem cartanU4_apply_ne {i j : Fin 3} (h : i ≠ j) : cartanU4 p i j = 1 := by
  simp only [cartanU4, Matrix.add_apply, Matrix.one_apply_ne h, Matrix.of_apply, zero_add]

theorem cartanU4_nondeg [Fact p.Prime] (h4 : (4 : ZMod p) ≠ 0) (x : Fin 3 → ZMod p)
    (h : ∀ y, y ⬝ᵥ (cartanU4 p *ᵥ x) = 0) : x = 0 := by
  have h0 := h (Pi.single 0 1)
  have h1 := h (Pi.single 1 1)
  have h2 := h (Pi.single 2 1)
  simp only [mulVec, dotProduct, cartanU4, Fin.sum_univ_three, Matrix.add_apply,
    Matrix.one_apply, Matrix.of_apply] at h0 h1 h2
  simp at h0 h1 h2
  have hsum : 4 * (x 0 + x 1 + x 2) = 0 := by linear_combination h0 + h1 + h2
  have hs : x 0 + x 1 + x 2 = 0 := (mul_eq_zero.mp hsum).resolve_left h4
  funext i
  fin_cases i
  · show x 0 = 0
    linear_combination h0 - hs
  · show x 1 = 0
    linear_combination h1 - hs
  · show x 2 = 0
    linear_combination h2 - hs

end Coord

section Model

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem emb4_perm (σ : Equiv.Perm (Fin 4)) {x y : Fin 3 → ZMod p}
    (h : ∀ k, ext3 y k = ext3 x (σ⁻¹ k)) :
    emb4 p (ofAdd y) = permAutV σ (emb4 p (ofAdd x)) :=
  ext_crd fun k => by rw [crd_permAutV, crd_emb4, crd_emb4, h]

theorem ggNoTransvectionSC_of_permEltSC_four [Fact p.Prime] (hp2 : p ≠ 2)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusPermEltSC p 4 R) : GGNoTransvectionSC p R I := by
  have hp : p.Prime := Fact.out
  intro Eh hEhI hEhA h3 hscR a htv
  have hI : ∀ φ ∈ Eh, φ ∈ Set.range (MulAut.conj : R →* MulAut R) :=
    fun φ hφ => hIp φ (hEhI hφ) (hEhA.2 φ hφ)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI φ hφ
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA x.2 y.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    show MulAut.conj g ∈ Eh
    refine hscR g (fun φ hφ => ?_) hgp
    obtain ⟨y, rfl⟩ := hI φ hφ
    have hy : y ∈ E := hφ
    rw [MulAut.conj_apply, ← hg y hy, mul_inv_cancel_right]
  obtain ⟨τ, hτinj, hτE, hP, hnorm⟩ := h E hEe (hcardE ▸ h3) hscE
  have hτmem : ∀ f, τ f ∈ E := fun f => hτE ▸ ⟨f, rfl⟩
  have haE : ∀ b : Subgroup.normalizer (Eh : Set (MulAut R)), ∀ e ∈ E, (b : MulAut R) e ∈ E := by
    intro b e he
    show MulAut.conj ((b : MulAut R) e) ∈ Eh
    rw [← TableBOrth.mulAut_mul_conj_mul_inv]
    exact (Subgroup.mem_normalizer_iff.mp b.2 (MulAut.conj e)).mp he
  have hex : ∀ f, ∃ f', (a : MulAut R) (τ f) = τ f' := fun f => by
    have h1 : (a : MulAut R) (τ f) ∈ τ.range := hτE ▸ haE a _ (hτmem f)
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', hf'.symm⟩
  choose u hu using hex
  have humul : ∀ f g, u (f * g) = u f * u g := fun f g => hτinj (by
    calc τ (u (f * g)) = (a : MulAut R) (τ (f * g)) := (hu _).symm
      _ = (a : MulAut R) (τ f) * (a : MulAut R) (τ g) := by rw [map_mul, map_mul]
      _ = τ (u f) * τ (u g) := by rw [hu, hu]
      _ = τ (u f * u g) := (map_mul _ _ _).symm)
  set T : (Fin 3 → ZMod p) →+ (Fin 3 → ZMod p) :=
    AddMonoidHom.mk' (fun s => coords3 (u (emb4 p (ofAdd s)))) (fun x y => by
      show coords3 (u (emb4 p (ofAdd x * ofAdd y))) = _
      rw [map_mul, humul]
      funext i
      fin_cases i <;> rfl) with hTdef
  have hembT : ∀ s, emb4 p (ofAdd (T s)) = u (emb4 p (ofAdd s)) := fun s => emb4_coords3 _
  set ι : Multiplicative (Fin 3 → ZMod p) →* MulAut R :=
    (MulAut.conj : R →* MulAut R).comp (τ.comp (emb4 p)) with hιdef
  have hιapp : ∀ s, ι s = MulAut.conj (τ (emb4 p s)) := fun s => rfl
  have hι : Function.Injective ι := hinj.comp (hτinj.comp emb4_injective)
  have hιB : ι.range = Eh := by
    ext φ
    constructor
    · rintro ⟨s, rfl⟩
      exact hτmem _
    · intro hφ
      obtain ⟨y, rfl⟩ := hI φ hφ
      have hy : y ∈ E := hφ
      rw [← hτE] at hy
      obtain ⟨f, rfl⟩ := hy
      exact ⟨ofAdd (coords3 f), by rw [hιapp, emb4_coords3]⟩
  obtain ⟨hfix, hN⟩ := transvection_coords (t := T) hι hιB (fun b s hb => by
      show (a : MulAut R) * b * (a : MulAut R)⁻¹ = ι (ofAdd (T s))
      rw [hb, hιapp, hιapp, TableBOrth.mulAut_mul_conj_mul_inv, hu, hembT]) htv
  have hinv : ∀ σ : Equiv.Perm (Fin 4), ∀ x y x' y' : Fin 3 → ZMod p,
      emb4 p (ofAdd x') = permAutV σ (emb4 p (ofAdd x)) →
      emb4 p (ofAdd y') = permAutV σ (emb4 p (ofAdd y)) →
      T x' ⬝ᵥ (cartanU4 p *ᵥ T y') = T x ⬝ᵥ (cartanU4 p *ᵥ T y) := by
    intro σ x y x' y' hx hy
    obtain ⟨w, hw⟩ := hP σ
    have hwE : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
      intro e he
      rw [← hτE] at he
      obtain ⟨f, rfl⟩ := he
      rw [hw]
      exact hτmem _
    have haw : ∀ e ∈ E, (a : MulAut R) w * e * ((a : MulAut R) w)⁻¹ ∈ E := by
      intro e he
      have h1 : ((a⁻¹ : Subgroup.normalizer (Eh : Set (MulAut R))) : MulAut R) e ∈ E :=
        haE a⁻¹ e he
      have h2 := haE a _ (hwE _ h1)
      rwa [map_mul, map_mul, map_inv, Subgroup.coe_inv, MulAut.apply_inv_self] at h2
    obtain ⟨π, hπ⟩ := hnorm _ haw
    have hu' : ∀ f, u (permAutV σ f) = permAutV π (u f) := fun f => hτinj (by
      calc τ (u (permAutV σ f)) = (a : MulAut R) (τ (permAutV σ f)) := (hu _).symm
        _ = (a : MulAut R) (w * τ f * w⁻¹) := by rw [hw]
        _ = (a : MulAut R) w * (a : MulAut R) (τ f) * ((a : MulAut R) w)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = (a : MulAut R) w * τ (u f) * ((a : MulAut R) w)⁻¹ := by rw [hu]
        _ = τ (permAutV π (u f)) := hπ _)
    have hcrd : ∀ z z' : Fin 3 → ZMod p, emb4 p (ofAdd z') = permAutV σ (emb4 p (ofAdd z)) →
        ∀ k, ext3 (T z') k = crd (u (emb4 p (ofAdd z))) (π⁻¹ k) := by
      intro z z' hz k
      rw [← crd_emb4, hembT, hz, hu', crd_permAutV]
    rw [dot_cartanU4, dot_cartanU4]
    calc ∑ k, ext3 (T x') k * ext3 (T y') k
        = ∑ k, crd (u (emb4 p (ofAdd x))) (π⁻¹ k) * crd (u (emb4 p (ofAdd y))) (π⁻¹ k) :=
          Finset.sum_congr rfl fun k _ => by rw [hcrd x x' hx k, hcrd y y' hy k]
      _ = ∑ k, crd (u (emb4 p (ofAdd x))) k * crd (u (emb4 p (ofAdd y))) k :=
          Equiv.sum_comp π⁻¹ fun k => crd (u (emb4 p (ofAdd x))) k * crd (u (emb4 p (ofAdd y))) k
      _ = ∑ k, ext3 (T x) k * ext3 (T y) k :=
          Finset.sum_congr rfl fun k _ => by rw [← crd_emb4, ← crd_emb4, hembT, hembT]
  have m01 : emb4 p (ofAdd (Pi.single 1 1)) =
      permAutV (Equiv.swap 0 1) (emb4 p (ofAdd (Pi.single 0 1))) :=
    emb4_perm _ fun k => by fin_cases k <;> simp [ext3, Equiv.swap_apply_def]
  have m02 : emb4 p (ofAdd (Pi.single 2 1)) =
      permAutV (Equiv.swap 0 2) (emb4 p (ofAdd (Pi.single 0 1))) :=
    emb4_perm _ fun k => by fin_cases k <;> simp [ext3, Equiv.swap_apply_def]
  have m02b : emb4 p (ofAdd (Pi.single 1 1)) =
      permAutV (Equiv.swap 0 2) (emb4 p (ofAdd (Pi.single 1 1))) :=
    emb4_perm _ fun k => by fin_cases k <;> simp [ext3, Equiv.swap_apply_def]
  have m12a : emb4 p (ofAdd (Pi.single 0 1)) =
      permAutV (Equiv.swap 1 2) (emb4 p (ofAdd (Pi.single 0 1))) :=
    emb4_perm _ fun k => by fin_cases k <;> simp [ext3, Equiv.swap_apply_def]
  have m12b : emb4 p (ofAdd (Pi.single 2 1)) =
      permAutV (Equiv.swap 1 2) (emb4 p (ofAdd (Pi.single 1 1))) :=
    emb4_perm _ fun k => by fin_cases k <;> simp [ext3, Equiv.swap_apply_def]
  have m13 : emb4 p (ofAdd (Pi.single 0 1 - Pi.single 1 1)) =
      permAutV (Equiv.swap 1 3) (emb4 p (ofAdd (Pi.single 0 1))) :=
    emb4_perm _ fun k => by fin_cases k <;> simp [ext3, Equiv.swap_apply_def]
  have hsym : ∀ x y, T x ⬝ᵥ (cartanU4 p *ᵥ T y) = T y ⬝ᵥ (cartanU4 p *ᵥ T x) :=
    fun x y => dotProduct_mulVec_comm cartanU4_transpose _ _
  have h11 := hinv _ _ _ _ _ m01 m01
  have h22 := hinv _ _ _ _ _ m02 m02
  have h02 := hinv _ _ _ _ _ m12a m12b
  have h21 := hinv _ _ _ _ _ m02 m02b
  have h13 := hinv _ _ _ _ _ m13 m13
  rw [map_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h13
  have h00 : T (Pi.single 0 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 0 1)) =
      2 * (T (Pi.single 0 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 1 1))) := by
    linear_combination h13 - h11 + hsym (Pi.single 1 1) (Pi.single 0 1)
  obtain ⟨c, hc⟩ : ∃ c, T (Pi.single 0 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 1 1)) = c := ⟨_, rfl⟩
  have v00 : T (Pi.single 0 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 0 1)) = c * cartanU4 p 0 0 := by
    rw [cartanU4_apply_self]
    linear_combination h00 + 2 * hc
  have v01 : T (Pi.single 0 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 1 1)) = c * cartanU4 p 0 1 := by
    rw [cartanU4_apply_ne (by decide)]
    linear_combination hc
  have v02 : T (Pi.single 0 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 2 1)) = c * cartanU4 p 0 2 := by
    rw [cartanU4_apply_ne (by decide)]
    linear_combination h02 + hc
  have v10 : T (Pi.single 1 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 0 1)) = c * cartanU4 p 1 0 := by
    rw [cartanU4_apply_ne (by decide)]
    linear_combination hsym (Pi.single 1 1) (Pi.single 0 1) + hc
  have v11 : T (Pi.single 1 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 1 1)) = c * cartanU4 p 1 1 := by
    rw [cartanU4_apply_self]
    linear_combination h11 + h00 + 2 * hc
  have v12 : T (Pi.single 1 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 2 1)) = c * cartanU4 p 1 2 := by
    rw [cartanU4_apply_ne (by decide)]
    linear_combination hsym (Pi.single 1 1) (Pi.single 2 1) + h21 + hc
  have v20 : T (Pi.single 2 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 0 1)) = c * cartanU4 p 2 0 := by
    rw [cartanU4_apply_ne (by decide)]
    linear_combination hsym (Pi.single 2 1) (Pi.single 0 1) + h02 + hc
  have v21 : T (Pi.single 2 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 1 1)) = c * cartanU4 p 2 1 := by
    rw [cartanU4_apply_ne (by decide)]
    linear_combination h21 + hc
  have v22 : T (Pi.single 2 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single 2 1)) = c * cartanU4 p 2 2 := by
    rw [cartanU4_apply_self]
    linear_combination h22 + h00 + 2 * hc
  have hval : ∀ i j : Fin 3, T (Pi.single i 1) ⬝ᵥ (cartanU4 p *ᵥ T (Pi.single j 1)) =
      c * cartanU4 p i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact v00
    · exact v01
    · exact v02
    · exact v10
    · exact v11
    · exact v12
    · exact v20
    · exact v21
    · exact v22
  have hB : ∀ x y, T x ⬝ᵥ (cartanU4 p *ᵥ T y) = c * (x ⬝ᵥ (cartanU4 p *ᵥ y)) := by
    intro x y
    rw [addMonoidHom_eq_sum T x, addMonoidHom_eq_sum T y, mulVec_sum, sum_dotProduct]
    simp only [dotProduct_sum, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hval]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h4
    have h' : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h4
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h')
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  exact false_of_isTransvection_similitude_nd hp2 cartanU4_transpose (cartanU4_nondeg h4) T _
    hB hfix hN

end Model

end NoTvAut

open NoTvAut

section Drop

theorem ggUnitaryFourTvSCInput_holds : GGUnitaryFourTvSCInput := by
  intro K _ _ n p hK hn hp hpq
  have := Fact.mk hp
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hpd : ¬ p ∣ 4 := fun h4 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)))
  have hdq : ((4 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : (4 : ℕ) = 3 := congrArg Prod.fst h
    omega
  exact ggNoTransvectionSC_of_permEltSC_four hp2
    (fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn (by norm_num) hdq hp hpq hpd φ hφ hφp)
    (TableBUE.center_proj_eq_bot hK (by norm_num) hdq)
    (UModel.ggTorusPermEltSC_unitary hK hn (by norm_num) hp hp2 hpq hpd)

theorem ggOrthLTvSCRest_of_signedTorus (hS : GGOrthSignedTorusInput)
    (hE : GGOrthEvenTorusInput) : GGOrthLTvSCRest :=
  ggOrthLTvSCRest_of_torus hS hE ggUnitaryFourTvSCInput_holds

end Drop

end CFSG.StandardType

end
