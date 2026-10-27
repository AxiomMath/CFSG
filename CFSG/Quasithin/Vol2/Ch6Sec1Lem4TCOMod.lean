module

public import CFSG.Quasithin.Vol2.Ch6OrthX
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCOSL

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L216 CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self exists_add_frobPow_ne_zero
  fixed_of_unip)
open scoped MatrixGroups Matrix

theorem inv_lower_zero_of_upper {F : Type} [Field F] {g : SL(2, F)}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [L216.coe_inv_sl]
  simp [hg]

section Normalizer

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {F : Type} [Field F] [Finite F]

theorem conj_mem_autOn_TL_of_upper {ψ : ↥(autOn L V) ≃* SL(2, F)}
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (x : ↥(autOn L V)) (hx : (ψ x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    {p : MulAut V} (hp : p ∈ autOn (T ⊓ L) V) (hpA : p ∈ autOn L V) :
    (x : MulAut V) * p * (x : MulAut V)⁻¹ ∈ autOn (T ⊓ L) V := by
  obtain ⟨b, hb⟩ := (hψ ⟨p, hpA⟩).mp hp
  have key : ψ (x * ⟨p, hpA⟩ * x⁻¹) = unipSL ((ψ x : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b) := by
    rw [map_mul, map_mul, map_inv, hb]
    exact conj_unipSL_of_upper (g := (ψ x : SL(2, F))) hx b
  have hmem := (hψ (x * ⟨p, hpA⟩ * x⁻¹)).mpr ⟨_, key⟩
  exact hmem

theorem card_normalizer_part (hF : Nat.card F = 16)
    (ψ : ↥(autOn L V) ≃* SL(2, F))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b) :
    Nat.card ↥(autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))) = 240 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hmap : ((autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))).subgroupOf (autOn L V)).map
        ψ.toMonoidHom = CFSG.PSL2Table.borelSL F := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxN : (x : MulAut V) ∈ Subgroup.normalizer
          ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V)) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
      rw [CFSG.PSL2Table.mem_borelSL_iff]
      exact upper_of_mem_normalizer ψ hψ x hxN
    · intro hg
      rw [CFSG.PSL2Table.mem_borelSL_iff] at hg
      obtain ⟨x, rfl⟩ := ψ.surjective g
      refine ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩), rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · intro hp
        exact conj_mem_autOn_TL_of_upper hψ x hg hp (AutOn.autOn_mono inf_le_right hp)
      · intro hp
        have hpA : (x : MulAut V) * p * (x : MulAut V)⁻¹ ∈ autOn L V :=
          AutOn.autOn_mono inf_le_right hp
        have hxinv : ((ψ x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          rw [map_inv]
          exact inv_lower_zero_of_upper hg
        have h2 := conj_mem_autOn_TL_of_upper hψ x⁻¹ hxinv hp
          (by simpa using hpA)
        simpa [mul_assoc] using h2
  have h1 : Nat.card ((autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))).subgroupOf (autOn L V)) =
      Nat.card (CFSG.PSL2Table.borelSL F) := by
    rw [← hmap, Subgroup.card_map_of_injective ψ.injective]
  have hN : Nat.card ↥(autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))) =
      Nat.card ((autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))).subgroupOf (autOn L V)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [hN, h1, CFSG.PSL2Table.card_borelSL, hF']

end Normalizer

section Centralizer

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem card_fixed_four (hF : Nat.card F = 16) : Nat.card {x : F // x ^ 4 = x} = 4 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hdeg : (Polynomial.X ^ 4 - Polynomial.X : Polynomial F).natDegree = 4 := by
    compute_degree!
  have hne : (Polynomial.X ^ 4 - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hup : Fintype.card {x : F // x ^ 4 = x} ≤ 4 := by
    rw [Fintype.card_subtype]
    have hsub : (Finset.univ.filter (fun x : F => x ^ 4 = x)).val ⊆
        (Polynomial.X ^ 4 - Polynomial.X : Polynomial F).roots := by
      intro x hx
      rw [Finset.mem_val, Finset.mem_filter] at hx
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, hx.2, sub_self]
    have := Polynomial.card_le_degree_of_subset_roots hsub
    rw [hdeg] at this
    exact this
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hunits : Nat.card Fˣ = 15 := by rw [Nat.card_units, hF]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hunits]; norm_num)
  set ω : F := (u : F) with hω
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h
    have hu1 : u = 1 := Units.ext h
    rw [hu1, orderOf_one] at hu
    norm_num at hu
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω3
    norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h2, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hω2ω : ω ^ 2 ≠ ω := by
    intro h2
    have : ω * (ω - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact hω0 h
    · exact hω1 (sub_eq_zero.mp h)
  let g : Fin 4 → F := ![0, 1, ω, ω ^ 2]
  have hg4 : ∀ k : Fin 4, (g k) ^ 4 = g k := by
    intro k
    fin_cases k
    · simp [g]
    · simp [g]
    · simp only [g]
      calc ω ^ 4 = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω3, one_mul]
    · simp only [g]
      calc (ω ^ 2) ^ 4 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
        _ = ω ^ 2 := by rw [hω3, one_pow, one_mul]
  let f : Fin 4 → {x : F // x ^ 4 = x} := fun k => ⟨g k, hg4 k⟩
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have h0ω : (0 : F) ≠ ω := fun h => hω0 h.symm
  have h0ω2 : (0 : F) ≠ ω ^ 2 := fun h => hω0 (pow_eq_zero_iff two_ne_zero |>.mp h.symm)
  have h1ω : (1 : F) ≠ ω := fun h => hω1 h.symm
  have h1ω2 : (1 : F) ≠ ω ^ 2 := fun h => hω2 h.symm
  have hωω2 : ω ≠ ω ^ 2 := fun h => hω2ω h.symm
  have hinj : Function.Injective f := by
    intro i j hij
    have hv : g i = g j := congrArg Subtype.val hij
    by_contra hne
    apply hne
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hv h01 | exact absurd hv.symm h01 | exact absurd hv h0ω | exact absurd hv.symm h0ω | exact absurd hv h0ω2 | exact absurd hv.symm h0ω2 | exact absurd hv h1ω | exact absurd hv.symm h1ω | exact absurd hv h1ω2 | exact absurd hv.symm h1ω2 | exact absurd hv hωω2 | exact absurd hv.symm hωω2
  have hlow : 4 ≤ Nat.card {x : F // x ^ 4 = x} := by
    have := Nat.card_le_card_of_injective f hinj
    simpa using this
  have hup' : Nat.card {x : F // x ^ 4 = x} ≤ 4 := by
    rw [Nat.card_eq_fintype_card]
    exact hup
  omega

theorem diag_herm {x : F} (hx : x ^ 4 = x) :
    (frobPow 2 (!![x, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F))ᵀ = !![x, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, hx]

theorem diag_fixed {x : F} (b : F) :
    (unipSL b : Matrix (Fin 2) (Fin 2) F) * (!![x, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) *
      (frobPow 2 (unipSL b : Matrix (Fin 2) (Fin 2) F))ᵀ = !![x, 0; 0, 0] := by
  rw [coe_unipSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, Matrix.mul_apply, Fin.sum_univ_two]

theorem fix_iff_centralizer {T L V : Subgroup G} {ψ : ↥(autOn L V) ≃* SL(2, F)}
    (hTL : T ⊓ L ≤ Subgroup.normalizer (V : Set G))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (Y : ↥V →* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (hYinj : Function.Injective Y)
    (hYequiv : ∀ (x : ↥(autOn L V)) (w : ↥V),
      Multiplicative.toAdd (Y ((x : MulAut ↥V) w)) =
        (ψ x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (Y w) *
          (frobPow 2 (ψ x : Matrix (Fin 2) (Fin 2) F))ᵀ)
    (w : ↥V) :
    (w : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ↔
      ∀ b : F, (unipSL b : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (Y w) *
        (frobPow 2 (unipSL b : Matrix (Fin 2) (Fin 2) F))ᵀ = Multiplicative.toAdd (Y w) := by
  rw [mem_centralizer_iff_autOn hTL w]
  constructor
  · intro hw b
    have hxP : (ψ.symm (unipSL b) : MulAut V) ∈ autOn (T ⊓ L) V :=
      (hψ (ψ.symm (unipSL b))).mpr ⟨b, by rw [MulEquiv.apply_symm_apply]⟩
    have h1 : ((ψ.symm (unipSL b) : ↥(autOn L V)) : MulAut V) w = w := hw _ hxP
    have h2 := hYequiv (ψ.symm (unipSL b)) w
    rw [h1, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  · intro hfix x hx
    have hxA : x ∈ autOn L V := AutOn.autOn_mono inf_le_right hx
    obtain ⟨b, hb⟩ := (hψ ⟨x, hxA⟩).mp hx
    have h2 := hYequiv ⟨x, hxA⟩ w
    rw [hb, hfix b] at h2
    exact hYinj (Multiplicative.toAdd.injective h2)

theorem herm_entry_four {Z : Matrix (Fin 2) (Fin 2) F} (hZ : (frobPow 2 Z)ᵀ = Z) :
    Z 0 0 ^ 4 = Z 0 0 := by
  have h := congrFun (congrFun hZ 0) 0
  simpa [frobPow] using h

theorem fixed_eq_diag (hF : Nat.card F = 16) {Z : Matrix (Fin 2) (Fin 2) F}
    (hZ : (frobPow 2 Z)ᵀ = Z)
    (hfix : ∀ b : F, (unipSL b : Matrix (Fin 2) (Fin 2) F) * Z *
      (frobPow 2 (unipSL b : Matrix (Fin 2) (Fin 2) F))ᵀ = Z) :
    Z = !![Z 0 0, 0; 0, 0] := by
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hpow : ∀ x : F, (x ^ 2 ^ 2) ^ 2 ^ 2 = x := by
    intro x
    have h16 : x ^ 16 = x := by
      have := FiniteField.pow_card x
      rwa [hF'] at this
    calc (x ^ 2 ^ 2) ^ 2 ^ 2 = x ^ 16 := by ring
      _ = x := h16
  have hb0 : ∃ b : F, b + b ^ 2 ^ 2 ≠ 0 :=
    exists_add_frobPow_ne_zero (a := 2) (by norm_num) (by rw [hF]; norm_num)
  obtain ⟨h01, h10, h11⟩ := fixed_of_unip hpow hb0 hZ hfix
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

end Centralizer

section Assembly

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem card_V_centralizer (hF : Nat.card F = 16)
    {ψ : ↥(autOn L V) ≃* SL(2, F)} (hTL : T ⊓ L ≤ Subgroup.normalizer (V : Set G))
    (hψ : ∀ x : ↥(autOn L V), (x : MulAut V) ∈ autOn (T ⊓ L) V ↔ ∃ b : F, ψ x = unipSL b)
    (Y : ↥V →* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (hYinj : Function.Injective Y)
    (hYherm : ∀ w : ↥V, (frobPow 2 (Multiplicative.toAdd (Y w)))ᵀ = Multiplicative.toAdd (Y w))
    (hYsurj : ∀ Z : Matrix (Fin 2) (Fin 2) F, (frobPow 2 Z)ᵀ = Z → ∃ w : ↥V,
      Multiplicative.toAdd (Y w) = Z)
    (hYequiv : ∀ (x : ↥(autOn L V)) (w : ↥V),
      Multiplicative.toAdd (Y ((x : MulAut ↥V) w)) =
        (ψ x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (Y w) *
          (frobPow 2 (ψ x : Matrix (Fin 2) (Fin 2) F))ᵀ) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) = 4 := by
  classical
  let S := V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)
  let f : ↥S → {x : F // x ^ 4 = x} := fun s =>
    ⟨Multiplicative.toAdd (Y ⟨(s : G), (Subgroup.mem_inf.mp s.2).1⟩) 0 0,
      herm_entry_four (hYherm ⟨(s : G), (Subgroup.mem_inf.mp s.2).1⟩)⟩
  have hinj : Function.Injective f := by
    intro s s' hss
    have hv : Multiplicative.toAdd (Y ⟨(s : G), (Subgroup.mem_inf.mp s.2).1⟩) 0 0 =
        Multiplicative.toAdd (Y ⟨(s' : G), (Subgroup.mem_inf.mp s'.2).1⟩) 0 0 :=
      congrArg Subtype.val hss
    have hfixs := (fix_iff_centralizer hTL hψ Y hYinj hYequiv
      ⟨(s : G), (Subgroup.mem_inf.mp s.2).1⟩).mp (Subgroup.mem_inf.mp s.2).2
    have hfixs' := (fix_iff_centralizer hTL hψ Y hYinj hYequiv
      ⟨(s' : G), (Subgroup.mem_inf.mp s'.2).1⟩).mp (Subgroup.mem_inf.mp s'.2).2
    have e1 := fixed_eq_diag hF (hYherm _) hfixs
    have e2 := fixed_eq_diag hF (hYherm _) hfixs'
    have hYe : Multiplicative.toAdd (Y ⟨(s : G), (Subgroup.mem_inf.mp s.2).1⟩) =
        Multiplicative.toAdd (Y ⟨(s' : G), (Subgroup.mem_inf.mp s'.2).1⟩) := by
      rw [e1, e2, hv]
    have hw : (⟨(s : G), (Subgroup.mem_inf.mp s.2).1⟩ : ↥V) =
        ⟨(s' : G), (Subgroup.mem_inf.mp s'.2).1⟩ :=
      hYinj (Multiplicative.toAdd.injective hYe)
    exact Subtype.ext (congrArg (fun y : ↥V => (y : G)) hw)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨w, hw⟩ := hYsurj (!![x.1, 0; 0, 0]) (diag_herm x.2)
    have hwS : (w : G) ∈ S := by
      refine Subgroup.mem_inf.mpr ⟨w.2, ?_⟩
      rw [fix_iff_centralizer hTL hψ Y hYinj hYequiv w]
      intro b
      rw [hw]
      exact diag_fixed b
    refine ⟨⟨(w : G), hwS⟩, Subtype.ext ?_⟩
    show Multiplicative.toAdd (Y ⟨(w : G), (Subgroup.mem_inf.mp hwS).1⟩) 0 0 = x.1
    rw [show (⟨(w : G), (Subgroup.mem_inf.mp hwS).1⟩ : ↥V) = w from rfl, hw]
    simp
  have hequiv := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [hequiv, card_fixed_four hF]

theorem l216ModuleFact_holds : L216ModuleFact := by
  intro G _ _ T M L V h horth
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, hYherm, hYsurj, hYequiv, hψ⟩ :=
    IsOrthCh5.exists_sylowCoord (m := 2) (show IsOrthCh5 L V (2 * 2) from horth)
      h.isSylowTwoOf_inf_ch6
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  have hTL : T ⊓ L ≤ Subgroup.normalizer (V : Set G) := inf_le_right.trans h.L_le_normalizer
  exact ⟨card_normalizer_part hF16 ψ hψ, card_V_centralizer hF16 hTL hψ Y hYinj hYherm hYsurj
    hYequiv⟩

end Assembly

end CFSG.Quasithin.H13.T614
