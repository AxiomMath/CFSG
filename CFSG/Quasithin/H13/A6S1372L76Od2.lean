module

public import CFSG.Quasithin.H13.A6S1372L76Od1
public import CFSG.Quasithin.H13.A6S1372L76Y
public import CFSG.Quasithin.H13.A6S1372L76Z2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Od

variable {W : Type*} [CommGroup W]

theorem trivial_of_commute_natSL3 {F : Type} [Field F] [Finite F] {Y : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥Y}
    (h : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia Y U Z π)
    {a : MulAut W} (hcomm : ∀ y ∈ Y, a * y = y * a) (hU : ∀ u ∈ U, a u ∈ U)
    (hZ : ∀ z ∈ Z, a z ∈ Z) {N : ℕ} (hN0 : 0 < N) (hN : a ^ N = 1)
    (hcop : Nat.Coprime N (Nat.card F - 1)) : ∀ u ∈ U, a u * u⁻¹ ∈ Z := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨-, hYU, β, hβs, hβk, hβe⟩ := A6L76Z.natRealizes_clean h
  let aU : ↥U →* ↥U :=
    ((a : W ≃* W).toMonoidHom.comp U.subtype).codRestrict U fun u => hU u u.2
  have haU : ∀ u : ↥U, ((aU u : ↥U) : W) = a u := fun u => rfl
  have hker : β.ker ≤ (β.comp aU).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [MonoidHom.comp_apply, hβk, haU]
    exact hZ _ ((hβk u).1 hu)
  let fM : Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
    (β.liftOfRightInverse (Function.surjInv hβs) (Function.rightInverse_surjInv hβs))
      ⟨β.comp aU, hker⟩
  have hfM : ∀ u, fM (β u) = β (aU u) := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  let f : (Fin 3 → F) →+ (Fin 3 → F) := AddMonoidHom.toMultiplicative.symm fM
  have hf : ∀ u, f (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (aU u)) := fun u => by
    show Multiplicative.toAdd (fM (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))) = _
    rw [ofAdd_toAdd, hfM]
  have htr : ∀ i j : Fin 3, i ≠ j → ∀ (c : F) (w : Fin 3 → F),
      f (Matrix.transvection i j c *ᵥ w) = Matrix.transvection i j c *ᵥ f w := by
    intro i j hij c w
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F),
        (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = Matrix.transvection i j c :=
      ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
        (by rw [Matrix.det_transvection_of_ne _ _ hij]; exact one_ne_zero),
        Subgroup.subset_closure (Matrix.det_transvection_of_ne i j hij c :)⟩, rfl⟩
    have hu1 : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U := hYU _ u u.2
    have hu2 : ((π γ : ↥Y) : MulAut W) ((aU u : ↥U) : W) ∈ U := hYU _ _ (aU u).2
    have e1 := hβe γ u hu1
    have e2 := hβe γ (aU u) hu2
    have e3 : aU ⟨_, hu1⟩ = ⟨_, hu2⟩ := Subtype.ext (by
      show a (((π γ : ↥Y) : MulAut W) (u : W)) = ((π γ : ↥Y) : MulAut W) (a u)
      rw [← MulAut.mul_apply, hcomm _ (π γ).2, MulAut.mul_apply])
    calc f (Matrix.transvection i j c *ᵥ w) = f (Multiplicative.toAdd (β ⟨_, hu1⟩)) := by
          rw [e1, hγ, hu, toAdd_ofAdd, toAdd_ofAdd]
      _ = Multiplicative.toAdd (β (aU ⟨_, hu1⟩)) := hf _
      _ = Matrix.transvection i j c *ᵥ Multiplicative.toAdd (β (aU u)) := by
          rw [e3, e2, hγ, toAdd_ofAdd]
      _ = Matrix.transvection i j c *ᵥ f w := by rw [← hf, hu, toAdd_ofAdd]
  obtain ⟨c, hc⟩ := eq_smul_of_commute_transvection f htr
  have hc1 : ∀ u, Multiplicative.toAdd (β (aU u)) = c • Multiplicative.toAdd (β u) := fun u => by
    rw [← hf, hc]
  have hit : ∀ (m : ℕ) (u : ↥U), (((⇑aU)^[m] u : ↥U) : W) = (a ^ m) u := by
    intro m
    induction m with
    | zero => intro u; rfl
    | succ m ih =>
      intro u
      rw [Function.iterate_succ_apply, ih, haU, pow_succ, MulAut.mul_apply]
  have hitc : ∀ (m : ℕ) (u : ↥U),
      Multiplicative.toAdd (β ((⇑aU)^[m] u)) = c ^ m • Multiplicative.toAdd (β u) := by
    intro m
    induction m with
    | zero => intro u; simp
    | succ m ih =>
      intro u
      rw [Function.iterate_succ_apply, ih, hc1, pow_succ, mul_smul]
  have hcN : c ^ N = 1 := by
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
    have h1 : (⇑aU)^[N] u = u := Subtype.ext (by rw [hit, hN]; rfl)
    have h2 := hitc N u
    rw [h1, hu, toAdd_ofAdd] at h2
    have h3 := congrFun h2 0
    simpa using h3.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne'] at hcN
    exact zero_ne_one hcN
  have hcq : c ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one c hc0
  have hc' : c = 1 := by
    have h := pow_gcd_eq_one.2 ⟨hcN, hcq⟩
    rwa [hcop, pow_one] at h
  intro u hu
  have h1 : β (aU ⟨u, hu⟩) = β ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    rw [hc1, hc', one_smul]
  have h2 : β (aU ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (hβk _).1 h2

@[expose] def w5 (i : Fin 5) : Fin 5 → ZMod 2 := fun j => if j = i then 0 else 1

@[expose] def cyc (p q r : Fin 5) : Perm (Fin 5) := swap p q * swap q r

@[expose] def stab5 (i : Fin 5) : Perm (Fin 5) × Perm (Fin 5) :=
  ![(cyc 1 2 3, cyc 2 3 4), (cyc 0 2 3, cyc 2 3 4), (cyc 0 1 3, cyc 1 3 4), (cyc 0 1 2, cyc 1 2 4),
    (cyc 0 1 2, cyc 1 2 3)] i

theorem stab5_sign : ∀ i : Fin 5, Perm.sign (stab5 i).1 = 1 ∧ Perm.sign (stab5 i).2 = 1 := by
  decide +kernel

theorem stab5_fix : ∀ i j : Fin 5,
    w5 i ((stab5 i).1⁻¹ j) = w5 i j ∧ w5 i ((stab5 i).2⁻¹ j) = w5 i j := by
  decide +kernel

theorem stab5_fixed : ∀ (i : Fin 5) (m : Fin 5 → ZMod 2), ∑ j, m j = 0 →
    (∀ j, m ((stab5 i).1⁻¹ j) = m j) → (∀ j, m ((stab5 i).2⁻¹ j) = m j) → m = 0 ∨ m = w5 i := by
  decide +kernel

theorem gen_five : ∀ m : Fin 5 → ZMod 2, ∑ j, m j = 0 →
    m = 0 ∨ (∃ k, m = w5 k) ∨ ∃ i j, m = w5 i + w5 j := by
  decide +kernel

theorem w5_sum : ∀ i : Fin 5, ∑ j, w5 i j = 0 := by
  decide +kernel

theorem w5_ne_zero : ∀ i : Fin 5, w5 i ≠ 0 := by
  decide +kernel

theorem trivial_of_commute_altDn5 {Y : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥Y} (h : (FFModel.altDn 5).RealizesVia Y U Z π)
    {a : MulAut W} (hcomm : ∀ y ∈ Y, a * y = y * a) (hU : ∀ u ∈ U, a u ∈ U)
    (hZ : ∀ z ∈ Z, a z ∈ Z) (hZ' : ∀ z ∈ U, a z ∈ Z → z ∈ Z) : ∀ u ∈ U, a u * u⁻¹ ∈ Z := by
  classical
  obtain ⟨-, -, -, hYU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let aU : ↥U →* ↥U :=
    ((a : W ≃* W).toMonoidHom.comp U.subtype).codRestrict U fun u => hU u u.2
  have haU : ∀ u : ↥U, ((aU u : ↥U) : W) = a u := fun u => rfl
  have hmk := A7.altDn_five_mk_injective
  let δ : ↥U →* ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec :=
    β.comp aU / β
  have hδ : ∀ u, δ u = β (aU u) / β u := fun u => rfl
  have hδZ : β.ker ≤ δ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [hδ, hu, div_one, hβk, haU]
    exact hZ _ ((hβk u).1 hu)
  let δ' := (β.liftOfRightInverse (Function.surjInv hβs) (Function.rightInverse_surjInv hβs))
    ⟨δ, hδZ⟩
  have hδ' : ∀ u, δ' (β u) = δ u := fun u => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  obtain ⟨vec, wq, hvinj, hvact, hvone, hvmul, hvsec, hwq⟩ :
      ∃ (vec : (FFModel.altDn 5).Amb → (Fin 5 → ZMod 2)) (wq : Fin 5 → ↥(FFModel.altDn 5).sec),
        Function.Injective vec ∧
        (∀ (σ : ↥(alternatingGroup (Fin 5))) x j,
          vec ((FFModel.altDn 5).act σ x) j = vec x ((σ : Perm (Fin 5))⁻¹ j)) ∧
        vec 1 = 0 ∧ (∀ x y, vec (x * y) = vec x + vec y) ∧
        (∀ x ∈ (FFModel.altDn 5).sec, ∑ j, vec x j = 0) ∧
        ∀ i, vec (wq i : (FFModel.altDn 5).Amb) = w5 i :=
    ⟨fun x => Multiplicative.toAdd (x : G6.PermMod 5),
      fun i => ⟨(Multiplicative.ofAdd (w5 i) : G6.PermMod 5), w5_sum i⟩,
      Multiplicative.toAdd.injective, fun _ _ _ => rfl, rfl, fun _ _ => rfl, fun _ hx => hx,
      fun _ => rfl⟩
  have hδw : ∀ i, δ' (QuotientGroup.mk (wq i)) = 1 := by
    intro i
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (wq i))
    rw [← hu, hδ', hδ, div_eq_one]
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (β (aU u))
    have hfix : ∀ σ : ↥(alternatingGroup (Fin 5)),
        (∀ j, w5 i ((σ : Perm (Fin 5))⁻¹ j) = w5 i j) →
          ∀ j, vec (y : (FFModel.altDn 5).Amb) ((σ : Perm (Fin 5))⁻¹ j) =
            vec (y : (FFModel.altDn 5).Amb) j := by
      intro σ hσ
      have hu1 : ((π σ : ↥Y) : MulAut W) (u : W) ∈ U := hYU _ u u.2
      have hfixw : (FFModel.altDn 5).act σ (wq i : (FFModel.altDn 5).Amb) = wq i :=
        hvinj (funext fun j => by rw [hvact, hwq]; exact hσ j)
      have e1 := hβe σ u (wq i) hu1 (hsec σ _ (wq i).2) hu
      have e1' : β ⟨_, hu1⟩ = β u := by
        refine e1.trans ?_
        rw [hu]
        congr 1
        exact Subtype.ext hfixw
      have hmod1 : ((π σ : ↥Y) : MulAut W) (u : W) * (u : W)⁻¹ ∈ Z := by
        have h2 : β (⟨_, hu1⟩ * u⁻¹) = 1 := by rw [map_mul, map_inv, e1', mul_inv_cancel]
        exact (hβk _).1 h2
      have hu2 : ((π σ : ↥Y) : MulAut W) ((aU u : ↥U) : W) ∈ U := hYU _ _ (aU u).2
      have e2 := hβe σ (aU u) y hu2 (hsec σ _ y.2) hy.symm
      have e3 : (⟨_, hu2⟩ : ↥U) = aU ⟨_, hu1⟩ := Subtype.ext (by
        show ((π σ : ↥Y) : MulAut W) (a u) = a (((π σ : ↥Y) : MulAut W) (u : W))
        rw [← MulAut.mul_apply, ← hcomm _ (π σ).2, MulAut.mul_apply])
      have e4 : β (aU ⟨_, hu1⟩) = β (aU u) := by
        have h3 : aU ⟨_, hu1⟩ * (aU u)⁻¹ = aU (⟨_, hu1⟩ * u⁻¹) := by
          rw [map_mul, map_inv]
        have h4 : β (aU (⟨_, hu1⟩ * u⁻¹)) = 1 := by
          rw [hβk, haU]
          exact hZ _ hmod1
        have h5 : β (aU ⟨_, hu1⟩ * (aU u)⁻¹) = 1 := by rw [h3, h4]
        rwa [map_mul, map_inv, mul_inv_eq_one] at h5
      have e5 : (QuotientGroup.mk ⟨_, hsec σ _ y.2⟩ : ↥(FFModel.altDn 5).sec ⧸
          (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = QuotientGroup.mk y :=
        e2.symm.trans ((congrArg β e3).trans (e4.trans hy.symm))
      have e6 : (FFModel.altDn 5).act σ (y : (FFModel.altDn 5).Amb) = y :=
        congrArg Subtype.val (hmk e5)
      intro j
      have e7 := congrFun (congrArg vec e6) j
      rwa [hvact] at e7
    have hy1 := hfix ⟨(stab5 i).1, Perm.mem_alternatingGroup.2 (stab5_sign i).1⟩
      (fun j => (stab5_fix i j).1)
    have hy2 := hfix ⟨(stab5 i).2, Perm.mem_alternatingGroup.2 (stab5_sign i).2⟩
      (fun j => (stab5_fix i j).2)
    rcases stab5_fixed i _ (hvsec _ y.2) hy1 hy2 with h0 | h0
    ·
      exfalso
      have hy0 : y = 1 := Subtype.ext (hvinj (h0.trans hvone.symm))
      have hau : β (aU u) = 1 := by rw [← hy, hy0, QuotientGroup.mk_one]
      have huZ : (u : W) ∈ Z := hZ' _ u.2 (by rw [← haU]; exact (hβk _).1 hau)
      have hu0 : β u = 1 := (hβk u).2 huZ
      rw [hu] at hu0
      have hw1 : wq i = 1 := hmk (hu0.trans (QuotientGroup.mk_one _).symm)
      have hw2 : vec (wq i : (FFModel.altDn 5).Amb) = 0 := by
        rw [hw1]
        exact hvone
      exact w5_ne_zero i ((hwq i).symm.trans hw2)
    · rw [← hy, hu]
      congr 1
      exact Subtype.ext (hvinj (h0.trans (hwq i).symm))
  have hδ'1 : ∀ m : ↥(FFModel.altDn 5).sec, δ' (QuotientGroup.mk m) = 1 := by
    intro m
    rcases gen_five _ (hvsec _ m.2) with h0 | ⟨k, hk⟩ | ⟨i, j, hij⟩
    · have hm : m = 1 := Subtype.ext (hvinj (h0.trans hvone.symm))
      rw [hm, QuotientGroup.mk_one, map_one]
    · have hm : m = wq k := Subtype.ext (hvinj (hk.trans (hwq k).symm))
      rw [hm]
      exact hδw k
    · have hm : m = wq i * wq j := Subtype.ext (hvinj (by
        rw [hij, Subgroup.coe_mul, hvmul, hwq, hwq]))
      rw [hm, QuotientGroup.mk_mul, map_mul, hδw, hδw, one_mul]
  intro u hu
  have h1 : δ ⟨u, hu⟩ = 1 := by
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
    rw [← hδ', ← hm, hδ'1]
  rw [hδ, div_eq_one] at h1
  have h2 : β (aU ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (hβk _).1 h2

theorem coprime_two_pow_sub_one {n : ℕ} (hn : Odd n) (k : ℕ) :
    Nat.Coprime (18 * 2 ^ k) (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm]
  have hpos : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hc2 : Nat.Coprime 2 (2 ^ (2 * m + 1) - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, h2]
    omega
  have hc3 : Nat.Coprime 3 (2 ^ (2 * m + 1) - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three, h2]
    omega
  rw [show 18 * 2 ^ k = 2 ^ (k + 1) * 3 ^ 2 by ring]
  exact Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hc2) (Nat.Coprime.pow_left _ hc3)

theorem faithful_of_odd {Y : Subgroup (MulAut W)}
    (hmod : (∃ n, Odd n ∧ BinaryNaturalSL Y (commV Y) (fixV Y ⊓ commV Y) 3 n) ∨
      AlternatingNatural Y (commV Y) (fixV Y ⊓ commV Y) 5) :
    ∀ y ∈ Y, (∀ u ∈ commV Y, y u * u⁻¹ ∈ fixV Y) → y = 1 := by
  intro y hy htriv
  have htriv' : ∀ u ∈ commV Y, y u * u⁻¹ ∈ fixV Y ⊓ commV Y := fun u hu =>
    ⟨htriv u hu, Subgroup.subset_closure ⟨y, hy, u, rfl⟩⟩
  rcases hmod with ⟨n, -, F, _, _, -, π, hπ⟩ | ⟨π, hπ⟩
  · exact G64.RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) hπ hy htriv'
  · exact G64.RealizesVia.eq_one_of_trivial (FFC.altDn_faithful (le_refl 5)) hπ hy htriv'

theorem trivial_of_commute_odd {Y : Subgroup (MulAut W)}
    (hmod : (∃ n, Odd n ∧ BinaryNaturalSL Y (commV Y) (fixV Y ⊓ commV Y) 3 n) ∨
      AlternatingNatural Y (commV Y) (fixV Y ⊓ commV Y) 5)
    {a : MulAut W} (hcomm : ∀ y ∈ Y, a * y = y * a) {k : ℕ} (ha : a ^ (18 * 2 ^ k) = 1) :
    ∀ u ∈ commV Y, a u * u⁻¹ ∈ fixV Y := by
  have hcomm' : ∀ y ∈ Y, a⁻¹ * y = y * a⁻¹ := fun y hy => by
    calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * y) * a⁻¹ := by rw [hcomm y hy]
      _ = y * a⁻¹ := by group
  have hpres : ∀ b : MulAut W, (∀ y ∈ Y, b * y = y * b) →
      (∀ u ∈ commV Y, b u ∈ commV Y) ∧ (∀ c ∈ fixV Y, b c ∈ fixV Y) := by
    intro b hb
    refine ⟨fun u hu => ?_, fun c hc y hy => ?_⟩
    · induction hu using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨y, hy, w, rfl⟩ := hg
        have e : b (y w * w⁻¹) = y (b w) * (b w)⁻¹ := by
          rw [map_mul, map_inv, ← MulAut.mul_apply, hb y hy, MulAut.mul_apply]
        rw [e]
        exact Subgroup.subset_closure ⟨y, hy, b w, rfl⟩
      | one => rw [map_one]; exact Subgroup.one_mem _
      | mul g g' _ _ hg hg' => rw [map_mul]; exact Subgroup.mul_mem _ hg hg'
      | inv g _ hg => rw [map_inv]; exact Subgroup.inv_mem _ hg
    · calc y (b c) = b (y c) := by rw [← MulAut.mul_apply, ← hb y hy, MulAut.mul_apply]
        _ = b c := by rw [hc y hy]
  obtain ⟨hUa, hFa⟩ := hpres a hcomm
  obtain ⟨-, hFa'⟩ := hpres a⁻¹ hcomm'
  have hZ : ∀ z ∈ fixV Y ⊓ commV Y, a z ∈ fixV Y ⊓ commV Y := fun z hz =>
    ⟨hFa _ hz.1, hUa _ hz.2⟩
  have hZ' : ∀ z ∈ commV Y, a z ∈ fixV Y ⊓ commV Y → z ∈ fixV Y ⊓ commV Y := by
    intro z hz haz
    have h1 := hFa' _ haz.1
    rw [MulAut.inv_apply_self] at h1
    exact ⟨h1, hz⟩
  have key : ∀ u ∈ commV Y, a u * u⁻¹ ∈ fixV Y ⊓ commV Y := by
    rcases hmod with ⟨n, hn, F, _, _, hcard, π, hπ⟩ | ⟨π, hπ⟩
    · refine trivial_of_commute_natSL3 hπ hcomm hUa hZ (N := 18 * 2 ^ k) (by positivity) ha ?_
      rw [hcard]
      exact coprime_two_pow_sub_one hn k
    · exact trivial_of_commute_altDn5 hπ hcomm hUa hZ hZ'
  exact fun u hu => (key u hu).1

end A6L76Od

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem X1375_le_L1 : S.X1375 ≤ S.L1 := by
  by_cases hhat : IsHatA6 L
  · rw [S.X1375_of_hat hhat]
    exact (S14.plusData_l1plus S (S.hatL1Plus hhat)).le_L1
  · rw [S.X1375_of_not_hat hhat]

theorem X1375_le_H {H : Subgroup G} (hH : H ∈ S.Hz) :
    S.X1375 ≤ H :=
  X1375_le_L1.trans (le_sup_left.trans hH.1.1)

theorem V3_le_commutator_X1375 : S.V3 ≤ ⁅S.V3, S.X1375⁆ := by
  by_cases hhat : IsHatA6 L
  · rw [S.X1375_of_hat hhat]
    exact V3_le_commutator_of_plus (S14.plusData_l1plus S (S.hatL1Plus hhat))
  · rw [S.X1375_of_not_hat hhat]
    exact S.V3_le_commutator_V3_L1

theorem pow_eq_one_of_mem_L1 {x : G} (hx : x ∈ S.L1) :
    ∃ k : ℕ, x ^ (18 * 2 ^ k) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxL : x ∈ L := (S.L1_le.trans inf_le_left) hx
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hxL
  set g : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, hxV⟩ with hg
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := g) hx
  have h6 : S.frame.ρ g ^ 6 = 1 := by
    rw [← K4L_sq _ (cube_mem_K4L h4 h5 hs), ← pow_add]
  have hx6V : x ^ 6 ∈ Subgroup.centralizer (V : Set G) := by
    have h := (S.rho_eq_one_iff (g ^ 6)).1 (by rw [map_pow, h6])
    simpa [hg] using h
  set y : ↥L := ⟨x, hxL⟩ ^ 6 with hy
  have hyV : (y : G) ∈ Subgroup.centralizer (V : Set G) := by simpa [hy] using hx6V
  have hyZ := S.mk_mem_center hyV
  have hy3 : (y : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
      (x := ⟨_, hyZ⟩)
    rcases S.card_center_Q with h1 | h1
    · rw [h1, pow_one] at h
      have h2 : (y : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := congrArg Subtype.val h
      rw [h2, one_pow]
    · rw [h1] at h
      simpa using congrArg Subtype.val h
  have hyN : y ^ 3 ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy3]
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨_, hyN⟩
  have hk' : (y ^ 3) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have h7 : (⟨x, hxL⟩ : ↥L) ^ (18 * 2 ^ k) = 1 := by
    rw [show 18 * 2 ^ k = 6 * 3 * 2 ^ k by ring, pow_mul, pow_mul]
    exact hk'
  simpa using congrArg Subtype.val h7

theorem false_of_comm_odd (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) {H : Subgroup G}
    (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G}
    (hK : K ∈ cComp H)
    (hmod : (∃ n, Odd n ∧ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) ∨
        AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
          (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
            commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 5)
    (hcomm : ∀ x (hx : x ∈ S.X1375), ∀ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨x, X1375_le_H hH hx⟩ * y =
        y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨x, X1375_le_H hH hx⟩) :
    False := by
  refine false_of_trivial_on_UK hH hK rfl (X1375_le_H hH) h139 h37 h38 h13315
    (fun x hx y hy => ?_) V3_le_commutator_X1375 (A6L76Od.faithful_of_odd hmod)
    (fun x hx => ?_)
  · rw [hcomm x hx y hy, mul_inv_cancel_right]
    exact hy
  · obtain ⟨k, hk⟩ := pow_eq_one_of_mem_L1 (X1375_le_L1 hx)
    refine A6L76Od.trivial_of_commute_odd hmod (hcomm x hx) (k := k) ?_
    have h1 : (⟨x, X1375_le_H hH hx⟩ : ↥H) ^ (18 * 2 ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [← map_pow, h1, map_one]

end Setting4

end CFSG.Quasithin.H13.A6
