module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJTools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open Subgroup

section Four

variable {Y : Type*} [Group Y]

theorem isElemAbelian_two_of_sq {W : Subgroup Y} (h : ∀ w ∈ W, w ^ 2 = 1) :
    CFSG.Assembly.IsElemAbelian 2 W := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, h⟩
  have e1 : (x : Y) * x = 1 := by rw [← pow_two]; exact h x x.2
  have e2 : (y : Y) * y = 1 := by rw [← pow_two]; exact h y y.2
  have e3 : (x : Y) * y * ((x : Y) * y) = 1 := by
    rw [← pow_two]
    exact h _ (W.mul_mem x.2 y.2)
  have i1 : (x : Y)⁻¹ = x := inv_eq_of_mul_eq_one_right e1
  have i2 : (y : Y)⁻¹ = y := inv_eq_of_mul_eq_one_right e2
  calc ((x * y : W) : Y) = (x : Y) * y := rfl
    _ = ((x : Y) * y)⁻¹ := eq_inv_of_mul_eq_one_left e3
    _ = (y : Y) * x := by rw [mul_inv_rev, i1, i2]

theorem isKleinFour_of {W : Subgroup Y} (hW : CFSG.Assembly.IsElemAbelian 2 W)
    (h4 : Nat.card W = 4) : IsKleinFour W where
  card_four := h4
  exponent_two := by
    have : Finite W := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
    have hd : Monoid.exponent W ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun w => Subtype.ext (by simpa using hW.2 w w.2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exfalso
      rw [Monoid.exp_eq_one_iff] at h1
      have := Finite.card_le_one_iff_subsingleton.mpr h1
      omega
    · exact h2

theorem conj_eq_of_fix {W : Subgroup Y} (hW : CFSG.Assembly.IsElemAbelian 2 W)
    (h4 : Nat.card W = 4) {x : Y} (hxN : x ∈ normalizer (W : Set Y)) (hx3 : x ^ 3 = 1) {w : Y}
    (hwW : w ∈ W) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w) : ∀ u ∈ W, x * u * x⁻¹ = u := by
  have hK := isKleinFour_of hW h4
  intro u huW
  by_cases hu1 : u = 1
  · rw [hu1, mul_one, mul_inv_cancel]
  by_cases huw : u = w
  · rw [huw, hxw]
  by_contra hne
  obtain ⟨u', hu'⟩ : ∃ u', u' = x * u * x⁻¹ := ⟨_, rfl⟩
  rw [← hu'] at hne
  have hu'W : u' ∈ W := hu' ▸ (mem_normalizer_iff.mp hxN u).mp huW
  have hu'1 : u' ≠ 1 := fun h => hu1 (by
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [← hu', h]; group)
  have hu'w : u' ≠ w := fun h => huw (by
    have h1 : x * u * x⁻¹ = x * w * x⁻¹ := by rw [← hu', h, hxw]
    have h2 := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [mul_assoc] using h2)
  have hww : w * w = 1 := by rw [← pow_two]; exact hW.2 w hwW
  have hmul : u' = w * u := by
    have h := IsKleinFour.eq_mul_of_ne_all (G := W) (x := ⟨w, hwW⟩) (y := ⟨u, huW⟩)
      (z := ⟨u', hu'W⟩) (fun h => hw1 (congrArg Subtype.val h))
      (fun h => hu1 (congrArg Subtype.val h)) (fun h => huw (congrArg Subtype.val h).symm)
      (fun h => hu'1 (congrArg Subtype.val h)) (fun h => hu'w (congrArg Subtype.val h))
      (fun h => hne (congrArg Subtype.val h))
    exact congrArg Subtype.val h
  have h2 : x * u' * x⁻¹ = u := by
    calc x * u' * x⁻¹ = x * (w * u) * x⁻¹ := by rw [hmul]
      _ = (x * w * x⁻¹) * (x * u * x⁻¹) := by group
      _ = w * (w * u) := by rw [hxw, ← hu', hmul]
      _ = u := by rw [← mul_assoc, hww, one_mul]
  have hx3' : x * x * x = 1 := by rw [← hx3, pow_succ, pow_two]
  have h3 : x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ = u' := by
    rw [← hu', h2, hu']
  have h4' : x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * u * (x * x * x)⁻¹ := by group
  rw [h4', hx3', one_mul, inv_one, mul_one] at h3
  exact hne h3.symm

end Four

section PCore

variable {Y : Type*} [Group Y]

theorem le_pCore_of_normal {p : ℕ} {K : Subgroup Y} (hK : K.Normal) (hp : IsPGroup p K) :
    K ≤ CFSG.pCore p Y :=
  le_sSup ⟨hK, hp⟩

theorem le_inSubgroup_pCore {p : ℕ} {R K : Subgroup Y} (hRK : R ≤ K) (hR : IsPGroup p R)
    (hKR : K ≤ normalizer (R : Set Y)) : R ≤ inSubgroup (CFSG.pCore p) K := by
  have hn : (R.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hRK).mpr hKR
  intro r hr
  exact ⟨⟨r, hRK hr⟩, le_pCore_of_normal hn hR.comap_subtype (mem_subgroupOf.mpr hr), rfl⟩

theorem inSubgroup_pCore_le_of_normalizer {p : ℕ} {H K : Subgroup Y} (hHK : H ≤ K)
    (hKN : K ≤ normalizer (H : Set Y)) :
    inSubgroup (CFSG.pCore p) H ≤ inSubgroup (CFSG.pCore p) K :=
  le_inSubgroup_pCore ((map_subtype_le _).trans hHK) (CFSG.pCore_isPGroup.map H.subtype)
    (hKN.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      _ _ inferInstance))

end PCore

theorem kleinFour_sq : ∀ v ∈ alternatingGroup.kleinFour (Fin 4), v ^ 2 = 1 := by
  intro v hv
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : alternatingGroup.kleinFour (Fin 4))
  rw [alternatingGroup.exponent_kleinFour_of_card_eq_four h4] at h
  exact congrArg Subtype.val h

theorem alt_four_fpf : ∀ x v : alternatingGroup (Fin 4), x ^ 3 = 1 → x ≠ 1 → v ^ 2 = 1 →
    v ≠ 1 → x * v ≠ v * x := by
  decide

section J2

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def oTwoN (e : X) : Subgroup X :=
  inSubgroup (CFSG.pCore 2) (normalizer (zpowers e : Set X))

omit [Finite X] in
theorem centralizer_le_normalizer_zpowers (e : X) :
    centralizer ({e} : Set X) ≤ normalizer (zpowers e : Set X) := by
  rw [zpowers_eq_closure, ← centralizer_closure]
  exact centralizer_le_normalizer _

theorem j2_mem_center_of_dvd (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    (P : Sylow 3 X) {B : Subgroup X} (hBP : B ≤ P) (hB9 : Nat.card B = 9) {d : X} (hdB : d ∈ B)
    (h27 : 27 ∣ Nat.card (centralizer ({d} : Set X))) :
    d ∈ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X) := by
  by_contra hdZ
  obtain ⟨-, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, ⟨e⟩, -⟩ := h4 B ⟨hBP, hB9⟩ d hdB hdZ
  have h72 : Nat.card (normalizer (zpowers d : Set X)) = 72 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Sec14.natCard_perm_fin_three,
      Sec14.natCard_alternatingGroup_fin_four]
  have h := h27.trans (h72 ▸ card_dvd_of_le (centralizer_le_normalizer_zpowers d))
  norm_num at h

theorem j2_mem_zpowers_of_mem_center (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {d w : X}
    (hd : d ∈ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X)) (hd1 : d ≠ 1)
    (hw : w ∈ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X)) : w ∈ zpowers d := by
  rcases KFacts.KS14.j2_mem_inf_centralizer_eq h415 hX P hd hd1 hw with h | h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact mem_zpowers d
  · rw [h]
    exact mul_mem (mem_zpowers d) (mem_zpowers d)

theorem j2_oTwoN (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    (P : Sylow 3 X) {B : Subgroup X} (hBP : B ≤ P) (hB9 : Nat.card B = 9) {e : X} (heB : e ∈ B)
    (heZ : e ∉ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X)) :
    (∀ w ∈ oTwoN e, w ^ 2 = 1) ∧ Nat.card (oTwoN e) = 4 ∧
      oTwoN e ≤ centralizer ({e} : Set X) ∧ B ≤ normalizer (oTwoN e : Set X) ∧
      ¬ B ≤ centralizer (oTwoN e : Set X) ∧
      (∀ U : Subgroup X, IsPGroup 2 U → U ≤ centralizer ({e} : Set X) →
        B ≤ normalizer (U : Set X) → U ≤ oTwoN e) ∧
      inSubgroup (CFSG.pCore 2) (normalizer (oTwoN e : Set X)) = oTwoN e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, -, hexp⟩ := hHeis
  obtain ⟨-, ⟨φ⟩, hO2, -⟩ := h4 B ⟨hBP, hB9⟩ e heB heZ
  have hpow3 : ∀ y ∈ (P : Subgroup X), y ^ 3 = 1 := by
    intro y hy
    have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  set N := normalizer (zpowers e : Set X) with hN
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := B)
      (by rw [hB9]; norm_num)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hBC : B ≤ centralizer ({e} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hBcomm x hx e heB)
  have hCN := centralizer_le_normalizer_zpowers e
  have hBN : B ≤ N := hBC.trans hCN
  have heN : e ∈ N := le_normalizer (mem_zpowers e)
  set B' := B.subgroupOf N with hB'
  set T := B'.map φ.toMonoidHom with hT
  have hT9 : Nat.card T = 9 := by
    rw [hT, card_map_of_injective φ.injective, hB',
      Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv, hB9]
  have h4' : Nat.card (Fin 4) = 4 := by simp
  have : (alternatingGroup.kleinFour (Fin 4)).Normal := alternatingGroup.normal_kleinFour h4'
  set V : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :=
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4)) with hV
  have hVcard : Nat.card V = 4 := by
    rw [hV, Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, card_bot, one_mul,
      alternatingGroup.kleinFour_card_of_card_eq_four h4']
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hnot3 : ∀ {Q : Type} [Group Q] [Finite Q] (K : Subgroup Q), IsPGroup 2 K →
      ¬ 3 ∣ Nat.card K := by
    intro Q _ _ K hK h3
    obtain ⟨k, hk⟩ := hK.exists_card_eq
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hpc : CFSG.pCore 2 (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) = V := by
    apply le_antisymm
    · refine Sec14.perm_three_prod_alternating_four_le (hnot3 _ CFSG.pCore_isPGroup) hT9 ?_
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    · exact le_pCore_of_normal inferInstance hV2
  have hW' : (CFSG.pCore 2 N).map φ.toMonoidHom = V := (CFSG.pCore_map_iso 2 φ).trans hpc
  have hmemV : ∀ w₀ : N, w₀ ∈ CFSG.pCore 2 N → φ w₀ ∈ V := fun w₀ hw₀ =>
    hW' ▸ mem_map_of_mem _ hw₀
  have hmemW : ∀ v ∈ V, ∃ w₀ ∈ CFSG.pCore 2 N, φ w₀ = v := by
    intro v hv
    rw [← hW'] at hv
    obtain ⟨w₀, hw₀, rfl⟩ := hv
    exact ⟨w₀, hw₀, rfl⟩
  have hWmem : ∀ w ∈ oTwoN e, ∃ w₀ ∈ CFSG.pCore 2 N, (w₀ : X) = w := by
    rintro _ ⟨w₀, hw₀, rfl⟩
    exact ⟨w₀, hw₀, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hO2⟩
  ·
    intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ := hWmem w hw
    have hv := hmemV w₀ hw₀
    have hsq : φ (w₀ ^ 2) = 1 := by
      rw [map_pow]
      obtain ⟨h1, h2⟩ := mem_prod.mp hv
      rw [mem_bot] at h1
      apply Prod.ext
      · rw [Prod.pow_fst, h1, one_pow]
        rfl
      · rw [Prod.pow_snd, kleinFour_sq _ h2]
        rfl
    rw [map_eq_one_iff φ φ.injective] at hsq
    rw [← coe_pow, hsq, coe_one]
  ·
    rw [oTwoN, inSubgroup, card_map_of_injective (subtype_injective _),
      ← card_map_of_injective (f := φ.toMonoidHom) φ.injective, hW', hVcard]
  ·
    intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ := hWmem w hw
    rw [mem_centralizer_singleton_iff]
    set e₀ : N := ⟨e, heN⟩ with he₀
    set x := w₀ * e₀ * w₀⁻¹ * e₀⁻¹ with hx
    have hx2 : x ∈ CFSG.pCore 2 N := by
      have h1 : e₀ * w₀⁻¹ * e₀⁻¹ ∈ CFSG.pCore 2 N :=
        (CFSG.pCore_normal (p := 2) (G := N)).conj_mem _ (inv_mem hw₀) e₀
      have h2 := mul_mem hw₀ h1
      simpa [hx, mul_assoc] using h2
    have hx3 : x ^ 3 = 1 := by
      have hconj : (w₀ : X) * e * (w₀ : X)⁻¹ ∈ zpowers e :=
        (mem_normalizer_iff.mp w₀.2 e).mp (mem_zpowers e)
      have he3 : e ^ 3 = 1 := hpow3 e (hBP heB)
      have hmem : (x : X) ∈ zpowers e := by
        have : (x : X) = (w₀ : X) * e * (w₀ : X)⁻¹ * e⁻¹ := by simp [hx, he₀]
        rw [this]
        exact mul_mem hconj (inv_mem (mem_zpowers e))
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      apply Subtype.ext
      rw [coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        show ((3 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, he3, one_zpow, coe_one]
    have hx1 : x = 1 := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := N)) ⟨x, hx2⟩
      have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hd1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hd2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
      have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
      exact orderOf_eq_one_iff.mp this
    have hwe : w₀ * e₀ = e₀ * w₀ := by
      have : w₀ * e₀ * w₀⁻¹ * e₀⁻¹ = 1 := hx1
      calc w₀ * e₀ = w₀ * e₀ * w₀⁻¹ * e₀⁻¹ * (e₀ * w₀) := by group
        _ = e₀ * w₀ := by rw [this, one_mul]
    exact congrArg Subtype.val hwe
  ·
    refine fun b hb =>
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        N (CFSG.pCore 2 N) inferInstance (le_normalizer (hBN hb))
  ·
    intro hBW
    obtain ⟨t, htT, ht2⟩ : ∃ t ∈ T, t.2 ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hle : T ≤ (MonoidHom.snd (Equiv.Perm (Fin 3)) (alternatingGroup (Fin 4))).ker :=
        fun t ht => hcon t ht
      have h6 : Nat.card (MonoidHom.snd (Equiv.Perm (Fin 3)) (alternatingGroup (Fin 4))).ker =
          6 := by
        rw [MonoidHom.ker_snd, Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
          card_top, card_bot, mul_one, Sec14.natCard_perm_fin_three]
      have h9 : 9 ∣ 6 := hT9 ▸ h6 ▸ card_dvd_of_le hle
      norm_num at h9
    obtain ⟨b₀, hb₀, rfl⟩ := htT
    have hb₀3 : b₀ ^ 3 = 1 := Subtype.ext (by
      rw [coe_pow]
      exact hpow3 _ (hBP (mem_subgroupOf.mp hb₀)))
    have ht3 : (φ b₀).2 ^ 3 = 1 := by
      rw [← Prod.pow_snd, ← map_pow, hb₀3, map_one]
      rfl
    obtain ⟨v, hvK, hv1⟩ : ∃ v ∈ alternatingGroup.kleinFour (Fin 4), v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : alternatingGroup.kleinFour (Fin 4) = ⊥ := eq_bot_iff.mpr fun v hv => hcon v hv
      have := alternatingGroup.kleinFour_card_of_card_eq_four h4'
      rw [hbot, card_bot] at this
      omega
    have hvV : ((1 : Equiv.Perm (Fin 3)), v) ∈ V := mem_prod.mpr ⟨one_mem _, hvK⟩
    obtain ⟨w₀, hw₀, hw₀v⟩ := hmemW _ hvV
    have hcomm : b₀ * w₀ = w₀ * b₀ := by
      have h1 := mem_centralizer_iff.mp (hBW (mem_subgroupOf.mp hb₀)) (w₀ : X)
        ⟨w₀, hw₀, rfl⟩
      exact Subtype.ext h1.symm
    have h2 := congrArg (fun y => (φ y).2) hcomm
    simp only [map_mul, Prod.snd_mul, hw₀v] at h2
    exact alt_four_fpf _ v ht3 ht2 (kleinFour_sq v hvK) hv1 h2
  ·
    intro U hU2 hUe hBU
    have hUN : U ≤ N := hUe.trans hCN
    have hU' : ¬ 3 ∣ Nat.card ((U.subgroupOf N).map φ.toMonoidHom) :=
      hnot3 _ (hU2.comap_subtype.map _)
    have hTU := (map_mono (Sec14.subgroupOf_le_normalizer_subgroupOf' (N := N) hBU)).trans
      (le_normalizer_map φ.toMonoidHom)
    have hle := Sec14.perm_three_prod_alternating_four_le hU' hT9 hTU
    intro u hu
    have hφu : φ ⟨u, hUN hu⟩ ∈ V := hle ⟨⟨u, hUN hu⟩, mem_subgroupOf.mpr hu, rfl⟩
    obtain ⟨w₀, hw₀, hw₀u⟩ := hmemW _ hφu
    have : w₀ = ⟨u, hUN hu⟩ := φ.injective hw₀u
    exact ⟨w₀, hw₀, by rw [this]; rfl⟩

theorem j2_exists_four (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    {B : Subgroup X} (hB9 : Nat.card B = 9) {d : X} (hdB : d ∈ B) (hd1 : d ≠ 1)
    (h27 : 27 ∣ Nat.card (centralizer ({d} : Set X))) {e : X} (heB : e ∈ B)
    (hed : e ∉ zpowers d) :
    CFSG.Assembly.IsElemAbelian 2 (oTwoN e) ∧ Nat.card (oTwoN e) = 4 ∧
      oTwoN e ≤ centralizer ({e} : Set X) ∧ B ≤ normalizer (oTwoN e : Set X) ∧
      ∀ w ∈ oTwoN e, d * w * d⁻¹ = w → w = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  obtain ⟨P, hBP⟩ := hB3.exists_le_sylow
  have hdZ := j2_mem_center_of_dvd h415 hX P hBP hB9 hdB h27
  have heZ : e ∉ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X) := fun h =>
    hed (j2_mem_zpowers_of_mem_center h415 hX P hdZ hd1 h)
  obtain ⟨hsq, h4, hWe, hBW, hnB, -, -⟩ := j2_oTwoN h415 hX P hBP hB9 heB heZ
  have hab := isElemAbelian_two_of_sq hsq
  refine ⟨hab, h4, hWe, hBW, fun w hw hdw => ?_⟩
  by_contra hw1
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, -, hexp⟩ := hHeis
  have hd3 : d ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨d, hBP hdB⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  have hdC : d ∈ centralizer (oTwoN e : Set X) := by
    rw [mem_centralizer_iff]
    intro u hu
    have := conj_eq_of_fix hab h4 (hBW hdB) hd3 hw hw1 hdw u hu
    calc u * d = d * u * d⁻¹ * d := by rw [this]
      _ = d * u := by group
  have heC : e ∈ centralizer (oTwoN e : Set X) := by
    rw [mem_centralizer_iff]
    intro u hu
    exact (mem_centralizer_singleton_iff.mp (hWe hu))
  apply hnB
  have hdcard : Nat.card (zpowers d) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hd3 hd1
  have hle : zpowers d ≤ B ⊓ centralizer (oTwoN e : Set X) :=
    zpowers_le.mpr ⟨hdB, hdC⟩
  have hdvd : Nat.card (B ⊓ centralizer (oTwoN e : Set X) : Subgroup X) ∣ 9 :=
    hB9 ▸ card_dvd_of_le inf_le_left
  have hge : 3 ≤ Nat.card (B ⊓ centralizer (oTwoN e : Set X) : Subgroup X) :=
    hdcard ▸ card_le_of_le hle
  have hcases : Nat.card (B ⊓ centralizer (oTwoN e : Set X) : Subgroup X) = 3 ∨
      Nat.card (B ⊓ centralizer (oTwoN e : Set X) : Subgroup X) = 9 := by
    have hpos : 0 < Nat.card (B ⊓ centralizer (oTwoN e : Set X) : Subgroup X) := Nat.card_pos
    have hle9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (B ⊓ centralizer (oTwoN e : Set X) : Subgroup X) <;> simp_all
  rcases hcases with h3 | h9
  · exfalso
    have heq : zpowers d = B ⊓ centralizer (oTwoN e : Set X) :=
      eq_of_le_of_card_ge hle (by rw [h3, hdcard])
    exact hed (heq ▸ ⟨heB, heC⟩)
  · have heq : B ⊓ centralizer (oTwoN e : Set X) = B :=
      eq_of_le_of_card_ge inf_le_left (by rw [h9, hB9])
    exact heq ▸ inf_le_right

theorem j2_pCore_centralizer_le (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    {B : Subgroup X} (hB9 : Nat.card B = 9) {d : X} (hdB : d ∈ B) (hd1 : d ≠ 1)
    (h27 : 27 ∣ Nat.card (centralizer ({d} : Set X))) {e : X} (heB : e ∈ B)
    (hed : e ∉ zpowers d) {U : Subgroup X} (hU2 : IsPGroup 2 U) (hU4 : Nat.card U = 4)
    (hUe : U ≤ centralizer ({e} : Set X)) (hBU : B ≤ normalizer (U : Set X)) :
    inSubgroup (CFSG.pCore 2) (centralizer (U : Set X)) ≤ U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  obtain ⟨P, hBP⟩ := hB3.exists_le_sylow
  have hdZ := j2_mem_center_of_dvd h415 hX P hBP hB9 hdB h27
  have heZ : e ∉ (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X) := fun h =>
    hed (j2_mem_zpowers_of_mem_center h415 hX P hdZ hd1 h)
  obtain ⟨-, h4, -, -, -, hmax, hO2⟩ := j2_oTwoN h415 hX P hBP hB9 heB heZ
  have hUW : U = oTwoN e :=
    eq_of_le_of_card_ge (hmax U hU2 hUe hBU) (by rw [h4, hU4])
  calc inSubgroup (CFSG.pCore 2) (centralizer (U : Set X))
      ≤ inSubgroup (CFSG.pCore 2) (normalizer (U : Set X)) :=
        inSubgroup_pCore_le_of_normalizer (centralizer_le_normalizer _)
          (KFacts.KS14.normalizer_le_normalizer_centralizer U)
    _ = U := by rw [hUW]; exact hO2

end J2

end CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof
