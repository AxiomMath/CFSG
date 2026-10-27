module

public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Multiplicative
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

private def ggKGUl1_hypEntries {p r : ℕ} {K : Type} [Field K] (ζ : K)
    (t : Fin r → ZMod p) : HypIndex r 1 → K
  | .inl i => ζ ^ (t i).val
  | .inr (.inl _) => 1
  | .inr (.inr i) => (ζ ^ (t i).val)⁻¹

private theorem ggKGUl1_hypEntries_add {r p : ℕ} {K : Type} [Field K] {ζ : K}
    (hp : p.Prime) (hpow : ζ ^ p = 1) (t t' : Fin r → ZMod p) :
    ggKGUl1_hypEntries (r := r) ζ (t + t') =
      ggKGUl1_hypEntries ζ t * ggKGUl1_hypEntries ζ t' := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  funext x
  rcases x with i | k | i
  · simp only [ggKGUl1_hypEntries, Pi.add_apply, Pi.mul_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hpow, pow_add]
  · simp [ggKGUl1_hypEntries]
  · simp only [ggKGUl1_hypEntries, Pi.add_apply, Pi.mul_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hpow, pow_add, mul_inv]

private theorem ggKGUl1_exists_hypTorusHom {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hbar : h.bar ζ = ζ) :
    ∃ ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 1, ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal (ggKGUl1_hypEntries ζ t) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hbar_pow : ∀ m : ℕ, h.bar (ζ ^ m) = ζ ^ m := fun m => by rw [map_pow, hbar]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  let a : (Fin r → ZMod p) → Fin r → Kˣ :=
    fun t i => Units.mk0 (ζ ^ (t i).val) (pow_ne_zero _ hζ0)
  let d0 : Fin 1 → Kˣ := fun _ => 1
  have hd : ∀ k : Fin 1, h.norm (d0 k : K) = 1 := fun k => by
    simp [d0, UnitaryFieldData.norm]
  have hratio : ∀ t, torusRatio h (a t) d0 = 1 := by
    intro t
    have hprod : (∏ i, (a t i : K) / h.bar (a t i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hb : h.bar (a t i : K) = (a t i : K) := by
        rw [Units.val_mk0]
        exact hbar_pow _
      rw [hb]
      exact div_self (by rw [Units.val_mk0]; exact pow_ne_zero _ hζ0)
    rw [torusRatio, hprod, Finset.prod_eq_one (fun k _ => by simp [d0]), mul_one]
  have hex : ∀ t : Fin r → ZMod p, ∃ g : hypSU h r 1,
      (((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
        diagonal (ggKGUl1_hypEntries ζ t)) := by
    intro t
    obtain ⟨g, -, hg⟩ := torusMat_mem_hypSU (d := d0) h (a t) hd (hratio t)
    refine ⟨g, ?_⟩
    rw [hg]
    congr 1
    funext x
    rcases x with i | k | i
    · simp [torusEntries, ggKGUl1_hypEntries, a]
    · simp [torusEntries, ggKGUl1_hypEntries, d0]
    · simp [torusEntries, ggKGUl1_hypEntries, a, hbar_pow]
  let g : (Fin r → ZMod p) → hypSU h r 1 := fun t => Classical.choose (hex t)
  have hg : ∀ t : Fin r → ZMod p,
      (((g t : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal (ggKGUl1_hypEntries ζ t) :=
    fun t => Classical.choose_spec (hex t)
  have hmul : ∀ t t' : Fin r → ZMod p, g (t + t') = g t * g t' := by
    intro t t'
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hg, hg, hg, diagonal_mul_diagonal,
      ggKGUl1_hypEntries_add hp hζ.pow_eq_one]
    rfl
  refine ⟨MonoidHom.mk' (fun m : Multiplicative (Fin r → ZMod p) =>
    g (Multiplicative.toAdd m)) ?_, ?_⟩
  · intro m m'
    exact hmul (Multiplicative.toAdd m) (Multiplicative.toAdd m')
  · intro t
    exact hg t

private theorem ggKGUl1_card_range_hypTorusHom {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 1)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal (ggKGUl1_hypEntries ζ t)) :
    Nat.card ι.range = p ^ r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hker : ∀ t : Fin r → ZMod p, ι (ofAdd t) = 1 → t = 0 := by
    intro t ht
    funext i
    have hmat : diagonal (ggKGUl1_hypEntries ζ t) =
        (1 : Matrix (HypIndex r 1) (HypIndex r 1) K) := by
      have h1 := (hι t).symm
      rw [ht] at h1
      simpa using h1
    have hentry := congrFun (congrFun hmat (.inl i)) (.inl i)
    simp only [ggKGUl1_hypEntries, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hentry
    have hpow : ζ ^ (t i).val = 1 := by simpa using hentry
    exact (ZMod.val_eq_zero (t i)).mp
      (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd _).mp hpow) (ZMod.val_lt (t i)))
  have hinj : Function.Injective ι := by
    intro x y hxy
    have hz : ι (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hzt : (x * y⁻¹).toAdd = 0 := by
      rw [← ofAdd_toAdd (x * y⁻¹)] at hz
      exact hker _ hz
    rw [toAdd_mul, toAdd_inv] at hzt
    rw [← sub_eq_add_neg] at hzt
    exact Multiplicative.toAdd.injective (sub_eq_zero.mp hzt)
  have hcard : Nat.card ι.range = Nat.card (Multiplicative (Fin r → ZMod p)) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
  simp [Nat.card_zmod, Finset.prod_const]

private theorem ggKGUl1_hypTorus_inf_hypScalars {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 1)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 1) : GL (HypIndex r 1) K) :
        Matrix (HypIndex r 1) (HypIndex r 1) K) = diagonal (ggKGUl1_hypEntries ζ t)) :
    ι.range ⊓ hypScalars h r 1 = ⊥ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [eq_bot_iff]
  rintro x ⟨hx, hxs⟩
  rw [Subgroup.mem_bot]
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨c, -, -, hg⟩ := hxs
  have hg' : (ι (ofAdd (Multiplicative.toAdd m)) : GL (HypIndex r 1) K) =
      GeneralLinearGroup.scalar (HypIndex r 1) c := by
    rwa [ofAdd_toAdd]
  have hmat : diagonal (ggKGUl1_hypEntries ζ (Multiplicative.toAdd m)) =
      Matrix.scalar (HypIndex r 1) (c : K) := by
    rw [← hι (Multiplicative.toAdd m), hg', GeneralLinearGroup.coe_scalar]
  have ht : Multiplicative.toAdd m = 0 := by
    funext i
    have h1 := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
    have h2 := congrFun (congrFun hmat (Sum.inr (Sum.inr i))) (Sum.inr (Sum.inr i))
    simp only [ggKGUl1_hypEntries, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h1 h2
    have hpoweq : ζ ^ ((Multiplicative.toAdd m) i).val =
        (ζ ^ ((Multiplicative.toAdd m) i).val)⁻¹ := h1.trans h2.symm
    have hsq : (ζ ^ ((Multiplicative.toAdd m) i).val) ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun x => ζ ^ ((Multiplicative.toAdd m) i).val * x) hpoweq).trans
        (mul_inv_cancel₀ (pow_ne_zero _ (hζ.ne_zero hp.ne_zero)))
    have h2mul : ζ ^ (2 * ((Multiplicative.toAdd m) i).val) = 1 := by
      rw [mul_comm 2, pow_mul, hsq]
    have hdvd : p ∣ 2 * ((Multiplicative.toAdd m) i).val :=
      (hζ.pow_eq_one_iff_dvd _).mp h2mul
    have hp2' : ¬ p ∣ 2 := by
      intro hdiv
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
      · exact hp.one_lt.ne' h
      · exact hp2 h
    have hpdvd : p ∣ ((Multiplicative.toAdd m) i).val := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact absurd h hp2'
      · exact h
    exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hpdvd (ZMod.val_lt _))
  rw [← ofAdd_toAdd m, ht, ofAdd_zero]
  exact map_one ι

private theorem ggKGUl1_hypUnitriangular_not_le_hypScalars {n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ¬ hypUnitriangular h r 1 ≤ hypScalars h r 1 := by
  intro hle
  have hbot : hypUnitriangular h r 1 = ⊥ := by
    rw [← inf_eq_left.mpr hle, hypUnitriangular_inf_hypScalars h hr le_rfl]
  have hcard := card_hypUnitriangular h (r := r) (ε := 1) le_rfl
  rw [hbot, Subgroup.card_bot] at hcard
  have hexp : 0 < (2 * r + 1) * (2 * r + 1 - 1) / 2 := by
    have hprod : 2 ≤ (2 * r + 1) * (2 * r + 1 - 1) := by
      calc 2 = 2 * 1 := by norm_num
        _ ≤ (2 * r + 1) * (2 * r + 1 - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos hprod (by norm_num)
  have hbase : 1 < 2 ^ n := one_lt_pow' (by norm_num : (1 : ℕ) < 2) (by omega)
  have hlt : 1 < (2 ^ n) ^ ((2 * r + 1) * (2 * r + 1 - 1) / 2) :=
    one_lt_pow' hbase (ne_of_gt hexp)
  omega

theorem ggTorusLift_unitarySplit_odd
    {K : Type} [Field K] [Finite K] {n r p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusLift p r (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n))) := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 1) h
  set H := unitarySU 2 n K (2 * r + 1) with hH
  haveI : Finite H := Finite.of_injective
    (fun x : H => ((x : GL (Fin (2 * r + 1)) K) : Matrix (Fin (2 * r + 1)) (Fin (2 * r + 1)) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  set e := hypTransport h hR with he
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbarζ : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := ggKGUl1_exists_hypTorusHom (r := r) h hp hζ hbarζ
  have hapow : ∀ a : Multiplicative (Fin r → ZMod p), a ^ p = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    simp [Pi.smul_apply, nsmul_eq_mul]
  set E₀' : Subgroup (hypSU h r 1) := ι.range with hE₀'def
  have hE₀'ab : CFSG.Open.IsElemAbelian p E₀' := by
    rw [hE₀'def]
    exact isElemAbelian_range (fun a b => mul_comm a b) hapow ι
  have hE₀'card : Nat.card E₀' = p ^ r := by
    rw [hE₀'def]
    exact ggKGUl1_card_range_hypTorusHom h hp hζ ι hι
  have hE₀'hyp : E₀' ⊓ hypScalars h r 1 = ⊥ := by
    rw [hE₀'def]
    exact ggKGUl1_hypTorus_inf_hypScalars h hp hp2 hζ ι hι
  set U₀' : Subgroup (hypSU h r 1) := hypUnitriangular h r 1 with hU₀'def
  have hU₀'2 : IsPGroup 2 U₀' := by
    rw [hU₀'def]
    refine IsPGroup.of_card (n := n * ((2 * r + 1) * (2 * r + 1 - 1) / 2)) ?_
    rw [card_hypUnitriangular h (r := r) (ε := 1) le_rfl, ← pow_mul]
  have hU₀'hypScal : ¬ U₀' ≤ hypScalars h r 1 := by
    rw [hU₀'def]
    exact ggKGUl1_hypUnitriangular_not_le_hypScalars h hn hr
  have hE₀'B : E₀' ≤ hypBorel h r 1 := by
    intro x hx
    rw [hE₀'def] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [← ofAdd_toAdd m]
    refine mem_hypBorel_of_blockTriangular h ?_
    rw [hι (Multiplicative.toAdd m)]
    exact Matrix.blockTriangular_diagonal _
  have hBn : hypBorel h r 1 ≤ Subgroup.normalizer (U₀' : Set (hypSU h r 1)) := by
    rw [hU₀'def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).mp
      (normal_hypUnitriangular (h := h) (r := r) (ε := 1) le_rfl)
  have hEU' : E₀' ≤ Subgroup.normalizer (U₀' : Set (hypSU h r 1)) := hE₀'B.trans hBn
  set E₀ : Subgroup H := E₀'.map e.toMonoidHom with hE₀def
  set U₀ : Subgroup H := U₀'.map e.toMonoidHom with hU₀def
  have hE₀ab : CFSG.Open.IsElemAbelian p E₀ := by
    rw [hE₀def]
    exact CFSG.SectionRank.isElemAbelian_map hE₀'ab e.toMonoidHom
  have hE₀card : Nat.card E₀ = p ^ r := by
    rw [hE₀def, Subgroup.card_map_of_injective e.injective, hE₀'card]
  have hU₀ : IsPGroup 2 U₀ := by
    rw [hU₀def]
    exact hU₀'2.map e.toMonoidHom
  have hEU : E₀ ≤ Subgroup.normalizer (U₀ : Set H) := by
    rw [hE₀def, hU₀def]
    exact (Subgroup.map_mono hEU').trans (Subgroup.le_normalizer_map e.toMonoidHom)
  set q := LargeEvenProjMk H with hq
  have hkerq : q.ker = (LargeEvenScalars (Fin (2 * r + 1)) K).subgroupOf H :=
    QuotientGroup.ker_mk' _
  have hqker : (q.comp e.toMonoidHom).ker = hypScalars h r 1 := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hkerq,
      Subgroup.mem_subgroupOf, mem_hypScalars_iff_transport hR y, unitaryScalars_eq h (by omega),
      Subgroup.mem_subgroupOf]
    rfl
  have hmap : ((q.comp e.toMonoidHom).ker).map e.toMonoidHom = q.ker := by
    rw [show (q.comp e.toMonoidHom).ker = Subgroup.comap e.toMonoidHom q.ker from
      MonoidHom.comap_ker q e.toMonoidHom]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective q.ker
  have hE₀q : E₀ ⊓ q.ker = ⊥ := by
    rw [hE₀def]
    calc E₀'.map e.toMonoidHom ⊓ q.ker
        = E₀'.map e.toMonoidHom ⊓ ((q.comp e.toMonoidHom).ker).map e.toMonoidHom := by
          rw [hmap]
      _ = (E₀' ⊓ (q.comp e.toMonoidHom).ker).map e.toMonoidHom :=
          (Subgroup.map_inf_eq E₀' _ e.toMonoidHom e.injective).symm
      _ = (E₀' ⊓ hypScalars h r 1).map e.toMonoidHom := by rw [hqker]
      _ = ⊥ := by rw [hE₀'hyp, Subgroup.map_bot]
  have hU₀q : ¬ U₀ ≤ q.ker := by
    intro hle
    have hsub : U₀' ≤ (q.comp e.toMonoidHom).ker := by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact hle (by rw [hU₀def]; exact ⟨u, hu, rfl⟩)
    rw [hqker] at hsub
    exact hU₀'hypScal hsub
  have hdq : (2 * r + 1, 2 ^ n) ≠ (3, 2) := by
    rintro h0
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h0
    have hnle : n ≤ 1 := by
      by_contra hlt
      have h2le : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [h2] at h2le
      norm_num at h2le
    have hn1 : n = 1 := by omega
    rw [hn1] at hpq
    norm_num at hpq
    have hp2le : 2 ≤ p := hp.two_le
    omega
  have ho : ¬ Even (2 * r + 1) := by
    rintro ⟨k, hk⟩
    omega
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen _
    exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn (by omega) ho hdq hπ hcen
  intro L' _ _ ψ hψ hker _
  obtain ⟨U, E, hU, hU2, hEU', hEab, hEc, hEk⟩ :=
    TableBU.exists_lift_of_section q hsplit hp hp2 hE₀ab hE₀q hU₀ hU₀q hEU ψ hψ hker
  exact ⟨U, E, hU, hU2, hEU', hEab, hEc.trans hE₀card, hEk⟩

end CFSG.StandardType

end
