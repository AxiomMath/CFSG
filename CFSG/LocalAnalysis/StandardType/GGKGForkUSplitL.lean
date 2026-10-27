module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypEigen
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Multiplicative
open Matrix CFSG.ClassicalGroups.UnitaryFlag

private theorem ggKGUl_hypTorus_inf_hypScalars {n r p : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (ι : Multiplicative (Fin r → ZMod p) →* hypSU h r 0)
    (hι : ∀ t : Fin r → ZMod p,
      (((ι (ofAdd t) : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ t)) :
    ι.range ⊓ hypScalars h r 0 = ⊥ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [eq_bot_iff]
  rintro x ⟨hx, hxs⟩
  rw [Subgroup.mem_bot]
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨c, -, -, hg⟩ := hxs
  have hg' : (ι (ofAdd (Multiplicative.toAdd m)) : GL (HypIndex r 0) K) =
      GeneralLinearGroup.scalar (HypIndex r 0) c := by
    rwa [ofAdd_toAdd]
  have hmat : diagonal (hypEntries ζ (Multiplicative.toAdd m)) =
      Matrix.scalar (HypIndex r 0) (c : K) := by
    rw [← hι (Multiplicative.toAdd m), hg', GeneralLinearGroup.coe_scalar]
  have ht : Multiplicative.toAdd m = 0 := by
    funext i
    have h1 := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
    have h2 := congrFun (congrFun hmat (Sum.inr (Sum.inr i))) (Sum.inr (Sum.inr i))
    simp only [hypEntries, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h1 h2
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

private theorem ggKGUl_hypUnitriangular_not_le_hypScalars {n r : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ¬ hypUnitriangular h r 0 ≤ hypScalars h r 0 := by
  intro hle
  have hbot : hypUnitriangular h r 0 = ⊥ := by
    rw [← inf_eq_left.mpr hle, hypUnitriangular_inf_hypScalars h hr (by norm_num)]
  have hcard := card_hypUnitriangular h (r := r) (ε := 0) (by norm_num)
  rw [hbot, Subgroup.card_bot] at hcard
  have hexp : 0 < (2 * r + 0) * (2 * r + 0 - 1) / 2 := by
    have hprod : 2 ≤ (2 * r + 0) * (2 * r + 0 - 1) := by
      calc 2 = 2 * 1 := by norm_num
        _ ≤ (2 * r + 0) * (2 * r + 0 - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos hprod (by norm_num)
  have hbase : 1 < 2 ^ n := one_lt_pow' (by norm_num : (1 : ℕ) < 2) (by omega)
  have hlt : 1 < (2 ^ n) ^ ((2 * r + 0) * (2 * r + 0 - 1) / 2) :=
    one_lt_pow' hbase (ne_of_gt hexp)
  omega

theorem ggTorusLift_unitarySplit_even
    {K : Type} [Field K] [Finite K] {n r p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusLift p r (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n))) := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 0) h
  set H := unitarySU 2 n K (2 * r) with hH
  haveI : Finite H := Finite.of_injective
    (fun x : H => ((x : GL (Fin (2 * r)) K) : Matrix (Fin (2 * r)) (Fin (2 * r)) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  set e := hypTransport h hR with he
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbarζ : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := r) h hp hζ hbarζ
  have hapow : ∀ a : Multiplicative (Fin r → ZMod p), a ^ p = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    simp [Pi.smul_apply, nsmul_eq_mul]
  set E₀' : Subgroup (hypSU h r 0) := ι.range with hE₀'def
  have hE₀'ab : CFSG.Open.IsElemAbelian p E₀' := by
    rw [hE₀'def]
    exact isElemAbelian_range (fun a b => mul_comm a b) hapow ι
  have hE₀'card : Nat.card E₀' = p ^ r := by
    rw [hE₀'def]
    exact card_range_hypTorusHom h hp hζ ι hι
  have hE₀'hyp : E₀' ⊓ hypScalars h r 0 = ⊥ := by
    rw [hE₀'def]
    exact ggKGUl_hypTorus_inf_hypScalars h hp hp2 hζ ι hι
  set U₀' : Subgroup (hypSU h r 0) := hypUnitriangular h r 0 with hU₀'def
  have hU₀'2 : IsPGroup 2 U₀' := by
    rw [hU₀'def]
    refine IsPGroup.of_card (n := n * ((2 * r + 0) * (2 * r + 0 - 1) / 2)) ?_
    rw [card_hypUnitriangular h (r := r) (ε := 0) (by norm_num), ← pow_mul]
  have hU₀'hypScal : ¬ U₀' ≤ hypScalars h r 0 := by
    rw [hU₀'def]
    exact ggKGUl_hypUnitriangular_not_le_hypScalars h hn (by omega)
  have hE₀'B : E₀' ≤ hypBorel h r 0 := by
    intro x hx
    rw [hE₀'def] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [← ofAdd_toAdd m]
    refine mem_hypBorel_of_blockTriangular h ?_
    rw [hι (Multiplicative.toAdd m)]
    exact Matrix.blockTriangular_diagonal _
  have hBn : hypBorel h r 0 ≤ Subgroup.normalizer (U₀' : Set (hypSU h r 0)) := by
    rw [hU₀'def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).mp
      (normal_hypUnitriangular (h := h) (r := r) (ε := 0) (by norm_num))
  have hEU' : E₀' ≤ Subgroup.normalizer (U₀' : Set (hypSU h r 0)) := hE₀'B.trans hBn
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
  have hkerq : q.ker = (LargeEvenScalars (Fin (2 * r)) K).subgroupOf H := QuotientGroup.ker_mk' _
  have hqker : (q.comp e.toMonoidHom).ker = hypScalars h r 0 := by
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
      _ = (E₀' ⊓ hypScalars h r 0).map e.toMonoidHom := by rw [hqker]
      _ = ⊥ := by rw [hE₀'hyp, Subgroup.map_bot]
  have hU₀q : ¬ U₀ ≤ q.ker := by
    intro hle
    have hsub : U₀' ≤ (q.comp e.toMonoidHom).ker := by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact hle (by rw [hU₀def]; exact ⟨u, hu, rfl⟩)
    rw [hqker] at hsub
    exact hU₀'hypScal hsub
  have hdq : (2 * r, 2 ^ n) ≠ (3, 2) := fun h0 => by
    have h1 : 2 * r = 3 := congrArg Prod.fst h0
    omega
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even (2 * r)
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn (by omega) he hdq hπ hcen
  intro L' _ _ ψ hψ hker _
  obtain ⟨U, E, hU, hU2, hEU', hEab, hEc, hEk⟩ :=
    TableBU.exists_lift_of_section q hsplit hp hp2 hE₀ab hE₀q hU₀ hU₀q hEU ψ hψ hker
  exact ⟨U, E, hU, hU2, hEU', hEab, hEc.trans hE₀card, hEk⟩

end CFSG.StandardType
