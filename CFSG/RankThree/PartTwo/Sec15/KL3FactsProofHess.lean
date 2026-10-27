module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofHess
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofCentGen
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.Sec17.Item17Res2ProofL3Two
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)
open Matrix

namespace KL3FactsProof

theorem conj_injective_of_center {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro z
  have h := congrArg (fun α : MulAut X => α z) ((MonoidHom.mem_ker).mp hy)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc z * y = (y * z * y⁻¹) * y := by rw [h]
    _ = y * z := by group

theorem inner_inf_centralizer_conj {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) (x : X) :
    OuterAutomorphisms.inner X ⊓ Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X)) =
      (Subgroup.centralizer ({x} : Set X)).map MulAut.conj := by
  have hinj := conj_injective_of_center hZ
  ext α
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply hinj
    rw [map_mul, map_mul]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]

theorem card_centralizer_conj_dvd {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (x : X) :
    Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X))) ∣
      Nat.card (Subgroup.centralizer ({x} : Set X)) * Nat.card (Outer X) := by
  have h2 : Nat.card (OuterAutomorphisms.inner X ⊓
      Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X)) : Subgroup (MulAut X)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) := by
    rw [inner_inf_centralizer_conj hZ x,
      Subgroup.card_map_of_injective (conj_injective_of_center hZ)]
  have h3 := Subgroup.relIndex_mul_card (OuterAutomorphisms.inner X)
    (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X)))
  have h4 : (OuterAutomorphisms.inner X).relIndex
      (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X))) ∣
      (OuterAutomorphisms.inner X).index := Subgroup.relIndex_dvd_index_of_normal _ _
  rw [← h3, h2, mul_comm]
  exact Nat.mul_dvd_mul_left _ h4

theorem conj_map_eq_mul {X : Type*} [Group X] (σ : MulAut X) (x : X) :
    MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem apply_eq_of_commute_conj {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    {σ : MulAut X} {x : X} (h : σ * MulAut.conj x = MulAut.conj x * σ) : σ x = x := by
  apply conj_injective_of_center hZ
  rw [conj_map_eq_mul, h, mul_inv_cancel_right]

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem card_centMod_diagTau (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Nat.card (centMod (slPi π 3 (p ^ f) K) (diagTau hτ)) = 3 * qSubPi π (p ^ f) ^ 2 := by
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have h1 := Subgroup.relIndex_mul_card (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ})
    (centMod (slPi π 3 (p ^ f) K) (diagTau hτ))
  rw [relindex_centralizer_diagTau hK hq hτ hτ1,
    inf_eq_left.mpr (centralizer_le_centMod _ _)] at h1
  obtain ⟨e⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card] at h1
  rw [← h1, sq]

theorem card_centralizer_mk_dvd {L : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K} (hy : y ∈ L)
    [Finite (GL (Fin 3) K)] :
    Nat.card (Subgroup.centralizer
      ({(⟨ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩ : projImage L)} : Set (projImage L))) ∣
      Nat.card (centMod L y) := by
  set yb : projImage L := ⟨ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩ with hyb
  let ρ : centMod L y →* projImage L :=
    { toFun := fun l => ⟨ProjGenLinGroup.mk (l : GL (Fin 3) K),
        ⟨l, (mem_centMod_iff_scalar.mp l.2).1, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hle : Subgroup.centralizer ({yb} : Set (projImage L)) ≤ ρ.range := by
    intro m hm
    obtain ⟨l, hl, hlm⟩ := m.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hm
    have hmem : l ∈ centMod L y := by
      refine mem_centMod_iff_scalar.mpr ⟨hl, l * y * l⁻¹ * y⁻¹, ?_, by group⟩
      have h1 : ProjGenLinGroup.mk (l * y * l⁻¹ * y⁻¹) = 1 := by
        have := congrArg Subtype.val hm
        simp only [Subgroup.coe_mul] at this
        have hyy : ProjGenLinGroup.mk y = (yb : ProjGenLinGroup (Fin 3) K) := rfl
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hlm, hyy, this, mul_inv_cancel_right,
          mul_inv_cancel]
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
      exact h1
    exact ⟨⟨l, hmem⟩, Subtype.ext hlm⟩
  calc Nat.card (Subgroup.centralizer ({yb} : Set (projImage L))) ∣ Nat.card ρ.range :=
        Subgroup.card_dvd_of_le hle
    _ ∣ Nat.card (centMod L y) := by
        rw [MonoidHom.range_eq_map]
        exact (Subgroup.card_map_dvd _ _).trans (by rw [Subgroup.card_top])

theorem card_centralizer_dvd_of_orderOf_eq_three (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h9 : ¬ 9 ∣ Nat.card K - 1)
    (x : projImage (slPi π 3 (p ^ f) K)) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set (projImage (slPi π 3 (p ^ f) K)))) ∣
      3 * qSubPi π (p ^ f) ^ 2 := by
  have := hK.finite
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y, hy, hxy⟩ := x.2
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hy3' : ProjGenLinGroup.mk y ^ 3 = 1 := by
    rw [hxy]
    exact congrArg Subtype.val hx3
  have hy3 : y ^ 3 = 1 := Sec16.ProofHess.pow_three_eq_one_of_lift hK h9 hy hy3'
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hyZ : y ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply hx1
    apply Subtype.ext
    rw [← hxy, Subgroup.coe_one, ProjGenLinGroup.mk_eq_one,
      GeneralLinearGroup.center_eq_range_scalar]
    exact (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
  have hyo : orderOf y = 3 := by
    refine orderOf_eq_prime hy3 fun h1 => hyZ ?_
    rw [h1]
    exact one_mem _
  obtain ⟨g, hg, hgy⟩ := rank3II_4_10_three hK hq hτ hτ1 hy hyZ hyo
  have hyg : y = g * diagTau hτ * g⁻¹ := by rw [← hgy]; group
  have hxeq : x = ⟨ProjGenLinGroup.mk y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hxy.symm
  have hcard : Nat.card (centMod (slPi π 3 (p ^ f) K) y) = 3 * qSubPi π (p ^ f) ^ 2 := by
    rw [hyg, ← map_conj_centMod hπ hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      card_centMod_diagTau hK hq hτ hτ1]
  rw [hxeq, ← hcard]
  exact card_centralizer_mk_dvd hy

theorem not_dvd_centralizer_conj_of_eq_one {X : Type} [Group X] [Finite X]
    (hiso : IsoLThreePi X 2 1) (x : X) (hx : orderOf x = 3) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) :
    ¬ r ∣ Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X))) := by
  classical
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (MulAut X) := Finite.of_injective (fun α : MulAut X => (α : X → X))
    fun a b h => MulEquiv.ext (congrFun h)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hSx⟩ := hxp.exists_le_sylow
  have hxS : x ∈ (S : Subgroup X) := hSx (Subgroup.mem_zpowers x)
  obtain ⟨h72, hS9, hS3, hSn, hC⟩ :=
    Sec17.Proof17Res2.u32_structure le_rfl hiso (by norm_num) S
  have hZ : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hzS : z ∈ (S : Subgroup X) :=
      hC x hxS hx1 z ((Subgroup.mem_center_iff.mp hz) x).symm
    have htop : (S : Subgroup X) = ⊤ := by
      rw [eq_top_iff]
      intro t _
      exact hC z hzS hz1 t (Subgroup.mem_center_iff.mp hz t)
    have h1 := congrArg (fun H : Subgroup X => Nat.card H) htop
    simp only [Subgroup.card_top, hS9, h72] at h1
    norm_num at h1
  obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X)))) r hdvd
  have hαc : (α : MulAut X) * MulAut.conj x = MulAut.conj x * α :=
    Subgroup.mem_centralizer_singleton_iff.mp α.2
  have hαx : (α : MulAut X) x = x := apply_eq_of_commute_conj hZ hαc
  have hαo : orderOf (α : MulAut X) = r := by rw [Subgroup.orderOf_coe, hα]
  have hαr : (α : MulAut X) ^ r = 1 := by
    rw [← hαo]
    exact pow_orderOf_eq_one _
  have hchar := Sylow.characteristic_of_normal S hSn
  have hαS : ∀ s ∈ (S : Subgroup X), (α : MulAut X) s ∈ (S : Subgroup X) := fun s hs =>
    (Subgroup.characteristic_iff_map_le.mp hchar (α : MulAut X)) ⟨s, hs, rfl⟩
  let fS : Function.End ↥(S : Subgroup X) := fun s => ⟨(α : MulAut X) s, hαS s s.2⟩
  have hfpow : ∀ (n : ℕ) (s : ↥(S : Subgroup X)),
      (((fS ^ n) s : ↥(S : Subgroup X)) : X) = ((α : MulAut X) ^ n) s := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, pow_succ, MulAut.mul_apply]
      change (((fS ^ n) (fS s) : ↥(S : Subgroup X)) : X) = _
      rw [ih]
  have hfr : fS ^ r ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hfpow, hαr]
    rfl
  set F := (S : Subgroup X) ⊓ (α : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X) with hF
  have hfix : Nat.card ↥(Function.fixedPoints fS) = Nat.card F := by
    refine Nat.card_congr ⟨fun s => ⟨s.1, s.1.2, ?_⟩, fun y => ⟨⟨y, y.2.1⟩, ?_⟩, ?_, ?_⟩
    · have := congrArg Subtype.val (s.2 : fS s.1 = s.1)
      exact this
    · exact Subtype.ext y.2.2
    · intro s
      rfl
    · intro y
      rfl
  have : Fintype ↥(S : Subgroup X) := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := r) (n := 1) hfr
  simp only [← Nat.card_eq_fintype_card] at hmod
  rw [hfix, hS9] at hmod
  have hFS : Nat.card F ∣ 9 := hS9 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hxF : Subgroup.zpowers x ≤ F := by
    rw [Subgroup.zpowers_le]
    exact ⟨hxS, hαx⟩
  have h3F : 3 ∣ Nat.card F := by
    have := Subgroup.card_dvd_of_le hxF
    rwa [Nat.card_zpowers, hx] at this
  have hF9 : Nat.card F = 9 := by
    obtain ⟨k, hk9, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card F ∣ 3 ^ 2 from hFS)
    interval_cases k
    · rw [hk] at h3F
      norm_num at h3F
    · exfalso
      rw [hk, pow_one] at hmod
      have h6 : r ∣ 2 * 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
      rcases (Nat.Prime.dvd_mul hr).mp h6 with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · have := Nat.le_of_dvd (by norm_num) h
        omega
    · rw [hk]
      norm_num
  have hFeq : F = (S : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hF9, hS9])
  have hαfix : ∀ s ∈ (S : Subgroup X), (α : MulAut X) s = s := fun s hs =>
    (hFeq ▸ hs : s ∈ F).2
  have hSab : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := (S : Subgroup X))
      (by rw [hS9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  obtain ⟨s, hs, hαs⟩ := Sec19.Item19ResProof.autCent_of_eq_two le_rfl hiso
    (by norm_num) (by norm_num) (by norm_num) S hS9 hSab α hαfix
  have h3 : (α : MulAut X) ^ 3 = 1 := by
    rw [hαs, ← map_pow, hS3 s hs, map_one]
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hαo] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

end KL3FactsProof

open KL3FactsProof

theorem ks1519HessCentAut : KS1519HessCentAut := by
  intro X _ _ f hf hiso h9 x hx r hr hr3 hdvd
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    exact (not_dvd_centralizer_conj_of_eq_one hiso x hx hr hr3 hdvd).elim
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut X) := Finite.of_injective (fun α : MulAut X => (α : X → X))
    fun a b h => MulEquiv.ext (congrFun h)
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model hf hiso
  have hZM := Sec13.center_projImage_slPi hK hq hq2
  have hZX : Subgroup.center X = ⊥ := by
    have h := OuterAutomorphisms.center_map_equiv ψ.symm
    rw [hZM, Subgroup.map_bot] at h
    exact h.symm
  have h1 := card_centralizer_conj_dvd hZX x
  have h2 : Nat.card (Subgroup.centralizer ({x} : Set X)) =
      Nat.card (Subgroup.centralizer ({ψ x} : Set (projImage (slPi π 3 (2 ^ f) K)))) := by
    rw [← KFacts.KP4.map_centralizer_singleton ψ x,
      Subgroup.card_map_of_injective ψ.injective]
  have h3 := card_centralizer_dvd_of_orderOf_eq_three hK hq
    (Proof1513Res3.not_nine_dvd_card_sub_one' hK h9) (ψ x)
    (by rw [MulEquiv.orderOf_eq]; exact hx)
  rw [h2] at h1
  have hdvd' := hdvd.trans (h1.trans (Nat.mul_dvd_mul_right h3 _))
  have hr2' : ¬ r ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hr3' : ¬ r ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  rcases hiso with ⟨h31, ⟨φ⟩⟩ | ⟨h32, ⟨φ⟩⟩
  ·
    have hπ : π = true := by
      cases π
      · change 2 ^ f % 3 = 2 at hq
        omega
      · rfl
    subst hπ
    have hOut : Nat.card (Outer X) ∣ 2 * f * Nat.gcd 3 (2 ^ f - 1) := by
      have e := φ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 f))
      rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
      exact higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two hf (le_refl 3)
        (GaloisField.card 2 f (by omega))
    have hall := hdvd'.trans (Nat.mul_dvd_mul_left _ hOut)
    have hsub : r ∣ 2 ^ f - 1 ∨ r ∣ f := by
      change r ∣ 3 * (2 ^ f - 1) ^ 2 * (2 * f * Nat.gcd 3 (2 ^ f - 1)) at hall
      rcases (Nat.Prime.dvd_mul hr).mp hall with h | h
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · exact absurd h hr3'
        · exact Or.inl (hr.dvd_of_dvd_pow h)
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
          · exact absurd h hr2'
          · exact Or.inr h
        · exact absurd (h.trans (Nat.gcd_dvd_left _ _)) hr3'
    rcases hsub with h | h
    · left
      have hsign : sign1519 f r = 1 := by
        rw [sign1519, ite_eq_left_iff.mpr (fun h => absurd h31 h)]
      rw [hsign]
      have h1' : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have := (ZMod.natCast_eq_zero_iff _ r).mpr h
      rw [Nat.cast_sub h1', Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at this
      exact this
    · exact Or.inr h
  ·
    have hπ : π = false := by
      cases π
      · rfl
      · change 2 ^ f % 3 = 1 at hq
        omega
    subst hπ
    have hOut : Nat.card (Outer X) ∣ 2 * f * (2 ^ f + 1) := by
      rw [Nat.card_congr (OuterAutomorphisms.equivalence φ).toEquiv]
      refine card_outer_projSU_dvd 3 2 f hf (le_refl 3) ?_
      rintro ⟨-, h⟩
      omega
    have hall := hdvd'.trans (Nat.mul_dvd_mul_left _ hOut)
    have hsub : r ∣ 2 ^ f + 1 ∨ r ∣ f := by
      change r ∣ 3 * (2 ^ f + 1) ^ 2 * (2 * f * (2 ^ f + 1)) at hall
      rcases (Nat.Prime.dvd_mul hr).mp hall with h | h
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · exact absurd h hr3'
        · exact Or.inl (hr.dvd_of_dvd_pow h)
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
          · exact absurd h hr2'
          · exact Or.inr h
        · exact Or.inl h
    rcases hsub with h | h
    · left
      have hsign : sign1519 f r = -1 := by
        simp only [sign1519, show ¬ (2 ^ f % 3 = 1) by omega, ↓reduceIte]
      rw [hsign]
      have := (ZMod.natCast_eq_zero_iff _ r).mpr h
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, add_eq_zero_iff_eq_neg] at this
      exact this
    · exact Or.inr h

theorem step1519CentAut_of_y0E9' (hD : Step1519Y0E9) : Step1519CentAut :=
  step1519CentAut_of_y0E9 hD ks1519HessCentAut

end CFSG.RankThree.PartTwo.Sec15
