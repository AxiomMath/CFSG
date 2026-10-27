module

public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenAvoid
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusRoot2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open SpCoord

theorem ggKGRootDatumAt_omPlusTorus
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} (hm : 4 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    GGKGRootDatumAt p (omPlusTorus (m := m) hζ).range := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpq : p ∣ Nat.card K - 1 := by
    have h : orderOf ζ ∣ Nat.card Kˣ := orderOf_dvd_natCard ζ
    rwa [hζo, Nat.card_units] at h
  have hK : 4 ≤ Nat.card K := by
    have h1 : p ≤ Nat.card K - 1 := Nat.le_of_dvd (by
      have h2K : 2 ≤ Nat.card K := by
        haveI : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega) hpq
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hτ : Function.Injective (omPlusTorus (m := m) hζ) := by
    intro x y h
    apply omPlusTorusGL_injective hζ hζo
    simpa only [coe_omPlusTorus] using congrArg Subtype.val h
  have hW : ∀ x : OmPlusIdx m, ∃ w : StatedOmega (StatedQuadPlus m K),
      w ∈ (omPlusBlock K x).subgroupOf (StatedOmega (StatedQuadPlus m K)) ∧
      ∀ f, w * omPlusTorus hζ f * w⁻¹ = omPlusTorus hζ (omPlusRefl p x f) := by
    intro x
    obtain ⟨w, hw, hwx⟩ := exists_mem_omPlusBlock_conj (K := K) (m := m) (p := p) hζ x
    exact ⟨⟨w, omPlusBlock_le hK x hw⟩, Subgroup.mem_subgroupOf.mpr hw,
      fun f => Subtype.ext (hwx f)⟩
  choose w hwS hwconj using hW
  refine RealKGModelRoot.ggKGRootDatumAt_of_model (R := StatedOmega (StatedQuadPlus m K))
    (k := m) hp hτ rfl w (fun x => omPlusRefl p x)
    (fun x => (omPlusBlock K x).subgroupOf (StatedOmega (StatedQuadPlus m K)))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro x f
    exact hwconj x f
  · intro x
    exact hwS x
  · intro x
    exact isComponentOf_omPlusBlock hK hp hp2 hζ hζo x
  · intro x
    exact dvd_card_omPlusBlock hK hpq x
  · intro g u huact hu2 hcard
    have husp : IsSignedPerm ⇑u := ggKGOmR_isSignedPerm hp hζ hζo g u huact
    rcases RealKGSignedRefl.signedRefl_cases hp hp2 husp hu2 hcard with ⟨a, ha⟩ | ⟨x, hx⟩
    · exfalso
      rw [ha] at huact
      exact ggKGOmR_not_sgnAut hm hp hp2 hζ hζo a ⟨g, huact⟩
    · exact ⟨x, hx.symm⟩
  · intro a ha J hJperf hJa
    obtain ⟨f, rfl⟩ := ha
    refine ggKG_layer_of_chevSimple (R := StatedOmega (StatedQuadPlus m K))
      (ggKGOmR_isSimple (K := K) (m := m) hm)
      (ggKGOmR_nonabelian (K := K) (m := m) hm)
      (ggKGOmR_isChevSimple (K := K) (m := m) hm) hp hp2 ?_ hJperf hJa
    rw [← map_pow, ReflInner.pow_eq_one_of_zmod, map_one]

theorem ggKGRootDatum_statedOmegaPlus
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} (hm : 4 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGKGRootDatum p m (StatedOmega (StatedQuadPlus m K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units (α := K)]; exact hpq)
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  intro E hEab h3 hmE hsc
  obtain ⟨α, hα⟩ := exists_mulEquiv_eq_map_omPlusTorus (K := K) (m := m) hp2 hζ hζo
    (E := E) hEab hmE
  have hroot := ggKGRootDatumAt_omPlusTorus (m := m) hm hp hp2 hζo hζ
  refine ggKGRootDatumAt_of_mulEquiv α.symm ?_
  rw [hα, Subgroup.map_map]
  simpa using hroot

end CFSG.StandardType
