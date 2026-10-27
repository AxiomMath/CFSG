module

public import CFSG.RankThree.PartOne.KGD.D4T36PerX
public import CFSG.RankThree.PartOne.KGD.D4T36Gen
public import CFSG.RankThree.PartOne.KGD.D4QPlane
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley.TrialityFold
open scoped Matrix MatrixGroups Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Aux

theorem card_fixSubfield_cube {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  have hσfr : σ = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ = 3 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 3 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  obtain ⟨-, hσcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ
    (by omega : 1 ≤ 3 * f) hK3 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  exact hσcard

theorem exists_prime_dvd_sq_add_one {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Q ^ 2 + 1 := by
  have h3 : ¬ 3 ∣ Q ^ 2 + 1 := by
    intro h
    have h' : (Q ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have hQ3 : Q % 3 = 0 ∨ Q % 3 = 1 ∨ Q % 3 = 2 := by omega
    rcases hQ3 with h0 | h0 | h0 <;> simp [Nat.add_mod, Nat.pow_mod, h0] at h'
  obtain ⟨m, hmo, hm3, hmd⟩ : ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ m ∣ Q ^ 2 + 1 := by
    by_cases he : Even Q
    · refine ⟨Q ^ 2 + 1, ?_, ?_, dvd_rfl⟩
      · exact (Even.pow_of_ne_zero he (by norm_num : (2 : ℕ) ≠ 0)).add_one
      · nlinarith
    · obtain ⟨t, rfl⟩ := Nat.not_even_iff_odd.1 he
      refine ⟨2 * t ^ 2 + 2 * t + 1, ⟨t ^ 2 + t, by ring⟩, ?_, ⟨2, by ring⟩⟩
      have : 1 ≤ t := by omega
      nlinarith
  have hm1 : m ≠ 1 := by omega
  have hr := Nat.minFac_prime hm1
  have hrm : m.minFac ∣ m := Nat.minFac_dvd m
  refine ⟨m.minFac, hr, ?_, hrm.trans hmd⟩
  have hr2 : m.minFac ≠ 2 := by
    intro h2
    rw [h2] at hrm
    exact (Nat.not_even_iff_odd.2 hmo) (even_iff_two_dvd.2 hrm)
  have hr3 : m.minFac ≠ 3 := by
    intro h3'
    rw [h3'] at hrm
    exact h3 (hrm.trans hmd)
  have := hr.two_le
  by_contra hle
  interval_cases hrr : m.minFac
  · exact hr2 rfl
  · exact hr3 rfl

theorem odd_card_of_map_le {G H : Type*} [Group G] [Group H] (ψ : G →* H)
    (hψ : Function.Injective ψ) (V : Subgroup G) (T : Subgroup H) [Finite T]
    (hVT : ∀ v ∈ V, ψ v ∈ T) (hT : Odd (Nat.card T)) : Odd (Nat.card V) := by
  have h1 : Nat.card (V.map ψ) = Nat.card V := Subgroup.card_map_of_injective hψ
  have h2 : V.map ψ ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    exact hVT v hv
  rw [← h1]
  exact Odd.of_dvd_nat hT (Subgroup.card_dvd_of_le h2)

theorem d4T36_torus_card_odd {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ]
    [IsAlgClosed L] (hf : 1 ≤ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (w : WeylGroup TwistTag.D4.tag) (hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) :
    Odd (Nat.card (twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))) := by
  have hℓ : ℓ.Prime := Fact.out
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  rw [twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) hn w hnw (d4T36M ε) hw,
    Subgroup.card_map_of_injective rootDiagUnit_injective,
    d4T36_card hε hq1 (dvd_pow_self ℓ (by omega)) hFr]
  exact (d4T36d_odd hε hq1).mul (d4T36d_odd hε hq1)

end Aux

section Solvable

theorem d4T36_solvable {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (w : WeylGroup TwistTag.D4.tag) (hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    {x : 𝒞[K, σ]} (hx : orderOf x = p) (c : 𝒞[K, σ])
    (hxT : g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∀ V : Subgroup (Subgroup.centralizer ({x} : Set 𝒞[K, σ])), V.Normal →
      Group.IsSolvable V → Odd (Nat.card V) := by
  classical
  intro V hVn hVs
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hcomm := d4Q_hcomm K σ hσ L
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ hf hK σ hσ
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hxT).1
  have hperx := d4T36_perx hf K σ hkc hε hp hp3 hpd hn w hnw hw hg0C hg0 hperf hcomm hx c hb.symm
    (by rw [← hb]; exact hxT)
  have : Finite (twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :=
    Nat.finite_of_card_ne_zero (d4T36_torus_card_odd hf hε hn w hnw hw).pos.ne'
  exact odd_card_of_map_le (d4QPsi (triEmb K σ L) g0 c x) (d4QPsi_injective triEmb_injective g0 c x)
    V _ (fun v hv => (hperx.1 V hVn hVs v hv).1) (d4T36_torus_card_odd hf hε hn w hnw hw)

end Solvable

section Core

theorem d4T36_core_odd {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (hC : Subgroup.center 𝒞[K, σ] = ⊥)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (w : WeylGroup TwistTag.D4.tag) (hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {g0 : ModGL TwistTag.D4.tag L} (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range)
    {B : Subgroup (MulAut 𝒞[K, σ])}
    (hB : (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ≤ B)
    {x : 𝒞[K, σ]} (hx : orderOf x = p) (c : 𝒞[K, σ])
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)))
    (hsing : (rootCharKernel b).Nonempty) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut 𝒞[K, σ])} :
        Set (MulAut 𝒞[K, σ]))))) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hcomm := d4Q_hcomm K σ hσ L
  have hIntinj : Function.Injective (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) :=
    mulAut_conj_injective_of_center_eq_bot hC
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ hf hK σ hσ
  have hperx := d4T36_perx hf K σ hkc hε hp hp3 hpd hn w hnw hw hg0C hg0 hperf hcomm hx c hb hh
  have hsolv := d4T36_solvable hf K hK σ hσ hε hp hp3 hpd L hn w hnw hw hg0C hg0 hperf hx c
    (by rw [← hb]; exact hh)
  obtain ⟨V, hVn, hVs, hVl⟩ := innerCorePreimage hp hIntinj hB x
  obtain ⟨P, hPfin, hPq, hPQ, hPψ, hPr⟩ := hperx.2 hsing
  have hψinj : Function.Injective (d4QPsi (triEmb K σ L) g0 c x) :=
    d4QPsi_injective triEmb_injective g0 c x
  have hoddInn := odd_card_inf_range_of_solvable (B := B) hp hC hB hsolv
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := inSubgroup (aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut 𝒞[K, σ])} :
      Set (MulAut 𝒞[K, σ])))) 2 h2
  have hη2 : (g : MulAut 𝒞[K, σ]) ^ 2 = 1 := by
    have h3 := pow_orderOf_eq_one g
    rw [hg] at h3
    exact congrArg Subtype.val h3
  have hηo : (g : MulAut 𝒞[K, σ]) ∉
      (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range := by
    intro hmem
    have hmem' : (g : MulAut 𝒞[K, σ]) ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut 𝒞[K, σ])} :
          Set (MulAut 𝒞[K, σ]))) ⊓ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range :=
      Subgroup.mem_inf.2 ⟨g.2, hmem⟩
    have hord : orderOf (⟨(g : MulAut 𝒞[K, σ]), hmem'⟩ : ↥(inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut 𝒞[K, σ])} :
          Set (MulAut 𝒞[K, σ]))) ⊓ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (g : MulAut 𝒞[K, σ]) = 2
      rw [Subgroup.orderOf_coe]
      exact hg
    have hd := orderOf_dvd_natCard (⟨(g : MulAut 𝒞[K, σ]), hmem'⟩ : ↥(inSubgroup
      (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut 𝒞[K, σ])} :
        Set (MulAut 𝒞[K, σ]))) ⊓ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range))
    rw [hord] at hd
    exact (Nat.not_even_iff_odd.2 hoddInn) (even_iff_two_dvd.2 hd)
  have hηx : (g : MulAut 𝒞[K, σ]) x = x :=
    apply_eq_of_comm_conj hIntinj g x (mem_centralizer_of_mem_autCore g.2)
  set ψ := d4QPsi (triEmb K σ L) g0 c x with hψdef
  set V' : Subgroup 𝒞[K, σ] := V.map (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype with hV'
  have hV'l : ∀ q ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut 𝒞[K, σ])} :
        Set (MulAut 𝒞[K, σ]))) ⊓ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range,
      ∃ v ∈ V', MulAut.conj v = q := fun q hq => by
    obtain ⟨v, hv, hvq⟩ := hVl q hq
    exact ⟨v, ⟨v, hv, rfl⟩, hvq⟩
  have hVab : ∀ v ∈ V', ∀ w ∈ V', v * w = w * v := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
    obtain ⟨a, ha, -⟩ := (hperx.1 V hVn hVs v hv).2
    obtain ⟨a', ha', -⟩ := (hperx.1 V hVn hVs v' hv').2
    have : v * v' = v' * v := by
      apply hψinj
      rw [map_mul, map_mul, ha, ha', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm a a']
    exact congrArg Subtype.val this
  set A : Subgroup ↥(Subgroup.centralizer ({x} : Set 𝒞[K, σ])) := P.comap ψ with hA
  set R : Subgroup 𝒞[K, σ] := A.map (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype with hR
  have hmapA : A.map ψ = P := by
    rw [hA, Subgroup.map_comap_eq, inf_eq_right.2 hPψ]
  have hAperf : ⁅A, A⁆ = A := by
    apply Subgroup.map_injective hψinj
    rw [Subgroup.map_commutator, hmapA]
    exact Subgroup.isPerfect_iff.1 hPq.1
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, hAperf]
  have hRx : ∀ r ∈ R, r * x = x * r := by
    rintro _ ⟨r, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 r.2
  have hRV : ∀ r ∈ R, ∀ v ∈ V', r * v = v * r := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨a, ha, hker⟩ := (hperx.1 V hVn hVs v hv).2
    have hcen : ψ v ∈ Subgroup.centralizer
        (rootSpan TwistTag.D4.tag L (rootCharKernel b) : Set (ModGL TwistTag.D4.tag L)) := by
      rw [ha]
      exact (rootDiagUnit_mem_centralizer_rootSpan_iff a (fun α hα => hα.1)).2 hker
    have hrP : ψ r ∈ rootSpan TwistTag.D4.tag L (rootCharKernel b) := hPQ (Subgroup.mem_comap.1 hr)
    have h1 : ψ r * ψ v = ψ v * ψ r := Subgroup.mem_centralizer_iff.1 hcen _ hrP
    have h2 : r * v = v * r := hψinj (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  have hfixR := core_fixes_perfect hIntinj hB x V' hV'l hVab R hRx hRperf hRV g.2
  obtain ⟨e, hfe, -⟩ := d4Q_involution_conj hℓ hf K hK σ hσ g hη2 hηo
  have he1 : 1 ≤ e := by omega
  have hQ2 : 2 ≤ ℓ ^ e := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓ.pos he1
  obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_dvd_sq_add_one hQ2
  have hrq : r ∣ ℓ ^ f + 1 := by
    have : ℓ ^ f = (ℓ ^ e) ^ 2 := by rw [hfe, ← pow_mul, mul_comm]
    rw [this]
    exact hrd
  obtain ⟨y, hyP, hyr⟩ := hPr r hr hrq
  obtain ⟨z, hz⟩ := hPψ hyP
  have hzA : z ∈ A := Subgroup.mem_comap.2 (hz ▸ hyP)
  have hzR : (z : 𝒞[K, σ]) ∈ R := ⟨z, hzA, rfl⟩
  have hzo : orderOf (z : 𝒞[K, σ]) = r := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective ψ hψinj z, hz, hyr]
  exact d4Q_no_outer_involution hℓ hf K hK σ hσ hr hr3 hrq g hη2 hηo hzo (hfixR _ hzR)

end Core

end CFSG.RankThree.PartOne.KGD
