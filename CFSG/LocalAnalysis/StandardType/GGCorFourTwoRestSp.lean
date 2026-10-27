module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSpTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrLangNorm
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp

namespace CorFourTwoSp

variable {K : Type} [Field K] {m : ℕ}

section Coord

open Multiplicative

theorem eq_self_of_coord_transvection {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {j : Fin m → Fin m}
    {ε : Fin m → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) {c : ZMod p} (hc : c ≠ 0)
    {L : (Fin m → Multiplicative (ZMod p)) → Fin m → Multiplicative (ZMod p)}
    (hL : ∀ f i, toAdd (L f (j i)) = ε i * c * toAdd (f i))
    (htv : ∀ f, L (f⁻¹ * L f) = f⁻¹ * L f) (f : Fin m → Multiplicative (ZMod p)) : L f = f := by
  classical
  have hεc : ∀ i, ε i * c ≠ 0 := fun i =>
    SpCoord.coord_mul_ne_zero hp (SpCoord.coord_sign_ne_zero hp (hε i)) hc
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin m → Fin m → Multiplicative (ZMod p),
      ∀ i y, toAdd (δ i y) = if y = i then 1 else 0 :=
    ⟨fun i => Pi.mulSingle i (ofAdd 1), fun i y => SpCoord.toAdd_mulSingle i y 1⟩
  have hLδ : ∀ i k, toAdd (L (δ i) (j k)) = if k = i then ε i * c else 0 := by
    intro i k
    rw [hL, hδ]
    split_ifs with h
    · subst h
      ring
    · ring
  have hjinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    have h1 := hLδ i i
    have h2 := hLδ i i'
    rw [ite_eq_left rfl] at h1
    rw [ite_eq_right (Ne.symm hne), ← hii', h1] at h2
    exact hεc i h2
  have hjsurj : Function.Surjective j := Finite.surjective_of_injective hjinj
  have key : ∀ i, j i = i ∧ ε i * c = 1 := by
    intro i
    obtain ⟨v, hv⟩ : ∃ v, v = (δ i)⁻¹ * L (δ i) := ⟨_, rfl⟩
    have hLv : L v = v := by
      rw [hv]
      exact htv (δ i)
    have hva : ∀ y, toAdd (v y) = - toAdd (δ i y) + toAdd (L (δ i) y) := by
      intro y
      rw [hv, Pi.mul_apply, Pi.inv_apply, toAdd_mul, toAdd_inv]
    have hfix : ∀ k, toAdd (v (j k)) = ε k * c * toAdd (v k) := by
      intro k
      rw [← hL v k, hLv]
    by_cases hji : j i = i
    · refine ⟨hji, ?_⟩
      have h2 := hLδ i i
      rw [ite_eq_left rfl, hji] at h2
      have hvi : toAdd (v i) = -1 + ε i * c := by
        rw [hva, hδ, ite_eq_left rfl, h2]
      have h1 := hfix i
      rw [hji, hvi] at h1
      have h3 : (ε i * c - 1) * (ε i * c - 1) = 0 := by linear_combination -h1
      have h4 : ε i * c - 1 = 0 := (SpCoord.coord_mul_eq_zero hp h3).elim id id
      linear_combination h4
    · exfalso
      obtain ⟨k₀, hk₀⟩ := hjsurj i
      have hk₀i : k₀ ≠ i := fun h => hji (h ▸ hk₀)
      have hvi : toAdd (v i) = -1 := by
        have h2 := hLδ i k₀
        rw [ite_eq_right hk₀i, hk₀] at h2
        rw [hva, hδ, ite_eq_left rfl, h2]
        ring
      have hvji : toAdd (v (j i)) = ε i * c := by
        have h2 := hLδ i i
        rw [ite_eq_left rfl] at h2
        rw [hva, hδ, ite_eq_right hji, h2]
        ring
      have h1 := hfix i
      rw [hvji, hvi] at h1
      have h3 : ε i * c = -(ε i * c) := by linear_combination h1
      exact hεc i (SpCoord.coord_eq_zero_of_eq_neg hp hp2 h3)
  refine SpCoord.eq_of_toAdd_eq fun i => ?_
  have h1 := hL f i
  rw [(key i).1, (key i).2, one_mul] at h1
  exact h1

theorem exists_move_line {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    {f : Fin k → Multiplicative (ZMod p)} (hf : f ≠ 1) :
    ∃ α : MulAut (Fin k → Multiplicative (ZMod p)),
      ((∃ i, α = SpCoord.sgnAut i) ∨ ∃ σ : Equiv.Perm (Fin k), α = SpCoord.permAut σ) ∧
      ∀ n : ℕ, α f ≠ f ^ n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, toAdd (f i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (SpCoord.eq_of_toAdd_eq fun i => by rw [h i, Pi.one_apply, toAdd_one])
  by_cases h2 : ∃ j, j ≠ i ∧ toAdd (f j) ≠ 0
  · obtain ⟨j, hji, hj⟩ := h2
    refine ⟨SpCoord.sgnAut i, Or.inl ⟨i, rfl⟩, fun n hn => ?_⟩
    have h1 := congrArg (fun g : Fin k → Multiplicative (ZMod p) => toAdd (g j)) hn
    have h3 := congrArg (fun g : Fin k → Multiplicative (ZMod p) => toAdd (g i)) hn
    simp only [SpCoord.sgnAut_apply, Function.update_of_ne hji, Function.update_self,
      Pi.pow_apply, toAdd_pow, toAdd_inv, nsmul_eq_mul] at h1 h3
    have hn1 : (n : ZMod p) = 1 := by
      have h4 : ((n : ZMod p) - 1) * toAdd (f j) = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((SpCoord.coord_mul_eq_zero hp h4).resolve_right hj)
    rw [hn1, one_mul] at h3
    exact hi (SpCoord.coord_eq_zero_of_eq_neg hp hp2 h3.symm)
  · push Not at h2
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    obtain ⟨j, hji⟩ := exists_ne i
    refine ⟨SpCoord.permAut (Equiv.swap i j), Or.inr ⟨_, rfl⟩, fun n hn => ?_⟩
    have h1 := congrArg (fun g : Fin k → Multiplicative (ZMod p) => toAdd (g j)) hn
    simp only [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_right, Pi.pow_apply, toAdd_pow, nsmul_eq_mul, h2 j hji, mul_zero] at h1
    exact hi h1

end Coord

theorem conj_mulAut {G : Type*} [Group G] (ψ : MulAut G) (y : G) :
    ψ * MulAut.conj y * ψ⁻¹ = MulAut.conj (ψ y) := by
  rw [mulAut_mul_conj, mul_inv_cancel_right]

theorem exists_preimage_of_subset [Finite K] [CharP K 2] [NeZero m] {p : ℕ}
    {Eh : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))}
    (hEhI : (Eh : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
    (hEhA : IsElemAbelian p Eh) :
    ∃ E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)), IsElemAbelian p E ∧
      (∀ e, e ∈ E ↔ MulAut.conj e ∈ Eh) ∧ (∀ φ ∈ Eh, ∃ e ∈ E, MulAut.conj e = φ) ∧
      Nat.card E = Nat.card Eh := by
  have hinj := mulAut_conj_injective (center_spProj_eq_bot (K := K) (m := m))
  refine ⟨Eh.comap MulAut.conj, ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun e he => hinj ?_⟩,
    fun e => Iff.rfl, fun φ hφ => ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hEhA a.2 b.2
  · rw [map_pow, map_one]
    exact hEhA.2 _ he
  · obtain ⟨e, he⟩ := sp_I_subset_inn (hEhI hφ)
    refine ⟨e, ?_, he⟩
    show MulAut.conj e ∈ Eh
    rw [he]
    exact hφ
  · have hmap : (Eh.comap MulAut.conj).map MulAut.conj = Eh := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr]
      intro φ hφ
      exact sp_I_subset_inn (hEhI hφ)
    rw [Nat.card_congr ((Eh.comap MulAut.conj).equivMapOfInjective _ hinj).toEquiv, hmap]

section Center

open CFSG.LieType.Steinberg.CentralExt


theorem ggCenterCoprime_spGroup [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterCoprime p ↥(LargeEvenSpGroup K m) := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have := Fact.mk hp
  have : Group.IsPerfect L' := ⟨hperf⟩
  set N := CoprimeSplit.copPart p ψ.ker hker with hN
  have hNker : N ≤ ψ.ker := fun _ h => h.1
  let ψ₁ : L' ⧸ N →* ↥(LargeEvenSpGroup K m) := QuotientGroup.lift N ψ hNker
  have hψ₁e : ∀ e : L', ψ₁ (e : L' ⧸ N) = ψ e := fun e => rfl
  have hψ₁ : Function.Surjective ψ₁ := fun g => by
    obtain ⟨e, rfl⟩ := hψ g
    exact ⟨(e : L' ⧸ N), rfl⟩
  have : Group.IsPerfect (L' ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hker₁ : ψ₁.ker ≤ Subgroup.center (L' ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₁e]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hker he) z']
  have hp₁ : IsPGroup p ψ₁.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₁e]
      exact hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := p) hker he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have hcop : (2 : ℕ).Coprime (Nat.card ψ₁.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp₁
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨σ, hσ⟩ := SpClosed.sp_exists_section_of_coprime (K := K) (n := m) (p := 2)
    (L' ⧸ N) ψ₁ hψ₁ hker₁ hcop
  have hbot := SL2Closed.ker_eq_bot_of_section ψ₁ hker₁ σ hσ
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcN : (c : L') ∈ N := by
    have hq : ((c : L') : L' ⧸ N) ∈ ψ₁.ker := by
      rw [MonoidHom.mem_ker, hψ₁e]
      exact c.2
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hq
    exact hq
  have h1 := (CoprimeSplit.mem_copPart.1 hcN).2
  rw [Subgroup.orderOf_coe, hc] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 dvd_rfl)

theorem ggCenterCoprime_symplectic [Finite K] [CharP K 2] [NeZero m] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : GGCenterCoprime p (LargeEvenProj (LargeEvenSpGroup K m)) :=
  ggCenterCoprime_of_mulEquiv spProjEquivSp (ggCenterCoprime_spGroup hp hp2)

end Center

theorem ggNoTransvectionTorus_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGNoTransvectionTorus p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro Eh hEhI hEhA hr h3 a htv
  have : NeZero m := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hinj := mulAut_conj_injective (center_spProj_eq_bot (K := K) (m := m))
  obtain ⟨E, hEab, hEmem, hEsurj, hEcard⟩ := exists_preimage_of_subset hEhI hEhA
  have hrE : p ^ m ≤ Nat.card E := by
    rw [hEcard]
    exact hr
  have h3E : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact h3
  have hEm : Nat.card E ≤ p ^ m := card_le_of_isElemAbelian_spProj hp hp2 hpq hEab
  have hm3 : 3 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3E.trans hEm)
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨x, hτE, hEτ⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hEab hrE
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  have hβE : ∀ e ∈ E, (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) e ∈ E := by
    intro e he
    rw [hEmem]
    have h1 := (Subgroup.mem_normalizer_iff.mp a.2 (MulAut.conj e)).mp ((hEmem e).mp he)
    rwa [conj_mulAut] at h1
  obtain ⟨s, σ, c, -, hc, -, hform⟩ := exists_conj_pow_of_aut hm3 hζo hζ x
    (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))
  have hc0 : (c : ZMod p) ≠ 0 := natCast_ne_zero_of_eq_pow hp hζo hc
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin m ⊕ Fin m) K).subgroupOf (LargeEvenSpGroup K m))
    (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x)
  obtain ⟨j, ε, hε, hj⟩ := ReflSp.exists_monomial_data hζo hζ (g₀ : GL (Fin m ⊕ Fin m) K)
  have hcoord : ∀ f f', (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))
      (x * spTorus hζ f * x⁻¹) = x * spTorus hζ f' * x⁻¹ →
      ∀ i, Multiplicative.toAdd (f' (j i)) = ε i * c * Multiplicative.toAdd (f i) := by
    intro f f' hff' i
    rw [hform, conj_pow, ← map_pow] at hff'
    have h1 : (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x) * spTorus hζ (f ^ c) *
        (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x)⁻¹ = spTorus hζ f' := by
      calc (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x) * spTorus hζ (f ^ c) *
            (x⁻¹ * (s * fieldAutR m σ x * x⁻¹) * x)⁻¹ =
            x⁻¹ * ((s * fieldAutR m σ x * x⁻¹) * (x * spTorus hζ (f ^ c) * x⁻¹) *
              (s * fieldAutR m σ x * x⁻¹)⁻¹) * x := by group
        _ = spTorus hζ f' := by
          rw [hff']
          group
    have h2 : g₀ * spTorusSp hζ (f ^ c) * g₀⁻¹ = spTorusSp hζ f' := by
      apply hπi
      rw [map_mul, map_mul, map_inv]
      exact (congrArg (fun y => y * spTorus hζ (f ^ c) * y⁻¹) hg₀).trans h1
    have h3 : (g₀ : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ (f ^ c) =
        spTorusGL hζ f' * (g₀ : GL (Fin m ⊕ Fin m) K) := by
      have h4 := congrArg (fun y : LargeEvenSpGroup K m => (y : GL (Fin m ⊕ Fin m) K)) h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe] at h4
      rw [← h4]
      group
    rw [hj _ _ h3 i, Pi.pow_apply, toAdd_pow, nsmul_eq_mul]
    ring
  have hex : ∀ f, ∃ f', (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))
      (x * spTorus hζ f * x⁻¹) = x * spTorus hζ f' * x⁻¹ := by
    intro f
    obtain ⟨f', hf'⟩ := hEτ _ (hβE _ (hτE f))
    exact ⟨f', hf'.symm⟩
  choose L hLdef using hex
  have hτinj : ∀ f f', x * spTorus hζ f * x⁻¹ = x * spTorus hζ f' * x⁻¹ → f = f' :=
    fun f f' h => spTorus_injective hζ hζo (hp.odd_of_ne_two hp2)
      (mul_left_cancel (mul_right_cancel h))
  have htvE : ∀ e ∈ E, (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))
      (e⁻¹ * (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) e) =
        e⁻¹ * (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) e := by
    intro e he
    have h2 : (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) *
        ((MulAut.conj e)⁻¹ * ((a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) *
          MulAut.conj e * (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))⁻¹)) *
        (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))⁻¹ =
        (MulAut.conj e)⁻¹ * ((a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) *
          MulAut.conj e * (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))⁻¹) :=
      congrArg Subtype.val (htv.2 ⟨MulAut.conj e, (hEmem e).mp he⟩)
    have h3 : (MulAut.conj e)⁻¹ * ((a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) *
        MulAut.conj e * (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))⁻¹) =
        MulAut.conj (e⁻¹ * (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) e) := by
      rw [conj_mulAut, map_mul, map_inv]
    rw [h3, conj_mulAut] at h2
    exact hinj h2
  have hLtv : ∀ f, L (f⁻¹ * L f) = f⁻¹ * L f := by
    intro f
    apply hτinj
    rw [← hLdef]
    have h1 := htvE _ (hτE f)
    rw [hLdef f] at h1
    have e1 : (x * spTorus hζ f * x⁻¹)⁻¹ * (x * spTorus hζ (L f) * x⁻¹) =
        x * spTorus hζ (f⁻¹ * L f) * x⁻¹ := by
      rw [map_mul, map_inv]
      group
    rw [e1] at h1
    exact h1
  have hLid := eq_self_of_coord_transvection hp hp2 hε hc0 (L := L)
    (fun f i => hcoord f (L f) (hLdef f) i) hLtv
  have hψ : ∀ b : ↥Eh, Eh.normalizerMonoidHom a b = b := by
    intro b
    obtain ⟨e, he, hb⟩ := hEsurj b.1 b.2
    obtain ⟨f, rfl⟩ := hEτ e he
    apply Subtype.ext
    change (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) *
      (b : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) *
      (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))⁻¹ =
        (b : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))
    rw [← hb, conj_mulAut, hLdef, hLid]
  have hcard := htv.1
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hψ)] at hcard
  have hpos : 0 < Nat.card Eh := lt_of_lt_of_le (pow_pos hp.pos 3) h3
  nlinarith [hp.two_le]

theorem ggNoInvariantLineTorus_symplectic
    [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGNoInvariantLineTorus p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  intro Eh hEhI hEhA hr h3
  refine ⟨ggCenterCoprime_symplectic hp hp2, fun Λ hΛ hΛp => ?_⟩
  have hinj := mulAut_conj_injective (center_spProj_eq_bot (K := K) (m := m))
  have : Finite (MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := finite_mulAut
  obtain ⟨E, hEab, hEmem, hEsurj, hEcard⟩ := exists_preimage_of_subset hEhI hEhA
  have hrE : p ^ m ≤ Nat.card E := by
    rw [hEcard]
    exact hr
  have h3E : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact h3
  obtain ⟨k, τ, hτi, hτE, hsgn, hperm, -⟩ :=
    SpModel.ggTorusSignedElt_sp (K := K) (m := m) hp hp2 hpq E hEab hrE h3E
  have hk : 2 ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card E := by
      rw [← hτE]
      exact Nat.card_congr (MonoidHom.ofInjective hτi).toEquiv
    rw [hcV] at h1
    rw [← h1] at h3E
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3E
    omega
  obtain ⟨e₀, he₀Λ, he₀1⟩ : ∃ e ∈ Λ, e ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Λ = ⊥ := (Subgroup.eq_bot_iff_forall Λ).mpr h
    rw [hbot, Subgroup.card_bot] at hΛp
    exact hp.one_lt.ne hΛp
  have hΛz : ∀ e ∈ Λ, ∃ n : ℕ, e₀ ^ n = e := by
    have hz : Subgroup.zpowers e₀ = Λ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he₀Λ) ?_
      rw [hΛp, Nat.card_zpowers]
      have h1 : orderOf e₀ ∣ p := hΛp ▸ Subgroup.orderOf_dvd_natCard Λ he₀Λ
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) he₀1
      · exact h.ge
    intro e he
    rw [← hz] at he
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr he)
  obtain ⟨y₀, hy₀E, rfl⟩ := hEsurj e₀ (hΛ he₀Λ)
  obtain ⟨f₀, rfl⟩ : y₀ ∈ τ.range := by
    rw [hτE]
    exact hy₀E
  have hf₀ : f₀ ≠ 1 := by
    rintro rfl
    exact he₀1 (by rw [map_one, map_one])
  obtain ⟨α, hαw, hαmove⟩ := exists_move_line hp hp2 hk hf₀
  obtain ⟨w, hw⟩ : ∃ w : LargeEvenProj (LargeEvenSpGroup K m), ∀ f, w * τ f * w⁻¹ = τ (α f) := by
    rcases hαw with ⟨i, rfl⟩ | ⟨σ, rfl⟩
    · exact hsgn i
    · exact hperm σ
  have hwN : MulAut.conj w ∈ Subgroup.normalizer
      (Eh : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) := by
    refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨y, hyE, rfl⟩ := hEsurj b hb
    obtain ⟨f, rfl⟩ : y ∈ τ.range := by
      rw [hτE]
      exact hyE
    rw [← map_inv, ← map_mul, ← map_mul, hw]
    exact (hEmem _).mp (by rw [← hτE]; exact ⟨α f, rfl⟩)
  refine ⟨w, hwN, MulAut.conj (τ f₀), he₀Λ, fun hmem => ?_⟩
  obtain ⟨n, hn⟩ := hΛz _ hmem
  rw [← map_inv, ← map_mul, ← map_mul, hw, ← map_pow, ← map_pow] at hn
  exact hαmove n (hτi (hinj hn)).symm

theorem recipeSymplectic_corFourTwo {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I ∧ GGNoTransvectionTorus p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggInnerDiagBound_symplectic hp hp2 hpq hl, ggNoTransvectionTorus_symplectic hp hp2 hpq hl⟩

theorem recipeSymplectic_noInvariantLine
    {l n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggNoInvariantLineTorus_symplectic hp hp2 hpq hl⟩

end CorFourTwoSp

open CorFourTwoSp

theorem ggReflSpLabel_pilot {p : ℕ} {lab : LargeEvenLabel} (h : GGReflSpLabel p lab) :
    GGOutdiagPilotLabel lab := by
  rcases h.1 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem largeEvenLabelAll_corFourTwo_symplectic {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I ∧
      GGNoTransvectionTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_corFourTwo hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

theorem largeEvenLabelAll_noInvariantLine_symplectic
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_noInvariantLine hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

theorem ggBstarInnerDiagLInputOn_symplectic : GGBstarInnerDiagLInputOn GGReflSpLabel :=
  ggBstarInnerDiagLInputOn_of_labels (fun _ _ h => ggReflSpLabel_pilot h) fun _ _ hp hlab h =>
    (largeEvenLabelAll_corFourTwo_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggLTransvectionCenterInputOn_symplectic : GGLTransvectionCenterInputOn GGReflSpLabel :=
  ggLTransvectionCenterInputOn_of_labels (fun _ _ h => ggReflSpLabel_pilot h)
    fun _ _ hp hlab h => (largeEvenLabelAll_corFourTwo_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

theorem ggLNoInvariantLineInputOn_symplectic :
    GGLNoInvariantLineInputOn GGReflSpLabel :=
  ggLNoInvariantLineInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_noInvariantLine_symplectic hp hlab h

theorem ggTableBIrredInputOn_symplectic : GGTableBIrredInputOn GGReflSpLabel :=
  ggTableBIrredInputOn_of_labels fun _ _ hp hlab h =>
    (SpModel.largeEvenLabelAll_weylInputs_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, _, h3, _⟩ => ⟨r, h1, h3⟩

theorem ggTableBCxInputOn_symplectic : GGTableBCxInputOn GGReflSpLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_symplectic ggTableBIrredInputOn_symplectic

theorem ggTableBModuleInputOn_symplectic : GGTableBModuleInputOn GGReflSpLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_symplectic
    ggTableBIrredInputOn_symplectic

theorem ggTableBActionInputOn_symplectic : GGTableBActionInputOn GGReflSpLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_symplectic
    ggTableBIrredInputOn_symplectic

end CFSG.StandardType

end
