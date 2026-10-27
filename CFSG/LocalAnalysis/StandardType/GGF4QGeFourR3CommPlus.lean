module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusRankOne
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourR3Comm
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4CommPair
import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Multiplicative Module
open CFSG.RankThree.Classical2 (orthDerived)

namespace OmPlusFrame

open QuadraticMap Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

section Native

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem apply_eq_of_mem_specialBlock_of_fixed {p : ℕ} {s : V ≃ₗ[K] V}
    (hs : OddOrderIsometry Q p s) {h : K[X]} (hh : h ∈ primaryFactors s.toLinearMap)
    (hne : h ≠ X - 1) {g : V ≃ₗ[K] V} (hg : g ∈ specialBlock Q s h) :
    ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s, g v = v := by
  intro v hv
  have hgS := (mem_supportedBlock.mp (specialBlock_le_supportedBlock h hg)).2
  rw [← OrthRestOdd.fixedSpace_eq_lit, fixedSpace_eq_primaryComponent] at hv
  by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors s.toLinearMap
  · refine fixes_othersSpace_iff.mp hgS (X - 1) hmem (Ne.symm hne) ?_ v hv
    intro he
    apply hne
    rw [← hs.reciprocal_reciprocal_eq hh, ← he, reciprocalPolynomial_X_sub_one]
  · have hbot := fixedSpace_eq_bot_of_not_mem hmem
    rw [fixedSpace_eq_primaryComponent] at hbot
    rw [hbot] at hv
    rw [(Submodule.mem_bot K).mp hv, map_zero]

theorem commute_of_sign_transp (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {a b s : V ≃ₗ[K] V}
    (ha : a ∈ orthDerived Q) (hb : b ∈ orthDerived Q) (hs : s ∈ orthDerived Q)
    (hap : a ^ p = 1) (hbp : b ^ p = 1) (hsp : s ^ p = 1)
    (ha2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace a) = 2)
    (hb2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace b) = 2)
    (hsab : ∃ n : ℕ, s = a * b ^ n)
    (hcs : CFSG.RankThree.PartOne.LIT.commSpace s =
      CFSG.RankThree.PartOne.LIT.commSpace a ⊔ CFSG.RankThree.PartOne.LIT.commSpace b)
    {h : K[X]} (hh : h ∈ primaryFactors s.toLinearMap) (hne : h ≠ X - 1) {g₁ g₂ : V ≃ₗ[K] V}
    (hg₁ : g₁ ∈ ggOTwoPrime (orthDerived Q ⊓
      Subgroup.centralizer ({a, b} : Set (V ≃ₗ[K] V))))
    (hg₂ : g₂ ∈ specialBlock Q s h) : g₁ * g₂ = g₂ * g₁ := by
  have hsx : OddOrderIsometry Q p s :=
    oddOrderIsometry_of_orthDerived hQ hp hp2 (t := ⟨s, hs⟩) (Subtype.ext (by simpa using hsp))
  have hWM := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hsx.cast_ne_zero hsp
  have hg₂W := apply_eq_of_mem_specialBlock_of_fixed hsx hh hne hg₂
  have hg₂s : g₂ * s = s * g₂ :=
    LinearEquiv.ext fun v =>
      (mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hg₂)).2 v
  have hg₂M : ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s,
      g₂ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s := by
    intro v hv
    obtain ⟨y, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
    refine CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨g₂ y, ?_⟩
    rw [map_sub, ← LinearEquiv.mul_apply, ← hg₂s, LinearEquiv.mul_apply]
  have hP : (∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace s, g₁ v = v) ∧ g₁ * s = s * g₁ := by
    unfold ggOTwoPrime at hg₁
    induction hg₁ using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨-, hyC⟩, k, hk⟩ := hy
      have hya : a * y = y * a := Subgroup.mem_centralizer_iff.mp hyC a (by simp)
      have hyb : b * y = y * b := Subgroup.mem_centralizer_iff.mp hyC b (by simp)
      have hfa := apply_eq_of_two_pow_commSpace hQ hp hp2 hK1 ha hap ha2 hya hk
      have hfb := apply_eq_of_two_pow_commSpace hQ hp hp2 hK1 hb hbp hb2 hyb hk
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [hcs] at hv
        obtain ⟨va, hva, vb, hvb, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add, hfa va hva, hfb vb hvb]
      · obtain ⟨n, rfl⟩ := hsab
        exact ((Commute.symm hya).mul_right ((Commute.symm hyb).pow_right n)).eq
    | one => exact ⟨fun v _ => rfl, by rw [one_mul, mul_one]⟩
    | mul g g' _ _ ih ih' =>
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [LinearEquiv.mul_apply, ih'.1 v hv, ih.1 v hv]
      · exact ((Commute.mul_left ih.2 ih'.2)).eq
    | inv g _ ih =>
      refine ⟨fun v hv => ?_, (Commute.inv_left ih.2).eq⟩
      calc g⁻¹ v = g⁻¹ (g v) := by rw [ih.1 v hv]
        _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hg₁W : ∀ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s,
      g₁ v ∈ CFSG.RankThree.PartOne.LIT.fixedSpace s := by
    intro v hv
    rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace] at hv ⊢
    rw [← LinearEquiv.mul_apply, ← hP.2, LinearEquiv.mul_apply, hv]
  exact commute_of_isCompl hWM hP.1 hg₁W hg₂W hg₂M

end Native

end OmPlusFrame

section Model

private theorem rk1c_pow_p {p : ℕ} (g : Fin 3 → Multiplicative (ZMod p)) : g ^ p = 1 := by
  funext m
  rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (g m), ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

private theorem rk1c_mulSingle_eq_pow {p : ℕ} [NeZero p] (k : Fin 3) (η : ZMod p) :
    (Pi.mulSingle k (ofAdd η) : Fin 3 → Multiplicative (ZMod p)) =
      (Pi.mulSingle k (ofAdd 1)) ^ η.val := by
  rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private theorem rankOne_commute_sign_transp {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {Bs X : Subgroup G} {ψΩ : ↥(orthDerived Q) →* G}
    {τ : (Fin 3 → Multiplicative (ZMod p)) →* ↥(orthDerived Q)} {cv : ↥Bs → Fin 3 → ZMod p}
    (hcvsurj : ∀ v, ∃ b, cv b = v)
    (hU2 : ∀ m : Fin 3, finrank K (CFSG.RankThree.PartOne.LIT.commSpace
      ((τ (Pi.mulSingle m (ofAdd 1)) : ↥(orthDerived Q)) : V ≃ₗ[K] V)) = 2)
    {φ₁ φ₂ : MulAut ↥Bs} (hcomm : φ₁ * φ₂ = φ₂ * φ₁) {ε₁ : Fin 3 → ZMod p}
    (hcv₁ : ∀ b, cv (φ₁ b) = OmPlusFrame.spAct 1 ε₁ (cv b)) {i₀ : Fin 3} (hi₀ : ε₁ i₀ = -1)
    (hε₁ : ∀ m, m ≠ i₀ → ε₁ m = 1)
    (himg₁ : ∀ k l : Fin 3, k ≠ l → k ≠ i₀ → l ≠ i₀ →
      ggRankOneIn X Bs φ₁ = (ggOTwoPrime (Subgroup.centralizer
        ({τ (Pi.mulSingle k (ofAdd 1)), τ (Pi.mulSingle l (ofAdd 1))} :
          Set ↥(orthDerived Q)))).map ψΩ)
    {π₂ : Equiv.Perm (Fin 3)} {ε₂ : Fin 3 → ZMod p} (hε₂ : ∀ m, ε₂ m = 1 ∨ ε₂ m = -1)
    (hcv₂ : ∀ b, cv (φ₂ b) = OmPlusFrame.spAct π₂ ε₂ (cv b)) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hjπ : π₂ j = k) (hkπ : π₂ k = j) {h : Polynomial K}
    (hne : h ≠ Polynomial.X - 1)
    (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε₂ j))) : ↥(orthDerived Q)) :
        V ≃ₗ[K] V).toLinearMap)
    (himg₂ : ggRankOneIn X Bs φ₂ = (ggOTwoPrime (Subgroup.centralizer
      ({τ (Pi.mulSingle i (ofAdd 1)),
        τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε₂ j)))} :
        Set ↥(orthDerived Q)))).map ψΩ)
    (hsb₂ : (ggOTwoPrime (Subgroup.centralizer
      ({τ (Pi.mulSingle i (ofAdd 1)),
        τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε₂ j)))} :
        Set ↥(orthDerived Q)))).map (orthDerived Q).subtype =
      CFSG.RankThree.PartOne.KCOrthogonal.specialBlock Q
        ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε₂ j))) : ↥(orthDerived Q)) :
          V ≃ₗ[K] V) h)
    (hcs₂ : CFSG.RankThree.PartOne.LIT.commSpace
        ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε₂ j))) : ↥(orthDerived Q)) :
          V ≃ₗ[K] V) =
      CFSG.RankThree.PartOne.LIT.commSpace ((τ (Pi.mulSingle j (ofAdd 1)) :
          ↥(orthDerived Q)) : V ≃ₗ[K] V) ⊔
        CFSG.RankThree.PartOne.LIT.commSpace ((τ (Pi.mulSingle k (ofAdd 1)) :
          ↥(orthDerived Q)) : V ≃ₗ[K] V)) :
    ∀ a ∈ ggRankOneIn X Bs φ₁, ∀ b ∈ ggRankOneIn X Bs φ₂, a * b = b * a := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcv₁₂ : ∀ b, cv (φ₁ (φ₂ b)) = cv (φ₂ (φ₁ b)) := fun b => by
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  have hnot : ∀ m m' : Fin 3, π₂ m = m' → m ≠ m' → i₀ ≠ m := by
    intro m m' hπ hmm' him
    subst him
    obtain ⟨b, hb⟩ := hcvsurj (Pi.single i₀ 1)
    have e := congrFun (hcv₁₂ b) m'
    rw [hcv₁ (φ₂ b), hcv₂ b, hcv₂ (φ₁ b), hcv₁ b, hb, OmPlusFrame.spAct_one_apply,
      OmPlusFrame.spAct_apply_of_eq hπ, OmPlusFrame.spAct_apply_of_eq hπ,
      OmPlusFrame.spAct_one_apply, Pi.single_eq_same, hi₀, hε₁ m' (Ne.symm hmm')] at e
    have h2 : 2 * ε₂ i₀ = 0 := by linear_combination e
    exact OmPlusFrame.sign_ne_zero (hε₂ i₀)
      ((mul_eq_zero.mp h2).resolve_left (OmPlusFrame.two_ne_zero_zmod hp2))
  have hi₀i : i₀ = i := by
    rcases OmPlusFrame.fin_three_cases hij hik hjk i₀ with h0 | h0 | h0
    · exact h0
    · exact absurd h0 (hnot j k hjπ hjk)
    · exact absurd h0 (hnot k j hkπ (Ne.symm hjk))
  rw [hi₀i] at himg₁
  intro x hx y hy
  rw [himg₁ j k hjk (Ne.symm hij) (Ne.symm hik)] at hx
  rw [himg₂] at hy
  obtain ⟨z₁, hz₁, rfl⟩ := hx
  obtain ⟨z₂, hz₂, rfl⟩ := hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hz₁' : ((z₁ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ ggOTwoPrime (orthDerived Q ⊓
      Subgroup.centralizer ({((τ (Pi.mulSingle j (ofAdd 1)) : ↥(orthDerived Q)) : V ≃ₗ[K] V),
        ((τ (Pi.mulSingle k (ofAdd 1)) : ↥(orthDerived Q)) : V ≃ₗ[K] V)} :
          Set (V ≃ₗ[K] V))) := by
    rw [← map_subtype_ggOTwoPrime_centralizer]
    exact ⟨z₁, hz₁, rfl⟩
  have hz₂' : ((z₂ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈
      CFSG.RankThree.PartOne.KCOrthogonal.specialBlock Q
        ((τ (Pi.mulSingle j (ofAdd 1) * Pi.mulSingle k (ofAdd (ε₂ j))) : ↥(orthDerived Q)) :
          V ≃ₗ[K] V) h := by
    rw [← hsb₂]
    exact ⟨z₂, hz₂, rfl⟩
  have hpow : ∀ g : Fin 3 → Multiplicative (ZMod p),
      ((τ g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ^ p = 1 := fun g => by
    rw [← Subgroup.coe_pow, ← map_pow, rk1c_pow_p, map_one, Subgroup.coe_one]
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact OmPlusFrame.commute_of_sign_transp hQ hp hp2 hK1 (τ _).2 (τ _).2 (τ _).2 (hpow _)
    (hpow _) (hpow _) (hU2 j) (hU2 k)
    ⟨(ε₂ j).val, by rw [rk1c_mulSingle_eq_pow k (ε₂ j), map_mul, map_pow, Subgroup.coe_mul,
      Subgroup.coe_pow]⟩ hcs₂ hh hne hz₁' hz₂'

private theorem rk1c_card_ne {f : ℕ} (hf : 2 ≤ f) :
    2 ^ f * ((2 ^ f) ^ 2 - 1) ≠ (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  generalize 2 ^ f = q at hq ⊢
  have hq4 : q + 1 < q ^ 4 := by
    calc q + 1 < q * 4 := by omega
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_left _ (hq.trans (Nat.le_self_pow (by norm_num) q))
      _ = q ^ 4 := by ring
  have hlt : q < q ^ 4 - 1 := by omega
  have h3 : q * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) :=
    calc q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = q ^ 2 * q := by ring
      _ < q ^ 2 * (q ^ 4 - 1) := mul_lt_mul_of_pos_left hlt (by positivity)
  exact ne_of_lt h3

private theorem rk1c_f4_label_two :
    ∀ q : Fin 4 × Fin 4, CoxeterMatrix.F₄ q.1 q.2 = 2 → (q.1.val < 2 ↔ ¬ q.2.val < 2) := by
  decide

end Model

section Main

theorem plusMember_rankOne_commute {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) {ψ : (ggU .POmegaMinus 4 f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K) (hrange : ψ.range = X)
    {ℓ : ↥Bs →* (ggU .POmegaMinus 4 f).K}
    (hℓ : ∀ (b : ↥Bs) (u : (ggU .POmegaMinus 4 f).K),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hkerℓ : ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G))
    (hZX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p)
    (hrankℓ : p ^ 3 ≤ Nat.card ℓ.range) {φ φ' : MulAut ↥Bs}
    (hφL : φ ∈ ggAutomizer X Bs) (hφ'L : φ' ∈ ggAutomizer X Bs) (hφ : GGIsReflection p φ)
    (hφ' : GGIsReflection p φ') (hcomm : φ * φ' = φ' * φ)
    (hcard : Nat.card ↥(ggRankOneIn X Bs φ) ≠ Nat.card ↥(ggRankOneIn X Bs φ')) :
    ∀ a ∈ ggRankOneIn X Bs φ, ∀ b ∈ ggRankOneIn X Bs φ', a * b = b * a := by
  obtain ⟨V, _, _, _, Q, ψΩ, τ, cv, hQ, -, -, -, -, hcvsurj, hU2, hA, -, hper⟩ :=
    plusMember_native hp hBs hNT hf hpq hker hrange hℓ hkerℓ hZX hrankℓ
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  have hK1 : ∀ c : GaloisField 2 f, c ^ p = 1 → c = 1 :=
    OmPlusFrame.eq_one_of_pow_eq_one_of_dvd_add_one hp hp2
      (by rw [GaloisField.card 2 f (by omega)]; exact hpq)
  obtain ⟨π, ε, hε, hcv⟩ := hA φ hφL
  obtain ⟨π', ε', hε', hcv'⟩ := hA φ' hφ'L
  obtain ⟨-, hbig, hsmall⟩ := hper φ hφL hφ π ε hε hcv
  obtain ⟨-, hbig', hsmall'⟩ := hper φ' hφ'L hφ' π' ε' hε' hcv'
  by_cases hπ : π = 1 <;> by_cases hπ' : π' = 1
  · exact absurd ((hbig hπ).1.trans (hbig' hπ').1.symm) hcard
  · obtain ⟨-, i₀, hi₀, hε₁, himg⟩ := hbig hπ
    obtain ⟨-, i, j, k, hij, hik, hjk, -, hjπ, hkπ, -, -, h, hne, hh, himg', hsb, hcs⟩ :=
      hsmall' hπ'
    subst hπ
    exact rankOne_commute_sign_transp hp2 hQ hK1 hcvsurj hU2 hcomm hcv hi₀ hε₁ himg hε' hcv'
      hij hik hjk hjπ hkπ hne hh himg' hsb hcs
  · obtain ⟨-, i₀, hi₀, hε₁, himg'⟩ := hbig' hπ'
    obtain ⟨-, i, j, k, hij, hik, hjk, -, hjπ, hkπ, -, -, h, hne, hh, himg, hsb, hcs⟩ :=
      hsmall hπ
    subst hπ'
    intro a ha b hb
    exact (rankOne_commute_sign_transp hp2 hQ hK1 hcvsurj hU2 hcomm.symm hcv' hi₀ hε₁ himg'
      hε hcv hij hik hjk hjπ hkπ hne hh himg hsb hcs b hb a ha).symm
  · exact absurd ((hsmall hπ).1.trans (hsmall' hπ').1.symm) hcard

theorem ggOppPlus_rankOne_commute_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGCentralImage .POmegaMinus 4 f L) {φ φ' : MulAut ↥Bs}
    (hφL : φ ∈ ggAutomizer L Bs) (hφ'L : φ' ∈ ggAutomizer L Bs) (hφ : GGIsReflection p φ)
    (hφ' : GGIsReflection p φ') (hcomm : φ * φ' = φ' * φ)
    (hcard : Nat.card ↥(ggRankOneIn L Bs φ) ≠ Nat.card ↥(ggRankOneIn L Bs φ')) :
    ∀ a ∈ ggRankOneIn L Bs φ, ∀ b ∈ ggRankOneIn L Bs φ', a * b = b * a := by
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hZL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hc.bstar_inf_centralizer_L, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxBs) hc.1.2.2.2.2.2.2.1.2.2.1]
  obtain ⟨ψ, hker, hrange, ℓ, hℓ, hkerℓ, -, hrankℓ⟩ :=
    F4KGPosition.exists_spinMinus_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg (Or.inl rfl)
      hmark
  exact plusMember_rankOne_commute hp hBs hcfg.1.2.2.2.1 hf hpq hker hrange hℓ hkerℓ hZL hrankℓ
    hφL hφ'L hφ hφ' hcomm hcard

theorem ggOppPlus_label2_commute_of_frame {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGCentralImage .POmegaMinus 4 f L)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {ι' : Type} {M' : CoxeterMatrix ι'} (ε : M'.Group ≃* ↥(ggAutomizer L Bs))
    (hεrefl : ∀ i, GGIsReflection p ((ε (M'.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι') (hM : ∀ k l, M' (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (w₀ : CoxeterMatrix.F₄.Group) (i₀ j₀ : Fin 4)
    (hi : ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (hj : ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (hl : CoxeterMatrix.F₄ i₀ j₀ = 2) :
    ∀ a ∈ ggRankOneIn L Bs ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs),
      ∀ b ∈ ggRankOneIn L Bs ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs), a * b = b * a := by
  classical
  have hc : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hc.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hALind : ggAutomizer L Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    exact hAind (Subgroup.mem_sup_left hφ)
  have hZL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hc.bstar_inf_centralizer_L, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxBs) hc.1.2.2.2.2.2.2.1.2.2.1]
  obtain ⟨ψ, hker, hrange, ℓ, hℓ, hkerℓ, -, hrankℓ⟩ :=
    F4KGPosition.exists_spinMinus_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg (Or.inl rfl)
      hmark
  obtain ⟨-, h3, h4, -⟩ := plusMember_facts hp hBs hNT hf hpq hker hrange hℓ hkerℓ hZL hrankℓ
  obtain ⟨φ, hφe, haR, -, -, -, -⟩ :=
    exists_f4Triple_map_of_weyl hp hp2 hBs hNT hAind hpres le_sup_left ε hεrefl σ hM
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hsimp : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs k, CoxeterMatrix.toCoxeterSystem_simple]
  let εs : Fin 3 → MulAut ↥Bs := fun k => ((ε (M'.simple (σ k)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hεs : ∀ k l, εs k * εs l = ((ε (M'.simple (σ k) * M'.simple (σ l)) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := fun k l => by
    rw [map_mul, Subgroup.coe_mul]
  have hrel : ∀ k l, (εs k * εs l) ^ (CoxeterMatrix.B 3 k l) = 1 := by
    intro k l
    have h := M'.toCoxeterSystem.simple_mul_simple_pow (σ k) (σ l)
    rw [hM] at h
    simp only [CoxeterMatrix.toCoxeterSystem_simple] at h
    rw [hεs, ← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]
  have hpow_ne : ∀ k l (n : ℕ), 0 < n → n < CoxeterMatrix.B 3 k l → (εs k * εs l) ^ n ≠ 1 := by
    intro k l n hn hlt h1
    have h2 : (M'.simple (σ k) * M'.simple (σ l)) ^ n = 1 := by
      apply ε.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, ← hεs]
      exact h1
    have hord := M'.toCoxeterSystem.orderOf_simple_mul_simple (σ k) (σ l)
    simp only [CoxeterMatrix.toCoxeterSystem_simple] at hord
    rw [hM] at hord
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    exact absurd (Nat.le_of_dvd hn hdvd) (by omega)
  have hne01 : εs 0 ≠ εs 1 := by
    intro h
    apply hpow_ne 0 1 1 (by norm_num) (by decide)
    rw [pow_one, h, ← pow_two]
    exact (hεrefl _).1
  have hc0 : Nat.card ↥(ggRankOneIn L Bs (εs 0)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
    h3 _ (ε _).2 _ (ε _).2 (hεrefl _) (hεrefl _) hne01 (hrel 0 1)
  have hc1 : Nat.card ↥(ggRankOneIn L Bs (εs 1)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
    h3 _ (ε _).2 _ (ε _).2 (hεrefl _) (hεrefl _) hne01.symm (hrel 1 0)
  have hc2 : Nat.card ↥(ggRankOneIn L Bs (εs 2)) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) :=
    (h4 _ (ε _).2 _ (ε _).2 (hεrefl _) (hεrefl _) (hrel 2 1)
      (hpow_ne 2 1 2 (by norm_num) (by decide))).mpr hc1
  have hMe : M' = (CoxeterMatrix.B 3).reindex σ := by
    ext i j
    change M' i j = CoxeterMatrix.B 3 (σ.symm i) (σ.symm j)
    simpa only [Equiv.apply_symm_apply] using hM (σ.symm i) (σ.symm j)
  have hW : GGIsWeylMatrix M' :=
    Or.inl ⟨3, σ, by decide, Or.inr (Or.inl ⟨by decide, hMe⟩)⟩
  have hG2 : ¬ ∃ e : Fin 2 ≃ ι', M' = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, -⟩
    have h := Fintype.card_congr (e.trans σ.symm)
    simp at h
  have hconj : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t → ∃ (k : Fin 3) (v : M'.Group),
      t = ((ε (v * M'.simple (σ k) * v⁻¹) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    intro t htL ht
    obtain ⟨i, v, hv⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs hNT
      (ggAutomizer L Bs) hALind ι' M' hW hG2 ε hεrefl ⟨t, htL⟩ ht
    refine ⟨σ.symm i, v, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val hv
  have hcardconj : ∀ (v : M'.Group) (k : Fin 3),
      Nat.card ↥(ggRankOneIn L Bs ((ε (v * M'.simple (σ k) * v⁻¹) : ↥(ggAutomizer L Bs)) :
        MulAut ↥Bs)) = Nat.card ↥(ggRankOneIn L Bs (εs k)) := by
    intro v k
    have hform : ((ε (v * M'.simple (σ k) * v⁻¹) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
        ((ε v : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) * εs k *
          ((ε v : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)⁻¹ := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨g, -, -, hg⟩ := exists_ggRankOneIn_conj_of_mem_ggAutomizer (ε v).2 (εs k)
    rw [hform, ← hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hclsφ : ∀ (w' : CoxeterMatrix.F₄.Group) (i' : Fin 4) (v : M'.Group) (k : Fin 3),
      ((e (w' * CoxeterMatrix.F₄.simple i' * w'⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) = ((ε (v * M'.simple (σ k) * v⁻¹) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) →
      R.cls (R.s i') = R.cls (φ (M'.simple (σ k))) := by
    intro w' i' v k h
    have hw : w' * CoxeterMatrix.F₄.simple i' * w'⁻¹ = φ v * φ (M'.simple (σ k)) * (φ v)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      apply e.injective
      apply Subtype.ext
      rw [h, hφe]
    have hsi : R.IsRefl (R.s i') := ⟨1, i', by group⟩
    have hφk : R.IsRefl (φ (M'.simple (σ k))) := (F4Model.F4Rep.isRefl_iff hRs).2 (haR k)
    rw [← R.cls_conj hsi w', hsimp, hw, R.cls_conj hφk]
  have hcls01 : R.cls (φ (M'.simple (σ 0))) = R.cls (φ (M'.simple (σ 1))) := by
    set a := M'.simple (σ 0) with ha
    set b := M'.simple (σ 1) with hb
    have ha2 : a * a = 1 := by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        M'.toCoxeterSystem.simple_mul_simple_self (σ 0)
    have hb2 : b * b = 1 := by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        M'.toCoxeterSystem.simple_mul_simple_self (σ 1)
    have h3' : (b * a) ^ 3 = 1 := by
      have h := M'.toCoxeterSystem.simple_mul_simple_pow (σ 1) (σ 0)
      rw [hM, show (CoxeterMatrix.B 3).M 1 0 = 3 by decide] at h
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using h
    have hthree : (b * a) * (b * a) * (b * a) = 1 := by
      simpa only [pow_succ, pow_zero, one_mul] using h3'
    have hfive : b * a * b * a * b = a := by
      have h := congrArg (fun z : M'.Group => z * a) hthree
      simpa only [mul_assoc, ha2, mul_one, one_mul] using h
    have hconj' : a = (b * a) * b * (b * a)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
      simpa only [mul_assoc] using hfive.symm
    have hφb : R.IsRefl (φ b) := (F4Model.F4Rep.isRefl_iff hRs).2 (haR 1)
    rw [hconj', map_mul, map_mul, map_inv, R.cls_conj hφb]
  have hsb := rk1c_card_ne hf
  have hcardk : ∀ k : Fin 3, Nat.card ↥(ggRankOneIn L Bs (εs k)) =
      if k = 2 then (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) else 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    intro k
    fin_cases k
    · exact hc0
    · exact hc1
    · exact hc2
  have hclsk : ∀ k k' : Fin 3, (k = 2 ↔ k' = 2) →
      R.cls (φ (M'.simple (σ k))) = R.cls (φ (M'.simple (σ k'))) := by
    intro k k' hkk
    fin_cases k <;> fin_cases k' <;> simp at hkk ⊢ <;> first | rfl | exact hcls01 | exact hcls01.symm
  have hrefl₁ := ggCoxRefl_isReflection hpres.2 ⟨w₀, i₀, rfl⟩
  have hrefl₂ := ggCoxRefl_isReflection hpres.2 ⟨w₀, j₀, rfl⟩
  obtain ⟨k₁, v₁, hv₁⟩ := hconj _ hi hrefl₁
  obtain ⟨k₂, v₂, hv₂⟩ := hconj _ hj hrefl₂
  have hcard : Nat.card ↥(ggRankOneIn L Bs ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) ≠
      Nat.card ↥(ggRankOneIn L Bs ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) := by
    intro heq
    rw [hv₁, hv₂, hcardconj, hcardconj, hcardk, hcardk] at heq
    have hkk : k₁ = 2 ↔ k₂ = 2 := by
      by_cases h₁ : k₁ = 2 <;> by_cases h₂ : k₂ = 2 <;> simp only [h₁, h₂, if_true, if_false] at heq
      · exact iff_of_true h₁ h₂
      · exact absurd heq.symm hsb
      · exact absurd heq hsb
      · exact iff_of_false h₁ h₂
    have hcl := (hclsφ w₀ i₀ v₁ k₁ hv₁).trans ((hclsk k₁ k₂ hkk).trans (hclsφ w₀ j₀ v₂ k₂ hv₂).symm)
    rw [R.cls_s, R.cls_s] at hcl
    have hmix : (i₀.val < 2 ↔ ¬ j₀.val < 2) := rk1c_f4_label_two (i₀, j₀) hl
    by_cases h₁ : i₀.val < 2
    · have h₂ : ¬ j₀.val < 2 := hmix.mp h₁
      simp only [h₁, h₂, if_true, if_false] at hcl
      exact absurd hcl (by decide)
    · have h₂ : j₀.val < 2 := by
        by_contra h₂
        exact h₁ (hmix.mpr h₂)
      simp only [h₁, h₂, if_true, if_false] at hcl
      exact absurd hcl (by decide)
  have hsij : CoxeterMatrix.F₄.simple i₀ * CoxeterMatrix.F₄.simple j₀ =
      CoxeterMatrix.F₄.simple j₀ * CoxeterMatrix.F₄.simple i₀ := by
    have h := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_pow i₀ j₀
    rw [show CoxeterMatrix.F₄.M i₀ j₀ = 2 from hl, pow_two] at h
    have h' := eq_inv_of_mul_eq_one_left h
    rw [mul_inv_rev, CoxeterSystem.inv_simple, CoxeterSystem.inv_simple] at h'
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using h'
  have hcomm : ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) *
      ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) =
      ((e (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) *
      ((e (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    calc w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹ * (w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹)
        = w₀ * (CoxeterMatrix.F₄.simple i₀ * CoxeterMatrix.F₄.simple j₀) * w₀⁻¹ := by group
      _ = w₀ * (CoxeterMatrix.F₄.simple j₀ * CoxeterMatrix.F₄.simple i₀) * w₀⁻¹ := by rw [hsij]
      _ = w₀ * CoxeterMatrix.F₄.simple j₀ * w₀⁻¹ * (w₀ * CoxeterMatrix.F₄.simple i₀ * w₀⁻¹) := by
          group
  exact ggOppPlus_rankOne_commute_of_cfg hcfg hf hpq hmark hi hj hrefl₁ hrefl₂ hcomm hcard

theorem ggF4QGeFourR3S1S3_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGCentralImage .POmegaMinus 4 f L)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    (hfam : GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e))
    {ι' : Type} {M' : CoxeterMatrix ι'} (ε : M'.Group ≃* ↥(ggAutomizer L Bs))
    (hεrefl : ∀ i, GGIsReflection p ((ε (M'.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι') (hM : ∀ k l, M' (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (w : CoxeterMatrix.F₄.Group) {u r' : MulAut ↥Bs}
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (hr' : r' = ((e (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (huL : u ∈ ggAutomizer L Bs) :
    ∃ n ∈ L ⊔ K, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((r' b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G) := by
  obtain ⟨hpp, hEl, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 := ggAutomizer_mono Bs le_top (hAH hφ)
    rw [ggAutomizer_eq] at h1
    exact h1
  have hcomm : u * r' = r' * u := by
    rw [hu, hr', ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    calc w * CoxeterMatrix.F₄.simple 1 * w⁻¹ * (w * CoxeterMatrix.F₄.simple 3 * w⁻¹)
        = w * (CoxeterMatrix.F₄.simple 1 * CoxeterMatrix.F₄.simple 3) * w⁻¹ := by group
      _ = w * (CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 1) * w⁻¹ := by
          rw [f4_simple_one_mul_three]
      _ = w * CoxeterMatrix.F₄.simple 3 * w⁻¹ * (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) := by group
  have hcS := commute_rankOneFamily_of_exists_conj hAH (ggRankOneFrom p L (L ⊔ K) Bs)
    (fun t ht htR => hfam.2.1 t ht (ggCoxRefl_isReflection hpres.2 htR))
    (fun h hh hhN g hg t _ => (hfam.2.2 h hh hhN g hg t).symm) ⟨w, 1, hu⟩ ⟨w, 3, hr'⟩
    (exists_conj_commPair_mixed_of_label2 hpp hp2 hEl hNT hAind hpres le_sup_left ε hεrefl σ hM
      (fun w₀ i₀ j₀ hi₀ hj₀ hl =>
        ggOppPlus_label2_commute_of_frame hcfg hf hpq hmark hpres ε hεrefl σ hM w₀ i₀ j₀ hi₀ hj₀
          hl)
      w w 1 3 (by decide) hu hr' hcomm)
  exact hfam.exists_centralizing_reflection_lift huL
    (ggCoxRefl_isReflection hpres.2 ⟨w, 1, hu⟩) ⟨w, 3, hr'⟩ hcS

end Main

end CFSG.StandardType

end
