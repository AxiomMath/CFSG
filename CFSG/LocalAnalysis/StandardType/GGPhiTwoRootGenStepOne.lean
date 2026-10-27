module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7StepAux
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcG2Three
public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative

private theorem mul_conj_mul_inv {G : Type*} [Group G] (a x : G) :
    a * (a⁻¹ * x * a) * a⁻¹ = x := by group

private theorem conj_inv_eq_mulAut {G : Type*} [Group G] (a x : G) :
    a⁻¹ * x * a = (MulAut.conj a⁻¹) x := by
  rw [MulAut.conj_apply, inv_inv]

private theorem card_torusSet_eq_card_fixed {p n : ℕ} {G H : Type*} [Group G] [Group H]
    {T : Multiplicative (Fin n → ZMod p) →* H} (hT : Function.Injective T)
    {Ψ' : G →* H} (hΨ' : Function.Injective Ψ')
    {E : Subgroup G} {tau : (Fin n → Multiplicative (ZMod p)) →* G}
    (htau : Function.Injective tau) (hE : E = T.range.comap Ψ') (htauE : tau.range = E)
    (s : MulAut (Fin n → Multiplicative (ZMod p))) :
    Nat.card {t : Fin n → ZMod p // ∃ f, s f = f ∧ Ψ' (tau f) = T (ofAdd t)}
      = Nat.card {f : Fin n → Multiplicative (ZMod p) // s f = f} := by
  classical
  have hex : ∀ x : G, x ∈ E → ∃ t : Fin n → ZMod p, T (ofAdd t) = Ψ' x := by
    intro x hx
    have h1 : Ψ' x ∈ T.range := by
      rw [hE] at hx
      exact hx
    exact h1
  have hmem : ∀ f : Fin n → Multiplicative (ZMod p), tau f ∈ E := by
    intro f
    rw [← htauE]
    exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : {t : Fin n → ZMod p // ∃ f, s f = f ∧ Ψ' (tau f) = T (ofAdd t)} =>
      (⟨Classical.choose t.2, (Classical.choose_spec t.2).1⟩ :
        {f : Fin n → Multiplicative (ZMod p) // s f = f})) ⟨?_, ?_⟩)
  · rintro ⟨t1, ht1⟩ ⟨t2, ht2⟩ heq
    have hf : Classical.choose ht1 = Classical.choose ht2 := congrArg Subtype.val heq
    have h1 : T (ofAdd t1) = T (ofAdd t2) := by
      rw [← (Classical.choose_spec ht1).2, ← (Classical.choose_spec ht2).2, hf]
    exact Subtype.ext ((Multiplicative.ofAdd).injective (hT h1))
  · intro g
    have hspec := Classical.choose_spec (hex (tau g.1) (hmem g.1))
    have hmem' : (Classical.choose (hex (tau g.1) (hmem g.1))) ∈
        {t : Fin n → ZMod p | ∃ f, s f = f ∧ Ψ' (tau f) = T (ofAdd t)} :=
      ⟨g.1, g.2, hspec.symm⟩
    refine ⟨⟨Classical.choose (hex (tau g.1) (hmem g.1)), hmem'⟩, ?_⟩
    refine Subtype.ext ?_
    have h3 : Ψ' (tau (Classical.choose hmem')) =
        T (ofAdd (Classical.choose (hex (tau g.1) (hmem g.1)))) :=
      (Classical.choose_spec hmem').2
    exact htau (hΨ' (h3.trans hspec))

private theorem selfCentralizing_torusModel
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hTcoe : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {G : Type} [Group G] {Ψ : G →* adjointGroup τ K} (hΨ : Function.Injective Ψ)
    {E : Subgroup G} (hEeq : E.map Ψ = T.range) :
    ∀ g : G, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E := by
  intro g hgc hgp
  set d : (Fin τ.rank → ZMod p) → ModGL τ (AlgebraicClosure K) :=
    fun t => rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) with hd
  set w : ModGL τ (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (Ψ g : ModGL τ K) with hw
  have hdT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) = g0 * d t * g0⁻¹ :=
    fun t => hTcoe t
  have hy_adj : g0⁻¹ * w * g0 ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (mul_mem (inv_mem hg0C)
      (CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup
        (algebraMap K (AlgebraicClosure K)) (Ψ g).2)) hg0C
  have hcommw : ∀ t : Fin τ.rank → ZMod p,
      w * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) * w := by
    intro t
    have hcomm : (Ψ g) * T (ofAdd t) = T (ofAdd t) * (Ψ g) := by
      have hmem : T (ofAdd t) ∈ E.map Ψ := by
        rw [hEeq]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hmem
      have h1 : Ψ (g * e) = Ψ (e * g) := by rw [hgc e he]
      rwa [map_mul, map_mul, hee] at h1
    have h2 := congrArg (fun z : adjointGroup τ K =>
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K)) hcomm
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← hw] at h2
  have hy_comm : ∀ t : Fin τ.rank → ZMod p, (g0⁻¹ * w * g0) * d t = d t * (g0⁻¹ * w * g0) := by
    intro t
    have hXt : w * (g0 * d t * g0⁻¹) = (g0 * d t * g0⁻¹) * w := by
      rw [← hdT t]
      exact hcommw t
    calc (g0⁻¹ * w * g0) * d t = g0⁻¹ * (w * (g0 * d t * g0⁻¹)) * g0 :=
          ggPhiTwoStep_conj_mul_assoc g0 w (d t)
      _ = g0⁻¹ * ((g0 * d t * g0⁻¹) * w) * g0 := by rw [hXt]
      _ = d t * (g0⁻¹ * w * g0) := ggPhiTwoStep_conj_mul_conj g0 (d t) w
  have hg_pow : (Ψ g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have hw_pow : w ^ p = 1 := by
    rw [hw, ← map_pow, ← Subgroup.coe_pow, hg_pow, Subgroup.coe_one, map_one]
  have hy_pow : (g0⁻¹ * w * g0) ^ p = 1 := by
    have hyw : g0⁻¹ * w * g0 = (MulAut.conj g0⁻¹) w := conj_inv_eq_mulAut g0 w
    rw [hyw, ← map_pow, hw_pow, map_one]
  have hy_torus : g0⁻¹ * w * g0 ∈ torusGroup τ (AlgebraicClosure K) :=
    mem_torusGroup_of_forall_commute_zetaVec hp2 hζo hζ hy_adj hy_comm
  obtain ⟨t, ht⟩ := ggPhiTwoStep_exists_rootDiagUnit_zetaVec_eq_of_pow_eq_one hζo hζ hy_torus hy_pow
  have ht' : g0⁻¹ * w * g0 = d t := ht
  have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) (Ψ g : ModGL τ K)
      = baseChangeGL (algebraMap K (AlgebraicClosure K)) (T (ofAdd t) : ModGL τ K) := by
    rw [← hw, hdT t, ← ht']
    exact (mul_conj_mul_inv g0 w).symm
  have hTeq : Ψ g = T (ofAdd t) := by
    refine Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hbc)
  have h1 : Ψ g ∈ E.map Ψ := by
    rw [hEeq]
    exact MonoidHom.mem_range.mpr ⟨ofAdd t, hTeq.symm⟩
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp h1
  rwa [hΨ hyg] at hy

theorem range_le_iSup_phiTwoComp_of_ggTorusModelAt
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K} (hTinj : Function.Injective T)
    (hTcoe : ∀ t : Fin τ.rank → ZMod p, baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
      g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {G : Type} [Group G] {Ψ : G →* adjointGroup τ K} (hΨ : Function.Injective Ψ)
    (hTΨ : T.range ≤ Ψ.range)
    (hmodel : CFSG.Open.IsElemAbelian p (T.range.comap Ψ) →
      (∀ g : G, (∀ x ∈ T.range.comap Ψ, g * x = x * g) → g ^ p = 1 → g ∈ T.range.comap Ψ) →
        GGTorusModelAt p (T.range.comap Ψ)) :
    Ψ.range ≤ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1 := by
  classical
  have hp : p.Prime := Fact.out
  let E : Subgroup G := T.range.comap Ψ
  have hEeq : E.map Ψ = T.range := Subgroup.map_comap_eq_self hTΨ
  have hcardT : Nat.card T.range = p ^ τ.rank := by
    have h1 : Nat.card (Multiplicative (Fin τ.rank → ZMod p)) = p ^ τ.rank := by
      change Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank
      rw [Nat.card_fun]
      simp [Nat.card_zmod]
    rw [← h1]
    exact Nat.card_congr (Equiv.ofInjective T hTinj).symm
  have hcardE : Nat.card E = p ^ τ.rank := by
    have h1 : Nat.card (E.map Ψ) = Nat.card E := Subgroup.card_map_of_injective hΨ
    rw [hEeq] at h1
    rw [← h1, hcardT]
  have hEelem : CFSG.Open.IsElemAbelian p E := by
    constructor
    · rw [isMulCommutative_iff]
      intro a b
      have ha : Ψ a ∈ T.range := hEeq ▸ Subgroup.mem_map_of_mem _ a.2
      have hb : Ψ b ∈ T.range := hEeq ▸ Subgroup.mem_map_of_mem _ b.2
      obtain ⟨ta, hta⟩ := ha
      obtain ⟨tb, htb⟩ := hb
      refine Subtype.ext ?_
      refine hΨ ?_
      show Ψ ((a : G) * (b : G)) = Ψ ((b : G) * (a : G))
      rw [map_mul, map_mul, ← hta, ← htb, ← map_mul, ← map_mul, mul_comm]
    · intro a ha
      have haT : Ψ a ∈ T.range := hEeq ▸ Subgroup.mem_map_of_mem _ ha
      obtain ⟨t, ht⟩ := haT
      have hpt : t ^ p = 1 := by
        rw [← ofAdd_toAdd t, ← ofAdd_nsmul]
        have h0 : (p : ℕ) • t.toAdd = 0 := by
          funext j
          show p • (t.toAdd j) = 0
          rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rw [h0, ofAdd_zero]
      have h1 : Ψ (a ^ p) = 1 := by
        rw [map_pow, ← ht, ← map_pow, hpt, map_one]
      exact hΨ (by rw [h1, map_one])
  have hsc : ∀ g : G, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E :=
    selfCentralizing_torusModel hp2 hζo hζ hg0C hTcoe hΨ hEeq
  obtain ⟨k, τ', ι, w', s, S, hι, hτinj, hτrange, hws, hs, hfix, hsinj, hwS, hcomp, hdvd,
    hgen⟩ := hmodel hEelem hsc
  have hcardpk : ∀ k : ℕ, Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
    intro k
    change Nat.card (Fin k → ZMod p) = p ^ k
    rw [Nat.card_fun]
    simp [Nat.card_zmod]
  have hk : k = τ.rank := by
    have hcardrange : Nat.card τ'.range = Nat.card (Fin k → Multiplicative (ZMod p)) :=
      Nat.card_congr (Equiv.ofInjective τ' hτinj).symm
    have h1 : p ^ k = p ^ τ.rank := by
      rw [← hcardpk k, ← hcardrange, hτrange, hcardE]
    exact Nat.pow_right_injective hp.two_le h1
  subst hk
  have hrank : 0 < τ.rank := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hfix_card (i : ι) :
      Nat.card {f : Fin τ.rank → Multiplicative (ZMod p) // s i f = f} =
        p ^ (τ.rank - 1) := by
    have h := hfix i
    rw [hcardpk] at h
    have hpow : p ^ τ.rank = p ^ (τ.rank - 1) * p := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : τ.rank ≠ 0)
      rw [hr, Nat.succ_sub_one, pow_succ]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  let V : ι → Set (Fin τ.rank → ZMod p) := fun i =>
    {t | ∃ f : Fin τ.rank → Multiplicative (ZMod p), s i f = f ∧ Ψ (τ' f) = T (ofAdd t)}
  have hV_card (i : ι) : Nat.card {t : Fin τ.rank → ZMod p // t ∈ V i} =
      p ^ (τ.rank - 1) := by
    rw [← hfix_card i]
    exact card_torusSet_eq_card_fixed hTinj hΨ hτinj rfl hτrange (s i)
  have hV_ncard (i : ι) : (V i).ncard = p ^ (τ.rank - 1) := by
    rw [← Nat.card_coe_set_eq]
    exact hV_card i
  have hperfect : ∀ i : ι, ⁅(S i).map Ψ, (S i).map Ψ⁆ = (S i).map Ψ := by
    intro i
    have hq : CFSG.Assembly.IsQuasisimple ↥(S i) := (hcomp i).2.2
    have hcomm : commutator ↥(S i) = ⊤ := hq.1
    have hmt : (⊤ : Subgroup ↥(S i)).map (S i).subtype = S i := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have h2 : ⁅S i, S i⁆ = S i := by
      have h4 : (commutator ↥(S i)).map (S i).subtype = S i := by
        rw [hcomm]
        exact hmt
      rwa [show commutator ↥(S i) = ⁅(⊤ : Subgroup ↥(S i)), ⊤⁆ from rfl,
        Subgroup.map_commutator, hmt] at h4
    rw [← Subgroup.map_commutator, h2]
  have hcent : ∀ (i : ι) (x : adjointGroup τ K), x ∈ (S i).map Ψ →
      ∀ t ∈ V i, x * T (ofAdd t) = T (ofAdd t) * x := by
    intro i x hx t ht
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨f, hf, hft⟩ := ht
    have h1 : S i ≤ Subgroup.centralizer (τ' '' {f | s i f = f}) := (hcomp i).1
    have h3 : y * τ' f = τ' f * y :=
      (Subgroup.mem_centralizer_iff.mp (h1 hy) (τ' f) ⟨f, hf, rfl⟩).symm
    rw [← hft, ← map_mul, ← map_mul, h3]
  have hfamily : (⨆ i : ι, (S i).map Ψ) ≤
      ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1 :=
    iSup_le_iSup_phiTwoComp_of_hyperplane_family hτ hp2 hg0C hζo hζ hTcoe
      (fun i => (S i).map Ψ) hperfect (fun i => ⟨V i, hV_ncard i, hcent i⟩)
  obtain ⟨j⟩ := hι
  have hle : (⨆ (i : ι) (_ : i ≠ j), S i).map Ψ ≤
      ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1 := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun _ => le_trans (le_iSup (fun i => (S i).map Ψ) i) hfamily
  rintro y ⟨g, rfl⟩
  refine hle (Subgroup.mem_map_of_mem Ψ ?_)
  rw [hgen j]
  exact Subgroup.mem_top _

end CFSG.StandardType.PhiTwoRootGen

end
