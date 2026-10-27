module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddAct
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Frame
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

@[expose] def planeFix {K : Type*} [Group K] (Ē : Subgroup (MulAut K)) : Set K :=
  {k | ∃ ε ∈ Ē, ε ≠ 1 ∧ ε k = k}

@[expose] def SporPlaneConf (K : Type*) [Group K] (p : ℕ) (Ē R : Subgroup (MulAut K)) : Prop :=
  IsElemAbelian p Ē ∧ Nat.card Ē = p ^ 2 ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ Ē ≤ normalizer (R : Set (MulAut K)) ∧
    ∀ k ∈ planeFix Ē, MulAut.conj k ∈ normalizer (R : Set (MulAut K))

@[expose] def PlaneGenOrExc (K : Type*) [Group K] (p : ℕ) : Prop :=
  ∀ Ē : Subgroup (MulAut K), IsElemAbelian p Ē → Nat.card Ē = p ^ 2 →
    Subgroup.closure (planeFix Ē) = ⊤ ∨
      ((∀ N : Subgroup K, N ≤ Subgroup.closure (planeFix Ē) → IsPGroup 2 N →
          Subgroup.closure (planeFix Ē) ≤ normalizer (N : Set K) → N = ⊥) ∧
        ∀ α : MulAut K, (∀ k ∈ Subgroup.closure (planeFix Ē), α k = k) → Odd (orderOf α))

namespace Spor

section Aut

variable {K : Type*} [Group K]

theorem mul_conj_mul_inv (σ : MulAut K) (k : K) : σ * MulAut.conj k * σ⁻¹ = MulAut.conj (σ k) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem conj_injective (hZ : Subgroup.center K = ⊥) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hc : k ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj k g = g := by rw [hk]; rfl
    rw [MulAut.conj_apply] at h1
    calc g * k = (k * g * k⁻¹) * k := by rw [h1]
      _ = k * g := by group
  rw [hZ] at hc
  exact (Subgroup.mem_bot.1 hc)

theorem conj_commute_iff (hZ : Subgroup.center K = ⊥) (ε : MulAut K) (k : K) :
    ε * MulAut.conj k = MulAut.conj k * ε ↔ ε k = k := by
  constructor
  · intro h
    have h2 : ε * MulAut.conj k * ε⁻¹ = MulAut.conj k := by rw [h, mul_inv_cancel_right]
    rw [mul_conj_mul_inv] at h2
    exact conj_injective hZ h2
  · intro h
    have h2 : ε * MulAut.conj k * ε⁻¹ = MulAut.conj k := by rw [mul_conj_mul_inv, h]
    calc ε * MulAut.conj k = (ε * MulAut.conj k * ε⁻¹) * ε := by group
      _ = MulAut.conj k * ε := by rw [h2]

theorem conj_range_iff (ε x : MulAut K) :
    x ∈ (MulAut.conj : K →* MulAut K).range ↔ ε * x * ε⁻¹ ∈ (MulAut.conj : K →* MulAut K).range := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨ε k, (mul_conj_mul_inv ε k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨ε⁻¹ k, ?_⟩
    rw [← mul_conj_mul_inv, hk]
    group

theorem conj_mem_normalizer_of_mem_closure {Ē R : Subgroup (MulAut K)}
    (hfix : ∀ k ∈ planeFix Ē, MulAut.conj k ∈ normalizer (R : Set (MulAut K))) {k : K}
    (hk : k ∈ Subgroup.closure (planeFix Ē)) : MulAut.conj k ∈ normalizer (R : Set (MulAut K)) := by
  have hle : Subgroup.closure (planeFix Ē) ≤ (normalizer (R : Set (MulAut K))).comap MulAut.conj :=
    (Subgroup.closure_le _).2 fun k hk => hfix k hk
  exact hle hk

theorem conj_comm_mem {R : Subgroup (MulAut K)} {k : K} (hk : MulAut.conj k ∈ normalizer (R : Set (MulAut K)))
    {r : MulAut K} (hr : r ∈ R) : MulAut.conj (k * r k⁻¹) ∈ R := by
  have h1 : MulAut.conj k * r * (MulAut.conj k)⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hk r).1 hr
  have h2 : MulAut.conj k * r * (MulAut.conj k)⁻¹ * r⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem hr)
  have h3 : MulAut.conj k * r * (MulAut.conj k)⁻¹ * r⁻¹ = MulAut.conj (k * r k⁻¹) := by
    rw [map_mul, ← mul_conj_mul_inv, map_inv]
    group
  rwa [h3] at h2

theorem apply_eq_of_mul_apply_inv_eq_one {k : K} {r : MulAut K} (h : k * r k⁻¹ = 1) : r k = k := by
  rw [map_inv] at h
  exact (mul_inv_eq_one.1 h).symm

theorem apply_eq_of_conj_comm_eq_one (hZ : Subgroup.center K = ⊥) {k : K} {r : MulAut K}
    (h : MulAut.conj (k * r k⁻¹) = 1) : r k = k :=
  apply_eq_of_mul_apply_inv_eq_one (conj_injective hZ (h.trans (map_one _).symm))

end Aut

theorem eq_bot_of_forall_commute_eq_one {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {A N : Subgroup X} (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ 2) (hN : ¬ p ∣ Nat.card N)
    (hAN : A ≤ normalizer (N : Set X)) (h : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ N, a * x = x * a → x = 1) : N = ⊥ := by
  classical
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N (N.normalizerMonoidHom.comp (Subgroup.inclusion hAN))
  have hact : ∀ (a : A) (x : N), ((a • x : N) : X) = (a : X) * (x : X) * (a : X)⁻¹ := fun _ _ => rfl
  haveI : IsElementaryAbelian p A := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := A) (H := N)
    (by rw [hcard]) hN
  have hbot : ∀ a : A, a ≠ 1 → fixedPointSubgroup (Subgroup.zpowers a) N = ⊥ := by
    intro a ha
    rw [eq_bot_iff]
    intro x hx
    have hfix : a • x = x := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have h2 : (a : X) * (x : X) * (a : X)⁻¹ = (x : X) := by
      rw [← hact]
      exact congrArg Subtype.val hfix
    have h3 : (a : X) * (x : X) = (x : X) * (a : X) := by
      calc (a : X) * (x : X) = ((a : X) * (x : X) * (a : X)⁻¹) * (a : X) := by group
        _ = (x : X) * (a : X) := by rw [h2]
    have ha' : (a : X) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    exact Subgroup.mem_bot.2 (Subtype.ext (h a a.2 ha' x x.2 h3))
  have htop : (⊤ : Subgroup N) = ⊥ := by
    rw [← hgen]
    exact eq_bot_iff.2 (iSup₂_le fun a ha => (hbot a ha).le)
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hx'))

theorem not_dvd_card_of_isPGroup_two {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {N : Subgroup X} (hN : IsPGroup 2 N) : ¬ p ∣ Nat.card N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  rw [hn]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem not_sporPlaneConf_of_planeGenOrExc {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (hZ : Subgroup.center K = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : PlaneGenOrExc K p)
    {Ē R : Subgroup (MulAut K)} : ¬ SporPlaneConf K p Ē R := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨hE, hEc, hR2, hR1, hER, hfix⟩
  apply hR1
  rcases hK Ē hE hEc with hgen | ⟨hX1, hX2⟩
  ·
    have hinn : ∀ k : K, MulAut.conj k ∈ normalizer (R : Set (MulAut K)) := fun k =>
      conj_mem_normalizer_of_mem_closure hfix (hgen ▸ Subgroup.mem_top k)
    set N : Subgroup K := R.comap MulAut.conj with hNdef
    have hN2 : IsPGroup 2 N := hR2.comap_of_injective _ (conj_injective hZ)
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      change MulAut.conj (g * n * g⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hinn g) _).1 hn
    have hNbot : N = ⊥ := by
      rcases hNn.eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        have hK2 : IsPGroup 2 K := by
          intro g
          obtain ⟨n, hn⟩ := hN2 ⟨g, h ▸ Subgroup.mem_top g⟩
          exact ⟨n, by simpa using congrArg Subtype.val hn⟩
        haveI : Nontrivial K := IsSimpleGroup.toNontrivial
        have hlt := hK2.bot_lt_center
        rw [hZ] at hlt
        exact lt_irrefl _ hlt
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    ext k
    have hc : k * r k⁻¹ ∈ N := conj_comm_mem (hinn k) hr
    rw [hNbot, Subgroup.mem_bot] at hc
    exact apply_eq_of_mul_apply_inv_eq_one hc
  ·
    set H : Subgroup K := Subgroup.closure (planeFix Ē) with hHdef
    have hHn : ∀ k ∈ H, MulAut.conj k ∈ normalizer (R : Set (MulAut K)) := fun k hk =>
      conj_mem_normalizer_of_mem_closure hfix hk
    set N : Subgroup K := R.comap MulAut.conj ⊓ H with hNdef
    have hN2 : IsPGroup 2 N :=
      (hR2.comap_of_injective _ (conj_injective hZ)).to_le inf_le_left
    have hNH : H ≤ normalizer (N : Set K) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · rintro ⟨hnR, hnH⟩
        refine ⟨?_, H.mul_mem (H.mul_mem hh hnH) (H.inv_mem hh)⟩
        change MulAut.conj (h * n * h⁻¹) ∈ R
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 (hHn h hh) _).1 hnR
      · rintro ⟨hnR, hnH⟩
        have hnH' : n ∈ H := by
          have := H.mul_mem (H.mul_mem (H.inv_mem hh) hnH) hh
          simpa [mul_assoc] using this
        refine ⟨?_, hnH'⟩
        change MulAut.conj n ∈ R
        have h1 : MulAut.conj (h * n * h⁻¹) ∈ R := hnR
        rw [map_mul, map_mul, map_inv] at h1
        exact (Subgroup.mem_normalizer_iff.1 (hHn h hh) _).2 h1
    have hNbot : N = ⊥ := hX1 N inf_le_right hN2 hNH
    set R₀ : Subgroup (MulAut K) := R ⊓ (MulAut.conj : K →* MulAut K).range with hR₀def
    have hR₀2 : IsPGroup 2 R₀ := hR2.to_le inf_le_left
    have hER₀ : Ē ≤ normalizer (R₀ : Set (MulAut K)) := by
      intro ε hε
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hR := Subgroup.mem_normalizer_iff.1 (hER hε) x
      have hI := conj_range_iff ε x
      exact ⟨fun hx => ⟨hR.1 hx.1, hI.1 hx.2⟩, fun hx => ⟨hR.2 hx.1, hI.2 hx.2⟩⟩
    have hR₀bot : R₀ = ⊥ := by
      refine eq_bot_of_forall_commute_eq_one hE hEc (not_dvd_card_of_isPGroup_two hp hp2 hR₀2) hER₀ ?_
      rintro ε hε hε1 x ⟨hxR, k, rfl⟩ hcomm
      have hfixk : ε k = k := (conj_commute_iff hZ ε k).1 hcomm
      have hkH : k ∈ H := Subgroup.subset_closure ⟨ε, hε, hε1, hfixk⟩
      have hkN : k ∈ N := ⟨hxR, hkH⟩
      rw [hNbot, Subgroup.mem_bot] at hkN
      rw [hkN, map_one]
    rw [eq_bot_iff]
    intro r hr
    have hrH : ∀ k ∈ H, r k = k := by
      intro k hk
      have hc : MulAut.conj (k * r k⁻¹) ∈ R₀ := ⟨conj_comm_mem (hHn k hk) hr, _, rfl⟩
      rw [hR₀bot, Subgroup.mem_bot] at hc
      exact apply_eq_of_conj_comm_eq_one hZ hc
    have hodd := hX2 r hrH
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hR2) ⟨r, hr⟩
    rw [Subgroup.orderOf_mk] at hn
    rcases n with _ | n
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      exact Subgroup.mem_bot.2 hn
    · exfalso
      rw [hn] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero n⟩)

end Spor

namespace Hyp36

open Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem congr_actHom_of_mem (L : Subgroup G) [L.Normal] {K : Type*} [Group K]
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* K) {m : G} (hm : m ∈ L) :
    MulAut.congr φ (actHom L m) = MulAut.conj (φ (QuotientGroup.mk ⟨m, hm⟩)) := by
  ext k
  obtain ⟨c, rfl⟩ := φ.surjective k
  induction c using QuotientGroup.induction_on with
  | H y =>
    have h1 : actHom L m (QuotientGroup.mk y) =
        QuotientGroup.mk ⟨m, hm⟩ * QuotientGroup.mk y * (QuotientGroup.mk ⟨m, hm⟩)⁻¹ := by
      rw [actHom_apply_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h1, map_mul, map_mul, map_inv, MulAut.conj_apply]

theorem exists_sporPlaneConf (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {K : Type*} [Group K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* K) :
    ∃ Ē R : Subgroup (MulAut K), SporPlaneConf K p Ē R := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  by_cases hfaith : ∀ e ∈ E, e ≠ 1 → ∃ y ∈ L, e * y * e⁻¹ * y⁻¹ ∉ centerOf L
  swap
  · exfalso
    push Not at hfaith
    obtain ⟨e, he, he1, hall⟩ := hfaith
    have hcent := centralizes_of_forall_comm_mem L hLc hall
    refine h.false_of_component_le hL hne fun y hy => ?_
    exact h.centralizer_le_of_ne_one he he1
      (Subgroup.mem_centralizer_singleton_iff.2 (hcent y hy).symm)
  let Ψ : G →* MulAut K := (MulAut.congr φ).toMonoidHom.comp (actHom L)
  have hΨ : ∀ (g : G) (y : G) (hy : y ∈ L),
      Ψ g (φ (QuotientGroup.mk ⟨y, hy⟩)) = φ (QuotientGroup.mk ⟨y, hy⟩) ↔
        g * y * g⁻¹ * y⁻¹ ∈ centerOf L := by
    intro g y hy
    have h1 : Ψ g (φ (QuotientGroup.mk ⟨y, hy⟩)) = φ (actHom L g (QuotientGroup.mk ⟨y, hy⟩)) := by
      change (MulAut.congr φ) (actHom L g) (φ _) = _
      simp [MulAut.congr_apply]
    rw [h1, φ.injective.eq_iff, actHom_mk_eq_iff]
  have hΨ1 : ∀ e ∈ E, Ψ e = 1 → e = 1 := by
    intro e he hΨe
    by_contra he1
    obtain ⟨y, hy, hy'⟩ := hfaith e he he1
    apply hy'
    rw [← hΨ e y hy, hΨe]
    rfl
  have hinj : Function.Injective (Ψ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    exact Subtype.ext (hΨ1 e e.2 he)
  have hcard : Nat.card (E.map Ψ) = p ^ 2 := by
    have hr : (Ψ.comp E.subtype).range = E.map Ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← h.card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  set Q := pCoreOf 2 M with hQdef
  have hQn : M ≤ normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hΨn : ∀ g ∈ M, Ψ g ∈ normalizer ((Q.map Ψ : Subgroup (MulAut K)) : Set (MulAut K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨g * q * g⁻¹, (Subgroup.mem_normalizer_iff.1 (hQn hg) q).1 hq, by simp [map_mul, map_inv]⟩
    · rintro ⟨q', hq', hq'x⟩
      refine ⟨g⁻¹ * q' * g, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hQn (M.inv_mem hg)) q').1 hq'
        simpa [mul_assoc] using this
      · rw [map_mul, map_mul, map_inv, hq'x]
        group
  refine ⟨E.map Ψ, Q.map Ψ, CFSG.Open.IsElemAbelian.map h.elem Ψ, hcard,
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).map Ψ, ?_, ?_, ?_⟩
  ·
    intro hbot
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq1 : Ψ q = 1 := by
      have : Ψ q ∈ Q.map Ψ := Subgroup.mem_map_of_mem Ψ hq
      rwa [hbot, Subgroup.mem_bot] at this
    have hall : ∀ y' ∈ L, q * y' * q⁻¹ * y'⁻¹ ∈ centerOf L := by
      intro y' hy'
      rw [← hΨ q y' hy', hq1]
      rfl
    exact centralizes_of_forall_comm_mem L hLc hall y hy
  ·
    rintro _ ⟨e, he, rfl⟩
    exact hΨn e (h.E_le he)
  ·
    rintro k ⟨ε, hε, hε1, hεk⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hε
    have he1 : e ≠ 1 := fun h1 => hε1 (by rw [h1, map_one])
    obtain ⟨c, rfl⟩ := φ.surjective k
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨m, hm, z, hz, hyz⟩ := h.mem_mul_centerOf_of_fixed L he he1 hy ((hΨ e y hy).1 hεk)
    have hk : φ (QuotientGroup.mk ⟨y, hy⟩) = φ (QuotientGroup.mk ⟨m, hm.2⟩) := by
      rw [φ.injective.eq_iff, QuotientGroup.eq, mem_center_iff_mem_centerOf]
      have : (((⟨y, hy⟩ : ↥L)⁻¹ * ⟨m, hm.2⟩ : ↥L) : G) = y⁻¹ * m := rfl
      rw [this, hyz]
      have hz' : z⁻¹ ∈ centerOf L := (centerOf L).inv_mem hz
      simpa [mul_assoc] using hz'
    rw [hk, ← congr_actHom_of_mem L φ hm.2]
    exact hΨn m hm.1

theorem false_of_planeGen (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {K : Type*} [Group K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* K)
    (hK : PlaneGenOrExc K p) : False := by
  haveI : Finite K := Finite.of_equiv _ φ.toEquiv
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  haveI : IsSimpleGroup K := φ.symm.isSimpleGroup
  have hZ : Subgroup.center K = ⊥ := by
    rcases (Subgroup.center K).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := hL.1.2.2
      apply hab
      apply φ.injective
      have hb : φ b ∈ Subgroup.center K := hc ▸ Subgroup.mem_top _
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 hb (φ a)
  obtain ⟨Ē, R, hconf⟩ := h.exists_sporPlaneConf hL hne φ
  exact Spor.not_sporPlaneConf_of_planeGenOrExc hZ h.prime h.odd hK hconf

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
