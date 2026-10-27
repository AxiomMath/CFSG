module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.LocalAnalysis.StandardType.GGTorusGenCentIrred
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFree
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthSplitFour

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [CharP K 2] in
private instance finite_linearEquiv_orth : Finite (V ≃ₗ[K] V) := by
  haveI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun _ _ h => LinearEquiv.ext (congrFun h)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem exists_ne_one_of_three_le_card_orth (hp : p.Prime) (hE3 : p ^ 3 ≤ Nat.card E) :
    ∃ b ∈ E, b ≠ 1 := by
  have hE1 : 1 < Nat.card E := by
    have h8 : 8 ≤ p ^ 3 := by simpa using Nat.pow_le_pow_left hp.two_le 3
    omega
  have hEn : E ≠ ⊥ := fun hbot => by rw [hbot] at hE1; simp at hE1
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEn
  exact ⟨b, b.2, fun h => hb1 (Subtype.ext h)⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem tau_range_eq {τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)}
    {F : SevOm.Frame Q p E r}
    (hτF : ∀ f, τ f = F.ι (OrthTorus.piMul r p f)) : τ.range = E := by
  rw [← F.range]
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨OrthTorus.piMul r p f, (hτF f).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(OrthTorus.piMul r p).symm t, by rw [hτF, MulEquiv.apply_symm_apply]⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem three_le_r_of_frame (hp : p.Prime)
    {τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)}
    {F : SevOm.Frame Q p E r}
    (hτF : ∀ f, τ f = F.ι (OrthTorus.piMul r p f)) (hE3 : p ^ 3 ≤ Nat.card E) :
    3 ≤ r := by
  have hτrange := tau_range_eq hτF
  have hτinj : Function.Injective τ := by
    intro f g h
    have h1 : F.ι (OrthTorus.piMul r p f) = F.ι (OrthTorus.piMul r p g) := by
      rw [← hτF f, ← hτF g, h]
    exact (OrthTorus.piMul r p).injective (F.inj h1)
  have hcardDom : Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := by
    rw [Nat.card_fun, Nat.card_fin]
    exact congrArg (· ^ r) (Nat.card_zmod p)
  have hcardE : Nat.card (Fin r → Multiplicative (ZMod p)) = Nat.card E :=
    Nat.card_congr ((MonoidHom.ofInjective hτinj).toEquiv.trans
      (MulEquiv.subgroupCongr hτrange).toEquiv)
  have hpr : p ^ r = Nat.card E := by rw [← hcardDom, hcardE]
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rw [hpr]; exact hE3)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem irreducible_of_frame (hp : p.Prime) (hp2 : p ≠ 2)
    {τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)}
    {F : SevOm.Frame Q p E r}
    (hτF : ∀ f, τ f = F.ι (OrthTorus.piMul r p f))
    (hperm : ∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    (hdinv : ∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f,
      w * τ f * w⁻¹ = τ (NbrOrth.dinv i j f))
    (hr : 3 ≤ r) :
    ∀ B : Subgroup (V ≃ₗ[K] V), B ≤ E →
      (∀ w ∈ orthDerived Q, (∀ c ∈ E, w * c * w⁻¹ ∈ E) →
        ∀ b ∈ B, w * b * w⁻¹ ∈ B) → B = ⊥ ∨ B = E := by
  intro B hBE hBN
  have hτrange := tau_range_eq hτF
  let N : Set (V ≃ₗ[K] V) := {w | w ∈ orthDerived Q ∧ ∀ c ∈ E, w * c * w⁻¹ ∈ E}
  have hpermN : ∀ σ : Equiv.Perm (Fin r), ∃ w ∈ N, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.permAut σ f) := by
    intro σ
    obtain ⟨w, hw, hws⟩ := hperm σ
    refine ⟨w, ⟨hw, ?_⟩, hws⟩
    intro c hc
    rw [← hτrange] at hc ⊢
    obtain ⟨f, rfl⟩ := hc
    exact ⟨SpCoord.permAut σ f, (hws f).symm⟩
  have hdinvN : ∀ i j : Fin r, i ≠ j → ∃ w ∈ N, ∀ f,
      w * τ f * w⁻¹ = τ (NbrOrth.dinv i j f) := by
    intro i j hij
    obtain ⟨w, hw, hws⟩ := hdinv i j hij
    refine ⟨w, ⟨hw, ?_⟩, hws⟩
    intro c hc
    rw [← hτrange] at hc ⊢
    obtain ⟨f, rfl⟩ := hc
    exact ⟨NbrOrth.dinv i j f, (hws f).symm⟩
  rcases eq_bot_or_eq_range_of_conj hp hp2 hr τ hpermN hdinvN
    (by rw [hτrange]; exact hBE) (fun w hw => hBN w hw.1 hw.2) with hB | hB
  · exact Or.inl hB
  · exact Or.inr (by rw [hB, hτrange])

omit [CharP K 2] in
private theorem exists_max_order (hp : p.Prime) (hEΩ : E ≤ orthDerived Q)
    (hEp : ∀ c ∈ E, c ^ p = 1) (hEc : ∀ c ∈ E, ∀ d ∈ E, c * d = d * c)
    (hne : ∃ b ∈ E, b ≠ 1) :
    ∃ e : ℕ, (∃ y₀ ∈ orthDerived Q, (∀ c ∈ E, y₀ * c = c * y₀) ∧ orderOf y₀ = p ^ e) ∧
      ∀ y ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
        (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let P : ℕ → Prop := fun k => ∃ y ∈ orthDerived Q,
    (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ k
  have hP1 : P 1 := by
    obtain ⟨b, hbE, hb1⟩ := hne
    exact ⟨b, hEΩ hbE, fun c hc => hEc b hbE c hc,
      by simpa using orderOf_eq_prime (hEp b hbE) hb1⟩
  have hPbound : ∀ k, P k → k ≤ Nat.card ↥(orthDerived Q) := by
    rintro k ⟨y, hy, -, hyord⟩
    have hle : p ^ k ≤ Nat.card ↥(orthDerived Q) :=
      Nat.le_of_dvd Nat.card_pos (by rw [← hyord]; exact Subgroup.orderOf_dvd_natCard _ hy)
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self (n := k)
    have h2p : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
    omega
  let e : ℕ := Nat.findGreatest P (Nat.card ↥(orthDerived Q))
  have heP : P e :=
    Nat.findGreatest_spec (P := P)
      (by have := Nat.card_pos (α := ↥(orthDerived Q)); omega) hP1
  have hemax : ∀ k, P k → k ≤ e := fun k hk =>
    Nat.le_findGreatest (P := P) (hPbound k hk) hk
  obtain ⟨y₀, hy₀Ω, hy₀E, hy₀ord⟩ := heP
  have hexp : ∀ y ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
      (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1 := by
    intro y hy hyE hyp
    obtain ⟨k, hk⟩ := hyp
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk)
    have hje : j ≤ e := hemax j ⟨y, hy, hyE, hj⟩
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hj]; exact Nat.pow_dvd_pow p hje)
  exact ⟨e, ⟨y₀, hy₀Ω, hy₀E, hy₀ord⟩, hexp⟩

private theorem permAut_swap_mulSingle (j k : Fin r) :
    SpCoord.permAut (Equiv.swap j k) (Pi.mulSingle j (ofAdd (1 : ZMod p))) =
      Pi.mulSingle k (ofAdd (1 : ZMod p)) := by
  apply SpCoord.eq_of_toAdd_eq
  intro m
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
    SpCoord.toAdd_mulSingle, SpCoord.toAdd_mulSingle]
  have hiff : ((Equiv.swap j k) m = j) ↔ (m = k) := by
    constructor
    · intro h
      simpa [h] using (Equiv.swap_apply_self j k m).symm
    · intro h
      simpa [h] using Equiv.swap_apply_right j k
  by_cases hm : m = k
  · rw [if_pos (hiff.mpr hm), if_pos hm]
  · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem exists_conj_single_orth {τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)}
    {F : SevOm.Frame Q p E r}
    (hτF : ∀ f, τ f = F.ι (OrthTorus.piMul r p f))
    (hperm : ∀ σ : Equiv.Perm (Fin r), ∃ w ∈ orthDerived Q, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) :
    ∀ j k : Fin r, ∃ w ∈ orthDerived Q, (∀ c ∈ E, w * c * w⁻¹ ∈ E) ∧
      w * F.ι (ofAdd (Pi.single j (1 : ZMod p))) * w⁻¹ =
        F.ι (ofAdd (Pi.single k (1 : ZMod p))) := by
  intro j k
  have hpi : ∀ j : Fin r,
      OrthTorus.piMul r p (Pi.mulSingle j (ofAdd (1 : ZMod p))) =
        ofAdd (Pi.single j (1 : ZMod p)) := by
    intro j
    apply toAdd.injective
    funext i
    rw [OrthTorus.piMul_apply, toAdd_ofAdd, SpCoord.toAdd_mulSingle, toAdd_ofAdd,
      Pi.single_apply]
  have hτ : ∀ j : Fin r, τ (Pi.mulSingle j (ofAdd (1 : ZMod p))) =
      F.ι (ofAdd (Pi.single j (1 : ZMod p))) := fun j => by rw [hτF, hpi j]
  have hτrange := tau_range_eq hτF
  obtain ⟨w, hw, hws⟩ := hperm (Equiv.swap j k)
  refine ⟨w, hw, ?_, ?_⟩
  · intro c hc
    rw [← hτrange] at hc ⊢
    obtain ⟨f, rfl⟩ := hc
    exact ⟨SpCoord.permAut (Equiv.swap j k) f, (hws f).symm⟩
  · calc w * F.ι (ofAdd (Pi.single j (1 : ZMod p))) * w⁻¹
        = w * τ (Pi.mulSingle j (ofAdd (1 : ZMod p))) * w⁻¹ := by rw [hτ j]
      _ = τ (SpCoord.permAut (Equiv.swap j k)
            (Pi.mulSingle j (ofAdd (1 : ZMod p)))) := hws _
      _ = τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) := by rw [permAut_swap_mulSingle j k]
      _ = F.ι (ofAdd (Pi.single k (1 : ZMod p))) := hτ k

theorem exists_mem_of_isComponentOf (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) {e : ℕ}
    (hcomm : ∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
      (∀ c ∈ E, y' * c = c * y') → (∃ k : ℕ, y ^ p ^ k = 1) → (∃ k : ℕ, y' ^ p ^ k = 1) →
      y * y' = y' * y)
    (hz : ∀ k, ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v)
    {x : V ≃ₗ[K] V} (hx : x ∈ E) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {x})) :
    ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  classical
  obtain ⟨s, hs⟩ := SevOm.Frame.exists_eq F hx
  subst hs
  have hxIso : OddOrderIsometry Q p (F.ι s) := F.oddOrderIsometry hQ hp2 hp hEΩ s
  have hL : CFSG.Assembly.IsComponentOf J (isometryCentralizer Q (F.ι s)) :=
    SevOm.isComponentOf_isometryCentralizer hJ
  obtain ⟨h, hh, hJh⟩ := SevOm.exists_le_supportedBlock hxIso hL
  by_cases h1 : h = X - 1
  · rw [h1] at hJh
    obtain ⟨h4, hodd | hsplit⟩ :=
      SevOmSmall.fixed_case_small_odd hxIso hL hJh
    · exact exists_mem_of_odd_mem hQ hp hp2 hEΩ F hU hV hz s h4 hodd
    · obtain ⟨hsp, hK4, -⟩ := hsplit
      exact exists_mem_of_splitFour hQ hp hp2 hEΩ F hU hV hmax hcomm hz s hJ hJh hsp hK4
  · exact exists_mem_of_ne_X_sub_one hQ hp hp2 hEΩ F hU hcomm hz s hh h1 hL hJh

theorem torusIrred_orthDerived (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hEΩ : E ≤ orthDerived Q) (hEp : ∀ c ∈ E, c ^ p = 1)
    (hEc : ∀ c ∈ E, ∀ d ∈ E, c * d = d * c) (hE3 : p ^ 3 ≤ Nat.card E)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) :
    (∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
        (∀ c ∈ E, y' * c = c * y') → (∃ k : ℕ, y ^ p ^ k = 1) → (∃ k : ℕ, y' ^ p ^ k = 1) →
        y * y' = y' * y) ∧
      (∀ B : Subgroup (V ≃ₗ[K] V), B ≤ E → (∀ w ∈ orthDerived Q, (∀ c ∈ E, w * c * w⁻¹ ∈ E) →
          ∀ b ∈ B, w * b * w⁻¹ ∈ B) → B = ⊥ ∨ B = E) ∧
      ∃ e : ℕ, (∀ y ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) → (∃ k : ℕ, y ^ p ^ k = 1) →
          y ^ p ^ e = 1) ∧
        ∀ x ∈ E, ∀ J : Subgroup (V ≃ₗ[K] V),
          CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {x}) →
          ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hne := exists_ne_one_of_three_le_card_orth hp hE3
  have hmax' : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ E, g * c = c * g) → g ∈ E :=
    fun g hg hgp hgc => hmax g hg hgc hgp
  obtain ⟨r, τ, F, hτF, hU, hV, hperm, hdinv⟩ :=
    OrthTorus.exists_torus_frame hp2 hpq hQ hT hEΩ hEp hEc hmax' hne
  have hr := three_le_r_of_frame hp hτF hE3
  have hcomm : ∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
      (∀ c ∈ E, y' * c = c * y') → (∃ k : ℕ, y ^ p ^ k = 1) →
      (∃ k : ℕ, y' ^ p ^ k = 1) → y * y' = y' * y := by
    intro y hy y' hy' hyE hy'E hyp hyp'
    have hyW : ∀ v, (∀ c ∈ E, c v = v) → y v = v := fun v hv =>
      apply_eq_self_of_forall_apply_eq hQ hT hp hp2 hEΩ F hmax hy hyE hyp hv
    have hy'W : ∀ v, (∀ c ∈ E, c v = v) → y' v = v := fun v hv =>
      apply_eq_self_of_forall_apply_eq hQ hT hp hp2 hEΩ F hmax hy' hy'E hyp' hv
    exact commute_of_forall_apply_eq hQ hp hp2 hEΩ F hU hyE hy'E hyW hy'W
  have hirr := irreducible_of_frame hp hp2 hτF hperm hdinv hr
  obtain ⟨e, ⟨y₀, hy₀Ω, hy₀E, hy₀ord⟩, hexp⟩ :=
    exists_max_order hp hEΩ hEp hEc hne
  have hy₀p : ∃ k : ℕ, y₀ ^ p ^ k = 1 :=
    ⟨e, by rw [← hy₀ord]; exact pow_orderOf_eq_one y₀⟩
  have htr := exists_conj_single_orth hτF hperm
  have hz : ∀ k, ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v := by
    intro k
    exact exists_piece_orderOf hQ hT hp hp2 hEΩ F htr hy₀Ω hy₀E hy₀ord
      (fun v hv => apply_eq_self_of_forall_apply_eq hQ hT hp hp2 hEΩ F hmax
        hy₀Ω hy₀E hy₀p hv) k
  exact ⟨hcomm, hirr, e, hexp, fun x hx J hJ =>
    exists_mem_of_isComponentOf hQ hp hp2 hEΩ F hU hV hmax hcomm hz hx hJ⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem centralizer_map_subtype_orth {E : Subgroup ↥(orthDerived Q)} {y : ↥(orthDerived Q)}
    (hy : y ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q))) :
    ∀ c ∈ E.map (orthDerived Q).subtype, (y : V ≃ₗ[K] V) * c = c * (y : V ≃ₗ[K] V) := by
  rintro _ ⟨c, hc, rfl⟩
  exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy c hc)).symm

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem pElement_map_subtype {y : ↥(orthDerived Q)}
    (hy : ∃ k : ℕ, y ^ p ^ k = 1) : ∃ k : ℕ, (y : V ≃ₗ[K] V) ^ p ^ k = 1 :=
  hy.imp fun k hk => by simpa using congrArg Subtype.val hk

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem commute_centralizer_map_subtype {E : Subgroup ↥(orthDerived Q)}
    (hcomm : ∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q,
      (∀ c ∈ E.map (orthDerived Q).subtype, y * c = c * y) →
      (∀ c ∈ E.map (orthDerived Q).subtype, y' * c = c * y') →
      (∃ k : ℕ, y ^ p ^ k = 1) → (∃ k : ℕ, y' ^ p ^ k = 1) → y * y' = y' * y) :
    ∀ x ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q)),
      ∀ y ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q)),
      (∃ k : ℕ, x ^ p ^ k = 1) → (∃ k : ℕ, y ^ p ^ k = 1) → x * y = y * x := by
  intro x hx y hy hxp hyp
  exact Subtype.ext (hcomm (x : V ≃ₗ[K] V) x.2 (y : V ≃ₗ[K] V) y.2
    (centralizer_map_subtype_orth hx) (centralizer_map_subtype_orth hy)
    (pElement_map_subtype hxp) (pElement_map_subtype hyp))

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem exponent_centralizer_map_subtype {E : Subgroup ↥(orthDerived Q)} {e : ℕ}
    (hexp : ∀ y ∈ orthDerived Q, (∀ c ∈ E.map (orthDerived Q).subtype, y * c = c * y) →
      (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1) :
    ∀ y ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q)),
      (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1 := by
  intro y hy hyp
  exact Subtype.ext (hexp (y : V ≃ₗ[K] V) y.2 (centralizer_map_subtype_orth hy)
    (pElement_map_subtype hyp))

omit [CharP K 2] in
private theorem irreducible_normalizer_map_subtype {E : Subgroup ↥(orthDerived Q)}
    (hirr : ∀ B : Subgroup (V ≃ₗ[K] V), B ≤ E.map (orthDerived Q).subtype →
      (∀ w ∈ orthDerived Q, (∀ c ∈ E.map (orthDerived Q).subtype,
        w * c * w⁻¹ ∈ E.map (orthDerived Q).subtype) →
        ∀ b ∈ B, w * b * w⁻¹ ∈ B) → B = ⊥ ∨ B = E.map (orthDerived Q).subtype) :
    ∀ B : Subgroup ↥(orthDerived Q), B ≤ E →
      Subgroup.normalizer (E : Set ↥(orthDerived Q)) ≤
        Subgroup.normalizer (B : Set ↥(orthDerived Q)) → B = ⊥ ∨ B = E := by
  intro B hBE hNB
  let E' : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype
  let B' : Subgroup (V ≃ₗ[K] V) := B.map (orthDerived Q).subtype
  have hB'E' : B' ≤ E' := Subgroup.map_mono hBE
  have hBN' : ∀ w ∈ orthDerived Q, (∀ c ∈ E', w * c * w⁻¹ ∈ E') →
      ∀ b ∈ B', w * b * w⁻¹ ∈ B' := by
    intro w hw hwE b hb
    obtain ⟨q, hqB, rfl⟩ := Subgroup.mem_map.mp hb
    set wR : ↥(orthDerived Q) := ⟨w, hw⟩ with hwR
    have hle : E.map (MulAut.conj wR).toMonoidHom ≤ E := by
      rintro x ⟨ee, hee, rfl⟩
      obtain ⟨e', he', hge⟩ := Subgroup.mem_map.mp
        (hwE (ee : V ≃ₗ[K] V) (Subgroup.mem_map.mpr ⟨ee, hee, rfl⟩))
      have hEq : wR * ee * wR⁻¹ = e' := by
        apply Subtype.ext
        simpa [wR] using hge.symm
      change wR * ee * wR⁻¹ ∈ E
      rw [hEq]
      exact he'
    have hwRE : wR ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj wR).injective])
    have hconjB : wR * q * wR⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hNB hwRE) q).mp hqB
    exact Subgroup.mem_map.mpr ⟨_, hconjB, rfl⟩
  rcases hirr B' hB'E' hBN' with hbot | htop
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective B
      (orthDerived Q).subtype_injective).mp (by simpa [B'] using hbot))
  · exact Or.inr ((Subgroup.map_injective (orthDerived Q).subtype_injective) htop)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem component_meets_map_subtype {E : Subgroup ↥(orthDerived Q)} {e : ℕ}
    (hcomp : ∀ x ∈ E.map (orthDerived Q).subtype,
      ∀ J : Subgroup (V ≃ₗ[K] V),
        CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {x}) →
        ∃ y ∈ J, (∀ c ∈ E.map (orthDerived Q).subtype, y * c = c * y) ∧
          orderOf y = p ^ e) :
    ∀ x ∈ E, x ≠ 1 → ∀ J : Subgroup ↥(orthDerived Q),
      CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}) →
      ∃ s ∈ J, s ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q)) ∧ orderOf s = p ^ e := by
  intro x hx _ J hJ
  let J' : Subgroup (V ≃ₗ[K] V) := J.map (orthDerived Q).subtype
  have hJ' : CFSG.Assembly.IsComponentOf J'
      (orthDerived Q ⊓ Subgroup.centralizer ({(x : V ≃ₗ[K] V)})) := by
    have h1 : CFSG.Assembly.IsComponentOf J'
        ((Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map
          (orthDerived Q).subtype) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ
        (orthDerived Q).subtype (orthDerived Q).subtype_injective
    rwa [CFSG.LocalAnalysis.ComponentInitial.map_subtype_centralizer_singleton
      (orthDerived Q) x] at h1
  obtain ⟨s', hs'J, hs'E, hs'ord⟩ :=
    hcomp (x : V ≃ₗ[K] V) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) J' hJ'
  obtain ⟨s, hsJ, hs_eq⟩ := Subgroup.mem_map.mp hs'J
  refine ⟨s, hsJ, ?_, ?_⟩
  · intro c hc
    apply Subtype.ext
    simpa [← hs_eq] using (hs'E (c : V ≃ₗ[K] V)
      (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)).symm
  · rw [← orderOf_injective (orthDerived Q).subtype
      (orthDerived Q).subtype_injective s]
    simpa [← hs_eq] using hs'ord

theorem ggTorusGenR_orthDerived (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) :
    GGTorusGenR p 3 ↥(orthDerived Q) := by
  classical
  refine ggTorusGenR_of_forall_torusIrred hp ?_
  intro E hE hcard hmaxE
  let E' : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype
  have hE' : CFSG.Open.IsElemAbelian p E' := CFSG.Open.IsElemAbelian.map hE _
  haveI : IsMulCommutative E' := hE'.1
  have hcard' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (orthDerived Q).subtype_injective
  have hE3' : p ^ 3 ≤ Nat.card E' := by rw [hcard']; exact hcard
  have hmax' : ∀ g ∈ orthDerived Q, (∀ c ∈ E', g * c = c * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgc hgp
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, ?_, rfl⟩
    exact hmaxE ⟨g, hg⟩ (fun x hx => Subtype.ext (hgc (x : V ≃ₗ[K] V)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))) (Subtype.ext hgp)
  obtain ⟨hcomm', hirr', e, hexp', hcomp'⟩ :=
    torusIrred_orthDerived hp hp2 hpq hQ hT (by rintro _ ⟨x, -, rfl⟩; exact x.2) hE'.2
      (fun c hc d hd => Subgroup.mul_comm_of_mem_isMulCommutative E' hc hd) hE3' hmax'
  refine ⟨?_, ?_, e, ?_, ?_⟩
  · exact commute_centralizer_map_subtype hcomm'
  · exact irreducible_normalizer_map_subtype hirr'
  · exact exponent_centralizer_map_subtype hexp'
  · exact component_meets_map_subtype hcomp'

end CFSG.StandardType.OrthTorusGen
