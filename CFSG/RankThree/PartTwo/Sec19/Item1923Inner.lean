module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Plane
public import CFSG.RankThree.PartTwo.Sec19.Item1923InnerCore
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis
import CFSG.Quasithin.Background.F1Models
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem inner1923_comm {A : Subgroup G} (hA : IsE27 A) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem inner1923_plane_le_left : planeGroup A L c ≤ L := by
  intro x hx
  unfold planeGroup at hx
  exact hx.1.1

private theorem inner1923_inf_le_plane (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    A ⊓ L ≤ planeGroup A L c := by
  intro b hb
  unfold planeGroup
  refine ⟨⟨hb.2, Subgroup.le_normalizer hb⟩, ?_⟩
  have hbc : b ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact (inner1923_comm h.isE27 hb.1 (step1923_W h hF).mem).symm
  exact hbc

private theorem inner1923_inf_plane_eq (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    A ⊓ planeGroup A L c = A ⊓ L :=
  le_antisymm (inf_le_inf_left A inner1923_plane_le_left)
    (le_inf inf_le_left (inner1923_inf_le_plane h hF))

private theorem inner1923_quaternion (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    ∃ F : QuaternionGroup 2 →* MulAut (A ⊓ L : Subgroup G), Function.Injective F ∧
      ∀ x : MulAut (A ⊓ L : Subgroup G),
        x ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L) ↔ ∃ q, F q = x := by
  have hPQ := step1923_W h hF
  obtain ⟨f, hf⟩ := hPQ.quaternion
  have hc : c ∈ Subgroup.centralizer ((planeGroup A L c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun k hk => hPQ.commute k hk
  have hA : A = (A ⊓ planeGroup A L c) ⊔ Subgroup.zpowers c := by
    rw [inner1923_inf_plane_eq h hF, sup_comm]
    exact hPQ.eq_sup
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec4.Res423Four.nonempty_autIn_inf_equiv hc hA
  rw [inner1923_inf_plane_eq h hF] at e
  set f' : QuaternionGroup 2 →* Sec4.autIn (planeGroup A L c) (A ⊓ L) := e.toMonoidHom.comp f
  have hf' : Function.Injective f' := e.injective.comp hf
  have hcard : Nat.card (Sec4.autIn (planeGroup A L c) (A ⊓ L)) = 8 :=
    step1923_card_autIn_W h hF
  have hrange : f'.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective hf').toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  refine ⟨(Sec4.autIn (planeGroup A L c) (A ⊓ L)).subtype.comp f', ?_, ?_⟩
  · exact Subtype.val_injective.comp hf'
  · intro x
    constructor
    · intro hx
      have hmem : (⟨x, hx⟩ : Sec4.autIn (planeGroup A L c) (A ⊓ L)) ∈ f'.range := by
        rw [hrange]
        exact Subgroup.mem_top _
      obtain ⟨q, hq⟩ := hmem
      exact ⟨q, congrArg Subtype.val hq⟩
    · rintro ⟨q, rfl⟩
      exact (f' q).2

private theorem inner1923_rho (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    ∃ ρ : planeGroup A L c →* MulAut (A ⊓ L : Subgroup G),
      (∀ (w : planeGroup A L c) (b : (A ⊓ L : Subgroup G)),
        ((ρ w b : (A ⊓ L : Subgroup G)) : G) = (w : G) * (b : G) * (w : G)⁻¹) ∧
      ρ.range = Sec4.autIn (planeGroup A L c) (A ⊓ L) := by
  have hWN : planeGroup A L c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    (step1923_W h hF).le_normalizer_plane
  refine ⟨(A ⊓ L : Subgroup G).normalizerMonoidHom.comp (Subgroup.inclusion hWN),
    fun w b => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _, ?_⟩
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact Sec4.mem_autIn_iff.mpr ⟨w, hWN w.2, w.2, rfl⟩
  · intro hx
    obtain ⟨g, hgN, hgW, hgx⟩ := Sec4.mem_autIn_iff.mp hx
    exact ⟨⟨g, hgW⟩, hgx⟩

private theorem inner1923_quat_facts :
    (∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = 1 ∨ q = QuaternionGroup.a 2) ∧
    (∀ q : QuaternionGroup 2, q ^ 4 = 1) ∧
    (∀ q : QuaternionGroup 2, q ≠ 1 → q ≠ QuaternionGroup.a 2 → q ^ 2 = QuaternionGroup.a 2) ∧
    (∀ q : QuaternionGroup 2, q * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q) ∧
    (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 ∧
    (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

private theorem inner1923_central_facts {X : Type} [Group X] (F : QuaternionGroup 2 →* X)
    (hF : Function.Injective F) :
    F (QuaternionGroup.a 2) ^ 2 = 1 ∧ F (QuaternionGroup.a 2) ≠ 1 := by
  obtain ⟨-, -, -, -, h2, h1⟩ := inner1923_quat_facts
  refine ⟨?_, fun h0 => h1 (hF (h0.trans (map_one F).symm))⟩
  rw [← map_pow, h2, map_one]

private theorem inner1923_inv_of_fixed_eq_one {X : Type} [Group X] [Finite X]
    (hcomm : ∀ x y : X, x * y = y * x) (z : MulAut X) (hz2 : z ^ 2 = 1)
    (hfix : ∀ x : X, z x = x → x = 1) : ∀ b : X, z b = b⁻¹ := by
  letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
  have hsq : ∀ y : X, z (z y) = y := fun y => by
    have := congrArg (fun φ : MulAut X => φ y) hz2
    simpa [pow_two] using this
  let φ : X →* X := MonoidHom.mk' (fun x => z x * x⁻¹) (fun x y => by
    simp only [map_mul, mul_inv_rev]
    ac_rfl)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : z x * x⁻¹ = 1 := hx
    exact hfix x (mul_inv_eq_one.mp hx')
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro b
  obtain ⟨x, rfl⟩ := hsurj b
  show z (z x * x⁻¹) = (z x * x⁻¹)⁻¹
  rw [map_mul, map_inv, hsq, mul_inv_rev, inv_inv]

private theorem inner1923_card_le_four {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (s : Finset X) (hs : ∀ x ∈ T, x ∈ s) (hcard : s.card ≤ 4) : Nat.card T ≤ 4 := by
  refine le_trans (Nat.card_le_card_of_injective (fun x : T => (⟨x.1, hs x.1 x.2⟩ : s)) ?_) ?_
  · intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext hxy
  · rw [Nat.card_eq_finsetCard]
    exact hcard

private theorem inner1923_sq_mem_inner {Γ X : Type} [Group Γ] [Group X] (σ : Γ →* MulAut X)
    (hOE : OutTwoExpTwo X) {s : Γ} {e : ℕ} (hs : s ^ 2 ^ e = 1) :
    σ (s ^ 2) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
  set y : Outer X := QuotientGroup.mk'
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X) (σ s) with hy
  have hye : y ^ 2 ^ e = 1 := by
    rw [hy, ← map_pow, ← map_pow, hs, map_one, map_one]
  have hP : IsPGroup 2 (Subgroup.zpowers y) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨e, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hye, one_zpow]
  have h2 : y ^ 2 = 1 := hOE (Subgroup.zpowers y) hP y (Subgroup.mem_zpowers y)
  have h3 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
      (σ (s ^ 2)) = 1 := by
    rw [map_pow σ, map_pow (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner X))]
    exact h2
  exact (QuotientGroup.eq_one_iff _).mp h3

theorem step1923_involution_inverts (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (planeGroup A L c) (A ⊓ L)))
    {z : MulAut (A ⊓ L : Subgroup G)} (hz : z ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L))
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : ∀ b : (A ⊓ L : Subgroup G), z b = b⁻¹ := by
  obtain ⟨F, hFi, hFr⟩ := inner1923_quaternion h hF
  obtain ⟨q, rfl⟩ := (hFr z).mp hz
  obtain ⟨hsq1, -, -, hcomm, -, -⟩ := inner1923_quat_facts
  have hq2 : q ^ 2 = 1 := hFi (by rw [map_pow, hz2, map_one])
  rcases hsq1 q hq2 with hq1 | hqa
  · exact absurd (by rw [hq1, map_one]) hz1
  subst hqa
  have hcentral : ∀ φ ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L),
      F (QuaternionGroup.a 2) * φ = φ * F (QuaternionGroup.a 2) := by
    intro φ hφ
    obtain ⟨r, rfl⟩ := (hFr φ).mp hφ
    rw [← map_mul, ← map_mul, hcomm r]
  let Fix : Subgroup ↥(A ⊓ L : Subgroup G) :=
    { carrier := {b | F (QuaternionGroup.a 2) b = b}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul] at hx hy ⊢
        rw [hx, hy]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, map_inv] at hx ⊢
        rw [hx] }
  have hkey : ∀ ψ ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L), ∀ b ∈ Fix, ψ b ∈ Fix := by
    intro ψ hψ b hb
    have hb' : F (QuaternionGroup.a 2) b = b := hb
    show F (QuaternionGroup.a 2) (ψ b) = ψ b
    have this : F (QuaternionGroup.a 2) (ψ b) = ψ (F (QuaternionGroup.a 2) b) :=
      congrArg (fun θ : MulAut ↥(A ⊓ L : Subgroup G) => θ b) (hcentral ψ hψ)
    rw [this, hb']
  have hinv : ∀ φ ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L),
      Fix.map (φ : MulAut ↥(A ⊓ L : Subgroup G)).toMonoidHom = Fix := by
    intro φ hφ
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hkey φ hφ b hb
    · intro x hx
      refine ⟨(φ : MulAut ↥(A ⊓ L : Subgroup G))⁻¹ x, hkey _ (inv_mem hφ) x hx, ?_⟩
      simp
  rcases hirr Fix hinv with hbot | htop
  · refine inner1923_inv_of_fixed_eq_one ?_ (F (QuaternionGroup.a 2)) hz2 ?_
    · intro x y
      exact Subtype.ext (inner1923_comm h.isE27 x.2.1 y.2.1)
    · intro x hx
      have hxF : x ∈ Fix := hx
      rw [hbot, Subgroup.mem_bot] at hxF
      exact hxF
  · have h1 : F (QuaternionGroup.a 2) = 1 := by
      apply MulEquiv.ext
      intro b
      have hb : b ∈ Fix := by
        rw [htop]
        exact Subgroup.mem_top b
      exact hb
    exact absurd h1 hz1

theorem step1923_inverting (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ oTwoComponentsIn M) (hab : OutTwoAbelian (K ⧸ CFSG.pCore 2 K))
    (hexp : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
        (planeGroup A L c) = 2 → OutTwoExpTwo (K ⧸ CFSG.pCore 2 K)) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (K : Set G)), w ∈ planeGroup A L c ∧
      (∀ b ∈ A ⊓ L, w * b * w⁻¹ = b⁻¹) ∧
      Sec3.Sims321.barAut K ⟨w, hw⟩ ∈ inner (K ⧸ CFSG.pCore 2 K) := by
  classical
  obtain ⟨ρ, hρ, hrange⟩ := inner1923_rho h hF
  obtain ⟨F, hFi, hFr⟩ := inner1923_quaternion h hF
  have hcard : Nat.card (Sec4.autIn (planeGroup A L c) (A ⊓ L)) = 8 :=
    step1923_card_autIn_W h hF
  have hρcard : Nat.card ρ.range = 8 := by
    rw [hrange]
    exact hcard
  have hqρ : ∃ f : QuaternionGroup 2 →* MulAut (A ⊓ L : Subgroup G),
      Function.Injective f ∧ ∀ q, f q ∈ ρ.range :=
    ⟨F, hFi, fun q => by
      rw [hrange]
      exact (hFr _).mpr ⟨q, rfl⟩⟩
  have hzT : F (QuaternionGroup.a 2) ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L) :=
    (hFr _).mpr ⟨_, rfl⟩
  have hz₀ : F (QuaternionGroup.a 2) ∈ ρ.range := by
    rw [hrange]
    exact hzT
  obtain ⟨hz2, hz1⟩ := inner1923_central_facts F hFi
  have hinv := step1923_involution_inverts h hF (step1923_W h hF).irreducible hzT hz2 hz1
  by_cases h1 : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
      (planeGroup A L c) = 1
  ·
    have hWN : planeGroup A L c ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
      (Subgroup.relIndex_eq_one.mp h1 hx).2
    obtain ⟨γ, -, hγρ, hγσ⟩ := exists_mem_inverting_inner ρ
      ((Sec3.Sims321.barAut K).comp (Subgroup.inclusion hWN)) hρcard hqρ ⊤ (by simp) hab
      (fun h2 => by simp at h2) hz₀ hz2 hz1
    refine ⟨(γ : G), hWN γ.2, γ.2, fun b hb => ?_, hγσ⟩
    have key : ((ρ γ ⟨b, hb⟩ : ↥(A ⊓ L : Subgroup G)) : G) =
        ((F (QuaternionGroup.a 2) ⟨b, hb⟩ : ↥(A ⊓ L : Subgroup G)) : G) := by
      rw [hγρ]
    rw [hρ γ ⟨b, hb⟩, hinv ⟨b, hb⟩] at key
    exact key
  ·
    have hrel2 : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
        (planeGroup A L c) = 2 := by
      have hle := (step1923_irreducible h hF hK).2
      have hne : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
          (planeGroup A L c) ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hOE := hexp hrel2
    have hidx : ((planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).subgroupOf
        (planeGroup A L c)).index = 2 := hrel2
    have hdvd : ((planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).subgroupOf
        (planeGroup A L c)).index ∣ 2 := by
      rw [hidx]
    obtain ⟨a, ha⟩ := Subgroup.index_dvd_two_iff'.mp hdvd
    obtain ⟨t, htN, ht1, htz⟩ : ∃ t : ↥(planeGroup A L c),
        (t : G) ∈ Subgroup.normalizer (K : Set G) ∧ ρ t ≠ 1 ∧
          ρ t ≠ F (QuaternionGroup.a 2) := by
      by_contra hcon
      push Not at hcon
      have hsub : ∀ x ∈ ρ.range, x ∈ ({1, F (QuaternionGroup.a 2), (ρ a)⁻¹,
          (ρ a)⁻¹ * F (QuaternionGroup.a 2)} : Finset (MulAut (A ⊓ L : Subgroup G))) := by
        intro x hx
        obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases ha b with hab' | hb'
        · have hN' : ρ (a * b) = 1 ∨ ρ (a * b) = F (QuaternionGroup.a 2) := by
            by_cases h0 : ρ (a * b) = 1
            · exact Or.inl h0
            · exact Or.inr (hcon _ (Subgroup.mem_subgroupOf.mp hab').2 h0)
          rw [map_mul] at hN'
          rcases hN' with h0 | h0
          · exact Or.inr (Or.inr (Or.inl (eq_inv_of_mul_eq_one_right h0)))
          · exact Or.inr (Or.inr (Or.inr (eq_inv_mul_of_mul_eq h0)))
        · by_cases h0 : ρ b = 1
          · exact Or.inl h0
          · exact Or.inr (Or.inl (hcon b (Subgroup.mem_subgroupOf.mp hb').2 h0))
      have hc4 := inner1923_card_le_four ρ.range _ hsub Finset.card_le_four
      omega
    have hmemT : ρ t ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L) := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
    obtain ⟨q, hq⟩ := (hFr (ρ t)).mp hmemT
    have hq1 : q ≠ 1 := fun h0 => ht1 (by rw [← hq, h0, map_one])
    have hqa : q ≠ QuaternionGroup.a 2 := fun h0 => htz (by rw [← hq, h0])
    obtain ⟨-, hq4, hqsq, -, -, -⟩ := inner1923_quat_facts
    have ha2 : ρ t ^ 2 = F (QuaternionGroup.a 2) := by
      rw [← hq, ← map_pow, hqsq q hq1 hqa]
    have ha4 : ρ t ^ 4 = 1 := by
      rw [← hq, ← map_pow, hq4 q, map_one]
    let t' : ↥(planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)) := ⟨(t : G), t.2, htN⟩
    let ρ₁ := ρ.comp (Subgroup.inclusion (inf_le_left :
      planeGroup A L c ⊓ Subgroup.normalizer (K : Set G) ≤ planeGroup A L c))
    let σ₁ := (Sec3.Sims321.barAut K).comp (Subgroup.inclusion (inf_le_right :
      planeGroup A L c ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (K : Set G)))
    have h1t : ρ₁ t' = ρ t := rfl
    have ha2' : ρ₁ t' ^ 2 = F (QuaternionGroup.a 2) := by
      rw [h1t]
      exact ha2
    have ha4' : ρ₁ t' ^ 4 = 1 := by
      rw [h1t]
      exact ha4
    obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t').ne'
    have hs : (t' ^ (m * m)) ^ 2 ^ e = 1 := by
      rw [← pow_mul]
      have hmm : m * m * 2 ^ e = orderOf t' * m := by
        rw [hn]
        ring
      rw [hmm, pow_mul, pow_orderOf_eq_one, one_pow]
    obtain ⟨j, hj⟩ := hm.mul hm
    have hργ : ρ₁ ((t' ^ (m * m)) ^ 2) = F (QuaternionGroup.a 2) := by
      rw [map_pow, map_pow, ← pow_mul, hj]
      have h4 : (2 * j + 1) * 2 = 2 + 4 * j := by ring
      rw [h4, pow_add, pow_mul, ha4', one_pow, mul_one, ha2']
    have hσγ : σ₁ ((t' ^ (m * m)) ^ 2) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) :=
      inner1923_sq_mem_inner σ₁ hOE hs
    refine ⟨(((t' ^ (m * m)) ^ 2 : ↥(planeGroup A L c ⊓ Subgroup.normalizer (K : Set G))) : G),
      ((t' ^ (m * m)) ^ 2).2.2, ((t' ^ (m * m)) ^ 2).2.1, fun b hb => ?_, hσγ⟩
    have key := hρ ⟨(((t' ^ (m * m)) ^ 2 : ↥(planeGroup A L c ⊓ Subgroup.normalizer
      (K : Set G))) : G), ((t' ^ (m * m)) ^ 2).2.1⟩ ⟨b, hb⟩
    have hγρ' : ρ ⟨(((t' ^ (m * m)) ^ 2 : ↥(planeGroup A L c ⊓ Subgroup.normalizer
        (K : Set G))) : G), ((t' ^ (m * m)) ^ 2).2.1⟩ = F (QuaternionGroup.a 2) := hργ
    rw [hγρ', hinv ⟨b, hb⟩] at key
    exact key.symm

theorem step1923_square_inverting (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ oTwoComponentsIn M)
    (hcyc : CFSG.ClassicalInvolution.Nobq.OutTwoCyclic (K ⧸ CFSG.pCore 2 K))
    (hnorm : planeGroup A L c ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (K : Set G)), w ∈ planeGroup A L c ∧
      (∀ b ∈ A ⊓ L, w * w * b * (w * w)⁻¹ = b⁻¹) ∧
      Sec3.Sims321.barAut K ⟨w, hw⟩ ∈ inner (K ⧸ CFSG.pCore 2 K) := by
  obtain ⟨ρ, hρ, hrange⟩ := inner1923_rho h hF
  obtain ⟨F, hFi, hFr⟩ := inner1923_quaternion h hF
  have hcard : Nat.card (Sec4.autIn (planeGroup A L c) (A ⊓ L)) = 8 :=
    step1923_card_autIn_W h hF
  have hρcard : Nat.card ρ.range = 8 := by
    rw [hrange]
    exact hcard
  have hqρ : ∃ f : QuaternionGroup 2 →* MulAut (A ⊓ L : Subgroup G),
      Function.Injective f ∧ ∀ q, f q ∈ ρ.range :=
    ⟨F, hFi, fun q => by
      rw [hrange]
      exact (hFr _).mpr ⟨q, rfl⟩⟩
  have hzT : F (QuaternionGroup.a 2) ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L) :=
    (hFr _).mpr ⟨_, rfl⟩
  have hz₀ : F (QuaternionGroup.a 2) ∈ ρ.range := by
    rw [hrange]
    exact hzT
  obtain ⟨hz2, hz1⟩ := inner1923_central_facts F hFi
  have hinv := step1923_involution_inverts h hF (step1923_W h hF).irreducible hzT hz2 hz1
  obtain ⟨γ, hγσ, hγρ⟩ := exists_mem_square_inverting_inner ρ
    ((Sec3.Sims321.barAut K).comp (Subgroup.inclusion hnorm)) hρcard hqρ hcyc hz₀ hz2 hz1
  refine ⟨(γ : G), hnorm γ.2, γ.2, fun b hb => ?_, hγσ⟩
  have h2 : ρ (γ ^ 2) = F (QuaternionGroup.a 2) := by
    rw [map_pow, hγρ]
  have key : ((ρ (γ ^ 2) ⟨b, hb⟩ : ↥(A ⊓ L : Subgroup G)) : G) =
      ((F (QuaternionGroup.a 2) ⟨b, hb⟩ : ↥(A ⊓ L : Subgroup G)) : G) := by
    rw [h2]
  rw [hρ (γ ^ 2) ⟨b, hb⟩, hinv ⟨b, hb⟩] at key
  rw [Subgroup.coe_pow, pow_two] at key
  exact key

theorem step1923_inner (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ oTwoComponentsIn M) (hab : OutTwoAbelian (K ⧸ CFSG.pCore 2 K))
    (hexp : (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex
        (planeGroup A L c) = 2 → OutTwoExpTwo (K ⧸ CFSG.pCore 2 K)) :
    barActionImage K (A ⊓ L) ≤ inner (K ⧸ CFSG.pCore 2 K) := by
  obtain ⟨w, hwN, -, hwinv, hwι⟩ := step1923_inverting h hF hK hab hexp
  intro x hx
  unfold barActionImage at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyB : (y : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hy
  have hβ : Sec3.Sims321.barAut K y ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : y ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, h.isE27.1.2 (y : G) hyB.1, Subgroup.coe_one])
    rw [h3, map_one]
  have hconj : Sec3.Sims321.barAut K ⟨w, hwN⟩ * Sec3.Sims321.barAut K y *
      (Sec3.Sims321.barAut K ⟨w, hwN⟩)⁻¹ = (Sec3.Sims321.barAut K y)⁻¹ := by
    have hw' : (⟨w, hwN⟩ : Subgroup.normalizer (K : Set G)) * y * (⟨w, hwN⟩)⁻¹ = y⁻¹ :=
      Subtype.ext (hwinv (y : G) hyB)
    calc Sec3.Sims321.barAut K ⟨w, hwN⟩ * Sec3.Sims321.barAut K y *
          (Sec3.Sims321.barAut K ⟨w, hwN⟩)⁻¹
        = Sec3.Sims321.barAut K (⟨w, hwN⟩ * y * (⟨w, hwN⟩)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = Sec3.Sims321.barAut K y⁻¹ := by rw [hw']
      _ = (Sec3.Sims321.barAut K y)⁻¹ := map_inv _ _
  exact mem_inner_of_inverted hwι hβ hconj

end CFSG.RankThree.PartTwo.Late
