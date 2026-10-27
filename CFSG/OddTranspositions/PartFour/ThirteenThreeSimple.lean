module

public import CFSG.Blueprint.FischerDefs
import CFSG.Fischer.Classification.Basic.Trichotomy

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

private theorem mk_eq_of_commute_mk (hP : Pair X E) {N : Subgroup X} [N.Normal]
    (hcong : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a → a⁻¹ * b ∈ N) {a b : X} (ha : a ∈ E) (hb : b ∈ E)
    (hc : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a) :
    (QuotientGroup.mk a : X ⧸ N) = QuotientGroup.mk b := by
  by_cases hab : a * b = b * a
  · exact QuotientGroup.eq.mpr (hcong a ha b hb hab)
  have h3 := Pair.orderOf_mul_eq_three hP ha hb hab
  have hpow3 : ((QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, ← h3, pow_orderOf_eq_one,
      QuotientGroup.mk_one]
  have ha2 : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk a = 1 := by
    rw [← QuotientGroup.mk_mul, Pair.mul_self hP ha, QuotientGroup.mk_one]
  have hb2 : (QuotientGroup.mk b : X ⧸ N) * QuotientGroup.mk b = 1 := by
    rw [← QuotientGroup.mk_mul, Pair.mul_self hP hb, QuotientGroup.mk_one]
  have hpow2 : ((QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b) ^ 2 = 1 := by
    rw [pow_two, mul_assoc, ← mul_assoc (QuotientGroup.mk b), ← hc, mul_assoc, hb2, mul_one, ha2]
  have h1 : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b = 1 := by
    have : ((QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b) ^ 3 =
        ((QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b) ^ 2 *
          ((QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b) := pow_succ _ 2
    rw [hpow3, hpow2, one_mul] at this
    exact this.symm
  calc (QuotientGroup.mk a : X ⧸ N) = QuotientGroup.mk a * (QuotientGroup.mk b *
        QuotientGroup.mk b) := by rw [hb2, mul_one]
    _ = QuotientGroup.mk b := by rw [← mul_assoc, h1, one_mul]

theorem isSimpleGroup_commutator_of_derivedSeries (hP : Pair X E)
    (hsolv : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥)
    (hder : derivedSeries X 1 = derivedSeries X 2) : IsSimpleGroup (commutator X) := by
  classical
  have := Pair.finite hP
  have hZ : Subgroup.center X = ⊥ := hsolv _ inferInstance inferInstance
  have hp : ∀ p : ℕ, p.Prime → ∀ N : Subgroup X, N.Normal → IsPGroup p N → N = ⊥ :=
    fun p hp N hN hNp => by
      haveI : Fact p.Prime := ⟨hp⟩
      haveI := hNp.isNilpotent
      exact hsolv N hN inferInstance
  have h2 := hp 2 Nat.prime_two
  have h3 := hp 3 Nat.prime_three
  obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
  have htop : (⊤ : Subgroup X) ≠ ⊥ := by
    intro h
    have := Subgroup.mem_top e₀
    rw [h, Subgroup.mem_bot] at this
    exact Pair.ne_one hP he₀ this
  obtain ⟨N, hNn, -, hNbot, hmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
  have hNs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hNsol := Pair.not_isSolvable_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have := hNn
  have hNZ : ¬ N ≤ Subgroup.center X := fun h => hNbot (by rw [← le_bot_iff, ← hZ]; exact h)
  have hNle : N ≤ commutator X := by
    have hcN : commutator N = ⊤ := by
      rcases hNs.eq_bot_or_eq_top_of_normal (commutator N) with h | h
      · exfalso
        apply hNsol
        refine Group.isSolvable_of_comm fun a b => ?_
        have hc : ⁅a, b⁆ ∈ commutator N := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact h
    intro n hn
    have hmem : (⟨n, hn⟩ : N) ∈ commutator N := hcN ▸ Subgroup.mem_top _
    have h1 : n ∈ (commutator N).map N.subtype := ⟨⟨n, hn⟩, hmem, rfl⟩
    rw [Subgroup.map_subtype_commutator] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  have hcong : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a → a⁻¹ * b ∈ N := by
    intro a ha b hb hab
    by_contra hne
    refine hNZ (Pair.normal_le_center_of_commute hP hNn hNs ha hb hab fun n hn => ?_)
    by_contra hc
    apply hne
    have hb' := Pair.conj_mem hP hb n
    have h1 := Pair.mul_conj_left_eq hP ha hb' hc
    have hπ : (QuotientGroup.mk (n * b * n⁻¹) : X ⧸ N) = QuotientGroup.mk b := by
      rw [QuotientGroup.eq]
      have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) b⁻¹)
      convert this using 1
      group
    generalize n * b * n⁻¹ = b' at h1 hπ
    have key : (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk a := by
      rw [← hπ]
      conv_lhs => rw [← h1]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hπ]
      have hab' : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b =
          QuotientGroup.mk b * QuotientGroup.mk a := by
        rw [← QuotientGroup.mk_mul, hab, QuotientGroup.mk_mul]
      calc (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b * QuotientGroup.mk a *
            (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹
          = QuotientGroup.mk a * (QuotientGroup.mk b * QuotientGroup.mk a) *
            (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹ := by group
        _ = QuotientGroup.mk a := by rw [← hab']; group
    exact QuotientGroup.eq.1 key.symm
  set t : X ⧸ N := QuotientGroup.mk e₀ with ht
  have hgen : ∀ y : X ⧸ N, y ∈ Subgroup.closure
      {z : X ⧸ N | ∃ g : X ⧸ N, z = g * t * g⁻¹} := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ Subgroup.closure E := (Pair.closure_eq hP).symm ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP he₀ hx)
      exact Subgroup.subset_closure ⟨QuotientGroup.mk g, by
        rw [ht, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]⟩
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [QuotientGroup.mk_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [QuotientGroup.mk_inv]; exact Subgroup.inv_mem _ hx
  have hYcomm : commutator (X ⧸ N) = ⊥ := by
    by_cases ht1 : t = 1
    ·
      have hall : ∀ y : X ⧸ N, y = 1 := fun y => by
        have hy := hgen y
        have hset : {z : X ⧸ N | ∃ g : X ⧸ N, z = g * t * g⁻¹} ⊆ {1} := by
          rintro _ ⟨g, rfl⟩
          rw [ht1, mul_one, mul_inv_cancel]
          rfl
        have := Subgroup.closure_mono hset hy
        rwa [Subgroup.closure_singleton_one, Subgroup.mem_bot] at this
      rw [eq_bot_iff]
      intro y _
      exact Subgroup.mem_bot.mpr (hall y)
    haveI : Fintype (X ⧸ N) := Fintype.ofFinite _
    have ht2 : t * t = 1 := by
      rw [ht, ← QuotientGroup.mk_mul, Pair.mul_self hP he₀, QuotientGroup.mk_one]
    have hisol : ∀ g : X ⧸ N, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
      intro g hg
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      have hxe : x * e₀ * x⁻¹ ∈ E := Pair.conj_mem hP he₀ x
      have hmk : (QuotientGroup.mk x : X ⧸ N) * t * (QuotientGroup.mk x)⁻¹ =
          QuotientGroup.mk (x * e₀ * x⁻¹) := by
        rw [ht, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rw [hmk] at hg ⊢
      exact mk_eq_of_commute_mk hP hcong hxe he₀ hg
    obtain ⟨M, hMn, hModd, hM⟩ := CFSG.ZStar.glauberman_zStar (X ⧸ N) t ht1 ht2 hisol
    have hle : commutator (X ⧸ N) ≤ M := by
      rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
      have hpow : ∀ y : X ⧸ N, (QuotientGroup.mk y : (X ⧸ N) ⧸ M) ∈
          Subgroup.zpowers (QuotientGroup.mk t : (X ⧸ N) ⧸ M) := by
        intro y
        have hy := hgen y
        induction hy using Subgroup.closure_induction with
        | mem z hz =>
          obtain ⟨g, rfl⟩ := hz
          have : (QuotientGroup.mk (g * t * g⁻¹) : (X ⧸ N) ⧸ M) = QuotientGroup.mk t := by
            refine (QuotientGroup.eq.mpr ?_).symm
            have := hMn.conj_mem _ (hM g) t⁻¹
            convert this using 1
            group
          rw [this]
          exact Subgroup.mem_zpowers _
        | one => exact Subgroup.one_mem _
        | mul x y _ _ hx hy => rw [QuotientGroup.mk_mul]; exact Subgroup.mul_mem _ hx hy
        | inv x _ hx => rw [QuotientGroup.mk_inv]; exact Subgroup.inv_mem _ hx
      refine ⟨⟨fun q₁ q₂ => ?_⟩⟩
      obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
      obtain ⟨k₁, hk₁⟩ := Subgroup.mem_zpowers_iff.1 (hpow g₁)
      obtain ⟨k₂, hk₂⟩ := Subgroup.mem_zpowers_iff.1 (hpow g₂)
      rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]
    haveI : Group.IsSolvable M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hModd
    haveI : Group.IsSolvable (commutator (X ⧸ N)) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
    have hperf : ⁅commutator (X ⧸ N), commutator (X ⧸ N)⁆ = commutator (X ⧸ N) := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hder
      rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective N),
        map_derivedSeries_eq (QuotientGroup.mk'_surjective N)] at h
      rw [← derivedSeries_one, ← derivedSeries_succ]
      exact h.symm
    haveI : Group.IsPerfect (commutator (X ⧸ N)) := Subgroup.isPerfect_iff.mpr hperf
    by_contra hne
    haveI : Nontrivial (commutator (X ⧸ N)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (G := commutator (X ⧸ N)) inferInstance
  have hle : commutator X ≤ N := by
    have h := map_derivedSeries_eq (QuotientGroup.mk'_surjective N) 1
    rw [derivedSeries_one, derivedSeries_one, hYcomm, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at h
    exact h
  rw [le_antisymm hle hNle]
  exact hNs

end CFSG.OddTranspositions.PartFour
