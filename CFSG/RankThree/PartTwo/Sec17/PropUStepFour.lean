module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepTwoA
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

theorem no_p_subgroup_normalized_by_inner_nine
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* J2)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (P B : Subgroup (MulAut X)) (hP : IsPGroup p P)
    (hB : B ≤ (MulAut.conj : X →* MulAut X).range) (hB9 : Nat.card B = 9)
    (hBP : B ≤ Subgroup.normalizer (P : Set (MulAut X))) : P = ⊥ := by
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.Native.center_eq_bot_of_j2 hX
  have h415 : CFSG.RankThree.PartTwo.Sec4.Item4_15 :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : a ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut X => φ g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.mp hg).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hPr : ∀ σ ∈ P, σ ∈ (MulAut.conj : X →* MulAut X).range := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hP ⟨σ, hσ⟩
    have hk' : σ ^ (p ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    exact CFSG.RankThree.PartTwo.Sec17.Proof17Res3.j2_mem_range_conj_of_pow_eq_one' hX hp
      (by omega) hk'
  set c : X →* MulAut X := MulAut.conj
  have hPP' : IsPGroup p (P.comap c) := hP.comap_of_injective c hinj
  have hB'card : Nat.card (B.comap c) = 9 := by
    have h1 : Nat.card ((B.comap c).map c) = Nat.card (B.comap c) :=
      Subgroup.card_map_of_injective hinj
    have h2 : (B.comap c).map c = B := Subgroup.map_comap_eq_self hB
    rw [← h1, h2, hB9]
  have hB'N : B.comap c ≤ Subgroup.normalizer ((P.comap c : Subgroup X) : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcb : c b ∈ Subgroup.normalizer (P : Set (MulAut X)) :=
      hBP (Subgroup.mem_comap.mp hb)
    rw [Subgroup.mem_normalizer_iff] at hcb
    have key := hcb (c x)
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact key
  have hPbot : P.comap c = ⊥ :=
    CFSG.RankThree.PartTwo.Sec17.Proof17Res3.j2_eq_bot_of_le_normalizer h415 hX hB'card hp hp3
      hPP' hB'N
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hPr σ hσ)
  have hxP : x ∈ P.comap c := by
    rw [Subgroup.mem_comap, hx]
    exact hσ
  rw [hPbot, Subgroup.mem_bot] at hxP
  rw [← hx, hxP, map_one]

theorem pu_pCoreOf_eq_map (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    CFSG.Open.pCoreOf p H = (CFSG.pCore p ↥H).map H.subtype := rfl

theorem pu_mem_pCoreOf_iff {p : ℕ} {G : Type*} [Group G] {H : Subgroup G} (x : ↥H) :
    (x : G) ∈ CFSG.Open.pCoreOf p H ↔ x ∈ CFSG.pCore p ↥H := by
  rw [pu_pCoreOf_eq_map]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

theorem equiv_J2_of_covers {G : Type} [Group G] [Finite G] {Y₀ X : Subgroup G} (hXY : X ≤ Y₀)
    (hXV : X ⊓ CFSG.Open.pCoreOf 2 Y₀ = ⊥) (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2)) : Nonempty (↥X ≃* J2) := by
  obtain ⟨e⟩ := hYJ
  let f : ↥X →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hXY)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr ?_
    intro x hx
    have hq : (QuotientGroup.mk (Subgroup.inclusion hXY x) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = 1 := hx
    have hmem : Subgroup.inclusion hXY x ∈ CFSG.pCore 2 ↥Y₀ := (QuotientGroup.eq_one_iff _).mp hq
    have hG : (x : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := (pu_mem_pCoreOf_iff _).mpr hmem
    have hxX : (x : G) ∈ X ⊓ CFSG.Open.pCoreOf 2 Y₀ := Subgroup.mem_inf.mpr ⟨x.2, hG⟩
    rw [hXV, Subgroup.mem_bot] at hxX
    exact Subtype.ext hxX
  have htop : X.subgroupOf Y₀ ⊔ CFSG.pCore 2 ↥Y₀ = ⊤ := by
    apply Subgroup.map_injective Y₀.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXY,
      ← pu_pCoreOf_eq_map 2 Y₀, ← hcov]
    exact (Subgroup.range_subtype Y₀).symm.trans (MonoidHom.range_eq_map _)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) q
    have hy : y ∈ X.subgroupOf Y₀ ⊔ CFSG.pCore 2 ↥Y₀ := by
      rw [htop]
      exact Subgroup.mem_top y
    obtain ⟨x', hx', v', hv', hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    refine ⟨⟨(x' : G), Subgroup.mem_subgroupOf.mp hx'⟩, ?_⟩
    show (QuotientGroup.mk x' : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = QuotientGroup.mk y
    rw [← hxy]
    apply QuotientGroup.eq.mpr
    rw [inv_mul_cancel_left]
    exact hv'
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).trans e⟩

theorem exists_mul_of_covers {G : Type} [Group G] {Y₀ X : Subgroup G} (hXY : X ≤ Y₀)
    (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀) {a : G} (ha : a ∈ Y₀) :
    ∃ x ∈ X, ∃ v ∈ CFSG.Open.pCoreOf 2 Y₀, a = x * v := by
  have htop : X.subgroupOf Y₀ ⊔ CFSG.pCore 2 ↥Y₀ = ⊤ := by
    apply Subgroup.map_injective Y₀.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXY]
    change X ⊔ CFSG.Open.pCoreOf 2 Y₀ = _
    rw [← hcov]
    exact (Subgroup.range_subtype Y₀).symm.trans (MonoidHom.range_eq_map _)
  have hy : (⟨a, ha⟩ : ↥Y₀) ∈ X.subgroupOf Y₀ ⊔ CFSG.pCore 2 ↥Y₀ := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨x', hx', v', hv', hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  refine ⟨(x' : G), Subgroup.mem_subgroupOf.mp hx', (v' : G),
    Subgroup.mem_map_of_mem Y₀.subtype hv', ?_⟩
  have := congrArg Subtype.val hxy
  simpa using this.symm

theorem step4
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J2))
    (hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {X T : Subgroup G} (hXY : X ≤ Y₀) (hXV : X ⊓ CFSG.Open.pCoreOf 2 Y₀ = ⊥)
    (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hTp : IsPGroup p T) : T ≤ Subgroup.centralizer (X : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h9, -, -, -, -⟩ := hs.j2_local hJ
  have hXJ : Nonempty (↥X ≃* J2) := equiv_J2_of_covers hXY hXV hcov hYJ
  have hZ : Subgroup.center ↥X = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.Native.center_eq_bot_of_j2 hXJ
  set ρ := X.normalizerMonoidHom with hρ
  set E := A ⊓ L with hE
  have hEA : E ≤ A := inf_le_left
  have hEN : E ≤ Subgroup.normalizer (X : Set G) := hEA.trans hAX
  have hEY : E ≤ Y₀ := inf_le_right.trans hs.le_y0
  let ρT : ↥T →* MulAut ↥X := ρ.comp (Subgroup.inclusion hTX)
  let ρE : ↥E →* MulAut ↥X := ρ.comp (Subgroup.inclusion hEN)
  have hVn : Y₀ ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) Y₀
  have hv_comm : ∀ a ∈ E, ∀ x ∈ X, ∀ v ∈ CFSG.Open.pCoreOf 2 Y₀, a = x * v →
      ∀ y ∈ X, v * y = y * v := by
    intro a ha x hx v hv hxv y hy
    have hvN : v ∈ Subgroup.normalizer (X : Set G) := by
      have hveq : v = x⁻¹ * a := by rw [hxv]; group
      rw [hveq]
      exact Subgroup.mul_mem _ (inv_mem (Subgroup.le_normalizer hx)) (hEN ha)
    have hz1 : v * y * v⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hvN y).mp hy
    have hzX : v * y * v⁻¹ * y⁻¹ ∈ X := Subgroup.mul_mem _ hz1 (inv_mem hy)
    have hz2 : y * v⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
      (Subgroup.mem_normalizer_iff.mp (hVn (hXY hy)) v⁻¹).mp (inv_mem hv)
    have hzV : v * y * v⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
      have := Subgroup.mul_mem _ hv hz2
      simpa [mul_assoc] using this
    have hz : v * y * v⁻¹ * y⁻¹ ∈ X ⊓ CFSG.Open.pCoreOf 2 Y₀ := ⟨hzX, hzV⟩
    rw [hXV, Subgroup.mem_bot] at hz
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using hz)
  have hconj : ∀ (a : G) (ha : a ∈ E) (x : G) (hx : x ∈ X) (v : G),
      v ∈ CFSG.Open.pCoreOf 2 Y₀ → a = x * v →
      ρ ⟨a, hEN ha⟩ = MulAut.conj (⟨x, hx⟩ : ↥X) := by
    intro a ha x hx v hv hxv
    ext y
    show a * (y : G) * a⁻¹ = x * (y : G) * x⁻¹
    have hvc := hv_comm a ha x hx v hv hxv y y.2
    rw [hxv]
    calc x * v * (y : G) * (x * v)⁻¹ = x * (v * y * v⁻¹) * x⁻¹ := by group
      _ = x * y * x⁻¹ := by rw [hvc]; group
  have hE3 : IsPGroup 3 E := hs.isE27.isPGroup.to_le inf_le_left
  have hV2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y₀) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective ρE := by
    refine (injective_iff_map_eq_one ρE).mpr ?_
    intro a ha1
    obtain ⟨x, hx, v, hv, hxv⟩ := exists_mul_of_covers hXY hcov (hEY a.2)
    have h1 : ρ ⟨(a : G), hEN a.2⟩ = 1 := ha1
    have h2 := hconj (a : G) a.2 x hx v hv hxv
    rw [h1] at h2
    have hxc : (⟨x, hx⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut ↥X => (σ g : ↥X)) h2
      simp only [MulAut.one_apply, MulAut.conj_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this.symm).symm
    rw [hZ, Subgroup.mem_bot] at hxc
    have hx1 : x = 1 := congrArg Subtype.val hxc
    have hav : (a : G) = v := by rw [hxv, hx1, one_mul]
    have haV : (a : G) ∈ E ⊓ CFSG.Open.pCoreOf 2 Y₀ := ⟨a.2, hav ▸ hv⟩
    have hdisj : E ⊓ CFSG.Open.pCoreOf 2 Y₀ = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) E _ hE3 hV2).eq_bot
    rw [hdisj, Subgroup.mem_bot] at haV
    exact Subtype.ext haV
  have hB9 : Nat.card ρE.range = 9 := by
    rw [← h9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hB : ρE.range ≤ (MulAut.conj : ↥X →* MulAut ↥X).range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx, v, hv, hxv⟩ := exists_mul_of_covers hXY hcov (hEY a.2)
    exact ⟨⟨x, hx⟩, (hconj (a : G) a.2 x hx v hv hxv).symm⟩
  have hP : IsPGroup p ρT.range := hTp.of_surjective ρT.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  have hBP : ρE.range ≤ Subgroup.normalizer (ρT.range : Set (MulAut ↥X)) := by
    have key : ∀ b ∈ ρE.range, ∀ q ∈ ρT.range, b * q * b⁻¹ ∈ ρT.range := by
      rintro _ ⟨a, rfl⟩ _ ⟨t, rfl⟩
      have hat : (a : G) * (t : G) * (a : G)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hAT (hEA a.2)) t).mp t.2
      refine ⟨⟨(a : G) * (t : G) * (a : G)⁻¹, hat⟩, ?_⟩
      show ρ ⟨(a : G) * (t : G) * (a : G)⁻¹, hTX hat⟩ =
        ρ ⟨(a : G), hEN a.2⟩ * ρ ⟨(t : G), hTX t.2⟩ * (ρ ⟨(a : G), hEN a.2⟩)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext rfl)
    intro b hb
    refine Subgroup.mem_normalizer_iff.mpr fun q => ⟨key b hb q, fun hq => ?_⟩
    have := key b⁻¹ (inv_mem hb) _ hq
    simpa [mul_assoc] using this
  have hPbot : ρT.range = ⊥ :=
    no_p_subgroup_normalized_by_inner_nine hXJ hp hp3 ρT.range ρE.range hP hB hB9 hBP
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : ρT ⟨t, ht⟩ ∈ ρT.range := ⟨⟨t, ht⟩, rfl⟩
  rw [hPbot, Subgroup.mem_bot] at h1
  have h2 := congrArg (fun σ : MulAut ↥X => ((σ ⟨y, hy⟩ : ↥X) : G)) h1
  simp only [MulAut.one_apply] at h2
  have h3 : t * y * t⁻¹ = y := h2
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

end CFSG.RankThree.PartTwo.Sec17.PropU
