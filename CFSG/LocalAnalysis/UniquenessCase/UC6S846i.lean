module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl1
public import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
public import CFSG.LocalAnalysis.UniquenessCase.UCKPOut
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem map_rhoL_le_inner {M L : Subgroup G} (hN : M ≤ normalizer (L : Set G)) {n : ℕ}
    (hX : IsSU3 (Bar2 L) n) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ 2 ^ n + 1)
    (hOp : UC22.F10.OpRes p M = M) {A : Subgroup G} (hAM : A ≤ M) (hAel : IsElemAbelian p A) :
    (A.subgroupOf (normalizer (L : Set G))).map (rhoL L) ≤
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
  obtain ⟨Nsub, hNn, -, hcyc, hcube, hEven⟩ := UCK.u3OutShape (Bar2 L) n hX
  haveI := hNn
  have hgen := closure_pPrime_map (rhoL L) _ (closure_pPrime_subgroupOf hN (p := p) hOp)
  have hp3 : p ≠ 3 ∨ Nsub ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    by_cases h3 : p = 3
    · right
      apply hEven
      rcases Nat.even_or_odd n with h | h
      · exact h
      · exfalso; exact hpn (h3 ▸ three_dvd_two_pow_add_one h)
    · exact Or.inl h3
  rintro _ ⟨a, ha, rfl⟩
  have haA : (a : G) ∈ A := ha
  have hap : rhoL L a ^ (p ^ 1) = 1 := by
    rw [← map_pow]
    have : a ^ p ^ 1 = 1 := Subtype.ext (by simpa using hAel.2 _ haA)
    rw [this, map_one]
  exact mem_inner_of_pPow _ Nsub _ hcyc hcube hp hp3 hgen
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hAM haA))) hap

theorem exists_sub_fixing_sylow (hgr : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G}
    (hN : M ≤ normalizer (L : Set G)) {n : ℕ} (hX : IsSU3 (Bar2 L) n) {q p : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) (hp : p.Prime) (hp2 : p ≠ 2)
    (hOp : UC22.F10.OpRes p M = M) {B : Subgroup G} (hBM : B ≤ M) (hBel : IsElemAbelian p B)
    {k : ℕ} (hBcard : Nat.card B = p ^ (k + 1)) :
    ∃ B₁ : Subgroup G, B₁ ≤ B ∧ p ^ k ≤ Nat.card B₁ ∧
      (B₁ = B ∨ ∀ b (hb : b ∈ normalizer (L : Set G)), b ∈ B₁ → rhoL L ⟨b, hb⟩ = 1) ∧
      ∃ Sb : Sylow q (Bar2 L), ∀ b (hb : b ∈ normalizer (L : Set G)), b ∈ B₁ →
        ∀ s ∈ (Sb : Subgroup (Bar2 L)), rhoL L ⟨b, hb⟩ s ∈ (Sb : Subgroup (Bar2 L)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hBN : B ≤ normalizer (L : Set G) := hBM.trans hN
  by_cases hpn : p ∣ 2 ^ n + 1
  · have hndvd := UCK.u3SylCount_of_griess hgr (Bar2 L) n hX q p hq hq3 hqn hp hp2 hpn
    letI : MulDistribMulAction ↥B (Bar2 L) :=
      MulDistribMulAction.compHom _ ((rhoL L).comp (Subgroup.inclusion hBN))
    letI : MulAction ↥B (Sylow q (Bar2 L)) := Sylow.pointwiseMulAction
    obtain ⟨Sb, hSb⟩ := hBel.isPGroup.nonempty_fixed_point_of_prime_not_dvd_card _ hndvd
    refine ⟨B, le_rfl, by rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega), Or.inl rfl,
      Sb, ?_⟩
    intro b hb hbB s hs
    have hfix : (⟨b, hbB⟩ : ↥B) • (Sb : Subgroup (Bar2 L)) = Sb := by
      rw [← Sylow.pointwise_smul_def]
      exact congrArg Sylow.toSubgroup (hSb ⟨b, hbB⟩)
    have h1 := Subgroup.smul_mem_pointwise_smul s (⟨b, hbB⟩ : ↥B) (Sb : Subgroup (Bar2 L)) hs
    rw [hfix] at h1
    exact h1
  · let BN : Subgroup ↥(normalizer (L : Set G)) := B.subgroupOf (normalizer (L : Set G))
    let φ : ↥BN →* MulAut (Bar2 L) := (rhoL L).comp BN.subtype
    have hφrange : φ.range = BN.map (rhoL L) := by
      ext y
      simp only [φ, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
    have hR : Nat.card φ.range ≤ p := by
      rw [hφrange]
      exact UCK.u3RankOne (Bar2 L) n hX p hp hp2 hpn _
        (map_rhoL_le_inner hN hX hp hpn hOp hBM hBel) ((hBel.subgroupOf _).map _)
    have hBNcard : Nat.card BN = p ^ (k + 1) := by
      rw [← hBcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
    have hker : p ^ (k + 1) = Nat.card φ.range * Nat.card φ.ker := by
      rw [← hBNcard, Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have htriv : ∀ b (hb : b ∈ normalizer (L : Set G)),
        b ∈ (φ.ker.map BN.subtype).map (normalizer (L : Set G)).subtype → rhoL L ⟨b, hb⟩ = 1 := by
      intro b hb hbB
      obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hbB
      exact (MonoidHom.mem_ker).1 hc
    refine ⟨(φ.ker.map BN.subtype).map (normalizer (L : Set G)).subtype, ?_, ?_, Or.inr htriv,
      default, ?_⟩
    · calc _ ≤ BN.map (normalizer (L : Set G)).subtype :=
            Subgroup.map_mono (Subgroup.map_subtype_le _)
        _ = B := Subgroup.map_subgroupOf_eq_of_le hBN
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      have h1 : p * p ^ k ≤ p * Nat.card φ.ker :=
        calc p * p ^ k = p ^ (k + 1) := by ring
          _ = _ := hker
          _ ≤ p * Nat.card φ.ker := Nat.mul_le_mul_right _ hR
      exact Nat.le_of_mul_le_mul_left h1 hp.pos
    · intro b hb hbB s hs
      rw [htriv b hb hbB]
      exact hs

theorem exists_lift_normalized {L B₁ : Subgroup G} (hB₁N : B₁ ≤ normalizer (L : Set G)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q) (hp2 : p ≠ 2) (hB₁p : IsPGroup p B₁)
    (Sb : Sylow q (Bar2 L))
    (hSb : ∀ b (hb : b ∈ normalizer (L : Set G)), b ∈ B₁ →
      ∀ s ∈ (Sb : Subgroup (Bar2 L)), rhoL L ⟨b, hb⟩ s ∈ (Sb : Subgroup (Bar2 L))) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup q S ∧
      (∀ T : Subgroup G, T ≤ L → IsPGroup q T → S ≤ T → T = S) ∧
      (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb ∧
      B₁ ≤ normalizer (S : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Y : Subgroup G := ((Sb : Subgroup (Bar2 L)).comap π).map L.subtype with hYdef
  have hmemY : ∀ y : ↥L, (y : G) ∈ Y ↔ π y ∈ (Sb : Subgroup (Bar2 L)) := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      obtain rfl : y' = y := Subtype.ext hyy'
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hB₁Y : B₁ ≤ normalizer (Y : Set G) := by
    have key : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y := by
      rintro b hb _ ⟨y', hy', rfl⟩
      have hbN := hB₁N hb
      have h1 := rhoL_mk_coe L ⟨b, hbN⟩ y'
      simp only at h1
      rw [Subgroup.coe_subtype, ← h1, hmemY]
      exact hSb b hbN hb _ hy'
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key b hb y, fun hy => ?_⟩
    have := key b⁻¹ (B₁.inv_mem hb) _ hy
    simpa [mul_assoc] using this
  have hYp : ¬ p ∣ Nat.card Y := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨y', hy', hyy'⟩ := y.2
    have hoy : orderOf y' = p := by
      rw [← Subgroup.orderOf_coe, show ((y' : ↥L) : G) = ((y : ↥Y) : G) from hyy',
        Subgroup.orderOf_coe, hy]
    have hy'p : y' ^ p = 1 := hoy ▸ pow_orderOf_eq_one y'
    have hπy : π y' = 1 := by
      obtain ⟨k, hk⟩ := Sb.isPGroup' ⟨π y', hy'⟩
      have hk' : (π y') ^ (q ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have hp' : (π y') ^ p = 1 := by rw [← map_pow, hy'p, map_one]
      exact (pow_eq_one_iff_of_coprime
        (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 hpq))).1 ⟨hp', hk'⟩
    obtain ⟨j, hj⟩ := hker ⟨y', hπy⟩
    have hj' : y' ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have h1 : y' = 1 := (pow_eq_one_iff_of_coprime
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2))).1 ⟨hy'p, hj'⟩
    rw [h1, orderOf_one] at hoy
    exact hp.one_lt.ne hoy
  obtain ⟨T, hT⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hq hB₁p hB₁Y hYp
  set S : Subgroup G := (T : Subgroup ↥Y).map Y.subtype with hSdef
  have hSY : S ≤ Y := Subgroup.map_subtype_le _
  have hSL : S ≤ L := hSY.trans (Subgroup.map_subtype_le _)
  have hSq : IsPGroup q S := T.isPGroup'.map _
  set SL : Subgroup ↥L := S.subgroupOf L with hSLdef
  have hSLq : IsPGroup q SL := hSq.comap_subtype
  have hSLdisj : Disjoint SL π.ker := by
    rw [Subgroup.disjoint_def]
    exact fun hx1 hx2 => eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hSLq hker hx1 hx2
  have hSLmap : SL.map π = Sb := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmemY x).1 (hSY hx)
    rw [card_map_of_disjoint_ker π SL hSLdisj, hSLdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hSdef,
      Subgroup.card_map_of_injective Y.subtype_injective, T.card_eq_multiplicity]
    obtain ⟨a, ha⟩ := Sb.isPGroup'.exists_card_eq
    have hdvd : Nat.card (Sb : Subgroup (Bar2 L)) ∣ Nat.card Y := by
      rw [hYdef, Subgroup.card_map_of_injective L.subtype_injective]
      conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective hπsurj (Sb : Subgroup (Bar2 L))]
      exact Subgroup.card_map_dvd _ _
    rw [ha] at hdvd ⊢
    exact Nat.pow_le_pow_right hq.pos ((hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd)
  have hSLmax := lift_maximal π SL (Sb : Subgroup (Bar2 L)) hSLmap hSLdisj hker hq hq2
    (fun T' hT' hST' => Sb.is_maximal' hT' hST') hSLq
  refine ⟨S, hSL, hSq, fun T' hT'L hT' hST' => ?_, hSLmap, hT⟩
  have h1 := hSLmax _ (hT'.of_equiv (Subgroup.subgroupOfEquivOfLe hT'L).symm)
    (fun x hx => hST' hx)
  calc T' = (T'.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hT'L).symm
    _ = SL.map L.subtype := by rw [h1]
    _ = S := Subgroup.map_subgroupOf_eq_of_le hSL

theorem exists_omega_normalized (hgr : CFSG.Open.GriessAllModelsStatement) {L : Subgroup G}
    {n : ℕ} (hX : IsSU3 (Bar2 L) n) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1)
    {S : Subgroup G} (hSL : S ≤ L) (hSq : IsPGroup q S) (Sb : Sylow q (Bar2 L))
    (hSmap : (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb) :
    ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      normalizer (S : Set G) ≤ normalizer (E : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  obtain ⟨Eb, hEbS, hEbel, hEbcard, hEbΩ⟩ :=
    UCK.u3SylOmega_of_griess hgr (Bar2 L) n hX q hq hq3 hqn Sb Sb.isPGroup' Sb.not_dvd_index
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπdef
  have hker : IsPGroup 2 π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hSLdisj : Disjoint (S.subgroupOf L) π.ker := by
    rw [Subgroup.disjoint_def]
    exact fun hx1 hx2 =>
      eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hSq.comap_subtype hker hx1 hx2
  let E' : Subgroup ↥L := S.subgroupOf L ⊓ Eb.comap π
  have hE'map : E'.map π = Eb := by
    ext y
    constructor
    · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
      exact hx2
    · intro hy
      have hyS : y ∈ (S.subgroupOf L).map π := by rw [hSmap]; exact hEbS hy
      obtain ⟨x, hxS, rfl⟩ := hyS
      exact ⟨x, ⟨hxS, hy⟩, rfl⟩
  have hE'disj : Disjoint E' π.ker := hSLdisj.mono_left inf_le_left
  set E : Subgroup G := E'.map L.subtype with hEdef
  have hES : E ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.1
  have hEel : IsElemAbelian q E :=
    (isElemAbelian_of_disjoint_ker π E' hE'disj (by rw [hE'map]; exact hEbel)).map L.subtype
  have hEcard : Nat.card E = q ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_of_disjoint_ker π E' hE'disj, hE'map, hEbcard]
  have hΩ : ∀ s ∈ S, s ^ q = 1 → s ∈ E := by
    intro s hs hsq
    have hsL : s ∈ L := hSL hs
    refine ⟨⟨s, hsL⟩, ⟨hs, hEbΩ _ ?_ ?_⟩, rfl⟩
    · rw [← hSmap]
      exact ⟨⟨s, hsL⟩, hs, rfl⟩
    · rw [← map_pow]
      have : (⟨s, hsL⟩ : ↥L) ^ q = 1 := Subtype.ext (by simpa using hsq)
      rw [this, map_one]
  refine ⟨E, hES, hEel, hEcard, ?_⟩
  have key : ∀ b ∈ normalizer (S : Set G), ∀ x ∈ E, b * x * b⁻¹ ∈ E := by
    intro b hb x hx
    refine hΩ _ ((Subgroup.mem_normalizer_iff.1 hb x).1 (hES hx)) ?_
    rw [conj_pow, hEel.2 x hx, mul_one, mul_inv_cancel]
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key b hb x, fun hx => ?_⟩
  have := key b⁻¹ (inv_mem hb) _ hx
  simpa [mul_assoc] using this

theorem keyLemma4 (hgr : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G} (hLM : L ≤ M)
    (hN : M ≤ normalizer (L : Set G)) {n : ℕ} (hX : IsSU3 (Bar2 L) n) {q p : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q)
    (hOp : UC22.F10.OpRes p M = M) (hrank : 4 ≤ Open.pRank p M) :
    ∃ S E : Subgroup G, S ≤ L ∧ IsPGroup q S ∧
      (∀ T : Subgroup G, T ≤ L → IsPGroup q T → S ≤ T → T = S) ∧
      E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      3 ≤ Open.pRank p (M ⊓ normalizer (E : Set G)) ∧
      ∃ Sb : Subgroup (Bar2 L), IsPGroup q Sb ∧ ¬ q ∣ Sb.index ∧
        (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  obtain ⟨B, hBM, hBel, hBcard⟩ := exists_elemAbelian_card_of_le_pRank hp hrank
  obtain ⟨B₁, hB₁B, hB₁card, -, Sb, hSb⟩ :=
    exists_sub_fixing_sylow hgr hN hX hq hq3 hqn hp hp2 hOp hBM hBel (k := 3) hBcard
  obtain ⟨S, hSL, hSq, hSmax, hSmap, hB₁S⟩ := exists_lift_normalized (hB₁B.trans (hBM.trans hN))
    hp hq hq2 hpq hp2 (hBel.isPGroup.to_le hB₁B) Sb hSb
  obtain ⟨E, hES, hEel, hEcard, hNE⟩ := exists_omega_normalized hgr hX hq hq3 hqn hSL hSq Sb hSmap
  obtain ⟨j, hj⟩ := (hBel.isPGroup.to_le hB₁B).exists_card_eq
  have hj3 : 3 ≤ j := by
    rw [hj] at hB₁card
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hB₁card
  have hrk := le_pRank' hp (le_inf (hB₁B.trans hBM) (hB₁S.trans hNE)) (hBel.mono hB₁B) hj
  exact ⟨S, E, hSL, hSq, hSmax, hES, hEel, hEcard, by omega, Sb, Sb.isPGroup', Sb.not_dvd_index,
    hSmap⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
