module

public import CFSG.Quasithin.Background.G8Core
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.RankTwoShapes
open scoped commutatorElement

namespace G8

section Finite

variable {L : Type*} [Group L] [Finite L]

theorem exists_pow_orderOf_coprime {p : ℕ} (hp : p.Prime) (g : L) :
    ∃ e : ℕ, (orderOf (g ^ p ^ e)).Coprime p := by
  obtain ⟨e, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have hpe : 0 < p ^ e := pow_pos hp.pos e
  refine ⟨e, ?_⟩
  have h1 : orderOf (g ^ p ^ e) = n' := by
    rw [orderOf_pow_of_dvd hpe.ne' (hn ▸ dvd_mul_right _ _), hn, Nat.mul_div_cancel_left _ hpe]
  rw [h1]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn').symm

theorem normalizer_eq_mul_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hΩ : ∀ y : L, orderOf y = p → y ∈ Subgroup.center L) {S Q : Subgroup L} (hQS : Q ≤ S)
    (hS : IsPGroup p S)
    (hidx : Nat.Coprime p
      ((S ⊓ Subgroup.normalizer (Q : Set L)).subgroupOf (Subgroup.normalizer (Q : Set L))).index) :
    ∀ n ∈ Subgroup.normalizer (Q : Set L), ∃ s ∈ S ⊓ Subgroup.normalizer (Q : Set L),
      ∃ z ∈ Subgroup.centralizer (Q : Set L), n = s * z := by
  set Nn := Subgroup.normalizer (Q : Set L) with hNn
  set C := Subgroup.centralizer (Q : Set L) with hC
  have hQp : IsPGroup p Q := hS.to_le hQS
  have hCN : C ≤ Nn := Subgroup.centralizer_le_normalizer _
  have hpp : ∀ g ∈ Nn, (orderOf g).Coprime p → g ∈ C := by
    intro g hg hcop
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := centralizes_of_centralizes_orderP hp2 hQp hg hcop
      (fun y' _ hyo => (Subgroup.mem_center_iff.mp (hΩ y' hyo) g)) y hy
    exact this.symm
  set Ĉ : Subgroup Nn := C.subgroupOf Nn with hĈ
  have hĈn : Ĉ.Normal := inferInstance
  have hpq : IsPGroup p (Nn ⧸ Ĉ) := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, he⟩ := exists_pow_orderOf_coprime (Fact.out : p.Prime) (n : L)
    refine ⟨e, ?_⟩
    have hmem : (n : L) ^ p ^ e ∈ C := hpp _ (Nn.pow_mem n.2 _) he
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  set T : Subgroup Nn := (S ⊓ Nn).subgroupOf Nn with hT
  set φ : Nn →* Nn ⧸ Ĉ := QuotientGroup.mk' Ĉ with hφ
  obtain ⟨k, hk⟩ := hpq.index (T.map φ)
  have hdvd : (T.map φ).index ∣ T.index := Subgroup.index_map_dvd T (QuotientGroup.mk'_surjective Ĉ)
  have hpk : p ^ k = 1 := by
    rw [hk] at hdvd
    exact (Nat.Coprime.pow_left k hidx).eq_one_of_dvd hdvd
  have htop : T.map φ = ⊤ := Subgroup.index_eq_one.mp (by rw [hk, hpk])
  intro n hn
  have hmem : φ ⟨n, hn⟩ ∈ T.map φ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have hz : t⁻¹ * ⟨n, hn⟩ ∈ Ĉ := QuotientGroup.eq.mp hteq
  refine ⟨(t : L), ht, (t : L)⁻¹ * n, hz, ?_⟩
  simp

theorem fusion_in_sylow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hΩ : ∀ y : L, orderOf y = p → y ∈ Subgroup.center L) (S : Sylow p L)
    {P : Subgroup L} {c : L} (hdec : AlperinDecomposition p (S : Subgroup L) P c) :
    ∀ x ∈ P, ∃ m ∈ (S : Subgroup L), c⁻¹ * x * c = m⁻¹ * x * m := by
  induction hdec with
  | one => intro x hx; exact ⟨1, one_mem _, by simp⟩
  | @step c n Q _ hQ hPQ hn ih =>
    intro x hx
    obtain ⟨m, hm, hxm⟩ := ih x hx
    have hx'Q : c⁻¹ * x * c ∈ Q := by
      apply hPQ
      refine ⟨x, hx, ?_⟩
      simp
    obtain ⟨s, hs, z, hz, hnz⟩ :=
      normalizer_eq_mul_centralizer hp2 hΩ hQ.1 S.isPGroup' hQ.2.1 n hn
    refine ⟨m * s, (S : Subgroup L).mul_mem hm hs.1, ?_⟩
    have hsN : s ∈ Subgroup.normalizer (Q : Set L) := hs.2
    have h1 : s⁻¹ * (c⁻¹ * x * c) * s ∈ Q := (Subgroup.mem_normalizer_iff''.mp hsN _).mp hx'Q
    have h2 : z⁻¹ * (s⁻¹ * (c⁻¹ * x * c) * s) * z = s⁻¹ * (c⁻¹ * x * c) * s := by
      have hzc : z⁻¹ ∈ Subgroup.centralizer (Q : Set L) := Subgroup.inv_mem _ hz
      have := Subgroup.mem_centralizer_iff.mp hzc _ h1
      rw [← this]
      simp
    calc (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
      _ = z⁻¹ * (s⁻¹ * (c⁻¹ * x * c) * s) * z := by rw [hnz]; group
      _ = s⁻¹ * (c⁻¹ * x * c) * s := h2
      _ = s⁻¹ * (m⁻¹ * x * m) * s := by rw [hxm]
      _ = (m * s)⁻¹ * x * (m * s) := by group

theorem sylow_le_commutator {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hΩ : ∀ y : L, orderOf y = p → y ∈ Subgroup.center L) (hperf : commutator L = ⊤)
    (S : Sylow p L) : (S : Subgroup L) ≤ ⁅(S : Subgroup L), (S : Subgroup L)⁆ := by
  have hfocal := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p S
  have hder : CFSG.derivedSubgroup L = ⊤ := by
    rw [CFSG.derivedSubgroup, derivedSeries_one]; exact hperf
  rw [hder, inf_top_eq] at hfocal
  refine hfocal.le.trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hP : Subgroup.zpowers x ≤ (S : Subgroup L) := Subgroup.zpowers_le.mpr hx
  have hPg : (Subgroup.zpowers x).map (MulAut.conj c).toMonoidHom ≤ (S : Subgroup L) := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    simpa [hc] using hy
  obtain ⟨c₀, hdec, hc₀⟩ := alperin_centric_radical_fusion S hP (g := c⁻¹) (by simpa using hPg)
  have hx0 : c₀⁻¹ * x * c₀ = y := by
    have := hc₀ x (Subgroup.mem_zpowers x)
    rw [this]
    simpa using hc
  obtain ⟨m, hm, hxm⟩ := fusion_in_sylow hp2 hΩ S hdec x (Subgroup.mem_zpowers x)
  have : x⁻¹ * y = ⁅x⁻¹, m⁻¹⁆ := by
    rw [← hx0, hxm]
    simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact Subgroup.commutator_mem_commutator ((S : Subgroup L).inv_mem hx)
    ((S : Subgroup L).inv_mem hm)

theorem not_dvd_card_of_perfect {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hΩ : ∀ y : L, orderOf y = p → y ∈ Subgroup.center L) (hperf : commutator L = ⊤) :
    ¬ p ∣ Nat.card L := by
  intro hdvd
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p L))
  have hle := sylow_le_commutator hp2 hΩ hperf S
  have hperfS : Group.IsPerfect (S : Subgroup L) := by
    refine ⟨?_⟩
    have h1 : (commutator (S : Subgroup L)).map (S : Subgroup L).subtype =
        ⁅(S : Subgroup L), (S : Subgroup L)⁆ := Subgroup.map_subtype_commutator _
    have h2 : (⊤ : Subgroup (S : Subgroup L)).map (S : Subgroup L).subtype = (S : Subgroup L) := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective (S : Subgroup L).subtype_injective,
      h1, h2]
    exact hle
  have : Group.IsNilpotent (S : Subgroup L) := S.isPGroup'.isNilpotent
  have hsub : Subsingleton (S : Subgroup L) :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  have hcard : Nat.card (S : Subgroup L) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
  rw [S.card_eq_multiplicity] at hcard
  have hpos : 0 < (Nat.card L).factorization p :=
    (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd)
  have : p ^ (Nat.card L).factorization p ≥ p := Nat.le_self_pow hpos.ne' p
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  omega


omit [Finite L] in
theorem normal_lambdaSubgroup_top : (lambdaSubgroup (⊤ : Subgroup L)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    have : orderOf (g * x * g⁻¹) = orderOf x := (MulAut.conj g).orderOf_eq x
    rw [this]; exact hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    simpa [mul_assoc] using this

end Finite

end G8

theorem lambdaSubgroup_top_eq_top {L : Type*} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) :
    lambdaSubgroup (⊤ : Subgroup L) = ⊤ := by
  have hnormal := G8.normal_lambdaSubgroup_top (L := L)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    (lambdaSubgroup (⊤ : Subgroup L)) with hcenter | htop
  · exfalso
    have hΩ : ∀ {p : ℕ}, p.Prime → ∀ y : L, orderOf y = p → y ∈ Subgroup.center L := by
      intro p hp y hy
      exact hcenter (mem_lambdaSubgroup (Subgroup.mem_top _) (hy ▸ hp))
    have hnodd : ∀ d : ℕ, d.Prime → d ∣ Nat.card L → d = 2 := by
      intro d hd hdvd
      by_contra hd2
      have : Fact d.Prime := ⟨hd⟩
      exact G8.not_dvd_card_of_perfect hd2 (hΩ hd) hq.1 hdvd
    have hcard := Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdvd => hnodd d hd hdvd)
    have h2 : IsPGroup 2 L := IsPGroup.of_card hcard
    have : Group.IsNilpotent L := h2.isNilpotent
    have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    have hperf : Group.IsPerfect L := ⟨hq.1⟩
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · exact htop

theorem lambdaSubgroup_eq_of_isQuasisimple {H : Type*} [Group H] [Finite H] {L : Subgroup H}
    (hq : CFSG.Open.IsQuasisimple L) : lambdaSubgroup L = L := by
  have htop := lambdaSubgroup_top_eq_top hq
  have h1 : (lambdaSubgroup (⊤ : Subgroup L)).map L.subtype = lambdaSubgroup L := by
    unfold lambdaSubgroup
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨-, hxp⟩, rfl⟩
      exact ⟨x.2, by rw [← Subgroup.orderOf_coe] at hxp; exact hxp⟩
    · rintro ⟨hy, hyp⟩
      exact ⟨⟨y, hy⟩, ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hyp⟩, rfl⟩
  rw [← h1, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.Quasithin
