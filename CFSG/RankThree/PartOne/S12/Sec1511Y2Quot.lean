module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

section Order

variable {H : Type*} [Group H]

@[expose] def OrderModC (B : Subgroup H) (n : H) (r : ℕ) : Prop :=
  0 < r ∧ n ^ r ∈ Subgroup.centralizer (B : Set H) ∧
    ∀ k : ℕ, 0 < k → k < r → n ^ k ∉ Subgroup.centralizer (B : Set H)

theorem orderModC_dvd {B : Subgroup H} {n : H} {r L : ℕ} (h : OrderModC B n r)
    (hL : n ^ L ∈ Subgroup.centralizer (B : Set H)) : r ∣ L := by
  obtain ⟨hr, hnr, hmin⟩ := h
  have hmod : n ^ (L % r) ∈ Subgroup.centralizer (B : Set H) := by
    have h1 : n ^ L = (n ^ r) ^ (L / r) * n ^ (L % r) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h2 : n ^ (L % r) = ((n ^ r) ^ (L / r))⁻¹ * n ^ L := by rw [h1]; group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hnr _)) hL
  by_contra hdvd
  have hpos : 0 < L % r := Nat.pos_of_ne_zero fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
  exact hmin (L % r) hpos (Nat.mod_lt L hr) hmod

end Order

section Quot

variable {M : Type} [Group M] [Finite M] {p : ℕ}

theorem spe_map_quotient [Fact p.Prime] {Y K : Subgroup M} [K.Normal] (hY : IsStronglyPEmbedded p Y)
    (hKY : K ≤ Y) (hKp : ¬ p ∣ Nat.card K) :
    IsStronglyPEmbedded p (Y.map (QuotientGroup.mk' K)) := by
  classical
  set π : M →* M ⧸ K := QuotientGroup.mk' K with hπ
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hY.1
    rw [eq_top_iff]
    intro y _
    have hy : π y ∈ Y.map π := by rw [h]; trivial
    obtain ⟨y', hy', hyy'⟩ := hy
    have hk : y'⁻¹ * y ∈ K := QuotientGroup.eq.1 hyy'
    have : y = y' * (y'⁻¹ * y) := by group
    rw [this]
    exact Y.mul_mem hy' (hKY hk)
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hY.2.1
    have hxp : (x : M) ^ p = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hπx : π x ≠ 1 := by
      intro h1
      have hxK : (x : M) ∈ K := (QuotientGroup.eq_one_iff _).1 h1
      apply hKp
      have h2 := orderOf_dvd_natCard (⟨x, hxK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at h2
    have hπp : (π x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hord : orderOf (π x) = p := orderOf_eq_prime hπp hπx
    have h3 := orderOf_dvd_natCard (⟨π x, ⟨x, x.2, rfl⟩⟩ : ↥(Y.map π))
    have h4 : orderOf (⟨π x, ⟨x, x.2, rfl⟩⟩ : ↥(Y.map π)) = p :=
      (Subgroup.orderOf_coe (⟨π x, ⟨x, x.2, rfl⟩⟩ : ↥(Y.map π))).symm.trans hord
    rwa [h4] at h3
  · intro ĝ hĝ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K ĝ
    have hg : g ∉ Y := fun h => hĝ ⟨g, h, rfl⟩
    intro hdvd
    apply hY.2.2 g hg
    have hsub : (Y.map π) ⊓ (Y.map π).map (MulAut.conj (π g)).toMonoidHom ≤
        (Y ⊓ conjSub g Y).map π := by
      rintro _ ⟨⟨y, hy, rfl⟩, ŷ, ⟨y', hy', rfl⟩, hŷ⟩
      have h1 : π (g * y' * g⁻¹) = π y := by simpa [map_mul, MulAut.conj_apply] using hŷ
      have hk : y⁻¹ * (g * y' * g⁻¹) ∈ K := QuotientGroup.eq.1 h1.symm
      refine ⟨y, Subgroup.mem_inf.2 ⟨hy, ?_⟩, rfl⟩
      rw [mem_conjSub_iff]
      have hk' : g⁻¹ * (y⁻¹ * (g * y' * g⁻¹))⁻¹ * g ∈ K := by
        have := (inferInstance : K.Normal).conj_mem _ (K.inv_mem hk) g⁻¹
        simpa using this
      have e : g⁻¹ * y * g = y' * (g⁻¹ * (y⁻¹ * (g * y' * g⁻¹))⁻¹ * g) := by group
      rw [e]
      exact Y.mul_mem hy' (hKY hk')
    exact (hdvd.trans (Subgroup.card_dvd_of_le hsub)).trans (Subgroup.card_map_dvd _ _)

end Quot

section Img

variable {M : Type} [Group M] {p : ℕ} [Fact p.Prime] {O : Subgroup M} [O.Normal]

omit [O.Normal] in
theorem inf_eq_bot_of_isPGroup {T : Subgroup M} (hT : IsPGroup p ↥T) (hO : ¬ p ∣ Nat.card O) :
    T ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxT, hxO⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hT ⟨x, hxT⟩
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
  by_contra hx1
  have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hj)
  exact hO ((dvd_pow_self p hj0).trans (hj ▸ h2))

theorem eq_of_mk'_eq {T : Subgroup M} (hT : IsPGroup p ↥T) (hO : ¬ p ∣ Nat.card O) {x y : M}
    (hx : x ∈ T) (hy : y ∈ T) (h : QuotientGroup.mk' O x = QuotientGroup.mk' O y) : x = y := by
  have h1 : x⁻¹ * y ∈ O := QuotientGroup.eq.1 h
  have h2 : x⁻¹ * y ∈ T ⊓ O := ⟨T.mul_mem (T.inv_mem hx) hy, h1⟩
  rw [inf_eq_bot_of_isPGroup hT hO, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem card_map_mk' {T : Subgroup M} (hT : IsPGroup p ↥T) (hO : ¬ p ∣ Nat.card O) :
    Nat.card ↥(T.map (QuotientGroup.mk' O)) = Nat.card ↥T := by
  have hinj : Function.Injective ((QuotientGroup.mk' O).subgroupMap T) := by
    intro a b hab
    apply Subtype.ext
    exact eq_of_mk'_eq hT hO a.2 b.2 (congrArg Subtype.val hab)
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨hinj, (QuotientGroup.mk' O).subgroupMap_surjective T⟩)).symm

theorem omegaOne_map_mk' {T : Subgroup M} (hT : IsPGroup p ↥T) (hO : ¬ p ∣ Nat.card O) :
    omegaOne p (T.map (QuotientGroup.mk' O)) = (omegaOne p T).map (QuotientGroup.mk' O) := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro y ⟨⟨x, hxT, rfl⟩, hy⟩
    refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
    have h1 : QuotientGroup.mk' O (x ^ p) = QuotientGroup.mk' O 1 := by
      rw [map_pow, map_one]
      exact hy
    exact eq_of_mk'_eq hT hO (T.pow_mem hxT p) T.one_mem h1
  · apply Subgroup.closure_mono
    rintro _ ⟨x, ⟨hxT, hxp⟩, rfl⟩
    exact ⟨⟨x, hxT, rfl⟩, by rw [← map_pow, hxp, map_one]⟩

omit [Fact p.Prime] in
theorem isSylowOf_map_mk' {P : Subgroup M} (hP : IsSylowOf p P ⊤) :
    IsSylowOf p (P.map (QuotientGroup.mk' O)) ⊤ := by
  refine ⟨le_top, hP.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.index_map_dvd (H := P) (QuotientGroup.mk'_surjective O)
  have hP' : ¬ p ∣ P.index := by simpa [Subgroup.relIndex_top_right] using hP.2.2
  exact fun hd => hP' (hd.trans h)

theorem exists_lift_normalizer [Finite M] {T : Subgroup M} (hT : IsPGroup p ↥T) (hO : ¬ p ∣ Nat.card O)
    {y : M ⧸ O}
    (hy : y ∈ Subgroup.normalizer ((T.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O))) :
    ∃ n ∈ Subgroup.normalizer (T : Set M), QuotientGroup.mk' O n = y := by
  have : Fact (IsPGroup p ↥T) := ⟨hT⟩
  have h := normalizer_map_quotient_eq_map_normalizer p T O inferInstance
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hO)
  have hy' : y ∈ (Subgroup.normalizer (T : Set M)).map (QuotientGroup.mk' O) := by
    rw [← h]; exact hy
  obtain ⟨n, hn, rfl⟩ := hy'
  exact ⟨n, hn, rfl⟩

theorem map_mem_centralizer {T : Subgroup M} {n : M} (hn : n ∈ Subgroup.centralizer (T : Set M)) :
    QuotientGroup.mk' O n ∈
      Subgroup.centralizer ((T.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨t, ht, rfl⟩
  have h := Subgroup.mem_centralizer_iff.1 hn t ht
  rw [← map_mul, ← map_mul, h]

theorem pow_mem_centralizer_iff {T : Subgroup M} (hT : IsPGroup p ↥T) (hO : ¬ p ∣ Nat.card O)
    {n : M} (hn : n ∈ Subgroup.normalizer (T : Set M)) (k : ℕ) :
    n ^ k ∈ Subgroup.centralizer (T : Set M) ↔
      (QuotientGroup.mk' O n) ^ k ∈
        Subgroup.centralizer ((T.map (QuotientGroup.mk' O) : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
  constructor
  · intro h
    rw [← map_pow]
    exact map_mem_centralizer h
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hnk : n ^ k ∈ Subgroup.normalizer (T : Set M) := Subgroup.pow_mem _ hn k
    have ha : n ^ k * t * (n ^ k)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hnk t).1 ht
    have h1 := Subgroup.mem_centralizer_iff.1 h (QuotientGroup.mk' O t) ⟨t, ht, rfl⟩
    have hπ : QuotientGroup.mk' O (n ^ k * t * (n ^ k)⁻¹) = QuotientGroup.mk' O t := by
      simp only [map_mul, map_inv, map_pow] at h1 ⊢
      rw [← h1]
      group
    have h2 := eq_of_mk'_eq hT hO ha ht hπ
    calc t * n ^ k = (n ^ k * t * (n ^ k)⁻¹) * n ^ k := by rw [h2]
      _ = n ^ k * t := by group

end Img

end Sec1511

end CFSG.RankThree.PartOne
