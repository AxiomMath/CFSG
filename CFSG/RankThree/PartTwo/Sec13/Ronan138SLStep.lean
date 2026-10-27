module

public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec13.Item136Lift

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem r138_comm_of_conj_eq {M : Type*} [Group M] {y c : M}
    (h : y * c * y⁻¹ = c) : y * c = c * y := by
  calc y * c = y * c * y⁻¹ * y := by group
    _ = c * y := by rw [h]

private theorem r138_mem_normalizer_of_commute {M : Type*} [Group M] {H : Subgroup M} {y : M}
    (hy : ∀ h ∈ H, y * h = h * y) : y ∈ Subgroup.normalizer (H : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : y * h * y⁻¹ = h := by rw [hy h hh, mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hc
    have h4 : y * (y * h * y⁻¹) = y * h := by
      rw [hy _ hc]
      group
    have h5 : y * h * y⁻¹ = h := mul_left_cancel h4
    rw [← h5]
    exact hc

private theorem r138_comm_of_sup {M : Type*} [Group M] {H K : Subgroup M}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {x y : M} (hx : x ∈ H ⊔ K) (hy : y ∈ H ⊔ K) :
    x * y = y * x := by
  have hC : H ⊔ K ≤ Subgroup.centralizer ((H : Set M) ∪ (K : Set M)) := by
    refine sup_le (fun h hh => ?_) (fun k hk => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro s (hs | hs)
      · exact (hH h hh s hs).symm
      · exact (hHK h hh s hs).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro s (hs | hs)
      · exact hHK s hs k hk
      · exact hK s hs k hk
  have hC' : H ⊔ K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup M) : Set M) := by
    refine sup_le (fun h hh => ?_) (fun k hk => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hC hz) h (Or.inl hh)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hC hz) k (Or.inr hk)).symm
  exact (Subgroup.mem_centralizer_iff.mp (hC' hx) y hy).symm

private theorem r138_inv_mul_mem_thetaQuotCentralizer {L : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) (x : L)
    (h : ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨g, hgN⟩ =
      MulAut.conj (x : L ⧸ aschbacherSolvableCore 3 L)) :
    (x : G)⁻¹ * g ∈ Sec4.thetaQuotCentralizer L := by
  have hxN : (x : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer x.2
  have hN : (x : G)⁻¹ * g ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hxN) hgN
  have hx : ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨(x : G), hxN⟩ =
      MulAut.conj (x : L ⧸ aschbacherSolvableCore 3 L) :=
    CFSG.RankThree.PartTwo.Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem x
  refine Subgroup.mem_map.mpr ⟨⟨(x : G)⁻¹ * g, hN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
  rw [show (⟨(x : G)⁻¹ * g, hN⟩ : Subgroup.normalizer (L : Set G)) =
      (⟨(x : G), hxN⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨g, hgN⟩ from rfl,
    map_mul, map_inv, hx, h, inv_mul_cancel]

theorem exists_mem_inv_mul_mem_of_commute {L B : Subgroup G} (hBL : B ≤ L) (hB : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinn : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∃ y : L ⧸ aschbacherSolvableCore 3 L, σ = MulAut.conj y)
    (hab9 : ∀ X : Subgroup (L ⧸ aschbacherSolvableCore 3 L), IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → Nat.card X ≤ 9)
    {r : G} (hrN : r ∈ Subgroup.normalizer (L : Set G)) (hrB : ∀ b ∈ B, r * b = b * r)
    (hr3 : ∃ k : ℕ, r ^ 3 ^ k = 1) :
    ∃ β ∈ B, β⁻¹ * r ∈ Sec4.thetaQuotCentralizer L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hr3
  obtain ⟨σ, hσdef⟩ : ∃ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L),
      σ = ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨r, hrN⟩ := ⟨_, rfl⟩
  have hσk : σ ^ 3 ^ k = 1 := by
    rw [hσdef, ← map_pow,
      show (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 from Subtype.ext hk, map_one]
  have hσmk : ∀ l : L, σ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) (L.normalizerMonoidHom ⟨r, hrN⟩ l) := by
    intro l
    subst hσdef
    rfl
  obtain ⟨yb, hy⟩ := hinn σ ⟨k, hσk⟩
  have hyk : yb ^ 3 ^ k = 1 := by
    apply KFacts.KS14.conj_injective_of_center_eq_bot hZ
    rw [map_pow, map_one, ← hy, hσk]
  have hz3 : IsPGroup 3 (Subgroup.zpowers yb) :=
    IsPGroup.of_card_dvd_pow (n := k)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hyk)
  have hfix : ∀ b : L, (b : G) ∈ B →
      σ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) b) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) b := by
    intro b hb
    have hb' : L.normalizerMonoidHom ⟨r, hrN⟩ b = b := by
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe hrN b, hrB _ hb, mul_inv_cancel_right]
    rw [hσmk, hb']
  have hB' : IsPGroup 3 (B.subgroupOf L) := hB.comap_subtype
  obtain ⟨Bbar, hBbar⟩ : ∃ X : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      X = (B.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := ⟨_, rfl⟩
  have hinjB : Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
      ((B.subgroupOf L : Subgroup L) : Set L) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hB'
  have hBbar_card : Nat.card Bbar = 9 := by
    rw [hBbar, CFSG.RankThree.PartTwo.Sec13.card_map_eq_of_injOn _ hinjB,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB9]
  have hBbar3 : IsPGroup 3 Bbar := by
    rw [hBbar]
    exact hB'.map _
  have hBbarc : ∀ x ∈ Bbar, ∀ y ∈ Bbar, x * y = y * x := by
    intro x hx y hy'
    rw [hBbar, Subgroup.mem_map] at hx hy'
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
  have hcommy : ∀ h ∈ Bbar, yb * h = h * yb := by
    intro h hh
    rw [hBbar, Subgroup.mem_map] at hh
    obtain ⟨b, hb, rfl⟩ := hh
    have h1 := hfix b (Subgroup.mem_subgroupOf.mp hb)
    rw [hy, MulAut.conj_apply] at h1
    exact r138_comm_of_conj_eq h1
  have hyN : yb ∈ Subgroup.normalizer (Bbar : Set (L ⧸ aschbacherSolvableCore 3 L)) :=
    r138_mem_normalizer_of_commute hcommy
  have hzcomm : ∀ x ∈ Subgroup.zpowers yb, ∀ y ∈ Subgroup.zpowers yb, x * y = y * x := by
    intro x hx y hy'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact ((Commute.refl yb).zpow_right n).zpow_left m
  have hBz : ∀ x ∈ Bbar, ∀ y ∈ Subgroup.zpowers yb, x * y = y * x := by
    intro x hx y hy'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact (show Commute x yb from (hcommy x hx).symm).zpow_right n
  have hX3 : IsPGroup 3 (Bbar ⊔ Subgroup.zpowers yb : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :=
    IsPGroup.to_sup_of_normal_left' hBbar3 hz3 (Subgroup.zpowers_le.mpr hyN)
  have hXc : ∀ x ∈ Bbar ⊔ Subgroup.zpowers yb, ∀ y ∈ Bbar ⊔ Subgroup.zpowers yb,
      x * y = y * x :=
    fun x hx y hy' => r138_comm_of_sup hBbarc hzcomm hBz hx hy'
  have hXle : Nat.card (Bbar ⊔ Subgroup.zpowers yb : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) ≤
      9 := hab9 _ hX3 hXc
  have hBX : Bbar = Bbar ⊔ Subgroup.zpowers yb :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hBbar_card]; exact hXle)
  have hyBbar : yb ∈ Bbar := by
    rw [hBX]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers yb)
  rw [hBbar, Subgroup.mem_map] at hyBbar
  obtain ⟨x, hx, hxy⟩ := hyBbar
  rw [QuotientGroup.mk'_apply] at hxy
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hx,
    r138_inv_mul_mem_thetaQuotCentralizer hrN x ?_⟩
  rw [← hσdef, hy, ← hxy]

theorem exists_mem_inv_mul_mem_of_normalizes {L Q : Subgroup G} (hQL : Q ≤ L)
    (hQ : IsPGroup 3 Q) (hQsyl : Nat.card Q = 3 ^ (Nat.card L).factorization 3)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hinn : ∀ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∃ y : L ⧸ aschbacherSolvableCore 3 L, σ = MulAut.conj y)
    {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G)) (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1) :
    ∃ y ∈ Q, y⁻¹ * g ∈ Sec4.thetaQuotCentralizer L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hg3
  obtain ⟨σ, hσdef⟩ : ∃ σ : MulAut (L ⧸ aschbacherSolvableCore 3 L),
      σ = ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom) ⟨g, hgN⟩ := ⟨_, rfl⟩
  have hσk : σ ^ 3 ^ k = 1 := by
    rw [hσdef, ← map_pow,
      show (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 from Subtype.ext hk, map_one]
  have hσmk : ∀ l : L, σ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) (L.normalizerMonoidHom ⟨g, hgN⟩ l) := by
    intro l
    subst hσdef
    rfl
  obtain ⟨yb, hy⟩ := hinn σ ⟨k, hσk⟩
  have hyk : yb ^ 3 ^ k = 1 := by
    apply KFacts.KS14.conj_injective_of_center_eq_bot hZ
    rw [map_pow, map_one, ← hy, hσk]
  have hz3 : IsPGroup 3 (Subgroup.zpowers yb) :=
    IsPGroup.of_card_dvd_pow (n := k)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hyk)
  have hQ' : IsPGroup 3 (Q.subgroupOf L) := hQ.comap_subtype
  obtain ⟨Qbar, hQbar⟩ : ∃ X : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      X = (Q.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := ⟨_, rfl⟩
  have hinjQ : Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
      ((Q.subgroupOf L : Subgroup L) : Set L) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hQ'
  have hQbar_card : Nat.card Qbar = Nat.card Q := by
    rw [hQbar, CFSG.RankThree.PartTwo.Sec13.card_map_eq_of_injOn _ hinjQ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv]
  have hQbar3 : IsPGroup 3 Qbar := by
    rw [hQbar]
    exact hQ'.map _
  have hσmap : Qbar.map (σ : (L ⧸ aschbacherSolvableCore 3 L) →* (L ⧸ aschbacherSolvableCore 3 L))
      ≤ Qbar := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ (Q.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
      rw [← hQbar]
      exact hw
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hw'
    have hmem : L.normalizerMonoidHom ⟨g, hgN⟩ l ∈ Q.subgroupOf L := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [Sec4.normalizerMonoidHom_apply_coe hgN l]
      exact (Subgroup.mem_normalizer_iff.mp hgQ _).mp (Subgroup.mem_subgroupOf.mp hl)
    rw [hQbar]
    exact Subgroup.mem_map.mpr ⟨_, hmem, (hσmk l).symm⟩
  have hσinj : Function.Injective
      (σ : (L ⧸ aschbacherSolvableCore 3 L) →* (L ⧸ aschbacherSolvableCore 3 L)) :=
    σ.injective
  have hσeq : Qbar.map
      (σ : (L ⧸ aschbacherSolvableCore 3 L) →* (L ⧸ aschbacherSolvableCore 3 L)) = Qbar :=
    Subgroup.eq_of_le_of_card_ge hσmap (Subgroup.card_map_of_injective hσinj).ge
  have hyN : yb ∈ Subgroup.normalizer (Qbar : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hy] at hσeq
    exact hσeq
  have hX3 : IsPGroup 3 (Qbar ⊔ Subgroup.zpowers yb : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :=
    IsPGroup.to_sup_of_normal_left' hQbar3 hz3 (Subgroup.zpowers_le.mpr hyN)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX3
  have hdvd : Nat.card (Qbar ⊔ Subgroup.zpowers yb : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) ∣
      Nat.card L :=
    (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
  have hL0 : Nat.card L ≠ 0 := (Nat.card_pos).ne'
  have hn3 : n ≤ (Nat.card L).factorization 3 := by
    rw [hn] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0).mp hdvd
  have hXle : Nat.card (Qbar ⊔ Subgroup.zpowers yb : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) ≤
      Nat.card Qbar := by
    rw [hn, hQbar_card, hQsyl]
    exact Nat.pow_le_pow_right (by norm_num) hn3
  have hQX : Qbar = Qbar ⊔ Subgroup.zpowers yb :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hXle
  have hyQ : yb ∈ Qbar := by
    rw [hQX]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers yb)
  rw [hQbar, Subgroup.mem_map] at hyQ
  obtain ⟨x, hx, hxy⟩ := hyQ
  rw [QuotientGroup.mk'_apply] at hxy
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hx,
    r138_inv_mul_mem_thetaQuotCentralizer hgN x ?_⟩
  rw [← hσdef, hy, ← hxy]

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
