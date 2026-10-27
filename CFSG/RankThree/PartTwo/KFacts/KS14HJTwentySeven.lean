module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

section TwentySeven

variable {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem exists_zpow_mul_of_mem_sup (hzC : z ∈ Subgroup.centralizer (L : Set Y)) {x : Y}
    (hx : x ∈ Subgroup.zpowers z ⊔ L) : ∃ k : ℤ, ∃ ℓ ∈ L, x = z ^ k * ℓ := by
  have hcomm : ∀ ℓ ∈ L, ∀ k : ℤ, ℓ * z ^ k = z ^ k * ℓ := fun ℓ hℓ k =>
    ((Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hzC ℓ hℓ) k)).eq
  let S : Subgroup Y :=
    { carrier := {x | ∃ k : ℤ, ∃ ℓ ∈ L, x = z ^ k * ℓ}
      one_mem' := ⟨0, 1, one_mem L, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, ℓ, hℓ, rfl⟩ ⟨m, ℓ', hℓ', rfl⟩
        refine ⟨k + m, ℓ * ℓ', mul_mem hℓ hℓ', ?_⟩
        rw [zpow_add, mul_assoc, ← mul_assoc ℓ, hcomm ℓ hℓ m]
        group
      inv_mem' := by
        rintro _ ⟨k, ℓ, hℓ, rfl⟩
        refine ⟨-k, ℓ⁻¹, inv_mem hℓ, ?_⟩
        rw [mul_inv_rev]
        simpa [zpow_neg] using hcomm ℓ⁻¹ (inv_mem hℓ) (-k) }
  have hle : Subgroup.zpowers z ⊔ L ≤ S := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨1, 1, one_mem L, by simp⟩) fun ℓ hℓ => ?_
    exact ⟨0, ℓ, hℓ, by simp⟩
  exact hle hx

theorem zpow_eq_one_of_mem (hzL : z ∉ L) (hz3 : z ^ 3 = 1) {k : ℤ} (hk : z ^ k ∈ L) :
    z ^ k = 1 := by
  have hk' : z ^ (k % 3) = z ^ k := by
    conv_rhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hz3,
      one_zpow, one_mul]
  rw [← hk'] at hk ⊢
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hk
    exact absurd hk hzL
  · exfalso
    apply hzL
    rw [h] at hk
    have : z = (z ^ (2 : ℤ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_one_add, show (1 : ℤ) + 2 = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast, hz3]
    rw [this]
    exact inv_mem hk

theorem eq_sup_inf_of_mem (hzC : z ∈ Subgroup.centralizer (L : Set Y)) {E : Subgroup Y}
    (hE : E ≤ Subgroup.zpowers z ⊔ L) (hzE : z ∈ E) : E = Subgroup.zpowers z ⊔ (E ⊓ L) := by
  refine le_antisymm (fun e he => ?_) (sup_le (Subgroup.zpowers_le.mpr hzE) inf_le_left)
  obtain ⟨k, ℓ, hℓ, rfl⟩ := exists_zpow_mul_of_mem_sup hzC (hE he)
  have hℓE : ℓ ∈ E := by
    have : ℓ = (z ^ k)⁻¹ * (z ^ k * ℓ) := by group
    rw [this]
    exact mul_mem (inv_mem (zpow_mem hzE k)) he
  exact mul_mem (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers z) k))
    (Subgroup.mem_sup_right ⟨hℓE, hℓ⟩)

theorem card_eq_three_mul_card_inf [Finite Y] (hzC : z ∈ Subgroup.centralizer (L : Set Y))
    (hzL : z ∉ L) (hz3 : z ^ 3 = 1) {E : Subgroup Y} (hE : E ≤ Subgroup.zpowers z ⊔ L)
    (hzE : z ∈ E) : Nat.card E = 3 * Nat.card ↥(E ⊓ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem L)
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  let f : ↥(Subgroup.zpowers z) × ↥(E ⊓ L) → ↥E := fun p =>
    ⟨(p.1 : Y) * p.2, mul_mem (Subgroup.zpowers_le.mpr hzE p.1.2) p.2.2.1⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h' : a * b = a' * b' := congrArg Subtype.val h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have hmem : z ^ (k - k') ∈ L := by
      have : z ^ (k - k') = b' * b⁻¹ := by
        rw [zpow_sub]
        calc z ^ k * (z ^ k')⁻¹ = (z ^ k')⁻¹ * (z ^ k * b) * b⁻¹ := by
              rw [show (z ^ k')⁻¹ * (z ^ k * b) * b⁻¹ = (z ^ k')⁻¹ * z ^ k by group]
              exact (Commute.zpow_zpow_self z k k').inv_right.eq
          _ = (z ^ k')⁻¹ * (z ^ k' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      rw [this]
      exact mul_mem hb'.2 (inv_mem hb.2)
    have h1 := zpow_eq_one_of_mem hzL hz3 hmem
    have hkk : z ^ k = z ^ k' := by
      rw [zpow_sub, mul_inv_eq_one] at h1
      exact h1
    have hbb : b = b' := by
      rw [hkk] at h'
      exact mul_left_cancel h'
    subst hbb
    simp only [hkk]
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨k, ℓ, hℓ, rfl⟩ := exists_zpow_mul_of_mem_sup hzC (hE he)
    have hℓE : ℓ ∈ E := by
      have : ℓ = (z ^ k)⁻¹ * (z ^ k * ℓ) := by group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem hzE k)) he
    exact ⟨(⟨z ^ k, Subgroup.zpow_mem_zpowers z k⟩, ⟨ℓ, hℓE, hℓ⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_zpowers,
    hord]

end TwentySeven

section HJ

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem conjugate_eq_of_conjugate_inf {L : Subgroup Y} {z : Y}
    (hzC : z ∈ Subgroup.centralizer (L : Set Y)) {E E' : Subgroup Y}
    (hE : E ≤ Subgroup.zpowers z ⊔ L) (hE' : E' ≤ Subgroup.zpowers z ⊔ L) (hzE : z ∈ E)
    (hzE' : z ∈ E') {g : Y} (hgL : g ∈ L) (h : conjugate (E ⊓ L) g = E' ⊓ L) :
    E' = conjugate E g := by
  have hzg : conjugate (Subgroup.zpowers z) g = Subgroup.zpowers z := by
    rw [conjugate, MonoidHom.map_zpowers]
    congr 1
    have hc : g * z = z * g := Subgroup.mem_centralizer_iff.mp hzC g hgL
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * z * g = g⁻¹ * (g * z) := by rw [hc, mul_assoc]
      _ = z := by group
  rw [eq_sup_inf_of_mem hzC hE' hzE', eq_sup_inf_of_mem hzC hE hzE, conjugate,
    Subgroup.map_sup, ← conjugate, ← conjugate, hzg]
  congr 1
  exact h.symm

omit [Finite Y] in
theorem conjugate_map_subtype {L : Subgroup Y} (H : Subgroup L) (g : L) :
    conjugate (H.map L.subtype) (g : Y) = (conjugate H g).map L.subtype := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem j2_exists_conjugate_of_card_twentySeven (h415 : Sec4.Item4_15) {L : Subgroup Y}
    (hL : Nonempty (↥L ≃* NativeSporadic.J2)) {z : Y}
    (hzC : z ∈ Subgroup.centralizer (L : Set Y)) (hzL : z ∉ L) (hz3 : z ^ 3 = 1)
    {E E' : Subgroup Y} (hE : E ≤ Subgroup.zpowers z ⊔ L) (hE' : E' ≤ Subgroup.zpowers z ⊔ L)
    (hzE : z ∈ E) (hzE' : z ∈ E') (h27 : Nat.card E = 27) (h27' : Nat.card E' = 27) :
    ∃ g ∈ L, E' = conjugate E g := by
  have h9 : Nat.card ↥(E ⊓ L) = 9 := by
    have := card_eq_three_mul_card_inf hzC hzL hz3 hE hzE
    omega
  have h9' : Nat.card ↥(E' ⊓ L) = 9 := by
    have := card_eq_three_mul_card_inf hzC hzL hz3 hE' hzE'
    omega
  set F := (E ⊓ L).subgroupOf L with hF
  set F' := (E' ⊓ L).subgroupOf L with hF'
  have hFc : Nat.card F = 9 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hFc' : Nat.card F' = 9 := by
    rw [hF', Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9']
  obtain ⟨g, hg⟩ := j2_exists_conjugate_of_card_nine h415 hL hFc hFc'
  have hFmap : F.map L.subtype = E ⊓ L := by
    rw [hF, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hFmap' : F'.map L.subtype = E' ⊓ L := by
    rw [hF', Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hconjL : conjugate (E ⊓ L) (g : Y) = E' ⊓ L := by
    rw [← hFmap, conjugate_map_subtype, ← hg, hFmap']
  exact ⟨g, g.2, conjugate_eq_of_conjugate_inf hzC hE hE' hzE hzE' g.2 hconjL⟩

theorem j2_prod_exists_conjugate_of_card_twentySeven (h415 : Sec4.Item4_15) {X : Type}
    [Group X] [Finite X] (hX : Nonempty (X ≃* NativeSporadic.J2))
    {E E' : Subgroup (Multiplicative (ZMod 3) × X)}
    (hE : (⊤ : Subgroup (Multiplicative (ZMod 3))).prod (⊥ : Subgroup X) ≤ E)
    (hE' : (⊤ : Subgroup (Multiplicative (ZMod 3))).prod (⊥ : Subgroup X) ≤ E')
    (h27 : Nat.card E = 27) (h27' : Nat.card E' = 27) :
    ∃ x : X, E' = conjugate E (1, x) := by
  set L := (MonoidHom.inr (Multiplicative (ZMod 3)) X).range with hLdef
  have hL : Nonempty (↥L ≃* NativeSporadic.J2) := by
    obtain ⟨e⟩ := hX
    have hinj : Function.Injective (MonoidHom.inr (Multiplicative (ZMod 3)) X) :=
      fun a b h => congrArg Prod.snd h
    exact ⟨(MonoidHom.ofInjective hinj).symm.trans e⟩
  set z : Multiplicative (ZMod 3) × X := (Multiplicative.ofAdd 1, 1) with hzdef
  have hzC : z ∈ Subgroup.centralizer (L : Set (Multiplicative (ZMod 3) × X)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    ext <;> simp [hzdef, mul_comm]
  have hzL : z ∉ L := by
    rintro ⟨x, hx⟩
    have h1 := congrArg Prod.fst hx
    simp only [MonoidHom.inr_apply, hzdef] at h1
    exact absurd h1 (by decide)
  have hz3 : z ^ 3 = 1 := by
    ext
    · change Multiplicative.ofAdd (1 : ZMod 3) ^ 3 = 1
      decide
    · simp [hzdef]
  have hsup : ∀ p, p ∈ Subgroup.zpowers z ⊔ L := by
    rintro ⟨a, x⟩
    have hp : ((a, x) : Multiplicative (ZMod 3) × X) =
        z ^ (Multiplicative.toAdd a).val * (1, x) := by
      ext
      · change a = (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd a).val * 1
        rw [mul_one, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
        rfl
      · simp [hzdef]
    rw [hp]
    exact Subgroup.mul_mem_sup (Subgroup.npow_mem_zpowers z _) ⟨x, rfl⟩
  have hzE : z ∈ E := hE ⟨Subgroup.mem_top _, by simp [hzdef]⟩
  have hzE' : z ∈ E' := hE' ⟨Subgroup.mem_top _, by simp [hzdef]⟩
  obtain ⟨g, ⟨x, rfl⟩, hg⟩ := j2_exists_conjugate_of_card_twentySeven h415 hL hzC hzL hz3
    (fun p _ => hsup p) (fun p _ => hsup p) hzE hzE' h27 h27'
  exact ⟨x, hg⟩

end HJ

section Theta

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conjugate {G' : Type*} [Group G'] (φ : G →* G') (H : Subgroup G) (g : G) :
    (conjugate H g).map φ = conjugate (H.map φ) (φ g) := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem exists_conjugate_of_map_conjugate {p : ℕ} [hp : Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P P' : Subgroup G} (hP : IsPGroup p P)
    (hcard : Nat.card P' = Nat.card P) {g : G}
    (hg : P'.map (QuotientGroup.mk' N) =
      conjugate (P.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N g)) :
    ∃ x : G, P' = conjugate P x := by
  set Q := conjugate P g with hQdef
  have hQ : IsPGroup p Q := hP.map _
  have hQc : Nat.card Q = Nat.card P := by
    rw [hQdef, conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hle : P' ≤ Q ⊔ N := by
    intro y hy
    have hy' : QuotientGroup.mk' N y ∈ Q.map (QuotientGroup.mk' N) := by
      rw [hQdef, map_conjugate, ← hg]
      exact ⟨y, hy, rfl⟩
    obtain ⟨q, hq, hqy⟩ := hy'
    have hn : q⁻¹ * y ∈ N := by
      rw [← QuotientGroup.eq]
      exact hqy
    have : y = q * (q⁻¹ * y) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hn)
  set M := Q ⊔ N with hMdef
  have hdisj : N ⊓ Q = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have h1 : Nat.card ↥(N ⊓ Q) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk⟩ := (hQ.to_le (inf_le_right : N ⊓ Q ≤ Q)).exists_card_eq
    rcases k with _ | k
    · simpa using hk
    · exfalso
      apply hN
      rw [hk] at h1
      exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans h1
  have hM : Nat.card M = Nat.card Q * Nat.card N := by
    have h1 := Subgroup.relIndex_mul_card N M
    have h2 : N.relIndex M = N.relIndex Q := Subgroup.relIndex_sup_right Q N
    have h3 := Subgroup.relIndex_mul_card N Q
    rw [hdisj, Subgroup.card_bot, mul_one] at h3
    rw [inf_of_le_left le_sup_right, h2, h3] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hfac : (Nat.card M).factorization p = k := by
    rw [hM, hk, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) Nat.card_pos.ne',
      Nat.Prime.factorization_pow hp.out, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hN, add_zero]
  have hQM : Nat.card (Q.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hk, hfac]
  have hP'M : Nat.card (P'.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard, ← hQc, hk, hfac]
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) (Sylow.ofCard _ hQM) (Sylow.ofCard _ hP'M)
  have hm' : P'.subgroupOf M = (Q.subgroupOf M).map (MulAut.conj m).toMonoidHom := by
    have := congrArg (fun S : Sylow p M => (S : Subgroup M)) hm
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at this
    rw [← this, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g * (m : G)⁻¹, ?_⟩
  have hP'eq : P' = (P'.subgroupOf M).map M.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  rw [hP'eq, hm', Subgroup.map_map, ← conjugate_conjugate_eq_mul, ← hQdef]
  have hQeq : Q = (Q.subgroupOf M).map M.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left le_sup_left]
  conv_rhs => rw [hQeq, conjugate, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

end Theta

section HJTheta

variable {Y : Type} [Group Y] [Finite Y]

theorem j2_exists_conjugate_of_card_twentySeven_of_quot (h415 : Sec4.Item4_15)
    {L : Subgroup Y} {N : Subgroup L} [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N)
    (hL : Nonempty (↥L ⧸ N ≃* NativeSporadic.J2)) {z : Y}
    (hzC : z ∈ Subgroup.centralizer (L : Set Y)) (hzL : z ∉ L) (hz3 : z ^ 3 = 1)
    {E E' : Subgroup Y} (hE : E ≤ Subgroup.zpowers z ⊔ L) (hE' : E' ≤ Subgroup.zpowers z ⊔ L)
    (hzE : z ∈ E) (hzE' : z ∈ E') (h27 : Nat.card E = 27) (h27' : Nat.card E' = 27) :
    ∃ g ∈ L, E' = conjugate E g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card ↥(E ⊓ L) = 9 := by
    have := card_eq_three_mul_card_inf hzC hzL hz3 hE hzE
    omega
  have h9' : Nat.card ↥(E' ⊓ L) = 9 := by
    have := card_eq_three_mul_card_inf hzC hzL hz3 hE' hzE'
    omega
  set F := (E ⊓ L).subgroupOf L with hF
  set F' := (E' ⊓ L).subgroupOf L with hF'
  have hFc : Nat.card F = 9 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hFc' : Nat.card F' = 9 := by
    rw [hF', Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9']
  have hFp : IsPGroup 3 F := IsPGroup.of_card (n := 2) (by rw [hFc]; norm_num)
  have hFp' : IsPGroup 3 F' := IsPGroup.of_card (n := 2) (by rw [hFc']; norm_num)
  have hcard_map : ∀ H : Subgroup L, IsPGroup 3 H →
      Nat.card (H.map (QuotientGroup.mk' N)) = Nat.card H := by
    intro H hH
    have hdisj : N ⊓ H = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have h1 : Nat.card ↥(N ⊓ H) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨k, hk⟩ := (hH.to_le (inf_le_right : N ⊓ H ≤ H)).exists_card_eq
      rcases k with _ | k
      · simpa using hk
      · exfalso
        apply hN3
        rw [hk] at h1
        exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans h1
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp H.subtype) := by
      intro a b hab
      have h1 : (a : L)⁻¹ * b ∈ N := by
        rw [← QuotientGroup.eq]
        exact hab
      have h2 : (a : L)⁻¹ * b ∈ N ⊓ H := Subgroup.mem_inf.mpr ⟨h1, mul_mem (inv_mem a.2) b.2⟩
      rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h2
      exact Subtype.ext h2
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hFq : Nat.card (F.map (QuotientGroup.mk' N)) = 9 := by rw [hcard_map F hFp, hFc]
  have hFq' : Nat.card (F'.map (QuotientGroup.mk' N)) = 9 := by rw [hcard_map F' hFp', hFc']
  obtain ⟨gq, hgq⟩ := j2_exists_conjugate_of_card_nine h415 hL hFq hFq'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gq
  obtain ⟨x, hx⟩ := exists_conjugate_of_map_conjugate hN3 hFp (by rw [hFc, hFc']) hgq
  have hFmap : F.map L.subtype = E ⊓ L := by
    rw [hF, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hFmap' : F'.map L.subtype = E' ⊓ L := by
    rw [hF', Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hconjL : conjugate (E ⊓ L) (x : Y) = E' ⊓ L := by
    rw [← hFmap, conjugate_map_subtype, ← hx, hFmap']
  exact ⟨x, x.2, conjugate_eq_of_conjugate_inf hzC hE hE' hzE hzE' x.2 hconjL⟩

end HJTheta

end CFSG.RankThree.PartTwo.KFacts.KS14
