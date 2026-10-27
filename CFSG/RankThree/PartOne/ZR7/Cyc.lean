module

public import CFSG.RankThree.PartOne.K1214.OmegaAlg

public section

namespace CFSG.RankThree.PartOne.ZR7

open CFSG.RankThree.PartOne.K1214

variable {G : Type} [Group G]

theorem centralizer_le_of_not_centralize [Finite G] {p : ℕ} (hp : p.Prime) {P Q : Subgroup G}
    (hP : IsPGroup p ↥P) (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) {f c : G} (hfP : f ∈ P)
    (hPf : P = Q ⊔ Subgroup.zpowers f) (hcP : c ∈ P) (hcQ : c ∉ Q) (hcp : c ^ p = 1)
    {S : Set G} (hQS : ∀ q ∈ Q, ∀ s ∈ S, q * s = s * q) (hcS : ∃ s ∈ S, c * s ≠ s * c) :
    ∀ g ∈ P, (∀ s ∈ S, g * s = s * g) → g ∈ Q := by
  intro g hg hgS
  by_contra hgQ
  obtain ⟨k, q, hq, hc⟩ := exists_pow_mul_of_not_mem hp hP hQP hQn hfP hPf hcP hcQ hcp hg hgQ
  obtain ⟨s, hs, hne⟩ := hcS
  apply hne
  have h1 : g ^ k * s = s * g ^ k := (Commute.pow_left (show Commute g s from hgS s hs) k).eq
  rw [hc, mul_assoc, hQS q hq s hs, ← mul_assoc, h1, mul_assoc]

theorem mem_zpowers_of_cyclic {p : ℕ} (hp : p.Prime) {R : Type*} [Group R] [IsCyclic R]
    [Finite R] {u v : R} (hu : u ^ p = 1) (hv : v ^ p = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u ∈ Subgroup.zpowers v := by
  have : Fact p.Prime := ⟨hp⟩
  have hou : orderOf u = p := orderOf_eq_prime hu hu1
  have hov : orderOf v = p := orderOf_eq_prime hv hv1
  have hle : Subgroup.zpowers u ≤ Subgroup.zpowers v := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hou, hov]
  exact hle (Subgroup.mem_zpowers u)

theorem mem_zpowers_of_isCyclic_subgroup [Finite G] {p : ℕ} (hp : p.Prime) {R : Subgroup G}
    [IsCyclic ↥R] {u v : G} (hu : u ∈ R) (hv : v ∈ R) (hup : u ^ p = 1) (hvp : v ^ p = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u ∈ Subgroup.zpowers v := by
  have h := mem_zpowers_of_cyclic hp (R := ↥R) (u := ⟨u, hu⟩) (v := ⟨v, hv⟩)
    (Subtype.ext (by simpa using hup)) (Subtype.ext (by simpa using hvp))
    (fun h => hu1 (congrArg Subtype.val h)) (fun h => hv1 (congrArg Subtype.val h))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem inf_eq_bot_of_cyclic [Finite G] {p : ℕ} (hp : p.Prime) {R R' : Subgroup G} [IsCyclic ↥R]
    [IsCyclic ↥R'] (hR : IsPGroup p ↥R) {u u' : G} (hu : u ∈ R) (hu' : u' ∈ R')
    (hup : u ^ p = 1) (hup' : u' ^ p = 1) (hu1 : u ≠ 1) (hu1' : u' ≠ 1)
    (hne : u' ∉ Subgroup.zpowers u) : R ⊓ R' = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hgR : g ∈ R := hg.1
  have hgR' : g ∈ R' := hg.2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨g, hgR⟩
  have hk' : orderOf g = p ^ k := (Subgroup.orderOf_coe (⟨g, hgR⟩ : ↥R)).trans hk
  have hk1 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
    exact hg1 hk'
  have hog' : orderOf (g ^ (p ^ (k - 1))) = p := by
    have hdvd : p ^ (k - 1) ∣ orderOf g := by
      rw [hk']
      exact pow_dvd_pow p (Nat.sub_le k 1)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hk']
    have : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk1)]
    rw [this, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hg'p : (g ^ (p ^ (k - 1))) ^ p = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hog']
  have hg'1 : g ^ (p ^ (k - 1)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hog'
    exact hp.one_lt.ne hog'
  have h1 : g ^ (p ^ (k - 1)) ∈ Subgroup.zpowers u :=
    mem_zpowers_of_isCyclic_subgroup hp (R := R) (R.pow_mem hgR _) hu hg'p hup hg'1 hu1
  have h2 : u' ∈ Subgroup.zpowers (g ^ (p ^ (k - 1))) :=
    mem_zpowers_of_isCyclic_subgroup hp (R := R') hu' (R'.pow_mem hgR' _) hup' hg'p hu1' hg'1
  exact hne ((Subgroup.zpowers_le.2 h1) h2)

@[expose] def conjSub (n : G) (S : Subgroup G) : Subgroup G := S.map (MulAut.conj n).toMonoidHom

theorem mem_conjSub {n : G} {S : Subgroup G} {y : G} :
    y ∈ conjSub n S ↔ ∃ x ∈ S, y = n * x * n⁻¹ := by
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩

theorem card_conjSub (n : G) (S : Subgroup G) : Nat.card (conjSub n S) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj n).injective

theorem isCyclic_conjSub (n : G) (S : Subgroup G) [IsCyclic ↥S] : IsCyclic ↥(conjSub n S) := by
  have e := Subgroup.equivMapOfInjective S (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem conjSub_le {P S : Subgroup G} {n : G} (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hSP : S ≤ P) : conjSub n S ≤ P := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_conjSub.1 hy
  exact (Subgroup.mem_normalizer_iff.1 hnP x).1 (hSP hx)

theorem conjSub_normal {P S : Subgroup G} {n : G} (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hSn : ∀ g ∈ P, ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    ∀ g ∈ P, ∀ y ∈ conjSub n S, g * y * g⁻¹ ∈ conjSub n S := by
  intro g hg y hy
  obtain ⟨x, hx, rfl⟩ := mem_conjSub.1 hy
  have hg' : n⁻¹ * g * n ∈ P := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnP) g).1 hg
    simpa using this
  refine mem_conjSub.2 ⟨(n⁻¹ * g * n) * x * (n⁻¹ * g * n)⁻¹, hSn _ hg' x hx, ?_⟩
  group

theorem conj_le_of_swap [Finite G] {p : ℕ} (hp : p.Prime) {P Q S : Subgroup G}
    (hPp : IsPGroup p ↥P) (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) {f c n u : G}
    (hfP : f ∈ P) (hPf : P = Q ⊔ Subgroup.zpowers f) (hcP : c ∈ P) (hcQ : c ∉ Q)
    (hcp : c ^ p = 1) (hSP : S ≤ P) (hSn : ∀ g ∈ P, ∀ x ∈ S, g * x * g⁻¹ ∈ S) [IsCyclic ↥S]
    (hQS : ∀ q ∈ Q, ∀ s ∈ S, q * s = s * q) (hcS : ∃ s ∈ S, c * s ≠ s * c)
    (huS : u ∈ S) (hup : u ^ p = 1) (hu1 : u ≠ 1) (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hnu : n * u * n⁻¹ ∉ Subgroup.zpowers u) :
    conjSub n S ≤ Q ∧ S ⊓ conjSub n S = ⊥ := by
  classical
  have hCS : ∀ g ∈ P, (∀ s ∈ (S : Set G), g * s = s * g) → g ∈ Q :=
    centralizer_le_of_not_centralize hp hPp hQP hQn hfP hPf hcP hcQ hcp hQS hcS
  have hS'P := conjSub_le hnP hSP
  have hS'n := conjSub_normal hnP hSn
  have hS'cyc : IsCyclic ↥(conjSub n S) := isCyclic_conjSub n S
  have hSp : IsPGroup p ↥S := hPp.to_le hSP
  have hu' : n * u * n⁻¹ ∈ conjSub n S := mem_conjSub.2 ⟨u, huS, rfl⟩
  have hu'p : (n * u * n⁻¹) ^ p = 1 := by
    rw [conj_pow, hup]
    group
  have hu'1 : n * u * n⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have : n * u * n⁻¹ = n * 1 * n⁻¹ := by rw [h]; group
    simpa using this
  have hinf : S ⊓ conjSub n S = ⊥ := inf_eq_bot_of_cyclic hp hSp huS hu' hup hu'p hu1 hu'1 hnu
  refine ⟨fun y hy => hCS y (hS'P hy) (fun s hs => ?_), hinf⟩
  have h1 : s * y * s⁻¹ * y⁻¹ ∈ S := by
    have := S.mul_mem hs (hSn y (hS'P hy) s⁻¹ (S.inv_mem hs))
    simpa [mul_assoc] using this
  have h2 : s * y * s⁻¹ * y⁻¹ ∈ conjSub n S := by
    have := hS'n s (hSP hs) y hy
    exact (conjSub n S).mul_mem this ((conjSub n S).inv_mem hy)
  have h3 : s * y * s⁻¹ * y⁻¹ ∈ S ⊓ conjSub n S := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot] at h3
  calc y * s = (s * y * s⁻¹ * y⁻¹)⁻¹ * (s * y) := by group
    _ = s * y := by rw [h3]; group

theorem card_le_of_inf_bot [Finite G] {Q A B S : Subgroup G}
    (hQ : ∀ q ∈ Q, ∃ a ∈ A, ∃ b ∈ B, q = a * b) (hSQ : S ≤ Q) (hAS : A ⊓ S = ⊥) :
    Nat.card S ≤ Nat.card B := by
  classical
  have hex : ∀ s : S, ∃ b : B, ∃ a ∈ A, (s : G) = a * b := fun s => by
    obtain ⟨a, ha, b, hb, h⟩ := hQ s (hSQ s.2)
    exact ⟨⟨b, hb⟩, a, ha, h⟩
  choose g a ha hs using hex
  refine Nat.card_le_card_of_injective g ?_
  intro s₁ s₂ h
  have h1 : (s₁ : G) * (s₂ : G)⁻¹ = a s₁ * (a s₂)⁻¹ := by
    rw [hs s₁, hs s₂, h]
    group
  have h2 : (s₁ : G) * (s₂ : G)⁻¹ ∈ A ⊓ S :=
    ⟨by rw [h1]; exact A.mul_mem (ha s₁) (A.inv_mem (ha s₂)), S.mul_mem s₁.2 (S.inv_mem s₂.2)⟩
  rw [hAS, Subgroup.mem_bot] at h2
  exact Subtype.ext (mul_inv_eq_one.1 h2)

end CFSG.RankThree.PartOne.ZR7
