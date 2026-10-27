module

public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Quasithin.Background.A3Structure320Basic

public section

namespace CFSG.Quasithin

namespace A318

open CFSG.Open CFSG.SectionRank CFSG.Quasithin.A320
open scoped commutatorElement

theorem exists_pElement_lift {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (f : G →* G') (l : G) (hl : ∃ k : ℕ, orderOf (f l) = p ^ k) :
    ∃ x : G, (∃ k : ℕ, orderOf x = p ^ k) ∧ f x = f l ∧ x ∈ Subgroup.zpowers l := by
  obtain ⟨j, hj⟩ := hl
  have hn : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  obtain ⟨u, v, huv⟩ : IsCoprime (m : ℤ) ((p ^ a : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 hcop.symm
  refine ⟨l ^ (u * (m : ℤ)), ?_, ?_, ⟨u * (m : ℤ), rfl⟩⟩
  · have h1 : (l ^ (u * (m : ℤ))) ^ (p ^ a) = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : u * (m : ℤ) * ((p ^ a : ℕ) : ℤ) = (orderOf l : ℤ) * u := by
        rw [hnm]
        push_cast
        ring
      rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk⟩
  · have hdvd : p ^ j ∣ p ^ a := by
      have h1 : p ^ j ∣ p ^ a * m := hnm ▸ (hj ▸ orderOf_map_dvd f l)
      exact (Nat.Coprime.pow_left j
        ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)).dvd_of_dvd_mul_right h1
    have h2 : (f l) ^ (p ^ a) = 1 := by
      rw [← hj] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    rw [map_zpow]
    have : u * (m : ℤ) = 1 - ((p ^ a : ℕ) : ℤ) * v := by linarith
    rw [this, zpow_sub, zpow_one, zpow_mul, zpow_natCast, h2, one_zpow, inv_one, mul_one]

theorem orderOf_map_eq_of_pElement {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}
    (f : G →* G') (hf : Nat.Coprime p (Nat.card f.ker)) {x : G}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) : orderOf (f x) = orderOf x := by
  obtain ⟨k, hk⟩ := hx
  refine Nat.dvd_antisymm (orderOf_map_dvd f x) ?_
  have hy : x ^ orderOf (f x) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have h1 : orderOf (x ^ orderOf (f x)) ∣ p ^ k := hk ▸ orderOf_pow_dvd (orderOf (f x))
  have h2 : orderOf (x ^ orderOf (f x)) ∣ Nat.card f.ker := Subgroup.orderOf_dvd_natCard _ hy
  have h3 : orderOf (x ^ orderOf (f x)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (hf.pow_left k)) h2
  exact orderOf_dvd_of_pow_eq_one (orderOf_eq_one_iff.1 h3)

theorem mem_of_pElement_of_star {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    {L : Subgroup H} [L.Normal] {x : H} (hx : ∃ k : ℕ, orderOf x = p ^ k)
    (hxS : QuotientGroup.mk' (CFSG.pPrimeCore p H) x ∈ starImage p L) : x ∈ L := by
  obtain ⟨l, hl, hlx⟩ := hxS
  have hn : l⁻¹ * x ∈ CFSG.pPrimeCore p H := by
    have := (QuotientGroup.eq (a := l) (b := x)).1 (by simpa using hlx)
    exact this
  let f : H →* H ⧸ L := QuotientGroup.mk' L
  have hfx : f x ∈ (CFSG.pPrimeCore p H).map f := by
    refine ⟨l⁻¹ * x, hn, ?_⟩
    have h1 : f l = 1 := (QuotientGroup.eq_one_iff l).2 hl
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  obtain ⟨k, hk⟩ := hx
  have h1 : orderOf (f x) ∣ p ^ k := hk ▸ orderOf_map_dvd f x
  have h2 : orderOf (f x) ∣ Nat.card (CFSG.pPrimeCore p H) :=
    (Subgroup.orderOf_dvd_natCard _ hfx).trans (Subgroup.card_map_dvd _ _)
  have h3 : orderOf (f x) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1
      (CFSG.pPrimeCore_coprime_card.pow_left k)) h2
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

theorem eq_of_le_sup_solvable {H : Type*} [Group H] [Finite H] {L T K : Subgroup H} [T.Normal]
    (hperf : ⁅L, L⁆ = L) (hTL : T ≤ L) (hK : Group.IsSolvable ↥K) (hL : L ≤ T ⊔ K) :
    L = T := by
  let f : H →* H ⧸ T := QuotientGroup.mk' T
  have hle : L.map f ≤ K.map f := by
    have h1 : L.map f ≤ (T ⊔ K).map f := Subgroup.map_mono hL
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff T).2 (by simp [f]), bot_sup_eq] at h1
    exact h1
  have hsolv : Group.IsSolvable ↥(L.map f) := by
    have : Group.IsSolvable ↥(K.map f) :=
      Group.isSolvable_of_surjective (f.subgroupMap_surjective K)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hperf' : Group.IsPerfect ↥(L.map f) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hperf]
  have hsub : Subsingleton ↥(L.map f) := by
    by_contra hns
    have : Nontrivial ↥(L.map f) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have hbot : L.map f = ⊥ := Subgroup.eq_bot_of_subsingleton _
  refine le_antisymm ?_ hTL
  intro l hl
  have : f l ∈ L.map f := ⟨l, hl, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff l).1 this

theorem normal_closure_of_conj {H : Type*} [Group H] {Gen : Set H}
    (hconj : ∀ g x : H, x ∈ Gen → g * x * g⁻¹ ∈ Gen) : (Subgroup.closure Gen).Normal :=
  ⟨fun n hn g => by
    refine Subgroup.closure_induction
      (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure Gen) ?_ ?_ ?_ ?_ hn
    · intro y hy
      exact Subgroup.subset_closure (hconj g y hy)
    · simp
    · intro x y _ _ hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx⟩

theorem eq_closure_of_star {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {L : Subgroup H} [L.Normal] (hperf : ⁅L, L⁆ = L)
    (hsolv : Group.IsSolvable ↥((CFSG.pPrimeCore p H).subgroupOf L)) {Gen : Set H}
    (hGenL : Gen ⊆ L) (hconj : ∀ g x : H, x ∈ Gen → g * x * g⁻¹ ∈ Gen)
    (hgen : ∀ l ∈ L, ∃ t ∈ Subgroup.closure Gen,
      QuotientGroup.mk' (CFSG.pPrimeCore p H) t = QuotientGroup.mk' (CFSG.pPrimeCore p H) l) :
    L = Subgroup.closure Gen := by
  have hTn : (Subgroup.closure Gen).Normal := normal_closure_of_conj hconj
  have hTL : Subgroup.closure Gen ≤ L := (Subgroup.closure_le L).2 hGenL
  have hK : Group.IsSolvable ↥(L ⊓ CFSG.pPrimeCore p H) := by
    have := hsolv
    let g : ↥((CFSG.pPrimeCore p H).subgroupOf L) →* ↥(L ⊓ CFSG.pPrimeCore p H) :=
      ((L.subtype).comp ((CFSG.pPrimeCore p H).subgroupOf L).subtype).codRestrict _ fun x =>
        ⟨x.1.2, Subgroup.mem_subgroupOf.1 x.2⟩
    refine Group.isSolvable_of_surjective (f := g) ?_
    intro y
    exact ⟨⟨⟨y, y.2.1⟩, Subgroup.mem_subgroupOf.2 y.2.2⟩, Subtype.ext rfl⟩
  refine eq_of_le_sup_solvable hperf hTL hK ?_
  intro l hl
  obtain ⟨t, ht, htl⟩ := hgen l hl
  have hnt : t⁻¹ * l ∈ CFSG.pPrimeCore p H := QuotientGroup.eq.1 htl
  have : l = t * (t⁻¹ * l) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ht ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTL ht)) hl, hnt⟩

theorem exists_preimage_closure {H G : Type*} [Group H] [Group G] (f : H →* G) {Gen : Set H}
    {Y : Set G} (hY : ∀ y ∈ Y, ∃ t ∈ Subgroup.closure Gen, f t = y) {g : G}
    (hg : g ∈ Subgroup.closure Y) : ∃ t ∈ Subgroup.closure Gen, f t = g := by
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ t ∈ Subgroup.closure Gen, f t = g) ?_ ?_ ?_ ?_ hg
  · exact hY
  · exact ⟨1, Subgroup.one_mem _, map_one f⟩
  · rintro x y _ _ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, rfl⟩
    exact ⟨t₁ * t₂, Subgroup.mul_mem _ ht₁ ht₂, map_mul f t₁ t₂⟩
  · rintro x _ ⟨t, ht, rfl⟩
    exact ⟨t⁻¹, Subgroup.inv_mem _ ht, map_inv f t⟩

theorem conj_mem_pElements {H : Type*} [Group H] {p : ℕ} {L : Subgroup H} [L.Normal] {x : H}
    (g : H) (hx : x ∈ L ∧ ∃ k : ℕ, orderOf x = p ^ k) :
    g * x * g⁻¹ ∈ L ∧ ∃ k : ℕ, orderOf (g * x * g⁻¹) = p ^ k := by
  obtain ⟨hxL, k, hk⟩ := hx
  refine ⟨Subgroup.Normal.conj_mem ‹L.Normal› x hxL g, k, ?_⟩
  rw [← hk]
  exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem eq_oPrimeResidual_of_star {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    {L : Subgroup H} [L.Normal] (hperf : ⁅L, L⁆ = L)
    (hsolv : Group.IsSolvable ↥((CFSG.pPrimeCore p H).subgroupOf L))
    (hS : starImage p L = oPrimeResidualOf p (⊤ : Subgroup (PStar p H))) :
    L = oPrimeResidualOf p (⊤ : Subgroup H) := by
  have hker : Nat.Coprime p (Nat.card (QuotientGroup.mk' (CFSG.pPrimeCore p H)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  have hL : L = Subgroup.closure {x : H | x ∈ L ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
    refine eq_closure_of_star hperf hsolv (fun x hx => hx.1) (fun g x hx => conj_mem_pElements g hx)
      (fun l hl => ?_)
    have hmem : QuotientGroup.mk' (CFSG.pPrimeCore p H) l ∈ starImage p L := ⟨l, hl, rfl⟩
    rw [hS] at hmem
    refine exists_preimage_closure _ (fun y hy => ?_) hmem
    obtain ⟨-, k, hk⟩ := hy
    have hyS : y ∈ starImage p L := hS ▸ Subgroup.subset_closure ⟨Subgroup.mem_top _, k, hk⟩
    obtain ⟨l', hl', rfl⟩ := hyS
    obtain ⟨x, ⟨j, hj⟩, hx, hxl⟩ := exists_pElement_lift (QuotientGroup.mk' (CFSG.pPrimeCore p H))
      l' ⟨k, hk⟩
    exact ⟨x, Subgroup.subset_closure ⟨(Subgroup.zpowers_le.2 hl') hxl, j, hj⟩, hx⟩
  apply le_antisymm
  · rw [hL]
    exact Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_top _, hx.2⟩
  · refine (Subgroup.closure_le L).2 ?_
    rintro x ⟨-, k, hk⟩
    refine mem_of_pElement_of_star ⟨k, hk⟩ ?_
    rw [hS]
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1
      (hk ▸ orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore p H)) x)
    exact ⟨j, hj⟩

theorem eq_thetaOf_of_star {H : Type} [Group H] [Finite H] [hp : Fact (Nat.Prime 3)]
    {L : Subgroup H} [L.Normal] (hperf : ⁅L, L⁆ = L)
    (hsolv : Group.IsSolvable ↥((CFSG.pPrimeCore 3 H).subgroupOf L))
    (hS : starImage 3 L = thetaOf (⊤ : Subgroup (PStar 3 H))) :
    L = thetaOf (⊤ : Subgroup H) := by
  have hker : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  have hL : L = Subgroup.closure {x : H | x ∈ L ∧ orderOf x = 3} := by
    refine eq_closure_of_star hperf hsolv (fun x hx => hx.1) (fun g x hx => ?_) (fun l hl => ?_)
    · refine ⟨Subgroup.Normal.conj_mem ‹L.Normal› x hx.1 g, ?_⟩
      rw [← hx.2]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 H) l ∈ starImage 3 L := ⟨l, hl, rfl⟩
    rw [hS] at hmem
    refine exists_preimage_closure _ (fun y hy => ?_) hmem
    obtain ⟨-, hy3⟩ := hy
    have hyS : y ∈ starImage 3 L := hS ▸ Subgroup.subset_closure ⟨Subgroup.mem_top _, hy3⟩
    obtain ⟨l', hl', rfl⟩ := hyS
    obtain ⟨x, ⟨j, hj⟩, hx, hxl⟩ := exists_pElement_lift (p := 3)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) l' ⟨1, by rw [hy3]; simp⟩
    refine ⟨x, Subgroup.subset_closure ⟨(Subgroup.zpowers_le.2 hl') hxl, ?_⟩, hx⟩
    rw [← orderOf_map_eq_of_pElement (p := 3) _ hker ⟨j, hj⟩, hx, hy3]
  apply le_antisymm
  · rw [hL]
    exact Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_top _, hx.2⟩
  · refine (Subgroup.closure_le L).2 ?_
    rintro x ⟨-, hx3⟩
    refine mem_of_pElement_of_star (p := 3) ⟨1, by rw [hx3]; simp⟩ ?_
    rw [hS]
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    rw [orderOf_map_eq_of_pElement (p := 3) _ hker ⟨1, by rw [hx3]; simp⟩, hx3]

end A318

end CFSG.Quasithin
