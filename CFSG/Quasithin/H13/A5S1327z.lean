module

public import CFSG.Quasithin.H13.A5S1327s

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

theorem perm3_fpf : ∀ σ : Equiv.Perm (Fin 3), (∀ i, σ i ≠ i) → σ ^ 3 = 1 ∧ σ ≠ 1 := by
  decide

theorem perm3_fix : ∀ σ : Equiv.Perm (Fin 3), (∃ i, σ i = i) → σ ≠ 1 → σ ^ 2 = 1 := by
  decide

section Perm3

variable {G : Type} [Group G]

@[expose] def conjPerm {X : Subgroup G} {P : Set G}
    (hP : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) : ↥X →* Equiv.Perm ↥P where
  toFun x :=
    { toFun := fun p => ⟨(x : G) * p * (x : G)⁻¹, hP x x.2 p p.2⟩
      invFun := fun p => ⟨(x : G)⁻¹ * p * (x : G), by
        have := hP x⁻¹ (X.inv_mem x.2) p p.2
        simpa using this⟩
      left_inv := fun p => Subtype.ext (by simp [mul_assoc])
      right_inv := fun p => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext p; simp
  map_mul' x y := by ext p; simp [mul_assoc]

theorem quotient_pCore_equiv_perm3_of_conjPerm [Finite G] {X : Subgroup G} {P : Set G}
    (h3 : Nat.card ↥P = 3) (hP : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    {c : G} (hcX : c ∈ X) (hc : ∀ p ∈ P, c * p * c⁻¹ ≠ p)
    {j : G} (hjX : j ∈ X) {p₀ : G} (hp₀ : p₀ ∈ P) (hjp₀ : j * p₀ * j⁻¹ = p₀)
    {p₁ : G} (hp₁ : p₁ ∈ P) (hjp₁ : j * p₁ * j⁻¹ ≠ p₁)
    (hker : ∀ x ∈ X, (∀ p ∈ P, x * p * x⁻¹ = p) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    Nonempty (↥X ⧸ CFSG.Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : ↥P ≃ Fin 3 := (Finite.equivFin ↥P).trans (finCongr h3) with he
  set F : ↥X →* Equiv.Perm (Fin 3) := (Equiv.permCongrHom e).toMonoidHom.comp (conjPerm hP)
    with hF
  have hFapp : ∀ (x : ↥X) (i : Fin 3), F x i = e (conjPerm hP x (e.symm i)) := fun x i => rfl
  have hfix : ∀ (x : ↥X) (i : Fin 3), F x i = i ↔
      (x : G) * (e.symm i : G) * (x : G)⁻¹ = (e.symm i : G) := by
    intro x i
    rw [hFapp]
    constructor
    · intro h
      have h1 := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at h1
      exact congrArg Subtype.val h1
    · intro h
      have h1 : conjPerm hP x (e.symm i) = e.symm i := Subtype.ext h
      rw [h1, Equiv.apply_symm_apply]
  have hFc : F ⟨c, hcX⟩ ^ 3 = 1 ∧ F ⟨c, hcX⟩ ≠ 1 := by
    refine perm3_fpf _ fun i h => ?_
    exact hc _ (e.symm i).2 ((hfix _ i).1 h)
  have hFj1 : F ⟨j, hjX⟩ ≠ 1 := by
    intro h
    apply hjp₁
    have h1 := (hfix ⟨j, hjX⟩ (e ⟨p₁, hp₁⟩)).1 (by rw [h]; rfl)
    simpa using h1
  have hFj : F ⟨j, hjX⟩ ^ 2 = 1 :=
    perm3_fix _ ⟨e ⟨p₀, hp₀⟩, (hfix _ _).2 (by simpa using hjp₀)⟩ hFj1
  have h3c : orderOf (F ⟨c, hcX⟩) = 3 :=
    orderOf_eq_prime hFc.1 hFc.2
  have h2j : orderOf (F ⟨j, hjX⟩) = 2 :=
    orderOf_eq_prime hFj hFj1
  have hsurj : Function.Surjective F := by
    have hd3 : 3 ∣ Nat.card F.range := by
      have := Subgroup.orderOf_dvd_natCard F.range ⟨⟨c, hcX⟩, rfl⟩
      rwa [h3c] at this
    have hd2 : 2 ∣ Nat.card F.range := by
      have := Subgroup.orderOf_dvd_natCard F.range ⟨⟨j, hjX⟩, rfl⟩
      rwa [h2j] at this
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
    have hdvd : Nat.card F.range ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card _
    have hcard : Nat.card F.range = 6 := by
      have h6' : 6 ∣ Nat.card F.range :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd2 hd3
      exact Nat.dvd_antisymm hdvd h6'
    have htop : F.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard, h6])
    exact MonoidHom.range_eq_top.mp htop
  have hker' : CFSG.Open.pCore 2 ↥X = F.ker := by
    apply le_antisymm
    · have hn : ((CFSG.Open.pCore 2 ↥X).map F).Normal :=
        Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) _ hsurj
      have hp : IsPGroup 2 ↥((CFSG.Open.pCore 2 ↥X).map F) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup 2).map _
      have hbot := eq_bot_of_normal_isPGroup_perm3 hn hp
      intro g hg
      have : F g ∈ (CFSG.Open.pCore 2 ↥X).map F := Subgroup.mem_map_of_mem _ hg
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun g => ?_
      have hg1 : F g = 1 := g.2
      obtain ⟨k, hk⟩ := hker (g : ↥X) (g : ↥X).2 fun p hp => by
        have := (hfix g (e ⟨p, hp⟩)).1 (by rw [hg1]; rfl)
        simpa using this
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker').trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)⟩

end Perm3

namespace TwoBlocks

variable {G : Type} [Group G] [Finite G] {U : Subgroup G} {hU : IsElemAbelian 2 U}
  {H T : Subgroup G} {K₁ K₂ : Subgroup (MulAut (IntMod U hU))} (B : TwoBlocks hU H T K₁ K₂)
include B

theorem preserves_of_fix {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1)
    {g : MulAut (IntMod U hU)}
    (hgL : ∀ φ ∈ autI hU (twoResidual H), g * φ * g⁻¹ ∈ autI hU (twoResidual H))
    {e : IntMod U hU} (he : e ∈ commV K₂) (he1 : e ≠ 1) (hge : g e = e) :
    (∀ u ∈ commV K₁, g u ∈ commV K₁) ∧ (∀ u ∈ commV K₂, g u ∈ commV K₂) := by
  classical
  have hL := B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  have hc : ∀ a ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers y₂, a * b = b * a := fun a ha b hb =>
    B.comm a ((Subgroup.zpowers_le).2 hy₁ ha) b ((Subgroup.zpowers_le).2 hy₂ hb)
  have hpow : ∀ (y : MulAut (IntMod U hU)), y ^ 3 = 1 → ∀ a ∈ Subgroup.zpowers y, a ^ 3 = 1 := by
    rintro y hy _ ⟨i, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hst₁ : ∀ l ∈ K₁, ∀ u ∈ commV K₁, l u ∈ commV K₁ := fun l hl u hu => commV_stable K₁ hl hu
  have hst₂ : ∀ l ∈ K₂, ∀ u ∈ commV K₂, l u ∈ commV K₂ := fun l hl u hu => commV_stable K₂ hl hu
  have hy₁L : y₁ ∈ autI hU (twoResidual H) := by
    rw [hL]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  have hy₂L : y₂ ∈ autI hU (twoResidual H) := by
    rw [hL]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  have hcube : ∀ x : MulAut (IntMod U hU), x ^ 3 = 1 → (g * x * g⁻¹) ^ 3 = 1 := fun x hx => by
    rw [conj_pow, hx]; group
  have hne1 : ∀ x : MulAut (IntMod U hU), x ≠ 1 → g * x * g⁻¹ ≠ 1 := fun x hx h => hx (by
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, h]; group)
  have hgU : ∀ u ∈ commV K₁ ⊔ commV K₂, g u ∈ commV K₁ ⊔ commV K₂ := by
    intro u hu
    rw [← B.commV_autI_twoResidual hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1] at hu ⊢
    have h1 : g u ∈ (commV (autI hU (twoResidual H))).map g.toMonoidHom := ⟨u, hu, rfl⟩
    rw [commV_map_conjAut] at h1
    refine commV_mono' ?_ h1
    intro x hx
    rw [B1.mem_conjAut] at hx
    have := hgL _ hx
    simpa [mul_assoc] using this
  have hfpf : ∀ p ∈ Subgroup.zpowers y₁, ∀ q ∈ Subgroup.zpowers y₂, p ≠ 1 → q ≠ 1 →
      ∀ u ∈ commV K₁ ⊔ commV K₂, (p * q) u = u → u = 1 := by
    intro p hp q hq hp1 hq1 u hu hfix
    have hpK := (Subgroup.zpowers_le).2 hy₁ hp
    have hqK := (Subgroup.zpowers_le).2 hy₂ hq
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
    have e1 : (p * q) (u₁ * u₂) = p u₁ * q u₂ := by
      rw [MulAut.mul_apply, map_mul, B.apply_eq₂ hqK hu₁, map_mul,
        B.apply_eq₁ hpK (hst₂ q hqK u₂ hu₂)]
    rw [e1] at hfix
    obtain ⟨h1, h2⟩ := S1417.eq_of_mul_eq_of_inf_eq_bot B.commV_inf (hst₁ p hpK u₁ hu₁) hu₁
      (hst₂ q hqK u₂ hu₂) hu₂ hfix
    rw [natL2_fix_eq_one B.nat₁ hst₁ hpK (hpow y₁ hy₁3 p hp) hp1 hu₁ h1,
      natL2_fix_eq_one B.nat₂ hst₂ hqK (hpow y₂ hy₂3 q hq) hq1 hu₂ h2, one_mul]
  have hne : ∀ (K : Subgroup (MulAut (IntMod U hU))), ActsAsNaturalL2 K (commV K) →
      ∃ u ∈ commV K, u ≠ 1 := by
    intro K hN
    have := (S1417.card_of_actsAsNaturalL2 hN).2
    by_contra hcon
    push Not at hcon
    have hb : commV K = ⊥ := eq_bot_iff.mpr fun u hu => (Subgroup.mem_bot).mpr (hcon u hu)
    rw [hb, Subgroup.card_bot] at this
    omega
  have hline : ∀ y ∈ autI hU (twoResidual H), y ^ 3 = 1 → y ≠ 1 →
      (∃ u ∈ commV K₁ ⊔ commV K₂, u ≠ 1 ∧ y u = u) →
      y ∈ Subgroup.zpowers y₁ ∨ y ∈ Subgroup.zpowers y₂ := by
    intro y hyL _ _ ⟨u, hu, hu1, hyu⟩
    rw [hL] at hyL
    obtain ⟨p, hp, q, hq, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hc hyL
    by_cases hp1 : p = 1
    · right; rw [hp1, one_mul]; exact hq
    · by_cases hq1 : q = 1
      · left; rw [hq1, mul_one]; exact hp
      · exact absurd (hfpf p hp q hq hp1 hq1 u hu hyu) hu1
  have hy₁fix : ∃ u ∈ commV K₁ ⊔ commV K₂, u ≠ 1 ∧ (g * y₁ * g⁻¹) u = u := by
    obtain ⟨u, hu, hu1⟩ := hne K₂ B.nat₂
    refine ⟨g u, hgU u (Subgroup.mem_sup_right hu), fun h => hu1 ?_, ?_⟩
    · exact g.injective (h.trans (map_one g).symm)
    · simp [MulAut.mul_apply, B.apply_eq₁ hy₁ hu]
  have hy₂fix : ∃ u ∈ commV K₁ ⊔ commV K₂, u ≠ 1 ∧ (g * y₂ * g⁻¹) u = u := by
    obtain ⟨u, hu, hu1⟩ := hne K₁ B.nat₁
    refine ⟨g u, hgU u (Subgroup.mem_sup_left hu), fun h => hu1 ?_, ?_⟩
    · exact g.injective (h.trans (map_one g).symm)
    · simp [MulAut.mul_apply, B.apply_eq₂ hy₂ hu]
  have hl₁ := hline _ (hgL y₁ hy₁L) (hcube y₁ hy₁3) (hne1 y₁ hy₁1) hy₁fix
  have hl₂ := hline _ (hgL y₂ hy₂L) (hcube y₂ hy₂3) (hne1 y₂ hy₂1) hy₂fix
  have hA12 : Subgroup.zpowers y₁ ≠ Subgroup.zpowers y₂ := by
    intro h
    have : y₁ ∈ K₁ ⊓ K₂ := ⟨hy₁, (Subgroup.zpowers_le).2 hy₂ (h ▸ Subgroup.mem_zpowers y₁)⟩
    rw [B.inf, Subgroup.mem_bot] at this
    exact hy₁1 this
  have hgen : ∀ (y x : MulAut (IntMod U hU)), y ^ 3 = 1 → y ≠ 1 →
      x ∈ Subgroup.zpowers y → x ≠ 1 → Subgroup.zpowers x = Subgroup.zpowers y := by
    intro y x hy3 hy1 hx hx1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hox : orderOf x = 3 := orderOf_eq_prime (hpow y hy3 x hx) hx1
    have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    exact Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy])
  have himg : ∀ (y : MulAut (IntMod U hU)), y ^ 3 = 1 → y ≠ 1 →
      (g * y * g⁻¹ ∈ Subgroup.zpowers y₁ ∨ g * y * g⁻¹ ∈ Subgroup.zpowers y₂) →
      B1.conjAut g (Subgroup.zpowers y) = Subgroup.zpowers y₁ ∨
        B1.conjAut g (Subgroup.zpowers y) = Subgroup.zpowers y₂ := by
    intro y hy3 hy1 h
    rw [conjAut_zpowers]
    rcases h with h | h
    · exact Or.inl (hgen y₁ _ hy₁3 hy₁1 h (hne1 y hy1))
    · exact Or.inr (hgen y₂ _ hy₂3 hy₂1 h (hne1 y hy1))
  have hi₁ := himg y₁ hy₁3 hy₁1 hl₁
  have hi₂ := himg y₂ hy₂3 hy₂1 hl₂
  have hinjc : ∀ A A' : Subgroup (MulAut (IntMod U hU)),
      B1.conjAut g A = B1.conjAut g A' → A = A' := by
    intro A A' h
    ext x
    have h1 : g * x * g⁻¹ ∈ B1.conjAut g A ↔ x ∈ A := by
      rw [B1.mem_conjAut]; simp [mul_assoc]
    have h2 : g * x * g⁻¹ ∈ B1.conjAut g A' ↔ x ∈ A' := by
      rw [B1.mem_conjAut]; simp [mul_assoc]
    rw [← h1, ← h2, h]
  have hU₁z : commV K₁ = commV (Subgroup.zpowers y₁) :=
    (commV_zpowers_eq B.nat₁ hy₁ hy₁3 hy₁1).symm
  have hU₂z : commV K₂ = commV (Subgroup.zpowers y₂) :=
    (commV_zpowers_eq B.nat₂ hy₂ hy₂3 hy₂1).symm
  have hfix₂ : B1.conjAut g (Subgroup.zpowers y₂) = Subgroup.zpowers y₂ := by
    rcases hi₂ with h | h
    · exfalso
      have h1 : g e ∈ commV K₁ := by
        rw [hU₁z, ← h, ← commV_map_conjAut, ← hU₂z]
        exact ⟨e, he, rfl⟩
      rw [hge] at h1
      have h2 : e ∈ commV K₁ ⊓ commV K₂ := ⟨h1, he⟩
      rw [B.commV_inf, Subgroup.mem_bot] at h2
      exact he1 h2
    · exact h
  have hfix₁ : B1.conjAut g (Subgroup.zpowers y₁) = Subgroup.zpowers y₁ := by
    rcases hi₁ with h | h
    · exact h
    · exact absurd (hinjc _ _ (h.trans hfix₂.symm)) hA12
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : g u ∈ (commV K₁).map g.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hU₁z, commV_map_conjAut, hfix₁, ← hU₁z] at h1
  · have h1 : g u ∈ (commV K₂).map g.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hU₂z, commV_map_conjAut, hfix₂, ← hU₂z] at h1

theorem exists_c' {P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ P) :
    ∃ c ∈ twoResidual H, ∃ hc : c ∈ Subgroup.normalizer (U : Set G),
      c ^ 3 = 1 ∧ convI hU ⟨c, hc⟩ ∈ K₁ ∧ convI hU ⟨c, hc⟩ ≠ 1 := by
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨y₂, hy₂, hy₂3, hy₂1⟩ := S1417.exists_orderThree B.nat₂
  have hL := B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  have hy₁L : y₁ ∈ autI hU (twoResidual H) := by
    rw [hL]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  obtain ⟨x, hxL, hxy⟩ := (mem_autI hU).1 hy₁L
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
  set c := (x : G) ^ 2 ^ a with hcdef
  have hcN : c ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ x.2 _
  have hcv : convI hU ⟨c, hcN⟩ = y₁ ^ 2 ^ a := by
    rw [← hxy, ← map_pow]
    rfl
  have hc1 : convI hU ⟨c, hcN⟩ ≠ 1 := by
    rw [hcv]
    intro h
    have h3 : orderOf y₁ = 3 := orderOf_eq_prime hy₁3 hy₁1
    have hdvd : orderOf y₁ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
    rw [h3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hcodd : Odd (orderOf c) := by
    have h2a : (2 ^ a : ℕ) ≠ 0 := by positivity
    rw [hcdef, orderOf_pow' _ h2a, ham, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hcH : c ∈ H := (twoResidual_le H) (Subgroup.pow_mem _ hxL _)
  have hc3P : c ^ 3 ∈ P := by
    refine hCU ⟨H.pow_mem hcH 3, ?_⟩
    have h1 : convI hU ⟨c ^ 3, Subgroup.pow_mem _ hcN 3⟩ = 1 := by
      rw [show (⟨c ^ 3, Subgroup.pow_mem _ hcN 3⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        ⟨c, hcN⟩ ^ 3 from rfl, map_pow, hcv, ← pow_mul, mul_comm, pow_mul, hy₁3, one_pow]
    exact (convI_eq_one_iff hU _).1 h1
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hP ⟨c ^ 3, hc3P⟩
    have h2 : (c ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : (c ^ 3) ^ orderOf c = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_one_of_pow_coprime h2 hm' (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hcodd))
  exact ⟨c, Subgroup.pow_mem _ hxL _, hcN, hc3, by rw [hcv]; exact K₁.pow_mem hy₁ _, hc1⟩

end TwoBlocks

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem inf_M_eq_T (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {hU : IsElemAbelian 2 (S.UH H)}
    {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))} (B : TwoBlocks hU H T K₁ K₂)
    (htop : commV K₁ ⊔ commV K₂ = ⊤) :
    H ⊓ Subgroup.normalizer (L : Set G) = T := by
  classical
  set M := Subgroup.normalizer (L : Set G) with hM
  have hTH : T ≤ H := hH.1.1
  have hTM : T ≤ M := S.T_le_NL
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hCU : H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H :=
    S.centralizer_UH_le_pCoreOf_all h331 h1222 h5172 hH hHZ hsolv
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := B.le_norm
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨y₂, hy₂, hy₂3, hy₂1⟩ := S1417.exists_orderThree B.nat₂
  obtain ⟨t, htT, ht⟩ := B.swap
  have hJH := (E2_3_two_sylow_of_isSolvable hU (S.hyp501.minParabolic_of_isHStar h331 hH).1
    hsolv (fun p hp hp2 => by
      obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
      have : Fact p.Prime := ⟨hp⟩
      have h1 := hq p hp hp2
      rwa [← pRank_top_subtype]) (conjClosure_isTwoReducedIn_of_charTwo hsyl
        (S.charTwo_of_inH hH.1) le_rfl).2.2
    (S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ)).2
  rw [B.eqJ] at hJH
  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ :=
    S1417.exists_sylowData hJH B.nat₁ B.nat₂ B.comm B.inf B.commV_inf htop
  have hs₁sq : s₁ ^ 2 = 1 := by
    rcases hd.inf₁ (s₁ ^ 2) (Subgroup.pow_mem _ hd.s₁_mem_S 2) (K₁.pow_mem hd.s₁_mem_L 2) with
      h | h
    · exact h
    · exfalso
      apply hd.s₁_ne
      have : s₁ * s₁ = s₁ * 1 := by rw [← sq, h, mul_one]
      exact mul_left_cancel this
  have hs₁T : s₁ ∈ autI hU T := autI_mono hU (thompsonJ_le_self T) hd.s₁_mem_S
  set Y := autI hU (twoResidual H ⊓ M) with hYdef
  have hYL : Y ≤ autI hU (twoResidual H) := autI_mono hU inf_le_left
  have hTY : autI hU T ≤ Subgroup.normalizer (Y : Set (MulAut (IntMod (S.UH H) hU))) := by
    intro g hg
    obtain ⟨t₀, ht₀T, rfl⟩ := (mem_autI hU).1 hg
    have hmem : ∀ (s : G) (hs : s ∈ T) (hsN : s ∈ Subgroup.normalizer (S.UH H : Set G)),
        ∀ φ ∈ Y, convI hU ⟨s, hsN⟩ * φ * (convI hU ⟨s, hsN⟩)⁻¹ ∈ Y := by
      intro s hs hsN φ hφ
      obtain ⟨x, hx, rfl⟩ := (mem_autI hU).1 hφ
      rw [← map_inv, ← map_mul, ← map_mul]
      refine (mem_autI hU).2 ⟨⟨s, hsN⟩ * x * (⟨s, hsN⟩)⁻¹, ⟨?_, ?_⟩, rfl⟩
      · show s * (x : G) * s⁻¹ ∈ twoResidual H
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (hTH hs)) x).mp hx.1
      · show s * (x : G) * s⁻¹ ∈ M
        exact M.mul_mem (M.mul_mem (hTM hs) hx.2) (M.inv_mem (hTM hs))
    refine B6.mem_normalizer_of_forall_mem (fun φ hφ => hmem t₀ ht₀T t₀.2 φ hφ) fun φ hφ => ?_
    have := hmem (t₀ : G)⁻¹ (T.inv_mem ht₀T) (Subgroup.inv_mem _ t₀.2) φ hφ
    rw [show (⟨(t₀ : G)⁻¹, Subgroup.inv_mem _ t₀.2⟩ : ↥(Subgroup.normalizer (S.UH H : Set G))) =
      t₀⁻¹ from rfl, map_inv, inv_inv] at this
    exact this
  by_cases hY1 : Y = ⊥
  ·
    have hLM : twoResidual H ⊓ M ≤ T := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (S.UH H : Set G) := hHN (twoResidual_le H hx.1)
      have h1 : convI hU ⟨x, hxN⟩ = 1 := by
        have : convI hU ⟨x, hxN⟩ ∈ Y := convI_mem_autI hU hx hxN
        rwa [hY1, Subgroup.mem_bot] at this
      exact hOT (hCU ⟨twoResidual_le H hx.1, (convI_eq_one_iff hU _).1 h1⟩)
    refine le_antisymm (fun x hx => ?_) (le_inf hTH hTM)
    have hx' : x ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by
      rw [twoResidual_eq_oTwoUpper', ← eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl]; exact hx.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hTH.trans (le_normalizer_twoResidual H))]
      at hx'
    obtain ⟨l, hl, s, hs, rfl⟩ := hx'
    have hlM : l ∈ M := by
      have e : l = l * s * s⁻¹ := by group
      rw [e]; exact M.mul_mem hx.2 (M.inv_mem (hTM hs))
    exact T.mul_mem (hLM ⟨hl, hlM⟩) hs
  ·
    exfalso
    have hYeq := B.eq_of_normalized hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1 hs₁T hd.s₁_mem_L hs₁sq hd.s₁_ne
      htT ht hYL hY1 hTY
    have hLM : twoResidual H ≤ M := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (S.UH H : Set G) := hHN (twoResidual_le H hx)
      have h1 : convI hU ⟨x, hxN⟩ ∈ Y := by rw [hYeq]; exact convI_mem_autI hU hx hxN
      obtain ⟨y, hy, hyx⟩ := (mem_autI hU).1 h1
      have hu : (y : G)⁻¹ * x ∈ H ⊓ Subgroup.centralizer (S.UH H : Set G) := by
        refine ⟨H.mul_mem (H.inv_mem (twoResidual_le H hy.1)) (twoResidual_le H hx), ?_⟩
        have h2 : convI hU (y⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
        exact (convI_eq_one_iff hU _).1 h2
      have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
      rw [e]
      exact M.mul_mem hy.2 (hTM (hOT (hCU hu)))
    apply hH.2.1
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl, ← twoResidual_eq_oTwoUpper']
    exact sup_le hLM hTM

end Setting

end CFSG.Quasithin.H13.A5
