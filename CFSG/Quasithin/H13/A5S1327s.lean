module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs
public import CFSG.Quasithin.H13.A5S1327f
public import CFSG.Quasithin.H13.A5S1327q

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

section Blocks

variable {G : Type} [Group G] {U : Subgroup G} {hU : IsElemAbelian 2 U}
  {H T : Subgroup G} {K₁ K₂ : Subgroup (MulAut (IntMod U hU))}

theorem commV_mono' {W : Type*} [CommGroup W] {H K : Subgroup (MulAut W)} (h : H ≤ K) :
    commV H ≤ commV K :=
  Subgroup.closure_mono fun _ ⟨g, hg, v, hv⟩ => ⟨g, h hg, v, hv⟩

theorem commV_zpowers_eq [Finite G] {K : Subgroup (MulAut (IntMod U hU))}
    (hN : ActsAsNaturalL2 K (commV K))
    {y : MulAut (IntMod U hU)} (hy : y ∈ K) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    commV (Subgroup.zpowers y) = commV K := by
  refine le_antisymm (commV_mono' ((Subgroup.zpowers_le).2 hy)) ?_
  have hst : ∀ l ∈ K, ∀ u ∈ commV K, l u ∈ commV K := fun l hl u hu => commV_stable K hl hu
  have hinj : Set.InjOn (commHomAut y) (commV K : Set (IntMod U hU)) := by
    intro u hu v hv huv
    have h1 : commHomAut y (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    rw [commHomAut_apply] at h1
    have h2 : y (u * v⁻¹) = u * v⁻¹ := mul_inv_eq_one.mp h1
    have h3 := natL2_fix_eq_one hN hst hy hy3 hy1 ((commV K).mul_mem hu ((commV K).inv_mem hv)) h2
    exact mul_inv_eq_one.mp h3
  have hmaps : Set.MapsTo (commHomAut y) (commV K : Set (IntMod U hU)) (commV K) := by
    intro u hu
    exact (commV K).mul_mem (hst y hy u hu) ((commV K).inv_mem hu)
  have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite _) hmaps).1 hinj
  intro u hu
  obtain ⟨v, -, rfl⟩ := hsurj.surjOn hu
  exact Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, rfl⟩

theorem apply_eq_of_odd_of_fixed {K : Subgroup (MulAut (IntMod U hU))}
    (hN : ActsAsNaturalL2 K (commV K)) {g : MulAut (IntMod U hU)} (hgodd : Odd (orderOf g))
    (hg : (commV K).map g.toMonoidHom = commV K) {e : IntMod U hU} (he : e ∈ commV K)
    (he1 : e ≠ 1) (hge : g e = e) : ∀ u ∈ commV K, g u = u := by
  have hst : ∀ l ∈ K, ∀ u ∈ commV K, l u ∈ commV K := fun l hl u hu => commV_stable K hl hu
  have hgs : g ∈ stabSub (commV K) := S1417.mem_stabSub_of_map_eq hg
  have hgU : ∀ u ∈ commV K, g u ∈ commV K := fun u hu => (hgs u).2 hu
  obtain ⟨k, hk, hkg⟩ := S1417.exists_apply_eq_of_stab hN hst hgs
  have hgnU : ∀ n : ℕ, ∀ u ∈ commV K, (g ^ n) u ∈ commV K := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih => intro u hu; rw [pow_succ', MulAut.mul_apply]; exact hgU _ (ih u hu)
  have hpow : ∀ n : ℕ, ∀ u ∈ commV K, (k ^ n) u = (g ^ n) u := by
    intro n
    induction n with
    | zero => intro u _; rfl
    | succ n ih =>
      intro u hu
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih u hu,
        hkg _ (hgnU n u hu)]
  have hk1 : k ^ orderOf g = 1 := by
    refine S1417.eq_one_of_forall_apply_eq hN hst (K.pow_mem hk _) fun u hu => ?_
    rw [hpow _ u hu, pow_orderOf_eq_one, MulAut.one_apply]
  have hkodd : Odd (orderOf k) := Odd.of_dvd_nat hgodd (orderOf_dvd_of_pow_eq_one hk1)
  have hke : k e = e := by rw [hkg e he, hge]
  have hk1' := S1417.eq_one_of_odd_of_fixed hN hst hk hkodd he he1 hke
  intro u hu
  rw [← hkg u hu, hk1', MulAut.one_apply]

theorem conjAut_zpowers {W : Type*} [CommGroup W] (g y : MulAut W) :
    B1.conjAut g (Subgroup.zpowers y) = Subgroup.zpowers (g * y * g⁻¹) := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [conj_zpow, hi]
    group
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← hi, conj_zpow]
    group

namespace TwoBlocks

variable (B : TwoBlocks hU H T K₁ K₂)
include B

theorem commV_sup_le : commV (K₁ ⊔ K₂) ≤ commV K₁ ⊔ commV K₂ :=
  CFSG.Quasithin.FixVLat.commV_sup_le K₁ K₂

theorem commV_autI_twoResidual [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1) :
    commV (autI hU (twoResidual H)) = commV K₁ ⊔ commV K₂ := by
  have hL := B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  apply le_antisymm
  · exact (commV_mono' B.autI_twoResidual_le).trans B.commV_sup_le
  · rw [← commV_zpowers_eq B.nat₁ hy₁ hy₁3 hy₁1, ← commV_zpowers_eq B.nat₂ hy₂ hy₂3 hy₂1, hL]
    exact sup_le (commV_mono' le_sup_left) (commV_mono' le_sup_right)

theorem apply_eq_of_odd [Finite G] {y₁ y₂ : MulAut (IntMod U hU)} (hy₁ : y₁ ∈ K₁)
    (hy₁3 : y₁ ^ 3 = 1) (hy₁1 : y₁ ≠ 1) (hy₂ : y₂ ∈ K₂) (hy₂3 : y₂ ^ 3 = 1) (hy₂1 : y₂ ≠ 1)
    {t : MulAut (IntMod U hU)} (ht : B1.conjAut t K₁ = K₂) {g : MulAut (IntMod U hU)}
    (hgodd : Odd (orderOf g))
    (hgL : ∀ φ ∈ autI hU (twoResidual H), g * φ * g⁻¹ ∈ autI hU (twoResidual H))
    {e : IntMod U hU} (he1 : e ≠ 1) (heU : e ∈ commV K₁ ⊔ commV K₂) (hte : t e = e)
    (hge : g e = e) : ∀ u ∈ commV K₁ ⊔ commV K₂, g u = u := by
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
  have hfix₁ : B1.conjAut g (Subgroup.zpowers y₁) = Subgroup.zpowers y₁ := by
    rcases hi₁ with h | h
    · exact h
    exfalso
    have h₂ : B1.conjAut g (Subgroup.zpowers y₂) = Subgroup.zpowers y₁ := by
      rcases hi₂ with h' | h'
      · exact h'
      · exact absurd (hinjc _ _ (h.trans h'.symm)) hA12
    have hiter : ∀ m : ℕ, B1.conjAut (g ^ (2 * m)) (Subgroup.zpowers y₁) =
        Subgroup.zpowers y₁ := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.mul_zero, pow_zero]
        exact S1417.conjAut_eq_of_mem (Subgroup.one_mem _)
      | succ m ih =>
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ', S1417.conjAut_mul, pow_succ',
          S1417.conjAut_mul, ih, h, h₂]
    obtain ⟨m, hm⟩ := hgodd
    have h1 : B1.conjAut (g ^ orderOf g) (Subgroup.zpowers y₁) = Subgroup.zpowers y₂ := by
      rw [hm, pow_succ', S1417.conjAut_mul, hiter m, h]
    rw [pow_orderOf_eq_one, S1417.conjAut_eq_of_mem (Subgroup.one_mem _)] at h1
    exact hA12 h1
  have hfix₂ : B1.conjAut g (Subgroup.zpowers y₂) = Subgroup.zpowers y₂ := by
    rcases hi₂ with h | h
    · exact absurd (hinjc _ _ (h.trans hfix₁.symm)) hA12.symm
    · exact h
  have hU₁ : (commV K₁).map g.toMonoidHom = commV K₁ := by
    rw [← commV_zpowers_eq B.nat₁ hy₁ hy₁3 hy₁1, commV_map_conjAut, hfix₁]
  have hU₂ : (commV K₂).map g.toMonoidHom = commV K₂ := by
    rw [← commV_zpowers_eq B.nat₂ hy₂ hy₂3 hy₂1, commV_map_conjAut, hfix₂]
  have hgU₁ : ∀ u ∈ commV K₁, g u ∈ commV K₁ := fun u hu => by
    rw [← hU₁]; exact ⟨u, hu, rfl⟩
  have hgU₂ : ∀ u ∈ commV K₂, g u ∈ commV K₂ := fun u hu => by
    rw [← hU₂]; exact ⟨u, hu, rfl⟩
  have htU : (commV K₁).map t.toMonoidHom = commV K₂ := by rw [commV_map_conjAut, ht]
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Subgroup.mem_sup.mp heU
  have he₂1 : e₂ ≠ 1 := by
    intro h
    rw [h, mul_one] at he1 hte hge
    have h1 : t e₁ ∈ commV K₂ := by rw [← htU]; exact ⟨e₁, he₁, rfl⟩
    rw [hte] at h1
    have : e₁ ∈ commV K₁ ⊓ commV K₂ := ⟨he₁, h1⟩
    rw [B.commV_inf, Subgroup.mem_bot] at this
    exact he1 this
  have he₁1 : e₁ ≠ 1 := by
    intro h
    rw [h, one_mul] at he1 hte hge
    have h1 : e₂ ∈ (commV K₁).map t.toMonoidHom := by rw [htU]; exact he₂
    obtain ⟨u, hu, hu'⟩ := h1
    have h2 : u = e₂ := t.injective (hu'.trans hte.symm)
    have : e₂ ∈ commV K₁ ⊓ commV K₂ := ⟨h2 ▸ hu, he₂⟩
    rw [B.commV_inf, Subgroup.mem_bot] at this
    exact he1 this
  rw [map_mul] at hge
  obtain ⟨hge₁, hge₂⟩ := S1417.eq_of_mul_eq_of_inf_eq_bot B.commV_inf (hgU₁ e₁ he₁) he₁
    (hgU₂ e₂ he₂) he₂ hge
  have h₁ := apply_eq_of_odd_of_fixed B.nat₁ hgodd hU₁ he₁ he₁1 hge₁
  have h₂ := apply_eq_of_odd_of_fixed B.nat₂ hgodd hU₂ he₂ he₂1 hge₂
  intro u hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul, h₁ u₁ hu₁, h₂ u₂ hu₂]

end TwoBlocks

end Blocks

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem H0_le_normalizer_oTwoUpper (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (h1332 : Stmt13_3_2)
    (h137 : EmptyFaithfulMultiple.Input137) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) :
    S.H0 H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hXi := S.isXiStar_oTwoUpper h331 h1222 h5172 h1332 hH hHZ hsolv hS3
  have hU := h137 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow _ hXi
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨pCoreOf 2 (S.H0 H), hO2, pCoreOf_isPGroup 2 _, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (S.H0 H) : Set G)))
  have hH0M' : S.H0 H ≤ M' := (le_normalizer_pCoreOf 2 _).trans hM'le
  have hHH0 : H ≤ S.H0 H := le_sup_right
  have hXT : oTwoUpper H ⊔ T ≤ M' :=
    (sup_le (oTwoUpper_le H) hH.1.1).trans (hHH0.trans hH0M')
  rw [← hU.2 M' ⟨hM', hXT⟩]
  exact hH0M'

theorem UH_eq_conjClosure_oTwoUpper {H : Subgroup G} (hTH : T ≤ H) :
    S.UH H = conjClosure (quasithinOmegaOneCenter T) (oTwoUpper H) := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
    have hh' : h ∈ ((oTwoUpper H ⊔ T : Subgroup G) : Set G) := by
      rw [← eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl]; exact hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (hTH.trans (le_normalizer_oTwoUpper H))] at hh'
    obtain ⟨x, hx, t, ht, rfl⟩ := hh'
    have htz : t * z * t⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hz).2.1 t ht
      rw [this]; group
    have e : x * t * z * (x * t)⁻¹ = x * (t * z * t⁻¹) * x⁻¹ := by group
    rw [e, htz]
    exact mem_conjClosure hx hz
  · exact conjClosure_mono le_rfl (oTwoUpper_le H)

theorem L1_le_normalizer_UH {H : Subgroup G} (hTH : T ≤ H)
    (hH0L : S.H0 H ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hL1Z : S.L1 ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    S.L1 ≤ Subgroup.normalizer (S.UH H : Set G) := by
  intro l hl
  have hlH0 : l ∈ S.H0 H := by
    rw [S.H0_eq_sup hTH]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)
  have hlL := hH0L hlH0
  rw [S.UH_eq_conjClosure_oTwoUpper hTH]
  refine A4.mem_normalizer_of_conj_mem fun u hu => ?_
  have hle : conjClosure (quasithinOmegaOneCenter T) (oTwoUpper H) ≤
      (conjClosure (quasithinOmegaOneCenter T) (oTwoUpper H)).comap
        (MulAut.conj l).toMonoidHom := by
    refine conjClosure_le fun x hx z hz => ?_
    rw [Subgroup.mem_comap]
    have hlz : l * z * l⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp (hL1Z hl) z hz
      rw [← this]; group
    have e : (MulAut.conj l).toMonoidHom (x * z * x⁻¹) =
        (l * x * l⁻¹) * (l * z * l⁻¹) * (l * x * l⁻¹)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [e, hlz]
    exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hlL x).mp hx) hz
  exact hle hu

end Setting

end CFSG.Quasithin.H13.A5
