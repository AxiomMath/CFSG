module

public import CFSG.Quasithin.Background.D2Seventeen
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

theorem qhatStar_cases_of_indecomposable {X : Subgroup (MulAut V)} (hind : IsIndecomposablePair X)
    {V₁ V₂ : Subgroup V} (hd : IsDirectSum ⊤ V₁ V₂)
    (hcases : ∀ B ∈ QhatStar X,
      (B ≤ centSub V₂ ∧ commV B ≤ V₁) ∨ (B ≤ centSub V₁ ∧ commV B ≤ V₂)) :
    (∀ B ∈ QhatStar X, B ≤ centSub V₂ ∧ commV B ≤ V₁) ∨
      (∀ B ∈ QhatStar X, B ≤ centSub V₁ ∧ commV B ≤ V₂) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨B₁, hB₁, hB₁n⟩, ⟨B₂, hB₂, hB₂n⟩⟩ := hcon
  have hB₁2 : B₁ ≤ centSub V₁ ∧ commV B₁ ≤ V₂ := by
    rcases hcases B₁ hB₁ with h | h
    · exact absurd h.2 (hB₁n h.1)
    · exact h
  have hB₂1 : B₂ ≤ centSub V₂ ∧ commV B₂ ≤ V₁ := by
    rcases hcases B₂ hB₂ with h | h
    · exact h
    · exact absurd h.2 (hB₂n h.1)
  let Q₁ : Set (Subgroup (MulAut V)) := {B | B ∈ QhatStar X ∧ B ≤ centSub V₂ ∧ commV B ≤ V₁}
  let Q₂ : Set (Subgroup (MulAut V)) := {B | B ∈ QhatStar X ∧ B ≤ centSub V₁ ∧ commV B ≤ V₂}
  have hne : ∀ B ∈ QhatStar X, B ≠ ⊥ := by
    intro B hB
    obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hB
    exact hA2.ne_bot
  have hQ : QhatStar X = Q₁ ∪ Q₂ := by
    ext B
    constructor
    · intro hB
      rcases hcases B hB with h | h
      · exact Or.inl ⟨hB, h⟩
      · exact Or.inr ⟨hB, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint Q₁ Q₂ := by
    rw [Set.disjoint_left]
    rintro B ⟨hB, -, hc1⟩ ⟨-, -, hc2⟩
    have : commV B ≤ V₁ ⊓ V₂ := le_inf hc1 hc2
    rw [hd.2, le_bot_iff] at this
    apply hne B hB
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    ext v
    have hmem : b v * v⁻¹ ∈ commV B := Subgroup.subset_closure ⟨b, hb, v, rfl⟩
    rw [this, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hG₁ : (⨆ B ∈ Q₁, B) ≠ ⊥ := by
    intro h
    apply hne B₂ hB₂
    exact le_bot_iff.mp (h ▸ le_iSup₂_of_le B₂ ⟨hB₂, hB₂1⟩ le_rfl)
  have hG₂ : (⨆ B ∈ Q₂, B) ≠ ⊥ := by
    intro h
    apply hne B₁ hB₁
    exact le_bot_iff.mp (h ▸ le_iSup₂_of_le B₁ ⟨hB₁, hB₁2⟩ le_rfl)
  have hcomm1 : commV (⨆ B ∈ Q₁, B) ≤ V₁ := by
    have h1 := commV_iSup_le (fun B : Q₁ => (B : Subgroup (MulAut V)))
    have h2 : (⨆ B ∈ Q₁, B) = ⨆ B : Q₁, (B : Subgroup (MulAut V)) := by
      apply le_antisymm
      · exact iSup₂_le fun B hB => le_iSup (fun B : Q₁ => (B : Subgroup (MulAut V))) ⟨B, hB⟩
      · exact iSup_le fun B => le_iSup₂ (f := fun Z (_ : Z ∈ Q₁) => Z) B.1 B.2
    rw [h2]
    exact h1.trans (iSup_le fun B => B.2.2.2)
  have hcomm2 : commV (⨆ B ∈ Q₂, B) ≤ V₂ := by
    have h1 := commV_iSup_le (fun B : Q₂ => (B : Subgroup (MulAut V)))
    have h2 : (⨆ B ∈ Q₂, B) = ⨆ B : Q₂, (B : Subgroup (MulAut V)) := by
      apply le_antisymm
      · exact iSup₂_le fun B hB => le_iSup (fun B : Q₂ => (B : Subgroup (MulAut V))) ⟨B, hB⟩
      · exact iSup_le fun B => le_iSup₂ (f := fun Z (_ : Z ∈ Q₂) => Z) B.1 B.2
    rw [h2]
    exact h1.trans (iSup_le fun B => B.2.2.2)
  have hcen1 : commSub V₂ (⨆ B ∈ Q₁, B) = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro w hw g hg
    have : (⨆ B ∈ Q₁, B) ≤ centSub V₂ := iSup₂_le fun B hB => hB.2.1
    exact this hg w hw
  have hcen2 : commSub V₁ (⨆ B ∈ Q₂, B) = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro w hw g hg
    have : (⨆ B ∈ Q₂, B) ≤ centSub V₁ := iSup₂_le fun B hB => hB.2.1
    exact this hg w hw
  exact hind.2 ⟨⨆ B ∈ Q₁, B, ⨆ B ∈ Q₂, B, V₁, V₂, hG₁, hG₂, Q₁, Q₂, hQ, hdisj, rfl, rfl, hd,
    hcomm1, hcomm2, hcen1, hcen2⟩

theorem eq_one_of_fixes_vector (hV : ∀ v : V, v ^ 2 = 1) {X D : Subgroup (MulAut V)} {m : ℕ}
    (hk : m = 1 ∨ m = 2) (hD : D ∈ Xk X m) {g : MulAut V} (hcomm : ∀ y ∈ D, g * y = y * g)
    (hV₂ : ∀ v ∈ fixV D, g v = v) {v : V} (hv : v ∈ commV D) (hv1 : v ≠ 1) (hgv : g v = v) :
    g = 1 := by
  set F : Subgroup V := commV D ⊓ fixV (Subgroup.zpowers g) with hF
  have hFD : ∀ y ∈ D, ∀ f ∈ F, y f ∈ F := by
    intro y hy f hf
    refine ⟨?_, mem_fixV_zpowers_iff.mpr ?_⟩
    · have : y f = (y f * f⁻¹) * f := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨y, hy, f, rfl⟩) hf.1
    · have h1 : g f = f := mem_fixV_zpowers_iff.mp hf.2
      calc g (y f) = (g * y) f := rfl
        _ = (y * g) f := by rw [hcomm y hy]
        _ = y (g f) := rfl
        _ = y f := by rw [h1]
  have hF0 : F ≠ ⊥ := by
    intro h
    have : v ∈ F := ⟨hv, mem_fixV_zpowers_iff.mpr hgv⟩
    rw [h, Subgroup.mem_bot] at this
    exact hv1 this
  have hFeq := Xk_irreducible hV hk hD hFD inf_le_left hF0
  obtain ⟨hsup, -⟩ := Xk_decomp hV hD
  ext u
  have hu : u ∈ commV D ⊔ fixV D := by rw [hsup]; exact Subgroup.mem_top u
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
  have ha' : a ∈ F := by rw [hFeq]; exact ha
  rw [map_mul, mem_fixV_zpowers_iff.mp ha'.2, hV₂ c hc]
  rfl

theorem mul_mem_of_inverting (hV : ∀ v : V, v ^ 2 = 1) {X D : Subgroup (MulAut V)} {m : ℕ}
    (hm : m = 1 ∨ m = 2) (hD : D ∈ Xk X m) {b t : MulAut V} (hb : b ∈ TInv X)
    (hbm : rk (commV (Subgroup.zpowers b)) = m) (ht : t ∈ TInv X)
    (hbinv : ∀ y ∈ D, b * y * b⁻¹ = y⁻¹) (htinv : ∀ y ∈ D, t * y * t⁻¹ = y⁻¹)
    (hbV : ∀ v ∈ fixV D, b v = v) (htV : ∀ v ∈ fixV D, t v = v) : b * t ∈ D := by
  have : Fact (2 * m + 1).Prime := fact_prime_two_mul_add_one hm
  obtain ⟨d, hdD, hd1, hdz, hdord⟩ := exists_generator_of_prime_card hD.2.1
  have hDX : D ≤ X := hD.1.trans (fittingOf_le X)
  have hbX : b ∈ X := hb.1
  have htX : t ∈ X := ht.1
  have hb2 : b ^ 2 = 1 := hb.2.2.1
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hdinv_b := hbinv d hdD
  have hdinv_t := htinv d hdD
  have hcomm_d : ∀ g : MulAut V, g * d = d * g → ∀ y ∈ D, g * y = y * g := by
    intro g hg y hy
    rw [← hdz] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute g d from hg).zpow_right k).eq
  set c := b * t with hc
  have hcd : c * d = d * c := by
    have h1 : c * d * c⁻¹ = d := by
      calc c * d * c⁻¹ = b * (t * d * t⁻¹) * b⁻¹ := by rw [hc]; group
        _ = b * d⁻¹ * b⁻¹ := by rw [hdinv_t]
        _ = (b * d * b⁻¹)⁻¹ := by group
        _ = d := by rw [hdinv_b]; simp
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hcV : ∀ v ∈ fixV D, c v = v := by
    intro v hv
    show b (t v) = v
    rw [htV v hv, hbV v hv]
  have hbc : b * c * b⁻¹ = c⁻¹ := by
    calc b * c * b⁻¹ = (b * b) * t * b⁻¹ := by rw [hc]; group
      _ = t * b := by rw [hbb, one_mul, hbi]
      _ = c⁻¹ := by rw [hc, mul_inv_rev, hti, hbi]
  have hcX : c ∈ X := X.mul_mem hbX htX
  set G'' : Subgroup (MulAut V) :=
    Subgroup.centralizer ({d} : Set (MulAut V)) ⊓ centSub (fixV D) with hG
  have hcG : c ∈ G'' := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcd, hcV⟩
  have hdG : d ∈ G'' :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, fun v hv => hv d hdD⟩
  let Ω : Set V := {v | v ∈ commV D ∧ v ≠ 1}
  have hΩ : ∀ g ∈ G'', ∀ v ∈ Ω, g v ∈ Ω := by
    intro g hg v hv
    have hgcomm : ∀ y ∈ D, g * y = y * g :=
      hcomm_d g (Subgroup.mem_centralizer_singleton_iff.mp hg.1)
    have hstab : g ∈ stabSub (commV D) := by
      refine mem_stabSub_commV (fun p hp => ?_) (fun p hp => ?_)
      · rw [hgcomm p hp]; simpa using hp
      · have : g⁻¹ * p * g = p := by
          have := hgcomm p hp
          calc g⁻¹ * p * g = g⁻¹ * (p * g) := by group
            _ = g⁻¹ * (g * p) := by rw [← this]
            _ = p := by group
        rw [this]; exact hp
    refine ⟨(hstab v).mpr hv.1, fun h => hv.2 (g.injective (by rw [h, map_one]))⟩
  have hfree : ∀ g ∈ G'', ∀ v ∈ Ω, g v = v → g = 1 := by
    intro g hg v hv hgv
    exact eq_one_of_fixes_vector hV hm hD
      (hcomm_d g (Subgroup.mem_centralizer_singleton_iff.mp hg.1)) hg.2 hv.1 hv.2 hgv
  have hdvd : Nat.card G'' ∣ Nat.card Ω := card_dvd_card_of_free hΩ hfree
  have hΩcard : Nat.card Ω = 2 ^ (2 * m) - 1 := by
    have h1 := card_ne_one_add_one (commV D)
    have h2 : Nat.card (commV D) = 2 ^ (2 * m) := by rw [card_eq_two_pow hV, hD.2.2]
    have h3 : Nat.card Ω = Nat.card {c : V // c ∈ commV D ∧ c ≠ 1} := rfl
    omega
  rw [hΩcard] at hdvd
  have hdcard : 2 * m + 1 ∣ Nat.card G'' := by
    have := orderOf_dvd_natCard (⟨d, hdG⟩ : ↥G'')
    rwa [Subgroup.orderOf_mk, hdord] at this
  have hzG : Subgroup.zpowers d ≤ G'' := Subgroup.zpowers_le.mpr hdG
  have hfin : Nat.card G'' = 2 * m + 1 → b * t ∈ D := by
    intro hcard
    have heq : Subgroup.zpowers d = G'' :=
      Subgroup.eq_of_le_of_card_ge hzG (by rw [Nat.card_zpowers, hdord, hcard])
    rw [← hdz, heq]
    exact hcG
  rcases hm with rfl | rfl
  · have h3 : Nat.card G'' ∣ 3 := by simpa using hdvd
    exact hfin (Nat.dvd_antisymm h3 hdcard)
  · have h15 : Nat.card G'' ∣ 15 := by simpa using hdvd
    have h5 : 5 ∣ Nat.card G'' := by simpa using hdcard
    have hcases : Nat.card G'' = 5 ∨ Nat.card G'' = 15 := by
      obtain ⟨k, hk⟩ := h5
      rw [hk] at h15
      have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5)
        (by simpa using h15)
      rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h | h
      · left; rw [hk, h]
      · right; rw [hk, h]
    rcases hcases with h5' | h15'
    · exact hfin (by simpa using h5')
    · have hcord : orderOf c ∣ 15 := by
        have := orderOf_dvd_natCard (⟨c, hcG⟩ : ↥G'')
        rwa [Subgroup.orderOf_mk, h15'] at this
      have hno3 : ¬ 3 ∣ orderOf c := by
        intro h3
        have hco : orderOf c ≠ 0 := (orderOf_pos c).ne'
        set e := c ^ (orderOf c / 3) with he_def
        have he : orderOf e = 3 := orderOf_pow_orderOf_div hco h3
        have hec : Commute e d := (show Commute c d from hcd).pow_left _
        have hbe : b * e * b⁻¹ = e⁻¹ := by
          rw [he_def, ← conj_pow, hbc, inv_pow]
        have hx : orderOf (e * d) = 15 := by
          rw [hec.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [he, hdord]; norm_num), he, hdord]
        have hxX : e * d ∈ X := X.mul_mem (X.pow_mem hcX _) (hDX hdD)
        have hx1 : e * d ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hx
          omega
        have hinv : b * (e * d) * b⁻¹ = (e * d)⁻¹ := by
          calc b * (e * d) * b⁻¹ = (b * e * b⁻¹) * (b * d * b⁻¹) := by group
            _ = e⁻¹ * d⁻¹ := by rw [hbe, hdinv_b]
            _ = (e * d)⁻¹ := by rw [mul_inv_rev]; exact hec.inv_inv.eq
        have := (D2_11_2 hV hb hbm hxX hx1 (by rw [hx]; decide) hinv).1
        rw [hx] at this
        omega
      have hdiv : orderOf c = 1 ∨ orderOf c = 5 := by
        have hmem : orderOf c ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hcord, by norm_num⟩
        have hdivs : Nat.divisors 15 = {1, 3, 5, 15} := by decide
        rw [hdivs] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h | h | h
        · exact Or.inl h
        · exact absurd (by rw [h]) hno3
        · exact Or.inr h
        · exact absurd (by rw [h]; norm_num) hno3
      rcases hdiv with h1 | h5c
      · rw [orderOf_eq_one_iff.mp h1]
        exact D.one_mem
      ·
        let H₁ : Subgroup ↥G'' := Subgroup.zpowers ⟨c, hcG⟩
        let H₂ : Subgroup ↥G'' := Subgroup.zpowers ⟨d, hdG⟩
        have hH₁ : Nat.card H₁ = 5 := by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h5c]
        have hH₂ : Nat.card H₂ = 5 := by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hdord]
        have hfac : (Nat.card ↥G'').factorization 5 = 1 := by
          rw [h15']
          have : (15 : ℕ) = 3 * 5 := by norm_num
          rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
          simp [Nat.Prime.factorization (by norm_num : Nat.Prime 5),
            Nat.Prime.factorization (by norm_num : Nat.Prime 3)]
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        let P₁ : Sylow 5 ↥G'' := Sylow.ofCard H₁ (by rw [hH₁, hfac]; norm_num)
        let P₂ : Sylow 5 ↥G'' := Sylow.ofCard H₂ (by rw [hH₂, hfac]; norm_num)
        have hidx : H₁.index = 3 := by
          have := H₁.card_mul_index
          rw [hH₁, h15'] at this
          omega
        have hn1 : Nat.card (Sylow 5 ↥G'') % 5 = 1 := card_sylow_modEq_one 5 ↥G''
        have hn2 : Nat.card (Sylow 5 ↥G'') ∣ 3 := by
          have := Sylow.card_dvd_index P₁
          rwa [show (P₁ : Subgroup ↥G'') = H₁ from Sylow.coe_ofCard H₁ _, hidx] at this
        have hn3 : Nat.card (Sylow 5 ↥G'') = 1 := by
          have hle : Nat.card (Sylow 5 ↥G'') ≤ 3 := Nat.le_of_dvd (by norm_num) hn2
          interval_cases hnn : Nat.card (Sylow 5 ↥G'') <;> omega
        have hsub : Subsingleton (Sylow 5 ↥G'') := (Nat.card_eq_one_iff_unique.mp hn3).1
        have hP : P₁ = P₂ := Subsingleton.elim _ _
        have hHH : H₁ = H₂ := by
          have := congrArg (fun P : Sylow 5 ↥G'' => (P : Subgroup ↥G'')) hP
          simpa [P₁, P₂, Sylow.coe_ofCard] using this
        have hcH : (⟨c, hcG⟩ : ↥G'') ∈ H₂ := hHH ▸ Subgroup.mem_zpowers _
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcH
        have : d ^ k = c := congrArg Subtype.val hk
        rw [← this]
        exact D.zpow_mem hdD k

theorem nonempty_mulEquiv_dihedral {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {d t : G} (hd : orderOf d = p) (ht : orderOf t = 2) (hinv : t * d * t⁻¹ = d⁻¹)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers t) :
    Nonempty (G ≃* DihedralGroup p) := by
  have hpos : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let pw : ZMod p → G := fun i => d ^ i.val
  have pw_add : ∀ i j : ZMod p, pw (i + j) = pw i * pw j := by
    intro i j
    show d ^ (i + j).val = d ^ i.val * d ^ j.val
    rw [ZMod.val_add, ← pow_add]
    calc d ^ ((i.val + j.val) % p) = d ^ ((i.val + j.val) % orderOf d) := by rw [hd]
      _ = d ^ (i.val + j.val) := pow_mod_orderOf d _
  have pw_zero : pw 0 = 1 := by show d ^ (0 : ZMod p).val = 1; simp
  have pw_neg : ∀ i : ZMod p, pw (-i) = (pw i)⁻¹ := by
    intro i
    have := pw_add (-i) i
    have h0 : -i + i = 0 := neg_add_cancel i
    rw [h0, pw_zero] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have pw_conj : ∀ i : ZMod p, t * pw i * t⁻¹ = pw (-i) := by
    intro i
    show t * d ^ i.val * t⁻¹ = pw (-i)
    rw [← conj_pow, hinv, pw_neg, inv_pow]
  let f : DihedralGroup p →* G :=
    MonoidHom.mk' (fun x => match x with
      | DihedralGroup.r i => pw i
      | DihedralGroup.sr i => t * pw i) (by
      intro x y
      rcases x with i | i <;> rcases y with j | j
      · simp only [DihedralGroup.r_mul_r]
        exact pw_add i j
      · simp only [DihedralGroup.r_mul_sr]
        show t * pw (j - i) = pw i * (t * pw j)
        have h1 : pw i * t = t * pw (-i) := by
          have := pw_conj i
          rw [hti] at this
          calc pw i * t = t * (t * pw i * t) := by rw [← mul_assoc, ← mul_assoc, htt, one_mul]
            _ = t * pw (-i) := by rw [this]
        have e : j - i = -i + j := sub_eq_neg_add j i
        calc t * pw (j - i) = t * pw (-i + j) := by rw [e]
          _ = t * (pw (-i) * pw j) := by rw [pw_add]
          _ = (t * pw (-i)) * pw j := by rw [mul_assoc]
          _ = (pw i * t) * pw j := by rw [h1]
          _ = pw i * (t * pw j) := by rw [mul_assoc]
      · simp only [DihedralGroup.sr_mul_r]
        show t * pw (i + j) = t * pw i * pw j
        rw [mul_assoc, pw_add]
      · simp only [DihedralGroup.sr_mul_sr]
        show pw (j - i) = t * pw i * (t * pw j)
        have h1 : t * pw i * t = pw (-i) := by
          have := pw_conj i
          rwa [hti] at this
        have e : j - i = -i + j := sub_eq_neg_add j i
        calc pw (j - i) = pw (-i + j) := by rw [e]
          _ = pw (-i) * pw j := by rw [pw_add]
          _ = (t * pw i * t) * pw j := by rw [h1]
          _ = t * pw i * (t * pw j) := by rw [mul_assoc])
  have hfr : ∀ i : ZMod p, f (DihedralGroup.r i) = pw i := fun i => rfl
  have hfsr : ∀ i : ZMod p, f (DihedralGroup.sr i) = t * pw i := fun i => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases x with i | i
    · rw [hfr] at hx
      have h1 : orderOf d ∣ i.val := orderOf_dvd_of_pow_eq_one hx
      rw [hd] at h1
      have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
      have : i = 0 := (ZMod.val_eq_zero i).mp h2
      rw [this]
      rfl
    · exfalso
      rw [hfsr] at hx
      have h1 : t = (pw i)⁻¹ := eq_inv_of_mul_eq_one_left hx
      have hdp : d ^ p = 1 := by
        have := pow_orderOf_eq_one d
        rwa [hd] at this
      have h2 : t ^ p = 1 := by
        rw [h1, inv_pow]
        show ((d ^ i.val) ^ p)⁻¹ = 1
        rw [← pow_mul, mul_comm, pow_mul, hdp, one_pow, inv_one]
      have h3 : 2 ∣ p := ht ▸ orderOf_dvd_of_pow_eq_one h2
      exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp h3).symm
  have hsurj : Function.Surjective f := by
    have hdr : d ∈ f.range := ⟨DihedralGroup.r 1, by
      rw [hfr]; show d ^ (1 : ZMod p).val = d
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt, pow_one]⟩
    have htr : t ∈ f.range := ⟨DihedralGroup.sr 0, by rw [hfsr, show pw 0 = 1 from pw_zero, mul_one]⟩
    intro g
    have : g ∈ f.range := (sup_le (Subgroup.zpowers_le.mpr hdr) (Subgroup.zpowers_le.mpr htr)) (hgen g)
    exact this
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩


theorem exists_tinv_of_card_two {X B : Subgroup (MulAut V)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hB : B ∈ QhatStar X) (hcard : Nat.card B = 2) :
    ∃ t ∈ TInv X, Subgroup.zpowers t = B ∧ (rk (commV (Subgroup.zpowers t)) : ℚ) = r ∧ r ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r', hr', hr2, ⟨⟨hA2, hrAV⟩, hAk⟩, -⟩ := QhatStar_spec hB
  have hrr : r' = r := by
    have := hr.symm.trans hr'
    exact_mod_cast this.symm
  subst hrr
  obtain ⟨t, htB, ht1, htz, htord⟩ := exists_generator_of_prime_card hcard
  have hrk : rk B = 1 := by
    have : rk B = padicValNat 2 (Nat.card B) := rfl
    rw [this, hcard]; simp
  have hcomm : (rk (commV (Subgroup.zpowers t)) : ℚ) = r' := by
    have h := hrAV
    unfold rAV at h
    rw [hrk, ← htz, rkIdx_fixV_zpowers] at h
    simpa using h
  refine ⟨t, ⟨hA2.le htB, ht1, hA2.isElemAbelian2.2 t htB, ?_⟩, htz, hcomm, hr2⟩
  have : (rk (commV (Subgroup.zpowers t)) : ℚ) ≤ ((2 : ℕ) : ℚ) := by
    rw [hcomm]; exact_mod_cast hr2
  exact_mod_cast this

theorem tinv_dichotomy (hV : ∀ v : V, v ^ 2 = 1) {X D : Subgroup (MulAut V)} {m : ℕ}
    (hm : m = 1 ∨ m = 2) (hD : D ∈ Xk X m) {b : MulAut V} (hb : b ∈ TInv X)
    (hbm : rk (commV (Subgroup.zpowers b)) = m) :
    ((∀ y ∈ D, b * y * b⁻¹ = y⁻¹) ∧ ∀ v ∈ fixV D, b v = v) ∨
      ((∀ y ∈ D, b * y = y * b) ∧ ∀ v ∈ commV D, b v = v) := by
  have := fact_prime_two_mul_add_one hm
  have hDle : D ≤ Gk X m := le_iSup₂ (f := fun Y (_ : Y ∈ Xk X m) => Y) D hD
  rcases D2_12_3 hV hm hb hbm with ⟨hcomm, hcomm2⟩ | ⟨Y, hY, hinvY, -, -, hothers⟩
  · right
    refine ⟨fun y hy => (hcomm y (hDle hy)).symm, fun v hv => ?_⟩
    have h1 : v ∈ commV (Gk X m) := commV_mono hDle hv
    have h2 : commV (Gk X m) ≤ fixV (Subgroup.zpowers b) := commSub_eq_bot_iff.mp hcomm2
    exact mem_fixV_zpowers_iff.mp (h2 h1)
  · by_cases hYD : Y = D
    · subst hYD
      left
      refine ⟨hinvY, ?_⟩
      obtain ⟨x, hxY, hx1, hxz, hxord⟩ := exists_generator_of_prime_card hY.2.1
      have hxodd : Odd (orderOf x) := by rw [hxord]; exact ⟨m, rfl⟩
      have hxX : x ∈ X := fittingOf_le X (hY.1 hxY)
      have hrkx : rk (commV (Subgroup.zpowers x)) = 2 * rk (commV (Subgroup.zpowers b)) := by
        rw [hxz, hY.2.2, hbm]
      have h3 := D2_11_3 hV hb hxX hx1 hxodd (hinvY x hxY) hrkx
      rw [hxz] at h3
      intro v hv
      exact mem_fixV_zpowers_iff.mp (commSub_eq_bot_iff.mp h3.2.1 hv)
    · right
      obtain ⟨h1, h2⟩ := hothers D hD (fun h => hYD h.symm)
      exact ⟨fun y hy => h1 y hy, fun v hv => h2 v hv⟩


omit [Finite V] in
theorem commV_zpowers_le_of_forall {b : MulAut V} (hb2 : b ^ 2 = 1) {W : Subgroup V}
    (h : ∀ v : V, b v * v⁻¹ ∈ W) : commV (Subgroup.zpowers b) ≤ W := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases zpow_involution hb2 k with e | e
  · rw [e]; simp
  · rw [e]; exact h v

omit [Finite V] in
theorem kindI_of_inverts {D : Subgroup (MulAut V)} (hsup : commV D ⊔ fixV D = ⊤) {b : MulAut V}
    (hb2 : b ^ 2 = 1) (hinv : ∀ y ∈ D, b * y * b⁻¹ = y⁻¹) (hfix : ∀ v ∈ fixV D, b v = v) :
    Subgroup.zpowers b ≤ centSub (fixV D) ∧ commV (Subgroup.zpowers b) ≤ commV D := by
  refine ⟨Subgroup.zpowers_le.mpr (fun v hv => hfix v hv), ?_⟩
  apply commV_zpowers_le_of_forall hb2
  intro v
  have hv : v ∈ commV D ⊔ fixV D := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  have h1 : b v₁ ∈ commV D :=
    commV_smul_mem (fun p hp => by rw [hinv p hp]; exact D.inv_mem hp) hv₁
  rw [map_mul, hfix v₂ hv₂, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  exact (commV D).mul_mem h1 ((commV D).inv_mem hv₁)

omit [Finite V] in
theorem kindII_of_commutes {D : Subgroup (MulAut V)} (hsup : commV D ⊔ fixV D = ⊤) {b : MulAut V}
    (hb2 : b ^ 2 = 1) (hcomm : ∀ y ∈ D, b * y = y * b) (hfix : ∀ v ∈ commV D, b v = v) :
    Subgroup.zpowers b ≤ centSub (commV D) ∧ commV (Subgroup.zpowers b) ≤ fixV D := by
  refine ⟨Subgroup.zpowers_le.mpr (fun v hv => hfix v hv), ?_⟩
  apply commV_zpowers_le_of_forall hb2
  intro v
  have hv : v ∈ commV D ⊔ fixV D := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  have h1 : b v₂ ∈ fixV D := by
    refine fixV_smul_mem (fun p hp => ?_) hv₂
    have : b⁻¹ * p * b = p := by
      calc b⁻¹ * p * b = b⁻¹ * (p * b) := by group
        _ = b⁻¹ * (b * p) := by rw [← hcomm p hp]
        _ = p := by group
    rw [this]; exact hp
  rw [map_mul, hfix v₁ hv₁, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  exact (fixV D).mul_mem h1 ((fixV D).inv_mem hv₂)


theorem D2_dihedral (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (h : D217Hyp X r) (hcyc : ∀ B ∈ QhatStar X, Nat.card B = 2) (hA : A ∈ QhatStar X)
    {m : ℕ} (hm : m = 1 ∨ m = 2) (hr : r = m) {p : ℕ} [Fact p.Prime] (hp : p = 2 * m + 1)
    (hne : ⁅pCoreOf p X, A⁆ ≠ ⊥) :
    Nonempty (↥X ≃* DihedralGroup p) ∧ rk V = 2 * m := by
  have hp2 : p ≠ 2 := by omega
  have hfp := fact_prime_two_mul_add_one hm
  obtain ⟨t, ht, htz, htr, -⟩ := exists_tinv_of_card_two h.qhat hA (hcyc A hA)
  have htm : rk (commV (Subgroup.zpowers t)) = m := by
    rw [hr] at htr; exact_mod_cast htr
  have hact : ∃ y ∈ pCoreOf p X, t * y ≠ y * t := by
    obtain ⟨y, hy, a, ha, hne'⟩ := commutator_ne_bot_iff.mp hne
    rw [← htz] at ha
    by_contra hcon
    push Not at hcon
    apply hne'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute t y from hcon y hy).zpow_left k).eq
  have hPX := pCoreOf_le p X
  have hP := pCoreOf_isPGroup p X
  have hn : ∀ x ∈ X, ∀ g ∈ pCoreOf p X, x * g * x⁻¹ ∈ pCoreOf p X := fun x hx g hg =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p X hx) g).mp hg
  obtain ⟨-, -, hcore⟩ := core_involution hV ht hp2 hPX hP hn hact
  rw [htm] at hcore
  obtain ⟨D, hD, hinvD, -, -, -⟩ := hcore (by rw [hp])
  obtain ⟨hsup, hinf⟩ := Xk_decomp hV hD
  have hdirect : IsDirectSum ⊤ (commV D) (fixV D) := ⟨hsup, hinf⟩
  have hDX : D ≤ X := hD.1.trans (fittingOf_le X)
  have hcases : ∀ B ∈ QhatStar X,
      (B ≤ centSub (fixV D) ∧ commV B ≤ commV D) ∨
        (B ≤ centSub (commV D) ∧ commV B ≤ fixV D) := by
    intro B hB
    obtain ⟨b, hb, hbz, hbr, -⟩ := exists_tinv_of_card_two h.qhat hB (hcyc B hB)
    have hbm : rk (commV (Subgroup.zpowers b)) = m := by
      rw [hr] at hbr; exact_mod_cast hbr
    subst hbz
    rcases tinv_dichotomy hV hm hD hb hbm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (kindI_of_inverts hsup hb.2.2.1 h1 h2)
    · exact Or.inr (kindII_of_commutes hsup hb.2.2.1 h1 h2)
  obtain ⟨d, hdD, hd1, hdz, hdord⟩ := exists_generator_of_prime_card hD.2.1
  have htA : t ∈ A := htz ▸ Subgroup.mem_zpowers t
  rcases qhatStar_cases_of_indecomposable h.indecomposable hdirect hcases with hall | hall
  ·
    have hmemb : ∀ B ∈ QhatStar X, ∃ b ∈ TInv X, Subgroup.zpowers b = B ∧
        rk (commV (Subgroup.zpowers b)) = m ∧ (∀ y ∈ D, b * y * b⁻¹ = y⁻¹) ∧
          ∀ v ∈ fixV D, b v = v := by
      intro B hB
      obtain ⟨b, hb, hbz, hbr, -⟩ := exists_tinv_of_card_two h.qhat hB (hcyc B hB)
      have hbm : rk (commV (Subgroup.zpowers b)) = m := by
        rw [hr] at hbr; exact_mod_cast hbr
      rcases tinv_dichotomy hV hm hD hb hbm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨b, hb, hbz, hbm, h1, h2⟩
      · exfalso
        have hbB : b ∈ B := hbz ▸ Subgroup.mem_zpowers b
        have hfix2 : ∀ v ∈ fixV D, b v = v := fun v hv => (hall B hB).1 hbB v hv
        apply hb.2.1
        ext v
        have hv : v ∈ commV D ⊔ fixV D := by rw [hsup]; exact Subgroup.mem_top v
        obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
        rw [map_mul, h2 v₁ hv₁, hfix2 v₂ hv₂]
        rfl
    have htV : ∀ v ∈ fixV D, t v = v := fun v hv => (hall A hA).1 htA v hv
    have hAX : A ≤ X := by
      obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
      exact hA2.le
    have hXle : X ≤ D ⊔ A := by
      rw [h.jhat]
      refine iSup₂_le fun B hB => ?_
      obtain ⟨b, hb, hbz, hbm, hbinv, hbV⟩ := hmemb B hB
      rw [← hbz]
      refine Subgroup.zpowers_le.mpr ?_
      have hbt : b * t ∈ D := mul_mem_of_inverting hV hm hD hb hbm ht hbinv hinvD hbV htV
      have : (b * t) * t⁻¹ ∈ D ⊔ A := Subgroup.mul_mem_sup hbt (A.inv_mem htA)
      simpa using this
    have hfixD : fixV D = ⊥ := by
      refine (D2_20 hV h).2 (fixV D) fun B hB => ?_
      obtain ⟨b, hb, hbz, -, -, hbV⟩ := hmemb B hB
      rw [← hbz]
      exact fun v hv => mem_fixV_zpowers_iff.mpr (hbV v hv)
    have hcommtop : commV D = ⊤ := by
      rw [hfixD, sup_bot_eq] at hsup
      exact hsup
    refine ⟨?_, ?_⟩
    · have hdX : d ∈ X := hDX hdD
      have htX : t ∈ X := ht.1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hd'ord : orderOf (⟨d, hdX⟩ : ↥X) = p := by
        rw [Subgroup.orderOf_mk, hdord, hp]
      have ht'ord : orderOf (⟨t, htX⟩ : ↥X) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime ht.2.2.1 ht.2.1
      have hinv' : (⟨t, htX⟩ : ↥X) * ⟨d, hdX⟩ * (⟨t, htX⟩ : ↥X)⁻¹ = (⟨d, hdX⟩ : ↥X)⁻¹ :=
        Subtype.ext (hinvD d hdD)
      refine nonempty_mulEquiv_dihedral hp2 hd'ord ht'ord hinv' fun g => ?_
      have hmap : (Subgroup.zpowers (⟨d, hdX⟩ : ↥X) ⊔ Subgroup.zpowers (⟨t, htX⟩ : ↥X)).map
          X.subtype = Subgroup.zpowers d ⊔ Subgroup.zpowers t := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      have hgmem : (g : MulAut V) ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers t := by
        rw [hdz, htz]; exact hXle g.2
      rw [← hmap] at hgmem
      exact (Subgroup.mem_map_iff_mem X.subtype_injective).mp hgmem
    · have : rk V = rk (commV D) := by rw [hcommtop, rk_top]
      rw [this, hD.2.2]
  · exfalso
    have htfix : ∀ w ∈ commV D, t w = w := fun w hw => (hall A hA).1 htA w hw
    have hdd : d * d ∈ D := D.mul_mem hdD hdD
    have hfix : ∀ w ∈ commV D, (d * d) w = w := by
      intro w hw
      have hw' : d w ∈ commV D :=
        commV_smul_mem (fun q hq => D.mul_mem (D.mul_mem hdD hq) (D.inv_mem hdD)) hw
      have h1 : t⁻¹ w = w := by
        calc t⁻¹ w = t⁻¹ (t w) := by rw [htfix w hw]
          _ = w := by simp
      have h2 : (t * d * t⁻¹) w = d w := by
        show t (d (t⁻¹ w)) = d w
        rw [h1]
        exact htfix _ hw'
      rw [hinvD d hdD] at h2
      show d (d w) = w
      have h3 : d⁻¹ w = d w := h2
      calc d (d w) = d (d⁻¹ w) := by rw [h3]
        _ = w := by simp
    have hd2 : d * d = 1 := Xk_faithful hV hD hdd hfix
    have hdvd : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd2)
    rw [hdord] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega


theorem D2_23 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ} (h : D217Hyp X r)
    (hcyc : ∀ B ∈ QhatStar X, Nat.card B = 2) (hA : A ∈ QhatStar X)
    (hne : ⁅pCoreOf 5 X, A⁆ ≠ ⊥) :
    Nonempty (↥X ≃* DihedralGroup 5) ∧ rk V = 4 ∧ r = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, h5, -⟩ := D2_13 hV h.qhat hA (p := 5) (by norm_num) rfl hne
  obtain ⟨hr2, -⟩ := h5 rfl
  obtain ⟨hiso, hrk⟩ := D2_dihedral hV h hcyc hA (m := 2) (Or.inr rfl) (by rw [hr2]; norm_num)
    (p := 5) rfl hne
  exact ⟨hiso, hrk, hr2⟩

theorem D2_24 (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {r : ℚ} (h : D217Hyp X r)
    (hcyc : ∀ B ∈ QhatStar X, Nat.card B = 2) (hr : r = 1) :
    Nonempty (↥X ≃* DihedralGroup 3) ∧ rk V = 2 := by
  obtain ⟨A, hA⟩ := QhatStar_nonempty h.qhat h.le_two
  obtain ⟨⟨p, hp, hp2, hne⟩, -⟩ := D2_18 hV h hA (hcyc A hA)
  have : Fact p.Prime := ⟨hp⟩
  have hrk : rk A = 1 := by
    have : rk A = padicValNat 2 (Nat.card A) := rfl
    rw [this, hcyc A hA]; simp
  obtain ⟨-, -, h3, -⟩ := D2_13 hV h.qhat hA hp2 rfl hne
  obtain ⟨hp3, -⟩ := (h3 hrk).2 hr
  subst hp3
  obtain ⟨hiso, hrk2⟩ := D2_dihedral hV h hcyc hA (m := 1) (Or.inl rfl) (by rw [hr]; norm_num)
    (p := 3) rfl hne
  exact ⟨hiso, hrk2⟩

end CFSG.Quasithin
