module

public import CFSG.Quasithin.Background.D2Tools
public import CFSG.Quasithin.Background.D2Cyclic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem Gk_le_fittingOf (X : Subgroup (MulAut V)) (k : ℕ) : Gk X k ≤ fittingOf X :=
  iSup₂_le fun _ hY => hY.1

theorem odd_card_Gk {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥) (k : ℕ) :
    Odd (Nat.card (Gk X k)) := by
  have hodd := odd_card_fittingOf hO2
  have hdvd : Nat.card (Gk X k) ∣ Nat.card (fittingOf X) :=
    Subgroup.card_dvd_of_le (Gk_le_fittingOf X k)
  exact Odd.of_dvd_nat hodd hdvd

theorem Gk_decomp (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥)
    (k : ℕ) : commV (Gk X k) ⊔ fixV (Gk X k) = ⊤ ∧ commV (Gk X k) ⊓ fixV (Gk X k) = ⊥ := by
  obtain ⟨h1, h2⟩ := coprime_decomp (odd_card_Gk hO2 k) hV (W := ⊤)
    (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at h1 h2
  exact ⟨h1, h2⟩

theorem conj_mem_Gk {X : Subgroup (MulAut V)} {k : ℕ} {t y : MulAut V} (ht : t ∈ X)
    (hy : y ∈ Gk X k) : t * y * t⁻¹ ∈ Gk X k := by
  have hle : Gk X k ≤ (Gk X k).comap (MulAut.conj t).toMonoidHom := by
    refine iSup₂_le fun Y hY y hy => ?_
    have : t * y * t⁻¹ ∈ conjBy t Y := mem_conjBy_of_mem hy
    have h2 : conjBy t Y ∈ Xk X k := conjBy_mem_Xk ht hY
    exact le_iSup₂ (f := fun Z (_ : Z ∈ Xk X k) => Z) _ h2 this
  have := hle hy
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using this

theorem stab_commV_Gk {X : Subgroup (MulAut V)} {k : ℕ} {g : MulAut V} (hg : g ∈ X) :
    g ∈ stabSub (commV (Gk X k)) ∧ g ∈ stabSub (fixV (Gk X k)) := by
  have h1 : ∀ p ∈ Gk X k, g * p * g⁻¹ ∈ Gk X k := fun p hp => conj_mem_Gk hg hp
  have h2 : ∀ p ∈ Gk X k, g⁻¹ * p * g ∈ Gk X k := fun p hp => by
    have := conj_mem_Gk (X.inv_mem hg) hp
    simpa using this
  exact ⟨mem_stabSub_commV h1 h2, mem_stabSub_fixV h1 h2⟩

theorem rk_commSub_inverted (hV : ∀ v : V, v ^ 2 = 1) {X P : Subgroup (MulAut V)} {t : MulAut V}
    (ht : t ∈ TInv X) (hP : P ∈ Xk X 1) (hinv : ∀ y ∈ P, t * y * t⁻¹ = y⁻¹) :
    rk (commSub (commV P) (Subgroup.zpowers t)) = 1 := by
  have := fact_prime_two_mul_add_one (k := 1) (Or.inl rfl)
  obtain ⟨x, hxP, hx1, hxz, hxord⟩ := exists_generator_of_prime_card hP.2.1
  have hodd : Odd (orderOf x) := by rw [hxord]; exact ⟨1, rfl⟩
  have hm : rk (commV (Subgroup.zpowers t)) ≤ 2 := ht.2.2.2
  obtain ⟨h1, -⟩ := d2_11_core hV ht.2.2.1 hm hx1 hodd (hinv x hxP)
  rw [hxz, hP.2.2] at h1
  omega

theorem exists_pow_eq_on_commV (hV : ∀ v : V, v ^ 2 = 1) {X P : Subgroup (MulAut V)}
    (hP : P ∈ Xk X 1) {g : MulAut V} (hg : ∀ y ∈ P, g * y = y * g)
    (hstab : ∀ v ∈ commV P, g v ∈ commV P) :
    ∃ p ∈ P, ∀ v ∈ commV P, g v = p v := by
  classical
  have := fact_prime_two_mul_add_one (k := 1) (Or.inl rfl)
  obtain ⟨y, hyP, hy1, hyz, hyord⟩ := exists_generator_of_prime_card hP.2.1
  obtain ⟨-, hinf⟩ := Xk_decomp hV hP
  have hy3 : ∀ v : V, y (y (y v)) = v := by
    intro v
    have h : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hyord] at this
      simpa using this
    have := congrArg (fun g : MulAut V => g v) h
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcard4 : Nat.card (commV P) = 4 := by
    rw [card_eq_two_pow hV, hP.2.2]; norm_num
  have hinvP : ∀ q ∈ P, y * q * y⁻¹ ∈ P := fun q hq =>
    P.mul_mem (P.mul_mem hyP hq) (P.inv_mem hyP)
  have hfix : ∀ v ∈ commV P, y v = v → v = 1 := by
    intro v hv hyv
    have hvfix : v ∈ fixV P := by
      rw [← hyz]; exact mem_fixV_zpowers_iff.mpr hyv
    have : v ∈ commV P ⊓ fixV P := ⟨hv, hvfix⟩
    rw [hinf] at this
    exact this
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v₀ ∈ commV P, v₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card (commV P) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩, ⟨1⟩⟩
    omega
  have hyv : y v₀ ∈ commV P := commV_smul_mem hinvP hv₀
  have hyyv : y (y v₀) ∈ commV P := commV_smul_mem hinvP hyv
  have hne1 : y v₀ ≠ v₀ := fun h => hv₀1 (hfix v₀ hv₀ h)
  have hne2 : y (y v₀) ≠ v₀ := by
    intro h
    apply hne1
    have := hy3 v₀
    rw [h] at this
    exact this
  have hne3 : y (y v₀) ≠ y v₀ := fun h => hne1 (y.injective h)
  have hne1' : y v₀ ≠ 1 := fun h => hv₀1 (y.injective (by rw [h, map_one]))
  have hne2' : y (y v₀) ≠ 1 := fun h => hne1' (y.injective (by rw [h, map_one]))
  have hnz : ∀ u ∈ commV P, u ≠ 1 → u = v₀ ∨ u = y v₀ ∨ u = y (y v₀) := by
    intro u hu hu1
    have : Fintype {c : V // c ∈ commV P ∧ c ≠ 1} := Fintype.ofFinite _
    have hc : Fintype.card {c : V // c ∈ commV P ∧ c ≠ 1} = 3 := by
      have h1 := card_ne_one_add_one (commV P)
      rw [Nat.card_eq_fintype_card] at h1
      omega
    set a : {c : V // c ∈ commV P ∧ c ≠ 1} := ⟨v₀, hv₀, hv₀1⟩
    set b : {c : V // c ∈ commV P ∧ c ≠ 1} := ⟨y v₀, hyv, hne1'⟩
    set d : {c : V // c ∈ commV P ∧ c ≠ 1} := ⟨y (y v₀), hyyv, hne2'⟩
    have hab : a ≠ b := fun h => hne1 (congrArg Subtype.val h).symm
    have had : a ≠ d := fun h => hne2 (congrArg Subtype.val h).symm
    have hbd : b ≠ d := fun h => hne3 (congrArg Subtype.val h).symm
    have hcardS : ({a, b, d} : Finset {c : V // c ∈ commV P ∧ c ≠ 1}).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, had]),
        Finset.card_insert_of_notMem (by simp [hbd]), Finset.card_singleton]
    have hS : ({a, b, d} : Finset {c : V // c ∈ commV P ∧ c ≠ 1}) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcardS, hc])
    have hmem : (⟨u, hu, hu1⟩ : {c : V // c ∈ commV P ∧ c ≠ 1}) ∈
        ({a, b, d} : Finset {c : V // c ∈ commV P ∧ c ≠ 1}) := by
      rw [hS]; exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hgv₀ : g v₀ ∈ commV P := hstab v₀ hv₀
  have hgv₀1 : g v₀ ≠ 1 := fun h => hv₀1 (g.injective (by rw [h, map_one]))
  have hpow : ∃ p ∈ P, g v₀ = p v₀ := by
    rcases hnz _ hgv₀ hgv₀1 with h | h | h
    · exact ⟨1, P.one_mem, by simpa using h⟩
    · exact ⟨y, hyP, h⟩
    · exact ⟨y * y, P.mul_mem hyP hyP, by simpa [MulAut.mul_apply] using h⟩
  obtain ⟨p, hpP, hp⟩ := hpow
  have hpy : ∀ w : V, y (p w) = p (y w) := by
    intro w
    have hc : p * y = y * p := by
      rw [← hyz] at hpP
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hpP
      exact ((Commute.refl y).zpow_left k).eq
    calc y (p w) = (y * p) w := rfl
      _ = (p * y) w := by rw [hc]
      _ = p (y w) := rfl
  have hgy : ∀ w : V, g (y w) = y (g w) := by
    intro w
    calc g (y w) = (g * y) w := rfl
      _ = (y * g) w := by rw [hg y hyP]
      _ = y (g w) := rfl
  refine ⟨p, hpP, fun v hv => ?_⟩
  by_cases hv1 : v = 1
  · rw [hv1, map_one, map_one]
  rcases hnz v hv hv1 with rfl | rfl | rfl
  · exact hp
  · rw [hgy, hp, hpy]
  · rw [hgy, hgy, hp, hpy, hpy]

omit [Finite V] in
theorem invariant_zpowers {t : MulAut V} (ht2 : t ^ 2 = 1) {U : Subgroup V}
    (hU : ∀ u ∈ U, t u ∈ U) : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ U, x u ∈ U := by
  intro x hx u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases zpow_involution ht2 k with e | e
  · rw [e]; simpa using hu
  · rw [e]; exact hU u hu

theorem fixes_W_of_swap (hV : ∀ v : V, v ^ 2 = 1) {X Y₁ Y₂ : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥)
    {t : MulAut V} (ht : t ∈ TInv X) (hY₁ : Y₁ ∈ Xk X 1) (hY₂ : Y₂ ∈ Xk X 1)
    (h12 : conjBy t Y₁ = Y₂) (h21 : conjBy t Y₂ = Y₁)
    (hcomm : commV (Subgroup.zpowers t) =
      commSub (commV Y₁ ⊔ commV Y₂) (Subgroup.zpowers t)) :
    ∀ w ∈ fixV (Gk X 1), t w = w := by
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have e12 : commV Y₂ = (commV Y₁).map t.toMonoidHom := by rw [← h12, commV_conjBy]
  have e21 : commV Y₁ = (commV Y₂).map t.toMonoidHom := by rw [← h21, commV_conjBy]
  have hS : ∀ s ∈ commV Y₁ ⊔ commV Y₂, t s ∈ commV Y₁ ⊔ commV Y₂ := by
    intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Subgroup.mem_sup.mp hs
    rw [map_mul]
    have h1 : t s₁ ∈ commV Y₂ := by rw [e12]; exact ⟨s₁, hs₁, rfl⟩
    have h2 : t s₂ ∈ commV Y₁ := by rw [e21]; exact ⟨s₂, hs₂, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)
  have hSle : commV (Subgroup.zpowers t) ≤ commV Y₁ ⊔ commV Y₂ := by
    rw [hcomm]
    exact commSub_le_of_invariant (invariant_zpowers ht2 hS)
  have hle : commV Y₁ ⊔ commV Y₂ ≤ commV (Gk X 1) :=
    sup_le (commV_mono (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) Y₁ hY₁))
      (commV_mono (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) Y₂ hY₂))
  obtain ⟨-, hinf⟩ := Gk_decomp hV hO2 1
  obtain ⟨-, hstabW⟩ := stab_commV_Gk (k := 1) ht.1
  intro w hw
  have htw : t w ∈ fixV (Gk X 1) := (hstabW w).mpr hw
  have hmem : t w * w⁻¹ ∈ commV (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, rfl⟩
  have h1 : t w * w⁻¹ ∈ commV (Gk X 1) ⊓ fixV (Gk X 1) :=
    ⟨hle (hSle hmem), (fixV (Gk X 1)).mul_mem htw ((fixV (Gk X 1)).inv_mem hw)⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem fixes_W_of_two_inverted (hV : ∀ v : V, v ^ 2 = 1) {X P₀ P₁ : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 X = ⊥) {t : MulAut V} (ht : t ∈ TInv X)
    (hrk : rk (commV (Subgroup.zpowers t)) = 2) (hP₀ : P₀ ∈ Xk X 1) (hP₁ : P₁ ∈ Xk X 1)
    (hne : P₁ ≠ P₀) (hn₀ : ∀ y ∈ P₀, t * y * t⁻¹ = y⁻¹) (hn₁ : ∀ y ∈ P₁, t * y * t⁻¹ = y⁻¹) :
    ∀ w ∈ fixV (Gk X 1), t w = w := by
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  obtain ⟨hsup0, hinf0⟩ := Xk_decomp hV hP₀
  have hnorm : ∀ P : Subgroup (MulAut V), (∀ y ∈ P, t * y * t⁻¹ = y⁻¹) →
      ∀ y ∈ P, t * y * t⁻¹ ∈ P := by
    intro P hP y hy
    rw [hP y hy]
    exact P.inv_mem hy
  have hnorm' : ∀ P : Subgroup (MulAut V), (∀ y ∈ P, t * y * t⁻¹ = y⁻¹) →
      ∀ y ∈ P, t⁻¹ * y * t ∈ P := by
    intro P hP y hy
    rw [htinv]
    exact hnorm P hP y hy |> fun h => by rwa [htinv] at h
  have hV₀t : ∀ u ∈ commV P₀, t u ∈ commV P₀ := fun u hu => commV_smul_mem (hnorm P₀ hn₀) hu
  have hF₀t : ∀ u ∈ fixV P₀, t u ∈ fixV P₀ := fun u hu => fixV_smul_mem (hnorm' P₀ hn₀) hu
  have hd : IsDirectSum ⊤ (commV P₀) (fixV P₀) := ⟨hsup0, hinf0⟩
  have hrk_sum := rk_commSub_isDirectSum (g := t) hd (invariant_zpowers ht2 hV₀t)
    (invariant_zpowers ht2 hF₀t)
  rw [← commV_eq_commSub, hrk, rk_commSub_inverted hV ht hP₀ hn₀] at hrk_sum
  have hV₁le : commV P₁ ≤ fixV P₀ := by
    intro w hw y hy
    exact Xk_centralizes hV hk hP₁ hP₀ hne (Xk_commute hV hk P₁ hP₁ P₀ hP₀) y hy w hw
  have hV₁t : ∀ u ∈ commV P₁, t u ∈ commV P₁ := fun u hu => commV_smul_mem (hnorm P₁ hn₁) hu
  have hrk₁ := rk_commSub_inverted hV ht hP₁ hn₁
  have hle₁ : commSub (commV P₁) (Subgroup.zpowers t) ≤ commSub (fixV P₀) (Subgroup.zpowers t) :=
    commSub_mono hV₁le le_rfl
  have heq : commSub (commV P₁) (Subgroup.zpowers t) = commSub (fixV P₀) (Subgroup.zpowers t) :=
    eq_of_le_of_rk_le hV hle₁ (by omega)
  obtain ⟨-, hinf⟩ := Gk_decomp hV hO2 1
  obtain ⟨-, hstabW⟩ := stab_commV_Gk (k := 1) ht.1
  have hP₀le : P₀ ≤ Gk X 1 := le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) P₀ hP₀
  intro w hw
  have hwF : w ∈ fixV P₀ := fixV_anti hP₀le hw
  have htw : t w ∈ fixV (Gk X 1) := (hstabW w).mpr hw
  have hmem : t w * w⁻¹ ∈ commSub (fixV P₀) (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, hwF, rfl⟩
  rw [← heq] at hmem
  have hmem1 : t w * w⁻¹ ∈ commV P₁ :=
    commSub_le_of_invariant (invariant_zpowers ht2 hV₁t) hmem
  have hP₁le : commV P₁ ≤ commV (Gk X 1) :=
    commV_mono (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) P₁ hP₁)
  have h1 : t w * w⁻¹ ∈ commV (Gk X 1) ⊓ fixV (Gk X 1) :=
    ⟨hP₁le hmem1, (fixV (Gk X 1)).mul_mem htw ((fixV (Gk X 1)).inv_mem hw)⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem eq_of_ne_one_of_rk_le_one (hV : ∀ v : V, v ^ 2 = 1) {F : Subgroup V} (hF : rk F ≤ 1)
    {a b : V} (ha : a ∈ F) (hb : b ∈ F) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hne
  classical
  have hcard : Nat.card F ≤ 2 := by
    rw [card_eq_two_pow hV F]
    calc 2 ^ rk F ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hF
      _ = 2 := by norm_num
  have : Fintype F := Fintype.ofFinite F
  have h3 : 2 < Nat.card F := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.two_lt_card_iff]
    refine ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro h; exact ha1 (congrArg Subtype.val h).symm
    · intro h; exact hb1 (congrArg Subtype.val h).symm
    · intro h; exact hne (congrArg Subtype.val h)
  omega

theorem conjBy_eq_of_inverted {X P : Subgroup (MulAut V)} {t x : MulAut V} (hxX : x ∈ X)
    (ht2 : t ^ 2 = 1) (hx3 : x ^ 3 = 1) (htx : t * x * t⁻¹ = x⁻¹)
    (hnorm : ∀ Q ∈ Xk X 1, t ∈ Subgroup.normalizer (Q : Set (MulAut V))) (hP : P ∈ Xk X 1) :
    conjBy x P = P := by
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hQ : conjBy x⁻¹ P ∈ Xk X 1 := conjBy_mem_Xk (X.inv_mem hxX) hP
  have hQt : conjBy t (conjBy x⁻¹ P) = conjBy x⁻¹ P := conjBy_eq_of_mem_normalizer (hnorm _ hQ)
  have hPt : conjBy t⁻¹ P = P := by rw [htinv]; exact conjBy_eq_of_mem_normalizer (hnorm _ hP)
  have htx' : t * x⁻¹ * t⁻¹ = x := by
    have : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [this, htx, inv_inv]
  have hxx : conjBy (x * x) P = P := by
    have e : x * x = x * (t * (x⁻¹ * t⁻¹)) := by
      calc x * x = x * (t * x⁻¹ * t⁻¹) := by rw [htx']
        _ = x * (t * (x⁻¹ * t⁻¹)) := by group
    rw [e, ← conjBy_conjBy, ← conjBy_conjBy, ← conjBy_conjBy, hPt, hQt, conjBy_conjBy,
      mul_inv_cancel, conjBy_one]
  have e4 : x = (x * x) * (x * x) := by
    have : x ^ 4 = x := by
      calc x ^ 4 = x ^ 3 * x := by rw [pow_succ]
        _ = x := by rw [hx3, one_mul]
    calc x = x ^ 4 := this.symm
      _ = x ^ 2 * x ^ 2 := by rw [← pow_add]
      _ = (x * x) * (x * x) := by rw [pow_two]
  conv_lhs => rw [e4]
  rw [← conjBy_conjBy, hxx, hxx]

omit [Finite V] in
theorem fixes_commV_of_inverted {P : Subgroup (MulAut V)} {t x : MulAut V} (ht2 : t ^ 2 = 1)
    (hx3 : x ^ 3 = 1) (htx : t * x * t⁻¹ = x⁻¹) (hxP : ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    (htP : ∀ v ∈ commV P, t v = v) : ∀ v ∈ commV P, x v = v := by
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  intro v hv
  have hxv : x v ∈ commV P := commV_smul_mem hxP hv
  have h1 : (t * x * t⁻¹) v = x v := by
    show t (x (t⁻¹ v)) = x v
    rw [htinv, htP v hv]
    exact htP _ hxv
  rw [htx] at h1
  have h2 : x (x v) = v := by
    have := congrArg (fun u => x u) h1
    simpa using this.symm
  have h3 : x (x (x v)) = v := by
    have := congrArg (fun g : MulAut V => g v) hx3
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [h2] at h3
  exact h3

omit [Finite V] in
theorem zpowers_invariant_of_mem_stabSub {U : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub U) :
    ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U, x u ∈ U := by
  intro x hx u hu
  have : Subgroup.zpowers g ≤ stabSub U := Subgroup.zpowers_le.mpr hg
  exact ((this hx) u).mpr hu

omit [Finite V] in
theorem map_commHom_congr {W : Subgroup V} {g h : MulAut V} (hgh : ∀ w ∈ W, g w = h w) :
    W.map (commHom g) = W.map (commHom h) := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by simp [commHom_apply, hgh w hw]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by simp [commHom_apply, hgh w hw]⟩

theorem fixes_W_of_one_inverted (hV : ∀ v : V, v ^ 2 = 1) {X P₀ : Subgroup (MulAut V)}
    (c : CycCtx X) {t : MulAut V} (ht : t ∈ TInv X) (hP₀ : P₀ ∈ Xk X 1)
    (hn₀ : ∀ y ∈ P₀, t * y * t⁻¹ = y⁻¹)
    (hnorm : ∀ Q ∈ Xk X 1, t ∈ Subgroup.normalizer (Q : Set (MulAut V)))
    (hcen : ∀ Q ∈ Xk X 1, Q ≠ P₀ → ∀ y ∈ Q, t * y = y * t) :
    ∀ w ∈ fixV (Gk X 1), t w = w := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hrk : rk (commV (Subgroup.zpowers t)) = 2 := c.rk_eq_two hV ht
  have hO2 := c.hyp.o2
  by_contra hcon
  push Not at hcon
  obtain ⟨w₀, hw₀, htw₀⟩ := hcon
  set Y := Gk X 1 with hY
  set W := fixV Y with hW
  have hstab : ∀ g ∈ X, g ∈ stabSub W := fun g hg => (stab_commV_Gk (k := 1) hg).2
  have hWt : ∀ g ∈ Subgroup.zpowers t, ∀ w ∈ W, g w ∈ W :=
    zpowers_invariant_of_mem_stabSub (hstab t ht.1)
  have hF1 : rk (commSub W (Subgroup.zpowers t)) ≤ 1 := by
    obtain ⟨hsup0, hinf0⟩ := Xk_decomp hV hP₀
    have hnorm₀ : ∀ y ∈ P₀, t * y * t⁻¹ ∈ P₀ := fun y hy => by
      rw [hn₀ y hy]; exact P₀.inv_mem hy
    have hnorm₀' : ∀ y ∈ P₀, t⁻¹ * y * t ∈ P₀ := fun y hy => by
      have := hnorm₀ y hy
      rw [htinv] at this ⊢
      exact this
    have hV₀t : ∀ u ∈ commV P₀, t u ∈ commV P₀ := fun u hu => commV_smul_mem hnorm₀ hu
    have hF₀t : ∀ u ∈ fixV P₀, t u ∈ fixV P₀ := fun u hu => fixV_smul_mem hnorm₀' hu
    have hd : IsDirectSum ⊤ (commV P₀) (fixV P₀) := ⟨hsup0, hinf0⟩
    have hrk_sum := rk_commSub_isDirectSum (g := t) hd (invariant_zpowers ht2 hV₀t)
      (invariant_zpowers ht2 hF₀t)
    rw [← commV_eq_commSub, hrk, rk_commSub_inverted hV ht hP₀ hn₀] at hrk_sum
    have hWle : W ≤ fixV P₀ :=
      fixV_anti (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) P₀ hP₀)
    have := rk_mono (commSub_mono hWle (le_refl (Subgroup.zpowers t)))
    omega
  have hR := c.fittingOf_eq hV
  have hRX : pCoreOf 3 X ≤ X := pCoreOf_le 3 X
  have hxex : ∃ x ∈ pCoreOf 3 X, t * x * t⁻¹ = x⁻¹ ∧ ∃ w ∈ W, x w ≠ w := by
    by_contra hno
    push Not at hno
    have hRn : ∀ y ∈ pCoreOf 3 X, t * y * t⁻¹ ∈ pCoreOf 3 X := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X ht.1) y).mp hy
    have hcomm : ∀ y ∈ pCoreOf 3 X, ∀ u ∈ W, t (y u) = y (t u) := by
      intro y hy u hu
      set d := y⁻¹ * (t * y * t⁻¹) with hd
      have hdR : d ∈ pCoreOf 3 X := (pCoreOf 3 X).mul_mem ((pCoreOf 3 X).inv_mem hy) (hRn y hy)
      have hdinv : t * d * t⁻¹ = d⁻¹ := inv_conj_of_involution y ht2
      have hdu : ∀ u' ∈ W, d u' = u' := hno d hdR hdinv
      have h1 : ∀ u' ∈ W, (t * y * t⁻¹) u' = y u' := by
        intro u' hu'
        have h2 : y⁻¹ ((t * y * t⁻¹) u') = u' := hdu u' hu'
        calc (t * y * t⁻¹) u' = y (y⁻¹ ((t * y * t⁻¹) u')) := by simp
          _ = y u' := by rw [h2]
      have htu : t u ∈ W := hWt t (Subgroup.mem_zpowers t) u hu
      have h3 : (t * y * t⁻¹) (t u) = t (y u) := by
        show t (y (t⁻¹ (t u))) = t (y u)
        simp
      rw [← h3]
      exact h1 (t u) htu
    set F := commSub W (Subgroup.zpowers t) with hFdef
    have hFmap : F = W.map (commHom t) := commSub_zpowers_eq_map hWt
    have hFinv : ∀ y ∈ pCoreOf 3 X, ∀ f ∈ F, y f ∈ F := by
      intro y hy f hf
      rw [hFmap] at hf ⊢
      obtain ⟨u, hu, rfl⟩ := hf
      refine ⟨y u, ((hstab y (hRX hy)) u).mpr hu, ?_⟩
      show commHom t (y u) = y (commHom t u)
      simp only [commHom_apply, map_mul, map_inv]
      rw [hcomm y hy u hu]
    have hFfix : F ≤ fixV (pCoreOf 3 X) := by
      intro f hf y hy
      by_cases hf1 : f = 1
      · rw [hf1, map_one]
      · have hyf : y f ∈ F := hFinv y hy f hf
        have hyf1 : y f ≠ 1 := fun h => hf1 (y.injective (by rw [h, map_one]))
        exact eq_of_ne_one_of_rk_le_one hV hF1 hyf hf hyf1 hf1
    have hfixR : fixV (pCoreOf 3 X) = ⊥ := by
      rw [← hR]
      exact fixV_fittingOf_eq_bot hV hO2 c.hyp.comm_fitting
    have hFbot : F = ⊥ := le_bot_iff.mp (hfixR ▸ hFfix)
    have hWfix : W ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp hFbot
    exact htw₀ (mem_fixV_zpowers_iff.mp (hWfix hw₀))
  obtain ⟨x, hxR, hxinv, w₁, hw₁, hxw₁⟩ := hxex
  have hxX : x ∈ X := hRX hxR
  have hx1 : x ≠ 1 := by intro h; apply hxw₁; rw [h]; rfl
  have hxord : orderOf x = 3 :=
    (inverted_elem hV ht (p := 3) (by norm_num) hRX (pCoreOf_isPGroup 3 X) hxR hx1 hxinv).1
  have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hxN : ∀ P ∈ Xk X 1, conjBy x P = P := fun P hP =>
    conjBy_eq_of_inverted hxX ht2 hx3 hxinv hnorm hP
  have hxn : ∀ P ∈ Xk X 1, ∀ y ∈ P, x * y * x⁻¹ ∈ P := fun P hP y hy => by
    have := mem_conjBy_of_mem (g := x) hy
    rwa [hxN P hP] at this
  have hxn' : ∀ P ∈ Xk X 1, ∀ y ∈ P, x⁻¹ * y * x ∈ P := fun P hP y hy => by
    have h1 : y ∈ conjBy x P := by rw [hxN P hP]; exact hy
    exact mem_conjBy_iff.mp h1
  have hxcomm : ∀ P ∈ Xk X 1, ∀ y ∈ P, x * y = y * x := fun P hP =>
    commute_of_normalizes_prime (p := 3) (by simpa using hP.2.1) hxord (hxn P hP) (hxn' P hP)
  have hxfixP : ∀ P ∈ Xk X 1, P ≠ P₀ → ∀ v ∈ commV P, x v = v := by
    intro P hP hne
    refine fixes_commV_of_inverted ht2 hx3 hxinv (hxn P hP) ?_
    intro v hv
    exact mem_fixV_zpowers_iff.mp
      (commV_le_fixV_of_commutes hV hk ht2 hP (hcen P hP hne) hv)
  obtain ⟨p, hpP₀, hp⟩ := exists_pow_eq_on_commV hV hP₀ (hxcomm P₀ hP₀)
    (fun v hv => commV_smul_mem (hxn P₀ hP₀) hv)
  have hP₀Y : P₀ ≤ Y := le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) P₀ hP₀
  have hP₀F : P₀ ≤ fittingOf X := hP₀.1
  have hpinv : p⁻¹ ∈ P₀ := P₀.inv_mem hpP₀
  set x' := p⁻¹ * x with hx'
  have hx'comm : commV Y ≤ fixV (Subgroup.zpowers x') := by
    rw [hY, (D2_12_2 (X := X) hV hk).1]
    refine iSup₂_le fun Q hQ => ?_
    intro v hv
    refine mem_fixV_zpowers_iff.mpr ?_
    by_cases hQ0 : Q = P₀
    · subst hQ0
      show p⁻¹ (x v) = v
      rw [hp v hv]
      simp
    · have hxv : x v = v := hxfixP Q hQ hQ0 v hv
      have hpv : p⁻¹ v = v :=
        Xk_centralizes hV hk hQ hP₀ hQ0 (Xk_commute hV hk Q hQ P₀ hP₀) p⁻¹ hpinv v hv
      show p⁻¹ (x v) = v
      rw [hxv, hpv]
  have hx'W : ∀ w ∈ W, x' w = x w := by
    intro w hw
    have hxw : x w ∈ W := ((hstab x hxX) w).mpr hw
    show p⁻¹ (x w) = x w
    exact hxw p⁻¹ (hP₀Y hpinv)
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hxw₁
    have : x' w₁ = w₁ := by rw [h]; rfl
    rw [← hx'W w₁ hw₁]
    exact this
  have hpc : Commute p⁻¹ x := by
    have : x * p = p * x := hxcomm P₀ hP₀ p hpP₀
    exact ((show Commute x p from this).symm).inv_left
  have hp3 : p ^ 3 = 1 := by
    have h1 : orderOf p ∣ 3 := by
      have := orderOf_dvd_natCard (⟨p, hpP₀⟩ : ↥P₀)
      rwa [Subgroup.orderOf_mk, show Nat.card P₀ = 3 by simpa using hP₀.2.1] at this
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx', hpc.mul_pow, inv_pow, hp3, hx3]
    simp
  have hx'ord : orderOf x' = 3 := orderOf_eq_prime hx'3 hx'1
  have hx'X : x' ∈ X := X.mul_mem (X.inv_mem (hP₀F.trans (fittingOf_le X) hpP₀)) hxX
  have hx'stab : x' ∈ stabSub W := (stabSub W).mul_mem
    ((stabSub W).inv_mem (hstab p (hP₀F.trans (fittingOf_le X) hpP₀))) (hstab x hxX)
  have hWx' := zpowers_invariant_of_mem_stabSub hx'stab
  have hWx := zpowers_invariant_of_mem_stabSub (hstab x hxX)
  have hVx' : ∀ g ∈ Subgroup.zpowers x', ∀ u ∈ commV Y, g u ∈ commV Y := by
    intro g hg u hu
    rw [hx'comm hu g hg]
    exact hu
  obtain ⟨hdsup, hdinf⟩ := Gk_decomp hV hO2 1
  have hdirect : IsDirectSum ⊤ (commV Y) W := ⟨hdsup, hdinf⟩
  have hsum := rk_commSub_isDirectSum (g := x') hdirect hVx' hWx'
  have hbot : commSub (commV Y) (Subgroup.zpowers x') = ⊥ := commSub_eq_bot_iff.mpr hx'comm
  rw [← commV_eq_commSub, hbot, rk_bot, zero_add] at hsum
  have hcomm_eq : commSub W (Subgroup.zpowers x') = commSub W (Subgroup.zpowers x) := by
    rw [commSub_zpowers_eq_map hWx', commSub_zpowers_eq_map hWx]
    exact map_commHom_congr hx'W
  rw [hcomm_eq] at hsum
  obtain ⟨hev, hge, hle⟩ := rk_commSub_inverted_le hV ht2 (by rw [hxord]; exact ⟨1, rfl⟩) hxinv
    hWt hWx (by omega) ⟨w₁, hw₁, hxw₁⟩
  have hrk2 : rk (commV (Subgroup.zpowers x')) = 2 := by
    obtain ⟨m, hm⟩ := hev
    omega
  have hfx' : x' ∈ fittingOf X :=
    (fittingOf X).mul_mem ((fittingOf X).inv_mem (hP₀F hpP₀)) (by rw [hR]; exact hxR)
  have hmem : Subgroup.zpowers x' ∈ Xk X 1 := by
    refine ⟨Subgroup.zpowers_le.mpr hfx', ?_, ?_⟩
    · rw [Nat.card_zpowers, hx'ord]
    · rw [hrk2]
  have hle' : Subgroup.zpowers x' ≤ Y := le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) _ hmem
  have hx'Y : x' ∈ Y := hle' (Subgroup.mem_zpowers x')
  have hfix := hw₁ x' hx'Y
  apply hxw₁
  rw [← hx'W w₁ hw₁]
  exact hfix

theorem tinv_fixes_W_or_commV (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    {t : MulAut V} (ht : t ∈ TInv X) :
    (∀ w ∈ fixV (Gk X 1), t w = w) ∨ (∀ w ∈ commV (Gk X 1), t w = w) := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hrk := c.rk_eq_two hV ht
  have hO2 := c.hyp.o2
  by_cases hcen : ∀ P ∈ Xk X 1, ∀ y ∈ P, t * y = y * t
  · right
    have h1 : commV (Gk X 1) = ⨆ Y ∈ Xk X 1, commV Y := (D2_12_2 hV hk).1
    have h2 : (⨆ Y ∈ Xk X 1, commV Y) ≤ fixV (Subgroup.zpowers t) :=
      iSup₂_le fun P hP => commV_le_fixV_of_commutes hV hk ht2 hP (hcen P hP)
    intro w hw
    rw [h1] at hw
    exact mem_fixV_zpowers_iff.mp (h2 hw)
  · left
    push Not at hcen
    obtain ⟨P₀, hP₀, y₀, hy₀, hne₀⟩ := hcen
    rcases D2_12_5 hV ht hrk with hα | ⟨Y₁, hY₁, Y₂, hY₂, hne12, h12, h21, hcomm12, -⟩
    · have hn : ∀ P ∈ Xk X 1, ∀ y ∈ P, t * y * t⁻¹ ∈ P := fun P hP y hy =>
        (Subgroup.mem_normalizer_iff.mp (hα P hP) y).mp hy
      have hdich : ∀ P ∈ Xk X 1, (∀ y ∈ P, t * y * t⁻¹ = y) ∨ (∀ y ∈ P, t * y * t⁻¹ = y⁻¹) :=
        fun P hP => inverts_or_commutes (p := 3) (by simpa using hP.2.1) ht2 (hn P hP)
      have hinv₀ : ∀ y ∈ P₀, t * y * t⁻¹ = y⁻¹ := by
        rcases hdich P₀ hP₀ with h | h
        · exact absurd (mul_inv_eq_iff_eq_mul.mp (h y₀ hy₀)) hne₀
        · exact h
      by_cases h2 : ∃ P₁ ∈ Xk X 1, P₁ ≠ P₀ ∧ ∀ y ∈ P₁, t * y * t⁻¹ = y⁻¹
      · obtain ⟨P₁, hP₁, hne, hinv₁⟩ := h2
        exact fixes_W_of_two_inverted hV hO2 ht hrk hP₀ hP₁ hne hinv₀ hinv₁
      · push Not at h2
        refine fixes_W_of_one_inverted hV c ht hP₀ hinv₀ hα ?_
        intro Q hQ hne y hy
        rcases hdich Q hQ with h | h
        · exact mul_inv_eq_iff_eq_mul.mp (h y hy)
        · obtain ⟨y', hy', hne'⟩ := h2 Q hQ hne
          exact absurd (h y' hy') hne'
    · exact fixes_W_of_swap hV hO2 ht hY₁ hY₂ h12 h21 hcomm12

omit [Finite V] in
theorem commV_Gk_ne_bot {X : Subgroup (MulAut V)} (hne : (Xk X 1).Nonempty) :
    commV (Gk X 1) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := hne
  intro h
  have h1 : commV P ≤ commV (Gk X 1) :=
    commV_mono (le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => Z) P hP)
  rw [h, le_bot_iff] at h1
  have h2 : rk (commV P) = 2 * 1 := hP.2.2
  rw [h1, rk_bot] at h2
  omega

theorem fixV_Gk_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) : fixV (Gk X 1) = ⊥ := by
  obtain ⟨hdsup, hdinf⟩ := Gk_decomp hV c.hyp.o2 1
  have hdirect : IsDirectSum ⊤ (commV (Gk X 1)) (fixV (Gk X 1)) := ⟨hdsup, hdinf⟩
  have hcases : ∀ B ∈ QhatStar X,
      (B ≤ centSub (fixV (Gk X 1)) ∧ commV B ≤ commV (Gk X 1)) ∨
        (B ≤ centSub (commV (Gk X 1)) ∧ commV B ≤ fixV (Gk X 1)) := by
    intro B hB
    obtain ⟨t, ht, rfl⟩ := c.exists_tinv hB
    have ht2 := ht.2.2.1
    have hstab := stab_commV_Gk (k := 1) ht.1
    rcases tinv_fixes_W_or_commV hV c ht with h | h
    · left
      have := commV_zpowers_le_of_fixes (U₁ := commV (Gk X 1)) (U₂ := fixV (Gk X 1)) hdsup ht2
        (fun u hu => ((hstab.1 u).mpr hu)) h
      exact ⟨this.2, this.1⟩
    · right
      have := commV_zpowers_le_of_fixes (U₁ := fixV (Gk X 1)) (U₂ := commV (Gk X 1))
        (by rw [sup_comm]; exact hdsup) ht2 (fun u hu => (hstab.2 u).mpr hu) h
      exact ⟨this.2, this.1⟩
  rcases qhatStar_cases_of_indecomposable c.hyp.indecomposable hdirect hcases with hall | hall
  · refine c.fixV_T hV fun t ht w hw => ?_
    exact (hall (Subgroup.zpowers t) (c.zpowers_mem_qhatStar hV ht)).1
      (Subgroup.mem_zpowers t) w hw
  · exfalso
    apply commV_Gk_ne_bot hne
    refine c.fixV_T hV fun t ht w hw => ?_
    exact (hall (Subgroup.zpowers t) (c.zpowers_mem_qhatStar hV ht)).1
      (Subgroup.mem_zpowers t) w hw

theorem commV_Gk_eq_top (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) : commV (Gk X 1) = ⊤ := by
  obtain ⟨hdsup, -⟩ := Gk_decomp hV c.hyp.o2 1
  rwa [fixV_Gk_eq_bot hV c hne, sup_bot_eq] at hdsup

theorem rk_commV_Gk (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} :
    rk (commV (Gk X 1)) = 2 * Nat.card (Xk X 1) := by
  classical
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have : Fintype (Xk X 1) := Fintype.ofFinite _
  obtain ⟨h1, h2⟩ := D2_12_2 (X := X) hV hk
  have hsum := rk_iSup_biSup_eq_sum (fun Y : Xk X 1 => commV (Y : Subgroup (MulAut V))) h2
    Finset.univ
  have e : (⨆ Y : Xk X 1, commV (Y : Subgroup (MulAut V))) = ⨆ Y ∈ Xk X 1, commV Y := by
    apply le_antisymm
    · exact iSup_le fun Y => le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => commV Z) Y.1 Y.2
    · exact iSup₂_le fun Y hY =>
        le_iSup (fun Y : Xk X 1 => commV (Y : Subgroup (MulAut V))) ⟨Y, hY⟩
  have e2 : (⨆ i ∈ (Finset.univ : Finset (Xk X 1)), commV (i : Subgroup (MulAut V))) =
      ⨆ Y : Xk X 1, commV (Y : Subgroup (MulAut V)) :=
    iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [e2, e, ← h1] at hsum
  rw [hsum, Finset.sum_congr rfl (fun i _ => i.2.2.2)]
  simp [Nat.card_eq_fintype_card, mul_comm]

theorem iSup_commV_eq (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} :
    (⨆ P : Xk X 1, commV (P : Subgroup (MulAut V))) = commV (Gk X 1) := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  rw [(D2_12_2 (X := X) hV hk).1]
  apply le_antisymm
  · exact iSup_le fun Y => le_iSup₂ (f := fun Z (_ : Z ∈ Xk X 1) => commV Z) Y.1 Y.2
  · exact iSup₂_le fun Y hY =>
      le_iSup (fun Y : Xk X 1 => commV (Y : Subgroup (MulAut V))) ⟨Y, hY⟩

theorem exists_moved_pair (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) {t : MulAut V} (ht : t ∈ TInv X) :
    ∃ P₁ ∈ Xk X 1, ∃ P₂ ∈ Xk X 1, P₁ ≠ P₂ ∧
      ((conjBy t P₁ = P₂ ∧ conjBy t P₂ = P₁) ∨
        ((∀ y ∈ P₁, t * y * t⁻¹ = y⁻¹) ∧ ∀ y ∈ P₂, t * y * t⁻¹ = y⁻¹)) ∧
      ∀ Q ∈ Xk X 1, Q ≠ P₁ → Q ≠ P₂ → ∀ y ∈ Q, t * y = y * t := by
  classical
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have hrk := c.rk_eq_two hV ht
  rcases D2_12_5 hV ht hrk with hα | ⟨Y₁, hY₁, Y₂, hY₂, hne12, h12, h21, -, hothers⟩
  · have hn : ∀ P ∈ Xk X 1, ∀ y ∈ P, t * y * t⁻¹ ∈ P := fun P hP y hy =>
      (Subgroup.mem_normalizer_iff.mp (hα P hP) y).mp hy
    have hdich : ∀ P ∈ Xk X 1, (∀ y ∈ P, t * y * t⁻¹ = y) ∨ (∀ y ∈ P, t * y * t⁻¹ = y⁻¹) :=
      fun P hP => inverts_or_commutes (p := 3) (by simpa using hP.2.1) ht2 (hn P hP)
    have : Fintype (Xk X 1) := Fintype.ofFinite _
    set S : Xk X 1 → Subgroup V := fun P => commV (P : Subgroup (MulAut V)) with hS
    have hSind : iSupIndep S := (D2_12_2 (X := X) hV hk).2
    have hSinv : ∀ P, ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ S P, x u ∈ S P := fun P =>
      invariant_zpowers ht2 (fun u hu => commV_smul_mem (hn P P.2) hu)
    have hsup : (⨆ P, S P) = ⊤ := by
      rw [hS]
      simp only
      rw [iSup_commV_eq hV]
      exact commV_Gk_eq_top hV c hne
    have hrksum := rk_commSub_iSup S hSind hSinv
    rw [hsup, ← commV_eq_commSub, hrk] at hrksum
    have hterm : ∀ P : Xk X 1, rk (commSub (S P) (Subgroup.zpowers t)) =
        if (∀ y ∈ (P : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹) then 1 else 0 := by
      intro P
      split_ifs with hinv
      · exact rk_commSub_inverted hV ht P.2 hinv
      · rcases hdich P P.2 with hc | hc
        · have hcomm : ∀ y ∈ (P : Subgroup (MulAut V)), t * y = y * t := fun y hy =>
            mul_inv_eq_iff_eq_mul.mp (hc y hy)
          have hfix : commV (P : Subgroup (MulAut V)) ≤ fixV (Subgroup.zpowers t) :=
            commV_le_fixV_of_commutes hV hk ht2 P.2 hcomm
          have : commSub (S P) (Subgroup.zpowers t) = ⊥ := commSub_eq_bot_iff.mpr hfix
          rw [this, rk_bot]
        · exact absurd hc hinv
    simp only [hterm] at hrksum
    rw [Finset.sum_boole] at hrksum
    have hcard : (Finset.univ.filter fun P : Xk X 1 =>
        ∀ y ∈ (P : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹).card = 2 := by
      simpa using hrksum.symm
    obtain ⟨a, b, hab, hfil⟩ := Finset.card_eq_two.mp hcard
    have ha : ∀ y ∈ (a : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹ := by
      have : a ∈ Finset.univ.filter fun P : Xk X 1 =>
          ∀ y ∈ (P : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹ := by rw [hfil]; simp
      simpa using this
    have hb : ∀ y ∈ (b : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹ := by
      have : b ∈ Finset.univ.filter fun P : Xk X 1 =>
          ∀ y ∈ (P : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹ := by rw [hfil]; simp
      simpa using this
    refine ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h), Or.inr ⟨ha, hb⟩, ?_⟩
    intro Q hQ hQa hQb y hy
    rcases hdich Q hQ with hc | hc
    · exact mul_inv_eq_iff_eq_mul.mp (hc y hy)
    · exfalso
      have : (⟨Q, hQ⟩ : Xk X 1) ∈ Finset.univ.filter fun P : Xk X 1 =>
          ∀ y ∈ (P : Subgroup (MulAut V)), t * y * t⁻¹ = y⁻¹ := by
        simpa using hc
      rw [hfil] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact hQa (congrArg Subtype.val h)
      · exact hQb (congrArg Subtype.val h)
  · exact ⟨Y₁, hY₁, Y₂, hY₂, hne12, Or.inl ⟨h12, h21⟩,
      fun Q hQ h1 h2 y hy => (hothers Q hQ h1 h2).1 y hy⟩

omit [Finite V] in
theorem mul_comm_of_card_prime {Q : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime]
    (hQ : Nat.card Q = p) : ∀ a b : Q, a * b = b * a := by
  have : IsCyclic Q := isCyclic_of_prime_card hQ
  let _ := IsCyclic.commGroup (α := Q)
  intro a b
  exact mul_comm a b

omit [Finite V] in
theorem inf_eq_bot_of_card_prime {Q₁ Q₂ : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] [Finite V]
    (h₁ : Nat.card Q₁ = p) (h₂ : Nat.card Q₂ = p) (hne : Q₁ ≠ Q₂) : Q₁ ⊓ Q₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  by_contra hz1
  apply hne
  rw [← zpowers_eq_of_prime_card h₁ hz.1 hz1, ← zpowers_eq_of_prime_card h₂ hz.2 hz1]

theorem pRank_three_ge_two {X Q₁ Q₂ : Subgroup (MulAut V)} {t : MulAut V}
    (hQ₁ : Nat.card Q₁ = 3) (hQ₂ : Nat.card Q₂ = 3) (hne : Q₁ ≠ Q₂)
    (hX₁ : Q₁ ≤ X) (hX₂ : Q₂ ≤ X)
    (hcomm : ∀ y ∈ Q₁, ∀ z ∈ Q₂, y * z = z * y)
    (ht₁ : ∀ y ∈ Q₁, t * y = y * t) (ht₂ : ∀ y ∈ Q₂, t * y = y * t) :
    2 ≤ CFSG.Open.pRank 3 (X ⊓ Subgroup.centralizer ({t} : Set (MulAut V))) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbot := inf_eq_bot_of_card_prime hQ₁ hQ₂ hne
  let f : ↥Q₁ × ↥Q₂ →* MulAut V :=
    (Q₁.subtype).noncommCoprod (Q₂.subtype) (fun x y => hcomm x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    have h1 : (x : MulAut V) * y = 1 := h
    have hx : (x : MulAut V) ∈ Q₁ ⊓ Q₂ := by
      refine ⟨x.2, ?_⟩
      have : (x : MulAut V) = (y : MulAut V)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      rw [this]
      exact Q₂.inv_mem y.2
    rw [hbot, Subgroup.mem_bot] at hx
    have hy : (y : MulAut V) = 1 := by
      rw [hx, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm_of_card_prime hQ₁ a c) (mul_comm_of_card_prime hQ₂ b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (by simp [← hQ₁]) (by simp [← hQ₂])
  · rw [Nat.card_prod, hQ₁, hQ₂]
    norm_num
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    have hfab : f (a, b) = (a : MulAut V) * b := rfl
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [hfab]; exact X.mul_mem (hX₁ a.2) (hX₂ b.2)
    · rw [hfab]
      have h1 := ht₁ a a.2
      have h2 := ht₂ b b.2
      calc (a * b : MulAut V) * t = a * (b * t) := by rw [mul_assoc]
        _ = a * (t * b) := by rw [← h2]
        _ = (a * t) * b := by rw [mul_assoc]
        _ = (t * a) * b := by rw [← h1]
        _ = t * (a * b) := by rw [mul_assoc]

theorem CycCtx.faithful_zpowers (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (c : CycCtx X) {t : MulAut V} (ht : t ∈ TInv X) :
    ∀ a ∈ Subgroup.zpowers t, (∀ y ∈ pCoreOf 3 X, a * y = y * a) → a = 1 := by
  intro a ha hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rcases zpow_involution ht.2.2.1 k with e | e
  · exact e
  · exfalso
    rw [e] at hc
    obtain ⟨y, hy, hne⟩ := c.faithful_three hV ht
    exact hne (hc y hy)

theorem card_Xk_le_three (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) : Nat.card (Xk X 1) ≤ 3 := by
  classical
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hA⟩ := QhatStar_nonempty c.hyp.qhat c.hyp.le_two
  obtain ⟨t, ht, rfl⟩ := c.exists_tinv hA
  obtain ⟨P₁, hP₁, P₂, hP₂, hne12, -, hcen⟩ := exists_moved_pair hV c hne ht
  have : Fintype (Xk X 1) := Fintype.ofFinite _
  set s : Finset (Xk X 1) := (Finset.univ.erase ⟨P₁, hP₁⟩).erase ⟨P₂, hP₂⟩ with hs
  have hs_card : 2 ≤ s.card := by
    have h1 : (⟨P₂, hP₂⟩ : Xk X 1) ∈ Finset.univ.erase (⟨P₁, hP₁⟩ : Xk X 1) := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun h => hne12 (congrArg Subtype.val h).symm
    rw [hs, Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    have hc : Nat.card {x // x ∈ Xk X 1} = Nat.card (Xk X 1) := rfl
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  simp only [hs, Finset.mem_erase, Finset.mem_univ, and_true] at ha hb
  obtain ⟨ha2, ha1⟩ := ha
  obtain ⟨hb2, hb1⟩ := hb
  have ha1' : (a : Subgroup (MulAut V)) ≠ P₁ := fun h => ha1 (Subtype.ext h)
  have ha2' : (a : Subgroup (MulAut V)) ≠ P₂ := fun h => ha2 (Subtype.ext h)
  have hb1' : (b : Subgroup (MulAut V)) ≠ P₁ := fun h => hb1 (Subtype.ext h)
  have hb2' : (b : Subgroup (MulAut V)) ≠ P₂ := fun h => hb2 (Subtype.ext h)
  have hge := pRank_three_ge_two (X := X) (t := t) (Q₁ := a) (Q₂ := b)
    (by simpa using a.2.2.1) (by simpa using b.2.2.1) (fun h => hab (Subtype.ext h))
    (a.2.1.trans (fittingOf_le X)) (b.2.1.trans (fittingOf_le X))
    (Xk_commute hV hk a a.2 b b.2) (hcen a a.2 ha1' ha2') (hcen b b.2 hb1' hb2')
  have hle := D2_21 c.hyp hA (c.faithful_zpowers hV ht) (Subgroup.mem_zpowers t) ht.2.1
  omega

theorem CycCtx.rk_fixV_add_four_le (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (c : CycCtx X) {E : Subgroup (MulAut V)} (hE : IsElemAbelian2 E) (hEX : E ≤ X)
    (hcard : Nat.card E = 4) : rk (fixV E) + 4 ≤ rk V := by
  have hA : IsA2 X E := ⟨hEX, fun h => by rw [h, Subgroup.card_bot] at hcard; omega, hE⟩
  have hcub := commSeries_three_eq_bot_of_card_four hV hE hcard
  have h2 := le_kq_iff.mp c.hyp.qhat.ge E hA hcub
  have hrkE : rk E = 2 := by
    unfold rk
    rw [hcard]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this, padicValNat.prime_pow]
  unfold rAV at h2
  rw [hrkE] at h2
  have h3 : (4 : ℚ) ≤ (rkIdx (fixV E) : ℚ) := by
    have : (2 : ℚ) ≤ (rkIdx (fixV E) : ℚ) / ((2 : ℕ) : ℚ) := by exact_mod_cast h2
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have h4 : 4 ≤ rkIdx (fixV E) := by exact_mod_cast h3
  have := rk_add_rkIdx (fixV E)
  omega

theorem rk_inf_fixV_pos_of_isPGroup_two (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsPGroup 2 E) {U : Subgroup V} (hU : ∀ g ∈ E, ∀ u ∈ U, g u ∈ U) (hU0 : U ≠ ⊥) :
    0 < rk (U ⊓ fixV E : Subgroup V) := by
  have hstab : E ≤ stabSub U := by
    intro g hg u
    constructor
    · intro h
      have := hU g⁻¹ (E.inv_mem hg) (g u) h
      simpa using this
    · exact hU g hg u
  have h1 := rk_fixV_autSub hstab
  have hVU : ∀ w : U, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hrkU : 0 < rk U := by
    rcases Nat.eq_zero_or_pos (rk U) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hV).mp h0) hU0
    · exact h0
  have := rk_fixV_pos_of_isPGroup_two hVU (isPGroup_autSub (U := U) hE) hrkU
  omega

theorem card_Xk_le_rk_fixV (hV : ∀ v : V, v ^ 2 = 1) {X E : Subgroup (MulAut V)}
    (hE : IsPGroup 2 E) (hEn : ∀ g ∈ E, ∀ P ∈ Xk X 1, ∀ y ∈ P, g * y * g⁻¹ ∈ P) :
    Nat.card (Xk X 1) ≤ rk (fixV E) := by
  classical
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have : Fintype (Xk X 1) := Fintype.ofFinite _
  set S : Xk X 1 → Subgroup V := fun P => commV (P : Subgroup (MulAut V)) ⊓ fixV E with hS
  have hind : iSupIndep S :=
    (D2_12_2 (X := X) hV hk).2.mono fun P => inf_le_left
  have hsum := rk_iSup_biSup_eq_sum S hind Finset.univ
  have hpos : ∀ P : Xk X 1, 1 ≤ rk (S P) := by
    intro P
    have hU : ∀ g ∈ E, ∀ u ∈ commV (P : Subgroup (MulAut V)), g u ∈ commV (P : Subgroup (MulAut V)) :=
      fun g hg u hu => commV_smul_mem (hEn g hg P P.2) hu
    have hU0 : commV (P : Subgroup (MulAut V)) ≠ ⊥ := by
      intro h
      have h2 : rk (commV (P : Subgroup (MulAut V))) = 2 * 1 := P.2.2.2
      rw [h, rk_bot] at h2
      omega
    exact rk_inf_fixV_pos_of_isPGroup_two hV hE hU hU0
  have hle : (⨆ i ∈ (Finset.univ : Finset (Xk X 1)), S i) ≤ fixV E :=
    iSup₂_le fun P _ => inf_le_right
  have h1 := rk_mono hle
  rw [hsum] at h1
  have h2 : ∑ i : Xk X 1, 1 ≤ ∑ i : Xk X 1, rk (S i) := Finset.sum_le_sum fun i _ => hpos i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h2
  rw [← Nat.card_eq_fintype_card] at h2
  exact h2.trans h1

end CFSG.Quasithin
