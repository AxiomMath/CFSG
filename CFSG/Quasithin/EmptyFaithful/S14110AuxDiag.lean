module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4
public import CFSG.Quasithin.Background.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open Subgroup

variable {G : Type*} [Group G]

private theorem exists_mul_of_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {a : G} (ha : a ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, a = h * k := by
  have hle : H ≤ normalizer (K : Set G) := fun h hh =>
    centralizer_le_normalizer (K : Set G)
      (mem_centralizer_iff.2 fun k hk => (hHK h hh k hk).symm)
  have h1 : a ∈ ((H ⊔ K : Subgroup G) : Set G) := ha
  rw [coe_mul_of_left_le_normalizer_right H K hle] at h1
  obtain ⟨h, hh, k, hk, rfl⟩ := h1
  exact ⟨h, hh, k, hk, rfl⟩

private theorem normalizer_le_normalizer_of_a4 {X W : Subgroup G} {c : G} (h : A4Data X W c) :
    normalizer (X : Set G) ≤ normalizer (W : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro w
  have key : ∀ {w : G}, w ∈ W → g * w * g⁻¹ ∈ W := by
    intro w hw
    refine h.mem_W_of_sq_eq_one ((mem_normalizer_iff.1 hg w).1 (h.le hw)) ?_
    calc (g * w * g⁻¹) ^ 2 = g * w ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [h.sq_eq_one w hw]; group
  refine ⟨key, fun hw => ?_⟩
  have hwX : w ∈ X := (mem_normalizer_iff.1 hg w).2 (h.le hw)
  refine h.mem_W_of_sq_eq_one hwX ?_
  calc w ^ 2 = g⁻¹ * (g * w * g⁻¹) ^ 2 * g := by rw [pow_two, pow_two]; group
    _ = 1 := by rw [h.sq_eq_one _ hw]; group

variable {X Y W₁ W₂ : Subgroup G} {c₁ c₂ : G}

private theorem inf_eq_bot_of_commute (hX : A4Data X W₁ c₁)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : X ⊓ Y = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  exact hX.center g hg.1 fun l hl => (hXY l hl g hg.2).symm

private theorem eq_of_mul_eq_mul (hX : A4Data X W₁ c₁) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    {u u' v v' : G} (hu : u ∈ X) (hu' : u' ∈ X) (hv : v ∈ Y) (hv' : v' ∈ Y)
    (h : u * v = u' * v') : u = u' ∧ v = v' := by
  have h1 : u'⁻¹ * u = v' * v⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * v) * v⁻¹ := by group
      _ = u'⁻¹ * (u' * v') * v⁻¹ := by rw [h]
      _ = v' * v⁻¹ := by group
  have h2 : u'⁻¹ * u ∈ X ⊓ Y :=
    mem_inf.2 ⟨mul_mem (inv_mem hu') hu, by rw [h1]; exact mul_mem hv' (inv_mem hv)⟩
  rw [inf_eq_bot_of_commute hX hXY, mem_bot] at h2
  have h3 : u = u' := by
    calc u = u' * (u'⁻¹ * u) := by group
      _ = u' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel h

private theorem exists_mul_of_mem_sup_of_sq_eq_one (hX : A4Data X W₁ c₁) (hY : A4Data Y W₂ c₂)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {a : G} (ha : a ∈ X ⊔ Y) (ha2 : a ^ 2 = 1) :
    ∃ u ∈ W₁, ∃ v ∈ W₂, a = u * v := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hXY ha
  have hcomm : Commute x y := hXY x hx y hy
  rw [hcomm.mul_pow] at ha2
  have h1 : x ^ 2 ∈ X ⊓ Y := by
    refine mem_inf.2 ⟨pow_mem hx 2, ?_⟩
    have : x ^ 2 = (y ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left ha2
    rw [this]
    exact inv_mem (pow_mem hy 2)
  rw [inf_eq_bot_of_commute hX hXY, mem_bot] at h1
  have h2 : y ^ 2 = 1 := by rw [h1, one_mul] at ha2; exact ha2
  exact ⟨x, hX.mem_W_of_sq_eq_one hx h1, y, hY.mem_W_of_sq_eq_one hy h2, rfl⟩

private theorem isElemAbelian_sup (hX : A4Data X W₁ c₁) (hY : A4Data Y W₂ c₂)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : IsElemAbelian 2 (W₁ ⊔ W₂) := by
  have hc : ∀ u ∈ W₁, ∀ v ∈ W₂, u * v = v * u := fun u hu v hv =>
    hXY u (hX.le hu) v (hY.le hv)
  have key : ∀ {a b : G}, a ∈ W₁ ⊔ W₂ → b ∈ W₁ ⊔ W₂ → a * b = b * a := by
    intro a b ha hb
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hc ha
    obtain ⟨u', hu', v', hv', rfl⟩ := exists_mul_of_mem_sup hc hb
    have huu' : u * u' = u' * u := hX.comm u hu u' hu'
    have hvv' : v * v' = v' * v := hY.comm v hv v' hv'
    have hvu' : v * u' = u' * v := (hc u' hu' v hv).symm
    have huv' : u * v' = v' * u := hc u hu v' hv'
    calc u * v * (u' * v') = u * (v * u') * v' := by group
      _ = u * (u' * v) * v' := by rw [hvu']
      _ = (u * u') * (v * v') := by group
      _ = (u' * u) * (v' * v) := by rw [huu', hvv']
      _ = u' * (u * v') * v := by group
      _ = u' * (v' * u) * v := by rw [huv']
      _ = u' * v' * (u * v) := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (key a.2 b.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hc hx
  rw [Commute.mul_pow (hc u hu v hv), hX.sq_eq_one u hu, hY.sq_eq_one v hv, one_mul]

private theorem sixteen_le_card_sup [Finite G] (hX : A4Data X W₁ c₁) (hY : A4Data Y W₂ c₂)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : 16 ≤ Nat.card ↥(W₁ ⊔ W₂) := by
  have hf : Function.Injective
      (fun p : W₁ × W₂ => (⟨(p.1 : G) * p.2, mul_mem_sup p.1.2 p.2.2⟩ : ↥(W₁ ⊔ W₂))) := by
    intro p q h
    have h' : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul hX hXY (hX.le p.1.2) (hX.le q.1.2) (hY.le p.2.2)
      (hY.le q.2.2) h'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have h := Nat.card_le_card_of_injective _ hf
  rw [Nat.card_prod, hX.card_W, hY.card_W] at h
  exact h

private theorem card_le_two_mul_card_inf_centralizer [Finite G] {W A : Subgroup G}
    (hW4 : Nat.card W = 4) (hWsq : ∀ w ∈ W, w ^ 2 = 1) (hWc : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u)
    (hA : IsElemAbelian 2 A) (hAN : A ≤ normalizer (W : Set G)) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ centralizer (W : Set G)) := by
  have hWfin : Finite W := Nat.finite_of_card_ne_zero (by rw [hW4]; norm_num)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := W)
    (fun a b => Subtype.ext (hWc a a.2 b b.2)) (fun a => Subtype.ext (hWsq a a.2)) (n := 2)
    (by rw [hW4]; norm_num)
  have h6 : Nat.card (MulAut W) = 6 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod,
      Fin.prod_univ_two]
    norm_num
  let φ : A →* MulAut W := W.normalizerMonoidHom.comp (inclusion hAN)
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hrange : Nat.card φ.range ≤ 2 := by
    have hAp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
    have hrp : IsPGroup 2 φ.range := hAp.of_surjective φ.rangeRestrict hsurj
    have hfin : Finite φ.range := Finite.of_surjective φ.rangeRestrict hsurj
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hrp
    have hdvd : Nat.card φ.range ∣ 6 := by
      have := card_subgroup_dvd_card φ.range
      rwa [h6] at this
    rw [hn] at hdvd ⊢
    have h2 : 2 ^ n ∣ 2 :=
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right
        (show 2 ^ n ∣ 2 * 3 from hdvd)
    exact Nat.le_of_dvd (by norm_num) h2
  have hmem : ∀ x : φ.ker, (x.1 : G) ∈ centralizer (W : Set G) := by
    intro x
    have h1 : inclusion hAN x.1 ∈ W.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      exact x.2
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at h1
    exact h1
  have hker : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ centralizer (W : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨(x.1 : G), x.1.2, hmem x⟩ : ↥(A ⊓ centralizer (W : Set G)))) ?_
    intro x y h
    have h' : ((x.1 : A) : G) = ((y.1 : A) : G) :=
      congrArg (fun z : ↥(A ⊓ centralizer (W : Set G)) => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := (card_ker_mul_card_range φ).symm
    _ ≤ Nat.card ↥(A ⊓ centralizer (W : Set G)) * 2 := Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card ↥(A ⊓ centralizer (W : Set G)) := mul_comm _ _

private theorem card_inf_centralizer_le_two [Finite G] {W : Subgroup G} {a : G}
    (hW4 : Nat.card W = 4) (ha : a ∉ centralizer (W : Set G)) :
    Nat.card ↥(W ⊓ centralizer ({a} : Set G)) ≤ 2 := by
  have hWfin : Finite W := Nat.finite_of_card_ne_zero (by rw [hW4]; norm_num)
  have hle : W ⊓ centralizer ({a} : Set G) ≤ W := inf_le_left
  have hdvd : Nat.card ↥(W ⊓ centralizer ({a} : Set G)) ∣ 4 := by
    have := card_dvd_of_le hle
    rwa [hW4] at this
  have hne : Nat.card ↥(W ⊓ centralizer ({a} : Set G)) ≠ 4 := by
    intro h4
    apply ha
    have heq : W ⊓ centralizer ({a} : Set G) = W :=
      eq_of_le_of_card_ge hle (by rw [hW4, h4])
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ W ⊓ centralizer ({a} : Set G) := heq.symm ▸ hw
    exact mem_centralizer_singleton_iff.1 hw'.2
  have h4 : Nat.card ↥(W ⊓ centralizer ({a} : Set G)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card ↥(W ⊓ centralizer ({a} : Set G)) = n at hdvd hne h4 ⊢
  interval_cases n <;> omega

private theorem card_sup_inf_centralizer_le_four [Finite G] (hX : A4Data X W₁ c₁)
    (hY : A4Data Y W₂ c₂) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {a : G}
    (haX : a ∈ normalizer (X : Set G)) (haY : a ∈ normalizer (Y : Set G))
    (ha₁ : a ∉ centralizer (W₁ : Set G)) (ha₂ : a ∉ centralizer (W₂ : Set G)) :
    Nat.card ↥((W₁ ⊔ W₂) ⊓ centralizer ({a} : Set G)) ≤ 4 := by
  have haW₁ := normalizer_le_normalizer_of_a4 hX haX
  have haW₂ := normalizer_le_normalizer_of_a4 hY haY
  have hc : ∀ u ∈ W₁, ∀ v ∈ W₂, u * v = v * u := fun u hu v hv =>
    hXY u (hX.le hu) v (hY.le hv)
  let f : ↥(W₁ ⊓ centralizer ({a} : Set G)) × ↥(W₂ ⊓ centralizer ({a} : Set G)) →
      ↥((W₁ ⊔ W₂) ⊓ centralizer ({a} : Set G)) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem_sup p.1.2.1 p.2.2.1, mul_mem p.1.2.2 p.2.2.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨k, hk, hka⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hc hk
    have hka' : (u * v) * a = a * (u * v) := mem_centralizer_singleton_iff.1 hka
    have hu' : a * u * a⁻¹ ∈ W₁ := (mem_normalizer_iff.1 haW₁ u).1 hu
    have hv' : a * v * a⁻¹ ∈ W₂ := (mem_normalizer_iff.1 haW₂ v).1 hv
    have h1 : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
      calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
        _ = (u * v) * a * a⁻¹ := by rw [hka']
        _ = u * v := by group
    obtain ⟨h2, h3⟩ := eq_of_mul_eq_mul hX hXY (hX.le hu') (hX.le hu) (hY.le hv') (hY.le hv) h1
    refine ⟨(⟨u, hu, mem_centralizer_singleton_iff.2 ?_⟩,
      ⟨v, hv, mem_centralizer_singleton_iff.2 ?_⟩), Subtype.ext rfl⟩
    · calc u * a = (a * u * a⁻¹) * a := by rw [h2]
        _ = a * u := by group
    · calc v * a = (a * v * a⁻¹) * a := by rw [h3]
        _ = a * v := by group
  have h := Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod] at h
  exact h.trans (Nat.mul_le_mul (card_inf_centralizer_le_two hX.card_W ha₁)
    (card_inf_centralizer_le_two hY.card_W ha₂))

theorem false_of_diagonal {G : Type*} [Group G] [Finite G] {X Y W₁ W₂ R : Subgroup G}
    {c₁ c₂ : G} (hX : A4Data X W₁ c₁) (hY : A4Data Y W₂ c₂)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hW₁R : W₁ ≤ R) (hW₂R : W₂ ≤ R)
    (hJX : thompsonJ R ≤ Subgroup.normalizer (X : Set G))
    (hJY : thompsonJ R ≤ Subgroup.normalizer (Y : Set G))
    (H₁ : ∀ a ∈ thompsonJ R, a ∈ Subgroup.centralizer (W₁ : Set G) → a ∈ X ⊔ Y)
    (H₂ : ∀ a ∈ thompsonJ R, a ∈ Subgroup.centralizer (W₂ : Set G) → a ∈ X ⊔ Y)
    (hJ : ⁅X, thompsonJ R⁆ = X) : False := by
  have hc : ∀ u ∈ W₁, ∀ v ∈ W₂, u * v = v * u := fun u hu v hv =>
    hXY u (hX.le hu) v (hY.le hv)
  have hmax : ∀ A : Subgroup G, IsMaxElemAbelian R A → A ≤ W₁ ⊔ W₂ := by
    intro A hA
    have hAJ : A ≤ thompsonJ R :=
      le_iSup₂ (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian R B) => B) A hA
    have h16 : 16 ≤ Nat.card A := (sixteen_le_card_sup hX hY hXY).trans
      (hA.2.2 (W₁ ⊔ W₂) (sup_le hW₁R hW₂R) (isElemAbelian_sup hX hY hXY))
    have hAXY : A ≤ X ⊔ Y := by
      intro a ha
      by_contra haXY
      have haJ : a ∈ thompsonJ R := hAJ ha
      have ha₁ : a ∉ centralizer (W₁ : Set G) := fun h => haXY (H₁ a haJ h)
      have ha₂ : a ∉ centralizer (W₂ : Set G) := fun h => haXY (H₂ a haJ h)
      have hAX : A ≤ normalizer (X : Set G) := hAJ.trans hJX
      have hAY : A ≤ normalizer (Y : Set G) := hAJ.trans hJY
      have hAW₁ : A ≤ normalizer (W₁ : Set G) := fun b hb =>
        normalizer_le_normalizer_of_a4 hX (hAX hb)
      have h1 := card_le_two_mul_card_inf_centralizer hX.card_W hX.sq_eq_one hX.comm hA.2.1 hAW₁
      have h2 : Nat.card ↥(A ⊓ centralizer (W₁ : Set G)) ≤ 4 := by
        refine le_trans (card_le_of_le ?_)
          (card_sup_inf_centralizer_le_four hX hY hXY (hAX ha) (hAY ha) ha₁ ha₂)
        intro b hb
        obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_sq_eq_one hX hY hXY
          (H₁ b (hAJ hb.1) hb.2) (hA.2.1.2 b hb.1)
        refine mem_inf.2 ⟨mul_mem_sup hu hv, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hA.2.1.1.is_comm.comm ⟨u * v, hb.1⟩ ⟨a, ha⟩)
      omega
    intro b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_sq_eq_one hX hY hXY (hAXY hb)
      (hA.2.1.2 b hb)
    exact mul_mem_sup hu hv
  have hJW : thompsonJ R ≤ W₁ ⊔ W₂ := iSup₂_le fun A hA => hmax A hA
  have hXW : X ≤ W₁ := by
    have hle : ⁅X, thompsonJ R⁆ ≤ W₁ := by
      rw [commutator_le]
      intro x hx j hj
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup hc (hJW hj)
      show x * (u * v) * x⁻¹ * (u * v)⁻¹ ∈ W₁
      have hxv' : x * v * x⁻¹ = v := by rw [hXY x hx v (hY.le hv)]; group
      have hxu : x * u * x⁻¹ ∈ W₁ := (mem_normalizer_iff.1 (hX.le_normalizer hx) u).1 hu
      have hcomm : x * (u * v) * x⁻¹ * (u * v)⁻¹ = (x * u * x⁻¹) * u⁻¹ := by
        calc x * (u * v) * x⁻¹ * (u * v)⁻¹
            = (x * u * x⁻¹) * (x * v * x⁻¹) * v⁻¹ * u⁻¹ := by group
          _ = (x * u * x⁻¹) * u⁻¹ := by rw [hxv']; group
      rw [hcomm]
      exact mul_mem hxu (inv_mem hu)
    rwa [hJ] at hle
  have h := card_le_of_le hXW
  rw [hX.card_X, hX.card_W] at h
  omega

end CFSG.Quasithin.S14110
