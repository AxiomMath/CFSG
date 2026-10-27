module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofLStar
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item218Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item2130SplitProof Item2130LStarProof

variable {G : Type} [Group G]

theorem sq_conj_eq_of_mem_normalizer {c x : G} (hc3 : c ^ 3 = 1)
    (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    (x * x) * c * (x * x)⁻¹ = c := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hx c).mp (Subgroup.mem_zpowers c))
  have hc3' : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  have hconj : ∀ m : ℤ, x * c ^ m * x⁻¹ = c ^ (k * m) := fun m => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hk, ← zpow_mul]
  have e : (x * x) * c * (x * x)⁻¹ = c ^ (k * k) := by
    calc (x * x) * c * (x * x)⁻¹ = x * (x * c * x⁻¹) * x⁻¹ := by group
      _ = x * c ^ k * x⁻¹ := by rw [← hk]
      _ = c ^ (k * k) := hconj k
  rw [e]
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · have hc1 : c = 1 := by
      have h : x * c * x⁻¹ = 1 := by
        rw [← hk, zpow_eq_zpow_emod k hc3', h0, zpow_zero]
      have : c = x⁻¹ * (x * c * x⁻¹) * x := by group
      rw [this, h]
      group
    rw [hc1, one_zpow]
  · rw [zpow_eq_zpow_emod (k * k) hc3', Int.mul_emod, h1]
    norm_num
  · rw [zpow_eq_zpow_emod (k * k) hc3', Int.mul_emod, h2]
    norm_num

theorem card_sup_eq_nine [Finite G] {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1) (hca : c ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hcomm : ∀ u ∈ Subgroup.zpowers c, ∀ v ∈ Subgroup.zpowers a, u * v = v * u :=
    fun u hu v hv => congrArg Subtype.val (hA.1.is_comm.comm
      ⟨u, Subgroup.zpowers_le.mpr hcA hu⟩ ⟨v, Subgroup.zpowers_le.mpr haA hv⟩)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [Sec13.zpowers_inf_eq_bot (hA.2 c hcA) hca, Subgroup.card_bot, mul_one,
    Sec13.card_zpowers_of_pow_three (hA.2 c hcA) hc1,
    Sec13.card_zpowers_of_pow_three (hA.2 a haA) ha1, sup_comm] at hcard
  exact hcard

theorem sameOn_sq_one [Finite G] {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a c x : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxa : x * a * x⁻¹ = a) (hxc : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hx4 : SameOn A ((x * x) * (x * x)) 1) : SameOn A (x * x) 1 := by
  set D : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers c with hD
  have hD9 : Nat.card D = 9 := card_sup_eq_nine hA haA hcA ha1 hca
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hcA)
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := by
    have hle : D ≤ D.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        change x * a * x⁻¹ ∈ D
        rw [hxa]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      · rw [Subgroup.mem_comap]
        change x * c * x⁻¹ ∈ D
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp hxc c).mp (Subgroup.mem_zpowers c))
    exact mem_normalizer_of_conj_mem fun y hy => hle hy
  have hQ : QuotHyp A D (Subgroup.zpowers x) :=
    { elem := hA, le := hDA, card := by rw [h27, hD9]
      normA := Subgroup.zpowers_le.mpr hxA, normB := Subgroup.zpowers_le.mpr hxD }
  have htriv : TrivQ A D (x * x) := hQ.trivQ_sq (Subgroup.mem_zpowers x)
  have hc2 : (x * x) * c * (x * x)⁻¹ = c := sq_conj_eq_of_mem_normalizer (hA.2 c hcA) hxc
  have ha2 : (x * x) * a * (x * x)⁻¹ = a := by
    calc (x * x) * a * (x * x)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by group
      _ = a := by rw [hxa, hxa]
  have hDC : D ≤ Subgroup.centralizer ({x * x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * (x * x) = ((x * x) * a * (x * x)⁻¹) * (x * x) := by rw [ha2]
        _ = (x * x) * a := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * (x * x) = ((x * x) * c * (x * x)⁻¹) * (x * x) := by rw [hc2]
        _ = (x * x) * c := by group
  have hsX : ∀ d ∈ D, (x * x) * d * (x * x)⁻¹ = d := fun d hd => by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hDC hd)
    calc (x * x) * d * (x * x)⁻¹ = d * (x * x) * (x * x)⁻¹ := by rw [← h1]
      _ = d := by group
  exact sameOn_one_of_unipotent (Subgroup.mul_mem _ hxA hxA) (fun d hd => hA.2 d (hDA hd))
    htriv hsX hx4

theorem sq_eq_one_of_mem_starOf [Finite G] {A L : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A)
    (hcA : c ∈ A) (ha1 : a ≠ 1) (hca : c ∉ Subgroup.zpowers a) (hLa : ∀ x ∈ L, x * a * x⁻¹ = a)
    (hLc : L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {φ : MulAut A} (hφ : φ ∈ starOf A L) (h4 : φ ^ 4 = 1) : φ ^ 2 = 1 := by
  obtain ⟨x, hxL, rfl⟩ := exists_lift hφ
  have h4' : A.normalizerMonoidHom (x * x * (x * x)) = A.normalizerMonoidHom 1 := by
    rw [map_one, map_mul, map_mul, ← h4, pow_succ, pow_succ, pow_succ, pow_one]
    simp only [mul_assoc]
  have hsq := sameOn_sq_one hA h27 haA hcA ha1 hca x.2 (hLa x hxL) (hLc ⟨hxL, x.2⟩)
    (sameOn_of_eq h4')
  have h2 := eq_of_sameOn (x := x * x) (y := 1) hsq
  rw [map_one, map_mul] at h2
  rw [sq]
  exact h2

theorem false_of_orderOf_four [Finite G] {A L : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A)
    (hcA : c ∈ A) (ha1 : a ≠ 1) (hca : c ∉ Subgroup.zpowers a) (hLa : ∀ x ∈ L, x * a * x⁻¹ = a)
    (hLc : L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {H : Type*} [Group H] (e : starOf A L ≃* H) {h : H} (hh : orderOf h = 4) : False := by
  have hord : orderOf ((e.symm h : starOf A L) : MulAut A) = 4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hh]
  have h4 : ((e.symm h : starOf A L) : MulAut A) ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have h2 := sq_eq_one_of_mem_starOf hA h27 haA hcA ha1 hca hLa hLc (e.symm h).2 h4
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at this
  norm_num at this

theorem conj_eq_of_mem_sup {x a c : G} (ha : x * a * x⁻¹ = a) (hc : x * c * x⁻¹ = c) :
    ∀ y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c, x * y * x⁻¹ = y := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * x = (x * a * x⁻¹) * x := by rw [ha]
        _ = x * a := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * x = (x * c * x⁻¹) * x := by rw [hc]
        _ = x * c := by group
  intro y hy
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [← h1]
    _ = y := by group

theorem false_of_kleinFour_fix [Finite G] {A D : Subgroup G} {s t g : G} (h : A4On A s t g)
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h81 : Nat.card A = 81) (hDA : D ≤ A)
    (hD9 : 9 ≤ Nat.card D) (hsD : ∀ y ∈ D, s * y * s⁻¹ = y) (htD : ∀ y ∈ D, t * y * t⁻¹ = y) :
    False := by
  have hcommB : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set F := A4On.fixST A s t with hF
  have hDF : D ≤ F := fun y hy => A4On.mem_fixST.mpr ⟨hDA hy, hsD y hy, htD y hy⟩
  have hFB : F ≤ A := inf_le_left
  have hu : s * t ∈ Subgroup.normalizer (A : Set G) := Subgroup.mul_mem _ h.hs h.ht
  set τf : G → G := fun y => y * (s * y * s⁻¹) * (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹)
    with hτf
  have hτB : ∀ y ∈ A, τf y ∈ A := fun y hy =>
    A.mul_mem (A.mul_mem (A.mul_mem hy (A4On.conj_mem h.hs hy)) (A4On.conj_mem h.ht hy))
      (A4On.conj_mem hu hy)
  have hcomm4 : ∀ {a b c d : G}, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      (a * b * c * d = b * a * d * c) ∧ (a * b * c * d = c * d * a * b) ∧
        (a * b * c * d = a * c * d * b) := by
    intro a b c d ha hb hc hd
    let _ : CommGroup A := { (inferInstance : Group A) with
      mul_comm := fun x y => Subtype.ext (hcommB _ x.2 _ y.2) }
    have key : ∀ x y z w : A, (x * y * z * w = y * x * w * z) ∧
        (x * y * z * w = z * w * x * y) ∧ (x * y * z * w = x * z * w * y) := fun x y z w =>
      ⟨by ac_rfl, by ac_rfl, by ac_rfl⟩
    obtain ⟨k1, k2, k3⟩ := key ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨congrArg Subtype.val k1, congrArg Subtype.val k2, congrArg Subtype.val k3⟩
  have hss : ∀ y ∈ A, (s * s) * y * (s * s)⁻¹ = y := fun y hy => by simpa using h.s2 y hy
  have htt : ∀ y ∈ A, (t * t) * y * (t * t)⁻¹ = y := fun y hy => by simpa using h.t2 y hy
  have hsst : ∀ y ∈ A, (s * (s * t)) * y * (s * (s * t))⁻¹ = t * y * t⁻¹ := fun y hy => by
    rw [show s * (s * t) * y * (s * (s * t))⁻¹ = (s * s) * (t * y * t⁻¹) * (s * s)⁻¹ by group,
      hss _ (A4On.conj_mem h.ht hy)]
  have hts : ∀ y ∈ A, (t * s) * y * (t * s)⁻¹ = (s * t) * y * (s * t)⁻¹ := fun y hy =>
    (h.st y hy).symm
  have hsts : ∀ y ∈ A, (s * t * s) * y * (s * t * s)⁻¹ = t * y * t⁻¹ := fun y hy => by
    rw [show s * t * s * y * (s * t * s)⁻¹ = s * ((t * s) * y * (t * s)⁻¹) * s⁻¹ by group,
      hts y hy, show s * ((s * t) * y * (s * t)⁻¹) * s⁻¹ = s * (s * t) * y * (s * (s * t))⁻¹ by
        group, hsst y hy]
  have hstt : ∀ y ∈ A, (s * t * t) * y * (s * t * t)⁻¹ = s * y * s⁻¹ := fun y hy => by
    rw [show s * t * t * y * (s * t * t)⁻¹ = s * ((t * t) * y * (t * t)⁻¹) * s⁻¹ by group,
      htt y hy]
  have htst : ∀ y ∈ A, (t * (s * t)) * y * (t * (s * t))⁻¹ = s * y * s⁻¹ := h.tst
  have hτF : ∀ y ∈ A, τf y ∈ F := by
    intro y hy
    have hsy := A4On.conj_mem h.hs hy
    have hty := A4On.conj_mem h.ht hy
    have huy := A4On.conj_mem hu hy
    refine A4On.mem_fixST.mpr ⟨hτB y hy, ?_, ?_⟩
    · calc s * τf y * s⁻¹ = (s * y * s⁻¹) * ((s * s) * y * (s * s)⁻¹) *
            ((s * t) * y * (s * t)⁻¹) * ((s * (s * t)) * y * (s * (s * t))⁻¹) := by
            simp only [hτf]; group
        _ = (s * y * s⁻¹) * y * ((s * t) * y * (s * t)⁻¹) * (t * y * t⁻¹) := by
            rw [hss y hy, hsst y hy]
        _ = τf y := (hcomm4 hsy hy huy hty).1
    · calc t * τf y * t⁻¹ = (t * y * t⁻¹) * ((t * s) * y * (t * s)⁻¹) *
            ((t * t) * y * (t * t)⁻¹) * ((t * (s * t)) * y * (t * (s * t))⁻¹) := by
            simp only [hτf]; group
        _ = (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹) * y * (s * y * s⁻¹) := by
            rw [hts y hy, htt y hy, htst y hy]
        _ = τf y := (hcomm4 hty huy hy hsy).2.1
  let τ : A →* A := MonoidHom.mk' (fun y => ⟨τf y, hτB y y.2⟩) (by
    intro y z
    apply Subtype.ext
    let _ : CommGroup A := { (inferInstance : Group A) with
      mul_comm := fun x y => Subtype.ext (hcommB _ x.2 _ y.2) }
    have e : ∀ x : G, ∀ a b : A, x * ((a : G) * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) :=
      fun x a b => by group
    have hsy : s * (y : G) * s⁻¹ ∈ A := A4On.conj_mem h.hs y.2
    have hsz : s * (z : G) * s⁻¹ ∈ A := A4On.conj_mem h.hs z.2
    have hty : t * (y : G) * t⁻¹ ∈ A := A4On.conj_mem h.ht y.2
    have htz : t * (z : G) * t⁻¹ ∈ A := A4On.conj_mem h.ht z.2
    have huy : (s * t) * (y : G) * (s * t)⁻¹ ∈ A := A4On.conj_mem hu y.2
    have huz : (s * t) * (z : G) * (s * t)⁻¹ ∈ A := A4On.conj_mem hu z.2
    have key : ∀ y₀ z₀ y₁ z₁ y₂ z₂ y₃ z₃ : A,
        (y₀ * z₀) * (y₁ * z₁) * (y₂ * z₂) * (y₃ * z₃) =
          (y₀ * y₁ * y₂ * y₃) * (z₀ * z₁ * z₂ * z₃) := fun _ _ _ _ _ _ _ _ => by ac_rfl
    have := congrArg Subtype.val (key y z ⟨_, hsy⟩ ⟨_, hsz⟩ ⟨_, hty⟩ ⟨_, htz⟩ ⟨_, huy⟩
      ⟨_, huz⟩)
    simp only [Subgroup.coe_mul] at this
    change τf ((y : G) * z) = τf y * τf z
    simp only [hτf, e s y z, e t y z, e (s * t) y z]
    exact this)
  have hτapp : ∀ y : A, ((τ y : A) : G) = τf y := fun _ => rfl
  have hτFid : ∀ y ∈ F, τf y = y := by
    intro y hy
    obtain ⟨hyB, hsy, hty⟩ := A4On.mem_fixST.mp hy
    have huy : (s * t) * y * (s * t)⁻¹ = y := by
      rw [show s * t * y * (s * t)⁻¹ = s * (t * y * t⁻¹) * s⁻¹ by group, hty, hsy]
    simp only [hτf, hsy, hty, huy]
    calc y * y * y * y = y ^ 3 * y := by rw [pow_three]; simp only [mul_assoc]
      _ = y := by rw [hA.2 y hyB, one_mul]
  set Y : Subgroup G := τ.ker.map A.subtype with hY
  have hYB : Y ≤ A := Subgroup.map_subtype_le _
  have hmemY : ∀ y, y ∈ Y ↔ y ∈ A ∧ τf y = 1 := by
    intro y
    constructor
    · rintro ⟨⟨y', hy'⟩, hk, rfl⟩
      exact ⟨hy', (hτapp _).symm.trans (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))⟩
    · rintro ⟨hy, hτ1⟩
      exact ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr (Subtype.ext ((hτapp _).trans hτ1)), rfl⟩
  have hYs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
    intro y hy
    obtain ⟨hyB, hτ1⟩ := (hmemY y).mp hy
    have hsy := A4On.conj_mem h.hs hyB
    have hty := A4On.conj_mem h.ht hyB
    have huy := A4On.conj_mem hu hyB
    refine (hmemY _).mpr ⟨hsy, ?_⟩
    calc τf (s * y * s⁻¹) = (s * y * s⁻¹) * ((s * s) * y * (s * s)⁻¹) *
          ((t * s) * y * (t * s)⁻¹) * ((s * t * s) * y * (s * t * s)⁻¹) := by
          simp only [hτf]; group
      _ = (s * y * s⁻¹) * y * ((s * t) * y * (s * t)⁻¹) * (t * y * t⁻¹) := by
          rw [hss y hyB, hts y hyB, hsts y hyB]
      _ = τf y := (hcomm4 hsy hyB huy hty).1
      _ = 1 := hτ1
  have hYt : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    intro y hy
    obtain ⟨hyB, hτ1⟩ := (hmemY y).mp hy
    have hsy := A4On.conj_mem h.hs hyB
    have hty := A4On.conj_mem h.ht hyB
    have huy := A4On.conj_mem hu hyB
    refine (hmemY _).mpr ⟨hty, ?_⟩
    calc τf (t * y * t⁻¹) = (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹) *
          ((t * t) * y * (t * t)⁻¹) * ((s * t * t) * y * (s * t * t)⁻¹) := by
          simp only [hτf]; group
      _ = (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹) * y * (s * y * s⁻¹) := by
          rw [htt y hyB, hstt y hyB]
      _ = τf y := (hcomm4 hty huy hyB hsy).2.1
      _ = 1 := hτ1
  have hYg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro y hy
    obtain ⟨hyB, hτ1⟩ := (hmemY y).mp hy
    have hsy := A4On.conj_mem h.hs hyB
    have hty := A4On.conj_mem h.ht hyB
    have huy := A4On.conj_mem hu hyB
    have hgy := A4On.conj_mem h.hg hyB
    refine (hmemY _).mpr ⟨hgy, ?_⟩
    have e1 : s * (g * y * g⁻¹) * s⁻¹ = g * ((s * t) * y * (s * t)⁻¹) * g⁻¹ := by
      rw [← h.gst _ hgy]
      group
    have e2 : t * (g * y * g⁻¹) * t⁻¹ = g * (s * y * s⁻¹) * g⁻¹ := by
      rw [← h.gs _ hgy]
      group
    have e3 : (s * t) * (g * y * g⁻¹) * (s * t)⁻¹ = g * (t * y * t⁻¹) * g⁻¹ := by
      rw [← h.gt _ hgy]
      group
    calc τf (g * y * g⁻¹) = (g * y * g⁻¹) * (s * (g * y * g⁻¹) * s⁻¹) *
          (t * (g * y * g⁻¹) * t⁻¹) * ((s * t) * (g * y * g⁻¹) * (s * t)⁻¹) := rfl
      _ = g * (y * ((s * t) * y * (s * t)⁻¹) * (s * y * s⁻¹) * (t * y * t⁻¹)) * g⁻¹ := by
          rw [e1, e2, e3]
          group
      _ = g * τf y * g⁻¹ := by rw [(hcomm4 hyB huy hsy hty).2.2]
      _ = 1 := by rw [hτ1]; group
  have hsY := mem_normalizer_of_conj_mem hYs
  have htY := mem_normalizer_of_conj_mem hYt
  have hgY := mem_normalizer_of_conj_mem hYg
  have hYof : ∀ y ∈ A, (τf y)⁻¹ * y ∈ Y := by
    intro y hy
    refine (hmemY _).mpr ⟨A.mul_mem (A.inv_mem (hτB y hy)) hy, ?_⟩
    have e : ((τ ((⟨τf y, hτB y hy⟩ : A)⁻¹ * ⟨y, hy⟩) : A) : G) = (τf (τf y))⁻¹ * τf y := by
      rw [map_mul, map_inv]
      rfl
    rw [hτFid _ (hτF y hy), inv_mul_cancel] at e
    exact e
  have hsplit : ∀ x : G, (∀ f ∈ F, x * f * x⁻¹ = f) → SameOn Y x 1 → SameOn A x 1 := by
    intro x hxF hxY
    rw [sameOn_one_iff] at hxY ⊢
    intro y hy
    have h1 := hxF _ (hτF y hy)
    have h2 := hxY _ (hYof y hy)
    calc x * y * x⁻¹ = (x * τf y * x⁻¹) * (x * ((τf y)⁻¹ * y) * x⁻¹) := by group
      _ = τf y * ((τf y)⁻¹ * y) := by rw [h1, h2]
      _ = y := by group
  have hsF : ∀ f ∈ F, s * f * s⁻¹ = f := fun f hf => (A4On.mem_fixST.mp hf).2.1
  have htF : ∀ f ∈ F, t * f * t⁻¹ = f := fun f hf => (A4On.mem_fixST.mp hf).2.2
  have hstF : ∀ f ∈ F, (s * t) * f * (s * t)⁻¹ = f := fun f hf => by
    rw [show s * t * f * (s * t)⁻¹ = s * (t * f * t⁻¹) * s⁻¹ by group, htF f hf, hsF f hf]
  have hs1 : ¬ SameOn Y s 1 := fun hY => h.s1 (hsplit s hsF hY)
  have ht1 : ¬ SameOn Y t 1 := fun hY => h.t1 (hsplit t htF hY)
  have hst1 : ¬ SameOn Y (s * t) 1 := fun hY => h.st1 (hsplit (s * t) hstF hY)
  have hYk : Nat.card Y = Nat.card τ.ker := Subgroup.card_map_of_injective A.subtype_injective
  have hrange : Nat.card τ.range = Nat.card F := by
    have heq : τ.range = F.subgroupOf A := by
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        exact hτF y y.2
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        refine ⟨y, Subtype.ext ?_⟩
        rw [hτapp]
        exact hτFid _ hy
    rw [heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFB).toEquiv
  have hmul : Nat.card τ.ker * Nat.card τ.range = 81 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, h81]
  have hFD : Nat.card D ≤ Nat.card F := Subgroup.card_le_of_le hDF
  have hdvd : Nat.card Y ∣ 3 ^ 4 := by
    rw [show 3 ^ 4 = 81 by norm_num, ← hmul, hYk]
    exact Dvd.intro _ rfl
  have hYle : Nat.card Y ≤ 9 := by
    rw [hYk]
    have hpos : 0 < Nat.card τ.ker := Nat.card_pos
    nlinarith
  have hYe : CFSG.Assembly.IsElemAbelian 3 Y := elemAbelian_of_le hA hYB
  obtain ⟨k, hk, hYk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  ·
    apply hs1
    rw [sameOn_one_iff]
    intro y hy
    have hY1 : Y = ⊥ := Subgroup.eq_bot_of_card_eq Y (by simpa using hYk')
    rw [hY1, Subgroup.mem_bot] at hy
    rw [hy]
    group
  ·
    have hQ : QuotHyp Y ⊥ (Subgroup.closure ({s, t, g} : Set G)) :=
      { elem := hYe, le := bot_le, card := by rw [hYk', Subgroup.card_bot]; norm_num
        normA := closure_le_normalizer hsY htY hgY
        normB := fun x _ => by
          rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G)]
          trivial }
    obtain ⟨hqs, -⟩ := trivQ_of_quot hQ (h.g3.mono hYB) (h.gs.mono hYB) (h.gt.mono hYB)
    apply hs1
    rw [sameOn_one_iff]
    intro y hy
    have := hqs y hy
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  ·
    exact false_of_kleinFour_nine hYe (by simpa using hYk') hsY htY hgY (h.s2.mono hYB)
      (h.t2.mono hYB) (h.st.mono hYB) hs1 ht1 hst1 (h.gs.mono hYB) (h.gt.mono hYB)
  · omega
  · omega

theorem false_of_perm_fix [Finite G] {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h81 : Nat.card A = 81) {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) (hLa : ∀ x ∈ L, x * a * x⁻¹ = a)
    (hLc : L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (ψ : Equiv.Perm (Fin 4) →* MulAut A) (hψinj : Function.Injective ψ)
    (hψmem : ∀ x, ψ x ∈ starOf A L) : False := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := perm_relations
  obtain ⟨ls, hlsL, hls⟩ := exists_lift (hψmem permS)
  obtain ⟨lt, hltL, hlt⟩ := exists_lift (hψmem permT)
  obtain ⟨lg, hlgL, hlg⟩ := exists_lift (hψmem permG)
  set nmh := A.normalizerMonoidHom
  have rel : ∀ (x y : Subgroup.normalizer (A : Set G)), nmh x = nmh y → SameOn A x y :=
    fun x y h => sameOn_of_eq h
  have nontriv : ∀ (x : Subgroup.normalizer (A : Set G)), nmh x ≠ 1 → ¬ SameOn A x 1 := by
    intro x hx h
    apply hx
    rw [← map_one nmh]
    exact eq_of_sameOn (x := x) (y := 1) h
  have hA4 : A4On A ls lt lg := by
    refine
      { hs := ls.2, ht := lt.2, hg := lg.2
        s2 := rel (ls * ls) 1 ?_, t2 := rel (lt * lt) 1 ?_, st := rel (ls * lt) (lt * ls) ?_
        s1 := nontriv ls ?_, t1 := nontriv lt ?_
        st1 := nontriv (ls * lt) ?_
        g3 := rel (lg * lg * lg) 1 ?_, gs := rel (lg * ls * lg⁻¹) lt ?_
        gt := rel (lg * lt * lg⁻¹) (ls * lt) ?_ }
    · rw [map_mul, hls, ← map_mul, r1, map_one, map_one]
    · rw [map_mul, hlt, ← map_mul, r2, map_one, map_one]
    · rw [map_mul, map_mul, hls, hlt, ← map_mul, ← map_mul, r3]
    · rw [hls, ← map_one ψ]
      exact fun h => r4 (hψinj h)
    · rw [hlt, ← map_one ψ]
      exact fun h => r5 (hψinj h)
    · rw [map_mul, hls, hlt, ← map_mul, ← map_one ψ]
      exact fun h => r6 (hψinj h)
    · rw [map_mul, map_mul, hlg, ← map_mul, ← map_mul, r7, map_one, map_one]
    · rw [map_mul, map_mul, map_inv, hlg, hls, hlt, ← map_inv, ← map_mul, ← map_mul, r8]
    · rw [map_mul, map_mul, map_inv, map_mul, hlg, hls, hlt, ← map_inv, ← map_mul, ← map_mul,
        ← map_mul, r9]
  have hcle : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hN : ∀ x : Subgroup.normalizer (A : Set G), (x : G) ∈ L →
      (x : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx => hLc ⟨hx, x.2⟩
  have hQ : QuotHyp (Subgroup.zpowers c) ⊥
      (Subgroup.closure ({(ls : G), (lt : G), (lg : G)} : Set G)) :=
    { elem := elemAbelian_of_le hA hcle
      le := bot_le
      card := by rw [Sec13.card_zpowers_of_pow_three (hA.2 c hcA) hc1, Subgroup.card_bot]
      normA := closure_le_normalizer (hN ls hlsL) (hN lt hltL) (hN lg hlgL)
      normB := fun x _ => by
        rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G)]
        trivial }
  obtain ⟨hqs, hqt⟩ := trivQ_of_quot hQ (hA4.g3.mono hcle) (hA4.gs.mono hcle)
    (hA4.gt.mono hcle)
  have hfix : ∀ {x : G}, TrivQ (Subgroup.zpowers c) ⊥ x → x * c * x⁻¹ = c := fun hq => by
    have := hq c (Subgroup.mem_zpowers c)
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  have hD9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    card_sup_eq_nine hA haA hcA ha1 hca
  exact false_of_kleinFour_fix hA4 hA h81
    (sup_le (Subgroup.zpowers_le.mpr haA) hcle) hD9.ge
    (conj_eq_of_mem_sup (hLa ls hlsL) (hfix hqs)) (conj_eq_of_mem_sup (hLa lt hltL) (hfix hqt))

end CFSG.RankThree.PartTwo.Sec21.Item218Res2Proof
