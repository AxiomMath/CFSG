module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25M

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem card_inf_centralizer_modEq [Finite G] {p : ℕ} [Fact p.Prime] {S P : Subgroup G}
    (hP : IsPGroup p P) (hPS : P ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card ↥(S ⊓ Subgroup.centralizer (P : Set G)) ≡ Nat.card S [MOD p] := by
  let := SignalizerFunctor.Helpers.conjugationAction P S hPS
  have hmod := hP.card_modEq_card_fixedPoints S
  have heq : Nat.card (MulAction.fixedPoints P S) =
      Nat.card ↥(S ⊓ Subgroup.centralizer (P : Set G)) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1, s.1.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        invFun := fun s => ⟨⟨s, s.2.1⟩, fun x => Subtype.ext ?_⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    · have h : x * (s.1 : G) * x⁻¹ = s.1 := congrArg Subtype.val (s.2 ⟨x, hx⟩)
      calc x * (s.1 : G) = x * s.1 * x⁻¹ * x := by group
        _ = s.1 * x := by rw [h]
    · change (x : G) * s * (x : G)⁻¹ = s
      rw [Subgroup.mem_centralizer_iff.mp s.2.2 x x.2, mul_inv_cancel_right]
  rw [heq] at hmod
  exact hmod.symm

theorem isPGroup_zpowers_of_pow {X : Type*} [Group X] {p : ℕ} [hp : Fact p.Prime] {x : X}
    (hx : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])

theorem card_inf_centralizer_elem_modEq [Finite G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    {x : G} (hx : x ^ p = 1) (hxS : x ∈ Subgroup.normalizer (S : Set G)) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) ≡ Nat.card S [MOD p] := by
  have h := card_inf_centralizer_modEq (isPGroup_zpowers_of_pow hx)
    ((Subgroup.zpowers_le).mpr hxS)
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem eq_one_of_mem_ker {W W' : Type*} [Group W] [Group W'] (ψ : W →* W')
    (hker : IsPGroup 2 ψ.ker) {w : W} (hw : ψ w = 1) (hw3 : w ^ 3 = 1) : w = 1 := by
  obtain ⟨k, hk⟩ := hker ⟨w, hw⟩
  have h2 : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨h2, hw3⟩
  rwa [hcop, pow_one] at this

theorem pow_three_of_mem_zpowers {W : Type*} [Group W] {c z : W} (hc : c ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers c) : z ^ 3 = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

theorem exists_conj_of_map_eq {W W' : Type*} [Group W] [Finite W] [Group W'] (ψ : W →* W')
    (hker : IsPGroup 2 ψ.ker) {c₁ c₂ : W} (h₁ : c₁ ^ 3 = 1) (h₂ : c₂ ^ 3 = 1)
    (hψ : ψ c₁ = ψ c₂) : ∃ g : W, g * c₁ * g⁻¹ = c₂ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : ψ c₁ = 1
  · refine ⟨1, ?_⟩
    rw [eq_one_of_mem_ker ψ hker h1 h₁, eq_one_of_mem_ker ψ hker (hψ ▸ h1) h₂]
    group
  set P : Subgroup W := (Subgroup.zpowers (ψ c₁)).comap ψ with hP
  have hc₁P : c₁ ∈ P := Subgroup.mem_zpowers _
  have hc₂P : c₂ ∈ P := by
    show ψ c₂ ∈ Subgroup.zpowers (ψ c₁)
    rw [← hψ]
    exact Subgroup.mem_zpowers _
  set ψP : ↥P →* W' := ψ.comp P.subtype with hψP
  have hrange : ψP.range = Subgroup.zpowers (ψ c₁) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨c₁, hc₁P⟩, rfl⟩
  have hord : orderOf (ψ c₁) = 3 := by
    have hd : orderOf (ψ c₁) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h₁, map_one])
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have hkerP : IsPGroup 2 ψP.ker := by
    rw [hψP, ← MonoidHom.comap_ker]
    exact hker.comap_of_injective P.subtype P.subtype_injective
  obtain ⟨k, hk⟩ := hkerP.exists_card_eq
  have hcardP : Nat.card P = 2 ^ k * 3 := by
    rw [← Subgroup.card_ker_mul_card_range ψP, hk, hrange, Nat.card_zpowers, hord]
  have hsyl : ∀ c : ↥P, c ^ 3 = 1 → c ≠ 1 → IsPGroup 3 (Subgroup.zpowers c) ∧
      ¬ 3 ∣ (Subgroup.zpowers c).index := by
    intro c hc hc1
    have hoc : orderOf c = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc1
      · exact h
    refine ⟨isPGroup_zpowers_of_pow hc, fun h3 => ?_⟩
    have hmul := (Subgroup.zpowers c).card_mul_index
    rw [Nat.card_zpowers, hoc, hcardP] at hmul
    have hidx : (Subgroup.zpowers c).index = 2 ^ k := by omega
    rw [hidx] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hne : ∀ c : ↥P, ψP c ≠ 1 → c ≠ 1 := fun c hc h => hc (by rw [h, map_one])
  have hc₁' : (⟨c₁, hc₁P⟩ : ↥P) ^ 3 = 1 := Subtype.ext h₁
  have hc₂' : (⟨c₂, hc₂P⟩ : ↥P) ^ 3 = 1 := Subtype.ext h₂
  obtain ⟨hS₁, hS₁i⟩ := hsyl _ hc₁' (hne _ h1)
  obtain ⟨hS₂, hS₂i⟩ := hsyl _ hc₂' (hne _ (by show ψ c₂ ≠ 1; rw [← hψ]; exact h1))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P (hS₁.toSylow hS₁i) (hS₂.toSylow hS₂i)
  have hmem : (⟨c₂, hc₂P⟩ : ↥P) ∈ ((g • hS₁.toSylow hS₁i : Sylow 3 ↥P) : Subgroup ↥P) := by
    rw [hg]
    exact Subgroup.mem_zpowers _
  rw [Sylow.coe_subgroup_smul] at hmem
  obtain ⟨y, hy, hyc⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp hmem
  have hy3 : y ^ 3 = 1 := pow_three_of_mem_zpowers hc₁' hy
  have hyc' : g * y * g⁻¹ = ⟨c₂, hc₂P⟩ := by
    rw [← hyc, MulAut.smul_def, MulAut.conj_apply]
  have hgc : ψP g * ψ c₁ = ψ c₁ * ψP g := by
    have hg' : ψ (g : W) ∈ Subgroup.zpowers (ψ c₁) := g.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg'
    show ψ (g : W) * ψ c₁ = ψ c₁ * ψ (g : W)
    rw [← hj]
    exact (Commute.zpow_left (Commute.refl _) j).eq
  have hψy : ψP y = ψ c₁ := by
    have e1 := congrArg ψP hyc'
    rw [map_mul, map_mul, map_inv] at e1
    have e2 : ψP ⟨c₂, hc₂P⟩ = ψ c₁ := hψ.symm
    rw [e2] at e1
    calc ψP y = (ψP g)⁻¹ * (ψP g * ψP y * (ψP g)⁻¹) * ψP g := by group
      _ = (ψP g)⁻¹ * ψ c₁ * ψP g := by rw [e1]
      _ = (ψP g)⁻¹ * (ψP g * ψ c₁) := by rw [mul_assoc, ← hgc]
      _ = ψ c₁ := by group
  have hyc₁ : y = ⟨c₁, hc₁P⟩ := by
    have hw : ψP (y * (⟨c₁, hc₁P⟩ : ↥P)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψy]
      exact mul_inv_cancel _
    have hw3 : (y * (⟨c₁, hc₁P⟩ : ↥P)⁻¹) ^ 3 = 1 :=
      pow_three_of_mem_zpowers hc₁'
        (Subgroup.mul_mem _ hy (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
    have := eq_one_of_mem_ker ψP hkerP hw hw3
    exact mul_inv_eq_one.mp this
  refine ⟨(g : W), ?_⟩
  have := congrArg Subtype.val hyc'
  rw [hyc₁] at this
  simpa using this

theorem two_elem_of_mem_centralizer
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) {y : G}
    (hyY : y ∈ YY L U V) (hyA : y ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G)) :
    ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, _, ρ, -, hker, hρ, -⟩ := exists_Y_rep h1222 h1220 hH hNE hC hn3
  have h1 : (⟨y, hyY⟩ : ↥(YY L U V)) ∈ ρ.ker := (hρ _).mpr hyA
  rw [hker] at h1
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥(YY L U V)) ⟨_, h1⟩
  have h2 : (⟨y, hyY⟩ : ↥(YY L U V)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ⟨k, by simpa using congrArg Subtype.val h2⟩

theorem eq_one_of_mem_centralizer
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) {y : G}
    (hyY : y ∈ YY L U V) (hyA : y ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G))
    (hy : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := two_elem_of_mem_centralizer h1222 h1220 hH hNE hC hn3 hyY hyA
  have hd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf y) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hy)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd)

theorem exists_mem_Y_orderOf
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4) {q : ℕ}
    (hq : q.Prime) (hq168 : q ∣ 168) : ∃ y ∈ YY L U V, orderOf y = q := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, _, ρ, hsurj, -, -, ⟨eQ⟩⟩ := exists_Y_rep h1222 h1220 hH hNE hC (by omega)
  subst hn4
  have hQ : Nat.card Q = 168 := by
    rw [Nat.card_congr eQ.toEquiv]
    exact card_sl_three_zmod_two
  have hdvd : q ∣ Nat.card ↥(YY L U V) := by
    rw [← Subgroup.card_ker_mul_card_range ρ, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, hQ]
    exact dvd_mul_of_dvd_right hq168 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hdvd
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem YY_le_normalizer {L U V : Subgroup G} :
    YY L U V ≤ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
  (oTwoUpper_le _).trans inf_le_right

theorem card_inf_V_centralizer_three
    (h1222 : Stmt12_2_2)
    (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p)
    (hn4 : n = 4) {y : G} (hyY : y ∈ YY L U V) (hy : orderOf y = 3) :
    Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hmod := card_inf_centralizer_elem_modEq (S := U ⊓ V) hy3 (YY_le_normalizer hyY)
  rw [hA] at hmod
  have hdvd : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 8 :=
    hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) ≠ 8 := by
    intro h8
    have heq : U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G) = U ⊓ V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hA])
    have hyA : y ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [← heq] at ha
      exact Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have := eq_one_of_mem_centralizer h1222 h1220 hH hNE hC (by omega) hyY hyA
      (by rw [hy]; decide)
    rw [this, orderOf_one] at hy
    omega
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases hc : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) <;> simp_all

theorem eq_inf_V_of_le
    (h1222 : Stmt12_2_2) (h1220 : Stmt12_2_20) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn4 : n = 4)
    {B : Subgroup G} (hBA : B ≤ U ⊓ V) (hB : B ≠ ⊥)
    (hYB : YY L U V ≤ Subgroup.normalizer (B : Set G)) : B = U ⊓ V := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hA : Nat.card ↥(U ⊓ V) = 8 := by rw [card_inf_V hC, hn4]; norm_num
  obtain ⟨y, hyY, hy⟩ := exists_mem_Y_orderOf h1222 h1220 hH hNE hC hn4 (q := 7) (by norm_num)
    (by norm_num)
  have hy7 : y ^ 7 = 1 := hy ▸ pow_orderOf_eq_one y
  have hCA : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) = 1 := by
    have hmod := card_inf_centralizer_elem_modEq (S := U ⊓ V) hy7 (YY_le_normalizer hyY)
    rw [hA] at hmod
    have hdvd : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 8 :=
      hA ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) ≠ 8 := by
      intro h8
      have heq : U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G) = U ⊓ V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hA])
      have hyA : y ∈ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [← heq] at ha
        exact Subgroup.mem_centralizer_singleton_iff.mp ha.2
      have := eq_one_of_mem_centralizer h1222 h1220 hH hNE hC (by omega) hyY hyA
        (by rw [hy]; decide)
      rw [this, orderOf_one] at hy
      omega
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases hc : Nat.card ↥(U ⊓ V ⊓ Subgroup.centralizer ({y} : Set G)) <;> simp_all
  have hCB : Nat.card ↥(B ⊓ Subgroup.centralizer ({y} : Set G)) = 1 := by
    have hle : Nat.card ↥(B ⊓ Subgroup.centralizer ({y} : Set G)) ≤ 1 :=
      hCA ▸ Subgroup.card_le_of_le (inf_le_inf_right _ hBA)
    have := Nat.card_pos (α := ↥(B ⊓ Subgroup.centralizer ({y} : Set G)))
    omega
  have hmod := card_inf_centralizer_elem_modEq (S := B) hy7 (hYB hyY)
  rw [hCB] at hmod
  have hdvd : Nat.card B ∣ 8 := hA ▸ Subgroup.card_dvd_of_le hBA
  have hB1 : Nat.card B ≠ 1 := fun h1 => hB (Subgroup.eq_bot_of_card_eq B h1)
  have h8 : Nat.card B = 8 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases hc : Nat.card B <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [h8, hA])

end Lem25

end CFSG.Quasithin.H13
