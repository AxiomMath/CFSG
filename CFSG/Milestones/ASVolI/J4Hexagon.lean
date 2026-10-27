module

public import CFSG.Milestones.ASVolI.J4
public import CFSG.Quasithin.Recognition.RuTypeJ47Sig
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Co1.Module.TwoBCert

public section

namespace CFSG.ASVolI

open CFSG.Open

section BurnsideJ410Basic

variable {G : Type} [Group G]

theorem burnsideJ410_pow_five {X : Subgroup G} (h : Nat.card X = 5) {x : G} (hx : x ∈ X) :
    x ^ 5 = 1 := by
  have h1 := Subgroup.orderOf_dvd_natCard X hx
  rw [h] at h1
  exact orderOf_dvd_iff_pow_eq_one.mp h1

theorem burnsideJ410_eq_one_of_sq {x : G} (h5 : x ^ 5 = 1) (h2 : x * x = 1) : x = 1 := by
  have h2' : x ^ 2 = 1 := by rw [pow_two]; exact h2
  have := (pow_gcd_eq_one (a := x)).mpr ⟨h2', h5⟩
  rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this

theorem burnsideJ410_exists_ne_one {X : Subgroup G} (h : Nat.card X = 5) : ∃ x ∈ X, x ≠
    1 := by
  obtain ⟨x, hx, -, hx1, -⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five h
  exact ⟨x, hx, hx1⟩

theorem burnsideJ410_comm_of_card_five {X : Subgroup G} (h : Nat.card X = 5) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  obtain ⟨x, -, -, -, hx⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five h
  intro a ha b hb
  obtain ⟨m, rfl⟩ := hx a ha
  obtain ⟨n, rfl⟩ := hx b hb
  exact ((Commute.refl x).pow_pow m n).eq

theorem burnsideJ410_ne_of_cent_inv {X Y : Subgroup G} {a : G} (hX : Nat.card X = 5)
    (hXa : ∀ x ∈ X, a * x * a⁻¹ = x) (hYa : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) : X ≠ Y := by
  intro hXY
  obtain ⟨x, hxX, hx1⟩ := burnsideJ410_exists_ne_one hX
  apply hx1
  have hxY : x ∈ Y := hXY ▸ hxX
  have h1 := hXa x hxX
  have h2 := hYa x hxY
  have h3 : x = x⁻¹ := h1.symm.trans h2
  refine burnsideJ410_eq_one_of_sq (burnsideJ410_pow_five hX hxX) ?_
  calc x * x = x * x⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel x

open scoped Pointwise in
theorem burnsideJ410_mem_sup {S T : Subgroup G} (hST : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a)
    {g : G}
    (hg : g ∈ S ⊔ T) : ∃ s ∈ S, ∃ t ∈ T, s * t = g := by
  have hle : S ≤ Subgroup.normalizer (T : Set G) := fun s hs => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : s * h * s⁻¹ = h := by rw [hST s hs h hh]; group
      rw [this]; exact hh
    · intro hh
      have h1 : s⁻¹ * (s * h * s⁻¹) = (s * h * s⁻¹) * s⁻¹ := hST s⁻¹ (inv_mem hs) _ hh
      have : h = s * h * s⁻¹ := by
        calc h = s⁻¹ * (s * h * s⁻¹) * s := by group
          _ = ((s * h * s⁻¹) * s⁻¹) * s := by rw [h1]
          _ = s * h * s⁻¹ := by group
      rw [this]; exact hh
  have := Subgroup.coe_mul_of_left_le_normalizer_right S T hle
  have hg' : g ∈ ((S : Set G) * (T : Set G)) := by
    rw [← this]; exact hg
  obtain ⟨s, hs, t, ht, e⟩ := Set.mem_mul.mp hg'
  exact ⟨s, hs, t, ht, e⟩

theorem burnsideJ410_comm_sup {S T : Subgroup G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hST : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) :
    ∀ g ∈ S ⊔ T, ∀ h ∈ S ⊔ T, g * h = h * g := by
  intro g hg h hh
  obtain ⟨s1, hs1, t1, ht1, rfl⟩ := burnsideJ410_mem_sup hST hg
  obtain ⟨s2, hs2, t2, ht2, rfl⟩ := burnsideJ410_mem_sup hST hh
  have e1 : t1 * s2 = s2 * t1 := (hST s2 hs2 t1 ht1).symm
  have e2 : t2 * s1 = s1 * t2 := (hST s1 hs1 t2 ht2).symm
  calc s1 * t1 * (s2 * t2) = s1 * (t1 * s2) * t2 := by group
    _ = s1 * (s2 * t1) * t2 := by rw [e1]
    _ = (s1 * s2) * (t1 * t2) := by group
    _ = (s2 * s1) * (t2 * t1) := by rw [hS s1 hs1 s2 hs2, hT t1 ht1 t2 ht2]
    _ = s2 * (s1 * t2) * t1 := by group
    _ = s2 * (t2 * s1) * t1 := by rw [e2]
    _ = s2 * t2 * (s1 * t1) := by group

theorem burnsideJ410_card_25 {c : ℕ} (h5 : 5 ∣ c) (h125 : c ∣ 125) (hne5 : c ≠ 5)
    (hne125 : c ≠ 125) : c = 25 := by
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
    (show c ∣ 5 ^ 3 by simpa using h125)
  interval_cases k
  · rw [hk] at h5; norm_num at h5
  · exact absurd (by simpa using hk) hne5
  · simpa using hk
  · exact absurd (by simpa using hk) hne125

theorem burnsideJ410_card_25' {c : ℕ} (h25 : 25 ∣ c) (h125 : c ∣ 125) (hne125 : c ≠ 125) :
    c = 25 := by
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
    (show c ∣ 5 ^ 3 by simpa using h125)
  interval_cases k
  · rw [hk] at h25; norm_num at h25
  · rw [hk] at h25; norm_num at h25
  · simpa using hk
  · exact absurd (by simpa using hk) hne125

theorem burnsideJ410_nc [Finite G] {P Z X Y : Subgroup G} {t : G}
    (hP : Nat.card P = 125) (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hZP : Z ≤ P) (hZ : Nat.card Z = 5) (hZc : ∀ x ∈ P, ∀ y ∈ Z, x * y = y * x)
    (hXP : X ≤ P) (hYP : Y ≤ P) (hX : Nat.card X = 5) (hY : Nat.card Y = 5)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXZ : ∀ x ∈ X, x ∈ Z → x = 1) (hYZ : ∀ y ∈ Y, y ∈ Z → y = 1)
    (htZ : ∀ w ∈ Z, t * w * t⁻¹ ∈ Z) (htX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (htY : ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) : False := by
  have hXYtriv : ∀ x ∈ X, x ∈ Y → x = 1 := by
    intro x hxX hxY
    have h3 : x = x⁻¹ := (htX x hxX).symm.trans (htY x hxY)
    refine burnsideJ410_eq_one_of_sq (burnsideJ410_pow_five hX hxX) ?_
    calc x * x = x * x⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel x
  have hAle : X ⊔ Y ≤ P := sup_le hXP hYP
  have hAcomm := burnsideJ410_comm_sup (burnsideJ410_comm_of_card_five hX)
    (burnsideJ410_comm_of_card_five hY) hXY
  have hdvdP : ∀ K : Subgroup G, K ≤ P → Nat.card K ∣ 125 := fun K hK => by
    have := Subgroup.card_dvd_of_le hK
    rwa [hP] at this
  have hne125 : ∀ K : Subgroup G, K ≤ P → (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) →
      Nat.card K ≠ 125 := by
    intro K hKP hKc hK125
    apply hnab
    have hKP' : K = P := Subgroup.eq_of_le_of_card_ge hKP (by rw [hK125, hP])
    rw [hKP'] at hKc
    exact hKc
  have hA25 : Nat.card (X ⊔ Y : Subgroup G) = 25 := by
    have h1 : 5 ∣ Nat.card (X ⊔ Y : Subgroup G) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : X ≤ X ⊔ Y)
      rwa [hX] at this
    have h3 : Nat.card (X ⊔ Y : Subgroup G) ≠ 5 := by
      intro h5
      have hXA : X = X ⊔ Y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h5, hX])
      obtain ⟨y, hyY, hy1⟩ := burnsideJ410_exists_ne_one hY
      have hyA : y ∈ X ⊔ Y := Subgroup.mem_sup_right hyY
      rw [← hXA] at hyA
      exact hy1 (hXYtriv y hyA hyY)
    exact burnsideJ410_card_25 h1 (hdvdP _ hAle) h3 (hne125 _ hAle hAcomm)
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a (hZP ha) b hb
  have hAZ : ∀ a ∈ X ⊔ Y, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a (hAle ha) b hb
  have hA'le : (X ⊔ Y) ⊔ Z ≤ P := sup_le hAle hZP
  have hA'comm := burnsideJ410_comm_sup hAcomm hZcomm hAZ
  have hA'25 : Nat.card ((X ⊔ Y) ⊔ Z : Subgroup G) = 25 := by
    have h1 : 25 ∣ Nat.card ((X ⊔ Y) ⊔ Z : Subgroup G) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : (X ⊔ Y) ≤ (X ⊔ Y) ⊔ Z)
      rwa [hA25] at this
    exact burnsideJ410_card_25' h1 (hdvdP _ hA'le) (hne125 _ hA'le hA'comm)
  have hEq : X ⊔ Y = (X ⊔ Y) ⊔ Z :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hA25, hA'25])
  have hZA : Z ≤ X ⊔ Y := by
    have := le_sup_right (a := X ⊔ Y) (b := Z)
    rwa [← hEq] at this
  obtain ⟨b, hbZ, hb1⟩ := burnsideJ410_exists_ne_one hZ
  apply hb1
  obtain ⟨x, hx, y, hy, hxy⟩ := burnsideJ410_mem_sup hXY (hZA hbZ)
  have hw : t * b * t⁻¹ = x * y⁻¹ := by
    rw [← hxy]
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x * y⁻¹ := by rw [htX x hx, htY y hy]
  have hwZ : t * b * t⁻¹ ∈ Z := htZ b hbZ
  have hxy' : y * x = x * y := (hXY x hx y hy).symm
  have h1 : b * (t * b * t⁻¹) = x * x := by
    rw [hw, ← hxy]
    calc x * y * (x * y⁻¹) = x * (y * x) * y⁻¹ := by group
      _ = x * (x * y) * y⁻¹ := by rw [hxy']
      _ = x * x := by group
  have h2 : b * (t * b * t⁻¹)⁻¹ = y * y := by
    rw [hw, ← hxy]
    calc x * y * (x * y⁻¹)⁻¹ = x * y * (y * x⁻¹) := by group
      _ = x * (y * y) * x⁻¹ := by group
      _ = y * y := by
        have : x * (y * y) = (y * y) * x := by
          calc x * (y * y) = (x * y) * y := by group
            _ = (y * x) * y := by rw [hxy']
            _ = y * (x * y) := by group
            _ = y * (y * x) := by rw [hxy']
            _ = (y * y) * x := by group
        rw [this]; group
  have hxx : x * x ∈ Z := h1 ▸ mul_mem hbZ hwZ
  have hyy : y * y ∈ Z := h2 ▸ mul_mem hbZ (inv_mem hwZ)
  have hx1 : x = 1 := by
    have : x * x = 1 := hXZ _ (mul_mem hx hx) hxx
    exact burnsideJ410_eq_one_of_sq (burnsideJ410_pow_five hX hx) this
  have hy1 : y = 1 := by
    have : y * y = 1 := hYZ _ (mul_mem hy hy) hyy
    exact burnsideJ410_eq_one_of_sq (burnsideJ410_pow_five hY hy) this
  rw [← hxy, hx1, hy1, one_mul]

theorem burnsideJ410_mem_map_conj (g : G) (K : Subgroup G) (x : G) :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem burnsideJ410_normalizer_conj (g : G) (K : Subgroup G) :
    Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (K : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [burnsideJ410_mem_map_conj, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rw [burnsideJ410_mem_map_conj, burnsideJ410_mem_map_conj] at this
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1, e2] at this
    exact this
  · intro h y
    rw [burnsideJ410_mem_map_conj, burnsideJ410_mem_map_conj]
    have e2 : g⁻¹ * (x * y * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e2]
    exact h (g⁻¹ * y * g)

theorem burnsideJ410_inSubgroup_map (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (A B : Type) [Group A] [Group B] (e : A ≃* B), (F A).map e.toMonoidHom = F B)
    (g : G) (N : Subgroup G) :
    (F ↥(N.map (MulAut.conj g).toMonoidHom)).map (N.map (MulAut.conj g).toMonoidHom).subtype =
      ((F ↥N).map N.subtype).map (MulAut.conj g).toMonoidHom := by
  let e : ↥N ≃* ↥(N.map (MulAut.conj g).toMonoidHom) := MulEquiv.subgroupMap (MulAut.conj g) N
  have h1 := hF ↥N ↥(N.map (MulAut.conj g).toMonoidHom) e
  have hcomp : (N.map (MulAut.conj g).toMonoidHom).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp N.subtype := by
    ext x
    rfl
  rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

end BurnsideJ410Basic

open CFSG.Quasithin.RuType in
theorem burnsideJ410_pCoreOf_NB5
    {G : Type} [Group G] [Finite G] {M : RuDataM G} {b : G} (hbH : b ∈ ruH M.T)
    (hb5 : orderOf b = 5) : pCoreOf 5 (NB5 b) = P5 b := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set N := NB5 b with hNdef
  set P' : Subgroup N := (P5 b).subgroupOf N with hP'
  have hPn : P'.Normal :=
    ⟨fun y hy g => by
      rw [hP', Subgroup.mem_subgroupOf] at hy ⊢
      exact conj_mem_P5_of_normalizes g.2 hy⟩
  have hN : Nat.card N = 4000 := RuDataM.card_normalizer_B5 hbH hb5
  have hPc : Nat.card P' = 125 := by
    rw [hP', card_subgroupOf_of_le RuDataM.P5_le_NB5, RuDataM.card_P5_eq_125 hbH hb5]
  have hPp : IsPGroup 5 P' := by
    rw [IsPGroup.iff_card, hPc]
    exact ⟨3, by norm_num⟩
  unfold pCoreOf
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    show CFSG.pCore 5 N ≤ P'
    let S : Sylow 5 N := Sylow.ofCard P' (by
      rw [hPc, hN, show (4000 : ℕ) = 5 ^ 3 * 32 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
        Nat.prime_five]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 32 by norm_num)])
    exact (CFSG.pCore_isPGroup (p := 5) (G := N)).le_sylow_of_normal S
  · have hle : P' ≤ CFSG.pCore 5 N := le_sSup ⟨hPn, hPp⟩
    have := Subgroup.map_mono (f := N.subtype) hle
    rwa [hP', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr RuDataM.P5_le_NB5] at this

open CFSG.ASVolI.ChIJK in
structure burnsideJ410_LS {G : Type} [Group G] (z c : G) (Bc : Subgroup G) : Prop where
  card_B : Nat.card Bc = 5
  cent : ∀ x ∈ Bc, c * x * c⁻¹ = x
  card_P : Nat.card (PFstar Bc) = 125
  exp : ∀ x ∈ PFstar Bc, x ^ 5 = 1
  le_P : Bc ≤ PFstar Bc
  central : ∀ x ∈ PFstar Bc, ∀ y ∈ Bc, x * y = y * x
  nonab : ¬ ∀ x ∈ PFstar Bc, ∀ y ∈ PFstar Bc, x * y = y * x
  norm : ∀ n ∈ Subgroup.normalizer (Bc : Set G), ∀ x ∈ PFstar Bc, n * x * n⁻¹ ∈ PFstar Bc
  pcore : pCoreOf 5 (Subgroup.normalizer (Bc : Set G)) = PFstar Bc
  inv_mod : ∀ x ∈ PFstar Bc, c * x * c⁻¹ * x ∈ Bc
  card_cent : ∀ i : G, IsConj z i → i * i = 1 → (∀ x ∈ Bc, i * x * i⁻¹ = x⁻¹) →
    Nat.card (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5
  mem_P : ∀ x : G, (∀ y ∈ Bc, x * y = y * x) → x ^ 5 = 1 → x ∈ PFstar Bc
  comm_mem : ∀ x ∈ PFstar Bc, ∀ y ∈ PFstar Bc, x * y * x⁻¹ * y⁻¹ ∈ Bc
  card_C : Nat.card (Subgroup.centralizer (Bc : Set G)) = 1000
  inv_conj : ∀ t : G, t * t = 1 → t ≠ 1 → (∀ x ∈ Bc, t * x = x * t) →
    ∃ g : G, (∀ x ∈ Bc, g * x = x * g) ∧ g * t * g⁻¹ = c
  unique_inv : ∀ t : G, t * t = 1 → c * t = t * c → (∀ x ∈ Bc, t * x = x * t) → t = 1 ∨ t = c

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem burnsideJ410_LS_of_isConj
    {G : Type} [Group G] [Finite G] (M : RuDataM G) {c : G} {Bc : Subgroup G}
    (hc : IsConj M.z c) (hB : Nat.card Bc = 5)
    (hBc : Bc ≤ Subgroup.centralizer ({c} : Set G)) : burnsideJ410_LS M.z c Bc := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  obtain ⟨x0, hx0B, hx05, hx01, -⟩ := exists_gen_of_card_five hB
  have hzp : Subgroup.zpowers x0 = Bc := zpowers_eq_of_card_five hB hx0B hx05 hx01
  set b : G := g⁻¹ * x0 * g with hb
  have hx0c : x0 * c = c * x0 := Subgroup.mem_centralizer_singleton_iff.mp (hBc hx0B)
  have hbz : M.z * b = b * M.z := by
    rw [← hg] at hx0c
    calc M.z * b = g⁻¹ * ((g * M.z * g⁻¹) * x0) * g := by rw [hb]; group
      _ = g⁻¹ * (x0 * (g * M.z * g⁻¹)) * g := by rw [← hx0c]
      _ = b * M.z := by rw [hb]; group
  have hbH : b ∈ ruH M.T := M.mem_H_iff_comm.mpr hbz
  have hb5pow : b ^ 5 = 1 := by
    have e : b ^ 5 = g⁻¹ * x0 ^ 5 * g := by
      rw [hb, show g⁻¹ * x0 * g = g⁻¹ * x0 * g⁻¹⁻¹ by group, conj_pow]; group
    rw [e, hx05]; group
  have hgbg : g * b * g⁻¹ = x0 := by rw [hb]; group
  have hb1 : b ≠ 1 := fun h => hx01 (by rw [← hgbg, h]; group)
  have hb5 : orderOf b = 5 := orderOf_eq_prime hb5pow hb1
  have hBeq : Bc = Subgroup.zpowers (g * b * g⁻¹) := by rw [hgbg, hzp]
  have hgbgB : g * b * g⁻¹ ∈ Bc := by rw [hBeq]; exact Subgroup.mem_zpowers _
  have hBmap : Bc = (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers, hBeq]
    simp [MulAut.conj_apply]
  have hNmap : Subgroup.normalizer (Bc : Set G) =
      (NB5 b).map (MulAut.conj g).toMonoidHom := by
    rw [hBmap]
    exact burnsideJ410_normalizer_conj g _
  have hPF : PFstar Bc = RuDataM.P5c b g := by
    have key := burnsideJ410_inSubgroup_map (fun K _ => CFSG.generalizedFitting K)
      (fun A B _ _ e => CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv e)
      g (NB5 b)
    have hbase := RuDataM.generalizedFitting_NB5 hbH hb5
    unfold PFstar
    rw [hNmap]
    rw [key, hbase]
  have hpc : pCoreOf 5 (Subgroup.normalizer (Bc : Set G)) = RuDataM.P5c b g := by
    have key := burnsideJ410_inSubgroup_map (fun K _ => CFSG.pCore 5 K)
      (fun A B _ _ e => CFSG.pCore_map_iso 5 e) g (NB5 b)
    have hbase := burnsideJ410_pCoreOf_NB5 hbH hb5
    unfold pCoreOf at hbase ⊢
    rw [hNmap]
    rw [key, hbase]
  refine ⟨hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hBc hx)
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [← h]
      _ = x := by group
  · rw [hPF]
    exact RuDataM.card_P5c hbH hb5 g
  · intro x hx
    rw [hPF] at hx
    exact RuDataM.pow_five_P5c hbH hb5 hx
  · rw [hPF, hBeq]
    exact Subgroup.zpowers_le.mpr (RuDataM.conj_mem_P5c (RuDataM.b_mem_P5 hb5))
  · intro x hx y hy
    rw [hPF] at hx
    rw [hBeq] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (RuDataM.comm_center_P5c hx) k).eq
  · rw [hPF]
    exact RuDataM.not_comm_P5c hbH hb5 g
  · intro n hn x hx
    rw [hPF] at hx ⊢
    rw [hNmap, burnsideJ410_mem_map_conj] at hn
    have h := conj_mem_P5_of_normalizes hn (RuDataM.mem_P5c.mp hx)
    rw [RuDataM.mem_P5c]
    have e : g⁻¹ * (n * x * n⁻¹) * g = (g⁻¹ * n * g) * (g⁻¹ * x * g) * (g⁻¹ * n * g)⁻¹ := by
      group
    rw [e]
    exact h
  · rw [hpc, hPF]
  · intro x hx
    rw [hPF] at hx
    obtain ⟨k, hk⟩ := RuDataM.z_conj_P5 hbH hb5 (RuDataM.mem_P5c.mp hx)
    have e1 : c * x * c⁻¹ = x⁻¹ * (g * b * g⁻¹) ^ k := by
      rw [← hg, conj_zpow]
      calc g * M.z * g⁻¹ * x * (g * M.z * g⁻¹)⁻¹
          = g * (M.z * (g⁻¹ * x * g) * M.z⁻¹) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g)⁻¹ * b ^ k) * g⁻¹ := by rw [hk]
        _ = x⁻¹ * (g * b ^ k * g⁻¹) := by group
    have hcomm : x * (g * b * g⁻¹) ^ k = (g * b * g⁻¹) ^ k * x :=
      (Commute.zpow_right (RuDataM.comm_center_P5c hx) k).eq
    have e2 : c * x * c⁻¹ * x = (g * b * g⁻¹) ^ k := by
      rw [e1]
      calc x⁻¹ * (g * b * g⁻¹) ^ k * x = x⁻¹ * ((g * b * g⁻¹) ^ k * x) := by group
        _ = x⁻¹ * (x * (g * b * g⁻¹) ^ k) := by rw [hcomm]
        _ = (g * b * g⁻¹) ^ k := by group
    rw [e2]
    exact Subgroup.zpow_mem _ hgbgB k
  · intro i hiz hi2 hinv
    rw [hPF]
    exact RuDataM.card_P5c_inf_centralizer hbH hb5 hiz hi2 (hinv _ hgbgB)
  · intro x hxc hx5
    rw [hPF]
    exact RuDataM.mem_P5c_of_pow_five hbH hb5 (hxc _ hgbgB) hx5
  ·
    intro x hx y hy
    rw [hPF] at hx hy
    rw [hBeq]
    exact RuDataM.comm_mem_P5c hbH hb5 hx hy
  ·
    have hG5 : Nat.card (G5 b) = 5 ^ 3 * 8 := (RuDataM.lemma_J27_5 hbH hb5).2.2.2.1
    have e : Subgroup.centralizer (Bc : Set G) = (G5 b).map (MulAut.conj g).toMonoidHom := by
      rw [hBeq, centralizer_zpowers_eq]
      ext x
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_G5, mem_G5]
      constructor
      · intro hx
        calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [hx]
          _ = b * (g⁻¹ * x * g) := by group
      · intro hx
        calc x * (g * b * g⁻¹) = g * ((g⁻¹ * x * g) * b) * g⁻¹ := by group
          _ = g * (b * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
          _ = (g * b * g⁻¹) * x := by group
    rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective, hG5]
    norm_num
  ·
    intro t ht2 ht1 htc
    set t' : G := g⁻¹ * t * g with ht'
    have ht'b : t' * b = b * t' := by
      have h := htc _ hgbgB
      calc t' * b = g⁻¹ * (t * (g * b * g⁻¹)) * g := by rw [ht']; group
        _ = g⁻¹ * ((g * b * g⁻¹) * t) * g := by rw [h]
        _ = b * t' := by rw [ht']; group
    have ht'2 : t' * t' = 1 := by
      calc t' * t' = g⁻¹ * (t * t) * g := by rw [ht']; group
        _ = 1 := by rw [ht2]; group
    have ht'1 : t' ≠ 1 := fun h => ht1 (by
      calc t = g * t' * g⁻¹ := by rw [ht']; group
        _ = 1 := by rw [h]; group)
    have hG5 : Nat.card (G5 b) = 1000 := by
      have := (RuDataM.lemma_J27_5 hbH hb5).2.2.2.1
      rw [this]
      norm_num
    have hT5 : Nat.card (M.T5 b) = 8 := RuDataM.card_T5 hbH hb5
    have hrel : ¬ 2 ∣ (M.T5 b).relIndex (G5 b) := by
      have h := relIndex_mul_card_of_le (M.T5_le_G5 (b := b))
      rw [hT5, hG5] at h
      intro hd
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpT : IsPGroup 2 (M.T5 b) := by
      rw [IsPGroup.iff_card, hT5]
      exact ⟨3, by norm_num⟩
    obtain ⟨h, hhG, hhT⟩ := exists_conj_mem_of_sylow (K := G5 b) (S := M.T5 b)
      (M.T5_le_G5 (b := b)) hpT hrel (y := t') (mem_G5.mpr ht'b) (by rw [pow_two]; exact ht'2)
    have hhb : h * b = b * h := mem_G5.mp hhG
    have hz : h⁻¹ * t' * h = M.z :=
      RuDataM.eq_z_of_T5 hbH hb5 hhT (by
        rw [pow_two]
        calc (h⁻¹ * t' * h) * (h⁻¹ * t' * h) = h⁻¹ * (t' * t') * h := by group
          _ = 1 := by rw [ht'2]; group) (fun h1 => ht'1 (by
            calc t' = h * (h⁻¹ * t' * h) * h⁻¹ := by group
              _ = 1 := by rw [h1]; group))
    refine ⟨g * h⁻¹ * g⁻¹, ?_, ?_⟩
    · intro x hx
      rw [hBeq] at hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcom : Commute h b := hhb
      have e : g * h⁻¹ * g⁻¹ * (g * b * g⁻¹) ^ k = (g * b * g⁻¹) ^ k * (g * h⁻¹ * g⁻¹) := by
        rw [conj_zpow]
        have h2 : h⁻¹ * b ^ k = b ^ k * h⁻¹ :=
          (Commute.zpow_right (hcom.inv_left) k).eq
        calc g * h⁻¹ * g⁻¹ * (g * b ^ k * g⁻¹) = g * (h⁻¹ * b ^ k) * g⁻¹ := by group
          _ = g * (b ^ k * h⁻¹) * g⁻¹ := by rw [h2]
          _ = _ := by group
      exact e
    · calc g * h⁻¹ * g⁻¹ * t * (g * h⁻¹ * g⁻¹)⁻¹ = g * (h⁻¹ * (g⁻¹ * t * g) * h) * g⁻¹ := by group
        _ = g * M.z * g⁻¹ := by rw [← ht', hz]
        _ = c := hg
  ·
    intro t ht2 hct htc
    set t' : G := g⁻¹ * t * g with ht'
    have ht'b : t' * b = b * t' := by
      have h := htc _ hgbgB
      calc t' * b = g⁻¹ * (t * (g * b * g⁻¹)) * g := by rw [ht']; group
        _ = g⁻¹ * ((g * b * g⁻¹) * t) * g := by rw [h]
        _ = b * t' := by rw [ht']; group
    have ht'2 : t' * t' = 1 := by
      calc t' * t' = g⁻¹ * (t * t) * g := by rw [ht']; group
        _ = 1 := by rw [ht2]; group
    have ht'z : M.z * t' = t' * M.z := by
      rw [← hg] at hct
      calc M.z * t' = g⁻¹ * ((g * M.z * g⁻¹) * t) * g := by rw [ht']; group
        _ = g⁻¹ * (t * (g * M.z * g⁻¹)) * g := by rw [hct]
        _ = t' * M.z := by rw [ht']; group
    have ht'H : t' ∈ ruH M.T := M.mem_H_iff_comm.mpr ht'z
    by_cases ht1 : t' = 1
    · left
      calc t = g * t' * g⁻¹ := by rw [ht']; group
        _ = 1 := by rw [ht1]; group
    · right
      have hφ : M.phiG t' = 1 := by
        by_contra hne
        exact M.not_comm_of_pow_five hbH hb5pow hb1 ht'H ht'2 hne ht'b.symm
      have htQ : t' ∈ ruQ M.T := (M.phiG_eq_one_iff ht'H).mp hφ
      have hz : t' = M.z :=
        RuDataM.eq_z_of_T5 hbH hb5 ⟨htQ, mem_G5.mpr ht'b⟩ (by rw [pow_two]; exact ht'2) ht1
      calc t = g * t' * g⁻¹ := by rw [ht']; group
        _ = c := by rw [hz]; exact hg

theorem burnsideJ410_mem_normalizer_of_cent {G : Type} [Group G] {Bc : Subgroup G} {c : G}
    (h : ∀ x ∈ Bc, c * x * c⁻¹ = x) : c ∈ Subgroup.normalizer (Bc : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy]
    exact hy
  · intro hy
    have h2 := h (c * y * c⁻¹) hy
    have key : ∀ w : G, c * w * c⁻¹ = w → c⁻¹ * w * c = w := by
      intro w hw
      calc c⁻¹ * w * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [hw]
        _ = w := by group
    have h4 : y = c * y * c⁻¹ := by
      calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = c * y * c⁻¹ := key _ h2
    rw [h4]
    exact hy

open CFSG.ASVolI.ChIJK in
theorem burnsideJ410_step {G : Type} [Group G] {z c i : G} {Bc : Subgroup G}
    (hLS : burnsideJ410_LS z c Bc) (hzi : IsConj z i) (hi2 : i * i = 1) (hci : c * i = i * c)
    (hinv : ∀ x ∈ Bc, i * x * i⁻¹ = x⁻¹) :
    Nat.card (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5 ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G), i * x * i⁻¹ = x) ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      c * x * c⁻¹ = x⁻¹) ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      (c * i) * x * (c * i)⁻¹ = x⁻¹) ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G), x ∈ Bc → x = 1) := by
  have hcent : ∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      i * x * i⁻¹ = x := by
    intro x hx
    have h : x * i = i * x := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    calc i * x * i⁻¹ = x * i * i⁻¹ := by rw [h]
      _ = x := by group
  have hcn : c ∈ Subgroup.normalizer (Bc : Set G) := burnsideJ410_mem_normalizer_of_cent hLS.cent
  have hci' : c⁻¹ * i = i * c⁻¹ := by
    calc c⁻¹ * i = c⁻¹ * (i * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * i) * c⁻¹ := by rw [hci]
      _ = i * c⁻¹ := by group
  have hcinv : ∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      c * x * c⁻¹ = x⁻¹ := by
    intro x hx
    have hxP : x ∈ PFstar Bc := (Subgroup.mem_inf.mp hx).1
    have hxC : x * i = i * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    have hcxP : c * x * c⁻¹ ∈ PFstar Bc := hLS.norm c hcn x hxP
    have hcxC : (c * x * c⁻¹) * i = i * (c * x * c⁻¹) := by
      calc (c * x * c⁻¹) * i = c * x * (c⁻¹ * i) := by group
        _ = c * x * (i * c⁻¹) := by rw [hci']
        _ = c * (x * i) * c⁻¹ := by group
        _ = c * (i * x) * c⁻¹ := by rw [hxC]
        _ = (c * i) * x * c⁻¹ := by group
        _ = (i * c) * x * c⁻¹ := by rw [hci]
        _ = i * (c * x * c⁻¹) := by group
    set w : G := (c * x * c⁻¹) * x with hw
    have hwB : w ∈ Bc := hLS.inv_mod x hxP
    have hwC : w * i = i * w := by
      calc w * i = (c * x * c⁻¹) * (x * i) := by rw [hw]; group
        _ = (c * x * c⁻¹) * (i * x) := by rw [hxC]
        _ = ((c * x * c⁻¹) * i) * x := by group
        _ = (i * (c * x * c⁻¹)) * x := by rw [hcxC]
        _ = i * w := by rw [hw]; group
    have h1 : i * w * i⁻¹ = w := by
      calc i * w * i⁻¹ = w * i * i⁻¹ := by rw [hwC]
        _ = w := by group
    have h2 := hinv w hwB
    have h3 : w = w⁻¹ := h1.symm.trans h2
    have hw1 : w = 1 := by
      refine burnsideJ410_eq_one_of_sq (hLS.exp w (hLS.le_P hwB)) ?_
      calc w * w = w * w⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel w
    have : c * x * c⁻¹ * x = 1 := hw1
    exact eq_inv_of_mul_eq_one_left this
  refine ⟨hLS.card_cent i hzi hi2 hinv, hcent, hcinv, ?_, ?_⟩
  · intro x hx
    calc (c * i) * x * (c * i)⁻¹ = c * (i * x * i⁻¹) * c⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [hcent x hx]
      _ = x⁻¹ := hcinv x hx
  · intro x hx hxB
    have h1 := hcent x hx
    have h2 := hinv x hxB
    have h3 : x = x⁻¹ := h1.symm.trans h2
    refine burnsideJ410_eq_one_of_sq (hLS.exp x (hLS.le_P hxB)) ?_
    calc x * x = x * x⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel x

section BurnsideJ410B

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]

@[expose] def burnsideJ410_Cent (w : G) (Y : Subgroup G) : Prop := ∀ y ∈ Y, w * y * w⁻¹ = y

@[expose] def burnsideJ410_Inv (w : G) (Y : Subgroup G) : Prop := ∀ y ∈ Y, w * y * w⁻¹ = y⁻¹

@[expose] def burnsideJ410_Einv (z u : G) : Set G := {z, u, u * z}

@[expose] def burnsideJ410_QOf (w : G) : Subgroup G :=
  pCoreOf 2 (Subgroup.centralizer ({w} : Set G))

@[expose] def burnsideJ410_E (z u : G) : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers z

structure burnsideJ410_Loc (z u : G) : Prop where
  z_sq : z * z = 1
  u_sq : u * u = 1
  comm : u * z = z * u
  z_ne : z ≠ 1
  u_ne : u ≠ z
  conj_u : IsConj z u
  conj_uz : IsConj z (u * z)
  LS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
    Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ410_LS z c Bc

theorem burnsideJ410_cent_iff_comm {w : G} {Y : Subgroup G} :
    burnsideJ410_Cent w Y ↔ ∀ y ∈ Y, w * y = y * w := by
  unfold burnsideJ410_Cent
  refine forall₂_congr fun y _ => ?_
  constructor
  · intro h
    calc w * y = (w * y * w⁻¹) * w := by group
      _ = y * w := by rw [h]
  · intro h
    calc w * y * w⁻¹ = (y * w) * w⁻¹ := by rw [h]
      _ = y := by group

theorem burnsideJ410_le_centralizer_of_cent {w : G} {Y : Subgroup G}
    (h : burnsideJ410_Cent w Y) : Y ≤ Subgroup.centralizer ({w} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((burnsideJ410_cent_iff_comm.mp h) y hy).symm

theorem burnsideJ410_cent_of_le_centralizer {w : G} {Y : Subgroup G}
    (h : Y ≤ Subgroup.centralizer ({w} : Set G)) : burnsideJ410_Cent w Y := by
  refine burnsideJ410_cent_iff_comm.mpr fun y hy => ?_
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h hy)).symm

theorem burnsideJ410_cent_or_inv {Y : Subgroup G} (hY : Nat.card Y = 5) {w : G}
    (hw : w * w = 1) (hN : w ∈ Subgroup.normalizer (Y : Set G)) :
    burnsideJ410_Cent w Y ∨ burnsideJ410_Inv w Y := by
  obtain ⟨x, hxY, hx5, hx1, hgen⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five hY
  have hzp : Subgroup.zpowers x = Y := CFSG.Quasithin.RuType.zpowers_eq_of_card_five hY hxY hx5 hx1
  have hb5 : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hN' : w ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by rw [hzp]; exact hN
  rcases CFSG.Quasithin.RuType.RuDataM.conj_b_of_inv hb5 hN' hw with h | h
  · left
    intro y hy
    obtain ⟨n, rfl⟩ := hgen y hy
    rw [← conj_pow, h]
  · right
    intro y hy
    obtain ⟨n, rfl⟩ := hgen y hy
    rw [← conj_pow, h, inv_pow]

theorem burnsideJ410_not_cent_inv {Y : Subgroup G} (hY : Nat.card Y = 5) {w : G}
    (hc : burnsideJ410_Cent w Y) (hi : burnsideJ410_Inv w Y) : False := by
  obtain ⟨x, hxY, hx1⟩ := burnsideJ410_exists_ne_one hY
  apply hx1
  have h3 : x = x⁻¹ := (hc x hxY).symm.trans (hi x hxY)
  refine burnsideJ410_eq_one_of_sq (burnsideJ410_pow_five hY hxY) ?_
  calc x * x = x * x⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel x

theorem burnsideJ410_mem_normalizer_of_cent_or_inv [Finite G] {Y : Subgroup G} {w : G}
    (h : burnsideJ410_Cent w Y ∨ burnsideJ410_Inv w Y) :
    w ∈ Subgroup.normalizer (Y : Set G) := by
  refine CFSG.ASVolI.RuChoice.mem_normalizer fun y hy => ?_
  rcases h with h | h
  · rw [h y hy]; exact hy
  · rw [h y hy]; exact Subgroup.inv_mem _ hy

theorem burnsideJ410_E_le_normalizer_iff {z u : G} {Y : Subgroup G} :
    burnsideJ410_E z u ≤ Subgroup.normalizer (Y : Set G) ↔
      z ∈ Subgroup.normalizer (Y : Set G) ∧ u ∈ Subgroup.normalizer (Y : Set G) := by
  constructor
  · intro h
    exact ⟨h (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)),
      h (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))⟩
  · rintro ⟨hz, hu⟩
    exact sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr hz)

section Loc

variable {z u : G}

theorem burnsideJ410_u_ne_one (hL : burnsideJ410_Loc z u) : u ≠ 1 := by
  intro h
  apply hL.z_ne
  have := hL.conj_u
  rw [h] at this
  exact isConj_one_right.mp this.symm

theorem burnsideJ410_uz_ne_one (hL : burnsideJ410_Loc z u) : u * z ≠ 1 := by
  intro h
  apply hL.z_ne
  have := hL.conj_uz
  rw [h] at this
  exact isConj_one_right.mp this.symm

theorem burnsideJ410_z_ne_u (hL : burnsideJ410_Loc z u) : z ≠ u := hL.u_ne.symm

theorem burnsideJ410_z_ne_uz (hL : burnsideJ410_Loc z u) : z ≠ u * z := by
  intro h
  apply burnsideJ410_u_ne_one hL
  have : u * z = 1 * z := by rw [one_mul]; exact h.symm
  exact mul_right_cancel this

theorem burnsideJ410_uz_ne_z (hL : burnsideJ410_Loc z u) : u * z ≠ z :=
  (burnsideJ410_z_ne_uz hL).symm

theorem burnsideJ410_u_ne_uz (hL : burnsideJ410_Loc z u) : u ≠ u * z := by
  intro h
  apply hL.z_ne
  have : u * z = u * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel this

theorem burnsideJ410_uz_ne_u (hL : burnsideJ410_Loc z u) : u * z ≠ u :=
  (burnsideJ410_u_ne_uz hL).symm

theorem burnsideJ410_zu_eq (hL : burnsideJ410_Loc z u) : z * u = u * z := hL.comm.symm

theorem burnsideJ410_z_uz (hL : burnsideJ410_Loc z u) : z * (u * z) = u := by
  calc z * (u * z) = (z * u) * z := by group
    _ = (u * z) * z := by rw [hL.comm.symm]
    _ = u * (z * z) := by group
    _ = u := by rw [hL.z_sq]; group

theorem burnsideJ410_uz_z (hL : burnsideJ410_Loc z u) : (u * z) * z = u := by
  calc (u * z) * z = u * (z * z) := by group
    _ = u := by rw [hL.z_sq]; group

theorem burnsideJ410_u_uz (hL : burnsideJ410_Loc z u) : u * (u * z) = z := by
  calc u * (u * z) = (u * u) * z := by group
    _ = z := by rw [hL.u_sq]; group

theorem burnsideJ410_uz_u (hL : burnsideJ410_Loc z u) : (u * z) * u = z := by
  calc (u * z) * u = (z * u) * u := by rw [hL.comm]
    _ = z * (u * u) := by group
    _ = z := by rw [hL.u_sq]; group

theorem burnsideJ410_uz_sq (hL : burnsideJ410_Loc z u) : (u * z) * (u * z) = 1 := by
  calc (u * z) * (u * z) = u * (z * u) * z := by group
    _ = u * (u * z) * z := by rw [hL.comm.symm]
    _ = (u * u) * (z * z) := by group
    _ = 1 := by rw [hL.u_sq, hL.z_sq]; group

theorem burnsideJ410_Einv_sq (hL : burnsideJ410_Loc z u) {w : G}
    (hw : w ∈ burnsideJ410_Einv z u) : w * w = 1 := by
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact hL.z_sq
  · exact hL.u_sq
  · exact burnsideJ410_uz_sq hL

theorem burnsideJ410_Einv_ne_one (hL : burnsideJ410_Loc z u) {w : G}
    (hw : w ∈ burnsideJ410_Einv z u) : w ≠ 1 := by
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact hL.z_ne
  · exact burnsideJ410_u_ne_one hL
  · exact burnsideJ410_uz_ne_one hL

theorem burnsideJ410_Einv_conj (hL : burnsideJ410_Loc z u) {w : G}
    (hw : w ∈ burnsideJ410_Einv z u) : IsConj z w := by
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact IsConj.refl _
  · exact hL.conj_u
  · exact hL.conj_uz

theorem burnsideJ410_Einv_comm (hL : burnsideJ410_Loc z u) {a b : G}
    (ha : a ∈ burnsideJ410_Einv z u) (hb : b ∈ burnsideJ410_Einv z u) : a * b = b * a := by
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact burnsideJ410_zu_eq hL
  · rw [burnsideJ410_z_uz hL, burnsideJ410_uz_z hL]
  · exact hL.comm
  · rfl
  · rw [burnsideJ410_u_uz hL, burnsideJ410_uz_u hL]
  · rw [burnsideJ410_uz_z hL, burnsideJ410_z_uz hL]
  · rw [burnsideJ410_uz_u hL, burnsideJ410_u_uz hL]
  · rfl

theorem burnsideJ410_z_mem (z u : G) : z ∈ burnsideJ410_Einv z u := Or.inl rfl
theorem burnsideJ410_u_mem (z u : G) : u ∈ burnsideJ410_Einv z u := Or.inr (Or.inl rfl)
theorem burnsideJ410_uz_mem (z u : G) : u * z ∈ burnsideJ410_Einv z u := Or.inr (Or.inr rfl)

theorem burnsideJ410_Einv_mul (hL : burnsideJ410_Loc z u) {a b : G}
    (ha : a ∈ burnsideJ410_Einv z u) (hb : b ∈ burnsideJ410_Einv z u) (hab : a ≠ b) :
    a * b ∈ burnsideJ410_Einv z u ∧ a * b ≠ a ∧ a * b ≠ b := by
  have h1 := burnsideJ410_Einv_ne_one hL ha
  have h2 := burnsideJ410_Einv_ne_one hL hb
  refine ⟨?_, fun h => h2 (by simpa using h), fun h => h1 (by simpa using h)⟩
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · right; right; exact burnsideJ410_zu_eq hL
  · right; left; exact burnsideJ410_z_uz hL
  · right; right; rfl
  · exact absurd rfl hab
  · left; exact burnsideJ410_u_uz hL
  · right; left; exact burnsideJ410_uz_z hL
  · left; exact burnsideJ410_uz_u hL
  · exact absurd rfl hab

end Loc

theorem burnsideJ410_comm_bot_iff {A B : Subgroup G} :
    ⁅A, B⁆ = ⊥ ↔ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm
  · intro h a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (h a ha b hb).symm

section Loc2

variable {z u : G} [Finite G]

theorem burnsideJ410_Einv_trichotomy (hL : burnsideJ410_Loc z u) {a b c d : G}
    (ha : a ∈ burnsideJ410_Einv z u) (hb : b ∈ burnsideJ410_Einv z u)
    (hc : c ∈ burnsideJ410_Einv z u) (hd : d ∈ burnsideJ410_Einv z u)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : d = a ∨ d = b ∨ d = c := by
  have h1 := hL.u_ne
  have h1' := burnsideJ410_z_ne_u hL
  have h2 := burnsideJ410_z_ne_uz hL
  have h2' := burnsideJ410_uz_ne_z hL
  have h3 := burnsideJ410_u_ne_uz hL
  have h3' := burnsideJ410_uz_ne_u hL
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> simp_all

theorem burnsideJ410_trichotomy (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) :
    (burnsideJ410_Cent z Y ∧ burnsideJ410_Inv u Y ∧ burnsideJ410_Inv (u * z) Y) ∨
    (burnsideJ410_Inv z Y ∧ burnsideJ410_Cent u Y ∧ burnsideJ410_Inv (u * z) Y) ∨
    (burnsideJ410_Inv z Y ∧ burnsideJ410_Inv u Y ∧ burnsideJ410_Cent (u * z) Y) := by
  obtain ⟨hcard, hE⟩ := hY
  obtain ⟨hzN, huN⟩ := burnsideJ410_E_le_normalizer_iff.mp hE
  have hz := burnsideJ410_cent_or_inv hcard hL.z_sq hzN
  have hu := burnsideJ410_cent_or_inv hcard hL.u_sq huN
  rcases hz with hz | hz <;> rcases hu with hu | hu
  · exfalso
    have hLS := hL.LS z Y (IsConj.refl z) hcard (burnsideJ410_le_centralizer_of_cent hz)
    rcases hLS.unique_inv u hL.u_sq (burnsideJ410_zu_eq hL)
        (fun x hx => ((burnsideJ410_cent_iff_comm.mp hu) x hx)) with h | h
    · exact burnsideJ410_u_ne_one hL h
    · exact hL.u_ne h
  · refine Or.inl ⟨hz, hu, fun y hy => ?_⟩
    calc (u * z) * y * (u * z)⁻¹ = u * (z * y * z⁻¹) * u⁻¹ := by group
      _ = u * y * u⁻¹ := by rw [hz y hy]
      _ = y⁻¹ := hu y hy
  · refine Or.inr (Or.inl ⟨hz, hu, fun y hy => ?_⟩)
    calc (u * z) * y * (u * z)⁻¹ = u * (z * y * z⁻¹) * u⁻¹ := by group
      _ = u * y⁻¹ * u⁻¹ := by rw [hz y hy]
      _ = (u * y * u⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [hu y hy]
  · refine Or.inr (Or.inr ⟨hz, hu, fun y hy => ?_⟩)
    calc (u * z) * y * (u * z)⁻¹ = u * (z * y * z⁻¹) * u⁻¹ := by group
      _ = u * y⁻¹ * u⁻¹ := by rw [hz y hy]
      _ = (u * y * u⁻¹)⁻¹ := by group
      _ = y := by rw [hu y hy, inv_inv]

theorem burnsideJ410_label_exists (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) :
    ∃ v ∈ burnsideJ410_Einv z u, burnsideJ410_Cent v Y ∧
      ∀ w ∈ burnsideJ410_Einv z u, w ≠ v → burnsideJ410_Inv w Y := by
  rcases burnsideJ410_trichotomy hL hY with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨z, burnsideJ410_z_mem z u, h1, fun w hw hwz => ?_⟩
    simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd rfl hwz
    · exact h2
    · exact h3
  · refine ⟨u, burnsideJ410_u_mem z u, h2, fun w hw hwz => ?_⟩
    simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact h1
    · exact absurd rfl hwz
    · exact h3
  · refine ⟨u * z, burnsideJ410_uz_mem z u, h3, fun w hw hwz => ?_⟩
    simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact absurd rfl hwz

theorem burnsideJ410_label_unique (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) {v v' : G} (hv : v ∈ burnsideJ410_Einv z u)
    (hv' : v' ∈ burnsideJ410_Einv z u) (h : burnsideJ410_Cent v Y)
    (h' : burnsideJ410_Cent v' Y) : v = v' := by
  obtain ⟨c, hc, -, hcI⟩ := burnsideJ410_label_exists hL hY
  have key : ∀ x ∈ burnsideJ410_Einv z u, burnsideJ410_Cent x Y → x = c := by
    intro x hx hxC
    by_contra hne
    exact burnsideJ410_not_cent_inv hY.1 hxC (hcI x hx hne)
  rw [key v hv h, key v' hv' h']

theorem burnsideJ410_inv_of_ne (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) {v w : G} (hv : v ∈ burnsideJ410_Einv z u)
    (hvY : burnsideJ410_Cent v Y) (hw : w ∈ burnsideJ410_Einv z u) (hwv : w ≠ v) :
    burnsideJ410_Inv w Y := by
  obtain ⟨c, hc, hcC, hcI⟩ := burnsideJ410_label_exists hL hY
  have : v = c := burnsideJ410_label_unique hL hY hv hc hvY hcC
  subst this
  exact hcI w hw hwv

theorem burnsideJ410_LS_of_label (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) {v : G} (hv : v ∈ burnsideJ410_Einv z u)
    (hvY : burnsideJ410_Cent v Y) : burnsideJ410_LS z v Y :=
  hL.LS v Y (burnsideJ410_Einv_conj hL hv) hY.1 (burnsideJ410_le_centralizer_of_cent hvY)

theorem burnsideJ410_mem_O5N (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) {v : G} (hv : v ∈ burnsideJ410_Einv z u)
    (hvY : burnsideJ410_Cent v Y) {x : G} :
    x ∈ O5N Y ↔ x ^ 5 = 1 ∧ ∀ y ∈ Y, x * y = y * x := by
  have hLS := burnsideJ410_LS_of_label hL hY hv hvY
  have hP : O5N Y = PFstar Y := hLS.pcore
  rw [hP]
  constructor
  · intro hx
    exact ⟨hLS.exp x hx, fun y hy => hLS.central x hx y hy⟩
  · rintro ⟨h5, hc⟩
    exact hLS.mem_P x hc h5

theorem burnsideJ410_cent_O5N (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) {v : G} (hv : v ∈ burnsideJ410_Einv z u)
    (hvY : burnsideJ410_Cent v Y) :
    O5N Y ⊓ Subgroup.centralizer ({v} : Set G) = Y := by
  have hLS := burnsideJ410_LS_of_label hL hY hv hvY
  have hP : O5N Y = PFstar Y := hLS.pcore
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxv⟩ := Subgroup.mem_inf.mp hx
    rw [hP] at hxP
    have hcomm : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hxv
    have h1 := hLS.inv_mod x hxP
    have hxc : v * x * v⁻¹ = x := by
      calc v * x * v⁻¹ = (x * v) * v⁻¹ := by rw [← hcomm]
        _ = x := by group
    rw [hxc] at h1
    have h5 := hLS.exp x hxP
    have e : x = (x * x) ^ 3 := by
      calc x = x ^ 5 * x := by rw [h5, one_mul]
        _ = x ^ 6 := by rw [← pow_succ]
        _ = (x ^ 2) ^ 3 := by rw [← pow_mul]
        _ = (x * x) ^ 3 := by rw [pow_two]
    rw [e]
    exact Subgroup.pow_mem _ h1 3
  · intro y hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hP]; exact hLS.le_P hy
    · exact burnsideJ410_le_centralizer_of_cent hvY hy

theorem burnsideJ410_nb (hL : burnsideJ410_Loc z u) {Y : Subgroup G} (hY : Y ∈ EInv5Ru z u)
    {v w : G} (hv : v ∈ burnsideJ410_Einv z u) (hvY : burnsideJ410_Cent v Y)
    (hw : w ∈ burnsideJ410_Einv z u) (hwv : w ≠ v) :
    (O5N Y ⊓ Subgroup.centralizer ({w} : Set G)) ∈ EInv5Ru z u ∧
      burnsideJ410_Cent w (O5N Y ⊓ Subgroup.centralizer ({w} : Set G)) ∧
      (O5N Y ⊓ Subgroup.centralizer ({w} : Set G)) ≠ Y ∧
      ⁅Y, O5N Y ⊓ Subgroup.centralizer ({w} : Set G)⁆ = ⊥ := by
  have hLS := burnsideJ410_LS_of_label hL hY hv hvY
  have hP : O5N Y = PFstar Y := hLS.pcore
  rw [hP]
  have hinv := burnsideJ410_inv_of_ne hL hY hv hvY hw hwv
  obtain ⟨hcard, hcw, hinvv, hinvvw, -⟩ := burnsideJ410_step hLS
    (burnsideJ410_Einv_conj hL hw) (burnsideJ410_Einv_sq hL hw)
    (burnsideJ410_Einv_comm hL hv hw) hinv
  have hMul := burnsideJ410_Einv_mul hL hv hw hwv.symm
  have hnorm : ∀ t ∈ burnsideJ410_Einv z u,
      t ∈ Subgroup.normalizer ((PFstar Y ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) :
        Set G) := by
    intro t ht
    apply burnsideJ410_mem_normalizer_of_cent_or_inv
    rcases burnsideJ410_Einv_trichotomy hL hv hw hMul.1 ht hwv.symm hMul.2.1.symm hMul.2.2.symm
      with h | h | h
    · subst h; exact Or.inr hinvv
    · subst h; exact Or.inl hcw
    · subst h; exact Or.inr hinvvw
  refine ⟨⟨hcard, burnsideJ410_E_le_normalizer_iff.mpr
    ⟨hnorm z (burnsideJ410_z_mem z u), hnorm u (burnsideJ410_u_mem z u)⟩⟩, hcw, ?_, ?_⟩
  · intro h
    apply burnsideJ410_not_cent_inv hY.1 (w := w) _ hinv
    intro y hy
    rw [← h] at hy
    exact hcw y hy
  · refine burnsideJ410_comm_bot_iff.mpr fun y hy x hx => ?_
    exact (hLS.central x (Subgroup.mem_inf.mp hx).1 y hy).symm

theorem burnsideJ410_nbr_eq (hL : burnsideJ410_Loc z u) {Y Y' : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) (hY' : Y' ∈ EInv5Ru z u) (hne : Y ≠ Y') (hc : ⁅Y, Y'⁆ = ⊥)
    {v w : G} (hv : v ∈ burnsideJ410_Einv z u) (hvY : burnsideJ410_Cent v Y)
    (hw : w ∈ burnsideJ410_Einv z u) (hwY' : burnsideJ410_Cent w Y') :
    w ≠ v ∧ Y' = O5N Y ⊓ Subgroup.centralizer ({w} : Set G) := by
  have hcomm := burnsideJ410_comm_bot_iff.mp hc
  have hle : Y' ≤ O5N Y := by
    intro y hy
    exact (burnsideJ410_mem_O5N hL hY hv hvY).mpr
      ⟨burnsideJ410_pow_five hY'.1 hy, fun x hx => (hcomm x hx y hy).symm⟩
  have hle' : Y' ≤ O5N Y ⊓ Subgroup.centralizer ({w} : Set G) :=
    le_inf hle (burnsideJ410_le_centralizer_of_cent hwY')
  have hwv : w ≠ v := by
    intro h
    subst h
    have h1 : Y' ≤ Y := by
      rw [← burnsideJ410_cent_O5N hL hY hw hvY]
      exact hle'
    exact hne (Subgroup.eq_of_le_of_card_ge h1 (by rw [hY.1, hY'.1])).symm
  refine ⟨hwv, ?_⟩
  obtain ⟨hnb, -, -, -⟩ := burnsideJ410_nb hL hY hv hvY hw hwv
  exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hnb.1, hY'.1])

end Loc2

section Equiv

variable {z u : G} [Finite G]

theorem burnsideJ410_zpowers_sq {x : G} (h : x * x = 1) {s : G} (hs : s ∈ Subgroup.zpowers x) :
    s = 1 ∨ s = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hsq : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left; rw [zpow_mul, hsq, one_zpow]
  · right; rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

theorem burnsideJ410_mem_E_iff (hL : burnsideJ410_Loc z u) {x : G} :
    x ∈ burnsideJ410_E z u ↔ x = 1 ∨ x = z ∨ x = u ∨ x = u * z := by
  constructor
  · intro hx
    have hcomm : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow hL.comm m n).eq
    obtain ⟨s, hs, t, ht, rfl⟩ := burnsideJ410_mem_sup hcomm hx
    rcases burnsideJ410_zpowers_sq hL.u_sq hs with rfl | rfl <;>
      rcases burnsideJ410_zpowers_sq hL.z_sq ht with rfl | rfl
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem burnsideJ410_Einv_mem_E (hL : burnsideJ410_Loc z u) {w : G}
    (hw : w ∈ burnsideJ410_Einv z u) : w ∈ burnsideJ410_E z u := by
  rw [burnsideJ410_mem_E_iff hL]
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  tauto

theorem burnsideJ410_conj_Einv (hL : burnsideJ410_Loc z u) {g w : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G))
    (hw : w ∈ burnsideJ410_Einv z u) : g⁻¹ * w * g ∈ burnsideJ410_Einv z u := by
  have hwE := burnsideJ410_Einv_mem_E hL hw
  have hg' : g⁻¹ ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G) := inv_mem hg
  have h1 : g⁻¹ * w * g ∈ burnsideJ410_E z u := by
    have := (Subgroup.mem_normalizer_iff.mp hg' w).mp hwE
    simpa using this
  have hsq : (g⁻¹ * w * g) * (g⁻¹ * w * g) = 1 := by
    calc (g⁻¹ * w * g) * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [burnsideJ410_Einv_sq hL hw]; group
  have hne : g⁻¹ * w * g ≠ 1 := by
    intro h
    apply burnsideJ410_Einv_ne_one hL hw
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases (burnsideJ410_mem_E_iff hL).mp h1 with h | h | h | h
  · exact absurd h hne
  · rw [h]; exact burnsideJ410_z_mem z u
  · rw [h]; exact burnsideJ410_u_mem z u
  · rw [h]; exact burnsideJ410_uz_mem z u

theorem burnsideJ410_conj_mem_EInv5 {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) : CFSG.conjugate Y g ∈ EInv5Ru z u := by
  refine ⟨by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hY.1, ?_⟩
  rw [CFSG.ASVolI.RuChoice.fx_normalizer_conjugate]
  intro e he
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
  exact hY.2 ((Subgroup.mem_normalizer_iff.mp hg e).mp he)

theorem burnsideJ410_conj_cent {w : G} {Y : Subgroup G} (g : G) (h : burnsideJ410_Cent w Y) :
    burnsideJ410_Cent (g⁻¹ * w * g) (CFSG.conjugate Y g) := by
  intro x hx
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hx
  have := h _ hx
  calc g⁻¹ * w * g * x * (g⁻¹ * w * g)⁻¹ = g⁻¹ * (w * (g * x * g⁻¹) * w⁻¹) * g := by group
    _ = x := by rw [this]; group

theorem burnsideJ410_mem_conj_inv {A : Subgroup G} (g : G) {a : G} (ha : a ∈ A) :
    g⁻¹ * a * g ∈ CFSG.conjugate A g := by
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
  have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  rw [this]; exact ha

theorem burnsideJ410_comm_conj (g a b : G) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) ↔ a * b = b * a := by
  constructor
  · intro h
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
      _ = b * a := by group
  · intro h
    calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem burnsideJ410_conj_comm_bot {A B : Subgroup G} (g : G) :
    ⁅CFSG.conjugate A g, CFSG.conjugate B g⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  rw [burnsideJ410_comm_bot_iff, burnsideJ410_comm_bot_iff]
  constructor
  · intro h a ha b hb
    have h1 := h (g⁻¹ * a * g) (burnsideJ410_mem_conj_inv g ha) (g⁻¹ * b * g)
      (burnsideJ410_mem_conj_inv g hb)
    have := (burnsideJ410_comm_conj g⁻¹ a b).mp (by simpa using h1)
    exact this
  · intro h x hx y hy
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hx hy
    have h1 := h _ hx _ hy
    exact (burnsideJ410_comm_conj g x y).mp h1

theorem burnsideJ410_conj_nb (hL : burnsideJ410_Loc z u) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) {v : G} (hv : v ∈ burnsideJ410_Einv z u)
    (hvY : burnsideJ410_Cent v Y) (w : G) {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) :
    CFSG.conjugate (O5N Y ⊓ Subgroup.centralizer ({w} : Set G)) g =
      O5N (CFSG.conjugate Y g) ⊓ Subgroup.centralizer ({g⁻¹ * w * g} : Set G) := by
  have hYg := burnsideJ410_conj_mem_EInv5 hg hY
  have hvg := burnsideJ410_conj_Einv hL hg hv
  have hvYg := burnsideJ410_conj_cent g hvY
  ext x
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate, Subgroup.mem_inf, Subgroup.mem_inf,
    burnsideJ410_mem_O5N hL hY hv hvY, burnsideJ410_mem_O5N hL hYg hvg hvYg,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨h5, hc⟩, hw⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (g * x * g⁻¹) ^ 5 = g * x ^ 5 * g⁻¹ := conj_pow
      rw [this] at h5
      calc x ^ 5 = g⁻¹ * (g * x ^ 5 * g⁻¹) * g := by group
        _ = 1 := by rw [h5]; group
    · intro y hy
      rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hy
      have h1 := hc _ hy
      have := (burnsideJ410_comm_conj g x y).mp h1
      exact this
    · have h := burnsideJ410_comm_conj g x (g⁻¹ * w * g)
      rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h
      exact h.mp hw
  · rintro ⟨⟨h5, hc⟩, hw⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (g * x * g⁻¹) ^ 5 = g * x ^ 5 * g⁻¹ := conj_pow
      rw [this, h5]; group
    · intro y hy
      have hy' : g⁻¹ * y * g ∈ CFSG.conjugate Y g := burnsideJ410_mem_conj_inv g hy
      have h1 := hc _ hy'
      have h := burnsideJ410_comm_conj g x (g⁻¹ * y * g)
      rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
      exact h.mpr h1
    · have h := burnsideJ410_comm_conj g x (g⁻¹ * w * g)
      rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h
      exact h.mpr hw

end Equiv

end BurnsideJ410B

section BurnsideJ410C

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]

theorem burnsideJ410_no_two_element {κ d₁ d₂ : G} (hd₁ : orderOf d₁ = 5)
    (h5 : d₂ ^ 5 = 1) (hcomm : d₁ * d₂ = d₂ * d₁)
    (hindep : ∀ t : ℤ, d₁ ^ t ∈ Subgroup.zpowers d₂ → d₁ ^ t = 1)
    (hκ1 : κ * d₁ * κ⁻¹ = d₁ * d₂) (hκ2 : κ * d₂ * κ⁻¹ = d₁ * d₂ ^ 2)
    {k : ℕ} (hk : κ ^ (2 ^ k) = 1) : False := by
  have hc : Commute d₁ d₂ := hcomm
  have h5₁ : d₁ ^ 5 = 1 := by rw [← hd₁]; exact pow_orderOf_eq_one d₁
  set e : G := d₁ * d₂ ^ 3 with he
  have hd2e : d₂⁻¹ * e = d₁ * d₂ ^ 2 := by
    calc d₂⁻¹ * e = (d₂⁻¹ * d₁) * d₂ ^ 3 := by rw [he]; group
      _ = (d₁ * d₂⁻¹) * d₂ ^ 3 := by rw [← hc.inv_right.eq]
      _ = d₁ * d₂ ^ 2 := by group
  have hκd : κ * d₂ * κ⁻¹ = d₂⁻¹ * e := by rw [hκ2, hd2e]
  have hκe : κ * e * κ⁻¹ = e⁻¹ := by
    have e1 : κ * e * κ⁻¹ = (κ * d₁ * κ⁻¹) * (κ * d₂ * κ⁻¹) ^ 3 := by
      calc κ * e * κ⁻¹ = (κ * d₁ * κ⁻¹) * (κ * d₂ ^ 3 * κ⁻¹) := by rw [he]; group
        _ = (κ * d₁ * κ⁻¹) * (κ * d₂ * κ⁻¹) ^ 3 := by rw [conj_pow]
    rw [e1, hκ1, hκ2]
    have e2 : (d₁ * d₂ ^ 2) ^ 3 = d₁ ^ 3 * d₂ ^ 6 := by
      rw [(hc.pow_right 2).mul_pow, ← pow_mul]
    have e3 : (d₁ * d₂) * (d₁ ^ 3 * d₂ ^ 6) = d₁ ^ 4 * d₂ ^ 7 := by
      rw [Commute.mul_mul_mul_comm (hc.symm.pow_right 3)]
      group
    have e4 : d₁ ^ 4 = d₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h5₁])
    have e5 : d₂ ^ 7 = d₂ ^ 2 := by
      calc d₂ ^ 7 = d₂ ^ 5 * d₂ ^ 2 := by rw [← pow_add]
        _ = d₂ ^ 2 := by rw [h5, one_mul]
    have e6 : (d₂ ^ 3)⁻¹ = d₂ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, h5])
    rw [e2, e3, e4, e5, he, mul_inv_rev, e6]
    exact ((hc.symm.pow_left 2).inv_right.eq).symm
  have hcommE : Commute d₂ e := by
    rw [he]; exact hc.symm.mul_right ((Commute.refl d₂).pow_right 3)
  have key : ∀ n : ℕ, κ ^ n * d₂ * (κ ^ n)⁻¹ =
      d₂ ^ ((-1 : ℤ) ^ n) * e ^ ((-1 : ℤ) ^ (n + 1) * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have step : κ ^ (n + 1) * d₂ * (κ ^ (n + 1))⁻¹ =
          κ * (κ ^ n * d₂ * (κ ^ n)⁻¹) * κ⁻¹ := by
        rw [pow_succ']; group
      rw [step, ih]
      have e1 : κ * (d₂ ^ ((-1 : ℤ) ^ n) * e ^ ((-1 : ℤ) ^ (n + 1) * n)) * κ⁻¹ =
          (κ * d₂ * κ⁻¹) ^ ((-1 : ℤ) ^ n) * (κ * e * κ⁻¹) ^ ((-1 : ℤ) ^ (n + 1) * n) := by
        calc κ * (d₂ ^ ((-1 : ℤ) ^ n) * e ^ ((-1 : ℤ) ^ (n + 1) * n)) * κ⁻¹ =
            (κ * d₂ ^ ((-1 : ℤ) ^ n) * κ⁻¹) * (κ * e ^ ((-1 : ℤ) ^ (n + 1) * n) * κ⁻¹) := by
              group
          _ = _ := by rw [conj_zpow, conj_zpow]
      have hs : -((-1 : ℤ) ^ n) = (-1) ^ (n + 1) := by rw [pow_succ]; ring
      have ht : (-1 : ℤ) ^ n + -((-1 : ℤ) ^ (n + 1) * n) =
          (-1) ^ (n + 1 + 1) * ((n + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [e1, hκd, hκe, hcommE.inv_left.mul_zpow, inv_zpow', inv_zpow', mul_assoc, ← zpow_add,
        hs, ht]
  have hk' := key (2 ^ k)
  rw [hk, one_mul, inv_one, mul_one] at hk'
  have het : e ^ ((-1 : ℤ) ^ (2 ^ k + 1) * ((2 ^ k : ℕ) : ℤ)) ∈ Subgroup.zpowers d₂ := by
    have : e ^ ((-1 : ℤ) ^ (2 ^ k + 1) * ((2 ^ k : ℕ) : ℤ)) =
        (d₂ ^ ((-1 : ℤ) ^ (2 ^ k)))⁻¹ * d₂ := by
      calc e ^ ((-1 : ℤ) ^ (2 ^ k + 1) * ((2 ^ k : ℕ) : ℤ)) =
          (d₂ ^ ((-1 : ℤ) ^ (2 ^ k)))⁻¹ * (d₂ ^ ((-1 : ℤ) ^ (2 ^ k)) *
            e ^ ((-1 : ℤ) ^ (2 ^ k + 1) * ((2 ^ k : ℕ) : ℤ))) := by group
        _ = _ := by rw [← hk']
    rw [this]
    exact mul_mem (inv_mem (Subgroup.zpow_mem_zpowers d₂ _)) (Subgroup.mem_zpowers d₂)
  set t : ℤ := (-1 : ℤ) ^ (2 ^ k + 1) * ((2 ^ k : ℕ) : ℤ) with ht
  have h1 : d₁ ^ t ∈ Subgroup.zpowers d₂ := by
    have e1 : e ^ t = d₁ ^ t * (d₂ ^ 3) ^ t := by
      rw [he]; exact (hc.pow_right 3).mul_zpow t
    have e2 : d₁ ^ t = e ^ t * ((d₂ ^ 3) ^ t)⁻¹ := by rw [e1]; group
    rw [e2]
    exact mul_mem het (inv_mem (Subgroup.zpow_mem _ (Subgroup.pow_mem _
      (Subgroup.mem_zpowers d₂) 3) t))
  have h2 : d₁ ^ t = 1 := hindep t h1
  have h3 : ((orderOf d₁ : ℕ) : ℤ) ∣ t := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hd₁] at h3
  have h4 : 5 ∣ t.natAbs := Int.natCast_dvd.mp h3
  have h5' : t.natAbs = 2 ^ k := by
    rw [ht, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
      Int.natAbs_natCast]
  rw [h5'] at h4
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h4
  omega

theorem burnsideJ410_gen [Finite G] {Y : Subgroup G} (hY : Nat.card Y = 5) {x : G} (hx : x ∈ Y)
    (hx1 : x ≠ 1) : ∀ y ∈ Y, ∃ n : ℕ, x ^ n = y := by
  intro y hy
  have hzp := CFSG.Quasithin.RuType.zpowers_eq_of_card_five hY hx (burnsideJ410_pow_five hY hx) hx1
  have : y ∈ Subgroup.zpowers x := by rw [hzp]; exact hy
  exact CFSG.Quasithin.RuType.exists_pow_of_mem_zpowers this

theorem burnsideJ410_comm_of_gens [Finite G] {A B : Subgroup G} (hA : Nat.card A = 5) (hB : Nat.card B = 5)
    {x y : G} (hx : x ∈ A) (hy : y ∈ B) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := burnsideJ410_gen hA hx hx1 a ha
  obtain ⟨n, rfl⟩ := burnsideJ410_gen hB hy hy1 b hb
  exact ((show Commute x y from hxy).pow_pow m n).eq

theorem burnsideJ410_inter_triv {X Y : Subgroup G} (hX : Nat.card X = 5) {w : G}
    (hwX : burnsideJ410_Cent w X) (hwY : burnsideJ410_Inv w Y) {x : G} (hxX : x ∈ X)
    (hxY : x ∈ Y) : x = 1 := by
  have h3 : x = x⁻¹ := (hwX x hxX).symm.trans (hwY x hxY)
  refine burnsideJ410_eq_one_of_sq (burnsideJ410_pow_five hX hxX) ?_
  calc x * x = x * x⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel x

section Path

variable {z u : G} [Finite G]

theorem burnsideJ410_noncomm (hL : burnsideJ410_Loc z u) {X A B : Subgroup G}
    (hX : X ∈ EInv5Ru z u) (hA : A ∈ EInv5Ru z u) (hB : B ∈ EInv5Ru z u)
    {p α β : G} (hp : p ∈ burnsideJ410_Einv z u) (hα : α ∈ burnsideJ410_Einv z u)
    (hβ : β ∈ burnsideJ410_Einv z u) (hXp : burnsideJ410_Cent p X)
    (hAα : burnsideJ410_Cent α A) (hBβ : burnsideJ410_Cent β B) (hαp : α ≠ p) (hβp : β ≠ p)
    (hαβ : α ≠ β) (hAX : ⁅X, A⁆ = ⊥) (hBX : ⁅X, B⁆ = ⊥) :
    ∃ x ∈ A, ∃ y ∈ B, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hLS := burnsideJ410_LS_of_label hL hX hp hXp
  have hP : O5N X = PFstar X := hLS.pcore
  have hcommA := burnsideJ410_comm_bot_iff.mp hAX
  have hcommB := burnsideJ410_comm_bot_iff.mp hBX
  have hAP : A ≤ PFstar X := by
    intro a ha
    rw [← hP]
    exact (burnsideJ410_mem_O5N hL hX hp hXp).mpr
      ⟨burnsideJ410_pow_five hA.1 ha, fun y hy => (hcommA y hy a ha).symm⟩
  have hBP : B ≤ PFstar X := by
    intro b hb
    rw [← hP]
    exact (burnsideJ410_mem_O5N hL hX hp hXp).mpr
      ⟨burnsideJ410_pow_five hB.1 hb, fun y hy => (hcommB y hy b hb).symm⟩
  have hinvX := burnsideJ410_inv_of_ne hL hX hp hXp hα hαp
  have hinvXβ := burnsideJ410_inv_of_ne hL hX hp hXp hβ hβp
  have hinvB := burnsideJ410_inv_of_ne hL hB hβ hBβ hα hαβ
  exact burnsideJ410_nc (P := PFstar X) (Z := X) (X := A) (Y := B) (t := α)
    hLS.card_P hLS.nonab hLS.le_P hX.1 hLS.central hAP hBP hA.1 hB.1 hcon
    (fun x hx hxX => burnsideJ410_inter_triv hA.1 hAα hinvX hx hxX)
    (fun y hy hyX => burnsideJ410_inter_triv hB.1 hBβ hinvXβ hy hyX)
    (fun w hw => by rw [hinvX w hw]; exact inv_mem hw) hAα hinvB

theorem burnsideJ410_cent_triv (hL : burnsideJ410_Loc z u) {Y₀ Y₁ Y₂ : Subgroup G}
    (h₀ : Y₀ ∈ EInv5Ru z u) (h₁ : Y₁ ∈ EInv5Ru z u) (h₂ : Y₂ ∈ EInv5Ru z u)
    {a b c : G} (ha : a ∈ burnsideJ410_Einv z u) (hb : b ∈ burnsideJ410_Einv z u)
    (hc : c ∈ burnsideJ410_Einv z u) (hab : a ≠ b) (hcb : c ≠ b)
    (hY₀ : burnsideJ410_Cent a Y₀) (hY₁ : burnsideJ410_Cent b Y₁)
    (hY₂ : burnsideJ410_Cent c Y₂) (c10 : ⁅Y₁, Y₀⁆ = ⊥) (c12 : ⁅Y₁, Y₂⁆ = ⊥)
    {x₀ d₁ d₂ : G} (hx₀ : x₀ ∈ Y₀) (hd₁ : d₁ ∈ Y₁) (hd₂ : d₂ ∈ Y₂) (hd₁1 : d₁ ≠ 1)
    (hnc : x₀ * d₂ ≠ d₂ * x₀) {g : G} (hg1 : g * d₁ = d₁ * g) (hg2 : g * d₂ = d₂ * g)
    (hga : g * a = a * g) : g = 1 := by
  by_contra hg
  have hLS := burnsideJ410_LS_of_label hL h₁ hb hY₁
  have hP : O5N Y₁ = PFstar Y₁ := hLS.pcore
  have hne : Y₁ ≠ Y₀ := by
    intro h
    exact hab (burnsideJ410_label_unique hL h₁ ha hb (h ▸ hY₀) hY₁)
  obtain ⟨-, hY₀eq⟩ := burnsideJ410_nbr_eq hL h₁ h₀ hne c10 hb hY₁ ha hY₀
  have hd₂1 : d₂ ≠ 1 := by
    intro h; apply hnc; rw [h]; simp
  have hgY₁ : ∀ y ∈ Y₁, g * y = y * g := by
    intro y hy
    obtain ⟨n, rfl⟩ := burnsideJ410_gen h₁.1 hd₁ hd₁1 y hy
    exact ((show Commute g d₁ from hg1).pow_right n).eq
  have hgC : g ∈ Subgroup.centralizer (Y₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hgY₁ y hy).symm
  have hord : orderOf g ∣ 1000 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (Y₁ : Set G)) hgC
    rwa [hLS.card_C] at this
  have hne1 : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
  have hp25 : p = 2 ∨ p = 5 := by
    have h1 : p ∣ 2 ^ 3 * 5 ^ 3 := by
      have := hpd.trans hord
      simpa using this
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h))
  have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  set g' : G := g ^ (orderOf g / p) with hg'
  have hg'ord : orderOf g' = p := orderOf_pow_orderOf_div hord0 hpd
  have hg'pp : g' ^ p = 1 := by rw [← hg'ord]; exact pow_orderOf_eq_one _
  have hg'1 : g' * d₁ = d₁ * g' := ((show Commute g d₁ from hg1).pow_left _).eq
  have hg'2 : g' * d₂ = d₂ * g' := ((show Commute g d₂ from hg2).pow_left _).eq
  have hg'a : g' * a = a * g' := ((show Commute g a from hga).pow_left _).eq
  have hgY₁' : ∀ y ∈ Y₁, g' * y = y * g' := by
    intro y hy
    obtain ⟨n, rfl⟩ := burnsideJ410_gen h₁.1 hd₁ hd₁1 y hy
    exact ((show Commute g' d₁ from hg'1).pow_right n).eq
  have hg'1' : g' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg'ord
    exact hp.one_lt.ne hg'ord
  have hd₂P : d₂ ∈ O5N Y₁ := by
    have hcomm12 := burnsideJ410_comm_bot_iff.mp c12
    exact (burnsideJ410_mem_O5N hL h₁ hb hY₁).mpr
      ⟨burnsideJ410_pow_five h₂.1 hd₂, fun y hy => (hcomm12 y hy d₂ hd₂).symm⟩
  rcases hp25 with rfl | rfl
  ·
    have hsq : g' * g' = 1 := by rw [← pow_two]; exact hg'pp
    obtain ⟨h, hh, hgh⟩ := hLS.inv_conj g' hsq hg'1' hgY₁'
    have hb' : b * (h * d₂ * h⁻¹) = (h * d₂ * h⁻¹) * b := by
      calc b * (h * d₂ * h⁻¹) = (h * g' * h⁻¹) * (h * d₂ * h⁻¹) := by rw [hgh]
        _ = h * (g' * d₂) * h⁻¹ := by group
        _ = h * (d₂ * g') * h⁻¹ := by rw [hg'2]
        _ = (h * d₂ * h⁻¹) * (h * g' * h⁻¹) := by group
        _ = (h * d₂ * h⁻¹) * b := by rw [hgh]
    have hhc : ∀ x ∈ Y₁, h * x * h⁻¹ = x := by
      intro x hx
      calc h * x * h⁻¹ = (x * h) * h⁻¹ := by rw [← hh x hx]
        _ = x := by group
    have hhN : h ∈ Subgroup.normalizer (Y₁ : Set G) := burnsideJ410_mem_normalizer_of_cent hhc
    have hd₂P' : d₂ ∈ PFstar Y₁ := by rw [← hP]; exact hd₂P
    have hy1 : h * d₂ * h⁻¹ ∈ PFstar Y₁ := hLS.norm h hhN d₂ hd₂P'
    have hy2 : h * d₂ * h⁻¹ ∈ Y₁ := by
      rw [← burnsideJ410_cent_O5N hL h₁ hb hY₁]
      refine Subgroup.mem_inf.mpr ⟨by rw [hP]; exact hy1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hb'.symm
    have hd₂Y₁ : d₂ ∈ Y₁ := by
      have key : h⁻¹ * (h * d₂ * h⁻¹) = (h * d₂ * h⁻¹) * h⁻¹ := by
        calc h⁻¹ * (h * d₂ * h⁻¹) = h⁻¹ * ((h * d₂ * h⁻¹) * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * (h * d₂ * h⁻¹)) * h⁻¹ := by rw [← hh _ hy2]
          _ = (h * d₂ * h⁻¹) * h⁻¹ := by group
      have hd₂eq : d₂ = h * d₂ * h⁻¹ := by
        calc d₂ = (h⁻¹ * (h * d₂ * h⁻¹)) * h := by group
          _ = ((h * d₂ * h⁻¹) * h⁻¹) * h := by rw [key]
          _ = h * d₂ * h⁻¹ := by group
      rw [hd₂eq]; exact hy2
    exact hd₂1 (burnsideJ410_inter_triv h₂.1 hY₂
      (burnsideJ410_inv_of_ne hL h₁ hb hY₁ hc hcb) hd₂ hd₂Y₁)
  ·
    have hg'P : g' ∈ O5N Y₁ :=
      (burnsideJ410_mem_O5N hL h₁ hb hY₁).mpr ⟨hg'pp, hgY₁'⟩
    have hg'Y₀ : g' ∈ Y₀ := by
      rw [hY₀eq]
      exact Subgroup.mem_inf.mpr ⟨hg'P, Subgroup.mem_centralizer_singleton_iff.mpr hg'a⟩
    exact hnc (burnsideJ410_comm_of_gens h₀.1 h₂.1 hg'Y₀ hd₂ hg'1' hd₂1 hg'2 x₀ hx₀ d₂ hd₂)

theorem burnsideJ410_le_O5N (hL : burnsideJ410_Loc z u) {X A : Subgroup G}
    (hX : X ∈ EInv5Ru z u) (hA : A ∈ EInv5Ru z u) {p : G} (hp : p ∈ burnsideJ410_Einv z u)
    (hXp : burnsideJ410_Cent p X) (hAX : ⁅X, A⁆ = ⊥) : A ≤ O5N X := by
  have hcommA := burnsideJ410_comm_bot_iff.mp hAX
  intro a ha
  exact (burnsideJ410_mem_O5N hL hX hp hXp).mpr
    ⟨burnsideJ410_pow_five hA.1 ha, fun y hy => (hcommA y hy a ha).symm⟩

theorem burnsideJ410_pow_conj {x δ d : G} (hxδ : x * δ * x⁻¹ = δ) (hxd : x * d * x⁻¹ = δ * d)
    (m : ℕ) : x ^ m * d * (x ^ m)⁻¹ = δ ^ m * d := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc x ^ (m + 1) * d * (x ^ (m + 1))⁻¹ = x * (x ^ m * d * (x ^ m)⁻¹) * x⁻¹ := by
          rw [pow_succ']; group
      _ = x * (δ ^ m * d) * x⁻¹ := by rw [ih]
      _ = (x * δ * x⁻¹) ^ m * (x * d * x⁻¹) := by rw [conj_pow]; group
      _ = δ ^ m * (δ * d) := by rw [hxδ, hxd]
      _ = δ ^ (m + 1) * d := by rw [pow_succ]; group

open scoped Pointwise in
theorem burnsideJ410_mem_sup_normalizer {S T : Subgroup G}
    (hle : S ≤ Subgroup.normalizer (T : Set G)) {g : G} (hg : g ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, s * t = g := by
  have := Subgroup.coe_mul_of_left_le_normalizer_right S T hle
  have hg' : g ∈ ((S : Set G) * (T : Set G)) := by
    rw [← this]; exact hg
  obtain ⟨s, hs, t, ht, e⟩ := Set.mem_mul.mp hg'
  exact ⟨s, hs, t, ht, e⟩

theorem burnsideJ410_path_gens (hL : burnsideJ410_Loc z u) {Y₀ Y₁ Y₂ Y₃ : Subgroup G}
    (h₀ : Y₀ ∈ EInv5Ru z u) (h₁ : Y₁ ∈ EInv5Ru z u) (h₂ : Y₂ ∈ EInv5Ru z u)
    (h₃ : Y₃ ∈ EInv5Ru z u) {a b c : G} (ha : a ∈ burnsideJ410_Einv z u)
    (hb : b ∈ burnsideJ410_Einv z u) (hc : c ∈ burnsideJ410_Einv z u) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hY₀ : burnsideJ410_Cent a Y₀) (hY₁ : burnsideJ410_Cent b Y₁)
    (hY₂ : burnsideJ410_Cent c Y₂) (hY₃ : burnsideJ410_Cent a Y₃) (c01 : ⁅Y₀, Y₁⁆ = ⊥)
    (c12 : ⁅Y₁, Y₂⁆ = ⊥) (c23 : ⁅Y₂, Y₃⁆ = ⊥) :
    ∃ x₀ ∈ Y₀, ∃ d₁ ∈ Y₁, ∃ d₂ ∈ Y₂, ∃ x₃ ∈ Y₃, d₁ ≠ 1 ∧ d₂ ≠ 1 ∧ x₀ * d₂ ≠ d₂ * x₀ ∧
      x₀ * d₁ = d₁ * x₀ ∧ d₁ * d₂ = d₂ * d₁ ∧ x₃ * d₂ = d₂ * x₃ ∧
      x₀ * d₂ * x₀⁻¹ = d₁ * d₂ ∧ x₃ * d₁ * x₃⁻¹ = d₂⁻¹ * d₁ := by
  have c10 : ⁅Y₁, Y₀⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact c01
  have c21 : ⁅Y₂, Y₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact c12
  have c32 : ⁅Y₃, Y₂⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact c23
  obtain ⟨x₀, hx₀, d₂, hd₂, hnc⟩ := burnsideJ410_noncomm hL h₁ h₀ h₂ hb ha hc hY₁ hY₀ hY₂
    hab hbc.symm hac c10 c12
  have hd₂1 : d₂ ≠ 1 := by intro h; apply hnc; rw [h]; simp
  have hLS₁ := burnsideJ410_LS_of_label hL h₁ hb hY₁
  have hP₁ : O5N Y₁ = PFstar Y₁ := hLS₁.pcore
  have hY₀P : Y₀ ≤ PFstar Y₁ := by
    rw [← hP₁]; exact burnsideJ410_le_O5N hL h₁ h₀ hb hY₁ c10
  have hY₂P : Y₂ ≤ PFstar Y₁ := by
    rw [← hP₁]; exact burnsideJ410_le_O5N hL h₁ h₂ hb hY₁ c12
  have hd₁ : x₀ * d₂ * x₀⁻¹ * d₂⁻¹ ∈ Y₁ := hLS₁.comm_mem x₀ (hY₀P hx₀) d₂ (hY₂P hd₂)
  set d₁ : G := x₀ * d₂ * x₀⁻¹ * d₂⁻¹ with hd₁def
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    apply hnc
    calc x₀ * d₂ = (x₀ * d₂ * x₀⁻¹ * d₂⁻¹) * d₂ * x₀ := by group
      _ = d₂ * x₀ := by rw [← hd₁def, h]; group
  have hr5 : x₀ * d₂ * x₀⁻¹ = d₁ * d₂ := by rw [hd₁def]; group
  have hr2 : x₀ * d₁ = d₁ * x₀ := burnsideJ410_comm_bot_iff.mp c01 x₀ hx₀ d₁ hd₁
  have hr1 : d₁ * d₂ = d₂ * d₁ := burnsideJ410_comm_bot_iff.mp c12 d₁ hd₁ d₂ hd₂
  obtain ⟨x, hx, hx1⟩ := burnsideJ410_exists_ne_one h₃.1
  obtain ⟨p₁, hp₁, p₃, hp₃, hp13⟩ := burnsideJ410_noncomm hL h₂ h₁ h₃ hc hb ha hY₂ hY₁ hY₃
    hbc hac hab.symm c21 c23
  have hxd1 : x * d₁ ≠ d₁ * x := by
    intro h
    exact hp13 (burnsideJ410_comm_of_gens h₁.1 h₃.1 hd₁ hx hd₁1 hx1 h.symm p₁ hp₁ p₃ hp₃)
  have hLS₂ := burnsideJ410_LS_of_label hL h₂ hc hY₂
  have hP₂ : O5N Y₂ = PFstar Y₂ := hLS₂.pcore
  have hY₃P : Y₃ ≤ PFstar Y₂ := by
    rw [← hP₂]; exact burnsideJ410_le_O5N hL h₂ h₃ hc hY₂ c23
  have hY₁P : Y₁ ≤ PFstar Y₂ := by
    rw [← hP₂]; exact burnsideJ410_le_O5N hL h₂ h₁ hc hY₂ c21
  have hδ : x * d₁ * x⁻¹ * d₁⁻¹ ∈ Y₂ := hLS₂.comm_mem x (hY₃P hx) d₁ (hY₁P hd₁)
  set δ : G := x * d₁ * x⁻¹ * d₁⁻¹ with hδdef
  have hδ1 : δ ≠ 1 := by
    intro h
    apply hxd1
    calc x * d₁ = (x * d₁ * x⁻¹ * d₁⁻¹) * d₁ * x := by group
      _ = d₁ * x := by rw [← hδdef, h]; group
  have hδx : δ * x = x * δ := burnsideJ410_comm_bot_iff.mp c23 δ hδ x hx
  have hxδ : x * δ * x⁻¹ = δ := by
    calc x * δ * x⁻¹ = (δ * x) * x⁻¹ := by rw [hδx]
      _ = δ := by group
  have hxd : x * d₁ * x⁻¹ = δ * d₁ := by rw [hδdef]; group
  obtain ⟨m, hm⟩ := burnsideJ410_gen h₂.1 hδ hδ1 d₂⁻¹ (inv_mem hd₂)
  have hx₃ : x ^ m ∈ Y₃ := Subgroup.pow_mem _ hx m
  refine ⟨x₀, hx₀, d₁, hd₁, d₂, hd₂, x ^ m, hx₃, hd₁1, hd₂1, hnc, hr2, hr1, ?_, hr5, ?_⟩
  · exact (burnsideJ410_comm_bot_iff.mp c23 d₂ hd₂ (x ^ m) hx₃).symm
  · rw [burnsideJ410_pow_conj hxδ hxd m, hm]

theorem burnsideJ410_edge_swap (hL : burnsideJ410_Loc z u) {Y₀ Y₁ Y₂ Y₃ : Subgroup G}
    (h₀ : Y₀ ∈ EInv5Ru z u) (h₁ : Y₁ ∈ EInv5Ru z u) (h₂ : Y₂ ∈ EInv5Ru z u)
    (h₃ : Y₃ ∈ EInv5Ru z u) {a b c : G} (ha : a ∈ burnsideJ410_Einv z u)
    (hb : b ∈ burnsideJ410_Einv z u) (hc : c ∈ burnsideJ410_Einv z u) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hY₀ : burnsideJ410_Cent a Y₀) (hY₁ : burnsideJ410_Cent b Y₁)
    (hY₂ : burnsideJ410_Cent c Y₂) (hY₃ : burnsideJ410_Cent a Y₃) (c01 : ⁅Y₀, Y₁⁆ = ⊥)
    (c12 : ⁅Y₁, Y₂⁆ = ⊥) (c23 : ⁅Y₂, Y₃⁆ = ⊥) :
    ∃ s ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G),
      CFSG.conjugate Y₁ s = Y₂ ∧ CFSG.conjugate Y₂ s = Y₁ := by
  have c10 : ⁅Y₁, Y₀⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact c01
  obtain ⟨x₀, hx₀, d₁, hd₁, d₂, hd₂, x₃, hx₃, hd₁1, hd₂1, hnc, r2, r1, r4, r5, r3⟩ :=
    burnsideJ410_path_gens hL h₀ h₁ h₂ h₃ ha hb hc hab hac hbc hY₀ hY₁ hY₂ hY₃ c01 c12 c23
  have e1 : x₀ * d₁ * x₀⁻¹ = d₁ := by
    calc x₀ * d₁ * x₀⁻¹ = (d₁ * x₀) * x₀⁻¹ := by rw [r2]
      _ = d₁ := by group
  have e4 : x₃ * d₂ * x₃⁻¹ = d₂ := by
    calc x₃ * d₂ * x₃⁻¹ = (d₂ * x₃) * x₃⁻¹ := by rw [r4]
      _ = d₂ := by group
  set s : G := x₀ * x₃ * x₀ with hs
  have hs1 : s * d₁ * s⁻¹ = d₂⁻¹ := by
    calc s * d₁ * s⁻¹ = x₀ * (x₃ * (x₀ * d₁ * x₀⁻¹) * x₃⁻¹) * x₀⁻¹ := by rw [hs]; group
      _ = x₀ * (x₃ * d₁ * x₃⁻¹) * x₀⁻¹ := by rw [e1]
      _ = x₀ * (d₂⁻¹ * d₁) * x₀⁻¹ := by rw [r3]
      _ = (x₀ * d₂ * x₀⁻¹)⁻¹ * (x₀ * d₁ * x₀⁻¹) := by group
      _ = (d₁ * d₂)⁻¹ * d₁ := by rw [r5, e1]
      _ = d₂⁻¹ := by group
  have hs2 : s * d₂ * s⁻¹ = d₁ := by
    calc s * d₂ * s⁻¹ = x₀ * (x₃ * (x₀ * d₂ * x₀⁻¹) * x₃⁻¹) * x₀⁻¹ := by rw [hs]; group
      _ = x₀ * (x₃ * (d₁ * d₂) * x₃⁻¹) * x₀⁻¹ := by rw [r5]
      _ = x₀ * ((x₃ * d₁ * x₃⁻¹) * (x₃ * d₂ * x₃⁻¹)) * x₀⁻¹ := by group
      _ = x₀ * ((d₂⁻¹ * d₁) * d₂) * x₀⁻¹ := by rw [r3, e4]
      _ = x₀ * (d₂⁻¹ * (d₁ * d₂)) * x₀⁻¹ := by group
      _ = x₀ * (d₂⁻¹ * (d₂ * d₁)) * x₀⁻¹ := by rw [r1]
      _ = x₀ * d₁ * x₀⁻¹ := by group
      _ = d₁ := e1
  have hs1' : s⁻¹ * d₂ * s = d₁⁻¹ := by
    calc s⁻¹ * d₂ * s = s⁻¹ * (s * d₁ * s⁻¹)⁻¹ * s := by rw [hs1]; group
      _ = d₁⁻¹ := by group
  have hs2' : s⁻¹ * d₁ * s = d₂ := by
    calc s⁻¹ * d₁ * s = s⁻¹ * (s * d₂ * s⁻¹) * s := by rw [hs2]
      _ = d₂ := by group
  have hax₀ : a * x₀ = x₀ * a := burnsideJ410_cent_iff_comm.mp hY₀ x₀ hx₀
  have hax₃ : a * x₃ = x₃ * a := burnsideJ410_cent_iff_comm.mp hY₃ x₃ hx₃
  have has : a * s = s * a :=
    (((show Commute a x₀ from hax₀).mul_right (show Commute a x₃ from hax₃)).mul_right
      (show Commute a x₀ from hax₀)).eq
  have hcd : ∀ t t' : G, t * d₁ * t⁻¹ = t' * d₁ * t'⁻¹ → t * d₂ * t⁻¹ = t' * d₂ * t'⁻¹ →
      t * a = a * t → t' * a = a * t' → t = t' := by
    intro t t' h1 h2 h3 h4
    have h4' : t'⁻¹ * a = a * t'⁻¹ := by
      calc t'⁻¹ * a = t'⁻¹ * (a * t') * t'⁻¹ := by group
        _ = t'⁻¹ * (t' * a) * t'⁻¹ := by rw [h4]
        _ = a * t'⁻¹ := by group
    have hg := burnsideJ410_cent_triv hL h₀ h₁ h₂ ha hb hc hab hbc.symm hY₀ hY₁ hY₂ c10 c12
      hx₀ hd₁ hd₂ hd₁1 hnc (g := t'⁻¹ * t) (by
        calc (t'⁻¹ * t) * d₁ = t'⁻¹ * (t * d₁ * t⁻¹) * t := by group
          _ = t'⁻¹ * (t' * d₁ * t'⁻¹) * t := by rw [h1]
          _ = d₁ * (t'⁻¹ * t) := by group) (by
        calc (t'⁻¹ * t) * d₂ = t'⁻¹ * (t * d₂ * t⁻¹) * t := by group
          _ = t'⁻¹ * (t' * d₂ * t'⁻¹) * t := by rw [h2]
          _ = d₂ * (t'⁻¹ * t) := by group) (by
        calc (t'⁻¹ * t) * a = t'⁻¹ * (t * a) := by group
          _ = t'⁻¹ * (a * t) := by rw [h3]
          _ = (t'⁻¹ * a) * t := by group
          _ = (a * t'⁻¹) * t := by rw [h4']
          _ = a * (t'⁻¹ * t) := by group)
    calc t = t' * (t'⁻¹ * t) := by group
      _ = t' := by rw [hg, mul_one]
  have hbd₂ : b * d₂ * b⁻¹ = d₂⁻¹ :=
    burnsideJ410_inv_of_ne hL h₂ hc hY₂ hb hbc d₂ hd₂
  have hcd₁ : c * d₁ * c⁻¹ = d₁⁻¹ :=
    burnsideJ410_inv_of_ne hL h₁ hb hY₁ hc hbc.symm d₁ hd₁
  have hbd₁ : b * d₁ * b⁻¹ = d₁ := hY₁ d₁ hd₁
  have hcd₂ : c * d₂ * c⁻¹ = d₂ := hY₂ d₂ hd₂
  have hbs : s * b * s⁻¹ = c := by
    apply hcd
    · calc (s * b * s⁻¹) * d₁ * (s * b * s⁻¹)⁻¹ = s * (b * (s⁻¹ * d₁ * s) * b⁻¹) * s⁻¹ := by group
        _ = s * (b * d₂ * b⁻¹) * s⁻¹ := by rw [hs2']
        _ = s * d₂⁻¹ * s⁻¹ := by rw [hbd₂]
        _ = (s * d₂ * s⁻¹)⁻¹ := by group
        _ = d₁⁻¹ := by rw [hs2]
        _ = c * d₁ * c⁻¹ := hcd₁.symm
    · calc (s * b * s⁻¹) * d₂ * (s * b * s⁻¹)⁻¹ = s * (b * (s⁻¹ * d₂ * s) * b⁻¹) * s⁻¹ := by group
        _ = s * (b * d₁⁻¹ * b⁻¹) * s⁻¹ := by rw [hs1']
        _ = s * (b * d₁ * b⁻¹)⁻¹ * s⁻¹ := by group
        _ = s * d₁⁻¹ * s⁻¹ := by rw [hbd₁]
        _ = (s * d₁ * s⁻¹)⁻¹ := by group
        _ = d₂ := by rw [hs1, inv_inv]
        _ = c * d₂ * c⁻¹ := hcd₂.symm
    · have hab' : a * b = b * a := burnsideJ410_Einv_comm hL ha hb
      have h1 : Commute a (s * b * s⁻¹) :=
        ((show Commute a s from has).mul_right (show Commute a b from hab')).mul_right
          (show Commute a s from has).inv_right
      exact h1.eq.symm
    · exact burnsideJ410_Einv_comm hL hc ha
  have hcs : s * c * s⁻¹ = b := by
    apply hcd
    · calc (s * c * s⁻¹) * d₁ * (s * c * s⁻¹)⁻¹ = s * (c * (s⁻¹ * d₁ * s) * c⁻¹) * s⁻¹ := by group
        _ = s * (c * d₂ * c⁻¹) * s⁻¹ := by rw [hs2']
        _ = s * d₂ * s⁻¹ := by rw [hcd₂]
        _ = d₁ := hs2
        _ = b * d₁ * b⁻¹ := hbd₁.symm
    · calc (s * c * s⁻¹) * d₂ * (s * c * s⁻¹)⁻¹ = s * (c * (s⁻¹ * d₂ * s) * c⁻¹) * s⁻¹ := by group
        _ = s * (c * d₁⁻¹ * c⁻¹) * s⁻¹ := by rw [hs1']
        _ = s * (c * d₁ * c⁻¹)⁻¹ * s⁻¹ := by group
        _ = s * (d₁⁻¹)⁻¹ * s⁻¹ := by rw [hcd₁]
        _ = s * d₁ * s⁻¹ := by rw [inv_inv]
        _ = d₂⁻¹ := hs1
        _ = b * d₂ * b⁻¹ := hbd₂.symm
    · have hac' : a * c = c * a := burnsideJ410_Einv_comm hL ha hc
      have h1 : Commute a (s * c * s⁻¹) :=
        ((show Commute a s from has).mul_right (show Commute a c from hac')).mul_right
          (show Commute a s from has).inv_right
      exact h1.eq.symm
    · exact burnsideJ410_Einv_comm hL hb ha
  have hsEinv : ∀ t ∈ burnsideJ410_Einv z u, s * t * s⁻¹ ∈ burnsideJ410_Einv z u := by
    intro t ht
    rcases burnsideJ410_Einv_trichotomy hL ha hb hc ht hab hac hbc with rfl | rfl | rfl
    · have : s * t * s⁻¹ = t := by
        calc s * t * s⁻¹ = (t * s) * s⁻¹ := by rw [← has]
          _ = t := by group
      rw [this]; exact ha
    · rw [hbs]; exact hc
    · rw [hcs]; exact hb
  have hsN : s ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G) := by
    refine CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => ?_
    rcases (burnsideJ410_mem_E_iff hL).mp hx with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact burnsideJ410_Einv_mem_E hL (hsEinv _ (burnsideJ410_z_mem z u))
    · rw [h]; exact burnsideJ410_Einv_mem_E hL (hsEinv _ (burnsideJ410_u_mem z u))
    · rw [h]; exact burnsideJ410_Einv_mem_E hL (hsEinv _ (burnsideJ410_uz_mem z u))
  refine ⟨s, hsN, ?_, ?_⟩
  · have hzp := CFSG.Quasithin.RuType.zpowers_eq_of_card_five h₂.1 hd₂
      (burnsideJ410_pow_five h₂.1 hd₂) hd₂1
    have hle : Y₂ ≤ CFSG.conjugate Y₁ s := by
      rw [← hzp]
      refine Subgroup.zpowers_le.mpr ?_
      rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate, hs2]
      exact hd₁
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate, h₁.1, h₂.1])).symm
  · have hzp := CFSG.Quasithin.RuType.zpowers_eq_of_card_five h₁.1 hd₁
      (burnsideJ410_pow_five h₁.1 hd₁) hd₁1
    have hle : Y₁ ≤ CFSG.conjugate Y₂ s := by
      rw [← hzp]
      refine Subgroup.zpowers_le.mpr ?_
      rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate, hs1]
      exact inv_mem hd₂
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate, h₂.1, h₁.1])).symm

theorem burnsideJ410_path_sup_ne (hL : burnsideJ410_Loc z u) {Y₀ Y₁ Y₂ Y₃ : Subgroup G}
    (h₀ : Y₀ ∈ EInv5Ru z u) (h₁ : Y₁ ∈ EInv5Ru z u) (h₂ : Y₂ ∈ EInv5Ru z u)
    (h₃ : Y₃ ∈ EInv5Ru z u) {a b c : G} (ha : a ∈ burnsideJ410_Einv z u)
    (hb : b ∈ burnsideJ410_Einv z u) (hc : c ∈ burnsideJ410_Einv z u) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hY₀ : burnsideJ410_Cent a Y₀) (hY₁ : burnsideJ410_Cent b Y₁)
    (hY₂ : burnsideJ410_Cent c Y₂) (hY₃ : burnsideJ410_Cent a Y₃) (c01 : ⁅Y₀, Y₁⁆ = ⊥)
    (c12 : ⁅Y₁, Y₂⁆ = ⊥) (c23 : ⁅Y₂, Y₃⁆ = ⊥) :
    Y₀ ⊔ burnsideJ410_QOf a ≠ Y₃ ⊔ burnsideJ410_QOf a := by
  intro hsup
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x₀, hx₀, d₁, hd₁, d₂, hd₂, x₃, hx₃, hd₁1, hd₂1, hnc, r2, r1, r4, r5, r3⟩ :=
    burnsideJ410_path_gens hL h₀ h₁ h₂ h₃ ha hb hc hab hac hbc hY₀ hY₁ hY₂ hY₃ c01 c12 c23
  have hx₃sup : x₃ ∈ Y₀ ⊔ burnsideJ410_QOf a := by
    rw [hsup]; exact Subgroup.mem_sup_left hx₃
  have hCa : ∀ y ∈ Y₀, y ∈ Subgroup.centralizer ({a} : Set G) := fun y hy =>
    burnsideJ410_le_centralizer_of_cent hY₀ hy
  have hQconj : ∀ h ∈ Subgroup.centralizer ({a} : Set G), ∀ q ∈ burnsideJ410_QOf a,
      h * q * h⁻¹ ∈ burnsideJ410_QOf a := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) hh)
      q).mp hq
  have hY₀N : Y₀ ≤ Subgroup.normalizer (burnsideJ410_QOf a : Set G) := fun y hy =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) (hCa y hy)
  obtain ⟨y, hy, q, hq, hyq⟩ := burnsideJ410_mem_sup_normalizer hY₀N hx₃sup
  have hxy : x₀ * y = y * x₀ := burnsideJ410_comm_of_card_five h₀.1 x₀ hx₀ y hy
  set κ : G := x₀ * x₃ * x₀⁻¹ * x₃⁻¹ with hκdef
  have hκ : κ = y * (x₀ * q * x₀⁻¹ * q⁻¹) * y⁻¹ := by
    rw [hκdef, ← hyq]
    calc x₀ * (y * q) * x₀⁻¹ * (y * q)⁻¹ = (x₀ * y) * q * x₀⁻¹ * q⁻¹ * y⁻¹ := by group
      _ = (y * x₀) * q * x₀⁻¹ * q⁻¹ * y⁻¹ := by rw [hxy]
      _ = y * (x₀ * q * x₀⁻¹ * q⁻¹) * y⁻¹ := by group
  have hκQ : κ ∈ burnsideJ410_QOf a := by
    rw [hκ]
    exact hQconj y (hCa y hy) _ (mul_mem (hQconj x₀ (hCa x₀ hx₀) q hq) (inv_mem hq))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, κ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({a} : Set G)) ⟨κ, hκQ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have e1 : x₀ * d₁ * x₀⁻¹ = d₁ := by
    calc x₀ * d₁ * x₀⁻¹ = (d₁ * x₀) * x₀⁻¹ := by rw [r2]
      _ = d₁ := by group
  have e4 : x₃ * d₂ * x₃⁻¹ = d₂ := by
    calc x₃ * d₂ * x₃⁻¹ = (d₂ * x₃) * x₃⁻¹ := by rw [r4]
      _ = d₂ := by group
  have i1 : x₀⁻¹ * d₁ * x₀ = d₁ := by
    calc x₀⁻¹ * d₁ * x₀ = x₀⁻¹ * (d₁ * x₀) := by group
      _ = x₀⁻¹ * (x₀ * d₁) := by rw [r2]
      _ = d₁ := by group
  have i2 : x₀⁻¹ * d₂ * x₀ = d₁⁻¹ * d₂ := by
    calc x₀⁻¹ * d₂ * x₀ = d₁⁻¹ * (d₁ * (x₀⁻¹ * d₂ * x₀)) := by group
      _ = d₁⁻¹ * ((x₀⁻¹ * d₁ * x₀) * (x₀⁻¹ * d₂ * x₀)) := by rw [i1]
      _ = d₁⁻¹ * (x₀⁻¹ * (d₁ * d₂) * x₀) := by group
      _ = d₁⁻¹ * (x₀⁻¹ * (x₀ * d₂ * x₀⁻¹) * x₀) := by rw [r5]
      _ = d₁⁻¹ * d₂ := by group
  have j2 : x₃⁻¹ * d₂ * x₃ = d₂ := by
    calc x₃⁻¹ * d₂ * x₃ = x₃⁻¹ * (d₂ * x₃) := by group
      _ = x₃⁻¹ * (x₃ * d₂) := by rw [r4]
      _ = d₂ := by group
  have j1 : x₃⁻¹ * d₁ * x₃ = d₂ * d₁ := by
    calc x₃⁻¹ * d₁ * x₃ = d₂ * (d₂⁻¹ * (x₃⁻¹ * d₁ * x₃)) := by group
      _ = d₂ * ((x₃⁻¹ * d₂ * x₃)⁻¹ * (x₃⁻¹ * d₁ * x₃)) := by rw [j2]
      _ = d₂ * (x₃⁻¹ * (d₂⁻¹ * d₁) * x₃) := by group
      _ = d₂ * (x₃⁻¹ * (x₃ * d₁ * x₃⁻¹) * x₃) := by rw [r3]
      _ = d₂ * d₁ := by group
  have hd : (d₁⁻¹ * d₂) * d₁ = d₂ := by
    calc (d₁⁻¹ * d₂) * d₁ = d₁⁻¹ * (d₂ * d₁) := by group
      _ = d₁⁻¹ * (d₁ * d₂) := by rw [r1]
      _ = d₂ := by group
  have hκ1 : κ * d₁ * κ⁻¹ = d₁ * d₂ := by
    calc κ * d₁ * κ⁻¹ = x₀ * (x₃ * (x₀⁻¹ * (x₃⁻¹ * d₁ * x₃) * x₀) * x₃⁻¹) * x₀⁻¹ := by
          rw [hκdef]; group
      _ = x₀ * (x₃ * (x₀⁻¹ * (d₂ * d₁) * x₀) * x₃⁻¹) * x₀⁻¹ := by rw [j1]
      _ = x₀ * (x₃ * ((x₀⁻¹ * d₂ * x₀) * (x₀⁻¹ * d₁ * x₀)) * x₃⁻¹) * x₀⁻¹ := by group
      _ = x₀ * (x₃ * ((d₁⁻¹ * d₂) * d₁) * x₃⁻¹) * x₀⁻¹ := by rw [i2, i1]
      _ = x₀ * (x₃ * d₂ * x₃⁻¹) * x₀⁻¹ := by rw [hd]
      _ = x₀ * d₂ * x₀⁻¹ := by rw [e4]
      _ = d₁ * d₂ := r5
  have hκ2 : κ * d₂ * κ⁻¹ = d₁ * d₂ ^ 2 := by
    calc κ * d₂ * κ⁻¹ = x₀ * (x₃ * (x₀⁻¹ * (x₃⁻¹ * d₂ * x₃) * x₀) * x₃⁻¹) * x₀⁻¹ := by
          rw [hκdef]; group
      _ = x₀ * (x₃ * (x₀⁻¹ * d₂ * x₀) * x₃⁻¹) * x₀⁻¹ := by rw [j2]
      _ = x₀ * (x₃ * (d₁⁻¹ * d₂) * x₃⁻¹) * x₀⁻¹ := by rw [i2]
      _ = x₀ * ((x₃ * d₁ * x₃⁻¹)⁻¹ * (x₃ * d₂ * x₃⁻¹)) * x₀⁻¹ := by group
      _ = x₀ * ((d₂⁻¹ * d₁)⁻¹ * d₂) * x₀⁻¹ := by rw [r3, e4]
      _ = (x₀ * d₁ * x₀⁻¹)⁻¹ * (x₀ * d₂ * x₀⁻¹) * (x₀ * d₂ * x₀⁻¹) := by group
      _ = d₁⁻¹ * (d₁ * d₂) * (d₁ * d₂) := by rw [e1, r5]
      _ = d₂ * (d₁ * d₂) := by group
      _ = (d₂ * d₁) * d₂ := by group
      _ = (d₁ * d₂) * d₂ := by rw [r1]
      _ = d₁ * d₂ ^ 2 := by rw [pow_two, mul_assoc]
  have hzp : Subgroup.zpowers d₂ = Y₂ :=
    CFSG.Quasithin.RuType.zpowers_eq_of_card_five h₂.1 hd₂ (burnsideJ410_pow_five h₂.1 hd₂) hd₂1
  have hindep : ∀ t : ℤ, d₁ ^ t ∈ Subgroup.zpowers d₂ → d₁ ^ t = 1 := by
    intro t ht
    have hY₂m : d₁ ^ t ∈ Y₂ := by rw [← hzp]; exact ht
    have hY₁m : d₁ ^ t ∈ Y₁ := Subgroup.zpow_mem _ hd₁ t
    exact burnsideJ410_inter_triv h₂.1 hY₂ (burnsideJ410_inv_of_ne hL h₁ hb hY₁ hc hbc.symm)
      hY₂m hY₁m
  exact burnsideJ410_no_two_element (orderOf_eq_prime (burnsideJ410_pow_five h₁.1 hd₁) hd₁1)
    (burnsideJ410_pow_five h₂.1 hd₂) r1 hindep hκ1 hκ2 hk

end Path

end BurnsideJ410C

section BurnsideJ410D

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]

structure burnsideJ410_Fix (z u : G) (F1 B5 : Subgroup G) : Prop where
  F1_le : F1 ≤ Subgroup.centralizer ({z} : Set G)
  E_le : burnsideJ410_E z u ≤ F1
  B5_le : B5 ≤ F1
  B5_card : Nat.card B5 = 5
  B5_inv : burnsideJ410_Inv u B5
  F1_card : Nat.card F1 = 2 ^ 12 * 5
  H_card : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ 11 * 120
  Z_le : ∀ c ∈ F1, (∀ f ∈ F1, f * c = c * f) → c ∈ Subgroup.zpowers z
  Q_le : burnsideJ410_QOf z ≤ Subgroup.normalizer (F1 : Set G)
  F1_norm : F1 ≤ Subgroup.normalizer ((B5 ⊔ burnsideJ410_QOf z : Subgroup G) : Set G)
  NH_le : ∀ n ∈ Subgroup.centralizer ({z} : Set G), n ∈ Subgroup.normalizer (B5 : Set G) →
    n ∈ Subgroup.normalizer (F1 : Set G)
  S5 : ∀ w : G, w * w = 1 → z * w = w * z → w ∉ burnsideJ410_QOf z →
    ∀ Y₁ Y₂ Y₃ : Subgroup G,
      (Y₁ ≤ Subgroup.centralizer ({z} : Set G) ∧ Nat.card Y₁ = 5 ∧
        w ∈ Subgroup.normalizer ((Y₁ ⊔ burnsideJ410_QOf z : Subgroup G) : Set G)) →
      (Y₂ ≤ Subgroup.centralizer ({z} : Set G) ∧ Nat.card Y₂ = 5 ∧
        w ∈ Subgroup.normalizer ((Y₂ ⊔ burnsideJ410_QOf z : Subgroup G) : Set G)) →
      (Y₃ ≤ Subgroup.centralizer ({z} : Set G) ∧ Nat.card Y₃ = 5 ∧
        w ∈ Subgroup.normalizer ((Y₃ ⊔ burnsideJ410_QOf z : Subgroup G) : Set G)) →
      Y₁ ⊔ burnsideJ410_QOf z = Y₂ ⊔ burnsideJ410_QOf z ∨
        Y₁ ⊔ burnsideJ410_QOf z = Y₃ ⊔ burnsideJ410_QOf z ∨
        Y₂ ⊔ burnsideJ410_QOf z = Y₃ ⊔ burnsideJ410_QOf z

variable [Finite G]

theorem burnsideJ410_conj_le_iff {A B : Subgroup G} (g : G) :
    CFSG.conjugate A g ≤ CFSG.conjugate B g ↔ A ≤ B := by
  constructor
  · intro h x hx
    have h1 : g⁻¹ * x * g ∈ CFSG.conjugate A g := burnsideJ410_mem_conj_inv g hx
    have h2 := h h1
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at h2
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [this] at h2
  · intro h x hx
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hx ⊢
    exact h hx

theorem burnsideJ410_conj_conj_inv (A : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate A g) g⁻¹ = A := by
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, mul_inv_cancel,
    CFSG.ASVolI.RuChoice.fx_conjugate_one]

theorem burnsideJ410_conj_inv_conj (A : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate A g⁻¹) g = A := by
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, inv_mul_cancel,
    CFSG.ASVolI.RuChoice.fx_conjugate_one]

theorem burnsideJ410_conj_inj {A B : Subgroup G} (g : G)
    (h : CFSG.conjugate A g = CFSG.conjugate B g) : A = B := by
  have := congrArg (fun X => CFSG.conjugate X g⁻¹) h
  simpa [burnsideJ410_conj_conj_inv] using this

open CFSG.LieType.BorelTits in
theorem burnsideJ410_pCoreOf_conj (X : Subgroup G) (t : G) :
    pCoreOf 2 (CFSG.conjugate X t) = CFSG.conjugate (pCoreOf 2 X) t := by
  have key : ∀ (X : Subgroup G) (t : G),
      CFSG.conjugate (pCoreOf 2 X) t ≤ pCoreOf 2 (CFSG.conjugate X t) := by
    intro X t
    refine le_pCoreOf_of_le_normalizer 2 ((burnsideJ410_conj_le_iff t).mpr
      (pCoreOf_le 2 X)) ?_ ?_
    · rw [CFSG.ASVolI.RuChoice.fx_normalizer_conjugate, burnsideJ410_conj_le_iff]
      exact le_normalizer_pCoreOf 2 X
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X).exists_card_eq
      exact IsPGroup.of_card (n := k) (by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hk)
  apply le_antisymm _ (key X t)
  have h := key (CFSG.conjugate X t) t⁻¹
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, mul_inv_cancel,
    CFSG.ASVolI.RuChoice.fx_conjugate_one] at h
  rw [← burnsideJ410_conj_le_iff t⁻¹, CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, mul_inv_cancel,
    CFSG.ASVolI.RuChoice.fx_conjugate_one]
  exact h

theorem burnsideJ410_conj_centralizer (w g : G) :
    CFSG.conjugate (Subgroup.centralizer ({w} : Set G)) g =
      Subgroup.centralizer ({g⁻¹ * w * g} : Set G) := by
  ext x
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have h := burnsideJ410_comm_conj g x (g⁻¹ * w * g)
  rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h
  exact h

theorem burnsideJ410_conj_QOf (w g : G) :
    CFSG.conjugate (burnsideJ410_QOf w) g = burnsideJ410_QOf (g⁻¹ * w * g) := by
  unfold burnsideJ410_QOf
  rw [← burnsideJ410_pCoreOf_conj, burnsideJ410_conj_centralizer]

theorem burnsideJ410_mem_H_iff {z k : G} :
    k ∈ Subgroup.centralizer ({z} : Set G) ↔ k⁻¹ * z * k = z := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [← h]
      _ = z := by group
  · intro h
    calc k * z = k * (k⁻¹ * z * k) := by rw [h]
      _ = z * k := by group

theorem burnsideJ410_sylow_conj {K : Subgroup G} (hK : ¬ 5 ^ 2 ∣ Nat.card K)
    {Y Y' : Subgroup G} (hY : Nat.card Y = 5) (hY' : Nat.card Y' = 5) (hYK : Y ≤ K)
    (hY'K : Y' ≤ K) : ∃ g ∈ K, Y' = CFSG.conjugate Y g := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy, hy5, hy1, -⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five hY
  obtain ⟨y', hy', hy5', hy1', -⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five hY'
  have hzy := CFSG.Quasithin.RuType.zpowers_eq_of_card_five hY hy hy5 hy1
  have hzy' := CFSG.Quasithin.RuType.zpowers_eq_of_card_five hY' hy' hy5' hy1'
  obtain ⟨g, hg, hgy⟩ := CFSG.Quasithin.RuType.exists_conj_zpowers hK (hYK hy) (hY'K hy')
    (orderOf_eq_prime hy5 hy1) (orderOf_eq_prime hy5' hy1')
  refine ⟨g⁻¹, inv_mem hg, ?_⟩
  have hc : CFSG.conjugate Y g⁻¹ = Subgroup.zpowers (g * y * g⁻¹) := by
    rw [← hzy, CFSG.ASVolI.RuChoice.fx_conjugate_zpowers]
    simp
  have hle : Y' ≤ CFSG.conjugate Y g⁻¹ := by
    rw [← hzy', hc]
    exact Subgroup.zpowers_le.mpr hgy
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.ASVolI.RuChoice.fx_card_conjugate, hY, hY'])

theorem burnsideJ410_conj_Q_eq {z n : G} (hn : n ∈ Subgroup.centralizer ({z} : Set G)) :
    CFSG.conjugate (burnsideJ410_QOf z) n = burnsideJ410_QOf z := by
  unfold burnsideJ410_QOf
  exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) hn)

theorem burnsideJ410_QOf_conj_mem {z h : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G)) {q : G}
    (hq : q ∈ burnsideJ410_QOf z) : h * q * h⁻¹ ∈ burnsideJ410_QOf z := by
  unfold burnsideJ410_QOf at hq ⊢
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) hh) q).mp hq

theorem burnsideJ410_Z1 {z u : G} {F1 B5 : Subgroup G} (hF : burnsideJ410_Fix z u F1 B5) {n : G}
    (hn : n ∈ Subgroup.centralizer ({z} : Set G)) {Y : Subgroup G}
    (hY : Y ≤ CFSG.conjugate F1 n) (hYc : Nat.card Y = 5) :
    Y ⊔ burnsideJ410_QOf z = CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z := by
  have hQn := burnsideJ410_conj_Q_eq hn
  have hY₀F : CFSG.conjugate B5 n ≤ CFSG.conjugate F1 n :=
    CFSG.ASVolI.RuChoice.fx_conjugate_mono n hF.B5_le
  have hY₀c : Nat.card (CFSG.conjugate B5 n) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF.B5_card
  have hK : ¬ 5 ^ 2 ∣ Nat.card (CFSG.conjugate F1 n) := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate, hF.F1_card]; norm_num
  obtain ⟨g, hg, hYeq⟩ := burnsideJ410_sylow_conj hK hY₀c hYc hY₀F hY
  have hgH : g ∈ Subgroup.centralizer ({z} : Set G) :=
    (CFSG.ASVolI.RuChoice.fx_conjugate_le hF.F1_le hn) hg
  have hQg := burnsideJ410_conj_Q_eq hgH
  have hgN : g ∈ Subgroup.normalizer
      ((CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z : Subgroup G) : Set G) := by
    have h1 : CFSG.conjugate F1 n ≤ CFSG.conjugate
        (Subgroup.normalizer ((B5 ⊔ burnsideJ410_QOf z : Subgroup G) : Set G)) n :=
      CFSG.ASVolI.RuChoice.fx_conjugate_mono n hF.F1_norm
    rw [← CFSG.ASVolI.RuChoice.fx_normalizer_conjugate, CFSG.ASVolI.RuChoice.fx_conjugate_sup,
      hQn] at h1
    exact h1 hg
  calc Y ⊔ burnsideJ410_QOf z
      = CFSG.conjugate (CFSG.conjugate B5 n) g ⊔ CFSG.conjugate (burnsideJ410_QOf z) g := by
        rw [hYeq, hQg]
    _ = CFSG.conjugate (CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z) g :=
        (CFSG.ASVolI.RuChoice.fx_conjugate_sup _ _ _).symm
    _ = CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z :=
        CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hgN

theorem burnsideJ410_Z2 {z u : G} {F1 B5 : Subgroup G} (hF : burnsideJ410_Fix z u F1 B5)
    {n n' : G} (hn : n ∈ Subgroup.centralizer ({z} : Set G))
    (hn' : n' ∈ Subgroup.centralizer ({z} : Set G))
    (h : CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z = CFSG.conjugate B5 n' ⊔ burnsideJ410_QOf z) :
    CFSG.conjugate F1 n = CFSG.conjugate F1 n' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQn := burnsideJ410_conj_Q_eq hn
  have hY₀F : CFSG.conjugate B5 n ≤ CFSG.conjugate F1 n :=
    CFSG.ASVolI.RuChoice.fx_conjugate_mono n hF.B5_le
  have hY₀c : Nat.card (CFSG.conjugate B5 n) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF.B5_card
  have hY2c : Nat.card (CFSG.conjugate B5 n') = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF.B5_card
  have hQp : IsPGroup 2 (burnsideJ410_QOf z) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hY₀H : CFSG.conjugate B5 n ≤ Subgroup.centralizer ({z} : Set G) :=
    hY₀F.trans (CFSG.ASVolI.RuChoice.fx_conjugate_le hF.F1_le hn)
  have hY₀N : CFSG.conjugate B5 n ≤ Subgroup.normalizer (burnsideJ410_QOf z : Set G) :=
    fun y hy => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hY₀H hy)
  have hinf : CFSG.conjugate B5 n ⊓ burnsideJ410_QOf z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hQp ⟨x, hx.2⟩
    have h2k : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h5 := burnsideJ410_pow_five hY₀c hx.1
    have := (pow_gcd_eq_one (a := x)).mpr ⟨h5, h2k⟩
    rwa [show Nat.gcd 5 (2 ^ k) = 1 from Nat.Coprime.pow_right k (by norm_num), pow_one] at this
  have hcardK : ¬ 5 ^ 2 ∣ Nat.card (CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z : Subgroup G) := by
    have hprod := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes hY₀N
    rw [hinf, Subgroup.card_bot, mul_one, hY₀c] at hprod
    obtain ⟨j, hj⟩ := hQp.exists_card_eq
    rw [hprod, hj]
    intro hd
    have h5 : 5 ∣ 2 ^ j := by
      have : 5 * 5 ∣ 5 * 2 ^ j := by simpa using hd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
    omega
  have hY₀K : CFSG.conjugate B5 n ≤ CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z := le_sup_left
  have hY2K : CFSG.conjugate B5 n' ≤ CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z := by
    rw [h]; exact le_sup_left
  obtain ⟨g, hg, hgeq⟩ := burnsideJ410_sylow_conj hcardK hY₀c hY2c hY₀K hY2K
  have hQN : burnsideJ410_QOf z ≤
      Subgroup.normalizer ((CFSG.conjugate F1 n : Subgroup G) : Set G) := by
    rw [CFSG.ASVolI.RuChoice.fx_normalizer_conjugate]
    intro q hq
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
    have : q ∈ CFSG.conjugate (burnsideJ410_QOf z) n := by rw [hQn]; exact hq
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at this
    exact hF.Q_le this
  have hKN : (CFSG.conjugate B5 n ⊔ burnsideJ410_QOf z : Subgroup G) ≤
      Subgroup.normalizer ((CFSG.conjugate F1 n : Subgroup G) : Set G) :=
    sup_le (hY₀F.trans Subgroup.le_normalizer) hQN
  have hY2F : CFSG.conjugate B5 n' ≤ CFSG.conjugate F1 n := by
    rw [hgeq]
    calc CFSG.conjugate (CFSG.conjugate B5 n) g ≤ CFSG.conjugate (CFSG.conjugate F1 n) g :=
          CFSG.ASVolI.RuChoice.fx_conjugate_mono g hY₀F
      _ = CFSG.conjugate F1 n := CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (hKN hg)
  have hY3F1 : CFSG.conjugate (CFSG.conjugate B5 n') n⁻¹ ≤ F1 := by
    have := CFSG.ASVolI.RuChoice.fx_conjugate_mono n⁻¹ hY2F
    rwa [burnsideJ410_conj_conj_inv] at this
  have hY3c : Nat.card (CFSG.conjugate (CFSG.conjugate B5 n') n⁻¹) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hY2c
  have hK1 : ¬ 5 ^ 2 ∣ Nat.card F1 := by rw [hF.F1_card]; norm_num
  obtain ⟨f, hf, hfeq⟩ := burnsideJ410_sylow_conj hK1 hF.B5_card hY3c hF.B5_le hY3F1
  have hYeq : CFSG.conjugate B5 n' = CFSG.conjugate B5 (f * n) := by
    calc CFSG.conjugate B5 n' = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate B5 n') n⁻¹) n :=
          (burnsideJ410_conj_inv_conj _ n).symm
      _ = CFSG.conjugate (CFSG.conjugate B5 f) n := by rw [hfeq]
      _ = CFSG.conjugate B5 (f * n) := CFSG.ASVolI.RuChoice.fx_conjugate_conjugate _ _ _
  have hfH : f ∈ Subgroup.centralizer ({z} : Set G) := hF.F1_le hf
  have hmH : (f * n) * n'⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem hfH hn) (inv_mem hn')
  have hmN : (f * n) * n'⁻¹ ∈ Subgroup.normalizer (B5 : Set G) := by
    refine CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => ?_
    have h1 : n'⁻¹ * x * n' ∈ CFSG.conjugate B5 n' := burnsideJ410_mem_conj_inv n' hx
    rw [hYeq, CFSG.ASVolI.RuChoice.fx_mem_conjugate] at h1
    have e : f * n * n'⁻¹ * x * (f * n * n'⁻¹)⁻¹ = f * n * (n'⁻¹ * x * n') * (f * n)⁻¹ := by group
    rw [e]; exact h1
  have hm := hF.NH_le _ hmH hmN
  calc CFSG.conjugate F1 n = CFSG.conjugate (CFSG.conjugate F1 f) n := by
        rw [CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer hf)]
    _ = CFSG.conjugate F1 (f * n) := CFSG.ASVolI.RuChoice.fx_conjugate_conjugate _ _ _
    _ = CFSG.conjugate F1 ((f * n * n'⁻¹) * n') := by rw [inv_mul_cancel_right]
    _ = CFSG.conjugate (CFSG.conjugate F1 (f * n * n'⁻¹)) n' :=
        (CFSG.ASVolI.RuChoice.fx_conjugate_conjugate _ _ _).symm
    _ = CFSG.conjugate F1 n' := by rw [CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hm]

theorem burnsideJ410_Zeq_iff {z u : G} {F1 B5 : Subgroup G} (hF : burnsideJ410_Fix z u F1 B5)
    {n n' : G} (hn : n ∈ Subgroup.centralizer ({z} : Set G))
    (hn' : n' ∈ Subgroup.centralizer ({z} : Set G)) {Y Y' : Subgroup G}
    (hY : Y ≤ CFSG.conjugate F1 n) (hY' : Y' ≤ CFSG.conjugate F1 n')
    (cY : Nat.card Y = 5) (cY' : Nat.card Y' = 5) :
    CFSG.conjugate F1 n = CFSG.conjugate F1 n' ↔
      Y ⊔ burnsideJ410_QOf z = Y' ⊔ burnsideJ410_QOf z := by
  constructor
  · intro h
    rw [burnsideJ410_Z1 hF hn hY cY, burnsideJ410_Z1 hF hn (h ▸ hY') cY']
  · intro h
    apply burnsideJ410_Z2 hF hn hn'
    rw [← burnsideJ410_Z1 hF hn hY cY, ← burnsideJ410_Z1 hF hn' hY' cY', h]

theorem burnsideJ410_Fset_le_centralizer {z u : G} {F1 B5 : Subgroup G}
    (hF : burnsideJ410_Fix z u F1 B5) {v : G} {E : Subgroup G} (hE : E ∈ FsetRu F1 z v) :
    E ≤ Subgroup.centralizer ({v} : Set G) := by
  obtain ⟨k, hk, rfl⟩ := hE
  have := CFSG.ASVolI.RuChoice.fx_conjugate_mono k hF.F1_le
  rwa [burnsideJ410_conj_centralizer, hk] at this

theorem burnsideJ410_Fset_le_normalizer {z u : G} {F1 B5 : Subgroup G}
    (hF : burnsideJ410_Fix z u F1 B5) {v k : G} (hk : k⁻¹ * z * k = v) :
    CFSG.conjugate F1 k ≤
      Subgroup.normalizer ((CFSG.conjugate B5 k ⊔ burnsideJ410_QOf v : Subgroup G) : Set G) := by
  have h1 := CFSG.ASVolI.RuChoice.fx_conjugate_mono k hF.F1_norm
  rw [← CFSG.ASVolI.RuChoice.fx_normalizer_conjugate, CFSG.ASVolI.RuChoice.fx_conjugate_sup,
    burnsideJ410_conj_QOf, hk] at h1
  exact h1

theorem burnsideJ410_frame_exists {z u : G} {F1 B5 : Subgroup G}
    (hF : burnsideJ410_Fix z u F1 B5) {v : G} (hv : IsConj z v) {Y : Subgroup G}
    (hY : Nat.card Y = 5) (hYv : Y ≤ Subgroup.centralizer ({v} : Set G)) :
    ∃ k : G, k⁻¹ * z * k = v ∧ Y = CFSG.conjugate B5 k := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hv
  have hA'c : Nat.card (CFSG.conjugate Y c) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hY
  have hA'z : CFSG.conjugate Y c ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hx
    have h : c * x * c⁻¹ * v = v * (c * x * c⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp (hYv hx)
    rw [← hc] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (burnsideJ410_comm_conj c x z).mp h
  have hK : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    rw [hF.H_card]; norm_num
  have hB5H : B5 ≤ Subgroup.centralizer ({z} : Set G) := hF.B5_le.trans hF.F1_le
  obtain ⟨h, hh, hheq⟩ := burnsideJ410_sylow_conj hK hF.B5_card hA'c hB5H hA'z
  refine ⟨h * c⁻¹, ?_, ?_⟩
  · have hz := burnsideJ410_mem_H_iff.mp hh
    calc (h * c⁻¹)⁻¹ * z * (h * c⁻¹) = c * (h⁻¹ * z * h) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [hz]
      _ = v := hc
  · calc Y = CFSG.conjugate (CFSG.conjugate Y c) c⁻¹ := (burnsideJ410_conj_conj_inv Y c).symm
      _ = CFSG.conjugate (CFSG.conjugate B5 h) c⁻¹ := by rw [hheq]
      _ = CFSG.conjugate B5 (h * c⁻¹) := CFSG.ASVolI.RuChoice.fx_conjugate_conjugate _ _ _

theorem burnsideJ410_Fset_exists {z u : G} {F1 B5 : Subgroup G}
    (hF : burnsideJ410_Fix z u F1 B5) {v : G} (hv : IsConj z v) {Y : Subgroup G}
    (hY : Nat.card Y = 5) (hYv : Y ≤ Subgroup.centralizer ({v} : Set G)) :
    ∃ E' ∈ FsetRu F1 z v, Y ≤ E' := by
  obtain ⟨k, hk, hYk⟩ := burnsideJ410_frame_exists hF hv hY hYv
  refine ⟨CFSG.conjugate F1 k, ⟨k, hk, rfl⟩, ?_⟩
  rw [hYk]
  exact CFSG.ASVolI.RuChoice.fx_conjugate_mono k hF.B5_le

theorem burnsideJ410_Fset_eq_iff {z u : G} {F1 B5 : Subgroup G}
    (hF : burnsideJ410_Fix z u F1 B5) {v : G} {E₁ E₂ Y₁ Y₂ : Subgroup G}
    (h₁ : E₁ ∈ FsetRu F1 z v) (h₂ : E₂ ∈ FsetRu F1 z v) (hY₁ : Y₁ ≤ E₁) (hY₂ : Y₂ ≤ E₂)
    (c₁ : Nat.card Y₁ = 5) (c₂ : Nat.card Y₂ = 5) :
    E₁ = E₂ ↔ Y₁ ⊔ burnsideJ410_QOf v = Y₂ ⊔ burnsideJ410_QOf v := by
  obtain ⟨k₁, hk₁, rfl⟩ := h₁
  obtain ⟨k₂, hk₂, rfl⟩ := h₂
  have hz : k₁ * v * k₁⁻¹ = z := by rw [← hk₁]; group
  have hn₂ : k₂ * k₁⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [burnsideJ410_mem_H_iff]
    calc (k₂ * k₁⁻¹)⁻¹ * z * (k₂ * k₁⁻¹) = k₁ * (k₂⁻¹ * z * k₂) * k₁⁻¹ := by group
      _ = k₁ * v * k₁⁻¹ := by rw [hk₂]
      _ = z := hz
  have hn₁ : (1 : G) ∈ Subgroup.centralizer ({z} : Set G) := one_mem _
  have hE₂ : CFSG.conjugate F1 k₂ = CFSG.conjugate (CFSG.conjugate F1 (k₂ * k₁⁻¹)) k₁ := by
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, inv_mul_cancel_right]
  have hE₁ : CFSG.conjugate F1 k₁ = CFSG.conjugate (CFSG.conjugate F1 1) k₁ := by
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_one]
  have hY₁' : CFSG.conjugate Y₁ k₁⁻¹ ≤ CFSG.conjugate F1 1 := by
    have := CFSG.ASVolI.RuChoice.fx_conjugate_mono k₁⁻¹ hY₁
    rw [hE₁, burnsideJ410_conj_conj_inv] at this
    exact this
  have hY₂' : CFSG.conjugate Y₂ k₁⁻¹ ≤ CFSG.conjugate F1 (k₂ * k₁⁻¹) := by
    have := CFSG.ASVolI.RuChoice.fx_conjugate_mono k₁⁻¹ hY₂
    rw [hE₂, burnsideJ410_conj_conj_inv] at this
    exact this
  have hc₁ : Nat.card (CFSG.conjugate Y₁ k₁⁻¹) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact c₁
  have hc₂ : Nat.card (CFSG.conjugate Y₂ k₁⁻¹) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact c₂
  have key := burnsideJ410_Zeq_iff hF hn₁ hn₂ hY₁' hY₂' hc₁ hc₂
  have hQ : CFSG.conjugate (burnsideJ410_QOf v) k₁⁻¹ = burnsideJ410_QOf z := by
    rw [burnsideJ410_conj_QOf]
    congr 1
    rw [inv_inv]; exact hz
  rw [hE₁, hE₂]
  constructor
  · intro h
    have h' := burnsideJ410_conj_inj k₁ h
    have h'' := key.mp h'
    rw [← hQ, ← CFSG.ASVolI.RuChoice.fx_conjugate_sup, ← CFSG.ASVolI.RuChoice.fx_conjugate_sup]
      at h''
    exact burnsideJ410_conj_inj k₁⁻¹ h''
  · intro h
    have h1 : CFSG.conjugate (Y₁ ⊔ burnsideJ410_QOf v) k₁⁻¹ =
        CFSG.conjugate (Y₂ ⊔ burnsideJ410_QOf v) k₁⁻¹ := by rw [h]
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_sup, CFSG.ASVolI.RuChoice.fx_conjugate_sup, hQ] at h1
    rw [key.mpr h1]

theorem burnsideJ410_S5_v {z u : G} {F1 B5 : Subgroup G} (hF : burnsideJ410_Fix z u F1 B5)
    {v : G} (hv : IsConj z v) {w : G} (hw2 : w * w = 1) (hvw : v * w = w * v)
    (hwQ : w ∉ burnsideJ410_QOf v) {Y₁ Y₂ Y₃ : Subgroup G}
    (h₁ : Y₁ ≤ Subgroup.centralizer ({v} : Set G) ∧ Nat.card Y₁ = 5 ∧
      w ∈ Subgroup.normalizer ((Y₁ ⊔ burnsideJ410_QOf v : Subgroup G) : Set G))
    (h₂ : Y₂ ≤ Subgroup.centralizer ({v} : Set G) ∧ Nat.card Y₂ = 5 ∧
      w ∈ Subgroup.normalizer ((Y₂ ⊔ burnsideJ410_QOf v : Subgroup G) : Set G))
    (h₃ : Y₃ ≤ Subgroup.centralizer ({v} : Set G) ∧ Nat.card Y₃ = 5 ∧
      w ∈ Subgroup.normalizer ((Y₃ ⊔ burnsideJ410_QOf v : Subgroup G) : Set G)) :
    Y₁ ⊔ burnsideJ410_QOf v = Y₂ ⊔ burnsideJ410_QOf v ∨
      Y₁ ⊔ burnsideJ410_QOf v = Y₃ ⊔ burnsideJ410_QOf v ∨
      Y₂ ⊔ burnsideJ410_QOf v = Y₃ ⊔ burnsideJ410_QOf v := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hv
  have hcv : c⁻¹ * v * c = z := by rw [← hc]; group
  have hQ : CFSG.conjugate (burnsideJ410_QOf v) c = burnsideJ410_QOf z := by
    rw [burnsideJ410_conj_QOf]
    congr 1
  have hCz : CFSG.conjugate (Subgroup.centralizer ({v} : Set G)) c =
      Subgroup.centralizer ({z} : Set G) := by
    rw [burnsideJ410_conj_centralizer, hcv]
  have hw₀2 : (c⁻¹ * w * c) * (c⁻¹ * w * c) = 1 := by
    calc (c⁻¹ * w * c) * (c⁻¹ * w * c) = c⁻¹ * (w * w) * c := by group
      _ = 1 := by rw [hw2]; group
  have hzw₀ : z * (c⁻¹ * w * c) = (c⁻¹ * w * c) * z := by
    have h := (burnsideJ410_comm_conj c⁻¹ v w).mpr hvw
    simp only [inv_inv] at h
    rw [hcv] at h
    exact h
  have hw₀Q : c⁻¹ * w * c ∉ burnsideJ410_QOf z := by
    intro h
    apply hwQ
    have h1 : c⁻¹ * w * c ∈ CFSG.conjugate (burnsideJ410_QOf v) c := by rw [hQ]; exact h
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at h1
    have e : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
    rw [e] at h1
    exact h1
  have hY : ∀ {Y : Subgroup G}, (Y ≤ Subgroup.centralizer ({v} : Set G) ∧ Nat.card Y = 5 ∧
      w ∈ Subgroup.normalizer ((Y ⊔ burnsideJ410_QOf v : Subgroup G) : Set G)) →
      (CFSG.conjugate Y c ≤ Subgroup.centralizer ({z} : Set G) ∧ Nat.card (CFSG.conjugate Y c) = 5 ∧
        c⁻¹ * w * c ∈ Subgroup.normalizer
          ((CFSG.conjugate Y c ⊔ burnsideJ410_QOf z : Subgroup G) : Set G)) := by
    intro Y h
    refine ⟨?_, ?_, ?_⟩
    · rw [← hCz]; exact CFSG.ASVolI.RuChoice.fx_conjugate_mono c h.1
    · rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact h.2.1
    · have h1 : c⁻¹ * w * c ∈ CFSG.conjugate
          (Subgroup.normalizer ((Y ⊔ burnsideJ410_QOf v : Subgroup G) : Set G)) c := by
        rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
        have e : c * (c⁻¹ * w * c) * c⁻¹ = w := by group
        rw [e]
        exact h.2.2
      rw [← CFSG.ASVolI.RuChoice.fx_normalizer_conjugate, CFSG.ASVolI.RuChoice.fx_conjugate_sup,
        hQ] at h1
      exact h1
  have unc : ∀ {A B : Subgroup G}, CFSG.conjugate A c ⊔ burnsideJ410_QOf z =
      CFSG.conjugate B c ⊔ burnsideJ410_QOf z → A ⊔ burnsideJ410_QOf v = B ⊔ burnsideJ410_QOf v := by
    intro A B h
    apply burnsideJ410_conj_inj c
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_sup, CFSG.ASVolI.RuChoice.fx_conjugate_sup, hQ]
    exact h
  rcases hF.S5 (c⁻¹ * w * c) hw₀2 hzw₀ hw₀Q _ _ _ (hY h₁) (hY h₂) (hY h₃) with h | h | h
  · exact Or.inl (unc h)
  · exact Or.inr (Or.inl (unc h))
  · exact Or.inr (Or.inr (unc h))

theorem burnsideJ410_not_mem_QOf {v w : G} {X : Subgroup G} (hX : Nat.card X = 5)
    (hXv : X ≤ Subgroup.centralizer ({v} : Set G)) (hw : burnsideJ410_Inv w X) :
    w ∉ burnsideJ410_QOf v := by
  intro hwQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hx1⟩ := burnsideJ410_exists_ne_one hX
  have h1 : x * w * x⁻¹ ∈ burnsideJ410_QOf v := burnsideJ410_QOf_conj_mem (hXv hx) hwQ
  have h2 : (x * w * x⁻¹) * w⁻¹ ∈ burnsideJ410_QOf v := mul_mem h1 (inv_mem hwQ)
  have hxx : (x * w * x⁻¹) * w⁻¹ = x * x := by
    have hwx : w * x * w⁻¹ = x⁻¹ := hw x hx
    calc (x * w * x⁻¹) * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
      _ = x * (w * x * w⁻¹)⁻¹ := by group
      _ = x * x := by rw [hwx, inv_inv]
  rw [hxx] at h2
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (Subgroup.centralizer ({v} : Set G))) ⟨x * x, h2⟩
  have h2k : (x * x) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hx5 := burnsideJ410_pow_five hX hx
  have h5 : (x * x) ^ 5 = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hx5, one_pow]
  have := (pow_gcd_eq_one (a := x * x)).mpr ⟨h5, h2k⟩
  rw [show Nat.gcd 5 (2 ^ k) = 1 from Nat.Coprime.pow_right k (by norm_num), pow_one] at this
  exact hx1 (burnsideJ410_eq_one_of_sq hx5 this)

theorem burnsideJ410_Ev_le_two {z u : G} {F1 B5 : Subgroup G} (hL : burnsideJ410_Loc z u)
    (hF : burnsideJ410_Fix z u F1 B5) {v : G} (hv : v ∈ burnsideJ410_Einv z u)
    {X : Subgroup G} (hX : X ∈ EInv5Ru z u) (hXv : burnsideJ410_Cent v X) {A B C : Subgroup G}
    (hA : A ∈ EvRu F1 z u v) (hB : B ∈ EvRu F1 z u v) (hC : C ∈ EvRu F1 z u v) :
    A = B ∨ A = C ∨ B = C := by
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ burnsideJ410_Einv z u, w ≠ v := by
    by_cases h : v = z
    · exact ⟨u, burnsideJ410_u_mem z u, by rw [h]; exact hL.u_ne⟩
    · exact ⟨z, burnsideJ410_z_mem z u, fun hh => h hh.symm⟩
  have hwX := burnsideJ410_inv_of_ne hL hX hv hXv hw hwv
  have hwQ := burnsideJ410_not_mem_QOf hX.1 (burnsideJ410_le_centralizer_of_cent hXv) hwX
  have hvc := burnsideJ410_Einv_conj hL hv
  have hwE : w ∈ burnsideJ410_E z u := burnsideJ410_Einv_mem_E hL hw
  obtain ⟨⟨kA, hkA, rfl⟩, hEA⟩ := hA
  obtain ⟨⟨kB, hkB, rfl⟩, hEB⟩ := hB
  obtain ⟨⟨kC, hkC, rfl⟩, hEC⟩ := hC
  have hpack : ∀ {k : G}, k⁻¹ * z * k = v → burnsideJ410_E z u ≤ CFSG.conjugate F1 k →
      (CFSG.conjugate B5 k ≤ Subgroup.centralizer ({v} : Set G) ∧
        Nat.card (CFSG.conjugate B5 k) = 5 ∧
        w ∈ Subgroup.normalizer ((CFSG.conjugate B5 k ⊔ burnsideJ410_QOf v : Subgroup G) :
          Set G)) := by
    intro k hk hE
    refine ⟨?_, ?_, ?_⟩
    · exact (CFSG.ASVolI.RuChoice.fx_conjugate_mono k hF.B5_le).trans
        (burnsideJ410_Fset_le_centralizer hF ⟨k, hk, rfl⟩)
    · rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF.B5_card
    · exact burnsideJ410_Fset_le_normalizer hF hk (hE hwE)
  have cp : ∀ k : G, Nat.card (CFSG.conjugate B5 k) = 5 := fun k => by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF.B5_card
  have le_ : ∀ k : G, CFSG.conjugate B5 k ≤ CFSG.conjugate F1 k := fun k =>
    CFSG.ASVolI.RuChoice.fx_conjugate_mono k hF.B5_le
  have key := burnsideJ410_S5_v hF hvc (burnsideJ410_Einv_sq hL hw)
    (burnsideJ410_Einv_comm hL hv hw) hwQ (hpack hkA hEA) (hpack hkB hEB) (hpack hkC hEC)
  rcases key with h | h | h
  · exact Or.inl ((burnsideJ410_Fset_eq_iff hF ⟨kA, hkA, rfl⟩ ⟨kB, hkB, rfl⟩ (le_ kA) (le_ kB)
      (cp kA) (cp kB)).mpr h)
  · exact Or.inr (Or.inl ((burnsideJ410_Fset_eq_iff hF ⟨kA, hkA, rfl⟩ ⟨kC, hkC, rfl⟩ (le_ kA)
      (le_ kC) (cp kA) (cp kC)).mpr h))
  · exact Or.inr (Or.inr ((burnsideJ410_Fset_eq_iff hF ⟨kB, hkB, rfl⟩ ⟨kC, hkC, rfl⟩ (le_ kB)
      (le_ kC) (cp kB) (cp kC)).mpr h))

theorem burnsideJ410_conj_Fset {z v g : G} {F1 E' : Subgroup G} (h : E' ∈ FsetRu F1 z v) :
    CFSG.conjugate E' g ∈ FsetRu F1 z (g⁻¹ * v * g) := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨k * g, ?_, ?_⟩
  · calc (k * g)⁻¹ * z * (k * g) = g⁻¹ * (k⁻¹ * z * k) * g := by group
      _ = g⁻¹ * v * g := by rw [hk]
  · exact CFSG.ASVolI.RuChoice.fx_conjugate_conjugate F1 k g

theorem burnsideJ410_conj_Ev {z u v g : G} {F1 E' : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) (h : E' ∈ EvRu F1 z u v) :
    CFSG.conjugate E' g ∈ EvRu F1 z u (g⁻¹ * v * g) := by
  refine ⟨burnsideJ410_conj_Fset h.1, fun e he => ?_⟩
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
  exact h.2 ((Subgroup.mem_normalizer_iff.mp hg e).mp he)

end BurnsideJ410D

section BurnsideJ410E

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]

@[expose] def burnsideJ410_lab (z u : G) (i : ℤ) : G :=
  if i % 3 = 0 then z else if i % 3 = 1 then u else u * z

theorem burnsideJ410_lab_mem (z u : G) (i : ℤ) :
    burnsideJ410_lab z u i ∈ burnsideJ410_Einv z u := by
  unfold burnsideJ410_lab
  split_ifs
  · exact burnsideJ410_z_mem z u
  · exact burnsideJ410_u_mem z u
  · exact burnsideJ410_uz_mem z u

theorem burnsideJ410_lab_add_three (z u : G) (i : ℤ) :
    burnsideJ410_lab z u (i + 3) = burnsideJ410_lab z u i := by
  unfold burnsideJ410_lab
  have : (i + 3) % 3 = i % 3 := by omega
  rw [this]

theorem burnsideJ410_lab_cases (z u : G) (i : ℤ) :
    (burnsideJ410_lab z u i = z ∧ burnsideJ410_lab z u (i + 1) = u ∧
        burnsideJ410_lab z u (i + 2) = u * z) ∨
      (burnsideJ410_lab z u i = u ∧ burnsideJ410_lab z u (i + 1) = u * z ∧
        burnsideJ410_lab z u (i + 2) = z) ∨
      (burnsideJ410_lab z u i = u * z ∧ burnsideJ410_lab z u (i + 1) = z ∧
        burnsideJ410_lab z u (i + 2) = u) := by
  unfold burnsideJ410_lab
  have h : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases h with h | h | h
  · left
    have h1 : (i + 1) % 3 = 1 := by omega
    have h2 : (i + 2) % 3 = 2 := by omega
    simp [h, h1, h2]
  · right; left
    have h1 : (i + 1) % 3 = 2 := by omega
    have h2 : (i + 2) % 3 = 0 := by omega
    simp [h, h1, h2]
  · right; right
    have h1 : (i + 1) % 3 = 0 := by omega
    have h2 : (i + 2) % 3 = 1 := by omega
    simp [h, h1, h2]

theorem burnsideJ410_lab_distinct {z u : G} (hL : burnsideJ410_Loc z u) (i : ℤ) :
    burnsideJ410_lab z u i ≠ burnsideJ410_lab z u (i + 1) ∧
      burnsideJ410_lab z u i ≠ burnsideJ410_lab z u (i + 2) ∧
      burnsideJ410_lab z u (i + 1) ≠ burnsideJ410_lab z u (i + 2) := by
  have h1 := hL.u_ne
  have h1' := burnsideJ410_z_ne_u hL
  have h2 := burnsideJ410_z_ne_uz hL
  have h2' := burnsideJ410_uz_ne_z hL
  have h3 := burnsideJ410_u_ne_uz hL
  have h3' := burnsideJ410_uz_ne_u hL
  rcases burnsideJ410_lab_cases z u i with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
    rw [a, b, c] <;> exact ⟨by assumption, by assumption, by assumption⟩

theorem burnsideJ410_lab_inj {z u : G} (hL : burnsideJ410_Loc z u) {i j : ℤ}
    (h : burnsideJ410_lab z u i = burnsideJ410_lab z u j) : i % 3 = j % 3 := by
  have h1 := hL.u_ne
  have h1' := burnsideJ410_z_ne_u hL
  have h2 := burnsideJ410_z_ne_uz hL
  have h2' := burnsideJ410_uz_ne_z hL
  have h3 := burnsideJ410_u_ne_uz hL
  have h3' := burnsideJ410_uz_ne_u hL
  unfold burnsideJ410_lab at h
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
    first | omega | (exfalso; simp [hi, hj] at h <;> simp_all)

theorem burnsideJ410_lab_zero (z u : G) : burnsideJ410_lab z u 0 = z := by
  simp [burnsideJ410_lab]

theorem burnsideJ410_lab_one (z u : G) : burnsideJ410_lab z u 1 = u := by
  simp [burnsideJ410_lab]

theorem burnsideJ410_lab_neg_one (z u : G) : burnsideJ410_lab z u (-1) = u * z := by
  simp [burnsideJ410_lab]

@[expose] noncomputable def burnsideJ410_fw (z u : G) (B5 : Subgroup G) : ℕ → Subgroup G
  | 0 => B5
  | n + 1 => O5N (burnsideJ410_fw z u B5 n) ⊓
      Subgroup.centralizer ({burnsideJ410_lab z u ((n + 1 : ℕ) : ℤ)} : Set G)

@[expose] noncomputable def burnsideJ410_bw (z u : G) (B5 : Subgroup G) : ℕ → Subgroup G
  | 0 => B5
  | n + 1 => O5N (burnsideJ410_bw z u B5 n) ⊓
      Subgroup.centralizer ({burnsideJ410_lab z u (-((n + 1 : ℕ) : ℤ))} : Set G)

@[expose] noncomputable def burnsideJ410_W (z u : G) (B5 : Subgroup G) (i : ℤ) : Subgroup G :=
  if 0 ≤ i then burnsideJ410_fw z u B5 i.toNat else burnsideJ410_bw z u B5 (-i).toNat

theorem burnsideJ410_W_nat (z u : G) (B5 : Subgroup G) (n : ℕ) :
    burnsideJ410_W z u B5 (n : ℤ) = burnsideJ410_fw z u B5 n := by
  simp [burnsideJ410_W]

theorem burnsideJ410_W_neg (z u : G) (B5 : Subgroup G) (n : ℕ) :
    burnsideJ410_W z u B5 (-(n : ℤ)) = burnsideJ410_bw z u B5 n := by
  rcases n with _ | n
  · simp [burnsideJ410_W, burnsideJ410_fw, burnsideJ410_bw]
  · have h : ¬ (0 ≤ -((n + 1 : ℕ) : ℤ)) := by omega
    rw [burnsideJ410_W, if_neg h, neg_neg, Int.toNat_natCast]

section Walk

variable [Finite G] {z u : G}

theorem burnsideJ410_nb_symm (hL : burnsideJ410_Loc z u) {Y : Subgroup G} (hY : Y ∈ EInv5Ru z u)
    {v w : G} (hv : v ∈ burnsideJ410_Einv z u) (hvY : burnsideJ410_Cent v Y)
    (hw : w ∈ burnsideJ410_Einv z u) (hwv : w ≠ v) :
    Y = O5N (O5N Y ⊓ Subgroup.centralizer ({w} : Set G)) ⊓ Subgroup.centralizer ({v} : Set G) := by
  obtain ⟨hnb, hnbC, hne, hcomm⟩ := burnsideJ410_nb hL hY hv hvY hw hwv
  have hc' : ⁅O5N Y ⊓ Subgroup.centralizer ({w} : Set G), Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hcomm
  exact (burnsideJ410_nbr_eq hL hnb hY hne hc' hw hnbC hv hvY).2

theorem burnsideJ410_fw_spec (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (n : ℕ) :
    burnsideJ410_fw z u B5 n ∈ EInv5Ru z u ∧
      burnsideJ410_Cent (burnsideJ410_lab z u n) (burnsideJ410_fw z u B5 n) := by
  induction n with
  | zero =>
    refine ⟨hB, ?_⟩
    simp only [burnsideJ410_fw, Nat.cast_zero, burnsideJ410_lab_zero]
    exact hz
  | succ n ih =>
    obtain ⟨hn, hcn⟩ := ih
    have hne := (burnsideJ410_lab_distinct hL (n : ℤ)).1
    obtain ⟨h1, h2, -, -⟩ := burnsideJ410_nb hL hn (burnsideJ410_lab_mem z u n) hcn
      (burnsideJ410_lab_mem z u ((n + 1 : ℕ) : ℤ)) (by push_cast; exact hne.symm)
    exact ⟨h1, h2⟩

theorem burnsideJ410_bw_spec (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (n : ℕ) :
    burnsideJ410_bw z u B5 n ∈ EInv5Ru z u ∧
      burnsideJ410_Cent (burnsideJ410_lab z u (-(n : ℤ))) (burnsideJ410_bw z u B5 n) := by
  induction n with
  | zero =>
    refine ⟨hB, ?_⟩
    simp only [burnsideJ410_bw, Nat.cast_zero, neg_zero, burnsideJ410_lab_zero]
    exact hz
  | succ n ih =>
    obtain ⟨hn, hcn⟩ := ih
    have hne := (burnsideJ410_lab_distinct hL (-((n + 1 : ℕ) : ℤ))).1
    have e : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
    rw [e] at hne
    obtain ⟨h1, h2, -, -⟩ := burnsideJ410_nb hL hn (burnsideJ410_lab_mem z u (-(n : ℤ))) hcn
      (burnsideJ410_lab_mem z u (-((n + 1 : ℕ) : ℤ))) hne
    exact ⟨h1, h2⟩

theorem burnsideJ410_W_spec (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (i : ℤ) :
    burnsideJ410_W z u B5 i ∈ EInv5Ru z u ∧
      burnsideJ410_Cent (burnsideJ410_lab z u i) (burnsideJ410_W z u B5 i) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [burnsideJ410_W_nat]; exact burnsideJ410_fw_spec hL hB hz n
  · rw [burnsideJ410_W_neg]; exact burnsideJ410_bw_spec hL hB hz n

theorem burnsideJ410_W_succ_nb (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (i : ℤ) :
    burnsideJ410_W z u B5 (i + 1) = O5N (burnsideJ410_W z u B5 i) ⊓
        Subgroup.centralizer ({burnsideJ410_lab z u (i + 1)} : Set G) ∧
      burnsideJ410_W z u B5 i = O5N (burnsideJ410_W z u B5 (i + 1)) ⊓
        Subgroup.centralizer ({burnsideJ410_lab z u i} : Set G) := by
  have hne := (burnsideJ410_lab_distinct hL i).1
  have hspec := burnsideJ410_W_spec hL hB hz i
  have hsymm : burnsideJ410_W z u B5 (i + 1) = O5N (burnsideJ410_W z u B5 i) ⊓
        Subgroup.centralizer ({burnsideJ410_lab z u (i + 1)} : Set G) →
      burnsideJ410_W z u B5 i = O5N (burnsideJ410_W z u B5 (i + 1)) ⊓
        Subgroup.centralizer ({burnsideJ410_lab z u i} : Set G) := by
    intro h
    rw [h]
    exact burnsideJ410_nb_symm hL hspec.1 (burnsideJ410_lab_mem z u i) hspec.2
      (burnsideJ410_lab_mem z u (i + 1)) hne.symm
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · have h1 : burnsideJ410_W z u B5 ((n : ℤ) + 1) = O5N (burnsideJ410_W z u B5 n) ⊓
        Subgroup.centralizer ({burnsideJ410_lab z u ((n : ℤ) + 1)} : Set G) := by
      have : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [this, burnsideJ410_W_nat, burnsideJ410_W_nat]
      rfl
    exact ⟨h1, hsymm h1⟩
  · rcases n with _ | n
    · have h1 : burnsideJ410_W z u B5 (-((0 : ℕ) : ℤ) + 1) = O5N (burnsideJ410_W z u B5 (-((0 : ℕ) : ℤ))) ⊓
          Subgroup.centralizer ({burnsideJ410_lab z u (-((0 : ℕ) : ℤ) + 1)} : Set G) := by
        simp only [Nat.cast_zero, neg_zero, zero_add]
        have := burnsideJ410_W_nat z u B5 1
        simp only [Nat.cast_one] at this
        rw [this]
        rfl
      exact ⟨h1, hsymm h1⟩
    · have e : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      have h2 : burnsideJ410_W z u B5 (-((n + 1 : ℕ) : ℤ)) =
          O5N (burnsideJ410_W z u B5 (-((n + 1 : ℕ) : ℤ) + 1)) ⊓
            Subgroup.centralizer ({burnsideJ410_lab z u (-((n + 1 : ℕ) : ℤ))} : Set G) := by
        rw [e, burnsideJ410_W_neg, burnsideJ410_W_neg]
        rfl
      refine ⟨?_, h2⟩
      have hspec' := burnsideJ410_W_spec hL hB hz (-((n + 1 : ℕ) : ℤ) + 1)
      have hne' := (burnsideJ410_lab_distinct hL (-((n + 1 : ℕ) : ℤ))).1
      have := burnsideJ410_nb_symm hL hspec'.1 (burnsideJ410_lab_mem z u _) hspec'.2
        (burnsideJ410_lab_mem z u (-((n + 1 : ℕ) : ℤ))) hne'
      rw [← h2] at this
      exact this

end Walk

section Walk2

variable [Finite G] {z u : G}

theorem burnsideJ410_W_comm (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (i : ℤ) :
    ⁅burnsideJ410_W z u B5 i, burnsideJ410_W z u B5 (i + 1)⁆ = ⊥ := by
  have hspec := burnsideJ410_W_spec hL hB hz i
  obtain ⟨-, -, -, hc⟩ := burnsideJ410_nb hL hspec.1 (burnsideJ410_lab_mem z u i) hspec.2
    (burnsideJ410_lab_mem z u (i + 1)) (burnsideJ410_lab_distinct hL i).1.symm
  rw [(burnsideJ410_W_succ_nb hL hB hz i).1]
  exact hc

theorem burnsideJ410_W_label_ne (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) {i j : ℤ}
    (h : burnsideJ410_lab z u i ≠ burnsideJ410_lab z u j) :
    burnsideJ410_W z u B5 i ≠ burnsideJ410_W z u B5 j := by
  intro heq
  apply h
  refine burnsideJ410_label_unique hL (burnsideJ410_W_spec hL hB hz i).1
    (burnsideJ410_lab_mem z u i) (burnsideJ410_lab_mem z u j)
    (burnsideJ410_W_spec hL hB hz i).2 ?_
  rw [heq]
  exact (burnsideJ410_W_spec hL hB hz j).2

theorem burnsideJ410_W_two_reg (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (i : ℤ) {Y : Subgroup G}
    (hY : Y ∈ EInv5Ru z u) (hne : Y ≠ burnsideJ410_W z u B5 i)
    (hc : ⁅burnsideJ410_W z u B5 i, Y⁆ = ⊥) :
    Y = burnsideJ410_W z u B5 (i - 1) ∨ Y = burnsideJ410_W z u B5 (i + 1) := by
  have hspec := burnsideJ410_W_spec hL hB hz i
  obtain ⟨w, hw, hwC, -⟩ := burnsideJ410_label_exists hL hY
  obtain ⟨hwv, hYeq⟩ := burnsideJ410_nbr_eq hL hspec.1 hY hne.symm hc
    (burnsideJ410_lab_mem z u i) hspec.2 hw hwC
  have d1 := burnsideJ410_lab_distinct hL i
  have d0 := burnsideJ410_lab_distinct hL (i - 1)
  have e1 : i - 1 + 1 = i := by ring
  have e2 : i - 1 + 2 = i + 1 := by ring
  rw [e1, e2] at d0
  rcases burnsideJ410_Einv_trichotomy hL (burnsideJ410_lab_mem z u i)
    (burnsideJ410_lab_mem z u (i + 1)) (burnsideJ410_lab_mem z u (i - 1)) hw d1.1
    d0.1.symm d0.2.1.symm with h | h | h
  · exact absurd h hwv
  · right
    rw [hYeq, h, (burnsideJ410_W_succ_nb hL hB hz i).1]
  · left
    have := (burnsideJ410_W_succ_nb hL hB hz (i - 1)).2
    rw [e1] at this
    rw [hYeq, h, this]

theorem burnsideJ410_W_rev_up (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) {j m : ℤ}
    (h0 : CFSG.conjugate (burnsideJ410_W z u B5 j) g = burnsideJ410_W z u B5 m)
    (h1 : CFSG.conjugate (burnsideJ410_W z u B5 (j + 1)) g = burnsideJ410_W z u B5 (m - 1)) :
    CFSG.conjugate (burnsideJ410_W z u B5 (j + 2)) g = burnsideJ410_W z u B5 (m - 2) := by
  have hY := burnsideJ410_conj_mem_EInv5 hg (burnsideJ410_W_spec hL hB hz (j + 2)).1
  have hc : ⁅burnsideJ410_W z u B5 (m - 1), CFSG.conjugate (burnsideJ410_W z u B5 (j + 2)) g⁆
      = ⊥ := by
    rw [← h1, burnsideJ410_conj_comm_bot]
    have := burnsideJ410_W_comm hL hB hz (j + 1)
    rwa [show j + 1 + 1 = j + 2 by ring] at this
  have hd := burnsideJ410_lab_distinct hL j
  have hne : CFSG.conjugate (burnsideJ410_W z u B5 (j + 2)) g ≠ burnsideJ410_W z u B5 (m - 1) := by
    intro h
    rw [← h1] at h
    exact burnsideJ410_W_label_ne hL hB hz (i := j + 2) (j := j + 1) (Ne.symm hd.2.2)
      (burnsideJ410_conj_inj g h)
  rcases burnsideJ410_W_two_reg hL hB hz (m - 1) hY hne hc with h | h
  · rw [h]; congr 1; ring
  · exfalso
    have e : m - 1 + 1 = m := by ring
    rw [e, ← h0] at h
    exact burnsideJ410_W_label_ne hL hB hz (i := j + 2) (j := j) (Ne.symm hd.2.1)
      (burnsideJ410_conj_inj g h)

theorem burnsideJ410_W_rev_down (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) {j m : ℤ}
    (h0 : CFSG.conjugate (burnsideJ410_W z u B5 j) g = burnsideJ410_W z u B5 m)
    (h1 : CFSG.conjugate (burnsideJ410_W z u B5 (j + 1)) g = burnsideJ410_W z u B5 (m - 1)) :
    CFSG.conjugate (burnsideJ410_W z u B5 (j - 1)) g = burnsideJ410_W z u B5 (m + 1) := by
  have hY := burnsideJ410_conj_mem_EInv5 hg (burnsideJ410_W_spec hL hB hz (j - 1)).1
  have hc : ⁅burnsideJ410_W z u B5 m, CFSG.conjugate (burnsideJ410_W z u B5 (j - 1)) g⁆ = ⊥ := by
    rw [← h0, burnsideJ410_conj_comm_bot, Subgroup.commutator_comm]
    have := burnsideJ410_W_comm hL hB hz (j - 1)
    rwa [show j - 1 + 1 = j by ring] at this
  have hd := burnsideJ410_lab_distinct hL (j - 1)
  rw [show j - 1 + 1 = j by ring, show j - 1 + 2 = j + 1 by ring] at hd
  have hne : CFSG.conjugate (burnsideJ410_W z u B5 (j - 1)) g ≠ burnsideJ410_W z u B5 m := by
    intro h
    rw [← h0] at h
    exact burnsideJ410_W_label_ne hL hB hz (i := j - 1) (j := j) hd.1
      (burnsideJ410_conj_inj g h)
  rcases burnsideJ410_W_two_reg hL hB hz m hY hne hc with h | h
  · exfalso
    exact burnsideJ410_W_label_ne hL hB hz (i := j - 1) (j := j + 1) hd.2.1
      (burnsideJ410_conj_inj g (h.trans h1.symm))
  · exact h

theorem burnsideJ410_W_rev (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) {a b : ℤ}
    (h0 : CFSG.conjugate (burnsideJ410_W z u B5 a) g = burnsideJ410_W z u B5 b)
    (h1 : CFSG.conjugate (burnsideJ410_W z u B5 (a + 1)) g = burnsideJ410_W z u B5 (b - 1)) :
    ∀ k : ℤ, CFSG.conjugate (burnsideJ410_W z u B5 (a + k)) g = burnsideJ410_W z u B5 (b - k) := by
  have key : ∀ k : ℤ, CFSG.conjugate (burnsideJ410_W z u B5 (a + k)) g =
        burnsideJ410_W z u B5 (b - k) ∧
      CFSG.conjugate (burnsideJ410_W z u B5 (a + k + 1)) g = burnsideJ410_W z u B5 (b - k - 1) := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using ⟨h0, h1⟩
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e1 : a + ((k : ℤ) + 1) = a + k + 1 := by ring
      have e2 : b - ((k : ℤ) + 1) = b - k - 1 := by ring
      refine ⟨by rw [e1, e2]; exact ih2, ?_⟩
      have := burnsideJ410_W_rev_up hL hB hz hg ih1 ih2
      rw [show a + ((k : ℤ) + 1) + 1 = a + k + 2 by ring,
        show b - ((k : ℤ) + 1) - 1 = b - k - 1 - 1 by ring]
      rw [show b - k - 1 - 1 = b - k - 2 by ring]
      exact this
    | pred k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have := burnsideJ410_W_rev_down hL hB hz hg ih1 ih2
      refine ⟨?_, ?_⟩
      · rw [show a + (-(k : ℤ) - 1) = a + -(k : ℤ) - 1 by ring,
          show b - (-(k : ℤ) - 1) = b - -(k : ℤ) + 1 by ring]
        exact this
      · rw [show a + (-(k : ℤ) - 1) + 1 = a + -(k : ℤ) by ring,
          show b - (-(k : ℤ) - 1) - 1 = b - -(k : ℤ) by ring]
        exact ih1
  exact fun k => (key k).1

theorem burnsideJ410_W_swap (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) (j : ℤ) :
    ∃ s ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G), ∀ k : ℤ,
      CFSG.conjugate (burnsideJ410_W z u B5 (j + k)) s = burnsideJ410_W z u B5 (j + 1 - k) := by
  have d0 := burnsideJ410_lab_distinct hL (j - 1)
  have d1 := burnsideJ410_lab_distinct hL j
  have e1 : j - 1 + 1 = j := by ring
  have e2 : j - 1 + 2 = j + 1 := by ring
  rw [e1, e2] at d0
  have e3 : burnsideJ410_lab z u (j + 2) = burnsideJ410_lab z u (j - 1) := by
    have := burnsideJ410_lab_add_three z u (j - 1)
    rwa [show j - 1 + 3 = j + 2 by ring] at this
  have sp0 := burnsideJ410_W_spec hL hB hz (j - 1)
  have sp1 := burnsideJ410_W_spec hL hB hz j
  have sp2 := burnsideJ410_W_spec hL hB hz (j + 1)
  have sp3 := burnsideJ410_W_spec hL hB hz (j + 2)
  rw [e3] at sp3
  have c01 := burnsideJ410_W_comm hL hB hz (j - 1)
  rw [e1] at c01
  have c12 := burnsideJ410_W_comm hL hB hz j
  have c23 := burnsideJ410_W_comm hL hB hz (j + 1)
  rw [show j + 1 + 1 = j + 2 by ring] at c23
  obtain ⟨s, hs, hs1, hs2⟩ := burnsideJ410_edge_swap hL sp0.1 sp1.1 sp2.1 sp3.1
    (burnsideJ410_lab_mem z u (j - 1)) (burnsideJ410_lab_mem z u j)
    (burnsideJ410_lab_mem z u (j + 1)) d0.1 d0.2.1 d1.1 sp0.2 sp1.2 sp2.2 sp3.2 c01 c12 c23
  refine ⟨s, hs, ?_⟩
  have := burnsideJ410_W_rev hL hB hz hs (a := j) (b := j + 1) hs1 (by
    rw [show j + 1 - 1 = j by ring]; exact hs2)
  exact this

end Walk2

end BurnsideJ410E

section BurnsideJ410F

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G] {z u : G} {F1 B5 : Subgroup G}

theorem burnsideJ410_Fix_B5_cent (hF : burnsideJ410_Fix z u F1 B5) : burnsideJ410_Cent z B5 := by
  refine burnsideJ410_cent_iff_comm.mpr fun y hy => ?_
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hF.F1_le (hF.B5_le hy))).symm

theorem burnsideJ410_Fix_B5_mem (hF : burnsideJ410_Fix z u F1 B5) : B5 ∈ EInv5Ru z u :=
  ⟨hF.B5_card, burnsideJ410_E_le_normalizer_iff.mpr
    ⟨burnsideJ410_mem_normalizer_of_cent_or_inv (Or.inl (burnsideJ410_Fix_B5_cent hF)),
      burnsideJ410_mem_normalizer_of_cent_or_inv (Or.inr hF.B5_inv)⟩⟩

theorem burnsideJ410_Fset_unique_type (hL : burnsideJ410_Loc z u)
    (hF : burnsideJ410_Fix z u F1 B5) {v v' : G} {E' : Subgroup G} (h : E' ∈ FsetRu F1 z v)
    (h' : E' ∈ FsetRu F1 z v') : v = v' := by
  obtain ⟨k, hk, hE⟩ := h
  obtain ⟨k', hk', hE'⟩ := h'
  have heq : CFSG.conjugate F1 k = CFSG.conjugate F1 k' := hE.symm.trans hE'
  have hm : k' * k⁻¹ ∈ Subgroup.normalizer (F1 : Set G) := by
    refine CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => ?_
    have h1 : k⁻¹ * x * k ∈ CFSG.conjugate F1 k := by
      rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
      have : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rw [this]; exact hx
    rw [heq, CFSG.ASVolI.RuChoice.fx_mem_conjugate] at h1
    have e : k' * (k⁻¹ * x * k) * k'⁻¹ = (k' * k⁻¹) * x * (k' * k⁻¹)⁻¹ := by group
    rw [e] at h1
    exact h1
  have hc : ∀ f ∈ F1, f * ((k' * k⁻¹)⁻¹ * z * (k' * k⁻¹)) =
      ((k' * k⁻¹)⁻¹ * z * (k' * k⁻¹)) * f := by
    intro f hf
    have hmf : (k' * k⁻¹) * f * (k' * k⁻¹)⁻¹ ∈ F1 :=
      (Subgroup.mem_normalizer_iff.mp hm f).mp hf
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hF.F1_le hmf)
    calc f * ((k' * k⁻¹)⁻¹ * z * (k' * k⁻¹))
        = (k' * k⁻¹)⁻¹ * (((k' * k⁻¹) * f * (k' * k⁻¹)⁻¹) * z) * (k' * k⁻¹) := by group
      _ = (k' * k⁻¹)⁻¹ * (z * ((k' * k⁻¹) * f * (k' * k⁻¹)⁻¹)) * (k' * k⁻¹) := by rw [hcomm]
      _ = ((k' * k⁻¹)⁻¹ * z * (k' * k⁻¹)) * f := by group
  have hzF : z ∈ F1 := hF.E_le (burnsideJ410_Einv_mem_E hL (burnsideJ410_z_mem z u))
  have hmz : (k' * k⁻¹)⁻¹ * z * (k' * k⁻¹) ∈ F1 := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) z).mp hzF
    rwa [inv_inv] at this
  have hz := burnsideJ410_zpowers_sq hL.z_sq (hF.Z_le _ hmz hc)
  have hzz : (k' * k⁻¹)⁻¹ * z * (k' * k⁻¹) = z := by
    rcases hz with h1 | h1
    · exfalso
      apply hL.z_ne
      calc z = (k' * k⁻¹) * ((k' * k⁻¹)⁻¹ * z * (k' * k⁻¹)) * (k' * k⁻¹)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  calc v = k⁻¹ * z * k := hk.symm
    _ = k⁻¹ * ((k' * k⁻¹)⁻¹ * z * (k' * k⁻¹)) * k := by rw [hzz]
    _ = k'⁻¹ * z * k' := by group
    _ = v' := hk'

section Theta

variable {θ : ℤ → Subgroup G}

theorem burnsideJ410_W_zero (z u : G) (B5 : Subgroup G) : burnsideJ410_W z u B5 0 = B5 := by
  have := burnsideJ410_W_nat z u B5 0
  simpa [burnsideJ410_fw] using this

theorem burnsideJ410_theta_conj (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {s : G}
    (hs : s ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) {i i' : ℤ}
    (h : CFSG.conjugate (burnsideJ410_W z u B5 i) s = burnsideJ410_W z u B5 i') :
    CFSG.conjugate (θ i) s = θ i' := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  have hWi := burnsideJ410_W_spec hL hB hz i
  have hWi' := burnsideJ410_W_spec hL hB hz i'
  have hlab : s⁻¹ * burnsideJ410_lab z u i * s = burnsideJ410_lab z u i' := by
    refine burnsideJ410_label_unique hL hWi'.1
      (burnsideJ410_conj_Einv hL hs (burnsideJ410_lab_mem z u i))
      (burnsideJ410_lab_mem z u i') ?_ hWi'.2
    have := burnsideJ410_conj_cent s hWi.2
    rwa [h] at this
  have h1 : CFSG.conjugate (θ i) s ∈ FsetRu F1 z (burnsideJ410_lab z u i') := by
    have := burnsideJ410_conj_Fset (g := s) (hθ i).1
    rwa [hlab] at this
  have h2 : burnsideJ410_W z u B5 i' ≤ CFSG.conjugate (θ i) s := by
    rw [← h]; exact CFSG.ASVolI.RuChoice.fx_conjugate_mono s (hθ i).2
  exact (burnsideJ410_Fset_eq_iff hF h1 (hθ i').1 h2 (hθ i').2 hWi'.1.1 hWi'.1.1).mpr rfl

theorem burnsideJ410_theta_E_le (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) : burnsideJ410_E z u ≤ θ i := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  have h0 : θ 0 = F1 := by
    have hF1 : F1 ∈ FsetRu F1 z z :=
      ⟨1, by simp, (CFSG.ASVolI.RuChoice.fx_conjugate_one F1).symm⟩
    have hθ0 : θ 0 ∈ FsetRu F1 z z := by
      have := (hθ 0).1
      rwa [burnsideJ410_lab_zero] at this
    have hle : burnsideJ410_W z u B5 0 ≤ θ 0 := (hθ 0).2
    rw [burnsideJ410_W_zero] at hle
    exact (burnsideJ410_Fset_eq_iff hF hθ0 hF1 hle hF.B5_le hF.B5_card hF.B5_card).mpr rfl
  have hstep : ∀ j i : ℤ, burnsideJ410_E z u ≤ θ i → burnsideJ410_E z u ≤ θ (2 * j + 1 - i) := by
    intro j i hi
    obtain ⟨s, hs, hsk⟩ := burnsideJ410_W_swap hL hB hz j
    have h := hsk (i - j)
    rw [show j + (i - j) = i by ring, show j + 1 - (i - j) = 2 * j + 1 - i by ring] at h
    have hc := burnsideJ410_theta_conj hL hF hθ hs h
    rw [← hc]
    intro e he
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
    exact hi ((Subgroup.mem_normalizer_iff.mp hs e).mp he)
  have up2 : ∀ i : ℤ, burnsideJ410_E z u ≤ θ i → burnsideJ410_E z u ≤ θ (i + 2) := by
    intro i hi
    have h1 := hstep (-1) i hi
    have h2 := hstep 0 _ h1
    rwa [show 2 * (0 : ℤ) + 1 - (2 * (-1) + 1 - i) = i + 2 by ring] at h2
  have down2 : ∀ i : ℤ, burnsideJ410_E z u ≤ θ i → burnsideJ410_E z u ≤ θ (i - 2) := by
    intro i hi
    have h1 := hstep 0 i hi
    have h2 := hstep (-1) _ h1
    rwa [show 2 * (-1 : ℤ) + 1 - (2 * 0 + 1 - i) = i - 2 by ring] at h2
  have h00 : burnsideJ410_E z u ≤ θ 0 := by rw [h0]; exact hF.E_le
  have h01 : burnsideJ410_E z u ≤ θ 1 := by
    have := hstep 0 0 h00
    simpa using this
  have key : ∀ i : ℤ, burnsideJ410_E z u ≤ θ i ∧ burnsideJ410_E z u ≤ θ (i + 1) := by
    intro i
    induction i using Int.induction_on with
    | zero => exact ⟨h00, by simpa using h01⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have := up2 _ ih.1
      rwa [show (k : ℤ) + 2 = k + 1 + 1 by ring] at this
    | pred k ih =>
      refine ⟨?_, ?_⟩
      · have := down2 _ ih.2
        rwa [show -(k : ℤ) + 1 - 2 = -(k : ℤ) - 1 by ring] at this
      · rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
        exact ih.1
  exact (key i).1

theorem burnsideJ410_theta_mem_Ev (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) :
    θ i ∈ EvRu F1 z u (burnsideJ410_lab z u i) :=
  ⟨(hθ i).1, burnsideJ410_theta_E_le hL hF hθ i⟩

theorem burnsideJ410_theta_ne (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) : θ i ≠ θ (i + 3) := by
  intro h
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  have hl3 := burnsideJ410_lab_add_three z u i
  have h1 : θ (i + 3) ∈ FsetRu F1 z (burnsideJ410_lab z u i) := by
    have := (hθ (i + 3)).1
    rwa [hl3] at this
  have key := (burnsideJ410_Fset_eq_iff hF (hθ i).1 h1 (hθ i).2 (hθ (i + 3)).2
    (burnsideJ410_W_spec hL hB hz i).1.1 (burnsideJ410_W_spec hL hB hz (i + 3)).1.1).mp h
  have d := burnsideJ410_lab_distinct hL i
  have c01 := burnsideJ410_W_comm hL hB hz i
  have c12 := burnsideJ410_W_comm hL hB hz (i + 1)
  rw [show i + 1 + 1 = i + 2 by ring] at c12
  have c23 := burnsideJ410_W_comm hL hB hz (i + 2)
  rw [show i + 2 + 1 = i + 3 by ring] at c23
  exact burnsideJ410_path_sup_ne hL (burnsideJ410_W_spec hL hB hz i).1
    (burnsideJ410_W_spec hL hB hz (i + 1)).1 (burnsideJ410_W_spec hL hB hz (i + 2)).1
    (burnsideJ410_W_spec hL hB hz (i + 3)).1 (burnsideJ410_lab_mem z u i)
    (burnsideJ410_lab_mem z u (i + 1)) (burnsideJ410_lab_mem z u (i + 2)) d.1 d.2.1 d.2.2
    (burnsideJ410_W_spec hL hB hz i).2 (burnsideJ410_W_spec hL hB hz (i + 1)).2
    (burnsideJ410_W_spec hL hB hz (i + 2)).2
    (by rw [← hl3]; exact (burnsideJ410_W_spec hL hB hz (i + 3)).2) c01 c12 c23 key

theorem burnsideJ410_theta_type_ne (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {i j : ℤ}
    (h : burnsideJ410_lab z u i ≠ burnsideJ410_lab z u j) : θ i ≠ θ j := by
  intro heq
  exact h (burnsideJ410_Fset_unique_type hL hF (hθ i).1 (heq ▸ (hθ j).1))

theorem burnsideJ410_theta_cover (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) {E' : Subgroup G}
    (h : E' ∈ EvRu F1 z u (burnsideJ410_lab z u i)) : E' = θ i ∨ E' = θ (i + 3) := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  have hl3 := burnsideJ410_lab_add_three z u i
  have hB3 : θ (i + 3) ∈ EvRu F1 z u (burnsideJ410_lab z u i) := by
    have := burnsideJ410_theta_mem_Ev hL hF hθ (i + 3)
    rwa [hl3] at this
  have hsp := burnsideJ410_W_spec hL hB hz i
  rcases burnsideJ410_Ev_le_two hL hF (burnsideJ410_lab_mem z u i) hsp.1 hsp.2 h
    (burnsideJ410_theta_mem_Ev hL hF hθ i) hB3 with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 (burnsideJ410_theta_ne hL hF hθ i)

theorem burnsideJ410_theta_add6 (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) : θ (i + 6) = θ i := by
  have hl6 : burnsideJ410_lab z u (i + 6) = burnsideJ410_lab z u i := by
    have h1 := burnsideJ410_lab_add_three z u (i + 3)
    have h2 := burnsideJ410_lab_add_three z u i
    rw [show i + 3 + 3 = i + 6 by ring] at h1
    rw [h1, h2]
  have h6 : θ (i + 6) ∈ EvRu F1 z u (burnsideJ410_lab z u i) := by
    have := burnsideJ410_theta_mem_Ev hL hF hθ (i + 6)
    rwa [hl6] at this
  rcases burnsideJ410_theta_cover hL hF hθ i h6 with h | h
  · exact h
  · exfalso
    exact burnsideJ410_theta_ne hL hF hθ (i + 3) (by rw [show i + 3 + 3 = i + 6 by ring]; exact h.symm)

theorem burnsideJ410_theta_per (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {a b : ℤ} (hab : a ≡ b [ZMOD 6]) : θ a = θ b := by
  obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hab
  have hb : b = a + 6 * q := by omega
  have key : ∀ q : ℤ, θ (a + 6 * q) = θ a := by
    intro q
    induction q using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have := burnsideJ410_theta_add6 hL hF hθ (a + 6 * k)
      rw [show a + 6 * ((k : ℤ) + 1) = a + 6 * k + 6 by ring, this, ih]
    | pred k ih =>
      have := burnsideJ410_theta_add6 hL hF hθ (a + 6 * (-(k : ℤ) - 1))
      rw [show a + 6 * (-(k : ℤ) - 1) + 6 = a + 6 * (-(k : ℤ)) by ring] at this
      rw [← this]
      exact ih
  rw [hb, key q]

end Theta

end BurnsideJ410F

section BurnsideJ410G

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G] {z u : G} {F1 B5 I0 : Subgroup G}

structure burnsideJ410_Fix2 (z u : G) (F1 B5 I0 : Subgroup G) : Prop where
  I0_le : I0 ≤ F1 ⊓ Subgroup.normalizer (B5 : Set G)
  I0_card : Nat.card I0 = 16
  NF1_card : Nat.card (F1 ⊓ Subgroup.normalizer (B5 : Set G) : Subgroup G) = 80
  I0_inv : ∀ i ∈ I0, i * i = 1 → i = 1 ∨ i = z ∨ i = u ∨ i = u * z
  E_le_I0 : burnsideJ410_E z u ≤ I0
  Fe : ∀ f ∈ F1, f * u * f⁻¹ ≠ u * z
  J : ∃ k : G, k⁻¹ * z * k = u ∧ (∀ c ∈ F1, c * u = u * c → k * c * k⁻¹ ∈ F1) ∧
    ∃ w ∈ O5N B5 ⊓ Subgroup.centralizer ({u} : Set G), w ≠ 1 ∧ k * w * k⁻¹ ∈ F1
  r : ∃ r ∈ Subgroup.centralizer ({z} : Set G), r ∈ Subgroup.normalizer (B5 : Set G) ∧
    r ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G) ∧ r * u * r⁻¹ = u * z

@[expose] def burnsideJ410_R (z u : G) (E₁ E₂ : Subgroup G) : Prop :=
  ∃ B₁ B₂ : Subgroup G, B₁ ≤ E₁ ∧ B₂ ≤ E₂ ∧ Nat.card B₁ = 5 ∧ Nat.card B₂ = 5 ∧
    burnsideJ410_E z u ≤ Subgroup.normalizer (B₁ : Set G) ∧
    burnsideJ410_E z u ≤ Subgroup.normalizer (B₂ : Set G) ∧ ⁅B₁, B₂⁆ = ⊥

theorem burnsideJ410_R_symm {E₁ E₂ : Subgroup G} (h : burnsideJ410_R z u E₁ E₂) :
    burnsideJ410_R z u E₂ E₁ := by
  obtain ⟨B₁, B₂, h1, h2, c1, c2, n1, n2, hc⟩ := h
  exact ⟨B₂, B₁, h2, h1, c2, c1, n2, n1, by rw [Subgroup.commutator_comm]; exact hc⟩

theorem burnsideJ410_adj_iff {Es : Set (Subgroup G)} {E₁ E₂ : ↥Es} :
    (EgonGraph Es z u).Adj E₁ E₂ ↔ (E₁ : Subgroup G) ≠ E₂ ∧ burnsideJ410_R z u E₁ E₂ := by
  unfold EgonGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨fun h' => hne (Subtype.ext h'), h⟩
    · exact ⟨fun h' => hne (Subtype.ext h'), burnsideJ410_R_symm h⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun h' => hne (congrArg Subtype.val h'), Or.inl h⟩

theorem burnsideJ410_conj_R {E₁ E₂ : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) (h : burnsideJ410_R z u E₁ E₂) :
    burnsideJ410_R z u (CFSG.conjugate E₁ g) (CFSG.conjugate E₂ g) := by
  obtain ⟨B₁, B₂, h1, h2, c1, c2, n1, n2, hc⟩ := h
  refine ⟨CFSG.conjugate B₁ g, CFSG.conjugate B₂ g, CFSG.ASVolI.RuChoice.fx_conjugate_mono g h1,
    CFSG.ASVolI.RuChoice.fx_conjugate_mono g h2, ?_, ?_,
    (burnsideJ410_conj_mem_EInv5 hg (⟨c1, n1⟩ : B₁ ∈ EInv5Ru z u)).2,
    (burnsideJ410_conj_mem_EInv5 hg (⟨c2, n2⟩ : B₂ ∈ EInv5Ru z u)).2,
    (burnsideJ410_conj_comm_bot g).mpr hc⟩
  · rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact c1
  · rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact c2

theorem burnsideJ410_conj_Es (hL : burnsideJ410_Loc z u) {g : G}
    (hg : g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G)) {E' : Subgroup G}
    (h : E' ∈ EsetRu F1 z u) : CFSG.conjugate E' g ∈ EsetRu F1 z u := by
  have key : ∀ v : G, v ∈ burnsideJ410_Einv z u → E' ∈ EvRu F1 z u v →
      CFSG.conjugate E' g ∈ EsetRu F1 z u := by
    intro v hv hE
    have h1 := burnsideJ410_conj_Ev hg hE
    have h2 := burnsideJ410_conj_Einv hL hg hv
    simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h2 | h2 | h2
    · rw [h2] at h1; exact Or.inl (Or.inl h1)
    · rw [h2] at h1; exact Or.inl (Or.inr h1)
    · rw [h2] at h1; exact Or.inr h1
  rcases h with (h | h) | h
  · exact key z (burnsideJ410_z_mem z u) h
  · exact key u (burnsideJ410_u_mem z u) h
  · exact key (u * z) (burnsideJ410_uz_mem z u) h

theorem burnsideJ410_W_one (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) :
    burnsideJ410_W z u B5 1 = O5N B5 ⊓ Subgroup.centralizer ({u} : Set G) := by
  have := (burnsideJ410_W_succ_nb hL hB hz 0).1
  rwa [zero_add, burnsideJ410_W_zero, burnsideJ410_lab_one] at this

theorem burnsideJ410_W_neg_one (hL : burnsideJ410_Loc z u) {B5 : Subgroup G}
    (hB : B5 ∈ EInv5Ru z u) (hz : burnsideJ410_Cent z B5) :
    burnsideJ410_W z u B5 (-1) = O5N B5 ⊓ Subgroup.centralizer ({u * z} : Set G) := by
  have := (burnsideJ410_W_succ_nb hL hB hz (-1)).2
  rwa [neg_add_cancel, burnsideJ410_W_zero, burnsideJ410_lab_neg_one] at this

theorem burnsideJ410_exists_conj_le_sylow {p : ℕ} [hp : Fact p.Prime] {K S A : Subgroup G}
    (hSK : S ≤ K) (hS : IsPGroup p S) (hidx : ¬ p ∣ S.relIndex K) (hAK : A ≤ K)
    (hA : IsPGroup p A) : ∃ g ∈ K, A ≤ CFSG.conjugate S g := by
  have hS' : IsPGroup p (S.subgroupOf K) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  set P := hS'.toSylow hidx
  have hA' : IsPGroup p (A.subgroupOf K) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  refine ⟨(g : G)⁻¹, inv_mem g.2, ?_⟩
  intro x hx
  have hx' : (⟨x, hAK hx⟩ : K) ∈ ((g • P : Sylow p K) : Subgroup K) := by
    rw [hg]
    exact hQ (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  have hP : ((P : Sylow p K) : Subgroup K) = S.subgroupOf K := IsPGroup.toSylow_coe _ _
  rw [hP, Subgroup.mem_subgroupOf] at hx'
  have e : (((MulAut.conj g)⁻¹ • (⟨x, hAK hx⟩ : K) : K) : G) = (g : G)⁻¹ * x * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rw [e] at hx'
  rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
  simpa using hx'

theorem burnsideJ410_E_isPGroup (hL : burnsideJ410_Loc z u) : IsPGroup 2 (burnsideJ410_E z u) := by
  intro x
  refine ⟨1, ?_⟩
  have hx : (x : G) * x = 1 := by
    rcases (burnsideJ410_mem_E_iff hL).mp x.2 with h | h | h | h <;> rw [h]
    · simp
    · exact hL.z_sq
    · exact hL.u_sq
    · exact burnsideJ410_uz_sq hL
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  simpa [pow_two] using hx

theorem burnsideJ410_trans (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hF2 : burnsideJ410_Fix2 z u F1 B5 I0) {B₁ : Subgroup G} (hB₁ : B₁ ∈ EInv5Ru z u)
    (hB₁F : B₁ ≤ F1) :
    ∃ g ∈ F1, g ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G) ∧
      B₁ = CFSG.conjugate B5 g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK1 : ¬ 5 ^ 2 ∣ Nat.card F1 := by rw [hF.F1_card]; norm_num
  obtain ⟨g₀, hg₀, hB₁eq⟩ := burnsideJ410_sylow_conj hK1 hF.B5_card hB₁.1 hF.B5_le hB₁F
  have hF1c : CFSG.conjugate F1 g₀ = F1 :=
    CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer hg₀)
  have hKeq : CFSG.conjugate (F1 ⊓ Subgroup.normalizer (B5 : Set G)) g₀ =
      F1 ⊓ Subgroup.normalizer (B₁ : Set G) := by
    rw [CFSG.ASVolI.RuChoice.conjugate_inf, hF1c, ← CFSG.ASVolI.RuChoice.fx_normalizer_conjugate,
      ← hB₁eq]
  have hK'c : Nat.card (F1 ⊓ Subgroup.normalizer (B₁ : Set G) : Subgroup G) = 80 := by
    rw [← hKeq, CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF2.NF1_card
  have hI0'le : CFSG.conjugate I0 g₀ ≤ F1 ⊓ Subgroup.normalizer (B₁ : Set G) := by
    rw [← hKeq]; exact CFSG.ASVolI.RuChoice.fx_conjugate_mono g₀ hF2.I0_le
  have hI0'c : Nat.card (CFSG.conjugate I0 g₀) = 16 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hF2.I0_card
  have hI0'p : IsPGroup 2 (CFSG.conjugate I0 g₀) := IsPGroup.of_card (n := 4) (by rw [hI0'c]; norm_num)
  have hidx : ¬ 2 ∣ (CFSG.conjugate I0 g₀).relIndex (F1 ⊓ Subgroup.normalizer (B₁ : Set G)) := by
    have h := CFSG.Quasithin.RuType.relIndex_mul_card_of_le hI0'le
    rw [hI0'c, hK'c] at h
    intro hd
    omega
  have hEK' : burnsideJ410_E z u ≤ F1 ⊓ Subgroup.normalizer (B₁ : Set G) :=
    le_inf hF.E_le hB₁.2
  obtain ⟨x, hxK', hEx⟩ := burnsideJ410_exists_conj_le_sylow hI0'le hI0'p hidx hEK'
    (burnsideJ410_E_isPGroup hL)
  have hxF : x ∈ F1 := (Subgroup.mem_inf.mp hxK').1
  have hxN : x ∈ Subgroup.normalizer (B₁ : Set G) := (Subgroup.mem_inf.mp hxK').2
  have hgB : B₁ = CFSG.conjugate B5 (g₀ * x) := by
    rw [← CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, ← hB₁eq,
      CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hxN]
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate] at hEx
  refine ⟨g₀ * x, mul_mem hg₀ hxF, ?_, hgB⟩
  refine CFSG.ASVolI.RuChoice.mem_normalizer fun e he => ?_
  have h1 : (g₀ * x) * e * (g₀ * x)⁻¹ ∈ I0 := by
    have := hEx he
    rwa [CFSG.ASVolI.RuChoice.fx_mem_conjugate] at this
  have hsq : ((g₀ * x) * e * (g₀ * x)⁻¹) * ((g₀ * x) * e * (g₀ * x)⁻¹) = 1 := by
    have hee : e * e = 1 := by
      rcases (burnsideJ410_mem_E_iff hL).mp he with h | h | h | h <;> rw [h]
      · simp
      · exact hL.z_sq
      · exact hL.u_sq
      · exact burnsideJ410_uz_sq hL
    calc ((g₀ * x) * e * (g₀ * x)⁻¹) * ((g₀ * x) * e * (g₀ * x)⁻¹)
        = (g₀ * x) * (e * e) * (g₀ * x)⁻¹ := by group
      _ = 1 := by rw [hee]; group
  exact (burnsideJ410_mem_E_iff hL).mpr (hF2.I0_inv _ h1 hsq)

theorem burnsideJ410_deg_z (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    {E'' : Subgroup G} (hE : E'' ∈ EvRu F1 z u z) (hR : burnsideJ410_R z u F1 E'') :
    E'' = F1 := by
  obtain ⟨B₁, B₂, hB₁F, hB₂E, c₁, c₂, hN₁, hN₂, hcomm⟩ := hR
  have hB₁X : B₁ ∈ EInv5Ru z u := ⟨c₁, hN₁⟩
  have hB₂X : B₂ ∈ EInv5Ru z u := ⟨c₂, hN₂⟩
  have hz₁ : burnsideJ410_Cent z B₁ :=
    burnsideJ410_cent_of_le_centralizer (hB₁F.trans hF.F1_le)
  have hB₂z : B₂ ≤ Subgroup.centralizer ({z} : Set G) :=
    hB₂E.trans (burnsideJ410_Fset_le_centralizer hF hE.1)
  have hle : B₂ ≤ B₁ := by
    rw [← burnsideJ410_cent_O5N hL hB₁X (burnsideJ410_z_mem z u) hz₁]
    exact le_inf (burnsideJ410_le_O5N hL hB₁X hB₂X (burnsideJ410_z_mem z u) hz₁ hcomm) hB₂z
  have heq : B₂ = B₁ := Subgroup.eq_of_le_of_card_ge hle (by rw [c₁, c₂])
  have hF1 : F1 ∈ FsetRu F1 z z :=
    ⟨1, by simp, (CFSG.ASVolI.RuChoice.fx_conjugate_one F1).symm⟩
  exact ((burnsideJ410_Fset_eq_iff hF hF1 hE.1 hB₁F (heq ▸ hB₂E) c₁ c₁).mpr rfl).symm

theorem burnsideJ410_deg_u (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hF2 : burnsideJ410_Fix2 z u F1 B5 I0) {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {E'' : Subgroup G} (hE : E'' ∈ EvRu F1 z u u)
    (hR : burnsideJ410_R z u F1 E'') : E'' = θ 1 := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  obtain ⟨B₁, B₂, hB₁F, hB₂E, c₁, c₂, hN₁, hN₂, hcomm⟩ := hR
  have hB₁X : B₁ ∈ EInv5Ru z u := ⟨c₁, hN₁⟩
  have hB₂X : B₂ ∈ EInv5Ru z u := ⟨c₂, hN₂⟩
  have hz₁ : burnsideJ410_Cent z B₁ :=
    burnsideJ410_cent_of_le_centralizer (hB₁F.trans hF.F1_le)
  have hu₂ : burnsideJ410_Cent u B₂ :=
    burnsideJ410_cent_of_le_centralizer (hB₂E.trans (burnsideJ410_Fset_le_centralizer hF hE.1))
  have hne12 : B₁ ≠ B₂ := by
    intro h
    rw [← h] at hu₂
    exact hL.u_ne (burnsideJ410_label_unique hL hB₁X (burnsideJ410_u_mem z u)
      (burnsideJ410_z_mem z u) hu₂ hz₁)
  obtain ⟨-, hB₂eq⟩ := burnsideJ410_nbr_eq hL hB₁X hB₂X hne12 hcomm (burnsideJ410_z_mem z u) hz₁
    (burnsideJ410_u_mem z u) hu₂
  obtain ⟨g, hgF, hgN, hB₁eq⟩ := burnsideJ410_trans hL hF hF2 hB₁X hB₁F
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hF.F1_le hgF)
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have hguE : g * u * g⁻¹ ∈ burnsideJ410_E z u :=
    (Subgroup.mem_normalizer_iff.mp hgN u).mp (burnsideJ410_Einv_mem_E hL (burnsideJ410_u_mem z u))
  have hgu : g * u * g⁻¹ = u := by
    rcases (burnsideJ410_mem_E_iff hL).mp hguE with h | h | h | h
    · exfalso
      apply burnsideJ410_u_ne_one hL
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hL.u_ne
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * z * g := by rw [h]
        _ = z := by
          calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgz]
            _ = z := by group
    · exact h
    · exact absurd h (hF2.Fe g hgF)
  have hgu' : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (g * u * g⁻¹) * g := by rw [hgu]
      _ = u := by group
  have hWB := burnsideJ410_conj_nb hL hB (burnsideJ410_z_mem z u) hz u hgN
  have hB₂W : CFSG.conjugate (burnsideJ410_W z u B5 1) g = B₂ := by
    rw [burnsideJ410_W_one hL hB hz, hWB, hgu', ← hB₁eq, hB₂eq]
  have hθ1 : θ 1 ∈ FsetRu F1 z u := by
    have := (hθ 1).1
    rwa [burnsideJ410_lab_one] at this
  have hθ1g : CFSG.conjugate (θ 1) g ∈ FsetRu F1 z u := by
    have := burnsideJ410_conj_Fset (g := g) hθ1
    rwa [hgu'] at this
  have hW1le : B₂ ≤ CFSG.conjugate (θ 1) g := by
    rw [← hB₂W]; exact CFSG.ASVolI.RuChoice.fx_conjugate_mono g (hθ 1).2
  have hE1 : CFSG.conjugate (θ 1) g = E'' :=
    (burnsideJ410_Fset_eq_iff hF hθ1g hE.1 hW1le hB₂E c₂ c₂).mpr rfl
  obtain ⟨k, hk, hkc, w, hwmem, hw1, hkw⟩ := hF2.J
  have hFu : CFSG.conjugate F1 k ∈ FsetRu F1 z u := ⟨k, hk, rfl⟩
  have hW1c : Nat.card (burnsideJ410_W z u B5 1) = 5 := (burnsideJ410_W_spec hL hB hz 1).1.1
  have hwW : w ∈ burnsideJ410_W z u B5 1 := by rw [burnsideJ410_W_one hL hB hz]; exact hwmem
  have hW1gen : Subgroup.zpowers w = burnsideJ410_W z u B5 1 :=
    CFSG.Quasithin.RuType.zpowers_eq_of_card_five hW1c hwW (burnsideJ410_pow_five hW1c hwW) hw1
  have hW1Fu : burnsideJ410_W z u B5 1 ≤ CFSG.conjugate F1 k := by
    rw [← hW1gen]
    refine Subgroup.zpowers_le.mpr ?_
    rw [CFSG.ASVolI.RuChoice.fx_mem_conjugate]
    exact hkw
  have hθFu : θ 1 = CFSG.conjugate F1 k :=
    (burnsideJ410_Fset_eq_iff hF hθ1 hFu (hθ 1).2 hW1Fu hW1c hW1c).mpr rfl
  have hgFu : g ∈ θ 1 := by
    rw [hθFu, CFSG.ASVolI.RuChoice.fx_mem_conjugate]
    exact hkc g hgF (by
      calc g * u = (g * u * g⁻¹) * g := by group
        _ = u * g := by rw [hgu])
  rw [← hE1]
  exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer hgFu)

theorem burnsideJ410_deg_uz (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hF2 : burnsideJ410_Fix2 z u F1 B5 I0) {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {E'' : Subgroup G} (hE : E'' ∈ EvRu F1 z u (u * z))
    (hR : burnsideJ410_R z u F1 E'') : E'' = θ (-1) := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  obtain ⟨r, hrH, hrB, hrE, hru⟩ := hF2.r
  have hrF : r ∈ Subgroup.normalizer (F1 : Set G) := hF.NH_le r hrH hrB
  have hF1r : CFSG.conjugate F1 r = F1 := CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hrF
  have hrz : r⁻¹ * (u * z) * r = u := by
    calc r⁻¹ * (u * z) * r = r⁻¹ * (r * u * r⁻¹) * r := by rw [hru]
      _ = u := by group
  have hE0 : CFSG.conjugate E'' r ∈ EvRu F1 z u u := by
    have := burnsideJ410_conj_Ev hrE hE
    rwa [hrz] at this
  have hR0 : burnsideJ410_R z u F1 (CFSG.conjugate E'' r) := by
    have := burnsideJ410_conj_R hrE hR
    rwa [hF1r] at this
  have h1 := burnsideJ410_deg_u hL hF hF2 hθ hE0 hR0
  have hE'' : E'' = CFSG.conjugate (θ 1) r⁻¹ := by
    calc E'' = CFSG.conjugate (CFSG.conjugate E'' r) r⁻¹ := (burnsideJ410_conj_conj_inv E'' r).symm
      _ = CFSG.conjugate (θ 1) r⁻¹ := by rw [h1]
  have hr' : r⁻¹ ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G) := inv_mem hrE
  have hrB' : r⁻¹ ∈ Subgroup.normalizer (B5 : Set G) := inv_mem hrB
  have hθ1 : θ 1 ∈ FsetRu F1 z u := by
    have := (hθ 1).1
    rwa [burnsideJ410_lab_one] at this
  have hrr : (r⁻¹)⁻¹ * u * r⁻¹ = u * z := by rw [inv_inv]; exact hru
  have h2 : CFSG.conjugate (θ 1) r⁻¹ ∈ FsetRu F1 z (u * z) := by
    have := burnsideJ410_conj_Fset (g := r⁻¹) hθ1
    rwa [hrr] at this
  have h3 : θ (-1) ∈ FsetRu F1 z (u * z) := by
    have := (hθ (-1)).1
    rwa [burnsideJ410_lab_neg_one] at this
  have hWW : CFSG.conjugate (burnsideJ410_W z u B5 1) r⁻¹ = burnsideJ410_W z u B5 (-1) := by
    rw [burnsideJ410_W_one hL hB hz, burnsideJ410_conj_nb hL hB (burnsideJ410_z_mem z u) hz u hr',
      CFSG.ASVolI.RuChoice.fx_conjugate_eq_self hrB', hrr, burnsideJ410_W_neg_one hL hB hz]
  have h4 : burnsideJ410_W z u B5 (-1) ≤ CFSG.conjugate (θ 1) r⁻¹ := by
    rw [← hWW]; exact CFSG.ASVolI.RuChoice.fx_conjugate_mono r⁻¹ (hθ 1).2
  have hcard : Nat.card (burnsideJ410_W z u B5 (-1)) = 5 :=
    (burnsideJ410_W_spec hL hB hz (-1)).1.1
  rw [hE'']
  exact (burnsideJ410_Fset_eq_iff hF h2 h3 h4 (hθ (-1)).2 hcard hcard).mpr rfl

end BurnsideJ410G

section BurnsideJ410H

open CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G] {z u : G} {F1 B5 I0 : Subgroup G}

theorem burnsideJ410_lab_two (z u : G) : burnsideJ410_lab z u 2 = u * z := by
  simp [burnsideJ410_lab]

theorem burnsideJ410_theta_zero (hF : burnsideJ410_Fix z u F1 B5) {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) : θ 0 = F1 := by
  have hF1 : F1 ∈ FsetRu F1 z z :=
    ⟨1, by simp, (CFSG.ASVolI.RuChoice.fx_conjugate_one F1).symm⟩
  have hθ0 : θ 0 ∈ FsetRu F1 z z := by
    have := (hθ 0).1
    rwa [burnsideJ410_lab_zero] at this
  have hle : burnsideJ410_W z u B5 0 ≤ θ 0 := (hθ 0).2
  rw [burnsideJ410_W_zero] at hle
  exact (burnsideJ410_Fset_eq_iff hF hθ0 hF1 hle hF.B5_le hF.B5_card hF.B5_card).mpr rfl

@[expose] def burnsideJ410_P (z u : G) (F1 : Subgroup G) (θ : ℤ → Subgroup G) (i : ℤ) : Prop :=
  ∀ E'' : Subgroup G, E'' ∈ EsetRu F1 z u → θ i ≠ E'' → burnsideJ410_R z u (θ i) E'' →
    E'' = θ (i + 1) ∨ E'' = θ (i - 1)

theorem burnsideJ410_P_zero (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hF2 : burnsideJ410_Fix2 z u F1 B5 I0) {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) : burnsideJ410_P z u F1 θ 0 := by
  intro E'' hE'' hne hR
  have h0 := burnsideJ410_theta_zero hF hθ
  rw [h0] at hne hR
  rcases hE'' with (h | h) | h
  · exact absurd (burnsideJ410_deg_z hL hF h hR).symm hne
  · left
    rw [burnsideJ410_deg_u hL hF hF2 hθ h hR, zero_add]
  · right
    rw [burnsideJ410_deg_uz hL hF hF2 hθ h hR, zero_sub]

theorem burnsideJ410_P_step (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (j : ℤ) {i : ℤ} (hP : burnsideJ410_P z u F1 θ i) :
    burnsideJ410_P z u F1 θ (2 * j + 1 - i) := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  obtain ⟨s, hs, hsk⟩ := burnsideJ410_W_swap hL hB hz j
  have hconj : ∀ k : ℤ, CFSG.conjugate (θ k) s = θ (2 * j + 1 - k) := by
    intro k
    have h := hsk (k - j)
    rw [show j + (k - j) = k by ring, show j + 1 - (k - j) = 2 * j + 1 - k by ring] at h
    exact burnsideJ410_theta_conj hL hF hθ hs h
  intro E'' hE'' hne hR
  have hs' : s⁻¹ ∈ Subgroup.normalizer (burnsideJ410_E z u : Set G) := inv_mem hs
  have hE0 : CFSG.conjugate E'' s⁻¹ ∈ EsetRu F1 z u := burnsideJ410_conj_Es hL hs' hE''
  have hθi : CFSG.conjugate (θ (2 * j + 1 - i)) s⁻¹ = θ i := by
    rw [← hconj i, burnsideJ410_conj_conj_inv]
  have hne0 : θ i ≠ CFSG.conjugate E'' s⁻¹ := by
    intro h
    apply hne
    rw [← hconj i, h, burnsideJ410_conj_inv_conj]
  have hR0 : burnsideJ410_R z u (θ i) (CFSG.conjugate E'' s⁻¹) := by
    have := burnsideJ410_conj_R hs' hR
    rwa [hθi] at this
  have hback : E'' = CFSG.conjugate (CFSG.conjugate E'' s⁻¹) s :=
    (burnsideJ410_conj_inv_conj E'' s).symm
  rcases hP _ hE0 hne0 hR0 with h | h
  · right
    rw [hback, h, hconj]
    congr 1; ring
  · left
    rw [hback, h, hconj]
    congr 1; ring

theorem burnsideJ410_P_all (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hF2 : burnsideJ410_Fix2 z u F1 B5 I0) {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) : burnsideJ410_P z u F1 θ i := by
  have h0 := burnsideJ410_P_zero hL hF hF2 hθ
  have h1 : burnsideJ410_P z u F1 θ 1 := by
    have := burnsideJ410_P_step hL hF hθ 0 h0
    simpa using this
  have up2 : ∀ i : ℤ, burnsideJ410_P z u F1 θ i → burnsideJ410_P z u F1 θ (i + 2) := by
    intro i hi
    have h2 := burnsideJ410_P_step hL hF hθ 0 (burnsideJ410_P_step hL hF hθ (-1) hi)
    rwa [show 2 * (0 : ℤ) + 1 - (2 * (-1) + 1 - i) = i + 2 by ring] at h2
  have down2 : ∀ i : ℤ, burnsideJ410_P z u F1 θ i → burnsideJ410_P z u F1 θ (i - 2) := by
    intro i hi
    have h2 := burnsideJ410_P_step hL hF hθ (-1) (burnsideJ410_P_step hL hF hθ 0 hi)
    rwa [show 2 * (-1 : ℤ) + 1 - (2 * 0 + 1 - i) = i - 2 by ring] at h2
  have key : ∀ i : ℤ, burnsideJ410_P z u F1 θ i ∧ burnsideJ410_P z u F1 θ (i + 1) := by
    intro i
    induction i using Int.induction_on with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have := up2 _ ih.1
      rwa [show (k : ℤ) + 2 = k + 1 + 1 by ring] at this
    | pred k ih =>
      refine ⟨?_, ?_⟩
      · have := down2 _ ih.2
        rwa [show -(k : ℤ) + 1 - 2 = -(k : ℤ) - 1 by ring] at this
      · rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
        exact ih.1
  exact (key i).1

theorem burnsideJ410_theta_mem_Es (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) : θ i ∈ EsetRu F1 z u := by
  have h := burnsideJ410_theta_mem_Ev hL hF hθ i
  have hm := burnsideJ410_lab_mem z u i
  simp only [burnsideJ410_Einv, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with hm | hm | hm
  · rw [hm] at h; exact Or.inl (Or.inl h)
  · rw [hm] at h; exact Or.inl (Or.inr h)
  · rw [hm] at h; exact Or.inr h

theorem burnsideJ410_theta_cover_Es (hL : burnsideJ410_Loc z u)
    (hF : burnsideJ410_Fix z u F1 B5) {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {E' : Subgroup G} (hE' : E' ∈ EsetRu F1 z u) :
    ∃ n : ℕ, n < 6 ∧ E' = θ (n : ℤ) := by
  rcases hE' with (h | h) | h
  · have h' : E' ∈ EvRu F1 z u (burnsideJ410_lab z u 0) := by
      rw [burnsideJ410_lab_zero]; exact h
    rcases burnsideJ410_theta_cover hL hF hθ 0 h' with h1 | h1
    · exact ⟨0, by norm_num, by simpa using h1⟩
    · exact ⟨3, by norm_num, by simpa using h1⟩
  · have h' : E' ∈ EvRu F1 z u (burnsideJ410_lab z u 1) := by
      rw [burnsideJ410_lab_one]; exact h
    rcases burnsideJ410_theta_cover hL hF hθ 1 h' with h1 | h1
    · exact ⟨1, by norm_num, by simpa using h1⟩
    · exact ⟨4, by norm_num, by rw [h1]; norm_num⟩
  · have h' : E' ∈ EvRu F1 z u (burnsideJ410_lab z u 2) := by
      rw [burnsideJ410_lab_two]; exact h
    rcases burnsideJ410_theta_cover hL hF hθ 2 h' with h1 | h1
    · exact ⟨2, by norm_num, by simpa using h1⟩
    · exact ⟨5, by norm_num, by rw [h1]; norm_num⟩

theorem burnsideJ410_R_theta (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) (i : ℤ) : burnsideJ410_R z u (θ i) (θ (i + 1)) := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  exact ⟨burnsideJ410_W z u B5 i, burnsideJ410_W z u B5 (i + 1), (hθ i).2, (hθ (i + 1)).2,
    (burnsideJ410_W_spec hL hB hz i).1.1, (burnsideJ410_W_spec hL hB hz (i + 1)).1.1,
    (burnsideJ410_W_spec hL hB hz i).1.2, (burnsideJ410_W_spec hL hB hz (i + 1)).1.2,
    burnsideJ410_W_comm hL hB hz i⟩

theorem burnsideJ410_theta_mod (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    {θ : ℤ → Subgroup G}
    (hθ : ∀ i : ℤ, θ i ∈ FsetRu F1 z (burnsideJ410_lab z u i) ∧
      burnsideJ410_W z u B5 i ≤ θ i) {a b : ℤ} (h : θ a = θ b) : a ≡ b [ZMOD 6] := by
  by_contra hne
  rcases (show (a - b) % 3 = 0 ∨ (a - b) % 3 ≠ 0 by omega) with h3 | h3
  · have h6 : a ≡ b + 3 [ZMOD 6] := by
      unfold Int.ModEq at hne ⊢
      omega
    have := burnsideJ410_theta_per hL hF hθ h6
    exact burnsideJ410_theta_ne hL hF hθ b (by rw [← this, h])
  · refine burnsideJ410_theta_type_ne hL hF hθ ?_ h
    intro hl
    have := burnsideJ410_lab_inj hL hl
    omega

theorem burnsideJ410_cyc_adj (i j : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i j ↔
      (((i : ℕ) : ℤ) + 1) % 6 = ((j : ℕ) : ℤ) ∨ (((j : ℕ) : ℤ) + 1) % 6 = ((i : ℕ) : ℤ) := by
  rw [SimpleGraph.cycleGraph_adj]
  fin_cases i <;> fin_cases j <;> decide

theorem burnsideJ410_hexagon (hL : burnsideJ410_Loc z u) (hF : burnsideJ410_Fix z u F1 B5)
    (hF2 : burnsideJ410_Fix2 z u F1 B5 I0) :
    Nonempty (EgonGraph (EsetRu F1 z u) z u ≃g SimpleGraph.cycleGraph 6) := by
  have hB := burnsideJ410_Fix_B5_mem hF
  have hz := burnsideJ410_Fix_B5_cent hF
  choose θ hθ using fun i : ℤ => burnsideJ410_Fset_exists hF
    (burnsideJ410_Einv_conj hL (burnsideJ410_lab_mem z u i))
    (burnsideJ410_W_spec hL hB hz i).1.1
    (burnsideJ410_le_centralizer_of_cent (burnsideJ410_W_spec hL hB hz i).2)
  have hP := burnsideJ410_P_all hL hF hF2 hθ
  have hmem := burnsideJ410_theta_mem_Es hL hF hθ
  have hmod := fun a b (h : θ a = θ b) => burnsideJ410_theta_mod hL hF hθ h
  let f : Fin 6 → ↥(EsetRu F1 z u) := fun i => ⟨θ ((i : ℕ) : ℤ), hmem _⟩
  have hf_inj : Function.Injective f := by
    intro i j h
    have h' : θ ((i : ℕ) : ℤ) = θ ((j : ℕ) : ℤ) := congrArg Subtype.val h
    have := hmod _ _ h'
    unfold Int.ModEq at this
    have hi := i.2
    have hj := j.2
    exact Fin.ext (by omega)
  have hf_surj : Function.Surjective f := by
    rintro ⟨E', hE'⟩
    obtain ⟨n, hn, rfl⟩ := burnsideJ410_theta_cover_Es hL hF hθ hE'
    exact ⟨⟨n, hn⟩, rfl⟩
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  let φ : SimpleGraph.cycleGraph 6 ≃g EgonGraph (EsetRu F1 z u) z u :=
    { toEquiv := Equiv.ofBijective f hbij
      map_rel_iff' := by
        intro i j
        simp only [Equiv.ofBijective_apply]
        rw [burnsideJ410_cyc_adj, burnsideJ410_adj_iff]
        show (θ ((i : ℕ) : ℤ) ≠ θ ((j : ℕ) : ℤ) ∧ burnsideJ410_R z u (θ ((i : ℕ) : ℤ))
          (θ ((j : ℕ) : ℤ))) ↔ _
        have hi := i.2
        have hj := j.2
        constructor
        · rintro ⟨hne, hR⟩
          rcases hP ((i : ℕ) : ℤ) _ (hmem ((j : ℕ) : ℤ)) hne hR with h | h
          · have := hmod _ _ h
            unfold Int.ModEq at this
            left; omega
          · have := hmod _ _ h
            unfold Int.ModEq at this
            right; omega
        · rintro (h | h)
          · have hθj : θ ((j : ℕ) : ℤ) = θ (((i : ℕ) : ℤ) + 1) := by
              apply burnsideJ410_theta_per hL hF hθ
              unfold Int.ModEq
              omega
            rw [hθj]
            refine ⟨?_, burnsideJ410_R_theta hL hF hθ _⟩
            exact burnsideJ410_theta_type_ne hL hF hθ (burnsideJ410_lab_distinct hL _).1
          · have hθi : θ ((i : ℕ) : ℤ) = θ (((j : ℕ) : ℤ) + 1) := by
              apply burnsideJ410_theta_per hL hF hθ
              unfold Int.ModEq
              omega
            rw [hθi]
            refine ⟨?_, burnsideJ410_R_symm (burnsideJ410_R_theta hL hF hθ _)⟩
            exact (burnsideJ410_theta_type_ne hL hF hθ (burnsideJ410_lab_distinct hL _).1).symm }
  exact ⟨φ.symm⟩

end BurnsideJ410H

section BurnsideJ410S5

open CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma47

theorem burnsideJ410_card_normBy : ∀ σ : SigmaL2F4, σ ^ 5 = 1 → σ ≠ 1 →
    (Finset.univ.filter (fun ν : SigmaL2F4 => NormBy ν σ)).card ≤ 20 := by
  decide +kernel

end BurnsideJ410S5

section BurnsideJ410I

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G]

theorem burnsideJ410_H_eq (M : RuDataM G) :
    ruH M.T = Subgroup.centralizer ({M.z} : Set G) := by
  ext x
  rw [M.mem_H_iff_comm, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem burnsideJ410_Q_eq (M : RuDataM G) : ruQ M.T = burnsideJ410_QOf M.z := by
  unfold burnsideJ410_QOf
  show pCoreOf 2 (ruH M.T) = _
  rw [burnsideJ410_H_eq M]

theorem burnsideJ410_class_le {M : RuDataM G} {σ τ : G} (hσ : σ ∈ ruH M.T) (hτ : τ ∈ ruH M.T)
    (h : Sigma47.PowOfG (M.phiG σ) (M.phiG τ)) :
    Subgroup.zpowers τ ⊔ burnsideJ410_QOf M.z ≤ Subgroup.zpowers σ ⊔ burnsideJ410_QOf M.z := by
  obtain ⟨k, hk⟩ := h
  have hσk : σ ^ (k : ℕ) ∈ ruH M.T := pow_mem hσ _
  have hq : (σ ^ (k : ℕ))⁻¹ * τ ∈ ruQ M.T := by
    rw [← M.phiG_eq_one_iff (mul_mem (inv_mem hσk) hτ), M.phiG_mul (inv_mem hσk) hτ,
      M.phiG_inv hσk, M.phiG_pow hσ, hk, inv_mul_cancel]
  have hτ' : τ ∈ Subgroup.zpowers σ ⊔ burnsideJ410_QOf M.z := by
    have e : τ = σ ^ (k : ℕ) * ((σ ^ (k : ℕ))⁻¹ * τ) := by group
    rw [e]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · rw [← zpow_natCast]; exact Subgroup.zpow_mem_zpowers _ _
    · rw [← burnsideJ410_Q_eq]; exact hq
  exact sup_le (Subgroup.zpowers_le.mpr hτ') le_sup_right

theorem burnsideJ410_class_eq {M : RuDataM G} {σ τ : G} (hσ : σ ∈ ruH M.T) (hτ : τ ∈ ruH M.T)
    (hσ5 : (M.phiG σ) ^ 5 = 1) (hτ1 : M.phiG τ ≠ 1)
    (h : Sigma47.PowOfG (M.phiG σ) (M.phiG τ)) :
    Subgroup.zpowers σ ⊔ burnsideJ410_QOf M.z = Subgroup.zpowers τ ⊔ burnsideJ410_QOf M.z :=
  le_antisymm (burnsideJ410_class_le hτ hσ (Sigma47.powOfG_symm hσ5 hτ1 h))
    (burnsideJ410_class_le hσ hτ h)

theorem burnsideJ410_S5 (M : RuDataM G) {w : G} (hw2 : w * w = 1) (hzw : M.z * w = w * M.z)
    (hwQ : w ∉ burnsideJ410_QOf M.z) {Y₁ Y₂ Y₃ : Subgroup G}
    (h₁ : Y₁ ≤ Subgroup.centralizer ({M.z} : Set G) ∧ Nat.card Y₁ = 5 ∧
      w ∈ Subgroup.normalizer ((Y₁ ⊔ burnsideJ410_QOf M.z : Subgroup G) : Set G))
    (h₂ : Y₂ ≤ Subgroup.centralizer ({M.z} : Set G) ∧ Nat.card Y₂ = 5 ∧
      w ∈ Subgroup.normalizer ((Y₂ ⊔ burnsideJ410_QOf M.z : Subgroup G) : Set G))
    (h₃ : Y₃ ≤ Subgroup.centralizer ({M.z} : Set G) ∧ Nat.card Y₃ = 5 ∧
      w ∈ Subgroup.normalizer ((Y₃ ⊔ burnsideJ410_QOf M.z : Subgroup G) : Set G)) :
    Y₁ ⊔ burnsideJ410_QOf M.z = Y₂ ⊔ burnsideJ410_QOf M.z ∨
      Y₁ ⊔ burnsideJ410_QOf M.z = Y₃ ⊔ burnsideJ410_QOf M.z ∨
      Y₂ ⊔ burnsideJ410_QOf M.z = Y₃ ⊔ burnsideJ410_QOf M.z := by
  have hwH : w ∈ ruH M.T := M.mem_H_iff_comm.mpr hzw
  have key : ∀ Y : Subgroup G, (Y ≤ Subgroup.centralizer ({M.z} : Set G) ∧ Nat.card Y = 5 ∧
      w ∈ Subgroup.normalizer ((Y ⊔ burnsideJ410_QOf M.z : Subgroup G) : Set G)) →
      ∃ σ : G, σ ∈ ruH M.T ∧ σ ^ 5 = 1 ∧ M.phiG σ ≠ 1 ∧ Y = Subgroup.zpowers σ ∧
        Sigma47.NormBy (M.phiG w) (M.phiG σ) := by
    rintro Y ⟨hYz, hY5, hN⟩
    obtain ⟨σ, hσY, hσ5, hσ1, hgen⟩ := exists_gen_of_card_five hY5
    have hσH : σ ∈ ruH M.T := by
      rw [burnsideJ410_H_eq]; exact hYz hσY
    refine ⟨σ, hσH, hσ5, M.phiG_ne_one_of_pow_five hσH hσ5 hσ1,
      (zpowers_eq_of_card_five hY5 hσY hσ5 hσ1).symm, ?_⟩
    have hmem : w * σ * w⁻¹ ∈ Y ⊔ burnsideJ410_QOf M.z :=
      (Subgroup.mem_normalizer_iff.mp hN σ).mp (Subgroup.mem_sup_left hσY)
    have hle : Y ≤ Subgroup.normalizer (burnsideJ410_QOf M.z : Set G) := fun y hy =>
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({M.z} : Set G))
        (hYz hy)
    obtain ⟨y, hy, q, hq, e⟩ := burnsideJ410_mem_sup_normalizer hle hmem
    obtain ⟨k, rfl⟩ := hgen y hy
    have hqC : q ∈ Subgroup.centralizer ({M.z} : Set G) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
    have hqH : q ∈ ruH M.T := by rw [burnsideJ410_H_eq]; exact hqC
    have hqQ : q ∈ ruQ M.T := by rw [burnsideJ410_Q_eq]; exact hq
    have h1 : M.phiG (w * σ * w⁻¹) = M.phiG σ ^ k := by
      rw [← e, M.phiG_mul (pow_mem hσH k) hqH, M.phiG_pow hσH, (M.phiG_eq_one_iff hqH).mpr hqQ,
        mul_one]
    have hσ5' : (M.phiG σ) ^ 5 = 1 := by rw [← M.phiG_pow hσH, hσ5]; exact M.phiG_one47
    obtain ⟨k', hk'⟩ := Sigma47.powOfG_pow (M.phiG σ) k hσ5'
    exact ⟨k', (M.phiG_conj hwH hσH).symm.trans (h1.trans hk')⟩
  obtain ⟨σ₁, h1H, h15, h11, rfl, hN1⟩ := key _ h₁
  obtain ⟨σ₂, h2H, h25, h21, rfl, hN2⟩ := key _ h₂
  obtain ⟨σ₃, h3H, h35, h31, rfl, hN3⟩ := key _ h₃
  have φ5 : ∀ {σ : G}, σ ∈ ruH M.T → σ ^ 5 = 1 → (M.phiG σ) ^ 5 = 1 := fun hσ h5 => by
    rw [← M.phiG_pow hσ, h5]; exact M.phiG_one47
  have hd2 : M.phiG w * M.phiG w = 1 := by
    rw [← M.phiG_mul hwH hwH, hw2]; exact M.phiG_one47
  have hd1 : M.phiG w ≠ 1 := fun h => hwQ (by
    rw [← burnsideJ410_Q_eq]; exact (M.phiG_eq_one_iff hwH).mp h)
  by_cases hp : Sigma47.PowOfG (M.phiG σ₁) (M.phiG σ₂)
  · left
    exact burnsideJ410_class_eq h1H h2H (φ5 h1H h15) h21 hp
  · rcases Sigma47.powOf_of_two_classes hd2 hd1 (φ5 h1H h15) h11 hN1 (φ5 h2H h25) h21 hN2 hp
      (φ5 h3H h35) h31 hN3 with h | h
    · right; left
      exact burnsideJ410_class_eq h1H h3H (φ5 h1H h15) h31 h
    · right; right
      exact burnsideJ410_class_eq h2H h3H (φ5 h2H h25) h31 h

section Conf

variable {M : RuDataM G} (C : RuDataM.Conf47 M)

theorem burnsideJ410_Q_le_normalizer :
    burnsideJ410_QOf M.z ≤ Subgroup.normalizer (C.F1 : Set G) := by
  rw [← burnsideJ410_Q_eq]
  intro q hq
  exact CFSG.ASVolI.RuChoice.mem_normalizer fun f hf => C.conj_mem_F1_of_mem_Q hq hf

theorem burnsideJ410_F1_norm :
    C.F1 ≤ Subgroup.normalizer
      ((Subgroup.zpowers C.b ⊔ burnsideJ410_QOf M.z : Subgroup G) : Set G) := by
  intro f hf
  have hfH : f ∈ ruH M.T := C.F1_le_H hf
  have hfH' : f ∈ Subgroup.centralizer ({M.z} : Set G) := by rw [← burnsideJ410_H_eq]; exact hfH
  have hb : f * C.b * f⁻¹ ∈ Subgroup.zpowers C.b ⊔ burnsideJ410_QOf M.z := by
    obtain ⟨k, hk⟩ := C.F1_norm f hf
    have hbk : C.b ^ k ∈ ruH M.T := pow_mem C.b_mem_H k
    have hfb : f * C.b * f⁻¹ ∈ ruH M.T := mul_mem (mul_mem hfH C.b_mem_H) (inv_mem hfH)
    have hq : (C.b ^ k)⁻¹ * (f * C.b * f⁻¹) ∈ ruQ M.T := by
      rw [← M.phiG_eq_one_iff (mul_mem (inv_mem hbk) hfb), M.phiG_mul (inv_mem hbk) hfb,
        M.phiG_inv hbk, M.phiG_pow C.b_mem_H, hk, inv_mul_cancel]
    have e : f * C.b * f⁻¹ = C.b ^ k * ((C.b ^ k)⁻¹ * (f * C.b * f⁻¹)) := by group
    rw [e]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · rw [← zpow_natCast]; exact Subgroup.zpow_mem_zpowers _ _
    · rw [← burnsideJ410_Q_eq]; exact hq
  refine CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => ?_
  have hle : Subgroup.zpowers C.b ≤ Subgroup.normalizer (burnsideJ410_QOf M.z : Set G) := by
    intro y hy
    have hyH : y ∈ Subgroup.centralizer ({M.z} : Set G) := by
      rw [← burnsideJ410_H_eq]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact zpow_mem C.b_mem_H n
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({M.z} : Set G)) hyH
  obtain ⟨s, hs, q, hq, rfl⟩ := burnsideJ410_mem_sup_normalizer hle hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have e : f * (C.b ^ n * q) * f⁻¹ = (f * C.b * f⁻¹) ^ n * (f * q * f⁻¹) := by
    rw [conj_zpow]; group
  rw [e]
  exact mul_mem (Subgroup.zpow_mem _ hb n)
    (Subgroup.mem_sup_right (burnsideJ410_QOf_conj_mem hfH' hq))

theorem burnsideJ410_card_range :
    Nat.card (M.φ.comp (Subgroup.inclusion C.F1_le_H)).range = 20 := by
  set ψ := M.φ.comp (Subgroup.inclusion C.F1_le_H) with hψ
  have hker : ψ.ker = (C.F1 ⊓ ruQ M.T).subgroupOf C.F1 := by
    ext x
    have e : x ∈ ψ.ker ↔ (⟨(x : G), C.F1_le_H x.2⟩ : ruH M.T) ∈ M.φ.ker := Iff.rfl
    rw [e, M.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [hker, card_subgroupOf_of_le inf_le_left, C.card_F1_inf_Q, C.card_F1] at h
  have h' : 2 ^ 10 * Nat.card ψ.range = 2 ^ 10 * 20 := by rw [h]; norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem burnsideJ410_NH_le {n : G} (hn : n ∈ Subgroup.centralizer ({M.z} : Set G))
    (hnb : n ∈ Subgroup.normalizer (Subgroup.zpowers C.b : Set G)) :
    n ∈ Subgroup.normalizer (C.F1 : Set G) := by
  have hnH : n ∈ ruH M.T := by rw [burnsideJ410_H_eq]; exact hn
  have hbH := C.b_mem_H
  have hb1 : C.b ≠ 1 := fun h => by
    have := C.orderOf_b
    rw [h, orderOf_one] at this
    norm_num at this
  set σ := M.phiG C.b with hσ
  have hσ5 : σ ^ 5 = 1 := by rw [hσ, ← M.phiG_pow hbH, C.b_pow_five]; exact M.phiG_one47
  have hσ1 : σ ≠ 1 := M.phiG_ne_one_of_pow_five hbH C.b_pow_five hb1
  have hNB : ∀ {g : G}, g ∈ ruH M.T → (∃ k : ℕ, M.phiG (g * C.b * g⁻¹) = σ ^ k) →
      Sigma47.NormBy (M.phiG g) σ := by
    intro g hg ⟨k, hk⟩
    obtain ⟨k', hk'⟩ := Sigma47.powOfG_pow σ k hσ5
    exact ⟨k', (M.phiG_conj hg hbH).symm.trans (hk.trans hk')⟩
  set ψ := M.φ.comp (Subgroup.inclusion C.F1_le_H) with hψ
  have hψapp : ∀ f : C.F1, ψ f = M.phiG f := fun f => (M.phiG_of_mem (C.F1_le_H f.2)).symm
  let N20 : Set SigmaL2F4 := {ν | Sigma47.NormBy ν σ}
  have hsub : Set.range ψ ⊆ N20 := by
    rintro _ ⟨f, rfl⟩
    show Sigma47.NormBy (ψ f) σ
    rw [hψapp]
    exact hNB (C.F1_le_H f.2) (C.F1_norm f f.2)
  have hN20 : N20.ncard ≤ 20 := by
    have h := burnsideJ410_card_normBy σ hσ5 hσ1
    have e : N20 = ↑(Finset.univ.filter fun ν : SigmaL2F4 => Sigma47.NormBy ν σ) := by
      ext ν; simp [N20]
    rw [e, Set.ncard_coe_finset]
    exact h
  have hrange : (Set.range ψ).ncard = 20 := by
    rw [← Nat.card_coe_set_eq]
    exact burnsideJ410_card_range C
  have heq : Set.range ψ = N20 :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hrange]; exact hN20) (Set.toFinite _)
  have hn' : M.phiG n ∈ N20 := by
    show Sigma47.NormBy (M.phiG n) σ
    refine hNB hnH ?_
    have hmem : n * C.b * n⁻¹ ∈ Subgroup.zpowers C.b :=
      (Subgroup.mem_normalizer_iff.mp hnb C.b).mp (Subgroup.mem_zpowers C.b)
    obtain ⟨k, hk⟩ := exists_pow_of_mem_zpowers hmem
    exact ⟨k, by rw [← hk, M.phiG_pow hbH]⟩
  rw [← heq] at hn'
  obtain ⟨f, hf⟩ := hn'
  have hfH : (f : G) ∈ ruH M.T := C.F1_le_H f.2
  have hq : (f : G)⁻¹ * n ∈ ruQ M.T := by
    rw [← M.phiG_eq_one_iff (mul_mem (inv_mem hfH) hnH), M.phiG_mul (inv_mem hfH) hnH,
      M.phiG_inv hfH, ← hψapp f, hf, inv_mul_cancel]
  have hqn : n = (f : G) * ((f : G)⁻¹ * n) := by group
  rw [hqn]
  refine mul_mem (Subgroup.le_normalizer f.2) ?_
  rw [burnsideJ410_Q_eq] at hq
  exact burnsideJ410_Q_le_normalizer C hq

theorem burnsideJ410_u_inv_zpowers {M : RuDataM G} (C : RuDataM.Conf47 M) :
    burnsideJ410_Inv C.u (Subgroup.zpowers C.b) := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, C.u_inv_b, inv_zpow]

theorem burnsideJ410_z_cent_zpowers {M : RuDataM G} (C : RuDataM.Conf47 M) :
    burnsideJ410_Cent M.z (Subgroup.zpowers C.b) := by
  refine burnsideJ410_cent_iff_comm.mpr fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((Commute.zpow_right (show Commute M.z C.b from C.b_comm_z.symm) k)).eq

theorem burnsideJ410_u_mem_SF1 {M : RuDataM G} (C : RuDataM.Conf47 M) : C.u ∈ C.SF1 :=
  ⟨⟨C.u_mem, burnsideJ410_mem_normalizer_of_cent_or_inv (Or.inr (burnsideJ410_u_inv_zpowers C))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem burnsideJ410_z_mem_SF1 {M : RuDataM G} (C : RuDataM.Conf47 M) (hzF : M.z ∈ C.F1) :
    M.z ∈ C.SF1 :=
  ⟨⟨hzF, burnsideJ410_mem_normalizer_of_cent_or_inv (Or.inl (burnsideJ410_z_cent_zpowers C))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr C.u_comm_z.symm⟩

theorem burnsideJ410_conf_u_ne_one {M : RuDataM G} (C : RuDataM.Conf47 M) : C.u ≠ 1 := by
  intro h
  apply C.b_ne_inv
  rw [← C.u_inv_b, h]
  group

theorem burnsideJ410_Loc_of_conf
    {M : RuDataM G} (C : RuDataM.Conf47 M) : burnsideJ410_Loc M.z C.u where
  z_sq := M.z_mul_self
  u_sq := C.u_mul_self
  comm := C.u_comm_z
  z_ne := M.z_ne_one
  u_ne := C.u_ne_z
  conj_u := C.isConj_u
  conj_uz := C.isConj_t
  LS := fun _ _ hc hB hBc => burnsideJ410_LS_of_isConj M hc hB hBc

theorem burnsideJ410_Fix_of_conf {M : RuDataM G} (C : RuDataM.Conf47 M) (hzF : M.z ∈ C.F1)
    (hZ : ∀ c ∈ C.F1, (∀ f ∈ C.F1, f * c = c * f) → c ∈ Subgroup.zpowers M.z) :
    burnsideJ410_Fix M.z C.u C.F1 (Subgroup.zpowers C.b) where
  F1_le := fun f hf => by rw [← burnsideJ410_H_eq]; exact C.F1_le_H hf
  E_le := by
    unfold burnsideJ410_E
    exact sup_le (Subgroup.zpowers_le.mpr C.u_mem) (Subgroup.zpowers_le.mpr hzF)
  B5_le := Subgroup.zpowers_le.mpr C.b_mem
  B5_card := by rw [Nat.card_zpowers, C.orderOf_b]
  B5_inv := burnsideJ410_u_inv_zpowers C
  F1_card := C.card_F1
  H_card := by rw [← burnsideJ410_H_eq]; exact M.toRuData.card_H
  Z_le := hZ
  Q_le := burnsideJ410_Q_le_normalizer C
  F1_norm := burnsideJ410_F1_norm C
  NH_le := fun _ hn hnb => burnsideJ410_NH_le C hn hnb
  S5 := fun _ hw2 hzw hwQ _ _ _ h₁ h₂ h₃ => burnsideJ410_S5 M hw2 hzw hwQ h₁ h₂ h₃
end Conf

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.RuDataM
  CFSG.Quasithin.RuType.RuDataM.Conf47 CFSG.Quasithin.RuType.Sigma47 CFSG.LieType.BorelTits
  CFSG.QuasithinUnique in
attribute [local instance] CFSG.Quasithin.RuType.RuDataM.Conf47.fact_prime_five in
theorem burnsideJ410_exists_mem_F1_conj
    {M : RuDataM G} (C : RuDataM.Conf47 M) :
    ∃ w : G, w ^ 5 = 1 ∧ w ≠ 1 ∧ w * C.b = C.b * w ∧ w * C.u = C.u * w ∧
      C.j * w * C.j⁻¹ ∈ C.F1 := by
  obtain ⟨D⟩ := C.nonempty_fives
  have hzu : M.z * C.u = C.u * M.z := C.u_comm_z.symm
  have hρ5 : ∀ w : G, w * C.u = C.u * w → w ^ 5 = 1 → w ≠ 1 →
      C.rhoU w ^ 5 = 1 ∧ C.rhoU w ≠ 1 := by
    intro w hw hw5 hw1
    refine ⟨by rw [← C.rhoU_pow hw, hw5, C.rhoU_one], fun h => hw1 ?_⟩
    have h1 := C.pow_eq_one_of_rhoU hw h
    have := (pow_gcd_eq_one (a := w)).mpr ⟨hw5, h1⟩
    rwa [show Nat.gcd 5 2048 = 1 by norm_num, pow_one] at this
  have hρconj : ∀ g w : G, g * C.u = C.u * g → w * C.u = C.u * w →
      C.rhoU (g * w * g⁻¹) = C.rhoU g * C.rhoU w * (C.rhoU g)⁻¹ := by
    intro g w hg hw
    unfold rhoU
    rw [show C.j * (g * w * g⁻¹) * C.j⁻¹ =
        (C.j * g * C.j⁻¹) * (C.j * w * C.j⁻¹) * (C.j * g * C.j⁻¹)⁻¹ by group,
      M.phiG_mul (mul_mem (C.jconj_mem_H hg) (C.jconj_mem_H hw)) (inv_mem (C.jconj_mem_H hg)),
      M.phiG_mul (C.jconj_mem_H hg) (C.jconj_mem_H hw), M.phiG_inv (C.jconj_mem_H hg)]
  have hρz : C.rhoU M.z = M.phiG C.u := by unfold rhoU; rw [C.j_conj_z]
  obtain ⟨d, hd⟩ : ∃ d, d = M.phiG C.u := ⟨_, rfl⟩
  have hd2 : d * d = 1 := by
    rw [hd, ← M.phiG_mul C.u_mem_H C.u_mem_H, C.u_mul_self]
    exact M.phiG_one47
  have hd1 : d ≠ 1 := by rw [hd]; exact C.phiG_u_ne_one
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 = C.j⁻¹ * C.b * C.j := ⟨_, rfl⟩
  have hjw0 : C.j * w0 * C.j⁻¹ = C.b := by rw [hw0]; group
  have hw0u : w0 * C.u = C.u * w0 := by
    have hbz := C.b_comm_z
    calc w0 * C.u = C.j⁻¹ * (C.b * (C.j * C.u * C.j⁻¹)) * C.j := by rw [hw0]; group
      _ = C.j⁻¹ * (C.b * M.z) * C.j := by rw [C.j_conj_u]
      _ = C.j⁻¹ * (M.z * C.b) * C.j := by rw [hbz]
      _ = C.j⁻¹ * (C.j * C.u * C.j⁻¹ * C.b) * C.j := by rw [C.j_conj_u]
      _ = C.u * w0 := by rw [hw0]; group
  have hw05 : w0 ^ 5 = 1 := by
    rw [hw0, show C.j⁻¹ * C.b * C.j = C.j⁻¹ * C.b * C.j⁻¹⁻¹ by group, conj_pow, C.b_pow_five]
    group
  have hw01 : w0 ≠ 1 := fun h => C.b_ne_inv (by
    have : C.b = 1 := by rw [← hjw0, h]; group
    rw [this, inv_one])
  have hρw0 : C.rhoU w0 = M.phiG C.b := by unfold rhoU; rw [hjw0]
  obtain ⟨h15, h11⟩ := hρ5 D.bu D.bu_comm D.bu_pow D.bu_ne
  obtain ⟨h25, h21⟩ := hρ5 D.bu' D.bu'_comm D.bu'_pow D.bu'_ne
  obtain ⟨h05, h01⟩ := hρ5 w0 hw0u hw05 hw01
  have hNBu : NormBy d (C.rhoU D.bu) := by
    refine ⟨4, ?_⟩
    show d * C.rhoU D.bu * d⁻¹ = C.rhoU D.bu ^ 4
    rw [hd, ← hρz, ← hρconj M.z D.bu hzu D.bu_comm, D.z_inv_bu,
      show D.bu⁻¹ = D.bu ^ 4 by
        calc D.bu⁻¹ = D.bu ^ 5 * D.bu⁻¹ := by rw [D.bu_pow, one_mul]
          _ = D.bu ^ 4 := by group,
      C.rhoU_pow D.bu_comm]
  have hNBu' : NormBy d (C.rhoU D.bu') := by
    obtain ⟨k, hk⟩ := D.z_norm_bu'
    obtain ⟨k', hk'⟩ := powOfG_pow (C.rhoU D.bu') k h25
    refine ⟨k', ?_⟩
    rw [hd, ← hρz, ← hρconj M.z D.bu' hzu D.bu'_comm, hk, C.rhoU_pow D.bu'_comm, hk']
  have hNb : NormBy d (M.phiG C.b) := by
    refine ⟨4, ?_⟩
    show d * M.phiG C.b * d⁻¹ = M.phiG C.b ^ 4
    rw [hd, ← M.phiG_conj C.u_mem_H C.b_mem_H, C.u_inv_b,
      show C.b⁻¹ = C.b ^ 4 by
        calc C.b⁻¹ = C.b ^ 5 * C.b⁻¹ := by rw [C.b_pow_five, one_mul]
          _ = C.b ^ 4 := by group,
      M.phiG_pow C.b_mem_H]
  have hNw0 : NormBy d (C.rhoU w0) := by rw [hρw0]; exact hNb
  rcases powOf_of_two_classes hd2 hd1 h15 h11 hNBu h25 h21 hNBu' D.not_powOfG_bu h05 h01 hNw0
    with h | h
  ·
    have h' := powOfG_symm h15 h01 h
    rw [hρw0] at h'
    exact ⟨D.bu, D.bu_pow, D.bu_ne, D.bu_comm_b, D.bu_comm,
      C.mem_F1_of_powOfG (C.jconj_mem_H D.bu_comm)
      (by rw [conj_pow, D.bu_pow]; group) h'⟩
  ·
    exfalso
    have h' := powOfG_symm h25 h01 h
    rw [hρw0] at h'
    obtain ⟨x, hx⟩ : ∃ x, x = C.j * D.bu' * C.j⁻¹ := ⟨_, rfl⟩
    have hxH : x ∈ ruH M.T := by rw [hx]; exact C.jconj_mem_H D.bu'_comm
    have hx5 : x ^ 5 = 1 := by rw [hx, conj_pow, D.bu'_pow]; group
    have hx1 : x ≠ 1 := by
      intro h1
      apply D.bu'_ne
      calc D.bu' = C.j⁻¹ * x * C.j := by rw [hx]; group
        _ = 1 := by rw [h1]; group
    have hxo : orderOf x = 5 := orderOf_eq_prime hx5 hx1
    have hxF : x ∈ C.F1 := C.mem_F1_of_powOfG hxH hx5 (by rw [hx]; exact h')
    have hux : ∃ k : ℕ, C.u * x * C.u⁻¹ = x ^ k := by
      obtain ⟨k, hk⟩ := D.z_norm_bu'
      refine ⟨k, ?_⟩
      rw [← C.j_conj_z, hx, conj_pow, ← hk]
      group
    have hxu : C.u * x * C.u⁻¹ = x⁻¹ :=
      inv_of_normalizes_zpowers C.u_mul_self hx5 hux (fun h => M.not_comm_of_pow_five hxH hx5
        hx1 C.u_mem_H C.u_mul_self C.phiG_u_ne_one h.symm)
    have hzx : M.z * x = x * M.z := M.Z_comm_H M.z_mem_Z hxH
    have htx : C.t * x * C.t⁻¹ = x⁻¹ := by
      show C.u * M.z * x * (C.u * M.z)⁻¹ = x⁻¹
      calc C.u * M.z * x * (C.u * M.z)⁻¹ = C.u * (M.z * x) * M.z⁻¹ * C.u⁻¹ := by group
        _ = C.u * x * C.u⁻¹ := by rw [hzx]; group
        _ = x⁻¹ := hxu
    have hK := card_P5_inf_centralizer hxH hxo C.isConj_t C.t_mul_self htx
    obtain ⟨c, -, hc5, -, hcgen⟩ := exists_gen_of_card_five hK
    obtain ⟨g, hgF, hgu, kk, hkk⟩ := C.exists_conj_of_norm hxF hxo hux
    have hgH : g ∈ ruH M.T := C.F1_le_H hgF
    have hgz : g * M.z = M.z * g := (M.Z_comm_H M.z_mem_Z hgH).symm
    have hgt : g * C.t = C.t * g := by
      show g * (C.u * M.z) = C.u * M.z * g
      calc g * (C.u * M.z) = (g * C.u) * M.z := by group
        _ = C.u * (g * M.z) := by rw [hgu]; group
        _ = C.u * M.z * g := by rw [hgz]; group
    have hbtt := D.bt_comm
    obtain ⟨w1, hw1⟩ : ∃ w1, w1 = C.j * D.bt * C.j⁻¹ := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2, w2 = g * D.bt * g⁻¹ := ⟨_, rfl⟩
    have hw1t : w1 * C.t = C.t * w1 := by
      have hjt := C.j_comm_t
      have hjit : C.j⁻¹ * C.t = C.t * C.j⁻¹ :=
        (Commute.inv_left (show Commute C.j C.t from hjt)).eq
      calc w1 * C.t = C.j * D.bt * (C.j⁻¹ * C.t) := by rw [hw1]; group
        _ = C.j * (D.bt * C.t) * C.j⁻¹ := by rw [hjit]; group
        _ = (C.j * C.t) * D.bt * C.j⁻¹ := by rw [hbtt]; group
        _ = C.t * w1 := by rw [hjt, hw1]; group
    have hw2t : w2 * C.t = C.t * w2 := by
      have hgit : g⁻¹ * C.t = C.t * g⁻¹ := (Commute.inv_left (show Commute g C.t from hgt)).eq
      calc w2 * C.t = g * D.bt * (g⁻¹ * C.t) := by rw [hw2]; group
        _ = g * (D.bt * C.t) * g⁻¹ := by rw [hgit]; group
        _ = (g * C.t) * D.bt * g⁻¹ := by rw [hbtt]; group
        _ = C.t * w2 := by rw [hgt, hw2]; group
    have hw1x : w1 * x = x * w1 := by
      rw [hw1, hx]
      calc C.j * D.bt * C.j⁻¹ * (C.j * D.bu' * C.j⁻¹) = C.j * (D.bt * D.bu') * C.j⁻¹ := by
            group
        _ = C.j * (D.bu' * D.bt) * C.j⁻¹ := by rw [D.bu'_comm_bt]
        _ = C.j * D.bu' * C.j⁻¹ * (C.j * D.bt * C.j⁻¹) := by group
    have hw2x : w2 * x = x * w2 := by
      have hc : Commute w2 (g * C.b * g⁻¹) := by
        show w2 * (g * C.b * g⁻¹) = g * C.b * g⁻¹ * w2
        rw [hw2]
        calc g * D.bt * g⁻¹ * (g * C.b * g⁻¹) = g * (D.bt * C.b) * g⁻¹ := by group
          _ = g * (C.b * D.bt) * g⁻¹ := by rw [D.b_comm_bt]
          _ = g * C.b * g⁻¹ * (g * D.bt * g⁻¹) := by group
      rw [← hkk]
      exact (hc.pow_right kk).eq
    have hw15 : w1 ^ 5 = 1 := by rw [hw1, conj_pow, D.bt_pow]; group
    have hw25 : w2 ^ 5 = 1 := by rw [hw2, conj_pow, D.bt_pow]; group
    have hw11 : w1 ≠ 1 := by
      intro h1
      apply D.bt_ne
      calc D.bt = C.j⁻¹ * w1 * C.j := by rw [hw1]; group
        _ = 1 := by rw [h1]; group
    have hw21 : w2 ≠ 1 := by
      intro h1
      apply D.bt_ne
      calc D.bt = g⁻¹ * w2 * g := by rw [hw2]; group
        _ = 1 := by rw [h1]; group
    have hw1K : w1 ∈ P5 x ⊓ Subgroup.centralizer ({C.t} : Set G) :=
      ⟨mem_P5_of_pow_five hxH hxo (mem_G5.mpr hw1x) hw15,
        Subgroup.mem_centralizer_singleton_iff.mpr hw1t⟩
    have hw2K : w2 ∈ P5 x ⊓ Subgroup.centralizer ({C.t} : Set G) :=
      ⟨mem_P5_of_pow_five hxH hxo (mem_G5.mpr hw2x) hw25,
        Subgroup.mem_centralizer_singleton_iff.mpr hw2t⟩
    obtain ⟨a1, ha1⟩ := hcgen w1 hw1K
    obtain ⟨a2, ha2⟩ := hcgen w2 hw2K
    obtain ⟨a3, ha3⟩ := exists_pow_pow_eq hc5 (show c ^ a1 ≠ 1 by rw [ha1]; exact hw11)
    rw [ha1] at ha3
    have hw12 : w1 ^ (a3 * a2) = w2 := by rw [pow_mul, ha3, ha2]
    have hgct : D.ct * g * D.ct⁻¹ ∈ C.F1 := by
      have hτQ : D.τ⁻¹ ∈ ruQ M.T := inv_mem D.τ_mem.1
      have h1 : D.τ⁻¹ * g * D.τ⁻¹⁻¹ ∈ C.F1 := C.conj_mem_F1_of_mem_Q hτQ hgF
      have hτu : D.τ⁻¹ * C.t * D.τ = C.u := by
        show D.τ⁻¹ * (C.u * M.z) * D.τ = C.u
        rw [← D.τ_conj]
        group
      have h2 : (D.τ⁻¹ * g * D.τ⁻¹⁻¹) * C.u = C.u * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) := by
        calc (D.τ⁻¹ * g * D.τ⁻¹⁻¹) * C.u = D.τ⁻¹ * g * D.τ⁻¹⁻¹ * (D.τ⁻¹ * C.t * D.τ) := by
              rw [hτu]
          _ = D.τ⁻¹ * (g * C.t) * D.τ := by group
          _ = D.τ⁻¹ * (C.t * g) * D.τ := by rw [hgt]
          _ = (D.τ⁻¹ * C.t * D.τ) * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) := by group
          _ = C.u * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) := by rw [hτu]
      have h3 := C.conj_mem_F1 _ h1 h2
      have e : D.ct * g * D.ct⁻¹ = C.j * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) * C.j⁻¹ := by
        unfold Fives.ct
        group
      rw [e]
      exact h3
    have hgctH : D.ct * g * D.ct⁻¹ ∈ ruH M.T := C.F1_le_H hgct
    have hgN : NormBy (D.rhoT g) (M.phiG C.b) := by
      obtain ⟨k, hk⟩ := C.F1_norm _ hgct
      rw [M.phiG_conj hgctH C.b_mem_H] at hk
      have hk1 : D.rhoT g * M.phiG C.b * (D.rhoT g)⁻¹ = M.phiG C.b ^ k := hk
      obtain ⟨k', hk'⟩ := powOfG_pow (M.phiG C.b) k
        (by rw [← M.phiG_pow C.b_mem_H, C.b_pow_five]; exact M.phiG_one47)
      exact ⟨k', by rw [hk1, hk']⟩
    have hgd : D.rhoT g * d = d * D.rhoT g := by
      have hcz : (D.ct * g * D.ct⁻¹) * C.u = C.u * (D.ct * g * D.ct⁻¹) := by
        rw [← D.ct_conj_z]
        calc D.ct * g * D.ct⁻¹ * (D.ct * M.z * D.ct⁻¹) = D.ct * (g * M.z) * D.ct⁻¹ := by group
          _ = D.ct * (M.z * g) * D.ct⁻¹ := by rw [hgz]
          _ = D.ct * M.z * D.ct⁻¹ * (D.ct * g * D.ct⁻¹) := by group
      show M.phiG (D.ct * g * D.ct⁻¹) * d = d * M.phiG (D.ct * g * D.ct⁻¹)
      rw [hd, ← M.phiG_mul hgctH C.u_mem_H, ← M.phiG_mul C.u_mem_H hgctH, hcz]
    obtain ⟨hσ5, hσ1⟩ := D.rhoT_bt_props
    have hσN : NormBy d (D.rhoT D.bt) := by
      refine ⟨4, ?_⟩
      show d * D.rhoT D.bt * d⁻¹ = D.rhoT D.bt ^ 4
      rw [hd, ← D.rhoT_z, ← D.rhoT_conj C.z_comm_t D.bt_comm, D.z_inv_bt,
        show D.bt⁻¹ = D.bt ^ 4 by
          calc D.bt⁻¹ = D.bt ^ 5 * D.bt⁻¹ := by rw [D.bt_pow, one_mul]
            _ = D.bt ^ 4 := by group,
        D.rhoT_pow D.bt_comm]
    have hb5 : M.phiG C.b ^ 5 = 1 := by
      rw [← M.phiG_pow C.b_mem_H, C.b_pow_five]; exact M.phiG_one47
    have hb1 : M.phiG C.b ≠ 1 :=
      M.phiG_ne_one_of_pow_five C.b_mem_H C.b_pow_five (fun h => by
        have := C.orderOf_b
        rw [h, orderOf_one] at this
        norm_num at this)
    have hgσ : NormBy (D.rhoT g) (D.rhoT D.bt) :=
      normBy_of_normBy_of_comm hd2 hd1 hb5 hb1 hNb hσ5 hσ1 hσN hgd hgN
    have hρw2 : D.rhoT w2 = D.rhoT g * D.rhoT D.bt * (D.rhoT g)⁻¹ := by
      rw [hw2, D.rhoT_conj hgt D.bt_comm]
    have hP1 : PowOfG (D.rhoT D.bt) (D.rhoT w2) := by
      obtain ⟨k, hk⟩ := hgσ
      exact ⟨k, by rw [hρw2, hk]⟩
    have hw1ρ5 : D.rhoT w1 ^ 5 = 1 := by rw [← D.rhoT_pow hw1t, hw15, D.rhoT_one]
    have hP2 : PowOfG (D.rhoT w1) (D.rhoT w2) := by
      rw [← hw12, D.rhoT_pow hw1t]
      exact powOfG_pow _ _ hw1ρ5
    have hρw2_1 : D.rhoT w2 ≠ 1 := by
      intro h1
      have hQ := (D.rhoT_eq_one_iff hw2t).mp h1
      have h2 := M.pow_eq_one_of_mem_Q hQ
      rw [conj_pow] at h2
      apply hw21
      have h3 : w2 ^ 2048 = 1 := by
        calc w2 ^ 2048 = D.ct⁻¹ * (D.ct * w2 ^ 2048 * D.ct⁻¹) * D.ct := by group
          _ = 1 := by rw [h2]; group
      have := (pow_gcd_eq_one (a := w2)).mpr ⟨hw25, h3⟩
      rwa [show Nat.gcd 5 2048 = 1 by norm_num, pow_one] at this
    have hP3 := powOfG_symm hw1ρ5 hρw2_1 hP2
    have hfin := powOfG_trans hσ5 hP1 hP3
    rw [hw1] at hfin
    exact D.not_powOfG_bt hfin

theorem burnsideJ410_exists_r
    {M : RuDataM G} (C : RuDataM.Conf47 M) :
    ∃ r ∈ Subgroup.centralizer ({M.z} : Set G),
      r ∈ Subgroup.normalizer (Subgroup.zpowers C.b : Set G) ∧ r * C.u * r⁻¹ = C.u * M.z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbH := C.b_mem_H
  have hb5 := C.orderOf_b
  set R := RuDataM.RB5 hbH hb5 with hR
  set K := M.NHB C.b with hK
  have hRK : R ≤ K := RuDataM.RB5_le_NHB hbH hb5
  have hRp : IsPGroup 2 R := RuDataM.RB5_isPGroup hbH hb5
  have hRc : Nat.card R = 32 := RuDataM.card_RB5 hbH hb5
  have hidx : ¬ 2 ∣ R.relIndex K := by
    have h1 := relIndex_mul_card_of_le hRK
    have h2 : Nat.card K ∣ Nat.card (Subgroup.normalizer (Subgroup.zpowers C.b : Set G)) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [RuDataM.card_normalizer_B5 hbH hb5] at h2
    intro hd
    have h64 : 64 ∣ Nat.card K := by
      obtain ⟨s, hs⟩ := hd
      exact ⟨s, by rw [← h1, hRc, hs]; ring⟩
    have := Nat.dvd_trans h64 h2
    norm_num at this
  have hSF1K : C.SF1 ≤ K := fun x hx => ⟨C.F1_le_H hx.1.1, hx.1.2⟩
  obtain ⟨g, hgK, hSg⟩ := burnsideJ410_exists_conj_le_sylow hRK hRp hidx hSF1K C.isPGroup_SF1
  set S := CFSG.conjugate R g with hS
  have hSK : S ≤ K := by
    have h := CFSG.ASVolI.RuChoice.fx_conjugate_mono g hRK
    rwa [CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer hgK)] at h
  have hScard : Nat.card S = 32 := by
    rw [hS, CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hRc
  have hidx2 : C.SF1.relIndex S = 2 := by
    have h := relIndex_mul_card_of_le hSg
    rw [C.card_SF1, hScard] at h
    omega
  have hnorm : (C.SF1.subgroupOf S).Normal :=
    Subgroup.normal_of_index_eq_two (by rw [← Subgroup.relIndex]; exact hidx2)
  have hcons : ∀ s ∈ S, ∀ x ∈ C.SF1, s * x * s⁻¹ ∈ C.SF1 := by
    intro s hs x hx
    have h := hnorm.conj_mem ⟨x, hSg hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨s, hs⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hgH : g ∈ ruH M.T := hgK.1
  have hnc : ∃ s ∈ S, s * C.u * s⁻¹ ≠ C.u := by
    by_contra hcon
    push Not at hcon
    have huS : C.u ∈ S := hSg (burnsideJ410_u_mem_SF1 C)
    have hwR : g * C.u * g⁻¹ ∈ R := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp huS
    have hwc : ∀ r ∈ R, (g * C.u * g⁻¹) * r = r * (g * C.u * g⁻¹) := by
      intro r hr
      have hs : g⁻¹ * r * g ∈ S := by
        rw [hS, CFSG.ASVolI.RuChoice.fx_mem_conjugate]
        have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
        rw [e]; exact hr
      have h1 := hcon _ hs
      have h2 : (g⁻¹ * r * g) * C.u = C.u * (g⁻¹ * r * g) := by
        calc (g⁻¹ * r * g) * C.u = ((g⁻¹ * r * g) * C.u * (g⁻¹ * r * g)⁻¹) * (g⁻¹ * r * g) := by
              group
          _ = C.u * (g⁻¹ * r * g) := by rw [h1]
      calc (g * C.u * g⁻¹) * r = g * (C.u * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * C.u) * g⁻¹ := by rw [h2]
        _ = r * (g * C.u * g⁻¹) := by group
    have hw2 : (g * C.u * g⁻¹) * (g * C.u * g⁻¹) = 1 := by
      calc (g * C.u * g⁻¹) * (g * C.u * g⁻¹) = g * (C.u * C.u) * g⁻¹ := by group
        _ = 1 := by rw [C.u_mul_self]; group
    have hw1 : g * C.u * g⁻¹ ≠ 1 := by
      intro h
      apply burnsideJ410_conf_u_ne_one C
      calc C.u = g⁻¹ * (g * C.u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hwz := RuDataM.eq_z_of_central_RB5 hbH hb5 hwR hw2 hw1 hwc
    apply C.u_ne_z
    have hgz : M.z * g = g * M.z := M.Z_comm_H M.z_mem_Z hgH
    calc C.u = g⁻¹ * (g * C.u * g⁻¹) * g := by group
      _ = g⁻¹ * M.z * g := by rw [hwz]
      _ = g⁻¹ * (M.z * g) := by group
      _ = g⁻¹ * (g * M.z) := by rw [hgz]
      _ = M.z := by group
  obtain ⟨r, hrS, hru⟩ := hnc
  have hrK : r ∈ K := hSK hrS
  have hrC : r ∈ Subgroup.centralizer ({M.z} : Set G) := by
    rw [← burnsideJ410_H_eq]; exact hrK.1
  refine ⟨r, hrC, hrK.2, ?_⟩
  have hv := hcons r hrS C.u (burnsideJ410_u_mem_SF1 C)
  have hv2 : (r * C.u * r⁻¹) * (r * C.u * r⁻¹) = 1 := by
    calc (r * C.u * r⁻¹) * (r * C.u * r⁻¹) = r * (C.u * C.u) * r⁻¹ := by group
      _ = 1 := by rw [C.u_mul_self]; group
  obtain ⟨p, hp, hpe⟩ := C.exists_iEl_eq hv
  have hi := C.iEl_inv p hp (by rw [hpe]; exact hv2)
  rw [hpe] at hi
  rcases hi with h | h | h | h
  · exfalso
    apply burnsideJ410_conf_u_ne_one C
    calc C.u = r⁻¹ * (r * C.u * r⁻¹) * r := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply C.u_ne_z
    have hrz : M.z * r = r * M.z := M.Z_comm_H M.z_mem_Z hrK.1
    calc C.u = r⁻¹ * (r * C.u * r⁻¹) * r := by group
      _ = r⁻¹ * M.z * r := by rw [h]
      _ = r⁻¹ * (M.z * r) := by group
      _ = r⁻¹ * (r * M.z) := by rw [hrz]
      _ = M.z := by group
  · exact absurd h hru
  · exact h

theorem burnsideJ410_Fix2_of_conf
    {M : RuDataM G} (C : RuDataM.Conf47 M) (hzF : M.z ∈ C.F1)
    (hL : burnsideJ410_Loc M.z C.u) :
    burnsideJ410_Fix2 M.z C.u C.F1 (Subgroup.zpowers C.b) C.SF1 where
  I0_le := fun x hx => hx.1
  I0_card := C.card_SF1
  NF1_card := C.card_NF1
  I0_inv := fun i hi hi2 => by
    obtain ⟨p, hp, rfl⟩ := C.exists_iEl_eq hi
    exact C.iEl_inv p hp hi2
  E_le_I0 := by
    unfold burnsideJ410_E
    exact sup_le (Subgroup.zpowers_le.mpr (burnsideJ410_u_mem_SF1 C))
      (Subgroup.zpowers_le.mpr (burnsideJ410_z_mem_SF1 C hzF))
  Fe := C.conj_u_ne
  J := by
    refine ⟨C.j, ?_, C.conj_mem_F1, ?_⟩
    · have h := C.j_conj_z
      rw [C.j_inv] at h ⊢
      exact h
    · obtain ⟨w, hw5, hw1, hwb, hwu, hjw⟩ := burnsideJ410_exists_mem_F1_conj C
      refine ⟨w, ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr hwu⟩, hw1, hjw⟩
      have hB5 : Nat.card (Subgroup.zpowers C.b) = 5 := by rw [Nat.card_zpowers, C.orderOf_b]
      have hBz : Subgroup.zpowers C.b ≤ Subgroup.centralizer ({M.z} : Set G) := fun y hy => by
        rw [← burnsideJ410_H_eq]
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact zpow_mem C.b_mem_H k
      have hLS := burnsideJ410_LS_of_isConj M (IsConj.refl M.z) hB5 hBz
      have hwP : w ∈ PFstar (Subgroup.zpowers C.b) := by
        refine hLS.mem_P w (fun y hy => ?_) hw5
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_right (show Commute w C.b from hwb) k).eq
      show w ∈ pCoreOf 5 (Subgroup.normalizer ((Subgroup.zpowers C.b : Subgroup G) : Set G))
      rw [hLS.pcore]
      exact hwP
  r := by
    obtain ⟨r, hrC, hrN, hru⟩ := burnsideJ410_exists_r C
    refine ⟨r, hrC, hrN, ?_, hru⟩
    have hrz : r * M.z * r⁻¹ = M.z := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hrC
      calc r * M.z * r⁻¹ = (M.z * r) * r⁻¹ := by rw [h]
        _ = M.z := by group
    refine CFSG.ASVolI.RuChoice.mem_normalizer fun x hx => ?_
    rw [burnsideJ410_mem_E_iff hL] at hx ⊢
    rcases hx with h | h | h | h
    · left; rw [h]; group
    · right; left; rw [h]; exact hrz
    · right; right; right; rw [h]; exact hru
    · right; right; left
      rw [h]
      calc r * (C.u * M.z) * r⁻¹ = (r * C.u * r⁻¹) * (r * M.z * r⁻¹) := by group
        _ = (C.u * M.z) * M.z := by rw [hru, hrz]
        _ = C.u := by rw [mul_assoc, M.z_mul_self, mul_one]

theorem burnsideJ410_conf_hexagon
    {M : RuDataM G} (C : RuDataM.Conf47 M) (hzF : M.z ∈ C.F1)
    (hZ : ∀ c ∈ C.F1, (∀ f ∈ C.F1, f * c = c * f) → c ∈ Subgroup.zpowers M.z) :
    Nonempty (EgonGraph (EsetRu C.F1 M.z C.u) M.z C.u ≃g SimpleGraph.cycleGraph 6) :=
  burnsideJ410_hexagon (burnsideJ410_Loc_of_conf C) (burnsideJ410_Fix_of_conf C hzF hZ)
    (burnsideJ410_Fix2_of_conf C hzF (burnsideJ410_Loc_of_conf C))

theorem burnsideJ410_E_conj (g z u : G) :
    burnsideJ410_E (g * z * g⁻¹) (g * u * g⁻¹) = CFSG.conjugate (burnsideJ410_E z u) g⁻¹ := by
  unfold burnsideJ410_E
  rw [CFSG.ASVolI.RuChoice.fx_conjugate_sup, CFSG.ASVolI.RuChoice.fx_conjugate_zpowers,
    CFSG.ASVolI.RuChoice.fx_conjugate_zpowers, inv_inv]

theorem burnsideJ410_Fset_map (g : G) {F1 : Subgroup G} {z v : G} {E : Subgroup G}
    (h : E ∈ FsetRu F1 z v) :
    CFSG.conjugate E g⁻¹ ∈ FsetRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * v * g⁻¹) := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  · rw [← hk]; group
  · rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate, CFSG.ASVolI.RuChoice.fx_conjugate_conjugate]
    congr 1
    group

theorem burnsideJ410_Es_map (g : G) {F1 : Subgroup G} {z u : G} {E : Subgroup G}
    (h : E ∈ EsetRu F1 z u) :
    CFSG.conjugate E g⁻¹ ∈ EsetRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * u * g⁻¹) := by
  have key : ∀ v : G, E ∈ EvRu F1 z u v →
      CFSG.conjugate E g⁻¹ ∈ EvRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * u * g⁻¹)
        (g * v * g⁻¹) := by
    intro v hv
    refine ⟨burnsideJ410_Fset_map g hv.1, ?_⟩
    have h1 := CFSG.ASVolI.RuChoice.fx_conjugate_mono g⁻¹ hv.2
    have h2 := burnsideJ410_E_conj g z u
    unfold burnsideJ410_E at h2
    rw [h2]
    exact h1
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (key z h))
  · exact Or.inl (Or.inr (key u h))
  · have h1 := key (u * z) h
    have e : g * (u * z) * g⁻¹ = (g * u * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e] at h1
    exact Or.inr h1

theorem burnsideJ410_R_map (g : G) {z u : G} {E₁ E₂ : Subgroup G}
    (h : burnsideJ410_R z u E₁ E₂) :
    burnsideJ410_R (g * z * g⁻¹) (g * u * g⁻¹) (CFSG.conjugate E₁ g⁻¹)
      (CFSG.conjugate E₂ g⁻¹) := by
  obtain ⟨B₁, B₂, h1, h2, c1, c2, n1, n2, hc⟩ := h
  have hE := burnsideJ410_E_conj g z u
  refine ⟨CFSG.conjugate B₁ g⁻¹, CFSG.conjugate B₂ g⁻¹,
    CFSG.ASVolI.RuChoice.fx_conjugate_mono g⁻¹ h1, CFSG.ASVolI.RuChoice.fx_conjugate_mono g⁻¹ h2,
    ?_, ?_, ?_, ?_, (burnsideJ410_conj_comm_bot g⁻¹).mpr hc⟩
  · rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact c1
  · rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact c2
  · rw [hE, CFSG.ASVolI.RuChoice.fx_normalizer_conjugate]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_mono g⁻¹ n1
  · rw [hE, CFSG.ASVolI.RuChoice.fx_normalizer_conjugate]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_mono g⁻¹ n2

theorem burnsideJ410_Egon_transport (g : G) (F1 : Subgroup G) (z u : G) :
    Nonempty (EgonGraph (EsetRu F1 z u) z u ≃g
      EgonGraph (EsetRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * u * g⁻¹)) (g * z * g⁻¹)
        (g * u * g⁻¹)) := by
  have fwd : ∀ E : Subgroup G, E ∈ EsetRu F1 z u →
      CFSG.conjugate E g⁻¹ ∈ EsetRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * u * g⁻¹) :=
    fun E h => burnsideJ410_Es_map g h
  have bwd : ∀ E : Subgroup G,
      CFSG.conjugate E g⁻¹ ∈ EsetRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * u * g⁻¹) →
        E ∈ EsetRu F1 z u := by
    intro E h
    have h2 := burnsideJ410_Es_map g⁻¹ h
    simp only [inv_inv, burnsideJ410_conj_inv_conj] at h2
    have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have e2 : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e1, e2] at h2
    exact h2
  let κ : Subgroup G ≃ Subgroup G :=
    { toFun := fun E => CFSG.conjugate E g⁻¹
      invFun := fun E => CFSG.conjugate E g
      left_inv := fun E => burnsideJ410_conj_inv_conj E g
      right_inv := fun E => burnsideJ410_conj_conj_inv E g }
  have hmem : ∀ E : Subgroup G, E ∈ EsetRu F1 z u ↔
      κ E ∈ EsetRu (CFSG.conjugate F1 g⁻¹) (g * z * g⁻¹) (g * u * g⁻¹) :=
    fun E => ⟨fwd E, bwd E⟩
  refine ⟨{ toEquiv := Equiv.subtypeEquiv κ hmem, map_rel_iff' := ?_ }⟩
  intro E₁ E₂
  show (EgonGraph _ _ _).Adj ⟨κ E₁.1, _⟩ ⟨κ E₂.1, _⟩ ↔ _
  rw [burnsideJ410_adj_iff, burnsideJ410_adj_iff]
  constructor
  · rintro ⟨hne, hR⟩
    refine ⟨fun h => hne (by simp only [κ, Equiv.coe_fn_mk]; rw [h]), ?_⟩
    have h2 := burnsideJ410_R_map g⁻¹ hR
    simp only [κ, Equiv.coe_fn_mk, inv_inv, burnsideJ410_conj_inv_conj] at h2
    have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have e2 : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e1, e2] at h2
    exact h2
  · rintro ⟨hne, hR⟩
    exact ⟨fun h => hne (burnsideJ410_conj_inj g⁻¹ h), burnsideJ410_R_map g hR⟩

theorem burnsideJ410_Egon_transport' (g : G) {F1 F1' : Subgroup G} {z z' u u' : G}
    (hF : CFSG.conjugate F1 g⁻¹ = F1') (hz : g * z * g⁻¹ = z') (hu : g * u * g⁻¹ = u') :
    Nonempty (EgonGraph (EsetRu F1 z u) z u ≃g EgonGraph (EsetRu F1' z' u') z' u') := by
  subst hF hz hu
  exact burnsideJ410_Egon_transport g F1 z u

theorem burnsideJ410_Egon_congr {Es Es' : Set (Subgroup G)} (h : Es = Es') {z u z' u' : G}
    (hE : burnsideJ410_E z u = burnsideJ410_E z' u') :
    Nonempty (EgonGraph Es z u ≃g EgonGraph Es' z' u') := by
  subst h
  refine ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩
  intro a b
  show (EgonGraph _ z' u').Adj a b ↔ (EgonGraph _ z u).Adj a b
  rw [burnsideJ410_adj_iff, burnsideJ410_adj_iff]
  have : burnsideJ410_R z u = burnsideJ410_R z' u' := by
    funext E₁ E₂
    unfold burnsideJ410_R
    rw [hE]
  rw [this]

theorem burnsideJ410_E_swap (z u : G) :
    burnsideJ410_E z (u * z) = burnsideJ410_E z u := by
  unfold burnsideJ410_E
  apply le_antisymm
  · exact sup_le (Subgroup.zpowers_le.mpr (mul_mem (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers u)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))))
      le_sup_right
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) le_sup_right
    have h : (u * z) * z⁻¹ ∈ Subgroup.zpowers (u * z) ⊔ Subgroup.zpowers z :=
      mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
    rwa [mul_inv_cancel_right] at h

theorem burnsideJ410_Es_swap {z : G} (hz : z * z = 1) (F1 : Subgroup G) (u : G) :
    EsetRu F1 z (u * z) = EsetRu F1 z u := by
  have hE := burnsideJ410_E_swap z u
  unfold burnsideJ410_E at hE
  have huzz : u * z * z = u := by rw [mul_assoc, hz, mul_one]
  have hEv : ∀ v : G, EvRu F1 z (u * z) v = EvRu F1 z u v := by
    intro v
    unfold EvRu
    rw [hE]
  unfold EsetRu
  rw [hEv, hEv, hEv, huzz]
  ext E
  simp only [Set.mem_union]
  tauto

theorem burnsideJ410_Egon_swap {z : G} (hz : z * z = 1) (F1 : Subgroup G) (u : G) :
    Nonempty (EgonGraph (EsetRu F1 z (u * z)) z (u * z) ≃g EgonGraph (EsetRu F1 z u) z u) :=
  burnsideJ410_Egon_congr (burnsideJ410_Es_swap hz F1 u) (burnsideJ410_E_swap z u)

open CFSG.Quasithin.RuType.Sigma47 in
theorem burnsideJ410_normalize
    {M : RuDataM G} (C : RuDataM.Conf47 M) {u' : G} {B5' : Subgroup G}
    (hu'F : u' ∈ C.F1) (hu'2 : u' * u' = 1) (hB5F : B5' ≤ C.F1) (hB5c : Nat.card B5' = 5)
    (hinv : ∀ x ∈ B5', u' * x * u'⁻¹ = x⁻¹) :
    ∃ h ∈ C.F1, h * u' * h⁻¹ = C.u ∨ h * u' * h⁻¹ = C.u * M.z := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxB, hx5, hx1, -⟩ := exists_gen_of_card_five hB5c
  have hxF : x ∈ C.F1 := hB5F hxB
  have hxo : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  obtain ⟨f, hfF, hfx⟩ := exists_conj_zpowers C.not_dvd_card_F1 C.b_mem hxF C.orderOf_b hxo
  obtain ⟨m, hm⟩ := exists_pow_of_mem_zpowers hfx
  have hxm : f⁻¹ * x * f = C.b ^ m := by
    rw [← hm, conj_pow]
    group
  have hbm1 : C.b ^ m ≠ 1 := by
    intro h
    apply hx1
    calc x = f * (f⁻¹ * x * f) * f⁻¹ := by group
      _ = 1 := by rw [hxm, h]; group
  set u'' := f⁻¹ * u' * f with hu''def
  have hu''bm : u'' * C.b ^ m * u''⁻¹ = (C.b ^ m)⁻¹ := by
    rw [← hxm]
    have h := hinv x hxB
    calc u'' * (f⁻¹ * x * f) * u''⁻¹ = f⁻¹ * (u' * x * u'⁻¹) * f := by rw [hu''def]; group
      _ = f⁻¹ * x⁻¹ * f := by rw [h]
      _ = (f⁻¹ * x * f)⁻¹ := by group
  obtain ⟨r, hr⟩ := RuDataM.Conf47.exists_pow_pow_eq C.b_pow_five hbm1
  have hu''b : u'' * C.b * u''⁻¹ = C.b⁻¹ := by
    calc u'' * C.b * u''⁻¹ = u'' * (C.b ^ m) ^ r * u''⁻¹ := by rw [hr]
      _ = (u'' * C.b ^ m * u''⁻¹) ^ r := by rw [conj_pow]
      _ = ((C.b ^ m)⁻¹) ^ r := by rw [hu''bm]
      _ = ((C.b ^ m) ^ r)⁻¹ := by rw [inv_pow]
      _ = C.b⁻¹ := by rw [hr]
  have hu''F : u'' ∈ C.F1 := mul_mem (mul_mem (inv_mem hfF) hu'F) hfF
  have hu''2 : u'' * u'' = 1 := by
    calc u'' * u'' = f⁻¹ * (u' * u') * f := by rw [hu''def]; group
      _ = 1 := by rw [hu'2]; group
  have hu''N : u'' ∈ C.NF1 := ⟨hu''F, RuDataM.mem_normalizer_of_inv hu''b⟩
  obtain ⟨n, hnN, hnS⟩ := exists_conj_mem_of_sylow (inf_le_left : C.SF1 ≤ C.NF1) C.isPGroup_SF1
    (by rw [C.relIndex_SF1]; norm_num) hu''N (by rw [pow_two]; exact hu''2)
  have hs2 : (n⁻¹ * u'' * n) * (n⁻¹ * u'' * n) = 1 := by
    calc (n⁻¹ * u'' * n) * (n⁻¹ * u'' * n) = n⁻¹ * (u'' * u'') * n := by group
      _ = 1 := by rw [hu''2]; group
  obtain ⟨p, hp, hpe⟩ := C.exists_iEl_eq hnS
  have hi := C.iEl_inv p hp (by rw [hpe]; exact hs2)
  rw [hpe] at hi
  have hnF : n ∈ C.F1 := hnN.1
  refine ⟨n⁻¹ * f⁻¹, mul_mem (inv_mem hnF) (inv_mem hfF), ?_⟩
  have hconj : (n⁻¹ * f⁻¹) * u' * (n⁻¹ * f⁻¹)⁻¹ = n⁻¹ * u'' * n := by rw [hu''def]; group
  rw [hconj]
  rcases hi with h | h | h | h
  · exfalso
    apply C.b_ne_inv
    have hu''1 : u'' = 1 := by
      calc u'' = n * (n⁻¹ * u'' * n) * n⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [← hu''b, hu''1]
    group
  · exfalso
    apply C.b_ne_inv
    have hzn : M.z * n = n * M.z := M.Z_comm_H M.z_mem_Z (C.F1_le_H hnF)
    have hu''z : u'' = M.z := by
      calc u'' = n * (n⁻¹ * u'' * n) * n⁻¹ := by group
        _ = n * M.z * n⁻¹ := by rw [h]
        _ = (M.z * n) * n⁻¹ := by rw [hzn]
        _ = M.z := by group
    calc C.b = C.b * M.z * M.z⁻¹ := by group
      _ = M.z * C.b * M.z⁻¹ := by rw [C.b_comm_z]
      _ = u'' * C.b * u''⁻¹ := by rw [hu''z]
      _ = C.b⁻¹ := hu''b
  · exact Or.inl h
  · exact Or.inr h

theorem burnsideJ410_final
    {M : RuDataM G} (C : RuDataM.Conf47 M) (hzF : M.z ∈ C.F1)
    (hZ : ∀ c ∈ C.F1, (∀ f ∈ C.F1, f * c = c * f) → c ∈ Subgroup.zpowers M.z)
    {y u : G} {B5 : Subgroup G} (hyz : y * M.z = M.z * y)
    (huF : u ∈ CFSG.conjugate C.F1 y) (hu2 : u * u = 1) (hB5F : B5 ≤ CFSG.conjugate C.F1 y)
    (hB5c : Nat.card B5 = 5) (hinv : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹) :
    Nonempty (EgonGraph (EsetRu (CFSG.conjugate C.F1 y) M.z u) M.z u ≃g
      SimpleGraph.cycleGraph 6) := by
  have hu'F : y * u * y⁻¹ ∈ C.F1 := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp huF
  have hu'2 : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
    calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hB5'F : CFSG.conjugate B5 y⁻¹ ≤ C.F1 := by
    intro x hx
    have h1 : y⁻¹ * x * y ∈ B5 := by
      have := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp hx
      simpa using this
    have h2 := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp (hB5F h1)
    have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    rwa [e] at h2
  have hB5'c : Nat.card (CFSG.conjugate B5 y⁻¹) = 5 := by
    rw [CFSG.ASVolI.RuChoice.fx_card_conjugate]; exact hB5c
  have hinv' : ∀ x ∈ CFSG.conjugate B5 y⁻¹, (y * u * y⁻¹) * x * (y * u * y⁻¹)⁻¹ = x⁻¹ := by
    intro x hx
    have h1 : y⁻¹ * x * y ∈ B5 := by
      have := CFSG.ASVolI.RuChoice.fx_mem_conjugate.mp hx
      simpa using this
    have h := hinv _ h1
    calc (y * u * y⁻¹) * x * (y * u * y⁻¹)⁻¹ = y * (u * (y⁻¹ * x * y) * u⁻¹) * y⁻¹ := by group
      _ = y * (y⁻¹ * x * y)⁻¹ * y⁻¹ := by rw [h]
      _ = x⁻¹ := by group
  obtain ⟨h, hhF, hh⟩ := burnsideJ410_normalize C hu'F hu'2 hB5'F hB5'c hinv'
  have hz : (h * y) * M.z * (h * y)⁻¹ = M.z := by
    have hhz : M.z * h = h * M.z := M.Z_comm_H M.z_mem_Z (C.F1_le_H hhF)
    calc (h * y) * M.z * (h * y)⁻¹ = h * (y * M.z) * y⁻¹ * h⁻¹ := by group
      _ = h * (M.z * y) * y⁻¹ * h⁻¹ := by rw [hyz]
      _ = (h * M.z) * h⁻¹ := by group
      _ = (M.z * h) * h⁻¹ := by rw [hhz]
      _ = M.z := by group
  have hF : CFSG.conjugate (CFSG.conjugate C.F1 y) (h * y)⁻¹ = C.F1 := by
    rw [CFSG.ASVolI.RuChoice.fx_conjugate_conjugate]
    have e : y * (h * y)⁻¹ = h⁻¹ := by group
    rw [e]
    exact CFSG.ASVolI.RuChoice.fx_conjugate_eq_self (Subgroup.le_normalizer (inv_mem hhF))
  have hu : (h * y) * u * (h * y)⁻¹ = h * (y * u * y⁻¹) * h⁻¹ := by group
  obtain ⟨ψ⟩ := burnsideJ410_conf_hexagon C hzF hZ
  rcases hh with hh | hh
  · obtain ⟨φ⟩ := burnsideJ410_Egon_transport' (h * y) hF hz (hu.trans hh)
    exact ⟨φ.trans ψ⟩
  · obtain ⟨φ⟩ := burnsideJ410_Egon_transport' (h * y) hF hz (hu.trans hh)
    obtain ⟨σ⟩ := burnsideJ410_Egon_swap M.z_mul_self C.F1 C.u
    exact ⟨(φ.trans σ).trans ψ⟩

theorem burnsideJ410_eq_z (M : RuDataM G) {z : G}
    (hz : Subgroup.zpowers z = CFSG.Quasithin.RuType.ruZ M.T) : z = M.z := by
  have hzmem : z ∈ CFSG.Quasithin.RuType.ruZ M.T := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have h2 := M.toRuData.card_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h2
    omega
  · exact h1

theorem burnsideJ410_card_five {H B : Subgroup G}
    (hH : Nat.card H = 2 ^ 11 * 120) (hB : CFSG.ASVolI.ChIJK.IsSylowIn 5 B H) :
    Nat.card B = 5 := by
  obtain ⟨hBH, hBp, hidx⟩ := hB
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have h := Subgroup.index_mul_card (B.subgroupOf H)
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hBH, hn, hH] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at h
      apply hidx
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h25 : 25 ∣ (B.subgroupOf H).index * 5 ^ (n + 2) :=
        Dvd.dvd.mul_left (by
          rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
          exact pow_dvd_pow 5 (by omega)) _
      rw [h] at h25
      norm_num at h25
  rw [hn, hn1, pow_one]
end BurnsideJ410I

section BurnsideJ410Setup

theorem burnsideJ410_mem_conjClass_iff {G : Type} [Group G] (z x : G) :
    x ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ IsConj z x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

open CFSG.ASVolI.ChIJK in
theorem burnsideJ410_Loc_of_setup
    {G : Type} [Group G] [Finite G]
    {L V T V2 B5 X : Subgroup G} {g v a z u : G} {I : Subgroup G}
    (hS : RuUSetup G L V T V2 B5 X g v a z u I) :
    burnsideJ410_Loc z u ∧ B5 ∈ EInv5Ru z u ∧ burnsideJ410_Cent z B5 := by
  have hRu := hS.setup.ru
  obtain ⟨M, -, hMT⟩ := hRu.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  have hH : Nat.card (HRu T) = 2 ^ 11 * 120 := by
    rw [hRu.HRu_eq_ruH, ← hMT]
    exact M.toRuData.card_H
  have hzM : z = M.z := by
    refine burnsideJ410_eq_z M ?_
    rw [hMT, ← hRu.ZRu_eq_ruZ]
    exact hS.z_gen
  have hB5card : Nat.card B5 = 5 := burnsideJ410_card_five hH hS.setup.b5.1
  have hz2 : z * z = 1 := by rw [hzM]; exact M.z_mul_self
  have hB5z : ∀ x ∈ B5, z * x * z⁻¹ = x := by
    intro x hx
    have hxH : x ∈ CFSG.Quasithin.RuType.ruH M.T := by
      rw [hMT, ← hRu.HRu_eq_ruH]
      exact hS.setup.b5.1.1 hx
    have h1 := M.mem_H_iff_comm.mp hxH
    rw [hzM]
    calc M.z * x * M.z⁻¹ = (x * M.z) * M.z⁻¹ := by rw [h1]
      _ = x := by group
  obtain ⟨h, -, hu⟩ := hS.u_x4
  have hu2 : u * u = 1 := by
    rw [hu]
    have e : (h : G) * z * (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) =
        (h : G) * (z * z) * (h : G)⁻¹ := by group
    rw [e, hz2]
    group
  have hzu : IsConj z u := isConj_iff.mpr ⟨h, hu.symm⟩
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hB5u : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have h1 := hS.u_inv.2 x hx
    rw [hui] at h1 ⊢
    exact h1
  have hu_ne : u ≠ z := by
    intro h1
    refine burnsideJ410_ne_of_cent_inv hB5card hB5z (fun y hy => ?_) (rfl : B5 = B5)
    have := hB5u y hy
    rwa [h1] at this
  obtain ⟨-, hF1⟩ := as_J_4_6 G L V T hRu V2 hS.setup.v2 g hS.setup.g_mem.1 hS.setup.g_mem.2 v
    hS.setup.v_mem.1 hS.setup.v_mem.2 B5 hS.setup.b5.1 hS.setup.b5.2 X hS.setup.x3 a
    hS.setup.a_choice hS.setup.a_norm hS.setup.q5_norm
  have hzZ : z ∈ ZRu T := by
    rw [← hS.z_gen]
    exact Subgroup.mem_zpowers z
  rw [← hF1] at hzZ
  have huF1 : u ∈ F1Ru L V V2 T a B5 := by
    unfold F1Ru
    exact Subgroup.mem_sup_left hS.u_TF
  have huz : u * z = z * u := by
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzZ
    have h1 := Subgroup.mem_center_iff.mp hw ⟨u, huF1⟩
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    have hwz' : (w : G) = z := hwz
    rw [hwz'] at h2
    exact h2
  have hzc : z ∈ conjClass z := ⟨1, by group⟩
  have huc : u ∈ conjClass z := (burnsideJ410_mem_conjClass_iff z u).mpr hzu
  have hne : u * z ≠ 1 := by
    intro h1
    apply hu_ne
    calc u = u * (z * z) := by rw [hz2]; group
      _ = (u * z) * z := by group
      _ = z := by rw [h1]; group
  have hmem := as_J_3_2 G L V T hRu z hS.z_gen u huc z hzc huz hne
  have hzuz : IsConj z (u * z) := (burnsideJ410_mem_conjClass_iff z _).mp hmem
  have hcent : burnsideJ410_Cent z B5 := hB5z
  refine ⟨⟨hz2, hu2, huz, ?_, hu_ne, hzu, hzuz, ?_⟩, ⟨hB5card,
    burnsideJ410_E_le_normalizer_iff.mpr
      ⟨burnsideJ410_mem_normalizer_of_cent_or_inv (Or.inl hcent),
        burnsideJ410_mem_normalizer_of_cent_or_inv (Or.inr hB5u)⟩⟩, hcent⟩
  · rw [hzM]; exact M.z_ne_one
  · intro c Bc hc hB hBc
    rw [hzM] at hc ⊢
    exact burnsideJ410_LS_of_isConj M hc hB hBc

end BurnsideJ410Setup

section

open CFSG.ASVolI.ChIJK in
theorem as_J_4_10 : J_4_10 := by
  intro G _ _ L V T V2 B5 X g v a z u I hS
  have hRu := hS.setup.ru
  obtain ⟨M, y, -, hMT, hyT, -, -, -, -, -, -, hF1, -, -⟩ :=
    RuChoice.reduce hRu hS.setup.v2 hS.setup.g_mem.1 hS.setup.g_mem.2 hS.setup.v_mem.1
      hS.setup.v_mem.2 hS.setup.b5.1 hS.setup.b5.2 hS.setup.x3 hS.setup.a_choice
      hS.setup.a_norm hS.setup.q5_norm
  have hMT' : M.T = hRu.sylowT := Sylow.ext (hMT.trans hRu.coe_sylowT.symm)
  have hH : Nat.card (HRu T) = 2 ^ 11 * 120 := by
    rw [hRu.HRu_eq_ruH, ← hMT']
    exact M.toRuData.card_H
  have hzM : z = M.z := by
    refine burnsideJ410_eq_z M ?_
    rw [hMT', ← hRu.ZRu_eq_ruZ]
    exact hS.z_gen
  have hz2 : z * z = 1 := by rw [hzM]; exact M.z_mul_self
  have hB5c : Nat.card B5 = 5 := burnsideJ410_card_five hH hS.setup.b5.1
  obtain ⟨h, -, hu⟩ := hS.u_x4
  have hu2 : u * u = 1 := by
    rw [hu]
    have e : (h : G) * z * (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) =
        (h : G) * (z * z) * (h : G)⁻¹ := by group
    rw [e, hz2]
    group
  have huF1 : u ∈ F1Ru L V V2 T a B5 := by
    unfold F1Ru
    exact Subgroup.mem_sup_left hS.u_TF
  have hB5F1 : B5 ≤ F1Ru L V V2 T a B5 := by
    unfold F1Ru
    exact le_sup_right
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hB5u : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have h1 := hS.u_inv.2 x hx
    rw [hui] at h1 ⊢
    exact h1
  obtain ⟨-, hFc⟩ := as_J_4_6 G L V T hRu V2 hS.setup.v2 g hS.setup.g_mem.1 hS.setup.g_mem.2 v
    hS.setup.v_mem.1 hS.setup.v_mem.2 B5 hS.setup.b5.1 hS.setup.b5.2 X hS.setup.x3 a
    hS.setup.a_choice hS.setup.a_norm hS.setup.q5_norm
  have hRuT : CFSG.Quasithin.RuType.IsTypeRu G := ⟨M.L, M.one, M.T, M.two⟩
  obtain ⟨e⟩ := CFSG.Quasithin.RuType.J47.exists_amalgamIso_of_case2F4
    (M.case2F4 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
      (CFSG.Quasithin.RuType.isQuasithinSub_of_isTypeRu hRuT _))
  have hCF1 : (M.conf47 e).F1 = M.F1 := rfl
  have hzF : M.z ∈ (M.conf47 e).F1 := by
    rw [hCF1]
    exact M.Agrp_le_F1 (M.W_le_Agrp (M.U_le_W (M.V_le_U M.z_mem_V)))
  have hyT' : y ∈ (M.T : Subgroup G) := by rw [hMT]; exact hyT
  have hyz : y * M.z = M.z * y :=
    (M.Z_comm_H M.z_mem_Z (M.toRuData.T_le_H hyT')).symm
  have hZ : ∀ c ∈ (M.conf47 e).F1, (∀ f ∈ (M.conf47 e).F1, f * c = c * f) →
      c ∈ Subgroup.zpowers M.z := by
    intro c hc hcc
    rw [hCF1] at hc hcc
    have hc' : y⁻¹ * c * y ∈ F1Ru L V V2 T a B5 := by
      rw [hF1, CFSG.ASVolI.RuChoice.fx_mem_conjugate]
      have e' : y * (y⁻¹ * c * y) * y⁻¹ = c := by group
      rw [e']
      exact hc
    have hcen : y⁻¹ * c * y ∈ centerOf (F1Ru L V V2 T a B5) := by
      refine Subgroup.mem_map.mpr ⟨⟨y⁻¹ * c * y, hc'⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro f
      apply Subtype.ext
      show (f : G) * (y⁻¹ * c * y) = (y⁻¹ * c * y) * f
      have hf : y * (f : G) * y⁻¹ ∈ M.F1 := by
        have key : ∀ x : G, x ∈ F1Ru L V V2 T a B5 → y * x * y⁻¹ ∈ M.F1 := by
          intro x hx
          rw [hF1, CFSG.ASVolI.RuChoice.fx_mem_conjugate] at hx
          exact hx
        exact key _ f.2
      have h1 := hcc _ hf
      calc (f : G) * (y⁻¹ * c * y) = y⁻¹ * ((y * (f : G) * y⁻¹) * c) * y := by group
        _ = y⁻¹ * (c * (y * (f : G) * y⁻¹)) * y := by rw [h1]
        _ = (y⁻¹ * c * y) * f := by group
    rw [hFc, ← hS.z_gen, hzM] at hcen
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcen
    have hzz : y * M.z * y⁻¹ = M.z := by rw [hyz]; group
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc M.z ^ k = (y * M.z * y⁻¹) ^ k := by rw [hzz]
      _ = y * M.z ^ k * y⁻¹ := by rw [conj_zpow]
      _ = y * (y⁻¹ * c * y) * y⁻¹ := by rw [hk]
      _ = c := by group
  have huC : u ∈ CFSG.conjugate M.F1 y := by rw [← hF1]; exact huF1
  have hB5C : B5 ≤ CFSG.conjugate M.F1 y := by rw [← hF1]; exact hB5F1
  rw [hzM, hF1]
  exact burnsideJ410_final (M.conf47 e) hzF hZ hyz huC hu2 hB5C hB5c hB5u

end

end CFSG.ASVolI
