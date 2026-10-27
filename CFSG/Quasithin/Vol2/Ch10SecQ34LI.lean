module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] {Kc X : Subgroup G}

theorem oTwoUpper_map_eq {Q : Type} [Group Q] (f : ↥Kc →* Q) (hXK : X ≤ Kc)
    (hX : oTwoUpper X = X) : oTwoUpper ((X.subgroupOf Kc).map f) = (X.subgroupOf Kc).map f := by
  refine le_antisymm (oTwoUpper_le _) ?_
  set M : Subgroup G := ((oTwoUpper ((X.subgroupOf Kc).map f)).comap f).map Kc.subtype with hM
  have hXM : X ≤ M := by
    rw [← hX]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxX, hodd⟩ := hx
    refine ⟨⟨x, hXK hxX⟩, ?_, rfl⟩
    refine mem_oTwoUpper_of_odd ⟨⟨x, hXK hxX⟩, hxX, rfl⟩ ?_
    exact hodd.of_dvd_nat ((orderOf_map_dvd f _).trans (dvd_of_eq (Subgroup.orderOf_mk _ _)))
  rintro _ ⟨⟨x, hxK⟩, hx, rfl⟩
  obtain ⟨k, hk, hkx⟩ := hXM hx
  have : k = ⟨x, hxK⟩ := Subtype.ext hkx
  rw [← this]
  exact hk

theorem map_le_normalizer_map {Q : Type} [Group Q] [Finite Q] (f : ↥Kc →* Q)
    {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hAK : A ≤ Kc) :
    (B.subgroupOf Kc).map f ≤
      Subgroup.normalizer (((A.subgroupOf Kc).map f : Subgroup Q) : Set Q) := by
  rintro _ ⟨⟨b, hbK⟩, hb, rfl⟩
  refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
  obtain ⟨⟨a, haK⟩, ha, rfl⟩ := hw
  have hba : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hBA hb) a).mp ha
  refine ⟨⟨b * a * b⁻¹, hAK hba⟩, hba, ?_⟩
  rw [show (⟨b * a * b⁻¹, hAK hba⟩ : ↥Kc) = ⟨b, hbK⟩ * ⟨a, haK⟩ * (⟨b, hbK⟩ : ↥Kc)⁻¹ from rfl,
    map_mul, map_mul, map_inv]

theorem pow_three_mem_map [Finite G] {Q : Type} [Group Q] [Finite Q] (f : ↥Kc →* Q)
    (hXK : X ≤ Kc)
    (h3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) :
    ∀ y ∈ (X.subgroupOf Kc).map f, y ^ 3 ∈ pCoreOf 2 ((X.subgroupOf Kc).map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOX := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hOK : pCoreOf 2 X ≤ Kc := hOX.trans hXK
  have hWY : ((pCoreOf 2 X).subgroupOf Kc).map f ≤ (X.subgroupOf Kc).map f :=
    Subgroup.map_mono fun k hk => hOX hk
  have hW2 : IsPGroup 2 ↥(((pCoreOf 2 X).subgroupOf Kc).map f) :=
    (A4.isPGroup_subgroupOf_of_le hOK (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)).map f
  have hYW := map_le_normalizer_map f (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) hOK
  have hWO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWY hYW hW2
  rintro _ ⟨⟨x, hxK⟩, hx, rfl⟩
  refine hWO ⟨⟨x ^ 3, Kc.pow_mem hxK 3⟩, h3 x hx, ?_⟩
  rw [← map_pow]
  rfl

theorem not_nine_dvd {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (e : Q ≃* PSL(2, ZMod p)) {Y : Subgroup Q}
    (hYO : oTwoUpper Y = Y) (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) : ¬ 9 ∣ Nat.card Y := by
  by_cases hY1 : Y = ⊥
  · rw [hY1, Subgroup.card_bot]
    norm_num
  · rcases card_eq_three_or_alt4 hp5 e hY1 hYO hY3 with h | heY
    · rw [h]
      norm_num
    · obtain ⟨eY⟩ := heY
      rw [Nat.card_congr eY.toEquiv, card_alt4]
      norm_num

theorem le_of_three_dvd {Q : Type} [Group Q] [Finite Q] {Y N : Subgroup Q} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set Q)) (h3 : 3 ∣ Nat.card N)
    (h9 : ¬ 9 ∣ Nat.card Y) (hYO : oTwoUpper Y = Y) (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) :
    Y ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN' : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  have hcard : Nat.card N * (N.subgroupOf Y).index = Nat.card Y := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv]
    exact (N.subgroupOf Y).card_mul_index
  have hi : ¬ 3 ∣ (N.subgroupOf Y).index := by
    intro h
    apply h9
    rw [← hcard, show 9 = 3 * 3 by norm_num]
    exact Nat.mul_dvd_mul h3 h
  rw [← hYO]
  refine (Subgroup.closure_le _).mpr fun w hw => ?_
  obtain ⟨hwY, hodd⟩ := hw
  have hw3 : w ^ 3 = 1 := eq_one_of_odd_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (hY3 w hwY) (hodd.of_dvd_nat (orderOf_pow_dvd 3))
  have hmem : (⟨w, hwY⟩ : ↥Y) ^ (N.subgroupOf Y).index ∈ N.subgroupOf Y :=
    Subgroup.pow_index_mem _ _
  have hcop : Nat.Coprime (N.subgroupOf Y).index (orderOf (⟨w, hwY⟩ : ↥Y)) := by
    have hd : orderOf (⟨w, hwY⟩ : ↥Y) ∣ 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hw3
    exact Nat.Coprime.coprime_dvd_right hd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hi).symm
  exact (Subgroup.zpowers_le.mpr hmem) (A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_inl_mem [Finite G] {Q₁ Q₂ : Type} [Group Q₁]
    [Group Q₂] [Finite Q₂] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (e₂ : Q₂ ≃* PSL(2, ZMod p))
    {φ : ↥Kc →* Q₁ × Q₂} (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) (hXK : X ≤ Kc)
    (hX : oTwoUpper X = X) (h3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) {P : Subgroup G}
    (hPX : P ≤ X) (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ y : Q₁, orderOf y = 3 ∧ (y, 1) ∈ (X.subgroupOf Kc).map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ₂ := (MonoidHom.snd Q₁ Q₂).comp φ with hφ₂
  have hPK : P ≤ Kc := hPX.trans hXK
  set g : ↥P →* Q₂ := φ₂.comp (Subgroup.inclusion hPK) with hg
  have hrange : g.range ≤ (X.subgroupOf Kc).map φ₂ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hPK x, hPX x.2, rfl⟩
  have h9 := not_nine_dvd hp5 e₂ (oTwoUpper_map_eq φ₂ hXK hX) (pow_three_mem_map φ₂ hXK h3)
  have hr : Nat.card g.range ≠ 9 := fun h => h9 (h ▸ Subgroup.card_dvd_of_le hrange)
  have hk1 : g.ker ≠ ⊥ := by
    intro hb
    apply hr
    rw [← Subgroup.index_ker, ← hP, ← Subgroup.card_mul_index g.ker, hb, Subgroup.card_bot,
      one_mul]
  obtain ⟨⟨x, hxk⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk1
  have hx2 : (φ ⟨x, hPK x.2⟩).2 = 1 := hxk
  have hx3 : (x : G) ^ 3 = 1 := hP3 x x.2
  have hxne : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
  set y := (φ ⟨x, hPK x.2⟩).1 with hy
  have hy3 : y ^ 3 = 1 := by
    have h1 : φ (⟨x, hPK x.2⟩ ^ 3) = 1 := by
      rw [show (⟨x, hPK x.2⟩ : ↥Kc) ^ 3 = 1 from Subtype.ext hx3, map_one]
    rw [map_pow] at h1
    exact congrArg Prod.fst h1
  have hy1 : y ≠ 1 := by
    intro h
    have h2 := hker _ (Prod.ext h hx2)
    exact hxne (eq_one_of_odd_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kc) h2
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)))
  exact ⟨y, orderOf_eq_prime hy3 hy1, ⟨⟨x, hPK x.2⟩, hPX x.2, Prod.ext rfl hx2⟩⟩

theorem fst_le_comap_inl [Finite G] {Q₁ Q₂ : Type} [Group Q₁]
    [Group Q₂] [Finite Q₁] [Finite Q₂] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e₁ : Q₁ ≃* PSL(2, ZMod p)) (e₂ : Q₂ ≃* PSL(2, ZMod p)) {φ : ↥Kc →* Q₁ × Q₂}
    (hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 Kc) (hXK : X ≤ Kc) (hX : oTwoUpper X = X)
    (h3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) :
    (X.subgroupOf Kc).map ((MonoidHom.fst Q₁ Q₂).comp φ) ≤
      ((X.subgroupOf Kc).map φ).comap (MonoidHom.inl Q₁ Q₂) := by
  set φ₁ := (MonoidHom.fst Q₁ Q₂).comp φ with hφ₁
  set Y₁ := (X.subgroupOf Kc).map φ₁ with hY₁
  set XX := (X.subgroupOf Kc).map φ with hXX
  set N := Y₁ ⊓ XX.comap (MonoidHom.inl Q₁ Q₂) with hN
  obtain ⟨y, hy3, hyX⟩ := exists_inl_mem hp5 e₂ hker hXK hX h3 hPX hP hP3
  have hyN : y ∈ N := by
    refine ⟨?_, hyX⟩
    obtain ⟨x, hx, hxy⟩ := hyX
    exact ⟨x, hx, by rw [hφ₁, MonoidHom.comp_apply, hxy]; rfl⟩
  have h3N : 3 ∣ Nat.card N := by
    rw [← hy3, ← Subgroup.orderOf_mk y hyN]
    exact orderOf_dvd_natCard _
  have hYN : Y₁ ≤ Subgroup.normalizer (N : Set Q₁) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_normalizer_of_forall_conj_mem fun n hn =>
      ⟨Y₁.mul_mem (Y₁.mul_mem ⟨x, hx, rfl⟩ hn.1) (Y₁.inv_mem ⟨x, hx, rfl⟩), ?_⟩
    have h1 : φ x * (n, 1) * (φ x)⁻¹ ∈ XX :=
      XX.mul_mem (XX.mul_mem ⟨x, hx, rfl⟩ hn.2) (XX.inv_mem ⟨x, hx, rfl⟩)
    have h2 : φ x * (n, 1) * (φ x)⁻¹ = (φ₁ x * n * (φ₁ x)⁻¹, 1) := by
      ext <;> simp [hφ₁]
    change (φ₁ x * n * (φ₁ x)⁻¹, (1 : Q₂)) ∈ XX
    rw [← h2]
    exact h1
  have hYO := oTwoUpper_map_eq φ₁ hXK hX
  have hY3 := pow_three_mem_map φ₁ hXK h3
  exact (le_of_three_dvd inf_le_left hYN h3N (not_nine_dvd hp5 e₁ hYO hY3) hYO hY3).trans
    inf_le_right

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
