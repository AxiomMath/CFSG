module

public import CFSG.Quasithin.Vol2.Ch10SecE9H

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

theorem mod_twelve_of_normalizes {Q : Type} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (e : Q ≃* PSL(2, ZMod p)) {S Y : Subgroup Q}
    (hS : IsKleinFour ↥S) (hY : Nat.card Y = 3) (hSY : S ≤ Subgroup.normalizer (Y : Set Q)) :
    p % 12 = 1 ∨ p % 12 = 11 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  have hidx := C10P34.relIndex_centralizer_dvd_two hY hSY
  have h1 := Subgroup.relIndex_mul_card (S ⊓ Subgroup.centralizer (Y : Set Q)) S
  rw [inf_right_comm, inf_idem, hS.card_four] at h1
  have hle := Nat.le_of_dvd two_pos hidx
  have hC2 : 1 < Nat.card ↥(S ⊓ Subgroup.centralizer (Y : Set Q)) := by
    by_contra hcon
    have : Nat.card ↥(S ⊓ Subgroup.centralizer (Y : Set Q)) ≤ 1 := by omega
    have : (S ⊓ Subgroup.centralizer (Y : Set Q)).relIndex S *
        Nat.card ↥(S ⊓ Subgroup.centralizer (Y : Set Q)) ≤ 2 * 1 := Nat.mul_le_mul hle this
    omega
  obtain ⟨⟨z, hzC⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hC2))
  have hzS : z ∈ S := hzC.1
  have hz2 : orderOf z = 2 := by
    have hz' : (⟨z, hzS⟩ : ↥S) ≠ 1 := fun h =>
      hz1 (Subtype.ext (by simpa using congrArg Subtype.val h))
    have h2 : orderOf (⟨z, hzS⟩ : ↥S) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hS.mul_self _) hz'
    rwa [Subgroup.orderOf_mk] at h2
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 (by rw [hY])
  have hyz : (y : Q) * z = z * y := Subgroup.mem_centralizer_iff.mp hzC.2 y y.2
  have hez : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz2
  have hC := CFSG.Walter.psl2_centralizer_involution (ZMod p) (p := p) (f := 1)
    (by rw [Nat.card_zmod, pow_one]) hpo one_pos hez
  have hmem : e y ∈ Subgroup.centralizer ({e z} : Set PSL(2, ZMod p)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyz]
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({e z} : Set PSL(2, ZMod p))) := by
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy] at this
  rw [pow_one] at hC
  rcases h8 with h8 | h8
  · rw [(hC.2 (by omega)).1] at h3
    obtain ⟨k, hk⟩ := h3
    omega
  · rw [(hC.1 (by omega)).1] at h3
    obtain ⟨k, hk⟩ := h3
    omega

variable {G : Type} [Group G] [Finite G] {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

theorem mod_twelve_of_pair {X T : Subgroup G}
    (hc : C10P34.PairCtx H K₁ K₂ φ) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (e₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hXK : X ≤ K₁ ⊔ K₂) (hXO : oTwoUpper X = X) (hX3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hbad : pCoreOf 2 X ≤ pCoreOf 2 (K₁ ⊔ K₂)) : p % 12 = 1 ∨ p % 12 = 11 := by
  have hker : ∀ k, φ k = 1 → (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) := fun k hk => by
    have h1 : k ∈ φ.ker := hk
    rw [hc.ker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hO : ∀ k : ↥(K₁ ⊔ K₂), (k : G) ∈ pCoreOf 2 (K₁ ⊔ K₂) → φ k = 1 := fun k hk => by
    have h1 : k ∈ φ.ker := by rw [hc.ker, Subgroup.mem_subgroupOf]; exact hk
    exact h1
  obtain ⟨hSyl₁, -, -⟩ := map_sylow_eq_prod hc.surj hS
  have hXprod := C10P34.map_eq_prod hp5 e₁ e₂ hker hXK hXO hX3 hPX hP hP3
  have hY₁ := card_eq_three_of_pCoreOf_eq_bot hp5 e₁
    (C10P34.fst_ne_bot hp5 e₂ hker hXK hXO hX3 hPX hP hP3) (C10P34.oTwoUpper_map_eq _ hXK hXO)
    (C10P34.pow_three_mem_map _ hXK hX3) (pCoreOf_map_fst_eq_bot hker hO hXK hXprod hbad)
  have hSX : T ⊓ (K₁ ⊔ K₂) ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have hSY₁ := C10P34.map_le_normalizer_map ((MonoidHom.fst _ _).comp φ) hSX hXK
  exact mod_twelve_of_normalizes h8 e₁ (isKleinFour_of_sylow h8 e₁ hSyl₁) hY₁ hSY₁

omit [Finite G] in
theorem pow_eq_one_of_conj_pow {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) {a : Q}
    {m : ℕ} (h : (MulAut.conj a) ^ m = 1) : a ^ m = 1 := by
  have h1 : MulAut.conj (a ^ m) = 1 := by rw [map_pow]; exact h
  have h2 : a ^ m ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun y => by
    have h3 := congrArg (fun f : MulAut Q => f y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * a ^ m = a ^ m * y * (a ^ m)⁻¹ * a ^ m := by rw [h3]
      _ = a ^ m * y := by group
  rw [hZ] at h2
  exact Subgroup.mem_bot.mp h2

theorem mem_normalizer_of_coprime {X T T₁ : Subgroup G}
    (hc : C10P34.PairCtx H K₁ K₂ φ) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (e₁ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (e₂ : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* PSL(2, ZMod p))
    (hXK : X ≤ K₁ ⊔ K₂) (hXO : oTwoUpper X = X) (hX3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    {P : Subgroup G} (hPX : P ≤ X) (hP : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hS : IsSylowTwoOf (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT2 : IsPGroup 2 T) (hTH : T ≤ H) (hT₁T : T₁ ≤ T)
    (hTT₁ : T ≤ Subgroup.normalizer (T₁ : Set G))
    (hW : pCoreOf 2 (X ⊔ T ⊓ (K₁ ⊔ K₂)) ≤ T₁ ⊓ (K₁ ⊔ K₂)) {s : G} (hs : s ∈ T)
    (hs₁₂ : K₁.map (MulAut.conj s).toMonoidHom = K₂)
    (hbad : pCoreOf 2 X ≤ pCoreOf 2 (K₁ ⊔ K₂)) {n : G} (hnH : n ∈ H)
    (hnT₁ : n ∈ Subgroup.normalizer (T₁ : Set G)) (hn6 : Nat.Coprime (orderOf n) 6) :
    n ∈ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (orderOf n) := by
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => ?_)
    have h3 := Nat.dvd_gcd h2 (show 2 ∣ 6 by norm_num)
    rw [Nat.Coprime.gcd_eq_one hn6] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
  rcases mem_normalizer_or_witness hc hp5 h8 e₁ e₂ hXK hXO hX3 hPX hP hP3 hS hTX hT2 hTH hT₁T
      hTT₁ hW hs hs₁₂ hbad hnH hnT₁ hodd with h | ⟨hST₁, -⟩
  · exact h
  obtain ⟨hn₁, hn₂⟩ := hc.fix_of_odd hnH hodd
  have hnK := hc.normal hnH
  obtain ⟨a₁, ha₁, ha₁o⟩ :=
    C10P34.exists_inner_of_pow_eq_one e₁ hodd (C10P34.conjQuot_pow_orderOf hn₁)
  obtain ⟨a₂, ha₂, ha₂o⟩ :=
    C10P34.exists_inner_of_pow_eq_one e₂ hodd (C10P34.conjQuot_pow_orderOf hn₂)
  have hconj : ∀ (z : G) (hz : z ∈ K₁ ⊔ K₂) (hz' : n * z * n⁻¹ ∈ K₁ ⊔ K₂),
      φ ⟨n * z * n⁻¹, hz'⟩ = (a₁ * (φ ⟨z, hz⟩).1 * a₁⁻¹, a₂ * (φ ⟨z, hz⟩).2 * a₂⁻¹) := by
    intro z hz hz'
    rw [hc.app_conj_fix hn₁ hn₂ hz, ← ha₁, ← ha₂]
    rfl
  obtain ⟨hSyl₁, hSyl₂, -⟩ := map_sylow_eq_prod hc.surj hS
  have hnS : ∀ w ∈ T ⊓ (K₁ ⊔ K₂), n * w * n⁻¹ ∈ T ⊓ (K₁ ⊔ K₂) := fun w hw =>
    ⟨hT₁T ((Subgroup.mem_normalizer_iff.mp hnT₁ w).mp (hST₁ hw)),
      conj_mem_of_mem_normalizer hnK hw.2⟩
  have ha₁S : a₁ ∈ Subgroup.normalizer
      (((((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.fst _ _).comp φ)) :
        Subgroup _) : Set _) := C10P34.mem_normalizer_of_forall_conj_mem fun u hu => by
    obtain ⟨⟨w, hwK⟩, hw, hwu⟩ := hu
    have hw' := conj_mem_of_mem_normalizer hnK hwK
    refine ⟨⟨n * w * n⁻¹, hw'⟩, hnS w (Subgroup.mem_subgroupOf.mp hw), ?_⟩
    rw [MonoidHom.comp_apply, hconj w hwK hw', ← hwu]
    simp
  have ha₂S : a₂ ∈ Subgroup.normalizer
      (((((T ⊓ (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)).map ((MonoidHom.snd _ _).comp φ)) :
        Subgroup _) : Set _) := C10P34.mem_normalizer_of_forall_conj_mem fun u hu => by
    obtain ⟨⟨w, hwK⟩, hw, hwu⟩ := hu
    have hw' := conj_mem_of_mem_normalizer hnK hwK
    refine ⟨⟨n * w * n⁻¹, hw'⟩, hnS w (Subgroup.mem_subgroupOf.mp hw), ?_⟩
    rw [MonoidHom.comp_apply, hconj w hwK hw', ← hwu]
    simp
  have ha₁1 : a₁ = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one (pow_three_eq_one_of_mem_normalizer h8 e₁ hSyl₁ ha₁S ha₁o)
    have h2 := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_conj_pow hc.center₁
      (by rw [ha₁]; exact C10P34.conjQuot_pow_orderOf hn₁))
    have h3 := Nat.dvd_gcd h2 (h1.trans (show 3 ∣ 6 by norm_num))
    rwa [Nat.Coprime.gcd_eq_one hn6, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have ha₂1 : a₂ = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one (pow_three_eq_one_of_mem_normalizer h8 e₂ hSyl₂ ha₂S ha₂o)
    have h2 := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_conj_pow hc.center₂
      (by rw [ha₂]; exact C10P34.conjQuot_pow_orderOf hn₂))
    have h3 := Nat.dvd_gcd h2 (h1.trans (show 3 ∣ 6 by norm_num))
    rwa [Nat.Coprime.gcd_eq_one hn6, Nat.dvd_one, orderOf_eq_one_iff] at h3
  subst ha₁1 ha₂1
  exact mem_normalizer_of_inner hc hp5 e₁ e₂ hXK hXO hX3 hPX hP hP3 hS hTX hnK hconj
    (Subgroup.one_mem _) (Subgroup.one_mem _)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
