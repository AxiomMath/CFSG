module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspL3
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspF4Aut
public import CFSG.Quasithin.EmptyFaithful.S151S4B
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspDefs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint CFSG.Blueprint.Chevalley L3M
  CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin (perfectCore map_perfectCore)

theorem F4A.three_dvd_card_and_center_eq_bot {X : Type} [Group X] {n : ℕ}
    (h : IsPSL 2 2 n X) : 3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨F, _, _, hchar, hF, ⟨eF⟩⟩ := CFSG.Quasithin.S151S4.exists_equiv_sl2 h
  refine ⟨?_, ?_⟩
  · have hc := CFSG.OrderReductions.LinearOrders.card_specialLinear F 2 (by norm_num)
    rw [Nat.card_congr eF.toEquiv, hc, hF]
    simp only [show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, Finset.Icc_self,
      Finset.prod_singleton]
    refine dvd_mul_of_dvd_right ?_ _
    rw [← pow_mul, mul_comm n 2, pow_mul]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 n
  · rw [eq_bot_iff]
    intro z hz
    have h1 : eF z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eF.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [CFSG.Quasithin.S151S4.center_sl2_eq_bot F, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact eF.injective (by simpa using h1)

theorem F4A.not_three_dvd_card_rankOneGroupTwo
    {a : ℕ} {L : Type} [Field L] [Finite L] [CharP L F4.prime] (ha : 1 ≤ a)
    (hL : Nat.card L = 2 ^ (2 * a + 1)) : ¬ 3 ∣ Nat.card ↥(rankOneGroupTwo L a) := by
  rw [card_rankOneGroupTwo ha hL]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega

theorem insp436F4_holds :
    Insp436F4 := by
  intro G _ _ K P V R₀ n hn hKq hF4 hP hPSL hnat hV hR₀2 hR₀N hR₀P hNP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Subgroup ↥K := P.comap K.subtype with hP₀
  have hPK : P ≤ K := hP.1.1
  have hP₀K : P₀.map K.subtype = P := by
    rw [hP₀, Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])]
  have hP₀max : IsMaxParabolic2 (⊤ : Subgroup ↥K) P₀ :=
    L436.isMaxParabolic2_comap K.subtype K.subtype_injective K.range_subtype.symm hP
  obtain ⟨S₁, hS₁, hNS₁, hPcov⟩ :=
    CFSG.Quasithin.Lie2Parabolic.exists_sylow_of_isMaxParabolic2 hP₀max
  obtain ⟨a, L, _, _, _, ha, hna, hL, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hF4
  subst hna
  have : Finite (ModGL F4.tag L) := finite_modGL
  set C := F4.reeGamma L a with hC
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a L w₀ hw₀).1
  have hres := CFSG.QuasithinUnique.Setup.X6.large_Ree_residualOvergroupsAt (a := a) hL
  set q : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hT := isSylowTwoOf_map_top hS₁ (f := e.toMonoidHom.comp q) (e.surjective.comp hqs)
  have hidx : ¬ 2 ∣ (S₁.map (e.toMonoidHom.comp q)).index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex_top_right]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C (hT.2.1.toSylow hidx) PU
  set θ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥C := e.trans (MulAut.conj c) with hθ
  set Φ : ↥K →* ↥C := θ.toMonoidHom.comp q with hΦ
  have hΦs : Function.Surjective Φ := θ.surjective.comp hqs
  have hΦker : ∀ x, Φ x = 1 → x ∈ Subgroup.center ↥K := by
    intro x hx
    have h1 : q x = 1 := θ.injective (by rw [map_one]; exact hx)
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hker : Φ.ker ≤ P₀ := fun x hx =>
    ((Subgroup.center_le_normalizer _).trans hNS₁) (hΦker x hx)
  have hSU : S₁.map Φ = (F4.reeFixedPosUnipotent L a).subgroupOf C := by
    have h1 : ((c • hT.2.1.toSylow hidx : Sylow 2 ↥C) : Subgroup ↥C) =
        (F4.reeFixedPosUnipotent L a).subgroupOf C := by
      rw [hc]
      exact hPU
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e (q y), Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hcov : P₀.map Φ ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective Φ hΦs]
    exact covBy_map_of_ker_le hΦs hker hPcov
  have hUM : (F4.reeFixedPosUnipotent L a).subgroupOf C ≤ P₀.map Φ :=
    hSU ▸ Subgroup.map_mono (Subgroup.le_normalizer.trans hNS₁)
  obtain ⟨j, hj⟩ := (hres.2.2.1 _ hUM).mp hcov
  have hPcore : (perfectCore P₀).map K.subtype = perfectCore P := by rw [map_perfectCore, hP₀K]
  have hmemP₀ : ∀ a : ↥K, (a : G) ∈ perfectCore P → a ∈ perfectCore P₀ := by
    intro a ha
    rw [← hPcore] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rwa [Subtype.ext hba] at hb
  have hP₀le : ∀ a ∈ perfectCore P₀, (a : G) ∈ perfectCore P := fun a ha =>
    hPcore ▸ Subgroup.mem_map_of_mem _ ha
  have hAK : perfectCore P ≤ K := (CFSG.Quasithin.perfectCore_le P).trans hPK
  have hcoreJ' : (perfectCore P₀).map Φ = perfectCore
      ((F4.reeParabolic L a {CFSG.QuasithinUnique.Setup.X6.f4Index j}).subgroupOf C) := by
    rw [map_perfectCore Φ P₀, hj]
  have hcoreJ : ((perfectCore P₀).map Φ).map C.subtype =
      perfectCore (F4.reeParabolic L a {CFSG.QuasithinUnique.Setup.X6.f4Index j}) := by
    rw [hcoreJ', CFSG.QuasithinUnique.Vol2Native.A312L.perfectCore_map_subgroupOf
      (reeParabolic_le F4 L a _)]
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (CFSG.QuasithinUnique.Setup.X6.f4Index j) with hj0 | hj1
  ·
    have hcore0 : ((perfectCore P₀).map Φ).map C.subtype =
        perfectCore (F4.reeLocalParabolic L a ⟨0, by decide⟩) := by
      rw [hj0, reeParabolic_singleton] at hcoreJ
      exact hcoreJ
    intro r hr
    set ψ : MulAut ↥K := conjOn K (hR₀N hr) with hψ
    have hψx : ∀ x : ↥K, ((ψ x : ↥K) : G) = r * x * r⁻¹ := fun x => coe_conjOn K (hR₀N hr) x
    have hfix : ∀ x ∈ perfectCore P₀, ψ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hψx, ← Subgroup.mem_centralizer_iff.mp (hR₀P hr) _ (hP₀le x hx), mul_inv_cancel_right]
    set φ' : MulAut ↥C := θ.symm.trans ((autCenter ψ).trans θ) with hφ'
    have hφ'Φ : ∀ y : ↥K, φ' (Φ y) = Φ (ψ y) := by
      intro y
      simp only [hφ', hΦ, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]
      rw [hq, QuotientGroup.mk'_apply, autCenter_mk]
      rfl
    have hfix' : ∀ x : ↥C, (x : ModGL F4.tag L) ∈
        perfectCore (F4.reeLocalParabolic L a ⟨0, by decide⟩) → φ' x = x := by
      intro x hx
      rw [← hcore0] at hx
      obtain ⟨x', hx', hx'x⟩ := hx
      have hxx : x' = x := Subtype.ext hx'x
      subst hxx
      obtain ⟨y, hy, rfl⟩ := hx'
      rw [hφ'Φ, hfix y hy]
    obtain ⟨m₀, hm₀⟩ := hR₀2 ⟨r, hr⟩
    have hrm : r ^ 2 ^ m₀ = 1 := congrArg Subtype.val hm₀
    have hψpow : ∀ (m : ℕ) (y : ↥K), (((ψ ^ m) y : ↥K) : G) = r ^ m * y * (r ^ m)⁻¹ := by
      intro m y
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ' ψ m, MulAut.mul_apply, hψx, ih]
        group
    have hφ'pow : ∀ (m : ℕ) (y : ↥K), (φ' ^ m) (Φ y) = Φ ((ψ ^ m) y) := by
      intro m y
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ' φ' m, pow_succ' ψ m, MulAut.mul_apply, MulAut.mul_apply, ih, hφ'Φ]
    have hφ'2 : φ' ^ 2 ^ m₀ = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨y, rfl⟩ := hΦs x
      rw [hφ'pow, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [hψpow, hrm, one_mul, inv_one, mul_one]
    have hφ'1 := F4A.aut_eq_one_of_fixes ha hL φ' hφ'2 hfix'
    have hψ1 : autCenter ψ = 1 := by
      ext y
      have h := congrArg (fun β : MulAut ↥C => β (θ y)) hφ'1
      simp only [hφ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
      rw [MulAut.one_apply]
      exact θ.injective h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h := congrArg Subtype.val (eq_of_autCenter_eq_one hKq.1 ψ hψ1 ⟨k, hk⟩)
    rw [hψx] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  ·
    exfalso
    have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent L a) := by
      have h1 : IsPGroup 2 ↥((PU : Subgroup ↥C).map C.subtype) := PU.isPGroup'.map _
      rwa [hPU, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 reeFixedPosUnipotent_le_reeGamma] at h1
    obtain ⟨-, ⟨h1eq, -, -⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hL
    have : IsSimpleGroup ↥(rankOneGroupTwo L a) := (isSimpleGroup_rankOneGroupTwo ha hL).1
    obtain ⟨g, -, hgk⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.ree_levi_hom (K := L) (a := a)
      hUp (CFSG.QuasithinUnique.Setup.X6.f4Index j) (M := rankOneGroupTwo L a)
      (by rw [hj1]; exact h1eq) (isSimpleGroup_rankOneGroupTwo ha hL).2
    have hSz := F4A.not_three_dvd_card_rankOneGroupTwo ha hL
    obtain ⟨h3, hcen⟩ := F4A.three_dvd_card_and_center_eq_bot hPSL
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨yb, hyb⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective yb
    obtain ⟨s, m, hm3, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3
      (by norm_num)
    set x := y ^ m with hx
    have hx3 : x ^ 3 ^ s = 1 := by
      rw [hx, ← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    have hxne : (x : ModO2 (perfectCore P)) ≠ 1 := by
      intro h1
      rw [hx, QuotientGroup.mk_pow, hy] at h1
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hyb] at h2
      exact hm3 h2
    set xK : ↥K := ⟨x, hAK x.2⟩ with hxK
    have hxKP : xK ∈ perfectCore P₀ := hmemP₀ xK x.2
    have hxK3 : xK ^ 3 ^ s = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hxK]
      exact congrArg Subtype.val hx3)
    have hwmem : Φ xK ∈ perfectCore
        ((F4.reeParabolic L a {CFSG.QuasithinUnique.Setup.X6.f4Index j}).subgroupOf C) :=
      hcoreJ' ▸ Subgroup.mem_map_of_mem Φ hxKP
    set w : ↥(perfectCore ((F4.reeParabolic L a
      {CFSG.QuasithinUnique.Setup.X6.f4Index j}).subgroupOf C)) := ⟨Φ xK, hwmem⟩ with hw
    have hw3 : w ^ 3 ^ s = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hw, ← map_pow, hxK3, map_one]
      rfl)
    have hgw : g w = 1 := by
      have h1 : g w ^ 3 ^ s = 1 := by rw [← map_pow, hw3, map_one]
      have h2 : g w ^ Nat.card ↥(rankOneGroupTwo L a) = 1 := pow_card_eq_one'
      have hcop : Nat.Coprime (3 ^ s) (Nat.card ↥(rankOneGroupTwo L a)) :=
        Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hSz)
      have h3' := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h3'
    have hw1 : w = 1 := by
      obtain ⟨k, hk⟩ := hgk ⟨w, hgw⟩
      have h2 : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hcop : Nat.Coprime (3 ^ s) (2 ^ k) := Nat.Coprime.pow s k (by norm_num)
      have h3' := pow_gcd_eq_one.2 ⟨hw3, h2⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h3'
    have hΦx : Φ xK = 1 := congrArg Subtype.val hw1
    have hxZ := hΦker xK hΦx
    apply hxne
    have hxc : (x : ModO2 (perfectCore P)) ∈ Subgroup.center (ModO2 (perfectCore P)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨z', hAK z'.2⟩)
      simpa [hxK] using h1
    rw [hcen, Subgroup.mem_bot] at hxc
    exact hxc

end CFSG.Quasithin.H13.Ch4
