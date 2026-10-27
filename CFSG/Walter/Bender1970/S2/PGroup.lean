module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_24SolvableOddP
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

theorem commutator_le_commutator_commutator {Q : Type*} [Group Q] [Finite Q] (W R : Subgroup Q)
    (hRW : R ≤ Subgroup.normalizer (W : Set Q)) (hcop : Nat.Coprime (Nat.card R) (Nat.card W)) :
    ⁅W, R⁆ ≤ ⁅⁅W, R⁆, R⁆ := by
  classical
  have : Subgroup.Normalizes R W := ⟨hRW⟩
  have h2 : CFSG.commutatorAction₂ (A := R) (G := W) = CFSG.commutatorAction (A := R) (G := W) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := W) (A := R) hcop
  have hmap : (CFSG.commutatorAction (A := R) (G := W)).map W.subtype = ⁅W, R⁆ := by
    simpa using CFSG.commutatorAction_subgroup_conj_map_eq_commutator W R hRW
  have hmap2 : (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype ≤ ⁅⁅W, R⁆, R⁆ := by
    let C : Subgroup W := CFSG.commutatorAction (A := R) (G := W)
    let S : Set W := {x : W | ∃ a : R, ∃ h : W, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype =
          (Subgroup.closure S).map W.subtype := rfl
      _ = Subgroup.closure (W.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := W.subtype) S)
      _ ≤ ⁅⁅W, R⁆, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅W, R⁆, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : Q) ∈ ⁅W, R⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem W.subtype hhC
        have hcomm : ⁅(h : Q)⁻¹, (a : Q)⁆ ∈ ⁅⁅W, R⁆, R⁆ :=
          Subgroup.commutator_mem_commutator ((⁅W, R⁆ : Subgroup Q).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hRW, mul_assoc] using hcomm
  intro x hx
  rw [← hmap, ← h2] at hx
  exact hmap2 hx

theorem conj_eq_inv_of_inf_centralizer_eq_bot {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    {s : G} (hs : s * s = 1) (hsR : s ∈ Subgroup.normalizer (R : Set G))
    (hfix : R ⊓ Subgroup.centralizer ({s} : Set G) = ⊥) {r : G} (hr : r ∈ R) :
    s * r * s⁻¹ = r⁻¹ := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  let φ : R → R := fun x => ⟨(x : G)⁻¹ * (s * x * s⁻¹), R.mul_mem (R.inv_mem x.2)
    ((Subgroup.mem_normalizer_iff.mp hsR x).mp x.2)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (x : G)⁻¹ * (s * x * s⁻¹) = (y : G)⁻¹ * (s * y * s⁻¹) := congrArg Subtype.val hxy
    have h2 : (y : G) * (x : G)⁻¹ ∈ R ⊓ Subgroup.centralizer ({s} : Set G) := by
      refine ⟨R.mul_mem y.2 (R.inv_mem x.2), ?_⟩
      show (y : G) * (x : G)⁻¹ ∈ Subgroup.centralizer ({s} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : s * ((y : G) * (x : G)⁻¹) * s⁻¹ = (y : G) * (x : G)⁻¹ := by
        calc s * ((y : G) * (x : G)⁻¹) * s⁻¹ = (s * y * s⁻¹) * (s * x * s⁻¹)⁻¹ := by group
          _ = (y : G) * (x : G)⁻¹ := by
            rw [show s * (x : G) * s⁻¹ = x * ((y : G)⁻¹ * (s * y * s⁻¹)) by rw [← h1]; group]
            group
      calc (y : G) * (x : G)⁻¹ * s = (s * ((y : G) * (x : G)⁻¹) * s⁻¹) * s := by rw [h3]
        _ = s * ((y : G) * (x : G)⁻¹) := by group
    rw [hfix, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact Subtype.ext h2.symm
  have hφs : Function.Surjective φ := Finite.surjective_of_injective hφ
  obtain ⟨x, hx⟩ := hφs ⟨r, hr⟩
  have hrx : r = (x : G)⁻¹ * (s * x * s⁻¹) := (congrArg Subtype.val hx).symm
  rw [hrx]
  calc s * ((x : G)⁻¹ * (s * x * s⁻¹)) * s⁻¹ = s * (x : G)⁻¹ * s * x * (s * s)⁻¹ := by group
    _ = s * (x : G)⁻¹ * s * x := by rw [hs, inv_one, mul_one]
    _ = s * (x : G)⁻¹ * s⁻¹ * x := by rw [hsinv]
    _ = ((x : G)⁻¹ * (s * x * s⁻¹))⁻¹ := by group

theorem exists_ne_one_ne_of_three_le_card {H : Type*} [Group H] [Finite H] (h3 : 3 ≤ Nat.card H) :
    ∃ a b : H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have := Fintype.ofFinite H
  have : Nontrivial H := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  refine ⟨a, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset H) ⊆ {1, a} := by
    intro y _
    by_cases hy : y = 1
    · rw [Finset.mem_insert]
      exact Or.inl hy
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (hcon y ha hy).symm
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 := Finset.card_le_two (a := (1 : H)) (b := a)
  omega

theorem psl2_even_eq_bot_of_centralizer_le_normalizer {f : ℕ} (hf : 2 ≤ f)
    {ℓ : PSL(2, GaloisField 2 f)} (hℓ : orderOf ℓ = 2) {R : Subgroup PSL(2, GaloisField 2 f)}
    (hRodd : Odd (Nat.card R))
    (hCR : Subgroup.centralizer ({ℓ} : Set PSL(2, GaloisField 2 f)) ≤
      Subgroup.normalizer (R : Set PSL(2, GaloisField 2 f))) : R = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers ℓ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hℓ, pow_one])
  obtain ⟨U, hU⟩ := hp.exists_le_sylow
  have hℓ1 : ℓ ≠ 1 := by rintro rfl; simp at hℓ
  have hCU := psl2_even_centralizer_involution hf U (hU (Subgroup.mem_zpowers ℓ)) hℓ1
  obtain ⟨hUel, hUcard⟩ := psl2_even_sylow_two hf U
  have hUR : (U : Subgroup PSL(2, GaloisField 2 f)) ≤
      Subgroup.normalizer (R : Set PSL(2, GaloisField 2 f)) := hCU ▸ hCR
  have hodd1 : ∀ x ∈ R, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x = 1 := by
    intro x hx k hk
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf x ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    have h4 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right k
        (Nat.coprime_two_right.mpr hRodd))) h1
    exact orderOf_eq_one_iff.mp h4
  have hinv : ∀ u ∈ (U : Subgroup PSL(2, GaloisField 2 f)), u ≠ 1 → ∀ r ∈ R,
      u * r * u⁻¹ = r⁻¹ := by
    intro u hu hu1 r hr
    have huo : orderOf u = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := (U : Subgroup PSL(2, GaloisField 2 f))) u hu) hu1
    have huu : u * u = 1 := by
      have h := pow_orderOf_eq_one u
      rwa [huo, pow_two] at h
    refine conj_eq_inv_of_inf_centralizer_eq_bot huu (hUR hu) ?_ hr
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := psl2_centralizer_isPGroup_of_charTwo huo ⟨x, hx.2⟩
    exact Subgroup.mem_bot.mpr (hodd1 x hx.1 k (by simpa using congrArg Subtype.val hk))
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ha1, hb1, hab⟩ := exists_ne_one_ne_of_three_le_card (H := U) (by
    rw [hUcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    apply Subtype.ext
    have h1 : a * a = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := (U : Subgroup PSL(2, GaloisField 2 f))) a ha
      rwa [pow_two] at this
    show a = b
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = (a * a) * b := by group
      _ = b := by rw [h1, one_mul]
  rw [eq_bot_iff]
  intro r hr
  have h1 := hinv (a * b) ((U : Subgroup PSL(2, GaloisField 2 f)).mul_mem ha hb) hab1 r hr
  have h2 : (a * b) * r * (a * b)⁻¹ = r := by
    calc (a * b) * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
      _ = a * r⁻¹ * a⁻¹ := by rw [hinv b hb hb1' r hr]
      _ = (a * r * a⁻¹)⁻¹ := by group
      _ = r := by rw [hinv a ha ha1' r hr, inv_inv]
  rw [h2] at h1
  refine Subgroup.mem_bot.mpr (hodd1 r hr 1 ?_)
  calc r ^ (2 ^ 1) = r * r := by rw [pow_one, pow_two]
    _ = r * r⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel r

theorem eq_bot_of_le_commutator_of_isTypeL2_or_isTypeJR
    {L : Type} [Group L] [Finite L]
    (hL : IsTypeL2 L ∨ IsTypeJR L) {ℓ : L} (hℓ : orderOf ℓ = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {R : Subgroup L} (hRp : IsPGroup p R) (hR : R ≤ ⁅R, Subgroup.zpowers ℓ⁆)
    (hCR : Subgroup.centralizer ({ℓ} : Set L) ≤ Subgroup.normalizer (R : Set L)) : R = ⊥ := by
  have hRodd : Odd (Nat.card R) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hmaxcase : IsSimpleGroup L → IsCoatom (Subgroup.centralizer ({ℓ} : Set L)) → R = ⊥ := by
    intro hs hmax
    rcases hmax.le_iff.mp hCR with h | h
    · have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h1 | h1
      · exact h1
      · exfalso
        have h2 : 2 ∣ Nat.card L := hℓ ▸ orderOf_dvd_natCard ℓ
        rw [← Subgroup.card_top (G := L), ← h1] at h2
        exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2)
    · have hRC : R ≤ Subgroup.centralizer ({ℓ} : Set L) := h ▸ R.le_normalizer
      have h1 : ⁅R, Subgroup.zpowers ℓ⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hRC hx)).symm k).eq
      exact le_bot_iff.mp (h1 ▸ hR)
  have hevencase : IsTypeL2Even L → R = ⊥ := by
    rintro ⟨f, hf, ⟨e⟩⟩
    have h1 := psl2_even_eq_bot_of_centralizer_le_normalizer hf (ℓ := e ℓ)
      (by rwa [MulEquiv.orderOf_eq]) (R := R.map e.toMonoidHom)
      (by rwa [Subgroup.card_map_of_injective e.injective])
      (by
        rw [← map_centralizer_singleton_mulEquiv, ← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.map_mono hCR)
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  rcases hL with (hev | ⟨p', f, hp', hpodd, hf, h5, h8, ⟨e⟩⟩) | hJR
  · exact hevencase hev
  · by_cases h11 : 11 ≤ p' ^ f
    · have : IsSimpleGroup PSL(2, GaloisField p' f) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
          (by rw [GaloisField.card p' f hf.ne']; omega)
      apply hmaxcase e.isSimpleGroup
      have hmax := psl2_odd_centralizer_involution_isCoatom hpodd hf h11 h8 (t := e ℓ)
        (by rwa [MulEquiv.orderOf_eq])
      have h2 : (Subgroup.centralizer ({e ℓ} : Set PSL(2, GaloisField p' f))).map
          e.symm.toMonoidHom = Subgroup.centralizer ({ℓ} : Set L) := by
        rw [map_centralizer_singleton_mulEquiv, MulEquiv.symm_apply_apply]
      rw [← h2]
      exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e.symm) _).mpr hmax
    · exact hevencase (isTypeL2Even_of_mulEquiv_psl2_five hf (by omega) e)
  · exact hmaxcase hJR.1 (hJR.2.2 ℓ hℓ).1

section ActingAs

variable {Y : Type*} [Group Y]

@[expose] def actingAs (L J : Subgroup Y) (hJL : J ≤ L) : Subgroup Y where
  carrier := {y | y ∈ Subgroup.normalizer (L : Set Y) ∧
    ∃ j ∈ J, ∀ x ∈ L, y * x * y⁻¹ = j * x * j⁻¹}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, j₁, hj₁, h₁⟩ ⟨hy₂, j₂, hj₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hy₁ hy₂, j₁ * j₂, J.mul_mem hj₁ hj₂, fun x hx => ?_⟩
    have hm : j₂ * x * j₂⁻¹ ∈ L := L.mul_mem (L.mul_mem (hJL hj₂) hx) (L.inv_mem (hJL hj₂))
    calc y₁ * y₂ * x * (y₁ * y₂)⁻¹ = y₁ * (y₂ * x * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * (j₂ * x * j₂⁻¹) * y₁⁻¹ := by rw [h₂ x hx]
      _ = j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹ := h₁ _ hm
      _ = j₁ * j₂ * x * (j₁ * j₂)⁻¹ := by group
  one_mem' := ⟨Subgroup.one_mem _, 1, J.one_mem, fun x _ => by group⟩
  inv_mem' := by
    rintro y ⟨hy, j, hj, h⟩
    refine ⟨Subgroup.inv_mem _ hy, j⁻¹, J.inv_mem hj, fun x hx => ?_⟩
    have hz : y⁻¹ * x * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) x).mp hx
      simpa using this
    have h1 := h _ hz
    have h2 : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    rw [h2] at h1
    calc y⁻¹ * x * y⁻¹⁻¹ = y⁻¹ * x * y := by rw [inv_inv]
      _ = j⁻¹ * (j * (y⁻¹ * x * y) * j⁻¹) * j := by group
      _ = j⁻¹ * x * j⁻¹⁻¹ := by rw [← h1, inv_inv]

theorem mem_actingAs {L J : Subgroup Y} (hJL : J ≤ L) {y : Y} :
    y ∈ actingAs L J hJL ↔ y ∈ Subgroup.normalizer (L : Set Y) ∧
      ∃ j ∈ J, ∀ x ∈ L, y * x * y⁻¹ = j * x * j⁻¹ :=
  Iff.rfl

theorem eq_of_conj_eq_of_center_eq_bot {L : Subgroup Y} (hZ : Subgroup.center L = ⊥)
    {a b : Y} (ha : a ∈ L) (hb : b ∈ L) (h : ∀ x ∈ L, a * x * a⁻¹ = b * x * b⁻¹) : a = b := by
  have hc : (⟨b⁻¹ * a, L.mul_mem (L.inv_mem hb) ha⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have h1 := h x x.2
    show (x : Y) * (b⁻¹ * a) = b⁻¹ * a * x
    calc (x : Y) * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  have h2 : b⁻¹ * a = 1 := congrArg Subtype.val hc
  rw [inv_mul_eq_one] at h2
  exact h2.symm

theorem generalizedFittingSubgroupOf_le_actingAs [Finite Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    generalizedFittingSubgroupOf (⊤ : Subgroup Y) ≤ actingAs L L le_rfl := by
  have hLc : CFSG.IsComponent L := (isComponent_iff_isComponentOf_top L).mpr hL
  have hcentral : ∀ y ∈ Subgroup.centralizer (L : Set Y), y ∈ actingAs L L le_rfl := by
    intro y hy
    refine ⟨mem_normalizer_of_mem_centralizer hy, 1, L.one_mem, fun x hx => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hy
    rw [← hy x hx]
    group
  apply sup_le
  ·
    intro f hf
    apply hcentral
    have hfit : CFSG.fittingSubgroupOf (⊤ : Subgroup Y) ≤ CFSG.fittingSubgroup Y :=
      CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top
    have h1 := (CFSG.LocalCores.component_solvable_centralizer (R := CFSG.fittingSubgroup Y)
      inferInstance (CFSG.fittingSubgroup_normal).isSubnormal).1 L hLc
    have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h2 hx) f (hfit hf)).symm
  ·
    refine sSup_le fun K hK => ?_
    rcases CFSG.LocalCores.distinct_components_commute
        ((isComponent_iff_isComponentOf_top K).mpr hK) hLc with rfl | h
    · intro k hk
      exact ⟨Subgroup.le_normalizer hk, k, hk, fun x _ => rfl⟩
    · intro k hk
      apply hcentral
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp (h2 hk) x hx

end ActingAs

theorem eq_one_of_isPGroup_two_of_isPGroup {Y : Type*} [Group Y] {A B : Subgroup Y} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsPGroup 2 A) (hB : IsPGroup p B) {x : Y} (hxA : x ∈ A)
    (hxB : x ∈ B) : x = 1 := by
  obtain ⟨a, ha⟩ := hA ⟨x, hxA⟩
  obtain ⟨b, hb⟩ := hB ⟨x, hxB⟩
  have h1 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2 : orderOf x ∣ p ^ b := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hb)
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem normal_of_isNormalIn_top' {Y : Type*} [Group Y] {K : Subgroup Y} (h : IsNormalIn K ⊤) :
    K.Normal :=
  ⟨fun k hk g => h.2 g trivial k hk⟩

theorem eq_bot_of_isPGroup_of_pPrimeCore_eq_bot
    {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) (hab : HasAbelianSylowTwo Y)
    (htype : ∀ K : Subgroup Y, IsComponentOf K ⊤ → IsTypeL2 K ∨ IsTypeJR K)
    {t : Y} (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup Y}
    (hQp : IsPGroup p Q) (hQ : Q ≤ ⁅Q, Subgroup.zpowers t⁆)
    (hCQ : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (Q : Set Y)) : Q = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := htp.exists_le_sylow
  have htS : t ∈ (S : Subgroup Y) := hS (Subgroup.mem_zpowers t)
  have hSab := hab S
  set F := CFSG.fittingSubgroup Y with hFdef
  set Fst := generalizedFittingSubgroupOf (⊤ : Subgroup Y) with hFst
  have hF2 : IsPGroup 2 F :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO
  have hFt : F ≤ Subgroup.centralizer ({t} : Set Y) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm (hF2.le_sylow_of_normal S hf) htS)
  have hFstn : Fst.Normal := normal_of_isNormalIn_top' (generalizedFittingSubgroupOf_isNormalIn ⊤)
  have htF : t ∈ Fst := sylow_le_generalizedFittingSubgroupOf hO hab S htS
  have hQF : Q ≤ Fst := by
    refine hQ.trans ?_
    rw [Subgroup.commutator_le]
    intro q _ z hz
    have hzF : z ∈ Fst := (Subgroup.zpowers_le.mpr htF) hz
    rw [commutatorElement_def]
    exact Fst.mul_mem (hFstn.conj_mem z hzF q) (Fst.inv_mem hzF)
  have hQFit : Q ≤ Subgroup.centralizer (F : Set Y) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 : f * q * f⁻¹ * q⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCQ (hFt hf)) q).mp hq) (Q.inv_mem hq)
    have h2 : f * q * f⁻¹ * q⁻¹ ∈ F := by
      have : f * q * f⁻¹ * q⁻¹ = f * (q * f⁻¹ * q⁻¹) := by group
      rw [this]
      exact F.mul_mem hf ((CFSG.fittingSubgroup_normal).conj_mem _ (F.inv_mem hf) q)
    have h3 := eq_one_of_isPGroup_two_of_isPGroup hp hp2 hF2 hQp h2 h1
    calc f * q = (f * q * f⁻¹ * q⁻¹) * (q * f) := by group
      _ = q * f := by rw [h3, one_mul]
  have hQL : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Q ≤ Subgroup.centralizer (L : Set Y) := by
    intro L hL
    have hZL : Subgroup.center L = ⊥ := center_eq_bot_of_isComponentOf hO hab hL
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_inner_of_isComponentOf hab S hL htS
    have hinnF := generalizedFittingSubgroupOf_le_actingAs hL
    set N := Subgroup.normalizer (L : Set Y) with hN
    have hQN : Q ≤ N := fun q hq => (hinnF (hQF hq)).1
    have htN : t ∈ N := (hinnF htF).1
    set ρ : N →* MulAut L := L.normalizerMonoidHom with hρ
    set θ : L →* MulAut L := MulAut.conj with hθ
    have hθinj : Function.Injective θ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZL]
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun α : MulAut L => α y) (MonoidHom.mem_ker.mp hx)
      simp only [hθ, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    have hρθ : ∀ (y : N) (k : L), (∀ x ∈ L, (y : Y) * x * (y : Y)⁻¹ = k * x * (k : Y)⁻¹) →
        ρ y = θ k := by
      intro y k h
      ext x
      rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe, hθ, MulAut.conj_apply]
      simpa using h x x.2
    set Q' := Q.subgroupOf N with hQ'
    set t' : N := ⟨t, htN⟩ with ht'
    set ℓ' : L := ⟨ℓ, hℓL⟩ with hℓ'
    have hρt : ρ t' = θ ℓ' := hρθ t' ℓ' hℓ
    set R₀ := Q'.map ρ with hR₀
    have hR₀θ : R₀ ≤ θ.range := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨-, k, hk, hkq⟩ := hinnF (hQF hq)
      exact ⟨⟨k, hk⟩, (hρθ q ⟨k, hk⟩ hkq).symm⟩
    set R := R₀.comap θ with hR
    have hRmap : R.map θ = R₀ := Subgroup.map_comap_eq_self hR₀θ
    have hRp : IsPGroup p R := by
      have hQ'p : IsPGroup p Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
      exact (hQ'p.map ρ).comap_of_injective θ hθinj
    have hRcomm : R ≤ ⁅R, Subgroup.zpowers ℓ'⁆ := by
      rw [← Subgroup.map_le_map_iff_of_injective hθinj, Subgroup.map_commutator,
        MonoidHom.map_zpowers, hRmap, ← hρt, ← MonoidHom.map_zpowers, ← Subgroup.map_commutator]
      apply Subgroup.map_mono
      rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective, Subgroup.map_commutator,
        MonoidHom.map_zpowers, hQ', Subgroup.subgroupOf_map_subtype, inf_of_le_left hQN]
      exact hQ
    have hCR : Subgroup.centralizer ({ℓ'} : Set L) ≤ Subgroup.normalizer (R : Set L) := by
      intro c hc
      have hct : (c : Y) ∈ Subgroup.centralizer ({t} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hℓ c c.2
        have h2 : (c : Y) * ℓ = ℓ * c := congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp hc)
        have h3 : ℓ * (c : Y) * ℓ⁻¹ = c := by rw [← h2, mul_inv_cancel_right]
        calc (c : Y) * t = (t * c * t⁻¹) * t := by rw [h1, h3]
          _ = t * c := by group
      have hcN : (c : Y) ∈ N := Subgroup.le_normalizer c.2
      have hcQ' : (⟨c, hcN⟩ : N) ∈ Subgroup.normalizer (Q' : Set N) := by
        rw [hQ', ← Subgroup.subgroupOf_normalizer_eq hQN, Subgroup.mem_subgroupOf]
        exact hCQ hct
      have h1 : ρ ⟨c, hcN⟩ ∈ Subgroup.normalizer (R₀ : Set (MulAut L)) :=
        Subgroup.le_normalizer_map ρ ⟨_, hcQ', rfl⟩
      have h2 : ρ ⟨c, hcN⟩ = θ c := hρθ ⟨c, hcN⟩ c (fun x _ => rfl)
      rw [h2] at h1
      exact Subgroup.le_normalizer_comap θ h1
    have hR1 : R = ⊥ := by
      by_cases hℓ1 : ℓ' = 1
      · rw [hℓ1, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right] at hRcomm
        exact le_bot_iff.mp hRcomm
      · have hℓ2 : orderOf ℓ' = 2 := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          refine orderOf_eq_prime (hθinj ?_) hℓ1
          rw [map_pow, ← hρt, ← map_pow, map_one]
          have ht2 : t' ^ 2 = 1 := by
            apply Subtype.ext
            have h := pow_orderOf_eq_one t
            rw [ht] at h
            simpa using h
          rw [ht2, map_one]
        exact eq_bot_of_le_commutator_of_isTypeL2_or_isTypeJR (htype L hL) hℓ2 hp hp2 hRp
          hRcomm hCR
    have hR₀1 : R₀ = ⊥ := by rw [← hRmap, hR1, Subgroup.map_bot]
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : ρ ⟨q, hQN hq⟩ = 1 := by
      have : ρ ⟨q, hQN hq⟩ ∈ R₀ := ⟨⟨q, hQN hq⟩, hq, rfl⟩
      rwa [hR₀1, Subgroup.mem_bot] at this
    have h2 : ((ρ ⟨q, hQN hq⟩ ⟨x, hx⟩ : L) : Y) = x := by rw [h1]; rfl
    have h3 := Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨q, hQN hq⟩ ⟨x, hx⟩
    rw [← hρ, h2] at h3
    calc x * q = (q * x * q⁻¹) * q := by rw [← h3]
      _ = q * x := by group
  have hQC : Q ≤ Subgroup.centralizer (Fst : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ (sSup_le fun L hL => ?_)
    · have hfit : CFSG.fittingSubgroupOf (⊤ : Subgroup Y) ≤ F :=
        CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top
      exact hfit.trans (Subgroup.le_centralizer_iff.mp hQFit)
    · exact Subgroup.le_centralizer_iff.mp (hQL L hL)
  have hQFfit : Q ≤ CFSG.fittingSubgroupOf (⊤ : Subgroup Y) := fun q hq =>
    centralizer_generalizedFitting_intersection_le_fittingSubgroupOf ⟨hQC hq, hQF hq⟩
  have hfit : CFSG.fittingSubgroupOf (⊤ : Subgroup Y) ≤ F :=
    CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top
  rw [eq_bot_iff]
  intro q hq
  exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_two_of_isPGroup hp hp2 hF2 hQp (hfit (hQFfit hq))
    hq)

theorem centralizer_zpowers_eq' {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem commutator_zpowers_le_of_mem_normalizer {G : Type*} [Group G] {Q : Subgroup G} {t : G}
    (htQ : t ∈ Subgroup.normalizer (Q : Set G)) : ⁅Q, Subgroup.zpowers t⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq z hz
  have hzQ : z ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr htQ) hz
  rw [commutatorElement_def]
  have h1 : q * z * q⁻¹ * z⁻¹ = q * (z * q⁻¹ * z⁻¹) := by group
  rw [h1]
  exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp hzQ q⁻¹).mp (Q.inv_mem hq))

theorem mem_normalizer_commutator {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (A : Set G) →
      g ∈ Subgroup.normalizer (B : Set G) → ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hA hB x hx
    have h1 : ⁅A, B⁆.map (MulAut.conj g).toMonoidHom ≤ ⁅A, B⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hA a).mp ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hB b).mp hb
    exact h1 ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hA hB x, fun hx => ?_⟩
  have h := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hx
  simpa [mul_assoc] using h

theorem le_pCore_of_isPGroup_of_le_commutator
    {X : Type} [Group X] [Finite X] (hX : IsAStar X)
    {t : X} (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQp : IsPGroup p Q) (hQ : Q ≤ ⁅Q, Subgroup.zpowers t⁆)
    (hCQ : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (Q : Set X)) :
    Q ≤ pCore p X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set O := pPrimeCore 2 X with hOdef
  set q : X →* X ⧸ O := QuotientGroup.mk' O with hq
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have htC : t ∈ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hQeq : ⁅Q, Subgroup.zpowers t⁆ = Q :=
    le_antisymm (commutator_zpowers_le_of_mem_normalizer (hCQ htC)) hQ
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htO : t ∉ O := by
    intro h
    have h2 : 2 ∣ Nat.card O := ht ▸ Subgroup.orderOf_dvd_natCard O h
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  have hQO : Q ≤ O := by
    set Qb := Q.map q with hQb
    have htb : orderOf (q t) = 2 := by
      have h1 : q t ≠ 1 := by
        rw [hq, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
        exact htO
      have h2 : (q t) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one t
        rw [ht] at h
        rw [← map_pow, h, map_one]
      exact orderOf_eq_prime h2 h1
    have hQbp : IsPGroup p Qb := hQp.map q
    have hQb1 : Qb ≤ ⁅Qb, Subgroup.zpowers (q t)⁆ := by
      rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hQ
    have hCQb : Subgroup.centralizer ({q t} : Set (X ⧸ O)) ≤
        Subgroup.normalizer (Qb : Set (X ⧸ O)) := by
      have : Fact (IsPGroup 2 (Subgroup.zpowers t)) := ⟨htp⟩
      have hC := centralizer_map_quotient_eq_map_centralizer (p := 2) (Subgroup.zpowers t) O
        inferInstance (Nat.coprime_two_left.mpr hOodd)
      simp only at hC
      rw [MonoidHom.map_zpowers] at hC
      have hC1 : Subgroup.centralizer ({q t} : Set (X ⧸ O)) =
          (Subgroup.centralizer ({t} : Set X)).map q := by
        rw [← centralizer_zpowers_eq', ← centralizer_zpowers_eq']
        exact hC
      rw [hC1]
      exact (Subgroup.map_mono hCQ).trans (Subgroup.le_normalizer_map q)
    have hQbot := eq_bot_of_isPGroup_of_pPrimeCore_eq_bot
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (hX.1.quotient O)
      (fun K hK => (hX.2.2 K hK).2) htb hp hp2 hQbp hQb1 hCQb
    have := (Subgroup.map_eq_bot_iff _).mp hQbot
    rwa [hq, QuotientGroup.ker_mk'] at this
  set Y₀ := O ⊔ Subgroup.zpowers t with hY₀
  have hOY : O ≤ Y₀ := le_sup_left
  have htY : t ∈ Y₀ := (le_sup_right : Subgroup.zpowers t ≤ Y₀) (Subgroup.mem_zpowers t)
  have hQY : Q ≤ Y₀ := hQO.trans hOY
  set O' := O.subgroupOf Y₀ with hO'
  set t' : Y₀ := ⟨t, htY⟩ with ht'
  have hY₀solv : Group.IsSolvable Y₀ := by
    have hO'solv : Group.IsSolvable O' := by
      have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hOY).symm.toMonoidHom) (MulEquiv.surjective _)
    have hgen : ∀ y : Y₀, ∃ k : ℤ,
        (QuotientGroup.mk y : Y₀ ⧸ O') = (QuotientGroup.mk t' : Y₀ ⧸ O') ^ k := by
      intro y
      have hy : (y : X) ∈ Subgroup.zpowers t ⊔ O := by rw [sup_comm]; exact y.2
      obtain ⟨z, hz, o, ho, hzo⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 : ((y⁻¹ * t' ^ k : Y₀) : X) = o⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, ← hzo]
        show (t ^ k * o)⁻¹ * t ^ k = o⁻¹
        group
      rw [h1]
      exact O.inv_mem ho
    have hQsolv : Group.IsSolvable (Y₀ ⧸ O') := by
      refine Group.isSolvable_of_comm fun a b => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨i, hi⟩ := hgen x
      obtain ⟨j, hj⟩ := hgen y
      rw [hi, hj, ← zpow_add, ← zpow_add, add_comm]
    exact Group.isSolvable_of_ker_le_range O'.subtype (QuotientGroup.mk' O')
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have ht'inv : BenderSuzuki.PFAppendixIII.IsInvolution t' := by
    refine ⟨fun h => ?_, Subtype.ext ?_⟩
    · have h1 : t = 1 := congrArg Subtype.val h
      rw [h1, orderOf_one] at ht
      omega
    · have h := pow_orderOf_eq_one t
      rw [ht] at h
      simpa using h
  set Q' := Q.subgroupOf Y₀ with hQ'
  have hQ'p : IsPGroup p Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQY).symm
  have hCQ' : Subgroup.centralizer ({t'} : Set Y₀) ≤ Subgroup.normalizer (Q' : Set Y₀) := by
    intro y hy
    rw [hQ', ← Subgroup.subgroupOf_normalizer_eq hQY, Subgroup.mem_subgroupOf]
    apply hCQ
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact congrArg Subtype.val hy
  have hQ'comm : ⁅Q', Subgroup.zpowers t'⁆ = Q' := by
    apply Subgroup.map_injective Y₀.subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hQ', Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hQY]
    exact hQeq
  have h1 := GorensteinWalter.bender1970_2_4_solvable_oddP_selfCommutator_le_pCore Q' p
    hY₀solv hp (hp.odd_of_ne_two hp2) (hX.1.subgroup Y₀) ht'inv hQ'p hCQ' hQ'comm
  set P₁ := (pCore p Y₀).map Y₀.subtype ⊓ O with hP₁
  have hP₁p : IsPGroup p P₁ := ((pCore_isPGroup (p := p) (G := Y₀)).map Y₀.subtype).to_le
    inf_le_left
  have hle1 : P₁.subgroupOf O ≤ pCore p O := by
    apply le_sSup
    refine ⟨⟨fun x hx g => ?_⟩, hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨⟨y, hyp, hyx⟩, hxO⟩ := hx
    refine ⟨⟨⟨g, hOY g.2⟩ * y * ⟨g, hOY g.2⟩⁻¹, ?_, ?_⟩, ?_⟩
    · exact (pCore_normal (p := p) (G := Y₀)).conj_mem y hyp _
    · rw [Subgroup.coe_subtype] at hyx ⊢
      simp [hyx]
    · exact O.mul_mem (O.mul_mem g.2 hxO) (O.inv_mem g.2)
  have hle2 : (pCore p O).map O.subtype ≤ pCore p X := by
    apply le_sSup
    refine ⟨⟨fun x hx g => conj_mem_map_of_characteristic ?_ hx⟩,
      (pCore_isPGroup (p := p) (G := O)).map O.subtype⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  intro x hx
  have hxP₁ : x ∈ P₁ := ⟨⟨⟨x, hQY hx⟩, h1 hx, rfl⟩, hQO hx⟩
  exact hle2 ⟨⟨x, hQO hx⟩, hle1 hxP₁, rfl⟩

theorem bender1970_2_4_pGroup
    {X : Type} [Group X] [Finite X] (hX : IsAStar X) {t : X}
    (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hPp : IsPGroup p P)
    (hCP : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X)) :
    ⁅P, Subgroup.zpowers t⁆ ≤ pCore p X := by
  have : Fact p.Prime := ⟨hp⟩
  have htP : t ∈ Subgroup.normalizer (P : Set X) :=
    hCP (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hQP : ⁅P, Subgroup.zpowers t⁆ ≤ P := commutator_zpowers_le_of_mem_normalizer htP
  have hQp : IsPGroup p (⁅P, Subgroup.zpowers t⁆ : Subgroup X) := hPp.to_le hQP
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card P) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [Nat.card_zpowers, ht, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hQ : ⁅P, Subgroup.zpowers t⁆ ≤ ⁅⁅P, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ :=
    commutator_le_commutator_commutator P (Subgroup.zpowers t) (Subgroup.zpowers_le.mpr htP) hcop
  have hCQ : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer ((⁅P, Subgroup.zpowers t⁆ : Subgroup X) : Set X) := by
    intro c hc
    refine mem_normalizer_commutator (hCP hc) (mem_normalizer_of_mem_centralizer ?_)
    rw [centralizer_zpowers_eq']
    exact hc
  exact le_pCore_of_isPGroup_of_le_commutator hX ht hp hp2 hQp hQ hCQ

theorem bender1970_2_4_pGroup_subgroup
    {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) {t : G} (htH : t ∈ H) (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup G} (hPH : P ≤ H) (hPp : IsPGroup p P)
    (hCP : H ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (P : Set G)) :
    ⁅P, Subgroup.zpowers t⁆ ≤ qCoreOf H p := by
  set t' : H := ⟨t, htH⟩
  set P' := P.subgroupOf H
  have hP'p : IsPGroup p P' := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hCP' : Subgroup.centralizer ({t'} : Set H) ≤ Subgroup.normalizer (P' : Set H) := by
    intro x hx
    rw [← Subgroup.subgroupOf_normalizer_eq hPH, Subgroup.mem_subgroupOf]
    apply hCP
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  have h1 := bender1970_2_4_pGroup hH (t := t') (by rw [Subgroup.orderOf_mk]; exact ht) hp hp2
    hP'p hCP'
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rwa [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hPH] at h2

end CFSG.Walter
