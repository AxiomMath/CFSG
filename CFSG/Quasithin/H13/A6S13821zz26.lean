module

public import CFSG.Quasithin.H13.A6S1388
public import CFSG.Quasithin.Background.B1Transvection
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6S20

theorem index_fixV_zpowers_le_two {W : Type} [CommGroup W] [Finite W] {a : MulAut W} {e : W}
    (he : ∀ w : W, a w * w⁻¹ = 1 ∨ a w * w⁻¹ = e) :
    (fixV (Subgroup.zpowers a)).index ≤ 2 := by
  classical
  let f : W →* W :=
    { toFun := fun v => a v * v⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel }
  have hker : f.ker = fixV (Subgroup.zpowers a) := by
    ext v
    rw [MonoidHom.mem_ker]
    change a v * v⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    constructor
    · intro h g hg
      have hinv : a⁻¹ v = v := by
        have := MulAut.inv_apply_self W a v
        rwa [h] at this
      have hpow : ∀ k : ℤ, (a ^ k) v = v := by
        intro k
        induction k using Int.induction_on with
        | zero => rfl
        | succ k ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
        | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, hinv, ih]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact hpow k
    · intro h
      exact h a (Subgroup.mem_zpowers a)
  rw [← hker, Subgroup.index_ker]
  calc Nat.card (Set.range f) ≤ Nat.card ({1, e} : Set W) :=
        Nat.card_mono (Set.toFinite _) (by
          rintro _ ⟨v, rfl⟩
          rcases he v with h | h
          · exact Or.inl h
          · exact Or.inr h)
    _ ≤ 2 := by
        rw [Nat.card_eq_card_toFinset]
        refine (Finset.card_le_two (a := (1 : W)) (b := e)).trans_eq' ?_
        congr 1
        ext x
        simp

theorem pow_mul_inv_mem_13820b {G : Type} [Group G] {K : Subgroup G} {t k : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) (n : ℕ) :
    (t * k) ^ n * (t ^ n)⁻¹ ∈ K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : t ^ (n + 1) * k * (t ^ (n + 1))⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht (n + 1)) k).mp hk
    have e : (t * k) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
        ((t * k) ^ n * (t ^ n)⁻¹) * (t ^ (n + 1) * k * (t ^ (n + 1))⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact K.mul_mem ih h1

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_pCoreOf_of_ker_13820b {H : Subgroup G} {K : Subgroup G}
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ T) {M : Type*} [Group M]
    (ρ : ↥H →* M) (hK : ∀ h : ↥H, (h : G) ∈ K → ρ h = 1 → (h : G) ∈ pCoreOf 2 H) (h : ↥H)
    (h1 : ρ h = 1) :
    (h : G) ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := ρ.ker.map H.subtype with hC
  have hCH : C ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨g, hg⟩ * x * (⟨g, hg⟩ : ↥H)⁻¹, ρ.normal_ker.conj_mem x hx _, rfl⟩
    · rintro ⟨y, hy, hyc⟩
      refine ⟨(⟨g, hg⟩ : ↥H)⁻¹ * y * ⟨g, hg⟩, ?_, ?_⟩
      · have := ρ.normal_ker.conj_mem y hy ((⟨g, hg⟩ : ↥H)⁻¹)
        simpa using this
      · have hyc' : (y : G) = g * c * g⁻¹ := hyc
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hyc']
        group
  have hKC : K ⊓ C ≤ pCoreOf 2 H := by
    rintro _ ⟨hk, x, hx, rfl⟩
    exact hK x hk hx
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hTn : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hKn
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right T K hTn
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hCp : IsPGroup 2 C := by
    intro c
    have hc' : (c : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm, ← hHK]
      exact hCH c.2
    rw [hset] at hc'
    obtain ⟨t, ht, k, hk, htk⟩ := hc'
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have h1 := A6S20.pow_mul_inv_mem_13820b (hTn ht) hk (2 ^ a)
    have htk' : t * k = (c : G) := htk
    rw [hta, inv_one, mul_one, htk'] at h1
    have h3 : (c : G) ^ 2 ^ a ∈ pCoreOf 2 H := hKC ⟨h1, C.pow_mem c.2 _⟩
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 H ⟨_, h3⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((c : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  exact le_pCoreOf_of_le_normalizer 2 hCH hCn hCp ⟨h, h1, rfl⟩

theorem false_of_section_13820b (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ T)
    {W : Type} [CommGroup W] [Finite W] (ρ : ↥H →* MulAut W) {X : Subgroup G}
    (hXU : X ≤ conjClosure S.V3 H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (π : ↥X →* W) (hπ : Function.Surjective π)
    (hπV : ∀ x : ↥X, (x : G) ∈ fsuV1 T V → π x = 1)
    (hρπ : ∀ (h : ↥H) (x : ↥X) (hx : (h : G) * x * (h : G)⁻¹ ∈ X),
      ρ h (π x) = π ⟨(h : G) * x * (h : G)⁻¹, hx⟩)
    (hK : ∀ h : ↥H, (h : G) ∈ K → ρ h = 1 → (h : G) ∈ pCoreOf 2 H)
    (hmod : ∀ A : Subgroup (MulAut W), A ≤ ρ.range → IsElemAbelian2 A →
      ∀ D : Subgroup W, D.index ≤ Nat.card ↥A → ∀ a₁ : W,
        (∀ d ∈ D, ∀ a ∈ A, a d * d⁻¹ ∈ Subgroup.zpowers a₁) → A = ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hconj : ∀ (h : ↥H) (x : G), x ∈ X → (h : G) * x * (h : G)⁻¹ ∈ X := fun h x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHX h.2) x).mp hx
  have hcomm : ∀ (h : ↥H) (x : ↥X), ρ h (π x) * (π x)⁻¹ =
      π ⟨(h : G) * x * (h : G)⁻¹ * (x : G)⁻¹, X.mul_mem (hconj h x x.2) (X.inv_mem x.2)⟩ := by
    intro h x
    rw [hρπ h x (hconj h x x.2), ← map_inv, ← map_mul]
    rfl
  have hXel : IsElemAbelian 2 X :=
    F7.isElemAbelian_mono hF.F911_2 (hXU.trans (conjClosure_mono S.V3_le_V le_rfl))
  have hW2 : ∀ w : W, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := hπ w
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using F7.isElemAbelian_pow_eq_one hXel x.2)
    rw [← map_pow, hx2, map_one]
  have hQ : ∀ h : ↥H, (h : G) ∈ pCoreOf 2 H → ρ h = 1 := by
    intro h hh
    rw [hF1.pCoreOf_eq_centralizerMod] at hh
    refine MulEquiv.ext fun w => ?_
    obtain ⟨x, rfl⟩ := hπ w
    have h1 : ρ h (π x) * (π x)⁻¹ = 1 := by
      rw [hcomm]
      exact hπV _ (hh.2.2 x (hXU x.2))
    rw [MulAut.one_apply]
    exact mul_inv_eq_one.mp h1
  have hfaith := S.mem_pCoreOf_of_ker_13820b hKn hHK ρ hK
  have hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V) := by
    intro h hh htr
    obtain ⟨hnot, c, hc⟩ := htr
    apply hnot
    suffices hρ : ρ ⟨h, hh⟩ = 1 by
      have h1 := hfaith _ hρ
      rw [hF1.pCoreOf_eq_centralizerMod] at h1
      exact h1.2.2
    by_contra ha
    set a := ρ ⟨h, hh⟩ with ha_def
    obtain ⟨e, he⟩ : ∃ e : W, ∀ w : W, a w * w⁻¹ = 1 ∨ a w * w⁻¹ = e := by
      by_cases hall : ∀ x : ↥X, h * x * h⁻¹ * (x : G)⁻¹ ∈ fsuV1 T V
      · refine ⟨1, fun w => Or.inl ?_⟩
        obtain ⟨x, rfl⟩ := hπ w
        rw [ha_def, hcomm]
        exact hπV _ (hall x)
      · push Not at hall
        obtain ⟨x₀, hx₀⟩ := hall
        have h0 := (hc x₀ (hXU x₀.2)).resolve_left hx₀
        refine ⟨π ⟨h * x₀ * h⁻¹ * (x₀ : G)⁻¹,
          X.mul_mem (hconj ⟨h, hh⟩ x₀ x₀.2) (X.inv_mem x₀.2)⟩, fun w => ?_⟩
        obtain ⟨x, rfl⟩ := hπ w
        rw [ha_def, hcomm]
        rcases hc x (hXU x.2) with h1 | h1
        · exact Or.inl (hπV _ h1)
        · right
          rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
          apply hπV
          have e1 : h * x * h⁻¹ * (x : G)⁻¹ * (h * x₀ * h⁻¹ * (x₀ : G)⁻¹)⁻¹ =
              (h * x * h⁻¹ * (x : G)⁻¹ * c⁻¹) * (h * x₀ * h⁻¹ * (x₀ : G)⁻¹ * c⁻¹)⁻¹ := by
            group
          change h * x * h⁻¹ * (x : G)⁻¹ * (h * x₀ * h⁻¹ * (x₀ : G)⁻¹)⁻¹ ∈ fsuV1 T V
          rw [e1]
          exact (fsuV1 T V).mul_mem h1 ((fsuV1 T V).inv_mem h0)
    have he1 : e ≠ 1 := by
      intro he1
      apply ha
      refine MulEquiv.ext fun w => ?_
      rw [MulAut.one_apply]
      rcases he w with h1 | h1
      · exact mul_inv_eq_one.mp h1
      · rw [he1] at h1
        exact mul_inv_eq_one.mp h1
    have htv : IsTransvectionWith a e := ⟨he1, fun w => by
      rcases he w with h1 | h1
      · exact Or.inl (mul_inv_eq_one.mp h1)
      · right
        rw [← h1, mul_comm, inv_mul_cancel_right]⟩
    have ha2 : a * a = 1 := B1.tv_sq hW2 htv ha
    have hAel : IsElemAbelian2 (Subgroup.zpowers a) := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ha2, one_zpow]
    have hAle : Subgroup.zpowers a ≤ ρ.range :=
      (Subgroup.zpowers_le).mpr ⟨⟨h, hh⟩, rfl⟩
    have hcA : Nat.card ↥(Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq]; exact ha2) ha
    have hbot := hmod _ hAle hAel (fixV (Subgroup.zpowers a))
      (hcA ▸ A6S20.index_fixV_zpowers_le_two he) 1 (fun d hd a' ha' => by
        rw [hd a' ha', mul_inv_cancel]
        exact Subgroup.one_mem _)
    apply ha
    have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨γ, γ', g, s, hDγ, -, -, hle, -⟩ := S.case2_of_no_transv hF hnt
  set Uγ := F8.Uγ S.V3 H (g : G) with hUγ
  have hUγH : Uγ ≤ H := hF.Uγ_le_H s
  have hUγel : IsElemAbelian 2 Uγ :=
    F7.isElemAbelian_mono (hF.isElemAbelian_Vγ (g := g)) (hF.Uγ_le_Vγ (g := g))
  have hUγ2 : IsPGroup 2 ↥Uγ := fun x =>
    ⟨1, Subtype.ext (by simpa using F7.isElemAbelian_pow_eq_one hUγel x.2)⟩
  set A : Subgroup (MulAut W) := (Uγ.subgroupOf H).map ρ with hA
  have hAel : IsElemAbelian2 A := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (F7.isElemAbelian_comm hUγel (Subgroup.mem_subgroupOf.mp hx)
        (Subgroup.mem_subgroupOf.mp hy))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have hx2 : x ^ 2 = 1 := Subtype.ext (by
        simpa using F7.isElemAbelian_pow_eq_one hUγel (Subgroup.mem_subgroupOf.mp hx))
      rw [hx2, map_one]
  have hkerρ : ρ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨hfaith x, hQ x⟩
  have hcardA : Nat.card ↥A = 2 ^ mIdx Uγ (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by
    have h1 : Nat.card ↥A = ρ.ker.relIndex (Uγ.subgroupOf H) := by
      rw [hA, ← MonoidHom.domRestrict_range, ← Subgroup.index_ker, MonoidHom.ker_domRestrict]
      rfl
    rw [h1, hkerρ, Subgroup.relIndex_subgroupOf hUγH, ← HypF98.relIndex_eq_two_pow_mIdx hUγ2,
      hF.Dγ_eq_inf_pCoreOf s, Subgroup.inf_relIndex_left]
  set DH := F8.DH S.V3 (fsuV1 T V) H (g : G) with hDHdef
  set D : Subgroup W := ((DH ⊓ X).subgroupOf X).map π with hD
  have hDidx : D.index ≤ Nat.card ↥A := by
    have h1 : D.index ∣ ((DH ⊓ X).subgroupOf X).index := Subgroup.index_map_dvd _ hπ
    have h2 : ((DH ⊓ X).subgroupOf X).index = DH.relIndex X := Subgroup.inf_relIndex_right DH X
    have hU2 : IsPGroup 2 ↥(conjClosure S.V3 H) :=
      (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
    have h4 : DH.relIndex (conjClosure S.V3 H) = 2 ^ mIdx (conjClosure S.V3 H) DH :=
      HypF98.relIndex_eq_two_pow_mIdx hU2
    have h3 : DH.relIndex X ≤ DH.relIndex (conjClosure S.V3 H) :=
      Subgroup.relIndex_le_of_le_right hXU (by rw [h4]; positivity)
    have h5 : 2 ^ mIdx (conjClosure S.V3 H) DH ≤ 2 ^ mIdx Uγ (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) :=
      Nat.pow_le_pow_right (by norm_num) hle
    have h6 := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
    rw [hcardA]
    omega
  have hA₁ : Nat.card ↥(F8.A₁ (fsuV1 T V) (g : G)) = 2 := hF.card_A₁
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : W, ∀ (y : G) (hy : y ∈ X), y ∈ F8.A₁ (fsuV1 T V) (g : G) →
      π ⟨y, hy⟩ ∈ Subgroup.zpowers a₁ := by
    by_cases hex : ∃ y ∈ X, y ∈ F8.A₁ (fsuV1 T V) (g : G) ∧ y ≠ 1
    · obtain ⟨y₀, hy₀X, hy₀A, hy₀1⟩ := hex
      have hzp : Subgroup.zpowers y₀ = F8.A₁ (fsuV1 T V) (g : G) := by
        apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hy₀A)
        rw [hA₁, Nat.card_zpowers]
        have hpos := orderOf_pos y₀
        have hne : orderOf y₀ ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        omega
      refine ⟨π ⟨y₀, hy₀X⟩, fun y hy hyA => ?_⟩
      rw [← hzp] at hyA
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyA
      have e1 : (⟨y₀ ^ k, hy⟩ : ↥X) = ⟨y₀, hy₀X⟩ ^ k := Subtype.ext (by simp)
      rw [e1, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ k
    · push Not at hex
      refine ⟨1, fun y hy hyA => ?_⟩
      obtain rfl : y = 1 := hex y hy hyA
      have e1 : (⟨1, hy⟩ : ↥X) = 1 := rfl
      rw [e1, map_one]
      exact Subgroup.one_mem _
  have hDA : ∀ d ∈ D, ∀ a ∈ A, a d * d⁻¹ ∈ Subgroup.zpowers a₁ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [hcomm]
    apply ha₁
    have hxD : (x : G) ∈ DH := (Subgroup.mem_subgroupOf.mp hx).1
    have huU : (u : G) ∈ Uγ := Subgroup.mem_subgroupOf.mp hu
    have h1 := (F8.A₁ (fsuV1 T V) (g : G)).inv_mem (hxD.2.2 u huU)
    rwa [show ((x : G) * u * (x : G)⁻¹ * (u : G)⁻¹)⁻¹ =
      (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ by group] at h1
  have hbot := hmod A (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩) hAel D hDidx a₁ hDA
  apply hDγ.ne
  refine le_antisymm (centralizerMod_le_left _ _ _) fun u hu => ?_
  have h1 : ρ ⟨u, hUγH hu⟩ ∈ A := ⟨⟨u, hUγH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  rw [hF.Dγ_eq_inf_pCoreOf s]
  exact ⟨hu, hfaith _ h1⟩

end Setting4

end CFSG.Quasithin.H13.A6
