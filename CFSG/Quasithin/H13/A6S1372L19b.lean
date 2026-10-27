module

public import CFSG.Quasithin.H13.A6S1372L19a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace A6L19

variable {G : Type} [Group G]

@[expose] def vbar (T K : Subgroup G) (α : ↥K →* alternatingGroup (Fin 5)) :
    Subgroup (Perm (Fin 5)) :=
  ((T ⊓ K).subgroupOf K).map ((alternatingGroup (Fin 5)).subtype.comp α)

theorem mem_vbar {T K : Subgroup G} {α : ↥K →* alternatingGroup (Fin 5)} {x : Perm (Fin 5)} :
    x ∈ vbar T K α ↔ ∃ s : ↥K, (s : G) ∈ T ∧ (α s : Perm (Fin 5)) = x := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, (Subgroup.mem_subgroupOf.mp hs).1, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Subgroup.mem_subgroupOf.mpr ⟨hs, s.2⟩, rfl⟩

theorem mem_normalizer_of_conj [Finite G] {Y : Subgroup G} {x : G}
    (h : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) : x ∈ Subgroup.normalizer (Y : Set G) := by
  let f : ↥Y → ↥Y := fun y => ⟨x * (y : G) * x⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h1 : x * (a : G) * x⁻¹ = x * (b : G) * x⁻¹ := congrArg Subtype.val hab
    simpa using h1
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨s, hs⟩ := hsurj ⟨x * y * x⁻¹, hy⟩
  have hs' : x * (s : G) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hs
  have : (s : G) = y := by simpa using hs'
  rw [← this]
  exact s.2

theorem mem_sup_iff {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAB, Set.mem_mul]
  rfl

theorem pow_four_pow_eq {M : Type*} [Monoid M] {x : M} (h3 : x ^ 3 = 1) (a : ℕ) :
    x ^ (4 ^ a) = x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]

theorem conj_mem_of_normKl {a b σ : Perm (Fin 5)} {D : Subgroup (Perm (Fin 5))}
    (hV : ∀ x, x ∈ D ↔ x ∈ kl a b) (hn : NormKl a b σ) {v : Perm (Fin 5)}
    (hv : v ∈ D) : σ * v * σ⁻¹ ∈ D := by
  have ha : σ * a * σ⁻¹ ∈ D := (hV _).2 hn.1
  have hb : σ * b * σ⁻¹ ∈ D := (hV _).2 hn.2
  have hv' := (hV v).1 hv
  simp only [kl, List.mem_cons, List.not_mem_nil, or_false] at hv'
  rcases hv' with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact D.one_mem
  · exact ha
  · exact hb
  · have e : σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) := by group
    rw [e]
    exact D.mul_mem ha hb

section Gam

variable {H K T : Subgroup G}

theorem gam_T_conj_vbar (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (t : ↥H) (ht : (t : G) ∈ T)
    {x : Perm (Fin 5)} (hx : x ∈ vbar T K α) :
    gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk t * x *
      (gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk t)⁻¹ ∈ vbar T K α := by
  obtain ⟨s, hsT, rfl⟩ := mem_vbar.1 hx
  rw [gam5_conj]
  refine mem_vbar.2 ⟨_, ?_, rfl⟩
  rw [AutA6Rank.conjK_coe]
  exact T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht)

theorem TK_le_normalizer_QH (hKH : K ≤ H) :
    T ⊓ K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  inf_le_right.trans (hKH.trans (le_normalizer_pCoreOf 2 H))

theorem mem_N0_of_gam (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hfT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H)
    (x : ↥H) (hxT : (x : G) ∈ T)
    (hx : gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk x ∈ vbar T K α) :
    (x : G) ∈ T ⊓ K ⊔ pCoreOf 2 H := by
  obtain ⟨s, hsT, hs⟩ := mem_vbar.1 hx
  have hs' : gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk ⟨s, hKH s.2⟩ =
      gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk x := by
    rw [gam5_of_mem, hs]
  have h1 : gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk (⟨s, hKH s.2⟩⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hs', inv_mul_cancel]
  rw [gam5_eq_one_iff] at h1
  have hmem : (s : G)⁻¹ * x ∈ pCoreOf 2 H := hfT _ (T.mul_mem (T.inv_mem hsT) hxT) h1
  have e : (x : G) = s * ((s : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hsT, s.2⟩) (Subgroup.mem_sup_right hmem)

theorem mem_normalizer_N0_of_gam_one [Finite G] (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (x : ↥H)
    (hx : gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk x = 1) :
    (x : G) ∈ Subgroup.normalizer ((T ⊓ K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  rw [gam5_eq_one_iff] at hx
  refine mem_normalizer_of_conj fun y hy => ?_
  obtain ⟨s, hs, p, hp, rfl⟩ := (mem_sup_iff (TK_le_normalizer_QH (T := T) hKH)).1 hy
  have hq : (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ pCoreOf 2 H := hx s hs.2
  have hxp : (x : G) * p * (x : G)⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H x.2) p).mp hp
  have e : (x : G) * (s * p) * (x : G)⁻¹ =
      ((x : G) * s * (x : G)⁻¹ * s⁻¹) * s * ((x : G) * p * (x : G)⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hq)
    (Subgroup.mem_sup_left hs)) (Subgroup.mem_sup_right hxp)

theorem mem_normalizer_N0_of_K [Finite G] (hKH : K ≤ H) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (k : ↥K)
    (hk : ∀ v ∈ vbar T K α, (α k : Perm (Fin 5)) * v * (α k : Perm (Fin 5))⁻¹ ∈ vbar T K α) :
    (k : G) ∈ Subgroup.normalizer ((T ⊓ K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj fun y hy => ?_
  obtain ⟨s, hs, p, hp, rfl⟩ := (mem_sup_iff (TK_le_normalizer_QH (T := T) hKH)).1 hy
  set s' : ↥K := ⟨s, hs.2⟩ with hs'
  have hv : (α s' : Perm (Fin 5)) ∈ vbar T K α := mem_vbar.2 ⟨s', hs.1, rfl⟩
  obtain ⟨u, huT, hu⟩ := mem_vbar.1 (hk _ hv)
  have hu' : α u = α (k * s' * k⁻¹) := by
    apply Subtype.ext
    rw [hu, map_mul, map_mul, map_inv]
    rfl
  have h1 : α (u⁻¹ * (k * s' * k⁻¹)) = 1 := by rw [map_mul, map_inv, hu', inv_mul_cancel]
  have h2 : (u : G)⁻¹ * ((k : G) * s * (k : G)⁻¹) ∈ pCoreOf 2 H := (hαk _).1 h1
  have hkp : (k : G) * p * (k : G)⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH k.2)) p).mp hp
  have e : (k : G) * (s * p) * (k : G)⁻¹ =
      (u : G) * ((u : G)⁻¹ * ((k : G) * s * (k : G)⁻¹)) * ((k : G) * p * (k : G)⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨huT, u.2⟩)
    (Subgroup.mem_sup_right h2)) (Subgroup.mem_sup_right hkp)

end Gam

end A6L19

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem card_vbar {H K : Subgroup G} (hH : H ∈ S.Hz) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) : Nat.card (A6L19.vbar T K α) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Dα : Subgroup (alternatingGroup (Fin 5)) := ((T ⊓ K).subgroupOf K).map α with hDα
  have hV : A6L19.vbar T K α = Dα.map (alternatingGroup (Fin 5)).subtype := by
    rw [A6L19.vbar, hDα, Subgroup.map_map]
  have hc : Nat.card (A6L19.vbar T K α) = Nat.card Dα := by
    rw [hV, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [hc]
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTs hKH hKn.isSubnormal
  have hodd : ¬ 2 ∣ Dα.index := fun h => hTK.2.2 (h.trans (Subgroup.index_map_dvd _ hαs))
  have hcard : Nat.card Dα * Dα.index = 60 := by
    rw [Subgroup.card_mul_index, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hcop : Nat.Coprime (2 ^ 2) Dα.index :=
    Nat.Coprime.pow_left 2
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)))
  have h4 : 2 ^ 2 ∣ Nat.card Dα := hcop.dvd_of_dvd_mul_right (by rw [hcard]; norm_num)
  have hD2 : IsPGroup 2 Dα := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨s, (Subgroup.mem_subgroupOf.mp hs).1⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hsk : s ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hsk, map_one]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hD2
  have hdvd60 : Nat.card Dα ∣ 60 := Dvd.intro _ hcard
  rw [hn] at h4 hdvd60 ⊢
  have hn2 : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h4
  have hn2' : n ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have h3 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 hlt).trans hdvd60
    norm_num at h3
  rw [le_antisymm hn2' hn2]
  norm_num

theorem exists_kl_vbar {H K : Subgroup G} (hH : H ∈ S.Hz) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) :
    ∃ a b : Perm (Fin 5), A6L19.IsKl a b ∧ ∀ x, x ∈ A6L19.vbar T K α ↔ x ∈ A6L19.kl a b := by
  refine A6L19.exists_kl (S.card_vbar hH hKH hHK hαs) ?_ ?_
  · intro x hx
    obtain ⟨s, hsT, rfl⟩ := A6L19.mem_vbar.1 hx
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨s, hsT⟩
    have hsk : s ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    refine A6L19.pow_eight_of_pow (k := k) ?_
    rw [← Subgroup.coe_pow, ← map_pow, hsk, map_one, Subgroup.coe_one]
  · intro x hx
    obtain ⟨s, -, rfl⟩ := A6L19.mem_vbar.1 hx
    exact Perm.mem_alternatingGroup.mp (α s).2

theorem sign_gam_L1 {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (l : ↥H)
    (hl : (l : G) ∈ S.L1) :
    Perm.sign (A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk l) = 1 :=
  A6L19.sign_of_mem_oTwoRes (X := L ⊓ Subgroup.normalizer (fsuV1 T V : Set G))
    (le_sup_left.trans hH.1.1) _ hl

theorem pCoreOf_L1_le_R1 : pCoreOf 2 S.L1 ≤ pCoreOf 2 (S.L1 ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 S.L1).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 S.L1)
      (S.T_le_normalizer_L1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)))
    (pCoreOf_isPGroup 2 S.L1)

theorem R1_le_T : pCoreOf 2 (S.L1 ⊔ T) ≤ T :=
  pCoreOf_le_of_sylow S.h13.sylow le_sup_right

theorem O2L1_le_T : pCoreOf 2 S.L1 ≤ T :=
  S.pCoreOf_L1_le_R1.trans S.R1_le_T

theorem gam_O2L1_mem_vbar {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {a b : Perm (Fin 5)} (hkl : A6L19.IsKl a b)
    (hV : ∀ x, x ∈ A6L19.vbar T K α ↔ x ∈ A6L19.kl a b) (o : ↥H)
    (ho : (o : G) ∈ pCoreOf 2 S.L1) :
    A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk o ∈ A6L19.vbar T K α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoT : (o : G) ∈ T := S.O2L1_le_T ho
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨o, ho⟩
  have hok : o ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h8 : A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk o ^ 8 = 1 :=
    A6L19.pow_eight_of_pow (k := k) (by rw [← map_pow, hok, map_one])
  have ha : a ∈ A6L19.vbar T K α := (hV a).2 (by simp [A6L19.kl])
  have hb : b ∈ A6L19.vbar T K α := (hV b).2 (by simp [A6L19.kl])
  have hnorm : A6L19.NormKl a b (A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk o) :=
    ⟨(hV _).1 (A6L19.gam_T_conj_vbar hHK hαs hαk o hoT ha),
      (hV _).1 (A6L19.gam_T_conj_vbar hHK hαs hαk o hoT hb)⟩
  have hs := S.sign_gam_L1 hH hHK hαs hαk o (pCoreOf_le 2 S.L1 ho)
  exact (hV _).2 (A6L19.two_mem_check a b hkl _ h8 hnorm hs)

theorem T_le_normalizer_N0 {H K : Subgroup G} (hH : H ∈ S.Hz) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer ((T ⊓ K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  intro t ht
  have htH : t ∈ H := (le_sup_right.trans hH.1.1) ht
  refine A6L19.mem_normalizer_of_conj fun y hy => ?_
  obtain ⟨s, hs, p, hp, rfl⟩ :=
    (A6L19.mem_sup_iff (A6L19.TK_le_normalizer_QH (T := T) hKH)).1 hy
  have hts : t * s * t⁻¹ ∈ T ⊓ K :=
    ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (hHK htH) s).mp hs.2⟩
  have htp : t * p * t⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H htH) p).mp hp
  have e : t * (s * p) * t⁻¹ = (t * s * t⁻¹) * (t * p * t⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hts) (Subgroup.mem_sup_right htp)

theorem normKl_gam_c (hhat : ¬ IsHatA6 L) {H K : Subgroup G}
    (hH : H ∈ S.Hz) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {a b : Perm (Fin 5)}
    (hkl : A6L19.IsKl a b) (hV : ∀ x, x ∈ A6L19.vbar T K α ↔ x ∈ A6L19.kl a b) :
    A6L19.NormKl a b (A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk
      ⟨(S.cL1 hhat : G), (le_sup_left.trans hH.1.1) (S.cL1_mem hhat)⟩) := by
  set Γ := A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk with hΓ
  set c₀ : ↥H := ⟨(S.cL1 hhat : G), (le_sup_left.trans hH.1.1) (S.cL1_mem hhat)⟩ with hc₀
  have hc3 : (c₀ : G) * c₀ * c₀ = 1 := by rw [← pow_three']; exact S.cL1_cube hhat
  have hc3' : c₀ * c₀ * c₀ = 1 := Subtype.ext hc3
  refine A6L19.normalizes_check a b hkl (Γ c₀) ⟨?_, fun v hv => ?_⟩
  · rw [← map_mul, ← map_mul, hc3', map_one]
  · obtain ⟨s, hsT, rfl⟩ := A6L19.mem_vbar.1 ((hV v).2 hv)
    set s' : ↥H := ⟨s, hKH s.2⟩ with hs'
    have hsΓ : Γ s' = (α s : Perm (Fin 5)) :=
      A6L19.gam5_of_mem hHK (le_normalizer_pCoreOf 2 H) hαs hαk s (hKH s.2)
    have e : (α s : Perm (Fin 5)) * Γ c₀ * (α s : Perm (Fin 5))⁻¹ = Γ (s' * c₀ * s'⁻¹) := by
      rw [map_mul, map_mul, map_inv, hsΓ]
    rw [e]
    obtain ⟨y, hy⟩ : ∃ y : ↥H, y = s' * c₀ * s'⁻¹ := ⟨_, rfl⟩
    rw [← hy]
    have hyL : (y : G) ∈ S.L1 := by
      rw [hy]
      exact (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hsT) _).mp (S.cL1_mem hhat)
    rcases S.L1_decomp hhat hyL with h | h | h
    · have hw := S.gam_O2L1_mem_vbar hH hHK hαs hαk hkl hV y h
      exact List.mem_flatMap.2 ⟨Γ y, (hV _).1 hw, by simp⟩
    · obtain ⟨o, ho⟩ : ∃ o : ↥H, o = c₀ * c₀ * y := ⟨_, rfl⟩
      have hoO : (o : G) ∈ pCoreOf 2 S.L1 := by rw [ho]; exact h
      have hw := S.gam_O2L1_mem_vbar hH hHK hαs hαk hkl hV o hoO
      have e2 : c₀ * o = y := by
        rw [ho]
        calc c₀ * (c₀ * c₀ * y) = (c₀ * c₀ * c₀) * y := by group
          _ = y := by rw [hc3', one_mul]
      refine List.mem_flatMap.2 ⟨Γ o, (hV _).1 hw, ?_⟩
      rw [← e2, map_mul]
      simp
    · obtain ⟨o, ho⟩ : ∃ o : ↥H, o = c₀ * y := ⟨_, rfl⟩
      have hoO : (o : G) ∈ pCoreOf 2 S.L1 := by rw [ho]; exact h
      have hw := S.gam_O2L1_mem_vbar hH hHK hαs hαk hkl hV o hoO
      have e2 : c₀ * c₀ * o = y := by
        rw [ho]
        calc c₀ * c₀ * (c₀ * y) = (c₀ * c₀ * c₀) * y := by group
          _ = y := by rw [hc3', one_mul]
      refine List.mem_flatMap.2 ⟨Γ o, (hV _).1 hw, ?_⟩
      rw [← e2, map_mul, map_mul]
      simp

theorem N0_le_R1 (hhat : ¬ IsHatA6 L) {H K : Subgroup G}
    (hH : H ∈ S.Hz) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    T ⊓ K ⊔ pCoreOf 2 H ≤ pCoreOf 2 (S.L1 ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hkl, hV⟩ := S.exists_kl_vbar hH hKH hHK hαs
  set Γ := A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk with hΓ
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  set c₀ : ↥H := ⟨(S.cL1 hhat : G), hL1H (S.cL1_mem hhat)⟩ with hc₀
  have hσN := S.normKl_gam_c hhat hH hKH hHK hαs hαk hkl hV
  have hσA : Γ c₀ ∈ alternatingGroup (Fin 5) :=
    Perm.mem_alternatingGroup.mpr (S.sign_gam_L1 hH hHK hαs hαk c₀ (S.cL1_mem hhat))
  obtain ⟨k₀, hk₀⟩ := hαs ⟨Γ c₀, hσA⟩
  have hk₀' : Γ ⟨k₀, hKH k₀.2⟩ = Γ c₀ := by
    rw [hΓ, A6L19.gam5_of_mem, hk₀]
  have hx₀ : Γ (⟨k₀, hKH k₀.2⟩⁻¹ * c₀) = 1 := by rw [map_mul, map_inv, hk₀', inv_mul_cancel]
  have hTN := S.T_le_normalizer_N0 hH hKH hHK
  have hc₀N : (c₀ : G) ∈ Subgroup.normalizer
      ((T ⊓ K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    have h1 := A6L19.mem_normalizer_N0_of_K (T := T) hKH hαk k₀ fun v hv => by
      rw [hk₀]
      exact A6L19.conj_mem_of_normKl hV hσN hv
    have h2 := A6L19.mem_normalizer_N0_of_gam_one (T := T) hKH hHK hαs hαk _ hx₀
    have e : (c₀ : G) = k₀ * ((⟨k₀, hKH k₀.2⟩⁻¹ * c₀ : ↥H) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  have hL1N : S.L1 ≤ Subgroup.normalizer ((T ⊓ K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro l hl
    rcases S.L1_decomp hhat hl with h | h | h
    · exact hTN (S.O2L1_le_T h)
    · have e : l = (c₀ : G)⁻¹ * (c₀ : G)⁻¹ * ((c₀ : G) * c₀ * l) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀N)
        (Subgroup.inv_mem _ hc₀N)) (hTN (S.O2L1_le_T h))
    · have e : l = (c₀ : G)⁻¹ * ((c₀ : G) * l) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀N) (hTN (S.O2L1_le_T h))
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  refine le_pCoreOf_of_le_normalizer 2 ((sup_le inf_le_left hQT).trans le_sup_right)
    (sup_le hL1N hTN) (S.h13.sylow.1.to_le (sup_le inf_le_left hQT))

theorem R1_le_N0 (hhat : ¬ IsHatA6 L) {H K : Subgroup G}
    (hH : H ∈ S.Hz) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hfT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H) :
    pCoreOf 2 (S.L1 ⊔ T) ≤ T ⊓ K ⊔ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hkl, hV⟩ := S.exists_kl_vbar hH hKH hHK hαs
  set Γ := A6L19.gam5 hHK (le_normalizer_pCoreOf 2 H) hαs hαk with hΓ
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  set c₀ : ↥H := ⟨(S.cL1 hhat : G), hL1H (S.cL1_mem hhat)⟩ with hc₀
  have hc3 : (c₀ : G) * c₀ * c₀ = 1 := by rw [← pow_three']; exact S.cL1_cube hhat
  have hc3' : c₀ * c₀ * c₀ = 1 := Subtype.ext hc3
  have hc0O : (c₀ : G) ∉ pCoreOf 2 S.L1 := S.cL1_not_mem hhat
  have hc0sq : (c₀ : G) * c₀ ∉ pCoreOf 2 S.L1 := by
    intro h
    apply hc0O
    have e : (c₀ : G) = ((c₀ : G) * c₀) * ((c₀ : G) * c₀) := by
      calc (c₀ : G) = (c₀ : G) * c₀ * c₀ * c₀ := by rw [hc3, one_mul]
        _ = ((c₀ : G) * c₀) * ((c₀ : G) * c₀) := by group
    rw [e]
    exact Subgroup.mul_mem _ h h
  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl)
      (le_normalizer_pCoreOf 2 H (hL1H hl))
  have hON : S.L1 ≤ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) :=
    le_normalizer_pCoreOf 2 S.L1
  have hRc : ∀ r ∈ pCoreOf 2 (S.L1 ⊔ T), r * c₀ * r⁻¹ * (c₀ : G)⁻¹ ∈ pCoreOf 2 S.L1 := by
    intro r hr
    have hrT : r ∈ T := S.R1_le_T hr
    have h1 : r * c₀ * r⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hrT) _).mp (S.cL1_mem hhat)
    have h2 : r * c₀ * r⁻¹ * (c₀ : G)⁻¹ ∈ S.L1 :=
      S.L1.mul_mem h1 (S.L1.inv_mem (S.cL1_mem hhat))
    have hcN : (c₀ : G) ∈ Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) :=
      le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left (S.cL1_mem hhat))
    have h3 : (c₀ : G) * r⁻¹ * (c₀ : G)⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp hcN _).mp ((pCoreOf 2 _).inv_mem hr)
    have h4 : r * c₀ * r⁻¹ * (c₀ : G)⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) := by
      rw [show r * c₀ * r⁻¹ * (c₀ : G)⁻¹ = r * ((c₀ : G) * r⁻¹ * (c₀ : G)⁻¹) by group]
      exact Subgroup.mul_mem _ hr h3
    have hLR : S.L1 ⊓ pCoreOf 2 (S.L1 ⊔ T) ≤ pCoreOf 2 S.L1 :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl)
          (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl)))
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hLR ⟨h2, h4⟩
  have h2el : ∀ x : ↥H, (x : G) ∈ T → Γ x ^ 8 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨x, hx⟩
    have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact A6L19.pow_eight_of_pow (k := k) (by rw [← map_pow, hxk, map_one])
  have ha : a ∈ A6L19.vbar T K α := (hV a).2 (by simp [A6L19.kl])
  have hb : b ∈ A6L19.vbar T K α := (hV b).2 (by simp [A6L19.kl])
  have hnorm : ∀ x : ↥H, (x : G) ∈ T → A6L19.NormKl a b (Γ x) := fun x hx =>
    ⟨(hV _).1 (A6L19.gam_T_conj_vbar hHK hαs hαk x hx ha),
      (hV _).1 (A6L19.gam_T_conj_vbar hHK hαs hαk x hx hb)⟩
  obtain ⟨tn, htT, hρt⟩ := S.frame.DA_T (swap 0 1 * swap 4 5) (by decide)
    (Perm.mem_alternatingGroup.mpr (by decide))
  have hto : (c₀ : G) * ((tn : G) * c₀ * (tn : G)⁻¹) ∈ pCoreOf 2 S.L1 := by
    have hmem : (c₀ : G) * ((tn : G) * c₀ * (tn : G)⁻¹) ∈ S.L1 :=
      S.L1.mul_mem (S.cL1_mem hhat)
        ((Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 htT) _).mp (S.cL1_mem hhat))
    exact S.mem_pCoreOf_L1_of_K4 hhat (x := S.cL1 hhat * (tn * S.cL1 hhat * tn⁻¹)) hmem
      (by rw [map_mul, map_mul, map_mul, map_inv, S.cL1_rho, hρt]; decide)
  set t' : ↥H := ⟨tn, hTH htT⟩ with ht'
  intro r hr
  have hrT : r ∈ T := S.R1_le_T hr
  set r' : ↥H := ⟨r, hTH hrT⟩ with hr'
  refine A6L19.mem_N0_of_gam hKH hHK hαs hαk hfT r' hrT ?_
  have hcommΓ : Γ r' * Γ c₀ * (Γ r')⁻¹ * (Γ c₀)⁻¹ ∈ A6L19.kl a b := by
    have hw := S.gam_O2L1_mem_vbar hH hHK hαs hαk hkl hV (r' * c₀ * r'⁻¹ * c₀⁻¹) (hRc r hr)
    have e : Γ r' * Γ c₀ * (Γ r')⁻¹ * (Γ c₀)⁻¹ = Γ (r' * c₀ * r'⁻¹ * c₀⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact (hV _).1 hw
  by_cases hσ1 : Γ c₀ = 1
  ·
    rw [hV]
    by_contra hr'n
    have hc0K : ∀ k ∈ K, (c₀ : G) * k * (c₀ : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (A6L19.gam5_eq_one_iff hHK _ hαs hαk c₀).1 hσ1
    have hA : ∀ x : ↥H, (x : G) ∈ T → Γ x ∈ A6L19.kl a b →
        (x : G) * c₀ * (x : G)⁻¹ * (c₀ : G)⁻¹ ∈ pCoreOf 2 H := by
      intro x hxT hx
      obtain ⟨s, hs, p, hp, hsp⟩ := (A6L19.mem_sup_iff (A6L19.TK_le_normalizer_QH hKH)).1
        (A6L19.mem_N0_of_gam hKH hHK hαs hαk hfT x hxT ((hV _).2 hx))
      have hsH : s ∈ H := hKH hs.2
      have hq1 : p * ((c₀ : G) * p⁻¹ * (c₀ : G)⁻¹) ∈ pCoreOf 2 H :=
        Subgroup.mul_mem _ hp ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H c₀.2)
          _).mp ((pCoreOf 2 H).inv_mem hp))
      have hq2 : (c₀ : G) * s⁻¹ * (c₀ : G)⁻¹ * s⁻¹⁻¹ ∈ pCoreOf 2 H := hc0K _ (K.inv_mem hs.2)
      have e : (x : G) * c₀ * (x : G)⁻¹ * (c₀ : G)⁻¹ = s * ((p * ((c₀ : G) * p⁻¹ *
          (c₀ : G)⁻¹)) * ((c₀ : G) * s⁻¹ * (c₀ : G)⁻¹ * s⁻¹⁻¹)) * s⁻¹ := by
        rw [← hsp]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hsH) _).mp
        (Subgroup.mul_mem _ hq1 hq2)
    have hB : Γ t' ∉ A6L19.kl a b := by
      intro ht
      have h1 := hA t' htT ht
      have h2 : (tn : G) * c₀ * (tn : G)⁻¹ * (c₀ : G)⁻¹ ∈ S.L1 :=
        S.L1.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 htT) _).mp
          (S.cL1_mem hhat)) (S.L1.inv_mem (S.cL1_mem hhat))
      have hu := hL1Q ⟨h2, h1⟩
      apply hc0sq
      have e : (c₀ : G) * c₀ = ((c₀ : G) * ((tn : G) * c₀ * (tn : G)⁻¹ * (c₀ : G)⁻¹)⁻¹ *
          (c₀ : G)⁻¹) * ((c₀ : G) * ((tn : G) * c₀ * (tn : G)⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hON (S.cL1_mem hhat)) _).mp
        ((pCoreOf 2 _).inv_mem hu)) hto
    have hsr : Perm.sign (Γ r') ≠ 1 := fun h =>
      hr'n (A6L19.two_mem_check a b hkl _ (h2el r' hrT) (hnorm r' hrT) h)
    have hst : Perm.sign (Γ t') ≠ 1 := fun h =>
      hB (A6L19.two_mem_check a b hkl _ (h2el t' htT) (hnorm t' htT) h)
    have hsr' : Perm.sign (Γ r') = -1 := (Int.units_eq_one_or _).resolve_left hsr
    have hst' : Perm.sign (Γ t') = -1 := (Int.units_eq_one_or _).resolve_left hst
    have hxT : ((t'⁻¹ * r' : ↥H) : G) ∈ T := T.mul_mem (T.inv_mem htT) hrT
    have hx : Γ (t'⁻¹ * r') ∈ A6L19.kl a b := by
      refine A6L19.two_mem_check a b hkl _ (h2el _ hxT) (hnorm _ hxT) ?_
      rw [map_mul, map_inv, map_mul, map_inv, hsr', hst']
      decide
    have hq := hA (t'⁻¹ * r') hxT hx
    have hq' : (r * c₀ * r⁻¹) * ((tn : G) * c₀ * (tn : G)⁻¹)⁻¹ ∈ pCoreOf 2 H := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H t'.2) _).mp hq
      have e : (t' : G) * (((t'⁻¹ * r' : ↥H) : G) * c₀ * ((t'⁻¹ * r' : ↥H) : G)⁻¹ *
          (c₀ : G)⁻¹) * (t' : G)⁻¹ = (r * c₀ * r⁻¹) * ((tn : G) * c₀ * (tn : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht', hr']
        group
      rw [← e]
      exact h1
    have hq'L : (r * c₀ * r⁻¹) * ((tn : G) * c₀ * (tn : G)⁻¹)⁻¹ ∈ S.L1 :=
      S.L1.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hrT) _).mp
        (S.cL1_mem hhat)) (S.L1.inv_mem ((Subgroup.mem_normalizer_iff.mp
          (S.T_le_normalizer_L1 htT) _).mp (S.cL1_mem hhat)))
    have hq'O := hL1Q ⟨hq'L, hq'⟩
    apply hc0sq
    have e : (c₀ : G) * c₀ = ((c₀ : G) * ((c₀ : G) * ((tn : G) * c₀ * (tn : G)⁻¹)) *
        (c₀ : G)⁻¹) * (r * c₀ * r⁻¹ * (c₀ : G)⁻¹)⁻¹ *
        ((r * c₀ * r⁻¹) * ((tn : G) * c₀ * (tn : G)⁻¹)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      ((Subgroup.mem_normalizer_iff.mp (hON (S.cL1_mem hhat)) _).mp hto)
      ((pCoreOf 2 _).inv_mem (hRc r hr))) hq'O
  ·
    have hσ3 : Γ c₀ * Γ c₀ * Γ c₀ = 1 := by rw [← map_mul, ← map_mul, hc3', map_one]
    have hσN := S.normKl_gam_c hhat hH hKH hHK hαs hαk hkl hV
    exact (hV _).2 (A6L19.centralizes_check a b hkl (Γ c₀) ⟨hσ3, hσ1, hσN⟩ (Γ r')
      ⟨h2el r' hrT, hnorm r' hrT, hcommΓ⟩)

theorem pCoreOf_L1T_eq (hhat : ¬ IsHatA6 L) {H K : Subgroup G}
    (hH : H ∈ S.Hz) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hfT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H) :
    pCoreOf 2 (S.L1 ⊔ T) = T ⊓ K ⊔ pCoreOf 2 H :=
  le_antisymm (S.R1_le_N0 hhat hH hKH hHK hαs hαk hfT) (S.N0_le_R1 hhat hH hKH hHK hαs hαk)

theorem exists_d_normalizer_R1 (hhat : ¬ IsHatA6 L)
    {H K : Subgroup G} (hH : H ∈ S.Hz) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hfT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H) :
    ∃ d ∈ K, d ^ 3 = 1 ∧ d ∉ pCoreOf 2 H ∧
      d ∈ Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hkl, hV⟩ := S.exists_kl_vbar hH hKH hHK hαs
  obtain ⟨σ, hσ3, hσ1, hσN⟩ := A6L19.exists_normalizing_check a b hkl
  have hσ3' : σ ^ 3 = 1 := by rw [pow_three']; exact hσ3
  have hσA : σ ∈ alternatingGroup (Fin 5) :=
    Perm.mem_alternatingGroup.mpr (A6L19.sign_eq_one_of_pow_odd (by decide) hσ3')
  obtain ⟨d₀, hd₀⟩ := hαs ⟨σ, hσA⟩
  have hs3 : (⟨σ, hσA⟩ : alternatingGroup (Fin 5)) ^ 3 = 1 := Subtype.ext (by simpa using hσ3')
  have h3P : ((d₀ ^ 3 : ↥K) : G) ∈ pCoreOf 2 H := (hαk _).1 (by rw [map_pow, hd₀, hs3])
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, h3P⟩
  have hk' : ((d₀ : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨((d₀ ^ 4 ^ k : ↥K) : G), (d₀ ^ 4 ^ k).2, ?_, ?_, ?_⟩
  · have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]
  · intro hP
    apply hσ1
    have h1 := (hαk _).2 hP
    rw [map_pow, hd₀, A6L19.pow_four_pow_eq hs3] at h1
    exact congrArg Subtype.val h1
  · rw [S.pCoreOf_L1T_eq hhat hH hKH hHK hαs hαk hfT]
    refine A6L19.mem_normalizer_N0_of_K hKH hαk (d₀ ^ 4 ^ k) fun v hv => ?_
    rw [map_pow, hd₀, A6L19.pow_four_pow_eq hs3]
    exact A6L19.conj_mem_of_normKl hV hσN hv

theorem pCoreOf_L1_le_KP {H K : Subgroup G} (hH : H ∈ S.Hz) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {α : ↥K →* alternatingGroup (Fin 5)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hfT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H) :
    pCoreOf 2 S.L1 ≤ K ⊔ pCoreOf 2 H := by
  obtain ⟨a, b, hkl, hV⟩ := S.exists_kl_vbar hH hKH hHK hαs
  intro o ho
  have hoT := S.O2L1_le_T ho
  have hoH : o ∈ H := (le_sup_right.trans hH.1.1) hoT
  have h := A6L19.mem_N0_of_gam hKH hHK hαs hαk hfT ⟨o, hoH⟩ hoT
    (S.gam_O2L1_mem_vbar hH hHK hαs hαk hkl hV ⟨o, hoH⟩ ho)
  exact (sup_le_sup_right (inf_le_right : T ⊓ K ≤ K) (pCoreOf 2 H)) h

end Setting4

end CFSG.Quasithin.H13.A6
