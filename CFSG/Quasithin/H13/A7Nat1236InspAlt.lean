module

public import CFSG.Quasithin.H13.A7Nat1236InspBase
public import CFSG.Quasithin.Background.C2Blocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin
open scoped Nat

theorem card_centralizer_swap {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) = (n - 2)! * 2 := by
  rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.isSwap_iff_cycleType.1 hσ]
  simp

theorem card_le_of_commute_swap {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap)
    {Y : Subgroup (alternatingGroup (Fin n))} (hY : ∀ y ∈ Y, (y : Perm (Fin n)) * σ = σ * y) :
    Nat.card Y ≤ (n - 2)! * 2 := by
  rw [← card_centralizer_swap hσ,
    ← Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective]
  apply Subgroup.card_le_of_le
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact hY y hy

theorem false_of_alt_eight {Y S₀ : Subgroup (alternatingGroup (Fin 8))}
    (hS₀ : QuasithinUnique.IsSylowTwoOf S₀ ⊤)
    (hS₀Y : S₀ ≤ normalizer (Y : Set (alternatingGroup (Fin 8)))) (h360 : 360 ∣ Nat.card Y)
    (hY : Nat.card Y ≤ 1440) : False := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  set N := normalizer (Y : Set (alternatingGroup (Fin 8))) with hNdef
  have hYN : Y ≤ N := le_normalizer
  have h1 : N.index * Nat.card N = 20160 := by rw [mul_comm, Subgroup.card_mul_index, hcard]
  have h2 : ¬ 2 ∣ N.index := by
    intro h
    apply hS₀.2.2
    show 2 ∣ S₀.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.trans (Subgroup.index_dvd_of_le hS₀Y)
  have h45 : 45 ∣ Nat.card N := (dvd_trans (by norm_num) h360).trans (Subgroup.card_dvd_of_le hYN)
  have h3 : N.index * 45 ∣ 448 * 45 := by
    rw [show 448 * 45 = 20160 by norm_num, ← h1]
    exact mul_dvd_mul_left _ h45
  have h4 : N.index ∣ 2 ^ 6 * 7 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
  have h5 : Nat.Coprime N.index (2 ^ 6) :=
    Nat.Coprime.pow_right 6 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
  have h6 : N.index ∣ 7 := h5.dvd_of_dvd_mul_left h4
  have hNtop : N = ⊤ := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h6 with h | h
    · exact Subgroup.index_eq_one.1 h
    · exfalso
      have h8 := Subgroup.index_normalCore_dvd_factorial_index N
      rw [h] at h8
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N.normalCore with h9 | h9
      · rw [h9, Subgroup.index_bot, hcard] at h8
        norm_num [Nat.factorial] at h8
      · have h10 : N = ⊤ := eq_top_iff.2 (h9 ▸ Subgroup.normalCore_le N)
        rw [h10, Subgroup.index_top] at h
        norm_num at h
  have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.1 hNtop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
  · rw [h, Subgroup.card_bot] at h360
    norm_num at h360
  · rw [h, Subgroup.card_top, hcard] at hY
    norm_num at hY

variable {G : Type} [Group G] [Finite G]

theorem false_of_case_b {K R V M X T : Subgroup G} (hRK : R ≤ normalizer (K : Set G))
    (hC : (K ⊔ R) ⊓ centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hKRV : K ⊔ R ≤ normalizer (V : Set G)) (hX : X ≤ K ⊓ M) (hTX : T ≤ normalizer (X : Set G))
    (hTK : QuasithinUnique.IsSylowTwoOf (T ⊓ K) K) {θ : ↥X →* alternatingGroup (Fin 6)}
    (hθ : Function.Surjective θ) (hθO : ∀ x : ↥X, x ∈ CFSG.pCore 2 ↥X → θ x = 1) {n : ℕ}
    {α : ↥K →* alternatingGroup (Fin n)} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hα : IsAltBlockTypeWith K n α) {t : G} (htR : t ∈ R) (htV : t ∈ normalizer (V : Set G))
    {σ : Perm (Fin n)} (hσ : σ.IsSwap)
    (hσα : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ K) V = autOn K V ⊓ centralizer (autOn R V : Set (MulAut ↥V))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hαs, hαk, -⟩ := hα
  have hXK : X ≤ K := hX.trans inf_le_left
  have hXM : X ≤ M := hX.trans inf_le_right
  have hKV : K ≤ normalizer (V : Set G) := le_sup_left.trans hKRV
  set P := pCoreOf 2 (K ⊔ R) with hPdef
  have hKRN : K ⊔ R ≤ normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hcen : ∀ k : ↥K, (k : G) ∈ centralizer (V : Set G) → α k = 1 := by
    intro k hkV
    have hk : (k : G) ∈ P ⊔ oTwoZIn K := hC ⟨(le_sup_left : K ≤ K ⊔ R) k.2, hkV⟩
    have hZP : oTwoZIn K ≤ normalizer (P : Set G) := fun z hz =>
      hKRN ((le_sup_left : K ≤ K ⊔ R) (oTwoZIn_le_self K hz))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left P (oTwoZIn K) hZP] at hk
    obtain ⟨p, hp, z, hz, hpz⟩ := hk
    have hzK : z ∈ K := oTwoZIn_le_self K hz
    have hpK : p ∈ K := by
      have hpe : p = (k : G) * z⁻¹ := by rw [← hpz]; group
      rw [hpe]
      exact K.mul_mem k.2 (K.inv_mem hzK)
    have hαz : α ⟨z, hzK⟩ = 1 := by
      have hcz : α ⟨z, hzK⟩ ∈ center (alternatingGroup (Fin n)) := by
        rw [mem_center_iff]
        intro g
        obtain ⟨k', rfl⟩ := hαs g
        have h1 := commutator_mem_pCoreOf_of_mem_oTwoZIn hz k'.2
        have h2 : (⟨z, hzK⟩ : ↥K) * k' * (⟨z, hzK⟩ : ↥K)⁻¹ * k'⁻¹ ∈ α.ker := by
          rw [hαk]
          exact mem_pCore_of_coe_mem h1
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
        calc α k' * α ⟨z, hzK⟩
            = (α ⟨z, hzK⟩ * α k' * (α ⟨z, hzK⟩)⁻¹ * (α k')⁻¹)⁻¹ * (α ⟨z, hzK⟩ * α k') := by
              group
          _ = α ⟨z, hzK⟩ * α k' := by rw [h2, inv_one, one_mul]
      rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot] at hcz
      exact hcz
    have hαp : α ⟨p, hpK⟩ = 1 := by
      have hN : ((P ⊓ K).subgroupOf K).Normal :=
        (normal_subgroupOf_iff_le_normalizer inf_le_right).2 fun y hy =>
          A4.mem_normalizer_inf (hKRN ((le_sup_left : K ≤ K ⊔ R) hy)) (le_normalizer hy)
      have h2 : IsPGroup 2 ((P ⊓ K).subgroupOf K) :=
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_left).comap_of_injective
          _ K.subtype_injective
      have hle : (P ⊓ K).subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, h2⟩
      have hmem : (⟨p, hpK⟩ : ↥K) ∈ α.ker := by
        rw [hαk]
        exact hle (show (⟨p, hpK⟩ : ↥K) ∈ (P ⊓ K).subgroupOf K from ⟨hp, hpK⟩)
      exact hmem
    have hkpz : k = ⟨p, hpK⟩ * ⟨z, hzK⟩ := Subtype.ext hpz.symm
    rw [hkpz, map_mul, hαp, hαz, one_mul]
  have htAut : conjAct V ⟨t, htV⟩ ∈ autOn R V :=
    Subgroup.mem_map_of_mem _ (show (⟨t, htV⟩ : normalizer (V : Set G)) ∈ R.subgroupOf _ from htR)
  have hcomm : ∀ x : ↥X, ((α (Subgroup.inclusion hXK x) : alternatingGroup (Fin n)) :
      Perm (Fin n)) * σ = σ * (α (Subgroup.inclusion hXK x) : Perm (Fin n)) := by
    intro x
    have hxK : (x : G) ∈ K := hXK x.2
    have hxV : (x : G) ∈ normalizer (V : Set G) := hKV hxK
    have hxA : conjAct V ⟨x, hxV⟩ ∈ autOn (M ⊓ K) V :=
      Subgroup.mem_map_of_mem _
        (show (⟨x, hxV⟩ : normalizer (V : Set G)) ∈ (M ⊓ K).subgroupOf _ from ⟨hXM x.2, hxK⟩)
    rw [hMK] at hxA
    have h1 := mem_centralizer_iff.1 hxA.2 _ htAut
    have h2 : conjAct V (⟨x, hxV⟩ * ⟨t, htV⟩ * (⟨x, hxV⟩ : normalizer (V : Set G))⁻¹ *
        (⟨t, htV⟩ : normalizer (V : Set G))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have hcV : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ centralizer (V : Set G) := A4.conjAct_eq_one_iff.1 h2
    have htx : t * (x : G)⁻¹ * t⁻¹ ∈ K := (mem_normalizer_iff.1 (hRK htR) _).1 (K.inv_mem hxK)
    have hcK : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ K := by
      have h3 := K.mul_mem hxK htx
      rwa [← mul_assoc, ← mul_assoc] at h3
    have h4 : (⟨_, hcK⟩ : ↥K) = ⟨x, hxK⟩ * ⟨t * (x : G)⁻¹ * t⁻¹, htx⟩ := by
      apply Subtype.ext
      show (x : G) * t * (x : G)⁻¹ * t⁻¹ = (x : G) * (t * (x : G)⁻¹ * t⁻¹)
      group
    have h5 := congrArg Subtype.val (hcen ⟨_, hcK⟩ hcV)
    rw [h4, map_mul, Subgroup.coe_mul, hσα _ (K.inv_mem hxK) htx] at h5
    have h6 : ((α ⟨(x : G)⁻¹, K.inv_mem hxK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((α ⟨x, hxK⟩ : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹ := by
      have h7 : (⟨(x : G)⁻¹, K.inv_mem hxK⟩ : ↥K) = (⟨x, hxK⟩ : ↥K)⁻¹ := rfl
      rw [h7, map_inv]
      rfl
    rw [h6] at h5
    have h8 : Subgroup.inclusion hXK x = ⟨x, hxK⟩ := rfl
    rw [h8]
    calc ((α ⟨x, hxK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * σ
        = ((α ⟨x, hxK⟩ : Perm (Fin n)) * (σ * (α ⟨x, hxK⟩ : Perm (Fin n))⁻¹ * σ⁻¹)) *
            (σ * (α ⟨x, hxK⟩ : Perm (Fin n))) := by group
      _ = σ * (α ⟨x, hxK⟩ : Perm (Fin n)) := by
        rw [show ((α ⟨x, hxK⟩ : Perm (Fin n)) * (σ * (α ⟨x, hxK⟩ : Perm (Fin n))⁻¹ * σ⁻¹)) = 1
          from h5, one_mul]
  set Y := (α.comp (Subgroup.inclusion hXK)).range with hYdef
  have hYc : ∀ y ∈ Y, (y : Perm (Fin n)) * σ = σ * y := by
    rintro _ ⟨x, rfl⟩
    exact hcomm x
  have hXO : pCoreOf 2 K ⊓ X ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun y hy => A4.mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hXK hy))
        (le_normalizer hy))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
  obtain ⟨fY, hfY⟩ := exists_surj_of_ker_le (α.comp (Subgroup.inclusion hXK)) hθ fun x hx => by
    have hx' : Subgroup.inclusion hXK x ∈ α.ker := hx
    rw [hαk] at hx'
    exact hθO x (mem_pCore_of_coe_mem (hXO ⟨coe_mem_pCoreOf hx', x.2⟩))
  have h360 : 360 ∣ Nat.card Y := card_alt_six_dvd hfY
  have hYle : Nat.card Y ≤ (n - 2)! * 2 := card_le_of_commute_swap hσ hYc
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  rcases Nat.lt_or_ge n 8 with hn | hn
  · have h360' : 360 ≤ Nat.card Y := Nat.le_of_dvd hYpos h360
    have hfac : ∀ m : ℕ, 5 ≤ m → m < 8 → (m - 2)! * 2 ≤ 240 := by
      intro m hm5 hm8
      interval_cases m <;> decide
    have := hfac n hn5 hn
    omega
  · obtain rfl : n = 8 := by omega
    have hS₀ := isSylowTwoOf_map_subgroupOf hTK α hαs
    have hS₀Y : ((T ⊓ K).subgroupOf K).map α ≤ normalizer (Y : Set (alternatingGroup (Fin 8))) :=
      map_le_normalizer_range hXK (inf_le_left.trans hTX) α
    exact false_of_alt_eight hS₀ hS₀Y h360 (hYle.trans (by decide))

end CFSG.Quasithin.H13.A7
