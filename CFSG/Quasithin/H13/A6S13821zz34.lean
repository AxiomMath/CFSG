module

public import CFSG.Quasithin.H13.A6S13821zo
public import CFSG.Quasithin.H13.A6S13821zh
public import CFSG.Quasithin.H13.L32AC44g
public import CFSG.Quasithin.H13.A6S13821za

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open Equiv

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_natural_sl34_13820b
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h1337 : Stmt13_3_7) {H K : Subgroup G} {n : ℕ}
    (hC : S.Ctx13820 H K n) (hb : S.Case13820bHyp H K) (hL1K : S.L1 ≤ K)
    (hF : HypF918 T V L (fsuV1 T V) S.V3 H K) {I : Subgroup G} (hIU : I ≤ conjClosure S.V3 H)
    (hkerK : ∀ k ∈ K, (∀ u ∈ conjClosure I H, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      k ∈ pCoreOf 2 H) :
    haveI := factElem hF hIU
    BinaryNaturalSL (autIH (fsuV1 T V) I H K) ⊤ ⊥ 3 2 → False := by
  classical
  have hFe := factElem hF hIU
  intro hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hH, hK, hKn, hHK, hn, hLie⟩ := hC
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  obtain ⟨e₀⟩ := S.kst_equiv hS hH hK
  have hLieQ : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n := lieF2n_congr e₀.symm hLie
  have hV₁ := hF.H_le_normalizer_V₁
  have hIH := le_normalizer_conjClosure I H
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  set ψ := actH hV₁ hIH with hψ
  set Lk := autIH (fsuV1 T V) I H K with hLk
  have hψK : Lk = (K.subgroupOf H).map ψ := autIH_eq_map hF hKH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  set U : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure I H))) :=
    ((T ⊓ K).subgroupOf H).map ψ with hU
  have hTK := S.isSylowTwoOf_TK hH hKH hKn
  have hψU : ∀ y : ↥H, (y : G) ∈ T ⊓ K → ψ y ∈ U := fun y hy =>
    ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hψL : ∀ y : ↥H, (y : G) ∈ K → ψ y ∈ Lk := fun y hy => by
    rw [hψK]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hmemU : ∀ k : ↥H, (k : G) ∈ K → ψ k ∈ U → (k : G) ∈ T := by
    rintro k hk ⟨u, hu, hψu⟩
    have hu' : (u : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hu
    have h1 : ψ (u⁻¹ * k) = 1 := by rw [map_mul, map_inv, hψu, inv_mul_cancel]
    have h2 := hkerK _ (K.mul_mem (K.inv_mem hu'.2) hk)
      ((A6Tv.actH_eq_one_iff hV₁ hIHN hIH (u⁻¹ * k)).mp h1)
    have e : (k : G) = u * ((u⁻¹ * k : ↥H) : G) := by simp
    rw [e]
    exact T.mul_mem hu'.1 (hQT h2)
  have hUL : U ≤ Lk := by
    rintro _ ⟨y, hy, rfl⟩
    exact hψL y (Subgroup.mem_subgroupOf.mp hy).2
  have hUsyl : IsSylowTwoOf U Lk := by
    refine ⟨hUL, ?_, ?_⟩
    · have h1 : IsPGroup 2 ↥((T ⊓ K).subgroupOf H) :=
        hTK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hKH)).symm
      exact h1.map ψ
    · intro h2
      apply hTK.2.2
      let σ : ↥K →* ↥Lk :=
        { toFun := fun k => ⟨ψ (Subgroup.inclusion hKH k), hψL _ k.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp) }
      have hσs : Function.Surjective σ := by
        rintro ⟨_, hy⟩
        rw [hψK] at hy
        obtain ⟨y, hy', rfl⟩ := hy
        exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy'⟩, rfl⟩
      have hmap : ((T ⊓ K).subgroupOf K).map σ = U.subgroupOf Lk := by
        ext y
        rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact hψU _ (Subgroup.mem_subgroupOf.mp hk)
        · rintro ⟨w, hw, hwy⟩
          have hwK : (w : G) ∈ K := (Subgroup.mem_subgroupOf.mp hw).2
          refine ⟨⟨w, hwK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hw), ?_⟩
          exact Subtype.ext hwy
      have h3 := Subgroup.index_map_dvd ((T ⊓ K).subgroupOf K) hσs
      rw [hmap] at h3
      exact h2.trans h3
  have hconjU : ∀ k : ↥H, (k : G) ∈ K → ψ k ∈ Subgroup.normalizer (U : Set (MulAut _)) →
      (k : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro k hk hkN
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hyH : y ∈ H := hKH hy.2
    have h1 : ψ (k * ⟨y, hyH⟩ * k⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hkN _).mp (hψU ⟨y, hyH⟩ hy)
    have hK' : (k : G) * y * (k : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hy.2) (K.inv_mem hk)
    exact ⟨hmemU _ hK' h1, hK'⟩
  have hNU : ∀ x : G, ∀ hxH : x ∈ H, x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
      ψ ⟨x, hxH⟩ ∈ Subgroup.normalizer (U : Set (MulAut _)) := by
    intro x hxH hxN
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨x, hxH⟩ * y * (⟨x, hxH⟩ : ↥H)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by
        rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.mem_subgroupOf.mp hy)
    · intro hu
      obtain ⟨y, hy, hyu⟩ := hu
      refine ⟨(⟨x, hxH⟩ : ↥H)⁻¹ * y * ⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp
          (Subgroup.mem_subgroupOf.mp hy)
        simpa using h1
      · rw [map_mul, map_mul, map_inv, hyu]
        group
  have hNT : ∀ x ∈ S.L1 ⊔ T, ∀ hxH : x ∈ H, ψ ⟨x, hxH⟩ ∈
      Subgroup.normalizer (U : Set (MulAut _)) := fun x hx hxH =>
    hNU x hxH (S.L1T_le_normalizer_TK h1334 hS hH hKH hKn hn hLieQ hx)
  by_cases hhat : IsHatA6 L
  ·
    obtain ⟨-, t, ⟨htT, htL⟩, htX, -⟩ := hb
    have htH : t ∈ H := hTH htT
    set g := ψ ⟨t, htH⟩ with hg
    have hgQ : ∀ x ∈ Lk, g * x * g⁻¹ ∈ Lk := by
      intro x hx
      rw [hψK] at hx ⊢
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨⟨t, htH⟩ * k * (⟨t, htH⟩ : ↥H)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by
        rw [hg, map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKn htH) _).mp (Subgroup.mem_subgroupOf.mp hk)
    have hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu =>
      (Subgroup.mem_normalizer_iff.mp (hNT t (Subgroup.mem_sup_right htT) htH) u).mp hu
    have hsemi := A6Semi.semi_of_binaryNaturalSL hnat hUsyl hgQ hgU (fun v _ => trivial)
      (fun z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one])
    have hsq : ∀ x : G, x ∈ S.L1 → ∀ hxH : x ∈ H,
        g * ψ ⟨x, hxH⟩ * g⁻¹ * (ψ ⟨x, hxH⟩)⁻¹ ∈ U → g * ψ ⟨x, hxH⟩ * g⁻¹ * ψ ⟨x, hxH⟩ ∈ U →
        ∃ a : ℕ, x ^ 2 ^ (a + 1) = 1 := by
      intro x hxL1 hxH h1 h2
      have hxK : x ∈ K := hL1K hxL1
      have h3 : ψ (⟨x, hxH⟩ ^ 2) ∈ U := by
        have e : ψ (⟨x, hxH⟩ ^ 2) = (g * ψ ⟨x, hxH⟩ * g⁻¹ * (ψ ⟨x, hxH⟩)⁻¹)⁻¹ *
            (g * ψ ⟨x, hxH⟩ * g⁻¹ * ψ ⟨x, hxH⟩) := by
          rw [map_pow, sq]
          group
        rw [e]
        exact U.mul_mem (U.inv_mem h1) h2
      have h4 := hmemU _ (by simpa using K.pow_mem hxK 2) h3
      obtain ⟨a, ha⟩ := S.h13.sylow.1 ⟨_, h4⟩
      refine ⟨a, ?_⟩
      have ha' : ((x ^ 2 : G)) ^ 2 ^ a = 1 := by
        simpa using congrArg Subtype.val ha
      rw [pow_succ', pow_mul, ha']
    rcases hsemi with hcen | hinv
    ·
      have P := S.plusData_X13820
      have hτ : (swap (0 : Fin 6) 1 * swap 1 2) ∈ S14.C3 := by decide
      obtain ⟨x, hxX, hρx⟩ := P.three _ hτ
      have hxL1 : (x : G) ∈ S.L1 := P.le_L1 hxX
      have hxH : (x : G) ∈ H := (le_sup_left.trans hH.1.1) hxL1
      have h1 := hcen (ψ ⟨x, hxH⟩) ⟨hψL _ (hL1K hxL1), hNT _ (Subgroup.mem_sup_left hxL1) hxH⟩
      have hO2X : pCoreOf 2 S.X13820 ≤ T ⊓ K := by
        refine le_inf ?_ ((pCoreOf_le 2 _).trans (P.le_L1.trans hL1K))
        refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 S.X13820).trans le_sup_left)
          (sup_le (le_normalizer_pCoreOf 2 S.X13820)
            (P.T_le.trans (normalizer_le_normalizer_pCoreOf 2 S.X13820)))
          (pCoreOf_isPGroup 2 S.X13820)).trans ?_
        exact pCoreOf_le_of_sylow S.h13.sylow le_sup_right
      have h2 : g * ψ ⟨x, hxH⟩ * g⁻¹ * ψ ⟨x, hxH⟩ ∈ U := by
        have h3 := hO2X (htX _ hxX)
        have h4 := hψU ⟨t * x * t⁻¹ * x, H.mul_mem (H.mul_mem (H.mul_mem htH hxH)
          (H.inv_mem htH)) hxH⟩ h3
        rwa [show (⟨t * x * t⁻¹ * x, _⟩ : ↥H) =
          ⟨t, htH⟩ * ⟨x, hxH⟩ * (⟨t, htH⟩ : ↥H)⁻¹ * ⟨x, hxH⟩ from rfl, map_mul, map_mul,
          map_mul, map_inv] at h4
      obtain ⟨a, ha⟩ := hsq x hxL1 hxH h1 h2
      have hρ1 : S.frame.ρ x ^ 2 ^ (a + 1) = 1 := by
        rw [← map_pow]
        have : x ^ 2 ^ (a + 1) = 1 := Subtype.ext (by simpa using ha)
        rw [this, map_one]
      rw [hρx] at hρ1
      have hτ3 := (S14.c3_facts _ hτ).2.2.2
      have hτ1 : orderOf (swap (0 : Fin 6) 1 * swap 1 2) ∣ Nat.gcd (2 ^ (a + 1)) 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hρ1) (orderOf_dvd_of_pow_eq_one hτ3)
      have hg1 : Nat.gcd (2 ^ (a + 1)) 3 = 1 :=
        Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)
      rw [hg1, Nat.dvd_one, orderOf_eq_one_iff] at hτ1
      exact absurd hτ1 (by decide)
    ·
      obtain ⟨c, hc, hc3, hcO, -⟩ := l0_decomp hhat
      have hcL1 : c ∈ S.L1 := S.l0_le_L1 hc
      have hcK : c ∈ K := hL1K hcL1
      have hcH : c ∈ H := (le_sup_left.trans hH.1.1) hcL1
      have h1 := hinv (ψ ⟨c, hcH⟩) ⟨hψL _ hcK, hNT _ (Subgroup.mem_sup_left hcL1) hcH⟩
      have hO2L : pCoreOf 2 L ≤ T := by
        refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
          (sup_le (le_normalizer_pCoreOf 2 L)
            (S.T_le_NL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
          (pCoreOf_isPGroup 2 L)).trans ?_
        exact pCoreOf_le_of_sylow S.h13.sylow le_sup_right
      have h2 : g * ψ ⟨c, hcH⟩ * g⁻¹ * (ψ ⟨c, hcH⟩)⁻¹ ∈ U := by
        have h3 : c * t * c⁻¹ * t⁻¹ ∈ pCoreOf 2 L := (mem_o2Z_iff.1 (oTwoRes_le _ hc)).2 t htL
        have h4 : t * c * t⁻¹ * c⁻¹ ∈ T ⊓ K := by
          refine ⟨?_, ?_⟩
          · have := T.inv_mem (hO2L h3)
            rwa [show (c * t * c⁻¹ * t⁻¹)⁻¹ = t * c * t⁻¹ * c⁻¹ by group] at this
          · exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn htH) c).mp hcK)
              (K.inv_mem hcK)
        have h5 := hψU ⟨t * c * t⁻¹ * c⁻¹, H.mul_mem (H.mul_mem (H.mul_mem htH hcH)
          (H.inv_mem htH)) (H.inv_mem hcH)⟩ h4
        rwa [show (⟨t * c * t⁻¹ * c⁻¹, _⟩ : ↥H) =
          ⟨t, htH⟩ * ⟨c, hcH⟩ * (⟨t, htH⟩ : ↥H)⁻¹ * (⟨c, hcH⟩ : ↥H)⁻¹ from rfl, map_mul,
          map_mul, map_mul, map_inv, map_inv] at h5
      obtain ⟨a, ha⟩ := hsq c hcL1 hcH h2 h1
      apply hcO
      have hc1 : orderOf c ∣ Nat.gcd (2 ^ (a + 1)) 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hc3)
      have hg1 : Nat.gcd (2 ^ (a + 1)) 3 = 1 :=
        Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)
      rw [hg1, Nat.dvd_one, orderOf_eq_one_iff] at hc1
      rw [hc1]
      exact Subgroup.one_mem _
  ·
    have h9 := L32A.C.relIndex_normalizer_eq_nine hnat hUsyl
    have h9' : 9 ∣ Nat.card ↥(Lk ⊓ Subgroup.normalizer (U : Set (MulAut _))) := by
      rw [← h9]
      exact Subgroup.relIndex_dvd_card _ _
    set B := K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) with hB
    have hBH : B ≤ H := inf_le_left.trans hKH
    let β : ↥B →* ↥(Lk ⊓ Subgroup.normalizer (U : Set (MulAut _))) :=
      (ψ.comp (Subgroup.inclusion hBH)).codRestrict _ fun b =>
        ⟨hψL _ b.2.1, hNU b (hBH b.2) b.2.2⟩
    have hβs : Function.Surjective β := by
      rintro ⟨y, hyL, hyN⟩
      have hyL' := hyL
      rw [hψK] at hyL'
      obtain ⟨k, hk, rfl⟩ := hyL'
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      exact ⟨⟨k, hkK, hconjU k hkK hyN⟩, rfl⟩
    have h9B : 9 ∣ Nat.card ↥B := h9'.trans (Subgroup.card_dvd_of_surjective hβs)
    have hBM := S.borel_le_M h13 h1334 hS hH hKH hKn hn hLieQ
    have hBV : B ≤ Subgroup.normalizer (V : Set G) := fun b hb =>
      S.inf_M_le_NV h1334 hH ⟨hBH hb, hBM hb⟩
    exact S.not_nine_dvd_card h1337 hhat hH hBH hBV h9B

end Setting4

end CFSG.Quasithin.H13.A6
