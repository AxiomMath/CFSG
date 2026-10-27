module

public import CFSG.Quasithin.Vol2.Ch3E213MOS11
public import CFSG.Quasithin.Vol2.GoldschmidtE217L2Dih
public import CFSG.Quasithin.Vol2.GoldschmidtE217Klein

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.GLS.IVK CFSG.GH74.GLS
open scoped MatrixGroups

namespace E217R3

variable {X : Type} [Group X] [Finite X]

theorem exists_central_involution {K T M : Subgroup X} (hX : E2P.ASHyp K T M)
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X)) :
    ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ ∀ m ∈ M, m * z = z * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hX.minPar.le
  have hMtop : M < ⊤ := (isMaxSubgroupIn_lt hX.minPar.maximal)
  have hP : T ⊓ K ≠ ⊥ := by
    intro hP
    have hz : E2P.zOf (T ⊓ K) = ⊥ := by
      rw [hP]
      simp [E2P.zOf]
    rw [hz] at hMK
    have hKM : K ≤ M := by
      intro k hk
      have : k ∈ K ⊓ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) :=
        ⟨hk, Subgroup.mem_centralizer_iff.2 fun h hh => by
          have : h = 1 := by simpa using hh
          rw [this]
          simp⟩
      rw [← hMK] at this
      exact this.1
    have : (⊤ : Subgroup X) ≤ M := hX.sup ▸ sup_le hKM hTM
    exact lt_irrefl _ (lt_of_lt_of_le hMtop this)
  obtain ⟨z, hzP, hz2, hzc⟩ := exists_involution_mem_center_of_normal hX.minPar.isSylow.2.1
    (inf_le_left : T ⊓ K ≤ T) (fun t ht y hy => ⟨T.mul_mem (T.mul_mem ht hy.1) (T.inv_mem ht),
      by
        have := hX.normal.conj_mem y hy.2 t
        simpa using this⟩) hP
  refine ⟨z, hzP, hz2, fun m hm => ?_⟩
  obtain ⟨k, hk, t, ht, rfl⟩ := E2P.exists_mul_of_mem_sup_of_le_normalizer'
    (fun y _ => (Subgroup.normalizer_eq_top_iff.mpr hX.normal).symm ▸ Subgroup.mem_top y)
    (show m ∈ K ⊔ T from hX.sup ▸ Subgroup.mem_top m)
  have hkM : k ∈ M := by
    have : k = (k * t) * t⁻¹ := by group
    rw [this]
    exact M.mul_mem hm (M.inv_mem (hTM ht))
  have hkC : k ∈ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X) := by
    have : k ∈ M ⊓ K := ⟨hkM, hk⟩
    rw [hMK] at this
    exact this.2
  have hzZ : z ∈ E2P.zOf (T ⊓ K) :=
    ⟨hzP, Subgroup.mem_centralizer_iff.2 fun y hy => hzc y hy.1⟩
  have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hkC z hzZ).symm
  calc k * t * z = k * (t * z) := by group
    _ = k * (z * t) := by rw [hzc t ht]
    _ = (k * z) * t := by group
    _ = (z * k) * t := by rw [hkz]
    _ = z * (k * t) := by group

theorem eq_central_involution_of_asHyp (h12 : IVK_1_2_general) (h13a : IVK_1_3a)
    (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L)))
    {K T M : Subgroup X} (hX : E2P.ASHyp K T M) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : f = 1 ∨ f = 2) (hpsl : IsPSL 2 p f ↥K)
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X))
    (hAut : 8 < E2.autCard T K) {v z : X} (hz2 : orderOf z = 2) (hzT : z ∈ T)
    (hzM : ∀ m ∈ M, m * z = z * m) (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvT : v ∈ T)
    (hvM : ∀ m ∈ M, m * v = v * m) : v = z := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hX.minPar.le
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    omega
  have hvz : v * z = z * v := (hvM z (hTM hzT)).symm
  set V1 : Subgroup X := Subgroup.closure ({v, z} : Set X) with hV1
  have hcomm : ∀ m ∈ M, ∀ x ∈ V1, m * x = x * m := fun m hm x hx =>
    commute_closure hv2 hz2' hvz (hvM m hm) (hzM m hm) x hx
  have hsq : ∀ x ∈ V1, x * x = 1 := by
    intro x hx
    rcases klein_closure hv2 hz2' hvz x hx with h | h | h | h <;> rw [h]
    · simp
    · exact hv2
    · exact hz2'
    · calc (v * z) * (v * z) = v * (z * v) * z := by group
        _ = v * (v * z) * z := by rw [← hvz]
        _ = (v * v) * (z * z) := by group
        _ = 1 := by rw [hv2, hz2', one_mul]
  have hV4 : 4 ≤ Nat.card V1 := four_le_card_closure hv2 hz2' hv1 hz1 hne
  have hVT : V1 ≤ T := (Subgroup.closure_le T).2 (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [hvT, hzT])
  have hVM1 : V1 ≤ M := hVT.trans hTM
  have hVn : T ≤ Subgroup.normalizer (V1 : Set X) :=
    (show T ≤ Subgroup.centralizer (V1 : Set X) from fun t ht =>
      Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm t (hTM ht) x hx).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMn : M ≤ Subgroup.normalizer (V1 : Set X) :=
    (show M ≤ Subgroup.centralizer (V1 : Set X) from fun m hm =>
      Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm m hm x hx).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hVp : IsPGroup 2 ↥V1 := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩
  have hVM : V1 ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM1 hMn hVp
  exact Ch3E213M.OS.false_of_asHyp h12 h13a h13b hcoat hX hp hp3 hf hpsl hMK hAut hVT hVn hsq
    hV4 hVM

theorem card_eq_seven_of_asHyp (h12 : IVK_1_2_general) (h13a : IVK_1_3a) (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L)))
    {K T M : Subgroup X} (hX : E2P.ASHyp K T M) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : f = 1 ∨ f = 2) (hp8 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7) (hpsl : IsPSL 2 p f ↥K)
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X))
    (hAut : 8 < E2.autCard T K) {v : X} (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvT : v ∈ T)
    (hvM : ∀ m ∈ M, m * v = v * m) (hodd : OddCube v) : p ^ f = 7 ∧ v ∈ K := by
  obtain ⟨z, hzK, hz2, hzM⟩ := exists_central_involution hX hMK
  have hvz := eq_central_involution_of_asHyp h12 h13a h13b hcoat hX hp hp3 hf hpsl hMK hAut hz2
    hzK.1 hzM hv2 hv1 hvT hvM
  subst hvz
  have hvK : v ∈ K := hzK.2
  refine ⟨?_, hvK⟩
  obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := hpsl
  have hf0 : f ≠ 0 := by omega
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  have hF2 : ringChar F ≠ 2 := by
    intro h2
    have : CharP F 2 := h2 ▸ ringChar.charP F
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hp2, hn⟩ := FiniteField.card F 2
    have h1 : p ^ f = 2 ^ (n : ℕ) := by rw [← hcard, Nat.card_eq_fintype_card, hn]
    have h3 : p ∣ 2 ^ (n : ℕ) := h1 ▸ dvd_pow_self p hf0
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
    omega
  have hq5 : 5 ≤ Nat.card F := by
    rw [hcard]
    exact hp5.trans (Nat.le_self_pow hf0 p)
  let θ : ↥K ≃* PSL(2, F) := e₀.trans (L2.equivPSL F)
  have hv'1 : θ ⟨v, hvK⟩ ≠ 1 := fun h => hv1 (by
    have := θ.injective (h.trans (map_one θ).symm)
    exact congrArg Subtype.val this)
  have hv'2 : θ ⟨v, hvK⟩ * θ ⟨v, hvK⟩ = 1 := by
    rw [← map_mul, show (⟨v, hvK⟩ : ↥K) * ⟨v, hvK⟩ = 1 from Subtype.ext hv2, map_one]
  have hodd' : OddCube (θ ⟨v, hvK⟩) :=
    (OddCube.of_subgroup hvK (fun g _ n hn h1 => hodd g n hn h1)).map θ
  have h57 := card_eq_five_or_seven hF2 hq5 hv'1 hv'2 hodd'
  rw [hcard] at h57
  omega

end E217R3

end CFSG.Quasithin
