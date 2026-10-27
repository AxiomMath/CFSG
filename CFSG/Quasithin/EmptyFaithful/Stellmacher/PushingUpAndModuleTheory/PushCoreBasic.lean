module

public import CFSG.Quasithin.Background.A4Bridge

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem mem_sup_of_le_normalizer {N K : Subgroup G} (hK : K ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ K) : ∃ n ∈ N, ∃ k ∈ K, x = n * k := by
  have hconj : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := fun k hk n hn =>
    (Subgroup.mem_normalizer_iff.mp (hK hk) n).mp hn
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, by simp⟩
    · exact ⟨1, N.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, N.one_mem, 1, K.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    obtain ⟨n', hn', k', hk', rfl⟩ := hy
    refine ⟨n * (k * n' * k⁻¹), N.mul_mem hn (hconj k hk n' hn'), k * k', K.mul_mem hk hk', ?_⟩
    group
  | inv x _ hx =>
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    refine ⟨k⁻¹ * n⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, by group⟩
    have := hconj k⁻¹ (K.inv_mem hk) n⁻¹ (N.inv_mem hn)
    simpa using this

theorem card_sup_mul_card_inf_of_normal (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem relIndex_sup_eq_relIndex_inf [Finite G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    B.relIndex (A ⊔ B) = (A ⊓ B).relIndex A := by
  have h := card_sup_mul_card_inf_of_le_normalizer hB
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := A)
  rw [inf_of_le_left (le_sup_right : B ≤ A ⊔ B)] at h1
  rw [inf_of_le_left (inf_le_left : A ⊓ B ≤ A)] at h2
  have hpos : 0 < Nat.card B * Nat.card (A ⊓ B : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc Nat.card B * Nat.card (A ⊓ B : Subgroup G) * B.relIndex (A ⊔ B)
      = Nat.card (A ⊓ B : Subgroup G) * (B.relIndex (A ⊔ B) * Nat.card B) := by ring
    _ = Nat.card (A ⊓ B : Subgroup G) * Nat.card (A ⊔ B : Subgroup G) := by rw [h1]
    _ = Nat.card A * Nat.card B := by rw [mul_comm, h]
    _ = Nat.card B * Nat.card (A ⊓ B : Subgroup G) * (A ⊓ B).relIndex A := by
        rw [← h2]; ring

theorem relIndex_sup_eq_relIndex_inf_right [Finite G] {N H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) :
    N.relIndex (N ⊔ H) = (N ⊓ H).relIndex H := by
  have h := card_sup_mul_card_inf_of_le_normalizer hH
  have h1 := Subgroup.relIndex_mul_card (H := N) (K := N ⊔ H)
  have h2 := Subgroup.relIndex_mul_card (H := N ⊓ H) (K := H)
  rw [inf_of_le_left (le_sup_left : N ≤ N ⊔ H)] at h1
  rw [inf_of_le_left (inf_le_right : N ⊓ H ≤ H)] at h2
  have hpos : 0 < Nat.card N * Nat.card (N ⊓ H : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc Nat.card N * Nat.card (N ⊓ H : Subgroup G) * N.relIndex (N ⊔ H)
      = Nat.card (N ⊓ H : Subgroup G) * (N.relIndex (N ⊔ H) * Nat.card N) := by ring
    _ = Nat.card (N ⊓ H : Subgroup G) * Nat.card (N ⊔ H : Subgroup G) := by rw [h1]
    _ = Nat.card N * Nat.card H := by rw [mul_comm, h]
    _ = Nat.card N * Nat.card (N ⊓ H : Subgroup G) * (N ⊓ H).relIndex H := by
        rw [← h2]; ring

structure PushHyp (X S Z : Subgroup G) : Prop where
  sylow : IsSylowTwoOf S X
  normal : X ≤ Subgroup.normalizer (Z : Set G)
  elemAbelian : IsElemAbelian 2 Z
  le_core : Z ≤ pCoreOf 2 X
  cent_eq : X ⊓ Subgroup.centralizer (Z : Set G) = pCoreOf 2 X

theorem pResidualOf_le_self (X : Subgroup G) [Finite G] : pResidualOf 2 X ≤ X := by
  rw [← oTwoUpper_eq_pResidualOf]
  exact oTwoUpper_le X

theorem le_normalizer_pResidualOf (X : Subgroup G) [Finite G] :
    X ≤ Subgroup.normalizer (pResidualOf 2 X : Set G) := by
  rw [← oTwoUpper_eq_pResidualOf]
  exact le_normalizer_oTwoUpper X

theorem exists_pow_mem_pResidualOf [Finite G] (X : Subgroup G) {x : G} (hx : x ∈ X) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ pResidualOf 2 X := by
  rw [← oTwoUpper_eq_pResidualOf]
  exact exists_pow_mem_oTwoUpper X hx

theorem pResidualOf_sup_eq_of_sylow [Finite G] {S X : Subgroup G} (hS : IsSylowTwoOf S X) :
    pResidualOf 2 X ⊔ S = X := by
  classical
  rw [← oTwoUpper_eq_pResidualOf]
  have hKH : oTwoUpper X ≤ X := oTwoUpper_le X
  refine le_antisymm (sup_le hKH hS.1) ?_
  have h1 : (oTwoUpper X ⊔ S).relIndex X ∣ S.relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X le_sup_right
  have h2 : (oTwoUpper X ⊔ S).relIndex X ∣ (oTwoUpper X).relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X le_sup_left
  have h3 : ∃ m : ℕ, (oTwoUpper X).relIndex X = 2 ^ m := by
    have hn : ((oTwoUpper X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper X)
    have hp : IsPGroup 2 (↥X ⧸ (oTwoUpper X).subgroupOf X) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X h.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := h3
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    apply hS.2.2
    have h2d : 2 ∣ (oTwoUpper X ⊔ S).relIndex X := by
      rw [hj]
      exact dvd_pow_self 2 hne
    exact h2d.trans h1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

theorem relIndex_residual_inf_sylow [Finite G] {S X : Subgroup G} (hS : IsSylowTwoOf S X) :
    ¬ 2 ∣ (pResidualOf 2 X ⊓ S).relIndex (pResidualOf 2 X) := by
  have hSn : S ≤ Subgroup.normalizer (pResidualOf 2 X : Set G) :=
    hS.1.trans (le_normalizer_pResidualOf X)
  have h := relIndex_sup_eq_relIndex_inf hSn
  rw [pResidualOf_sup_eq_of_sylow hS] at h
  rw [← h]
  exact hS.2.2

theorem pCoreOf_le_of_sylow [Finite G] {S X : Subgroup G} (hS : IsSylowTwoOf S X) :
    pCoreOf 2 X ≤ S := by
  have hS' : IsPGroup 2 (S.subgroupOf X) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 X := hS'.toSylow hS.2.2
  have : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 X ≤ (P : Subgroup X) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) P
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  have h3 : (P : Subgroup X).map X.subtype = S := by
    change (S.subgroupOf X).map X.subtype = S
    rw [Subgroup.map_subgroupOf_eq_of_le hS.1]
  change Subgroup.map X.subtype (CFSG.Open.pCore 2 X) ≤ S
  rw [← h3]
  exact h2

namespace PushHyp

variable {X S Z : Subgroup G} (h : PushHyp X S Z)

include h

theorem le_self : S ≤ X := h.sylow.1

omit h in
theorem le_normalizer_core : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X

theorem core_le_centralizer : pCoreOf 2 X ≤ Subgroup.centralizer (Z : Set G) := by
  rw [← h.cent_eq]
  exact inf_le_right

theorem mem_core_of_centralizes {x : G} (hx : x ∈ X)
    (hc : x ∈ Subgroup.centralizer (Z : Set G)) : x ∈ pCoreOf 2 X := by
  rw [← h.cent_eq]
  exact ⟨hx, hc⟩

variable [Finite G]

theorem core_le : pCoreOf 2 X ≤ S := pCoreOf_le_of_sylow h.sylow

theorem Z_le : Z ≤ S := h.le_core.trans h.core_le

theorem inf_centralizer_eq : S ⊓ Subgroup.centralizer (Z : Set G) = pCoreOf 2 X := by
  refine le_antisymm ?_ (le_inf h.core_le (h.cent_eq ▸ inf_le_right))
  rw [← h.cent_eq]
  exact inf_le_inf_right _ h.le_self |>.trans le_rfl

end PushHyp

theorem sylow_conjClosure_of_residual_inf_le [Finite G] {X S B : Subgroup G}
    (hS : IsSylowTwoOf S X) (hBS : B ≤ S) (hBn : S ≤ Subgroup.normalizer (B : Set G))
    (h : pResidualOf 2 X ⊓ S ≤ B) : IsSylowTwoOf B (conjClosure B X) := by
  set L := pResidualOf 2 X with hL
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_pResidualOf X
  have hLX : L ≤ X := pResidualOf_le_self X
  have hXLS : L ⊔ S = X := pResidualOf_sup_eq_of_sylow hS
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBS.trans (hS.1.trans hXL)
  have hK : conjClosure B X ≤ L ⊔ B := by
    refine conjClosure_le fun x hx b hb => ?_
    rw [← hXLS] at hx
    obtain ⟨l, hl, s, hs, rfl⟩ := mem_sup_of_le_normalizer (hS.1.trans hXL) hx
    have hsb : s * b * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hBn hs) b).mp hb
    have hb' : (s * b * s⁻¹) ∈ L ⊔ B := Subgroup.mem_sup_right hsb
    set b' := s * b * s⁻¹ with hb'def
    have hbX : b' ∈ X := hS.1 (hBS hsb)
    have hc : b' * l⁻¹ * b'⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hXL hbX) l⁻¹).mp (L.inv_mem hl)
      exact this
    have : l * s * b * (l * s)⁻¹ = (l * (b' * l⁻¹ * b'⁻¹)) * b' := by
      simp only [hb'def]; group
    rw [this]
    exact (L ⊔ B).mul_mem (Subgroup.mem_sup_left (L.mul_mem hl hc)) hb'
  refine ⟨le_conjClosure B X, hS.2.1.to_le hBS, ?_⟩
  have h1 : B.relIndex (conjClosure B X) ∣ B.relIndex (L ⊔ B) := by
    have := Subgroup.relIndex_mul_relIndex B (conjClosure B X) (L ⊔ B) (le_conjClosure B X) hK
    exact Dvd.intro _ this
  have h2 : B.relIndex (L ⊔ B) = (L ⊓ B).relIndex L := relIndex_sup_eq_relIndex_inf hBL
  have h3 : L ⊓ B = L ⊓ S := le_antisymm (inf_le_inf_left L hBS) (le_inf inf_le_left h)
  rw [h3] at h2
  intro hd
  apply relIndex_residual_inf_sylow hS
  exact hd.trans (h1.trans (h2 ▸ dvd_rfl))

end CFSG.Quasithin.F53Push
