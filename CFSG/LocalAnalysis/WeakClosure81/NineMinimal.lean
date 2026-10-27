module

public import CFSG.LocalAnalysis.WeakClosure81.NineStruct
public import CFSG.LocalAnalysis.WeakClosure81.NineMinA
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T X : Subgroup G} {p : ℕ}

private theorem nineMinimal_sup_eq_mul {X T : Subgroup G}
    (hXT : (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G)) :
    ((X ⊔ T : Subgroup G) : Set G) = (X : Set G) * (T : Set G) := by
  let H : Subgroup G :=
    { carrier := (X : Set G) * (T : Set G)
      one_mem' := ⟨1, X.one_mem, 1, T.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro a b ⟨x₁, hx₁, t₁, ht₁, rfl⟩ ⟨x₂, hx₂, t₂, ht₂, rfl⟩
        have htx : t₁ * x₂ ∈ (T : Set G) * (X : Set G) := ⟨t₁, ht₁, x₂, hx₂, rfl⟩
        rw [← hXT] at htx
        obtain ⟨x₃, hx₃, t₃, ht₃, htx_eq⟩ := htx
        refine ⟨x₁ * x₃, X.mul_mem hx₁ hx₃, t₃ * t₂, T.mul_mem ht₃ ht₂, ?_⟩
        calc
          (x₁ * x₃) * (t₃ * t₂) = x₁ * (x₃ * t₃) * t₂ := by group
          _ = x₁ * (t₁ * x₂) * t₂ := by rw [show x₃ * t₃ = t₁ * x₂ from htx_eq]
          _ = (x₁ * t₁) * (x₂ * t₂) := by group
      inv_mem' := by
        rintro a ⟨x, hx, t, ht, rfl⟩
        have htx : t⁻¹ * x⁻¹ ∈ (T : Set G) * (X : Set G) :=
          ⟨t⁻¹, T.inv_mem ht, x⁻¹, X.inv_mem hx, rfl⟩
        rw [← hXT] at htx
        obtain ⟨x', hx', t', ht', htx_eq⟩ := htx
        exact ⟨x', hx', t', ht', by rw [htx_eq]; group⟩ }
  have hle : X ⊔ T ≤ H :=
    sup_le (fun x hx => ⟨x, hx, 1, T.one_mem, mul_one x⟩)
      (fun t ht => ⟨1, X.one_mem, t, ht, one_mul t⟩)
  refine le_antisymm (fun g hg => hle hg) ?_
  rintro g ⟨x, hx, t, ht, rfl⟩
  exact (X ⊔ T).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ht)

private theorem nineMinimal_frattini_argument {p : ℕ} [Fact p.Prime] {H N P : Subgroup G}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hP : IsSylowIn p P N) {h : G} (hh : h ∈ H) :
    ∃ k ∈ N, ∃ n ∈ H ⊓ normalizer (P : Set G), h = k * n := by
  have hHN : H ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
  obtain ⟨k, hk, hkx⟩ := Ch1Sec3.exists_conj_of_isSylowIn hP
    (Ch1Sec3.isSylowIn_map_conj hP (hHN hh))
  refine ⟨k, hk, k⁻¹ * h, Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem (hNH hk)) hh, ?_⟩,
    by group⟩
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  have h1 : h * z * h⁻¹ ∈ P.map (MulAut.conj h).toMonoidHom ↔ z ∈ P := by
    constructor
    · rintro ⟨y, hy, hyz⟩
      have : y = z := by simpa [mul_assoc] using hyz
      exact this ▸ hy
    · intro hz
      exact ⟨z, hz, by simp⟩
  rw [← h1, hkx]
  have e : k⁻¹ * (h * z * h⁻¹) * k = k⁻¹ * h * z * (k⁻¹ * h)⁻¹ := by group
  rw [e]

theorem twoPTwo_of_minimal {W : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hT : IsPGroup 2 T) (hXT : (X : Set G) * T = T * X) (hTW : T ≤ normalizer (W : Set G))
    (hKW : ¬ X ⊔ T ≤ normalizer (W : Set G))
    (hmin : ∀ K₀ : Subgroup G, T ≤ K₀ → K₀ < X ⊔ T → K₀ ≤ normalizer (W : Set G)) :
    TwoPTwo (X ⊔ T) T X p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := X ⊔ T
  have hXK : X ≤ K := le_sup_left
  have hTK : T ≤ K := le_sup_right
  have hKT : (K : Set G) = (X : Set G) * (T : Set G) := nineMinimal_sup_eq_mul hXT
  have hX' : IsPGroup p (X.subgroupOf K) := hX.comap_subtype
  have hT' : IsPGroup 2 (T.subgroupOf K) := hT.comap_subtype
  have hdisj' : Disjoint (X.subgroupOf K) (T.subgroupOf K) :=
    IsPGroup.disjoint_of_ne p 2 hp2 _ _ hX' hT'
  have hXT' : (X.subgroupOf K : Set ↥K) * (T.subgroupOf K : Set ↥K) = Set.univ := by
    ext q
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    have hq : (q : G) ∈ (X : Set G) * (T : Set G) := by
      rw [← hKT]
      exact q.2
    obtain ⟨x, hx, t, ht, hxt⟩ := hq
    exact ⟨⟨x, hXK hx⟩, hx, ⟨t, hTK ht⟩, ht, Subtype.ext hxt⟩
  have hcardK : Nat.card ↥K = Nat.card ↥X * Nat.card ↥T := by
    have h1 : Nat.card ↥(X.subgroupOf K) * Nat.card ↥(T.subgroupOf K) = Nat.card ↥K :=
      (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hXT').card_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  have hcardK' : Nat.card ↥K = p ^ a * 2 ^ b := by rw [hcardK, ha, hb]
  have hTsyl : IsSylowIn 2 T K := by
    refine ⟨hTK, hT, ?_⟩
    intro hdvd
    have h := Subgroup.relIndex_mul_card T K
    rw [inf_eq_left.mpr hTK, hcardK', hb] at h
    have hTi : T.relIndex K = p ^ a := Nat.mul_right_cancel (pow_pos (by norm_num) b) h
    rw [hTi] at hdvd
    have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  have hXsyl : IsSylowIn p X K := by
    refine ⟨hXK, hX, ?_⟩
    intro hdvd
    have h := Subgroup.relIndex_mul_card X K
    rw [inf_eq_left.mpr hXK, hcardK', ha] at h
    have h' : X.relIndex K * p ^ a = 2 ^ b * p ^ a := by rw [h, mul_comm]
    have hXi : X.relIndex K = 2 ^ b := Nat.mul_right_cancel (pow_pos hp.pos a) h'
    rw [hXi] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hN : (normalizer (W : Set G)).subgroupOf K ≠ ⊤ := by
    intro hNtop
    apply hKW
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ (normalizer (W : Set G)).subgroupOf K := by
      rw [hNtop]
      trivial
    exact this
  have hTN : T.subgroupOf K ≤ (normalizer (W : Set G)).subgroupOf K := fun t ht => hTW ht
  have hmax : ∀ L : Subgroup ↥K, T.subgroupOf K ≤ L → L ≠ ⊤ →
      L ≤ (normalizer (W : Set G)).subgroupOf K := by
    intro L hTL hLtop
    let L₀ : Subgroup G := L.map K.subtype
    have hTL₀ : T ≤ L₀ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hTK]
      exact Subgroup.map_mono hTL
    have hL₀K : L₀ ≤ K := Subgroup.map_subtype_le L
    have hL₀ne : L₀ ≠ K := by
      intro hL₀
      apply hLtop
      have hmap : L.map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
        exact hL₀
      exact Subgroup.map_injective K.subtype_injective hmap
    have hL₀N : L₀ ≤ normalizer (W : Set G) :=
      hmin L₀ hTL₀ (lt_of_le_of_ne hL₀K hL₀ne)
    intro l hl
    exact hL₀N ⟨l, hl, rfl⟩
  have hoTwo : E1.oTwoPTwo ↥K p = ⊤ :=
    oTwoPTwo_eq_top_of_unique_max hp hp2 hX' hT' hXT' hTN hN hmax
  exact ⟨hp, hp2, hoTwo, hTsyl, hXsyl⟩

theorem TwoPTwo.exists_mul_pCoreOf_inf_normalizer {K S : Subgroup G} (h : TwoPTwo K S X p)
    {t : G} (ht : t ∈ S) :
    ∃ r ∈ pCoreOf 2 K, ∃ n ∈ S ⊓ normalizer (X : Set G), t = r * n := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  let R : Subgroup G := pCoreOf 2 K
  let P : Subgroup G := R ⊔ X
  have hPK : P ≤ K := sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) h.sylowP.le
  have hPN : (P.subgroupOf K).Normal := h.normal_pCoreOf_sup
  have hXP : X ≤ P := le_sup_right
  have hPX : IsSylowIn p X P := by
    refine ⟨hXP, h.sylowP.isPGroup, ?_⟩
    intro hdvd
    have hrel : X.relIndex P ∣ X.relIndex K :=
      ⟨P.relIndex K, (Subgroup.relIndex_mul_relIndex X P K hXP hPK).symm⟩
    exact h.sylowP.not_dvd_relIndex (hdvd.trans hrel)
  obtain ⟨k, hk, n', hn', hkn⟩ :=
    nineMinimal_frattini_argument hPK hPN hPX (h.sylowTwo.le ht)
  have hXnormR : X ≤ normalizer (R : Set G) :=
    h.sylowP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hkXR : k ∈ (X : Set G) * (R : Set G) := by
    have hcoe : ((X ⊔ R : Subgroup G) : Set G) = (X : Set G) * (R : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right X R hXnormR
    rw [← hcoe]
    have hk' : k ∈ X ⊔ R := by
      rw [sup_comm]
      exact hk
    exact hk'
  obtain ⟨x, hx, r₀, hr₀, hxr⟩ := hkXR
  have hrR : x * r₀ * x⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hXnormR hx) r₀).mp hr₀
  refine ⟨x * r₀ * x⁻¹, hrR, x * n', Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · have hrt : x * n' = (x * r₀ * x⁻¹)⁻¹ * t := by
      rw [hkn, ← hxr]
      group
    rw [hrt]
    exact S.mul_mem (h.pCoreOf_le_sylowTwo (R.inv_mem hrR)) ht
  · exact (normalizer (X : Set G)).mul_mem (Subgroup.le_normalizer hx) hn'.2
  · rw [hkn, ← hxr]
    group

end CFSG.LocalAnalysis.WeakClosure81
