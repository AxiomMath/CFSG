module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C24Pf

variable {G : Type} [Group G] [Finite G]

theorem inf_le_blockQ {L D : Subgroup G} (hL : IsShort2 L)
    (hLD : L ≤ Subgroup.normalizer (D : Set G))
    (hD : ∀ d ∈ D ⊓ L, ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (blockU L : Set G)) :
    D ⊓ L ≤ blockQ L := by
  set Q := blockQ L with hQ
  have hQ2 : IsPGroup 2 ↥Q := C1.blockQ_isPGroup L
  have hQL : Q ≤ L := C1.blockQ_le L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := C1.le_normalizer_blockQ L
  have hDLn : Q ≤ Subgroup.normalizer ((D ⊓ L : Subgroup G) : Set G) := fun q hq =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLD (hQL hq), Subgroup.le_normalizer (hQL hq)⟩
  have hpow : ∀ d ∈ D ⊓ L, ∃ k : ℕ, d ^ 2 ^ k ∈ Q := by
    intro d hd
    obtain ⟨k, hk⟩ := hD d hd
    exact ⟨k, C1.inf_centralizer_blockU_le hL ⟨L.pow_mem hd.2 _, hk⟩⟩
  have hN2 : IsPGroup 2 ↥((D ⊓ L) ⊔ Q : Subgroup G) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := C1.exists_pow_mem_of_mem_sup hQ2 hDLn hg
    obtain ⟨j, hj⟩ := hpow _ hk
    obtain ⟨m, hm⟩ := C1.exists_pow_eq_one_of_isPGroup hQ2 hj
    refine ⟨k + j + m, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_add, pow_mul, pow_mul, hm]
  have hNL : (D ⊓ L) ⊔ Q ≤ L := sup_le inf_le_right hQL
  have hLN : L ≤ Subgroup.normalizer (((D ⊓ L) ⊔ Q : Subgroup G) : Set G) := fun l hl =>
    C1.mem_normalizer_sup (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hLD hl, Subgroup.le_normalizer hl⟩) (hLQ hl)
  exact le_sup_left.trans (C1.le_pCoreOf_of_normalized hNL hLN hN2)

theorem isTwoReducedIn_blockU {L X : Subgroup G} (hL : IsShort2 L) (hLX : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) : IsTwoReducedIn X (blockU L) := by
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)
  refine ⟨hUL.trans hLX, fun x hx => C1.mem_normalizer_blockU (hXN hx),
    C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hL), fun D hDX hXD hD => ?_⟩
  have hDL : D ⊓ L ≤ blockQ L :=
    inf_le_blockQ hL (hLX.trans hXD) fun d hd => hD d hd.1
  intro d hd
  have hcomm : ∀ e ∈ D, ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ blockQ L := by
    intro e he l hl
    refine hDL ⟨?_, ?_⟩
    · have h1 : l * e⁻¹ * l⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hXD (hLX hl)) _).mp (D.inv_mem he)
      have e1 : e * l * e⁻¹ * l⁻¹ = e * (l * e⁻¹ * l⁻¹) := by group
      rw [e1]
      exact D.mul_mem he h1
    · have h1 : e * l * e⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hXN (hDX he)) _).mp hl
      exact L.mul_mem h1 (L.inv_mem hl)
  obtain ⟨k, hk⟩ := hD d hd
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hy2 : ∃ j : ℕ, (d ^ b) ^ 2 ^ j = 1 :=
    ⟨a, by rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]⟩
  have hyc : ∀ u ∈ blockU L, u * d ^ b = d ^ b * u :=
    C1.commute_blockU_of_mem hL (hXN (hDX (D.pow_mem hd b))) hy2
      (hcomm _ (D.pow_mem hd b))
  have hyC : d ^ b ∈ Subgroup.centralizer (blockU L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => hyc u hu
  have hcop : Nat.Coprime (2 ^ k) b :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hb)
  have hgcd : ((Nat.gcd (2 ^ k) b : ℕ) : ℤ) = (2 ^ k : ℕ) * Nat.gcdA (2 ^ k) b +
      (b : ℤ) * Nat.gcdB (2 ^ k) b := Nat.gcd_eq_gcd_ab _ _
  rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
  have e : d = (d ^ 2 ^ k) ^ Nat.gcdA (2 ^ k) b * (d ^ b) ^ Nat.gcdB (2 ^ k) b := by
    have h1 : (d ^ 2 ^ k) ^ Nat.gcdA (2 ^ k) b =
        d ^ (((2 ^ k : ℕ) : ℤ) * Nat.gcdA (2 ^ k) b) := by
      rw [zpow_mul, zpow_natCast]
    have h2 : (d ^ b) ^ Nat.gcdB (2 ^ k) b = d ^ ((b : ℤ) * Nat.gcdB (2 ^ k) b) := by
      rw [zpow_mul, zpow_natCast]
    rw [h1, h2, ← zpow_add, ← hgcd, zpow_one]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hk _) (Subgroup.zpow_mem _ hyC _)

theorem isSylowTwoOf_sup {L T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (h : IsSylowTwoOf (T ⊓ L) L) :
    IsSylowTwoOf T (L ⊔ T) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hT, fun P hPH hP hTP => ?_⟩
  intro t ht
  have htH : t ∈ T ⊔ L := by rw [sup_comm]; exact hPH ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T L hTL] at htH
  obtain ⟨r, hr, k, hk, rfl⟩ := htH
  have hkP : k ∈ P := by
    have := P.mul_mem (P.inv_mem (hTP hr)) ht
    simpa using this
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp h).2.2 (P ⊓ L) inf_le_right hP.to_inf_left
    (le_inf (inf_le_left.trans hTP) inf_le_right)
  exact T.mul_mem hr (hmax ⟨hkP, hk⟩).1

theorem exists_isFFOffender {L T : Subgroup G} (hL : IsShort2 L) (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (T ⊓ L) L)
    (hJ : ⁅L, thompsonJ T⁆ = L) :
    IsTwoReducedIn (L ⊔ T) (blockU L) ∧
      ∃ A : Subgroup G, A ≤ T ∧ IsFFOffender (L ⊔ T) (blockU L) A := by
  have hXN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  refine ⟨isTwoReducedIn_blockU hL le_sup_left hXN, ?_⟩
  have hTsyl := isSylowTwoOf_sup hT hTL hsyl
  by_contra hno
  push Not at hno
  have hJC : thompsonJ T ≤ Subgroup.centralizer (blockU L : Set G) := by
    refine iSup₂_le fun A hA => ?_
    by_contra hAC
    exact hno A hA.1 ⟨B6.isMaxElemAbelian_of_sylow hTsyl hA, hAC⟩
  have hLC : L ≤ Subgroup.centralizer (blockU L : Set G) := by
    suffices hc : ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (blockU L : Set G) by rwa [hJ] at hc
    rw [Subgroup.commutator_le]
    intro l hl j hj
    have hlN : l ∈ Subgroup.normalizer (Subgroup.centralizer (blockU L : Set G) : Set G) :=
      Subgroup.mem_normalizer_iff.mpr fun c => by
        have hlU := C1.mem_normalizer_blockU (Subgroup.le_normalizer hl)
        constructor
        · intro hc
          rw [Subgroup.mem_centralizer_iff] at hc ⊢
          intro u hu
          have hu' : l⁻¹ * u * l⁻¹⁻¹ ∈ blockU L :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlU) u).mp hu
          have := hc _ hu'
          calc u * (l * c * l⁻¹) = l * ((l⁻¹ * u * l⁻¹⁻¹) * c) * l⁻¹ := by group
            _ = l * (c * (l⁻¹ * u * l⁻¹⁻¹)) * l⁻¹ := by rw [this]
            _ = l * c * l⁻¹ * u := by group
        · intro hc
          rw [Subgroup.mem_centralizer_iff] at hc ⊢
          intro u hu
          have hu' : l * u * l⁻¹ ∈ blockU L :=
            (Subgroup.mem_normalizer_iff.mp hlU u).mp hu
          have := hc _ hu'
          calc u * c = l⁻¹ * ((l * u * l⁻¹) * (l * c * l⁻¹)) * l := by group
            _ = l⁻¹ * ((l * c * l⁻¹) * (l * u * l⁻¹)) * l := by rw [this]
            _ = c * u := by group
    rw [commutatorElement_def]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (hJC hj))
    exact (Subgroup.mem_normalizer_iff.mp hlN j).mp (hJC hj)
  have hUZ : blockU L ≤ blockZ L := fun u hu =>
    ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLC hl) u hu).symm⟩
  exact (not_le_of_gt hL.2.2.2.2.1) hUZ

end C24Pf

end CFSG.Quasithin
