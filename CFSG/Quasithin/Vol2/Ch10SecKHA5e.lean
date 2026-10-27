module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Vol2.Ch10SecKHA5d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate3017
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate4033
public import Certificates.Certificate4034
public import Certificates.Certificate4068
public import Certificates.Certificate4075
public import Certificates.Certificate4080
public import Certificates.Certificate4102
public import Certificates.Certificate4140
public import Certificates.Certificate4141
public import Certificates.Certificate4143

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem not_isSL25_of_overgroups {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X)
    {t₂ : ℕ} (ht₂ : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → Nat.card T = t₂)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y = ⊤ ∨
      (Nat.card Y = 15 * t₂ → ∃ q : ℕ, q * 128 < t₂ ∧ ∀ (N : Subgroup ↥Y) [N.Normal],
        IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ q))
    {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hne : B ≠ ⊤)
    (hTB : T ≤ Subgroup.normalizer (B : Set X)) : ¬ IsSL25Group ↥B := by
  intro hD
  obtain ⟨j, hj1, hj2, hnorm, hq⟩ := sl25_sup_data hT hD hTB
  have hYN : B ⊔ T ≤ Subgroup.normalizer (B : Set X) := sup_le Subgroup.le_normalizer hTB
  rcases hover T (B ⊔ T) hT le_sup_right with htop | hrow
  · have hBn : B.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ Subgroup.normalizer (B : Set X) := hYN (htop ▸ Subgroup.mem_top g)
      exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
    · have h1 := hD.card
      rw [h, Subgroup.card_bot] at h1
      omega
    · exact hne h
  · have ht2 : t₂ = 2 ^ (7 + j) := by rw [← ht₂ T hT, hj1]
    have hY15 : Nat.card ↥(B ⊔ T) = 15 * t₂ := by
      rw [hj2, ht2, pow_add]
      ring
    obtain ⟨q, hq128, hqN⟩ := hrow hY15
    have := hnorm
    have hle := hqN (B.subgroupOf (B ⊔ T)) (IsPGroup.of_card hq)
    rw [hq] at hle
    have h1 : 2 ^ j * 128 ≤ q * 128 := Nat.mul_le_mul_right 128 hle
    have h2 : t₂ = 2 ^ j * 128 := by rw [ht2, pow_add]; ring
    omega

theorem noSL25In_of_overgroups {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {t₂ : ℕ}
    (ht₂ : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → Nat.card T = t₂)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y = ⊤ ∨
      (Nat.card Y = 15 * t₂ → ∃ q : ℕ, q * 128 < t₂ ∧ ∀ (N : Subgroup ↥Y) [N.Normal],
        IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ q)) :
    NoSL25In X :=
  fun _ hT _ _ hne hTB => not_isSL25_of_overgroups hX ht₂ hover hT hne hTB

theorem noSL25In_of_rows {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {a m : ℕ}
    (hm : ¬ 2 ∣ m) (hcard : Nat.card X = 2 ^ a * m) (mems : List Mem)
    (hmems : ∀ r ∈ mems, r.order = 15 * 2 ^ a → r.quot2 * 128 < 2 ^ a)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y = ⊤ ∨
      ∃ r ∈ mems, Nat.card Y = r.order ∧ Nat.card (pCoreOf 2 Y) = r.o2 ∧
        ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ r.quot2) :
    NoSL25In X := by
  refine noSL25In_of_overgroups hX (t₂ := 2 ^ a)
    (fun T hT => A5.G3.card_eq_of_isSylowTwoOf hT hm hcard) ?_
  intro T Y hT hTY
  rcases hover T Y hT hTY with h | ⟨r, hr, hord, -, hq⟩
  · exact Or.inl h
  · refine Or.inr fun hY => ?_
    rw [hord] at hY
    exact ⟨r.quot2, hmems r hr hY, fun N _ hN => hq N hN⟩

theorem noSL25In_m24
    {X : Type} [Group X] [Finite X] (h : IsSporadic .M24 X) : NoSL25In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 10 * 239085 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24.trans (by norm_num)
  exact noSL25In_of_rows hX (by norm_num) hcard M24.m24Mems (by decide +kernel)
    (fun T Y hT hTY => M24.m24_overgroups ⟨e⟩ hT hTY)

theorem noSL25In_hs
    {X : Type} [Group X] [Finite X] (h : IsSporadic .HS X) : NoSL25In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
    CFSG.Sporadic.HS.isSimpleGroup_HS
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 9 * 86625 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS.trans (by norm_num)
  exact noSL25In_of_rows hX (by norm_num) hcard HS.hsMems (by decide +kernel)
    (fun T Y hT hTY => HS.hs_overgroups ⟨e⟩ hT hTY)

theorem noSL25In_he
    {X : Type} [Group X] [Finite X] (h : IsSporadic .He X) : NoSL25In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He.trans (by norm_num)
  exact noSL25In_of_rows hX (by norm_num) hcard He.heMems (by decide +kernel)
    (fun T Y hT hTY => He.he_overgroups ⟨e⟩ hT hTY)

theorem noSL25In_ru
    {X : Type} [Group X] [Finite X] (h : IsSporadic .Ru X) : NoSL25In X := by
  obtain ⟨e⟩ := h
  have hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcard : Nat.card X = 2 ^ 14 * 8906625 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru.trans (by norm_num)
  exact noSL25In_of_rows hX (by norm_num) hcard Ru.ruMems (by decide +kernel)
    (fun T Y hT hTY => Ru.ru_overgroups ⟨e⟩ hT hTY)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
