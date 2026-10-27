module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Plane
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
import CFSG.RankThree.PartOne.CTP.StrongPTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c K7 LieFam811 IsLie811 IsSignedCoords qPlusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

omit [Finite G] in
theorem GoodPoint.centralizer_le {M : Subgroup G} {x : G} (hx : GoodPoint M x) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro y hy
  apply hx
  have hy' : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hy
  exact Subgroup.centralizer_le_normalizer _ hy'

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem dvd_card_inf_centralizer_of_k7 (h : Case811Sylow c) (hK7 : K7) {f p : ℕ}
    (hlie : IsLie811 c.Lbar .psp6 2 f) (hp : p ∈ D.sig) (hpq : p ∣ qPlusPi 2 f)
    {X : Subgroup G} (hXA : X ≤ h.A) (hXcard : Nat.card X = 3) :
    p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  have hK := hK7 c.Lbar .psp6 2 f hlie p hp_prime hp5 hp2 h.Abar h.isElemAbelian_Abar
    h.card_Abar
  obtain ⟨-, hdvdXbar, -⟩ := (hK.2.1 hpq).2.2.1 (Or.inl rfl)
  have hXbar_le : (X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) ≤
      h.Abar := h.map_le_Abar hXA
  have hXbar_card : Nat.card ((X.subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) = 3 := by
    rw [h.card_map_of_le_A hXA, hXcard]
  exact (Ctx82E3.dvd_card_centralizer_lbar_iff c (q := 3) (by norm_num) (p := p) hp2
    (hXA.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hXA)).mpr
    (hdvdXbar _ hXbar_le hXbar_card)

private theorem dvdM_of_dvd (h : Case811Sylow c) {p : ℕ}
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :
    ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
  fun X hX h3 => (hdvd X hX h3).trans (Subgroup.card_dvd_of_le (inf_le_inf c.hyp81.1 le_rfl))

theorem mem_of_fusion_of_good_of_dvdM (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (hdvdM : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    {x : G} (hx3 : orderOf x = 3) (hgood : GoodPoint D.M x) {g : G}
    (hg : g * x * g⁻¹ ∈ D.M) : g ∈ D.M := by
  have : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hord : ∀ k : G, orderOf (k * x * k⁻¹) = 3 := fun k => by
    rw [← hx3]
    exact orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective x
  obtain ⟨m, hmM, hmy⟩ := h.cover _ hg (hord g)
  have hz : (m * g) * x * (m * g)⁻¹ ∈ h.A := by simpa [mul_assoc] using hmy
  have hXz : Subgroup.zpowers ((m * g) * x * (m * g)⁻¹) ≤ h.A := Subgroup.zpowers_le.mpr hz
  have hXzcard : Nat.card (Subgroup.zpowers ((m * g) * x * (m * g)⁻¹)) = 3 := by
    rw [Nat.card_zpowers, hord (m * g)]
  have h1 := hdvdM _ hXz hXzcard
  have hmap : (Subgroup.zpowers x).map (MulAut.conj (m * g)).toMonoidHom =
      Subgroup.zpowers ((m * g) * x * (m * g)⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hdvd' : p ∣ Nat.card (D.M ⊓ Subgroup.centralizer
      (((Subgroup.zpowers x).map (MulAut.conj (m * g)).toMonoidHom : Subgroup G) : Set G) :
        Subgroup G) := by
    rw [hmap]
    exact h1
  have hCx : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer _).trans hgood
  have hmg : m * g ∈ D.M :=
    (c.isStronglyPEmbedded_of_mem_sigma hp).mem_of_centralizer_le hCx hdvd'
  have hg' : g = m⁻¹ * (m * g) := by simp
  rw [hg']
  exact D.M.mul_mem (D.M.inv_mem hmM) hmg

theorem good_of_centralizer_le_of_dvdM (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (hdvdM : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    {x : G} (hxA : x ∈ h.A) (hx3 : orderOf x = 3)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) : GoodPoint D.M x := by
  have : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  intro g hg
  have hXA : Subgroup.zpowers x ≤ h.A := Subgroup.zpowers_le.mpr hxA
  have hXcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hCx : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ D.M := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hC
  have hmap : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hdvd' : p ∣ Nat.card (D.M ⊓ Subgroup.centralizer
      (((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :
        Subgroup G) := by
    rw [hmap]
    exact hdvdM _ hXA hXcard
  exact (c.isStronglyPEmbedded_of_mem_sigma hp).mem_of_centralizer_le hCx hdvd'

theorem good_of_centralizer_le (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    {x : G} (hxA : x ∈ h.A) (hx3 : orderOf x = 3)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) : GoodPoint D.M x :=
  h.good_of_centralizer_le_of_dvdM hp (dvdM_of_dvd h hdvd) hxA hx3 hC

theorem normalizer_A_le_of_dvdM (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (hdvdM : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    {x : G} (hxA : x ∈ h.A) (hx3 : orderOf x = 3) (hgood : GoodPoint D.M x) :
    Subgroup.normalizer (h.A : Set G) ≤ D.M := by
  intro n hn
  refine h.mem_of_fusion_of_good_of_dvdM hp hdvdM hx3 hgood ?_
  have hnx : n * x * n⁻¹ ∈ h.A := (Subgroup.mem_normalizer_iff.mp hn x).mp hxA
  exact c.hyp81.1 (h.A_le_L hnx)

theorem normalizer_A_le (h : Case811Sylow c) {p : ℕ} (hp : p ∈ D.sig)
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    {x : G} (hxA : x ∈ h.A) (hx3 : orderOf x = 3) (hgood : GoodPoint D.M x) :
    Subgroup.normalizer (h.A : Set G) ≤ D.M :=
  h.normalizer_A_le_of_dvdM hp (dvdM_of_dvd h hdvd) hxA hx3 hgood

theorem mem_normalizer_A_of_mem_normalizer_P (h : Case811Sylow c) {n : G}
    (hn : n ∈ Subgroup.normalizer (h.P : Set G)) : n ∈ Subgroup.normalizer (h.A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hBP : h.A.map (MulAut.conj n).toMonoidHom ≤ h.P := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn x).mp (h.A_le hx)
  have hBab : CFSG.Open.IsElemAbelian 3 (h.A.map (MulAut.conj n).toMonoidHom) :=
    h.elemAbelian.map _
  have hBcard : Nat.card (h.A.map (MulAut.conj n).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_A]
  exact h.unique _ hBP hBab hBcard

theorem normalizer_P_le (h : Case811Sylow c)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M) :
    Subgroup.normalizer (h.P : Set G) ≤ D.M :=
  fun _ hn => hNA (h.mem_normalizer_A_of_mem_normalizer_P hn)

theorem isSylowOf_top (h : Case811Sylow c)
    (hNP : Subgroup.normalizer (h.P : Set G) ≤ D.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22q_isSylowOf_top_of_normalizer h.sylow hNP

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
