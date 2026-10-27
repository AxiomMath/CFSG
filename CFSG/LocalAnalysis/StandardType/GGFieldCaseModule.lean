module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL44
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type*} [Group G]

theorem eq_of_lt_of_card_le_mul [Finite G] {p : ℕ} [hp : Fact p.Prime] {V B₂ T : Subgroup G}
    (hV : IsPGroup p V) (hB₂T : B₂ < T) (hTV : T ≤ V) (hcard : Nat.card V ≤ p * Nat.card B₂) :
    T = V := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hV
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hB₂T.le
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hTV
  have hB₂pos : 0 < Nat.card B₂ := Nat.card_pos
  have hlt := Subgroup.card_lt_of_lt hB₂T
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exfalso
      interval_cases k
      · rw [mul_zero] at hk
        exact absurd hk (Nat.card_pos (α := T)).ne'
      · rw [mul_one] at hk
        omega
    · exact h
  have hkm : k * m ≤ p := by
    have : Nat.card B₂ * (k * m) ≤ Nat.card B₂ * p := by
      rw [← mul_assoc, ← hk, ← hm]; linarith
    exact Nat.le_of_mul_le_mul_left this hB₂pos
  have hdvd : k * m ∣ p ^ a := ⟨Nat.card B₂, by rw [← ha, hm, hk]; ring⟩
  obtain ⟨c, -, hkmc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact absurd hm (Nat.card_pos (α := V)).ne'
  have hc1 : c = 1 := by
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c
      · simp at hkmc; nlinarith [Nat.pos_of_ne_zero hm0]
      · rfl
    · have : p ^ 2 ≤ p ^ c := Nat.pow_le_pow_right hp.out.pos hc
      nlinarith [hp.out.two_le]
  have hkp : k ∣ p := ⟨m, by rw [← pow_one p, ← hc1, hkmc]⟩
  have hk' : k = p := (Nat.Prime.eq_one_or_self_of_dvd hp.out k hkp).resolve_left (by omega)
  have hm1 : m = 1 := by
    subst hk'
    have : k * m = k * 1 := by rw [hkmc, hc1, pow_one, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  exact Subgroup.eq_of_le_of_card_ge hTV (by rw [hm, hm1, mul_one])

theorem conj_mem_sup_of_conj_mem {I Z : Subgroup G} {n : G}
    (hI : ∀ i ∈ I, n * i * n⁻¹ ∈ I) (hZ : ∀ z ∈ Z, n * z * n⁻¹ ∈ Z) :
    ∀ s ∈ I ⊔ Z, n * s * n⁻¹ ∈ I ⊔ Z := by
  have hle : I ⊔ Z ≤ (I ⊔ Z).comap (MulAut.conj n).toMonoidHom :=
    sup_le (fun i hi => le_sup_left (a := I) (b := Z) (hI i hi))
      (fun z hz => le_sup_right (a := I) (b := Z) (hZ z hz))
  intro s hs
  simpa [MulAut.conj_apply] using hle hs

theorem comm_mul_eq {B₁ : Subgroup G} {x g h : G} (hgB₁ : ∀ b ∈ B₁, g * b = b * g)
    (ht : h * x * h⁻¹ * x⁻¹ ∈ B₁)
    (hcomm : (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) =
      (h * x * h⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹)) :
    g * h * x * (g * h)⁻¹ * x⁻¹ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) := by
  calc g * h * x * (g * h)⁻¹ * x⁻¹ = (g * (h * x * h⁻¹ * x⁻¹)) * x * g⁻¹ * x⁻¹ := by group
    _ = ((h * x * h⁻¹ * x⁻¹) * g) * x * g⁻¹ * x⁻¹ := by rw [hgB₁ _ ht]
    _ = (h * x * h⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    _ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) := hcomm.symm

end General

section Socle

variable {G : Type} [Group G] [Finite G]

theorem le_of_ggTableBModule {p : ℕ} [Fact p.Prime] {Bs L B₂ S : Subgroup G} {x : G}
    (hBs : IsPGroup p Bs) (hM : GGTableBModule p Bs x L B₂) (hxS : Subgroup.zpowers x ≤ S)
    (hSV : S ≤ Bs)
    (hSinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S)
    (hSne : S ≠ Subgroup.zpowers x) : B₂ ≤ S := by
  obtain ⟨hxB₂, hB₂V, hcard, hB₂inv, hirr, hind⟩ := hM
  have hZB₂ : Subgroup.zpowers x ≤ B₂ := Subgroup.zpowers_le.mpr hxB₂
  rcases hirr (S ⊓ B₂) (le_inf hxS hZB₂) inf_le_right
      (fun n hn s hs => ⟨hSinv n hn s hs.1, hB₂inv n hn s hs.2⟩) with h | h
  · by_cases hB₂S : B₂ ≤ S
    · exact hB₂S
    exfalso
    by_cases hSB₂ : S ≤ B₂
    · exact hSne (by rw [← inf_eq_left.mpr hSB₂]; exact h)
    · have hlt : B₂ < S ⊔ B₂ :=
        lt_of_le_of_ne le_sup_right (fun heq => hSB₂ (by rw [heq]; exact le_sup_left))
      have hSB : S ⊔ B₂ = Bs := eq_of_lt_of_card_le_mul hBs hlt (sup_le hSV hB₂V) hcard
      rcases hind S B₂ hxS hZB₂ hSinv hB₂inv h hSB with h' | h'
      · exact hSne h'
      · exact hB₂S (h' ▸ hxS)
  · rw [← h]
    exact inf_le_left

end Socle

section L44ii

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup h

theorem ggL44ii_of_ggL43 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G}
    (hFC : GGFieldCase p B Bs x L D J X) (hM : GGTableBModule p Bs x L B₂) (h43 : GGL43 Bs x X)
    (h44 : GGL44i p Bs x X) : GGL44ii Bs x X B₂ := by
  obtain ⟨hcfg, -, hXN, -, hXn, -, hXC⟩ := hFC
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hxB₁ : x ∉ B₁ := h43.1
  have hgB₁ : ∀ g ∈ X, ∀ b ∈ B₁, g * b = b * g := fun g hg b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 g hg
  have hθB₁ : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ B₁ := fun g hg => h44.2.1 g hg x hxBs
  let θ : X →* G := MonoidHom.mk' (fun g => (g : G) * x * (g : G)⁻¹ * x⁻¹) (fun g h => by
    simp only [Subgroup.coe_mul]
    exact comm_mul_eq (hgB₁ g g.2) (hθB₁ h h.2)
      (mul_comm_of_isElemAbelian hBs (hθB₁ g g.2).1 (hθB₁ h h.2).1))
  set I : Subgroup G := θ.range with hIdef
  have hmemI : ∀ b, b ∈ I ↔ ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b := by
    intro b
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hIB₁ : I ≤ B₁ := by
    rintro _ ⟨g, rfl⟩
    exact hθB₁ g g.2
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x * n⁻¹ = x := by
    intro n hn
    have h1 := Subgroup.mem_centralizer_iff.mp (hLx hn.1) x rfl
    rw [← h1, mul_inv_cancel_right]
  have hIinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ i ∈ I, n * i * n⁻¹ ∈ I := by
    intro n hn i hi
    obtain ⟨g, hg, rfl⟩ := (hmemI i).mp hi
    refine (hmemI _).mpr ⟨n * g * n⁻¹, hconj n hn.2 g hg, ?_⟩
    calc n * g * n⁻¹ * x * (n * g * n⁻¹)⁻¹ * x⁻¹
        = n * g * n⁻¹ * (n * x * n⁻¹) * (n * g * n⁻¹)⁻¹ * (n * x * n⁻¹)⁻¹ := by
          rw [hnx n hn]
      _ = n * (g * x * g⁻¹ * x⁻¹) * n⁻¹ := by group
  have hZinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ z ∈ Subgroup.zpowers x,
      n * z * n⁻¹ ∈ Subgroup.zpowers x := by
    intro n hn z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hnx n hn]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hSinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ I ⊔ Subgroup.zpowers x,
      n * s * n⁻¹ ∈ I ⊔ Subgroup.zpowers x := fun n hn =>
    conj_mem_sup_of_conj_mem (hIinv n hn) (hZinv n hn)
  have hSV : I ⊔ Subgroup.zpowers x ≤ Bs :=
    sup_le (hIB₁.trans inf_le_left) (Subgroup.zpowers_le.mpr hxBs)
  have hB₁Z : ∀ b ∈ B₁, b ∈ Subgroup.zpowers x → b = 1 := by
    intro b hb hbZ
    by_contra hb1
    have hz := zpowers_eq_of_mem_of_ne_one (hBs.2 x hxBs) hbZ hb1
    have h' : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hb
    rw [hz] at h'
    exact hxB₁ (Subgroup.zpowers_le.mp h')
  have hSne : I ⊔ Subgroup.zpowers x ≠ Subgroup.zpowers x := by
    intro hSZ
    obtain ⟨g, hg, hgC⟩ := Set.not_subset.mp hXC
    have hθ1 : g * x * g⁻¹ * x⁻¹ ≠ 1 := by
      intro h1
      apply hgC
      refine h44.1 g hg ?_
      calc g * x = g * x * g⁻¹ * x⁻¹ * x * g := by group
        _ = x * g := by rw [h1, one_mul]
    apply hθ1
    refine hB₁Z _ (hθB₁ g hg) ?_
    rw [← hSZ]
    exact le_sup_left (a := I) ((hmemI _).mpr ⟨g, hg, rfl⟩)
  have hBsp := isPGroup_of_isElemAbelian hBs
  have hB₂S : B₂ ≤ I ⊔ Subgroup.zpowers x :=
    le_of_ggTableBModule hBsp hM le_sup_right hSV hSinv hSne
  have hded : ∀ b ∈ B₁, b ∈ I ⊔ Subgroup.zpowers x → b ∈ I := by
    intro b hb hbS
    have hxI : ∀ i ∈ I, x * i = i * x := fun i hi =>
      mul_comm_of_isElemAbelian hBs hxBs (hIB₁ hi).1
    obtain ⟨i, hi, j, rfl⟩ := exists_mem_mul_pow_of_mem_sup hxI hbS
    have hxj : x ^ j ∈ B₁ := by
      have := B₁.mul_mem (B₁.inv_mem (hIB₁ hi)) hb
      simpa using this
    rw [hB₁Z _ hxj (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j), mul_one]
    exact hi
  by_cases hSBs : I ⊔ Subgroup.zpowers x = Bs
  · left
    intro b
    constructor
    · intro hb
      exact (hmemI b).mp (hded b hb (by rw [hSBs]; exact hb.1))
    · rintro ⟨g, hg, rfl⟩
      exact hθB₁ g hg
  · right
    have hB₂ne : B₂ ≠ Bs := fun h => hSBs (le_antisymm hSV (h ▸ hB₂S))
    have hSB₂ : I ⊔ Subgroup.zpowers x = B₂ := by
      by_contra hne
      exact hSBs (eq_of_lt_of_card_le_mul hBsp (lt_of_le_of_ne hB₂S (Ne.symm hne)) hSV
        hM.2.2.1)
    refine ⟨lt_of_le_of_ne hM.2.1 hB₂ne, fun b => ⟨fun hb => ?_, ?_⟩⟩
    · exact (hmemI b).mp (hded b hb.1 (by rw [hSB₂]; exact hb.2))
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hθB₁ g hg, ?_⟩
      rw [← hSB₂]
      exact le_sup_left (a := I) ((hmemI _).mpr ⟨g, hg, rfl⟩)

end L44ii

end CFSG.StandardType

end
