module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin.H.L3Cover

open CFSG.Open
open scoped commutatorElement Pointwise

theorem commutatorElement_center_mul {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (u b : Q) : ⁅z * u, b⁆ = ⁅u, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc z * u * b * (z * u)⁻¹ * b⁻¹ = z * (u * b * u⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = u * b * u⁻¹ * z * z⁻¹ * b⁻¹ := by rw [← hz' (u * b * u⁻¹)]
    _ = u * b * u⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_center {Q : Type*} [Group Q] {z : Q} (hz : z ∈ Subgroup.center Q)
    (u b : Q) : ⁅u, z * b⁆ = ⁅u, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_center_mul hz, commutatorElement_inv]

theorem pow_mem_of_mem_ker {X Y : Type*} [Group X] [Group Y] (N : Subgroup X) [N.Normal]
    (hX : CFSG.IsQuasisimple (X ⧸ N)) {F : Type} [Field F] [Finite F] (hF : 5 ≤ Nat.card F)
    (φ : X →* Y) (hN : N ≤ φ.ker) (ρ : Matrix.SpecialLinearGroup (Fin 3) F →* Y)
    (hrange : φ.range = ρ.range) (hne : ρ.range ≠ ⊥) {e : ℕ}
    (he : ∀ g ∈ ρ.ker, g ^ e = 1) : ∀ x ∈ φ.ker, x ^ e ∈ N := by
  intro x hx
  set φ₁ : X ⧸ N →* Y := QuotientGroup.lift N φ hN with hφ₁
  have hφ₁mk : ∀ a : X, φ₁ (a : X ⧸ N) = φ a := fun a => QuotientGroup.lift_mk N hN a
  have hmem : ∀ g, ∃ a : X ⧸ N, φ₁ a = ρ g := by
    intro g
    have : ρ g ∈ φ.range := hrange ▸ ⟨g, rfl⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [hφ₁mk, ha]⟩
  have hmem' : ∀ a : X ⧸ N, ∃ g, φ₁ a = ρ g := by
    intro a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    have : φ a ∈ ρ.range := hrange ▸ ⟨a, rfl⟩
    obtain ⟨g, hg⟩ := this
    exact ⟨g, by rw [hφ₁mk, hg]⟩
  have hnt : ∃ a : X ⧸ N, φ₁ a ≠ 1 := by
    obtain ⟨⟨y, ⟨g, rfl⟩⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    obtain ⟨a, ha⟩ := hmem g
    exact ⟨a, by rw [ha]; exact fun h => hy1 (Subtype.ext h)⟩
  have hker₁ : φ₁.ker ≤ Subgroup.center (X ⧸ N) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hX hnt
  let E : Subgroup ((X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F) :=
    (φ₁.comp (MonoidHom.fst _ _)).eqLocus (ρ.comp (MonoidHom.snd _ _))
  let π : E →* Matrix.SpecialLinearGroup (Fin 3) F := (MonoidHom.snd _ _).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨a, ha⟩ := hmem g
    exact ⟨⟨(a, g), ha⟩, rfl⟩
  have hcen : π.ker ≤ Subgroup.center E := by
    intro w hw
    have hw1 : (w : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 = 1 := hw
    have hw2 : (w : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).1 ∈ φ₁.ker := by
      have h : φ₁ (w : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).1 =
          ρ (w : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 := w.2
      rw [MonoidHom.mem_ker, h, hw1, map_one]
    rw [Subgroup.mem_center_iff]
    intro w'
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.mp (hker₁ hw2) _
    · show (w' : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 *
          (w : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 =
        (w : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 *
          (w' : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2
      rw [hw1, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (m := 2) le_rfl hF hπ hcen
  let ψ : Matrix.SpecialLinearGroup (Fin 3) F →* X ⧸ N :=
    (MonoidHom.fst _ _).comp (E.subtype.comp σ)
  have hψ : ∀ g, φ₁ (ψ g) = ρ g := by
    intro g
    have h1 : φ₁ ((σ g : E) : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).1 =
        ρ ((σ g : E) : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 := (σ g).2
    have h2 : ((σ g : E) : (X ⧸ N) × Matrix.SpecialLinearGroup (Fin 3) F).2 = g := hσ g
    rw [h2] at h1
    exact h1
  have hdec : ∀ a : X ⧸ N, ∃ g, a * (ψ g)⁻¹ ∈ Subgroup.center (X ⧸ N) := by
    intro a
    obtain ⟨g, hg⟩ := hmem' a
    refine ⟨g, hker₁ ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, hg, mul_inv_cancel]
  have hsurj : Function.Surjective ψ := by
    have hcomm : commutator (X ⧸ N) ≤ ψ.range := by
      rw [commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨a, b, rfl⟩
      obtain ⟨g, hg⟩ := hdec a
      obtain ⟨g', hg'⟩ := hdec b
      have ea : a = a * (ψ g)⁻¹ * ψ g := by group
      have eb : b = b * (ψ g')⁻¹ * ψ g' := by group
      have : ⁅a, b⁆ = ⁅ψ g, ψ g'⁆ := by
        rw [ea, eb, commutatorElement_center_mul hg, commutatorElement_mul_center hg']
      rw [this]
      exact ⟨⁅g, g'⁆, map_commutatorElement ψ g g'⟩
    intro a
    have ha : a ∈ commutator (X ⧸ N) := by
      rw [hX.1.commutator_eq_top]
      exact Subgroup.mem_top a
    obtain ⟨g, hg⟩ := hcomm ha
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hsurj (x : X ⧸ N)
  have hg1 : g ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, ← hψ, hg, hφ₁mk]
    exact hx
  have h3 : (x : X ⧸ N) ^ e = 1 := by rw [← hg, ← map_pow, he g hg1, map_one]
  rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3

section Automizer

variable {G : Type*} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem pRank_autI_le_of_not_dvd [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hp : ¬ p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G))) :
    CFSG.Open.pRank p (autI hV M) ≤ CFSG.Open.pRank p M := by
  set φ := convHom hV M hMN with hφ
  have hker : ¬ p ∣ Nat.card φ.ker := by
    rw [hφ, ker_convHom]
    have e : Nat.card ((M ⊓ Subgroup.centralizer (V : Set G)).subgroupOf M) =
        Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rwa [e]
  have e1 : CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ φ.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_quotient_eq φ.ker hker
  have e2 : (↥M ⧸ φ.ker) ≃* ↥(autI hV M) :=
    (QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr (range_convHom hV M hMN))
  have e3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e2
  rw [← pRank_top_subtype (autI hV M), ← e3, e1, pRank_top_subtype]

theorem sup_inf_centralizer_le {L : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G))
    {y : G} (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) {p : ℕ} (hp : p.Prime) (hyp : y ^ p = 1)
    (hy : convI hV ⟨y, hyN⟩ ∉ autI hV L) :
    (L ⊔ Subgroup.zpowers y) ⊓ Subgroup.centralizer (V : Set G) ≤ L := by
  rintro m ⟨hm, hmC⟩
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left L (Subgroup.zpowers y)
    (Subgroup.zpowers_le.mpr hyL)
  have hm' : m ∈ (L : Set G) * (Subgroup.zpowers y : Set G) := hset ▸ hm
  obtain ⟨l, hl, z, hz, rfl⟩ := hm'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  set yb := convI hV ⟨y, hyN⟩ with hyb
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := hLN hl
  have hyk : yb ^ k ∈ autI hV L := by
    have hmN : l * y ^ k ∈ Subgroup.normalizer (V : Set G) :=
      mul_mem hlN (zpow_mem hyN k)
    have h1 : convI hV ⟨l * y ^ k, hmN⟩ = 1 := (convI_eq_one_iff hV _).mpr hmC
    have h2 : (⟨l * y ^ k, hmN⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨l, hlN⟩ * ⟨y, hyN⟩ ^ k := Subtype.ext (by simp)
    rw [h2, map_mul, map_zpow] at h1
    have h3 : yb ^ k = (convI hV ⟨l, hlN⟩)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h3]
    exact inv_mem (convI_mem_autI hV hl hlN)
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hpk
    have h1 : y ^ ((p : ℤ) * j) = 1 := by rw [zpow_mul, zpow_natCast, hyp, one_zpow]
    show l * y ^ ((p : ℤ) * j) ∈ L
    rw [h1, mul_one]
    exact hl
  · exfalso
    apply hy
    have hybp : yb ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, hyb, ← map_pow]
      have : (⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) ^ p = 1 := Subtype.ext (by simp [hyp])
      rw [this, map_one]
    have hg : Int.gcd k p = 1 := by
      have h1 : Int.gcd k p ∣ p := by
        have := Int.gcd_dvd_right (a := k) (b := (p : ℤ))
        exact_mod_cast this
      rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
      · exact h
      · exfalso
        apply hpk
        have := Int.gcd_dvd_left (a := k) (b := (p : ℤ))
        rw [h] at this
        exact this
    have hb := Int.gcd_eq_gcd_ab k p
    rw [hg, Nat.cast_one] at hb
    have e : yb = (yb ^ k) ^ (Int.gcdA k p) * (yb ^ (p : ℤ)) ^ (Int.gcdB k p) := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← hb, zpow_one]
    rw [e, hybp, one_zpow, mul_one]
    exact zpow_mem hyk _

end Automizer

end CFSG.Quasithin.H.L3Cover
