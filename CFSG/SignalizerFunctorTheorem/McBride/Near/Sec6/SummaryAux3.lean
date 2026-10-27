module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux2
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S34

section Uniform

variable {p : ℕ} {X Y : Type*} [Group X] [Group Y]

def GoodPrime (r : ℕ) (φ : MulAut X) : Prop :=
  r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer φ) ∧
    ∀ Z : Subgroup X, fixedCore1 φ ≤ Z → (∃ y ∈ Z, orderOf y = r) → Z = ⊤

theorem GoodPrime.congr (e : X ≃* Y) {r : ℕ} {φ : MulAut X} (h : GoodPrime r φ) :
    GoodPrime r (MulAut.congr e φ) := by
  obtain ⟨hr, hrX, hrM, hall⟩ := h
  refine ⟨hr, ?_, ?_, fun Z hZ ⟨y, hyZ, hyr⟩ => ?_⟩
  · rwa [← Nat.card_congr e.toEquiv]
  · rwa [fixedNormalizer_congr, Subgroup.card_map_of_injective e.injective]
  · have hZ' : fixedCore1 φ ≤ Z.comap e.toMonoidHom := by
      rw [← Subgroup.map_le_iff_le_comap, ← fixedCore1_congr]
      exact hZ
    have h1 := hall _ hZ' ⟨e.symm y, by simpa using hyZ, by rw [MulEquiv.orderOf_eq]; exact hyr⟩
    refine eq_top_iff.mpr fun z _ => ?_
    have : e.symm z ∈ Z.comap e.toMonoidHom := h1 ▸ Subgroup.mem_top _
    simpa using this

theorem GoodPrime.of_fixed_eq {φ ψ : MulAut X}
    (hC : signalizerFixedSubgroup φ = signalizerFixedSubgroup ψ) {r : ℕ} (h : GoodPrime r φ) :
    GoodPrime r ψ := by
  unfold GoodPrime at h ⊢
  rwa [← fixedNormalizer_eq_of_fixed_eq hC, ← fixedCore1_eq_of_fixed_eq hC]

omit [Group Y] in
theorem signalizerFixedSubgroup_le_of_mem_zpowers {φ ψ : MulAut X}
    (h : ψ ∈ Subgroup.zpowers φ) : signalizerFixedSubgroup φ ≤ signalizerFixedSubgroup ψ := by
  intro x hx
  have h1 : φ ∈ MulAction.stabilizer (MulAut X) x := hx
  exact (Subgroup.zpowers_le.mpr h1) h

end Uniform

section Conj

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

theorem exists_sylow_eq_zpowers
    (h : NearSimple p X) {φ : MulAut X} (hφ : orderOf φ = p) :
    ∃ S : Sylow p (MulAut X), (S : Subgroup (MulAut X)) = Subgroup.zpowers φ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card (Subgroup.zpowers φ) = p := by rw [Nat.card_zpowers, hφ]
  have hP : IsPGroup p (Subgroup.zpowers φ) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hSdvd := near_aut_pSubgroup_card_dvd h S S.isPGroup'
  have hle : Nat.card (S : Subgroup (MulAut X)) ≤ Nat.card (Subgroup.zpowers φ) := by
    rw [hcard]
    exact Nat.le_of_dvd h.prime.pos hSdvd
  exact ⟨S, (Subgroup.eq_of_le_of_card_ge hS hle).symm⟩

theorem exists_fixed_eq_congr
    (h : NearSimple p X) {φ ψ : MulAut X} (hφ : orderOf φ = p)
    (hψ : orderOf ψ = p) :
    ∃ α : MulAut X, signalizerFixedSubgroup ψ = signalizerFixedSubgroup (MulAut.congr α φ) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨Sφ, hSφ⟩ := exists_sylow_eq_zpowers h hφ
  obtain ⟨Sψ, hSψ⟩ := exists_sylow_eq_zpowers h hψ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut X) Sφ Sψ
  have hconj : Subgroup.zpowers ψ = (Subgroup.zpowers φ).map (MulAut.conj g).toMonoidHom := by
    rw [← hSψ, ← hSφ, ← hg]
    rfl
  have hcg : (MulAut.conj g).toMonoidHom φ = MulAut.congr g φ := rfl
  rw [MonoidHom.map_zpowers, hcg] at hconj
  refine ⟨g, le_antisymm ?_ ?_⟩
  · exact signalizerFixedSubgroup_le_of_mem_zpowers (hconj ▸ Subgroup.mem_zpowers _)
  · exact signalizerFixedSubgroup_le_of_mem_zpowers (hconj ▸ Subgroup.mem_zpowers _)

theorem GoodPrime.of_orderOf_eq
    (h : NearSimple p X) {φ ψ : MulAut X} (hφ : orderOf φ = p)
    (hψ : orderOf ψ = p) {r : ℕ} (hg : GoodPrime r φ) : GoodPrime r ψ := by
  obtain ⟨α, hα⟩ := exists_fixed_eq_congr h hφ hψ
  exact (hg.congr (α : X ≃* X)).of_fixed_eq hα.symm

omit [Finite X] in
theorem GoodPrime.ne
    (h : NearSimple p X) {φ : MulAut X} (hφ : orderOf φ = p) {r : ℕ}
    (hg : GoodPrime r φ) : r ≠ p ∧ r ≠ 2 ∧ r ≠ 3 := by
  obtain ⟨hr, hrX, hrM, -⟩ := hg
  have hCM : Nat.card (signalizerFixedSubgroup φ) ∣ Nat.card (fixedNormalizer φ) :=
    Subgroup.card_dvd_of_le (fixed_le_fixedNormalizer φ)
  have key : ∀ k : ℕ, k ∣ Nat.card (signalizerFixedSubgroup φ) → r ∣ k → False :=
    fun k hk hrk => hrM (hrk.trans (hk.trans hCM))
  refine ⟨fun hrp => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · subst hrp
    exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h.coprime hrX)
  · subst h2
    rcases Sec6S31.card_fixed_cases h hφ with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨n, -, -, hc⟩ | ⟨-, hc⟩ <;>
      exact key 2 (by rw [hc]; norm_num) dvd_rfl
  · subst h3
    rcases Sec6S31.card_fixed_cases h hφ with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨n, -, ⟨e⟩, hc⟩ | ⟨-, hc⟩
    · exact key 3 (by rw [hc]; norm_num) dvd_rfl
    · exact key 3 (by rw [hc]; norm_num) dvd_rfl
    · refine NearSolvable.not_three_dvd_suzuki
        (NearSolvable.two_pow_mod_three (odd_two_mul_add_one n)) ?_
      rw [← NearSolvable.card_sz n, ← Nat.card_congr e.toEquiv]
      exact hrX
    · exact key 3 (by rw [hc]; norm_num) dvd_rfl

theorem exists_goodPrime
    (h : NearSimple p X) {φ : MulAut X} (hφ : orderOf φ = p) :
    ∃ r : ℕ, GoodPrime r φ :=
  (NearSimple.exists_prime_overgroup_C₁ h hφ).imp fun _ hr => hr

end Conj

section Component

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem fixedCore1_map_subtype {J C : Subgroup G} {φ : MulAut ↥J}
    (hC : (signalizerFixedSubgroup φ).map J.subtype = C)
    (hC₀ : (fixedFitting φ).map J.subtype = CFSG.fittingSubgroupOf C) :
    (fixedCore1 φ).map J.subtype = C ⊓ sectionCentralizer (CFSG.fittingSubgroupOf C) C := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hcC : (c : G) ∈ C := hC ▸ ⟨c, hc.1, rfl⟩
    refine ⟨hcC, mem_sectionCentralizer_iff.mpr ⟨?_, Subgroup.le_normalizer hcC, ?_⟩⟩
    · exact Thm210.le_normalizer_fittingSubgroupOf C hcC
    · intro y hy
      obtain ⟨y', hy', rfl⟩ : y ∈ (signalizerFixedSubgroup φ).map J.subtype := hC ▸ hy
      have h3 : ((⁅c, y'⁆ : J) : G) ∈ (fixedFitting φ).map J.subtype :=
        ⟨⁅c, y'⁆, hc.2 y' hy', rfl⟩
      rw [hC₀] at h3
      exact h3
  · rintro ⟨hxC, hx⟩
    obtain ⟨c, hcC, rfl⟩ : x ∈ (signalizerFixedSubgroup φ).map J.subtype := hC ▸ hxC
    refine ⟨c, ⟨hcC, fun y' hy' => ?_⟩, rfl⟩
    have hy'C : ((y' : J) : G) ∈ C := hC ▸ ⟨y', hy', rfl⟩
    have h3 := (mem_sectionCentralizer_iff.mp hx).2.2 _ hy'C
    have h3' : ((⁅c, y'⁆ : J) : G) ∈ (fixedFitting φ).map J.subtype := by
      rw [hC₀]
      exact h3
    obtain ⟨z, hz, hzc⟩ := h3'
    exact (Subtype.ext hzc : z = ⁅c, y'⁆) ▸ hz

structure GoodComp (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E : Subgroup G) (r : ℕ)
    (L : Subgroup G) : Prop where
  dvd : r ∣ Nat.card L
  not_dvd : ¬ r ∣ Nat.card (kJ A L)
  abelian : ∀ P : Subgroup G, P ≤ L → IsPGroup r P → Nat.Coprime (P.relIndex L) r →
    IsMulCommutative P
  generate : ∀ Y : Subgroup G, Y ≤ L → L ⊓ sThree p A θ ⊓ thetaOf θ E ≤ Y →
    (∃ y ∈ Y, orderOf y = r) → Y = L

variable {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.goodComp
    (d : Data h E f) {L : Subgroup G} (hL : L ∈ lcal (θ f)) {r : ℕ}
    {φ : MulAut ↥L} (hφ : orderOf φ = p)
    (hC : (signalizerFixedSubgroup φ).map L.subtype = cenIn L (norIn A L))
    (hC₀ : (fixedFitting φ).map L.subtype = CFSG.fittingSubgroupOf (cenIn L (norIn A L)))
    (hM : (fixedNormalizer φ).map L.subtype = kJ A L) (hg : GoodPrime r φ) :
    GoodComp p A θ E r L := by
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  have hNS : NearSimple p ↥L := d.semisimpleAction.nearSimple hL'
  obtain ⟨hr, hrX, hrM, hall⟩ := hg
  have : Fact r.Prime := ⟨hr⟩
  refine ⟨hrX, ?_, fun P hPL hP hidx => ?_, fun Y hYL hTY ⟨y, hyY, hyr⟩ => ?_⟩
  · rw [← hM, Subgroup.card_map_of_injective L.subtype_injective]
    exact hrM
  · have hP' : IsPGroup r (P.subgroupOf L) := hP.comap_subtype
    have hnd : ¬ r ∣ (P.subgroupOf L).index :=
      (Nat.Prime.coprime_iff_not_dvd hr).mp hidx.symm
    let R : Sylow r ↥L := hP'.toSylow hnd
    have hab : IsMulCommutative (R : Subgroup ↥L) :=
      near_sylow_abelian hNS hφ hr hrX hrM R
    have hab' : IsMulCommutative (P.subgroupOf L) := hab
    exact (isMulCommutative_congr (Subgroup.subgroupOfEquivOfLe hPL)).mp hab'
  · have hY' : fixedCore1 φ ≤ Y.subgroupOf L := by
      intro c hc
      have hcT : (c : G) ∈ (fixedCore1 φ).map L.subtype := ⟨c, hc, rfl⟩
      rw [fixedCore1_map_subtype hC hC₀, ← d.inf_sThree_eq hL] at hcT
      exact hTY hcT
    have hyL : y ∈ L := hYL hyY
    have := hall _ hY' ⟨⟨y, hyL⟩, hyY, by rw [Subgroup.orderOf_mk]; exact hyr⟩
    refine le_antisymm hYL fun x hx => ?_
    have hx' : (⟨x, hx⟩ : ↥L) ∈ Y.subgroupOf L := this ▸ Subgroup.mem_top _
    exact hx'

theorem exists_good_prime
    (h : Counterexample p A θ) {E : Subgroup G} (hE : DistE p A θ E) :
    ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ r ≠ 2 ∧ r ≠ 3 ∧
      ∀ f : G, Data h E f → ∀ L ∈ lcal (θ f), GoodComp p A θ E r L := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨f₀, hf₀A, hf₀E⟩ := exists_mem_not_mem h hE
  have d₀ : Data h E f₀ := ⟨hE, hf₀A, hf₀E⟩
  obtain ⟨J₀, hJ₀⟩ := d₀.lcal_nonempty
  have hJ₀' : J₀ ∈ lcal (kOf (θ f₀)) := d₀.lcal_kOf ▸ hJ₀
  obtain ⟨φ₀, hφ₀, -⟩ := d₀.semisimpleAction.exists_frame_data hJ₀'
  have hNS₀ : NearSimple p ↥J₀ := d₀.semisimpleAction.nearSimple hJ₀'
  obtain ⟨r, hr⟩ := exists_goodPrime hNS₀ hφ₀
  obtain ⟨hrp, hr2, hr3⟩ := hr.ne hNS₀ hφ₀
  refine ⟨r, hr.1, hrp, hr2, hr3, fun f d L hL => ?_⟩
  have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
  obtain ⟨φ, hφ, hC, hC₀, hM, -⟩ := d.semisimpleAction.exists_frame_data hL'
  have hNS : NearSimple p ↥L := d.semisimpleAction.nearSimple hL'
  have hthe := hθ.isFunctor.thetaOf_zpowers d.mem d.ne_one
  have hthe₀ := hθ.isFunctor.thetaOf_zpowers d₀.mem d₀.ne_one
  obtain ⟨ψ⟩ : Nonempty (↥J₀ ≃* ↥L) :=
    h.lemma610 d₀.zpowers_mem_rSet d.zpowers_mem_rSet (by rw [hthe₀]; exact hJ₀)
      (by rw [hthe]; exact hL)
  have hg1 : GoodPrime r (MulAut.congr ψ φ₀) := hr.congr ψ
  have hg2 : GoodPrime r φ :=
    hg1.of_orderOf_eq hNS (by rw [orderOf_congr, hφ₀]) hφ
  exact d.goodComp hL hφ hC hC₀ hM hg2

end Component

end Sec6S34

end CFSG.SignalizerFunctorTheorem.McBride.Near
