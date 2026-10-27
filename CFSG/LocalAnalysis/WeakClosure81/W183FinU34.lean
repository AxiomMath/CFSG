module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Rank
import CFSG.LocalAnalysis.WeakClosure81.W183L313Borel
import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
import CFSG.GH74.KGroups.CoverEven
import CFSG.CGT.T75E.RootBender
import CFSG.Quasithin.EmptyFaithful.R3c12Syl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)
open CFSG.GH74.Uniqueness.Bender (BenderType autFixed)

private theorem w183fin_benderType_of_isU3_two {X : Type} [Group X] (h : IsU3 X 2) :
    BenderType X 2 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (le_refl 2) h
  exact BenderType.unitary 2 (le_refl 2)
    (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 2)))

theorem finRkU34_holds : FinRkU34 := by
  intro L _ _ hL A hA
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (le_refl 2) hL
  let e' : L ≃* ↥(CFSG.Theory.Comparator.PSU3Model 2) :=
    e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 2))
  have hsq : ∀ a ∈ A.map e'.toMonoidHom, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x * x = 1 := by simpa [pow_two] using hA.2 x hx
    rw [← map_mul, hx2, map_one]
  calc Nat.card A = Nat.card (A.map e'.toMonoidHom) :=
        (Subgroup.card_map_of_injective e'.injective).symm
    _ ≤ 2 ^ 2 := CFSG.CGT.T75E.card_le_two_pow_of_sq_eq_one (le_refl 2) _ hsq
    _ = 4 := by norm_num

private theorem w183fin_u34_false_of_outer {Y : Type} [Group Y] {L : Subgroup Y} [L.Normal]
    (hU : IsU3 ↥L 2) (hC : Subgroup.centralizer (L : Set Y) = ⊥) {A : Subgroup Y}
    (hcard : Nat.card A = 4) (hel : IsElemAbelian 2 A) {a : Y} (haA : a ∈ A) (haL : a ∉ L)
    (hcen : ∀ g ∈ L, g * a = a * g → ∀ x ∈ A, g * x = x * g) : False := by
  classical
  have hB := w183fin_benderType_of_isU3_two hU
  have ha1 : a ≠ 1 := fun h => haL (h ▸ L.one_mem)
  have haa : a * a = 1 := by simpa [pow_two] using hel.2 a haA
  obtain ⟨b, hbA, hb1, hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    obtain ⟨u, huA, hu1, hua, -⟩ := CFSG.Quasithin.R3c12.klein_elems hcard
      (fun v hv => by simpa [pow_two] using hel.2 v hv) haA ha1
    exact ⟨u, huA, hu1, hua⟩
  let α : MulAut ↥L := MulAut.conjNormal a
  let β : MulAut ↥L := MulAut.conjNormal b
  have hα : α * α = 1 := by
    rw [← map_mul, haa, map_one]
  have hout : ¬ ∃ g : ↥L, ∀ x : ↥L, α x = g * x * g⁻¹ := by
    rintro ⟨⟨gy, hgy⟩, hg⟩
    apply haL
    have hz : gy⁻¹ * a ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val (hg ⟨l, hl⟩)
      simp only [α, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have h2 : gy⁻¹ * a * l * a⁻¹ * gy = l := by
        calc gy⁻¹ * a * l * a⁻¹ * gy = gy⁻¹ * (a * l * a⁻¹) * gy := by group
          _ = gy⁻¹ * (gy * l * gy⁻¹) * gy := by rw [h1]
          _ = l := by group
      calc l * (gy⁻¹ * a) = (gy⁻¹ * a * l * a⁻¹ * gy) * (gy⁻¹ * a) := by rw [h2]
        _ = gy⁻¹ * a * l := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hz
    rw [← hz]
    exact hgy
  have hβα : β * α = α * β := by
    rw [← map_mul, ← map_mul, hel.comm hbA haA]
  have hβ : ∀ x ∈ autFixed α, β x = x := by
    intro x hx
    rw [CFSG.GH74.Uniqueness.Bender.mem_autFixed_iff] at hx
    have hx' := congrArg Subtype.val hx
    simp only [α, MulAut.conjNormal_apply] at hx'
    have hxa : (x : Y) * a = a * x := by
      calc (x : Y) * a = (a * x * a⁻¹) * a := by rw [hx']
        _ = a * x := by group
    have hxb := hcen x x.2 hxa b hbA
    apply Subtype.ext
    simp only [β, MulAut.conjNormal_apply]
    calc b * (x : Y) * b⁻¹ = (x * b) * b⁻¹ := by rw [← hxb]
      _ = x := by group
  rcases hB.centralizer_unitary α hα hout β hβα hβ with h | h
  · apply hb1
    have hz : b ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val (congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) h)
      simp only [β, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc l * b = (b * l * b⁻¹) * b := by rw [h1]
        _ = b * l := by group
    rw [hC, Subgroup.mem_bot] at hz
    exact hz
  · apply hba
    have hz : a⁻¹ * b ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val (congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) h)
      simp only [α, β, MulAut.conjNormal_apply] at h1
      have h2 : a⁻¹ * b * l * b⁻¹ * a = l := by
        calc a⁻¹ * b * l * b⁻¹ * a = a⁻¹ * (b * l * b⁻¹) * a := by group
          _ = a⁻¹ * (a * l * a⁻¹) * a := by rw [h1]
          _ = l := by group
      calc l * (a⁻¹ * b) = (a⁻¹ * b * l * b⁻¹ * a) * (a⁻¹ * b) := by rw [h2]
        _ = a⁻¹ * b * l := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm

private theorem w183fin_hcen_of_isTISub {Y : Type} [Group Y] {L : Subgroup Y} [hLn : L.Normal]
    {A : Subgroup Y} (hcard : Nat.card A = 4) (hel : IsElemAbelian 2 A) (hTI : IsTISub Y A)
    {a : Y} (haA : a ∈ A) (haL : a ∉ L) :
    ∀ g ∈ L, g * a = a * g → ∀ x ∈ A, g * x = x * g := by
  intro g hgL hga
  have ha1 : a ≠ 1 := fun h => haL (h ▸ L.one_mem)
  have hgN : g ∈ Subgroup.normalizer (A : Set Y) := hTI a haA ha1 g hga.symm.symm
  obtain ⟨u, huA, hu1, hua, hall⟩ := CFSG.Quasithin.R3c12.klein_elems hcard
      (fun v hv => by simpa [pow_two] using hel.2 v hv) haA ha1
  have hgu : g * u = u * g := by
    have hmem : g * u * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgN u).mp huA
    rcases hall _ hmem with h | h | h | h
    · exfalso; apply hu1
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exfalso; apply hua
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * a * g := by rw [h]
        _ = g⁻¹ * (g * a) * g⁻¹ * g := by rw [hga]; group
        _ = a := by group
    · calc g * u = (g * u * g⁻¹) * g := by group
        _ = u * g := by rw [h]
    · exfalso; apply haL
      have h2 : a = g * (u * g⁻¹ * u⁻¹) := by
        calc a = (a * u) * u⁻¹ := by group
          _ = (g * u * g⁻¹) * u⁻¹ := by rw [h]
          _ = g * (u * g⁻¹ * u⁻¹) := by group
      rw [h2]
      exact L.mul_mem hgL (hLn.conj_mem g⁻¹ (L.inv_mem hgL) u)
  intro x hx
  rcases hall x hx with rfl | rfl | rfl | rfl
  · simp
  · exact hga
  · exact hgu
  · calc g * (a * u) = (g * a) * u := by group
      _ = (a * g) * u := by rw [hga]
      _ = a * (g * u) := by group
      _ = a * (u * g) := by rw [hgu]
      _ = (a * u) * g := by group

theorem finU34_holds : FinU34 := by
  intro Y _ _ L hLn hU hC A hcard hel hTI
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hLn
  have hAL : A ≤ L := by
    by_contra hAL
    rw [SetLike.not_le_iff_exists] at hAL
    obtain ⟨a, haA, haL⟩ := hAL
    exact w183fin_u34_false_of_outer hU hC hcard hel haA haL
      (w183fin_hcen_of_isTISub hcard hel hTI haA haL)
  obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 hAL hel.isPGroup
  obtain ⟨D, hD⟩ := w183l313_borel_exists hU hS
  have hle : A ≤ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter S :=
    fun x hx => hD.omega_le x (hAS hx) (by simpa [pow_two] using hel.2 x hx)
  have heq : A = CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hD.card_center, hcard])
  exact ⟨S, hS, by rw [heq, w183l313_center_map_eq]⟩

theorem finG3U34_holds
    (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (hLn : L.Normal) (hU : IsU3 ↥L 2)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (A : Subgroup Y) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    A ≤ L ∧ ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hLn
  have hAL : A ≤ L := by
    by_contra hAL
    rw [SetLike.not_le_iff_exists] at hAL
    obtain ⟨a, haA, haL⟩ := hAL
    have ha1 : a ≠ 1 := fun h => haL (h ▸ L.one_mem)
    exact w183fin_u34_false_of_outer hU hC hcard hel haA haL
      (fun g hg hga x hx => hTI1 a haA ha1 g hg hga x hx)
  refine ⟨hAL, ?_⟩
  obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 hAL hel.isPGroup
  obtain ⟨D, hD⟩ := w183l313_borel_exists hU hS
  have hle : A ≤ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter S :=
    fun x hx => hD.omega_le x (hAS hx) (by simpa [pow_two] using hel.2 x hx)
  have heq : A = CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hD.card_center, hcard])
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one A with h | h
    · rw [h, Subgroup.card_bot] at hcard; omega
    · exact h
  obtain ⟨u, huA, hu1, hua, hall⟩ := CFSG.Quasithin.R3c12.klein_elems hcard
      (fun v hv => by simpa [pow_two] using hel.2 v hv) haA ha1
  obtain ⟨d, hdD, hd⟩ := hD.trans_center a (heq ▸ haA) u (heq ▸ huA) ha1 hu1
  set n : Y := d⁻¹ with hn
  have hnD : n ∈ D := D.inv_mem hdD
  have hnL : n ∈ L := hD.le_Q hnD
  have hnN : n ∈ Subgroup.normalizer (A : Set Y) := by
    rw [heq]
    exact w183l313_normalizes_center (hD.le_normalizer hnD)
  have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun x hx => (Subgroup.mem_normalizer_iff.mp hnN x).mp hx
  have hna : n * a * n⁻¹ = u := by simpa [hn] using hd
  have hodd : Odd (orderOf n) :=
    Odd.of_dvd_nat hD.odd (Subgroup.orderOf_dvd_natCard D hnD)
  have huu : u * u = 1 := by simpa [pow_two] using hel.2 u huA
  have hcommAu : a * u = u * a := hel.comm haA huA
  have hnu_ne_u : n * u * n⁻¹ ≠ u := by
    intro h
    apply hua
    have : n * u * n⁻¹ = n * a * n⁻¹ := by rw [h, hna]
    have := mul_left_cancel (a := n) (mul_right_cancel this)
    exact this
  have hnu_ne_a : n * u * n⁻¹ ≠ a := by
    intro h
    have h1 : n * a = u * n := by
      calc n * a = (n * a * n⁻¹) * n := by group
        _ = u * n := by rw [hna]
    have h2 : n * u = a * n := by
      calc n * u = (n * u * n⁻¹) * n := by group
        _ = a * n := by rw [h]
    have hc : Commute a (n * n) := by
      show a * (n * n) = (n * n) * a
      calc a * (n * n) = (a * n) * n := by group
        _ = (n * u) * n := by rw [h2]
        _ = n * (u * n) := by group
        _ = n * (n * a) := by rw [h1]
        _ = (n * n) * a := by group
    obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.Bender.exists_sq_eq_of_odd_orderOf hodd
    have hcn : Commute a n := by
      have := hc.pow_right k
      rwa [(Commute.refl n).mul_pow, hk] at this
    apply hua
    calc u = n * a * n⁻¹ := hna.symm
      _ = a := by
        have h3 : a * n = n * a := hcn
        calc n * a * n⁻¹ = a * n * n⁻¹ := by rw [h3]
          _ = a := by group
  refine ⟨n, hnL, hnA, ?_⟩
  intro x hx hx1
  rcases hall x hx with rfl | rfl | rfl | rfl
  · exact absurd rfl hx1
  · rw [hna]; exact hua
  · exact hnu_ne_u
  · have hw : n * u * n⁻¹ ∈ A := hnA u huA
    have hw1 : n * u * n⁻¹ ≠ 1 := by
      intro h; apply hu1
      calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    have hwau : n * u * n⁻¹ = a * u := by
      rcases hall _ hw with h | h | h | h
      · exact absurd h hw1
      · exact absurd h hnu_ne_a
      · exact absurd h hnu_ne_u
      · exact h
    intro hfix
    have h4 : n * (a * u) * n⁻¹ = (n * a * n⁻¹) * (n * u * n⁻¹) := by group
    rw [h4, hna, hwau] at hfix
    have h2 : u * (a * u) = a := by
      calc u * (a * u) = (u * a) * u := by group
        _ = (a * u) * u := by rw [← hcommAu]
        _ = a * (u * u) := by group
        _ = a := by rw [huu, mul_one]
    apply hu1
    calc u = a⁻¹ * (a * u) := by group
      _ = a⁻¹ * a := by rw [← hfix, h2]
      _ = 1 := by group

end CFSG.LocalAnalysis.WeakClosure81

end
