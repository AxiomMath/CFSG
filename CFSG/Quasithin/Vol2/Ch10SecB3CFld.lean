module

public import CFSG.Quasithin.Vol2.Ch10SecB3C
public import CFSG.Quasithin.Vol2.Ch10SecB3FactsC
public import CFSG.Quasithin.Vol2.Ch10SecB3Ind

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem cV1_eq_bot (hCV : fsuCVM T L I = ⊥) : cV1 T L I = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  have h : (u : G) ∈ fsuCVM T L I := ⟨fsuUL_le' T L I u.2, hu⟩
  rw [hCV, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext h)

omit [Finite G] in
theorem module_of_cases (hCV : fsuCVM T L I = ⊥)
    (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I) :
    ∃ (_ : IsMulCommutative ↥(fsuUL T L I)) (a : ℕ),
      (2 ≤ a ∧ BinaryNaturalSL (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥ 2 a) ∨
        BinaryNaturalSz (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥ a ∨
        (2 ≤ a ∧ BinaryOrthogonalFour (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥ a) := by
  rcases hc with ⟨n, hn, -, hab, hnat⟩ | ⟨n, hn, -, hab, hnat⟩ | ⟨n, -, hab, hnat⟩
  · rw [cV1_eq_bot hCV] at hnat
    exact ⟨hab, n, Or.inl ⟨hn, hnat⟩⟩
  · exact ⟨hab, n, Or.inr (Or.inr ⟨hn, hnat⟩)⟩
  · exact ⟨hab, n, Or.inr (Or.inl hnat)⟩

theorem isSylowTwoOf_autOn (hyp : Hyp10 G T L I) {U : Subgroup G}
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) U) (autOn L U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hodd⟩ := SecA.isSylowTwoOf_inf hyp.fsu.maximal.1
  refine ⟨InternalSec.autOn_le_autOn_of_le inf_le_right,
    isPGroup_autOn (hyp.fsu.sylow.1.to_le inf_le_left), fun h2 => hodd ?_⟩
  set ρ := InternalSec.autOnHom hLU
  have heq : (autOn (T ⊓ L) U).subgroupOf (autOn L U) = ((T ⊓ L).subgroupOf L).map ρ := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := SecB.mem_autOn_iff.mp hy
      refine ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext ?_⟩
      rw [← hxy]
      rfl
    · rintro ⟨l, hl, rfl⟩
      exact SecB.mem_autOn_iff.mpr ⟨⟨l, hLU l.2⟩, Subgroup.mem_subgroupOf.mp hl, rfl⟩
  rw [heq] at h2
  exact h2.trans (Subgroup.index_map_dvd _ (InternalSec.autOnHom_surjective hLU))

theorem centralizes_U (hF : FactCommField) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h331 : Stmt3_3_1)
    (hyp : Hyp10 G T L I)
    (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥)
    {g : G} (hgH : g ∈ H) (hgM : g ∈ fsuM T L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hgr : g ^ r = 1) (hrL : ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∀ u ∈ fsuUL T L I, g * u * g⁻¹ = u := by
  have hCV := fsuCVM_eq_bot_of_comm h331 hyp hH hZH
  obtain ⟨hab, a, hmod⟩ := module_of_cases hCV hc
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hodd : Odd r := hr.odd_of_ne_two hr2
  set U := fsuUL T L I with hUdef
  have hgL := mem_normalizer_of_pow_prime h37 h38 hyp hgM hodd hgr
  have hgLt := mem_normalizer_conjugate_of_pow_prime h37 h38 hyp hgM hodd hgr ht
  have hgV : g ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I hgM
  have hNU : ∀ {x : G}, x ∈ Subgroup.normalizer (fsuVM T L I : Set G) →
      x ∈ Subgroup.normalizer (L : Set G) → x ∈ Subgroup.normalizer (U : Set G) :=
    fun hxV hxL => SecA.le_normalizer_commutator (Subgroup.zpowers_le.mpr hxV)
      (Subgroup.zpowers_le.mpr hxL) (Subgroup.mem_zpowers _)
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := fun l hl =>
    hNU (L_le_normalizer_fsuVM T L I hl) (Subgroup.le_normalizer hl)
  have hgU := hNU hgV hgL
  set x : MulAut ↥U := conjAct U ⟨g, hgU⟩ with hx
  have hR2 : IsPGroup 2 (autOn (T1 T L) U) :=
    isPGroup_autOn (hyp.fsu.sylow.1.to_le inf_le_left)
  have hconj : ∀ {y z : ↥(Subgroup.normalizer (U : Set G))},
      conjAct U y * conjAct U z * (conjAct U y)⁻¹ = conjAct U (y * z * y⁻¹) := by
    intro y z
    rw [map_mul, map_mul, map_inv]
  have hnormH : ∀ {y : ↥(Subgroup.normalizer (U : Set G))},
      (y : G) ∈ Subgroup.normalizer (L : Set G) →
      ∀ h ∈ autOn L U, conjAct U y * h * (conjAct U y)⁻¹ ∈ autOn L U := by
    intro y hy h hh
    obtain ⟨z, hzL, rfl⟩ := SecB.mem_autOn_iff.mp hh
    rw [hconj]
    exact SecB.mem_autOn_iff.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp hy z).mp hzL, rfl⟩
  have hRH : ∀ ρ ∈ autOn (T1 T L) U, ∀ h ∈ autOn L U, ρ * h * ρ⁻¹ ∈ autOn L U := by
    intro ρ hρ h hh
    obtain ⟨y, hy, rfl⟩ := SecB.mem_autOn_iff.mp hρ
    exact hnormH hy.2 h hh
  have hS : ∃ S : Subgroup (MulAut ↥U), S ≤ autOn (T1 T L) U ⊓ autOn L U ∧
      QuasithinUnique.IsSylowTwoOf S (autOn L U) :=
    ⟨autOn (T ⊓ L) U, le_inf (InternalSec.autOn_le_autOn_of_le
      (inf_le_inf_left T Subgroup.le_normalizer)) (InternalSec.autOn_le_autOn_of_le inf_le_right),
      isSylowTwoOf_autOn hyp hLU⟩
  have hrH : ¬ r ∣ Nat.card (autOn L U) := not_dvd_card_autOn_L hr hr2 hrL U
  have hxr : x ^ r = 1 := by
    rw [hx, ← map_pow]
    have : (⟨g, hgU⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ r = 1 :=
      Subtype.ext (by simpa using hgr)
    rw [this, map_one]
  have hxH : ∀ h ∈ autOn L U, x * h * x⁻¹ ∈ autOn L U := hnormH hgL
  have hfix : ∀ v : ↥U, (∀ ρ ∈ autOn (T1 T L) U, ρ v = v) → x v = v := by
    intro v hv
    have huT : ∀ s ∈ T1 T L, s * (v : G) * s⁻¹ = v := by
      intro s hs
      have hsU := hNU (SecA.le_normalizer_fsuVM T L I hs.1) hs.2
      have h1 := hv _ (SecB.mem_autOn_iff.mpr ⟨⟨s, hsU⟩, hs, rfl⟩)
      have h2 := congrArg Subtype.val h1
      rwa [conjAct_apply_coe] at h2
    have h := fix_of_comm h37 h38 h1011 hyp hCV hZH hgH hgL hgV ht htn hgLt v.2 huT
    apply Subtype.ext
    rw [hx, conjAct_apply_coe]
    exact h
  have hx1 : x = 1 := hF ↥U (autOn L U) (autOn (T1 T L) U) x a r hmod hR2 hRH hS hr hr2 hrH hxr
    hxH hfix
  intro u hu
  have h := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : G)) hx1
  simpa [hx, conjAct_apply_coe] using h

theorem mem_cenL0_of_field (hF : FactCommField) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h331 : Stmt3_3_1)
    (hyp : Hyp10 G T L I)
    (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥)
    {g : G} (hgH : g ∈ H) (hgM : g ∈ fsuM T L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hgr : g ^ r = 1) (hrL : ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) : g ∈ cenL0 T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have htH := hH.1.1 ht
  have htM := SecA.le_fsuM T L ht
  have h1 := centralizes_U hF h37 h38 h1011 h331 hyp hc hH hZH hgH hgM hr hr2 hgr hrL
  have h2 := centralizes_U hF h37 h38 h1011 h331 hyp hc hH hZH (g := t * g * t⁻¹)
    (H.mul_mem (H.mul_mem htH hgH) (H.inv_mem htH))
    ((fsuM T L).mul_mem ((fsuM T L).mul_mem htM hgM) ((fsuM T L).inv_mem htM)) hr hr2
    (by rw [conj_pow, hgr, mul_one, mul_inv_cancel]) hrL
  have hU : fsuUL T L I ≤ Subgroup.centralizer ({g} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := h1 u hu
    calc y * u = y * u * y⁻¹ * y := by group
      _ = u * y := by rw [this]
  have hU' : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [← SecA.conjugate_commutator_fsuVM htM]
    intro u hu
    rw [SecA.mem_conjugate_iff] at hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := h2 _ hu
    have e : y * u * y⁻¹ = u := by
      have e1 : t * (y * u * y⁻¹) * t⁻¹ = t * u * t⁻¹ := by
        calc t * (y * u * y⁻¹) * t⁻¹ = t * y * t⁻¹ * (t * u * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
          _ = t * u * t⁻¹ := this
      exact mul_left_cancel (mul_right_cancel e1)
    calc y * u = y * u * y⁻¹ * y := by group
      _ = u * y := by rw [e]
  have hgV : g ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [SecA.fsuVM_eq_sup h37 h38 hyp ht htn] at hv
    have := Subgroup.mem_centralizer_iff.mp (sup_le hU hU' hv) g (Set.mem_singleton g)
    exact this.symm
  refine mem_cenL0.mpr ⟨hgM, fun l hl => ?_⟩
  have hlN : l ∈ Subgroup.normalizer
      ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
    SecA.le_normalizer_centralizer (SecA.fsuL0_le_normalizer_fsuVM T L I) hl
  have h3 := (Subgroup.mem_normalizer_iff.mp hlN _).mp (Subgroup.inv_mem _ hgV)
  have h4 := Subgroup.mul_mem _ hgV h3
  simpa [mul_assoc] using h4

theorem eq_one_of_mem_cenL0 {H : Subgroup G} (hfaith : HallFaithful T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {z : G}
    (hz : z ∈ H ⊓ fsuM T L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hzp : z ^ p = 1)
    (hzC : z ∈ cenL0 T L I) : z = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx, hle⟩ := Ch11.SecB.exists_conj_le_hall hp2 hB (Subgroup.zpowers_le.mpr hz)
    (isPGroup_zpowers_of_pow_eq_one hp hzp)
  exact hfaith _ (isHallTwoPrimeOf_conjSub hx hB) z (hle (Subgroup.mem_zpowers z))
    (mem_cenL0.mp hzC).2

end CFSG.Quasithin.Vol2.Ch10.SecB
