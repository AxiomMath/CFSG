module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item14J2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148HJ

open CFSG Equiv
open scoped commutatorElement

theorem eq_one_of_central_of_coprime {X : Type*} [Group X] {b z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : z ^ 3 = 1) {k : ℕ} (hk : Nat.Coprime k 3)
    (hb : b ^ k = 1) (hbz : (b * z) ^ k = 1) : z = 1 := by
  have hcomm : Commute b z := Subgroup.mem_center_iff.mp hz b
  rw [hcomm.mul_pow, hb, one_mul] at hbz
  have h1 : orderOf z ∣ Nat.gcd k 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hbz) (orderOf_dvd_of_pow_eq_one hz3)
  rw [hk.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem map_inSubgroup_perfectResidual {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (T : Subgroup X) :
    (inSubgroup perfectResidual T).map f = inSubgroup perfectResidual (T.map f) := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq (f.subgroupMap T)
    (f.subgroupMap_surjective T)
  rw [inSubgroup, inSubgroup, Subgroup.map_map]
  rw [show (perfectResidual ↥(T.map f)) =
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(T.map f) from rfl, ← h,
    Subgroup.map_map]
  rfl

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {U : Subgroup X} {t : X}
    (h : ∀ u ∈ U, t * u * t⁻¹ ∈ U) : t ∈ Subgroup.normalizer (U : Set X) := by
  have hle : U.map (MulAut.conj t).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have heq : U.map (MulAut.conj t).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨h u, fun hu => ?_⟩
  rw [← heq] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  have hvu' : t * v * t⁻¹ = t * u * t⁻¹ := hvu
  have : v = u := by simpa using hvu'
  exact this ▸ hv

theorem commutatorElement_mul_central {X : Type*} [Group X] {a b z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  have e₁ : z * (b * w) * z⁻¹ = b * w := by rw [← hz' (b * w), mul_inv_cancel_right]
  have e₂ : a * (b * w) * a⁻¹ = a * b * a⁻¹ * w := by
    calc a * (b * w) * a⁻¹ = a * b * (w * a⁻¹) := by group
      _ = a * b * (a⁻¹ * w) := by rw [hw' a⁻¹]
      _ = a * b * a⁻¹ * w := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * b * a⁻¹ * w * (b * w)⁻¹ := by rw [e₁, e₂]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem card_le_sixty_of_lt {K : Subgroup (Perm (Fin 6))} (hK : K ≤ alternatingGroup (Fin 6))
    (hne : K ≠ alternatingGroup (Fin 6)) : Nat.card K ≤ 60 := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  set K' := K.subgroupOf (alternatingGroup (Fin 6))
  have hK' : K' ≠ ⊤ := fun h => hne (le_antisymm hK (Subgroup.subgroupOf_eq_top.1 h))
  have hcore : K'.normalCore = ⊥ := by
    rcases K'.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ K'.normalCore_le)) hK'
  have h1 := K'.index_normalCore_le_factorial_index
  rw [hcore, Subgroup.index_bot, card_alternatingGroup_six] at h1
  have h2 := K'.index_mul_card
  rw [card_alternatingGroup_six, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h2
  by_contra hlt
  have h5 : K'.index ≤ 5 := by
    by_contra h6
    have := Nat.mul_le_mul (show 6 ≤ K'.index by omega) (show 61 ≤ Nat.card K by omega)
    omega
  have h120 := Nat.factorial_le h5
  have : (5 : ℕ).factorial = 120 := rfl
  omega

section Cover

variable {X : Type*} [Group X] [Finite X]

theorem triple_cover_dichotomy (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6)))
    (hXp : Group.IsPerfect X) {x : X} (hx3 : x ^ 3 = 1) (hxZ : x ∉ Subgroup.center X)
    {T : Subgroup X} (hxT : x ∈ Subgroup.normalizer (T : Set X)) :
    (∀ U : Subgroup X, U ≤ T → ¬ 3 ∣ Nat.card U → x ∈ Subgroup.normalizer (U : Set X) →
        T ≤ Subgroup.normalizer (U : Set X)) ∨
      ((Nonempty (↥(inSubgroup perfectResidual T) ≃* alternatingGroup (Fin 5)) ∨
          inSubgroup perfectResidual T = ⊤) ∧
        ∀ U : Subgroup X, U ≤ T → ¬ 3 ∣ Nat.card U → U ≤ inSubgroup perfectResidual T) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ3, ⟨e⟩⟩ := hX
  set Z := Subgroup.center X with hZdef
  set p : X →* Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Z)) with hp
  have hpker : ∀ g : X, p g = 1 ↔ g ∈ Z := by
    intro g
    simp only [hp, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, OneMemClass.coe_eq_one, map_eq_one_iff _ e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hpA : ∀ g : X, p g ∈ alternatingGroup (Fin 6) := fun g => (e (QuotientGroup.mk g)).2
  have hpsurj : ∀ y ∈ alternatingGroup (Fin 6), ∃ g : X, p g = y := by
    intro y hy
    obtain ⟨q, hq⟩ := e.surjective ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨g, congrArg Subtype.val hq⟩
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ3] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hfib : ∀ g h : X, p g = p h → h⁻¹ * g ∈ Z := fun g h hgh => by
    rw [← hpker, map_mul, map_inv, hgh, inv_mul_cancel]
  have hcop : ∀ U : Subgroup X, ¬ 3 ∣ Nat.card U → Nat.Coprime (Nat.card U) 3 := fun U hU =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU).symm
  have hpowU : ∀ U : Subgroup X, ∀ u ∈ U, u ^ Nat.card U = 1 := fun U u hu =>
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard U hu)
  by_cases hTs : Group.IsSolvable T
  ·
    left
    intro U hUT hU3 hxU
    have hx1 : p x ≠ 1 := fun h => hxZ ((hpker x).mp h)
    have hTA : T.map p ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨t, -, rfl⟩
      exact hpA t
    have hxT' : p x ∈ Subgroup.normalizer ((T.map p : Subgroup _) : Set (Perm (Fin 6))) :=
      Subgroup.le_normalizer_map p ⟨x, hxT, rfl⟩
    have hxU' : p x ∈ Subgroup.normalizer ((U.map p : Subgroup _) : Set (Perm (Fin 6))) :=
      Subgroup.le_normalizer_map p ⟨x, hxU, rfl⟩
    have hTs' : Group.IsSolvable (T.map p) :=
      Group.isSolvable_of_surjective (p.subgroupMap_surjective T)
    have hU3' : ¬ 3 ∣ Nat.card (U.map p) := fun h => hU3 (h.trans (Subgroup.card_map_dvd U p))
    have key := le_normalizer_of_isSolvable (by rw [← map_pow, hx3, map_one]) hx1 hTA hxT' hTs'
      (Subgroup.map_mono hUT) hU3' hxU'
    intro t ht
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have hpw : p (t * u * t⁻¹) ∈ U.map p := by
      have h := key (Subgroup.mem_map_of_mem p ht)
      have := (Subgroup.mem_normalizer_iff.mp h (p u)).mp ⟨u, hu, rfl⟩
      simpa [map_mul, map_inv] using this
    obtain ⟨u', hu', hu'w⟩ := hpw
    have hz : u'⁻¹ * (t * u * t⁻¹) ∈ Z := hfib _ u' hu'w.symm
    have hwk : (t * u * t⁻¹) ^ Nat.card U = 1 := by rw [conj_pow, hpowU U u hu, mul_one,
      mul_inv_cancel]
    have h1 := eq_one_of_central_of_coprime hz (hz3 _ hz) (hcop U hU3) (hpowU U u' hu')
      (by rw [show u' * (u'⁻¹ * (t * u * t⁻¹)) = t * u * t⁻¹ by group]; exact hwk)
    have : t * u * t⁻¹ = u' := by
      calc t * u * t⁻¹ = u' * (u'⁻¹ * (t * u * t⁻¹)) := by group
        _ = u' := by rw [h1, mul_one]
    exact this ▸ hu'
  ·
    right
    set P := inSubgroup perfectResidual T with hPdef
    obtain ⟨-, -, hRperf, -, -, hRbot⟩ := perfect_residual_characterization (G := T)
    have hPperf : Group.IsPerfect P :=
      Group.IsPerfect.ofSurjective
        (f := ((perfectResidual T).equivMapOfInjective T.subtype T.subtype_injective).toMonoidHom)
        (MulEquiv.surjective _)
    have hPne : P ≠ ⊥ := by
      intro h
      apply hTs
      apply hRbot.mp
      rwa [hPdef, inSubgroup, Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at h
    have hPT : P ≤ T := Subgroup.map_subtype_le _
    set Pb := P.map p with hPbdef
    have hPbperf : Group.IsPerfect Pb := Group.IsPerfect.map (H := P) p
    have hPbne : Pb ≠ ⊥ := by
      intro h
      have hPZ : P ≤ Z := fun g hg => (hpker g).mp (by
        have : p g ∈ Pb := ⟨g, hg, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this)
      apply hPne
      have hZZ : ⁅Z, Z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.center_le_centralizer _)
      rw [← Subgroup.isPerfect_iff.mp hPperf]
      exact le_bot_iff.mp (hZZ ▸ Subgroup.commutator_mono hPZ hPZ)
    rcases CFSG.RankThree.PartTwo.Sec4.Census.perfect_perm_six hPbperf hPbne with hA6 | hA5
    ·
      have hdecomp : ∀ g : X, ∃ q ∈ P, q⁻¹ * g ∈ Z := fun g => by
        have : p g ∈ Pb := hA6 ▸ hpA g
        obtain ⟨q, hq, hqg⟩ := this
        exact ⟨q, hq, hfib g q hqg.symm⟩
      have hcomm : commutator X ≤ P := by
        rw [commutator_def, Subgroup.commutator_le]
        intro g _ h _
        obtain ⟨q, hq, hqz⟩ := hdecomp g
        obtain ⟨q', hq', hq'z⟩ := hdecomp h
        have hg : g = q * (q⁻¹ * g) := by group
        have hh : h = q' * (q'⁻¹ * h) := by group
        rw [hg, hh, commutatorElement_mul_central hqz hq'z]
        exact Subgroup.commutator_mem_commutator hq hq' |>
          (Subgroup.isPerfect_iff.mp hPperf).le
      have hPtop : P = ⊤ := top_le_iff.mp (hXp.commutator_eq_top ▸ hcomm)
      exact ⟨Or.inr hPtop, fun U _ _ => hPtop ▸ le_top⟩
    ·
      obtain ⟨eA5⟩ := hA5
      have hPbcard : Nat.card Pb = 60 := by
        rw [Nat.card_congr eA5.toEquiv, card_alternatingGroup_five]
      have hPZ : P ⊓ Z = ⊥ := by
        by_contra hne
        have hZP : Z ≤ P := by
          have hdvd : Nat.card (P ⊓ Z : Subgroup X) ∣ 3 :=
            hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
          · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
          · have : P ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZ3])
            exact this ▸ inf_le_left
        set Z' := Z.subgroupOf P with hZ'def
        have hZ'3 : Nat.card Z' = 3 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ3]
        have hker : (p.subgroupMap P).ker = Z' := by
          ext g
          rw [MonoidHom.mem_ker, hZ'def, Subgroup.mem_subgroupOf, ← hpker]
          exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
        have hPcard : Nat.card P = 180 := by
          have h := Subgroup.card_ker_mul_card_of_surjective (p.subgroupMap_surjective P)
          rw [hker, hZ'3, hPbcard] at h
          omega
        have hZ'p : IsPGroup 3 Z' := IsPGroup.of_card (n := 1) (by rw [hZ'3, pow_one])
        obtain ⟨S, hZ'S⟩ := hZ'p.exists_le_sylow
        have hS9 : Nat.card (S : Subgroup P) = 9 := by
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
          have hidx := Subgroup.card_mul_index (S : Subgroup P)
          have hndvd := S.not_dvd_index
          rw [hk, hPcard] at hidx
          have hk4 : k ≤ 4 := by
            by_contra hk4
            have : 3 ^ 5 ≤ 3 ^ k * (S : Subgroup P).index :=
              (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
                (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (fun h0 => by
                  rw [h0, mul_zero] at hidx; omega)))
            omega
          interval_cases k <;> omega
        have hSab : IsMulCommutative (S : Subgroup P) :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hS9]; norm_num)
        obtain ⟨⟨z, hzZ'⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
          (fun h : Z' = ⊥ => by rw [h, Subgroup.card_bot] at hZ'3; omega)
        have hzc : z ∈ Subgroup.center P := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext ((Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hzZ')) g)
        have hPc : commutator P = ⊤ := hPperf.commutator_eq_top
        exact hz1 (Subtype.ext (CFSG.RankThree.PartTwo.KFacts.K412.eq_one_of_mem_center_of_mem_sylow
          hPc S hSab hzc (hZ'S hzZ')))
      have hinj : Function.Injective (p.subgroupMap P) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro g hg
        have hgZ : (g : X) ∈ Z := (hpker g).mp (congrArg Subtype.val hg)
        have : (g : X) ∈ P ⊓ Z := ⟨g.2, hgZ⟩
        rw [hPZ, Subgroup.mem_bot] at this
        exact Subtype.ext this
      let eP : P ≃* Pb := MulEquiv.ofBijective (p.subgroupMap P) ⟨hinj, p.subgroupMap_surjective P⟩
      have hTP : T.map p = Pb := by
        have hle : Pb ≤ T.map p := Subgroup.map_mono hPT
        have hTA : T.map p ≤ alternatingGroup (Fin 6) := by
          rintro _ ⟨t, -, rfl⟩
          exact hpA t
        have hne : T.map p ≠ alternatingGroup (Fin 6) := by
          intro h
          have h1 : Pb = inSubgroup perfectResidual (T.map p) := map_inSubgroup_perfectResidual p T
          rw [h, CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect
            alternatingGroup_six_isPerfect] at h1
          have := hPbcard
          rw [h1, card_alternatingGroup_six] at this
          omega
        exact (Subgroup.eq_of_le_of_card_ge hle
          (by rw [hPbcard]; exact card_le_sixty_of_lt hTA hne)).symm
      refine ⟨Or.inl ⟨eP.trans eA5⟩, fun U hUT hU3 u hu => ?_⟩
      have hpu : p u ∈ Pb := hTP ▸ ⟨u, hUT hu, rfl⟩
      obtain ⟨q, hq, hqu⟩ := hpu
      have hz : q⁻¹ * u ∈ Z := hfib u q hqu.symm
      have hqz : q * (q⁻¹ * u) = u := by group
      have hqk : q ^ Nat.card U = 1 := by
        have hcomm : Commute q (q⁻¹ * u) := ((Subgroup.mem_center_iff.mp hz) q)
        have e := hcomm.mul_pow (Nat.card U)
        rw [hqz, hpowU U u hu] at e
        have hqkZ : q ^ Nat.card U ∈ Z := by
          rw [eq_inv_of_mul_eq_one_left e.symm]
          exact inv_mem (pow_mem hz _)
        have : q ^ Nat.card U ∈ P ⊓ Z := ⟨pow_mem hq _, hqkZ⟩
        rw [hPZ, Subgroup.mem_bot] at this
        exact this
      have h1 := eq_one_of_central_of_coprime hz (hz3 _ hz) (hcop U hU3) hqk
        (by rw [hqz]; exact hpowU U u hu)
      have : u = q := by
        calc u = q * (q⁻¹ * u) := hqz.symm
          _ = q := by rw [h1, mul_one]
      exact this ▸ hq

theorem triple_cover_dichotomy_in {H : Type*} [Group H] [Finite H] {𝔍 : Subgroup H}
    (h𝔍 : Sec4.IsTripleCover ↥𝔍 (alternatingGroup (Fin 6))) (h𝔍p : Group.IsPerfect ↥𝔍)
    {x : H} (hx𝔍 : x ∈ 𝔍) (hx3 : x ^ 3 = 1) (hxZ : ∃ y ∈ 𝔍, x * y ≠ y * x)
    {T : Subgroup H} (hT𝔍 : T ≤ 𝔍) (hxT : x ∈ Subgroup.normalizer (T : Set H)) :
    (∀ U : Subgroup H, U ≤ T → ¬ 3 ∣ Nat.card U → x ∈ Subgroup.normalizer (U : Set H) →
        T ≤ Subgroup.normalizer (U : Set H)) ∨
      ((Nonempty (↥(inSubgroup perfectResidual T) ≃* alternatingGroup (Fin 5)) ∨
          inSubgroup perfectResidual T = 𝔍) ∧
        ∀ U : Subgroup H, U ≤ T → ¬ 3 ∣ Nat.card U → U ≤ inSubgroup perfectResidual T) := by
  set x' : 𝔍 := ⟨x, hx𝔍⟩ with hx'def
  set T' := T.subgroupOf 𝔍 with hT'def
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxZ' : x' ∉ Subgroup.center 𝔍 := by
    intro hc
    obtain ⟨y, hy, hxy⟩ := hxZ
    exact hxy (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc ⟨y, hy⟩).symm))
  have hnorm : ∀ {V : Subgroup H}, x ∈ Subgroup.normalizer (V : Set H) →
      x' ∈ Subgroup.normalizer ((V.subgroupOf 𝔍 : Subgroup 𝔍) : Set 𝔍) := by
    intro V hxV
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hxV y
  have hcard : ∀ {V : Subgroup H}, V ≤ 𝔍 → Nat.card (V.subgroupOf 𝔍) = Nat.card V :=
    fun hV => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv
  have hT'eq : T'.map 𝔍.subtype = T := Subgroup.map_subgroupOf_eq_of_le hT𝔍
  have hPeq : (inSubgroup perfectResidual T').map 𝔍.subtype = inSubgroup perfectResidual T := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      𝔍.subtype 𝔍.subtype_injective, hT'eq]
  rcases triple_cover_dichotomy h𝔍 h𝔍p hx'3 hxZ' (hnorm hxT) with hL | ⟨hP, hU⟩
  · left
    intro U hUT hU3 hxU
    have hU𝔍 : U ≤ 𝔍 := hUT.trans hT𝔍
    have key := hL (U.subgroupOf 𝔍) (Subgroup.comap_mono hUT) (by rwa [hcard hU𝔍]) (hnorm hxU)
    intro t ht
    have h := key (Subgroup.mem_subgroupOf.mpr ht : (⟨t, hT𝔍 ht⟩ : 𝔍) ∈ T')
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have := (Subgroup.mem_normalizer_iff.mp h ⟨u, hU𝔍 hu⟩).mp (Subgroup.mem_subgroupOf.mpr hu)
    exact Subgroup.mem_subgroupOf.mp this
  · right
    refine ⟨?_, fun U hUT hU3 => ?_⟩
    · rcases hP with he | htop
      · left
        obtain ⟨e⟩ := he
        rw [← hPeq]
        exact ⟨((inSubgroup perfectResidual T').equivMapOfInjective 𝔍.subtype
          𝔍.subtype_injective).symm.trans e⟩
      · right
        rw [← hPeq, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · have hU𝔍 : U ≤ 𝔍 := hUT.trans hT𝔍
      have h := hU (U.subgroupOf 𝔍) (Subgroup.comap_mono hUT) (by rwa [hcard hU𝔍])
      rw [← hPeq, ← Subgroup.map_subgroupOf_eq_of_le hU𝔍]
      exact Subgroup.map_mono h

end Cover

end CFSG.RankThree.PartTwo.Sec14.Item148HJ
