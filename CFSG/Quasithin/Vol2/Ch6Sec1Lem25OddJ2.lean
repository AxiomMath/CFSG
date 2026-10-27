module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
import CFSG.RankThree.PartOne.KS.J2
public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin.H13.OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem card_modEq_card_inf_centralizer {X : Type} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] {x : X} (hx : x ^ p = 1) {Y : Subgroup X}
    (hxY : x ∈ Subgroup.normalizer (Y : Set X)) :
    Nat.card Y ≡ Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) [MOD p] := by
  classical
  set R := Subgroup.zpowers x with hR
  have hRY : R ≤ Subgroup.normalizer (Y : Set X) := Subgroup.zpowers_le.mpr hxY
  let := Subgroup.conjMulDistribMulActionOfLeNormalizer R Y hRY
  have hRp : IsPGroup p R := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ p ^ 1 = 1 by rw [pow_one]; exact hx))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hRp.card_modEq_card_fixedPoints Y
  have hsmul : ∀ (r : R) (y : Y), ((r • y : Y) : X) = (r : X) * y * (r : X)⁻¹ := fun r y =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit R Y hRY r y
  let e : MulAction.fixedPoints R Y ≃
      (Y ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) :=
    { toFun := fun y => ⟨((y : Y) : X), Subgroup.mem_inf.mpr ⟨(y : Y).2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := congrArg Subtype.val (y.2 ⟨x, Subgroup.mem_zpowers x⟩)
        rw [hsmul] at h1
        calc ((y : Y) : X) * x = x * (y : Y) * x⁻¹ * x := by rw [h1]
          _ = x * (y : Y) := by group⟩⟩
      invFun := fun z => ⟨⟨z, (Subgroup.mem_inf.mp z.2).1⟩, fun r => by
        apply Subtype.ext
        rw [hsmul]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp r.2
        have hc : Commute x (z : X) :=
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp z.2).2).symm
        have hcj : Commute (x ^ j) (z : X) := hc.zpow_left j
        rw [← hj]
        change x ^ j * (z : X) * (x ^ j)⁻¹ = z
        rw [hcj.eq, mul_inv_cancel_right]⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  rwa [Nat.card_congr e] at hmod

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native
open CFSG.RankThree.PartOne

private theorem j2P_false_of_seven
    {T G : Equiv.Perm (Fin 315)} (hT : T ∈ j2P) (hG : G ∈ j2P)
    (hT2 : orderOf T = 2) (hG7 : orderOf G = 7) (hTG : T * G = G * T) : False := by
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hTR : T ∈ j2R := (le_sup_left : j2P ≤ j2P ⊔ Subgroup.zpowers j2u) hT
  obtain ⟨row, hrow, c, hc, hTc⟩ := hcover T hTR hT2
  obtain ⟨-, -, houter, -, hcard, -⟩ := hrows row hrow
  have hrep : tp 315 row.rep = c⁻¹ * T * c := by
    rw [hTc]
    group
  have hrepP : tp 315 row.rep ∈ j2P := by
    rw [hrep]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hc) hT) hc
  have hinner : row.outer = false := by
    cases h : row.outer
    · rfl
    · exact absurd hrepP (houter.1 h)
  have hco : row.centOrder = 240 ∨ row.centOrder = 1920 := by
    have hmem : (row.outer, row.classSize, row.centOrder) ∈
        [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
      rw [← hmap]
      exact List.mem_map_of_mem hrow
    rw [hinner] at hmem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact absurd h (by decide)
    · exact Or.inl h
    · exact Or.inr h
  have hmem : c⁻¹ * G * c ∈
      j2P ⊓ Subgroup.centralizer ({tp 315 row.rep} : Set (Equiv.Perm (Fin 315))) := by
    refine Subgroup.mem_inf.mpr ⟨j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hc) hG) hc, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hrep]
    calc c⁻¹ * G * c * (c⁻¹ * T * c) = c⁻¹ * (G * T) * c := by group
      _ = c⁻¹ * (T * G) * c := by rw [hTG]
      _ = c⁻¹ * T * c * (c⁻¹ * G * c) := by group
  have ho : orderOf (c⁻¹ * G * c) = 7 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) G
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hG7]
  have h7 : 7 ∣ row.centOrder := by
    rw [← hcard, ← ho]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  rcases hco with h | h <;> rw [h] at h7 <;> norm_num at h7

private theorem j2P_false_of_five
    {G : Equiv.Perm (Fin 315)} (hG : G ∈ j2P)
    (hG5 : orderOf G = 5) {E : Subgroup (Equiv.Perm (Fin 315))} (hEP : E ≤ j2P)
    (hE8 : Nat.card E = 8) (hEG : ∀ x ∈ E, x * G = G * x) : False := by
  obtain ⟨⟨-, -, -, -, S5, hS5⟩, ⟨hlines, -⟩, hrec, hgood, hbad⟩ :=
    R3E_J2_full_five_centralizer_structure
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set G' : ↥j2P := ⟨G, hG⟩ with hG'
  have hG'p : IsPGroup 5 (Subgroup.zpowers G') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hG', Subgroup.orderOf_mk, hG5, pow_one])
  obtain ⟨S', hS'⟩ := hG'p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥j2P) S' S5
  have hcG : c * G' * c⁻¹ ∈ (S5 : Subgroup ↥j2P) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, show c⁻¹ * (c * G' * c⁻¹) * c = G' by group]
    exact hS' (Subgroup.mem_zpowers G')
  rw [hS5, Subgroup.mem_subgroupOf] at hcG
  set C : Equiv.Perm (Fin 315) := (c : Equiv.Perm (Fin 315)) with hC
  have hCP : C ∈ j2P := c.2
  have hy : ((c * G' * c⁻¹ : ↥j2P) : Equiv.Perm (Fin 315)) = C * G * C⁻¹ := rfl
  rw [hy] at hcG
  have hy5 : orderOf (C * G * C⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hG5]
  have hline : Subgroup.zpowers (C * G * C⁻¹) ∈
      {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} :=
    ⟨Subgroup.zpowers_le.mpr hcG, by rw [Nat.card_zpowers, hy5]⟩
  rw [hlines] at hline
  obtain ⟨i, hi⟩ := hline
  have hxi : j2FiveLine i ∈ Subgroup.zpowers (C * G * C⁻¹) := by
    rw [← hi]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxi
  have hle : E.map (MulAut.conj C).toMonoidHom ≤ j2FiveC i := by
    rw [(hrec i).1]
    rintro _ ⟨x, hx, rfl⟩
    have hxP := hEP hx
    refine Subgroup.mem_inf.mpr ⟨(le_sup_left : j2P ≤ j2P ⊔ Subgroup.zpowers j2u)
      (j2P.mul_mem (j2P.mul_mem hCP hxP) (j2P.inv_mem hCP)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    have hcomm : Commute (C * x * C⁻¹) (C * G * C⁻¹) := by
      show C * x * C⁻¹ * (C * G * C⁻¹) = C * G * C⁻¹ * (C * x * C⁻¹)
      calc C * x * C⁻¹ * (C * G * C⁻¹) = C * (x * G) * C⁻¹ := by group
        _ = C * (G * x) * C⁻¹ := by rw [hEG x hx]
        _ = C * G * C⁻¹ * (C * x * C⁻¹) := by group
    exact (hcomm.zpow_right k).eq
  have h8 : 8 ∣ Nat.card (j2FiveC i) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj C).injective, hE8] at h
  have hcases : Nat.card (j2FiveC i) = 50 ∨ Nat.card (j2FiveC i) = 300 := by
    by_cases h : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
    · exact Or.inl (hgood i h).1
    · have h' : i.val = 2 ∨ i.val = 3 ∨ i.val = 5 := by
        have := i.isLt
        omega
      exact Or.inr (hbad i h').1
  rcases hcases with h | h <;> rw [h] at h8 <;> norm_num at h8

theorem oddSylowJ2_holds :
    OddSylowJ2 := by
  intro S _ _ hS hna hJ P hP d r hr hr2 hd hdP hx _
  obtain ⟨e⟩ := hJ
  let e' : S ≃* CFSG.Blueprint.NativeSporadic.J2 := e
  let ψ : S ≃* ↥j2P := e'.trans j2PermEquiv
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hout : ¬ r ∣ Nat.card (Outer S) := by
    intro h
    have hc : Nat.card (Outer S) = Nat.card (Outer CFSG.Blueprint.NativeSporadic.J2) :=
      Nat.card_congr (equivalence e').toEquiv
    have hle := AT_J2_Schreier.1
    have hpos : 0 < Nat.card (Outer S) := Nat.card_pos
    have := Nat.le_of_dvd hpos h
    omega
  have hinn := mem_innAut_of_not_dvd hr hd hout
  refine ⟨?_, hinn⟩
  obtain ⟨g, hgN, rfl, hgo⟩ := exists_conj_of_mem_innAut (conj_injective hS hna) hd hdP hinn
  obtain ⟨x0, hx0P, hx0⟩ := hx
  have hnc : ¬ P ≤ Subgroup.centralizer ({g} : Set S) := by
    intro h
    apply hx0
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (h hx0P)
    rw [MulAut.conj_apply, ← hc, mul_inv_cancel_right]
  have hcardS : Nat.card S = 604800 := by rw [Nat.card_congr ψ.toEquiv, card_j2P]
  have hrdvd : r ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := by
    rw [← hgo, show (2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 : ℕ) = 604800 by norm_num, ← hcardS]
    exact orderOf_dvd_natCard g
  have hr357 : r = 3 ∨ r = 5 ∨ r = 7 := by
    rcases (Nat.Prime.dvd_mul hr).1 hrdvd with h | h7
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h5
      · rcases (Nat.Prime.dvd_mul hr).1 h with h2 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
            hr2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
            (hr.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1
          (hr.dvd_of_dvd_pow h5)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h7))
  have hidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  have hP128 : Nat.card P = 128 := by
    obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
    have hmul := P.card_mul_index
    rw [hk, hcardS] at hmul
    have hk20 : k < 20 := by
      by_contra h
      have h1 : 2 ^ 20 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 0 < P.index := Nat.pos_of_ne_zero fun h0 => hidx (h0 ▸ dvd_zero 2)
      have h3 : 2 ^ k ≤ 604800 := by
        rw [← hmul]
        exact Nat.le_mul_of_pos_right _ h2
      norm_num at h1
      omega
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega
  set F := P ⊓ Subgroup.centralizer ({g} : Set S) with hF
  have hFP : F ≤ P := inf_le_left
  have hFne : Nat.card F ≠ 128 := by
    intro h
    have hFP' : F = P := Subgroup.eq_of_le_of_card_ge hFP (by rw [h, hP128])
    apply hnc
    rw [← hFP']
    exact inf_le_right
  obtain ⟨j, hj⟩ := (hP.2.1.to_le hFP).exists_card_eq
  have hj7 : j ≤ 7 := by
    have h := Subgroup.card_dvd_of_le hFP
    rw [hj, hP128, show (128 : ℕ) = 2 ^ 7 by norm_num] at h
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h
  have : Fact r.Prime := ⟨hr⟩
  have hmod : Nat.card P ≡ Nat.card F [MOD r] :=
    card_modEq_card_inf_centralizer (by rw [← hgo, pow_orderOf_eq_one]) hgN
  rw [hP128, hj] at hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hr357 with h3 | h5 | h7
  · exact h3
  · exfalso
    subst h5
    have hj3 : j = 3 := by
      interval_cases j
      all_goals first
        | rfl
        | (exfalso; norm_num [Nat.ModEq] at hmod; done)
        | (exfalso; exact hFne (by rw [hj]; norm_num))
    subst hj3
    refine j2P_false_of_five (G := (ψ g : Equiv.Perm (Fin 315))) (ψ g).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hgo])
      (E := (F.map ψ.toMonoidHom).map j2P.subtype) (Subgroup.map_subtype_le _) ?_ ?_
    · rw [Subgroup.card_map_of_injective j2P.subtype_injective,
        Subgroup.card_map_of_injective ψ.injective, hj]
      norm_num
    · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      have hfg : f * g = g * f := Subgroup.mem_centralizer_singleton_iff.mp hf.2
      change ((ψ f : ↥j2P) : Equiv.Perm (Fin 315)) * (ψ g : Equiv.Perm (Fin 315)) =
        (ψ g : Equiv.Perm (Fin 315)) * (ψ f : Equiv.Perm (Fin 315))
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hfg]
  · exfalso
    subst h7
    have hj1 : 1 ≤ j := by
      by_contra h
      have hj0 : j = 0 := by omega
      subst hj0
      norm_num [Nat.ModEq] at hmod
    have h2F : 2 ∣ Nat.card F := by
      rw [hj]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 2 h2F
    have htg : (t : S) * g = g * t := Subgroup.mem_centralizer_singleton_iff.mp t.2.2
    refine j2P_false_of_seven (T := (ψ t : Equiv.Perm (Fin 315)))
      (G := (ψ g : Equiv.Perm (Fin 315))) (ψ t).2 (ψ g).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht])
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hgo]) ?_
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, htg]

end CFSG.Quasithin.H13.OddSyl
