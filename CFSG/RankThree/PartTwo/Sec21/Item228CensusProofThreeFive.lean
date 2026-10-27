module

import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofA9
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def L2Order228 (S : Type) [Group S] : Prop :=
  ∀ x : S, orderOf x = 3 →
    (∀ m : ℕ, 0 < m → Even m →
      Nat.card (projSL 2 (GaloisField 2 m)) ∣ 3 * Nat.card (Subgroup.centralizer ({x} : Set S)) →
        m = 2) ∧
      ¬ 62400 ∣ 3 * Nat.card (Subgroup.centralizer ({x} : Set S))

@[expose] def ThreeFiveData228 (S : Type) [Group S] : Prop :=
  ∀ x k : S, orderOf x = 3 → orderOf k = 5 → x * k = k * x →
    18 * Nat.card (Subgroup.centralizer ({x} : Set S) ⊓
        Subgroup.normalizer ((Subgroup.zpowers k : Subgroup S) : Set S) : Subgroup S) <
      Nat.card (Subgroup.centralizer ({x} : Set S))

namespace Item228CensusProof

theorem card_sylow_five_le_six {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 60) :
    Nat.card (Sylow 5 H) ≤ 6 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 H) := inferInstance
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  have hmul := (P : Subgroup H).card_mul_index
  rw [hk, hH] at hmul
  have hndvd := P.not_dvd_index
  have hidx : (P : Subgroup H).index = 12 := by
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have : 5 ^ 2 ∣ 60 := (pow_dvd_pow 5 (by omega)).trans (Dvd.intro _ hmul)
      norm_num at this
    interval_cases k
    · rw [pow_zero, one_mul] at hmul
      rw [hmul] at hndvd
      norm_num at hndvd
    · rw [pow_one] at hmul
      omega
  have hdvd := P.card_dvd_index
  rw [hidx] at hdvd
  have hmod : Nat.card (Sylow 5 H) % 5 = 1 := card_sylow_modEq_one 5 H
  have hle : Nat.card (Sylow 5 H) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (Sylow 5 H) <;> simp_all

theorem card_subgroups_five_le_six {S : Type*} [Group S] {M : Subgroup S} [Finite M]
    (hM : Nat.card M = 60) :
    Nat.card {Q : Subgroup S // Q ≤ M ∧ Nat.card Q = 5} ≤ 6 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : ∀ Q : {Q : Subgroup S // Q ≤ M ∧ Nat.card Q = 5},
      Nat.card (Q.1.subgroupOf M) = 5 := fun Q => by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.2.1).toEquiv, Q.2.2]
  let φ : {Q : Subgroup S // Q ≤ M ∧ Nat.card Q = 5} → Sylow 5 M := fun Q =>
    IsPGroup.toSylow (P := Q.1.subgroupOf M) (IsPGroup.of_card (n := 1) (by rw [hcard Q, pow_one]))
      (by
        have h := (Q.1.subgroupOf M).card_mul_index
        rw [hcard Q, hM] at h
        have : (Q.1.subgroupOf M).index = 12 := by omega
        rw [this]
        norm_num)
  have hφ : Function.Injective φ := by
    intro Q₁ Q₂ h
    have h1 : Q₁.1.subgroupOf M = Q₂.1.subgroupOf M := congrArg Sylow.toSubgroup h
    apply Subtype.ext
    have h2 := congrArg (fun K : Subgroup M => K.map M.subtype) h1
    simp only [Subgroup.map_subgroupOf_eq_of_le Q₁.2.1, Subgroup.map_subgroupOf_eq_of_le Q₂.2.1]
      at h2
    exact h2
  exact (Nat.card_le_card_of_injective φ hφ).trans (card_sylow_five_le_six hM)

open Pointwise in
theorem card_le_six_mul_card_normalizer {S : Type*} [Group S] [Finite S] {C M Q : Subgroup S}
    (hnorm : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M) (hM : Nat.card M = 60)
    (hQM : Q ≤ M) (hQ : Nat.card Q = 5) :
    Nat.card C ≤ 6 * Nat.card (C ⊓ Subgroup.normalizer (Q : Set S) : Subgroup S) := by
  classical
  let ι : C →* ConjAct S := (ConjAct.toConjAct : S ≃* ConjAct S).toMonoidHom.comp C.subtype
  let _ : MulAction C (Subgroup S) := MulAction.compHom _ ι
  have hsmul : ∀ (c : C) (K : Subgroup S), c • K = ConjAct.toConjAct (c : S) • K := fun _ _ => rfl
  have hstab : MulAction.stabilizer C Q = (Subgroup.normalizer (Q : Set S)).subgroupOf C := by
    ext c
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.conjAct_pointwise_smul_iff,
      Subgroup.mem_subgroupOf]
  have hstabcard : Nat.card (MulAction.stabilizer C Q) =
      Nat.card (C ⊓ Subgroup.normalizer (Q : Set S) : Subgroup S) := by
    rw [hstab, ← Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have horb : Nat.card (MulAction.orbit C Q) ≤ 6 := by
    have hmem : ∀ K ∈ MulAction.orbit C Q, K ≤ M ∧ Nat.card K = 5 := by
      rintro _ ⟨c, rfl⟩
      change ConjAct.toConjAct (c : S) • Q ≤ M ∧ Nat.card ↥(ConjAct.toConjAct (c : S) • Q) = 5
      refine ⟨fun z hz => ?_, ?_⟩
      · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ConjAct.toConjAct_smul]
          at hz
        have := hnorm c c.2 _ (hQM hz)
        simpa [mul_assoc] using this
      · rw [← Nat.card_congr (Subgroup.equivSMul (ConjAct.toConjAct (c : S)) Q).toEquiv, hQ]
    let ψ : MulAction.orbit C Q → {K : Subgroup S // K ≤ M ∧ Nat.card K = 5} :=
      fun K => ⟨K.1, hmem K.1 K.2⟩
    have hψ : Function.Injective ψ := fun K₁ K₂ h => Subtype.ext (by
      have := congrArg (fun K : {K : Subgroup S // K ≤ M ∧ Nat.card K = 5} => K.1) h
      exact this)
    exact (Nat.card_le_card_of_injective ψ hψ).trans (card_subgroups_five_le_six hM)
  have hidx := MulAction.index_stabilizer C Q
  have hmul := (MulAction.stabilizer C Q).card_mul_index
  rw [hidx, hstabcard] at hmul
  rw [← hmul, mul_comm]
  exact Nat.mul_le_mul_right _ horb

theorem card_eq_card_ker_mul_card_map {Y S : Type*} [Group Y] [Group S] (f : Y →* S)
    (H : Subgroup Y) : Nat.card H = Nat.card (f.ker.subgroupOf H) * Nat.card (H.map f) := by
  have h := (f.domRestrict H).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h
  exact h.symm

theorem card_comap_centralizer_le {Y S : Type*} [Group Y] [Group S] [Finite Y] (f : Y →* S)
    (hker : f.ker = Subgroup.center Y) (y : Y) :
    Nat.card ((Subgroup.centralizer ({f y} : Set S)).comap f) ≤
      Nat.card (Subgroup.center Y) * Nat.card (Subgroup.centralizer ({y} : Set Y)) := by
  set P := (Subgroup.centralizer ({f y} : Set S)).comap f with hPdef
  have hmemZ : ∀ g ∈ P, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.center Y := by
    intro g hg
    rw [← hker, MonoidHom.mem_ker]
    have hg' : f g * f y = f y * f g :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hg)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg']
    group
  let Φ : P →* Subgroup.center Y :=
    { toFun := fun g => ⟨(g : Y) * y * (g : Y)⁻¹ * y⁻¹, hmemZ g g.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        have hz := hmemZ h h.2
        have hg := hmemZ g g.2
        set ch := (h : Y) * y * (h : Y)⁻¹ * y⁻¹ with hch
        set cg := (g : Y) * y * (g : Y)⁻¹ * y⁻¹ with hcg
        have e1 : (h : Y) * y * (h : Y)⁻¹ = ch * y := by rw [hch]; group
        have e2 : (g : Y) * ch = ch * (g : Y) := Subgroup.mem_center_iff.mp hz g
        have e3 : cg * ch = ch * cg := Subgroup.mem_center_iff.mp hz cg
        simp only [Subgroup.coe_mul]
        calc (g : Y) * h * y * ((g : Y) * h)⁻¹ * y⁻¹ = (g : Y) * ((h : Y) * y * (h : Y)⁻¹) *
              (g : Y)⁻¹ * y⁻¹ := by group
          _ = (g : Y) * ch * y * (g : Y)⁻¹ * y⁻¹ := by rw [e1]; group
          _ = ch * cg := by rw [e2, hcg]; group
          _ = cg * ch := e3.symm }
  have hker' : Φ.ker = (Subgroup.centralizer ({y} : Set Y)).subgroupOf P := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 : (g : Y) * y * (g : Y)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : (g : Y) * y * (g : Y)⁻¹ = y := by
        calc (g : Y) * y * (g : Y)⁻¹ = (g : Y) * y * (g : Y)⁻¹ * y⁻¹ * y := by group
          _ = y := by rw [h2, one_mul]
      calc (g : Y) * y = (g : Y) * y * (g : Y)⁻¹ * g := by group
        _ = y * g := by rw [h3]
    · intro h1
      apply Subtype.ext
      change (g : Y) * y * (g : Y)⁻¹ * y⁻¹ = 1
      rw [h1]
      group
  have h1 := Φ.ker.card_mul_index
  rw [Subgroup.index_ker, hker'] at h1
  have h2 : Nat.card ((Subgroup.centralizer ({y} : Set Y)).subgroupOf P) ≤
      Nat.card (Subgroup.centralizer ({y} : Set Y)) := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_le_of_le inf_le_left
  have h3 : Nat.card Φ.range ≤ Nat.card (Subgroup.center Y) := by
    rw [← Subgroup.card_top (G := Subgroup.center Y)]
    exact Subgroup.card_le_of_le le_top
  rw [← h1, mul_comm (Nat.card (Subgroup.center Y))]
  exact Nat.mul_le_mul h2 h3

theorem card_centralizer_le_mul {Y S : Type*} [Group Y] [Group S] [Finite Y] (f : Y →* S)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.center Y) (y : Y) :
    Nat.card (Subgroup.centralizer ({f y} : Set S)) ≤
      Nat.card (Subgroup.center Y) * Nat.card ((Subgroup.centralizer ({y} : Set Y)).map f) := by
  set P := (Subgroup.centralizer ({f y} : Set S)).comap f with hPdef
  set CY := Subgroup.centralizer ({y} : Set Y) with hCYdef
  have hZP : f.ker ≤ P := fun z hz => by
    rw [hPdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact Subgroup.one_mem _
  have hZC : f.ker ≤ CY := fun z hz => by
    rw [hker] at hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hz y).symm
  have hPmap : P.map f = Subgroup.centralizer ({f y} : Set S) :=
    Subgroup.map_comap_eq_self_of_surjective hf _
  have hP := card_eq_card_ker_mul_card_map f P
  have hC := card_eq_card_ker_mul_card_map f CY
  rw [hPmap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv] at hP
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv] at hC
  have hle := card_comap_centralizer_le f hker y
  rw [← hPdef, ← hCYdef, hP, hC, ← hker] at hle
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  rw [← hker]
  have : Nat.card f.ker * Nat.card (Subgroup.centralizer ({f y} : Set S)) ≤
      Nat.card f.ker * (Nat.card f.ker * Nat.card (CY.map f)) := by
    calc Nat.card f.ker * Nat.card (Subgroup.centralizer ({f y} : Set S)) ≤
          Nat.card f.ker * (Nat.card f.ker * Nat.card (CY.map f)) := hle
      _ = _ := rfl
  exact Nat.le_of_mul_le_mul_left this hpos

theorem l2Order228_of_card {S : Type} [Group S] [Finite S] (h13 : ¬ 13 ∣ Nat.card S)
    (h17 : ¬ 17 ∣ Nat.card S) (h1024 : ¬ 1024 ∣ Nat.card S) : L2Order228 S := by
  intro x _
  have hdvd : 3 * Nat.card (Subgroup.centralizer ({x} : Set S)) ∣ 3 * Nat.card S :=
    Nat.mul_dvd_mul_left 3 (Subgroup.card_subgroup_dvd_card _)
  have h13' : ¬ 13 ∣ 3 * Nat.card S := fun h =>
    h13 ((Nat.Coprime.dvd_mul_left (by norm_num)).mp h)
  have h17' : ¬ 17 ∣ 3 * Nat.card S := fun h =>
    h17 ((Nat.Coprime.dvd_mul_left (by norm_num)).mp h)
  have h1024' : ¬ 1024 ∣ 3 * Nat.card S := fun h =>
    h1024 ((Nat.Coprime.dvd_mul_left (by norm_num)).mp h)
  refine ⟨fun m hm he hm2 => ?_, fun h62 => h13' ((show 13 ∣ 62400 by norm_num).trans
    (h62.trans hdvd))⟩
  rw [card_projSL_two m hm] at hm2
  have h2 := hm2.trans hdvd
  have hm10 : m < 10 := by
    by_contra hm10
    exact h1024' ((show 1024 = 2 ^ 10 by norm_num) ▸
      (pow_dvd_pow 2 (show 10 ≤ m by omega)).trans ((Dvd.intro _ rfl).trans h2))
  obtain ⟨r, rfl⟩ := he
  have hr : r < 5 := by omega
  interval_cases r
  · omega
  · rfl
  · exact absurd ((show 17 ∣ 2 ^ (2 + 2) * ((2 ^ (2 + 2)) ^ 2 - 1) by norm_num).trans h2) h17'
  · exact absurd ((show 13 ∣ 2 ^ (3 + 3) * ((2 ^ (3 + 3)) ^ 2 - 1) by norm_num).trans h2) h13'
  · exact absurd ((show 17 ∣ 2 ^ (4 + 4) * ((2 ^ (4 + 4)) ^ 2 - 1) by norm_num).trans h2) h17'

theorem l2Order228_of_centralizer {S : Type} [Group S]
    (h : ∀ x : S, orderOf x = 3 → ¬ 32 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) ∧
      ¬ 17 ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) : L2Order228 S := by
  intro x hx
  obtain ⟨hC32, hC17⟩ := h x hx
  have h32 : ¬ 32 ∣ 3 * Nat.card (Subgroup.centralizer ({x} : Set S)) := fun h32 =>
    hC32 ((Nat.Coprime.dvd_mul_left (by norm_num)).mp h32)
  have h17 : ¬ 17 ∣ 3 * Nat.card (Subgroup.centralizer ({x} : Set S)) := fun h17 =>
    hC17 ((Nat.Coprime.dvd_mul_left (by norm_num)).mp h17)
  refine ⟨fun m hm he hm2 => ?_, fun h62 => h32 ((show 32 ∣ 62400 by norm_num).trans h62)⟩
  rw [card_projSL_two m hm] at hm2
  have h2m := (Dvd.intro _ rfl).trans hm2
  have hm5 : m < 5 := by
    by_contra hm5
    exact h32 ((pow_dvd_pow 2 (show 5 ≤ m by omega)).trans h2m)
  obtain ⟨r, rfl⟩ := he
  have hr : r < 3 := by omega
  interval_cases r
  · omega
  · rfl
  · exact absurd ((show 17 ∣ 2 ^ (2 + 2) * ((2 ^ (2 + 2)) ^ 2 - 1) by norm_num).trans hm2) h17

theorem noL2Normal228_of_threeFive {Y S : Type} [Group Y] [Group S] [Finite Y] (f : Y →* S)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.center Y)
    (hZ3 : Nat.card (Subgroup.center Y) ∣ 3) (hL : L2Order228 S) (h : ThreeFiveData228 S) :
    NoL2Normal228 Y := by
  have : Finite S := Finite.of_surjective f hf
  intro y N Kb m hyZ hy3 hcomm hnorm hKbN ⟨eK⟩ hm he hU
  obtain ⟨hNs, -⟩ := isSimpleGroup_and_card_ne_360 eK hm he hU
  set x := f y with hxdef
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← map_pow, ← MonoidHom.mem_ker, hker]
    exact hy3
  have hx1 : x ≠ 1 := fun h1 => hyZ (hker ▸ MonoidHom.mem_ker.mpr h1)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨hLm, hL62⟩ := hL x hxo
  set CY := Subgroup.centralizer ({y} : Set Y) with hCYdef
  have hNCY : N ≤ CY := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm k hk).symm
  have hCYmap : CY.map f ≤ Subgroup.centralizer ({x} : Set S) := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff, hxdef, ← map_mul, ← map_mul, hg']
  have hCYcard : Nat.card CY = Nat.card (Subgroup.center Y) * Nat.card (CY.map f) := by
    have hZC : f.ker ≤ CY := fun z hz => by
      rw [hker] at hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hz y).symm
    have hC := card_eq_card_ker_mul_card_map f CY
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hker] at hC
  have hNdvd : Nat.card N ∣ 3 * Nat.card (Subgroup.centralizer ({x} : Set S)) := by
    refine (Subgroup.card_dvd_of_le hNCY).trans ?_
    rw [hCYcard]
    exact Nat.mul_dvd_mul hZ3 (Subgroup.card_dvd_of_le hCYmap)
  have hKbdvd : Nat.card Kb ∣ 3 * Nat.card (Subgroup.centralizer ({x} : Set S)) :=
    (Subgroup.card_dvd_of_le hKbN).trans hNdvd
  rw [Nat.card_congr eK.toEquiv] at hKbdvd
  have hm2 : m = 2 := hLm m hm he hKbdvd
  subst hm2
  have hNKb : Kb = N := by
    rcases hU with heq | hU
    · exact heq
    · exfalso
      exact hL62 (Item22Res4Proof.card_of_statedU34 hU ▸ hNdvd)
  subst hNKb
  have hN60 : Nat.card Kb = 60 := by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two 2 (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 5 (G := Kb) (by rw [hN60]; norm_num)
  have hk5 : orderOf (k : Y) = 5 := by rw [Subgroup.orderOf_coe, hk]
  have hZKb : ∀ z ∈ Kb, z ∈ Subgroup.center Y → z = 1 := by
    intro z hzK hzZ
    have hZK : Subgroup.center Kb = ⊥ :=
      Item223CensusProof.center_eq_bot_of_isSimpleGroup (by rw [hN60]; norm_num)
    have : (⟨z, hzK⟩ : Kb) ∈ Subgroup.center Kb := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzZ w)
    rw [hZK, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hfinj : Function.Injective (f.comp Kb.subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hwZ : (w : Y) ∈ Subgroup.center Y := by
      rw [← hker, MonoidHom.mem_ker]
      exact hw
    exact Subtype.ext (hZKb w w.2 hwZ)
  have hNbar : Nat.card (Kb.map f) = 60 := by
    have hrange : Kb.map f = (f.comp Kb.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← hN60]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hfk1 : f k ≠ 1 := by
    intro h1
    have : (f.comp Kb.subtype) k = (f.comp Kb.subtype) 1 := by
      rw [map_one]
      exact h1
    have hk1 := hfinj this
    rw [hk1, orderOf_one] at hk
    norm_num at hk
  have hfk5 : orderOf (f k) = 5 := by
    refine orderOf_eq_prime ?_ hfk1
    rw [← map_pow, ← hk5, pow_orderOf_eq_one, map_one]
  have hQ : Nat.card (Subgroup.zpowers (f k)) = 5 := by rw [Nat.card_zpowers, hfk5]
  have hQN : Subgroup.zpowers (f k) ≤ Kb.map f := Subgroup.zpowers_le.mpr ⟨k, k.2, rfl⟩
  have hnorm' : ∀ c ∈ CY.map f, ∀ n ∈ Kb.map f, c * n * c⁻¹ ∈ Kb.map f := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨n, hn, rfl⟩
    refine ⟨g * n * g⁻¹, hnorm g (Subgroup.mem_centralizer_singleton_iff.mp hg) n hn, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have h6 := card_le_six_mul_card_normalizer hnorm' hNbar hQN hQ
  have h3 := card_centralizer_le_mul f hf hker y
  have hZle : Nat.card (Subgroup.center Y) ≤ 3 := Nat.le_of_dvd (by norm_num) hZ3
  have hsub : Nat.card (CY.map f ⊓ Subgroup.normalizer ((Subgroup.zpowers (f k) :
      Subgroup S) : Set S) : Subgroup S) ≤
      Nat.card (Subgroup.centralizer ({x} : Set S) ⊓ Subgroup.normalizer
        ((Subgroup.zpowers (f k) : Subgroup S) : Set S) : Subgroup S) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hCYmap)
  have hxk : x * f k = f k * x := by
    rw [hxdef, ← map_mul, ← map_mul, hcomm k k.2]
  have hdata := h x (f k) hxo hfk5 hxk
  rw [← hxdef] at h3
  have h3' : Nat.card (Subgroup.centralizer ({x} : Set S)) ≤ 3 * Nat.card (CY.map f) :=
    h3.trans (Nat.mul_le_mul_right _ hZle)
  omega

end Item228CensusProof

end CFSG.RankThree.PartTwo.Sec21
