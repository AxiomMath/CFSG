module

public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import Certificates.Certificate111604
import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
import CFSG.RankThree.PartTwo.J2Residue.KFactsCommon
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.CentralCover
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native C16

theorem c16_spec :
    eqA 315 (compA 315 (wordArr cWord) Sec4.Sporadic.J2.zArr)
        (compA 315 (wordArr x0Word) (wordArr cWord)) = true ∧
      (∀ a ∈ d0, invTab[a]! ∈ d0 ∧ ∀ b ∈ d0, (mulTab[a]!)[b]! ∈ d0) ∧
      (∀ a ∈ d0, eqA 315 (compA 315 eltArrs[a]! (wordArr x0Word))
        (compA 315 (wordArr x0Word) eltArrs[a]!) = true) ∧
      maskBit lamMaskD0 0 = false ∧
      ∀ a ∈ d0, ∀ b ∈ d0, bitAt fRows a b = cobBit lamMaskD0 a b := by
  have h := Certificates.certificate111604
  simp only [c16Check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.not_eq_true', beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem d0_lt {a : ℕ} (ha : a ∈ d0) : a < 128 := by
  simp only [d0, List.mem_cons, List.not_mem_nil, or_false] at ha
  omega

section Model


private noncomputable def x0P : P := ⟨wordPerm x0Word, wordPerm_mem x0Word⟩

private noncomputable def cP : P := ⟨wordPerm cWord, wordPerm_mem cWord⟩


private noncomputable def z0P : P := CFSG.ComponentClassification.J2Cover.Lift.toModels
  Sec4.Sporadic.J2.zJ

private theorem cP_mul_z0P : cP * z0P = x0P * cP := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, z0P,
    CFSG.ComponentClassification.J2Cover.Lift.coe_toModels]
  exact eq_of_eqA (rep_compA (rep_wordArr cWord) Sec4.Sporadic.J2.rep_z)
    (rep_compA (rep_wordArr x0Word) (rep_wordArr cWord)) c16_spec.1

private theorem x0P_eq : x0P = cP * z0P * cP⁻¹ :=
  eq_mul_inv_of_mul_eq cP_mul_z0P.symm

private theorem card_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (g : G) :
    Nat.card (Subgroup.centralizer ({e g} : Set H)) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  symm
  refine Nat.card_congr
    { toFun := fun x => ⟨e x, ?_⟩
      invFun := fun y => ⟨e.symm y, ?_⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply _) }
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 x.2]
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, Subgroup.mem_centralizer_singleton_iff.1 y.2]

private theorem card_centralizer_x0P :
    Nat.card (Subgroup.centralizer ({x0P} : Set P)) = 1080 := by
  rw [x0P_eq, ← MulAut.conj_apply, card_centralizer_mulEquiv, z0P, card_centralizer_mulEquiv]
  exact Sec4.Sporadic.J2.card_centralizer_z


private noncomputable def D0P : Subgroup P where
  carrier := {q | ∃ a ∈ d0, (q : Perm315) = elt a}
  one_mem' := ⟨0, by simp [d0], by rw [elt_zero, OneMemClass.coe_one, OneMemClass.coe_one]⟩
  mul_mem' := by
    rintro q r ⟨a, ha, hq⟩ ⟨b, hb, hr⟩
    refine ⟨(mulTab[a]!)[b]!, (c16_spec.2.1 a ha).2 b hb, ?_⟩
    rw [mulTab_get (d0_lt ha) (d0_lt hb), (mulIdx_spec (d0_lt hb)).2, Subgroup.coe_mul,
      Subgroup.coe_mul, hq, hr]
  inv_mem' := by
    rintro q ⟨a, ha, hq⟩
    refine ⟨invTab[a]!, (c16_spec.2.1 a ha).1, ?_⟩
    rw [invTab_get (d0_lt ha), ← (elt_inv (d0_lt ha)).2, Subgroup.coe_inv, Subgroup.coe_inv, hq]

private theorem mem_D0P {q : P} : q ∈ D0P ↔ ∃ a ∈ d0, (q : Perm315) = elt a := Iff.rfl

private theorem D0P_le_Sp : D0P ≤ Sp := by
  rintro q ⟨a, -, hq⟩
  rw [Subgroup.mem_subgroupOf, hq]
  exact (elt a).2

private theorem D0P_le_centralizer : D0P ≤ Subgroup.centralizer ({x0P} : Set P) := by
  rintro q ⟨a, ha, hq⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hq]
  exact eq_of_eqA (rep_compA (rep_eltArrs (d0_lt ha)) (rep_wordArr x0Word))
    (rep_compA (rep_wordArr x0Word) (rep_eltArrs (d0_lt ha))) (c16_spec.2.2.1 a ha)

private noncomputable def eltD0 (a : {a // a ∈ d0}) : D0P :=
  ⟨incl (elt a), mem_D0P.2 ⟨a, a.2, incl_coe _⟩⟩

private theorem coe_eltD0 (a : {a // a ∈ d0}) : ((eltD0 a : P) : Perm315) = elt a :=
  incl_coe _

private theorem eltD0_injective : Function.Injective eltD0 := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  have h' := congrArg (fun q : D0P => ((q : P) : Perm315)) h
  simp only [coe_eltD0] at h'
  exact Subtype.ext (elt_injective (d0_lt ha) (d0_lt hb) (Subtype.ext h'))

private theorem eltD0_surjective : Function.Surjective eltD0 := by
  rintro ⟨q, hq⟩
  obtain ⟨a, ha, hqa⟩ := mem_D0P.1 hq
  refine ⟨⟨a, ha⟩, Subtype.ext (Subtype.ext ?_)⟩
  rw [coe_eltD0]
  exact hqa.symm

private theorem card_d0 : Nat.card {a // a ∈ d0} = 8 := by
  rw [← Nat.card_congr (Equiv.subtypeEquivRight fun a => List.mem_toFinset (l := d0) (a := a)),
    Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

private theorem card_D0P : Nat.card D0P = 8 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨eltD0_injective, eltD0_surjective⟩), card_d0]

end Model

private theorem zmod_two_ite_xor (x y w : Bool) :
    ((if (x ^^ y ^^ w) then 1 else 0 : ZMod 2)) + (if w then 1 else 0) =
      (if x then 1 else 0) + (if y then 1 else 0) := by
  cases x <;> cases y <;> cases w <;> decide

section Character


private theorem exists_hom_comap_D0P {E : Type*} [Group E] [Finite E] (hE : commutator E = ⊤)
    {π : E →* P} {z : E} (hπ : IsCentralDoubleExt π z) :
    ∃ ψ : D0P.comap π →* Multiplicative (ZMod 2), ∀ hz : z ∈ D0P.comap π, ψ ⟨z, hz⟩ ≠ 1 := by
  obtain ⟨ι, hι, hιz⟩ := CFSG.ComponentClassification.J2Cover.Lift.exists_mulEquiv_RfN hE hπ
  have hle : D0P.comap π ≤ Sp.comap π := Subgroup.comap_mono D0P_le_Sp
  let κ : D0P.comap π → RfN := fun g => ι ⟨g, hle g.2⟩
  have hκ : ∀ g h, κ (g * h) = κ g * κ h := fun g h => by
    rw [← map_mul]
    rfl
  have helt : ∀ g, ∃ a ∈ d0, eS (κ g).snd = elt a := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, hga⟩ := mem_D0P.1 (Subgroup.mem_comap.1 hg)
    exact ⟨a, ha, Subtype.ext (by rw [coe_eS, hι]; exact hga)⟩
  have hlam1 : mk1 lamMaskD0 (1 : S) = 0 := by
    rw [← elt_zero, mk1_elt _ (by norm_num), c16_spec.2.2.2.1]
    rfl
  let ψ : D0P.comap π →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd ((κ g).fst + mk1 lamMaskD0 (eS (κ g).snd))
      map_one' := by
        change Multiplicative.ofAdd ((ι 1).fst + mk1 lamMaskD0 (eS (ι 1).snd)) = 1
        rw [map_one, CocycleExtension.one_fst, CocycleExtension.one_snd, map_one, hlam1,
          add_zero, ofAdd_zero]
      map_mul' := fun g h => by
        obtain ⟨a, ha, hga⟩ := helt g
        obtain ⟨b, hb, hhb⟩ := helt h
        rw [hκ, CocycleExtension.mul_fst, CocycleExtension.mul_snd, map_mul, fN_apply, hga,
          hhb, ← ofAdd_add, ← (mulIdx_spec (d0_lt hb)).2, fCoc, tbl_elt _ (d0_lt ha) (d0_lt hb),
          mk1_elt _ (d0_lt ha), mk1_elt _ (d0_lt hb),
          mk1_elt _ (mulIdx_spec (a := a) (d0_lt hb)).1, c16_spec.2.2.2.2 a ha b hb, cobBit,
          mulTab_get (d0_lt ha) (d0_lt hb)]
        congr 1
        linear_combination zmod_two_ite_xor (maskBit lamMaskD0 a) (maskBit lamMaskD0 b)
          (maskBit lamMaskD0 (mulIdx a b)) }
  refine ⟨ψ, fun hz => ?_⟩
  have h11 : κ ⟨z, hz⟩ = ⟨1, 1⟩ := by
    change ι ⟨z, hle hz⟩ = ⟨1, 1⟩
    rw [show (⟨z, hle hz⟩ : Sp.comap π) = ι.symm ⟨1, 1⟩ from Subtype.ext hιz.symm,
      MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd ((κ ⟨z, hz⟩).fst + mk1 lamMaskD0 (eS (κ ⟨z, hz⟩).snd)) ≠ 1
  rw [h11]
  change Multiplicative.ofAdd (1 + mk1 lamMaskD0 (eS 1)) ≠ 1
  rw [map_one, hlam1, add_zero]
  decide

end Character

private theorem transfer_ne_one {C : Type*} [Group C] {H : Subgroup C} [H.FiniteIndex]
    (hodd : Odd H.index) (ψ : H →* Multiplicative (ZMod 2)) {z : C}
    (hzc : z ∈ Subgroup.center C) (hzH : z ∈ H) (hψ : ψ ⟨z, hzH⟩ ≠ 1) :
    MonoidHom.transfer ψ z ≠ 1 := by
  have key : ∀ (k : ℕ) (g₀ : C), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k :=
    fun k g₀ _ => by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hzc k) g₀, ← mul_assoc,
        inv_mul_cancel, one_mul]
  rw [MonoidHom.transfer_eq_pow ψ z key]
  show ψ ⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ ≠ 1
  rw [show (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : H) = ⟨z, hzH⟩ ^ H.index from
    Subtype.ext (by simp), map_pow]
  obtain ⟨k, hk⟩ := hodd
  have h2 : ∀ w : Multiplicative (ZMod 2), w ^ 2 = 1 := by decide
  rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
  exact hψ

private theorem centralizer_eq_comap {E Q : Type*} [Group E] [Group Q] {π : E →* Q} {z : E}
    (hπ : IsCentralDoubleExt π z) {d : E} (hd : orderOf d = 3) :
    Subgroup.centralizer ({d} : Set E) = (Subgroup.centralizer ({π d} : Set Q)).comap π := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun h => by rw [← map_mul, h, map_mul], fun h => ?_⟩
  have hk : g * d * g⁻¹ * d⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  rw [hπ.ker_eq, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, hn⟩ := hk
  rw [← zpow_mod_orderOf, hπ.orderOf_eq] at hn
  have hn2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hn2 with h0 | h1
  · rw [h0, zpow_zero] at hn
    have : g * d * g⁻¹ = d := by rw [← mul_inv_eq_one, hn]
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [this]
  · exfalso
    rw [h1, zpow_one] at hn
    have hconj : g * d * g⁻¹ = z * d := by rw [hn]; group
    have hcomm : Commute z d := (Subgroup.mem_center_iff.1 hπ.mem_center d).symm
    have h6 : orderOf (z * d) = 6 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hπ.orderOf_eq, hd]; norm_num),
        hπ.orderOf_eq, hd]
    have h3 : orderOf (g * d * g⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hd]
    rw [hconj, h6] at h3
    norm_num at h3

private theorem exists_hom_centralizer_conj {E : Type*} [Group E] {z : E}
    (hzc : z ∈ Subgroup.center E) (g d : E)
    (h : ∃ T : Subgroup.centralizer ({g * d * g⁻¹} : Set E) →* Multiplicative (ZMod 2),
      ∀ hz, T ⟨z, hz⟩ ≠ 1) :
    ∃ T : Subgroup.centralizer ({d} : Set E) →* Multiplicative (ZMod 2), ∀ hz, T ⟨z, hz⟩ ≠ 1 := by
  obtain ⟨T, hT⟩ := h
  have hmem : ∀ x : Subgroup.centralizer ({d} : Set E),
      g * x * g⁻¹ ∈ Subgroup.centralizer ({g * d * g⁻¹} : Set E) := by
    intro x
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x * g⁻¹ * (g * d * g⁻¹) = g * (x * d) * g⁻¹ := by group
      _ = g * (d * x) * g⁻¹ := by rw [hx]
      _ = g * d * g⁻¹ * (g * x * g⁻¹) := by group
  let φ : Subgroup.centralizer ({d} : Set E) →* Subgroup.centralizer ({g * d * g⁻¹} : Set E) :=
    { toFun := fun x => ⟨g * x * g⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨T.comp φ, fun hz => ?_⟩
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_center_iff.1 hzc g, mul_inv_cancel_right]
  have hz' : z ∈ Subgroup.centralizer ({g * d * g⁻¹} : Set E) :=
    Subgroup.center_le_centralizer _ hzc
  have : φ ⟨z, hz⟩ = ⟨z, hz'⟩ := Subtype.ext hgz
  rw [MonoidHom.comp_apply, this]
  exact hT hz'

section Main


private theorem exists_hom_centralizer {E : Type*} [Group E] [Finite E] (hE : commutator E = ⊤)
    {π : E →* P} {z : E} (hπ : IsCentralDoubleExt π z) {d : E} (hd : orderOf d = 3)
    (hdx : Subgroup.centralizer ({π d} : Set P) = Subgroup.centralizer ({x0P} : Set P)) :
    ∃ T : Subgroup.centralizer ({d} : Set E) →* Multiplicative (ZMod 2),
      ∀ hz, T ⟨z, hz⟩ ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_comap_D0P hE hπ
  set K := (Subgroup.centralizer ({x0P} : Set P)).comap π with hK
  have hCK : Subgroup.centralizer ({d} : Set E) = K := by rw [centralizer_eq_comap hπ hd, hdx]
  have hHK : D0P.comap π ≤ K := Subgroup.comap_mono D0P_le_centralizer
  set H := (D0P.comap π).subgroupOf K with hH
  have hidx : H.index = 135 := by
    change (D0P.comap π).relIndex K = 135
    rw [hK, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hπ.surjective]
    have h := Subgroup.relIndex_mul_card (H := D0P) (K := Subgroup.centralizer ({x0P} : Set P))
    rw [inf_of_le_left D0P_le_centralizer, card_D0P, card_centralizer_x0P] at h
    omega
  let ψ' : H →* Multiplicative (ZMod 2) :=
    ψ.comp (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
  have hzD : z ∈ D0P.comap π := by
    rw [Subgroup.mem_comap, hπ.map_z]
    exact D0P.one_mem
  have hzK : z ∈ K := hHK hzD
  have hzc : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hπ.mem_center g)
  have hzH : (⟨z, hzK⟩ : K) ∈ H := hzD
  have hT := transfer_ne_one (by rw [hidx]; decide) ψ' hzc hzH (hψ hzD)
  refine ⟨(MonoidHom.transfer ψ').comp (MulEquiv.subgroupCongr hCK).toMonoidHom, fun hz => ?_⟩
  exact hT

end Main

section Normalize


private theorem exists_sylow_zJ :
    ∃ S : Sylow 3 Sec4.Sporadic.J2.GJ, Sec4.Sporadic.J2.zJ ∈ (S : Subgroup Sec4.Sporadic.J2.GJ) ∧
      (S : Subgroup Sec4.Sporadic.J2.GJ) ≤ Subgroup.centralizer {Sec4.Sporadic.J2.zJ} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Sec4.Sporadic.J2.P3 =
      3 ^ (Nat.card Sec4.Sporadic.J2.GJ).factorization 3 := by
    rw [Sec4.Sporadic.J2.card_P3, Sec4.Sporadic.J2.card_GJ,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  have hz : Sec4.Sporadic.J2.zJ ∈ Sec4.Sporadic.J2.P3 ⊓
      Subgroup.centralizer (Sec4.Sporadic.J2.P3 : Set Sec4.Sporadic.J2.GJ) := by
    rw [Sec4.Sporadic.J2.inf_centralizer_P3, ← Sec4.Sporadic.J2.z_eq]
    exact Subgroup.mem_zpowers _
  refine ⟨Sylow.ofCard _ hcard, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact hz.1
  · rw [Sylow.coe_ofCard]
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hz.2 p hp

private noncomputable def eJ : J2 ≃* P :=
  CFSG.ComponentClassification.J2Cover.nativeEquivP.trans
    CFSG.ComponentClassification.J2Cover.Lift.toModels


private theorem x0P_ne_one : x0P ≠ 1 := by
  rw [x0P_eq, ← MulAut.conj_apply, MulEquiv.map_ne_one_iff, z0P, MulEquiv.map_ne_one_iff]
  exact Sec4.Sporadic.J2.zJ_ne_one

private theorem exists_sylow_x0 :
    ∃ S : Sylow 3 J2, eJ.symm x0P ∈ (S : Subgroup J2) ∧
      (S : Subgroup J2) ≤ Subgroup.centralizer {eJ.symm x0P} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Sec4.Sporadic.J2.GJ →* J2 := eJ.symm.toMonoidHom.comp ((MulAut.conj cP).toMonoidHom.comp
    CFSG.ComponentClassification.J2Cover.Lift.toModels.toMonoidHom)
  have hf : Function.Surjective f := eJ.symm.surjective.comp ((MulAut.conj cP).surjective.comp
    CFSG.ComponentClassification.J2Cover.Lift.toModels.surjective)
  have hfz : f Sec4.Sporadic.J2.zJ = eJ.symm x0P := by
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [x0P_eq, z0P]
  rw [← hfz]
  exact exists_sylow_mem_le_centralizer_map f hf exists_sylow_zJ

end Normalize

private theorem centralizer_inv_singleton {G : Type*} [Group G] (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext k
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor <;> intro h
  · calc k * x = x * (x⁻¹ * k) * x := by group
      _ = x * (k * x⁻¹) * x := by rw [← h]
      _ = x * k := by group
  · calc k * x⁻¹ = x⁻¹ * (x * k) * x⁻¹ := by group
      _ = x⁻¹ * (k * x) * x⁻¹ := by rw [← h]
      _ = x⁻¹ * k := by group

private theorem perfectResidual_le_commutator' (Q : Type*) [Group Q] :
    perfectResidual Q ≤ commutator Q :=
  (iInf_le (fun n : ℕ => derivedSeries Q n) 1).trans (derivedSeries_one Q).le

theorem kJCover_holds :
    KJCover := by
  intro L _ _ hperf Z _ hZc hZ2 hφ d hd hdS
  obtain ⟨φ⟩ := hφ
  obtain ⟨z, hzZ, hz1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left fun h => by
    rw [h, Subgroup.card_bot] at hZ2
    norm_num at hZ2
  have hzord : orderOf z = 2 := by
    have h := Subgroup.orderOf_dvd_natCard Z hzZ
    rw [hZ2] at h
    rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
    · exact absurd (orderOf_eq_one_iff.1 h1) hz1
    · exact h2
  have hZz : Z = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzZ)
      (by rw [hZ2, Nat.card_zpowers, hzord])).symm
  let π : L →* P := (φ.trans eJ).toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπx : ∀ x : L, π x = eJ (φ (x : L ⧸ Z)) := fun _ => rfl
  have hker : π.ker = Subgroup.zpowers z := by
    rw [← hZz]
    ext x
    rw [MonoidHom.mem_ker, hπx, ← MulEquiv.trans_apply, map_eq_one_iff _ (φ.trans eJ).injective,
      QuotientGroup.eq_one_iff]
  have hπ : IsCentralDoubleExt π z :=
    ⟨(φ.trans eJ).surjective.comp (QuotientGroup.mk'_surjective Z), hZc hzZ, hzord, hker⟩
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mk_eq_or_eq_inv hZp φ hd hdS
    (by rw [Ne, MulEquiv.symm_apply_eq, map_one]; exact x0P_ne_one) exists_sylow_x0
  have hC : Subgroup.centralizer ({π (g * d * g⁻¹)} : Set P) =
      Subgroup.centralizer ({x0P} : Set P) := by
    rw [hπx]
    rcases hg with h | h
    · rw [h, MulEquiv.apply_symm_apply]
    · rw [h, map_inv, MulEquiv.apply_symm_apply, centralizer_inv_singleton]
  have hd' : orderOf (g * d * g⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hd]
  obtain ⟨T, hT⟩ := exists_hom_centralizer_conj (hZc hzZ) g d
    (exists_hom_centralizer hperf.commutator_eq_top hπ hd' hC)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxZ, hxR⟩ := Subgroup.mem_inf.1 hx
  rw [hZz, Subgroup.mem_zpowers_iff] at hxZ
  obtain ⟨n, rfl⟩ := hxZ
  rw [← zpow_mod_orderOf, hzord] at hxR ⊢
  have hn2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hn2 with h0 | h1
  · rw [h0, zpow_zero]
  · exfalso
    rw [h1, zpow_one] at hxR
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hxR
    have hyT := Abelianization.commutator_subset_ker T (perfectResidual_le_commutator' _ hy)
    have hy' : y = ⟨z, by rw [← hyz]; exact y.2⟩ := Subtype.ext hyz
    rw [MonoidHom.mem_ker, hy'] at hyT
    exact hT _ hyT

end CFSG.RankThree.PartTwo.J2Residue
