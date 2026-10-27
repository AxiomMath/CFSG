module

public import CFSG.Quasithin.Vol2.Ch10SecA1011E
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch3Sec1Aux
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_centralizer_le_pCoreOf_sup (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) :
    (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤
      pCoreOf 2 (fsuL0 T L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer hHN hx⟩) ?_
  rintro ⟨x, hxH, hxC⟩
  obtain ⟨e, he⟩ := InternalSec.two_of_sup hyp.fsu.sylow.1 (le_fsuM T L) x hxH
  have hxe : x ^ 2 ^ e ∈ pCoreOf 2 (fsuL0 T L) :=
    fsuL0_inf_centralizer_le h37 h38 hyp ⟨he, Subgroup.pow_mem _ hxC _⟩
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hxe⟩
  refine ⟨e + j, Subtype.ext ?_⟩
  have hj' : (x ^ 2 ^ e) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  simpa [pow_add, pow_mul] using hj'

theorem inf_centralizer_eq_sup_inf (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) :
    T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) =
      (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuVM T L I : Set G) :=
  le_antisymm (inf_le_inf_right _ le_sup_right) (le_inf
    ((inf_centralizer_le_pCoreOf_sup h37 h38 hyp).trans (pCoreOf_le_of_sylow hyp.fsu.sylow
      le_sup_right)) inf_le_right)

theorem le_normalizer_inf_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) :
    fsuL0 T L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) := by
  rw [inf_centralizer_eq_sup_inf h37 h38 hyp]
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer hHN hx⟩

theorem inf_centralizer_eq_pCoreOf_of_not_six
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : TmpL6_3_2_2_eight) (hyp : Ch10.Hyp10 G T L I)
    (hnot : ¬ Ch10.Case10_1_1Six T L I) :
    T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) = pCoreOf 2 (fsuL0 T L ⊔ T) := by
  have hVV : fsuV T I = fsuVM T L I := by
    obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
    rcases hc with ⟨-, h⟩ | ⟨-, h, -⟩ | hiii
    · exact h
    · exact h
    · exact absurd (case_six_of h37 h38 hyp hiii) hnot
  obtain ⟨-, -, h⟩ := h3228 G T L I hyp.fsu
  rw [h, hVV]

theorem isUniqueM_of_le {X Y M : Subgroup G} (hU : IsUniqueM Y M) (hYX : Y ≤ X)
    (hX : pCoreOf 2 X ≠ ⊥) : IsUniqueM X M := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hX
  have hM : M' = M := hU.2 M' ⟨hM'.1, hYX.trans hM'.2⟩
  subst hM
  exact ⟨hM', fun M'' hM'' => hU.2 M'' ⟨hM''.1, hYX.trans hM''.2⟩⟩

omit [Finite G] in
theorem pCoreOf_normalizer_ne_bot {C : Subgroup G} (hC : IsPGroup 2 ↥C) (hC1 : C ≠ ⊥) :
    pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  apply hC1
  have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hC
  rw [h] at this
  exact le_bot_iff.mp this

theorem isPGroup_inf_centralizer (hyp : Ch10.Hyp10 G T L I) :
    IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ∧
      T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≠ ⊥ := by
  refine ⟨hyp.fsu.sylow.1.to_le inf_le_left, fun h => fsuVM_ne_bot hyp.fsu ?_⟩
  have hab := (isElemAbelian_fsuVM hyp).1
  refine le_bot_iff.mp (h ▸ le_inf (fsuVM_le_T hyp) fun v hv => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (hab.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem isUniqueM_normalizer_inf_centralizer (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) :
    IsUniqueM (Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G)) (fsuM T L) ∧
      IsUniqueM (Subgroup.normalizer
        (thompsonJ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) : Set G)) (fsuM T L) := by
  have hU := SecB.isUniqueM_L0T h331 hyp
  have hN := le_normalizer_inf_centralizer h37 h38 hyp
  obtain ⟨hC2, hC1⟩ := isPGroup_inf_centralizer hyp
  refine ⟨isUniqueM_of_le hU hN (pCoreOf_normalizer_ne_bot hC2 hC1), ?_⟩
  refine isUniqueM_of_le hU (hN.trans (normalizer_le_normalizer_thompsonJ _))
    (pCoreOf_normalizer_ne_bot (hC2.to_le (thompsonJ_le_self _))
      (thompsonJ_ne_bot_of_isPGroup hC2 hC1))

end CFSG.Quasithin.Vol2.Ch10.SecA
