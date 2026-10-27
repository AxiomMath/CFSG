module

public import CFSG.Quasithin.H13.GoldschmidtU43ModOrb
public import CFSG.Quasithin.H13.GoldschmidtU43ModRel
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.GoldschmidtU43ModSimple
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43

@[expose] def Stage2HModel : Prop :=
  ∃ A s u v : ↥(Subgroup.centralizer ({xElt} : Set X₀)), JW13 A s u v ∧
    Subgroup.closure ({A, s, u, v} : Set ↥(Subgroup.centralizer ({xElt} : Set X₀))) = ⊤

@[expose] def Stage2HCard : Prop :=
  Nat.card ↥(Subgroup.centralizer ({xElt} : Set X₀)) = 1152

theorem rels4_lt5 : ∀ r ∈ rels4Codes, ∀ l ∈ r, l.1 < 5 := by
  rw [rels4Codes_eq]
  decide

theorem evalG_rels4_md (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    (hE : invsOK 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) = true)
    (hr : rels4Codes.all (fun w => eqA 820 (evalArr 820 (hGens 820 tabA tabB)
      (invArrs 820 (hGens 820 tabA tabB)) w) (idA 820)) = true) :
    ∀ r ∈ rels4Codes, evalG (gen5 mdA mdS mdU mdV 1) r = 1 := by
  intro r hrm
  have h := List.all_eq_true.1 hr r hrm
  have hrep := rep_hWord h1 hE (rels4_lt5 r hrm)
  have hrid : Rep 820 (idA 820) (psi (1 : X₀)) := by rw [map_one]; exact rep_idA
  exact psi_inj ((eqA_iff hrep hrid).1 h)

theorem comm_md (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    (hc : (List.range 4).all (fun i => eqA 820 (compA 820 (hGens 820 tabA tabB)[i]! tabA)
      (compA 820 tabA (hGens 820 tabA tabB)[i]!)) = true) :
    ∀ i < 4, gen5 mdA mdS mdU mdV 1 i * xElt = xElt * gen5 mdA mdS mdU mdV 1 i := by
  intro i hi
  have h := List.all_eq_true.1 hc i (List.mem_range.2 hi)
  have hr := rep_hGens h1 i (by omega)
  have e := (eqA_iff (rep_compA hr rep_tabA) (rep_compA rep_tabA hr)).1 h
  exact psi_inj (by simpa [map_mul] using e)

theorem card_closure_md_ge
    (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    (hd : derivOK 820 (leftStep 820 (hGens 820 tabA tabB)) 4 (idA 820)
      (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)) 1152 = true)
    (hk : keysNodup (bfsRec (leftStep 820 (hGens 820 tabA tabB)) 4 1200 (idA 820)).L = true) :
    1152 ≤ Nat.card (Subgroup.closure ({mdA, mdS, mdU, mdV} : Set X₀)) := by
  have hgen : ∀ j < 4,
      gen5 mdA mdS mdU mdV 1 j ∈ Subgroup.closure ({mdA, mdS, mdU, mdV} : Set X₀) := by
    intro j hj
    refine Subgroup.subset_closure ?_
    interval_cases j <;> simp [gen5]
  obtain ⟨hsz, -⟩ := derivOK_size hd
  have hex := deriv_sound psi (Subgroup.closure ({mdA, mdS, mdU, mdV} : Set X₀) : Set X₀)
    (leftStep 820 (hGens 820 tabA tabB)) (fun j x => gen5 mdA mdS mdU mdV 1 j * x)
    (one_mem _) (by rw [map_one]; exact rep_idA)
    (fun j hj x hx => Subgroup.mul_mem _ (hgen j hj) hx)
    (fun j hj t x hx => by
      unfold leftStep
      simpa [map_mul] using rep_compA (rep_hGens h1 j (by omega)) hx) hd
  exact card_ge_of_deriv psi (by norm_num) _ hsz hk hex

theorem stage2HModel_of_checks (ho : orbCheck 820 tabA tabB = true)
    (hh : h4Check 820 tabA tabB rels4Codes = true) : Stage2HModel ∧ Stage2HCard := by
  unfold h4Check at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨h1, hE⟩, hc⟩, hr⟩, hd⟩, hk⟩ := hh
  have hcomm := comm_md h1 hc
  have hrels := evalG_rels4_md h1 hE hr
  have hlow := card_closure_md_ge h1 hd hk
  have mem : ∀ i < 4, gen5 mdA mdS mdU mdV 1 i ∈ Subgroup.centralizer ({xElt} : Set X₀) :=
    fun i hi => Subgroup.mem_centralizer_singleton_iff.2 (hcomm i hi)
  let C := Subgroup.centralizer ({xElt} : Set X₀)
  let A : C := ⟨mdA, by simpa [gen5] using mem 0 (by norm_num)⟩
  let S : C := ⟨mdS, by simpa [gen5] using mem 1 (by norm_num)⟩
  let U : C := ⟨mdU, by simpa [gen5] using mem 2 (by norm_num)⟩
  let V : C := ⟨mdV, by simpa [gen5] using mem 3 (by norm_num)⟩
  have key : ∀ i, C.subtype (gen5 A S U V 1 i) = gen5 mdA mdS mdU mdV 1 i := fun i => by
    rw [map_gen5]
    simp [A, S, U, V]
  have hJ : JW13 A S U V := JW13.of_eval_rels4 fun r hrm => by
    have h0 : C.subtype (evalG (gen5 A S U V 1) r) = evalG (gen5 mdA mdS mdU mdV 1) r := by
      rw [map_evalG]
      exact congrArg (fun g => evalG g r) (funext key)
    exact C.subtype_injective (by rw [h0, hrels r hrm, map_one])
  have hmap : (Subgroup.closure ({A, S, U, V} : Set C)).map C.subtype =
      Subgroup.closure ({mdA, mdS, mdU, mdV} : Set X₀) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, A, S, U, V]
  have hcl : Nat.card (Subgroup.closure ({A, S, U, V} : Set C)) =
      Nat.card (Subgroup.closure ({mdA, mdS, mdU, mdV} : Set X₀)) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective C.subtype_injective).symm
  have hle : Nat.card C ≤ 1152 := card_centralizer_le ho
  have hCle : Subgroup.closure ({mdA, mdS, mdU, mdV} : Set X₀) ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [gen5] using mem 0 (by norm_num)
    · simpa [gen5] using mem 1 (by norm_num)
    · simpa [gen5] using mem 2 (by norm_num)
    · simpa [gen5] using mem 3 (by norm_num)
  have hge : 1152 ≤ Nat.card C := hlow.trans (Subgroup.card_le_of_le hCle)
  have htop : Subgroup.closure ({A, S, U, V} : Set C) = ⊤ :=
    Subgroup.eq_top_of_le_card _ (by rw [hcl]; exact hle.trans hlow)
  exact ⟨⟨A, S, U, V, hJ, htop⟩, le_antisymm hle hge⟩

end CFSG.Quasithin.H13.U43
