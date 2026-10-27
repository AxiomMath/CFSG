module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCasesTools
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofInner
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Y4Core

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem exists_ne_comm_of_isPerfect {Q : Type*} [Group Q] [Nontrivial Q]
    (hQ : Group.IsPerfect Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hbot : commutator Q = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  have htop : commutator Q = ⊤ := hQ.commutator_eq_top
  rw [hbot] at htop
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  exact hx (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top x))

theorem commutator_eq_self_of_inf_eq_bot {Q : Type*} [Group Q] {J K : Subgroup Q} [J.Normal]
    [K.Normal] (hQ : Group.IsPerfect Q) (hsup : J ⊔ K = ⊤) (hinf : J ⊓ K = ⊥) :
    ⁅J, J⁆ = J := by
  refine le_antisymm (Subgroup.commutator_le_left J J) ?_
  have hcomm : ⁅J, K⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf J K)
  have hJK : (J ⊔ K).Normal := Subgroup.sup_normal J K
  have htop : ⁅(⊤ : Subgroup Q), ⊤⁆ = ⊤ := hQ.commutator_eq_top
  have hQJK : ⁅J, J⁆ ⊔ ⁅K, K⁆ = ⊤ := by
    rw [← htop, ← hsup, Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
      Subgroup.commutator_sup_left, hcomm, Subgroup.commutator_comm K J, hcomm, sup_bot_eq,
      bot_sup_eq]
  intro x hx
  have hxtop : x ∈ ⁅J, J⁆ ⊔ ⁅K, K⁆ := hQJK ▸ Subgroup.mem_top x
  have : (⁅K, K⁆ : Subgroup Q).Normal := Subgroup.commutator_normal K K
  rw [Subgroup.mem_sup_of_normal_right] at hxtop
  obtain ⟨a, ha, b, hb, rfl⟩ := hxtop
  have hbJ : b ∈ J := by
    have := mul_mem (inv_mem (Subgroup.commutator_le_left J J ha)) hx
    rwa [inv_mul_cancel_left] at this
  have hbK : b ∈ K := Subgroup.commutator_le_left K K hb
  have hb1 : b = 1 := by
    have : b ∈ J ⊓ K := ⟨hbJ, hbK⟩
    rwa [hinf, Subgroup.mem_bot] at this
  rw [hb1, mul_one]
  exact ha

theorem nonempty_commutator_equiv {P H : Type*} [Group P] [Group H]
    (ψ : P ≃* Multiplicative (ZMod 3) × H) :
    Nonempty (↥(commutator P) ≃* ↥(commutator H)) := by
  set Z := Multiplicative (ZMod 3)
  have h1 : (commutator P).map ψ.toMonoidHom = commutator (Z × H) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.surjective]
  have hZ : ⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact mul_comm y x
  have h2 : commutator (Z × H) = (⊥ : Subgroup Z).prod (commutator H) := by
    rw [commutator_def, show (⊤ : Subgroup (Z × H)) = (⊤ : Subgroup Z).prod (⊤ : Subgroup H) from
      Subgroup.top_prod_top.symm, Subgroup.commutator_prod_prod, hZ, commutator_def]
  have e1 : ↥(commutator P) ≃* ↥(commutator (Z × H)) :=
    ((commutator P).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr h1)
  have e2 : ↥((⊥ : Subgroup Z).prod (commutator H)) ≃* ↥(commutator H) :=
    { toFun := fun x => ⟨(x : Z × H).2, x.2.2⟩
      invFun := fun y => ⟨(1, y), ⟨Subgroup.one_mem _, y.2⟩⟩
      left_inv := fun x => by
        obtain ⟨⟨z, y⟩, hz, hy⟩ := x
        have : z = 1 := (Subgroup.mem_bot).mp hz
        subst this
        rfl
      right_inv := fun y => rfl
      map_mul' := fun x y => rfl }
  exact ⟨(e1.trans (MulEquiv.subgroupCongr h2)).trans e2⟩

theorem good3_of_isZ3PGLThreeAt {M : Type} [Group M] [Finite M] {X J B : Subgroup M}
    (hJX : J ≤ X) (hXJ : X ≤ Subgroup.normalizer (J : Set M)) (hJp : ⁅J, J⁆ = J)
    (hB : IsMulCommutative B) (hBX : B ≤ Subgroup.normalizer (X : Set M)) {p f : ℕ}
    (hZ : Sec14.IsZ3PGLThreeAt ↥(J ⊔ B) p f) : Good3 ↥J := by
  obtain ⟨hab, -⟩ := (⟨KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ, trivial⟩ :
    (∃ a b : ↥(J ⊔ B), a * b ≠ b * a) ∧ True)
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := hZ
  set P := J ⊔ B with hP
  set C : Subgroup M := ⁅P, P⁆ with hC
  have hCX : C ≤ X :=
    (Subgroup.commutator_mono (sup_le_sup_right hJX B) (sup_le_sup_right hJX B)).trans
      (Sec14.commutator_sup_le_of_le_normalizer hB hBX)
  have hJC : J ≤ C := hJp ▸ Subgroup.commutator_mono le_sup_left le_sup_left
  have hmapC : (commutator ↥P).map P.subtype = C := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have eC : ↥C ≃* ↥(commutator ↥P) :=
    (((commutator ↥P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapC)).symm
  obtain ⟨e'⟩ := nonempty_commutator_equiv ψ
  have eCG : ↥C ≃* ↥(commutator (projImage (Sec4.glPi π 3 (p ^ f) K))) := eC.trans e'
  have hJ1 : J ≠ ⊥ := by
    intro hJb
    obtain ⟨a, b, hab'⟩ := hab
    apply hab'
    have hPB : P = B := by rw [hP, hJb, bot_sup_eq]
    have ha : (a : M) ∈ B := hPB ▸ a.2
    have hb : (b : M) ∈ B := hPB ▸ b.2
    have h := congrArg Subtype.val (hB.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact Subtype.ext (by simpa using h)
  have hJn : (J.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr (hCX.trans hXJ)
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hJp' : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJp
  have hJnt : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  set PG := projImage (Sec4.glPi π 3 (p ^ f) K) with hPG
  set PS := projImage (Sec4.slPi π 3 (p ^ f) K) with hPS
  rcases Sec14.Item148PtRes2.solvable_or_simple hK hq with hsol | ⟨hq2, hsimp⟩
  ·
    exfalso
    have hle := Sec14.Item148PtRes2.commutator_projImage_glPi_le (K := K) hπ
    set ι₀ := PG.subtype.comp (commutator ↥PG).subtype with hι₀
    have hmapPG : (commutator ↥PG).map PG.subtype = ⁅PG, PG⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hemb : ∀ x : ↥(commutator ↥PG), ι₀ x ∈ PS := fun x => by
      have hx : ι₀ x ∈ (commutator ↥PG).map PG.subtype := ⟨x.1, x.2, rfl⟩
      exact hle (hmapPG ▸ hx)
    set ι := ι₀.codRestrict PS hemb with hι
    have hι : Function.Injective ι := by
      intro x y h
      have h' : ι₀ x = ι₀ y := by
        have := congrArg (fun z : ↥PS => (z : Matrix.ProjGenLinGroup (Fin 3) K)) h
        simpa [hι] using this
      exact (PG.subtype_injective.comp (commutator ↥PG).subtype_injective) h'
    have : Group.IsSolvable ↥(commutator ↥PG) := Group.isSolvable_of_isSolvable_injective hι
    have : Group.IsSolvable ↥C :=
      Group.isSolvable_of_isSolvable_injective (f := eCG.toMonoidHom) eCG.injective
    have : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJC)
    exact Group.IsPerfect.not_isSolvable ↥J inferInstance
  ·
    have hcomm := Sec13.commutator_projImage_glPi hK hq2
    have hSG : PS ≤ PG := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    have eS : ↥(commutator ↥PG) ≃* ↥PS :=
      (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSG)
    have eCS : ↥C ≃* ↥PS := eCG.trans eS
    have hCs : IsSimpleGroup ↥C := eCS.isSimpleGroup
    have hJCeq : J = C := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.subgroupOf C) with h | h
      · exfalso
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact hJ1 (disjoint_self.mp (h.mono_right hJC))
      · exact le_antisymm hJC (Subgroup.subgroupOf_eq_top.mp h)
    have eJ : ↥J ≃* ↥PS := (MulEquiv.subgroupCongr hJCeq).trans eCS
    have hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup
    obtain ⟨D, -, hD9⟩ := Sec13.exists_elemAbelian_nine_projImage_slPi hK hq
    have h3 : 3 ∣ Nat.card ↥J := by
      rw [Nat.card_congr eJ.toEquiv]
      exact (show 3 ∣ 9 by norm_num).trans (hD9 ▸ Subgroup.card_subgroup_dvd_card D)
    exact good3_of_isSimpleGroup (exists_ne_comm_of_isPerfect hJp') h3

end CFSG.RankThree.PartTwo.Sec15.Y4Core
