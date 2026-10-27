module

public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Unc25M11
  CFSG.QuasithinUnique.Vol2Native.L239

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

namespace GoldCMaxM11

@[expose] def zM : MG := ga ^ 4

theorem coe_ga_pow (n : ℕ) : (((ga ^ n : MG)) : Equiv.Perm (Fin 11)) = sa ^ n := by
  simp [ga]

theorem coe_zM : ((zM : MG) : Equiv.Perm (Fin 11)) = sa ^ 4 := coe_ga_pow 4

theorem mem_M_of_mem_P0L {q : Equiv.Perm (Fin 11)} (hq : q ∈ P0L) : q ∈ 𝓜 := by
  obtain ⟨i, -, j, -, rfl⟩ := mem_P0L_iff.mp hq
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ sa_mem i) (Subgroup.pow_mem _ sb_mem j)

theorem zM_mem : zM ∈ P0 := mem_P0.mpr (by rw [coe_zM]; decide +kernel)

theorem zM_sq : zM * zM = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_zM]
  show sa ^ 4 * sa ^ 4 = 1
  decide +kernel

theorem zM_ne_one : zM ≠ 1 := by
  intro h
  have := congrArg (fun x : MG => (x : Equiv.Perm (Fin 11))) h
  rw [coe_zM] at this
  exact sa_pow_four_ne this

theorem orderOf_zM : orderOf zM = 2 :=
  orderOf_eq_prime (by rw [sq]; exact zM_sq) zM_ne_one

theorem center_check : P0L.all (fun p => decide ((P0L.all fun q => decide (q * p = p * q)) = true →
    p = 1 ∨ p = sa ^ 4)) = true := by decide +kernel

theorem sb_ne_one : sb ≠ 1 := by decide +kernel

theorem sb_ne_z : sb ≠ sa ^ 4 := by decide +kernel

theorem zM_central : P0L.all (fun p => decide (p * sa ^ 4 = sa ^ 4 * p)) = true := by
  decide +kernel

theorem centerOf_P0 : centerOf P0 = Subgroup.zpowers zM := by
  apply le_antisymm
  · rintro x ⟨hxP, hxc⟩
    have hxL : (x : Equiv.Perm (Fin 11)) ∈ P0L := mem_P0.mp hxP
    have hcomm : (P0L.all fun q => decide (q * (x : Equiv.Perm (Fin 11)) =
        (x : Equiv.Perm (Fin 11)) * q)) = true := by
      refine List.all_eq_true.mpr fun q hq => decide_eq_true ?_
      have hqM : q ∈ 𝓜 := mem_M_of_mem_P0L hq
      have := Subgroup.mem_centralizer_iff.mp hxc ⟨q, hqM⟩ (mem_P0.mpr hq)
      exact congrArg Subtype.val this
    have h := of_decide_eq_true (List.all_eq_true.mp center_check _ hxL) hcomm
    rcases h with h | h
    · have : x = 1 := Subtype.ext h
      rw [this]
      exact Subgroup.one_mem _
    · have : x = zM := Subtype.ext (h.trans coe_zM.symm)
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨zM_mem, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    apply Subtype.ext
    have h := of_decide_eq_true (List.all_eq_true.mp zM_central _ (mem_P0.mp hs))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zM]
    exact h

theorem zM_not_central : ¬ ∀ g : MG, g * zM = zM * g := by
  intro h
  have hb2 : gb * gb = 1 := Subtype.ext sb_sq
  have hb1 : gb ≠ 1 := fun h' => by
    have := congrArg (fun x : MG => (x : Equiv.Perm (Fin 11))) h'
    exact sb_ne_one this
  obtain ⟨g₁, hg₁⟩ := M11Insp.exists_conj zM_sq zM_ne_one
  obtain ⟨g₂, hg₂⟩ := M11Insp.exists_conj hb2 hb1
  have hA : Unc25G2.gA = zM := by
    calc Unc25G2.gA = g₁⁻¹ * (g₁ * Unc25G2.gA * g₁⁻¹) * g₁ := by group
      _ = g₁⁻¹ * zM * g₁ := by rw [hg₁]
      _ = zM := by rw [h g₁⁻¹]; group
  have : gb = zM := by
    calc gb = g₂ * Unc25G2.gA * g₂⁻¹ := hg₂.symm
      _ = g₂ * zM * g₂⁻¹ := by rw [hA]
      _ = zM := by rw [h g₂]; group
  exact sb_ne_z (by
    have := congrArg (fun x : MG => (x : Equiv.Perm (Fin 11))) this
    rwa [coe_zM] at this)

theorem isMaxSubgroupIn_centralizer_zM :
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer ({zM} : Set MG)) := by
  have hne : Subgroup.centralizer ({zM} : Set MG) ≠ ⊤ := by
    intro htop
    refine zM_not_central fun g => ?_
    have : g ∈ Subgroup.centralizer ({zM} : Set MG) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  refine ⟨lt_top_iff_ne_top.mpr hne, fun K hCK _ => ?_⟩
  rcases M11Insp.max_of_equiv (MulEquiv.refl MG) zM_sq zM_ne_one hCK.le with h | h
  · exact h
  · exact absurd h hCK.ne'

end GoldCMaxM11

open GoldCMaxM11 in
theorem centMaxProp_m11 :
    CentMaxProp MG := by
  have hsyl : IsSylowTwoOf P0 ⊤ := isSylowTwoOf_P0
  have hPi : ¬ 2 ∣ P0.index := by
    have h := hsyl.2.2
    rwa [show (P0.subgroupOf ⊤).index = P0.index from Subgroup.relIndex_top_right P0] at h
  exact centMaxProp_of_data hsyl.2.1 hPi orderOf_zM centerOf_P0 isMaxSubgroupIn_centralizer_zM

theorem centMax_m11 (Q : Type)
    [Group Q] [Finite Q] (P : Subgroup Q) (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index)
    (hQ : IsSporadic .M11 Q) (W : Subgroup Q) (hW : W ≤ centerOf P) (hW0 : W ≠ ⊥) :
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q)) := by
  obtain ⟨e⟩ := hQ
  exact (centMaxProp_m11.of_mulEquiv e.symm) P hP2 hPi W hW hW0

end CFSG.Quasithin
