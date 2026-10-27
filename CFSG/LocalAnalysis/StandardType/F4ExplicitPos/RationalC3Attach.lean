module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalC3Attach

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.F4ExplicitPos.RationalC3

open scoped Matrix

theorem eq_of_isComponentOf_of_fixed_quasisimple_of_le
    {G : Type*} [Group G] {C M Γ H N K : Subgroup G}
    (hNdef : N = H ⊓ M) (hΓleM : Γ ≤ M) (hNleC : N ≤ C)
    (hNq : CFSG.IsQuasisimple ↥N)
    (hK : CFSG.Assembly.IsComponentOf K C) (hKleH : K ≤ H) (hKleΓ : K ≤ Γ)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hKsub_ne : K.subgroupOf N ≠ ⊥) :
    K = N := by
  have hKleN : K ≤ N := by
    intro x hx
    rw [hNdef]
    exact ⟨hKleH hx, hKleΓ.trans hΓleM hx⟩
  have hKcompN : CFSG.Assembly.IsComponentOf K N := hK.of_le_of_le hKleN hNleC
  have hKsn : (K.subgroupOf N).IsSubnormal :=
    CFSG.Assembly.IsSubnormal.subgroupOf hKcompN.2.1
  have hKq' : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp hKq
  have hKperf : Group.IsPerfect ↥(K.subgroupOf N) := by
    let : Group.IsPerfect ↥K := hKq'.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKleN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKleN).symm.surjective
  have htop : K.subgroupOf N = ⊤ :=
    CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82.eq_top_of_isSubnormal_of_isQuasisimple
      hNq hKsn hKperf hKsub_ne
  have hmap := congrArg (Subgroup.map N.subtype) htop
  rwa [Subgroup.map_subgroupOf_eq_of_le hKleN, Subgroup.map_top,
    Subgroup.range_subtype] at hmap

theorem eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
    {G : Type*} [Group G] {C M Γ H N K : Subgroup G}
    (hNdef : N = H ⊓ M) (hΓleM : Γ ≤ M) (hNleC : N ≤ C)
    (hNq : CFSG.IsQuasisimple ↥N)
    (hK : CFSG.Assembly.IsComponentOf K C) (hKleH : K ≤ H) (hKleΓ : K ≤ Γ)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K) :
    K = N := by
  have hKleN : K ≤ N := by
    intro x hx
    rw [hNdef]
    exact ⟨hKleH hx, hKleΓ.trans hΓleM hx⟩
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hq' : CFSG.IsQuasisimple ↥K :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp hKq
    obtain ⟨a, b, hab⟩ := hq'.2.2
    have : Subsingleton ↥K := by rw [hbot]; infer_instance
    exact hab (by rw [Subsingleton.elim a b])
  have hKsub_ne : K.subgroupOf N ≠ ⊥ := by
    intro hbot
    apply hKne
    have hmap := congrArg (Subgroup.map N.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hKleN, Subgroup.map_bot] at hmap
  exact eq_of_isComponentOf_of_fixed_quasisimple_of_le hNdef hΓleM hNleC hNq hK hKleH hKleΓ
    hKq hKsub_ne

section Actual

theorem component_eq_range_Phi_of_le_cent
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra K Ω]
    (D : LangDatum Tag.F4 Ω) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (n z : ModGL Tag.F4 Ω) (hn_adj : n ∈ adjointGroup Tag.F4 Ω)
    (hz_adj : z ∈ adjointGroup Tag.F4 Ω)
    (hn : bcGL (τ := Tag.F4) Fr n = n)
    (hzH : ∀ g, g ∈ MonoidHom.range (conjIM Ω n) ↔
      z * g * z⁻¹ ∈ MonoidHom.range (conjIM Ω n))
    (hzF : ∀ g ∈ MonoidHom.range (conjIM Ω n),
      D.step (z * g * z⁻¹) = z * bcGL (τ := Tag.F4) Fr g * z⁻¹)
    {C Ccent : Subgroup (ModGL Tag.F4 Ω)} (hC : C = D.Γ ⊓ Ccent)
    (hHcent : MonoidHom.range (conjIM Ω n) ≤ Ccent)
    {P : Subgroup (ModGL Tag.F4 Ω)}
    (hP : CFSG.Assembly.IsComponentOf P C)
    (hPleH : P ≤ MonoidHom.range (conjIM Ω n)) :
    P = MonoidHom.range
      (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3)) := by
  set N : Subgroup (ModGL Tag.F4 Ω) := MonoidHom.range
      (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3)) with hN
  have hrange := CFSG.StandardType.F4ExplicitPos.RationalC3.range_Phi_eq_inf_model (Ω := Ω) (K := K)
    D Fr hFr n z hn_adj hz_adj hn hzH hzF
  have hNdef : N = MonoidHom.range (conjIM Ω n) ⊓ D.model := by
    rw [hN]; exact hrange
  have hNq : CFSG.IsQuasisimple ↥N := by
    rw [hN]
    exact CFSG.StandardType.F4ExplicitPos.RationalC3.isQuasisimple_range_Phi (Ω := Ω) (K := K) n z
  have hperf : Group.IsPerfect ↥N := by
    rw [hN]
    exact CFSG.StandardType.F4ExplicitPos.RationalC3.isPerfect_range_Phi (Ω := Ω) (K := K) n z
  have hNleM : N ≤ D.model := by
    rw [hNdef]; exact inf_le_right
  have hNΓ : N ≤ D.Γ := by
    have : Group.IsPerfect ↥N := hperf
    calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅D.model, D.model⁆ := Subgroup.commutator_mono hNleM hNleM
      _ = D.Γ := rfl
  have hNcent : N ≤ Ccent := by
    rw [hNdef]; exact inf_le_left.trans hHcent
  have hNleC : N ≤ C := by
    rw [hC]; exact le_inf hNΓ hNcent
  have hΓleM : D.Γ ≤ D.model := Subgroup.commutator_le_self D.model
  have hKleΓ : P ≤ D.Γ := by
    have h := hP.1
    rw [hC] at h
    exact h.trans inf_le_left
  have hPN : P = N :=
    eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
      (C := C) (M := D.model) (Γ := D.Γ) (H := MonoidHom.range (conjIM Ω n))
      (N := N) (K := P) hNdef hΓleM hNleC hNq hP hPleH hKleΓ hP.2.2
  exact hPN.trans hN

end Actual

end CFSG.StandardType.F4ExplicitPos.RationalC3Attach

end

end
