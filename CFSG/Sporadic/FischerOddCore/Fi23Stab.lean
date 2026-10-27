module

public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.FischerOddCore.CentralExt
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer

theorem oddCore_centralizer_fi22J
    {u : CFSG.Sporadic.Fi22.J} (hu : u ^ 2 = 1) :
    CFSG.oddCore ↥(Subgroup.centralizer ({u} : Set CFSG.Sporadic.Fi22.J)) = ⊥ := by
  by_cases h1 : u = 1
  · subst h1
    have htop : Subgroup.centralizer ({1} : Set CFSG.Sporadic.Fi22.J) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul]
    have : IsSimpleGroup CFSG.Sporadic.Fi22.J := CFSG.Sporadic.Fi22.isSimpleGroup_J
    have hJ : CFSG.oddCore CFSG.Sporadic.Fi22.J = ⊥ :=
      oddCore_eq_bot_of_isSimpleGroup (by rw [CFSG.Sporadic.Fi22.card_J]; decide)
    exact @oddCore_eq_bot_of_mulEquiv _ inferInstance _ inferInstance
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hJ
  · have hp2 : orderOf ((fi22PJ.symm u : fi22P) : Equiv.Perm (Fin 3510)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hu h1
    have h := CTUC_Fi22_all_involution_fixed_subgroups_odd_core_trivial _
      (fi22P_le_R (fi22PJ.symm u).2) hp2
    have e1 := infCentralizerEquiv fi22P (fi22PJ.symm u).2
    have e2 := @centralizerMulEquiv fi22P CFSG.Sporadic.Fi22.J inferInstance inferInstance fi22PJ
      (fi22PJ.symm u)
    have e3 : ↥(Subgroup.centralizer ({fi22PJ (fi22PJ.symm u)} : Set CFSG.Sporadic.Fi22.J)) ≃*
        ↥(Subgroup.centralizer ({u} : Set CFSG.Sporadic.Fi22.J)) :=
      MulEquiv.subgroupCongr (by rw [MulEquiv.apply_symm_apply])
    exact @oddCore_eq_bot_of_mulEquiv _ inferInstance _ inferInstance ((e1.trans e2).trans e3) h

@[expose] def fi23Kappa :
    Fi23.Cd →* CFSG.Sporadic.Fi22.J :=
  { toFun := fun c => Fi23.quotCenterEquiv (c : Fi23.Cd ⧸ Subgroup.center Fi23.Cd)
    map_one' := by simp
    map_mul' := fun x y => by simp }

theorem fi23Kappa_apply
    (c : Fi23.Cd) :
    fi23Kappa c = Fi23.quotCenterEquiv (c : Fi23.Cd ⧸ Subgroup.center Fi23.Cd) := rfl

theorem fi23Kappa_surjective :
    Function.Surjective fi23Kappa := by
  intro y
  obtain ⟨q, rfl⟩ := Fi23.quotCenterEquiv.surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨c, rfl⟩

theorem ker_fi23Kappa :
    fi23Kappa.ker = Subgroup.center Fi23.Cd := by
  ext x
  rw [MonoidHom.mem_ker, fi23Kappa_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem oddCore_inf_centralizer_conj {G : Type*} [Group G] (g a b : G)
    (h : CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) = ⊥) :
    CFSG.oddCore ↥(Subgroup.centralizer {g * a * g⁻¹} ⊓ Subgroup.centralizer {g * b * g⁻¹}) =
      ⊥ :=
  oddCore_eq_bot_of_mulEquiv (centralizerInfEquiv (MulAut.conj g) a b) h

theorem oddCore_inf_centralizer_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (a b : G) (h : CFSG.oddCore ↥(Subgroup.centralizer {e a} ⊓ Subgroup.centralizer {e b}) = ⊥) :
    CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (centralizerInfEquiv e a b).symm h

theorem oddCore_inf_centralizer_of_central {G : Type*} [Group G] [Finite G] {Q : Type*}
    [Group Q] (M : Subgroup G) (κ : ↥M →* Q) (hκ : Function.Surjective κ)
    (hker : κ.ker ≤ Subgroup.center M) (hcard : Nat.card κ.ker ∣ 2) {s : G} (hs : s ∈ M)
    (hQ : CFSG.oddCore ↥(Subgroup.centralizer ({κ ⟨s, hs⟩} : Set Q)) = ⊥) :
    CFSG.oddCore ↥(M ⊓ Subgroup.centralizer {s}) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (infCentralizerEquiv M hs).symm
    (oddCore_centralizer_eq_bot_of_central κ hκ hker hcard _ hQ)

theorem oddCore_inf_centralizer_J
    {x : Fi23.J} (hx : IsConj Fi23.d x) {s : Fi23.J}
    (hs : s * x = x * s) (hs2 : s ^ 2 = 1) :
    CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {s}) = ⊥ := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  have hs'd : g⁻¹ * s * g ∈ Fi23.Cd := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * s * g * Fi23.d = g⁻¹ * (s * (g * Fi23.d * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * Fi23.d * g⁻¹) * s) * g := by rw [hs]
      _ = Fi23.d * (g⁻¹ * s * g) := by group
  have hu : fi23Kappa ⟨g⁻¹ * s * g, hs'd⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨g⁻¹ * s * g, hs'd⟩ : Fi23.Cd) ^ 2 = 1 := by
      apply Subtype.ext
      change (g⁻¹ * s * g) ^ 2 = 1
      rw [sq, show g⁻¹ * s * g * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g by group, ← sq, hs2]
      group
    rw [this, map_one]
  have h := @oddCore_inf_centralizer_of_central Fi23.J _ _ CFSG.Sporadic.Fi22.J _ Fi23.Cd
    fi23Kappa fi23Kappa_surjective ker_fi23Kappa.le
    (dvd_of_eq (by rw [ker_fi23Kappa, Fi23.card_center_C])) _ hs'd
    (oddCore_centralizer_fi22J hu)
  have h' := oddCore_inf_centralizer_conj g Fi23.d (g⁻¹ * s * g) h
  rwa [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h'

theorem fi23EquivJ_dFi23 : Fi23.fi23EquivJ Fi23.dFi23 = Fi23.d :=
  Fi23.fi23EquivJ.apply_symm_apply Fi23.d

theorem CTUC_Fi23_central_cover_involution_stabilizers_odd_core_trivial :
    (∀ x : Blueprint.NativeSporadic.Fi23, IsConj Fi23.dFi23 x →
      ∀ s ∈ Subgroup.centralizer {x}, orderOf s = 2 →
        CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {s}) = ⊥) ∧
    (∀ s ∈ Subgroup.centralizer {Fi23.dFi23}, orderOf s = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer {Fi23.dFi23} ⊓ Subgroup.centralizer {s}) = ⊥) := by
  have main : ∀ x : Blueprint.NativeSporadic.Fi23, IsConj Fi23.dFi23 x →
      ∀ s ∈ Subgroup.centralizer {x}, orderOf s = 2 →
        CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {s}) = ⊥ := by
    intro x hx s hs hs2
    have hx' : IsConj Fi23.d (Fi23.fi23EquivJ x) := by
      obtain ⟨c, rfl⟩ := isConj_iff.1 hx
      refine isConj_iff.2 ⟨Fi23.fi23EquivJ c, ?_⟩
      rw [map_mul, map_mul, map_inv, fi23EquivJ_dFi23]
    have hsx : Fi23.fi23EquivJ s * Fi23.fi23EquivJ x = Fi23.fi23EquivJ x * Fi23.fi23EquivJ s := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hs]
    have hs2' : Fi23.fi23EquivJ s ^ 2 = 1 := by
      rw [← map_pow, ← hs2, pow_orderOf_eq_one, map_one]
    exact @oddCore_inf_centralizer_of_mulEquiv Blueprint.NativeSporadic.Fi23 Fi23.J
      Units.instGroup inferInstance Fi23.fi23EquivJ x s (oddCore_inf_centralizer_J hx' hsx hs2')
  exact ⟨main, fun s hs hs2 => main _ (IsConj.refl _) s hs hs2⟩

end CFSG.Sporadic.FischerOddCore
