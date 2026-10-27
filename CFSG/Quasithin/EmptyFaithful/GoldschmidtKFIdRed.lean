module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdCyc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdSub
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.Open CFSG.Quasithin

@[expose] def IdentTable : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → A23List S →
    (∃ Q : Sylow 3 S, ¬ IsCyclic ↥(Q : Subgroup S)) → ∀ w : MulAut S, w * w = 1 →
    ∀ K : Subgroup S, IsSubnormal K (SBd18.fixedSub w) → IsPSL 3 2 1 ↥K →
      IsPSL 3 2 2 S ∨ IsSporadic .J2 S ∨ IsPSL 3 7 1 S

theorem input15338IdentC_of_table (hT : IdentTable) :
    ∀ (L₂ : Type) [Group L₂] [Finite L₂], CFSG.IsQuasisimple L₂ →
      A23List (L₂ ⧸ Subgroup.center L₂) → CFSG.Open.pRank 3 (⊤ : Subgroup L₂) = 2 →
      ∀ v : MulAut L₂, v * v = 1 →
        (∃ Lf : Subgroup L₂, Lf ∈ cComp (SBd18.fixedSub v) ∧ CFSG.IsQuasisimple ↥Lf ∧
          Subgroup.center ↥Lf = ⊥ ∧ IsPSL 3 2 1 (↥Lf ⧸ Subgroup.center ↥Lf)) →
        IsPSL 3 2 2 (L₂ ⧸ Subgroup.center L₂) ∨ IsSporadic .J2 (L₂ ⧸ Subgroup.center L₂) ∨
          IsPSL 3 7 1 (L₂ ⧸ Subgroup.center L₂) := by
  intro L₂ _ _ hq hlist hrk v hv2 ⟨Lf, hLf, hqf, hcen, hPSL⟩
  classical
  have hperf : Group.IsPerfect L₂ := hq.1
  have hS : IsSimpleGroup (L₂ ⧸ Subgroup.center L₂) := hq.2.1
  have hsyl : ∃ Q : Sylow 3 (L₂ ⧸ Subgroup.center L₂),
      ¬ IsCyclic ↥(Q : Subgroup (L₂ ⧸ Subgroup.center L₂)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (⊤ : Subgroup L₂)
    rw [hrk] at hEcard
    exact exists_noncyclic_sylow_quotient (E := E) hE.2 hEcard
  let π : L₂ →* L₂ ⧸ Subgroup.center L₂ := QuotientGroup.mk' (Subgroup.center L₂)
  let w : MulAut (L₂ ⧸ Subgroup.center L₂) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L₂ v
  have hw2 : w * w = 1 := by rw [← map_mul, hv2, map_one]
  have hsub : IsSubnormal (Lf.map π) (SBd18.fixedSub w) :=
    isSubnormal_map_fixedSub v (subnormal_of_mem_cComp hLf)
  have hinj : Function.Injective (π.comp Lf.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxZ : (x : L₂) ∈ Subgroup.center L₂ :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hxc : x ∈ Subgroup.center ↥Lf := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ y)
    rw [hcen, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr hxc
  let e : ↥Lf ≃* ↥(Lf.map π) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  have hPSL' : IsPSL 3 2 1 ↥Lf := by
    have e0 : ↥Lf ≃* (↥Lf ⧸ Subgroup.center ↥Lf) :=
      MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥Lf))
        ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen],
          QuotientGroup.mk'_surjective _⟩
    exact IsPSL.of_mulEquiv e0.symm hPSL
  exact hT _ hS hq.2.2 hlist hsyl w hw2 (Lf.map π) hsub (IsPSL.of_mulEquiv e hPSL')

end CFSG.Quasithin.SBd19F
