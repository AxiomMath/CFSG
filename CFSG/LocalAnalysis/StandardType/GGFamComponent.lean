module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGLangFamily

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem famComp_ringChar_ne_of_pow_eq_one {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type}
    [Field L] {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) : ringChar L ≠ p := by
  intro hc
  haveI : CharP L p := ringChar.of_eq hc
  haveI : Fact p.Prime := ⟨hp⟩
  apply h1
  have ha : a = 1 := by
    funext j
    have h : ((a j : L) - 1) ^ p = 0 := by
      rw [sub_pow_char, one_pow, sub_eq_zero]
      simpa using congrArg (fun u : Lˣ => (u : L)) (hap j)
    have h' : (a j : L) - 1 = 0 := pow_eq_zero_iff hp.ne_zero |>.1 h
    exact Units.ext (sub_eq_zero.1 h')
  rw [ha]
  exact rootDiagUnit_one

private theorem famComp_natCast_ne_zero_of_ringChar_ne {p : ℕ} (hp : p.Prime) {L : Type}
    [Field L] (h : ringChar L ≠ p) : ((p : ℕ) : L) ≠ 0 := by
  intro h'
  have hd : ringChar L ∣ p := (ringChar.spec L p).1 (by exact_mod_cast h')
  rcases (Nat.dvd_prime hp).1 hd with h'' | h''
  · exact CharP.ringChar_ne_one h''
  · exact h h''

theorem famComp_iterate_mem_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hker _ ih

theorem famComp_rationalRootsM_subset_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    rationalRootsM ρ χ i ⊆ kernelRoots χ := by
  rintro γ ⟨k, δ, hδ, rfl⟩
  exact famComp_iterate_mem_kernelRoots hker k hδ.1

private theorem famComp_exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

theorem exists_eq_rationalComponentM_of_isComponentOf_gen
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (hTame : ∀ i : KernelComponent (famCharHom a),
      CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
        Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i))
    {J : Subgroup (ModGL τ L)}
    (hJ : IsComponentOf J
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))) :
    ∃ i : KernelComponent (famCharHom a),
      J = rationalComponentM S.ρ S.Γ (famCharHom a) i ∧
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  obtain ⟨u₀, hu₀⟩ := h1
  have hℓp : ringChar L ≠ p :=
    famComp_ringChar_ne_of_pow_eq_one hp (fun j => hap u₀ j) hu₀
  have hpL : ((p : ℕ) : L) ≠ 0 := famComp_natCast_ne_zero_of_ringChar_ne hp hℓp
  obtain ⟨i, hi⟩ := CFSG.StandardType.LangRat.langFamilyComponentsInRootSpan
    τ L p₀ p S hτ hp hp2 hpL ι a hT hap J hJ
  have hker : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hJΓ : J ≤ S.Γ := hJ.1.trans inf_le_left
  have hperfJ : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  have hJspan : J ≤ rationalSpanM S.ρ S.Γ (famCharHom a) i := le_inf hi hJΓ
  have hJR : J ≤ rationalComponentM S.ρ S.Γ (famCharHom a) i := by
    calc J = ⁅J, J⁆ := hperfJ.symm
      _ ≤ ⁅rationalSpanM S.ρ S.Γ (famCharHom a) i,
              rationalSpanM S.ρ S.Γ (famCharHom a) i⁆ :=
            Subgroup.commutator_mono hJspan hJspan
      _ = rationalComponentM S.ρ S.Γ (famCharHom a) i := rfl
  have hcent : rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i) ≤
      Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have hsub : rationalRootsM S.ρ (famCharHom a) i ⊆ rootCharKernel (a u) := by
      intro γ hγ
      obtain ⟨h1', h2'⟩ := (mem_kernelRoots_famChar a).1
        (famComp_rationalRootsM_subset_kernelRoots hker i hγ)
      exact ⟨h1', h2' u⟩
    exact Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer (a u) hsub hx) _ rfl
  have hRC : rationalComponentM S.ρ S.Γ (famCharHom a) i ≤
      S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
    refine (Subgroup.commutator_le_self _).trans ?_
    exact le_inf inf_le_right (inf_le_left.trans hcent)
  have hJC' : CFSG.Assembly.IsSubnormal J
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open J _).2 hJ.2.1
  have hJR' : CFSG.Assembly.IsSubnormal J (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
    have := hJC'.inf (rationalComponentM S.ρ S.Γ (famCharHom a) i)
    rwa [inf_eq_left.2 hJR, inf_eq_right.2 hRC] at this
  have hsubmath : (J.subgroupOf (rationalComponentM S.ρ S.Γ (famCharHom a) i)).IsSubnormal :=
    hJR'.subgroupOf
  rcases hTame i with hRq | hRsolv
  · refine ⟨i, ?_, hRq⟩
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hRq hsubmath with
      htop | hcenter
    · exact le_antisymm hJR (Subgroup.subgroupOf_eq_top.1 htop)
    · exfalso
      obtain ⟨x, y, hxy⟩ := famComp_exists_noncomm_of_isQuasisimple hJ.2.2
      have hcomm : x * y = y * x := Subtype.ext (by
        have h1' : (⟨x, hJR x.2⟩ : ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) ∈
            J.subgroupOf (rationalComponentM S.ρ S.Γ (famCharHom a) i) := x.2
        have h2' := Subgroup.mem_center_iff.1
          (hcenter h1') ⟨y, hJR y.2⟩
        simpa using congrArg Subtype.val h2'.symm)
      exact hxy hcomm
  · exfalso
    have : Nontrivial ↥J := by
      obtain ⟨x, y, hxy⟩ := famComp_exists_noncomm_of_isQuasisimple hJ.2.2
      exact ⟨x, y, fun h => hxy (by rw [h])⟩
    have : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    have : Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) := hRsolv
    have hsolvJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJR)
        (Subgroup.inclusion_injective hJR)
    exact Group.IsPerfect.not_isSolvable ↥J hsolvJ

theorem exists_eq_rationalComponentM_of_isComponentOf
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (hTame : ∀ i : KernelComponent (famCharHom a),
      CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
        Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i))
    {J : Subgroup (ModGL τ L)}
    (hJ : IsComponentOf J
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))) :
    ∃ i : KernelComponent (famCharHom a),
      J = rationalComponentM S.ρ S.Γ (famCharHom a) i ∧
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  exact exists_eq_rationalComponentM_of_isComponentOf_gen S hp (Or.inr hτ) hp2 hT hap h1 hTame hJ

end CFSG.StandardType.TableCRes
