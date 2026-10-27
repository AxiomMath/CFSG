module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PLengthOne
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

open Subgroup

public theorem CFSG.isTrivialCompSubtypeOfLeKer {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (N : Subgroup G)
    (hN_le_ker : N ≤ ρ.ker) :
    Representation.IsTrivial (ρ.comp N.subtype) where
  out n := by
    ext v
    have hnker : (n : G) ∈ ρ.ker := hN_le_ker n.property
    rw [MonoidHom.mem_ker] at hnker
    simpa using congrArg (fun f : Module.End F V => f v) hnker

public instance CFSG.instIsTrivialCompSubtypeKer {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    Representation.IsTrivial (ρ.comp ρ.ker.subtype) :=
  isTrivialCompSubtypeOfLeKer (ρ := ρ) (N := ρ.ker) (le_rfl)

public theorem CFSG.fixedSubspace_map_mk'_ofQuotient_eq {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (N R : Subgroup G)
    [N.Normal] [Representation.IsTrivial (ρ.comp N.subtype)] :
    (Representation.ofQuotient ρ N).fixedSubspace (R.map (QuotientGroup.mk' N)) = ρ.fixedSubspace R := by
  ext v
  constructor
  · intro hv
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hv
    rw [Representation.fixedSubspace, Representation.mem_invariants]
    intro r
    have hvr :
        Representation.ofQuotient ρ N ((QuotientGroup.mk' N) r) v = v :=
      hv ⟨(QuotientGroup.mk' N) r, ⟨r, r.property, rfl⟩⟩
    simpa using hvr
  · intro hv
    rw [Representation.fixedSubspace, Representation.mem_invariants]
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hv
    intro x
    have hx : (x : G ⧸ N) ∈ R.map (QuotientGroup.mk' N) := x.property
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨r, hrR, hrx⟩
    have hvr : Representation.ofQuotient ρ N ((QuotientGroup.mk' N) r) v = v := by
      simpa using hv ⟨r, hrR⟩
    simpa [hrx] using hvr

public theorem CFSG.ker_ofQuotient_ker_eq_bot {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    (Representation.ofQuotient ρ ρ.ker).ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := ρ.ker) x
  rw [MonoidHom.mem_ker] at hx
  have hgker : g ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    ext v
    have hxv := congrArg (fun f : Module.End F V => f v) hx
    simpa using hxv
  simpa using (QuotientGroup.eq_one_iff (N := ρ.ker) g).2 hgker

public theorem CFSG.fixedSubspace_map_mk'_of_kerRepresentation_eq {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R : Subgroup G) :
    (Theory.Representation.kerRepresentation ρ).fixedSubspace (R.map (QuotientGroup.mk' ρ.ker)) =
      ρ.fixedSubspace R := by
  change (Representation.ofQuotient ρ ρ.ker).fixedSubspace
    (R.map (QuotientGroup.mk' ρ.ker)) = ρ.fixedSubspace R
  exact fixedSubspace_map_mk'_ofQuotient_eq (ρ := ρ) (N := ρ.ker) (R := R)

public theorem CFSG.ker_of_kerRepresentation_eq_bot {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    (Theory.Representation.kerRepresentation ρ).ker = ⊥ := by
  change (Representation.ofQuotient ρ ρ.ker).ker = ⊥
  exact ker_ofQuotient_ker_eq_bot (ρ := ρ)

public theorem CFSG.not_map_le_ker_of_not_le_ker_of_quotient
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (N K : Subgroup G) [N.Normal]
    [Representation.IsTrivial (ρ.comp N.subtype)] (hK : ¬ K ≤ ρ.ker) :
    ¬ K.map (QuotientGroup.mk' N) ≤ (Representation.ofQuotient ρ N).ker := by
  intro hmap
  apply hK
  intro k hkK
  have hqk : QuotientGroup.mk' N k ∈ K.map (QuotientGroup.mk' N) := by
    exact ⟨k, hkK, rfl⟩
  have hkker : QuotientGroup.mk' N k ∈ (Representation.ofQuotient ρ N).ker := hmap hqk
  rw [MonoidHom.mem_ker] at hkker
  rw [MonoidHom.mem_ker]
  ext v
  simpa using congrArg (fun f : Module.End F V => f v) hkker

public theorem CFSG.not_map_le_ker_of_not_le_ker_of_kerRepresentation
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (K : Subgroup G) (hK : ¬ K ≤ ρ.ker) :
    ¬ K.map (QuotientGroup.mk' ρ.ker) ≤ (Theory.Representation.kerRepresentation ρ).ker := by
  change ¬ K.map (QuotientGroup.mk' ρ.ker) ≤ (Representation.ofQuotient ρ ρ.ker).ker
  exact not_map_le_ker_of_not_le_ker_of_quotient
    (ρ := ρ) (N := ρ.ker) (K := K) hK

public theorem CFSG.quotient_representation_data_of_irreducible_not_le_ker_local
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R K : Subgroup G) (hirr : Representation.IsIrreducible ρ)
    (hfixR : ρ.fixedSubspace R = ⊥) (hK_nontrivial : ¬ K ≤ ρ.ker) :
    let ρq := Theory.Representation.kerRepresentation ρ
    Representation.IsIrreducible ρq ∧
      Function.Injective ρq ∧
      ρq.fixedSubspace (R.map (QuotientGroup.mk' ρ.ker)) = ⊥ ∧
      ¬ K.map (QuotientGroup.mk' ρ.ker) ≤ ρq.ker := by
  dsimp
  refine ⟨(Theory.Representation.kerRepresentation_irreducible_iff ρ).2 hirr,
    Theory.Representation.kerRepresentation_faithful ρ, ?_, ?_⟩
  · rw [fixedSubspace_map_mk'_of_kerRepresentation_eq (ρ := ρ) (R := R)]
    exact hfixR
  · exact not_map_le_ker_of_not_le_ker_of_kerRepresentation (ρ := ρ) (K := K) hK_nontrivial

public theorem CFSG.not_isMulCommutative_map_mk'_of_commutator_map_ne_bot
    {G : Type*} [Group G] (K N : Subgroup G) [N.Normal]
    (hC_ne_bot :
      ((commutator (↥K)).map K.subtype).map (QuotientGroup.mk' N) ≠ ⊥) :
    ¬ IsMulCommutative ↥(K.map (QuotientGroup.mk' N)) := by
  intro hcomm
  have hcomm_bot : ⁅K.map (QuotientGroup.mk' N), K.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simpa using
      hcomm.is_comm.comm
        (⟨y, hy⟩ : K.map (QuotientGroup.mk' N))
        (⟨x, hx⟩ : K.map (QuotientGroup.mk' N))
  have hC_eq :
      ((commutator (↥K)).map K.subtype).map (QuotientGroup.mk' N) =
        ⁅K.map (QuotientGroup.mk' N), K.map (QuotientGroup.mk' N)⁆ := by
    rw [Subgroup.map_subtype_commutator, Subgroup.map_commutator]
  exact hC_ne_bot (hC_eq.trans hcomm_bot)

public theorem CFSG.exponent_map_mk'_eq_prime_of_exponent_eq_prime_of_ne_bot
    {G : Type*} [Group G] {q : ℕ} [Fact q.Prime] (K N : Subgroup G) [N.Normal]
    (hexp : Monoid.exponent (↥K) = q) (hKmap_ne_bot : K.map (QuotientGroup.mk' N) ≠ ⊥) :
    Monoid.exponent (↥(K.map (QuotientGroup.mk' N))) = q := by
  let qK : K →* K.map (QuotientGroup.mk' N) :=
    { toFun := fun k => ⟨(QuotientGroup.mk' N) k, ⟨k, k.property, rfl⟩⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp }
  have hqK_surj : Function.Surjective qK := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨k, hkK, rfl⟩
    exact ⟨⟨k, hkK⟩, rfl⟩
  have hdvd :
      Monoid.exponent (↥(K.map (QuotientGroup.mk' N))) ∣ q := by
    simpa [hexp] using (MonoidHom.exponent_dvd (f := qK) hqK_surj)
  have hne_one : Monoid.exponent (↥(K.map (QuotientGroup.mk' N))) ≠ 1 := by
    intro h_exp_one
    have hsubsingleton : Subsingleton ↥(K.map (QuotientGroup.mk' N)) :=
      (Monoid.exp_eq_one_iff (G := ↥(K.map (QuotientGroup.mk' N)))).mp h_exp_one
    have hKmap_bot : K.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hx_one_sub : (⟨x, hx⟩ : K.map (QuotientGroup.mk' N)) = 1 :=
        @Subsingleton.elim _ hsubsingleton _ _
      have hx_one : x = 1 := congrArg Subtype.val hx_one_sub
      simp [hx_one]
    exact hKmap_ne_bot hKmap_bot
  rcases (Nat.dvd_prime Fact.out).mp hdvd with h_exp_one | h_exp_q
  · exact False.elim (hne_one h_exp_one)
  · exact h_exp_q

public theorem CFSG.commutator_le_centralizerIn_of_map_le_centralizerIn_ofQuotient {G : Type*}
    [Group G] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (N K R : Subgroup G) [N.Normal] (ρ : Representation F G V)
    [Representation.IsTrivial (ρ.comp N.subtype)]
    (hK_normal : K.Normal)
    (hquot :
      ⁅R.map (QuotientGroup.mk' N), K.map (QuotientGroup.mk' N)⁆ ≤
        (Representation.ofQuotient ρ N).centralizerIn (K.map (QuotientGroup.mk' N))) :
    ⁅R, K⁆ ≤ ρ.centralizerIn K := by
  let _ : K.Normal := hK_normal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  intro z hz
  have hzK : z ∈ K := (Subgroup.commutator_le_right (H₁ := R) (H₂ := K)) hz
  have hqz_map : q z ∈ (⁅R, K⁆).map q := ⟨z, hz, rfl⟩
  have hqz : q z ∈ ⁅R.map q, K.map q⁆ := by
    simpa [Subgroup.map_commutator] using hqz_map
  have hzqker : q z ∈ (Representation.ofQuotient ρ N).ker := (hquot hqz).2
  have hzker : z ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hzqker
    ext v
    have hzqv := congrArg (fun f : Module.End F V => f v) hzqker
    simpa [q] using hzqv
  exact ⟨hzK, hzker⟩


public theorem CFSG.fixedSubspace_subgroupOf_eq {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (S R : Subgroup G) (hR_le : R ≤ S) :
    Representation.fixedSubspace (ρ.comp S.subtype) (R.subgroupOf S) =
      Representation.fixedSubspace ρ R := by
  ext v
  rw [Representation.fixedSubspace, Representation.mem_invariants]
  rw [Representation.fixedSubspace, Representation.mem_invariants]
  constructor
  · intro hv r
    simpa using hv ⟨⟨r, hR_le r.2⟩, r.2⟩
  · intro hv r
    simpa using hv ⟨r.1, r.2⟩

public theorem CFSG.centralizerIn_subgroupOf_map_eq {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (S H : Subgroup G) (hH_le : H ≤ S) :
    (Representation.centralizerIn (ρ.comp S.subtype) (H.subgroupOf S)).map S.subtype =
      Representation.centralizerIn ρ H := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Representation.centralizerIn] at hx ⊢
    exact ⟨hx.1, by simpa [MonoidHom.mem_ker] using hx.2⟩
  · intro hz
    rw [Representation.centralizerIn] at hz
    refine ⟨⟨z, hH_le hz.1⟩, ⟨hz.1, ?_⟩, rfl⟩
    simpa [MonoidHom.mem_ker] using hz.2


public theorem CFSG.commutator_le_centralizerIn_of_subgroupOf_eq {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (S H R : Subgroup G) (hH_le : H ≤ S) (hR_le : R ≤ S)
    (hsub :
      ⁅R.subgroupOf S, H.subgroupOf S⁆ ≤
        Representation.centralizerIn (ρ.comp S.subtype) (H.subgroupOf S)) :
    ⁅R, H⁆ ≤ Representation.centralizerIn ρ H := by
  rw [← commutator_subgroupOf_map_eq (S := S) (H := H) (R := R) hH_le hR_le]
  have hmap :
      (⁅R.subgroupOf S, H.subgroupOf S⁆).map S.subtype ≤
        (Representation.centralizerIn (ρ.comp S.subtype) (H.subgroupOf S)).map S.subtype :=
    Subgroup.map_mono hsub
  simpa [centralizerIn_subgroupOf_map_eq (ρ := ρ) (S := S) (H := H) hH_le] using hmap

public theorem CFSG.centralizerIn_eq_bot_of_le_of_centralizerIn_eq_bot {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) {H K : Subgroup G} (hH_le : H ≤ K)
    (hKbot : Representation.centralizerIn ρ K = ⊥) :
    Representation.centralizerIn ρ H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxK : x ∈ Representation.centralizerIn ρ K := by
    exact ⟨hH_le hx.1, hx.2⟩
  rw [hKbot] at hxK
  simpa using hxK

public theorem CFSG.centralizerIn_eq_bot_of_ker_eq_bot {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (H : Subgroup G) (hker : ρ.ker = ⊥) :
    Representation.centralizerIn ρ H = ⊥ := by
  rw [Representation.centralizerIn, hker]
  simp

public theorem CFSG.le_centralizerIn_iff_le_ker {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) {H K : Subgroup G} (hH_le : H ≤ K) :
    H ≤ ρ.centralizerIn K ↔ H ≤ ρ.ker := by
  constructor
  · intro hH_cent h hh
    exact (hH_cent hh).2
  · intro hH_ker h hh
    exact ⟨hH_le hh, hH_ker hh⟩

public theorem CFSG.commutator_le_centralizerIn_iff_le_ker {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R K : Subgroup G) [K.Normal] :
    ⁅R, K⁆ ≤ ρ.centralizerIn K ↔ ⁅R, K⁆ ≤ ρ.ker := by
  exact
    le_centralizerIn_iff_le_ker (ρ := ρ)
      (H := ⁅R, K⁆) (K := K) (Subgroup.commutator_le_right (H₁ := R) (H₂ := K))


set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.le_ker_of_forall_simple_submodule_le_ker {G : Type*} [Group G] {F : Type*}
    [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule] (H : Subgroup G)
    (hsimple :
      ∀ m : Submodule (MonoidAlgebra F G) ρ.asModule, IsSimpleModule (MonoidAlgebra F G) m →
        H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker) :
    H ≤ ρ.ker := by
  classical
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  let v' : ρ.asModule := ρ.asModuleEquiv.symm v
  have hv :
      v' ∈ sSup
        {m : Submodule (MonoidAlgebra F G) ρ.asModule |
          IsSimpleModule (MonoidAlgebra F G) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.mp hv
  have hsfix :
      ∀ s : Finset (Submodule (MonoidAlgebra F G) ρ.asModule),
        ↑s ⊆ {m : Submodule (MonoidAlgebra F G) ρ.asModule |
          IsSimpleModule (MonoidAlgebra F G) m} →
        ∀ x : ρ.asModule, x ∈ ⨆ m ∈ s, m → ρ h (ρ.asModuleEquiv x) = ρ.asModuleEquiv x := by
    intro s hs x hx
    induction s using Finset.induction_on generalizing x with
    | empty =>
        simp at hx
        simp [hx]
    | @insert q t hqt ih =>
        rw [Finset.iSup_insert] at hx
        have hx' : x ∈ q ⊔ ⨆ m ∈ t, m := by
          simpa [hqt] using hx
        obtain ⟨xq, hxq, xt, hxt, rfl⟩ := Submodule.mem_sup.mp hx'
        have hq_simple : IsSimpleModule (MonoidAlgebra F G) q := hs (Finset.mem_insert_self q t)
        have hq_fix : ρ h (ρ.asModuleEquiv xq) = ρ.asModuleEquiv xq := by
          have hhq : h ∈ (Subrepresentation.ofSubmodule' q).toRepresentation.ker :=
            hsimple q hq_simple hh
          rw [MonoidHom.mem_ker] at hhq
          have hhq' := congrArg (fun f => f ⟨xq, hxq⟩) hhq
          have hhq'' := congrArg Subtype.val hhq'
          change ρ h (ρ.asModuleEquiv xq) = ρ.asModuleEquiv xq at hhq''
          exact hhq''
        have ht_fix : ρ h (ρ.asModuleEquiv xt) = ρ.asModuleEquiv xt :=
          ih (by
            intro m hm
            exact hs (Finset.mem_insert_of_mem hm)) xt hxt
        calc
          ρ h (ρ.asModuleEquiv (xq + xt))
              = ρ h (ρ.asModuleEquiv xq + ρ.asModuleEquiv xt) := by simp
          _ = ρ h (ρ.asModuleEquiv xq) + ρ h (ρ.asModuleEquiv xt) := by simp
          _ = ρ.asModuleEquiv xq + ρ.asModuleEquiv xt := by simp [hq_fix, ht_fix]
          _ = ρ.asModuleEquiv (xq + xt) := by simp
  simpa [v'] using hsfix s hs v' hvs

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.exists_simple_submodule_nontrivial_of_not_le_ker {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule] (H : Subgroup G) (hH : ¬ H ≤ ρ.ker) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
      ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  by_contra hcontra
  push Not at hcontra
  exact hH (le_ker_of_forall_simple_submodule_le_ker (ρ := ρ) H hcontra)

public theorem CFSG.fixedSubspace_ofSubmodule'_eq_bot_of_fixedSubspace_eq_bot {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R : Subgroup G)
    (m : Submodule (MonoidAlgebra F G) ρ.asModule) (hfix : ρ.fixedSubspace R = ⊥) :
    (Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  apply Subtype.ext
  have hv' : ((v : m) : V) ∈ ρ.fixedSubspace R := by
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hv ⊢
    intro r
    exact congrArg Subtype.val (hv r)
  rw [hfix] at hv'
  simpa using hv'

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.irreducible_of_ofSubmodule'_simple {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    {m : Submodule (MonoidAlgebra F G) ρ.asModule}
    (hm : IsSimpleModule (MonoidAlgebra F G) m) :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' m).toRepresentation := by
  rw [Subrepresentation.irreducible_iff_isAtom]
  exact
    ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm.isAtom_iff
      (a := m)).2 <| (isSimpleModule_iff_isAtom).1 hm

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.finiteDimensional_of_irreducible_finite_group
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hirr : Representation.IsIrreducible ρ) :
    FiniteDimensional F V := by
  let hSimple : IsSimpleModule (MonoidAlgebra F G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  let hNontrivialV : Nontrivial V :=
    Subrepresentation.irreducible_module_nontrivial (ρ := ρ) (inst := hirr)
  let hNontrivialM : Nontrivial ρ.asModule :=
    @Function.Injective.nontrivial _ _ hNontrivialV ρ.asModuleEquiv.symm
      (LinearEquiv.injective ρ.asModuleEquiv.symm)
  let hFiniteAM : Module.Finite (MonoidAlgebra F G) ρ.asModule := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
    exact @Module.Finite.of_surjective
      (MonoidAlgebra F G) (MonoidAlgebra F G) _ _ _ (MonoidAlgebra F G) ρ.asModule _ _ _ _ _
      (LinearMap.toSpanSingleton (MonoidAlgebra F G) ρ.asModule v)
      ((isSimpleModule_iff_toSpanSingleton_surjective.mp hSimple).2 v hv)
  let hFiniteFM : Module.Finite F ρ.asModule :=
    @Module.Finite.trans F (MonoidAlgebra F G) ρ.asModule
      _ _ _ _ _ _ _ _ hFiniteAM
  exact @Module.Finite.equiv F ρ.asModule V _ _ _ _ _ hFiniteFM
    (ρ.asModuleEquiv : ρ.asModule ≃ₗ[F] V)
