module

public import CFSG.LieType.Ree.TitsSylowLocalSchreier

public noncomputable section

namespace CFSG.Sporadic.SchreierLemmas

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type*} [Group G]

theorem map_centralizer_eq_of_forall_apply_eq {X : Set G} {α : MulAut G}
    (hα : ∀ x ∈ X, α x = x) :
    (Subgroup.centralizer X).map α.toMonoidHom = Subgroup.centralizer X := by
  have key : ∀ β : MulAut G, (∀ x ∈ X, β x = x) → ∀ h ∈ Subgroup.centralizer X,
      β h ∈ Subgroup.centralizer X := fun β hβ h hh => by
    rw [Subgroup.mem_centralizer_iff] at hh ⊢
    intro z hz
    rw [← hβ z hz, ← map_mul, ← map_mul, hh z hz]
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun h hh => key α hα h hh) fun h hh => ?_
  exact ⟨α⁻¹ h, key α⁻¹ (fun x hx => (α.symm_apply_eq).2 (hα x hx).symm) h hh,
    α.apply_symm_apply h⟩

theorem exists_injective_pointwiseFixingAut_restrict {S H K : Subgroup G}
    (hH : ∀ α ∈ pointwiseFixingAut S, H.map α.toMonoidHom = H)
    (hK : ∀ α ∈ pointwiseFixingAut S, K.map α.toMonoidHom = K) (hgen : H ⊔ K = ⊤)
    {U : Subgroup H} {V : Subgroup K} (hU : ∀ u ∈ U, (u : G) ∈ S)
    (hV : ∀ v ∈ V, (v : G) ∈ S) :
    ∃ ρ : pointwiseFixingAut S →* pointwiseFixingAut U × pointwiseFixingAut V,
      Function.Injective ρ := by
  have hC1 : pointwiseFixingAut S ≤ pairAutSubgroup H K := fun α hα => ⟨hH α hα, hK α hα⟩
  have hC2 : pointwiseFixingAut S ≤ pairAutSubgroup K H := fun α hα => ⟨hK α hα, hH α hα⟩
  let ρH : pointwiseFixingAut S →* MulAut H :=
    (pairAutRestrict H K).comp (Subgroup.inclusion hC1)
  let ρK : pointwiseFixingAut S →* MulAut K :=
    (pairAutRestrict K H).comp (Subgroup.inclusion hC2)
  have hmemH : ∀ α, ρH α ∈ pointwiseFixingAut U := fun α u hu => Subtype.ext (α.2 _ (hU u hu))
  have hmemK : ∀ α, ρK α ∈ pointwiseFixingAut V := fun α v hv => Subtype.ext (α.2 _ (hV v hv))
  refine ⟨(ρH.codRestrict _ hmemH).prod (ρK.codRestrict _ hmemK), ?_⟩
  rw [injective_iff_map_eq_one]
  intro α hα1
  have h0 : ρH α = 1 := congrArg Subtype.val (congrArg Prod.fst hα1)
  have h1 : ρK α = 1 := congrArg Subtype.val (congrArg Prod.snd hα1)
  have hle : H ⊔ K ≤ MonoidHom.eqLocus (α : MulAut G).toMonoidHom (MonoidHom.id G) := by
    refine sup_le (fun x hx => ?_) fun x hx => ?_
    · exact congrArg Subtype.val (DFunLike.congr_fun h0 ⟨x, hx⟩)
    · exact congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)
  rw [hgen] at hle
  exact Subtype.ext (MulEquiv.ext fun g => hle (Subgroup.mem_top g))

theorem outer_of_pointwiseFixingAut [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    (Group.IsSolvable (pointwiseFixingAut (S : Subgroup G)) →
      Group.IsSolvable (MulAut (S : Subgroup G)) → Group.IsSolvable (Outer G)) ∧
    (IsPGroup p (pointwiseFixingAut (S : Subgroup G)) →
      IsPGroup p (MulAut (S : Subgroup G)) → IsPGroup p (Outer G)) := by
  classical
  set C := pointwiseFixingAut (S : Subgroup G)
  set R := pairAutSubgroup (S : Subgroup G) (S : Subgroup G)
  have hCR : C ≤ R := fun α hα => ⟨map_eq_of_fixes hα, map_eq_of_fixes hα⟩
  let r := pairAutRestrict (S : Subgroup G) (S : Subgroup G)
  have hker : ∀ α : R, r α = 1 → (α : MulAut G) ∈ C := fun α hα s hs => by
    have h := DFunLike.congr_fun hα (⟨s, hs⟩ : (S : Subgroup G))
    exact congrArg Subtype.val h
  let π : R →* Outer G := (QuotientGroup.mk' (inner G)).comp R.subtype
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) q
    obtain ⟨c, β, hβ, rfl⟩ := exists_conj_mul_mem_pairAutSubgroup S α
    refine ⟨⟨β, hβ⟩, ?_⟩
    change ((β : MulAut G) : Outer G) = ((MulAut.conj c * β : MulAut G) : Outer G)
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := inner G) (MulAut.conj c)).2 ⟨c, rfl⟩, one_mul]
  refine ⟨fun hC hS => ?_, fun hPC hpS => ?_⟩
  · have hRsolv : Group.IsSolvable R := Group.isSolvable_of_ker_le_range
      (Subgroup.inclusion hCR) r fun α hα => ⟨⟨α, hker α hα⟩, rfl⟩
    exact Group.isSolvable_of_surjective hπ
  · have hPR : IsPGroup p R := by
      intro α
      obtain ⟨n, hn⟩ := hpS (r α)
      rw [← map_pow] at hn
      obtain ⟨m, hm⟩ := hPC ⟨_, hker _ hn⟩
      refine ⟨n + m, Subtype.ext ?_⟩
      have hm' := congrArg Subtype.val hm
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hm'
      rw [SubmonoidClass.coe_pow, pow_add, pow_mul, OneMemClass.coe_one]
      exact hm'
    exact hPR.of_surjective π hπ

theorem local_restriction_Schreier_criterion [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (Q : Subgroup G) (hQS : Q ≤ S) (C : Subgroup G)
    (hC : C = Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) : Set G))
    (N : Subgroup G) (hN : N = Subgroup.normalizer (Q : Set G)) (hgen : C ⊔ N = ⊤)
    (hAS : Group.IsSolvable (MulAut (S : Subgroup G)))
    (hCsolv : Group.IsSolvable (pointwiseFixingAut ((S : Subgroup G).subgroupOf C)))
    (hNsolv : Group.IsSolvable (pointwiseFixingAut (Q.subgroupOf N))) :
    Group.IsSolvable (Outer G) := by
  have hZS : ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) ≤ S :=
    Subgroup.map_subtype_le _
  obtain ⟨ρ, hρ⟩ := exists_injective_pointwiseFixingAut_restrict (S := (S : Subgroup G))
    (H := C) (K := N) (U := (S : Subgroup G).subgroupOf C) (V := Q.subgroupOf N)
    (fun α hα => by
      rw [hC]
      exact map_centralizer_eq_of_fixes fun z hz => hα z (hZS hz))
    (fun α hα => by
      rw [hN]
      exact map_normalizer_eq_of_fixes fun q hq => hα q (hQS hq))
    hgen (fun u hu => Subgroup.mem_subgroupOf.1 hu) fun v hv => hQS (Subgroup.mem_subgroupOf.1 hv)
  have : Group.IsSolvable (pointwiseFixingAut (S : Subgroup G)) :=
    Group.isSolvable_of_isSolvable_injective hρ
  exact (outer_of_pointwiseFixingAut S).1 this hAS

theorem two_centralizer_Schreier_criterion [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (C : Subgroup G) (hC : C = Subgroup.centralizer {u})
    (D : Subgroup G) (hD : D = Subgroup.centralizer {v}) (Q R : Subgroup G)
    (hQp : IsPGroup p Q) (hRp : IsPGroup p R) (hQS : Q ≤ S) (hRS : R ≤ S) (hQC : Q ≤ C)
    (hRD : R ≤ D) (hQn : (Q.subgroupOf C).Normal) (hRn : (R.subgroupOf D).Normal)
    (hCQ : C ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hDR : D ⊓ Subgroup.centralizer (R : Set G) ≤ R) (hgen : C ⊔ D = ⊤) :
    IsPGroup p (pointwiseFixingAut (S : Subgroup G)) ∧
    (∀ α β : pointwiseFixingAut (S : Subgroup G), α * β = β * α) ∧
    (Group.IsSolvable (MulAut (S : Subgroup G)) → Group.IsSolvable (Outer G)) ∧
    (IsPGroup p (MulAut (S : Subgroup G)) → IsPGroup p (Outer G)) := by
  obtain ⟨ρ, hρ⟩ := exists_injective_pointwiseFixingAut_restrict (S := (S : Subgroup G))
    (H := C) (K := D) (U := Q.subgroupOf C) (V := R.subgroupOf D)
    (fun α hα => by
      rw [hC]
      exact map_centralizer_eq_of_forall_apply_eq fun x hx =>
        hα x ((Set.mem_singleton_iff.1 hx) ▸ hu))
    (fun α hα => by
      rw [hD]
      exact map_centralizer_eq_of_forall_apply_eq fun x hx =>
        hα x ((Set.mem_singleton_iff.1 hx) ▸ hv))
    hgen (fun x hx => hQS (Subgroup.mem_subgroupOf.1 hx))
    fun x hx => hRS (Subgroup.mem_subgroupOf.1 hx)
  obtain ⟨hPQ, hcommQ⟩ := pointwiseFixingAut_abelian_pGroup (centralizer_subgroupOf_le hQC hCQ)
    (isPGroup_subgroupOf hQC hQp)
  obtain ⟨hPR, hcommR⟩ := pointwiseFixingAut_abelian_pGroup (centralizer_subgroupOf_le hRD hDR)
    (isPGroup_subgroupOf hRD hRp)
  have hPB : IsPGroup p (pointwiseFixingAut (S : Subgroup G)) := by
    refine IsPGroup.of_injective ?_ ρ hρ
    intro x
    obtain ⟨n, hn⟩ := hPQ x.1
    obtain ⟨m, hm⟩ := hPR x.2
    refine ⟨n + m, Prod.ext ?_ ?_⟩
    · rw [Prod.pow_fst, pow_add, pow_mul, hn, one_pow, Prod.fst_one]
    · rw [Prod.pow_snd, pow_add, mul_comm, pow_mul, hm, one_pow, Prod.snd_one]
  have hcommB : ∀ α β : pointwiseFixingAut (S : Subgroup G), α * β = β * α := fun α β =>
    hρ (by rw [map_mul, map_mul]; exact Prod.ext (hcommQ _ _) (hcommR _ _))
  have hsolvB : Group.IsSolvable (pointwiseFixingAut (S : Subgroup G)) :=
    Group.isSolvable_of_comm hcommB
  exact ⟨hPB, hcommB, (outer_of_pointwiseFixingAut S).1 hsolvB,
    (outer_of_pointwiseFixingAut S).2 hPB⟩

end CFSG.Sporadic.SchreierLemmas
