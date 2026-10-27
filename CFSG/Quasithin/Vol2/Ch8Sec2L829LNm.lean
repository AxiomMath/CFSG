module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

private theorem l829_subsingleton_of_perfect_solvable {A : Type} [Group A]
    [Group.IsSolvable A] (h : commutator A = ⊤) : Subsingleton A := by
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial A).ne h

private theorem l829_commutator_eq_top_of_surj {A B : Type} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (h : commutator A = ⊤) : commutator B = ⊤ := by
  have key : (commutator A).map f = commutator B := by
    rw [commutator_def A, commutator_def B, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hf]
  rw [← key, h]
  exact Subgroup.map_top_of_surjective f hf

private theorem l829_exists_noncomm {A : Type} [Group A] [Nontrivial A]
    (h : commutator A = ⊤) : ∃ a b : A, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  haveI := Group.isSolvable_of_comm hc
  exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
    (l829_subsingleton_of_perfect_solvable h)

private theorem l829_mk_comm_iff {A : Type} [Group A] (N : Subgroup A) [N.Normal] (a y : A) :
    (QuotientGroup.mk a : A ⧸ N) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk a ↔ a * y * a⁻¹ * y⁻¹ ∈ N := by
  rw [← mul_inv_eq_one, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  simp only [mul_inv_rev, mul_assoc]

private theorem l829_mk_mem_center_iff {A : Type} [Group A] (N : Subgroup A) [N.Normal] (a : A) :
    (QuotientGroup.mk a : A ⧸ N) ∈ Subgroup.center (A ⧸ N) ↔
      ∀ y : A, a * y * a⁻¹ * y⁻¹ ∈ N := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h y
    exact (l829_mk_comm_iff N a y).mp (h (QuotientGroup.mk y)).symm
  · intro h g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    exact ((l829_mk_comm_iff N a y).mpr (h y)).symm

private theorem l829_quotient_comm {A : Type} [Group A] (N : Subgroup A) [N.Normal]
    (h : ∀ a y : A, a * y * a⁻¹ * y⁻¹ ∈ N) (x z : A ⧸ N) : x * z = z * x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  exact (l829_mk_comm_iff N a y).mpr (h a y)

private theorem l829_subgroupOf_normal {G : Type} [Group G] {A N : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (N : Set G)) : (N.subgroupOf A).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hA g.2) (n : G)).mp hn

private theorem l829_inf_subgroupOf_normal {G : Type} [Group G] {A Q : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (Q : Set G)) : ((A ⊓ Q).subgroupOf A).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem g.2 hn1) (A.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.mp (hA g.2) (n : G)).mp hn2⟩

private def l829Cen {G : Type} [Group G] (H Q : Subgroup G)
    (hQ : H ≤ Subgroup.normalizer (Q : Set G)) (k : G) (hk : k ∈ H) : Subgroup G where
  carrier := {x | x ∈ H ∧ k * x * k⁻¹ * x⁻¹ ∈ Q}
  one_mem' := ⟨H.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxQ⟩ ⟨hy, hyQ⟩
    refine ⟨H.mul_mem hx hy, ?_⟩
    have e : k * (x * y) * k⁻¹ * (x * y)⁻¹ =
        (k * x * k⁻¹ * x⁻¹) * (x * (k * y * k⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact Q.mul_mem hxQ ((Subgroup.mem_normalizer_iff.mp (hQ hx) _).mp hyQ)
  inv_mem' := by
    rintro x ⟨hx, hxQ⟩
    refine ⟨H.inv_mem hx, ?_⟩
    have e : k * x⁻¹ * k⁻¹ * x⁻¹⁻¹ = x⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hQ (H.inv_mem hx)) _).mp (Q.inv_mem hxQ)

private theorem l829Cen_mem {G : Type} [Group G] (H Q : Subgroup G)
    (hQ : H ≤ Subgroup.normalizer (Q : Set G)) (k : G) (hk : k ∈ H) (x : G) :
    x ∈ l829Cen H Q hQ k hk ↔ x ∈ H ∧ k * x * k⁻¹ * x⁻¹ ∈ Q :=
  Iff.rfl

private theorem l829_pCoreOf_eq_inf {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hKH : K ≤ H) (hHn : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) :
    pCoreOf 2 K = K ⊓ pCoreOf 2 H := by
  apply le_antisymm
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH) hHn
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
  · exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
      (l829_inf_subgroupOf_normal (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)))
      (IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) inf_le_right)

private theorem l829_mem_kerIn_iff {G : Type} [Group G] [Finite G] {M H K : Subgroup G}
    (hJ : ∀ x : G, x ∈ kerIn M H ↔
      x ∈ K ⊔ pCoreOf 2 H ∧ ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hKH : K ≤ H) (hHn : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {k : G} (hk : k ∈ K) :
    k ∈ kerIn M H ↔ ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
  have hO := l829_pCoreOf_eq_inf hKH hHn
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hkH : k ∈ H := hKH hk
  constructor
  · intro hkJ y hy
    have hcQ := ((hJ k).mp hkJ).2 y (Subgroup.mem_sup_left hy)
    rw [hO]
    exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))
      (K.inv_mem hy), hcQ⟩
  · intro hyO
    rw [hO] at hyO
    have hyQ : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 H := fun y hy =>
      (Subgroup.mem_inf.mp (hyO y hy)).2
    have hS : K ⊔ pCoreOf 2 H ≤ l829Cen H (pCoreOf 2 H) hQn k hkH := by
      refine sup_le (fun y hy => ?_) (fun q hq => ?_)
      · exact (l829Cen_mem H _ hQn k hkH y).mpr ⟨hKH hy, hyQ y hy⟩
      · refine (l829Cen_mem H _ hQn k hkH q).mpr
          ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 H) hq, ?_⟩
        exact (pCoreOf 2 H).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hQn hkH) q).mp hq) ((pCoreOf 2 H).inv_mem hq)
    exact (hJ k).mpr ⟨Subgroup.mem_sup_left hk,
      fun y hy => ((l829Cen_mem H _ hQn k hkH y).mp (hS hy)).2⟩

private theorem l829_mem_pCoreOf_iff {G : Type} [Group G] (K : Subgroup G) (w : ↥K) :
    (w : G) ∈ pCoreOf 2 K ↔ w ∈ CFSG.pCore 2 ↥K :=
  Subgroup.mem_map_iff_mem K.subtype_injective

noncomputable def starHom {G : Type} [Group G] (M H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M H K) :=
  MonoidHom.codRestrict
    ((QuotientGroup.mk' ((kerIn M H).subgroupOf H)).comp (Subgroup.inclusion hKH))
    (E2.star M H K) (fun k => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2))

theorem starHom_surjective {G : Type} [Group G] (M H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starHom M H K hKH) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩

theorem mem_ker_starHom {G : Type} [Group G] (M H K : Subgroup G) (hKH : K ≤ H) (k : ↥K) :
    starHom M H K hKH k = 1 ↔ (k : G) ∈ kerIn M H := by
  have key : (QuotientGroup.mk' ((kerIn M H).subgroupOf H) (Subgroup.inclusion hKH k) :
      E2.StarQuot M H) = 1 ↔ (k : G) ∈ kerIn M H :=
    (QuotientGroup.eq_one_iff _).trans Subgroup.mem_subgroupOf
  exact ⟨fun h => key.mp (congrArg Subtype.val h), fun h => Subtype.ext (key.mpr h)⟩

theorem commutator_top_of_perfect {G : Type} [Group G] {K : Subgroup G} (h : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  have h1 : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [commutator_def, Subgroup.map_commutator, h1]
  exact h

theorem proper_normal_le_ker_of_perfect {K Ks : Type} [Group K] [Group Ks] [Finite K]
    (hperf : commutator K = ⊤) (hs : IsSimpleGroup Ks) (ψ : K →* Ks)
    (hψ : Function.Surjective ψ) (hsolv : Group.IsSolvable ↥ψ.ker) :
    ∀ N : Subgroup K, N.Normal → N ≠ ⊤ → N ≤ ψ.ker := by
  intro N hN hNtop n hn
  haveI : (N.map ψ).Normal := hN.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ψ) with hbot | htop
  · rw [MonoidHom.mem_ker]
    have hmem : ψ n ∈ N.map ψ := Subgroup.mem_map_of_mem ψ hn
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hsup : ∀ g : K, g ∈ N ⊔ ψ.ker := by
      intro g
      have hg : ψ g ∈ N.map ψ := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.mp hg
      have hk : m⁻¹ * g ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel]
      have hgm : m * (m⁻¹ * g) = g := mul_inv_cancel_left m g
      rw [← hgm]
      exact Subgroup.mul_mem_sup hm hk
    have hf : Function.Surjective ((QuotientGroup.mk' N).comp ψ.ker.subtype) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hsup g)
      refine ⟨⟨z, hz⟩, ?_⟩
      show (QuotientGroup.mk z : K ⧸ N) = QuotientGroup.mk (y * z)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul]
    haveI : Group.IsSolvable (K ⧸ N) := Group.isSolvable_of_surjective hf
    have hperfQ : commutator (K ⧸ N) = ⊤ :=
      l829_commutator_eq_top_of_surj (QuotientGroup.mk'_surjective N) hperf
    haveI := l829_subsingleton_of_perfect_solvable hperfQ
    apply hNtop
    rw [eq_top_iff]
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private def l829Quot (A : Type) [Group A] (N : Subgroup A) [N.Normal] :
    A →* (A ⧸ N) ⧸ Subgroup.center (A ⧸ N) :=
  (QuotientGroup.mk' (Subgroup.center (A ⧸ N))).comp (QuotientGroup.mk' N)

private theorem l829Quot_surjective (A : Type) [Group A] (N : Subgroup A) [N.Normal] :
    Function.Surjective (l829Quot A N) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

private theorem l829Quot_eq_one_iff {A : Type} [Group A] (N : Subgroup A) [N.Normal] (k : A) :
    l829Quot A N k = 1 ↔ ∀ y : A, k * y * k⁻¹ * y⁻¹ ∈ N := by
  unfold l829Quot
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact l829_mk_mem_center_iff N k

theorem star_facts_case2 {G : Type} [Group G] [Finite G] {H T M K : Subgroup G}
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hJ : ∀ x : G, x ∈ kerIn M H ↔
      x ∈ K ⊔ pCoreOf 2 H ∧ ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    IsSimpleGroup ↥(E2.star M H K) ∧ (∃ a b : ↥(E2.star M H K), a * b ≠ b * a) ∧
      Group.IsSolvable ↥(K ⊓ kerIn M H) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHn : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
    rw [hHK]
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hK : ∀ {k : G}, k ∈ K → (k ∈ kerIn M H ↔ ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K) :=
    fun {k} hk => l829_mem_kerIn_iff hJ hKH hHn hk
  obtain ⟨hq1, hq2⟩ := hq
  haveI : IsSimpleGroup ((↥K ⧸ CFSG.Open.pCore 2 ↥K) ⧸
      Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K)) := hq2
  have hker_eq : (starHom M H K hKH).ker = (l829Quot ↥K (CFSG.Open.pCore 2 ↥K)).ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, l829Quot_eq_one_iff, mem_ker_starHom, hK k.2]
    constructor
    · intro h y
      exact (l829_mem_pCoreOf_iff K (k * y * k⁻¹ * y⁻¹)).mp (h y y.2)
    · intro h y hy
      exact (l829_mem_pCoreOf_iff K (k * ⟨y, hy⟩ * k⁻¹ * ⟨y, hy⟩⁻¹)).mpr (h ⟨y, hy⟩)
  have hsurjψ : Function.Surjective (l829Quot ↥K (CFSG.Open.pCore 2 ↥K)) :=
    l829Quot_surjective _ _
  have hstar_eq : ↥(E2.star M H K) ≃*
      ((↥K ⧸ CFSG.Open.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K)) :=
    (((QuotientGroup.quotientKerEquivOfSurjective (starHom M H K hKH)
        (starHom_surjective M H K hKH)).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker_eq)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurjψ)
  have hstar_simple : IsSimpleGroup ↥(E2.star M H K) := MulEquiv.isSimpleGroup hstar_eq
  have hnonab : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a := by
    have hpq : commutator ((↥K ⧸ CFSG.Open.pCore 2 ↥K) ⧸
        Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K)) = ⊤ :=
      l829_commutator_eq_top_of_surj (QuotientGroup.mk'_surjective _) hq1
    obtain ⟨a', b', hab⟩ := l829_exists_noncomm hpq
    refine ⟨hstar_eq.symm a', hstar_eq.symm b', fun h => hab ?_⟩
    have := congrArg hstar_eq h
    simpa using this
  have hsolv : Group.IsSolvable ↥(K ⊓ kerIn M H) := by
    have hP2 : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf (K ⊓ kerIn M H)) :=
      IsPGroup.comap_subtype (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    haveI : ((pCoreOf 2 K).subgroupOf (K ⊓ kerIn M H)).Normal :=
      l829_subgroupOf_normal (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    haveI := IsPGroup.isNilpotent hP2
    have hcomm : ∀ a y : ↥(K ⊓ kerIn M H),
        a * y * a⁻¹ * y⁻¹ ∈ (pCoreOf 2 K).subgroupOf (K ⊓ kerIn M H) := by
      intro a y
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp a.2
      exact (hK ha1).mp ha2 _ (Subgroup.mem_inf.mp y.2).1
    haveI : Group.IsSolvable (↥(K ⊓ kerIn M H) ⧸ (pCoreOf 2 K).subgroupOf (K ⊓ kerIn M H)) :=
      Group.isSolvable_of_comm (l829_quotient_comm _ hcomm)
    exact Group.isSolvable_of_subgroup_quotient ((pCoreOf 2 K).subgroupOf (K ⊓ kerIn M H))
  exact ⟨hstar_simple, hnonab, hsolv⟩

theorem solvable_kerIn_case1 {G : Type} [Group G] [Finite G] {H M K : Subgroup G}
    (hJ : kerIn M H = pCoreOf 2 H) : Group.IsSolvable ↥(K ⊓ kerIn M H) := by
  rw [hJ]
  have hp : IsPGroup 2 ↥(K ⊓ pCoreOf 2 H) :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) inf_le_right
  haveI := IsPGroup.isNilpotent hp
  infer_instance

theorem proper_normal_le_ker_star {G : Type} [Group G] [Finite G] {H M K : Subgroup G}
    (hKH : K ≤ H) (hperf : ⁅K, K⁆ = K) (hs : IsSimpleGroup ↥(E2.star M H K))
    (hsolv : Group.IsSolvable ↥(K ⊓ kerIn M H)) :
    ∀ N : Subgroup ↥K, N.Normal → N ≠ ⊤ → N ≤ (starHom M H K hKH).ker := by
  have hinj : Function.Injective (MonoidHom.codRestrict
      (K.subtype.comp (starHom M H K hKH).ker.subtype) (K ⊓ kerIn M H)
      (fun x => Subgroup.mem_inf.mpr
        ⟨x.1.2, (mem_ker_starHom M H K hKH x.1).mp (MonoidHom.mem_ker.mp x.2)⟩)) := by
    intro x y hxy
    have h1 : ((x.1 : ↥K) : G) = ((y.1 : ↥K) : G) :=
      congrArg (fun z : ↥(K ⊓ kerIn M H) => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h1)
  haveI hker : Group.IsSolvable ↥(starHom M H K hKH).ker :=
    Group.isSolvable_of_isSolvable_injective hinj
  exact proper_normal_le_ker_of_perfect (commutator_top_of_perfect hperf) hs
    (starHom M H K hKH) (starHom_surjective M H K hKH) hker

end CFSG.Quasithin.H13.L829N
