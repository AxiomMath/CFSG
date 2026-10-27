module

public import CFSG.Quasithin.EmptyFaithful.S153MFF
public import CFSG.Quasithin.EmptyFaithful.S153MMod
public import CFSG.Quasithin.EmptyFaithful.S153MSig

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

namespace S153M

section Core

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem kAction_data
    (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (hF : HypF918 T V L V₁ Vp H K) (M' : Subgroup G) (hHK : H = K ⊔ T) (hS : SQTKGroup ↥H)
    (hK0 : conjClosure K T = K)
    (hkerchar : ∀ x : G, x ∈ kerIn M' H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {n : ℕ} (hn3 : 3 ≤ n) (hnodd : Odd n) (hKs : Shape15365 n (E2.star M' H K))
    {W U : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W U))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWN hUN x = 1)
    (hnt : ¬ K.subgroupOf H ≤ (actH hWN hUN).ker)
    (hFF : IsFFModule (actH hWN hUN).range) :
    ∃ ρK : ↥K →* ↥((K.subgroupOf H).map (actH hWN hUN)),
      Function.Surjective ρK ∧
      (∀ k : ↥K, ((ρK k : ↥((K.subgroupOf H).map (actH hWN hUN))) : MulAut ↥(tildeOf W U)) =
        actH hWN hUN (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp) k)) ∧
      (∀ k : ↥K, ρK k = 1 →
        Subgroup.inclusion (le_of_mem_cComp hF.K_cComp) k ∈ (kerIn M' H).subgroupOf H) ∧
      CFSG.IsQuasisimple ↥((K.subgroupOf H).map (actH hWN hUN)) ∧
      S153L.KsCover ↥((K.subgroupOf H).map (actH hWN hUN)) ∧
      FFNatShape ((K.subgroupOf H).map (actH hWN hUN)) ∧
      ffJ (actH hWN hUN).range = (K.subgroupOf H).map (actH hWN hUN) ∧
      ∃ σ : ↥((K.subgroupOf H).map (actH hWN hUN)) →* ↥(E2.star M' H K),
        Function.Surjective σ ∧ σ.ker ≤ Subgroup.center ↥((K.subgroupOf H).map (actH hWN hUN)) ∧
        ∀ k : ↥K, σ (ρK k) = starMapK M' H K (le_of_mem_cComp hF.K_cComp) k := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hsub : IsSubnormal K H := subnormal_of_mem_cComp hF.K_cComp
  have hFE : Fact (IsElemAbelian 2 (tildeOf W U)) := inferInstance
  have hV : ∀ v : ↥(tildeOf W U), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hFE.out.2 v v.2)
  have hKn : (K.subgroupOf H).Normal := normal_subgroupOf_of_le hKH (hK0 ▸ hF.K₀_normal)
  set φ := actH hWN hUN with hφ
  have hq := isQuasisimple_subgroupOf hKH hF.K_quasisimple
  have hQ' : CFSG.pCore 2 ↥H ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine hQ x ?_
    have hx' : x ∈ CFSG.Open.pCore 2 ↥H := hx
    exact Subgroup.mem_map.mpr ⟨x, hx', rfl⟩
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hK0 ▸ le_normalizer_conjClosure K T
  have h2 := exists_two_pow_mem hHK hF.sylow_H.2.1 hTK
  set L' : Subgroup (MulAut ↥(tildeOf W U)) := (K.subgroupOf H).map φ with hL'
  let ρK : ↥K →* ↥L' := (φ.comp (Subgroup.inclusion hKH)).codRestrict L' fun k =>
    ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hρK : Function.Surjective ρK := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hKQ : pCoreOf 2 K ≤ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 hsub
  have hQK : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 H → ρK k = 1 := by
    intro k hk
    apply Subtype.ext
    exact hQ (Subgroup.inclusion hKH k) hk
  have hO2K : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρK k = 1 := fun k hk => hQK k (hKQ hk)
  have hneK : ∃ k : ↥K, ρK k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnt
    rintro _ hx
    obtain ⟨k, hk, rfl⟩ : ∃ k : ↥K, Subgroup.inclusion hKH k = _ := ⟨⟨_, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val (hcon ⟨_, Subgroup.mem_subgroupOf.mp hx⟩)
  have hker := ker_le_kerIn_of_action hKH hsub hF.K_quasisimple ρK hO2K hneK hkerchar
  obtain ⟨σ, hσ, hz, hσρ⟩ := exists_sigma_central_of_action' hKH ρK hρK hker hkerchar hQK
  have hKsC : S153L.KsCover ↥L' :=
    ⟨_, inferInstance, E2.star M' H K, n, σ, hn3, hnodd, hKs, hσ, hz⟩
  obtain ⟨hsh, hJ⟩ := ffLayer_abstract h51 hA21 hS hV φ (K.subgroupOf H) hq hQ' h2 hnt hFF hKsC
  have hqL := (ar_facts φ (K.subgroupOf H) hq hQ' h2 hnt).1
  exact ⟨ρK, hρK, fun k => rfl, hker, hqL, hKsC, hsh, hJ, σ, hσ, hz, hσρ⟩

end Core

end S153M

end CFSG.Quasithin
