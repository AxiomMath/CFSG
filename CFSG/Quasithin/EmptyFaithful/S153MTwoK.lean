module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoData
public import CFSG.Quasithin.EmptyFaithful.S153MMod
public import CFSG.Quasithin.EmptyFaithful.S1565L12
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565
open scoped Pointwise commutatorElement

namespace S153M

section TwoK

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem mem_pCore_of_mem_pCoreOf {H : Subgroup G} (x : ↥H) (hx : (x : G) ∈ pCoreOf 2 H) :
    x ∈ CFSG.pCore 2 ↥H := (CFSG.mem_openPCoreOf_iff x).mp hx

omit [Finite G] in
theorem map_conj_subgroupOf {H K : Subgroup G} (hKH : K ≤ H) {t : G} (htH : t ∈ H) :
    (K.subgroupOf H).map (MulAut.conj (⟨t, htH⟩ : ↥H)).toMonoidHom =
      (K.map (MulAut.conj t).toMonoidHom).subgroupOf H := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(k : G), Subgroup.mem_subgroupOf.mp hk, by simp [MulAut.conj_apply]⟩
  · intro hy
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext ?_⟩
    simpa [MulAut.conj_apply] using hky

omit [Finite G] in
theorem sup_map_conj_subgroupOf {H K T : Subgroup G} (hKH : K ≤ H) {t : G} (htH : t ∈ H)
    (hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H)
    (hK₀eq : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj (⟨t, htH⟩ : ↥H)).toMonoidHom =
      (conjClosure K T).subgroupOf H := by
  rw [map_conj_subgroupOf hKH htH, ← Subgroup.subgroupOf_sup hKH hKtH, hK₀eq]

theorem kActionTwo_data (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hF : HypF918 T V L V₁ Vp H K) (M' : Subgroup G) (hS : SQTKGroup ↥H) (hHK : H = K ⊔ T)
    {t : G} (htT : t ∈ T) (hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp H)
    (hK₀eq : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 H)
    (hperm : ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K : Set G))
    (hker : kerIn M' H = pCoreOf 2 H) {n : ℕ} (hn3 : 3 ≤ n) (hnodd : Odd n)
    (hKs : IsPSL 2 2 n ↥(E2.star M' H K) ∨ IsSz n ↥(E2.star M' H K))
    (hB : E2.IsBorelIn (E2.star M' H K) (E2.star M' H (M' ⊓ K)))
    {W U : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf W U))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → actH hWN hUN x = 1)
    (hnt : ¬ (conjClosure K T).subgroupOf H ≤ (actH hWN hUN).ker)
    (hFF : IsFFModule (actH hWN hUN).range) :
    TwoActConcl (actH hWN hUN) (K.subgroupOf H) (⟨t, hF.T_le_H htT⟩ : ↥H) ∧
      ∃ S : Sylow 2 ↥((K.subgroupOf H).map (actH hWN hUN)),
        ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥((K.subgroupOf H).map (actH hWN hUN))) :
            Set ↥((K.subgroupOf H).map (actH hWN hUN))),
          ∃ k : ↥K, (k : G) ∈ M' ∧
            (b : MulAut ↥(tildeOf W U)) =
              actH hWN hUN (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp) k) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  have htH : t ∈ H := hF.T_le_H htT
  have hFE : Fact (IsElemAbelian 2 (tildeOf W U)) := inferInstance
  have hV : ∀ v : ↥(tildeOf W U), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hFE.out.2 v v.2)
  set t' : ↥H := ⟨t, htH⟩ with ht'
  set φ := actH hWN hUN with hφ
  have hmapconj := map_conj_subgroupOf hKH htH
  have hsup : K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom =
      (conjClosure K T).subgroupOf H := by
    rw [hmapconj, ← Subgroup.subgroupOf_sup hKH hKtH, hK₀eq]
  have hqK := isQuasisimple_subgroupOf hKH hF.K_quasisimple
  have hKn : (K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom).Normal := by
    rw [hsup]
    exact normal_subgroupOf_of_le (K := conjClosure K T) hF.K₀_le_H hF.K₀_normal
  have hcomm' : ⁅K.subgroupOf H, (K.subgroupOf H).map (MulAut.conj t').toMonoidHom⁆ ≤
      CFSG.pCore 2 ↥H := by
    rw [hmapconj]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine mem_pCore_of_mem_pCoreOf _ (hcomm ?_)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
  have hQ' : CFSG.pCore 2 ↥H ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine hQ x ?_
    have hx' : x ∈ CFSG.Open.pCore 2 ↥H := hx
    exact Subgroup.mem_map.mpr ⟨x, hx', rfl⟩
  have hTK₀ : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
  have hHK₀ : H = conjClosure K T ⊔ T :=
    le_antisymm (hHK ▸ sup_le_sup_right (le_conjClosure K T) T) hF.K₀T_le_H
  have h2' : ∀ y : ↥H, ∃ e : ℕ, y ^ 2 ^ e ∈
      K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom := by
    intro y
    rw [hsup]
    exact exists_two_pow_mem hHK₀ hF.sylow_H.2.1 hTK₀ y
  have hperm' : ∀ x : ↥H, x ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∨
      t'⁻¹ * x ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro x
    have key : ∀ y : ↥H, (y : G) ∈ Subgroup.normalizer (K : Set G) →
        y ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact Subgroup.mem_normalizer_iff.mp hy (h : G)
    rcases hperm x x.2 with h | h
    · exact Or.inl (key x h)
    · exact Or.inr (key (t'⁻¹ * x) (by simpa [ht'] using h))
  have hnt' : ¬ K.subgroupOf H ⊔ (K.subgroupOf H).map (MulAut.conj t').toMonoidHom ≤ φ.ker := by
    rw [hsup]
    exact hnt
  have hKnt : ¬ K.subgroupOf H ≤ φ.ker := by
    intro h
    apply hnt'
    refine sup_le h ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk1 : φ k = 1 := MonoidHom.mem_ker.mp (h hk)
    rw [MonoidHom.mem_ker]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hk1, mul_one,
      mul_inv_cancel]
  let ρ₁ : ↥K →* ↥((K.subgroupOf H).map φ) :=
    (φ.comp (Subgroup.inclusion hKH)).codRestrict ((K.subgroupOf H).map φ) fun k =>
      ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hρ₁ : Function.Surjective ρ₁ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hne₁ : Nontrivial ↥((K.subgroupOf H).map φ) := by
    by_contra hcon
    have hsub : Subsingleton ↥((K.subgroupOf H).map φ) := not_nontrivial_iff_subsingleton.mp hcon
    apply hKnt
    intro k hk
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val (Subsingleton.elim (⟨φ k, k, hk, rfl⟩ : ↥((K.subgroupOf H).map φ)) 1)
  have hker' : ∀ k : ↥K, Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H → ρ₁ k = 1 := by
    intro k hk
    rw [Subgroup.mem_subgroupOf, hker] at hk
    apply Subtype.ext
    exact hQ _ hk
  obtain ⟨e⟩ := nonempty_mulEquiv_star_of_surjective hKH ρ₁ hρ₁ hker'
    (isSimpleGroup_of_psl2_or_sz hKs)
  have hK : KsCoverTwo ↥((K.subgroupOf H).map φ) :=
    ⟨_, inferInstance, E2.star M' H K, n, e.symm.toMonoidHom, hn3, hnodd, hKs, e.symm.surjective,
      by
        intro x hx
        have h1 : x = 1 := e.symm.injective (by simpa using hx)
        rw [h1]
        exact Subgroup.one_mem _⟩
  refine ⟨twoNat_of_action hA21 h56 hS hV φ (K.subgroupOf H) t' hqK hKn hcomm' hQ' h2' hperm' hnt'
    hFF hK, ?_⟩
  obtain ⟨S, hS'⟩ := exists_sylow_borel_lift hKH ρ₁ hρ₁ hker' (isSimpleGroup_of_psl2_or_sz hKs) hB
  refine ⟨S, fun b hb => ?_⟩
  obtain ⟨k, hkM, hkb⟩ := hS' b hb
  exact ⟨k, hkM, by rw [← hkb]; rfl⟩

end TwoK

end S153M

end CFSG.Quasithin
