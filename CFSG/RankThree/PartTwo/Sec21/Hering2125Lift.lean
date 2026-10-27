module

public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG

theorem lift_pCore_of_lift {H : Type} [Group H] [Finite H] (Θ : Subgroup H) [Θ.Normal]
    (hcen : ∀ t ∈ Θ, ∀ h : H, t * h = h * t) (U : Subgroup H) :
    ∀ r ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer
        ((U.map (QuotientGroup.mk' Θ) : Subgroup (H ⧸ Θ)) : Set (H ⧸ Θ))),
      (∃ h₀ ∈ Subgroup.centralizer (U : Set H), QuotientGroup.mk' Θ h₀ = r) →
        ∃ x ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set H)),
          QuotientGroup.mk' Θ x = r := by
  intro r hr hex
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Θ with hπ
  set M : Subgroup (H ⧸ Θ) :=
    Subgroup.centralizer ((U.map π : Subgroup (H ⧸ Θ)) : Set (H ⧸ Θ)) with hM
  set R : Subgroup (H ⧸ Θ) := inSubgroup (CFSG.pCore 2) M with hR
  set C : Subgroup H := Subgroup.centralizer (U : Set H) with hC
  have hRM : R ≤ M := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := (CFSG.pCore_isPGroup (p := 2) (G := M)).map M.subtype
  have hMR : M ≤ Subgroup.normalizer (R : Set (H ⧸ Θ)) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 M))
  have hCM : ∀ h ∈ C, π h ∈ M := by
    intro h hh
    rw [hM, Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
    have := Subgroup.mem_centralizer_iff.mp hh u hu
    rw [← map_mul, this, map_mul]
  set T : Subgroup H := C ⊓ R.comap π with hT
  have hΘT : Θ ≤ T := by
    intro t ht
    have htC : t ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro u hu
      exact (hcen t ht u).symm
    have h1 : π t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    refine Subgroup.mem_inf.mpr ⟨htC, ?_⟩
    show π t ∈ R
    rw [h1]
    exact R.one_mem
  have hTC : T ≤ C := inf_le_left
  have hCT : C ≤ Subgroup.normalizer (T : Set H) := by
    have key : ∀ c'' ∈ C, ∀ x ∈ T, c'' * x * c''⁻¹ ∈ T := by
      intro c'' hc'' x hx
      refine ⟨C.mul_mem (C.mul_mem hc'' hx.1) (C.inv_mem hc''), ?_⟩
      show π (c'' * x * c''⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      have h1 : π c'' ∈ Subgroup.normalizer (R : Set (H ⧸ Θ)) := hMR (hCM c'' hc'')
      exact (Subgroup.mem_normalizer_iff.mp h1 _).mp hx.2
    intro c' hc'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key c' hc' x, fun hx => ?_⟩
    have := key c'⁻¹ (C.inv_mem hc') _ hx
    simpa [mul_assoc] using this
  have hTnil : Group.IsNilpotent T := by
    let f : T →* R := (π.comp T.subtype).codRestrict R (fun t => t.2.2)
    have hker : f.ker ≤ Subgroup.center T := by
      intro t ht
      have h1 : π t = 1 := congrArg Subtype.val ht
      have h2 : (t : H) ∈ Θ := by
        have : (t : H) ∈ π.ker := h1
        rwa [hπ, QuotientGroup.ker_mk'] at this
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcen _ h2 g).symm
    have : Group.IsNilpotent R := hR2.isNilpotent
    exact Subgroup.isNilpotent_of_ker_le_center f hker
  haveI : Group.IsNilpotent T := hTnil
  obtain ⟨S₂⟩ : Nonempty (Sylow 2 T) := inferInstance
  have hS₂n : (S₂ : Subgroup T).Normal := inferInstance
  haveI : (S₂ : Subgroup T).Characteristic := Sylow.characteristic_of_normal S₂ hS₂n
  set N : Subgroup H := (S₂ : Subgroup T).map T.subtype with hN
  have hNT : N ≤ T := Subgroup.map_subtype_le _
  have hN2 : IsPGroup 2 N := S₂.isPGroup'.map T.subtype
  have hCN : C ≤ Subgroup.normalizer (N : Set H) :=
    hCT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (S₂ : Subgroup T))
  have hNP : N ≤ inSubgroup (CFSG.pCore 2) C :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hNT.trans hTC) hCN hN2
  have hTΘ : T ≤ Subgroup.normalizer (Θ : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hpow : ∀ t ∈ T, ∃ k : ℕ, t ^ (2 ^ k) ∈ Θ := by
    intro t ht
    obtain ⟨k, hk⟩ := hR2 ⟨π t, ht.2⟩
    refine ⟨k, ?_⟩
    have h1 : π t ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [← map_pow] at h1
    have : t ^ (2 ^ k) ∈ π.ker := h1
    rwa [hπ, QuotientGroup.ker_mk'] at this
  have hcover : T ≤ N ⊔ Θ := Sec6.le_sylow_sup_of_forall_pow_mem hΘT hTΘ hpow S₂
  obtain ⟨h0, hh0C, hh0⟩ := hex
  have hh0T : h0 ∈ T := by
    refine Subgroup.mem_inf.mpr ⟨hh0C, ?_⟩
    show π h0 ∈ R
    rw [hπ, hh0]
    exact hr
  obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_right.mp (hcover hh0T)
  refine ⟨n, hNP hn, ?_⟩
  rw [← hh0, ← hnz, map_mul]
  have : QuotientGroup.mk' Θ z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  rw [this, mul_one]

theorem map_inSubgroup_pCore {G M : Type} [Group G] [Group M] {ι : G →* M}
    (hι : Function.Injective ι) (p : ℕ) (N : Subgroup G) :
    (CFSG.inSubgroup (CFSG.pCore p) N).map ι = CFSG.inSubgroup (CFSG.pCore p) (N.map ι) := by
  have h := CFSG.pCore_map_iso p (N.equivMapOfInjective ι hι)
  unfold CFSG.inSubgroup
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

variable {G : Type} [Group G]

theorem coe_mem_inSubgroup_pCore {Y U₁ : Subgroup G} (hU : U₁ ≤ Y) {x : Y}
    (hx : x ∈ inSubgroup (CFSG.pCore 2)
      (Subgroup.centralizer ((U₁.subgroupOf Y : Subgroup Y) : Set Y))) :
    (x : G) ∈ inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)) := by
  have hmap : (Subgroup.centralizer ((U₁.subgroupOf Y : Subgroup Y) : Set Y)).map Y.subtype =
      Y ⊓ Subgroup.centralizer (U₁ : Set G) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have := Subgroup.mem_centralizer_iff.mp hy ⟨u, hU hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      exact congrArg Subtype.val this
    · intro hz
      obtain ⟨hzY, hz⟩ := Subgroup.mem_inf.mp hz
      refine ⟨⟨z, hzY⟩, ?_, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz u (Subgroup.mem_subgroupOf.mp hu))
  rw [← hmap, ← map_inSubgroup_pCore Y.subtype_injective 2]
  exact ⟨x, hx, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2125
