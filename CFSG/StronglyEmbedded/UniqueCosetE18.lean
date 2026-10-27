module

public import CFSG.StronglyEmbedded.UniqueCosetEnd
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.StronglyEmbedded.UniqueCoset

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic

theorem exists_conj_mem_of_isSylow2In {G : Type} [Group G] [Finite G] {T C : Subgroup G}
    (hT : IsSylow2In T C) {w : G} (hw : w ∈ C) (hw2 : orderOf w = 2) :
    ∃ c ∈ C, c⁻¹ * w * c ∈ T := by
  obtain ⟨hTC, hTp, hTmax⟩ := hT
  have hT' : IsPGroup 2 ↥(T.subgroupOf C) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  obtain ⟨P, hP⟩ := hT'.exists_le_sylow
  have hPT : (P : Subgroup ↥C) ≤ T.subgroupOf C := by
    have hV : (P : Subgroup ↥C).map C.subtype = T := by
      refine hTmax _ ?_ (P.isPGroup'.map C.subtype) ?_
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · intro t ht
        exact ⟨⟨t, hTC ht⟩, hP (Subgroup.mem_subgroupOf.2 ht), rfl⟩
    intro x hx
    rw [Subgroup.mem_subgroupOf, ← hV]
    exact ⟨x, hx, rfl⟩
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers (⟨w, hw⟩ : ↥C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hw2, pow_one])
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P' P
  have hwP : MulAut.conj c • (⟨w, hw⟩ : ↥C) ∈ (P : Subgroup ↥C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (Subgroup.mem_zpowers _))
  have hwT := Subgroup.mem_subgroupOf.1 (hPT hwP)
  refine ⟨(c : G)⁻¹, C.inv_mem c.2, ?_⟩
  simpa [MulAut.smul_def, MulAut.conj_apply] using hwT

theorem existsUnique_fixed_mul_of_isSylow2In {G : Type} [Group G] [Finite G] {H S : Subgroup G}
    {z : G} (hz : orderOf z = 2)
    (hSyl : IsSylow2In (S ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (h2S : ∀ h : G, h⁻¹ * z * h ∈ S → h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = h⁻¹ * z * h * z →
      ∃! c : G ⧸ H, (z * (h⁻¹ * z * h)) • c = c)
    (g : G) (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c := by
  set w := g⁻¹ * z * g with hw
  have hwC : w ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm
  have hw2 : orderOf w = 2 := by
    have hconj : w = MulAut.conj g⁻¹ z := by rw [hw, MulAut.conj_apply, inv_inv]
    rw [hconj, MulEquiv.orderOf_eq, hz]
  obtain ⟨c, hcC, hcS⟩ := exists_conj_mem_of_isSylow2In hSyl hwC hw2
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hcz' : z * c⁻¹ = c⁻¹ * z := by
    calc z * c⁻¹ = c⁻¹ * (c * z) * c⁻¹ := by group
      _ = c⁻¹ * (z * c) * c⁻¹ := by rw [hcz]
      _ = c⁻¹ * z := by group
  have he : (g * c)⁻¹ * z * (g * c) = c⁻¹ * w * c := by
    rw [hw]
    group
  have hS' : (g * c)⁻¹ * z * (g * c) ∈ S := by
    rw [he]
    exact (Subgroup.mem_inf.1 hcS).1
  have hne' : (g * c)⁻¹ * z * (g * c) ≠ z := by
    rw [he]
    intro h
    apply hne
    calc w = c * (c⁻¹ * w * c) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [h]
      _ = z * c * c⁻¹ := by rw [hcz]
      _ = z := by group
  have hcomm' : z * ((g * c)⁻¹ * z * (g * c)) = (g * c)⁻¹ * z * (g * c) * z := by
    rw [he]
    calc z * (c⁻¹ * w * c) = z * c⁻¹ * w * c := by group
      _ = c⁻¹ * z * w * c := by rw [hcz']
      _ = c⁻¹ * (z * w) * c := by group
      _ = c⁻¹ * (w * z) * c := by rw [hcomm]
      _ = c⁻¹ * w * (z * c) := by group
      _ = c⁻¹ * w * (c * z) := by rw [← hcz]
      _ = c⁻¹ * w * c * z := by group
  have key := existsUnique_fixed_conj c (h2S _ hS' hne' hcomm')
  have heq : c * (z * ((g * c)⁻¹ * z * (g * c))) * c⁻¹ = z * w := by
    rw [he]
    calc c * (z * (c⁻¹ * w * c)) * c⁻¹ = c * z * c⁻¹ * w := by group
      _ = z * c * c⁻¹ * w := by rw [hcz]
      _ = z * w := by group
  rwa [heq] at key

theorem le_centralizer_of_isUniqueInvolution {G : Type*} [Group G] {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : K ≤ Subgroup.centralizer ({z} : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : w * z * w⁻¹ ∈ K := K.mul_mem (K.mul_mem hw hz.mem) (K.inv_mem hw)
  have hsq : w * z * w⁻¹ * (w * z * w⁻¹) = 1 := by
    calc w * z * w⁻¹ * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz.sq, mul_one, mul_inv_cancel]
  rcases hz.unique _ hmem hsq with h | h
  · exfalso
    apply hz.ne_one
    calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  · calc w * z = w * z * w⁻¹ * w := by group
      _ = z * w := by rw [h]

theorem not_isSolvable_of_mem {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : ¬ Group.IsSolvable ↥K := by
  intro hsolv
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have hperf : Group.IsPerfect ↥K := hz'.perfect
  have hnt : Nontrivial ↥K := ⟨⟨⟨z, hz.mem⟩, 1, fun h => hz.ne_one (congrArg Subtype.val h)⟩⟩
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)
  rw [hperf.commutator_eq_top] at hlt
  exact lt_irrefl _ hlt

@[expose] def E18_endC (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      (∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥) →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        FixesUniqueCoset z H →
        (∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
          z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) →
        False

theorem e18_endC (p f : ℕ) [Fact p.Prime] : E18_endC p f := by
  intro G _ _ Ω K S R W H c hF z hz hSyl h1 h2S
  obtain ⟨F, hFn, hFs, hFnab, hFc⟩ := hF
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  exact false_of_uniqueCoset_of_not_isSolvable c.proper hz2 h1
    (existsUnique_fixed_mul_of_isSylow2In hz2 hSyl h2S) hFs hFnab hFc
    (le_centralizer_of_isUniqueInvolution hz) (not_isSolvable_of_mem c.stand.hyp c.stand.mem hz)

end CFSG.StronglyEmbedded.UniqueCoset
