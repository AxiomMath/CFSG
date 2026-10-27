module

public import CFSG.Quasithin.EmptyFaithful.E111L2C

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G]

theorem isPGroup_iSup {ι : Type*} [DecidableEq ι] {r : ℕ} (F : ι → Subgroup G)
    (hF : ∀ i j, F i = F j ∨ ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x)
    (hs : ∀ i, IsPGroup r ↥(F i)) (s : Finset ι) : IsPGroup r ↥(⨆ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ i ∈ (∅ : Finset ι), F i) = ⊥ := by simp
    rw [h0]
    exact IsPGroup.of_bot
  | insert a s _ ih =>
    rw [Finset.iSup_insert]
    refine IsPGroup.to_sup_of_normal_right' (hs a) ih ?_
    refine le_normalizer_iSup F s fun i _ => ?_
    rcases hF a i with h | h
    · rw [← h]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_comm h

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

theorem mem_centralizer_of_conj_diag {v : G} (hv : v ∈ A ⊓ Subgroup.normalizer (S : Set G))
    {s : ↥S} (hs : ∀ x : ↥S, v * diagHom S C h.diagComm x * v⁻¹ =
      diagHom S C h.diagComm s * diagHom S C h.diagComm x * (diagHom S C h.diagComm s)⁻¹) :
    (s : G)⁻¹ * v ∈ Subgroup.centralizer (S : Set G) := by
  have hinj := diagHom_injective h.diagComm h.center_trivial
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hs ⟨y, hy⟩
  rw [conj_diagHom_of_comm h.diagComm _ hv.2 fun c hc => h.comm hv.1 (h.CA hc), ← map_inv,
    ← map_mul, ← map_mul] at h1
  have h2 : v * y * v⁻¹ = (s : G) * y * (s : G)⁻¹ := congrArg Subtype.val (hinj h1)
  calc y * ((s : G)⁻¹ * v) = (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * v := by group
    _ = (s : G)⁻¹ * (v * y * v⁻¹) * v := by rw [h2]
    _ = (s : G)⁻¹ * v * y := by group

theorem inner_of_mem_diag_mul {v y y₀ : G} (hv : v ∈ A ⊓ Subgroup.normalizer (S : Set G))
    (hy : y ∈ diagSub S C h.diagComm)
    (hy₀ : y₀ ∈ Subgroup.centralizer (diagSub S C h.diagComm : Set G)) (hvy : v = y * y₀) :
    ∃ s ∈ S, s⁻¹ * v ∈ Subgroup.centralizer (S : Set G) := by
  obtain ⟨s, rfl⟩ := hy
  refine ⟨s, s.2, mem_centralizer_of_conj_diag h hv fun x => ?_⟩
  have hc := Subgroup.mem_centralizer_iff.mp hy₀ _ ⟨x, rfl⟩
  rw [hvy]
  calc diagHom S C h.diagComm s * y₀ * diagHom S C h.diagComm x *
        (diagHom S C h.diagComm s * y₀)⁻¹ =
      diagHom S C h.diagComm s * (y₀ * diagHom S C h.diagComm x) * y₀⁻¹ *
        (diagHom S C h.diagComm s)⁻¹ := by group
    _ = diagHom S C h.diagComm s * (diagHom S C h.diagComm x * y₀) * y₀⁻¹ *
        (diagHom S C h.diagComm s)⁻¹ := by rw [hc]
    _ = _ := by group

theorem mem_centralizer_of_centralizer_diag {v : G}
    (hv : v ∈ A ⊓ Subgroup.normalizer (S : Set G))
    (hvc : v ∈ Subgroup.centralizer (diagSub S C h.diagComm : Set G)) :
    v ∈ Subgroup.centralizer (S : Set G) := by
  have := mem_centralizer_of_conj_diag h hv (s := 1) fun x => by
    rw [map_one, one_mul, inv_one, mul_one]
    have hc := Subgroup.mem_centralizer_iff.mp hvc _ ⟨x, rfl⟩
    calc v * diagHom S C h.diagComm x * v⁻¹ = diagHom S C h.diagComm x * v * v⁻¹ := by rw [hc]
      _ = diagHom S C h.diagComm x := by group
  simpa using this

theorem inf_diag_eq [Finite G] :
    T ⊓ diagSub S C h.diagComm = ((T ⊓ S).subgroupOf S).map (diagHom S C h.diagComm) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := diagHom_injective h.diagComm h.center_trivial
  have hTS := isSylowIn_inf h.red h.comp
  set P := ((T ⊓ S).subgroupOf S).map (diagHom S C h.diagComm) with hP
  have hPD : P ≤ diagSub S C h.diagComm := Subgroup.map_le_range _ _
  have hPT : P ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    refine diagHom_mem_of h.diagComm x fun c hc => ?_
    have hxT : (x : G) ∈ T := (Subgroup.mem_subgroupOf.mp hx).1
    exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) hxT) (T.inv_mem (h.AT (h.CA hc)))
  have hcardP : Nat.card P = Nat.card ↥(T ⊓ S) := by
    rw [hP, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcardD : Nat.card ↥(diagSub S C h.diagComm) = Nat.card S :=
    (Nat.card_congr h.diagEquiv.toEquiv).symm
  have hPsyl : IsSylowIn 2 P (diagSub S C h.diagComm) := by
    refine isSylowIn_of_card_eq hPD ?_
    rw [hcardP, hcardD]
    exact hTS.card_eq
  exact (eq_of_le_of_isPGroup hPsyl (le_inf hPT hPD) inf_le_right
    (h.isPGroup_T.to_le inf_le_left)).symm

theorem diag_central [Finite G] {z : G} (hz : z ∈ T ⊓ S) (hzc : ∀ x ∈ T ⊓ S, z * x = x * z) :
    diagHom S C h.diagComm ⟨z, hz.2⟩ ∈ T ⊓ diagSub S C h.diagComm ∧
      ∀ y ∈ T ⊓ diagSub S C h.diagComm,
        diagHom S C h.diagComm ⟨z, hz.2⟩ * y = y * diagHom S C h.diagComm ⟨z, hz.2⟩ := by
  rw [inf_diag_eq h]
  refine ⟨⟨⟨z, hz.2⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hzc x (Subgroup.mem_subgroupOf.mp hx))

end CFSG.Quasithin.E2.E22N.E111L
