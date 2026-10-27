module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P64Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P64Grp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P64Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52S

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62 P63 P64

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan64 (F : FanTree Γ G) (hΞ : ∃ T : Track Γ G, InXi T) (h61 : Fan61 F) (h62 : Fan62 F)
    (h512b : Fan512b F) (h517a : Fan517a F) (hD : LemmaD F) (h517c : Fan517c F) : Fan64 F := by
  intro h40 α z hz
  have hα : valence Γ α = 5 := by
    have h1 := h61 h40 α z hz
    have h2 : valence Γ α = 3 ∨ valence Γ α = 5 := F.valence α
    omega
  obtain ⟨L, ℓ, j, hLz, H, D⟩ := exists_lab_data F h40 hΞ h62 h512b h517a hD h517c hα hz
  rw [zBall_eq F hα hLz]
  have hcomm := zGen_comm F H h40 D α
  have hK : Subgroup.closure (zGen L α) ≤ nbrStab Γ G α :=
    (Subgroup.closure_le _).2 fun w hw => zGen_mem_nbrStab F H hα w hw
  have : Finite (Subgroup.closure (zGen L α)) := by
    have := F.finite_nbrStab α
    exact Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)
  refine ⟨closure_comm hcomm, hα, fun x hx hxo => ?_⟩
  have hxo5 : orderOf x = 5 := by rw [hxo, hα]
  have hxo' : orderOf x = valence Γ α := hxo
  have hxS : x • α = α := MulAction.mem_stabilizer_iff.1 hx
  obtain ⟨ν₀, hν₀⟩ := F.exists_adj α
  obtain ⟨l₀, hl₀, hl₀α⟩ := F.exists_adj_ne ν₀ α
  have h0 : Br Γ α ν₀ l₀ := ⟨hν₀, hl₀, hl₀α⟩
  have hv0 : valence Γ l₀ = 5 := (Br.valence F hα h0).2
  have hgen := closure_zGen_eq F H hα hx hxo5 h0
  rw [hLz] at hgen
  have hsq : ∀ v ∈ Subgroup.closure (zGen L α), v * v = 1 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨δ, hδ, -, rfl⟩ := hw
      exact z_sq hδ
    | one => simp
    | mul a b ha hb ha2 hb2 =>
      have hab := closure_comm hcomm a ha b hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    | inv a _ ha2 =>
      rw [← mul_inv_rev, ha2, inv_one]
  have hnorm : ∀ v ∈ Subgroup.closure (zGen L α),
      x * v * x⁻¹ ∈ Subgroup.closure (zGen L α) := by
    refine conj_mem_closure ?_
    rintro _ ⟨δ, hδ, hd, rfl⟩
    refine ⟨x • δ, by rw [F.valence_smul_eq]; exact hδ, ?_, (z_smul hδ x).symm⟩
    have := dist_smul F x α δ
    rw [hxS] at this
    rw [this]
    exact hd
  have hxz : x * z = z * x := by
    have := z_comm hα hx (L := L)
    rwa [hLz] at this
  have hνν : ν₀ ≠ x • ν₀ := by
    intro h
    obtain ⟨ν', hν', hne'⟩ := F.exists_adj_ne α ν₀
    obtain ⟨i, hi⟩ := F.exists_pow_smul_eq hx hxo' hν₀ hν'
    have : ∀ n : ℕ, x ^ n • ν₀ = ν₀ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, ← h, ih]
    exact hne' ((this i).symm.trans hi).symm
  have h0' : Br Γ α (x • ν₀) (x • l₀) := by
    have := Br.smul F x h0
    rwa [hxS] at this
  have hd4 := dist_four F h0 h0' hνν
  have hne : l₀ ≠ x • l₀ := fun h => by
    rw [← h, SimpleGraph.dist_self] at hd4
    omega
  have hv0' : valence Γ (x • l₀) = 5 := by rw [F.valence_smul_eq]; exact hv0
  have hcx : x * L.z l₀ * x⁻¹ ≠ L.z l₀ := by
    rw [← z_smul hv0 x]
    exact (H.dist l₀ (x • l₀) hne hv0 hv0' (Or.inr hd4)).symm
  have hx5 : x ^ 5 = 1 := by rw [← hxo5]; exact pow_orderOf_eq_one x
  have key := relIndex_centralizer_eq_sixteen (Subgroup.closure (zGen L α)) x z (L.z l₀) hx5
    (closure_comm hcomm) hsq hnorm hxz hcx hgen
  rw [key]
  norm_num

end CFSG.Quasithin.Fan86
