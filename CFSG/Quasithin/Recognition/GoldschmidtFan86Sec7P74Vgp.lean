module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Conj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lbl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Base

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem z_mem_cinv (L : ZLab Γ G) {α : V} (hα : valence Γ α = 5) : L.z α ∈ Cinv G α :=
  P62.cinv_iff.2 (L.isCentral α hα)

theorem zGroup_comm (h40 : Fan40 F) (h64 : Fan64 F) {α : V} (hα : valence Γ α = 5) {u v : G}
    (hu : u ∈ L.zGroup 2 α) (hv : v ∈ L.zGroup 2 α) : u * v = v * u := by
  have h := (h64 h40 α (L.z α) (z_mem_cinv L hα)).1
  rw [zGroup_eq_closure_zBall F L hα] at hu hv
  exact h u hu v hv

theorem zGroup_sq (h40 : Fan40 F) (h64 : Fan64 F) {α : V} (hα : valence Γ α = 5) {v : G}
    (hv : v ∈ L.zGroup 2 α) : v * v = 1 := by
  unfold ZLab.zGroup at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, -, h5, rfl⟩ := hx
    exact L.z_mul_self h5
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc := zGroup_comm (L := L) h40 h64 hα ha hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hc]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    rw [← mul_inv_rev, iha, inv_one]

theorem xe_comm_z (h71c : Fan71c F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    xe L P * L.z (P.vert 4) = L.z (P.vert 4) * xe L P :=
  L.comm_z_of_mem_stabilizer h5 (xe_mem_stabilizer h71c h5)

theorem zGroup_inf_centralizer (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5)
    {v : G} (hv : v ∈ L.zGroup 2 (P.vert 4)) (hc : xe L P * v = v * xe L P) :
    v = 1 ∨ v = L.z (P.vert 4) := by
  set α := P.vert 4 with hαdef
  have hrel := (h64 h40 α (L.z α) (z_mem_cinv L h5)).2.2 (xe L P) (xe_mem_stabilizer h71c h5)
    (by rw [orderOf_xe h71a h71c h5, h5])
  rw [← zGroup_eq_closure_zBall F L h5] at hrel
  set C0 : Subgroup (L.zGroup 2 α) :=
    (Subgroup.centralizer ({xe L P} : Set G)).subgroupOf (L.zGroup 2 α) with hC0
  have hidx : C0.index = 2 ^ 4 := hrel
  have hcard := Subgroup.card_mul_index C0
  rw [hidx, h72b α h5] at hcard
  have h2 : Nat.card C0 = 2 := by omega
  have hz : L.z α ∈ L.zGroup 2 α :=
    Subgroup.subset_closure ⟨α, by simp, h5, rfl⟩
  let z' : C0 := ⟨⟨L.z α, hz⟩, by
    rw [hC0, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact xe_comm_z h71c h5⟩
  obtain ⟨a, b, hab, hset⟩ := Nat.card_eq_two_iff.1 h2
  have hall : ∀ c : C0, c = a ∨ c = b := fun c => by
    have : c ∈ ({a, b} : Set C0) := by rw [hset]; trivial
    simpa using this
  have hz1 : z' ≠ 1 := fun h => L.z_ne_one h5 (congrArg (fun c : C0 => (c : G)) h)
  let v' : C0 := ⟨⟨v, hv⟩, by
    rw [hC0, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hc⟩
  have key : v' = 1 ∨ v' = z' := by
    rcases hall v' with h1 | h1 <;> rcases hall z' with h2 | h2 <;> rcases hall 1 with h3 | h3
    all_goals first
      | exact Or.inl (h1.trans h3.symm)
      | exact Or.inr (h1.trans h2.symm)
      | exact absurd (h2.trans h3.symm) hz1
  rcases key with h | h
  · left; exact congrArg (fun c : C0 => (c : G)) h
  · right; exact congrArg (fun c : C0 => (c : G)) h

end P74

end CFSG.Quasithin.Fan86
