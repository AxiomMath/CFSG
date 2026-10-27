module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Set

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem z_mem_labSpan2 {v l : V} (h5 : valence Γ l = 5) (h : Γ.dist v l = 2) :
    L.z l ∈ labSpan2 L v :=
  Subgroup.subset_closure ⟨l, h5, h, rfl⟩

theorem labSpan2_le_ballStab (_h40 : Fan40 F) (H : Lab18 L) {v : V} (_hv : valence Γ v = 5) :
    labSpan2 L v ≤ ballStab Γ G 2 v := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl5, hl, rfl⟩
  exact H.z4 l v hl5 (by rw [dist_comm]; exact hl)

theorem labSpan2_normalized (_h40 : Fan40 F) (_H : Lab18 L) {v : V} (_hv : valence Γ v = 5)
    {g : G} (hg : g ∈ MulAction.stabilizer G v) {h : G} (hh : h ∈ labSpan2 L v) :
    g * h * g⁻¹ ∈ labSpan2 L v := by
  have hgv : g • v = v := MulAction.mem_stabilizer_iff.1 hg
  unfold labSpan2 at hh ⊢
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl5, hl, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨g • l, ?_, ?_, (L.equivariant g l hl5).symm⟩
    · rw [F.valence_smul_eq g l]
      exact hl5
    · have := dist_smul F g v l
      rw [hgv] at this
      exact this.trans hl
  | one => simp
  | mul y z _ _ hy hz =>
    have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [this]
    exact mul_mem hy hz
  | inv y _ hy =>
    have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hy

theorem ballStab_commute_labSpan2 (_h40 : Fan40 F) (_H : Lab18 L) {v : V}
    (_hv : valence Γ v = 5) {g : G} (hg : g ∈ ballStab Γ G 2 v) {h : G}
    (hh : h ∈ labSpan2 L v) : g * h = h * g := by
  have key : labSpan2 L v ≤ Subgroup.centralizer {g} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨l, hl5, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    have hkl : k • l = l := mem_ballStab.1 hg l (le_of_eq hl)
    exact (L.isCentral l hl5).2.2.2 k (MulAction.mem_stabilizer_iff.2 hkl)
  exact Subgroup.mem_centralizer_iff.1 (key hh) g (Set.mem_singleton g)

theorem smul_ne_of_orderOf_five (F : FanTree Γ G) {v ν : V} (hν : Γ.Adj v ν) {x : G}
    (hx : x ∈ MulAction.stabilizer G v) (hx5 : orderOf x = 5) : x • ν ≠ ν := by
  intro h
  have hmem : x ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G ν :=
    ⟨hx, MulAction.mem_stabilizer_iff.2 h⟩
  obtain ⟨k, hk⟩ := F.edge_two v ν hν ⟨x, hmem⟩
  have h1 : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : 5 ∣ 2 ^ k := by
    rw [← hx5]
    exact orderOf_dvd_of_pow_eq_one h1
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h2
  omega

theorem exists_label_moved (F : FanTree Γ G) (H : Lab18 L) {v : V} (hv : valence Γ v = 5)
    {x : G} (hx : x ∈ MulAction.stabilizer G v) (hx5 : orderOf x = 5) :
    ∃ l : V, valence Γ l = 5 ∧ Γ.dist v l = 2 ∧ x * L.z l * x⁻¹ ≠ L.z l := by
  have hxv : x • v = v := MulAction.mem_stabilizer_iff.1 hx
  obtain ⟨ν, hν⟩ := F.exists_adj v
  obtain ⟨l, hl, hlv⟩ := F.exists_adj_ne ν v
  have hbr : Br Γ v ν l := ⟨hν, hl, hlv⟩
  have hbr' : Br Γ v (x • ν) (x • l) := by
    have := Br.smul F x hbr
    rwa [hxv] at this
  have hl5 : valence Γ l = 5 := (Br.valence F hv hbr).2
  have hd : Γ.dist l (x • l) = 4 :=
    dist_four F hbr hbr' (fun h => smul_ne_of_orderOf_five F hν hx hx5 h.symm)
  have hne : l ≠ x • l := fun h => by
    rw [← h, dist_self] at hd
    omega
  have hxl5 : valence Γ (x • l) = 5 := by
    rw [F.valence_smul_eq x l]
    exact hl5
  refine ⟨l, hl5, Br.dist_two F hbr, fun h => ?_⟩
  have := H.hyp.dist l (x • l) hne hl5 hxl5 (Or.inr hd)
  exact this (by rw [L.equivariant x l hl5, h])

theorem vLayer (S : B2Set F L T a) {x : G} (hx : x ∈ MulAction.stabilizer G (xv T a 6))
    (hxo : orderOf x = 5) :
    ∃ h ∈ labSpan2 L (xv T a 6), x * h * x⁻¹ * h⁻¹ ≠ 1 := by
  have hv : valence Γ (xv T a 6) = 5 := by simpa using S.val_even 3
  obtain ⟨l, hl5, hl, hne⟩ := exists_label_moved F S.lab hv hx hxo
  exact ⟨L.z l, z_mem_labSpan2 hl5 hl, fun h => hne (mul_inv_eq_one.1 h)⟩

end P518

end CFSG.Quasithin.Fan86
