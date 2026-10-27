module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCen

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62 P63

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P64

@[expose] def zGen (L : ZLab Γ G) (α : V) : Set G :=
  {w | ∃ δ, valence Γ δ = 5 ∧ Γ.dist α δ ≤ 2 ∧ w = L.z δ}

variable {L : ZLab Γ G} (F : FanTree Γ G)
include F

theorem zBall_eq {α : V} (hα : valence Γ α = 5) {z : G} (hLz : L.z α = z) :
    zBall Γ α z 2 = zGen L α := by
  ext w
  constructor
  · rintro ⟨g, hd, rfl⟩
    refine ⟨g • α, by rw [F.valence_smul_eq]; exact hα, hd, ?_⟩
    rw [z_smul hα g, hLz]
  · rintro ⟨δ, hδ, hd, rfl⟩
    obtain ⟨g, hg⟩ := exists_smul_of_valence_eq F (u := α) (w := δ) (by rw [hδ, hα])
    refine ⟨g, by rw [hg]; exact hd, ?_⟩
    rw [← hLz, ← z_smul hα g, hg]

theorem dist_cases {α δ : V} (hα : valence Γ α = 5) (hδ : valence Γ δ = 5)
    (hd : Γ.dist α δ ≤ 2) : δ = α ∨ Γ.dist α δ = 2 := by
  have hc : Γ.dist α δ = 0 ∨ Γ.dist α δ = 1 ∨ Γ.dist α δ = 2 := by omega
  rcases hc with h | h | h
  · left
    exact ((F.isTree.connected.dist_eq_zero_iff).1 h).symm
  · exfalso
    have := valence_adj_three F hα (dist_eq_one_iff_adj.1 h)
    omega
  · right
    exact h

variable (H : LabHyp L)
include H

theorem zGen_mem_nbrStab {α : V} (hα : valence Γ α = 5) :
    ∀ w ∈ zGen L α, w ∈ nbrStab Γ G α := by
  rintro _ ⟨δ, hδ, hd, rfl⟩
  rcases dist_cases F hα hδ hd with rfl | h
  · exact cinv_mem_nbrStab F (cinv_iff.2 (L.isCentral _ hα))
  · exact H.ker α δ hα h

theorem zGen_comm (h40 : Fan40 F) {ℓ : Line Γ} {j : ℤ} (D : LineData L ℓ j) (α : V) :
    ∀ a ∈ zGen L α, ∀ b ∈ zGen L α, a * b = b * a := by
  rintro _ ⟨δ, hδ, hd, rfl⟩ _ ⟨δ', hδ', hd', rfl⟩
  have hdd : Γ.dist δ δ' ≤ 4 := by
    have h1 := F.isTree.connected.dist_triangle (u := δ) (v := α) (w := δ')
    have h2 : Γ.dist δ α = Γ.dist α δ := SimpleGraph.dist_comm
    omega
  have hfix := mem_ballStab.1 (ballStab_four F h40 H D hδ) δ' hdd
  exact z_comm hδ' (MulAction.mem_stabilizer_iff.2 hfix)

omit F H in
theorem conj_mem_closure {S : Set G} {x : G} (h : ∀ s ∈ S, x * s * x⁻¹ ∈ S) :
    ∀ v ∈ Subgroup.closure S, x * v * x⁻¹ ∈ Subgroup.closure S := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem s hs => exact Subgroup.subset_closure (h s hs)
  | one => simp
  | mul a b _ _ ha hb =>
    have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

omit F H in
theorem closure_comm {S : Set G} (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ u ∈ Subgroup.closure S, ∀ v ∈ Subgroup.closure S, u * v = v * u := by
  have h1 : ∀ a ∈ S, ∀ v ∈ Subgroup.closure S, a * v = v * a := by
    intro a ha v hv
    have := closure_le_centralizer (S := S) (z := a) (fun s hs => h s hs a ha) hv
    rw [Subgroup.mem_centralizer_iff] at this
    exact this a rfl
  intro u hu v hv
  have := closure_le_centralizer (S := S) (z := v) (fun s hs => h1 s hs v hv) hu
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this v rfl).symm

omit H in
theorem closure_zGen_eq (H : LabHyp L) {α : V} (hα : valence Γ α = 5) {x : G}
    (hx : x ∈ MulAction.stabilizer G α) (hxo : orderOf x = 5) {ν₀ l₀ : V}
    (h0 : Br Γ α ν₀ l₀) :
    Subgroup.closure (zGen L α) = Subgroup.closure ({L.z α} ∪
      Set.range fun k : Fin 5 => x ^ (k : ℕ) * L.z l₀ * (x ^ (k : ℕ))⁻¹) := by
  have hxo' : orderOf x = valence Γ α := by rw [hxo, hα]
  have hl₀ : valence Γ l₀ = 5 := (Br.valence F hα h0).2
  have hpowS : ∀ n : ℕ, x ^ n • α = α := fun n =>
    MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer G α).pow_mem hx n)
  have hck : ∀ k : ℕ, L.z (x ^ k • l₀) = x ^ k * L.z l₀ * (x ^ k)⁻¹ := fun k => z_smul hl₀ _
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨δ, hδ, hd, rfl⟩
    rcases dist_cases F hα hδ hd with rfl | h
    · exact Subgroup.subset_closure (Or.inl rfl)
    · obtain ⟨ν, hν⟩ := exists_br F h
      obtain ⟨k, hk⟩ := F.exists_pow_smul_eq hx hxo' h0.1 hν.1
      have hk5 : x ^ (k % 5) = x ^ k := by rw [← hxo, pow_mod_orderOf]
      have hbr : Br Γ α ν (x ^ k • l₀) := by
        have := Br.smul F (x ^ k) h0
        rwa [hpowS, hk] at this
      obtain ⟨l', hl', hne, -⟩ := exists_sibling F hα hbr
      have hcl : x ^ k * L.z l₀ * (x ^ k)⁻¹ ∈ Subgroup.closure ({L.z α} ∪
          Set.range fun k : Fin 5 => x ^ (k : ℕ) * L.z l₀ * (x ^ (k : ℕ))⁻¹) := by
        rw [← hk5]
        exact Subgroup.subset_closure (Or.inr ⟨⟨k % 5, Nat.mod_lt _ (by norm_num)⟩, rfl⟩)
      rcases br_cases F hα hbr hl' hne.symm hν with e | e
      · rw [e, hck]
        exact hcl
      · rw [e, sib_label F H hα hbr hl' hne.symm, hck]
        exact mul_mem hcl (Subgroup.subset_closure (Or.inl rfl))
  · rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨k, rfl⟩)
    · exact Subgroup.subset_closure ⟨α, hα, by simp, rfl⟩
    · refine Subgroup.subset_closure ⟨x ^ (k : ℕ) • l₀, by rw [F.valence_smul_eq]; exact hl₀, ?_,
        (hck k).symm⟩
      have := dist_smul F (x ^ (k : ℕ)) α l₀
      rw [hpowS] at this
      rw [this, Br.dist_two F h0]

end P64

end CFSG.Quasithin.Fan86
