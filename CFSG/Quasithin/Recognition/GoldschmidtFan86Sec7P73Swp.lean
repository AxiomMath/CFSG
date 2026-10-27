module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

open Classical in
@[expose] noncomputable def swp (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (g : G)
    (ν : V) : ZMod 2 :=
  if g ∈ nbrStab Γ G ν then 0 else 1

theorem swp_eq_zero_iff {g : G} {ν : V} : swp Γ G g ν = 0 ↔ g ∈ nbrStab Γ G ν := by
  unfold swp
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

theorem swp_eq_one_iff {g : G} {ν : V} : swp Γ G g ν = 1 ↔ g ∉ nbrStab Γ G ν := by
  unfold swp
  split_ifs with h
  · exact ⟨fun e => absurd e (by decide), fun e => absurd h e⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

theorem swp_cases (g : G) (ν : V) : swp Γ G g ν = 0 ∨ swp Γ G g ν = 1 := by
  unfold swp
  split_ifs <;> simp

theorem swp_smul (F : FanTree Γ G) (g k : G) (ν : V) :
    swp Γ G k (g • ν) = swp Γ G (g⁻¹ * k * g) ν := by
  by_cases h : k ∈ nbrStab Γ G (g • ν)
  · have h' := (F.mem_nbrStab_smul_iff g ν (h := k)).1 h
    rw [swp_eq_zero_iff.2 h, swp_eq_zero_iff.2 h']
  · have h' : g⁻¹ * k * g ∉ nbrStab Γ G ν := fun hh =>
      h ((F.mem_nbrStab_smul_iff g ν (h := k)).2 hh)
    rw [swp_eq_one_iff.2 h, swp_eq_one_iff.2 h']

theorem swap_or_fix (F : FanTree Γ G) {α ν a b : V} (hset : Γ.neighborSet ν = {α, a, b})
    (hab : a ≠ b) (haα : α ≠ a) (hbα : α ≠ b) {g : G} (hgα : g • α = α) (hgν : g • ν = ν) :
    (g • a = a ∧ g • b = b) ∨ (g • a = b ∧ g • b = a) := by
  have hnb : ∀ w, Γ.Adj ν w → w = α ∨ w = a ∨ w = b := by
    intro w hw
    have : w ∈ Γ.neighborSet ν := hw
    rw [hset] at this
    simpa using this
  have hadj : ∀ w, Γ.Adj ν w → Γ.Adj ν (g • w) := by
    intro w hw
    have := (F.adj_smul g ν w).2 hw
    rwa [hgν] at this
  have hna : Γ.Adj ν a := by
    have : a ∈ Γ.neighborSet ν := by rw [hset]; simp
    exact this
  have hnb' : Γ.Adj ν b := by
    have : b ∈ Γ.neighborSet ν := by rw [hset]; simp
    exact this
  have hga : g • a = a ∨ g • a = b := by
    rcases hnb _ (hadj a hna) with e | e | e
    · exact absurd (MulAction.injective g (e.trans hgα.symm)) (Ne.symm haα)
    · exact Or.inl e
    · exact Or.inr e
  have hgb : g • b = a ∨ g • b = b := by
    rcases hnb _ (hadj b hnb') with e | e | e
    · exact absurd (MulAction.injective g (e.trans hgα.symm)) (Ne.symm hbα)
    · exact Or.inl e
    · exact Or.inr e
  have hinj : g • a ≠ g • b := fun e => hab (MulAction.injective g e)
  rcases hga with e1 | e1 <;> rcases hgb with e2 | e2
  · exact absurd (e1.trans e2.symm) hinj
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (e1.trans e2.symm) hinj

theorem mem_nbrStab_iff_fix (F : FanTree Γ G) {α ν a : V} (hνα : Γ.Adj ν α) (hνa : Γ.Adj ν a)
    (haα : α ≠ a) {g : G} (hgα : g • α = α) : g ∈ nbrStab Γ G ν ↔ g • a = a := by
  constructor
  · intro h
    exact mem_nbrStab.1 h a hνa
  · intro h
    exact F.fix_two_nbrs hνα hνa haα hgα h

theorem swp_mul (F : FanTree Γ G) {α ν : V} (hα : valence Γ α = 5) (hαν : Γ.Adj α ν) {g h : G}
    (hg : g ∈ nbrStab Γ G α) (hh : h ∈ nbrStab Γ G α) :
    swp Γ G (g * h) ν = swp Γ G g ν + swp Γ G h ν := by
  have hv3 := valence_adj_three F hα hαν
  have hνα : Γ.Adj ν α := hαν.symm
  obtain ⟨a, hνa, haα⟩ := F.exists_adj_ne ν α
  obtain ⟨b, hset, hαb, hab⟩ := exists_third_neighbor hv3 hνα hνa (Ne.symm haα)
  have hfix : ∀ k, k ∈ nbrStab Γ G α → k • α = α := fun k hk =>
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hk)
  have hfixν : ∀ k, k ∈ nbrStab Γ G α → k • ν = ν := fun k hk => mem_nbrStab.1 hk ν hαν
  have hsw : ∀ k, k ∈ nbrStab Γ G α → (swp Γ G k ν = 0 ↔ k • a = a) := fun k hk => by
    rw [swp_eq_zero_iff, mem_nbrStab_iff_fix F hνα hνa (Ne.symm haα) (hfix k hk)]
  have hzero : ∀ k, k ∈ nbrStab Γ G α → k • a = a → swp Γ G k ν = 0 := fun k hk e =>
    (hsw k hk).2 e
  have hone : ∀ k, k ∈ nbrStab Γ G α → k • a ≠ a → swp Γ G k ν = 1 := fun k hk hne =>
    (swp_cases k ν).resolve_left (fun h0 => hne ((hsw k hk).1 h0))
  have hgh : g * h ∈ nbrStab Γ G α := Subgroup.mul_mem _ hg hh
  rcases swap_or_fix F hset hab (Ne.symm haα) hαb (hfix g hg) (hfixν g hg) with ⟨g1, g2⟩ | ⟨g1, g2⟩
  <;> rcases swap_or_fix F hset hab (Ne.symm haα) hαb (hfix h hh) (hfixν h hh) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hzero g hg g1, hzero h hh h1, hzero _ hgh (by rw [mul_smul, h1, g1])]
    rfl
  · rw [hzero g hg g1, hone h hh (by rw [h1]; exact hab.symm), hone _ hgh (by
      rw [mul_smul, h1, g2]; exact hab.symm)]
    rfl
  · rw [hone g hg (by rw [g1]; exact hab.symm), hzero h hh h1, hone _ hgh (by
      rw [mul_smul, h1, g1]; exact hab.symm)]
    rfl
  · rw [hone g hg (by rw [g1]; exact hab.symm), hone h hh (by rw [h1]; exact hab.symm),
      hzero _ hgh (by rw [mul_smul, h1, g2])]
    decide

end P73

end CFSG.Quasithin.Fan86
