module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigBall

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

variable {α : RankTwoAmalgam.{u}} {Y : Type} [Group Y]

theorem f1_smul_lv_iff (c : α.Completion Y) (hc : c.IsFaithful) (a : α.G1) :
    f1 (c := c) a • c.lv = c.lv ↔ a ∈ α.α1.range := by
  constructor
  · intro h
    have h1 := CosetGeom.mem_stab_of_smul_eq h
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right] at h1
    have h2 : c.φ1 a ∈ c.φ1.range ⊓ c.φ2.range := ⟨⟨a, rfl⟩, h1⟩
    rw [c.inter] at h2
    obtain ⟨g, hg⟩ := h2
    refine ⟨g, hc.1 ?_⟩
    rw [c.comm1]
    exact hg
  · rintro ⟨g, rfl⟩
    apply CosetGeom.smul_eq_of_mem_stab
    rw [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) le_sup_right]
    show c.φ1 (α.α1 g) ∈ c.φ2.range
    rw [c.comm1]
    have : c.φ12 g ∈ c.φ1.range ⊓ c.φ2.range := by
      rw [c.inter]; exact ⟨g, rfl⟩
    exact this.2

@[expose] def Cz (c : α.Completion Y) (z : c.Γ) : Subgroup α.G1 :=
  (stv c z).comap (f1 (c := c))

theorem mem_Cz {c : α.Completion Y} {z : c.Γ} {a : α.G1} :
    a ∈ Cz c z ↔ f1 (c := c) a • z = z := MulAction.mem_stabilizer_iff

section Far

variable {S : LieSetting.{u, w}} [Finite Y]

theorem far_structure (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall S.m) {z : β.Γ} (hz : β.graph.dist β.xv z = S.m) :
    IsComplementIn (Cz β z) S.Qb1 ⊤ ∧
      ∀ u₁ u₂ u₃ u₄ : β.Γ, β.graph.Adj β.xv u₁ → β.graph.Adj β.xv u₂ → β.graph.Adj β.xv u₃ →
        β.graph.Adj β.xv u₄ → u₁ ≠ u₂ → u₃ ≠ u₄ →
        ∃ a ∈ Cz β z, f1 (c := β) a • u₁ = u₃ ∧ f1 (c := β) a • u₂ = u₄ := by
  have Fβ : β.Facts46 S.m := hS.facts46 β hβ
  obtain ⟨p, hp, hpz⟩ := Facts46.exists_geod_path (c := β) hz
  obtain ⟨-, hcase⟩ := hS.lemma_F46_8 β hβ β.xv hp
  rcases hcase with h1 | ⟨hcomp, h2, hbij⟩
  · exfalso
    obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := Fβ.two_geods_point hs (a := β.xv) rfl hz
    have e1 := h1 t₁ ht₁.1 (by rw [hpz]; exact ht₁.2.1) ht₁.2.2
    have e2 := h1 t₂ ht₂.1 (by rw [hpz]; exact ht₂.2.1) ht₂.2.2
    exact hne (e1.trans e2.symm)
  · have hQ : β.Qvert (S.Qx β) (S.Ql β) β.xv = S.Qx β :=
      Qvert_baseVert (S.Qx_normalized β) false
    rw [hQ, hpz] at hcomp
    have rg : stv β β.xv ≤ (f1 (c := β)).range := stv_xv_le_range_f1 β
    have hQle : S.Qx β ≤ (f1 (c := β)).range := Subgroup.map_le_range _ _
    have h3 := (IsComplementIn.comap_iff (f1 (c := β)) (f1_injective β hβ)
      (inf_le_left.trans rg) hQle rg).mp hcomp
    have e1 : (stv β β.xv).comap (f1 (c := β)) = ⊤ :=
      eq_top_iff.mpr fun a _ => MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a)
    have e2 : (S.Qx β).comap (f1 (c := β)) = S.Qb1 :=
      Subgroup.comap_map_eq_self_of_injective (f1_injective β hβ) _
    have e3 : (stv β β.xv ⊓ stv β z).comap (f1 (c := β)) = Cz β z := by
      rw [Subgroup.comap_inf, e1, top_inf_eq]
      rfl
    rw [e1, e2, e3] at h3
    refine ⟨h3, fun u₁ u₂ u₃ u₄ h₁ h₂ h₃ h₄ hne₁ hne₂ => ?_⟩
    obtain ⟨t₁, ht₁, ht₁1⟩ := hbij.surjOn (show u₁ ∈ CosetGeom.nbrs β.xv from h₁)
    obtain ⟨t₂, ht₂, ht₂1⟩ := hbij.surjOn (show u₂ ∈ CosetGeom.nbrs β.xv from h₂)
    obtain ⟨t₃, ht₃, ht₃1⟩ := hbij.surjOn (show u₃ ∈ CosetGeom.nbrs β.xv from h₃)
    obtain ⟨t₄, ht₄, ht₄1⟩ := hbij.surjOn (show u₄ ∈ CosetGeom.nbrs β.xv from h₄)
    have hn12 : t₁ ≠ t₂ := fun h => hne₁ (by rw [← ht₁1, ← ht₂1, h])
    have hn34 : t₃ ≠ t₄ := fun h => hne₂ (by rw [← ht₃1, ← ht₄1, h])
    obtain ⟨g, hg1, hg2, hg3, hg4⟩ := h2 t₁ t₂ t₃ t₄ ht₁ ht₂ ht₃ ht₄ hn12 hn34
    obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 β (MulAction.mem_stabilizer_iff.mpr hg1)
    refine ⟨a, ?_, ?_, ?_⟩
    · rw [mem_Cz, ← hpz]
      exact hg2
    · have := congrArg (fun t : GPath β.graph S.m => t 1) hg3
      simp only [GPath.smul_apply] at this
      rw [← ht₁1, ← ht₃1]
      exact this
    · have := congrArg (fun t : GPath β.graph S.m => t 1) hg4
      simp only [GPath.smul_apply] at this
      rw [← ht₂1, ← ht₄1]
      exact this

theorem qTrans_far (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall S.m) {z z' : β.Γ} (hz : β.graph.dist β.xv z = S.m)
    (hz' : β.graph.dist β.xv z' = S.m) : ∃ q ∈ S.Qb1, f1 (c := β) q • z = z' := by
  have Fβ : β.Facts46 S.m := hS.facts46 β hβ
  obtain ⟨t, ht, htz⟩ := Facts46.exists_geod_path (c := β) hz
  obtain ⟨t', ht', htz'⟩ := Facts46.exists_geod_path (c := β) hz'
  obtain ⟨g, hg1, hg2⟩ := Fβ.trans_pt β.xv rfl t t' ht ht'
  obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 β (MulAction.mem_stabilizer_iff.mpr hg1)
  obtain ⟨q, hq, k, hk, hqk⟩ := (far_structure hS β hβ hs hz).1.2.2.2 a (Subgroup.mem_top a)
  refine ⟨q, hq, ?_⟩
  have h1 : f1 (c := β) a • z = z' := by
    have := congrArg (fun r : GPath β.graph S.m => r S.m) hg2
    simp only [GPath.smul_apply] at this
    rw [← htz, ← htz']
    exact this
  rw [← h1, ← hqk, map_mul, mul_smul, (mem_Cz.mp hk)]

end Far

section Parity

variable (c : α.Completion Y) {m : ℕ}

theorem even_dist_xv_iff {z : c.Γ} (hz : CosetGeom.vtype z = decide (Odd m)) :
    Even (c.graph.dist c.xv z) ↔ Even m := by
  have hpar := GPath.dist_even_iff (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) c.xv z
  rw [← hpar]
  have h0 : CosetGeom.vtype c.xv = false := rfl
  rw [h0, hz]
  rcases Nat.even_or_odd m with h | h
  · simp [h, Nat.not_odd_iff_even.mpr h]
  · simp [h, Nat.not_even_iff_odd.mpr h]

theorem not_near_iff (hm : 1 ≤ m) (hD : ∀ u v : c.Γ, c.graph.dist u v ≤ m) {z : c.Γ}
    (hz : CosetGeom.vtype z = decide (Odd m)) :
    ¬ NearV m c z ↔ c.graph.dist c.xv z = m := by
  have hpar := even_dist_xv_iff c hz
  have hd := hD c.xv z
  rw [Nat.even_iff, Nat.even_iff] at hpar
  show ¬ c.graph.dist c.xv z ≤ m - 2 ↔ c.graph.dist c.xv z = m
  generalize c.graph.dist c.xv z = d at hpar hd ⊢
  omega

theorem vtype_of_dist_xv {z : c.Γ} (hz : c.graph.dist c.xv z = m) :
    CosetGeom.vtype z = decide (Odd m) := by
  have hpar := GPath.dist_even_iff (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) c.xv z
  rw [hz] at hpar
  have h0 : CosetGeom.vtype c.xv = false := rfl
  rw [h0] at hpar
  cases hvt : CosetGeom.vtype z
  · have hev : Even m := hpar.mp hvt.symm
    simp [Nat.not_odd_iff_even.mpr hev]
  · have hodd : ¬ Even m := fun he => by
      have := hpar.mpr he
      rw [hvt] at this
      exact Bool.noConfusion this
    simp [Nat.not_even_iff_odd.mp hodd]

end Parity

end CFSG.Quasithin.H13.F48Rig
