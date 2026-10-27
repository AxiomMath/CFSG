module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S29

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

namespace S29Step3

omit [Finite G] in
theorem mem_normalizer_sup {X Y : Subgroup G} {x : G} (hX : x ∈ Subgroup.normalizer (X : Set G))
    (hY : x ∈ Subgroup.normalizer (Y : Set G)) :
    x ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have h1 : conjSub x (X ⊔ Y) = X ⊔ Y := by
    rw [show conjSub x (X ⊔ Y) = conjSub x X ⊔ conjSub x Y from Subgroup.map_sup _ _ _,
      conjSub_eq_of_mem_normalizer hX, conjSub_eq_of_mem_normalizer hY]
  exact mem_normalizer_of_conjSub_eq h1

omit [Finite G] in
theorem commutator_le_inf {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    (hA : A ≤ Subgroup.normalizer (B : Set G)) : ⁅A, B⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hyA : y * x⁻¹ * y⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hB hy) x⁻¹).mp (Subgroup.inv_mem _ hx)
  have hxB : x * y * x⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (hA hx) y).mp hy
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have := Subgroup.mul_mem _ hx hyA
    simpa [mul_assoc] using this
  · have := Subgroup.mul_mem _ hxB (Subgroup.inv_mem _ hy)
    simpa [mul_assoc] using this

theorem exists_not_le (hs : Sit29 H M S α a₂ a₃ β) (hb : bMin H M = 2) :
    ∃ a ∈ nbrs β, a ≠ α ∧ ¬ Zv α ≤ Qv a := by
  obtain ⟨α'', hd, hn⟩ := bAt_spec hs.amalg α
  rw [hs.bα, hb] at hd
  obtain ⟨β'', hadj, hd1⟩ :=
    exists_adj_dist_eq hs.amalg.amalgam.gen (α := α) (δ := α'') (d := 1) hd
  have hβ''n : β'' ∈ nbrs α := dist_eq_one_iff_adj.mp hd1
  obtain ⟨g, hg, hgβ⟩ := stab_transitive_on_nbrs hβ''n hs.adj
  have hgα : g • α = α := smul_eq_of_mem_stab hg
  refine ⟨g • α'', ?_, ?_, ?_⟩
  · have h : (graph (H ⊔ M) H M).Adj (g • α'') (g • β'') := (smul_adj g).mpr hadj
    rw [hgβ] at h
    exact h.symm
  · intro heq
    have h2 : dist α (g • α'') = 2 := by
      have h := CosetGeom.dist_smul g α α''
      rw [hgα] at h
      exact h.trans hd
    have : dist α α = 0 := dist_self α
    rw [heq] at h2
    omega
  · intro hle
    have hZ : conjSub (g : G) (Zv α) = Zv α :=
      conjSub_eq_of_mem_normalizer (stab_le_normalizer_Zv hs.amalg α hg)
    rw [Qv_smul] at hle
    have h2 : conjSub (g : G) (Zv α) ≤ conjSub (g : G) (Qv α'') := by
      rw [hZ]; exact hle
    exact hn ((conjSub_le_conjSub_iff' (g : G)).mp h2)

theorem centralizer_eq (hs : Sit29 H M S α a₂ a₃ β) :
    Zv a₂ ⊓ Subgroup.centralizer (Zv α : Set G) = Qv α ⊓ Zv a₂ := by
  have hZ : Zv a₂ ≤ stab α :=
    (hs.swap₁₂.Zv_le_Qv_right).trans (Qv_le_stab_of_mem_nbrs hs.amalg hs.n₁)
  rw [← centralizer_Zv_eq_Qv_of_bAt hs.amalg hs.bα]
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hZ h1, h2⟩, h1⟩, fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, h2⟩⟩

theorem elem (hs : Sit29 H M S α a₂ a₃ β) :
    (Qv α ⊓ Zv a₂).relIndex (Zv a₂) ≤ 4 ∧
    (Qv α ⊓ Zv a₂).relIndex (Zv a₂) ≤ (Qv a₂ ⊓ Zv α).relIndex (Zv α) ∧
    ((Qv α ⊓ Zv a₂).relIndex (Zv a₂) = 4 → 4 ≤ Nat.card ↥⁅Zv α, Zv a₂⁆) := by
  have hZ2b : Zv a₂ ≤ Qv β := hs.swap₁₂.Zv_le_Qv_right
  have hS : Zv a₂ ≤ stab α ⊓ stab β :=
    le_inf (hZ2b.trans (Qv_le_stab_of_mem_nbrs hs.amalg hs.n₁)) (hZ2b.trans (pCoreOf_le 2 _))
  have hc := centralizer_eq hs.swap₁₂
  obtain ⟨h1, h2, h3⟩ := hs.mod₁.elem_abelian (Zv a₂) hS (isElemAbelian_Zv hs.amalg a₂)
  refine ⟨h1, ?_, h3⟩
  have e : Zv α ⊓ Subgroup.centralizer (Zv a₂ : Set G) = Qv a₂ ⊓ Zv α := hc
  rw [e] at h2
  exact h2

theorem idx_eq_four (hs : Sit29 H M S α a₂ a₃ β)
    (h : (Qv α ⊓ Zv a₂).relIndex (Zv a₂) = 2) : (Qv a₂ ⊓ Zv α).relIndex (Zv α) = 4 := by
  have hA := hs.amalg
  have hZ2b : Zv a₂ ≤ Qv β := hs.swap₁₂.Zv_le_Qv_right
  have hZ2α : Zv a₂ ≤ stab α := hZ2b.trans (Qv_le_stab_of_mem_nbrs hA hs.n₁)
  have hS : Zv a₂ ≤ stab α ⊓ stab β := le_inf hZ2α (hZ2b.trans (pCoreOf_le 2 _))
  have hN1 : stab α ≤ Subgroup.normalizer (Qv α : Set G) := le_normalizer_pCoreOf 2 _
  have hN : stab α ⊓ stab β ≤ Subgroup.normalizer ((Qv α ⊔ Zv a₂ : Subgroup G) : Set G) := by
    rw [← hs.sup_Qv]
    refine sup_le (fun x hx => Subgroup.le_normalizer (Subgroup.mem_sup_left hx))
      (fun x hx => mem_normalizer_sup (hN1 (Qv_le_stab_of_mem_nbrs hA hs.n₁ hx))
        (stab_le_normalizer_Zv hA a₂ (Qv_le_stab_of_mem_nbrs hA hs.n₂ hx)))
  have hidx : (Qv α).relIndex (Qv α ⊔ Zv a₂) = 2 := by
    have := relIndex_inf_eq_relIndex_sup (K := Zv a₂) (Q := Qv α) (hZ2α.trans hN1)
    rw [inf_comm, sup_comm, h] at this
    exact this.symm
  have h4 := hs.mod₁.central_involution (Zv a₂) hS hN hidx
  have e : Zv α ⊓ Subgroup.centralizer (Zv a₂ : Set G) = Qv a₂ ⊓ Zv α :=
    centralizer_eq hs.swap₁₂
  rwa [e] at h4

theorem aux (hs : Sit29 H M S α a₂ a₃ β) (hn : ¬ Zv α ≤ Qv a₂) :
    Nat.card ↥(Zv α ⊓ Zv a₂) = 4 := by
  have hA := hs.amalg
  have hs' := hs.swap₁₂
  obtain ⟨h1, h2, h3⟩ := elem hs
  obtain ⟨-, h2', -⟩ := elem hs'
  have hdvd : (Qv α ⊓ Zv a₂).relIndex (Zv a₂) ∣ 16 :=
    hs'.card_Zv ▸ Subgroup.relIndex_dvd_card _ _
  have hne : (Qv a₂ ⊓ Zv α).relIndex (Zv α) ≠ 1 := fun h =>
    hn ((Subgroup.relIndex_eq_one.mp h).trans inf_le_left)
  have hne0 : (Qv α ⊓ Zv a₂).relIndex (Zv a₂) ≠ 0 :=
    (Nat.pos_of_dvd_of_pos hdvd (by norm_num)).ne'

  have heq : (Qv α ⊓ Zv a₂).relIndex (Zv a₂) = (Qv a₂ ⊓ Zv α).relIndex (Zv α) :=
    le_antisymm h2 h2'
  have h4 : (Qv α ⊓ Zv a₂).relIndex (Zv a₂) = 4 := by
    have hcases : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → n ≤ 4 → n ∣ 16 → n = 2 ∨ n = 4 := by
      intro n h0 h1 h4 hd
      interval_cases n <;> omega
    rcases hcases _ hne0 (heq ▸ hne) h1 hdvd with h | h
    · exact absurd (heq ▸ idx_eq_four hs h) (by omega)
    · exact h
  have hcomm : 4 ≤ Nat.card ↥⁅Zv α, Zv a₂⁆ := h3 h4
  have hZ1b : Zv α ≤ Qv β := hs.Zv_le_Qv_right
  have hZ2b : Zv a₂ ≤ Qv β := hs'.Zv_le_Qv_right
  have hZ2α : Zv a₂ ≤ stab α := hZ2b.trans (Qv_le_stab_of_mem_nbrs hA hs.n₁)
  have hZ1a₂ : Zv α ≤ stab a₂ := hZ1b.trans (Qv_le_stab_of_mem_nbrs hA hs.n₂)
  have hle : ⁅Zv α, Zv a₂⁆ ≤ Zv α ⊓ Zv a₂ :=
    commutator_le_inf (fun x hx => stab_le_normalizer_Zv hA α (hZ2α hx))
      (fun x hx => stab_le_normalizer_Zv hA a₂ (hZ1a₂ hx))
  have hup : Nat.card ↥(Zv α ⊓ Zv a₂) ≤ Nat.card ↥(Qv α ⊓ Zv a₂) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ (Zv_le_Qv hA α))
  have hcard : Nat.card ↥(Qv α ⊓ Zv a₂) = 4 := by
    have := Subgroup.relIndex_mul_card (Qv α) (Zv a₂)
    rw [← Subgroup.inf_relIndex_right, h4, hs'.card_Zv] at this
    omega
  have hlow : Nat.card ↥⁅Zv α, Zv a₂⁆ ≤ Nat.card ↥(Zv α ⊓ Zv a₂) := Subgroup.card_le_of_le hle
  omega

end S29Step3

theorem step3 (hs : Sit29 H M S α a₂ a₃ β) (hb : bMin H M = 2) :
    Nat.card ↥(Zv α ⊓ Zv a₂) = 4 := by
  obtain ⟨a, ha, hne, hn⟩ := S29Step3.exists_not_le hs hb
  rcases hs.nbrs_eq a ha with h | h | h
  · exact absurd h hne
  · subst h
    exact S29Step3.aux hs hn
  · subst h
    rw [hs.R_eq₁]
    exact S29Step3.aux hs.swap₂₃ hn

end F53.Stellmacher.S29

end CFSG.Quasithin
