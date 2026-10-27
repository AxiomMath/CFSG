module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bTab

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def Zidx : List ℕ := [0, 6, 20, 58, 64, 70, 84, 122]

@[expose] def Zl : List PL := Zidx.map fun i => Thl.getD i []

theorem Zl_center : ∀ l ∈ Thl, comp l fhatL = comp fhatL l →
    (∀ m ∈ Thl, comp m fhatL = comp fhatL m → comp m l = comp l m) → l ∈ Zl := by
  decide +kernel

theorem zf_types : ∀ k < 43, invL k ∈ Zl → invL k ≠ xL → invTgt.getD k 0 ≠ 0 := by
  decide +kernel

theorem cent_fhat : (Thl.filter fun m => comp m fhatL == comp fhatL m).length = 32 := by
  decide +kernel

theorem cent64_check : ∀ l ∈ Thl, comp l l = idL → l ≠ idL → l ≠ xL →
    (Thl.filter fun m => comp m l == comp l m).length ≤ 64 := by
  decide +kernel

theorem card_cent_ge_k {v : Ah} {vL : PL}
    (hv : RepL vL (v : P45)) {k : ℕ}
    (h : k ≤ (Thl.filter fun l => comp l vL == comp vL l).length) :
    k ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)) := by
  set F := Thl.filter fun l => comp l vL == comp vL l with hF
  have hnd : F.Nodup := Thl_nodup.filter _
  have key : ∀ l ∈ F, ∃ g : Ah, g ∈ That ⊓ Subgroup.centralizer ({v} : Set Ah) ∧
      RepL l (g : P45) := by
    intro l hl
    rw [hF, List.mem_filter] at hl
    obtain ⟨g, hg, hrep⟩ := exists_That_of_mem_Thl hl.1
    have hc : comp l vL = comp vL l := by simpa using hl.2
    refine ⟨g, Subgroup.mem_inf.2 ⟨hg, ?_⟩, hrep⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 := repL_mul hv hrep
    have h2 := repL_mul hrep hv
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (eq_of_repL (l := comp vL l) h1 (hc ▸ h2)).symm
  choose! gf hgf using key
  have hinj : Function.Injective fun i : Fin F.length =>
      (⟨gf (F.get i), (hgf _ (List.get_mem F i)).1⟩ :
        ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah))) := by
    intro i j hij
    have h1 : gf (F.get i) = gf (F.get j) := congrArg Subtype.val hij
    have h2 := hgf _ (List.get_mem F i)
    have h3 := hgf _ (List.get_mem F j)
    have : F.get i = F.get j := by
      apply repL_unique h2.2
      rw [h1]
      exact h3.2
    exact (hnd.get_inj_iff).1 this
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem card_cent_le_k {v : Ah} {vL : PL}
    (hv : RepL vL (v : P45)) {k : ℕ}
    (h : (Thl.filter fun l => comp l vL == comp vL l).length ≤ k) :
    Nat.card ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)) ≤ k := by
  classical
  set F := Thl.filter fun l => comp l vL == comp vL l with hF
  have hmem : ∀ g : ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)),
      permL ((g : Ah) : P45) ∈ F.toFinset := by
    intro g
    rw [List.mem_toFinset, hF, List.mem_filter]
    obtain ⟨hgT, hgC⟩ := g.2
    refine ⟨?_, ?_⟩
    · obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 hgT
      rw [permL_eq_of_repL hrep]
      exact hl
    · have hc : (g : Ah) * v = v * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
      have hc' : ((g : Ah) : P45) * (v : P45) = (v : P45) * ((g : Ah) : P45) :=
        congrArg Subtype.val hc
      have h1 := repL_mul (repL_permL ((g : Ah) : P45)) hv
      have h2 := repL_mul hv (repL_permL ((g : Ah) : P45))
      rw [← hc'] at h2
      simp only [beq_iff_eq]
      exact repL_unique h1 h2
  have hinj : Function.Injective fun g : ↥(That ⊓ Subgroup.centralizer ({v} : Set Ah)) =>
      (⟨permL ((g : Ah) : P45), hmem g⟩ : ↥F.toFinset) := by
    intro g₁ g₂ hg
    have h1 : permL ((g₁ : Ah) : P45) = permL ((g₂ : Ah) : P45) := congrArg Subtype.val hg
    have h2 : ((g₁ : Ah) : P45) = ((g₂ : Ah) : P45) :=
      eq_of_repL (repL_permL _) (h1 ▸ repL_permL _)
    exact Subtype.ext (Subtype.ext h2)
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card ↥F.toFinset = F.toFinset.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [h3] at h1
  exact h1.trans ((List.toFinset_card_le F).trans h)

theorem card_Tf_model :
    Nat.card ↥(That ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 32 :=
  le_antisymm (card_cent_le_k (v := fhatA) repL_fhat (le_of_eq cent_fhat))
    (card_cent_ge_k (v := fhatA) repL_fhat (le_of_eq cent_fhat.symm))

theorem card_cent_le_64 {u : Ah} (hu : u ∈ That)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hux : u ≠ xA) :
    Nat.card ↥(That ⊓ Subgroup.centralizer ({u} : Set Ah)) ≤ 64 := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff u).1 hu
  have hl2 : comp l l = idL := repL_unique (repL_mul hrep hrep) (by
    have : (u : P45) * (u : P45) = 1 := congrArg Subtype.val hu2
    rw [this]
    exact repL_one 45)
  have hl1 : l ≠ idL := fun h => hu1 (Subtype.ext (eq_of_repL hrep (h ▸ repL_one 45)))
  have hlx : l ≠ xL := fun h => hux (Subtype.ext (eq_of_repL hrep (h ▸ (repL_x : RepL xL _))))
  exact card_cent_le_k hrep (cent64_check l hl hl2 hl1 hlx)

end CFSG.Quasithin.H13.F431.U42Aut
