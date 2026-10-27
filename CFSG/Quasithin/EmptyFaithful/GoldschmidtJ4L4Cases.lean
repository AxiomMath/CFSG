module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Cz0
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Aut
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocFix

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint CFSG.Quasithin.J4Loc

local notation "A₈" => alternatingGroup (Fin 8)

theorem V0L_lt : ∀ c ∈ V0L, c < 2048 := by decide

section V0


theorem V0_maskList (hM : MatFacts) : MaskList V0 V0L := by
  intro c
  constructor
  · intro hc
    exact ⟨V0L_lt c hc, (mem_V0_iff hM).2 ⟨c, hc, rfl⟩⟩
  · rintro ⟨hc, h⟩
    obtain ⟨c', hc', e⟩ := (mem_V0_iff hM).1 h
    rw [eta_inj' hM hc (V0L_lt c' hc') e]
    exact hc'

theorem card_V0 (hM : MatFacts) : Nat.card ↥V0 = 8 := by
  have := MaskList.card hM (fun x hx => V0_le_Eg hM hx) (V0_maskList hM) (by decide)
  simpa [V0L] using this

theorem card_mulAut_V0_lt (hM : MatFacts) : Nat.card (MulAut ↥V0) < 20160 := by
  have h1 : eta uJ 11 422 ∈ V0 := Subgroup.subset_closure (by simp)
  have h2 : eta uJ 11 553 ∈ V0 := Subgroup.subset_closure (by simp)
  have h3 : eta uJ 11 1131 ∈ V0 := Subgroup.subset_closure (by simp)
  have : Finite ↥V0 := Nat.finite_of_card_ne_zero (by rw [card_V0 hM]; norm_num)
  have hgen : Subgroup.closure ({⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩} : Set ↥V0) = ⊤ := by
    have h : Subgroup.closure (((↑) : ↥V0 → J) ⁻¹'
        ({eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131} : Set J)) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hset : (((↑) : ↥V0 → J) ⁻¹'
        ({eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131} : Set J)) =
        ({⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩} : Set ↥V0) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (hx | hx | hx)
        · left; exact Subtype.ext hx
        · right; left; exact Subtype.ext hx
        · right; right; exact Subtype.ext hx
      · rintro (rfl | rfl | rfl)
        · left; rfl
        · right; left; rfl
        · right; right; rfl
    rw [hset] at h
    exact h
  have := card_mulAut_le _ _ _ hgen
  rw [card_V0 hM] at this
  omega

end V0

theorem exists_fixed_V0
    (hn : ∀ t ∈ P0, ∀ x ∈ V0, t * x * t⁻¹ ∈ V0) :
    ∃ z ∈ V0, z ≠ 1 ∧ ∀ t ∈ P0, t * z = z * t := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Finite J := CFSG.Quasithin.H13.J4.finite_J'
  have hV0P : V0 ≤ P0 := fun x hx => Eg_le_P0 (V0_le_Eg hM hx)
  have hne : (⊥ : Subgroup J) ≠ V0 := by
    intro h
    have hc := card_V0 hM
    rw [← h, Subgroup.card_bot] at hc
    omega
  obtain ⟨m, hmV, hmB, hfix⟩ := CFSG.Quasithin.J4Loc.exists_fixed_mod (T := P0) (B := ⊥)
    (M := V0) (isPGroup_P0 hF) bot_le hV0P hne
    (fun t _ x hx => by rw [Subgroup.mem_bot.1 hx]; simp) hn
  refine ⟨m, hmV, fun h => hmB (by rw [h]; exact Subgroup.one_mem _), fun t ht => ?_⟩
  have h1 := Subgroup.mem_bot.1 (hfix t ht)
  calc t * m = (t * m * t⁻¹ * m⁻¹) * m * t := by group
    _ = m * t := by rw [h1]; group

theorem false_of_case_z0
    (hP : P0 ≤ Subgroup.centralizer ({z0} : Set J)) {B : Subgroup J}
    (hB : B ≤ Subgroup.centralizer ({z0} : Set J)) (f : ↥B →* A₈) (hf : Function.Surjective f)
    (hker : ∀ x : ↥B, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) : False := by
  have hM := (j4Facts : J4Facts).mat
  exact false_of_le_centralizer (eta_mem_Eg 11 le_rfl 1131) (z0_ne_one hM)
    (fun t ht => (Subgroup.mem_centralizer_singleton_iff (G := J) (g := z0) (k := t)).1 (hP ht))
    B.subtype B.subtype_injective
    (fun x => hB x.2) f hf hker

theorem false_of_case_V0
    (hP : P0 ≤ Subgroup.normalizer (V0 : Set J)) {B : Subgroup J}
    (hB : B ≤ Subgroup.normalizer (V0 : Set J)) (f : ↥B →* A₈) (hf : Function.Surjective f)
    (hker : ∀ x : ↥B, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) : False := by
  have hM := (j4Facts : J4Facts).mat
  obtain ⟨z, hzV, hz1, hzfix⟩ := exists_fixed_V0 fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.1 (hP ht) x).1 hx
  have hsurj := surjective_comp_inclusion_centralizer (card_mulAut_V0_lt hM) hB f hf
  refine false_of_le_centralizer (V0_le_Eg hM hzV) hz1 hzfix
    (B := ↥(B ⊓ Subgroup.centralizer (V0 : Set J))) (Subgroup.subtype _)
    (Subgroup.subtype_injective _) (fun x => ?_)
    (f.comp (Subgroup.inclusion (inf_le_left : B ⊓ Subgroup.centralizer (V0 : Set J) ≤ B))) hsurj
    (fun x hx => ?_)
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 x.2.2 z hzV).symm
  · obtain ⟨k, hk⟩ := hker (Subgroup.inclusion inf_le_left x) hx
    refine ⟨k, Subgroup.inclusion_injective
      (inf_le_left : B ⊓ Subgroup.centralizer (V0 : Set J) ≤ B) ?_⟩
    rw [map_pow, hk, map_one]

end CFSG.Quasithin.J4L4
