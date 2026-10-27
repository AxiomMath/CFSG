module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EB
public import CFSG.Quasithin.Vol2.E2StatementsAS
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc

public section

namespace CFSG.Quasithin.RonanE27

open Equiv CFSG.Quasithin CFSG.Quasithin.Ch3E213M.P6E CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Borel252.A6

@[expose] def s06L : List R6 := d0L ++ d0L.map (· * R6.enc zB)

theorem mem_S06_iff {x : P6} : x ∈ S06 ↔ R6.enc x ∈ s06L := by
  constructor
  · exact enc_mem_s06L
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ((mem_D0 x).2 h)
    · obtain ⟨r, hr, hrx⟩ := List.mem_map.1 h
      obtain ⟨y, hy, rfl⟩ := sound_D0 r hr
      refine Or.inr ?_
      have h1 : x = y * zB := R6.enc_inj (by rw [R6.enc_mul, hrx.symm])
      rw [h1, mul_assoc, zB_mul_self, mul_one]
      exact hy

theorem chk_core :
    ∀ x : P6, R6.enc x ∈ s06L → (∀ b : P6, R6.enc (b * x * b⁻¹) ∈ s06L) → x = 1 := by
  decide +kernel

theorem core_S06 {x : P6} (h : ∀ b : P6, b * x * b⁻¹ ∈ S06) : x = 1 :=
  chk_core x (mem_S06_iff.1 (by simpa using h 1)) fun b => mem_S06_iff.1 (h b)

private theorem conj_mem_A6 {n y : P6} (hy : y ∈ A6s) : n * y * n⁻¹ ∈ A6s := by
  rw [Equiv.Perm.mem_alternatingGroup] at hy ⊢
  rw [map_mul, map_mul, map_inv, hy, mul_one, mul_inv_cancel]

theorem normalizer_S06 : Subgroup.normalizer (S06 : Set P6) = S06 := by
  refine le_antisymm (fun n hn => normalizer_D0_le ?_) fun n hn => ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn' := Subgroup.mem_normalizer_iff.1 hn y
    constructor
    · intro hy
      exact mem_of_mem_extZ_of_mem (hn'.1 (Or.inl hy)) (conj_mem_A6 (D0_le_A6 hy))
    · intro hy
      have hyA : y ∈ A6s := by
        have := conj_mem_A6 (n := n⁻¹) (D0_le_A6 hy)
        simpa [mul_assoc] using this
      exact mem_of_mem_extZ_of_mem (hn'.2 (Or.inl hy)) hyA
  · exact (Subgroup.mem_normalizer_iff).2 fun y => by
      constructor
      · intro hy; exact S06.mul_mem (S06.mul_mem hn hy) (S06.inv_mem hn)
      · intro hy
        have := S06.mul_mem (S06.mul_mem (S06.inv_mem hn) hy) hn
        simpa [mul_assoc] using this

theorem chk_comm : ∀ s : P6, R6.enc s ∈ s06L → zA * s = s * zA ∧ zB * s = s * zB := by
  decide +kernel

theorem Z6_comm {z s : P6} (hz : z ∈ Z6) (hs : s ∈ S06) : z * s = s * z := by
  obtain ⟨hA, hB⟩ := chk_comm s (mem_S06_iff.1 hs)
  rcases hz with hz | hz
  · rcases mem_inf_VA_VB hz with rfl | rfl
    · simp
    · exact hA
  · rcases mem_inf_VA_VB hz with h | h
    · have : z = zB := by
        calc z = z * zB * zB := by rw [mul_assoc, zB_mul_self, mul_one]
          _ = zB := by rw [h, one_mul]
      rw [this]; exact hB
    · have : z = zA * zB := by
        calc z = z * zB * zB := by rw [mul_assoc, zB_mul_self, mul_one]
          _ = zA * zB := by rw [h]
      rw [this, mul_assoc, hB, ← mul_assoc, hA, mul_assoc]

theorem chk_cent : ∀ x : P6, x * zA = zA * x → x * zB = zB * x →
    R6.enc x ∈ d0L ∨ R6.enc (x * zB) ∈ d0L := by
  decide +kernel

theorem zA_mem_Z6 : zA ∈ Z6 := Or.inl ⟨zA_mem_VA, zA_mem_VB⟩

theorem mem_S06_of_comm_Z6 {c : P6} (h : ∀ z ∈ Z6, z * c = c * z) : c ∈ S06 := by
  rcases chk_cent c (h zA zA_mem_Z6).symm (h zB zB_mem_extZ).symm with h1 | h1
  · exact Or.inl ((mem_D0 c).2 h1)
  · exact Or.inr ((mem_D0 _).2 h1)

theorem exists_between_S06 : ∃ Q : Subgroup P6, S06 < Q ∧ Q < ⊤ := by
  refine ⟨Subgroup.centralizer ({zB} : Set P6), ?_, ?_⟩
  · refine lt_of_le_of_ne ?_ ?_
    · intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hs with hs | hs
      · exact (zB_comm_D0 hs).symm
      · exact (zB_comm_of_mul_mem hs).symm
    · intro heq
      have h1 : swap (0 : Fin 6) 1 ∈ Subgroup.centralizer ({zB} : Set P6) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        decide
      rw [← heq, mem_S06_iff] at h1
      revert h1
      decide +kernel
  · refine lt_top_iff_ne_top.2 fun htop => ?_
    have h1 : swap (0 : Fin 6) 4 ∈ Subgroup.centralizer ({zB} : Set P6) := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    revert h1
    decide

theorem le_normalizer_twoGen {Q : Type*} [Group Q] (P : Subgroup Q) :
    P ≤ Subgroup.normalizer (ASInputs.twoGen P : Set Q) := by
  have key : ∀ p ∈ P, ∀ x ∈ ASInputs.twoGen P, p * x * p⁻¹ ∈ ASInputs.twoGen P := by
    intro p hp x hx
    have h : ASInputs.twoGen P ≤ (ASInputs.twoGen P).comap (MulAut.conj p).toMonoidHom := by
      rw [ASInputs.twoGen, Subgroup.closure_le]
      rintro y ⟨hyP, m, hm⟩
      refine Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hp hyP) (P.inv_mem hp), m, ?_⟩
      show (p * y * p⁻¹) ^ 2 ^ m = 1
      rw [conj_pow, hm, mul_one, mul_inv_cancel]
    exact h hx
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key p hp x, fun hx => ?_⟩
  have := key p⁻¹ (P.inv_mem hp) _ hx
  rwa [inv_inv, show p⁻¹ * (p * x * p⁻¹) * p = x by group] at this

theorem not_Z6_le_rootGroupOf {P : Subgroup P6} (hS : IsSylowTwoOf S06 (⊤ : Subgroup P6))
    (hP : IsMaxParabolic2 (⊤ : Subgroup P6) P) (hSP : S06 ≤ P) :
    ¬ Z6 ≤ ASInputs.rootGroupOf P := by
  intro hZ
  have h1 : S06 ≤ ASInputs.twoGen P := by
    intro s hs
    obtain ⟨k, hk⟩ := hS.2.1 ⟨s, hs⟩
    exact Subgroup.subset_closure ⟨hSP hs, k, congrArg Subtype.val hk⟩
  have h2 : ASInputs.twoGen P ≤ S06 := by
    intro x hx
    refine mem_S06_of_comm_Z6 fun z hz => ?_
    have := (Subgroup.mem_centralizer_iff.1 (hZ hz).2) x hx
    exact this.symm
  have h3 : ASInputs.twoGen P = S06 := le_antisymm h2 h1
  have h4 : P ≤ S06 := by
    have := le_normalizer_twoGen P
    rwa [h3, normalizer_S06] at this
  have h5 : P = S06 := le_antisymm h4 hSP
  obtain ⟨Q, hQ1, hQ2⟩ := exists_between_S06
  have hQpar : IsParabolic2 (⊤ : Subgroup P6) Q :=
    ⟨le_top, S06, hS, by rw [top_inf_eq, normalizer_S06]; exact hQ1.le⟩
  have := hP.2.2 Q hQpar hQ2.ne (h5 ▸ hQ1.le)
  rw [h5] at this
  exact hQ1.ne this.symm

end CFSG.Quasithin.RonanE27
