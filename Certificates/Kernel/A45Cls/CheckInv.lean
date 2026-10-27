
module

public import Certificates.Kernel.A45Cls.GlueInv

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
  CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.ConjOrb Certificates.OmegaInv
  Certificates.OmegaF1051 CFSG.ComponentClassification.RankTwoHypIICover.U42

local notation "P45" => Equiv.Perm (Fin 45)

section CloseL

variable (s : P45)

theorem i7inner_mono : ∀ (gl acc : List P45) (x : P45), x ∈ acc →
    x ∈ gl.foldl (fun acc' g => if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc
  | [], _, _, hx => hx
  | g :: gl, acc, x, hx => by
    refine i7inner_mono gl _ x ?_
    simp only
    split_ifs
    · exact hx
    · exact List.mem_append_left _ hx

theorem i7inner_hit : ∀ (gl acc : List P45), ∀ g ∈ gl,
    s * g ∈ gl.foldl (fun acc' g => if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc
  | [], _, g, hg => absurd hg List.not_mem_nil
  | g' :: gl, acc, g, hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · refine i7inner_mono s gl _ _ ?_
      simp only
      split_ifs with h
      · exact h
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact i7inner_hit gl _ g hg

theorem i7inner_nodup : ∀ (gl acc : List P45), acc.Nodup →
    (gl.foldl (fun acc' g => if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc).Nodup
  | [], _, h => h
  | g :: gl, acc, h => by
    refine i7inner_nodup gl _ ?_
    simp only
    split_ifs with hm
    · exact h
    · rw [← List.concat_eq_append]
      exact h.concat hm

theorem i7outer_mono (gl0 : List P45) : ∀ (l acc : List P45) (x : P45), x ∈ acc →
    x ∈ l.foldl (fun acc s => gl0.foldl (fun acc' g =>
      if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc) acc
  | [], _, _, hx => hx
  | s :: l, acc, x, hx => i7outer_mono gl0 l _ x (i7inner_mono s gl0 acc x hx)

theorem i7outer_hit (gl0 : List P45) : ∀ (l acc : List P45), ∀ s ∈ l, ∀ g ∈ gl0,
    s * g ∈ l.foldl (fun acc s => gl0.foldl (fun acc' g =>
      if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc) acc
  | [], _, s, hs, _, _ => absurd hs List.not_mem_nil
  | s' :: l, acc, s, hs, g, hg => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact i7outer_mono gl0 l _ _ (i7inner_hit s gl0 acc g hg)
    · exact i7outer_hit gl0 l _ s hs g hg

theorem i7outer_nodup (gl0 : List P45) : ∀ (l acc : List P45), acc.Nodup →
    (l.foldl (fun acc s => gl0.foldl (fun acc' g =>
      if s * g ∈ acc' then acc' else acc' ++ [s * g]) acc) acc).Nodup
  | [], _, h => h
  | s :: l, acc, h => i7outer_nodup gl0 l _ (i7inner_nodup s gl0 acc h)

end CloseL

theorem i7close_mono (gl0 : List P45) : ∀ (n : ℕ) (S : List P45) (x : P45), x ∈ S →
    x ∈ closeL gl0 n S
  | 0, _, _, hx => hx
  | n + 1, S, x, hx => i7close_mono gl0 n _ x (i7outer_mono gl0 S S x hx)

theorem i7close_step (gl0 : List P45) : ∀ (n : ℕ) (S : List P45) (x : P45),
    x ∈ closeL gl0 n S → ∀ g ∈ gl0, x * g ∈ closeL gl0 (n + 1) S
  | 0, S, x, hx, g, hg => i7outer_hit gl0 S S x hx g hg
  | n + 1, S, x, hx, g, hg => i7close_step gl0 n (stepL gl0 S) x hx g hg

theorem i7close_nodup (gl0 : List P45) : ∀ (n : ℕ) (S : List P45), S.Nodup →
    (closeL gl0 n S).Nodup
  | 0, _, h => h
  | n + 1, S, h => i7close_nodup gl0 n _ (i7outer_nodup gl0 S S h)

theorem i7close_word (gl0 : List P45) (l : List P45) (hl : ∀ g ∈ l, g ∈ gl0) :
    ∀ n, l.length ≤ n → l.prod ∈ closeL gl0 n [1] := by
  induction l using List.reverseRecOn with
  | nil =>
    intro n _
    exact i7close_mono gl0 n [1] 1 (List.mem_singleton_self _)
  | append_singleton l g ih =>
    intro n hn
    rw [List.length_append, List.length_singleton] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [List.prod_append, List.prod_singleton]
    exact i7close_step gl0 m [1] _ (ih (fun g' hg' => hl g' (List.mem_append_left _ hg')) m
      (by omega)) g (hl g (List.mem_append_right _ (List.mem_singleton_self _)))

abbrev K0 : Subgroup P45 := closure (i7kg '' {k | k < 2})

theorem i7kg_mem_list {k : ℕ} (hk : k < 2) : i7kg k ∈ [k1 (), k2 ()] := by
  interval_cases k
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem k0_words {c : ℕ → P45} (hc : ∀ i < 120, PRep 45 6 (K0Z.T i) (c i)) (hc0 : c 0 = 1) :
    ∀ d, ∀ i < 120, tDep (K0Z.D i) = d →
      ∃ l : List P45, (∀ g ∈ l, g ∈ [k1 (), k2 ()]) ∧ l.length ≤ d ∧ l.prod = c i := by
  have hN : K0Z.N = 120 := i7binds.2.2.1
  have hng : K0Z.ng = 2 := i7binds.2.2.2.1
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi hd
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨[], by simp, by simp, by rw [hc0]; rfl⟩
    · have htr : treePt 2 120 0 K0Z.E K0Z.D i = true := K0Z.tr i (by omega)
      obtain ⟨hp, hlab, he, hdep⟩ := treePt_spec htr hi0
      obtain ⟨l, hl, hlen, hprod⟩ := ih _ (by omega) _ hp rfl
      have hcl : closPtL 45 6 2 120 K0Z.G K0Z.T K0Z.E (tPar (K0Z.D i)) = true :=
        K0Z.cl _ (by omega)
      obtain ⟨-, hstep⟩ := closPtL_spec hcl
      obtain ⟨-, hT⟩ := hstep _ hlab
      rw [he] at hT
      have hpr := prep_pcomp hn45 (prep_i7kg _ hlab) (hc _ hp)
      rw [hT] at hpr
      refine ⟨i7kg (tLab (K0Z.D i)) :: l, fun g hg => ?_, by simp; omega, ?_⟩
      · rcases List.mem_cons.1 hg with rfl | hg
        · exact i7kg_mem_list hlab
        · exact hl g hg
      · rw [List.prod_cons, hprod]
        exact prep_eq hpr (hc i hi)

theorem mem_k0List_iff {x : P45} : x ∈ k0List () ↔ x ∈ K0 := by
  constructor
  · intro hx
    refine CFSG.OddStandard.SmallF3.Omega.Mo107.closeL_mem (fun g hg => ?_) 16 [1]
      (fun s hs => ?_) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact subset_closure ⟨0, by norm_num, rfl⟩
      · exact subset_closure ⟨1, by norm_num, rfl⟩
    · rw [List.mem_singleton.1 hs]
      exact one_mem _
  · intro hx
    obtain ⟨c, hc, hall, -⟩ := k0_enum
    obtain ⟨i, hi, rfl⟩ := hall x hx
    have hc0 : c 0 = 1 := by
      have h := (hc 0 (by norm_num)).1
      rw [i7binds.2.2.2.2.1] at h
      exact prep_eq h prep_pid
    obtain ⟨l, hl, hlen, hprod⟩ := k0_words (fun i hi => (hc i hi).1) hc0 _ i hi rfl
    rw [← hprod]
    have hdep := allN_spec i7binds.2.2.2.2.2 i hi
    exact i7close_word _ l hl 16 (by have := Nat.le_of_ble_eq_true hdep; omega)

theorem k0_core : ∀ d ∈ QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45),
    (∀ g ∈ QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45), g * d * g⁻¹ ∈ K0) →
      d = 1 := by
  obtain ⟨c, hc, hall, -⟩ := k0_enum
  intro d hd hdK
  have hd1 : d ∈ K0 := by
    have := hdK 1 (one_mem _)
    rwa [one_mul, inv_one, mul_one] at this
  obtain ⟨i, hi, rfl⟩ := hall d hd1
  have hk := i7core.2.2
  rw [i7coreK] at hk
  have h := allN_spec hk i hi
  beta_reduce at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact (isIdK_iff (hc i hi).1).1 h
  · obtain ⟨j, hj, hj'⟩ := exN_spec h
    obtain ⟨hgD, hgP, hgiP⟩ := i7g_D j hj
    obtain ⟨i', hi', e⟩ := hall _ (hdK _ hgD)
    have hp := prep_pcomp hn45 hgP (prep_pcomp hn45 (hc i hi).1 hgiP)
    rw [← mul_assoc, ← e] at hp
    have := inPts_of hi' (hc i' hi').1 hp
    have h3 : (!inPts 45 6 120 K0Z.T (pcomp 45 6 (mask 6) (i7gP j)
        (pcomp 45 6 (mask 6) (K0Z.T i) (i7giP j)))) = true := hj'
    rw [this] at h3
    exact absurd h3 (by decide)

theorem k0List_nodup : (k0List ()).Nodup := i7close_nodup _ 16 [1] (List.nodup_singleton _)

theorem k0List_length : (k0List ()).length = 120 := by
  obtain ⟨-, -, -, hcard⟩ := k0_enum
  have h : Nat.card ↥K0 = (k0List ()).length :=
    card_eq_length (fun g : P45 => g ∈ K0) id Function.injective_id (k0List ())
      k0List_nodup (fun b => ⟨fun hb => ⟨b, mem_k0List_iff.1 hb, rfl⟩,
        fun ⟨a, ha, hab⟩ => hab ▸ mem_k0List_iff.2 ha⟩)
  rw [← h]
  exact hcard

theorem cntL_eq (a : P45) :
    cntL (elemsT QA45) a =
      Nat.card ↥(QA45.originalSubgroup ⊓ centralizer ({a} : Set P45)) := by
  rw [cntL, card_inf_centralizer QA45 QA45_ok]

theorem i7mem_d0 {y x : P45} :
    x ∈ d0List (elemsT QP45) y ↔ x ∈ QP45.originalSubgroup ∧ x * y = y * x := by
  simp only [d0List, List.mem_filter, decide_eq_true_eq, mem_elemsT QP45 QP45_ok]

theorem omegaInv_check : Certificates.OmegaInv.check () = true := by
  have F := facts442007
  have hrep : repChk (elemsT QA45) (elemsT QP45) = true := by
    unfold repChk
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, mem_elemsT QA45 QA45_ok, mem_elemsT QP45 QP45_ok, cntL_eq]
    exact ⟨⟨⟨⟨⟨⟨F.rep, F.z0_mem⟩, F.yB_mem⟩, F.r3_not⟩, F.r4_not⟩, F.cent⟩, F.fix⟩
  have hcov : coverAll (reps ()) (elemsT QA45) (elemsT QP45) = true := by
    unfold coverAll
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.any_eq_true, decide_eq_true_eq, mem_elemsT QA45 QA45_ok, mem_elemsT QP45 QP45_ok]
    intro t ht
    by_cases h : t * t = 1 ∧ t ≠ 1
    · exact Or.inr (F.cover t ht h.1 h.2)
    · exact Or.inl h
  have hlay : layerChk (elemsT QP45) (r4 ()) = true := by
    unfold layerChk
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true,
      i7mem_d0, mem_k0List_iff]
    have hD : (d0List (elemsT QP45) (r4 ())).length = 720 := by
      rw [d0List, ← card_inf_centralizer QP45 QP45_ok]
      exact card_D
    have hKD : ∀ a ∈ K0, a ∈ QP45.originalSubgroup ∧ a * r4 () = r4 () * a := by
      intro a ha
      have hle : K0 ≤ QP45.originalSubgroup ⊓ centralizer ({r4 ()} : Set P45) := by
        rw [closure_le]
        rintro _ ⟨k, hk, rfl⟩
        exact i7kg_D k hk
      have := hle ha
      exact ⟨(mem_inf.1 this).1, mem_centralizer_singleton_iff.1 (mem_inf.1 this).2⟩
    refine ⟨⟨⟨⟨⟨hD, k0List_length, k0List_nodup⟩, one_mem _⟩, fun a ha =>
      ⟨inv_mem ha, fun b hb => mul_mem ha hb⟩⟩, hKD⟩, fun d hd => ?_⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    refine Or.inr (by_contra fun hno => hd1 (k0_core d ((mem_inf.2 ⟨hd.1,
      mem_centralizer_singleton_iff.2 hd.2⟩)) fun g hg => ?_))
    by_contra hgK
    exact hno ⟨g, ⟨(mem_inf.1 hg).1, mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2⟩, hgK⟩
  simp only [Certificates.OmegaInv.check, Bool.and_eq_true]
  exact ⟨⟨hrep, hcov⟩, hlay⟩

theorem omegaQ2m_check : Certificates.OmegaQ2m.check () = true := by
  have F := facts442019
  simp only [Certificates.OmegaQ2m.check, Certificates.OmegaQ2m.conjChk,
    Certificates.OmegaQ2m.qChk, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    mem_elemsT QP45 QP45_ok, cntL_eq]
  refine ⟨F.conj, fun q hq => ?_⟩
  by_cases h2 : q * q = 1
  · by_cases h1 : q = 1
    · exact Or.inl (Or.inl (Or.inr h1))
    · by_cases hz : q = Certificates.OmegaT0.z0 ()
      · exact Or.inl (Or.inr hz)
      · exact Or.inr (F.q q hq h2 h1 hz)
  · exact Or.inl (Or.inl (Or.inl h2))

end CertificateChecks.KernelA45

end
