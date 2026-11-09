module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1
public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.T1

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin
  CFSG.Quasithin.F53.Stellmacher.S35.At

@[expose] def stepF (T X : Finset (Perm (Fin 5))) : Finset (Perm (Fin 5)) :=
  X ∪ X.biUnion fun x => T.image fun t => x * t

@[expose] def ballF (T : Finset (Perm (Fin 5))) : ℕ → Finset (Perm (Fin 5))
  | 0 => {1}
  | n + 1 => stepF T (ballF T n)

@[expose] def ptF : Finset (Perm (Fin 5)) := Finset.univ.filter fun x => x 4 = 4

namespace BallK

open CFSG.Permutation.FinPack CFSG.Quasithin.F53.Stellmacher.S35.At.InvStabK

@[expose] noncomputable def addK (c : ℕ) (L : List ℕ) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ) (c :: L) L (memK c L)

@[expose] noncomputable def stepK (TK L : List ℕ) : List ℕ :=
  (L.flatMap fun a => TK.map fun t => mulK 5 a t).foldr addK L

@[expose] noncomputable def ballK (TK : List ℕ) (n : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [e5] (fun _ L => stepK TK L) n

@[expose] def ptL : List ℕ :=
  [274960, 271120, 274720, 267040, 270640, 266800, 274945, 271105, 274465, 262945, 270385,
    262705, 274690, 267010, 274450, 262930, 266290, 262450, 270595, 266755, 270355, 262675,
    266275, 262435]

@[expose] def sylL : List ℕ := [274960, 262945, 266290, 270595, 274450, 262435, 266800, 271105]

@[expose] def c02 : ℕ := 274450

@[expose] def c13 : ℕ := 266800

theorem pt_walk : walkK 5 (fun c => !Nat.beq (rd c 4) 4 || memK c ptL) 5 0 0 0 = true := by
  decide +kernel

theorem ball_chk : allK (fun x => memK x sylL ||
    allK (fun y => memK y (ballK [c02, c13, x] 8)) ptL) ptL = true := by
  decide +kernel

theorem c02_enc : enc (swap 0 2 : Perm (Fin 5)) = c02 := by
  unfold c02
  decide +kernel

theorem c13_enc : enc (swap 1 3 : Perm (Fin 5)) = c13 := by
  unfold c13
  decide +kernel

theorem sylL_eq : sylL = [enc (1 : Perm (Fin 5)), enc S5g, enc (S5g ^ 2), enc (S5g ^ 3),
    enc (swap 0 2 : Perm (Fin 5)), enc (S5g * swap 0 2), enc (S5g ^ 2 * swap 0 2),
    enc (S5g ^ 3 * swap 0 2)] := by
  unfold sylL
  decide +kernel

theorem mem_S5SylF_of_code (σ : Perm (Fin 5)) (h : memK (enc σ) sylL = true) : σ ∈ S5SylF := by
  have hn : 5 ≤ 16 := by norm_num
  have e : ∀ τ : Perm (Fin 5), enc σ = enc τ ↔ σ = τ := fun τ => ⟨enc_inj hn, congrArg enc⟩
  rw [sylL_eq, memK_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, e] at h
  unfold S5SylF
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

theorem ballK_succ (TK : List ℕ) (n : ℕ) : ballK TK (n + 1) = stepK TK (ballK TK n) := rfl

theorem mem_addK {x c : ℕ} {L : List ℕ} (h : x ∈ addK c L) : x = c ∨ x ∈ L := by
  unfold addK at h
  revert h
  cases memK c L
  · intro h
    exact List.mem_cons.1 h
  · intro h
    exact Or.inr h

theorem mem_foldr_addK {c : ℕ} {L : List ℕ} : ∀ M : List ℕ, c ∈ M.foldr addK L → c ∈ M ∨ c ∈ L
  | [], h => Or.inr h
  | d :: M, h => by
    rw [List.foldr_cons] at h
    rcases mem_addK h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases mem_foldr_addK M h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem mem_stepK {c : ℕ} {TK L : List ℕ} (h : c ∈ stepK TK L) :
    c ∈ L ∨ ∃ a ∈ L, ∃ t ∈ TK, c = mulK 5 a t := by
  unfold stepK at h
  rcases mem_foldr_addK _ h with h | h
  · obtain ⟨a, ha, h⟩ := List.mem_flatMap.1 h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    exact Or.inr ⟨a, ha, t, ht, rfl⟩
  · exact Or.inl h

theorem ballK_sound (T : Finset (Perm (Fin 5))) (TK : List ℕ)
    (hT : ∀ t ∈ TK, ∃ τ ∈ T, enc τ = t) : ∀ n, ∀ c ∈ ballK TK n, ∃ g ∈ ballF T n, enc g = c := by
  have hn : 5 ≤ 16 := by norm_num
  intro n
  induction n with
  | zero =>
    intro c hc
    have hc' : c = e5 := List.mem_singleton.1 hc
    exact ⟨1, by simp [ballF], by rw [hc', e5_enc]⟩
  | succ n ih =>
    intro c hc
    rw [ballK_succ] at hc
    rcases mem_stepK hc with hc | ⟨a, ha, t, ht, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := ih c hc
      refine ⟨g, ?_, rfl⟩
      simp only [ballF, stepF]
      exact Finset.mem_union_left _ hg
    · obtain ⟨g, hg, rfl⟩ := ih a ha
      obtain ⟨τ, hτ, rfl⟩ := hT t ht
      refine ⟨g * τ, ?_, enc_mul hn g τ⟩
      simp only [ballF, stepF]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image.2 ⟨τ, hτ, rfl⟩⟩)

end BallK

open CFSG.Permutation.FinPack BallK in
theorem ptF_le_ballF : ∀ x ∈ ptF, x ∉ S5SylF → ptF ⊆ ballF {swap 0 2, swap 1 3, x} 8 := by
  intro x hx hxS y hy
  have hn : 5 ≤ 16 := by norm_num
  have hcode : ∀ z ∈ ptF, memK (enc z) ptL = true := by
    intro z hz
    have h4 : rd (enc z) 4 = 4 := by
      have h := rd_enc hn z 4
      rw [(Finset.mem_filter.1 hz).2] at h
      exact h
    have h := walkK_sound pt_walk z
    rw [h4, Nat.beq_refl, Bool.not_true, Bool.false_or] at h
    exact h
  have hc := allK_iff.1 ball_chk _ (memK_iff.1 (hcode x hx))
  have hsyl : memK (enc x) sylL = false := by
    cases h : memK (enc x) sylL
    · rfl
    · exact absurd (mem_S5SylF_of_code x h) hxS
  rw [hsyl, Bool.false_or] at hc
  have hy' := allK_iff.1 hc _ (memK_iff.1 (hcode y hy))
  have hT : ∀ t ∈ [c02, c13, enc x], ∃ τ ∈ ({swap 0 2, swap 1 3, x} : Finset (Perm (Fin 5))),
      enc τ = t := by
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨swap 0 2, Finset.mem_insert_self _ _, c02_enc⟩
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨swap 1 3, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), c13_enc⟩
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
      rfl⟩
  obtain ⟨g, hg, he⟩ := ballK_sound _ _ hT 8 _ (memK_iff.1 hy')
  rw [enc_inj hn he] at hg
  exact hg

theorem ptStab_le_of_That_le {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {K : Subgroup (Perm (Fin 5))} (hT : That D ≤ K) (hK : K ≤ ptStab (fixPt D))
    (hnD : ¬ K ≤ D) : ptStab (fixPt D) ≤ K := by
  obtain ⟨g, rfl, hTg, -, hp⟩ := std_data hD
  rw [hp] at hK ⊢
  obtain ⟨x, hxK, hxD⟩ := Set.not_subset.mp hnD
  have hx4 : (g⁻¹ * x * g) 4 = 4 := by
    have h := mem_ptStab.mp (hK hxK)
    simp only [Perm.mul_apply]
    rw [h]
    simp
  have hxS : g⁻¹ * x * g ∉ S5SylF := by
    intro h
    exact hxD (mem_cj.mpr ((mem_S5Syl_iff _).mpr h))
  have hsub := ptF_le_ballF (g⁻¹ * x * g) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx4⟩) hxS
  intro y hy
  have hy4 : (g⁻¹ * y * g) 4 = 4 := by
    have h := mem_ptStab.mp hy
    simp only [Perm.mul_apply]
    rw [h]
    simp
  have hmem := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy4⟩)
  have key : ∀ n, ∀ z ∈ ballF {swap 0 2, swap 1 3, g⁻¹ * x * g} n, g * z * g⁻¹ ∈ K := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [ballF, Finset.mem_singleton] at hz
      rw [hz]
      simp
    | succ n ih =>
      intro z hz
      simp only [ballF, stepF, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hz
      rcases hz with hz | ⟨a, ha, t, ht, rfl⟩
      · exact ih z hz
      · have h1 := ih a ha
        have h2 : g * t * g⁻¹ ∈ K := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · refine hT ?_
            rw [hTg]
            have h0 : (swap 0 2 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
            exact mem_cj.mpr (by simpa [mul_assoc] using h0)
          · refine hT ?_
            rw [hTg]
            have h0 : (swap 1 3 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
            exact mem_cj.mpr (by simpa [mul_assoc] using h0)
          · simpa [mul_assoc] using hxK
        have := K.mul_mem h1 h2
        simpa [mul_assoc] using this
  have := key 8 _ hmem
  simpa [mul_assoc] using this

theorem exists_act_ep_ne {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {x y : Fin 5}
    (hxy : x ≠ y) : ∃ g ∈ D, orth.act g (ep x y) ≠ ep x y := by
  by_contra h
  push Not at h
  have hP : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD]; norm_num)
  have := (card_le_four_of_fix hP hxy h).1
  omega

end CFSG.Quasithin.F53.Stellmacher.S35.T1
