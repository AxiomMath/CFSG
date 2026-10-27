module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
public import CFSG.Quasithin.Vol2.KGFactC31ArrChain
public import CFSG.Quasithin.Vol2.KGFactC31BadScan
public import CFSG.Sporadic.Schreier.RuCentralizer
public import CFSG.Sporadic.Schreier.RuConj

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31 CFSG.Certificates

@[expose] noncomputable def g6G : List (Equiv.Perm (Fin 4060)) :=
  [ruA0, ruA1, ruC0, ruC1, ruNs0, ruNs1]

@[expose] noncomputable def wG (w : List ℤ) : Equiv.Perm (Fin 4060) := evalSigned g6G w

theorem ruNs0_mem' : ruNs0 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN0_mem) (ruP.inv_mem ruH_mem)

theorem ruNs1_mem' : ruNs1 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN1_mem) (ruP.inv_mem ruH_mem)

theorem g6G_mem : ∀ g ∈ g6G, g ∈ ruP := by
  intro g hg
  simp only [g6G, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ruA0_mem
  · exact ruA1_mem
  · exact ruC0_mem
  · exact ruC1_mem
  · exact ruNs0_mem'
  · exact ruNs1_mem'

theorem wG_mem (w : List ℤ) : wG w ∈ ruP := evalSigned_mem g6G_mem w

theorem rep_getD_six {t₀ t₁ t₂ t₃ t₄ t₅ : Array ℕ}
    {g₀ g₁ g₂ g₃ g₄ g₅ : Equiv.Perm (Fin 4060)} (h₀ : Rep 4060 t₀ g₀) (h₁ : Rep 4060 t₁ g₁)
    (h₂ : Rep 4060 t₂ g₂) (h₃ : Rep 4060 t₃ g₃) (h₄ : Rep 4060 t₄ g₄) (h₅ : Rep 4060 t₅ g₅) :
    ∀ h < 6, Rep 4060 #[t₀, t₁, t₂, t₃, t₄, t₅][h]! ([g₀, g₁, g₂, g₃, g₄, g₅].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃
  · simpa using h₄
  · simpa using h₅

theorem rep_g6 :
    ∀ h < 6, Rep 4060 g6A[h]! (g6G.getD h 1) :=
  rep_getD_six rep_ruA0 rep_ruA1 rep_ruC0 rep_ruC1 rep_ruNs0 rep_ruNs1

theorem rep_g6I :
    ∀ h < 6, Rep 4060 g6IA[h]! (g6G.getD h 1)⁻¹ := by
  intro h hh
  have e : g6IA[h]! = ruInv g6A[h]! := by
    rw [g6IA, getElem!_pos (g6A.map ruInv) h (by simpa [g6A] using hh), Array.getElem_map,
      getElem!_pos g6A h (by simpa [g6A] using hh)]
  rw [e]
  exact rep_invCand_of_rep (rep_g6 h hh)

theorem rep_wA {w : List ℤ} (hw : lettersOK 6 w = true) :
    Rep 4060 (wA w) (wG w) :=
  rep_wordA_evalSigned rep_g6 rep_g6I w hw

theorem rep_ruInv' {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    Rep 4060 (ruInv t) g⁻¹ :=
  rep_invCand_of_rep ht

theorem evalSigned_mem_of_letters {G : Type*} [Group G] {H : Subgroup G} {gens : List G} :
    ∀ {w : List ℤ}, (∀ l ∈ w, gens.getD (l.natAbs - 1) 1 ∈ H) → evalSigned gens w ∈ H
  | [], _ => H.one_mem
  | l :: w, h => by
    rw [evalSigned_cons]
    refine H.mul_mem ?_ (evalSigned_mem_of_letters fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    split
    · exact h l List.mem_cons_self
    · exact H.inv_mem (h l List.mem_cons_self)

theorem wG_memC {w : List ℤ} (hw : w.all (fun l => l.natAbs == 3 || l.natAbs == 4) = true) :
    wG w ∈ ruC := by
  refine evalSigned_mem_of_letters fun l hl => ?_
  have h := List.all_eq_true.mp hw l hl
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  rcases h with h | h <;> rw [h]
  · exact ruC0_memC
  · exact ruC1_memC

theorem wG_memN {w : List ℤ} (hw : w.all (fun l => l.natAbs == 5 || l.natAbs == 6) = true) :
    wG w ∈ ruN := by
  refine evalSigned_mem_of_letters fun l hl => ?_
  have h := List.all_eq_true.mp hw l hl
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  rcases h with h | h <;> rw [h]
  · exact ruNs0_memN
  · exact ruNs1_memN

theorem rep_getD_two' {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin 4060)}
    (h₀ : Rep 4060 t₀ g₀) (h₁ : Rep 4060 t₁ g₁) :
    ∀ h < 2, Rep 4060 #[t₀, t₁][h]! ([g₀, g₁].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_getD_two_inv' {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin 4060)}
    (h₀ : Rep 4060 t₀ g₀⁻¹) (h₁ : Rep 4060 t₁ g₁⁻¹) :
    ∀ h < 2, Rep 4060 #[t₀, t₁][h]! ([g₀, g₁].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem ab_gens :
    (∀ h < 2, Rep 4060 (#[ruA0A, ruA1A] : Array (Array ℕ))[h]! ([ruA0, ruA1].getD h 1)) ∧
      ∀ h < 2, Rep 4060 (#[ruInv ruA0A, ruInv ruA1A] : Array (Array ℕ))[h]!
        ([ruA0, ruA1].getD h 1)⁻¹ :=
  ⟨rep_getD_two' rep_ruA0 rep_ruA1, rep_getD_two_inv' (rep_ruInv' rep_ruA0) (rep_ruInv' rep_ruA1)⟩

theorem rep_abA {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (abA w) (evalSigned [ruA0, ruA1] w) :=
  rep_wordA_evalSigned ab_gens.1 ab_gens.2 w hw

theorem evalSigned_ab_mem (w : List ℤ) : evalSigned [ruA0, ruA1] w ∈ ruP :=
  evalSigned_mem (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ruA0_mem
    · exact ruA1_mem) w

theorem rep_conjA {h t : Array ℕ} {hg tg : Equiv.Perm (Fin 4060)} (hh : Rep 4060 h hg)
    (ht : Rep 4060 t tg) : Rep 4060 (conjA h t) (hg * tg * hg⁻¹) :=
  rep_compA (rep_compA hh ht) (rep_ruInv' hh)

theorem isInvA_self_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    isInvA 4060 t t = true ↔ g * g = 1 := by
  constructor
  · intro h
    have h1 := Rep.unique (rep_inv_of_isInvA ht h) ht
    have h2 := mul_inv_cancel g
    rwa [h1] at h2
  · intro hg
    rw [isInvA, allLt_iff]
    intro i hi
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨Rep.lt ht hi, ?_⟩
    have key : t[((g ⟨i, hi⟩ : Fin 4060) : ℕ)]! = i := by
      rw [ht (g ⟨i, hi⟩)]
      have := congrArg (fun f : Equiv.Perm (Fin 4060) => (f ⟨i, hi⟩ : ℕ)) hg
      simpa using this
    rw [ht.apply hi]
    exact key

theorem length_fixedList_eq {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    (fixedList 4060 t).length = (fixSet g).ncard := by
  rw [← ncard_finSet (pointList_fixedList t), finSet_fixedList ht]

theorem ebasis_of_ebasisA {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {bs : List (Array ℕ)}
    (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) (h : ebasisA bs = true) : EBasis v := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  simp only [ebasisA, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsq, hcomm⟩, hne⟩ := h
  have hrep : ∀ i : Fin k, ∃ b ∈ bs, Rep 4060 b (v i) := fun i =>
    KGC31.exists_left_of_forall₂ hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
  refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
  · obtain ⟨b, hb, hbi⟩ := hrep i
    have h1 := Rep.unique (rep_inv_of_isInvA hbi (hsq b hb)) hbi
    have h2 := inv_mul_cancel (v i)
    rwa [h1] at h2
  · obtain ⟨b, hb, hbi⟩ := hrep i
    obtain ⟨b', hb', hbj⟩ := hrep j
    exact (commA_iff hbi hbj).mp (hcomm b hb b' hb')
  · obtain ⟨m, hm, rfl⟩ := exists_maskVec c
    have h1 := hne m (by rw [List.mem_range, hlen]; exact hm)
    rw [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h0 | h1
    · subst h0
      funext i
      simp [maskVec]
    · exfalso
      rw [Bool.not_eq_true'] at h1
      have h2 := (eqA_iff (rep_maskA v bs hbs m) rep_idA).mpr hc
      rw [h1] at h2
      exact absurd h2 (by decide)

theorem centA_iff {bs : List (Array ℕ)} {gs : List (Equiv.Perm (Fin 4060))}
    (hbs : List.Forall₂ (Rep 4060) bs gs) {c : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (hc : Rep 4060 c g) : centA bs c = true ↔ ∀ b ∈ gs, g * b = b * g := by
  rw [centA, List.all_eq_true]
  constructor
  · intro h b hb
    obtain ⟨t, ht, htb⟩ := KGC31.exists_left_of_forall₂ hbs hb
    exact (commA_iff hc htb).mp (h t ht)
  · intro h t ht
    obtain ⟨b, hb, htb⟩ := KGC31.exists_right_of_forall₂ hbs ht
    exact (commA_iff hc htb).mpr (h b hb)

theorem rep_pA {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    ∀ k, Rep 4060 (pA k t) (g ^ k)
  | 0 => by simpa [pA] using (rep_idA : Rep 4060 (idA 4060) 1)
  | k + 1 => by
    rw [pA, pow_succ']
    exact rep_compA ht (rep_pA ht k)

theorem orbCommA_iff {x xi c : Array ℕ} {gx gc : Equiv.Perm (Fin 4060)} (hx : Rep 4060 x gx)
    (hxi : Rep 4060 xi gx⁻¹) (hc : Rep 4060 c gc) (m : ℕ) :
    orbCommA x xi m c = true ↔
      ∀ j < m, gc * (gx ^ (j + 1) * gc * (gx ^ (j + 1))⁻¹) =
        gx ^ (j + 1) * gc * (gx ^ (j + 1))⁻¹ * gc := by
  rw [orbCommA, List.all_eq_true]
  have hrep : ∀ j, Rep 4060 (cjA (pA (j + 1) x) (pA (j + 1) xi) c)
      (gx ^ (j + 1) * gc * (gx ^ (j + 1))⁻¹) := fun j => by
    have h2 := rep_pA hxi (j + 1)
    rw [inv_pow] at h2
    exact rep_cjA (rep_pA hx (j + 1)) h2 hc
  constructor
  · intro h j hj
    exact (commA_iff hc (hrep j)).mp (h j (List.mem_range.mpr hj))
  · intro h j hj
    exact (commA_iff hc (hrep j)).mpr (h j (List.mem_range.mp hj))

theorem twoElt_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) (k : ℕ) :
    twoElt k t = true ↔ g ^ 2 ^ k = 1 := by
  rw [twoElt]
  exact eqA_iff (rep_sqIterA ht k) rep_idA

theorem normsA_iff {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {sp : List (Array ℕ)}
    {bv : List (Array ℕ)} (hbv : List.Forall₂ (Rep 4060) bv (List.ofFn v)) (hsp : sp = spanA bv)
    {bs : List (Array ℕ)} {gs : List (Equiv.Perm (Fin 4060))}
    (hbs : List.Forall₂ (Rep 4060) bs gs) {t ti : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (ht : Rep 4060 t g) (hti : Rep 4060 ti g⁻¹) :
    normsA t ti bs sp = true ↔ ∀ b ∈ gs, ∃ c, eElt v c = g * b * g⁻¹ := by
  subst hsp
  rw [normsA, List.all_eq_true]
  constructor
  · intro h b hb
    obtain ⟨u, hu, hub⟩ := KGC31.exists_left_of_forall₂ hbs hb
    exact (inA_spanA_iff hbv (rep_cjA ht hti hub)).mp (h u hu)
  · intro h u hu
    obtain ⟨b, hb, hub⟩ := KGC31.exists_right_of_forall₂ hbs hu
    exact (inA_spanA_iff hbv (rep_cjA ht hti hub)).mpr (h b hb)

theorem normPre_of {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {bs : List (Array ℕ)}
    (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) {c : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (hc : Rep 4060 c g) (hn : ∀ i, ∃ d, eElt v d = g * v i * g⁻¹) :
    normPre c bs (spanA bs) = true := by
  rw [normPre, Bool.and_eq_true]
  have hnorm : normsA c (ruInv c) bs (spanA bs) = true := by
    refine (normsA_iff hbs rfl hbs hc (rep_ruInv' hc)).mpr fun b hb => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact hn i
  refine ⟨?_, hnorm⟩
  rw [List.all_eq_true]
  intro b hb
  rw [normsA, List.all_eq_true] at hnorm
  have h1 := hnorm b hb
  rw [inA, List.any_eq_true] at h1
  rw [List.any_eq_true]
  obtain ⟨u, hu, hue⟩ := h1
  refine ⟨u, hu, ?_⟩
  obtain ⟨gb, -, hgb⟩ := KGC31.exists_right_of_forall₂ hbs hb
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hu
  have hrm := rep_maskA v bs hbs m
  have hcj := rep_cjA hc (rep_ruInv' hc) hgb
  have heq := eq_of_eqA hrm hcj hue
  rw [beq_iff_eq]
  have e1 : ∀ (t : Array ℕ) (i : ℕ), t.getD i 0 = t[i]! := fun t i => Array.getElem!_eq_getD.symm
  have h0 : (0 : ℕ) < 4060 := by norm_num
  rw [e1, e1, e1, e1, hc.apply h0, hgb.apply h0, hrm (g ⟨0, h0⟩), hc (gb ⟨0, h0⟩), heq]
  simp [Equiv.Perm.mul_apply]

end CFSG.Quasithin.KGC31.Ru

end
