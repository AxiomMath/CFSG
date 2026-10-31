
module

public import CFSG.Quasithin.Vol2.KGFactC31RuCand
public import CFSG.Quasithin.Vol2.KGFactC31RuHyp
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase

@[expose] public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native

theorem forall₂_refBasis (τ : ℕ) :
    List.Forall₂ (Rep 4060) (refBasisA τ) (refG τ) := by
  rcases Nat.lt_or_ge τ 5 with hτ | hτ
  · interval_cases τ
    · exact hbE
    · exact hb64
    · exact hb3
    · exact hb16
    · exact hb32
  · rw [refBasisA, refG, List.getD_eq_default _ _ (by simpa using hτ),
      List.getD_eq_default _ _ (by simpa using hτ)]
    exact .nil

theorem closure_ofFn {k : ℕ} (v : Fin k → Equiv.Perm (Fin 4060)) :
    Subgroup.closure {x | x ∈ List.ofFn v} = refSub v := by
  rw [refSub]
  congr 1
  ext x
  simp [List.mem_ofFn, Set.mem_range]

theorem closure_refG {τ : ℕ} (hτ : τ < 5) : Subgroup.closure {x | x ∈ refG τ} = refU τ := by
  interval_cases τ <;> exact closure_ofFn _

theorem refU_le_ruP (τ : ℕ) : refU τ ≤ ruP := by
  rcases Nat.lt_or_ge τ 5 with hτ | hτ
  · interval_cases τ <;> exact refSub_le_ruP _
  · rw [refU, List.getD_eq_default _ _ (by simpa using hτ)]
    exact bot_le

theorem refG_mem (τ : ℕ) : ∀ x ∈ refG τ, x ∈ ruP := by
  intro x hx
  rcases Nat.lt_or_ge τ 5 with hτ | hτ
  · exact refU_le_ruP τ (by rw [← closure_refG hτ]; exact Subgroup.subset_closure hx)
  · rw [refG, List.getD_eq_default _ _ (by simpa using hτ)] at hx
    exact absurd hx List.not_mem_nil

theorem candData_letters : ∀ c ∈ candData.flatten, lettersOK 6 c.2 = true := by decide +kernel

theorem candData_lt : ∀ c ∈ candData.flatten, c.1 < 5 := by decide +kernel

theorem mem_flatten_of_getD {i : ℕ} {c : ℕ × List ℤ} (hc : c ∈ candData.getD i []) :
    c ∈ candData.flatten := by
  rcases Nat.lt_or_ge i candData.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi] at hc
    exact List.mem_flatten.mpr ⟨_, List.getElem_mem hi, hc⟩
  · rw [List.getD_eq_default _ _ hi] at hc
    exact absurd hc List.not_mem_nil

theorem forall₂_cands (i p : ℕ) :
    List.Forall₂ (List.Forall₂ (RepW 4060)) (candsAt i p) (candsG i p) := by
  rw [candsAt, candsG, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun c hc => ?_
  have hcd := mem_flatten_of_getD (List.mem_of_mem_filter hc)
  have hk := rep_wA (candData_letters c hcd)
  rw [candWords, candElts, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine (forall₂_refBasis c.1).imp fun {b g} hbg => ?_
  have := ((RepW.single (rep_ruInv' hk)).append (RepW.single hbg)).append (RepW.single hk)
  simpa [mul_assoc] using this

theorem candsG_mem (i p : ℕ) : ∀ cg ∈ candsG i p, ∀ x ∈ cg, x ∈ ruP := by
  intro cg hcg x hx
  rw [candsG] at hcg
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hcg
  rw [candElts] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact ruP.mul_mem (ruP.mul_mem (wG_mem _) (refG_mem _ b hb)) (ruP.inv_mem (wG_mem _))

theorem orbSub_conj_of_comm' {c y τ : Equiv.Perm (Fin 4060)} (hc : c * τ = τ * c) :
    (orbSub y τ).map (MulAut.conj c).toMonoidHom = orbSub (c * y * c⁻¹) τ := by
  have h1 : (MulAut.conj c).toMonoidHom τ = τ := by
    show c * τ * c⁻¹ = τ
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [orbSub_map, h1]
  rfl

theorem conj_facts {U : Subgroup (Equiv.Perm (Fin 4060))} {L : List (Equiv.Perm (Fin 4060))}
    (hL : Subgroup.closure {x | x ∈ L} = U) {k c y τ : Equiv.Perm (Fin 4060)}
    (hcτ : c * τ = τ * c)
    (hcg : ∀ x ∈ L.map (fun b => k * b * k⁻¹), x ∈ orbSub (c * y * c⁻¹) τ)
    (hn : ∀ x ∈ L.map (fun b => k * b * k⁻¹), c * y * c⁻¹ * x * (c * y * c⁻¹)⁻¹ ∈
      Subgroup.closure {x | x ∈ L.map (fun b => k * b * k⁻¹)}) :
    U.map (MulAut.conj (c⁻¹ * k)).toMonoidHom ≤ orbSub y τ ∧
      (c⁻¹ * k)⁻¹ * y * (c⁻¹ * k) ∈ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 4060))) := by
  have hcl : Subgroup.closure {x | x ∈ L.map (fun b => k * b * k⁻¹)} =
      U.map (MulAut.conj k).toMonoidHom := by
    rw [← hL, MonoidHom.map_closure]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hcτ' : c⁻¹ * τ = τ * c⁻¹ := by
    calc c⁻¹ * τ = c⁻¹ * (τ * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * τ) * c⁻¹ := by rw [hcτ]
      _ = τ * c⁻¹ := by group
  constructor
  · have hle : U.map (MulAut.conj k).toMonoidHom ≤ orbSub (c * y * c⁻¹) τ := by
      rw [← hcl, Subgroup.closure_le]
      exact hcg
    have h2 := Subgroup.map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) hle
    rw [Subgroup.map_map, ← orbSub_conj_of_comm' hcτ, Subgroup.map_map] at h2
    have e1 : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
        (MulAut.conj (c⁻¹ * k)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have e2 : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e1, e2, Subgroup.map_id] at h2
    exact h2
  · have hN : c * y * c⁻¹ ∈ Subgroup.normalizer
        ((U.map (MulAut.conj k).toMonoidHom : Subgroup _) : Set (Equiv.Perm (Fin 4060))) := by
      rw [← hcl]
      refine mem_normalizer_of_conj_le fun u hu => ?_
      have hle : Subgroup.closure {x | x ∈ L.map (fun b => k * b * k⁻¹)} ≤
          (Subgroup.closure {x | x ∈ L.map (fun b => k * b * k⁻¹)}).comap
            (MulAut.conj (c * y * c⁻¹)).toMonoidHom := by
        rw [Subgroup.closure_le]
        intro x hx
        exact hn x hx
      exact hle hu
    have hkU := conj_mem_normalizer_of_map (H := U) (k := k) rfl hN
    have e : (c⁻¹ * k)⁻¹ * y * (c⁻¹ * k) = k⁻¹ * (c * y * c⁻¹) * k := by group
    rw [e]
    exact hkU

theorem cosetWords_letters (i : ℕ) : lettersOK 2 (cosetWords.getD i []) = true := by
  rcases Nat.lt_or_ge i cosetWords.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    have h : cosetWords.all (lettersOK 2) = true := by decide +kernel
    exact List.all_eq_true.mp h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    rfl

section Scans

theorem rep_cosetH (i : ℕ) : Rep 4060 (abA (cosetWords.getD i [])) (cosetH i) :=
  rep_abA (cosetWords_letters i)

end Scans

theorem move_conj {c y τ : Equiv.Perm (Fin 4060)} (hc : c * τ = τ * c) (h : y * τ * y⁻¹ ≠ τ) :
    c * y * c⁻¹ * τ * (c * y * c⁻¹)⁻¹ ≠ τ := by
  intro he
  apply h
  have hτ : c⁻¹ * τ * c = τ := by rw [mul_assoc, ← hc]; group
  calc y * τ * y⁻¹ = c⁻¹ * (c * y * (c⁻¹ * τ * c) * y⁻¹ * c⁻¹) * c := by rw [hτ]; group
    _ = c⁻¹ * (c * y * c⁻¹ * τ * (c * y * c⁻¹)⁻¹) * c := by group
    _ = τ := by rw [he, hτ]

theorem conj_comm_facts {c y τ : Equiv.Perm (Fin 4060)} (hc : c * τ = τ * c)
    (hcomm : ∀ j : ℕ, τ * (y ^ j * τ * (y ^ j)⁻¹) = y ^ j * τ * (y ^ j)⁻¹ * τ) :
    ∀ j : ℕ, τ * ((c * y * c⁻¹) ^ j * τ * ((c * y * c⁻¹) ^ j)⁻¹) =
      (c * y * c⁻¹) ^ j * τ * ((c * y * c⁻¹) ^ j)⁻¹ * τ := by
  intro j
  have hci : c⁻¹ * τ = τ * c⁻¹ := by
    calc c⁻¹ * τ = c⁻¹ * (τ * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * τ) * c⁻¹ := by rw [hc]
      _ = τ * c⁻¹ := by group
  have key : (c * y * c⁻¹) ^ j * τ * ((c * y * c⁻¹) ^ j)⁻¹ = c * (y ^ j * τ * (y ^ j)⁻¹) * c⁻¹ := by
    rw [conj_pow]
    calc c * y ^ j * c⁻¹ * τ * (c * y ^ j * c⁻¹)⁻¹ =
        c * y ^ j * (c⁻¹ * τ) * c * (y ^ j)⁻¹ * c⁻¹ := by group
      _ = c * y ^ j * (τ * c⁻¹) * c * (y ^ j)⁻¹ * c⁻¹ := by rw [hci]
      _ = c * (y ^ j * τ * (y ^ j)⁻¹) * c⁻¹ := by group
  rw [key]
  calc τ * (c * (y ^ j * τ * (y ^ j)⁻¹) * c⁻¹) = (τ * c) * (y ^ j * τ * (y ^ j)⁻¹) * c⁻¹ := by
        group
    _ = (c * τ) * (y ^ j * τ * (y ^ j)⁻¹) * c⁻¹ := by rw [hc]
    _ = c * (τ * (y ^ j * τ * (y ^ j)⁻¹)) * c⁻¹ := by group
    _ = c * (y ^ j * τ * (y ^ j)⁻¹ * τ) * c⁻¹ := by rw [hcomm j]
    _ = c * (y ^ j * τ * (y ^ j)⁻¹) * (τ * c⁻¹) := by group
    _ = c * (y ^ j * τ * (y ^ j)⁻¹) * (c⁻¹ * τ) := by rw [hci]
    _ = c * (y ^ j * τ * (y ^ j)⁻¹) * c⁻¹ * τ := by group

def BadConcl (y τ : Equiv.Perm (Fin 4060)) (q : ℕ) : Prop :=
  ∃ g ∈ ruP, ∃ c ∈ candData.flatten, refPrime c.1 = q ∧
    (refU c.1).map (MulAut.conj g).toMonoidHom ≤ orbSub y τ ∧
    g⁻¹ * y * g ∈ Subgroup.normalizer (refU c.1 : Set (Equiv.Perm (Fin 4060)))

theorem badConcl_of_cand {i q : ℕ} {c₁ y τ : Equiv.Perm (Fin 4060)} (hc₁ : c₁ ∈ ruP)
    (hcτ : c₁ * τ = τ * c₁) {cg : List (Equiv.Perm (Fin 4060))} (hcg : cg ∈ candsG i q)
    (h1 : ∀ x ∈ cg, x ∈ orbSub (c₁ * y * c₁⁻¹) τ)
    (h2 : ∀ x ∈ cg, c₁ * y * c₁⁻¹ * x * (c₁ * y * c₁⁻¹)⁻¹ ∈ Subgroup.closure {x | x ∈ cg}) :
    BadConcl y τ q := by
  obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hcg
  obtain ⟨hcdD, hq⟩ := List.mem_filter.mp hcd
  have hcdF := mem_flatten_of_getD hcdD
  obtain ⟨hF, hT⟩ := conj_facts (closure_refG (candData_lt cd hcdF)) hcτ h1 h2
  exact ⟨c₁⁻¹ * wG cd.2, ruP.mul_mem (ruP.inv_mem hc₁) (wG_mem _), cd, hcdF,
    beq_iff_eq.mp hq, hF, hT⟩

theorem hWordsZ_length : hWordsZ.length = 4 := rfl

theorem hWordsA_length : hWordsA.length = 5 := rfl

theorem cosetH_Z {i : ℕ} (hi : i < 4) : cosetH i = abG (hWordsZ.getD i []) := by
  rw [cosetH, cosetWords, List.getD_append _ _ _ _ (by rw [hWordsZ_length]; exact hi)]

theorem cosetH_A (i : ℕ) : cosetH (i + 4) = abG (hWordsA.getD i []) := by
  rw [cosetH, cosetWords, List.getD_append_right _ _ _ _ (by rw [hWordsZ_length]; omega),
    hWordsZ_length, Nat.add_sub_cancel]

section Classify

end Classify

end CFSG.Quasithin.KGC31.Ru

end
