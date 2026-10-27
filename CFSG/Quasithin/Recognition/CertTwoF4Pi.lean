module

public import CFSG.Quasithin.Recognition.CertTwoF4Check
public import CFSG.Quasithin.Recognition.CertTitsOuter
public import CFSG.Quasithin.Recognition.CertTitsBridge

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits

theorem mem_normalizer_of_forall_conj_mem_f4 {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  rw [← this]
  exact hy

def tπ : Equiv.Perm (Fin 1755) := permOfArr 1755 titsPiArr

theorem tπ_rep
    : Rep 1755 titsPiArr tπ := (rep_permOfArr titsOuter_check.1).1

theorem tπ_inv_rep
    : Rep 1755 piInv tπ⁻¹ := rep_inv_of_isInvA tπ_rep twoF4Pi_check.1

theorem conjPi_rep
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    Rep 1755 (conjPi a) (tπ * g * tπ⁻¹) := rep_compA (rep_compA tπ_rep ha) tπ_inv_rep

theorem tπ_conj_titsD :
    ∀ x ∈ titsD, tπ * x * tπ⁻¹ ∈ titsD := by
  obtain ⟨hπ, -, -, hsσ, hsτ, -, -⟩ := titsOuter_check
  obtain ⟨hp1, hp2, -⟩ := titsChain_check
  have hrσ := (rep_permOfArr hp1).1
  have hrτ := (rep_permOfArr hp2).1
  have hD : titsModelJ = titsD := titsModelJ_eq.trans titsBridge_closure
  have hconj : ∀ t ∈ ({titsσ, titsτ} : Set (Equiv.Perm (Fin 1755))), tπ * t * tπ⁻¹ ∈ titsModelJ := by
    intro t ht
    rcases ht with rfl | ht
    · exact (titsSift_iff (conjPi_rep hrσ)).1 hsσ
    · rw [Set.mem_singleton_iff.1 ht]
      exact (titsSift_iff (conjPi_rep hrτ)).1 hsτ
  have hcj := conj_mem_closure_of_gen tπ (T := ({titsσ, titsτ} : Set (Equiv.Perm (Fin 1755))))
    (fun t ht => by rw [← titsModelJ_eq]; exact hconj t ht)
  intro x hx
  rw [← hD] at hx ⊢
  rw [titsModelJ_eq] at hx ⊢
  exact hcj x hx

theorem tπ_norm_D
    : tπ ∈ Subgroup.normalizer (titsD : Set (Equiv.Perm (Fin 1755))) :=
  mem_normalizer_of_forall_conj_mem_f4 tπ_conj_titsD

theorem tπ_not_mem_D :
    tπ ∉ titsD := by
  have hD : titsModelJ = titsD := titsModelJ_eq.trans titsBridge_closure
  intro h
  rw [← hD] at h
  have := (titsSift_iff tπ_rep).2 h
  rw [titsOuter_check.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem tπ_sq_J :
    tπ * tπ ∈ titsJ :=
  mem_titsJ_of_sift (rep_compA tπ_rep tπ_rep) twoF4Pi_check.2.2.2.2.2.2.1

theorem tπ_sq_D
    : tπ * tπ ∈ titsD := titsJ_le_titsD tπ_sq_J

theorem centralizer_titsD_eq_one :
    ∀ c : Equiv.Perm (Fin 1755), (∀ g ∈ titsD, c * g = g * c) → c = 1 := by
  obtain ⟨hA, hB, -, -, hOS, hSO, hchain, -, hprim, -⟩ := titsPair_check
  have hD : titsModelJ = titsD := titsModelJ_eq.trans titsBridge_closure
  obtain ⟨-, -, -, -, -, -, hnt⟩ := titsOuter_check
  have hle : Subgroup.closure {g | ∃ k < titsPairO.size, permOfArr 1755 titsPairO[k]! = g} ≤
      titsModelJ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hk, rfl⟩
    have hAJ : permOfArr 1755 titsA ∈ titsModelJ :=
      (titsSift_iff (rep_permOfArr hA).1).1 titsOuter_check.2.1
    have hBJ : permOfArr 1755 titsB ∈ titsModelJ :=
      (titsSift_iff (rep_permOfArr hB).1).1 titsOuter_check.2.2.1
    have hsz : titsPairO.size = 2 := by simp [titsPairO]
    rw [hsz] at hk
    interval_cases k
    · simpa [titsPairO] using hAJ
    · simpa [titsPairO] using hBJ
  have hSJ : ∀ j < titsPairStrong.size, permOfArr 1755 titsPairStrong[j]! ∈ titsModelJ := fun j hj =>
    hle (strong_mem_closure hOS hSO hchain j hj)
  have hSinv : ∀ j < titsPairStrong.size,
      isInvA 1755 titsPairStrong[j]! (rawInvs 1755 titsPairStrong)[j]! = true := fun j hj =>
    (chainCheckFacts hchain).strong_inv j hj
  have hnt' : ∀ p < 1755, p ≠ 0 → ∃ q < 1755, q ≠ p ∧ titsLabels[q]! = titsLabels[p]! := by
    intro p hp hp0
    have h := hnt
    simp only [titsLabelsNontrivial, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      beq_iff_eq, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h p hp with h0 | ⟨q, hq, hne, hlab⟩
    · exact absurd h0 hp0
    · exact ⟨q, hq, hne, hlab⟩
  intro c hc
  exact centralizer_eq_one_of_primCheck hSinv hSJ hprim hnt' c (fun g hg => hc g (hD ▸ hg))

theorem tπ_norm_S
    : tπ ∈ Subgroup.normalizer (titsS : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_forall_conj_mem_f4
  have hgen : ∀ t ∈ ({g | ∃ w ∈ titsSWords, wordIn 13 titsT w = g} : Set (Equiv.Perm (Fin 1755))),
      tπ * t * tπ⁻¹ ∈ titsS := by
    rintro t ⟨w, hw, rfl⟩
    exact mem_titsS_of_sift (conjPi_rep (rep_wordArr_titsT
      (titsLocalWords_letters titsLocalWords_mem.2.1 hw)))
      (List.all_eq_true.1 twoF4Pi_check.2.1 w hw)
  exact conj_mem_closure_of_gen tπ (T := {g | ∃ w ∈ titsSWords, wordIn 13 titsT w = g}) hgen

theorem tπ_norm_H
    : tπ ∈ Subgroup.normalizer (titsH : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_forall_conj_mem_f4
  have hgen : ∀ t ∈ ({g | ∃ w ∈ titsHWords, wordIn 13 titsT w = g} : Set (Equiv.Perm (Fin 1755))),
      tπ * t * tπ⁻¹ ∈ titsH := by
    rintro t ⟨w, hw, rfl⟩
    exact mem_titsH_of_sift (conjPi_rep (rep_wordArr_titsT
      (titsLocalWords_letters titsLocalWords_mem.1 hw)))
      (List.all_eq_true.1 twoF4Pi_check.2.2.1 w hw)
  exact conj_mem_closure_of_gen tπ (T := {g | ∃ w ∈ titsHWords, wordIn 13 titsT w = g}) hgen

theorem tπ_norm_N
    : tπ ∈ Subgroup.normalizer (titsN : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_forall_conj_mem_f4
  have hgen : ∀ t ∈ ({g | ∃ w ∈ titsNWords, wordIn 13 titsT w = g} : Set (Equiv.Perm (Fin 1755))),
      tπ * t * tπ⁻¹ ∈ titsN := by
    rintro t ⟨w, hw, rfl⟩
    exact mem_titsN_of_sift (conjPi_rep (rep_wordArr_titsT
      (titsLocalWords_letters titsLocalWords_mem.2.2.1 hw)))
      (List.all_eq_true.1 twoF4Pi_check.2.2.2.1 w hw)
  exact conj_mem_closure_of_gen tπ (T := {g | ∃ w ∈ titsNWords, wordIn 13 titsT w = g}) hgen

theorem tπ_norm_J
    : tπ ∈ Subgroup.normalizer (titsJ : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_forall_conj_mem_f4
  have hgen : ∀ t ∈ ({g | ∃ w ∈ titsJWords, wordIn 13 titsT w = g} : Set (Equiv.Perm (Fin 1755))),
      tπ * t * tπ⁻¹ ∈ titsJ := by
    rintro t ⟨w, hw, rfl⟩
    exact mem_titsJ_of_sift (conjPi_rep (rep_wordArr_titsT
      (titsLocalWords_letters titsLocalWords_mem.2.2.2.1 hw)))
      (List.all_eq_true.1 twoF4Pi_check.2.2.2.2.1 w hw)
  exact conj_mem_closure_of_gen tπ (T := {g | ∃ w ∈ titsJWords, wordIn 13 titsT w = g}) hgen

theorem tπ_norm_K
    : tπ ∈ Subgroup.normalizer (titsK : Set (Equiv.Perm (Fin 1755))) := by
  apply mem_normalizer_of_forall_conj_mem_f4
  have hgen : ∀ t ∈ ({g | ∃ w ∈ titsKWords, wordIn 13 titsT w = g} : Set (Equiv.Perm (Fin 1755))),
      tπ * t * tπ⁻¹ ∈ titsK := by
    rintro t ⟨w, hw, rfl⟩
    exact mem_titsK_of_sift (conjPi_rep (rep_wordArr_titsT
      (titsLocalWords_letters titsLocalWords_mem.2.2.2.2.1 hw)))
      (List.all_eq_true.1 twoF4Pi_check.2.2.2.2.2.1 w hw)
  exact conj_mem_closure_of_gen tπ (T := {g | ∃ w ∈ titsKWords, wordIn 13 titsT w = g}) hgen

end CFSG.Quasithin
