module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6LemD

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

open P62

theorem mem_zpowers_sq {z x : G} (hz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  have e : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul]
  rw [e]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

end P517

theorem fan517c (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h53a : Fan53a F)
    (hXi : ∃ T : Track Γ G, InXi T) (hD : LemmaD F) : Fan517c F := by
  intro h40 α z hα hz g₁ g₂ g₃ d₁ d₂ d₃
  have h35 : valence Γ α = 3 ∨ valence Γ α = 5 := F.valence α
  have h := P517.lab5_of F h510 h511 h53a h40 hXi hz (by omega)
  refine fan517b F h510 h511 h53a hXi h40 α z (Subgroup.zpowers z) hα hz
    (Subgroup.mem_zpowers z) (Subgroup.zpowers_le.2 hz.2.2.1) ?_ ?_ g₁ g₂ g₃ d₁ d₂ d₃
  · intro g hg n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g z := hz.2.2.2 g hg
    rw [(Commute.zpow_right hc k).mul_inv_cancel]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  · intro g g' hg hg' hd hmem
    set l := g • α with hl
    set m := g' • α with hm
    have e1 : g * z * g⁻¹ = P514.Lb z α l := (P514.Lb_eq h.cinv rfl).symm
    have e2 : g' * z * g'⁻¹ = P514.Lb z α m := (P514.Lb_eq h.cinv rfl).symm
    rw [e1, e2] at hmem
    obtain ⟨ν, hν⟩ := P62.exists_br F hg
    obtain ⟨ν', hν'⟩ := P62.exists_br F hg'
    have hl5 : valence Γ l = 5 := (P62.Br.valence F h.val5 hν).2
    have hm5 : valence Γ m = 5 := (P62.Br.valence F h.val5 hν').2
    have hne : l ≠ m := fun e => by rw [e, SimpleGraph.dist_self] at hd; omega
    have hνν : ν ≠ ν' := by
      rintro rfl
      have := dist_le (Walk.cons hν.2.1.symm (Walk.cons hν'.2.1 Walk.nil))
      simp only [Walk.length_cons, Walk.length_nil] at this
      omega
    rcases P517.mem_zpowers_sq hz.2.1 hmem with h1 | h1
    · have hLb : P514.Lb z α l = P514.Lb z α m := by
        rw [eq_inv_of_mul_eq_one_left h1, P517.lb_inv F h hg']
      exact hD h40 l m hne hl5 hm5 (Or.inr hd) (P514.Lb z α l) (P517.lb_cinv F h hg)
        (by rw [hLb]; exact P517.lb_cinv F h hg')
    · obtain ⟨l', hl', hne', -⟩ := P62.exists_sibling F h.val5 hν
      have hs := P517.sib F h hν hl' hne'.symm
      have hLb : P514.Lb z α l' = P514.Lb z α m := by
        rw [hs]
        have : P514.Lb z α m = (P514.Lb z α l)⁻¹ * z := by
          calc P514.Lb z α m = (P514.Lb z α l)⁻¹ * (P514.Lb z α l * P514.Lb z α m) := by group
            _ = (P514.Lb z α l)⁻¹ * z := by rw [h1]
        rw [this, P517.lb_inv F h hg]
      have hd' : Γ.dist l' m = 4 := P62.dist_four F hl' hν' hνν
      have hl'5 : valence Γ l' = 5 := (P62.Br.valence F h.val5 hl').2
      have hne'' : l' ≠ m := fun e => by rw [e, SimpleGraph.dist_self] at hd'; omega
      exact hD h40 l' m hne'' hl'5 hm5 (Or.inr hd') (P514.Lb z α l')
        (P517.lb_cinv F h (P62.Br.dist_two F hl'))
        (by rw [hLb]; exact P517.lb_cinv F h hg')

end CFSG.Quasithin.Fan86
