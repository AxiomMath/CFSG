module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517Trk
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lbl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P517

variable (F : FanTree Γ G) {α : V} {z : G} (h : Lab5 Γ α z)
include F h

theorem exists_conj_of_dist {l : V} (hl : Γ.dist α l = 2) : ∃ g : G, g • α = l := by
  obtain ⟨ν, hν⟩ := P62.exists_br F hl
  exact P62.exists_smul_of_valence_eq F (u := α) (w := l)
    (by rw [(P62.Br.valence F h.val5 hν).2, h.val5])

theorem lb_ker {l : V} (hl : Γ.dist α l = 2) : P514.Lb z α l ∈ nbrStab Γ G α := by
  obtain ⟨g, hg⟩ := exists_conj_of_dist F h hl
  rw [P514.Lb_eq h.cinv hg]
  exact h.ker g (by rw [hg]; exact hl)

theorem lb_cinv {l : V} (hl : Γ.dist α l = 2) : P514.Lb z α l ∈ Cinv G l :=
  P514.Lb_cinv h.cinv (exists_conj_of_dist F h hl)

theorem lb_sq {l : V} (hl : Γ.dist α l = 2) : P514.Lb z α l * P514.Lb z α l = 1 :=
  (lb_cinv F h hl).2.1

theorem lb_inv {l : V} (hl : Γ.dist α l = 2) : (P514.Lb z α l)⁻¹ = P514.Lb z α l :=
  inv_eq_of_mul_eq_one_right (lb_sq F h hl)

theorem lb_comm_z {l : V} (hl : Γ.dist α l = 2) :
    P514.Lb z α l * z = z * P514.Lb z α l :=
  h.cinv.2.2.2 _ (F.nbrStab_le_stabilizer α (lb_ker F h hl))

theorem lb_conj {l : V} (hl : Γ.dist α l = 2) (k : G) :
    k * P514.Lb z α l * k⁻¹ = P514.Lb z α (k • l) :=
  P514.Lb_conj h.cinv (exists_conj_of_dist F h hl) k

theorem sib {ν l l' : V} (hν : P62.Br Γ α ν l) (hν' : P62.Br Γ α ν l') (hne : l ≠ l') :
    P514.Lb z α l' = P514.Lb z α l * z := by
  obtain ⟨l'', hl'', hne'', hset⟩ := P62.exists_sibling F h.val5 hν
  have hl'l' : l'' = l' := by
    have hmem : l' ∈ Γ.neighborSet ν := hν'.2.1
    rw [hset] at hmem
    rcases hmem with e | e | e
    · exact absurd e hν'.2.2
    · exact absurd e.symm hne
    · exact e.symm
  subst hl'l'
  have hv3 : valence Γ ν = 3 := (P62.Br.valence F h.val5 hν).1
  have hβ : ¬ Equiv3 G α ν := by
    rintro ⟨g, hg⟩
    have := F.valence_smul_eq g α
    rw [hg, h.val5, hv3] at this
    omega
  have hmem : ∀ u, u ∈ [α, l, l''] ↔ Γ.Adj ν u := by
    intro u
    have : u ∈ Γ.neighborSet ν ↔ u ∈ ({α, l, l''} : Set V) := by rw [hset]
    simpa [or_assoc] using this.symm
  have hfun : ∀ u, Γ.Adj ν u → P62.pick G α u • α = u := by
    intro u hu
    obtain ⟨g, hg⟩ := P62.exists_smul_of_valence_eq F (u := α) (w := u)
      (by rw [F.val5_of_adj_val3 hu hv3, h.val5])
    exact P62.pick_smul ⟨g, hg⟩
  have hnd : ([α, l, l''] : List V).Nodup := by
    simp [hν.2.2.symm, hl''.2.2.symm, hne]
  obtain ⟨-, hp⟩ := P512.prod_eq_one F h.cinv h.ball2 h.noCinv hβ [α, l, l''] (P62.pick G α)
    hnd hmem hfun
  have hLb : ∀ u, Γ.Adj ν u → P62.pick G α u * z * (P62.pick G α u)⁻¹ = P514.Lb z α u :=
    fun u hu => (P514.Lb_eq h.cinv (hfun u hu)).symm
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
  rw [hLb α hν.1.symm, hLb l hν.2.1, hLb l'' hl''.2.1, P514.Lb_self h.cinv] at hp
  have hlsq := lb_sq F h (P62.Br.dist_two F hν)
  have hzsq := h.cinv.2.1
  have e1 : P514.Lb z α l'' = (z * P514.Lb z α l)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_assoc]
    exact hp
  rw [e1, mul_inv_rev, lb_inv F h (P62.Br.dist_two F hν), inv_eq_of_mul_eq_one_right hzsq]

theorem label_br {ν l l' : V} (hν : P62.Br Γ α ν l) (hν' : P62.Br Γ α ν l') :
    P514.Lb z α l = P514.Lb z α l' ∨ P514.Lb z α l = P514.Lb z α l' * z := by
  by_cases hll : l' = l
  · exact Or.inl (by rw [hll])
  · exact Or.inr (sib F h hν' hν hll)

theorem comm_lab {l m : V} (hl : Γ.dist α l = 2) (hm : Γ.dist α m = 2) :
    fcomm (P514.Lb z α l) (P514.Lb z α m) ∈ Subgroup.zpowers z := by
  obtain ⟨ν, hν⟩ := P62.exists_br F hl
  have hK := lb_ker F h hm
  have hbr := P62.Br.of_mem_nbrStab F hK hν
  have hconj := lb_conj F h hl (P514.Lb z α m)
  have hcases := label_br F h hbr hν
  have hs := lb_inv F h hl
  have ht := lb_inv F h hm
  unfold fcomm
  rw [hs, ht]
  have e : P514.Lb z α l * P514.Lb z α m * P514.Lb z α l * P514.Lb z α m =
      P514.Lb z α l * (P514.Lb z α m * P514.Lb z α l * (P514.Lb z α m)⁻¹) := by
    rw [ht]
    simp only [mul_assoc]
  rw [e, hconj]
  rcases hcases with h1 | h1
  · rw [h1, lb_sq F h hl]
    exact Subgroup.one_mem _
  · rw [h1, ← mul_assoc, lb_sq F h hl, one_mul]
    exact Subgroup.mem_zpowers z

end P517

end CFSG.Quasithin.Fan86
