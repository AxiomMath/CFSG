module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Core

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem dist_le_of_mem_nbrs (hA : F53Amalgam H M S) {x y z : Geo H M} (hz : z ∈ nbrs y) :
    dist x z ≤ dist x y + 1 := by
  have h1 : dist y z = 1 := dist_eq_one_iff_adj.mpr hz
  have := dist_triangle hA.amalgam.gen x y z
  omega

theorem dist_le_of_mem_nbrs' (hA : F53Amalgam H M S) {x y z : Geo H M} (hz : z ∈ nbrs y) :
    dist x y ≤ dist x z + 1 := by
  have h1 : dist z y = 1 := by rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hz
  have := dist_triangle hA.amalgam.gen x z y
  omega

theorem exists_nbr_dist (hA : F53Amalgam H M S) {x y : Geo H M} {n : ℕ}
    (h : dist x y = n + 1) : ∃ y' ∈ nbrs y, dist x y' = n :=
  exists_adj_dist_eq hA.amalgam.gen h

theorem vtype_of_even (hA : F53Amalgam H M S) (hs : Sit43 α) {x : Geo H M}
    (h : Even (dist α x)) : vtype x = false := by
  have h1 := (vtype_eq_iff_even_dist hA.amalgam.gen α x).mpr h
  rw [hs.vα] at h1
  exact h1.symm

theorem vtype_of_odd (hA : F53Amalgam H M S) (hs : Sit43 α) {x : Geo H M}
    (h : ¬ Even (dist α x)) : vtype x = true := by
  have h1 := (vtype_eq_iff_even_dist hA.amalgam.gen α x).not.mpr h
  rw [hs.vα] at h1
  cases hx : vtype x
  · exact absurd hx.symm h1
  · rfl

theorem vtype_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : vtype α' = true :=
  vtype_of_odd hA hs (by rw [hc.2]; exact Nat.not_even_iff_odd.mpr ho)

theorem exists_crit_data (hA : F53Amalgam H M S) (hs : Sit43 α) {α' : Geo H M}
    (hc : IsCritPair₁ α α') :
    ∃ β ν : Geo H M, β ∈ nbrs α ∧ ν ∈ nbrs α' ∧ dist β α' + 1 = bMin H M ∧
      dist α ν + 1 = bMin H M ∧ dist β ν + 2 = bMin H M := by
  have hb := hs.b1
  obtain ⟨β, hβ, hdβ⟩ := exists_nbr_dist hA (x := α') (y := α) (n := bMin H M - 1)
    (by rw [CosetGeom.dist_comm, hc.2]; omega)
  have hdβ' : dist β α' = bMin H M - 1 := by rw [CosetGeom.dist_comm]; exact hdβ
  obtain ⟨ν, hν, hdν⟩ := exists_nbr_dist hA (x := β) (y := α') (n := bMin H M - 2)
    (by rw [hdβ']; omega)
  have h1 := dist_le_of_mem_nbrs' hA (x := α) hν
  have h2 := dist_triangle hA.amalgam.gen α β ν
  have h3 : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
  rw [hc.2] at h1
  exact ⟨β, ν, hβ, hν, by omega, by omega, by omega⟩

theorem exists_nu (hA : F53Amalgam H M S) (hs : Sit43 α) {α' β : Geo H M}
    (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α) (hdβ : dist β α' + 1 = bMin H M) :
    ∃ ν ∈ nbrs α', dist α ν + 1 = bMin H M ∧ dist β ν + 2 = bMin H M := by
  have hb := hs.b1
  obtain ⟨ν, hν, hdν⟩ := exists_nbr_dist hA (x := β) (y := α') (n := bMin H M - 2)
    (by omega)
  have h1 := dist_le_of_mem_nbrs' hA (x := α) hν
  have h2 := dist_triangle hA.amalgam.gen α β ν
  have h3 : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
  rw [hc.2] at h1
  exact ⟨ν, hν, by omega, by omega⟩

theorem dist_beta_crit (hA : F53Amalgam H M S) {α' ν β : Geo H M}
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hβ : β ∈ nbrs α)
    (hdβ : dist β ν + 2 = bMin H M) : dist β α' + 1 = bMin H M := by
  have h1 := dist_le_of_mem_nbrs' hA (x := β) hν
  have h2 := dist_triangle hA.amalgam.gen α β α'
  have h3 : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
  rw [hc.2] at h2
  omega

theorem Vn_le_Qv_of_dist (hA : F53Amalgam H M S) (hs : Sit43 α) {δ x : Geo H M}
    (hδ : vtype δ = true) (hd : dist δ x + 2 ≤ bMin H M) : Vn δ ≤ Qv x := by
  refine iSup₂_le fun l hl => ?_
  have h1 := dist_le_of_mem_nbrs hA (x := x) hl
  rw [CosetGeom.dist_comm x δ, CosetGeom.dist_comm x l] at h1
  exact hs.Zv_le_Qv_of_dist_lt_false (Sit43.vtype_false_of_adj hδ hl) (by omega)

theorem Vn_le_stab_of_dist (hA : F53Amalgam H M S) (hs : Sit43 α) {δ x : Geo H M}
    (hδ : vtype δ = true) (hd : dist δ x + 1 ≤ bMin H M) : Vn δ ≤ stab x := by
  refine iSup₂_le fun l hl => ?_
  have h1 := dist_le_of_mem_nbrs hA (x := x) hl
  rw [CosetGeom.dist_comm x δ, CosetGeom.dist_comm x l] at h1
  exact hs.Zv_le_stab_of_dist_le_false hA (Sit43.vtype_false_of_adj hδ hl) (by omega)

omit [Finite G] in
theorem Zv_le_Vn {δ l : Geo H M} (hl : l ∈ nbrs δ) : Zv l ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs δ) => Zv m) l hl le_rfl

section Crit

variable {α' ν β : Geo H M}

theorem vtype_nu (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') : vtype ν = false :=
  Sit43.vtype_false_of_adj (vtype_crit hA hs ho hc) hν

omit [Finite G] in
theorem vtype_beta (hs : Sit43 α) (hβ : β ∈ nbrs α) : vtype β = true :=
  Sit43.vtype_true_of_adj hs.vα hβ

theorem Zv_le_stab_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (hc : IsCritPair₁ α α') :
    Zv α ≤ stab α' :=
  hs.Zv_le_stab_of_dist_le_false hA hs.vα (le_of_eq hc.2)

omit [Finite G] in
theorem Zv_le_Qv_nu (hs : Sit43 α) (hdν : dist α ν + 1 = bMin H M) : Zv α ≤ Qv ν :=
  hs.Zv_le_Qv_of_dist_lt_false hs.vα (by omega)

theorem Zv_le_edge_nu (hA : F53Amalgam H M S) (hs : Sit43 α) (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) : Zv α ≤ stab ν ⊓ stab α' :=
  le_inf ((Zv_le_Qv_nu hs hdν).trans (pCoreOf_le 2 _))
    ((Zv_le_Qv_nu hs hdν).trans (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hν)))

theorem Zv_nu_le_Qv (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M) :
    Zv ν ≤ Qv α :=
  hs.Zv_le_Qv_of_dist_lt_false (vtype_nu hA hs ho hc hν)
    (by rw [CosetGeom.dist_comm]; omega)

theorem Yv_le_Qv (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M) :
    Yv α' ≤ Qv α :=
  (Yv_le_Zv hν).trans (Zv_nu_le_Qv hA hs ho hc hν hdν)

theorem Zv_nu_le_Qv_beta (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdβ : dist β ν + 2 = bMin H M) :
    Zv ν ≤ Qv β :=
  hs.Zv_le_Qv_of_dist_lt_false (vtype_nu hA hs ho hc hν)
    (by rw [CosetGeom.dist_comm]; omega)

theorem Vn_beta_le_Qv_nu (hA : F53Amalgam H M S) (hs : Sit43 α) (hβ : β ∈ nbrs α)
    (hdβ : dist β ν + 2 = bMin H M) : Vn β ≤ Qv ν :=
  Vn_le_Qv_of_dist hA hs (vtype_beta hs hβ) (le_of_eq hdβ)

theorem Vn_beta_le_stab (hA : F53Amalgam H M S) (hs : Sit43 α) {α' β : Geo H M}
    (hβ : β ∈ nbrs α) (hdβ : dist β α' + 1 = bMin H M) : Vn β ≤ stab α' :=
  Vn_le_stab_of_dist hA hs (vtype_beta hs hβ) (le_of_eq hdβ)

theorem Vn_le_stab_beta (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    {α' β : Geo H M} (hc : IsCritPair₁ α α') (hdβ : dist β α' + 1 = bMin H M) :
    Vn α' ≤ stab β :=
  Vn_le_stab_of_dist hA hs (vtype_crit hA hs ho hc)
    (by rw [CosetGeom.dist_comm]; exact le_of_eq hdβ)

theorem Zv_le_stab_beta (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    {α' β l : Geo H M} (hc : IsCritPair₁ α α') (hdβ : dist β α' + 1 = bMin H M)
    (hl : l ∈ nbrs α') : Zv l ≤ stab β :=
  (Zv_le_Vn hl).trans (Vn_le_stab_beta hA hs ho hc hdβ)

theorem isCritPair₃_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    {α' β : Geo H M} (hc : IsCritPair₁ α α') (hβ : β ∈ nbrs α)
    (hdβ : dist β α' + 1 = bMin H M) : IsCritPair₃ β α' :=
  ⟨vtype_beta hs hβ, vtype_crit hA hs ho hc, hdβ,
    fun h => hc.1 ((Zv_le_Vn (nbrs_symm hβ)).trans h)⟩

end Crit

theorem exists_crit_of_crit3 (hA : F53Amalgam H M S) (hs : Sit43 α) {δ δ' : Geo H M}
    (h : IsCritPair₃ δ δ') : ∃ l ∈ nbrs δ, vtype l = false ∧ IsCritPair₁ l δ' := by
  obtain ⟨hδ, -, hd, hV⟩ := h
  have hex : ∃ l ∈ nbrs δ, ¬ Zv l ≤ Qv δ' := by
    by_contra hcon
    push Not at hcon
    exact hV (iSup₂_le fun l hl => hcon l hl)
  obtain ⟨l, hl, hlQ⟩ := hex
  have hlv : vtype l = false := Sit43.vtype_false_of_adj hδ hl
  refine ⟨l, hl, hlv, hlQ, ?_⟩
  have h1 := dist_triangle hA.amalgam.gen l δ δ'
  have h2 : dist l δ = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hl)
  by_contra hne
  exact hlQ (hs.Zv_le_Qv_of_dist_lt_false hlv (by omega))

section G1

variable {α' ν : Geo H M}

theorem exists_sit29_nu (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') :
    ∃ l l' : Geo H M, S29.Sit29 H M S ν l l' α' :=
  hs.exists_sit29 hA h26 (vtype_crit hA hs ho hc) hν

theorem smul_swap_of_crit (hA : F53Amalgam H M S) (hs : Sit43 α) {l l' : Geo H M}
    (h29 : S29.Sit29 H M S ν l l' α') (hdν : dist α ν + 1 = bMin H M) {z : G}
    (hz : z ∈ Zv α) (hzQ : z ∉ Qv α') :
    ∃ hz' : z ∈ H ⊔ M, (⟨z, hz'⟩ : ↥(H ⊔ M)) • l = l' ∧ (⟨z, hz'⟩ : ↥(H ⊔ M)) • l' = l := by
  have hE := Zv_le_edge_nu hA hs h29.n₁ hdν hz
  exact ⟨stab_le α' hE.2, h29.smul_swap ⟨z, stab_le α' hE.2⟩ hE.1 hE.2 hzQ⟩

theorem conj_swap_of_crit (hA : F53Amalgam H M S) (hs : Sit43 α) {l l' : Geo H M}
    (h29 : S29.Sit29 H M S ν l l' α') (hdν : dist α ν + 1 = bMin H M) {z : G}
    (hz : z ∈ Zv α) (hzQ : z ∉ Qv α') : conjSub z (Zv l) = Zv l' ∧ conjSub z (Zv l') = Zv l :=
  h29.Zv_conj_swap (Zv_le_edge_nu hA hs h29.n₁ hdν hz).1
    (Zv_le_edge_nu hA hs h29.n₁ hdν hz).2 hzQ

theorem eq_of_mem_nbrs_crit (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) {μ : Geo H M} (hμ : μ ∈ nbrs α')
    (hdμ : dist α μ + 1 = bMin H M) : μ = ν := by
  obtain ⟨l, l', h29⟩ := exists_sit29_nu hA h26 hs ho hc hν
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv α, z ∉ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hc.1 fun x hx => hcon x hx
  obtain ⟨hz', h1, h2⟩ := smul_swap_of_crit hA hs h29 hdν hz hzQ
  have hfix : (⟨z, hz'⟩ : ↥(H ⊔ M)) • μ = μ :=
    smul_eq_of_mem_stab ((Zv_le_Qv_nu hs hdμ).trans (pCoreOf_le 2 _) hz)
  rcases h29.nbrs_eq μ hμ with h | h | h
  · exact h
  · rw [h] at hfix
    exact absurd (h1.symm.trans hfix) h29.ne₂₃.symm
  · rw [h] at hfix
    exact absurd (h2.symm.trans hfix) h29.ne₂₃

theorem Zv_sup_Qv_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M) :
    Zv α ⊔ Qv α' = stab ν ⊓ stab α' := by
  have hνv := vtype_nu hA hs ho hc hν
  have h2 : (Qv α').relIndex (stab ν ⊓ stab α') = 2 :=
    Sit43.relIndex_Qv_edge hA hνv (nbrs_symm hν)
  have hQE : Qv α' ≤ stab ν ⊓ stab α' :=
    le_inf (Qv_le_stab_of_mem_nbrs hA hν) (pCoreOf_le 2 _)
  have hKE : Zv α ⊔ Qv α' ≤ stab ν ⊓ stab α' := sup_le (Zv_le_edge_nu hA hs hν hdν) hQE
  have hmul := Subgroup.relIndex_mul_relIndex (Qv α') (Zv α ⊔ Qv α') (stab ν ⊓ stab α')
    le_sup_right hKE
  rw [h2] at hmul
  have hne : (Qv α').relIndex (Zv α ⊔ Qv α') ≠ 1 := fun h =>
    hc.1 (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h))
  have h1 : (Zv α ⊔ Qv α').relIndex (stab ν ⊓ stab α') = 1 := by
    rcases Nat.dvd_prime Nat.prime_two |>.mp (Dvd.intro_left _ hmul) with h | h
    · exact h
    · rw [h] at hmul
      omega
  exact le_antisymm hKE (Subgroup.relIndex_eq_one.mp h1)

theorem relIndex_Zv_inf_Qv_crit (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M) :
    (Zv α ⊓ Qv α').relIndex (Zv α) = 2 := by
  have hn : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    (Zv_le_stab_crit hA hs hc).trans (le_normalizer_pCoreOf 2 _)
  have h1 := Sit43.relIndex_sup_of_le_normalizer hn
  have hνv := vtype_nu hA hs ho hc hν
  rw [Zv_sup_Qv_crit hA hs ho hc hν hdν, Sit43.relIndex_Qv_edge hA hνv (nbrs_symm hν)] at h1
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact h1.symm

end G1

end Core

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
