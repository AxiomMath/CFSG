module

public import CFSG.Quasithin.EmptyFaithful.ModGLat

public section

namespace CFSG.Quasithin.ModG

open scoped Pointwise
open MulAction CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Setup.X1
  CFSG.Sporadic.Schreier

theorem map_eq_of_le_aut {H : Subgroup Mg} (α : MulAut Mg) (h : H.map α.toMonoidHom ≤ H) :
    H.map α.toMonoidHom = H := by
  apply Subgroup.eq_of_le_of_card_ge h
  rw [Subgroup.card_map_of_injective α.injective]

theorem map_conj_of_mem {H : Subgroup Mg} {n : Mg} (hn : n ∈ H) :
    H.map (MulAut.conj n).toMonoidHom = H := by
  apply map_eq_of_le_aut
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem hn hx) (H.inv_mem hn)

theorem aut_stab_S {α : MulAut Mg} (h : Sg.map α.toMonoidHom = Sg) :
    (∀ s ∈ Sg, α s ∈ Sg) ∧ ∀ s ∈ Sg, α.symm s ∈ Sg := by
  constructor
  · intro s hs
    rw [← h]
    exact ⟨s, hs, rfl⟩
  · intro s hs
    rw [← h] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    simpa using ht

theorem mem_Sg_of_normalizes (n : Mg)
    (h : Sg.map (MulAut.conj n).toMonoidHom = Sg) : n ∈ Sg := by
  obtain ⟨hf, hb⟩ := aut_stab_S h
  have hf' : ∀ s ∈ Sg, n * s * n⁻¹ ∈ Sg := fun s hs => hf s hs
  have hb' : ∀ s ∈ Sg, n⁻¹ * s * n ∈ Sg := fun s hs => by
    have := hb s hs
    simpa [MulAut.conj_symm_apply] using this
  obtain ⟨E, -, -, -, horb⟩ := m22_struct
  have hfix : ∀ l ∈ Ls, l • (n • M22Insp.data.B₀) = n • M22Insp.data.B₀ := by
    intro l hl
    have hlS : l ∈ Sg := Subgroup.subset_closure hl
    have h1 : n⁻¹ * l * n ∈ Sg := hb' l hlS
    have h2 : (n⁻¹ * l * n) • M22Insp.data.B₀ = M22Insp.data.B₀ :=
      mem_stabilizer_iff.1 (Sg_le_Dg h1)
    calc l • (n • M22Insp.data.B₀) = (l * n) • M22Insp.data.B₀ := (mul_smul _ _ _).symm
      _ = (n * (n⁻¹ * l * n)) • M22Insp.data.B₀ := by congr 1; group
      _ = n • ((n⁻¹ * l * n) • M22Insp.data.B₀) := mul_smul _ _ _
      _ = n • M22Insp.data.B₀ := by rw [h2]
  have hnH : n • M22Insp.data.B₀ ∈ M22Insp.data.H := horb _ ⟨n, rfl⟩
  have hHdef : M22Insp.data.H = M22Insp.blocks.map M22Insp.blk := rfl
  rw [hHdef, List.mem_map] at hnH
  obtain ⟨l, hl, hln⟩ := hnH
  obtain ⟨i, hi, hil⟩ := List.getElem_of_mem hl
  have hi77 : i < 77 := by rw [← blocks_length]; exact hi
  have hli : l = M22Insp.blocks.getD i [] := by rw [List.getD_eq_getElem _ _ hi, hil]
  have hi0 : i = 0 := by
    by_contra hne
    obtain ⟨s, hs, x, hx, hsx⟩ := hex_unique i hi77 hne
    have h1 := hfix s hs
    rw [← hln] at h1
    have hxm : x ∈ M22Insp.blk l := (mem_blk l x).2 (by rw [hli]; exact hx)
    have h2 : s • x ∈ s • M22Insp.blk l := Finset.smul_mem_smul_finset hxm
    rw [h1] at h2
    have := (mem_blk l _).1 h2
    rw [hli] at this
    exact hsx this
  have hnB : n • M22Insp.data.B₀ = M22Insp.data.B₀ := by
    rw [← hln, hli, hi0, blocks_zero]
    rfl
  have hnD : n ∈ Dg := mem_stabilizer_iff.2 hnB
  obtain ⟨d, hd, hds⟩ := Dg_cosets n hnD
  have hdn : ∀ s ∈ Sg, d * s * d⁻¹ ∈ Sg := by
    intro s hs
    have h1 : (d⁻¹ * n)⁻¹ * s * (d⁻¹ * n) ∈ Sg :=
      Sg.mul_mem (Sg.mul_mem (Sg.inv_mem hds) hs) hds
    have h2 := hf' _ h1
    have : d * s * d⁻¹ = n * ((d⁻¹ * n)⁻¹ * s * (d⁻¹ * n)) * n⁻¹ := by group
    rw [this]
    exact h2
  rcases dEl_normalizes d hd with hd1 | ⟨s, hs, hsn⟩
  · rw [hd1, inv_one, one_mul] at hds
    exact hds
  · exact absurd (hdn s (Subgroup.subset_closure hs)) hsn

theorem delta1_mem_A : delta1 ∈ m22A := by
  have h1 : M22Insp.delta ∈ m22A := delta_mem_A
  exact m22A.mul_mem h1 (m22_le_A (x0 : Mg).2)

@[expose] noncomputable def alpha1 : MulAut Mg :=
  muA ⟨delta1, delta1_mem_A⟩

theorem alpha1_coe (x : Mg) :
    ((alpha1 x : Mg) : Equiv.Perm (Fin 22)) = delta1 * (x : Equiv.Perm (Fin 22)) * delta1⁻¹ := rfl

theorem Ls_eq_getD (x : Mg) (hx : x ∈ Ls) : ∃ i < 6, x = Ls.getD i 1 := by
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hx
  have hi6 : i < 6 := by
    have := hi
    rw [Ls, invAlph_length, List.length_map, sWd_len] at this
    omega
  exact ⟨i, hi6, by rw [List.getD_eq_getElem _ _ hi, hia]⟩

theorem alpha1_Ls :
    ∀ x ∈ Ls, alpha1 x ∈ Sg := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Ls_eq_getD x hx
  have key : ∀ j < 3, alpha1 (Ls.getD j 1) ∈ Sg := by
    intro j hj
    obtain ⟨t, ht, hte⟩ := delta1_S j hj
    have : alpha1 (Ls.getD j 1) = t := Subtype.ext (by rw [alpha1_coe, hte])
    rw [this]
    exact (mem_Sg_iff t).2 ht
  have hinv : ∀ j < 3, Ls.getD (j + 3) 1 = (Ls.getD j 1)⁻¹ := Ls_inv
  by_cases h3 : i < 3
  · exact key i h3
  · have : i = (i - 3) + 3 := by omega
    rw [this, hinv (i - 3) (by omega), map_inv]
    exact Sg.inv_mem (key (i - 3) (by omega))

theorem alpha1_Sg :
    Sg.map alpha1.toMonoidHom = Sg := by
  apply map_eq_of_le_aut
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact alpha1_Ls y hy
  | one => simp
  | mul y z _ _ ihy ihz =>
    show alpha1 (y * z) ∈ Sg
    rw [map_mul]
    exact Sg.mul_mem ihy ihz
  | inv y _ ih =>
    show alpha1 y⁻¹ ∈ Sg
    rw [map_inv]
    exact Sg.inv_mem ih

theorem alpha1_Dg :
    Dg.map alpha1.toMonoidHom = Dg := by
  apply map_eq_of_le_aut
  rintro _ ⟨x, hx, rfl⟩
  have hB : delta1 • M22Insp.data.B₀ = M22Insp.data.B₀ := by
    rw [B0_eq]
    exact smul_blk_eq _ _ delta1_B
  have hBi : delta1⁻¹ • M22Insp.data.B₀ = M22Insp.data.B₀ := by
    rw [inv_smul_eq_iff, hB]
  have hx' : (x : Equiv.Perm (Fin 22)) • M22Insp.data.B₀ = M22Insp.data.B₀ := mem_stabilizer_iff.1 hx
  show alpha1 x ∈ Dg
  rw [Dg, mem_stabilizer_iff]
  show ((alpha1 x : Mg) : Equiv.Perm (Fin 22)) • M22Insp.data.B₀ = M22Insp.data.B₀
  rw [alpha1_coe, mul_smul, mul_smul, hBi, hx', hB]

theorem alpha1_P1 :
    P1.map alpha1.toMonoidHom = P1 := by
  apply map_eq_of_le_aut
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | rfl
    · exact Ls_le_P1 (alpha1_Ls y hy)
    · obtain ⟨w, -, t, ht, hte⟩ := delta1_P1
      have : alpha1 u1 = ev (alph4 u1) w * t := Subtype.ext (by rw [alpha1_coe, hte]; rfl)
      show alpha1 u1 ∈ P1
      rw [this]
      exact P1.mul_mem (rep_mem_P1 w) (Ls_le_P1 ((mem_Sg_iff t).2 ht))
  | one => simp
  | mul y z _ _ ihy ihz =>
    show alpha1 (y * z) ∈ P1
    rw [map_mul]
    exact P1.mul_mem ihy ihz
  | inv y _ ih =>
    show alpha1 y⁻¹ ∈ P1
    rw [map_inv]
    exact P1.inv_mem ih

theorem alpha1_P2 :
    P2.map alpha1.toMonoidHom = P2 := by
  apply map_eq_of_le_aut
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | rfl
    · exact Ls_le_P2 (alpha1_Ls y hy)
    · obtain ⟨w, -, t, ht, hte⟩ := delta1_P2
      have : alpha1 u2 = ev (alph4 u2) w * t := Subtype.ext (by rw [alpha1_coe, hte]; rfl)
      show alpha1 u2 ∈ P2
      rw [this]
      exact P2.mul_mem (rep_mem_P2 w) (Ls_le_P2 ((mem_Sg_iff t).2 ht))
  | one => simp
  | mul y z _ _ ihy ihz =>
    show alpha1 (y * z) ∈ P2
    rw [map_mul]
    exact P2.mul_mem ihy ihz
  | inv y _ ih =>
    show alpha1 y⁻¹ ∈ P2
    rw [map_inv]
    exact P2.inv_mem ih

theorem aut_decomp
    (α : MulAut Mg) (h : Sg.map α.toMonoidHom = Sg) :
    ∃ n ∈ Sg, α = MulAut.conj n ∨ α = MulAut.conj n * alpha1 := by
  obtain ⟨a, rfl⟩ := muA_surjective α
  rcases mem_m22A.1 a.2 with ha | ha
  · refine ⟨⟨(a : Equiv.Perm (Fin 22)), ha⟩, ?_, Or.inl ?_⟩
    · have hc : muA a = MulAut.conj (⟨(a : Equiv.Perm (Fin 22)), ha⟩ : Mg) :=
        muA_of_mem ⟨(a : Equiv.Perm (Fin 22)), ha⟩
      rw [hc] at h
      exact mem_Sg_of_normalizes _ h
    · exact muA_of_mem ⟨(a : Equiv.Perm (Fin 22)), ha⟩
  ·
    have hm : (M22Insp.delta)⁻¹ * (a : Equiv.Perm (Fin 22)) ∈ NativeSporadic.M22 := ha
    have hn : M22Insp.delta * ((M22Insp.delta)⁻¹ * (a : Equiv.Perm (Fin 22)) * (x0 : Equiv.Perm (Fin 22))⁻¹) *
        (M22Insp.delta)⁻¹ ∈ NativeSporadic.M22 :=
      m22_delta_normalizes _ (mul_mem hm (inv_mem (x0 : Mg).2))
    set n : Mg := ⟨M22Insp.delta * ((M22Insp.delta)⁻¹ * (a : Equiv.Perm (Fin 22)) *
      (x0 : Equiv.Perm (Fin 22))⁻¹) * (M22Insp.delta)⁻¹, hn⟩ with hndef
    have hna : a = ⟨(n : Equiv.Perm (Fin 22)), m22_le_A n.2⟩ * ⟨delta1, delta1_mem_A⟩ := by
      apply Subtype.ext
      show (a : Equiv.Perm (Fin 22)) = (n : Equiv.Perm (Fin 22)) * delta1
      rw [hndef, delta1]
      group
    have hα : muA a = MulAut.conj n * alpha1 := by
      rw [hna, map_mul, muA_of_mem]
      rfl
    have hconj : MulAut.conj n = muA a * alpha1⁻¹ := by
      rw [hα]
      group
    have hSn : Sg.map (MulAut.conj n).toMonoidHom ≤ Sg := by
      rintro _ ⟨x, hx, rfl⟩
      show (MulAut.conj n) x ∈ Sg
      rw [hconj]
      exact (aut_stab_S h).1 _ ((aut_stab_S alpha1_Sg).2 x hx)
    exact ⟨n, mem_Sg_of_normalizes n (map_eq_of_le_aut _ hSn), Or.inr hα⟩

theorem aut_inv
    (α : MulAut Mg) (h : Sg.map α.toMonoidHom = Sg) :
    Dg.map α.toMonoidHom = Dg ∧ P1.map α.toMonoidHom = P1 ∧ P2.map α.toMonoidHom = P2 := by
  obtain ⟨n, hn, hα | hα⟩ := aut_decomp α h
  · subst hα
    exact ⟨map_conj_of_mem (Sg_le_Dg hn), map_conj_of_mem (Ls_le_P1 hn), map_conj_of_mem (Ls_le_P2 hn)⟩
  · subst hα
    have key : ∀ H : Subgroup Mg, n ∈ H → H.map alpha1.toMonoidHom = H →
        H.map (MulAut.conj n * alpha1).toMonoidHom = H := by
      intro H hnH h1
      have : H.map (MulAut.conj n * alpha1).toMonoidHom =
          (H.map alpha1.toMonoidHom).map (MulAut.conj n).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      rw [this, h1]
      exact map_conj_of_mem hnH
    exact ⟨key Dg (Sg_le_Dg hn) alpha1_Dg, key P1 (Ls_le_P1 hn) alpha1_P1,
      key P2 (Ls_le_P2 hn) alpha1_P2⟩

end CFSG.Quasithin.ModG
