module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
public import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open CFSG.Quasithin.F7
open CFSG.Quasithin.F112Crit

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

theorem ConfigA.false_of_three_le (hA : ConfigA G₀ G₁ G₂ T L E) (hL : LocalA G₀ G₁ G₂ E)
    (hb : 3 ≤ critDist G₀ G₁ G₂ E)
    (hQ2 : ∀ γ γ' δ : CosetGeom G₀ G₁ G₂, vtype γ = false →
      dist γ δ = critDist G₀ G₁ G₂ E → γ' ∈ nbrs γ →
      Vv E δ ⊓ pCoreOf 2 (stab γ') ≤ pCoreOf 2 (stab γ)) :
    False := by
  classical
  let b := critDist G₀ G₁ G₂ E
  have hb3 : 3 ≤ b := hb
  obtain ⟨α', hα'dist, hα'not⟩ := exists_dist_eq_critDist_not_le hA.hypV hA.ne_bot
  have hα'dist' : dist (γ₀ G₀ G₁ G₂) α' = b := hα'dist
  have hoddα' : Odd (dist (γ₀ G₀ G₁ G₂) α') := by
    rw [hα'dist']; exact hA.odd
  have hα'type : vtype α' = true := vtype_eq_true_of_odd hA.hyp.gen hoddα'
  have hEα : Vv E (γ₀ G₀ G₁ G₂) = E := Vv_γ₀ hA.hypV.normalizes
  have hα'stab : E ≤ stab α' := by
    have := hL.le_stab (γ₀ G₀ G₁ G₂) vtype_γ₀ α' (by rw [hα'dist'])
    rwa [hEα] at this
  have hQα' : ¬ E ≤ pCoreOf 2 (stab α') := fun h =>
    hα'not (h.trans (pCoreOf_stab_le_ballStab_one hA.hyp α'))
  obtain ⟨β, hβadj, hα'βdist⟩ := exists_adj_dist_eq hA.hyp.gen (α := α')
    (δ := γ₀ G₀ G₁ G₂) (d := b - 1) (by rw [CosetGeom.dist_comm, hα'dist']; omega)
  have hβtype : vtype β = true := vtype_eq_true_of_mem_nbrs vtype_γ₀ hβadj
  obtain ⟨α2, hβα2, hα'α2dist⟩ := exists_adj_dist_eq hA.hyp.gen (α := α') (δ := β) (d := b - 2)
    (by rw [hα'βdist]; omega)
  have hα2mem : α2 ∈ nbrs β := hβα2
  have hαmem : γ₀ G₀ G₁ G₂ ∈ nbrs β := mem_nbrs_symm hβadj
  have hα'α : dist α' (γ₀ G₀ G₁ G₂) = b := by
    rw [CosetGeom.dist_comm]; exact hα'dist'
  have hα_ne_α2 : γ₀ G₀ G₁ G₂ ≠ α2 := by
    intro h
    rw [h] at hα'α
    omega
  have hnbrs : (nbrs β).ncard = 3 := (hL.point β hβtype).ncard_nbrs
  obtain ⟨α2', hα2'mem, hα2'notin⟩ : ∃ c ∈ nbrs β, c ∉ ({γ₀ G₀ G₁ G₂, α2} : Set _) := by
    have hlt : ({γ₀ G₀ G₁ G₂, α2} : Set (CosetGeom G₀ G₁ G₂)).ncard < (nbrs β).ncard := by
      rw [Set.ncard_pair hα_ne_α2, hnbrs]; norm_num
    exact Set.exists_mem_notMem_of_ncard_lt_ncard hlt
      (Set.finite_of_ncard_pos (by rw [Set.ncard_pair hα_ne_α2]; norm_num))
  have hα2'neα : α2' ≠ γ₀ G₀ G₁ G₂ := fun h => hα2'notin (by
    rw [h]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
  have hα2'neα2 : α2' ≠ α2 := fun h => hα2'notin (by
    rw [h]; exact Set.mem_insert_iff.mpr (Or.inr rfl))
  have hthird : ∀ x ∈ nbrs β, x = γ₀ G₀ G₁ G₂ ∨ x = α2 ∨ x = α2' := by
    intro x hx
    by_cases hxα : x = γ₀ G₀ G₁ G₂
    · exact Or.inl hxα
    · by_cases hxα2 : x = α2
      · exact Or.inr (Or.inl hxα2)
      · right; right
        by_contra hx'
        have hsub : ({γ₀ G₀ G₁ G₂, α2, x} : Set (CosetGeom G₀ G₁ G₂)) ⊆ nbrs β := by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact hαmem
          · exact hα2mem
          · exact hx
        have hcard : ({γ₀ G₀ G₁ G₂, α2, x} : Set (CosetGeom G₀ G₁ G₂)).ncard = 3 := by
          rw [Set.ncard_eq_three]
          exact ⟨γ₀ G₀ G₁ G₂, α2, x, hα_ne_α2, fun h => hxα h.symm,
            fun h => hxα2 h.symm, rfl⟩
        have hfin : (nbrs β).Finite := Set.finite_of_ncard_pos (by rw [hnbrs]; norm_num)
        have heq : ({γ₀ G₀ G₁ G₂, α2, x} : Set (CosetGeom G₀ G₁ G₂)) = nbrs β :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hnbrs]) hfin
        have hmem : α2' ∈ ({γ₀ G₀ G₁ G₂, α2, x} : Set (CosetGeom G₀ G₁ G₂)) :=
          heq ▸ hα2'mem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h | h
        · exact hα2'neα h
        · exact hα2'neα2 h
        · exact hx' h.symm
  have hα2'type : vtype α2' = false := vtype_eq_false_of_mem_nbrs hβtype hα2'mem
  have hcent_not : ¬ E ≤ Subgroup.centralizer (Vv E α' : Set G) := by
    intro hcent
    set N : Subgroup G := stab α' ⊓ Subgroup.centralizer (Vv E α' : Set G) with hNdef
    have hNle : N ≤ stab α' := by
      rw [hNdef]; exact inf_le_left
    have hstabN : stab α' ≤ Subgroup.normalizer (N : Set G) := by
      rw [hNdef]
      refine le_normalizer_inf Subgroup.le_normalizer ?_
      exact (stab_le_normalizer_Vv hA.hypV.normalizes α').trans
        (normalizer_le_normalizer_centralizer (Vv E α' : Subgroup G))
    obtain ⟨e, heE, heQ⟩ := Set.not_subset.mp hQα'
    have heN : e ∈ N := by
      rw [hNdef]; exact ⟨hα'stab heE, hcent heE⟩
    have hEea : IsElemAbelian 2 E := by
      simpa [hEα] using hL.elemAbelian (γ₀ G₀ G₁ G₂) vtype_γ₀
    have he2 : e ^ 2 = 1 := isElemAbelian_pow_eq_one hEea heE
    have htrans := (hL.point α' hα'type).transitive_of_normal N hNle hstabN
      ⟨e, heN, ⟨1, by simpa using he2⟩, heQ⟩
    obtain ⟨l₀, hl₀adj⟩ := exists_adj (α' : CosetGeom G₀ G₁ G₂)
    have hl₀mem : l₀ ∈ nbrs α' := hl₀adj
    have hWle : Vv E l₀ ≤ Vv E α' := Vv_le_Vv_of_mem_nbrs (Z := E) hα'type hl₀mem
    have hEl : ∀ l ∈ nbrs α', Vv E l = Vv E l₀ := by
      intro l hl
      obtain ⟨n, hnN, hnl⟩ := htrans l₀ hl₀mem l hl
      have hnN' : (n : G) ∈ stab α' ∧
          (n : G) ∈ Subgroup.centralizer (Vv E α' : Set G) := hnN
      have hnW : (n : G) ∈ Subgroup.normalizer (Vv E l₀ : Set G) :=
        (Subgroup.centralizer_le_normalizer (Vv E l₀ : Set G))
          ((Subgroup.centralizer_le hWle) hnN'.2)
      calc Vv E l = Vv E (n • l₀) := by rw [hnl]
        _ = conjSub (n : G) (Vv E l₀) := Vv_smul hA.hypV.normalizes n l₀
        _ = Vv E l₀ := conjSub_eq_of_mem_normalizer hnW
    have hstabNW : stab α' ≤ Subgroup.normalizer (Vv E l₀ : Set G) := by
      intro x hx
      apply mem_normalizer_of_conjSub_eq
      have hxG0 : x ∈ G₀ := stab_le α' hx
      have hxsmul : (⟨x, hxG0⟩ : ↥G₀) • α' = α' := smul_eq_of_mem_stab hx
      have hxlmem : (⟨x, hxG0⟩ : ↥G₀) • l₀ ∈ nbrs α' := by
        have h := (smul_adj (⟨x, hxG0⟩ : ↥G₀)).mpr hl₀adj
        rwa [hxsmul] at h
      calc conjSub x (Vv E l₀) = Vv E ((⟨x, hxG0⟩ : ↥G₀) • l₀) :=
            (Vv_smul hA.hypV.normalizes ⟨x, hxG0⟩ l₀).symm
        _ = Vv E l₀ := hEl _ hxlmem
    have hl₀NW : stab l₀ ≤ Subgroup.normalizer (Vv E l₀ : Set G) :=
      stab_le_normalizer_Vv hA.hypV.normalizes l₀
    have hG0NW : G₀ ≤ Subgroup.normalizer (Vv E l₀ : Set G) := by
      intro x hx
      have hx' : x ∈ stab α' ⊔ stab l₀ := by
        rw [hL.sup_stab α' l₀ hl₀mem]; exact hx
      exact sup_le hstabNW hl₀NW hx'
    have hl₀type : vtype l₀ = false := vtype_eq_false_of_mem_nbrs hα'type hl₀mem
    have hWleG0 : Vv E l₀ ≤ G₀ := by
      have h := hL.le_stab l₀ hl₀type l₀ (by rw [CosetGeom.dist_self]; exact Nat.zero_le b)
      exact h.trans (stab_le l₀)
    have hW2 : IsPGroup 2 (Vv E l₀) :=
      isPGroup_of_isElemAbelian (hL.elemAbelian l₀ hl₀type)
    have hWbot : Vv E l₀ ≤ pCoreOf 2 G₀ :=
      le_pCoreOf_of_le_normalizer 2 hWleG0 hG0NW hW2
    have hWbot' : Vv E l₀ = ⊥ := by
      apply le_bot_iff.mp
      rw [← hA.hyp.o2_trivial]
      exact hWbot
    exact (hL.ne_bot l₀ hl₀type) hWbot'
  have hVα'Qβ : ¬ Vv E α' ≤ pCoreOf 2 (stab β) := by
    intro hle
    have hQα_cent : pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ≤
        Subgroup.centralizer (Vv E (γ₀ G₀ G₁ G₂) : Set G) :=
      hL.pCoreOf_le_centralizer (γ₀ G₀ G₁ G₂) vtype_γ₀
    have hleQα : Vv E α' ≤ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
      calc Vv E α' = Vv E α' ⊓ pCoreOf 2 (stab β) := (inf_eq_left.mpr hle).symm
        _ ≤ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) :=
            hQ2 (γ₀ G₀ G₁ G₂) β α' vtype_γ₀ hα'dist' hβadj
    have hleC : Vv E α' ≤ Subgroup.centralizer (E : Set G) := by
      calc Vv E α' ≤ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := hleQα
        _ ≤ Subgroup.centralizer (Vv E (γ₀ G₀ G₁ G₂) : Set G) := hQα_cent
        _ = Subgroup.centralizer (E : Set G) := by rw [hEα]
    exact hcent_not (Subgroup.le_centralizer_iff.mp hleC)
  obtain ⟨l, hlmem, hlQβ⟩ : ∃ l ∈ nbrs α', ¬ Vv E l ≤ pCoreOf 2 (stab β) := by
    by_contra h
    exact hVα'Qβ (Vv_le_of_forall_mem_nbrs hα'type fun l hl => by
      by_contra hq
      exact h ⟨l, hl, hq⟩)
  have hltype : vtype l = false := vtype_eq_false_of_mem_nbrs hα'type hlmem
  have hlβ : dist l β = b := by
    have hlα' : dist l α' = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hlmem
    have hle : dist l β ≤ b := by
      have h1 := dist_triangle hA.hyp.gen l α' β
      omega
    have hge : b - 2 ≤ dist l β := by
      have h1 := dist_triangle hA.hyp.gen α' l β
      have h2 : dist α' l = 1 := by rw [CosetGeom.dist_comm]; exact hlα'
      omega
    have hoddlβ : Odd (dist l β) := Nat.not_even_iff_odd.mp (by
      intro he
      have hvt := (vtype_eq_iff_even_dist hA.hyp.gen l β).mpr he
      rw [hltype, hβtype] at hvt
      exact Bool.false_ne_true hvt)
    obtain ⟨i, hi⟩ := hA.odd
    obtain ⟨j, hj⟩ := hoddlβ
    by_cases hcase : dist l β = b - 2
    · exact absurd (hL.le_pCoreOf_of_dist_lt l hltype β (by omega)) hlQβ
    · omega
  have h6a : Vv E β ⊓ pCoreOf 2 (stab α') ≤ pCoreOf 2 (stab l) :=
    hQ2 l α' β hltype hlβ (mem_nbrs_symm hlmem)
  obtain ⟨f, hfEl, hfQβ⟩ := Set.not_subset.mp hlQβ
  have hW'C : Vv E β ⊓ pCoreOf 2 (stab α') ≤
      Subgroup.centralizer ({f} : Set G) := by
    refine h6a.trans ?_
    have hfsub : ({f} : Set G) ⊆ (Vv E l : Set G) := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rwa [hy]
    exact (hL.pCoreOf_le_centralizer l hltype).trans (Subgroup.centralizer_le hfsub)
  obtain ⟨α'', hα'α'', hβα''⟩ := exists_adj_dist_eq hA.hyp.gen (α := β) (δ := α') (d := b - 2)
    (by rw [CosetGeom.dist_comm, hα'βdist]; omega)
  have hVβle : Vv E β ≤ stab α' ⊓ stab α'' := by
    refine Vv_le_of_forall_mem_nbrs hβtype fun μ hμ => le_inf ?_ ?_
    · have hμtype : vtype μ = false := vtype_eq_false_of_mem_nbrs hβtype hμ
      refine hL.le_stab μ hμtype α' ?_
      have h1 := dist_triangle hA.hyp.gen μ β α'
      have h2 : dist μ β = 1 := by
        rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hμ
      have h3 : dist β α' = b - 1 := by rw [CosetGeom.dist_comm]; exact hα'βdist
      omega
    · have hμtype : vtype μ = false := vtype_eq_false_of_mem_nbrs hβtype hμ
      refine hL.le_stab μ hμtype α'' ?_
      have h1 := dist_triangle hA.hyp.gen μ β α''
      have h2 : dist μ β = 1 := by
        rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hμ
      omega
  have hVβ2 : IsPGroup 2 (Vv E β) :=
    isPGroup_of_isElemAbelian (hL.elemAbelian_δ (by omega) β hβtype)
  have hW'idx : (Vv E β ⊓ pCoreOf 2 (stab α')).relIndex (Vv E β) ≤ 2 :=
    (hL.point α' hα'type).relIndex_le_two α'' hα'α'' (Vv E β) hVβle hVβ2
  have hfstabβ : f ∈ stab β := by
    have h := hL.le_stab l hltype β (by rw [hlβ])
    exact h hfEl
  let fG : ↥G₀ := ⟨f, stab_le β hfstabβ⟩
  have hfGβ : fG • β = β := smul_eq_of_mem_stab hfstabβ
  have hlea : IsElemAbelian 2 (Vv E l) := hL.elemAbelian l hltype
  have hf2 : f ^ 2 = 1 := isElemAbelian_pow_eq_one hlea hfEl
  have hf2elt : ∃ k : ℕ, f ^ 2 ^ k = 1 := ⟨1, by simpa using hf2⟩
  have hla2 : dist l α2 < b := by
    have hlα' : dist l α' = 1 := by
      rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hlmem
    have h1 := dist_triangle hA.hyp.gen l α' α2
    omega
  have hfQα2 : f ∈ pCoreOf 2 (stab α2) :=
    hL.le_pCoreOf_of_dist_lt l hltype α2 hla2 hfEl
  have hfstabα2 : f ∈ stab α2 := (pCoreOf_le 2 (stab α2)) hfQα2
  have hfGα2 : fG • α2 = α2 := smul_eq_of_mem_stab hfstabα2
  have hfα_ne : fG • (γ₀ G₀ G₁ G₂) ≠ γ₀ G₀ G₁ G₂ :=
    (hL.point β hβtype).smul_ne fG hfstabβ hf2elt hfQβ α2 hα2mem hfGα2
      (γ₀ G₀ G₁ G₂) hαmem hα_ne_α2
  have hfα_mem : fG • (γ₀ G₀ G₁ G₂) ∈ nbrs β := by
    have h := (smul_adj fG).mpr hαmem
    rwa [hfGβ] at h
  have hfα_ne_α2 : fG • (γ₀ G₀ G₁ G₂) ≠ α2 := by
    intro h
    have hh : fG • (γ₀ G₀ G₁ G₂) = fG • α2 := by rw [h, hfGα2]
    have heq : (γ₀ G₀ G₁ G₂) = α2 := by
      have := congrArg (fun v => fG⁻¹ • v) hh
      simpa using this
    exact hα_ne_α2 heq
  have hfα : fG • (γ₀ G₀ G₁ G₂) = α2' := by
    rcases hthird (fG • (γ₀ G₀ G₁ G₂)) hfα_mem with h | h | h
    · exact absurd h hfα_ne
    · exact absurd h hfα_ne_α2
    · exact h
  have hconjfE : CFSG.Quasithin.A1b.conjSub f E = Vv E α2' := by
    have h1 : Vv E α2' = CFSG.Quasithin.conjSub f E := by
      rw [← hfα, Vv_smul hA.hypV.normalizes, hEα]
    exact h1.symm
  have hEVβ : E ≤ Vv E β := by
    have h := Vv_le_Vv_of_mem_nbrs (Z := E) hβtype (mem_nbrs_symm hβadj)
    rwa [hEα] at h
  have h6e := relIndex_inf_conjSub_le_two (V := Vv E β)
    (W := Vv E β ⊓ pCoreOf 2 (stab α')) (E := E) (f := f) hW'idx hW'C hEVβ
  have h6e' : (E ⊓ Vv E α2').relIndex E ≤ 2 := by
    rwa [hconjfE] at h6e
  have hRleQα : pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) ≤
      pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
    have hRleQβ : pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) ≤ pCoreOf 2 (stab β) :=
      inf_le_right
    have hQβstabα : pCoreOf 2 (stab β) ≤ stab (γ₀ G₀ G₁ G₂) := by
      have hdist : dist β (γ₀ G₀ G₁ G₂) ≤ 1 := by
        rw [dist_eq_one_iff_adj.mpr hαmem]
      exact (pCoreOf_stab_le_ballStab_one hA.hyp β).trans (ballStab_le_stab_of_dist_le hdist)
    have hRleG₁ : pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) ≤ G₁ := by
      have hRstab : pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) ≤
          stab (γ₀ G₀ G₁ G₂) := hRleQβ.trans hQβstabα
      rwa [stab_γ₀ hA.hyp.le₁] at hRstab
    have hR2 : IsPGroup 2 ↥(pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)) :=
      (pCoreOf_isPGroup 2 (stab β)).to_le inf_le_right
    have hRcent : pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) ≤
        Subgroup.centralizer (Vv E α2' : Set G) :=
      inf_le_left.trans (hL.pCoreOf_le_centralizer α2' hα2'type)
    have hEin : E ⊓ Vv E α2' ≤
        E ⊓ Subgroup.centralizer ((pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) : Subgroup G) : Set G) := by
      refine le_inf inf_le_left ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (Subgroup.mem_centralizer_iff.mp (hRcent hr) x hx.2).symm
    have hle4 : (E ⊓ Subgroup.centralizer
        ((pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) : Subgroup G) : Set G)).relIndex E ≤ 4 := by
      have hmono : (E ⊓ Subgroup.centralizer
          ((pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) : Subgroup G) : Set G)).relIndex E ≤
          (E ⊓ Vv E α2').relIndex E :=
        Subgroup.relIndex_le_of_le_left hEin Subgroup.index_ne_zero_of_finite
      omega
    have hstar := StarBound.le_of_relIndex_le_four hA.star hRleG₁ hR2 hle4
    simpa [stab_γ₀ hA.hyp.le₁] using hstar
  have hcardQ : Nat.card (pCoreOf 2 (stab α2')) =
      Nat.card (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) := by
    have hstab : stab α2' = conjSub (fG : G) (stab (γ₀ G₀ G₁ G₂)) := by
      rw [← hfα, stab_smul]
    rw [hstab, pCoreOf_conjSub, card_conjSub]
  have hrelα : (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β)).relIndex
      (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) = 2 :=
    hL.relIndex_inf (γ₀ G₀ G₁ G₂) β vtype_γ₀ hβadj
  have hrelα2' : (pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)).relIndex
      (pCoreOf 2 (stab α2')) = 2 :=
    hL.relIndex_inf α2' β hα2'type (mem_nbrs_symm hα2'mem)
  have hcardR : Nat.card ↥(pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)) =
      Nat.card ↥(pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β)) := by
    have h1 := Subgroup.relIndex_mul_card
      (H := pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)) (K := pCoreOf 2 (stab α2'))
    have h1' : (pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)).relIndex
        (pCoreOf 2 (stab α2')) * Nat.card ↥(pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)) =
        Nat.card (pCoreOf 2 (stab α2')) := by
      simpa [inf_assoc, inf_left_comm, inf_comm, inf_idem] using h1
    rw [hrelα2'] at h1'
    have h2 := Subgroup.relIndex_mul_card
      (H := pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β))
      (K := pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)))
    have h2' : (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β)).relIndex
        (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) *
        Nat.card ↥(pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β)) =
        Nat.card (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) := by
      simpa [inf_assoc, inf_left_comm, inf_comm, inf_idem] using h2
    rw [hrelα] at h2'
    have h3 : 2 * Nat.card ↥(pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β)) =
        2 * Nat.card ↥(pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β)) := by
      rw [h1', hcardQ, h2']
    omega
  have hReq : pCoreOf 2 (stab α2') ⊓ pCoreOf 2 (stab β) =
      pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hRleQα inf_le_right) (by rw [hcardR])
  obtain ⟨g, hgstabβ, hgα, hgα2, hgα2'⟩ :=
    (hL.point β hβtype).exists_swap_fix (γ₀ G₀ G₁ G₂) hαmem α2 hα2mem α2' hα2'mem
      (Ne.symm hα_ne_α2) hα2'neα (fun h => hα2'neα2 h.symm)
  have hQsmul : ∀ (h : ↥G₀) (γ : CosetGeom G₀ G₁ G₂),
      pCoreOf 2 (stab (h • γ)) = conjSub (h : G) (pCoreOf 2 (stab γ)) := by
    intro h γ
    rw [stab_smul, pCoreOf_conjSub]
  have hQα2_inf : pCoreOf 2 (stab α2) ⊓ pCoreOf 2 (stab β) =
      pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β) := by
    have hgoal := congrArg (fun H => conjSub (g : G) H) hReq
    rw [conjSub_inf, conjSub_inf] at hgoal
    have e1 : conjSub (g : G) (pCoreOf 2 (stab α2')) = pCoreOf 2 (stab α2) := by
      rw [← hQsmul g α2', hgα2']
    have e2 : conjSub (g : G) (pCoreOf 2 (stab β)) = pCoreOf 2 (stab β) := by
      rw [← hQsmul g β, smul_eq_of_mem_stab hgstabβ]
    have e3 : conjSub (g : G) (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) =
        pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
      rw [← hQsmul g (γ₀ G₀ G₁ G₂), hgα]
    rw [e1, e2, e3] at hgoal
    exact hgoal
  have hnotnorm := hL.not_le_normalizer (γ₀ G₀ G₁ G₂) β vtype_γ₀ hβadj
  apply hnotnorm
  intro x hx
  have hxG0 : x ∈ G₀ := stab_le β hx
  let xG : ↥G₀ := ⟨x, hxG0⟩
  have hxβ : xG • β = β := smul_eq_of_mem_stab hx
  have hxαmem : xG • (γ₀ G₀ G₁ G₂) ∈ nbrs β := by
    have h := (smul_adj xG).mpr hαmem
    rwa [hxβ] at h
  have hxclass := hthird (xG • (γ₀ G₀ G₁ G₂)) hxαmem
  have hQx : pCoreOf 2 (stab (xG • (γ₀ G₀ G₁ G₂))) ⊓ pCoreOf 2 (stab β) =
      pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β) := by
    rcases hxclass with h | h | h
    · rw [h]
    · rw [h]; exact hQα2_inf
    · rw [h]; exact hReq
  apply mem_normalizer_of_conjSub_eq
  calc conjSub x (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β))
      = conjSub x (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) ⊓ conjSub x (pCoreOf 2 (stab β)) :=
          conjSub_inf x _ _
    _ = pCoreOf 2 (stab (xG • (γ₀ G₀ G₁ G₂))) ⊓ pCoreOf 2 (stab (xG • β)) := by
          rw [← hQsmul xG (γ₀ G₀ G₁ G₂), ← hQsmul xG β]
    _ = pCoreOf 2 (stab (xG • (γ₀ G₀ G₁ G₂))) ⊓ pCoreOf 2 (stab β) := by rw [hxβ]
    _ = pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ⊓ pCoreOf 2 (stab β) := hQx

end CFSG.Quasithin.F112Crit.APrime

end
