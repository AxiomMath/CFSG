module

public import CFSG.Quasithin.Background.C126A5ExtractFam
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C126A5ExtractAux
public import CFSG.Quasithin.Background.C126A5Perm
public import CFSG.Quasithin.Background.C126Split

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G]

theorem exists_famData {H T M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hmin : MinParabolic H T M) (hred : IsTwoReducedIn H V) (hA5 : A5Case H T V hV) :
    Nonempty (FamData H T V hV) := by
  classical
  obtain ⟨-, I, hfam, hall⟩ := hA5
  obtain ⟨hcard, hJH, hcomm, -, hconj, -, -, -, -, h3⟩ := hfam
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  obtain ⟨L, hL⟩ : I.Nonempty := by
    rcases hcard with h | h <;> exact Finset.card_pos.1 (by omega)
  obtain ⟨θ, β, hβ⟩ := hall L hL
  obtain ⟨hbaum, hJTeq, hcards⟩ := h3 hall
  obtain ⟨hc4, θ', hW⟩ := hcards L hL
  have hLN : L ≤ autI hV (thompsonJ H) := by
    rw [hJH]
    exact le_iSup₂ (f := fun L _ => L) L hL
  have hNL : autI hV (thompsonJ H) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) := by
    rw [hJH]
    have := iSup_inf_le_normalizer I hcomm hL (le_refl L) ⊤ (by simpa using Subgroup.le_normalizer)
    simpa using this
  have hTs : IsSylowTwoOf (autI hV T) (autI hV H) := B2F.isSylowTwoOf_autI hV hHN hmin.isSylow
  have hNH : autI hV (thompsonJ H) ≤ autI hV H := autI_mono hV (thompsonJ_le_self H)
  have hHsN := autI_le_normalizer_autI hV (B6.le_normalizer_thompsonJ H)
  have hSylN : IsSylowTwoOf (autI hV T ⊓ autI hV (thompsonJ H)) (autI hV (thompsonJ H)) :=
    B6.isSylowTwoOf_inf_normal hTs hNH hHsN
  have hSylL : IsSylowTwoOf (autI hV T ⊓ L) L := by
    have := B6.isSylowTwoOf_inf_normal hSylN hLN hNL
    rwa [inf_assoc, inf_eq_right.2 hLN] at this
  have hD8 := card_eq_eight_of_isSylowTwoOf hSylL (card_of_isA5Module ⟨θ, β, hβ⟩)
  set Wst : Subgroup (MulAut (IntMod V hV)) := L ⊓ autI hV (thompsonJ T) with hWst
  set Wθ : Subgroup (Perm (Fin 5)) := (Wst.subgroupOf L).map θ.toMonoidHom with hWθ
  have hmemW : ∀ x (hx : x ∈ L), θ ⟨x, hx⟩ ∈ Wθ ↔ x ∈ Wst := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = ⟨x, hx⟩ := θ.injective hyx
      subst this
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hWcard : Nat.card Wθ = 4 := by
    rw [hWθ, Subgroup.card_map_of_injective (by exact θ.injective),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Wst ≤ L)).toEquiv]
    exact hc4
  have hgen : Wθ = Subgroup.closure {g | g ∈ Wθ ∧ g.IsSwap} := by
    refine le_antisymm (fun w hw => ?_) ((Subgroup.closure_le _).2 fun g hg => hg.1)
    obtain ⟨y, hy, rfl⟩ := hw
    have hy' : (y : MulAut (IntMod V hV)) ∈ Subgroup.closure
        {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ' ⟨x, hx⟩).IsSwap} := by
      rw [← hW]
      exact hy
    have key := Subgroup.closure_induction
      (p := fun x _ => ∃ hxL : x ∈ L, θ ⟨x, hxL⟩ ∈
        Subgroup.closure {g | g ∈ Wθ ∧ g.IsSwap}) ?_ ?_ ?_ ?_ hy'
    · obtain ⟨hyL, hyZ⟩ := key
      exact hyZ
    · rintro x ⟨hx, hxT, hsw⟩
      have hxW : x ∈ Wst := by
        rw [hW]
        exact Subgroup.subset_closure ⟨hx, hxT, hsw⟩
      refine ⟨hx, Subgroup.subset_closure ⟨(hmemW x hx).2 hxW, ?_⟩⟩
      have := (isSwap_mulEquiv_iff (θ'.symm.trans θ) (θ' ⟨x, hx⟩)).2 hsw
      simpa using this
    · exact ⟨L.one_mem, by
        have : (⟨1, L.one_mem⟩ : ↥L) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _⟩
    · rintro x y - - ⟨hxL, hx⟩ ⟨hyL, hy⟩
      refine ⟨L.mul_mem hxL hyL, ?_⟩
      have : (⟨x * y, L.mul_mem hxL hyL⟩ : ↥L) = ⟨x, hxL⟩ * ⟨y, hyL⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ hx hy
    · rintro x - ⟨hxL, hx⟩
      refine ⟨L.inv_mem hxL, ?_⟩
      have : (⟨x⁻¹, L.inv_mem hxL⟩ : ↥L) = ⟨x, hxL⟩⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ hx
  obtain ⟨π, hπ⟩ := klein_swaps Wθ hWcard hgen
  have h1 : swap (π 0) (π 1) ∈ Wθ := by
    rw [hπ]
    exact Subgroup.subset_closure (by simp)
  have h2 : swap (π 2) (π 3) ∈ Wθ := by
    rw [hπ]
    exact Subgroup.subset_closure (by simp)
  set D : Subgroup (Perm (Fin 5)) := ((autI hV T ⊓ L).subgroupOf L).map θ.toMonoidHom with hD
  have hDcard : Nat.card D = 8 := by
    rw [hD, Subgroup.card_map_of_injective (by exact θ.injective),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        autI hV T ⊓ L ≤ L)).toEquiv]
    exact hD8
  have hWD : Wθ ≤ D := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ⟨(autI_mono hV (thompsonJ_le_self T)) hy.2, y.2⟩, rfl⟩
  have hDtop : D ⊔ Subgroup.closure {cyc3 π} = ⊤ := closure_cycle π D hDcard (hWD h1) (hWD h2)
  set C : Subgroup (MulAut (IntMod V hV)) := (Subgroup.closure {cyc3 π}).map (embL L θ) with hC
  have hCL : C ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact embL_mem L θ x
  have hCθ : ∀ φ ∈ C, ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ ∈ Subgroup.closure {cyc3 π} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨embL_mem L θ x, ?_⟩
    have : θ ⟨embL L θ x, embL_mem L θ x⟩ = x := by simp [embL_apply]
    rw [this]
    exact hx
  have hWstN : L ⊓ autI hV (thompsonJ T) ≤
      Subgroup.normalizer (C : Set (MulAut (IntMod V hV))) := by
    intro x hx
    have hmem : θ ⟨x, hx.1⟩ ∈ Wθ := (hmemW x hx.1).2 hx
    rw [hπ] at hmem
    exact mem_normalizer_map_embL hx.1 (closure_swaps_le_normalizer π hmem)
  have hJTC : autI hV (thompsonJ T) ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hV))) :=
    hJTeq.le.trans (iSup_inf_le_normalizer I hcomm hL hCL (autI hV (thompsonJ T)) hWstN)
  refine ⟨⟨L, θ, β, hβ, π, C, ?_, hCL, hCθ, hLN, hNL, hJTC, hbaum.le.trans hJTC, ?_, ?_, ?_⟩⟩
  · rw [hC, Subgroup.card_map_of_injective (embL_injective L θ), card_closure_cyc3]
  · intro X hTX hCX
    set E : Subgroup (Perm (Fin 5)) := (X.subgroupOf L).map θ.toMonoidHom with hE
    have hDE : D ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hTX hy.1, rfl⟩
    have hcE : Subgroup.closure {cyc3 π} ≤ E := by
      rw [Subgroup.closure_le]
      rintro _ rfl
      refine ⟨θ.symm (cyc3 π), hCX ⟨cyc3 π, Subgroup.subset_closure rfl, rfl⟩, by simp⟩
    have hEtop : E = ⊤ := top_le_iff.1 (hDtop ▸ sup_le hDE hcE)
    intro x hx
    have : θ ⟨x, hx⟩ ∈ E := hEtop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have hyx' : y = ⟨x, hx⟩ := θ.injective hyx
    subst hyx'
    exact hy
  · intro X hTX hLX
    rw [hJH]
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨t, htT, ht⟩ := hconj L hL L' hL'
    intro x hx
    rw [← ht, B1.mem_conjAut] at hx
    have h1 : t⁻¹ * x * t ∈ X := hLX hx
    have h2 : t ∈ X := hTX htT
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact X.mul_mem (X.mul_mem h2 h1) (X.inv_mem h2)
  · obtain ⟨y, hy, hyθ⟩ := h2
    exact ⟨(y : MulAut (IntMod V hV)), hy.2, y.2, by simpa using hyθ⟩

end CFSG.Quasithin.C126.A5
