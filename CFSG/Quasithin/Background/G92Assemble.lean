module

public import CFSG.Quasithin.Background.G92Peel
public import CFSG.Quasithin.Background.G8DihedralBasic
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin.G92

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

section Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ι : Type}

theorem conjSub_eq_of_apply_mem {g : GLV V} {Y : Submodule (ZMod 2) V}
    (h : ∀ u ∈ Y, g u ∈ Y) : conjSub g Y = Y := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_conjSub g Y)
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

theorem iSup_fix {F : Frame V ι} {Hs : ι → Subgroup (GLV V)}
    (hclos : ∀ j, Hs j = Subgroup.closure {F.x j, F.a j}) (S : Finset ι)
    (Y : Submodule (ZMod 2) V) (hx : ∀ j ∈ S, ∀ u ∈ Y, F.x j u = u)
    (ha : ∀ j ∈ S, ∀ u ∈ Y, F.a j u = u) : ∀ g ∈ (⨆ j ∈ S, Hs j), ∀ u ∈ Y, g u = u := by
  have hle : (⨆ j ∈ S, Hs j) ≤ centralizerOn ⊤ Y := by
    refine iSup₂_le fun j hj => ?_
    rw [hclos j, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨Subgroup.mem_top _, hx j hj⟩
    · exact ⟨Subgroup.mem_top _, ha j hj⟩
  intro g hg u hu
  exact (hle hg).2 u hu

theorem iSup_apply_mem {F : Frame V ι} {Hs : ι → Subgroup (GLV V)}
    (hclos : ∀ j, Hs j = Subgroup.closure {F.x j, F.a j}) (S : Finset ι)
    (Y : Submodule (ZMod 2) V) (hx : ∀ j ∈ S, ∀ u ∈ Y, F.x j u ∈ Y)
    (ha : ∀ j ∈ S, ∀ u ∈ Y, F.a j u ∈ Y) : ∀ g ∈ (⨆ j ∈ S, Hs j), ∀ u ∈ Y, g u ∈ Y := by
  have hle : (⨆ j ∈ S, Hs j) ≤ stabilizerOf ⊤ Y := by
    refine iSup₂_le fun j hj => ?_
    rw [hclos j, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨Subgroup.mem_top _, conjSub_eq_of_apply_mem (hx j hj)⟩
    · exact ⟨Subgroup.mem_top _, conjSub_eq_of_apply_mem (ha j hj)⟩
  intro g hg u hu
  have := (hle hg).2
  rw [← this]
  exact apply_mem_conjSub hu

theorem sup_eq_closure_four {G : Type*} [Group G] {H₁ H₂ : Subgroup G} {x₁ a₁ x₂ a₂ : G}
    (h₁ : H₁ = Subgroup.closure {x₁, a₁}) (h₂ : H₂ = Subgroup.closure {x₂, a₂}) :
    H₁ ⊔ H₂ = Subgroup.closure {x₁, a₁, x₂, a₂} := by
  rw [h₁, h₂, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end Aux

section Assemble

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_block_enum {m : ℕ} (F : Frame V (Fin m)) (hB : BlockData F (Bf F)) (i₁ : Fin m) :
    ∃ (r : ℕ) (S : Fin r → Finset (Fin m)) (h0 : 0 < r),
      (∀ k, ∃ i, S k = Bf F i) ∧ (∀ i, ∃ k, i ∈ S k) ∧
        (∀ k k' j, j ∈ S k → j ∈ S k' → k = k') ∧ i₁ ∈ S ⟨0, h0⟩ := by
  classical
  let κ := {b : Finset (Fin m) // ∃ i, Bf F i = b}
  let e : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  have hne : Nonempty κ := ⟨⟨Bf F i₁, i₁, rfl⟩⟩
  have hr : 0 < Nat.card κ := Nat.card_pos
  let k₀ : Fin (Nat.card κ) := e ⟨Bf F i₁, i₁, rfl⟩
  let ε : Fin (Nat.card κ) ≃ κ := (Equiv.swap k₀ ⟨0, hr⟩).trans e.symm
  refine ⟨Nat.card κ, fun k => (ε k).1, hr, fun k => ?_, fun i => ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := (ε k).2
    exact ⟨i, hi.symm⟩
  · refine ⟨ε.symm ⟨Bf F i, i, rfl⟩, ?_⟩
    show i ∈ (ε (ε.symm ⟨Bf F i, i, rfl⟩)).1
    rw [Equiv.apply_symm_apply]
    exact mem_Bf_self i
  · intro k k' j hk hk'
    obtain ⟨i, hi⟩ := (ε k).2
    obtain ⟨i', hi'⟩ := (ε k').2
    have h1 : (ε k).1 = Bf F j := by
      have hj : j ∈ Bf F i := by
        rw [hi]
        exact hk
      rw [← hi, hB.block_eq i j hj]
    have h2 : (ε k').1 = Bf F j := by
      have hj : j ∈ Bf F i' := by
        rw [hi']
        exact hk'
      rw [← hi', hB.block_eq i' j hj]
    exact ε.injective (Subtype.ext (h1.trans h2.symm))
  · show i₁ ∈ (ε ⟨0, hr⟩).1
    have : ε ⟨0, hr⟩ = e.symm k₀ := by
      show e.symm (Equiv.swap k₀ ⟨0, hr⟩ ⟨0, hr⟩) = e.symm k₀
      rw [Equiv.swap_apply_right]
    rw [this]
    show i₁ ∈ (e.symm (e ⟨Bf F i₁, i₁, rfl⟩)).1
    rw [Equiv.symm_apply_apply]
    exact mem_Bf_self i₁

@[expose] def OrthHyp (Orth : Subgroup (GLV V) → Submodule (ZMod 2) V → Prop) : Prop :=
  ∀ (x₁ a₁ x₂ a₂ : GLV V) (K : Subgroup (GLV V)), K = Subgroup.closure {x₁, a₁, x₂, a₂} →
    ∀ U : Submodule (ZMod 2) V, Module.finrank (ZMod 2) U = 4 →
    x₁ ^ 3 = 1 → x₂ ^ 3 = 1 → a₁ * a₁ = 1 → a₂ * a₂ = 1 →
    a₁ * x₁ * a₁⁻¹ = x₁⁻¹ → a₂ * x₂ * a₂⁻¹ = x₂⁻¹ →
    x₁ * x₂ = x₂ * x₁ → x₁ * a₂ = a₂ * x₁ → a₁ * x₂ = x₂ * a₁ → a₁ * a₂ = a₂ * a₁ →
    (∀ g ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)), ∀ u ∈ U, g u ∈ U) →
    (∀ u ∈ U, x₁ u = u → u = 0) → (∀ u ∈ U, x₂ u = u → u = 0) →
    (∀ g ∈ K, (∀ u ∈ U, g u = u) → g = 1) → Orth K U

theorem assemble {m : ℕ} (Orth : Subgroup (GLV V) → Submodule (ZMod 2) V → Prop)
    (horth : OrthHyp Orth) (F : Frame V (Fin m)) (Hs : Fin m → Subgroup (GLV V))
    (hD : IsDihedralFamily Hs F.p) (hclos : ∀ j, Hs j = Subgroup.closure {F.x j, F.a j})
    (hx1 : ∀ i, F.x i ≠ 1) (hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j))
    (i₁ : Fin m) (hP : PrimeShape F i₁) (X A : Subgroup (GLV V)) (hge : A ≤ ⨆ i, Hs i)
    (hle : (⨆ i, Hs i) ≤ X ⊔ A) :
    ∃ (r : ℕ) (Gs : Fin r → Subgroup (GLV V)),
      (⨆ i, Gs i) ≤ X ⊔ A ∧ A ≤ ⨆ i, Gs i ∧ iSupIndep Gs ∧
      (∀ i j, i ≠ j → ∀ x ∈ Gs i, ∀ y ∈ Gs j, x * y = y * x) ∧
      (iSupIndep (fun i => commSpace (Gs i) ⊤) ∧ (⨆ i, commSpace (Gs i) ⊤) = ⊤) ∧
      (F.p i₁ = 5 → ∃ h : 0 < r, Nonempty (↥(Gs ⟨0, h⟩) ≃* DihedralGroup 5) ∧
        Module.finrank (ZMod 2) ↥(commSpace (Gs ⟨0, h⟩) ⊤) = 4) ∧
      (∀ k : Fin r, (F.p i₁ = 3 ∨ 1 ≤ k.val) →
        ((Nonempty (↥(Gs k) ≃* DihedralGroup 3) ∧
            Module.finrank (ZMod 2) ↥(commSpace (Gs k) ⊤) = 2) ∨
          Orth (Gs k) (commSpace (Gs k) ⊤))) := by
  classical
  have hB : BlockData F (Bf F) := blockData F hx1 hdim hP
  obtain ⟨r, S, hr, hSb, hcover, hpart, hS0⟩ := exists_block_enum F hB i₁
  set Gs : Fin r → Subgroup (GLV V) := fun k => ⨆ j ∈ S k, Hs j with hGs
  have hmemS : ∀ k j, j ∈ S k → S k = Bf F j := by
    intro k j hj
    obtain ⟨i, hi⟩ := hSb k
    have hj' : j ∈ Bf F i := by
      rw [← hi]
      exact hj
    rw [hi, hB.block_eq i j hj']
  have hxmem : ∀ j, F.x j ∈ Hs j := fun j => by
    rw [hclos j]
    exact Subgroup.subset_closure (by simp)
  have hamem : ∀ j, F.a j ∈ Hs j := fun j => by
    rw [hclos j]
    exact Subgroup.subset_closure (by simp)
  have hHle : ∀ k j, j ∈ S k → Hs j ≤ Gs k := fun k j hj =>
    le_iSup₂ (f := fun j (_ : j ∈ S k) => Hs j) j hj
  have hnotin : ∀ k i'' j, i'' ∉ S k → j ∈ S k → j ∉ Bf F i'' := by
    intro k i'' j hi'' hj hjB
    apply hi''
    have h1 := hB.block_eq i'' j hjB
    have h2 := hmemS k j hj
    rw [h2, h1]
    exact mem_Bf_self i''
  have hGfix : ∀ k, ∀ i'', i'' ∉ S k → ∀ g ∈ Gs k, ∀ u ∈ Rsp F i'', g u = u := by
    intro k i'' hi'' g hg u hu
    refine iSup_fix hclos (S k) (Rsp F i'') (fun j hj u hu => ?_) (fun j hj u hu => ?_) g hg u hu
    · exact (hB.trivial_off i'' j (hnotin k i'' j hi'' hj) u hu).1
    · exact (hB.trivial_off i'' j (hnotin k i'' j hi'' hj) u hu).2
  have hGstab : ∀ k i, ∀ g ∈ Gs k, ∀ u ∈ Rsp F i, g u ∈ Rsp F i := fun k i =>
    iSup_apply_mem hclos (S k) (Rsp F i) (fun j _ => Rsp_x_inv F i j) (fun j _ => Rsp_a_inv F i j)
  have hReqS : ∀ k i' i, i' ∈ S k → i ∈ S k → Rsp F i' = Rsp F i := by
    intro k i' i hi' hi
    have h1 := hmemS k i hi
    rw [h1] at hi'
    exact hB.R_eq i i' hi'
  have hcommSpace : ∀ k i, i ∈ S k → commSpace (Gs k) ⊤ = Rsp F i := by
    intro k i hi
    apply le_antisymm
    · rw [commSpace_le_iff]
      intro g hg u _
      have hu : u ∈ ⨆ i', Rsp F i' := by
        rw [hB.sup_eq_top]
        exact Submodule.mem_top
      refine Submodule.iSup_induction (fun i' => Rsp F i') (motive := fun u => g u - u ∈ Rsp F i)
        hu ?_ ?_ ?_
      · intro i' u hu'
        by_cases hi' : i' ∈ S k
        · rw [hReqS k i' i hi' hi] at hu'
          exact sub_mem (hGstab k i g hg u hu') hu'
        · rw [hGfix k i' hi' g hg u hu', sub_self]
          exact zero_mem _
      · simp
      · intro u v hu hv
        have : g (u + v) - (u + v) = (g u - u) + (g v - v) := by
          rw [map_add]
          abel
        rw [this]
        exact add_mem hu hv
    · intro v hv
      obtain ⟨s, -, rfl⟩ := mem_commSp.1 hv
      exact sub_mem_commSpace (hHle k i hi (hxmem i)) (Submodule.mem_top (x := s))
  have hG1 : (⨆ i, Gs i) ≤ X ⊔ A := by
    refine iSup_le fun k => iSup₂_le fun j _ => ?_
    exact (le_iSup Hs j).trans hle
  have hG2 : A ≤ ⨆ i, Gs i := by
    refine hge.trans (iSup_le fun j => ?_)
    obtain ⟨k, hk⟩ := hcover j
    exact (hHle k j hk).trans (le_iSup Gs k)
  have htriv_all : ∀ g : GLV V, (∀ i, ∀ u ∈ Rsp F i, g u = u) → g = 1 := by
    intro g hg
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ ⨆ i', Rsp F i' := by
      rw [hB.sup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun i' => Rsp F i') (motive := fun u => g u = u) hv ?_ ?_ ?_
    · intro i' u hu
      exact hg i' u hu
    · exact map_zero g
    · intro u v hu hv
      rw [map_add, hu, hv]
  have hG3 : iSupIndep Gs := by
    rw [iSupIndep_def]
    intro k
    rw [Subgroup.disjoint_def]
    intro g hg hg'
    apply htriv_all
    intro i u hu
    by_cases hi : i ∈ S k
    · have hle : (⨆ (k' : Fin r) (_ : k' ≠ k), Gs k') ≤ centralizerOn ⊤ (Rsp F i) := by
        refine iSup₂_le fun k' hk' => ?_
        intro h hh
        exact ⟨Subgroup.mem_top _, fun u hu =>
          hGfix k' i (fun hik' => hk' (hpart k' k i hik' hi)) h hh u hu⟩
      exact (hle hg').2 u hu
    · exact hGfix k i hi g hg u hu
  have hsub : ∀ S : Finset (Fin m), (⨆ j : S, Hs j) = ⨆ j ∈ S, Hs j := fun S =>
    le_antisymm (iSup_le fun j => le_iSup₂ (f := fun j (_ : j ∈ S) => Hs j) j.1 j.2)
      (iSup₂_le fun j hj => le_iSup (fun j : S => Hs j) ⟨j, hj⟩)
  have hG4 : ∀ k k', k ≠ k' → ∀ x ∈ Gs k, ∀ y ∈ Gs k', x * y = y * x := by
    intro k k' hkk x hx y hy
    have hcomm : ∀ (j : S k) (j' : S k'), ∀ x ∈ Hs j, ∀ y ∈ Hs j', x * y = y * x := by
      intro j j' x hx y hy
      refine hD.commute j j' (fun h => ?_) x hx y hy
      refine hkk (hpart k k' j j.2 ?_)
      rw [h]
      exact j'.2
    exact G8.iSup_commute hcomm x (by rw [hsub]; exact hx) y (by rw [hsub]; exact hy)
  have hU1 : iSupIndep (fun k => commSpace (Gs k) ⊤) := by
    rw [iSupIndep_def]
    intro k
    obtain ⟨i, hSi⟩ := hSb k
    have hiS : i ∈ S k := by
      rw [hSi]
      exact mem_Bf_self i
    rw [hcommSpace k i hiS]
    refine (hB.indep i).mono_right ?_
    refine iSup₂_le fun k' hk' => ?_
    obtain ⟨i', hSi'⟩ := hSb k'
    have hi'S : i' ∈ S k' := by
      rw [hSi']
      exact mem_Bf_self i'
    rw [hcommSpace k' i' hi'S]
    refine le_iSup₂ (f := fun j (_ : j ∈ {j | j ∉ Bf F i}) => Rsp F j) i' ?_
    intro hmem
    apply hk'
    refine hpart k' k i' hi'S ?_
    rw [hSi]
    exact hmem
  have hU2 : (⨆ k, commSpace (Gs k) ⊤) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Submodule (ZMod 2) V) = ⨆ i, Rsp F i := hB.sup_eq_top.symm
      _ ≤ ⨆ k, commSpace (Gs k) ⊤ := by
        refine iSup_le fun i => ?_
        obtain ⟨k, hk⟩ := hcover i
        rw [← hcommSpace k i hk]
        exact le_iSup (fun k => commSpace (Gs k) ⊤) k
  have hall3 : ∀ k : Fin r, (F.p i₁ = 3 ∨ 1 ≤ k.val) → ∀ j ∈ S k, F.p j = 3 := by
    intro k hk j hj
    by_cases hji : j = i₁
    · rcases hk with h3 | h1
      · rw [hji]
        exact h3
      · exfalso
        have hk0 : k = ⟨0, hr⟩ := hpart k ⟨0, hr⟩ j hj (by rw [hji]; exact hS0)
        rw [hk0] at h1
        simp at h1
    · exact hP.three j hji
  have hlast : ∀ k, (∀ j ∈ S k, F.p j = 3) →
      ((Nonempty (↥(Gs k) ≃* DihedralGroup 3) ∧
          Module.finrank (ZMod 2) ↥(commSpace (Gs k) ⊤) = 2) ∨
        Orth (Gs k) (commSpace (Gs k) ⊤)) := by
    intro k hk3
    obtain ⟨i, hSi⟩ := hSb k
    have hiS : i ∈ S k := by
      rw [hSi]
      exact mem_Bf_self i
    have hcomm := hcommSpace k i hiS
    rcases hB.card_cases i with hc1 | ⟨hc2, -⟩
    · left
      have hBi : Bf F i = {i} := by
        obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc1
        have hia : i ∈ Bf F i := mem_Bf_self i
        rw [ha, Finset.mem_singleton] at hia
        rw [ha, hia]
      have hGk : Gs k = Hs i := by
        show (⨆ j ∈ S k, Hs j) = Hs i
        rw [hSi, hBi, Finset.iSup_singleton]
      have hpi3 : F.p i = 3 := hk3 i hiS
      refine ⟨?_, ?_⟩
      · obtain ⟨e⟩ := hD.iso i
        rw [hpi3] at e
        rw [hGk]
        exact ⟨e⟩
      · rw [hcomm, hB.finrank_eq i, hBi, Finset.sum_singleton, hpi3, gFun_three]
    · right
      have hJne : JW F i ≠ ∅ := by
        intro hJ
        have hBi : Bf F i = {i} := by simp [Bf, hJ]
        rw [hBi] at hc2
        simp at hc2
      obtain ⟨i', hi'⟩ := Finset.nonempty_iff_ne_empty.2 hJne
      obtain ⟨hJi, -, hpi, hpi'⟩ := partner_pair F hx1 hdim hP hi'
      have hii' : i' ≠ i := ((mem_JW F).1 hi').1
      have hBi : Bf F i = {i, i'} := by simp [Bf, hJi]
      have hGk : Gs k = Hs i ⊔ Hs i' := by
        show (⨆ j ∈ S k, Hs j) = Hs i ⊔ Hs i'
        rw [hSi, hBi, Finset.iSup_insert, Finset.iSup_singleton]
      have hReq : Rsp F i' = Rsp F i := hB.R_eq i i' (Bf_of_mem_JW hi')
      rw [hcomm]
      refine horth (F.x i) (F.a i) (F.x i') (F.a i') (Gs k) ?_ (Rsp F i) ?_ ?_ ?_ (F.asq i)
        (F.asq i') (F.conj i) (F.conj i') (F.xx i i' hii'.symm) (F.xa i i' hii'.symm)
        (F.xa i' i hii').symm (F.aa i i' hii'.symm) ?_ (Rsp_fpf F i) ?_ ?_
      · rw [hGk]
        exact sup_eq_closure_four (hclos i) (hclos i')
      · rw [hB.finrank_eq i, hBi, Finset.sum_pair hii'.symm, hpi, hpi', gFun_three]
      · have := F.xpow i
        rwa [hpi] at this
      · have := F.xpow i'
        rwa [hpi'] at this
      · intro g hg u hu
        rcases hg with rfl | rfl | rfl | rfl
        · exact Rsp_x_inv F i i u hu
        · exact Rsp_a_inv F i i u hu
        · exact Rsp_x_inv F i i' u hu
        · exact Rsp_a_inv F i i' u hu
      · intro u hu hfix
        refine Rsp_fpf F i' u ?_ hfix
        rw [hReq]
        exact hu
      · intro g hg hgfix
        apply htriv_all
        intro i'' u hu
        by_cases hi'' : i'' ∈ S k
        · rw [hReqS k i'' i hi'' hiS] at hu
          exact hgfix u hu
        · exact hGfix k i'' hi'' g hg u hu
  have hspec : F.p i₁ = 5 → ∃ h : 0 < r, Nonempty (↥(Gs ⟨0, h⟩) ≃* DihedralGroup 5) ∧
      Module.finrank (ZMod 2) ↥(commSpace (Gs ⟨0, h⟩) ⊤) = 4 := by
    intro h5
    have hSi : S ⟨0, hr⟩ = Bf F i₁ := hmemS _ _ hS0
    have hBi : Bf F i₁ = {i₁} := by
      rcases hB.card_cases i₁ with hc1 | ⟨-, h3⟩
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc1
        have hia := mem_Bf_self (F := F) i₁
        rw [ha, Finset.mem_singleton] at hia
        rw [ha, hia]
      · exfalso
        have := h3 i₁ (mem_Bf_self i₁)
        rw [h5] at this
        omega
    have hGk : Gs ⟨0, hr⟩ = Hs i₁ := by
      show (⨆ j ∈ S ⟨0, hr⟩, Hs j) = Hs i₁
      rw [hSi, hBi, Finset.iSup_singleton]
    refine ⟨hr, ?_, ?_⟩
    · obtain ⟨e⟩ := hD.iso i₁
      rw [h5] at e
      rw [hGk]
      exact ⟨e⟩
    · rw [hcommSpace ⟨0, hr⟩ i₁ hS0, hB.finrank_eq i₁, hBi, Finset.sum_singleton, h5, gFun_five]
  exact ⟨r, Gs, hG1, hG2, hG3, hG4, ⟨hU1, hU2⟩, hspec, fun k hk => hlast k (hall3 k hk)⟩

end Assemble

end CFSG.Quasithin.G92
