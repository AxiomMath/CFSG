module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGQTwoDegFramePath
import CFSG.ClassicalInvolution.Generic.TypeA

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

private def qTwoDegFrame_permCongrMulEquiv {α β : Type*} (f : α ≃ β) :
    Equiv.Perm α ≃* Equiv.Perm β where
  toFun σ := f.symm.trans (σ.trans f)
  invFun σ := f.trans (σ.trans f.symm)
  left_inv σ := by
    ext x
    simp
  right_inv σ := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp

private theorem qTwoDegFrame_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ≃ β) (a b : α) :
    qTwoDegFrame_permCongrMulEquiv f (Equiv.swap a b) = Equiv.swap (f a) (f b) := by
  classical
  ext x
  change f ((Equiv.swap a b) (f.symm x)) = (Equiv.swap (f a) (f b)) x
  by_cases h : x = f a
  · subst h
    simp
  · by_cases h2 : x = f b
    · subst h2
      simp [h]
    · have hx : f.symm x ≠ a := fun hh =>
        h ((f.apply_symm_apply x).symm.trans (congrArg f hh))
      have hx2 : f.symm x ≠ b := fun hh =>
        h2 ((f.apply_symm_apply x).symm.trans (congrArg f hh))
      simp [Equiv.swap_apply_def, h, h2, hx, hx2]

theorem qTwoDegFrame_perm_equiv {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (hP : ∀ i : ι, GGIsReflection 3 ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    {N : ℕ} (hN : 2 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e') :
    ∃ ρ : Equiv.Perm (Fin N) ≃* ↥A,
      (∀ a b : Fin N, a ≠ b → GGIsReflection 3 ((ρ (Equiv.swap a b) : ↥A) : MulAut ↥Bs)) ∧
      ∀ (k : ℕ) (hk : k + 1 < N),
        ((ρ (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) : ↥A) : MulAut ↥Bs) =
          ((e (M.simple (e' ⟨k, by omega⟩)) : ↥A) : MulAut ↥Bs) := by
  classical
  subst hM
  have hN1 : 1 ≤ N := by omega
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm (N - 1)
  let f : Fin N ≃ Fin (N - 1 + 1) := finCongr hsub.symm
  let pc : Equiv.Perm (Fin N) ≃* Equiv.Perm (Fin (N - 1 + 1)) :=
    qTwoDegFrame_permCongrMulEquiv f
  let eb : (CoxeterMatrix.A (N - 1)).Group ≃* ↥A :=
    (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A (N - 1)) e').symm.trans e
  let ρeq : Equiv.Perm (Fin N) ≃* ↥A := pc.trans (e0.symm.trans eb)
  have hρrefl : ∀ a b : Fin N, a ≠ b →
      GGIsReflection 3 ((ρeq (Equiv.swap a b) : ↥A) : MulAut ↥Bs) := by
    let i0 : Fin (N - 1) := ⟨0, by omega⟩
    let E2 : Equiv.Perm (Fin (N - 1 + 1)) →* MulAut ↥Bs :=
      (A.subtype.comp ρeq.toMonoidHom).comp pc.symm.toMonoidHom
    have hfix : GGIsReflection 3 (E2 (Equiv.swap i0.castSucc i0.succ)) := by
      have hsimple : e0.symm (Equiv.swap i0.castSucc i0.succ) =
          (CoxeterMatrix.A (N - 1)).simple i0 := by
        rw [← he0 i0, MulEquiv.symm_apply_apply]
      have hE : (E2 (Equiv.swap i0.castSucc i0.succ) : MulAut ↥Bs) =
          ((eb ((CoxeterMatrix.A (N - 1)).simple i0) : ↥A) : MulAut ↥Bs) := by
        simp [E2, ρeq, hsimple]
      have hsym : (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A (N - 1)) e').symm
          ((CoxeterMatrix.A (N - 1)).simple i0) =
            (CoxeterMatrix.reindex e' (CoxeterMatrix.A (N - 1))).simple (e' i0) :=
        CoxeterMatrix.reindexGroupEquiv_symm_apply_simple (CoxeterMatrix.A (N - 1)) e' i0
      rw [hE]
      have hEb : ((eb ((CoxeterMatrix.A (N - 1)).simple i0) : ↥A) : MulAut ↥Bs) =
          ((e ((CoxeterMatrix.reindex e' (CoxeterMatrix.A (N - 1))).simple (e' i0)) :
            ↥A) : MulAut ↥Bs) := by
        simp [eb, hsym]
      rw [hEb]
      exact hP (e' i0)
    intro a b hab
    let u : Fin (N - 1 + 1) := f a
    let v : Fin (N - 1 + 1) := f b
    have huv : u ≠ v := by
      intro h
      exact hab (f.injective (by simpa [u, v] using h))
    have hswap : pc.symm (Equiv.swap u v) = Equiv.swap a b := by
      have h1 : pc (Equiv.swap a b) = Equiv.swap u v := by
        simpa [pc, u, v] using qTwoDegFrame_permCongr_swap f a b
      rw [← h1, MulEquiv.symm_apply_apply]
    have hr := ggIsReflection_swap_of_swap (p := 3) E2 (a := i0.castSucc) (b := i0.succ)
      (by exact Fin.castSucc_lt_succ.ne) hfix (x := u) (y := v) huv
    simpa [E2, hswap] using hr
  refine ⟨ρeq, hρrefl, ?_⟩
  intro k hk
  have hkd : k < N - 1 := by omega
  let kd : Fin (N - 1) := ⟨k, hkd⟩
  have hf1 : f ⟨k, by omega⟩ = kd.castSucc := Fin.ext rfl
  have hf2 : f ⟨k + 1, hk⟩ = kd.succ := Fin.ext rfl
  have hkd_eq : kd = (⟨k, by omega⟩ : Fin (N - 1)) := Fin.ext rfl
  have hpc : pc (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) =
      Equiv.swap kd.castSucc kd.succ := by
    rw [show pc (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) =
        Equiv.swap (f ⟨k, by omega⟩) (f ⟨k + 1, hk⟩) from
      qTwoDegFrame_permCongr_swap f _ _, hf1, hf2]
  have hsimple : e0.symm (Equiv.swap kd.castSucc kd.succ) =
      (CoxeterMatrix.A (N - 1)).simple kd := by
    rw [← he0 kd, MulEquiv.symm_apply_apply]
  have hsym : (CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A (N - 1)) e').symm
      ((CoxeterMatrix.A (N - 1)).simple kd) =
        (CoxeterMatrix.reindex e' (CoxeterMatrix.A (N - 1))).simple (e' kd) :=
    CoxeterMatrix.reindexGroupEquiv_symm_apply_simple (CoxeterMatrix.A (N - 1)) e' kd
  show ((ρeq (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) : ↥A) : MulAut ↥Bs) =
    ((e ((CoxeterMatrix.reindex e' (CoxeterMatrix.A (N - 1))).simple
      (e' ⟨k, by omega⟩)) : ↥A) : MulAut ↥Bs)
  rw [show ρeq (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) =
      eb (e0.symm (pc (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩))) from rfl,
    hpc, hsimple]
  have hEb : ((eb ((CoxeterMatrix.A (N - 1)).simple kd) : ↥A) : MulAut ↥Bs) =
      ((e ((CoxeterMatrix.reindex e' (CoxeterMatrix.A (N - 1))).simple (e' kd)) :
        ↥A) : MulAut ↥Bs) := by
    simp [eb, hsym]
  rw [hEb, hkd_eq]

theorem qTwoDegFrame_card_weyl {Bs : Subgroup G} {AL : Subgroup (MulAut ↥Bs)} {m : ℕ}
    (hm : 1 ≤ m) (hW : GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) AL) :
    Nat.card ↥AL = m.factorial := by
  obtain ⟨eL, -⟩ := hW
  obtain ⟨e0, -⟩ := ggCoxeterA_mulEquivPerm (m - 1)
  calc Nat.card ↥AL = Nat.card (CoxeterMatrix.A (m - 1)).Group :=
        Nat.card_congr eL.symm.toEquiv
    _ = Nat.card (Equiv.Perm (Fin (m - 1 + 1))) := Nat.card_congr e0.toEquiv
    _ = (m - 1 + 1).factorial := by rw [Nat.card_perm, Nat.card_fin]
    _ = m.factorial := by rw [Nat.sub_add_cancel hm]

private theorem qTwoDegFrame_simple_not_commute (n : ℕ)
    (e0 : (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)))
    (he0 : ∀ k : Fin n, e0 ((CoxeterMatrix.A n).simple k) = Equiv.swap k.castSucc k.succ)
    {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    ¬ Commute ((CoxeterMatrix.A n).simple i)
      ((CoxeterMatrix.A n).simple ⟨(i : ℕ) + 1, hi⟩) := by
  intro h
  have h' : Commute (Equiv.swap i.castSucc i.succ)
      (Equiv.swap (⟨(i : ℕ) + 1, hi⟩ : Fin n).castSucc
        (⟨(i : ℕ) + 1, hi⟩ : Fin n).succ) := by
    simpa only [he0] using h.map e0
  exact (CFSG.ClassicalInvolution.Generic.adjSwap_not_comm (n := n) (i := i)
    (j := ⟨(i : ℕ) + 1, hi⟩) (by simp)) h'

private theorem qTwoDegFrame_simple_commute (n : ℕ)
    (e0 : (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)))
    (he0 : ∀ k : Fin n, e0 ((CoxeterMatrix.A n).simple k) = Equiv.swap k.castSucc k.succ)
    {i j : Fin n} (hij : (i : ℕ) + 1 < j) :
    Commute ((CoxeterMatrix.A n).simple i) ((CoxeterMatrix.A n).simple j) := by
  have h' : Commute (Equiv.swap i.castSucc i.succ) (Equiv.swap j.castSucc j.succ) :=
    CFSG.ClassicalInvolution.Generic.adjSwap_comm (n := n) hij
  have h2 := h'.map e0.symm
  simpa only [← he0 i, ← he0 j, MulEquiv.symm_apply_apply] using h2

private theorem qTwoDegFrame_simple_ne (n : ℕ)
    (e0 : (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)))
    (he0 : ∀ k : Fin n, e0 ((CoxeterMatrix.A n).simple k) = Equiv.swap k.castSucc k.succ)
    {i j : Fin n} (hij : (i : ℕ) + 1 < j) :
    (CoxeterMatrix.A n).simple i ≠ (CoxeterMatrix.A n).simple j := by
  intro h
  have h'' : Equiv.swap i.castSucc i.succ = Equiv.swap j.castSucc j.succ := by
    simpa only [he0] using congrArg e0 h
  have h2 : CFSG.ClassicalInvolution.Generic.adjSwap n i =
      CFSG.ClassicalInvolution.Generic.adjSwap n j := h''
  exact absurd (congrArg Fin.val (CFSG.ClassicalInvolution.Generic.adjSwap_injective n h2))
    (by omega)

theorem qTwoDegFrame_path {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    {A AL : Subgroup (MulAut ↥Bs)} {N : ℕ} (ρ : Equiv.Perm (Fin N) ≃* ↥A)
    (hρ : ∀ a b : Fin N, a ≠ b → GGIsReflection 3 ((ρ (Equiv.swap a b) : ↥A) : MulAut ↥Bs))
    (hAL : AL ≤ A) {m : ℕ} (hm : 2 ≤ m)
    (hW : GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) AL) :
    ∃ p : ℕ → Fin N, (∀ i < m, ∀ j < m, p i = p j → i = j) ∧
      AL = Subgroup.map (A.subtype.comp ρ.toMonoidHom)
        (Subgroup.closure ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio (m - 1))) := by
  classical
  obtain ⟨n, hn_eq⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  subst hn_eq
  have hmn : n + 1 - 1 = n := by omega
  rw [hmn] at hW ⊢
  have hn1 : 1 ≤ n := by omega
  let E : Equiv.Perm (Fin N) →* MulAut ↥Bs := A.subtype.comp ρ.toMonoidHom
  have hEinj : Function.Injective E := by
    intro x y hxy
    exact ρ.injective (Subtype.val_injective hxy)
  have hρE : ∀ a b : Fin N, a ≠ b → GGIsReflection 3 (E (Equiv.swap a b)) :=
    fun a b hab => hρ a b hab
  obtain ⟨eL, heL⟩ := hW
  let ψ : (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin N) :=
    ρ.symm.toMonoidHom.comp ((Subgroup.inclusion hAL).comp eL.toMonoidHom)
  have hψE : ∀ w : (CoxeterMatrix.A n).Group, E (ψ w) = ((eL w : ↥AL) : MulAut ↥Bs) := by
    intro w
    simp [E, ψ, Subgroup.inclusion]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : E (ψ a) = E (ψ b) := by rw [hab]
    rw [hψE a, hψE b] at h1
    exact eL.injective (Subtype.val_injective h1)
  let π : Fin n → Equiv.Perm (Fin N) := fun i => ψ ((CoxeterMatrix.A n).simple i)
  have hπE : ∀ i : Fin n, E (π i) =
      ((eL ((CoxeterMatrix.A n).simple i) : ↥AL) : MulAut ↥Bs) := fun i => hψE _
  have hπswap : ∀ i : Fin n, (π i).IsSwap := by
    intro i
    refine isSwap_of_ggIsReflection (p := 3) (by norm_num) hBs E hEinj hρE ?_
    rw [hπE i]
    exact heL i
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm n
  have hπnc : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      ¬ Commute (π i) (π ⟨(i : ℕ) + 1, hi⟩) := by
    intro i hi hc
    have hc'' : Commute ((CoxeterMatrix.A n).simple i)
        ((CoxeterMatrix.A n).simple ⟨(i : ℕ) + 1, hi⟩) :=
      hψinj (by rw [map_mul, map_mul]; exact hc)
    exact qTwoDegFrame_simple_not_commute n e0 he0 hi hc''
  have hπcomm : ∀ (i j : Fin n), (i : ℕ) + 2 ≤ j → Commute (π i) (π j) := by
    intro i j hij
    have h1 : Commute ((CoxeterMatrix.A n).simple i) ((CoxeterMatrix.A n).simple j) :=
      qTwoDegFrame_simple_commute n e0 he0 (by omega)
    exact h1.map ψ
  have hπne : ∀ (i j : Fin n), (i : ℕ) + 2 ≤ j → π i ≠ π j := by
    intro i j hij h
    exact qTwoDegFrame_simple_ne n e0 he0 (by omega) (hψinj h)
  let t : ℕ → Equiv.Perm (Fin N) := fun i => if h : i < n then π ⟨i, h⟩ else 1
  have ht_swap : ∀ i < n, (t i).IsSwap := by
    intro i hi
    simp only [t, dif_pos hi]
    exact hπswap ⟨i, hi⟩
  have ht_adj : ∀ i, i + 1 < n → ¬ Commute (t i) (t (i + 1)) := by
    intro i hi
    simp only [t, dif_pos (by omega : i < n), dif_pos hi]
    exact hπnc ⟨i, by omega⟩ hi
  have ht_far : ∀ i j, i + 2 ≤ j → j < n → Commute (t i) (t j) ∧ t i ≠ t j := by
    intro i j hij hj
    simp only [t, dif_pos (by omega : i < n), dif_pos hj]
    exact ⟨hπcomm ⟨i, by omega⟩ ⟨j, hj⟩ hij, hπne ⟨i, by omega⟩ ⟨j, hj⟩ hij⟩
  obtain ⟨p, hpdist, hpt⟩ := qTwoDegFrame_path_labelling hn1 t ht_swap ht_adj ht_far
  refine ⟨p, ?_, ?_⟩
  · intro i hi j hj hij
    exact hpdist i (by omega) j (by omega) hij
  · show AL = Subgroup.map E (Subgroup.closure
      ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio n))
    have hALgen : AL = Subgroup.closure (Set.range fun i : Fin n =>
        ((eL ((CoxeterMatrix.A n).simple i) : ↥AL) : MulAut ↥Bs)) := by
      have hmap : Subgroup.map (AL.subtype.comp eL.toMonoidHom) ⊤ = AL := by
        rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
          show (eL.toMonoidHom).range = ⊤ from MonoidHom.range_eq_top.mpr eL.surjective,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      calc AL = Subgroup.map (AL.subtype.comp eL.toMonoidHom) ⊤ := hmap.symm
        _ = Subgroup.map (AL.subtype.comp eL.toMonoidHom)
              (Subgroup.closure (Set.range (CoxeterMatrix.simple (M := CoxeterMatrix.A n)))) := by
              rw [show Subgroup.closure
                (Set.range (CoxeterMatrix.simple (M := CoxeterMatrix.A n))) =
                ⊤ from (CoxeterMatrix.A n).toCoxeterSystem.subgroup_closure_range_simple]
        _ = Subgroup.closure ((AL.subtype.comp eL.toMonoidHom) ''
              Set.range (CoxeterMatrix.simple (M := CoxeterMatrix.A n))) :=
              MonoidHom.map_closure _ _
        _ = Subgroup.closure (Set.range fun i : Fin n =>
              ((eL ((CoxeterMatrix.A n).simple i) : ↥AL) : MulAut ↥Bs)) := by
              congr 1
              ext x
              constructor
              · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
                exact ⟨i, rfl⟩
              · rintro ⟨i, rfl⟩
                exact ⟨CoxeterMatrix.simple (M := CoxeterMatrix.A n) i, ⟨i, rfl⟩, rfl⟩
    have hle1 : Subgroup.map E (Subgroup.closure
        ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio n)) ≤ AL := by
      rw [MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro x ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      change E (Equiv.swap (p i) (p (i + 1))) ∈ AL
      have hi' : i < n := Set.mem_Iio.mp hi
      have hti : Equiv.swap (p i) (p (i + 1)) = π ⟨i, hi'⟩ := by
        rw [← hpt i hi']
        simp only [t, dif_pos hi']
      rw [hti, hπE ⟨i, hi'⟩]
      exact (eL ((CoxeterMatrix.A n).simple ⟨i, hi'⟩)).2
    have hle2 : AL ≤ Subgroup.map E (Subgroup.closure
        ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio n)) := by
      rw [hALgen]
      rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      change ((eL ((CoxeterMatrix.A n).simple i) : ↥AL) : MulAut ↥Bs) ∈
        Subgroup.map E (Subgroup.closure
          ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio n))
      have hswap_eq : Equiv.swap (p i) (p (i + 1)) = π i := by
        rw [← hpt i i.2]
        simp only [t, dif_pos i.2]
      rw [← hπE i, ← hswap_eq]
      exact Subgroup.mem_map_of_mem E (Subgroup.subset_closure ⟨i, i.2, rfl⟩)
    exact le_antisymm hle2 hle1

theorem qTwoDegFrame_stabilizer {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    {A AL : Subgroup (MulAut ↥Bs)} {N : ℕ} (ρ : Equiv.Perm (Fin N) ≃* ↥A)
    (hρ : ∀ a b : Fin N, a ≠ b → GGIsReflection 3 ((ρ (Equiv.swap a b) : ↥A) : MulAut ↥Bs))
    (hAL : AL ≤ A) {m : ℕ} (hm : 2 ≤ m)
    (hW : GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) AL) (hNm : N = m + 1) :
    ∃ ω : Fin N, AL = Subgroup.map (A.subtype.comp ρ.toMonoidHom)
      (MulAction.stabilizer (Equiv.Perm (Fin N)) ω) := by
  classical
  subst hNm
  obtain ⟨p, hpdist, hpAL⟩ := qTwoDegFrame_path hBs ρ hρ hAL hm hW
  let E : Equiv.Perm (Fin (m + 1)) →* MulAut ↥Bs := A.subtype.comp ρ.toMonoidHom
  have hEinj : Function.Injective E := by
    intro x y hxy
    exact ρ.injective (Subtype.val_injective hxy)
  have hinj : Set.InjOn (fun i : Fin m => p i.val)
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro i _ j _ hij
    exact Fin.ext (hpdist i.val i.2 j.val j.2 hij)
  have hScard : (Finset.univ.image (fun i : Fin m => p i.val)).card = m := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]
  have hpS : ∀ i < m, p i ∈ Finset.univ.image (fun j : Fin m => p j.val) := by
    intro i hi
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  have hSlt : (Finset.univ.image (fun i : Fin m => p i.val)).card <
      (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [hScard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hSlt
  have hfix : ∀ i < m - 1, Equiv.swap (p i) (p (i + 1)) ω = ω := by
    intro i hi
    have hi1 : i + 1 < m := by omega
    have h1 : p i ≠ ω := fun h => hω (h ▸ hpS i (by omega))
    have h2 : p (i + 1) ≠ ω := fun h => hω (h ▸ hpS (i + 1) hi1)
    exact Equiv.swap_apply_of_ne_of_ne h1.symm h2.symm
  have hle : Subgroup.closure ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio (m - 1))
      ≤ MulAction.stabilizer (Equiv.Perm (Fin (m + 1))) ω := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, hi, rfl⟩
    change Equiv.swap (p i) (p (i + 1)) ∈
      MulAction.stabilizer (Equiv.Perm (Fin (m + 1))) ω
    rw [MulAction.mem_stabilizer_iff]
    simpa using hfix i (Set.mem_Iio.mp hi)
  have hcard_cl : Nat.card ↥(Subgroup.closure
      ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio (m - 1))) = m.factorial := by
    rw [← Subgroup.card_map_of_injective (K := Subgroup.closure
      ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio (m - 1))) hEinj, ← hpAL]
    exact qTwoDegFrame_card_weyl (by omega) hW
  have hcard_stab : Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin (m + 1))) ω) =
      m.factorial := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm (Fin (m + 1))) ω)
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_perm,
      Nat.card_fin, Nat.factorial_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) (h1.trans (mul_comm _ _))
  have hclosure_eq : Subgroup.closure
      ((fun i : ℕ => Equiv.swap (p i) (p (i + 1))) '' Set.Iio (m - 1)) =
      MulAction.stabilizer (Equiv.Perm (Fin (m + 1))) ω := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard_cl, hcard_stab]
  exact ⟨ω, by rw [hpAL, hclosure_eq]⟩

end CFSG.StandardType.QTwo

end
