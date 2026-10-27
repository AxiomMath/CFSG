module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHeart

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

section Act

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

theorem GGE6ThreeData.normalizer_clause (h : GGE6ThreeData Z A Φ T w) (hodd : Odd (Nat.card Z))
    {n : L'} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ v ∈ Subgroup.closure (Set.range w), ∀ a ∈ A, a (n * v⁻¹) = n * v⁻¹ := by
  obtain ⟨_, hnorm⟩ := h.odd hodd
  obtain ⟨v, hv, htv⟩ := hnorm n hn
  exact ⟨v, hv, fun a ha => h.fixed a ha (n * v⁻¹) htv⟩

theorem GGE6ThreeData.mem_closure_involutions (h : GGE6ThreeData Z A Φ T w)
    (hodd : Odd (Nat.card Z)) {n : L'} (hn : n ∈ Subgroup.closure (Set.range w)) :
    n ∈ Subgroup.closure
      {m | m ∈ (Subgroup.closure (Set.range w) : Set L') ∧ m * m = 1} := by
  obtain ⟨hwi, _⟩ := h.odd hodd
  have hle : Subgroup.closure (Set.range w) ≤
      Subgroup.closure {m | m ∈ (Subgroup.closure (Set.range w) : Set L') ∧ m * m = 1} := by
    rw [Subgroup.closure_le]
    rintro m ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨i, rfl⟩, hwi i⟩
  exact hle hn

theorem GGE6ThreeData.exists_power_map (h : GGE6ThreeData Z A Φ T w)
    (f : MulAut L' → MulAut L')
    (hf1 : ∀ a ∈ heartOf Φ, f a ∈ heartOf Φ)
    (hf2 : ∀ a ∈ heartOf Φ, ∀ b ∈ heartOf Φ, f (a * b) = f a * f b)
    (hf3 : ∀ n ∈ (Subgroup.closure (Set.range w) : Set L'), ∀ a ∈ heartOf Φ,
      f (MulAut.conj n * a * (MulAut.conj n)⁻¹) = MulAut.conj n * f a * (MulAut.conj n)⁻¹) :
    ∃ c : ℕ, ∀ a ∈ heartOf Φ, f a = a ^ c := by
  classical
  let ax : NoOffRest.hypE6 → A := fun x => Classical.choose (h.exists_eq_of_mem_hypE6 x.2)
  have hax : ∀ x : NoOffRest.hypE6,
      Φ (ax x) = Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3) :=
    fun x => Classical.choose_spec (h.exists_eq_of_mem_hypE6 x.2)
  have hax_heart : ∀ x : NoOffRest.hypE6, (ax x : MulAut L') ∈ heartOf Φ := by
    intro x
    rw [mem_heartOf_iff]
    refine ⟨(ax x).2, ?_⟩
    have h1 : (⟨(ax x : MulAut L'), (ax x).2⟩ : A) = ax x := rfl
    rw [h1, hax x]
    change (x : Fin Tag.E6.rank → ZMod 3) ∈ NoOffRest.hypE6
    exact x.2
  have hf_heart : ∀ x : NoOffRest.hypE6, f (ax x : MulAut L') ∈ heartOf Φ :=
    fun x => hf1 _ (hax_heart x)
  let g : NoOffRest.hypE6 → NoOffRest.hypE6 := fun x =>
    let hx := mem_heartOf_iff.mp (hf_heart x)
    ⟨Multiplicative.toAdd (Φ ⟨f (ax x : MulAut L'), hx.1⟩), hx.2⟩
  have g_val : ∀ x : NoOffRest.hypE6,
      ((g x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
        Multiplicative.toAdd (Φ ⟨f (ax x : MulAut L'),
          (mem_heartOf_iff.mp (hf_heart x)).1⟩) := fun x => rfl
  have hg_add : ∀ x y : NoOffRest.hypE6, g (x + y) = g x + g y := by
    intro x y
    have hax_add : ax (x + y) = ax x * ax y := by
      apply h.injective
      rw [map_mul, hax x, hax y, hax (x + y)]
      exact ofAdd_add (x : Fin Tag.E6.rank → ZMod 3)
        (y : Fin Tag.E6.rank → ZMod 3)
    have hf_add : f ((ax (x + y) : A) : MulAut L') =
        f ((ax x : A) : MulAut L') * f ((ax y : A) : MulAut L') := by
      have hcongr : ((ax (x + y) : A) : MulAut L') =
          ((ax x : A) : MulAut L') * ((ax y : A) : MulAut L') := by
        rw [hax_add]; rfl
      rw [hcongr, hf2 (ax x : MulAut L') (hax_heart x) (ax y : MulAut L') (hax_heart y)]
    apply Subtype.ext
    show ((g (x + y) : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
      ((g x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) +
        ((g y : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3)
    rw [g_val (x + y), g_val x, g_val y]
    have hA : (⟨f ((ax (x + y) : A) : MulAut L'),
          (mem_heartOf_iff.mp (hf_heart (x + y))).1⟩ : A)
        = ⟨f ((ax x : A) : MulAut L'), (mem_heartOf_iff.mp (hf_heart x)).1⟩
          * ⟨f ((ax y : A) : MulAut L'), (mem_heartOf_iff.mp (hf_heart y)).1⟩ := by
      apply Subtype.ext
      exact hf_add
    rw [hA, map_mul, toAdd_mul]
    rfl
  let gA : NoOffRest.hypE6 →+ NoOffRest.hypE6 := AddMonoidHom.mk' g hg_add
  have gA_val : ∀ x : NoOffRest.hypE6,
      ((gA x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
        ((g x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) := fun x => rfl
  have hc : ∀ (i : Fin Tag.E6.rank) (x y : NoOffRest.hypE6),
      (y : Fin Tag.E6.rank → ZMod 3) = adRefl .E6 3 i (x : Fin Tag.E6.rank → ZMod 3) →
        ((gA y : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
          adRefl .E6 3 i ((gA x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) := by
    intro i x y hy
    rw [gA_val y, gA_val x, g_val y, g_val x]
    obtain ⟨b, hbconj, hbphi⟩ := h.act i (ax x)
    have hphi_x : Multiplicative.toAdd (Φ (ax x)) = (x : Fin Tag.E6.rank → ZMod 3) := by
      rw [hax x]; rfl
    have hb_toAdd : Multiplicative.toAdd (Φ b) = (y : Fin Tag.E6.rank → ZMod 3) := by
      rw [hbphi, hy]
      exact congrArg (adRefl .E6 3 i) hphi_x
    have hb_phi : Φ b = Multiplicative.ofAdd (y : Fin Tag.E6.rank → ZMod 3) :=
      (ofAdd_toAdd (Φ b)).symm.trans (congrArg Multiplicative.ofAdd hb_toAdd)
    have hb_eq : b = ax y := by
      apply h.injective
      rw [hb_phi, hax y]
    have hb_val : (b : MulAut L') = (ax y : MulAut L') := congrArg Subtype.val hb_eq
    have hwi_mem : w i ∈ (Subgroup.closure (Set.range w) : Set L') :=
      Subgroup.subset_closure ⟨i, rfl⟩
    have hf3w := hf3 (w i) hwi_mem (ax x : MulAut L') (hax_heart x)
    have hf_y : f (ax y : MulAut L') =
        MulAut.conj (w i) * f (ax x : MulAut L') * (MulAut.conj (w i))⁻¹ := by
      have h' := hf3w
      rw [hbconj, hb_val] at h'
      exact h'
    obtain ⟨d, hdconj, hdphi⟩ :=
      h.act i ⟨f (ax x : MulAut L'), (mem_heartOf_iff.mp (hf_heart x)).1⟩
    have hd_val : (d : MulAut L') = f (ax y : MulAut L') := by
      rw [← hdconj]
      exact hf_y.symm
    have hd_eq : d = ⟨f (ax y : MulAut L'), (mem_heartOf_iff.mp (hf_heart y)).1⟩ := by
      apply Subtype.ext
      exact hd_val
    rw [← hd_eq]
    exact hdphi
  obtain ⟨c, hc_smul⟩ := exists_smul_of_commute_hypE6 gA hc
  refine ⟨c.val, ?_⟩
  intro a ha
  have ha_mem : a ∈ A := (mem_heartOf_iff.mp ha).1
  have ha_hyp : Multiplicative.toAdd (Φ ⟨a, ha_mem⟩) ∈ NoOffRest.hypE6 :=
    (mem_heartOf_iff.mp ha).2
  let x : NoOffRest.hypE6 := ⟨Multiplicative.toAdd (Φ ⟨a, ha_mem⟩), ha_hyp⟩
  have hax_x : (ax x : MulAut L') = a := by
    have hphi_a : Φ (ax x) = Φ ⟨a, ha_mem⟩ := by
      rw [hax x]; rfl
    exact congrArg Subtype.val (h.injective hphi_a)
  rw [← hax_x]
  have h_toAdd : Multiplicative.toAdd (Φ ⟨f (ax x : MulAut L'),
      (mem_heartOf_iff.mp (hf_heart x)).1⟩) = c • (x : Fin Tag.E6.rank → ZMod 3) := by
    have h1 : Multiplicative.toAdd (Φ ⟨f (ax x : MulAut L'),
        (mem_heartOf_iff.mp (hf_heart x)).1⟩) =
        ((g x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) := (g_val x).symm
    have h2 : ((gA x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
        c • (x : Fin Tag.E6.rank → ZMod 3) := hc_smul x
    rw [gA_val x] at h2
    exact h1.trans h2
  have h_pow : Φ ⟨f (ax x : MulAut L'), (mem_heartOf_iff.mp (hf_heart x)).1⟩ =
      (Φ (ax x)) ^ c.val := by
    have step1 : Φ ⟨f (ax x : MulAut L'), (mem_heartOf_iff.mp (hf_heart x)).1⟩ =
        Multiplicative.ofAdd (Multiplicative.toAdd (Φ ⟨f (ax x : MulAut L'),
          (mem_heartOf_iff.mp (hf_heart x)).1⟩)) := (ofAdd_toAdd _).symm
    have step2 : Multiplicative.ofAdd (Multiplicative.toAdd (Φ ⟨f (ax x : MulAut L'),
          (mem_heartOf_iff.mp (hf_heart x)).1⟩)) =
        Multiplicative.ofAdd (c • (x : Fin Tag.E6.rank → ZMod 3)) :=
      congrArg Multiplicative.ofAdd h_toAdd
    have hcv : c • (x : Fin Tag.E6.rank → ZMod 3) =
        c.val • (x : Fin Tag.E6.rank → ZMod 3) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      exact Nat.cast_smul_eq_nsmul (ZMod 3) c.val _
    have step3 : Multiplicative.ofAdd (c • (x : Fin Tag.E6.rank → ZMod 3)) =
        Multiplicative.ofAdd (c.val • (x : Fin Tag.E6.rank → ZMod 3)) :=
      congrArg Multiplicative.ofAdd hcv
    have step4 : Multiplicative.ofAdd (c.val • (x : Fin Tag.E6.rank → ZMod 3)) =
        (Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3)) ^ c.val :=
      ofAdd_nsmul c.val _
    have step5 : (Multiplicative.ofAdd (x : Fin Tag.E6.rank → ZMod 3)) ^ c.val =
        (Φ (ax x)) ^ c.val :=
      (congrArg (fun t => t ^ c.val) (hax x)).symm
    exact step1.trans (step2.trans (step3.trans (step4.trans step5)))
  have h_pow' : Φ ⟨f (ax x : MulAut L'), (mem_heartOf_iff.mp (hf_heart x)).1⟩ =
      Φ ((ax x) ^ c.val) := by rw [h_pow, map_pow]
  have hfin : f (ax x : MulAut L') = ((ax x : A) : MulAut L') ^ c.val := by
    have hval := congrArg Subtype.val (h.injective h_pow')
    simpa using hval
  exact hfin

end Act

end CFSG.StandardType
