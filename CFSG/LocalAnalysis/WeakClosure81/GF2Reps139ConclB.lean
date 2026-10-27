module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139ConclBAux2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139ConclBCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.RankThree.PartOne.Q1327T.Perm3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private noncomputable def w1369_kAutEquiv {M : Subgroup W} {K : Subgroup (MulAut W)}
    (hKM : StableUnder K M) (hfaith : ∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1)
    (hsurj : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W)) :
    ↥K ≃* MulAut ↥M := by
  let f : ↥K →* MulAut ↥M :=
    { toFun := fun k =>
        { toFun := fun m => ⟨(k : MulAut W) (m : W), hKM k k.2 m m.2⟩
          invFun := fun m =>
            ⟨(k : MulAut W)⁻¹ (m : W), hKM (k : MulAut W)⁻¹ (K.inv_mem k.2) m m.2⟩
          left_inv := fun m => Subtype.ext (by simp)
          right_inv := fun m => Subtype.ext (by simp)
          map_mul' := fun m m' =>
            Subtype.ext (map_mul (k : MulAut W) (m : W) (m' : W)) }
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro k l
        ext m
        simp [MulAut.mul_apply] }
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    refine Subtype.ext (hfaith (k : MulAut W) k.2 ?_)
    intro m hm
    have h1 := congrArg (fun g : MulAut ↥M => g ⟨m, hm⟩) hk
    exact congrArg Subtype.val h1
  have hfsurj : Function.Surjective f := by
    intro g
    obtain ⟨k, hk, hkg⟩ := hsurj g
    refine ⟨⟨k, hk⟩, ?_⟩
    ext m
    exact (hkg m).symm
  exact MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩

private lemma w1369_kAutEquiv_apply {M : Subgroup W} {K : Subgroup (MulAut W)}
    (hKM : StableUnder K M) (hfaith : ∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1)
    (hsurj : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (k : ↥K) (m : ↥M) :
    ((w1369_kAutEquiv hKM hfaith hsurj k m : ↥M) : W) = (k : MulAut W) (m : W) := rfl

private theorem w1369_realizesVia_of_equiv {V : Type*} [CommGroup V] {Γ : Type} [Group Γ]
    {A : Type} [CommGroup A]
    (act : Γ → A → A) (hact1 : ∀ γ, act γ 1 = 1) {H : Subgroup (MulAut V)} {U : Subgroup V}
    (π : Γ →* ↥H) (hπ : Function.Surjective π) (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U)
    (e : ↥U ≃* A)
    (he : ∀ (γ : Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (e u)) :
    (FFModel.mk Γ A act ⊤ ⊥).RealizesVia H U ⊥ π := by
  refine ⟨hπ, bot_le, bot_le, hHU, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    change m ∈ (⊥ : Subgroup A) at hm
    change act γ m ∈ (⊥ : Subgroup A)
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · let β : ↥U →* ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp e.toMonoidHom)
    have hβ : ∀ u : ↥U,
        β u = ((Subgroup.topEquiv.symm (e u) : ↥(⊤ : Subgroup A)) :
          ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤) := fun _ => rfl
    have hinj : ∀ a b : ↥(⊤ : Subgroup A), ((a : ↥(⊤ : Subgroup A) ⧸
        (⊥ : Subgroup A).subgroupOf ⊤) = b) → a = b := by
      intro a b h
      rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h
      exact (inv_mul_eq_one.mp h)
    refine ⟨β, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨⟨m, -⟩, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨e.symm m, ?_⟩
      rw [hβ]
      congr 1
      exact Subtype.ext (by simp)
    · intro u
      rw [hβ, QuotientGroup.eq_one_iff, Subgroup.bot_subgroupOf, Subgroup.mem_bot,
        Subgroup.mem_bot]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        simpa using h'
      · intro h
        have hu1 : u = 1 := Subtype.ext h
        apply Subtype.ext
        simp [hu1]
    · intro γ u m hu hm hum
      rw [hβ] at hum ⊢
      have hm' := hinj _ _ hum
      congr 1
      apply Subtype.ext
      change e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (m : A)
      rw [he, ← hm']
      rfl

private theorem w1369_realizesVia_transport {W V : Type*} [CommGroup W] [CommGroup V]
    (ι : W →* V) (hι : Function.Injective ι) {G₂ : Subgroup (MulAut V)}
    {H : Subgroup (MulAut W)} (e : ↥G₂ ≃* ↥H)
    (he : ∀ (g : ↥G₂) (w : W), ι ((e g : MulAut W) w) = (g : MulAut V) (ι w))
    {D : FFModel} {U Z : Subgroup W} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    D.RealizesVia G₂ (U.map ι) (Z.map ι) (e.symm.toMonoidHom.comp π) := by
  obtain ⟨hsurj, hZU, hkersec, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hact : ∀ (g : ↥G₂) (w : W), (g : MulAut V) (ι w) = ι ((e g : MulAut W) w) :=
    fun g w => (he g w).symm
  refine ⟨?_, Subgroup.map_mono hZU, hkersec, ?_, ?_, hsec, hker, ?_⟩
  · exact e.symm.surjective.comp hsurj
  · rintro g _ ⟨u, hu, rfl⟩
    rw [hact]
    exact ⟨_, hHU (e g) u hu, rfl⟩
  · rintro g _ ⟨z, hz, rfl⟩
    rw [hact]
    exact ⟨_, hHZ (e g) z hz, rfl⟩
  · let iso : ↥(U.map ι) ≃* ↥U := (Subgroup.equivMapOfInjective U ι hι).symm
    have hiso : ∀ (u : ↥(U.map ι)), ι ((iso u : ↥U) : W) = (u : V) := by
      intro u
      have := (Subgroup.equivMapOfInjective U ι hι).apply_symm_apply u
      exact congrArg Subtype.val this
    refine ⟨β.comp iso.toMonoidHom, hβs.comp iso.surjective, ?_, ?_⟩
    · intro u
      show β (iso u) = 1 ↔ _
      rw [hβk, ← hiso u]
      exact (Subgroup.mem_map_iff_mem hι).symm
    · intro γ u m hu hm hbu
      set g : ↥G₂ := e.symm (π γ) with hg
      have hge : e g = π γ := by rw [hg]; exact e.apply_symm_apply _
      set u₀ : ↥U := iso u with hu₀
      have hU' : ((π γ : ↥H) : MulAut W) (u₀ : W) ∈ U := hHU (π γ) u₀ u₀.2
      have h1 : (g : MulAut V) (u : V) = ι (((π γ : ↥H) : MulAut W) (u₀ : W)) := by
        rw [← hiso u, hact, hge]
      have h2 : iso ⟨(g : MulAut V) (u : V), hu⟩ =
          ⟨((π γ : ↥H) : MulAut W) (u₀ : W), hU'⟩ := by
        apply Subtype.ext
        apply hι
        exact (hiso _).trans h1
      have h3 := hβe γ u₀ m hU' hm hbu
      show β (iso ⟨(g : MulAut V) (u : V), hu⟩) = _
      rw [h2]
      exact h3

theorem Std139.shapeTensor_isSLn (hw2 : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} (h : ShapeTensor K X n) :
    IsSLn ↥K n 1 := by
  obtain ⟨M, x, hxX, hx1, hKM, hrk, hdis, hsup, hfaith, hsurj⟩ := h
  have hcardM : Nat.card ↥M = 2 ^ n := by
    rw [card_eq_two_pow hw2 M, hrk]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥M)
    (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by simpa using hw2 (a : W))) hcardM
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp [Nat.card_zmod], ?_⟩
  let f : ↥K →* MulAut ↥M :=
    { toFun := fun k =>
        { toFun := fun m => ⟨(k : MulAut W) (m : W), hKM k k.2 m m.2⟩
          invFun := fun m =>
            ⟨(k : MulAut W)⁻¹ (m : W), hKM (k : MulAut W)⁻¹ (K.inv_mem k.2) m m.2⟩
          left_inv := fun m => Subtype.ext (by simp)
          right_inv := fun m => Subtype.ext (by simp)
          map_mul' := fun m m' =>
            Subtype.ext (map_mul (k : MulAut W) (m : W) (m' : W)) }
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro k l
        ext m
        simp [MulAut.mul_apply] }
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    refine Subtype.ext (hfaith (k : MulAut W) k.2 ?_)
    intro m hm
    have h1 := congrArg (fun g : MulAut ↥M => g ⟨m, hm⟩) hk
    exact congrArg Subtype.val h1
  have hfsurj : Function.Surjective f := by
    intro g
    obtain ⟨k, hk, hkg⟩ := hsurj g
    refine ⟨⟨k, hk⟩, ?_⟩
    ext m
    exact (hkg m).symm
  let φ : ↥K ≃* GL (Fin n) (ZMod 2) :=
    (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).trans (CFSG.SectionRank.Ccomm.elemAutEquivGL e)
  have htop : CFSG.Open.StatedSL n (ZMod 2) = ⊤ :=
    s16c1610_statedSL_eq_top_of_card_two (by rw [Nat.card_zmod]) n
  exact ⟨φ.trans (MulEquiv.ofBijective (Subgroup.subtype (CFSG.Open.StatedSL n (ZMod 2)))
    ⟨Subtype.val_injective, fun g => ⟨⟨g, by rw [htop]; exact Subgroup.mem_top g⟩, rfl⟩⟩).symm⟩

theorem Std139.shapeTensor_sumOfNat (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (h : ShapeTensor K X n) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) K ⊤ ⊥ 2 := by
  obtain ⟨M, x, hxX, hx1, hKM, hrk, hdis, hsup, hfaith, hsurj⟩ := h
  have hcardM : Nat.card ↥M = 2 ^ n := by
    rw [card_eq_two_pow hw2 M, hrk]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥M)
    (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by simpa using hw2 (a : W))) hcardM
  let ρ : ↥K ≃* MulAut ↥M := w1369_kAutEquiv hKM hfaith hsurj
  have htop : StatedSL n (ZMod 2) = ⊤ :=
    s16c1610_statedSL_eq_top_of_card_two (by rw [Nat.card_zmod]) n
  let π : ↥(StatedSL n (ZMod 2)) →* ↥K :=
    ρ.symm.toMonoidHom.comp
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm.toMonoidHom.comp
        (StatedSL n (ZMod 2)).subtype)
  have hπ : Function.Surjective π := by
    intro k
    refine ⟨⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e) (ρ k), ?_⟩, ?_⟩
    · rw [htop]
      exact Subgroup.mem_top _
    · show ρ.symm ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm
        ((CFSG.SectionRank.Ccomm.elemAutEquivGL e) (ρ k))) = k
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  have hhe : ∀ (γ : ↥(StatedSL n (ZMod 2))) (m : ↥M)
      (hm : ((π γ : ↥K) : MulAut W) (m : W) ∈ M),
      e ⟨((π γ : ↥K) : MulAut W) (m : W), hm⟩ =
        natAct (StatedSL n (ZMod 2)) γ (e m) := by
    intro γ m hm
    have hρ : ρ (π γ) = (CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm
        (γ : GL (Fin n) (ZMod 2)) := by
      change ρ (ρ.symm ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm
        (γ : GL (Fin n) (ZMod 2)))) = _
      rw [MulEquiv.apply_symm_apply]
    have hval : (⟨((π γ : ↥K) : MulAut W) (m : W), hm⟩ : ↥M) = ρ (π γ) m :=
      Subtype.ext (w1369_kAutEquiv_apply hKM hfaith hsurj (π γ) m).symm
    rw [hval, hρ]
    have hmv := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e
      ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm (γ : GL (Fin n) (ZMod 2))) m
    rw [MulEquiv.apply_symm_apply] at hmv
    change e (((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm (γ : GL (Fin n) (ZMod 2))) m) =
      Multiplicative.ofAdd (((γ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (e m)))
    rw [hmv]
    rfl
  have hrealM : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia K M ⊥ π := by
    refine w1369_realizesVia_of_equiv (natAct (StatedSL n (ZMod 2))) ?_ π hπ
      (fun h u hu => hKM h h.2 u hu) e hhe
    intro γ
    show Multiplicative.ofAdd (((γ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (Multiplicative.toAdd (1 : Multiplicative (Fin n → ZMod 2)))) = 1
    simp
  have hnatM : BinaryNaturalSL K M ⊥ n 1 :=
    ⟨ZMod 2, inferInstance, inferInstance, by simp [Nat.card_zmod], π, hrealM⟩
  have hxcomm : ∀ k ∈ K, k * x = x * k :=
    fun k hk => S.component_commutes_X hK.comp k hk x hxX
  have hrealxM : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia K
      (M.map x.toMonoidHom) ⊥ ((MulEquiv.refl ↥K).symm.toMonoidHom.comp π) := by
    have hxh : ∀ (g : ↥K) (w : W),
        x.toMonoidHom ((MulEquiv.refl ↥K g : MulAut W) w) =
          (g : MulAut W) (x.toMonoidHom w) := by
      intro g w
      change x ((g : MulAut W) w) = (g : MulAut W) (x w)
      have hk : (g : MulAut W) * x = x * (g : MulAut W) := hxcomm g g.2
      change (x * (g : MulAut W)) w = ((g : MulAut W) * x) w
      rw [hk]
    have htr := w1369_realizesVia_transport (W := W) (V := W) x.toMonoidHom x.injective
      (MulEquiv.refl ↥K) hxh hrealM
    rw [Subgroup.map_bot] at htr
    exact htr
  have hnatxM : BinaryNaturalSL K (M.map x.toMonoidHom) ⊥ n 1 :=
    ⟨ZMod 2, inferInstance, inferInstance, by simp [Nat.card_zmod],
      (MulEquiv.refl ↥K).symm.toMonoidHom.comp π, hrealxM⟩
  let I : Fin 2 → Subgroup W := ![M, M.map x.toMonoidHom]
  have hI0 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
    apply le_antisymm
    · refine iSup_le ?_
      intro j
      refine iSup_le ?_
      intro hj
      fin_cases j
      · exact absurd rfl hj
      · exact le_rfl
    · exact le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl)
  have hI1 : (⨆ (j : Fin 2) (_ : j ≠ 1), I j) = I 0 := by
    apply le_antisymm
    · refine iSup_le ?_
      intro j
      refine iSup_le ?_
      intro hj
      fin_cases j
      · exact le_rfl
      · exact absurd rfl hj
    · exact le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl)
  have hsupI : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
    apply le_antisymm
    · refine iSup_le ?_
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup I 0) (le_iSup I 1)
  refine ⟨I, fun i => bot_le, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change I 0 ⊓ (⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ (0 : Fin 2)), I j) ≤ ⊥
      rw [bot_sup_eq, hI0]
      simp only [I, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hdis]
    · change I 1 ⊓ (⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ (1 : Fin 2)), I j) ≤ ⊥
      rw [bot_sup_eq, hI1]
      simp only [I, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [inf_comm, hdis]
  · rw [bot_sup_eq, hsupI]
    simp only [I, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hsup]
  · intro i
    fin_cases i
    · simpa [I, Matrix.cons_val_zero] using hnatM
    · simpa [I, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hnatxM

theorem Std139.shapeTensor_normalizer (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (h : ShapeTensor K X n) :
    ∃ Kb : Subgroup (MulAut W), IsSym ↥Kb 3 ∧ IsInternalDirect Kb K G := by
  letI : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (fun a => by
      rw [two_nsmul]
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zero, ← pow_two]
      exact hw2 _)
  obtain ⟨M, x, hxX, hx1, hKM, hrk, hdis, hsup, hfaith, hsurj⟩ := h
  obtain ⟨xg, hXgen, hxg3, hxg1, hfixX, hsxg⟩ := Std139.exists_gen hw2 S
  have hKG : K ≤ G := hK.comp.1
  have hKX : ∀ k ∈ K, ∀ y ∈ X, k * y = y * k := fun k hk y hy =>
    S.component_commutes_X hK.comp k hk y hy
  have hXcent : X ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact hKX k hk y hy
  have hcentcard : Nat.card ↥(Subgroup.centralizer (K : Set (MulAut W))) ≤ 6 :=
    Std139.shapeTensor_cent_card hw2 hKM hfaith hsurj hrk (by omega) x hdis hsup
      (fun k hk => hKX k hk x hxX)
  let Kb : Subgroup (MulAut W) := G ⊓ Subgroup.centralizer (K : Set (MulAut W))
  have hKbG : Kb ≤ G := inf_le_left
  have hKbCent : Kb ≤ Subgroup.centralizer (K : Set (MulAut W)) := inf_le_right
  have hinfKcent : K ⊓ Subgroup.centralizer (K : Set (MulAut W)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    obtain ⟨hkK, hkCent⟩ := hk
    exact w1369_K_inf_centralizer hw2 hKM hfaith hsurj hrk (by omega) hkK
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hkCent l hl).symm)
  have hsupKbK : Kb ⊔ K = G := by
    apply le_antisymm
    · exact sup_le hKbG hKG
    · intro g hg
      obtain ⟨k0, hk0K, hck0⟩ :=
        w1369_exists_centralizing hw2 hKM hfaith hsurj x hdis hsup
          (fun k hk => hKX k hk x hxX) hK.normal hg
      have hcG : g * k0⁻¹ ∈ G := G.mul_mem hg (G.inv_mem (hKG hk0K))
      have hcCent : g * k0⁻¹ ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (hck0 k hk).symm
      have hcKb : g * k0⁻¹ ∈ Kb := ⟨hcG, hcCent⟩
      have hg_eq : (g * k0⁻¹) * k0 = g := by group
      rw [← hg_eq]
      exact Subgroup.mul_mem_sup hcKb hk0K
  have hinfKbK : Kb ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    obtain ⟨hkKb, hkK⟩ := hk
    exact w1369_K_inf_centralizer hw2 hKM hfaith hsurj hrk (by omega) hkK
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hkKb.2 l hl).symm)
  obtain ⟨k0, hk0K, hck0⟩ :=
    w1369_exists_centralizing hw2 hKM hfaith hsurj x hdis hsup
      (fun k hk => hKX k hk x hxX) hK.normal S.sG
  let c : MulAut W := s * k0⁻¹
  have hcCent : c ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hck0 k hk).symm
  have hcG : c ∈ G := G.mul_mem S.sG (G.inv_mem (hKG hk0K))
  have hcKb : c ∈ Kb := ⟨hcG, hcCent⟩
  have hxgX : xg ∈ X := hXgen ▸ Subgroup.mem_zpowers xg
  have hxgKb : xg ∈ Kb := ⟨S.XG hxgX, hXcent hxgX⟩
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [S.s2] at h
    simpa [pow_two] using h
  have hk0s : k0 * s = s * k0 := by
    have h := hck0 k0 hk0K
    have h' : s = k0 * (s * k0⁻¹) := by
      calc s = (s * k0⁻¹) * k0 := by group
        _ = k0 * (s * k0⁻¹) := h
    have h'' : s = k0 * s * k0⁻¹ := by
      rw [← mul_assoc] at h'
      exact h'
    have hs : s * k0 = k0 * s := by
      conv_lhs => rw [h'']
      group
    exact hs.symm
  have hc2 : c * c = 1 := by
    have hmem : c * c ∈ K ⊓ Subgroup.centralizer (K : Set (MulAut W)) := by
      constructor
      · have hk0sinv : k0⁻¹ * s = s * k0⁻¹ := by
          have h := hk0s
          calc k0⁻¹ * s = k0⁻¹ * (s * k0) * k0⁻¹ := by group
            _ = k0⁻¹ * (k0 * s) * k0⁻¹ := by rw [← h]
            _ = s * k0⁻¹ := by group
        have hcc : c * c = (k0 * k0)⁻¹ := by
          dsimp [c]
          calc (s * k0⁻¹) * (s * k0⁻¹)
              = s * (k0⁻¹ * s) * k0⁻¹ := by group
            _ = s * (s * k0⁻¹) * k0⁻¹ := by rw [hk0sinv]
            _ = (s * s) * (k0⁻¹ * k0⁻¹) := by group
            _ = (k0 * k0)⁻¹ := by rw [hs2]; group
        rw [hcc]
        exact K.inv_mem (K.mul_mem hk0K hk0K)
      · exact Subgroup.mul_mem _ hcCent hcCent
    rw [hinfKcent] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcxg : c * xg * c⁻¹ = xg⁻¹ := by
    have hk0x : k0 * xg = xg * k0 := hKX k0 hk0K xg hxgX
    have hk0inv : k0⁻¹ * xg * k0 = xg := by
      calc k0⁻¹ * xg * k0 = k0⁻¹ * (xg * k0) := by group
        _ = k0⁻¹ * (k0 * xg) := by rw [← hk0x]
        _ = xg := by group
    dsimp [c]
    calc (s * k0⁻¹) * xg * (s * k0⁻¹)⁻¹
        = s * (k0⁻¹ * xg * k0) * s⁻¹ := by group
      _ = s * xg * s⁻¹ := by rw [hk0inv]
      _ = xg⁻¹ := hsxg
  have hxgne : xg ≠ xg⁻¹ := by
    intro h
    have h2 : xg * xg = 1 := by
      calc xg * xg = xg * xg⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel xg
    have h1 : xg = 1 := by
      calc xg = xg ^ 3 * (xg * xg)⁻¹ := by group
        _ = 1 := by rw [hxg3, h2]; simp
    exact hxg1 h1
  have hc1 : c ≠ 1 := by
    intro h
    apply hxgne
    rw [← hcxg, h]
    simp
  have hKb_card_le : Nat.card ↥Kb ≤ 6 :=
    le_trans (Nat.card_le_card_of_injective (Subgroup.inclusion hKbCent)
      (Subgroup.inclusion_injective hKbCent)) hcentcard
  have h3 : 3 ∣ Nat.card ↥Kb := by
    have hXKb : X ≤ Kb := fun y hy => ⟨S.XG hy, hXcent hy⟩
    have h := Subgroup.card_subgroup_dvd_card (X.subgroupOf Kb)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXKb).toEquiv, S.Xcard] at h
  have h2 : 2 ∣ Nat.card ↥Kb := by
    have hc2' : (⟨c, hcKb⟩ : ↥Kb) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two]
      exact hc2
    have h := orderOf_dvd_natCard (⟨c, hcKb⟩ : ↥Kb)
    have hord : orderOf (⟨c, hcKb⟩ : ↥Kb) = 2 :=
      orderOf_eq_prime hc2' (by intro hh; exact hc1 (congrArg Subtype.val hh))
    rwa [hord] at h
  have h6 : 6 ∣ Nat.card ↥Kb := by
    have hcop : Nat.Coprime 2 3 := by decide
    have h := hcop.mul_dvd_of_dvd_of_dvd h2 h3
    simpa using h
  have hKb_card : Nat.card ↥Kb = 6 :=
    le_antisymm hKb_card_le (Nat.le_of_dvd Nat.card_pos h6)
  have hsym : IsSym ↥Kb 3 :=
    CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three
      (⟨xg, hxgKb⟩ : ↥Kb) (⟨c, hcKb⟩ : ↥Kb)
      (by simpa [Subgroup.coe_pow] using hxg3)
      (by intro hh; exact hxg1 (congrArg Subtype.val hh))
      (by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hc2]
        rfl)
      (by intro hh; exact hc1 (congrArg Subtype.val hh))
      (by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hcxg])
      hKb_card
  have hdir : IsInternalDirect Kb K G :=
    ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKbCent, hinfKbK, hsupKbK⟩
  exact ⟨Kb, hsym, hdir⟩

theorem Std139.concl_of_shapeTensor (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (h : ShapeTensor K X n) :
    Concl139 W G X n := by
  obtain ⟨Kb, hKb, hdir⟩ := Std139.shapeTensor_normalizer hw2 S hn hK h
  exact Or.inl (Or.inr (Or.inl (s16c1610_isTensorS3L2_of_sum_natural hn hKb
    (s16k_isLn_of_isSLn hn (Std139.shapeTensor_isSLn hw2 h)) hdir
    (Std139.shapeTensor_sumOfNat hw2 S hK h))))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
