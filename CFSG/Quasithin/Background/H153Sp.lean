module

public import CFSG.Quasithin.Background.H153SpChk
public import CFSG.Quasithin.Background.H153Std
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

open scoped Matrix Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H156
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans

@[expose] def iotaEquiv : Wn 4 ≃* Multiplicative (I4 → ZMod 2) where
  toFun v := Multiplicative.ofAdd fun i => Multiplicative.toAdd v (eI i)
  invFun w := Multiplicative.ofAdd fun k => Multiplicative.toAdd w (eI.symm k)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext k
    simp
  right_inv w := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    simp

@[expose] noncomputable def beta4 : W11 →* Multiplicative (I4 → ZMod 2) :=
  iotaEquiv.toMonoidHom.comp (maskHom 11 4 c4)

theorem beta4_toW (m : ℕ) : beta4 (toW 11 m) = iotaEquiv (toW 4 (actM c4 m)) := by
  show iotaEquiv (maskHom 11 4 c4 (toW 11 m)) = _
  rw [maskHom_toW c4_len]

theorem c4_lt : ∀ c ∈ c4, c < 2 ^ 4 := by decide

theorem actM_c4_lt (m : ℕ) : actM c4 m < 16 := actM_lt c4_lt m

theorem beta4_surj : Function.Surjective beta4 := by
  intro w
  obtain ⟨v, rfl⟩ := iotaEquiv.surjective w
  obtain ⟨y, hy, rfl⟩ := toW_surj 4 v
  obtain ⟨m, hm, hmy⟩ := c4_surj y hy
  exact ⟨toW 11 m, by rw [beta4_toW, hmy]⟩

theorem toW_mem_maskSub_iff {n : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < 2 ^ n) {m : ℕ}
    (hm : m < 2 ^ n) : toW n m ∈ maskSub n l ↔ m ∈ combos l := by
  constructor
  · rintro ⟨m', hm', e⟩
    have : m' = m := toW_inj (combos_lt hl m' hm') hm e
    rwa [← this]
  · exact toW_mem_maskSub

theorem beta4_ker (x : W11) : beta4 x = 1 ↔ x ∈ W0 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [beta4_toW, toW_mem_maskSub_iff w0_lt hm, ← c4_ker m hm]
  constructor
  · intro h
    have h1 : toW 4 (actM c4 m) = 1 := iotaEquiv.injective (h.trans (map_one iotaEquiv).symm)
    exact toW_inj (actM_c4_lt m) (by norm_num) (h1.trans (toW_zero 4).symm)
  · intro h
    rw [h, toW_zero, map_one]

theorem natHomI'_injective : Function.Injective (natHomI' I4 (ZMod 2)) := by
  rw [injective_iff_map_eq_one]
  intro a h
  apply Units.ext
  ext i j
  have h1 := congrArg (fun φ : MulAut (Multiplicative (I4 → ZMod 2)) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1))) i) h
  simp only [natHomI', MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    toAdd_ofAdd, MulAut.one_apply, Matrix.mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1

@[expose] def Typ4 (g : MulAut W11) (A : GL I4 (ZMod 2)) : Prop :=
  ∀ x, beta4 (g x) = natHomI' I4 (ZMod 2) A (beta4 x)

theorem typ4_one : Typ4 1 1 := fun x => by
  rw [map_one]
  rfl

theorem typ4_mul {g h : MulAut W11} {A B : GL I4 (ZMod 2)} (hg : Typ4 g A) (hh : Typ4 h B) :
    Typ4 (g * h) (A * B) := fun x => by
  show beta4 (g (h x)) = natHomI' I4 (ZMod 2) (A * B) (beta4 x)
  rw [hg, hh, map_mul]
  rfl

theorem typ4_inv {g : MulAut W11} {A : GL I4 (ZMod 2)} (hg : Typ4 g A) : Typ4 g⁻¹ A⁻¹ :=
  fun x => by
    have h1 : beta4 x = natHomI' I4 (ZMod 2) A (beta4 (g⁻¹ x)) := by
      have := hg (g⁻¹ x)
      rwa [MulAut.apply_inv_self] at this
    rw [h1]
    show beta4 (g⁻¹ x) = natHomI' I4 (ZMod 2) A⁻¹ (natHomI' I4 (ZMod 2) A (beta4 (g⁻¹ x)))
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

theorem typ4_unique {g : MulAut W11} {A B : GL I4 (ZMod 2)} (hA : Typ4 g A) (hB : Typ4 g B) :
    A = B := by
  apply natHomI'_injective
  refine MulEquiv.ext fun w => ?_
  obtain ⟨x, rfl⟩ := beta4_surj w
  exact (hA x).symm.trans (hB x)

@[expose] def Good4 : Subgroup (MulAut W11) where
  carrier := {g | ∃ A ∈ StatedSp 2 (ZMod 2), Typ4 g A}
  mul_mem' := by
    rintro g h ⟨A, hA, hgA⟩ ⟨B, hB, hhB⟩
    exact ⟨A * B, (StatedSp 2 (ZMod 2)).mul_mem hA hB, typ4_mul hgA hhB⟩
  one_mem' := ⟨1, (StatedSp 2 (ZMod 2)).one_mem, typ4_one⟩
  inv_mem' := by
    rintro g ⟨A, hA, hgA⟩
    exact ⟨A⁻¹, (StatedSp 2 (ZMod 2)).inv_mem hA, typ4_inv hgA⟩

theorem good_exists (g : ↥Good4) : ∃ A : GL I4 (ZMod 2), A ∈ StatedSp 2 (ZMod 2) ∧ Typ4 g.1 A :=
  g.2

@[expose] noncomputable def psi4 (g : ↥Good4) : GL I4 (ZMod 2) := Classical.choose (good_exists g)

theorem psi4_mem (g : ↥Good4) : psi4 g ∈ StatedSp 2 (ZMod 2) :=
  (Classical.choose_spec (good_exists g)).1

theorem psi4_spec (g : ↥Good4) : Typ4 g.1 (psi4 g) := (Classical.choose_spec (good_exists g)).2

theorem psi4_eq {g : ↥Good4} {A : GL I4 (ZMod 2)} (h : Typ4 g.1 A) : psi4 g = A :=
  typ4_unique (psi4_spec g) h

@[expose] noncomputable def Psi4 : ↥Good4 →* GL I4 (ZMod 2) where
  toFun := psi4
  map_one' := psi4_eq (by rw [OneMemClass.coe_one]; exact typ4_one)
  map_mul' g h := psi4_eq (by rw [Subgroup.coe_mul]; exact typ4_mul (psi4_spec g) (psi4_spec h))

@[expose] def mkGLS (cs ics : List ℕ) (h1 : colMatS cs * colMatS ics = 1)
    (h2 : colMatS ics * colMatS cs = 1) : GL I4 (ZMod 2) :=
  ⟨colMatS cs, colMatS ics, h1, h2⟩

theorem natHomI'_mkGLS {cs ics : List ℕ} {h1 : colMatS cs * colMatS ics = 1}
    {h2 : colMatS ics * colMatS cs = 1}
    (hmv : ∀ q < 16, (colMatS cs).mulVec (fun i => bvec 4 q (eI i)) =
      fun i => bvec 4 (actM cs q) (eI i)) {q : ℕ} (hq : q < 16) :
    natHomI' I4 (ZMod 2) (mkGLS cs ics h1 h2) (iotaEquiv (toW 4 q)) =
      iotaEquiv (toW 4 (actM cs q)) := by
  show Multiplicative.ofAdd ((colMatS cs).mulVec (fun i => bvec 4 q (eI i))) =
    Multiplicative.ofAdd (fun i => bvec 4 (actM cs q) (eI i))
  rw [hmv q hq]

theorem typ4_of_cols {g : MulAut W11} {arr : Array ℕ}
    (hg : ∀ m, g (toW 11 m) = toW 11 (act11 arr m)) {cs ics : List ℕ}
    {h1 : colMatS cs * colMatS ics = 1} {h2 : colMatS ics * colMatS cs = 1}
    (hmv : ∀ q < 16, (colMatS cs).mulVec (fun i => bvec 4 q (eI i)) =
      fun i => bvec 4 (actM cs q) (eI i))
    (hty : ∀ m < 2048, actM c4 (act11 arr m) = actM cs (actM c4 m)) :
    Typ4 g (mkGLS cs ics h1 h2) := by
  intro x
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [hg m, beta4_toW, beta4_toW, hty m hm]
  exact (natHomI'_mkGLS hmv (actM_c4_lt m)).symm

theorem mem_cols_x : xC ∈ [xC, xI, yC, yI, oC] ++ trv := by simp
theorem mem_cols_y : yC ∈ [xC, xI, yC, yI, oC] ++ trv := by simp
theorem mem_cols_o : oC ∈ [xC, xI, yC, yI, oC] ++ trv := by simp

@[expose] def gxM : GL I4 (ZMod 2) := mkGLS xC xI x_inv1 x_inv2
@[expose] def gyM : GL I4 (ZMod 2) := mkGLS yC yI y_inv1 y_inv2
@[expose] def goM : GL I4 (ZMod 2) := mkGLS oC oC o_inv o_inv

theorem gxM_mem : gxM ∈ StatedSp 2 (ZMod 2) := CFSG.Open.StatedAPI.mem_statedSp_iff.2 x_symp
theorem gyM_mem : gyM ∈ StatedSp 2 (ZMod 2) := CFSG.Open.StatedAPI.mem_statedSp_iff.2 y_symp
theorem goM_mem : goM ∈ StatedSp 2 (ZMod 2) := CFSG.Open.StatedAPI.mem_statedSp_iff.2 o_symp

theorem typ4_x : Typ4 (rho11 AutPerm le_rfl ⟨lzX, lzX_mem⟩) gxM :=
  typ4_of_cols (fun m => rho11_toW AutPerm le_rfl _ hasArr_lzX m)
    (fun q hq => mulVec_cols xC mem_cols_x q hq) x_type

theorem typ4_y : Typ4 (rho11 AutPerm le_rfl ⟨lzY, lzY_mem⟩) gyM :=
  typ4_of_cols (fun m => rho11_toW AutPerm le_rfl _ hasArr_lzY m)
    (fun q hq => mulVec_cols yC mem_cols_y q hq) y_type

theorem typ4_o : Typ4 (rho11 AutPerm le_rfl ⟨oddP, oddP_mem⟩) goM :=
  typ4_of_cols (fun m => rho11_toW AutPerm le_rfl _ hasArr_oddP m)
    (fun q hq => mulVec_cols oC mem_cols_o q hq) o_type

theorem typ4_t : Typ4 (rho11 AutPerm le_rfl ⟨tP, tP_mem⟩) 1 := by
  intro x
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [rho11_toW AutPerm le_rfl _ hasArr_tP m, beta4_toW, beta4_toW, t_type m hm, map_one]
  rfl

@[expose] noncomputable def GoodP : Subgroup S24 :=
  (Good4.comap (rho11 AutPerm le_rfl)).map AutPerm.subtype

theorem lzX_good : lzX ∈ GoodP := ⟨⟨lzX, lzX_mem⟩, ⟨gxM, gxM_mem, typ4_x⟩, rfl⟩
theorem lzY_good : lzY ∈ GoodP := ⟨⟨lzY, lzY_mem⟩, ⟨gyM, gyM_mem, typ4_y⟩, rfl⟩
theorem oddP_good : oddP ∈ GoodP := ⟨⟨oddP, oddP_mem⟩, ⟨goM, goM_mem, typ4_o⟩, rfl⟩

theorem Lz_le_GoodP : Lz ≤ GoodP := by
  rw [Lz, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact lzX_good
  · exact lzY_good

theorem MY0_le_GoodP :
    MY M24g S0 ≤ GoodP := by
  intro σ hσ
  rcases MY0_cases hσ with h | h
  · exact Lz_le_GoodP h
  · have := GoodP.mul_mem oddP_good (Lz_le_GoodP h)
    simpa using this

theorem rho11_MY0_good
    {σ : S24} (hσ : σ ∈ MY M24g S0) :
    rho11 AutPerm le_rfl ⟨σ, MY0_le_autPerm hσ⟩ ∈ Good4 := by
  obtain ⟨y, hy, hyσ⟩ := MY0_le_GoodP hσ
  have : y = ⟨σ, MY0_le_autPerm hσ⟩ := Subtype.ext hyσ
  rw [this] at hy
  exact hy

@[expose] noncomputable def psiM :
    ↥(MY M24g S0) →* GL I4 (ZMod 2) :=
  Psi4.comp (((rho11 AutPerm le_rfl).comp (Subgroup.inclusion MY0_le_autPerm)).codRestrict Good4
    (fun σ => rho11_MY0_good σ.2))

section PsiM


theorem psiM_spec (σ : ↥(MY M24g S0)) :
    Typ4 (rho11 AutPerm le_rfl ⟨σ.1, MY0_le_autPerm σ.2⟩) (psiM σ) :=
  psi4_spec ⟨_, rho11_MY0_good σ.2⟩

theorem psiM_eq {σ : ↥(MY M24g S0)} {A : GL I4 (ZMod 2)}
    (h : Typ4 (rho11 AutPerm le_rfl ⟨σ.1, MY0_le_autPerm σ.2⟩) A) : psiM σ = A :=
  psi4_eq (g := ⟨_, rho11_MY0_good σ.2⟩) h

theorem psiM_mem (σ : ↥(MY M24g S0)) : psiM σ ∈ StatedSp 2 (ZMod 2) :=
  psi4_mem ⟨_, rho11_MY0_good σ.2⟩

theorem psiM_one_iff {σ : ↥(MY M24g S0)} :
    psiM σ = 1 ↔ ∀ x : W11, rho11 AutPerm le_rfl ⟨σ.1, MY0_le_autPerm σ.2⟩ x * x⁻¹ ∈ W0 := by
  constructor
  · intro h x
    have h1 := psiM_spec σ x
    rw [h, map_one] at h1
    have e1 : beta4 x⁻¹ = (beta4 x)⁻¹ := map_inv beta4 x
    rw [← beta4_ker, map_mul, e1]
    show beta4 (((rho11 AutPerm le_rfl) ⟨σ.1, MY0_le_autPerm σ.2⟩) x) * (beta4 x)⁻¹ = 1
    rw [h1]
    exact mul_inv_cancel _
  · intro h
    refine psiM_eq fun x => ?_
    have h1 := (beta4_ker _).2 (h x)
    have e1 : beta4 x⁻¹ = (beta4 x)⁻¹ := map_inv beta4 x
    rw [map_mul, e1] at h1
    have h2 : beta4 (rho11 AutPerm le_rfl ⟨σ.1, MY0_le_autPerm σ.2⟩ x) = beta4 x :=
      mul_inv_eq_one.1 h1
    rw [h2, map_one]
    rfl

end PsiM

section Kernel


theorem psiM_ksP (c : Fin 64) : psiM ⟨ksP c, KSp_le_MY0 (ksP_mem_KSp c)⟩ = 1 := by
  rw [psiM_one_iff]
  intro x
  exact img11_KSp_le_commSub (mem_img11_KSp.2 ⟨c, rfl⟩) x

theorem psiM_tP : psiM ⟨tP, tP_mem_MY0⟩ = 1 := psiM_eq typ4_t

theorem ker_psiM_ge : piM.ker ≤ psiM.ker := by
  intro σ hσ
  have hN : (σ : S24) ∈ N0 := mem_N0.2 ⟨σ.2, hσ⟩
  rw [N0_eq_sup] at hN
  have hK : (KSp ⊔ Subgroup.zpowers tP) ≤ psiM.ker.map (MY M24g S0).subtype := by
    refine sup_le (fun k hk => ?_) (Subgroup.zpowers_le.2 ?_)
    · obtain ⟨c, rfl⟩ := mem_KSp_iff.1 hk
      exact ⟨⟨ksP c, KSp_le_MY0 (ksP_mem_KSp c)⟩, psiM_ksP c, rfl⟩
    · exact ⟨⟨tP, tP_mem_MY0⟩, psiM_tP, rfl⟩
  obtain ⟨y, hy, hyσ⟩ := hK hN
  have : y = σ := Subtype.ext hyσ
  rwa [this] at hy

theorem W0_ne_top : W0 ≠ ⊤ := by
  intro h
  have h1 : Nat.card ↥W0 = Nat.card ↥(⊤ : Subgroup W11) := by rw [h]
  rw [card_W0, Subgroup.card_top, Nat.card_eq_fintype_card, card_Wn] at h1
  norm_num at h1

theorem ker_psiM_le : psiM.ker ≤ piM.ker := by
  intro σ hσ
  by_contra hne
  have hQn : (psiM.ker.map piM).Normal := (MonoidHom.normal_ker psiM).map piM piM_surjective
  have hnt : Nontrivial (psiM.ker.map piM) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => hne ?_
    have : piM σ ∈ psiM.ker.map piM := ⟨σ, hσ, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (N := psiM.ker.map piM)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
  have hLz : ∀ l (hl : l ∈ Lz), psiM ⟨l, Lz_le_MY0 hl⟩ = 1 := by
    intro l hl
    have h1 : piM ⟨l, Lz_le_MY0 hl⟩ ∈ alternatingGroup (Fin 6) := by
      have := colLz_mem l hl
      rw [A6c_eq] at this
      exact this
    obtain ⟨q, hq, hqe⟩ := hA h1
    have h2 : q⁻¹ * ⟨l, Lz_le_MY0 hl⟩ ∈ piM.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqe, inv_mul_cancel]
    have h3 : psiM (q⁻¹ * ⟨l, Lz_le_MY0 hl⟩) = 1 := ker_psiM_ge h2
    have h4 : psiM q = 1 := hq
    have h5 : (⟨l, Lz_le_MY0 hl⟩ : ↥(MY M24g S0)) = q * (q⁻¹ * ⟨l, Lz_le_MY0 hl⟩) :=
      (mul_inv_cancel_left q _).symm
    rw [h5, map_mul, h4, h3, one_mul]
  have hle : img11 Lz ≤ moveSub W0 := by
    rintro _ ⟨σ', hσ', rfl⟩ x
    have hl : (σ' : S24) ∈ Lz := Subgroup.mem_subgroupOf.1 hσ'
    exact (psiM_one_iff.1 (hLz σ' hl)) x
  have h1 : commV (img11 Lz) ≤ W0 := commV_le_iff.2 hle
  rw [commV_img11_Lz] at h1
  exact W0_ne_top (eq_top_iff.2 h1)

theorem ker_psiM : psiM.ker = piM.ker := le_antisymm ker_psiM_le ker_psiM_ge

theorem card_ker_psiM : Nat.card psiM.ker = 192 := by rw [ker_psiM, card_ker_piM]

theorem card_statedSp_two_zmod : Nat.card (StatedSp 2 (ZMod 2)) = 720 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, Nat.card_zmod]
  norm_num

theorem psiM_range : psiM.range = StatedSp 2 (ZMod 2) := by
  have hle : psiM.range ≤ StatedSp 2 (ZMod 2) := by
    rintro _ ⟨σ, rfl⟩
    exact psiM_mem σ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup psiM.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange psiM).toEquiv, card_ker_psiM,
    card_MY0] at h
  rw [card_statedSp_two_zmod]
  omega

theorem act_trivial_iff {σ : S24} (hσ : σ ∈ MY M24g S0) :
    (∀ x : W11, rho11 AutPerm le_rfl ⟨σ, MY0_le_autPerm hσ⟩ x * x⁻¹ ∈ W0) ↔ σ ∈ N0 := by
  rw [← psiM_one_iff (σ := ⟨σ, hσ⟩)]
  have : psiM ⟨σ, hσ⟩ = 1 ↔ (⟨σ, hσ⟩ : ↥(MY M24g S0)) ∈ piM.ker := by
    rw [← ker_psiM]
    exact Iff.rfl
  rw [this]
  exact ⟨fun h => mem_N0.2 ⟨hσ, h⟩, fun h => (mem_N0.1 h).2⟩

theorem std_ind4 : InducesOn (img11 (MY M24g S0)) ⊤ W0 (Multiplicative (I4 → ZMod 2))
    (natSubI' I4 (ZMod 2) (StatedSp 2 (ZMod 2))) := by
  refine ⟨le_top, fun g hg u hu => Subgroup.mem_top _, fun g hg z hz => HS_stab_W0 hg hz,
    beta4.comp (⊤ : Subgroup W11).subtype, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨x, hx⟩ := beta4_surj w
    exact ⟨⟨x, Subgroup.mem_top x⟩, hx⟩
  · intro u
    exact beta4_ker (u : W11)
  · intro g hg
    obtain ⟨σ, hσ, rfl⟩ := hg
    have hσ' : (σ : S24) ∈ MY M24g S0 := Subgroup.mem_subgroupOf.1 hσ
    refine ⟨natHomI' I4 (ZMod 2) (psiM ⟨σ, hσ'⟩), ⟨_, psiM_mem _, rfl⟩, fun u u' h => ?_⟩
    show beta4 (u' : W11) = natHomI' I4 (ZMod 2) (psiM ⟨σ, hσ'⟩) (beta4 (u : W11))
    rw [h]
    exact psiM_spec ⟨σ, hσ'⟩ (u : W11)
  · rintro γ ⟨A, hA, rfl⟩
    have hA' : A ∈ psiM.range := by rw [psiM_range]; exact hA
    obtain ⟨σ, hσ⟩ := hA'
    refine ⟨rho11 AutPerm le_rfl ⟨σ.1, MY0_le_autPerm σ.2⟩,
      ⟨⟨σ.1, MY0_le_autPerm σ.2⟩, Subgroup.mem_subgroupOf.2 σ.2, rfl⟩, fun u u' h => ?_⟩
    show beta4 (u' : W11) = natHomI' I4 (ZMod 2) A (beta4 (u : W11))
    rw [h, ← hσ]
    exact psiM_spec σ (u : W11)

end Kernel

theorem irred4 (W' : Subgroup (Multiplicative (I4 → ZMod 2)))
    (hinv : ∀ γ ∈ natSubI' I4 (ZMod 2) (StatedSp 2 (ZMod 2)), ∀ w ∈ W', γ w ∈ W') :
    W' = ⊥ ∨ W' = ⊤ := by
  have key := irred_of_check (W' := W'.comap iotaEquiv.toMonoidHom) trv trv_len 1 trv_check (by
    intro cs hcs w hw
    obtain ⟨q, hq, rfl⟩ := toW_surj 4 w
    have hlen := trv_len cs hcs
    show iotaEquiv (maskHom 4 4 cs (toW 4 q)) ∈ W'
    rw [maskHom_toW hlen]
    have hmem : cs ∈ [xC, xI, yC, yI, oC] ++ trv := List.mem_append_right _ hcs
    have hA : mkGLS cs cs (trv_inv cs hcs) (trv_inv cs hcs) ∈ StatedSp 2 (ZMod 2) :=
      CFSG.Open.StatedAPI.mem_statedSp_iff.2 (trv_symp cs hcs)
    have h1 := hinv _ ⟨_, hA, rfl⟩ (iotaEquiv (toW 4 q)) hw
    rwa [natHomI'_mkGLS (fun q' hq' => mulVec_cols cs hmem q' hq') hq] at h1)
  rcases key with h0 | h1
  · left
    rw [eq_bot_iff]
    intro w hw
    have : iotaEquiv.symm w ∈ W'.comap iotaEquiv.toMonoidHom := by
      show iotaEquiv (iotaEquiv.symm w) ∈ W'
      rw [MulEquiv.apply_symm_apply]
      exact hw
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply iotaEquiv w, this, map_one]
  · right
    rw [eq_top_iff]
    intro w _
    have : iotaEquiv.symm w ∈ W'.comap iotaEquiv.toMonoidHom := by rw [h1]; exact Subgroup.mem_top _
    have h2 : iotaEquiv (iotaEquiv.symm w) ∈ W' := this
    rwa [MulEquiv.apply_symm_apply] at h2

end CFSG.Quasithin.H153
