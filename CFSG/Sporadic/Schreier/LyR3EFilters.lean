module

public import CFSG.Sporadic.Schreier.LyLocalAut
public import CFSG.Sporadic.Schreier.LyR3EData
public import CFSG.Sporadic.Schreier.LyR3ECertificate
public import CFSG.Sporadic.Schreier.LyR3EPerm
public import CFSG.Sporadic.Schreier.LyCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native
open scoped commutatorElement

private theorem RepM.pow
    {X : Mat} {g : J} (h : RepM X g) (n : ℕ) : RepM (powM 5 111 X n) (g ^ n) := by
  unfold RepM at *
  rw [toMat_powM, h, mat_pow' g n]

theorem RepM.eq_of_beq
    {X Y : Mat} {g h : J} (hX : RepM X g) (hY : RepM Y h)
    (e : (X == Y) = true) : g = h := by
  have hXY : X = Y := beq_iff_eq.1 e
  subst hXY
  exact hX.unique hY

theorem RepM.ne_of_diff
    {X Y : Mat} {g h : J} (hX : RepM X g) (hY : RepM Y h)
    (e : diffMod5 X Y = true) : g ≠ h := by
  intro hgh
  apply toMat_ne_of_diffMod5 e
  rw [show toMat 5 111 X = mat g from hX, show toMat 5 111 Y = mat h from hY, hgh]

abbrev fM : Mat := sPts[113]!

abbrev b4M : Mat := powM 5 111 matB 4

abbrev gM : Mat := r3eGM (r3eHM b4M) fM

abbrev cM : Mat := (pairAt csArr 3).1

theorem r3e_parts :
    (mulM 5 111 (mulM 5 111 (mulM 5 111 syGenArr[2]! syGenArr[1]!) syGenArr[2]!) syGenArr[1]! ==
      fM) = true ∧
    (mulM 5 111 fM fM == idM 111) = true ∧ diffMod5 fM (idM 111) = true ∧
    diffMod5 fM matA = true ∧ (mulM 5 111 matA fM == mulM 5 111 fM matA) = true ∧
    (mulM 5 111 gM matA == mulM 5 111 fM gM) = true ∧
    (∀ w ∈ r3eWordsN, (mulM 5 111 (cWordM csArr w) fM == mulM 5 111 fM (cWordM csArr w)) =
      true) ∧
    (r3eP18 cM (idM 111) gM == idM 111) = true ∧ diffMod5 (r3eP18 cM matA gM) (idM 111) = true ∧
    diffMod5 (r3eP18 cM fM gM) (idM 111) = true ∧
    (r3eP18 cM (mulM 5 111 matA fM) gM == idM 111) = true := by
  have h := ly_r3e_certificate
  unfold r3eCertificate r3eWithStar r3eWithGens r3eChecks at h
  dsimp only at h
  rw [← csArr_def, show sylowGens csArr = syGenArr from rfl,
    show (sylowBFS syGenArr 256).1 = sPts from rfl] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem lyf_eq_sTree :
    lyf = sTree 113 := by
  rw [lyf, sylowElt_eq (by decide)]
  rfl

theorem repM_fM :
    RepM fM lyf := by
  rw [lyf_eq_sTree]
  exact (repM_sTree 113 (by norm_num)).1

theorem repM_hM : RepM (r3eHM b4M) r3eH := by
  have h1 := ((repM_matA.mul repM_matB).mul repM_matA).mul (repM_b4.mul repM_matA)
  have e : a * b * a * (b⁻¹ * a) = r3eH := by
    rw [r3eH, lyz, mul_inv_rev, a_inv']
  rw [← e]
  exact h1

theorem repM_gM :
    RepM gM r3eG := by
  have h1 := ((repM_hM.mul repM_fM).pow 7).mul ((repM_matA.mul repM_hM).pow 4)
  rw [r3eG, lyz]
  exact h1

theorem repM_cM :
    RepM cM r3eC := (repM_csArr 3).1

theorem repM_cWordM
    (w : List ℤ) : RepM (cWordM csArr w) (evalWord cStar w) :=
  repM_evalWordM (fun i => (repM_csArr i).1) (fun i => (repM_csArr i).2) w

theorem r3eFusion_eq :
    r3eFusion = lyf := by
  have h1 := (((repM_syGen 2).mul (repM_syGen 1)).mul (repM_syGen 2)).mul (repM_syGen 1)
  have e := h1.eq_of_beq repM_fM r3e_parts.1
  rw [← e]
  simp [r3eFusion, r3eFusionWord, evalWord, letterVal, mul_assoc]

private theorem lyf_sq :
    lyf * lyf = 1 :=
  (repM_fM.mul repM_fM).eq_of_beq repM_id r3e_parts.2.1

private theorem lyf_ne_one :
    lyf ≠ 1 := repM_fM.ne_of_diff repM_id r3e_parts.2.2.1

theorem lyf_ne_lyz :
    lyf ≠ lyz := repM_fM.ne_of_diff repM_matA r3e_parts.2.2.2.1

private theorem orderOf_lyf :
    orderOf lyf = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact lyf_sq) lyf_ne_one

theorem lyz_mul_lyf :
    lyz * lyf = lyf * lyz :=
  (repM_matA.mul repM_fM).eq_of_beq (repM_fM.mul repM_matA) r3e_parts.2.2.2.2.1

theorem r3eG_mul_lyz :
    r3eG * lyz = lyf * r3eG :=
  (repM_gM.mul repM_matA).eq_of_beq (repM_fM.mul repM_gM) r3e_parts.2.2.2.2.2.1

theorem r3eG_conj_lyz :
    r3eG * lyz * r3eG⁻¹ = lyf := by
  rw [r3eG_mul_lyz, mul_inv_cancel_right]

theorem r3eD_mul_lyf
    {k : ℕ} (hk : k < 6) : r3eD k * lyf = lyf * r3eD k := by
  have hw : r3eWords.getD k [] ∈ r3eWordsN := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [r3eWords] using hk)]
    exact List.getElem_mem _
  exact ((repM_cWordM _).mul repM_fM).eq_of_beq (repM_fM.mul (repM_cWordM _))
    (r3e_parts.2.2.2.2.2.2.1 _ hw)

theorem r3e_pow_one :
    (r3eC * 1 * r3eG) ^ 18 = 1 :=
  (((repM_cM.mul repM_id).mul repM_gM).pow 18).eq_of_beq repM_id r3e_parts.2.2.2.2.2.2.2.1

theorem r3e_pow_z :
    (r3eC * lyz * r3eG) ^ 18 ≠ 1 :=
  (((repM_cM.mul repM_matA).mul repM_gM).pow 18).ne_of_diff repM_id
    r3e_parts.2.2.2.2.2.2.2.2.1

theorem r3e_pow_f :
    (r3eC * lyf * r3eG) ^ 18 ≠ 1 :=
  (((repM_cM.mul repM_fM).mul repM_gM).pow 18).ne_of_diff repM_id
    r3e_parts.2.2.2.2.2.2.2.2.2.1

theorem r3e_pow_zf :
    (r3eC * (lyz * lyf) * r3eG) ^ 18 = 1 :=
  (((repM_cM.mul (repM_matA.mul repM_fM)).mul repM_gM).pow 18).eq_of_beq repM_id
    r3e_parts.2.2.2.2.2.2.2.2.2.2

theorem lyf_mem_lyC :
    lyf ∈ lyC := by
  rw [lyf_eq_sTree]
  exact lyS_le_lyC (sTree_mem 113 (by norm_num))

theorem r3eD_mem_lyC
    (k : ℕ) : r3eD k ∈ lyC := evalWord_mem fun _ _ => cStar_mem _

theorem lyC_eq_centralizer :
    lyC = Subgroup.centralizer ({lyz} : Set J) :=
  full_involution_centralizer.1

theorem gen_mul_lyf
    {y : J} (hy : y ∈ ({lyz, lyf} ∪ r3eD '' Set.Iio 6 : Set J)) :
    y * lyf = lyf * y := by
  rcases hy with hy | ⟨k, hk, rfl⟩
  · rcases hy with rfl | rfl
    · exact lyz_mul_lyf
    · rfl
  · exact r3eD_mul_lyf hk

theorem gen_mem_lyC
    {y : J} (hy : y ∈ ({lyz, lyf} ∪ r3eD '' Set.Iio 6 : Set J)) : y ∈ lyC := by
  rcases hy with hy | ⟨k, -, rfl⟩
  · rcases hy with rfl | rfl
    · exact lyz_mem_lyC
    · exact lyf_mem_lyC
  · exact r3eD_mem_lyC k

theorem mem_conj_lyC
    {y : J} (hy : y * lyf = lyf * y) :
    y ∈ lyC.map (MulAut.conj r3eG).toMonoidHom := by
  refine ⟨r3eG⁻¹ * y * r3eG, ?_, ?_⟩
  · rw [SetLike.mem_coe, lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hz : lyz = r3eG⁻¹ * lyf * r3eG := by
      rw [← r3eG_conj_lyz]; group
    rw [hz]
    calc r3eG⁻¹ * y * r3eG * (r3eG⁻¹ * lyf * r3eG) = r3eG⁻¹ * (y * lyf) * r3eG := by group
      _ = r3eG⁻¹ * (lyf * y) * r3eG := by rw [hy]
      _ = r3eG⁻¹ * lyf * r3eG * (r3eG⁻¹ * y * r3eG) := by group
  · show (MulAut.conj r3eG) (r3eG⁻¹ * y * r3eG) = y
    rw [MulAut.conj_apply]
    group

theorem r3eD0_le :
    r3eD0 ≤ lyC ⊓ lyC.map (MulAut.conj r3eG).toMonoidHom := by
  rw [r3eD0, Subgroup.closure_le]
  intro y hy
  exact ⟨gen_mem_lyC hy, mem_conj_lyC (gen_mul_lyf hy)⟩

theorem lyz_mem_r3eD0 : lyz ∈ r3eD0 :=
  Subgroup.subset_closure (Or.inl (Set.mem_insert _ _))

theorem lyf_mem_r3eD0 : lyf ∈ r3eD0 :=
  Subgroup.subset_closure (Or.inl (Set.mem_insert_of_mem _ rfl))

theorem r3eD_mem_r3eD0 {k : ℕ} (hk : k < 6) : r3eD k ∈ r3eD0 :=
  Subgroup.subset_closure (Or.inr ⟨k, hk, rfl⟩)

@[expose] def fC :
    lyC := ⟨lyf, lyf_mem_lyC⟩

@[expose] def dC (k : ℕ) : lyC := ⟨r3eD k, r3eD_mem_lyC k⟩

theorem imgC_dC_eq
    (k : ℕ) : imgC (dC k) = evalWord pPerm (r3eWords.getD k []) := by
  have h1 : dC k = evalWord cStarC (r3eWords.getD k []) := by
    apply Subtype.ext
    rw [← Subgroup.coe_subtype, map_evalWord]
    rfl
  rw [h1, map_evalWord]
  simp only [imgC_cStarC]

theorem imgC_fC_eq :
    imgC fC = evalWord pPerm (sylowWords[2]!) * evalWord pPerm (sylowWords[1]!) *
    (evalWord pPerm (sylowWords[2]!) * evalWord pPerm (sylowWords[1]!)) := by
  have h1 : fC = ⟨sylowGen ⟨2, by omega⟩, sylowGen_mem_lyC _⟩ *
      ⟨sylowGen ⟨1, by omega⟩, sylowGen_mem_lyC _⟩ *
      (⟨sylowGen ⟨2, by omega⟩, sylowGen_mem_lyC _⟩ *
        ⟨sylowGen ⟨1, by omega⟩, sylowGen_mem_lyC _⟩) := by
    apply Subtype.ext
    rw [fC]
    show lyf = sylowGen ⟨2, by omega⟩ * sylowGen ⟨1, by omega⟩ *
      (sylowGen ⟨2, by omega⟩ * sylowGen ⟨1, by omega⟩)
    rw [← r3eFusion_eq]
    simp [r3eFusion, r3eFusionWord, evalWord, letterVal, mul_assoc]
  rw [h1]
  simp only [map_mul]
  rw [imgC_sylowGen (k := 2) (by norm_num), imgC_sylowGen (k := 1) (by norm_num)]

theorem dImg_eq : ∀ k : Fin 6, ∀ x : Fin 11,
    evalWord pPerm (r3eWords.getD k.val []) x = arrFun (dImgArr[k.val]!) x := by
  decide +kernel

theorem fImg_eq : ∀ x : Fin 11,
    (evalWord pPerm (sylowWords[2]!) * evalWord pPerm (sylowWords[1]!) *
      (evalWord pPerm (sylowWords[2]!) * evalWord pPerm (sylowWords[1]!))) x =
      arrFun (dImgArr[6]!) x := by
  decide +kernel

theorem img_arr
    (k : Fin 7) : ∃ y ∈ r3eD0, ∃ hy : y ∈ lyC,
    ∀ x, imgC ⟨y, hy⟩ x = arrFun (dImgArr[k.val]!) x := by
  by_cases hk : k.val < 6
  · refine ⟨r3eD k.val, r3eD_mem_r3eD0 hk, r3eD_mem_lyC _, fun x => ?_⟩
    have := imgC_dC_eq k.val
    rw [show (⟨r3eD k.val, r3eD_mem_lyC _⟩ : lyC) = dC k.val from rfl, this]
    exact dImg_eq ⟨k.val, hk⟩ x
  · have hk6 : k.val = 6 := by omega
    refine ⟨lyf, lyf_mem_r3eD0, lyf_mem_lyC, fun x => ?_⟩
    rw [show (⟨lyf, lyf_mem_lyC⟩ : lyC) = fC from rfl, imgC_fC_eq, hk6]
    exact fImg_eq x

theorem perm_of_commute (σ : Equiv.Perm (Fin 11))
    (hσ : ∀ k : Fin 7, ∀ x, σ (arrFun (dImgArr[k.val]!) x) = arrFun (dImgArr[k.val]!) (σ x)) :
    σ = 1 ∨ ∀ x, σ x = arrFun (dImgArr[6]!) x := by
  have hfold : ∀ (w : List ℕ) (y : Fin 11), (∀ k ∈ w, k < 7) →
      σ (w.foldr (fun k y => arrFun (dImgArr[k]!) y) y) =
        w.foldr (fun k y => arrFun (dImgArr[k]!) y) (σ y) := by
    intro w y hw
    induction w with
    | nil => rfl
    | cons k w ih =>
      simp only [List.foldr_cons]
      rw [hσ ⟨k, hw k List.mem_cons_self⟩, ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))]
  have hcand : ∀ x, σ x = dCand (σ 0) (σ 8) x := by
    intro x
    have := hfold (dWord x) (dRep x) (dWord_lt x)
    rw [dWord_rep] at this
    rw [this, dCand]
    congr 1
    unfold dRep
    split_ifs <;> rfl
  have hcomm : ∀ k : Fin 7, ∀ x, dCand (σ 0) (σ 8) (arrFun (dImgArr[k.val]!) x) =
      arrFun (dImgArr[k.val]!) (dCand (σ 0) (σ 8) x) := by
    intro k x
    rw [← hcand, ← hcand, hσ]
  have hinj : ∀ x y, dCand (σ 0) (σ 8) x = dCand (σ 0) (σ 8) y → x = y :=
    fun x y h => σ.injective (by rw [hcand x, hcand y]; exact h)
  rcases dCand_check _ _ hcomm hinj with h | h
  · left
    ext x
    rw [hcand x, h x]
    rfl
  · right
    intro x
    rw [hcand x, h x]

theorem mem_centralizer_r3eD0
    {x : J} (hx : x ∈ Subgroup.centralizer (r3eD0 : Set J)) :
    x = 1 ∨ x = lyz ∨ x = lyf ∨ x = lyz * lyf := by
  rw [Subgroup.mem_centralizer_iff] at hx
  have hxC : x ∈ lyC := by
    rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact (hx lyz lyz_mem_r3eD0).symm
  set σ := imgC ⟨x, hxC⟩ with hσdef
  have hσ : ∀ k : Fin 7, ∀ p, σ (arrFun (dImgArr[k.val]!) p) =
      arrFun (dImgArr[k.val]!) (σ p) := by
    intro k p
    obtain ⟨y, hyD, hyC, himg⟩ := img_arr k
    have hxy : (⟨y, hyC⟩ : lyC) * ⟨x, hxC⟩ = ⟨x, hxC⟩ * ⟨y, hyC⟩ :=
      Subtype.ext (hx y hyD)
    have h2 := congrArg (fun c => imgC c p) hxy
    simp only [map_mul, Equiv.Perm.mul_apply] at h2
    rw [← himg, ← himg, hσdef]
    exact h2.symm
  rcases perm_of_commute σ hσ with h1 | h1
  · have hk : (⟨x, hxC⟩ : lyC) ∈ zGroup := (imgC_eq_one_iff _).1 h1
    rcases mem_zGroup.1 hk with h | h
    · left
      exact congrArg Subtype.val h
    · right; left
      exact congrArg Subtype.val h
  · have hf : ∀ p, imgC fC p = arrFun (dImgArr[6]!) p := by
      intro p
      rw [imgC_fC_eq]
      exact fImg_eq p
    have h2 : imgC (⟨x, hxC⟩ * fC⁻¹) = 1 := by
      rw [map_mul, map_inv]
      have e : imgC ⟨x, hxC⟩ = imgC fC := Equiv.ext fun p => by rw [← hσdef, h1 p, hf p]
      rw [e, mul_inv_cancel]
    have hk := (imgC_eq_one_iff _).1 h2
    have hff : lyf * lyf = 1 := lyf_sq
    have hfinv : lyf = lyf⁻¹ := eq_inv_of_mul_eq_one_left hff
    rcases mem_zGroup.1 hk with h | h
    · right; right; left
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h'
      have : x * lyf⁻¹ = 1 := h'
      rw [← hfinv] at this
      calc x = x * lyf * lyf := by rw [mul_assoc, hff, mul_one]
        _ = lyf := by rw [this, one_mul]
    · right; right; right
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h'
      have : x * lyf⁻¹ = lyz := h'
      rw [← hfinv] at this
      calc x = x * lyf * lyf := by rw [mul_assoc, hff, mul_one]
        _ = lyz * lyf := by rw [this]

theorem lyz_mem_centralizer_r3eD0 :
    lyz ∈ Subgroup.centralizer (r3eD0 : Set J) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyC : y ∈ lyC := (r3eD0_le hy).1
  rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hyC
  exact hyC

theorem lyf_mem_centralizer_r3eD0 :
    lyf ∈ Subgroup.centralizer (r3eD0 : Set J) := by
  have : r3eD0 ≤ Subgroup.centralizer ({lyf} : Set J) := by
    rw [r3eD0, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact gen_mul_lyf hy
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := this hy
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem centralizer_r3eD0_eq :
    (Subgroup.centralizer (r3eD0 : Set J) : Set J) = {1, lyz, lyf, lyz * lyf} := by
  ext x
  constructor
  · intro hx
    rcases mem_centralizer_r3eD0 hx with h | h | h | h <;> simp [h]
  · intro hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (Subgroup.centralizer _).one_mem
    · exact lyz_mem_centralizer_r3eD0
    · exact lyf_mem_centralizer_r3eD0
    · exact (Subgroup.centralizer _).mul_mem lyz_mem_centralizer_r3eD0 lyf_mem_centralizer_r3eD0

theorem centralizer_r3eD0_eq_closure :
    Subgroup.centralizer (r3eD0 : Set J) = Subgroup.closure {lyz, lyf} := by
  apply le_antisymm
  · intro x hx
    rcases mem_centralizer_r3eD0 hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact lyz_mem_centralizer_r3eD0
    · exact lyf_mem_centralizer_r3eD0

private theorem lyz_ne_one : lyz ≠ 1 := by
  obtain ⟨-, -, -, hord, -⟩ := centralizer_double_cover
  intro h
  rw [h, orderOf_one] at hord
  exact absurd hord (by norm_num)


theorem involution_intersection_centralizer_and_filters :
    r3eFusion = lyf ∧ orderOf lyf = 2 ∧ lyf ≠ 1 ∧ lyf ≠ lyz ∧ ⁅lyz, lyf⁆ = 1 ∧
    r3eG * lyz * r3eG⁻¹ = lyf ∧
    r3eD0 ≤ lyC ⊓ lyC.map (MulAut.conj r3eG).toMonoidHom ∧
    Subgroup.centralizer (r3eD0 : Set J) = Subgroup.closure {lyz, lyf} ∧
    (Subgroup.centralizer (r3eD0 : Set J) : Set J) = {1, lyz, lyf, lyz * lyf} ∧
    ∀ δ ∈ ({1, lyz, lyf, lyz * lyf} : Set J),
      (r3eC * δ * r3eG) ^ 18 = 1 ↔ δ = 1 ∨ δ = lyz * lyf := by
  refine ⟨r3eFusion_eq, orderOf_lyf, lyf_ne_one, lyf_ne_lyz,
    (by exact commutatorElement_eq_one_iff_mul_comm.2 lyz_mul_lyf), r3eG_conj_lyz,
    (by exact r3eD0_le), (by exact centralizer_r3eD0_eq_closure), (by exact centralizer_r3eD0_eq),
    ?_⟩
  intro δ hδ
  rcases hδ with rfl | rfl | rfl | rfl
  · exact ⟨fun _ => Or.inl rfl, fun _ => r3e_pow_one⟩
  · refine ⟨fun h => absurd h r3e_pow_z, fun h => ?_⟩
    rcases h with h | h
    · exact absurd h lyz_ne_one
    · exact absurd (by simpa using h) lyf_ne_one
  · refine ⟨fun h => absurd h r3e_pow_f, fun h => ?_⟩
    rcases h with h | h
    · exact absurd h lyf_ne_one
    · exact absurd (by simpa using h) lyz_ne_one
  · exact ⟨fun _ => Or.inr rfl, fun _ => r3e_pow_zf⟩

end CFSG.Sporadic.LySchreier
