module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Std
public import CFSG.Permutation.FinPackPair6

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Fr6K

open CFSG.Permutation.FinPack Equiv J6

@[expose] def e1K : S6 := swap 0 1

@[expose] def ppK : S6 := swap 2 3

@[expose] def qqK : S6 := swap 4 5

@[expose] def v1K : S6 := ppK * qqK

@[expose] def v2K : S6 := swap 2 4 * swap 3 5

@[expose] def v3K : S6 := swap 2 5 * swap 3 4

@[expose] def c0K : S6 := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)

@[expose] def T1K : Finset S6 := {1, e1K, v1K, v2K, v3K, e1K * v1K, e1K * v2K, e1K * v3K}

@[expose] def V1K : Finset S6 :=
  {1, e1K, ppK, qqK, e1K * ppK, e1K * qqK, ppK * qqK, e1K * ppK * qqK}

@[expose] def RK : Finset S6 := Finset.univ.filter fun σ =>
  ({σ 0, σ 1} : Finset (Fin 6)) = {0, 1} ∧
    (({σ 2, σ 3} : Finset (Fin 6)) = {2, 3} ∨ ({σ 2, σ 3} : Finset (Fin 6)) = {4, 5})

@[expose] def NT1K : Finset S6 := Finset.univ.filter fun σ => ∀ s ∈ T1K, σ * s * σ⁻¹ ∈ T1K

@[expose] def NV1K : Finset S6 := Finset.univ.filter fun σ => ∀ s ∈ V1K, σ * s * σ⁻¹ ∈ V1K

@[expose] def orbitBK : Finset S6 := {c₁, c₁⁻¹, c₂, c₂⁻¹}

@[expose] def orbitCK : Finset S6 := {c₁ * c₂, (c₁ * c₂)⁻¹, c₁ * c₂⁻¹, c₁⁻¹ * c₂}

@[expose] def convVTK : Finset S6 := {1, c0K, c0K⁻¹, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5}

@[expose] def convTVK : Finset S6 := {1, swap 3 4, swap 3 5}

@[expose] def T1P : List ℕ := [
    92573999051280, 92573747393025, 76016899138320, 55336630375440, 38779530462480, 76016647480065,
    55336378717185, 38779278804225]

@[expose] def V1P : List ℕ := [
    92573999051280, 92573747393025, 92509574538000, 76081323651600, 92509322879745, 76081071993345,
    76016899138320, 76016647480065]

@[expose] def RP : List ℕ := [
    92573999051280, 76081323651600, 92509574538000, 76016899138320, 55336630375440, 55272204882960,
    38843955954960, 38779530462480, 92573747393025, 76081071993345, 92509322879745, 76016647480065,
    55336378717185, 55271953224705, 38843704296705, 38779278804225]

@[expose] def NT1P : List ℕ := [
    92573999051280, 76081323651600, 91543206838800, 74019738305040, 58557856961040, 57527063826960,
    92509574538000, 76016899138320, 91414357754640, 73826463728400, 58429007876880, 57333789250320,
    90447990170640, 72924521636880, 90383565599760, 72795671573520, 55336630375440, 55272204882960,
    40969965872400, 39939172738320, 40905541301520, 39810322674960, 38843955954960, 38779530462480,
    92573747393025, 76081071993345, 91542955180545, 74019486646785, 58557605302785, 57526812168705,
    92509322879745, 76016647480065, 91414106096385, 73826212070145, 58428756218625, 57333537592065,
    90447738512385, 72924269978625, 90383313941505, 72795419915265, 55336378717185, 55271953224705,
    40969714214145, 39938921080065, 40905289643265, 39810071016705, 38843704296705, 38779278804225]

@[expose] def NV1P : List ℕ := [
    92573999051280, 76081323651600, 92509574538000, 76016899138320, 55336630375440, 55272204882960,
    38843955954960, 38779530462480, 92573747393025, 76081071993345, 92509322879745, 76016647480065,
    55336378717185, 55271953224705, 38843704296705, 38779278804225, 92428540579890, 75935865180210,
    92428288917810, 75935613518130, 55045711221810, 55045458580530, 38553036801330, 38552784160050,
    92364116070435, 75871440670755, 92363864408355, 75871189008675, 54981286712355, 54981034071075,
    38488612291875, 38488359650595, 17953805439060, 17889379946580, 17953553776980, 17889128284500,
    17808344756820, 17808092115540, 17743920243540, 17743667602260, 1461131022405, 1396705529925,
    1460879360325, 1396453867845, 1315670340165, 1315417698885, 1251245826885, 1250993185605]

@[expose] def EP : List ℕ := [
    92573999051280, 74019738305040, 58557856961040, 92569469202465, 74015208456225, 58553327112225,
    92565694329090, 74011433582850, 58549552238850]

@[expose] def N6P : List ℕ := [
    92573999051280, 76081323651600, 91543206838800, 74019738305040, 58557856961040, 57527063826960,
    92569972519200, 76077297119520, 91539180306720, 74015711772960, 58553830428960, 57523037294880,
    92573747393025, 76081071993345, 91542955180545, 74019486646785, 58557605302785, 57526812168705,
    92569469202465, 76076793802785, 91538676989985, 74015208456225, 58553327112225, 57522533978145,
    92565694329090, 76073018929410, 91534902116610, 74011433582850, 58549552238850, 57518759104770,
    92565442670610, 76072767270930, 91534650458130, 74011181924370, 58549300580370, 57518507446290,
    36306484790595, 36302457275715, 36306233070915, 36301952914755, 36298178962755, 36297926321475,
    19813810373715, 19809782858835, 19813558654035, 19809278497875, 19805504545875, 19805251904595,
    35275692639540, 35271665124660, 35275440919860, 35271160763700, 35267386811700, 35267134170420,
    17752226071380, 17748198556500, 17751974351700, 17747694195540, 17743920243540, 17743667602260,
    2290343806005, 2286316291125, 2290092086325, 2285811930165, 2282037978165, 2281785336885,
    1259551654725, 1255524139845, 1259299935045, 1255019778885, 1251245826885, 1250993185605]

@[expose] def orbBP : List ℕ := [92569469202465, 92565694329090, 74019738305040, 58557856961040]

@[expose] def orbCP : List ℕ := [74015208456225, 58549552238850, 58553327112225, 74011433582850]

@[expose] def cVTP : List ℕ :=
  [92573999051280, 55045711221810, 17953805439060, 92428540579890, 17808344756820]

@[expose] def cTVP : List ℕ := [92573999051280, 91543206838800, 57527063826960]

@[expose] def gTP : List ℕ := [92573999051280, 76016647480065, 55336378717185, 38779278804225]

@[expose] def g1eP : List ℕ := [92573999051280, 92573747393025]

@[expose] def g1pP : List ℕ := [92573999051280, 92509574538000]

@[expose] def g1qP : List ℕ := [92573999051280, 76081323651600]

@[expose] def cyc1P : List ℕ := [92573999051280, 92569469202465, 92565694329090]

@[expose] def cyc2P : List ℕ := [92573999051280, 74019738305040, 58557856961040]

@[expose] def cycdP : List ℕ := [92573999051280, 74015208456225, 58549552238850]

theorem pc6_one : pc6 (1 : S6) = 92573999051280 := by decide +kernel

theorem pc6_e1 : pc6 e1K = 92573747393025 := by decide +kernel

theorem pc6_epq : pc6 (e1K * ppK * qqK) = 76016647480065 := by decide +kernel

theorem pc6_c0 : pc6 c0K = 55045711221810 := by decide +kernel

theorem pc6_c1 : pc6 c₁ = 92569469202465 := by decide +kernel

theorem pc6_c1i : pc6 c₁⁻¹ = 92565694329090 := by decide +kernel

theorem pc6_c2 : pc6 c₂ = 74019738305040 := by decide +kernel

theorem pc6_c2i : pc6 c₂⁻¹ = 58557856961040 := by decide +kernel

theorem pc6_d :pc6 (c₁ * c₂) = 74015208456225 := by decide +kernel

theorem pc6_di : pc6 (c₁ * c₂)⁻¹ = 58549552238850 := by decide +kernel

theorem T1_img : T1K.image pc6 = T1P.toFinset := by decide +kernel

theorem V1_img : V1K.image pc6 = V1P.toFinset := by decide +kernel

theorem E_img : Efin.image pc6 = EP.toFinset := by decide +kernel

theorem orbB_img : orbitBK.image pc6 = orbBP.toFinset := by decide +kernel

theorem orbC_img : orbitCK.image pc6 = orbCP.toFinset := by decide +kernel

theorem cVT_img : convVTK.image pc6 = cVTP.toFinset := by decide +kernel

theorem cTV_img : convTVK.image pc6 = cTVP.toFinset := by decide +kernel

theorem gT_img :
    ({1, e1K * v1K, e1K * v2K, e1K * v3K} : Finset S6).image pc6 = gTP.toFinset := by
  decide +kernel

theorem g1e_img : ({1, e1K} : Finset S6).image pc6 = g1eP.toFinset := by decide +kernel

theorem g1p_img : ({1, ppK} : Finset S6).image pc6 = g1pP.toFinset := by decide +kernel

theorem g1q_img : ({1, qqK} : Finset S6).image pc6 = g1qP.toFinset := by decide +kernel

theorem cyc1_img : ({1, c₁, c₁⁻¹} : Finset S6).image pc6 = cyc1P.toFinset := by decide +kernel

theorem cyc2_img : ({1, c₂, c₂⁻¹} : Finset S6).image pc6 = cyc2P.toFinset := by decide +kernel

theorem cycd_img :
    ({1, c₁ * c₂, (c₁ * c₂)⁻¹} : Finset S6).image pc6 = cycdP.toFinset := by
  decide +kernel

theorem T1_code : ∀ σ, σ ∈ T1K ↔ memK (pc6 σ) T1P = true := code_of_image T1_img

theorem V1_code : ∀ σ, σ ∈ V1K ↔ memK (pc6 σ) V1P = true := code_of_image V1_img

theorem E_code : ∀ σ, σ ∈ Efin ↔ memK (pc6 σ) EP = true := code_of_image E_img

theorem orbB_code : ∀ σ, σ ∈ orbitBK ↔ memK (pc6 σ) orbBP = true := code_of_image orbB_img

theorem orbC_code : ∀ σ, σ ∈ orbitCK ↔ memK (pc6 σ) orbCP = true := code_of_image orbC_img

theorem cyc1_code : ∀ σ, σ ∈ ({1, c₁, c₁⁻¹} : Finset S6) ↔ memK (pc6 σ) cyc1P = true :=
  code_of_image cyc1_img

theorem cyc2_code : ∀ σ, σ ∈ ({1, c₂, c₂⁻¹} : Finset S6) ↔ memK (pc6 σ) cyc2P = true :=
  code_of_image cyc2_img

theorem cycd_code :
    ∀ σ, σ ∈ ({1, c₁ * c₂, (c₁ * c₂)⁻¹} : Finset S6) ↔ memK (pc6 σ) cycdP = true :=
  code_of_image cycd_img

@[expose] def pB (a b x y : ℕ) : Bool :=
  (Nat.beq a x && Nat.beq b y) || (Nat.beq a y && Nat.beq b x)

theorem pair01 : ∀ a b : Fin 6, ({a, b} : Finset (Fin 6)) = {0, 1} ↔ pB a b 0 1 = true := by
  decide +kernel

theorem pair23 : ∀ a b : Fin 6, ({a, b} : Finset (Fin 6)) = {2, 3} ↔ pB a b 2 3 = true := by
  decide +kernel

theorem pair45 : ∀ a b : Fin 6, ({a, b} : Finset (Fin 6)) = {4, 5} ↔ pB a b 4 5 = true := by
  decide +kernel

@[expose] def rT (p : ℕ) : Bool :=
  pB (rd (lo6 p) 0) (rd (lo6 p) 1) 0 1 &&
    (pB (rd (lo6 p) 2) (rd (lo6 p) 3) 2 3 || pB (rd (lo6 p) 2) (rd (lo6 p) 3) 4 5)

theorem R_twin (σ : S6) : (({σ 0, σ 1} : Finset (Fin 6)) = {0, 1} ∧
    (({σ 2, σ 3} : Finset (Fin 6)) = {2, 3} ∨ ({σ 2, σ 3} : Finset (Fin 6)) = {4, 5})) ↔
      rT (pc6 σ) = true := by
  have h0 : rd (enc σ) 0 = (σ 0 : ℕ) := rd_enc (by norm_num) σ 0
  have h1 : rd (enc σ) 1 = (σ 1 : ℕ) := rd_enc (by norm_num) σ 1
  have h2 : rd (enc σ) 2 = (σ 2 : ℕ) := rd_enc (by norm_num) σ 2
  have h3 : rd (enc σ) 3 = (σ 3 : ℕ) := rd_enc (by norm_num) σ 3
  unfold rT
  rw [lo6_pc6, h0, h1, h2, h3, Bool.and_eq_true, Bool.or_eq_true, ← pair01, ← pair23, ← pair45]

theorem R_pin : allK (fun p => rT p == memK p RP) allCodes6 = true := by decide +kernel

theorem R_code (σ : S6) : σ ∈ RK ↔ memK (pc6 σ) RP = true := by
  unfold RK
  rw [Finset.mem_filter]
  exact (and_iff_right (Finset.mem_univ σ)).trans (code_of_pin R_twin R_pin σ)

@[expose] noncomputable def nT1 (p : ℕ) : Bool :=
  allK (fun q => memK (mulP6 (mulP6 p q) (invP6 p)) T1P) T1P

@[expose] noncomputable def nV1 (p : ℕ) : Bool :=
  allK (fun q => memK (mulP6 (mulP6 p q) (invP6 p)) V1P) V1P

@[expose] noncomputable def nE (p : ℕ) : Bool :=
  allK (fun q => memK (mulP6 (mulP6 p q) (invP6 p)) EP) EP

theorem NT1_pin : allK (fun p => nT1 p == memK p NT1P) allCodes6 = true := by decide +kernel

theorem NV1_pin : allK (fun p => nV1 p == memK p NV1P) allCodes6 = true := by decide +kernel

theorem N6_pin : allK (fun p => nE p == memK p N6P) allCodes6 = true := by decide +kernel

theorem NT1_code (σ : S6) : σ ∈ NT1K ↔ memK (pc6 σ) NT1P = true := by
  unfold NT1K
  rw [Finset.mem_filter]
  exact (and_iff_right (Finset.mem_univ σ)).trans
    (code_of_pin (t := nT1) (fun τ => norm_iff T1_img T1_code τ) NT1_pin σ)

theorem NV1_code (σ : S6) : σ ∈ NV1K ↔ memK (pc6 σ) NV1P = true := by
  unfold NV1K
  rw [Finset.mem_filter]
  exact (and_iff_right (Finset.mem_univ σ)).trans
    (code_of_pin (t := nV1) (fun τ => norm_iff V1_img V1_code τ) NV1_pin σ)

theorem N6_code (σ : S6) : σ ∈ N6 ↔ memK (pc6 σ) N6P = true := by
  unfold N6
  rw [Finset.mem_filter]
  exact (and_iff_right (Finset.mem_univ σ)).trans
    (code_of_pin (t := nE) (fun τ => norm_iff E_img E_code τ) N6_pin σ)

theorem Rfin_card : RK.card = 16 :=
  card_of_image (image_of_code R_code (by decide +kernel)) (by decide +kernel)

theorem NT1_card : NT1K.card = 48 :=
  card_of_image (image_of_code NT1_code (by decide +kernel)) (by decide +kernel)

theorem NV1_card : NV1K.card = 48 :=
  card_of_image (image_of_code NV1_code (by decide +kernel)) (by decide +kernel)

theorem T1fin_mul : ∀ a ∈ T1K, ∀ b ∈ T1K, a * b ∈ T1K :=
  mul_of_check T1_code T1_code T1_code (by decide +kernel)

theorem V1fin_mul : ∀ a ∈ V1K, ∀ b ∈ V1K, a * b ∈ V1K :=
  mul_of_check V1_code V1_code V1_code (by decide +kernel)

theorem Rfin_mul : ∀ a ∈ RK, ∀ b ∈ RK, a * b ∈ RK :=
  mul_of_check R_code R_code R_code (by decide +kernel)

theorem T1fin_inv : ∀ a ∈ T1K, a⁻¹ ∈ T1K := inv_of_check T1_code T1_code (by decide +kernel)

theorem V1fin_inv : ∀ a ∈ V1K, a⁻¹ ∈ V1K := inv_of_check V1_code V1_code (by decide +kernel)

theorem Rfin_inv : ∀ a ∈ RK, a⁻¹ ∈ RK := inv_of_check R_code R_code (by decide +kernel)

theorem T1fin_subset_R : T1K ⊆ RK := sub_of_check T1_code R_code (by decide +kernel)

theorem V1fin_subset_R : V1K ⊆ RK := sub_of_check V1_code R_code (by decide +kernel)

theorem T1fin_sq : ∀ s ∈ T1K, s * s = 1 := sq_of_check T1_code pc6_one (by decide +kernel)

theorem V1fin_sq : ∀ s ∈ V1K, s * s = 1 := sq_of_check V1_code pc6_one (by decide +kernel)

theorem T1fin_comm : ∀ a ∈ T1K, ∀ b ∈ T1K, a * b = b * a :=
  comm_of_check T1_code T1_code (by decide +kernel)

theorem V1fin_comm : ∀ a ∈ V1K, ∀ b ∈ V1K, a * b = b * a :=
  comm_of_check V1_code V1_code (by decide +kernel)

theorem c2_norm_T1 : ∀ s ∈ T1K, c₂ * s * c₂⁻¹ ∈ T1K :=
  norm_of_check T1_code T1_code pc6_c2 (by decide +kernel)

theorem c0_norm_V1 : ∀ s ∈ V1K, c0K * s * c0K⁻¹ ∈ V1K :=
  norm_of_check V1_code V1_code pc6_c0 (by decide +kernel)

theorem T1_cen_c2 : ∀ s ∈ T1K, s * c₂ = c₂ * s → s = 1 ∨ s = e1K :=
  cen_of_check T1_code pc6_c2 pc6_one pc6_e1 (by decide +kernel)

theorem V1_cen_c0 : ∀ s ∈ V1K, s * c0K = c0K * s → s = 1 ∨ s = e1K * ppK * qqK :=
  cen_of_check V1_code pc6_c0 pc6_one pc6_epq (by decide +kernel)

theorem T1_gen : ∀ s ∈ T1K, ∃ x ∈ ({1, e1K * v1K, e1K * v2K, e1K * v3K} : Finset S6),
    ∃ y ∈ ({1, e1K * v1K, e1K * v2K, e1K * v3K} : Finset S6),
      ∃ z ∈ ({1, e1K * v1K, e1K * v2K, e1K * v3K} : Finset S6), s = x * y * z :=
  gen_of_check T1_code gT_img gT_img gT_img (by decide +kernel)

theorem V1_gen : ∀ s ∈ V1K, ∃ x ∈ ({1, e1K} : Finset S6), ∃ y ∈ ({1, ppK} : Finset S6),
    ∃ z ∈ ({1, qqK} : Finset S6), s = x * y * z :=
  gen_of_check V1_code g1e_img g1p_img g1q_img (by decide +kernel)

theorem V1_conj_T1 : ∀ r ∈ V1K, ∃ γ ∈ convVTK, γ * r * γ⁻¹ ∈ T1K :=
  conj_of_check V1_code T1_code cVT_img (by decide +kernel)

theorem T1_conj_V1 : ∀ r ∈ T1K, ∃ γ ∈ convTVK, γ * r * γ⁻¹ ∈ V1K :=
  conj_of_check T1_code V1_code cTV_img (by decide +kernel)

theorem R_inv_mem : ∀ r ∈ RK, r * r = 1 → r ∈ T1K ∨ r ∈ V1K :=
  invol_of_check R_code T1_code V1_code pc6_one (by decide +kernel)

theorem noncomm_TV : ∀ x ∈ V1K, x ∉ T1K → ∀ y ∈ T1K, y ∉ V1K → x * y ≠ y * x :=
  noncomm_of_check V1_code T1_code (by decide +kernel)

theorem R_sub_NT1 : RK ⊆ NT1K := sub_of_check R_code NT1_code (by decide +kernel)

theorem R_sub_NV1 : RK ⊆ NV1K := sub_of_check R_code NV1_code (by decide +kernel)

theorem norm_orbits : ∀ σ ∈ N6, σ * c₁ * σ⁻¹ ∈ orbitBK ∧ σ * c₂ * σ⁻¹ ∈ orbitBK ∧
    σ * (c₁ * c₂) * σ⁻¹ ∈ orbitCK := fun σ hσ =>
  ⟨conjBy_of_check N6_code orbB_code pc6_c1 (by decide +kernel) σ hσ,
    conjBy_of_check N6_code orbB_code pc6_c2 (by decide +kernel) σ hσ,
    conjBy_of_check N6_code orbC_code pc6_d (by decide +kernel) σ hσ⟩

theorem orbitB_cyc_c1 : ∀ x ∈ orbitBK, x ∈ ({1, c₁, c₁⁻¹} : Finset S6) → x = c₁ ∨ x = c₁⁻¹ :=
  pick_of_check orbB_code cyc1_code pc6_c1 pc6_c1i (by decide +kernel)

theorem orbitB_cyc_c2 : ∀ x ∈ orbitBK, x ∈ ({1, c₂, c₂⁻¹} : Finset S6) → x = c₂ ∨ x = c₂⁻¹ :=
  pick_of_check orbB_code cyc2_code pc6_c2 pc6_c2i (by decide +kernel)

theorem orbitB_not_cyc_d : ∀ x ∈ orbitBK, x ∉ ({1, c₁ * c₂, (c₁ * c₂)⁻¹} : Finset S6) :=
  notin_of_check orbB_code cycd_code (by decide +kernel)

theorem orbitC_not_cyc_c1 : ∀ x ∈ orbitCK, x ∉ ({1, c₁, c₁⁻¹} : Finset S6) :=
  notin_of_check orbC_code cyc1_code (by decide +kernel)

theorem orbitC_cyc_d : ∀ x ∈ orbitCK, x ∈ ({1, c₁ * c₂, (c₁ * c₂)⁻¹} : Finset S6) →
    x = c₁ * c₂ ∨ x = (c₁ * c₂)⁻¹ :=
  pick_of_check orbC_code cycd_code pc6_d pc6_di (by decide +kernel)

theorem orbitB_ne_one : ∀ x ∈ orbitBK, x ≠ 1 :=
  ne_one_of_check orbB_code pc6_one (by decide +kernel)

theorem orbitC_ne_one : ∀ x ∈ orbitCK, x ≠ 1 :=
  ne_one_of_check orbC_code pc6_one (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec21.FF81.Fr6K
