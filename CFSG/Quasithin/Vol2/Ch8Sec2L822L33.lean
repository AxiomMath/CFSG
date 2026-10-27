module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB9
public import CFSG.Quasithin.Vol2.Ch3E213MOLB2
public import CFSG.Quasithin.Vol2.Ch8Sec2L822A
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Vol2.E2SevenKGAS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

theorem false_of_normal_l33
    {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    (ι : SL(3, GaloisField 3 1) ≃* K) (hC : Subgroup.centralizer (K : Set X) = ⊥)
    {V : Subgroup X} (hV2 : ∀ v ∈ V, v * v = 1) (hVK : ¬ V ≤ K)
    (hVz : V ⊓ K ≤ Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X))
    (hVn : Subgroup.centralizer
      ({(ι (Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num)) : X)} : Set X) ≤
      Subgroup.normalizer (V : Set X)) : False := by
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) Ch3E213M.OLB.two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  have hz₀2 : z₀ * z₀ = 1 := by
    have h1 := pow_orderOf_eq_one z₀
    rw [hcl.orderOf_eq_two, pow_two] at h1
    exact h1
  have hz₀1 : z₀ ≠ 1 := fun h => by
    have h1 : orderOf z₀ = 2 := hcl.orderOf_eq_two
    rw [h, orderOf_one] at h1
    omega
  have hιmul : ∀ x y : SL(3, GaloisField 3 1), ((ι (x * y) : K) : X) = (ι x : X) * (ι y : X) :=
    fun x y => by rw [map_mul, Subgroup.coe_mul]
  have hιinj : ∀ x y : SL(3, GaloisField 3 1), ((ι x : K) : X) = (ι y : X) → x = y :=
    fun x y h => ι.injective (Subtype.ext h)
  set z : X := (ι z₀ : X) with hzdef
  have hz2 : z * z = 1 := by rw [hzdef, ← hιmul, hz₀2, map_one, Subgroup.coe_one]
  have hz1 : z ≠ 1 := fun h => hz₀1 (hιinj _ _ (by rw [← hzdef, h, map_one, Subgroup.coe_one]))
  set P := V ⊓ K with hPdef
  have hP : IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hV2 _ x.2.1)⟩
  have hPn : Subgroup.centralizer ({z} : Set X) ≤ Subgroup.normalizer (P : Set X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.mp (hVn hc) w
    have h2 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer_of_normal (H := K) (Subgroup.mem_top c)) w
    exact ⟨fun hw => ⟨h1.mp hw.1, h2.mp hw.2⟩, fun hw => ⟨h1.mpr hw.1, h2.mpr hw.2⟩⟩
  have hPK : ∀ w ∈ P, w = 1 ∨ w = z := by
    intro w hw
    have hιx : ((ι (ι.symm ⟨w, hw.2⟩) : K) : X) = w := by rw [MulEquiv.apply_symm_apply]
    have hx2 : ι.symm ⟨w, hw.2⟩ * ι.symm ⟨w, hw.2⟩ = 1 :=
      hιinj _ _ (by rw [hιmul, hιx, hV2 w hw.1, map_one, Subgroup.coe_one])
    rcases Ch3E213M.OLB.eq_one_or_eq_rootInv ι hP hVz hPn (by rw [hιx]; exact hw) hx2 with h | h
    · left
      rw [← hιx, h, map_one, Subgroup.coe_one]
    · right
      rw [← hιx, h]
  obtain ⟨t, htV, htK⟩ : ∃ t ∈ V, t ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hVK hcon
  have ht2 := hV2 t htV
  have hcomm : ∀ h ∈ K, h ∈ Subgroup.centralizer ({z} : Set X) →
      h * t * h⁻¹ * t⁻¹ = 1 ∨ h * t * h⁻¹ * t⁻¹ = z := by
    intro h hhK hhC
    refine hPK _ ⟨?_, ?_⟩
    · exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVn hhC) t).mp htV) (V.inv_mem htV)
    · have h1 : t * h⁻¹ * t⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ (K.inv_mem hhK) t
      have h2 := K.mul_mem hhK h1
      simpa [mul_assoc] using h2
  have htz : t * z = z * t := by
    have hzC : z ∈ Subgroup.centralizer ({z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rcases hcomm z (ι z₀).2 hzC with h | h
    · have h1 : z * t * z⁻¹ = t := mul_inv_eq_one.mp h
      calc t * z = z * t * z⁻¹ * z := by rw [h1]
        _ = z * t := by group
    · exfalso
      apply hz1
      have h1 : t * z⁻¹ * t⁻¹ = 1 := by
        have := congrArg (z⁻¹ * ·) h
        simpa [mul_assoc] using this
      have h2 : z⁻¹ = 1 := by
        have := congrArg (t⁻¹ * · * t) h1
        simpa [mul_assoc] using this
      exact inv_eq_one.mp h2
  have hyA : ∀ A : SL(2, GaloisField 3 1), A * A * A = 1 →
      t * (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A) : X) =
        (ι (WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A) : X) * t := by
    intro A hA3
    set h₀ := WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) A with hh₀
    have hh₀z : h₀ * z₀ = z₀ * h₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcl.le_centralizer ⟨A, rfl⟩)
    have hzh : z * (ι h₀ : X) = (ι h₀ : X) * z := by
      rw [hzdef, ← hιmul, ← hιmul, hh₀z]
    have hh3 : (ι h₀ : X) * (ι h₀ : X) * (ι h₀ : X) = 1 := by
      rw [← hιmul, ← hιmul, hh₀, ← map_mul, ← map_mul, hA3, map_one, map_one,
        Subgroup.coe_one]
    have hhC : (ι h₀ : X) ∈ Subgroup.centralizer ({z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzh.symm
    exact Ch3E213M.OLB.commute_of_comm_mem hz1 hz2 hzh hh3 (hcomm _ (ι h₀).2 hhC)
  set A₁ : SL(2, GaloisField 3 1) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hA₁
  set A₂ : SL(2, GaloisField 3 1) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ with hA₂
  have cA₁ : (A₁ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 1; 0, 1] := rfl
  have cA₂ : (A₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = !![1, 0; 1, 1] := rfl
  have hA₁3 : A₁ * A₁ * A₁ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cA₁]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination Ch3E213M.OLB.three_eq_zero_gf3
  have hA₂3 : A₂ * A₂ * A₂ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cA₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination Ch3E213M.OLB.three_eq_zero_gf3
  exact Ch3E213M.OLB.false_of_fix ι hC htK ht2 htz cA₁ cA₂ (hyA _ hA₁3) (hyA _ hA₂3)

theorem res822L33_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) : Res822L33 := by
  intro G _ _ T L I hyp _ _ hc hcase H hH ⟨hL33, hVK⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hcase
  obtain ⟨hmin, -, -, hHMN⟩ := setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hVM : fsuV T I ≤ H ⊓ fsuM T L :=
    le_inf (hVT.trans hH.1.1) (hVT.trans (le_normalizer_conjClosure L T))
  set M := H ⊓ fsuM T L with hM
  have : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hminX := E2P.minParabolic_star hmin
  have hkerX := E2P.kerIn_star M H
  set K := oTwoUpper (⊤ : Subgroup (E2.StarQuot M H)) with hK
  have hKn : K.Normal := ⟨fun k hk g => (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_oTwoUpper ⊤ (Subgroup.mem_top g)) k).mp hk⟩
  have hVsN : E2.star M H M ≤
      Subgroup.normalizer (E2.star M H (fsuV T I) : Set (E2.StarQuot M H)) := by
    refine le_trans ?_ (Subgroup.le_normalizer_map _)
    refine Subgroup.map_mono fun m hm => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hHMN (Subgroup.mem_subgroupOf.mp hm)) n
  have hVs2 : ∀ v ∈ E2.star M H (fsuV T I), v * v = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
      exact hV.2 _ (Subgroup.mem_subgroupOf.mp hv))
    rw [this, map_one]
  have hVsp : IsPGroup 2 (E2.star M H (fsuV T I)) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hVs2 _ x.2)⟩
  have hVsM : E2.star M H (fsuV T I) ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hVM)
  have hVsT : E2.star M H (fsuV T I) ≤ E2.star M H T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVsM hVsN hVsp).trans
      (E2.pCoreOf_le_of_minParabolic hminX)
  obtain ⟨ι₀⟩ := Ch3E213M.OLB.exists_equiv_sl3 hL33
  have hZ : Subgroup.center SL(3, GaloisField 3 1) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 3) (by norm_num)
      (GaloisField 3 1)
    have h3 : Nat.gcd 3 (Nat.card (GaloisField 3 1) - 1) = 1 := by
      rw [Ch3E213M.OLB.card_gf3]
      norm_num
    rw [h3] at h
    exact Nat.dvd_one.mp h
  have hC : Subgroup.centralizer (K : Set (E2.StarQuot M H)) = ⊥ := by
    set C := Subgroup.centralizer (K : Set (E2.StarQuot M H)) with hCdef
    have hCK : ∀ c ∈ C, c ∈ K → c = 1 := by
      intro c hc hcK
      have h1 : ι₀.symm ⟨c, hcK⟩ ∈ Subgroup.center SL(3, GaloisField 3 1) := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply ι₀.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact Subgroup.mem_centralizer_iff.mp hc _ (ι₀ y).2
      rw [hZ, Subgroup.mem_bot] at h1
      have h2 := congrArg (fun k => ((ι₀ k : K) : E2.StarQuot M H)) h1
      simpa using h2
    have hC2 : IsPGroup 2 C := by
      intro c
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup (E2.StarQuot M H))
        (Subgroup.mem_top (c : E2.StarQuot M H))
      exact ⟨k, Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hCK _ (C.pow_mem c.2 _) hk)⟩
    have hCn : (⊤ : Subgroup (E2.StarQuot M H)) ≤ Subgroup.normalizer (C : Set _) :=
      fun g _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)
    have h1 : C ≤ pCoreOf 2 ⊤ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hCn hC2
    rw [eq_bot_iff, ← hkerX]
    exact h1.trans hminX.pCoreOf_le_kerIn
  have hS : QuasithinUnique.IsSylowTwoOf (E2.star M H T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hminX.isSylow le_top
      (fun g _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top g))
  let SK : Sylow 2 ↥K := IsPGroup.toSylow (hS.2.1.comap_subtype) hS.2.2
  have hSK : (SK : Subgroup ↥K) = (E2.star M H T ⊓ K).subgroupOf K := rfl
  obtain ⟨g, hg⟩ := Ch3E213M.OLB.exists_zOf_sl3 ι₀ SK
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  set ι : SL(3, GaloisField 3 1) ≃* K := (MulAut.conj g).trans ι₀ with hι
  have hιz : ι z₀ = ι₀ (g * z₀ * g⁻¹) := rfl
  set z : E2.StarQuot M H := (ι z₀ : E2.StarQuot M H) with hzdef
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) Ch3E213M.OLB.two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  have hz₀2 : z₀ * z₀ = 1 := by
    have h1 := pow_orderOf_eq_one z₀
    rw [hcl.orderOf_eq_two, pow_two] at h1
    exact h1
  have hz₀1 : z₀ ≠ 1 := fun h => by
    have h1 : orderOf z₀ = 2 := hcl.orderOf_eq_two
    rw [h, orderOf_one] at h1
    omega
  have hz1 : z ≠ 1 := fun h => hz₀1 (ι.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hz2 : z * z = 1 := by
    rw [hzdef, ← Subgroup.coe_mul, ← map_mul, hz₀2, map_one, Subgroup.coe_one]
  have hzZ : (ι z₀ : K) ∈ E2P.zOf (SK : Subgroup ↥K) := by
    rw [hg, ← hιz]
    exact Subgroup.mem_zpowers _
  have hVz : E2.star M H (fsuV T I) ⊓ K ≤
      Subgroup.centralizer ({z} : Set (E2.StarQuot M H)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwS : (⟨w, hw.2⟩ : ↥K) ∈ (SK : Subgroup ↥K) :=
      Subgroup.mem_subgroupOf.mpr ⟨hVsT hw.1, hw.2⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hzZ.2 _ hwS
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    exact h2
  have hTz : E2.star M H T ≤ Subgroup.centralizer ({z} : Set (E2.StarQuot M H)) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzK : z ∈ K := (ι z₀).2
    have htzK : t * z * t⁻¹ ∈ K := hKn.conj_mem _ hzK t
    have hzS : z ∈ E2.star M H T ⊓ K := Subgroup.mem_subgroupOf.mp hzZ.1
    have htzS : t * z * t⁻¹ ∈ E2.star M H T ⊓ K :=
      Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem ht hzS.1) (inv_mem ht), htzK⟩
    have hmemZ : (⟨t * z * t⁻¹, htzK⟩ : ↥K) ∈ E2P.zOf (SK : Subgroup ↥K) := by
      refine ⟨Subgroup.mem_subgroupOf.mpr htzS, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro s hs
      have hs0 : (s : E2.StarQuot M H) ∈ E2.star M H T ⊓ K := Subgroup.mem_subgroupOf.mp hs
      have hs' : t⁻¹ * (s : E2.StarQuot M H) * t ∈ E2.star M H T ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem ht) hs0.1) ht, ?_⟩
        have := hKn.conj_mem _ hs0.2 t⁻¹
        simpa using this
      have hs'K : (⟨t⁻¹ * (s : E2.StarQuot M H) * t, hs'.2⟩ : ↥K) ∈ (SK : Subgroup ↥K) :=
        Subgroup.mem_subgroupOf.mpr hs'
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hzZ.2 _ hs'K)
      simp only [Subgroup.coe_mul] at h1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (s : E2.StarQuot M H) * (t * z * t⁻¹)
          = t * ((t⁻¹ * (s : E2.StarQuot M H) * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * (s : E2.StarQuot M H) * t)) * t⁻¹ := by rw [h1]
        _ = t * z * t⁻¹ * (s : E2.StarQuot M H) := by group
    rw [hg, ← hιz, Subgroup.mem_zpowers_iff] at hmemZ
    obtain ⟨k, hk⟩ := hmemZ
    have hk' : z ^ k = t * z * t⁻¹ := by
      have := congrArg Subtype.val hk
      simpa using this
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    rw [← zpow_mod_orderOf, hzo, Nat.cast_ofNat] at hk'
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · exfalso
      rw [h0, zpow_zero] at hk'
      apply hz1
      have := congrArg (fun y => t⁻¹ * y * t) hk'
      simpa [mul_assoc] using this.symm
    · rw [h0, zpow_one] at hk'
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [← hk']
  have hlt : Subgroup.centralizer ({z} : Set (E2.StarQuot M H)) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hz1 ?_
    have hzC : z ∈ Subgroup.centralizer (K : Set (E2.StarQuot M H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top k)
    rw [hC, Subgroup.mem_bot] at hzC
    exact hzC
  have hVn : Subgroup.centralizer ({z} : Set (E2.StarQuot M H)) ≤
      Subgroup.normalizer (E2.star M H (fsuV T I) : Set (E2.StarQuot M H)) :=
    (hminX.le_of_lt hTz hlt).trans hVsN
  exact false_of_normal_l33 ι hC hVs2 hVK hVz hVn

end CFSG.Quasithin.H13
