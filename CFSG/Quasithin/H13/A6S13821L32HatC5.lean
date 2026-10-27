module

public import CFSG.Quasithin.H13.A6S13821L32HatC1
public import CFSG.Quasithin.H13.A6S13821L32HatC4

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace L32HatC5

open CFSG.Quasithin.H13.A6.L32HatC4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem sm_mul {x y : G} (hx : x ∈ NV T V) (hy : y ∈ NV T V) :
    sm T V ((NV T V).mul_mem hx hy) = sm T V hx * sm T V hy :=
  map_mul (secMk (NV T V) (fsuV1 T V)) ⟨x, hx⟩ ⟨y, hy⟩

theorem sm_inv {x : G} (hx : x ∈ NV T V) : sm T V ((NV T V).inv_mem hx) = (sm T V hx)⁻¹ :=
  map_inv (secMk (NV T V) (fsuV1 T V)) ⟨x, hx⟩

theorem sm_congr {x y : G} (hx : x ∈ NV T V) (hy : y ∈ NV T V) (h : x = y) :
    sm T V hx = sm T V hy := by
  subst h
  rfl

theorem sm_conj {a y : G} (ha : a ∈ NV T V) (hy : y ∈ NV T V) :
    sm T V ha * sm T V hy * (sm T V ha)⁻¹ =
      sm T V ((NV T V).mul_mem ((NV T V).mul_mem ha hy) ((NV T V).inv_mem ha)) := by
  rw [sm_mul ((NV T V).mul_mem ha hy) ((NV T V).inv_mem ha), sm_mul ha hy, sm_inv ha]

theorem sm_eq_one_iff {x : G} (hx : x ∈ NV T V) : sm T V hx = 1 ↔ x ∈ fsuV1 T V :=
  secMk_eq_one_iff

theorem sm_eq_one_of_conj_eq {S : Setting4 G T L V} {H : Subgroup G}
    {c : G} (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V)
    {z : G} (hz : z ∈ S.V3) (hzN : z ∈ NV T V) (hczN : c * z * c⁻¹ ∈ NV T V)
    (h : sm T V hczN = sm T V hzN) : z ∈ fsuV1 T V := by
  have h1 := secMk_eq_secMk_iff.mp h
  have h2 : c * z⁻¹ * c⁻¹ * z⁻¹⁻¹ ∈ fsuV1 T V := by
    have e : c * z⁻¹ * c⁻¹ * z⁻¹⁻¹ = (c * z * c⁻¹)⁻¹ * z := by group
    rw [e]
    exact h1
  have hzU : z ∈ conjClosure S.V3 H :=
    Subgroup.subset_closure ⟨1, H.one_mem, z, hz, by simp⟩
  have h3 := hfpf z⁻¹ ((conjClosure S.V3 H).inv_mem hzU) h2
  have := (fsuV1 T V).inv_mem h3
  simpa using this

theorem hC_holds {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hS : S.Hyp138) (hhat : IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    4 ≤ mIdx (conjClosure S.V3 H)
      (centralizerMod (fsuV1 T V) (conjClosure S.V3 H) (pCoreOf 2 (S.L1 ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ⊔ T ≤ H := hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hL1H
  have hXH : S.X13820 ≤ H := S.plusData_X13820.le_L1.trans (le_sup_left.trans hL1H)
  have hRH : pCoreOf 2 (S.L1 ⊔ T) ≤ H := (pCoreOf_le 2 _).trans hL1H
  have hF : HypF91 T V L (fsuV1 T V) S.V3 H := (hS.hF H hH).toHypF91
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  have hV1H : fsuV1 T V ≤ H := hV1V.trans (S.V_le_T.trans hTH)
  have hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G) :=
    H_le_normalizer_X h139 h37 h38 h1334 h13 hS hhat hH hK hKn hP hHK
  obtain ⟨π, hπ, hker, hE0, hA0⟩ :=
    L32HatC3.exists_pi_good h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK
  obtain ⟨c, hcX, hc3, hθ, hfpf, -, -⟩ := S.exists_c_13820a' hS hH hHX
  have hcH : c ∈ H := hXH hcX
  have hX : ∀ x ∈ S.X13820, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    L32HatStep.step21 h139 h37 h38 h1334 hS hhat hH hK hKn hP
  have hUN : conjClosure S.V3 H ≤ NV T V := fun u hu =>
    hF.H_normalizes_V₁ (pCoreOf_le 2 H (hF.conjClosure_Vp_le_pCoreOf hu))
  have hV3U : S.V3 ≤ conjClosure S.V3 H := fun z hz =>
    Subgroup.subset_closure ⟨1, H.one_mem, z, hz, by simp⟩
  have hV3N : S.V3 ≤ NV T V := hV3U.trans hUN
  have hE : IsElemAbelian 2 (UT T V S.V3 H) := hF.isElemAbelian_tilde
  letI : CommGroup ↥(UT T V S.V3 H) := CFSG.Quasithin.commGroupOfElemAbelian hE
  have hsq : ∀ w : ↥(UT T V S.V3 H), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hE.2 w.1 w.2)
  have hK2 : pCoreOf 2 K ≤ pCoreOf 2 H :=
    L32HatC3.le_pCoreOf_of_two ((pCoreOf_le 2 K).trans hKH)
      (hKn.trans (normalizer_le_normalizer_pCoreOf 2 K))
      (fun y hy => L32HatC3.two_pow_of_mem_pCoreOf hy)
  have hσ : ∀ k : ↥K, π k = 1 → ((actU hF).comp (Subgroup.inclusion hKH)) k = 1 := by
    intro k hk
    exact actU_eq_one_of_pCore hF (hK2 ((hker k).mp hk)) (hKH k.2)
  obtain ⟨ρ, hρ⟩ := exists_rhoPi π hπ ((actU hF).comp (Subgroup.inclusion hKH)) hσ
  set cW : MulAut ↥(UT T V S.V3 H) := actU hF ⟨c, hcH⟩ with hcW
  have hcN : c ∈ NV T V := hF.H_normalizes_V₁ hcH
  have hcW_coe : ∀ w : ↥(UT T V S.V3 H),
      ((cW w : ↥(UT T V S.V3 H)) : QV T V) = sm T V hcN * (w : QV T V) * (sm T V hcN)⁻¹ :=
    fun w => coe_actU hF ⟨c, hcH⟩ w
  have hconj : ∀ y : G, ∀ hy : y ∈ NV T V, sm T V hcN * sm T V hy * (sm T V hcN)⁻¹ =
      sm T V ((NV T V).mul_mem ((NV T V).mul_mem hcN hy) ((NV T V).inv_mem hcN)) := by
    intro y hy
    rw [sm_mul ((NV T V).mul_mem hcN hy) ((NV T V).inv_mem hcN), sm_mul hcN hy, sm_inv hcN]
  have hc : ∀ w : ↥(UT T V S.V3 H), w * cW w * cW (cW w) = 1 := by
    intro w
    obtain ⟨x, hxU, hwx⟩ := mem_secImg.mp (show (w : QV T V) ∈
      secImg (NV T V) (fsuV1 T V) (conjClosure S.V3 H) from w.2)
    have hwx' : sm T V x.2 = (w : QV T V) := hwx
    have hcxN : c * (x : G) * c⁻¹ ∈ NV T V := (NV T V).mul_mem ((NV T V).mul_mem hcN x.2) ((NV T V).inv_mem hcN)
    have e1 : ((cW w : ↥(UT T V S.V3 H)) : QV T V) = sm T V hcxN := by
      rw [hcW_coe, ← hwx', hconj (x : G) x.2]
    have e2 : ((cW (cW w) : ↥(UT T V S.V3 H)) : QV T V) =
        sm T V ((NV T V).mul_mem ((NV T V).mul_mem hcN hcxN) ((NV T V).inv_mem hcN)) := by
      rw [hcW_coe, e1, hconj _ hcxN]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_one, e2, e1, ← hwx']
    rw [← sm_mul, ← sm_mul]
    exact (sm_eq_one_iff _).mpr (hθ _ hxU)
  have hV1S3 : fsuV1 T V ≤ S.V3 := S.V1_le_V2.trans S.V2_le_V3
  have hV3s : tildeOf (fsuV1 T V) S.V3 ≤ UT T V S.V3 H := secImg_mono hV3U
  have hcard4 : Nat.card ↥(tildeOf (fsuV1 T V) S.V3) = 4 :=
    card_tilde_V3 hV1S3 hV3N hF.card_V₁ S.card_V3
  obtain ⟨w₁, hw₁⟩ : ∃ w : ↥(tildeOf (fsuV1 T V) S.V3), w ≠ 1 := by
    have h1 : 1 < Nat.card ↥(tildeOf (fsuV1 T V) S.V3) := by rw [hcard4]; norm_num
    haveI := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne 1
  obtain ⟨z₁, hz₁, hz₁w⟩ := mem_secImg.mp (show (w₁ : QV T V) ∈
    secImg (NV T V) (fsuV1 T V) S.V3 from w₁.2)
  set v0 : ↥(UT T V S.V3 H) := ⟨(w₁ : QV T V), hV3s w₁.2⟩ with hv0def
  have hv0_coe : (v0 : QV T V) = (w₁ : QV T V) := rfl
  have hz₁w' : secMk (NV T V) (fsuV1 T V) z₁ = (w₁ : QV T V) := hz₁w
  have hv0ne : v0 ≠ 1 := by
    intro h
    apply hw₁
    exact Subtype.ext (congrArg (fun y : ↥(UT T V S.V3 H) => (y : QV T V)) h)
  have hcLT : c ∈ S.L1 ⊔ T := Subgroup.mem_sup_left (S.plusData_X13820.le_L1 hcX)
  have hcV3 : ∀ z ∈ S.V3, c * z * c⁻¹ ∈ S.V3 := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hF.L₁T_normalizes_Vp hcLT) z).mp hz
  have hcczN : ∀ z : ↥(NV T V), c * (z : G) * c⁻¹ ∈ NV T V := fun z =>
    (NV T V).mul_mem ((NV T V).mul_mem hcN z.2) ((NV T V).inv_mem hcN)
  have hcv0ne1 : cW v0 ≠ 1 := by
    intro h
    apply hv0ne
    have h' : cW v0 = cW 1 := by rw [map_one]; exact h
    exact cW.injective h'
  have hcv0ne : cW v0 ≠ v0 := by
    intro h
    apply hv0ne
    have hq : ((cW v0 : ↥(UT T V S.V3 H)) : QV T V) = (v0 : QV T V) := congrArg Subtype.val h
    rw [hcW_coe, hv0_coe, ← hz₁w'] at hq
    have hq' : sm T V (hcczN z₁) = sm T V z₁.2 := by
      rw [← hconj (z₁ : G) z₁.2]
      exact hq
    have hz1V1 := sm_eq_one_of_conj_eq hfpf hz₁ z₁.2 (hcczN z₁) hq'
    apply Subtype.ext
    rw [hv0_coe, ← hz₁w']
    exact (sm_eq_one_iff _).mpr hz1V1
  set V3s : Subgroup ↥(UT T V S.V3 H) := (tildeOf (fsuV1 T V) S.V3).subgroupOf (UT T V S.V3 H)
    with hV3s_def
  have hV3s_card : Nat.card ↥V3s = 4 := by
    rw [← hcard4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV3s).toEquiv
  have hv0V3s : v0 ∈ V3s := Subgroup.mem_subgroupOf.mpr w₁.2
  have hcv0V3s : cW v0 ∈ V3s := by
    rw [hV3s_def, Subgroup.mem_subgroupOf]
    show (cW v0 : QV T V) ∈ secImg (NV T V) (fsuV1 T V) S.V3
    rw [hcW_coe, hv0_coe, ← hz₁w']
    have e : sm T V hcN * secMk (NV T V) (fsuV1 T V) z₁ * (sm T V hcN)⁻¹ =
        sm T V (hcczN z₁) := hconj (z₁ : G) z₁.2
    rw [e]
    exact secMk_mem_secImg (A := NV T V) (B := fsuV1 T V) (x := ⟨c * z₁ * c⁻¹, hcczN z₁⟩)
      (hcV3 _ hz₁)
  have hK0le : Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) ≤ V3s := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hv0V3s
    · exact hcv0V3s
  have hK0eq : Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) = V3s := by
    have hdvd : Nat.card ↥(Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H))) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV3s_card]
      exact Subgroup.card_dvd_of_le hK0le
    obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases i
    · exfalso
      have hn1 : Nat.card ↥(Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H))) = 1 := by
        rw [hn]; norm_num
      have hbot := Subgroup.card_eq_one.mp hn1
      have hmem : v0 ∈ Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hv0ne hmem
    · exfalso
      have hn2 : Nat.card ↥(Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H))) = 2 := by
        rw [hn]; norm_num
      obtain ⟨a, b, hab, hset⟩ := Nat.card_eq_two_iff.mp hn2
      have hall : ∀ z : ↥(Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H))),
          z = a ∨ z = b := fun z => by
        have hz : z ∈ ({a, b} : Set ↥(Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)))) := by
          rw [hset]; exact Set.mem_univ z
        simpa using hz
      have hvK : v0 ∈ Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hcK : cW v0 ∈ Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hoK : (1 : ↥(UT T V S.V3 H)) ∈ Subgroup.closure
          ({v0, cW v0} : Set ↥(UT T V S.V3 H)) := (Subgroup.closure _).one_mem
      set K₀ := Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) with hK₀
      let o : ↥K₀ := ⟨1, hoK⟩
      let u : ↥K₀ := ⟨v0, hvK⟩
      let t : ↥K₀ := ⟨cW v0, hcK⟩
      have hou : o ≠ u := fun h => hv0ne (congrArg Subtype.val h).symm
      have hot : o ≠ t := fun h => hcv0ne1 (congrArg Subtype.val h).symm
      have hut : u ≠ t := fun h => hcv0ne (congrArg Subtype.val h).symm
      rcases hall o with h1 | h1 <;> rcases hall u with h2 | h2 <;> rcases hall t with h3 | h3 <;>
        first
        | exact hou (h1.trans h2.symm)
        | exact hot (h1.trans h3.symm)
        | exact hut (h2.trans h3.symm)
    · exact Subgroup.eq_of_le_of_card_ge hK0le (by rw [hV3s_card, hn]; norm_num)
  have hV3s_sub : ∀ w ∈ V3s, w ∈ Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)) :=
    fun w hw => by rw [hK0eq]; exact hw
  have hcomm : ∀ (g : SL3.S) (w : ↥(UT T V S.V3 H)), ρ g (cW w) = cW (ρ g w) := by
    intro g w
    obtain ⟨k, rfl⟩ := hπ g
    rw [hρ k]
    have hcomm' := actU_comm_X hF hKn hKH hXH hX hcX k.2
    have := congrArg (fun φ : MulAut ↥(UT T V S.V3 H) => φ w) hcomm'
    simp only [MulAut.mul_apply] at this
    exact this.symm
  have hA : ∀ a ∈ L32HatM.A₀, ρ a v0 = v0 := by
    intro a ha
    obtain ⟨k, hkl, hka⟩ := hA0 a ha
    rw [← hka, hρ k]
    apply Subtype.ext
    show ((actU hF ⟨(k : G), hKH k.2⟩ v0 : ↥(UT T V S.V3 H)) : QV T V) = (v0 : QV T V)
    rw [coe_actU]
    have hkZ : (k : G) ∈ o2Z L := oTwoRes_le _ hkl
    have hkC : (k : G) ∈ Subgroup.centralizer (V : Set G) := S.o2Z_le_centralizer hkZ
    have hkz : (k : G) * (z₁ : G) = (z₁ : G) * (k : G) :=
      (Subgroup.mem_centralizer_iff.mp hkC (z₁ : G) (S.V3_le_V hz₁)).symm
    rw [hv0_coe, ← hz₁w']
    have hkk : sm T V (hF.H_normalizes_V₁ (hKH k.2)) * secMk (NV T V) (fsuV1 T V) z₁ =
        secMk (NV T V) (fsuV1 T V) z₁ * sm T V (hF.H_normalizes_V₁ (hKH k.2)) := by
      rw [← map_mul, ← map_mul]
      exact congrArg (secMk (NV T V) (fsuV1 T V)) (Subtype.ext hkz)
    rw [hkk, mul_inv_cancel_right]
  have hnt : ∃ g : SL3.S, ρ g ≠ 1 := by
    obtain ⟨k, hk⟩ := hπ L32HatM.rho₃
    refine ⟨L32HatM.rho₃, ?_⟩
    rw [← hk, hρ k]
    intro h1
    have hkQ : (k : G) ∉ pCoreOf 2 H := by
      intro hkQ'
      obtain ⟨j, hj⟩ := L32HatC3.two_pow_of_mem_pCoreOf hkQ'
      have hk2 : k ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
      have hr : L32HatM.rho₃ ^ 2 ^ j = 1 := by rw [← hk, ← map_pow, hk2, map_one]
      have h3 : L32HatM.rho₃ ^ 3 = 1 := by decide +kernel
      have hr1 : L32HatM.rho₃ ^ (Nat.gcd 3 (2 ^ j)) = 1 := (pow_gcd_eq_one).2 ⟨h3, hr⟩
      have hcop : Nat.gcd 3 (2 ^ j) = 1 := Nat.Coprime.pow_right j (by norm_num)
      rw [hcop, pow_one] at hr1
      exact (by decide +kernel : L32HatM.rho₃ ≠ 1) hr1
    exact actU_ne_one_of_not_pCore hF hKH hV1H k.2 hkQ h1
  set Ω : Subgroup ↥(UT T V S.V3 H) :=
    Subgroup.closure {w : ↥(UT T V S.V3 H) | ∃ g : SL3.S, w = ρ g v0 ∨ w = cW (ρ g v0)}
    with hΩdef
  have hΩK : ∀ k : ↥K, ∀ w ∈ Subgroup.closure ({v0, cW v0} : Set ↥(UT T V S.V3 H)),
      actU hF ⟨(k : G), hKH k.2⟩ w ∈ Ω := by
    intro k w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · apply Subgroup.subset_closure
        exact ⟨π k, Or.inl (by rw [hρ k]; rfl)⟩
      · apply Subgroup.subset_closure
        refine ⟨π k, Or.inr ?_⟩
        rw [← hcomm (π k) v0, hρ k]
        rfl
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  have hMK : S.L1 ⊔ T ≤ Subgroup.normalizer (K : Set G) := hL1H.trans hKn
  set Ωq : Subgroup (QV T V) := Ω.map (UT T V S.V3 H).subtype with hΩq
  have hUΩ : ∀ x : G, x ∈ conjClosure S.V3 H → ∀ hxN : x ∈ NV T V, sm T V hxN ∈ Ωq := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {x : G | ∃ h ∈ H, ∃ z ∈ S.V3, h * z * h⁻¹ = x} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx0 =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx0
      intro hxN
      obtain ⟨k, hk, m, hm, rfl⟩ := L32HatStep.mul_decomp_of_sup hMK h (hHK ▸ hh)
      have hm' : m ∈ S.L1 ⊔ T := hm
      have hz' : m * z * m⁻¹ ∈ S.V3 :=
        (Subgroup.mem_normalizer_iff.mp (hF.L₁T_normalizes_Vp hm') z).mp hz
      have hz'N : m * z * m⁻¹ ∈ NV T V := hV3N hz'
      have hkN : (k : G) ∈ NV T V := hF.H_normalizes_V₁ (hKH hk)
      set zt : ↥(UT T V S.V3 H) := ⟨sm T V hz'N, secMk_mem_secImg (A := NV T V) (B := fsuV1 T V)
          (x := ⟨m * z * m⁻¹, hz'N⟩) (hV3U hz')⟩ with hzt
      have hzU : zt ∈ V3s := by
        rw [hV3s_def, Subgroup.mem_subgroupOf]
        exact secMk_mem_secImg (A := NV T V) (B := fsuV1 T V) (x := ⟨m * z * m⁻¹, hz'N⟩) hz'
      have hw' := hΩK ⟨k, hk⟩ zt (hV3s_sub zt hzU)
      refine Subgroup.mem_map.mpr ⟨_, hw', ?_⟩
      show ((actU hF ⟨(k : G), hKH hk⟩ zt : ↥(UT T V S.V3 H)) : QV T V) = sm T V hxN
      rw [coe_actU]
      show sm T V hkN * sm T V hz'N * (sm T V hkN)⁻¹ = sm T V hxN
      rw [sm_conj]
      apply sm_congr
      group
    | one =>
      intro hxN
      have e : sm T V hxN = 1 := map_one (secMk (NV T V) (fsuV1 T V))
      rw [e]
      exact Subgroup.one_mem _
    | mul x y hx1 hy1 ih1 ih2 =>
      intro hxyN
      have hxN : x ∈ NV T V := hUN hx1
      have hyN : y ∈ NV T V := hUN hy1
      have e : sm T V hxyN = sm T V hxN * sm T V hyN := sm_mul hxN hyN
      rw [e]
      exact Subgroup.mul_mem _ (ih1 hxN) (ih2 hyN)
    | inv x hx1 ih =>
      intro hxiN
      have hxN : x ∈ NV T V := hUN hx1
      have e : sm T V hxiN = (sm T V hxN)⁻¹ := sm_inv hxN
      rw [e]
      exact Subgroup.inv_mem _ (ih hxN)
  have hgen : Subgroup.closure {w : ↥(UT T V S.V3 H) | ∃ g : SL3.S, w = ρ g v0 ∨ w = cW (ρ g v0)} = ⊤ := by
    refine (Subgroup.eq_top_iff' _).mpr fun w => ?_
    obtain ⟨x, hxU, hwx⟩ := mem_secImg.mp (show (w : QV T V) ∈
      secImg (NV T V) (fsuV1 T V) (conjClosure S.V3 H) from w.2)
    obtain ⟨w', hw'Ω, hw'⟩ := Subgroup.mem_map.mp (hUΩ x hxU x.2)
    have hww : w' = w := Subtype.ext (hw'.trans hwx)
    rw [← hww]
    exact hw'Ω
  set CW : Subgroup ↥(UT T V S.V3 H) := (UT T V S.V3 H ⊓
      Subgroup.centralizer ((tildeOf (fsuV1 T V) (pCoreOf 2 (S.L1 ⊔ T)) :
        Subgroup (QV T V)) : Set (QV T V))).subgroupOf (UT T V S.V3 H) with hCW
  have hCfix : ∀ w ∈ CW, ∀ e ∈ L32HatM.E₀, ρ e w = w := by
    intro w hw e he
    obtain ⟨k, hkR, hke⟩ := hE0 e he
    rw [← hke, hρ k]
    apply Subtype.ext
    show ((actU hF ⟨(k : G), hKH k.2⟩ w : ↥(UT T V S.V3 H)) : QV T V) = (w : QV T V)
    rw [coe_actU]
    have hwc : (w : QV T V) ∈ Subgroup.centralizer ((tildeOf (fsuV1 T V)
        (pCoreOf 2 (S.L1 ⊔ T)) : Subgroup (QV T V)) : Set (QV T V)) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)).2
    have hmemk : secMk (NV T V) (fsuV1 T V) ⟨(k : G), hF.H_normalizes_V₁ (hKH k.2)⟩ ∈
        tildeOf (fsuV1 T V) (pCoreOf 2 (S.L1 ⊔ T)) :=
      secMk_mem_secImg (A := NV T V) (B := fsuV1 T V) (x := ⟨(k : G), hF.H_normalizes_V₁ (hKH k.2)⟩) hkR
    have hcm := Subgroup.mem_centralizer_iff.mp hwc _ hmemk
    rw [hcm]
    group
  set Y := centralizerMod (fsuV1 T V) (conjClosure S.V3 H) (pCoreOf 2 (S.L1 ⊔ T)) with hYdef
  have hYU : Y ≤ conjClosure S.V3 H := fun x hx => hx.1
  have hYker : conjClosure S.V3 H ⊓ fsuV1 T V ≤ Y := by
    intro x hx
    obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.mp hx
    refine ⟨hxU, hUN hxU, fun u hu => ?_⟩
    have hun : u ∈ NV T V := hF.H_normalizes_V₁ (hRH hu)
    have h1 : u * x⁻¹ * u⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp hun x⁻¹).mp ((fsuV1 T V).inv_mem hxV)
    have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact (fsuV1 T V).mul_mem hxV h1
  have hidx : CW.index = Y.relIndex (conjClosure S.V3 H) := by
    have h1 := HypF91.tilde_inf_centralizer_mod hF hRH
    have h2 := relIndex_secImg_of_inf_le (A := NV T V) (K := fsuV1 T V) (C := Y)
      (X := conjClosure S.V3 H) hYU hUN hYker
    show (UT T V S.V3 H ⊓ Subgroup.centralizer ((tildeOf (fsuV1 T V) (pCoreOf 2 (S.L1 ⊔ T)) :
      Subgroup (QV T V)) : Set (QV T V))).relIndex (UT T V S.V3 H) = _
    rw [h1]
    exact h2
  have hdvd := L32HatC.index_dvd_of_fixed hsq cW hc ρ hcomm v0 hA hgen hnt CW hCfix
  rw [← Subgroup.card_mul_index CW] at hdvd
  have hpos : 0 < Nat.card CW := Nat.card_pos
  have h16 : 16 ∣ CW.index := by
    have h' : Nat.card CW * 16 ∣ Nat.card CW * CW.index := by
      rw [mul_comm (Nat.card CW) 16]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hpos h'
  show 4 ≤ padicValNat 2 (Y.relIndex (conjClosure S.V3 H))
  rw [← hidx]
  have hne : CW.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h16' : 2 ^ 4 ∣ CW.index := by
    norm_num
    exact h16
  exact (padicValNat_dvd_iff_le hne).mp h16'

end L32HatC5

end CFSG.Quasithin.H13.A6
