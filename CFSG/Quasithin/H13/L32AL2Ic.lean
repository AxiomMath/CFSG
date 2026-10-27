module

public import CFSG.Quasithin.H13.L32AL2Ib
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem exists_sq_eq_conj_of_GL32 {R : Type*} [Group R] (e : R ≃* GL (Fin 3) (ZMod 2))
    (α : R ≃* R) : ∃ r : R, ∀ x, α (α x) = r * x * r⁻¹ := by
  set β : MulAut (GL (Fin 3) (ZMod 2)) := (e.symm.trans α).trans e with hβ
  obtain ⟨g, hg⟩ := Subgroup.sq_mem_of_index_two LieType.SteinbergBR.AutGL32.index_inner β
  refine ⟨e.symm g, fun x => e.injective ?_⟩
  have h1 := congrArg (fun φ : MulAut (GL (Fin 3) (ZMod 2)) => φ (e x)) hg
  simp only [MulAut.conj_apply, pow_two, MulAut.mul_apply, hβ, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h1.symm

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_self_mem_sup {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hsq : ∀ α : MulAut (↥K ⧸ CFSG.pCore 2 ↥K), ∃ r : ↥K ⧸ CFSG.pCore 2 ↥K,
      ∀ x, α (α x) = r * x * r⁻¹)
    {g : G} (hg : g ∈ H) : g * g ∈ K ⊔ centralizerSection H K (pCoreOf 2 K) := by
  have hgN := hHK hg
  set φ : MulAut ↥K := K.normalizerMonoidHom ⟨g, hgN⟩ with hφ
  have hφapp : ∀ x : ↥K, ((φ x : ↥K) : G) = g * x * g⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨g, hgN⟩ x
  set α : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ) with hα
  obtain ⟨r, hr⟩ := hsq α
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) r
  have hPK : pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := by
    rw [pCoreOf]
  have hm : (k : G)⁻¹ * (g * g) ∈ centralizerSection H K (pCoreOf 2 K) := by
    have hmN : (k : G)⁻¹ * (g * g) ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer k.2))
        (Subgroup.mul_mem _ hgN hgN)
    refine ⟨H.mul_mem (H.inv_mem (hKH k.2)) (H.mul_mem hg hg), hmN,
      normalizer_le_normalizer_pCoreOf 2 K hmN, fun x hx => ?_⟩
    have hαmk : ∀ y : ↥K, α (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := fun y => rfl
    have h1 := hr (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥K))
    rw [hαmk, hαmk, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    set p : ↥K := (φ (φ (⟨x, hx⟩⁻¹ : ↥K)))⁻¹ * (k * (⟨x, hx⟩⁻¹ : ↥K) * k⁻¹) with hp
    have hpG : (p : G) = (g * (g * x⁻¹ * g⁻¹) * g⁻¹)⁻¹ * ((k : G) * x⁻¹ * (k : G)⁻¹) := by
      simp only [hp, Subgroup.coe_mul, Subgroup.coe_inv, hφapp]
    have hpP : (p : G)⁻¹ ∈ pCoreOf 2 K := by
      rw [hPK]
      exact ⟨p⁻¹, inv_mem h1, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf 2 K (K.inv_mem k.2)) ((p : G)⁻¹)).1 hpP
    have he : x * ((k : G)⁻¹ * (g * g)) * x⁻¹ * ((k : G)⁻¹ * (g * g))⁻¹ =
        (k : G)⁻¹ * (p : G)⁻¹ * (k : G)⁻¹⁻¹ := by
      rw [hpG]
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [he]
    exact hconj
  have h2 : g * g = (k : G) * ((k : G)⁻¹ * (g * g)) := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hm)

omit [Finite G] in
theorem mem_sup_of_odd {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hsq : ∀ α : MulAut (↥K ⧸ CFSG.pCore 2 ↥K), ∃ r : ↥K ⧸ CFSG.pCore 2 ↥K,
      ∀ x, α (α x) = r * x * r⁻¹)
    {y : G} (hy : y ∈ H) (ho : Odd (orderOf y)) :
    y ∈ K ⊔ centralizerSection H K (pCoreOf 2 K) := by
  obtain ⟨n, hn⟩ := ho
  have h1 : y = (y * y) ^ (n + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (n + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h1]
  exact Subgroup.pow_mem _ (mul_self_mem_sup hKH hHK hsq hy) _

omit [Finite G] in
theorem mem_normalizer_of_mem_centralizerSection {H K X : Subgroup G} {c : G}
    (hc : c ∈ centralizerSection H K (pCoreOf 2 K)) (hPX : pCoreOf 2 K ≤ X) (hXK : X ≤ K) :
    c ∈ Subgroup.normalizer (X : Set G) := by
  have key : ∀ d ∈ centralizerSection H K (pCoreOf 2 K), ∀ x ∈ X, d * x * d⁻¹ ∈ X := by
    intro d hd x hx
    have h1 := (mem_centralizerSection.mp hd).2.2.2 x⁻¹ (K.inv_mem (hXK hx))
    have e : d * x * d⁻¹ = x * (x⁻¹ * d * x⁻¹⁻¹ * d⁻¹) := by group
    rw [e]
    exact X.mul_mem hx (hPX h1)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key c hc x, fun hx => ?_⟩
  have := key c⁻¹ (Subgroup.inv_mem _ hc) _ hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

theorem card_inf_centralizer_eq_two {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting G T L V V₂) {x : G} (hxL : x ∈ L) (hx3 : orderOf x = 3) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = 2 := by
  classical
  have hxN := S14.LV hxL
  set F := V ⊓ Subgroup.centralizer ({x} : Set G) with hF
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have := Fintype.ofFinite ↥V
  let σ : Equiv.Perm ↥V :=
    { toFun := fun v => ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN v).mp v.2⟩
      invFun := fun v => ⟨x⁻¹ * v * x, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) v).mp v.2
        rwa [inv_inv] at this⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc]) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    ext v
    rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    show x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v
    have hxxx : x * x * x = 1 := by rw [← pow_three']; exact hx3'
    have e : x * (x * (x * (v : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * v * (x * x * x)⁻¹ := by
      group
    rw [e, hxxx, one_mul, inv_one, mul_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := Equiv.Perm.card_compl_support_modEq hσ
  have hfix1 : (σ.supportᶜ : Finset ↥V).card = Nat.card {v : ↥V // σ v = v} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    simp [Equiv.Perm.mem_support]
  have hfix2 : Nat.card {v : ↥V // σ v = v} = Nat.card F := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1, v.1.2, ?_⟩
        invFun := fun f => ⟨⟨f, f.2.1⟩, ?_⟩
        left_inv := fun v => rfl
        right_inv := fun f => rfl }
    · have h1 := congrArg Subtype.val v.2
      change x * (v.1 : G) * x⁻¹ = v.1 at h1
      show (v.1 : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (v.1 : G) * x = x * v.1 * x⁻¹ * x := by rw [h1]
        _ = x * v.1 := by group
    · apply Subtype.ext
      change x * (f : G) * x⁻¹ = f
      have h2 : (f : G) * x = x * f := Subgroup.mem_centralizer_singleton_iff.mp f.2.2
      rw [← h2, mul_inv_cancel_right]
  have hfix : (σ.supportᶜ : Finset ↥V).card = Nat.card F := hfix1.trans hfix2
  rw [hfix, ← Nat.card_eq_fintype_card, S14.card_V] at hc
  obtain ⟨k, hk3, hk⟩ : ∃ k ≤ 3, Nat.card F = 2 ^ k := by
    have hdvd : Nat.card F ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← S14.card_V]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk] at hc
  interval_cases k
  · norm_num [Nat.ModEq] at hc
  · exact hk
  · norm_num [Nat.ModEq] at hc
  · exfalso
    have hFV : F = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, S14.card_V]; norm_num)
    have hxC : x ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨hxL, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hvF : v ∈ F := hFV ▸ hv
      exact Subgroup.mem_centralizer_singleton_iff.mp hvF.2
    rw [S14.cent_eq] at hxC
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 L ⟨x, hxC⟩
    have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 := orderOf_dvd_of_pow_eq_one hm'
    rw [hx3] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)
    omega

omit [Finite G] in
theorem mem_normalizer_sup' {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem mem_centralizer_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : g ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  have hga : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  have h1 := hu ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
  have h2 := hu ⟨g * a * g⁻¹, hga⟩ (fun h => ha1 (by
    have h3 := congrArg Subtype.val h
    change g * a * g⁻¹ = 1 at h3
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group))
  have h4 : g * a * g⁻¹ = a := congrArg Subtype.val (h2.trans h1.symm)
  calc a * g = (g * a * g⁻¹) * g := by rw [h4]
    _ = g * a := by group

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem exists_set14 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ (V₂ : Subgroup G) (h : IsMulCommutative ↥V), @L32NSet14.Setting G _ _ T L V V₂ h := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V D.S.hyp.hyp D.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 D.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  exact ⟨V₂, inferInstance, Hyp147.set14 D.S.hyp h1222 h1332 h1334 hV2⟩

omit D [Finite G] in
theorem l1_le_L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left

omit D [Finite G] in
theorem lY_le_l1 : lY T L V z' ≤ l1 T L V := (oTwoUpper_le _).trans inf_le_left

theorem inf_centralizer_eq_V1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    V ⊓ Subgroup.centralizer ((lY T L V z' ⊔ pCoreOf 2 L : Subgroup G) : Set G) =
      fsuV1 T V := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  obtain ⟨x, hxY, hxL, hx3, -⟩ := D.exists_x
  have hO2V : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
    rw [← S14.cent_eq]
    exact inf_le_right
  have hXC : lY T L V z' ⊔ pCoreOf 2 L ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
    refine sup_le ?_ (hO2V.trans (Subgroup.centralizer_le inf_le_left))
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
      ((oTwoUpper_le _).trans inf_le_right) (lY_le_l1 hg)
    exact mem_centralizer_of_card_two S14.card_V1 hgN
  have hle : fsuV1 T V ≤ V ⊓ Subgroup.centralizer
      ((lY T L V z' ⊔ pCoreOf 2 L : Subgroup G) : Set G) :=
    le_inf inf_le_left (Subgroup.le_centralizer_iff.mp hXC)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [S14.card_V1, ← card_inf_centralizer_eq_two S14 (l1_le_L (lY_le_l1 hxY)) hx3]
  refine Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le ?_))
  rintro _ rfl
  exact Subgroup.mem_sup_left hxY

theorem oTwoUpper_l1_sup (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    oTwoUpper (l1 T L V ⊔ pCoreOf 2 L) = l1 T L V := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  have hO2N : pCoreOf 2 L ≤ Subgroup.normalizer (l1 T L V : Set G) := by
    intro q hq
    have hqC : q ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      rw [S14.cent_eq]
      exact hq
    have hqN : q ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :=
      ⟨hqC.1, Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le inf_le_left hqC.2)⟩
    exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.le_normalizer hqN)
  refine le_antisymm (L32A.oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 L) hO2N) ?_
  calc l1 T L V = oTwoUpper (l1 T L V) := (oTwoUpper_oTwoUpper _).symm
    _ ≤ _ := oTwoUpper_mono le_sup_left

theorem odd_mem_normalizer_l1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {y : G} (hy : y ∈ a114Y z z')
    (hyM : y ∈ Subgroup.normalizer (L : Set G)) (ho : Odd (orderOf y)) :
    y ∈ Subgroup.normalizer (l1 T L V : Set G) := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  obtain ⟨e⟩ := LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 S14.hlin
  have hsq : ∀ α : MulAut (↥L ⧸ CFSG.pCore 2 ↥L), ∃ r : ↥L ⧸ CFSG.pCore 2 ↥L,
      ∀ x, α (α x) = r * x * r⁻¹ := fun α => exists_sq_eq_conj_of_GL32 e α
  have hyLC := mem_sup_of_odd (H := Subgroup.normalizer (L : Set G)) (K := L)
    Subgroup.le_normalizer le_rfl hsq hyM ho
  have hCN : centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L) ≤
      Subgroup.normalizer (L : Set G) := fun c hc => (mem_centralizerSection.mp hc).2.1
  obtain ⟨l, hl, c, hc, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hCN).1 hyLC
  have hXL : lY T L V z' ⊔ pCoreOf 2 L ≤ L := sup_le (l1_le_L.trans' lY_le_l1) (pCoreOf_le 2 L)
  have hcX := mem_normalizer_of_mem_centralizerSection hc le_sup_right hXL
  have hlcX : l * c ∈ Subgroup.normalizer ((lY T L V z' ⊔ pCoreOf 2 L : Subgroup G) : Set G) :=
    mem_normalizer_sup' (D.a114Y_le_normalizer_lY h1332 hy)
      (normalizer_le_normalizer_pCoreOf 2 L hyM)
  have hlX : l ∈ Subgroup.normalizer ((lY T L V z' ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
    have := Subgroup.mul_mem _ hlcX (Subgroup.inv_mem _ hcX)
    rwa [mul_inv_cancel_right] at this
  have hlV1 : l ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [← D.inf_centralizer_eq_V1 h1222 h1332 h1334]
    exact mem_normalizer_inf (S14.LV hl) (mem_normalizer_centralizer hlX)
  have hl1 : l ∈ Subgroup.normalizer (l1 T L V : Set G) :=
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.le_normalizer ⟨hl, hlV1⟩)
  have hc1 : c ∈ Subgroup.normalizer (l1 T L V : Set G) := by
    have h := mem_normalizer_of_mem_centralizerSection hc
      (le_sup_right : pCoreOf 2 L ≤ l1 T L V ⊔ pCoreOf 2 L) (sup_le l1_le_L (pCoreOf_le 2 L))
    have h' := normalizer_le_normalizer_oTwoUpper _ h
    rwa [D.oTwoUpper_l1_sup h1222 h1332 h1334] at h'
  exact Subgroup.mul_mem _ hl1 hc1

theorem a114Y_not_le_normalizer_L (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : ¬ a114Y z z' ≤ Subgroup.normalizer (L : Set G) := by
  intro hYM
  apply D.a114Y_not_le_normalizer_l1 h1222 h1332 h1334
  have hO2 : oTwoUpper (a114Y z z') ≤ Subgroup.normalizer (l1 T L V : Set G) := by
    rw [oTwoUpper, Subgroup.closure_le]
    rintro y ⟨hy, ho⟩
    exact D.odd_mem_normalizer_l1 h1222 h1332 h1334 hy (hYM hy) ho
  exact D.a114Y_le_sup.trans (sup_le hO2 (D.hTY.trans (Setting147.T_le_N_l1 D.S h1332)))

end IData

end CFSG.Quasithin.H13.L32A.L2
