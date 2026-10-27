module

public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.H13.L32NLem14324q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cube_mem_of_relIndex_three {X N : Subgroup G} (hn : (N.subgroupOf X).Normal)
    (h3 : N.relIndex X = 3) {x : G} (hx : x ∈ X) : x ^ 3 ∈ N := by
  have hcard : Nat.card (↥X ⧸ N.subgroupOf X) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact h3
  have := pow_card_eq_one' (G := ↥X ⧸ N.subgroupOf X) (x := ((⟨x, hx⟩ : ↥X) : ↥X ⧸ N.subgroupOf X))
  rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  simpa using this

namespace Ctx5

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx5 G T L V V₂ g a D)
include C

theorem inf_le_p128 : (L ⊔ T) ⊓ Subgroup.normalizer (V₂ : Set G) ≤ p128 T L V := by
  rintro c ⟨hcL, hcN⟩
  refine Subgroup.mem_inf.2 ⟨hcL, Subgroup.mem_iInf.2 fun Y => Subgroup.mem_iInf.2 fun hY => ?_⟩
  obtain ⟨i, hi, hYi⟩ := hY
  rcases tinv_comparable_of_hyp1281One C.h1222 C.setting.hyp hYi.1 C.plane.1.1 hYi.2.2
      C.plane.1.2.2 with hle | hle
  · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [C.plane.1.2.1, hYi.2.1]
      exact Nat.pow_le_pow_right (by norm_num) hi)
    rw [heq]
    exact hcN
  · have h8 : Nat.card Y ≤ 8 := by
      rw [← C.cardV]
      exact Subgroup.card_le_of_le hYi.1
    rw [hYi.2.1] at h8
    have hi3 : i ≤ 3 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
    rcases (show i = 2 ∨ i = 3 by omega) with rfl | rfl
    · have heq : V₂ = Y := Subgroup.eq_of_le_of_card_ge hle (by rw [C.plane.1.2.1, hYi.2.1])
      rw [← heq]
      exact hcN
    · have heq : Y = V := Subgroup.eq_of_le_of_card_ge hYi.1 (by rw [C.cardV, hYi.2.1]; norm_num)
      rw [heq]
      exact C.LTV hcL

theorem lOne_sup_le : lOne L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
  sup_le ((oTwoUpper_le _).trans inf_le_right) C.setting.v1.2.2

omit [Finite G] C in
theorem lOne_sup_le_LT : lOne L (fsuV1 T V) ⊔ T ≤ L ⊔ T :=
  sup_le_sup_right ((oTwoUpper_le _).trans inf_le_left) T

theorem exists_mem_p128 {m : G} (hm : m ∈ L ⊔ T)
    (hmN : m ∈ Subgroup.normalizer (fsuV1 T V : Set G)) :
    ∃ s ∈ lOne L (fsuV1 T V) ⊔ T, ∃ x ∈ p128 T L V, m = s⁻¹ * x := by
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  have hmV := C.LTV hm
  have hu : m * a * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hmV a).mp haV
  have hu1 : m * a * m⁻¹ ∉ fsuV1 T V := fun h =>
    C.a1 ((Subgroup.mem_normalizer_iff.mp hmN a).mpr h)
  obtain ⟨s, hs, hsa⟩ :=
    L1297.exists_mem_sup_conj_eq C.h1222 C.setting.hyp C.setting.v1 hu haV hu1 C.a1
  set x := s * m with hxdef
  have hxa : x * a * x⁻¹ = a := by
    rw [show x * a * x⁻¹ = s * (m * a * m⁻¹) * s⁻¹ by rw [hxdef]; group, hsa]
  have hxN1 : x ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
    Subgroup.mul_mem _ (C.lOne_sup_le hs) hmN
  have hxN2 : x ∈ Subgroup.normalizer (V₂ : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    by_cases hv1 : v ∈ fsuV1 T V
    · exact C.plane.2 ((Subgroup.mem_normalizer_iff.mp hxN1 v).mp hv1)
    · have hcard : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by
        rw [C.plane.1.2.1, C.card_V1]
        norm_num
      have hav : a⁻¹ * v ∈ fsuV1 T V :=
        L32NSet14.mul_mem_of_card_eq_two_mul C.plane.2 hcard (by rw [C.card_V1]; norm_num)
          (V₂.inv_mem C.aV₂) hv (fun hm => C.a1 (by simpa using (fsuV1 T V).inv_mem hm)) hv1
      rw [show x * v * x⁻¹ = (x * a * x⁻¹) * (x * (a⁻¹ * v) * x⁻¹) by group, hxa]
      exact V₂.mul_mem C.aV₂ (C.plane.2 ((Subgroup.mem_normalizer_iff.mp hxN1 _).mp hav))
  refine ⟨s, hs, x, C.inf_le_p128 ⟨Subgroup.mul_mem _ (lOne_sup_le_LT hs) hm, hxN2⟩, ?_⟩
  rw [hxdef]
  group

theorem L_le : L ≤ (lOne L (fsuV1 T V) ⊔ T) ⊔ p128 T L V := by
  intro l hl
  have hlLT : l ∈ L ⊔ T := Subgroup.mem_sup_left hl
  set X := (lOne L (fsuV1 T V) ⊔ T) ⊔ p128 T L V with hX
  have hN1 : ∀ m ∈ L ⊔ T, m ∈ Subgroup.normalizer (fsuV1 T V : Set G) → m ∈ X := by
    intro m hm hmN
    obtain ⟨s, hs, x, hx, rfl⟩ := C.exists_mem_p128 hm hmN
    exact X.mul_mem (X.inv_mem (Subgroup.mem_sup_left hs)) (Subgroup.mem_sup_right hx)
  by_cases hlN : l ∈ Subgroup.normalizer (fsuV1 T V : Set G)
  · exact hN1 l hlLT hlN
  · have hgLT : g ∈ L ⊔ T := (inf_le_left : p128 T L V ≤ L ⊔ T) C.gP
    obtain ⟨s, hs, m, hm, hlsgm⟩ :=
      L128P.exists_eq_mul_mul C.h1222 C.setting.hyp C.setting.v1 hgLT C.gN hlLT hlN
    have hmLT : m ∈ L ⊔ T := by
      have : m = g⁻¹ * s⁻¹ * l := by rw [hlsgm]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgLT)
        (Subgroup.inv_mem _ (lOne_sup_le_LT hs))) hlLT
    rw [hlsgm]
    exact X.mul_mem (X.mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right C.gP))
      (hN1 m hmLT hm)

theorem comm_zD_ne (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h36 : A36ForSQTK)
    (M : S8Five.Model5 (D.img (l32nH T V))) {K : Subgroup G} (hK : K ∈ cComp (l32nH T V))
    (hKimg : D.img K = M.A) (hKn : l32nH T V ≤ Subgroup.normalizer (K : Set G)) :
    ⁅quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V (fsuV1 T V)), K⁆ ≠ ⊥ := by
  classical
  intro hbot
  set ZD := quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V (fsuV1 T V)) with hZD
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKC : K ≤ Subgroup.centralizer (ZD : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hz => hz.1
  have hTC : T ≤ Subgroup.centralizer (ZD : Set G) :=
    Subgroup.le_centralizer_iff.mp ((inf_le_left.trans hZT).trans inf_le_right)
  have hI2C : i128 T L V (fsuV1 T V) ≤ Subgroup.centralizer (ZD : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2.2 x hx).symm
  have hO2P : oTwoUpper (p128 T L V) ≤ Subgroup.centralizer (ZD : Set G) :=
    (C.i2_eq ▸ le_sup_left : oTwoUpper (p128 T L V) ≤ i128 T L V (fsuV1 T V)).trans hI2C
  have hPC : p128 T L V ≤ Subgroup.centralizer (ZD : Set G) := by
    have hsyl : IsSylowTwoOf T (p128 T L V) :=
      isSylowTwoOf_of_isSylowTwo C.hyp.fsu.sylow L128P.le_p128
    have hP := sup_twoResidual_eq hsyl
    rw [F6.twoResidual_eq_oTwoUpper] at hP
    rw [← hP]
    exact sup_le hTC hO2P
  have hO2HT : pCoreOf 2 (l32nH T V) ≤ T :=
    B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo C.hyp.fsu.sylow C.T_le)
  obtain ⟨_, S⟩ := L14332.exists_setting h1332 h1334 C.h1222 C.hyp C.plane
  have hL3 := S.Lp3
  rw [← lOne_eq_L₁Of] at hL3
  have hL1n : ((pCoreOf 2 (lOne L (fsuV1 T V))).subgroupOf (lOne L (fsuV1 T V))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hL1C : lOne L (fsuV1 T V) ≤ Subgroup.centralizer (ZD : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxLN, hxo⟩
    have hxL1 : x ∈ lOne L (fsuV1 T V) := Subgroup.subset_closure ⟨hxLN, hxo⟩
    have h3 := cube_mem_of_relIndex_three hL1n hL3 hxL1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (lOne L (fsuV1 T V)) ⟨_, h3⟩
    have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf (x ^ 3)) := Odd.of_dvd_nat hxo (orderOf_pow_dvd 3)
    have hx3 : x ^ 3 = 1 := by
      have hd : orderOf (x ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf (x ^ 3)) (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd)
    obtain ⟨k₀, hk₀, q, hq, rfl⟩ := C.mem_of_cube h36 M hK hKimg hKn hxLN.2 hx3
    exact Subgroup.mul_mem _ (hKC hk₀) (hTC (hO2HT hq))
  have hLC : L ≤ Subgroup.centralizer (ZD : Set G) :=
    C.L_le.trans (sup_le (sup_le hL1C hTC) hPC)
  have hZDne := C.zD_ne M
  have hZD2 : IsPGroup 2 ↥ZD := C.hyp.fsu.sylow.1.to_le (inf_le_left.trans (hZT.trans inf_le_left))
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (ZD : Set G))
    ⟨ZD, hZDne, hZD2, rfl⟩
  have hLT : L ⊔ T ≤ M' :=
    (sup_le hLC hTC).trans ((Subgroup.centralizer_le_normalizer _).trans hle)
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hM'eq := (h13322 G T L C.hyp.hyp.h13 L C.hyp.hyp.h13.faithful).2.2.2 M' hM' hLT
  have hKM : K ≤ Subgroup.normalizer (L : Set G) :=
    hKC.trans ((Subgroup.centralizer_le_normalizer _).trans (hle.trans hM'eq.le))
  have hV1ne : fsuV1 T V ≠ ⊥ := by
    intro h
    have := C.card_V1
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have h1433 := lemma1433Six_of_inputs h1332 h1334 C.h1222 G T L V C.hyp.hyp C.hyp.fsu
    (fsuV1 T V) (l32nH T V) inf_le_left hV1ne le_rfl
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := fun k hk => by
    have : k ∈ l32nH T V ⊓ Subgroup.normalizer (V : Set G) := by
      rw [← h1433]
      exact ⟨hKH hk, hKM hk⟩
    exact this.2
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  have hV₂V : V₂ < V := lt_of_le_of_ne C.plane.1.1 fun he => by
    have h4 : Nat.card V₂ = 4 := C.plane.1.2.1
    rw [he, C.cardV] at h4
    norm_num at h4
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hV₂V
  have hcU := C.V_U hcV
  have haU := C.V_U haV
  have hcard12 : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by
    rw [C.plane.1.2.1, C.card_V1]
    norm_num
  have hcard2 : Nat.card V = 2 * Nat.card V₂ := by
    rw [C.cardV, C.plane.1.2.1]
    norm_num
  have hπcls : ∀ w ∈ V, w ∉ fsuV1 T V →
      D.π w = D.π a ∨ D.π w = D.π c ∨ D.π w = D.π c + D.π a := by
    intro w hw hw1
    have hwU := C.V_U hw
    by_cases hw2 : w ∈ V₂
    · left
      have h1 : a⁻¹ * w ∈ fsuV1 T V :=
        L32NSet14.mul_mem_of_card_eq_two_mul C.plane.2 hcard12 (by rw [C.card_V1]; norm_num)
          (V₂.inv_mem C.aV₂) hw2 (fun hm => C.a1 (by simpa using (fsuV1 T V).inv_mem hm)) hw1
      exact ((D.π_eq_iff _ haU _ hwU).mpr (C.V1_le_zU h1)).symm
    · have h1 : c⁻¹ * w ∈ V₂ :=
        L32NSet14.mul_mem_of_card_eq_two_mul C.plane.1.1 hcard2 (by rw [C.plane.1.2.1]; norm_num)
          (V.inv_mem hcV) hw (fun hm => hc2 (by simpa using V₂.inv_mem hm)) hw2
      by_cases h2 : c⁻¹ * w ∈ fsuV1 T V
      · right; left
        exact ((D.π_eq_iff _ hcU _ hwU).mpr (C.V1_le_zU h2)).symm
      · right; right
        have h3 : a⁻¹ * (c⁻¹ * w) ∈ fsuV1 T V :=
          L32NSet14.mul_mem_of_card_eq_two_mul C.plane.2 hcard12 (by rw [C.card_V1]; norm_num)
            (V₂.inv_mem C.aV₂) h1 (fun hm => C.a1 (by simpa using (fsuV1 T V).inv_mem hm)) h2
        have hca : c * a ∈ fsuU T V := (fsuU T V).mul_mem hcU haU
        rw [← D.π_mul c hcU a haU]
        refine ((D.π_eq_iff _ hca _ hwU).mpr ?_).symm
        rw [show (c * a)⁻¹ * w = a⁻¹ * (c⁻¹ * w) by group]
        exact C.V1_le_zU h3
  have hAorb : ∀ α ∈ M.A, α (D.π a) = D.π a ∨ α (D.π a) = D.π c ∨
      α (D.π a) = D.π c + D.π a := by
    intro α hα
    rw [← hKimg] at hα
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hα
    rw [D.ρ_π ⟨k, hkN⟩ a haU]
    have hkV := hKV hk
    have hkV1 : k ∈ Subgroup.normalizer (fsuV1 T V : Set G) := hKH hk
    exact hπcls _ ((Subgroup.mem_normalizer_iff.mp hkV a).mp haV)
      (fun h => C.a1 ((Subgroup.mem_normalizer_iff.mp hkV1 a).mpr h))
  have : IsSimpleGroup ↥M.A := M.isSimpleGroup_A
  set Sb := MulAction.stabilizer ↥M.A (D.π a) with hSb
  have hidx : Sb.index ≤ 3 := by
    rw [hSb, MulAction.index_stabilizer]
    have hsub : MulAction.orbit ↥M.A (D.π a) ⊆ {D.π a, D.π c, D.π c + D.π a} := by
      rintro _ ⟨α, rfl⟩
      rcases hAorb α α.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    calc (MulAction.orbit ↥M.A (D.π a)).ncard ≤ ({D.π a, D.π c, D.π c + D.π a} : Set D.V).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 3 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
          rw [Set.ncard_singleton]
  have hcore : Sb.normalCore = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Sb.normalCore with h | h
    · exfalso
      have h1 := Subgroup.index_normalCore_le_factorial_index Sb
      rw [h, Subgroup.index_bot, M.card_A] at h1
      have h2 : Nat.factorial Sb.index ≤ Nat.factorial 3 := Nat.factorial_le hidx
      have h3 : Nat.factorial 3 = 6 := by decide
      omega
    · exact h
  have hfix : ∀ α ∈ M.A, α (D.π a) = D.π a := by
    intro α hα
    have hmem : (⟨α, hα⟩ : ↥M.A) ∈ Sb :=
      Subgroup.normalCore_le Sb (hcore ▸ Subgroup.mem_top _)
    exact hmem
  have hall : ∀ α ∈ M.A, ∀ w : D.V, α w = w := by
    intro α hα
    have hsub : Submodule.span (ZMod 2) (MulAction.orbit (D.img (l32nH T V)) (D.π a)) ≤
        LinearMap.ker (α.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hγα : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ * α * (γ : D.V ≃ₗ[ZMod 2] D.V) ∈ M.A := by
        have := M.A_normal (Subgroup.inv_mem _ γ.2) hα
        simpa [mul_assoc] using this
      have h2 : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ (α ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a))) = D.π a :=
        hfix _ hγα
      show α ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a)) - (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) = 0
      have h3 : α ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a)) = (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
        have := congrArg (fun w => (γ : D.V ≃ₗ[ZMod 2] D.V) w) h2
        simpa using this
      rw [h3, sub_self]
    intro w
    have hw : w ∈ LinearMap.ker (α.toLinearMap - LinearMap.id) := by
      apply hsub
      rw [C.span]
      exact Submodule.mem_top
    have := LinearMap.mem_ker.mp hw
    simpa [sub_eq_zero] using this
  have ha9A : M.ψ S8Five.a9 ∈ M.A :=
    ⟨S8Five.a9, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.1, rfl⟩
  have h1 : M.ψ S8Five.a9 = 1 := LinearEquiv.ext fun w => hall _ ha9A w
  exact absurd (M.ψ_injective (h1.trans (map_one M.ψ).symm)) (by decide)

end Ctx5

end L14324

end CFSG.Quasithin.H13
