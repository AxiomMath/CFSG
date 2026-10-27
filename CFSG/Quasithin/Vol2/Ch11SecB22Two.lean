module

public import CFSG.Quasithin.Vol2.Ch11SecB22R

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem natSetting (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) :
    IsElemAbelian 2 (fsuV T I) ∧ 2 ≤ n ∧ L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      ⁅fsuV T I, L⁆ = fsuV T I ∧ NatModuleOf L (fsuV T I) n ∧
      L ≤ Subgroup.normalizer (L : Set G) ∧
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (fsuV T I : Set G) ≤
        Subgroup.normalizer (L : Set G) :=
  ⟨isElemAbelian_fsuV hyp, hyp.one_lt, L_le_normalizer_fsuV hyp, commutator_fsuV_eq_self hyp,
    natModuleOf_fsuV h1102 hyp, Subgroup.le_normalizer, inf_le_left⟩

theorem centralizer_le_of_lt (hFM : FactMParam) (hFO : FactOddCodim) (hFH : FactHyperplaneT)
    (hS44 : FactSp4FourExt) (hN : FactNot4213) (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) (h664 : ASInputs.AS_E_6_6_four)
    (h614 : ASInputs.AS_E_6_14) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1104 : Stmt11_0_4) (hyp : Hyp11 G T L I n) {m : ℕ}
    (hm : KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n)
    {U : Subgroup G} (hUV : U ≤ fsuV T I)
    (hres : twoPrimeResidual (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G))
      ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G))
    (hk : E3.mQuot (fsuV T I) U < 2 * m) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      twoPrimeResidual (Subgroup.centralizer (U : Set G)) ≤
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨hU1, heq⟩ := inf_centralizer_eq_of_lt hFM hFO h1102 h1103 h1104 hyp hm hUV hk hres
  have hr := le_rParam hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331 h1102 h1103 hyp hm
  have hm2 : 2 ≤ m := by
    have := hyp.one_lt
    rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hCM : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hC
    have h1 := (h612 G T _ (fsuV T I) U (hypE61_of h331 h1102 h1103 hyp) hU1 hUV heq hC).2
    rw [h1] at hr
    have : m ≤ 1 := by exact_mod_cast hr
    omega
  refine ⟨hCM, ?_⟩
  have e : Subgroup.centralizer (U : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) :=
    (inf_eq_right.mpr hCM).symm
  rw [e]
  exact hres

omit [Finite G] in
theorem exists_eq_rParam {V : Subgroup G} (h : E3.rParam V ≠ ⊤) :
    ∃ U : Subgroup G, U ≤ V ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      (E3.mQuot V U : ℕ∞) = E3.rParam V := by
  set S := {U : Subgroup G | U ≤ V ∧
    ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)} with hSdef
  have hr : E3.rParam V = ⨅ U : S, (E3.mQuot V U : ℕ∞) := by
    rw [E3.rParam, iInf_subtype']
  have hne : Nonempty S := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    apply h
    rw [hr]
    exact iInf_of_empty _
  obtain ⟨⟨U, hUS⟩, hU⟩ := ENat.exists_eq_iInf (fun U : S => (E3.mQuot V U : ℕ∞))
  exact ⟨U, hUS.1, hUS.2, hU.trans hr.symm⟩

theorem twoPrimeResidual_le_of_forall {H V : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ y ∈ H, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ∈ Subgroup.centralizer (V : Set G)) :
    twoPrimeResidual H ≤ H ⊓ Subgroup.centralizer (V : Set G) := by
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two H
  have hSC : S ≤ Subgroup.centralizer (V : Set G) := fun s hs => by
    obtain ⟨k, hk⟩ := hS.2.1 ⟨s, hs⟩
    exact h s (hS.1 hs) ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine iInf₂_le (H ⊓ Subgroup.centralizer (V : Set G))
    ⟨inf_le_left, B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer hHN), fun h2 => ?_⟩
  exact hS.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left H (le_inf hS.1 hSC)))

theorem eq_isVi_of_flag (hNF : NatFacts) (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {i : ℕ}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) {U W : Subgroup G} (hW : IsVi T L I n i W)
    (hUV : U ≤ fsuV T I) (hCU : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ U)
    (hE : IsEndStable L (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) U)
    (hidx : (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i))
    (hTU : T ⊓ L ≤ Subgroup.normalizer (U : Set G)) : U = W := by
  have hL := L_le_normalizer_fsuV hyp
  have hflag : IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (2 ^ n) i
      (U.subgroupOf (fsuV T I)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      exact hCU ⟨z.2, hz⟩
    · have := (isEndStable_iff hL _ U).mp hE
      rwa [inf_centralizer_subgroupOf] at this
    · rw [← inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx, pow_mul]
    · intro g hg
      obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
      exact (conjV_mem_stabW_iff hUV hxV).mpr (hTU hx)
  have hflagW := isFlagW_of_isVi hyp hW
  obtain ⟨U₁, U₂, U₃, -, -, -, -, -, hu1, hu2, hu3⟩ := hasUniqueFlag hNF h1102 hyp
  have heq : U.subgroupOf (fsuV T I) = W.subgroupOf (fsuV T I) := by
    rcases hi with rfl | rfl | rfl
    · rw [hu1 _ hflag, hu1 _ hflagW]
    · rw [hu2 _ hflag, hu2 _ hflagW]
    · rw [hu3 _ hflag, hu3 _ hflagW]
  have h2 := Subgroup.subgroupOf_inj.mp heq
  rwa [inf_eq_left.mpr hUV, inf_eq_left.mpr (IsVi.le_fsuV hW)] at h2

omit [Finite G] in
theorem centralizer_le_of_conjSubgroup {U X : Subgroup G} {g : G} (hg : g ∈ X)
    (h : Subgroup.centralizer (conjSubgroup U g : Set G) ≤ X) :
    Subgroup.centralizer (U : Set G) ≤ X := by
  intro c hc
  have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer (conjSubgroup U g : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ (mem_conjSubgroup_iff.mp hu)
    calc u * (g⁻¹ * c * g) = g⁻¹ * ((g * u * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * u * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * c * g * u := by group
  have e : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
  rw [e]
  exact X.mul_mem (X.mul_mem hg (h hc')) (X.inv_mem hg)

omit [Finite G] in
theorem inf_centralizer_zpowers (V : Subgroup G) (x : G) :
    V ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      V ⊓ Subgroup.centralizer ({x} : Set G) := by
  refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le ?_)) ?_
  · rw [Set.singleton_subset_iff]
    exact Subgroup.mem_zpowers x
  · rintro c ⟨hcV, hc⟩
    refine ⟨hcV, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k, rfl⟩
    have hx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)
    exact ((Commute.zpow_left hx k).eq)

theorem rParam_cases (hNF : NatFacts) (hFM : FactMParam) (hFO : FactOddCodim)
    (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt) (hN : FactNot4213) (hFR : FactRootInv)
    (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt) (h63 : ASInputs.AS_E_6_3)
    (h612 : ASInputs.AS_E_6_12) (h664 : ASInputs.AS_E_6_6_four) (h614 : ASInputs.AS_E_6_14)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4)
    (h1114 : Stmt11_1_4) (hyp : Hyp11 G T L I n) {m : ℕ}
    (hm : KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n)
    {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) :
    (m : ℕ∞) < E3.rParam (fsuV T I) ∨
      (KindSL3 L (fsuV T I) n ∧ E3.rParam (fsuV T I) = m ∧
        ¬ Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  obtain ⟨hV, hn, hLV, hVL, hnat, hLM, hMN⟩ := natSetting h1102 hyp
  have hTV := T_le_normalizer_fsuV T I
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  obtain ⟨hmP, hdim⟩ := hFM G L (fsuV T I) M n m hV hn hLV hVL hnat hm hLM hMN
  have hm2 : 2 ≤ m := by rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hr := le_rParam hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331 h1102 h1103 hyp hm
  rcases lt_or_eq_of_le hr with hlt | heq
  · exact Or.inl hlt
  obtain ⟨U, hUV, hUC, hUm⟩ := exists_eq_rParam (heq ▸ ENat.natCast_ne_top m)
  have hUm' : E3.mQuot (fsuV T I) U = m := by
    rw [← heq] at hUm
    exact_mod_cast hUm
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    omega
  have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun h =>
    hUC fun x hx => inf_centralizer_le_normalizer h1103 hyp hUV hU1 ⟨h hx, hx⟩
  have hnres : ¬ twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (fsuV T I : Set G) := fun hres =>
    hCM (centralizer_le_of_lt hFM hFO hFH hS44 hN h4213 h311 h63 h612 h664 h614 h331 h1102
      h1103 h1104 hyp hm hUV hres (by omega)).1
  have hHN := inf_centralizer_le_normalizer h1103 hyp hUV hU1
  obtain ⟨y, hyH, ⟨k, hyk⟩, hyC⟩ : ∃ y ∈ M ⊓ Subgroup.centralizer (U : Set G),
      (∃ k : ℕ, y ^ 2 ^ k = 1) ∧ y ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnres ((twoPrimeResidual_le_of_forall hHN fun y hy h2 => hcon y hy h2).trans
      (inf_le_inf_right _ inf_le_left))
  have hyN : y ∈ Subgroup.normalizer (fsuV T I : Set G) := hHN hyH
  set φ := conjHomL (fsuV T I) (Subgroup.normalizer (fsuV T I : Set G)) le_rfl with hφdef
  have hker : ∀ z (hz : z ∈ Subgroup.normalizer (fsuV T I : Set G)),
      φ ⟨z, hz⟩ = 1 ↔ z ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro z hz
    rw [← MonoidHom.mem_ker, ker_conjHomL, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  have hpow : ∀ j : ℕ, φ ⟨y ^ j, Subgroup.pow_mem _ hyN j⟩ = φ ⟨y, hyN⟩ ^ j := by
    intro j
    rw [← map_pow]
    rfl
  set d := orderOf (φ ⟨y, hyN⟩) with hddef
  have hd1 : d ≠ 1 := fun h => hyC ((hker y hyN).mp (orderOf_eq_one_iff.mp h))
  have hdk : d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [← hpow]
    refine (hker _ _).mpr ?_
    rw [hyk]
    exact Subgroup.one_mem _)
  have h2d : 2 ∣ d := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdk
    rw [hj]
    rcases j with _ | j
    · exact absurd (by rw [hj, pow_zero]) hd1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  set x := y ^ (d / 2) with hxdef
  have hxN : x ∈ Subgroup.normalizer (fsuV T I : Set G) := Subgroup.pow_mem _ hyN _
  have hxord : orderOf (φ ⟨x, hxN⟩) = 2 := by
    rw [show φ ⟨x, hxN⟩ = φ ⟨y, hyN⟩ ^ (d / 2) from hpow (d / 2)]
    exact orderOf_pow_orderOf_div (orderOf_pos _).ne' h2d
  have hx2 : x ^ 2 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    refine (hker _ (Subgroup.pow_mem _ hxN 2)).mp ?_
    rw [show (⟨x ^ 2, Subgroup.pow_mem _ hxN 2⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G))) =
      ⟨x, hxN⟩ ^ 2 from rfl, map_pow, ← hxord, pow_orderOf_eq_one]
  have hxC : x ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    intro h
    rw [(hker x hxN).mpr h, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  have hxM : x ∈ M ⊓ Subgroup.normalizer (fsuV T I : Set G) := ⟨M.pow_mem hyH.1 _, hxN⟩
  have hxU : x ∈ Subgroup.centralizer (U : Set G) := Subgroup.pow_mem _ hyH.2 _
  have hUx : U ≤ fsuV T I ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro u hu
    refine ⟨hUV hu, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    rw [Set.mem_singleton_iff.mp hw]
    exact (Subgroup.mem_centralizer_iff.mp hxU u hu).symm
  have hle1 := E3.mQuot_mono (V := fsuV T I) hUx
  have hle2 : m ≤ E3.mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hxN' : Subgroup.zpowers x ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hA1 : autI hV (Subgroup.zpowers x) ≠ ⊥ := by
      rw [Ne, autI_eq_bot_iff hV hxN']
      exact fun h => hxC (h (Subgroup.mem_zpowers x))
    have hA2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
      have hxk : x ^ 2 ^ k = 1 := by
        rw [hxdef, ← pow_mul, mul_comm, pow_mul, hyk, one_pow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxk)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have := E3.mParam_le_rkIdx_fixV (autI_mono hV (Subgroup.zpowers_le.mpr hxM.1))
      (B6.isPGroup_autOn hA2 (fsuV T I)) hA1
    rwa [E3.rkIdx_fixV_autI hV hxN', inf_centralizer_zpowers, hmP] at this
  have hxm : E3.mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer ({x} : Set G)) = m := by
    omega
  have hUeq : U = fsuV T I ⊓ Subgroup.centralizer ({x} : Set G) := by
    have hadd := E3.mQuot_add hUx inf_le_left
    rw [hUm', hxm] at hadd
    have h0 : E3.mQuot (fsuV T I ⊓ Subgroup.centralizer ({x} : Set G)) U = 0 := by omega
    exact (E3.mQuot_eq_zero_iff ((isPGroup_fsuV hyp).to_le inf_le_left) hUx).mp h0
  obtain ⟨i, W, hWx, hcase, g, hgL, hCg, hEg, hidxg, hTg⟩ := hFR G L (fsuV T I) M T n m hV hn
    hLV hVL hnat hm hLM hMN hTS hTV hyp.normal x hxM hx2 hxC hxm
  have hgN : g ∈ Subgroup.normalizer (fsuV T I : Set G) := hLV hgL
  have hWgV : conjSubgroup W g ≤ fsuV T I := by
    intro y' hy'
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp
      ((hWx.trans inf_le_left) (mem_conjSubgroup_iff.mp hy'))
    simpa [mul_assoc] using h
  obtain ⟨V₁', V₂', V₃', hV₁', hV₂', hV₃', h12, h23, -, hu2, -⟩ := exists_isVi hNF h1102 hyp
  rcases hcase with ⟨⟨hnSp4, hnG2⟩, rfl, hWeq⟩ | ⟨hSG, rfl⟩
  ·
    right
    have hSL3 : KindSL3 L (fsuV T I) n := by
      rcases kind_cases h1102 hyp with h | h | h
      · exact h
      · exact absurd h hnSp4
      · exact absurd h hnG2
    refine ⟨hSL3, heq.symm, fun hC2 => hCM ?_⟩
    have hW2 := eq_isVi_of_flag hNF h1102 hyp (Or.inr (Or.inl rfl)) hV₂ hWgV hCg hEg hidxg hTg
    rw [hUeq, ← hWeq]
    exact centralizer_le_of_conjSubgroup (hLM hgL) (hW2 ▸ hC2)
  ·
    exfalso
    have hW3 := eq_isVi_of_flag hNF h1102 hyp (Or.inr (Or.inr rfl)) hV₃' hWgV hCg hEg hidxg hTg
    have hC3 : Subgroup.centralizer (V₃' : Set G) ≤ M := by
      refine le_trans ?_ (h1114 G T L I n V₁' V₃' hyp hV₁' hV₃').1
      intro c hc
      refine ⟨Subgroup.centralizer_le_normalizer _ hc,
        Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (h12.trans h23) hc),
        fun v hv => ?_⟩
      rw [← Subgroup.mem_centralizer_iff.mp hc v hv, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    apply hCM
    rw [hUeq]
    exact (Subgroup.centralizer_le hWx).trans
      (centralizer_le_of_conjSubgroup (hLM hgL) (hW3 ▸ hC3))

theorem sParam_eq (hFM : FactMParam) (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt)
    (hN : FactNot4213) (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt) (h63 : ASInputs.AS_E_6_3)
    (h664 : ASInputs.AS_E_6_6_four) (h614 : ASInputs.AS_E_6_14) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) {m : ℕ}
    (hm : KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n)
    (hV : IsElemAbelian 2 (fsuV T I)) : E3.sParam hV = m := by
  obtain ⟨-, hn, hLV, hVL, hnat, -, -⟩ := natSetting h1102 hyp
  have hmP := (hFM G L (fsuV T I) ⊤ n m hV hn hLV hVL hnat hm le_top
    (inf_le_right.trans (normalizer_fsuV_le h331 hyp))).1
  have hr := le_rParam hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331 h1102 h1103 hyp hm
  unfold E3.sParam
  rw [hmP, min_eq_right hr]
  rfl

end CFSG.Quasithin.Vol2.Ch11.SecB
