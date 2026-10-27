module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem card_mulAut_of_card_four {V : Subgroup G} (hV : IsElemAbelian 2 V) (h4 : Nat.card V = 4) :
    Nat.card (MulAut ↥V) = 6 := by
  have hsq : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have := @card_mulAut_eq ↥V (commGroupOfElemAbelian hV) _ hsq
  have hrk : @rk ↥V _ = 2 := by
    unfold rk
    rw [h4, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  rw [hrk] at this
  rw [this]
  simp [Fin.prod_univ_two]

omit [Finite G] in
theorem autOn_eq_bot_iff {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn X V = ⊥ ↔ X ≤ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h x hx
    have hmem : conjAct V ⟨x, hX hx⟩ ∈ autOn X V := mem_autOn_iff_exists.mpr ⟨x, hX hx, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact A4.conjAct_eq_one_iff.mp hmem
  · intro h
    refine eq_bot_iff.mpr fun a ha => ?_
    obtain ⟨x, hxV, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
    exact Subgroup.mem_bot.mpr (A4.conjAct_eq_one_iff.mpr (h hxX))

theorem isTwoReducedIn_VZ_of_inM {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) : IsTwoReducedIn M (VZ T M) ∧ VZ T M ≤ T := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M hM.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M (VZ T M) := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  refine ⟨hVred, ?_⟩
  have := le_sylow_of_isTwoReducedIn S hSM hVred
  rwa [hS] at this

structure Hyp14118 (T Mc M : Subgroup G) : Prop where
  qtfe : quasithinQTFE14Cat G T Mc
  lemma14111 : ∃ C₂ : Subgroup G, Lemma14111Concl T Mc C₂
  isMf : IsMf T Mc M
  rank_two : Nat.card (VZ T M) = 4

namespace Hyp14118

variable {T Mc M : Subgroup G}

theorem ne (hyp : Hyp14118 T Mc M) : M ≠ Mc := hyp.isMf.2.1

theorem inM (hyp : Hyp14118 T Mc M) : InM T M := hyp.isMf.1.1

theorem twoReduced (hyp : Hyp14118 T Mc M) : IsTwoReducedIn M (VZ T M) :=
  (isTwoReducedIn_VZ_of_inM hyp.qtfe hyp.inM).1

theorem VZ_le (hyp : Hyp14118 T Mc M) : VZ T M ≤ T :=
  (isTwoReducedIn_VZ_of_inM hyp.qtfe hyp.inM).2

theorem le_normalizer (hyp : Hyp14118 T Mc M) :
    M ≤ Subgroup.normalizer (VZ T M : Set G) := hyp.twoReduced.2.1

theorem hyp1417 (hyp : Hyp14118 T Mc M) : Hyp14117 T Mc M Mc (VZ T M) :=
  ⟨hyp.inM, hyp.twoReduced, VZ_ne_bot hyp.qtfe.omegaOneCenter_ne_bot, hyp.qtfe.inM_mc,
    hyp.ne.symm, Or.inr rfl⟩

theorem autOn_eq_top (hyp : Hyp14118 T Mc M) : autOn M (VZ T M) = ⊤ :=
  autOn_eq_top_of_card_VZ_eq_four hyp.qtfe hyp.inM hyp.ne hyp.rank_two

theorem card_autOn (hyp : Hyp14118 T Mc M) : Nat.card (autOn M (VZ T M)) = 6 := by
  rw [hyp.autOn_eq_top, Subgroup.card_top]
  exact card_mulAut_of_card_four hyp.twoReduced.2.2.1 hyp.rank_two

theorem not_le_centralizer (hyp : Hyp14118 T Mc M) :
    ¬ T ≤ Subgroup.centralizer (VZ T M : Set G) := fun hTV =>
  hyp.ne (eq_mc_of_le_centralizer_VZ hyp.qtfe hyp.inM hTV)

theorem autOn_T_ne_bot (hyp : Hyp14118 T Mc M) : autOn T (VZ T M) ≠ ⊥ := fun hb =>
  hyp.not_le_centralizer ((autOn_eq_bot_iff (hyp.inM.2.trans hyp.le_normalizer)).mp hb)

theorem isPGroup_autOn_T (hyp : Hyp14118 T Mc M) : IsPGroup 2 (autOn T (VZ T M)) := by
  unfold autOn
  exact (hyp.qtfe.sylow.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe (hyp.inM.2.trans hyp.le_normalizer)).symm).map _

theorem card_autOn_T (hyp : Hyp14118 T Mc M) : Nat.card (autOn T (VZ T M)) = 2 := by
  have hTM : T ≤ M := hyp.inM.2
  obtain ⟨k, hk⟩ := hyp.isPGroup_autOn_T.exists_card_eq
  have hdvd : Nat.card (autOn T (VZ T M)) ∣ 6 :=
    hyp.card_autOn ▸ Subgroup.card_dvd_of_le (A4.autOn_mono hTM)
  have hne : Nat.card (autOn T (VZ T M)) ≠ 1 := fun h1 =>
    hyp.autOn_T_ne_bot (Subgroup.card_eq_one.mp h1)
  rw [hk] at hdvd hne ⊢
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h4 : 4 ∣ 6 := by simpa using this.trans hdvd
    omega
  interval_cases k
  · simp at hne
  · rfl

theorem eq_bot_of_normal_isPGroup (hyp : Hyp14118 T Mc M) {Q : Subgroup (MulAut ↥(VZ T M))}
    (hQA : Q ≤ autOn M (VZ T M)) (hQn : autOn M (VZ T M) ≤ Subgroup.normalizer (Q : Set _))
    (hQ2 : IsPGroup 2 Q) : Q = ⊥ := by
  obtain ⟨D, hDM, hMD, hD2, -, hDQ⟩ := A4.exists_preimage_section hyp.le_normalizer hQA hQn hQ2
  have hDC : D ≤ Subgroup.centralizer (VZ T M : Set G) := by
    refine hyp.twoReduced.2.2.2 D hDM hMD fun d hd => ?_
    obtain ⟨k, hk⟩ := hD2 d hd
    exact ⟨k, hk.2⟩
  refine eq_bot_iff.mpr fun q hq => ?_
  obtain ⟨x, hxD, hxq⟩ := hDQ q hq
  have h1 : A4.actionOn (VZ T M) M hyp.le_normalizer x = 1 :=
    (A4.actionOn_eq_one_iff hyp.le_normalizer x).mpr (hDC hxD)
  rw [Subgroup.mem_bot, ← hxq, h1]

theorem exists_P3 (hyp : Hyp14118 T Mc M) :
    ∃ P : Subgroup (MulAut ↥(VZ T M)), P.Normal ∧ Nat.card P = 3 := by
  have hcard : Nat.card (MulAut ↥(VZ T M)) = 6 :=
    card_mulAut_of_card_four hyp.twoReduced.2.2.1 hyp.rank_two
  have : Finite (MulAut ↥(VZ T M)) := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 (MulAut ↥(VZ T M))))
  have h3 : Nat.card (P : Subgroup (MulAut ↥(VZ T M))) = 3 := by
    rw [P.card_eq_multiplicity, hcard]
    have h : Nat.factorization 6 3 = 1 := by norm_num [Nat.factorization]
    rw [h]
    norm_num
  have hidx : (P : Subgroup (MulAut ↥(VZ T M))).index = 2 := by
    have := (P : Subgroup (MulAut ↥(VZ T M))).card_mul_index
    rw [h3, hcard] at this
    omega
  exact ⟨P, Subgroup.normal_of_index_eq_two hidx, h3⟩

theorem exists_Y₀ (hyp : Hyp14118 T Mc M) :
    ∃ (Y₀ : Subgroup G) (P : Subgroup (MulAut ↥(VZ T M))), P.Normal ∧ Nat.card P = 3 ∧ Y₀ ≤ M ∧
      M ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Y₀ ∧ autOn Y₀ (VZ T M) = P ∧
      P ⊔ autOn T (VZ T M) = ⊤ ∧ Y₀ ⊔ T = M := by
  obtain ⟨P, hPn, hP3⟩ := hyp.exists_P3
  have hMV := hyp.le_normalizer
  have hTM : T ≤ M := hyp.inM.2
  have hcard : Nat.card (MulAut ↥(VZ T M)) = 6 :=
    card_mulAut_of_card_four hyp.twoReduced.2.2.1 hyp.rank_two
  set φ : ↥M →* MulAut ↥(VZ T M) := A4.actionOn (VZ T M) M hMV with hφ
  set Y₀ : Subgroup G := (P.comap φ).map M.subtype with hY₀
  have hmem : ∀ x : G, x ∈ Y₀ ↔ ∃ hx : x ∈ M, φ ⟨x, hx⟩ ∈ P := by
    intro x
    rw [hY₀, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hP'⟩
      exact ⟨⟨x, hx⟩, hP', rfl⟩
  have hY₀M : Y₀ ≤ M := Subgroup.map_subtype_le _
  have key : ∀ m ∈ M, ∀ y ∈ Y₀, m * y * m⁻¹ ∈ Y₀ := by
    intro m hm y hy
    obtain ⟨hyM, hyP⟩ := (hmem y).mp hy
    have hmym : m * y * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)
    refine (hmem _).mpr ⟨hmym, ?_⟩
    have e : φ ⟨m * y * m⁻¹, hmym⟩ = φ ⟨m, hm⟩ * φ ⟨y, hyM⟩ * (φ ⟨m, hm⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hPn.conj_mem _ hyP (φ ⟨m, hm⟩)
  have hnorm : M ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key m hm y, fun hy => ?_⟩
    have := key m⁻¹ (M.inv_mem hm) _ hy
    simpa [mul_assoc] using this
  have hCY₀ : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Y₀ := by
    intro c hc
    refine (hmem c).mpr ⟨hc.1, ?_⟩
    have : φ ⟨c, hc.1⟩ = 1 := (A4.actionOn_eq_one_iff hMV _).mpr hc.2
    rw [this]
    exact P.one_mem
  have hY₀P : autOn Y₀ (VZ T M) = P := by
    ext a
    constructor
    · intro ha
      obtain ⟨y, hyV, hyY, rfl⟩ := mem_autOn_iff_exists.mp ha
      obtain ⟨hyM, hyP⟩ := (hmem y).mp hyY
      exact hyP
    · intro ha
      have ha' : a ∈ autOn M (VZ T M) := by
        rw [hyp.autOn_eq_top]
        trivial
      obtain ⟨m, hmV, hmM, rfl⟩ := mem_autOn_iff_exists.mp ha'
      exact mem_autOn_iff_exists.mpr ⟨m, hmV, (hmem m).mpr ⟨hmM, ha⟩, rfl⟩
  have hPT : P ⊔ autOn T (VZ T M) = ⊤ := by
    have h3 : 3 ∣ Nat.card (P ⊔ autOn T (VZ T M) : Subgroup _) :=
      hP3 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : 2 ∣ Nat.card (P ⊔ autOn T (VZ T M) : Subgroup _) :=
      hyp.card_autOn_T ▸ Subgroup.card_dvd_of_le le_sup_right
    have h6 : 6 ∣ Nat.card (P ⊔ autOn T (VZ T M) : Subgroup _) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 2) h3 h2
    have hle : Nat.card (P ⊔ autOn T (VZ T M) : Subgroup _) ≤ 6 :=
      hcard ▸ Subgroup.card_le_card_group _
    have hpos : 0 < Nat.card (P ⊔ autOn T (VZ T M) : Subgroup _) := Nat.card_pos
    have := Nat.le_of_dvd hpos h6
    exact Subgroup.card_eq_iff_eq_top _ |>.mp (by omega)
  refine ⟨Y₀, P, hPn, hP3, hY₀M, hnorm, hCY₀, hY₀P, hPT, ?_⟩
  refine le_antisymm (sup_le hY₀M hTM) fun m hm => ?_
  have ha : conjAct (VZ T M) ⟨m, hMV hm⟩ ∈ P ⊔ autOn T (VZ T M) := by
    rw [hPT]
    trivial
  obtain ⟨p, hp, tb, htb, hptb⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  have hp' : p ∈ autOn Y₀ (VZ T M) := by
    rw [hY₀P]
    exact hp
  obtain ⟨y, hyV, hyY, rfl⟩ := mem_autOn_iff_exists.mp hp'
  obtain ⟨t, htV, htT, rfl⟩ := mem_autOn_iff_exists.mp htb
  have hyM : y ∈ M := hY₀M hyY
  have htM : t ∈ M := hTM htT
  have hcM : (y * t)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (M.mul_mem hyM htM)) hm
  have hcV : (y * t)⁻¹ * m ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hcM
  have hcC : (y * t)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) := by
    refine (A4.conjAct_eq_one_iff (g := ⟨(y * t)⁻¹ * m, hcV⟩)).mp ?_
    have e : conjAct (VZ T M) ⟨(y * t)⁻¹ * m, hcV⟩ =
        (conjAct (VZ T M) ⟨y, hyV⟩ * conjAct (VZ T M) ⟨t, htV⟩)⁻¹ *
          conjAct (VZ T M) ⟨m, hMV hm⟩ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e, hptb]
    exact inv_mul_cancel _
  have hc' : t * ((y * t)⁻¹ * m) * t⁻¹ ∈ Y₀ := key t htM _ (hCY₀ ⟨hcM, hcC⟩)
  have e : m = (y * (t * ((y * t)⁻¹ * m) * t⁻¹)) * t := by group
  rw [e]
  exact (Y₀ ⊔ T).mul_mem ((Y₀ ⊔ T).mul_mem (Subgroup.mem_sup_left hyY) (Subgroup.mem_sup_left hc'))
    (Subgroup.mem_sup_right htT)

theorem Rc_le (hyp : Hyp14118 T Mc M) : pCoreOf 2 (M ⊓ Mc) ≤ T := by
  have := hyp.hyp1417.pCoreOf_le_sylow hyp.qtfe
  rwa [inf_comm] at this

theorem autOn_Rc_eq (h113 : StageLemma14113) (hyp : Hyp14118 T Mc M) :
    autOn (pCoreOf 2 (M ⊓ Mc)) (VZ T M) = autOn T (VZ T M) := by
  have hne : autOn (pCoreOf 2 (M ⊓ Mc)) (VZ T M) ≠ ⊥ := by
    have := lemma_14_1_17_one h113 hyp.qtfe hyp.hyp1417
    rwa [inf_comm] at this
  have hle : autOn (pCoreOf 2 (M ⊓ Mc)) (VZ T M) ≤ autOn T (VZ T M) := A4.autOn_mono hyp.Rc_le
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : 1 < Nat.card (autOn (pCoreOf 2 (M ⊓ Mc)) (VZ T M)) :=
    Subgroup.one_lt_card_iff_ne_bot _ |>.mpr hne
  rw [hyp.card_autOn_T]
  omega

theorem lemma_14_1_18_two (h113 : StageLemma14113) (hyp : Hyp14118 T Mc M) :
    pCoreOf 2 (M ⊓ Mc) ⊔ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) = T ∧
      M ⊓ Mc = (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ pCoreOf 2 (M ⊓ Mc) := by
  have hMV := hyp.le_normalizer
  have hTM : T ≤ M := hyp.inM.2
  have hRcT := hyp.Rc_le
  have hRcM : pCoreOf 2 (M ⊓ Mc) ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hbar := hyp.autOn_Rc_eq h113
  have hfac : ∀ (x : G) (hx : x ∈ M), conjAct (VZ T M) ⟨x, hMV hx⟩ ∈ autOn T (VZ T M) →
      ∃ ρ ∈ pCoreOf 2 (M ⊓ Mc), ρ⁻¹ * x ∈ Subgroup.centralizer (VZ T M : Set G) := by
    intro x hx hxT
    rw [← hbar] at hxT
    obtain ⟨ρ, hρV, hρR, hρeq⟩ := mem_autOn_iff_exists.mp hxT
    refine ⟨ρ, hρR, ?_⟩
    have hρM : ρ ∈ M := hRcM hρR
    have hρxV : ρ⁻¹ * x ∈ Subgroup.normalizer (VZ T M : Set G) := hMV (M.mul_mem (M.inv_mem hρM) hx)
    refine (A4.conjAct_eq_one_iff (g := ⟨ρ⁻¹ * x, hρxV⟩)).mp ?_
    have e : conjAct (VZ T M) ⟨ρ⁻¹ * x, hρxV⟩ =
        (conjAct (VZ T M) ⟨ρ, hρV⟩)⁻¹ * conjAct (VZ T M) ⟨x, hMV hx⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e, hρeq]
    exact inv_mul_cancel _
  have hC : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ M ⊓ Mc :=
    hyp.hyp1417.centralizer_le hyp.qtfe
  refine ⟨?_, ?_⟩
  · refine le_antisymm (sup_le hRcT inf_le_left) fun t ht => ?_
    have hρ := hfac t (hTM ht) (mem_autOn_iff_exists.mpr ⟨t, hMV (hTM ht), ht, rfl⟩)
    obtain ⟨ρ, hρR, hρc⟩ := hρ
    have : t = ρ * (ρ⁻¹ * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hρR)
      (Subgroup.mem_sup_right ⟨T.mul_mem (T.inv_mem (hRcT hρR)) ht, hρc⟩)
  · refine le_antisymm (fun m hm => ?_) (sup_le hC (pCoreOf_le 2 _))
    set K : Subgroup (MulAut ↥(VZ T M)) := autOn (M ⊓ Mc) (VZ T M) with hK
    have hTK : autOn T (VZ T M) ≤ K := A4.autOn_mono (le_inf hTM hyp.qtfe.t_le_mc)
    have hKA : K ≤ autOn M (VZ T M) := A4.autOn_mono inf_le_left
    have hKdvd : Nat.card K ∣ 6 := hyp.card_autOn ▸ Subgroup.card_dvd_of_le hKA
    have hTdvd : 2 ∣ Nat.card K := hyp.card_autOn_T ▸ Subgroup.card_dvd_of_le hTK
    have hKne6 : Nat.card K ≠ 6 := by
      intro h6
      apply hyp.ne
      have hKtop : K = autOn M (VZ T M) :=
        Subgroup.eq_of_le_of_card_ge hKA (by rw [hyp.card_autOn, h6])
      have hMle : M ≤ Mc := by
        intro m' hm'
        have hmem : conjAct (VZ T M) ⟨m', hMV hm'⟩ ∈ K := by
          rw [hKtop]
          exact mem_autOn_iff_exists.mpr ⟨m', hMV hm', hm', rfl⟩
        obtain ⟨x, hxV, hxMc, hxeq⟩ := mem_autOn_iff_exists.mp hmem
        have hxM : x ∈ M := hxMc.1
        have hcM : x⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hxM) hm'
        have hcV : x⁻¹ * m' ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hcM
        have hcC : x⁻¹ * m' ∈ Subgroup.centralizer (VZ T M : Set G) := by
          refine (A4.conjAct_eq_one_iff (g := ⟨x⁻¹ * m', hcV⟩)).mp ?_
          have e : conjAct (VZ T M) ⟨x⁻¹ * m', hcV⟩ =
              (conjAct (VZ T M) ⟨x, hxV⟩)⁻¹ * conjAct (VZ T M) ⟨m', hMV hm'⟩ := by
            rw [← map_inv, ← map_mul]
            rfl
          rw [e, hxeq]
          exact inv_mul_cancel _
        have : m' = x * (x⁻¹ * m') := by group
        rw [this]
        exact (M ⊓ Mc).mul_mem hxMc (hC ⟨hcM, hcC⟩) |>.2
      exact (hyp.inM.1.2 Mc hyp.qtfe.mc_max.1 hMle).symm
    have hKT : K = autOn T (VZ T M) := by
      refine (Subgroup.eq_of_le_of_card_ge hTK ?_).symm
      have : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) hKdvd
      rw [hyp.card_autOn_T]
      have hge : 2 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hTdvd
      have hcases : Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 4 ∨ Nat.card K = 5 ∨
          Nat.card K = 6 := by omega
      rcases hcases with h2 | h3 | h4 | h5 | h6
      · omega
      · rw [h3] at hTdvd
        omega
      · rw [h4] at hKdvd
        omega
      · rw [h5] at hKdvd
        omega
      · exact absurd h6 hKne6
    have hmem : conjAct (VZ T M) ⟨m, hMV hm.1⟩ ∈ autOn T (VZ T M) := by
      rw [← hKT]
      exact mem_autOn_iff_exists.mpr ⟨m, hMV hm.1, hm, rfl⟩
    obtain ⟨ρ, hρR, hρc⟩ := hfac m hm.1 hmem
    have : m = ρ * (ρ⁻¹ * m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hρR)
      (Subgroup.mem_sup_left ⟨M.mul_mem (M.inv_mem (hRcM hρR)) hm.1, hρc⟩)

theorem not_le_centralizer_P (hyp : Hyp14118 T Mc M) {P : Subgroup (MulAut ↥(VZ T M))}
    (hPT : P ⊔ autOn T (VZ T M) = ⊤) :
    ¬ autOn T (VZ T M) ≤ Subgroup.centralizer (P : Set (MulAut ↥(VZ T M))) := by
  intro h
  have hPc : P ≤ Subgroup.centralizer (autOn T (VZ T M) : Set (MulAut ↥(VZ T M))) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h hx) p hp).symm
  have hnorm : (⊤ : Subgroup (MulAut ↥(VZ T M))) ≤
      Subgroup.normalizer (autOn T (VZ T M) : Set (MulAut ↥(VZ T M))) := by
    rw [← hPT]
    exact sup_le (fun p hp => Subgroup.centralizer_le_normalizer _ (hPc hp))
      Subgroup.le_normalizer
  exact hyp.autOn_T_ne_bot (hyp.eq_bot_of_normal_isPGroup (A4.autOn_mono hyp.inM.2)
    (by rw [hyp.autOn_eq_top]; exact hnorm) hyp.isPGroup_autOn_T)

end Hyp14118

theorem nonempty_mulAut_mulEquiv_perm_three {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h4 : Nat.card V = 4) : Nonempty (MulAut ↥V ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hcard : Nat.card (MulAut ↥V) = 6 := card_mulAut_of_card_four hV h4
  have hthree : Nat.card {v : V // v ≠ 1} = 3 := by
    have : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have hone : Fintype.card {v : V // v = 1} = 1 := by simp
    rw [hone, ← Nat.card_eq_fintype_card, h4]
  let f : MulAut ↥V →* Equiv.Perm {v : V // v ≠ 1} :=
    { toFun := fun a => Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
      map_one' := by ext v; simp
      map_mul' := fun a b => by ext v; simp }
  have hf : Function.Injective f := by
    intro a b hab
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · simpa [f] using congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
  have hcard' : Nat.card (Equiv.Perm {v : V // v ≠ 1}) = 6 := by
    rw [Nat.card_perm, hthree]
    rfl
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hcard', hcard])
  have e : {v : V // v ≠ 1} ≃ Fin 3 :=
    (Finite.equivFin {v : V // v ≠ 1}).trans (finCongr hthree)
  exact ⟨(MulEquiv.ofBijective f hbij).trans e.permCongrHom⟩

end CFSG.Quasithin
