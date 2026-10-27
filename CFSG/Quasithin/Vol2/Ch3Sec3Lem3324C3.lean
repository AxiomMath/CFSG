module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Ctx
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace C3of3324

variable {G : Type} [Group G]

theorem b2_ne_one : b2 ≠ 1 := by
  intro h1
  have h2 := b2_check.2
  rw [h1, L3.act_one, vec_add_self] at h2
  exact e12_check.1 h2.symm

theorem exists_moved_dual {F : Type} [Field F] {g : GL (Fin 3) F} (hg : g ≠ 1) :
    ∃ u : Fin 3 → F, (moduleAct true g).mulVec u ≠ u := by
  by_contra hcon
  push Not at hcon
  apply hg
  have hM : moduleAct true g = 1 := Matrix.toLin'.injective (LinearMap.ext fun u => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    exact hcon u)
  simp only [moduleAct, ite_true, Matrix.transpose_eq_one] at hM
  have h1 : g⁻¹ = 1 := Units.ext (by rw [hM, Units.val_one])
  exact inv_eq_one.mp h1

variable [Finite G] {T M L D : Subgroup G}

theorem false_case3
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h20 : Stmt3_3_20) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hi : IsC134Case3 (L ⊔ T) T L)
    (hD : ¬ D ≤ Subgroup.normalizer (pCoreOf 2
      (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  obtain ⟨hQO, hOQ, -, hTQ⟩ := C23.qData hTL
  set Q := c134Q (L ⊔ T) L with hQ
  set W := centerOf Q with hW
  obtain ⟨⟨n, F, _, _, α, hFc, hα, ⟨hLZ, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩,
    ⟨hLQ, hZQ, β, hβs, hβk, hβe⟩⟩, -⟩ := hi
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  set Z := quasithinOmegaOneCenter T with hZdef
  have hOq : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQq : Q ≤ qL L T := hQO.trans hOq
  have hQT : qL L T ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hQO
  have hWQ : W ≤ Q := inf_le_left
  set α₃ := Ctx3324.alpha3 hF α with hα₃
  have hα₃s : Function.Surjective α₃ := Ctx3324.alpha3_surjective hF hα.1
  have hα₃k : ∀ ℓ : ↥L, α₃ ℓ = 1 → (ℓ : G) ∈ pCoreOf 2 L := Ctx3324.mem_of_alpha3 hF hα
  set γW : ↥W →* Multiplicative L3.Vec :=
    (Sec3323.coord 0).comp ((Ctx3324.z2Coords hF 1).comp β₁) with hγW
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  have hc0 : Function.Injective (Sec3323.coord (F := ZMod 2) (k := 1) 0) := fun x y hxy =>
    Multiplicative.toAdd.injective (funext fun i => by
      fin_cases i
      exact congrArg Multiplicative.toAdd hxy)
  have hγWi : Function.Injective γW := hc0.comp ((Ctx3324.z2Coords_injective hF 1).comp hβ₁i)
  have hγWs : Function.Surjective γW :=
    Sec3323.coord_zero_surj ((Ctx3324.z2Coords_surjective hF 1).comp hβ₁s)
  set βW : ↥W ≃* Multiplicative L3.Vec := MulEquiv.ofBijective γW ⟨hγWi, hγWs⟩ with hβW
  have hβWe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (βW v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (βW u)) :=
    fun ℓ u v huv => Ctx3324.z2_equiv hF β₁ hβ₁e ℓ u v huv 0
  obtain ⟨z₀, ⟨hz₀Z, hz₀VL⟩, hz₀1⟩ := Ctx3324.exists_z₀ h h38 h39 hTL
  have hVL := Ctx3324.vL_le h
  have hVLW : ⁅vPlus L T, L⁆ ≤ W := fun x hx =>
    ⟨(hVL hx).1, Subgroup.centralizer_le hQq (hVL hx).2⟩
  have hz₀W : z₀ ∈ W := hVLW hz₀VL
  have hLVL : L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun ℓ hℓ =>
    Main3324.mem_normalizer_comm
      (((le_conjClosure L T).trans (le_normalizer_conjClosure _ _)) hℓ)
      (Subgroup.le_normalizer hℓ)
  have hWVL : W ≤ ⁅vPlus L T, L⁆ :=
    Ctx3324.le_of_conj_z₀ βW α₃ hLZ hα₃s hβWe hz₀W hz₀1 hz₀VL hLVL
  have hqW : qL L T ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mp (hWVL.trans fun x hx => (hVL hx).2)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := fun t ht =>
    C23.mem_normalizer_centerOf (hTQ ht)
  have hWq : W ≤ qL L T := hWQ.trans hQq
  have hρs : Function.Surjective (rhoV βW) := fun γ => by
    obtain ⟨ℓ, rfl⟩ := hα₃s γ
    exact ⟨_, rhoV_eq βW hLZ α₃ hβWe ℓ⟩
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hcz : ∀ {u : G}, u ∈ Z → ∀ t ∈ T, t * u * t⁻¹ = u := fun hu t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hTZ ht) _ hu
    rw [← this]
    group
  have hne : Multiplicative.toAdd (βW ⟨z₀, hz₀W⟩) ≠ 0 := fun h0 => hz₀1 (congrArg Subtype.val
    (eq_of_toAdd_beta βW (u := ⟨z₀, hz₀W⟩) (u' := 1) (by rw [toAdd_beta_one]; exact h0)))
  have hZ : ∀ y (hy : y ∈ L), L3.act (α₃ ⟨y, hy⟩) (Multiplicative.toAdd (βW ⟨z₀, hz₀W⟩)) =
      Multiplicative.toAdd (βW ⟨z₀, hz₀W⟩) → y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy hfix
    refine Ctx3324.centZ h hTL hy fun u hu => ?_
    have huW : u ∈ W := hVLW hu.2
    rcases Ctx3324.fix_of_odd (rhoV βW) hTW hT2 hTidx hρs hne
        (fun t ht => act_rhoV_of_conj βW (g := ⟨t, hTW ht⟩) (u := ⟨z₀, hz₀W⟩) (hcz hz₀Z t ht))
        (v := Multiplicative.toAdd (βW ⟨u, huW⟩))
        (fun t ht => act_rhoV_of_conj βW (g := ⟨t, hTW ht⟩) (u := ⟨u, huW⟩) (hcz hu.1 t ht))
      with h0 | h1
    · have hu1 : u = 1 := congrArg Subtype.val (eq_of_toAdd_beta βW (u := ⟨u, huW⟩) (u' := 1)
        (by rw [toAdd_beta_one]; exact h0))
      rw [hu1]
      group
    · have hyu : y * u * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLZ hy) u).mp huW
      have := eq_of_toAdd_beta βW (u := ⟨_, hyu⟩) (u' := ⟨u, huW⟩) (by
        rw [hβWe ⟨y, hy⟩ ⟨u, huW⟩ ⟨_, hyu⟩ rfl, h1]
        exact hfix)
      exact congrArg Subtype.val this
  obtain ⟨σ, X, hXX, hTX, hS3, hXTe, hXL, -, hWXc, hWO, hirr, hcomm, hv₁, hliftC, hNC⟩ :=
    Ctx3324.xStructU h hTL hLZ hTW hWq hqW βW α₃ hα₃s hα₃k hβWe hz₀W hz₀Z hz₀1 hZ
  have hD' : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) := by
    rw [hXTe]
    exact hD
  have hXN : ∀ {S : Subgroup G}, L ≤ Subgroup.normalizer (S : Set G) →
      X ≤ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G) :=
    fun hS x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hS (hXL hx))
  have hW1 : NCAtMost X ⊥ (X ⊓ W) 1 := by
    have := Ctx3324.ncAtMost_inf (X := X) (c := 1) (bot_le : (⊥ : Subgroup G) ≤ W)
      (by rw [Sec3323.relIndex_one hF β₁ hβ₁s hβ₁k]; norm_num)
    rwa [inf_bot_eq] at this
  have hW2 : NCAtMost X (X ⊓ W) (X ⊓ Sec3323.sumFst β) 1 :=
    Ctx3324.ncAtMost_inf (Sec3323.le_sumFst β hZQ hβk)
      (by rw [Sec3323.relIndex_fst β hF hβs hβk]; norm_num)
  have hW3 : NCAtMost X (X ⊓ Sec3323.sumFst β) (X ⊓ Q) 1 :=
    Ctx3324.ncAtMost_inf (Sec3323.sumFst_le β) (by rw [Sec3323.relIndex_snd β hF hβs]; norm_num)
  have hW4 : NCAtMost X (X ⊓ Q) (X ⊓ pCoreOf 2 L) 0 := ncAtMost_zero_of_commutator_le (le_inf
    (commutator_le_right_of_le_normalizer (inf_le_left.trans Subgroup.le_normalizer))
    ((Subgroup.commutator_mono inf_le_right hXL).trans hOQ))
  have hS1 : L ≤ Subgroup.normalizer (Sec3323.sumFst β : Set G) :=
    Sec3323.le_normalizer_sumFst β (fun l => moduleAct true (α l : GL (Fin 3) F)) hLQ hβe
  have h5 : ¬ HasNoncentralTwoChief X 5 := by
    rw [Chief3323.hasNoncentralTwoChief_iff]
    have h12 := hW1.add hW2 bot_le (inf_le_inf_left X (Sec3323.le_sumFst β hZQ hβk))
      inf_le_left (hXN hLZ)
    have h123 := h12.add hW3 bot_le (inf_le_inf_left X (Sec3323.sumFst_le β)) inf_le_left
      (hXN hS1)
    have h1234 := h123.add hW4 bot_le (inf_le_inf_left X hQO) inf_le_left (hXN hLQ)
    exact h1234.add hNC bot_le inf_le_left le_rfl
      (hXN (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
  obtain ⟨r, hr, hrL, er⟩ := hliftC b2 (mem_rSub.mpr b2_check.1)
  have hαr : (α ⟨r, hrL⟩ : GL (Fin 3) F) ≠ 1 := by
    intro h1
    have h2 : α₃ ⟨r, hrL⟩ = 1 := (Ctx3324.alpha3_eq_one hF ⟨r, hrL⟩).mpr (Subtype.ext h1)
    rw [er] at h2
    apply b2_ne_one
    calc b2 = σ * (σ⁻¹ * b2 * σ) * σ⁻¹ := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨u, hu⟩ := exists_moved_dual hαr
  have hmoved : ∀ q : ↥Q, (∃ i, (moduleAct true (α ⟨r, hrL⟩ : GL (Fin 3) F)).mulVec
      (Multiplicative.toAdd (β q) i) ≠ Multiplicative.toAdd (β q) i) →
        ⁅r, (q : G)⁆ ∉ Subgroup.zpowers z₀ := by
    rintro q ⟨i, hi⟩ hcz'
    have hrq : r * q * r⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hrL) q).mp q.2
    have hk : (⟨r * q * r⁻¹, hrq⟩ * q⁻¹ : ↥Q) ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact Subgroup.zpowers_le.mpr hz₀W hcz'
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    apply hi
    rw [← hβe ⟨r, hrL⟩ q ⟨_, hrq⟩ rfl i, hk]
  obtain ⟨q₁, hq₁⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 u))
  obtain ⟨q₂, hq₂⟩ := hβs (Multiplicative.ofAdd (Pi.single 1 u))
  have hQX : Q ≤ pCoreOf 2 (X ⊔ T) :=
    Ctx3324.le_pCoreOf_sup (hQq.trans hQT) (hXL.trans hLQ) hTQ hQ2
  refine Main3324.false_of_config h20 h hXX hTX hS3 hD' h5 hz₀Z hz₀W (hXL.trans hLZ) hWXc hWO
    hirr hcomm hv₁ (a₁ := q₁) (a₂ := q₂) (hQX q₁.2) (hQX q₂.2) ?_
  rintro a (rfl | rfl | rfl)
  · exact ⟨r, hr, hmoved q₁ ⟨0, by rw [hq₁]; simpa using hu⟩⟩
  · exact ⟨r, hr, hmoved q₂ ⟨1, by rw [hq₂]; simpa using hu⟩⟩
  · refine ⟨r, hr, hmoved (q₁ * q₂) ⟨0, ?_⟩⟩
    rw [map_mul, hq₁, hq₂]
    simpa using hu

end C3of3324

end CFSG.Quasithin.H13
