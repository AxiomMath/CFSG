module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Ctx
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace C2of3324

theorem vec_add_eq_zero : ∀ x y : L3.Vec, x + y = 0 → x = y := by decide

theorem fin2_cases : ∀ a b c : Fin 2, b ≠ c → a = b ∨ a = c := by decide

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem false_case2
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h20 : Stmt3_3_20) (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hi : IsC134Case2 (L ⊔ T) T L)
    (hD : ¬ D ≤ Subgroup.normalizer (pCoreOf 2
      (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  obtain ⟨hQO, hOQ, -, hTQ⟩ := C23.qData hTL
  set Q := c134Q (L ⊔ T) L with hQ
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hLQ, -, β, hβs, hβk, hβe⟩, -⟩ := hi
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  set Z := quasithinOmegaOneCenter T with hZdef
  have hOq : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQq : Q ≤ qL L T := hQO.trans hOq
  have hQT : qL L T ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hQO
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hcz : ∀ {u : G}, u ∈ Z → ∀ t ∈ T, t * u * t⁻¹ = u := fun hu t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hTZ ht) _ hu
    rw [← this]
    group
  set α₃ := Ctx3324.alpha3 hF α with hα₃
  have hα₃s : Function.Surjective α₃ := Ctx3324.alpha3_surjective hF hα.1
  have hα₃k : ∀ ℓ : ↥L, α₃ ℓ = 1 → (ℓ : G) ∈ pCoreOf 2 L := Ctx3324.mem_of_alpha3 hF hα
  set β₂ := (Ctx3324.z2Coords hF 2).comp β with hβ₂
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hβ₂i : Function.Injective β₂ := (Ctx3324.z2Coords_injective hF 2).comp hβi
  have hβ₂s : Function.Surjective β₂ := (Ctx3324.z2Coords_surjective hF 2).comp hβs
  have hβ₂e : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β₂ v) i = L3.act (α₃ ℓ) (Multiplicative.toAdd (β₂ u) i) :=
    Ctx3324.z2_equiv hF β hβe
  have hβ₂mul : ∀ (a b : ↥Q) (i : Fin 2), Multiplicative.toAdd (β₂ (a * b)) i =
      Multiplicative.toAdd (β₂ a) i + Multiplicative.toAdd (β₂ b) i := fun a b i => by
    simp only [map_mul, toAdd_mul, Pi.add_apply]
  have hβ₂inv : ∀ (a : ↥Q) (i : Fin 2),
      Multiplicative.toAdd (β₂ a⁻¹) i = Multiplicative.toAdd (β₂ a) i := fun a i => by
    rw [map_inv, toAdd_inv]
    exact vec_neg _
  obtain ⟨z₀, ⟨hz₀Z, hz₀VL⟩, hz₀1⟩ := Ctx3324.exists_z₀ h h38 h39 hTL
  have hVL := Ctx3324.vL_le h
  have hz₀Q : z₀ ∈ Q := (hVL hz₀VL).1
  set I := (T.subgroupOf L).map α₃ with hI
  have hI2 : IsPGroup 2 I := (hT2.comap_of_injective L.subtype L.subtype_injective).map α₃
  have hIodd : ¬ 2 ∣ I.index := by
    have h1 := Subgroup.index_map_dvd (T.subgroupOf L) hα₃s
    have h2 : T.relIndex L ∣ T.index :=
      (C45.relIndex_eq hTL) ▸ Subgroup.relIndex_dvd_index_of_le le_sup_right
    exact fun h3 => hTidx ((h3.trans h1).trans h2)
  obtain ⟨e, he⟩ := Mod3323.exists_fix hI2 hIodd
  have hfixI : ∀ {u : ↥Q}, (u : G) ∈ Z → ∀ i, Multiplicative.toAdd (β₂ u) i = 0 ∨
      Multiplicative.toAdd (β₂ u) i = e := by
    intro u hu i
    apply he
    rintro _ ⟨t, ht, rfl⟩
    exact (hβ₂e t u u (hcz hu _ ht).symm i).symm
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, Multiplicative.toAdd (β₂ ⟨z₀, hz₀Q⟩) i₀ = e := by
    by_contra hcon
    push Not at hcon
    apply hz₀1
    have h1 : β₂ ⟨z₀, hz₀Q⟩ = β₂ 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      funext i
      rcases hfixI (u := ⟨z₀, hz₀Q⟩) hz₀Z i with h0 | h1
      · exact h0
      · exact absurd h1 (hcon i)
    exact congrArg Subtype.val (hβ₂i h1)
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin 2, j₀ ≠ i₀ := ⟨i₀ + 1, by
    have := fin2_cases i₀ 0 1 (by decide)
    rcases this with rfl | rfl <;> decide⟩
  have hij : ∀ i : Fin 2, i = i₀ ∨ i = j₀ := fun i => fin2_cases i i₀ j₀ hj₀.symm
  obtain ⟨κ, hκact, hκe⟩ : ∃ κ : L3.Vec →+ L3.Vec, (∀ g v, κ (L3.act g v) = L3.act g (κ v)) ∧
      κ e = Multiplicative.toAdd (β₂ ⟨z₀, hz₀Q⟩) j₀ := by
    rcases hfixI (u := ⟨z₀, hz₀Q⟩) hz₀Z j₀ with h0 | h1
    · exact ⟨0, fun g v => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, L3.act_zero],
        by rw [h0, AddMonoidHom.zero_apply]⟩
    · exact ⟨AddMonoidHom.id _, fun g v => rfl, by rw [h1, AddMonoidHom.id_apply]⟩
  let W : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ Q, Multiplicative.toAdd (β₂ ⟨g, hg⟩) j₀ =
        κ (Multiplicative.toAdd (β₂ ⟨g, hg⟩) i₀)}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Q.mul_mem ha hb, ?_⟩
        show Multiplicative.toAdd (β₂ (⟨a, ha⟩ * ⟨b, hb⟩)) j₀ =
          κ (Multiplicative.toAdd (β₂ (⟨a, ha⟩ * ⟨b, hb⟩)) i₀)
        rw [hβ₂mul, hβ₂mul, ha', hb', map_add]
      one_mem' := ⟨Q.one_mem, by
        show Multiplicative.toAdd (β₂ 1) j₀ = κ (Multiplicative.toAdd (β₂ 1) i₀)
        simp only [map_one, toAdd_one, Pi.zero_apply, map_zero]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Q.inv_mem ha, ?_⟩
        show Multiplicative.toAdd (β₂ (⟨a, ha⟩)⁻¹) j₀ =
          κ (Multiplicative.toAdd (β₂ (⟨a, ha⟩)⁻¹) i₀)
        rw [hβ₂inv, hβ₂inv]
        exact ha' }
  have hWQ : W ≤ Q := fun g hg => hg.1
  have hWmem : ∀ {g : G} (hg : g ∈ W), Multiplicative.toAdd (β₂ ⟨g, hWQ hg⟩) j₀ =
      κ (Multiplicative.toAdd (β₂ ⟨g, hWQ hg⟩) i₀) := fun hg => hg.2
  set γW : ↥W →* Multiplicative L3.Vec :=
    (Sec3323.coord (F := ZMod 2) i₀).comp (β₂.comp (Subgroup.inclusion hWQ)) with hγW
  have hγWi : Function.Injective γW := by
    intro u u' huu
    have h0 : Multiplicative.toAdd (β₂ ⟨u, hWQ u.2⟩) i₀ =
        Multiplicative.toAdd (β₂ ⟨u', hWQ u'.2⟩) i₀ := congrArg Multiplicative.toAdd huu
    have h1 : Multiplicative.toAdd (β₂ ⟨u, hWQ u.2⟩) j₀ =
        Multiplicative.toAdd (β₂ ⟨u', hWQ u'.2⟩) j₀ := by
      rw [hWmem u.2, hWmem u'.2, h0]
    have h2 : β₂ ⟨u, hWQ u.2⟩ = β₂ ⟨u', hWQ u'.2⟩ :=
      Multiplicative.toAdd.injective (funext fun i => by
        rcases hij i with hi | hi <;> rw [hi]
        · exact h0
        · exact h1)
    exact Subtype.ext (congrArg (fun x : ↥Q => (x : G)) (hβ₂i h2))
  have hγWs : Function.Surjective γW := by
    intro y
    obtain ⟨q, hq⟩ := hβ₂s (Multiplicative.ofAdd fun i =>
      if i = i₀ then Multiplicative.toAdd y else κ (Multiplicative.toAdd y))
    have hqi : ∀ i, Multiplicative.toAdd (β₂ q) i =
        if i = i₀ then Multiplicative.toAdd y else κ (Multiplicative.toAdd y) := fun i => by
      rw [hq]
      rfl
    have hqW : (q : G) ∈ W := ⟨q.2, by
      show Multiplicative.toAdd (β₂ q) j₀ = κ (Multiplicative.toAdd (β₂ q) i₀)
      rw [hqi j₀, hqi i₀, ite_eq_right hj₀, ite_eq_left rfl]⟩
    refine ⟨⟨q, hqW⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (β₂ q) i₀ = Multiplicative.toAdd y
    rw [hqi i₀, ite_eq_left rfl]
  set βW : ↥W ≃* Multiplicative L3.Vec := MulEquiv.ofBijective γW ⟨hγWi, hγWs⟩ with hβW
  have hβWe : ∀ (ℓ : ↥L) (u v : ↥W), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (βW v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (βW u)) :=
    fun ℓ u v huv => hβ₂e ℓ ⟨u, hWQ u.2⟩ ⟨v, hWQ v.2⟩ huv i₀
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    Main3324.le_normalizer_of_conj fun ℓ hℓ g hg => by
      have h1 : ℓ * g * ℓ⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hℓ) g).mp (hWQ hg)
      refine ⟨h1, ?_⟩
      rw [hβ₂e ⟨ℓ, hℓ⟩ ⟨g, hWQ hg⟩ ⟨_, h1⟩ rfl j₀, hβ₂e ⟨ℓ, hℓ⟩ ⟨g, hWQ hg⟩ ⟨_, h1⟩ rfl i₀,
        hWmem hg, hκact]
  have hz₀W : z₀ ∈ W := ⟨hz₀Q, by rw [hi₀]; exact hκe.symm⟩
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    Ctx3324.le_normalizer_of_trans βW α₃ hLW hα₃s hβWe hz₀W hz₀1 hTL fun t ht => hcz hz₀Z t ht
  have hLVL : L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun ℓ hℓ =>
    Main3324.mem_normalizer_comm
      (((le_conjClosure L T).trans (le_normalizer_conjClosure _ _)) hℓ)
      (Subgroup.le_normalizer hℓ)
  have hWVL : W ≤ ⁅vPlus L T, L⁆ :=
    Ctx3324.le_of_conj_z₀ βW α₃ hLW hα₃s hβWe hz₀W hz₀1 hz₀VL hLVL
  have hqW : qL L T ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mp (hWVL.trans fun x hx => (hVL hx).2)
  have hWq : W ≤ qL L T := hWQ.trans hQq
  have hZ : ∀ y (hy : y ∈ L), L3.act (α₃ ⟨y, hy⟩) (Multiplicative.toAdd (βW ⟨z₀, hz₀W⟩)) =
      Multiplicative.toAdd (βW ⟨z₀, hz₀W⟩) → y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy hfix
    have hfe : L3.act (α₃ ⟨y, hy⟩) e = e := by
      rw [← hi₀]
      exact hfix
    refine Ctx3324.centZ h hTL hy fun u hu => ?_
    have huQ : u ∈ Q := (hVL hu.2).1
    have hyu : y * u * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hy) u).mp huQ
    have h1 : (⟨_, hyu⟩ : ↥Q) = ⟨u, huQ⟩ := hβ₂i (Multiplicative.toAdd.injective (funext fun i => by
      rw [hβ₂e ⟨y, hy⟩ ⟨u, huQ⟩ ⟨_, hyu⟩ rfl i]
      rcases hfixI (u := ⟨u, huQ⟩) hu.1 i with h0 | h1
      · rw [h0, L3.act_zero]
      · rw [h1, hfe]))
    exact congrArg Subtype.val h1
  obtain ⟨σ, X, hXX, hTX, hS3, hXTe, hXL, -, hWXc, hWO, hirr, hcomm, hv₁, hliftC, hNC⟩ :=
    Ctx3324.xStructU h hTL hLW hTW hWq hqW βW α₃ hα₃s hα₃k hβWe hz₀W hz₀Z hz₀1 hZ
  have hD' : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) := by
    rw [hXTe]
    exact hD
  have hXN : ∀ {S : Subgroup G}, L ≤ Subgroup.normalizer (S : Set G) →
      X ≤ Subgroup.normalizer ((X ⊓ S : Subgroup G) : Set G) :=
    fun hS x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hS (hXL hx))
  let act : ↥L → Matrix (Fin 3) (Fin 3) F := fun l => ((α l : GL (Fin 3) F) : Matrix _ _ F)
  have hβe' : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i) :=
    fun a u v huv i => by simpa [moduleAct, act] using hβe a u v huv i
  have hS1 : L ≤ Subgroup.normalizer (Sec3323.sumFst β : Set G) :=
    Sec3323.le_normalizer_sumFst β act hLQ hβe'
  have hW1 : NCAtMost X ⊥ (X ⊓ Sec3323.sumFst β) 1 := by
    have := Ctx3324.ncAtMost_inf (X := X) (c := 1)
      (bot_le : (⊥ : Subgroup G) ≤ Sec3323.sumFst β)
      (by rw [Sec3323.relIndex_fst β hF hβs hβk]; norm_num)
    rwa [inf_bot_eq] at this
  have hW2 : NCAtMost X (X ⊓ Sec3323.sumFst β) (X ⊓ Q) 1 :=
    Ctx3324.ncAtMost_inf (Sec3323.sumFst_le β) (by rw [Sec3323.relIndex_snd β hF hβs]; norm_num)
  have hW3 : NCAtMost X (X ⊓ Q) (X ⊓ pCoreOf 2 L) 0 := ncAtMost_zero_of_commutator_le (le_inf
    (commutator_le_right_of_le_normalizer (inf_le_left.trans Subgroup.le_normalizer))
    ((Subgroup.commutator_mono inf_le_right hXL).trans hOQ))
  have h5 : ¬ HasNoncentralTwoChief X 5 := by
    rw [Chief3323.hasNoncentralTwoChief_iff]
    have h12 := hW1.add hW2 bot_le (inf_le_inf_left X (Sec3323.sumFst_le β)) inf_le_left
      (hXN hS1)
    have h123 := h12.add hW3 bot_le (inf_le_inf_left X hQO) inf_le_left (hXN hLQ)
    exact (h123.add hNC bot_le inf_le_left le_rfl
      (hXN (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))).mono (by norm_num)
  have hmoved : ∀ q : ↥Q, Multiplicative.toAdd (β₂ q) i₀ = 0 → ∀ r (hrL : r ∈ L),
      L3.act (α₃ ⟨r, hrL⟩) (Multiplicative.toAdd (β₂ q) j₀) ≠ Multiplicative.toAdd (β₂ q) j₀ →
        ⁅r, (q : G)⁆ ∉ Subgroup.zpowers z₀ := by
    intro q hq0 r hrL hmv hcz'
    have hrq : r * q * r⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hrL) q).mp q.2
    have hcW : ((⟨r * q * r⁻¹, hrq⟩ * q⁻¹ : ↥Q) : G) ∈ W := Subgroup.zpowers_le.mpr hz₀W hcz'
    have hc := hWmem hcW
    rw [show (⟨((⟨r * q * r⁻¹, hrq⟩ * q⁻¹ : ↥Q) : G), hWQ hcW⟩ : ↥Q) =
        ⟨r * q * r⁻¹, hrq⟩ * q⁻¹ from rfl, hβ₂mul, hβ₂mul, hβ₂inv, hβ₂inv,
      hβ₂e ⟨r, hrL⟩ q ⟨_, hrq⟩ rfl, hβ₂e ⟨r, hrL⟩ q ⟨_, hrq⟩ rfl, hq0, L3.act_zero, add_zero,
      map_zero] at hc
    exact hmv (vec_add_eq_zero _ _ hc)
  have hgo : ∀ q : ↥Q, Multiplicative.toAdd (β₂ q) i₀ = 0 → ∀ w : L3.Vec, w ≠ 0 → w ≠ e1 →
      Multiplicative.toAdd (β₂ q) j₀ = L3.act σ⁻¹ w →
        ∃ r ∈ ⁅pCoreOf 2 X, X⁆, ⁅r, (q : G)⁆ ∉ Subgroup.zpowers z₀ := by
    intro q hq0 w hw0 hw1 hqw
    obtain ⟨γ, hγ, hγw⟩ := move_check w hw0 hw1
    obtain ⟨r, hr, hrL, er⟩ := hliftC γ (mem_rSet.mp hγ)
    refine ⟨r, hr, hmoved q hq0 r hrL ?_⟩
    rw [hqw, er, L3.act_mul, L3.act_mul, L3.act_act_inv]
    intro h1
    apply hγw
    have h2 := congrArg (L3.act σ) h1
    rwa [L3.act_act_inv, L3.act_act_inv] at h2
  obtain ⟨q₁, hq₁⟩ := hβ₂s (Multiplicative.ofAdd fun i =>
    if i = j₀ then L3.act σ⁻¹ ![0, 1, 0] else 0)
  obtain ⟨q₂, hq₂⟩ := hβ₂s (Multiplicative.ofAdd fun i =>
    if i = j₀ then L3.act σ⁻¹ ![0, 0, 1] else 0)
  have hq₁i : ∀ i, Multiplicative.toAdd (β₂ q₁) i =
      if i = j₀ then L3.act σ⁻¹ ![0, 1, 0] else 0 := fun i => by
    rw [hq₁]
    rfl
  have hq₂i : ∀ i, Multiplicative.toAdd (β₂ q₂) i =
      if i = j₀ then L3.act σ⁻¹ ![0, 0, 1] else 0 := fun i => by
    rw [hq₂]
    rfl
  have hQX : Q ≤ pCoreOf 2 (X ⊔ T) :=
    Ctx3324.le_pCoreOf_sup (hQq.trans hQT) (hXL.trans hLQ) hTQ hQ2
  refine Main3324.false_of_config h20 h hXX hTX hS3 hD' h5 hz₀Z hz₀W (hXL.trans hLW) hWXc hWO
    hirr hcomm hv₁ (a₁ := q₁) (a₂ := q₂) (hQX q₁.2) (hQX q₂.2) ?_
  obtain ⟨h21, h22, h31, h32, h41, h42⟩ := e23_check
  rintro a (rfl | rfl | rfl)
  · exact hgo q₁ (by rw [hq₁i, ite_eq_right hj₀.symm]) _ h21 h22 (by rw [hq₁i, ite_eq_left rfl])
  · exact hgo q₂ (by rw [hq₂i, ite_eq_right hj₀.symm]) _ h31 h32 (by rw [hq₂i, ite_eq_left rfl])
  · refine hgo (q₁ * q₂) ?_ _ h41 h42 ?_
    · rw [hβ₂mul, hq₁i, hq₂i, ite_eq_right hj₀.symm, ite_eq_right hj₀.symm, add_zero]
    · rw [hβ₂mul, hq₁i, hq₂i, ite_eq_left rfl, ite_eq_left rfl, L3.act_add]

end C2of3324

end CFSG.Quasithin.H13
