module

public import CFSG.Quasithin.Vol2.Ch12Sec8Three
public import CFSG.Quasithin.Vol2.Ch12Sec8Four
public import CFSG.Quasithin.Background.F8
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.EmptyFaithful.S142Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coreIn_centralizerMod_le {V₁ V H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V₁ : Set G)) (hVN : V ≤ Subgroup.normalizer (V₁ : Set G)) :
    coreIn (centralizerMod V₁ H V) H ≤ centralizerMod V₁ H (conjClosure V H) := by
  intro x hx
  obtain ⟨hxH, hxc⟩ := hx
  have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) := hHN hxH
  refine ⟨hxH, hxN, fun u hu => ?_⟩
  suffices key : u ∈ Subgroup.normalizer (V₁ : Set G) ∧ x * u * x⁻¹ * u⁻¹ ∈ V₁ from key.2
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hu
    have hgN := hHN hg
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN (hVN hv)) (Subgroup.inv_mem _ hgN), ?_⟩
    have h1 : (g⁻¹ * x * g) * v * (g⁻¹ * x * g)⁻¹ * v⁻¹ ∈ V₁ := (hxc g hg).2.2 v hv
    have h2 := (Subgroup.mem_normalizer_iff.mp hgN _).mp h1
    have e : x * (g * v * g⁻¹) * x⁻¹ * (g * v * g⁻¹)⁻¹ =
        g * ((g⁻¹ * x * g) * v * (g⁻¹ * x * g)⁻¹ * v⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  | one => exact ⟨Subgroup.one_mem _, by simp⟩
  | mul a b _ _ iha ihb =>
    refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, ?_⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp iha.1 _).mp ihb.2
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact V₁.mul_mem iha.2 h2
  | inv a _ iha =>
    refine ⟨Subgroup.inv_mem _ iha.1, ?_⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ iha.1) _).mp (V₁.inv_mem iha.2)
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h2

variable {T M L : Subgroup G}

namespace Hyp1281Two

theorem normalizer_omegaOneCenter (h : Hyp1281Two G T M L) :
    Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) =
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  le_antisymm (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
    (Subgroup.centralizer_le_normalizer _)

theorem uOfL22_abelian_of_forall (h : Hyp1281Two G T M L)
    (hall : ∀ H : Subgroup G, IsHz T M L H → IsMulCommutative ↥(conjClosure (VZ T M) H)) :
    IsMulCommutative ↥(uOfL22 T M) := by
  have := hall _ h.isHz_normalizer
  rwa [h.normalizer_omegaOneCenter] at this

theorem commutator_eq_bot_of_abelian (h : Hyp1281Two G T M L)
    (hU : IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : VZ T M ⊓ conjSub g (VZ T M) ≠ ⊥) :
    ⁅VZ T M, conjSub g (VZ T M)⁆ = ⊥ := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  set V := VZ T M with hVdef
  set Z := quasithinOmegaOneCenter T with hZdef
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  have hxV : (x : G) ∈ V := (Subgroup.mem_inf.mp x.2).1
  have hxVg : (x : G) ∈ conjSub g V := (Subgroup.mem_inf.mp x.2).2
  have hx1' : (x : G) ≠ 1 := fun he => hx1 (Subtype.ext he)
  have hZ2 := h.card_omegaOneCenter
  obtain ⟨z, hzZ⟩ : ∃ z : Z, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ2
  have hz1 : (z : G) ≠ 1 := fun he => hzZ (Subtype.ext he)
  have hzV : (z : G) ∈ V := le_conjClosure _ _ z.2
  obtain ⟨l, hlL, hl⟩ := h.exists_conj_eq hxV hzV hx1' hz1
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := hVred.2.1 (h.le hlL)
  have hZle : Z ≤ conjSub (l * g) V := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    · have hwz : w = z := by
        have h1 := hy ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))
        have h2 := hy z hzZ
        exact congrArg Subtype.val (h1.trans h2.symm)
      rw [hwz, conjSub_mul, ← hl]
      exact mul_mem_conjSub hxVg
  obtain ⟨x', hx'N, hx'eq⟩ := h.exists_eq_conjSub hZle
  have hVU : V ≤ uOfL22 T M := le_conjClosure _ _
  have hVlgU : conjSub (l * g) V ≤ uOfL22 T M := by
    rw [hx'eq]
    intro u hu
    rw [mem_conjSub] at hu
    have hx'C : x' ∈ Subgroup.centralizer (Z : Set G) := h.normalizer_omegaOneCenter ▸ hx'N
    have : x' * (x'⁻¹ * u * x') * x'⁻¹ ∈ uOfL22 T M := mem_conjClosure hx'C hu
    simpa [mul_assoc] using this
  have hcomm : ⁅V, conjSub (l * g) V⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hab : (⟨a, hVU ha⟩ : uOfL22 T M) * ⟨b, hVlgU hb⟩ = ⟨b, hVlgU hb⟩ * ⟨a, hVU ha⟩ :=
      hU.is_comm.comm _ _
    have hab' : a * b = b * a := congrArg Subtype.val hab
    rw [Subgroup.mem_bot, commutatorElement_def, hab']
    group
  have e1 : conjSub l V = V := by
    ext u
    rw [mem_conjSub]
    constructor
    · intro hu
      have := (Subgroup.mem_normalizer_iff.mp hlN _).mp hu
      simpa [mul_assoc] using this
    · intro hu
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) _).mp hu
      simpa using this
  have : conjSub l ⁅V, conjSub g V⁆ = ⊥ := by
    rw [← conjSub_commutator, e1, ← conjSub_mul]
    exact hcomm
  exact (conjSub_eq_bot_iff l).mp this

theorem hypF81_of_commutator (h : Hyp1281Two G T M L)
    (h3 : ∀ g : G, VZ T M ⊓ conjSub g (VZ T M) ≠ ⊥ → ⁅VZ T M, conjSub g (VZ T M)⁆ = ⊥)
    {H : Subgroup G} (hH : IsHz T M L H) :
    HypF81 T (VZ T M) L (quasithinOmegaOneCenter T) H := by
  obtain ⟨hVred, hVT⟩ := h.isTwoReducedIn
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hA := h.almostSpecialHyp hH
  have hHz := (h.isHz_iff).mp hH
  have hlOne : L₁Of L (quasithinOmegaOneCenter T) = ⊥ := by
    rw [← lOne_eq_L₁Of]
    exact h.lOne_eq_bot
  have hTM : T ≤ M := h.inM.2
  have hsylG : IsSylowTwoOf T ⊤ := by
    have := isSylowTwoOf_of_sylow S (le_top : (S : Subgroup G) ≤ ⊤)
    rwa [hS] at this
  have hMchar : CharTwo M := by
    have := charTwo_of_inH h.qtke.2.1 S (hS ▸ inH_of_inM h.inM)
    exact this
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hA.sylow_LT
  refine
    { sylow := hsylG
      elemAbelian := hVred.2.2.1
      normalizes_L := hTM.trans h.normal
      oTwoRes_eq := by rw [oTwoRes_eq_oTwoUpper]; exact h.residual
      charTwo_L := CharTwo.of_normal hMchar h.le
        (Subgroup.normal_subgroupOf_of_le_normalizer h.normal)
      reduced := h.isTwoReducedIn_LT
      cT := ?_
      V₁_ne_bot := h.omegaOneCenter_ne_bot
      V₁_le_V := le_conjClosure _ _
      T_normalizes_V₁ := hA.T_le_normV₁
      weak_a := ?_
      V₁_lt_V := hA.irred.1
      irred := ?_
      H_normalizes_V₁ := hA.H_le
      L₁T_le_H := by rw [hlOne, bot_sup_eq]; exact hHz.1.1
      charTwo_H := hA.charTwo
      ker_le := ?_
      o2_trivial := ?_ }
  ·
    apply le_antisymm
    · rw [← h.centralizer]
      exact inf_le_inf_right _ le_sup_right
    · refine le_inf hOT ?_
      rw [← h.centralizer]
      exact inf_le_right
  ·
    intro g hg
    apply h3 g⁻¹
    intro hbot
    apply hg
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ VZ T M ⊓ conjSub g⁻¹ (VZ T M) := ⟨le_conjClosure _ _ hw.1, hw.2⟩
    rwa [hbot] at this
  ·
    intro W hZW hWV hTW
    rw [hlOne, bot_sup_eq] at hTW
    have := hA.irred.2.2.2 W hZW hWV
    rw [h.lOne_eq_bot, bot_sup_eq] at this
    exact this hTW
  ·
    rw [← h.lemma_12_8_4_four hH]
    exact coreIn_centralizerMod_le hA.H_le (hA.V_le_T.trans hA.T_le_normV₁)
  ·
    by_contra hne
    obtain ⟨N, hN⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have hNM : N = M := h.unique.2 N ⟨hN.1, le_sup_left.trans hN.2⟩
    exact hHz.2.2 (hNM ▸ le_sup_right.trans hN.2)

theorem abelian_of_hypF81 {H : Subgroup G}
    (hF : HypF81 T (VZ T M) L (quasithinOmegaOneCenter T) H) :
    IsMulCommutative ↥(conjClosure (VZ T M) H) :=
  (F8.isElemAbelian_conjClosure hF).1

theorem lemma_12_8_6 (h : Hyp1281Two G T M L) :
    ((∀ H : Subgroup G, IsHz T M L H → IsMulCommutative ↥(conjClosure (VZ T M) H)) ↔
      IsMulCommutative ↥(uOfL22 T M)) ∧
    (IsMulCommutative ↥(uOfL22 T M) ↔
      ∀ g : G, VZ T M ⊓ conjSub g (VZ T M) ≠ ⊥ → ⁅VZ T M, conjSub g (VZ T M)⁆ = ⊥) ∧
    ((∀ g : G, VZ T M ⊓ conjSub g (VZ T M) ≠ ⊥ → ⁅VZ T M, conjSub g (VZ T M)⁆ = ⊥) ↔
      ∀ H : Subgroup G, IsHz T M L H → HypF81 T (VZ T M) L (quasithinOmegaOneCenter T) H) := by
  have h12 : (∀ H : Subgroup G, IsHz T M L H → IsMulCommutative ↥(conjClosure (VZ T M) H)) →
      IsMulCommutative ↥(uOfL22 T M) := h.uOfL22_abelian_of_forall
  have h23 : IsMulCommutative ↥(uOfL22 T M) →
      ∀ g : G, VZ T M ⊓ conjSub g (VZ T M) ≠ ⊥ → ⁅VZ T M, conjSub g (VZ T M)⁆ = ⊥ :=
    fun hU g hg => h.commutator_eq_bot_of_abelian hU hg
  have h34 : (∀ g : G, VZ T M ⊓ conjSub g (VZ T M) ≠ ⊥ → ⁅VZ T M, conjSub g (VZ T M)⁆ = ⊥) →
      ∀ H : Subgroup G, IsHz T M L H → HypF81 T (VZ T M) L (quasithinOmegaOneCenter T) H :=
    fun h3 H hH => h.hypF81_of_commutator h3 hH
  have h41 : (∀ H : Subgroup G, IsHz T M L H →
      HypF81 T (VZ T M) L (quasithinOmegaOneCenter T) H) →
      ∀ H : Subgroup G, IsHz T M L H → IsMulCommutative ↥(conjClosure (VZ T M) H) :=
    fun h4 H hH => abelian_of_hypF81 (h4 H hH)
  exact ⟨⟨h12, fun hU => h41 (h34 (h23 hU))⟩, ⟨h23, fun h3 => h12 (h41 (h34 h3))⟩,
    ⟨h34, fun h4 => h23 (h12 (h41 h4))⟩⟩

end Hyp1281Two

end CFSG.Quasithin
