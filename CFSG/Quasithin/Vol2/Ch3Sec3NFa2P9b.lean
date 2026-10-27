module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Orb9

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem isPGroup_two_of_sq (H : Subgroup G) (h : ∀ x ∈ H, x ^ 2 = 1) : IsPGroup 2 ↥H :=
  fun x => ⟨1, Subtype.ext (by simpa using h x.1 x.2)⟩

theorem commutator_le_left_of_le_normalizer' {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ⁅V, L⁆ ≤ V := by
  refine Subgroup.commutator_le.2 fun v hv l hl => ?_
  have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) v⁻¹).1 (V.inv_mem hv)
  have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact V.mul_mem hv h1

theorem exists_fixed_ne_one_of_isPGroup [Finite G] {P X : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hX : IsPGroup 2 ↥X) (hne : X ≠ ⊥) :
    ∃ f ∈ X, f ≠ 1 ∧ ∀ t ∈ P, t * f * t⁻¹ = f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥P ↥X :=
    { smul := fun t x => ⟨(t : G) * x * (t : G)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (hPX t.2) x).1 x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        simp
      mul_smul := fun a b x => by
        apply Subtype.ext
        change ((a : G) * (b : G)) * (x : G) * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc] }
  letI := act
  have hdvd : 2 ∣ Nat.card ↥X := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hX
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne ((Subgroup.eq_bot_iff_card X).2 (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1 : (1 : ↥X) ∈ MulAction.fixedPoints ↥P ↥X := by
    rw [MulAction.mem_fixedPoints]
    intro t
    apply Subtype.ext
    change (t : G) * 1 * (t : G)⁻¹ = 1
    simp
  obtain ⟨b, hb, hab⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥X hdvd h1
  refine ⟨b.1, b.2, fun hb1 => hab (Subtype.ext hb1.symm), fun t ht => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hb ⟨t, ht⟩)

theorem mem_omegaOne_of_fixed {T : Subgroup G} {f : G} (hfT : f ∈ T) (hf2 : f ^ 2 = 1)
    (hfc : ∀ t ∈ T, t * f * t⁻¹ = f) : f ∈ quasithinOmegaOneCenter T :=
  Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hfT, Subgroup.mem_centralizer_iff.2 fun t ht =>
    mul_inv_eq_iff_eq_mul.1 (hfc t ht)⟩, hf2⟩

theorem mem_normalizer_conjClosure_of {Z L : Subgroup G} {k : G}
    (hkL : k ∈ Subgroup.normalizer (L : Set G)) (hkZ : k ∈ Subgroup.normalizer (Z : Set G)) :
    k ∈ Subgroup.normalizer (conjClosure Z L : Set G) := by
  have key : ∀ k : G, k ∈ Subgroup.normalizer (L : Set G) →
      k ∈ Subgroup.normalizer (Z : Set G) →
      ∀ x ∈ conjClosure Z L, k * x * k⁻¹ ∈ conjClosure Z L := by
    intro k hkL hkZ
    have hle : conjClosure Z L ≤ (conjClosure Z L).comap (MulAut.conj k).toMonoidHom := by
      refine conjClosure_le fun h hh z hz => ?_
      rw [Subgroup.mem_comap]
      show k * (h * z * h⁻¹) * k⁻¹ ∈ conjClosure Z L
      have hkh : k * h * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hkL h).1 hh
      have hkz : k * z * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hkZ z).1 hz
      have e : k * (h * z * h⁻¹) * k⁻¹ = (k * h * k⁻¹) * (k * z * k⁻¹) * (k * h * k⁻¹)⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure hkh hkz
    exact fun x hx => hle hx
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => key k hkL hkZ x hx, fun hx => ?_⟩
  have := key k⁻¹ (Subgroup.inv_mem _ hkL) (Subgroup.inv_mem _ hkZ) _ hx
  have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem mem_normalizer_commutator_of {A B : Subgroup G} {k : G}
    (hkA : k ∈ Subgroup.normalizer (A : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G)) :
    k ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ k : G, k ∈ Subgroup.normalizer (A : Set G) →
      k ∈ Subgroup.normalizer (B : Set G) → ∀ x ∈ ⁅A, B⁆, k * x * k⁻¹ ∈ ⁅A, B⁆ := by
    intro k hkA hkB
    have hle : ⁅A, B⁆ ≤ (⁅A, B⁆ : Subgroup G).comap (MulAut.conj k).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [Subgroup.mem_comap]
      show k * ⁅a, b⁆ * k⁻¹ ∈ ⁅A, B⁆
      have e : k * ⁅a, b⁆ * k⁻¹ = ⁅k * a * k⁻¹, k * b * k⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hkA a).1 ha)
        ((Subgroup.mem_normalizer_iff.1 hkB b).1 hb)
    exact fun x hx => hle hx
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => key k hkA hkB x hx, fun hx => ?_⟩
  have := key k⁻¹ (Subgroup.inv_mem _ hkA) (Subgroup.inv_mem _ hkB) _ hx
  have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rwa [e] at this

end Generic

namespace A2Cfg

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}
variable (c : A2Cfg G T M L D H K q)
include c

theorem vPlus_le_T : vPlus L T ≤ T := by
  obtain ⟨-, -, -, hVO, hOR, hRT, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  exact hVO.trans (hOR.trans hRT)

theorem inf_centralizer_L_eq_bot (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) :
    vPlus L T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨hVe, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  by_contra hne
  have hFT : T ≤ Subgroup.normalizer
      ((vPlus L T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hTV (c.TL.trans (F7.normalizer_le_normalizer_centralizer _))
  have hF2 : IsPGroup 2 ↥(vPlus L T ⊓ Subgroup.centralizer (L : Set G)) :=
    isPGroup_two_of_sq _ fun x hx => hVe.2 x (Subgroup.mem_inf.1 hx).1
  obtain ⟨f, hfF, hf1, hfT⟩ :=
    exists_fixed_ne_one_of_isPGroup c.nf.hyp.sylow.1 hFT hF2 hne
  obtain ⟨hfV, hfC⟩ := Subgroup.mem_inf.1 hfF
  have hfZ : f ∈ quasithinOmegaOneCenter T :=
    mem_omegaOne_of_fixed (c.vPlus_le_T hfV) (hVe.2 f hfV) hfT
  have hZC : f ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) := by
    rw [c.mPlus_eq]
    exact Subgroup.mem_inf.2 ⟨hfZ, hfC⟩
  rw [c.nf.inf_centralizer_mPlus_eq_bot h36 h5 h128 h37 h38 h39, Subgroup.mem_bot] at hZC
  exact hf1 hZC

theorem inf_commutator_ne (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) :
    quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆ ≠ ⊥ := by
  obtain ⟨hVe, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hWV : ⁅vPlus L T, L⁆ ≤ vPlus L T := commutator_le_left_of_le_normalizer' hLV
  have hWne : ⁅vPlus L T, L⁆ ≠ ⊥ := by
    intro hbot
    have hC : vPlus L T ≤ Subgroup.centralizer (L : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem : ⁅v, l⁆ ∈ ⁅vPlus L T, L⁆ := Subgroup.commutator_mem_commutator hv hl
      rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
      exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hmem)).symm
    have h1 : vPlus L T ⊓ Subgroup.centralizer (L : Set G) = vPlus L T := inf_eq_left.2 hC
    rw [c.inf_centralizer_L_eq_bot h36 h5 h128 h37 h38 h39] at h1
    exact c.V_ne_bot h1.symm
  have hT2 : T ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_commutator_of (hTV ht) (c.TL ht)
  have hX2 : IsPGroup 2 ↥⁅vPlus L T, L⁆ :=
    isPGroup_two_of_sq _ fun x hx => hVe.2 x (hWV hx)
  obtain ⟨f, hfW, hf1, hfT⟩ := exists_fixed_ne_one_of_isPGroup c.nf.hyp.sylow.1 hT2 hX2 hWne
  have hfV : f ∈ vPlus L T := hWV hfW
  have hfZ : f ∈ quasithinOmegaOneCenter T :=
    mem_omegaOne_of_fixed (c.vPlus_le_T hfV) (hVe.2 f hfV) hfT
  intro h
  have hmem : f ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆ := Subgroup.mem_inf.2 ⟨hfZ, hfW⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hf1 hmem

theorem card_commutator_le (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) :
    Nat.card ↥⁅vPlus L T, L⁆ ≤ 2 ^ 6 := by
  classical
  obtain ⟨hTL, ⟨-⟩, hc, hmodE, -, -⟩ := c.site
  obtain ⟨-, hLV, -, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  obtain ⟨Z₀, hZ₀, -, π, hπ⟩ := hmodE
  have hZ₀bot : Z₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzf : z ∈ fixV (autOn L (vPlus L T)) := (Subgroup.mem_inf.1 (hZ₀ hz)).1
    have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
      (AutOn.mem_fixV_autOn_iff hLV z).1 hzf
    have h2 : (z : G) ∈ vPlus L T ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.2 ⟨z.2, hzC⟩
    rw [c.inf_centralizer_L_eq_bot h36 h5 h128 h37 h38 h39, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  obtain ⟨D₀⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => (hZ₀.trans inf_le_left) hz g hg)
  have hβ : Function.Injective D₀.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' := D₀.ker u hu
    rw [hZ₀bot, Subgroup.mem_bot] at hu'
    exact Subtype.ext hu'
  haveI : Finite (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Quasithin.B513N.card_wedge4]; norm_num)
  have hle := Nat.card_le_card_of_injective D₀.β hβ
  rw [CFSG.Quasithin.B513N.card_wedge4, AutOn.commV_autOn_eq hLV,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commutator_le_left_of_le_normalizer' hLV)).toEquiv]
    at hle
  exact hle

theorem vPlus_le_omegaOne_sup :
    vPlus L T ≤ quasithinOmegaOneCenter T ⊔ ⁅vPlus L T, L⁆ := by
  have hV : vPlus L T = conjClosure (quasithinOmegaOneCenter T) L := by
    show conjClosure (quasithinOmegaOneCenter T) (mPlus L T) = _
    rw [c.mPlus_eq]
  have key : conjClosure (quasithinOmegaOneCenter T) L ≤
      quasithinOmegaOneCenter T ⊔ ⁅vPlus L T, L⁆ := by
    refine conjClosure_le fun y hy z hz => ?_
    have hzV : z ∈ vPlus L T := by
      rw [hV]
      exact le_conjClosure _ _ hz
    have hcomm : ⁅y, z⁆ ∈ ⁅vPlus L T, L⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy hzV
    have e : y * z * y⁻¹ = ⁅y, z⁆ * z := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hz)
  exact (le_of_eq hV).trans key

end A2Cfg

theorem leaf_P9b_of (h36 : A36ForSQTK) (h5 : Stmt3_3_5)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q →
        ∀ w : G, w ∈ M → w ∈ Subgroup.centralizer (a2Z T : Set G) → orderOf w = 9 →
          w ^ 3 ∈ Subgroup.centralizer (a2V L T : Set G) := by
  intro G _ _ T M L D H K q c w hwM hwZ hw9
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hM := (h5 G T M L c.nf.hyp.toSetup331).1
  rw [c.mPlus_eq] at hM
  rw [hM] at hwM
  have hwZN : w ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _ hwZ
  have hVeq : vPlus L T = conjClosure (quasithinOmegaOneCenter T) L := by
    show conjClosure (quasithinOmegaOneCenter T) (mPlus L T) = _
    rw [c.mPlus_eq]
  have hwV : w ∈ Subgroup.normalizer (vPlus L T : Set G) := by
    rw [hVeq]
    exact mem_normalizer_conjClosure_of hwM hwZN
  have hwW : w ∈ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator_of hwV hwM
  obtain ⟨⟨x₀, hx₀⟩, hx₀ne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (c.inf_commutator_ne h36 h5 h128 h37 h38 h39)
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀ne (Subtype.ext h)
  have hx₀Z : x₀ ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.1 hx₀).1
  have hx₀W : x₀ ∈ ⁅vPlus L T, L⁆ := (Subgroup.mem_inf.1 hx₀).2
  have hcomm : Commute w x₀ := (Subgroup.mem_centralizer_iff.1 hwZ x₀ hx₀Z).symm
  have hfix : w ^ 3 * x₀ * (w ^ 3)⁻¹ = x₀ :=
    mul_inv_eq_iff_eq_mul.2 (hcomm.pow_left 3).eq
  have hWV : ⁅vPlus L T, L⁆ ≤ vPlus L T := commutator_le_left_of_le_normalizer' hLV
  have hW2 : ∀ x ∈ ⁅vPlus L T, L⁆, x ^ 2 = 1 := fun x hx => hVe.2 x (hWV hx)
  have hWc : ∀ x ∈ ⁅vPlus L T, L⁆, ∀ y ∈ ⁅vPlus L T, L⁆, x * y = y * x := by
    intro x hx y hy
    have hxV := hWV hx
    have hyV := hWV hy
    exact congrArg Subtype.val (isMulCommutative_iff.1 hVe.1 ⟨x, hxV⟩ ⟨y, hyV⟩)
  have hWcard : Nat.card ↥⁅vPlus L T, L⁆ ≤ 64 := by
    have h := c.card_commutator_le h36 h5 h128 h37 h38 h39
    norm_num at h
    exact h
  have hcube := cube_central_of_elemAbelian_card_le_64 w ⁅vPlus L T, L⁆ hw9 hW2 hWc hWcard hwW
    x₀ hx₀W hx₀1 hfix
  have hw3Z : w ^ 3 ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.pow_mem _ hwZ 3
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer ({w ^ 3} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hw3Z z hz).symm
  have hWC : ⁅vPlus L T, L⁆ ≤ Subgroup.centralizer ({w ^ 3} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact mul_inv_eq_iff_eq_mul.1 (hcube y hy)
  have hVle : vPlus L T ≤ Subgroup.centralizer ({w ^ 3} : Set G) :=
    (c.vPlus_le_omegaOne_sup).trans (sup_le hZC hWC)
  refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
  exact (Subgroup.mem_centralizer_iff.1 (hVle hv) (w ^ 3) (Set.mem_singleton _)).symm

end CFSG.Quasithin.H13.NFa2
