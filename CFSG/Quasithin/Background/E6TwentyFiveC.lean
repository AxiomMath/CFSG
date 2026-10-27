module

public import CFSG.Quasithin.Background.E6TwentyFiveA
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bTransvection

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E625SLeTwoLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L X : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    E625Setting T M V U hV → E611Data hV M U L X →
    IsComponentIn L (Subgroup.centralizer (U : Set G)) →
    (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2
        (E3.mQuot V U) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 (E3.mQuot V U)) →
    ∀ (s : ℕ) (Y : Fin s → Subgroup (MulAut (IntMod V hV)))
      (Vs : Fin s → Subgroup (IntMod V hV)), E624Body hV M X s Y Vs → s ≤ 2

section Tools

variable {W : Type*} [CommGroup W]

theorem apply_eq_of_mem_factor {s : ℕ} {Y : Fin s → Subgroup (MulAut W)}
    {Vs : Fin s → Subgroup W}
    (hYcomm : ∀ i j, i ≠ j → ∀ a ∈ Y i, ∀ b ∈ Y j, a * b = b * a) (hVind : iSupIndep Vs)
    (hVi : ∀ k, commSub ⊤ (Y k) = Vs k) {i j : Fin s} (hij : i ≠ j) {y : MulAut W}
    (hy : y ∈ Y i) {v : W} (hv : v ∈ Vs j) : y v = v := by
  have hstab : y v ∈ Vs j := by
    have hYj : (Y j).map (MulAut.conj y).toMonoidHom = Y j := by
      ext z
      constructor
      · rintro ⟨z', hz', rfl⟩
        have hc := hYcomm i j hij y hy z' hz'
        show y * z' * y⁻¹ ∈ Y j
        rw [hc, mul_inv_cancel_right]
        exact hz'
      · intro hz
        refine ⟨z, hz, ?_⟩
        have hc := hYcomm i j hij y hy z hz
        show y * z * y⁻¹ = z
        rw [hc, mul_inv_cancel_right]
    have h1 := Asc81c.commSub_map_conj (Y j) y
    rw [hYj, hVi j] at h1
    have h2 : y v ∈ (Vs j).map y.toMonoidHom := ⟨v, hv, rfl⟩
    rw [← h1] at h2
    exact h2
  have h1 : y v * v⁻¹ ∈ Vs i := by
    rw [← hVi i]
    exact Subgroup.subset_closure ⟨y, hy, v, Subgroup.mem_top v, rfl⟩
  have h2 : y v * v⁻¹ ∈ Vs j := (Vs j).mul_mem hstab ((Vs j).inv_mem hv)
  have hdisj : Vs i ⊓ Vs j = ⊥ := disjoint_iff.1 (hVind.pairwiseDisjoint hij)
  have h3 : y v * v⁻¹ ∈ Vs i ⊓ Vs j := ⟨h1, h2⟩
  rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact h3

theorem eq_one_of_fix_factor {s : ℕ} {Y : Fin s → Subgroup (MulAut W)} {Vs : Fin s → Subgroup W}
    (hYcomm : ∀ i j, i ≠ j → ∀ a ∈ Y i, ∀ b ∈ Y j, a * b = b * a) (hVind : iSupIndep Vs)
    (hVi : ∀ k, commSub ⊤ (Y k) = Vs k) (hVtop : (⨆ k, Vs k) = ⊤) {k : Fin s} {y : MulAut W}
    (hy : y ∈ Y k) (hfix : ∀ v ∈ Vs k, y v = v) : y = 1 := by
  have hle : (⨆ j, Vs j) ≤ fixV (Subgroup.zpowers y) := by
    refine iSup_le fun j => fun v hv => ?_
    have hyv : y v = v := by
      by_cases hjk : j = k
      · subst hjk
        exact hfix v hv
      · exact apply_eq_of_mem_factor hYcomm hVind hVi (Ne.symm hjk) hy hv
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hm : ∀ m : ℕ, (y ^ m) v = v := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, MulAut.mul_apply, hyv, ih]
    rcases Int.eq_nat_or_neg m with ⟨j', rfl | rfl⟩
    · rw [zpow_natCast]
      exact hm j'
    · rw [zpow_neg, zpow_natCast]
      have h2 := congrArg (fun w => (y ^ j')⁻¹ w) (hm j')
      simp only [MulAut.inv_apply_self] at h2
      exact h2.symm
  rw [hVtop] at hle
  ext v
  exact hle (Subgroup.mem_top v) y (Subgroup.mem_zpowers y)

end Tools

section Group

variable {G : Type} [Group G] [Finite G]

theorem exists_pSubgroup_le_normalized {p : ℕ} [hp : Fact p.Prime] {R B : Subgroup G}
    (hR : IsPGroup p R) (hRB : R ≤ Subgroup.normalizer (B : Set G)) (hpB : p ∣ Nat.card B) :
    ∃ P : Subgroup G, P ≤ B ∧ IsPGroup p P ∧ P ≠ ⊥ ∧ R ≤ Subgroup.normalizer (P : Set G) := by
  classical
  set K := R ⊔ B with hKdef
  have hRK : R ≤ K := le_sup_left
  have hBK : B ≤ K := le_sup_right
  have hKN : K ≤ Subgroup.normalizer (B : Set G) := sup_le hRB Subgroup.le_normalizer
  have hBn : (B.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).2 hKN
  have hR' : IsPGroup p (R.subgroupOf K) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  obtain ⟨P', hP'⟩ := exists_sylow_map_eq_inf_of_subnormal S hBn.isSubnormal
  have hpB' : p ∣ Nat.card (B.subgroupOf K) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv]
  have hP'1 := Sylow.ne_bot_of_dvd_card P' hpB'
  refine ⟨((S : Subgroup K) ⊓ B.subgroupOf K).map K.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · exact (S.isPGroup'.to_le inf_le_left).map _
  · intro h0
    apply hP'1
    have h1 :
        ((P' : Subgroup (B.subgroupOf K)).map (B.subgroupOf K).subtype).map K.subtype = ⊥ := by
      rw [hP']
      exact h0
    rw [Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ (B.subgroupOf K).subtype_injective] at h1
    exact h1
  · intro r hr
    have hrK : r ∈ K := hRK hr
    have hrS : (⟨r, hrK⟩ : K) ∈ (S : Subgroup K) := hS hr
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨z, ⟨hzS, hzB⟩, rfl⟩
      refine ⟨⟨r, hrK⟩ * z * ⟨r, hrK⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
      · exact (S : Subgroup K).mul_mem ((S : Subgroup K).mul_mem hrS hzS)
          ((S : Subgroup K).inv_mem hrS)
      · exact hBn.conj_mem z hzB ⟨r, hrK⟩
    · rintro ⟨z, ⟨hzS, hzB⟩, hz⟩
      have hzK : (⟨r, hrK⟩ : K)⁻¹ * z * ⟨r, hrK⟩ ∈ (S : Subgroup K) ⊓ B.subgroupOf K := by
        refine ⟨(S : Subgroup K).mul_mem ((S : Subgroup K).mul_mem
          ((S : Subgroup K).inv_mem hrS) hzS) hrS, ?_⟩
        have := hBn.conj_mem z hzB (⟨r, hrK⟩ : K)⁻¹
        simpa using this
      refine ⟨_, hzK, ?_⟩
      have hz' : (z : G) = r * y * r⁻¹ := hz
      show (r⁻¹ * (z : G) * r) = y
      rw [hz']
      group

theorem three_le_pRank_of_elems {p : ℕ} [hp : Fact p.Prime] {K C₁ C₂ : Subgroup G}
    {x₁ x₂ x₃ : G} (hx₁K : x₁ ∈ K) (hx₂K : x₂ ∈ K) (hx₃K : x₃ ∈ K) (c12 : Commute x₁ x₂)
    (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃) (hp₁ : x₁ ^ p = 1) (hp₂ : x₂ ^ p = 1)
    (hp₃ : x₃ ^ p = 1) (hx₁1 : x₁ ≠ 1) (h₁ : x₁ ∈ C₁) (h₂ : x₂ ∉ C₁) (h₁' : x₁ ∈ C₂)
    (h₂' : x₂ ∈ C₂) (h₃ : x₃ ∉ C₂) : 3 ≤ CFSG.Open.pRank p K := by
  have hp1 : 1 < p := hp.out.one_lt
  let F₀ : PUnit.{1} →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = p ^ 0 := by simp
  have hx₁r : x₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact hx₁1 ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ hp₁ hx₁r (fun _ => Commute.one_left x₁)
  have hr₁ : ∀ a, F₁ a ∈ Subgroup.zpowers x₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    rw [hb]
    exact Subgroup.mul_mem _ (by simp [F₀]) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) n)
  have hZ₁ : Subgroup.zpowers x₁ ≤ C₁ := Subgroup.zpowers_le.2 h₁
  have hZ₂ : Subgroup.zpowers x₁ ≤ C₂ := Subgroup.zpowers_le.2 h₁'
  have hx₂r : x₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    exact h₂ (ha ▸ hZ₁ (hr₁ a))
  have hc12 : ∀ a, Commute (F₁ a) x₂ := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ a)
    rw [← hk]
    exact c12.zpow_left k
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ hp₂ hx₂r hc12
  have hr₂ : ∀ a, F₂ a ∈ C₂ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    exact C₂.mul_mem (hZ₂ (hr₁ b)) (C₂.pow_mem h₂' n)
  have hr₂' : ∀ a, Commute (F₂ a) x₃ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ b)
    rw [← hk]
    exact (c13.zpow_left k).mul_left (c23.pow_left n)
  have hx₃r : x₃ ∉ F₂.range := by
    rintro ⟨a, ha⟩
    exact h₃ (ha ▸ hr₂ a)
  obtain ⟨F₃, hF₃, hcomm₃, hpow₃, hcard₃, hrep₃⟩ :=
    CFSG.SectionRank.exists_extend hcomm₂ hpow₂ hcard₂ F₂ hF₂ hp₃ hx₃r hr₂'
  have hrange : F₃.range ≤ K := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₃ a
    rw [hb]
    refine K.mul_mem ?_ (K.pow_mem hx₃K n)
    obtain ⟨c, m, hc⟩ := hrep₂ b
    rw [hc]
    refine K.mul_mem ?_ (K.pow_mem hx₂K m)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ c)
    rw [← hk]
    exact K.zpow_mem hx₁K k
  have := CFSG.SectionRank.le_pRank_of_injective hp1 hcomm₃ hpow₃ hcard₃ F₃ hF₃ hrange
  omega

end Group

section Main

variable {G : Type} [Group G] [Finite G]

theorem e625SLeTwo_of (hLie : E625SLeTwoLie) : E625SLeTwo := by
  intro G _ _ T M V U L X hV hset hD s Y Vs hB
  classical
  have hD' := hD
  obtain ⟨hLU, -, hLM, hCL, hXLM, hXcyc, hXcard, hUX1, hUX2, hreg, hnorm, hNL, hLMX, htype⟩ := hD'
  rcases htype with ⟨-, hker⟩ | ⟨hLc, hlie⟩
  swap
  · exact hLie G T M V U L X hV hset hD hLc hlie s Y Vs hB
  obtain ⟨h, hm, hU, hr, hU1, hUm⟩ := hset
  have := h.simple
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hXMU : X ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (hXLM.trans inf_le_right) ((hXLM.trans inf_le_left).trans hLU)
  have hXeq : X = L ⊓ M := le_antisymm hXLM hLMX
  have hXN : X ≤ Subgroup.normalizer (V : Set G) :=
    hXMU.trans (inf_centralizer_le_normalizer h hU.1 hU.2.1)
  obtain ⟨-, hfixmap, -⟩ := hyp102_autI hV h hU hU1 hUm hXMU hXcyc hXcard hUX2 hreg hnorm
  obtain ⟨⟨hYsup, hYind, hYcomm⟩, ⟨-, hfix2⟩, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, hdich⟩ := hB
  have hY0 : fixV (e624Y hV M X) = ⊥ := fixV_e624Y_eq_bot hV h hU hfixmap
  have hVtop : (⨆ k, Vs k) = ⊤ := by
    rw [hVsup]
    rw [hY0, bot_sup_eq] at hfix2
    exact hfix2
  have hVi' : ∀ k, commSub ⊤ (Y k) = Vs k := fun k => (hVi k).1
  obtain ⟨i₀, hXY₀⟩ : ∃ i₀, autI hV X ≤ Y i₀ := by
    rcases hdich with ⟨i, hi⟩ | ⟨-, i, hi, -⟩
    · exact ⟨i, hi.le⟩
    · exact ⟨i, hi⟩
  by_contra hs
  push Not at hs
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin s, i₁ ≠ i₀ := by
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin s)) ⊆ {i₀} := fun k _ => by simp [hall k]
    have h2 := Finset.card_le_card h1
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h2
    omega
  obtain ⟨i₂, hi₂₀, hi₂₁⟩ : ∃ i₂ : Fin s, i₂ ≠ i₀ ∧ i₂ ≠ i₁ := by
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin s)) ⊆ {i₀, i₁} := fun k _ => by
      by_cases hk : k = i₀
      · simp [hk]
      · simp [hall k hk]
    have h2 := (Finset.card_le_card h1).trans (Finset.card_insert_le _ _)
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h2
    omega
  have h4 : 4 ≤ 2 ^ E3.mQuot V U :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hU1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ E3.mQuot V U - 1 ≠ 1 by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have he : Even (2 ^ E3.mQuot V U) := (Nat.even_pow' (by omega)).2 even_two
    have hodd : Odd (2 ^ E3.mQuot V U - 1) := Nat.Even.sub_odd (by omega) he odd_one
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpd)
  set B := L ⊓ M with hBdef
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hXeq ▸ hXN
  have hBM : B ≤ M := inf_le_right
  have hBY : ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (V : Set G), convI hV ⟨b, hb⟩ ∈ Y i₀ :=
    fun b hb hbN => hXY₀ ((mem_autI hV).2 ⟨⟨b, hbN⟩, hXeq ▸ hb, rfl⟩)
  have hpBcard : p ∣ Nat.card B := by
    have h1 := card_autI_mul_card_inf hV hBN
    have h2 : Nat.card (autI hV B) = 2 ^ E3.mQuot V U - 1 := by rw [← hXeq]; exact hXcard
    rw [← h1, h2]
    exact Dvd.dvd.mul_right hpd _
  have hnormU : ∀ y ∈ Subgroup.normalizer (V : Set G),
      (∀ hy : y ∈ Subgroup.normalizer (V : Set G), ∀ ξ ∈ autI hV X,
        convI hV ⟨y, hy⟩ * ξ = ξ * convI hV ⟨y, hy⟩) → y ∈ Subgroup.normalizer (U : Set G) := by
    intro y hyN hc
    have hle : U.map (MulAut.conj y).toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← hfixmap] at hu ⊢
      obtain ⟨w, hw, rfl⟩ := hu
      refine ⟨convI hV ⟨y, hyN⟩ w, fun ξ hξ => ?_, ?_⟩
      · rw [← MulAut.mul_apply, ← hc hyN ξ hξ, MulAut.mul_apply, hw ξ hξ]
      · rw [E3.valHom_apply, convI_apply_val]
        rfl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
  have step : ∀ (k : Fin s) (g : Subgroup.normalizer (V : Set G)), (g : G) ∈ M →
      (Y i₀).map (MulAut.conj (convI hV g)).toMonoidHom = Y k →
      ∀ (R : Subgroup G), IsPGroup p R → R ≤ M → R ≤ Subgroup.normalizer (V : Set G) →
      (∀ r ∈ R, ∀ hr : r ∈ Subgroup.normalizer (V : Set G), ∀ η ∈ Y k,
        convI hV ⟨r, hr⟩ * η = η * convI hV ⟨r, hr⟩) →
      ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ B.map (MulAut.conj (g : G)).toMonoidHom ∧ P ≤ M ∧
        P ≤ Subgroup.normalizer (V : Set G) ∧
        (∀ x ∈ P, ∀ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ Y k) ∧
        P ⊓ Subgroup.centralizer (V : Set G) = ⊥ ∧ P ≠ ⊥ ∧ ∀ r ∈ R, ∀ x ∈ P, r * x = x * r := by
    intro k g hgM hφ R hR hRM hRN hRc
    have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := g.2
    set Bk := B.map (MulAut.conj (g : G)).toMonoidHom with hBkdef
    have hBkM : Bk ≤ M := by
      rintro _ ⟨b, hb, rfl⟩
      exact M.mul_mem (M.mul_mem hgM (hBM hb)) (M.inv_mem hgM)
    have hBkN : Bk ≤ Subgroup.normalizer (V : Set G) := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN (hBN hb)) (Subgroup.inv_mem _ hgN)
    have hBkY : ∀ x ∈ Bk, ∀ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ Y k := by
      rintro _ ⟨b, hb, rfl⟩ hx
      rw [← hφ]
      refine ⟨convI hV ⟨b, hBN hb⟩, hBY b hb (hBN hb), ?_⟩
      have he : (⟨(MulAut.conj (g : G)).toMonoidHom b, hx⟩ : Subgroup.normalizer (V : Set G)) =
          g * ⟨b, hBN hb⟩ * g⁻¹ := rfl
      rw [he, map_mul, map_mul, map_inv]
      rfl
    have hkerk : ¬ p ∣ Nat.card ↥(Bk ⊓ Subgroup.centralizer (V : Set G)) := by
      have hgC : (g : G) ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
        B2F.le_normalizer_centralizer le_rfl hgN
      have heq : Bk ⊓ Subgroup.centralizer (V : Set G) =
          (B ⊓ Subgroup.centralizer (V : Set G)).map (MulAut.conj (g : G)).toMonoidHom := by
        ext x
        constructor
        · rintro ⟨⟨b, hb, rfl⟩, hxC⟩
          exact ⟨b, ⟨hb, (Subgroup.mem_normalizer_iff.1 hgC b).2 hxC⟩, rfl⟩
        · rintro ⟨b, ⟨hb, hbC⟩, rfl⟩
          exact ⟨⟨b, hb, rfl⟩, (Subgroup.mem_normalizer_iff.1 hgC b).1 hbC⟩
      rw [heq, Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]
      exact hker p hp hpd
    have hpBk : p ∣ Nat.card Bk := by
      rw [hBkdef, Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]
      exact hpBcard
    have hRBk : R ≤ Subgroup.normalizer (Bk : Set G) := by
      intro r hr
      set y := (g : G)⁻¹ * r * g with hydef
      have hyM : y ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) (hRM hr)) hgM
      have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) (hRN hr)) hgN
      have hyU : y ∈ Subgroup.normalizer (U : Set G) := by
        refine hnormU y hyN fun hy ξ hξ => ?_
        have he : (⟨y, hy⟩ : Subgroup.normalizer (V : Set G)) = g⁻¹ * ⟨r, hRN hr⟩ * g := rfl
        have hη : convI hV g * ξ * (convI hV g)⁻¹ ∈ Y k := by
          rw [← hφ]
          exact ⟨ξ, hXY₀ hξ, rfl⟩
        have hc := hRc r hr (hRN hr) _ hη
        rw [he, map_mul, map_mul, map_inv]
        calc (convI hV g)⁻¹ * convI hV ⟨r, hRN hr⟩ * convI hV g * ξ
            = (convI hV g)⁻¹ * (convI hV ⟨r, hRN hr⟩ * (convI hV g * ξ * (convI hV g)⁻¹)) *
                convI hV g := by group
          _ = (convI hV g)⁻¹ * ((convI hV g * ξ * (convI hV g)⁻¹) * convI hV ⟨r, hRN hr⟩) *
                convI hV g := by rw [hc]
          _ = ξ * ((convI hV g)⁻¹ * convI hV ⟨r, hRN hr⟩ * convI hV g) := by group
      have hyL := hNL y ⟨hyM, hyN⟩ hyU
      have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro b
        constructor
        · intro hb
          exact ⟨(Subgroup.mem_normalizer_iff.1 hyL b).1 hb.1,
            M.mul_mem (M.mul_mem hyM hb.2) (M.inv_mem hyM)⟩
        · intro hb
          have h1 := (Subgroup.mem_normalizer_iff.1 hyL b).2 hb.1
          refine ⟨h1, ?_⟩
          have h2 : b = y⁻¹ * (y * b * y⁻¹) * y := by group
          rw [h2]
          exact M.mul_mem (M.mul_mem (M.inv_mem hyM) hb.2) hyM
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨y * b * y⁻¹, (Subgroup.mem_normalizer_iff.1 hyB b).1 hb, ?_⟩
        show (g : G) * (y * b * y⁻¹) * (g : G)⁻¹ = r * ((g : G) * b * (g : G)⁻¹) * r⁻¹
        rw [hydef]
        group
      · rintro ⟨b, hb, hbz⟩
        refine ⟨y⁻¹ * b * y, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyB) b).1 hb
          simpa using this
        · have hbz' : (g : G) * b * (g : G)⁻¹ = r * z * r⁻¹ := hbz
          show (g : G) * (y⁻¹ * b * y) * (g : G)⁻¹ = z
          have h1 : (g : G) * (y⁻¹ * b * y) * (g : G)⁻¹ =
              r⁻¹ * ((g : G) * b * (g : G)⁻¹) * r := by rw [hydef]; group
          rw [h1, hbz']
          group
    obtain ⟨P, hPB, hPp, hP1, hRP⟩ := exists_pSubgroup_le_normalized hR hRBk hpBk
    have hPC : P ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxp : IsPGroup p ↥(P ⊓ Subgroup.centralizer (V : Set G)) := hPp.to_le inf_le_left
      have hle : P ⊓ Subgroup.centralizer (V : Set G) ≤ Bk ⊓ Subgroup.centralizer (V : Set G) :=
        inf_le_inf_right _ hPB
      have hcop : Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) = 1 := by
        obtain ⟨a, ha⟩ := hxp.exists_card_eq
        rcases Nat.eq_zero_or_pos a with h0 | hpos
        · rw [ha, h0, pow_zero]
        · exfalso
          apply hkerk
          have h1 := Subgroup.card_dvd_of_le hle
          rw [ha] at h1
          exact (dvd_pow_self p hpos.ne').trans h1
      rw [Subgroup.eq_bot_of_card_eq _ hcop] at hx
      exact hx
    refine ⟨P, hPp, hPB, hPB.trans hBkM, hPB.trans hBkN, fun x hx hxN => hBkY x (hPB hx) hxN, hPC,
      hP1, fun r hr x hx => ?_⟩
    have hrN := hRN hr
    have hxN := hBkN (hPB hx)
    have hcomm : r * x * r⁻¹ * x⁻¹ ∈ P ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨P.mul_mem ((Subgroup.mem_normalizer_iff.1 (hRP hr) x).1 hx) (P.inv_mem hx), ?_⟩
      have hξ := hBkY x (hPB hx) hxN
      have hc := hRc r hr hrN _ hξ
      have h1 : convI hV (⟨r, hrN⟩ * ⟨x, hxN⟩ * ⟨r, hrN⟩⁻¹ * ⟨x, hxN⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      exact (convI_eq_one_iff hV _).1 h1
    rw [hPC, Subgroup.mem_bot] at hcomm
    calc r * x = (r * x * r⁻¹ * x⁻¹) * (x * r) := by group
      _ = x * r := by rw [hcomm, one_mul]
  have hYc : ∀ i j, i ≠ j → ∀ x ∈ Y i, ∀ η ∈ Y j, x * η = η * x := hYcomm
  have hone :
      (Y i₀).map (MulAut.conj (convI hV (1 : Subgroup.normalizer (V : Set G)))).toMonoidHom =
        Y i₀ := by
    rw [map_one, map_one]
    exact Subgroup.map_id _
  obtain ⟨P₀, hP₀p, hP₀B, hP₀M, hP₀N, hP₀Y, hP₀C, hP₀1, -⟩ :=
    step i₀ 1 M.one_mem hone ⊥ IsPGroup.of_bot bot_le bot_le (fun r hr => by
      rw [Subgroup.mem_bot] at hr
      subst hr
      intro hr η _
      have h1 : convI hV ⟨1, hr⟩ = 1 := by
        rw [show (⟨1, hr⟩ : Subgroup.normalizer (V : Set G)) = 1 from rfl, map_one]
      rw [h1, one_mul, mul_one])
  obtain ⟨φ₁, hφ₁M, hφ₁⟩ := htrans i₀ i₁
  obtain ⟨g₁, hg₁M, rfl⟩ := (mem_autI hV).1 hφ₁M
  obtain ⟨P₁, hP₁p, -, hP₁M, hP₁N, hP₁Y, hP₁C, hP₁1, hP₀₁⟩ :=
    step i₁ g₁ hg₁M hφ₁ P₀ hP₀p hP₀M hP₀N fun r hr hrN η hη =>
      hYc i₀ i₁ (Ne.symm hi₁) _ (hP₀Y r hr hrN) η hη
  have hP₀₁N : P₀ ≤ Subgroup.normalizer (P₁ : Set G) := fun r hr =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx =>
      (hP₀₁ r hr x hx).symm)
  have hRp : IsPGroup p ↥(P₀ ⊔ P₁) := IsPGroup.to_sup_of_normal_right' hP₀p hP₁p hP₀₁N
  set Z : Subgroup G := ((Subgroup.centralizer (Y i₂ : Set (MulAut (IntMod V hV)))).comap
    (convI hV)).map (Subgroup.normalizer (V : Set G)).subtype with hZdef
  have hmemZ : ∀ r ∈ Subgroup.normalizer (V : Set G), (∀ hr : r ∈ Subgroup.normalizer (V : Set G),
      ∀ η ∈ Y i₂, convI hV ⟨r, hr⟩ * η = η * convI hV ⟨r, hr⟩) → r ∈ Z := by
    intro r hrN hc
    refine ⟨⟨r, hrN⟩, ?_, rfl⟩
    show convI hV ⟨r, hrN⟩ ∈ Subgroup.centralizer (Y i₂ : Set (MulAut (IntMod V hV)))
    rw [Subgroup.mem_centralizer_iff]
    intro η hη
    exact (hc hrN η hη).symm
  have hZmem : ∀ r ∈ Z, ∀ hr : r ∈ Subgroup.normalizer (V : Set G), ∀ η ∈ Y i₂,
      convI hV ⟨r, hr⟩ * η = η * convI hV ⟨r, hr⟩ := by
    rintro _ ⟨r', hr', rfl⟩ hr η hη
    have he : (⟨(Subgroup.normalizer (V : Set G)).subtype r', hr⟩ :
        Subgroup.normalizer (V : Set G)) = r' := rfl
    rw [he]
    have h1 : convI hV r' ∈ Subgroup.centralizer (Y i₂ : Set (MulAut (IntMod V hV))) := hr'
    exact ((Subgroup.mem_centralizer_iff.1 h1) η hη).symm
  have hP₀Z : P₀ ≤ Z := fun r hr => hmemZ r (hP₀N hr) fun hr' η hη =>
    hYc i₀ i₂ (Ne.symm hi₂₀) _ (hP₀Y r hr hr') η hη
  have hP₁Z : P₁ ≤ Z := fun r hr => hmemZ r (hP₁N hr) fun hr' η hη =>
    hYc i₁ i₂ (Ne.symm hi₂₁) _ (hP₁Y r hr hr') η hη
  obtain ⟨φ₂, hφ₂M, hφ₂⟩ := htrans i₀ i₂
  obtain ⟨g₂, hg₂M, rfl⟩ := (mem_autI hV).1 hφ₂M
  obtain ⟨P₂, hP₂p, -, -, hP₂N, hP₂Y, hP₂C, hP₂1, hP₀₁₂⟩ :=
    step i₂ g₂ hg₂M hφ₂ (P₀ ⊔ P₁) hRp (sup_le hP₀M hP₁M) (sup_le hP₀N hP₁N)
      (fun r hr => hZmem r (sup_le hP₀Z hP₁Z hr))
  have hel : ∀ P : Subgroup G, IsPGroup p P → P ≠ ⊥ → ∃ a ∈ P, a ^ p = 1 ∧ a ≠ 1 := by
    intro P hPp hP1
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hP1 (Subgroup.eq_bot_of_card_eq P (by rw [hk, pow_zero]))
    obtain ⟨⟨a, haP⟩, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) p
      (by rw [hk]; exact dvd_pow_self p hk0)
    refine ⟨a, haP, ?_, ?_⟩
    · have : (⟨a, haP⟩ : P) ^ p = 1 := ha ▸ pow_orderOf_eq_one _
      simpa using congrArg Subtype.val this
    · intro h1
      have : orderOf (⟨a, haP⟩ : P) = 1 := by
        rw [orderOf_eq_one_iff]
        exact Subtype.ext h1
      rw [ha] at this
      exact hp.one_lt.ne' this
  obtain ⟨a₀, ha₀P, ha₀p, ha₀1⟩ := hel P₀ hP₀p hP₀1
  obtain ⟨a₁, ha₁P, ha₁p, ha₁1⟩ := hel P₁ hP₁p hP₁1
  obtain ⟨a₂, ha₂P, ha₂p, ha₂1⟩ := hel P₂ hP₂p hP₂1
  have hnotfix : ∀ (k : Fin s) (P : Subgroup G), P ≤ Subgroup.normalizer (V : Set G) →
      (∀ x ∈ P, ∀ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ Y k) →
      P ⊓ Subgroup.centralizer (V : Set G) = ⊥ → ∀ a ∈ P, a ≠ 1 →
      a ∉ Subgroup.centralizer (((Vs k).map (E3.valHom hV) : Subgroup G) : Set G) := by
    intro k P hPN hPY hPC a haP ha1 haC
    have haN := hPN haP
    have hfix : ∀ v ∈ Vs k, convI hV ⟨a, haN⟩ v = v := by
      intro v hv
      apply IntMod.val_injective
      rw [convI_apply_val]
      have h1 := Subgroup.mem_centralizer_iff.1 haC v.val ⟨v, hv, rfl⟩
      show a * v.val * a⁻¹ = v.val
      rw [← h1, mul_inv_cancel_right]
    have h1 := eq_one_of_fix_factor hYcomm hVind hVi' hVtop (hPY a haP haN) hfix
    have h2 : a ∈ P ⊓ Subgroup.centralizer (V : Set G) := ⟨haP, (convI_eq_one_iff hV _).1 h1⟩
    rw [hPC, Subgroup.mem_bot] at h2
    exact ha1 h2
  have hfixo : ∀ (j k : Fin s), j ≠ k → ∀ (P : Subgroup G),
      P ≤ Subgroup.normalizer (V : Set G) →
      (∀ x ∈ P, ∀ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ Y j) →
      ∀ a ∈ P, a ∈ Subgroup.centralizer (((Vs k).map (E3.valHom hV) : Subgroup G) : Set G) := by
    intro j k hjk P hPN hPY a haP
    have haN := hPN haP
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 := apply_eq_of_mem_factor hYcomm hVind hVi' hjk (hPY a haP haN) hv
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    rw [E3.valHom_apply]
    calc v.val * a = (a * v.val * a⁻¹) * a := by rw [h2]
      _ = a * v.val := by group
  have hUa : ∀ (k : Fin s), k ≠ i₀ → ∀ (P : Subgroup G), P ≤ Subgroup.normalizer (V : Set G) →
      (∀ x ∈ P, ∀ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ Y k) →
      P ≤ Subgroup.normalizer (U : Set G) := by
    intro k hk P hPN hPY x hx
    refine hnormU x (hPN hx) fun hx' ξ hξ => ?_
    exact hYcomm k i₀ hk _ (hPY x hx hx') ξ (hXY₀ hξ)
  have ha₀U : a₀ ∈ Subgroup.normalizer (U : Set G) := by
    obtain ⟨b, hb, hba⟩ := hP₀B ha₀P
    have hba' : a₀ = b := by
      rw [← hba]
      show (1 : G) * b * (1 : G)⁻¹ = b
      group
    rw [hba']
    exact Subgroup.centralizer_le_normalizer _ (hLU hb.1)
  have ha₁U := hUa i₁ hi₁ P₁ hP₁N hP₁Y ha₁P
  have ha₂U := hUa i₂ hi₂₀ P₂ hP₂N hP₂Y ha₂P
  have c01 : Commute a₀ a₁ := hP₀₁ a₀ ha₀P a₁ ha₁P
  have c02 : Commute a₀ a₂ := hP₀₁₂ a₀ (Subgroup.mem_sup_left ha₀P) a₂ ha₂P
  have c12 : Commute a₁ a₂ := hP₀₁₂ a₁ (Subgroup.mem_sup_right ha₁P) a₂ ha₂P
  have h3 := three_le_pRank_of_elems ha₀U ha₁U ha₂U c01 c02 c12 ha₀p ha₁p ha₂p ha₀1
    (hfixo i₀ i₁ (Ne.symm hi₁) P₀ hP₀N hP₀Y a₀ ha₀P) (hnotfix i₁ P₁ hP₁N hP₁Y hP₁C a₁ ha₁P ha₁1)
    (hfixo i₀ i₂ (Ne.symm hi₂₀) P₀ hP₀N hP₀Y a₀ ha₀P)
    (hfixo i₁ i₂ (Ne.symm hi₂₁) P₁ hP₁N hP₁Y a₁ ha₁P)
    (hnotfix i₂ P₂ hP₂N hP₂Y hP₂C a₂ ha₂P ha₂1)
  have h4 : CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) ≤ 2 :=
    (A1b.pRank_le_evenRank hp hp2 ⟨U, hU.2.1, hV2.to_le hU.1, rfl⟩).trans h.qtke.2.2
  omega

end Main

end E6

end CFSG.Quasithin
