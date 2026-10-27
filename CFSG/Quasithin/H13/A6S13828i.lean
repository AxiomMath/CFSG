module

public import CFSG.Quasithin.H13.A6S13828h

public section

namespace CFSG.Quasithin.H13.A6

open Matrix Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem comm_of_mem_conjSub {G : Type*} [Group G] {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (x : G) {a b : G} (ha : a ∈ conjSub x A)
    (hb : b ∈ conjSub x A) : a * b = b * a := by
  rw [mem_conjSub] at ha hb
  have h := hA _ ha _ hb
  calc a * b = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [h]
    _ = b * a := by group

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
  {γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)} {g c : G}

local notation "UL" => conjClosure (conjClosure S.V3 S.G1) L

theorem conjSub_pow_U0 (D : S.LineData ρ β) (hg : S.GData g) (k : ℕ) :
    conjSub (g ^ k) (S.U0 g) = S.U0 g := by
  induction k with
  | zero => rw [pow_zero, conjSub_one]
  | succ k ih => rw [pow_succ', conjSub_mul, ih, S.conjSub_U0 D (S.frame.L_le hg.L) hg.N hg.H]

theorem VH_comm [IsMulCommutative ↥(conjClosure V S.G1)] :
    ∀ a ∈ conjClosure V S.G1, ∀ b ∈ conjClosure V S.G1, a * b = b * a :=
  fun a ha b hb => congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := ↥(conjClosure V S.G1))).comm ⟨a, ha⟩ ⟨b, hb⟩)

variable [IsMulCommutative ↥(conjClosure V S.G1)]

theorem UL_le (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    UL ≤ S.Xs β γ ⊔ conjSub g (S.Xs β γ) ⊔ conjSub (g ^ 2) (S.Xs β γ) := by
  refine conjClosure_le fun l hl u hu => ?_
  obtain ⟨i, hi⟩ := S.exists_conjSub_UH_le D hg hc hγ hΘ hl
  have hmem := hi (mul_mem_conjSub hu)
  fin_cases i
  · simp only [pow_zero, conjSub_one] at hmem
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem)
  · simp only [pow_one] at hmem
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
  · exact Subgroup.mem_sup_right hmem

theorem comm_UH_conj (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v)
    {l : G} (hl : l ∈ L) {u w : G} (hu : u ∈ conjClosure S.V3 S.G1)
    (hw : w ∈ conjSub l (conjClosure S.V3 S.G1)) : u * w = w * u := by
  obtain ⟨i, hi⟩ := S.exists_conjSub_UH_le D hg hc hγ hΘ hl
  have hw' : w ∈ conjSub (g ^ (i : ℕ)) (conjClosure V S.G1) :=
    conjSub_mono _ S.Xs_le_VH (hi hw)
  have hu' : u ∈ conjSub (g ^ (i : ℕ)) (conjClosure V S.G1) := by
    have h1 : u ∈ S.U0 g := Subgroup.mem_sup_left hu
    rw [← S.conjSub_pow_U0 D hg (i : ℕ)] at h1
    exact conjSub_mono _ (S.U0_le_VH D (S.frame.L_le hg.L) hg.N) h1
  exact comm_of_mem_conjSub S.VH_comm _ hu' hw'

theorem UL_comm (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    UL ≤ Subgroup.centralizer (UL : Set G) := by
  set k : Set G := {x | ∃ h ∈ L, ∃ z ∈ conjClosure S.V3 S.G1, h * z * h⁻¹ = x} with hk
  have hUL : UL = Subgroup.closure k := rfl
  have hgen : k ⊆ Subgroup.centralizer k := by
    rintro _ ⟨l, hl, u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l', hl', u', hu', rfl⟩
    have hw : (l⁻¹ * l') * u' * (l⁻¹ * l')⁻¹ ∈ conjSub (l⁻¹ * l') (conjClosure S.V3 S.G1) :=
      mul_mem_conjSub hu'
    have h1 := S.comm_UH_conj D hg hc hγ hΘ (L.mul_mem (L.inv_mem hl) hl') hu hw
    calc l' * u' * l'⁻¹ * (l * u * l⁻¹) = l * ((l⁻¹ * l') * u' * (l⁻¹ * l')⁻¹ * u) * l⁻¹ := by
          group
      _ = l * (u * ((l⁻¹ * l') * u' * (l⁻¹ * l')⁻¹)) * l⁻¹ := by rw [h1]
      _ = l * u * l⁻¹ * (l' * u' * l'⁻¹) := by group
  have h2 : UL ≤ Subgroup.centralizer k := by
    rw [hUL, Subgroup.closure_le]
    exact hgen
  have h3 : k ⊆ Subgroup.centralizer (UL : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (h2 hy)) x hx).symm
  rw [hUL, Subgroup.closure_le]
  exact h3

theorem le_normalizer_of_le_UL (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v)
    {A B : Subgroup G} (hA : A ≤ UL) (hB : B ≤ UL) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have hc' : ∀ b ∈ UL, a * b * a⁻¹ = b := fun b hb => by
    have := (Subgroup.mem_centralizer_iff.mp (S.UL_comm D hg hc hγ hΘ (hA ha))) b hb
    rw [← this, mul_inv_cancel_right]
  constructor
  · intro hb
    rw [hc' b (hB hb)]
    exact hb
  · intro hb
    have hb' : a * b * a⁻¹ ∈ UL := hB hb
    have e : b = a⁻¹ * (a * b * a⁻¹) * a := by group
    have hbUL : b ∈ UL := by
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hA ha)) hb') (hA ha)
    rw [← hc' b hbUL]
    exact hb

theorem Xs_le_UL (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) : S.Xs β γ ≤ UL := by
  have hconj : ∀ x ∈ L, conjSub x UL ≤ UL := fun x hx y hy => by
    rw [mem_conjSub] at hy
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hx) _).mp hy
    simpa [mul_assoc] using this
  have hU0 : S.U0 g ≤ UL := sup_le (le_conjClosure _ _)
    ((conjSub_mono _ (le_conjClosure _ L)).trans (hconj g hg.L))
  refine (S.Xs_le_sup (c := ⟨c, hc.G1⟩) D hg.L hg.N hg.H hγ hΘ hc.u1_eq).trans ?_
  exact sup_le hU0 ((conjSub_mono _ hU0).trans (hconj c hc.L))

theorem conjSub_Xs_le_UL (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) {x : G} (hx : x ∈ L) :
    conjSub x (S.Xs β γ) ≤ UL := by
  intro y hy
  have h1 := S.Xs_le_UL D hg hc hγ hΘ (mem_conjSub.1 hy)
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hx) _).mp h1
  simpa [mul_assoc] using this

theorem card_UL_le (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    Nat.card ↥UL ≤ 16384 := by
  set X := S.Xs β γ with hX
  have hX1 := S.Xs_le_UL D hg hc hγ hΘ
  have hX2 := S.conjSub_Xs_le_UL D hg hc hγ hΘ hg.L
  have hX3 := S.conjSub_Xs_le_UL D hg hc hγ hΘ (L.pow_mem hg.L 2)
  have hcX : Nat.card ↥X = 1024 := S.card_Xs D hγ
  have hcX2 : Nat.card ↥(conjSub g X) = 1024 := by rw [card_conjSub, hcX]
  have hcX3 : Nat.card ↥(conjSub (g ^ 2) X) = 1024 := by rw [card_conjSub, hcX]
  have hU0 : Nat.card ↥(S.U0 g) = 256 := S.card_U0 D hg.L hg.N hg.H hγ hΘ
  have hU0X : S.U0 g ≤ X := S.U0_le_Xs D hg.L hg.N hg.H hγ hΘ
  have hU0X' : ∀ k : ℕ, S.U0 g ≤ conjSub (g ^ k) X := fun k => by
    rw [← S.conjSub_pow_U0 D hg k]
    exact conjSub_mono _ hU0X
  have h12 := card_sup_mul_card_inf'
    (S.le_normalizer_of_le_UL D hg hc hγ hΘ hX2 hX1)
  have hi12 : 256 ≤ Nat.card ↥(conjSub g X ⊓ X) := by
    rw [← hU0]
    exact Subgroup.card_le_of_le (le_inf (by simpa using hU0X' 1) hU0X)
  rw [hcX2, hcX] at h12
  have hs12 : Nat.card ↥(conjSub g X ⊔ X) ≤ 4096 := by nlinarith
  have hY : conjSub g X ⊔ X ≤ UL := sup_le hX2 hX1
  have h3 := card_sup_mul_card_inf' (S.le_normalizer_of_le_UL D hg hc hγ hΘ hX3 hY)
  have hi3 : 256 ≤ Nat.card ↥(conjSub (g ^ 2) X ⊓ (conjSub g X ⊔ X)) := by
    rw [← hU0]
    exact Subgroup.card_le_of_le (le_inf (hU0X' 2) (hU0X.trans le_sup_right))
  rw [hcX3] at h3
  have hs3 : Nat.card ↥(conjSub (g ^ 2) X ⊔ (conjSub g X ⊔ X)) ≤ 16384 := by nlinarith
  have hle : UL ≤ conjSub (g ^ 2) X ⊔ (conjSub g X ⊔ X) := by
    refine (S.UL_le D hg hc hγ hΘ).trans ?_
    refine sup_le (sup_le ?_ ?_) le_sup_left
    · exact le_sup_right.trans le_sup_right
    · exact le_sup_left.trans le_sup_right
  exact (Subgroup.card_le_of_le hle).trans hs3

omit [IsMulCommutative ↥(conjClosure V S.G1)] in
theorem not_normalizes_VH (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hG1 : S.G1 ∈ S.Hz)
    {g : G} (hgL : g ∈ L) (hgH : g ∉ S.G1)
    (hgU : g ∈ Subgroup.normalizer (conjClosure V S.G1 : Set G)) : False := by
  set N := Subgroup.normalizer (conjClosure V S.G1 : Set G) with hN
  have hG1N : S.G1 ≤ N := le_normalizer_conjClosure V S.G1
  have hM : (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤ (L ⊔ T) ⊓ N := fun x hx =>
    ⟨hx.1, hG1N (by rw [S.normalizer_V1] at hx; exact hx.2)⟩
  rcases S.NLTV1_max ((L ⊔ T) ⊓ N) hM inf_le_left with h | h
  · have : g ∈ (L ⊔ T) ⊓ N := ⟨Subgroup.mem_sup_left hgL, hgU⟩
    rw [h, S.normalizer_V1] at this
    exact hgH this.2
  · have hLT : L ⊔ T ≤ N := h ▸ inf_le_right
    have hU2 : IsPGroup 2 ↥(conjClosure V S.G1) := isPGroup_of_isElemAbelian hF.F911_2
    have hU1 : conjClosure V S.G1 ≠ ⊥ := by
      intro h0
      have := le_conjClosure V S.G1 S.z_mem_V
      rw [h0, Subgroup.mem_bot] at this
      exact S.z_ne_one this
    have hloc : IsTwoLocal N := ⟨_, hU1, hU2, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hMeq := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
    exact hG1.2.2 (hMeq ▸ hG1N.trans hle)

theorem Xs_ne_UL (D : S.LineData ρ β) (hg : S.GData g) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) : S.Xs β γ ≠ UL := by
  intro hXU
  set X := S.Xs β γ with hX
  set I := conjClosure V S.G1 ⊓ conjSub g (conjClosure V S.G1) with hI
  have hXg : conjSub g X ≤ X := by
    intro y hy
    rw [hXU] at hy ⊢
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hg.L) _).mp
      (mem_conjSub.1 hy)
    simpa [mul_assoc] using this
  have hXg' : X ≤ conjSub g X := by
    intro y hy
    rw [hXU] at hy ⊢
    rw [mem_conjSub]
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L (L.inv_mem hg.L)) _).mp
      hy
    simpa using this
  have hXI : X ≤ I := le_inf S.Xs_le_VH (hXg'.trans (conjSub_mono g S.Xs_le_VH))
  have hC2I : ∀ k ∈ Subgroup.centralizer (S.V2 : Set G), ∀ x ∈ I, k * x * k⁻¹ ∈ I := by
    intro k hk x hx
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V S.G1
      (S.C2_le_G1 hk)) x).mp hx.1, ?_⟩
    rw [mem_conjSub]
    have h1 : g⁻¹ * k * g ∈ Subgroup.centralizer (S.V2 : Set G) := S.conj_mem_C2 hg.N hk
    have h2 : g⁻¹ * x * g ∈ (conjClosure V S.G1) := mem_conjSub.1 hx.2
    have e : g⁻¹ * (k * x * k⁻¹) * g = (g⁻¹ * k * g) * (g⁻¹ * x * g) * (g⁻¹ * k * g)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V S.G1
      (S.C2_le_G1 h1)) _).mp h2
  set Img : Subgroup (Multiplicative (Fin 6 → ZMod 2)) :=
    (I.subgroupOf (conjClosure V S.G1)).map γ with hImg
  have hmem : ∀ a y : Fin 4 → ZMod 2, Multiplicative.ofAdd (pl a y) ∈ Img := by
    intro a y
    by_cases ha : pl (S.w1 β) a = 0
    · obtain ⟨x, hx⟩ := hγ.surj (Multiplicative.ofAdd (pl a y))
      refine ⟨x, Subgroup.mem_subgroupOf.2 (hXI (S.mem_Xs.2 ⟨x.2, ?_⟩)), hx⟩
      change Multiplicative.toAdd (γ x) ∈ _
      rw [hx, toAdd_ofAdd]
      rcases S.bv_eq_zero_or_w1 D.hβk ha with h | h
      · rw [h, pl_zero_left]
        exact (plS _ _).zero_mem
      · rw [h]
        exact pl_mem_plS_left _ _ _
    · obtain ⟨g', hg'1, hg'2⟩ := S.exists_GL_fix_w1 (S.pl_w1_w2_ne_zero D.hβk) ha
      obtain ⟨k, hk, hkC⟩ := S.exists_lift_C2 D.hF D.hρs D.hker D.hβk D.hβe D.hQu1 g' hg'1
      obtain ⟨x, hx⟩ := hγ.surj (Multiplicative.ofAdd
        (pl (S.w2 β) (((g'⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y)))
      have hxX : (x : G) ∈ X := S.mem_Xs.2 ⟨x.2, by
        change Multiplicative.toAdd (γ x) ∈ _
        rw [hx, toAdd_ofAdd]
        exact pl_mem_plS_right _ _ _⟩
      set x' : ↥(conjClosure V S.G1) := ⟨(k : G) * x * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure V S.G1 k.2) x).mp x.2⟩ with hx'
      refine ⟨x', Subgroup.mem_subgroupOf.2 (hC2I k hkC x (hXI hxX)), ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hγ.equiv k x x' rfl, hx, toAdd_ofAdd, toAdd_ofAdd, wedge2_mulVec_pl, hk, hg'2,
        GL_mulVec_inv]
  have htop : ∀ ω : Fin 6 → ZMod 2, Multiplicative.ofAdd ω ∈ Img := by
    intro ω
    rw [vec6_decomp ω, ofAdd_sum]
    refine Subgroup.prod_mem _ fun p _ => ?_
    rcases zmodTwo_cases (ω p) with h | h
    · rw [h, zero_smul, ofAdd_zero]
      exact Img.one_mem
    · rw [h, one_smul, ← pl_single p]
      exact hmem _ _
  have hVg : (conjClosure V S.G1) ≤ conjSub g (conjClosure V S.G1) := by
    intro v hv
    obtain ⟨x, hxI, hxv⟩ := htop (Multiplicative.toAdd (γ ⟨v, hv⟩))
    have hq : (⟨v, hv⟩ * x⁻¹ : ↥(conjClosure V S.G1)) ∈ γ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxv, ofAdd_toAdd]
      exact mul_inv_cancel _
    have hqU : ((⟨v, hv⟩ * x⁻¹ : ↥(conjClosure V S.G1)) : G) ∈ conjClosure S.V3 S.G1 :=
      (hγ.ker _).1 hq
    have hqI : ((⟨v, hv⟩ * x⁻¹ : ↥(conjClosure V S.G1)) : G) ∈ I :=
      hXI (S.U0_le_Xs D hg.L hg.N hg.H hγ hΘ (Subgroup.mem_sup_left hqU))
    have hxI' : (x : G) ∈ I := Subgroup.mem_subgroupOf.1 hxI
    have e : v = ((⟨v, hv⟩ * x⁻¹ : ↥(conjClosure V S.G1)) : G) * x := by simp
    rw [e]
    exact (I.mul_mem hqI hxI').2
  have heq : conjSub g (conjClosure V S.G1) = (conjClosure V S.G1) := by
    refine (Subgroup.eq_of_le_of_card_ge hVg ?_).symm
    rw [card_conjSub]
  refine S.not_normalizes_VH D.hF D.hG1 hg.L hg.H (Subgroup.mem_normalizer_iff.2 fun y => ?_)
  constructor
  · intro hy
    rw [← heq, mem_conjSub]
    simpa [mul_assoc] using hy
  · intro hy
    rw [← heq, mem_conjSub] at hy
    simpa [mul_assoc] using hy

theorem card_UL_ge (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    2048 ≤ Nat.card ↥UL := by
  have hle := S.Xs_le_UL D hg hc hγ hΘ
  have hne := S.Xs_ne_UL D hg hγ hΘ
  have hcX := S.card_Xs D hγ
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  rw [hcX] at hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hm, hcX]))
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have : 2 ≤ m := by omega
  rw [hm]
  omega

end Setting4

end CFSG.Quasithin.H13.A6

