module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Two
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem finrank_img_Vt_eq_two {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {t : G} (h2 : SLMNat hc t 2) :
    Module.finrank K (imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun s e he => hc.smul_mem_img_Vt h t s he)) = 2 := by
  let V := Vt M (LB M Q B) B Z t
  let Vsub : Submodule K M₀.E :=
    imgSub M₀ V (fun s e he => hc.smul_mem_img_Vt h t s he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hVcardImg : Nat.card ↥Vsub = Nat.card (M₀.img V) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => (hVsub_mem e).symm)
  have hcard : Nat.card ↥V = Nat.card Z * Nat.card (M₀.img V) :=
    M₀.card_eq (S := V) (hc.Vt_le_Q t) sec39_Z_le_Vt
  have hVcard : Nat.card ↥Vsub = Nat.card Z ^ 2 := by
    rw [hVcardImg]
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
    rw [← hcard, SLMNat.card_Vt h2, pow_succ']
  have hK2 : 2 ≤ Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have h1 : Nat.card K ^ Module.finrank K Vsub = Nat.card K ^ 2 := by
    rw [← Module.natCard_eq_pow_finrank, hVcard, h.card]
  exact Nat.pow_right_injective hK2 h1

private theorem finrank_ker_B_pi_eq_one {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {t : G} (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q)
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) :
    Module.finrank K (LinearMap.ker ((M₀.B (M₀.π c)).comp
      (imgSub M₀ (Vt M (LB M Q B) B Z t)
        (fun s e he => hc.smul_mem_img_Vt h t s he)).subtype)) = 1 := by
  let V := Vt M (LB M Q B) B Z t
  let Vsub : Submodule K M₀.E :=
    imgSub M₀ V (fun s e he => hc.smul_mem_img_Vt h t s he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  let f : M₀.E →ₗ[K] K := M₀.B (M₀.π c)
  let g : Vsub →ₗ[K] K := f.comp Vsub.subtype
  have hcC : c ∉ Subgroup.centralizer (V : Set G) := fun hcV =>
    hcW (Subgroup.mem_inf.mpr ⟨hcQ, hcV⟩)
  have hv : ∃ v ∈ V, v * c ≠ c * v := by
    by_contra hcon
    push Not at hcon
    exact hcC (Subgroup.mem_centralizer_iff.mpr hcon)
  obtain ⟨v, hvV, hvc⟩ := hv
  have hvc' : ⁅c, v⁆ ≠ 1 := fun h1 =>
    hvc (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hvZ : ⁅c, v⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hcQ (hVQ hvV)
  have hγ : γ ⁅c, v⁆ ≠ 0 := fun h0 => hvc' (h.reg.inj _ hvZ h0)
  let v' : Vsub := ⟨M₀.π v, (hVsub_mem _).mpr (M₀.pi_mem_img hvV (hVQ hvV))⟩
  have hgv : g v' ≠ 0 := by
    intro h0
    have h0' : M₀.B (M₀.π c) (M₀.π v) = 0 := by simpa [v', f, g] using h0
    exact hγ (by rw [M₀.comm_eq c hcQ v (hVQ hvV)]; exact h0')
  have hsurj : g.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro s
    refine ⟨(s / g v') • v', ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hgv]
  have hgrange : Module.finrank K g.range = 1 := by
    rw [hsurj]
    simpa using Module.finrank_self K
  have hVdim : Module.finrank K Vsub = 2 := by
    simpa [Vsub, V] using finrank_img_Vt_eq_two hc h h2
  have hru := LinearMap.finrank_range_add_finrank_ker g
  rw [hgrange, hVdim] at hru
  have hker : Module.finrank K g.ker = 1 := by omega
  simpa [f, g, Vsub, V] using hker

private theorem pi_mem_img_B_of_mem_Vt_inf_centralizer {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {t : G} (h2 : SLMNat hc t 2) {c x : G}
    (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    (hBV : B ≤ Vt M (LB M Q B) B Z t) (hxV : x ∈ Vt M (LB M Q B) B Z t)
    (hxC : x ∈ Subgroup.centralizer ({c} : Set G)) : M₀.π x ∈ M₀.img B := by
  let V := Vt M (LB M Q B) B Z t
  let Vsub : Submodule K M₀.E := imgSub M₀ V (fun s e he => hc.smul_mem_img_Vt h t s he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hxVsub : M₀.π x ∈ Vsub := (hVsub_mem _).mpr (M₀.pi_mem_img hxV (hVQ hxV))
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hcomm : ⁅c, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hxc.symm
  let g : Vsub →ₗ[K] K := (M₀.B (M₀.π c)).comp Vsub.subtype
  have hfx : g ⟨M₀.π x, hxVsub⟩ = 0 := by
    have h1 : M₀.B (M₀.π c) (M₀.π x) = 0 := by
      rw [← M₀.comm_eq c hcQ x (hVQ hxV), hcomm, h.reg.one]
    simpa [g] using h1
  have hkerdim : Module.finrank K g.ker = 1 := by
    simpa [g, Vsub, V] using finrank_ker_B_pi_eq_one hc h h2 hcQ hcW
  obtain ⟨b, hb0, -, hbimg, hbcent, -⟩ := hc.dictB h
  have hbV : b ∈ M₀.img V :=
    M₀.img_mono hBV ((hbimg b).mpr ⟨1, (one_smul K b).symm⟩)
  have hbVsub : b ∈ Vsub := (hVsub_mem b).mpr hbV
  let b' : Vsub := ⟨b, hbVsub⟩
  have hbker : g b' = 0 := by
    have h1 : M₀.B (M₀.π c) b = 0 := (hbcent c hcQ).mp hcB
    simpa [b', g] using h1
  have hLle : Submodule.span K ({b'} : Set Vsub) ≤ g.ker := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact LinearMap.mem_ker.mpr hbker
  have hb'0 : b' ≠ 0 := fun hh => hb0 (congrArg Subtype.val hh)
  have hLfin : Module.finrank K (Submodule.span K ({b'} : Set Vsub)) = 1 :=
    finrank_span_singleton hb'0
  have hLeq : Submodule.span K ({b'} : Set Vsub) = g.ker :=
    Submodule.eq_of_le_of_finrank_eq hLle (by rw [hLfin, hkerdim])
  have hspan : (⟨M₀.π x, hxVsub⟩ : Vsub) ∈ Submodule.span K ({b'} : Set Vsub) := by
    rw [hLeq]
    exact LinearMap.mem_ker.mpr hfx
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hspan
  have hpi : M₀.π x = s • b := by
    have h1 := congrArg Subtype.val hs
    simpa [b'] using h1.symm
  exact (hbimg _).mpr ⟨s, hpi⟩

private theorem mem_B_of_pi_mem_img_B {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) {t x : G} {Y : Subgroup G}
    (hBY : B ≤ QB Y) (hZQB : Z ⊓ QB Y = ⊥) (hxQY : x ∈ QB Y)
    (hxV : x ∈ Vt M (LB M Q B) B Z t) (hπ : M₀.π x ∈ M₀.img B) : x ∈ B := by
  obtain ⟨b₁, hb₁B, hb₁Q, hb₁π⟩ := M₀.mem_img.mp hπ
  have hxZ : x⁻¹ * b₁ ∈ Z :=
    (M₀.pi_eq_iff (hc.Vt_le_Q t hxV) (hc.le hb₁B)).mp hb₁π.symm
  have hxQB : x⁻¹ * b₁ ∈ QB Y :=
    (QB Y).mul_mem ((QB Y).inv_mem hxQY) (hBY hb₁B)
  have hbot : x⁻¹ * b₁ ∈ Z ⊓ QB Y := ⟨hxZ, hxQB⟩
  rw [hZQB, Subgroup.mem_bot] at hbot
  have hxb : x = b₁ := by
    calc x = x * 1 := (mul_one x).symm
      _ = x * (x⁻¹ * b₁) := by rw [hbot]
      _ = b₁ := by group
  rwa [hxb]

theorem Good101.inf_Vt_inf_centralizer_eq {hc : Ctx M Q Z B}
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) :
    Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G) = B := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht.mem_LB
  have hBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hZQB : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hBc : B ≤ Subgroup.centralizer ({c} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcB b hb)
  refine le_antisymm ?_ ?_
  · intro x hx
    simp only [Subgroup.mem_inf] at hx
    obtain ⟨⟨⟨-, hxQY⟩, hxV⟩, hxC⟩ := hx
    exact mem_B_of_pi_mem_img_B hc hBY hZQB hxQY hxV
      (pi_mem_img_B_of_mem_Vt_inf_centralizer hc hD h2 hcQ hcB hcW hBV hxV hxC)
  · intro b hb
    exact ⟨⟨⟨hc.le hb, hBY hb⟩, hBV hb⟩, hBc hb⟩

end CFSG.RankThree.GF2n.Stroth80
