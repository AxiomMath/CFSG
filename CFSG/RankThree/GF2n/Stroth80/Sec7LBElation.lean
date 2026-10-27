module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Wild

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K}

@[expose] def sec7LBCent (hc : Ctx M Q Z B) (M₀ : Tim79.QuadModel Q Z K γ)
    (Y : Submodule K M₀.E) : Subgroup G where
  carrier := {x | x ∈ LB M Q B ∧ ∀ y ∈ Q ⊓ QB B, M₀.π y ∈ Y → ⁅x, y⁆ ∈ Z}
  mul_mem' := by
    rintro x x' ⟨hx, hxc⟩ ⟨hx', hxc'⟩
    refine ⟨(LB M Q B).mul_mem hx hx', fun y hy hyY => ?_⟩
    have hxM : x ∈ M := hc.LB_le_M hx
    have e : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) _).mp
      (hxc' y hy hyY)) (hxc y hy hyY)
  one_mem' := ⟨(LB M Q B).one_mem, fun y _ _ => by
    rw [commutatorElement_one_left]
    exact Z.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hxc⟩
    refine ⟨(LB M Q B).inv_mem hx, fun y hy hyY => ?_⟩
    have hxM : x ∈ M := hc.LB_le_M hx
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * (⁅x, y⁆)⁻¹ * (x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hxM)) _).mp
      (Z.inv_mem (hxc y hy hyY))

variable [CharP K 2] {M₀ : Tim79.QuadModel Q Z K γ}

theorem sec7_LB_elation (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    (h : GlobalModelData M Q Z γ M₀) :
    ∃ (T : Submodule K M₀.E) (b : T),
      (∀ v, v ∈ T ↔ v ∈ M₀.img (Q ⊓ QB B)) ∧ Module.finrank K T = n ∧
      (∀ v : M₀.E, (∀ u ∈ T, M₀.B v u = 0) → v ∈ T) ∧ (b : M₀.E) ≠ 0 ∧
      (∀ v, v ∈ M₀.img B ↔ ∃ c : K, v = c • (b : M₀.E)) ∧
      (∀ l ∈ LB M Q B, ∀ S : M₀.E ≃ₗ[K] M₀.E,
        (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) →
        S b = b ∧ (∀ e ∈ T, ∃ c : K, S e - e = c • (b : M₀.E)) ∧
        (∀ e, M₀.B e b = 0 → S e - e ∈ T) ∧ ((∀ e ∈ T, S e = e) ↔ l ∈ Q)) ∧
      (∀ f : Module.Dual K T, f b = 0 → ∃ l ∈ LB M Q B,
        ∀ S : M₀.E ≃ₗ[K] M₀.E, (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) →
          ∀ y : T, S y = y + f y • (b : M₀.E)) := by
  classical
  obtain ⟨W, b, θ, hW, hb0, hB, hfix, hel, hker, hfr, hcomm, hSθ⟩ :=
    hc.exists_elation_action hw hn hno hcardL h
  obtain ⟨W', hW'mem, hW'o⟩ := hc.img_inf_QB_lagrangian hw hn hno h
  have hb0' : (b : M₀.E) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
  have hQLB : Q ≤ LB M Q B := sec39_Q_le_LB
  have hθker : θ.ker = Q.subgroupOf (LB M Q B) := by
    ext g
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hcard : Nat.card (LB M Q B) = Nat.card θ.ker * Nat.card K ^ (Module.finrank K W - 1) := by
    rw [hθker, hfr, hcardLB, hKZ]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQLB).toEquiv).symm
  refine ⟨W, b, hW, hfr, fun v hv => ?_, hb0', hB, fun l hl S hS => ?_, fun f hf => ?_⟩
  · have h1 : v ∈ W' := hW'o v fun u hu => hv u ((hW u).mpr ((hW'mem u).mpr hu))
    exact (hW v).mpr ((hW'mem v).mpr h1)
  · have hSb := hSθ ⟨l, hl⟩ S hS
    refine ⟨?_, fun e he => ?_, fun e he => ?_, ?_⟩
    · rw [← hSb b, hfix]
    · obtain ⟨c, hc'⟩ := hel ⟨l, hl⟩ ⟨e, he⟩
      refine ⟨c, ?_⟩
      have h1 := congrArg Subtype.val hc'
      rw [hSb] at h1
      have h2 : S e = e + c • (b : M₀.E) := h1
      rw [h2]
      abel
    · have hflag := (hc.LB_act_flag hw hn hno h hB hl (T := (S : M₀.E →ₗ[K] M₀.E)) hS).2.2 e he
      exact (hW _).mpr hflag
    · have hk := hker ⟨l, hl⟩
      constructor
      · intro hfx
        apply hk.mp
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        rw [hSb]
        exact hfx w w.2
      · intro hlQ e he
        have h1 := congrArg (fun F : W ≃ₗ[K] W => ((F ⟨e, he⟩ : W) : M₀.E)) (hk.mpr hlQ)
        have h2 : ((θ ⟨l, hl⟩ ⟨e, he⟩ : W) : M₀.E) = e := by simpa using h1
        exact (hSb ⟨e, he⟩).symm.trans h2
  · obtain ⟨Fd, hFdrep, -, -, -, hsurj⟩ := elation_dual_data hb0 θ hfix hel hcard
    have hfmem : f ∈ (Submodule.span K {b}).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hf, smul_zero]
    obtain ⟨g, hg⟩ := hsurj f hfmem
    refine ⟨(g : G), g.2, fun S hS y => ?_⟩
    have h2 := congrArg Subtype.val (hFdrep g y)
    rw [hSθ g S hS, hg] at h2
    exact h2

theorem sec7_LB_elation_count (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    (h : GlobalModelData M Q Z γ M₀) (Y : Submodule K M₀.E)
    (hYT : ∀ e ∈ Y, e ∈ M₀.img (Q ⊓ QB B)) (hBY : ∀ e ∈ M₀.img B, e ∈ Y) :
    Nat.card ↥(sec7LBCent hc M₀ Y) = Nat.card Q * Nat.card K ^ (n - Module.finrank K Y) := by
  classical
  obtain ⟨T, b, hT, hfT, -, hb0, hB, -⟩ := sec7_LB_elation hc hw hn hno hcardLB hcardL h
  have hLZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  set Y₀ : Subgroup G := sec7Pre M₀ Y.toAddSubgroup with hY₀def
  have hBY₀ : B ≤ Y₀ := fun x hx => ⟨hc.le hx, hBY _ (M₀.pi_mem_img hx (hc.le hx))⟩
  have hYL : Y₀ ≤ Q ⊓ QB B := fun x hx =>
    (Tim79.QuadModel.mem_img_iff M₀ hLZ hx.1).mp (hYT _ hx.2)
  have hYimg : ∀ e, e ∈ M₀.img Y₀ ↔ e ∈ Y := fun e => sec7_img_pre M₀ Y.toAddSubgroup e
  have hY₀K : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y₀ → c • e ∈ M₀.img Y₀ := fun c e he =>
    (hYimg _).mpr (Y.smul_mem c ((hYimg e).mp he))
  obtain ⟨b₁, hb₁Y, hb₁0, hb₁B, -, -, hcount⟩ :=
    hc.elation_package hw hn hno hcardLB hcardL h hBY₀ hYL hY₀K
  have hsub : imgSub M₀ Y₀ hY₀K = Y := Submodule.ext fun e => hYimg e
  have hfr : Module.finrank K ↥(imgSub M₀ Y₀ hY₀K) = Module.finrank K ↥Y :=
    congrArg (fun S : Submodule K M₀.E => Module.finrank K ↥S) hsub
  have hCmem : ∀ x, x ∈ sec7LBCent hc M₀ Y ↔ x ∈ LB M Q B ∧ ∀ y ∈ Y₀, ⁅x, y⁆ ∈ Z := by
    intro x
    constructor
    · rintro ⟨hx, hxc⟩
      exact ⟨hx, fun y hy => hxc y (hYL hy) hy.2⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨hx, fun y hy hyY => hxc y ⟨hy.1, hyY⟩⟩
  have hcnt := hcount (sec7LBCent hc M₀ Y) hCmem
  rw [hfr, hcardLB, ← h.card] at hcnt
  have hYle : Y ≤ T := fun e he => (hT e).mpr (hYT e he)
  have hdn : Module.finrank K Y ≤ n := hfT ▸ Submodule.finrank_mono hYle
  have hbimg : (b : M₀.E) ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K _).symm⟩
  have hd1 : 1 ≤ Module.finrank K Y := by
    have : 0 < Module.finrank K Y := Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨(b : M₀.E), hBY _ hbimg⟩, fun h0 => hb0 (congrArg Subtype.val h0)⟩
    omega
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hKpos : 0 < Nat.card K ^ (Module.finrank K Y - 1) := pow_pos Nat.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hKpos
  rw [← hcnt, mul_assoc, ← pow_add]
  congr 2
  omega

theorem sec7_LB_elation_card_le (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    (h : GlobalModelData M Q Z γ M₀) (Y : Submodule K M₀.E)
    (hYT : ∀ e ∈ Y, e ∈ M₀.img (Q ⊓ QB B)) (hBY : ∀ e ∈ M₀.img B, e ∈ Y)
    (D : Subgroup G) (hDL : D ≤ LB M Q B)
    (hDY : ∀ l ∈ D, ∀ y ∈ Q ⊓ QB B, M₀.π y ∈ Y → ⁅l, y⁆ ∈ Z) :
    Nat.card D ≤ Nat.card Q * Nat.card K ^ (n - Module.finrank K Y) := by
  rw [← sec7_LB_elation_count hc hw hn hno hcardLB hcardL h Y hYT hBY]
  exact Subgroup.card_le_of_le fun x hx => ⟨hDL hx, hDY x hx⟩

theorem sec7_LB_elation_exists_moved (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    (h : GlobalModelData M Q Z γ M₀) (Y : Submodule K M₀.E)
    (hYT : ∀ e ∈ Y, e ∈ M₀.img (Q ⊓ QB B)) (hBY : ∀ e ∈ M₀.img B, e ∈ Y)
    (D : Subgroup G) (hDL : D ≤ LB M Q B)
    (hD : Nat.card Q * Nat.card K ^ (n - Module.finrank K Y) < Nat.card D) :
    ∃ l ∈ D, ∃ y ∈ Q ⊓ QB B, M₀.π y ∈ Y ∧ ⁅l, y⁆ ∉ Z := by
  by_contra hcon
  push Not at hcon
  exact absurd (sec7_LB_elation_card_le hc hw hn hno hcardLB hcardL h Y hYT hBY D hDL
    fun l hl y hy hyY => hcon l hl y hy hyY) (not_le.mpr hD)

end CFSG.RankThree.GF2n.Stroth80
