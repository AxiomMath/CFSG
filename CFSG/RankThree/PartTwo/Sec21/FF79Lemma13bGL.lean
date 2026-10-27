module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bData
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bAct

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13b

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {b : G} {J B : Subgroup G}

theorem nor_of_sup {B B₁ B₂ : Subgroup G} (hsup : B₁ ⊔ B₂ = B) {k : G}
    (h1 : ∀ y ∈ B₁, k * y * k⁻¹ ∈ B₁) (h2 : ∀ y ∈ B₂, k * y * k⁻¹ ∈ B₂) : k ∈ Nor B := by
  apply mem_nor_of_forall
  intro y hy
  rw [← hsup] at hy ⊢
  have hle : (B₁ ⊔ B₂).map (MulAut.conj k).toMonoidHom ≤ B₁ ⊔ B₂ := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (by rintro _ ⟨y, hy, rfl⟩; exact h1 y hy)
      (by rintro _ ⟨y, hy, rfl⟩; exact h2 y hy)
  have := hle (Subgroup.mem_map_of_mem _ hy)
  simpa [MulAut.conj_apply] using this

namespace Data

variable (hD : Data b J B)
include hD

theorem conj_b_of_mem_cen {j : G} (hj : j ∈ Cen b) : j * b * j⁻¹ = b := by
  have := mem_cen_iff'.mp hj
  calc j * b * j⁻¹ = b * j * j⁻¹ := by rw [this]
    _ = b := by group

theorem nor_B {k : G} (hk : k * b * k⁻¹ = b ∨ k * b * k⁻¹ = b⁻¹)
    (h0 : ∀ y ∈ B ⊓ J, k * y * k⁻¹ ∈ B ⊓ J) : k ∈ Nor B := by
  refine nor_of_sup hD.hsup (fun y hy => ?_) h0
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow]
  refine Subgroup.zpow_mem _ ?_ m
  rcases hk with hk | hk <;> rw [hk]
  · exact Subgroup.mem_zpowers b
  · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)

theorem nor_B_of_J {j : G} (hj : j ∈ J) (hjn : j ∈ Nor (B ⊓ J)) : j ∈ Nor B :=
  hD.nor_B (Or.inl (hD.conj_b_of_mem_cen (hD.hJC hj))) fun y hy => conj_mem_of_nor hjn hy

theorem nor_J {k : G} (hk : k * b * k⁻¹ = b ∨ k * b * k⁻¹ = b⁻¹) : k ∈ Nor J :=
  mem_nor_of_forall (hD.hnormJ k hk)

theorem nor_B0 {k : G} (hk : k * b * k⁻¹ = b ∨ k * b * k⁻¹ = b⁻¹) (hkB : k ∈ Nor B) :
    k ∈ Nor (B ⊓ J) :=
  mem_nor_of_forall fun y hy => ⟨conj_mem_of_nor hkB hy.1, hD.hnormJ k hk y hy.2⟩

theorem conj_eq_on_B {n₁ n₂ : G} (hb₁ : n₁ * b * n₁⁻¹ = b) (hb₂ : n₂ * b * n₂⁻¹ = b)
    (hx : ∀ x ∈ B ⊓ J, n₁ * x * n₁⁻¹ = n₂ * x * n₂⁻¹) :
    ∀ y ∈ B, n₁ * y * n₁⁻¹ = n₂ * y * n₂⁻¹ := by
  let E := MonoidHom.eqLocus (MulAut.conj n₁).toMonoidHom (MulAut.conj n₂).toMonoidHom
  have hE : B ≤ E := by
    rw [← hD.hsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show (MulAut.conj n₁).toMonoidHom b = (MulAut.conj n₂).toMonoidHom b
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hb₁, hb₂]
    · intro x hx'
      show (MulAut.conj n₁).toMonoidHom x = (MulAut.conj n₂).toMonoidHom x
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx x hx'
  intro y hy
  have h2 : (MulAut.conj n₁).toMonoidHom y = (MulAut.conj n₂).toMonoidHom y := hE hy
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2

variable (c : Coord B)
include c

theorem fix_iff {g : GL (Fin 3) (ZMod 3)} {n : G}
    (hg : ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹)) (hn : n ∈ Nor B) :
    act33 g (c.e b) = c.e b ↔ n * b * n⁻¹ = b := by
  rw [hg b hD.hbB]
  exact ⟨fun h => c.e_inj (conj_mem_of_nor hn hD.hbB) hD.hbB h, fun h => by rw [h]⟩

theorem neg_iff {g : GL (Fin 3) (ZMod 3)} {n : G}
    (hg : ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹)) (hn : n ∈ Nor B) :
    act33 g (c.e b) = -c.e b ↔ n * b * n⁻¹ = b⁻¹ := by
  rw [hg b hD.hbB, ← c.e_inv hD.hbB]
  exact ⟨fun h => c.e_inj (conj_mem_of_nor hn hD.hbB) (B.inv_mem hD.hbB) h, fun h => by rw [h]⟩

theorem exists_tau :
    ∃ τ ∈ c.X, act33 τ (c.e b) = c.e b ∧ ∀ x ∈ B ⊓ J, act33 τ (c.e x) = -c.e x := by
  obtain ⟨τ, hτJ, hτN, hτinv⟩ := hD.hτ
  have hk : τ * b * τ⁻¹ = b := hD.conj_b_of_mem_cen (hD.hJC hτJ)
  have hτB : τ ∈ Nor B := hD.nor_B (Or.inl hk) fun y hy => conj_mem_of_nor hτN hy
  obtain ⟨g, hg, hgx⟩ := c.exists_mem_X hτB
  refine ⟨g, hg, ?_, fun x hx => ?_⟩
  · rw [hgx b hD.hbB, hk]
  · rw [hgx x hx.1, hτinv x hx, c.e_inv hx.1]

theorem card_stab :
    Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ c.X ∧ act33 g (c.e b) = c.e b} = 8 := by
  let T : Set (GL (Fin 3) (ZMod 3)) := {g | g ∈ c.X ∧ act33 g (c.e b) = c.e b}
  let R : GL (Fin 3) (ZMod 3) → (↥(B ⊓ J) → G) := fun g x => c.d (act33 g (c.e (x : G)))
  have hinj : Set.InjOn R T := by
    rintro g₁ ⟨⟨n₁, hn₁, hg₁⟩, hf₁⟩ g₂ ⟨⟨n₂, hn₂, hg₂⟩, hf₂⟩ hR
    have hb₁ := (hD.fix_iff c hg₁ hn₁).mp hf₁
    have hb₂ := (hD.fix_iff c hg₂ hn₂).mp hf₂
    have hx : ∀ x ∈ B ⊓ J, n₁ * x * n₁⁻¹ = n₂ * x * n₂⁻¹ := by
      intro x hx
      have := congrFun hR ⟨x, hx⟩
      simpa only [R, hg₁ x hx.1, hg₂ x hx.1, c.d_e _ (conj_mem_of_nor hn₁ hx.1),
        c.d_e _ (conj_mem_of_nor hn₂ hx.1)] using this
    have hy := hD.conj_eq_on_B hb₁ hb₂ hx
    refine Coord.gl_ext fun u => ?_
    rw [c.act_eq hg₁, c.act_eq hg₂, hy _ (c.d_mem u)]
  have himg : R '' T = {f : ↥(B ⊓ J) → G | ∃ j ∈ J, j ∈ Nor (B ⊓ J) ∧
      ∀ x : ↥(B ⊓ J), f x = j * x * j⁻¹} := by
    ext f
    constructor
    · rintro ⟨g, ⟨⟨n, hn, hg⟩, hf⟩, rfl⟩
      have hnb := (hD.fix_iff c hg hn).mp hf
      obtain ⟨j, hjJ, hjN, hj⟩ :=
        hD.hlast n (hD.nor_J (Or.inl hnb)) (hD.nor_B0 (Or.inl hnb) hn)
      refine ⟨j, hjJ, hjN, fun x => ?_⟩
      simp only [R, hg x x.2.1, c.d_e _ (conj_mem_of_nor hn x.2.1)]
      exact hj x x.2
    · rintro ⟨j, hjJ, hjN, hf⟩
      obtain ⟨g, hg, hgx⟩ := c.exists_mem_X (hD.nor_B_of_J hjJ hjN)
      have hjb := hD.conj_b_of_mem_cen (hD.hJC hjJ)
      refine ⟨g, ⟨hg, ?_⟩, ?_⟩
      · rw [hgx b hD.hbB, hjb]
      · funext x
        simp only [R, hgx x x.2.1, c.d_e _ (conj_mem_of_nor (hD.nor_B_of_J hjJ hjN) x.2.1)]
        exact (hf x).symm
  have h1 : Nat.card ↥T = T.ncard := Nat.card_coe_set_eq T
  have h2 : (R '' T).ncard = T.ncard := hinj.ncard_image
  show Nat.card ↥T = 8
  rw [h1, ← h2, himg]
  exact hD.hcard

theorem exists_noncomm : ∃ g ∈ c.X, ∃ h ∈ c.X, act33 g (c.e b) = c.e b ∧
    act33 h (c.e b) = c.e b ∧ g * h ≠ h * g := by
  obtain ⟨j₁, hj₁, j₂, hj₂, hn₁, hn₂, x, hx, hne⟩ := hD.hnab
  have hB₁ := hD.nor_B_of_J hj₁ hn₁
  have hB₂ := hD.nor_B_of_J hj₂ hn₂
  obtain ⟨g, hg, hgx⟩ := c.exists_mem_X hB₁
  obtain ⟨h, hh, hhx⟩ := c.exists_mem_X hB₂
  refine ⟨g, hg, h, hh, ?_, ?_, fun heq => hne ?_⟩
  · rw [hgx b hD.hbB, hD.conj_b_of_mem_cen (hD.hJC hj₁)]
  · rw [hhx b hD.hbB, hD.conj_b_of_mem_cen (hD.hJC hj₂)]
  · have e1 : act33 (g * h) (c.e x) = c.e (j₂ * (j₁ * x * j₁⁻¹) * j₂⁻¹) := by
      rw [Coord.act33_mul, hgx x hx.1, hhx _ (conj_mem_of_nor hB₁ hx.1)]
    have e2 : act33 (h * g) (c.e x) = c.e (j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹) := by
      rw [Coord.act33_mul, hhx x hx.1, hgx _ (conj_mem_of_nor hB₂ hx.1)]
    rw [heq] at e1
    exact (c.e_inj (conj_mem_of_nor hB₁ (conj_mem_of_nor hB₂ hx.1))
      (conj_mem_of_nor hB₂ (conj_mem_of_nor hB₁ hx.1)) (e2.symm.trans e1))

theorem line_stab (W : Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (hW : ∀ u, u ∈ W ↔ c.d u ∈ B ⊓ J) :
    ∀ g ∈ c.X, (act33 g (c.e b) = c.e b ∨ act33 g (c.e b) = -c.e b) →
      (∀ w ∈ W, act33 g w ∈ W) ∧ ∃ d ∈ c.X, act33 d (c.e b) = c.e b ∧
        ((∀ w ∈ W, act33 g w = act33 d w) ∨ ∀ w ∈ W, act33 g w = -act33 d w) := by
  rintro g ⟨n, hn, hg⟩ hline
  have hk : n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹ :=
    hline.imp ((hD.fix_iff c hg hn).mp) ((hD.neg_iff c hg hn).mp)
  have hnJ : n ∈ Nor J := hD.nor_J hk
  have hn0 : n ∈ Nor (B ⊓ J) := hD.nor_B0 hk hn
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [c.act_eq hg, hW, c.d_e _ (conj_mem_of_nor hn (c.d_mem _))]
    exact conj_mem_of_nor hn0 ((hW w).mp hw)
  · obtain ⟨j, hjJ, hjN, hj⟩ := hD.hlast n hnJ hn0
    obtain ⟨d, hd, hdx⟩ := c.exists_mem_X (hD.nor_B_of_J hjJ hjN)
    refine ⟨d, hd, ?_, Or.inl fun w hw => ?_⟩
    · rw [hdx b hD.hbB, hD.conj_b_of_mem_cen (hD.hJC hjJ)]
    · rw [c.act_eq hg, c.act_eq hdx, hj _ ((hW w).mp hw)]

theorem exists_move : ∃ g ∈ c.X, act33 g (c.e b) ≠ c.e b ∧ act33 g (c.e b) ≠ -c.e b := by
  obtain ⟨n, hn, hnB, hnn⟩ := exists_nor_move hD.ord hD.hB hD.hbB hD.hab hD.hnsc
  obtain ⟨g, hg, hgx⟩ := c.exists_mem_X hn
  refine ⟨g, hg, fun h => hnn ?_, fun h => hnn ?_⟩
  · rw [(hD.fix_iff c hgx hn).mp h]
    exact Subgroup.mem_zpowers b
  · rw [(hD.neg_iff c hgx hn).mp h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)

end Data

end CFSG.RankThree.PartTwo.Sec21.FF79.L13b
