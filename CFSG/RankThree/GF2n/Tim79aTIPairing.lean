module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

structure TIPairData (M V P A E : Subgroup G) (Y : Set G) (Aj : G → Subgroup G) : Prop where
  VleP : V ≤ P
  PleM : P ≤ M
  normV : ∀ m ∈ M, conjSubgroup m V = V
  normP : ∀ m ∈ M, conjSubgroup m P = P
  maxAb : Maximal (fun U : Subgroup G =>
    U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧ IsMulCommutative U) V
  PcentV : ∀ x ∈ P, ∀ v ∈ V, x * v = v * x
  PcommV : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V
  ti : IsTI V
  AleV : A ≤ V
  AjleV : ∀ y ∈ Y, Aj y ≤ conjSubgroup y V
  AjleP : ∀ y ∈ Y, Aj y ≤ P
  AjeqP : ∀ y ∈ Y, ¬ Aj y ≤ V → Aj y = conjSubgroup y V ⊓ P
  Ajcard : ∀ y ∈ Y, Nat.card (Aj y) = Nat.card A
  Ajcomm : ∀ y ∈ Y, ∀ x ∈ P, ∀ α ∈ Aj y, ⁅x, α⁆ ∈ A
  EleP : E ≤ P
  AjleE : ∀ y ∈ Y, Aj y ≤ E
  abelL : ∀ x ∈ V ⊔ E, ∀ z ∈ V ⊔ E, x * z = z * x
  moves : ∃ y ∈ Y, ¬ Aj y ≤ V
  beta : ∀ x ∈ P, (∀ y ∈ Y, ∀ α ∈ Aj y, x * α = α * x) → x ∈ V ⊔ E

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

theorem tiPair_conj_conj (g h : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup h T) = conjSubgroup (g * h) T := by
  ext x
  simp only [mem_conjSubgroup]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem tiPair_conj_one (T : Subgroup G) : conjSubgroup 1 T = T := by
  ext x
  simp [mem_conjSubgroup]

theorem tiPair_card_conj (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem tiPair_conj_inf (g : G) (S T : Subgroup G) :
    conjSubgroup g (S ⊓ T) = conjSubgroup g S ⊓ conjSubgroup g T :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

theorem tiPair_conj_bot (g : G) : conjSubgroup g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem tiPair_conj_mono (g : G) {S T : Subgroup G} (h : S ≤ T) :
    conjSubgroup g S ≤ conjSubgroup g T :=
  Subgroup.map_mono h

theorem tiPair_conj_mem (g : G) {x : G} {T : Subgroup G} (hx : x ∈ T) :
    g * x * g⁻¹ ∈ conjSubgroup g T := by
  rw [mem_conjSubgroup]
  simpa [mul_assoc] using hx

theorem tiPair_conj_eq_of_inf_ne_bot [Finite G] {V : Subgroup G} (hti : IsTI V) {a b : G}
    (h : conjSubgroup a V ⊓ conjSubgroup b V ≠ ⊥) : conjSubgroup a V = conjSubgroup b V := by
  have h1 : V ⊓ conjSubgroup (a⁻¹ * b) V ≠ ⊥ := by
    intro h0
    apply h
    have h2 := congrArg (conjSubgroup a) h0
    rwa [tiPair_conj_inf, tiPair_conj_conj, mul_inv_cancel_left, tiPair_conj_bot] at h2
  rcases hti (a⁻¹ * b) with h2 | h2
  · exact absurd h2 h1
  · have heq : V = conjSubgroup (a⁻¹ * b) V :=
      Subgroup.eq_of_le_of_card_ge (inf_eq_left.1 h2) (tiPair_card_conj _ _).le
    calc conjSubgroup a V = conjSubgroup a (conjSubgroup (a⁻¹ * b) V) := by rw [← heq]
      _ = conjSubgroup b V := by rw [tiPair_conj_conj, mul_inv_cancel_left]

namespace TIPairData

variable {M V P A E : Subgroup G} {Y : Set G} {Aj : G → Subgroup G}

theorem sup_le_P (D : TIPairData M V P A E Y Aj) : V ⊔ E ≤ P :=
  sup_le D.VleP D.EleP

theorem V_comm (D : TIPairData M V P A E Y Aj) {v w : G} (hv : v ∈ V) (hw : w ∈ V) :
    v * w = w * v :=
  D.PcentV v (D.VleP hv) w hw

theorem comm_mul_right (D : TIPairData M V P A E Y Aj) {b x y : G} (hb : b ∈ P) (hx : x ∈ P)
    (hy : y ∈ P) : ⁅b, x * y⁆ = ⁅b, x⁆ * ⁅b, y⁆ := by
  have h1 : ⁅b, x * y⁆ = ⁅b, x⁆ * (x * ⁅b, y⁆ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h2 : x * ⁅b, y⁆ = ⁅b, y⁆ * x := D.PcentV x hx _ (D.PcommV b hb y hy)
  rw [h1, h2, mul_inv_cancel_right]

theorem comm_inv_right (D : TIPairData M V P A E Y Aj) {b x : G} (hb : b ∈ P) (hx : x ∈ P) :
    ⁅b, x⁻¹⁆ = ⁅b, x⁆⁻¹ := by
  have h := D.comm_mul_right hb hx (P.inv_mem hx)
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem comm_mul_left (D : TIPairData M V P A E Y Aj) {b x y : G} (hb : b ∈ P) (hx : x ∈ P)
    (hy : y ∈ P) : ⁅x * y, b⁆ = ⁅x, b⁆ * ⁅y, b⁆ := by
  rw [← commutatorElement_inv b (x * y), D.comm_mul_right hb hx hy, mul_inv_rev,
    commutatorElement_inv, commutatorElement_inv]
  exact D.V_comm (D.PcommV y hy b hb) (D.PcommV x hx b hb)

theorem comm_inv_left (D : TIPairData M V P A E Y Aj) {b x : G} (hb : b ∈ P) (hx : x ∈ P) :
    ⁅x⁻¹, b⁆ = ⁅x, b⁆⁻¹ := by
  rw [← commutatorElement_inv b x⁻¹, D.comm_inv_right hb hx, commutatorElement_inv]

theorem centralizes_of_commute (D : TIPairData M V P A E Y Aj) {S : Subgroup G} (hSP : S ≤ P)
    (hSV : S ⊓ V = ⊥) (hTI : ∀ m ∈ M, conjSubgroup m S ⊓ S ≠ ⊥ → conjSubgroup m S = S)
    {x s : G} (hx : x ∈ P) (hs : s ∈ S) (hs1 : s ≠ 1) (hxs : x * s = s * x) :
    ∀ t ∈ S, x * t = t * x := by
  have hsx : s ∈ conjSubgroup x S := by
    rw [mem_conjSubgroup]
    have h1 : x⁻¹ * s * x = s := by rw [mul_assoc, ← hxs, inv_mul_cancel_left]
    rwa [h1]
  have hne : conjSubgroup x S ⊓ S ≠ ⊥ := by
    intro h0
    apply hs1
    have h1 : s ∈ conjSubgroup x S ⊓ S := ⟨hsx, hs⟩
    rw [h0] at h1
    exact Subgroup.mem_bot.1 h1
  have heq := hTI x (D.PleM hx) hne
  intro t ht
  have hc : ⁅x, t⁆ ∈ S := by
    have h1 := tiPair_conj_mem x ht
    rw [heq] at h1
    rw [commutatorElement_def]
    exact S.mul_mem h1 (S.inv_mem ht)
  have h1 : ⁅x, t⁆ ∈ S ⊓ V := ⟨hc, D.PcommV x hx t (hSP ht)⟩
  rw [hSV, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem Aj_inf_V (D : TIPairData M V P A E Y Aj) [Finite G] {y : G} (hy : y ∈ Y)
    (hA : ¬ Aj y ≤ V) : Aj y ⊓ V = ⊥ := by
  rcases D.ti y with h | h
  · rw [eq_bot_iff, ← h]
    exact le_inf inf_le_right (inf_le_left.trans (D.AjleV y hy))
  · exfalso
    have heq : V = conjSubgroup y V :=
      Subgroup.eq_of_le_of_card_ge (inf_eq_left.1 h) (tiPair_card_conj _ _).le
    exact hA ((D.AjleV y hy).trans heq.symm.le)

theorem conj_Aj_eq (D : TIPairData M V P A E Y Aj) {h y : G} (hh : h ∈ M) (hy : y ∈ Y)
    (hA : ¬ Aj y ≤ V) : conjSubgroup h (Aj y) = conjSubgroup (h * y) V ⊓ P := by
  rw [D.AjeqP y hy hA, tiPair_conj_inf, tiPair_conj_conj, D.normP h hh]

theorem conj_Aj_TI (D : TIPairData M V P A E Y Aj) [Finite G] {h y : G} (hh : h ∈ M)
    (hy : y ∈ Y) (hA : ¬ Aj y ≤ V) {m : G} (hm : m ∈ M)
    (hne : conjSubgroup m (conjSubgroup h (Aj y)) ⊓ conjSubgroup h (Aj y) ≠ ⊥) :
    conjSubgroup m (conjSubgroup h (Aj y)) = conjSubgroup h (Aj y) := by
  rw [tiPair_conj_conj] at hne ⊢
  rw [D.conj_Aj_eq (M.mul_mem hm hh) hy hA, D.conj_Aj_eq hh hy hA] at hne ⊢
  have h1 : conjSubgroup (m * h * y) V ⊓ conjSubgroup (h * y) V ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff, ← h0]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  rw [tiPair_conj_eq_of_inf_ne_bot D.ti h1]

theorem conj_Aj_inf_V (D : TIPairData M V P A E Y Aj) [Finite G] {h y : G} (hh : h ∈ M)
    (hy : y ∈ Y) (hA : ¬ Aj y ≤ V) : conjSubgroup h (Aj y) ⊓ V = ⊥ := by
  calc conjSubgroup h (Aj y) ⊓ V = conjSubgroup h (Aj y) ⊓ conjSubgroup h V := by
        rw [D.normV h hh]
    _ = ⊥ := by rw [← tiPair_conj_inf, D.Aj_inf_V hy hA, tiPair_conj_bot]

theorem conj_Aj_le_P (D : TIPairData M V P A E Y Aj) {h y : G} (hh : h ∈ M) (hy : y ∈ Y) :
    conjSubgroup h (Aj y) ≤ P :=
  (tiPair_conj_mono h (D.AjleP y hy)).trans (D.normP h hh).le

theorem exists_conj_sup_ne (D : TIPairData M V P A E Y Aj) :
    ∃ h ∈ M, conjSubgroup h (V ⊔ E) ≠ V ⊔ E := by
  by_contra hcon
  push Not at hcon
  have hL : V ⊔ E ≤ M ∧ M ≤ Subgroup.normalizer ((V ⊔ E : Subgroup G) : Set G) ∧
      IsMulCommutative (V ⊔ E : Subgroup G) := by
    refine ⟨D.sup_le_P.trans D.PleM, fun m hm => ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hcon m hm
    · exact isMulCommutative_iff.2 fun a b => Subtype.ext (D.abelL a a.2 b b.2)
  have hle : V ⊔ E ≤ V := D.maxAb.2 hL le_sup_left
  obtain ⟨y, hy, hA⟩ := D.moves
  exact hA ((D.AjleE y hy).trans (le_sup_right.trans hle))

theorem exists_conj_Aj_not_le (D : TIPairData M V P A E Y Aj) [Finite G] {h : G} (hh : h ∈ M)
    (hne : conjSubgroup h (V ⊔ E) ≠ V ⊔ E) : ∃ y ∈ Y, ¬ conjSubgroup h (Aj y) ≤ V ⊔ E := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hsub : conjSubgroup h⁻¹ (V ⊔ E) ≤ V ⊔ E := by
    intro x hx
    have hxP : x ∈ P := by
      have h1 := tiPair_conj_mono h⁻¹ D.sup_le_P
      rw [D.normP h⁻¹ (M.inv_mem hh)] at h1
      exact h1 hx
    refine D.beta x hxP fun y hy α hα => ?_
    have hα' : h * α * h⁻¹ ∈ V ⊔ E := hcon y hy (tiPair_conj_mem h hα)
    rw [mem_conjSubgroup, inv_inv] at hx
    have h1 := D.abelL _ hx _ hα'
    calc x * α = h⁻¹ * ((h * x * h⁻¹) * (h * α * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * α * h⁻¹) * (h * x * h⁻¹)) * h := by rw [h1]
      _ = α * x := by group
  have heq : conjSubgroup h⁻¹ (V ⊔ E) = V ⊔ E :=
    Subgroup.eq_of_le_of_card_ge hsub (tiPair_card_conj _ _).ge
  calc conjSubgroup h (V ⊔ E) = conjSubgroup h (conjSubgroup h⁻¹ (V ⊔ E)) := by rw [heq]
    _ = V ⊔ E := by rw [tiPair_conj_conj, mul_inv_cancel, tiPair_conj_one]

theorem pairing (D : TIPairData M V P A E Y Aj) [Finite G] :
    ∃ B : Subgroup G, (∃ h ∈ M, ∃ y ∈ Y, B = conjSubgroup h (Aj y)) ∧ B ≤ P ∧ ¬ B ≤ V ⊔ E ∧
      B ⊓ V = ⊥ ∧ (∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B) ∧
      ∃ y' ∈ Y, ¬ Aj y' ≤ V ∧ ∀ b ∈ B, b ≠ 1 → ∀ a ∈ A, ∃! α : G, α ∈ Aj y' ∧ ⁅b, α⁆ = a := by
  obtain ⟨h, hh, hne⟩ := D.exists_conj_sup_ne
  obtain ⟨y, hy, hBL⟩ := D.exists_conj_Aj_not_le hh hne
  have hyV : ¬ Aj y ≤ V := fun hle =>
    hBL (((tiPair_conj_mono h hle).trans (D.normV h hh).le).trans le_sup_left)
  have hBP := D.conj_Aj_le_P hh hy
  have hBV := D.conj_Aj_inf_V hh hy hyV
  have hBTI : ∀ m ∈ M, conjSubgroup m (conjSubgroup h (Aj y)) ⊓ conjSubgroup h (Aj y) ≠ ⊥ →
      conjSubgroup m (conjSubgroup h (Aj y)) = conjSubgroup h (Aj y) :=
    fun m hm hne' => D.conj_Aj_TI hh hy hyV hm hne'
  obtain ⟨b₁, hb₁B, hb₁L⟩ := SetLike.not_le_iff_exists.1 hBL
  have hb₁P := hBP hb₁B
  obtain ⟨y', hy', α₁, hα₁, hne1⟩ : ∃ y' ∈ Y, ∃ α₁ ∈ Aj y', b₁ * α₁ ≠ α₁ * b₁ := by
    by_contra hc
    push Not at hc
    exact hb₁L (D.beta b₁ hb₁P hc)
  have hy'V : ¬ Aj y' ≤ V := fun hle => hne1 (D.PcentV b₁ hb₁P α₁ (hle hα₁))
  have hA'P := D.AjleP y' hy'
  have hA'V := D.Aj_inf_V hy' hy'V
  have hA'TI : ∀ m ∈ M, conjSubgroup m (Aj y') ⊓ Aj y' ≠ ⊥ → conjSubgroup m (Aj y') = Aj y' := by
    intro m hm hne'
    have h1 := D.conj_Aj_TI M.one_mem hy' hy'V hm
    rw [tiPair_conj_one] at h1
    exact h1 hne'
  have hnocent : ∀ α ∈ Aj y', α ≠ 1 → (∀ t ∈ conjSubgroup h (Aj y), α * t = t * α) → False := by
    intro α hα hα1 hcent
    have h2 := D.centralizes_of_commute hA'P hA'V hA'TI hb₁P hα hα1 (hcent b₁ hb₁B).symm
    exact hne1 (h2 α₁ hα₁)
  have hker : ∀ b ∈ conjSubgroup h (Aj y), b ≠ 1 → ∀ α ∈ Aj y', ⁅b, α⁆ = 1 → α = 1 := by
    intro b hb hb1 α hα hbα
    by_contra hα1
    have h1 : α * b = b * α := (commutatorElement_eq_one_iff_mul_comm.1 hbα).symm
    exact hnocent α hα hα1 (D.centralizes_of_commute hBP hBV hBTI (hA'P hα) hb hb1 h1)
  refine ⟨conjSubgroup h (Aj y), ⟨h, hh, y, hy, rfl⟩, hBP, hBL, hBV, hBTI, y', hy', hy'V, ?_⟩
  intro b hb hb1 a ha
  have hbP := hBP hb
  let f : Aj y' → A := fun α => ⟨⁅b, (α : G)⁆, D.Ajcomm y' hy' b hbP α α.2⟩
  have hinj : Function.Injective f := by
    intro α β hαβ
    have h1 : ⁅b, (α : G)⁆ = ⁅b, (β : G)⁆ := congrArg Subtype.val hαβ
    have h2 : ⁅b, (β : G)⁻¹ * α⁆ = 1 := by
      rw [D.comm_mul_right hbP (P.inv_mem (hA'P β.2)) (hA'P α.2),
        D.comm_inv_right hbP (hA'P β.2), h1, inv_mul_cancel]
    have h3 := hker b hb hb1 _ ((Aj y').mul_mem ((Aj y').inv_mem β.2) α.2) h2
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (D.Ajcard y' hy').ge
  obtain ⟨α, hα⟩ := hbij.2 ⟨a, ha⟩
  refine ⟨(α : G), ⟨α.2, congrArg Subtype.val hα⟩, ?_⟩
  rintro β ⟨hβ, hβa⟩
  have h1 : f ⟨β, hβ⟩ = f α := Subtype.ext (hβa.trans (congrArg Subtype.val hα).symm)
  exact congrArg Subtype.val (hinj h1)

theorem exists_comm_mem_A (D : TIPairData M V P A E Y Aj) [Finite G] {B : Subgroup G}
    (hBP : B ≤ P) (hcard : Nat.card V < Nat.card B * Nat.card A) {g : G} (hg : g ∈ P) :
    ∃ b₀ ∈ B, b₀ ≠ 1 ∧ ⁅b₀, g⁆ ∈ A := by
  let F : B × A → V := fun p =>
    ⟨⁅(p.1 : G), g⁆ * p.2, V.mul_mem (D.PcommV _ (hBP p.1.2) g hg) (D.AleV p.2.2)⟩
  have hF : ¬ Function.Injective F := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective F hinj
    rw [Nat.card_prod] at h1
    exact absurd hcard (not_lt.2 h1)
  obtain ⟨⟨b, a⟩, ⟨b', a'⟩, hFeq, hne⟩ := Function.not_injective_iff.1 hF
  have h1 : ⁅(b : G), g⁆ * a = ⁅(b' : G), g⁆ * a' := congrArg Subtype.val hFeq
  have hbb' : (b : G) ≠ b' := by
    intro hbb
    apply hne
    have hb : b = b' := Subtype.ext hbb
    subst hb
    have ha : a = a' := Subtype.ext (mul_left_cancel h1)
    rw [ha]
  refine ⟨(b' : G)⁻¹ * b, B.mul_mem (B.inv_mem b'.2) b.2,
    fun h0 => hbb' (inv_mul_eq_one.1 h0).symm, ?_⟩
  have h2 : ⁅(b' : G), g⁆⁻¹ * ⁅(b : G), g⁆ = a' * (a : G)⁻¹ := by
    calc ⁅(b' : G), g⁆⁻¹ * ⁅(b : G), g⁆ = ⁅(b' : G), g⁆⁻¹ * (⁅(b : G), g⁆ * a) * (a : G)⁻¹ := by
          group
      _ = ⁅(b' : G), g⁆⁻¹ * (⁅(b' : G), g⁆ * a') * (a : G)⁻¹ := by rw [h1]
      _ = a' * (a : G)⁻¹ := by group
  rw [D.comm_mul_left hg (P.inv_mem (hBP b'.2)) (hBP b.2), D.comm_inv_left hg (hBP b'.2), h2]
  exact A.mul_mem a'.2 (A.inv_mem a.2)

theorem tiEnd (D : TIPairData M V P A E Y Aj) [Finite G]
    (hcard : Nat.card V < Nat.card A * Nat.card A) :
    ∃ b ∈ P, b ∉ V ⊔ E ∧ ∀ x ∈ P, ⁅b, x⁆ ∈ A := by
  obtain ⟨B, ⟨h, hh, y, hy, hB⟩, hBP, hBL, hBV, hBTI, y', hy', -, hpair⟩ := D.pairing
  have hBcard : Nat.card B = Nat.card A := by
    rw [hB, tiPair_card_conj, D.Ajcard y hy]
  have key : ∀ g ∈ P, ∀ b ∈ B, ⁅b, g⁆ ∈ A := by
    intro g hg
    obtain ⟨b₀, hb₀, hb₀1, hb₀A⟩ := D.exists_comm_mem_A hBP (by rwa [hBcard]) hg
    obtain ⟨α, ⟨hα, hαeq⟩, -⟩ := hpair b₀ hb₀ hb₀1 _ hb₀A
    have hαP := D.AjleP y' hy' hα
    have hcP : g * α⁻¹ ∈ P := P.mul_mem hg (P.inv_mem hαP)
    have hcb₀ : ⁅b₀, g * α⁻¹⁆ = 1 := by
      rw [D.comm_mul_right (hBP hb₀) hg (P.inv_mem hαP), D.comm_inv_right (hBP hb₀) hαP, hαeq,
        mul_inv_cancel]
    have hcent := D.centralizes_of_commute hBP hBV hBTI hcP hb₀ hb₀1
      (commutatorElement_eq_one_iff_mul_comm.1 hcb₀).symm
    intro b hb
    have h1 : ⁅b, g⁆ = ⁅b, α⁆ :=
      calc ⁅b, g⁆ = ⁅b, g * α⁻¹ * α⁆ := by rw [inv_mul_cancel_right]
        _ = ⁅b, g * α⁻¹⁆ * ⁅b, α⁆ := D.comm_mul_right (hBP hb) hcP hαP
        _ = ⁅b, α⁆ := by
          rw [commutatorElement_eq_one_iff_mul_comm.2 (hcent b hb).symm, one_mul]
    rw [h1]
    exact D.Ajcomm y' hy' b (hBP hb) α hα
  obtain ⟨b₁, hb₁B, hb₁L⟩ := SetLike.not_le_iff_exists.1 hBL
  exact ⟨b₁, hBP hb₁B, hb₁L, fun x hx => key x hx b₁ hb₁B⟩

end TIPairData

theorem tiPairingStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V P A E : Subgroup G) (Y : Set G) (Aj : G → Subgroup G),
      TIPairData M V P A E Y Aj →
      ∃ B : Subgroup G, (∃ h ∈ M, ∃ y ∈ Y, B = conjSubgroup h (Aj y)) ∧ B ≤ P ∧ ¬ B ≤ V ⊔ E ∧
        B ⊓ V = ⊥ ∧ (∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B) ∧
        ∃ y' ∈ Y, ¬ Aj y' ≤ V ∧ ∀ b ∈ B, b ≠ 1 → ∀ a ∈ A, ∃! α : G, α ∈ Aj y' ∧ ⁅b, α⁆ = a :=
  fun _ _ _ _ _ _ _ _ _ _ D => D.pairing

theorem tiEndStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V P A E : Subgroup G) (Y : Set G) (Aj : G → Subgroup G),
      TIPairData M V P A E Y Aj → Nat.card V < Nat.card A * Nat.card A →
      ∃ b ∈ P, b ∉ V ⊔ E ∧ ∀ x ∈ P, ⁅b, x⁆ ∈ A :=
  fun _ _ _ _ _ _ _ _ _ _ D hcard => D.tiEnd hcard

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

namespace TIPairData

variable {M V P A E : Subgroup G} {Y : Set G} {Aj : G → Subgroup G}

theorem card_le_of_summand (D : TIPairData M V P A E Y Aj) [Finite G] {A₁ S₁ : Subgroup G}
    (hS₁P : S₁ ≤ P) (hcomm : ∀ x ∈ P, ∀ f ∈ S₁, ⁅x, f⁆ ∈ A₁)
    (hβ : ∀ x ∈ P, (∀ f ∈ S₁, x * f = f * x) → x ∈ V ⊔ E) :
    Nat.card A ≤ Nat.card A₁ := by
  obtain ⟨B, ⟨h, hh, y, hy, hB⟩, hBP, hBL, hBV, hBTI, -⟩ := D.pairing
  have hBcard : Nat.card B = Nat.card A := by
    rw [hB, tiPair_card_conj, D.Ajcard y hy]
  obtain ⟨b₁, hb₁B, hb₁L⟩ := SetLike.not_le_iff_exists.1 hBL
  obtain ⟨f, hf, hne⟩ : ∃ f ∈ S₁, b₁ * f ≠ f * b₁ := by
    by_contra hc
    push Not at hc
    exact hb₁L (hβ b₁ (hBP hb₁B) hc)
  have hfP := hS₁P hf
  let φ : B → A₁ := fun b => ⟨⁅f, (b : G)⁆, by
    rw [← commutatorElement_inv]
    exact A₁.inv_mem (hcomm b (hBP b.2) f hf)⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb'
    have h1 : ⁅f, (b : G)⁆ = ⁅f, (b' : G)⁆ := congrArg Subtype.val hbb'
    have h2 : ⁅f, (b' : G)⁻¹ * b⁆ = 1 := by
      rw [D.comm_mul_right hfP (P.inv_mem (hBP b'.2)) (hBP b.2),
        D.comm_inv_right hfP (hBP b'.2), h1, inv_mul_cancel]
    by_contra hne'
    have hs1 : (b' : G)⁻¹ * b ≠ 1 := fun h0 => hne' (Subtype.ext (inv_mul_eq_one.1 h0).symm)
    have hcent := D.centralizes_of_commute hBP hBV hBTI hfP
      (B.mul_mem (B.inv_mem b'.2) b.2) hs1 (commutatorElement_eq_one_iff_mul_comm.1 h2)
    exact hne (hcent b₁ hb₁B).symm
  rw [← hBcard]
  exact Nat.card_le_card_of_injective φ hinj

end TIPairData

theorem tiSummandStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M V P A E : Subgroup G) (Y : Set G) (Aj : G → Subgroup G)
      (A₁ S₁ : Subgroup G), TIPairData M V P A E Y Aj → A₁ ≤ V → S₁ ≤ P →
      (∀ x ∈ P, ∀ f ∈ S₁, ⁅x, f⁆ ∈ A₁) →
      (∀ x ∈ P, (∀ f ∈ S₁, x * f = f * x) → x ∈ V ⊔ E) →
      Nat.card ↥A ≤ Nat.card ↥A₁ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ D _ hS₁P hcomm hβ => D.card_le_of_summand hS₁P hcomm hβ

end CFSG.RankThree.GF2n.Tim79a
