module

public import CFSG.Quasithin.Vol2.Ch11SecB23Point
public import CFSG.Quasithin.Vol2.Ch11SecBBasic
public import CFSG.Quasithin.Vol2.Ch11SecB23Core

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped IsMulCommutative Pointwise

section General

variable {G : Type} [Group G]

theorem conjV_eq_one_iff {V₁ : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V₁ : Set G)) :
    conjV V₁ x hx = 1 ↔ x ∈ Subgroup.centralizer (V₁ : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := congrArg (fun a : MulAut ↥V₁ => ((a ⟨v, hv⟩ : ↥V₁) : G)) h
    simp only [conjV_apply_coe] at this
    have e : x * v * x⁻¹ = v := this
    calc v * x = x * v * x⁻¹ * x := by rw [e]
      _ = x * v := by group
  · intro h
    ext v
    rw [conjV_apply_coe]
    have := (Subgroup.mem_centralizer_iff.mp h) v v.2
    calc x * (v : G) * x⁻¹ = v * x * x⁻¹ := by rw [this]
      _ = v := by group

theorem conjV_eq_conjV_iff {V₁ : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (V₁ : Set G)) (hy : y ∈ Subgroup.normalizer (V₁ : Set G)) :
    conjV V₁ x hx = conjV V₁ y hy ↔ x⁻¹ * y ∈ Subgroup.centralizer (V₁ : Set G) := by
  rw [← conjV_eq_one_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy),
    conjV_mul V₁ (Subgroup.inv_mem _ hx) hy, conjV_inv V₁ hx, inv_mul_eq_one]

theorem le_normalizer_of_forall {M : Type*} [Group M] {A B : Subgroup M}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) : A ≤ Subgroup.normalizer (B : Set M) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h a ha b, fun hb => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hb
  simpa [mul_assoc] using this

theorem mem_sup_of_conjV_mem {V₁ A : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.normalizer (V₁ : Set G)) (h : conjV V₁ z hz ∈ autOn A V₁) :
    z ∈ A ⊔ (Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.centralizer (V₁ : Set G)) := by
  obtain ⟨a, ha, haV, he⟩ := mem_autOn_iff.mp h
  have hc : a⁻¹ * z ∈ Subgroup.centralizer (V₁ : Set G) :=
    (conjV_eq_conjV_iff haV hz).mp he.symm
  have e : z = a * (a⁻¹ * z) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ha ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ haV) hz, hc⟩

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem autOn_inf_normalizer_le (h331 : Stmt3_3_1) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) :
    autOn (Subgroup.normalizer (V₁ : Set G)) V₁ ⊓
        Subgroup.normalizer (autOn T V₁ : Set (MulAut ↥V₁)) ≤
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G)) V₁ := by
  rintro _ ⟨hy, hyT⟩
  obtain ⟨y, -, hyV, rfl⟩ := mem_autOn_iff.mp hy
  set N₁ := Subgroup.normalizer (V₁ : Set G)
  set Q := T ⊔ (N₁ ⊓ Subgroup.centralizer (V₁ : Set G)) with hQ
  have hQN : Q ≤ N₁ := sup_le hTV₁ inf_le_left
  have hmemQ : ∀ z (hz : z ∈ N₁), z ∈ Q ↔ conjV V₁ z hz ∈ autOn T V₁ := by
    intro z hz
    refine ⟨fun hzQ => ?_, mem_sup_of_conjV_mem hz⟩
    have hDT : T ≤ Subgroup.normalizer
        ((N₁ ⊓ Subgroup.centralizer (V₁ : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf (hTV₁.trans Subgroup.le_normalizer)
        (B2F.le_normalizer_centralizer hTV₁)
    rw [← SetLike.mem_coe, hQ, sup_comm,
      Subgroup.coe_mul_of_right_le_normalizer_left _ T hDT] at hzQ
    obtain ⟨d, hd, t, ht, rfl⟩ := hzQ
    have hd1 : conjV V₁ d hd.1 = 1 := (conjV_eq_one_iff hd.1).mpr hd.2
    rw [conjV_mul V₁ hd.1 (hTV₁ ht), hd1, one_mul]
    exact conjV_mem_autOn ht _
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := by
    have key : ∀ x (hx : x ∈ N₁),
        conjV V₁ x hx ∈ Subgroup.normalizer (autOn T V₁ : Set (MulAut ↥V₁)) →
        ∀ z ∈ Q, x * z * x⁻¹ ∈ Q := by
      intro x hx hxT z hz
      have hzN := hQN hz
      have hc : x * z * x⁻¹ ∈ N₁ := Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hzN) (inv_mem hx)
      rw [hmemQ _ hc]
      rw [hmemQ _ hzN] at hz
      rw [← conjV_conj V₁ hx hzN]
      exact (Subgroup.mem_normalizer_iff.mp hxT _).mp hz
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨key y hyV hyT z, fun hz => ?_⟩
    have hyT' : conjV V₁ y⁻¹ (inv_mem hyV) ∈
        Subgroup.normalizer (autOn T V₁ : Set (MulAut ↥V₁)) := by
      rw [conjV_inv V₁ hyV]; exact inv_mem hyT
    have := key y⁻¹ (inv_mem hyV) hyT' _ hz
    simpa [mul_assoc] using this
  have hTQ : QuasithinUnique.IsSylowTwoOf T Q :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_left
  have hfr := B6.frattini_two (H := Subgroup.normalizer (Q : Set G) ⊓ N₁)
    (le_inf Subgroup.le_normalizer hQN) inf_le_left hTQ ⟨hyQ, hyV⟩
  have hKQ : (Subgroup.normalizer (Q : Set G) ⊓ N₁) ⊓ Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (Q : Set G) := inf_le_left.trans inf_le_left
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKQ] at hfr
  obtain ⟨q, hq, m, hm, rfl⟩ := hfr
  have hmN : m ∈ N₁ := hm.1.2
  have hqN : q ∈ N₁ := hQN hq
  rw [conjV_mul V₁ hqN hmN]
  refine Subgroup.mul_mem _ ?_ (conjV_mem_autOn
    (L := Subgroup.normalizer (L : Set G) ⊓ N₁) ⟨SecA.normalizer_T_le h331 hyp hm.2, hmN⟩ _)
  obtain ⟨t, ht, htV, he⟩ := mem_autOn_iff.mp ((hmemQ q hqN).mp hq)
  rw [he]
  exact conjV_mem_autOn (L := Subgroup.normalizer (L : Set G) ⊓ N₁) ⟨hyp.normal ht, htV⟩ _

theorem autOn_normalizer_le (hF : PointFacts) (h112 : ASInputs.AS_A_1_12) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    autOn (Subgroup.normalizer (V₁ : Set G)) V₁ ≤
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G)) V₁ := by
  have hle : V₁ ≤ fsuV T I := IsVi.le_fsuV hV₁
  have hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := IsVi.le_normalizer hV₁
  obtain ⟨hXc, hXr, hTc⟩ := actsOn_point hF h1102 hyp hV₁ hC
  rw [autOn_inf_stabW hle] at hXc hXr
  have hA1 : L ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (L_le_normalizer_fsuV hyp)
  have hXcyc := isCyclic_autOn_of_actsCyclicallyOn hle hA1 inf_le_right hXc
  obtain ⟨hXreg, hXfix⟩ := regular_autOn_of_actsRegularlyOn hle hA1 inf_le_right hXr
  have hTcyc := isCyclic_autOn_of_actsCyclicallyOn hle (T_le_normalizer_fsuV T I) hTV₁ hTc
  have : IsMulCommutative ↥V₁ := isMulCommutative_of_le hle (isElemAbelian_fsuV hyp).1
  have hW : ∀ w : ↥V₁, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV hyp).2 w (hle w.2))
  obtain ⟨v, hv⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (IsVi.ne_bot hyp hV₁ le_rfl)
  have hXodd := odd_card_of_fixes hW hv hXfix
  have hTsyl : QuasithinUnique.IsSylowTwoOf (autOn T V₁)
      (autOn (Subgroup.normalizer (V₁ : Set G)) V₁) :=
    isSylowTwoOf_autOn le_rfl (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTV₁)
  have hTX : autOn T V₁ ≤ Subgroup.normalizer
      (autOn (L ⊓ Subgroup.normalizer (V₁ : Set G)) V₁ : Set (MulAut ↥V₁)) := by
    refine le_normalizer_of_forall fun s hs x hx => ?_
    obtain ⟨t, ht, htV, rfl⟩ := mem_autOn_iff.mp hs
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hx
    rw [conjV_conj]
    exact conjV_mem_autOn (L := L ⊓ Subgroup.normalizer (V₁ : Set G))
      ⟨(Subgroup.mem_normalizer_iff.mp (hyp.normal ht) l).mp hl.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htV hlV) (inv_mem htV)⟩ _
  have hcore := le_sup_normalizer_of_regular h112 hW (A4.autOn_mono inf_le_right) hXcyc hXodd hXreg
    hTsyl hTcyc hTX
  exact hcore.trans (sup_le (A4.autOn_mono (inf_le_inf_right _ Subgroup.le_normalizer))
    (autOn_inf_normalizer_le h331 hyp hTV₁))

theorem normalizer_eq_mul (hF : PointFacts) (h112 : ASInputs.AS_A_1_12) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    (Subgroup.normalizer (V₁ : Set G) : Set G) =
      (Subgroup.centralizer (V₁ : Set G) : Set G) *
        ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
          Set G) := by
  have hY := autOn_normalizer_le hF h112 h331 h1102 hyp hV₁ hC
  ext y
  constructor
  · intro hy
    obtain ⟨m, hm, hmV, he⟩ := mem_autOn_iff.mp (hY (conjV_mem_autOn hy hy))
    have hc : y * m⁻¹ ∈ Subgroup.centralizer (V₁ : Set G) := by
      rw [← conjV_eq_one_iff (Subgroup.mul_mem _ hy (inv_mem hmV)), conjV_mul V₁ hy (inv_mem hmV),
        conjV_inv V₁ hmV, he, mul_inv_cancel]
    exact ⟨y * m⁻¹, hc, m, hm, by group⟩
  · rintro ⟨c, hc, m, hm, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hm.2

end CFSG.Quasithin.Vol2.Ch11.SecB
