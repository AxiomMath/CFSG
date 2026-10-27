module

public import CFSG.Milestones.ASVolI.F4K.Iface
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F4K.Base
public import CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section Label

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}

theorem burnsideF4k_asm_label {m : ℕ} (hm : 2 ≤ m) (hU : UniqueGeod c.graph m) {S : Set c.Γ}
    (hS : c.IsApartment m S) {x l : c.Γ} (hx : x ∈ S) (hl : l ∈ S) (hxl : c.graph.Adj x l) :
    ∃ (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))), (∀ i, z i ≠ z (i + 2)) ∧
      (∀ i, z (i + 2 * m) = z i) ∧ S = Set.range z ∧ z 0 = x ∧ z 1 = l := by
  have hΓ := connected_graph c
  have hc' : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  obtain ⟨⟨b, hbS, hbd⟩, -⟩ := GPath.exists_opposite_of_polygon hΓ hc' hU hm hS hx
  obtain ⟨p, q, hp, hq, hp0, hq0, hpm, hqm, hpq, hSeq⟩ :=
    GPath.exists_arcs_of_polygon hΓ hm hS hx hbS hbd
  have h0 : p 0 = q 0 := hp0.trans hq0.symm
  have hmm : p m = q m := hpm.trans hqm.symm
  obtain ⟨h1, h2⟩ := GPath.geod_first_last_ne hΓ hU (by omega) hp hq h0 hmm hpq
  have hlr : l = p 1 ∨ l = q 1 :=
    GPath.cycSeq_adj_start hΓ hc' hU hm hp hq h0 hmm hpq (w := l) (by rw [← hSeq]; exact hl)
      (by rw [hp0]; exact hxl)
  rcases hlr with hlp | hlq
  · refine ⟨GPath.cycSeq p q, GPath.cycSeq_adj p q (by omega) h0 hmm,
      GPath.cycSeq_nb p q hm (GPath.noBack_of_dist_eq hΓ p hp) (GPath.noBack_of_dist_eq hΓ q hq)
        h0 hmm h1 h2, GPath.cycSeq_per p q, hSeq, ?_, ?_⟩
    · rw [GPath.cycSeq_of_le p q (by omega) (Nat.zero_le m)]; exact hp0
    · rw [GPath.cycSeq_of_le p q (by omega) (by omega)]; exact hlp.symm
  · refine ⟨GPath.cycSeq q p, GPath.cycSeq_adj q p (by omega) h0.symm hmm.symm,
      GPath.cycSeq_nb q p hm (GPath.noBack_of_dist_eq hΓ q hq) (GPath.noBack_of_dist_eq hΓ p hp)
        h0.symm hmm.symm (Ne.symm h1) (Ne.symm h2), GPath.cycSeq_per q p, ?_, ?_, ?_⟩
    · rw [hSeq]; exact GPath.range_cycSeq_comm (by omega) h0 hmm
    · rw [GPath.cycSeq_of_le q p (by omega) (Nat.zero_le m)]; exact hq0
    · rw [GPath.cycSeq_of_le q p (by omega) (by omega)]; exact hlq.symm

end Label

section Orbit

@[expose, reducible] def burnsideF4k_asm_pathAction {V : Type} (Γ : SimpleGraph V) (H : Type)
    [Group H] [MulAction H V] [GraphAction H Γ] (n : ℕ) : MulAction H (GPath Γ n) where
  one_smul := GPath.one_smul'
  mul_smul := GPath.mul_smul'

theorem burnsideF4k_asm_stabilizer_eq {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H]
    [MulAction H V] [GraphAction H Γ] {n : ℕ} (q : GPath Γ n) :
    @MulAction.stabilizer H (GPath Γ n) _ (burnsideF4k_asm_pathAction Γ H n) q = q.stabPath := by
  letI := burnsideF4k_asm_pathAction Γ H n
  ext g
  rw [MulAction.mem_stabilizer_iff, GPath.mem_stabPath_iff]
  exact GPath.smul_eq_iff

theorem burnsideF4k_asm_card_trans {G X : Type} [Group G] [MulAction G X] (H : Subgroup G)
    (Λ : Set X) (hinv : ∀ h ∈ H, ∀ r ∈ Λ, h • r ∈ Λ)
    (htr : ∀ r₁ ∈ Λ, ∀ r₂ ∈ Λ, ∃ h ∈ H, h • r₁ = r₂) {r : X} (hr : r ∈ Λ) :
    Nat.card H = Nat.card ↥Λ * Nat.card ↥(MulAction.stabilizer G r ⊓ H) := by
  have horb : MulAction.orbit (↥H) r = Λ := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact hinv h.1 h.2 r hr
    · intro hy
      obtain ⟨h, hh, hhr⟩ := htr r hr y hy
      exact ⟨⟨h, hh⟩, hhr⟩
  have hstab : MulAction.stabilizer (↥H) r = (MulAction.stabilizer G r).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl
  have h1 := MulAction.index_stabilizer (G := ↥H) (x := r)
  rw [horb, hstab] at h1
  have h2 := Subgroup.relIndex_mul_card (H := MulAction.stabilizer G r) (K := H)
  rw [← h2, Subgroup.relIndex, h1, Nat.card_coe_set_eq]

end Orbit

section Opposite

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y} {m : ℕ}

theorem burnsideF4k_asm_card_geods (F : c.Facts46 m) (hs : c.IsSmall m) {a b : c.Γ}
    (hab : c.graph.dist a b = m) :
    Nat.card ↥(c.geods m a b) = Nat.card ↥(CosetGeom.nbrs a) :=
  Nat.card_congr (burnsideF4b_allBij F hs hab).equiv

theorem burnsideF4k_asm_apt_trans (F : c.Facts46 m) {a b : c.Γ} (hab : c.graph.dist a b = m)
    (h2 : ∀ q₁ ∈ c.geods m a b, ∀ q₂ ∈ c.geods m a b, q₁ ≠ q₂ →
      ∀ r₁ ∈ c.geods m a b, ∀ r₂ ∈ c.geods m a b, r₁ ≠ r₂ →
        ∃ g ∈ stv c a ⊓ stv c b, g • q₁ = r₁ ∧ g • q₂ = r₂)
    {A A' : Set c.Γ} (hA : c.IsApartment m A) (haA : a ∈ A) (hbA : b ∈ A)
    (hA' : c.IsApartment m A') (haA' : a ∈ A') (hbA' : b ∈ A') :
    ∃ g ∈ stv c a ⊓ stv c b, (fun w => g • w) '' A = A' := by
  have hm := F.hm
  obtain ⟨p₁, q₁, hp₁, hq₁, hpq₁, hAeq⟩ := (F.lemma_F414_1 hab A).mp ⟨hA, haA, hbA⟩
  obtain ⟨p₂, q₂, hp₂, hq₂, hpq₂, hA'eq⟩ := (F.lemma_F414_1 hab A').mp ⟨hA', haA', hbA'⟩
  obtain ⟨g, hg, e1, e2⟩ := h2 p₁ hp₁ q₁ hq₁ hpq₁ p₂ hp₂ q₂ hq₂ hpq₂
  refine ⟨g, hg, ?_⟩
  rw [hAeq, hA'eq,
    GPath.range_cycSeq (by omega) (hp₁.1.trans hq₁.1.symm) (hp₁.2.1.trans hq₁.2.1.symm),
    GPath.range_cycSeq (by omega) (hp₂.1.trans hq₂.1.symm) (hp₂.2.1.trans hq₂.2.1.symm),
    Set.image_union, GPath.image_smul_verts, GPath.image_smul_verts, e1, e2]

end Opposite

section Line

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_twoTrans_line (hF : F_4_6) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {a b : β.Γ}
    (ha : CosetGeom.vtype a = true) {A₁ A₂ : GPath β.graph κ.m} (h1 : A₁ ∈ β.geods κ.m a b)
    (h2 : A₂ ∈ β.geods κ.m a b) (hne : A₁ ≠ A₂) :
    ∀ q₁ ∈ β.geods κ.m a b, ∀ q₂ ∈ β.geods κ.m a b, q₁ ≠ q₂ →
      ∀ r₁ ∈ β.geods κ.m a b, ∀ r₂ ∈ β.geods κ.m a b, r₁ ≠ r₂ →
        ∃ g ∈ stv β a ⊓ stv β b, g • q₁ = r₁ ∧ g • q₂ = r₂ := by
  have h58 := (hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).2.2.2.2
  have hA₁ : A₁ ∈ GPath.nbPaths β.graph a κ.m :=
    ⟨h1.1, GPath.noBack_of_dist_eq (connected_graph β) A₁ h1.2.2⟩
  have hcase := (h58 a A₁ hA₁).2.2.2
  rw [h1.2.1] at hcase
  rcases hcase with huniq | ⟨-, htr, -⟩ | ⟨-, hv, -⟩ | ⟨-, hv, -⟩
  · exact absurd (huniq A₂ h2.1 h2.2.1 h2.2.2) (Ne.symm hne)
  · exact htr
  · rw [ha] at hv; exact absurd hv (by decide)
  · rw [ha] at hv; exact absurd hv (by decide)

end Line

section Orders

theorem burnsideF4k_asm_card_stab_geods {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} {m : ℕ} {a : c.Γ} {q : GPath c.graph m} (hq : q ∈ c.geods m a (q m))
    (htr : ∀ q₁ ∈ c.geods m a (q m), ∀ q₂ ∈ c.geods m a (q m),
      ∃ g ∈ stv c a ⊓ stv c (q m), g • q₁ = q₂) :
    Nat.card ↥(stv c a ⊓ stv c (q m)) =
      Nat.card ↥(c.geods m a (q m)) * Nat.card ↥(q.stabPath : Subgroup c.G0) := by
  letI := burnsideF4k_asm_pathAction c.graph c.G0 m
  have h := burnsideF4k_asm_card_trans (stv c a ⊓ stv c (q m)) (c.geods m a (q m))
    (fun h hh r hr => burnsideF4k_geods_smul hh hr) htr hq
  rw [burnsideF4k_asm_stabilizer_eq] at h
  have hle : (q.stabPath : Subgroup c.G0) ≤ stv c a ⊓ stv c (q m) :=
    le_inf (GPath.stabPath_le_stabilizer q hq.1) (GPath.stabPath_le_stabilizer
      (q.rev) (by rw [GPath.rev_apply _ (Nat.zero_le m), Nat.sub_zero]) |>.trans' (by
        rw [GPath.stabPath_rev]))
  rw [inf_eq_left.mpr hle] at h
  exact h

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_card_stabPath_eq (hF : F_4_6) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hκ : κ = .Tits ∨ κ = .G2d) {Y Y' : Type} [Group Y] [Group Y'] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (β' : Cpl M₁ M₂ Y') (hβ' : β'.IsFaithful)
    {q : GPath β.graph κ.m} (hq : q ∈ GPath.nbPaths β.graph β.xv κ.m)
    {q' : GPath β'.graph κ.m} (hq' : q' ∈ GPath.nbPaths β'.graph β'.xv κ.m) :
    Nat.card ↥(q.stabPath : Subgroup β.G0) = Nat.card ↥(q'.stabPath : Subgroup β'.G0) := by
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  have h467 := (hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).2.2.2.1
  have h467' := (hF κ p f E Gp M₁ M₂ hyp Y' β' hβ' (incl M₁ M₂) rfl).2.2.2.1
  obtain ⟨j, hj⟩ : ∃ j, κ.m = 2 * j + 2 := by
    rcases hκ with rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
  have hm0 : 0 < κ.m := by omega
  have hv : CosetGeom.vtype β.xv = false := rfl
  have hv' : CosetGeom.vtype β'.xv = false := rfl
  have e1 := ((h467 κ.m le_rfl β.xv q hq).1 hm0 (by rw [hv]; simp)).2 j hj
  have e2 := ((h467' κ.m le_rfl β'.xv q' hq').1 hm0 (by rw [hv']; simp)).2 j hj
  rw [hv] at e1
  rw [hv'] at e2
  have c1 := Subgroup.relIndex_mul_card (H := (q.stabPath : Subgroup β.G0)) (K := stv β β.xv)
  rw [inf_eq_left.mpr (GPath.stabPath_le_stabilizer q hq.1), e1, card_stv_xv β hβ] at c1
  have c2 := Subgroup.relIndex_mul_card (H := (q'.stabPath : Subgroup β'.G0)) (K := stv β' β'.xv)
  rw [inf_eq_left.mpr (GPath.stabPath_le_stabilizer q' hq'.1), e2, card_stv_xv β' hβ'] at c2
  have hpos : 0 < Nat.card (RankTwoAmalgam.ofSubgroups M₁ M₂).G1 := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero fun h0 => ?_) (c1.trans c2.symm)
  rw [h0, zero_mul] at c1
  omega

end Orders

section NotII

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_iota_xb (hF : F_4_6) (h5 : F_4_5) (hAll : burnsideF4b_Facts46All)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .Tits ∨ κ = .G2d)
    {q : GPath (incl M₁ M₂).graph κ.m} (hq : q ∈ GPath.nbPaths (incl M₁ M₂).graph (incl M₁ M₂).xv κ.m) :
    (Nat.card ↥(stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (q κ.m)) = 10 ∨
      Nat.card ↥(stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (q κ.m)) = 3) ∧
    (∀ q₁ ∈ (incl M₁ M₂).geods κ.m (incl M₁ M₂).xv (q κ.m),
      ∀ q₂ ∈ (incl M₁ M₂).geods κ.m (incl M₁ M₂).xv (q κ.m),
        ∃ g ∈ stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (q κ.m), g • q₁ = q₂) := by
  have hGp : Gp = ⊤ := hyp.canonical (hκ.elim Or.inr Or.inl)
  have Fι := hAll κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂)
  have hsι : (incl M₁ M₂).IsSmall κ.m := burnsideF4b_IotaSmall_of hAll h5 κ p f E Gp M₁ M₂ hyp
  have hdist : (incl M₁ M₂).graph.dist (incl M₁ M₂).xv (q κ.m) = κ.m :=
    Fι.dist_m (incl M₁ M₂).xv q hq
  refine ⟨?_, ?_⟩
  · have h9 := (h5 κ p f E Gp M₁ M₂ hyp (incl M₁ M₂) rfl).2.2.2.2.2.2.2.2 ⟨hGp, hκ⟩
      (incl M₁ M₂).xv (q κ.m) hdist
    rcases h9.2 rfl with h | h
    · obtain ⟨e⟩ := h
      left
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    · obtain ⟨e⟩ := h
      right
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · have h58 := (hF κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂) (incl M₁ M₂) rfl).2.2.2.2
    rcases (h58 (incl M₁ M₂).xv q hq).2.2.2 with huniq | ⟨-, htr2, -⟩ | ⟨-, -, -, htr, -⟩ |
        ⟨-, -, -, htr, -⟩
    · exfalso
      obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := burnsideF4b_lemma_F412 Fι hsι (incl M₁ M₂).xv (q κ.m) hdist
      exact hne ((huniq t₁ ht₁.1 ht₁.2.1 ht₁.2.2).trans (huniq t₂ ht₂.1 ht₂.2.1 ht₂.2.2).symm)
    · intro q₁ hq₁ q₂ hq₂
      by_cases h12 : q₁ = q₂
      · exact ⟨1, Subgroup.one_mem _, by rw [h12]; exact GPath.one_smul' q₂⟩
      · obtain ⟨g, hg, e1, -⟩ := htr2 q₁ hq₁ q₂ hq₂ h12 q₂ hq₂ q₁ hq₁ (Ne.symm h12)
        exact ⟨g, hg, e1⟩
    · exact htr
    · exact htr

theorem burnsideF4k_asm_not_ii (hT : burnsideF4k_GrpTwoTrans) (hF : F_4_6) (h5 : F_4_5)
    (hcompat : NativeChartCompatibilityGoal) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hκ : κ = .Tits ∨ κ = .G2d) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall κ.m) {q : GPath β.graph κ.m} (hq : q ∈ GPath.nbPaths β.graph β.xv κ.m)
    (h2 : ∀ q₁ ∈ β.geods κ.m β.xv (q κ.m), ∀ q₂ ∈ β.geods κ.m β.xv (q κ.m), q₁ ≠ q₂ →
      ∀ r₁ ∈ β.geods κ.m β.xv (q κ.m), ∀ r₂ ∈ β.geods κ.m β.xv (q κ.m), r₁ ≠ r₂ →
        ∃ g ∈ stv β β.xv ⊓ stv β (q κ.m), g • q₁ = r₁ ∧ g • q₂ = r₂) : False := by
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have hAll : burnsideF4b_Facts46All :=
    burnsideF4b_Facts46All_of_F46 hF (burnsideF4b_parabolics_of_compat hcompat)
  have F := hAll κ p f E Gp M₁ M₂ hyp Y β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  have Fι := hAll κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂)
  have hsι : (incl M₁ M₂).IsSmall κ.m := burnsideF4b_IotaSmall_of hAll h5 κ p f E Gp M₁ M₂ hyp
  have hm := F.hm
  have hqg : q ∈ β.geods κ.m β.xv (q κ.m) := F.mem_geods hq
  have hdist : β.graph.dist β.xv (q κ.m) = κ.m := F.dist_m β.xv q hq
  have hn : Nat.card ↥(β.geods κ.m β.xv (q κ.m)) = (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range.index := by
    rw [burnsideF4k_asm_card_geods F hs hdist, nbrs_xv_card (c := β) hβ]
  have hn3 : 3 ≤ (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range.index := by
    have := F.thick1
    unfold RankTwoAmalgam.qOne at this
    omega
  have htr : ∀ q₁ ∈ β.geods κ.m β.xv (q κ.m), ∀ q₂ ∈ β.geods κ.m β.xv (q κ.m),
      ∃ g ∈ stv β β.xv ⊓ stv β (q κ.m), g • q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂
    by_cases h12 : q₁ = q₂
    · exact ⟨1, Subgroup.one_mem _, by rw [h12]; exact GPath.one_smul' q₂⟩
    · obtain ⟨g, hg, e1, -⟩ := h2 q₁ hq₁ q₂ hq₂ h12 q₂ hq₂ q₁ hq₁ (Ne.symm h12)
      exact ⟨g, hg, e1⟩
  have hcardH := burnsideF4k_asm_card_stab_geods hqg htr
  obtain ⟨Q, hQ⟩ := GPath.exists_nbPaths (burnsideF4b_hval Fι) (incl M₁ M₂).xv κ.m
  have hQg : Q ∈ (incl M₁ M₂).geods κ.m (incl M₁ M₂).xv (Q κ.m) := Fι.mem_geods hQ
  have hdistι : (incl M₁ M₂).graph.dist (incl M₁ M₂).xv (Q κ.m) = κ.m :=
    Fι.dist_m (incl M₁ M₂).xv Q hQ
  obtain ⟨hcardι, htrι⟩ := burnsideF4k_asm_iota_xb hF h5 hAll hyp hκ hQ
  have hcardHι := burnsideF4k_asm_card_stab_geods hQg htrι
  have hnι : Nat.card ↥((incl M₁ M₂).geods κ.m (incl M₁ M₂).xv (Q κ.m)) =
      (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range.index := by
    rw [burnsideF4k_asm_card_geods Fι hsι hdistι, nbrs_xv_card (c := incl M₁ M₂) (incl_faithful M₁ M₂)]
  have hstab := burnsideF4k_asm_card_stabPath_eq hF hyp hκ β hβ (incl M₁ M₂) (incl_faithful M₁ M₂)
    hq hQ
  have hH : Nat.card ↥(stv β β.xv ⊓ stv β (q κ.m)) = 10 ∨
      Nat.card ↥(stv β β.xv ⊓ stv β (q κ.m)) = 3 := by
    rw [hcardH, hn, hstab, ← hnι, ← hcardHι]
    exact hcardι
  letI := burnsideF4k_asm_pathAction β.graph β.G0 κ.m
  haveI : Finite ↥(β.geods κ.m β.xv (q κ.m)) := Nat.finite_of_card_ne_zero (by rw [hn]; omega)
  have hdvd := hT (stv β β.xv ⊓ stv β (q κ.m)) (β.geods κ.m β.xv (q κ.m)) inferInstance
    (Set.toFinite _) (by rw [hn]; omega) (fun h hh r hr => burnsideF4k_geods_smul hh hr) h2
  rw [hn] at hdvd
  set n := (RankTwoAmalgam.ofSubgroups M₁ M₂).α1.range.index with hndef
  have hle : n * (n - 1) ≤ 10 := by
    rcases hH with h | h <;> rw [h] at hdvd <;> exact Nat.le_of_dvd (by norm_num) hdvd |>.trans
      (by norm_num)
  have hn' : n = 3 := by
    by_contra hne
    have h4 : 4 ≤ n := by omega
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul h4 (by omega)
    omega
  rw [hn'] at hdvd
  rcases hH with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

end NotII

section Point

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_point_cases (hT : burnsideF4k_GrpTwoTrans) (hF : F_4_6) (h5 : F_4_5)
    (hcompat : NativeChartCompatibilityGoal) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hκ : κ = .Tits ∨ κ = .G2d) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall κ.m) {q : GPath β.graph κ.m} (hq : q ∈ GPath.nbPaths β.graph β.xv κ.m) :
    (κ = .Tits ∧ Nonempty (↥(stv β β.xv ⊓ stv β (q κ.m)) ≃* DihedralGroup 5) ∧
      (∀ q₁ ∈ β.geods κ.m β.xv (q κ.m), ∀ q₂ ∈ β.geods κ.m β.xv (q κ.m),
        ∃ g ∈ stv β β.xv ⊓ stv β (q κ.m), g • q₁ = q₂) ∧
      Nat.card ↥(β.geods κ.m β.xv (q κ.m)) = 5) ∨
    (κ = .G2d ∧ Nonempty (↥(stv β β.xv ⊓ stv β (q κ.m)) ≃* Multiplicative (ZMod 3)) ∧
      (∀ q₁ ∈ β.geods κ.m β.xv (q κ.m), ∀ q₂ ∈ β.geods κ.m β.xv (q κ.m),
        ∃ g ∈ stv β β.xv ⊓ stv β (q κ.m), g • q₁ = q₂) ∧
      Nat.card ↥(β.geods κ.m β.xv (q κ.m)) = 3) := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  have h58 := (hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).2.2.2.2
  have hdist : β.graph.dist β.xv (q κ.m) = κ.m := F.dist_m β.xv q hq
  rcases (h58 β.xv q hq).2.2.2 with huniq | ⟨-, htr2, -⟩ | ⟨⟨-, hκT⟩, -, hD, htr, hc, -⟩ |
      ⟨⟨-, hκG⟩, -, hZ, htr, hc, -⟩
  · exfalso
    obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := burnsideF4b_lemma_F412 F hs β.xv (q κ.m) hdist
    exact hne ((huniq t₁ ht₁.1 ht₁.2.1 ht₁.2.2).trans (huniq t₂ ht₂.1 ht₂.2.1 ht₂.2.2).symm)
  · exact (burnsideF4k_asm_not_ii hT hF h5 hcompat hyp hκ β hβ hs hq htr2).elim
  · exact Or.inl ⟨hκT, hD, htr, hc⟩
  · exact Or.inr ⟨hκG, hZ, htr, hc⟩

theorem burnsideF4k_asm_swap_x (hD : burnsideF4k_GrpD10) (hF : F_4_6)
    (hcompat : NativeChartCompatibilityGoal) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hnG : ¬ (Gp = ⊤ ∧ κ = .G2d)) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    {b : β.Γ} {A₁ A₂ : GPath β.graph κ.m} (h1 : A₁ ∈ β.geods κ.m β.xv b)
    (h2 : A₂ ∈ β.geods κ.m β.xv b) (hne : A₁ ≠ A₂) :
    ∃ g ∈ stv β β.xv ⊓ stv β b, g • A₁ = A₂ ∧ g • A₂ = A₁ := by
  have h58 := (hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).2.2.2.2
  have hA₁ : A₁ ∈ GPath.nbPaths β.graph β.xv κ.m :=
    ⟨h1.1, GPath.noBack_of_dist_eq (connected_graph β) A₁ h1.2.2⟩
  have hcase := (h58 β.xv A₁ hA₁).2.2.2
  rw [h1.2.1] at hcase
  rcases hcase with huniq | ⟨-, htr2, -⟩ | ⟨-, -, ⟨e⟩, htr, hc, -⟩ | ⟨hG, -⟩
  · exact absurd (huniq A₂ h2.1 h2.2.1 h2.2.2) (Ne.symm hne)
  · exact htr2 A₁ h1 A₂ h2 hne A₂ h2 A₁ h1 (Ne.symm hne)
  · letI := burnsideF4k_asm_pathAction β.graph β.G0 κ.m
    exact (hD (stv β β.xv ⊓ stv β b) ⟨e⟩ (β.geods κ.m β.xv b)
      (fun h hh r hr => burnsideF4k_geods_smul hh hr) htr hc).1 A₁ h1 A₂ h2 hne
  · exact absurd hG hnG

theorem burnsideF4k_asm_tits_two_fix (hD : burnsideF4k_GrpD10) (hT : burnsideF4k_GrpTwoTrans)
    (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .Tits) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) {b : β.Γ} {A₁ A₂ : GPath β.graph κ.m}
    (h1 : A₁ ∈ β.geods κ.m β.xv b) (h2 : A₂ ∈ β.geods κ.m β.xv b) (hne : A₁ ≠ A₂)
    {g : β.G0} (hg : g ∈ stv β β.xv ⊓ stv β b) (hg1 : g • A₁ = A₁) (hg2 : g • A₂ = A₂) :
    g = 1 := by
  have hA₁ : A₁ ∈ GPath.nbPaths β.graph β.xv κ.m :=
    ⟨h1.1, GPath.noBack_of_dist_eq (connected_graph β) A₁ h1.2.2⟩
  have hb : A₁ κ.m = b := h1.2.1
  rcases burnsideF4k_asm_point_cases hT hF h5 hcompat hyp (Or.inl hκ) β hβ hs hA₁ with
    ⟨-, ⟨e⟩, htr, hc⟩ | ⟨hκG, -⟩
  · rw [hb] at e htr hc
    letI := burnsideF4k_asm_pathAction β.graph β.G0 κ.m
    exact (hD (stv β β.xv ⊓ stv β b) ⟨e⟩ (β.geods κ.m β.xv b)
      (fun h hh r hr => burnsideF4k_geods_smul hh hr) htr hc).2 A₁ h1 A₂ h2 hne g hg hg1 hg2
  · rw [hκ] at hκG
    exact absurd hκG (by decide)

theorem burnsideF4k_asm_g2d_x (hZ : burnsideF4k_GrpZ3) (hT : burnsideF4k_GrpTwoTrans)
    (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) {b : β.Γ} {A₁ : GPath β.graph κ.m}
    (h1 : A₁ ∈ β.geods κ.m β.xv b) :
    (∀ r ∈ β.geods κ.m β.xv b, ∀ g ∈ stv β β.xv ⊓ stv β b, g • r = r → g = 1) ∧
    (∀ r₁ ∈ β.geods κ.m β.xv b, ∀ r₂ ∈ β.geods κ.m β.xv b, r₁ ≠ r₂ →
      ∀ g ∈ stv β β.xv ⊓ stv β b, g • r₁ = r₂ → g • r₂ = r₁ → False) := by
  have hA₁ : A₁ ∈ GPath.nbPaths β.graph β.xv κ.m :=
    ⟨h1.1, GPath.noBack_of_dist_eq (connected_graph β) A₁ h1.2.2⟩
  have hb : A₁ κ.m = b := h1.2.1
  rcases burnsideF4k_asm_point_cases hT hF h5 hcompat hyp (Or.inr hκ) β hβ hs hA₁ with
    ⟨hκT, -⟩ | ⟨-, ⟨e⟩, htr, hc⟩
  · rw [hκ] at hκT
    exact absurd hκT (by decide)
  · rw [hb] at e htr hc
    letI := burnsideF4k_asm_pathAction β.graph β.G0 κ.m
    exact hZ (stv β β.xv ⊓ stv β b) ⟨e⟩ (β.geods κ.m β.xv b)
      (fun h hh r hr => burnsideF4k_geods_smul hh hr) htr hc

end Point

section Reflections

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_arc₁_mem {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))) (m j i : ℕ) :
    GPath.arc₁ z hz m j i ∈ Set.range z :=
  ⟨j + min i m, rfl⟩

theorem burnsideF4k_asm_arc₂_mem {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))) (m j i : ℕ) :
    GPath.arc₂ z hz m j i ∈ Set.range z :=
  ⟨j + 2 * m - min i m, rfl⟩

theorem burnsideF4k_asm_fix_arcs {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    {c : α.Completion Y} (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))) (m j : ℕ)
    {w : c.G0} (hw : ∀ v ∈ Set.range z, w • v = v) :
    w • GPath.arc₁ z hz m j = GPath.arc₁ z hz m j ∧ w • GPath.arc₂ z hz m j = GPath.arc₂ z hz m j :=
  ⟨GPath.ext' fun i _ => hw _ (burnsideF4k_asm_arc₁_mem z hz m j i),
    GPath.ext' fun i _ => hw _ (burnsideF4k_asm_arc₂_mem z hz m j i)⟩

theorem burnsideF4k_asm_refl_data (hA : burnsideF4k_PolyArcs) (hD : burnsideF4k_GrpD10)
    (hF : F_4_6) (hcompat : NativeChartCompatibilityGoal) (hyp : HypF_4_4 κ p f Gp M₁ M₂)
    (hnG : ¬ (Gp = ⊤ ∧ κ = .G2d)) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    {S : Set β.Γ} (hS : β.IsApartment κ.m S) (hx : β.xv ∈ S) (hl : β.lv ∈ S) :
    ∃ (z : ℕ → β.Γ) (hz : ∀ i, β.graph.Adj (z i) (z (i + 1))), (∀ i, z i ≠ z (i + 2)) ∧
      (∀ i, z (i + 2 * κ.m) = z i) ∧ S = Set.range z ∧ z 0 = β.xv ∧ z 1 = β.lv ∧
      ∃ sx sl : β.G0,
        sx • GPath.arc₁ z hz κ.m 0 = GPath.arc₂ z hz κ.m 0 ∧
        sx • GPath.arc₂ z hz κ.m 0 = GPath.arc₁ z hz κ.m 0 ∧
        sl • GPath.arc₁ z hz κ.m 1 = GPath.arc₂ z hz κ.m 1 ∧
        sl • GPath.arc₂ z hz κ.m 1 = GPath.arc₁ z hz κ.m 1 := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  have hm := F.hm
  have hU := F.uniqueGeod
  obtain ⟨z, hz, hnb, hper, hSz, hz0, hz1⟩ :=
    burnsideF4k_asm_label hm hU hS hx hl CosetGeom.adj_γ₀_γ₁
  obtain ⟨a1, a2, a3, -⟩ := hA β κ.m hm hU z hz hnb hper 0
  rw [hz0] at a1 a2
  obtain ⟨sx, -, e1, e2⟩ := burnsideF4k_asm_swap_x hD hF hcompat hyp hnG β hβ a1 a2 a3
  obtain ⟨b1, b2, b3, -⟩ := hA β κ.m hm hU z hz hnb hper 1
  have hv : CosetGeom.vtype (z 1) = true := by rw [hz1]; rfl
  obtain ⟨sl, -, f1, f2⟩ := burnsideF4k_asm_twoTrans_line hF hyp β hβ hv b1 b2 b3 _ b1 _ b2 b3
    _ b2 _ b1 (Ne.symm b3)
  exact ⟨z, hz, hnb, hper, hSz, hz0, hz1, sx, sl, e1, e2, f1, f2⟩

theorem burnsideF4k_asm_tits_K (hA : burnsideF4k_PolyArcs) (hD : burnsideF4k_GrpD10)
    (hT : burnsideF4k_GrpTwoTrans) (hF : F_4_6) (h5 : F_4_5)
    (hcompat : NativeChartCompatibilityGoal) (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .Tits)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m)
    (z : ℕ → β.Γ) (hz : ∀ i, β.graph.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * κ.m) = z i) (hz0 : z 0 = β.xv) (w : β.G0)
    (hw : ∀ v ∈ Set.range z, w • v = v) : w = 1 := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  have hm := F.hm
  have hU := F.uniqueGeod
  obtain ⟨a1, a2, a3, -⟩ := hA β κ.m hm hU z hz hnb hper 0
  rw [hz0] at a1 a2
  obtain ⟨w1, w2⟩ := burnsideF4k_asm_fix_arcs z hz κ.m 0 hw
  have hwx : w • β.xv = β.xv := by rw [← hz0]; exact hw _ ⟨0, rfl⟩
  have hwb : w • z (0 + κ.m) = z (0 + κ.m) := hw _ ⟨_, rfl⟩
  exact burnsideF4k_asm_tits_two_fix hD hT hF h5 hcompat hyp hκ β hβ hs a1 a2 a3
    (Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hwx,
      MulAction.mem_stabilizer_iff.mpr hwb⟩) w1 w2

end Reflections

section Apartments

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y} {m : ℕ}

theorem burnsideF4k_asm_apt_through [Finite Y] (F : c.Facts46 m) (hs : c.IsSmall m) {a b y : c.Γ}
    (hab : c.graph.dist a b = m) (hay : c.graph.Adj a y) :
    ∃ S : Set c.Γ, c.IsApartment m S ∧ a ∈ S ∧ b ∈ S ∧ y ∈ S := by
  have hm := F.hm
  obtain ⟨t, ⟨ht, ht1⟩, -⟩ := F.lemma_F414_2 hs hab hay
  obtain ⟨Q, hQ, hQt⟩ := F.exists_ne_geod hs hab t
  obtain ⟨hS, haS, hbS⟩ := (F.lemma_F414_1 hab (Set.range (GPath.cycSeq t Q))).mpr
    ⟨t, Q, ht, hQ, Ne.symm hQt, rfl⟩
  refine ⟨_, hS, haS, hbS, 1, ?_⟩
  rw [GPath.cycSeq_of_le t Q (by omega) (by omega)]
  exact ht1

theorem burnsideF4k_asm_image_apartment (F : c.Facts46 m) {a a' : c.Γ}
    (haa' : c.graph.dist a a' = m) {S : Set c.Γ} (hS : c.IsApartment m S) (ha : a ∈ S)
    (ha' : a' ∈ S) (g : c.G0) : c.IsApartment m ((fun w => g • w) '' S) := by
  have hm := F.hm
  obtain ⟨P, Q, hP, hQ, hPQ, hSeq⟩ := (F.lemma_F414_1 haa' S).mp ⟨hS, ha, ha'⟩
  have hd : c.graph.dist (g • a) (g • a') = m := by
    rw [GPath.dist_smul (connected_graph c)]; exact haa'
  have hgP := smul_mem_geods g hP
  have hgQ := smul_mem_geods g hQ
  have hne : g • P ≠ g • Q := fun h => hPQ (by
    have := congrArg (fun r : GPath c.graph m => g⁻¹ • r) h
    simpa only [GPath.inv_smul_smul'] using this)
  have himg : (fun w => g • w) '' S = Set.range (GPath.cycSeq (g • P) (g • Q)) := by
    rw [hSeq, GPath.range_cycSeq (by omega) (hP.1.trans hQ.1.symm) (hP.2.1.trans hQ.2.1.symm),
      GPath.range_cycSeq (by omega) (hgP.1.trans hgQ.1.symm) (hgP.2.1.trans hgQ.2.1.symm),
      Set.image_union, GPath.image_smul_verts, GPath.image_smul_verts]
  rw [himg]
  exact ((F.lemma_F414_1 hd _).mpr ⟨g • P, g • Q, hgP, hgQ, hne, rfl⟩).1

theorem burnsideF4k_asm_apt_line (F : c.Facts46 m) {S : Set c.Γ} (hS : c.IsApartment m S) :
    ∃ a ∈ S, CosetGeom.vtype a = true := by
  have hm := F.hm
  have hΓ := connected_graph c
  have hc' : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  obtain ⟨φ⟩ := hS
  have h0 : (φ ⟨0, by omega⟩ : ↥S).1 ∈ S := (φ ⟨0, by omega⟩).2
  by_cases h : CosetGeom.vtype (φ ⟨0, by omega⟩ : ↥S).1 = true
  · exact ⟨_, h0, h⟩
  · obtain ⟨w, hwS, hadj⟩ := (GPath.exists_opposite_of_polygon hΓ hc' F.uniqueGeod hm ⟨φ⟩ h0).2
    refine ⟨w, hwS, ?_⟩
    have := hc' _ _ hadj
    revert h this
    cases CosetGeom.vtype (φ ⟨0, by omega⟩ : ↥S).1 <;> cases CosetGeom.vtype w <;> simp

theorem burnsideF4k_asm_image_inv {g : c.G0} {A B : Set c.Γ} (h : (fun w => g • w) '' A = B) :
    (fun w => g⁻¹ • w) '' B = A := by
  rw [← h, Set.image_image]
  simp only [inv_smul_smul, Set.image_id']

end Apartments

section Three

open scoped Pointwise

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_F415_three (hA : burnsideF4k_PolyArcs) (hW : burnsideF4k_PolyW)
    (hO : burnsideF4k_PolyOpp) (hD : burnsideF4k_GrpD10) (hT : burnsideF4k_GrpTwoTrans)
    (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .Tits) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) :
    ∃ S₁ S₂ : Set β.Γ, β.IsApartment κ.m S₁ ∧ β.IsApartment κ.m S₂ ∧
      (∀ S : Set β.Γ, β.IsApartment κ.m S →
        (∃ g : β.G0, (fun w => g • w) '' S₁ = S) ∨ (∃ g : β.G0, (fun w => g • w) '' S₂ = S)) ∧
      (¬ ∃ g : β.G0, (fun w => g • w) '' S₁ = S₂) ∧
      Nat.card ↥{S : Set β.Γ | ∃ g : β.G0, (fun w => g • w) '' S₁ = S} =
        Nat.card ↥{S : Set β.Γ | ∃ g : β.G0, (fun w => g • w) '' S₂ = S} := by
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  have hm := F.hm
  have hU := F.uniqueGeod
  have hΓ := connected_graph β
  have hc' : ∀ a b : β.Γ, β.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun a b h => CosetGeom.vtype_ne_of_adj h
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr hκ)
  have hnG : ¬ (Gp = ⊤ ∧ κ = .G2d) := fun h => by rw [hκ] at h; exact absurd h.2 (by decide)
  have hvl : CosetGeom.vtype β.lv = true := rfl
  have h2b := ((hF κ p f E Gp M₁ M₂ hyp Y β hβ (incl M₁ M₂) rfl).1 β.lv).2 ⟨hGp, Or.inr hκ⟩
  obtain ⟨-, ⟨q₁, hq₁, q₂, hq₂, hcov, hdisj, -⟩, hlast⟩ := h2b.2 hvl
  have hd₁ : β.graph.dist β.lv (q₁ κ.m) = κ.m := F.dist_m β.lv q₁ hq₁
  have hd₂ : β.graph.dist β.lv (q₂ κ.m) = κ.m := F.dist_m β.lv q₂ hq₂
  have K1 : ∀ g ∈ stv β β.lv, g • q₁ κ.m ≠ q₂ κ.m := by
    intro g hg hgb
    have hg' : g • β.lv = β.lv := MulAction.mem_stabilizer_iff.mp hg
    have hgq : g • q₁ ∈ GPath.nbPaths β.graph β.lv κ.m :=
      ⟨by rw [GPath.smul_apply, hq₁.1, hg'], GPath.smul_noBack hq₁.2⟩
    obtain ⟨h, hh, hhq⟩ := hlast (g • q₁) hgq q₂ hq₂ (by rw [GPath.smul_apply]; exact hgb)
    have hmem : q₂ ∈ pathOrbit (stv β β.lv) q₁ :=
      ⟨h * g, (stv β β.lv).mul_mem (Subgroup.mem_inf.mp hh).1 hg, by
        rw [GPath.mul_smul']; exact hhq⟩
    exact Set.disjoint_left.mp hdisj hmem ⟨1, Subgroup.one_mem _, GPath.one_smul' q₂⟩
  have K2 : ∀ b, β.graph.dist β.lv b = κ.m →
      (∃ g ∈ stv β β.lv, g • q₁ κ.m = b) ∨ (∃ g ∈ stv β β.lv, g • q₂ κ.m = b) := by
    intro b hb
    obtain ⟨r, hr, hrb⟩ := Facts46.exists_geod_path (c := β) (m := κ.m) hb
    have hr' : r ∈ pathOrbit (stv β β.lv) q₁ ∪ pathOrbit (stv β β.lv) q₂ := by
      rw [← hcov]; exact hr
    rcases hr' with ⟨g, hg, hgr⟩ | ⟨g, hg, hgr⟩
    · exact Or.inl ⟨g, hg, by rw [← hrb, ← hgr]; rfl⟩
    · exact Or.inr ⟨g, hg, by rw [← hrb, ← hgr]; rfl⟩
  have hlx : β.graph.Adj β.lv β.xv := CosetGeom.adj_γ₀_γ₁.symm
  obtain ⟨S₁, hS₁, hlS₁, hbS₁, hxS₁⟩ := burnsideF4k_asm_apt_through F hs hd₁ hlx
  obtain ⟨S₂, hS₂, hlS₂, hbS₂, hxS₂⟩ := burnsideF4k_asm_apt_through F hs hd₂ hlx
  have hdata : ∀ {S : Set β.Γ}, β.IsApartment κ.m S → β.xv ∈ S → β.lv ∈ S →
      (∃ sx sl : β.G0, IsF415W β κ.m S sx sl) ∧ Nat.card ↥(setStab β S) = 2 * κ.m ∧
      ∃ z : ℕ → β.Γ, S = Set.range z ∧
        ∀ j, β.graph.dist β.lv (z j) = κ.m → z j = z (1 + κ.m) := by
    intro S hS hx hl
    obtain ⟨z, hz, hnb, hper, rfl, hz0, hz1, sx, sl, e1, e2, f1, f2⟩ :=
      burnsideF4k_asm_refl_data hA hD hF hcompat hyp hnG β hβ hS hx hl
    obtain ⟨hWW, hidx⟩ := hW β κ.m hm hU z hz hnb hper hz0 hz1 sx sl e1 e2 f1 f2
    have hK : pointwiseStab β (Set.range z) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact burnsideF4k_asm_tits_K hA hD hT hF h5 hcompat hyp hκ β hβ hs z hz hnb hper hz0 w
        ((burnsideF4k_mem_pointwiseStab β).mp hw)
    rw [hK, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
    refine ⟨⟨sx, sl, hWW⟩, hidx, z, rfl, fun j hj => ?_⟩
    rw [← hz1] at hj
    exact hO β κ.m hm hU z hz hnb hper 1 j hj
  refine ⟨S₁, S₂, hS₁, hS₂, ?_, ?_, ?_⟩
  ·
    intro S hS
    obtain ⟨a, haS, hva⟩ := burnsideF4k_asm_apt_line F hS
    obtain ⟨⟨a', ha'S, haa'⟩, -⟩ := GPath.exists_opposite_of_polygon hΓ hc' hU hm hS haS
    obtain ⟨g₁, hg₁⟩ := exists_smul_of_vtype_eq a β.lv (hva.trans hvl.symm)
    have hd : β.graph.dist β.lv (g₁ • a') = κ.m := by
      rw [← hg₁, GPath.dist_smul hΓ]; exact haa'
    have key : ∀ b : β.Γ, β.graph.dist β.lv b = κ.m → ∀ {S' : Set β.Γ},
        β.IsApartment κ.m S' → β.lv ∈ S' → b ∈ S' → ∀ h : β.G0, h ∈ stv β β.lv →
          h • b = g₁ • a' → ∃ g : β.G0, (fun w => g • w) '' S' = S := by
      intro b hb S' hS' hlS' hbS' h hh hhb
      have hh' : h • β.lv = β.lv := MulAction.mem_stabilizer_iff.mp hh
      have hka : (h⁻¹ * g₁) • a = β.lv := by rw [mul_smul, hg₁, inv_smul_eq_iff, hh']
      have hka' : (h⁻¹ * g₁) • a' = b := by rw [mul_smul, ← hhb, inv_smul_smul]
      have hTk := burnsideF4k_asm_image_apartment F haa' hS haS ha'S (h⁻¹ * g₁)
      obtain ⟨t₁, t₂, ht₁, ht₂, hne⟩ := burnsideF4b_lemma_F412 F hs β.lv b hb
      have h2t := burnsideF4k_asm_twoTrans_line hF hyp β hβ hvl ht₁ ht₂ hne
      obtain ⟨g₂, -, hg₂⟩ := burnsideF4k_asm_apt_trans F hb h2t hTk ⟨a, haS, hka⟩
        ⟨a', ha'S, hka'⟩ hS' hlS' hbS'
      refine ⟨(g₂ * (h⁻¹ * g₁))⁻¹, burnsideF4k_asm_image_inv ?_⟩
      rw [← hg₂, Set.image_image]
      simp only [mul_smul]
    rcases K2 _ hd with ⟨h, hh, hhb⟩ | ⟨h, hh, hhb⟩
    · exact Or.inl (key _ hd₁ hS₁ hlS₁ hbS₁ h hh hhb)
    · exact Or.inr (key _ hd₂ hS₂ hlS₂ hbS₂ h hh hhb)
  ·
    rintro ⟨g, hg⟩
    obtain ⟨⟨sx, sl, hWW⟩, -, z₁, hz₁S, hopp⟩ := hdata hS₁ hxS₁ hlS₁
    have hlS₂' : β.lv ∈ (fun w => g • w) '' S₁ := by rw [hg]; exact hlS₂
    obtain ⟨y, hyS₁, hgy⟩ := hlS₂'
    have hvy : CosetGeom.vtype y = CosetGeom.vtype β.lv := by
      rw [← hgy, CosetGeom.vtype_smul]
    obtain ⟨w, hwW, hwy⟩ := hWW.2.2.2.2.2 y hyS₁ β.lv hlS₁ hvy
    have hWle : Subgroup.closure {sx, sl} ≤ setStab β S₁ := by
      rw [Subgroup.closure_le]
      rintro s (rfl | rfl)
      · exact hWW.2.2.1.2.1
      · exact hWW.2.2.2.1.2.1
    have hwS := hWle hwW
    have hgy' : g • y = β.lv := hgy
    have hkl : (w * g⁻¹) • β.lv = β.lv := by
      rw [mul_smul, show g⁻¹ • β.lv = y by rw [← hgy', inv_smul_smul], hwy]
    have hb₂S₁ : g⁻¹ • q₂ κ.m ∈ S₁ := by
      have h' : q₂ κ.m ∈ (fun w => g • w) '' S₁ := by rw [hg]; exact hbS₂
      obtain ⟨v, hv, hgv⟩ := h'
      rw [← hgv, inv_smul_smul]
      exact hv
    have hkb : (w * g⁻¹) • q₂ κ.m ∈ S₁ := by
      rw [mul_smul]; exact burnsideF4k_setStab_mem β hwS hb₂S₁
    have hdk : β.graph.dist β.lv ((w * g⁻¹) • q₂ κ.m) = κ.m := by
      have e := GPath.dist_smul hΓ (w * g⁻¹) β.lv (q₂ κ.m)
      rw [hkl] at e
      rw [e]
      exact hd₂
    have e1 : (w * g⁻¹) • q₂ κ.m = q₁ κ.m := by
      rw [hz₁S] at hkb hbS₁
      obtain ⟨j, hj⟩ := hkb
      obtain ⟨j₁, hj₁⟩ := hbS₁
      rw [← hj, hopp j (by rw [hj]; exact hdk), ← hopp j₁ (by rw [hj₁]; exact hd₁), hj₁]
    apply K1 (w * g⁻¹)⁻¹ ((stv β β.lv).inv_mem (MulAction.mem_stabilizer_iff.mpr hkl))
    rw [← e1, inv_smul_smul]
  ·
    obtain ⟨-, hc₁, -⟩ := hdata hS₁ hxS₁ hlS₁
    obtain ⟨-, hc₂, -⟩ := hdata hS₂ hxS₂ hlS₂
    have horb : ∀ S' : Set β.Γ,
        {S : Set β.Γ | ∃ g : β.G0, (fun w => g • w) '' S' = S} = MulAction.orbit β.G0 S' := by
      intro S'
      ext S
      simp only [Set.mem_setOf_eq, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, by rw [← hg, Set.image_smul]⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, by rw [← hg, Set.image_smul]⟩
    rw [horb, horb, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← MulAction.index_stabilizer,
      ← MulAction.index_stabilizer]
    have e1 := Subgroup.card_mul_index (setStab β S₁)
    have e2 := Subgroup.card_mul_index (setStab β S₂)
    rw [hc₁] at e1
    rw [hc₂] at e2
    exact Nat.eq_of_mul_eq_mul_left (by omega) (e1.trans e2.symm)

end Three

section Four

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4k_asm_F415_four (hA : burnsideF4k_PolyArcs) (hR : burnsideF4k_PolyRefl)
    (hO : burnsideF4k_PolyOpp) (hN : burnsideF4k_PolyNbr) (hG : burnsideF4k_PolyG2d)
    (hZ : burnsideF4k_GrpZ3) (hT : burnsideF4k_GrpTwoTrans) (hF : F_4_6) (h5 : F_4_5)
    (hcompat : NativeChartCompatibilityGoal) (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .G2d)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) :
    ∀ S : Set β.Γ, β.IsApartment κ.m S → β.xv ∈ S → β.lv ∈ S →
      ∀ c ∈ CosetGeom.nbrs β.xv, c ∈ S → c ≠ β.lv →
        ∃ sl sc : β.G0, sl ∈ stv β β.lv ∧ sc ∈ stv β c ∧ IsReflectionOn β sl S β.lv ∧
          IsReflectionOn β sc S c ∧ setStab β S = Subgroup.closure {sl, sc} ∧
          Nonempty (↥(setStab β S) ≃* Equiv.Perm (Fin 3)) ∧
          Set.ncard {u : β.Γ | u ∈ S ∧ CosetGeom.vtype u = false} = 6 ∧
          (∀ u ∈ S, CosetGeom.vtype u = false → ∀ v ∈ S, CosetGeom.vtype v = false →
            ∃! w : ↥(setStab β S), (w : β.G0) • u = v) ∧
          {u : β.Γ | u ∈ S ∧ CosetGeom.vtype u = true} =
            {u | ∃ w ∈ setStab β S, w • β.lv = u} ∪ {u | ∃ w ∈ setStab β S, w • c = u} ∧
          Disjoint {u : β.Γ | ∃ w ∈ setStab β S, w • β.lv = u}
            {u | ∃ w ∈ setStab β S, w • c = u} ∧
          Set.ncard {u : β.Γ | ∃ w ∈ setStab β S, w • β.lv = u} = 3 ∧
          Set.ncard {u : β.Γ | ∃ w ∈ setStab β S, w • c = u} = 3 := by
  intro S hS hx hl c hc hcS hcl
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  have hm := F.hm
  have hU := F.uniqueGeod
  have hΓ := connected_graph β
  obtain ⟨z, hz, hnb, hper, rfl, hz0, hz1⟩ :=
    burnsideF4k_asm_label hm hU hS hx hl CosetGeom.adj_γ₀_γ₁
  subst hκ
  have hc11 : c = z 11 := by
    rcases hN β _ hm hU z hz hnb hper 0 c hcS (by rw [hz0]; exact hc) with h | h
    · exact absurd (h.trans hz1) hcl
    · exact h
  subst hc11
  obtain ⟨b1, b2, b3, -⟩ := hA β _ hm hU z hz hnb hper 1
  have hv1 : CosetGeom.vtype (z 1) = true := by rw [hz1]; rfl
  obtain ⟨sl, -, f1, f2⟩ := burnsideF4k_asm_twoTrans_line hF hyp β hβ hv1 b1 b2 b3 _ b1 _ b2 b3
    _ b2 _ b1 (Ne.symm b3)
  obtain ⟨c1, c2, c3, -⟩ := hA β _ hm hU z hz hnb hper 11
  have hv11 : CosetGeom.vtype (z 11) = true := by
    have hadj : β.graph.Adj (z 11) (z 0) := by
      have := hz 11
      rwa [show (11 + 1 : ℕ) = 0 + 2 * GLKind.m GLKind.G2d from rfl, hper 0] at this
    have hne := CosetGeom.vtype_ne_of_adj hadj
    rw [hz0] at hne
    revert hne
    cases CosetGeom.vtype (z 11) <;> simp [show CosetGeom.vtype β.xv = false from rfl]
  obtain ⟨sc, -, g1, g2⟩ := burnsideF4k_asm_twoTrans_line hF hyp β hβ hv11 c1 c2 c3 _ c1 _ c2 c3
    _ c2 _ c1 (Ne.symm c3)
  have hfree : ∀ g ∈ setStab β (Set.range z), g • z 0 = z 0 → g = 1 := by
    intro g hgS hg0
    obtain ⟨a1, a2, a3, hSv⟩ := hA β _ hm hU z hz hnb hper 0
    have hab : β.graph.dist (z 0) (z (0 + GLKind.m GLKind.G2d)) = GLKind.m GLKind.G2d := by
      have := a1.2.2
      unfold GPath.IsGeodesic at this
      rwa [a1.1, a1.2.1] at this
    have hgm : g • z (0 + GLKind.m GLKind.G2d) = z (0 + GLKind.m GLKind.G2d) := by
      obtain ⟨j, hj⟩ := burnsideF4k_setStab_mem β hgS (⟨_, rfl⟩ : z (0 + GLKind.m GLKind.G2d) ∈ Set.range z)
      rw [← hj]
      refine hO β _ hm hU z hz hnb hper 0 j ?_
      rw [hj, ← hg0, GPath.dist_smul hΓ]
      exact hab
    have hg' : g ∈ stv β (z 0) ⊓ stv β (z (0 + GLKind.m GLKind.G2d)) :=
      Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hg0, MulAction.mem_stabilizer_iff.mpr hgm⟩
    have hrange : Set.range z = Set.range (GPath.cycSeq (GPath.arc₁ z hz (GLKind.m GLKind.G2d) 0)
        (GPath.arc₂ z hz (GLKind.m GLKind.G2d) 0)) := by
      rw [hSv, GPath.range_cycSeq (by omega) (a1.1.trans a2.1.symm) (a1.2.1.trans a2.2.1.symm)]
    have himg : ∀ r : GPath β.graph (GLKind.m GLKind.G2d),
        r ∈ β.geods (GLKind.m GLKind.G2d) (z 0) (z (0 + GLKind.m GLKind.G2d)) →
        (∀ i, r i ∈ Set.range z) →
        g • r = GPath.arc₁ z hz (GLKind.m GLKind.G2d) 0 ∨ g • r = GPath.arc₂ z hz (GLKind.m GLKind.G2d) 0 := by
      intro r hr hrz
      refine F.eq_of_verts_subset hs hab a1 a2 a3 (burnsideF4k_geods_smul hg' hr) fun i _ => ?_
      rw [← hrange]
      exact burnsideF4k_setStab_mem β hgS (hrz i)
    have a1x : GPath.arc₁ z hz (GLKind.m GLKind.G2d) 0 ∈
        β.geods (GLKind.m GLKind.G2d) β.xv (z (0 + GLKind.m GLKind.G2d)) := by rw [← hz0]; exact a1
    have a2x : GPath.arc₂ z hz (GLKind.m GLKind.G2d) 0 ∈
        β.geods (GLKind.m GLKind.G2d) β.xv (z (0 + GLKind.m GLKind.G2d)) := by rw [← hz0]; exact a2
    have hg'' : g ∈ stv β β.xv ⊓ stv β (z (0 + GLKind.m GLKind.G2d)) := by rw [← hz0]; exact hg'
    obtain ⟨hfr, hsw⟩ := burnsideF4k_asm_g2d_x hZ hT hF h5 hcompat hyp rfl β hβ hs a1x
    rcases himg _ a1 (burnsideF4k_asm_arc₁_mem z hz _ 0) with h | h
    · exact hfr _ a1x g hg'' h
    · exfalso
      rcases himg _ a2 (burnsideF4k_asm_arc₂_mem z hz _ 0) with h' | h'
      · exact hsw _ a1x _ a2x a3 g hg'' h h'
      · apply a3
        have := h.trans h'.symm
        have := congrArg (fun r : GPath β.graph (GLKind.m GLKind.G2d) => g⁻¹ • r) this
        simpa only [GPath.inv_smul_smul'] using this
  have hRl := hR β _ hm hU z hz hnb hper 1 sl f1 f2
  have hRc := hR β _ hm hU z hz hnb hper 11 sc g1 g2
  obtain ⟨hcl', hiso, hpts, hreg, hlines, hdisj, hc1, hc2⟩ :=
    hG β hU z hz hnb hper hz0 hz1 sl sc f1 f2 g1 g2 hfree
  rw [hz1] at hRl
  refine ⟨sl, sc, MulAction.mem_stabilizer_iff.mpr hRl.2.2.1,
    MulAction.mem_stabilizer_iff.mpr hRc.2.2.1, hRl, hRc, hcl', hiso, hpts, hreg, hlines, hdisj,
    hc1, hc2⟩

end Four

theorem burnsideF4k_F415_of (hA : burnsideF4k_PolyArcs) (hR : burnsideF4k_PolyRefl)
    (hW : burnsideF4k_PolyW) (hO : burnsideF4k_PolyOpp) (hN : burnsideF4k_PolyNbr)
    (hG : burnsideF4k_PolyG2d) (hD : burnsideF4k_GrpD10) (hZ : burnsideF4k_GrpZ3)
    (hT : burnsideF4k_GrpTwoTrans) (hF : F_4_6) (h5 : F_4_5)
    (hcompat : NativeChartCompatibilityGoal) : F_4_15 := by
  intro κ p f E _ Gp M₁ M₂ hyp Y _ β hβ hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnT S₁ S₂ h₁ h₂
    exact burnsideF4k_F415_one hF hcompat hyp β hβ hnT h₁ h₂
  · intro hnG S hS hx hl
    have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
    obtain ⟨z, hz, hnb, hper, rfl, hz0, hz1, sx, sl, e1, e2, f1, f2⟩ :=
      burnsideF4k_asm_refl_data hA hD hF hcompat hyp hnG β hβ hS hx hl
    refine ⟨sx, sl, (hW β κ.m F.hm F.uniqueGeod z hz hnb hper hz0 hz1 sx sl e1 e2 f1 f2).1, ?_⟩
    rintro ⟨-, hκT⟩ w - hw
    exact burnsideF4k_asm_tits_K hA hD hT hF h5 hcompat hyp hκT β hβ hs z hz hnb hper hz0 w hw
  · rintro ⟨-, hκT⟩
    exact burnsideF4k_asm_F415_three hA hW hO hD hT hF h5 hcompat hyp hκT β hβ hs
  · rintro ⟨-, hκG⟩
    exact burnsideF4k_asm_F415_four hA hR hO hN hG hZ hT hF h5 hcompat hyp hκG β hβ hs

end CFSG.ASVolI
