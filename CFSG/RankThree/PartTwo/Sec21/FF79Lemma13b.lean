module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bGL
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bCF2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13b

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {b : G} {J B : Subgroup G}

theorem isPGroup_zpowers_of_pow_three {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)

theorem exists_gen_of_card_three {D : Subgroup G} (hD : Nat.card D = 3) :
    ∃ d ∈ D, D = Subgroup.zpowers d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial ↥D := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hD]; norm_num)
  obtain ⟨d, hd⟩ := exists_ne (1 : ↥D)
  have hdo : orderOf d ∣ 3 := hD ▸ orderOf_dvd_natCard d
  have hdo' : orderOf d = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdo with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd
    · exact h
  have hle : Subgroup.zpowers (d : G) ≤ D := Subgroup.zpowers_le.mpr d.2
  refine ⟨d, d.2, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [Nat.card_zpowers, hD, Subgroup.orderOf_coe, hdo']

namespace Data

variable (hD : Data b J B)
include hD

theorem pow_three : b ^ 3 = 1 := by
  have := pow_orderOf_eq_one b
  rwa [hD.ord] at this

variable (c : Coord B) (W : Submodule (ZMod 3) (Fin 3 → ZMod 3))
  (hW : ∀ u, u ∈ W ↔ c.d u ∈ B ⊓ J)
include c hW

theorem not_mem_W : c.e b ∉ W := fun hv => hD.hbJ (by
  have := (hW _).mp hv
  rw [c.d_e b hD.hbB] at this
  exact this.2)

theorem claimA (hstab : ∀ g ∈ c.X, ∀ w ∈ W, act33 g w ∈ W) {n : G} (hn : n ∈ Nor B)
    (hy : n * b * n⁻¹ ∈ B ⊓ J) : False := by
  obtain ⟨g, hg, hgx⟩ := c.exists_mem_X hn
  have h1 : act33 g (c.e b) ∈ W := by
    rw [hgx b hD.hbB, hW, c.d_e _ (conj_mem_of_nor hn hD.hbB)]
    exact hy
  have h2 := hstab g⁻¹ (inv_mem hg) _ h1
  rw [Coord.act33_inv_act33] at h2
  exact hD.not_mem_W c W hW h2

theorem not_conjInto (hstab : ∀ g ∈ c.X, ∀ w ∈ W, act33 g w ∈ W) : ¬ ConjInto b J := by
  rintro ⟨k, hk⟩
  have hk3 : (k * b * k⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hD.pow_three]
    group
  have hp : IsPGroup 3 (Subgroup.zpowers (k * b * k⁻¹)) := isPGroup_zpowers_of_pow_three hk3
  have hle : Subgroup.zpowers (k * b * k⁻¹) ≤ J := Subgroup.zpowers_le.mpr hk
  obtain ⟨j, hjJ, hj⟩ := exists_conj_le_sylowOf hD.hB0syl hle hp
  have hy := hj _ (Subgroup.mem_zpowers _)
  have hyk : (j * k) * b * (j * k)⁻¹ = j * (k * b * k⁻¹) * j⁻¹ := by group
  obtain ⟨n, hn, hnb⟩ := exists_nor_conj hD.hB hD.hab hy.1 hyk
  exact hD.claimA c W hW hstab hn (hnb ▸ hy)

theorem orbit (hstab : ∀ g ∈ c.X, ∀ w ∈ W, act33 g w ∈ W)
    (hmov : ∀ u ∉ W, ∃ g ∈ c.X, act33 g (c.e b) = u ∨ act33 g (c.e b) = -u)
    (D : Subgroup G) (hDB : D ≤ B) (hD3 : Nat.card D = 3) :
    (∃ g ∈ Nor B, conjBy g (Subgroup.zpowers b) = D) ↔ ¬ D ≤ J := by
  constructor
  · rintro ⟨g, hg, rfl⟩ hDJ
    apply hD.claimA c W hW hstab hg
    have : g * b * g⁻¹ ∈ conjBy g (Subgroup.zpowers b) :=
      ⟨b, Subgroup.mem_zpowers b, by simp [MulAut.conj_apply]⟩
    exact ⟨hDB this, hDJ this⟩
  · intro hDJ
    obtain ⟨d, hdD, rfl⟩ := exists_gen_of_card_three hD3
    have hdB : d ∈ B := hDB hdD
    have hdJ : d ∉ J := fun h => hDJ (Subgroup.zpowers_le.mpr h)
    have hu : c.e d ∉ W := by
      rw [hW, c.d_e d hdB]
      exact fun h => hdJ h.2
    obtain ⟨g, hg, hgu⟩ := hmov _ hu
    obtain ⟨n, hn, hgx⟩ := hg
    refine ⟨n, hn, ?_⟩
    have hnb : n * b * n⁻¹ = d ∨ n * b * n⁻¹ = d⁻¹ :=
      hgu.imp ((c.act_iff hgx hn hD.hbB hdB).mp) ((c.act_neg_iff hgx hn hD.hbB hdB).mp)
    show Subgroup.map (MulAut.conj n).toMonoidHom (Subgroup.zpowers b) = Subgroup.zpowers d
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hnb with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]

theorem case2 (hCF : ∀ b₁ b₂ : G, IsFullMonomial B b b₁ b₂ → ControlsFusionIn B)
    {u₁ u₂ : Fin 3 → ZMod 3} (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W)
    (hli : LinearIndependent (ZMod 3) ![c.e b, u₁, u₂])
    (hperm : ∀ g ∈ c.X, ∀ x ∈ ({c.e b, -c.e b, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)),
      act33 g x ∈ ({c.e b, -c.e b, u₁, -u₁, u₂, -u₂} : Set (Fin 3 → ZMod 3)))
    (h1 : ∃ g ∈ c.X, act33 g (c.e b) = -c.e b ∧ act33 g u₁ = u₁ ∧ act33 g u₂ = u₂)
    (h2 : ∃ g ∈ c.X, act33 g (c.e b) = u₁ ∧ act33 g u₁ = c.e b ∧ act33 g u₂ = u₂)
    (h3 : ∃ g ∈ c.X, act33 g (c.e b) = u₁ ∧ act33 g u₁ = u₂ ∧ act33 g u₂ = c.e b) :
    ConjInto b J ∧ ControlsFusionIn B ∧
      ∃ b₁ ∈ B ⊓ J, ∃ b₂ ∈ B ⊓ J, IsFullMonomial B b b₁ b₂ := by
  obtain ⟨b₁, hb₁, rfl⟩ : ∃ b₁ ∈ B ⊓ J, c.e b₁ = u₁ :=
    ⟨c.d u₁, (hW u₁).mp hu₁, c.e_d u₁⟩
  obtain ⟨b₂, hb₂, rfl⟩ : ∃ b₂ ∈ B ⊓ J, c.e b₂ = u₂ :=
    ⟨c.d u₂, (hW u₂).mp hu₂, c.e_d u₂⟩
  have hmono : ∀ y ∈ B, c.e y ∈ ({c.e b, -c.e b, c.e b₁, -c.e b₁, c.e b₂, -c.e b₂} :
      Set (Fin 3 → ZMod 3)) → y ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) := by
    intro y hy hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · exact Or.inl (c.e_inj hy hD.hbB h)
    · exact Or.inr (Or.inl (c.e_inj hy (B.inv_mem hD.hbB) (by rw [h, c.e_inv hD.hbB])))
    · exact Or.inr (Or.inr (Or.inl (c.e_inj hy hb₁.1 h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (c.e_inj hy (B.inv_mem hb₁.1) (by rw [h, c.e_inv hb₁.1])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (c.e_inj hy hb₂.1 h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (c.e_inj hy (B.inv_mem hb₂.1) (by rw [h, c.e_inv hb₂.1]))))))
  have hM : IsFullMonomial B b b₁ b₂ := by
    refine ⟨hD.hE, c.closure_eq hD.hbB hb₁.1 hb₂.1 hli, ?_, ?_, ?_, ?_⟩
    · intro n hn x hx
      obtain ⟨g, hg, hgx⟩ := c.exists_mem_X hn
      have key : x ∈ B ∧ c.e x ∈ ({c.e b, -c.e b, c.e b₁, -c.e b₁, c.e b₂, -c.e b₂} :
          Set (Fin 3 → ZMod 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h | h <;> rw [h]
        · exact ⟨hD.hbB, by simp⟩
        · exact ⟨hb₁.1, by simp⟩
        · exact ⟨hb₂.1, by simp⟩
      have := hperm g hg _ key.2
      rw [hgx x key.1] at this
      exact hmono _ (conj_mem_of_nor hn key.1) this
    · obtain ⟨g, ⟨n, hn, hgx⟩, a1, a2, a3⟩ := h1
      exact ⟨n, hn, (c.act_neg_iff hgx hn hD.hbB hD.hbB).mp a1,
        (c.act_iff hgx hn hb₁.1 hb₁.1).mp a2, (c.act_iff hgx hn hb₂.1 hb₂.1).mp a3⟩
    · obtain ⟨g, ⟨n, hn, hgx⟩, a1, a2, a3⟩ := h2
      exact ⟨n, hn, (c.act_iff hgx hn hD.hbB hb₁.1).mp a1,
        (c.act_iff hgx hn hb₁.1 hD.hbB).mp a2, (c.act_iff hgx hn hb₂.1 hb₂.1).mp a3⟩
    · obtain ⟨g, ⟨n, hn, hgx⟩, a1, a2, a3⟩ := h3
      exact ⟨n, hn, (c.act_iff hgx hn hD.hbB hb₁.1).mp a1,
        (c.act_iff hgx hn hb₁.1 hb₂.1).mp a2, (c.act_iff hgx hn hb₂.1 hD.hbB).mp a3⟩
  refine ⟨?_, hCF b₁ b₂ hM, b₁, hb₁, b₂, hb₂, hM⟩
  obtain ⟨g, ⟨n, hn, hgx⟩, a1, -, -⟩ := h2
  exact ⟨n, by rw [(c.act_iff hgx hn hD.hbB hb₁.1).mp a1]; exact hb₁.2⟩

end Data

end CFSG.RankThree.PartTwo.Sec21.FF79.L13b

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 L13b
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ff79_1_3_of_cf
    (hCF : ∀ {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {B : Subgroup G},
      IsSylowOf 3 B (Cen b) → IsFullMonomial B b b₁ b₂ → ControlsFusionIn B)
    (hK : FF79KTypeLn) (hN : FF79KTypeLnNorm) (hGL : FF79KGL33) : FF79_1_3 := by
  intro G _ _ n hn b J h B hB
  obtain ⟨hE, hB0, hsup, hBcen⟩ := ff79_1_3_struct hK hn h hB
  refine ⟨hE, hB0, hsup, ?_⟩
  have hD := Data.of_hyp hK hN hn h hB
  obtain ⟨c⟩ := exists_coord hE
  obtain ⟨c₁, hc₁, c₂, hc₂, hli, hspan⟩ :=
    c.exists_basis_sub (inf_le_left : B ⊓ J ≤ B) (by rw [hB0.2]; norm_num)
  let W : Submodule (ZMod 3) (Fin 3 → ZMod 3) :=
    Submodule.span (ZMod 3) {c.e c₁, c.e c₂}
  have hW : ∀ u, u ∈ W ↔ c.d u ∈ B ⊓ J := hspan
  have hv : c.e b ∉ W := hD.not_mem_W c W hW
  have hli3 : LinearIndependent (ZMod 3) ![c.e b, c.e c₁, c.e c₂] := by
    have h1 : LinearIndependent (ZMod 3) (Fin.cons (c.e b) ![c.e c₁, c.e c₂]) := by
      rw [linearIndependent_finCons]
      refine ⟨hli, ?_⟩
      have hr : Set.range ![c.e c₁, c.e c₂] = {c.e c₁, c.e c₂} := by
        ext u
        simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        simp [eq_comm]
      rw [hr]
      exact hv
    exact h1
  have hcase := hGL c.X (c.e b) (c.e c₁) (c.e c₂) hli3
    (by
      obtain ⟨τ, hτ, h1, h2⟩ := hD.exists_tau c
      exact ⟨τ, hτ, h1, h2 c₁ hc₁, h2 c₂ hc₂⟩)
    (hD.card_stab c) (hD.exists_noncomm c) (hD.line_stab c W hW) (hD.exists_move c)
  rcases hcase with ⟨hstab, hmov⟩ | ⟨u₁, hu₁, u₂, hu₂, hli', hperm, h1, h2, h3⟩
  · exact Or.inl ⟨hD.not_conjInto c W hW (fun g hg w hw => hstab g hg w hw),
      fun D hDB hD3 => hD.orbit c W hW (fun g hg w hw => hstab g hg w hw) hmov D hDB hD3⟩
  · exact Or.inr (hD.case2 c W hW (fun b₁ b₂ hM => hCF hB hM) hu₁ hu₂ hli' hperm h1 h2 h3)

theorem ff79_1_3_of (hK : FF79KTypeLn) (hN : FF79KTypeLnNorm) (hGL : FF79KGL33) :
    FF79_1_3 :=
  ff79_1_3_of_cf (fun hB hM => controlsFusionIn_of_monomial hB hM) hK hN hGL

end CFSG.RankThree.PartTwo.Sec21.FF79
