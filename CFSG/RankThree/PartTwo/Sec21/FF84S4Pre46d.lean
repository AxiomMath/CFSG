module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46c
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44c

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

abbrev cmap (g : G) (V : Subgroup G) : Subgroup G := V.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_cmap {g : G} {V : Subgroup G} {w : G} :
    w ∈ cmap g V ↔ ∃ y ∈ V, g⁻¹ * y * g = w := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩

theorem conj_pow'' (g y : G) (n : ℕ) : (g⁻¹ * y * g) ^ n = g⁻¹ * y ^ n * g := by
  have := conj_pow (a := g⁻¹) (b := y) (i := n)
  simpa using this

theorem cmap_elt {g : G} {V : Subgroup G} (hV : ∀ w ∈ V, ∃ k : ℕ, w ^ 2 ^ k = 1) :
    ∀ w ∈ cmap g V, ∃ k : ℕ, w ^ 2 ^ k = 1 := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := mem_cmap.1 hw
  obtain ⟨k, hk⟩ := hV y hy
  exact ⟨k, by rw [conj_pow'', hk]; group⟩

theorem isP_of_elt {V : Subgroup G} (hV : ∀ w ∈ V, ∃ k : ℕ, w ^ 2 ^ k = 1) : IsPGroup 2 V := by
  intro x
  obtain ⟨k, hk⟩ := hV x.1 x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem T_elt {σ : G} {w : G} (hw : w ∈ Op 2 (Cen σ)) : ∃ k : ℕ, w ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := (FF79.L41.Op_isPGroup (p := 2) (Cen σ)) ⟨w, hw⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem claim_b (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) (hθ : ThM L b₁ b₂ θ) {σ : G} (hσB : σ ∈ CenS B)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Op 2 (Cen σ) ⊓ Cen b ≤ Subgroup.zpowers σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro v hv
  have := V_le h hZ hX hθ hσB hσ2 hσ1 (V := Op 2 (Cen σ) ⊓ Cen b)
    (fun w hw => T_elt hw.1) inf_le_right (inf_le_left.trans (FF79.L41.Op_le (p := 2) (Cen σ)))
    (fun l hl w hw => Subgroup.mem_inf.2
      ⟨FF79.L41.Op_conj_mem hl.2 hw.1,
        mul_mem (mul_mem (h.hyp.hLC hl.1) hw.2) (inv_mem (h.hyp.hLC hl.1))⟩) v hv
  rcases this with he | he
  · rw [he]; exact one_mem _
  · rw [he]; exact Subgroup.mem_zpowers σ

theorem claim_b₁ (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) (hθ : ThM L b₁ b₂ θ) {σ : G} (hσB : σ ∈ CenS B)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Op 2 (Cen σ) ⊓ Cen b₁ ≤ Subgroup.zpowers σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨s, hsN, hsb, hsb₁, hsb₂⟩, -⟩ := h.mono
  have hs'b₁ : s⁻¹ * b₁ * s = b := by rw [← hsb]; group
  set σ' : G := s⁻¹ * σ * s with hσ'
  have hσ'B : σ' ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    have hβ' : s * β * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hsN β).1 hβ
    have hc : (s * β * s⁻¹) * σ = σ * (s * β * s⁻¹) := Subgroup.mem_centralizer_iff.1 hσB _ hβ'
    calc β * σ' = s⁻¹ * ((s * β * s⁻¹) * σ) * s := by rw [hσ']; group
      _ = s⁻¹ * (σ * (s * β * s⁻¹)) * s := by rw [hc]
      _ = σ' * β := by rw [hσ']; group
  have hσ'2 : σ' * σ' = 1 := by
    calc σ' * σ' = s⁻¹ * (σ * σ) * s := by rw [hσ']; group
      _ = 1 := by rw [hσ2]; group
  have hσ'1 : σ' ≠ 1 := by
    intro he
    apply hσ1
    calc σ = s * (s⁻¹ * σ * s) * s⁻¹ := by group
      _ = 1 := by rw [← hσ', he]; group
  set V₁ : Subgroup G := Op 2 (Cen σ) ⊓ Cen b₁ with hV₁
  have hVV : ∀ w ∈ cmap s V₁, w = 1 ∨ w = σ' := by
    refine V_le h hZ hX hθ hσ'B hσ'2 hσ'1 (cmap_elt fun y hy => T_elt hy.1) ?_ ?_ ?_
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := mem_cmap.1 hw
      have := conj_mem_cen (g := s⁻¹) hy.2
      rw [inv_inv] at this
      rwa [hs'b₁] at this
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := mem_cmap.1 hw
      have := conj_mem_cen (g := s⁻¹) (FF79.L41.Op_le (p := 2) (Cen σ) hy.1)
      rwa [inv_inv] at this
    · intro l hl w hw
      obtain ⟨y, hy, rfl⟩ := mem_cmap.1 hw
      have hlb : l ∈ Cen b := h.hyp.hLC hl.1
      have hl'σ : s * l * s⁻¹ ∈ Cen σ := by
        have := conj_mem_cen (g := s) hl.2
        rwa [show s * σ' * s⁻¹ = σ by rw [hσ']; group] at this
      have hl'b₁ : s * l * s⁻¹ ∈ Cen b₁ := by
        have := conj_mem_cen (g := s) hlb
        rwa [hsb] at this
      refine mem_cmap.2 ⟨(s * l * s⁻¹) * y * (s * l * s⁻¹)⁻¹, Subgroup.mem_inf.2
        ⟨FF79.L41.Op_conj_mem hl'σ hy.1, mul_mem (mul_mem hl'b₁ hy.2) (inv_mem hl'b₁)⟩, ?_⟩
      group
  intro x hx
  have hw : s⁻¹ * x * s ∈ cmap s V₁ := mem_cmap.2 ⟨x, hx, rfl⟩
  rcases hVV _ hw with he | he
  · have : x = 1 := by
      calc x = s * (s⁻¹ * x * s) * s⁻¹ := by group
        _ = 1 := by rw [he]; group
    rw [this]; exact one_mem _
  · have : x = σ := by
      calc x = s * (s⁻¹ * x * s) * s⁻¹ := by group
        _ = σ := by rw [he, hσ']; group
    rw [this]; exact Subgroup.mem_zpowers σ

theorem claim_bb₁ (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) (hθ : ThM L b₁ b₂ θ)
    (hD : Cen (b * b₁) ≤ Nor (Subgroup.closure ({b, b₁} : Set G))) {σ : G} (hσB : σ ∈ CenS B)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Op 2 (Cen σ) ⊓ Cen (b * b₁) ≤ Subgroup.zpowers σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbσ : b ∈ Cen σ := Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hσB b (mem_b h))
  have hbc : b ∈ Cen (b * b₁) := B_le_cen_bb₁ h (mem_b h)
  have hbV : b ∈ Nor (Op 2 (Cen σ) ⊓ Cen (b * b₁)) := FF79.L41.mem_nor_of_forall fun y hy =>
    Subgroup.mem_inf.2 ⟨FF79.L41.Op_conj_mem hbσ hy.1, mul_mem (mul_mem hbc hy.2) (inv_mem hbc)⟩
  have hVv := S45_E_cen_2sub h hD h.fus
    ((FF79.L41.Op_isPGroup (p := 2) (Cen σ)).to_le inf_le_left) inf_le_right hbV
  intro v hv
  exact claim_b h hZ hX hθ hσB hσ2 hσ1 (Subgroup.mem_inf.2 ⟨hv.1, (hVv hv).1⟩)

theorem claim_bb₁sq (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) (hθ : ThM L b₁ b₂ θ)
    (hD : Cen (b * b₁) ≤ Nor (Subgroup.closure ({b, b₁} : Set G))) {σ : G} (hσB : σ ∈ CenS B)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Op 2 (Cen σ) ⊓ Cen (b * b₁ ^ 2) ≤ Subgroup.zpowers σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨i, hiN, hib, hib₁, hib₂⟩, ⟨s, hsN, hsb, hsb₁, hsb₂⟩, -⟩ := h.mono
  have hs'b : s⁻¹ * b * s = b₁ := by rw [← hsb₁]; group
  have hs'b₁ : s⁻¹ * b₁ * s = b := by rw [← hsb]; group
  set m : G := s * i * s⁻¹ with hm
  have hmb : m * b * m⁻¹ = b := by
    calc m * b * m⁻¹ = s * (i * (s⁻¹ * b * s) * i⁻¹) * s⁻¹ := by rw [hm]; group
      _ = b := by rw [hs'b, hib₁, hsb₁]
  have hmb₁ : m * b₁ * m⁻¹ = b₁⁻¹ := by
    calc m * b₁ * m⁻¹ = s * (i * (s⁻¹ * b₁ * s) * i⁻¹) * s⁻¹ := by rw [hm]; group
      _ = s * (i * b * i⁻¹) * s⁻¹ := by rw [hs'b₁]
      _ = s * b⁻¹ * s⁻¹ := by rw [hib]
      _ = (s * b * s⁻¹)⁻¹ := by group
      _ = b₁⁻¹ := by rw [hsb]
  have hb₁inv : b₁⁻¹ = b₁ ^ 2 :=
    (eq_inv_of_mul_eq_one_right (by
      rw [← pow_succ']; exact pow3_of_mem h (mem_b₁ h))).symm
  have hmbb₁ : m * (b * b₁) * m⁻¹ = b * b₁ ^ 2 := by
    calc m * (b * b₁) * m⁻¹ = (m * b * m⁻¹) * (m * b₁ * m⁻¹) := by group
      _ = b * b₁ ^ 2 := by rw [hmb, hmb₁, hb₁inv]
  have hmb' : m * b = b * m := by
    calc m * b = (m * b * m⁻¹) * m := by group
      _ = b * m := by rw [hmb]
  have hm'b : m⁻¹ * b * m = b := by
    calc m⁻¹ * b * m = m⁻¹ * (b * m) := by group
      _ = m⁻¹ * (m * b) := by rw [hmb']
      _ = b := by group
  have hbσ : b ∈ Cen σ := Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hσB b (mem_b h))
  have hbc : b ∈ Cen (b * b₁ ^ 2) := by
    have hc : Commute b b₁ := comm_of_mem h (mem_b h) (mem_b₁ h)
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Commute.refl b).mul_right (hc.pow_right 2)).eq
  set V' : Subgroup G := Op 2 (Cen σ) ⊓ Cen (b * b₁ ^ 2) with hV'
  have hWD : cmap m V' ≤ Cen (b * b₁) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := mem_cmap.1 hw
    have := conj_mem_cen (g := m⁻¹) hy.2
    rw [inv_inv] at this
    rwa [show m⁻¹ * (b * b₁ ^ 2) * m = b * b₁ by rw [← hmbb₁]; group] at this
  have hbW : b ∈ Nor (cmap m V') := FF79.L41.mem_nor_of_forall fun w hw => by
    obtain ⟨y, hy, rfl⟩ := mem_cmap.1 hw
    refine mem_cmap.2 ⟨b * y * b⁻¹, Subgroup.mem_inf.2
      ⟨FF79.L41.Op_conj_mem hbσ hy.1, mul_mem (mul_mem hbc hy.2) (inv_mem hbc)⟩, ?_⟩
    have hm'b' : m⁻¹ * b⁻¹ * m = b⁻¹ := by
      rw [show m⁻¹ * b⁻¹ * m = (m⁻¹ * b * m)⁻¹ by group, hm'b]
    calc m⁻¹ * (b * y * b⁻¹) * m = (m⁻¹ * b * m) * (m⁻¹ * y * m) * (m⁻¹ * b⁻¹ * m) := by group
      _ = b * (m⁻¹ * y * m) * b⁻¹ := by rw [hm'b, hm'b']
  have hWv := S45_E_cen_2sub h hD h.fus
    (isP_of_elt (cmap_elt (V := V') fun y hy => T_elt hy.1)) hWD hbW
  intro y hy
  have hyc : m⁻¹ * y * m ∈ Cen b := (hWv (mem_cmap.2 ⟨y, hy, rfl⟩)).1
  have hyb : y ∈ Cen b := by
    have := conj_mem_cen (g := m) hyc
    rwa [show m * (m⁻¹ * y * m) * m⁻¹ = y by group, hmb] at this
  exact claim_b h hZ hX hθ hσB hσ2 hσ1 (Subgroup.mem_inf.2 ⟨hy.1, hyb⟩)

theorem no_inv_cenB (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥) (hY : Opp 3 (Cen (b * b₁)) = ⊥)
    (h41 : FF84_4_1) {σ : G} (hσB : σ ∈ CenS B) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) : False := by
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isElemAb_E h
  have hD := S45_D_normalizes h41 h hY
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  set T := Op 2 (Cen σ) with hT
  have hT2 : IsPGroup 2 T := FF79.L41.Op_isPGroup (p := 2) (Cen σ)
  have hBσ : ∀ β ∈ B, β ∈ Cen σ := fun β hβ =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hσB β hβ)
  have hEN : Subgroup.closure ({b, b₁} : Set G) ≤ Nor T := fun e he =>
    nor_Op (p := 2) (hBσ e (closure_pair_le h he))
  have hgen := B_gen_centralizers (E := Subgroup.closure ({b, b₁} : Set G)) (X := T)
    (card_E_ge h) hT2 hEN
  have hTS : T ≤ Subgroup.zpowers σ := by
    refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    rcases E_four h ha ha1 with h1 | h1 | h1 | h1
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans
        (claim_b h hZ hX hθ hσB hσ2 hσ1)
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans
        (claim_b₁ h hZ hX hθ hσB hσ2 hσ1)
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans
        (claim_bb₁ h hZ hX hθ hD hσB hσ2 hσ1)
    · exact (inf_le_inf_left _ (cen_le_of_mem_zpowers h1)).trans
        (claim_bb₁sq h hZ hX hθ hD hσB hσ2 hσ1)
  have hσb : Commute σ b := Subgroup.mem_centralizer_singleton_iff.1 (cenB_cen_b h hσB)
  have hbT : b ∈ CenS T := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hTS ht)
    exact (hσb.zpow_left k).eq
  have hbmem := B_charTwo_cen h.hyp.char2 hσo (Subgroup.mem_inf.2 ⟨hBσ b (mem_b h), hbT⟩)
  have hbS : b ∈ Subgroup.zpowers σ := hTS hbmem
  have hdvd := orderOf_dvd_of_mem_zpowers hbS
  rw [h.hyp.ord, hσo] at hdvd
  omega

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
