module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiK
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Cc
public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiC

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.Quasithin
open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb)

variable {G : Type} [Group G] [Finite G]

theorem S36_op2_map_eq (c : G ≃* G) (H : Subgroup G) :
    Op 2 (H.map c.toMonoidHom) = (Op 2 H).map c.toMonoidHom := by
  apply le_antisymm (S36_op2_map_le c H)
  have h := S36_op2_map_le c.symm (H.map c.toMonoidHom)
  have e1 : (H.map c.toMonoidHom).map c.symm.toMonoidHom = H := by
    ext x; simp
  have e2 : ∀ K : Subgroup G, (K.map c.symm.toMonoidHom).map c.toMonoidHom = K := by
    intro K; ext x; simp
  rw [e1] at h
  have h2 := Subgroup.map_mono (f := c.toMonoidHom) h
  rwa [e2] at h2

theorem S36_core {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1)
    (hA9 : A9CentralizerStmt) (e : ↥L ≃* alternatingGroup (Fin 8)) {bk bj s : G}
    (hbk : bk ∈ L) (hbj : bj ∈ L)
    (hek : ((e ⟨bk, hbk⟩ : alternatingGroup (Fin 8)) : P8) = m₁)
    (hej : ((e ⟨bj, hbj⟩ : alternatingGroup (Fin 8)) : P8) = m₂)
    (hsb : s * b * s⁻¹ = b) (hs2 : s * s = 1) (hsk : s * bk * s⁻¹ = bk⁻¹)
    (hsj : s * bj * s⁻¹ = bj) :
    ∃ Q : Subgroup G, ExtraspecialAt Q s ∧ Op 2 (Cen s ⊓ Cen b) = Q ∧
      ∃ A : Subgroup G, A ≤ Q ∧ IsElemAb 2 3 A := by
  have hLC : L ≤ Cen b := d.sec.hyp.hLC
  have hsbc : s * b = b * s := by
    calc s * b = s * b * s⁻¹ * s := by group
      _ = b * s := by rw [hsb]
  have hsC : s ∈ Cen b := S36_mem_cen_of hsbc.symm
  have hsL : s ∈ L := S36_invol_cen_mem_L d h31 hsC hs2
  obtain ⟨Q, hQK, hQN, hQp, hQE, hA, hmax⟩ :=
    S36_A9_transport hA9 e hbk hbj hsL hek hej hs2 hsk hsj
  refine ⟨Q, hQE, le_antisymm ?_ ?_, hA⟩
  ·
    apply hmax
    · intro x hx
      have hxH : x ∈ Cen s ⊓ Cen b := S36_op2_le _ hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxH).1, ?_⟩
      obtain ⟨m, hm⟩ := S36_op2_isPGroup (Cen s ⊓ Cen b) ⟨x, hx⟩
      have hxm : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      exact S36_cen_b_two d h31 (Subgroup.mem_inf.1 hxH).2 hxm
        (Nat.Coprime.pow_left m (by norm_num))
    · exact S36_op2_isPGroup _
    · constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgH : (g : G) ∈ Cen s ⊓ Cen b :=
        ⟨(Subgroup.mem_inf.1 g.2).1, hLC (Subgroup.mem_inf.1 g.2).2⟩
      exact S36_op2_conj hgH hn
  ·
    apply S36_op2_of_normal
    · intro x hx
      obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.1 (hQK hx)
      exact Subgroup.mem_inf.2 ⟨hxC, hLC hxL⟩
    · constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      show (g : G) * (n : G) * (g : G)⁻¹ ∈ Q
      obtain ⟨hgs, hgb⟩ := Subgroup.mem_inf.1 g.2
      obtain ⟨k, l, hlL, hgl⟩ := S36_cen_b_form d hgb
      have hcomm : s * b ^ k = b ^ k * s := ((show Commute s b from hsbc).zpow_right k).eq
      have hsl : s * l = l * s := by
        apply mul_left_cancel (a := b ^ k)
        calc b ^ k * (s * l) = s * (b ^ k * l) := by rw [← mul_assoc, ← hcomm, mul_assoc]
          _ = s * (g : G) := by rw [hgl]
          _ = (g : G) * s := S36_comm_of_cen hgs
          _ = b ^ k * (l * s) := by rw [hgl, mul_assoc]
      have hnL : (n : G) ∈ L := (Subgroup.mem_inf.1 (hQK hn)).2
      have hlK : l ∈ Cen s ⊓ L := Subgroup.mem_inf.2 ⟨S36_mem_cen_of hsl, hlL⟩
      have hyL : l * (n : G) * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hlL hnL) (L.inv_mem hlL)
      have hcy : Commute (b ^ k) (l * (n : G) * l⁻¹) :=
        Commute.zpow_left (show Commute b (l * (n : G) * l⁻¹) from S36_comm_of_cen (hLC hyL)) k
      have key : (g : G) * (n : G) * (g : G)⁻¹ = l * (n : G) * l⁻¹ := by
        rw [hgl]
        calc b ^ k * l * (n : G) * (b ^ k * l)⁻¹ = b ^ k * (l * (n : G) * l⁻¹) * (b ^ k)⁻¹ := by
              group
          _ = l * (n : G) * l⁻¹ := by rw [hcy.eq, mul_inv_cancel_right]
      rw [key]
      have hc := Subgroup.Normal.conj_mem hQN ⟨(n : G), hQK hn⟩
        (Subgroup.mem_subgroupOf.2 hn) ⟨l, hlK⟩
      exact Subgroup.mem_subgroupOf.1 hc
    · exact hQp

theorem S36_Ti_gen {b t b₁ b₂ : G} {L B : Subgroup G} (hA9 : A9CentralizerStmt)
    (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1) {bk bj n : G} (hbk : bk ∈ L) (hbj : bj ∈ L)
    (e : ↥L ≃* alternatingGroup (Fin 8))
    (hek : ((e ⟨bk, hbk⟩ : alternatingGroup (Fin 8)) : P8) = m₁)
    (hej : ((e ⟨bj, hbj⟩ : alternatingGroup (Fin 8)) : P8) = m₂)
    (hnb : n * b * n⁻¹ = bk) (hnk : n * bk * n⁻¹ = b) (hnj : n * bj * n⁻¹ = bj) :
    ∃ Q : Subgroup G, Op 2 (Cen t) ⊓ Cen bk ≤ Q ∧ Nat.card Q = 32 ∧
      IsExtraspecialPGroup 2 ↥Q ∧ Q = Op 2 (Cen t ⊓ Cen bk) ∧ t ∈ Q ∧
      ExtraspecialAt Q t ∧ ∃ A : Subgroup G, A ≤ Q ∧ IsElemAb 2 3 A := by
  have htt : t * t = 1 := by rw [← sq]; exact S36_sq_of_orderOf_two d.ht
  have htk : t * bk = bk * t := (Subgroup.mem_centralizer_iff.1 d.htL bk hbk).symm
  have htj : t * bj = bj * t := (Subgroup.mem_centralizer_iff.1 d.htL bj hbj).symm
  obtain ⟨hs2, hsb, hsk, hsj⟩ := S36_monomial_conj htt d.htb htk htj hnb hnk hnj
  obtain ⟨Q₀, hQ₀E, hQ₀eq, A₀, hA₀Q, hA₀el⟩ := S36_core d h31 hA9 e hbk hbj hek hej hsb hs2 hsk hsj
  let c : G ≃* G := MulAut.conj n⁻¹
  have hcs : c (n * t * n⁻¹) = t := by
    show n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t
    group
  have hcb : c b = bk := by
    show n⁻¹ * b * n⁻¹⁻¹ = bk
    rw [inv_inv, ← hnk]
    group
  have hHt : (Cen (n * t * n⁻¹) ⊓ Cen b).map c.toMonoidHom = Cen t ⊓ Cen bk := by
    rw [Subgroup.map_inf_eq _ _ _ (show Function.Injective c.toMonoidHom from c.injective),
      S36_map_cen, S36_map_cen, hcs, hcb]
  have hOp : Op 2 (Cen t ⊓ Cen bk) = Q₀.map c.toMonoidHom := by
    rw [← hHt, S36_op2_map_eq, hQ₀eq]
  have hE₀ : ExtraspecialAt (Q₀.map c.toMonoidHom) t := by
    have h := S36_ext_fwd c.toMonoidHom c.injective hQ₀E
    rwa [show c.toMonoidHom (n * t * n⁻¹) = t from hcs] at h
  refine ⟨Q₀.map c.toMonoidHom, ?_, ?_, S36_isExtraspecial_of_ext hE₀, hOp.symm, ?_, hE₀,
    ⟨A₀.map c.toMonoidHom, Subgroup.map_mono hA₀Q,
      S36_elemAb_map c.toMonoidHom c.injective hA₀el⟩⟩
  ·
    rw [← hOp]
    apply S36_op2_of_normal
    · intro x hx
      exact Subgroup.mem_inf.2 ⟨S36_op2_le _ (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    · constructor
      intro n₀ hn₀ g
      rw [Subgroup.mem_subgroupOf] at hn₀ ⊢
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn₀
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 g.2
      exact Subgroup.mem_inf.2 ⟨S36_op2_conj hg1 hn1, S36_conj_mem_cen hg2 hn2⟩
    · exact S36_isPGroup_mono (S36_op2_isPGroup _) inf_le_left
  · rw [Subgroup.card_map_of_injective c.injective]
    exact hQ₀E.card_eq
  · have h := Subgroup.mem_map_of_mem c.toMonoidHom hQ₀E.mem
    rwa [show c.toMonoidHom (n * t * n⁻¹) = t from hcs] at h

theorem S36_conj_swap_pair {b b₁ b₂ s c : G} (hs1 : s * b * s⁻¹ = b₁)
    (hs2 : s * b₁ * s⁻¹ = b) (hs3 : s * b₂ * s⁻¹ = b₂) (hc1 : c * b * c⁻¹ = b₁)
    (hc2 : c * b₁ * c⁻¹ = b₂) (hc3 : c * b₂ * c⁻¹ = b) :
    (c⁻¹ * s * c) * b * (c⁻¹ * s * c)⁻¹ = b₂ ∧ (c⁻¹ * s * c) * b₂ * (c⁻¹ * s * c)⁻¹ = b ∧
      (c⁻¹ * s * c) * b₁ * (c⁻¹ * s * c)⁻¹ = b₁ := by
  refine ⟨?_, ?_, ?_⟩
  · calc c⁻¹ * s * c * b * (c⁻¹ * s * c)⁻¹ = c⁻¹ * s * (c * b * c⁻¹) * s⁻¹ * c := by group
      _ = c⁻¹ * s * b₁ * s⁻¹ * c := by rw [hc1]
      _ = c⁻¹ * (s * b₁ * s⁻¹) * c := by group
      _ = c⁻¹ * b * c := by rw [hs2]
      _ = b₂ := by rw [← hc3]; group
  · calc c⁻¹ * s * c * b₂ * (c⁻¹ * s * c)⁻¹ = c⁻¹ * s * (c * b₂ * c⁻¹) * s⁻¹ * c := by group
      _ = c⁻¹ * s * b * s⁻¹ * c := by rw [hc3]
      _ = c⁻¹ * (s * b * s⁻¹) * c := by group
      _ = c⁻¹ * b₁ * c := by rw [hs1]
      _ = b := by rw [← hc1]; group
  · calc c⁻¹ * s * c * b₁ * (c⁻¹ * s * c)⁻¹ = c⁻¹ * s * (c * b₁ * c⁻¹) * s⁻¹ * c := by group
      _ = c⁻¹ * s * b₂ * s⁻¹ * c := by rw [hc2]
      _ = c⁻¹ * (s * b₂ * s⁻¹) * c := by group
      _ = c⁻¹ * b₂ * c := by rw [hs3]
      _ = b₁ := by rw [← hc2]; group

theorem F6_Ti {b t b₁ b₂ : G} {L B : Subgroup G} (hA9 : A9CentralizerStmt)
    (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1) (i : Fin 2) :
    ∃ Q : Subgroup G, Op 2 (Cen t) ⊓ Cen (![b₁, b₂] i) ≤ Q ∧ Nat.card Q = 32 ∧
      IsExtraspecialPGroup 2 ↥Q ∧ Q = Op 2 (Cen t ⊓ Cen (![b₁, b₂] i)) ∧ t ∈ Q ∧
      ExtraspecialAt Q t ∧ ∃ A : Subgroup G, A ≤ Q ∧ IsElemAb 2 3 A := by
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ d.sec).2
  obtain ⟨e, he⟩ := M0_model d.sec hZ
  have hb₁L : b₁ ∈ L := d.sec.hb₁.2
  have hb₂L : b₂ ∈ L := d.sec.hb₂.2
  obtain ⟨hm1, hm2⟩ := he ⟨b₁, hb₁L⟩ ⟨b₂, hb₂L⟩ rfl rfl
  obtain ⟨-, -, -, -, ⟨n₁, -, hs1, hs2, hs3⟩, ⟨c, -, hc1, hc2, hc3⟩⟩ := d.sec.mono
  fin_cases i
  · exact S36_Ti_gen hA9 d h31 hb₁L hb₂L e hm1 hm2 hs1 hs2 hs3
  ·
    have he2 : (((e.trans (MulAut.conjNormal (Equiv.swap 4 5))) ⟨b₂, hb₂L⟩ :
        alternatingGroup (Fin 8)) : P8) = m₁ := by
      rw [MulEquiv.trans_apply, M0_conjNormal_val, hm2]
      decide
    have he1 : (((e.trans (MulAut.conjNormal (Equiv.swap 4 5))) ⟨b₁, hb₁L⟩ :
        alternatingGroup (Fin 8)) : P8) = m₂ := by
      rw [MulEquiv.trans_apply, M0_conjNormal_val, hm1]
      decide
    obtain ⟨hnb, hnk, hnj⟩ := S36_conj_swap_pair hs1 hs2 hs3 hc1 hc2 hc3
    exact S36_Ti_gen hA9 d h31 hb₂L hb₁L (e.trans (MulAut.conjNormal (Equiv.swap 4 5)))
      he2 he1 hnb hnk hnj

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
