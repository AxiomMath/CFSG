module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMap

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

set_option maxRecDepth 100000

@[expose] def TPermChk (gc : List (List ℕ)) : Bool :=
  gc.all fun g =>
    (l1Lit.contains (cconj g (code a1)) && l1Lit.contains (cconj g (code b1)) &&
      l2Lit.contains (cconj g (code a2)) && l2Lit.contains (cconj g (code b2))) ||
    (l2Lit.contains (cconj g (code a1)) && l2Lit.contains (cconj g (code b1)) &&
      l1Lit.contains (cconj g (code a2)) && l1Lit.contains (cconj g (code b2)))

@[expose] def PermL (g : P16) : Prop :=
  (L01.map (MulAut.conj g).toMonoidHom = L01 ∧ L02.map (MulAut.conj g).toMonoidHom = L02) ∨
    (L01.map (MulAut.conj g).toMonoidHom = L02 ∧ L02.map (MulAut.conj g).toMonoidHom = L01)

theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp

theorem card_L02 : Nat.card L02 = 168 := by rw [l2_desc.card l2_nodup, l2_length]

theorem map_conj_eq_of_gens {H K : Subgroup P16} {g : P16} {S : Set P16} (hH : H = closure S)
    (hS : ∀ x ∈ S, g * x * g⁻¹ ∈ K) (hc : Nat.card H = Nat.card K) :
    H.map (MulAut.conj g).toMonoidHom = K := by
  refine eq_of_le_of_card_ge ?_ ?_
  · rw [hH, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hS x hx
  · rw [card_map_of_injective (MulAut.conj g).injective, hc]

theorem permL_of_chk {gc : List (List ℕ)} (h : TPermChk gc = true) {g : P16} (hg : code g ∈ gc) :
    PermL g := by
  simp only [TPermChk, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    List.contains_iff_mem] at h
  have hmem : ∀ {L : Subgroup P16} {LL : List (List ℕ)}, LDesc L LL → ∀ x : P16,
      cconj (code g) (code x) ∈ LL → g * x * g⁻¹ ∈ L := fun hL x hx => by
    rw [← code_conj] at hx
    exact (hL.mem _).2 hx
  have h1 : ∀ x ∈ ({g | g ∈ [a1, b1]} : Set P16), ∀ {L : Subgroup P16} {LL : List (List ℕ)},
      LDesc L LL → cconj (code g) (code a1) ∈ LL → cconj (code g) (code b1) ∈ LL →
      g * x * g⁻¹ ∈ L := by
    intro x hx L LL hL ha hb
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hmem hL _ ha
    · exact hmem hL _ hb
  have h2 : ∀ x ∈ ({g | g ∈ [a2, b2]} : Set P16), ∀ {L : Subgroup P16} {LL : List (List ℕ)},
      LDesc L LL → cconj (code g) (code a2) ∈ LL → cconj (code g) (code b2) ∈ LL →
      g * x * g⁻¹ ∈ L := by
    intro x hx L LL hL ha hb
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hmem hL _ ha
    · exact hmem hL _ hb
  rcases h _ hg with ⟨⟨⟨ha1, hb1⟩, ha2⟩, hb2⟩ | ⟨⟨⟨ha1, hb1⟩, ha2⟩, hb2⟩
  · exact Or.inl ⟨map_conj_eq_of_gens rfl (fun x hx => h1 x hx l1_desc ha1 hb1) rfl,
      map_conj_eq_of_gens rfl (fun x hx => h2 x hx l2_desc ha2 hb2) rfl⟩
  · exact Or.inr ⟨map_conj_eq_of_gens rfl (fun x hx => h1 x hx l2_desc ha1 hb1)
      (by rw [card_L01, card_L02]),
      map_conj_eq_of_gens rfl (fun x hx => h2 x hx l1_desc ha2 hb2) (by rw [card_L01, card_L02])⟩

theorem permL_mul {a b : P16} (ha : PermL a) (hb : PermL b) : PermL (a * b) := by
  unfold PermL at *
  rw [map_conj_mul, map_conj_mul]
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ha with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h1, h2, h3, h4] <;> simp

theorem permL_inv {a : P16} (ha : PermL a) : PermL a⁻¹ := by
  unfold PermL at *
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · conv_lhs => rw [← h1]
      exact map_conj_inv_map_conj _ _
    · conv_lhs => rw [← h2]
      exact map_conj_inv_map_conj _ _
  · right
    constructor
    · conv_lhs => rw [← h2]
      exact map_conj_inv_map_conj _ _
    · conv_lhs => rw [← h1]
      exact map_conj_inv_map_conj _ _

theorem permL_of_mem_TB {i : Fin 4} (h : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true)
    {t : P16} (ht : t ∈ TB i) : PermL t := by
  rw [TB] at ht
  induction ht using closure_induction with
  | mem x hx => exact permL_of_chk h (List.mem_map_of_mem hx)
  | one => exact Or.inl ⟨map_conj_one _, map_conj_one _⟩
  | mul x y _ _ hx hy => exact permL_mul hx hy
  | inv x _ hx => exact permL_inv hx

variable (i : Fin 4)

theorem map_conj_self {G : Type*} [Group G] {H : Subgroup G} {t : G} (ht : t ∈ H) :
    H.map (MulAut.conj t).toMonoidHom = H := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem ht hy) (inv_mem ht)
  · exact ⟨t⁻¹ * x * t, mul_mem (mul_mem (inv_mem ht) hx) ht, by
      simp [MulAut.conj_apply, mul_assoc]⟩

theorem tperm_X (h : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true) {t : ↥(GB i)}
    (ht : t ∈ Tb i) :
    ((L1b i).map (MulAut.conj t).toMonoidHom = L1b i ∧
        (L2b i).map (MulAut.conj t).toMonoidHom = L2b i) ∨
      ((L1b i).map (MulAut.conj t).toMonoidHom = L2b i ∧
        (L2b i).map (MulAut.conj t).toMonoidHom = L1b i) := by
  have hp := permL_of_mem_TB (t := (t : P16)) h ht
  have e1 : (L1b i).map (MulAut.conj t).toMonoidHom =
      (L01.map (MulAut.conj t.1).toMonoidHom).subgroupOf (GB i) := map_conj_subgroupOf t.2
  have e2 : (L2b i).map (MulAut.conj t).toMonoidHom =
      (L02.map (MulAut.conj t.1).toMonoidHom).subgroupOf (GB i) := map_conj_subgroupOf t.2
  rw [e1, e2]
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

theorem table_conj (h : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true)
    {t : ↥(GB i)} (ht : t ∈ Tb i) {A : Subgroup ↥(GB i)}
    (hA : (∃ H R Lh : Subgroup ↥(GB i), FiveWit (L1b i) (L2b i) (Tb i) A H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB i), SevenWit (L1b i) (L2b i) (Tb i) A K Y) :
    (∃ H R Lh : Subgroup ↥(GB i), FiveWit (L1b i) (L2b i) (Tb i)
        (A.map (MulAut.conj t).toMonoidHom) H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB i), SevenWit (L1b i) (L2b i) (Tb i)
        (A.map (MulAut.conj t).toMonoidHom) K Y := by
  have h1 := NGM.table_map_equiv (MulAut.conj t) hA
  rw [map_conj_self ht] at h1
  rcases tperm_X i h ht with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rwa [e1, e2] at h1
  · rw [e1, e2] at h1
    rcases h1 with ⟨H, R, Lh, hw⟩ | ⟨K, Y, hw⟩
    · exact Or.inl ⟨H, R, Lh, hw.swap⟩
    · exact Or.inr ⟨K, Y, hw.swap⟩

theorem close_conj (h : TPermChk (([u1, v1, u2, v2] ++ bGens i).map code) = true)
    {t : ↥(GB i)} (ht : t ∈ Tb i) {U : Subgroup ↥(GB i)}
    (hU : (∃ H R Lh : Subgroup ↥(GB i), FiveWit (L1b i) (L2b i) (Tb i) U H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB i), KillWit (L1b i) (L2b i) (Tb i) U K Y) :
    (∃ H R Lh : Subgroup ↥(GB i), FiveWit (L1b i) (L2b i) (Tb i)
        (U.map (MulAut.conj t).toMonoidHom) H R Lh) ∨
      ∃ K Y : Subgroup ↥(GB i), KillWit (L1b i) (L2b i) (Tb i)
        (U.map (MulAut.conj t).toMonoidHom) K Y := by
  have h1 := NGM.close_map_equiv (MulAut.conj t) hU
  rw [map_conj_self ht] at h1
  rcases tperm_X i h ht with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rwa [e1, e2] at h1
  · rw [e1, e2] at h1
    rcases h1 with ⟨H, R, Lh, hw⟩ | ⟨K, Y, hw⟩
    · exact Or.inl ⟨H, R, Lh, hw.swap⟩
    · exact Or.inr ⟨K, Y, hw.swap⟩

theorem xdesc_map_conj {A : Subgroup ↥(GB i)} {AL : List (List ℕ)} (hA : XDesc A AL) (t : ↥(GB i)) :
    XDesc (A.map (MulAut.conj t).toMonoidHom) (AL.map (cconj (code t.1))) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨code y.1, (hA.mem y).1 hy, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj]
    · rintro ⟨d, hd, hdx⟩
      obtain ⟨y, hy, rfl⟩ := hA.surj d hd
      refine ⟨y, hy, Subtype.ext (code_injective ?_)⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj, hdx]
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y, hy, rfl⟩ := hA.surj d hd
    exact ⟨t * y * t⁻¹, ⟨y, hy, rfl⟩, by rw [Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, code_conj]⟩

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
