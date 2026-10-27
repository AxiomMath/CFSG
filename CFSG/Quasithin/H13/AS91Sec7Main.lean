module

public import CFSG.Quasithin.H13.AS91Sec7Six
public import CFSG.Quasithin.H13.AS91Sec7Seven
public import CFSG.Quasithin.H13.AS91Sec7Eight
public import CFSG.Quasithin.H13.AS91Sec7Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

section Graph

variable {V : Type*} {Δ : SimpleGraph V}

theorem dist2_symm_of_dist2 {x y : V} (h : Dist2 Δ x y) : Dist2 Δ y x := by
  obtain ⟨hne, hnadj, w, h1, h2⟩ := h
  exact ⟨hne.symm, fun h' => hnadj h'.symm, w, h2.symm, h1.symm⟩

theorem adj_of_dSet {R : ℕ → V → V → V → Prop} {k : ℕ} {x u y w : V}
    (h : dSet Δ R k x u y w) : Δ.Adj x w := by
  rcases h with ⟨-, ⟨hw, -⟩, -⟩ | ⟨hw, -⟩
  exacts [hw, hw]

end Graph

section Parity

theorem exists_fixed_pt_of_odd_ncard {α : Type*} {T : Set α} (hT : T.Finite) (hodd : Odd T.ncard)
    (f : α → α) (hf : ∀ a, f (f a) = a) (hmem : ∀ a ∈ T, f a ∈ T) : ∃ a ∈ T, f a = a := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : ∑ _x ∈ hT.toFinset, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => f a) (fun a _ => ?_) (fun a ha _ => ?_)
      (fun a ha => ?_) (fun a ha => ?_)
    · decide
    · exact hcon a (hT.mem_toFinset.1 ha)
    · exact hT.mem_toFinset.2 (hmem a (hT.mem_toFinset.1 ha))
    · exact hf a
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← Set.ncard_eq_toFinset_card T hT,
    ZMod.natCast_eq_zero_iff_even] at hsum
  exact (Nat.not_even_iff_odd.2 hodd) hsum

end Parity

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem z_smul_smul (hJ : HypJ4 G z) (a : G ⧸ c.G1) : z • z • a = a := by
  have h := pow_orderOf_eq_one z
  rw [hJ.orderOf_z, pow_two] at h
  rw [← mul_smul, h, one_smul]

theorem z_fix_all_of_fix {a : G ⧸ c.G1} (ha : c.OnP a c.pi0) {m : G ⧸ c.G2} (hm : c.OnL a m)
    {p q : G ⧸ c.G1} (hp : c.OnL p m) (hpa : p ≠ a) (hq : c.OnL q m) (hqa : q ≠ a)
    (hzp : z • p = p) : z • q = q := by
  obtain ⟨h, hh, hha⟩ := c.exists_G3_smul_x0 ha
  have hm' : c.OnL c.x0 (h⁻¹ • m) := c.onL_x0_inv_smul hha hm
  have hp' : c.OnL (h⁻¹ • p) (h⁻¹ • m) := (cInc_smul c.G1 c.G2 h⁻¹ p m).2 hp
  have hq' : c.OnL (h⁻¹ • q) (h⁻¹ • m) := (cInc_smul c.G1 c.G2 h⁻¹ q m).2 hq
  have hp0 : h⁻¹ • p ≠ c.x0 := fun e => hpa (by rw [← hha, ← e, smul_inv_smul])
  have hq0 : h⁻¹ • q ≠ c.x0 := fun e => hqa (by rw [← hha, ← e, smul_inv_smul])
  have hcomm : ∀ r : G ⧸ c.G1, z • h⁻¹ • r = h⁻¹ • z • r := fun r => by
    rw [← mul_smul, ← mul_smul, c.z_mul_of_mem_G3 (inv_mem hh)]
  have hzp' : z • h⁻¹ • p = h⁻¹ • p := by rw [hcomm, hzp]
  have h1 : z • h⁻¹ • q = h⁻¹ • q := c.E_fix_all_of_fix hm' c.z_mem_E hp' hp0 hq' hq0 hzp'
  rw [hcomm] at h1
  exact MulAction.injective h⁻¹ h1

theorem exists_pt_inter_line {A B : Set (G ⧸ c.G1)} {m : G ⧸ c.G2} (hA3 : 3 ≤ A.ncard)
    (hB3 : 3 ≤ B.ncard) (hA : ∀ a ∈ A, c.OnL a m) (hB : ∀ a ∈ B, c.OnL a m) :
    ∃ a, a ∈ A ∧ a ∈ B := by
  have hsub : A ∪ B ⊆ {a | c.OnL a m} := by
    rintro a (ha | ha)
    · exact hA a ha
    · exact hB a ha
  have h5 := Set.ncard_le_ncard hsub
  rw [c.ncard_onL m] at h5
  have hinter := Set.ncard_union_add_ncard_inter A B
  have hne0 : (A ∩ B).ncard ≠ 0 := by omega
  obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero hne0
  exact ⟨a, ha.1, ha.2⟩

theorem dSet_one_two {x u y a : G ⧸ c.G1} (h : dSet c.Delta c.Rh 1 x u y a) :
    dSet c.Delta c.Rh 2 x u y a := by
  rcases h with h | ⟨hxa, d, hd, hR⟩
  · exact Or.inl h
  · exact Or.inr ⟨hxa, d, hd, c.rh_two_iff.2 (Or.inl hR)⟩

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

section B2


include ρ in
theorem b2_k0 (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v w : G ⧸ c.G1} (h1 : c.Rh 1 x u y)
    (h0 : ¬ c.Rh 0 x u y) (h3 : c.Rh 3 x v w) (h0' : ¬ c.Rh 0 x v w) :
    ∃ a b, comp c.Delta x u y a ∧ comp c.Delta x v w b ∧ Perp c.Delta a b := by
  obtain ⟨hxv, hvw, hxw⟩ := c.rh_three_iff.1 h3
  have hdw : Dist2 c.Delta x w := ⟨hxw, fun h => h0' ⟨hxv, hvw, h⟩, v, hxv, hvw⟩
  rcases c.rh_one_iff.1 h1 with h | ⟨hxu, huy, hxy, m, n, hum, hxm, hun, hyn, σ, hmσ, hnσ⟩
  · exact absurd h h0
  · have hdy : Dist2 c.Delta x y := ⟨hxy, fun h => h0 ⟨hxu, huy, h⟩, u, hxu, huy⟩
    have hxσ : c.OnP x σ := c.inc_pt_plane hxm hmσ
    have hyσ : c.OnP y σ := c.inc_pt_plane hyn hnσ
    obtain ⟨a, b, hxa, hya, hb, hab⟩ :=
      ρ.stmt7_6_two hI hJ hdy ⟨σ, hxσ, hyσ⟩ hdw hxv hvw
    exact ⟨a, b, ρ.stmt7_5_comp hI hJ hdy hxσ hyσ ⟨hxu, huy.symm⟩ ⟨hxa, hya⟩, hb, hab⟩

include ρ in
theorem b2_of_plane (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v w : G ⧸ c.G1} {k : ℕ}
    {π : G ⧸ c.G3} (hxπ : c.OnP x π)
    (hl : ∀ m, c.OnL x m → c.LnP m π → ∃ s, c.OnL s m ∧ dSet c.Delta c.Rh k x u y s)
    (hxv : c.Delta.Adj x v) (hvw : c.Delta.Adj v w) (hdw : Dist2 c.Delta x w) :
    ∃ a b, dSet c.Delta c.Rh k x u y a ∧ comp c.Delta x v w b ∧ induced c.Delta c.Rh 1 a b := by
  obtain ⟨s, hs, b, hb, hsb⟩ := ρ.stmt7_6_one hI hJ hxπ
    (S := {s | c.OnP s π ∧ dSet c.Delta c.Rh k x u y s})
    (fun s hs => ⟨adj_of_dSet hs.2, hs.1⟩)
    (fun m hm hmπ => by
      obtain ⟨s, hsm, hsd⟩ := hl m hm hmπ
      exact ⟨s, ⟨c.inc_pt_plane hsm hmπ, hsd⟩, hsm⟩) hdw hxv hvw
  exact ⟨s, b, hs.2, hb, hsb⟩

include ρ in
theorem b2_k1 (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v w : G ⧸ c.G1} (h2 : c.Rh 2 x u y)
    (h1 : ¬ c.Rh 1 x u y) (h3 : c.Rh 3 x v w) (h0' : ¬ c.Rh 0 x v w) :
    ∃ a b, dSet c.Delta c.Rh 1 x u y a ∧ comp c.Delta x v w b ∧ induced c.Delta c.Rh 1 a b := by
  obtain ⟨hxv, hvw, hxw⟩ := c.rh_three_iff.1 h3
  have hdw : Dist2 c.Delta x w := ⟨hxw, fun h => h0' ⟨hxv, hvw, h⟩, v, hxv, hvw⟩
  obtain ⟨hxu, huy, -⟩ := c.rh21_path h2 h1
  obtain ⟨L, hxL, huL⟩ := c.exists_onL_of_adj hxu
  obtain ⟨M, huM, hyM⟩ := c.exists_onL_of_adj huy
  have hδ3 : M ∈ c.deltaAt 3 u L := c.rh21_mem_delta3 hI hJ h2 h1 huL hxL huM hyM
  obtain ⟨π, ⟨hπu, hLπ, hMπ⟩, -⟩ := ρ.existsUnique_plane_meetsP hJ huL huM hδ3
  exact ρ.b2_of_plane hI hJ (c.inc_pt_plane hxL hLπ)
    (fun m hxm hmπ => ρ.stmt7_4_two hI hJ h2 h1 huL hxL huM hyM hπu hLπ hMπ hxm hmπ) hxv hvw hdw

include ρ in
theorem b2_k1' (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v w : G ⧸ c.G1} (h2 : c.Rh 2 x u y)
    (h0 : ¬ c.Rh 0 x u y) (h3 : c.Rh 3 x v w) (h0' : ¬ c.Rh 0 x v w) :
    ∃ a b, dSet c.Delta c.Rh 1 x u y a ∧ comp c.Delta x v w b ∧ induced c.Delta c.Rh 1 a b := by
  by_cases h1 : c.Rh 1 x u y
  · obtain ⟨a, b, ha, hb, hab⟩ := ρ.b2_k0 hI hJ h1 h0 h3 h0'
    exact ⟨a, b, Or.inl ha, hb, Or.inl hab⟩
  · exact ρ.b2_k1 hI hJ h2 h1 h3 h0'

include ρ in
theorem b2_k2 (hI : Sec7Inputs) (hJ : HypJ4 G z) {x u y v w : G ⧸ c.G1} (h3 : c.Rh 3 x u y)
    (h2 : ¬ c.Rh 2 x u y) (h3' : c.Rh 3 x v w) (h0' : ¬ c.Rh 0 x v w) :
    ∃ a b, dSet c.Delta c.Rh 2 x u y a ∧ comp c.Delta x v w b ∧ induced c.Delta c.Rh 1 a b := by
  obtain ⟨hxv, hvw, hxw⟩ := c.rh_three_iff.1 h3'
  have hdw : Dist2 c.Delta x w := ⟨hxw, fun h => h0' ⟨hxv, hvw, h⟩, v, hxv, hvw⟩
  obtain ⟨π, hxπ, hl⟩ := ρ.stmt7_7 hI hJ h3 h2
  exact ρ.b2_of_plane hI hJ hxπ hl hxv hvw hdw

include ρ in
theorem hypB2 (hI : Sec7Inputs) (hJ : HypJ4 G z) :
    ∀ k < 3, ∀ x u y v w, c.Rh (k + 1) x u y → ¬ c.Rh 0 x u y → c.Rh 3 x v w →
      ¬ c.Rh 0 x v w → ∃ a b, dSet c.Delta c.Rh k x u y a ∧ comp c.Delta x v w b ∧
        induced c.Delta c.Rh (min k 1) a b := by
  intro k hk x u y v w h1 h0 h3 h0'
  match k, hk, h1 with
  | 0, _, h1 =>
    obtain ⟨a, b, ha, hb, hab⟩ := ρ.b2_k0 hI hJ h1 h0 h3 h0'
    exact ⟨a, b, Or.inl ha, hb, Or.inl hab⟩
  | 1, _, h1 => exact ρ.b2_k1' hI hJ h1 h0 h3 h0'
  | 2, _, h1 =>
    by_cases h2 : c.Rh 2 x u y
    · obtain ⟨a, b, ha, hb, hab⟩ := ρ.b2_k1' hI hJ h2 h0 h3 h0'
      exact ⟨a, b, c.dSet_one_two ha, hb, hab⟩
    · exact ρ.b2_k2 hI hJ h1 h2 h3 h0'
  | k + 3, hk, _ => exact absurd hk (by omega)

end B2

section B3a


include ρ in
theorem three_adj_at (hI : Sec7Inputs) (hJ : HypJ4 G z) {x w : G ⧸ c.G1}
    {d k : G ⧸ c.G2} (hxd : c.OnL x d) (hwd : c.OnL w d) (hwx : w ≠ x) (hxk : c.OnL x k)
    (hco : c.CoL k d) : k = d ∨ 3 ≤ {a | c.OnL a k ∧ c.Delta.Adj w a}.ncard := by
  rcases (ρ.coL_iff_deltaAt hxd hxk).1 (Loc49.CoL.symm c hco) with h0 | h1 | h2
  · exact Or.inl ((ρ.mem_deltaAt_zero_iff hxd hxk).1 h0)
  · exact Or.inr (c.stmt7_1_one hI.s54 hJ hxd hwd hwx h1).ge
  · refine Or.inr ?_
    have hsub : {a | c.OnL a k} ⊆ {a | c.OnL a k ∧ c.Delta.Adj w a} :=
      fun a (ha : c.OnL a k) => ⟨ha, c.stmt7_1_two hI.s54 hJ hxd hwd hwx h2 ha⟩
    have h5 := Set.ncard_le_ncard hsub
    rw [c.ncard_onL k] at h5
    omega

include ρ in
theorem exists_pt_of_coL (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y w : G ⧸ c.G1}
    {d l : G ⧸ c.G2} {π : G ⧸ c.G3} (hxy : Dist2 c.Delta x y) (hxπ : c.OnP x π)
    (hyπ : c.OnP y π) (hyd : c.OnL y d) (hwd : c.OnL w d) (hwy : w ≠ y) (hyl : c.OnL y l)
    (hlπ : c.LnP l π) (hco : c.CoL l d) :
    ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w := by
  have hA := c.stmt7_5_three hI hJ (dist2_symm_of_dist2 hxy) hyπ hxπ hyl hlπ
  rcases ρ.three_adj_at hI hJ hyd hwd hwy hyl hco with hld | hB
  · obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero
      (by omega : {a | c.OnL a l ∧ c.Delta.Adj y a ∧ c.Delta.Adj x a}.ncard ≠ 0)
    refine ⟨a, ha.2.2, ha.2.1, ?_⟩
    rcases eq_or_ne a w with haw | haw
    · exact Or.inl haw
    · exact Or.inr (c.adj_of_onL haw ha.1 (by rw [hld]; exact hwd))
  · obtain ⟨a, haA, haB⟩ :=
      c.exists_pt_inter_line hA hB (fun a ha => ha.1) (fun a ha => ha.1)
    exact ⟨a, haA.2.2, haA.2.1, Or.inr haB.2.symm⟩

include ρ in
theorem adj_of_z_fix (hI : Sec7Inputs) (hJ : HypJ4 G z) {y v w : G ⧸ c.G1} {d : G ⧸ c.G2}
    (hy : c.OnP y c.pi0) (hyd : c.OnL y d) (hwd : c.OnL w d) (hwy : w ≠ y) (hzw : z • w ≠ w)
    (hvw : c.Delta.Adj w v) (hvd : ¬ c.OnL v d) (hzv : z • v = v) : c.Delta.Adj y v := by
  have hzd : z • d = d := ρ.z_smul_line_of_onP hy hyd
  have hmem : ∀ p ∈ {p | c.OnL p d ∧ c.Delta.Adj v p},
      z • p ∈ {p | c.OnL p d ∧ c.Delta.Adj v p} := by
    rintro p ⟨hpd, hvp⟩
    refine ⟨?_, ?_⟩
    · have h := (cInc_smul c.G1 c.G2 z p d).2 hpd
      rwa [hzd] at h
    · have h := (c.adj_smul_iff z).2 hvp
      rwa [hzv] at h
  obtain ⟨hzwd, hvzw⟩ := hmem w ⟨hwd, hvw.symm⟩
  obtain ⟨e, hze, hve⟩ := c.exists_onL_of_adj hvzw.symm
  have hcoL : c.CoL e d := by
    by_contra hn
    exact hvd (by
      rw [c.eq_of_not_coL hI.s55 hI.gamma2 hJ hze hzwd hn hwd (Ne.symm hzw) hve hvw]
      exact hzwd)
  have hvz : v ≠ z • w := hvzw.ne
  have hodd : Odd {p | c.OnL p d ∧ c.Delta.Adj v p}.ncard := by
    rcases (ρ.coL_iff_deltaAt hze hzwd).1 hcoL with h0 | h1 | h2
    · have hde : d = e := (ρ.mem_deltaAt_zero_iff hze hzwd).1 h0
      exact (hvd (by rw [hde]; exact hve)).elim
    · rw [c.stmt7_1_one hI.s54 hJ hze hve hvz h1]
      decide
    · have hset : {p | c.OnL p d ∧ c.Delta.Adj v p} = {p | c.OnL p d} :=
        Set.ext fun p => ⟨fun h => h.1, fun h => ⟨h, c.stmt7_1_two hI.s54 hJ hze hve hvz h2 h⟩⟩
      rw [hset, c.ncard_onL d]
      decide
  obtain ⟨p, ⟨hpd, hvp⟩, hzp⟩ := exists_fixed_pt_of_odd_ncard (Set.toFinite _) hodd (z • ·)
    (fun a => c.z_smul_smul hJ a) hmem
  by_cases hpy : p = y
  · rw [← hpy]
    exact hvp.symm
  · exact absurd (c.z_fix_all_of_fix hy hyd hpd hpy hwd hwy hzp) hzw

end B3a

section B3b


include ρ in
theorem z_smul_of_perp (hI : Sec7Inputs) (hJ : HypJ4 G z) {x a v : G ⧸ c.G1}
    (hx : c.OnP x c.pi0) (ha : c.OnP a c.pi0) (hxa : c.Delta.Adj x a) (hxv : c.Delta.Adj x v)
    (hav : Perp c.Delta a v) : z • v = v := by
  obtain ⟨n, hxn, hvn⟩ := c.exists_onL_of_adj hxv
  obtain ⟨l, hxl, hal⟩ := c.exists_onL_of_adj hxa
  have hlπ : c.LnP l c.pi0 := c.lnP_of_adj hI.gamma2 hJ hx ha hxa hxl hal
  refine (ρ.stmt7_8 hI hJ hx hxv hxn hvn).2 ⟨l, hxl, hlπ, ?_⟩
  rcases hav with hav | hav
  · have hln : l = n :=
      c.eq_of_onL hI.lineU hJ hxa.ne hxl hal hxn (by rw [hav]; exact hvn)
    exact ⟨c.pi0, hlπ, by rw [← hln]; exact hlπ⟩
  · obtain ⟨σ, hxσ, haσ, hvσ⟩ := hI.s55 G z hJ c x a v hxa hav hxv
    exact ⟨σ, c.lnP_of_adj hI.gamma2 hJ hxσ haσ hxa hxl hal,
      c.lnP_of_adj hI.gamma2 hJ hxσ hvσ hxv hxn hvn⟩

include ρ in
theorem b3_fixed (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y w : G ⧸ c.G1} {d : G ⧸ c.G2}
    (hx : c.OnP x c.pi0) (hy : c.OnP y c.pi0) (hxy : Dist2 c.Delta x y)
    (hyw : c.Delta.Adj y w) (hyd : c.OnL y d) (hwd : c.OnL w d) (hzw : z • w = w) :
    ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w := by
  obtain ⟨l, hyl, hlπ, hco⟩ := (ρ.stmt7_8 hI hJ hy hyw hyd hwd).1 hzw
  exact ρ.exists_pt_of_coL hI hJ hxy hx hy hyd hwd hyw.ne.symm hyl hlπ hco

end B3b

section B3c


include ρ in
theorem b3_moved (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y w : G ⧸ c.G1} {d : G ⧸ c.G2}
    (hx : c.OnP x c.pi0) (hy : c.OnP y c.pi0) (hxy : Dist2 c.Delta x y) (hxw : Dist2 c.Delta x w)
    (hyd : c.OnL y d) (hwd : c.OnL w d) (hwy : w ≠ y) (hzw : z • w ≠ w) :
    ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w := by
  obtain ⟨u, hxu, huw⟩ := hxw.2.2
  obtain ⟨a, v, hxa, hya, hcomp, hav⟩ := ρ.stmt7_6_two hI hJ hxy ⟨c.pi0, hx, hy⟩ hxw hxu huw
  obtain ⟨-, ⟨hxv, hwv⟩, -⟩ := hcomp
  have haπ : c.OnP a c.pi0 := c.stmt7_5_two hI hJ hxy hx hy hxa hya
  have hzv : z • v = v := ρ.z_smul_of_perp hI hJ hx haπ hxa hxv hav
  refine ⟨v, hxv, ?_, Or.inr hwv.symm⟩
  by_cases hvd : c.OnL v d
  · have hvy : v ≠ y := fun h => hxy.2.1 (by rw [← h]; exact hxv)
    exact c.adj_of_onL hvy.symm hyd hvd
  · exact ρ.adj_of_z_fix hI hJ hy hyd hwd hwy hzw hwv hvd hzv

include ρ in
theorem b3_core (hI : Sec7Inputs) (hJ : HypJ4 G z) {x y w : G ⧸ c.G1} (hx : c.OnP x c.pi0)
    (hy : c.OnP y c.pi0) (hxy : Dist2 c.Delta x y) (hyw : c.Delta.Adj y w)
    (hxw : Dist2 c.Delta x w) :
    ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w := by
  obtain ⟨d, hyd, hwd⟩ := c.exists_onL_of_adj hyw
  by_cases hzw : z • w = w
  · exact ρ.b3_fixed hI hJ hx hy hxy hyw hyd hwd hzw
  · exact ρ.b3_moved hI hJ hx hy hxy hxw hyd hwd hyw.ne.symm hzw

include ρ in
theorem hypB3 (hI : Sec7Inputs) (hJ : HypJ4 G z) :
    ∀ x y w, induced c.Delta c.Rh 1 x y → Dist2 c.Delta x y → c.Delta.Adj y w →
      Dist2 c.Delta x w → ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w := by
  intro x y w hind hxy hyw hxw
  obtain ⟨π, hxπ, hyπ⟩ : ∃ π, c.OnP x π ∧ c.OnP y π := by
    rcases hind with hp | ⟨u, hu⟩
    · rcases hp with h | h
      · exact absurd h hxy.1
      · exact absurd h hxy.2.1
    · rcases c.rh_one_iff.1 hu with ⟨-, -, hxy'⟩ | ⟨-, -, -, m, n, -, hxm, -, hyn, σ, hmσ, hnσ⟩
      · exact absurd hxy' hxy.2.1
      · exact ⟨σ, c.inc_pt_plane hxm hmσ, c.inc_pt_plane hyn hnσ⟩
  obtain ⟨g, -, hgπ⟩ := c.exists_frameP hxπ
  have hP : ∀ {a : G ⧸ c.G1}, c.OnP a π → c.OnP (g⁻¹ • a) c.pi0 := fun {a} ha =>
    (cInc_inv_smul_iff' c.G1 c.G3 g a c.pi0).2 (by rw [hgπ]; exact ha)
  obtain ⟨a, ha1, ha2, ha3⟩ := ρ.b3_core hI hJ (hP hxπ) (hP hyπ)
    ((c.dist2_smul_iff g⁻¹).2 hxy) ((c.adj_smul_iff g⁻¹).2 hyw) ((c.dist2_smul_iff g⁻¹).2 hxw)
  refine ⟨g • a, ?_, ?_, ?_⟩
  · have h := (c.adj_smul_iff g).2 ha1
    rwa [smul_inv_smul] at h
  · have h := (c.adj_smul_iff g).2 ha2
    rwa [smul_inv_smul] at h
  · have h := (c.perp_smul_iff g).2 ha3
    rwa [smul_inv_smul] at h

end B3c

end ResM24

section Main


theorem stmt7_9_holds (hI : Sec7Inputs)
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c)) : Stmt7_9 :=
  stmt7_9_of_hypB fun G _ _ z hJ c => by
    obtain ⟨ρ⟩ := hres G z hJ c
    exact ⟨3, c.Rh, ρ.hypB_of (ρ.hypB2 hI hJ) (ρ.hypB3 hI hJ)⟩

end Main

end CFSG.Quasithin.H13.AS91
