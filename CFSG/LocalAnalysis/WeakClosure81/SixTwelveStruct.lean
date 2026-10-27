module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s612_SixTwelveStruct_le_normalizer_of_conj {X S : Subgroup G}
    (h : ∀ x ∈ X, ∀ s ∈ S, x * s * x⁻¹ ∈ S) : X ≤ normalizer (S : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact h x hx s
  · intro hs
    have h2 := h x⁻¹ (X.inv_mem hx) (x * s * x⁻¹) hs
    rwa [show x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s by group] at h2

private theorem s612_SixTwelveStruct_KOf_le_LOf (M V : Subgroup G) (g : G) :
    KOf M V g ≤ LOf V g := by
  unfold KOf LOf UOf BOf
  exact sup_le_sup inf_le_left inf_le_left

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem elemAbelian_conj (h : Hyp612Sym n M V g) : IsElemAbelian 2 (conjSubgroup V g) :=
  CFSG.Quasithin.E3.isElemAbelian_conjSubgroup h.elemAbelian g

theorem commutator_mem_U (h : Hyp612Sym n M V g) {b v : G} (hb : b ∈ BOf M V g) (hv : v ∈ V) :
    ⁅v, b⁆ ∈ UOf M V g := by
  by_cases hbV : b ∈ V
  · have h1 : ⁅v, b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (h.elemAbelian.comm hv hbV)
    rw [h1]
    exact (UOf M V g).one_mem
  · have hbN : b ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hb.2
    have hb2 : b ^ 2 = 1 := (elemAbelian_conj h).2 b hb.1
    have hb2' : b * b = 1 := by simpa [pow_two] using hb2
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2'
    have hbuV : b * v⁻¹ * b⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hbN v⁻¹).1 (V.inv_mem hv)
    have hcV : ⁅v, b⁆ ∈ V := by
      rw [commutatorElement_def,
        show v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) by group]
      exact V.mul_mem hv hbuV
    have hc2 : ⁅v, b⁆ ^ 2 = 1 := h.elemAbelian.2 _ hcV
    have hc2' : ⁅v, b⁆ * ⁅v, b⁆ = 1 := by simpa [pow_two] using hc2
    have hcinv : ⁅v, b⁆⁻¹ = ⁅v, b⁆ := inv_eq_of_mul_eq_one_left hc2'
    have hc_inv : ⁅v, b⁆⁻¹ = b * v * b⁻¹ * v⁻¹ := by
      rw [commutatorElement_inv, commutatorElement_def]
    have hbc_inv : b * ⁅v, b⁆ * b⁻¹ = ⁅v, b⁆⁻¹ := by
      calc b * ⁅v, b⁆ * b⁻¹
          = b * (v * b * v⁻¹ * b⁻¹) * b⁻¹ := by rw [commutatorElement_def]
        _ = b * v * b * v⁻¹ * (b⁻¹ * b⁻¹) := by group
        _ = b * v * b * v⁻¹ := by rw [hbinv, hb2', mul_one]
        _ = ⁅v, b⁆⁻¹ := by rw [hc_inv, hbinv]
    have hbc : b * ⁅v, b⁆ * b⁻¹ = ⁅v, b⁆ := by rw [hbc_inv, hcinv]
    have hbcb : b * ⁅v, b⁆ = ⁅v, b⁆ * b := mul_inv_eq_iff_eq_mul.mp hbc
    have hcomm : ⁅⁅v, b⁆, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hbcb.symm
    have hcMg : ⁅v, b⁆ ∈ conjSubgroup M g :=
      h.mem_of_commutator_mem b hb hbV ⁅v, b⁆ hcV (by
        rw [hcomm]
        exact Subgroup.mem_inf.2 ⟨V.one_mem, (conjSubgroup V g).one_mem⟩)
    exact Subgroup.mem_inf.2 ⟨hcV, hcMg⟩

theorem commutator_mem_B (h : Hyp612Sym n M V g) {a w : G} (ha : a ∈ UOf M V g)
    (hw : w ∈ conjSubgroup V g) : ⁅w, a⁆ ∈ BOf M V g := by
  have ha' : a ∈ BOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by rwa [BOf_swap]
  have h' := (h.swap).commutator_mem_U (b := a) (v := w) ha' hw
  rwa [UOf_swap] at h'

theorem commutator_mem_N (h : Hyp612Sym n M V g) {u b : G} (hu : u ∈ UOf M V g)
    (hb : b ∈ BOf M V g) : ⁅u, b⁆ ∈ NOf M V g := by
  have hcU : ⁅u, b⁆ ∈ UOf M V g := commutator_mem_U h hb hu.1
  have hcB : ⁅u, b⁆ ∈ BOf M V g := by
    have h1 : ⁅b, u⁆ ∈ BOf M V g := commutator_mem_B h hu hb.1
    have h2 : ⁅b, u⁆⁻¹ ∈ BOf M V g := (BOf M V g).inv_mem h1
    rwa [commutatorElement_inv b u] at h2
  rw [NOf, Subgroup.mem_inf]
  exact ⟨hcU, hcB⟩

theorem mul_comm_of_mem_NOf (h : Hyp612Sym n M V g) {x l : G} (hx : x ∈ NOf M V g)
    (hl : l ∈ LOf V g) : x * l = l * x := by
  have hxV : x ∈ V := by
    have := hx; rw [h.NOf_eq_inf, Subgroup.mem_inf] at this; exact this.1
  have hxVg : x ∈ conjSubgroup V g := by
    have := hx; rw [h.NOf_eq_inf, Subgroup.mem_inf] at this; exact this.2
  have hVc : V ≤ centralizer ({x} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h.elemAbelian.comm hxV hv
  have hVgc : conjSubgroup V g ≤ centralizer ({x} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (elemAbelian_conj h).comm hxVg hw
  have hl' : l ∈ centralizer ({x} : Set G) := by
    rw [LOf] at hl
    exact (sup_le hVc hVgc) hl
  exact Subgroup.mem_centralizer_iff.1 hl' x (Set.mem_singleton x)

theorem mem_KOf_iff (h : Hyp612Sym n M V g) {x : G} :
    x ∈ KOf M V g ↔ ∃ u ∈ UOf M V g, ∃ b ∈ BOf M V g, x = u * b := by
  have hconj_mem : ∀ b ∈ BOf M V g, ∀ u ∈ UOf M V g,
      b * u * b⁻¹ ∈ UOf M V g := by
    intro b hb u hu
    have hN : ⁅u, b⁆ ∈ NOf M V g := commutator_mem_N h hu hb
    have hcU : ⁅b, u⁆ ∈ UOf M V g := by
      have h1 : ⁅u, b⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem hN
      have h2 : ⁅u, b⁆⁻¹ ∈ UOf M V g := by
        have := h1; rw [NOf, Subgroup.mem_inf] at this; exact this.1
      rwa [commutatorElement_inv u b] at h2
    have hbub : b * u * b⁻¹ = ⁅b, u⁆ * u := by rw [commutatorElement_def]; group
    rw [hbub]
    exact (UOf M V g).mul_mem hcU hu
  have hBU : BOf M V g ≤ normalizer (UOf M V g : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hconj_mem b hb u
    · intro hbu
      have hb' : b⁻¹ ∈ BOf M V g := (BOf M V g).inv_mem hb
      have hmem : b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ ∈ UOf M V g :=
        hconj_mem b⁻¹ hb' (b * u * b⁻¹) hbu
      rwa [show b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ = u by group] at hmem
  have hcoe : ((UOf M V g ⊔ BOf M V g : Subgroup G) : Set G) =
      (UOf M V g : Set G) * (BOf M V g : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (UOf M V g) (BOf M V g) hBU
  constructor
  · intro hx
    have hx' : x ∈ ((UOf M V g ⊔ BOf M V g : Subgroup G) : Set G) := by
      change x ∈ (UOf M V g ⊔ BOf M V g : Subgroup G) at hx
      exact hx
    rw [hcoe, Set.mem_mul] at hx'
    obtain ⟨u, hu, b, hb, hxub⟩ := hx'
    exact ⟨u, hu, b, hb, hxub.symm⟩
  · rintro ⟨u, hu, b, hb, rfl⟩
    exact (KOf M V g).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hb)

theorem V_inf_KOf (h : Hyp612Sym n M V g) : V ⊓ KOf M V g = UOf M V g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxK⟩ := hx
    obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hxK
    have huV : u ∈ V := hu.1
    have hbV : b ∈ V := by
      have h1 : u⁻¹ * (u * b) ∈ V := V.mul_mem (V.inv_mem huV) hxV
      simpa using h1
    have hbN : b ∈ NOf M V g := by
      rw [h.NOf_eq_inf, Subgroup.mem_inf]
      exact ⟨hbV, hb.1⟩
    have hbU : b ∈ UOf M V g := by
      have := hbN; rw [NOf, Subgroup.mem_inf] at this; exact this.1
    exact (UOf M V g).mul_mem hu hbU
  · exact le_inf inf_le_left (by rw [KOf]; exact le_sup_left)

theorem conjV_inf_KOf (h : Hyp612Sym n M V g) : conjSubgroup V g ⊓ KOf M V g = BOf M V g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxVg, hxK⟩ := hx
    obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hxK
    have hbVg : b ∈ conjSubgroup V g := hb.1
    have huVg : u ∈ conjSubgroup V g := by
      have h1 : (u * b) * b⁻¹ ∈ conjSubgroup V g :=
        (conjSubgroup V g).mul_mem hxVg ((conjSubgroup V g).inv_mem hbVg)
      simpa using h1
    have huV : u ∈ V := hu.1
    have huN : u ∈ NOf M V g := by
      rw [h.NOf_eq_inf, Subgroup.mem_inf]
      exact ⟨huV, huVg⟩
    have huB : u ∈ BOf M V g := by
      have := huN; rw [NOf, Subgroup.mem_inf] at this; exact this.2
    exact (BOf M V g).mul_mem huB hb
  · exact le_inf inf_le_left (by rw [KOf]; exact le_sup_right)

theorem LOf_le_normalizer_KOf (h : Hyp612Sym n M V g) :
    LOf V g ≤ normalizer ((KOf M V g : Subgroup G) : Set G) := by
  have hVK : V ≤ normalizer ((KOf M V g : Subgroup G) : Set G) := by
    refine s612_SixTwelveStruct_le_normalizer_of_conj ?_
    intro v hv x hx
    obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hx
    have huV : u ∈ V := hu.1
    have hcU : ⁅v, b⁆ ∈ UOf M V g := commutator_mem_U h hb hv
    have hvu : v * u * v⁻¹ = u := by rw [h.elemAbelian.comm hv huV]; group
    have hvb : v * b * v⁻¹ = ⁅v, b⁆ * b := by rw [commutatorElement_def]; group
    have hvk : v * (u * b) * v⁻¹ = u * (⁅v, b⁆ * b) := by
      rw [show v * (u * b) * v⁻¹ = (v * u * v⁻¹) * (v * b * v⁻¹) by group, hvu, hvb]
    rw [hvk]
    exact (KOf M V g).mul_mem (Subgroup.mem_sup_left hu)
      ((KOf M V g).mul_mem (Subgroup.mem_sup_left hcU) (Subgroup.mem_sup_right hb))
  have hVgK : conjSubgroup V g ≤ normalizer ((KOf M V g : Subgroup G) : Set G) := by
    refine s612_SixTwelveStruct_le_normalizer_of_conj ?_
    intro w hw x hx
    obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hx
    have hbVg : b ∈ conjSubgroup V g := hb.1
    have hcB : ⁅w, u⁆ ∈ BOf M V g := commutator_mem_B h hu hw
    have hwb : w * b * w⁻¹ = b := by rw [(elemAbelian_conj h).comm hw hbVg]; group
    have hwu : w * u * w⁻¹ = ⁅w, u⁆ * u := by rw [commutatorElement_def]; group
    have hwk : w * (u * b) * w⁻¹ = (⁅w, u⁆ * u) * b := by
      rw [show w * (u * b) * w⁻¹ = (w * u * w⁻¹) * (w * b * w⁻¹) by group, hwu, hwb]
    rw [hwk]
    exact (KOf M V g).mul_mem
      ((KOf M V g).mul_mem (Subgroup.mem_sup_right hcB) (Subgroup.mem_sup_left hu))
      (Subgroup.mem_sup_right hb)
  rw [LOf]
  exact sup_le hVK hVgK

theorem normal_KOf (h : Hyp612Sym n M V g) : ((KOf M V g).subgroupOf (LOf V g)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (s612_SixTwelveStruct_KOf_le_LOf M V g)).2
    (LOf_le_normalizer_KOf h)

theorem commutator_KOf_KOf_mem_N (h : Hyp612Sym n M V g) {k k' : G} (hk : k ∈ KOf M V g)
    (hk' : k' ∈ KOf M V g) : ⁅k, k'⁆ ∈ NOf M V g := by
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hk
  obtain ⟨u', hu', b', hb', rfl⟩ := (mem_KOf_iff h).1 hk'
  have huV : u ∈ V := hu.1
  have hu'V : u' ∈ V := hu'.1
  have hbVg : b ∈ conjSubgroup V g := hb.1
  have hb'Vg : b' ∈ conjSubgroup V g := hb'.1
  have huL : u ∈ LOf V g := by rw [LOf]; exact Subgroup.mem_sup_left huV
  have hu'L : u' ∈ LOf V g := by rw [LOf]; exact Subgroup.mem_sup_left hu'V
  have hn1 : ⁅b, u'⁆ ∈ NOf M V g := by
    have h1 : ⁅u', b⁆ ∈ NOf M V g := commutator_mem_N h hu' hb
    have h2 : ⁅u', b⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem h1
    rwa [commutatorElement_inv u' b] at h2
  have hn2 : ⁅u, b'⁆ ∈ NOf M V g := commutator_mem_N h hu hb'
  have hbb' : ⁅b, b'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 ((elemAbelian_conj h).comm hbVg hb'Vg)
  have huu' : ⁅u, u'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (h.elemAbelian.comm huV hu'V)
  have hc1 : u * ⁅b, u'⁆ * u⁻¹ = ⁅b, u'⁆ := by
    rw [← mul_comm_of_mem_NOf h hn1 huL]; group
  have hc2 : u' * ⁅u, b'⁆ * u'⁻¹ = ⁅u, b'⁆ := by
    rw [← mul_comm_of_mem_NOf h hn2 hu'L]; group
  have hbck : ⁅b, u' * b'⁆ = ⁅b, u'⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hbb']
    group
  have huck : ⁅u, u' * b'⁆ = ⁅u, b'⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, huu', one_mul]
    exact hc2
  have hmain : ⁅u * b, u' * b'⁆ = ⁅b, u'⁆ * ⁅u, b'⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hbck, hc1, huck]
  rw [hmain]
  exact (NOf M V g).mul_mem hn1 hn2

theorem mem_UOf_of_commutator_mem_N (h : Hyp612Sym n M V g) {v k : G} (hv : v ∈ V)
    (hvU : v ∉ UOf M V g) (hk : k ∈ KOf M V g) (hc : ⁅k, v⁆ ∈ NOf M V g) :
    k ∈ UOf M V g := by
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hk
  have huV : u ∈ V := hu.1
  have hcU : ⁅v, b⁆ ∈ UOf M V g := commutator_mem_U h hb hv
  have hbvV : ⁅b, v⁆ ∈ V := by
    have h1 : ⁅v, b⁆⁻¹ ∈ UOf M V g := (UOf M V g).inv_mem hcU
    have h2 : ⁅v, b⁆⁻¹ ∈ V := by
      have := h1; rw [UOf, Subgroup.mem_inf] at this; exact this.1
    rwa [commutatorElement_inv v b] at h2
  have huv : ⁅u, v⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (h.elemAbelian.comm huV hv)
  have hconj : u * ⁅b, v⁆ * u⁻¹ = ⁅b, v⁆ := by
    rw [h.elemAbelian.comm huV hbvV]; group
  have hkv : ⁅u * b, v⁆ = ⁅b, v⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, huv, mul_one, hconj]
  have hcvbN : ⁅v, b⁆ ∈ NOf M V g := by
    have h1 : ⁅u * b, v⁆ ∈ NOf M V g := hc
    rw [hkv] at h1
    have h2 : ⁅b, v⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem h1
    rwa [commutatorElement_inv b v] at h2
  have hcvb_inf : ⁅v, b⁆ ∈ V ⊓ conjSubgroup V g := by
    rw [← h.NOf_eq_inf]
    exact hcvbN
  by_cases hbV : b ∈ V
  · have hbN : b ∈ NOf M V g := by
      rw [h.NOf_eq_inf, Subgroup.mem_inf]
      exact ⟨hbV, hb.1⟩
    have hbU : b ∈ UOf M V g := by
      have := hbN; rw [NOf, Subgroup.mem_inf] at this; exact this.1
    exact (UOf M V g).mul_mem hu hbU
  · exact absurd (Subgroup.mem_inf.2
      ⟨hv, h.mem_of_commutator_mem b hb hbV v hv hcvb_inf⟩) hvU

theorem mem_BOf_of_commutator_mem_N (h : Hyp612Sym n M V g) {w k : G}
    (hw : w ∈ conjSubgroup V g) (hwB : w ∉ BOf M V g) (hk : k ∈ KOf M V g)
    (hc : ⁅k, w⁆ ∈ NOf M V g) : k ∈ BOf M V g := by
  have hw' : w ∉ UOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by rwa [UOf_swap]
  have hk' : k ∈ KOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by rwa [KOf_swap]
  have hc' : ⁅k, w⁆ ∈ NOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by rwa [NOf_swap]
  have h' := (h.swap).mem_UOf_of_commutator_mem_N (v := w) (k := k) hw hw' hk' hc'
  rwa [UOf_swap] at h'

end Hyp612Sym

end CFSG.LocalAnalysis.WeakClosure81
