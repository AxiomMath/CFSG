module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveStar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def centralizerMod (S T Q : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ S ∧ x ∈ normalizer (Q : Set G) ∧ ∀ k ∈ T, ⁅k, x⁆ ∈ Q}
  one_mem' := ⟨S.one_mem, (normalizer (Q : Set G)).one_mem, fun k _ => by
    rw [commutatorElement_one_right]
    exact Q.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxS, hxN, hxc⟩ ⟨hyS, hyN, hyc⟩
    refine ⟨S.mul_mem hxS hyS, (normalizer (Q : Set G)).mul_mem hxN hyN, fun k hk => ?_⟩
    have e : ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem (hxc k hk) ((Subgroup.mem_normalizer_iff.1 hxN _).1 (hyc k hk))
  inv_mem' := by
    rintro x ⟨hxS, hxN, hxc⟩
    refine ⟨S.inv_mem hxS, (normalizer (Q : Set G)).inv_mem hxN, fun k hk => ?_⟩
    have e : ⁅k, x⁻¹⁆ = x⁻¹ * ⁅k, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 ((normalizer (Q : Set G)).inv_mem hxN) _).1
      (Q.inv_mem (hxc k hk))

theorem mem_centralizerMod {S T Q : Subgroup G} {x : G} :
    x ∈ centralizerMod S T Q ↔ x ∈ S ∧ x ∈ normalizer (Q : Set G) ∧ ∀ k ∈ T, ⁅k, x⁆ ∈ Q :=
  Iff.rfl

@[expose] def CKOf (M V : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod (LOf V g) (KOf M V g) (NOf M V g)

@[expose] def EOf (M V : Subgroup G) (g : G) : Subgroup G :=
  centralizerMod (LOf V g) (KOf M V g) (BOf M V g) ⊓
    centralizerMod (LOf V g) (BOf M V g) (NOf M V g)

theorem CKOf_swap (M V : Subgroup G) (g : G) :
    CKOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ = CKOf M V g := by
  unfold CKOf
  rw [LOf_swap, KOf_swap, NOf_swap]

theorem CKOf_le_LOf (M V : Subgroup G) (g : G) : CKOf M V g ≤ LOf V g := fun _ hx => hx.1

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

private theorem c612_SixTwelveCent_KOf_le_LOf (M V : Subgroup G) (g : G) :
    KOf M V g ≤ LOf V g := by
  unfold KOf LOf UOf BOf
  exact sup_le_sup inf_le_left inf_le_left

private theorem c612_SixTwelveCent_conj_eq_of_mem_NOf {m y : G} (h : Hyp612Sym n M V g)
    (hm : m ∈ NOf M V g) (hy : y ∈ LOf V g) : y * m * y⁻¹ = m := by
  have hc := mul_comm_of_mem_NOf h hm hy
  rw [← hc]
  group

private theorem c612_SixTwelveCent_mem_normalizer_NOf {x : G} (h : Hyp612Sym n M V g)
    (hx : x ∈ LOf V g) : x ∈ normalizer ((NOf M V g : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    rw [c612_SixTwelveCent_conj_eq_of_mem_NOf h hm hx]
    exact hm
  · intro hm
    have h1 : x⁻¹ * (x * m * x⁻¹) * x = x * m * x⁻¹ := by
      rw [show x⁻¹ * (x * m * x⁻¹) * x = x⁻¹ * (x * m * x⁻¹) * (x⁻¹)⁻¹ by group]
      exact c612_SixTwelveCent_conj_eq_of_mem_NOf h hm ((LOf V g).inv_mem hx)
    have h2 : x⁻¹ * (x * m * x⁻¹) * x ∈ NOf M V g := by rw [h1]; exact hm
    have h3 : m = x⁻¹ * (x * m * x⁻¹) * x := by group
    rw [h3]
    exact h2

private theorem c612_SixTwelveCent_mem_normalizer_BOf {x : G} (h : Hyp612Sym n M V g)
    (hx : x ∈ LOf V g) (hxB : ∀ b ∈ BOf M V g, ⁅b, x⁆ ∈ NOf M V g) :
    x ∈ normalizer ((BOf M V g : Subgroup G) : Set G) := by
  have hforward : ∀ s ∈ BOf M V g, x * s * x⁻¹ ∈ BOf M V g := by
    intro s hs
    have h1 : ⁅s, x⁆ ∈ NOf M V g := hxB s hs
    have hs' : ⁅x, s⁆ ∈ BOf M V g := by
      have h4 := (NOf M V g).inv_mem h1
      rw [NOf, Subgroup.mem_inf] at h4
      have h5 : ⁅s, x⁆⁻¹ ∈ BOf M V g := h4.2
      rwa [commutatorElement_inv s x] at h5
    have hxs : x * s * x⁻¹ = ⁅x, s⁆ * s := by rw [commutatorElement_def]; group
    rw [hxs]
    exact (BOf M V g).mul_mem hs' hs
  have hreverse : ∀ s ∈ BOf M V g, x⁻¹ * s * x ∈ BOf M V g := by
    intro s hs
    have h1 : ⁅s, x⁆ ∈ NOf M V g := hxB s hs
    have hs' : ⁅x⁻¹, s⁆ ∈ BOf M V g := by
      have h2 : ⁅x⁻¹, s⁆ = x⁻¹ * ⁅s, x⁆ * x := commutatorElement_inv_left x s
      rw [h2]
      have hcen : x⁻¹ * ⁅s, x⁆ * x = ⁅s, x⁆ := by
        rw [show x⁻¹ * ⁅s, x⁆ * x = x⁻¹ * (⁅s, x⁆ * x) by group,
          mul_comm_of_mem_NOf h h1 hx]
        group
      rw [hcen]
      have h4 := h1
      rw [NOf, Subgroup.mem_inf] at h4
      exact h4.2
    have hxs : x⁻¹ * s * x = ⁅x⁻¹, s⁆ * s := by rw [commutatorElement_def]; group
    rw [hxs]
    exact (BOf M V g).mul_mem hs' hs
  rw [Subgroup.mem_normalizer_iff]
  intro s
  exact ⟨hforward s, fun hs => by
    have h := hreverse (x * s * x⁻¹) hs
    rwa [show x⁻¹ * (x * s * x⁻¹) * x = s by group] at h⟩

theorem mem_CKOf_iff (h : Hyp612Sym n M V g) {x : G} :
    x ∈ CKOf M V g ↔ x ∈ LOf V g ∧ ∀ k ∈ KOf M V g, ⁅k, x⁆ ∈ NOf M V g := by
  refine ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, ?_, hx.2⟩⟩
  rw [Subgroup.mem_normalizer_iff]
  intro m
  have hc : ∀ m ∈ NOf M V g, x * m * x⁻¹ = m := fun m hm => by
    rw [← mul_comm_of_mem_NOf h hm hx.1]
    group
  constructor
  · intro hm
    rw [hc m hm]
    exact hm
  · intro hm
    have hm' : m ∈ NOf M V g := by
      have h1 : x⁻¹ * (x * m * x⁻¹) * x = m := by group
      rw [← h1]
      have hxinv : ∀ m' ∈ NOf M V g, x⁻¹ * m' * x = m' := fun m' hm' => by
        rw [← mul_comm_of_mem_NOf h hm' ((LOf V g).inv_mem hx.1)]
        group
      rw [hxinv _ hm]
      exact hm
    exact hm'

theorem KOf_le_CKOf (h : Hyp612Sym n M V g) : KOf M V g ≤ CKOf M V g := by
  intro k hk
  rw [mem_CKOf_iff h]
  exact ⟨c612_SixTwelveCent_KOf_le_LOf M V g hk,
    fun k' hk' => commutator_KOf_KOf_mem_N h hk' hk⟩

theorem LOf_le_normalizer_CKOf (h : Hyp612Sym n M V g) :
    LOf V g ≤ normalizer ((CKOf M V g : Subgroup G) : Set G) := by
  have hconj : ∀ l ∈ LOf V g, ∀ x ∈ CKOf M V g, l * x * l⁻¹ ∈ CKOf M V g := by
    intro l hl x hx
    rw [mem_CKOf_iff h] at hx ⊢
    obtain ⟨hxL, hxN⟩ := hx
    refine ⟨(LOf V g).mul_mem ((LOf V g).mul_mem hl hxL) ((LOf V g).inv_mem hl), ?_⟩
    intro k hk
    have hk' : l⁻¹ * k * l ∈ KOf M V g := by
      have h0 := (Subgroup.mem_normalizer_iff.1
        (LOf_le_normalizer_KOf h ((LOf V g).inv_mem hl)) k).1 hk
      simpa using h0
    have hn := hxN _ hk'
    have hcomm : ⁅k, l * x * l⁻¹⁆ = l * ⁅l⁻¹ * k * l, x⁆ * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hcomm]
    have hconjn : l * ⁅l⁻¹ * k * l, x⁆ * l⁻¹ = ⁅l⁻¹ * k * l, x⁆ := by
      rw [← mul_comm_of_mem_NOf h hn hl]
      group
    rw [hconjn]
    exact hn
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconj l hl x, fun hx => by
    have h := hconj l⁻¹ ((LOf V g).inv_mem hl) (l * x * l⁻¹) hx
    rwa [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group] at h⟩

theorem commutator_KOf_V_mem_U (h : Hyp612Sym n M V g) {k v : G} (hk : k ∈ KOf M V g)
    (hv : v ∈ V) : ⁅k, v⁆ ∈ UOf M V g := by
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hk
  have huv : ⁅u, v⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (h.elemAbelian.comm hu.1 hv)
  have hbv : ⁅b, v⁆ ∈ UOf M V g := by
    have h1 : ⁅v, b⁆ ∈ UOf M V g := commutator_mem_U h hb hv
    have h2 := (UOf M V g).inv_mem h1
    rwa [commutatorElement_inv v b] at h2
  have hmain : ⁅u * b, v⁆ = u * ⁅b, v⁆ * u⁻¹ := by
    rw [commutatorElement_mul_left_eq_conj_mul, huv, mul_one]
  rw [hmain]
  exact (UOf M V g).mul_mem ((UOf M V g).mul_mem hu hbv) ((UOf M V g).inv_mem hu)

theorem commutator_KOf_conjV_mem_B (h : Hyp612Sym n M V g) {k w : G} (hk : k ∈ KOf M V g)
    (hw : w ∈ conjSubgroup V g) : ⁅k, w⁆ ∈ BOf M V g := by
  have h1 := (swap h).commutator_KOf_V_mem_U (k := k) (v := w) (by rwa [KOf_swap]) hw
  rwa [UOf_swap] at h1

theorem V_inf_CKOf (h : Hyp612Sym n M V g) : V ⊓ CKOf M V g = UOf M V g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxD⟩ := hx
    by_contra hxU
    obtain ⟨b, hbB, hbN⟩ := IsConcreteLE.exists_of_lt h.NOf_lt_BOf
    have hbK : b ∈ KOf M V g := by rw [KOf]; exact Subgroup.mem_sup_right hbB
    have hbc : ⁅b, x⁆ ∈ NOf M V g := ((mem_CKOf_iff h).1 hxD).2 b hbK
    have hbU : b ∈ UOf M V g := mem_UOf_of_commutator_mem_N h hxV hxU hbK hbc
    exact hbN (by rw [NOf]; exact Subgroup.mem_inf.2 ⟨hbU, hbB⟩)
  · intro x hx
    have hxV : x ∈ V := (inf_le_left : UOf M V g ≤ V) hx
    exact ⟨hxV, KOf_le_CKOf h (by rw [KOf]; exact Subgroup.mem_sup_left hx)⟩

theorem conjV_inf_CKOf (h : Hyp612Sym n M V g) : conjSubgroup V g ⊓ CKOf M V g = BOf M V g := by
  have h1 := (swap h).V_inf_CKOf
  rwa [CKOf_swap, UOf_swap] at h1

theorem CKOf_le_normalizer_UOf (h : Hyp612Sym n M V g) :
    CKOf M V g ≤ normalizer ((UOf M V g : Subgroup G) : Set G) := by
  have hstep : ∀ y ∈ CKOf M V g, ∀ u ∈ UOf M V g, y * u * y⁻¹ ∈ UOf M V g := by
    intro y hy u hu
    have huK : u ∈ KOf M V g := by rw [KOf]; exact Subgroup.mem_sup_left hu
    have hcN : ⁅u, y⁆ ∈ NOf M V g := ((mem_CKOf_iff h).1 hy).2 u huK
    have hcU : ⁅y, u⁆ ∈ UOf M V g := by
      have h1 : ⁅u, y⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem hcN
      have h2 := h1
      rw [NOf, Subgroup.mem_inf] at h2
      have h3 : ⁅u, y⁆⁻¹ ∈ UOf M V g := h2.1
      rwa [commutatorElement_inv u y] at h3
    have hyu : y * u * y⁻¹ = ⁅y, u⁆ * u := by rw [commutatorElement_def]; group
    rw [hyu]
    exact (UOf M V g).mul_mem hcU hu
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact ⟨hstep x hx u, fun h => by
    have h' := hstep x⁻¹ ((CKOf M V g).inv_mem hx) (x * u * x⁻¹) h
    rwa [show x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u by group] at h'⟩

theorem CKOf_le_M (h : Hyp612Sym n M V g) : CKOf M V g ≤ M :=
  h.CKOf_le_normalizer_UOf.trans h.normalizer_U_le

theorem commutator_CKOf_V_mem_U (h : Hyp612Sym n M V g) {x v : G} (hx : x ∈ CKOf M V g)
    (hv : v ∈ V) : ⁅x, v⁆ ∈ UOf M V g := by
  have hxN : x ∈ normalizer (V : Set G) := by
    rw [h.normalizer_eq]
    exact CKOf_le_M h hx
  have hxvV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxN v).1 hv
  have h1 : ⁅x, v⁆ ∈ V := by
    rw [commutatorElement_def]
    exact V.mul_mem hxvV (V.inv_mem hv)
  have hvL : v ∈ LOf V g := by rw [LOf]; exact Subgroup.mem_sup_left hv
  have hconj : v * x⁻¹ * v⁻¹ ∈ CKOf M V g :=
    (Subgroup.mem_normalizer_iff.1 (LOf_le_normalizer_CKOf h hvL) x⁻¹).1
      ((CKOf M V g).inv_mem hx)
  have h2 : ⁅x, v⁆ ∈ CKOf M V g := by
    have hh : x * (v * x⁻¹ * v⁻¹) ∈ CKOf M V g := (CKOf M V g).mul_mem hx hconj
    convert hh using 1
    group
  rw [← V_inf_CKOf h]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem commutator_CKOf_conjV_mem_B (h : Hyp612Sym n M V g) {x w : G} (hx : x ∈ CKOf M V g)
    (hw : w ∈ conjSubgroup V g) : ⁅x, w⁆ ∈ BOf M V g := by
  have h1 := (swap h).commutator_CKOf_V_mem_U (x := x) (v := w) (by rwa [CKOf_swap]) hw
  rwa [UOf_swap] at h1

theorem commutator_CKOf_LOf_mem_KOf (h : Hyp612Sym n M V g) {x l : G} (hx : x ∈ CKOf M V g)
    (hl : l ∈ LOf V g) : ⁅x, l⁆ ∈ KOf M V g := by
  have hV : V ≤ centralizerMod (LOf V g) (CKOf M V g) (KOf M V g) := by
    intro v hv
    refine mem_centralizerMod.2 ⟨?_, ?_, ?_⟩
    · rw [LOf]; exact Subgroup.mem_sup_left hv
    · exact LOf_le_normalizer_KOf h (by rw [LOf]; exact Subgroup.mem_sup_left hv)
    · intro d hd
      have hdU : ⁅d, v⁆ ∈ UOf M V g := commutator_CKOf_V_mem_U h hd hv
      rw [KOf]; exact Subgroup.mem_sup_left hdU
  have hVg : conjSubgroup V g ≤ centralizerMod (LOf V g) (CKOf M V g) (KOf M V g) := by
    intro w hw
    refine mem_centralizerMod.2 ⟨?_, ?_, ?_⟩
    · rw [LOf]; exact Subgroup.mem_sup_right hw
    · exact LOf_le_normalizer_KOf h (by rw [LOf]; exact Subgroup.mem_sup_right hw)
    · intro d hd
      have hdB : ⁅d, w⁆ ∈ BOf M V g := commutator_CKOf_conjV_mem_B h hd hw
      rw [KOf]; exact Subgroup.mem_sup_right hdB
  have hl' : l ∈ V ⊔ conjSubgroup V g := by rw [LOf] at hl; exact hl
  exact (mem_centralizerMod.1 ((sup_le hV hVg) hl')).2.2 x hx

theorem normalizer_UOf_of_commutator_mem_CKOf (h : Hyp612Sym n M V g) {a x : G} (ha : a ∈ V)
    (haU : a ∉ UOf M V g) (hx : x ∈ LOf V g) (hc : ⁅a, x⁆ ∈ CKOf M V g) :
    x ∈ normalizer ((UOf M V g : Subgroup G) : Set G) := by
  have hstep : ∀ y ∈ LOf V g, ⁅a, y⁆ ∈ CKOf M V g → ∀ u ∈ UOf M V g,
      y * u * y⁻¹ ∈ UOf M V g := by
    intro y hy hyc u hu
    have hkK : y * u * y⁻¹ ∈ KOf M V g := by
      have hyN : y ∈ normalizer ((KOf M V g : Subgroup G) : Set G) :=
        LOf_le_normalizer_KOf h hy
      exact (Subgroup.mem_normalizer_iff.1 hyN u).1
        (by rw [KOf]; exact Subgroup.mem_sup_left hu)
    have hcN : ⁅y * u * y⁻¹, ⁅a, y⁆⁆ ∈ NOf M V g :=
      ((mem_CKOf_iff h).1 hyc).2 (y * u * y⁻¹) hkK
    have hcy : ⁅a, y⁆ * y * a = a * y := by
      rw [commutatorElement_def]; group
    have havu : a * u * a⁻¹ = u := by
      rw [h.elemAbelian.comm ha hu.1]; group
    have hconj : a * (y * u * y⁻¹) * a⁻¹
        = ⁅a, y⁆ * (y * u * y⁻¹) * ⁅a, y⁆⁻¹ := by
      calc a * (y * u * y⁻¹) * a⁻¹
          = (a * y) * u * (a * y)⁻¹ := by group
        _ = (⁅a, y⁆ * y * a) * u * (⁅a, y⁆ * y * a)⁻¹ := by rw [← hcy]
        _ = ⁅a, y⁆ * (y * u * y⁻¹) * ⁅a, y⁆⁻¹ := by
              calc (⁅a, y⁆ * y * a) * u * (⁅a, y⁆ * y * a)⁻¹
                  = ⁅a, y⁆ * (y * (a * u * a⁻¹) * y⁻¹) * ⁅a, y⁆⁻¹ := by group
                _ = ⁅a, y⁆ * (y * u * y⁻¹) * ⁅a, y⁆⁻¹ := by rw [havu]
    have hak : a * (y * u * y⁻¹) * a⁻¹
        = ⁅⁅a, y⁆, y * u * y⁻¹⁆ * (y * u * y⁻¹) := by
      rw [hconj, commutatorElement_def]; group
    have hka : ⁅y * u * y⁻¹, a⁆ ∈ NOf M V g := by
      have h2 : ⁅y * u * y⁻¹, a⁆
          = (y * u * y⁻¹) * (a * (y * u * y⁻¹) * a⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [h2, hak]
      have h3 : (y * u * y⁻¹) * (⁅⁅a, y⁆, y * u * y⁻¹⁆ * (y * u * y⁻¹))⁻¹
          = ⁅⁅a, y⁆, y * u * y⁻¹⁆⁻¹ := by group
      rw [h3]
      rwa [commutatorElement_inv ⁅a, y⁆ (y * u * y⁻¹)]
    exact mem_UOf_of_commutator_mem_N h ha haU hkK hka
  have hxinv : x⁻¹ ∈ LOf V g := (LOf V g).inv_mem hx
  have hcx : ⁅a, x⁻¹⁆ ∈ CKOf M V g := by
    have h1 : x⁻¹ * ⁅a, x⁆ * x ∈ CKOf M V g := by
      have h0 := (Subgroup.mem_normalizer_iff.1
        (LOf_le_normalizer_CKOf h hxinv) ⁅a, x⁆).1 hc
      simpa using h0
    have h2 := (CKOf M V g).inv_mem h1
    convert h2 using 1
    rw [commutatorElement_def]; group
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact ⟨fun hu => hstep x hx hc u hu, fun hu' => by
    have h := hstep x⁻¹ hxinv hcx (x * u * x⁻¹) hu'
    rwa [show x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u by group] at h⟩

theorem mem_EOf_iff (h : Hyp612Sym n M V g) {x : G} :
    x ∈ EOf M V g ↔ x ∈ LOf V g ∧ (∀ b ∈ BOf M V g, ⁅b, x⁆ ∈ NOf M V g) ∧
      ∀ k ∈ KOf M V g, ⁅k, x⁆ ∈ BOf M V g := by
  constructor
  · intro hx
    rw [EOf] at hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxL, _, hxK⟩ := mem_centralizerMod.1 hx1
    obtain ⟨_, _, hxB⟩ := mem_centralizerMod.1 hx2
    exact ⟨hxL, hxB, hxK⟩
  · rintro ⟨hxL, hxB, hxK⟩
    have hxN : x ∈ normalizer ((NOf M V g : Subgroup G) : Set G) :=
      c612_SixTwelveCent_mem_normalizer_NOf h hxL
    have hxB' : x ∈ normalizer ((BOf M V g : Subgroup G) : Set G) :=
      c612_SixTwelveCent_mem_normalizer_BOf h hxL hxB
    rw [EOf]
    exact Subgroup.mem_inf.2 ⟨mem_centralizerMod.2 ⟨hxL, hxB', hxK⟩,
      mem_centralizerMod.2 ⟨hxL, hxN, hxB⟩⟩

theorem conjV_le_EOf (h : Hyp612Sym n M V g) : conjSubgroup V g ≤ EOf M V g := by
  intro w hw
  rw [mem_EOf_iff h]
  refine ⟨by rw [LOf]; exact Subgroup.mem_sup_right hw, ?_, ?_⟩
  · intro b hb
    have h1 : ⁅b, w⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 ((elemAbelian_conj h).comm hb.1 hw)
    rw [h1]
    exact (NOf M V g).one_mem
  · intro k hk
    exact commutator_KOf_conjV_mem_B h hk hw

theorem conjV_le_EOf_of_conj_UOf_eq (h : Hyp612Sym n M V g) {l : G} (hl : l ∈ LOf V g)
    (hB : BOf M V g = conjSubgroup (UOf M V g) l) : conjSubgroup V l ≤ EOf M V g := by
  have hVL : V ≤ LOf V g := by rw [LOf]; exact le_sup_left
  have hconjL : conjSubgroup V l ≤ LOf V g := by
    intro y hy
    have hyV : l * y * l⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
    have h1 : y = l⁻¹ * (l * y * l⁻¹) * l := by group
    rw [h1]
    exact (LOf V g).mul_mem ((LOf V g).mul_mem ((LOf V g).inv_mem hl) (hVL hyV)) hl
  intro x hx
  rw [mem_EOf_iff h]
  refine ⟨hconjL hx, ?_, ?_⟩
  · intro b hb
    have hbU : l * b * l⁻¹ ∈ UOf M V g := by
      have h := hb
      rw [hB] at h
      exact mem_conjSubgroup_iff.1 h
    have hxV : l * x * l⁻¹ ∈ V := mem_conjSubgroup_iff.1 hx
    have hcomm : ⁅l * b * l⁻¹, l * x * l⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2
        (h.elemAbelian.comm ((inf_le_left : UOf M V g ≤ V) hbU) hxV)
    have h1 : l * ⁅b, x⁆ * l⁻¹ = 1 := by
      rw [conjugate_commutatorElement]
      exact hcomm
    have h2 : ⁅b, x⁆ = 1 := by
      have h3 : l⁻¹ * (l * ⁅b, x⁆ * l⁻¹) * l = ⁅b, x⁆ := by group
      rw [h1] at h3
      simpa using h3.symm
    rw [h2]
    exact (NOf M V g).one_mem
  · intro k hk
    have hkK : l * k * l⁻¹ ∈ KOf M V g :=
      (Subgroup.mem_normalizer_iff.1 (LOf_le_normalizer_KOf h hl) k).1 hk
    have hxV : l * x * l⁻¹ ∈ V := mem_conjSubgroup_iff.1 hx
    have hcommU : ⁅l * k * l⁻¹, l * x * l⁻¹⁆ ∈ UOf M V g :=
      commutator_KOf_V_mem_U h hkK hxV
    have h1 : l * ⁅k, x⁆ * l⁻¹ ∈ UOf M V g := by
      rw [conjugate_commutatorElement]
      exact hcommU
    rw [hB]
    exact mem_conjSubgroup_iff.2 h1

theorem commutator_mem_CKOf_of_mem_EOf (h : Hyp612Sym n M V g) {e e' : G} (he : e ∈ EOf M V g)
    (he' : e' ∈ EOf M V g) : ⁅e, e'⁆ ∈ CKOf M V g := by
  have heL : e ∈ LOf V g := ((mem_EOf_iff h).1 he).1
  have heB : ∀ b ∈ BOf M V g, ⁅b, e⁆ ∈ NOf M V g := ((mem_EOf_iff h).1 he).2.1
  have heK : ∀ k ∈ KOf M V g, ⁅k, e⁆ ∈ BOf M V g := ((mem_EOf_iff h).1 he).2.2
  have he'L : e' ∈ LOf V g := ((mem_EOf_iff h).1 he').1
  have he'B : ∀ b ∈ BOf M V g, ⁅b, e'⁆ ∈ NOf M V g := ((mem_EOf_iff h).1 he').2.1
  have he'K : ∀ k ∈ KOf M V g, ⁅k, e'⁆ ∈ BOf M V g := ((mem_EOf_iff h).1 he').2.2
  have hrel : ∀ k ∈ KOf M V g, ∃ n ∈ NOf M V g,
      e * e' * k * (e * e')⁻¹ = n * (e' * e * k * (e' * e)⁻¹) := by
    intro k hk
    have hβB : ⁅e, k⁆ ∈ BOf M V g := by
      have h1 : ⁅k, e⁆ ∈ BOf M V g := heK k hk
      have h2 := (BOf M V g).inv_mem h1
      rwa [commutatorElement_inv k e] at h2
    have hβ'B : ⁅e', k⁆ ∈ BOf M V g := by
      have h1 : ⁅k, e'⁆ ∈ BOf M V g := he'K k hk
      have h2 := (BOf M V g).inv_mem h1
      rwa [commutatorElement_inv k e'] at h2
    have hn1 : ⁅e', ⁅e, k⁆⁆ ∈ NOf M V g := by
      have h1 : ⁅⁅e, k⁆, e'⁆ ∈ NOf M V g := he'B _ hβB
      have h2 := (NOf M V g).inv_mem h1
      rwa [commutatorElement_inv ⁅e,k⁆ e'] at h2
    have hn2 : ⁅e, ⁅e', k⁆⁆ ∈ NOf M V g := by
      have h1 : ⁅⁅e', k⁆, e⁆ ∈ NOf M V g := heB _ hβ'B
      have h2 := (NOf M V g).inv_mem h1
      rwa [commutatorElement_inv ⁅e',k⁆ e] at h2
    have hek : e * k * e⁻¹ = ⁅e, k⁆ * k := by rw [commutatorElement_def]; group
    have he'k : e' * k * e'⁻¹ = ⁅e', k⁆ * k := by rw [commutatorElement_def]; group
    have he'β : e' * ⁅e, k⁆ * e'⁻¹ = ⁅e', ⁅e, k⁆⁆ * ⁅e, k⁆ := by
      rw [commutatorElement_def]; group
    have heβ' : e * ⁅e', k⁆ * e⁻¹ = ⁅e, ⁅e', k⁆⁆ * ⁅e', k⁆ := by
      rw [commutatorElement_def]; group
    have hcalcA : e' * e * k * (e' * e)⁻¹
        = ⁅e', ⁅e,k⁆⁆ * (⁅e,k⁆ * ⁅e',k⁆) * k := by
      calc e' * e * k * (e' * e)⁻¹
          = e' * (e * k * e⁻¹) * e'⁻¹ := by group
        _ = e' * (⁅e,k⁆ * k) * e'⁻¹ := by rw [hek]
        _ = (e' * ⁅e,k⁆ * e'⁻¹) * (e' * k * e'⁻¹) := by group
        _ = (⁅e', ⁅e,k⁆⁆ * ⁅e,k⁆) * (⁅e',k⁆ * k) := by rw [he'β, he'k]
        _ = ⁅e', ⁅e,k⁆⁆ * (⁅e,k⁆ * ⁅e',k⁆) * k := by group
    have hcalcB : e * e' * k * (e * e')⁻¹
        = ⁅e, ⁅e',k⁆⁆ * (⁅e',k⁆ * ⁅e,k⁆) * k := by
      calc e * e' * k * (e * e')⁻¹
          = e * (e' * k * e'⁻¹) * e⁻¹ := by group
        _ = e * (⁅e',k⁆ * k) * e⁻¹ := by rw [he'k]
        _ = (e * ⁅e',k⁆ * e⁻¹) * (e * k * e⁻¹) := by group
        _ = (⁅e, ⁅e',k⁆⁆ * ⁅e',k⁆) * (⁅e,k⁆ * k) := by rw [heβ', hek]
        _ = ⁅e, ⁅e',k⁆⁆ * (⁅e',k⁆ * ⁅e,k⁆) * k := by group
    refine ⟨⁅e, ⁅e',k⁆⁆ * (⁅e', ⁅e,k⁆⁆)⁻¹,
      (NOf M V g).mul_mem hn2 ((NOf M V g).inv_mem hn1), ?_⟩
    rw [hcalcB, hcalcA]
    have hββ' : ⁅e',k⁆ * ⁅e,k⁆ = ⁅e,k⁆ * ⁅e',k⁆ :=
      (elemAbelian_conj h).comm hβ'B.1 hβB.1
    rw [hββ']
    group
  have hmain : ∀ k₀ ∈ KOf M V g, ⁅k₀, ⁅e, e'⁆⁆ ∈ NOf M V g := by
    intro k₀ hk₀
    have hL : e' * e ∈ LOf V g := (LOf V g).mul_mem he'L heL
    have hkK : (e' * e)⁻¹ * k₀ * (e' * e) ∈ KOf M V g := by
      have h0 := (Subgroup.mem_normalizer_iff.1
        (LOf_le_normalizer_KOf h ((LOf V g).inv_mem hL)) k₀).1 hk₀
      simpa using h0
    obtain ⟨n, hnN, hnEq⟩ := hrel _ hkK
    have hc_eq : e * e' * ((e' * e)⁻¹ * k₀ * (e' * e)) * (e * e')⁻¹
        = ⁅e, e'⁆ * k₀ * ⁅e, e'⁆⁻¹ := by
      rw [commutatorElement_def]; group
    have hinner : e' * e * ((e' * e)⁻¹ * k₀ * (e' * e)) * (e' * e)⁻¹ = k₀ := by group
    have hck : ⁅e, e'⁆ * k₀ * ⁅e, e'⁆⁻¹ = n * k₀ := by
      rw [hc_eq, hinner] at hnEq
      exact hnEq
    have h1 : ⁅⁅e, e'⁆, k₀⁆ ∈ NOf M V g := by
      rw [commutatorElement_def, hck]
      simpa using hnN
    have h2 := (NOf M V g).inv_mem h1
    rwa [commutatorElement_inv ⁅e,e'⁆ k₀] at h2
  rw [mem_CKOf_iff h]
  refine ⟨?_, hmain⟩
  exact (LOf V g).mul_mem ((LOf V g).mul_mem ((LOf V g).mul_mem heL he'L)
    ((LOf V g).inv_mem heL)) ((LOf V g).inv_mem he'L)

theorem mem_CKOf_of_mem_EOf_of_commutator_mem_KOf (h : Hyp612Sym n M V g) {e v : G}
    (he : e ∈ EOf M V g) (hv : v ∈ V) (hvU : v ∉ UOf M V g) (hc : ⁅e, v⁆ ∈ KOf M V g) :
    e ∈ CKOf M V g := by
  have heL : e ∈ LOf V g := ((mem_EOf_iff h).1 he).1
  have heB : ∀ b ∈ BOf M V g, ⁅b, e⁆ ∈ NOf M V g := ((mem_EOf_iff h).1 he).2.1
  have heK : ∀ k ∈ KOf M V g, ⁅k, e⁆ ∈ BOf M V g := ((mem_EOf_iff h).1 he).2.2
  have hUpart : ∀ u ∈ UOf M V g, ⁅u, e⁆ ∈ NOf M V g := by
    intro u hu
    have huK : u ∈ KOf M V g := by rw [KOf]; exact Subgroup.mem_sup_left hu
    have hβB : ⁅e, u⁆ ∈ BOf M V g := by
      have h1 : ⁅u, e⁆ ∈ BOf M V g := heK u huK
      have h2 := (BOf M V g).inv_mem h1
      rwa [commutatorElement_inv u e] at h2
    have hβK : ⁅e, u⁆ ∈ KOf M V g := by rw [KOf]; exact Subgroup.mem_sup_right hβB
    have hκK : ⁅v, e⁆ ∈ KOf M V g := by
      have h1 := (KOf M V g).inv_mem hc
      rwa [commutatorElement_inv e v] at h1
    have heu : e * u * e⁻¹ = ⁅e, u⁆ * u := by rw [commutatorElement_def]; group
    have hn' : ⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ ∈ NOf M V g :=
      commutator_KOf_KOf_mem_N h hκK ((KOf M V g).mul_mem hβK huK)
    have hfirst : v * (e * u * e⁻¹) * v⁻¹
        = ⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ * (⁅e, u⁆ * u) := by
      have hve : v * e * v⁻¹ = ⁅v, e⁆ * e := by rw [commutatorElement_def]; group
      have hvu : v * u * v⁻¹ = u := by rw [h.elemAbelian.comm hv hu.1]; group
      have h1a : v * (e * u * e⁻¹) * v⁻¹
          = (v * e * v⁻¹) * (v * u * v⁻¹) * (v * e * v⁻¹)⁻¹ := by group
      rw [h1a, hvu, hve]
      have h2 : (⁅v, e⁆ * e) * u * (⁅v, e⁆ * e)⁻¹
          = ⁅v, e⁆ * (e * u * e⁻¹) * ⁅v, e⁆⁻¹ := by group
      rw [h2, heu, commutatorElement_def]
      group
    have hsecond : v * (e * u * e⁻¹) * v⁻¹ = (v * ⁅e, u⁆ * v⁻¹) * u := by
      rw [heu]
      have hvu : v * u * v⁻¹ = u := by rw [h.elemAbelian.comm hv hu.1]; group
      calc v * (⁅e, u⁆ * u) * v⁻¹
          = (v * ⁅e, u⁆ * v⁻¹) * (v * u * v⁻¹) := by group
        _ = (v * ⁅e, u⁆ * v⁻¹) * u := by rw [hvu]
    have heq : ⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ * (⁅e, u⁆ * u) = (v * ⁅e, u⁆ * v⁻¹) * u := by
      rw [← hfirst, hsecond]
    have hvβ : v * ⁅e, u⁆ * v⁻¹ = ⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ * ⁅e, u⁆ := by
      have h2 : (⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ * ⁅e, u⁆) * u = (v * ⁅e, u⁆ * v⁻¹) * u := by
        rw [show (⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ * ⁅e, u⁆) * u
              = ⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ * (⁅e, u⁆ * u) by group]
        exact heq
      exact (mul_right_cancel h2).symm
    have hvβN : ⁅v, ⁅e, u⁆⁆ ∈ NOf M V g := by
      have h3 : ⁅v, ⁅e, u⁆⁆ = ⁅⁅v, e⁆, ⁅e, u⁆ * u⁆ := by
        rw [commutatorElement_def, hvβ]
        group
      rw [h3]
      exact hn'
    have hβvN : ⁅⁅e, u⁆, v⁆ ∈ NOf M V g := by
      have h1 := (NOf M V g).inv_mem hvβN
      rwa [commutatorElement_inv v ⁅e,u⁆] at h1
    have hβU : ⁅e, u⁆ ∈ UOf M V g :=
      mem_UOf_of_commutator_mem_N h hv hvU hβK hβvN
    have hβN : ⁅e, u⁆ ∈ NOf M V g := by
      rw [NOf]; exact Subgroup.mem_inf.2 ⟨hβU, hβB⟩
    have h1 := (NOf M V g).inv_mem hβN
    rwa [commutatorElement_inv e u] at h1
  rw [mem_CKOf_iff h]
  refine ⟨heL, ?_⟩
  intro k hk
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_KOf_iff h).1 hk
  have huL : u ∈ LOf V g := by rw [LOf]; exact Subgroup.mem_sup_left hu.1
  have hbeN : ⁅b, e⁆ ∈ NOf M V g := heB b hb
  have hcomm : ⁅u * b, e⁆ = u * ⁅b, e⁆ * u⁻¹ * ⁅u, e⁆ :=
    commutatorElement_mul_left_eq_conj_mul u b e
  rw [hcomm]
  have h1 : u * ⁅b, e⁆ * u⁻¹ = ⁅b, e⁆ := by
    rw [← mul_comm_of_mem_NOf h hbeN huL]; group
  rw [h1]
  exact (NOf M V g).mul_mem hbeN (hUpart u hu)

end Hyp612Sym

end CFSG.LocalAnalysis.WeakClosure81
