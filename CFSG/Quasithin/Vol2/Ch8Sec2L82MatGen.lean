module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB
public import CFSG.Quasithin.Background.HCocBase
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H13

theorem comm_toW_mat {n : ℕ} {g : MulAut (Wn n)} {c : List ℕ} (hg : ActsBy g c) (m : ℕ) :
    g (toW n m) * (toW n m)⁻¹ = toW n (actM c m ^^^ m) := by
  rw [hg m, toW_inv_self, toW_xor]

theorem xorLin_actM_id (c : List ℕ) : XorLin (fun m => actM c m ^^^ m) := by
  intro a b
  show actM c (a ^^^ b) ^^^ (a ^^^ b) = (actM c a ^^^ a) ^^^ (actM c b ^^^ b)
  rw [actM_xor c a b]
  ac_rfl

theorem actM_id_mem_combos {c : List ℕ} {L : List ℕ} {n : ℕ}
    (h : ∀ j < n, (actM c (2 ^ j) ^^^ 2 ^ j) ∈ combos L) {m : ℕ} (hm : m < 2 ^ n) :
    actM c m ^^^ m ∈ combos L :=
  mem_combos_of_xorLin (f := fun m => actM c m ^^^ m) (xorLin_actM_id c) h m hm

theorem commV_closure_le_maskSub {n : ℕ} {S : Set (MulAut (Wn n))} {L : List ℕ}
    (h : ∀ g ∈ S, ∃ c, ActsBy g c ∧ ∀ j < n, (actM c (2 ^ j) ^^^ 2 ^ j) ∈ combos L) :
    commV (Subgroup.closure S) ≤ maskSub n L := by
  refine commV_closure_le S (maskSub n L) fun g hg v => ?_
  obtain ⟨c, hc, hj⟩ := h g hg
  obtain ⟨m, hm, rfl⟩ := toW_surj n v
  have e : g (toW n m) * (toW n m)⁻¹ = toW n (actM c m ^^^ m) := comm_toW_mat hc m
  exact Eq.mpr (congrArg (· ∈ maskSub n L) e) (toW_mem_maskSub (actM_id_mem_combos hj hm))

theorem maskSub_le_commV_sup {n : ℕ} {S : Set (MulAut (Wn n))} {L Ub : List ℕ}
    (h : ∀ l ∈ L, (∃ g ∈ S, ∃ c, ActsBy g c ∧ ∃ j < n, l = actM c (2 ^ j) ^^^ 2 ^ j) ∨
      l ∈ combos Ub) :
    maskSub n L ≤ commV (Subgroup.closure S) ⊔ maskSub n Ub := by
  rintro _ ⟨m, hm, rfl⟩
  refine mem_of_combos (fun m => toW n m ∈ commV (Subgroup.closure S) ⊔ maskSub n Ub) ?_ ?_ L
    ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · intro l hl
    rcases h l hl with ⟨g, hg, c, hc, j, hj, rfl⟩ | hU
    · refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g, Subgroup.subset_closure hg,
        toW n (2 ^ j), ?_⟩)
      exact comm_toW_mat hc (2 ^ j)
    · exact Subgroup.mem_sup_right (toW_mem_maskSub hU)

theorem s828CommSub_closure_le {V : Type} [CommGroup V] (S : Set (MulAut V)) (B D : Subgroup V)
    (hB : ∀ s ∈ Subgroup.closure S, ∀ w ∈ B, s w ∈ B)
    (hS : ∀ s ∈ S, ∀ w ∈ B, s w * w⁻¹ ∈ D) :
    s828CommSub (Subgroup.closure S) B ≤ D := by
  have key : ∀ y ∈ Subgroup.closure S, ∀ w ∈ B, y w * w⁻¹ ∈ D := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hS x hx
    | one => intro w _; simp
    | mul x y hx hy ihx ihy =>
      intro w hw
      have e : (x * y) w * w⁻¹ = (x (y w) * (y w)⁻¹) * (y w * w⁻¹) := by
        rw [MulAut.mul_apply]
        group
      rw [e]
      exact D.mul_mem (ihx (y w) (hB y hy w hw)) (ihy w hw)
    | inv x hx ih =>
      intro w hw
      have hxi : x⁻¹ w ∈ B := hB x⁻¹ (Subgroup.inv_mem _ hx) w hw
      have e : x⁻¹ w * w⁻¹ = (x (x⁻¹ w) * (x⁻¹ w)⁻¹)⁻¹ := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        group
      rw [e]
      exact D.inv_mem (ih (x⁻¹ w) hxi)
  unfold s828CommSub
  rw [Subgroup.closure_le]
  rintro _ ⟨y, hy, w, hw, rfl⟩
  exact key y hy w hw

theorem s828CommSub_le_commV {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))
    (B : Subgroup V) : s828CommSub Y B ≤ commV Y := by
  unfold s828CommSub commV
  exact Subgroup.closure_mono fun x ⟨y, hy, w, _, hx⟩ => ⟨y, hy, w, hx.symm⟩

theorem invariant_of_commV_le_mat {V : Type} [CommGroup V] {P : Subgroup (MulAut V)} {B : Subgroup V}
    (h : commV P ≤ B) : ∀ s ∈ P, ∀ w ∈ B, s w ∈ B := by
  intro s hs w hw
  have h1 : s w * w⁻¹ ∈ B := h (Subgroup.subset_closure ⟨s, hs, w, rfl⟩)
  have e : s w = (s w * w⁻¹) * w := by group
  rw [e]
  exact B.mul_mem h1 hw

theorem mem_combos_of_mem_mat {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ∈ combos l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [combos, List.mem_append, List.mem_map]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr ⟨0, zero_mem_combos l, by simp⟩
    · exact Or.inl (ih h)

theorem maskSub_le_commSub_sup {n : ℕ} {S : Set (MulAut (Wn n))} {L L2 Ub : List ℕ}
    (hL2 : ∀ l ∈ L2, (∃ g ∈ S, ∃ c, ActsBy g c ∧ ∃ b ∈ L, l = actM c b ^^^ b) ∨ l ∈ combos Ub) :
    maskSub n L2 ≤ s828CommSub (Subgroup.closure S) (maskSub n L) ⊔ maskSub n Ub := by
  set T := s828CommSub (Subgroup.closure S) (maskSub n L) ⊔ maskSub n Ub with hT
  have hclosed : ∀ (M : List ℕ), (∀ a ∈ M, toW n a ∈ T) → ∀ m ∈ combos M, toW n m ∈ T := by
    intro M hM m hm
    refine mem_of_combos (fun m => toW n m ∈ T) ?_ ?_ M hM m hm
    · rw [toW_zero]
      exact Subgroup.one_mem _
    · intro a b ha hb
      rw [toW_xor]
      exact Subgroup.mul_mem _ ha hb
  have hL2sub : ∀ a ∈ L2, toW n a ∈ T := by
    intro l hl
    rcases hL2 l hl with ⟨g, hg, c, hc, b, hb, rfl⟩ | hU
    · refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g, Subgroup.subset_closure hg,
        toW n b, toW_mem_maskSub (mem_combos_of_mem_mat hb), ?_⟩)
      exact (comm_toW_mat hc b).symm
    · exact Subgroup.mem_sup_right (toW_mem_maskSub hU)
  rintro _ ⟨m, hm, rfl⟩
  exact hclosed L2 hL2sub m hm

theorem maskSub_le_commSub_sup_of_cover {n : ℕ} {S : Set (MulAut (Wn n))} {L L2 Ub : List ℕ}
    (hL2 : ∀ l ∈ L2, (∃ g ∈ S, ∃ c, ActsBy g c ∧ ∃ b ∈ L, l = actM c b ^^^ b) ∨ l ∈ combos Ub)
    (hLL2 : ∀ l ∈ L, l ∈ combos L2) :
    maskSub n L ≤ s828CommSub (Subgroup.closure S) (maskSub n L) ⊔ maskSub n Ub := by
  refine le_trans ?_ (maskSub_le_commSub_sup (L := L) hL2)
  rintro _ ⟨m, hm, rfl⟩
  refine mem_of_combos (fun m => toW n m ∈ maskSub n L2) ?_ ?_ L ?_ m hm
  · rw [toW_zero]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [toW_xor]
    exact Subgroup.mul_mem _ ha hb
  · exact fun l hl => toW_mem_maskSub (hLL2 l hl)

theorem index_maskSub {n : ℕ} {L : List ℕ} (hl : ∀ a ∈ L, a < 2 ^ n) (hnd : (combos L).Nodup) :
    (maskSub n L).index = 2 ^ (n - L.length) := by
  have hc := card_maskSub hl hnd
  have h := Subgroup.index_mul_card (H := maskSub n L)
  rw [hc, natCard_Wn] at h
  have hle : L.length ≤ n := by
    have : Nat.card (maskSub n L) ≤ Nat.card (Wn n) := Subgroup.card_le_card_group _
    rw [hc, natCard_Wn] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  obtain ⟨k, hk⟩ : ∃ k, n = L.length + k := ⟨n - L.length, by omega⟩
  subst hk
  rw [pow_add] at h
  have h2 : (maskSub (L.length + k) L).index = 2 ^ k := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos L.length)
    rw [h, mul_comm]
  rw [Nat.add_sub_cancel_left]
  exact h2

theorem mQuot_top_maskSub {n : ℕ} {L : List ℕ} (hl : ∀ a ∈ L, a < 2 ^ n)
    (hnd : (combos L).Nodup) : mQuot ⊤ (maskSub n L) = n - L.length := by
  unfold mQuot
  rw [Subgroup.relIndex_top_right, index_maskSub hl hnd, padicValNat.prime_pow]

theorem relIndex_maskSub {n : ℕ} {L2 L : List ℕ} (hl2 : ∀ a ∈ L2, a < 2 ^ n)
    (hnd2 : (combos L2).Nodup) (hl : ∀ a ∈ L, a < 2 ^ n) (hnd : (combos L).Nodup)
    (hle : maskSub n L2 ≤ maskSub n L) :
    (maskSub n L2).relIndex (maskSub n L) = 2 ^ (L.length - L2.length) := by
  have h1 := Subgroup.relIndex_mul_index hle
  have hi1 := index_maskSub hl hnd
  have hi2 := index_maskSub hl2 hnd2
  have hc1 := card_maskSub hl hnd
  have hc2 := card_maskSub hl2 hnd2
  have h3 := Subgroup.relIndex_mul_index hle
  have hrel : (maskSub n L2).relIndex (maskSub n L) * (maskSub n L).index =
      (maskSub n L2).index := h3
  have hlen : L2.length ≤ L.length := by
    have := Subgroup.card_le_of_le hle
    rw [hc1, hc2] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hLn : L.length ≤ n := by
    have : Nat.card (maskSub n L) ≤ Nat.card (Wn n) := Subgroup.card_le_card_group _
    rw [hc1, natCard_Wn] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  rw [hi1, hi2] at hrel
  obtain ⟨k, hk⟩ : ∃ k, L.length = L2.length + k := ⟨L.length - L2.length, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, n = L.length + j := ⟨n - L.length, by omega⟩
  have e1 : n - L.length = j := by omega
  have e2 : n - L2.length = k + j := by omega
  rw [e1, e2] at hrel
  have e3 : L.length - L2.length = k := by omega
  rw [e3]
  have : (maskSub n L2).relIndex (maskSub n L) * 2 ^ j = 2 ^ k * 2 ^ j := by
    rw [hrel, pow_add]
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos j) this

@[expose] def trivOnAut {V : Type} [CommGroup V] [Finite V] (B U : Subgroup V) (hUB : U ≤ B) :
    Subgroup (MulAut V) where
  carrier := {x | ∀ b ∈ B, x b * b⁻¹ ∈ U}
  one_mem' := fun b _ => by simp
  mul_mem' := by
    intro x y hx hy b hb
    have hyb : y b ∈ B := by
      have h1 : y b * b⁻¹ ∈ B := hUB (hy b hb)
      have e : y b = (y b * b⁻¹) * b := by group
      rw [e]
      exact B.mul_mem h1 hb
    have e : (x * y) b * b⁻¹ = (x (y b) * (y b)⁻¹) * (y b * b⁻¹) := by
      rw [MulAut.mul_apply]
      group
    show (x * y) b * b⁻¹ ∈ U
    rw [e]
    exact U.mul_mem (hx (y b) hyb) (hy b hb)
  inv_mem' := by
    intro x hx b hb
    have hxB : ∀ b ∈ B, x b ∈ B := by
      intro b hb
      have h1 : x b * b⁻¹ ∈ B := hUB (hx b hb)
      have e : x b = (x b * b⁻¹) * b := by group
      rw [e]
      exact B.mul_mem h1 hb
    let f : B → B := fun b => ⟨x b, hxB b b.2⟩
    have hf : Function.Injective f := fun a b h => Subtype.ext (x.injective (congrArg Subtype.val h))
    obtain ⟨b', hb'⟩ := Finite.surjective_of_injective hf ⟨b, hb⟩
    have hb'x : x (b' : V) = b := congrArg Subtype.val hb'
    have e : x⁻¹ b * b⁻¹ = (x (b' : V) * (b' : V)⁻¹)⁻¹ := by
      have : x⁻¹ b = b' := by
        rw [← hb'x]
        exact x.symm_apply_apply _
      show x.symm b * b⁻¹ = _
      rw [show x.symm b = b' from this, hb'x]
      group
    show x⁻¹ b * b⁻¹ ∈ U
    rw [e]
    exact U.inv_mem (hx b' b'.2)

theorem mem_trivOnAut {V : Type} [CommGroup V] [Finite V] {B U : Subgroup V} {hUB : U ≤ B}
    {x : MulAut V} : x ∈ trivOnAut B U hUB ↔ ∀ b ∈ B, x b * b⁻¹ ∈ U := Iff.rfl

theorem closure_le_trivOnAut {n : ℕ} {S : Set (MulAut (Wn n))} {L Ub : List ℕ}
    (hUB : maskSub n Ub ≤ maskSub n L)
    (h : ∀ g ∈ S, ∃ c, ActsBy g c ∧ ∀ b ∈ L, (actM c b ^^^ b) ∈ combos Ub) :
    Subgroup.closure S ≤ trivOnAut (maskSub n L) (maskSub n Ub) hUB := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  obtain ⟨c, hc, hb⟩ := h g hg
  rintro _ ⟨m, hm, rfl⟩
  have hm' : actM c m ^^^ m ∈ combos Ub := by
    refine mem_of_combos (fun m => actM c m ^^^ m ∈ combos Ub) ?_ ?_ L hb m hm
    · rw [Nat.xor_zero, (actM_xor c).map_zero]
      exact zero_mem_combos Ub
    · intro a b ha hb'
      have e : actM c (a ^^^ b) ^^^ (a ^^^ b) = (actM c a ^^^ a) ^^^ (actM c b ^^^ b) :=
        xorLin_actM_id c a b
      rw [e]
      exact xor_mem_combos Ub ha hb'
  have e : g (toW n m) * (toW n m)⁻¹ = toW n (actM c m ^^^ m) := comm_toW_mat hc m
  show g (toW n m) * (toW n m)⁻¹ ∈ maskSub n Ub
  exact Eq.mpr (congrArg (· ∈ maskSub n Ub) e) (toW_mem_maskSub hm')

theorem comm_mem_of_index_two_mat {V : Type} [CommGroup V] [Finite V] {Q : Subgroup (MulAut V)}
    {U : Subgroup V} {x : MulAut V} (hQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hU : ∀ u ∈ U, x u = u) (hidx : (commV Q ⊔ U).index = 2) (v : V) :
    x v * v⁻¹ ∈ commV Q ⊔ U := by
  set W := commV Q ⊔ U with hW
  have hle : W ≤ W.comap x.toMonoidHom := by
    refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨y, hy, v, rfl⟩
      show x (y v * v⁻¹) ∈ W
      have e : x (y v * v⁻¹) = ((x * y * x⁻¹) (x v)) * (x v)⁻¹ := by
        rw [map_mul, map_inv]
        simp [MulAut.mul_apply]
      rw [e]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, hQ y hy, x v, rfl⟩)
    · intro u hu
      show x u ∈ W
      rw [hU u hu]
      exact Subgroup.mem_sup_right hu
  have hx1 : ∀ w ∈ W, x w ∈ W := fun w hw => hle hw
  have hx2 : ∀ w ∈ W, x⁻¹ w ∈ W := by
    let f : W → W := fun w => ⟨x w, hx1 w w.2⟩
    have hf : Function.Injective f := fun a b h => Subtype.ext (x.injective (congrArg Subtype.val h))
    intro w hw
    obtain ⟨w', hw'⟩ := Finite.surjective_of_injective hf ⟨w, hw⟩
    have h1 : x (w' : V) = w := congrArg Subtype.val hw'
    have h2 : x⁻¹ w = w' := by
      rw [← h1]
      exact x.symm_apply_apply _
    rw [h2]
    exact w'.2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  by_cases hv : v ∈ W
  · exact W.mul_mem (hx1 v hv) (W.inv_mem hv)
  · have hxv : x v ∉ W := fun h => hv (by
      have := hx2 _ h
      simpa using this)
    have h1 : v * a ∈ W := by
      rcases ha v with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hv
    have h2 : x v * a ∈ W := by
      rcases ha (x v) with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hxv
    have e : x v * v⁻¹ = (x v * a) * (v * a)⁻¹ := by group
    rw [e]
    exact W.mul_mem h2 (W.inv_mem h1)

open CFSG.QuasithinUnique.Setup.X1 in
theorem subprods_map_mem_closure {P M : Type*} [Group P] [Group M] (f : P →* M) (l : List P) :
    ∀ s ∈ subprods l, f s ∈ Subgroup.closure {y | ∃ x ∈ l, y = f x} := by
  induction l with
  | nil =>
    intro s hs
    simp only [subprods, List.mem_singleton] at hs
    rw [hs, map_one]
    exact Subgroup.one_mem _
  | cons y l ih =>
    intro s hs
    have hmono : Subgroup.closure {z | ∃ x ∈ l, z = f x} ≤
        Subgroup.closure {z | ∃ x ∈ y :: l, z = f x} :=
      Subgroup.closure_mono fun z ⟨x, hx, hz⟩ => ⟨x, List.mem_cons_of_mem y hx, hz⟩
    rcases mem_subprods_cons.1 hs with hs | ⟨w, hw, rfl⟩
    · exact hmono (ih s hs)
    · rw [map_mul]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨y, List.mem_cons_self, rfl⟩)
        (hmono (ih w hw))

theorem commV_mono_mat {V : Type*} [CommGroup V] {X Y : Subgroup (MulAut V)} (h : X ≤ Y) :
    commV X ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hw⟩ => ⟨x, h hx, v, hw⟩

section Transport

variable {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W]

theorem s828BPrime_map (e : V ≃* W) (H X : Subgroup (MulAut V)) :
    (s828BPrime H X).map e.toMonoidHom =
      s828BPrime (H.map (congrHom e)) (X.map (congrHom e)) := by
  unfold s828BPrime
  rw [Subgroup.map_sup, Subgroup.map_sup, ← commV_map_congrHom e X, ← fixV_map_congrHom e X,
    ← commV_map_congrHom e (perfectCore (H ⊓ stabSub (fixV X))), perfectCore_inf_stab_map e H X]

theorem s828CommSub_map (e : V ≃* W) (Y : Subgroup (MulAut V)) (B : Subgroup V) :
    (s828CommSub Y B).map e.toMonoidHom =
      s828CommSub (Y.map (congrHom e)) (B.map e.toMonoidHom) := by
  unfold s828CommSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, w, hw, rfl⟩, rfl⟩
    refine ⟨congrHom e y, Subgroup.mem_map_of_mem _ hy, e w, Subgroup.mem_map_of_mem _ hw, ?_⟩
    simp [congrHom]
  · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨y w * w⁻¹, ⟨y, hy, w, hw, rfl⟩, ?_⟩
    simp [congrHom]

theorem mQuot_top_map (e : V ≃* W) (B : Subgroup V) :
    mQuot ⊤ (B.map e.toMonoidHom) = mQuot ⊤ B := by
  unfold mQuot
  have h := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) B ⊤ e.injective
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h
  rw [h]

theorem mQuot_s828BPrime_map (e : V ≃* W) (H X : Subgroup (MulAut V)) :
    mQuot ⊤ (s828BPrime (H.map (congrHom e)) (X.map (congrHom e))) =
      mQuot ⊤ (s828BPrime H X) := by
  rw [← s828BPrime_map, mQuot_top_map]

theorem mb3_of_map (e : V ≃* W) (H X : Subgroup (MulAut V))
    (h : ∀ x ∈ pCoreOf 2 (perfectCore (H.map (congrHom e) ⊓
          stabSub (fixV (X.map (congrHom e))))),
      ∀ b ∈ s828BPrime (H.map (congrHom e)) (X.map (congrHom e)),
        x b * b⁻¹ ∈ fixV (X.map (congrHom e))) :
    ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))), ∀ b ∈ s828BPrime H X,
      x b * b⁻¹ ∈ fixV X := by
  intro x hx b hb
  have hxe : congrHom e x ∈ pCoreOf 2 (perfectCore (H.map (congrHom e) ⊓
      stabSub (fixV (X.map (congrHom e))))) := by
    rw [← perfectCore_inf_stab_map e H X, pCoreOf_map_congrHom]
    exact Subgroup.mem_map_of_mem _ hx
  have hbe : e b ∈ s828BPrime (H.map (congrHom e)) (X.map (congrHom e)) := by
    rw [← s828BPrime_map]
    exact Subgroup.mem_map_of_mem _ hb
  have key := h _ hxe _ hbe
  rw [fixV_map_congrHom] at key
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 key
  have e1 : e (x b * b⁻¹) = congrHom e x (e b) * (e b)⁻¹ := by
    have hs : e.symm (e b) = b := e.symm_apply_apply b
    show e (x b * b⁻¹) = e (x (e.symm (e b))) * (e b)⁻¹
    rw [hs, map_mul, map_inv]
  have hyb : y = x b * b⁻¹ := e.injective (hye.trans e1.symm)
  rw [← hyb]
  exact hy

theorem mb1_lhs_map (e : V ≃* W) (H X : Subgroup (MulAut V)) :
    (s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X).map
        e.toMonoidHom =
      s828CommSub (perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e)))))
        (s828BPrime (H.map (congrHom e)) (X.map (congrHom e))) ⊔ fixV (X.map (congrHom e)) := by
  rw [Subgroup.map_sup, s828CommSub_map, s828BPrime_map, ← fixV_map_congrHom e X,
    perfectCore_inf_stab_map e H X]

theorem mb1_eq_of_map (e : V ≃* W) (H X : Subgroup (MulAut V))
    (h : s828CommSub (perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e)))))
        (s828BPrime (H.map (congrHom e)) (X.map (congrHom e))) ⊔ fixV (X.map (congrHom e)) =
      s828BPrime (H.map (congrHom e)) (X.map (congrHom e))) :
    s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
      s828BPrime H X := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [mb1_lhs_map, s828BPrime_map]
  exact h

theorem mb1_relIndex_of_map (e : V ≃* W) (H X : Subgroup (MulAut V)) {k : ℕ}
    (h : (s828CommSub (perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e)))))
        (s828BPrime (H.map (congrHom e)) (X.map (congrHom e))) ⊔
          fixV (X.map (congrHom e))).relIndex
        (s828BPrime (H.map (congrHom e)) (X.map (congrHom e))) = k) :
    (s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X).relIndex
      (s828BPrime H X) = k := by
  rw [← mb1_lhs_map, ← s828BPrime_map, Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    at h
  exact h

theorem mb0_of_map' (e : V ≃* W) (H X : Subgroup (MulAut V)) (Hs Xs : Subgroup (MulAut W))
    (hH : H.map (congrHom e) = Hs) (hX : X.map (congrHom e) = Xs) :
    mQuot ⊤ (s828BPrime H X) = mQuot ⊤ (s828BPrime Hs Xs) := by
  subst hH hX
  exact (mQuot_s828BPrime_map e H X).symm

theorem mb3_of_map' (e : V ≃* W) (H X : Subgroup (MulAut V)) (Hs Xs : Subgroup (MulAut W))
    (hH : H.map (congrHom e) = Hs) (hX : X.map (congrHom e) = Xs)
    (h : ∀ x ∈ pCoreOf 2 (perfectCore (Hs ⊓ stabSub (fixV Xs))), ∀ b ∈ s828BPrime Hs Xs,
      x b * b⁻¹ ∈ fixV Xs) :
    ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))), ∀ b ∈ s828BPrime H X,
      x b * b⁻¹ ∈ fixV X := by
  subst hH hX
  exact mb3_of_map e H X h

theorem mb1_eq_of_map' (e : V ≃* W) (H X : Subgroup (MulAut V)) (Hs Xs : Subgroup (MulAut W))
    (hH : H.map (congrHom e) = Hs) (hX : X.map (congrHom e) = Xs)
    (h : s828CommSub (perfectCore (Hs ⊓ stabSub (fixV Xs))) (s828BPrime Hs Xs) ⊔ fixV Xs =
      s828BPrime Hs Xs) :
    s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
      s828BPrime H X := by
  subst hH hX
  exact mb1_eq_of_map e H X h

theorem mb1_relIndex_of_map' (e : V ≃* W) (H X : Subgroup (MulAut V)) (Hs Xs : Subgroup (MulAut W))
    (hH : H.map (congrHom e) = Hs) (hX : X.map (congrHom e) = Xs) {k : ℕ}
    (h : (s828CommSub (perfectCore (Hs ⊓ stabSub (fixV Xs))) (s828BPrime Hs Xs) ⊔
        fixV Xs).relIndex (s828BPrime Hs Xs) = k) :
    (s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X).relIndex
      (s828BPrime H X) = k := by
  subst hH hX
  exact mb1_relIndex_of_map e H X h

end Transport

end CFSG.Quasithin.H13.Mat
