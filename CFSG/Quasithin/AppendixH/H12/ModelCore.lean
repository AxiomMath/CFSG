module

public import CFSG.Quasithin.AppendixH.H12.GLAction
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.Quasithin.H.Mathieu.H12Pf (glMul toAdd_glMul)
open CFSG.ASVolI.ChH (IsIntDirect cenIn ptStab)

abbrev G0 : Subgroup Γ12 := H12Cert.G

abbrev T0 : Subgroup Γ12 := H12Cert.T0

@[expose] def dc (c : ℕ) : Vec12 := Multiplicative.ofAdd (vecN 12 c)

@[expose] def cd (v : Vec12) : ℕ := codeN (Multiplicative.toAdd v)

theorem cd_lt (v : Vec12) : cd v < 4096 := codeN_lt _

theorem cd_dc {c : ℕ} (hc : c < 4096) : cd (dc c) = c := codeN_vecN hc

theorem dc_cd (v : Vec12) : dc (cd v) = v := by
  simp only [dc, cd]
  rw [vecN_codeN]
  exact ofAdd_toAdd v

theorem dc_inj {c d : ℕ} (hc : c < 4096) (hd : d < 4096) (h : dc c = dc d) : c = d := by
  exact vecN_inj hc hd (by simpa only [dc, toAdd_ofAdd] using congrArg Multiplicative.toAdd h)

theorem dc_zero : dc 0 = 1 := by
  rw [dc, vecN_zero]
  rfl

theorem dc_xor (a b : ℕ) : dc (a ^^^ b) = dc a * dc b := by
  rw [dc, vecN_xor, dc, dc]
  rfl

theorem glHom_dc (g : Γ12) (c : ℕ) :
    glHom g (dc c) = dc (mvN (colsN (g : Matrix (Fin 12) (Fin 12) (ZMod 2))) c) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_glHom]
  simp only [dc, toAdd_ofAdd]
  rw [mulVec_vecN]

theorem colsN_tU (w : List ℕ) : colsN ((tU w : Γ12) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = tW w := by
  rw [tU_val, colsN_decN (validN_evalW gG validN_gG w)]

theorem glHom_tU (w : List ℕ) (c : ℕ) : glHom (tU w) (dc c) = dc (mvN (tW w) c) := by
  rw [glHom_dc, colsN_tU]

@[expose] def gmv (g : Γ12) (c : ℕ) : ℕ := mvN (colsN (g : Matrix (Fin 12) (Fin 12) (ZMod 2))) c

theorem gmv_lt (g : Γ12) (c : ℕ) : gmv g c < 4096 := by
  rw [gmv]
  simpa using mvN_lt (validN_colsN (n := 12) _).2 c

theorem gmv_one {c : ℕ} (hc : c < 4096) : gmv 1 c = c := by
  rw [gmv, Units.val_one, colsN_one]
  have h := mulVec_vecN (n := 12) (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) c
  rw [Matrix.one_mulVec, colsN_one] at h
  exact vecN_inj (mvN_lt (n := 12) validN_oneN.2 c) hc h.symm

theorem gmv_mul (g h : Γ12) (c : ℕ) : gmv (g * h) c = gmv g (gmv h c) := by
  simp only [gmv, Units.val_mul, colsN_mul, mvN_mulN]

theorem gmv_xor (g : Γ12) (a b : ℕ) : gmv g (a ^^^ b) = gmv g a ^^^ gmv g b := by
  simp only [gmv, mvN_xor]

theorem gmv_tU (w : List ℕ) (c : ℕ) : gmv (tU w) c = mvN (tW w) c := by
  rw [gmv, colsN_tU]

private theorem gmv_gU (i c : ℕ) : gmv (gU i) c = mvN (gG.getD i one12) c := by
  rw [gmv, gU_val, colsN_decN (validN_getD validN_gG i)]

theorem closed_of_gen {S : ℕ → Prop} (h : ∀ i < 2, ∀ c, S c → S (mvN (gG.getD i one12) c)) {g : Γ12}
    (hg : g ∈ G0) {c : ℕ} (hc : S c) : S (gmv g c) := by
  have hgen : ∀ i < 2, ∀ c, S c → S (gmv (gU i) c) := by
    intro i hi c hc
    simpa only [gmv_gU] using h i hi c hc
  have h1 : ∀ c, S c → S (gmv 1 c) := by
    intro c hc
    have hpow : ∀ m : ℕ, S c → S (gmv ((gU 0) ^ (m + 1)) c) := by
      intro m
      induction m with
      | zero =>
        intro hc
        rw [pow_one]
        exact hgen 0 (by norm_num) c hc
      | succ m ih =>
        intro hc
        rw [pow_succ', gmv_mul]
        exact hgen 0 (by norm_num) _ (ih hc)
    have hfin : IsOfFinOrder (gU 0) := isOfFinOrder_of_finite _
    have hk : (gU 0) ^ (orderOf (gU 0) - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [← hk]
    exact hpow (orderOf (gU 0) - 1) hc
  refine G_induction (p := fun x => ∀ c, S c → S (gmv x c)) h1 ?_ hg c hc
  intro i hi y hy c hc
  rw [gmv_mul]
  exact hgen i hi _ (hy c hc)

@[expose] def smulSub (g : Γ12) (P : Subgroup Vec12) : Subgroup Vec12 := P.map (glHom g).toMonoidHom

theorem smulSub_one (P : Subgroup Vec12) : smulSub 1 P = P := by
  rw [smulSub, map_one]
  exact Subgroup.map_id P

theorem smulSub_mul (g h : Γ12) (P : Subgroup Vec12) :
    smulSub (g * h) P = smulSub g (smulSub h P) := by
  rw [smulSub, smulSub, smulSub, map_mul, Subgroup.map_map]
  congr 1

theorem card_smulSub (g : Γ12) (P : Subgroup Vec12) : Nat.card (smulSub g P) = Nat.card P := by
  rw [smulSub]
  exact Subgroup.card_map_of_injective (glHom g).injective

theorem smulSub_eq_of_le (g : Γ12) (P : Subgroup Vec12) (h : smulSub g P ≤ P) : smulSub g P = P :=
  Subgroup.eq_of_le_of_card_ge h (le_of_eq (card_smulSub g P).symm)

theorem mem_ptStab_iff (X : Subgroup Γ12) (P : Subgroup Vec12) (g : Γ12) :
    g ∈ ptStab glHom X P ↔ g ∈ X ∧ smulSub g P = P := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨h1, StabLat.mem_stabSub_iff_map.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.mpr ⟨h1, StabLat.mem_stabSub_iff_map.mpr h2⟩

theorem mem_cenIn_iff (X : Subgroup Γ12) (W : Subgroup Vec12) (g : Γ12) :
    g ∈ cenIn glHom X W ↔ g ∈ X ∧ ∀ u ∈ W, glHom g u = u := by
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨h1, mem_centSub.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.mpr ⟨h1, mem_centSub.mpr h2⟩

@[expose] def spanSub (b : List ℕ) : Subgroup Vec12 := Subgroup.closure {x | ∃ c ∈ b, x = dc c}

private def snStep (S : List ℕ) (v : ℕ) : List ℕ :=
  if S.contains v then S else S ++ S.map (· ^^^ v)

private theorem snStep_contains {S : List ℕ} {v : ℕ} (h : v ∈ S) : S.contains v = true :=
  List.contains_iff_mem.mpr h

private theorem snStep_not_contains {S : List ℕ} {v : ℕ} (h : v ∉ S) : S.contains v = false := by
  cases hc : S.contains v with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) h

private theorem spanN_foldl_nd (vs : List ℕ) (S : List ℕ) (hSn : S.Nodup)
    (hSxor : ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S) (hS0 : 0 ∈ S) :
    (vs.foldl snStep S).Nodup ∧
      (∀ a ∈ vs.foldl snStep S, ∀ b ∈ vs.foldl snStep S, a ^^^ b ∈ vs.foldl snStep S) ∧
      0 ∈ vs.foldl snStep S ∧ (∀ v ∈ vs, v ∈ vs.foldl snStep S) ∧
      (∀ a ∈ S, a ∈ vs.foldl snStep S) := by
  induction vs generalizing S with
  | nil => exact ⟨hSn, hSxor, hS0, by simp, fun a ha => ha⟩
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have hS1 : snStep S v = S := by rw [snStep, snStep_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih S hSn hSxor hS0
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h5 w hv
        · exact h4 w hw
      · intro a ha; exact h5 a ha
    · have hS1 : snStep S v = S ++ S.map (· ^^^ v) := by
        rw [snStep, snStep_not_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      have hS1n : (S ++ S.map (· ^^^ v)).Nodup := by
        rw [List.nodup_append]
        refine ⟨hSn, hSn.map (fun a b h => Nat.xor_left_inj.mp h), ?_⟩
        intro a ha b hb hab
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        exact hv (by
          have h2 : v = a ^^^ c := by
            rw [hab]
            simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self, Nat.xor_zero]
          rw [h2]; exact hSxor a ha c hc)
      have hS1xor : ∀ a ∈ S ++ S.map (· ^^^ v), ∀ b ∈ S ++ S.map (· ^^^ v),
          a ^^^ b ∈ S ++ S.map (· ^^^ v) := by
        intro a ha b hb
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp hb with hb | hb
          · exact List.mem_append.mpr (Or.inl (hSxor a ha b hb))
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
            exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
              ⟨a ^^^ c, hSxor a ha c hc, by simp [Nat.xor_assoc]⟩))
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
          rcases List.mem_append.mp hb with hb | hb
          · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
              ⟨c ^^^ b, hSxor c hc b hb, by simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]⟩))
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
            exact List.mem_append.mpr (Or.inl (by
              simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self, Nat.xor_zero]
                using hSxor c hc d hd))
      obtain ⟨h1, h2, h3, h4, h5⟩ :=
        ih (S ++ S.map (· ^^^ v)) hS1n hS1xor (List.mem_append.mpr (Or.inl hS0))
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with hwv | hw
        · have hvS1 : v ∈ S ++ S.map (· ^^^ v) :=
            List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨0, hS0, by simp⟩))
          rw [hwv]
          exact h5 v hvS1
        · exact h4 w hw
      · intro a ha
        exact h5 a (List.mem_append.mpr (Or.inl ha))

private theorem spanN_foldl_lt (vs : List ℕ) (S : List ℕ)
    (hSlt : ∀ a ∈ S, a < 2 ^ 12) (hvs : ∀ v ∈ vs, v < 2 ^ 12) :
    ∀ a ∈ vs.foldl snStep S, a < 2 ^ 12 := by
  induction vs generalizing S with
  | nil => simpa using hSlt
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have hS1 : snStep S v = S := by rw [snStep, snStep_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      exact ih S hSlt (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
    · have hS1 : snStep S v = S ++ S.map (· ^^^ v) := by
        rw [snStep, snStep_not_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      refine ih (S ++ S.map (· ^^^ v)) ?_ (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hSlt a ha
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        exact Nat.xor_lt_two_pow (hSlt c hc) (hvs v List.mem_cons_self)

private theorem spanN_eq_foldl (b : List ℕ) : spanN b = b.foldl snStep [0] := rfl

private theorem spanN_nd_parts (b : List ℕ) :
    (spanN b).Nodup ∧ (∀ a ∈ spanN b, ∀ c ∈ spanN b, a ^^^ c ∈ spanN b) ∧
      0 ∈ spanN b ∧ (∀ v ∈ b, v ∈ spanN b) := by
  have h := spanN_foldl_nd b [0] (by simp)
    (by
      intro a ha c hc
      simp only [List.mem_singleton] at ha hc
      subst ha; subst hc
      simp)
    (by simp)
  simpa only [spanN_eq_foldl] using ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private theorem spanN_xor {b : List ℕ} {a c : ℕ} (ha : a ∈ spanN b) (hc : c ∈ spanN b) :
    a ^^^ c ∈ spanN b :=
  (spanN_nd_parts b).2.1 a ha c hc

private theorem zero_mem_spanN (b : List ℕ) : 0 ∈ spanN b :=
  (spanN_nd_parts b).2.2.1

private theorem self_mem_spanN (b : List ℕ) : ∀ c ∈ b, c ∈ spanN b :=
  (spanN_nd_parts b).2.2.2

private theorem dc_mem_foldl (T : Subgroup Vec12) (vs S : List ℕ)
    (hS : ∀ a ∈ S, dc a ∈ T) (hvs : ∀ v ∈ vs, dc v ∈ T) :
    ∀ a ∈ vs.foldl snStep S, dc a ∈ T := by
  induction vs generalizing S with
  | nil => simpa using hS
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have hS1 : snStep S v = S := by rw [snStep, snStep_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      exact ih S hS (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
    · have hS1 : snStep S v = S ++ S.map (· ^^^ v) := by
        rw [snStep, snStep_not_contains hv]; rfl
      rw [List.foldl_cons, hS1]
      refine ih (S ++ S.map (· ^^^ v)) ?_ (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hS a ha
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        rw [dc_xor]
        exact T.mul_mem (hS c hc) (hvs v List.mem_cons_self)

private theorem cd_mul (u v : Vec12) : cd (u * v) = cd u ^^^ cd v := by
  conv_lhs => rw [← dc_cd u, ← dc_cd v, ← dc_xor]
  rw [cd_dc (Nat.xor_lt_two_pow (n := 12) (cd_lt u) (cd_lt v))]

private theorem inv_eq_self_vec12 (x : Vec12) : x⁻¹ = x := by
  rw [← dc_cd x]
  apply inv_eq_of_mul_eq_one_right
  show dc (cd x) * dc (cd x) = 1
  rw [← dc_xor, Nat.xor_self, dc_zero]

theorem spanN_nodup (b : List ℕ) : (spanN b).Nodup :=
  (spanN_nd_parts b).1

theorem spanN_lt {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) : ∀ c ∈ spanN b, c < 4096 := by
  have h := spanN_foldl_lt b [0] (by intro a ha; simp only [List.mem_singleton] at ha; subst ha; norm_num)
    (fun v hv => hb v hv)
  intro c hc
  rw [spanN_eq_foldl] at hc
  simpa using h c hc

theorem mem_spanSub_iff {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) (v : Vec12) :
    v ∈ spanSub b ↔ cd v ∈ spanN b := by
  constructor
  · intro hv
    let K : Subgroup Vec12 :=
      { carrier := {v | cd v ∈ spanN b}
        one_mem' := by
          change cd (1 : Vec12) ∈ spanN b
          rw [show (1 : Vec12) = dc 0 from dc_zero.symm, cd_dc (by norm_num)]
          exact zero_mem_spanN b
        mul_mem' := by
          intro x y hx hy
          change cd (x * y) ∈ spanN b
          change cd x ∈ spanN b at hx
          change cd y ∈ spanN b at hy
          rw [cd_mul]
          exact spanN_xor hx hy
        inv_mem' := by
          intro x hx
          change cd x⁻¹ ∈ spanN b
          change cd x ∈ spanN b at hx
          simpa only [inv_eq_self_vec12 x] using hx }
    have hle : spanSub b ≤ K := by
      rw [spanSub, Subgroup.closure_le]
      rintro x ⟨c, hc, rfl⟩
      change cd (dc c) ∈ spanN b
      rw [cd_dc (hb c hc)]
      exact self_mem_spanN b c hc
    exact hle hv
  · intro hv
    have h := dc_mem_foldl (spanSub b) b [0]
      (by
        intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        rw [dc_zero]
        exact Subgroup.one_mem _)
      (fun c hc => Subgroup.subset_closure ⟨c, hc, rfl⟩)
    have := h (cd v) (by simpa only [spanN_eq_foldl] using hv)
    rwa [dc_cd] at this

theorem dc_mem_spanSub_iff {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) {c : ℕ} (hc : c < 4096) :
    dc c ∈ spanSub b ↔ c ∈ spanN b := by
  rw [mem_spanSub_iff hb, cd_dc hc]

theorem card_spanSub {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) :
    Nat.card (spanSub b) = (spanN b).length := by
  classical
  have hnd := spanN_nodup b
  have memF : ∀ a : ℕ, a ∈ (spanN b).toFinset ↔ a ∈ spanN b := fun a => List.mem_toFinset
  let e : spanSub b ≃ (spanN b).toFinset :=
    { toFun := fun v => ⟨cd v.1, (memF _).mpr ((mem_spanSub_iff hb v.1).mp v.2)⟩
      invFun := fun x => ⟨dc x.1, (mem_spanSub_iff hb (dc x.1)).mpr (by
        rw [cd_dc (spanN_lt hb x.1 ((memF _).mp x.2))]
        exact (memF _).mp x.2)⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change dc (cd v.1) = v.1
        rw [dc_cd]
      right_inv := by
        intro x
        apply Subtype.ext
        change cd (dc x.1) = x.1
        rw [cd_dc (spanN_lt hb x.1 ((memF _).mp x.2))] }
  calc Nat.card (spanSub b) = Nat.card (spanN b).toFinset := Nat.card_congr e
    _ = (spanN b).length := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem smulSub_spanSub (g : Γ12) (b : List ℕ) :
    smulSub g (spanSub b) = spanSub (b.map (gmv g)) := by
  rw [smulSub, spanSub, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨gmv g c, List.mem_map.mpr ⟨c, hc, rfl⟩, glHom_dc g c⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact ⟨dc d, ⟨d, hd, rfl⟩, glHom_dc g d⟩

theorem spanSub_eq_iff {b b' : List ℕ} (hb : ∀ c ∈ b, c < 4096) (hb' : ∀ c ∈ b', c < 4096) :
    spanSub b = spanSub b' ↔ ∀ c < 4096, c ∈ spanN b ↔ c ∈ spanN b' := by
  constructor
  · intro h c hc
    rw [← dc_mem_spanSub_iff hb hc, h, dc_mem_spanSub_iff hb' hc]
  · intro h
    apply le_antisymm
    · intro v hv
      rw [mem_spanSub_iff hb] at hv
      rw [mem_spanSub_iff hb']
      exact (h (cd v) (cd_lt v)).mp hv
    · intro v hv
      rw [mem_spanSub_iff hb'] at hv
      rw [mem_spanSub_iff hb]
      exact (h (cd v) (cd_lt v)).mpr hv

theorem spanSub_le_iff {b b' : List ℕ} (hb : ∀ c ∈ b, c < 4096) (hb' : ∀ c ∈ b', c < 4096) :
    spanSub b ≤ spanSub b' ↔ ∀ c ∈ b, c ∈ spanN b' := by
  constructor
  · intro hle c hc
    rw [← dc_mem_spanSub_iff hb' (hb c hc)]
    exact hle (Subgroup.subset_closure ⟨c, hc, rfl⟩)
  · intro h
    rw [spanSub, Subgroup.closure_le]
    rintro x ⟨c, hc, rfl⟩
    exact (dc_mem_spanSub_iff hb' (hb c hc)).mpr (h c hc)

@[expose] def ptSub (c : ℕ) : Subgroup Vec12 := spanSub [c, mvN z12 c]

@[expose] def lineOf (c : ℕ) : List ℕ := [c, mvN z12 c, mvN z12 (mvN z12 c)]

theorem z12_lt (c : ℕ) : mvN z12 c < 4096 := by
  simpa using mvN_lt (n := 12) validN_z12.2 c

theorem lineOf_lt {c : ℕ} (hc : c < 4096) : ∀ x ∈ lineOf c, x < 4096 := by
  intro x hx
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hc
  · exact z12_lt c
  · exact z12_lt _

theorem omega_sq {c : ℕ} (hc : c < 4096) : mvN z12 (mvN z12 c) = c ^^^ mvN z12 c := by
  have h : (List.range 4096).all (fun c => mvN z12 (mvN z12 c) == c ^^^ mvN z12 c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

theorem omega_cube {c : ℕ} (hc : c < 4096) : mvN z12 (mvN z12 (mvN z12 c)) = c := by
  have h : (List.range 4096).all (fun c => mvN z12 (mvN z12 (mvN z12 c)) == c) = true := by
    decide +kernel
  have := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simpa using this

theorem omega_ne {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) : mvN z12 c ≠ c := by
  have h : (List.range 4096).all (fun c => mvN z12 c != c || c == 0) = true := by decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc'
  rcases hc' with hne | h0
  · exact hne
  · omega

private theorem ptSub_hb {c : ℕ} (hc : c < 4096) : ∀ x ∈ [c, mvN z12 c], x < 4096 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hc
  · exact z12_lt c

theorem spanN_ptSub {c : ℕ} (hc : c < 4096) :
    ∀ x, x ∈ spanN [c, mvN z12 c] ↔ x = 0 ∨ x ∈ lineOf c := by
  have h : (List.range 4096).all (fun c => spanN [c, mvN z12 c] ==
      (if c == 0 then [0] else [0, c, mvN z12 c, mvN z12 (mvN z12 c)])) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  have hspan : spanN [c, mvN z12 c] =
      (if c == 0 then [0] else [0, c, mvN z12 c, mvN z12 (mvN z12 c)]) := by
    simpa using hc'
  rw [hspan]
  intro x
  by_cases hc0 : c = 0
  · subst hc0
    simp [lineOf, mvN_zero]
  · have hc0' : (c == 0) = false := by
      cases h : c == 0 with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) hc0
    simp only [hc0', Bool.false_eq_true, if_false, lineOf, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc]

theorem mem_ptSub_iff {c : ℕ} (hc : c < 4096) (v : Vec12) :
    v ∈ ptSub c ↔ cd v = 0 ∨ cd v ∈ lineOf c := by
  rw [ptSub, mem_spanSub_iff (ptSub_hb hc) v]
  exact spanN_ptSub hc (cd v)

theorem card_ptSub {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) : Nat.card (ptSub c) = 4 := by
  rw [ptSub, card_spanSub (ptSub_hb hc)]
  have h : (List.range 4096).all (fun c => (spanN [c, mvN z12 c]).length == 4 || c == 0) = true := by
    decide +kernel
  have hc' := (List.all_eq_true.mp h) c (List.mem_range.mpr hc)
  have hc0' : (c == 0) = false := by
    cases h : c == 0 with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp h) (ne_of_gt hc0)
  rw [hc0', Bool.or_false] at hc'
  simpa using hc'

private theorem card_ptSub_zero : Nat.card (ptSub 0) = 1 := by
  have hb : ∀ x ∈ [0, mvN z12 0], x < 4096 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · norm_num
    · rw [mvN_zero]; norm_num
  rw [ptSub, card_spanSub hb]
  decide +kernel

private theorem mem_lineOf_omega {c x : ℕ} (hc : c < 4096) :
    x ∈ lineOf (mvN z12 c) ↔ x ∈ lineOf c := by
  have h3 := omega_cube hc
  rw [show lineOf (mvN z12 c) = [mvN z12 c, mvN z12 (mvN z12 c), c] from by
    simp only [lineOf, h3]]
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mem_lineOf_omega2 {c x : ℕ} (hc : c < 4096) :
    x ∈ lineOf (mvN z12 (mvN z12 c)) ↔ x ∈ lineOf c := by
  have h3 := omega_cube hc
  have h4 : mvN z12 (mvN z12 (mvN z12 (mvN z12 c))) = mvN z12 c := congrArg (mvN z12) h3
  rw [show lineOf (mvN z12 (mvN z12 c)) = [mvN z12 (mvN z12 c), c, mvN z12 c] from by
    simp only [lineOf, h3, h4]]
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem ptSub_eq_iff {c d : ℕ} (hc0 : 0 < c) (hc : c < 4096) (hd : d < 4096) :
    ptSub c = ptSub d ↔ d ∈ lineOf c := by
  constructor
  · intro h
    have hs : spanSub [c, mvN z12 c] = spanSub [d, mvN z12 d] := by
      simpa only [ptSub] using h
    have hm := (spanSub_eq_iff (ptSub_hb hc) (ptSub_hb hd)).mp hs d hd
    have hdself : d ∈ spanN [d, mvN z12 d] := self_mem_spanN _ d (List.mem_cons_self)
    have hdc : d ∈ spanN [c, mvN z12 c] := hm.mpr hdself
    rw [spanN_ptSub hc] at hdc
    rcases hdc with hd0 | hlin
    · exfalso
      have h4 := card_ptSub hc0 hc
      rw [h, hd0, card_ptSub_zero] at h4
      omega
    · exact hlin
  · intro hd
    apply (spanSub_eq_iff (ptSub_hb hc) (ptSub_hb (lineOf_lt hc d hd))).mpr
    intro x _
    rw [spanN_ptSub hc, spanN_ptSub (lineOf_lt hc d hd)]
    have hperm : x ∈ lineOf d ↔ x ∈ lineOf c := by
      simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact Iff.rfl
      · exact mem_lineOf_omega hc
      · exact mem_lineOf_omega2 hc
    rw [hperm]

theorem ptSub_eq_of_mem {c d : ℕ} (hc0 : 0 < c) (hc : c < 4096) (hd : d ∈ lineOf c) :
    ptSub c = ptSub d :=
  (ptSub_eq_iff hc0 hc (lineOf_lt hc d hd)).mpr hd

theorem gmv_omega {g : Γ12} (hg : g ∈ G0) {c : ℕ} (hc : c < 4096) :
    gmv g (mvN z12 c) = mvN z12 (gmv g c) := by
  have hz : ∀ x, gmv zU x = mvN z12 x := fun x => by
    rw [gmv, zU_val, colsN_decN validN_z12]
  rw [← hz c, ← gmv_mul, zU_comm hg, gmv_mul, hz (gmv g c)]

theorem smulSub_ptSub {g : Γ12} (hg : g ∈ G0) {c : ℕ} (hc : c < 4096) :
    smulSub g (ptSub c) = ptSub (gmv g c) := by
  show smulSub g (spanSub [c, mvN z12 c]) = spanSub [gmv g c, mvN z12 (gmv g c)]
  rw [smulSub_spanSub]
  simp only [List.map_cons, List.map_nil, gmv_omega hg hc]

@[expose] def vecStab (c : ℕ) : Subgroup Γ12 := cenIn glHom G0 (spanSub [c])

theorem mem_vecStab_iff {c : ℕ} (hc : c < 4096) (g : Γ12) :
    g ∈ vecStab c ↔ g ∈ G0 ∧ gmv g c = c := by
  rw [vecStab, mem_cenIn_iff]
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    have h1 := hfix (dc c) (Subgroup.subset_closure ⟨c, List.mem_singleton_self c, rfl⟩)
    rw [glHom_dc] at h1
    exact dc_inj (gmv_lt g c) hc h1
  · rintro ⟨hg, hgc⟩
    refine ⟨hg, ?_⟩
    let K : Subgroup Vec12 :=
      { carrier := {u | glHom g u = u}
        one_mem' := by change glHom g 1 = 1; simp
        mul_mem' := by intro a b ha hb; change glHom g (a * b) = a * b; rw [map_mul, ha, hb]
        inv_mem' := by intro a ha; change glHom g a⁻¹ = a⁻¹; rw [inv_eq_self_vec12 a]; exact ha }
    have hle : spanSub [c] ≤ K := by
      rw [spanSub, Subgroup.closure_le]
      rintro x ⟨d, hd, rfl⟩
      simp only [List.mem_singleton] at hd
      subst d
      have hz : glHom g (dc c) = dc c := by rw [glHom_dc]; exact congrArg dc hgc
      exact hz
    intro u hu
    exact hle hu

theorem vecStab_le_G0 (c : ℕ) : vecStab c ≤ G0 := inf_le_left

theorem vecStab_five : vecStab 5 = H12Cert.S0 := by
  apply le_antisymm
  · intro x hx
    rw [mem_vecStab_iff (by norm_num) x] at hx
    obtain ⟨hxG, hx5⟩ := hx
    obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hxG
    have hs5 : gmv s 5 = 5 := by
      have h := S0_fix hs
      rw [v0, mulVec_vecN] at h
      exact vecN_inj (gmv_lt s 5) (by norm_num) h
    have huwv : uw.1 = v0 := by
      have h1 := orbB_spec.2.2.2 uw huw
      rw [v0] at h1
      rw [gmv_mul, hs5, gmv_tU, h1] at hx5
      simpa [v0] using hx5
    have huw' : uw = (v0, []) := orbL_ext huw v0_mem huwv
    rw [huw']
    simpa [tU] using hs
  · intro s hs
    rw [mem_vecStab_iff (by norm_num) s]
    refine ⟨S0_le hs, ?_⟩
    have h := S0_fix hs
    rw [v0, mulVec_vecN] at h
    exact vecN_inj (gmv_lt s 5) (by norm_num) h

theorem center_G0 (hZ : Nat.card ↥(Subgroup.center ↥G0) = 3) :
    (Subgroup.center ↥G0).map G0.subtype = Subgroup.zpowers zU := by
  have hzU : zU ∈ (Subgroup.center ↥G0).map G0.subtype := by
    refine ⟨⟨zU, zU_mem⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact zU_comm x.2
  have hle : Subgroup.zpowers zU ≤ (Subgroup.center ↥G0).map G0.subtype :=
    Subgroup.zpowers_le.mpr hzU
  have hcard : Nat.card ((Subgroup.center ↥G0).map G0.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective G0), hZ]
  have hcard2 : Nat.card (Subgroup.zpowers zU) = 3 := by
    rw [Nat.card_zpowers, orderOf_zU]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hcard])).symm

private theorem gmv_zU (x : ℕ) : gmv zU x = mvN z12 x := by
  rw [gmv, zU_val, colsN_decN validN_z12]

private theorem gmv_zU_inv_zU (x : ℕ) (hx : x < 4096) : gmv zU⁻¹ (gmv zU x) = x := by
  rw [← gmv_mul, inv_mul_cancel, gmv_one hx]

private theorem omega2_ne {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    mvN z12 (mvN z12 c) ≠ c := by
  intro h
  have hh := congrArg (mvN z12) h
  rw [omega_cube hc] at hh
  exact omega_ne hc0 hc hh.symm

private theorem zU_mem_ptStab_aux {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    zU ∈ ptStab glHom G0 (ptSub c) := by
  rw [mem_ptStab_iff]
  refine ⟨zU_mem, ?_⟩
  rw [smulSub_ptSub zU_mem hc, gmv_zU c]
  exact (ptSub_eq_of_mem hc0 hc (by simp [lineOf])).symm

private theorem ptStab_mem_prod {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) {n : Γ12}
    (hn : n ∈ ptStab glHom G0 (ptSub c)) :
    ∃ x ∈ vecStab c, ∃ z ∈ Subgroup.zpowers zU, x * z = n := by
  rw [mem_ptStab_iff] at hn
  obtain ⟨hnG, hnsmul⟩ := hn
  have hnc : gmv n c ∈ lineOf c := by
    have h : ptSub (gmv n c) = ptSub c := by
      rw [← smulSub_ptSub hnG hc]; exact hnsmul
    exact (ptSub_eq_iff hc0 hc (gmv_lt n c)).mp h.symm
  simp only [lineOf, List.mem_cons, List.not_mem_nil, or_false] at hnc
  rcases hnc with h1 | h2 | h3
  · exact ⟨n, (mem_vecStab_iff hc n).mpr ⟨hnG, h1⟩, 1, (Subgroup.zpowers zU).one_mem,
      by simp⟩
  · have hx : zU⁻¹ * n ∈ vecStab c := by
      rw [mem_vecStab_iff hc]
      refine ⟨G0.mul_mem (G0.inv_mem zU_mem) hnG, ?_⟩
      rw [gmv_mul, h2, ← gmv_zU c, gmv_zU_inv_zU c hc]
    have heq : (zU⁻¹ * n) * zU = n := by
      rw [mul_assoc, zU_comm hnG, ← mul_assoc, inv_mul_cancel, one_mul]
    exact ⟨zU⁻¹ * n, hx, zU, Subgroup.mem_zpowers zU, heq⟩
  · have hx : (zU * zU)⁻¹ * n ∈ vecStab c := by
      rw [mem_vecStab_iff hc]
      refine ⟨G0.mul_mem (G0.inv_mem (G0.mul_mem zU_mem zU_mem)) hnG, ?_⟩
      rw [gmv_mul, h3, ← gmv_zU (mvN z12 c), ← gmv_zU c, ← gmv_mul, ← gmv_mul,
        show (zU * zU)⁻¹ * zU * zU = 1 by rw [mul_assoc, inv_mul_cancel], gmv_one hc]
    have hnz : n * (zU * zU) = (zU * zU) * n := by
      rw [← mul_assoc, zU_comm hnG, mul_assoc, zU_comm hnG, ← mul_assoc]
    have heq : ((zU * zU)⁻¹ * n) * (zU * zU) = n := by
      rw [mul_assoc, hnz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact ⟨(zU * zU)⁻¹ * n, hx, zU * zU,
      (Subgroup.zpowers zU).mul_mem (Subgroup.mem_zpowers zU) (Subgroup.mem_zpowers zU), heq⟩

private theorem ptStab_le_sup_aux {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    ptStab glHom G0 (ptSub c) ≤ vecStab c ⊔ Subgroup.zpowers zU := by
  intro n hn
  obtain ⟨x, hx, z, hz, rfl⟩ := ptStab_mem_prod hc0 hc hn
  exact (vecStab c ⊔ Subgroup.zpowers zU).mul_mem (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right hz)

private theorem sup_le_ptStab_aux {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    vecStab c ⊔ Subgroup.zpowers zU ≤ ptStab glHom G0 (ptSub c) := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [mem_vecStab_iff hc x] at hx
    obtain ⟨hxG, hxc⟩ := hx
    rw [mem_ptStab_iff]
    exact ⟨hxG, by rw [smulSub_ptSub hxG hc, hxc]⟩
  · exact Subgroup.zpowers_le.mpr (zU_mem_ptStab_aux hc0 hc)

private theorem commute_vecStab_zpowers {c : ℕ} {x : Γ12} (hx : x ∈ vecStab c) {z : Γ12}
    (hz : z ∈ Subgroup.zpowers zU) : x * z = z * x := by
  have hcomm : Commute x zU := zU_comm (vecStab_le_G0 c hx)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact hcomm.zpow_right k

private theorem inf_vecStab_zpowers_eq_bot {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    vecStab c ⊓ Subgroup.zpowers zU = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxX, hxZ⟩ := hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  rw [mem_vecStab_iff hc x] at hxX
  obtain ⟨hxG, hxc⟩ := hxX
  rw [← hk] at hxc ⊢
  have hk3 : zU ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact zU_pow_three
  have hmod : zU ^ k = zU ^ (k % 3) := zpow_eq_zpow_emod k hk3
  rw [hmod] at hxc ⊢
  have hrem : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    have h1 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h2 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hrem with h0 | h1 | h2
  · rw [h0, zpow_zero]
  · exfalso
    rw [h1, zpow_one, gmv_zU] at hxc
    exact omega_ne hc0 hc hxc
  · exfalso
    rw [h2, zpow_ofNat, pow_two, gmv_mul, gmv_zU, gmv_zU] at hxc
    exact omega2_ne hc0 hc hxc

theorem isIntDirect_ptStab {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    IsIntDirect (ptStab glHom G0 (ptSub c)) (vecStab c) (Subgroup.zpowers zU) := by
  have hsup : vecStab c ⊔ Subgroup.zpowers zU ≤ ptStab glHom G0 (ptSub c) :=
    sup_le_ptStab_aux hc0 hc
  refine ⟨le_trans le_sup_left hsup, le_trans le_sup_right hsup,
    fun x hx z hz => commute_vecStab_zpowers hx hz, inf_vecStab_zpowers_eq_bot hc0 hc, ?_⟩
  exact le_antisymm hsup (ptStab_le_sup_aux hc0 hc)

theorem card_ptStab {c : ℕ} (hc0 : 0 < c) (hc : c < 4096) :
    Nat.card (ptStab glHom G0 (ptSub c)) = 3 * Nat.card (vecStab c) := by
  have hsup : ptStab glHom G0 (ptSub c) = vecStab c ⊔ Subgroup.zpowers zU :=
    le_antisymm (ptStab_le_sup_aux hc0 hc) (sup_le_ptStab_aux hc0 hc)
  rw [hsup]
  have hZcard : Nat.card (Subgroup.zpowers zU) = 3 := by
    rw [Nat.card_zpowers, orderOf_zU]
  let f : vecStab c × Subgroup.zpowers zU → ↥(vecStab c ⊔ Subgroup.zpowers zU) := fun p =>
    ⟨p.1.1 * p.2.1,
      (vecStab c ⊔ Subgroup.zpowers zU).mul_mem (Subgroup.mem_sup_left p.1.2)
        (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨x1, hx1⟩, ⟨z1, hz1⟩⟩ ⟨⟨x2, hx2⟩, ⟨z2, hz2⟩⟩ h
      have h1 : x1 * z1 = x2 * z2 := by simpa [f] using congrArg Subtype.val h
      have hx : x1⁻¹ * x2 = z1 * z2⁻¹ := by
        have h2 := congrArg (fun t => x1⁻¹ * t * z2⁻¹) h1
        simpa [mul_assoc] using h2.symm
      have hmem : x1⁻¹ * x2 ∈ vecStab c ⊓ Subgroup.zpowers zU := by
        refine Subgroup.mem_inf.mpr ⟨vecStab c |>.mul_mem ((vecStab c).inv_mem hx1) hx2, ?_⟩
        rw [hx]
        exact (Subgroup.zpowers zU).mul_mem hz1 ((Subgroup.zpowers zU).inv_mem hz2)
      rw [inf_vecStab_zpowers_eq_bot hc0 hc, Subgroup.mem_bot] at hmem
      have hxeq : x1 = x2 := by
        have h2 := congrArg (fun t => x1 * t) hmem
        simpa [mul_assoc] using h2.symm
      have hzeq : z1 = z2 := by
        rw [hxeq] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hxeq) (Subtype.ext hzeq)
    · rintro ⟨n, hn⟩
      rw [← hsup] at hn
      obtain ⟨x, hx, z, hz, rfl⟩ := ptStab_mem_prod hc0 hc hn
      exact ⟨(⟨x, hx⟩, ⟨z, hz⟩), rfl⟩
  have hcard : Nat.card (vecStab c × Subgroup.zpowers zU) =
      Nat.card ↥(vecStab c ⊔ Subgroup.zpowers zU) := Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hcard, Nat.card_prod, hZcard]
  ring

theorem card_mul_le_of_orbit {H : Subgroup Γ12} (P : Subgroup Vec12) (l : List (Subgroup Vec12))
    (hnd : l.Nodup) (hl : ∀ Q ∈ l, ∃ h ∈ H, smulSub h P = Q) :
    l.length * Nat.card (ptStab glHom H P) ≤ Nat.card H := by
  classical
  let K : Subgroup Γ12 := ptStab glHom H P
  have hKH : K ≤ H := inf_le_left
  let K' : Subgroup ↥H := K.subgroupOf H
  let w : {Q // Q ∈ l} → Γ12 := fun Q => Classical.choose (hl Q.1 Q.2)
  have hwH : ∀ Q, w Q ∈ H := fun Q => (Classical.choose_spec (hl Q.1 Q.2)).1
  have hwP : ∀ Q, smulSub (w Q) P = Q.1 := fun Q => (Classical.choose_spec (hl Q.1 Q.2)).2
  let g : {Q // Q ∈ l} → ↥H ⧸ K' := fun Q => QuotientGroup.mk ⟨w Q, hwH Q⟩
  have hg : Function.Injective g := by
    intro Q Q' h
    have hmem' : (⟨w Q, hwH Q⟩ : ↥H)⁻¹ * ⟨w Q', hwH Q'⟩ ∈ K' := QuotientGroup.eq.mp h
    have hmem : (w Q)⁻¹ * w Q' ∈ K := by
      have hh := Subgroup.mem_subgroupOf.mp hmem'
      simpa using hh
    have hfix : smulSub ((w Q)⁻¹ * w Q') P = P := ((mem_ptStab_iff H P _).mp hmem).2
    have hww : w Q' = w Q * ((w Q)⁻¹ * w Q') := by group
    have h1 : smulSub (w Q') P = smulSub (w Q) P := by
      rw [hww, smulSub_mul, hfix]
    apply Subtype.ext
    rw [← hwP Q, ← hwP Q']
    exact h1.symm
  have hlen : Nat.card {Q // Q ∈ l} = l.length := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := l) (a := x)).symm),
      Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]
  have hidx : K'.index = K.relIndex H := by
    change (K.subgroupOf H).index = K.relIndex H
    rw [← Subgroup.comap_subtype K H, Subgroup.index_comap, Subgroup.range_subtype]
  have hle : l.length ≤ K.relIndex H := by
    rw [← hidx, Subgroup.index_eq_card, ← hlen]
    exact Nat.card_le_card_of_injective g hg
  have hKcard : Nat.card ↥K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  calc l.length * Nat.card K
      = l.length * Nat.card K' := by rw [hKcard]
    _ ≤ K.relIndex H * Nat.card K' := Nat.mul_le_mul_right _ hle
    _ = Nat.card H := by
        rw [hKcard]
        have h := Subgroup.relIndex_mul_card K H
        rwa [inf_eq_left.mpr hKH] at h

end CFSG.Quasithin.AppendixH.H12.Model
