module

public import CFSG.LocalAnalysis.StandardType.GGDepAThreeCheck
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


open Certificates.DepASmall

private def lr7sc_sp (ha aa : List ℕ) (r : GGDepAThreeSurv) : List GGDepANPair :=
  r.s.map fun e =>
    let q := ggDepANWord 3 6 (ggDepANGen 3 6 ha aa e.1) e.2.1 ha aa
    (ggDepANSmul 3 e.2.2 q.1, ggDepANSmul 3 e.2.2 q.2)

private def lr7sc_S (ha aa : List ℕ) (r : GGDepAThreeSurv) (i : Fin 6) :
    Module.End (ZMod 3) (GGDepAE 3 6) :=
  let q := (lr7sc_sp ha aa r).getD i.1 ([], [])
  ggDepARefl (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2)

private def lr7sc_gens (ha aa : List ℕ) : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  Set.range (fun i : Fin (6 - 1) => ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
    {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}

private lemma lr7sc_form_apply (f v : GGDepAE 3 6) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma lr7sc_refl_smul_center (p N : ℕ) (k : ZMod p) (c f : GGDepAE p N)
    (hk : k * k = 1) :
    ggDepARefl (k • c) (k • f) = ggDepARefl c f := by
  apply LinearMap.ext; intro v; ext j
  simp only [l05nNC_refl_apply, Pi.sub_apply, Pi.smul_apply, l05nNC_dot_smul_left, smul_eq_mul]
  congr 1
  calc k * ggDepAdot f v * (k * c j) = (k * k) * (ggDepAdot f v * c j) := by ring
    _ = ggDepAdot f v * c j := by rw [hk, one_mul]

private lemma lr7sc_refl_neg (c f : List ℕ) (hc : c.length = 6) (hf : f.length = 6) :
    ggDepARefl (ggDepANToZ 3 6 (ggDepANSmul 3 2 c))
        (ggDepANToZ 3 6 (ggDepANSmul 3 2 f)) =
      ggDepARefl (ggDepANToZ 3 6 c) (ggDepANToZ 3 6 f) := by
  rw [l05nNC_toZ_smul hc, l05nNC_toZ_smul hf]
  exact lr7sc_refl_smul_center 3 6 (2 : ZMod 3) _ _ (by decide)

private lemma lr7sc_refl_toZ_sub {c f v : List ℕ} (hc : c.length = 6) (hf : f.length = 6)
    (hv : v.length = 6) :
    ggDepARefl (ggDepANToZ 3 6 c) (ggDepANToZ 3 6 f) (ggDepANToZ 3 6 v) =
      ggDepANToZ 3 6 (ggDepANSub 3 v (ggDepANSmul 3 (ggDepANDot 3 f v) c)) := by
  rw [l05nNC_refl_apply, ← ggDepANDot_cast f v hf hv,
    l05nNC_toZ_sub hv (l05nNC_smul_length hc), l05nNC_toZ_smul hc]

private lemma lr7sc_sameRefl_refl {q r : GGDepANPair} (hq1 : q.1.length = 6)
    (hq2 : q.2.length = 6) (hr1 : r.1.length = 6) (hr2 : r.2.length = 6)
    (h : ggDepAThreeSameRefl 3 q r = true) :
    ggDepARefl (ggDepANToZ 3 6 r.1) (ggDepANToZ 3 6 r.2) =
      ggDepARefl (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2) := by
  simp only [ggDepAThreeSameRefl, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact (lr7sc_refl_neg r.1 r.2 hr1 hr2).symm

private lemma lr7sc_getD_mem {α : Type*} {l : List α} {n : ℕ} (d : α) (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem (l := l) (d := d) h]
  exact List.getElem_mem h

private lemma lr7sc_sp_length (ha aa : List ℕ) (r : GGDepAThreeSurv)
    (hslen : r.s.length = 6) : (lr7sc_sp ha aa r).length = 6 := by
  simp only [lr7sc_sp, List.length_map, hslen]

private theorem lr7sc_intcartan_e6 : GGIntCartan CoxeterMatrix.E₆ (CartanMatrix.E 6) := by
  unfold GGIntCartan
  constructor
  · intro i; fin_cases i <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma lr7sc_e6res_cartan (i j : Fin 6) :
    ((ggDepAThreeE6Res 3 i.1 j.1 : ℕ) : ZMod 3) = ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma lr7sc_end_pow_coe (e : GGDepAE 3 6 ≃ₗ[ZMod 3] GGDepAE 3 6) (m : ℕ) :
    ((e ^ m : GGDepAE 3 6 ≃ₗ[ZMod 3] GGDepAE 3 6) :
        Module.End (ZMod 3) (GGDepAE 3 6)) = (e : Module.End (ZMod 3) (GGDepAE 3 6)) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private lemma lr7sc_coe_rel (c f c' f' : GGDepAE 3 6) (h : ggDepAform f c = 2)
    (h' : ggDepAform f' c' = 2) (m : ℕ)
    (hrel : (Module.reflection h * Module.reflection h') ^ m = 1) :
    (ggDepARefl c f * ggDepARefl c' f') ^ m = 1 := by
  have hcoe := congrArg (fun e : GGDepAE 3 6 ≃ₗ[ZMod 3] GGDepAE 3 6 =>
    (e : Module.End (ZMod 3) (GGDepAE 3 6))) hrel
  rw [lr7sc_end_pow_coe, LinearEquiv.coe_toLinearMap_mul,
    LinearEquiv.coe_toLinearMap_one] at hcoe
  rw [show ggDepARefl c f = ((Module.reflection h : GGDepAE 3 6 ≃ₗ[ZMod 3] GGDepAE 3 6) :
      Module.End (ZMod 3) (GGDepAE 3 6)) from rfl,
    show ggDepARefl c' f' = ((Module.reflection h' : GGDepAE 3 6 ≃ₗ[ZMod 3] GGDepAE 3 6) :
      Module.End (ZMod 3) (GGDepAE 3 6)) from rfl]
  rw [show (1 : Module.End (ZMod 3) (GGDepAE 3 6)) = LinearMap.id from rfl]
  exact hcoe

private lemma lr7sc_key_append (p : ℕ) (a : List ℕ) (x : ℕ) :
    ggDepAThreeKey p (a ++ [x]) = ggDepAThreeKey p a * p + x % p := by
  simp only [ggDepAThreeKey, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma lr7sc_key_mod (p : ℕ) (a : List ℕ) :
    ggDepAThreeKey p a = ggDepAThreeKey p (a.map (· % p)) := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a x ih =>
      rw [List.map_append, List.map_cons, List.map_nil, lr7sc_key_append, lr7sc_key_append, ih,
        Nat.mod_mod]

private lemma lr7sc_key_congr {p : ℕ} {a b : List ℕ} (h : a.map (· % p) = b.map (· % p)) :
    ggDepAThreeKey p a = ggDepAThreeKey p b := by
  rw [lr7sc_key_mod p a, lr7sc_key_mod p b, h]

private lemma lr7sc_key_eq_of_toZ_eq {a b : List ℕ} (ha : a.length = 6) (hb : b.length = 6)
    (h : ggDepANToZ 3 6 a = ggDepANToZ 3 6 b) :
    ggDepAThreeKey 3 a = ggDepAThreeKey 3 b := by
  apply lr7sc_key_congr
  rw [List.ext_getElem?_iff']
  intro n hn
  rw [List.getElem?_map, List.getElem?_map]
  have hna : n < a.length := by
    have := hn; rw [List.length_map, List.length_map, ha, hb] at this; omega
  have hnb : n < b.length := by
    have := hn; rw [List.length_map, List.length_map, ha, hb] at this; omega
  rw [List.getElem?_eq_getElem hna, List.getElem?_eq_getElem hnb]
  have hcoord := congrFun h ⟨n, by omega⟩
  change ((a.getD n 0 : ℕ) : ZMod 3) = ((b.getD n 0 : ℕ) : ZMod 3) at hcoord
  rw [List.getD_eq_getElem (l := a) (d := 0) (by omega),
      List.getD_eq_getElem (l := b) (d := 0) (by omega)] at hcoord
  simp only [Option.map_some]
  exact congrArg some ((ZMod.natCast_eq_natCast_iff' (a[n]) (b[n]) 3).mp hcoord)

private lemma lr7sc_toZ_X : ggDepANToZ 3 6 (ggDepANX 6) = ggDepAx 3 6 := by
  funext j
  have hj : j.1 < (ggDepANX 6).length := by simpa [ggDepANX] using j.2
  rw [ggDepANToZ, List.getD_eq_getElem (l := ggDepANX 6) (d := 0) hj]
  simp only [ggDepANX, ggDepAx, List.getElem_map, List.getElem_range]
  split <;> simp

private lemma lr7sc_cast_ht (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    ((((if a then 1 else 0) + (if c then 1 else 0) +
        (3 - (if b then 1 else 0))) % 3 : ℕ) : ZMod 3)
      = (if a then (1 : ZMod 3) else 0) - (if b then (1 : ZMod 3) else 0) +
          (if c then (1 : ZMod 3) else 0) := by
  split_ifs <;> decide

private lemma lr7sc_cast_at (a b : Prop) [Decidable a] [Decidable b] :
    ((((if a then 1 else 0) + (3 - (if b then 1 else 0))) % 3 : ℕ) : ZMod 3)
      = (if a then (1 : ZMod 3) else 0) - (if b then (1 : ZMod 3) else 0) := by
  split_ifs <;> decide

private lemma lr7sc_toZ_H {i : ℕ} (h : i + 1 < 6) :
    ggDepANToZ 3 6 (ggDepANH 3 6 i) = ggDepAh 3 6 ⟨i, by omega⟩ := by
  funext j
  have hj : j.1 < (ggDepANH 3 6 i).length := by simpa [ggDepANH] using j.2
  rw [ggDepANToZ, List.getD_eq_getElem (l := ggDepANH 3 6 i) (d := 0) hj]
  simp only [ggDepANH, ggDepAh, List.getElem_map, List.getElem_range]
  by_cases hj6 : j.1 + 1 = 6
  · simp [hj6]
  · rw [if_neg hj6, if_neg hj6]
    exact lr7sc_cast_ht (j.1 = i) (j.1 = i + 1) (i + 2 = 6)

private lemma lr7sc_toZ_A {i : ℕ} (h : i + 1 < 6) :
    ggDepANToZ 3 6 (ggDepANA 3 6 i) = ggDepAα 3 6 ⟨i, by omega⟩ := by
  funext j
  have hj : j.1 < (ggDepANA 3 6 i).length := by simpa [ggDepANA] using j.2
  rw [ggDepANToZ, List.getD_eq_getElem (l := ggDepANA 3 6 i) (d := 0) hj]
  simp only [ggDepANA, ggDepAα, List.getElem_map, List.getElem_range]
  by_cases hj6 : j.1 + 1 = 6
  · simp [hj6]
  · rw [if_neg hj6, if_neg hj6]
    exact lr7sc_cast_at (j.1 = i) (j.1 = i + 1)

private lemma lr7sc_sp_mem (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (hdot : ggDepANDot 3 aa ha = 2 % 3) (r : GGDepAThreeSurv)
    (hslen : r.s.length = 6)
    (hsall : ∀ x ∈ r.s,
      (x.1 < 6 ∧ ∀ t ∈ x.2.1, t < 6) ∧ (x.2.2 == 1 || x.2.2 == 3 - 1) = true)
    (hspall : ∀ x ∈ lr7sc_sp ha aa r, (ggDepANDot 3 x.2 x.1 == 2 % 3) = true) :
    ∀ q ∈ lr7sc_sp ha aa r,
      q.1.length = 6 ∧ q.2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2 ∧
      ggDepARefl (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2) ∈
        Submonoid.closure (lr7sc_gens ha aa) := by
  intro q hq
  have hdotq := hspall q hq
  simp only [lr7sc_sp, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  obtain ⟨⟨he1, he2⟩, hesign⟩ := hsall e he
  set q0 : GGDepANPair := ggDepANWord 3 6 (ggDepANGen 3 6 ha aa e.1) e.2.1 ha aa with hq0
  have hgen1 : (ggDepANGen 3 6 ha aa e.1).1.length = 6 := l05nNC_gen_length1 hha haa e.1
  have hgen2 : (ggDepANGen 3 6 ha aa e.1).2.length = 6 := l05nNC_gen_length2 hha haa e.1
  have hq01 : q0.1.length = 6 := (l05nNC_word_length hha haa e.2.1 _ hgen1 hgen2).1
  have hq02 : q0.2.length = 6 := (l05nNC_word_length hha haa e.2.1 _ hgen1 hgen2).2
  have hword := l05nNC_word ha aa hha haa (Submonoid.closure (lr7sc_gens ha aa))
      (fun g => l05nNC_gen_dot hha haa hdot g)
      (fun g => l05nNC_gen_mem hha haa g)
      e.2.1 (ggDepANGen 3 6 ha aa e.1) hgen1 hgen2
      (l05nNC_gen_dot hha haa hdot e.1) (l05nNC_gen_mem hha haa e.1)
  have hsig : e.2.2 = 1 ∨ e.2.2 = 2 := by simpa using hesign
  have hkk : (e.2.2 : ZMod 3) * (e.2.2 : ZMod 3) = 1 := by
    rcases hsig with h | h <;> rw [h] <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact l05nNC_smul_length hq01
  · exact l05nNC_smul_length hq02
  · have hE : ggDepANDot 3 (ggDepANSmul 3 e.2.2 q0.2) (ggDepANSmul 3 e.2.2 q0.1) = 2 := by
      have hh := hdotq
      simp only [beq_iff_eq] at hh
      norm_num at hh
      exact hh
    rw [← ggDepANDot_cast (p := 3) (N := 6) _ _
      (l05nNC_smul_length hq02) (l05nNC_smul_length hq01), hE]
    norm_num
  · rw [l05nNC_toZ_smul hq01, l05nNC_toZ_smul hq02]
    rw [show ggDepARefl ((e.2.2 : ZMod 3) • ggDepANToZ 3 6 q0.1)
          ((e.2.2 : ZMod 3) • ggDepANToZ 3 6 q0.2) =
        ggDepARefl (ggDepANToZ 3 6 q0.1) (ggDepANToZ 3 6 q0.2) from
      lr7sc_refl_smul_center 3 6 (e.2.2 : ZMod 3) _ _ hkk]
    exact hword.2

private lemma lr7sc_sp_props (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (hdot : ggDepANDot 3 aa ha = 2 % 3) (r : GGDepAThreeSurv) (hslen : r.s.length = 6)
    (hsall : ∀ x ∈ r.s,
      (x.1 < 6 ∧ ∀ t ∈ x.2.1, t < 6) ∧ (x.2.2 == 1 || x.2.2 == 3 - 1) = true)
    (hspall : ∀ x ∈ lr7sc_sp ha aa r, (ggDepANDot 3 x.2 x.1 == 2 % 3) = true) :
    ∀ i : Fin 6,
      ((lr7sc_sp ha aa r).getD i.1 ([], [])).1.length = 6 ∧
      ((lr7sc_sp ha aa r).getD i.1 ([], [])).2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2)
        (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).1) = 2 ∧
      ggDepARefl (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).1)
        (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2) ∈
        Submonoid.closure (lr7sc_gens ha aa) := by
  intro i
  have hlen := lr7sc_sp_length ha aa r hslen
  have hget : (lr7sc_sp ha aa r).getD i.1 ([], []) ∈ lr7sc_sp ha aa r :=
    lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := i.1) ([], []) (by simpa [hlen] using i.2)
  exact lr7sc_sp_mem ha aa hha haa hdot r hslen hsall hspall _ hget

private lemma lr7sc_coxeter (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (r : GGDepAThreeSurv) (hslen : r.s.length = 6)
    (hsp : ∀ q ∈ lr7sc_sp ha aa r, q.1.length = 6 ∧ q.2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2)
    (hpair : ∀ x < 6, ∀ y < 6,
      (ggDepANDot 3 ((lr7sc_sp ha aa r).getD x ([], [])).2
        ((lr7sc_sp ha aa r).getD y ([], [])).1 == ggDepAThreeE6Res 3 x y) = true) :
    ∀ i j : Fin 6,
      (lr7sc_S ha aa r i * lr7sc_S ha aa r j) ^ CoxeterMatrix.E₆ i j = 1 := by
  intro i j
  have hα : ∀ i : Fin 6,
      ggDepAform (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2)
        (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).1) = 2 := by
    intro i
    rw [lr7sc_form_apply]
    exact (hsp _ (lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := i.1) ([], [])
      (by simpa [lr7sc_sp_length ha aa r hslen] using i.2))).2.2
  have hP : ∀ i j : Fin 6,
      ggDepAform (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2)
        (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD j.1 ([], [])).1) =
      ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) := by
    intro i j
    rw [lr7sc_form_apply]
    have h1 : ggDepANDot 3 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2
        ((lr7sc_sp ha aa r).getD j.1 ([], [])).1 = ggDepAThreeE6Res 3 i.1 j.1 := by
      have hh := hpair i.1 i.2 j.1 j.2
      simpa [beq_iff_eq] using hh
    have hgeti' : (lr7sc_sp ha aa r).getD i.1 ([], []) ∈ lr7sc_sp ha aa r :=
      lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := i.1) ([], [])
        (by simpa [lr7sc_sp_length ha aa r hslen] using i.2)
    have hgetj' : (lr7sc_sp ha aa r).getD j.1 ([], []) ∈ lr7sc_sp ha aa r :=
      lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := j.1) ([], [])
        (by simpa [lr7sc_sp_length ha aa r hslen] using j.2)
    rw [← ggDepANDot_cast (p := 3) (N := 6) _ _
      (hsp _ hgeti').2.1 (hsp _ hgetj').1, h1, lr7sc_e6res_cartan i j]
  have hrel := isLiftable_reflection_of_intCartan lr7sc_intcartan_e6
      (fun i : Fin 6 => ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).1)
      (fun i : Fin 6 => ggDepAform (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2))
      hα hP
  exact lr7sc_coe_rel _ _ _ _ (hα i) (hα j) _ (hrel i j)

private lemma lr7sc_sword_length (ha aa : List ℕ) (r : GGDepAThreeSurv)
    (hsp : ∀ q ∈ lr7sc_sp ha aa r, q.1.length = 6 ∧ q.2.length = 6)
    (j0 : ℕ) (hj0 : j0 < (lr7sc_sp ha aa r).length) (w : List ℕ)
    (hw : ∀ t ∈ w, t < (lr7sc_sp ha aa r).length) :
    (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w).1.length = 6 ∧
      (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w).2.length = 6 := by
  induction w with
  | nil =>
      simpa only [ggDepAThreeSWord, List.foldr_nil] using
        hsp _ (lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := j0) ([], []) hj0)
  | cons t w ih =>
      rw [show ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 (t :: w) =
          ggDepANConj 3 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w)
            ((lr7sc_sp ha aa r).getD t ([], [])) from by
        simp only [ggDepAThreeSWord, List.foldr_cons]]
      have hwt : t < (lr7sc_sp ha aa r).length := hw t List.mem_cons_self
      exact l05nNC_conj_length (ih (fun s hs => hw s (List.mem_cons_of_mem t hs))).1
        (ih (fun s hs => hw s (List.mem_cons_of_mem t hs))).2
        (hsp _ (lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := t) ([], []) hwt)).1
        (hsp _ (lr7sc_getD_mem (l := lr7sc_sp ha aa r) (n := t) ([], []) hwt)).2

private lemma lr7sc_sword_mem (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (r : GGDepAThreeSurv) (hslen : r.s.length = 6)
    (hsp : ∀ q ∈ lr7sc_sp ha aa r, q.1.length = 6 ∧ q.2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2)
    (j0 : ℕ) (hj0 : j0 < (lr7sc_sp ha aa r).length) (w : List ℕ)
    (hw : ∀ t ∈ w, t < (lr7sc_sp ha aa r).length) :
    ggDepARefl (ggDepANToZ 3 6 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w).1)
        (ggDepANToZ 3 6 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w).2) ∈
      Submonoid.closure (Set.range (lr7sc_S ha aa r)) := by
  have hsplen : (lr7sc_sp ha aa r).length = 6 := lr7sc_sp_length ha aa r hslen
  induction w with
  | nil =>
      rw [show ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 [] =
          (lr7sc_sp ha aa r).getD j0 ([], []) from by
        simp only [ggDepAThreeSWord, List.foldr_nil]]
      exact Submonoid.subset_closure ⟨⟨j0, by simpa [hsplen] using hj0⟩, rfl⟩
  | cons t w ih =>
      rw [show ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 (t :: w) =
          ggDepANConj 3 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w)
            ((lr7sc_sp ha aa r).getD t ([], [])) from by
        simp only [ggDepAThreeSWord, List.foldr_cons]]
      set q : GGDepANPair := ggDepAThreeSWord 3 (lr7sc_sp ha aa r) j0 w with hq
      have hwt : t < (lr7sc_sp ha aa r).length := hw t List.mem_cons_self
      have hw' : ∀ s ∈ w, s < (lr7sc_sp ha aa r).length :=
        fun s hs => hw s (List.mem_cons_of_mem t hs)
      have hqt1 : q.1.length = 6 := (lr7sc_sword_length ha aa r
        (fun s hs => ⟨(hsp s hs).1, (hsp s hs).2.1⟩) j0 hj0 w hw').1
      have hqt2 : q.2.length = 6 := (lr7sc_sword_length ha aa r
        (fun s hs => ⟨(hsp s hs).1, (hsp s hs).2.1⟩) j0 hj0 w hw').2
      have hgt1 : ((lr7sc_sp ha aa r).getD t ([], [])).1.length = 6 :=
        (hsp _ (lr7sc_getD_mem _ hwt)).1
      have hgt2 : ((lr7sc_sp ha aa r).getD t ([], [])).2.length = 6 :=
        (hsp _ (lr7sc_getD_mem _ hwt)).2.1
      have hgtd : ggDepAdot (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD t ([], [])).2)
          (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD t ([], [])).1) = 2 :=
        (hsp _ (lr7sc_getD_mem _ hwt)).2.2
      obtain ⟨hc1, hc2⟩ := l05nNC_toZ_conj (p := 3) (N := 6) (q := q)
        (g := (lr7sc_sp ha aa r).getD t ([], [])) hqt1 hqt2 hgt1 hgt2
      rw [hc1, hc2]
      rw [← l05nNC_refl_conj (ggDepANToZ 3 6 q.1) (ggDepANToZ 3 6 q.2)
        (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD t ([], [])).1)
        (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD t ([], [])).2) hgtd]
      have hgm : ggDepARefl (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD t ([], [])).1)
          (ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD t ([], [])).2) ∈
          Submonoid.closure (Set.range (lr7sc_S ha aa r)) :=
        Submonoid.subset_closure ⟨⟨t, by simpa [hsplen] using hwt⟩, rfl⟩
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hgm (by rw [hq]; exact ih hw')) hgm

private lemma lr7sc_gen_single_mem (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (r : GGDepAThreeSurv) (hslen : r.s.length = 6)
    (hsp : ∀ q ∈ lr7sc_sp ha aa r, q.1.length = 6 ∧ q.2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2)
    (hglen : r.g.length = 6)
    (hgall : ∀ x ∈ r.g, x.1 < 6 ∧ ∀ t ∈ x.2, t < 6)
    (hg6 : ∀ x < 6, (match r.g[x]? with
      | none => false
      | some e => ggDepAThreeSameRefl 3 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2)
          (ggDepANGen 3 6 ha aa x)) = true)
    (k : ℕ) (hk : k < 6) :
    ggDepARefl (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa k).1)
        (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa k).2) ∈
      Submonoid.closure (Set.range (lr7sc_S ha aa r)) := by
  have hsplen : (lr7sc_sp ha aa r).length = 6 := lr7sc_sp_length ha aa r hslen
  have hk' : k < r.g.length := by simpa [hglen] using hk
  set e : ℕ × List ℕ := r.g[k] with he
  have hmem : e ∈ r.g := by rw [he]; exact List.getElem_mem hk'
  obtain ⟨he1, he2⟩ := hgall e hmem
  have h6 := hg6 k hk
  rw [List.getElem?_eq_getElem (l := r.g) hk'] at h6
  rw [← he] at h6
  have hsword : ggDepARefl (ggDepANToZ 3 6
      (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2).1)
      (ggDepANToZ 3 6 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2).2) ∈
      Submonoid.closure (Set.range (lr7sc_S ha aa r)) :=
    lr7sc_sword_mem ha aa hha haa r hslen hsp e.1
      (by rw [hsplen]; exact he1) e.2
      (fun t ht => by rw [hsplen]; exact he2 t ht)
  have hq1 : (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2).1.length = 6 :=
    (lr7sc_sword_length ha aa r (fun s hs => ⟨(hsp s hs).1, (hsp s hs).2.1⟩)
      e.1 (by rw [hsplen]; exact he1) e.2 (fun t ht => by rw [hsplen]; exact he2 t ht)).1
  have hq2 : (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2).2.length = 6 :=
    (lr7sc_sword_length ha aa r (fun s hs => ⟨(hsp s hs).1, (hsp s hs).2.1⟩)
      e.1 (by rw [hsplen]; exact he1) e.2 (fun t ht => by rw [hsplen]; exact he2 t ht)).2
  rw [lr7sc_sameRefl_refl hq1 hq2 (l05nNC_gen_length1 hha haa k) (l05nNC_gen_length2 hha haa k) h6]
  exact hsword

private lemma lr7sc_gens_mem (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (r : GGDepAThreeSurv) (hslen : r.s.length = 6)
    (hsp : ∀ q ∈ lr7sc_sp ha aa r, q.1.length = 6 ∧ q.2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2)
    (hglen : r.g.length = 6)
    (hgall : ∀ x ∈ r.g, x.1 < 6 ∧ ∀ t ∈ x.2, t < 6)
    (hg6 : ∀ x < 6, (match r.g[x]? with
      | none => false
      | some e => ggDepAThreeSameRefl 3 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2)
          (ggDepANGen 3 6 ha aa x)) = true) :
    ∀ g ∈ lr7sc_gens ha aa, g ∈ Submonoid.closure (Set.range (lr7sc_S ha aa r)) := by
  intro g hg
  rcases hg with ⟨i, rfl⟩ | rfl
  · have hgen : ggDepANGen 3 6 ha aa i.1 = (ggDepANH 3 6 i.1, ggDepANA 3 6 i.1) := by
      simp only [ggDepANGen, if_pos (show i.1 + 1 < 6 by have := i.2; omega)]
    have hrew : ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i) =
        ggDepARefl (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa i.1).1)
          (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa i.1).2) := by
      rw [hgen, lr7sc_toZ_H (show i.1 + 1 < 6 by have := i.2; omega),
        lr7sc_toZ_A (show i.1 + 1 < 6 by have := i.2; omega)]
    change ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i) ∈
      Submonoid.closure (Set.range (lr7sc_S ha aa r))
    rw [hrew]
    exact lr7sc_gen_single_mem ha aa hha haa r hslen hsp hglen hgall hg6 i.1
      (by have := i.2; omega)
  · have hgen : ggDepANGen 3 6 ha aa 5 = (ha, aa) := by
      simp only [ggDepANGen, if_neg (show ¬ (5 + 1 < 6) by omega)]
    rw [show ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa) =
        ggDepARefl (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa 5).1)
          (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa 5).2) from by rw [hgen]]
    exact lr7sc_gen_single_mem ha aa hha haa r hslen hsp hglen hgall hg6 5 (by omega)

private def lr7sc_stateStep (ha aa : List ℕ)
    (st : List (List ℕ) × List (Module.End (ZMod 3) (GGDepAE 3 6))) (e : ℕ × ℕ) :
    List (List ℕ) × List (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  let g := ggDepANGen 3 6 ha aa e.2
  (st.1 ++ [ggDepANSub 3 (st.1.getD e.1 [])
      (ggDepANSmul 3 (ggDepANDot 3 g.2 (st.1.getD e.1 [])) g.1)],
   st.2 ++ [ggDepARefl (ggDepANToZ 3 6 g.1) (ggDepANToZ 3 6 g.2) * st.2.getD e.1 1])

private def lr7sc_vecStep (ha aa : List ℕ) (acc : List (List ℕ)) (e : ℕ × ℕ) :
    List (List ℕ) :=
  acc ++ [ggDepANSub 3 (acc.getD e.1 [])
    (ggDepANSmul 3 (ggDepANDot 3 (ggDepANGen 3 6 ha aa e.2).2 (acc.getD e.1 []))
      (ggDepANGen 3 6 ha aa e.2).1)]

private lemma lr7sc_fold_fst (ha aa : List ℕ) (o : List (ℕ × ℕ)) (v : List (List ℕ))
    (w : List (Module.End (ZMod 3) (GGDepAE 3 6))) :
    (o.foldl (lr7sc_stateStep ha aa) (v, w)).1 = o.foldl (lr7sc_vecStep ha aa) v := by
  induction o generalizing v w with
  | nil => rfl
  | cons e o ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _

private lemma lr7sc_orbit_eq (ha aa : List ℕ) (o : List (ℕ × ℕ)) :
    ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) o =
      o.foldl (lr7sc_vecStep ha aa) [ggDepANX 6] := by
  rfl

private lemma lr7sc_getD_append_singleton {α : Type*} (l : List α) (a d : α) {n : ℕ}
    (h : n = l.length) : (l ++ [a]).getD n d = a := by
  subst h
  rw [List.getD_append_right (l := l) (l' := [a]) (d := d) (n := l.length) (le_refl _),
    Nat.sub_self]
  rfl

private lemma lr7sc_fold_inv (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (o : List (ℕ × ℕ)) (v : List (List ℕ))
    (w : List (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hlen : v.length = w.length)
    (hvlen : ∀ k, k < v.length → (v.getD k []).length = 6)
    (hax : ∀ k, k < v.length → w.getD k 1 (ggDepAx 3 6) = ggDepANToZ 3 6 (v.getD k []))
    (hcl : ∀ k, k < w.length → w.getD k 1 ∈ Submonoid.closure (lr7sc_gens ha aa))
    (hpar : ∀ k, k < o.length → (o.getD k (0, 0)).1 < v.length + k)
    (hgen : ∀ k, k < o.length → (o.getD k (0, 0)).2 < 6) :
    (o.foldl (lr7sc_stateStep ha aa) (v, w)).1.length =
        (o.foldl (lr7sc_stateStep ha aa) (v, w)).2.length ∧
      (∀ k, k < (o.foldl (lr7sc_stateStep ha aa) (v, w)).1.length →
        ((o.foldl (lr7sc_stateStep ha aa) (v, w)).1.getD k []).length = 6) ∧
      (∀ k, k < (o.foldl (lr7sc_stateStep ha aa) (v, w)).1.length →
        (o.foldl (lr7sc_stateStep ha aa) (v, w)).2.getD k 1 (ggDepAx 3 6) =
          ggDepANToZ 3 6 ((o.foldl (lr7sc_stateStep ha aa) (v, w)).1.getD k [])) ∧
      (∀ k, k < (o.foldl (lr7sc_stateStep ha aa) (v, w)).2.length →
        (o.foldl (lr7sc_stateStep ha aa) (v, w)).2.getD k 1 ∈
          Submonoid.closure (lr7sc_gens ha aa)) := by
  induction o generalizing v w with
  | nil => exact ⟨hlen, hvlen, hax, hcl⟩
  | cons e o ih =>
      rw [List.foldl_cons]
      apply ih
      · simp only [lr7sc_stateStep, List.length_append, List.length_singleton]
        omega
      · intro k hk
        simp only [lr7sc_stateStep, List.length_append, List.length_singleton] at hk
        simp only [lr7sc_stateStep]
        by_cases hkv : k < v.length
        · rw [List.getD_append _ _ _ _ hkv]; exact hvlen k hkv
        · have hk' : k = v.length := by omega
          subst hk'
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
          simp only [List.getD_cons_zero]
          exact l05nNC_sub_length (hvlen e.1 (by have := hpar 0 (by simp); simpa using this))
            (l05nNC_smul_length (l05nNC_gen_length1 hha haa e.2))
      · intro k hk
        simp only [lr7sc_stateStep, List.length_append, List.length_singleton] at hk
        simp only [lr7sc_stateStep]
        by_cases hkv : k < v.length
        · rw [List.getD_append _ _ _ _ (by rw [← hlen]; exact hkv),
            List.getD_append _ _ _ _ hkv, hax k hkv]
        · have hk' : k = v.length := by omega
          subst hk'
          rw [lr7sc_getD_append_singleton w
                (ggDepARefl (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa e.2).1)
                  (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa e.2).2) * w.getD e.1 1) 1 hlen,
            lr7sc_getD_append_singleton v
                (ggDepANSub 3 (v.getD e.1 [])
                  (ggDepANSmul 3 (ggDepANDot 3 (ggDepANGen 3 6 ha aa e.2).2 (v.getD e.1 []))
                    (ggDepANGen 3 6 ha aa e.2).1)) [] rfl]
          have hpe : e.1 < v.length := by have := hpar 0 (by simp); simpa using this
          have hve : (v.getD e.1 []).length = 6 := hvlen e.1 hpe
          rw [show (ggDepARefl (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa e.2).1)
                (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa e.2).2) * w.getD e.1 1)
                (ggDepAx 3 6) =
              ggDepARefl (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa e.2).1)
                (ggDepANToZ 3 6 (ggDepANGen 3 6 ha aa e.2).2) (w.getD e.1 1 (ggDepAx 3 6))
              from rfl]
          rw [hax e.1 hpe]
          exact lr7sc_refl_toZ_sub (l05nNC_gen_length1 hha haa e.2)
            (l05nNC_gen_length2 hha haa e.2) hve
      · intro k hk
        simp only [lr7sc_stateStep, List.length_append, List.length_singleton] at hk
        simp only [lr7sc_stateStep]
        by_cases hkv : k < w.length
        · rw [List.getD_append _ _ _ _ hkv]; exact hcl k hkv
        · have hk' : k = w.length := by omega
          subst hk'
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
          simp only [List.getD_cons_zero]
          have hpe : e.1 < v.length := by have := hpar 0 (by simp); simpa using this
          have hpew : e.1 < w.length := by rwa [← hlen]
          exact Submonoid.mul_mem _ (l05nNC_gen_mem hha haa e.2) (hcl e.1 hpew)
      · intro k hk
        have hh := hpar (k + 1) (by simpa using hk)
        simp only [List.getD_cons_succ, List.length_append, List.length_singleton] at hh ⊢
        omega
      · intro k hk
        have hh := hgen (k + 1) (by simpa using hk)
        simp only [List.getD_cons_succ] at hh ⊢
        exact hh

private lemma lr7sc_orbit_data (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (r : GGDepAThreeSurv)
    (ho6 : ∀ k < r.o.length, (match r.o[k]? with
      | none => false
      | some e => decide (e.1 < k + 1) && decide (e.2 < 6)) = true)
    (horblen : (ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o).length = 72)
    (hkeynodup : (List.map (ggDepAThreeKey 3)
      (ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o)).Nodup) :
    ∃ w : Fin 72 → Module.End (ZMod 3) (GGDepAE 3 6),
      (∀ k, w k ∈ Submonoid.closure (lr7sc_gens ha aa)) ∧
      (∀ k, w k (ggDepAx 3 6) =
        ggDepANToZ 3 6 ((ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o).getD k.1 [])) ∧
      Function.Injective (fun k : Fin 72 => w k (ggDepAx 3 6)) := by
  have hrof : ∀ k < r.o.length, (r.o.getD k (0, 0)).1 < 1 + k ∧ (r.o.getD k (0, 0)).2 < 6 := by
    intro k hk
    have h6 := ho6 k hk
    rw [List.getElem?_eq_getElem (l := r.o) hk] at h6
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h6
    obtain ⟨h6a, h6b⟩ := h6
    rw [List.getD_eq_getElem (l := r.o) (d := (0, 0)) hk]
    exact ⟨by omega, h6b⟩
  have hvlen0 : ∀ k, k < ([ggDepANX 6] : List (List ℕ)).length →
      (([ggDepANX 6] : List (List ℕ)).getD k []).length = 6 := by
    intro k hk
    have : k = 0 := by simp at hk; omega
    subst this
    simp [ggDepANX]
  have hax0 : ∀ k, k < ([ggDepANX 6] : List (List ℕ)).length →
      ([1] : List (Module.End (ZMod 3) (GGDepAE 3 6))).getD k 1 (ggDepAx 3 6) =
        ggDepANToZ 3 6 (([ggDepANX 6] : List (List ℕ)).getD k []) := by
    intro k hk
    have : k = 0 := by simp at hk; omega
    subst this
    simp [lr7sc_toZ_X]
  have hcl0 : ∀ k, k < ([1] : List (Module.End (ZMod 3) (GGDepAE 3 6))).length →
      ([1] : List (Module.End (ZMod 3) (GGDepAE 3 6))).getD k 1 ∈
        Submonoid.closure (lr7sc_gens ha aa) := by
    intro k hk
    have : k = 0 := by simp at hk; omega
    subst this
    exact Submonoid.one_mem _
  have hpar0 : ∀ k, k < r.o.length →
      (r.o.getD k (0, 0)).1 < ([ggDepANX 6] : List (List ℕ)).length + k := by
    intro k hk; have := (hrof k hk).1; simpa using this
  have hgen0 : ∀ k, k < r.o.length → (r.o.getD k (0, 0)).2 < 6 := by
    intro k hk; exact (hrof k hk).2
  have hInv := lr7sc_fold_inv ha aa hha haa r.o [ggDepANX 6] [1] rfl hvlen0 hax0 hcl0 hpar0 hgen0
  set V := (r.o.foldl (lr7sc_stateStep ha aa) ([ggDepANX 6], [1])).1 with hV
  set W := (r.o.foldl (lr7sc_stateStep ha aa) ([ggDepANX 6], [1])).2 with hW
  have hVlen : V.length = W.length := hInv.1
  have hVvlen : ∀ k, k < V.length → (V.getD k []).length = 6 := hInv.2.1
  have hVax : ∀ k, k < V.length → W.getD k 1 (ggDepAx 3 6) = ggDepANToZ 3 6 (V.getD k []) :=
    hInv.2.2.1
  have hWcl : ∀ k, k < W.length → W.getD k 1 ∈ Submonoid.closure (lr7sc_gens ha aa) :=
    hInv.2.2.2
  have hVorbit : V = ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o := by
    rw [hV, lr7sc_fold_fst, ← lr7sc_orbit_eq]
  refine ⟨fun k => W.getD k.1 1, ?_, ?_, ?_⟩
  · intro k
    exact hWcl k.1 (by rw [← hVlen, hVorbit, horblen]; exact k.2)
  · intro k
    rw [hVax k.1 (by rw [hVorbit, horblen]; exact k.2), hVorbit]
  · intro i j hij
    have htoZ : ggDepANToZ 3 6
          ((ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o).getD i.1 []) =
        ggDepANToZ 3 6
          ((ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o).getD j.1 []) := by
      rw [← hVorbit]
      rw [← hVax i.1 (by rw [hVorbit, horblen]; exact i.2),
          ← hVax j.1 (by rw [hVorbit, horblen]; exact j.2)]
      exact hij
    have hvei : ((ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o).getD i.1 []).length = 6 := by
      rw [← hVorbit]; exact hVvlen i.1 (by rw [hVorbit, horblen]; exact i.2)
    have hvej : ((ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o).getD j.1 []).length = 6 := by
      rw [← hVorbit]; exact hVvlen j.1 (by rw [hVorbit, horblen]; exact j.2)
    have hkeyeq := lr7sc_key_eq_of_toZ_eq hvei hvej htoZ
    have hi' : i.1 < (List.map (ggDepAThreeKey 3)
        (ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o)).length := by
      rw [List.length_map, horblen]; exact i.2
    have hj' : j.1 < (List.map (ggDepAThreeKey 3)
        (ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o)).length := by
      rw [List.length_map, horblen]; exact j.2
    have heq : (List.map (ggDepAThreeKey 3)
          (ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o))[i.1] =
        (List.map (ggDepAThreeKey 3)
          (ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o))[j.1] := by
      rw [List.getElem_map, List.getElem_map]
      rw [List.getD_eq_getElem
            (l := ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o) (d := [])
            (by rw [horblen]; exact i.2),
          List.getD_eq_getElem
            (l := ggDepAThreeOrbit 3 6 (ggDepANGen 3 6 ha aa) r.o) (d := [])
            (by rw [horblen]; exact j.2)] at hkeyeq
      exact hkeyeq
    exact Fin.ext ((List.Nodup.getElem_inj_iff hkeynodup (i := i.1) (j := j.1)
      (hi := hi') (hj := hj')).mp heq)

theorem ggDepAThreeSurvTest_sound (ha aa : List ℕ) (hha : ha.length = 6) (haa : aa.length = 6)
    (hdot : ggDepANDot 3 aa ha = 2 % 3) (r : GGDepAThreeSurv)
    (h : ggDepAThreeSurvTest 3 6 ha aa r = true) :
    GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
        ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
      {ggDepARefl (ggDepANToZ 3 6 ha) (ggDepANToZ 3 6 aa)}) := by
  rw [ggDepAThreeSurvTest] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨hslen, hglen, holen, hsall, hgall, ho6, hspall, hpair, hg6, horblen, hkeynodup⟩ := h
  have hspall' : ∀ x ∈ lr7sc_sp ha aa r, (ggDepANDot 3 x.2 x.1 == 2 % 3) = true := by
    simpa [lr7sc_sp] using hspall
  have hpair' : ∀ x < 6, ∀ y < 6,
      (ggDepANDot 3 ((lr7sc_sp ha aa r).getD x ([], [])).2
        ((lr7sc_sp ha aa r).getD y ([], [])).1 == ggDepAThreeE6Res 3 x y) = true := by
    simpa [lr7sc_sp] using hpair
  have hg6' : ∀ x < 6, (match r.g[x]? with
      | none => false
      | some e => ggDepAThreeSameRefl 3 (ggDepAThreeSWord 3 (lr7sc_sp ha aa r) e.1 e.2)
          (ggDepANGen 3 6 ha aa x)) = true := by
    exact hg6
  have hsall' : ∀ x ∈ r.s,
      (x.1 < 6 ∧ ∀ t ∈ x.2.1, t < 6) ∧ (x.2.2 == 1 || x.2.2 == 3 - 1) = true := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hsall x hx
    exact ⟨⟨h1, h2⟩, h3⟩
  have hspmem : ∀ q ∈ lr7sc_sp ha aa r, q.1.length = 6 ∧ q.2.length = 6 ∧
      ggDepAdot (ggDepANToZ 3 6 q.2) (ggDepANToZ 3 6 q.1) = 2 := by
    intro q hq
    have := lr7sc_sp_mem ha aa hha haa hdot r hslen hsall' hspall' q hq
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hprops := lr7sc_sp_props ha aa hha haa hdot r hslen hsall' hspall'
  obtain ⟨w, hwcl, hwax, hwinj⟩ := lr7sc_orbit_data ha aa hha haa r ho6 horblen hkeynodup
  refine ⟨lr7sc_S ha aa r, w, ?_, ?_, ?_, ?_, hwcl, hwinj⟩
  · intro i; exact (hprops i).2.2.2
  · intro i
    exact ⟨ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).1,
      ggDepANToZ 3 6 ((lr7sc_sp ha aa r).getD i.1 ([], [])).2, (hprops i).2.2.1, rfl⟩
  · exact lr7sc_coxeter ha aa hha haa r hslen hspmem hpair'
  · exact lr7sc_gens_mem ha aa hha haa r hslen hspmem hglen hgall hg6'

theorem ggDepAThree_cells6_of_check (data : GGDepANData) (sdata : GGDepAThreeSData)
    (h : ggDepAThreeCheck 3 6 data sdata = true) : GGDepAThreeCells6 := by
  intro b c0 m n hpat ha aa hpair hdot hx
  have hcore := ggDepAThreeCheck_core (p := 3) (N := 6) (by omega) (⟨2, rfl⟩) (by omega)
    data sdata h
  rcases hcore b c0 m n hpat ha aa hpair hdot hx with
    ⟨g, hg, htv⟩ | ⟨hl, al, r, _hr, hhl, hal, htoZ1, htoZ2, htest⟩
  · exact Or.inl ⟨g, hg, htv⟩
  · refine Or.inr ?_
    have hdotl : ggDepANDot 3 al hl = 2 % 3 := by
      have hh := ggDepANDot_cast (p := 3) (N := 6) al hl hal hhl
      rw [htoZ2, htoZ1, hdot] at hh
      have h2 : ((ggDepANDot 3 al hl : ℕ) : ZMod 3) = ((2 % 3 : ℕ) : ZMod 3) := by
        rw [ZMod.natCast_mod]; exact hh
      rw [ZMod.natCast_eq_natCast_iff'] at h2
      simpa [ggDepANDot, Nat.mod_mod] using h2
    have hsnd := ggDepAThreeSurvTest_sound hl al hhl hal hdotl r htest
    rwa [htoZ1, htoZ2] at hsnd

end CFSG.StandardType
