module

public import Certificates.Certificate550881
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiSeven
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open CFSG.ClassicalInvolution.Solomon73

set_option maxRecDepth 100000 in
theorem commute_pairInv_of_conj : ∀ π : Perm (Fin 6),
    (∀ i, (π * pairInv * π⁻¹) i = i ∨ (π * pairInv * π⁻¹) i = partner i) →
    π * pairInv = pairInv * π := by decide +kernel

theorem swapsOf_one : swapsOf (fun _ => 1) = pairInv := by decide

theorem mem_X0W_of_normalizes {a : Wr 6} (ha : a ∈ Wsub) (h : ∀ b ∈ SW, a * b * a⁻¹ ∈ SW) :
    a ∈ X0W := by
  refine ⟨ha, ?_⟩
  have h1 := (mem_SW.mp (h _ (cSp_mem_SW (0, fun _ => 1)))).2
  have hperm : (a * cSp (0, fun _ => 1) * a⁻¹).perm = a.perm * pairInv * a.perm⁻¹ := by
    rw [mul_perm, mul_perm, inv_perm]
    congr 2
    exact swapsOf_one
  rw [hperm] at h1
  exact commute_pairInv_of_conj _ h1

set_option maxRecDepth 100000 in
theorem card_centralizer_pairInv :
    Fintype.card {σ : Perm (Fin 6) // σ * pairInv = pairInv * σ} = 48 := by decide +kernel

theorem card_X0W : Nat.card X0W = 1536 := by
  have h1 : Nat.card X0W = Nat.card ({v : Fin 6 → ZMod 2 // ∑ i, v i = 0} ×
      {σ : Perm (Fin 6) // σ * pairInv = pairInv * σ}) :=
    Nat.card_congr
      { toFun := fun a => (⟨(a : Wr 6).vec, a.2.1⟩, ⟨(a : Wr 6).perm, a.2.2⟩)
        invFun := fun p => ⟨⟨p.1.1, p.2.1⟩, p.1.2, p.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0} = 32 := by
    rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [h1, Nat.card_prod, h2, Nat.card_eq_fintype_card, card_centralizer_pairInv]

theorem X0W_le_Wsub : X0W ≤ Wsub := fun _ ha => ha.1

@[expose] def xiP : Perm (Fin 6) := swap 0 4 * swap 0 2 * (swap 1 5 * swap 1 3)

theorem vec_decomp : ∀ u : Fin 6 → ZMod 2, ∑ i, u i = 0 → ∃ c : Fin 3 → ZMod 2, ∃ b₁ b₂ : Bool,
    u = (fun i => c (blk i)) + ((if b₁ then v6 [0, 2] else 0) + (if b₂ then v6 [0, 4] else 0)) := by
  decide

set_option maxRecDepth 100000 in
theorem perm_decomp : ∀ π : Perm (Fin 6), π * pairInv = pairInv * π →
    ∃ d : Fin 3 → ZMod 2, ∃ b : Bool, ∃ k : Fin 3,
      π = swapsOf d * ((if b then tauP else 1) * xiP ^ (k : ℕ)) := by
  decide +kernel

theorem wp_mul (σ τ : Perm (Fin 6)) : wp (σ * τ) = wp σ * wp τ :=
  Wr.ext (funext fun i => by show (0 : ZMod 2) = 0 + 0; rw [add_zero]) rfl

theorem wp_pow (σ : Perm (Fin 6)) (k : ℕ) : wp (σ ^ k) = wp σ ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, wp_mul, ih, pow_succ]

theorem wXi_eq : wXi = wp xiP := rfl

theorem cSp_0d (d : Fin 3 → ZMod 2) : cSp (0, d) = wp (swapsOf d) := rfl

theorem vec_split : ∀ (c : Fin 3 → ZMod 2) (b₁ b₂ : Bool),
    (⟨(fun i => c (blk i)) + ((if b₁ then v6 [0, 2] else 0) + (if b₂ then v6 [0, 4] else 0)), 1⟩ :
      Wr 6) = cSp (c, 0) * ((if b₁ then wMu else 1) * (if b₂ then wMu' else 1)) := by
  decide

theorem wp_ite (b : Bool) : wp (if b then tauP else 1) = if b then wTau else 1 := by
  cases b <;> rfl

theorem X0W_decomp {a : Wr 6} (ha : a ∈ X0W) : ∃ c d : Fin 3 → ZMod 2, ∃ b₁ b₂ b : Bool,
    ∃ k : Fin 3, a = cSp (c, 0) * ((if b₁ then wMu else 1) * (if b₂ then wMu' else 1)) *
      (cSp (0, d) * ((if b then wTau else 1) * wXi ^ (k : ℕ))) := by
  obtain ⟨u, π⟩ := a
  obtain ⟨c, b₁, b₂, hu⟩ := vec_decomp u ha.1
  obtain ⟨d, b, k, hπ⟩ := perm_decomp π ha.2
  refine ⟨c, d, b₁, b₂, b, k, ?_⟩
  rw [mk_eq_vec_mul_wp, hu, hπ, vec_split, wp_mul, wp_mul, wp_ite, wXi_eq, ← wp_pow, cSp_0d]

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

theorem mem_XN_iff (x : G) : x ∈ Y.XN ↔ x ∈ Y.lift X0W := by
  rw [Y.mem_lift]
  constructor
  · rintro ⟨hxN, hxC⟩
    refine ⟨hxC, mem_X0W_of_normalizes (Y.ϑ ⟨x, hxC⟩).2 fun b hb => ?_⟩
    obtain ⟨c, rfl⟩ := mem_SW_iff.mp hb
    have h1 : x * Y.σA c * x⁻¹ ∈ Y.A := Y.conj_mem_A hxN (Y.σA_mem_A c)
    obtain ⟨hC', hS⟩ := Y.mem_lift.mp h1
    have h2 : (Y.ϑ ⟨x * Y.σA c * x⁻¹, hC'⟩ : Wr 6) =
        (Y.ϑ ⟨x, hxC⟩ : Wr 6) * cSp c * (Y.ϑ ⟨x, hxC⟩ : Wr 6)⁻¹ := by
      have e : (⟨x * Y.σA c * x⁻¹, hC'⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨x, hxC⟩ * ⟨Y.σA c, Y.σA_mem_C c⟩ * (⟨x, hxC⟩)⁻¹ := rfl
      rw [e]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Y.ϑ_σA]
    rw [h2] at hS
    exact hS
  · rintro ⟨hxC, hX⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hxC⟩
    have key : ∀ (y : G) (hy : y ∈ Subgroup.centralizer ({z} : Set G)),
        (Y.ϑ ⟨y, hy⟩ : Wr 6) ∈ X0W → ∀ a ∈ Y.A, y * a * y⁻¹ ∈ Y.A := by
      intro y hy hyX a ha
      obtain ⟨haC, haS⟩ := Y.mem_lift.mp ha
      refine Y.mem_lift.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy haC)
        (Subgroup.inv_mem _ hy), ?_⟩
      have e : (⟨y * a * y⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy haC)
          (Subgroup.inv_mem _ hy)⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨y, hy⟩ * ⟨a, haC⟩ * (⟨y, hy⟩)⁻¹ := rfl
      rw [e]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      exact conj_mem_SW_of_mem_X0W hyX haS
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact key x hxC hX a
    · intro ha
      have hinv : (Y.ϑ ⟨x⁻¹, Subgroup.inv_mem _ hxC⟩ : Wr 6) ∈ X0W := by
        rw [Y.ϑ_inv_coe hxC]
        exact X0W.inv_mem hX
      have := key _ _ hinv _ ha
      rwa [show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group] at this

theorem XN_eq : Y.XN = Y.lift X0W := by
  ext x
  exact Y.mem_XN_iff x

theorem card_XN : Nat.card Y.XN = 1536 := by
  rw [Y.XN_eq, Y.card_lift X0W_le_Wsub, card_X0W]

end YData

@[expose] def bW : Fin 7 → SC :=
  ![sc [0, 1, 2], sc [1, 2, 3], sc [0, 2, 4], sc [0, 1, 5], sc [0, 1, 2, 5], sc [0, 1, 2, 4],
    sc [0, 1, 2, 3]]

theorem mem_Omega_iff : ∀ c : SC, c ∈ scOrb 0 ∪ scOrb 6 ↔ ∃ i, bW i = c := by decide

theorem bW_injective : Function.Injective bW := by
  intro i j h
  revert i j
  decide

@[expose] def bIdx (c : SC) : Fin 7 := ((List.finRange 7).find? fun i => bW i = c).getD 0

theorem bIdx_bW : ∀ i, bIdx (bW i) = i := by decide

theorem bW_bIdx {c : SC} (hc : c ∈ scOrb 0 ∪ scOrb 6) : bW (bIdx c) = c := by
  obtain ⟨i, rfl⟩ := (mem_Omega_iff c).mp hc
  rw [bIdx_bW]

theorem bW_zero : bW 0 = sc [0, 1, 2] := rfl

theorem card_Omega : (scOrb 0 ∪ scOrb 6).card = 7 := by decide

theorem actOf_bW : (∀ i, bIdx (actMu (bW i)) = s7Mu i) ∧ (∀ i, bIdx (actMu' (bW i)) = s7Mu' i) ∧
    (∀ i, bIdx (actTau (bW i)) = s7Tau i) ∧ (∀ i, bIdx (actXi (bW i)) = s7Xi i) := by decide

@[expose] def Lc (c : Perm (Fin 7)) : Subgroup (Perm (Fin 7)) :=
  l32.comap (MulAut.conj c).toMonoidHom

theorem mem_Lc {c g : Perm (Fin 7)} : g ∈ Lc c ↔ InL32 (c * g * c⁻¹) := Iff.rfl

set_option maxRecDepth 100000 in
theorem gens_mem_Lc : (s7Mu ∈ Lc s7c1 ∧ s7Mu' ∈ Lc s7c1 ∧ s7Tau ∈ Lc s7c1 ∧ s7Xi ∈ Lc s7c1) ∧
    (s7Mu ∈ Lc s7c2 ∧ s7Mu' ∈ Lc s7c2 ∧ s7Tau ∈ Lc s7c2 ∧ s7Xi ∈ Lc s7c2) := by
  simp only [mem_Lc]
  decide

theorem s7Check_holds : s7Check () = true :=
  Certificates.certificate550881

theorem s7Check_spec (g : Perm (Fin 7)) (hg : g 0 ≠ 0) :
    InL32 (s7c1 * g * s7c1⁻¹) ∨ InL32 (s7c2 * g * s7c2⁻¹) ∨
      ∃ w ∈ s7Words (), IsOrd5 (evalWord (s7Letters g) w) := by
  have h : s7CheckW (s7Words ()) (s7Perms ()) = true := s7Check_holds
  have hmem : g ∈ s7Perms () := mem_permsOfList_of_mem fun x _ => List.mem_finRange x
  have h1 : s7Ok (s7Words ()) g = true := List.all_eq_true.mp h g hmem
  simp only [s7Ok, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h1
  rcases h1 with ((h0 | h1) | h2) | h3
  · exact absurd h0 hg
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

theorem evalWord_map {H : Type*} [Group H] (f : H →* Perm (Fin 7)) (hs : Fin 5 → H) :
    ∀ w : List (Fin 5), evalWord (fun a => f (hs a)) w = f (w.map hs).prod
  | [] => by simp [evalWord]
  | a :: w => by simp [evalWord, evalWord_map f hs w]

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

section Std

variable (hstd : Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 6)
include hstd

theorem mem_conj_z_iff (c : SC) : Y.σA c ∈ conjSet Y.NA z ↔ c ∈ scOrb 0 ∪ scOrb 6 := by
  rw [← hstd, Y.mem_coord]

theorem card_NA : Nat.card Y.NA = 10752 := by
  have e := ncard_conjSet_mul Y.NA z
  rw [← Y.card_coord (conjSet_normalizer_subset Y.z_mem_A), hstd, card_Omega] at e
  have e' : 7 * Nat.card Y.XN = Nat.card Y.NA := e
  rw [← e', Y.card_XN]

theorem cc_bW_mem {n : G} (hn : n ∈ Y.NA) (i : Fin 7) : Y.cc n (bW i) ∈ scOrb 0 ∪ scOrb 6 := by
  rw [← Y.mem_conj_z_iff hstd, Y.σA_cc hn]
  exact conj_mem_conjSet ((Y.mem_conj_z_iff hstd _).mpr ((mem_Omega_iff _).mpr ⟨i, rfl⟩)) hn

omit hstd in
@[expose] noncomputable def pf (n : G) (i : Fin 7) : Fin 7 := bIdx (Y.cc n (bW i))

theorem bW_pf {n : G} (hn : n ∈ Y.NA) (i : Fin 7) : bW (Y.pf n i) = Y.cc n (bW i) :=
  bW_bIdx (Y.cc_bW_mem hstd hn i)

theorem pf_mul {n m : G} (hn : n ∈ Y.NA) (hm : m ∈ Y.NA) (i : Fin 7) :
    Y.pf (n * m) i = Y.pf n (Y.pf m i) := by
  apply bW_injective
  rw [Y.bW_pf hstd (Y.NA.mul_mem hn hm), Y.cc_mul hn hm, ← Y.bW_pf hstd hm, Y.bW_pf hstd hn]

theorem pf_one (i : Fin 7) : Y.pf 1 i = i := by
  apply bW_injective
  rw [Y.bW_pf hstd Y.NA.one_mem, Y.cc_one]

@[expose] noncomputable def permHom : ↥Y.NA →* Perm (Fin 7) where
  toFun n :=
    { toFun := Y.pf n
      invFun := Y.pf (n⁻¹ : ↥Y.NA)
      left_inv := fun i => by
        rw [← Y.pf_mul hstd (n⁻¹ : ↥Y.NA).2 n.2]
        simp only [Subgroup.coe_inv, inv_mul_cancel]
        exact Y.pf_one hstd i
      right_inv := fun i => by
        rw [← Y.pf_mul hstd n.2 (n⁻¹ : ↥Y.NA).2]
        simp only [Subgroup.coe_inv, mul_inv_cancel]
        exact Y.pf_one hstd i }
  map_one' := Equiv.ext fun i => Y.pf_one hstd i
  map_mul' n m := Equiv.ext fun i => Y.pf_mul hstd n.2 m.2 i

theorem permHom_apply (n : ↥Y.NA) (i : Fin 7) : Y.permHom hstd n i = Y.pf n i := rfl

theorem bW_permHom (n : ↥Y.NA) (i : Fin 7) : bW (Y.permHom hstd n i) = Y.cc n (bW i) :=
  Y.bW_pf hstd n.2 i

omit hstd in
theorem cc_of {g : Wr 6} (hg : g ∈ Wsub) {f : SC → SC} (hf : ∀ x, g * cSp x * g⁻¹ = cSp (f x))
    (c : SC) : Y.cc (Y.ι ⟨g, hg⟩) c = f c := by
  rw [cc, Y.conj_σA_of hg hf, Y.coordOf_σA]

omit hstd in
theorem cc_of_mem_A {a : G} (ha : a ∈ Y.A) (c : SC) : Y.cc a c = c := by
  rw [cc, Y.A_comm ha (Y.σA_mem_A c), mul_assoc, mul_inv_cancel, mul_one, Y.coordOf_σA]

theorem pf_of_mem_A {a : G} (ha : a ∈ Y.A) (i : Fin 7) : Y.pf a i = i := by
  rw [pf, Y.cc_of_mem_A ha, bIdx_bW]

omit hstd in
theorem ιMu_mem : Y.ι ⟨wMu, wMu_mem_Wsub⟩ ∈ Y.NA := Y.gens_mem_normalizer.1

omit hstd in
theorem ιMu'_mem : Y.ι ⟨wMu', wMu'_mem_Wsub⟩ ∈ Y.NA := Y.gens_mem_normalizer.2.1

omit hstd in
theorem ιTau_mem : Y.ι ⟨wTau, wTau_mem_Wsub⟩ ∈ Y.NA := Y.gens_mem_normalizer.2.2.1

omit hstd in
theorem ιXi_mem : Y.ι ⟨wXi, wXi_mem_Wsub⟩ ∈ Y.NA := Y.gens_mem_normalizer.2.2.2

theorem permHom_gens :
    Y.permHom hstd ⟨_, Y.ιMu_mem⟩ = s7Mu ∧ Y.permHom hstd ⟨_, Y.ιMu'_mem⟩ = s7Mu' ∧
      Y.permHom hstd ⟨_, Y.ιTau_mem⟩ = s7Tau ∧ Y.permHom hstd ⟨_, Y.ιXi_mem⟩ = s7Xi := by
  obtain ⟨h1, h2, h3, h4⟩ := actOf_bW
  refine ⟨Equiv.ext fun i => ?_, Equiv.ext fun i => ?_, Equiv.ext fun i => ?_,
    Equiv.ext fun i => ?_⟩
  · rw [permHom_apply, pf, Y.cc_of wMu_mem_Wsub conj_cS_wMu, h1]
  · rw [permHom_apply, pf, Y.cc_of wMu'_mem_Wsub conj_cS_wMu', h2]
  · rw [permHom_apply, pf, Y.cc_of wTau_mem_Wsub conj_cS_wTau, h3]
  · rw [permHom_apply, pf, Y.cc_of wXi_mem_Wsub conj_cS_wXi, h4]

@[expose] noncomputable def KL (c : Perm (Fin 7)) : Subgroup G :=
  ((Lc c).comap (Y.permHom hstd)).map Y.NA.subtype

theorem mem_KL {c : Perm (Fin 7)} {g : G} (hg : g ∈ Y.NA) :
    g ∈ Y.KL hstd c ↔ Y.permHom hstd ⟨g, hg⟩ ∈ Lc c := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hn
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit hstd in
theorem A_le_NA : Y.A ≤ Y.NA := Subgroup.le_normalizer

@[expose] noncomputable def KW (c : Perm (Fin 7)) : Subgroup (Wr 6) :=
  ((Y.KL hstd c).comap Y.ι).map Wsub.subtype

theorem mem_KW {c : Perm (Fin 7)} {w : Wr 6} :
    w ∈ Y.KW hstd c ↔ ∃ hw : w ∈ Wsub, Y.ι ⟨w, hw⟩ ∈ Y.KL hstd c := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hw, h⟩
    exact ⟨⟨w, hw⟩, h, rfl⟩

theorem permHom_mem_of_mem_XN {c : Perm (Fin 7)} (hc : c = s7c1 ∨ c = s7c2) (n : ↥Y.NA)
    (hn : (n : G) ∈ Subgroup.centralizer ({z} : Set G)) : Y.permHom hstd n ∈ Lc c := by
  have hgens : s7Mu ∈ Lc c ∧ s7Mu' ∈ Lc c ∧ s7Tau ∈ Lc c ∧ s7Xi ∈ Lc c := by
    rcases hc with rfl | rfl
    exacts [gens_mem_Lc.1, gens_mem_Lc.2]
  obtain ⟨g1, g2, g3, g4⟩ := hgens
  obtain ⟨p1, p2, p3, p4⟩ := Y.permHom_gens hstd
  have hS : ∀ x : SC, cSp x ∈ Y.KW hstd c := by
    intro x
    refine (Y.mem_KW hstd).mpr ⟨SW_le_Wsub (cSp_mem_SW x), ?_⟩
    have ha : Y.ι ⟨cSp x, SW_le_Wsub (cSp_mem_SW x)⟩ ∈ Y.A := Y.ι_mem_lift (cSp_mem_SW x)
    refine (Y.mem_KL hstd (Y.A_le_NA ha)).mpr ?_
    have h1 : Y.permHom hstd ⟨_, Y.A_le_NA ha⟩ = 1 := Equiv.ext fun i => Y.pf_of_mem_A hstd ha i
    rw [h1]
    exact (Lc c).one_mem
  have hMu : wMu ∈ Y.KW hstd c :=
    (Y.mem_KW hstd).mpr ⟨wMu_mem_Wsub, (Y.mem_KL hstd Y.ιMu_mem).mpr (p1 ▸ g1)⟩
  have hMu' : wMu' ∈ Y.KW hstd c :=
    (Y.mem_KW hstd).mpr ⟨wMu'_mem_Wsub, (Y.mem_KL hstd Y.ιMu'_mem).mpr (p2 ▸ g2)⟩
  have hTau : wTau ∈ Y.KW hstd c :=
    (Y.mem_KW hstd).mpr ⟨wTau_mem_Wsub, (Y.mem_KL hstd Y.ιTau_mem).mpr (p3 ▸ g3)⟩
  have hXi : wXi ∈ Y.KW hstd c :=
    (Y.mem_KW hstd).mpr ⟨wXi_mem_Wsub, (Y.mem_KL hstd Y.ιXi_mem).mpr (p4 ▸ g4)⟩
  have hite : ∀ (b : Bool) {w : Wr 6}, w ∈ Y.KW hstd c → (if b then w else 1) ∈ Y.KW hstd c := by
    intro b w hw
    cases b
    · exact (Y.KW hstd c).one_mem
    · exact hw
  have hX : (Y.ϑ ⟨n, hn⟩ : Wr 6) ∈ X0W :=
    ((Y.mem_lift.mp ((Y.mem_XN_iff n).mp ⟨n.2, hn⟩)).2)
  obtain ⟨cv, d, b₁, b₂, b, k, hdec⟩ := X0W_decomp hX
  have hW : (Y.ϑ ⟨n, hn⟩ : Wr 6) ∈ Y.KW hstd c := by
    rw [hdec]
    exact (Y.KW hstd c).mul_mem ((Y.KW hstd c).mul_mem (hS _) ((Y.KW hstd c).mul_mem
      (hite b₁ hMu) (hite b₂ hMu'))) ((Y.KW hstd c).mul_mem (hS _) ((Y.KW hstd c).mul_mem
        (hite b hTau) ((Y.KW hstd c).pow_mem hXi _)))
  obtain ⟨hw, hK⟩ := (Y.mem_KW hstd).mp hW
  rw [Subtype.coe_eta, Y.ι_ϑ] at hK
  exact (Y.mem_KL hstd n.2).mp hK

theorem permHom_zero_iff (n : ↥Y.NA) :
    Y.permHom hstd n 0 = 0 ↔ (n : G) ∈ Subgroup.centralizer ({z} : Set G) := by
  have hz0 : Y.σA (bW 0) = z := by rw [bW_zero, sc012_eq, Y.σA_one_zero]
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg Y.σA (Y.bW_permHom hstd n 0)
    rw [h, Y.σA_cc n.2, hz0] at h1
    calc (n : G) * z = ((n : G) * z * (n : G)⁻¹) * n := by group
      _ = z * n := by rw [← h1]
  · intro h
    apply bW_injective
    apply Y.σA_injective
    rw [Y.bW_permHom hstd n 0, Y.σA_cc n.2, hz0, h, mul_inv_cancel_right]

@[expose] noncomputable def lettersN (n : ↥Y.NA) : Fin 5 → ↥Y.NA :=
  ![⟨_, Y.ιMu_mem⟩, ⟨_, Y.ιMu'_mem⟩, ⟨_, Y.ιTau_mem⟩, ⟨_, Y.ιXi_mem⟩, n]

theorem letters_eq (n : ↥Y.NA) :
    (fun a => Y.permHom hstd (Y.lettersN n a)) = s7Letters (Y.permHom hstd n) := by
  obtain ⟨p1, p2, p3, p4⟩ := Y.permHom_gens hstd
  funext a
  fin_cases a
  exacts [p1, p2, p3, p4, rfl]

theorem permHom_mem_union (n : ↥Y.NA) :
    Y.permHom hstd n ∈ Lc s7c1 ∨ Y.permHom hstd n ∈ Lc s7c2 := by
  by_cases h0 : Y.permHom hstd n 0 = 0
  · exact Or.inl (Y.permHom_mem_of_mem_XN hstd (Or.inl rfl) n ((Y.permHom_zero_iff hstd n).mp h0))
  · rcases s7Check_spec _ h0 with h | h | ⟨w, -, hw⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [← Y.letters_eq hstd n, evalWord_map] at hw
      have ho : orderOf (Y.permHom hstd (w.map (Y.lettersN n)).prod) = 5 :=
        orderOf_eq_prime hw.1 hw.2
      have h5 : 5 ∣ Nat.card Y.NA :=
        (ho ▸ orderOf_map_dvd _ _).trans (orderOf_dvd_natCard _)
      rw [Y.card_NA hstd] at h5
      norm_num at h5

theorem exists_perm_l32 :
    ∃ c : Perm (Fin 7), (c = s7c1 ∨ c = s7c2) ∧ ∀ n : ↥Y.NA, Y.permHom hstd n ∈ Lc c := by
  by_cases h1 : ∀ n, Y.permHom hstd n ∈ Lc s7c1
  · exact ⟨s7c1, Or.inl rfl, h1⟩
  by_cases h2 : ∀ n, Y.permHom hstd n ∈ Lc s7c2
  · exact ⟨s7c2, Or.inr rfl, h2⟩
  exfalso
  push Not at h1 h2
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  have hn1' := (Y.permHom_mem_union hstd n1).resolve_left hn1
  have hn2' := (Y.permHom_mem_union hstd n2).resolve_right hn2
  rcases Y.permHom_mem_union hstd (n1 * n2) with h | h
  · apply hn1
    have := (Lc s7c1).mul_mem h ((Lc s7c1).inv_mem hn2')
    rwa [map_mul, mul_inv_cancel_right] at this
  · apply hn2
    have := (Lc s7c2).mul_mem ((Lc s7c2).inv_mem hn1') h
    rwa [map_mul, inv_mul_cancel_left] at this

end Std

end YData

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
