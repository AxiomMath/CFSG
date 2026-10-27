module

public import CFSG.Quasithin.H13.VolIAltCover
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm
public import CFSG.Quasithin.Vol2.Ch3B513NC1Lin

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

variable {n : ℕ}

@[expose] def evenOnVec (i j k : Fin n) (p : ZMod 2 × ZMod 2) : PermMod n :=
  Multiplicative.ofAdd (Pi.single i p.1 + Pi.single j p.2 + Pi.single k (p.1 + p.2))

theorem toAdd_evenOnVec (i j k : Fin n) (p : ZMod 2 × ZMod 2) (l : Fin n) :
    Multiplicative.toAdd (evenOnVec i j k p) l =
      (if l = i then p.1 else 0) + (if l = j then p.2 else 0) +
        (if l = k then p.1 + p.2 else 0) := by
  simp only [evenOnVec, toAdd_ofAdd, Pi.add_apply, Pi.single_apply]

theorem card_evenOn {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (evenOn i j k).card = 4 := by
  classical
  have hinj : Function.Injective (evenOnVec i j k) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have hi := congrArg (fun x : PermMod n => Multiplicative.toAdd x i) h
    have hj := congrArg (fun x : PermMod n => Multiplicative.toAdd x j) h
    simp only [toAdd_evenOnVec, if_neg hij, if_neg hik, if_neg hij.symm,
      if_neg hjk, add_zero, zero_add] at hi hj
    exact Prod.ext hi hj
  have himg : evenOn i j k = Finset.univ.image (evenOnVec i j k) := by
    ext x
    simp only [evenOn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h0, hs⟩
      refine ⟨(Multiplicative.toAdd x i, Multiplicative.toAdd x j), ?_⟩
      apply Multiplicative.toAdd.injective
      funext l
      rw [toAdd_evenOnVec]
      by_cases hli : l = i
      · subst hli
        simp [hij, hik]
      by_cases hlj : l = j
      · subst hlj
        simp [hij.symm, hjk]
      by_cases hlk : l = k
      · subst hlk
        rw [if_neg hli, if_neg hlj, if_pos rfl, zero_add, zero_add]
        have h1 : Multiplicative.toAdd x l =
            -(Multiplicative.toAdd x i + Multiplicative.toAdd x j) :=
          eq_neg_of_add_eq_zero_right hs
        rw [h1]
        exact (ZMod.neg_eq_self_mod_two _).symm
      · simp only [if_neg hli, if_neg hlj, if_neg hlk, add_zero]
        exact (h0 l hli hlj hlk).symm
    · rintro ⟨p, -, rfl⟩
      refine ⟨fun l hli hlj hlk => ?_, ?_⟩
      · simp only [toAdd_evenOnVec, if_neg hli, if_neg hlj, if_neg hlk, add_zero]
      · simp only [toAdd_evenOnVec, if_neg hij, if_neg hik, if_neg hij.symm,
          if_neg hjk, if_neg hik.symm, if_neg hjk.symm, add_zero, zero_add]
        have h2 : (2 : ZMod 2) = 0 := rfl
        calc p.1 + p.2 + (p.1 + p.2) = 2 * (p.1 + p.2) := by ring
          _ = 0 := by rw [h2, zero_mul]
  rw [himg, Finset.card_image_of_injective _ hinj]
  rfl

theorem comm_mem_evenOn_tri {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (m : PermMod n) : G6.permAct n (GL83.PiGen.tri a b c) m * m⁻¹ ∈ evenOn a b c := by
  classical
  set σ := GL83.PiGen.tri a b c with hσ
  have hσa : σ⁻¹ a = c := by
    rw [Perm.inv_eq_iff_eq, hσ, GL83.PiGen.tri_apply_c hac hbc]
  have hσb : σ⁻¹ b = a := by
    rw [Perm.inv_eq_iff_eq, hσ, GL83.PiGen.tri_apply_a hab hbc]
  have hσc : σ⁻¹ c = b := by
    rw [Perm.inv_eq_iff_eq, hσ, GL83.PiGen.tri_apply_b]
  have hσl : ∀ l, l ≠ a → l ≠ b → l ≠ c → σ⁻¹ l = l := by
    intro l hla hlb hlc
    rw [Perm.inv_eq_iff_eq, hσ, GL83.PiGen.tri, Perm.mul_apply, swap_apply_of_ne_of_ne hla hlb,
      swap_apply_of_ne_of_ne hla hlc]
  simp only [evenOn, Finset.mem_filter, Finset.mem_univ, true_and, toAdd_mul, toAdd_inv,
    Pi.add_apply, Pi.neg_apply, G6.permAct_apply]
  refine ⟨fun l hla hlb hlc => by rw [hσl l hla hlb hlc]; exact add_neg_cancel _, ?_⟩
  rw [hσa, hσb, hσc]
  have key : ∀ x y z : ZMod 2, z + -x + (x + -y) + (y + -z) = 0 := fun x y z => by abel
  exact key _ _ _

@[expose] def altChainPt (n i : ℕ) : ℕ := min (2 * i) (n - 3)

theorem altChainPt_add_two_lt (hn : 3 ≤ n) (i : ℕ) : altChainPt n i + 2 < n := by
  unfold altChainPt; omega

@[expose] def altChainFin (hn : 3 ≤ n) (i : ℕ) (d : Fin 3) : Fin n :=
  ⟨altChainPt n i + d, by have := altChainPt_add_two_lt hn i; omega⟩

@[expose] def altChainSet (hn : 3 ≤ n) (i : Fin (n / 2)) : Set (Fin n) :=
  {altChainFin hn i 0, altChainFin hn i 1, altChainFin hn i 2}

@[expose] def altChainTri (hn : 3 ≤ n) (i : Fin (n / 2)) : Perm (Fin n) :=
  GL83.PiGen.tri (altChainFin hn i 0) (altChainFin hn i 1) (altChainFin hn i 2)

theorem altChainFin_ne_01 (hn : 3 ≤ n) (i : ℕ) : altChainFin hn i 0 ≠ altChainFin hn i 1 := by
  simp [altChainFin, Fin.ext_iff]

theorem altChainFin_ne_02 (hn : 3 ≤ n) (i : ℕ) : altChainFin hn i 0 ≠ altChainFin hn i 2 := by
  simp [altChainFin, Fin.ext_iff]

theorem altChainFin_ne_12 (hn : 3 ≤ n) (i : ℕ) : altChainFin hn i 1 ≠ altChainFin hn i 2 := by
  simp [altChainFin, Fin.ext_iff]

theorem mem_altChainSet_iff (hn : 3 ≤ n) (i : Fin (n / 2)) (x : Fin n) :
    x ∈ altChainSet hn i ↔ altChainPt n i ≤ x ∧ (x : ℕ) ≤ altChainPt n i + 2 := by
  simp only [altChainSet, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff, altChainFin]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero]
  omega

theorem ncard_altChainSet (hn : 3 ≤ n) (i : Fin (n / 2)) : 3 ≤ (altChainSet hn i).ncard := by
  rw [altChainSet, Set.ncard_insert_of_notMem, Set.ncard_pair (altChainFin_ne_12 hn i)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨altChainFin_ne_01 hn i, altChainFin_ne_02 hn i⟩

theorem iUnion_altChainSet (hn : 3 ≤ n) : (⋃ i, altChainSet hn i) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hpos : 0 < n / 2 := by omega
  refine ⟨⟨min ((x : ℕ) / 2) (n / 2 - 1), by omega⟩, ?_⟩
  rw [mem_altChainSet_iff]
  have hx := x.2
  simp only [altChainPt]
  omega

theorem altChainSet_inter_succ (hn : 3 ≤ n) (i : ℕ) (hi : i + 1 < n / 2) :
    (altChainSet hn ⟨i, by omega⟩ ∩ altChainSet hn ⟨i + 1, hi⟩).Nonempty := by
  refine ⟨altChainFin hn (i + 1) 0, ?_, ?_⟩
  · rw [mem_altChainSet_iff]
    simp only [altChainFin, altChainPt, Fin.val_zero, add_zero]
    omega
  · rw [mem_altChainSet_iff]
    simp only [altChainFin, altChainPt, Fin.val_zero, add_zero]
    omega

theorem altChainSet_reflTransGen (hn : 3 ≤ n) (i j : Fin (n / 2)) :
    Relation.ReflTransGen (fun a b => (altChainSet hn a ∩ altChainSet hn b).Nonempty) i j := by
  set R : Fin (n / 2) → Fin (n / 2) → Prop :=
    fun a b => (altChainSet hn a ∩ altChainSet hn b).Nonempty
  have hRsymm : ∀ a b, R a b → R b a := fun a b h => by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, hx.2, hx.1⟩
  have h0 : ∀ k (hk : k < n / 2), Relation.ReflTransGen R ⟨0, by omega⟩ ⟨k, hk⟩ ∧
      Relation.ReflTransGen R ⟨k, hk⟩ ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hR := altChainSet_inter_succ hn k hk
      exact ⟨h1.tail hR, Relation.ReflTransGen.head (hRsymm _ _ hR) h2⟩
  exact (h0 i i.2).2.trans (h0 j j.2).1

theorem alternatingGroup_le_closure_altChainTri (hn : 3 ≤ n) :
    alternatingGroup (Fin n) ≤ closure (Set.range (altChainTri hn)) := by
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [← GL83.iSup_altOn_eq_alternatingGroup (ncard_altChainSet hn) (iUnion_altChainSet hn)
    (altChainSet_reflTransGen hn)]
  refine iSup_le fun i => ?_
  exact (GL83.PiGen.altOn_three_le_zpowers (altChainFin_ne_01 hn i) (altChainFin_ne_02 hn i)
    (altChainFin_ne_12 hn i)).trans (zpowers_le.2 (subset_closure ⟨i, rfl⟩))

theorem altChainTri_mem_alternatingGroup (hn : 3 ≤ n) (i : Fin (n / 2)) :
    altChainTri hn i ∈ alternatingGroup (Fin n) :=
  (GL83.mem_altOn.1 (GL83.PiGen.tri_mem_altOn (altChainFin_ne_01 hn i)
    (altChainFin_ne_02 hn i))).1

theorem card_mul_card_dnQuot_le (hn : 3 ≤ n) (W : Type) [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (H : Subgroup (MulAut W)) (Z : Subgroup W) (hZ : Z ≤ fixV H)
    (hcomm : commV H = ⊤) (hnat : AlternatingNatural H ⊤ Z n) :
    Nat.card ↥Z * Nat.card (DnQuot n) ≤ 4 ^ (n / 2) := by
  obtain ⟨π₀, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  let π : ↥(alternatingGroup (Fin n)) →* ↥H := π₀
  let ρ : ↥(alternatingGroup (Fin n)) →* MulAut W := H.subtype.comp π
  let g : Fin (n / 2) → ↥(alternatingGroup (Fin n)) := fun i =>
    ⟨altChainTri hn i, altChainTri_mem_alternatingGroup hn i⟩
  let M : Subgroup W := ⨆ i, (commMap (ρ (g i))).range
  have hgenle : closure (Set.range (altChainTri hn)) ≤ alternatingGroup (Fin n) := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact altChainTri_mem_alternatingGroup hn i
  have key : ∀ τ ∈ closure (Set.range (altChainTri hn)), ∀ hτ : τ ∈ alternatingGroup (Fin n),
      ∀ w, ρ ⟨τ, hτ⟩ w * w⁻¹ ∈ M := by
    intro τ hτ
    induction hτ using closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro _ w
      exact mem_iSup_of_mem i ⟨w, rfl⟩
    | one =>
      intro h1 w
      have e : (⟨1, h1⟩ : ↥(alternatingGroup (Fin n))) = 1 := rfl
      rw [e, map_one, MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    | mul a b ha hb iha ihb =>
      intro hab w
      have e : (⟨a * b, hab⟩ : ↥(alternatingGroup (Fin n))) = ⟨a, hgenle ha⟩ * ⟨b, hgenle hb⟩ :=
        rfl
      have e2 : ρ (⟨a, hgenle ha⟩ * ⟨b, hgenle hb⟩) w * w⁻¹ =
          (ρ ⟨a, hgenle ha⟩ (ρ ⟨b, hgenle hb⟩ w) * (ρ ⟨b, hgenle hb⟩ w)⁻¹) *
            (ρ ⟨b, hgenle hb⟩ w * w⁻¹) := by
        rw [map_mul, MulAut.mul_apply]
        group
      rw [e, e2]
      exact mul_mem (iha _ _) (ihb _ _)
    | inv a ha iha =>
      intro ha' w
      have e : (⟨a⁻¹, ha'⟩ : ↥(alternatingGroup (Fin n))) = (⟨a, hgenle ha⟩)⁻¹ := rfl
      set σ : ↥(alternatingGroup (Fin n)) := ⟨a, hgenle ha⟩
      have hv : ρ σ (ρ σ⁻¹ w) = w := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      have e2 : ρ σ⁻¹ w * w⁻¹ = (ρ σ (ρ σ⁻¹ w) * (ρ σ⁻¹ w)⁻¹)⁻¹ := by
        rw [hv]
        group
      rw [e, e2]
      exact inv_mem (iha _ _)
  have hP : ∀ σ : ↥(alternatingGroup (Fin n)), ∀ w, ρ σ w * w⁻¹ ∈ M := fun σ w =>
    key σ.1 (alternatingGroup_le_closure_altChainTri hn σ.2) σ.2 w
  have hle : (⊤ : Subgroup W) ≤ M := by
    rw [← hcomm]
    refine (closure_le _).2 ?_
    rintro _ ⟨x, hx, w, rfl⟩
    obtain ⟨σ, hσ⟩ := hπs ⟨x, hx⟩
    have hx' : ρ σ = x := congrArg Subtype.val hσ
    rw [← hx']
    exact hP σ w
  let β' : W →* DnQuot n :=
    { toFun := fun v => β ⟨v, mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
  have hβ's : Function.Surjective β' := fun q => by
    obtain ⟨⟨v, hvm⟩, hv⟩ := hβs q
    exact ⟨v, hv⟩
  have hker : β'.ker = Z := by
    ext v
    rw [MonoidHom.mem_ker]
    exact hβk ⟨v, mem_top v⟩
  have hcard : ∀ i, Nat.card (commMap (ρ (g i))).range ≤ 4 := by
    intro i
    have h3 : (ρ (g i)) ^ 3 = 1 := by
      have hc : (altChainTri hn i).IsThreeCycle :=
        Equiv.Perm.isThreeCycle_swap_mul_swap_same (altChainFin_ne_02 hn i)
          (altChainFin_ne_01 hn i) (altChainFin_ne_12 hn i).symm
      have hg3 : g i ^ 3 = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow]
        rw [← hc.orderOf]
        exact pow_orderOf_eq_one _
      rw [← map_pow, hg3, map_one]
    have h := card_commMap_range_le (β := β') hW2 (fun v => hβk ⟨v, mem_top v⟩) h3
      (fun z hz => hZ hz _ (π (g i)).2)
      (fun v m hm => hβe (g i) ⟨v, mem_top v⟩ m (mem_top _) (G6.permAct_mem_coreMod _ m.2) hm)
      (evenOn (altChainFin hn i 0) (altChainFin hn i 1) (altChainFin hn i 2))
      (comm_mem_evenOn_tri (altChainFin_ne_01 hn i) (altChainFin_ne_02 hn i)
        (altChainFin_ne_12 hn i))
    rwa [card_evenOn (altChainFin_ne_01 hn i) (altChainFin_ne_02 hn i)
      (altChainFin_ne_12 hn i)] at h
  have hW : Nat.card W ≤ 4 ^ (n / 2) :=
    calc Nat.card W = Nat.card (⊤ : Subgroup W) := card_top.symm
      _ ≤ Nat.card M := card_le_of_le hle
      _ ≤ ∏ i, Nat.card (commMap (ρ (g i))).range :=
          CFSG.Quasithin.B513N.card_iSup_le_prod (n / 2) _
      _ ≤ 4 ^ (Finset.univ : Finset (Fin (n / 2))).card :=
          Finset.prod_le_pow_card _ _ _ fun i _ => hcard i
      _ = 4 ^ (n / 2) := by rw [Finset.card_univ, Fintype.card_fin]
  have hcardW := Subgroup.card_ker_mul_card_of_surjective hβ's
  rw [hker] at hcardW
  rw [hcardW]
  exact hW

theorem card_le_four_of_altNaturalCover (hn : 3 ≤ n) (W : Type) [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (H : Subgroup (MulAut W)) (Z : Subgroup W) (hZ : Z ≤ fixV H)
    (hcomm : commV H = ⊤) (hnat : AlternatingNatural H ⊤ Z n) : Nat.card ↥Z ≤ 4 := by
  have h := card_mul_card_dnQuot_le hn W hW2 H Z hZ hcomm hnat
  have hq : Nat.card (DnQuot n) = if Even n then 2 ^ (n - 2) else 2 ^ (n - 1) :=
    Explicit.card_dn_sec (by omega) .alternating
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos he] at hq
    obtain ⟨r, rfl⟩ := he
    have h4 : (4 : ℕ) ^ ((r + r) / 2) = 2 ^ (r + r - 2) * 4 := by
      rw [show (r + r) / 2 = r by omega, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [h4, hq] at h
    have hpos : 0 < 2 ^ (r + r - 2) := pow_pos (by norm_num) _
    nlinarith
  · rw [if_neg (Nat.not_even_iff_odd.2 ho)] at hq
    obtain ⟨r, rfl⟩ := ho
    have h4 : (4 : ℕ) ^ ((2 * r + 1) / 2) = 2 ^ (2 * r + 1 - 1) := by
      rw [show (2 * r + 1) / 2 = r by omega, show 2 * r + 1 - 1 = 2 * r by omega,
        show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4, hq] at h
    have hpos : 0 < 2 ^ (2 * r + 1 - 1) := pow_pos (by norm_num) _
    nlinarith

end CFSG.Quasithin.H13.VolI
