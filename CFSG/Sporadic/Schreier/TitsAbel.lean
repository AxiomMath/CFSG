module

public import CFSG.Sporadic.Schreier.TitsAbelCheck
public import CFSG.Sporadic.Schreier.TitsStab

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section GroupTheory

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj {R : Subgroup G} [Finite R] {s : G}
    (h : ∀ r ∈ R, s * r * s⁻¹ ∈ R) : s ∈ Subgroup.normalizer (R : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun r => ⟨h r, fun hr => ?_⟩
  let f : R → R := fun x => ⟨s * x * s⁻¹, h x x.2⟩
  have hf : Function.Injective f := fun a b e => by
    have := congrArg Subtype.val e
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨r', hr'⟩ := Finite.injective_iff_surjective.1 hf ⟨_, hr⟩
  have e := congrArg Subtype.val hr'
  simp only [f, mul_left_inj, mul_right_inj] at e
  exact e ▸ r'.2

theorem commutator_le_of_gens {H N : Subgroup G} {X : Set G} (hHX : H = Subgroup.closure X)
    [hN : (N.subgroupOf H).Normal] (hcomm : ∀ x ∈ X, ∀ y ∈ X, tcomm x y ∈ N) :
    commutator H ≤ N.subgroupOf H := by
  subst hHX
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  set N' := N.subgroupOf (Subgroup.closure X)
  set k : Set (Subgroup.closure X ⧸ N') :=
    QuotientGroup.mk' N' '' ((Subgroup.closure X).subtype ⁻¹' X)
  have hk : Subgroup.closure k = ⊤ := by
    rw [← MonoidHom.map_closure, Subgroup.coe_subtype, Subgroup.closure_closure_coe_preimage,
      ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  have hpair : k.Pairwise Commute := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
    show QuotientGroup.mk' N' a * QuotientGroup.mk' N' b =
      QuotientGroup.mk' N' b * QuotientGroup.mk' N' a
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := hcomm _ hb _ ha
    simp only [tcomm, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev] at this ⊢
    simpa [mul_assoc] using this
  have hc := Subgroup.isMulCommutative_closure hpair
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : a ∈ Subgroup.closure k := hk ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.closure k := hk ▸ Subgroup.mem_top b
  exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end GroupTheory

theorem titsR_chainArrays :
    ChainArrays titsQR (titsRArrs.extract 0 3) titsRArrs (baseArr 1755 titsRBase)
      (wordsArr 3 8 titsRDerivations) :=
  chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mem_titsS_iff_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    inS a = true ↔ g ∈ titsS := by
  rw [← titsQS_facts.2.2.1]
  exact siftA_iff_mem_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num : 0 < 4) titsLocalChains_check.2.1 ha

theorem mem_titsR_iff_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    inR a = true ↔ g ∈ titsR := by
  rw [← titsQR_facts.2.2.1]
  exact siftA_iff_mem_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num : 0 < 4) titsLocalChains_check.2.2.2.2.2.1 ha

@[expose] def titsSGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsSArrs[i]!

@[expose] def titsRGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsRArrs[i]!

theorem titsSGen_rep
    {i : ℕ} (hi : i < 3) : Rep 1755 titsSArrs[i]! (titsSGen i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsSArrs_size]; omega)

theorem titsRGen_rep
    {i : ℕ} (hi : i < 3) : Rep 1755 titsRArrs[i]! (titsRGen i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsRArrs_size]; omega)

theorem titsS_eq_closure :
    titsS = Subgroup.closure (Set.range fun i : Fin 3 => titsSGen i) := by
  rw [← titsQS_facts.2.2.1, titsQS, originalSubgroup_ofArrays]
  rfl

theorem titsR_eq_closure :
    titsR = Subgroup.closure (Set.range fun i : Fin 3 => titsRGen i) := by
  rw [← titsQR_facts.2.2.1, titsQR, originalSubgroup_ofArrays]
  rfl

theorem titsSGen_mem
    {i : ℕ} (hi : i < 3) : titsSGen i ∈ titsS := by
  rw [titsS_eq_closure]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem titsRGen_mem
    {i : ℕ} (hi : i < 3) : titsRGen i ∈ titsR := by
  rw [titsR_eq_closure]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem titsAbel_prov
    {k : ℕ} (hk : k < 3) :
    ∃ u < 3, ∃ v < 3, ∃ w ∈ titsS, titsRGen k = w⁻¹ * tcomm (titsSGen u) (titsSGen v) * w := by
  obtain ⟨-, -, -, h, -, -⟩ := titsAbel_check
  obtain ⟨-, hu, hv, hl, hinv, hsift, heq⟩ := h k hk
  set cw := titsProvenance[k]!.2.2
  have hrep := rep_wordArr_titsT hl
  refine ⟨_, hu, _, hv, wordIn 13 titsT cw, (mem_titsS_iff_sift hrep).1 hsift, ?_⟩
  exact eq_of_eqA (titsRGen_rep hk) (rep_compA (rep_compA (rep_inv_of_isInvA hrep hinv)
    (rep_commArr (titsSGen_rep hu) (titsSGen_rep hv)
      (isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by rw [titsSArrs_size]; omega))
      (isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by rw [titsSArrs_size]; omega)))) hrep) heq

theorem titsSGen_inv {a : ℕ} (ha : a < 3) :
    isInvA 1755 titsSArrs[a]! (invCand 1755 titsSArrs[a]!) = true :=
  isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsSArrs_size]; omega)

theorem titsSGen_conj_gen
    {a b : ℕ} (ha : a < 3) (hb : b < 3) :
    titsSGen a * titsRGen b * (titsSGen a)⁻¹ ∈ titsR := by
  have hrep : Rep 1755 (compA 1755 (compA 1755 titsSArrs[a]! titsRArrs[b]!)
      (invCand 1755 titsSArrs[a]!)) (titsSGen a * titsRGen b * (titsSGen a)⁻¹) :=
    rep_compA (rep_compA (titsSGen_rep ha) (titsRGen_rep hb))
      (rep_inv_of_isInvA (titsSGen_rep ha) (titsSGen_inv ha))
  exact (mem_titsR_iff_sift hrep).1 (titsAbel_check.2.2.2.2.1 a ha b hb)

theorem titsSGen_conj
    {a : ℕ} (ha : a < 3) :
    ∀ r ∈ titsR, titsSGen a * r * (titsSGen a)⁻¹ ∈ titsR := by
  have hle : titsR ≤ titsR.comap (MulAut.conj (titsSGen a)).toMonoidHom := by
    conv_lhs => rw [titsR_eq_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact titsSGen_conj_gen ha b.2
  intro r hr
  have := Subgroup.mem_comap.1 (hle hr)
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem titsS_le_normalizer :
    titsS ≤ Subgroup.normalizer (titsR : Set (Equiv.Perm (Fin 1755))) := by
  rw [titsS_eq_closure, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact mem_normalizer_of_conj (titsSGen_conj a.2)

instance titsR_normal :
    (titsR.subgroupOf titsS).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (titsS_le_normalizer g.2) n).1 hn⟩

theorem titsS_commutator_le :
    commutator titsS ≤ titsR.subgroupOf titsS := by
  have := commutator_le_of_gens (H := titsS) (N := titsR) titsS_eq_closure (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact (mem_titsR_iff_sift (rep_commArr (titsSGen_rep a.2) (titsSGen_rep b.2)
      (isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by rw [titsSArrs_size]; omega))
      (isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (by rw [titsSArrs_size]; omega)))).1 (titsAbel_check.2.2.2.2.2 a a.2 b b.2))
  exact this

theorem titsR_le_commutator :
    titsR.subgroupOf titsS ≤ commutator titsS := by
  intro r hr
  rw [Subgroup.mem_subgroupOf] at hr
  have key : ∀ x (hx : x ∈ Subgroup.closure (Set.range fun i : Fin 3 => titsRGen i)),
      ∀ hxS : x ∈ titsS, (⟨x, hxS⟩ : titsS) ∈ commutator titsS := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨k, rfl⟩ := ht
      obtain ⟨u, hu, v, hv, w, hw, e⟩ := titsAbel_prov k.2
      intro hxS
      have he : (⟨titsRGen k, hxS⟩ : titsS) =
          (⟨w, hw⟩ : titsS)⁻¹ * tcomm ⟨titsSGen u, titsSGen_mem hu⟩ ⟨titsSGen v, titsSGen_mem hv⟩ *
            ⟨w, hw⟩ := Subtype.ext (by simp [e, tcomm])
      rw [he]
      have hc : tcomm (⟨titsSGen u, titsSGen_mem hu⟩ : titsS) ⟨titsSGen v, titsSGen_mem hv⟩ ∈
          commutator titsS := by
        rw [commutator_def]
        exact tcomm_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have := (Subgroup.commutator_normal (⊤ : Subgroup titsS) ⊤).conj_mem _ hc
        (⟨w, hw⟩ : titsS)⁻¹
      simpa [commutator_def] using this
    | one => intro _; exact one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxy
      have hxS : x ∈ titsS := (titsR_eq_closure ▸ titsR_le_titsS) hx
      have hyS : y ∈ titsS := (titsR_eq_closure ▸ titsR_le_titsS) hy
      exact mul_mem (ihx hxS) (ihy hyS)
    | inv x hx ih =>
      intro hxS
      exact inv_mem (ih ((titsR_eq_closure ▸ titsR_le_titsS) hx))
  exact key _ (titsR_eq_closure ▸ hr) r.2

theorem titsR_eq_commutator :
    titsR.subgroupOf titsS = commutator titsS :=
  le_antisymm titsR_le_commutator titsS_commutator_le

theorem titsX_rep :
    Rep 1755 titsXArr titsX :=
  rep_wordArr_titsT titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsY_rep :
    Rep 1755 titsYArr titsY :=
  rep_wordArr_titsT titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem titsX_mem_titsS :
    titsX ∈ titsS :=
  (mem_titsS_iff_sift titsX_rep).1 titsAbel_check2.2.2.1

theorem titsY_mem_titsS :
    titsY ∈ titsS :=
  (mem_titsS_iff_sift titsY_rep).1 titsAbel_check2.2.2.2.1

theorem rep_iterate {n : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g) :
    ∀ i, Rep n (Nat.iterate (compA n a) i (idA n)) (g ^ i)
  | 0 => by simpa using (rep_idA (n := n))
  | i + 1 => by
    rw [Function.iterate_succ_apply', pow_succ']
    exact rep_compA ha (rep_iterate ha i)

theorem titsXY_rep
    (i j : ℕ) : Rep 1755 (titsXYArr i j) (titsX ^ i * titsY ^ j) :=
  rep_compA (rep_iterate titsX_rep i) (rep_iterate titsY_rep j)

abbrev TitsSR :
    Type := titsS ⧸ titsR.subgroupOf titsS

abbrev titsXbar :
    TitsSR := QuotientGroup.mk (⟨titsX, titsX_mem_titsS⟩ : titsS)

abbrev titsYbar :
    TitsSR := QuotientGroup.mk (⟨titsY, titsY_mem_titsS⟩ : titsS)

theorem titsSR_comm
    (a b : TitsSR) : a * b = b * a := by
  have h : IsMulCommutative TitsSR :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 titsS_commutator_le
  exact h.is_comm.comm a b

theorem titsSR_mk_eq_iff
    (g h : titsS) :
    (QuotientGroup.mk g : TitsSR) = QuotientGroup.mk h ↔
      (g : Equiv.Perm (Fin 1755))⁻¹ * h ∈ titsR := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem titsXbar_pow
    (i j : ℕ) : titsXbar ^ i * titsYbar ^ j =
    QuotientGroup.mk ((⟨titsX, titsX_mem_titsS⟩ : titsS) ^ i * ⟨titsY, titsY_mem_titsS⟩ ^ j) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]

theorem titsXbar_pow_four :
    titsXbar ^ 4 = 1 := by
  have h := titsXbar_pow 4 0
  rw [pow_zero, mul_one, pow_zero, mul_one] at h
  rw [h, ← QuotientGroup.mk_one, titsSR_mk_eq_iff]
  have := (mem_titsR_iff_sift (titsXY_rep 4 0)).1 titsAbel_check2.2.2.2.2.1
  simpa using inv_mem this

theorem titsYbar_sq :
    titsYbar ^ 2 = 1 := by
  have h := titsXbar_pow 0 2
  rw [pow_zero, one_mul, pow_zero, one_mul] at h
  rw [h, ← QuotientGroup.mk_one, titsSR_mk_eq_iff]
  have := (mem_titsR_iff_sift (titsXY_rep 0 2)).1 titsAbel_check2.2.2.2.2.2.1
  simpa using inv_mem this

theorem pow_mod_eq {G : Type*} [Monoid G] {x : G} {n : ℕ} (hx : x ^ n = 1) (m : ℕ) :
    x ^ (m % n) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def titsAbelMap :

    Multiplicative (ZMod 4) × Multiplicative (ZMod 2) →* TitsSR where
  toFun p := titsXbar ^ (Multiplicative.toAdd p.1).val * titsYbar ^ (Multiplicative.toAdd p.2).val
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, ZMod.val_add]
    rw [pow_mod_eq titsXbar_pow_four, pow_mod_eq titsYbar_sq, pow_add, pow_add]
    calc titsXbar ^ (Multiplicative.toAdd p.1).val * titsXbar ^ (Multiplicative.toAdd q.1).val *
          (titsYbar ^ (Multiplicative.toAdd p.2).val * titsYbar ^ (Multiplicative.toAdd q.2).val)
        = titsXbar ^ (Multiplicative.toAdd p.1).val *
          (titsXbar ^ (Multiplicative.toAdd q.1).val * titsYbar ^ (Multiplicative.toAdd p.2).val) *
            titsYbar ^ (Multiplicative.toAdd q.2).val := by simp only [mul_assoc]
      _ = titsXbar ^ (Multiplicative.toAdd p.1).val *
          (titsYbar ^ (Multiplicative.toAdd p.2).val * titsXbar ^ (Multiplicative.toAdd q.1).val) *
            titsYbar ^ (Multiplicative.toAdd q.2).val := by
          rw [titsSR_comm (titsXbar ^ (Multiplicative.toAdd q.1).val)
            (titsYbar ^ (Multiplicative.toAdd p.2).val)]
      _ = _ := by simp only [mul_assoc]

theorem titsAbelMap_apply
    (p : Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) :
    titsAbelMap p =
      titsXbar ^ (Multiplicative.toAdd p.1).val * titsYbar ^ (Multiplicative.toAdd p.2).val :=
  rfl

theorem titsAbelMap_injective :
    Function.Injective titsAbelMap := by
  intro p q h
  rw [titsAbelMap_apply, titsAbelMap_apply, titsXbar_pow, titsXbar_pow, titsSR_mk_eq_iff] at h
  set i := (Multiplicative.toAdd p.1).val
  set j := (Multiplicative.toAdd p.2).val
  set i' := (Multiplicative.toAdd q.1).val
  set j' := (Multiplicative.toAdd q.2).val
  have hi : i < 4 := ZMod.val_lt _
  have hj : j < 2 := ZMod.val_lt _
  have hi' : i' < 4 := ZMod.val_lt _
  have hj' : j' < 2 := ZMod.val_lt _
  have hmem : (titsX ^ i * titsY ^ j)⁻¹ * (titsX ^ i' * titsY ^ j') ∈ titsR := by simpa using h
  have hsift := (mem_titsR_iff_sift (rep_compA (rep_inv_of_isInvA (titsXY_rep i j)
    (titsAbel_check2.2.2.2.2.2.2 i hi j hj)) (titsXY_rep i' j'))).2 hmem
  rcases titsAbel_check3 i hi j hj i' hi' j' hj' with e | e
  · obtain ⟨e1, e2⟩ := Prod.mk.injEq _ _ _ _ ▸ e
    exact Prod.ext (congrArg Multiplicative.ofAdd (ZMod.val_injective _ e1))
      (congrArg Multiplicative.ofAdd (ZMod.val_injective _ e2))
  · rw [e] at hsift
    exact absurd hsift Bool.false_ne_true

theorem card_TitsSR :
    Nat.card TitsSR = 8 := by
  rw [← Subgroup.index_eq_card]
  have h := Subgroup.card_mul_index (titsR.subgroupOf titsS)
  rw [card_subgroupOf_eq titsR_le_titsS, titsQR_facts.2.2.2, titsQS_facts.2.2.2] at h
  omega

theorem card_C4C2 : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) = 8 := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

theorem titsAbelMap_bijective :
    Function.Bijective titsAbelMap :=
  titsAbelMap_injective.bijective_of_nat_card_le (by rw [card_TitsSR, card_C4C2])

@[expose] def titsAbelEquiv :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ≃* TitsSR :=
  MulEquiv.ofBijective titsAbelMap titsAbelMap_bijective

theorem titsAbelEquiv_apply
    (i j : ℕ) :
    titsAbelEquiv (Multiplicative.ofAdd (i : ZMod 4), Multiplicative.ofAdd (j : ZMod 2)) =
      QuotientGroup.mk ((⟨titsX, titsX_mem_titsS⟩ : titsS) ^ i * ⟨titsY, titsY_mem_titsS⟩ ^ j) := by
  show titsAbelMap _ = _
  rw [titsAbelMap_apply, toAdd_ofAdd, toAdd_ofAdd, ZMod.val_natCast, ZMod.val_natCast,
    pow_mod_eq titsXbar_pow_four, pow_mod_eq titsYbar_sq, titsXbar_pow]

@[expose] def titsAbelianizationEquiv :
    Abelianization titsS ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq titsR_eq_commutator.symm).trans titsAbelEquiv.symm

theorem AT_Tits_Sylow_abelianization :
    titsR.subgroupOf titsS = commutator titsS ∧
    (∃ e : Multiplicative (ZMod 4) × Multiplicative (ZMod 2) ≃* titsS ⧸ titsR.subgroupOf titsS,
      ∀ i j : ℕ, e (Multiplicative.ofAdd (i : ZMod 4), Multiplicative.ofAdd (j : ZMod 2)) =
        QuotientGroup.mk ((⟨titsX, titsX_mem_titsS⟩ : titsS) ^ i *
          ⟨titsY, titsY_mem_titsS⟩ ^ j)) ∧
    Nonempty (Abelianization titsS ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) :=
  ⟨titsR_eq_commutator, ⟨titsAbelEquiv, titsAbelEquiv_apply⟩, ⟨titsAbelianizationEquiv⟩⟩

end CFSG.Sporadic.Schreier.Tits
