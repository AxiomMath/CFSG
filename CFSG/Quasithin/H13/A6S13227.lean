module

public import CFSG.Quasithin.H13.U3C137Five
public import CFSG.Quasithin.H13.U3L13x7
public import CFSG.Quasithin.H13.A6Set14
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise IsMulCommutative

@[expose] def stab45List : List (Perm (Fin 6)) :=
  [1, swap 2 3 * swap 4 5, swap 1 2 * swap 4 5, swap 1 2 * swap 2 3, swap 1 3 * swap 3 2,
    swap 1 3 * swap 4 5, swap 0 1 * swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 1 2,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 1 * swap 1 3 * swap 3 2 * swap 4 5,
    swap 0 1 * swap 1 3, swap 0 2 * swap 2 1, swap 0 2 * swap 2 3 * swap 3 1 * swap 4 5,
    swap 0 2 * swap 4 5, swap 0 2 * swap 2 3, swap 0 2 * swap 1 3,
    swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5, swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5,
    swap 0 3 * swap 3 1, swap 0 3 * swap 3 2, swap 0 3 * swap 4 5,
    swap 0 3 * swap 3 1 * swap 1 2 * swap 4 5, swap 0 3 * swap 1 2]

theorem stab45_mul : ∀ σ ∈ stab45List, ∀ τ ∈ stab45List, σ * τ ∈ stab45List := by
  decide +kernel

theorem stab45_inv : ∀ σ ∈ stab45List, σ⁻¹ ∈ stab45List := by
  decide +kernel

theorem stab45_one : (1 : Perm (Fin 6)) ∈ stab45List := by
  decide +kernel

theorem stab45_nodup : stab45List.Nodup := by
  decide +kernel

theorem stab45_sign_fix : ∀ σ ∈ stab45List, Perm.sign σ = 1 ∧ act4f σ e0123 = e0123 := by
  decide +kernel

@[expose] def stab45 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ stab45List}
  mul_mem' := fun {σ τ} hσ hτ => stab45_mul σ hσ τ hτ
  one_mem' := stab45_one
  inv_mem' := fun {σ} hσ => stab45_inv σ hσ

theorem card_stab45 : Nat.card stab45 = 24 := by
  rw [← (show stab45List.length = 24 from rfl), ← List.toFinset_card_of_nodup stab45_nodup,
    ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => by rw [List.mem_toFinset]; rfl)

theorem stab45_le_alt : stab45 ≤ alternatingGroup (Fin 6) := fun σ hσ =>
  Perm.mem_alternatingGroup.2 (stab45_sign_fix σ hσ).1

theorem fix45_odd : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → σ ^ 3 = 1 → σ ∈ S14.C3 := by
  decide +kernel

theorem fix45_exp : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → σ ^ 12 = 1 := by
  decide +kernel

@[expose] def InLine4 (a b x : P6) : Prop := x = 1 ∨ x = a ∨ x = b ∨ x = a * b

instance (a b x : P6) : Decidable (InLine4 a b x) := by unfold InLine4; infer_instance

@[expose] def NoLineAt (a b : P6) : Prop :=
  InW4 a → InW4 b → a ≠ 1 → b ≠ 1 → a ≠ b →
    InLine4 a b (act4f (swap 0 1 * swap 1 2) a) → InLine4 a b (act4f (swap 0 1 * swap 1 2) b) →
    InLine4 a b (act4f (swap 1 2 * swap 2 3) a) → InLine4 a b (act4f (swap 1 2 * swap 2 3) b) →
    False

instance (a b : P6) : Decidable (NoLineAt a b) := by unfold NoLineAt; infer_instance

theorem no_line_c3 : ∀ a b : P6, NoLineAt a b := by
  decide +kernel

theorem alt6_le_of_overgroup24 {C X : Subgroup (Perm (Fin 6))} (hC24 : Nat.card C = 24)
    (hCA : C ≤ alternatingGroup (Fin 6)) (hCX : C ≤ X) {s : Perm (Fin 6)} (hs : s ∈ X)
    (hs1 : Perm.sign s = 1) (hsC : s ∉ C) : alternatingGroup (Fin 6) ≤ X := by
  set A := alternatingGroup (Fin 6) with hAdef
  have hsimp : IsSimpleGroup ↥A := alternatingGroup.isSimpleGroup (by simp)
  have hCXA : C ≤ X ⊓ A := le_inf hCX hCA
  have h24 : 24 ∣ Nat.card ↥(X ⊓ A) := hC24 ▸ Subgroup.card_dvd_of_le hCXA
  have hne : Nat.card ↥(X ⊓ A) ≠ 24 := by
    intro h
    have e : C = X ⊓ A := Subgroup.eq_of_le_of_card_ge hCXA (by rw [h, hC24])
    exact hsC (e ▸ ⟨hs, Perm.mem_alternatingGroup.mpr hs1⟩)
  set Y := (X ⊓ A).subgroupOf A with hYdef
  have hcY : Nat.card Y = Nat.card ↥(X ⊓ A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hmul := Subgroup.card_mul_index Y
  rw [hcY, card_alt6] at hmul
  obtain ⟨k, hk⟩ := h24
  have hki : k * Y.index = 15 := by
    rw [hk, mul_assoc] at hmul
    omega
  have hi5 : Y.index ≤ 5 := by
    have hpos : 0 < Y.index := Nat.pos_of_ne_zero (by intro h; rw [h, mul_zero] at hki; omega)
    have hle : Y.index ≤ 15 := Nat.le_of_dvd (by norm_num) ⟨k, by rw [mul_comm]; exact hki.symm⟩
    have hk1 : k ≠ 1 := fun h => hne (by rw [hk, h])
    interval_cases h : Y.index <;> omega
  have hcore := Subgroup.index_normalCore_le_factorial_index Y
  rcases (Subgroup.normalCore_normal Y).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot, card_alt6] at hcore
    have : Nat.factorial Y.index ≤ Nat.factorial 5 := Nat.factorial_le hi5
    have h120 : Nat.factorial 5 = 120 := rfl
    omega
  · intro σ hσ
    have hm : (⟨σ, hσ⟩ : ↥A) ∈ Y := Y.normalCore_le (h ▸ Subgroup.mem_top _)
    exact (Subgroup.mem_subgroupOf.mp hm).1

theorem relIndex_sup_of_normalizes {G : Type} [Group G] [Finite G] {N P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) : P.relIndex (N ⊔ P) = (P ⊓ N).relIndex N := by
  set K := N ⊔ P with hK
  have hNK : N ≤ K := le_sup_left
  have hPK : P ≤ K := le_sup_right
  have hnorm : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hkN : (k : G) ∈ Subgroup.normalizer (N : Set G) :=
      (sup_le Subgroup.le_normalizer hPN : K ≤ _) k.2
    simpa using (Subgroup.mem_normalizer_iff.mp hkN n).mp hn
  have htop : P.subgroupOf K ⊔ N.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPK hNK, sup_comm]
    exact Subgroup.subgroupOf_self K
  have h1 := Subgroup.relIndex_sup_right (H := P.subgroupOf K) (K := N.subgroupOf K)
  rw [htop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hPK] at h1
  have hNKidx : N.relIndex K = (P ⊓ N).relIndex P := by
    rw [Subgroup.relIndex, h1, ← Subgroup.inf_relIndex_right, inf_comm]
  have hm1 := Subgroup.relIndex_mul_relIndex (P ⊓ N) N K inf_le_right hNK
  have hm2 := Subgroup.relIndex_mul_relIndex (P ⊓ N) P K inf_le_left hPK
  rw [← hm2, hNKidx, mul_comm] at hm1
  have hne : (P ⊓ N).relIndex P ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hm1).symm

theorem relIndex_eq_three {G : Type} [Group G] [Finite G] {A B : Subgroup G} {c : G}
    (hcB : c ∈ B) (hcA : c ∉ A) (hc3 : c ^ 3 = 1)
    (hcov : ∀ x ∈ B, x ∈ A ∨ c * c * x ∈ A ∨ c * x ∈ A) : A.relIndex B = 3 := by
  set A' := A.subgroupOf B with hA'
  set C : ↥B := ⟨c, hcB⟩ with hC
  have hc3' : C ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hCA : C ∉ A' := fun h => hcA (Subgroup.mem_subgroupOf.mp h)
  have hC2A : C * C ∉ A' := by
    intro h
    apply hCA
    have : C = (C * C) * (C * C) := by
      calc C = C ^ 3 * C := by rw [hc3', one_mul]
        _ = (C * C) * (C * C) := by rw [pow_three]; simp only [mul_assoc]
    rw [this]
    exact A'.mul_mem h h
  let f : Fin 3 → ↥B ⧸ A' := fun i => QuotientGroup.mk (C ^ (i : ℕ))
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have key : ∀ i j : Fin 3, (i : ℕ) < j → f i ≠ f j := by
        intro i j hlt h
        rw [QuotientGroup.eq] at h
        have e : (C ^ (i : ℕ))⁻¹ * C ^ (j : ℕ) = C ^ ((j : ℕ) - i) := by
          have hj : C ^ (j : ℕ) = C ^ (i : ℕ) * C ^ ((j : ℕ) - i) := by
            rw [← pow_add, Nat.add_sub_cancel' hlt.le]
          rw [hj, inv_mul_cancel_left]
        rw [e] at h
        have hji : (j : ℕ) - i = 1 ∨ (j : ℕ) - i = 2 := by omega
        rcases hji with h1 | h1 <;> rw [h1] at h
        · exact hCA (by simpa using h)
        · exact hC2A (by rw [pow_two] at h; exact h)
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · exact key i j hlt hij
      · exact key j i hlt hij.symm
    · intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hc3m : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
      have hinv : c⁻¹ = c * c := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hc3m])
      have hinv2 : (c * c)⁻¹ = c := inv_eq_of_mul_eq_one_right hc3m
      rcases hcov x x.2 with h | h | h
      · refine ⟨0, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa using h
      · refine ⟨1, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        have e : (((C ^ ((1 : Fin 3) : ℕ))⁻¹ * x : ↥B) : G) = c * c * (x : G) := by
          simp only [Fin.val_one, pow_one, Subgroup.coe_mul, InvMemClass.coe_inv, hC, hinv]
        rw [e]
        exact h
      · refine ⟨2, QuotientGroup.eq.2 ?_⟩
        rw [Subgroup.mem_subgroupOf]
        have e : (((C ^ ((2 : Fin 3) : ℕ))⁻¹ * x : ↥B) : G) = c * (x : G) := by
          simp only [Fin.val_two, pow_two, Subgroup.coe_mul, InvMemClass.coe_inv, hC, hinv2]
        rw [e]
        exact h
  rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mul_decomp {x : G} (hx : x ∈ L ⊔ T) : ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL
  have hx' : x ∈ (L : Set G) * (T : Set G) := by rw [← hmul]; exact hx
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨l, hl, t, ht, rfl⟩

theorem mem_NV1_iff (g : ↥(Subgroup.normalizer (V : Set G))) :
    (g : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G) ↔ act4f (S.frame.ρ g) e0123 = e0123 := by
  rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hz : (g : G) * S.z * (g : G)⁻¹ = S.z := by rw [h, mul_inv_cancel_right]
    have := (S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩).1 hz
    rw [S.psi_z] at this
    exact congrArg Subtype.val this
  · intro h
    have hz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
      rw [S.conj_eq_iff g ⟨S.z, S.z_mem_V⟩, S.psi_z]
      exact Subtype.ext h
    calc (g : G) * S.z = (g : G) * S.z * (g : G)⁻¹ * g := by group
      _ = S.z * g := by rw [hz]

theorem NLTV1_max (H : Subgroup G) (hMH : (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤ H)
    (hHX : H ≤ L ⊔ T) :
    H = (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ∨ H = L ⊔ T := by
  set M := (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) with hM
  by_cases hHM : H ≤ M
  · exact Or.inl (le_antisymm hHM hMH)
  right
  obtain ⟨h, hhH, hhM⟩ := IsConcreteLE.not_le_iff_exists.1 hHM
  obtain ⟨l, hl, t, ht, rfl⟩ := S.mul_decomp (hHX hhH)
  have htM : t ∈ M := ⟨Subgroup.mem_sup_right ht, S.T_le_NV1 ht⟩
  have hlH : l ∈ H := by
    have := H.mul_mem hhH (H.inv_mem (hMH htM))
    rwa [mul_inv_cancel_right] at this
  have hlM : l ∉ M := fun h' => hhM (M.mul_mem h' htM)
  set lN : ↥(Subgroup.normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
  have hs1 : Perm.sign (S.frame.ρ lN) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨lN, hl, rfl⟩)
  have hsC : S.frame.ρ lN ∉ stab45 := fun hmem =>
    hlM ⟨Subgroup.mem_sup_left hl, (S.mem_NV1_iff lN).2 (stab45_sign_fix _ hmem).2⟩
  set Y : Subgroup (Perm (Fin 6)) :=
    ((H ⊓ L).subgroupOf (Subgroup.normalizer (V : Set G))).map S.frame.ρ with hY
  have hCY : stab45 ≤ Y := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (stab45_le_alt hσ)
    have hgM : (g : G) ∈ M := ⟨Subgroup.mem_sup_left hgL,
      (S.mem_NV1_iff g).2 (by rw [hg]; exact (stab45_sign_fix σ hσ).2)⟩
    exact ⟨g, Subgroup.mem_subgroupOf.2 ⟨hMH hgM, hgL⟩, hg⟩
  have hsY : S.frame.ρ lN ∈ Y := ⟨lN, Subgroup.mem_subgroupOf.2 ⟨hlH, hl⟩, rfl⟩
  have hA := alt6_le_of_overgroup24 card_stab45 stab45_le_alt hCY hsY hs1 hsC
  refine le_antisymm hHX (sup_le (fun l' hl' => ?_) fun t' ht' =>
    hMH ⟨Subgroup.mem_sup_right ht', S.T_le_NV1 ht'⟩)
  set l'N : ↥(Subgroup.normalizer (V : Set G)) := ⟨l', S.frame.L_le hl'⟩ with hl'N
  obtain ⟨g, hg, hgρ⟩ := hA ((S.frame.image_L _).1 ⟨l'N, hl', rfl⟩)
  have hgHL := Subgroup.mem_subgroupOf.1 hg
  have hk : S.frame.ρ (g⁻¹ * l'N) = 1 := by rw [map_mul, map_inv, hgρ, inv_mul_cancel]
  have hkM : ((g⁻¹ * l'N : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ M := by
    refine ⟨Subgroup.mem_sup_left ?_, (S.mem_NV1_iff _).2 (by rw [hk]; decide)⟩
    simpa [hl'N] using L.mul_mem (L.inv_mem hgHL.2) hl'
  have := H.mul_mem hgHL.1 (hMH hkM)
  simpa [hl'N] using this

theorem NLTV1_lt : (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) < L ⊔ T := by
  refine lt_of_le_of_ne inf_le_left fun h => ?_
  have hz : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨S.z_mem_V, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hlN : l ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
      (h.symm.le (Subgroup.mem_sup_left hl)).2
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff] at hlN
    exact hlN
  rw [S.zv, Subgroup.mem_bot] at hz
  exact S.z_ne_one hz

theorem NLV1_le_L1T :
    L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤ S.L1 ⊔ T := by
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer S.T_le_NL)
  have hTN : T ⊓ L ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := fun t ht =>
    ⟨ht.2, S.T_le_NV1 ht.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) :=
    C1GN.isSylowTwoOf_of_le hsylL hTN inf_le_left
  have h := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  rw [← h, ← oTwoRes_eq_oTwoUpper]
  exact sup_le_sup le_rfl inf_le_left

theorem L1T_eq_NLTV1 : S.L1 ⊔ T = (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
  apply le_antisymm
  · exact le_inf (sup_le_sup_right S.L1_le_L T) (sup_le (S.L1_le.trans inf_le_right) S.T_le_NV1)
  · rintro x ⟨hx, hxN⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := S.mul_decomp hx
    have hlN : l ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
      have := (Subgroup.normalizer (fsuV1 T V : Set G)).mul_mem hxN
        ((Subgroup.normalizer (fsuV1 T V : Set G)).inv_mem (S.T_le_NV1 ht))
      rwa [mul_inv_cancel_right] at this
    exact (S.L1 ⊔ T).mul_mem (S.NLV1_le_L1T ⟨hl, hlN⟩) (Subgroup.mem_sup_right ht)

end Setting4

theorem mem_normalizer_centralizer_of_mem {G : Type} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ k ∈ Subgroup.normalizer (X : Set G), ∀ y ∈ Subgroup.centralizer (X : Set G),
      k * y * k⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro k hk y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have hx' : k⁻¹ * x * k ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) x).mp hx
      rwa [inv_inv] at this
    have h := hy _ hx'
    calc x * (k * y * k⁻¹) = k * ((k⁻¹ * x * k) * y) * k⁻¹ := by group
      _ = k * (y * (k⁻¹ * x * k)) * k⁻¹ := by rw [h]
      _ = k * y * k⁻¹ * x := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem o2Z_le_l0_sup {G : Type} [Group G] [Finite G] {L : Subgroup G} (hhat : IsHatA6 L) :
    o2Z L ≤ l0 L ⊔ pCoreOf 2 L := by
  obtain ⟨c, hc, -, -, hdec⟩ := exists_l0_c hhat.2.1
  intro x hx
  rcases hdec x hx with h | h | h
  · exact Subgroup.mem_sup_right h
  · have e : x = (c * c)⁻¹ * (c * c * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((l0 L).inv_mem ((l0 L).mul_mem hc hc)))
      (Subgroup.mem_sup_right h)
  · have e : x = c⁻¹ * (c * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((l0 L).inv_mem hc))
      (Subgroup.mem_sup_right h)

theorem cube_two_pow_eq_one {G : Type} [Group G] {x : G} {k : ℕ} (h2 : x ^ (2 ^ k) = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_l0_sup (hhat : IsHatA6 L) {Lp : Subgroup G}
    (P : S14.PlusData S Lp) : S.L1 ≤ l0 L ⊔ (Lp ⊔ T) := by
  change oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨⟨hyL, hyN⟩, m, hm, hym⟩
  set yN : ↥(Subgroup.normalizer (V : Set G)) := ⟨y, S.frame.L_le hyL⟩ with hyNdef
  have hfix : act4f (S.frame.ρ yN) e0123 = e0123 := (S.mem_NV1_iff yN).1 hyN
  have hpow : S.frame.ρ yN ^ m = 1 := by
    rw [← map_pow]
    have : yN ^ m = 1 := Subtype.ext (by simpa using hym)
    rw [this, map_one]
  have h3 : S.frame.ρ yN ^ 3 = 1 := by
    have h1 : orderOf (S.frame.ρ yN) ∣ m := orderOf_dvd_of_pow_eq_one hpow
    have h2 : orderOf (S.frame.ρ yN) ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one (fix45_exp _ hfix)
    have hodd : ¬ 2 ∣ orderOf (S.frame.ρ yN) := fun h2' =>
      (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr (h2'.trans h1))
    have hcop : Nat.Coprime (orderOf (S.frame.ρ yN)) 4 :=
      (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)).symm
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h2)
  obtain ⟨x, hxLp, hxρ⟩ := P.three _ (fix45_odd _ hfix h3)
  have hk : S.frame.ρ (x⁻¹ * yN) = 1 := by rw [map_mul, map_inv, hxρ, inv_mul_cancel]
  have hkC := (S.rho_eq_one_iff _).1 hk
  have hkL : ((x⁻¹ * yN : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := by
    simpa [hyNdef] using L.mul_mem (L.inv_mem (P.le_L hxLp)) hyL
  have hkZ := o2Z_le_l0_sup hhat (S.centralizer_le_o2Z ⟨hkL, hkC⟩)
  have hkX : ((x⁻¹ * yN : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ l0 L ⊔ (Lp ⊔ T) :=
    sup_le_sup_left (S.pCoreOf_L_le_T.trans le_sup_right) _ hkZ
  have e : y = (x : G) * ((x⁻¹ * yN : ↥(Subgroup.normalizer (V : Set G))) : G) := by
    simp [hyNdef]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left hxLp)) hkX

theorem hat_index (hhat : IsHatA6 L) {Lp : Subgroup G}
    (P : S14.PlusData S Lp) : (Lp ⊔ T).relIndex (S.L1 ⊔ T) = 3 := by
  have hle : Lp ⊔ T ≤ S.L1 ⊔ T := sup_le_sup_right P.le_L1 T
  have heq : S.L1 ⊔ T = l0 L ⊔ (Lp ⊔ T) := by
    apply le_antisymm
    · exact sup_le (S.L1_le_l0_sup hhat P) (le_sup_right.trans le_sup_right)
    · exact sup_le (S.l0_le_L1.trans le_sup_left) hle
  have hN : Lp ⊔ T ≤ Subgroup.normalizer (l0 L : Set G) :=
    (sup_le P.le_NV S.frame.T_le).trans S.normalizer_le_l0
  rw [heq, relIndex_sup_of_normalizes hN]
  obtain ⟨c, hc, hc3, hcO, hdec⟩ := l0_decomp hhat
  have hO : pCoreOf 2 (l0 L) ≤ (Lp ⊔ T) ⊓ l0 L :=
    le_inf ((pCoreOf_l0_le.trans S.pCoreOf_L_le_T).trans le_sup_right)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  refine relIndex_eq_three hc ?_ hc3 fun x hx => ?_
  · rintro ⟨hcP, -⟩
    have hmul : ((Lp ⊔ T : Subgroup G) : Set G) = (Lp : Set G) * (T : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left Lp T P.T_le
    have hc' : c ∈ (Lp : Set G) * (T : Set G) := by rw [← hmul]; exact hcP
    obtain ⟨a, ha, t, ht, hat⟩ := Set.mem_mul.mp hc'
    have hcC : c ∈ Subgroup.centralizer (V : Set G) :=
      S.o2Z_le_centralizer (oTwoRes_le _ hc)
    set aN : ↥(Subgroup.normalizer (V : Set G)) := ⟨a, P.le_NV ha⟩ with haN
    set tN : ↥(Subgroup.normalizer (V : Set G)) := ⟨t⁻¹, S.frame.T_le (T.inv_mem ht)⟩ with htN
    have hcN : aN * tN⁻¹ = ⟨c, S.frame.L_le (o2Z_le_L (oTwoRes_le _ hc))⟩ :=
      Subtype.ext (by simp [haN, htN, hat])
    have hρ : S.frame.ρ aN = S.frame.ρ tN := by
      have h1 := (S.rho_eq_one_iff ⟨c, S.frame.L_le (o2Z_le_L (oTwoRes_le _ hc))⟩).2 hcC
      rw [← hcN, map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    obtain ⟨h4, h5, hs⟩ := P.rho (x := aN) ha
    have hD : InD6 (S.frame.ρ aN) := by
      rw [hρ]
      exact S.frame.T_D tN (T.inv_mem ht)
    have haO : a ∈ pCoreOf 2 Lp := P.mem_pCoreOf_of_K4 (x := aN) ha (S14.D_A4 _ hD h4 h5 hs)
    have hcT : c ∈ T := by
      rw [← hat]
      exact T.mul_mem (P.pCoreOf_le_T haO) ht
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨c, hcT⟩
    have hc1 : c = 1 := cube_two_pow_eq_one (by simpa using congrArg Subtype.val hk) hc3
    exact hcO (hc1 ▸ Subgroup.one_mem _)
  · rcases hdec x hx with h | h | h
    · exact Or.inl (hO h)
    · exact Or.inr (Or.inl (hO h))
    · exact Or.inr (Or.inr (hO h))

end Setting4

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_oTwoUpper_le_o2Z {Lp : Subgroup G}
    (P : S14.PlusData S Lp) : ¬ oTwoUpper (Lp ⊔ T) ≤ o2Z L := by
  intro h
  have hLp : Lp ≤ o2Z L := by
    have h1 : oTwoUpper Lp ≤ oTwoUpper (Lp ⊔ T) := by
      rw [← oTwoRes_eq_oTwoUpper, ← oTwoRes_eq_oTwoUpper]
      exact oTwoRes_mono le_sup_left
    rw [← P.eq] at h1
    exact h1.trans h
  obtain ⟨x, hxLp, hxρ⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
  have h1 := (S.rho_eq_one_iff x).2 (S.o2Z_le_centralizer (hLp hxLp))
  rw [hxρ] at h1
  exact absurd h1 (by decide)

theorem no_line {Lp : Subgroup G} (P : S14.PlusData S Lp)
    {l : Subgroup G} (hlV : l ≤ V) (hl4 : Nat.card l = 4)
    (hN : Lp ≤ Subgroup.normalizer (l : Set G)) : False := by
  classical
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one S.elemAbelian_V hv
  have hne1 : l ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hl4; omega
  obtain ⟨⟨a, haL⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne1
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  have haV := hlV haL
  obtain ⟨b, hbL, hb1, hba⟩ : ∃ b ∈ l, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : l ≤ Subgroup.zpowers a := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · rw [h x hx hx1]; exact Subgroup.mem_zpowers a
    have hc := Subgroup.card_le_of_le hsub
    rw [hl4, Nat.card_zpowers] at hc
    have : orderOf a ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hsq a haV)
    omega
  have hbV := hlV hbL
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a haV)
  have hab1 : a * b ≠ 1 := fun h => hba (by rw [eq_inv_of_mul_eq_one_right h, hainv])
  have haba : a * b ≠ a := fun h => hb1 (mul_eq_left.mp h)
  have habb : a * b ≠ b := fun h => ha1 (mul_eq_right.mp h)
  have hcover : ∀ x ∈ l, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    by_contra h
    push Not at h
    obtain ⟨x, hxL, hx1, hxa, hxb, hxab⟩ := h
    have hsub : ({1, a, b, a * b, x} : Set G) ⊆ (l : Set G) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact l.one_mem
      · exact haL
      · exact hbL
      · exact l.mul_mem haL hbL
      · exact hxL
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hl : (l : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hl4
    rw [hl] at hle
    have e1 : ({a * b, x} : Set G).ncard = 2 := Set.ncard_pair hxab.symm
    have e2 : ({b, a * b, x} : Set G).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨habb.symm, hxb.symm⟩), e1]
    have e3 : ({a, b, a * b, x} : Set G).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hba.symm, haba.symm, hxa.symm⟩), e2]
    have e4 : ({1, a, b, a * b, x} : Set G).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨ha1.symm, hb1.symm, hab1.symm, hx1.symm⟩), e3]
    omega
  set A : P6 := (S.frame.ψ ⟨a, haV⟩ : P6) with hA
  set B : P6 := (S.frame.ψ ⟨b, hbV⟩ : P6) with hB
  have key : ∀ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ Lp → ∀ w (hw : w ∈ l),
      InLine4 A B (act4f (S.frame.ρ y) (S.frame.ψ ⟨w, hlV hw⟩ : P6)) := by
    intro y hy w hw
    have hyw : (y : G) * w * (y : G)⁻¹ ∈ l :=
      (Subgroup.mem_normalizer_iff.mp (hN hy) w).mp hw
    have hpsi := S.psi_conj y ⟨w, hlV hw⟩
    have hval : act4f (S.frame.ρ y) (S.frame.ψ ⟨w, hlV hw⟩ : P6) =
        (S.frame.ψ ⟨(y : G) * w * (y : G)⁻¹, hlV hyw⟩ : P6) := by
      rw [hpsi]; rfl
    rw [hval]
    rcases hcover _ hyw with h | h | h | h
    · left
      have e : (⟨(y : G) * w * (y : G)⁻¹, hlV hyw⟩ : ↥V) = 1 := Subtype.ext h
      rw [e, map_one]; rfl
    · right; left
      have e : (⟨(y : G) * w * (y : G)⁻¹, hlV hyw⟩ : ↥V) = ⟨a, haV⟩ := Subtype.ext h
      rw [e]
    · right; right; left
      have e : (⟨(y : G) * w * (y : G)⁻¹, hlV hyw⟩ : ↥V) = ⟨b, hbV⟩ := Subtype.ext h
      rw [e]
    · right; right; right
      have e : (⟨(y : G) * w * (y : G)⁻¹, hlV hyw⟩ : ↥V) = ⟨a, haV⟩ * ⟨b, hbV⟩ := Subtype.ext h
      rw [e, map_mul]; rfl
  have hinj : ∀ (u w : G) (hu : u ∈ V) (hw : w ∈ V), u ≠ w →
      (S.frame.ψ ⟨u, hu⟩ : P6) ≠ S.frame.ψ ⟨w, hw⟩ := by
    intro u w hu hw huw h
    exact huw (congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h)))
  have hA1 : A ≠ 1 := by
    have := hinj a 1 haV V.one_mem ha1
    rwa [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, map_one] at this
  have hB1 : B ≠ 1 := by
    have := hinj b 1 hbV V.one_mem hb1
    rwa [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, map_one] at this
  have hAB : A ≠ B := hinj a b haV hbV hba.symm
  obtain ⟨x₁, hx₁, hρ₁⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
  obtain ⟨x₂, hx₂, hρ₂⟩ := P.three (swap 1 2 * swap 2 3) (by decide)
  have k1 := key x₁ hx₁ a haL
  have k2 := key x₁ hx₁ b hbL
  have k3 := key x₂ hx₂ a haL
  have k4 := key x₂ hx₂ b hbL
  rw [hρ₁] at k1 k2
  rw [hρ₂] at k3 k4
  exact no_line_c3 A B (S.frame.ψ ⟨a, haV⟩).2 (S.frame.ψ ⟨b, hbV⟩).2 hA1 hB1 hAB k1 k2 k3 k4

theorem card_autOn_ne : Nat.card ↥(autOn (L ⊔ T) V) ≠ 12096 := by
  intro h
  set H := (L ⊔ T).subgroupOf (Subgroup.normalizer (V : Set G)) with hH
  let f : ↥H →* MulAut ↥V := (conjAct V).comp H.subtype
  let g : ↥H →* Perm (Fin 6) := S.frame.ρ.comp H.subtype
  have hf : f.range = autOn (L ⊔ T) V := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : g.ker ≤ f.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact A1b.conjAct_eq_one_iff.2 ((S.rho_eq_one_iff _).1 hx)
  have h1 : f.ker.index ∣ g.ker.index := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker, Subgroup.index_ker, hf, h] at h1
  have h2 : Nat.card g.range ∣ 720 := by
    have := Subgroup.card_subgroup_dvd_card g.range
    have h720 : Nat.card (Perm (Fin 6)) = 720 := by rw [Nat.card_perm]; simp [Nat.factorial]
    rwa [h720] at this
  have := h1.trans h2
  norm_num at this

theorem not_isHatBlock (hhat : IsHatA6 L) :
    ¬ H13.IsHatA6Block L := by
  rintro ⟨hshort, -, -, hCU⟩
  obtain ⟨-, -, -, -, -, hirr⟩ := hshort
  have hcomm : ⁅V, L⁆ = V := S.irr.2.2.2.1
  have hVL : V ≤ L := by
    rw [← hcomm, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have hvl : v * l * v⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_NL (S.V_le_T hv)) l).mp hl
    exact L.mul_mem hvl (L.inv_mem hl)
  have hVQ : V ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL S.frame.L_le S.isPGroup_V
  have hVU : V ≤ QuasithinUnique.blockU L := by
    rw [← hcomm]
    exact Subgroup.commutator_mono hVQ le_rfl
  set W : Subgroup G := QuasithinUnique.blockU L ⊓ Subgroup.centralizer (o2Z L : Set G) with hW
  have hZW : QuasithinUnique.blockZ L ≤ W :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le o2Z_le_L))
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine F7.le_normalizer_inf ?_ ?_
    · exact A5.le_normalizer_commutator (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        Subgroup.le_normalizer
    · exact fun l hl => mem_normalizer_centralizer_of_mem
        (normalizer_L_le_o2Z (Subgroup.le_normalizer hl))
  have hVW : V ≤ W := le_inf hVU (Subgroup.le_centralizer_iff.mp S.o2Z_le_centralizer)
  rcases hirr W hZW inf_le_left hLW with h | h
  · have hVC : V ≤ V ⊓ Subgroup.centralizer (L : Set G) :=
      le_inf le_rfl (hVW.trans (h.le.trans inf_le_right))
    rw [S.zv] at hVC
    exact S.irr.2.1 (le_bot_iff.mp hVC)
  · obtain ⟨c, hc, -, hcO, -⟩ := exists_l0_c hhat.2.1
    have hcZ : c ∈ o2Z L := oTwoRes_le _ hc
    have hUC : QuasithinUnique.blockU L ≤ Subgroup.centralizer (o2Z L : Set G) :=
      h.symm.le.trans inf_le_right
    have hcU : c ∈ Subgroup.centralizer (QuasithinUnique.blockU L : Set G) :=
      Subgroup.le_centralizer_iff.mp hUC hcZ
    exact hcO (hCU.le ⟨o2Z_le_L hcZ, hcU⟩)

end Setting4

theorem card_autOn_dvd_quot {G : Type} [Group G] [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(autOn L V) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hO2 : CFSG.pCore 2 ↥L ≤ (autOnHom hLV).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxC : (x : G) ∈ Subgroup.centralizer (V : Set G) := hO (U3.coe_mem_pCoreOf_iff.2 hx)
    exact Subtype.ext (by
      rw [autOnHom_apply]
      exact A1b.conjAct_eq_one_iff.2 hxC)
  let φ₁ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) (autOnHom hLV) hO2
  have hφ₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨x, rfl⟩ := autOnHom_surjective hLV y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), rfl⟩
  exact Subgroup.card_dvd_of_surjective hφ₁

theorem stmt13_2_2_7_holds (h1332 : Stmt13_3_2)
    (hC137 : U3.C137StatementFive) : U3.Stmt13_2_2_7 := by
  intro G _ _ T L V Lp hH hV hZV hLp1 hLp2 hA6
  obtain ⟨h5, ⟨hTL, -, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    intro k hk
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      ((U3.mem_reducedAggregate' (hV.1 hv)).2.1 k hk).symm
  have := hab
  obtain ⟨e6⟩ := hA6
  have hdvd := card_autOn_dvd_quot hLV hO
  rw [Nat.card_congr e6.toEquiv, card_alt6] at hdvd
  have h6 : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨hn5, -⟩ | ⟨hn6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e5⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hn5
      have h1 := Nat.card_congr (e6.symm.trans e5).toEquiv
      rw [card_alt6] at h1
      have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup]; simp [Nat.factorial]
      exact absurd (h1.trans h2) (by norm_num)
    · exact hn6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      omega
    · exfalso
      obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel hl
      rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hdvd
      norm_num at hdvd
    · exfalso
      rw [card_of_lieModel_PSU_three_three hu] at hdvd
      norm_num at hdvd
  obtain ⟨S⟩ := U3.setting4_of_case_b h1332 hH hV hZV h6
  have hcharL : CharTwo L := A5.charTwo_of_faithful hH.qtke.2.1 hH.sylow hH.faithful
  have hX := charTwo_sup_of_normalizes hH.sylow.1 hTL hcharL
  have hsyl := A5.isSylowTwoOf_of_le hH.sylow (le_sup_right : T ≤ L ⊔ T)
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x hx => S.mul_decomp hx
  have htype := U3.a6_or_hatA6_of_isA6On hLV hO h5 ⟨e6⟩
  have hVL : ⁅V, L⁆ ≠ ⊥ := by rw [hV.2.2.2.1]; exact hV.2.1
  have hL32 : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun hl => by
    obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel hl
    rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hdvd
    norm_num at hdvd
  have hM := S.L1T_eq_NLTV1
  by_cases hhat : IsHatA6 L
  · have hLp := hLp1 hhat
    subst hLp
    have P := S14.plusData_l1plus S (S.hatL1Plus hhat)
    have hPM : l1plus T L V ⊔ T ≤ (L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :=
      (sup_le_sup_right P.le_L1 T).trans hM.le
    rcases hC137 G (L ⊔ T) T V L (l1plus T L V ⊔ T)
        ((L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) hX hsyl hLT hH.faithful.1.2.1 hcharL
        (Or.inr (Or.inr (Or.inl hhat))) (Or.inr (Or.inr ⟨hab, h6⟩)) le_sup_right hPM
        S.NLTV1_lt S.NLTV1_max
        (Or.inr ⟨hhat, hM ▸ S.hat_index hhat P, S.not_oTwoUpper_le_o2Z P⟩) S.reduced hVL
        (fun h => absurd h hL32) with h | h | ⟨h4, -⟩ | ⟨-, ⟨l, -, hlV, hl4, hlN⟩, -⟩
    · exact Or.inl h
    · exact absurd (h.2.2.1 hhat) (S.not_isHatBlock hhat)
    · exact absurd h4 S.card_autOn_ne
    · rw [hZV, Subgroup.card_bot, mul_one] at hl4
      exact (S.no_line P hlV hl4 (le_sup_left.trans hlN)).elim
  · have hLp := hLp2 hhat
    subst hLp
    have P := S14.plusData_L1 S hhat
    obtain ⟨e⟩ := htype.resolve_right hhat
    rcases hC137 G (L ⊔ T) T V L (S.L1 ⊔ T)
        ((L ⊔ T) ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) hX hsyl hLT hH.faithful.1.2.1 hcharL
        (Or.inr (Or.inl ⟨e⟩)) (Or.inr (Or.inr ⟨hab, h6⟩)) le_sup_right hM.le
        S.NLTV1_lt S.NLTV1_max (Or.inl hM) S.reduced hVL (fun h => absurd h hL32) with
      h | h | ⟨h4, -⟩ | ⟨-, ⟨l, -, hlV, hl4, hlN⟩, -⟩
    · exact Or.inl h
    · exact Or.inr (h.2.1 ⟨e⟩)
    · exact absurd h4 S.card_autOn_ne
    · rw [hZV, Subgroup.card_bot, mul_one] at hl4
      exact (S.no_line P hlV hl4 (le_sup_left.trans hlN)).elim

end CFSG.Quasithin.H13.A6
