module

public import CFSG.Quasithin.H13.A7AltFive
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.SteinbergCBAlternatingFive

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Quasithin

@[expose] def kleinV0Set : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kleinV0Set_mul : ∀ a ∈ kleinV0Set, ∀ b ∈ kleinV0Set, a * b ∈ kleinV0Set := by
  decide +kernel

theorem kleinV0Set_inv : ∀ a ∈ kleinV0Set, a⁻¹ ∈ kleinV0Set := by
  decide +kernel

@[expose] def kleinV0 : Subgroup (Perm (Fin 5)) where
  carrier := {a | a ∈ kleinV0Set}
  mul_mem' {a b} ha hb := kleinV0Set_mul a ha b hb
  one_mem' := by
    show (1 : Perm (Fin 5)) ∈ kleinV0Set
    decide +kernel
  inv_mem' {a} ha := kleinV0Set_inv a ha

theorem mem_kleinV0 {a : Perm (Fin 5)} : a ∈ kleinV0 ↔ a ∈ kleinV0Set := Iff.rfl

theorem kleinV0Set_sign : ∀ a ∈ kleinV0Set, sign a = 1 := by
  decide +kernel

theorem kleinV0_le_alternating : kleinV0 ≤ alternatingGroup (Fin 5) := fun a ha =>
  mem_alternatingGroup.2 (kleinV0Set_sign a ha)

theorem card_kleinV0Set : kleinV0Set.card = 4 := by
  decide +kernel

theorem nat_card_kleinV0 : Nat.card kleinV0 = 4 := by
  rw [← card_kleinV0Set, ← Nat.card_eq_finsetCard]
  rfl

theorem exists_conj_kleinV0 {S : Subgroup (Perm (Fin 5))} (hSA : S ≤ alternatingGroup (Fin 5))
    (hS : Nat.card S = 4) :
    ∃ c ∈ alternatingGroup (Fin 5), ∀ s, s ∈ S ↔ c * s * c⁻¹ ∈ kleinV0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ X : Subgroup (Perm (Fin 5)), X ≤ alternatingGroup (Fin 5) → Nat.card X = 4 →
      IsPGroup 2 (X.subgroupOf (alternatingGroup (Fin 5))) ∧
        ¬ 2 ∣ (X.subgroupOf (alternatingGroup (Fin 5))).index := by
    intro X hXA hX
    have hc : Nat.card (X.subgroupOf (alternatingGroup (Fin 5))) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hXA).toEquiv, hX]
    refine ⟨IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), ?_⟩
    have h := (X.subgroupOf (alternatingGroup (Fin 5))).index_mul_card
    rw [hc, SteinbergCB.nat_card_alternating_five] at h
    omega
  obtain ⟨h1, h1'⟩ := key S hSA hS
  obtain ⟨h2, h2'⟩ := key kleinV0 kleinV0_le_alternating nat_card_kleinV0
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) (h1.toSylow h1')
    (h2.toSylow h2')
  have hmem : ∀ x : alternatingGroup (Fin 5), x ∈ ((h2.toSylow h2' : Sylow 2 _) :
      Subgroup (alternatingGroup (Fin 5))) ↔ c⁻¹ * x * c ∈ ((h1.toSylow h1' : Sylow 2 _) :
      Subgroup (alternatingGroup (Fin 5))) := by
    intro x
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨c, c.2, fun s => ?_⟩
  by_cases hsA : s ∈ alternatingGroup (Fin 5)
  · have h := hmem (c * ⟨s, hsA⟩ * c⁻¹)
    rw [show c⁻¹ * (c * ⟨s, hsA⟩ * c⁻¹) * c = ⟨s, hsA⟩ by group, IsPGroup.toSylow_coe,
      IsPGroup.toSylow_coe, mem_subgroupOf, mem_subgroupOf] at h
    exact h.symm
  · constructor
    · intro hs
      exact absurd (hSA hs) hsA
    · intro h
      exfalso
      apply hsA
      have h' := mul_mem (mul_mem (inv_mem c.2) (kleinV0_le_alternating h)) c.2
      rwa [show (c : Perm (Fin 5))⁻¹ * (c * s * (c : Perm (Fin 5))⁻¹) * c = s by group] at h'

theorem fix_four_of_mem_normalizer_kleinV0 {σ : Perm (Fin 5)}
    (hσ : ∀ a ∈ kleinV0Set, σ * a * σ⁻¹ ∈ kleinV0Set) : σ 4 = 4 :=
  fix_four_of_normalizes_V0 σ (hσ _ (mem_kleinV0.2 (by decide +kernel)))
    (hσ _ (mem_kleinV0.2 (by decide +kernel)))

theorem fixed_of_kleinV0 : ∀ m : Fin 5 → ZMod 2, ∑ i, m i = 0 →
    (∀ a ∈ kleinV0Set, ∀ i, m (a⁻¹ i) = m i) →
    ∀ σ : Perm (Fin 5), σ 4 = 4 → ∀ i, m (σ⁻¹ i) = m i := by
  intro m hm ha σ hσ
  refine fixed_of_V0 m hm (fun i => ?_) (fun i => ?_) σ hσ
  · have := ha (swap 0 1 * swap 2 3) (by decide +kernel) i
    rwa [show (swap 0 1 * swap 2 3 : Perm (Fin 5))⁻¹ = swap 0 1 * swap 2 3 by decide +kernel]
      at this
  · have := ha (swap 0 2 * swap 1 3) (by decide +kernel) i
    rwa [show (swap 0 2 * swap 1 3 : Perm (Fin 5))⁻¹ = swap 0 2 * swap 1 3 by decide +kernel]
      at this

theorem threeCycle_normalizes_kleinV0 :
    ∀ a ∈ kleinV0Set, (swap 0 1 * swap 1 2 : Perm (Fin 5)) * a * (swap 0 1 * swap 1 2)⁻¹ ∈
      kleinV0Set := by
  decide +kernel

@[expose] def NormalizesKleinV0 (σ : Perm (Fin 5)) : Prop :=
  ∀ a ∈ kleinV0Set, σ * a * σ⁻¹ ∈ kleinV0Set

instance (σ : Perm (Fin 5)) : Decidable (NormalizesKleinV0 σ) := by
  unfold NormalizesKleinV0
  infer_instance

@[expose] def InvertsCond (σ κ : Perm (Fin 5)) : Prop :=
  NormalizesKleinV0 σ → NormalizesKleinV0 κ → κ ^ 3 = 1 → κ ∉ kleinV0Set →
    σ * κ * σ⁻¹ * κ ∈ kleinV0Set → sign σ = -1

instance (σ κ : Perm (Fin 5)) : Decidable (InvertsCond σ κ) := by
  unfold InvertsCond
  infer_instance

theorem invertsCond_all : ∀ σ κ : Perm (Fin 5), InvertsCond σ κ := by
  decide +kernel

theorem sign_eq_neg_one_of_inverts {σ κ : Perm (Fin 5)} (hσ : NormalizesKleinV0 σ)
    (hκ : NormalizesKleinV0 κ) (hκ3 : κ ^ 3 = 1) (hκV : κ ∉ kleinV0Set)
    (hinv : σ * κ * σ⁻¹ * κ ∈ kleinV0Set) : sign σ = -1 :=
  invertsCond_all σ κ hσ hκ hκ3 hκV hinv


theorem toAdd_allOnes_zpow (k : ℤ) (i : Fin 5) :
    Multiplicative.toAdd (G6.allOnes 5 ^ k) i = (k : ZMod 2) := by
  rw [toAdd_zpow]
  simp [G6.allOnes]

theorem altDn_five_ker_eq_bot : (FFModel.altDn 5).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  have hx2 : G6.allOnes 5 ^ k ∈ G6.coreMod 5 := hx2
  rw [G6.mem_coreMod] at hx2
  simp only [toAdd_allOnes_zpow, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hx2
  have hk : (k : ZMod 2) = 0 := by
    have h5 : (5 : ZMod 2) = 1 := by decide
    rwa [nsmul_eq_mul, Nat.cast_ofNat, h5, one_mul] at hx2
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_allOnes_zpow, hk]
  rfl

theorem altDn_five_mk_injective :
    Function.Injective (QuotientGroup.mk : ↥(FFModel.altDn 5).sec →
      ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) := by
  intro a b h
  rw [QuotientGroup.eq, mem_subgroupOf, altDn_five_ker_eq_bot, Subgroup.mem_bot] at h
  have h' : a⁻¹ * b = 1 := Subtype.ext h
  rw [inv_mul_eq_one] at h'
  exact h'

section Module

variable {G : Type} [Group G]

theorem nat_card_sylow_two_of_card_sixty {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 60)
    (P : Sylow 2 H) : Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have h1 := (P : Subgroup H).index_mul_card
  rw [hH, hk] at h1
  have h2 := P.not_dvd_index
  have hk6 : k < 6 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    have hpos : 0 < (P : Subgroup H).index := Nat.pos_of_ne_zero
      (fun h => by rw [h, zero_mul] at h1; norm_num at h1)
    nlinarith
  rw [hk]
  interval_cases k <;> omega

theorem IsA5ModuleUnder.conj_eq_of_fixed [Finite G] {K W S : Subgroup G}
    (hW : IsA5ModuleUnder K W) (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.relIndex K) {x : G}
    (hxK : x ∈ K) (hxS : x ∈ normalizer (S : Set G)) {w : G} (hwW : w ∈ W)
    (hwS : ∀ s ∈ S, s * w * s⁻¹ = w) : x * w * x⁻¹ = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : K ≤ normalizer (W : Set G) ∧ ∃ π : alternatingGroup (Fin 5) →* autOn K W,
      Function.Surjective π ∧ ∃ β : (⊤ : Subgroup W) →* (FFModel.altDn 5).sec ⧸
        (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec,
        (∀ u : (⊤ : Subgroup W), β u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W)) ∧
        ∀ (γ : alternatingGroup (Fin 5)) (u : (⊤ : Subgroup W)) (m : G6.coreMod 5)
          (hu : ((π γ : autOn K W) : MulAut W) (u : W) ∈ (⊤ : Subgroup W))
          (hm : G6.permAct 5 (γ : Perm (Fin 5)) (m : G6.PermMod 5) ∈ G6.coreMod 5),
          β u = QuotientGroup.mk m →
            β ⟨((π γ : autOn K W) : MulAut W) (u : W), hu⟩ =
              QuotientGroup.mk ⟨G6.permAct 5 (γ : Perm (Fin 5)) (m : G6.PermMod 5), hm⟩ := by
    obtain ⟨hKW, hcomm, π, hπs, -, -, -, -, -, -, β, -, hβk, hβe⟩ := hW
    exact ⟨hKW, π, hπs, β, hβk, hβe⟩
  obtain ⟨hKW, π, hπs, β, hβk, hβe⟩ := hW'
  let f : K →* autOn K W := ((conjAct W).comp (inclusion hKW)).codRestrict (autOn K W)
    fun k => Subgroup.mem_map_of_mem _ (show (⟨k, hKW k.2⟩ : normalizer (W : Set G)) ∈
      K.subgroupOf (normalizer (W : Set G)) from k.2)
  have hfw : ∀ (k : K) (u : W), (((f k : autOn K W) : MulAut W) u : G) = k * u * (k : G)⁻¹ :=
    fun _ _ => rfl
  have hfs : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨⟨y, hyN⟩, hyK, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨⟨y, hyK⟩, rfl⟩
  set wW : W := ⟨w, hwW⟩ with hwWdef
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨γ, hγ⟩ := hπs (f ⟨x, hxK⟩)
  have hgoal : (((π γ : autOn K W) : MulAut W) wW) = wW → x * w * x⁻¹ = w := by
    intro h
    have h' := congrArg (fun u : W => (u : G)) h
    rw [hγ, hfw] at h'
    exact h'
  apply hgoal
  have hker' : π.ker = ⊥ ∨ π.ker = ⊤ :=
    @IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 5)) _ hsimple π.ker
      (MonoidHom.normal_ker π)
  rcases hker' with hker | hker
  swap
  · have : γ ∈ π.ker := hker ▸ mem_top γ
    rw [MonoidHom.mem_ker.1 this]
    rfl
  have hπi : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  have hS1 : IsPGroup 2 (S.subgroupOf K) := hS2.comap_of_injective K.subtype K.subtype_injective
  set P1 : Sylow 2 K := hS1.toSylow hSodd with hP1def
  have hP1 : (P1 : Subgroup K) = S.subgroupOf K := IsPGroup.toSylow_coe hS1 hSodd
  set P2 : Sylow 2 (autOn K W) := P1.mapSurjective hfs with hP2def
  have hP2 : (P2 : Subgroup (autOn K W)) = (S.subgroupOf K).map f := by
    rw [hP2def, Sylow.coe_mapSurjective, hP1]
  have hP2card : Nat.card P2 = 4 := by
    refine nat_card_sylow_two_of_card_sixty ?_ P2
    rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hπi, hπs⟩).toEquiv]
    exact SteinbergCB.nat_card_alternating_five
  set S' : Subgroup (alternatingGroup (Fin 5)) := (P2 : Subgroup (autOn K W)).comap π
    with hS'def
  have hS'card : Nat.card S' = 4 := by
    have h1 : S'.map π = P2 := Subgroup.map_comap_eq_self_of_surjective hπs _
    have h2 : Nat.card (S'.map π) = Nat.card S' := Subgroup.card_map_of_injective hπi
    rw [h1, hP2card] at h2
    exact h2.symm
  set Sp : Subgroup (Perm (Fin 5)) := S'.map (alternatingGroup (Fin 5)).subtype with hSpdef
  have hSpA : Sp ≤ alternatingGroup (Fin 5) := map_subtype_le _
  have hSpcard : Nat.card Sp = 4 := by
    rw [hSpdef, Subgroup.card_map_of_injective (subtype_injective _), hS'card]
  obtain ⟨c, -, hc⟩ := exists_conj_kleinV0 hSpA hSpcard
  have hγS' : ∀ s ∈ S', γ * s * γ⁻¹ ∈ S' := by
    intro s hs
    rw [hS'def, Subgroup.mem_comap] at hs ⊢
    rw [map_mul, map_mul, map_inv, hγ]
    rw [hP2] at hs ⊢
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.1 hs
    rw [← hks, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem f ?_
    rw [mem_subgroupOf] at hk ⊢
    exact (mem_normalizer_iff.1 hxS k).1 hk
  have hmemSp : ∀ p : Perm (Fin 5), p ∈ Sp → ∃ s ∈ S', (s : Perm (Fin 5)) = p := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hp
    exact ⟨s, hs, rfl⟩
  have hσN : NormalizesKleinV0 (c * (γ : Perm (Fin 5)) * c⁻¹) := by
    intro a ha
    have hs : c⁻¹ * a * c ∈ Sp := (hc _).2 (by
      rw [show c * (c⁻¹ * a * c) * c⁻¹ = a by group]
      exact ha)
    obtain ⟨s, hsS', hsa⟩ := hmemSp _ hs
    have h1 := hγS' s hsS'
    have h2 : (γ : Perm (Fin 5)) * (c⁻¹ * a * c) * (γ : Perm (Fin 5))⁻¹ ∈ Sp := by
      rw [← hsa]
      exact Subgroup.mem_map_of_mem _ h1
    have h3 := (hc _).1 h2
    rw [show c * ((γ : Perm (Fin 5)) * (c⁻¹ * a * c) * (γ : Perm (Fin 5))⁻¹) * c⁻¹ =
      c * (γ : Perm (Fin 5)) * c⁻¹ * a * (c * (γ : Perm (Fin 5)) * c⁻¹)⁻¹ by group] at h3
    exact h3
  have h4 : (c * (γ : Perm (Fin 5)) * c⁻¹) 4 = 4 := fix_four_of_mem_normalizer_kleinV0 hσN
  obtain ⟨m, hm⟩ : ∃ m : G6.coreMod 5, (QuotientGroup.mk m : (FFModel.altDn 5).sec ⧸
      (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = β ⟨wW, mem_top _⟩ :=
    QuotientGroup.mk_surjective _
  have hfix : ∀ s ∈ S', G6.permAct 5 (s : Perm (Fin 5)) (m : G6.PermMod 5) = m := by
    intro s hs
    have hsP2 : π s ∈ (P2 : Subgroup (autOn K W)) := hs
    rw [hP2] at hsP2
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.1 hsP2
    have hkw : ((π s : autOn K W) : MulAut W) wW = wW := by
      rw [← hks]
      apply Subtype.ext
      rw [hfw]
      exact hwS k (mem_subgroupOf.1 hk)
    have h1 := hβe s ⟨wW, mem_top _⟩ m (mem_top _) (G6.permAct_mem_coreMod _ m.2) hm.symm
    rw [show (⟨((π s : autOn K W) : MulAut W) wW, mem_top _⟩ : (⊤ : Subgroup W)) =
      ⟨wW, mem_top _⟩ from Subtype.ext hkw, ← hm] at h1
    exact (congrArg Subtype.val (altDn_five_mk_injective h1)).symm
  set mv : Fin 5 → ZMod 2 := Multiplicative.toAdd (m : G6.PermMod 5) with hmv
  have hfixv : ∀ s ∈ S', ∀ i, mv ((s : Perm (Fin 5))⁻¹ i) = mv i := by
    intro s hs i
    have := congrFun (congrArg Multiplicative.toAdd (hfix s hs)) i
    rw [G6.permAct_apply] at this
    exact this
  set nv : Fin 5 → ZMod 2 := fun i => mv (c⁻¹ i) with hnv
  have hnsum : ∑ i, nv i = 0 := by
    rw [hnv]
    simp only
    rw [Equiv.sum_comp c⁻¹ mv]
    exact m.2
  have hnfix : ∀ a ∈ kleinV0Set, ∀ i, nv (a⁻¹ i) = nv i := by
    intro a ha i
    have hs : c⁻¹ * a * c ∈ Sp := (hc _).2 (by
      rw [show c * (c⁻¹ * a * c) * c⁻¹ = a by group]
      exact ha)
    obtain ⟨s, hsS', hsa⟩ := hmemSp _ hs
    have h1 := hfixv s hsS' (c⁻¹ i)
    rw [hsa] at h1
    simp only [hnv]
    rw [← h1]
    congr 1
    simp [Perm.mul_apply, mul_inv_rev]
  have h5 := fixed_of_kleinV0 nv hnsum hnfix _ h4
  have hγm : ∀ j, mv ((γ : Perm (Fin 5))⁻¹ j) = mv j := by
    intro j
    have := h5 (c j)
    simpa [hnv, mul_inv_rev, inv_inv, Perm.mul_apply] using this
  have hγm' : G6.permAct 5 (γ : Perm (Fin 5)) (m : G6.PermMod 5) = m := by
    apply Multiplicative.toAdd.injective
    funext j
    rw [G6.permAct_apply]
    exact hγm j
  have h6 := hβe γ ⟨wW, mem_top _⟩ m (mem_top _) (G6.permAct_mem_coreMod _ m.2) hm.symm
  have h7 : (⟨G6.permAct 5 (γ : Perm (Fin 5)) (m : G6.PermMod 5),
      G6.permAct_mem_coreMod _ m.2⟩ : (FFModel.altDn 5).sec) = m := Subtype.ext hγm'
  rw [h7] at h6
  have h8 := h6.trans hm
  have hβi : Function.Injective β := by
    intro a b hab
    have h : β (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    rw [hβk, Subgroup.mem_bot] at h
    have h' : a⁻¹ * b = 1 := Subtype.ext h
    rw [inv_mul_eq_one] at h'
    exact h'
  exact congrArg Subtype.val (hβi h8)

theorem IsA5ModuleSum.conj_eq_of_fixed [Finite G] {K U S : Subgroup G}
    (hU : IsA5ModuleSum K U) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hSK : S ≤ K)
    (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.relIndex K) {x : G} (hxK : x ∈ K)
    (hxS : x ∈ normalizer (S : Set G)) {u : G} (huU : u ∈ U)
    (huS : ∀ s ∈ S, s * u * s⁻¹ = u) : x * u * x⁻¹ = u := by
  rcases hU with hU | ⟨W₁, W₂, h₁, h₂, hinf, hsup⟩
  · exact IsA5ModuleUnder.conj_eq_of_fixed hU hS2 hSodd hxK hxS huU huS
  have hW₁U : W₁ ≤ U := hsup ▸ le_sup_left
  have hW₂U : W₂ ≤ U := hsup ▸ le_sup_right
  have hN : W₁ ≤ normalizer (W₂ : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hUc a (hW₁U ha) b (hW₂U hb), mul_inv_cancel_right]
      exact hb
    · intro hb
      have hc : a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := hUc a (hW₁U ha) _ (hW₂U hb)
      have key : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [hc]
          _ = b := by group
      rw [← key]
      exact hb
  have hu' : u ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by
    rw [hsup]
    exact huU
  rw [coe_mul_of_left_le_normalizer_right _ _ hN] at hu'
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu'
  have hsplit : ∀ s ∈ S, s * u₁ * s⁻¹ = u₁ ∧ s * u₂ * s⁻¹ = u₂ := by
    intro s hs
    have hs1 : s * u₁ * s⁻¹ ∈ W₁ := (mem_normalizer_iff.1 (h₁.1 (hSK hs)) u₁).1 hu₁
    have hs2 : s * u₂ * s⁻¹ ∈ W₂ := (mem_normalizer_iff.1 (h₂.1 (hSK hs)) u₂).1 hu₂
    have heq : (s * u₁ * s⁻¹) * (s * u₂ * s⁻¹) = u₁ * u₂ := by
      rw [show (s * u₁ * s⁻¹) * (s * u₂ * s⁻¹) = s * (u₁ * u₂) * s⁻¹ by group]
      exact huS s hs
    have hmem : u₁⁻¹ * (s * u₁ * s⁻¹) ∈ W₁ ⊓ W₂ := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu₁) hs1, ?_⟩
      have h : u₁⁻¹ * (s * u₁ * s⁻¹) = u₂ * (s * u₂ * s⁻¹)⁻¹ := by
        calc u₁⁻¹ * (s * u₁ * s⁻¹)
            = u₁⁻¹ * ((s * u₁ * s⁻¹) * (s * u₂ * s⁻¹) * (s * u₂ * s⁻¹)⁻¹) := by group
          _ = u₁⁻¹ * (u₁ * u₂ * (s * u₂ * s⁻¹)⁻¹) := by rw [heq]
          _ = u₂ * (s * u₂ * s⁻¹)⁻¹ := by group
      rw [h]
      exact mul_mem hu₂ (inv_mem hs2)
    rw [hinf, mem_bot] at hmem
    have h1 : s * u₁ * s⁻¹ = u₁ := by
      calc s * u₁ * s⁻¹ = u₁ * (u₁⁻¹ * (s * u₁ * s⁻¹)) := by group
        _ = u₁ := by rw [hmem, mul_one]
    refine ⟨h1, ?_⟩
    rw [h1] at heq
    exact mul_left_cancel heq
  have hx1 := IsA5ModuleUnder.conj_eq_of_fixed h₁ hS2 hSodd hxK hxS hu₁ fun s hs =>
    (hsplit s hs).1
  have hx2 := IsA5ModuleUnder.conj_eq_of_fixed h₂ hS2 hSodd hxK hxS hu₂ fun s hs =>
    (hsplit s hs).2
  show x * (u₁ * u₂) * x⁻¹ = u₁ * u₂
  calc x * (u₁ * u₂) * x⁻¹ = (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) := by group
    _ = u₁ * u₂ := by rw [hx1, hx2]

end Module

end CFSG.Quasithin.H13.A7
