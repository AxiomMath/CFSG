module

public import CFSG.Quasithin.Vol2.Ch12Sec6L24a
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6L20c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L19 S126L19a S126L20a Equiv
open scoped IsMulCommutative Pointwise

namespace S126L24

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

abbrev preV (F : Frame126 T L V) (Ŵ : Subgroup D8) : Subgroup G := (Ŵ.comap F.β).map V.subtype

omit [Finite G] in
theorem mem_preV {F : Frame126 T L V} {Ŵ : Subgroup D8} {v : G} (hv : v ∈ V) :
    v ∈ preV F Ŵ ↔ F.β ⟨v, hv⟩ ∈ Ŵ := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    rw [show (⟨v, hv⟩ : ↥V) = w from Subtype.ext hwv.symm]
    exact hw
  · intro h
    exact ⟨⟨v, hv⟩, h, rfl⟩

omit [Finite G] in
theorem preV_le (F : Frame126 T L V) (Ŵ : Subgroup D8) : preV F Ŵ ≤ V :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem beta_injective (F : Frame126 T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Function.Injective F.β := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  have h1 : (w : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨w.2, (F.β_ker w).1 hw⟩
  rw [hZ] at h1
  exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h1))

omit [Finite G] in
theorem preV_map {F : Frame126 T L V} (hinj : Function.Injective F.β) {X : Subgroup G}
    (hX : X ≤ V) : preV F ((X.comap V.subtype).map F.β) = X := by
  ext v
  constructor
  · rintro ⟨w, ⟨x, hx, hxw⟩, rfl⟩
    rw [← hinj hxw]
    exact hx
  · intro hv
    exact ⟨⟨v, hX hv⟩, ⟨⟨v, hX hv⟩, hv, rfl⟩, rfl⟩

omit [Finite G] in
theorem card_preV {F : Frame126 T L V} (hinj : Function.Injective F.β) (Ŵ : Subgroup D8) :
    Nat.card (preV F Ŵ) = Nat.card Ŵ := by
  have e1 : Nat.card (preV F Ŵ) = Nat.card ↥(Ŵ.comap F.β) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv.symm
  have e2 : (Ŵ.comap F.β).map F.β = Ŵ := Subgroup.map_comap_eq_self_of_surjective F.β_surj Ŵ
  have e3 : Nat.card ↥((Ŵ.comap F.β).map F.β) = Nat.card ↥(Ŵ.comap F.β) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv.symm
  rw [e1, ← e3, e2]

omit [Finite G] in
theorem card_V5 {F : Frame126 T L V} (hinj : Function.Injective F.β) : Nat.card F.V5 = 32 :=
  (card_preV hinj W5).trans card_W5

omit [Finite G] in
theorem mem_normalizer_preV {F : Frame126 T L V} {Ŵ : Subgroup D8} {x : G} {σ : Perm (Fin 8)}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hσ : ActsAs F x σ)
    (h1 : ∀ y ∈ Ŵ, dAct σ y ∈ Ŵ) (h2 : ∀ y ∈ Ŵ, dAct σ⁻¹ y ∈ Ŵ) :
    x ∈ Subgroup.normalizer (preV F Ŵ : Set G) := by
  have key : ∀ (x : G) (σ : Perm (Fin 8)), x ∈ Subgroup.normalizer (V : Set G) →
      ActsAs F x σ → (∀ y ∈ Ŵ, dAct σ y ∈ Ŵ) → ∀ v ∈ preV F Ŵ, x * v * x⁻¹ ∈ preV F Ŵ := by
    intro x σ hxV hσ h v hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨⟨x * w * x⁻¹, conj_mem hxV w⟩, ?_, rfl⟩
    show F.β ⟨x * w * x⁻¹, conj_mem hxV w⟩ ∈ Ŵ
    rw [hσ w _ rfl]
    exact h _ hw
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key x σ hxV hσ h1 v, fun hv => ?_⟩
  have := key x⁻¹ σ⁻¹ (Subgroup.inv_mem _ hxV) hσ.inv h2 _ hv
  rwa [show x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v by group] at this

omit [Finite G] in
theorem mem_centralizer_of_actsAs_one' {F : Frame126 T L V} (hinj : Function.Injective F.β)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (h : ActsAs F x 1) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := h ⟨v, hv⟩ ⟨x * v * x⁻¹, conj_mem hxV ⟨v, hv⟩⟩ rfl
  rw [dAct_one] at h1
  have h2 : x * v * x⁻¹ = v := congrArg Subtype.val (hinj h1)
  calc v * x = x * v * x⁻¹ * x := by rw [h2]
    _ = x * v := by group

theorem part1 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ W : Subgroup G, F.V1 ≤ W → W ≤ F.V5 →
      L₁Of L F.V1 ⊔ T ≤ Subgroup.normalizer (W : Set G) → W = F.V1 ∨ W = F.V5 := by
  intro W h1 h5 hN
  have hinj := beta_injective F hZ
  have hWV : W ≤ V := h5.trans (preV_le F W5)
  set Ŵ : Subgroup D8 := (W.comap V.subtype).map F.β with hŴ
  have hW : preV F Ŵ = W := preV_map hinj hWV
  have inv : ∀ (x : G) (σ : Perm (Fin 8)), x ∈ L₁Of L F.V1 ⊔ T →
      x ∈ Subgroup.normalizer (V : Set G) → ActsAs F x σ → ∀ y ∈ Ŵ, dAct σ y ∈ Ŵ := by
    intro x σ hx hxV hσ y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨⟨x * w * x⁻¹, conj_mem hxV w⟩,
      (Subgroup.mem_normalizer_iff.1 (hN hx) w).1 hw, (hσ w _ rfl)⟩
  obtain ⟨l, hl, hlV, hlσ⟩ := S126L1b.exists_mem_L1 F c1_mem c1_pow_three c1_block
  obtain ⟨t, ht, htσ⟩ := S126T2.exists_TL_of_Q8 F hH _ S126L1c.mem_Q8.2.2.2.2
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have h1' : W1 ≤ Ŵ := by
    intro y hy
    obtain ⟨v, rfl⟩ := F.β_surj y
    exact ⟨v, h1 ⟨v, hy, rfl⟩, rfl⟩
  have h5' : Ŵ ≤ W5 := by
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_preV w.2).1 (h5 hw)
  rcases irred_W h1' h5' (inv l c1 (Subgroup.mem_sup_left hl) hlV hlσ)
    (inv t _ (Subgroup.mem_sup_right ht.1) (hTV ht.1) htσ) with h | h
  · left
    rw [← hW, h]
    rfl
  · right
    rw [← hW, h]
    rfl

theorem part4 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.normalizer (F.V5 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  by_contra hgV
  have hle : F.V5 ≤ V ⊓ conjSubgroup V g := le_inf (preV_le F W5) fun x hx =>
    mem_conjSubgroup_iff.2 (preV_le F W5 ((Subgroup.mem_normalizer_iff.1 hg x).1 hx))
  have h8 := S126L20.card_inter_le h331 h1222 h1262 F hH hfus hgV
  have h32 := Subgroup.card_le_of_le hle
  rw [card_V5 (beta_injective F hZ)] at h32
  omega

omit [Finite G] [IsMulCommutative ↥V] in
theorem centralizerMod_le_normalizer' {V₁ U : Subgroup G} (h : V₁ ≤ U) :
    centralizerMod V₁ ⊤ U ≤ Subgroup.normalizer (U : Set G) := by
  have key : ∀ y ∈ centralizerMod V₁ ⊤ U, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro y hy u hu
    have h1 := hy.2.2 u hu
    rw [show y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u by group]
    exact U.mul_mem (h h1) hu
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key x hx u, fun hu => ?_⟩
  have := key x⁻¹ ((centralizerMod V₁ ⊤ U).inv_mem hx) _ hu
  rwa [show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group] at this

omit [Finite G] in
theorem cent_of_mem_centralizerMod {F : Frame126 T L V} {x : G} {σ : Perm (Fin 8)}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hσ : ActsAs F x σ)
    (hx : x ∈ centralizerMod F.V1 ⊤ F.V5) : ∀ y ∈ W5, dAct σ y * y⁻¹ ∈ W1 := by
  intro y hy
  obtain ⟨v, rfl⟩ := F.β_surj y
  have hv5 : (v : G) ∈ F.V5 := (mem_preV v.2).2 hy
  have hc := hx.2.2 v hv5
  set w : ↥V := ⟨x * v * x⁻¹, conj_mem hxV v⟩ with hw
  rw [← hσ v w rfl, ← map_inv, ← map_mul]
  have e : x * (v : G) * x⁻¹ * (v : G)⁻¹ = ((w * v⁻¹ : ↥V) : G) := rfl
  rw [e] at hc
  exact (mem_preV (w * v⁻¹).2).1 hc

omit [Finite G] in
theorem mem_centralizerMod_of_E16 {F : Frame126 T L V} {x : G} {σ : Perm (Fin 8)}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx1 : x ∈ Subgroup.normalizer (F.V1 : Set G))
    (hσ : ActsAs F x σ) (hE : σ ∈ E16) : x ∈ centralizerMod F.V1 ⊤ F.V5 := by
  refine ⟨Subgroup.mem_top _, hx1, fun u hu => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hu
  set w : ↥V := ⟨x * v * x⁻¹, conj_mem hxV v⟩ with hw
  have e : x * (v : G) * x⁻¹ * (v : G)⁻¹ = ((w * v⁻¹ : ↥V) : G) := rfl
  show x * (v : G) * x⁻¹ * (v : G)⁻¹ ∈ F.V1
  rw [e]
  refine ⟨w * v⁻¹, ?_, rfl⟩
  show F.β (w * v⁻¹) ∈ W1
  rw [map_mul, map_inv, hσ v w rfl]
  exact cent_of_mem_E16 hE hv

omit [Finite G] [IsMulCommutative ↥V] in
theorem exists_pow_eq {X : Subgroup G} {l t : G} (hl : l ∈ X)
    (ht : ∀ n : ℕ, t ^ n ∈ Subgroup.normalizer (X : Set G)) (n : ℕ) :
    ∃ l' ∈ X, (l * t) ^ n = l' * t ^ n := by
  induction n with
  | zero => exact ⟨1, X.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹),
      X.mul_mem hl' ((Subgroup.mem_normalizer_iff.1 (ht n) l).1 hl), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

omit [Finite G] [IsMulCommutative ↥V] in
theorem exists_pow_mem_of_mem_sup {X : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT : IsPGroup 2 T) {g : G} (hg : g ∈ X ⊔ T) : ∃ k : ℕ, g ^ 2 ^ k ∈ X := by
  have hmul : ((X ⊔ T : Subgroup G) : Set G) = (X : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left X T hTX
  obtain ⟨l, hl, t, ht, rfl⟩ : g ∈ (X : Set G) * (T : Set G) := by
    rw [← hmul]
    exact hg
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨l', hl', he⟩ := exists_pow_eq hl (fun n => hTX (T.pow_mem ht n)) (2 ^ k)
  exact ⟨k, by rw [he, htk, mul_one]; exact hl'⟩

omit [IsMulCommutative ↥V] in
theorem pow_eq_one_of_mem (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {g : G} (hg : g ∈ L ⊔ T)
    (hgC : g ∈ Subgroup.centralizer (V : Set G)) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  have hyp := hH.hyp
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hyp.normalizes hyp.sylow.1 hg
  obtain ⟨j, hj⟩ := S126L19a.isPGroup_ker h1222 hH
    ⟨⟨g ^ 2 ^ k, hk⟩, Subgroup.pow_mem _ hgC _⟩
  refine ⟨k + j, ?_⟩
  have h1 := congrArg
    (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) => ((z : ↥L) : G)) hj
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
  rw [pow_add, pow_mul]
  exact h1

theorem mem_normalizer_V5 (F : Frame126 T L V) (hH : Hyp126 G T L V) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hx1 : x ∈ Subgroup.normalizer (F.V1 : Set G)) :
    x ∈ Subgroup.normalizer (F.V5 : Set G) := by
  obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH hxL hxV
  have hb := blocks_of_mem_V1 F hx1 hσ
  have hb' := blocks_of_mem_V1 F (Subgroup.inv_mem _ hx1) hσ.inv
  exact mem_normalizer_preV hxV hσ (fun y hy => dAct_mem_W5 hb hy)
    (fun y hy => dAct_mem_W5 hb' hy)

theorem sup_le_normalizers (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    Li L F.V1 ⊔ T ≤ Subgroup.normalizer (L : Set G) ∧
      Li L F.V1 ⊔ T ≤ Subgroup.normalizer (V : Set G) ∧
      Li L F.V1 ⊔ T ≤ Subgroup.normalizer (F.V1 : Set G) ∧
      Li L F.V1 ⊔ T ≤ Subgroup.normalizer (F.V5 : Set G) := by
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTV1 : T ≤ Subgroup.normalizer (F.V1 : Set G) := S126L19b.T_le_normalizer_V1 h1222 hH
  have hL1L := S126L19b.L1_le_L F
  have hXL : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hL1L.trans Subgroup.le_normalizer) hyp.normalizes
  have hXV : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le (hL1L.trans hLV) hTV
  have hXV1 : Li L F.V1 ⊔ T ≤ Subgroup.normalizer (F.V1 : Set G) :=
    sup_le (S126L19b.L1_le_normalizer F) hTV1
  exact ⟨hXL, hXV, hXV1, fun x hx => mem_normalizer_V5 F hH (hXL hx) (hXV hx) (hXV1 hx)⟩

theorem inf_centralizerMod_le_R1 (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    (Li L F.V1 ⊔ T) ⊓ centralizerMod F.V1 ⊤ F.V5 ≤ Ri T L F.V1 := by
  obtain ⟨hXL, hXV, hXV1, hXV5⟩ := sup_le_normalizers h1222 F hH
  have hinj := beta_injective F hZ
  have htop : Li L F.V1 ⊔ T ≤ Subgroup.normalizer ((⊤ : Subgroup G) : Set G) := fun x _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (A1a.le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizerMod hXV1 htop hXV5))
    ?_
  rintro ⟨g, hgX, hgC⟩
  obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH (hXL hgX) (hXV hgX)
  have hE := mem_E16_of_cent (cent_of_mem_centralizerMod (hXV hgX) hσ hgC)
  have hσσ : σ * σ = 1 := by
    obtain ⟨u, v, rfl⟩ := hE
    rw [tau_mul, xr_self, xr_self, tau_zero]
  have h2 : ActsAs F (g * g) 1 := hσσ ▸ hσ.mul hσ (hXV hgX)
  have hgg := mem_centralizer_of_actsAs_one' hinj
    (Subgroup.mul_mem _ (hXV hgX) (hXV hgX)) h2
  have hggLT : g * g ∈ L ⊔ T :=
    sup_le_sup_right (S126L19b.L1_le_L F) T (Subgroup.mul_mem _ hgX hgX)
  obtain ⟨k, hk⟩ := pow_eq_one_of_mem h1222 hH hggLT hgg
  refine ⟨k + 1, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_succ', pow_mul, sq]
  exact hk

theorem part6 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    centralizerMod F.V1 ⊤ F.V5 = Subgroup.centralizer (V : Set G) ⊔ Ri T L F.V1 ∧
      Subgroup.centralizer (V : Set G) ⊔ Ri T L F.V1 =
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ Ri T L F.V1 ∧
      Subgroup.centralizer (F.V5 : Set G) = Subgroup.centralizer (V : Set G) ∧
      Subgroup.centralizer (V : Set G) =
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
  have hyp := hH.hyp
  have hinj := beta_injective F hZ
  have hNVM := S126L20c.normalizer_V_le h331 h1222 F hH
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTV1 : T ≤ Subgroup.normalizer (F.V1 : Set G) := S126L19b.T_le_normalizer_V1 h1222 hH
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hCM : Subgroup.centralizer (V : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (le_inf ((Subgroup.centralizer_le_normalizer _).trans hNVM) le_rfl)
      inf_le_right
  have h4 := part4 h331 h1222 h1262 F hH hfus hZ
  have hV15 : F.V1 ≤ F.V5 := Subgroup.map_mono (Subgroup.comap_mono W1_le_W5)
  refine ⟨le_antisymm ?_ ?_, by rw [← hCM], le_antisymm ?_ ?_, hCM⟩
  · intro x hx
    have hxV := h4 (centralizerMod_le_normalizer' hV15 hx)
    obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH (hNVM hxV) hxV
    have hE := mem_E16_of_cent (cent_of_mem_centralizerMod hxV hσ hx)
    obtain ⟨t, ht, htσ⟩ := S126T2.exists_TL_of_Q8 F hH σ (E16_le_Q8 hE)
    have htR : t ∈ Ri T L F.V1 := inf_centralizerMod_le_R1 h1222 F hH hZ
      ⟨Subgroup.mem_sup_right ht.1, mem_centralizerMod_of_E16 (hTV ht.1) (hTV1 ht.1) htσ hE⟩
    have h1 : ActsAs F (x * t⁻¹) 1 := by
      have := hσ.mul htσ.inv (Subgroup.inv_mem _ (hTV ht.1))
      rwa [mul_inv_cancel] at this
    have hxt := mem_centralizer_of_actsAs_one' hinj
      (Subgroup.mul_mem _ hxV (Subgroup.inv_mem _ (hTV ht.1))) h1
    rw [show x = (x * t⁻¹) * t by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxt) (Subgroup.mem_sup_right htR)
  · refine sup_le ?_ ?_
    · intro x hx
      refine ⟨Subgroup.mem_top _, ?_, fun u hu => ?_⟩
      · exact Subgroup.centralizer_le_normalizer _
          (Subgroup.centralizer_le (preV_le F W1) hx)
      · have hc := Subgroup.mem_centralizer_iff.1 hx u (preV_le F W5 hu)
        rw [show x * u * x⁻¹ * u⁻¹ = 1 by rw [← hc]; group]
        exact Subgroup.one_mem _
    · intro r hr
      have hrT := hR1T hr
      obtain ⟨σ, -, hσ⟩ := actsAs_of_mem_T F hrT
      exact mem_centralizerMod_of_E16 (hTV hrT) (hTV1 hrT) hσ
        (S126L1b.mem_E16 F hTV hR1T hr hσ)
  · intro x hx
    have hxV := h4 (Subgroup.centralizer_le_normalizer _ hx)
    obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH (hNVM hxV) hxV
    have h1 : σ = 1 := eq_one_of_fix fun y hy => by
      obtain ⟨v, rfl⟩ := F.β_surj y
      have hv5 : (v : G) ∈ F.V5 := (mem_preV v.2).2 hy
      have hc := Subgroup.mem_centralizer_iff.1 hx v hv5
      have hvx : (v : G) = x * v * x⁻¹ := by rw [← hc]; group
      exact (hσ v v hvx).symm
    rw [h1] at hσ
    exact mem_centralizer_of_actsAs_one' hinj hxV hσ
  · exact Subgroup.centralizer_le (preV_le F W5)

end S126L24

end CFSG.Quasithin.H13
