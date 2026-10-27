module

public import CFSG.Quasithin.Background.B610TwoW
public import CFSG.Quasithin.Background.F918Z8Kw2
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.B610

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

structure NatData (L V : Subgroup G) (F : Type) [Field F] where
  α : ↥L →* ↥(Assembly.LowTwoRank.StatedSL 2 F)
  surj : Function.Surjective α
  ker : α.ker = (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L
  β : ↥⁅V, L⁆ →* H.StdMod (Fin 2) F
  βsurj : Function.Surjective β
  βker : β.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆
  βeq : ∀ (a : ↥L) (u v : ↥⁅V, L⁆), (v : G) = a * u * a⁻¹ →
    Multiplicative.toAdd (β v) =
      ((α a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β u))

theorem exists_natData {n : ℕ} {L V : Subgroup G} (hn : 2 ≤ n) (h : IsNaturalL2Prime n L V) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      Nonempty (NatData L V F) := by
  rcases h with ⟨-, F, _, _, hF, -, α, hα, hαk, β, hβ, hβk, hβe⟩ | ⟨h1, -⟩
  · exact ⟨F, inferInstance, inferInstance, hF, ⟨⟨α, hα, hαk, β, hβ, hβk, hβe⟩⟩⟩
  · omega

variable {L V : Subgroup G} {F : Type} [Field F] (D : NatData L V F)

noncomputable abbrev NatData.act : ↥(nLV L V) →* MulAut (H.StdMod (Fin 2) F) :=
  rhoHom D.β D.βsurj D.βker

noncomputable abbrev NatData.img (X : Subgroup G) : Subgroup (MulAut (H.StdMod (Fin 2) F)) :=
  (X.subgroupOf (nLV L V)).map D.act

theorem NatData.act_of_mem (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) :
    D.act ⟨l, Subgroup.le_normalizer l.2, hLV l.2⟩ =
      H.natAut (Assembly.LowTwoRank.StatedSL 2 F) (D.α l) :=
  rho_of_mem D.β D.βsurj D.βker hLV D.α D.βeq l

theorem NatData.act_eq_one (hLV : L ≤ Subgroup.normalizer (V : Set G)) (g : ↥(nLV L V))
    (hg : (g : G) ∈ Subgroup.centralizer (V : Set G)) : D.act g = 1 :=
  rho_eq_one D.β D.βsurj D.βker hLV g hg

theorem NatData.card_mul_card_le [Finite G] [Finite F]
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (X : Subgroup G) :
    Nat.card (H.StdMod (Fin 2) F) * Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)) ≤
      Nat.card ↥(fixV (D.img X)) * Nat.card V := by
  set W : Subgroup G := ⁅V, L⁆ with hW
  have hWV : W ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  set C₁ : Subgroup G := W ⊓ Subgroup.centralizer (X : Set G) with hC₁
  have hc1 : (C₁.subgroupOf W).map D.β ≤ fixV (D.img X) := by
    rintro _ ⟨w, hw, rfl⟩ e he
    obtain ⟨x, hx, rfl⟩ := he
    rw [rhoHom_apply, rho_apply]
    congr 1
    apply Subtype.ext
    rw [coe_cW]
    have hwX := (Subgroup.mem_subgroupOf.mp hw).2
    have h1 := Subgroup.mem_centralizer_iff.mp hwX _ (Subgroup.mem_subgroupOf.mp hx)
    rw [h1, mul_inv_cancel_right]
  set f₁ : ↥(C₁.subgroupOf W) →* H.StdMod (Fin 2) F := D.β.comp (C₁.subgroupOf W).subtype
    with hf₁
  have hf₁r : f₁.range = (C₁.subgroupOf W).map D.β := by
    rw [hf₁, MonoidHom.range_comp, Subgroup.range_subtype]
  have hk₁ : Nat.card f₁.ker ≤ Nat.card D.β.ker := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥(C₁.subgroupOf W)) : ↥W), x.2⟩) fun x y hxy => ?_
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    exact this
  have hC₁W : C₁ ≤ W := inf_le_left
  have hcC₁ : Nat.card ↥(C₁.subgroupOf W) = Nat.card C₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₁W).toEquiv
  have e1 := Subgroup.card_ker_mul_card_range f₁
  have e2 := Subgroup.card_ker_mul_card_range D.β
  rw [MonoidHom.range_eq_top.mpr D.βsurj, Subgroup.card_top] at e2
  have hcomm : ∀ a ∈ W, ∀ b ∈ V ⊓ Subgroup.centralizer (X : Set G), a * b = b * a :=
    fun a ha b hb => hVc a (hWV ha) b hb.1
  have e3 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : W ⊓ (V ⊓ Subgroup.centralizer (X : Set G)) = C₁ := by
    rw [hC₁, ← inf_assoc, inf_eq_left.mpr hWV]
  rw [hinf] at e3
  have hsup : Nat.card ↥(W ⊔ (V ⊓ Subgroup.centralizer (X : Set G))) ≤ Nat.card V :=
    Subgroup.card_le_of_le (sup_le hWV inf_le_left)
  have hkpos : 0 < Nat.card D.β.ker := Nat.card_pos
  have hfix : Nat.card ↥((C₁.subgroupOf W).map D.β) ≤ Nat.card ↥(fixV (D.img X)) :=
    Subgroup.card_le_of_le hc1
  have key : Nat.card D.β.ker * (Nat.card (H.StdMod (Fin 2) F) *
      Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G))) ≤
      Nat.card D.β.ker * (Nat.card ↥(fixV (D.img X)) * Nat.card V) := by
    calc Nat.card D.β.ker * (Nat.card (H.StdMod (Fin 2) F) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)))
        = Nat.card W * Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)) := by rw [← e2]; ring
      _ = Nat.card ↥(W ⊔ (V ⊓ Subgroup.centralizer (X : Set G))) * Nat.card C₁ := e3.symm
      _ ≤ Nat.card V * Nat.card C₁ := Nat.mul_le_mul_right _ hsup
      _ = Nat.card V * (Nat.card f₁.ker * Nat.card f₁.range) := by rw [e1, hcC₁]
      _ ≤ Nat.card V * (Nat.card D.β.ker * Nat.card ↥(fixV (D.img X))) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul hk₁ ?_)
          rw [hf₁r]
          exact hfix
      _ = Nat.card D.β.ker * (Nat.card ↥(fixV (D.img X)) * Nat.card V) := by ring
  exact Nat.le_of_mul_le_mul_left key hkpos

include D in
theorem NatData.card_mul_card_cent_le [Finite G]
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (H.StdMod (Fin 2) F) * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card V := by
  set W : Subgroup G := ⁅V, L⁆ with hW
  have hWV : W ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  set C₀ : Subgroup G := W ⊓ Subgroup.centralizer (L : Set G) with hC₀
  have e2 := Subgroup.card_ker_mul_card_range D.β
  rw [MonoidHom.range_eq_top.mpr D.βsurj, Subgroup.card_top, D.βker] at e2
  have hcC : Nat.card ↥(C₀.subgroupOf W) = Nat.card C₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcomm : ∀ a ∈ W, ∀ b ∈ V ⊓ Subgroup.centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => hVc a (hWV ha) b hb.1
  have e3 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : W ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = C₀ := by
    rw [hC₀, ← inf_assoc, inf_eq_left.mpr hWV]
  rw [hinf] at e3
  have hsup : Nat.card ↥(W ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) ≤ Nat.card V :=
    Subgroup.card_le_of_le (sup_le hWV inf_le_left)
  have hpos : 0 < Nat.card C₀ := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card C₀ * (Nat.card (H.StdMod (Fin 2) F) *
        Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)))
      = Nat.card W * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := by
        rw [← e2, hcC]; ring
    _ = Nat.card ↥(W ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) * Nat.card C₀ := e3.symm
    _ ≤ Nat.card V * Nat.card C₀ := Nat.mul_le_mul_right _ hsup
    _ = Nat.card C₀ * Nat.card V := by ring

omit [Group G] in
theorem pow_mul_eq {G : Type} [Group G] {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ Subgroup.normalizer (L : Set G)) :
    ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
  intro m
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', he⟩ := ih
    have htm : t ^ m ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ ht m
    have h1 : t ^ m * l * (t ^ m)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htm l).mp hl
    refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), L.mul_mem hl' h1, ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem NatData.act_faithful [Finite G] {Hp T : Subgroup G} (hred : IsTwoReducedIn Hp V)
    (hT2 : IsPGroup 2 T) (hHLT : Hp = L ⊔ T) (hHN : Hp ≤ nLV L V)
    (g : ↥(nLV L V)) (hgH : (g : G) ∈ Hp) (hg : D.act g = 1) :
    (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    (hHN (hHLT ▸ Subgroup.mem_sup_left hx : x ∈ Hp)).2
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    (hHN (hHLT ▸ Subgroup.mem_sup_right hx : x ∈ Hp)).1
  set K : Subgroup G := Hp ⊓ (D.act.ker).map (nLV L V).subtype with hK
  have hgK : (g : G) ∈ K := ⟨hgH, g, hg, rfl⟩
  have hmemK : ∀ {x : G}, x ∈ K → ∃ hx : x ∈ nLV L V, D.act ⟨x, hx⟩ = 1 := by
    rintro x ⟨-, y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have hKH : K ≤ Hp := inf_le_left
  have hconj : ∀ h ∈ Hp, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    intro h hh x hx
    obtain ⟨hxN, hx1⟩ := hmemK hx
    refine ⟨Hp.mul_mem (Hp.mul_mem hh (hKH hx)) (Hp.inv_mem hh),
      ⟨h, hHN hh⟩ * ⟨x, hxN⟩ * (⟨h, hHN hh⟩ : ↥(nLV L V))⁻¹, MonoidHom.mem_ker.mpr ?_, rfl⟩
    rw [map_mul, map_mul, hx1, mul_one, map_inv, mul_inv_cancel]
  have hHK : Hp ≤ Subgroup.normalizer (K : Set G) := fun h hh =>
    B6.mem_normalizer_of_forall_mem (hconj h hh) fun x hx => by
      simpa using hconj h⁻¹ (Hp.inv_mem hh) x hx
  have hpow : ∀ x ∈ K, ∃ k : ℕ, x ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have hxLT : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN, ← hHLT]
      exact hKH hx
    obtain ⟨l, hl, t, ht, rfl⟩ := hxLT
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_eq hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    refine ⟨a, ?_⟩
    rw [he]
    have hK' : l' ∈ K := he ▸ K.pow_mem hx _
    obtain ⟨hl'N, hl'1⟩ := hmemK hK'
    have h1 := D.act_of_mem hLV ⟨l', hl'⟩
    have h2 : D.α ⟨l', hl'⟩ = 1 := by
      apply H.natAut_injective (Assembly.LowTwoRank.StatedSL 2 F)
      rw [← h1, map_one]
      exact hl'1
    have h3 : (⟨l', hl'⟩ : ↥L) ∈ D.α.ker := h2
    rw [D.ker, Subgroup.mem_subgroupOf] at h3
    exact h3.2
  exact hred.2.2.2 K hKH hHK hpow hgK

theorem NatData.offender_core [Finite G] [Finite F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hV : IsElemAbelian 2 V) {Hp : Subgroup G} (hLH : L ≤ Hp)
    (hHN : Hp ≤ nLV L V)
    (hfaith : ∀ g : ↥(nLV L V), (g : G) ∈ Hp → D.act g = 1 →
      (g : G) ∈ Subgroup.centralizer (V : Set G))
    {B : Subgroup (MulAut (IntMod V hV))} (hBH : B ≤ autI hV Hp) (hB1 : B ≠ ⊥)
    (hBe : IsElemAbelian2 B)
    (hoff : Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B)) :
    B ≤ autI hV L ∧ Nat.card B = 2 ^ n ∧ 2 ^ n * Nat.card (fixV B) ≤ Nat.card (IntMod V hV) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := fun x hx => (hHN (hLH hx)).2
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    IntMod.val_comm (hV := hV) ⟨a, ha⟩ ⟨b, hb⟩
  have hHV : Hp ≤ Subgroup.normalizer (V : Set G) := fun x hx => (hHN hx).2
  set P : Subgroup G := Hp ⊓ (B.comap (convI hV)).map (Subgroup.normalizer (V : Set G)).subtype
    with hP
  have hPH : P ≤ Hp := inf_le_left
  have hPN : P ≤ nLV L V := hPH.trans hHN
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans hHV
  have hmemP : ∀ {x : G} (hx : x ∈ P), convI hV ⟨x, hPV hx⟩ ∈ B := by
    rintro x ⟨-, y, hy, rfl⟩
    exact hy
  have hPB : autI hV P = B := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨y, hyP, rfl⟩ := (mem_autI hV).mp hφ
      exact hmemP hyP
    · intro φ hφ
      obtain ⟨y, hyH, hy⟩ := (mem_autI hV).mp (hBH hφ)
      refine (mem_autI hV).mpr ⟨y, ⟨hyH, y, ?_, rfl⟩, hy⟩
      rw [← hy] at hφ
      exact hφ
  set P' : Subgroup ↥(nLV L V) := P.subgroupOf (nLV L V) with hP'
  set f : ↥P' →* MulAut (H.StdMod (Fin 2) F) := D.act.comp P'.subtype with hf
  set g : ↥P' →* MulAut (IntMod V hV) :=
    (convI hV).comp ((Subgroup.inclusion (fun x hx => hx.2 : nLV L V ≤
      Subgroup.normalizer (V : Set G))).comp P'.subtype) with hg
  have hcV : ∀ x : ↥P', g x = 1 ↔ ((x : ↥(nLV L V)) : G) ∈ Subgroup.centralizer (V : Set G) :=
    fun x => convI_eq_one_iff hV _
  have hker : f.ker = g.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hcV]
    constructor
    · intro h
      exact hfaith _ (hPH (Subgroup.mem_subgroupOf.mp x.2)) h
    · intro h
      exact D.act_eq_one hLV _ h
  have hEf : D.img P = f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hBg : B = g.range := by
    rw [← hPB]
    ext φ
    rw [mem_autI, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hyP, rfl⟩
      exact ⟨⟨⟨y, hPN hyP⟩, Subgroup.mem_subgroupOf.mpr hyP⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨_, ((x : ↥(nLV L V))).2.2⟩, Subgroup.mem_subgroupOf.mp x.2, rfl⟩
  have hcard : Nat.card (D.img P) = Nat.card B := by
    have e1 := Subgroup.card_ker_mul_card_range f
    have e2 := Subgroup.card_ker_mul_card_range g
    rw [hker] at e1
    have hpos : 0 < Nat.card g.ker := Nat.card_pos
    rw [hEf, hBg]
    exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  have hEe : IsElemAbelian2 (D.img P) := by
    have hcomm : ∀ x y : ↥P', f x * f y = f y * f x := by
      intro x y
      have h1 : g x * g y = g y * g x := hBe.1 _ (hBg ▸ ⟨x, rfl⟩) _ (hBg ▸ ⟨y, rfl⟩)
      have h2 : g (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have h3 : f (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [← MonoidHom.mem_ker, hker, MonoidHom.mem_ker]
        exact h2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
      calc f x * f y = f x * f y * (f x)⁻¹ * (f y)⁻¹ * (f y * f x) := by group
        _ = f y * f x := by rw [h3, one_mul]
    have hsq : ∀ x : ↥P', f x ^ 2 = 1 := by
      intro x
      have h1 : g x ^ 2 = 1 := hBe.2 _ (hBg ▸ ⟨x, rfl⟩)
      have h2 : f (x ^ 2) = 1 := by
        rw [← MonoidHom.mem_ker, hker, MonoidHom.mem_ker, map_pow]
        exact h1
      rwa [map_pow] at h2
    rw [hEf]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact hcomm x y
    · rintro _ ⟨x, rfl⟩
      exact hsq x
  have hfixB : Nat.card (fixV B) = Nat.card ↥(V ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [← hPB]
    exact card_fixV_autI hV hPV
  have hcardV : Nat.card (IntMod V hV) = Nat.card V := rfl
  have hineq := D.card_mul_card_le hVc hLV P
  rw [← hfixB] at hineq
  have hfpos : 0 < Nat.card (fixV B) := Nat.card_pos
  have hoffE : Nat.card (H.StdMod (Fin 2) F) ≤
      Nat.card (D.img P) * Nat.card ↥(fixV (D.img P)) := by
    rw [hcard]
    refine Nat.le_of_mul_le_mul_right ?_ hfpos
    calc Nat.card (H.StdMod (Fin 2) F) * Nat.card (fixV B)
        ≤ Nat.card ↥(fixV (D.img P)) * Nat.card V := hineq
      _ ≤ Nat.card ↥(fixV (D.img P)) * (Nat.card B * Nat.card (fixV B)) :=
          Nat.mul_le_mul_left _ (hcardV ▸ hoff)
      _ = Nat.card B * Nat.card ↥(fixV (D.img P)) * Nat.card (fixV B) := by ring
  have hEN : D.img P ≤ H.natNorm (Assembly.LowTwoRank.StatedSL 2 F) := by
    rintro _ ⟨x, hx, rfl⟩
    have hnorm : ∀ (y : ↥(nLV L V)), ∀ l : ↥L,
        D.act y * H.natAut (Assembly.LowTwoRank.StatedSL 2 F) (D.α l) * (D.act y)⁻¹ ∈
          H.natImage (Assembly.LowTwoRank.StatedSL 2 F) := by
      intro y l
      have hyl : (y : G) * l * (y : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp y.2.1 l).mp l.2
      refine ⟨D.α ⟨_, hyl⟩, ?_⟩
      rw [← D.act_of_mem hLV ⟨_, hyl⟩, ← D.act_of_mem hLV l, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    refine B6.mem_normalizer_of_forall_mem (fun e he => ?_) fun e he => ?_
    · obtain ⟨γ, rfl⟩ := he
      obtain ⟨l, rfl⟩ := D.surj γ
      exact hnorm x l
    · obtain ⟨γ, rfl⟩ := he
      obtain ⟨l, rfl⟩ := D.surj γ
      have := hnorm x⁻¹ l
      rwa [map_inv, inv_inv] at this
  have hEim : D.img P ≤ H.natImage (Assembly.LowTwoRank.StatedSL 2 F) :=
    B69.le_natImage_of_offender hn hF hEN (fun x hx => hEe.2 x hx)
      (fun x hx y hy => hEe.1 x hx y hy) hoffE
  have hBL : B ≤ autI hV L := by
    intro φ hφ
    rw [hBg] at hφ
    obtain ⟨x, rfl⟩ := hφ
    obtain ⟨γ, hγ⟩ := hEim (show f x ∈ D.img P by rw [hEf]; exact ⟨x, rfl⟩)
    obtain ⟨l, rfl⟩ := D.surj γ
    rw [← D.act_of_mem hLV l] at hγ
    have hxl : D.act ((x : ↥(nLV L V)) * (⟨l, Subgroup.le_normalizer l.2, hLV l.2⟩ :
        ↥(nLV L V))⁻¹) = 1 := by
      rw [map_mul, map_inv, hγ]
      exact mul_inv_cancel _
    have hxlH : (((x : ↥(nLV L V)) * (⟨l, Subgroup.le_normalizer l.2, hLV l.2⟩ :
        ↥(nLV L V))⁻¹ : ↥(nLV L V)) : G) ∈ Hp :=
      Hp.mul_mem (hPH (Subgroup.mem_subgroupOf.mp x.2)) (Hp.inv_mem (hLH l.2))
    have hC := hfaith _ hxlH hxl
    refine (mem_autI hV).mpr ⟨⟨l, hLV l.2⟩, l.2, ?_⟩
    have h1 := (convI_eq_one_iff hV ⟨_, (Subgroup.normalizer (V : Set G)).mul_mem
      ((x : ↥(nLV L V)).2.2) ((Subgroup.normalizer (V : Set G)).inv_mem (hLV l.2))⟩).mpr hC
    show convI hV ⟨l, hLV l.2⟩ = convI hV ⟨_, ((x : ↥(nLV L V))).2.2⟩
    have e : (⟨_, (Subgroup.normalizer (V : Set G)).mul_mem ((x : ↥(nLV L V)).2.2)
        ((Subgroup.normalizer (V : Set G)).inv_mem (hLV l.2))⟩ :
          ↥(Subgroup.normalizer (V : Set G))) =
        ⟨_, ((x : ↥(nLV L V))).2.2⟩ * (⟨l, hLV l.2⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ :=
      rfl
    rw [e, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  have hEle := nl2w_card_mul_card_fixV_le hn hF hEN hEe
  have hEq : Nat.card (D.img P) ≤ 2 ^ n :=
    (B42L2.card_le_of_isPGroup hEim hEe.isPGroup hn (nl2w_card_natImage hF)).1
  have hW : Nat.card (H.StdMod (Fin 2) F) = 2 ^ n * 2 ^ n := by
    rw [H.card_stdMod, Fintype.card_fin, hF, sq]
  have hE1 : D.img P ≠ ⊥ := by
    intro h
    apply hB1
    rw [← Subgroup.card_eq_one, ← hcard, h, Subgroup.card_bot]
  have hfixE : Nat.card ↥(fixV (D.img P)) ≤ 2 ^ n := by
    obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    obtain ⟨γ, hγ⟩ := hEim heE
    have hM : ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
      intro h
      apply he1'
      rw [← hγ]
      refine H.toAddMap_injective fun v => ?_
      rw [H.toAddMap_natAut, H.toAddMap_one, h, Matrix.one_mulVec]
    have hv : ∀ v : ↥(fixV (D.img P)), ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (v : H.StdMod (Fin 2) F)) =
          Multiplicative.toAdd (v : H.StdMod (Fin 2) F) := fun v => by
      have h1 : e (v : H.StdMod (Fin 2) F) = v := v.2 e heE
      rw [← hγ] at h1
      exact congrArg Multiplicative.toAdd h1
    let j : ↥(fixV (D.img P)) → {w : Fin 2 → F //
        ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w} :=
      fun v => ⟨Multiplicative.toAdd (v : H.StdMod (Fin 2) F), hv v⟩
    have hj : Function.Injective j := by
      intro v w hvw
      have h1 := Subtype.ext_iff.mp hvw
      exact Subtype.ext (Multiplicative.toAdd.injective h1)
    exact (Nat.card_le_card_of_injective j hj).trans (hF ▸ B42L2.card_fixed_le _ hM)
  have hEqq : Nat.card (D.img P) = 2 ^ n := by
    refine le_antisymm hEq ?_
    have h1 : 2 ^ n * 2 ^ n ≤ Nat.card (D.img P) * 2 ^ n :=
      (hW ▸ hoffE).trans (Nat.mul_le_mul_left _ hfixE)
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  refine ⟨hBL, hcard ▸ hEqq, ?_⟩
  have h1 : 2 ^ n * 2 ^ n * Nat.card (fixV B) ≤ 2 ^ n * Nat.card V :=
    (hW ▸ hineq).trans (Nat.mul_le_mul_right _ hfixE)
  rw [hcardV]
  rw [mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

end CFSG.Quasithin.B610T

end
