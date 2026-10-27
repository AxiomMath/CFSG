module

public import CFSG.Quasithin.EmptyFaithful.A38cAutOn
public import CFSG.Quasithin.EmptyFaithful.A38cPerm
public import CFSG.Quasithin.EmptyFaithful.S153F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.Ch10.SecA
open scoped Pointwise

section Helpers

variable {G : Type} [Group G]

private theorem mem_normalizer_inf_of_mem_both {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX h, hY h]

theorem inf_pCoreOf_sup_le_pCoreOf [Finite G] {K R : Subgroup G} :
    K ⊓ pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 K := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_right)
  intro g hg
  exact mem_normalizer_inf_of_mem_both (Subgroup.le_normalizer hg)
    (le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hg))

theorem mem_pCoreOf_iff_of_ker_eq {K : Subgroup G} {Q : Type*} [Group Q] {α : ↥K →* Q}
    (hk : α.ker = CFSG.pCore 2 ↥K) {x : G} (hx : x ∈ K) : x ∈ pCoreOf 2 K ↔ α ⟨x, hx⟩ = 1 := by
  rw [← MonoidHom.mem_ker, hk]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem exists_subgroup_card_nine_autOn [Finite G] {K R V Y : Subgroup G} (hYK : Y ≤ K ⊔ R)
    (hN : K ⊔ R ≤ Subgroup.normalizer (V : Set G))
    (hC2 : IsPGroup 2 ↥((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G))) (h9 : 9 ∣ Nat.card ↥Y) :
    ∃ E : Subgroup (MulAut ↥V), E ≤ autOn Y V ∧ Nat.card ↥E = 9 := by
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := hYK.trans hN
  have hker : IsPGroup 2 (A4.actionOn V Y hYV).ker := by
    intro x
    have hx1 : ((x : ↥Y) : G) ∈ Subgroup.centralizer (V : Set G) :=
      (A4.actionOn_eq_one_iff hYV x).mp x.2
    have hxC : ((x : ↥Y) : G) ∈ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hYK (x : ↥Y).2, hx1⟩
    obtain ⟨k, hk⟩ := hC2 ⟨_, hxC⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun y : ↥((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) => (y : G)) hk
    simpa using this
  obtain ⟨E, hE, hcard⟩ := exists_subgroup_card_nine_of_range (A4.actionOn V Y hYV) hker h9
  refine ⟨E, fun a ha => ?_, hcard⟩
  obtain ⟨y, hy⟩ := hE ha
  exact (A4.mem_autOn_iff hYV).mpr ⟨y, hy⟩

theorem conj_mem_autOn_of_le_normalizer {R V Y : Subgroup G}
    (hYR : Y ≤ Subgroup.normalizer (R : Set G)) {x a : MulAut ↥V}
    (hx : x ∈ autOn Y V) (ha : a ∈ autOn R V) : x * a * x⁻¹ ∈ autOn R V := by
  obtain ⟨g₁, hg₁, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨g₂, hg₂, rfl⟩ := Subgroup.mem_map.mp ha
  refine Subgroup.mem_map.mpr ⟨g₁ * g₂ * g₁⁻¹, ?_, by simp [map_mul, map_inv]⟩
  rw [Subgroup.mem_subgroupOf] at hg₁ hg₂ ⊢
  show (g₁ : G) * g₂ * (g₁ : G)⁻¹ ∈ R
  exact (Subgroup.mem_normalizer_iff.mp (hYR hg₁) g₂).mp hg₂

theorem card_map_subgroupOf_mulEquiv {X Q : Type*} [Group X] [Group Q] {A E : Subgroup X}
    (hEA : E ≤ A) (e : ↥A ≃* Q) :
    Nat.card ↥((E.subgroupOf A).map e.toMonoidHom) = Nat.card ↥E := by
  rw [Subgroup.card_map_of_injective e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv

end Helpers

theorem card_sl_three_pow_ne_2520 {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) ≠ 2520 := by
  intro h
  have hu : Odd ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
    (Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega)).mul
      (Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega))
  obtain ⟨h3, huv⟩ := two_pow_mul_odd_inj hu (by decide : Odd 315)
    (h.trans (by norm_num : (2520 : ℕ) = 2 ^ 3 * 315))
  have hn1 : n = 1 := by omega
  subst hn1
  norm_num at huv

theorem one_lt_card_sl_three_pow {n : ℕ} (hn : 1 ≤ n) :
    1 < 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
  have h8 : 2 ≤ 2 ^ (3 * n) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 : 1 ≤ 2 ^ (3 * n) - 1 := by omega
  have h3 : 1 ≤ 2 ^ (2 * n) - 1 := by
    have : 2 ≤ 2 ^ (2 * n) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 1 < 2 ^ (3 * n) := by omega
    _ ≤ 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos h7 h3)

theorem dihedral_four_central_unique :
    ∀ w : DihedralGroup 4, (∀ g : DihedralGroup 4, g * w = w * g) → w ≠ 1 →
      w = DihedralGroup.r 2 := by
  decide

theorem not_isExcA7Block_of_isAltBlockType {G : Type} [Group G] {K : Subgroup G}
    (hA : IsAltBlockType K 7) : ¬ IsExcA7Block K := by
  intro hE
  obtain ⟨-, α, -, -, β, hβs, hβk, -⟩ := hA
  have h1 : Nat.card (↥(blockU K) ⧸ β.ker) = Nat.card (Multiplicative (AltHeart 7)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv
  have h2 : Nat.card (AltHeart 7) = 64 := by
    rw [← Nat.card_congr (Equiv.ofBijective _ (altHeart_mk_bijective (by decide : Odd 7)))]
    have h : Nat.card (evenWeight 7) = Nat.card {x : Fin 7 → ZMod 2 // ∑ i, x i = 0} := by
      apply Nat.card_congr
      exact (Equiv.subtypeEquivRight (fun x => by simp [evenWeight, AddMonoidHom.mem_ker]))
    rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  have h3 := hE.2.2
  rw [← hβk, Subgroup.index, h1, Nat.card_congr (Multiplicative.toAdd : Multiplicative (AltHeart 7) ≃ AltHeart 7),
    h2] at h3
  omega

theorem ordA7ConfigNoNine_holds : OrdA7ConfigNoNine := by
  intro G _ _ H R M K V Y hK7 hR _ hC hYMK hYR h9
  obtain ⟨h1, -, h3⟩ := hC
  have hK7' : IsAltBlockType K 7 := hK7
  obtain ⟨-, α₀, hα₀⟩ := hK7
  have hcardQ : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by
    rw [card_quotPCore_of_isAltBlockTypeWith (by norm_num) hα₀]
    decide
  have hs7 : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    Vol2.Ch10.SecA.isSimpleGroup_alt (by norm_num)
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (quotPCoreMulEquiv α₀ hα₀.1 hα₀.2.1).isSimpleGroup
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_of_card_not_prime (by rw [hcardQ]; norm_num)
  have hO : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G) := h1.1.trans inf_le_right
  have hNV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := h1.2.2.2.1
  have hC2 := isPGroup_centralizer_of_center_eq_bot hR hZ h1.2.1
  have hCle := centralizer_le_pCoreOf_of_center_eq_bot hR hZ h1.2.1
  have hYK : Y ≤ K := hYMK.trans inf_le_right
  have hYKR : Y ≤ K ⊔ R := hYK.trans le_sup_left
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := hYKR.trans hNV
  rcases h3 with ⟨hchi, hi | hii | hiii | hiv⟩ | hb | hc | hd | he | hf | hg | hh
  ·
    exfalso
    obtain ⟨⟨n, hn, hlin⟩, -, -⟩ := hi
    exact not_shapeCard_2520 (Or.inl ⟨n, hn, hcardQ.symm.trans (card_quotPCore_of_isLin2Type hlin)⟩)
  ·
    exfalso
    obtain ⟨hA5, -⟩ := hii
    have h := card_quotPCore_of_isAltType (by norm_num) hA5
    rw [hcardQ] at h
    revert h
    decide
  ·
    exfalso
    obtain ⟨-, ⟨ψ⟩, e, P, hP, hMap⟩ := hiii
    obtain ⟨E, hEY, hE9⟩ := exists_subgroup_card_nine_autOn hYKR hNV hC2 h9
    have hRA : autOn R V ≤ autOn (K ⊔ R) V := A4.autOn_mono le_sup_right
    have hYA : autOn Y V ≤ autOn (K ⊔ R) V := A4.autOn_mono hYKR
    have hEA : E ≤ autOn (K ⊔ R) V := hEY.trans hYA
    set z₁ : ↥(autOn R V) := ψ.symm (DihedralGroup.r 2) with hz₁
    have hψz₁ : ψ z₁ = DihedralGroup.r 2 := ψ.apply_symm_apply _
    have hz₁c : ∀ a : ↥(autOn R V), a * z₁ = z₁ * a := by
      intro a
      apply ψ.injective
      rw [map_mul, map_mul, hψz₁]
      revert a
      have : ∀ g : DihedralGroup 4, g * DihedralGroup.r 2 = DihedralGroup.r 2 * g := by decide
      intro a
      exact this _
    have hz₁ne : z₁ ≠ 1 := by
      intro h
      have := congrArg ψ h
      rw [hψz₁, map_one] at this
      revert this
      decide
    have hz₁sq : z₁ * z₁ = 1 := by
      apply ψ.injective
      rw [map_mul, hψz₁, map_one]
      decide
    let z : Equiv.Perm (Fin 7) := e ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩
    have hz1 : z ≠ 1 := by
      intro h
      apply hz₁ne
      have h' := e.injective (h.trans (map_one e).symm)
      have h'' : (z₁ : MulAut ↥V) = 1 := congrArg Subtype.val h'
      exact Subtype.ext h''
    have hz2 : z * z = 1 := by
      have hsq' : (z₁ : MulAut ↥V) * (z₁ : MulAut ↥V) = 1 := congrArg Subtype.val hz₁sq
      have : (⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ * ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ :
          ↥(autOn (K ⊔ R) V)) = 1 := Subtype.ext hsq'
      show e _ * e _ = 1
      rw [← map_mul, this, map_one]
    have hE₂card := card_map_subgroupOf_mulEquiv hEA e
    refine false_of_card_nine_centralizes hz1 hz2 (hE₂card.trans hE9) ?_
    intro g hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
    have huE : (u : MulAut ↥V) ∈ E := hu
    have hux : (u : MulAut ↥V) ∈ autOn Y V := hEY huE
    have hkey : (u : MulAut ↥V) * (z₁ : MulAut ↥V) = (z₁ : MulAut ↥V) * (u : MulAut ↥V) := by
      have hw : (u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹ ∈ autOn R V :=
        conj_mem_autOn_of_le_normalizer hYR hux z₁.2
      set w : ↥(autOn R V) := ⟨_, hw⟩ with hwdef
      have hwc : ∀ a : ↥(autOn R V), a * w = w * a := by
        intro a
        have ha' : (u : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * ((u : MulAut ↥V)⁻¹)⁻¹ ∈ autOn R V :=
          conj_mem_autOn_of_le_normalizer hYR ((autOn Y V).inv_mem hux) a.2
        have hc := congrArg Subtype.val (hz₁c ⟨_, ha'⟩)
        simp only [Subgroup.coe_mul, inv_inv] at hc
        apply Subtype.ext
        show (a : MulAut ↥V) * ((u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹) =
          ((u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹) * a
        calc (a : MulAut ↥V) * ((u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹)
            = (u : MulAut ↥V) * ((u : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * (u : MulAut ↥V) * z₁) *
                (u : MulAut ↥V)⁻¹ := by group
          _ = (u : MulAut ↥V) * (z₁ * ((u : MulAut ↥V)⁻¹ * (a : MulAut ↥V) * (u : MulAut ↥V))) *
                (u : MulAut ↥V)⁻¹ := by rw [hc]
          _ = ((u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹) * a := by group
      have hψw : ψ w = DihedralGroup.r 2 := by
        refine dihedral_four_central_unique _ (fun g => ?_) (fun h => ?_)
        · obtain ⟨a, rfl⟩ := ψ.surjective g
          rw [← map_mul, ← map_mul, hwc a]
        · apply hz₁ne
          have hw1 : w = 1 := ψ.injective (h.trans (map_one ψ).symm)
          have hw1' : (u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹ = 1 := congrArg Subtype.val hw1
          apply Subtype.ext
          calc (z₁ : MulAut ↥V) = (u : MulAut ↥V)⁻¹ * ((u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹) *
                (u : MulAut ↥V) := by group
            _ = 1 := by rw [hw1']; group
      have hwz : w = z₁ := ψ.injective (hψw.trans hψz₁.symm)
      have hwz' : (u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹ = z₁ := congrArg Subtype.val hwz
      calc (u : MulAut ↥V) * z₁ = ((u : MulAut ↥V) * z₁ * (u : MulAut ↥V)⁻¹) * u := by group
        _ = z₁ * u := by rw [hwz']
    show e u * e ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ = e ⟨(z₁ : MulAut ↥V), hRA z₁.2⟩ * e u
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hkey)
  ·
    exfalso
    obtain ⟨-, -, e, P, hP, hMap⟩ := hiv
    obtain ⟨E, hEY, hE9⟩ := exists_subgroup_card_nine_autOn hYKR hNV hC2 h9
    have hYA : autOn Y V ≤ autOn (K ⊔ R) V := A4.autOn_mono hYKR
    have hYMKA : autOn Y V ≤ autOn (M ⊓ K) V := A4.autOn_mono hYMK
    have hEA : E ≤ autOn (K ⊔ R) V := hEY.trans hYA
    have hE₂card := card_map_subgroupOf_mulEquiv hEA e
    have hle : (E.subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom ≤
        MulAction.stabilizer (Equiv.Perm (Fin 7)) P := by
      have h2 : (E.subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom ≤
          ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono _ (hEY.trans hYMKA))
      rw [hMap] at h2
      exact h2.trans inf_le_left
    have h2B : ∃ B ∈ P, B.card = 2 := by
      have hmem : (2 : ℕ) ∈ P.val.map Finset.card := by
        rw [hP.2.2.2]
        simp
      obtain ⟨B, hB, hB2⟩ := Multiset.mem_map.mp hmem
      exact ⟨B, hB, hB2⟩
    exact false_of_card_nine_le_stabilizer hP.2.1 h2B (hE₂card.trans hE9) hle
  ·
    exfalso
    obtain ⟨⟨n, α, h5, h8, -, hα, t, htR, htV, hRact, -, σ, hσ, hconj⟩, hMKV⟩ := hb
    have hcn := card_quotPCore_of_isAltBlockTypeWith (by omega) hα
    rw [hcardQ] at hcn
    have hn7 : n = 7 := by
      interval_cases n <;> first | rfl | (exfalso; revert hcn; decide)
    subst hn7
    obtain ⟨p, q, hpq, rfl⟩ := hσ
    have hkey : ∀ (s : G) (hs : s ∈ Y),
        ((α ⟨s, hYK hs⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * Equiv.swap p q =
          Equiv.swap p q * ((α ⟨s, hYK hs⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
      intro s hs
      have hsK : s ∈ K := hYK hs
      have hsN : s ∈ Subgroup.normalizer (V : Set G) := hYV hs
      have hmem : conjAct V ⟨s, hsN⟩ ∈ autOn (M ⊓ K) V :=
        Subgroup.mem_map.mpr ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr (hYMK hs), rfl⟩
      rw [hMKV] at hmem
      have hcent := (Subgroup.mem_centralizer_iff.mp hmem.2) (conjAct V ⟨t, htV⟩)
        (by rw [hRact]; exact Subgroup.mem_zpowers _)
      have hc1 : conjAct V (⟨s, hsN⟩ * ⟨t, htV⟩ * ⟨s, hsN⟩⁻¹ * ⟨t, htV⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcent]
        group
      have hcV : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        A4.conjAct_eq_one_iff.mp hc1
      have hcKR : s * t * s⁻¹ * t⁻¹ ∈ K ⊔ R :=
        (K ⊔ R).mul_mem ((K ⊔ R).mul_mem ((K ⊔ R).mul_mem (Subgroup.mem_sup_left hsK)
          (Subgroup.mem_sup_right htR)) ((K ⊔ R).inv_mem (Subgroup.mem_sup_left hsK)))
          ((K ⊔ R).inv_mem (Subgroup.mem_sup_right htR))
      have hcP : s * t * s⁻¹ * t⁻¹ ∈ pCoreOf 2 (K ⊔ R) := hCle ⟨hcKR, hcV⟩
      have hts : t * s⁻¹ * t⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hR htR) s⁻¹).mp (K.inv_mem hsK)
      have hcK : s * t * s⁻¹ * t⁻¹ ∈ K := by
        have : s * t * s⁻¹ * t⁻¹ = s * (t * s⁻¹ * t⁻¹) := by group
        rw [this]
        exact K.mul_mem hsK hts
      have hcO : s * t * s⁻¹ * t⁻¹ ∈ pCoreOf 2 K := inf_pCoreOf_sup_le_pCoreOf ⟨hcK, hcP⟩
      have hα1 : α ⟨s * t * s⁻¹ * t⁻¹, hcK⟩ = 1 :=
        (mem_pCoreOf_iff_of_ker_eq hα.2.1 hcK).mp hcO
      have hsplit : (⟨s * t * s⁻¹ * t⁻¹, hcK⟩ : ↥K) =
          ⟨s, hsK⟩ * ⟨t * s⁻¹ * t⁻¹, hts⟩ := Subtype.ext (by simp [mul_assoc])
      have h2 := hconj s⁻¹ (K.inv_mem hsK) hts
      have hinv : (⟨s⁻¹, K.inv_mem hsK⟩ : ↥K) = ⟨s, hsK⟩⁻¹ := rfl
      rw [hinv, map_inv] at h2
      rw [hsplit, map_mul] at hα1
      have h3 := congrArg (fun a : alternatingGroup (Fin 7) => (a : Equiv.Perm (Fin 7))) hα1
      simp only [Subgroup.coe_mul, Subgroup.coe_one, Subgroup.coe_inv] at h3 h2
      rw [h2] at h3
      have h4 : ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          Equiv.swap p q * ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))⁻¹ *
          (Equiv.swap p q)⁻¹ = 1 := by
        simpa [mul_assoc] using h3
      have h6 : ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * Equiv.swap p q =
          Equiv.swap p q * ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
        calc ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * Equiv.swap p q
            = (((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * Equiv.swap p q *
                ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))⁻¹ *
                (Equiv.swap p q)⁻¹) *
              (Equiv.swap p q * ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) := by
              group
          _ = Equiv.swap p q * ((α ⟨s, hsK⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
              rw [h4, one_mul]
      exact h6
    let f : ↥Y →* alternatingGroup (Fin 7) := α.comp (Subgroup.inclusion hYK)
    have hkerf : IsPGroup 2 f.ker := by
      intro x
      have hx0 : f x = 1 := x.2
      have hxK : ((x : ↥Y) : G) ∈ pCoreOf 2 K :=
        (mem_pCoreOf_iff_of_ker_eq hα.2.1 (hYK (x : ↥Y).2)).mpr hx0
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨_, hxK⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun y : ↥(pCoreOf 2 K) => (y : G)) hk
      simpa using this
    obtain ⟨E, hEf, hE9⟩ := exists_subgroup_card_nine_of_range f hkerf h9
    have hE'9 : Nat.card ↥(E.map (alternatingGroup (Fin 7)).subtype) = 9 := by
      rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective]
      exact hE9
    have hsw1 : Equiv.swap p q ≠ 1 := fun h => hpq (by
      have := congrArg (fun π : Equiv.Perm (Fin 7) => π p) h
      simpa using this.symm)
    refine false_of_card_nine_centralizes hsw1 (Equiv.swap_mul_self p q) hE'9 ?_
    intro g hg
    obtain ⟨a, haE, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨y, hy⟩ := hEf haE
    have hya : ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        ((α ⟨(y : G), hYK y.2⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
      rw [← hy]
      rfl
    show ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * Equiv.swap p q =
      Equiv.swap p q * ((a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
    rw [hya]
    exact hkey (y : G) y.2
  ·
    exfalso
    have h := card_quotPCore_of_isHatA6Block hc.1
    omega
  ·
    exact (not_isExcA7Block_of_isAltBlockType hK7' hd.1).elim
  ·
    exfalso
    rcases he.1 with hA6 | hSp
    · obtain ⟨-, α, hα⟩ := hA6
      have h := card_quotPCore_of_isAltBlockTypeWith (by norm_num) hα
      rw [hcardQ] at h
      revert h
      decide
    · have h := card_quotPCore_of_isSp4Block hSp
      omega
  ·
    exfalso
    have h := card_quotPCore_of_isG2Block hf.1
    omega
  ·
    exfalso
    obtain ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ := hg
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    have hA : Nat.card ↥(autOn K V) = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hF']
    have heq := card_autOn_eq_card_quot hR hO hNV (hA ▸ one_lt_card_sl_three_pow hn1)
    rw [hA, hcardQ] at heq
    exact card_sl_three_pow_ne_2520 hn1 heq
  ·
    exfalso
    obtain ⟨hSL, -, -⟩ := hh
    rcases hSL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hA : Nat.card ↥(autOn K V) = 20160 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA, hcardQ] at heq
      omega
    · have hA : Nat.card ↥(autOn K V) = 9999360 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA, hcardQ] at heq
      omega

end CFSG.Quasithin
