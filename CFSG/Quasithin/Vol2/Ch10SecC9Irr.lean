module

public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Vol2.Ch10SecCFacts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

theorem d5_span : ∀ m m' : Fin 5 → ZMod 2, ∑ i, m i = 0 → ∑ i, m' i = 0 → m ≠ 0 →
    ∃ c : Fin 4 → ZMod 2, m' = ∑ k : Fin 4, c k • (fun i => m (((finRotate 5) ^ (k : ℕ))⁻¹ i)) := by
  decide +kernel

theorem d5_span' (m m' : G6.PermMod 5) (hm : m ∈ G6.coreMod 5) (hm' : m' ∈ G6.coreMod 5)
    (h1 : m ≠ 1) : ∃ c : Fin 4 → ℕ,
      m' = ∏ k : Fin 4, (G6.permAct 5 ((finRotate 5) ^ (k : ℕ)) m) ^ c k := by
  rw [G6.mem_coreMod] at hm hm'
  have h0 : Multiplicative.toAdd m ≠ 0 := fun h => h1 (by
    apply Multiplicative.toAdd.injective; rw [h]; rfl)
  obtain ⟨c, hc⟩ := d5_span _ _ hm hm' h0
  refine ⟨fun k => (c k).val, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  funext i
  have := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [toAdd_pow, Finset.sum_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
    ZMod.natCast_zmod_val, G6.permAct_apply]
  exact this

theorem allOnes_sq : G6.allOnes 5 ^ 2 = 1 := by decide

theorem allOnes_not_mem : G6.allOnes 5 ∉ G6.coreMod 5 := by
  rw [G6.mem_coreMod]; decide

theorem allOnes_ne : G6.allOnes 5 ≠ 1 := by decide

theorem allOnes_zpow {x : G6.PermMod 5} (hx : x ∈ Subgroup.zpowers (G6.allOnes 5)) :
    x = 1 ∨ x = G6.allOnes 5 := by
  classical
  have ho : orderOf (G6.allOnes 5) = 2 := orderOf_eq_prime allOnes_sq allOnes_ne
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hi
  interval_cases i
  · left; exact pow_zero _
  · right; exact pow_one _

theorem altDn5_ker_eq : (FFModel.altDn 5).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  rcases allOnes_zpow hx1 with h | h
  · exact h
  · exact absurd (h ▸ hx2) allOnes_not_mem

theorem rot_even : finRotate 5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

abbrev e01 : G6.PermMod 5 := Multiplicative.ofAdd ![1, 1, 0, 0, 0]

theorem e01_mem : e01 ∈ G6.coreMod 5 := G6.mem_coreMod.mpr (by decide)

theorem e01_ne : e01 ≠ 1 := by decide

theorem isIrrSec_of_altNat5 {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : AlternatingNatural H ⊤ ⊥ 5) : XMod.IsIrrSec ↥H (⊥ : Subgroup V) ⊤ := by
  obtain ⟨π, hπ, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hker : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    rw [altDn5_ker_eq, Subgroup.bot_subgroupOf]
  have hmk : ∀ m : ↥(FFModel.altDn 5).sec,
      (QuotientGroup.mk m : ↥(FFModel.altDn 5).sec ⧸
        (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = 1 → m = 1 := by
    intro m hm
    rw [QuotientGroup.eq_one_iff, hker] at hm
    exact hm
  have hβinj : ∀ u : ↥(⊤ : Subgroup V), β u = 1 → u = 1 :=
    fun u hu => Subtype.ext ((hβk u).1 hu)
  let σ : ↥(alternatingGroup (Fin 5)) := ⟨finRotate 5, rot_even⟩
  refine ⟨bot_lt_iff_ne_bot.mpr fun htop => ?_, fun J hJ _ _ => ?_⟩
  · let m0 : ↥(FFModel.altDn 5).sec := ⟨(e01 : G6.PermMod 5), e01_mem⟩
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m0)
    have hu1 : u = 1 := Subtype.ext (by
      have : (u : V) ∈ (⊥ : Subgroup V) := by rw [← htop]; exact Subgroup.mem_top _
      exact this)
    have := hmk m0 (by rw [← hu, hu1, map_one])
    exact e01_ne (congrArg Subtype.val this)
  · by_cases hJb : J = ⊥
    · exact Or.inl hJb
    right
    obtain ⟨⟨x, hxJ⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJb
    have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨x, trivial⟩)
    have hm1 : (show G6.PermMod 5 from m.1) ≠ 1 := fun h => hx1 (by
      have h' : m = 1 := Subtype.ext h
      have := hβinj ⟨x, trivial⟩ (by rw [← hm, h', QuotientGroup.mk_one])
      exact congrArg Subtype.val this)
    rw [eq_top_iff]
    intro y _
    obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (β ⟨y, trivial⟩)
    obtain ⟨c, hc⟩ := d5_span' (show G6.PermMod 5 from m.1) (show G6.PermMod 5 from m'.1) m.2
      m'.2 hm1
    have hfac : ∀ k : Fin 4, β ⟨((π (σ ^ (k : ℕ)) : ↥H) : MulAut V) x, trivial⟩ =
        QuotientGroup.mk ⟨(FFModel.altDn 5).act (σ ^ (k : ℕ)) m, hsec _ _ m.2⟩ :=
      fun k => hβe _ _ _ trivial (hsec _ _ m.2) hm.symm
    have hinj : Function.Injective β := (injective_iff_map_eq_one β).mpr hβinj
    have hy : (⟨y, trivial⟩ : ↥(⊤ : Subgroup V)) = ∏ k : Fin 4,
        (⟨((π (σ ^ (k : ℕ)) : ↥H) : MulAut V) x, trivial⟩ : ↥(⊤ : Subgroup V)) ^ c k := by
      apply hinj
      rw [map_prod]
      simp_rw [map_pow, hfac]
      rw [← hm']
      set N := (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec
      have hmk' : ∀ a : ↥(FFModel.altDn 5).sec, (a : ↥(FFModel.altDn 5).sec ⧸ N) =
          QuotientGroup.mk' N a := fun _ => rfl
      simp only [hmk', ← map_pow, ← map_prod]
      congr 1
      apply Subtype.ext
      rw [SubmonoidClass.coe_finsetProd]
      simp only [SubmonoidClass.coe_pow]
      exact hc
    have hy' := congrArg Subtype.val hy
    rw [SubmonoidClass.coe_finsetProd] at hy'
    simp only [SubmonoidClass.coe_pow] at hy'
    show y ∈ J
    rw [hy']
    exact Subgroup.prod_mem J fun k _ => J.pow_mem (hJ (π (σ ^ (k : ℕ))) x hxJ) _

section Transport

variable {G : Type} [Group G]

@[expose] def IrrG (L W : Subgroup G) : Prop :=
  W ≠ ⊥ ∧ ∀ X : Subgroup G, X ≤ W → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = W

theorem coe_conjAct_apply (V : Subgroup G) (g : Subgroup.normalizer (V : Set G))
    (x : V) : ((conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

open scoped IsMulCommutative in
theorem irrG_of_isIrrSec {L W : Subgroup G} [IsMulCommutative ↥W]
    (h : XMod.IsIrrSec ↥(autOn L W) (⊥ : Subgroup ↥W) ⊤) : IrrG L W := by
  refine ⟨fun hW => ?_, fun X hXW hXL => ?_⟩
  · obtain ⟨w, -, hw⟩ := IsConcreteLE.exists_of_lt h.1
    apply hw
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp ((le_of_eq hW) w.2))
  · have hinv : XMod.IsInv ↥(autOn L W) (X.subgroupOf W) := by
      rintro ⟨a, ha⟩ ⟨v, hv⟩ hvX
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp ha
      rw [Subgroup.mem_subgroupOf] at hvX ⊢
      show ((conjAct W n ⟨v, hv⟩ : ↥W) : G) ∈ X
      rw [coe_conjAct_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hXL (Subgroup.mem_subgroupOf.mp hn)) v).mp hvX
    rcases h.2 _ hinv bot_le le_top with h' | h'
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hXW hx⟩ : ↥W) ∈ X.subgroupOf W := hx
      rw [h', Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    · right
      refine le_antisymm hXW fun w hw => ?_
      have : (⟨w, hw⟩ : ↥W) ∈ X.subgroupOf W := h' ▸ Subgroup.mem_top _
      exact this


open scoped IsMulCommutative in
theorem irrG_or_case5 [Finite G] {L V₁ : Subgroup G} (h : ModCase L V₁)
    (hC : (Subgroup.centralizer (L : Set G)).subgroupOf V₁ = ⊥) (hK8a : FactK8a)
    (hK8b : FactK8b) :
    IrrG L V₁ ∨ ∃ s ∈ Subgroup.normalizer (L : Set G), ∃ W : Subgroup G, W ≤ V₁ ∧
      L ≤ Subgroup.normalizer (W : Set G) ∧ W ⊔ CFSG.conjugate W s = V₁ ∧
      W ⊓ CFSG.conjugate W s = ⊥ ∧ IrrG L W ∧ ¬ IsXSectionIso L ⊥ W (CFSG.conjugate W s) := by
  obtain ⟨hc, hcases⟩ := h
  rcases hcases with ⟨n, -, -, hnat⟩ | ⟨-, halt⟩ | ⟨-, hnat⟩ | ⟨n, hn, -, horth⟩ |
    ⟨-, s, hs, W, hWV, hLW, hsup, hinf, ⟨hWc, hWnat⟩, hni⟩ | ⟨n, -, hsz⟩
  · rw [hC] at hnat
    obtain ⟨K, _, _, -, π, hD⟩ := hnat
    exact Or.inl (irrG_of_isIrrSec (B5.isIrr_of_realizes (by norm_num) hD).2)
  · exact Or.inl (irrG_of_isIrrSec (isIrrSec_of_altNat5 halt))
  · rw [hC] at hnat
    obtain ⟨K, _, _, -, π, hD⟩ := hnat
    exact Or.inl (irrG_of_isIrrSec (B5.isIrr_of_realizes (by norm_num) hD).2)
  · exact Or.inl (irrG_of_isIrrSec (hK8a _ _ _ _ n (by omega) horth))
  · obtain ⟨K, _, _, -, π, hD⟩ := hWnat
    exact Or.inr ⟨s, hs, W, hWV, hLW, hsup, hinf,
      irrG_of_isIrrSec (B5.isIrr_of_realizes (by norm_num) hD).2, hni⟩
  · exact Or.inl (irrG_of_isIrrSec (hK8b _ _ _ _ n hsz))

end Transport

end CFSG.Quasithin.Vol2.Ch10.SecC
