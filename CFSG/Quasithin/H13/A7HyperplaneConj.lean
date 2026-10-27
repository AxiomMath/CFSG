module

public import CFSG.Quasithin.H13.A7Hyperplane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Module Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem conj_smul_conj_smul_inv (V : Subgroup G) (g : G) :
    MulAut.conj g⁻¹⁻¹ • (MulAut.conj g⁻¹ • V) = V := by
  ext x
  rw [mem_conj_smul_iff, mem_conj_smul_iff,
    show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group]

theorem A7_no_noncentral_normalizing_hyperplane_conj {V M : Subgroup G}
    (hNM : normalizer (V : Set G) ≤ M) (φ : V ≃* Multiplicative (evenWeight 7))
    (hact : ∀ n ∈ normalizer (V : Set G), ∃ σ : Perm (Fin 7), ∀ v w : V,
      (w : G) = n * v * n⁻¹ →
        ((Multiplicative.toAdd (φ w) : evenWeight 7) : Fin 7 → ZMod 2) =
          permAct7 σ ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2))
    (hTI : ∀ m ∈ M, MulAut.conj m⁻¹ • V = V ∨ V ⊓ (MulAut.conj m⁻¹ • V) = ⊥)
    (hwt2 : ∀ v : V,
      hammingNorm ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2) = 2 →
        centralizer ({(v : G)} : Set G) ≤ M)
    (hwt4 : ∀ g : G, MulAut.conj g⁻¹ • V ≠ V → ∀ v : V,
      (v : G) ∈ MulAut.conj g⁻¹ • V → v ≠ 1 →
        hammingNorm ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2) = 4)
    (g : G) :
    (∀ h : G, ((MulAut.conj h⁻¹ • (MulAut.conj g⁻¹ • V)) ⊓
        normalizer ((MulAut.conj g⁻¹ • V : Subgroup G) : Set G)).relIndex
          (MulAut.conj h⁻¹ • (MulAut.conj g⁻¹ • V)) ≤ 2 →
      ⁅MulAut.conj g⁻¹ • V, (MulAut.conj h⁻¹ • (MulAut.conj g⁻¹ • V)) ⊓
        normalizer ((MulAut.conj g⁻¹ • V : Subgroup G) : Set G)⁆ = ⊥) ∧
      ∀ H : Subgroup G, H ≤ MulAut.conj g⁻¹ • V → 16 ≤ Nat.card H →
        centralizer (H : Set G) ≤ normalizer ((MulAut.conj g⁻¹ • V : Subgroup G) : Set G) := by
  classical
  set A := MulAut.conj g⁻¹ • V with hAdef
  set φA : A ≃* Multiplicative (evenWeight 7) := (conjIso V g).trans φ with hφAdef
  have hvecA : ∀ x : A, vec φA x = vec φ (conjIso V g x) := fun _ => rfl
  have hmemAh : ∀ h x : G, x ∈ MulAut.conj h⁻¹ • A ↔ g * h * x * h⁻¹ * g⁻¹ ∈ V := by
    intro h x
    rw [mem_conj_smul_iff, mem_conj_smul_iff]
    simp only [mul_assoc]
  have hAel : CFSG.IsElementaryAbelian 2 A :=
    { is_comm := ⟨fun x y => mul_comm_of_vec φA x y⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        rw [pow_two]
        exact sq_eq_one_of_vec φA x }
  refine A7_no_noncentral_normalizing_hyperplane (V := A) (M := MulAut.conj g⁻¹ • M)
    hAel (nat_card_of_vec φA) ?_ φA ?_ ?_ ?_ ?_
  ·
    intro x hx
    rw [mem_conj_smul_iff]
    exact hNM (mem_normalizer_conj_smul_iff.1 hx)
  ·
    intro n hn
    obtain ⟨σ, hσ⟩ := hact (g * n * g⁻¹) (mem_normalizer_conj_smul_iff.1 hn)
    refine ⟨σ, fun x y hxy => ?_⟩
    change vec φ (conjIso V g y) = permAct7 σ (vec φ (conjIso V g x))
    apply hσ
    rw [coe_conjIso, coe_conjIso, hxy]
    group
  ·
    intro m hm
    rw [mem_conj_smul_iff] at hm
    rcases hTI _ hm with h | h
    · left
      ext x
      rw [hmemAh, hAdef, mem_conj_smul_iff]
      have hiff := (conj_smul_eq_self_iff.1 h)
      rw [mem_normalizer_iff] at hiff
      rw [hiff (g * x * g⁻¹)]
      constructor <;> intro hx <;> convert hx using 1 <;> group
    · right
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxA, hxAm⟩ := Subgroup.mem_inf.1 hx
      rw [hmemAh] at hxAm
      have h1 : g * x * g⁻¹ ∈ V ⊓ (MulAut.conj (g * m * g⁻¹)⁻¹ • V) := by
        refine Subgroup.mem_inf.2 ⟨mem_conj_smul_iff.1 hxA, ?_⟩
        rw [mem_conj_smul_iff]
        convert hxAm using 1
        group
      rw [h, mem_bot] at h1
      rw [mem_bot]
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
  ·
    intro a ha y hy
    rw [mem_conj_smul_iff]
    apply hwt2 (conjIso V g a) ha
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [coe_conjIso]
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  ·
    intro h hne a haAh ha1
    change hammingNorm (vec φ (conjIso V g a)) = 4
    have hne' : MulAut.conj (g * h * g⁻¹)⁻¹ • V ≠ V := by
      intro heq
      apply hne
      ext x
      rw [hmemAh, hAdef, mem_conj_smul_iff]
      have hiff := (conj_smul_eq_self_iff.1 heq)
      rw [mem_normalizer_iff] at hiff
      rw [hiff (g * x * g⁻¹)]
      constructor <;> intro hx <;> convert hx using 1 <;> group
    refine hwt4 _ hne' _ ?_ ?_
    · rw [mem_conj_smul_iff, coe_conjIso]
      convert (hmemAh h a).1 haAh using 1
      group
    · intro h1
      apply ha1
      exact (conjIso V g).injective (h1.trans (map_one _).symm)

theorem A7_hyperplane_in_Sylow_centralizes_entire_conjugate [Finite G] {V T M : Subgroup G}
    (hV : CFSG.IsElementaryAbelian 2 V) (hV64 : Nat.card V = 64) (_hT : IsPGroup 2 T)
    (_hVT : V ≤ T) (hTN : T ≤ normalizer (V : Set G)) (hNM : normalizer (V : Set G) ≤ M)
    (φ : V ≃* Multiplicative (evenWeight 7))
    (hact : ∀ n ∈ normalizer (V : Set G), ∃ σ : Perm (Fin 7), ∀ v w : V,
      (w : G) = n * v * n⁻¹ →
        ((Multiplicative.toAdd (φ w) : evenWeight 7) : Fin 7 → ZMod 2) =
          permAct7 σ ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2))
    (hTI : ∀ m ∈ M, MulAut.conj m⁻¹ • V = V ∨ V ⊓ (MulAut.conj m⁻¹ • V) = ⊥)
    (hwt2 : ∀ v : V,
      hammingNorm ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2) = 2 →
        centralizer ({(v : G)} : Set G) ≤ M)
    (hwt4 : ∀ g : G, MulAut.conj g⁻¹ • V ≠ V → ∀ v : V,
      (v : G) ∈ MulAut.conj g⁻¹ • V → v ≠ 1 →
        hammingNorm ((Multiplicative.toAdd (φ v) : evenWeight 7) : Fin 7 → ZMod 2) = 4) :
    (∀ g : G, ∀ B : Subgroup G, B ≤ (MulAut.conj g⁻¹ • V) ⊓ T →
      B.relIndex (MulAut.conj g⁻¹ • V) ≤ 2 → ⁅V, MulAut.conj g⁻¹ • V⁆ = ⊥) ∧
      (⨆ (g : G) (_ : MulAut.conj g⁻¹ • V ≤ T), MulAut.conj g⁻¹ • V) ≤
        T ⊓ centralizer (V : Set G) := by
  classical
  have hmain := A7_no_noncentral_normalizing_hyperplane hV hV64 hNM φ hact hTI hwt2 hwt4
  have hcent : ∀ g : G, ∀ B : Subgroup G, B ≤ (MulAut.conj g⁻¹ • V) ⊓ T →
      B.relIndex (MulAut.conj g⁻¹ • V) ≤ 2 → ⁅V, MulAut.conj g⁻¹ • V⁆ = ⊥ := by
    intro g B hB hBidx
    set A := MulAut.conj g⁻¹ • V with hAdef
    have hBA : B ≤ A := hB.trans inf_le_left
    have hBN : B ≤ A ⊓ normalizer (V : Set G) := le_inf hBA ((hB.trans inf_le_right).trans hTN)
    have hA64 : Nat.card A = 64 := nat_card_of_vec ((conjIso V g).trans φ)
    have hidx : (A ⊓ normalizer (V : Set G)).relIndex A ≤ 2 := by
      have h1 := Subgroup.relIndex_dvd_of_le_left A hBN
      have h2 : B.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1).trans hBidx
    have hVB : ⁅V, A ⊓ normalizer (V : Set G)⁆ = ⊥ := hmain.1 g hidx
    have hVcB : V ≤ centralizer (B : Set G) := by
      rw [← commutator_eq_bot_iff_le_centralizer]
      exact le_bot_iff.1 (hVB ▸ commutator_mono le_rfl hBN)
    have hB16 : 16 ≤ Nat.card B := by
      have h := Subgroup.card_mul_index (B.subgroupOf A)
      have h2 : Nat.card (B.subgroupOf A) = Nat.card B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
      rw [h2, hA64] at h
      have h3 : (B.subgroupOf A).index ≤ 2 := hBidx
      have h4 : Nat.card B * (B.subgroupOf A).index ≤ Nat.card B * 2 :=
        Nat.mul_le_mul_left _ h3
      omega
    have hconj := A7_no_noncentral_normalizing_hyperplane_conj hNM φ hact hTI hwt2 hwt4 g
    have hVNA : V ≤ normalizer (A : Set G) := hVcB.trans (hconj.2 B hBA hB16)
    have h1 := hconj.1 g⁻¹
    rw [conj_smul_conj_smul_inv, inf_eq_left.2 hVNA, Subgroup.relIndex_self] at h1
    rw [commutator_comm]
    exact h1 (by norm_num)
  refine ⟨hcent, iSup₂_le fun g hg => le_inf hg ?_⟩
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
  refine hcent g (MulAut.conj g⁻¹ • V) (le_inf le_rfl hg) ?_
  rw [Subgroup.relIndex_self]
  norm_num

end CFSG.Quasithin.H13.A7
