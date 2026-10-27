module

public import CFSG.Quasithin.Vol2.Ch11SecOE7B
public import CFSG.Quasithin.Vol2.Ch11SecOE7F
public import CFSG.Quasithin.Vol2.Ch11SecOE7G
public import CFSG.Quasithin.Vol2.Ch11SecU1Crit

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
  (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

omit [Finite G] in
include hJ hf hcard hfixed in
theorem card_le_of_le_psu3 {L A : Subgroup G} (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hAL : A ≤ L) (hA : IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ f := by
  set ψ := psuEmb J e with hψdef
  have hψi := psuEmb_injective J e
  have hAA : (A.comap ψ).map ψ = A :=
    Subgroup.map_comap_eq_self (by rw [psuEmb_range J e]; exact hAL)
  have hE : IsElemAbelian 2 (A.comap ψ) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hψi ?_)⟩⟩, fun x hx => hψi ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact commute_of_isElemAbelian hA (Subgroup.mem_comap.mp x.2) (Subgroup.mem_comap.mp y.2)
    · rw [map_pow, hA.2 _ (Subgroup.mem_comap.mp hx), map_one]
  calc Nat.card A = Nat.card (A.comap ψ) := by
        rw [← hAA, Subgroup.card_map_of_injective hψi, hAA]
    _ ≤ 2 ^ f := card_le_of_isElemAbelian J hJ hf hcard hfixed hE

include hJ hf hcard hfixed in
theorem exists_member_of_psu3 {L T : Subgroup G} (h : AlmostSimple L)
    (hT : quasithinIsSylowTwo T) (hLT : L ⊔ T = ⊤)
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 f)
    (e : ↥L ≃* ProjectiveSpecialUnitaryMatrixGroup J) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcA : 2 ^ f < Nat.card A) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, IsE f ⊤ T (A1b.conjSub g A) K ∧
      Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ⊔ K = ⊤ := by
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a, haA, haL⟩ : ∃ a ∈ A, a ∉ L := by
    by_contra hc
    push Not at hc
    exact absurd (card_le_of_le_psu3 J hJ hf hcard hfixed e hc hA) (not_le.mpr hcA)
  obtain ⟨g, hgT, hsyl⟩ := SecU1.exists_conj_le_sylow hT' hA haA
  set A' := A1b.conjSub g A with hA'def
  set a' := g * a * g⁻¹ with ha'def
  have ha'A : a' ∈ A' := by
    rw [hA'def, A1b.mem_conjSub_iff, ha'def, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
    exact haA
  have ha'L : a' ∉ L := fun h' => haL (by
    have := hLn.conj_mem _ h' g⁻¹
    rwa [ha'def, show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this)
  have hA' : IsElemAbelian 2 A' := SecU1.isElemAbelian_conjSub hA g
  have hcA' : 2 ^ f < Nat.card A' := by rwa [hA'def, card_conjSub_eq]
  set α : MulAut ↥L := MulAut.conjNormal a' with hαdef
  have hcent : ∀ x : G, (∀ y : ↥L, MulAut.conjNormal x y = y) → x = 1 := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg Subtype.val (hx ⟨y, hy⟩)
      rw [MulAut.conjNormal_apply] at h1
      calc y * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    rw [h.centralizer_eq] at hxC
    exact hxC
  have hα1 : α ≠ 1 := fun h1 => ha'L (by
    rw [hcent a' fun y => by rw [← hαdef, h1, MulAut.one_apply]]
    exact L.one_mem)
  have hα2 : α ^ 2 = 1 := by
    rw [hαdef, ← map_pow, hA'.2 a' ha'A, map_one]
  have hα : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  have hαout : α ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rintro ⟨y, hy⟩
    apply ha'L
    have h1 : (y : G)⁻¹ * a' = 1 := hcent _ fun z => by
      apply Subtype.ext
      have h2 := congrArg (fun β : MulAut ↥L => ((β z : ↥L) : G)) hy
      simp only [MulAut.conj_apply, hαdef, MulAut.conjNormal_apply] at h2
      rw [MulAut.conjNormal_apply]
      rw [show (↑y)⁻¹ * a' * ↑z * ((↑y)⁻¹ * a')⁻¹ = (↑y)⁻¹ * (a' * ↑z * a'⁻¹) * ↑y by group,
        ← h2]
      push_cast
      group
    have h3 : (y : G) = a' := inv_mul_eq_one.mp h1
    rw [← h3]
    exact y.2
  obtain ⟨k, _, _, _, j, hk, hjinj, hfixj, hP2⟩ := fixed_iff_mem_range_of_outer hf hD α hα hαout
  set L₀ : Subgroup G := j.range.map L.subtype with hL₀def
  have hL₀L : L₀ ≤ L := Subgroup.map_subtype_le _
  have hmemL₀ : ∀ y : G, y ∈ L₀ ↔ y ∈ L ∧ a' * y = y * a' := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have h1 := congrArg Subtype.val ((hfixj z).mpr hz)
      rw [hαdef, MulAut.conjNormal_apply] at h1
      calc a' * z = a' * z * a'⁻¹ * a' := by group
        _ = z * a' := by rw [h1]
    · rintro ⟨hyL, hy⟩
      refine ⟨⟨y, hyL⟩, (hfixj _).mp (Subtype.ext ?_), rfl⟩
      rw [hαdef, MulAut.conjNormal_apply]
      calc a' * y * a'⁻¹ = y * a' * a'⁻¹ := by rw [hy]
        _ = y := by group
  let eL₀ : ↥L₀ ≃* SL(2, k) :=
    (Subgroup.equivMapOfInjective j.range L.subtype L.subtype_injective).symm.trans
      (MonoidHom.ofInjective hjinj).symm
  have hk4 : 4 ≤ Nat.card k := hk ▸ h4
  have hL₀s : ¬ Group.IsSolvable ↥L₀ := fun hs => E1.RootLift.not_isSolvable_SL2 hk4
    (Group.isSolvable_of_isSolvable_injective (f := eL₀.symm.toMonoidHom) eL₀.symm.injective)
  have hstep : ∀ t : G, t * a' = a' * t → ∀ y : G, y ∈ L₀ → t * y * t⁻¹ ∈ L₀ := by
    intro t ht y hy
    obtain ⟨hyL, hy⟩ := (hmemL₀ y).mp hy
    refine (hmemL₀ _).mpr ⟨hLn.conj_mem y hyL t, ?_⟩
    have ht' : t⁻¹ * a' = a' * t⁻¹ := by
      calc t⁻¹ * a' = t⁻¹ * (a' * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * a') * t⁻¹ := by rw [ht]
        _ = a' * t⁻¹ := by group
    calc a' * (t * y * t⁻¹) = (a' * t) * y * t⁻¹ := by group
      _ = (t * a') * y * t⁻¹ := by rw [← ht]
      _ = t * (a' * y) * t⁻¹ := by group
      _ = t * (y * a') * t⁻¹ := by rw [hy]
      _ = t * y * (a' * t⁻¹) := by group
      _ = t * y * (t⁻¹ * a') := by rw [ht']
      _ = t * y * t⁻¹ * a' := by group
  have hCN : Subgroup.centralizer {a'} ≤ Subgroup.normalizer (L₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff] at ht
    have hti : t⁻¹ * a' = a' * t⁻¹ := by
      calc t⁻¹ * a' = t⁻¹ * (a' * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * a') * t⁻¹ := by rw [ht]
        _ = a' * t⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hstep t ht y, fun hy => ?_⟩
    have := hstep t⁻¹ hti _ hy
    rwa [show t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y by group] at this
  have hτN : tauOf ⊤ T A' ≤ Subgroup.normalizer (L₀ : Set G) :=
    (tauOf_le_centralizer h ha'A).trans hCN
  have hL₀C : L₀ ≤ Subgroup.centralizer {a'} := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hmemL₀ y).mp hy).2.symm
  have hL₀syl : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    have h1 := B6.isSylowTwoOf_inf_normal (⟨hsyl.1, hsyl.2.1, hsyl.2.2⟩ :
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer {a'}) (Subgroup.centralizer {a'}))
      hL₀C hCN
    rw [inf_assoc, inf_eq_right.mpr hL₀C] at h1
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  have hA'C : ¬ A' ≤ Subgroup.centralizer (L₀ : Set G) := by
    intro hle
    set φ : G →* MulAut ↥L := MulAut.conjNormal with hφ
    have hφi : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      exact hcent x fun y => by rw [MonoidHom.mem_ker.mp hx, MulAut.one_apply]
    have hP := hP2 (A'.map φ) ((isPGroup_of_isElemAbelian hA').map φ) (by
      rintro _ ⟨b, hb, rfl⟩ x hx
      apply Subtype.ext
      rw [hφ, MulAut.conjNormal_apply]
      have hxL₀ : (x : G) ∈ L₀ := ⟨x, hx, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp (hle hb) _ hxL₀
      calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [← h1]
        _ = x := by group)
    rw [Subgroup.card_map_of_injective hφi] at hP
    omega
  refine ⟨g, hgT, L₀ ⊔ tauOf ⊤ T A',
    isE_sup_tauOf_of_sl2 hT' hgT hA' eL₀ hk hk4 hτN hL₀syl hA'C, ?_⟩
  have hLD := le_sup_normalizer_of_not_isSolvable J hJ hf hcard hfixed hT e hL₀L hL₀s
  refine eq_top_iff.mpr ?_
  rw [← hLT]
  refine sup_le (hLD.trans (sup_le_sup_left le_sup_left _)) ?_
  exact SecE3.le_normalizer_inf.trans le_sup_left

end Transport

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
