module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Hyp
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BFrattini
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Act
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmOrder

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] {S : Subgroup G}

theorem mem_nor_of_forward {H : Subgroup G} {n : G} (h1 : ∀ y ∈ H, n * y * n⁻¹ ∈ H)
    (h2 : ∀ y ∈ H, n⁻¹ * y * n ∈ H) : n ∈ Nor H := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  simpa [mul_assoc] using this

theorem psi0_eq_one_of_cen (e : ↥S ≃* Multiplicative F6) (n : ↥(Nor S))
    (hn : ∀ z : ↥S, (n : G) * (z : G) = (z : G) * (n : G)) : psi0 e n = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨z, rfl⟩ : ∃ z : ↥S, Multiplicative.toAdd (e z) = v :=
    ⟨e.symm (Multiplicative.ofAdd v), by simp⟩
  rw [psi0_apply]
  have : (⟨(n : G) * (z : G) * (n : G)⁻¹, (n.2 (z : G)).mp z.2⟩ : ↥S) = z :=
    Subtype.ext (by
      show (n : G) * (z : G) * (n : G)⁻¹ = (z : G)
      rw [hn z]
      group)
  rw [this]
  rfl

theorem inf_nor_eq_inf_cen {B : Subgroup G} (hSp : ∀ x ∈ S, x ^ 2 = 1) (hBp : ∀ x ∈ B, x ^ 3 = 1)
    (hBS : B ≤ Nor S) : S ⊓ Nor B = S ⊓ CenS B := by
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hxS, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyN := hBS hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 hxN y).1 hy
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hxN y).1 hy) (inv_mem hy) |> fun h => by
      simpa [mul_assoc] using h
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ S := by
    have h3 : y * x⁻¹ * y⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hyN x⁻¹).1 (inv_mem hxS)
      simpa [mul_assoc] using this
    simpa [mul_assoc] using mul_mem hxS h3
  have hc : x * y * x⁻¹ * y⁻¹ = 1 := by
    set c := x * y * x⁻¹ * y⁻¹
    have a2 := hSp c h2
    have a3 := hBp c h1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [a2, a3]; simp
  have : x * y = y * x := by
    have := congrArg (fun z => z * y * x) hc
    simpa [mul_assoc] using this
  exact this.symm

variable [Finite G]

theorem range_psi0_ne_O (e : ↥S ≃* Multiplicative F6) {B : Subgroup G}
    (hSE : IsElemAb 2 6 S) (hBE : IsElemAb 3 3 B) (hBS : B ≤ Nor S)
    (hker : ∀ n : ↥(Nor S), psi0 e n = 1 → (n : G) ∈ S)
    (hcard : Nat.card ↥(Nor B ⊓ Nor S) ≤ 648) (hE27 : HypOmNormalizerE27) :
    (psi0 e).range ≠ TauCeti.QuadraticMap.orthogonalGroup qMinusForm := by
  intro heq
  classical
  haveI := hSE.1
  haveI := hBE.1
  have hSp : ∀ x ∈ S, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S) x hx
  have hBp : ∀ x ∈ B, x ^ 3 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := B) x hx
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => by
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : S) ⟨y, hy⟩)
  have hSB : ∀ x ∈ S, x ∈ B → x = 1 := fun x hxS hxB => by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hSp x hxS, hBp x hxB]; simp
  have hSN : S ⊓ Nor B = S ⊓ CenS B := inf_nor_eq_inf_cen hSp hBp hBS
  have hfr : Nor (S ⊔ B) ⊓ Nor S = (S ⊔ B) ⊓ Nor S ⊔ Nor B ⊓ Nor S := by
    refine B_frattini_B ?_ ?_ hBS hSN
    · obtain ⟨k, hk⟩ : ∃ k, Nat.card S = 2 ^ k := ⟨6, hSE.2⟩
      exact IsPGroup.of_card hk
    · exact IsPGroup.of_card (n := 3) hBE.2
  let Bs : Subgroup ↥(Nor S) := B.subgroupOf (Nor S)
  let f : ↥Bs →* (F6 ≃ₗ[ZMod 2] F6) := (psi0 e).comp Bs.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := hker x.1 hx
    have h2 : (x.1 : G) ∈ B := x.2
    exact Subtype.ext (Subtype.ext (hSB _ h1 h2))
  let E : Subgroup (F6 ≃ₗ[ZMod 2] F6) := f.range
  have hEeq : E = Bs.map (psi0 e) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm := by
    rw [← heq]
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  have hEcard : Nat.card E = 3 ^ 3 := by
    rw [← hBE.2]
    calc Nat.card E = Nat.card Bs := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      _ = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv
  have hEA : IsElementaryAbelian 3 E := by
    refine
      { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
        exponent_dvd_p := ?_ }
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : F6 ≃ₗ[ZMod 2] F6) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subtype.ext (hBc _ x.2 _ y.2))
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
      obtain ⟨x, hx⟩ := a.2
      apply Subtype.ext
      show (a : F6 ≃ₗ[ZMod 2] F6) ^ 3 = 1
      rw [← hx, ← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (Subtype.ext (hBp _ x.2))
      rw [this, map_one]
  have hN27 := hE27 E hEO ⟨hEA, hEcard⟩
  have hpre : ∀ y : ↥(Nor S), (y : G) ∈ S ⊔ B ↔ psi0 e y ∈ E := by
    intro y
    constructor
    · intro hy
      have hle : S ⊔ B ≤ ((E.comap (psi0 e)).map (Nor S).subtype) := by
        refine sup_le ?_ ?_
        · intro x hx
          refine ⟨⟨x, Subgroup.le_normalizer hx⟩, ?_, rfl⟩
          show psi0 e ⟨x, _⟩ ∈ E
          have : psi0 e ⟨x, Subgroup.le_normalizer hx⟩ = 1 :=
            psi0_eq_one_of_cen e _ (fun z => hSc _ hx _ z.2)
          rw [this]
          exact one_mem _
        · intro x hx
          exact ⟨⟨x, hBS hx⟩, ⟨⟨⟨x, hBS hx⟩, hx⟩, rfl⟩, rfl⟩
      obtain ⟨y', hy', hyy⟩ := hle hy
      have : y' = y := Subtype.ext hyy
      rw [← this]
      exact hy'
    · rintro ⟨b', hb'⟩
      have hb'' : psi0 e b'.1 = psi0 e y := hb'
      have h1 : psi0 e (b'.1⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hb'', inv_mul_cancel]
      have h2 : (b'.1 : G)⁻¹ * (y : G) ∈ S := hker _ h1
      have hb'B : (b'.1 : G) ∈ B := b'.2
      have : (y : G) = (b'.1 : G) * ((b'.1 : G)⁻¹ * (y : G)) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb'B) (Subgroup.mem_sup_left h2)
  let M₂s : Subgroup ↥(Nor S) := (Nor B ⊓ Nor S).subgroupOf (Nor S)
  let Q : Subgroup (F6 ≃ₗ[ZMod 2] F6) := M₂s.map (psi0 e)
  have hEQ : E ≤ Q := by
    rw [hEeq]
    refine Subgroup.map_mono (fun x hx => ?_)
    have hxB : (x : G) ∈ B := hx
    show (x : G) ∈ Nor B ⊓ Nor S
    exact Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hxB, x.2⟩
  have hsub : (Subgroup.normalizer (E : Set (F6 ≃ₗ[ZMod 2] F6)) ⊓
      TauCeti.QuadraticMap.orthogonalGroup qMinusForm) ≤ Q := by
    intro g hg
    have hgO : g ∈ (psi0 e).range := heq ▸ hg.2
    obtain ⟨n, rfl⟩ := hgO
    have hconj : ∀ m : ↥(Nor S), psi0 e m ∈ Subgroup.normalizer (E : Set (F6 ≃ₗ[ZMod 2] F6)) →
        ∀ y ∈ S ⊔ B, (m : G) * y * (m : G)⁻¹ ∈ S ⊔ B := by
      intro m hm y hy
      have hyN : y ∈ Nor S := sup_le Subgroup.le_normalizer hBS hy
      have h1 := (hpre ⟨y, hyN⟩).1 hy
      have h2 := (Subgroup.mem_normalizer_iff.1 hm (psi0 e ⟨y, hyN⟩)).1 h1
      have h3 : psi0 e (m * ⟨y, hyN⟩ * m⁻¹) ∈ E := by
        rw [map_mul, map_mul, map_inv]
        exact h2
      exact (hpre _).2 h3
    have hnm : (n : G) ∈ Nor (S ⊔ B) := by
      refine mem_nor_of_forward (hconj n hg.1) (fun y hy => ?_)
      have := hconj n⁻¹ (by rw [map_inv]; exact inv_mem hg.1) y hy
      simpa using this
    have hmem : (n : G) ∈ Nor (S ⊔ B) ⊓ Nor S := Subgroup.mem_inf.2 ⟨hnm, n.2⟩
    rw [hfr] at hmem
    have hle2 : (S ⊔ B) ⊓ Nor S ⊔ Nor B ⊓ Nor S ≤ (Q.comap (psi0 e)).map (Nor S).subtype := by
      refine sup_le ?_ ?_
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
        exact ⟨⟨x, hx2⟩, hEQ ((hpre ⟨x, hx2⟩).1 hx1), rfl⟩
      · intro x hx
        exact ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩,
          ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩, hx, rfl⟩, rfl⟩
    obtain ⟨n', hn', hnn'⟩ := hle2 hmem
    have : n' = n := Subtype.ext hnn'
    rw [← this]
    exact hn'
  have hQcard : Nat.card Q ≤ Nat.card M₂s :=
    Nat.card_le_card_of_surjective (fun k : M₂s => (⟨psi0 e k, k.1, k.2, rfl⟩ : Q)) (by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩)
  have hM₂card : Nat.card M₂s = Nat.card ↥(Nor B ⊓ Nor S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have := Subgroup.card_le_of_le hsub
  omega

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
