module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G]

theorem mulAut_eq_tau_of_commute_fix_line {B : Subgroup G} {b b₁ b₂ b₃ : G}
    (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    (hB : B = Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hE : IsElemAb 3 4 B)
    {τ σ : MulAut ↥B}
    (hτb : τ ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hτ₁ : τ ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (hτ₂ : τ ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹)
    (hτ₃ : τ ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹)
    (hτ2 : τ * τ = 1) (hσ2 : σ * σ = 1)
    (hcomm : σ * τ = τ * σ)
    (hσb : σ ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hfix : ∀ x : ↥B, σ x = x → x ∈ Subgroup.zpowers (⟨b, hbB⟩ : ↥B)) :
    σ = τ := by
  classical
  let bB : ↥B := ⟨b, hbB⟩
  let b₁B : ↥B := ⟨b₁, hb₁B⟩
  let b₂B : ↥B := ⟨b₂, hb₂B⟩
  let b₃B : ↥B := ⟨b₃, hb₃B⟩
  let B₁B : Subgroup ↥B := Subgroup.closure ({b₁B, b₂B, b₃B} : Set ↥B)
  have hcardB : Nat.card ↥B = 81 := by
    rw [hE.2]
    norm_num
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hcardB]; norm_num)
  haveI : IsElementaryAbelian 3 ↥B := hE.1
  haveI : IsMulCommutative ↥B := hE.1.toIsMulCommutative
  letI : CommGroup ↥B := IsMulCommutative.instCommGroup
  have hBexp : ∀ x : ↥B, x ^ 3 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.1.exponent_dvd_p x
  have hgen : Subgroup.closure ({bB, b₁B, b₂B, b₃B} : Set ↥B) = ⊤ := by
    have h := Subgroup.closure_preimage_eq_top ({b, b₁, b₂, b₃} : Set G)
    rw [← hB] at h
    have hset : (B.subtype : ↥B → G) ⁻¹' ({b, b₁, b₂, b₃} : Set G) =
        ({bB, b₁B, b₂B, b₃B} : Set ↥B) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
      · rintro (rfl | rfl | rfl | rfl) <;> simp [bB, b₁B, b₂B, b₃B]
    rwa [hset] at h
  have htop : (⊤ : Subgroup ↥B) = Subgroup.zpowers bB ⊔ B₁B := by
    rw [← hgen, closure_four_eq]
  have hb1mem : b₁B ∈ B₁B := Subgroup.subset_closure (by simp)
  have hb2mem : b₂B ∈ B₁B := Subgroup.subset_closure (by simp)
  have hb3mem : b₃B ∈ B₁B := Subgroup.subset_closure (by simp)
  have hcardB₁ : Nat.card ↥B₁B ≤ 27 := by
    have hpow : ∀ x : ↥B₁B, x ^ 3 = 1 := fun x => Subtype.ext (hBexp (x : ↥B))
    have hdvd : Nat.card ↥B₁B ∣ 3 ^ Group.rank ↥B₁B :=
      card_dvd_exponent_pow_rank' (G := ↥B₁B) hpow
    have hrank : Group.rank ↥B₁B ≤ 3 := by
      let t : Finset ↥B₁B :=
        {⟨b₁B, hb1mem⟩, ⟨b₂B, hb2mem⟩, ⟨b₃B, hb3mem⟩}
      have ht : Subgroup.closure (t : Set ↥B₁B) = ⊤ := by
        apply Subgroup.map_injective (f := B₁B.subtype) B₁B.subtype_injective
        rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
        have himage : B₁B.subtype '' (t : Set ↥B₁B) =
            ({b₁B, b₂B, b₃B} : Set ↥B) := by
          ext z
          simp [t]
        rw [himage]
      have hle : Group.rank ↥B₁B ≤ t.card := Group.rank_le ht
      have hcardt : t.card ≤ 3 := by
        simpa [t] using
          Finset.card_le_three (a := (⟨b₁B, hb1mem⟩ : ↥B₁B))
            (b := (⟨b₂B, hb2mem⟩ : ↥B₁B)) (c := (⟨b₃B, hb3mem⟩ : ↥B₁B))
      exact hle.trans hcardt
    calc Nat.card ↥B₁B ≤ 3 ^ Group.rank ↥B₁B := Nat.le_of_dvd (by positivity) hdvd
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hrank
      _ = 27 := by norm_num
  have hb_not_mem : bB ∉ B₁B := by
    intro hmem
    have hle : Subgroup.zpowers bB ≤ B₁B := Subgroup.zpowers_le.mpr hmem
    have htopB₁ : (⊤ : Subgroup ↥B) = B₁B := by
      rw [htop, sup_eq_right.mpr hle]
    have hcard81 : Nat.card ↥B₁B = 81 := by
      rw [← htopB₁, Subgroup.card_top, hcardB]
    omega
  have hbB3 : bB ^ 3 = 1 := hBexp bB
  have hbBne : bB ≠ 1 := fun h1 => hb_not_mem (h1 ▸ B₁B.one_mem)
  have horder : orderOf bB = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hbB3 hbBne
  have hinf : Subgroup.zpowers bB ⊓ B₁B = ⊥ := by
    haveI : Fact (Nat.Prime (Nat.card ↥(Subgroup.zpowers bB))) :=
      ⟨by rw [Nat.card_zpowers, horder]; norm_num⟩
    let K : Subgroup ↥(Subgroup.zpowers bB) :=
      (Subgroup.zpowers bB ⊓ B₁B).subgroupOf (Subgroup.zpowers bB)
    have hK : K = ⊥ ∨ K = ⊤ := Subgroup.eq_bot_or_eq_top_of_prime_card K
    rcases hK with hbot | htopK
    · rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ Subgroup.zpowers bB ∧ x ∈ B₁B := by
        simpa [Subgroup.mem_inf] using hx
      have hxK : (⟨x, hx'.1⟩ : ↥(Subgroup.zpowers bB)) ∈ K := by
        simpa [K, Subgroup.mem_subgroupOf] using hx'.2
      rw [hbot] at hxK
      exact Subtype.ext (by simpa using hxK)
    · exfalso
      have hbK : (⟨bB, Subgroup.mem_zpowers bB⟩ : ↥(Subgroup.zpowers bB)) ∈ K := by
        rw [htopK]
        exact Subgroup.mem_top _
      have hbK' : (⟨bB, Subgroup.mem_zpowers bB⟩ : ↥(Subgroup.zpowers bB)) ∈
          (Subgroup.zpowers bB ⊓ B₁B).subgroupOf (Subgroup.zpowers bB) := by
        simpa [K] using hbK
      have hbIn' := Subgroup.mem_subgroupOf.mp hbK'
      have hbIn : bB ∈ Subgroup.zpowers bB ⊓ B₁B := by
        simpa using hbIn'
      exact hb_not_mem (Subgroup.mem_inf.mp hbIn).2
  have hτ_inv_B₁ : ∀ y : ↥B, y ∈ B₁B → τ y = y⁻¹ := by
    intro y hy
    have hy' : y ∈ Subgroup.closure ({b₁B, b₂B, b₃B} : Set ↥B) := hy
    refine Subgroup.closure_induction (p := fun z _ => τ z = z⁻¹) ?_ ?_ ?_ ?_ hy'
    · rintro z (rfl | rfl | rfl)
      · simpa [b₁B] using hτ₁
      · simpa [b₂B] using hτ₂
      · simpa [b₃B] using hτ₃
    · simp
    · intro x y _ _ ihx ihy
      rw [map_mul, ihx, ihy, mul_inv]
    · intro x _ ih
      rw [map_inv, ih, inv_inv]
  have hτ_eq_inv_iff : ∀ y : ↥B, τ y = y⁻¹ ↔ y ∈ B₁B := by
    intro y
    constructor
    · intro hy
      have hy' : y ∈ Subgroup.zpowers bB ⊔ B₁B := by
        rw [← htop]
        exact Subgroup.mem_top y
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hy'
      have hτa : τ a = a := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [map_zpow, hτb]
      have hτc : τ c = c⁻¹ := hτ_inv_B₁ c hc
      have hcancel : a = a⁻¹ := by
        have h := hy
        rw [map_mul, hτa, hτc, mul_inv] at h
        exact mul_right_cancel h
      have hdiv3 : orderOf a ∣ 3 := by
        simpa [horder] using orderOf_dvd_of_mem_zpowers ha
      have ha2 : a ^ 2 = 1 := by
        rw [pow_two]
        exact eq_inv_iff_mul_eq_one.mp hcancel
      have hdiv2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
      have hdiv1 : orderOf a ∣ 1 := by
        have h := Nat.dvd_gcd hdiv3 hdiv2
        rwa [show Nat.gcd 3 2 = 1 by norm_num] at h
      have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv1)
      simpa [ha1] using hc
    · exact hτ_inv_B₁ y
  have hσ_mem_B₁ : ∀ y : ↥B, y ∈ B₁B → σ y ∈ B₁B := by
    intro y hy
    have hτσy : τ (σ y) = (σ y)⁻¹ := by
      have hcomm_apply : τ (σ y) = σ (τ y) := by
        have h := congrArg (fun f : MulAut ↥B => f y) hcomm.symm
        simpa [MulAut.mul_apply] using h
      calc τ (σ y) = σ (τ y) := hcomm_apply
        _ = σ (y⁻¹) := by rw [hτ_inv_B₁ y hy]
        _ = (σ y)⁻¹ := map_inv σ y
    exact (hτ_eq_inv_iff (σ y)).mp hτσy
  let φ : ↥B₁B →* ↥B₁B :=
    { toFun := fun y => ⟨σ (y : ↥B), hσ_mem_B₁ (y : ↥B) y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp [map_mul] }
  have hφ2 : Function.Involutive φ := by
    intro y
    apply Subtype.ext
    change σ (σ (y : ↥B)) = (y : ↥B)
    have h := congrArg (fun f : MulAut ↥B => f (y : ↥B)) hσ2
    simpa using h
  have hφfree : MonoidHom.FixedPointFree φ := by
    intro y hy
    have hyfix : σ (y : ↥B) = (y : ↥B) := by
      have := congrArg (fun z : ↥B₁B => (z : ↥B)) hy
      simpa [φ] using this
    have hyZ : (y : ↥B) ∈ Subgroup.zpowers bB := hfix (y : ↥B) hyfix
    have hybot : (y : ↥B) ∈ (⊥ : Subgroup ↥B) := by
      rw [← hinf]
      exact ⟨hyZ, y.2⟩
    apply Subtype.ext
    simpa using hybot
  have hφinv : ∀ y : ↥B₁B, φ y = y⁻¹ := fun y =>
    congrFun (hφfree.coe_eq_inv_of_involutive hφ2) y
  have hσ_inv_B₁ : ∀ y : ↥B, y ∈ B₁B → σ y = y⁻¹ := by
    intro y hy
    let y' : ↥B₁B := ⟨y, hy⟩
    have h := hφinv y'
    have hcoe := congrArg (fun z : ↥B₁B => (z : ↥B)) h
    simpa [φ, y'] using hcoe
  apply MulEquiv.ext
  intro x
  have hx : x ∈ Subgroup.closure ({bB, b₁B, b₂B, b₃B} : Set ↥B) := by
    rw [hgen]
    exact Subgroup.mem_top x
  refine Subgroup.closure_induction (p := fun z _ => σ z = τ z) ?_ ?_ ?_ ?_ hx
  · rintro z (rfl | rfl | rfl | rfl)
    · simpa [bB] using hσb.trans hτb.symm
    · have hτ₁' : τ b₁B = b₁B⁻¹ := by simpa [b₁B] using hτ₁
      rw [hσ_inv_B₁ b₁B hb1mem]
      exact hτ₁'.symm
    · have hτ₂' : τ b₂B = b₂B⁻¹ := by simpa [b₂B] using hτ₂
      rw [hσ_inv_B₁ b₂B hb2mem]
      exact hτ₂'.symm
    · have hτ₃' : τ b₃B = b₃B⁻¹ := by simpa [b₃B] using hτ₃
      rw [hσ_inv_B₁ b₃B hb3mem]
      exact hτ₃'.symm
  · simp
  · intro x y _ _ ihx ihy
    rw [map_mul, map_mul, ihx, ihy]
  · intro x _ ih
    rw [map_inv, map_inv, ih]

end CFSG.RankThree.PartTwo.Sec21.FF81
