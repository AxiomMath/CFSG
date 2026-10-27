module

public import CFSG.Quasithin.EmptyFaithful.SBc17BlkSpec
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Aux
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc17

namespace Blk

theorem charP_two {F : Type} [Field F] [Fintype F] {n : ℕ} (h : Fintype.card F = 2 ^ n) :
    CharP F 2 :=
  charP_of_card_eq_prime_pow h

theorem four_le_card {F : Type} [Fintype F] {n : ℕ} (hn : 1 < n) (h : Fintype.card F = 2 ^ n) :
    4 ≤ Fintype.card F := by
  rw [h]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem eq_zero_of_forall_mulVec_eq {F : Type} [Field F] {v : Fin 2 → F}
    (h : ∀ g : SL2 F, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v = 0 := by
  have e1 := congrFun (h (uElt 1)) 0
  have e2 := congrFun (h (lElt 1)) 1
  simp [uElt, lElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2
  ext i
  fin_cases i
  · simpa using e2
  · simpa using e1

theorem cocycle_one {Γ : Type} [Group Γ] {F : Type} [Field F] (α : Γ →* SL2 F)
    (d : Γ → (Fin 2 → F))
    (hd : ∀ ℓ ℓ' : Γ, d (ℓ * ℓ') = d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ')) :
    d 1 = 0 := by
  have h := hd 1 1
  simpa using h

theorem cocycle_ker_eq_zero {Γ : Type} [Group Γ] {F : Type} [Field F] (α : Γ →* SL2 F)
    (hαs : Function.Surjective α) (d : Γ → (Fin 2 → F))
    (hd : ∀ ℓ ℓ' : Γ, d (ℓ * ℓ') = d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ'))
    (hu : ∀ q ∈ α.ker, ∀ ℓ : Γ, ∃ u ∈ α.ker, d u = 0 ∧ ℓ * q * ℓ⁻¹ = u * q) :
    ∀ q ∈ α.ker, d q = 0 := by
  intro q hq
  have hq1 : α q = 1 := hq
  apply eq_zero_of_forall_mulVec_eq
  intro g
  obtain ⟨ℓ, rfl⟩ := hαs g
  obtain ⟨u, hu1, hu0, hℓ⟩ := hu q hq ℓ
  have hu1' : α u = 1 := hu1
  have e1 : d (ℓ * q * ℓ⁻¹) = d q := by
    rw [hℓ, hd, hu0, hu1']
    simp
  have e2 : d (ℓ * q * ℓ⁻¹) = d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d q) +
      (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ⁻¹) := by
    rw [mul_assoc, hd, hd, hq1]
    simp [Matrix.mulVec_add, add_assoc]
  have e3 : d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ⁻¹) = 0 := by
    rw [← hd, mul_inv_cancel]
    exact cocycle_one α d hd
  calc (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d q)
      = (d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ⁻¹)) +
          (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d q) := by rw [e3, zero_add]
    _ = d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d q) +
          (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ⁻¹) := by abel
    _ = d (ℓ * q * ℓ⁻¹) := e2.symm
    _ = d q := e1

theorem cocycle_eq_zero (hCoc : CocycleStatement) {Γ : Type} [Group Γ] {F : Type} [Field F]
    [Fintype F] [DecidableEq F] [CharP F 2] (h4 : 4 ≤ Fintype.card F) (α : Γ →* SL2 F)
    (hαs : Function.Surjective α) (d : Γ → (Fin 2 → F))
    (hd : ∀ ℓ ℓ' : Γ, d (ℓ * ℓ') = d ℓ + (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (d ℓ'))
    (hker : ∀ q ∈ α.ker, d q = 0) (hbor : ∀ g ∈ borelSub F, ∃ x : Γ, α x = g ∧ d x = 0) :
    ∀ ℓ : Γ, d ℓ = 0 := by
  have hconst : ∀ ℓ ℓ' : Γ, α ℓ = α ℓ' → d ℓ = d ℓ' := by
    intro ℓ ℓ' h
    have hq : ℓ⁻¹ * ℓ' ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h1 := hd ℓ (ℓ⁻¹ * ℓ')
    rw [mul_inv_cancel_left, hker _ hq] at h1
    simpa using h1.symm
  let dbar : SL2 F → (Fin 2 → F) := fun g => d (Function.surjInv hαs g)
  have hdbar : ∀ ℓ : Γ, dbar (α ℓ) = d ℓ := fun ℓ => hconst _ _ (Function.surjInv_eq hαs (α ℓ))
  have hcoc : ∀ g h : SL2 F,
      dbar (g * h) = dbar g + (g : Matrix (Fin 2) (Fin 2) F).mulVec (dbar h) := by
    intro g h
    have hga : α (Function.surjInv hαs g) = g := Function.surjInv_eq hαs g
    have hhb : α (Function.surjInv hαs h) = h := Function.surjInv_eq hαs h
    have hgh : g * h = α (Function.surjInv hαs g * Function.surjInv hαs h) := by
      rw [map_mul, hga, hhb]
    rw [hgh, hdbar, hd, hga]
  have hbor0 : ∀ b ∈ borelSub F, dbar b = 0 := by
    intro b hb
    obtain ⟨x, hx, hx0⟩ := hbor b hb
    rw [← hx, hdbar, hx0]
  have h0 := hCoc h4 dbar hcoc hbor0
  intro ℓ
  rw [← hdbar, h0]

theorem mem_blockZ_iff {G : Type} [Group G] {L : Subgroup G} {x : G} :
    x ∈ blockZ L ↔ x ∈ blockU L ∧ ∀ ℓ ∈ L, ℓ * x = x * ℓ := by
  unfold blockZ
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem commutator_mem_blockU {G : Type} [Group G] {L : Subgroup G} {z ℓ : G}
    (hz : z ∈ blockQ L) (hℓ : ℓ ∈ L) : z * ℓ * z⁻¹ * ℓ⁻¹ ∈ blockU L :=
  Subgroup.commutator_mem_commutator hz hℓ

noncomputable def commCocycle {G : Type} [Group G] {F : Type} [Field F] (L : Subgroup G)
    (β : blockU L →* Multiplicative (Fin 2 → F)) {z : G} (hz : z ∈ blockQ L) (ℓ : ↥L) :
    Fin 2 → F :=
  Multiplicative.toAdd (β ⟨z * (ℓ : G) * z⁻¹ * (ℓ : G)⁻¹, commutator_mem_blockU hz ℓ.2⟩)

theorem commCocycle_mul {G : Type} [Group G] {F : Type} [Field F] {L : Subgroup G}
    (α : ↥L →* SL2 F) (β : blockU L →* Multiplicative (Fin 2 → F))
    (hβ : ∀ ℓ : ↥L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {z : G} (hz : z ∈ blockQ L) (ℓ ℓ' : ↥L) :
    commCocycle L β hz (ℓ * ℓ') = commCocycle L β hz ℓ +
      (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (commCocycle L β hz ℓ') := by
  let a : blockU L := ⟨z * (ℓ : G) * z⁻¹ * (ℓ : G)⁻¹, commutator_mem_blockU hz ℓ.2⟩
  let u : blockU L := ⟨z * (ℓ' : G) * z⁻¹ * (ℓ' : G)⁻¹, commutator_mem_blockU hz ℓ'.2⟩
  let ab : blockU L :=
    ⟨z * ((ℓ * ℓ' : ↥L) : G) * z⁻¹ * ((ℓ * ℓ' : ↥L) : G)⁻¹, commutator_mem_blockU hz (ℓ * ℓ').2⟩
  have hv : ((a⁻¹ * ab : blockU L) : G) = ℓ * (u : G) * ℓ⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, a, ab, u]
    group
  have h1 := hβ ℓ u (a⁻¹ * ab) hv
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv] at h1
  change Multiplicative.toAdd (β ab) = Multiplicative.toAdd (β a) +
    (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))
  rw [← h1]
  abel

theorem commCocycle_eq_zero_of_commute {G : Type} [Group G] {F : Type} [Field F] {L : Subgroup G}
    (β : blockU L →* Multiplicative (Fin 2 → F)) {z : G} (hz : z ∈ blockQ L) {ℓ : ↥L}
    (h : (ℓ : G) * z = z * ℓ) : commCocycle L β hz ℓ = 0 := by
  have h1 : (⟨z * (ℓ : G) * z⁻¹ * (ℓ : G)⁻¹, commutator_mem_blockU hz ℓ.2⟩ : blockU L) = 1 := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.symm
  unfold commCocycle
  rw [h1, map_one]
  rfl

theorem commutator_mem_blockZ (hCoc : CocycleStatement) {G : Type} [Group G] {L : Subgroup G}
    (hshort : IsShort2 L) {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (h4 : 4 ≤ Fintype.card F) (α : ↥L →* SL2 F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (β : blockU L →* Multiplicative (Fin 2 → F))
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβ : ∀ ℓ : ↥L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {z : G} (hz : z ∈ blockQ L)
    (hbor : ∀ g ∈ borelSub F, ∃ (x : G) (hx : x ∈ L), α ⟨x, hx⟩ = g ∧ x * z = z * x) :
    ∀ ℓ ∈ L, z * ℓ * z⁻¹ * ℓ⁻¹ ∈ blockZ L := by
  have hd := commCocycle_mul α β hβ hz
  have hker : ∀ q ∈ α.ker, commCocycle L β hz q = 0 := by
    refine cocycle_ker_eq_zero α hαs _ hd ?_
    intro q hq ℓ
    have hq' : (q : G) ∈ blockQ L := by
      have h := hq
      rw [hαk, ← SBc13.pCoreOf_subgroupOf_eq_pCore_J1, Subgroup.mem_subgroupOf] at h
      exact h
    have hq1 : α q = 1 := hq
    have hU : ((ℓ * q * ℓ⁻¹ * q⁻¹ : ↥L) : G) ∈ blockU L := by
      have h : (ℓ : G) * q * (ℓ : G)⁻¹ * (q : G)⁻¹ ∈ blockU L := by
        have h' := Subgroup.commutator_mem_commutator ℓ.2 hq'
        rw [Subgroup.commutator_comm] at h'
        exact h'
      simpa using h
    refine ⟨ℓ * q * ℓ⁻¹ * q⁻¹, ?_, ?_, by group⟩
    · rw [MonoidHom.mem_ker]
      simp [hq1]
    · apply commCocycle_eq_zero_of_commute β hz
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hshort.2.2.1.1 hU)).2 z hz).symm
  have hall : ∀ ℓ : ↥L, commCocycle L β hz ℓ = 0 := by
    refine cocycle_eq_zero hCoc h4 α hαs _ hd hker ?_
    intro g hg
    obtain ⟨x, hx, hαx, hxz⟩ := hbor g hg
    exact ⟨⟨x, hx⟩, hαx, commCocycle_eq_zero_of_commute β hz hxz⟩
  intro ℓ hℓ
  have h1 : (⟨z * ℓ * z⁻¹ * ℓ⁻¹, commutator_mem_blockU hz hℓ⟩ : blockU L) ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    exact toAdd_eq_zero.mp (hall ⟨ℓ, hℓ⟩)
  rw [hβk, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem commute_of_commutator_mem_blockZ {G : Type} [Group G] {L : Subgroup G}
    (hshort : IsShort2 L) {z : G} (hz : ∀ ℓ ∈ L, z * ℓ * z⁻¹ * ℓ⁻¹ ∈ blockZ L) :
    ∀ ℓ ∈ L, ℓ * z = z * ℓ := by
  have hU : ∀ ℓ ∈ L, z * ℓ * z⁻¹ * ℓ⁻¹ ∈ blockU L := fun ℓ hℓ => (mem_blockZ_iff.mp (hz ℓ hℓ)).1
  have hC : ∀ ℓ ∈ L, ∀ m ∈ L, m * (z * ℓ * z⁻¹ * ℓ⁻¹) = (z * ℓ * z⁻¹ * ℓ⁻¹) * m :=
    fun ℓ hℓ => (mem_blockZ_iff.mp (hz ℓ hℓ)).2
  let φ : ↥L →* blockU L :=
    { toFun := fun ℓ => ⟨z * (ℓ : G) * z⁻¹ * (ℓ : G)⁻¹, hU ℓ ℓ.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro ℓ ℓ'
        apply Subtype.ext
        have hc := hC ℓ' ℓ'.2 ℓ ℓ.2
        show z * ((ℓ : G) * ℓ') * z⁻¹ * ((ℓ : G) * ℓ')⁻¹ =
          (z * (ℓ : G) * z⁻¹ * (ℓ : G)⁻¹) * (z * (ℓ' : G) * z⁻¹ * (ℓ' : G)⁻¹)
        calc z * ((ℓ : G) * ℓ') * z⁻¹ * ((ℓ : G) * ℓ')⁻¹
            = (z * (ℓ : G) * z⁻¹ * (ℓ : G)⁻¹) *
                ((ℓ : G) * (z * (ℓ' : G) * z⁻¹ * (ℓ' : G)⁻¹) * (ℓ : G)⁻¹) := by group
          _ = _ := by rw [hc]; group }
  have hp : IsPGroup 2 (↥L ⧸ φ.ker) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H ℓ =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
      apply Subtype.ext
      simpa using hshort.2.2.1.2 _ (φ ℓ).2
  have htop : φ.ker = ⊤ := hshort.1 φ.ker hp
  intro ℓ hℓ
  have h1 : (⟨ℓ, hℓ⟩ : ↥L) ∈ φ.ker := by
    rw [htop]
    trivial
  rw [MonoidHom.mem_ker] at h1
  have h2 : z * ℓ * z⁻¹ * ℓ⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm

end Blk

theorem centralizer_block_of_borel (hStd : StdPositionStatement) (hCoc : CocycleStatement)
    (hCen : CenterStatement) {G : Type} [Group G] [Finite G] {L B : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hshort : IsShort2 L) (hlin : IsLin2Type L n) (hB : IsBorelOfBlock L B) :
    B ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  classical
  obtain ⟨F, instF, instFin, hcard, α, hαs, hαk, β, -, hβk, hβ⟩ := hlin
  have : CharP F 2 := Blk.charP_two hcard
  have h4 : 4 ≤ Fintype.card F := Blk.four_le_card hn hcard
  obtain ⟨g₀, hg₀, hconjL, hbor⟩ := hStd h4 α hαs hαk hB
  intro z hz
  obtain ⟨hzB, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzC' : ∀ b ∈ B, b * z = z * b := Subgroup.mem_centralizer_iff.mp hzC
  have hz'B : g₀⁻¹ * z * g₀ ∈ conjSub g₀⁻¹ B := by
    rw [mem_conjSub, inv_inv]
    have e : g₀ * (g₀⁻¹ * z * g₀) * g₀⁻¹ = z := by group
    rw [e]
    exact hzB
  have hz'L : g₀⁻¹ * z * g₀ ∈ L := hconjL _ hz'B
  have hcomm : ∀ x ∈ conjSub g₀⁻¹ B, x * (g₀⁻¹ * z * g₀) = (g₀⁻¹ * z * g₀) * x := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have h := hzC' _ hx
    calc x * (g₀⁻¹ * z * g₀) = g₀⁻¹ * ((g₀ * x * g₀⁻¹) * z) * g₀ := by group
      _ = g₀⁻¹ * (z * (g₀ * x * g₀⁻¹)) * g₀ := by rw [h]
      _ = (g₀⁻¹ * z * g₀) * x := by group
  have hbor' : ∀ g ∈ borelSub F, ∃ (x : G) (hx : x ∈ L), α ⟨x, hx⟩ = g ∧
      x * (g₀⁻¹ * z * g₀) = (g₀⁻¹ * z * g₀) * x := by
    intro g hg
    obtain ⟨x, hx, hxB, hαx⟩ := (hbor g).mp hg
    exact ⟨x, hx, hαx, hcomm x hxB⟩
  have hα1 : α ⟨g₀⁻¹ * z * g₀, hz'L⟩ = 1 := by
    apply hCen h4 _ ((hbor _).mpr ⟨g₀⁻¹ * z * g₀, hz'L, hz'B, rfl⟩)
    intro b hb
    obtain ⟨x, hx, hαx, hxz⟩ := hbor' b hb
    rw [← hαx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxz.symm
  have hz'Q : g₀⁻¹ * z * g₀ ∈ blockQ L := by
    have h : (⟨g₀⁻¹ * z * g₀, hz'L⟩ : ↥L) ∈ α.ker := hα1
    rw [hαk, ← SBc13.pCoreOf_subgroupOf_eq_pCore_J1, Subgroup.mem_subgroupOf] at h
    exact h
  have hcent := Blk.commute_of_commutator_mem_blockZ hshort
    (Blk.commutator_mem_blockZ hCoc hshort h4 α hαs hαk β hβk hβ hz'Q hbor')
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hc := hcent (g₀⁻¹ * h * g₀) (L.mul_mem (L.mul_mem (L.inv_mem hg₀) hh) hg₀)
  calc h * z = g₀ * ((g₀⁻¹ * h * g₀) * (g₀⁻¹ * z * g₀)) * g₀⁻¹ := by group
    _ = g₀ * ((g₀⁻¹ * z * g₀) * (g₀⁻¹ * h * g₀)) * g₀⁻¹ := by rw [hc]
    _ = z * h := by group

end SBc17

end CFSG.Quasithin
