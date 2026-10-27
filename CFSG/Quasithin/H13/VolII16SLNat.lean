module

public import CFSG.Quasithin.H13.VolII16Forms
public import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.Quasithin.Background.JonesParshallSLn

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix Subgroup

theorem topBot_data {D : FFModel} (hs : D.sec = ⊤) (hk : D.ker = ⊥) {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {Z : Subgroup W} (h : D.Realizes H ⊤ Z) :
    ∃ (π : D.Gam →* ↥H) (b : W →* D.Amb), Function.Surjective π ∧ Function.Surjective b ∧
      (∀ w, b w = 1 ↔ w ∈ Z) ∧ ∀ γ w, b (((π γ : ↥H) : MulAut W) w) = D.act γ (b w) := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  set e := secEquivAmb D hs hk
  let β₁ : W →* D.Sec :=
    { toFun := fun v => β ⟨v, mem_top v⟩
      map_one' := map_one β
      map_mul' := fun x y => map_mul β ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
  refine ⟨π, e.toMonoidHom.comp β₁, hπs, fun y => ?_, fun w => ?_, fun γ w => ?_⟩
  · obtain ⟨u, hu⟩ := hβs (e.symm y)
    refine ⟨u, ?_⟩
    show e (β ⟨(u : W), mem_top _⟩) = y
    have hu' : (⟨(u : W), mem_top _⟩ : ↥(⊤ : Subgroup W)) = u := rfl
    rw [hu', hu, MulEquiv.apply_symm_apply]
  · show e (β₁ w) = 1 ↔ w ∈ Z
    rw [e.map_eq_one_iff]
    exact hβk ⟨w, mem_top w⟩
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₁ w)
    have hmem : D.act γ (m : D.Amb) ∈ D.sec := (Subgroup.eq_top_iff' D.sec).mp hs _
    have h1 := hβe γ ⟨w, mem_top w⟩ m (mem_top _) hmem hm.symm
    show e (β ⟨((π γ : ↥H) : MulAut W) w, mem_top _⟩) = D.act γ (e (β₁ w))
    rw [h1, ← hm]
    rfl

theorem natSL_data {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {W : Type}
    [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (h : (FFModel.nat (StatedSL n K)).Realizes H ⊤ Z) :
    ∃ (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut W)
      (β : W →* Multiplicative (Fin n → ZMod 2)),
      (∀ g, ρ g ∈ H) ∧ (∀ x ∈ H, ∃ g, ρ g = x) ∧ Function.Surjective β ∧
        (∀ w, β w = 1 ↔ w ∈ Z) ∧
        ∀ g w, Multiplicative.toAdd (β (ρ g w)) =
          (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (β w) := by
  classical
  obtain ⟨π, hπs, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  let ψ : SpecialLinearGroup (Fin n) (ZMod 2) →* ↥(StatedSL n K) :=
    (specialLinearGroupEquivStatedSL n K).toMonoidHom.comp
      (SpecialLinearGroup.map φ.symm.toRingHom)
  have hψ : ∀ g, ((ψ g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)).map φ.symm := fun g => rfl
  have hψs : Function.Surjective ψ := fun γ => by
    obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL n K).surjective γ
    refine ⟨SpecialLinearGroup.map φ.toRingHom A, ?_⟩
    show (specialLinearGroupEquivStatedSL n K) (SpecialLinearGroup.map φ.symm.toRingHom
      (SpecialLinearGroup.map φ.toRingHom A)) = _
    congr 1
    ext i j
    simp
  let π' : ↥(StatedSL n K) →* ↥H := π
  let ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* MulAut W := H.subtype.comp (π'.comp ψ)
  let q : ↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤ ≃* Multiplicative (Fin n → K) :=
    ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf ⊤)).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  have hq : ∀ m : ↥(⊤ : Subgroup (Multiplicative (Fin n → K))),
      q (QuotientGroup.mk m) = (m : Multiplicative (Fin n → K)) := fun _ => rfl
  let β₁ : W →* ↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤ :=
    { toFun := fun v => β₀ ⟨v, mem_top v⟩
      map_one' := map_one β₀
      map_mul' := fun x y => map_mul β₀ ⟨x, mem_top x⟩ ⟨y, mem_top y⟩ }
  let b : W →* Multiplicative (Fin n → K) := q.toMonoidHom.comp β₁
  have hb : ∀ g w, Multiplicative.toAdd (b (ρ g w)) =
      ((ψ g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Multiplicative.toAdd (b w) := by
    intro g w
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₁ w)
    have h1 := hβe (ψ g) ⟨w, mem_top w⟩ m (mem_top _) (mem_top _) hm.symm
    have h2 : b w = (m : Multiplicative (Fin n → K)) := by
      show q (β₁ w) = _
      rw [← hm, hq]
    have h3 : b (ρ g w) = natAct (StatedSL n K) (ψ g) (m : Multiplicative (Fin n → K)) := by
      show q (β₀ ⟨((π (ψ g) : ↥H) : MulAut W) w, mem_top _⟩) = _
      rw [h1]
      rfl
    rw [h3, h2]
    rfl
  let c : Multiplicative (Fin n → K) →* Multiplicative (Fin n → ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (fun i => φ (Multiplicative.toAdd x i))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        funext i
        simp }
  have hc : ∀ x, Multiplicative.toAdd (c x) = fun i => φ (Multiplicative.toAdd x i) :=
    fun _ => rfl
  have hci : Function.Injective c := fun x y hxy => by
    have h1 := congrArg Multiplicative.toAdd hxy
    rw [hc, hc] at h1
    apply Multiplicative.toAdd.injective
    funext i
    exact φ.injective (congrFun h1 i)
  refine ⟨ρ, c.comp b, fun g => (π (ψ g)).2, fun x hx => ?_, fun y => ?_, fun w => ?_,
    fun g w => ?_⟩
  · obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := hψs γ
    exact ⟨g, congrArg Subtype.val hγ⟩
  · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨Multiplicative.ofAdd
      (fun i => φ.symm (Multiplicative.toAdd y i)), mem_top _⟩))
    refine ⟨u, ?_⟩
    show c (q (β₀ ⟨(u : W), mem_top _⟩)) = y
    have hu' : (⟨(u : W), mem_top _⟩ : ↥(⊤ : Subgroup W)) = u := rfl
    rw [hu', hu]
    change c (Multiplicative.ofAdd (fun i => φ.symm (Multiplicative.toAdd y i))) = y
    apply Multiplicative.toAdd.injective
    funext i
    rw [hc]
    simp
  · rw [MonoidHom.comp_apply, ← map_one c, hci.eq_iff, ← (hβk ⟨w, mem_top w⟩)]
    show q (β₁ w) = 1 ↔ β₁ w = 1
    exact q.map_eq_one_iff
  · show Multiplicative.toAdd (c (b (ρ g w))) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd (c (b w))
    rw [hc, hc, hb, hψ]
    funext i
    have h1 := RingHom.map_mulVec φ.toRingHom ((g : Matrix (Fin n) (Fin n) (ZMod 2)).map φ.symm)
      (Multiplicative.toAdd (b w)) i
    have h2 : ((g : Matrix (Fin n) (Fin n) (ZMod 2)).map φ.symm).map φ.toRingHom =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      ext k l
      simp
    rw [h2] at h1
    exact h1

section Cover

variable {n : ℕ} {K : Type} [Field K] [Finite K] {W : Type} [CommGroup W] [Finite W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W}

omit [Finite W] in
theorem mem_closure_of_commV {G : Type*} [Group G] {ρ : G →* MulAut W} (hρH : ∀ g, ρ g ∈ H)
    (hρs : ∀ x ∈ H, ∃ g, ρ g = x) (hcomm : commV H = ⊤) (w : W) :
    w ∈ Subgroup.closure {x | ∃ g v, x = ρ g v * v⁻¹} := by
  have hw : w ∈ commV H := hcomm ▸ mem_top w
  have heq : {x | ∃ g v, x = ρ g v * v⁻¹} = {x | ∃ y ∈ H, ∃ v, y v * v⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨g, v, rfl⟩
      exact ⟨_, hρH g, v, rfl⟩
    · rintro ⟨y, hy, v, rfl⟩
      obtain ⟨g, rfl⟩ := hρs y hy
      exact ⟨g, v, rfl⟩
  rw [heq]
  exact hw

theorem muF2_invTranspose (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    muF2 n (invTransposeSL n (ZMod 2) g) x =
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ x := by
  rw [muF2_apply', invTransposeSL_coe]

omit [Finite W] in
theorem natSL_eq_bot (hZB : Z1A (muF2 n) = B1A (muF2 n)) (hK : Nat.card K = 2)
    (hW2 : ∀ w : W, w ^ 2 = 1) (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : (FFModel.nat (StatedSL n K)).Realizes H ⊤ Z) : Z = ⊥ := by
  obtain ⟨ρ, β, hρH, hρs, hβs, hβk, hβe⟩ := natSL_data hK h
  exact eq_bot_of_Z1A_eq_B1A (μ := fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
    (g : Matrix (Fin n) (Fin n) (ZMod 2)))
    (θ := invTransposeSL n (ZMod 2)) muF2_invTranspose hZB hW2 hβs hβk
    (fun g z hz => hZ hz _ (hρH g)) hβe (mem_closure_of_commV hρH hρs hcomm)

theorem natSL_card_le (hZB : Nat.card (Z1A (muF2 n)) = 2 * Nat.card (B1A (muF2 n)))
    (hK : Nat.card K = 2) (hW2 : ∀ w : W, w ^ 2 = 1) (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : (FFModel.nat (StatedSL n K)).Realizes H ⊤ Z) : Nat.card Z ≤ 2 := by
  obtain ⟨ρ, β, hρH, hρs, hβs, hβk, hβe⟩ := natSL_data hK h
  exact card_le_two_of_card_Z1A (μ := fun g : SpecialLinearGroup (Fin n) (ZMod 2) =>
    (g : Matrix (Fin n) (Fin n) (ZMod 2)))
    (θ := invTransposeSL n (ZMod 2)) muF2_invTranspose hZB hW2 hβs hβk
    (fun g z hz => hZ hz _ (hρH g)) hβe (mem_closure_of_commV hρH hρs hcomm)

end Cover

theorem binaryNaturalSL_four_eq_bot
    {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (h : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 4 1) : fixV L ⊓ commV L = ⊥ := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  exact eq_bot_of_restrict _ (fun W _ _ hW2 H Z hZ hcomm hRW =>
    natSL_eq_bot Z1A_eq_B1A_four (by simpa using hK) hW2 hZ hcomm hRW) hV2 hI hR

theorem binaryNaturalSL_five_eq_bot
    {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (h : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 5 1) : fixV L ⊓ commV L = ⊥ := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  exact eq_bot_of_restrict _ (fun W _ _ hW2 H Z hZ hcomm hRW =>
    natSL_eq_bot Z1A_eq_B1A_five (by simpa using hK) hW2 hZ hcomm hRW) hV2 hI hR

theorem binaryNaturalSL_three_card_le
    {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (h : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1) :
    Nat.card ↥(fixV L ⊓ commV L) ≤ 2 := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  exact card_le_of_restrict _ (fun W _ _ hW2 H Z hZ hcomm hRW =>
    natSL_card_le card_Z1A_three (by simpa using hK) hW2 hZ hcomm hRW) hV2 hI hR

end CFSG.Quasithin.H13.VolI
