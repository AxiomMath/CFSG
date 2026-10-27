module

public import CFSG.Quasithin.MS93.M15Cover
public import CFSG.Quasithin.MS93.M15Quot
public import CFSG.Quasithin.Vol2.Ch3B513NG2C
public import CFSG.Quasithin.H13.VolIAltCoverG2

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B513N

section Bound

variable {W : Type} [CommGroup W] [Finite W]

theorem card_le_of_zornQ_realizesVia (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W))
    (U Z : Subgroup W) (hZU : Z ≤ U) (hZfix : ∀ z ∈ Z, ∀ x ∈ L, x z = z)
    (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    {π : ↥(quasithinG2 K) →* ↥L} (hπ : (FFModel.zornQ (quasithinG2 K)).RealizesVia L U Z π) :
    Nat.card ↥Z ≤ 2 ^ n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Finite ↥(quasithinG2 K) := by
    have : Finite (quasithinZorn K ≃ₗ[K] quasithinZorn K) := inferInstance
    exact Subtype.finite
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hΓ := (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le
  obtain ⟨β, hβs, hβk, hβe⟩ := g2_coord hΓ hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(quasithinG2 K)) hexp L U Z hZU hZfix hinv
    hcomm π hπ.1 (g2Rep K hΓ) β hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [finrank_H1_dual_g2Rep K hK hn] at hcard

end Bound

section Gen

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem zmk_sub' (r u₀ u₁ u₂ v₀ v₁ v₂ s r' u₀' u₁' u₂' v₀' v₁' v₂' s' : F) :
    zmk r u₀ u₁ u₂ v₀ v₁ v₂ s - zmk r' u₀' u₁' u₂' v₀' v₁' v₂' s' =
      zmk (r - r') (u₀ - u₀') (u₁ - u₁') (u₂ - u₂') (v₀ - v₀') (v₁ - v₁') (v₂ - v₂') (s - s') := by
  simp [zmk]

@[expose] def g2Xq (a : Fin 3 → F) : ↥(quasithinG2 F) :=
  ⟨(g2X a : ↥(Explicit.cayleyGroup F)), by
    rw [G11.P3G2.quasithinG2_eq_cayleyGroup]; exact (g2X a).2⟩

@[expose] def g2Yq (b : Fin 3 → F) : ↥(quasithinG2 F) :=
  ⟨(g2Y b : ↥(Explicit.cayleyGroup F)), by
    rw [G11.P3G2.quasithinG2_eq_cayleyGroup]; exact (g2Y b).2⟩

theorem zornAct_g2Xq_comm (a : Fin 3 → F) (v₀ v₁ v₂ : F) :
    zornAct (quasithinG2 F) (g2Xq a) (Multiplicative.ofAdd (zmk 0 0 0 0 v₀ v₁ v₂ 0)) *
        (Multiplicative.ofAdd (zmk 0 0 0 0 v₀ v₁ v₂ 0))⁻¹ =
      Multiplicative.ofAdd (zmk (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)
        ((a 0 * v₀ + a 1 * v₁ + a 2 * v₂) * a 0) ((a 0 * v₀ + a 1 * v₁ + a 2 * v₂) * a 1)
        ((a 0 * v₀ + a 1 * v₁ + a 2 * v₂) * a 2) 0 0 0 (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
  show xaFun a (zmk 0 0 0 0 v₀ v₁ v₂ 0) + -zmk 0 0 0 0 v₀ v₁ v₂ 0 = _
  rw [xaFun_zmk, ← sub_eq_add_neg, zmk_sub']
  apply zmk_congr <;> ring

theorem zornAct_g2Yq_comm (b : Fin 3 → F) (u₀ u₁ u₂ : F) :
    zornAct (quasithinG2 F) (g2Yq b) (Multiplicative.ofAdd (zmk 0 u₀ u₁ u₂ 0 0 0 0)) *
        (Multiplicative.ofAdd (zmk 0 u₀ u₁ u₂ 0 0 0 0))⁻¹ =
      Multiplicative.ofAdd (zmk (b 0 * u₀ + b 1 * u₁ + b 2 * u₂) 0 0 0
        ((b 0 * u₀ + b 1 * u₁ + b 2 * u₂) * b 0) ((b 0 * u₀ + b 1 * u₁ + b 2 * u₂) * b 1)
        ((b 0 * u₀ + b 1 * u₁ + b 2 * u₂) * b 2) (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
  show ybFun b (zmk 0 u₀ u₁ u₂ 0 0 0 0) + -zmk 0 u₀ u₁ u₂ 0 0 0 0 = _
  rw [ybFun_zmk, ← sub_eq_add_neg, zmk_sub']
  apply zmk_congr <;> ring

theorem zornO0_gen_g2 (m : Multiplicative (quasithinZorn F)) (hm : m ∈ zornO0 F) :
    m ∈ Subgroup.closure {x | ∃ γ : ↥(quasithinG2 F), ∃ y ∈ zornO0 F,
      x = zornAct (quasithinG2 F) γ y * y⁻¹} := by
  set G := Subgroup.closure {x | ∃ γ : ↥(quasithinG2 F), ∃ y ∈ zornO0 F,
      x = zornAct (quasithinG2 F) γ y * y⁻¹} with hG
  have hO : ∀ r u₀ u₁ u₂ v₀ v₁ v₂ s : F, r + s = 0 →
      Multiplicative.ofAdd (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) ∈ zornO0 F := by
    intro r u₀ u₁ u₂ v₀ v₁ v₂ s h
    exact h
  have hx : ∀ (a : Fin 3 → F) (v₀ v₁ v₂ : F),
      Multiplicative.ofAdd (zmk (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)
        ((a 0 * v₀ + a 1 * v₁ + a 2 * v₂) * a 0) ((a 0 * v₀ + a 1 * v₁ + a 2 * v₂) * a 1)
        ((a 0 * v₀ + a 1 * v₁ + a 2 * v₂) * a 2) 0 0 0 (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) ∈ G := by
    intro a v₀ v₁ v₂
    rw [← zornAct_g2Xq_comm]
    exact Subgroup.subset_closure ⟨g2Xq a, _, hO _ _ _ _ _ _ _ _ (by ring), rfl⟩
  have hy : ∀ (b : Fin 3 → F) (u₀ u₁ u₂ : F),
      Multiplicative.ofAdd (zmk (b 0 * u₀ + b 1 * u₁ + b 2 * u₂) 0 0 0
        ((b 0 * u₀ + b 1 * u₁ + b 2 * u₂) * b 0) ((b 0 * u₀ + b 1 * u₁ + b 2 * u₂) * b 1)
        ((b 0 * u₀ + b 1 * u₁ + b 2 * u₂) * b 2) (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) ∈ G := by
    intro b u₀ u₁ u₂
    rw [← zornAct_g2Yq_comm]
    exact Subgroup.subset_closure ⟨g2Yq b, _, hO _ _ _ _ _ _ _ _ (by ring), rfl⟩
  have hsub : ∀ {p q : quasithinZorn F}, Multiplicative.ofAdd p ∈ G →
      Multiplicative.ofAdd q ∈ G → Multiplicative.ofAdd (p - q) ∈ G := by
    intro p q hp hq
    have := G.mul_mem hp (G.inv_mem hq)
    rwa [← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg] at this
  have hadd : ∀ {p q : quasithinZorn F}, Multiplicative.ofAdd p ∈ G →
      Multiplicative.ofAdd q ∈ G → Multiplicative.ofAdd (p + q) ∈ G := by
    intro p q hp hq
    have := G.mul_mem hp hq
    rwa [← ofAdd_add] at this
  have e0 : ∀ t : F, Multiplicative.ofAdd (zmk t t 0 0 0 0 0 t) ∈ G := fun t => by
    have := hx ![1, 0, 0] t 0 0
    simpa using this
  have e01 : ∀ t : F, Multiplicative.ofAdd (zmk t t t 0 0 0 0 t) ∈ G := fun t => by
    have := hx ![1, 1, 0] t 0 0
    simpa using this
  have e02 : ∀ t : F, Multiplicative.ofAdd (zmk t t 0 t 0 0 0 t) ∈ G := fun t => by
    have := hx ![1, 0, 1] t 0 0
    simpa using this
  have e1 : ∀ t : F, Multiplicative.ofAdd (zmk t 0 t 0 0 0 0 t) ∈ G := fun t => by
    have := hx ![0, 1, 0] 0 t 0
    simpa using this
  have e10 : ∀ t : F, Multiplicative.ofAdd (zmk t t t 0 0 0 0 t) ∈ G := fun t => by
    have := hx ![1, 1, 0] 0 t 0
    simpa using this
  have f0 : ∀ t : F, Multiplicative.ofAdd (zmk t 0 0 0 t 0 0 t) ∈ G := fun t => by
    have := hy ![1, 0, 0] t 0 0
    simpa using this
  have f01 : ∀ t : F, Multiplicative.ofAdd (zmk t 0 0 0 t t 0 t) ∈ G := fun t => by
    have := hy ![1, 1, 0] t 0 0
    simpa using this
  have f02 : ∀ t : F, Multiplicative.ofAdd (zmk t 0 0 0 t 0 t t) ∈ G := fun t => by
    have := hy ![1, 0, 1] t 0 0
    simpa using this
  have bU1 : ∀ t : F, Multiplicative.ofAdd (zmk 0 0 t 0 0 0 0 0) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (e01 t) (e0 t)
  have bU2 : ∀ t : F, Multiplicative.ofAdd (zmk 0 0 0 t 0 0 0 0) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (e02 t) (e0 t)
  have bU0 : ∀ t : F, Multiplicative.ofAdd (zmk 0 t 0 0 0 0 0 0) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (e10 t) (e1 t)
  have bR : ∀ t : F, Multiplicative.ofAdd (zmk t 0 0 0 0 0 0 t) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (e0 t) (bU0 t)
  have bV0 : ∀ t : F, Multiplicative.ofAdd (zmk 0 0 0 0 t 0 0 0) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (f0 t) (bR t)
  have bV1 : ∀ t : F, Multiplicative.ofAdd (zmk 0 0 0 0 0 t 0 0) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (f01 t) (f0 t)
  have bV2 : ∀ t : F, Multiplicative.ofAdd (zmk 0 0 0 0 0 0 t 0) ∈ G := fun t => by
    simpa [zmk_sub'] using hsub (f02 t) (f0 t)
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective m
  have hx0 : x.1 + x.2.2.2 = 0 := hm
  rw [zorn_eta x]
  have hs : x.2.2.2 = x.1 := by
    exact (CharTwo.add_eq_zero.1 hx0).symm
  have e : zmk x.1 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2) x.2.2.2 =
      zmk x.1 0 0 0 0 0 0 x.1 + zmk 0 (x.2.1 0) 0 0 0 0 0 0 + zmk 0 0 (x.2.1 1) 0 0 0 0 0 +
        zmk 0 0 0 (x.2.1 2) 0 0 0 0 + zmk 0 0 0 0 (x.2.2.1 0) 0 0 0 +
        zmk 0 0 0 0 0 (x.2.2.1 1) 0 0 + zmk 0 0 0 0 0 0 (x.2.2.1 2) 0 := by
    simp only [zmk_add, add_zero, zero_add, hs]
  rw [e]
  exact hadd (hadd (hadd (hadd (hadd (hadd (bR _) (bU0 _)) (bU1 _)) (bU2 _)) (bV0 _)) (bV1 _))
    (bV2 _)

end Gen

section Case

theorem card_zornR' (F : Type) [Field F] : Nat.card ↥(zornR F) = Nat.card F := by
  have e : F ≃ ↥(zornR F) :=
    { toFun := fun c => ⟨Multiplicative.ofAdd (c, 0, 0, c), ⟨c, rfl⟩⟩
      invFun := fun x => (Multiplicative.toAdd x.1).1
      left_inv := fun _ => rfl
      right_inv := fun x => by
        obtain ⟨y, c, hc⟩ := x
        apply Subtype.ext
        show Multiplicative.ofAdd ((Multiplicative.toAdd y).1, 0, 0,
          (Multiplicative.toAdd y).1) = y
        rw [hc]
        exact Multiplicative.toAdd.injective hc.symm }
  exact (Nat.card_congr e).symm

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem g2_case_large (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K) {n : ℕ} (hn : 2 ≤ n)
    (hG : G2Natural K ⊤ (fixV K) n) :
    Nat.card (fixV K) ≤ 2 ^ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ Z ≤ zornR F, (zornWeylQuot (quasithinG2 F) Z).Realizes K ⊤ ⊥ := by
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := hG
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hcomm : XMod.commOf ↥K (⊤ : Subgroup V) = ⊤ := (xmodCommOf_top_eq K).trans h.comm
  refine ⟨card_le_of_zornQ_realizesVia hV K ⊤ (fixV K) le_top (fun z hz x hx => hz x hx)
    (fun _ _ _ _ => Subgroup.mem_top _) hcomm hn hF hπ, F, iF, fF, hF, ?_⟩
  have hD := FFModel.zornQ_isActionModel (quasithinG2 F) le_rfl
  have : Finite (FFModel.zornQ (quasithinG2 F)).Amb :=
    (inferInstance : Finite (Multiplicative (quasithinZorn F)))
  have : Finite ↥(FFModel.zornQ (quasithinG2 F)).sec := Subtype.finite
  have hkfix : ∀ (γ : ↥(quasithinG2 F)), ∀ m ∈ zornR F, zornAct (quasithinG2 F) γ m = m := by
    rintro γ m ⟨c, hc⟩
    show Multiplicative.ofAdd ((γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
      (Multiplicative.toAdd m)) = m
    rw [hc, (mem_quasithinG2_isZornAuto γ.2).map_smul_one c, ← hc]
    rfl
  have hE2 : ∀ m ∈ zornO0 F, m ^ 2 = 1 := by
    intro m _
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_smul]
  have hRc : Nat.card ↥((zornR F).subgroupOf (zornO0 F)) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe zornR_le_zornO0).toEquiv, card_zornR', hF]
  obtain ⟨N, hN, hR⟩ := exists_quotBy_of_realizes hD hkfix (fun m hm => zornO0_gen_g2 m hm)
    hE2 (fun W _ _ hW L Z π' hreal hZ hcommL =>
      le_trans (card_le_of_zornQ_realizesVia hW L ⊤ Z le_top (fun z hz x hx => hZ hz x hx)
        (fun _ _ _ _ => Subgroup.mem_top _) hcommL hn hF hreal) (le_of_eq hRc.symm))
    hV (fun z hz => hz) h.comm ⟨π, hπ⟩
  exact ⟨N, hN, hR⟩

theorem g2_case_two
    (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K)
    (hG : G2NaturalDerived K ⊤ (fixV K) 1) :
    Nat.card (fixV K) = 2 ∧ Nat.card V = 2 ^ 7 ∧ H13.G2WeylDerived K := by
  rcases H13.VolI.g2NaturalCover_holds V hV K (fixV K) le_rfl h.comm hG with h0 | h2
  · exact absurd h0 h.fix_ne
  · exact h2

end Case

end CFSG.Quasithin.MS93
