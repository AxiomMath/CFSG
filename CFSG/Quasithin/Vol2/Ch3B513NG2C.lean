module

public import CFSG.Quasithin.Vol2.Ch3B513NSelfDual
public import CFSG.Quasithin.Background.SmithB51G2DKey
public import CFSG.Quasithin.Background.F918D0

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.JonesParshall CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Rep

variable (K : Type) [Field K] [CharP K 2]

noncomputable local instance algZ2G : Algebra (ZMod 2) K := ZMod.algebra K 2

@[expose] noncomputable def g2Rep {Γ₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hΓ : Γ₀ ≤ Explicit.cayleyGroup K) : Representation (ZMod 2) ↥Γ₀ (Ix3 → K) where
  toFun γ := (B5.G2D.g2Lin (Subgroup.inclusion hΓ γ)).restrictScalars (ZMod 2)
  map_one' := LinearMap.ext fun w => by
    show g2Act (Subgroup.inclusion hΓ 1) w = w
    rw [map_one]
    exact B5.G2D.g2Act_one_apply w
  map_mul' γ δ := LinearMap.ext fun w => by
    show g2Act (Subgroup.inclusion hΓ (γ * δ)) w =
      g2Act (Subgroup.inclusion hΓ γ) (g2Act (Subgroup.inclusion hΓ δ) w)
    rw [map_mul]
    exact B5.G2D.g2Act_mul_apply _ _ w

theorem finrank_H1_dual_g2Rep [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    Module.finrank (ZMod 2) (H1 (Representation.dual
      (g2Rep K (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le))) = n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : Finite ↥(quasithinG2 K) := by
    have : Finite (quasithinZorn K ≃ₗ[K] quasithinZorn K) := inferInstance
    exact Subtype.finite
  have : Finite (Module.Dual (ZMod 2) (Ix3 → K)) := by
    have : Module.Finite (ZMod 2) (Ix3 → K) := Module.Finite.of_finite
    exact Module.finite_of_finite (ZMod 2)
  apply finrank_H1_of_card
  rw [card_H1_dual_of_selfDual K (g2Rep K (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le)
    B5.G2D.bilQLin (fun u hu => B5.G2D.eq_zero_of_bilQ hu)
    (fun γ u x => bilQ_g2Act _ u x)
    (MulEquiv.subgroupCongr (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K))) g2Act
    (fun γ x => rfl) (card_Z1A_g2Act hF (by omega)), hF]

end Rep

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem g2_coord {K : Type} [Field K] [CharP K 2]
    {Γ₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (hΓ : Γ₀ ≤ Explicit.cayleyGroup K)
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {π : ↥Γ₀ →* ↥L}
    (h : (FFModel.zornQ Γ₀).RealizesVia L U Z π) :
    ∃ β : ↥U →* Multiplicative (Ix3 → K), Function.Surjective β ∧
      (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : ↥Γ₀) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
        β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (g2Act (Subgroup.inclusion hΓ γ) (Multiplicative.toAdd (β u))) := by
  obtain ⟨-, -, -, -, -, hsec, -, β₀, hβs, hβk, hβe⟩ := h
  let e := zornSecEquiv (F := K) Γ₀
  refine ⟨e.toMonoidHom.comp β₀, e.surjective.comp hβs, fun u => ?_, fun γ u hu => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hβk]
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hm0 : (FFModel.zornQ Γ₀).act γ m.1 ∈ (FFModel.zornQ Γ₀).sec := hsec γ _ m.2
    have h1 := hβe γ u m hu hm0 hm.symm
    refine (congrArg e h1).trans ?_
    show _ = Multiplicative.ofAdd (g2Act (Subgroup.inclusion hΓ γ)
      (Multiplicative.toAdd (e (β₀ u))))
    rw [← hm]
    change Multiplicative.ofAdd (zP ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd (show Multiplicative (quasithinZorn K) from m.1)))) =
      Multiplicative.ofAdd (zP ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (zI (zP (Multiplicative.toAdd (show Multiplicative (quasithinZorn K) from m.1))))))
    exact congrArg Multiplicative.ofAdd (g2_zP_apply (Subgroup.inclusion hΓ γ) _ m.2)

theorem card_fixV_le_of_g2 (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (U : Subgroup W)
    (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hreal : (FFModel.zornQ (quasithinG2 K)).Realizes L U (fixV L ⊓ U)) :
    Nat.card ↥(fixV L ⊓ U) ≤ 2 ^ n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Finite ↥(quasithinG2 K) := by
    have : Finite (quasithinZorn K ≃ₗ[K] quasithinZorn K) := inferInstance
    exact Subtype.finite
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  have hΓ := (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le
  obtain ⟨β, hβs, hβk, hβe⟩ := g2_coord hΓ hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(quasithinG2 K)) hexp L U (fixV L ⊓ U)
    inf_le_right (fun z hz x hx => mem_fixV.1 hz.1 x hx) hinv hcomm π hπ.1 (g2Rep K hΓ) β
    hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [finrank_H1_dual_g2Rep K hK hn] at hcard

end CFSG.Quasithin.B513N
