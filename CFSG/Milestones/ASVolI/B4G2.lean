module

public import CFSG.Milestones.ASVolI.B4
public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.Quasithin.MS93.M15G2Off
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.GH74.GLS.Stage4.HexModelG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base13
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel
public import CFSG.Sporadic.Recognition.LyonsAS44Frattini
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ASVolI

open CFSG.Open

section Base

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8

structure burnsideB46_Hyp (V : Type) [CommGroup V] (n : ℕ) (K : Type) [Field K]
    (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
    (θ : V →* Multiplicative (NatQ K)) : Prop where
  exp2 : ∀ v : V, v ^ 2 = 1
  one_le : 1 ≤ n
  card : Nat.card K = 2 ^ n
  inj : Function.Injective π
  range : π.range = L
  le : L ≤ G
  fstar : quasithinGenFitting G = layerOf L
  comm : commV (layerOf L) = ⊤
  surj : Function.Surjective θ
  ker : θ.ker = fixV L
  equiv : ∀ (γ : ↥(quasithinG2 K)) (v : V), θ ((π γ) v) = Multiplicative.ofAdd
    (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)))

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_charP [Finite K] (H : burnsideB46_Hyp V n K G L π θ) : CharP K 2 :=
  charP_two_of_card (by have := H.one_le; omega) H.card

@[expose] def burnsideB46_ix (x : NatQ K) : Ix3 → K := Sum.elim x.1 x.2

@[expose] def burnsideB46_nat (w : Ix3 → K) : NatQ K :=
  (fun i => w (Sum.inl i), fun i => w (Sum.inr i))

theorem burnsideB46_ix_nat (w : Ix3 → K) : burnsideB46_ix (burnsideB46_nat w) = w := by
  funext i
  rcases i with i | i <;> rfl

theorem burnsideB46_nat_ix (x : NatQ K) : burnsideB46_nat (burnsideB46_ix x) = x := rfl

theorem burnsideB46_ix_injective : Function.Injective (burnsideB46_ix (K := K)) := fun x y h => by
  rw [← burnsideB46_nat_ix x, ← burnsideB46_nat_ix y, h]

theorem burnsideB46_ix_add (x y : NatQ K) :
    burnsideB46_ix (x + y) = burnsideB46_ix x + burnsideB46_ix y := by
  funext i
  rcases i with i | i <;> rfl

theorem burnsideB46_ix_smul (c : K) (x : NatQ K) :
    burnsideB46_ix (c • x) = c • burnsideB46_ix x := by
  funext i
  rcases i with i | i <;> rfl

theorem burnsideB46_ix_zero : burnsideB46_ix (0 : NatQ K) = 0 := by
  funext i
  rcases i with i | i <;> rfl

@[expose] def burnsideB46_cg [CharP K 2] : ↥(quasithinG2 K) ≃* ↥(cayleyGroup K) :=
  MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup

theorem burnsideB46_cg_coe [CharP K 2] (γ : ↥(quasithinG2 K)) :
    ((burnsideB46_cg γ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) =
      (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) := rfl

theorem burnsideB46_ix_qAct [CharP K 2] (γ : ↥(quasithinG2 K)) (x : NatQ K) :
    burnsideB46_ix (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x) =
      g2Act (burnsideB46_cg γ) (burnsideB46_ix x) := by
  have h1 : zI (burnsideB46_ix x) = ((0 : K), x.1, x.2, (0 : K)) := by
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  have h2 : cgE (burnsideB46_cg γ) = (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) := rfl
  rw [g2Act_apply, h2, h1]
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem burnsideB46_mem_L (H : burnsideB46_Hyp V n K G L π θ) {l : MulAut V} :
    l ∈ L ↔ ∃ γ : ↥(quasithinG2 K), π γ = l := by
  rw [← H.range]
  exact MonoidHom.mem_range

theorem burnsideB46_theta_act (H : burnsideB46_Hyp V n K G L π θ) (γ : ↥(quasithinG2 K)) (v : V) :
    Multiplicative.toAdd (θ ((π γ) v)) =
      qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)) := by
  rw [H.equiv]
  rfl

theorem burnsideB46_part_2 [Finite K] (H : burnsideB46_Hyp V n K G L π θ) :
    ∀ v w : V, θ v ≠ 1 → θ w ≠ 1 → ∃ l ∈ L, θ (l v) = θ w := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro v w hv hw
  have hx : burnsideB46_ix (Multiplicative.toAdd (θ v)) ≠ 0 := by
    intro h
    apply hv
    have h1 : Multiplicative.toAdd (θ v) = 0 :=
      burnsideB46_ix_injective (h.trans burnsideB46_ix_zero.symm)
    exact h1
  have hy : burnsideB46_ix (Multiplicative.toAdd (θ w)) ≠ 0 := by
    intro h
    apply hw
    have h1 : Multiplicative.toAdd (θ w) = 0 :=
      burnsideB46_ix_injective (h.trans burnsideB46_ix_zero.symm)
    exact h1
  obtain ⟨g₁, hg₁⟩ := exists_g2Act_eu_eq hx
  obtain ⟨g₂, hg₂⟩ := exists_g2Act_eu_eq hy
  let γ : ↥(cayleyGroup K) := g₂ * g₁⁻¹
  have hγ : g2Act γ (burnsideB46_ix (Multiplicative.toAdd (θ v))) =
      burnsideB46_ix (Multiplicative.toAdd (θ w)) := by
    rw [← hg₁, ← hg₂]
    change g2Act (g₂ * g₁⁻¹) (g2Act g₁ (eu 0 1)) = g2Act g₂ (eu 0 1)
    rw [← g2Act_mul_apply, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨π (burnsideB46_cg.symm γ), (burnsideB46_mem_L H).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [burnsideB46_theta_act H]
  apply burnsideB46_ix_injective
  rw [burnsideB46_ix_qAct, MulEquiv.apply_symm_apply, hγ]

theorem burnsideB46_nat_add (w w' : Ix3 → K) :
    burnsideB46_nat (w + w') = burnsideB46_nat w + burnsideB46_nat w' := rfl

theorem burnsideB46_nat_zero : burnsideB46_nat (0 : Ix3 → K) = 0 := rfl

theorem burnsideB46_nat_smul (c : K) (w : Ix3 → K) :
    burnsideB46_nat (c • w) = c • burnsideB46_nat w := rfl

theorem burnsideB46_part_1a [Finite K] (H : burnsideB46_Hyp V n K G L π θ) :
    ∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
      (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
        ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x) := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro ψ hψ
  let φ : NatQ K → NatQ K := fun y => Multiplicative.toAdd (ψ (Multiplicative.ofAdd y))
  have hφ : ∀ y, ψ (Multiplicative.ofAdd y) = Multiplicative.ofAdd (φ y) := fun y => rfl
  let T : (Ix3 → K) →+ (Ix3 → K) :=
    { toFun := fun w => burnsideB46_ix (φ (burnsideB46_nat w))
      map_zero' := by
        have h : φ (burnsideB46_nat (0 : Ix3 → K)) = 0 := by
          change Multiplicative.toAdd (ψ 1) = 0
          rw [map_one]
          rfl
        rw [h]
        exact burnsideB46_ix_zero
      map_add' := fun w w' => by
        have h : φ (burnsideB46_nat (w + w')) = φ (burnsideB46_nat w) + φ (burnsideB46_nat w') := by
          change Multiplicative.toAdd (ψ (Multiplicative.ofAdd _)) = _
          rw [burnsideB46_nat_add, ofAdd_add, map_mul, toAdd_mul]
        rw [h, burnsideB46_ix_add] }
  have hT : ∀ w, T w = burnsideB46_ix (φ (burnsideB46_nat w)) := fun w => rfl
  have hcomm : ∀ (g : ↥(cayleyGroup K)) (x : Ix3 → K), T (g2Act g x) = g2Act g (T x) := by
    intro g x
    obtain ⟨v, hv⟩ := H.surj (Multiplicative.ofAdd (burnsideB46_nat x))
    obtain ⟨w, hw⟩ := H.surj (ψ (θ v))
    have h1 := hψ (π (burnsideB46_cg.symm g)) ((burnsideB46_mem_L H).2 ⟨_, rfl⟩) v w hw.symm
    have e1 : θ ((π (burnsideB46_cg.symm g)) v) = Multiplicative.ofAdd
        (burnsideB46_nat (g2Act g x)) := by
      apply Multiplicative.toAdd.injective
      rw [burnsideB46_theta_act H, hv]
      apply burnsideB46_ix_injective
      rw [burnsideB46_ix_qAct, MulEquiv.apply_symm_apply]
      simp only [toAdd_ofAdd, burnsideB46_ix_nat]
    have e2 : θ ((π (burnsideB46_cg.symm g)) w) = Multiplicative.ofAdd
        (burnsideB46_nat (g2Act g (T x))) := by
      apply Multiplicative.toAdd.injective
      rw [burnsideB46_theta_act H, hw, hv]
      apply burnsideB46_ix_injective
      rw [burnsideB46_ix_qAct, MulEquiv.apply_symm_apply]
      simp only [toAdd_ofAdd, burnsideB46_ix_nat]
      rfl
    rw [e1, e2, hφ] at h1
    have h2 : φ (burnsideB46_nat (g2Act g x)) = burnsideB46_nat (g2Act g (T x)) :=
      Multiplicative.ofAdd.injective h1
    rw [hT, h2, burnsideB46_ix_nat]
  obtain ⟨c, hc⟩ := commutant_cayley T hcomm
  refine ⟨c, fun x => ?_⟩
  have h3 := hc (burnsideB46_ix (Multiplicative.toAdd x))
  rw [hT, burnsideB46_nat_ix, ← burnsideB46_ix_smul] at h3
  have h4 : φ (Multiplicative.toAdd x) = c • Multiplicative.toAdd x :=
    burnsideB46_ix_injective h3
  rw [← h4]
  exact (hφ _).trans (by rw [ofAdd_toAdd]) |>.symm ▸ rfl

theorem burnsideB46_qAct_smul (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (c : K) (x : NatQ K) :
    qAct γ (c • x) = c • qAct γ x := by
  have h : ((0 : K), (c • x).1, (c • x).2, (0 : K)) = c • ((0 : K), x.1, x.2, (0 : K)) := by
    refine Prod.ext (by simp) (Prod.ext rfl (Prod.ext rfl (by simp)))
  unfold qAct
  rw [h, map_smul]
  rfl

theorem burnsideB46_part_1b (H : burnsideB46_Hyp V n K G L π θ) :
    ∀ (c : K), ∀ l ∈ L, ∀ v w : V,
      θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
        θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v))) := by
  intro c l hl v w hw
  obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L H).1 hl
  apply Multiplicative.toAdd.injective
  rw [burnsideB46_theta_act H, hw, toAdd_ofAdd, burnsideB46_qAct_smul, toAdd_ofAdd,
    burnsideB46_theta_act H]

@[expose] def burnsideB46_O0Equiv [CharP K 2] : ↥(zornO0 K) ≃* Multiplicative (WeylM K) where
  toFun m := Multiplicative.ofAdd
    ((Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1,
      (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.1,
      (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.2.1)
  invFun w := ⟨Multiplicative.ofAdd ((Multiplicative.toAdd w).1, (Multiplicative.toAdd w).2.1,
      (Multiplicative.toAdd w).2.2, (Multiplicative.toAdd w).1), by
    change (Multiplicative.toAdd w).1 + (Multiplicative.toAdd w).1 = 0
    exact CharTwo.add_self_eq_zero _⟩
  left_inv m := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    have h : (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1 +
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.2.2 = 0 := m.2
    have h2 : (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.2.2 =
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1 := by
      rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl h2.symm))
  right_inv w := rfl
  map_mul' x y := rfl

theorem burnsideB46_card_O0 [CharP K 2] : Nat.card ↥(zornO0 K) = Nat.card K ^ 7 := by
  rw [Nat.card_congr (burnsideB46_O0Equiv (K := K)).toEquiv]
  change Nat.card (K × (Fin 3 → K) × (Fin 3 → K)) = _
  rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

theorem burnsideB46_layerOf_le (X : Subgroup (MulAut V)) : layerOf X ≤ X :=
  sSup_le fun _ hK => hK.1

theorem burnsideB46_commV_L (H : burnsideB46_Hyp V n K G L π θ) : commV L = ⊤ :=
  top_le_iff.mp (H.comm ▸ commV_mono (burnsideB46_layerOf_le L))

@[expose] noncomputable def burnsideB46_ixMul : Multiplicative (NatQ K) →* Multiplicative (Ix3 → K) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.mk' burnsideB46_ix burnsideB46_ix_add)

theorem burnsideB46_ixMul_apply (x : Multiplicative (NatQ K)) :
    burnsideB46_ixMul x = Multiplicative.ofAdd (burnsideB46_ix (Multiplicative.toAdd x)) := rfl

theorem burnsideB46_ixMul_injective : Function.Injective (burnsideB46_ixMul (K := K)) :=
  fun x y h => Multiplicative.toAdd.injective
    (burnsideB46_ix_injective (Multiplicative.ofAdd.injective h))

theorem burnsideB46_ixMul_surjective : Function.Surjective (burnsideB46_ixMul (K := K)) :=
  fun y => ⟨Multiplicative.ofAdd (burnsideB46_nat (Multiplicative.toAdd y)), by
    rw [burnsideB46_ixMul_apply, toAdd_ofAdd, burnsideB46_ix_nat, ofAdd_toAdd]⟩

theorem burnsideB46_ixMul_act [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (γ : ↥(quasithinG2 K)) (v : V) :
    Multiplicative.toAdd (burnsideB46_ixMul (θ ((π γ) v))) =
      zornLin (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd (burnsideB46_ixMul (θ v))) := by
  rw [burnsideB46_ixMul_apply, toAdd_ofAdd, burnsideB46_theta_act H, burnsideB46_ix_qAct,
    burnsideB46_ixMul_apply, toAdd_ofAdd]
  rfl

open CFSG.Quasithin.MS93 CFSG.Quasithin.H13.VolI in
noncomputable def burnsideB46_cover [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) :
    ModelCover (FFModel.zornQ (quasithinG2 K)) V where
  ρ := π
  β := (zornSecEquiv (quasithinG2 K)).symm.toMonoidHom.comp (burnsideB46_ixMul.comp θ)
  surj := (zornSecEquiv (quasithinG2 K)).symm.surjective.comp
    (burnsideB46_ixMul_surjective.comp H.surj)
  fix := by
    intro γ v hv
    have h1 : burnsideB46_ixMul (θ v) = 1 := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hv
      exact hv
    have h2 : θ v = 1 := burnsideB46_ixMul_injective (h1.trans (map_one _).symm)
    have h3 : v ∈ fixV L := H.ker ▸ (MonoidHom.mem_ker.2 h2)
    exact mem_fixV.1 h3 (π γ) ((burnsideB46_mem_L H).2 ⟨γ, rfl⟩)
  equiv := by
    intro γ v m hm hvm
    have hΓ : quasithinG2 K ≤ cayleyGroup K :=
      (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).le
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq] at hvm ⊢
    have h1 := (linModelZorn (quasithinG2 K) hΓ).e_act γ m hm
    apply Multiplicative.toAdd.injective
    have h2 : Multiplicative.toAdd ((zornSecEquiv (quasithinG2 K))
        (QuotientGroup.mk (⟨(FFModel.zornQ (quasithinG2 K)).act γ ↑m, hm⟩ :
          ↥(FFModel.zornQ (quasithinG2 K)).sec))) =
        zornLin ((show ↥(quasithinG2 K) from γ) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
          (Multiplicative.toAdd ((zornSecEquiv (quasithinG2 K)) (QuotientGroup.mk m))) := h1
    rw [h2, ← hvm]
    exact burnsideB46_ixMul_act H γ v
  gen := by
    intro v
    have hv : v ∈ commV L := by rw [burnsideB46_commV_L H]; trivial
    refine (Subgroup.closure_mono ?_) hv
    rintro _ ⟨x, hx, w, rfl⟩
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L H).1 hx
    exact ⟨γ, w, rfl⟩

open CFSG.Quasithin.MS93 CFSG.Quasithin.H13.VolI in
theorem burnsideB46_weyl [CharP K 2] [Finite K] [Finite V] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    ∃ ψ : ↥(zornO0 K) →* V, Function.Surjective ψ ∧
      (∀ m, ψ m = 1 → (m : Multiplicative (quasithinZorn K)) ∈ zornR K) ∧
      (∀ (γ : ↥(quasithinG2 K)) (m m' : ↥(zornO0 K)),
        (m' : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m →
          ψ m' = π γ (ψ m)) ∧
      ∀ m, Multiplicative.toAdd (θ (ψ m)) =
        burnsideB46_nat (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) := by
  have hD := FFModel.zornQ_isActionModel (quasithinG2 K) (le_refl _)
  have : Finite (FFModel.zornQ (quasithinG2 K)).Amb :=
    (inferInstance : Finite (Multiplicative (quasithinZorn K)))
  have : Finite ↥(FFModel.zornQ (quasithinG2 K)).sec := Subtype.finite
  have hkfix : ∀ (γ : ↥(quasithinG2 K)), ∀ m ∈ zornR K, zornAct (quasithinG2 K) γ m = m := by
    rintro γ m ⟨c, hc⟩
    show Multiplicative.ofAdd ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd m)) = m
    rw [hc, (mem_quasithinG2_isZornAuto γ.2).map_smul_one c, ← hc]
    rfl
  have hE2 : ∀ m ∈ zornO0 K, m ^ 2 = 1 := by
    intro m _
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_smul]
  have hRc : Nat.card ↥((zornR K).subgroupOf (zornO0 K)) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe zornR_le_zornO0).toEquiv, card_zornR', H.card]
  set D := FFModel.zornQ (quasithinG2 K) with hDdef
  have hkfix' : ∀ γ (m : ↥D.sec), (m : D.Amb) ∈ D.ker → secAut hD γ m = m :=
    fun γ m hm => Subtype.ext (hkfix γ m.1 hm)
  have hgen' : ∀ m : ↥D.sec, m ∈ Subgroup.closure {x | ∃ γ y, x = secAut hD γ y * y⁻¹} := by
    intro m
    have hle : Subgroup.closure {x | ∃ γ, ∃ y ∈ D.sec, x = D.act γ y * y⁻¹} ≤
        (Subgroup.closure {x : ↥D.sec | ∃ γ y, x = secAut hD γ y * y⁻¹}).map D.sec.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨γ, y, hy, rfl⟩
      exact ⟨secAut hD γ ⟨y, hy⟩ * ⟨y, hy⟩⁻¹, Subgroup.subset_closure ⟨γ, ⟨y, hy⟩, rfl⟩, rfl⟩
    obtain ⟨m', hm', hmm'⟩ := hle (zornO0_gen_g2 m.1 m.2)
    rwa [show m' = m from Subtype.ext hmm'] at hm'
  have hE2' : ∀ m : ↥D.sec, m ^ 2 = 1 := fun m =>
    Subtype.ext (hE2 m.1 m.2)
  have hbound' : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ C : ModelCover D W, Nat.card C.β.ker ≤ Nat.card ↥(D.ker.subgroupOf D.sec) := by
    intro W _ _ hW C
    exact le_trans (card_le_of_zornQ_realizesVia hW C.ρ.range ⊤ C.β.ker le_top
      (fun z hz x hx => by
        obtain ⟨γ, rfl⟩ := hx
        exact C.fix γ z (MonoidHom.mem_ker.1 hz))
      (fun _ _ _ _ => Subgroup.mem_top _) (ModelCover.commOf_range C) hn H.card
      (ModelCover.realizesVia_range hD C)) (le_of_eq hRc.symm)
  obtain ⟨ψ, hψs, hψk, hψe, hψβ⟩ := ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl)
    hkfix' hgen' hE2' hbound' H.exp2 (burnsideB46_cover H)
  refine ⟨ψ, hψs, hψk, fun γ m m' hm' => ?_, fun m => ?_⟩
  · have h1 : m' = secAut hD γ m := Subtype.ext hm'
    have h2 := hψe γ m
    rw [h1]
    exact h2
  · have h1 := hψβ m
    have h2 : burnsideB46_ixMul (θ (ψ m)) = (zornSecEquiv (quasithinG2 K)) (QuotientGroup.mk m) := by
      have h3 : (zornSecEquiv (quasithinG2 K)).symm (burnsideB46_ixMul (θ (ψ m))) =
          QuotientGroup.mk m := h1
      exact (zornSecEquiv (quasithinG2 K)).symm_apply_eq.1 h3
    have h4 : (zornSecEquiv (quasithinG2 K)) (QuotientGroup.mk m) =
        Multiplicative.ofAdd (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) := rfl
    rw [h4, burnsideB46_ixMul_apply] at h2
    have h5 : burnsideB46_ix (Multiplicative.toAdd (θ (ψ m))) =
        zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) :=
      Multiplicative.ofAdd.injective h2
    rw [← h5, burnsideB46_nat_ix]
    rfl

theorem burnsideB46_O0Equiv_act [CharP K 2] (γ : ↥(quasithinG2 K)) (m m' : ↥(zornO0 K))
    (h : (m' : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m) :
    burnsideB46_O0Equiv m' = Multiplicative.ofAdd
      (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd (burnsideB46_O0Equiv m))) := by
  have hm : Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)) =
      ((Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1,
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.1,
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.2.1,
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1) :=
    congrArg (fun x : ↥(zornO0 K) => Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)))
      (burnsideB46_O0Equiv.symm_apply_apply m).symm
  have h' : Multiplicative.toAdd (m' : Multiplicative (quasithinZorn K)) =
      (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) :=
    congrArg Multiplicative.toAdd h
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  show ((Multiplicative.toAdd (m' : Multiplicative (quasithinZorn K))).1,
    (Multiplicative.toAdd (m' : Multiplicative (quasithinZorn K))).2.1,
    (Multiplicative.toAdd (m' : Multiplicative (quasithinZorn K))).2.2.1) =
    weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      ((Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1,
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.1,
        (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.2.1)
  unfold weylAct
  simp only []
  rw [← hm, h']

theorem burnsideB46_part_1c_ge2 [Finite K] [Finite V] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) : Nat.card V ≤ 2 ^ (7 * n) := by
  haveI : CharP K 2 := burnsideB46_charP H
  obtain ⟨ψ, hψs, -⟩ := burnsideB46_weyl H hn
  have h1 : Nat.card V ≤ Nat.card ↥(zornO0 K) := Nat.card_le_card_of_surjective ψ hψs
  rw [burnsideB46_card_O0, H.card, ← pow_mul, mul_comm] at h1
  exact h1

theorem burnsideB46_part_1d_ge2 [Finite K] [Finite V] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
      ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
        (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))) := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro hcard
  obtain ⟨ψ, hψs, hψk, hψe, -⟩ := burnsideB46_weyl H hn
  have hD := FFModel.zornQ_isActionModel (quasithinG2 K) (le_refl _)
  have hc : Nat.card ↥(zornO0 K) ≤ Nat.card V := by
    rw [burnsideB46_card_O0, H.card, ← pow_mul, mul_comm, hcard]
  have hbij : Function.Bijective ψ := hψs.bijective_of_nat_card_le hc
  refine ⟨(MulEquiv.ofBijective ψ hbij).symm.trans burnsideB46_O0Equiv, fun γ v => ?_⟩
  obtain ⟨m, rfl⟩ := hψs v
  let m' : ↥(zornO0 K) := ⟨zornAct (quasithinG2 K) γ m, hD.sec_inv γ m.1 m.2⟩
  have h1 : ψ m' = π γ (ψ m) := hψe γ m m' rfl
  have e1 : (MulEquiv.ofBijective ψ hbij).symm (ψ m) = m :=
    (MulEquiv.ofBijective ψ hbij).symm_apply_apply m
  have e2 : (MulEquiv.ofBijective ψ hbij).symm (π γ (ψ m)) = m' := by
    rw [← h1]
    exact (MulEquiv.ofBijective ψ hbij).symm_apply_apply m'
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1, e2]
  exact burnsideB46_O0Equiv_act γ m m' rfl

theorem burnsideB46_mem_cPre {C : Subgroup V} {Z : Subgroup (MulAut V)} {v : V} :
    v ∈ cPre C Z ↔ ∀ z ∈ Z, (z : MulAut V) v * v⁻¹ ∈ C := by
  simp [cPre, Subgroup.mem_iInf]

theorem burnsideB46_fix_lift [CharP K 2] (γ : ↥(cayleyGroup K)) (x : quasithinZorn K)
    (hx : cayleyTr x = 0) (h : g2Act γ (zP x) = zP x) : cgE γ x = x := by
  have h1 : zP (cgE γ x) = zP x := by
    rw [← h, g2_zP_apply γ x hx]
    rfl
  have hγ : cayleyTr (cgE γ x) = 0 := by rw [cg_tr, hx]
  have e1 := trace_zero_eq hx
  have e2 := trace_zero_eq hγ
  rw [h1] at e2
  have e3 : cgE γ x - x = ((cgE γ x).1 - x.1) • cayleyOne K := by
    calc cgE γ x - x = (zI (zP x) + (cgE γ x).1 • cayleyOne K) - (zI (zP x) + x.1 • cayleyOne K) := by
          rw [← e2, ← e1]
      _ = ((cgE γ x).1 - x.1) • cayleyOne K := by rw [sub_smul]; abel
  have e4 : cgE γ x - x = zmk ((cgE γ x).1 - x.1) 0 0 0 0 0 0 ((cgE γ x).1 - x.1) := by
    rw [e3, cayleyOne_eq, zmk_smul]
    apply zmk_congr <;> ring
  have e5 := CFSG.Quasithin.MS93.comm_eq_zero_of_mem_R γ hx e4
  rw [e5, zmk_zero] at e4
  exact sub_eq_zero.mp e4

theorem burnsideB46_lift_fix_ge2 [Finite K] [Finite V] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) {l : MulAut V} (hl : l ∈ L) {v : V} (h : l v * v⁻¹ ∈ fixV L) : l v = v := by
  haveI : CharP K 2 := burnsideB46_charP H
  obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L H).1 hl
  obtain ⟨ψ, hψs, -, hψe, hψθ⟩ := burnsideB46_weyl H hn
  obtain ⟨m, rfl⟩ := hψs v
  have h1 : θ ((π γ) (ψ m) * (ψ m)⁻¹) = 1 := by
    have : (π γ) (ψ m) * (ψ m)⁻¹ ∈ θ.ker := by rw [H.ker]; exact h
    exact MonoidHom.mem_ker.1 this
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  rw [burnsideB46_theta_act H, hψθ] at h2
  have h3 : g2Act (burnsideB46_cg γ) (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) =
      zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) := by
    have h4 := congrArg burnsideB46_ix h2
    rw [burnsideB46_ix_qAct, burnsideB46_ix_nat] at h4
    simpa [burnsideB46_ix_nat] using h4
  have hm0 : cayleyTr (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) = 0 := m.2
  have h5 := burnsideB46_fix_lift (burnsideB46_cg γ) _ hm0 h3
  have h6 : (m : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m := by
    apply Multiplicative.toAdd.injective
    exact h5.symm
  have h7 := hψe γ m m h6
  exact h7.symm

theorem burnsideB46_part_7_ge2 [Finite K] [Finite V] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    ∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L := by
  intro i hi _ _
  apply le_antisymm
  · intro v hv
    have h := (burnsideB46_mem_cPre.1 hv) i (Subgroup.mem_zpowers i)
    have h2 := burnsideB46_lift_fix_ge2 H hn hi h
    exact Subgroup.mem_sup_left (mem_fixV_zpowers_iff_apply.2 h2)
  · refine sup_le ?_ ?_
    · intro v hv
      rw [burnsideB46_mem_cPre]
      intro z hz
      rw [mem_fixV.1 hv z hz, mul_inv_cancel]
      exact one_mem _
    · intro v hv
      rw [burnsideB46_mem_cPre]
      intro z hz
      rw [mem_fixV.1 hv z ((Subgroup.zpowers_le.2 hi) hz), mul_inv_cancel]
      exact one_mem _

theorem burnsideB46_shortRootFn_eq [CharP K 2] (t : K) (x : quasithinZorn K) :
    shortRootFn t x = xaFun ![t, 0, 0] x := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [zorn_eta x, xaFun_zmk]
  obtain ⟨r, u, v, s⟩ := x
  simp only [shortRootFn, zmk]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp
  · funext i
    fin_cases i
    · simp [Pi.single_apply]
      ring
    · simp [Pi.single_apply]
    · simp [Pi.single_apply]
  · funext i
    fin_cases i
    · simp [Pi.single_apply, Matrix.vecHead, Matrix.vecTail]
    · simp [Pi.single_apply, Matrix.vecHead, Matrix.vecTail]
      linear_combination (t * u 2) * h2
    · simp [Pi.single_apply, Matrix.vecHead, Matrix.vecTail]
  · simp

theorem burnsideB46_shortRoot_mem [CharP K 2] (t : K) :
    ∃ φ : ↥(quasithinG2 K), ∀ x, (φ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = shortRootFn t x :=
  ⟨burnsideB46_cg.symm (g2X ![t, 0, 0]), fun x => by
    rw [burnsideB46_shortRootFn_eq, ← g2X_apply]
    rfl⟩

@[expose] def burnsideB46_av (c : K) : ↥(zornO0 K) :=
  ⟨Multiplicative.ofAdd ((0 : K), (0 : Fin 3 → K), (Pi.single 0 c : Fin 3 → K), (0 : K)), by
    change (0 : K) + 0 = 0
    exact add_zero 0⟩

theorem burnsideB46_comm_psi {ψ : ↥(zornO0 K) →* V} {φ : ↥(quasithinG2 K)} {m m' : ↥(zornO0 K)}
    (hψe : ∀ (γ : ↥(quasithinG2 K)) (m m' : ↥(zornO0 K)),
      (m' : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m →
        ψ m' = π γ (ψ m))
    (h : (m' : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) φ m) :
    (π φ) (ψ m) * (ψ m)⁻¹ = ψ (m' * m⁻¹) := by
  rw [map_mul, map_inv, hψe φ m m' h]

theorem burnsideB46_part8_id [CharP K 2] (φ₁ φ₂ : ↥(quasithinG2 K)) (t c₁ : K)
    (h₁ : ∀ x, (φ₁ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = shortRootFn t x)
    (h₂ : ∀ x, (φ₂ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = shortRootFn 1 x) :
    Multiplicative.toAdd (zornAct (quasithinG2 K) φ₁ (burnsideB46_av c₁ : Multiplicative (quasithinZorn K))) -
      Multiplicative.toAdd (burnsideB46_av c₁ : Multiplicative (quasithinZorn K)) -
      (Multiplicative.toAdd (zornAct (quasithinG2 K) φ₂
          (burnsideB46_av (t ^ 2 * c₁) : Multiplicative (quasithinZorn K))) -
        Multiplicative.toAdd (burnsideB46_av (t ^ 2 * c₁) : Multiplicative (quasithinZorn K))) =
      (t * c₁ + t ^ 2 * c₁, (0 : Fin 3 → K), (0 : Fin 3 → K), t * c₁ + t ^ 2 * c₁) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  change (φ₁ : quasithinZorn K ≃ₗ[K] quasithinZorn K) _ - _ - ((φ₂ : quasithinZorn K ≃ₗ[K] quasithinZorn K) _ - _) = _
  rw [h₁, h₂]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [shortRootFn, burnsideB46_av, Pi.single_apply]
    linear_combination (-(t ^ 2 * c₁)) * h2
  · funext i
    fin_cases i <;> simp [shortRootFn, burnsideB46_av, Pi.single_apply, Matrix.vecHead, Matrix.vecTail]
  · funext i
    fin_cases i <;> simp [shortRootFn, burnsideB46_av, Pi.single_apply, Matrix.vecHead, Matrix.vecTail]
  · simp [shortRootFn, burnsideB46_av, Pi.single_apply]
    linear_combination (-(t ^ 2 * c₁)) * h2

theorem burnsideB46_conj_gen {R : Subgroup (MulAut V)} (a b : MulAut V) (hab : a * b * a⁻¹ ∈ R)
    (v : V) : a (b v * v⁻¹) ∈ commV R := by
  refine Subgroup.subset_closure ⟨a * b * a⁻¹, hab, a v, ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, map_mul,
    map_inv]

theorem burnsideB46_part_8_ge2 [Finite K] [Finite V] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro _ R hR w hw
  obtain ⟨g, hg⟩ := hR
  obtain ⟨ψ, hψs, -, hψe, hψθ⟩ := burnsideB46_weyl H hn
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one (K := K) (CFSG.Quasithin.B42G2.two_lt_card H.card hn)
  obtain ⟨φ₁, hφ₁⟩ := burnsideB46_shortRoot_mem (K := K) t
  obtain ⟨φ₂, hφ₂⟩ := burnsideB46_shortRoot_mem (K := K) 1
  have hD := FFModel.zornQ_isActionModel (quasithinG2 K) (le_refl _)
  have hgL : π g ∈ L := (burnsideB46_mem_L H).2 ⟨g, rfl⟩
  have hwg : π g w = w := mem_fixV.1 hw (π g) hgL
  obtain ⟨m, rfl⟩ := hψs w
  have hθ : θ (ψ m) = 1 := by
    have : ψ m ∈ θ.ker := by rw [H.ker]; exact hw
    exact MonoidHom.mem_ker.1 this
  set x := Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)) with hx
  have hzP : zP x = 0 := by
    have h0 : burnsideB46_nat (zP x) = 0 := by rw [← hψθ m, hθ]; rfl
    rw [← burnsideB46_ix_nat (zP x), h0, burnsideB46_ix_zero]
  have hu : x.2.1 = 0 := by
    funext i
    have := congrFun hzP (Sum.inl i)
    fin_cases i <;> simpa [zP, q6] using this
  have hv : x.2.2.1 = 0 := by
    funext i
    have := congrFun hzP (Sum.inr i)
    fin_cases i <;> simpa [zP, q6] using this
  have hs : x.2.2.2 = x.1 := by
    have h : x.1 + x.2.2.2 = 0 := m.2
    rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
  have hxc : x = (x.1, 0, 0, x.1) := Prod.ext rfl (Prod.ext hu (Prod.ext hv hs))
  have ht1' : t + 1 ≠ 0 := by
    intro h
    apply ht1
    have : t = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]
  set c₁ : K := x.1 / (t * (t + 1)) with hc₁
  have hc₁' : t * c₁ + t ^ 2 * c₁ = x.1 := by
    rw [hc₁]
    field_simp
    ring
  have hRmem : ∀ (φ : ↥(quasithinG2 K)) (t' : K),
      (∀ y, (φ : quasithinZorn K ≃ₗ[K] quasithinZorn K) y = shortRootFn t' y) →
        π g * π φ * (π g)⁻¹ ∈ R := fun φ t' h => (hg _).2 ⟨t', φ, h, rfl⟩
  let m₁ : ↥(zornO0 K) := burnsideB46_av c₁
  let m₂ : ↥(zornO0 K) := burnsideB46_av (t ^ 2 * c₁)
  let m₁' : ↥(zornO0 K) := ⟨zornAct (quasithinG2 K) φ₁ m₁, hD.sec_inv φ₁ m₁.1 m₁.2⟩
  let m₂' : ↥(zornO0 K) := ⟨zornAct (quasithinG2 K) φ₂ m₂, hD.sec_inv φ₂ m₂.1 m₂.2⟩
  have e₁ : (π φ₁) (ψ m₁) * (ψ m₁)⁻¹ = ψ (m₁' * m₁⁻¹) := burnsideB46_comm_psi hψe rfl
  have e₂ : (π φ₂) (ψ m₂) * (ψ m₂)⁻¹ = ψ (m₂' * m₂⁻¹) := burnsideB46_comm_psi hψe rfl
  have hid : m = (m₁' * m₁⁻¹) * (m₂' * m₂⁻¹)⁻¹ := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    have key := burnsideB46_part8_id φ₁ φ₂ t c₁ hφ₁ hφ₂
    rw [hc₁'] at key
    calc Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)) = x := hx.symm
      _ = (x.1, 0, 0, x.1) := hxc
      _ = _ := key.symm
      _ = _ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv]
        abel
  have hw' : ψ m = ((π φ₁) (ψ m₁) * (ψ m₁)⁻¹) * ((π φ₂) (ψ m₂) * (ψ m₂)⁻¹)⁻¹ := by
    rw [e₁, e₂, ← map_inv, ← map_mul, ← hid]
  rw [← hwg, hw', map_mul, map_inv]
  exact Subgroup.mul_mem _ (burnsideB46_conj_gen (π g) (π φ₁) (hRmem φ₁ t hφ₁) (ψ m₁))
    (Subgroup.inv_mem _ (burnsideB46_conj_gen (π g) (π φ₂) (hRmem φ₂ 1 hφ₂) (ψ m₂)))

@[expose] def burnsideB46_G2Qs : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    CFSG.Open.IsQuasisimple ↥(quasithinG2 K)

theorem burnsideB46_layerOf_eq [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) : layerOf L = L := by
  refine le_antisymm (burnsideB46_layerOf_le L) ?_
  have e : ↥(quasithinG2 K) ≃* ↥L :=
    (MonoidHom.ofInjective H.inj).trans (MulEquiv.subgroupCongr H.range)
  have hq : CFSG.Open.IsQuasisimple ↥L := CFSG.Open.IsQuasisimple.of_mulEquiv e.symm (hqs K n hn H.card)
  exact le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl L, hq⟩

theorem burnsideB46_normal [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  intro g hg l hl
  have h1 := le_normalizer_quasithinGenFitting G hg
  rw [H.fstar, burnsideB46_layerOf_eq hqs H hn] at h1
  exact (Subgroup.mem_normalizer_iff.mp h1 l).mp hl

end Base

section Cert

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.Vol2.KGNat CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint

theorem burnsideB46_G2Qs_of_cert
    : burnsideB46_G2Qs := by
  intro K _ _ n hn hK
  have hCharP : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K)
    (by rw [hK]; calc 2 < 2 ^ 2 := by norm_num
                       _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have h2 : IsG2 2 n (↥(quasithinG2 K) ⧸ Subgroup.center ↥(quasithinG2 K)) :=
    CFSG.Quasithin.factG2Cayley_holds K n hn hK
  obtain ⟨-, F, _, hFfin, hF, ⟨e⟩⟩ := h2
  have hF3 : 3 ≤ Nat.card F := by
    rw [hF]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI hs : IsSimpleGroup (AdjointQuotient .G2 F) := isSimpleGroup_g2Model hF3
  refine ⟨?_, e.isSimpleGroup⟩
  have hder : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := g2Derived_eq hc0 hc1
  have hq : quasithinG2 K = cayleyGroup K :=
    CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup
  have hD : (commutator ↥(quasithinG2 K)).map (quasithinG2 K).subtype =
      ⁅quasithinG2 K, quasithinG2 K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hder, ← hq] at hD
  rw [eq_top_iff]
  intro x _
  have hx : (x : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
      (commutator ↥(quasithinG2 K)).map (quasithinG2 K).subtype := by
    rw [hD]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  exact (Subtype.ext hyx) ▸ hy

end Cert

section R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

@[expose] noncomputable def burnsideB46_pi [CharP K 2] (π : ↥(quasithinG2 K) →* MulAut V) :
    ↥(cayleyGroup K) →* MulAut V :=
  π.comp burnsideB46_cg.symm.toMonoidHom

theorem burnsideB46_pi_apply [CharP K 2] (g : ↥(cayleyGroup K)) :
    burnsideB46_pi π g = π (burnsideB46_cg.symm g) := rfl

theorem burnsideB46_pi_injective [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) :
    Function.Injective (burnsideB46_pi π) :=
  H.inj.comp burnsideB46_cg.symm.injective

theorem burnsideB46_pi_mem_L [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (g : ↥(cayleyGroup K)) : burnsideB46_pi π g ∈ L :=
  (burnsideB46_mem_L H).2 ⟨_, rfl⟩

theorem burnsideB46_mem_L' [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) {l : MulAut V} :
    l ∈ L ↔ ∃ g : ↥(cayleyGroup K), burnsideB46_pi π g = l := by
  rw [burnsideB46_mem_L H]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨burnsideB46_cg γ, by simp [burnsideB46_pi_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, rfl⟩

@[expose] noncomputable def burnsideB46_f (θ : V →* Multiplicative (NatQ K)) (v : V) : Ix3 → K :=
  burnsideB46_ix (Multiplicative.toAdd (θ v))

theorem burnsideB46_f_mul (v w : V) :
    burnsideB46_f θ (v * w) = burnsideB46_f θ v + burnsideB46_f θ w := by
  unfold burnsideB46_f
  rw [map_mul, toAdd_mul, burnsideB46_ix_add]

theorem burnsideB46_f_one : burnsideB46_f θ (1 : V) = 0 := by
  unfold burnsideB46_f
  rw [map_one, toAdd_one, burnsideB46_ix_zero]

theorem burnsideB46_f_inv (v : V) : burnsideB46_f θ v⁻¹ = - burnsideB46_f θ v := by
  have h := burnsideB46_f_mul (θ := θ) v v⁻¹
  rw [mul_inv_cancel, burnsideB46_f_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem burnsideB46_f_surj (H : burnsideB46_Hyp V n K G L π θ) :
    Function.Surjective (burnsideB46_f θ) := by
  intro w
  obtain ⟨v, hv⟩ := H.surj (Multiplicative.ofAdd (burnsideB46_nat w))
  refine ⟨v, ?_⟩
  unfold burnsideB46_f
  rw [hv, toAdd_ofAdd, burnsideB46_ix_nat]

theorem burnsideB46_f_eq_zero_iff (H : burnsideB46_Hyp V n K G L π θ) (v : V) :
    burnsideB46_f θ v = 0 ↔ v ∈ fixV L := by
  rw [← H.ker, MonoidHom.mem_ker]
  unfold burnsideB46_f
  constructor
  · intro h
    have h1 : Multiplicative.toAdd (θ v) = 0 :=
      burnsideB46_ix_injective (h.trans burnsideB46_ix_zero.symm)
    exact h1
  · intro h
    rw [h]
    exact burnsideB46_ix_zero.trans rfl

theorem burnsideB46_f_act [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (g : ↥(cayleyGroup K)) (v : V) :
    burnsideB46_f θ ((burnsideB46_pi π g) v) = g2Act g (burnsideB46_f θ v) := by
  unfold burnsideB46_f
  rw [burnsideB46_pi_apply, burnsideB46_theta_act H, burnsideB46_ix_qAct,
    MulEquiv.apply_symm_apply]

theorem burnsideB46_f_sub (v w : V) :
    burnsideB46_f θ (v * w⁻¹) = burnsideB46_f θ v - burnsideB46_f θ w := by
  rw [burnsideB46_f_mul, burnsideB46_f_inv, sub_eq_add_neg]

@[expose] noncomputable def burnsideB46_pre (θ : V →* Multiplicative (NatQ K))
    (S : Submodule K (Ix3 → K)) : Subgroup V where
  carrier := {v | burnsideB46_f θ v ∈ S}
  one_mem' := by
    change burnsideB46_f θ (1 : V) ∈ S
    rw [burnsideB46_f_one]
    exact S.zero_mem
  mul_mem' := fun {a b} ha hb => by
    change burnsideB46_f θ (a * b) ∈ S
    rw [burnsideB46_f_mul]
    exact S.add_mem ha hb
  inv_mem' := fun {a} ha => by
    change burnsideB46_f θ a⁻¹ ∈ S
    rw [burnsideB46_f_inv]
    exact S.neg_mem ha

theorem burnsideB46_mem_pre {S : Submodule K (Ix3 → K)} {v : V} :
    v ∈ burnsideB46_pre θ S ↔ burnsideB46_f θ v ∈ S := Iff.rfl

@[expose] noncomputable def burnsideB46_ixLin : NatQ K ≃ₗ[K] (Ix3 → K) where
  toFun := burnsideB46_ix
  map_add' := burnsideB46_ix_add
  map_smul' := burnsideB46_ix_smul
  invFun := burnsideB46_nat
  left_inv := burnsideB46_nat_ix
  right_inv := burnsideB46_ix_nat

theorem burnsideB46_ixLin_apply (x : NatQ K) : burnsideB46_ixLin x = burnsideB46_ix x := rfl

theorem burnsideB46_isFPre_iff {d : ℕ} {X : Subgroup V} :
    IsFPre θ d X ↔ ∃ S : Submodule K (Ix3 → K), Module.finrank K S = d ∧ X = burnsideB46_pre θ S := by
  constructor
  · rintro ⟨S, hS, hX⟩
    refine ⟨S.map (burnsideB46_ixLin (K := K) : NatQ K →ₗ[K] (Ix3 → K)), ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact hS
    · ext v
      rw [hX v, burnsideB46_mem_pre]
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨y, hy, hyv⟩
        have : y = Multiplicative.toAdd (θ v) := burnsideB46_ix_injective hyv
        rwa [← this]
  · rintro ⟨S, hS, hX⟩
    refine ⟨S.comap (burnsideB46_ixLin (K := K) : NatQ K →ₗ[K] (Ix3 → K)), ?_, ?_⟩
    · rw [← hS]
      exact LinearEquiv.finrank_eq (burnsideB46_ixLin.ofSubmodule' S)
    · intro v
      rw [hX, burnsideB46_mem_pre]
      rfl

theorem burnsideB46_pre_map_ker (H : burnsideB46_Hyp V n K G L π θ) (S : Submodule K (Ix3 → K)) :
    fixV L ≤ burnsideB46_pre θ S := fun v hv => by
  rw [burnsideB46_mem_pre, (burnsideB46_f_eq_zero_iff H v).2 hv]
  exact S.zero_mem

theorem burnsideB46_stab_pre [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (S : Submodule K (Ix3 → K)) :
    L ⊓ stabSub (burnsideB46_pre θ S) = (stabQ S).map (burnsideB46_pi π) := by
  have key : ∀ g : ↥(cayleyGroup K),
      burnsideB46_pi π g ∈ stabSub (burnsideB46_pre θ S) ↔ g ∈ stabQ S := by
    intro g
    change (∀ u : V, (burnsideB46_pi π g) u ∈ burnsideB46_pre θ S ↔ u ∈ burnsideB46_pre θ S) ↔
      ∀ w, w ∈ S ↔ g2Act g w ∈ S
    simp only [burnsideB46_mem_pre, burnsideB46_f_act H]
    constructor
    · intro h w
      obtain ⟨u, rfl⟩ := burnsideB46_f_surj H w
      exact (h u).symm
    · intro h u
      exact (h (burnsideB46_f θ u)).symm
  ext l
  constructor
  · rintro ⟨hl, hs⟩
    obtain ⟨g, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    exact ⟨g, (key g).1 hs, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨burnsideB46_pi_mem_L H g, (key g).2 hg⟩

theorem burnsideB46_cPre_map [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (X : Subgroup ↥(cayleyGroup K)) :
    cPre (fixV L) (X.map (burnsideB46_pi π)) = burnsideB46_pre θ (fixSub X) := by
  ext v
  rw [burnsideB46_mem_cPre, burnsideB46_mem_pre]
  constructor
  · intro h γ hγ
    have h1 := h (burnsideB46_pi π γ) ⟨γ, hγ, rfl⟩
    have h2 := (burnsideB46_f_eq_zero_iff H _).2 h1
    rw [burnsideB46_f_sub, burnsideB46_f_act H, sub_eq_zero] at h2
    exact h2
  · intro h z hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    refine (burnsideB46_f_eq_zero_iff H _).1 ?_
    rw [burnsideB46_f_sub, burnsideB46_f_act H, sub_eq_zero]
    exact h γ hγ

section Transfer

variable {M N : Type*} [Group M] [Group N]

theorem burnsideB46_pCoreOf_map (φ : M →* N) (hφ : Function.Injective φ) (X : Subgroup M) :
    pCoreOf 2 (X.map φ) = (pCoreOf 2 X).map φ := by
  let e : ↥X ≃* ↥(X.map φ) := X.equivMapOfInjective φ hφ
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  have h2 : (X.map φ).subtype.comp e.toMonoidHom = φ.comp X.subtype := by
    ext x
    rfl
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem burnsideB46_centerOf_map (φ : M →* N) (hφ : Function.Injective φ) (X : Subgroup M) :
    centerOf (X.map φ) = (centerOf X).map φ := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro x' hx'
    have := hy (φ x') ⟨x', hx', rfl⟩
    exact hφ (by rw [map_mul, map_mul]; exact this)
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (hc x' hx')

end Transfer

end R

section GS

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_derived_eq [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (CFSG.Quasithin.B42G2.two_lt_card H.card hn)
  exact g2Derived_eq hc0 hc1

@[expose] noncomputable def burnsideB46_piDer (H : burnsideB46_Hyp V n K G L π θ) :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥L :=
  (π.comp (Subgroup.inclusion (Subgroup.commutator_le_self _))).codRestrict L
    (fun γ => (burnsideB46_mem_L H).2 ⟨_, rfl⟩)

theorem burnsideB46_isCoord [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    IsCoord (lmG K) L (fixV L) (burnsideB46_piDer H) (burnsideB46_f θ) := by
  have hder := burnsideB46_derived_eq H hn
  have hq : quasithinG2 K = cayleyGroup K :=
    CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)
  refine ⟨burnsideB46_f_mul, burnsideB46_f_eq_zero_iff H, burnsideB46_f_surj H, ?_, ?_⟩
  · intro γ u
    have h1 := burnsideB46_f_act H (burnsideB46_cg (Subgroup.inclusion (Subgroup.commutator_le_self _) γ)) u
    change burnsideB46_f θ ((π (Subgroup.inclusion (Subgroup.commutator_le_self _) γ)) u) = _
    simp only [burnsideB46_pi_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1]
    rfl
  · intro l
    obtain ⟨γ, hγ⟩ := (burnsideB46_mem_L H).1 l.2
    have hγ' : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ ⁅quasithinG2 K, quasithinG2 K⁆ := by
      rw [hder, ← hq]
      exact γ.2
    refine ⟨⟨γ, hγ'⟩, Subtype.ext ?_⟩
    exact hγ

theorem burnsideB46_scalar_eq_one [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {g : MulAut V} (hg : g ∈ G) {c : K}
    (hc : c ≠ 0) (hgc : ∀ v, burnsideB46_f θ (g v) = c • burnsideB46_f θ v) : g = 1 := by
  haveI : Finite (MulAut V) := Finite.of_injective (fun e : MulAut V => (e : V → V))
    (fun e e' h => MulEquiv.ext (congrFun h))
  have hginv : ∀ u, burnsideB46_f θ (g⁻¹ u) = c⁻¹ • burnsideB46_f θ u := by
    intro u
    have h1 := hgc (g⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hcomm : ∀ l ∈ L, l * g = g * l := by
    intro l hl
    have hgl : g * l * g⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem (burnsideB46_normal hqs H hn g hg l hl) (L.inv_mem hl)
    obtain ⟨δ, hδ⟩ := (burnsideB46_mem_L' H).1 hgl
    obtain ⟨η, hη⟩ := (burnsideB46_mem_L' H).1 hl
    have h1 : ∀ w, g2Act δ w = w := by
      intro w
      obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
      rw [← burnsideB46_f_act H δ v, hδ, ← hη]
      have e1 : burnsideB46_f θ ((burnsideB46_pi π η)⁻¹ v) = g2Act η⁻¹ (burnsideB46_f θ v) := by
        rw [← map_inv, burnsideB46_f_act H]
      calc burnsideB46_f θ ((g * burnsideB46_pi π η * g⁻¹ * (burnsideB46_pi π η)⁻¹) v)
          = c • burnsideB46_f θ ((burnsideB46_pi π η) (g⁻¹ ((burnsideB46_pi π η)⁻¹ v))) := hgc _
        _ = c • g2Act η (burnsideB46_f θ (g⁻¹ ((burnsideB46_pi π η)⁻¹ v))) := by
            rw [burnsideB46_f_act H]
        _ = c • g2Act η (c⁻¹ • burnsideB46_f θ ((burnsideB46_pi π η)⁻¹ v)) := by rw [hginv]
        _ = c • g2Act η (c⁻¹ • g2Act η⁻¹ (burnsideB46_f θ v)) := by rw [e1]
        _ = burnsideB46_f θ v := by
            rw [JonesParshall.g2Act_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, g2Act_apply_inv]
    have h2 : δ = 1 := cayley_eq_one h1
    rw [h2, map_one] at hδ
    have h3 : g * l * g⁻¹ = l := mul_inv_eq_one.1 hδ.symm
    calc l * g = g * l * g⁻¹ * g := by rw [h3]
      _ = g * l := by group
  have hfs : quasithinGenFitting G = L := H.fstar.trans (burnsideB46_layerOf_eq hqs H hn)
  have hgL : g ∈ L := by
    have hmem : g ∈ G ⊓ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) := by
      refine ⟨hg, ?_⟩
      rw [hfs]
      exact Subgroup.mem_centralizer_iff.mpr (fun h hh => hcomm h hh)
    have := centralizer_quasithinGenFitting_le G hmem
    rwa [hfs] at this
  obtain ⟨δ', rfl⟩ := (burnsideB46_mem_L' H).1 hgL
  have hcen : ∀ η : ↥(cayleyGroup K), η * δ' = δ' * η := by
    intro η
    have := hcomm (burnsideB46_pi π η) (burnsideB46_pi_mem_L H η)
    rw [← map_mul, ← map_mul] at this
    exact burnsideB46_pi_injective H this
  let T : (Ix3 → K) →+ (Ix3 → K) := g2Act δ'
  obtain ⟨c', hc'⟩ := commutant_cayley T (fun η x => by
    change g2Act δ' (g2Act η x) = g2Act η (g2Act δ' x)
    rw [← g2Act_mul_apply, ← g2Act_mul_apply, hcen η])
  have hc'1 : c' = 1 := scalar_eq_one (fun w => hc' w)
  have : δ' = 1 := cayley_eq_one (fun w => by rw [show g2Act δ' w = T w from rfl, hc', hc'1, one_smul])
  rw [this, map_one]

theorem burnsideB46_fixV_inv [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {g : MulAut V} (hg : g ∈ G) :
    ∀ z ∈ fixV L, g z ∈ fixV L := by
  intro z hz
  rw [mem_fixV] at hz ⊢
  intro l hl
  have h1 : g⁻¹ * l * g ∈ L := by
    simpa using burnsideB46_normal hqs H hn g⁻¹ (G.inv_mem hg) l hl
  calc l (g z) = g ((g⁻¹ * l * g) z) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = g z := by rw [hz _ h1]

theorem burnsideB46_G_semilinear [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {g : MulAut V} (hg : g ∈ G) :
    ∃ (c : K) (γ : ↥(cayleyGroup K)) (σ : K ≃+* K), c ≠ 0 ∧
      ∀ v, burnsideB46_f θ (g v) = c • g2Act γ (frobQ σ (burnsideB46_f θ v)) := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (CFSG.Quasithin.B42G2.two_lt_card H.card hn)
  have hnorm := burnsideB46_normal hqs H hn
  have hginv : g⁻¹ ∈ G := G.inv_mem hg
  exact exists_smul_frob_of_normalizes (burnsideB46_isCoord H hn) hc0 hc1 H.card hn g
    (burnsideB46_fixV_inv hqs H hn hg) (burnsideB46_fixV_inv hqs H hn hginv)
    (fun h hh => hnorm g hg h hh) (fun h hh => by simpa using hnorm g⁻¹ hginv h hh)

theorem burnsideB46_mem_L_of_fix [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {g : MulAut V} (hg : g ∈ G)
    {S : Submodule K (Ix3 → K)} (hS : S ≠ ⊥)
    (hfix : ∀ v, burnsideB46_f θ v ∈ S → burnsideB46_f θ (g v) = burnsideB46_f θ v) : g ∈ L := by
  obtain ⟨c, γ, σ, hc, hform⟩ := burnsideB46_G_semilinear hqs H hn hg
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  obtain ⟨vx, hvx⟩ := burnsideB46_f_surj H x
  have hgx : burnsideB46_f θ (g vx) = x := by rw [hfix vx (hvx ▸ hxS), hvx]
  have hgx' : c • g2Act γ (frobQ (σ : K →+* K) x) = x := by
    have := hform vx
    rw [hgx, hvx] at this
    exact this.symm
  have hσ : ∀ a : K, σ a = a := by
    intro a
    obtain ⟨va, hva⟩ := burnsideB46_f_surj H (a • x)
    have h1 : burnsideB46_f θ (g va) = a • x := by
      rw [hfix va (hva ▸ S.smul_mem a hxS), hva]
    have h2 : burnsideB46_f θ (g va) = σ a • x := by
      rw [hform va, hva, frobQ_smul, JonesParshall.g2Act_smul, smul_comm, hgx']
      rfl
    have h3 : σ a • x = a • x := h2.symm.trans h1
    exact (smul_left_injective K hx0) h3
  have hσ1 : σ = RingEquiv.refl K := RingEquiv.ext hσ
  have hform' : ∀ v, burnsideB46_f θ (g v) = c • g2Act γ (burnsideB46_f θ v) := by
    intro v
    rw [hform v, hσ1]
    rfl
  have hg'G : g * (burnsideB46_pi π γ)⁻¹ ∈ G :=
    G.mul_mem hg (G.inv_mem (H.le (burnsideB46_pi_mem_L H γ)))
  have hg'1 : g * (burnsideB46_pi π γ)⁻¹ = 1 := by
    refine burnsideB46_scalar_eq_one hqs H hn hg'G hc (fun v => ?_)
    rw [MulAut.mul_apply, hform', ← map_inv, burnsideB46_f_act H, g2Act_apply_inv]
  have : g = burnsideB46_pi π γ := mul_inv_eq_one.1 hg'1
  rw [this]
  exact burnsideB46_pi_mem_L H γ

end GS

section M

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

section Defs

variable (K : Type) [Field K] [CharP K 2]

@[expose] def burnsideB46_pt (x : Ix3 → K) : Submodule K (Ix3 → K) := Submodule.span K {x}

@[expose] def burnsideB46_P1 (x : Ix3 → K) : Subgroup ↥(cayleyGroup K) :=
  stabQ (burnsideB46_pt K x)

@[expose] def burnsideB46_R1 (x : Ix3 → K) : Subgroup ↥(cayleyGroup K) :=
  pCoreOf 2 (burnsideB46_P1 K x)

@[expose] def burnsideB46_Z1 (x : Ix3 → K) : Subgroup ↥(cayleyGroup K) :=
  centerOf (burnsideB46_R1 K x)

@[expose] noncomputable def burnsideB46_F3 (x : Ix3 → K) : Submodule K (Ix3 → K) :=
  fixSub (burnsideB46_Z1 K x)

@[expose] def burnsideB46_A1 (x : Ix3 → K) : Subgroup ↥(cayleyGroup K) where
  carrier := {γ | ∀ w ∈ burnsideB46_F3 K x, g2Act γ w = w}
  one_mem' := fun w _ => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb w hw => by rw [g2Act_mul_apply, hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    have h1 := congrArg (g2Act a⁻¹) (ha w hw)
    rwa [g2Act_inv_apply, eq_comm] at h1

end Defs

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_cfg1_point [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (h : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁) :
    ∃ x : Ix3 → K, x ≠ 0 ∧ V₁ = burnsideB46_pre θ (burnsideB46_pt K x) ∧
      P₁ = (burnsideB46_P1 K x).map (burnsideB46_pi π) ∧
      R₁ = (burnsideB46_R1 K x).map (burnsideB46_pi π) ∧
      Z₁ = (burnsideB46_Z1 K x).map (burnsideB46_pi π) ∧
      V₃ = burnsideB46_pre θ (burnsideB46_F3 K x) := by
  obtain ⟨hV₁, hP₁, hR₁, hZ₁, hV₃, -⟩ := h
  obtain ⟨S, hS, hV₁S⟩ := burnsideB46_isFPre_iff.1 hV₁
  obtain ⟨x, hx0, hSx⟩ : ∃ x : Ix3 → K, x ≠ 0 ∧ S = burnsideB46_pt K x := by
    obtain ⟨x, hx, hxS⟩ := (finrank_eq_one_iff'.1 hS)
    refine ⟨(x : Ix3 → K), fun h => hx (Subtype.ext h), ?_⟩
    ext w
    constructor
    · intro hw
      obtain ⟨c, hc⟩ := hxS ⟨w, hw⟩
      have : w = c • (x : Ix3 → K) := (congrArg Subtype.val hc).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · intro hw
      exact (Submodule.span_singleton_le_iff_mem _ _).2 x.2 hw
  have hV₁' : V₁ = burnsideB46_pre θ (burnsideB46_pt K x) := hSx ▸ hV₁S
  have hP : P₁ = (burnsideB46_P1 K x).map (burnsideB46_pi π) := by
    rw [hP₁, hV₁', burnsideB46_stab_pre H]
    rfl
  have hR : R₁ = (burnsideB46_R1 K x).map (burnsideB46_pi π) := by
    rw [hR₁, hP, burnsideB46_pCoreOf_map _ (burnsideB46_pi_injective H)]
    rfl
  have hZ : Z₁ = (burnsideB46_Z1 K x).map (burnsideB46_pi π) := by
    rw [hZ₁, hR, burnsideB46_centerOf_map _ (burnsideB46_pi_injective H)]
    rfl
  refine ⟨x, hx0, hV₁', hP, hR, hZ, ?_⟩
  rw [hV₃, hZ, burnsideB46_cPre_map H]
  rfl

theorem burnsideB46_cfg1_A1 [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {x : Ix3 → K}
    (hF3 : burnsideB46_F3 K x ≠ ⊥) {V₃ : Subgroup V} {A₁ : Subgroup (MulAut V)}
    (hV₃ : V₃ = burnsideB46_pre θ (burnsideB46_F3 K x))
    (hA : ∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) :
    A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) := by
  have key : ∀ (g : MulAut V), (∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K x → burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    intro g
    rw [hV₃]
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  ext g
  rw [hA]
  constructor
  · rintro ⟨hgG, hg⟩
    have hgL : g ∈ L := burnsideB46_mem_L_of_fix hqs H hn hgG hF3 ((key g).1 hg)
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hgL
    refine ⟨γ, fun w hw => ?_, rfl⟩
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
    rw [← burnsideB46_f_act H]
    exact (key _).1 hg v hw
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨H.le (burnsideB46_pi_mem_L H γ), (key _).2 fun v hv => ?_⟩
    rw [burnsideB46_f_act H]
    exact hγ _ hv

end M

section MP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_mp_exists_sq [Finite K] (x : K) : ∃ α : K, α * α = x := by
  have hinj : Function.Injective (fun α : K => α * α) := fun a b h => eq_of_mul_self_eq_charTwo h
  obtain ⟨α, hα⟩ := Finite.surjective_of_injective hinj x
  exact ⟨α, hα⟩

theorem burnsideB46_mp_mem_P {g : ↥(cayleyGroup K)} {c : K} (hc : c ≠ 0)
    (h : g2Act g (eu 0 1) = c • eu 0 1) : g ∈ stabQ (stdF K 1) := by
  refine mem_stabQ.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨t, rfl⟩ := mem_stdF_one_iff.mp hw
    rw [JonesParshall.g2Act_smul, h, smul_smul]
    exact mem_stdF_one_iff.mpr ⟨_, rfl⟩
  · have h1 := inv_smul_of_smul hc h
    obtain ⟨t, ht⟩ := mem_stdF_one_iff.mp hw
    have e : w = g2Act g⁻¹ (g2Act g w) := (g2Act_inv_apply g w).symm
    rw [e, ht, JonesParshall.g2Act_smul, h1, smul_smul]
    exact mem_stdF_one_iff.mpr ⟨_, rfl⟩

open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)


@[expose] def burnsideB46_mp_ke (α β γ p q' : K) : ↥(cayleyGroup K) :=
  g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)

theorem burnsideB46_mp_ke_mem (α β γ p q' : K) :
    burnsideB46_mp_ke α β γ p q' ∈ stabQ (stdF K 1) :=
  stabV0_le_stabQ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (g2X_e0_mem_stabV0 α)
    (g2Y_mem_stabV0 β γ)) (g2A_mem_stabV0 (uSL_mulVec_e0 p q' 0)))

theorem burnsideB46_mp_ke_apply (α β γ p q' a b c d e f : K) :
    g2Act (burnsideB46_mp_ke α β γ p q') (q6 a b c d e f) =
      q6 ((a + p * b + q' * c + β * (f + q' * d) + γ * (e + p * d)) + α * α * d)
        (b + γ * d) (c + β * d) d
        ((e + p * d + (β * b + γ * c) * β) + α * (c + β * d))
        ((f + q' * d + (β * b + γ * c) * γ) + α * (b + γ * d)) :=
  g2Act_kerElt α β γ p q' a b c d e f

theorem burnsideB46_mp_tv12 (t a b c d e f : K) :
    g2Act (g2A (tv 1 2 (by decide) t)) (q6 a b c d e f) =
      q6 a (b + t * c) c d e (f + t * e) := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6, eu, ev, Pi.single_apply]

theorem burnsideB46_mp_tv21 (t a b c d e f : K) :
    g2Act (g2A (tv 2 1 (by decide) t)) (q6 a b c d e f) =
      q6 a b (c + t * b) d (e + t * f) f := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6, eu, ev, Pi.single_apply]

theorem burnsideB46_mp_tv12_mem (t : K) : g2A (tv 1 2 (by decide) t) ∈ stabQ (stdF K 1) := by
  refine burnsideB46_mp_mem_P (c := 1) one_ne_zero ?_
  rw [eu_eq_q6, burnsideB46_mp_tv12, one_smul]
  simp

theorem burnsideB46_mp_tv21_mem (t : K) : g2A (tv 2 1 (by decide) t) ∈ stabQ (stdF K 1) := by
  refine burnsideB46_mp_mem_P (c := 1) one_ne_zero ?_
  rw [eu_eq_q6, burnsideB46_mp_tv21, one_smul]
  simp

theorem burnsideB46_mp_tG_mem (c : Kˣ) : tG c ∈ stabQ (stdF K 1) :=
  mem_stabQ.mpr fun w => (tG_mem_stab c w).symm

theorem burnsideB46_mp_to_r6 [Finite K] (a b c d e f : K) (hd : d ≠ 0) :
    ∃ p ∈ stabQ (stdF K 1), g2Act p (q6 a b c d e f) = q6 (0 : K) 0 0 1 0 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨a₁, b₁, c₁, e₁, f₁, h1⟩ : ∃ a₁ b₁ c₁ e₁ f₁ : K,
      g2Act (tG (Units.mk0 d hd)) (q6 a b c d e f) = q6 a₁ b₁ c₁ 1 e₁ f₁ :=
    ⟨d * a, d⁻¹ * b, c, d * e, d * d⁻¹ * f, by
      rw [g2Act_tG]
      simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
        q6_apply_inr2, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hd]⟩
  obtain ⟨α, hα⟩ := burnsideB46_mp_exists_sq (a₁ + e₁ * b₁ + f₁ * c₁)
  refine ⟨burnsideB46_mp_ke α c₁ b₁ e₁ f₁ * tG (Units.mk0 d hd),
    Subgroup.mul_mem _ (burnsideB46_mp_ke_mem _ _ _ _ _) (burnsideB46_mp_tG_mem _), ?_⟩
  rw [show ∀ x, g2Act (burnsideB46_mp_ke α c₁ b₁ e₁ f₁ * tG (Units.mk0 d hd)) x =
      g2Act (burnsideB46_mp_ke α c₁ b₁ e₁ f₁) (g2Act (tG (Units.mk0 d hd)) x) from
      fun x => g2Act_mul_apply _ _ x, h1, burnsideB46_mp_ke_apply]
  refine q6_congr ?_ ?_ ?_ rfl ?_ ?_
  · linear_combination hα + (a₁ + e₁ * b₁ + f₁ * c₁ + c₁ * f₁ + b₁ * e₁) * h2
  · linear_combination b₁ * h2
  · linear_combination c₁ * h2
  · linear_combination (e₁ + b₁ * c₁ * c₁ + α * c₁) * h2
  · linear_combination (f₁ + c₁ * b₁ * b₁ + α * b₁) * h2

theorem burnsideB46_mp_tG_apply (c : K) (hc : c ≠ 0) (a b c₀ d e f : K) :
    g2Act (tG (Units.mk0 c hc)) (q6 a b c₀ d e f) =
      q6 (c * a) (c⁻¹ * b) c₀ (c⁻¹ * d) (c * e) (c * c⁻¹ * f) := by
  rw [g2Act_tG]
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2, Units.val_inv_eq_inv_val, Units.val_mk0]

@[expose] def burnsideB46_mp_Rel (y y' : Ix3 → K) : Prop :=
  ∃ p ∈ stabQ (stdF K 1), g2Act p y = y'

theorem burnsideB46_mp_Rel.refl (y : Ix3 → K) : burnsideB46_mp_Rel y y :=
  ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩

theorem burnsideB46_mp_Rel.symm {y y' : Ix3 → K} (h : burnsideB46_mp_Rel y y') :
    burnsideB46_mp_Rel y' y := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p⁻¹, Subgroup.inv_mem _ hp, g2Act_inv_apply p y⟩

theorem burnsideB46_mp_Rel.trans {y y' y'' : Ix3 → K} (h : burnsideB46_mp_Rel y y')
    (h' : burnsideB46_mp_Rel y' y'') : burnsideB46_mp_Rel y y'' := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨p', hp', rfl⟩ := h'
  exact ⟨p' * p, Subgroup.mul_mem _ hp' hp, g2Act_mul_apply p' p y⟩

theorem burnsideB46_mp_Rel_of_mem {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1))
    (y : Ix3 → K) : burnsideB46_mp_Rel y (g2Act p y) := ⟨p, hp, rfl⟩

theorem burnsideB46_mp_rel_u1 [Finite K] (a e f : K) :
    burnsideB46_mp_Rel (q6 a 1 0 0 e f) (q6 (0 : K) 1 0 0 0 0) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨β, hβ⟩ := burnsideB46_mp_exists_sq e
  refine ⟨_, burnsideB46_mp_ke_mem f β 0 (a + β * f) 0, ?_⟩
  rw [burnsideB46_mp_ke_apply]
  refine q6_congr ?_ ?_ ?_ rfl ?_ ?_
  · linear_combination (a + β * f) * h2
  · ring
  · ring
  · linear_combination hβ + e * h2
  · linear_combination f * h2

theorem burnsideB46_mp_rel_r5_of_b [Finite K] (a b c e f : K) (hb : b ≠ 0) :
    burnsideB46_mp_Rel (q6 a b c 0 e f) (q6 (0 : K) 1 0 0 0 0) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hbb : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  have s1 : burnsideB46_mp_Rel (q6 a b c 0 e f) (q6 a b 0 0 (e + c * b⁻¹ * f) f) := by
    refine ⟨_, burnsideB46_mp_tv21_mem (c * b⁻¹), ?_⟩
    rw [burnsideB46_mp_tv21]
    exact q6_congr rfl rfl (by linear_combination c * hbb + c * h2) rfl rfl rfl
  have s2 : burnsideB46_mp_Rel (q6 a b 0 0 (e + c * b⁻¹ * f) f)
      (q6 (b * a) 1 0 0 (b * (e + c * b⁻¹ * f)) (b * b⁻¹ * f)) := by
    refine ⟨_, burnsideB46_mp_tG_mem (Units.mk0 b hb), ?_⟩
    rw [burnsideB46_mp_tG_apply]
    exact q6_congr rfl hbb rfl (mul_zero _) rfl rfl
  exact s1.trans (s2.trans (burnsideB46_mp_rel_u1 _ _ _))

theorem burnsideB46_mp_rel_r5 [Finite K] (a b c e f : K) (h : b ≠ 0 ∨ c ≠ 0) :
    burnsideB46_mp_Rel (q6 a b c 0 e f) (q6 (0 : K) 1 0 0 0 0) := by
  by_cases hb : b = 0
  · have hc : c ≠ 0 := h.resolve_left (not_not.mpr hb)
    have s0 : burnsideB46_mp_Rel (q6 a b c 0 e f) (q6 a (b + c⁻¹ * c) c 0 e (f + c⁻¹ * e)) :=
      ⟨_, burnsideB46_mp_tv12_mem c⁻¹, burnsideB46_mp_tv12 _ _ _ _ _ _ _⟩
    have hb' : b + c⁻¹ * c ≠ 0 := by
      rw [hb, zero_add, inv_mul_cancel₀ hc]
      exact one_ne_zero
    exact s0.trans (burnsideB46_mp_rel_r5_of_b _ _ _ _ _ hb')
  · exact burnsideB46_mp_rel_r5_of_b a b c e f hb

theorem burnsideB46_mp_rel_r3_of_e [Finite K] (a e f : K) (he : e ≠ 0) :
    burnsideB46_mp_Rel (q6 a 0 0 0 e f) (q6 (0 : K) 0 0 0 0 1) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hee : e⁻¹ * e = 1 := inv_mul_cancel₀ he
  have s1 : burnsideB46_mp_Rel (q6 a 0 0 0 e f) (q6 a 0 0 0 e 1) := by
    refine ⟨_, burnsideB46_mp_tv12_mem ((1 + f) * e⁻¹), ?_⟩
    rw [burnsideB46_mp_tv12]
    exact q6_congr rfl (by ring) rfl rfl rfl (by linear_combination (1 + f) * hee + f * h2)
  have s2 : burnsideB46_mp_Rel (q6 a 0 0 0 e 1) (q6 a 0 0 0 0 1) := by
    refine ⟨_, burnsideB46_mp_tv21_mem e, ?_⟩
    rw [burnsideB46_mp_tv21]
    exact q6_congr rfl rfl (by ring) rfl (by linear_combination e * h2) rfl
  have s3 : burnsideB46_mp_Rel (q6 a 0 0 0 0 1) (q6 (0 : K) 0 0 0 0 1) := by
    refine ⟨_, burnsideB46_mp_ke_mem 0 a 0 0 0, ?_⟩
    rw [burnsideB46_mp_ke_apply]
    refine q6_congr ?_ ?_ ?_ rfl ?_ ?_
    · linear_combination a * h2
    · ring
    · ring
    · ring
    · ring
  exact s1.trans (s2.trans s3)

theorem burnsideB46_mp_rel_r3 [Finite K] (a e f : K) (h : e ≠ 0 ∨ f ≠ 0) :
    burnsideB46_mp_Rel (q6 a 0 0 0 e f) (q6 (0 : K) 0 0 0 0 1) := by
  by_cases he : e = 0
  · have hf : f ≠ 0 := h.resolve_left (not_not.mpr he)
    have s0 : burnsideB46_mp_Rel (q6 a 0 0 0 e f) (q6 a 0 0 0 (e + f⁻¹ * f) f) := by
      refine ⟨_, burnsideB46_mp_tv21_mem f⁻¹, ?_⟩
      rw [burnsideB46_mp_tv21]
      exact q6_congr rfl rfl (by ring) rfl rfl rfl
    have he' : e + f⁻¹ * f ≠ 0 := by
      rw [he, zero_add, inv_mul_cancel₀ hf]
      exact one_ne_zero
    exact s0.trans (burnsideB46_mp_rel_r3_of_e _ _ _ he')
  · exact burnsideB46_mp_rel_r3_of_e a e f he

theorem burnsideB46_mp_mem_F5 (y : Ix3 → K) : y ∈ stdF K 5 ↔ y (.inr 0) = 0 := by
  conv_lhs => rw [q6_eta y]
  rw [mem_stdF, inF_q6_iff]
  simp

theorem burnsideB46_mp_mem_F3 (y : Ix3 → K) :
    y ∈ stdF K 3 ↔ y (.inl 1) = 0 ∧ y (.inl 2) = 0 ∧ y (.inr 0) = 0 := by
  conv_lhs => rw [q6_eta y]
  rw [mem_stdF, inF_q6_iff]
  simp

theorem burnsideB46_mp_mem_F1 (y : Ix3 → K) :
    y ∈ stdF K 1 ↔ y (.inl 1) = 0 ∧ y (.inl 2) = 0 ∧ y (.inr 0) = 0 ∧ y (.inr 1) = 0 ∧
      y (.inr 2) = 0 := by
  conv_lhs => rw [q6_eta y]
  rw [mem_stdF, inF_q6_iff]
  simp

theorem burnsideB46_mp_rel_r6' [Finite K] {y : Ix3 → K} (hy : y ∉ stdF K 5) :
    burnsideB46_mp_Rel y (q6 (0 : K) 0 0 1 0 0) := by
  have hd : y (.inr 0) ≠ 0 := fun h => hy ((burnsideB46_mp_mem_F5 y).2 h)
  rw [q6_eta y]
  obtain ⟨p, hp, h⟩ := burnsideB46_mp_to_r6 (y (.inl 0)) (y (.inl 1)) (y (.inl 2)) (y (.inr 0))
    (y (.inr 1)) (y (.inr 2)) hd
  exact ⟨p, hp, h⟩

theorem burnsideB46_mp_rel_r5' [Finite K] {y : Ix3 → K} (h5 : y ∈ stdF K 5)
    (h3 : y ∉ stdF K 3) : burnsideB46_mp_Rel y (q6 (0 : K) 1 0 0 0 0) := by
  have hd : y (.inr 0) = 0 := (burnsideB46_mp_mem_F5 y).1 h5
  have hbc : y (.inl 1) ≠ 0 ∨ y (.inl 2) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h3 ((burnsideB46_mp_mem_F3 y).2 ⟨hcon.1, hcon.2, hd⟩)
  conv_lhs => rw [q6_eta y, hd]
  exact burnsideB46_mp_rel_r5 _ _ _ _ _ hbc

theorem burnsideB46_mp_rel_r3' [Finite K] {y : Ix3 → K} (h3 : y ∈ stdF K 3)
    (h1 : y ∉ stdF K 1) : burnsideB46_mp_Rel y (q6 (0 : K) 0 0 0 0 1) := by
  obtain ⟨hb, hc, hd⟩ := (burnsideB46_mp_mem_F3 y).1 h3
  have hef : y (.inr 1) ≠ 0 ∨ y (.inr 2) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h1 ((burnsideB46_mp_mem_F1 y).2 ⟨hb, hc, hd, hcon.1, hcon.2⟩)
  conv_lhs => rw [q6_eta y, hb, hc, hd]
  exact burnsideB46_mp_rel_r3 _ _ _ hef

theorem burnsideB46_mp_card_Ix3 [Finite K] : Nat.card (Ix3 → K) = Nat.card K ^ 6 := by
  rw [Nat.card_fun]
  congr 1
  rw [Nat.card_eq_fintype_card]
  rfl

@[expose, instance_reducible] def burnsideB46_mp_act : MulAction ↥(cayleyGroup K) (Ix3 → K) where
  smul g w := g2Act g w
  one_smul w := by
    change g2Act 1 w = w
    rw [map_one]
    rfl
  mul_smul g h w := g2Act_mul_apply g h w

theorem burnsideB46_mp_orbit_count [Finite K] (Q : Subgroup ↥(cayleyGroup K))
    (hQ : stabV0 K ≤ Q) :
    Set.ncard {w : Ix3 → K | ∃ q ∈ Q, g2Act q (eu 0 1) = w} * Q.index + 1 = Nat.card K ^ 6 := by
  classical
  letI : MulAction ↥(cayleyGroup K) (Ix3 → K) := burnsideB46_mp_act (K := K)
  have hsmul : ∀ (g : ↥(cayleyGroup K)) (w : Ix3 → K), g • w = g2Act g w := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥(cayleyGroup K) (eu 0 1 : Ix3 → K) = stabV0 K := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul]
    rfl
  have hQs : (stabV0 K).subgroupOf Q = MulAction.stabilizer ↥Q (eu 0 1 : Ix3 → K) := by
    ext q
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def, hsmul]
    rfl
  have hu0 : (eu 0 1 : Ix3 → K) ≠ 0 := by
    rw [eu_eq_q6]
    intro h
    have := congrArg (fun w : Ix3 → K => w (.inl 0)) h
    exact one_ne_zero this
  have hGorb : MulAction.orbit ↥(cayleyGroup K) (eu 0 1 : Ix3 → K) = {w | w ≠ 0} := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩ h
      rw [hsmul] at h
      have h1 := g2Act_inv_apply g (eu 0 1)
      rw [h, map_zero] at h1
      exact hu0 h1.symm
    · intro hw
      obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hw
      exact ⟨g, hg⟩
  have hQorb : MulAction.orbit ↥Q (eu 0 1 : Ix3 → K) = {w | ∃ q ∈ Q, g2Act q (eu 0 1) = w} := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, q.2, hq⟩
    · rintro ⟨q, hq, hqw⟩
      exact ⟨⟨q, hq⟩, hqw⟩
  have h1 := Subgroup.relIndex_mul_index hQ
  rw [Subgroup.relIndex, hQs, MulAction.index_stabilizer, hQorb, ← hstab,
    MulAction.index_stabilizer, hGorb] at h1
  have hcard : {w : Ix3 → K | w ≠ 0}.ncard + 1 = Nat.card K ^ 6 := by
    have h6 := burnsideB46_mp_card_Ix3 (K := K)
    have hset : {w : Ix3 → K | w ≠ 0} = (Set.univ : Set (Ix3 → K)) \ {0} := by
      ext w
      simp
    rw [hset, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, h6]
    have : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ Nat.card_pos
    omega
  rw [h1]
  exact hcard

theorem burnsideB46_mp_ncard_step {Ω : Type*} [Finite Ω] (X A B : Set Ω) (hAB : A ⊆ B)
    (h : B \ A ⊆ X ∨ (B \ A) ∩ X = ∅) :
    ((B ∩ X).ncard + A.ncard = (A ∩ X).ncard + B.ncard ∧ B \ A ⊆ X) ∨
      ((B ∩ X).ncard = (A ∩ X).ncard ∧ (B \ A) ∩ X = ∅) := by
  have hsplit : B ∩ X = (A ∩ X) ∪ ((B \ A) ∩ X) := by
    ext w
    constructor
    · rintro ⟨hwB, hwX⟩
      by_cases hwA : w ∈ A
      · exact Or.inl ⟨hwA, hwX⟩
      · exact Or.inr ⟨⟨hwB, hwA⟩, hwX⟩
    · rintro (⟨hwA, hwX⟩ | ⟨⟨hwB, -⟩, hwX⟩)
      · exact ⟨hAB hwA, hwX⟩
      · exact ⟨hwB, hwX⟩
  have hdisj : Disjoint (A ∩ X) ((B \ A) ∩ X) := by
    rw [Set.disjoint_left]
    rintro w ⟨hwA, -⟩ ⟨⟨-, hwA'⟩, -⟩
    exact hwA' hwA
  have hcard : (B ∩ X).ncard = (A ∩ X).ncard + ((B \ A) ∩ X).ncard := by
    rw [hsplit, Set.ncard_union_eq hdisj]
  rcases h with h | h
  · left
    refine ⟨?_, h⟩
    rw [hcard, Set.inter_eq_left.mpr h]
    have h1 := Set.ncard_diff hAB
    have hle : A.ncard ≤ B.ncard := Set.ncard_le_ncard hAB
    omega
  · right
    refine ⟨?_, h⟩
    rw [hcard, h, Set.ncard_empty]
    rfl

theorem burnsideB46_mp_arith_aux (A R k m : ℤ) (hR : 0 < R) (hRA : R < A)
    (h : (m - k) * A = R) : False := by
  have hA : 0 < A := hR.trans hRA
  rcases le_or_gt m k with hmk | hmk
  · nlinarith [mul_nonneg (sub_nonneg.2 hmk) hA.le]
  · have h1 : (1 : ℤ) ≤ m - k := by omega
    nlinarith [mul_le_mul_of_nonneg_right h1 hA.le]

theorem burnsideB46_mp_arith_FTF_Z (M m N₁ N₃ N₅ N₆ : ℤ) (hM : 2 ≤ M) (hA : N₁ + 1 = M)
    (hB : N₃ = N₁) (hC : N₅ + M ^ 3 = N₃ + M ^ 5) (hD : N₆ = N₅)
    (hcount : N₆ * m + 1 = M ^ 6) : False := by
  have hN6 : N₆ = M ^ 5 - M ^ 3 + M - 1 := by linarith
  have key : (m - M) * N₆ = M ^ 4 - M ^ 2 + M - 1 := by
    rw [hN6] at hcount ⊢
    linear_combination hcount
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, M = t + 2 := ⟨M - 2, by ring⟩
  have ht : 0 ≤ t := by linarith
  refine burnsideB46_mp_arith_aux N₆ _ (t + 2) m ?_ ?_ key
  · ring_nf
    positivity
  · rw [hN6, ← sub_pos]
    ring_nf
    positivity

theorem burnsideB46_mp_arith_FFT_Z (M m N₁ N₃ N₅ N₆ : ℤ) (hM : 2 ≤ M) (hA : N₁ + 1 = M)
    (hB : N₃ = N₁) (hC : N₅ = N₃) (hD : N₆ + M ^ 5 = N₅ + M ^ 6)
    (hcount : N₆ * m + 1 = M ^ 6) : False := by
  have hN6 : N₆ = M ^ 6 - M ^ 5 + M - 1 := by linarith
  have key : (m - 1) * N₆ = M ^ 5 - M := by
    rw [hN6] at hcount ⊢
    linear_combination hcount
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, M = t + 2 := ⟨M - 2, by ring⟩
  have ht : 0 ≤ t := by linarith
  refine burnsideB46_mp_arith_aux N₆ _ 1 m ?_ ?_ key
  · ring_nf
    positivity
  · rw [hN6, ← sub_pos]
    ring_nf
    positivity

theorem burnsideB46_mp_arith_TTF_Z (M m N₁ N₃ N₅ N₆ : ℤ) (hM : 2 ≤ M) (hA : N₁ + 1 = M)
    (hB : N₃ + M = N₁ + M ^ 3) (hC : N₅ + M ^ 3 = N₃ + M ^ 5) (hD : N₆ = N₅)
    (hcount : N₆ * m + 1 = M ^ 6) : False := by
  have hN6 : N₆ = M ^ 5 - 1 := by linarith
  have key : (m - M) * N₆ = M - 1 := by
    rw [hN6] at hcount ⊢
    linear_combination hcount
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, M = t + 2 := ⟨M - 2, by ring⟩
  have ht : 0 ≤ t := by linarith
  refine burnsideB46_mp_arith_aux N₆ _ (t + 2) m ?_ ?_ key
  · linarith
  · rw [hN6, ← sub_pos]
    ring_nf
    positivity

theorem burnsideB46_mp_arith_TFT_Z (M m N₁ N₃ N₅ N₆ : ℤ) (hM : 2 ≤ M) (hA : N₁ + 1 = M)
    (hB : N₃ + M = N₁ + M ^ 3) (hC : N₅ = N₃) (hD : N₆ + M ^ 5 = N₅ + M ^ 6)
    (hcount : N₆ * m + 1 = M ^ 6) : False := by
  have hN6 : N₆ = M ^ 6 - M ^ 5 + M ^ 3 - 1 := by linarith
  have key : (m - 1) * N₆ = M ^ 5 - M ^ 3 := by
    rw [hN6] at hcount ⊢
    linear_combination hcount
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, M = t + 2 := ⟨M - 2, by ring⟩
  have ht : 0 ≤ t := by linarith
  refine burnsideB46_mp_arith_aux N₆ _ 1 m ?_ ?_ key
  · ring_nf
    positivity
  · rw [hN6, ← sub_pos]
    ring_nf
    positivity

theorem burnsideB46_mp_arith_FTT_Z (M m N₁ N₃ N₅ N₆ : ℤ) (hM : 2 ≤ M) (hA : N₁ + 1 = M)
    (hB : N₃ = N₁) (hC : N₅ + M ^ 3 = N₃ + M ^ 5) (hD : N₆ + M ^ 5 = N₅ + M ^ 6)
    (hcount : N₆ * m + 1 = M ^ 6) : False := by
  have hN6 : N₆ = M ^ 6 - M ^ 3 + M - 1 := by linarith
  have key : (m - 1) * N₆ = M ^ 3 - M := by
    rw [hN6] at hcount ⊢
    linear_combination hcount
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, M = t + 2 := ⟨M - 2, by ring⟩
  have ht : 0 ≤ t := by linarith
  refine burnsideB46_mp_arith_aux N₆ _ 1 m ?_ ?_ key
  · ring_nf
    positivity
  · rw [hN6, ← sub_pos]
    ring_nf
    positivity

theorem burnsideB46_mp_arith_TTT_Z (M m N₁ N₃ N₅ N₆ : ℤ) (hM : 2 ≤ M) (hA : N₁ + 1 = M)
    (hB : N₃ + M = N₁ + M ^ 3) (hC : N₅ + M ^ 3 = N₃ + M ^ 5) (hD : N₆ + M ^ 5 = N₅ + M ^ 6)
    (hcount : N₆ * m + 1 = M ^ 6) : m = 1 := by
  have hN6 : N₆ = M ^ 6 - 1 := by linarith
  have hpos : 0 < N₆ := by
    rw [hN6]
    have : (2 : ℤ) ^ 6 ≤ M ^ 6 := pow_le_pow_left₀ (by norm_num) hM 6
    nlinarith
  rw [hN6] at hcount
  have h1 : N₆ * (m - 1) = 0 := by
    rw [hN6]
    linear_combination hcount
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hpos.ne'
  · linarith

theorem burnsideB46_mp_eu_ne_zero : (eu 0 1 : Ix3 → K) ≠ 0 := by
  rw [eu_eq_q6]
  intro h
  have := congrArg (fun w : Ix3 → K => w (.inl 0)) h
  exact one_ne_zero this

theorem burnsideB46_mp_stabV0_le : stabV0 K ≤ stabQ (stdF K 1) := fun g hg =>
  burnsideB46_mp_mem_P (c := 1) one_ne_zero (by rw [one_smul]; exact hg)

theorem burnsideB46_mp_stab_of_eq (Q : Subgroup ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K))
    (hS : ∀ w, w ∈ S ↔ w = 0 ∨ w ∈ {w : Ix3 → K | ∃ q ∈ Q, g2Act q (eu 0 1) = w}) :
    Q ≤ stabQ S := by
  have key : ∀ q ∈ Q, ∀ w ∈ S, g2Act q w ∈ S := by
    intro q hq w hw
    rcases (hS w).1 hw with rfl | ⟨q', hq', rfl⟩
    · rw [map_zero]
      exact S.zero_mem
    · rw [← g2Act_mul_apply]
      exact (hS _).2 (Or.inr ⟨q * q', Subgroup.mul_mem _ hq hq', rfl⟩)
  intro q hq
  refine mem_stabQ.mpr fun w => ⟨key q hq w, fun h => ?_⟩
  have := key q⁻¹ (Subgroup.inv_mem _ hq) _ h
  rwa [g2Act_inv_apply] at this

theorem burnsideB46_mp_ncard_stdF [Finite K] {h : ℕ} (hh : h ≤ 6) :
    ((stdF K h : Submodule K (Ix3 → K)) : Set (Ix3 → K)).ncard = Nat.card K ^ h := by
  rw [← Nat.card_coe_set_eq]
  exact card_stdF hh

theorem burnsideB46_mp_layers {Ω : Type*} [Finite Ω] (X F1 F3 F5 : Set Ω) (z : Ω) (M m : ℕ)
    (hM : 2 ≤ M) (h13 : F1 ⊆ F3) (h35 : F3 ⊆ F5) (c1 : F1.ncard = M) (c3 : F3.ncard = M ^ 3)
    (c5 : F5.ncard = M ^ 5) (c6 : (Set.univ : Set Ω).ncard = M ^ 6) (hzF1 : z ∈ F1)
    (hzX : z ∉ X) (hF1X : F1 \ {z} ⊆ X) (hL3 : F3 \ F1 ⊆ X ∨ (F3 \ F1) ∩ X = ∅)
    (hL5 : F5 \ F3 ⊆ X ∨ (F5 \ F3) ∩ X = ∅)
    (hL6 : Set.univ \ F5 ⊆ X ∨ (Set.univ \ F5) ∩ X = ∅)
    (hcount : X.ncard * m + 1 = M ^ 6) :
    X ⊆ F1 ∨ (X ⊆ F3 ∧ F3 \ {z} ⊆ X) ∨ m = 1 := by
  have hN1 : (F1 ∩ X).ncard + 1 = M := by
    have hF : F1 ∩ X = F1 \ {z} := by
      ext w
      constructor
      · rintro ⟨hw1, hwX⟩
        refine ⟨hw1, fun h => hzX ?_⟩
        rwa [Set.mem_singleton_iff.mp h] at hwX
      · rintro ⟨hw1, hw⟩
        exact ⟨hw1, hF1X ⟨hw1, hw⟩⟩
    rw [hF, Set.ncard_diff_singleton_of_mem hzF1, c1]
    omega
  have stB := burnsideB46_mp_ncard_step X F1 F3 h13 hL3
  have stC := burnsideB46_mp_ncard_step X F3 F5 h35 hL5
  have stD := burnsideB46_mp_ncard_step X F5 Set.univ (Set.subset_univ _) hL6
  rw [Set.univ_inter] at stD
  rw [c1, c3] at stB
  rw [c3, c5] at stC
  rw [c5, c6] at stD
  generalize (F1 ∩ X).ncard = N₁ at *
  generalize (F3 ∩ X).ncard = N₃ at *
  generalize (F5 ∩ X).ncard = N₅ at *
  generalize X.ncard = N₆ at *
  have hMz : (2 : ℤ) ≤ M := by exact_mod_cast hM
  have hAz : (N₁ : ℤ) + 1 = M := by exact_mod_cast hN1
  have hcz : (N₆ : ℤ) * m + 1 = (M : ℤ) ^ 6 := by exact_mod_cast hcount
  rcases stB with ⟨hB, hB'⟩ | ⟨hB, hB'⟩
  · rcases stC with ⟨hC, hC'⟩ | ⟨hC, hC'⟩
    · rcases stD with ⟨hD, hD'⟩ | ⟨hD, hD'⟩
      · right; right
        have := burnsideB46_mp_arith_TTT_Z M m N₁ N₃ N₅ N₆ hMz hAz (by exact_mod_cast hB)
          (by exact_mod_cast hC) (by exact_mod_cast hD) hcz
        exact_mod_cast this
      · exact (burnsideB46_mp_arith_TTF_Z M m N₁ N₃ N₅ N₆ hMz hAz (by exact_mod_cast hB)
          (by exact_mod_cast hC) (by exact_mod_cast hD) hcz).elim
    · rcases stD with ⟨hD, hD'⟩ | ⟨hD, hD'⟩
      · exact (burnsideB46_mp_arith_TFT_Z M m N₁ N₃ N₅ N₆ hMz hAz (by exact_mod_cast hB)
          (by exact_mod_cast hC) (by exact_mod_cast hD) hcz).elim
      · right; left
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · by_contra hw3
          by_cases hw5 : w ∈ F5
          · have h : w ∈ (F5 \ F3) ∩ X := ⟨⟨hw5, hw3⟩, hw⟩
            rw [hC'] at h
            simp at h
          · have h : w ∈ (Set.univ \ F5) ∩ X := ⟨⟨Set.mem_univ _, hw5⟩, hw⟩
            rw [hD'] at h
            simp at h
        · by_cases hw1 : w ∈ F1
          · exact hF1X ⟨hw1, hw.2⟩
          · exact hB' ⟨hw.1, hw1⟩
  · rcases stC with ⟨hC, hC'⟩ | ⟨hC, hC'⟩
    · rcases stD with ⟨hD, hD'⟩ | ⟨hD, hD'⟩
      · exact (burnsideB46_mp_arith_FTT_Z M m N₁ N₃ N₅ N₆ hMz hAz (by exact_mod_cast hB)
          (by exact_mod_cast hC) (by exact_mod_cast hD) hcz).elim
      · exact (burnsideB46_mp_arith_FTF_Z M m N₁ N₃ N₅ N₆ hMz hAz (by exact_mod_cast hB)
          (by exact_mod_cast hC) (by exact_mod_cast hD) hcz).elim
    · rcases stD with ⟨hD, hD'⟩ | ⟨hD, hD'⟩
      · exact (burnsideB46_mp_arith_FFT_Z M m N₁ N₃ N₅ N₆ hMz hAz (by exact_mod_cast hB)
          (by exact_mod_cast hC) (by exact_mod_cast hD) hcz).elim
      · left
        intro w hw
        by_contra hw1
        by_cases hw3 : w ∈ F3
        · have h : w ∈ (F3 \ F1) ∩ X := ⟨⟨hw3, hw1⟩, hw⟩
          rw [hB'] at h
          simp at h
        · by_cases hw5 : w ∈ F5
          · have h : w ∈ (F5 \ F3) ∩ X := ⟨⟨hw5, hw3⟩, hw⟩
            rw [hC'] at h
            simp at h
          · have h : w ∈ (Set.univ \ F5) ∩ X := ⟨⟨Set.mem_univ _, hw5⟩, hw⟩
            rw [hD'] at h
            simp at h

theorem burnsideB46_mp_max [Finite K] (Q : Subgroup ↥(cayleyGroup K))
    (hPQ : stabQ (stdF K 1) ≤ Q) : Q = stabQ (stdF K 1) ∨ Q = ⊤ := by
  classical
  have hM : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcount := burnsideB46_mp_orbit_count Q (burnsideB46_mp_stabV0_le.trans hPQ)
  set X : Set (Ix3 → K) := {w | ∃ q ∈ Q, g2Act q (eu 0 1) = w} with hXdef
  have hX0 : (0 : Ix3 → K) ∉ X := by
    rintro ⟨q, -, h⟩
    have h1 := g2Act_inv_apply q (eu 0 1)
    rw [h, map_zero] at h1
    exact burnsideB46_mp_eu_ne_zero h1.symm
  have hXinv : ∀ q ∈ Q, ∀ w ∈ X, g2Act q w ∈ X := by
    rintro q hq w ⟨q', hq', rfl⟩
    exact ⟨q * q', Subgroup.mul_mem _ hq hq', g2Act_mul_apply q q' _⟩
  have hRel : ∀ w w', w ∈ X → burnsideB46_mp_Rel w w' → w' ∈ X := by
    rintro w w' hw ⟨p, hp, rfl⟩
    exact hXinv p (hPQ hp) w hw
  have hF1X : ((stdF K 1 : Submodule K (Ix3 → K)) : Set (Ix3 → K)) \ {0} ⊆ X := by
    rintro w ⟨hw1, hw0⟩
    obtain ⟨t, rfl⟩ := mem_stdF_one_iff.mp hw1
    have ht : t ≠ 0 := fun h => hw0 (by rw [h, zero_smul]; exact Set.mem_singleton _)
    refine ⟨tG (Units.mk0 t ht), hPQ (burnsideB46_mp_tG_mem _), ?_⟩
    rw [eu_eq_q6, burnsideB46_mp_tG_apply, smul_q6]
    exact q6_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  have layer : ∀ (L : Set (Ix3 → K)) (r : Ix3 → K), (∀ y ∈ L, burnsideB46_mp_Rel y r) →
      (L ⊆ X ∨ L ∩ X = ∅) := by
    intro L r hL
    by_cases h : ∃ y ∈ L, y ∈ X
    · obtain ⟨y, hyL, hyX⟩ := h
      left
      intro y' hy'
      exact hRel y y' hyX ((hL y hyL).trans (hL y' hy').symm)
    · right
      ext y
      constructor
      · rintro ⟨hyL, hyX⟩
        exact absurd ⟨y, hyL, hyX⟩ h
      · intro h'
        exact h'.elim
  have key := burnsideB46_mp_layers X (stdF K 1 : Set (Ix3 → K)) (stdF K 3 : Set (Ix3 → K))
    (stdF K 5 : Set (Ix3 → K)) 0 (Nat.card K) Q.index hM
    (SetLike.coe_subset_coe.2 (stdF_mono (by norm_num)))
    (SetLike.coe_subset_coe.2 (stdF_mono (by norm_num)))
    (by rw [burnsideB46_mp_ncard_stdF (by norm_num), pow_one])
    (burnsideB46_mp_ncard_stdF (by norm_num)) (burnsideB46_mp_ncard_stdF (by norm_num))
    (by rw [Set.ncard_univ, burnsideB46_mp_card_Ix3]) (Submodule.zero_mem _) hX0 hF1X
    (layer _ _ (fun y hy => burnsideB46_mp_rel_r3' hy.1 hy.2))
    (layer _ _ (fun y hy => burnsideB46_mp_rel_r5' hy.1 hy.2))
    (layer _ _ (fun y hy => burnsideB46_mp_rel_r6' hy.2)) hcount
  rcases key with hX1 | ⟨hX3, hX3'⟩ | hm
  · left
    refine le_antisymm (burnsideB46_mp_stab_of_eq Q (stdF K 1) fun w => ⟨fun hw => ?_, fun hw => ?_⟩) hPQ
    · by_cases hw0 : w = 0
      · exact Or.inl hw0
      · exact Or.inr (hF1X ⟨hw, hw0⟩)
    · rcases hw with rfl | hw
      · exact Submodule.zero_mem _
      · exact hX1 hw
  · left
    have hQ3 : Q ≤ stabQ (stdF K 3) :=
      burnsideB46_mp_stab_of_eq Q (stdF K 3) fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · rw [← stabQ_one_eq_three] at hQ3
      exact le_antisymm hQ3 hPQ
    · by_cases hw0 : w = 0
      · exact Or.inl hw0
      · exact Or.inr (hX3' ⟨hw, hw0⟩)
    · rcases hw with rfl | hw
      · exact Submodule.zero_mem _
      · exact hX3 hw
  · right
    exact Subgroup.index_eq_one.mp hm

theorem burnsideB46_mp_U0_le : U0 K ≤ stabQ (stdF K 1) := by
  intro u hu
  refine mem_stabQ.mpr fun w => ⟨fun hw => FlagUni.mem hu hw, fun hw => ?_⟩
  have := FlagUni.mem ((U0 K).inv_mem hu) hw
  rwa [g2Act_inv_apply] at this

theorem burnsideB46_mp_torus_le : torusG K ≤ stabQ (stdF K 1) := by
  rintro _ ⟨s, rfl⟩
  exact mem_stabQ.mpr fun w => (g2T_inF (h := 1) s w).symm

theorem burnsideB46_mp_isSylow [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    CFSG.QuasithinUnique.IsSylowTwoOf (U0 K) (⊤ : Subgroup ↥(cayleyGroup K)) := by
  refine ⟨le_top, isPGroup_U0, ?_⟩
  have h := not_two_dvd_index_U0 hK hn
  rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right]

theorem burnsideB46_mp_isParabolic2 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    IsParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 1)) := by
  refine ⟨le_top, U0 K, burnsideB46_mp_isSylow hK hn, ?_⟩
  rw [normalizer_U0_eq]
  exact inf_le_right.trans (sup_le burnsideB46_mp_U0_le burnsideB46_mp_torus_le)

theorem burnsideB46_mp_ne_top [Finite K] :
    stabQ (stdF K 1) ≠ (⊤ : Subgroup ↥(cayleyGroup K)) := by
  intro h
  obtain ⟨g, hg⟩ := exists_g2Act_eu_eq (F := K) (w := q6 (0 : K) 0 0 1 0 0) (by
    intro h0
    have := congrArg (fun w : Ix3 → K => w (.inr 0)) h0
    exact one_ne_zero this)
  have hmem : g ∈ stabQ (stdF K 1) := h ▸ Subgroup.mem_top g
  have h1 : (eu 0 1 : Ix3 → K) ∈ stdF K 1 := mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩
  have h2 := (mem_stabQ.mp hmem (eu 0 1)).mp h1
  rw [hg] at h2
  exact one_ne_zero ((burnsideB46_mp_mem_F1 _).1 h2).2.2.1

theorem burnsideB46_mp_isMax [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 1)) :=
  ⟨burnsideB46_mp_isParabolic2 hK hn, burnsideB46_mp_ne_top, fun Q _ hQne hPQ =>
    (burnsideB46_mp_max Q hPQ).resolve_right hQne⟩

theorem burnsideB46_mp_P1_eq_map [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    ∃ g : ↥(cayleyGroup K),
      burnsideB46_P1 K x = (stabQ (stdF K 1)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hx
  refine ⟨g, ?_⟩
  have hpt : ∀ w, w ∈ burnsideB46_pt K x ↔ g2Act g⁻¹ w ∈ stdF K 1 := by
    intro w
    rw [burnsideB46_pt, Submodule.mem_span_singleton, mem_stdF_one_iff]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      rw [JonesParshall.g2Act_smul, ← hg, g2Act_inv_apply]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have h1 := congrArg (g2Act g) ht
      rw [g2Act_apply_inv, JonesParshall.g2Act_smul, hg] at h1
      exact h1.symm
  ext k
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  change k ∈ stabQ (burnsideB46_pt K x) ↔ g⁻¹ * k * g ∈ stabQ (stdF K 1)
  rw [mem_stabQ, mem_stabQ]
  constructor
  · intro h w'
    have h1 := h (g2Act g w')
    rw [hpt, hpt, g2Act_inv_apply] at h1
    have e : g2Act g⁻¹ (g2Act k (g2Act g w')) = g2Act (g⁻¹ * k * g) w' := by
      rw [g2Act_mul_apply, g2Act_mul_apply]
    rwa [e] at h1
  · intro h w
    rw [hpt, hpt]
    have h1 := h (g2Act g⁻¹ w)
    have e : g2Act (g⁻¹ * k * g) (g2Act g⁻¹ w) = g2Act g⁻¹ (g2Act k w) := by
      rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv]
    rwa [e] at h1

theorem burnsideB46_mp_hmax1 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {x : Ix3 → K} (hx : x ≠ 0) :
    IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (burnsideB46_P1 K x) := by
  obtain ⟨g, hg⟩ := burnsideB46_mp_P1_eq_map hx
  rw [hg]
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup
  exact CFSG.QuasithinUnique.Vol2Native.A312L.isMaxParabolic2_top_map_equiv (MulAut.conj g)
    (burnsideB46_mp_isMax hK hn)

end MP

section WP2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

@[expose] def burnsideB46_wp2_Rel (y y' : Ix3 → K) : Prop :=
  ∃ p ∈ stabQ (stdF K 2), g2Act p y = y'

theorem burnsideB46_wp2_Rel.refl (y : Ix3 → K) : burnsideB46_wp2_Rel y y :=
  ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩

theorem burnsideB46_wp2_Rel.symm {y y' : Ix3 → K} (h : burnsideB46_wp2_Rel y y') :
    burnsideB46_wp2_Rel y' y := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p⁻¹, Subgroup.inv_mem _ hp, g2Act_inv_apply p y⟩

theorem burnsideB46_wp2_Rel.trans {y y' y'' : Ix3 → K} (h : burnsideB46_wp2_Rel y y')
    (h' : burnsideB46_wp2_Rel y' y'') : burnsideB46_wp2_Rel y y'' := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨p', hp', rfl⟩ := h'
  exact ⟨p' * p, Subgroup.mul_mem _ hp' hp, g2Act_mul_apply p' p y⟩

theorem burnsideB46_wp2_x1_mem (t : K) : g2X ![0, t, 0] ∈ stabQ (stdF K 2) :=
  sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inl rfl⟩)

theorem burnsideB46_wp2_y1_mem (t : K) : g2Y ![0, t, 0] ∈ stabQ (stdF K 2) :=
  sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inr rfl⟩)

theorem burnsideB46_wp2_ke_mem (α β γ p q' : K) :
    burnsideB46_mp_ke α β γ p q' ∈ stabQ (stdF K 2) :=
  CFSG.Quasithin.Vol2.Ch11.SecB.K5.U0_le_stabQ 2
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (g2X_mem_U0 α) (g2Y_mem_U0 β γ)) (g2A_mem_U0 p q' 0))

theorem burnsideB46_wp2_uSL_mem (p q' s : K) : g2A (uSL p q' s) ∈ stabQ (stdF K 2) :=
  CFSG.Quasithin.Vol2.Ch11.SecB.K5.U0_le_stabQ 2 (g2A_mem_U0 p q' s)

theorem burnsideB46_wp2_tG_mem (c : Kˣ) : tG c ∈ stabQ (stdF K 2) :=
  mem_stabQ.mpr fun w => (tG_inF c w).symm

theorem burnsideB46_wp2_uSL_apply (p q' s a b c d e f : K) :
    g2Act (g2A (uSL p q' s)) (q6 a b c d e f) =
      q6 (a + p * b + q' * c) (b + s * c) c d (e + p * d) (f + (p * s + q') * d + s * e) := by
  rw [g2Act_g2A_uSL]
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2]

theorem burnsideB46_wp2_rel_A_of_a (a f : K) (ha : a ≠ 0) :
    burnsideB46_wp2_Rel (q6 a 0 0 0 0 f) (q6 (1 : K) 0 0 0 0 0) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have haa : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  have s1 : burnsideB46_wp2_Rel (q6 a 0 0 0 0 f) (q6 a 0 0 0 0 0) := by
    refine ⟨_, burnsideB46_wp2_x1_mem (f * a⁻¹), ?_⟩
    rw [g2Act_x1q]
    exact q6_congr rfl (by ring) rfl (by ring) rfl (by linear_combination f * haa + f * h2)
  have s2 : burnsideB46_wp2_Rel (q6 a 0 0 0 0 0) (q6 (1 : K) 0 0 0 0 0) := by
    refine ⟨_, burnsideB46_wp2_tG_mem (Units.mk0 a⁻¹ (inv_ne_zero ha)), ?_⟩
    rw [burnsideB46_mp_tG_apply]
    exact q6_congr haa (by ring) rfl (by ring) (by ring) (by ring)
  exact s1.trans s2

theorem burnsideB46_wp2_rel_A_of_f (f : K) (hf : f ≠ 0) :
    burnsideB46_wp2_Rel (q6 (0 : K) 0 0 0 0 f) (q6 (1 : K) 0 0 0 0 0) := by
  have hff : f⁻¹ * f = 1 := inv_mul_cancel₀ hf
  have s1 : burnsideB46_wp2_Rel (q6 (0 : K) 0 0 0 0 f) (q6 (1 : K) 0 0 0 0 f) := by
    refine ⟨_, burnsideB46_wp2_y1_mem f⁻¹, ?_⟩
    rw [g2Act_y1q]
    exact q6_congr (by linear_combination hff) rfl (by ring) rfl (by ring) rfl
  exact s1.trans (burnsideB46_wp2_rel_A_of_a 1 f one_ne_zero)

theorem burnsideB46_wp2_rel_A (a f : K) (h : a ≠ 0 ∨ f ≠ 0) :
    burnsideB46_wp2_Rel (q6 a 0 0 0 0 f) (q6 (1 : K) 0 0 0 0 0) := by
  by_cases ha : a = 0
  · subst ha
    exact burnsideB46_wp2_rel_A_of_f f (h.resolve_left (not_not.mpr rfl))
  · exact burnsideB46_wp2_rel_A_of_a a f ha

theorem burnsideB46_wp2_rel_B_of_e [Finite K] (a b e f : K) (he : e ≠ 0) :
    burnsideB46_wp2_Rel (q6 a b 0 0 e f) (q6 (0 : K) 0 0 0 1 0) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hee : e⁻¹ * e = 1 := inv_mul_cancel₀ he
  obtain ⟨t, ht⟩ := burnsideB46_mp_exists_sq (b * e⁻¹)
  have s1 : burnsideB46_wp2_Rel (q6 a b 0 0 e f) (q6 a 0 0 0 e (f + t * a)) := by
    refine ⟨_, burnsideB46_wp2_x1_mem t, ?_⟩
    rw [g2Act_x1q]
    exact q6_congr rfl (by linear_combination e * ht + b * hee + b * h2) rfl (by ring) rfl rfl
  have s2 : burnsideB46_wp2_Rel (q6 a 0 0 0 e (f + t * a)) (q6 a 0 0 0 e 0) := by
    refine ⟨_, burnsideB46_wp2_uSL_mem 0 0 ((f + t * a) * e⁻¹), ?_⟩
    rw [burnsideB46_wp2_uSL_apply]
    exact q6_congr (by ring) (by ring) rfl rfl (by ring)
      (by linear_combination (f + t * a) * hee + (f + t * a) * h2)
  have s3 : burnsideB46_wp2_Rel (q6 a 0 0 0 e 0) (q6 (0 : K) 0 0 0 e 0) := by
    refine ⟨_, burnsideB46_wp2_ke_mem 0 0 (a * e⁻¹) 0 0, ?_⟩
    rw [burnsideB46_mp_ke_apply]
    exact q6_congr (by linear_combination a * hee + a * h2) (by ring) (by ring) rfl (by ring)
      (by ring)
  have s4 : burnsideB46_wp2_Rel (q6 (0 : K) 0 0 0 e 0) (q6 (0 : K) 0 0 0 1 0) := by
    refine ⟨_, burnsideB46_wp2_tG_mem (Units.mk0 e⁻¹ (inv_ne_zero he)), ?_⟩
    rw [burnsideB46_mp_tG_apply]
    exact q6_congr (by ring) (by ring) rfl (by ring) hee (by ring)
  exact s1.trans (s2.trans (s3.trans s4))

theorem burnsideB46_wp2_rel_B_of_b [Finite K] (a b f : K) (hb : b ≠ 0) :
    burnsideB46_wp2_Rel (q6 a b 0 0 0 f) (q6 (0 : K) 0 0 0 1 0) := by
  have hbb : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  obtain ⟨t, ht⟩ := burnsideB46_mp_exists_sq b⁻¹
  have s1 : burnsideB46_wp2_Rel (q6 a b 0 0 0 f) (q6 (a + t * f) b 0 0 1 f) := by
    refine ⟨_, burnsideB46_wp2_y1_mem t, ?_⟩
    rw [g2Act_y1q]
    exact q6_congr rfl rfl (by ring) rfl (by linear_combination b * ht + hbb) rfl
  exact s1.trans (burnsideB46_wp2_rel_B_of_e _ _ _ _ one_ne_zero)

theorem burnsideB46_wp2_rel_B [Finite K] (a b e f : K) (h : b ≠ 0 ∨ e ≠ 0) :
    burnsideB46_wp2_Rel (q6 a b 0 0 e f) (q6 (0 : K) 0 0 0 1 0) := by
  by_cases he : e = 0
  · subst he
    exact burnsideB46_wp2_rel_B_of_b a b f (h.resolve_right (not_not.mpr rfl))
  · exact burnsideB46_wp2_rel_B_of_e a b e f he

theorem burnsideB46_wp2_rel_C_of_d [Finite K] (a b c d e f : K) (hd : d ≠ 0) :
    burnsideB46_wp2_Rel (q6 a b c d e f) (q6 (0 : K) 0 0 1 0 0) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨a₁, b₁, c₁, e₁, f₁, h1⟩ : ∃ a₁ b₁ c₁ e₁ f₁ : K,
      g2Act (tG (Units.mk0 d hd)) (q6 a b c d e f) = q6 a₁ b₁ c₁ 1 e₁ f₁ :=
    ⟨d * a, d⁻¹ * b, c, d * e, d * d⁻¹ * f, by
      rw [g2Act_tG]
      simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
        q6_apply_inr2, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hd]⟩
  obtain ⟨α, hα⟩ := burnsideB46_mp_exists_sq (a₁ + e₁ * b₁ + f₁ * c₁)
  refine ⟨burnsideB46_mp_ke α c₁ b₁ e₁ f₁ * tG (Units.mk0 d hd),
    Subgroup.mul_mem _ (burnsideB46_wp2_ke_mem _ _ _ _ _) (burnsideB46_wp2_tG_mem _), ?_⟩
  rw [show ∀ x, g2Act (burnsideB46_mp_ke α c₁ b₁ e₁ f₁ * tG (Units.mk0 d hd)) x =
      g2Act (burnsideB46_mp_ke α c₁ b₁ e₁ f₁) (g2Act (tG (Units.mk0 d hd)) x) from
      fun x => g2Act_mul_apply _ _ x, h1, burnsideB46_mp_ke_apply]
  refine q6_congr ?_ ?_ ?_ rfl ?_ ?_
  · linear_combination hα + (a₁ + e₁ * b₁ + f₁ * c₁ + c₁ * f₁ + b₁ * e₁) * h2
  · linear_combination b₁ * h2
  · linear_combination c₁ * h2
  · linear_combination (e₁ + b₁ * c₁ * c₁ + α * c₁) * h2
  · linear_combination (f₁ + c₁ * b₁ * b₁ + α * b₁) * h2

theorem burnsideB46_wp2_rel_C [Finite K] (a b c d e f : K) (h : c ≠ 0 ∨ d ≠ 0) :
    burnsideB46_wp2_Rel (q6 a b c d e f) (q6 (0 : K) 0 0 1 0 0) := by
  by_cases hd : d = 0
  · subst hd
    have hc : c ≠ 0 := h.resolve_right (not_not.mpr rfl)
    have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    have s1 : burnsideB46_wp2_Rel (q6 a b c 0 e f)
        (q6 a (b + c⁻¹ * c⁻¹ * e) c 1 e (f + c⁻¹ * a)) := by
      refine ⟨_, burnsideB46_wp2_x1_mem c⁻¹, ?_⟩
      rw [g2Act_x1q]
      exact q6_congr rfl rfl rfl (by linear_combination hcc) rfl rfl
    exact s1.trans (burnsideB46_wp2_rel_C_of_d _ _ _ _ _ _ one_ne_zero)
  · exact burnsideB46_wp2_rel_C_of_d a b c d e f hd

theorem burnsideB46_wp2_mem_F2 (y : Ix3 → K) :
    y ∈ stdF K 2 ↔ y (.inl 1) = 0 ∧ y (.inl 2) = 0 ∧ y (.inr 0) = 0 ∧ y (.inr 1) = 0 := by
  conv_lhs => rw [q6_eta y]
  rw [mem_stdF, inF_q6_iff]
  simp

theorem burnsideB46_wp2_mem_F4 (y : Ix3 → K) :
    y ∈ stdF K 4 ↔ y (.inl 2) = 0 ∧ y (.inr 0) = 0 := by
  conv_lhs => rw [q6_eta y]
  rw [mem_stdF, inF_q6_iff]
  simp

theorem burnsideB46_wp2_le_stabQ_of_maps (Q : Subgroup ↥(cayleyGroup K))
    (S : Submodule K (Ix3 → K)) (h : ∀ q ∈ Q, ∀ w ∈ S, g2Act q w ∈ S) : Q ≤ stabQ S := by
  intro q hq
  refine mem_stabQ.mpr fun w => ⟨fun hw => h q hq w hw, fun hw => ?_⟩
  have := h q⁻¹ (Subgroup.inv_mem _ hq) _ hw
  rwa [g2Act_inv_apply] at this

@[expose] def burnsideB46_wp2_W (K : Type) [Field K] [CharP K 2] : ↥(cayleyGroup K) :=
  g2X ![0, 1, 0] * g2Y ![0, 1, 0] * g2X ![0, 1, 0]

theorem burnsideB46_wp2_W_apply (a b c d e f : K) :
    g2Act (burnsideB46_wp2_W K) (q6 a b c d e f) = q6 f e d c b a := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [burnsideB46_wp2_W, g2Act_mul_apply', g2Act_mul_apply', g2Act_x1q, g2Act_y1q, g2Act_x1q]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination a * h2
  · linear_combination (b + e) * h2
  · linear_combination c * h2
  · linear_combination (d + c) * h2
  · linear_combination e * h2
  · linear_combination (f + a) * h2

theorem burnsideB46_wp2_W_inv : (burnsideB46_wp2_W K)⁻¹ = burnsideB46_wp2_W K := by
  rw [burnsideB46_wp2_W, mul_inv_rev, mul_inv_rev, JonesParshall.g2X_inv, JonesParshall.g2Y_inv,
    mul_assoc]

theorem burnsideB46_wp2_conj_y1 (t : K) :
    g2X ![0, t, 0] =
      burnsideB46_wp2_W K * g2Y ![0, t, 0] * (burnsideB46_wp2_W K)⁻¹ := by
  rw [burnsideB46_wp2_W_inv]
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w, g2Act_mul_apply', g2Act_mul_apply', burnsideB46_wp2_W_apply, g2Act_y1q,
    burnsideB46_wp2_W_apply, g2Act_x1q]

theorem burnsideB46_wp2_top_of_transitive (Q : Subgroup ↥(cayleyGroup K)) (hU : U0 K ≤ Q)
    (hQ : ∀ w : Ix3 → K, w ≠ 0 → ∃ q ∈ Q, g2Act q (eu 0 1) = w) : Q = ⊤ := by
  have key : ∀ (g : ↥(cayleyGroup K)) (t : K), g * g2Y ![0, t, 0] * g⁻¹ ∈ Q := by
    intro g t
    have hgu : g2Act g (eu 0 1) ≠ 0 := by
      intro h
      have h1 := g2Act_inv_apply g (eu 0 1)
      rw [h, map_zero] at h1
      exact burnsideB46_mp_eu_ne_zero h1.symm
    obtain ⟨q, hq, hqg⟩ := hQ _ hgu
    have hsS : q⁻¹ * g ∈ stabV0 K := by
      rw [mem_stabV0, g2Act_mul_apply, ← hqg, g2Act_inv_apply]
    have hy : g2Y ![0, t, 0] ∈ stabV0 K := g2Y_mem_stabV0 t 0
    have hm : q⁻¹ * g * g2Y ![0, t, 0] * (q⁻¹ * g)⁻¹ ∈ stabV0 K :=
      (stabV0 K).mul_mem ((stabV0 K).mul_mem hsS hy) ((stabV0 K).inv_mem hsS)
    have h1 : levi1Mat (q⁻¹ * g * g2Y ![0, t, 0] * (q⁻¹ * g)⁻¹) = 1 := by
      rw [levi1Mat_mul ((stabV0 K).mul_mem hsS hy) ((stabV0 K).inv_mem hsS), levi1Mat_mul hsS hy,
        levi1Mat_g2Y, mul_one, ← levi1Mat_mul hsS ((stabV0 K).inv_mem hsS), mul_inv_cancel,
        levi1Mat_one]
    have hconj : q⁻¹ * g * g2Y ![0, t, 0] * (q⁻¹ * g)⁻¹ ∈ U0 K :=
      ker_levi1_le (g := ⟨_, hm⟩) (Subtype.ext h1)
    have e : g * g2Y ![0, t, 0] * g⁻¹ = q * (q⁻¹ * g * g2Y ![0, t, 0] * (q⁻¹ * g)⁻¹) * q⁻¹ := by
      group
    rw [e]
    exact Q.mul_mem (Q.mul_mem hq (hU hconj)) (Q.inv_mem hq)
  have keyX : ∀ (g : ↥(cayleyGroup K)) (t : K), g * g2X ![0, t, 0] * g⁻¹ ∈ Q := by
    intro g t
    have e : g * g2X ![0, t, 0] * g⁻¹ =
        (g * burnsideB46_wp2_W K) * g2Y ![0, t, 0] * (g * burnsideB46_wp2_W K)⁻¹ := by
      rw [burnsideB46_wp2_conj_y1 t, mul_inv_rev]
      group
    rw [e]
    exact key _ t
  have hgen : genE12 K ≤ Q := by
    rw [genE12, Subgroup.closure_le]
    rintro g (⟨t, rfl | rfl⟩ | ⟨g', ⟨t, rfl | rfl⟩, rfl⟩)
    · simpa using keyX 1 t
    · simpa using key 1 t
    · exact keyX _ t
    · exact key _ t
  rw [genE12_eq_top] at hgen
  exact eq_top_iff.mpr hgen

theorem burnsideB46_wp2_coatom [Finite K] (Q : Subgroup ↥(cayleyGroup K))
    (hPQ : stabQ (stdF K 2) ≤ Q) (hQ : Q ≠ ⊤) : Q = stabQ (stdF K 2) := by
  classical
  have hU : U0 K ≤ Q := (CFSG.Quasithin.Vol2.Ch11.SecB.K5.U0_le_stabQ 2).trans hPQ
  set X : Set (Ix3 → K) := {w | ∃ q ∈ Q, g2Act q (eu 0 1) = w}
  have hX0 : (0 : Ix3 → K) ∉ X := by
    rintro ⟨q, -, h⟩
    have h1 := g2Act_inv_apply q (eu 0 1)
    rw [h, map_zero] at h1
    exact burnsideB46_mp_eu_ne_zero h1.symm
  have hXinv : ∀ q ∈ Q, ∀ w ∈ X, g2Act q w ∈ X := by
    rintro q hq w ⟨q', hq', rfl⟩
    exact ⟨q * q', Subgroup.mul_mem _ hq hq', g2Act_mul_apply q q' _⟩
  have hRel : ∀ w w', w ∈ X → burnsideB46_wp2_Rel w w' → w' ∈ X := by
    rintro w w' hw ⟨p, hp, rfl⟩
    exact hXinv p (hPQ hp) w hw
  have hu0 : (q6 (1 : K) 0 0 0 0 0) ∈ X :=
    ⟨1, Q.one_mem, by rw [eu_eq_q6, map_one]; rfl⟩
  have layer : ∀ (L : Set (Ix3 → K)) (r : Ix3 → K), (∀ y ∈ L, burnsideB46_wp2_Rel y r) →
      (L ⊆ X ∨ L ∩ X = ∅) := by
    intro L r hL
    by_cases h : ∃ y ∈ L, y ∈ X
    · obtain ⟨y, hyL, hyX⟩ := h
      left
      intro y' hy'
      exact hRel y y' hyX ((hL y hyL).trans (hL y' hy').symm)
    · right
      ext y
      constructor
      · rintro ⟨hyL, hyX⟩
        exact absurd ⟨y, hyL, hyX⟩ h
      · intro h'
        exact h'.elim
  have hA : ∀ y ∈ stdF K 2, y ≠ 0 → y ∈ X := by
    intro y hy hy0
    obtain ⟨hb, hc, hd, he⟩ := (burnsideB46_wp2_mem_F2 y).1 hy
    have hne : y (.inl 0) ≠ 0 ∨ y (.inr 2) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hy0
      funext k
      rcases k with k | k <;> fin_cases k <;> simp [hb, hc, hd, he, hcon.1, hcon.2]
    have hy' : y = q6 (y (.inl 0)) 0 0 0 0 (y (.inr 2)) := by
      conv_lhs => rw [q6_eta y, hb, hc, hd, he]
    rw [hy']
    exact hRel _ _ hu0 (burnsideB46_wp2_Rel.symm (burnsideB46_wp2_rel_A _ _ hne))
  have hBrel : ∀ y ∈ (stdF K 4 : Set (Ix3 → K)) \ (stdF K 2 : Set (Ix3 → K)),
      burnsideB46_wp2_Rel y (q6 (0 : K) 0 0 0 1 0) := by
    rintro y ⟨hy4, hy2⟩
    obtain ⟨hc, hd⟩ := (burnsideB46_wp2_mem_F4 y).1 hy4
    have hbe : y (.inl 1) ≠ 0 ∨ y (.inr 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy2 ((burnsideB46_wp2_mem_F2 y).2 ⟨hcon.1, hc, hd, hcon.2⟩)
    conv_lhs => rw [q6_eta y, hc, hd]
    exact burnsideB46_wp2_rel_B _ _ _ _ hbe
  have hCrel : ∀ y ∈ (Set.univ : Set (Ix3 → K)) \ (stdF K 4 : Set (Ix3 → K)),
      burnsideB46_wp2_Rel y (q6 (0 : K) 0 0 1 0 0) := by
    rintro y ⟨-, hy4⟩
    have hcd : y (.inl 2) ≠ 0 ∨ y (.inr 0) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy4 ((burnsideB46_wp2_mem_F4 y).2 hcon)
    conv_lhs => rw [q6_eta y]
    exact burnsideB46_wp2_rel_C _ _ _ _ _ _ hcd
  have hF4 : stabQ (stdF K 4) ≤ stabQ (stdF K 2) :=
    CFSG.Quasithin.Vol2.Ch11.SecB.K5.stabQ_le_perp (h := 4) (by norm_num)
  rcases layer _ _ hBrel with hBX | hBX <;> rcases layer _ _ hCrel with hCX | hCX
  ·
    refine absurd (burnsideB46_wp2_top_of_transitive Q hU fun w hw => ?_) hQ
    by_cases hw2 : w ∈ stdF K 2
    · exact hA w hw2 hw
    · by_cases hw4 : w ∈ stdF K 4
      · exact hBX ⟨hw4, hw2⟩
      · exact hCX ⟨Set.mem_univ _, hw4⟩
  ·
    refine le_antisymm (le_trans (burnsideB46_wp2_le_stabQ_of_maps Q (stdF K 4) ?_) hF4) hPQ
    intro q hq w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
      exact Submodule.zero_mem _
    · have hwX : w ∈ X := by
        by_cases hw2 : w ∈ stdF K 2
        · exact hA w hw2 hw0
        · exact hBX ⟨hw, hw2⟩
      by_contra h4
      have : g2Act q w ∈ (Set.univ : Set (Ix3 → K)) \ (stdF K 4 : Set (Ix3 → K)) ∩ X :=
        ⟨⟨Set.mem_univ _, h4⟩, hXinv q hq w hwX⟩
      rw [hCX] at this
      exact this
  ·
    refine le_antisymm (le_trans (burnsideB46_wp2_le_stabQ_of_maps Q (stdF K 4) ?_) hF4) hPQ
    intro q hq
    have hB' : ∀ w ∈ (stdF K 4 : Set (Ix3 → K)) \ (stdF K 2 : Set (Ix3 → K)),
        g2Act q w ∈ stdF K 4 := by
      rintro w ⟨hw4, hw2⟩
      by_contra h4
      have hqwX : g2Act q w ∈ X := hCX ⟨Set.mem_univ _, h4⟩
      have hwX : w ∈ X := by
        have := hXinv q⁻¹ (Subgroup.inv_mem _ hq) _ hqwX
        rwa [g2Act_inv_apply] at this
      have : w ∈ ((stdF K 4 : Set (Ix3 → K)) \ (stdF K 2 : Set (Ix3 → K))) ∩ X :=
        ⟨⟨hw4, hw2⟩, hwX⟩
      rw [hBX] at this
      exact this
    intro w hw
    by_cases hw2 : w ∈ stdF K 2
    ·
      have hv1 : q6 (0 : K) 0 0 0 1 0 ∈
          (stdF K 4 : Set (Ix3 → K)) \ (stdF K 2 : Set (Ix3 → K)) := by
        refine ⟨(burnsideB46_wp2_mem_F4 _).2 ⟨rfl, rfl⟩, fun h => ?_⟩
        have := ((burnsideB46_wp2_mem_F2 _).1 h).2.2.2
        exact one_ne_zero this
      have hwv : w + q6 (0 : K) 0 0 0 1 0 ∈
          (stdF K 4 : Set (Ix3 → K)) \ (stdF K 2 : Set (Ix3 → K)) := by
        refine ⟨(stdF K 4).add_mem hw hv1.1, fun h => ?_⟩
        have h1 := ((burnsideB46_wp2_mem_F2 _).1 h).2.2.2
        have h2 := ((burnsideB46_wp2_mem_F2 _).1 hw2).2.2.2
        rw [Pi.add_apply, h2, q6_apply_inr1, zero_add] at h1
        exact one_ne_zero h1
      have e : g2Act q w =
          g2Act q (w + q6 (0 : K) 0 0 0 1 0) - g2Act q (q6 (0 : K) 0 0 0 1 0) := by
        rw [map_add]
        exact (add_sub_cancel_right _ _).symm
      rw [e]
      exact (stdF K 4).sub_mem (hB' _ hwv) (hB' _ hv1)
    · exact hB' w ⟨hw, hw2⟩
  ·
    refine le_antisymm (burnsideB46_wp2_le_stabQ_of_maps Q (stdF K 2) ?_) hPQ
    intro q hq w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
      exact Submodule.zero_mem _
    · have hqwX : g2Act q w ∈ X := hXinv q hq w (hA w hw hw0)
      by_contra h2
      by_cases h4 : g2Act q w ∈ stdF K 4
      · have : g2Act q w ∈ ((stdF K 4 : Set (Ix3 → K)) \ (stdF K 2 : Set (Ix3 → K))) ∩ X :=
          ⟨⟨h4, h2⟩, hqwX⟩
        rw [hBX] at this
        exact this
      · have : g2Act q w ∈ ((Set.univ : Set (Ix3 → K)) \ (stdF K 4 : Set (Ix3 → K))) ∩ X :=
          ⟨⟨Set.mem_univ _, h4⟩, hqwX⟩
        rw [hCX] at this
        exact this

theorem burnsideB46_wp2_ne_top [Finite K] :
    stabQ (stdF K 2) ≠ (⊤ : Subgroup ↥(cayleyGroup K)) := by
  intro h
  obtain ⟨g, hg⟩ := exists_g2Act_eu_eq (F := K) (w := q6 (0 : K) 0 0 1 0 0) (by
    intro h0
    have := congrArg (fun w : Ix3 → K => w (.inr 0)) h0
    exact one_ne_zero this)
  have hmem : g ∈ stabQ (stdF K 2) := h ▸ Subgroup.mem_top g
  have h1 : (eu 0 1 : Ix3 → K) ∈ stdF K 2 := by
    rw [eu_eq_q6, burnsideB46_wp2_mem_F2]
    simp [q6]
  have h2 := (mem_stabQ.mp hmem (eu 0 1)).mp h1
  rw [hg] at h2
  exact one_ne_zero ((burnsideB46_wp2_mem_F2 _).1 h2).2.2.1

theorem burnsideB46_wp2_torus_le : torusG K ≤ stabQ (stdF K 2) := by
  rintro _ ⟨s, rfl⟩
  exact mem_stabQ.mpr fun w => (g2T_inF (h := 2) s w).symm

theorem burnsideB46_wp2_isParabolic2 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    IsParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2)) := by
  refine ⟨le_top, U0 K, burnsideB46_mp_isSylow hK hn, ?_⟩
  rw [normalizer_U0_eq]
  exact inf_le_right.trans
    (sup_le (CFSG.Quasithin.Vol2.Ch11.SecB.K5.U0_le_stabQ 2) burnsideB46_wp2_torus_le)

theorem burnsideB46_wp2_isMax [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2)) :=
  ⟨burnsideB46_wp2_isParabolic2 hK hn, burnsideB46_wp2_ne_top, fun Q _ hQne hPQ =>
    burnsideB46_wp2_coatom Q hPQ hQne⟩

theorem burnsideB46_wp2_isMax_conj [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (g : ↥(cayleyGroup K)) :
    IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K))
      ((stabQ (stdF K 2)).map (MulAut.conj g).toMonoidHom) := by
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup
  exact CFSG.QuasithinUnique.Vol2Native.A312L.isMaxParabolic2_top_map_equiv (MulAut.conj g)
    (burnsideB46_wp2_isMax hK hn)

end WP2

section W14B

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)


variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_w14b_card_le_orbit [Finite K] (w : Ix3 → K) (φ : K → ↥(cayleyGroup K))
    (hφ : ∀ t, φ t ∈ U0 K) (hinj : Function.Injective fun t => g2Act (φ t) w) :
    Nat.card K ≤ Set.ncard {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u w = x} := by
  have h1 : Set.range (fun t => g2Act (φ t) w) ⊆ {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u w = x} := by
    rintro _ ⟨t, rfl⟩
    exact ⟨φ t, hφ t, rfl⟩
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ] at h2
  exact h2

theorem burnsideB46_w14b_orbit_ge_bcd [Finite K] (a b c d e f : K)
    (h : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    Nat.card K ≤ Set.ncard {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u (q6 a b c d e f) = x} := by
  refine burnsideB46_w14b_card_le_orbit _ (fun α => g2X ![α, 0, 0]) (fun α => g2X_mem_U0 α) ?_
  intro α α' hαα'
  simp only [g2Act_g2X_e0] at hαα'
  obtain ⟨h1, -, -, -, h5, h6⟩ := q6_inj hαα'
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2] at h1 h5 h6
  rcases h with hb | hc | hd
  · exact mul_right_cancel₀ hb (add_left_cancel h6)
  · exact mul_right_cancel₀ hc (add_left_cancel h5)
  · exact eq_of_mul_self_eq_charTwo (mul_right_cancel₀ hd (add_left_cancel h1))

theorem burnsideB46_w14b_orbit_ge_e [Finite K] (a e f : K) (he : e ≠ 0) :
    Nat.card K ≤ Set.ncard {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u (q6 a 0 0 0 e f) = x} := by
  refine burnsideB46_w14b_card_le_orbit _ (fun t => g2A (uSL 0 0 t)) (fun t => g2A_mem_U0 0 0 t) ?_
  intro t t' htt'
  simp only [g2Act_g2A_uSL] at htt'
  obtain ⟨-, -, -, -, -, h6⟩ := q6_inj htt'
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2] at h6
  exact mul_right_cancel₀ he (by linear_combination h6)

theorem burnsideB46_w14b_orbit_ge_f [Finite K] (a f : K) (hf : f ≠ 0) :
    Nat.card K ≤ Set.ncard {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u (q6 a 0 0 0 0 f) = x} := by
  refine burnsideB46_w14b_card_le_orbit _ (fun β => g2Y ![0, β, 0]) (fun β => g2Y_mem_U0 β 0) ?_
  intro β β' hββ'
  simp only [g2Act_g2Y_e12] at hββ'
  obtain ⟨h1, -, -, -, -, -⟩ := q6_inj hββ'
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2] at h1
  exact mul_right_cancel₀ hf (by linear_combination h1)

theorem burnsideB46_w14b_orbit_ge [Finite K] :
    ∀ w ∉ stdF K 1, Nat.card K ≤ Set.ncard {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u w = x} := by
  intro w hw
  obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f : K, w = q6 a b c d e f :=
    ⟨_, _, _, _, _, _, q6_eta w⟩
  rw [burnsideB46_mp_mem_F1] at hw
  simp only [q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2,
    not_and_or] at hw
  by_cases hbcd : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0
  · exact burnsideB46_w14b_orbit_ge_bcd a b c d e f hbcd
  · push Not at hbcd
    obtain ⟨rfl, rfl, rfl⟩ := hbcd
    by_cases he : e = 0
    · subst he
      have hf : f ≠ 0 := by
        rcases hw with h | h | h | h | h <;> simp_all
      exact burnsideB46_w14b_orbit_ge_f a f hf
    · exact burnsideB46_w14b_orbit_ge_e a e f he

theorem burnsideB46_w14b_orbit_card_le [Finite K] {H : Subgroup ↥(cayleyGroup K)}
    (hU : U0 K ≤ H) :
    Set.ncard {w : Ix3 → K | ∃ h ∈ H, g2Act h (eu 0 1) = w} ≤ (U0 K).relIndex H := by
  classical
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup
  letI : MulAction ↥(cayleyGroup K) (Ix3 → K) := burnsideB46_mp_act (K := K)
  have hsmul : ∀ (g : ↥(cayleyGroup K)) (w : Ix3 → K), g • w = g2Act g w := fun _ _ => rfl
  have hle : (U0 K).subgroupOf H ≤ MulAction.stabilizer ↥H (eu 0 1 : Ix3 → K) := by
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, hsmul]
    exact U0_le_stabV0 hq
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [MulAction.index_stabilizer] at hdvd
  have horb : MulAction.orbit ↥H (eu 0 1 : Ix3 → K) = {w | ∃ h ∈ H, g2Act h (eu 0 1) = w} := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, q.2, hq⟩
    · rintro ⟨q, hq, hqw⟩
      exact ⟨⟨q, hq⟩, hqw⟩
  rw [horb] at hdvd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd

theorem burnsideB46_w14b_le_P1 [Finite K] (hK : 4 ≤ Nat.card K) {H : Subgroup ↥(cayleyGroup K)}
    (hU : U0 K ≤ H) (hidx : (U0 K).relIndex H ≤ 3) : H ≤ stabQ (stdF K 1) := by
  set X : Set (Ix3 → K) := {w | ∃ h ∈ H, g2Act h (eu 0 1) = w} with hX
  have hXcard : X.ncard ≤ 3 := (burnsideB46_w14b_orbit_card_le hU).trans hidx
  have hXinv : ∀ u ∈ U0 K, ∀ w ∈ X, g2Act u w ∈ X := by
    rintro u hu w ⟨h, hh, rfl⟩
    exact ⟨u * h, H.mul_mem (hU hu) hh, g2Act_mul_apply u h _⟩
  have hXF : ∀ w ∈ X, w ∈ stdF K 1 := by
    intro w hw
    by_contra hw1
    have h1 := burnsideB46_w14b_orbit_ge w hw1
    have h2 : {x : Ix3 → K | ∃ u ∈ U0 K, g2Act u w = x} ⊆ X := by
      rintro _ ⟨u, hu, rfl⟩
      exact hXinv u hu w hw
    have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
    omega
  intro h hh
  obtain ⟨c, hc⟩ := mem_stdF_one_iff.mp (hXF _ ⟨h, hh, rfl⟩)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have h1 := g2Act_inv_apply h (eu 0 1)
    rw [hc, map_zero] at h1
    exact burnsideB46_mp_eu_ne_zero h1.symm
  exact burnsideB46_mp_mem_P hc0 hc

end W14B

section N1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_n1_der_le : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
  Subgroup.commutator_le_self _

theorem burnsideB46_n1_der_conj {g x : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ quasithinG2 K) (hx : x ∈ ⁅quasithinG2 K, quasithinG2 K⁆) :
    g * x * g⁻¹ ∈ ⁅quasithinG2 K, quasithinG2 K⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    refine Subgroup.subset_closure ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg ha) (Subgroup.inv_mem _ hg)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hb) (Subgroup.inv_mem _ hg)
    · simp only [commutatorElement_def]
      group
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem burnsideB46_n1_layerOf_le_commutator (X : Subgroup (MulAut V)) : layerOf X ≤ ⁅X, X⁆ := by
  refine sSup_le fun C hC => ?_
  haveI : Group.IsPerfect ↥C := Group.isPerfect_def.2 hC.2.2.1
  calc C = ⁅C, C⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hC.1 hC.1

theorem burnsideB46_n1_comm_le_range (H : burnsideB46_Hyp V n K G L π θ) :
    ⁅L, L⁆ ≤ (π.comp (Subgroup.inclusion (burnsideB46_n1_der_le (K := K)))).range := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (burnsideB46_mem_L H).1 hx
  obtain ⟨b, rfl⟩ := (burnsideB46_mem_L H).1 hy
  refine ⟨⟨⁅(a : quasithinZorn K ≃ₗ[K] quasithinZorn K), (b : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁆,
    Subgroup.commutator_mem_commutator a.2 b.2⟩, ?_⟩
  have h : Subgroup.inclusion (burnsideB46_n1_der_le (K := K))
      ⟨⁅(a : quasithinZorn K ≃ₗ[K] quasithinZorn K), (b : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁆,
        Subgroup.commutator_mem_commutator a.2 b.2⟩ = ⁅a, b⁆ := Subtype.ext rfl
  rw [MonoidHom.comp_apply, h, map_commutatorElement]

theorem burnsideB46_n1_gen (H : burnsideB46_Hyp V n K G L π θ) (v : V) :
    v ∈ Subgroup.closure {x | ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, ∃ w : V,
      x = (π.comp (Subgroup.inclusion (burnsideB46_n1_der_le (K := K)))) γ w * w⁻¹} := by
  have hv : v ∈ commV (layerOf L) := by rw [H.comm]; trivial
  refine (Subgroup.closure_mono ?_) hv
  rintro _ ⟨x, hx, w, rfl⟩
  obtain ⟨γ, rfl⟩ := burnsideB46_n1_comm_le_range H
    ((burnsideB46_n1_layerOf_le_commutator L) hx)
  exact ⟨γ, w, rfl⟩

open CFSG.Quasithin.MS93 CFSG.Quasithin.H13.VolI in
@[expose] noncomputable def burnsideB46_n1_cover [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) :
    ModelCover (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) V where
  ρ := π.comp (Subgroup.inclusion burnsideB46_n1_der_le)
  β := (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆).symm.toMonoidHom.comp
    (burnsideB46_ixMul.comp θ)
  surj := (zornSecEquiv _).symm.surjective.comp (burnsideB46_ixMul_surjective.comp H.surj)
  fix := by
    intro γ v hv
    have h1 : burnsideB46_ixMul (θ v) = 1 := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hv
      exact hv
    have h2 : θ v = 1 := burnsideB46_ixMul_injective (h1.trans (map_one _).symm)
    have h3 : v ∈ fixV L := H.ker ▸ (MonoidHom.mem_ker.2 h2)
    exact mem_fixV.1 h3 _
      ((burnsideB46_mem_L H).2 ⟨Subgroup.inclusion burnsideB46_n1_der_le γ, rfl⟩)
  equiv := by
    intro γ v m hm hvm
    have hΓ : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K := g2Derived_le K
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq] at hvm ⊢
    have h1 := (linModelZorn ⁅quasithinG2 K, quasithinG2 K⁆ hΓ).e_act γ m hm
    apply Multiplicative.toAdd.injective
    have h2 : Multiplicative.toAdd ((zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆)
        (QuotientGroup.mk (⟨(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act γ ↑m, hm⟩ :
          ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec))) =
        zornLin ((show ↥⁅quasithinG2 K, quasithinG2 K⁆ from γ) :
            quasithinZorn K ≃ₗ[K] quasithinZorn K)
          (Multiplicative.toAdd ((zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆)
            (QuotientGroup.mk m))) := h1
    rw [h2, ← hvm]
    exact burnsideB46_ixMul_act H (Subgroup.inclusion burnsideB46_n1_der_le γ) v
  gen := burnsideB46_n1_gen H

section N1Transport

variable {K' : Type} [Field K']

@[expose] def burnsideB46_n1_E (e : K ≃+* K') : ↥(zornO0 K) ≃* ↥(zornO0 K') where
  toFun m := ⟨Multiplicative.ofAdd
    (zornMap e (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))), by
      have h : (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).1 +
          (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))).2.2.2 = 0 := m.2
      change e _ + e _ = 0
      rw [← map_add, h, map_zero]⟩
  invFun m := ⟨Multiplicative.ofAdd
    (zornMap e.symm (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K')))), by
      have h : (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K'))).1 +
          (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K'))).2.2.2 = 0 := m.2
      change e.symm _ + e.symm _ = 0
      rw [← map_add, h, map_zero]⟩
  left_inv m := Subtype.ext (by
    change Multiplicative.ofAdd (zornMap e.symm (zornMap e _)) = _
    rw [zornMap_symm_apply]
    rfl)
  right_inv m := Subtype.ext (by
    change Multiplicative.ofAdd (zornMap e (zornMap e.symm _)) = _
    rw [zornMap_apply_symm]
    rfl)
  map_mul' x y := Subtype.ext (by
    change Multiplicative.ofAdd (zornMap e (_ + _)) =
      Multiplicative.ofAdd (zornMap e _) * Multiplicative.ofAdd (zornMap e _)
    rw [zornMap_add]
    rfl)

theorem burnsideB46_n1_E_val (e : K ≃+* K') (m : ↥(zornO0 K)) :
    Multiplicative.toAdd (burnsideB46_n1_E e m : Multiplicative (quasithinZorn K')) =
      zornMap e (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) := rfl

theorem burnsideB46_n1_E_act [CharP K 2] [CharP K' 2] (e : K ≃+* K')
    (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (m m' : ↥(zornO0 K))
    (h : (m' : Multiplicative (quasithinZorn K)) = zornAct _ γ m) :
    (burnsideB46_n1_E e m' : Multiplicative (quasithinZorn K')) =
      zornAct _ (CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv e γ)
        (burnsideB46_n1_E e m : Multiplicative (quasithinZorn K')) := by
  apply Multiplicative.toAdd.injective
  rw [burnsideB46_n1_E_val, h]
  change zornMap e ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) _) =
    (zornConj e (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)) (zornMap e _)
  rw [zornConj_apply, zornMap_symm_apply]

end N1Transport

open CFSG.Quasithin.MS93 CFSG.Quasithin.H13.VolI in
theorem burnsideB46_n1_gen_O0
    [CharP K 2] (e : K ≃+* ZMod 2)
    (hD : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).IsActionModel)
    (m : ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec) :
    m ∈ Subgroup.closure {x | ∃ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆)
      (y : ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec), x = secAut hD γ y * y⁻¹} := by
  set T := Subgroup.closure {x | ∃ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆)
      (y : ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec), x = secAut hD γ y * y⁻¹} with hT
  have hle : Subgroup.closure {x | ∃ γ y, x = zornSecAct γ y * y⁻¹} ≤
      T.map (burnsideB46_n1_E e).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨γ₂, y₂, rfl⟩
    let γ : ↥⁅quasithinG2 K, quasithinG2 K⁆ := (g2DerivedFieldEquiv e).symm γ₂
    let y : ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec := (burnsideB46_n1_E e).symm y₂
    refine ⟨secAut hD γ y * y⁻¹, Subgroup.subset_closure ⟨γ, y, rfl⟩, ?_⟩
    have h1 : burnsideB46_n1_E e (secAut hD γ y) =
        zornSecAct (g2DerivedFieldEquiv e γ) (burnsideB46_n1_E e y) :=
      Subtype.ext (burnsideB46_n1_E_act e γ y _ rfl)
    have h2 : g2DerivedFieldEquiv e γ = γ₂ := MulEquiv.apply_symm_apply _ γ₂
    have h3 : burnsideB46_n1_E e y = y₂ := MulEquiv.apply_symm_apply _ y₂
    rw [h2, h3] at h1
    have key : ∀ a b : ↥(zornO0 K), burnsideB46_n1_E e (a * b⁻¹) =
        burnsideB46_n1_E e a * (burnsideB46_n1_E e b)⁻¹ := fun a b => by rw [map_mul, map_inv]
    have h5 := key (secAut hD γ y) y
    rw [h1, h3] at h5
    exact h5
  obtain ⟨m', hm', hm'e⟩ := hle (zornO0_gen (burnsideB46_n1_E e m))
  have : m' = m := (burnsideB46_n1_E e).injective hm'e
  rwa [this] at hm'

open CFSG.Quasithin.MS93 CFSG.Quasithin.H13.VolI in
theorem burnsideB46_n1_psi
    [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hK : Nat.card K = 2) :
    ∃ ψ : ↥(zornO0 K) →* V, Function.Surjective ψ ∧
      (∀ m, ψ m = 1 → (m : Multiplicative (quasithinZorn K)) ∈ zornR K) ∧
      (∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (m m' : ↥(zornO0 K)),
        (m' : Multiplicative (quasithinZorn K)) = zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ m →
          ψ m' = π (Subgroup.inclusion burnsideB46_n1_der_le γ) (ψ m)) ∧
      ∀ m, Multiplicative.toAdd (θ (ψ m)) =
        burnsideB46_nat (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) := by
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hKf).symm
  have hΓ' : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := burnsideB46_n1_der_le
  have hD := FFModel.zornQ_isActionModel ⁅quasithinG2 K, quasithinG2 K⁆ hΓ'
  have : Finite (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Amb :=
    (inferInstance : Finite (Multiplicative (quasithinZorn K)))
  have : Finite ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec := Subtype.finite
  have hkfix : ∀ (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆), ∀ m ∈ zornR K,
      zornAct ⁅quasithinG2 K, quasithinG2 K⁆ γ m = m := by
    rintro γ m ⟨c, hc⟩
    show Multiplicative.ofAdd ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd m)) = m
    rw [hc, (mem_quasithinG2_isZornAuto (hΓ' γ.2)).map_smul_one c, ← hc]
    rfl
  have hE2 : ∀ m ∈ zornO0 K, m ^ 2 = 1 := by
    intro m _
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_smul]
  have hRc : Nat.card ↥((zornR K).subgroupOf (zornO0 K)) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe zornR_le_zornO0).toEquiv,
      CFSG.Quasithin.MS93.card_zornR', hK]
  set D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆ with hDdef
  have hkfix' : ∀ γ (m : ↥D.sec), (m : D.Amb) ∈ D.ker → secAut hD γ m = m :=
    fun γ m hm => Subtype.ext (hkfix γ m.1 hm)
  have hgen' := burnsideB46_n1_gen_O0 e hD
  have hE2' : ∀ m : ↥D.sec, m ^ 2 = 1 := fun m => Subtype.ext (hE2 m.1 m.2)
  have hbound' : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ C : ModelCover D W, Nat.card C.β.ker ≤ Nat.card ↥(D.ker.subgroupOf D.sec) := by
    intro W _ _ hW C
    have h1 := coverG2_two_bound W hW (C.mapZorn e)
    rw [ModelCover.mapZorn_ker e C] at h1
    rw [show Nat.card ↥(D.ker.subgroupOf D.sec) = 2 from hRc]
    exact h1
  obtain ⟨ψ, hψs, hψk, hψe, hψβ⟩ := ModelCover.exists_quotient (secAut hD) (fun _ _ => rfl)
    hkfix' hgen' hE2' hbound' H.exp2 (burnsideB46_n1_cover H)
  refine ⟨ψ, hψs, hψk, fun γ m m' hm' => ?_, fun m => ?_⟩
  · have h1 : m' = secAut hD γ m := Subtype.ext hm'
    have h2 := hψe γ m
    rw [h1]
    exact h2
  · have h1 := hψβ m
    have h2 : burnsideB46_ixMul (θ (ψ m)) =
        (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆) (QuotientGroup.mk m) := by
      have h3 : (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆).symm
          (burnsideB46_ixMul (θ (ψ m))) = QuotientGroup.mk m := h1
      exact (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆).symm_apply_eq.1 h3
    have h4 : (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆) (QuotientGroup.mk m) =
        Multiplicative.ofAdd
          (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) := rfl
    rw [h4, burnsideB46_ixMul_apply] at h2
    have h5 : burnsideB46_ix (Multiplicative.toAdd (θ (ψ m))) =
        zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) :=
      Multiplicative.ofAdd.injective h2
    rw [← h5, burnsideB46_nat_ix]
    rfl

theorem burnsideB46_n1_theta_act [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    {ψ : ↥(zornO0 K) →* V}
    (hψθ : ∀ m, Multiplicative.toAdd (θ (ψ m)) =
      burnsideB46_nat (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))))
    (γ : ↥(quasithinG2 K)) (m m' : ↥(zornO0 K))
    (h : (m' : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m) :
    θ (ψ m') = θ ((π γ) (ψ m)) := by
  apply Multiplicative.toAdd.injective
  rw [hψθ, burnsideB46_theta_act H, hψθ]
  have hx : cayleyTr (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) = 0 := m.2
  apply burnsideB46_ix_injective
  rw [burnsideB46_ix_nat, burnsideB46_ix_qAct, burnsideB46_ix_nat, h]
  exact g2_zP_apply (burnsideB46_cg γ) _ hx

open CFSG.Quasithin.MS93 CFSG.Quasithin.H13.VolI in
theorem burnsideB46_n1_weyl
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) :
    ∃ ψ : ↥(zornO0 K) →* V, Function.Surjective ψ ∧
      (∀ m, ψ m = 1 → (m : Multiplicative (quasithinZorn K)) ∈ zornR K) ∧
      (∀ (γ : ↥(quasithinG2 K)) (m m' : ↥(zornO0 K)),
        (m' : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m →
          ψ m' = π γ (ψ m)) ∧
      ∀ m, Multiplicative.toAdd (θ (ψ m)) =
        burnsideB46_nat (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have hK : Nat.card K = 2 := by rw [H.card, hn1, pow_one]
  obtain ⟨ψ, hψs, hψk, hψe, hψθ⟩ := burnsideB46_n1_psi H hK
  refine ⟨ψ, hψs, hψk, ?_, hψθ⟩
  intro γ m m' hm'
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hKf).symm
  have hΓ' : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := burnsideB46_n1_der_le
  have hD' := FFModel.zornQ_isActionModel ⁅quasithinG2 K, quasithinG2 K⁆ hΓ'
  have hD := FFModel.zornQ_isActionModel (quasithinG2 K) (le_refl _)
  let f₁ : ↥(zornO0 K) →* V := ψ.comp (secAut hD γ).toMonoidHom
  let f₂ : ↥(zornO0 K) →* V := (π γ).toMonoidHom.comp ψ
  let d : ↥(zornO0 K) →* V := f₁ * f₂⁻¹
  have hd1 : ∀ m, d m = f₁ m * (f₂ m)⁻¹ := fun m => rfl
  have hdfix : ∀ m, d m ∈ fixV L := by
    intro m
    rw [← H.ker, MonoidHom.mem_ker, hd1, map_mul, map_inv, mul_inv_eq_one]
    exact burnsideB46_n1_theta_act H hψθ γ m _ rfl
  have hdδ : ∀ (δ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (y : ↥(zornO0 K)),
      d (secAut hD' δ y) = d y := by
    intro δ y
    let δ' : ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
      ⟨(γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) * (δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) *
        (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁻¹, burnsideB46_n1_der_conj γ.2 δ.2⟩
    have e1 : secAut hD γ (secAut hD' δ y) = secAut hD' δ' (secAut hD γ y) := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      change (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
          ((δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) _) =
        ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) * (δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) *
          (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁻¹)
          ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) _)
      simp
    have e2 : (γ : ↥(quasithinG2 K)) * Subgroup.inclusion hΓ' δ = Subgroup.inclusion hΓ' δ' * γ := by
      apply Subtype.ext
      change (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) * (δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) =
        (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) * (δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) *
          (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁻¹ * (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      group
    have h1 : f₁ (secAut hD' δ y) = π (Subgroup.inclusion hΓ' δ') (f₁ y) := by
      change ψ (secAut hD γ (secAut hD' δ y)) = _
      rw [e1]
      exact hψe δ' (secAut hD γ y) _ rfl
    have h2 : f₂ (secAut hD' δ y) = π (Subgroup.inclusion hΓ' δ') (f₂ y) := by
      change π γ (ψ (secAut hD' δ y)) = _
      rw [hψe δ y (secAut hD' δ y) rfl]
      change (π γ) ((π (Subgroup.inclusion hΓ' δ)) (ψ y)) = (π (Subgroup.inclusion hΓ' δ')) ((π γ) (ψ y))
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, e2]
    have h3 : d (secAut hD' δ y) = f₁ (secAut hD' δ y) * (f₂ (secAut hD' δ y))⁻¹ := hd1 _
    have h4 : d y = f₁ y * (f₂ y)⁻¹ := hd1 y
    rw [h3, h4, h1, h2, ← map_inv, ← map_mul]
    exact mem_fixV.1 (hdfix y) _ ((burnsideB46_mem_L H).2 ⟨_, rfl⟩)
  have hker : Subgroup.closure {x | ∃ (δ : ↥⁅quasithinG2 K, quasithinG2 K⁆)
      (y : ↥(FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec), x = secAut hD' δ y * y⁻¹} ≤
      d.ker := by
    refine (Subgroup.closure_le d.ker).2 ?_
    rintro _ ⟨δ, y, rfl⟩
    have key : ∀ a b : ↥(zornO0 K), d (a * b⁻¹) = d a * (d b)⁻¹ := fun a b => by
      rw [map_mul, map_inv]
    exact MonoidHom.mem_ker.2 ((key (secAut hD' δ y) y).trans (by rw [hdδ δ y, mul_inv_cancel]))
  have hdm : d m = 1 :=
    MonoidHom.mem_ker.1 (hker (burnsideB46_n1_gen_O0 e hD' m))
  have h1 : ψ (secAut hD γ m) = π γ (ψ m) := by
    have := hdm
    rw [hd1, mul_inv_eq_one] at this
    exact this
  have h2 : m' = secAut hD γ m := Subtype.ext hm'
  rw [h2]
  exact h1

theorem burnsideB46_part_1c_one
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) : Nat.card V ≤ 2 ^ (7 * n) := by
  haveI : CharP K 2 := burnsideB46_charP H
  obtain ⟨ψ, hψs, -⟩ := burnsideB46_n1_weyl H hn1
  have h1 : Nat.card V ≤ Nat.card ↥(zornO0 K) := Nat.card_le_card_of_surjective ψ hψs
  rw [burnsideB46_card_O0, H.card, ← pow_mul, mul_comm] at h1
  exact h1

theorem burnsideB46_part_1d_one
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) :
    Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
      ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
        (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))) := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro hcard
  obtain ⟨ψ, hψs, hψk, hψe, -⟩ := burnsideB46_n1_weyl H hn1
  have hD := FFModel.zornQ_isActionModel (quasithinG2 K) (le_refl _)
  have hc : Nat.card ↥(zornO0 K) ≤ Nat.card V := by
    rw [burnsideB46_card_O0, H.card, ← pow_mul, mul_comm, hcard]
  have hbij : Function.Bijective ψ := hψs.bijective_of_nat_card_le hc
  refine ⟨(MulEquiv.ofBijective ψ hbij).symm.trans burnsideB46_O0Equiv, fun γ v => ?_⟩
  obtain ⟨m, rfl⟩ := hψs v
  let m' : ↥(zornO0 K) := ⟨zornAct (quasithinG2 K) γ m, hD.sec_inv γ m.1 m.2⟩
  have h1 : ψ m' = π γ (ψ m) := hψe γ m m' rfl
  have e1 : (MulEquiv.ofBijective ψ hbij).symm (ψ m) = m :=
    (MulEquiv.ofBijective ψ hbij).symm_apply_apply m
  have e2 : (MulEquiv.ofBijective ψ hbij).symm (π γ (ψ m)) = m' := by
    rw [← h1]
    exact (MulEquiv.ofBijective ψ hbij).symm_apply_apply m'
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1, e2]
  exact burnsideB46_O0Equiv_act γ m m' rfl

theorem burnsideB46_n1_lift_fix
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) {l : MulAut V} (hl : l ∈ L) {v : V}
    (h : l v * v⁻¹ ∈ fixV L) : l v = v := by
  haveI : CharP K 2 := burnsideB46_charP H
  obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L H).1 hl
  obtain ⟨ψ, hψs, -, hψe, hψθ⟩ := burnsideB46_n1_weyl H hn1
  obtain ⟨m, rfl⟩ := hψs v
  have h1 : θ ((π γ) (ψ m) * (ψ m)⁻¹) = 1 := by
    have : (π γ) (ψ m) * (ψ m)⁻¹ ∈ θ.ker := by rw [H.ker]; exact h
    exact MonoidHom.mem_ker.1 this
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  rw [burnsideB46_theta_act H, hψθ] at h2
  have h3 : g2Act (burnsideB46_cg γ) (zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K)))) =
      zP (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) := by
    have h4 := congrArg burnsideB46_ix h2
    rw [burnsideB46_ix_qAct, burnsideB46_ix_nat] at h4
    simpa [burnsideB46_ix_nat] using h4
  have hm0 : cayleyTr (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) = 0 := m.2
  have h5 := burnsideB46_fix_lift (burnsideB46_cg γ) _ hm0 h3
  have h6 : (m : Multiplicative (quasithinZorn K)) = zornAct (quasithinG2 K) γ m := by
    apply Multiplicative.toAdd.injective
    exact h5.symm
  have h7 := hψe γ m m h6
  exact h7.symm

theorem burnsideB46_part_7_one
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) :
    ∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L := by
  intro i hi _ _
  apply le_antisymm
  · intro v hv
    have h := (burnsideB46_mem_cPre.1 hv) i (Subgroup.mem_zpowers i)
    have h2 := burnsideB46_n1_lift_fix H hn1 hi h
    exact Subgroup.mem_sup_left (mem_fixV_zpowers_iff_apply.2 h2)
  · refine sup_le ?_ ?_
    · intro v hv
      rw [burnsideB46_mem_cPre]
      intro z hz
      rw [mem_fixV.1 hv z hz, mul_inv_cancel]
      exact one_mem _
    · intro v hv
      rw [burnsideB46_mem_cPre]
      intro z hz
      rw [mem_fixV.1 hv z ((Subgroup.zpowers_le.2 hi) hz), mul_inv_cancel]
      exact one_mem _

end N1

section W1G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

@[expose] def burnsideB46_w1g_D (π : ↥(quasithinG2 K) →* MulAut V) : Subgroup (MulAut V) :=
  (π.comp (Subgroup.inclusion (burnsideB46_n1_der_le (K := K)))).range

theorem burnsideB46_w1g_D_le (H : burnsideB46_Hyp V n K G L π θ) :
    burnsideB46_w1g_D π ≤ L := by
  rintro _ ⟨γ, rfl⟩
  exact (burnsideB46_mem_L H).2 ⟨_, rfl⟩

@[expose] noncomputable def burnsideB46_w1g_Dequiv (H : burnsideB46_Hyp V n K G L π θ) :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥(burnsideB46_w1g_D π) :=
  MonoidHom.ofInjective (f := π.comp (Subgroup.inclusion (burnsideB46_n1_der_le (K := K))))
    (H.inj.comp (Subgroup.inclusion_injective _))

theorem burnsideB46_w1g_D_conj (H : burnsideB46_Hyp V n K G L π θ) {l d : MulAut V}
    (hl : l ∈ L) (hd : d ∈ burnsideB46_w1g_D π) : l * d * l⁻¹ ∈ burnsideB46_w1g_D π := by
  obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L H).1 hl
  obtain ⟨δ, rfl⟩ := hd
  refine ⟨⟨(γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) *
    (δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) *
    (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁻¹, burnsideB46_n1_der_conj γ.2 δ.2⟩, ?_⟩
  have : Subgroup.inclusion (burnsideB46_n1_der_le (K := K))
      ⟨(γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) * (δ : quasithinZorn K ≃ₗ[K] quasithinZorn K) *
        (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁻¹, burnsideB46_n1_der_conj γ.2 δ.2⟩ =
      γ * Subgroup.inclusion (burnsideB46_n1_der_le (K := K)) δ * γ⁻¹ := Subtype.ext rfl
  simp only [MonoidHom.comp_apply, this, map_mul, map_inv]

theorem burnsideB46_w1g_isPSU
    [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : IsPSU 3 3 1 ↥(burnsideB46_w1g_D π) :=
  CFSG.Quasithin.SmithC27.isPSU_of_equiv_g2Derived hK (burnsideB46_w1g_Dequiv H).symm

theorem burnsideB46_w1g_simple
    [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : IsSimpleGroup ↥(burnsideB46_w1g_D π) :=
  SBc11.isSimpleGroup_of_list (Or.inr (Or.inr (burnsideB46_w1g_isPSU H hK)))

theorem burnsideB46_w1g_center
    [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : Subgroup.center ↥(burnsideB46_w1g_D π) = ⊥ :=
  SBc11.center_eq_bot_of_list (Or.inr (Or.inr (burnsideB46_w1g_isPSU H hK)))

theorem burnsideB46_w1g_isQuasisimple {S : Type*} [Group S] [IsSimpleGroup S]
    (hZ : Subgroup.center S = ⊥) : CFSG.Open.IsQuasisimple S := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      have hc : Subgroup.center S = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        have hm : ⁅y, x⁆ ∈ commutator S := by
          rw [_root_.commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [h, Subgroup.mem_bot] at hm
        exact commutatorElement_eq_one_iff_mul_comm.1 hm
      obtain ⟨x, hx⟩ : ∃ x : S, x ≠ 1 := exists_ne 1
      have hxc : x ∈ Subgroup.center S := by rw [hc]; trivial
      rw [hZ, Subgroup.mem_bot] at hxc
      exact hx hxc
    · exact h
  · exact (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)).2 inferInstance

theorem burnsideB46_w1g_isComponent
    [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : IsComponentOf (burnsideB46_w1g_D π) L := by
  have hDL := burnsideB46_w1g_D_le H
  haveI := burnsideB46_w1g_simple H hK
  refine ⟨hDL, ?_, burnsideB46_w1g_isQuasisimple (burnsideB46_w1g_center H hK)⟩
  refine IsSubnormal.step hDL ?_ (IsSubnormal.refl L)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).2 fun l hl => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨burnsideB46_w1g_D_conj H hl, fun hd => ?_⟩
  have := burnsideB46_w1g_D_conj H (L.inv_mem hl) hd
  simpa [mul_assoc] using this

theorem burnsideB46_w1g_layerOf_eq
    [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : layerOf L = burnsideB46_w1g_D π :=
  le_antisymm ((burnsideB46_n1_layerOf_le_commutator L).trans (burnsideB46_n1_comm_le_range H))
    (le_sSup (burnsideB46_w1g_isComponent H hK))

theorem burnsideB46_w1g_card_L [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : Nat.card ↥L = 12096 := by
  haveI : CharP K 2 := burnsideB46_charP H
  have e : ↥(quasithinG2 K) ≃* ↥L :=
    (MonoidHom.ofInjective H.inj).trans (MulEquiv.subgroupCongr H.range)
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr (burnsideB46_cg (K := K)).toEquiv,
    card_cayleyGroup, hK]
  norm_num

theorem burnsideB46_w1g_card_le_aut {M : Type*} [Group M] {Y X : Subgroup M}
    (hXY : X ≤ Subgroup.normalizer (Y : Set M))
    (hC : X ⊓ Subgroup.centralizer (Y : Set M) ≤ Y) (hZ : Subgroup.center ↥Y = ⊥)
    [Finite (MulAut ↥Y)] : Nat.card ↥X ≤ Nat.card (MulAut ↥Y) := by
  let φ : ↥X →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hXY)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : Subgroup.inclusion hXY x ∈ Y.normalizerMonoidHom.ker := hx
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    have h2 : (x : M) ∈ X ⊓ Subgroup.centralizer (Y : Set M) := ⟨x.2, h1⟩
    have hxY : (x : M) ∈ Y := hC h2
    have hz : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h1 y y.2)
    rw [hZ, Subgroup.mem_bot] at hz
    have hx1 : (x : M) = 1 := congrArg (Subtype.val : ↥Y → M) hz
    exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
  exact Nat.card_le_card_of_injective φ hφ

theorem burnsideB46_w1g_card_aut
    [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hK : Nat.card K = 2) : Nat.card (MulAut ↥(burnsideB46_w1g_D π)) = 12096 := by
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  let eSU : ↥(burnsideB46_w1g_D π) ≃*
      CFSG.Assembly.LowTwoRank.StatedSU 3 3 CFSG.Quasithin.G2U.F9 :=
    (burnsideB46_w1g_Dequiv H).symm.trans ((Insp9.g2DerivedEquivZMod2 K hK).trans
      ((Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm.trans
        CFSG.Quasithin.G11.P3G2.commutatorG2EquivSU))
  exact CFSG.Quasithin.G11.P3G2.card_mulAut_of_equiv eSU

theorem burnsideB46_w1g_G_eq_L
    [Finite V] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) : G = L := by
  have hK : Nat.card K = 2 := by rw [H.card, hn1, pow_one]
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  have hD := burnsideB46_w1g_layerOf_eq H hK
  have hN : G ≤ Subgroup.normalizer
      ((burnsideB46_w1g_D π : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have := CFSG.Quasithin.le_normalizer_quasithinGenFitting G
    rwa [H.fstar, hD] at this
  have hC : G ⊓ Subgroup.centralizer
      ((burnsideB46_w1g_D π : Subgroup (MulAut V)) : Set (MulAut V)) ≤ burnsideB46_w1g_D π := by
    have := CFSG.Quasithin.centralizer_quasithinGenFitting_le G
    rwa [H.fstar, hD] at this
  haveI : Finite ↥(burnsideB46_w1g_D π) := inferInstance
  haveI : Finite (MulAut ↥(burnsideB46_w1g_D π)) := MulEquiv.finite_left
  have h1 := burnsideB46_w1g_card_le_aut hN hC (burnsideB46_w1g_center H hK)
  rw [burnsideB46_w1g_card_aut H hK] at h1
  have h3 := burnsideB46_w1g_card_L H hK
  exact (Subgroup.eq_of_le_of_card_ge H.le (by omega)).symm

theorem burnsideB46_w1g_layerOf_eq_commutator
    [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) : layerOf L = ⁅L, L⁆ := by
  have hK : Nat.card K = 2 := by rw [H.card, hn1, pow_one]
  exact le_antisymm (burnsideB46_n1_layerOf_le_commutator L)
    ((burnsideB46_n1_comm_le_range H).trans (burnsideB46_w1g_layerOf_eq H hK).ge)

theorem burnsideB46_w1g_normal
    [Finite V] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) :
    ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  intro g hg l hl
  rw [burnsideB46_w1g_G_eq_L H hn1] at hg
  exact L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg)

theorem burnsideB46_w1g_mem_G
    [Finite V] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) {g : MulAut V} :
    g ∈ G ↔ ∃ γ : ↥(quasithinG2 K), π γ = g := by
  rw [burnsideB46_w1g_G_eq_L H hn1]
  exact burnsideB46_mem_L H

end W1G

section Fin1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

section Certs1


theorem burnsideB46_part_1c (H : burnsideB46_Hyp V n K G L π θ) : Nat.card V ≤ 2 ^ (7 * n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact burnsideB46_part_1c_one H (by have := H.one_le; omega)
  · exact burnsideB46_part_1c_ge2 H h

theorem burnsideB46_part_1d (H : burnsideB46_Hyp V n K G L π θ) :
    Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
      ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
        (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact burnsideB46_part_1d_one H (by have := H.one_le; omega)
  · exact burnsideB46_part_1d_ge2 H h

theorem burnsideB46_part_1 (H : burnsideB46_Hyp V n K G L π θ) :
    ((∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
        (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
          ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x)) ∧
      (∀ (c : K), ∀ l ∈ L, ∀ v w : V,
        θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
          θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v)))) ∧
      Nat.card V ≤ 2 ^ (7 * n) ∧
      (Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
        ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
          (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))))) :=
  ⟨burnsideB46_part_1a H, burnsideB46_part_1b H, burnsideB46_part_1c H, burnsideB46_part_1d H⟩

theorem burnsideB46_part_7 (H : burnsideB46_Hyp V n K G L π θ) :
    ∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact burnsideB46_part_7_one H (by have := H.one_le; omega)
  · exact burnsideB46_part_7_ge2 H h

end Certs1

theorem burnsideB46_part_8 (H : burnsideB46_Hyp V n K G L π θ) :
    1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R :=
  fun h => burnsideB46_part_8_ge2 H h h

end Fin1

section OF

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_of_card_pre_set (H : burnsideB46_Hyp V n K G L π θ)
    (P : (Ix3 → K) → Prop) :
    Nat.card {v : V // P (burnsideB46_f θ v)} =
      Nat.card (fixV L) * Nat.card {x : Ix3 → K // P x} := by
  classical
  let s : (Ix3 → K) → V := Function.surjInv (burnsideB46_f_surj H)
  have hs : ∀ x, burnsideB46_f θ (s x) = x := Function.surjInv_eq (burnsideB46_f_surj H)
  have hz : ∀ v : V, v * (s (burnsideB46_f θ v))⁻¹ ∈ fixV L := fun v =>
    (burnsideB46_f_eq_zero_iff H _).1 (by rw [burnsideB46_f_sub, hs, sub_self])
  have hf1 : ∀ (z : fixV L) (x : Ix3 → K), burnsideB46_f θ (z.1 * s x) = x := by
    intro z x
    rw [burnsideB46_f_mul, (burnsideB46_f_eq_zero_iff H _).2 z.2, hs, zero_add]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun v => (⟨v.1 * (s (burnsideB46_f θ v.1))⁻¹, hz v.1⟩, ⟨burnsideB46_f θ v.1, v.2⟩)
      invFun := fun p => ⟨p.1.1 * s p.2.1, by
        show P (burnsideB46_f θ (p.1.1 * s p.2.1))
        rw [hf1]
        exact p.2.2⟩
      left_inv := fun v => Subtype.ext (inv_mul_cancel_right _ _)
      right_inv := fun p => Prod.ext (Subtype.ext (by
          show p.1.1 * s p.2.1 * (s (burnsideB46_f θ (p.1.1 * s p.2.1)))⁻¹ = p.1.1
          rw [hf1]
          exact mul_inv_cancel_right _ _)) (Subtype.ext (hf1 p.1 p.2.1)) }

theorem burnsideB46_of_mem_fixV_iff [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (v : V) :
    v ∈ fixV A ↔ burnsideB46_f θ v ∈ fixSub (A.comap (burnsideB46_pi π)) := by
  rw [mem_fixSub]
  constructor
  · intro hv γ hγ
    rw [← burnsideB46_f_act H γ v, mem_fixV.1 hv _ (Subgroup.mem_comap.1 hγ)]
  · intro hv a ha
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hAL ha)
    refine burnsideB46_lift_fix_ge2 H hn (burnsideB46_pi_mem_L H γ) ?_
    refine (burnsideB46_f_eq_zero_iff H _).1 ?_
    rw [burnsideB46_f_sub, burnsideB46_f_act H, hv γ (Subgroup.mem_comap.2 ha), sub_self]

theorem burnsideB46_of_card_fixV [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    Nat.card (fixV A) =
      Nat.card (fixV L) * Nat.card (fixSub (A.comap (burnsideB46_pi π))) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun v => burnsideB46_of_mem_fixV_iff H hn hAL v)]
  exact burnsideB46_of_card_pre_set H (fun x => x ∈ fixSub (A.comap (burnsideB46_pi π)))

theorem burnsideB46_of_map_comap [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    (A.comap (burnsideB46_pi π)).map (burnsideB46_pi π) = A := by
  refine Subgroup.map_comap_eq_self fun a ha => ?_
  obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hAL ha)
  exact ⟨γ, rfl⟩

theorem burnsideB46_of_card_comap [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    Nat.card (A.comap (burnsideB46_pi π)) = Nat.card A := by
  conv_rhs => rw [← burnsideB46_of_map_comap H hAL]
  exact (Subgroup.card_map_of_injective (burnsideB46_pi_injective H)).symm

theorem burnsideB46_of_comap_elem [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    {A : Subgroup (MulAut V)} (hAe : IsElemAbelian2 A) :
    (∀ γ ∈ A.comap (burnsideB46_pi π), γ * γ = 1) ∧
      ∀ γ ∈ A.comap (burnsideB46_pi π), ∀ δ ∈ A.comap (burnsideB46_pi π), γ * δ = δ * γ := by
  refine ⟨fun γ hγ => burnsideB46_pi_injective H ?_, fun γ hγ δ hδ =>
    burnsideB46_pi_injective H ?_⟩
  · rw [map_mul, map_one, ← sq]
    exact hAe.2 _ (Subgroup.mem_comap.1 hγ)
  · rw [map_mul, map_mul]
    exact hAe.1 _ (Subgroup.mem_comap.1 hγ) _ (Subgroup.mem_comap.1 hδ)

theorem burnsideB46_of_map_elem {Γ : Subgroup ↥(cayleyGroup K)}
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ)
    (φ : ↥(cayleyGroup K) →* MulAut V) : IsElemAbelian2 (Γ.map φ) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    rw [← map_mul, ← map_mul, hΓc γ hγ δ hδ]
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [← map_pow, sq, hΓ1 γ hγ, map_one]

@[expose] noncomputable def burnsideB46_of_fHom (θ : V →* Multiplicative (NatQ K)) :
    V →* Multiplicative (Ix3 → K) where
  toFun v := Multiplicative.ofAdd (burnsideB46_f θ v)
  map_one' := by rw [burnsideB46_f_one]; rfl
  map_mul' v w := by rw [burnsideB46_f_mul]; rfl

theorem burnsideB46_of_fHom_apply (v : V) :
    burnsideB46_of_fHom θ v = Multiplicative.ofAdd (burnsideB46_f θ v) := rfl

theorem burnsideB46_of_fHom_surj (H : burnsideB46_Hyp V n K G L π θ) :
    Function.Surjective (burnsideB46_of_fHom θ) := fun w => by
  obtain ⟨v, hv⟩ := burnsideB46_f_surj H (Multiplicative.toAdd w)
  exact ⟨v, by rw [burnsideB46_of_fHom_apply, hv]; rfl⟩

theorem burnsideB46_of_fHom_eq_iff (H : burnsideB46_Hyp V n K G L π θ) (v w : V) :
    burnsideB46_of_fHom θ v = burnsideB46_of_fHom θ w ↔ v * w⁻¹ ∈ fixV L := by
  rw [← burnsideB46_f_eq_zero_iff H, burnsideB46_f_sub, sub_eq_zero, burnsideB46_of_fHom_apply,
    burnsideB46_of_fHom_apply]
  exact Multiplicative.ofAdd.injective.eq_iff

@[expose] noncomputable def burnsideB46_of_sec (H : burnsideB46_Hyp V n K G L π θ) :
    Multiplicative (Ix3 → K) → V := Function.surjInv (burnsideB46_of_fHom_surj H)

theorem burnsideB46_of_sec_spec (H : burnsideB46_Hyp V n K G L π θ) (w : Multiplicative (Ix3 → K)) :
    burnsideB46_of_fHom θ (burnsideB46_of_sec H w) = w :=
  Function.surjInv_eq (burnsideB46_of_fHom_surj H) w

@[expose] noncomputable def burnsideB46_of_ind (H : burnsideB46_Hyp V n K G L π θ) (g : MulAut V)
    (w : Multiplicative (Ix3 → K)) : Multiplicative (Ix3 → K) :=
  burnsideB46_of_fHom θ (g (burnsideB46_of_sec H w))

theorem burnsideB46_of_ind_apply (H : burnsideB46_Hyp V n K G L π θ) {g : MulAut V}
    (hg : ∀ z ∈ fixV L, g z ∈ fixV L) (v : V) :
    burnsideB46_of_ind H g (burnsideB46_of_fHom θ v) = burnsideB46_of_fHom θ (g v) := by
  unfold burnsideB46_of_ind
  rw [burnsideB46_of_fHom_eq_iff H]
  have h1 : burnsideB46_of_sec H (burnsideB46_of_fHom θ v) * v⁻¹ ∈ fixV L :=
    (burnsideB46_of_fHom_eq_iff H _ _).1 (burnsideB46_of_sec_spec H _)
  have h2 := hg _ h1
  rwa [map_mul, map_inv] at h2

@[expose] noncomputable def burnsideB46_of_indAut (H : burnsideB46_Hyp V n K G L π θ) {g : MulAut V}
    (hg : ∀ z ∈ fixV L, g z ∈ fixV L) (hg' : ∀ z ∈ fixV L, g⁻¹ z ∈ fixV L) :
    MulAut (Multiplicative (Ix3 → K)) where
  toFun := burnsideB46_of_ind H g
  invFun := burnsideB46_of_ind H g⁻¹
  left_inv w := by
    obtain ⟨v, rfl⟩ := burnsideB46_of_fHom_surj H w
    rw [burnsideB46_of_ind_apply H hg, burnsideB46_of_ind_apply H hg', MulAut.inv_apply_self]
  right_inv w := by
    obtain ⟨v, rfl⟩ := burnsideB46_of_fHom_surj H w
    rw [burnsideB46_of_ind_apply H hg', burnsideB46_of_ind_apply H hg, MulAut.apply_inv_self]
  map_mul' a b := by
    obtain ⟨v, rfl⟩ := burnsideB46_of_fHom_surj H a
    obtain ⟨w, rfl⟩ := burnsideB46_of_fHom_surj H b
    rw [← map_mul (burnsideB46_of_fHom θ) v w, burnsideB46_of_ind_apply H hg,
      burnsideB46_of_ind_apply H hg, burnsideB46_of_ind_apply H hg, map_mul, map_mul]

@[expose] noncomputable def burnsideB46_of_PhiFun [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (g : ↥G) :
    MulAut (Multiplicative (Ix3 → K)) :=
  burnsideB46_of_indAut H (burnsideB46_fixV_inv hqs H hn g.2)
    (burnsideB46_fixV_inv hqs H hn (G.inv_mem g.2))

theorem burnsideB46_of_PhiFun_apply [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (g : ↥G) (v : V) :
    burnsideB46_of_PhiFun hqs H hn g (burnsideB46_of_fHom θ v) = burnsideB46_of_fHom θ ((g : MulAut V) v) :=
  burnsideB46_of_ind_apply H (burnsideB46_fixV_inv hqs H hn g.2) v

@[expose] noncomputable def burnsideB46_of_Phi [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    ↥G →* MulAut (Multiplicative (Ix3 → K)) :=
  MonoidHom.mk' (burnsideB46_of_PhiFun hqs H hn) fun g₁ g₂ => by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := burnsideB46_of_fHom_surj H w
    rw [MulAut.mul_apply, burnsideB46_of_PhiFun_apply, burnsideB46_of_PhiFun_apply,
      burnsideB46_of_PhiFun_apply]
    rfl

theorem burnsideB46_of_Phi_apply [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (g : ↥G) (v : V) :
    burnsideB46_of_Phi hqs H hn g (burnsideB46_of_fHom θ v) = burnsideB46_of_fHom θ ((g : MulAut V) v) :=
  burnsideB46_of_PhiFun_apply hqs H hn g v

theorem burnsideB46_of_Phi_injective [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    Function.Injective (burnsideB46_of_Phi hqs H hn) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Subtype.ext (burnsideB46_scalar_eq_one hqs H hn g.2 (c := 1) one_ne_zero fun v => ?_)
  have h1 := burnsideB46_of_Phi_apply hqs H hn g v
  rw [hg] at h1
  rw [one_smul]
  exact (Multiplicative.ofAdd.injective h1).symm

theorem burnsideB46_of_Phi_pi [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (l : ↥G) (γ : ↥(cayleyGroup K))
    (hl : (l : MulAut V) = burnsideB46_pi π γ) (w : Multiplicative (Ix3 → K)) :
    burnsideB46_of_Phi hqs H hn l w = Multiplicative.ofAdd (g2Act γ (Multiplicative.toAdd w)) := by
  obtain ⟨v, rfl⟩ := burnsideB46_of_fHom_surj H w
  rw [burnsideB46_of_Phi_apply, hl]
  simp only [burnsideB46_of_fHom_apply, burnsideB46_f_act H]
  rfl

@[expose] noncomputable def burnsideB46_of_HW [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    Subgroup (MulAut (Multiplicative (Ix3 → K))) :=
  ((burnsideB46_of_Phi hqs H hn).comp (Subgroup.inclusion H.le)).range

theorem burnsideB46_of_mem_HW [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {h : MulAut (Multiplicative (Ix3 → K))} :
    h ∈ burnsideB46_of_HW hqs H hn ↔ ∃ l : ↥G, (l : MulAut V) ∈ L ∧ burnsideB46_of_Phi hqs H hn l = h := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion H.le l, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

@[expose] noncomputable def burnsideB46_of_piW [CharP K 2] [Finite K] [Finite V]
    (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(burnsideB46_of_HW hqs H hn) :=
  (MonoidHom.rangeRestrict ((burnsideB46_of_Phi hqs H hn).comp (Subgroup.inclusion H.le))).comp
    (burnsideB46_piDer H)

theorem burnsideB46_of_isCoordW [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    IsCoord (lmG K) (burnsideB46_of_HW hqs H hn) ⊥ (burnsideB46_of_piW hqs H hn)
      (fun w : Multiplicative (Ix3 → K) => Multiplicative.toAdd w) := by
  have hV := burnsideB46_isCoord H hn
  refine ⟨fun u u' => rfl, fun u => ?_, fun x => ⟨Multiplicative.ofAdd x, rfl⟩, fun γ u => ?_, ?_⟩
  · rw [Subgroup.mem_bot]
    exact ⟨fun h => Multiplicative.toAdd.injective (h.trans toAdd_one.symm), fun h => by
      rw [h]
      rfl⟩
  · obtain ⟨v, rfl⟩ := burnsideB46_of_fHom_surj H u
    have h1 := hV.act γ v
    have h2 : (((burnsideB46_of_piW hqs H hn γ : ↥(burnsideB46_of_HW hqs H hn)) :
        MulAut (Multiplicative (Ix3 → K))) (burnsideB46_of_fHom θ v)) =
        burnsideB46_of_fHom θ (((burnsideB46_piDer H γ : ↥L) : MulAut V) v) :=
      burnsideB46_of_Phi_apply hqs H hn _ v
    exact (congrArg Multiplicative.toAdd h2).trans h1
  · exact (MonoidHom.rangeRestrict_surjective _).comp hV.onto

theorem burnsideB46_of_Phi_normalizes [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (g : ↥G) :
    burnsideB46_of_Phi hqs H hn g ∈
      Subgroup.normalizer ((burnsideB46_of_HW hqs H hn : Subgroup _) : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [burnsideB46_of_mem_HW, burnsideB46_of_mem_HW]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact burnsideB46_normal hqs H hn _ g.2 _ hl
  · rintro ⟨l, hl, hlh⟩
    refine ⟨g⁻¹ * l * g, ?_, ?_⟩
    · have := burnsideB46_normal hqs H hn _ (G.inv_mem g.2) _ hl
      simpa using this
    · rw [map_mul, map_mul, map_inv, hlh]
      group

theorem burnsideB46_of_card_fixV_Phi [CharP K 2] [Finite K] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    Nat.card (fixV ((A.subgroupOf G).map (burnsideB46_of_Phi hqs H hn))) =
      Nat.card (fixSub (A.comap (burnsideB46_pi π))) := by
  have hAG : A ≤ G := hAL.trans H.le
  refine Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd w.1, ?_⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.1, ?_⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  · rw [mem_fixSub]
    intro γ hγ
    have hl : (burnsideB46_pi π γ) ∈ A := Subgroup.mem_comap.1 hγ
    have h1 := mem_fixV.1 w.2 (burnsideB46_of_Phi hqs H hn
      ⟨burnsideB46_pi π γ, H.le (burnsideB46_pi_mem_L H γ)⟩) ⟨_, hl, rfl⟩
    rw [burnsideB46_of_Phi_pi hqs H hn _ γ rfl] at h1
    exact congrArg Multiplicative.toAdd h1
  · rw [mem_fixV]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨γ, hγ⟩ := (burnsideB46_mem_L' H).1 (hAL hg)
    have hγA : γ ∈ A.comap (burnsideB46_pi π) := by
      rw [Subgroup.mem_comap, hγ]
      exact hg
    rw [burnsideB46_of_Phi_pi hqs H hn g γ hγ.symm]
    exact congrArg Multiplicative.ofAdd (mem_fixSub.1 x.2 γ hγA)

theorem burnsideB46_of_offender [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hA : A ≤ G)
    (hAe : CFSG.Quasithin.IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hff : Nat.card V ≤ Nat.card A * Nat.card (CFSG.Quasithin.fixV A)) :
    A ≤ L ∧ Nat.card A = Nat.card K ^ 3 ∧
      Nat.card (CFSG.Quasithin.fixV A) = Nat.card (CFSG.Quasithin.fixV L) * Nat.card K ^ 3 := by
  haveI : CharP K 2 := burnsideB46_charP H
  have hinj := burnsideB46_of_Phi_injective hqs H hn
  set A' : Subgroup (MulAut (Multiplicative (Ix3 → K))) :=
    (A.subgroupOf G).map (burnsideB46_of_Phi hqs H hn) with hA'
  have hA'card : Nat.card A' = Nat.card A := by
    rw [hA', Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hA'e : CFSG.Quasithin.IsElemAbelian2 A' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hAe.1 _ hx _ hy))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (hAe.2 _ hx), map_one]
  have hA'N : A' ≤ Subgroup.normalizer
      ((burnsideB46_of_HW hqs H hn : Subgroup _) : Set (MulAut (Multiplicative (Ix3 → K)))) := by
    rintro _ ⟨g, -, rfl⟩
    exact burnsideB46_of_Phi_normalizes hqs H hn g
  have hA'ne : A' ≠ ⊥ := by
    intro h
    refine hAne (Subgroup.card_eq_one.1 ?_)
    rw [← hA'card]
    exact Subgroup.card_eq_one.2 h
  have hfix : Nat.card (fixV A) ≤ Nat.card (fixV L) * Nat.card (fixV A') := by
    have h1 := burnsideB46_of_card_pre_set H (fun x => Multiplicative.ofAdd x ∈ fixV A')
    have h2 : Nat.card {x : Ix3 → K // Multiplicative.ofAdd x ∈ fixV A'} =
        Nat.card (fixV A') :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun _ => Iff.rfl)
    rw [h2] at h1
    rw [← h1]
    refine Nat.card_le_card_of_injective
      (fun v : fixV A => (⟨v.1, ?_⟩ : {v : V // Multiplicative.ofAdd (burnsideB46_f θ v) ∈ fixV A'}))
      fun v w h => Subtype.ext (Subtype.mk.inj h)
    rw [mem_fixV]
    rintro _ ⟨g, hg, rfl⟩
    have h3 := burnsideB46_of_Phi_apply hqs H hn g v.1
    have h4 : (g : MulAut V) v.1 = v.1 := mem_fixV.1 v.2 _ hg
    rw [h4] at h3
    exact h3
  have hVcard : Nat.card V = Nat.card (fixV L) * Nat.card (Multiplicative (Ix3 → K)) := by
    have h1 := burnsideB46_of_card_pre_set H (fun _ => True)
    have e1 : Nat.card {v : V // True} = Nat.card V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    have e2 : Nat.card {x : Ix3 → K // True} = Nat.card (Multiplicative (Ix3 → K)) :=
      Nat.card_congr ((Equiv.subtypeUnivEquiv fun _ => trivial).trans Multiplicative.ofAdd)
    rw [e1, e2] at h1
    exact h1
  have hpos : 0 < Nat.card (fixV L) := Nat.card_pos
  have hWle : Nat.card (Multiplicative (Ix3 → K)) ≤ Nat.card A' * Nat.card (fixV A') := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card (fixV L) * Nat.card (Multiplicative (Ix3 → K)) = Nat.card V := hVcard.symm
      _ ≤ Nat.card A * Nat.card (fixV A) := hff
      _ ≤ Nat.card A * (Nat.card (fixV L) * Nat.card (fixV A')) := Nat.mul_le_mul_left _ hfix
      _ = Nat.card (fixV L) * (Nat.card A' * Nat.card (fixV A')) := by rw [hA'card]; ring
  obtain ⟨hA'H, hA'3, hfixA'3⟩ :=
    (B42G2.offender_facts H.card hn (burnsideB46_of_isCoordW hqs H hn) hA'N hA'e).2 hA'ne hWle
  have hAL : A ≤ L := by
    intro a ha
    obtain ⟨l, hl, hl'⟩ := (burnsideB46_of_mem_HW hqs H hn).1
      (hA'H (⟨⟨a, hA ha⟩, ha, rfl⟩ : burnsideB46_of_Phi hqs H hn ⟨a, hA ha⟩ ∈ A'))
    have h5 : l = ⟨a, hA ha⟩ := hinj hl'
    rw [show a = (l : MulAut V) from congrArg Subtype.val h5.symm]
    exact hl
  refine ⟨hAL, hA'card ▸ hA'3, ?_⟩
  rw [burnsideB46_of_card_fixV H hn hAL, ← hfixA'3,
    ← burnsideB46_of_card_fixV_Phi hqs H hn hAL]

theorem burnsideB46_of_offender_conj [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hA : A ≤ G)
    (hAe : CFSG.Quasithin.IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hff : Nat.card V ≤ Nat.card A * Nat.card (CFSG.Quasithin.fixV A)) :
    ∃ x : ↥(cayleyGroup K),
      A = ((CFSG.Quasithin.Vol2.Ch11.G2Q8.A1 K).map (MulAut.conj x).toMonoidHom).map
        (burnsideB46_pi π) := by
  obtain ⟨hAL, hcard, hfix⟩ := burnsideB46_of_offender hqs H hn hA hAe hAne hff
  obtain ⟨hΓ1, hΓc⟩ := burnsideB46_of_comap_elem H hAe
  have hΓne : A.comap (burnsideB46_pi π) ≠ ⊥ := by
    intro h
    apply hAne
    rw [← burnsideB46_of_map_comap H hAL, h, Subgroup.map_bot]
  have hΓcard : Nat.card (A.comap (burnsideB46_pi π)) = Nat.card K ^ 3 :=
    (burnsideB46_of_card_comap H hAL).trans hcard
  have hΓfix : Nat.card (fixSub (A.comap (burnsideB46_pi π))) = Nat.card K ^ 3 := by
    have h1 := burnsideB46_of_card_fixV H hn hAL
    rw [hfix] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
  have hoff : Nat.card K ^ 6 ≤
      Nat.card (A.comap (burnsideB46_pi π)) * Nat.card (fixSub (A.comap (burnsideB46_pi π))) := by
    rw [hΓcard, hΓfix, ← pow_add]
  obtain ⟨x, hx⟩ := CFSG.Quasithin.MS93.eq_conj_A1_of_offender H.card (by omega) hΓ1 hΓc hΓne hoff
  exact ⟨x, by rw [← hx]; exact (burnsideB46_of_map_comap H hAL).symm⟩

end OF

section OFa

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)


variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_of_g2Act_inj [CharP K 2] {g h : ↥(cayleyGroup K)}
    (hgh : ∀ w, g2Act g w = g2Act h w) : g = h := by
  have h1 : g * h⁻¹ = 1 := cayley_eq_one fun w => by
    rw [g2Act_mul_apply, hgh, g2Act_apply_inv]
  calc g = g * h⁻¹ * h := by group
    _ = h := by rw [h1, one_mul]

abbrev burnsideB46_of_kE {K : Type} [Field K] [CharP K 2] (α p q' : K) : ↥(cayleyGroup K) :=
  g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)

theorem burnsideB46_of_kE_mul [CharP K 2] (α p q' α' p' q'' : K) (w : Ix3 → K) :
    g2Act (burnsideB46_of_kE α p q' * burnsideB46_of_kE α' p' q'') w =
      g2Act (burnsideB46_of_kE (α + α') (p + p') (q' + q'')) w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [g2Act_mul_apply, q6_eta w, g2Act_A1, g2Act_A1, g2Act_A1]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first | ring1 | linear_combination (-(α * α' * w (.inr 0))) * h2

theorem burnsideB46_of_A1_elem [CharP K 2] :
    (∀ γ ∈ A1 K, γ * γ = 1) ∧ ∀ γ ∈ A1 K, ∀ δ ∈ A1 K, γ * δ = δ * γ := by
  refine ⟨fun γ hγ => ?_, fun γ hγ δ hδ => ?_⟩
  · obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
    refine cayley_eq_one fun w => ?_
    change g2Act (burnsideB46_of_kE α p q' * burnsideB46_of_kE α p q') w = w
    rw [burnsideB46_of_kE_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, q6_eta w, g2Act_A1]
    simp
  · obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
    obtain ⟨α', p', q'', rfl⟩ := exists_eq_of_mem_A1 hδ
    refine burnsideB46_of_g2Act_inj fun w => ?_
    change g2Act (burnsideB46_of_kE α p q' * burnsideB46_of_kE α' p' q'') w =
      g2Act (burnsideB46_of_kE α' p' q'' * burnsideB46_of_kE α p q') w
    rw [burnsideB46_of_kE_mul, burnsideB46_of_kE_mul, add_comm α, add_comm p, add_comm q']

theorem burnsideB46_of_map_map_conj (S : Subgroup ↥(cayleyGroup K)) (a b : ↥(cayleyGroup K)) :
    (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      S.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem burnsideB46_of_map_conj (S : Subgroup ↥(cayleyGroup K)) (y : ↥(cayleyGroup K))
    (φ : ↥(cayleyGroup K) →* MulAut V) :
    (S.map φ).map (MulAut.conj (φ y)).toMonoidHom = (S.map (MulAut.conj y).toMonoidHom).map φ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext s
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem burnsideB46_of_conj_elem {Γ : Subgroup ↥(cayleyGroup K)}
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ)
    (x : ↥(cayleyGroup K)) :
    (∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom, γ * γ = 1) ∧
      ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom, ∀ δ ∈ Γ.map (MulAut.conj x).toMonoidHom,
        γ * δ = δ * γ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    change x * g * x⁻¹ * (x * g * x⁻¹) = 1
    rw [show x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ by group, hΓ1 g hg]
    group
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    change x * g * x⁻¹ * (x * h * x⁻¹) = x * h * x⁻¹ * (x * g * x⁻¹)
    rw [show x * g * x⁻¹ * (x * h * x⁻¹) = x * (g * h) * x⁻¹ by group, hΓc g hg h hh]
    group

theorem burnsideB46_of_card_fixSub_conj [CharP K 2] [Finite K] (x : ↥(cayleyGroup K)) :
    Nat.card K ^ 3 ≤ Nat.card (fixSub ((A1 K).map (MulAut.conj x).toMonoidHom)) := by
  rw [← card_stdF (F := K) (h := 3) (by norm_num)]
  refine Nat.card_le_card_of_injective
    (fun w : stdF K 3 => (⟨g2Act x w.1, ?_⟩ : fixSub ((A1 K).map (MulAut.conj x).toMonoidHom))) ?_
  · rw [mem_fixSub]
    rintro _ ⟨a, ha, rfl⟩
    change g2Act (x * a * x⁻¹) (g2Act x w.1) = g2Act x w.1
    rw [← g2Act_mul_apply, show x * a * x⁻¹ * x = x * a by group, g2Act_mul_apply,
      mem_A1.1 ha _ w.2]
  · intro w w' h
    have h1 : g2Act x w.1 = g2Act x w'.1 := congrArg Subtype.val h
    exact Subtype.ext (by rw [← g2Act_inv_apply x w.1, h1, g2Act_inv_apply])

theorem burnsideB46_of_conj_isOffender [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (x : ↥(cayleyGroup K)) :
    IsFFStarOffender G (((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)) := by
  obtain ⟨hA1sq, hA1c⟩ := burnsideB46_of_A1_elem (K := K)
  obtain ⟨hΓ1, hΓc⟩ := burnsideB46_of_conj_elem hA1sq hA1c x
  have hAL : ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) ≤ L := by
    rintro _ ⟨γ, -, rfl⟩
    exact burnsideB46_pi_mem_L H γ
  have hΓcard : Nat.card ↥((A1 K).map (MulAut.conj x).toMonoidHom) = Nat.card K ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact card_A1
  have hAcard : Nat.card ↥(((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)) =
      Nat.card K ^ 3 := by
    rw [Subgroup.card_map_of_injective (burnsideB46_pi_injective H), hΓcard]
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hAne : ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)) = 1 := by
      rw [h]
      exact Subgroup.card_bot
    have h2 : 1 < Nat.card K ^ 3 := Nat.one_lt_pow (by norm_num) hq
    omega
  have hAe := burnsideB46_of_map_elem hΓ1 hΓc (burnsideB46_pi π)
  refine ⟨hAL.trans H.le, hAne, hAe, fun B hBA => ?_⟩
  have hBL : B ≤ L := hBA.trans hAL
  have hBe : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  obtain ⟨hB1, hBc⟩ := burnsideB46_of_comap_elem H hBe
  have h1 := (card_mul_card_fixSub H.card (by omega) hB1 hBc).1
  have hBc1 := burnsideB46_of_card_comap H hBL
  have hBc2 := burnsideB46_of_card_fixV H hn hBL
  have hcomapA : (((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)).comap
      (burnsideB46_pi π) = (A1 K).map (MulAut.conj x).toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (burnsideB46_pi_injective H) _
  have hAc2 := burnsideB46_of_card_fixV H hn hAL
  rw [hcomapA] at hAc2
  have hge := burnsideB46_of_card_fixSub_conj (K := K) x
  rw [hAcard, hAc2]
  calc Nat.card B * Nat.card (fixV B)
      = Nat.card (fixV L) * (Nat.card (B.comap (burnsideB46_pi π)) *
          Nat.card (fixSub (B.comap (burnsideB46_pi π)))) := by rw [hBc2, hBc1]; ring
    _ ≤ Nat.card (fixV L) * Nat.card K ^ 6 := Nat.mul_le_mul_left _ h1
    _ = Nat.card K ^ 3 * (Nat.card (fixV L) * Nat.card K ^ 3) := by ring
    _ ≤ Nat.card K ^ 3 * (Nat.card (fixV L) *
          Nat.card (fixSub ((A1 K).map (MulAut.conj x).toMonoidHom))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hge)

theorem burnsideB46_part_13a [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    (hF3 : ∀ x : Ix3 → K, x ≠ 0 → burnsideB46_F3 K x ≠ ⊥)
    (hA1 : ∀ x : Ix3 → K, x ≠ 0 → ∃ γ : ↥(cayleyGroup K),
      burnsideB46_A1 K x = (A1 K).map (MulAut.conj γ).toMonoidHom) :
    ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg
  obtain ⟨x, hx0, -, -, -, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  have hA₁ : A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) :=
    burnsideB46_cfg1_A1 hqs H hn (hF3 x hx0) hV₃ hcfg.2.2.2.2.2
  obtain ⟨γ, hγ⟩ := hA1 x hx0
  have hA₁' : A₁ = ((A1 K).map (MulAut.conj γ).toMonoidHom).map (burnsideB46_pi π) := by
    rw [hA₁, hγ]
  ext A
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hAG, hAne, hAe, hB⟩
    have hff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
      have h := hB ⊥ bot_le
      rwa [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top] at h
    obtain ⟨x', hx'⟩ := burnsideB46_of_offender_conj hqs H hn hAG hAe hAne hff
    refine ⟨burnsideB46_pi π (x' * γ⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
    rw [hA₁', burnsideB46_of_map_conj, burnsideB46_of_map_map_conj, inv_mul_cancel_right]
    exact hx'
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨y, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    rw [hA₁', burnsideB46_of_map_conj, burnsideB46_of_map_map_conj]
    exact burnsideB46_of_conj_isOffender H hn _

end OFa

section P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p3_pt_eu : burnsideB46_pt K (eu 0 (1 : K)) = stdF K 1 := by
  ext w
  rw [burnsideB46_pt, Submodule.mem_span_singleton, mem_stdF_one_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

theorem burnsideB46_p3_P1_eu : burnsideB46_P1 K (eu 0 (1 : K)) = stabQ (stdF K 1) := by
  rw [burnsideB46_P1, burnsideB46_p3_pt_eu]

theorem burnsideB46_p3_conj_stabV0 {p s : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1))
    (hs : s ∈ stabV0 K) : p * s * p⁻¹ ∈ stabV0 K := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hp
  have hinv := inv_smul_of_smul hc0 hc
  rw [mem_stabV0, g2Act_mul_apply, g2Act_mul_apply, hinv, JonesParshall.g2Act_smul,
    show g2Act s (eu 0 1) = eu 0 (1 : K) from hs, JonesParshall.g2Act_smul, hc, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

theorem burnsideB46_p3_stabQ_le_normalizer_stabV0 :
    stabQ (stdF K 1) ≤ Subgroup.normalizer (stabV0 K : Set ↥(cayleyGroup K)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact burnsideB46_p3_conj_stabV0 hp hh
  · intro hh
    have := burnsideB46_p3_conj_stabV0 ((stabQ (stdF K 1)).inv_mem hp) hh
    simpa [mul_assoc] using this

theorem burnsideB46_p3_mem_stabV0_of_two_pow {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1))
    {k : ℕ} (hk : p ^ 2 ^ k = 1) : p ∈ stabV0 K := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hp
  have hpow : ∀ m : ℕ, g2Act (p ^ m) (eu 0 (1 : K)) = c ^ m • eu 0 (1 : K) := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, one_smul, map_one]
      rfl
    | succ m ih =>
      rw [pow_succ', g2Act_mul_apply, ih, JonesParshall.g2Act_smul, hc, smul_smul, pow_succ]
  have h1 : c ^ 2 ^ k • eu 0 (1 : K) = eu 0 1 := by
    rw [← hpow, hk, map_one]
    rfl
  have h2 : c ^ 2 ^ k = 1 := by
    have := congrFun h1 (.inl 0)
    simpa [eu] using this
  have h3 : (c - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h2, one_pow, sub_self]
  have h4 : c = 1 := sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k two_ne_zero) |>.mp h3)
  rw [mem_stabV0, hc, h4, one_smul]

theorem burnsideB46_p3_R1_eu [Finite K] :
    burnsideB46_R1 K (eu 0 (1 : K)) = pCoreOf 2 (stabV0 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin := finite_cayleyGroup (F := K)
  rw [burnsideB46_R1, burnsideB46_p3_P1_eu]
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · intro x hx
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (stabQ (stdF K 1)) ⟨x, hx⟩
      exact burnsideB46_p3_mem_stabV0_of_two_pow
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx) (by simpa using congrArg Subtype.val hk)
    · exact stabV0_le_stabQ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans stabV0_le_stabQ
    · exact burnsideB46_p3_stabQ_le_normalizer_stabV0.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (stabV0 K))
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

@[expose] def burnsideB46_p3_kerElt (α β γ p q' : K) : ↥(cayleyGroup K) :=
  g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)

theorem burnsideB46_p3_act_kerElt (α β γ p q' a b c d e f : K) :
    g2Act (burnsideB46_p3_kerElt α β γ p q') (q6 a b c d e f) =
      q6 ((a + p * b + q' * c + β * (f + q' * d) + γ * (e + p * d)) + α * α * d)
        (b + γ * d) (c + β * d) d
        ((e + p * d + (β * b + γ * c) * β) + α * (c + β * d))
        ((f + q' * d + (β * b + γ * c) * γ) + α * (b + γ * d)) :=
  g2Act_kerElt α β γ p q' a b c d e f

theorem burnsideB46_p3_kerElt_mem_stabV0 (α β γ p q' : K) :
    burnsideB46_p3_kerElt α β γ p q' ∈ stabV0 K :=
  (stabV0 K).mul_mem ((stabV0 K).mul_mem (g2X_e0_mem_stabV0 α) (g2Y_mem_stabV0 β γ))
    (g2A_mem_stabV0 (uSL_mulVec_e0 p q' 0))

theorem burnsideB46_p3_levi1Mat_kerElt (α β γ p q' : K) :
    levi1Mat (burnsideB46_p3_kerElt α β γ p q') = 1 := by
  unfold burnsideB46_p3_kerElt
  rw [levi1Mat_decomp (uSL_mulVec_e0 p q' 0), levi1Mat_g2A (uSL_mulVec_e0 p q' 0)]
  have hA : ((uSL p q' 0 : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, p, q'; 0, 1, 0; 0, 0, 1] := rfl
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideB46_p3_mem_R1_eu [Finite K] {g : ↥(cayleyGroup K)} :
    g ∈ burnsideB46_R1 K (eu 0 (1 : K)) ↔
      ∃ α β γ p q' : K, g = burnsideB46_p3_kerElt α β γ p q' := by
  rw [burnsideB46_p3_R1_eu, mem_pCoreOf_stabV0_iff]
  constructor
  · rintro ⟨hg, hM⟩
    exact eq_of_levi1Mat_eq_one hg hM
  · rintro ⟨α, β, γ, p, q', rfl⟩
    exact ⟨burnsideB46_p3_kerElt_mem_stabV0 _ _ _ _ _, burnsideB46_p3_levi1Mat_kerElt _ _ _ _ _⟩

theorem burnsideB46_p3_kerElt_comm_Z (α β γ p q' p₂ q₂ : K) :
    burnsideB46_p3_kerElt 0 0 0 p₂ q₂ * burnsideB46_p3_kerElt α β γ p q' =
      burnsideB46_p3_kerElt α β γ p q' * burnsideB46_p3_kerElt 0 0 0 p₂ q₂ := by
  refine cayley_ext_Q fun w => ?_
  rw [g2Act_mul_apply, g2Act_mul_apply, q6_eta w]
  simp only [burnsideB46_p3_act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p3_center_aux {α β γ p q' : K}
    (h1 : burnsideB46_p3_kerElt α β γ p q' * burnsideB46_p3_kerElt 1 0 0 0 0 =
      burnsideB46_p3_kerElt 1 0 0 0 0 * burnsideB46_p3_kerElt α β γ p q')
    (h2 : burnsideB46_p3_kerElt α β γ p q' * burnsideB46_p3_kerElt 0 1 0 0 0 =
      burnsideB46_p3_kerElt 0 1 0 0 0 * burnsideB46_p3_kerElt α β γ p q') :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have e1 := congrArg (fun g => g2Act g (q6 0 0 0 1 0 0)) h1
  have e2 := congrArg (fun g => g2Act g (q6 0 0 0 1 0 0)) h2
  simp only [g2Act_mul_apply, burnsideB46_p3_act_kerElt] at e1 e2
  obtain ⟨-, -, -, -, e1e, e1f⟩ := q6_inj e1
  obtain ⟨-, -, -, -, e2e, -⟩ := q6_inj e2
  have hβ : β = 0 := by linear_combination (-1 : K) * e1e
  have hγ : γ = 0 := by linear_combination (-1 : K) * e1f
  subst hβ hγ
  have hα : α = 0 := by linear_combination e2e
  exact ⟨hα, rfl, rfl⟩

theorem burnsideB46_p3_kerElt_zero (p q' : K) :
    burnsideB46_p3_kerElt 0 0 0 p q' = g2A (uSL p q' 0) := eq_uSL_of_A1

theorem burnsideB46_p3_Z1_eu [Finite K] : burnsideB46_Z1 K (eu 0 (1 : K)) = Z1 K := by
  ext z
  simp only [burnsideB46_Z1, centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hz, hc⟩
    obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_R1_eu.mp hz
    have hm1 : burnsideB46_p3_kerElt 1 0 0 0 0 ∈ burnsideB46_R1 K (eu 0 (1 : K)) :=
      burnsideB46_p3_mem_R1_eu.mpr ⟨_, _, _, _, _, rfl⟩
    have hm2 : burnsideB46_p3_kerElt 0 1 0 0 0 ∈ burnsideB46_R1 K (eu 0 (1 : K)) :=
      burnsideB46_p3_mem_R1_eu.mpr ⟨_, _, _, _, _, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := burnsideB46_p3_center_aux (hc _ hm1).symm (hc _ hm2).symm
    exact ⟨(p, q'), by rw [burnsideB46_p3_kerElt_zero]⟩
  · rintro ⟨v, rfl⟩
    refine ⟨burnsideB46_p3_mem_R1_eu.mpr ⟨0, 0, 0, v.1, v.2, ?_⟩, fun h hh => ?_⟩
    · rw [burnsideB46_p3_kerElt_zero]
    · obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_R1_eu.mp hh
      rw [← burnsideB46_p3_kerElt_zero v.1 v.2]
      exact (burnsideB46_p3_kerElt_comm_Z α β γ p q' v.1 v.2).symm

theorem burnsideB46_p3_fixSub_Z1 : fixSub (Z1 K) = stdF K 3 := by
  ext w
  rw [mem_fixSub]
  constructor
  · intro h
    have h1 := h (g2A (uSL 1 0 0)) ⟨(1, 0), rfl⟩
    have h2 := h (g2A (uSL 0 1 0)) ⟨(0, 1), rfl⟩
    rw [g2Act_g2A_uSL] at h1 h2
    have e1 := congrFun h1 (.inl 0)
    have e2 := congrFun h1 (.inr 1)
    have e3 := congrFun h2 (.inl 0)
    simp only [q6_apply_inl0, q6_apply_inr1] at e1 e2 e3
    exact mem_stdF_three.mpr ⟨by linear_combination e1, by linear_combination e3,
      by linear_combination e2⟩
  · intro hw γ hγ
    exact Z1_le_A1 hγ w hw

theorem burnsideB46_p3_F3_eu [Finite K] : burnsideB46_F3 K (eu 0 (1 : K)) = stdF K 3 := by
  rw [burnsideB46_F3, burnsideB46_p3_Z1_eu, burnsideB46_p3_fixSub_Z1]

theorem burnsideB46_p3_finrank_stdF_three [Finite K] : Module.finrank K (stdF K 3) = 3 := by
  have h := card_stdF (F := K) (h := 3) (by norm_num)
  have h2 : Nat.card (stdF K 3) = Nat.card K ^ Module.finrank K (stdF K 3) :=
    Module.natCard_eq_pow_finrank
  rw [h2] at h
  exact Nat.pow_right_injective Finite.one_lt_card h

theorem burnsideB46_p3_mem_map_conj {G : Type*} [Group G] {H : Subgroup G} {γ g : G} :
    g ∈ H.map (MulAut.conj γ).toMonoidHom ↔ γ⁻¹ * g * γ ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem burnsideB46_p3_pt_act (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_pt K (g2Act γ x) = gmapG γ (burnsideB46_pt K x) := by
  ext w
  rw [burnsideB46_pt, burnsideB46_pt, Submodule.mem_span_singleton, mem_gmapG,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [JonesParshall.g2Act_smul, g2Act_inv_apply]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← JonesParshall.g2Act_smul, ha, g2Act_apply_inv]⟩

theorem burnsideB46_p3_stabQ_gmapG (γ : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K)) :
    stabQ (gmapG γ S) = (stabQ S).map (MulAut.conj γ).toMonoidHom := by
  ext g
  rw [burnsideB46_p3_mem_map_conj, mem_stabQ, mem_stabQ]
  constructor
  · intro hg w
    have h1 : w ∈ S ↔ g2Act γ w ∈ gmapG γ S := by rw [mem_gmapG, g2Act_inv_apply]
    rw [h1, hg, mem_gmapG, g2Act_mul_apply, g2Act_mul_apply]
  · intro hg w
    have h1 := hg (g2Act γ⁻¹ w)
    rw [mem_gmapG, h1, mem_gmapG, g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv]

theorem burnsideB46_p3_fixSub_map_conj (γ : ↥(cayleyGroup K)) (H : Subgroup ↥(cayleyGroup K)) :
    fixSub (H.map (MulAut.conj γ).toMonoidHom) = gmapG γ (fixSub H) := by
  ext w
  rw [mem_gmapG, mem_fixSub, mem_fixSub]
  constructor
  · intro h g hg
    have h1 := h (γ * g * γ⁻¹) (by rw [burnsideB46_p3_mem_map_conj]; simpa [mul_assoc] using hg)
    rw [g2Act_mul_apply, g2Act_mul_apply] at h1
    have h2 := congrArg (g2Act γ⁻¹) h1
    rwa [g2Act_inv_apply] at h2
  · intro h g hg
    rw [burnsideB46_p3_mem_map_conj] at hg
    have h1 := h _ hg
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv] at h1
    have h2 := congrArg (g2Act γ) h1
    rwa [g2Act_apply_inv, g2Act_apply_inv] at h2

theorem burnsideB46_p3_P1_act (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_P1 K (g2Act γ x) = (burnsideB46_P1 K x).map (MulAut.conj γ).toMonoidHom := by
  rw [burnsideB46_P1, burnsideB46_P1, burnsideB46_p3_pt_act, burnsideB46_p3_stabQ_gmapG]

theorem burnsideB46_p3_R1_act [Finite K] (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_R1 K (g2Act γ x) = (burnsideB46_R1 K x).map (MulAut.conj γ).toMonoidHom := by
  rw [burnsideB46_R1, burnsideB46_R1, burnsideB46_p3_P1_act]
  exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj γ) _

theorem burnsideB46_p3_Z1_act [Finite K] (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_Z1 K (g2Act γ x) = (burnsideB46_Z1 K x).map (MulAut.conj γ).toMonoidHom := by
  rw [burnsideB46_Z1, burnsideB46_Z1, burnsideB46_p3_R1_act]
  exact burnsideB46_centerOf_map _ (MulAut.conj γ).injective _

theorem burnsideB46_p3_F3_act [Finite K] (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_F3 K (g2Act γ x) = gmapG γ (burnsideB46_F3 K x) := by
  rw [burnsideB46_F3, burnsideB46_F3, burnsideB46_p3_Z1_act, burnsideB46_p3_fixSub_map_conj]

theorem burnsideB46_p3_A1_act [Finite K] (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_A1 K (g2Act γ x) = (burnsideB46_A1 K x).map (MulAut.conj γ).toMonoidHom := by
  ext g
  rw [burnsideB46_p3_mem_map_conj]
  change (∀ w ∈ burnsideB46_F3 K (g2Act γ x), g2Act g w = w) ↔
    (∀ w ∈ burnsideB46_F3 K x, g2Act (γ⁻¹ * g * γ) w = w)
  rw [burnsideB46_p3_F3_act]
  constructor
  · intro h w hw
    have hmem : g2Act γ w ∈ gmapG γ (burnsideB46_F3 K x) := by
      rw [mem_gmapG, g2Act_inv_apply]
      exact hw
    have h1 := h _ hmem
    rw [g2Act_mul_apply, g2Act_mul_apply, h1, g2Act_inv_apply]
  · intro h w hw
    rw [mem_gmapG] at hw
    have h1 := h _ hw
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv] at h1
    have h2 := congrArg (g2Act γ) h1
    rwa [g2Act_apply_inv, g2Act_apply_inv] at h2

theorem burnsideB46_p3_finrank_gmapG [Finite K] (γ : ↥(cayleyGroup K))
    (S : Submodule K (Ix3 → K)) : Module.finrank K (gmapG γ S) = Module.finrank K S := by
  have h := card_gmapG γ S
  have h1 : Nat.card (gmapG γ S) = Nat.card K ^ Module.finrank K (gmapG γ S) :=
    Module.natCard_eq_pow_finrank
  have h2 : Nat.card S = Nat.card K ^ Module.finrank K S := Module.natCard_eq_pow_finrank
  rw [h1, h2] at h
  exact Nat.pow_right_injective Finite.one_lt_card h

theorem burnsideB46_p3_F3_card [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    Module.finrank K (burnsideB46_F3 K x) = 3 := by
  obtain ⟨γ, hγ⟩ := exists_g2Act_eu_eq hx
  rw [← hγ, burnsideB46_p3_F3_act, burnsideB46_p3_finrank_gmapG, burnsideB46_p3_F3_eu,
    burnsideB46_p3_finrank_stdF_three]

theorem burnsideB46_p3_A1_conj [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) {x : Ix3 → K} (hx : x ≠ 0) :
    ∃ γ : ↥(cayleyGroup K),
      burnsideB46_A1 K x =
        (CFSG.Quasithin.Vol2.Ch11.G2Q8.A1 K).map (MulAut.conj γ).toMonoidHom := by
  obtain ⟨γ, hγ⟩ := exists_g2Act_eu_eq hx
  refine ⟨γ, ?_⟩
  rw [← hγ, burnsideB46_p3_A1_act]
  congr 1
  ext g
  change (∀ w ∈ burnsideB46_F3 K (eu 0 (1 : K)), g2Act g w = w) ↔ _
  rw [burnsideB46_p3_F3_eu]
  exact Iff.rfl

end P3

section P3a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB

@[expose] def burnsideB46_p3_NatQ (K : Type) [Field K] (k : ℕ) {M : Type*} [Group M]
    (P R Y A : Subgroup M) : Prop :=
  R ≤ P ∧ A ≤ Y ∧ P ≤ Subgroup.normalizer (Y : Set M) ∧ P ≤ Subgroup.normalizer (A : Set M) ∧
    ∃ (ρ : ↥P →* GL (Fin 2) K) (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
      Function.Surjective ρ ∧ ρ.ker = R.subgroupOf P ∧ Function.Surjective ζ ∧
      ζ.ker = A.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : M) = (p : M) * (y : M) * (p : M)⁻¹ →
        ζ y' = Multiplicative.ofAdd
          ((((ρ p : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ^ k) •
            (((ρ p : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
              (Multiplicative.toAdd (ζ y))))

@[expose] def burnsideB46_p3_IsNatGL2QuotTw (K : Type) [Field K] (k : ℕ) {M : Type*} [Group M]
    (P R Y A : Subgroup M) : Prop :=
  R ≤ P ∧ A ≤ Y ∧ P ≤ Subgroup.normalizer (Y : Set M) ∧ P ≤ Subgroup.normalizer (A : Set M) ∧
    ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
      Function.Surjective ζ ∧ ζ.ker = A.subgroupOf Y ∧
        ∀ (p : ↥P) (y y' : ↥Y), (y' : M) = (p : M) * (y : M) * (p : M)⁻¹ →
          ζ y' = Multiplicative.ofAdd
            ((((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ^ k) •
              (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
                (Multiplicative.toAdd (ζ y))))

section NatQ

variable {M : Type*} [Group M] {K : Type} [Field K]

theorem burnsideB46_p3_isNatGL2QuotTw_iff {k : ℕ} {P R Y A : Subgroup M} :
    burnsideB46_p3_IsNatGL2QuotTw K k P R Y A ↔ burnsideB46_p3_NatQ K k P R Y A := by
  unfold burnsideB46_p3_IsNatGL2QuotTw burnsideB46_p3_NatQ
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  constructor
  · rintro ⟨hN, θ', ζ, hζs, hζk, hζ⟩
    refine ⟨θ'.toMonoidHom.comp (QuotientGroup.mk' (R.subgroupOf P)), ζ, ?_, ?_, hζs, hζk, hζ⟩
    · intro g
      obtain ⟨q, hq⟩ := θ'.surjective g
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨p, hq⟩
    · ext p
      rw [MonoidHom.mem_ker]
      change θ' (QuotientGroup.mk p) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  · rintro ⟨ρ, ζ, hρs, hρk, hζs, hζk, hζ⟩
    have hN : (R.subgroupOf P).Normal := by
      rw [← hρk]
      exact MonoidHom.normal_ker ρ
    refine ⟨hN, (QuotientGroup.quotientMulEquivOfEq hρk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs), ζ, hζs, hζk, ?_⟩
    intro p y y' h
    have := hζ p y y' h
    exact this

theorem burnsideB46_p3_isNatGL2Quot_iff {P R Y A : Subgroup M} :
    IsNatGL2Quot K P R Y A ↔ burnsideB46_p3_NatQ K 0 P R Y A := by
  rw [← burnsideB46_p3_isNatGL2QuotTw_iff]
  unfold burnsideB46_p3_IsNatGL2QuotTw IsNatGL2Quot
  simp only [pow_zero, one_smul]

theorem burnsideB46_p3_le_normalizer_iff {P Y : Subgroup M} :
    P ≤ Subgroup.normalizer (Y : Set M) ↔ ∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y := by
  constructor
  · intro h p hp y hy
    exact (Subgroup.mem_normalizer_iff.mp (h hp) y).mp hy
  · intro h p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨h p hp y, fun hy => ?_⟩
    have := h p⁻¹ (P.inv_mem hp) _ hy
    simpa [mul_assoc] using this

theorem burnsideB46_p3_map_le_normalizer_iff {N : Type*} [Group N] {φ : M →* N}
    (hφ : Function.Injective φ) {P Y : Subgroup M} :
    P.map φ ≤ Subgroup.normalizer ((Y.map φ : Subgroup N) : Set N) ↔
      P ≤ Subgroup.normalizer (Y : Set M) := by
  rw [burnsideB46_p3_le_normalizer_iff, burnsideB46_p3_le_normalizer_iff]
  constructor
  · intro h p hp y hy
    have := h (φ p) ⟨p, hp, rfl⟩ (φ y) ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at this
    exact (Subgroup.mem_map_iff_mem hφ).mp this
  · rintro h _ ⟨p, hp, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨p * y * p⁻¹, h p hp y hy, by simp⟩

theorem burnsideB46_p3_NatQ_map {N : Type*} [Group N] (φ : M →* N) (hφ : Function.Injective φ)
    (k : ℕ) (P R Y A : Subgroup M) :
    burnsideB46_p3_NatQ K k (P.map φ) (R.map φ) (Y.map φ) (A.map φ) ↔
      burnsideB46_p3_NatQ K k P R Y A := by
  unfold burnsideB46_p3_NatQ
  rw [Subgroup.map_le_map_iff_of_injective hφ, Subgroup.map_le_map_iff_of_injective hφ,
    burnsideB46_p3_map_le_normalizer_iff hφ, burnsideB46_p3_map_le_normalizer_iff hφ]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  let eP := P.equivMapOfInjective φ hφ
  let eY := Y.equivMapOfInjective φ hφ
  have hP : ∀ p : ↥P, ((eP p : ↥(P.map φ)) : N) = φ p :=
    fun p => Subgroup.coe_equivMapOfInjective_apply P φ hφ p
  have hY : ∀ y : ↥Y, ((eY y : ↥(Y.map φ)) : N) = φ y :=
    fun y => Subgroup.coe_equivMapOfInjective_apply Y φ hφ y
  constructor
  · rintro ⟨ρ', ζ', hρs, hρk, hζs, hζk, hconj⟩
    refine ⟨ρ'.comp eP.toMonoidHom, ζ'.comp eY.toMonoidHom, hρs.comp eP.surjective, ?_,
      hζs.comp eY.surjective, ?_, ?_⟩
    · ext p
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change ρ' (eP p) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hρk, Subgroup.mem_subgroupOf, hP]
      exact Subgroup.mem_map_iff_mem hφ
    · ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change ζ' (eY y) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hζk, Subgroup.mem_subgroupOf, hY]
      exact Subgroup.mem_map_iff_mem hφ
    · intro p y y' h
      exact hconj (eP p) (eY y) (eY y') (by rw [hY, hY, hP, h, map_mul, map_mul, map_inv])
  · rintro ⟨ρ, ζ, hρs, hρk, hζs, hζk, hconj⟩
    refine ⟨ρ.comp eP.symm.toMonoidHom, ζ.comp eY.symm.toMonoidHom, hρs.comp eP.symm.surjective, ?_,
      hζs.comp eY.symm.surjective, ?_, ?_⟩
    · ext q
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change ρ (eP.symm q) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hρk, Subgroup.mem_subgroupOf]
      have : (q : N) = φ ((eP.symm q : ↥P) : M) := by
        rw [← hP, MulEquiv.apply_symm_apply]
      rw [this]
      exact (Subgroup.mem_map_iff_mem hφ).symm
    · ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change ζ (eY.symm y) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hζk, Subgroup.mem_subgroupOf]
      have : (y : N) = φ ((eY.symm y : ↥Y) : M) := by
        rw [← hY, MulEquiv.apply_symm_apply]
      rw [this]
      exact (Subgroup.mem_map_iff_mem hφ).symm
    · intro q y y' h
      have hq : (q : N) = φ ((eP.symm q : ↥P) : M) := by rw [← hP, MulEquiv.apply_symm_apply]
      have hy : (y : N) = φ ((eY.symm y : ↥Y) : M) := by rw [← hY, MulEquiv.apply_symm_apply]
      have hy' : (y' : N) = φ ((eY.symm y' : ↥Y) : M) := by rw [← hY, MulEquiv.apply_symm_apply]
      refine hconj (eP.symm q) (eY.symm y) (eY.symm y') (hφ ?_)
      rw [← hy', map_mul, map_mul, map_inv, ← hq, ← hy]
      exact h

end NatQ

section MaxPar

variable {M N : Type} [Group M] [Group N]

theorem burnsideB46_p3_mem_normalizer_map_iff {φ : M →* N} (hφ : Function.Injective φ)
    {S : Subgroup M} {l : M} :
    φ l ∈ Subgroup.normalizer ((S.map φ : Subgroup N) : Set N) ↔
      l ∈ Subgroup.normalizer (S : Set M) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h s
    have := h (φ s)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hφ,
      Subgroup.mem_map_iff_mem hφ] at this
    exact this
  · rintro h _
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨l * s * l⁻¹, (h s).mp hs, by simp⟩
    · rintro ⟨s, hs, hse⟩
      refine ⟨l⁻¹ * s * l, ?_, ?_⟩
      · have := (h (l⁻¹ * s * l)).mpr (by simpa [mul_assoc] using hs)
        exact this
      · rw [map_mul, map_mul, map_inv, hse]
        simp [mul_assoc]

theorem burnsideB46_p3_isSylowTwoOf_map {φ : M →* N} (hφ : Function.Injective φ)
    {S L : Subgroup M} : IsSylowTwoOf (S.map φ) (L.map φ) ↔ IsSylowTwoOf S L := by
  unfold IsSylowTwoOf
  rw [Subgroup.map_le_map_iff_of_injective hφ]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h
      exact h.of_equiv (S.equivMapOfInjective φ hφ).symm
    · intro h
      exact h.map φ
  · change ¬ 2 ∣ (S.map φ).relIndex (L.map φ) ↔ ¬ 2 ∣ S.relIndex L
    rw [Subgroup.relIndex_map_map_of_injective S L hφ]

theorem burnsideB46_p3_isMaxParabolic2_map {φ : M →* N} (hφ : Function.Injective φ)
    {L P : Subgroup M} (h : IsMaxParabolic2 L P) : IsMaxParabolic2 (L.map φ) (P.map φ) := by
  obtain ⟨⟨hPL, S, hS, hN⟩, hne, hmax⟩ := h
  refine ⟨⟨Subgroup.map_mono hPL, S.map φ, (burnsideB46_p3_isSylowTwoOf_map hφ).mpr hS, ?_⟩,
    fun h => hne (Subgroup.map_injective hφ h), ?_⟩
  · rintro _ ⟨⟨l, hl, rfl⟩, hq⟩
    exact ⟨l, hN ⟨hl, (burnsideB46_p3_mem_normalizer_map_iff hφ).mp hq⟩, rfl⟩
  · intro Q' hQ' hQ'ne hPQ'
    obtain ⟨hQ'L, S', hS', hN'⟩ := hQ'
    have hLr : L.map φ ≤ φ.range := Subgroup.map_le_range φ L
    have hQQ' : (Q'.comap φ).map φ = Q' := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (hQ'L.trans hLr)
    have hSS' : (S'.comap φ).map φ = S' := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (hS'.1.trans hLr)
    have hpar : IsParabolic2 L (Q'.comap φ) := by
      refine ⟨fun x hx => ?_, S'.comap φ, ?_, ?_⟩
      · exact (Subgroup.mem_map_iff_mem hφ).mp (hQ'L hx)
      · rw [← burnsideB46_p3_isSylowTwoOf_map hφ, hSS']
        exact hS'
      · rintro l ⟨hl, hln⟩
        have h1 : φ l ∈ L.map φ ⊓ Subgroup.normalizer (S' : Set N) := by
          refine ⟨⟨l, hl, rfl⟩, ?_⟩
          rw [← hSS']
          exact (burnsideB46_p3_mem_normalizer_map_iff hφ).mpr hln
        exact hN' h1
    have hne' : Q'.comap φ ≠ L := by
      intro hc
      apply hQ'ne
      rw [← hQQ', hc]
    have hPQ : P ≤ Q'.comap φ := Subgroup.map_le_iff_le_comap.mp hPQ'
    have := hmax _ hpar hne' hPQ
    rw [← hQQ', this]

theorem burnsideB46_p3_isElemAbelian_map {φ : M →* N} {A : Subgroup M}
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map φ) := by
  obtain ⟨hc, hx⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx', hxa⟩ := a.2
    obtain ⟨y, hy', hyb⟩ := b.2
    apply Subtype.ext
    change (a : N) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx'⟩ ⟨y, hy'⟩)
  · rintro _ ⟨x, hx', rfl⟩
    rw [← map_pow, hx x hx', map_one]

end MaxPar

end P3a

section P3b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

@[expose] def burnsideB46_p3_z3 {ω : K} (h : ω ^ 3 = 1) : ↥(cayleyGroup K) :=
  g2A (diag3 ω ω ω (by rw [← h]; ring))

theorem burnsideB46_p3_act_z3 {ω : K} (h : ω ^ 3 = 1) (a b c d e f : K) :
    g2Act (burnsideB46_p3_z3 h) (q6 a b c d e f) =
      q6 (ω * a) (ω * b) (ω * c) (ω * ω * d) (ω * ω * e) (ω * ω * f) :=
  g2Act_diag3 _ _ _ _ _ _ _

theorem burnsideB46_p3_z3_mem_stabQ {ω : K} (h : ω ^ 3 = 1) :
    burnsideB46_p3_z3 h ∈ stabQ (stdF K 1) := by
  have hω : ω ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  rw [mem_stabQ]
  intro w
  conv_lhs => rw [mem_stdF, q6_eta w, inF_q6_iff]
  rw [q6_eta w, burnsideB46_p3_act_z3, mem_stdF, inF_q6_iff]
  simp only [mul_eq_zero, hω, false_or]
  simp [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2]

theorem burnsideB46_p3_z3_not_mem_stabV0 {ω : K} (h : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    burnsideB46_p3_z3 h ∉ stabV0 K := by
  intro hz
  rw [mem_stabV0, eu_eq_q6, burnsideB46_p3_act_z3] at hz
  have := congrFun hz (.inl 0)
  simp only [q6_apply_inl0] at this
  exact h1 (by linear_combination this)

theorem burnsideB46_p3_z3_comm {ω : K} (h : ω ^ 3 = 1) (p q' : K) :
    g2A (uSL p q' 0) * burnsideB46_p3_z3 h = burnsideB46_p3_z3 h * g2A (uSL p q' 0) := by
  unfold burnsideB46_p3_z3
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (uSL p q' 0 : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ![ω, ω, ω] =
    Matrix.diagonal ![ω, ω, ω] * (uSL p q' 0 : Matrix (Fin 3) (Fin 3) K)
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem burnsideB46_p3_not_isNatGL2Quot_Z1_eu [Finite K] {ω : K} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ¬ IsNatGL2Quot K (burnsideB46_P1 K (eu 0 (1 : K))) (burnsideB46_R1 K (eu 0 (1 : K)))
      (burnsideB46_Z1 K (eu 0 (1 : K))) ⊥ := by
  rw [burnsideB46_p3_isNatGL2Quot_iff]
  rintro ⟨-, -, -, -, ρ, ζ, hρs, hρk, hζs, hζk, hζ⟩
  have hzP : burnsideB46_p3_z3 h3 ∈ burnsideB46_P1 K (eu 0 (1 : K)) := by
    rw [burnsideB46_p3_P1_eu]
    exact burnsideB46_p3_z3_mem_stabQ h3
  set p : ↥(burnsideB46_P1 K (eu 0 (1 : K))) := ⟨_, hzP⟩ with hp
  have hvec : ∀ v : Fin 2 → K, ((ρ p : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v = v := by
    intro v
    obtain ⟨y, hy⟩ := hζs (Multiplicative.ofAdd v)
    have hy' : ((y : ↥(cayleyGroup K)) ) = (p : ↥(cayleyGroup K)) * (y : ↥(cayleyGroup K)) *
        (p : ↥(cayleyGroup K))⁻¹ := by
      have hyz : (y : ↥(cayleyGroup K)) ∈ Z1 K :=
        (SetLike.ext_iff.mp (burnsideB46_p3_Z1_eu (K := K)) _).mp y.2
      obtain ⟨u, hu⟩ := hyz
      rw [hu]
      change _ = burnsideB46_p3_z3 h3 * _ * (burnsideB46_p3_z3 h3)⁻¹
      rw [← burnsideB46_p3_z3_comm h3, mul_assoc, mul_inv_cancel, mul_one]
    have := hζ p y y hy'
    rw [hy, pow_zero, one_smul] at this
    exact (Multiplicative.ofAdd.injective this).symm
  have hone : ((ρ p : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    have := congrFun (hvec (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hρ1 : ρ p = 1 := Units.ext hone
  have hmem : p ∈ ρ.ker := hρ1
  rw [hρk, Subgroup.mem_subgroupOf] at hmem
  have hR : burnsideB46_p3_z3 h3 ∈ pCoreOf 2 (stabV0 K) := by
    rw [← burnsideB46_p3_R1_eu]
    exact hmem
  exact burnsideB46_p3_z3_not_mem_stabV0 h3 h1
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (stabV0 K) hR)

theorem burnsideB46_p3_mem_F3 {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1)) {w : Ix3 → K}
    (hw : w ∈ stdF K 3) : g2Act p w ∈ stdF K 3 := by
  rw [stabQ_one_eq_three] at hp
  exact (mem_stabQ.mp hp w).mp hw

theorem burnsideB46_p3_vpart_act {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1)) {w : Ix3 → K}
    (hw : w ∈ stdF K 3) : vpart (g2Act p w) = (levi1Mat p).mulVec (vpart w) := by
  obtain ⟨c, -, hc⟩ := exists_smul_of_mem_stabQ_one hp
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  have hw' : w = q6 (w (.inl 0)) 0 0 0 (w (.inr 1)) (w (.inr 2)) := by
    conv_lhs => rw [q6_eta w]
    rw [h1, h2, h3]
  have hvu : vpart (eu 0 (1 : K)) = 0 := by
    funext i
    fin_cases i <;> rfl
  rw [hw', q6_F3_decomp, map_add, map_add, JonesParshall.g2Act_smul, JonesParshall.g2Act_smul,
    JonesParshall.g2Act_smul, hc]
  simp only [vpart_add, vpart_smul, hvu, smul_zero, zero_add]
  funext i
  fin_cases i <;>
    (simp [vpart, levi1Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, q6]; try ring)

theorem burnsideB46_p3_levi1Mat_mul {p q : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1))
    (hq : q ∈ stabQ (stdF K 1)) : levi1Mat (p * q) = levi1Mat p * levi1Mat q := by
  ext i j
  have hmem : q6 (0 : K) 0 0 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) ∈ stdF K 3 :=
    mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have e1 : levi1Mat (p * q) i j =
      vpart (g2Act p (g2Act q (q6 0 0 0 0 (if j = 0 then 1 else 0)
        (if j = 1 then 1 else 0)))) i := by
    rw [← g2Act_mul_apply]
    rfl
  rw [e1, burnsideB46_p3_vpart_act hp (burnsideB46_p3_mem_F3 hq hmem), Matrix.mul_apply,
    Matrix.mulVec, dotProduct]
  rfl

@[expose] noncomputable def burnsideB46_p3_levi :
    ↥(stabQ (stdF K 1)) →* Matrix (Fin 2) (Fin 2) K where
  toFun p := levi1Mat p.1
  map_one' := levi1Mat_one
  map_mul' p q := burnsideB46_p3_levi1Mat_mul p.2 q.2

@[expose] noncomputable def burnsideB46_p3_rho : ↥(stabQ (stdF K 1)) →* GL (Fin 2) K :=
  burnsideB46_p3_levi.toHomUnits

theorem burnsideB46_p3_rho_apply (p : ↥(stabQ (stdF K 1))) :
    ((burnsideB46_p3_rho p : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = levi1Mat p.1 :=
  rfl

@[expose] def burnsideB46_p3_c (p : ↥(cayleyGroup K)) : K := g2Act p (eu 0 1) (.inl 0)

theorem burnsideB46_p3_act_eu {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1)) :
    g2Act p (eu 0 1) = burnsideB46_p3_c p • eu 0 (1 : K) ∧ burnsideB46_p3_c p ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hp
  have hcc : burnsideB46_p3_c p = c := by
    unfold burnsideB46_p3_c
    rw [hc]
    simp [eu]
  rw [hcc]
  exact ⟨hc, hc0⟩

theorem burnsideB46_p3_c_mul {p q : ↥(cayleyGroup K)} (hq : q ∈ stabQ (stdF K 1))
    (hp : p ∈ stabQ (stdF K 1)) :
    burnsideB46_p3_c (p * q) = burnsideB46_p3_c p * burnsideB46_p3_c q := by
  obtain ⟨hq1, -⟩ := burnsideB46_p3_act_eu hq
  obtain ⟨hp1, -⟩ := burnsideB46_p3_act_eu hp
  unfold burnsideB46_p3_c
  rw [g2Act_mul_apply, hq1, JonesParshall.g2Act_smul, hp1]
  simp [mul_comm]

theorem burnsideB46_p3_levi1Mat_tG (u : Kˣ) :
    levi1Mat (tG u) = Matrix.diagonal ![(u : K), 1] := by
  have key : ∀ a b c d e f : K, g2Act (tG u) (q6 a b c d e f) =
      q6 ((u : K) * a) (((u⁻¹ : Kˣ) : K) * b) (1 * c) (((u⁻¹ : Kˣ) : K) * 1 * d)
        ((u : K) * 1 * e) ((u : K) * ((u⁻¹ : Kˣ) : K) * f) :=
    fun a b c d e f => g2Act_diag3 _ _ _ _ _ _ _
  ext i j
  simp only [levi1Mat_apply, key]
  fin_cases i <;> fin_cases j <;> simp [vpart, q6]

theorem burnsideB46_p3_tG_mem_stabQ (u : Kˣ) : tG u ∈ stabQ (stdF K 1) :=
  mem_stabQ.mpr fun w => (tG_mem_stab u w).symm

theorem burnsideB46_p3_det_levi {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1)) :
    (levi1Mat p).det = burnsideB46_p3_c p := by
  obtain ⟨hc, hc0⟩ := burnsideB46_p3_act_eu hp
  set u : Kˣ := Units.mk0 _ hc0 with hu
  have ht : tG u ∈ stabQ (stdF K 1) := burnsideB46_p3_tG_mem_stabQ u
  have hs : p * (tG u)⁻¹ ∈ stabV0 K := by
    rw [mem_stabV0, g2Act_mul_apply, tG_inv, g2Act_tG_eu, ← smul_eu, JonesParshall.g2Act_smul, hc,
      smul_smul]
    have : (((u⁻¹ : Kˣ) : K)) * burnsideB46_p3_c p = 1 := by
      rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0]
      exact inv_mul_cancel₀ hc0
    rw [this, one_smul]
  have hS' : p * (tG u)⁻¹ ∈ stabQ (stdF K 1) := stabV0_le_stabQ hs
  have hP : p = (p * (tG u)⁻¹) * tG u := by group
  have hm := burnsideB46_p3_levi1Mat_mul hS' ht
  rw [← hP] at hm
  rw [hm, Matrix.det_mul, det_levi1Mat hs, burnsideB46_p3_levi1Mat_tG, Matrix.det_diagonal,
    Fin.prod_univ_two]
  simp [hu]

theorem burnsideB46_p3_rho_ker [Finite K] :
    (burnsideB46_p3_rho (K := K)).ker =
      (pCoreOf 2 (stabV0 K)).subgroupOf (stabQ (stdF K 1)) := by
  ext p
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_pCoreOf_stabV0_iff]
  constructor
  · intro h
    have h1 : levi1Mat p.1 = 1 := by
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h
      exact this
    refine ⟨?_, h1⟩
    obtain ⟨hc, hc0⟩ := burnsideB46_p3_act_eu p.2
    have h2 := burnsideB46_p3_det_levi p.2
    rw [h1, Matrix.det_one] at h2
    rw [mem_stabV0, hc, ← h2, one_smul]
  · rintro ⟨-, h1⟩
    exact Units.ext h1

theorem burnsideB46_p3_rho_surjective [Finite K] :
    Function.Surjective (burnsideB46_p3_rho (K := K)) := by
  intro B
  set Bm : Matrix (Fin 2) (Fin 2) K := (B : Matrix (Fin 2) (Fin 2) K) with hBm
  have hdet : Bm.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det Bm).mp B.isUnit).ne_zero
  set δ : K := Bm.det with hδ
  let N : Matrix (Fin 2) (Fin 2) K := Bm * Matrix.diagonal ![δ⁻¹, 1]
  have hN : N.det = 1 := by
    simp only [N, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]
    simp [← hδ, hdet]
  obtain ⟨s, hs⟩ := levi1_surjective (F := K) ⟨N, hN⟩
  set u : Kˣ := Units.mk0 δ hdet with hu
  have hsP : s.1 ∈ stabQ (stdF K 1) := stabV0_le_stabQ s.2
  have htP : tG u ∈ stabQ (stdF K 1) := burnsideB46_p3_tG_mem_stabQ u
  refine ⟨⟨s.1 * tG u, (stabQ (stdF K 1)).mul_mem hsP htP⟩, Units.ext ?_⟩
  rw [burnsideB46_p3_rho_apply]
  change levi1Mat (s.1 * tG u) = Bm
  rw [burnsideB46_p3_levi1Mat_mul hsP htP, burnsideB46_p3_levi1Mat_tG]
  have h1 : levi1Mat s.1 = N := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hs
    exact this
  rw [h1]
  simp only [N]
  have hd : Matrix.diagonal ![δ⁻¹, 1] * Matrix.diagonal ![((u : Kˣ) : K), 1] =
      (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hu, hdet]
  rw [Matrix.mul_assoc, hd, Matrix.mul_one]

end P3b

section P3c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p3_mem_core_iff [Finite K] {g : ↥(cayleyGroup K)} :
    g ∈ pCoreOf 2 (stabV0 K) ↔ ∃ α β γ p q' : K, g = burnsideB46_p3_kerElt α β γ p q' := by
  rw [← burnsideB46_p3_R1_eu]
  exact burnsideB46_p3_mem_R1_eu

theorem burnsideB46_p3_kerElt_v0 (α β γ p q' : K) :
    g2Act (burnsideB46_p3_kerElt α β γ p q') (q6 0 0 0 1 0 0) =
      q6 (β * q' + γ * p + α * α) γ β 1 (p + α * β) (q' + α * γ) := by
  rw [burnsideB46_p3_act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p3_kerElt_u1 (α β γ p q' : K) :
    g2Act (burnsideB46_p3_kerElt α β γ p q') (q6 0 1 0 0 0 0) =
      q6 p 1 0 0 (β * β) (β * γ + α) := by
  rw [burnsideB46_p3_act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p3_core_coords [Finite K] {r : ↥(cayleyGroup K)}
    (hr : r ∈ pCoreOf 2 (stabV0 K)) (w : Ix3 → K) :
    g2Act r w (.inr 0) = w (.inr 0) ∧
      g2Act r w (.inl 2) = w (.inl 2) + g2Act r (q6 0 0 0 1 0 0) (.inl 2) * w (.inr 0) ∧
      g2Act r w (.inl 1) = w (.inl 1) + g2Act r (q6 0 0 0 1 0 0) (.inl 1) * w (.inr 0) := by
  obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_core_iff.mp hr
  have h := burnsideB46_p3_act_kerElt α β γ p q' (w (.inl 0)) (w (.inl 1)) (w (.inl 2))
    (w (.inr 0)) (w (.inr 1)) (w (.inr 2))
  rw [← q6_eta w] at h
  rw [h, burnsideB46_p3_kerElt_v0]
  refine ⟨?_, ?_, ?_⟩
  · simp only [q6_apply_inr0]
  · simp only [q6_apply_inl2, q6_apply_inr0]
  · simp only [q6_apply_inl1, q6_apply_inr0]

theorem burnsideB46_p3_core_sub_mem [Finite K] {r : ↥(cayleyGroup K)}
    (hr : r ∈ pCoreOf 2 (stabV0 K)) {w : Ix3 → K} (hw : w (.inr 0) = 0) :
    g2Act r w - w ∈ stdF K 3 := by
  obtain ⟨h0, h2, h1⟩ := burnsideB46_p3_core_coords hr w
  refine mem_stdF_three.mpr ⟨?_, ?_, ?_⟩
  · rw [Pi.sub_apply, h1, hw]
    ring
  · rw [Pi.sub_apply, h2, hw]
    ring
  · rw [Pi.sub_apply, h0, sub_self]

@[expose] noncomputable def burnsideB46_p3_zetaR [Finite K] :
    ↥(pCoreOf 2 (stabV0 K)) →* Multiplicative (Fin 2 → K) where
  toFun r := Multiplicative.ofAdd
    ![g2Act r.1 (q6 0 0 0 1 0 0) (.inl 2), g2Act r.1 (q6 0 0 0 1 0 0) (.inl 1)]
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext i
    fin_cases i <;> simp [q6]
  map_mul' r r' := by
    obtain ⟨h0, h2, h1⟩ := burnsideB46_p3_core_coords r.2 (g2Act r'.1 (q6 0 0 0 1 0 0))
    obtain ⟨h0', -, -⟩ := burnsideB46_p3_core_coords r'.2 (q6 0 0 0 1 0 0)
    simp only [q6_apply_inr0] at h0'
    rw [← ofAdd_add]
    congr 1
    funext i
    have e : g2Act (r * r' : ↥(pCoreOf 2 (stabV0 K))).1 (q6 0 0 0 1 0 0) =
        g2Act r.1 (g2Act r'.1 (q6 0 0 0 1 0 0)) := g2Act_mul_apply _ _ _
    rw [e]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.add_apply]
      rw [h2, h0']
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply]
      rw [h1, h0']
      simp only [Matrix.cons_val_zero]
      ring

theorem burnsideB46_p3_zetaR_kerElt [Finite K] (α β γ p q' : K)
    (h : burnsideB46_p3_kerElt α β γ p q' ∈ pCoreOf 2 (stabV0 K)) :
    burnsideB46_p3_zetaR ⟨_, h⟩ = Multiplicative.ofAdd ![β, γ] := by
  change Multiplicative.ofAdd _ = _
  rw [burnsideB46_p3_kerElt_v0]
  simp [q6]

theorem burnsideB46_p3_zetaR_surjective [Finite K] :
    Function.Surjective (burnsideB46_p3_zetaR (K := K)) := by
  intro v
  have hmem : burnsideB46_p3_kerElt 0 (Multiplicative.toAdd v 0) (Multiplicative.toAdd v 1) 0 0 ∈
      pCoreOf 2 (stabV0 K) := burnsideB46_p3_mem_core_iff.mpr ⟨_, _, _, _, _, rfl⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [burnsideB46_p3_zetaR_kerElt]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem burnsideB46_p3_zetaR_ker [Finite K] :
    (burnsideB46_p3_zetaR (K := K)).ker = (A1 K).subgroupOf (pCoreOf 2 (stabV0 K)) := by
  ext ⟨r, hr⟩
  obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_core_iff.mp hr
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, burnsideB46_p3_zetaR_kerElt _ _ _ _ _ hr]
  change _ ↔ burnsideB46_p3_kerElt α β γ p q' ∈ A1 K
  constructor
  · intro h
    have h' : ![β, γ] = (0 : Fin 2 → K) := Multiplicative.ofAdd.injective h
    have hβ : β = 0 := congrFun h' 0
    have hγ : γ = 0 := congrFun h' 1
    subst hβ hγ
    exact kerElt_mem_A1 α p q'
  · intro h
    have e1 := h (q6 0 0 0 0 1 0) (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
    have e2 := h (q6 0 0 0 0 0 1) (mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩)
    rw [burnsideB46_p3_act_kerElt] at e1 e2
    have a1 := congrFun e1 (.inl 0)
    have a2 := congrFun e2 (.inl 0)
    simp only [q6_apply_inl0] at a1 a2
    have hγ : γ = 0 := by linear_combination a1
    have hβ : β = 0 := by linear_combination a2
    subst hβ hγ
    rw [← ofAdd_zero]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem burnsideB46_p3_polarQ_eu (x : Ix3 → K) : polarQ x (eu 0 1) = x (.inr 0) := by
  simp [polarQ, eu, Pi.single_apply]

theorem burnsideB46_p3_polarQ_v1 (x : Ix3 → K) : polarQ x (q6 0 0 0 0 1 0) = x (.inl 1) := by
  simp [polarQ, q6]

theorem burnsideB46_p3_polarQ_v2 (x : Ix3 → K) : polarQ x (q6 0 0 0 0 0 1) = x (.inl 2) := by
  simp [polarQ, q6]

theorem burnsideB46_p3_polarQ_F3 (x : Ix3 → K) {z : Ix3 → K} (hz : z ∈ stdF K 3) :
    polarQ x z = z (.inl 0) * x (.inr 0) + x (.inl 1) * z (.inr 1) + x (.inl 2) * z (.inr 2) := by
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hz
  simp only [polarQ, h1, h2, h3]
  ring

theorem burnsideB46_p3_levi1Mat_10 (g : ↥(cayleyGroup K)) :
    levi1Mat g 1 0 = g2Act g (q6 0 0 0 0 1 0) (.inr 2) := by
  simp [levi1Mat_apply, vpart]

theorem burnsideB46_p3_core_conj_polar [Finite K] {p y : ↥(cayleyGroup K)}
    (hp : p ∈ stabQ (stdF K 1)) (hy : y ∈ pCoreOf 2 (stabV0 K)) {z : Ix3 → K}
    (hz : z ∈ stdF K 3) :
    polarQ (g2Act (p * y * p⁻¹) (q6 0 0 0 1 0 0) - q6 0 0 0 1 0 0) (g2Act p z) =
      burnsideB46_p3_c p * polarQ (g2Act y (q6 0 0 0 1 0 0) - q6 0 0 0 1 0 0) z := by
  obtain ⟨hc, hc0⟩ := burnsideB46_p3_act_eu hp
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : Ix3 → K, x₁ = g2Act p⁻¹ (q6 0 0 0 1 0 0) := ⟨_, rfl⟩
  have hpx₁ : g2Act p x₁ = q6 0 0 0 1 0 0 := by rw [hx₁, g2Act_apply_inv]
  have hd : x₁ (.inr 0) = burnsideB46_p3_c p := by
    have h3 : polarQ (q6 0 0 0 1 0 0) (burnsideB46_p3_c p • eu 0 (1 : K)) =
        burnsideB46_p3_c p := by
      rw [polarQ_symm, polarQ_smul_left, polarQ_symm, burnsideB46_p3_polarQ_eu]
      simp [q6]
    rw [← burnsideB46_p3_polarQ_eu x₁, ← polarQ_g2Act p x₁ (eu 0 1), hpx₁, hc]
    exact h3
  have hD : g2Act y x₁ - x₁ = burnsideB46_p3_c p • (g2Act y (q6 0 0 0 1 0 0) - q6 0 0 0 1 0 0) +
      (g2Act y (x₁ - burnsideB46_p3_c p • q6 0 0 0 1 0 0) -
        (x₁ - burnsideB46_p3_c p • q6 0 0 0 1 0 0)) := by
    rw [map_sub, JonesParshall.g2Act_smul]
    simp only [smul_sub]
    abel
  have hw'0 : ((x₁ - burnsideB46_p3_c p • (q6 0 0 0 1 0 0 : Ix3 → K) : Ix3 → K)) (.inr 0) = 0 := by
    simp [hd, q6]
  have hmem := burnsideB46_p3_core_sub_mem hy hw'0
  have key : g2Act (p * y * p⁻¹) (q6 0 0 0 1 0 0) - q6 0 0 0 1 0 0 =
      g2Act p (g2Act y x₁ - x₁) := by
    rw [g2Act_mul_apply, g2Act_mul_apply, map_sub, ← hx₁, hpx₁]
  rw [key, polarQ_g2Act, hD, polarQ_add_left, polarQ_smul_left, polarQ_F3 hmem hz, add_zero]

theorem burnsideB46_p3_zetaR_equivar [Finite K] {p y y' : ↥(cayleyGroup K)}
    (hp : p ∈ stabQ (stdF K 1)) (hy : y ∈ pCoreOf 2 (stabV0 K)) (hy' : y' ∈ pCoreOf 2 (stabV0 K))
    (h : y' = p * y * p⁻¹) :
    ![g2Act y' (q6 0 0 0 1 0 0) (.inl 2), g2Act y' (q6 0 0 0 1 0 0) (.inl 1)] =
      (levi1Mat p).mulVec
        ![g2Act y (q6 0 0 0 1 0 0) (.inl 2), g2Act y (q6 0 0 0 1 0 0) (.inl 1)] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hc, hc0⟩ := burnsideB46_p3_act_eu hp
  have hdet := burnsideB46_p3_det_levi hp
  rw [Matrix.det_fin_two] at hdet
  have hv1 : q6 (0 : K) 0 0 0 1 0 ∈ stdF K 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have hv2 : q6 (0 : K) 0 0 0 0 1 ∈ stdF K 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  have hw1 := burnsideB46_p3_mem_F3 hp hv1
  have hw2 := burnsideB46_p3_mem_F3 hp hv2
  have c1 := burnsideB46_p3_core_conj_polar hp hy hv1
  have c2 := burnsideB46_p3_core_conj_polar hp hy hv2
  rw [← h] at c1 c2
  rw [burnsideB46_p3_polarQ_F3 _ hw1, burnsideB46_p3_polarQ_v1] at c1
  rw [burnsideB46_p3_polarQ_F3 _ hw2, burnsideB46_p3_polarQ_v2] at c2
  obtain ⟨h0', -, -⟩ := burnsideB46_p3_core_coords hy' (q6 0 0 0 1 0 0)
  simp only [q6_apply_inr0] at h0'
  simp only [Pi.sub_apply, h0', q6_apply_inr0, q6_apply_inl1, q6_apply_inl2, sub_self, mul_zero,
    add_zero, sub_zero] at c1 c2
  rw [← levi1Mat_00, ← burnsideB46_p3_levi1Mat_10] at c1
  rw [← levi1Mat_01, ← levi1Mat_11] at c2
  set c := burnsideB46_p3_c p
  set M := levi1Mat p
  set β := g2Act y (q6 0 0 0 1 0 0) (.inl 2)
  set γ := g2Act y (q6 0 0 0 1 0 0) (.inl 1)
  set β' := g2Act y' (q6 0 0 0 1 0 0) (.inl 2)
  set γ' := g2Act y' (q6 0 0 0 1 0 0) (.inl 1)
  have eγ : c * γ' = c * (M 1 0 * β + M 1 1 * γ) := by
    linear_combination (M 1 1) * c1 - (M 1 0) * c2 - γ' * hdet - (c * M 1 0 * β) * h2
  have eβ : c * β' = c * (M 0 0 * β + M 0 1 * γ) := by
    linear_combination (M 0 0) * c2 - (M 0 1) * c1 - β' * hdet - (c * M 0 1 * γ) * h2
  have hβ := mul_left_cancel₀ hc0 eβ
  have hγ := mul_left_cancel₀ hc0 eγ
  funext i
  fin_cases i
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hβ
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hγ

theorem burnsideB46_p3_core_le_stabQ [Finite K] :
    pCoreOf 2 (stabV0 K) ≤ stabQ (stdF K 1) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 (stabV0 K)).trans stabV0_le_stabQ

theorem burnsideB46_p3_A1_le_core [Finite K] : A1 K ≤ pCoreOf 2 (stabV0 K) := by
  intro g hg
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hg
  exact burnsideB46_p3_mem_core_iff.mpr ⟨α, 0, 0, p, q', rfl⟩

theorem burnsideB46_p3_stabQ_le_normalizer_core [Finite K] :
    stabQ (stdF K 1) ≤ Subgroup.normalizer (pCoreOf 2 (stabV0 K) : Set ↥(cayleyGroup K)) :=
  burnsideB46_p3_stabQ_le_normalizer_stabV0.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (stabV0 K))

theorem burnsideB46_p3_stabQ_le_normalizer_A1 [Finite K] :
    stabQ (stdF K 1) ≤ Subgroup.normalizer (A1 K : Set ↥(cayleyGroup K)) := by
  rw [burnsideB46_p3_le_normalizer_iff]
  intro p hp a ha w hw
  have hpi : p⁻¹ ∈ stabQ (stdF K 1) := (stabQ (stdF K 1)).inv_mem hp
  have h1 := burnsideB46_p3_mem_F3 hpi hw
  rw [g2Act_mul_apply, g2Act_mul_apply, ha _ h1, g2Act_apply_inv]

theorem burnsideB46_p3_natQ_RA_eu [Finite K] :
    burnsideB46_p3_NatQ K 0 (stabQ (stdF K 1)) (pCoreOf 2 (stabV0 K)) (pCoreOf 2 (stabV0 K))
      (A1 K) := by
  refine ⟨burnsideB46_p3_core_le_stabQ, burnsideB46_p3_A1_le_core,
    burnsideB46_p3_stabQ_le_normalizer_core, burnsideB46_p3_stabQ_le_normalizer_A1,
    burnsideB46_p3_rho, burnsideB46_p3_zetaR, burnsideB46_p3_rho_surjective,
    burnsideB46_p3_rho_ker, burnsideB46_p3_zetaR_surjective, burnsideB46_p3_zetaR_ker, ?_⟩
  intro p y y' h
  rw [pow_zero, one_smul, burnsideB46_p3_rho_apply]
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  congr 1
  exact burnsideB46_p3_zetaR_equivar p.2 y.2 y'.2 (by rw [← h])

end P3c

section P3d

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p3_pinv_v0_coord {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1)) :
    g2Act p⁻¹ (q6 0 0 0 1 0 0) (.inr 0) = burnsideB46_p3_c p := by
  obtain ⟨hc, hc0⟩ := burnsideB46_p3_act_eu hp
  have h3 : polarQ (q6 0 0 0 1 0 0) (burnsideB46_p3_c p • eu 0 (1 : K)) = burnsideB46_p3_c p := by
    rw [polarQ_symm, polarQ_smul_left, polarQ_symm, burnsideB46_p3_polarQ_eu]
    simp [q6]
  rw [← burnsideB46_p3_polarQ_eu (g2Act p⁻¹ (q6 0 0 0 1 0 0)), ← polarQ_g2Act p _ (eu 0 1),
    g2Act_apply_inv, hc]
  exact h3

theorem burnsideB46_p3_uSL0_sub (a b : K) (w : Ix3 → K) :
    g2Act (g2A (uSL a b 0)) w - w =
      q6 (a * w (.inl 1) + b * w (.inl 2)) 0 0 0 (a * w (.inr 0)) (b * w (.inr 0)) := by
  conv_lhs => rw [q6_eta w]
  rw [g2Act_g2A_uSL]
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6] <;> ring

theorem burnsideB46_p3_vpart_q6_F3 (a e f : K) : vpart (q6 a 0 0 0 e f) = ![e, f] := by
  funext i
  fin_cases i <;> rfl

@[expose] noncomputable def burnsideB46_p3_zetaZ : ↥(Z1 K) →* Multiplicative (Fin 2 → K) where
  toFun z := Multiplicative.ofAdd (vpart (g2Act z.1 (q6 0 0 0 1 0 0)))
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext i
    fin_cases i <;> simp [vpart, q6]
  map_mul' z z' := by
    obtain ⟨v, hv⟩ := z.2
    obtain ⟨v', hv'⟩ := z'.2
    rw [← ofAdd_add]
    congr 1
    change vpart (g2Act (z.1 * z'.1) _) = _
    rw [g2Act_mul_apply, hv', g2Act_uSL_v0, hv, g2Act_uSL_v0]
    funext i
    fin_cases i <;> simp [vpart, q6, g2Act_g2A_uSL] <;> ring

theorem burnsideB46_p3_zetaZ_uSL (a b : K) (h : g2A (uSL a b 0) ∈ Z1 K) :
    burnsideB46_p3_zetaZ ⟨_, h⟩ = Multiplicative.ofAdd ![a, b] := by
  change Multiplicative.ofAdd _ = _
  rw [g2Act_uSL_v0]
  rfl

theorem burnsideB46_p3_zetaZ_surjective : Function.Surjective (burnsideB46_p3_zetaZ (K := K)) := by
  intro v
  have hz : g2A (uSL (Multiplicative.toAdd v 0) (Multiplicative.toAdd v 1) 0) ∈ Z1 K :=
    ⟨(Multiplicative.toAdd v 0, Multiplicative.toAdd v 1), rfl⟩
  refine ⟨⟨_, hz⟩, ?_⟩
  rw [burnsideB46_p3_zetaZ_uSL _ _ hz]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem burnsideB46_p3_zetaZ_ker :
    (burnsideB46_p3_zetaZ (K := K)).ker = (⊥ : Subgroup ↥(cayleyGroup K)).subgroupOf (Z1 K) := by
  ext ⟨z, hz⟩
  obtain ⟨v, rfl⟩ := hz
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, burnsideB46_p3_zetaZ_uSL _ _ ⟨v, rfl⟩]
  change _ ↔ g2A (uSL v.1 v.2 0) ∈ (⊥ : Subgroup ↥(cayleyGroup K))
  rw [Subgroup.mem_bot]
  constructor
  · intro h
    have h' : ![v.1, v.2] = (0 : Fin 2 → K) := Multiplicative.ofAdd.injective h
    have e1 : v.1 = 0 := congrFun h' 0
    have e2 : v.2 = 0 := congrFun h' 1
    rw [e1, e2, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]
  · intro h
    have h1 := congrArg (fun g => g2Act g (q6 (0 : K) 0 0 1 0 0)) h
    simp only [g2Act_uSL_v0, map_one] at h1
    obtain ⟨-, -, -, -, e1, e2⟩ := q6_inj h1
    rw [← ofAdd_zero]
    congr 1
    funext i
    fin_cases i
    · exact e1
    · exact e2

theorem burnsideB46_p3_Z1_le_core [Finite K] : Z1 K ≤ pCoreOf 2 (stabV0 K) := by
  rintro _ ⟨v, rfl⟩
  refine burnsideB46_p3_mem_core_iff.mpr ⟨0, 0, 0, v.1, v.2, ?_⟩
  rw [burnsideB46_p3_kerElt_zero]

theorem burnsideB46_p3_stabQ_le_normalizer_Z1 [Finite K] :
    stabQ (stdF K 1) ≤ Subgroup.normalizer (Z1 K : Set ↥(cayleyGroup K)) := by
  rw [burnsideB46_p3_le_normalizer_iff]
  intro p hp z hz
  have hN : ∀ p ∈ stabQ (stdF K 1), ∀ r ∈ pCoreOf 2 (stabV0 K),
      p * r * p⁻¹ ∈ pCoreOf 2 (stabV0 K) :=
    burnsideB46_p3_le_normalizer_iff.mp burnsideB46_p3_stabQ_le_normalizer_core
  have hzR : z ∈ pCoreOf 2 (stabV0 K) := burnsideB46_p3_Z1_le_core hz
  have hcomm : ∀ r ∈ pCoreOf 2 (stabV0 K), r * z = z * r := by
    intro r hr
    obtain ⟨α, β, γ, p₁, q₁, rfl⟩ := burnsideB46_p3_mem_core_iff.mp hr
    obtain ⟨v, rfl⟩ := hz
    rw [← burnsideB46_p3_kerElt_zero v.1 v.2]
    exact (burnsideB46_p3_kerElt_comm_Z α β γ p₁ q₁ v.1 v.2).symm
  have hmem : p * z * p⁻¹ ∈ burnsideB46_Z1 K (eu 0 (1 : K)) := by
    simp only [burnsideB46_Z1, centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      burnsideB46_p3_R1_eu]
    refine ⟨hN p hp z hzR, fun r hr => ?_⟩
    have hr' : p⁻¹ * r * p ∈ pCoreOf 2 (stabV0 K) := by
      simpa using hN p⁻¹ ((stabQ (stdF K 1)).inv_mem hp) r hr
    have h1 := hcomm _ hr'
    calc r * (p * z * p⁻¹) = p * ((p⁻¹ * r * p) * z) * p⁻¹ := by group
      _ = p * (z * (p⁻¹ * r * p)) * p⁻¹ := by rw [h1]
      _ = p * z * p⁻¹ * r := by group
  rwa [burnsideB46_p3_Z1_eu] at hmem

theorem burnsideB46_p3_zetaZ_equivar {p : ↥(cayleyGroup K)} (hp : p ∈ stabQ (stdF K 1))
    {z z' : ↥(cayleyGroup K)} (hz : z ∈ Z1 K) (h : z' = p * z * p⁻¹) :
    vpart (g2Act z' (q6 0 0 0 1 0 0)) =
      burnsideB46_p3_c p • (levi1Mat p).mulVec (vpart (g2Act z (q6 0 0 0 1 0 0))) := by
  obtain ⟨v, rfl⟩ := hz
  obtain ⟨hc, hc0⟩ := burnsideB46_p3_act_eu hp
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : Ix3 → K, x₁ = g2Act p⁻¹ (q6 0 0 0 1 0 0) := ⟨_, rfl⟩
  have hpx₁ : g2Act p x₁ = q6 0 0 0 1 0 0 := by rw [hx₁, g2Act_apply_inv]
  have hd : x₁ (.inr 0) = burnsideB46_p3_c p := by
    rw [hx₁]
    exact burnsideB46_p3_pinv_v0_coord hp
  have key : g2Act z' (q6 0 0 0 1 0 0) = g2Act p (g2Act (g2A (uSL v.1 v.2 0)) x₁) := by
    rw [h, g2Act_mul_apply, g2Act_mul_apply, ← hx₁]
  have hsplit : g2Act (g2A (uSL v.1 v.2 0)) x₁ = x₁ + q6 (v.1 * x₁ (.inl 1) + v.2 * x₁ (.inl 2))
      0 0 0 (v.1 * burnsideB46_p3_c p) (v.2 * burnsideB46_p3_c p) := by
    have := eq_add_of_sub_eq (burnsideB46_p3_uSL0_sub v.1 v.2 x₁)
    rw [hd] at this
    exact this.trans (add_comm _ _)
  have hF3 : q6 (v.1 * x₁ (.inl 1) + v.2 * x₁ (.inl 2)) 0 0 0 (v.1 * burnsideB46_p3_c p)
      (v.2 * burnsideB46_p3_c p) ∈ stdF K 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  rw [key, hsplit, map_add, hpx₁, vpart_add, burnsideB46_p3_vpart_act hp hF3,
    burnsideB46_p3_vpart_q6_F3, g2Act_uSL_v0]
  have hv0 : vpart (q6 (0 : K) 0 0 1 0 0) = 0 := by
    funext i
    fin_cases i <;> rfl
  have hv : vpart (q6 (0 : K) 0 0 1 v.1 v.2) = ![v.1, v.2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv0, hv, zero_add]
  have : (![v.1 * burnsideB46_p3_c p, v.2 * burnsideB46_p3_c p] : Fin 2 → K) =
      burnsideB46_p3_c p • ![v.1, v.2] := by
    funext i
    fin_cases i <;> simp [mul_comm]
  rw [this, Matrix.mulVec_smul]

theorem burnsideB46_p3_stabQ_le_normalizer_bot :
    stabQ (stdF K 1) ≤ Subgroup.normalizer ((⊥ : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) := by
  rw [burnsideB46_p3_le_normalizer_iff]
  intro p _ y hy
  rw [Subgroup.mem_bot] at hy ⊢
  simp [hy]

theorem burnsideB46_p3_natQ_Z_eu [Finite K] :
    burnsideB46_p3_NatQ K 1 (stabQ (stdF K 1)) (pCoreOf 2 (stabV0 K)) (Z1 K) ⊥ := by
  refine ⟨burnsideB46_p3_core_le_stabQ, bot_le, burnsideB46_p3_stabQ_le_normalizer_Z1,
    burnsideB46_p3_stabQ_le_normalizer_bot, burnsideB46_p3_rho, burnsideB46_p3_zetaZ,
    burnsideB46_p3_rho_surjective, burnsideB46_p3_rho_ker, burnsideB46_p3_zetaZ_surjective,
    burnsideB46_p3_zetaZ_ker, ?_⟩
  intro p y y' h
  rw [burnsideB46_p3_rho_apply, burnsideB46_p3_det_levi p.2, pow_one]
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  congr 1
  exact burnsideB46_p3_zetaZ_equivar p.2 y.2 (by rw [← h])

end P3d

section P3e

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p3_card_core [Finite K] :
    Nat.card (pCoreOf 2 (stabV0 K)) = Nat.card K ^ 5 := by
  let f : K × K × K × K × K → ↥(pCoreOf 2 (stabV0 K)) := fun t =>
    ⟨burnsideB46_p3_kerElt t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2,
      burnsideB46_p3_mem_core_iff.mpr ⟨_, _, _, _, _, rfl⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨α, β, γ, p, q'⟩ ⟨α', β', γ', p', q''⟩ h
    have h' : burnsideB46_p3_kerElt α β γ p q' = burnsideB46_p3_kerElt α' β' γ' p' q'' :=
      congrArg Subtype.val h
    have e1 := congrArg (fun g => g2Act g (q6 0 0 0 1 0 0)) h'
    have e2 := congrArg (fun g => g2Act g (q6 0 1 0 0 0 0)) h'
    simp only [burnsideB46_p3_kerElt_v0, burnsideB46_p3_kerElt_u1] at e1 e2
    obtain ⟨-, hγ, hβ, -, hp, hq⟩ := q6_inj e1
    obtain ⟨-, -, -, -, -, hα⟩ := q6_inj e2
    subst hβ hγ
    have hα' : α = α' := by linear_combination hα
    subst hα'
    have hp' : p = p' := by linear_combination hp
    have hq' : q' = q'' := by linear_combination hq
    subst hp' hq'
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_core_iff.mp hr
    exact ⟨(α, β, γ, p, q'), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  simp only [Nat.card_prod]
  ring

theorem burnsideB46_p3_kerElt_mul_self (α p q' : K) :
    burnsideB46_p3_kerElt α 0 0 p q' * burnsideB46_p3_kerElt α 0 0 p q' = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine cayley_ext_Q fun w => ?_
  rw [g2Act_mul_apply, map_one]
  change _ = w
  conv_rhs => rw [q6_eta w]
  conv_lhs => rw [q6_eta w]
  simp only [burnsideB46_p3_act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination (p * w (.inl 1) + q' * w (.inl 2) + α * α * w (.inr 0)) * h2
  · ring
  · ring
  · ring
  · linear_combination (p * w (.inr 0) + α * w (.inl 2)) * h2
  · linear_combination (q' * w (.inr 0) + α * w (.inl 1)) * h2

theorem burnsideB46_p3_kerElt_A1_comm (α p q' α' p' q'' : K) :
    burnsideB46_p3_kerElt α 0 0 p q' * burnsideB46_p3_kerElt α' 0 0 p' q'' =
      burnsideB46_p3_kerElt α' 0 0 p' q'' * burnsideB46_p3_kerElt α 0 0 p q' := by
  refine cayley_ext_Q fun w => ?_
  rw [g2Act_mul_apply, g2Act_mul_apply, q6_eta w]
  simp only [burnsideB46_p3_act_kerElt]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p3_isElemAbelian_A1 : IsElemAbelian 2 (A1 K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨α, p, q', ha⟩ := exists_eq_of_mem_A1 a.2
    obtain ⟨α', p', q'', hb⟩ := exists_eq_of_mem_A1 b.2
    apply Subtype.ext
    change (a : ↥(cayleyGroup K)) * b = b * a
    rw [ha, hb]
    exact burnsideB46_p3_kerElt_A1_comm α p q' α' p' q''
  · obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hx
    rw [pow_two]
    exact burnsideB46_p3_kerElt_mul_self α p q'

theorem burnsideB46_p3_A1_eu [Finite K] : burnsideB46_A1 K (eu 0 (1 : K)) = A1 K := by
  ext g
  change (∀ w ∈ burnsideB46_F3 K (eu 0 (1 : K)), g2Act g w = w) ↔ _
  rw [burnsideB46_p3_F3_eu]
  exact Iff.rfl

theorem burnsideB46_p3_conj_injective (γ : ↥(cayleyGroup K)) :
    Function.Injective (MulAut.conj γ).toMonoidHom := (MulAut.conj γ).injective

theorem burnsideB46_p3_natQ_Z [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    burnsideB46_p3_NatQ K 1 (burnsideB46_P1 K x) (burnsideB46_R1 K x) (burnsideB46_Z1 K x) ⊥ := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_P1_act, burnsideB46_p3_R1_act, burnsideB46_p3_Z1_act,
    ← Subgroup.map_bot (MulAut.conj γ).toMonoidHom,
    burnsideB46_p3_NatQ_map _ (burnsideB46_p3_conj_injective γ), burnsideB46_p3_P1_eu,
    burnsideB46_p3_R1_eu, burnsideB46_p3_Z1_eu]
  exact burnsideB46_p3_natQ_Z_eu

theorem burnsideB46_p3_natQ_RA [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    burnsideB46_p3_NatQ K 0 (burnsideB46_P1 K x) (burnsideB46_R1 K x) (burnsideB46_R1 K x)
      (burnsideB46_A1 K x) := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_P1_act, burnsideB46_p3_R1_act, burnsideB46_p3_A1_act,
    burnsideB46_p3_NatQ_map _ (burnsideB46_p3_conj_injective γ), burnsideB46_p3_P1_eu,
    burnsideB46_p3_R1_eu, burnsideB46_p3_A1_eu]
  exact burnsideB46_p3_natQ_RA_eu

theorem burnsideB46_p3_card_R1 [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    Nat.card (burnsideB46_R1 K x) = Nat.card K ^ 5 := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_R1_act, Subgroup.card_map_of_injective (burnsideB46_p3_conj_injective γ),
    burnsideB46_p3_R1_eu]
  exact burnsideB46_p3_card_core

theorem burnsideB46_p3_A1_facts [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    IsElemAbelian 2 (burnsideB46_A1 K x) ∧ Nat.card (burnsideB46_A1 K x) = Nat.card K ^ 3 := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_A1_act, Subgroup.card_map_of_injective (burnsideB46_p3_conj_injective γ),
    burnsideB46_p3_A1_eu]
  exact ⟨burnsideB46_p3_isElemAbelian_map burnsideB46_p3_isElemAbelian_A1, card_A1⟩

end P3e

section P3f

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

theorem burnsideB46_IsNatGL2QuotTw_iff {M : Type*} [Group M] {K : Type} [Field K]
    {P R Y A : Subgroup M} :
    IsNatGL2QuotTw K P R Y A ↔ burnsideB46_p3_NatQ K 1 P R Y A := by
  rw [← burnsideB46_p3_isNatGL2QuotTw_iff]
  unfold IsNatGL2QuotTw burnsideB46_p3_IsNatGL2QuotTw
  simp only [pow_one]

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p3_transvection_mulVec (i j : Fin 3) (c : K) (u : Fin 3 → K) :
    Matrix.transvection i j c *ᵥ u = u + Pi.single i (c * u j) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, transvection_entry, Pi.add_apply, Pi.single_apply,
    add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  by_cases hk : k = i
  · subst hk
    simp [Finset.sum_ite_eq']
  · simp [hk, Finset.sum_ite_eq', Ne.symm hk]

theorem burnsideB46_p3_transvection_transpose_mulVec (i j : Fin 3) (c : K) (v : Fin 3 → K) :
    (Matrix.transvection i j c)ᵀ *ᵥ v = v + Pi.single j (c * v i) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, transvection_entry, Pi.add_apply,
    Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hk : k = j
  · subst hk
    simp [Finset.sum_ite_eq']
  · simp [hk, Finset.sum_ite_eq', Ne.symm hk]

theorem burnsideB46_p3_longRootFn_eq (i j : Fin 3) (hij : i ≠ j) (c : K) (x : quasithinZorn K) :
    longRootFn i j c x = (g2A (tv i j hij c) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x := by
  rw [g2A_apply]
  have hA : ((tv i j hij c : SL3 K) : Matrix (Fin 3) (Fin 3) K) = Matrix.transvection i j c := rfl
  rw [gAFun, adjugate_tv, hA, longRootFn, burnsideB46_p3_transvection_mulVec,
    burnsideB46_p3_transvection_transpose_mulVec]

theorem burnsideB46_p3_tv_ne_one (i j : Fin 3) (hij : i ≠ j) :
    g2A (tv i j hij (1 : K)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : ↥(cayleyGroup K) => g2Act g (eu j 1) (.inl i)) h
  simp only [g2Act_tv, map_one] at h1
  simp [eu, ev, Pi.single_apply, hij, Ne.symm hij] at h1

@[expose] def burnsideB46_p3_hyp (x : Ix3 → K) : Submodule K (Ix3 → K) where
  carrier := {w | polarQ x w = 0}
  add_mem' := fun {a b} ha hb => by
    change polarQ x (a + b) = 0
    rw [polarQ_add_right, show polarQ x a = 0 from ha, show polarQ x b = 0 from hb, add_zero]
  zero_mem' := by
    change polarQ x 0 = 0
    simp [polarQ]
  smul_mem' := fun c w hw => by
    change polarQ x (c • w) = 0
    rw [polarQ_symm, polarQ_smul_left, polarQ_symm, show polarQ x w = 0 from hw, mul_zero]

theorem burnsideB46_p3_mem_hyp {x w : Ix3 → K} :
    w ∈ burnsideB46_p3_hyp x ↔ polarQ x w = 0 := Iff.rfl

theorem burnsideB46_p3_mem_hyp_eu {w : Ix3 → K} :
    w ∈ burnsideB46_p3_hyp (eu 0 (1 : K)) ↔ w (.inr 0) = 0 := by
  rw [burnsideB46_p3_mem_hyp, polarQ_symm, burnsideB46_p3_polarQ_eu]

theorem burnsideB46_p3_hyp_act (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    burnsideB46_p3_hyp (g2Act γ x) = gmapG γ (burnsideB46_p3_hyp x) := by
  ext w
  rw [mem_gmapG, burnsideB46_p3_mem_hyp, burnsideB46_p3_mem_hyp,
    ← polarQ_g2Act γ x (g2Act γ⁻¹ w), g2Act_apply_inv]

theorem burnsideB46_p3_finrank_hyp_eu :
    Module.finrank K (burnsideB46_p3_hyp (eu 0 (1 : K))) = 5 := by
  have hker : burnsideB46_p3_hyp (eu 0 (1 : K)) =
      LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Ix3 => K) (.inr 0)) := by
    ext w
    rw [burnsideB46_p3_mem_hyp_eu]
    simp
  rw [hker]
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := K) (φ := fun _ : Ix3 => K) (.inr 0))
  have hr : LinearMap.range (LinearMap.proj (R := K) (φ := fun _ : Ix3 => K) (.inr 0)) = ⊤ :=
    LinearMap.range_eq_top.mpr fun a => ⟨Pi.single (.inr 0) a, by simp⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_pi] at h
  have h6 : Fintype.card Ix3 = 6 := by simp [Ix3]
  omega

theorem burnsideB46_p3_finrank_hyp [Finite K] {x : Ix3 → K} (hx : x ≠ 0) :
    Module.finrank K (burnsideB46_p3_hyp x) = 5 := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_hyp_act, burnsideB46_p3_finrank_gmapG, burnsideB46_p3_finrank_hyp_eu]

theorem burnsideB46_p3_fix_Z1_hyp [Finite K] {x : Ix3 → K} (hx : x ≠ 0) {z : ↥(cayleyGroup K)}
    (hz : z ∈ burnsideB46_Z1 K x) (hz1 : z ≠ 1) {w : Ix3 → K} (hw : g2Act z w = w) :
    w ∈ burnsideB46_p3_hyp x := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu] at hz
  rw [burnsideB46_p3_hyp_act, mem_gmapG]
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := hz₀
  change g2Act (γ * g2A (uSL v.1 v.2 0) * γ⁻¹) w = w at hw
  have hz0 : v ≠ 0 := by
    rintro rfl
    apply hz1
    change γ * g2A (uSL (0 : K × K).1 (0 : K × K).2 0) * γ⁻¹ = 1
    simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero]
  have hfix : g2Act (g2A (uSL v.1 v.2 0)) (g2Act γ⁻¹ w) = g2Act γ⁻¹ w := by
    rw [g2Act_mul_apply, g2Act_mul_apply] at hw
    have h1 := congrArg (g2Act γ⁻¹) hw
    rwa [g2Act_inv_apply] at h1
  rw [burnsideB46_p3_mem_hyp_eu]
  have e1 := congrFun hfix (.inr 1)
  have e2 := congrFun hfix (.inr 2)
  rw [g2Act_g2A_uSL] at e1 e2
  simp only [q6_apply_inr1, q6_apply_inr2] at e1 e2
  have ha : v.1 * (g2Act γ⁻¹ w) (.inr 0) = 0 := by linear_combination e1
  have hb : v.2 * (g2Act γ⁻¹ w) (.inr 0) = 0 := by linear_combination e2
  by_contra hne
  apply hz0
  exact Prod.ext ((mul_eq_zero.mp ha).resolve_right hne) ((mul_eq_zero.mp hb).resolve_right hne)

theorem burnsideB46_p3_rootD_le_Z1 (d : Option K) : rootD d ≤ Z1 K := by
  rintro _ ⟨v, -, rfl⟩
  exact ⟨v, rfl⟩

theorem burnsideB46_p3_hyp_le_sup_eu :
    burnsideB46_p3_hyp (eu 0 (1 : K)) ≤ fixSub (rootD (none : Option K)) ⊔ fixSub (rootD (some 0)) := by
  intro w hw
  rw [burnsideB46_p3_mem_hyp_eu] at hw
  have h1 : q6 (0 : K) 0 (w (.inl 2)) 0 0 0 ∈ fixSub (rootD (some (0 : K))) := by
    rw [mem_fixSub]
    exact (fixD_iff (some (0 : K)) _).mpr ⟨rfl, by simp [OnLine, q6]⟩
  have h2 : w - q6 (0 : K) 0 (w (.inl 2)) 0 0 0 ∈ fixSub (rootD (none : Option K)) := by
    rw [mem_fixSub]
    refine (fixD_iff (none : Option K) _).mpr ⟨?_, ?_⟩
    · simp [q6, hw]
    · simp [OnLine, q6]
  have := Submodule.add_mem_sup h2 h1
  rwa [sub_add_cancel] at this

theorem burnsideB46_p3_F3_comm_eu {y : Ix3 → K} (hy : y ∈ stdF K 3) :
    ∃ (g₁ g₂ g₃ : ↥(cayleyGroup K)) (w₁ w₂ w₃ : Ix3 → K), g₁ ∈ A1 K ∧ g₂ ∈ A1 K ∧ g₃ ∈ A1 K ∧
      w₁ ∈ burnsideB46_p3_hyp (eu 0 (1 : K)) ∧ w₂ ∈ burnsideB46_p3_hyp (eu 0 (1 : K)) ∧
      w₃ ∈ burnsideB46_p3_hyp (eu 0 (1 : K)) ∧
      y = (g2Act g₁ w₁ - w₁) + (g2Act g₂ w₂ - w₂) + (g2Act g₃ w₃ - w₃) := by
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hy
  have hy' : y = q6 (y (.inl 0)) 0 0 0 (y (.inr 1)) (y (.inr 2)) := by
    conv_lhs => rw [q6_eta y]
    rw [h1, h2, h3]
  refine ⟨burnsideB46_p3_kerElt 0 0 0 1 0, burnsideB46_p3_kerElt 1 0 0 0 0,
    burnsideB46_p3_kerElt 1 0 0 0 0, q6 0 (y (.inl 0)) 0 0 0 0, q6 0 0 (y (.inr 1)) 0 0 0,
    q6 0 (y (.inr 2)) 0 0 0 0, kerElt_mem_A1 _ _ _, kerElt_mem_A1 _ _ _, kerElt_mem_A1 _ _ _,
    ?_, ?_, ?_, ?_⟩
  · rw [burnsideB46_p3_mem_hyp_eu]
    rfl
  · rw [burnsideB46_p3_mem_hyp_eu]
    rfl
  · rw [burnsideB46_p3_mem_hyp_eu]
    rfl
  · rw [burnsideB46_p3_act_kerElt, burnsideB46_p3_act_kerElt, burnsideB46_p3_act_kerElt]
    conv_lhs => rw [hy']
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6]

theorem burnsideB46_p3_hyp_le_sup [Finite K] (γ : ↥(cayleyGroup K)) :
    burnsideB46_p3_hyp (g2Act γ (eu 0 (1 : K))) ≤
      fixSub ((rootD (none : Option K)).map (MulAut.conj γ).toMonoidHom) ⊔
        fixSub ((rootD (some (0 : K))).map (MulAut.conj γ).toMonoidHom) := by
  rw [burnsideB46_p3_hyp_act, burnsideB46_p3_fixSub_map_conj, burnsideB46_p3_fixSub_map_conj]
  exact (gmapG_mono burnsideB46_p3_hyp_le_sup_eu).trans (le_of_eq (Submodule.map_sup _ _ _))

theorem burnsideB46_p3_comm_mem_F3 [Finite K] {x : Ix3 → K} (hx : x ≠ 0) {g : ↥(cayleyGroup K)}
    (hg : g ∈ burnsideB46_A1 K x) {w : Ix3 → K} (hw : w ∈ burnsideB46_p3_hyp x) :
    g2Act g w - w ∈ burnsideB46_F3 K x := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_A1_act, burnsideB46_p3_mem_map_conj, burnsideB46_p3_A1_eu] at hg
  rw [burnsideB46_p3_hyp_act, mem_gmapG, burnsideB46_p3_mem_hyp_eu] at hw
  rw [burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu, mem_gmapG]
  have h1 := burnsideB46_p3_core_sub_mem (burnsideB46_p3_A1_le_core hg) hw
  have e : g2Act γ⁻¹ (g2Act g w - w) =
      g2Act (γ⁻¹ * g * γ) (g2Act γ⁻¹ w) - g2Act γ⁻¹ w := by
    rw [map_sub]
    congr 1
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv]
  rw [e]
  exact h1

theorem burnsideB46_p3_F3_comm [Finite K] {x : Ix3 → K} (hx : x ≠ 0) {y : Ix3 → K}
    (hy : y ∈ burnsideB46_F3 K x) :
    ∃ (g₁ g₂ g₃ : ↥(cayleyGroup K)) (w₁ w₂ w₃ : Ix3 → K),
      g₁ ∈ burnsideB46_A1 K x ∧ g₂ ∈ burnsideB46_A1 K x ∧ g₃ ∈ burnsideB46_A1 K x ∧
      w₁ ∈ burnsideB46_p3_hyp x ∧ w₂ ∈ burnsideB46_p3_hyp x ∧ w₃ ∈ burnsideB46_p3_hyp x ∧
      y = (g2Act g₁ w₁ - w₁) + (g2Act g₂ w₂ - w₂) + (g2Act g₃ w₃ - w₃) := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu, mem_gmapG] at hy
  obtain ⟨g₁, g₂, g₃, w₁, w₂, w₃, hg₁, hg₂, hg₃, hw₁, hw₂, hw₃, hy'⟩ :=
    burnsideB46_p3_F3_comm_eu hy
  have e : ∀ (g : ↥(cayleyGroup K)) (w : Ix3 → K),
      g2Act (γ * g * γ⁻¹) (g2Act γ w) - g2Act γ w = g2Act γ (g2Act g w - w) := by
    intro g w
    rw [map_sub, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
  have hA : ∀ g ∈ A1 K, γ * g * γ⁻¹ ∈ burnsideB46_A1 K (g2Act γ (eu 0 (1 : K))) := by
    intro g hg
    rw [burnsideB46_p3_A1_act, burnsideB46_p3_A1_eu]
    exact ⟨g, hg, rfl⟩
  have hH : ∀ w ∈ burnsideB46_p3_hyp (eu 0 (1 : K)),
      g2Act γ w ∈ burnsideB46_p3_hyp (g2Act γ (eu 0 (1 : K))) := by
    intro w hw
    rw [burnsideB46_p3_hyp_act, mem_gmapG, g2Act_inv_apply]
    exact hw
  refine ⟨γ * g₁ * γ⁻¹, γ * g₂ * γ⁻¹, γ * g₃ * γ⁻¹, g2Act γ w₁, g2Act γ w₂, g2Act γ w₃,
    hA _ hg₁, hA _ hg₂, hA _ hg₃, hH _ hw₁, hH _ hw₂, hH _ hw₃, ?_⟩
  rw [e, e, e, ← map_add, ← map_add, ← hy', g2Act_apply_inv]

end P3f

section P3g

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p3_pre_sup [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (S T : Submodule K (Ix3 → K)) :
    burnsideB46_pre θ (S ⊔ T) ≤ burnsideB46_pre θ S ⊔ burnsideB46_pre θ T := by
  intro v hv
  rw [burnsideB46_mem_pre] at hv
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hv
  obtain ⟨vs, hvs⟩ := burnsideB46_f_surj H s
  have h1 : v * vs⁻¹ ∈ burnsideB46_pre θ T := by
    rw [burnsideB46_mem_pre, burnsideB46_f_sub, hvs, ← hst]
    simpa using ht
  have h2 : vs ∈ burnsideB46_pre θ S := by
    rw [burnsideB46_mem_pre, hvs]
    exact hs
  have := Subgroup.mul_mem_sup h1 h2
  rw [inv_mul_cancel_right, sup_comm] at this
  exact this

theorem burnsideB46_p3_pre_mono {S T : Submodule K (Ix3 → K)} (h : S ≤ T) :
    burnsideB46_pre θ S ≤ burnsideB46_pre θ T :=
  fun _ hv => h hv

theorem burnsideB46_p3_cg_apply [CharP K 2] (γ : ↥(quasithinG2 K)) (y : quasithinZorn K) :
    ((burnsideB46_cg γ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) y =
      (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) y := rfl

theorem burnsideB46_p3_isLongRootSub_of [CharP K 2] {i j : Fin 3} (hij : i ≠ j)
    {D : Subgroup ↥(cayleyGroup K)} (hD : ∀ d, d ∈ D ↔ ∃ c : K, d = g2A (tv i j hij c))
    (γ : ↥(cayleyGroup K)) :
    IsLongRootSub π ((D.map (MulAut.conj γ).toMonoidHom).map (burnsideB46_pi π)) := by
  refine ⟨i, j, hij, burnsideB46_cg.symm γ, fun ψ => ?_⟩
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (hD d).mp hd
    refine ⟨c, burnsideB46_cg.symm (g2A (tv i j hij c)), fun y => ?_, ?_⟩
    · have := burnsideB46_p3_cg_apply (burnsideB46_cg.symm (g2A (tv i j hij c))) y
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm.trans (burnsideB46_p3_longRootFn_eq i j hij c y).symm
    · change burnsideB46_pi π (γ * g2A (tv i j hij c) * γ⁻¹) = _
      simp only [burnsideB46_pi_apply, map_mul, map_inv]
  · rintro ⟨c, φ, hφ, rfl⟩
    have h1 : burnsideB46_cg φ = g2A (tv i j hij c) :=
      Subtype.ext (LinearEquiv.ext fun y => (hφ y).trans (burnsideB46_p3_longRootFn_eq i j hij c y))
    refine ⟨γ * g2A (tv i j hij c) * γ⁻¹, ⟨g2A (tv i j hij c), (hD _).mpr ⟨c, rfl⟩, rfl⟩, ?_⟩
    rw [← h1]
    simp only [burnsideB46_pi_apply, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem burnsideB46_p3_mem_rootD_none_iff [CharP K 2] (d : ↥(cayleyGroup K)) :
    d ∈ rootD (none : Option K) ↔ ∃ c : K, d = g2A (tv 0 2 (by decide) c) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, ?_⟩
    have hv1 : v.1 = 0 := hv
    rw [hv1]
    congr 1
    exact Subtype.ext (by rw [tv02_lit, uSL_coe])
  · rintro ⟨c, rfl⟩
    refine ⟨(0, c), rfl, ?_⟩
    congr 1
    exact Subtype.ext (by rw [tv02_lit, uSL_coe])

theorem burnsideB46_p3_mem_rootD_zero_iff [CharP K 2] (d : ↥(cayleyGroup K)) :
    d ∈ rootD (some (0 : K)) ↔ ∃ c : K, d = g2A (tv 0 1 (by decide) c) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.1, ?_⟩
    have hv2 : v.2 = 0 := by
      have : v.2 = 0 * v.1 := hv
      rw [this, zero_mul]
    rw [hv2]
    congr 1
    exact Subtype.ext (by rw [tv01_lit, uSL_coe])
  · rintro ⟨c, rfl⟩
    refine ⟨(c, 0), by simp [OnLine], ?_⟩
    congr 1
    exact Subtype.ext (by rw [tv01_lit, uSL_coe])

theorem burnsideB46_p3_E_eq [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    {x : Ix3 → K} (hx : x ≠ 0) :
    (⨆ (Z : Subgroup (MulAut V))
        (_ : IsLongRootSub π Z ∧ Z ≤ (burnsideB46_Z1 K x).map (burnsideB46_pi π)),
        cPre (fixV L) Z) = burnsideB46_pre θ (burnsideB46_p3_hyp x) := by
  apply le_antisymm
  · refine iSup₂_le fun Z hZ => ?_
    obtain ⟨⟨i, j, hij, g, hg⟩, hZZ⟩ := hZ
    obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ↥(quasithinG2 K),
        φ₁ = burnsideB46_cg.symm (g2A (tv i j hij (1 : K))) := ⟨_, rfl⟩
    have hψ₀ : π g * π φ₁ * (π g)⁻¹ ∈ Z := by
      refine (hg _).mpr ⟨1, φ₁, fun y => ?_, rfl⟩
      have := burnsideB46_p3_cg_apply φ₁ y
      rw [hφ₁, MulEquiv.apply_symm_apply] at this
      rw [hφ₁]
      exact this.symm.trans (burnsideB46_p3_longRootFn_eq i j hij 1 y).symm
    have hψ₀1 : π g * π φ₁ * (π g)⁻¹ ≠ 1 := by
      intro h
      have h1 : π φ₁ = 1 := by
        have := congrArg (fun a => (π g)⁻¹ * a * π g) h
        simpa [mul_assoc] using this
      have h2 : φ₁ = 1 := H.inj (by rw [h1, map_one])
      apply burnsideB46_p3_tv_ne_one i j hij (K := K)
      have := congrArg burnsideB46_cg h2
      rwa [hφ₁, MulEquiv.apply_symm_apply, map_one] at this
    obtain ⟨z₀, hz₀, hz₀e⟩ := hZZ hψ₀
    have hz₀1 : z₀ ≠ 1 := fun h => hψ₀1 (by rw [← hz₀e, h, map_one])
    intro v hv
    rw [burnsideB46_mem_cPre] at hv
    have h1 := hv _ hψ₀
    have h2 := (burnsideB46_f_eq_zero_iff H _).2 h1
    rw [burnsideB46_f_sub, ← hz₀e, burnsideB46_f_act H, sub_eq_zero] at h2
    rw [burnsideB46_mem_pre]
    exact burnsideB46_p3_fix_Z1_hyp hx hz₀ hz₀1 h2
  · obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
    have hZa : IsLongRootSub π (((rootD (none : Option K)).map (MulAut.conj γ).toMonoidHom).map
        (burnsideB46_pi π)) :=
      burnsideB46_p3_isLongRootSub_of (by decide) burnsideB46_p3_mem_rootD_none_iff γ
    have hZb : IsLongRootSub π (((rootD (some (0 : K))).map (MulAut.conj γ).toMonoidHom).map
        (burnsideB46_pi π)) :=
      burnsideB46_p3_isLongRootSub_of (by decide) burnsideB46_p3_mem_rootD_zero_iff γ
    have hlea : ((rootD (none : Option K)).map (MulAut.conj γ).toMonoidHom).map
        (burnsideB46_pi π) ≤ (burnsideB46_Z1 K (g2Act γ (eu 0 (1 : K)))).map (burnsideB46_pi π) := by
      rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu]
      exact Subgroup.map_mono (Subgroup.map_mono (burnsideB46_p3_rootD_le_Z1 _))
    have hleb : ((rootD (some (0 : K))).map (MulAut.conj γ).toMonoidHom).map
        (burnsideB46_pi π) ≤ (burnsideB46_Z1 K (g2Act γ (eu 0 (1 : K)))).map (burnsideB46_pi π) := by
      rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu]
      exact Subgroup.map_mono (Subgroup.map_mono (burnsideB46_p3_rootD_le_Z1 _))
    calc burnsideB46_pre θ (burnsideB46_p3_hyp (g2Act γ (eu 0 (1 : K))))
        ≤ burnsideB46_pre θ (fixSub ((rootD (none : Option K)).map (MulAut.conj γ).toMonoidHom) ⊔
            fixSub ((rootD (some (0 : K))).map (MulAut.conj γ).toMonoidHom)) :=
          burnsideB46_p3_pre_mono (burnsideB46_p3_hyp_le_sup γ)
      _ ≤ burnsideB46_pre θ (fixSub ((rootD (none : Option K)).map (MulAut.conj γ).toMonoidHom)) ⊔
          burnsideB46_pre θ (fixSub ((rootD (some (0 : K))).map (MulAut.conj γ).toMonoidHom)) :=
          burnsideB46_p3_pre_sup H _ _
      _ = cPre (fixV L) (((rootD (none : Option K)).map (MulAut.conj γ).toMonoidHom).map
            (burnsideB46_pi π)) ⊔
          cPre (fixV L) (((rootD (some (0 : K))).map (MulAut.conj γ).toMonoidHom).map
            (burnsideB46_pi π)) := by
          rw [burnsideB46_cPre_map H, burnsideB46_cPre_map H]
      _ ≤ _ := sup_le (le_iSup₂_of_le _ ⟨hZa, hlea⟩ le_rfl) (le_iSup₂_of_le _ ⟨hZb, hleb⟩ le_rfl)

theorem burnsideB46_p3_comm_eq [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    {x : Ix3 → K} (hx : x ≠ 0) :
    CFSG.Quasithin.commSub (burnsideB46_pre θ (burnsideB46_p3_hyp x))
        ((burnsideB46_A1 K x).map (burnsideB46_pi π)) ⊔ fixV L =
      burnsideB46_pre θ (burnsideB46_F3 K x) := by
  apply le_antisymm
  · refine sup_le ?_ (burnsideB46_pre_map_ker H _)
    unfold CFSG.Quasithin.commSub
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ⟨g, hg, rfl⟩, v, hv, rfl⟩
    rw [SetLike.mem_coe, burnsideB46_mem_pre, burnsideB46_f_sub, burnsideB46_f_act H]
    exact burnsideB46_p3_comm_mem_F3 hx hg hv
  · intro u hu
    rw [burnsideB46_mem_pre] at hu
    obtain ⟨g₁, g₂, g₃, w₁, w₂, w₃, hg₁, hg₂, hg₃, hw₁, hw₂, hw₃, hy⟩ :=
      burnsideB46_p3_F3_comm hx hu
    obtain ⟨v₁, hv₁⟩ := burnsideB46_f_surj H w₁
    obtain ⟨v₂, hv₂⟩ := burnsideB46_f_surj H w₂
    obtain ⟨v₃, hv₃⟩ := burnsideB46_f_surj H w₃
    have hc : ∀ (g : ↥(cayleyGroup K)) (v : V), g ∈ burnsideB46_A1 K x →
        burnsideB46_f θ v ∈ burnsideB46_p3_hyp x →
        burnsideB46_pi π g v * v⁻¹ ∈ CFSG.Quasithin.commSub (burnsideB46_pre θ (burnsideB46_p3_hyp x))
          ((burnsideB46_A1 K x).map (burnsideB46_pi π)) := fun g v hg hv =>
      Subgroup.subset_closure ⟨_, ⟨g, hg, rfl⟩, v, hv, rfl⟩
    set c := (burnsideB46_pi π g₁ v₁ * v₁⁻¹) * (burnsideB46_pi π g₂ v₂ * v₂⁻¹) *
      (burnsideB46_pi π g₃ v₃ * v₃⁻¹) with hcdef
    have hcmem : c ∈ CFSG.Quasithin.commSub (burnsideB46_pre θ (burnsideB46_p3_hyp x))
        ((burnsideB46_A1 K x).map (burnsideB46_pi π)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hc g₁ v₁ hg₁ (hv₁ ▸ hw₁)) (hc g₂ v₂ hg₂ (hv₂ ▸ hw₂)))
        (hc g₃ v₃ hg₃ (hv₃ ▸ hw₃))
    have hfc : burnsideB46_f θ c = burnsideB46_f θ u := by
      rw [hcdef, burnsideB46_f_mul, burnsideB46_f_mul, burnsideB46_f_sub, burnsideB46_f_sub,
        burnsideB46_f_sub, burnsideB46_f_act H, burnsideB46_f_act H, burnsideB46_f_act H, hv₁, hv₂,
        hv₃, hy]
    have hker : u * c⁻¹ ∈ fixV L := by
      rw [← burnsideB46_f_eq_zero_iff H, burnsideB46_f_sub, hfc, sub_self]
    have := Subgroup.mul_mem_sup hcmem hker
    have h3 : c * (u * c⁻¹) = u := by
      rw [mul_comm u, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [h3] at this
    exact this

end P3g

section P3h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB

@[expose] noncomputable def burnsideB46_p3_detTwist (K : Type) [Field K] :
    GL (Fin 2) K →* GL (Fin 2) K :=
  Units.map
    { toFun := fun A : Matrix (Fin 2) (Fin 2) K => A.det • A
      map_one' := by simp
      map_mul' := fun A B => by
        rw [Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] }

theorem burnsideB46_p3_detTwist_coe {K : Type} [Field K] (A : GL (Fin 2) K) :
    ((burnsideB46_p3_detTwist K A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K).det • (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem burnsideB46_p3_detTwist_injective {K : Type} [Field K]
    (h3 : ∀ w : K, w ^ 3 = 1 → w = 1) : Function.Injective (burnsideB46_p3_detTwist K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 := congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K)) hA
  simp only [burnsideB46_p3_detTwist_coe, Units.val_one] at h1
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  set δ := (A : Matrix (Fin 2) (Fin 2) K).det with hδ
  have hAδ : (A : Matrix (Fin 2) (Fin 2) K) = δ⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← h1, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  have h2 := congrArg Matrix.det hAδ
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h2
  have h4 : δ ^ 3 = 1 := by
    have h5 : δ * δ ^ 2 = δ⁻¹ ^ 2 * δ ^ 2 := by rw [← h2]
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ = δ⁻¹ ^ 2 * δ ^ 2 := h5
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hdet, one_pow]
  have h6 := h3 δ h4
  apply Units.ext
  rw [hAδ, h6, inv_one, one_smul, Units.val_one]

theorem burnsideB46_p3_natQ_untwist {M : Type*} [Group M] {K : Type} [Field K] [Finite K]
    (h3 : ∀ w : K, w ^ 3 = 1 → w = 1) {P R Y A : Subgroup M}
    (h : burnsideB46_p3_NatQ K 1 P R Y A) : burnsideB46_p3_NatQ K 0 P R Y A := by
  obtain ⟨hRP, hAY, hPY, hPA, ρ, ζ, hρs, hρk, hζs, hζk, hζ⟩ := h
  have hinj := burnsideB46_p3_detTwist_injective h3
  have hsurj : Function.Surjective (burnsideB46_p3_detTwist K) :=
    Finite.surjective_of_injective hinj
  refine ⟨hRP, hAY, hPY, hPA, (burnsideB46_p3_detTwist K).comp ρ, ζ, hsurj.comp hρs, ?_, hζs, hζk,
    ?_⟩
  · ext p
    rw [MonoidHom.mem_ker, ← hρk, MonoidHom.mem_ker]
    change burnsideB46_p3_detTwist K (ρ p) = 1 ↔ ρ p = 1
    exact ⟨fun h => (injective_iff_map_eq_one _).mp hinj _ h, fun h => by rw [h, map_one]⟩
  · intro p y y' h
    rw [hζ p y y' h, pow_zero, one_smul, pow_one]
    congr 1
    change _ = (burnsideB46_p3_detTwist K (ρ p) : Matrix (Fin 2) (Fin 2) K).mulVec _
    rw [burnsideB46_p3_detTwist_coe, Matrix.smul_mulVec]

end P3h

section P3i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [CharP K 2] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p3_L_eq_map (H : burnsideB46_Hyp V n K G L π θ) :
    L = (⊤ : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup K)).map (burnsideB46_pi π) := by
  ext l
  rw [Subgroup.mem_map]
  constructor
  · intro hl
    obtain ⟨g, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    exact ⟨g, Subgroup.mem_top _, rfl⟩
  · rintro ⟨g, -, rfl⟩
    exact burnsideB46_pi_mem_L H g

theorem burnsideB46_p3_isMaxParabolic2_L (H : burnsideB46_Hyp V n K G L π θ)
    {P : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup K)}
    (h : IsMaxParabolic2 (⊤ : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup K)) P) :
    IsMaxParabolic2 L (P.map (burnsideB46_pi π)) := by
  rw [burnsideB46_p3_L_eq_map H]
  exact burnsideB46_p3_isMaxParabolic2_map (burnsideB46_pi_injective H) h

theorem burnsideB46_part_3_twisted (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n)
    (hmax : ∀ x : CFSG.Quasithin.JonesParshall.Ix3 → K, x ≠ 0 →
      IsMaxParabolic2 (⊤ : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup K)) (burnsideB46_P1 K x)) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧
        IsNatGL2QuotTw K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) := by
  intro V₁ P₁ R₁ Z₁ V₃ A₁ h
  obtain ⟨x, hx0, hV₁, hP, hR, hZ, hV₃⟩ := burnsideB46_cfg1_point H h
  have hF3 : burnsideB46_F3 K x ≠ ⊥ := by
    intro hbot
    have h1 := burnsideB46_p3_F3_card hx0
    rw [hbot, finrank_bot] at h1
    omega
  have hA : A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) :=
    burnsideB46_cfg1_A1 hqs H hn hF3 hV₃ h.2.2.2.2.2
  have hinj := burnsideB46_pi_injective H
  subst hP hR hZ hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [burnsideB46_p3_L_eq_map H]
    exact burnsideB46_p3_isMaxParabolic2_map hinj (hmax x hx0)
  · rw [Subgroup.card_map_of_injective hinj]
    exact burnsideB46_p3_card_R1 hx0
  · rw [← Subgroup.map_bot (burnsideB46_pi π), burnsideB46_IsNatGL2QuotTw_iff,
      burnsideB46_p3_NatQ_map _ hinj]
    exact burnsideB46_p3_natQ_Z hx0
  · exact burnsideB46_isFPre_iff.mpr ⟨_, burnsideB46_p3_F3_card hx0, hV₃⟩
  · rw [Subgroup.card_map_of_injective hinj]
    exact ⟨burnsideB46_p3_isElemAbelian_map (burnsideB46_p3_A1_facts hx0).1,
      (burnsideB46_p3_A1_facts hx0).2⟩
  · rw [burnsideB46_p3_isNatGL2Quot_iff, burnsideB46_p3_NatQ_map _ hinj]
    exact burnsideB46_p3_natQ_RA hx0
  · intro E hE
    have hE' := hE.trans (burnsideB46_p3_E_eq H hx0)
    refine ⟨burnsideB46_isFPre_iff.mpr ⟨_, burnsideB46_p3_finrank_hyp hx0, hE'⟩, ?_⟩
    rw [hE', burnsideB46_p3_comm_eq H hx0, hV₃]

theorem burnsideB46_part_3 (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) (h3 : ∀ w : K, w ^ 3 = 1 → w = 1)
    (hmax : ∀ x : CFSG.Quasithin.JonesParshall.Ix3 → K, x ≠ 0 →
      IsMaxParabolic2 (⊤ : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup K)) (burnsideB46_P1 K x)) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2Quot K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) := by
  intro V₁ P₁ R₁ Z₁ V₃ A₁ h
  obtain ⟨h1, h2, h3', h4, h5, h6, h7⟩ := burnsideB46_part_3_twisted hqs H hn hmax V₁ P₁ R₁ Z₁ V₃ A₁ h
  refine ⟨h1, h2, ?_, h4, h5, h6, h7⟩
  rw [burnsideB46_p3_isNatGL2Quot_iff]
  exact burnsideB46_p3_natQ_untwist h3 (burnsideB46_IsNatGL2QuotTw_iff.mp h3')

end P3i

section P3j

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [CharP K 2] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p3_cfg1_exists (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)), B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧
        P₁ = (burnsideB46_P1 K (eu 0 (1 : K))).map (burnsideB46_pi π) ∧
        R₁ = (burnsideB46_R1 K (eu 0 (1 : K))).map (burnsideB46_pi π) ∧
        Z₁ = (burnsideB46_Z1 K (eu 0 (1 : K))).map (burnsideB46_pi π) := by
  have hx0 : (eu 0 (1 : K) : Ix3 → K) ≠ 0 := by
    intro h
    have := congrFun h (.inl 0)
    simp [eu] at this
  have hinj := burnsideB46_pi_injective H
  have hF3 : burnsideB46_F3 K (eu 0 (1 : K)) ≠ ⊥ := by
    intro hbot
    have h1 := burnsideB46_p3_F3_card hx0
    rw [hbot, finrank_bot] at h1
    omega
  have key : ∀ g : MulAut V,
      (∀ v ∈ burnsideB46_pre θ (burnsideB46_F3 K (eu 0 (1 : K))), g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K (eu 0 (1 : K)) →
        burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    intro g
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  refine ⟨burnsideB46_pre θ (burnsideB46_pt K (eu 0 1)),
    (burnsideB46_P1 K (eu 0 (1 : K))).map (burnsideB46_pi π),
    (burnsideB46_R1 K (eu 0 (1 : K))).map (burnsideB46_pi π),
    (burnsideB46_Z1 K (eu 0 (1 : K))).map (burnsideB46_pi π),
    burnsideB46_pre θ (burnsideB46_F3 K (eu 0 (1 : K))),
    (burnsideB46_A1 K (eu 0 (1 : K))).map (burnsideB46_pi π), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl,
    rfl⟩
  · refine burnsideB46_isFPre_iff.mpr ⟨_, ?_, rfl⟩
    exact finrank_span_singleton hx0
  · exact (burnsideB46_stab_pre H _).symm
  · exact (burnsideB46_pCoreOf_map _ hinj _).symm
  · exact (burnsideB46_centerOf_map _ hinj _).symm
  · exact (burnsideB46_cPre_map H _).symm
  · intro g
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨H.le (burnsideB46_pi_mem_L H γ), (key _).2 fun v hv => ?_⟩
      rw [burnsideB46_f_act H]
      exact hγ _ hv
    · rintro ⟨hgG, hg⟩
      have hgL : g ∈ L := burnsideB46_mem_L_of_fix hqs H hn hgG hF3 ((key g).1 hg)
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hgL
      refine ⟨γ, fun w hw => ?_, rfl⟩
      obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
      rw [← burnsideB46_f_act H γ v]
      exact (key _).1 hg v hw

theorem burnsideB46_p3_not_isNatGL2Quot_Z1 (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {ω : K} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)), B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧
        ¬ IsNatGL2Quot K P₁ R₁ Z₁ ⊥ := by
  obtain ⟨V₁, P₁, R₁, Z₁, V₃, A₁, hcfg, hP, hR, hZ⟩ := burnsideB46_p3_cfg1_exists hqs H hn
  refine ⟨V₁, P₁, R₁, Z₁, V₃, A₁, hcfg, ?_⟩
  rw [hP, hR, hZ, ← Subgroup.map_bot (burnsideB46_pi π), burnsideB46_p3_isNatGL2Quot_iff,
    burnsideB46_p3_NatQ_map _ (burnsideB46_pi_injective H), ← burnsideB46_p3_isNatGL2Quot_iff]
  exact burnsideB46_p3_not_isNatGL2Quot_Z1_eu h3 h1

end P3j

section P3k

variable {K : Type} [Field K] [Finite K]

theorem burnsideB46_p3_h3_of_odd {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) :
    ∀ w : K, w ^ 3 = 1 → w = 1 := by
  intro w hw
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  by_contra hw1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let u : Kˣ := Units.mk0 w hw0
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hw)
  have hu1 : u ≠ 1 := fun h => hw1 (by simpa [u] using congrArg Units.val h)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard u
  rw [Nat.card_units, hK] at hdvd
  obtain ⟨m, rfl⟩ := hn
  have h4 : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * m + 1) = N at hdvd h4
  omega

theorem burnsideB46_p3_exists_cube_root_of_even {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Even n) : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hn
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK, hm]
    have h4 : 2 ^ (m + m) % 3 = 1 := by
      rw [← two_mul, pow_mul]
      norm_num [Nat.pow_mod]
    have hpos : 1 ≤ 2 ^ (m + m) := Nat.one_le_two_pow
    generalize 2 ^ (m + m) = N at h4 hpos
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨u, ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one u
    rw [hu] at h1
    simpa using congrArg Units.val h1
  · intro h
    have h1 : u = 1 := Units.ext h
    rw [h1, orderOf_one] at hu
    omega

end P3k

section P3n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p3_cfg1_A1_of_GL [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) (hGL : G = L)
    {x : CFSG.Quasithin.JonesParshall.Ix3 → K} {V₃ : Subgroup V} {A₁ : Subgroup (MulAut V)}
    (hV₃ : V₃ = burnsideB46_pre θ (burnsideB46_F3 K x))
    (hA : ∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) :
    A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) := by
  have key : ∀ (g : MulAut V), (∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K x → burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    intro g
    rw [hV₃]
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  ext g
  rw [hA]
  constructor
  · rintro ⟨hgG, hg⟩
    have hgL : g ∈ L := hGL ▸ hgG
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hgL
    refine ⟨γ, fun w hw => ?_, rfl⟩
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
    rw [← burnsideB46_f_act H]
    exact (key _).1 hg v hw
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨H.le (burnsideB46_pi_mem_L H γ), (key _).2 fun v hv => ?_⟩
    rw [burnsideB46_f_act H]
    exact hγ _ hv

theorem burnsideB46_part_3_one (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2Quot K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) := by
  haveI := burnsideB46_charP H
  intro V₁ P₁ R₁ Z₁ V₃ A₁ h
  obtain ⟨x, hx0, hV₁, hP, hR, hZ, hV₃⟩ := burnsideB46_cfg1_point H h
  have hA : A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) :=
    burnsideB46_p3_cfg1_A1_of_GL H hGL hV₃ h.2.2.2.2.2
  have hinj := burnsideB46_pi_injective H
  have hmax := burnsideB46_mp_hmax1 H.card H.one_le hx0
  have h3 : ∀ w : K, w ^ 3 = 1 → w = 1 :=
    burnsideB46_p3_h3_of_odd H.card (by rw [hn1]; exact odd_one)
  subst hP hR hZ hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [burnsideB46_p3_L_eq_map H]
    exact burnsideB46_p3_isMaxParabolic2_map hinj hmax
  · rw [Subgroup.card_map_of_injective hinj]
    exact burnsideB46_p3_card_R1 hx0
  · rw [burnsideB46_p3_isNatGL2Quot_iff, ← Subgroup.map_bot (burnsideB46_pi π),
      burnsideB46_p3_NatQ_map _ hinj]
    exact burnsideB46_p3_natQ_untwist h3 (burnsideB46_p3_natQ_Z hx0)
  · exact burnsideB46_isFPre_iff.mpr ⟨_, burnsideB46_p3_F3_card hx0, hV₃⟩
  · rw [Subgroup.card_map_of_injective hinj]
    exact ⟨burnsideB46_p3_isElemAbelian_map (burnsideB46_p3_A1_facts hx0).1,
      (burnsideB46_p3_A1_facts hx0).2⟩
  · rw [burnsideB46_p3_isNatGL2Quot_iff, burnsideB46_p3_NatQ_map _ hinj]
    exact burnsideB46_p3_natQ_RA hx0
  · intro E hE
    have hE' := hE.trans (burnsideB46_p3_E_eq H hx0)
    refine ⟨burnsideB46_isFPre_iff.mpr ⟨_, burnsideB46_p3_finrank_hyp hx0, hE'⟩, ?_⟩
    rw [hE', burnsideB46_p3_comm_eq H hx0, hV₃]

end P3n

section ASModel

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {F : Type} [Field F] [CharP F 2]

theorem burnsideB46_as_eq_of_act {γ δ : ↥(cayleyGroup F)} (h : ∀ w, g2Act γ w = g2Act δ w) :
    γ = δ := by
  have h1 : δ⁻¹ * γ = 1 := cayley_eq_one fun x => by
    rw [g2Act_mul_apply, h, g2Act_inv_apply]
  exact (inv_mul_eq_one.mp h1).symm

theorem burnsideB46_as_exists_q6 (w : Ix3 → F) : ∃ a b c d e f : F, w = q6 a b c d e f :=
  ⟨_, _, _, _, _, _, q6_eta w⟩

@[expose] def burnsideB46_as_k1 (F : Type) [Field F] [CharP F 2] (α p q' : F) :
    ↥(cayleyGroup F) :=
  g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)

theorem burnsideB46_as_k1_act (α p q' a b c d e f : F) :
    g2Act (burnsideB46_as_k1 F α p q') (q6 a b c d e f) =
      q6 (a + p * b + q' * c + α * α * d) b c d (e + p * d + α * c) (f + q' * d + α * b) :=
  g2Act_A1 α p q' a b c d e f

theorem burnsideB46_as_k1_mem (α p q' : F) : burnsideB46_as_k1 F α p q' ∈ A1 F :=
  kerElt_mem_A1 α p q'

theorem burnsideB46_as_exists_k1 {g : ↥(cayleyGroup F)} (hg : g ∈ A1 F) :
    ∃ α p q' : F, g = burnsideB46_as_k1 F α p q' :=
  exists_eq_of_mem_A1 hg

theorem burnsideB46_as_A1_comm {γ δ : ↥(cayleyGroup F)} (hγ : γ ∈ A1 F) (hδ : δ ∈ A1 F) :
    γ * δ = δ * γ := by
  obtain ⟨α, p, q', rfl⟩ := burnsideB46_as_exists_k1 hγ
  obtain ⟨α', p', q'', rfl⟩ := burnsideB46_as_exists_k1 hδ
  refine burnsideB46_as_eq_of_act fun w => ?_
  obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_as_exists_q6 w
  rw [g2Act_mul_apply (burnsideB46_as_k1 F α p q'), g2Act_mul_apply (burnsideB46_as_k1 F α' p' q''),
    burnsideB46_as_k1_act, burnsideB46_as_k1_act, burnsideB46_as_k1_act, burnsideB46_as_k1_act]
  exact q6_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem burnsideB46_as_A1_sq {γ : ↥(cayleyGroup F)} (hγ : γ ∈ A1 F) : γ * γ = 1 := by
  obtain ⟨α, p, q', rfl⟩ := burnsideB46_as_exists_k1 hγ
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine burnsideB46_as_eq_of_act fun w => ?_
  obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_as_exists_q6 w
  rw [g2Act_mul_apply (burnsideB46_as_k1 F α p q'), burnsideB46_as_k1_act, burnsideB46_as_k1_act,
    map_one]
  refine q6_congr ?_ rfl rfl rfl ?_ ?_
  · linear_combination (p * b + q' * c + α * α * d) * h2
  · linear_combination (p * d + α * c) * h2
  · linear_combination (q' * d + α * b) * h2

theorem burnsideB46_as_card_A1 [Finite F] : Nat.card ↥(A1 F) = Nat.card F ^ 3 := by
  refine le_antisymm card_A1_le ?_
  have hinj : Function.Injective (fun t : Fin 3 → F =>
      (⟨burnsideB46_as_k1 F (t 0) (t 1) (t 2), burnsideB46_as_k1_mem _ _ _⟩ : ↥(A1 F))) := by
    intro t t' h
    have h1 := congrArg (fun g : ↥(A1 F) => g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0)) h
    simp only [burnsideB46_as_k1_act] at h1
    obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
    funext i
    fin_cases i
    · show t 0 = t' 0
      exact eq_of_mul_self_eq_charTwo (by linear_combination e0)
    · show t 1 = t' 1
      linear_combination e4
    · show t 2 = t' 2
      linear_combination e5
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_fin] at h1

theorem burnsideB46_as_A1_ne_bot : A1 F ≠ ⊥ := by
  intro h
  have h1 : burnsideB46_as_k1 F 1 0 0 ∈ A1 F := burnsideB46_as_k1_mem _ _ _
  rw [h, Subgroup.mem_bot] at h1
  have h2 := congrArg (fun g => g2Act g (q6 (0 : F) 0 0 1 0 0)) h1
  simp only [burnsideB46_as_k1_act, map_one] at h2
  obtain ⟨e0, -⟩ := q6_inj h2
  have : (1 : F) = 0 := by linear_combination e0
  exact one_ne_zero this

theorem burnsideB46_as_card_rootD_ge [Finite F] {v₀ : F × F} (hv₀ : v₀ ≠ 0) :
    Nat.card F ≤ Nat.card ↥(rootD (dirV v₀)) := by
  have hmem : ∀ t : F, g2A (uSL (t * v₀.1) (t * v₀.2) 0) ∈ rootD (dirV v₀) := fun t =>
    ⟨(t * v₀.1, t * v₀.2), onLine_dirV_of hv₀ (show t * v₀.1 * v₀.2 = t * v₀.2 * v₀.1 by ring), rfl⟩
  have hinj : Function.Injective (fun t : F =>
      (⟨g2A (uSL (t * v₀.1) (t * v₀.2) 0), hmem t⟩ : ↥(rootD (dirV v₀)))) := by
    intro t t' h
    have h1 := g2A_uSL_injective (v := (t * v₀.1, t * v₀.2)) (w := (t' * v₀.1, t' * v₀.2))
      (congrArg Subtype.val h)
    obtain ⟨e1, e2⟩ := Prod.mk.inj h1
    by_cases hv : v₀.1 = 0
    · have hv2 : v₀.2 ≠ 0 := fun h0 => hv₀ (Prod.ext hv h0)
      exact mul_right_cancel₀ hv2 e2
    · exact mul_right_cancel₀ hv e1
  exact Nat.card_le_card_of_injective _ hinj

theorem burnsideB46_as_card_rootD_none [Finite F] :
    Nat.card F ≤ Nat.card ↥(rootD (none : Option F)) := by
  have h := burnsideB46_as_card_rootD_ge (F := F) (v₀ := (0, 1)) (by simp)
  simpa [dirV] using h

theorem burnsideB46_as_A1_fixStable [Finite F] : FixStable (Nat.card F ^ 2) (A1 F) := by
  intro B hB hcard w hw γ hγ
  by_cases hw3 : w ∈ stdF F 3
  · exact hγ w hw3
  exfalso
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hBq : Nat.card F < Nat.card ↥B := by
    have h3 : Nat.card F ^ 2 * Nat.card F < Nat.card F ^ 2 * Nat.card ↥B := by
      rw [show Nat.card F ^ 2 * Nat.card F = Nat.card F ^ 3 by ring, ← burnsideB46_as_card_A1]
      exact hcard
    exact Nat.lt_of_mul_lt_mul_left h3
  obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_as_exists_q6 w
  rw [mem_stdF_three, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0] at hw3
  have hfix : ∀ β ∈ B, ∃ α p q' : F, β = burnsideB46_as_k1 F α p q' ∧
      p * b + q' * c + α * α * d = 0 ∧ p * d + α * c = 0 ∧ q' * d + α * b = 0 := by
    intro β hβ
    obtain ⟨α, p, q', rfl⟩ := burnsideB46_as_exists_k1 (hB hβ)
    have h1 := hw _ hβ
    rw [burnsideB46_as_k1_act] at h1
    obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
    exact ⟨α, p, q', rfl, by linear_combination e0, by linear_combination e4,
      by linear_combination e5⟩
  by_cases hd : d = 0
  ·
    have hbc : b ≠ 0 ∨ c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw3 ⟨hcon.1, hcon.2, hd⟩
    obtain ⟨d₀, hd₀⟩ := exists_onLine_of_linear hbc
    have hBD : B ≤ rootD d₀ := by
      intro β hβ
      obtain ⟨α, p, q', rfl, e1, e2, e3⟩ := hfix β hβ
      subst hd
      have hα : α = 0 := by
        rcases hbc with hb | hc
        · exact (mul_eq_zero.mp (by linear_combination e3)).resolve_right hb
        · exact (mul_eq_zero.mp (by linear_combination e2)).resolve_right hc
      subst hα
      refine ⟨(p, q'), hd₀ (p, q') (by linear_combination e1), ?_⟩
      exact eq_uSL_of_A1
    exact absurd (hBq.trans_le ((Subgroup.card_le_of_le hBD).trans (card_rootD_le d₀)))
      (lt_irrefl _)
  ·
    have hB1 : B ≤ ⊥ := by
      intro β hβ
      obtain ⟨α, p, q', rfl, e1, e2, e3⟩ := hfix β hβ
      have hαd : (α * d) * (α * d) = 0 := by
        linear_combination d * e1 - b * e2 - c * e3 + (α * b * c) * h2
      have hα : α = 0 := (mul_eq_zero.mp (mul_self_eq_zero.mp hαd)).resolve_right hd
      subst hα
      have hp : p = 0 := (mul_eq_zero.mp (by linear_combination e2)).resolve_right hd
      have hq' : q' = 0 := (mul_eq_zero.mp (by linear_combination e3)).resolve_right hd
      subst hp hq'
      rw [Subgroup.mem_bot]
      exact eq_uSL_of_A1.trans (by rw [CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one])
    have h1 : Nat.card ↥B ≤ 1 := by
      have := Subgroup.card_le_of_le hB1
      rwa [Subgroup.card_bot] at this
    omega

theorem burnsideB46_as_A1_not_fixStable [Finite F] :
    ¬ FixStable (2 * Nat.card F ^ 2) (A1 F) := by
  intro h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hD := burnsideB46_as_card_rootD_none (F := F)
  have hpos : 0 < Nat.card F ^ 3 := by positivity
  have hlt : Nat.card ↥(A1 F) <
      2 * Nat.card F ^ 2 * Nat.card ↥(rootD (none : Option F)) := by
    rw [burnsideB46_as_card_A1]
    calc Nat.card F ^ 3 < 2 * Nat.card F ^ 2 * Nat.card F := by
          rw [show 2 * Nat.card F ^ 2 * Nat.card F = 2 * Nat.card F ^ 3 by ring]
          omega
      _ ≤ _ := Nat.mul_le_mul_left _ hD
  have h1 := h (rootD none) (rootD_le_A1 none) hlt (rootW none)
    (fun b hb => rootD_fix none hb) (burnsideB46_as_k1 F 1 0 0) (burnsideB46_as_k1_mem _ _ _)
  have h2 : g2Act (burnsideB46_as_k1 F 1 0 0) (q6 (0 : F) 1 0 0 0 0) = q6 0 1 0 0 0 0 := h1
  rw [burnsideB46_as_k1_act] at h2
  obtain ⟨-, -, -, -, -, e5⟩ := q6_inj h2
  have : (1 : F) = 0 := by linear_combination e5
  exact one_ne_zero this

theorem burnsideB46_as_exists_conj_le_A1 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) {k : ℕ} (hk1 : Nat.card F < k)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) (hΓne : Γ ≠ ⊥) (hP : FixStable k Γ) :
    ∃ x : ↥(cayleyGroup F), Γ.map (MulAut.conj x⁻¹).toMonoidHom ≤ A1 F ∧
      ∀ w, (∀ γ ∈ Γ.map (MulAut.conj x⁻¹).toMonoidHom, g2Act γ w = w) → w ∈ stdF F 3 := by
  have := finite_cayleyGroup (F := F)
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hconj1 : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      γ * γ = 1 := by
    rintro x _ ⟨g, hg, rfl⟩
    change x * g * x⁻¹ * (x * g * x⁻¹) = 1
    rw [show x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ by group, hΓ1 g hg]
    group
  have hconjc : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      ∀ δ ∈ Γ.map (MulAut.conj x).toMonoidHom, γ * δ = δ * γ := by
    rintro x _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    change x * g * x⁻¹ * (x * h * x⁻¹) = x * h * x⁻¹ * (x * g * x⁻¹)
    rw [show x * g * x⁻¹ * (x * h * x⁻¹) = x * (g * h) * x⁻¹ by group, hΓc g hg h hh]
    group
  have htriv : ∀ x : ↥(cayleyGroup F),
      (∀ w, ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom, g2Act γ w = w) → False := by
    intro x h
    apply hΓne
    rw [eq_bot_iff]
    intro g hg
    have h1 : x * g * x⁻¹ = 1 := cayley_eq_one fun w => h w _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_bot]
    calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  by_cases hA : ∃ r ∈ Γ, ∃ x, qr r x ≠ 0
  ·
    obtain ⟨r, hrΓ, x₀, hx₀⟩ := hA
    obtain ⟨p, hp⟩ := exists_qr_eq_sq (hΓ1 r hrΓ)
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply hx₀
      rw [hp]
      simp [polarQ]
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hp0
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hP' : FixStable k Γ' := hΓ' ▸ fixStable_map_conj hP g⁻¹
    have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := hΓ' ▸ hconj1 g⁻¹
    have hΓ'c : ∀ γ ∈ Γ', ∀ δ ∈ Γ', γ * δ = δ * γ := hΓ' ▸ hconjc g⁻¹
    have hr' : g⁻¹ * r * g ∈ Γ' := by
      have h1 := hΓ' ▸ conj_apply_mem_map g⁻¹ hrΓ
      rwa [inv_inv] at h1
    have hqr' : ∀ x, qr (g⁻¹ * r * g) x = x (.inr 0) * x (.inr 0) := by
      intro x
      have h1 := qr_conj g⁻¹ r (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      rw [h1, hp, ← polarQ_g2Act g⁻¹, g2Act_inv_apply, ← hg, g2Act_inv_apply, polarQ_eu0]
    obtain ⟨a, b, hab⟩ := eq_kerElt_of_qr (hΓ'1 _ hr') hqr'
    have hS : Γ' ≤ stabV0 F := fun s hs =>
      fix_of_qr_sq (r := g⁻¹ * r * g) (p := eu 0 1) (fun x => by rw [hqr', polarQ_eu0])
        (hΓ'c s hs _ hr')
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ A1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      have hc := hΓ'c _ hhΓ' _ hr'
      rw [hab] at hc
      obtain ⟨rfl, rfl⟩ := kerElt_eq_of_comm hc
      exact kerElt_mem_A1 α p' q'
    have hlt : Nat.card ↥Γ' < k * Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F)) :=
      (card_le_mul_card_inf_R1 hF hn hS hΓ'1).trans_lt
        (Nat.mul_lt_mul_of_pos_right hk1 Nat.card_pos)
    have hΓ'A1 : Γ' ≤ A1 F := fun γ hγ w hw =>
      hP' _ inf_le_left hlt w (fun h hh => hR hh w hw) γ hγ
    have hfix' : ∀ w, (∀ γ ∈ Γ', g2Act γ w = w) → w ∈ stdF F 3 := by
      intro w hw
      have h1 := hw _ hr'
      rw [hab] at h1
      exact mem_F3_of_fix_short h1
    refine ⟨g, ?_, ?_⟩
    · rw [← hΓ']
      exact hΓ'A1
    · rw [← hΓ']
      exact hfix'
  ·
    have hA' : ∀ r ∈ Γ, ∀ x, qr r x = 0 := fun r hr x => by
      by_contra h
      exact hA ⟨r, hr, x, h⟩
    exfalso
    obtain ⟨w₀, hw₀, hfix₀⟩ := exists_fix_ne_zero hΓ1
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hw₀
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hP' : FixStable k Γ' := hΓ' ▸ fixStable_map_conj hP g⁻¹
    have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := hΓ' ▸ hconj1 g⁻¹
    have hS : Γ' ≤ stabV0 F := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩
      show g2Act (g⁻¹ * γ * g⁻¹⁻¹) (eu 0 1) = eu 0 1
      rw [inv_inv, g2Act_mul_apply, g2Act_mul_apply, hg, hfix₀ γ hγ, ← hg, g2Act_inv_apply]
    have hq0 : ∀ r ∈ Γ', ∀ x, qr r x = 0 := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩ x
      have h1 := qr_conj g⁻¹ γ (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      change qr (g⁻¹ * γ * g⁻¹⁻¹) x = 0
      rw [inv_inv, h1, hA' γ hγ]
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ Z1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq_of_qr_zero (hq0 _ hhΓ')
      exact ⟨(p', q'), eq_uSL_of_A1⟩
    have hlt : Nat.card ↥Γ' < k * Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F)) :=
      (card_le_mul_card_inf_R1 hF hn hS hΓ'1).trans_lt
        (Nat.mul_lt_mul_of_pos_right hk1 Nat.card_pos)
    have hfixR := hP' _ inf_le_left hlt
    have hF3 : ∀ γ ∈ Γ', γ ∈ A1 F := fun γ hγ w hw =>
      hfixR w (fun h hh => Z1_le_A1 (hR hh) w hw) γ hγ
    obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Γ' ⊓ pCoreOf 2 (stabV0 F), z ≠ 1 := by
      by_contra hcon
      apply htriv g⁻¹
      intro w γ hγ
      rw [← hΓ'] at hγ
      refine hfixR w (fun h hh => ?_) γ hγ
      have h1 : h = 1 := by
        by_contra h1
        exact hcon ⟨h, hh, h1⟩
      rw [h1, map_one]
      rfl
    obtain ⟨v₀, hv₀⟩ := hR hz₀
    have hv₀0 : v₀ ≠ 0 := by
      rintro rfl
      apply hz₀1
      rw [hv₀, Prod.fst_zero, Prod.snd_zero,
        CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]
    by_cases hall : ∀ h ∈ Γ' ⊓ pCoreOf 2 (stabV0 F), ∀ v : F × F,
        h = g2A (uSL v.1 v.2 0) → v.1 * v₀.2 = v.2 * v₀.1
    ·
      have hw : ∀ γ ∈ Γ', g2Act γ (q6 0 v₀.2 v₀.1 0 0 0) = q6 0 v₀.2 v₀.1 0 0 0 := by
        refine hfixR _ fun h hh => ?_
        obtain ⟨v, hv⟩ := hR hh
        have h1 := hall h hh v hv
        rw [hv, g2Act_g2A_uSL]
        refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [q6]
        linear_combination h1 + v.2 * v₀.1 * h2
      have hΓ'D : Γ' ≤ rootD (dirV v₀) := by
        intro γ hγ
        obtain ⟨α, p', q', hγeq⟩ := exists_eq_of_mem_A1 (hF3 γ hγ)
        have h1 := hw γ hγ
        rw [hγeq, g2Act_A1] at h1
        obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
        have hα : α = 0 := by
          by_contra hα
          apply hv₀0
          exact Prod.ext ((mul_eq_zero.mp (by linear_combination e4)).resolve_left hα)
            ((mul_eq_zero.mp (by linear_combination e5)).resolve_left hα)
        subst hα
        refine ⟨(p', q'), onLine_dirV_of hv₀0 ?_, by rw [hγeq, eq_uSL_of_A1]⟩
        linear_combination e0 - q' * v₀.1 * h2
      apply htriv g⁻¹
      intro w γ hγ
      rw [← hΓ'] at hγ
      refine hP' ⊥ bot_le ?_ w (fun b hb => by rw [Subgroup.mem_bot.mp hb, map_one]; rfl) γ hγ
      rw [Subgroup.card_bot, mul_one]
      exact ((Subgroup.card_le_of_le hΓ'D).trans (card_rootD_le _)).trans_lt hk1
    ·
      obtain ⟨h₁, hh₁, v₁, hv₁, hne⟩ : ∃ h ∈ Γ' ⊓ pCoreOf 2 (stabV0 F), ∃ v : F × F,
          h = g2A (uSL v.1 v.2 0) ∧ v.1 * v₀.2 ≠ v.2 * v₀.1 := by
        by_contra hcon
        apply hall
        intro h hh v hv
        by_contra hne
        exact hcon ⟨h, hh, v, hv, hne⟩
      have hfixF3 : ∀ w, (∀ γ ∈ Γ', g2Act γ w = w) → w ∈ stdF F 3 := by
        intro w hw
        have e₀ := hw _ hz₀.1
        have e₁ := hw _ hh₁.1
        rw [hv₀, g2Act_g2A_uSL] at e₀
        rw [hv₁, g2Act_g2A_uSL] at e₁
        have a0 := congrFun e₀ (.inl 0)
        have a4 := congrFun e₀ (.inr 1)
        have a5 := congrFun e₀ (.inr 2)
        have b0 := congrFun e₁ (.inl 0)
        simp only [q6_apply_inl0, q6_apply_inr1, q6_apply_inr2] at a0 a4 a5 b0
        have hd : w (.inr 0) = 0 := by
          by_contra hd
          apply hv₀0
          exact Prod.ext ((mul_eq_zero.mp (by linear_combination a4)).resolve_right hd)
            ((mul_eq_zero.mp (by linear_combination a5)).resolve_right hd)
        have hdet : v₁.1 * v₀.2 - v₁.2 * v₀.1 ≠ 0 := sub_ne_zero.mpr hne
        have hb : w (.inl 1) = 0 := (mul_eq_zero.mp (show w (.inl 1) *
            (v₁.1 * v₀.2 - v₁.2 * v₀.1) = 0 by
          linear_combination v₀.2 * b0 - v₁.2 * a0)).resolve_right hdet
        have hc : w (.inl 2) = 0 := (mul_eq_zero.mp (show w (.inl 2) *
            (v₁.1 * v₀.2 - v₁.2 * v₀.1) = 0 by
          linear_combination v₁.1 * a0 - v₀.1 * b0)).resolve_right hdet
        exact mem_stdF_three.mpr ⟨hb, hc, hd⟩
      have hZ : Γ' ≤ Z1 F := by
        intro γ hγ
        obtain ⟨α, p', q', hγeq⟩ := exists_eq_of_mem_A1 (hF3 γ hγ)
        have h1 := hq0 γ hγ (q6 0 0 0 1 0 0)
        rw [hγeq, qr_kerElt_v0] at h1
        have hα : α = 0 := mul_self_eq_zero.mp (by linear_combination h1)
        subst hα
        exact ⟨(p', q'), by rw [hγeq, eq_uSL_of_A1]⟩
      have hcontra : k * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) ≤ Nat.card ↥Γ' := by
        by_contra h
        exact rootW_not_mem _ (hfixF3 _ (hP' _ inf_le_left (not_le.mp h) _
          fun b hb => rootD_fix _ hb.2))
      have hDle : rootD (dirV v₀) ≤ Z1 F := by
        rintro _ ⟨v, -, rfl⟩
        exact ⟨v, rfl⟩
      have hDq : Nat.card F ≤ Nat.card ↥(rootD (dirV v₀)) :=
        burnsideB46_as_card_rootD_ge hv₀0
      have hidx : Nat.card ↥Γ' ≤ Nat.card F * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) := by
        have h1 := Subgroup.relIndex_mul_card (H := rootD (dirV v₀)) (K := Γ')
        have h3 := Subgroup.relIndex_mul_card (H := rootD (dirV v₀)) (K := Z1 F)
        rw [inf_eq_left.mpr hDle] at h3
        have h4 : (rootD (dirV v₀)).relIndex Γ' ≤ (rootD (dirV v₀)).relIndex (Z1 F) :=
          Subgroup.relIndex_le_of_le_right hZ (E3.relIndex_ne_zero' _ _)
        have h5 : (rootD (dirV v₀)).relIndex (Z1 F) ≤ Nat.card F := by
          have h6 : (rootD (dirV v₀)).relIndex (Z1 F) * Nat.card F ≤
              Nat.card F * Nat.card F := by
            calc (rootD (dirV v₀)).relIndex (Z1 F) * Nat.card F
                ≤ (rootD (dirV v₀)).relIndex (Z1 F) * Nat.card ↥(rootD (dirV v₀)) :=
                  Nat.mul_le_mul_left _ hDq
              _ = Nat.card ↥(Z1 F) := h3
              _ ≤ Nat.card F ^ 2 := card_Z1_le
              _ = Nat.card F * Nat.card F := sq _
          exact Nat.le_of_mul_le_mul_right h6 (by omega)
        rw [inf_comm] at h1
        calc Nat.card ↥Γ' = (rootD (dirV v₀)).relIndex Γ' *
              Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) := h1.symm
          _ ≤ Nat.card F * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) :=
            Nat.mul_le_mul_right _ (h4.trans h5)
      have h7 : k * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) ≤ Nat.card F * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) :=
        hcontra.trans hidx
      have h8 : k ≤ Nat.card F := Nat.le_of_mul_le_mul_right h7 Nat.card_pos
      omega

@[expose] def burnsideB46_as_k5 (F : Type) [Field F] [CharP F 2] (α β γ p q' : F) :
    ↥(cayleyGroup F) :=
  g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL p q' 0)

theorem burnsideB46_as_k5_act (α β γ p q' a b c d e f : F) :
    g2Act (burnsideB46_as_k5 F α β γ p q') (q6 a b c d e f) =
      q6 ((a + p * b + q' * c + β * (f + q' * d) + γ * (e + p * d)) + α * α * d)
        (b + γ * d) (c + β * d) d
        ((e + p * d + (β * b + γ * c) * β) + α * (c + β * d))
        ((f + q' * d + (β * b + γ * c) * γ) + α * (b + γ * d)) :=
  g2Act_kerElt α β γ p q' a b c d e f

theorem burnsideB46_as_exists_k5 [Finite F] {g : ↥(cayleyGroup F)}
    (hg : g ∈ pCoreOf 2 (stabV0 F)) :
    ∃ α β γ p q' : F, g = burnsideB46_as_k5 F α β γ p q' := by
  obtain ⟨hS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hg
  exact eq_of_levi1Mat_eq_one hS hM

theorem burnsideB46_as_k5_v0 (α β γ p q' : F) :
    g2Act (burnsideB46_as_k5 F α β γ p q') (q6 0 0 0 1 0 0) (.inl 2) = β ∧
      g2Act (burnsideB46_as_k5 F α β γ p q') (q6 0 0 0 1 0 0) (.inl 1) = γ :=
  ⟨by rw [burnsideB46_as_k5_act, q6_apply_inl2]; ring,
    by rw [burnsideB46_as_k5_act, q6_apply_inl1]; ring⟩

theorem burnsideB46_as_k5_sq {α β γ p q' : F}
    (h : burnsideB46_as_k5 F α β γ p q' * burnsideB46_as_k5 F α β γ p q' = 1) :
    α * β = 0 ∧ α * γ = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : g2Act (burnsideB46_as_k5 F α β γ p q' * burnsideB46_as_k5 F α β γ p q')
      (q6 0 0 0 1 0 0) = q6 0 0 0 1 0 0 := by
    rw [h, map_one]
    rfl
  rw [g2Act_mul_apply, burnsideB46_as_k5_act, burnsideB46_as_k5_act] at h1
  obtain ⟨-, -, -, -, e4, e5⟩ := q6_inj h1
  exact ⟨by linear_combination e4 + (-α * β - β ^ 2 * γ - p) * h2,
    by linear_combination e5 + (-α * γ - β * γ ^ 2 - q') * h2⟩

theorem burnsideB46_as_k5_comm {α β γ p q' α' β' γ' p' q'' : F}
    (h : burnsideB46_as_k5 F α β γ p q' * burnsideB46_as_k5 F α' β' γ' p' q'' =
      burnsideB46_as_k5 F α' β' γ' p' q'' * burnsideB46_as_k5 F α β γ p q') :
    (β * γ' + γ * β') * (β + β') = α * β' + α' * β ∧
      (β * γ' + γ * β') * (γ + γ') = α * γ' + α' * γ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 := congrArg (fun y => g2Act y (q6 (0 : F) 0 0 1 0 0)) h
  simp only [g2Act_mul_apply (burnsideB46_as_k5 F α β γ p q'),
    g2Act_mul_apply (burnsideB46_as_k5 F α' β' γ' p' q''), burnsideB46_as_k5_act] at h1
  obtain ⟨-, -, -, -, e4, e5⟩ := q6_inj h1
  exact ⟨by linear_combination e4 + (-α * β' + β * β' * γ' + β' ^ 2 * γ) * h2,
    by linear_combination e5 + (-α * γ' + β * γ' ^ 2 + β' * γ * γ') * h2⟩

theorem burnsideB46_as_delta_eq_zero {α β γ α' β' γ' : F}
    (h1 : α * β = 0) (h2 : α * γ = 0) (h1' : α' * β' = 0) (h2' : α' * γ' = 0)
    (hc1 : (β * γ' + γ * β') * (β + β') = α * β' + α' * β)
    (hc2 : (β * γ' + γ * β') * (γ + γ') = α * γ' + α' * γ) : β * γ' + γ * β' = 0 := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  by_contra hΔ
  rcases eq_or_ne α 0 with hα | hα
  · rcases eq_or_ne α' 0 with hα' | hα'
    · subst hα hα'
      have e1 : (β + β') = 0 := by
        have := mul_eq_zero.mp (show (β * γ' + γ * β') * (β + β') = 0 by
          linear_combination hc1)
        exact this.resolve_left hΔ
      have e2 : (γ + γ') = 0 := by
        have := mul_eq_zero.mp (show (β * γ' + γ * β') * (γ + γ') = 0 by
          linear_combination hc2)
        exact this.resolve_left hΔ
      apply hΔ
      have hb : β' = β := by linear_combination e1 - β * h2F
      have hg : γ' = γ := by linear_combination e2 - γ * h2F
      subst hb hg
      linear_combination β' * γ' * h2F
    · have hb : β' = 0 := (mul_eq_zero.mp h1').resolve_left hα'
      have hg : γ' = 0 := (mul_eq_zero.mp h2').resolve_left hα'
      apply hΔ
      rw [hb, hg]
      ring
  · have hb : β = 0 := (mul_eq_zero.mp h1).resolve_left hα
    have hg : γ = 0 := (mul_eq_zero.mp h2).resolve_left hα
    apply hΔ
    rw [hb, hg]
    ring

theorem burnsideB46_as_card_le_R1 [Finite F] {Γ : Subgroup ↥(cayleyGroup F)}
    (hΓR : Γ ≤ pCoreOf 2 (stabV0 F)) (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) :
    Nat.card ↥Γ ≤ Nat.card ↥(Γ ⊓ A1 F) * Nat.card F := by
  classical
  have := finite_cayleyGroup (F := F)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let bb : ↥Γ → F := fun g => g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 2)
  let cc : ↥Γ → F := fun g => g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 1)
  have hmem : ∀ g : ↥Γ, ∃ α β γ p q' : F, (g : ↥(cayleyGroup F)) =
      burnsideB46_as_k5 F α β γ p q' ∧ bb g = β ∧ cc g = γ ∧ α * β = 0 ∧ α * γ = 0 := by
    intro g
    obtain ⟨α, β, γ, p, q', hg⟩ := burnsideB46_as_exists_k5 (hΓR g.2)
    have hsq : burnsideB46_as_k5 F α β γ p q' * burnsideB46_as_k5 F α β γ p q' = 1 := by
      rw [← hg]
      exact hΓ1 _ g.2
    obtain ⟨s1, s2⟩ := burnsideB46_as_k5_sq hsq
    obtain ⟨b1, c1⟩ := burnsideB46_as_k5_v0 α β γ p q'
    refine ⟨α, β, γ, p, q', hg, ?_, ?_, s1, s2⟩
    · show g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 2) = β
      rw [hg]
      exact b1
    · show g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 1) = γ
      rw [hg]
      exact c1
  have hline : ∀ g h : ↥Γ, bb g * cc h = cc g * bb h := by
    intro g h
    obtain ⟨α, β, γ, p, q', hg, hbg, hcg, s1, s2⟩ := hmem g
    obtain ⟨α', β', γ', p', q'', hh, hbh, hch, s1', s2'⟩ := hmem h
    have hcomm : burnsideB46_as_k5 F α β γ p q' * burnsideB46_as_k5 F α' β' γ' p' q'' =
        burnsideB46_as_k5 F α' β' γ' p' q'' * burnsideB46_as_k5 F α β γ p q' := by
      rw [← hg, ← hh]
      exact hΓc _ g.2 _ h.2
    obtain ⟨c1, c2⟩ := burnsideB46_as_k5_comm hcomm
    have hΔ := burnsideB46_as_delta_eq_zero s1 s2 s1' s2' c1 c2
    rw [hbg, hcg, hbh, hch]
    linear_combination hΔ - (γ * β') * h2
  have hadd : ∀ g h : ↥Γ, bb (g * h) = bb g + bb h ∧ cc (g * h) = cc g + cc h := by
    intro g h
    obtain ⟨α, β, γ, p, q', hg, hbg, hcg, -, -⟩ := hmem g
    obtain ⟨α', β', γ', p', q'', hh, hbh, hch, -, -⟩ := hmem h
    have e1 : bb (g * h) = g2Act (burnsideB46_as_k5 F α β γ p q')
        (g2Act (burnsideB46_as_k5 F α' β' γ' p' q'') (q6 0 0 0 1 0 0)) (.inl 2) := by
      show g2Act ((g * h : ↥Γ) : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 2) = _
      rw [Subgroup.coe_mul, g2Act_mul_apply, hg, hh]
    have e2 : cc (g * h) = g2Act (burnsideB46_as_k5 F α β γ p q')
        (g2Act (burnsideB46_as_k5 F α' β' γ' p' q'') (q6 0 0 0 1 0 0)) (.inl 1) := by
      show g2Act ((g * h : ↥Γ) : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 1) = _
      rw [Subgroup.coe_mul, g2Act_mul_apply, hg, hh]
    rw [e1, e2, burnsideB46_as_k5_act, burnsideB46_as_k5_act, q6_apply_inl2, q6_apply_inl1, hbg,
      hbh, hcg, hch]
    exact ⟨by ring, by ring⟩
  have hone : bb 1 = 0 ∧ cc 1 = 0 := by
    constructor
    · show g2Act ((1 : ↥Γ) : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 2) = 0
      rw [OneMemClass.coe_one, map_one]
      rfl
    · show g2Act ((1 : ↥Γ) : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0) (.inl 1) = 0
      rw [OneMemClass.coe_one, map_one]
      rfl
  have hA1 : ∀ g : ↥Γ, (g : ↥(cayleyGroup F)) ∈ A1 F ↔ bb g = 0 ∧ cc g = 0 := by
    intro g
    obtain ⟨α, β, γ, p, q', hg, hbg, hcg, -, -⟩ := hmem g
    rw [hbg, hcg]
    constructor
    · intro hA
      obtain ⟨α', p', q'', hk⟩ := burnsideB46_as_exists_k1 hA
      have h1 := congrArg (fun y => g2Act y (q6 (0 : F) 0 0 1 0 0)) (hg.symm.trans hk)
      simp only [burnsideB46_as_k5_act, burnsideB46_as_k1_act] at h1
      obtain ⟨-, e1, e2, -⟩ := q6_inj h1
      exact ⟨by linear_combination e2, by linear_combination e1⟩
    · rintro ⟨rfl, rfl⟩
      rw [hg]
      exact kerElt_mem_A1 α p q'
  by_cases hz : ∀ g : ↥Γ, bb g = 0 ∧ cc g = 0
  · have hle : Γ ≤ A1 F := fun g hg => (hA1 ⟨g, hg⟩).mpr (hz ⟨g, hg⟩)
    rw [inf_eq_left.mpr hle]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  · push Not at hz
    obtain ⟨g₀, hg₀⟩ := hz
    let lam : ↥Γ → F := fun g => if bb g₀ = 0 then cc g else bb g
    have hlam : ∀ g : ↥Γ, lam g = 0 ↔ (bb g = 0 ∧ cc g = 0) := by
      intro g
      have hl := hline g₀ g
      by_cases hb0 : bb g₀ = 0
      · have hc0 : cc g₀ ≠ 0 := fun hc0 => hg₀ hb0 hc0
        have : lam g = cc g := if_pos hb0
        rw [this]
        refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
        rw [hb0, zero_mul] at hl
        exact (mul_eq_zero.mp hl.symm).resolve_left hc0
      · have : lam g = bb g := if_neg hb0
        rw [this]
        refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
        rw [h, mul_zero] at hl
        exact (mul_eq_zero.mp hl).resolve_left hb0
    let φ : ↥Γ →* Multiplicative F :=
      { toFun := fun g => Multiplicative.ofAdd (lam g)
        map_one' := by
          show Multiplicative.ofAdd (lam 1) = 1
          have : lam 1 = 0 := by
            show (if bb g₀ = 0 then cc 1 else bb 1) = 0
            split_ifs
            · exact hone.2
            · exact hone.1
          rw [this]
          rfl
        map_mul' := fun g h => by
          show Multiplicative.ofAdd (lam (g * h)) = Multiplicative.ofAdd (lam g) *
            Multiplicative.ofAdd (lam h)
          rw [← ofAdd_add]
          congr 1
          show (if bb g₀ = 0 then cc (g * h) else bb (g * h)) =
            (if bb g₀ = 0 then cc g else bb g) + (if bb g₀ = 0 then cc h else bb h)
          split_ifs
          · exact (hadd g h).2
          · exact (hadd g h).1 }
    have hkerφ : ∀ g : ↥Γ, φ g = 1 ↔ (g : ↥(cayleyGroup F)) ∈ A1 F := by
      intro g
      rw [hA1 g, ← hlam g]
      show Multiplicative.ofAdd (lam g) = 1 ↔ lam g = 0
      exact ofAdd_eq_one
    have h1 := card_le_card_inf_mul φ hkerφ
    have h3 : Nat.card ↥φ.range ≤ Nat.card F :=
      (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq
        (Nat.card_congr Multiplicative.toAdd)
    exact h1.trans (Nat.mul_le_mul_left _ h3)

theorem burnsideB46_as_le_A1_of_le_R1 [Finite F] {k : ℕ} (hk : Nat.card F < k)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓR : Γ ≤ pCoreOf 2 (stabV0 F))
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ)
    (hP : FixStable k Γ) : Γ ≤ A1 F := by
  have h1 := burnsideB46_as_card_le_R1 hΓR hΓ1 hΓc
  have hlt : Nat.card ↥Γ < k * Nat.card ↥(Γ ⊓ A1 F) := by
    calc Nat.card ↥Γ ≤ Nat.card ↥(Γ ⊓ A1 F) * Nat.card F := h1
      _ < Nat.card ↥(Γ ⊓ A1 F) * k := Nat.mul_lt_mul_of_pos_left hk Nat.card_pos
      _ = k * Nat.card ↥(Γ ⊓ A1 F) := mul_comm _ _
  intro γ hγ w hw
  exact hP (Γ ⊓ A1 F) inf_le_left hlt w (fun b hb => hb.2 w hw) γ hγ

end ASModel

section ASV

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_as_mem_fixV_iff [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (v : V) :
    v ∈ fixV A ↔ burnsideB46_f θ v ∈ fixSub (A.comap (burnsideB46_pi π)) := by
  rw [mem_fixSub]
  constructor
  · intro hv γ hγ
    rw [← burnsideB46_f_act H γ v, mem_fixV.1 hv _ (Subgroup.mem_comap.1 hγ)]
  · intro hv a ha
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hAL ha)
    refine burnsideB46_lift_fix_ge2 H hn (burnsideB46_pi_mem_L H γ) ?_
    refine (burnsideB46_f_eq_zero_iff H _).1 ?_
    rw [burnsideB46_f_sub, burnsideB46_f_act H, hv γ (Subgroup.mem_comap.2 ha), sub_self]

theorem burnsideB46_as_fixV_map [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (X : Subgroup ↥(cayleyGroup K)) :
    fixV (X.map (burnsideB46_pi π)) = burnsideB46_pre θ (fixSub X) := by
  have hle : X.map (burnsideB46_pi π) ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact burnsideB46_pi_mem_L H x
  ext v
  rw [burnsideB46_as_mem_fixV_iff H hn hle, burnsideB46_mem_pre,
    Subgroup.comap_map_eq_self_of_injective (burnsideB46_pi_injective H)]

theorem burnsideB46_as_pre_injective (H : burnsideB46_Hyp V n K G L π θ)
    {S S' : Submodule K (Ix3 → K)} (h : burnsideB46_pre θ S = burnsideB46_pre θ S') : S = S' := by
  ext x
  obtain ⟨v, rfl⟩ := burnsideB46_f_surj H x
  exact SetLike.ext_iff.mp h v

theorem burnsideB46_as_mQuot_lt_iff [Finite V] {A B : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) (hBA : B ≤ A) (k : ℕ) :
    E3.mQuot A B < k ↔ Nat.card A < 2 ^ k * Nat.card B := by
  have hp : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa [pow_one] using hA.2 g.1 g.2)⟩
  have h1 := E3.card_eq_two_pow_mul hp hBA
  have hB : 0 < Nat.card B := Nat.card_pos
  rw [h1]
  constructor
  · intro h
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) h) hB
  · intro h
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (Nat.lt_of_mul_lt_mul_right h)

theorem burnsideB46_as_mem_aSet_map_iff [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {Γ : Subgroup ↥(cayleyGroup K)} {k : ℕ} :
    Γ.map (burnsideB46_pi π) ∈ E3.aSet k G ↔
      Γ ≠ ⊥ ∧ (∀ γ ∈ Γ, γ * γ = 1) ∧ (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) ∧
        FixStable (2 ^ k) Γ := by
  have hinj := burnsideB46_pi_injective H
  have hAL : Γ.map (burnsideB46_pi π) ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact burnsideB46_pi_mem_L H x
  have hcomap : (Γ.map (burnsideB46_pi π)).comap (burnsideB46_pi π) = Γ :=
    Subgroup.comap_map_eq_self_of_injective hinj Γ
  constructor
  · rintro ⟨hAG, hAne, hAel, hAfix⟩
    refine ⟨?_, fun γ hγ => hinj ?_, fun γ hγ δ hδ => hinj ?_, ?_⟩
    · intro hΓ
      apply hAne
      rw [hΓ, Subgroup.map_bot]
    · rw [map_mul, map_one, ← sq]
      exact hAel.2 _ ⟨γ, hγ, rfl⟩
    · rw [map_mul, map_mul]
      exact hAel.1 _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    · intro B' hB' hcard w hw γ hγ
      have hBA : B'.map (burnsideB46_pi π) ≤ Γ.map (burnsideB46_pi π) := Subgroup.map_mono hB'
      have hmq : E3.mQuot (Γ.map (burnsideB46_pi π)) (B'.map (burnsideB46_pi π)) < k := by
        rw [burnsideB46_as_mQuot_lt_iff hAel hBA, Subgroup.card_map_of_injective hinj,
          Subgroup.card_map_of_injective hinj]
        exact hcard
      have hfe := hAfix _ hBA hmq
      obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
      have hv : v ∈ fixV (B'.map (burnsideB46_pi π)) := by
        rw [burnsideB46_as_fixV_map H hn]
        exact hw
      rw [hfe, burnsideB46_as_fixV_map H hn] at hv
      exact hv γ hγ
  · rintro ⟨hne, h1, hc, hP⟩
    have hel : IsElemAbelian2 (Γ.map (burnsideB46_pi π)) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
        rw [← map_mul, ← map_mul, hc γ hγ δ hδ]
      · rintro _ ⟨γ, hγ, rfl⟩
        rw [← map_pow, sq, h1 γ hγ, map_one]
    refine ⟨hAL.trans H.le, ?_, hel, ?_⟩
    · intro h
      exact hne ((Subgroup.map_eq_bot_iff_of_injective Γ hinj).mp h)
    · intro B hBA hmq
      have hBL : B ≤ L := hBA.trans hAL
      have hBeq : (B.comap (burnsideB46_pi π)).map (burnsideB46_pi π) = B := by
        refine Subgroup.map_comap_eq_self fun b hb => ?_
        obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 (hBL hb)
        exact ⟨g, hg⟩
      have hB'Γ : B.comap (burnsideB46_pi π) ≤ Γ := by
        intro γ hγ
        obtain ⟨γ', hγ', hγγ'⟩ := hBA (Subgroup.mem_comap.1 hγ)
        rw [← hinj hγγ']
        exact hγ'
      have hcard : Nat.card ↥Γ < 2 ^ k * Nat.card ↥(B.comap (burnsideB46_pi π)) := by
        have h1 := (burnsideB46_as_mQuot_lt_iff hel hBA k).mp hmq
        rw [Subgroup.card_map_of_injective hinj] at h1
        rwa [← Subgroup.card_map_of_injective hinj (f := burnsideB46_pi π)
          (K := B.comap (burnsideB46_pi π)), hBeq]
      have hsub := hP _ hB'Γ hcard
      refine le_antisymm ?_ (fun v hv b hb => hv b (hBA hb))
      intro v hv
      rw [burnsideB46_as_mem_fixV_iff H hn hBL] at hv
      rw [burnsideB46_as_mem_fixV_iff H hn hAL, hcomap]
      exact fun γ hγ => hsub _ hv γ hγ

theorem burnsideB46_as_sigma_sq [CharP K 2] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) {τ : MulAut V} (hτ2 : τ * τ = 1) {c : K}
    {γ : ↥(cayleyGroup K)} {σ : K ≃+* K}
    (hrep : ∀ v, burnsideB46_f θ (τ v) = semiMap c γ σ (burnsideB46_f θ v)) (k : K) :
    σ (σ k) = k := by
  have hTT : ∀ x, semiMap c γ σ (semiMap c γ σ x) = x := by
    intro x
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H x
    rw [← hrep, ← hrep, ← MulAut.mul_apply, hτ2, MulAut.one_apply]
  refine eq_of_semilinear (T := fun x => semiMap c γ σ (semiMap c γ σ x)) (x₀ := eu 0 1)
    (σ := fun k => σ (σ k)) (σ' := fun k => k) ?_ (fun k x => ?_) (fun k x => ?_) k
  · rw [hTT]
    intro h0
    have h1 := congrFun h0 (.inl 0)
    simp at h1
  · rw [semiMap_smul, semiMap_smul]
  · rw [hTT, hTT]

theorem burnsideB46_as_mem_L_of_lin [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {τ : MulAut V} (hτ : τ ∈ G) {c : K}
    {γ : ↥(cayleyGroup K)} {σ : K ≃+* K} (hc : c ≠ 0)
    (hrep : ∀ v, burnsideB46_f θ (τ v) = semiMap c γ σ (burnsideB46_f θ v))
    (hσ : ∀ k, σ k = k) : τ ∈ L := by
  have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => funext fun j => hσ (x j)
  have hform' : ∀ v, burnsideB46_f θ (τ v) = c • g2Act γ (burnsideB46_f θ v) := by
    intro v
    rw [hrep, semiMap_apply, hfrob]
  have hg'G : τ * (burnsideB46_pi π γ)⁻¹ ∈ G :=
    G.mul_mem hτ (G.inv_mem (H.le (burnsideB46_pi_mem_L H γ)))
  have hg'1 : τ * (burnsideB46_pi π γ)⁻¹ = 1 := by
    refine burnsideB46_scalar_eq_one hqs H hn hg'G hc (fun v => ?_)
    rw [MulAut.mul_apply, hform', ← map_inv, burnsideB46_f_act H, g2Act_apply_inv]
  have : τ = burnsideB46_pi π γ := mul_inv_eq_one.1 hg'1
  rw [this]
  exact burnsideB46_pi_mem_L H γ

theorem burnsideB46_as_mul_mem_L [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hA : IsElemAbelian2 A) {a b : MulAut V} (ha : a ∈ A) (hb : b ∈ A) (haL : a ∉ L)
    (hbL : b ∉ L) : a * b ∈ L := by
  obtain ⟨ca, γa, σa, hca, hra⟩ := burnsideB46_G_semilinear hqs H hn (hAG ha)
  obtain ⟨cb, γb, σb, hcb, hrb⟩ := burnsideB46_G_semilinear hqs H hn (hAG hb)
  have hra' : ∀ v, burnsideB46_f θ (a v) = semiMap ca γa σa (burnsideB46_f θ v) := hra
  have hrb' : ∀ v, burnsideB46_f θ (b v) = semiMap cb γb σb (burnsideB46_f θ v) := hrb
  have ha2 := mul_self_of_elemAbelian hA ha
  have hb2 := mul_self_of_elemAbelian hA hb
  have hσa : ∃ k, σa k ≠ k := by
    by_contra hcon
    push Not at hcon
    exact haL (burnsideB46_as_mem_L_of_lin hqs H hn (hAG ha) hca hra' hcon)
  have hσb : ∃ k, σb k ≠ k := by
    by_contra hcon
    push Not at hcon
    exact hbL (burnsideB46_as_mem_L_of_lin hqs H hn (hAG hb) hcb hrb' hcon)
  have hσ : σa = σb := ringEquiv_involution_unique H.card hn
    (burnsideB46_as_sigma_sq H ha2 hra') (burnsideB46_as_sigma_sq H hb2 hrb') hσa hσb
  obtain ⟨c, γ, σ, hc, hr⟩ := burnsideB46_G_semilinear hqs H hn (G.mul_mem (hAG ha) (hAG hb))
  have hr' : ∀ v, burnsideB46_f θ ((a * b) v) = semiMap c γ σ (burnsideB46_f θ v) := hr
  have hTab : ∀ x, semiMap c γ σ x = semiMap ca γa σa (semiMap cb γb σb x) := by
    intro x
    obtain ⟨w, rfl⟩ := burnsideB46_f_surj H x
    rw [← hr', ← hrb', ← hra', MulAut.mul_apply]
  have hlin : ∀ k, σ k = k := by
    intro k
    refine eq_of_semilinear (T := semiMap c γ σ) (x₀ := eu 0 1)
      (σ := fun k => σ k) (σ' := fun k => k) (semiMap_eu_ne_zero hc γ σ)
      (fun k x => semiMap_smul c γ σ k x) (fun k x => ?_) k
    rw [hTab, hTab, semiMap_smul, semiMap_smul, hσ, burnsideB46_as_sigma_sq H hb2 hrb']
  exact burnsideB46_as_mem_L_of_lin hqs H hn (G.mul_mem (hAG ha) (hAG hb)) hc hr' hlin

theorem burnsideB46_as_card_le_two [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hA : IsElemAbelian2 A) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := by
  classical
  by_cases hAL : A ≤ L
  · rw [inf_eq_left.mpr hAL]
    omega
  · obtain ⟨a, ha, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hAL
    let φ : A → Bool × ↥(A ⊓ L) := fun b =>
      if hb : (b : MulAut V) ∈ L then (true, ⟨b, b.2, hb⟩)
      else (false, ⟨a * b, A.mul_mem ha b.2,
        burnsideB46_as_mul_mem_L hqs H hn hAG hA ha b.2 haL hb⟩)
    have hφ : Function.Injective φ := by
      intro b b' h
      by_cases hb : (b : MulAut V) ∈ L <;> by_cases hb' : (b' : MulAut V) ∈ L <;>
        simp only [φ, hb, hb', dite_true, dite_false, Prod.mk.injEq, Bool.true_eq_false,
          Bool.false_eq_true, false_and, true_and] at h
      · exact Subtype.ext (congrArg (fun x : ↥(A ⊓ L) => (x : MulAut V)) h)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun x : ↥(A ⊓ L) => (x : MulAut V)) h))
    have h1 := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

theorem burnsideB46_as_mQuot_inf_lt_two [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hA : IsElemAbelian2 A) : E3.mQuot A (A ⊓ L) < 2 := by
  rw [burnsideB46_as_mQuot_lt_iff hA inf_le_left]
  have h1 := burnsideB46_as_card_le_two hqs H hn hAG hA
  have hpos : 0 < Nat.card ↥(A ⊓ L) := Nat.card_pos
  have h4 : 2 ^ 2 * Nat.card ↥(A ⊓ L) = 4 * Nat.card ↥(A ⊓ L) := by norm_num
  omega

theorem burnsideB46_as_aSet_two_le [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {A : Subgroup (MulAut V)}
    (hA : A ∈ E3.aSet 2 G) : A ≤ L := by
  obtain ⟨hAG, hAne, hAel, hAfix⟩ := hA
  by_contra hAL
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hAL
  have hfix : fixV (A ⊓ L) = fixV A :=
    hAfix (A ⊓ L) inf_le_left (burnsideB46_as_mQuot_inf_lt_two hqs H hn hAG hAel)
  have hΓ1 : ∀ γ ∈ (A ⊓ L).comap (burnsideB46_pi π), γ * γ = 1 := by
    intro γ hγ
    refine burnsideB46_pi_injective H ?_
    rw [map_mul, map_one, ← sq]
    exact hAel.2 _ (Subgroup.mem_comap.1 hγ).1
  obtain ⟨w₀, hw₀, hfix₀⟩ := exists_fix_ne_zero hΓ1
  have hS : fixSub ((A ⊓ L).comap (burnsideB46_pi π)) ≠ ⊥ := by
    intro hbot
    apply hw₀
    have : w₀ ∈ fixSub ((A ⊓ L).comap (burnsideB46_pi π)) := hfix₀
    rw [hbot] at this
    exact (Submodule.mem_bot K).mp this
  refine haL (burnsideB46_mem_L_of_fix hqs H hn (hAG ha) hS fun v hv => ?_)
  have hv' : v ∈ fixV (A ⊓ L) := (burnsideB46_as_mem_fixV_iff H hn inf_le_right v).2 hv
  rw [hfix] at hv'
  rw [mem_fixV.1 hv' a ha]

theorem burnsideB46_as_map_conj [CharP K 2] (Γ : Subgroup ↥(cayleyGroup K))
    (g : ↥(cayleyGroup K)) :
    (Γ.map (burnsideB46_pi π)).map (MulAut.conj (burnsideB46_pi π g)).toMonoidHom =
      (Γ.map (MulAut.conj g).toMonoidHom).map (burnsideB46_pi π) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem burnsideB46_as_map_conj_conj {M : Type*} [Group M] (Γ : Subgroup M) (a b : M) :
    (Γ.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      Γ.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem burnsideB46_as_conj_sq {M : Type*} [Group M] {Γ : Subgroup M}
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) (x : M) :
    ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom, γ * γ = 1 := by
  rintro _ ⟨g, hg, rfl⟩
  change x * g * x⁻¹ * (x * g * x⁻¹) = 1
  rw [show x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ by group, hΓ1 g hg]
  group

theorem burnsideB46_as_conj_comm {M : Type*} [Group M] {Γ : Subgroup M}
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) (x : M) :
    ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom, ∀ δ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      γ * δ = δ * γ := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  change x * g * x⁻¹ * (x * h * x⁻¹) = x * h * x⁻¹ * (x * g * x⁻¹)
  rw [show x * g * x⁻¹ * (x * h * x⁻¹) = x * (g * h) * x⁻¹ by group, hΓc g hg h hh]
  group

theorem burnsideB46_as_aSet_mono {X : Subgroup (MulAut V)} {j k : ℕ} (h : j ≤ k) :
    E3.aSet k X ⊆ E3.aSet j X := by
  rintro A ⟨hAX, hAne, hAel, hAfix⟩
  exact ⟨hAX, hAne, hAel, fun B hB hmq => hAfix B hB (lt_of_lt_of_le hmq h)⟩

theorem burnsideB46_as_fixStable_mono {k k' : ℕ} (h : k ≤ k') {Γ : Subgroup ↥(cayleyGroup K)}
    [CharP K 2] (hP : FixStable k' Γ) : FixStable k Γ :=
  fun B hB hcard => hP B hB (lt_of_lt_of_le hcard (Nat.mul_le_mul_right _ h))

theorem burnsideB46_as_map_comap [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    (A.comap (burnsideB46_pi π)).map (burnsideB46_pi π) = A := by
  refine Subgroup.map_comap_eq_self fun a ha => ?_
  obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hAL ha)
  exact ⟨γ, rfl⟩

theorem burnsideB46_as_exists_of_mem_aSet [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {k : ℕ} (hk : 2 ≤ k) {A : Subgroup (MulAut V)}
    (hA : A ∈ E3.aSet k G) :
    ∃ Γ : Subgroup ↥(cayleyGroup K), A = Γ.map (burnsideB46_pi π) ∧ Γ ≠ ⊥ ∧
      (∀ γ ∈ Γ, γ * γ = 1) ∧ (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) ∧ FixStable (2 ^ k) Γ := by
  have hAL : A ≤ L :=
    burnsideB46_as_aSet_two_le hqs H hn (burnsideB46_as_aSet_mono hk hA)
  have hcomap := burnsideB46_as_map_comap H hAL
  refine ⟨A.comap (burnsideB46_pi π), hcomap.symm, ?_⟩
  exact (burnsideB46_as_mem_aSet_map_iff H hn (k := k)).1 (by rw [hcomap]; exact hA)

theorem burnsideB46_as_pow_two_mul (H : burnsideB46_Hyp V n K G L π θ) :
    2 ^ (2 * n) = Nat.card K ^ 2 := by
  rw [H.card, ← pow_mul, mul_comm]

theorem burnsideB46_as_conj_A1_mem_aSet [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (x : ↥(cayleyGroup K)) :
    ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) ∈ E3.aSet (2 * n) G := by
  rw [burnsideB46_as_mem_aSet_map_iff H hn]
  refine ⟨?_, burnsideB46_as_conj_sq (fun γ hγ => burnsideB46_as_A1_sq hγ) x,
    burnsideB46_as_conj_comm (fun γ hγ δ hδ => burnsideB46_as_A1_comm hγ hδ) x, ?_⟩
  · intro h
    have h1 := (Subgroup.map_eq_bot_iff_of_injective (A1 K) (MulAut.conj x).injective).mp h
    exact burnsideB46_as_A1_ne_bot h1
  · rw [burnsideB46_as_pow_two_mul H]
    exact fixStable_map_conj burnsideB46_as_A1_fixStable x

theorem burnsideB46_as_aSet_succ_empty [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) : E3.aSet (2 * n + 1) G = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun A hA => ?_
  obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
    burnsideB46_as_exists_of_mem_aSet hqs H hn (k := 2 * n + 1) (by omega) hA
  have hF := H.card
  have hle : Nat.card K ^ 2 ≤ 2 ^ (2 * n + 1) := by
    rw [← burnsideB46_as_pow_two_mul H]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP2 : FixStable (Nat.card K ^ 2) Γ := burnsideB46_as_fixStable_mono hle hP
  obtain ⟨x, hx⟩ := eq_conj_A1 hF (by omega) h1 hc hne hP2
  have hP3 : FixStable (2 * Nat.card K ^ 2) Γ := by
    refine burnsideB46_as_fixStable_mono (le_of_eq ?_) hP
    rw [← burnsideB46_as_pow_two_mul H, pow_succ]
    ring
  rw [hx] at hP3
  have h4 := fixStable_map_conj hP3 x⁻¹
  rw [show ((A1 K).map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = A1 K by
    rw [burnsideB46_as_map_conj_conj, inv_mul_cancel]
    ext g
    simp] at h4
  exact burnsideB46_as_A1_not_fixStable h4

theorem burnsideB46_as_aParam [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) : E3.aParam G = 2 * n := by
  have hmem := burnsideB46_as_conj_A1_mem_aSet H hn (1 : ↥(cayleyGroup K))
  have hne : (E3.aSet (2 * n) G).Nonempty := ⟨_, hmem⟩
  have hev : Even (Nat.card G) := by
    obtain ⟨hAG, hAne, hAel, -⟩ := hmem
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
    have ha2 : (⟨a, hAG haA⟩ : ↥G) ^ 2 = 1 := Subtype.ext (hAel.2 a haA)
    have ha1' : (⟨a, hAG haA⟩ : ↥G) ≠ 1 := by
      intro h
      apply ha1
      have h' : a = 1 := congrArg (fun x : ↥G => (x : MulAut V)) h
      exact Subtype.ext h'
    have h2 := orderOf_eq_prime ha2 ha1'
    have h3 : 2 ∣ Nat.card G := h2 ▸ orderOf_dvd_natCard _
    exact even_iff_two_dvd.mpr h3
  have hempty := burnsideB46_as_aSet_succ_empty hqs H hn
  rw [E3.aParam, if_pos hev]
  refine IsGreatest.csSup_eq ⟨⟨by omega, hne⟩, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ := hk.2
  have hA' := burnsideB46_as_aSet_mono (X := G) (j := 2 * n + 1) (k := k) (by omega) hA
  rw [hempty] at hA'
  exact hA'

theorem burnsideB46_as_map_conj_one {M : Type*} [Group M] (P : Subgroup M) :
    P.map (MulAut.conj (1 : M)).toMonoidHom = P := by
  ext g
  simp

theorem burnsideB46_as_aSet_two_n [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (γ₀ : ↥(cayleyGroup K)) :
    E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = (((A1 K).map (MulAut.conj γ₀).toMonoidHom).map
      (burnsideB46_pi π)).map (MulAut.conj l).toMonoidHom} := by
  ext A
  constructor
  · intro hA
    obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
      burnsideB46_as_exists_of_mem_aSet hqs H hn (k := 2 * n) (by omega) hA
    have hP' : FixStable (Nat.card K ^ 2) Γ := by
      rw [← burnsideB46_as_pow_two_mul H]
      exact hP
    obtain ⟨x, hx⟩ := eq_conj_A1 H.card (by omega) h1 hc hne hP'
    refine ⟨burnsideB46_pi π (x * γ₀⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
    rw [burnsideB46_as_map_conj, burnsideB46_as_map_conj_conj, hx, inv_mul_cancel_right]
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨g, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    rw [burnsideB46_as_map_conj, burnsideB46_as_map_conj_conj]
    exact burnsideB46_as_conj_A1_mem_aSet H hn (g * γ₀)

theorem burnsideB46_as_aSet_succ_fused [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (γ₀ : ↥(cayleyGroup K)) :
    ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤
      ((A1 K).map (MulAut.conj γ₀).toMonoidHom).map (burnsideB46_pi π) := by
  intro A hA
  obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
    burnsideB46_as_exists_of_mem_aSet hqs H hn (k := n + 1) (by omega) hA
  have hk1 : Nat.card K < 2 ^ (n + 1) := by
    rw [H.card, pow_succ]
    have : 0 < 2 ^ n := by positivity
    omega
  obtain ⟨x, hxle, -⟩ := burnsideB46_as_exists_conj_le_A1 H.card (by omega) hk1 h1 hc hne hP
  refine ⟨burnsideB46_pi π (γ₀ * x⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
  rw [burnsideB46_as_map_conj, ← burnsideB46_as_map_conj_conj Γ x⁻¹ γ₀]
  exact Subgroup.map_mono (Subgroup.map_mono hxle)

theorem burnsideB46_as_le_A1 [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {R : Subgroup ↥(cayleyGroup K)}
    {g : ↥(cayleyGroup K)} (hR : R = (pCoreOf 2 (stabV0 K)).map (MulAut.conj g).toMonoidHom)
    {A : Subgroup (MulAut V)} (hA : A ∈ E3.aSet (2 * n - 1) G)
    (hAR : A ≤ R.map (burnsideB46_pi π)) :
    A ≤ ((A1 K).map (MulAut.conj g).toMonoidHom).map (burnsideB46_pi π) := by
  obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
    burnsideB46_as_exists_of_mem_aSet hqs H hn (k := 2 * n - 1) (by omega) hA
  have hΓR : Γ ≤ R := by
    intro γ hγ
    obtain ⟨r, hr, hrγ⟩ := hAR ⟨γ, hγ, rfl⟩
    rw [← burnsideB46_pi_injective H hrγ]
    exact hr
  have hΓ'R : Γ.map (MulAut.conj g⁻¹).toMonoidHom ≤ pCoreOf 2 (stabV0 K) := by
    refine (Subgroup.map_mono (hΓR.trans hR.le)).trans (le_of_eq ?_)
    rw [burnsideB46_as_map_conj_conj, inv_mul_cancel, burnsideB46_as_map_conj_one]
  have hk : Nat.card K < 2 ^ (2 * n - 1) := by
    rw [H.card]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hle := burnsideB46_as_le_A1_of_le_R1 hk hΓ'R (burnsideB46_as_conj_sq h1 g⁻¹)
    (burnsideB46_as_conj_comm hc g⁻¹) (fixStable_map_conj hP g⁻¹)
  refine Subgroup.map_mono ?_
  calc Γ = (Γ.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
        (map_map_conj_inv Γ g).symm
    _ ≤ (A1 K).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hle

theorem burnsideB46_as_part_9_of [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    (hF3 : ∀ x : Ix3 → K, x ≠ 0 → burnsideB46_F3 K x ≠ ⊥)
    (hA1 : ∀ x : Ix3 → K, x ≠ 0 → ∃ γ : ↥(cayleyGroup K),
      burnsideB46_A1 K x = (A1 K).map (MulAut.conj γ).toMonoidHom) :
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
        (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) := by
  refine ⟨burnsideB46_as_aParam hqs H hn, fun A hA => burnsideB46_as_aSet_two_le hqs H hn hA, ?_⟩
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg
  obtain ⟨x, hx0, -, -, -, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  obtain ⟨-, -, -, -, -, hAcl⟩ := hcfg
  have hA₁ := burnsideB46_cfg1_A1 hqs H hn (hF3 x hx0) hV₃ hAcl
  obtain ⟨γ₀, hγ₀⟩ := hA1 x hx0
  rw [hA₁, hγ₀]
  exact ⟨burnsideB46_as_aSet_two_n hqs H hn γ₀, burnsideB46_as_aSet_succ_fused hqs H hn γ₀⟩

theorem burnsideB46_as_part_12_of [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    (hF3 : ∀ x : Ix3 → K, x ≠ 0 → burnsideB46_F3 K x ≠ ⊥)
    (hstd : ∀ x : Ix3 → K, x ≠ 0 → ∃ g : ↥(cayleyGroup K),
      burnsideB46_R1 K x = (pCoreOf 2 (stabV0 K)).map (MulAut.conj g).toMonoidHom ∧
      burnsideB46_A1 K x = (A1 K).map (MulAut.conj g).toMonoidHom) :
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)), B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) := by
  intro _ V₁ P₁ R₁ Z₁ V₃ A₁ hcfg A hA hAR
  obtain ⟨x, hx0, -, -, hR₁, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  obtain ⟨-, -, -, -, -, hAcl⟩ := hcfg
  have hA₁ := burnsideB46_cfg1_A1 hqs H hn (hF3 x hx0) hV₃ hAcl
  obtain ⟨g, hgR, hgA⟩ := hstd x hx0
  rw [hA₁, hgA]
  rw [hR₁] at hAR
  exact burnsideB46_as_le_A1 hqs H hn hgR hA hAR

end ASV

section ASb

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_as_F3_ne_bot [CharP K 2] {x : Ix3 → K} (hx : x ≠ 0) :
    burnsideB46_F3 K x ≠ ⊥ := by
  intro h
  have h3 := burnsideB46_p3_F3_card hx
  rw [h, finrank_bot] at h3
  omega

theorem burnsideB46_as_std [CharP K 2] {x : Ix3 → K} (hx : x ≠ 0) :
    ∃ g : ↥(cayleyGroup K),
      burnsideB46_R1 K x = (pCoreOf 2 (stabV0 K)).map (MulAut.conj g).toMonoidHom ∧
      burnsideB46_A1 K x = (A1 K).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨γ, hγ⟩ := exists_g2Act_eu_eq hx
  refine ⟨γ, ?_, ?_⟩
  · rw [← hγ, burnsideB46_p3_R1_act, burnsideB46_p3_R1_eu]
  · rw [← hγ, burnsideB46_p3_A1_act]
    congr 1
    ext g
    change (∀ w ∈ burnsideB46_F3 K (eu 0 (1 : K)), g2Act g w = w) ↔ _
    rw [burnsideB46_p3_F3_eu]
    exact Iff.rfl

theorem burnsideB46_as_part_9 (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
        (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_as_part_9_of hqs H hn (fun x hx => burnsideB46_as_F3_ne_bot hx)
    (fun x hx => (burnsideB46_as_std hx).imp fun _ h => h.2)

theorem burnsideB46_as_part_12 (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)), B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_as_part_12_of hqs H hn (fun x hx => burnsideB46_as_F3_ne_bot hx)
    (fun x hx => burnsideB46_as_std hx)

end ASb

section OFn

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_of_card_V [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ) :
    Nat.card V = Nat.card (fixV L) * Nat.card K ^ 6 := by
  have h1 := burnsideB46_of_card_pre_set H (fun _ => True)
  have e1 : Nat.card {v : V // True} = Nat.card V :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  have e2 : Nat.card {x : Ix3 → K // True} = Nat.card (Ix3 → K) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [e1, e2, CFSG.Quasithin.Vol2.Ch11.G2Q8.card_Q] at h1
  exact h1

theorem burnsideB46_of_card_fixV_le [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (A : Subgroup (MulAut V)) :
    Nat.card (fixV A) ≤
      Nat.card (fixV L) * Nat.card (fixSub (A.comap (burnsideB46_pi π))) := by
  have h1 := burnsideB46_of_card_pre_set H (fun x => x ∈ fixSub (A.comap (burnsideB46_pi π)))
  refine le_of_le_of_eq (Nat.card_le_card_of_injective
    (fun v : fixV A => (⟨v.1, ?_⟩ :
      {v : V // burnsideB46_f θ v ∈ fixSub (A.comap (burnsideB46_pi π))}))
    (fun v w h => Subtype.ext (Subtype.mk.inj h))) h1
  rw [mem_fixSub]
  intro γ hγ
  rw [← burnsideB46_f_act H γ v.1, mem_fixV.1 v.2 _ (Subgroup.mem_comap.1 hγ)]

theorem burnsideB46_of_mem_fixV_iff_lift [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (v : V) :
    v ∈ fixV A ↔ burnsideB46_f θ v ∈ fixSub (A.comap (burnsideB46_pi π)) := by
  rw [mem_fixSub]
  constructor
  · intro hv γ hγ
    rw [← burnsideB46_f_act H γ v, mem_fixV.1 hv _ (Subgroup.mem_comap.1 hγ)]
  · intro hv a ha
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hAL ha)
    refine hlift (burnsideB46_pi_mem_L H γ) ?_
    refine (burnsideB46_f_eq_zero_iff H _).1 ?_
    rw [burnsideB46_f_sub, burnsideB46_f_act H, hv γ (Subgroup.mem_comap.2 ha), sub_self]

theorem burnsideB46_of_card_fixV_lift [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) :
    Nat.card (fixV A) =
      Nat.card (fixV L) * Nat.card (fixSub (A.comap (burnsideB46_pi π))) := by
  rw [Nat.card_congr
    (Equiv.subtypeEquivRight fun v => burnsideB46_of_mem_fixV_iff_lift H hlift hAL v)]
  exact burnsideB46_of_card_pre_set H (fun x => x ∈ fixSub (A.comap (burnsideB46_pi π)))

theorem burnsideB46_of_offender_conj_of_le [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ x : ↥(cayleyGroup K),
      A = ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) := by
  obtain ⟨hΓ1, hΓc⟩ := burnsideB46_of_comap_elem H hAe
  have hΓne : A.comap (burnsideB46_pi π) ≠ ⊥ := by
    intro h
    apply hAne
    rw [← burnsideB46_of_map_comap H hAL, h, Subgroup.map_bot]
  have hcard := burnsideB46_of_card_comap H hAL
  have hle := burnsideB46_of_card_fixV_le H A
  have hV := burnsideB46_of_card_V H
  have hpos : 0 < Nat.card (fixV L) := Nat.card_pos
  have hoff : Nat.card K ^ 6 ≤
      Nat.card (A.comap (burnsideB46_pi π)) * Nat.card (fixSub (A.comap (burnsideB46_pi π))) := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card (fixV L) * Nat.card K ^ 6 = Nat.card V := hV.symm
      _ ≤ Nat.card A * Nat.card (fixV A) := hff
      _ ≤ Nat.card A * (Nat.card (fixV L) *
            Nat.card (fixSub (A.comap (burnsideB46_pi π)))) := Nat.mul_le_mul_left _ hle
      _ = Nat.card (fixV L) * (Nat.card (A.comap (burnsideB46_pi π)) *
            Nat.card (fixSub (A.comap (burnsideB46_pi π)))) := by rw [hcard]; ring
  obtain ⟨x, hx⟩ := CFSG.Quasithin.MS93.eq_conj_A1_of_offender H.card H.one_le hΓ1 hΓc hΓne hoff
  exact ⟨x, by rw [← hx]; exact (burnsideB46_of_map_comap H hAL).symm⟩

theorem burnsideB46_of_conj_isOffender_lift [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (x : ↥(cayleyGroup K)) :
    IsFFStarOffender G (((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)) := by
  obtain ⟨hA1sq, hA1c⟩ := burnsideB46_of_A1_elem (K := K)
  obtain ⟨hΓ1, hΓc⟩ := burnsideB46_of_conj_elem hA1sq hA1c x
  have hAL : ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) ≤ L := by
    rintro _ ⟨γ, -, rfl⟩
    exact burnsideB46_pi_mem_L H γ
  have hΓcard : Nat.card ↥((A1 K).map (MulAut.conj x).toMonoidHom) = Nat.card K ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact card_A1
  have hAcard : Nat.card ↥(((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)) =
      Nat.card K ^ 3 := by
    rw [Subgroup.card_map_of_injective (burnsideB46_pi_injective H), hΓcard]
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hAne : ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)) = 1 := by
      rw [h]
      exact Subgroup.card_bot
    have h2 : 1 < Nat.card K ^ 3 := Nat.one_lt_pow (by norm_num) hq
    omega
  have hAe := burnsideB46_of_map_elem hΓ1 hΓc (burnsideB46_pi π)
  refine ⟨hAL.trans H.le, hAne, hAe, fun B hBA => ?_⟩
  have hBL : B ≤ L := hBA.trans hAL
  have hBe : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  obtain ⟨hB1, hBc⟩ := burnsideB46_of_comap_elem H hBe
  have h1 := (card_mul_card_fixSub H.card H.one_le hB1 hBc).1
  have hBc1 := burnsideB46_of_card_comap H hBL
  have hBc2 := burnsideB46_of_card_fixV_le H B
  have hcomapA : (((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)).comap
      (burnsideB46_pi π) = (A1 K).map (MulAut.conj x).toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (burnsideB46_pi_injective H) _
  have hAc2 := burnsideB46_of_card_fixV_lift H hlift hAL
  rw [hcomapA] at hAc2
  have hge := burnsideB46_of_card_fixSub_conj (K := K) x
  rw [hAcard, hAc2]
  calc Nat.card B * Nat.card (fixV B)
      ≤ Nat.card B * (Nat.card (fixV L) * Nat.card (fixSub (B.comap (burnsideB46_pi π)))) :=
        Nat.mul_le_mul_left _ hBc2
    _ = Nat.card (fixV L) * (Nat.card (B.comap (burnsideB46_pi π)) *
          Nat.card (fixSub (B.comap (burnsideB46_pi π)))) := by rw [← hBc1]; ring
    _ ≤ Nat.card (fixV L) * Nat.card K ^ 6 := Nat.mul_le_mul_left _ h1
    _ = Nat.card K ^ 3 * (Nat.card (fixV L) * Nat.card K ^ 3) := by ring
    _ ≤ Nat.card K ^ 3 * (Nat.card (fixV L) *
          Nat.card (fixSub ((A1 K).map (MulAut.conj x).toMonoidHom))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hge)

theorem burnsideB46_of_ffstar_eq [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (hconj : ∀ A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∃ x : ↥(cayleyGroup K),
        A = ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π))
    (hoff : ∀ x : ↥(cayleyGroup K),
      IsFFStarOffender G (((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π)))
    {A₁ : Subgroup (MulAut V)} {γ : ↥(cayleyGroup K)}
    (hA₁ : A₁ = ((A1 K).map (MulAut.conj γ).toMonoidHom).map (burnsideB46_pi π)) :
    {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
  ext A
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hA
    obtain ⟨x', hx'⟩ := hconj A hA
    refine ⟨burnsideB46_pi π (x' * γ⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
    rw [hA₁, burnsideB46_of_map_conj, burnsideB46_of_map_map_conj, inv_mul_cancel_right]
    exact hx'
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨y, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    rw [hA₁, burnsideB46_of_map_conj, burnsideB46_of_map_map_conj]
    exact hoff _

theorem burnsideB46_of_cfg1_A1_of_le [CharP K 2] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hGL : G ≤ L) {x : Ix3 → K} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hV₃ : V₃ = burnsideB46_pre θ (burnsideB46_F3 K x))
    (hA : ∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) :
    A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) := by
  have key : ∀ (g : MulAut V), (∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K x → burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    intro g
    rw [hV₃]
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  ext g
  rw [hA]
  constructor
  · rintro ⟨hgG, hg⟩
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hGL hgG)
    refine ⟨γ, fun w hw => ?_, rfl⟩
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
    rw [← burnsideB46_f_act H]
    exact (key _).1 hg v hw
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨H.le (burnsideB46_pi_mem_L H γ), (key _).2 fun v hv => ?_⟩
    rw [burnsideB46_f_act H]
    exact hγ _ hv

theorem burnsideB46_part_13a_one
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg
  obtain ⟨x, hx0, -, -, -, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  have hA₁ := burnsideB46_of_cfg1_A1_of_le H hGL.le hV₃ hcfg.2.2.2.2.2
  obtain ⟨γ, -, hγ⟩ := burnsideB46_as_std hx0
  have hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v :=
    fun hl _ h => burnsideB46_n1_lift_fix H hn1 hl h
  refine burnsideB46_of_ffstar_eq H ?_ (burnsideB46_of_conj_isOffender_lift H hlift)
    (γ := γ) (by rw [hA₁, hγ])
  intro A hA
  obtain ⟨hAG, hAne, hAe, hB⟩ := hA
  have hff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have h := hB ⊥ bot_le
    rwa [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top] at h
  exact burnsideB46_of_offender_conj_of_le H (hAG.trans hGL.le) hAe hAne hff

end OFn

section ASn

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_as_g_mem_fixV_iff [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (v : V) :
    v ∈ fixV A ↔ burnsideB46_f θ v ∈ fixSub (A.comap (burnsideB46_pi π)) := by
  rw [mem_fixSub]
  constructor
  · intro hv γ hγ
    rw [← burnsideB46_f_act H γ v, mem_fixV.1 hv _ (Subgroup.mem_comap.1 hγ)]
  · intro hv a ha
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hAL ha)
    refine hlift (burnsideB46_pi_mem_L H γ) ?_
    refine (burnsideB46_f_eq_zero_iff H _).1 ?_
    rw [burnsideB46_f_sub, burnsideB46_f_act H, hv γ (Subgroup.mem_comap.2 ha), sub_self]

theorem burnsideB46_as_g_fixV_map [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (X : Subgroup ↥(cayleyGroup K)) :
    fixV (X.map (burnsideB46_pi π)) = burnsideB46_pre θ (fixSub X) := by
  have hle : X.map (burnsideB46_pi π) ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact burnsideB46_pi_mem_L H x
  ext v
  rw [burnsideB46_as_g_mem_fixV_iff H hlift hle, burnsideB46_mem_pre,
    Subgroup.comap_map_eq_self_of_injective (burnsideB46_pi_injective H)]

theorem burnsideB46_as_g_mem_aSet_map_iff [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    {Γ : Subgroup ↥(cayleyGroup K)} {k : ℕ} :
    Γ.map (burnsideB46_pi π) ∈ E3.aSet k G ↔
      Γ ≠ ⊥ ∧ (∀ γ ∈ Γ, γ * γ = 1) ∧ (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) ∧
        FixStable (2 ^ k) Γ := by
  have hinj := burnsideB46_pi_injective H
  have hAL : Γ.map (burnsideB46_pi π) ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact burnsideB46_pi_mem_L H x
  have hcomap : (Γ.map (burnsideB46_pi π)).comap (burnsideB46_pi π) = Γ :=
    Subgroup.comap_map_eq_self_of_injective hinj Γ
  constructor
  · rintro ⟨hAG, hAne, hAel, hAfix⟩
    refine ⟨?_, fun γ hγ => hinj ?_, fun γ hγ δ hδ => hinj ?_, ?_⟩
    · intro hΓ
      apply hAne
      rw [hΓ, Subgroup.map_bot]
    · rw [map_mul, map_one, ← sq]
      exact hAel.2 _ ⟨γ, hγ, rfl⟩
    · rw [map_mul, map_mul]
      exact hAel.1 _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    · intro B' hB' hcard w hw γ hγ
      have hBA : B'.map (burnsideB46_pi π) ≤ Γ.map (burnsideB46_pi π) := Subgroup.map_mono hB'
      have hmq : E3.mQuot (Γ.map (burnsideB46_pi π)) (B'.map (burnsideB46_pi π)) < k := by
        rw [burnsideB46_as_mQuot_lt_iff hAel hBA, Subgroup.card_map_of_injective hinj,
          Subgroup.card_map_of_injective hinj]
        exact hcard
      have hfe := hAfix _ hBA hmq
      obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
      have hv : v ∈ fixV (B'.map (burnsideB46_pi π)) := by
        rw [burnsideB46_as_g_fixV_map H hlift]
        exact hw
      rw [hfe, burnsideB46_as_g_fixV_map H hlift] at hv
      exact hv γ hγ
  · rintro ⟨hne, h1, hc, hP⟩
    have hel : IsElemAbelian2 (Γ.map (burnsideB46_pi π)) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
        rw [← map_mul, ← map_mul, hc γ hγ δ hδ]
      · rintro _ ⟨γ, hγ, rfl⟩
        rw [← map_pow, sq, h1 γ hγ, map_one]
    refine ⟨hAL.trans H.le, ?_, hel, ?_⟩
    · intro h
      exact hne ((Subgroup.map_eq_bot_iff_of_injective Γ hinj).mp h)
    · intro B hBA hmq
      have hBL : B ≤ L := hBA.trans hAL
      have hBeq : (B.comap (burnsideB46_pi π)).map (burnsideB46_pi π) = B := by
        refine Subgroup.map_comap_eq_self fun b hb => ?_
        obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 (hBL hb)
        exact ⟨g, hg⟩
      have hB'Γ : B.comap (burnsideB46_pi π) ≤ Γ := by
        intro γ hγ
        obtain ⟨γ', hγ', hγγ'⟩ := hBA (Subgroup.mem_comap.1 hγ)
        rw [← hinj hγγ']
        exact hγ'
      have hcard : Nat.card ↥Γ < 2 ^ k * Nat.card ↥(B.comap (burnsideB46_pi π)) := by
        have h1 := (burnsideB46_as_mQuot_lt_iff hel hBA k).mp hmq
        rw [Subgroup.card_map_of_injective hinj] at h1
        rwa [← Subgroup.card_map_of_injective hinj (f := burnsideB46_pi π)
          (K := B.comap (burnsideB46_pi π)), hBeq]
      have hsub := hP _ hB'Γ hcard
      refine le_antisymm ?_ (fun v hv b hb => hv b (hBA hb))
      intro v hv
      rw [burnsideB46_as_g_mem_fixV_iff H hlift hBL] at hv
      rw [burnsideB46_as_g_mem_fixV_iff H hlift hAL, hcomap]
      exact fun γ hγ => hsub _ hv γ hγ

theorem burnsideB46_as_g_exists_of_mem_aSet [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (hGL : G ≤ L) {k : ℕ} {A : Subgroup (MulAut V)} (hA : A ∈ E3.aSet k G) :
    ∃ Γ : Subgroup ↥(cayleyGroup K), A = Γ.map (burnsideB46_pi π) ∧ Γ ≠ ⊥ ∧
      (∀ γ ∈ Γ, γ * γ = 1) ∧ (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) ∧ FixStable (2 ^ k) Γ := by
  have hAL : A ≤ L := hA.1.trans hGL
  have hcomap := burnsideB46_as_map_comap H hAL
  refine ⟨A.comap (burnsideB46_pi π), hcomap.symm, ?_⟩
  exact (burnsideB46_as_g_mem_aSet_map_iff H hlift (k := k)).1 (by rw [hcomap]; exact hA)

theorem burnsideB46_as_g_conj_A1_mem_aSet [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (x : ↥(cayleyGroup K)) :
    ((A1 K).map (MulAut.conj x).toMonoidHom).map (burnsideB46_pi π) ∈ E3.aSet (2 * n) G := by
  rw [burnsideB46_as_g_mem_aSet_map_iff H hlift]
  refine ⟨?_, burnsideB46_as_conj_sq (fun γ hγ => burnsideB46_as_A1_sq hγ) x,
    burnsideB46_as_conj_comm (fun γ hγ δ hδ => burnsideB46_as_A1_comm hγ hδ) x, ?_⟩
  · intro h
    have h1 := (Subgroup.map_eq_bot_iff_of_injective (A1 K) (MulAut.conj x).injective).mp h
    exact burnsideB46_as_A1_ne_bot h1
  · rw [burnsideB46_as_pow_two_mul H]
    exact fixStable_map_conj burnsideB46_as_A1_fixStable x

theorem burnsideB46_as_g_aSet_succ_empty [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (hGL : G ≤ L) : E3.aSet (2 * n + 1) G = ∅ := by
  have hn := H.one_le
  refine Set.eq_empty_iff_forall_notMem.mpr fun A hA => ?_
  obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
    burnsideB46_as_g_exists_of_mem_aSet H hlift hGL (k := 2 * n + 1) hA
  have hF := H.card
  have hle : Nat.card K ^ 2 ≤ 2 ^ (2 * n + 1) := by
    rw [← burnsideB46_as_pow_two_mul H]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP2 : FixStable (Nat.card K ^ 2) Γ := burnsideB46_as_fixStable_mono hle hP
  obtain ⟨x, hx⟩ := eq_conj_A1 hF hn h1 hc hne hP2
  have hP3 : FixStable (2 * Nat.card K ^ 2) Γ := by
    refine burnsideB46_as_fixStable_mono (le_of_eq ?_) hP
    rw [← burnsideB46_as_pow_two_mul H, pow_succ]
    ring
  rw [hx] at hP3
  have h4 := fixStable_map_conj hP3 x⁻¹
  rw [show ((A1 K).map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = A1 K by
    rw [burnsideB46_as_map_conj_conj, inv_mul_cancel]
    ext g
    simp] at h4
  exact burnsideB46_as_A1_not_fixStable h4

theorem burnsideB46_as_g_aParam [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (hGL : G ≤ L) : E3.aParam G = 2 * n := by
  have hn := H.one_le
  have hmem := burnsideB46_as_g_conj_A1_mem_aSet H hlift (1 : ↥(cayleyGroup K))
  have hne : (E3.aSet (2 * n) G).Nonempty := ⟨_, hmem⟩
  have hev : Even (Nat.card G) := by
    obtain ⟨hAG, hAne, hAel, -⟩ := hmem
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
    have ha2 : (⟨a, hAG haA⟩ : ↥G) ^ 2 = 1 := Subtype.ext (hAel.2 a haA)
    have ha1' : (⟨a, hAG haA⟩ : ↥G) ≠ 1 := by
      intro h
      apply ha1
      have h' : a = 1 := congrArg (fun x : ↥G => (x : MulAut V)) h
      exact Subtype.ext h'
    have h2 := orderOf_eq_prime ha2 ha1'
    have h3 : 2 ∣ Nat.card G := h2 ▸ orderOf_dvd_natCard _
    exact even_iff_two_dvd.mpr h3
  have hempty := burnsideB46_as_g_aSet_succ_empty H hlift hGL
  rw [E3.aParam, if_pos hev]
  refine IsGreatest.csSup_eq ⟨⟨by omega, hne⟩, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ := hk.2
  have hA' := burnsideB46_as_aSet_mono (X := G) (j := 2 * n + 1) (k := k) (by omega) hA
  rw [hempty] at hA'
  exact hA'

theorem burnsideB46_as_g_aSet_two_n [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (hGL : G ≤ L) (γ₀ : ↥(cayleyGroup K)) :
    E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = (((A1 K).map (MulAut.conj γ₀).toMonoidHom).map
      (burnsideB46_pi π)).map (MulAut.conj l).toMonoidHom} := by
  have hn := H.one_le
  ext A
  constructor
  · intro hA
    obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
      burnsideB46_as_g_exists_of_mem_aSet H hlift hGL (k := 2 * n) hA
    have hP' : FixStable (Nat.card K ^ 2) Γ := by
      rw [← burnsideB46_as_pow_two_mul H]
      exact hP
    obtain ⟨x, hx⟩ := eq_conj_A1 H.card hn h1 hc hne hP'
    refine ⟨burnsideB46_pi π (x * γ₀⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
    rw [burnsideB46_as_map_conj, burnsideB46_as_map_conj_conj, hx, inv_mul_cancel_right]
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨g, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    rw [burnsideB46_as_map_conj, burnsideB46_as_map_conj_conj]
    exact burnsideB46_as_g_conj_A1_mem_aSet H hlift (g * γ₀)

theorem burnsideB46_as_g_aSet_succ_fused [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v)
    (hGL : G ≤ L) (γ₀ : ↥(cayleyGroup K)) :
    ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤
      ((A1 K).map (MulAut.conj γ₀).toMonoidHom).map (burnsideB46_pi π) := by
  have hn := H.one_le
  intro A hA
  obtain ⟨Γ, rfl, hne, h1, hc, hP⟩ :=
    burnsideB46_as_g_exists_of_mem_aSet H hlift hGL (k := n + 1) hA
  have hk1 : Nat.card K < 2 ^ (n + 1) := by
    rw [H.card, pow_succ]
    have : 0 < 2 ^ n := by positivity
    omega
  obtain ⟨x, hxle, -⟩ := burnsideB46_as_exists_conj_le_A1 H.card hn hk1 h1 hc hne hP
  refine ⟨burnsideB46_pi π (γ₀ * x⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
  rw [burnsideB46_as_map_conj, ← burnsideB46_as_map_conj_conj Γ x⁻¹ γ₀]
  exact Subgroup.map_mono (Subgroup.map_mono hxle)

theorem burnsideB46_as_n1_cfg1_A1 [CharP K 2] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hGL : G ≤ L) {x : Ix3 → K} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hV₃ : V₃ = burnsideB46_pre θ (burnsideB46_F3 K x))
    (hA : ∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) :
    A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) := by
  have key : ∀ (g : MulAut V), (∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K x → burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    intro g
    rw [hV₃]
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  ext g
  rw [hA]
  constructor
  · rintro ⟨hgG, hg⟩
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 (hGL hgG)
    refine ⟨γ, fun w hw => ?_, rfl⟩
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
    rw [← burnsideB46_f_act H]
    exact (key _).1 hg v hw
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨H.le (burnsideB46_pi_mem_L H γ), (key _).2 fun v hv => ?_⟩
    rw [burnsideB46_f_act H]
    exact hγ _ hv

theorem burnsideB46_as_part_9_one
    [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
        (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have hlift : ∀ {l : MulAut V}, l ∈ L → ∀ {v : V}, l v * v⁻¹ ∈ fixV L → l v = v :=
    fun hl _ h => burnsideB46_n1_lift_fix H hn1 hl h
  refine ⟨burnsideB46_as_g_aParam H hlift hGL.le, fun A hA => hA.1.trans hGL.le, ?_⟩
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg
  obtain ⟨x, hx0, -, -, -, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  obtain ⟨-, -, -, -, -, hAcl⟩ := hcfg
  have hA₁ := burnsideB46_as_n1_cfg1_A1 H hGL.le hV₃ hAcl
  obtain ⟨γ₀, -, hγ₀⟩ := burnsideB46_as_std hx0
  rw [hA₁, hγ₀]
  exact ⟨burnsideB46_as_g_aSet_two_n H hlift hGL.le γ₀,
    burnsideB46_as_g_aSet_succ_fused H hlift hGL.le γ₀⟩

end ASn

section P4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

open scoped commutatorElement
open CFSG.QuasithinUnique.Bridge.Alt57Model (stabElt stabElt_injective S0)


variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p4_smul (g : ↥(cayleyGroup K)) (c : K) (w : Ix3 → K) :
    g2Act g (c • w) = c • g2Act g w := JonesParshall.g2Act_smul g c w

theorem burnsideB46_p4_mul_apply (g h : ↥(cayleyGroup K)) (w : Ix3 → K) :
    g2Act (g * h) w = g2Act g (g2Act h w) := by
  rw [map_mul]
  rfl

@[expose] def burnsideB46_p4_Z0 (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) where
  carrier := {g | ∃ s : K, g = tL s}
  one_mem' := ⟨0, (tL_zero (K := K)).symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, tL_mul s t⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨s, inv_eq_of_mul_eq_one_right (tL_mul_self s)⟩

theorem burnsideB46_p4_mem_Z0 {g : ↥(cayleyGroup K)} :
    g ∈ burnsideB46_p4_Z0 K ↔ ∃ s : K, g = tL s := Iff.rfl

theorem burnsideB46_p4_tL_inj {s t : K} (h : tL s = tL t) : s = t := by
  have h1 := congrArg (fun g : ↥(cayleyGroup K) => g2Act g (q6 0 0 1 0 0 0) (.inl 0)) h
  simp only [g2Act_tL] at h1
  simpa [q6] using h1

theorem burnsideB46_p4_card_Z0 : Nat.card ↥(burnsideB46_p4_Z0 K) = Nat.card K := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun s : K => (⟨tL s, ⟨s, rfl⟩⟩ : ↥(burnsideB46_p4_Z0 K))) ⟨?_, ?_⟩)
  · intro s t h
    exact burnsideB46_p4_tL_inj (congrArg Subtype.val h)
  · rintro ⟨_, s, rfl⟩
    exact ⟨s, rfl⟩

theorem burnsideB46_p4_tL_mem_U0 (s : K) : tL s ∈ U0 K := by
  have h : tL s = g2A (uSL 0 s 0) := by
    unfold tL
    congr 1
    apply Subtype.ext
    rw [tv02_lit]
    rfl
  rw [h]
  exact g2A_mem_U0 0 s 0

theorem burnsideB46_p4_U0_le_stabQ_two : U0 K ≤ stabQ (stdF K 2) := by
  intro g hg
  rw [mem_stabQ]
  intro w
  exact ((stdF_stable (F := K) 2).mem_iff hg w).symm

theorem burnsideB46_p4_q6_exists (w : Ix3 → K) : ∃ a b c d e f : K, w = q6 a b c d e f :=
  ⟨_, _, _, _, _, _, q6_eta w⟩

theorem burnsideB46_p4_inC_q6 {a b c d e f : K} :
    InC (q6 a b c d e f) ↔ c = 0 ∧ d = 0 := Iff.rfl

theorem burnsideB46_p4_F2_q6 {a b c d e f : K} :
    q6 a b c d e f ∈ stdF K 2 ↔ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  rw [mem_stdF_two]
  exact Iff.rfl

theorem burnsideB46_p4_F2_of {a f : K} : q6 a 0 0 0 0 f ∈ stdF K 2 :=
  burnsideB46_p4_F2_q6.2 ⟨rfl, rfl, rfl, rfl⟩

theorem burnsideB46_p4_q6_sub_self {a b c d e f a' b' c' d' e' f' : K} :
    q6 a b c d e f - q6 a' b' c' d' e' f' = q6 (a - a') (b - b') (c - c') (d - d') (e - e') (f - f') :=
  q6_sub _ _ _ _ _ _ _ _ _ _ _ _

@[expose] def burnsideB46_p4_R2 (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) where
  carrier := {g | g2Act g (q6 1 0 0 0 0 0) = q6 1 0 0 0 0 0 ∧
    g2Act g (q6 0 0 0 0 0 1) = q6 0 0 0 0 0 1}
  one_mem' := ⟨by rw [map_one]; rfl, by rw [map_one]; rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [burnsideB46_p4_mul_apply, hb.1, ha.1],
    by rw [burnsideB46_p4_mul_apply, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨by
      have h := g2Act_inv_apply a (q6 (1 : K) 0 0 0 0 0)
      rwa [ha.1] at h, by
      have h := g2Act_inv_apply a (q6 (0 : K) 0 0 0 0 1)
      rwa [ha.2] at h⟩

theorem burnsideB46_p4_mem_R2 {g : ↥(cayleyGroup K)} :
    g ∈ burnsideB46_p4_R2 K ↔ g2Act g (q6 1 0 0 0 0 0) = q6 1 0 0 0 0 0 ∧
      g2Act g (q6 0 0 0 0 0 1) = q6 0 0 0 0 0 1 := Iff.rfl

theorem burnsideB46_p4_F2_eq {w : Ix3 → K} (hw : w ∈ stdF K 2) :
    w = q6 (w (.inl 0)) 0 0 0 0 (w (.inr 2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.mp hw
  conv_lhs => rw [q6_eta w]
  rw [h1, h2, h3, h4]

theorem burnsideB46_p4_R2_fix {g : ↥(cayleyGroup K)} (hg : g ∈ burnsideB46_p4_R2 K)
    {w : Ix3 → K} (hw : w ∈ stdF K 2) : g2Act g w = w := by
  rw [burnsideB46_p4_F2_eq hw, q6_F2_decomp, map_add, burnsideB46_p4_smul, burnsideB46_p4_smul,
    hg.1, hg.2]

theorem burnsideB46_p4_R2_le_stabQ : burnsideB46_p4_R2 K ≤ stabQ (stdF K 2) := by
  intro g hg
  rw [mem_stabQ]
  intro w
  constructor
  · intro hw
    rw [burnsideB46_p4_R2_fix hg hw]
    exact hw
  · intro hw
    have h := burnsideB46_p4_R2_fix ((burnsideB46_p4_R2 K).inv_mem hg) hw
    rw [g2Act_inv_apply] at h
    exact h ▸ hw

theorem burnsideB46_p4_actX (α a b c d e f : K) :
    g2Act (g2X ![α, 0, 0]) (q6 a b c d e f) = q6 (a + α * α * d) b c d (e + α * c) (f + α * b) :=
  g2Act_x0q α a b c d e f

theorem burnsideB46_p4_actY (γ a b c d e f : K) :
    g2Act (g2Y ![0, 0, γ]) (q6 a b c d e f) =
      q6 (a + γ * e) (b + γ * d) c d e (f + γ * c * γ) := by
  rw [g2Act_y12q]
  refine q6_congr ?_ ?_ ?_ rfl ?_ ?_ <;> ring

theorem burnsideB46_p4_actA (p r b0 a b c d e f : K) :
    g2Act (g2A (uSL p r b0)) (q6 a b c d e f) =
      q6 (a + p * b + r * c) (b + b0 * c) c d (e + p * d) (f + (p * b0 + r) * d + b0 * e) := by
  rw [g2Act_g2A_uSL]
  rfl

theorem burnsideB46_p4_R2_param {g : ↥(cayleyGroup K)} (hg : g ∈ burnsideB46_p4_R2 K) :
    ∃ α γ p r b : K, g = g2X ![α, 0, 0] * g2Y ![0, 0, γ] * g2A (uSL p r b) := by
  have hu : g ∈ stabV0 K := by
    rw [mem_stabV0, eu_eq_q6]
    exact hg.1
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hu
  have hv := hg.2
  rw [act_v2_decomp α β γ hA] at hv
  obtain ⟨e1, -, -, -, e5, e6⟩ := q6_inj hv
  have hdet := det_block_of_fix hA
  rw [e5, e6] at hdet
  have hA22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by linear_combination hdet
  rw [e5, e6] at e1
  have hβ : β = 0 := by simpa using e1
  subst hβ
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hAu : A = uSL ((A : Matrix (Fin 3) (Fin 3) K) 0 1) ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
      ((A : Matrix (Fin 3) (Fin 3) K) 1 2) := by
    apply Subtype.ext
    have hU : ((uSL ((A : Matrix (Fin 3) (Fin 3) K) 0 1) ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
        ((A : Matrix (Fin 3) (Fin 3) K) 1 2) : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
        !![1, (A : Matrix (Fin 3) (Fin 3) K) 0 1, (A : Matrix (Fin 3) (Fin 3) K) 0 2;
          0, 1, (A : Matrix (Fin 3) (Fin 3) K) 1 2; 0, 0, 1] := rfl
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, e6, e5, hA22]
  exact ⟨α, γ, _, _, _, by rw [← hAu]⟩

theorem burnsideB46_p4_R2_mk (α γ p r b : K) :
    g2X ![α, 0, 0] * g2Y ![0, 0, γ] * g2A (uSL p r b) ∈ burnsideB46_p4_R2 K := by
  constructor
  · rw [burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply, burnsideB46_p4_actA,
      burnsideB46_p4_actY, burnsideB46_p4_actX]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rw [burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply, burnsideB46_p4_actA,
      burnsideB46_p4_actY, burnsideB46_p4_actX]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p4_R2_le_U0 : burnsideB46_p4_R2 K ≤ U0 K := by
  intro g hg
  obtain ⟨α, γ, p, r, b, rfl⟩ := burnsideB46_p4_R2_param hg
  exact (U0 K).mul_mem ((U0 K).mul_mem (g2X_mem_U0 α) (g2Y_mem_U0 0 γ)) (g2A_mem_U0 p r b)

theorem burnsideB46_p4_uSL_inj {p r b p' r' b' : K} (h : uSL p r b = uSL p' r' b') :
    p = p' ∧ r = r' ∧ b = b' := by
  have h1 := congrArg (fun A : SL3 K => (A : Matrix (Fin 3) (Fin 3) K)) h
  have e1 := congrFun (congrFun h1 0) 1
  have e2 := congrFun (congrFun h1 0) 2
  have e3 := congrFun (congrFun h1 1) 2
  exact ⟨e1, e2, e3⟩

theorem burnsideB46_p4_card_R2 : Nat.card ↥(burnsideB46_p4_R2 K) = Nat.card K ^ 5 := by
  have hbij : Function.Bijective (fun x : K × K × K × K × K =>
      (⟨g2X ![x.1, 0, 0] * g2Y ![0, 0, x.2.1] * g2A (uSL x.2.2.1 x.2.2.2.1 x.2.2.2.2),
        burnsideB46_p4_R2_mk _ _ _ _ _⟩ : ↥(burnsideB46_p4_R2 K))) := by
    constructor
    · intro x y h
      have h1 : stabElt (x.1, 0, x.2.1, (⟨uSL x.2.2.1 x.2.2.2.1 x.2.2.2.2,
          uSL_mem_S0 _ _ _⟩ : ↥(S0 K))) = stabElt (y.1, 0, y.2.1, (⟨uSL y.2.2.1 y.2.2.2.1 y.2.2.2.2,
          uSL_mem_S0 _ _ _⟩ : ↥(S0 K))) := congrArg Subtype.val h
      have h2 := stabElt_injective h1
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h2
      obtain ⟨e1, -, e3, e4⟩ := h2
      obtain ⟨hp, hr, hb⟩ := burnsideB46_p4_uSL_inj e4
      exact Prod.ext e1 (Prod.ext e3 (Prod.ext hp (Prod.ext hr hb)))
    · rintro ⟨g, hg⟩
      obtain ⟨α, γ, p, r, b, rfl⟩ := burnsideB46_p4_R2_param hg
      exact ⟨(α, γ, p, r, b), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  ring

theorem burnsideB46_p4_inC_add {x y : Ix3 → K} (hx : InC x) (hy : InC y) : InC (x + y) :=
  ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩

theorem burnsideB46_p4_inC_sub {x y : Ix3 → K} (hx : InC x) (hy : InC y) : InC (x - y) :=
  ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩

theorem burnsideB46_p4_inC_of_F2 {x : Ix3 → K} (hx : x ∈ stdF K 2) : InC x :=
  ⟨(mem_stdF_two.1 hx).2.1, (mem_stdF_two.1 hx).2.2.1⟩

@[expose] def burnsideB46_p4_Filt (g : ↥(cayleyGroup K)) : Prop :=
  (∀ w ∈ stdF K 2, g2Act g w = w) ∧ (∀ w, InC w → g2Act g w - w ∈ stdF K 2) ∧
    ∀ w, InC (g2Act g w - w)

theorem burnsideB46_p4_filt_mul {g h : ↥(cayleyGroup K)} (hg : burnsideB46_p4_Filt g)
    (hh : burnsideB46_p4_Filt h) : burnsideB46_p4_Filt (g * h) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w => ?_⟩
  · rw [burnsideB46_p4_mul_apply, hh.1 w hw, hg.1 w hw]
  · have e : g2Act (g * h) w - w = (g2Act g (g2Act h w) - g2Act h w) + (g2Act h w - w) := by
      rw [burnsideB46_p4_mul_apply]; abel
    have hhw : InC (g2Act h w) := by
      have := burnsideB46_p4_inC_add hw (burnsideB46_p4_inC_of_F2 (hh.2.1 w hw))
      rwa [add_sub_cancel] at this
    rw [e]
    exact (stdF K 2).add_mem (hg.2.1 _ hhw) (hh.2.1 w hw)
  · have e : g2Act (g * h) w - w = (g2Act g (g2Act h w) - g2Act h w) + (g2Act h w - w) := by
      rw [burnsideB46_p4_mul_apply]; abel
    rw [e]
    exact burnsideB46_p4_inC_add (hg.2.2 _) (hh.2.2 w)

theorem burnsideB46_p4_filt_x (α : K) : burnsideB46_p4_Filt (g2X ![α, 0, 0]) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w => ?_⟩
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl, rfl, rfl⟩ := burnsideB46_p4_F2_q6.1 hw
    rw [burnsideB46_p4_actX]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl⟩ := burnsideB46_p4_inC_q6.1 hw
    rw [burnsideB46_p4_actX, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_F2_q6.2 ⟨by ring, by ring, by ring, by ring⟩
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    rw [burnsideB46_p4_actX, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_inC_q6.2 ⟨by ring, by ring⟩

theorem burnsideB46_p4_filt_y (γ : K) : burnsideB46_p4_Filt (g2Y ![0, 0, γ]) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w => ?_⟩
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl, rfl, rfl⟩ := burnsideB46_p4_F2_q6.1 hw
    rw [burnsideB46_p4_actY]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl⟩ := burnsideB46_p4_inC_q6.1 hw
    rw [burnsideB46_p4_actY, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_F2_q6.2 ⟨by ring, by ring, by ring, by ring⟩
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    rw [burnsideB46_p4_actY, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_inC_q6.2 ⟨by ring, by ring⟩

theorem burnsideB46_p4_filt_A (p r b0 : K) : burnsideB46_p4_Filt (g2A (uSL p r b0)) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w => ?_⟩
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl, rfl, rfl⟩ := burnsideB46_p4_F2_q6.1 hw
    rw [burnsideB46_p4_actA]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl⟩ := burnsideB46_p4_inC_q6.1 hw
    rw [burnsideB46_p4_actA, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_F2_q6.2 ⟨by ring, by ring, by ring, by ring⟩
  · obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    rw [burnsideB46_p4_actA, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_inC_q6.2 ⟨by ring, by ring⟩

theorem burnsideB46_p4_R2_filt {g : ↥(cayleyGroup K)} (hg : g ∈ burnsideB46_p4_R2 K) :
    burnsideB46_p4_Filt g := by
  obtain ⟨α, γ, p, r, b, rfl⟩ := burnsideB46_p4_R2_param hg
  exact burnsideB46_p4_filt_mul (burnsideB46_p4_filt_mul (burnsideB46_p4_filt_x α)
    (burnsideB46_p4_filt_y γ)) (burnsideB46_p4_filt_A p r b)

theorem burnsideB46_p4_comm_shape {g h : ↥(cayleyGroup K)} (hg : burnsideB46_p4_Filt g)
    (hh : burnsideB46_p4_Filt h) (hgi : burnsideB46_p4_Filt g⁻¹) (hhi : burnsideB46_p4_Filt h⁻¹) :
    (∀ w, InC w → g2Act (g * h * g⁻¹ * h⁻¹) w = w) ∧
      ∀ w, g2Act (g * h * g⁻¹ * h⁻¹) w - w ∈ stdF K 2 := by
  have key : ∀ w : Ix3 → K, g2Act (g * h * g⁻¹ * h⁻¹) w - w =
      (g2Act g (g2Act h (g2Act g⁻¹ (g2Act h⁻¹ w)) - g2Act g⁻¹ (g2Act h⁻¹ w)) -
        (g2Act h (g2Act g⁻¹ (g2Act h⁻¹ w)) - g2Act g⁻¹ (g2Act h⁻¹ w))) -
      (g2Act h (g2Act g (g2Act g⁻¹ (g2Act h⁻¹ w)) - g2Act g⁻¹ (g2Act h⁻¹ w)) -
        (g2Act g (g2Act g⁻¹ (g2Act h⁻¹ w)) - g2Act g⁻¹ (g2Act h⁻¹ w))) := by
    intro w
    have e2 : g2Act h (g2Act g (g2Act g⁻¹ (g2Act h⁻¹ w))) = w := by
      rw [g2Act_apply_inv, g2Act_apply_inv]
    rw [burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply]
    simp only [map_sub]
    rw [e2]
    abel
  refine ⟨fun w hw => ?_, fun w => ?_⟩
  · have h1 : InC (g2Act h⁻¹ w) := by
      have := burnsideB46_p4_inC_add hw (burnsideB46_p4_inC_of_F2 (hhi.2.1 w hw))
      rwa [add_sub_cancel] at this
    have h2 : InC (g2Act g⁻¹ (g2Act h⁻¹ w)) := by
      have := burnsideB46_p4_inC_add h1 (burnsideB46_p4_inC_of_F2 (hgi.2.1 _ h1))
      rwa [add_sub_cancel] at this
    have ha := hh.2.1 _ h2
    have hb := hg.2.1 _ h2
    have := key w
    rw [hg.1 _ ha, hh.1 _ hb, sub_self, sub_self, sub_zero] at this
    exact sub_eq_zero.1 this
  · rw [key w]
    exact (stdF K 2).sub_mem (hg.2.1 _ (hh.2.2 _)) (hh.2.1 _ (hg.2.2 _))

theorem burnsideB46_p4_Z0_le_R2 : burnsideB46_p4_Z0 K ≤ burnsideB46_p4_R2 K := by
  rintro _ ⟨s, rfl⟩
  constructor
  · rw [g2Act_tL]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rw [g2Act_tL]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p4_g2A_mem_R2 (p r b : K) : g2A (uSL p r b) ∈ burnsideB46_p4_R2 K := by
  constructor
  · rw [burnsideB46_p4_actA]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rw [burnsideB46_p4_actA]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p4_comm_R2_le : ⁅burnsideB46_p4_R2 K, burnsideB46_p4_R2 K⁆ ≤
    burnsideB46_p4_Z0 K := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨hC, hF⟩ := burnsideB46_p4_comm_shape (burnsideB46_p4_R2_filt hg)
    (burnsideB46_p4_R2_filt hh) (burnsideB46_p4_R2_filt ((burnsideB46_p4_R2 K).inv_mem hg))
    (burnsideB46_p4_R2_filt ((burnsideB46_p4_R2 K).inv_mem hh))
  rw [commutatorElement_def]
  exact eq_tL_of_shape hC hF

theorem burnsideB46_p4_Z0_le_comm : burnsideB46_p4_Z0 K ≤
    ⁅burnsideB46_p4_R2 K, burnsideB46_p4_R2 K⁆ := by
  rintro _ ⟨c, rfl⟩
  have e : tL c = ⁅g2A (uSL (1 : K) 0 0), g2A (tv 1 2 (by decide) c)⁆ := by
    rw [← map_commutatorElement]
    have := comm_uSL_tv12 (1 : K) 0 c
    rw [one_mul] at this
    rw [this]
    rfl
  rw [e]
  have h2 : g2A (tv 1 2 (by decide) c) = g2A (uSL 0 0 c) := by
    congr 1
    apply Subtype.ext
    rw [tv12_lit]
    rfl
  rw [h2]
  exact Subgroup.commutator_mem_commutator (burnsideB46_p4_g2A_mem_R2 1 0 0)
    (burnsideB46_p4_g2A_mem_R2 0 0 c)

theorem burnsideB46_p4_comm_R2 : ⁅burnsideB46_p4_R2 K, burnsideB46_p4_R2 K⁆ =
    burnsideB46_p4_Z0 K :=
  le_antisymm burnsideB46_p4_comm_R2_le burnsideB46_p4_Z0_le_comm

theorem burnsideB46_p4_sq_R2 {g : ↥(cayleyGroup K)} (hg : g ∈ burnsideB46_p4_R2 K) :
    g * g ∈ burnsideB46_p4_Z0 K := by
  have hf := burnsideB46_p4_R2_filt hg
  have e : ∀ w : Ix3 → K, g2Act (g * g) w - w =
      (g2Act g (g2Act g w - w) - (g2Act g w - w)) + ((g2Act g w - w) + (g2Act g w - w)) := by
    intro w
    rw [burnsideB46_p4_mul_apply]
    simp only [map_sub]
    abel
  apply eq_tL_of_shape
  · intro w hw
    have ha := hf.2.1 w hw
    rw [sub_eq_zero.symm, e w, two_smul_eq_zero, burnsideB46_p4_R2_fix hg ha, sub_self, add_zero]
  · intro w
    rw [e w, two_smul_eq_zero, add_zero]
    exact hf.2.1 _ (hf.2.2 w)

theorem burnsideB46_p4_q6_decomp (a b c d e f : K) : q6 a b c d e f =
    a • q6 1 0 0 0 0 0 + b • q6 0 1 0 0 0 0 + c • q6 0 0 1 0 0 0 + d • q6 0 0 0 1 0 0 +
      e • q6 0 0 0 0 1 0 + f • q6 0 0 0 0 0 1 := by
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem burnsideB46_p4_act_expand (z : ↥(cayleyGroup K)) (a b c d e f : K) :
    g2Act z (q6 a b c d e f) = a • g2Act z (q6 1 0 0 0 0 0) + b • g2Act z (q6 0 1 0 0 0 0) +
      c • g2Act z (q6 0 0 1 0 0 0) + d • g2Act z (q6 0 0 0 1 0 0) +
      e • g2Act z (q6 0 0 0 0 1 0) + f • g2Act z (q6 0 0 0 0 0 1) := by
  conv_lhs => rw [burnsideB46_p4_q6_decomp]
  simp only [map_add, burnsideB46_p4_smul]

theorem burnsideB46_p4_g2X_mem_R2 (α : K) : g2X ![α, 0, 0] ∈ burnsideB46_p4_R2 K := by
  constructor
  · rw [burnsideB46_p4_actX]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rw [burnsideB46_p4_actX]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p4_g2Y_mem_R2 (γ : K) : g2Y ![0, 0, γ] ∈ burnsideB46_p4_R2 K := by
  constructor
  · rw [burnsideB46_p4_actY]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rw [burnsideB46_p4_actY]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem burnsideB46_p4_filt_shape {z : ↥(cayleyGroup K)} (hz : burnsideB46_p4_Filt z) :
    ∃ s0 s5 t0 t5 a b e f a' b' e' f' : K,
      g2Act z (q6 0 1 0 0 0 0) = q6 s0 1 0 0 0 s5 ∧
      g2Act z (q6 0 0 0 0 1 0) = q6 t0 0 0 0 1 t5 ∧
      g2Act z (q6 0 0 1 0 0 0) = q6 a b 1 0 e f ∧
      g2Act z (q6 0 0 0 1 0 0) = q6 a' b' 0 1 e' f' := by
  obtain ⟨A1, B1, C1, D1, E1, F1, h1⟩ := burnsideB46_p4_q6_exists (g2Act z (q6 0 1 0 0 0 0))
  obtain ⟨A2, B2, C2, D2, E2, F2, h2⟩ := burnsideB46_p4_q6_exists (g2Act z (q6 0 0 0 0 1 0))
  obtain ⟨A3, B3, C3, D3, E3, F3, h3⟩ := burnsideB46_p4_q6_exists (g2Act z (q6 0 0 1 0 0 0))
  obtain ⟨A4, B4, C4, D4, E4, F4, h4⟩ := burnsideB46_p4_q6_exists (g2Act z (q6 0 0 0 1 0 0))
  have c1 := hz.2.1 (q6 0 1 0 0 0 0) ⟨rfl, rfl⟩
  have c2 := hz.2.1 (q6 0 0 0 0 1 0) ⟨rfl, rfl⟩
  have c3 := hz.2.2 (q6 0 0 1 0 0 0)
  have c4 := hz.2.2 (q6 0 0 0 1 0 0)
  rw [h1, burnsideB46_p4_q6_sub_self, burnsideB46_p4_F2_q6] at c1
  rw [h2, burnsideB46_p4_q6_sub_self, burnsideB46_p4_F2_q6] at c2
  rw [h3, burnsideB46_p4_q6_sub_self, burnsideB46_p4_inC_q6] at c3
  rw [h4, burnsideB46_p4_q6_sub_self, burnsideB46_p4_inC_q6] at c4
  obtain ⟨c1a, c1b, c1c, c1d⟩ := c1
  obtain ⟨c2a, c2b, c2c, c2d⟩ := c2
  obtain ⟨c3a, c3b⟩ := c3
  obtain ⟨c4a, c4b⟩ := c4
  refine ⟨A1, F1, A2, F2, A3, B3, E3, F3, A4, B4, E4, F4, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    refine q6_congr rfl ?_ ?_ ?_ ?_ rfl
    · linear_combination c1a
    · linear_combination c1b
    · linear_combination c1c
    · linear_combination c1d
  · rw [h2]
    refine q6_congr rfl ?_ ?_ ?_ ?_ rfl
    · linear_combination c2a
    · linear_combination c2b
    · linear_combination c2c
    · linear_combination c2d
  · rw [h3]
    refine q6_congr rfl rfl ?_ ?_ rfl rfl
    · linear_combination c3a
    · linear_combination c3b
  · rw [h4]
    refine q6_congr rfl rfl ?_ ?_ rfl rfl
    · linear_combination c4a
    · linear_combination c4b

theorem burnsideB46_p4_center_R2_le {z : ↥(cayleyGroup K)} (hz : z ∈ burnsideB46_p4_R2 K)
    (hc : ∀ h ∈ burnsideB46_p4_R2 K, h * z = z * h) : z ∈ burnsideB46_p4_Z0 K := by
  have hf := burnsideB46_p4_R2_filt hz
  obtain ⟨s0, s5, t0, t5, a, b, e, f, a', b', e', f', hu1, hv1, hu2, hv0⟩ :=
    burnsideB46_p4_filt_shape hf
  have hcomm : ∀ h ∈ burnsideB46_p4_R2 K, ∀ w, g2Act h (g2Act z w) = g2Act z (g2Act h w) := by
    intro h hh w
    rw [← burnsideB46_p4_mul_apply, ← burnsideB46_p4_mul_apply, hc h hh]
  have xu2 : g2Act (g2X ![(1 : K), 0, 0]) (q6 (0 : K) 0 1 0 0 0) = q6 0 0 1 0 0 0 + q6 0 0 0 0 1 0 := by
    rw [burnsideB46_p4_actX, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have xv0 : g2Act (g2X ![(1 : K), 0, 0]) (q6 (0 : K) 0 0 1 0 0) = q6 0 0 0 1 0 0 + q6 1 0 0 0 0 0 := by
    rw [burnsideB46_p4_actX, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have yv0 : g2Act (g2Y ![(0 : K), 0, 1]) (q6 0 0 0 1 0 0) = q6 0 0 0 1 0 0 + q6 0 1 0 0 0 0 := by
    rw [burnsideB46_p4_actY, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have yu2 : g2Act (g2Y ![(0 : K), 0, 1]) (q6 0 0 1 0 0 0) = q6 0 0 1 0 0 0 + q6 0 0 0 0 0 1 := by
    rw [burnsideB46_p4_actY, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have g1v0 : g2Act (g2A (uSL (1 : K) 0 0)) (q6 0 0 0 1 0 0) = q6 0 0 0 1 0 0 + q6 0 0 0 0 1 0 := by
    rw [burnsideB46_p4_actA, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have g2u2 : g2Act (g2A (uSL (0 : K) 0 1)) (q6 0 0 1 0 0 0) = q6 0 0 1 0 0 0 + q6 0 1 0 0 0 0 := by
    rw [burnsideB46_p4_actA, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have hu0 : g2Act z (q6 1 0 0 0 0 0) = q6 1 0 0 0 0 0 := hz.1
  have hw2 : g2Act z (q6 0 0 0 0 0 1) = q6 0 0 0 0 0 1 := hz.2
  have e1 := hcomm _ (burnsideB46_p4_g2X_mem_R2 1) (q6 0 0 1 0 0 0)
  rw [hu2, burnsideB46_p4_actX, xu2, map_add, hu2, hv1, q6_add] at e1
  obtain ⟨c10, -, -, -, -, c15⟩ := q6_inj e1
  have e2 := hcomm _ (burnsideB46_p4_g2X_mem_R2 1) (q6 0 0 0 1 0 0)
  rw [hv0, burnsideB46_p4_actX, xv0, map_add, hv0, hu0, q6_add] at e2
  obtain ⟨-, -, -, -, -, c25⟩ := q6_inj e2
  have e3 := hcomm _ (burnsideB46_p4_g2Y_mem_R2 1) (q6 0 0 0 1 0 0)
  rw [hv0, burnsideB46_p4_actY, yv0, map_add, hv0, hu1, q6_add] at e3
  obtain ⟨c30, -, -, -, -, c35⟩ := q6_inj e3
  have e4 := hcomm _ (burnsideB46_p4_g2Y_mem_R2 1) (q6 0 0 1 0 0 0)
  rw [hu2, burnsideB46_p4_actY, yu2, map_add, hu2, hw2, q6_add] at e4
  obtain ⟨c40, -, -, -, -, -⟩ := q6_inj e4
  have e5 := hcomm _ (burnsideB46_p4_g2A_mem_R2 1 0 0) (q6 0 0 0 1 0 0)
  rw [hv0, burnsideB46_p4_actA, g1v0, map_add, hv0, hv1, q6_add] at e5
  obtain ⟨c50, -, -, -, -, c55⟩ := q6_inj e5
  have e6 := hcomm _ (burnsideB46_p4_g2A_mem_R2 0 0 1) (q6 0 0 1 0 0 0)
  rw [hu2, burnsideB46_p4_actA, g2u2, map_add, hu2, hu1, q6_add] at e6
  obtain ⟨c60, -, -, -, -, c65⟩ := q6_inj e6
  have ht0 : t0 = 0 := by linear_combination -c10
  have ht5 : t5 = 0 := by linear_combination -c55
  have hb : b = 0 := by linear_combination c15 - c55
  have hb' : b' = 0 := by linear_combination c25
  have hs0 : s0 = 0 := by linear_combination -c60
  have he' : e' = 0 := by linear_combination c30 - c60
  have hs5 : s5 = 0 := by linear_combination -c35
  have he : e = 0 := by linear_combination c40
  have hu1' : g2Act z (q6 0 1 0 0 0 0) = q6 0 1 0 0 0 0 := by rw [hu1, hs0, hs5]
  have hv1' : g2Act z (q6 0 0 0 0 1 0) = q6 0 0 0 0 1 0 := by rw [hv1, ht0, ht5]
  have hu2' : g2Act z (q6 0 0 1 0 0 0) = q6 a 0 1 0 0 f := by rw [hu2, hb, he]
  have hv0' : g2Act z (q6 0 0 0 1 0 0) = q6 a' 0 0 1 0 f' := by rw [hv0, hb', he']
  apply eq_tL_of_shape
  · intro w hw
    obtain ⟨a1, b1, c1, d1, e1, f1, rfl⟩ := burnsideB46_p4_q6_exists w
    obtain ⟨rfl, rfl⟩ := burnsideB46_p4_inC_q6.1 hw
    rw [burnsideB46_p4_act_expand, hu0, hu1', hv1', hw2]
    simp only [zero_smul, add_zero, q6_smul, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · intro w
    obtain ⟨a1, b1, c1, d1, e1, f1, rfl⟩ := burnsideB46_p4_q6_exists w
    rw [burnsideB46_p4_act_expand, hu0, hu1', hu2', hv0', hv1', hw2]
    simp only [q6_smul, q6_add, burnsideB46_p4_q6_sub_self]
    exact burnsideB46_p4_F2_q6.2 ⟨by ring, by ring, by ring, by ring⟩

theorem burnsideB46_p4_U0_fix_u0 {g : ↥(cayleyGroup K)} (hg : g ∈ U0 K) :
    g2Act g (q6 1 0 0 0 0 0) = q6 1 0 0 0 0 0 := by
  have h := hg 0 (q6 1 0 0 0 0 0) (by
    rw [inF_q6_iff]
    exact ⟨fun h => absurd h (by decide), fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl⟩)
  exact sub_eq_zero.1 (eq_zero_of_inF_zero h)

theorem burnsideB46_p4_conj_tL {g : ↥(cayleyGroup K)} (hg : g ∈ U0 K) (s : K) :
    g * tL s * g⁻¹ = tL s := by
  obtain ⟨s', hs'⟩ := conj_tL_mem (burnsideB46_p4_U0_le_stabQ_two hg) s
  have hgi : g⁻¹ ∈ U0 K := (U0 K).inv_mem hg
  obtain ⟨A, B, C, D, E, F, hv⟩ := burnsideB46_p4_q6_exists (g2Act g⁻¹ (q6 0 0 1 0 0 0))
  have hy := hgi 4 (q6 0 0 1 0 0 0) (by
    rw [inF_q6_iff]
    exact ⟨fun _ => rfl, fun _ => rfl, fun h => absurd h (by decide), fun _ => rfl, fun _ => rfl,
      fun _ => rfl⟩)
  rw [hv, burnsideB46_p4_q6_sub_self, inF_q6_iff] at hy
  have hC : C = 1 := by
    have := hy.2.2.1 (by norm_num)
    linear_combination this
  have hD : D = 0 := by
    have := hy.2.2.2.1 (by norm_num)
    linear_combination this
  have e1 : g2Act (g * tL s * g⁻¹) (q6 0 0 1 0 0 0) =
      g2Act g (g2Act (tL s) (g2Act g⁻¹ (q6 0 0 1 0 0 0))) := by
    rw [burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply]
  rw [hs', hv] at e1
  simp only [g2Act_tL] at e1
  have e2 : q6 (A + s * C) B C D E (F + s * D) =
      g2Act g⁻¹ (q6 0 0 1 0 0 0) + s • q6 1 0 0 0 0 0 := by
    rw [hv, q6_smul, q6_add, hC, hD]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [e2, map_add, burnsideB46_p4_smul, g2Act_apply_inv, burnsideB46_p4_U0_fix_u0 hg,
    q6_smul, q6_add] at e1
  obtain ⟨c0, -, -, -, -, -⟩ := q6_inj e1
  have hss : s' = s := by linear_combination c0
  rw [hs', hss]

theorem burnsideB46_p4_center_R2 :
    centerOf (burnsideB46_p4_R2 K) = burnsideB46_p4_Z0 K := by
  apply le_antisymm
  · rintro z ⟨hz, hzc⟩
    exact burnsideB46_p4_center_R2_le hz (fun h hh => Subgroup.mem_centralizer_iff.1 hzc h hh)
  · intro z hz
    obtain ⟨s, rfl⟩ := hz
    refine ⟨burnsideB46_p4_Z0_le_R2 ⟨s, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact mul_inv_eq_iff_eq_mul.1 (burnsideB46_p4_conj_tL (burnsideB46_p4_R2_le_U0 hh) s)

theorem burnsideB46_p4_center_U0 : centerOf (U0 K) = burnsideB46_p4_Z0 K := by
  apply le_antisymm
  · rintro z ⟨hz, hzc⟩
    have hcomm : ∀ h ∈ U0 K, ∀ w, g2Act h (g2Act z w) = g2Act z (g2Act h w) := by
      intro h hh w
      rw [← burnsideB46_p4_mul_apply, ← burnsideB46_p4_mul_apply,
        Subgroup.mem_centralizer_iff.1 hzc h hh]
    obtain ⟨A, B, C, D, E, F, hv⟩ := burnsideB46_p4_q6_exists (g2Act z (q6 0 1 0 0 0 0))
    have hy := hz 3 (q6 0 1 0 0 0 0) (by
      rw [inF_q6_iff]
      exact ⟨fun _ => rfl, fun h => absurd h (by decide), fun _ => rfl, fun _ => rfl, fun _ => rfl,
        fun _ => rfl⟩)
    rw [hv, burnsideB46_p4_q6_sub_self, inF_q6_iff] at hy
    have hB : B = 1 := by
      have := hy.2.1 (by norm_num)
      linear_combination this
    have hC : C = 0 := by
      have := hy.2.2.1 (by norm_num)
      linear_combination this
    have hD : D = 0 := by
      have := hy.2.2.2.1 (by norm_num)
      linear_combination this
    have xu1 : g2Act (g2X ![(1 : K), 0, 0]) (q6 (0 : K) 1 0 0 0 0) =
        q6 0 1 0 0 0 0 + q6 0 0 0 0 0 1 := by
      rw [burnsideB46_p4_actX, q6_add]
      refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    have e := hcomm _ (g2X_mem_U0 1) (q6 0 1 0 0 0 0)
    rw [hv, burnsideB46_p4_actX, xu1, map_add, hv] at e
    have e' : g2Act z (q6 0 0 0 0 0 1) = q6 0 0 0 0 0 1 := by
      have e2 : q6 (A + 1 * 1 * D) B C D (E + 1 * C) (F + 1 * B) =
          q6 A B C D E F + g2Act z (q6 0 0 0 0 0 1) := e
      have e3 : g2Act z (q6 0 0 0 0 0 1) = q6 (A + 1 * 1 * D) B C D (E + 1 * C) (F + 1 * B) -
          q6 A B C D E F := by
        rw [e2]
        abel
      rw [e3, burnsideB46_p4_q6_sub_self, hB, hC, hD]
      refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    have hzR : z ∈ burnsideB46_p4_R2 K := ⟨burnsideB46_p4_U0_fix_u0 hz, e'⟩
    exact burnsideB46_p4_center_R2_le hzR fun h hh =>
      Subgroup.mem_centralizer_iff.1 hzc h (burnsideB46_p4_R2_le_U0 hh)
  · intro z hz
    obtain ⟨s, rfl⟩ := hz
    refine ⟨burnsideB46_p4_tL_mem_U0 s, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact mul_inv_eq_iff_eq_mul.1 (burnsideB46_p4_conj_tL hh s)

theorem burnsideB46_p4_R2_isPGroup : IsPGroup 2 ↥(burnsideB46_p4_R2 K) :=
  isPGroup_U0.of_injective (Subgroup.inclusion (burnsideB46_p4_R2_le_U0 (K := K)))
    (Subgroup.inclusion_injective _)

theorem burnsideB46_p4_R2_special [Finite K] :
    IsSpecial2 (burnsideB46_p4_R2 K) (burnsideB46_p4_Z0 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  haveI : Finite ↥(burnsideB46_p4_R2 K) := Subtype.finite
  have hmapcomm : (⁅(⊤ : Subgroup ↥(burnsideB46_p4_R2 K)), (⊤ : Subgroup ↥(burnsideB46_p4_R2 K))⁆ :
      Subgroup ↥(burnsideB46_p4_R2 K)).map (burnsideB46_p4_R2 K).subtype =
      burnsideB46_p4_Z0 K := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact burnsideB46_p4_comm_R2
  have hN : (burnsideB46_p4_Z0 K).subgroupOf (burnsideB46_p4_R2 K) =
      ⁅(⊤ : Subgroup ↥(burnsideB46_p4_R2 K)), (⊤ : Subgroup ↥(burnsideB46_p4_R2 K))⁆ := by
    apply Subgroup.map_injective (burnsideB46_p4_R2 K).subtype_injective
    rw [hmapcomm, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 (burnsideB46_p4_Z0_le_R2 (K := K))
  haveI : ((burnsideB46_p4_Z0 K).subgroupOf (burnsideB46_p4_R2 K)).Normal := by
    rw [hN]
    exact Subgroup.commutator_normal _ _
  have hfr : frattini ↥(burnsideB46_p4_R2 K) =
      (burnsideB46_p4_Z0 K).subgroupOf (burnsideB46_p4_R2 K) :=
    CFSG.Sporadic.Recognition.LyonsSims.frattini_eq_of_commutator_eq burnsideB46_p4_R2_isPGroup
      hN.symm (fun a => by
        rw [Subgroup.mem_subgroupOf, pow_two]
        exact burnsideB46_p4_sq_R2 a.2)
  refine ⟨burnsideB46_p4_R2_isPGroup, burnsideB46_p4_center_R2, burnsideB46_p4_comm_R2, ?_, ?_⟩
  · rw [hfr, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 (burnsideB46_p4_Z0_le_R2 (K := K))
  · intro h
    have : tL (1 : K) ∈ burnsideB46_p4_Z0 K := ⟨1, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact tL_one_ne_one this

theorem burnsideB46_p4_normalizer_Z0 :
    Subgroup.normalizer ((burnsideB46_p4_Z0 K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) =
      stabQ (stdF K 2) := by
  have hle : ∀ g ∈ Subgroup.normalizer
      ((burnsideB46_p4_Z0 K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)),
      ∀ w ∈ stdF K 2, g2Act g w ∈ stdF K 2 := by
    intro g hg w hw
    obtain ⟨s', hs'⟩ := (Subgroup.mem_normalizer_iff.1 hg (tL 1)).1 ⟨1, rfl⟩
    obtain ⟨y, hy⟩ := exists_tL_sub_eq (one_ne_zero (α := K)) hw
    have e : g2Act g w = g2Act (tL s') (g2Act g y) - g2Act g y := by
      rw [← hs', ← hy, map_sub, burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply,
        g2Act_inv_apply]
    rw [e]
    exact g2Act_tL_sub_mem s' _
  ext g
  constructor
  · intro hg
    rw [mem_stabQ]
    intro w
    refine ⟨hle g hg w, fun h => ?_⟩
    have hgi : g⁻¹ ∈ Subgroup.normalizer
        ((burnsideB46_p4_Z0 K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) :=
      Subgroup.inv_mem _ hg
    have := hle g⁻¹ hgi _ h
    rwa [g2Act_inv_apply] at this
  · intro hg
    have key : ∀ γ ∈ stabQ (stdF K 2), ∀ h ∈ burnsideB46_p4_Z0 K, γ * h * γ⁻¹ ∈ burnsideB46_p4_Z0 K := by
      rintro γ hγ _ ⟨s, rfl⟩
      obtain ⟨s', hs'⟩ := conj_tL_mem hγ s
      exact ⟨s', hs'⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hh => ?_⟩
    have := key g⁻¹ ((stabQ (stdF K 2)).inv_mem hg) _ hh
    simpa [mul_assoc] using this

@[expose] def burnsideB46_p4_levi2GL (K : Type) [Field K] [CharP K 2] :
    ↥(stabQ (stdF K 2)) →* GL (Fin 2) K where
  toFun g := ⟨levi2Mat g.1, levi2Mat g.1⁻¹, by
      have h := levi2Mat_mul (g := g.1) ((stabQ (stdF K 2)).inv_mem g.2)
      rw [mul_inv_cancel, levi2Mat_one] at h
      exact h.symm, by
      have h := levi2Mat_mul (g := g.1⁻¹) g.2
      rw [inv_mul_cancel, levi2Mat_one] at h
      exact h.symm⟩
  map_one' := Units.ext levi2Mat_one
  map_mul' g h := Units.ext (levi2Mat_mul h.2)

theorem burnsideB46_p4_levi2GL_coe (g : ↥(stabQ (stdF K 2))) :
    ((burnsideB46_p4_levi2GL K g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = levi2Mat g.1 :=
  rfl

theorem burnsideB46_p4_ker_levi2GL :
    (burnsideB46_p4_levi2GL K).ker = (burnsideB46_p4_R2 K).subgroupOf (stabQ (stdF K 2)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hM : levi2Mat g.1 = 1 := by
      have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h
      exact this
    have h00 := congrFun (congrFun hM 0) 0
    have h10 := congrFun (congrFun hM 1) 0
    have h01 := congrFun (congrFun hM 0) 1
    have h11 := congrFun (congrFun hM 1) 1
    simp only [levi2Mat_apply, upart] at h00 h10 h01 h11
    simp at h00 h10 h01 h11
    have hu : g2Act g.1 (q6 1 0 0 0 0 0) ∈ stdF K 2 :=
      (mem_stabQ.1 g.2 _).1 (burnsideB46_p4_F2_of)
    have hv : g2Act g.1 (q6 0 0 0 0 0 1) ∈ stdF K 2 :=
      (mem_stabQ.1 g.2 _).1 (burnsideB46_p4_F2_of)
    refine ⟨?_, ?_⟩
    · rw [burnsideB46_p4_F2_eq hu, h00, h10]
    · rw [burnsideB46_p4_F2_eq hv, h01, h11]
  · intro hg
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB46_p4_levi2GL_coe, levi2Mat_apply, upart, hg.1, hg.2, q6_apply_inl0,
        q6_apply_inr2]

theorem burnsideB46_p4_GL2_pCore [Finite K] {N : Subgroup (GL (Fin 2) K)} [hN : N.Normal]
    (hp : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL
  have h1 : N.comap φ = ⊥ := by
    haveI : (N.comap φ).Normal := hN.comap φ
    exact CFSG.Quasithin.Vol2.KGNat.eq_bot_of_normal_isPGroup_SL2
      (hp.comap_of_injective φ Matrix.SpecialLinearGroup.toGL_injective)
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨k, hk⟩ := hp ⟨n, hn⟩
  have hnk : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdet : Matrix.GeneralLinearGroup.det n = 1 := by
    have h2 : (Matrix.GeneralLinearGroup.det n) ^ 2 ^ k = 1 := by
      rw [← map_pow, hnk, map_one]
    have h3 : (((Matrix.GeneralLinearGroup.det n : Kˣ) : K) - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self]
    have h4 : ((Matrix.GeneralLinearGroup.det n : Kˣ) : K) - 1 = 0 :=
      pow_eq_zero_iff (by positivity) |>.1 h3
    exact Units.ext (sub_eq_zero.1 h4)
  have hdet' : (n : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨(n : Matrix (Fin 2) (Fin 2) K), hdet'⟩
  have hφA : φ A = n := Units.ext rfl
  have hmem : A ∈ N.comap φ := by
    rw [Subgroup.mem_comap, hφA]
    exact hn
  rw [h1, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot, ← hφA, hmem, map_one]

@[expose] def burnsideB46_p4_dg (d : Kˣ) : GL (Fin 2) K :=
  ⟨!![1, 0; 0, (d : K)], !![1, 0; 0, ((d⁻¹ : Kˣ) : K)], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

theorem burnsideB46_p4_det_dg (d : Kˣ) : Matrix.GeneralLinearGroup.det (burnsideB46_p4_dg d) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [burnsideB46_p4_dg, Matrix.det_fin_two_of]

theorem burnsideB46_p4_levi2GL_surjective [Finite K] (h4 : 4 ≤ Nat.card K) :
    Function.Surjective (burnsideB46_p4_levi2GL K) := by
  intro M
  set d : Kˣ := Matrix.GeneralLinearGroup.det M with hd
  have hdet : Matrix.GeneralLinearGroup.det (M * (burnsideB46_p4_dg d)⁻¹) = 1 := by
    rw [map_mul, map_inv, burnsideB46_p4_det_dg, ← hd, mul_inv_cancel]
  have hdetM : ((M * (burnsideB46_p4_dg d)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  obtain ⟨g₁, hg₁⟩ := levi2_surjective h4
    (⟨((M * (burnsideB46_p4_dg d)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), hdetM⟩ :
      Matrix.SpecialLinearGroup (Fin 2) K)
  have hg₁s : g₁.1 ∈ stabQ (stdF K 2) := perfectCore_le _ g₁.2
  have hg₂s : g2T (1, d) ∈ stabQ (stdF K 2) := g2T_mem_stabQ _ 2
  refine ⟨⟨g₁.1 * g2T (1, d), (stabQ (stdF K 2)).mul_mem hg₁s hg₂s⟩, ?_⟩
  apply Units.ext
  rw [burnsideB46_p4_levi2GL_coe]
  show levi2Mat (g₁.1 * g2T (1, d)) = _
  rw [levi2Mat_mul hg₂s, levi2Mat_g2T]
  have h1 : levi2Mat g₁.1 = ((M * (burnsideB46_p4_dg d)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) hg₁
  rw [h1]
  have h2 : (!![((1 : Kˣ) : K), 0; 0, ((1 : Kˣ) : K) * (d : K)] : Matrix (Fin 2) (Fin 2) K) =
      ((burnsideB46_p4_dg d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideB46_p4_dg]
  rw [h2, ← Units.val_mul, inv_mul_cancel_right]

theorem burnsideB46_p4_pCore_P2 [Finite K] (h4 : 4 ≤ Nat.card K) :
    pCoreOf 2 (stabQ (stdF K 2)) = burnsideB46_p4_R2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  haveI : Finite ↥(stabQ (stdF K 2)) := Subtype.finite
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hbot := burnsideB46_p4_GL2_pCore (N := (CFSG.pCore 2 ↥(stabQ (stdF K 2))).map
      (burnsideB46_p4_levi2GL K))
      (hN := (CFSG.LieType.BorelTits.pCore_normal 2).map _ (burnsideB46_p4_levi2GL_surjective h4))
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥(stabQ (stdF K 2)))).map
        (burnsideB46_p4_levi2GL K))
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hy' : y ∈ (burnsideB46_p4_levi2GL K).ker := hbot hy
    rw [burnsideB46_p4_ker_levi2GL, Subgroup.mem_subgroupOf] at hy'
    exact hy'
  · apply CFSG.LieType.BorelTits.le_pCoreOf 2 burnsideB46_p4_R2_le_stabQ
    · rw [← burnsideB46_p4_ker_levi2GL]
      exact MonoidHom.normal_ker _
    · exact burnsideB46_p4_R2_isPGroup

theorem burnsideB46_p4_fixSub_R2 : fixSub (burnsideB46_p4_R2 K) = stdF K 2 := by
  ext w
  constructor
  · intro hw
    obtain ⟨a, b, c, d, e, f, rfl⟩ := burnsideB46_p4_q6_exists w
    have h1 := hw _ (burnsideB46_p4_g2X_mem_R2 1)
    have h2 := hw _ (burnsideB46_p4_g2Y_mem_R2 1)
    rw [burnsideB46_p4_actX] at h1
    rw [burnsideB46_p4_actY] at h2
    obtain ⟨k1, -, -, -, k5, k6⟩ := q6_inj h1
    obtain ⟨m1, -, -, -, -, -⟩ := q6_inj h2
    exact burnsideB46_p4_F2_q6.2 ⟨by linear_combination k6, by linear_combination k5,
      by linear_combination k1, by linear_combination m1⟩
  · intro hw g hg
    exact burnsideB46_p4_R2_fix hg hw

theorem burnsideB46_p4_mem_stdF_four {w : Ix3 → K} : w ∈ stdF K 4 ↔ InC w := by
  rw [mem_stdF, q6_eta w, inF_q6_iff]
  constructor
  · rintro ⟨-, -, h3, h4, -, -⟩
    exact ⟨h3 (by norm_num), h4 (by norm_num)⟩
  · rintro ⟨h3, h4⟩
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => h3,
      fun _ => h4, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩

theorem burnsideB46_p4_fixSub_Z0 : fixSub (burnsideB46_p4_Z0 K) = stdF K 4 := by
  ext w
  rw [burnsideB46_p4_mem_stdF_four]
  constructor
  · intro hw
    have h1 : tL (1 : K) ∈ burnsideB46_p4_Z0 K := ⟨1, rfl⟩
    exact inC_of_tL_fix one_ne_zero (mem_fixSub.1 hw (tL 1) h1)
  · intro hw g hg
    obtain ⟨s, rfl⟩ := hg
    exact g2Act_tL_of_inC s hw

theorem burnsideB46_p4_fixSub_zpowers {z : ↥(cayleyGroup K)} (hz : z ∈ burnsideB46_p4_Z0 K)
    (hz1 : z ≠ 1) : fixSub (Subgroup.zpowers z) = stdF K 4 := by
  obtain ⟨s, rfl⟩ := hz
  have hs : s ≠ 0 := by
    rintro rfl
    exact hz1 (tL_zero (K := K))
  have hmem : tL s ∈ burnsideB46_p4_Z0 K := ⟨s, rfl⟩
  rw [← burnsideB46_p4_fixSub_Z0]
  apply le_antisymm
  · intro w hw g hg
    obtain ⟨t, rfl⟩ := hg
    have := inC_of_tL_fix hs (mem_fixSub.1 hw (tL s) (Subgroup.mem_zpowers _))
    exact g2Act_tL_of_inC t this
  · intro w hw g hg
    exact mem_fixSub.1 hw g ((Subgroup.zpowers_le.2 hmem) hg)

theorem burnsideB46_p4_finrank_stdF [Finite K] {h : ℕ} (hh : h ≤ 6) :
    Module.finrank K (stdF K h) = h := by
  have h1 : Nat.card (stdF K h) = Nat.card K ^ Module.finrank K (stdF K h) :=
    Module.natCard_eq_pow_finrank
  rw [card_stdF hh] at h1
  exact (Nat.pow_right_injective Finite.one_lt_card h1).symm

end P4

section P4a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

open CFSG.QuasithinUnique.Bridge.Alt57Model (stabElt stabElt_injective S0)

open scoped commutatorElement

@[expose] def burnsideB46_p4_NatMod (K : Type) [Field K] [CharP K 2]
    (P R : Subgroup ↥(cayleyGroup K)) (Y : Submodule K (Ix3 → K)) : Prop :=
  R ≤ P ∧ (∀ g ∈ P, ∀ y ∈ Y, g2Act g y ∈ Y) ∧
    ∃ (ρ : ↥P →* GL (Fin 2) K) (ζ : (Ix3 → K) →+ (Fin 2 → K)), Function.Surjective ρ ∧
      ρ.ker = R.subgroupOf P ∧ Set.InjOn ζ (Y : Set (Ix3 → K)) ∧
      Set.SurjOn ζ (Y : Set (Ix3 → K)) Set.univ ∧
      ∀ (g : ↥P) (y : Ix3 → K), y ∈ Y → ζ (g2Act g.1 y) =
        Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) K) (ζ y)

variable {K : Type} [Field K] [CharP K 2]

@[expose] def burnsideB46_p4_upartHom : (Ix3 → K) →+ (Fin 2 → K) :=
  AddMonoidHom.mk' upart upart_add

theorem burnsideB46_p4_natMod_std [Finite K] (h4 : 4 ≤ Nat.card K) :
    burnsideB46_p4_NatMod K (stabQ (stdF K 2)) (burnsideB46_p4_R2 K) (stdF K 2) := by
  refine ⟨burnsideB46_p4_R2_le_stabQ, fun g hg y hy => (mem_stabQ.1 hg y).1 hy,
    burnsideB46_p4_levi2GL K, burnsideB46_p4_upartHom, burnsideB46_p4_levi2GL_surjective h4,
    burnsideB46_p4_ker_levi2GL, ?_, ?_, ?_⟩
  · intro y hy y' hy' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [burnsideB46_p4_upartHom, AddMonoidHom.mk'_apply, upart] at h0 h1
    simp at h0 h1
    rw [burnsideB46_p4_F2_eq hy, burnsideB46_p4_F2_eq hy', h0, h1]
  · intro k _
    refine ⟨q6 (k 0) 0 0 0 0 (k 1), burnsideB46_p4_F2_of, ?_⟩
    funext i
    fin_cases i <;> simp [burnsideB46_p4_upartHom, upart, q6]
  · intro g y hy
    exact upart_act g.1 hy

structure burnsideB46_p4_Coord (V : Type) [CommGroup V] (K : Type) [Field K] [CharP K 2]
    (L : Subgroup (MulAut V)) where
  Φ : ↥(cayleyGroup K) →* MulAut V
  f : V → (Ix3 → K)
  inj : Function.Injective Φ
  mem_L : ∀ l : MulAut V, l ∈ L ↔ ∃ g, Φ g = l
  f_mul : ∀ v w, f (v * w) = f v + f w
  f_surj : Function.Surjective f
  f_ker : ∀ v, f v = 0 ↔ v ∈ fixV L
  f_act : ∀ g v, f (Φ g v) = g2Act g (f v)

namespace burnsideB46_p4_Coord

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} (C : burnsideB46_p4_Coord V K L)

theorem f_one : C.f 1 = 0 := by
  have h := C.f_mul 1 1
  rw [mul_one] at h
  have h2 : C.f 1 + C.f 1 = C.f 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem f_inv (v : V) : C.f v⁻¹ = - C.f v := by
  have h := C.f_mul v v⁻¹
  rw [mul_inv_cancel, C.f_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem f_sub (v w : V) : C.f (v * w⁻¹) = C.f v - C.f w := by
  rw [C.f_mul, C.f_inv, sub_eq_add_neg]

@[expose] def pre (Y : Submodule K (Ix3 → K)) : Subgroup V where
  carrier := {v | C.f v ∈ Y}
  one_mem' := by
    change C.f 1 ∈ Y
    rw [C.f_one]
    exact Y.zero_mem
  mul_mem' := fun {a b} ha hb => by
    change C.f (a * b) ∈ Y
    rw [C.f_mul]
    exact Y.add_mem ha hb
  inv_mem' := fun {a} ha => by
    change C.f a⁻¹ ∈ Y
    rw [C.f_inv]
    exact Y.neg_mem ha

theorem mem_pre {Y : Submodule K (Ix3 → K)} {v : V} : v ∈ C.pre Y ↔ C.f v ∈ Y := Iff.rfl

theorem fixV_le_pre (Y : Submodule K (Ix3 → K)) : fixV L ≤ C.pre Y := fun v hv => by
  rw [mem_pre, (C.f_ker v).2 hv]
  exact Y.zero_mem

theorem pre_le_pre_iff {Y Y' : Submodule K (Ix3 → K)} : C.pre Y ≤ C.pre Y' ↔ Y ≤ Y' := by
  constructor
  · intro h y hy
    obtain ⟨v, rfl⟩ := C.f_surj y
    exact h hy
  · intro h v hv
    exact h hv

theorem pre_injective {Y Y' : Submodule K (Ix3 → K)} (h : C.pre Y = C.pre Y') : Y = Y' :=
  le_antisymm (C.pre_le_pre_iff.1 h.le) (C.pre_le_pre_iff.1 h.ge)

theorem pre_inf (Y Y' : Submodule K (Ix3 → K)) : C.pre Y ⊓ C.pre Y' = C.pre (Y ⊓ Y') := rfl

theorem cPre_map (X : Subgroup ↥(cayleyGroup K)) :
    cPre (fixV L) (X.map C.Φ) = C.pre (fixSub X) := by
  ext v
  rw [burnsideB46_mem_cPre, mem_pre]
  constructor
  · intro h γ hγ
    have h1 := h (C.Φ γ) ⟨γ, hγ, rfl⟩
    have h2 := (C.f_ker _).2 h1
    rw [C.f_sub, C.f_act, sub_eq_zero] at h2
    exact h2
  · intro h z hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    refine (C.f_ker _).1 ?_
    rw [C.f_sub, C.f_act, sub_eq_zero]
    exact h γ hγ

theorem map_pre (g : ↥(cayleyGroup K)) (Y : Submodule K (Ix3 → K)) :
    (C.pre Y).map (C.Φ g : MulAut V).toMonoidHom = C.pre (gmapG g Y) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_pre]
    change C.f ((C.Φ g) v) ∈ gmapG g Y
    rw [C.f_act, mem_gmapG, g2Act_inv_apply]
    exact hv
  · intro hw
    rw [mem_pre, mem_gmapG] at hw
    refine ⟨C.Φ g⁻¹ w, ?_, ?_⟩
    · change C.f ((C.Φ g⁻¹) w) ∈ Y
      rw [C.f_act]
      exact hw
    · change (C.Φ g) ((C.Φ g⁻¹) w) = w
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem natMod {P R : Subgroup ↥(cayleyGroup K)} {Y : Submodule K (Ix3 → K)}
    (h : burnsideB46_p4_NatMod K P R Y) :
    IsNatGL2SecMod K (P.map C.Φ) (R.map C.Φ) (C.pre Y) (fixV L) := by
  obtain ⟨hRP, hY, ρ, ζ, hρs, hρk, hinj, hsurj, hequiv⟩ := h
  let e : ↥P ≃* ↥(P.map C.Φ) := P.equivMapOfInjective C.Φ C.inj
  let ρ' : ↥(P.map C.Φ) →* GL (Fin 2) K := ρ.comp e.symm.toMonoidHom
  have hρ's : Function.Surjective ρ' := hρs.comp e.symm.surjective
  have hep : ∀ p : ↥(P.map C.Φ), p.1 = C.Φ (e.symm p).1 := fun p =>
    (congrArg Subtype.val (e.apply_symm_apply p)).symm
  have hρ'k : ρ'.ker = (R.map C.Φ).subgroupOf (P.map C.Φ) := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : e.symm p ∈ ρ.ker := h1
      rw [hρk, Subgroup.mem_subgroupOf] at h2
      rw [hep p]
      exact ⟨_, h2, rfl⟩
    · intro h1
      rw [hep p] at h1
      have h3 : (e.symm p).1 ∈ R := (Subgroup.mem_map_iff_mem C.inj).1 h1
      have h2 : e.symm p ∈ ρ.ker := by
        rw [hρk, Subgroup.mem_subgroupOf]
        exact h3
      exact h2
  haveI hnorm : ((R.map C.Φ).subgroupOf (P.map C.Φ)).Normal := hρ'k ▸ MonoidHom.normal_ker ρ'
  let θ' : ↥(P.map C.Φ) ⧸ (R.map C.Φ).subgroupOf (P.map C.Φ) ≃* GL (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hρ'k.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ's)
  let ζ' : ↥(C.pre Y) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun y => Multiplicative.ofAdd (ζ (C.f y.1))
      map_one' := by
        change Multiplicative.ofAdd (ζ (C.f 1)) = 1
        rw [C.f_one, map_zero]
        rfl
      map_mul' := fun a b => by
        change Multiplicative.ofAdd (ζ (C.f (a.1 * b.1))) = _
        rw [C.f_mul, map_add]
        rfl }
  refine ⟨Subgroup.map_mono hRP, C.fixV_le_pre Y, ?_, ?_, hnorm, θ', ζ', ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ y hy
    change C.f ((C.Φ g) y) ∈ Y
    rw [C.f_act]
    exact hY g hg _ hy
  · rintro _ ⟨g, hg, rfl⟩ c hc
    have hL : C.Φ g ∈ L := (C.mem_L _).2 ⟨g, rfl⟩
    rw [mem_fixV.1 hc _ hL]
    exact hc
  · intro k
    obtain ⟨y0, hy0, hζ⟩ := hsurj (Set.mem_univ (Multiplicative.toAdd k))
    obtain ⟨v, hv⟩ := C.f_surj y0
    refine ⟨⟨v, by rw [mem_pre, hv]; exact hy0⟩, ?_⟩
    change Multiplicative.ofAdd (ζ (C.f v)) = k
    rw [hv, hζ]
    rfl
  · ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Multiplicative.ofAdd (ζ (C.f y.1)) = 1 ↔ y.1 ∈ fixV L
    rw [← C.f_ker]
    constructor
    · intro h1
      have h2 : ζ (C.f y.1) = 0 := h1
      exact hinj y.2 Y.zero_mem (by rw [h2, map_zero])
    · intro h1
      rw [h1, map_zero]
      rfl
  · rintro ⟨p, hp⟩ y y' hyy'
    obtain ⟨g, hg, rfl⟩ := hp
    have hθ : θ' (QuotientGroup.mk (⟨C.Φ g, ⟨g, hg, rfl⟩⟩ : ↥(P.map C.Φ))) =
        ρ ⟨g, hg⟩ := by
      have he : e.symm ⟨C.Φ g, ⟨g, hg, rfl⟩⟩ = ⟨g, hg⟩ := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      have h1 : θ' (QuotientGroup.mk (⟨C.Φ g, ⟨g, hg, rfl⟩⟩ : ↥(P.map C.Φ))) =
          ρ (e.symm ⟨C.Φ g, ⟨g, hg, rfl⟩⟩) := rfl
      rw [h1, he]
    rw [hθ]
    change Multiplicative.ofAdd (ζ (C.f y'.1)) = _
    rw [hyy', C.f_act]
    exact congrArg Multiplicative.ofAdd (hequiv ⟨g, hg⟩ _ y.2)

theorem comm_pre {g0 : ↥(cayleyGroup K)} {X : Subgroup ↥(cayleyGroup K)}
    {Y : Submodule K (Ix3 → K)} (hg0 : g0 ∈ X) (hX : ∀ g ∈ X, ∀ w, g2Act g w - w ∈ Y)
    (hY : ∀ y ∈ Y, ∃ w, g2Act g0 w - w = y) :
    commV (Subgroup.zpowers (C.Φ g0)) ⊔ fixV L = C.pre Y := by
  apply le_antisymm
  · refine sup_le ?_ (C.fixV_le_pre Y)
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hk : g0 ^ k ∈ X := X.zpow_mem hg0 k
    change C.f ((C.Φ g0 ^ k) v * v⁻¹) ∈ Y
    rw [← map_zpow, C.f_sub, C.f_act]
    exact hX _ hk _
  · intro v hv
    have hv' : C.f v ∈ Y := hv
    obtain ⟨w0, hw0⟩ := hY _ hv'
    obtain ⟨u, hu⟩ := C.f_surj w0
    have hz : (C.Φ g0) u * u⁻¹ ∈ commV (Subgroup.zpowers (C.Φ g0)) :=
      Subgroup.subset_closure ⟨C.Φ g0, Subgroup.mem_zpowers _, u, rfl⟩
    have hfix : v * ((C.Φ g0) u * u⁻¹)⁻¹ ∈ fixV L := by
      refine (C.f_ker _).1 ?_
      rw [C.f_sub, C.f_sub, C.f_act, hu, hw0, sub_self]
    have e : v = ((C.Φ g0) u * u⁻¹) * (v * ((C.Φ g0) u * u⁻¹)⁻¹) := by
      rw [mul_comm v (((C.Φ g0) u * u⁻¹)⁻¹), mul_inv_cancel_left]
    rw [e]
    exact Subgroup.mul_mem_sup hz hfix

end burnsideB46_p4_Coord

section OfHyp

variable {V : Type} [CommGroup V] {n : ℕ} {G L : Subgroup (MulAut V)}
  {π : ↥(quasithinG2 K) →* MulAut V} {θ : V →* Multiplicative (NatQ K)}

@[expose] noncomputable def burnsideB46_p4_ofHyp (H : burnsideB46_Hyp V n K G L π θ)
    (c : ↥(cayleyGroup K)) : burnsideB46_p4_Coord V K L where
  Φ := (burnsideB46_pi π).comp (MulAut.conj c).toMonoidHom
  f v := g2Act c⁻¹ (burnsideB46_f θ v)
  inj := (burnsideB46_pi_injective H).comp (MulAut.conj c).injective
  mem_L l := by
    rw [burnsideB46_mem_L' H]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨c⁻¹ * g * c, ?_⟩
      change burnsideB46_pi π (c * (c⁻¹ * g * c) * c⁻¹) = _
      rw [show c * (c⁻¹ * g * c) * c⁻¹ = g by group]
    · rintro ⟨g, rfl⟩
      exact ⟨_, rfl⟩
  f_mul v w := by rw [burnsideB46_f_mul, map_add]
  f_surj w := by
    obtain ⟨v, hv⟩ := burnsideB46_f_surj H (g2Act c w)
    exact ⟨v, by
      show g2Act c⁻¹ (burnsideB46_f θ v) = w
      rw [hv, g2Act_inv_apply]⟩
  f_ker v := by
    rw [← burnsideB46_f_eq_zero_iff H]
    constructor
    · intro h
      have := congrArg (g2Act c) h
      rwa [g2Act_apply_inv, map_zero] at this
    · intro h
      rw [h, map_zero]
  f_act g v := by
    have h1 : (((burnsideB46_pi π).comp (MulAut.conj c).toMonoidHom) g) =
        burnsideB46_pi π (c * g * c⁻¹) := rfl
    rw [h1, burnsideB46_f_act H, ← burnsideB46_p4_mul_apply, ← burnsideB46_p4_mul_apply,
      show c⁻¹ * (c * g * c⁻¹) = g * c⁻¹ by group]

theorem burnsideB46_p4_ofHyp_pre (H : burnsideB46_Hyp V n K G L π θ) (c : ↥(cayleyGroup K))
    (Y : Submodule K (Ix3 → K)) :
    (burnsideB46_p4_ofHyp H c).pre Y = burnsideB46_pre θ (gmapG c Y) := by
  ext v
  change g2Act c⁻¹ (burnsideB46_f θ v) ∈ Y ↔ burnsideB46_f θ v ∈ gmapG c Y
  rw [mem_gmapG]

end OfHyp

theorem burnsideB46_p4_tL_apply (s : K) (x : quasithinZorn K) :
    ((tL s : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x =
      longRootFn 0 2 s x := by
  change gAFun ((tv 0 2 (by decide) s : SL3 K) : Matrix (Fin 3) (Fin 3) K) x = _
  rw [gAFun]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    fin_cases i <;> simp [longRootFn, tv_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      transvection_entry, Pi.single_apply]
  · rw [adjugate_tv]
    funext i
    fin_cases i <;> simp [longRootFn, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      transvection_entry, Pi.single_apply] <;> ring

theorem burnsideB46_p4_cg_symm_coe (a : ↥(cayleyGroup K)) :
    ((burnsideB46_cg.symm a : ↥(quasithinG2 K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) =
      (a : quasithinZorn K ≃ₗ[K] quasithinZorn K) := by
  have := burnsideB46_cg_coe (burnsideB46_cg.symm a)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem burnsideB46_p4_isLongRootSub {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (c : ↥(cayleyGroup K)) :
    IsLongRootSub π ((burnsideB46_p4_Z0 K).map
      ((burnsideB46_pi π).comp (MulAut.conj c).toMonoidHom)) := by
  refine ⟨0, 2, by decide, burnsideB46_cg.symm c, fun ψ => ?_⟩
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨s, burnsideB46_cg.symm (tL s), fun x => ?_, ?_⟩
    · rw [burnsideB46_p4_cg_symm_coe]
      exact burnsideB46_p4_tL_apply s x
    · change burnsideB46_pi π (c * tL s * c⁻¹) = _
      simp only [burnsideB46_pi_apply, map_mul, map_inv]
  · rintro ⟨s, φ, hφ, rfl⟩
    have hφ' : φ = burnsideB46_cg.symm (tL s) := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [hφ x, burnsideB46_p4_cg_symm_coe, burnsideB46_p4_tL_apply]
    refine ⟨tL s, ⟨s, rfl⟩, ?_⟩
    change burnsideB46_pi π (c * tL s * c⁻¹) = _
    rw [hφ']
    simp only [burnsideB46_pi_apply, map_mul, map_inv]

theorem burnsideB46_p4_conjSubgroup_eq (c : ↥(cayleyGroup K)) (H : Subgroup ↥(cayleyGroup K)) :
    CFSG.CGT.Timmesfeld75.conjSubgroup c H = H.map (MulAut.conj c).toMonoidHom := by
  ext g
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, burnsideB46_p3_mem_map_conj]

theorem burnsideB46_p4_sylow_conj [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {S : Subgroup ↥(cayleyGroup K)} (hS : IsSylowTwoOf S ⊤) :
    ∃ c : ↥(cayleyGroup K), S = (U0 K).map (MulAut.conj c).toMonoidHom := by
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  have hSi : ¬ 2 ∣ S.index := by
    have h1 : ¬ 2 ∣ S.relIndex ⊤ := hS.2.2
    rwa [Subgroup.relIndex_top_right] at h1
  obtain ⟨c, hc⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow
    (IsPGroup.toSylow isPGroup_U0 (not_two_dvd_index_U0 hK hn)) (hS.2.1.toSylow hSi)
  refine ⟨c, ?_⟩
  rw [← burnsideB46_p4_conjSubgroup_eq]
  have h1 : ((IsPGroup.toSylow isPGroup_U0 (not_two_dvd_index_U0 hK hn) : Sylow 2 ↥(cayleyGroup K)) :
      Subgroup ↥(cayleyGroup K)) = U0 K := IsPGroup.toSylow_coe _ _
  have h2 : ((hS.2.1.toSylow hSi : Sylow 2 ↥(cayleyGroup K)) : Subgroup ↥(cayleyGroup K)) = S :=
    IsPGroup.toSylow_coe _ _
  rw [h1, h2] at hc
  exact hc.symm

namespace burnsideB46_p4_Coord

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} (C : burnsideB46_p4_Coord V K L)

theorem inf_normalizer_map (X : Subgroup ↥(cayleyGroup K)) :
    L ⊓ Subgroup.normalizer ((X.map C.Φ : Subgroup (MulAut V)) : Set (MulAut V)) =
      (Subgroup.normalizer (X : Set ↥(cayleyGroup K))).map C.Φ := by
  ext l
  constructor
  · rintro ⟨hl, hn⟩
    obtain ⟨g, rfl⟩ := (C.mem_L l).1 hl
    exact ⟨g, (burnsideB46_p3_mem_normalizer_map_iff C.inj).1 hn, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(C.mem_L _).2 ⟨g, rfl⟩, (burnsideB46_p3_mem_normalizer_map_iff C.inj).2 hg⟩

end burnsideB46_p4_Coord

theorem burnsideB46_p4_four_le {V : Type} [CommGroup V] {n : ℕ} {G L : Subgroup (MulAut V)}
    {π : ↥(quasithinG2 K) →* MulAut V} {θ : V →* Multiplicative (NatQ K)}
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) : 4 ≤ Nat.card K := by
  rw [H.card]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem burnsideB46_p4_cfg2 {V : Type} [CommGroup V] [Finite K] [Finite V] {n : ℕ}
    {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
    {θ : V →* Multiplicative (NatQ K)} (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {x : Ix3 → K} (hx : x ≠ 0)
    {P₁ T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hP₁ : P₁ = (burnsideB46_P1 K x).map (burnsideB46_pi π))
    (h : B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂) :
    ∃ c : ↥(cayleyGroup K), burnsideB46_pt K x = gmapG c (stdF K 1) ∧
      T ⊓ L = (U0 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      Z₂ = (burnsideB46_p4_Z0 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      P₂ = (stabQ (stdF K 2)).map (burnsideB46_p4_ofHyp H c).Φ ∧
      R₂ = (burnsideB46_p4_R2 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      V₂ = burnsideB46_pre θ (gmapG c (stdF K 2)) := by
  haveI : Finite (MulAut V) := Finite.of_injective (fun e : MulAut V => (e : V → V))
    (fun e e' h => MulEquiv.ext (congrFun h))
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  have h4 := burnsideB46_p4_four_le H hn
  have hnormLG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => burnsideB46_normal hqs H hn g hg l hl, fun h' => ?_⟩
    have := burnsideB46_normal hqs H hn g⁻¹ (G.inv_mem hg) _ h'
    simpa [mul_assoc] using this
  obtain ⟨hTG, hTLP₁, hZ₂, hP₂, hR₂, hV₂⟩ := h
  have hSyl : IsSylowTwoOf (T ⊓ L) L := B6.isSylowTwoOf_inf_normal hTG H.le hnormLG
  set S₀ : Subgroup ↥(cayleyGroup K) := (T ⊓ L).comap (burnsideB46_pi π) with hS₀def
  have hS₀map : S₀.map (burnsideB46_pi π) = T ⊓ L := by
    ext l
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hl
      obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 hl.2
      refine ⟨g, ?_, hg⟩
      show burnsideB46_pi π g ∈ T ⊓ L
      rw [hg]
      exact hl
  have hTop : (⊤ : Subgroup ↥(cayleyGroup K)).map (burnsideB46_pi π) = L := by
    ext l
    constructor
    · rintro ⟨g, -, rfl⟩
      exact burnsideB46_pi_mem_L H g
    · intro hl
      obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 hl
      exact ⟨g, trivial, hg⟩
  have hS₀ : IsSylowTwoOf S₀ ⊤ :=
    (burnsideB46_p3_isSylowTwoOf_map (burnsideB46_pi_injective H)).1 (by
      rw [hS₀map, hTop]
      exact hSyl)
  obtain ⟨c, hc⟩ := burnsideB46_p4_sylow_conj H.card (by omega) hS₀
  set C := burnsideB46_p4_ofHyp H c with hCdef
  have hT : T ⊓ L = (U0 K).map C.Φ := by
    rw [← hS₀map, hc, Subgroup.map_map]
    rfl
  have hS₀P : S₀ ≤ burnsideB46_P1 K x := by
    intro g hg
    have h1 : burnsideB46_pi π g ∈ P₁ := hTLP₁ hg
    rw [hP₁] at h1
    exact (Subgroup.mem_map_iff_mem (burnsideB46_pi_injective H)).1 h1
  have hpt : burnsideB46_pt K x = gmapG c (stdF K 1) := by
    have hstab : U0Stable (gmapG c⁻¹ (burnsideB46_pt K x)) := by
      intro g hg w hw
      rw [mem_gmapG] at hw ⊢
      have hmem : c * g * c⁻¹ ∈ burnsideB46_P1 K x := hS₀P (by rw [hc]; exact ⟨g, hg, rfl⟩)
      have h1 := (mem_stabQ.1 hmem (g2Act c w)).1 (by simpa using hw)
      rw [burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply, g2Act_inv_apply] at h1
      simpa using h1
    have hcard : Nat.card (gmapG c⁻¹ (burnsideB46_pt K x)) = Nat.card K ^ 1 := by
      rw [card_gmapG]
      have h1 : Nat.card (burnsideB46_pt K x) = Nat.card K ^ Module.finrank K (burnsideB46_pt K x) :=
        Module.natCard_eq_pow_finrank
      rw [h1, burnsideB46_pt, finrank_span_singleton hx]
    have h2 := eq_stdF_of_card hstab hcard
    rw [← h2, gmapG_gmapG_inv]
  have hZ : Z₂ = (burnsideB46_p4_Z0 K).map C.Φ := by
    rw [hZ₂, hT, burnsideB46_centerOf_map _ C.inj, ← burnsideB46_p4_center_U0]
  have hP : P₂ = (stabQ (stdF K 2)).map C.Φ := by
    rw [hP₂, hZ, C.inf_normalizer_map, burnsideB46_p4_normalizer_Z0]
  have hR : R₂ = (burnsideB46_p4_R2 K).map C.Φ := by
    rw [hR₂, hP, burnsideB46_pCoreOf_map _ C.inj, burnsideB46_p4_pCore_P2 h4]
  refine ⟨c, hpt, hT, hZ, hP, hR, ?_⟩
  rw [hV₂, hR, C.cPre_map, burnsideB46_p4_fixSub_R2, hCdef, burnsideB46_p4_ofHyp_pre]

theorem burnsideB46_p4_frattini_map_mulEquiv {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂) :
    (frattini H₁).map e.toMonoidHom = frattini H₂ :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem burnsideB46_p4_isSpecial2_map {M N : Type} [Group M] [Group N] {φ : M →* N}
    (hφ : Function.Injective φ) {R Z : Subgroup M} (h : IsSpecial2 R Z) :
    IsSpecial2 (R.map φ) (Z.map φ) := by
  obtain ⟨hp, hc, hcomm, hfr, hne⟩ := h
  let e : ↥R ≃* ↥(R.map φ) := R.equivMapOfInjective φ hφ
  refine ⟨hp.of_equiv e, ?_, ?_, ?_, ?_⟩
  · rw [burnsideB46_centerOf_map φ hφ, hc]
  · rw [← Subgroup.map_commutator, hcomm]
  · have h1 := burnsideB46_p4_frattini_map_mulEquiv e
    have h2 : (R.map φ).subtype.comp e.toMonoidHom = φ.comp R.subtype := by
      ext x
      rfl
    rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map, hfr]
  · intro h0
    apply hne
    apply Subgroup.map_injective hφ
    rw [h0, Subgroup.map_bot]

theorem burnsideB46_p4_Z0_elemAbelian : IsElemAbelian 2 (burnsideB46_p4_Z0 K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨t, ht⟩ := b.2
    apply Subtype.ext
    change (a : ↥(cayleyGroup K)) * b = b * a
    rw [hs, ht, tL_mul, tL_mul, add_comm]
  · rintro _ ⟨s, rfl⟩
    rw [pow_two]
    exact tL_mul_self s

theorem burnsideB46_p4_U0_sylow [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    IsSylowTwoOf (U0 K) ⊤ := by
  refine ⟨le_top, isPGroup_U0, ?_⟩
  change ¬ 2 ∣ (U0 K).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact not_two_dvd_index_U0 hK hn

theorem burnsideB46_p4_normalizer_center_U0 :
    Subgroup.normalizer ((centerOf (U0 K) : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) =
      stabQ (stdF K 2) := by
  rw [burnsideB46_p4_center_U0, burnsideB46_p4_normalizer_Z0]

theorem burnsideB46_p4_stabQ_two_ne_one : stabQ (stdF K 2) ≠ stabQ (stdF K 1) := by
  intro h
  have h1 : g2X ![(0 : K), 1, 0] ∈ stabQ (stdF K 2) :=
    sl2E1_le_stabQ (Subgroup.subset_closure ⟨1, Or.inl rfl⟩)
  rw [h] at h1
  have h2 := (mem_stabQ.1 h1 (q6 1 0 0 0 0 0)).1 (by
    rw [mem_stdF_one_iff]
    exact ⟨1, by
      funext k
      rcases k with k | k <;> fin_cases k <;> simp [q6]⟩)
  rw [g2Act_x1q] at h2
  rw [mem_stdF_one_iff] at h2
  obtain ⟨t, ht⟩ := h2
  have := congrFun ht (.inr 2)
  simp [q6] at this

namespace burnsideB46_p4_Coord

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} (C : burnsideB46_p4_Coord V K L)

theorem map_top : (⊤ : Subgroup ↥(cayleyGroup K)).map C.Φ = L := by
  ext l
  constructor
  · rintro ⟨g, -, rfl⟩
    exact (C.mem_L _).2 ⟨g, rfl⟩
  · intro hl
    obtain ⟨g, hg⟩ := (C.mem_L l).1 hl
    exact ⟨g, trivial, hg⟩

end burnsideB46_p4_Coord

end P4a

section P4b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_4 (hqs : burnsideB46_G2Qs)
    (hmax2 : ∀ S : Subgroup ↥(cayleyGroup K), IsSylowTwoOf S ⊤ →
      IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K))
        (Subgroup.normalizer ((centerOf S : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K))))
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have h4 := burnsideB46_p4_four_le H hn
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2
  obtain ⟨x, hx0, hV₁, hP₁, hR₁, hZ₁, hV₃⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, hZ, hP, hR, hV⟩ := burnsideB46_p4_cfg2 hqs H hn hx0 hP₁ hcfg2
  set C := burnsideB46_p4_ofHyp H c with hC
  have hV' : V₂ = C.pre (stdF K 2) := hV.trans (burnsideB46_p4_ofHyp_pre H c _).symm
  have hmaxstd : IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2)) := by
    have := hmax2 (U0 K) (burnsideB46_p4_U0_sylow H.card (by omega))
    rwa [burnsideB46_p4_normalizer_center_U0] at this
  have hP₁' : P₁ = (stabQ (stdF K 1)).map C.Φ := by
    rw [hP₁, burnsideB46_P1, hpt, burnsideB46_p3_stabQ_gmapG, Subgroup.map_map]
    rfl
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hZ]
    exact burnsideB46_p3_isElemAbelian_map burnsideB46_p4_Z0_elemAbelian
  · rw [hZ, Subgroup.card_map_of_injective C.inj, burnsideB46_p4_card_Z0]
  · rw [hZ]
    exact burnsideB46_p4_isLongRootSub π c
  · have h1 := burnsideB46_p3_isMaxParabolic2_map C.inj hmaxstd
    rw [C.map_top] at h1
    rw [hP]
    exact h1
  · rw [hT, hP]
    exact Subgroup.map_mono burnsideB46_p4_U0_le_stabQ_two
  · rw [hP, hP₁']
    intro h
    exact burnsideB46_p4_stabQ_two_ne_one (Subgroup.map_injective C.inj h)
  · rw [hZ, hR]
    exact burnsideB46_p4_isSpecial2_map C.inj burnsideB46_p4_R2_special
  · rw [hR, Subgroup.card_map_of_injective C.inj, burnsideB46_p4_card_R2]
  · rw [hP, hR, hV']
    exact C.natMod (burnsideB46_p4_natMod_std h4)
  · intro z hz hz1
    rw [hZ] at hz
    obtain ⟨g0, hg0, rfl⟩ := hz
    obtain ⟨s, rfl⟩ := hg0
    have hs : s ≠ 0 := by
      rintro rfl
      exact hz1 (by rw [tL_zero, map_one])
    rw [hV']
    exact (C.comm_pre (g0 := tL s) (X := burnsideB46_p4_Z0 K) (Y := stdF K 2) ⟨s, rfl⟩
      (by
        rintro _ ⟨t, rfl⟩ w
        exact g2Act_tL_sub_mem t w)
      (fun y hy => exists_tL_sub_eq hs hy)).symm
  · intro z hz hz1
    rw [hZ] at hz
    obtain ⟨g0, hg0, rfl⟩ := hz
    have hg01 : g0 ≠ 1 := fun h => hz1 (by rw [h, map_one])
    have hfix : cPre (fixV L) (burnsideB46_p4_Z0 K |>.map C.Φ) = C.pre (stdF K 4) := by
      rw [C.cPre_map, burnsideB46_p4_fixSub_Z0]
    refine ⟨?_, ?_⟩
    · rw [hZ, hfix, ← MonoidHom.map_zpowers, C.cPre_map,
        burnsideB46_p4_fixSub_zpowers hg0 hg01]
    · rw [hZ, hfix]
      refine burnsideB46_isFPre_iff.2 ⟨gmapG c (stdF K 4), ?_, ?_⟩
      · rw [burnsideB46_p3_finrank_gmapG, burnsideB46_p4_finrank_stdF (by norm_num)]
      · rw [← burnsideB46_p4_ofHyp_pre H c]

end P4b

section P4c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

@[expose] def burnsideB46_p4_Y (K : Type) [Field K] (e f : K) : Submodule K (Ix3 → K) where
  carrier := {w | w (.inl 1) = 0 ∧ w (.inl 2) = 0 ∧ w (.inr 0) = 0 ∧
    f * w (.inr 1) = e * w (.inr 2)}
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨by simp [a1, b1], by simp [a2, b2], by simp [a3, b3], ?_⟩
    simp only [Pi.add_apply]
    linear_combination a4 + b4
  zero_mem' := ⟨rfl, rfl, rfl, by simp⟩
  smul_mem' := by
    rintro t a ⟨a1, a2, a3, a4⟩
    refine ⟨by simp [a1], by simp [a2], by simp [a3], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination t * a4

theorem burnsideB46_p4_mem_Y {e f : K} {w : Ix3 → K} :
    w ∈ burnsideB46_p4_Y K e f ↔ w (.inl 1) = 0 ∧ w (.inl 2) = 0 ∧ w (.inr 0) = 0 ∧
      f * w (.inr 1) = e * w (.inr 2) := Iff.rfl

theorem burnsideB46_p4_F1_le_Y (e f : K) : stdF K 1 ≤ burnsideB46_p4_Y K e f := by
  intro w hw
  obtain ⟨t, rfl⟩ := mem_stdF_one_iff.1 hw
  refine ⟨by simp [eu], by simp [eu], by simp [eu], by simp [eu]⟩

theorem burnsideB46_p4_Y_le_F3 (e f : K) : burnsideB46_p4_Y K e f ≤ stdF K 3 := fun w hw =>
  mem_stdF_three.2 ⟨hw.1, hw.2.1, hw.2.2.1⟩

theorem burnsideB46_p4_mem_F1_of {w : Ix3 → K} (h1 : w (.inl 1) = 0) (h2 : w (.inl 2) = 0)
    (h3 : w (.inr 0) = 0) (h4 : w (.inr 1) = 0) (h5 : w (.inr 2) = 0) : w ∈ stdF K 1 := by
  rw [mem_stdF, q6_eta w, inF_q6_iff]
  exact ⟨fun h => absurd h (by norm_num), fun _ => h1, fun _ => h2, fun _ => h3, fun _ => h4,
    fun _ => h5⟩

theorem burnsideB46_p4_Y_inf {e f e' f' : K} (h : e * f' ≠ e' * f) :
    burnsideB46_p4_Y K e f ⊓ burnsideB46_p4_Y K e' f' = stdF K 1 := by
  apply le_antisymm
  · rintro w ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
    have h2 : w (.inr 2) = 0 := by
      have : (e * f' - e' * f) * w (.inr 2) = 0 := by linear_combination (-f') * a4 + f * b4
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h)
    have h1 : w (.inr 1) = 0 := by
      rw [h2, mul_zero] at a4 b4
      by_cases hf : f = 0
      · have hf' : f' ≠ 0 := by
          rintro rfl
          exact h (by rw [hf]; ring)
        exact (mul_eq_zero.1 b4).resolve_left hf'
      · exact (mul_eq_zero.1 a4).resolve_left hf
    exact burnsideB46_p4_mem_F1_of a1 a2 a3 h1 h2
  · exact le_inf (burnsideB46_p4_F1_le_Y e f) (burnsideB46_p4_F1_le_Y e' f')

@[expose] def burnsideB46_p4_Psi (K : Type) [Field K] : Option K → Submodule K (Ix3 → K)
  | none => burnsideB46_p4_Y K 1 0
  | some s => burnsideB46_p4_Y K s 1

theorem burnsideB46_p4_Psi_injective : Function.Injective (burnsideB46_p4_Psi K) := by
  intro o o' h
  rcases o with _ | s <;> rcases o' with _ | s'
  · rfl
  · exfalso
    have h' : burnsideB46_p4_Y K 1 0 = burnsideB46_p4_Y K s' 1 := h
    have hv : q6 (0 : K) 0 0 0 1 0 ∈ burnsideB46_p4_Y K 1 0 := ⟨rfl, rfl, rfl, by simp [q6]⟩
    rw [h'] at hv
    obtain ⟨-, -, -, h4⟩ := hv
    simp [q6] at h4
  · exfalso
    have h' : burnsideB46_p4_Y K s 1 = burnsideB46_p4_Y K 1 0 := h
    have hv : q6 (0 : K) 0 0 0 1 0 ∈ burnsideB46_p4_Y K 1 0 := ⟨rfl, rfl, rfl, by simp [q6]⟩
    rw [← h'] at hv
    obtain ⟨-, -, -, h4⟩ := hv
    simp [q6] at h4
  · have h' : burnsideB46_p4_Y K s 1 = burnsideB46_p4_Y K s' 1 := h
    have hv : q6 (0 : K) 0 0 0 s 1 ∈ burnsideB46_p4_Y K s 1 := ⟨rfl, rfl, rfl, by simp [q6]⟩
    rw [h'] at hv
    obtain ⟨-, -, -, h4⟩ := hv
    simp [q6] at h4
    rw [h4]

theorem burnsideB46_p4_Psi_le (o : Option K) :
    stdF K 1 ≤ burnsideB46_p4_Psi K o ∧ burnsideB46_p4_Psi K o ≤ stdF K 3 := by
  rcases o with _ | s
  · exact ⟨burnsideB46_p4_F1_le_Y _ _, burnsideB46_p4_Y_le_F3 _ _⟩
  · exact ⟨burnsideB46_p4_F1_le_Y _ _, burnsideB46_p4_Y_le_F3 _ _⟩

theorem burnsideB46_p4_Psi_inf {o o' : Option K} (h : o ≠ o') :
    burnsideB46_p4_Psi K o ⊓ burnsideB46_p4_Psi K o' = stdF K 1 := by
  rcases o with _ | s <;> rcases o' with _ | s'
  · exact absurd rfl h
  · exact burnsideB46_p4_Y_inf (by simp)
  · exact burnsideB46_p4_Y_inf (by simp)
  · refine burnsideB46_p4_Y_inf (fun h' => h ?_)
    simp at h'
    rw [h']

theorem burnsideB46_p4_Psi_cover {w : Ix3 → K} (hw : w ∈ stdF K 3) :
    ∃ o : Option K, w ∈ burnsideB46_p4_Psi K o := by
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.1 hw
  by_cases hf : w (.inr 2) = 0
  · exact ⟨none, h1, h2, h3, by simp [hf]⟩
  · refine ⟨some (w (.inr 1) / w (.inr 2)), h1, h2, h3, ?_⟩
    simp only [one_mul]
    field_simp

theorem burnsideB46_p4_exists_prop {e f w1 w2 : K} (hef : e ≠ 0 ∨ f ≠ 0)
    (h : f * w1 = e * w2) : ∃ β : K, β * e = w1 ∧ β * f = w2 := by
  by_cases hf : f = 0
  · have he : e ≠ 0 := hef.resolve_right (not_not.2 hf)
    have h2 : w2 = 0 := by
      rw [hf, zero_mul] at h
      exact (mul_eq_zero.1 h.symm).resolve_left he
    refine ⟨w1 / e, by field_simp, ?_⟩
    rw [h2, hf]
    simp
  · refine ⟨w2 / f, ?_, by field_simp⟩
    field_simp
    linear_combination (-1 : K) * h

theorem burnsideB46_p4_gv2 {g : ↥(cayleyGroup K)} (hg : g ∈ stabQ (stdF K 1)) :
    ∃ a e f : K, (e ≠ 0 ∨ f ≠ 0) ∧ g2Act g (q6 0 0 0 0 0 1) = q6 a 0 0 0 e f := by
  have hg3 : g ∈ stabQ (stdF K 3) := (stabQ_one_eq_three (F := K)).le hg
  have h1 : g2Act g (q6 0 0 0 0 0 1) ∈ stdF K 3 :=
    (mem_stabQ.1 hg3 _).1 (mem_stdF_three.2 ⟨rfl, rfl, rfl⟩)
  obtain ⟨a, b, c, d, e, f, hv⟩ := burnsideB46_p4_q6_exists (g2Act g (q6 0 0 0 0 0 1))
  rw [hv, mem_stdF_three] at h1
  obtain ⟨hb, hc, hd⟩ := h1
  have hb' : b = 0 := hb
  have hc' : c = 0 := hc
  have hd' : d = 0 := hd
  refine ⟨a, e, f, ?_, by rw [hv, hb', hc', hd']⟩
  by_contra hne
  push Not at hne
  have h2 : g2Act g (q6 0 0 0 0 0 1) ∈ stdF K 1 := by
    rw [hv, hb', hc', hd', hne.1, hne.2]
    exact mem_stdF_one_iff.2 ⟨a, by funext k; rcases k with k | k <;> fin_cases k <;> simp [q6, eu]⟩
  have h3 := (mem_stabQ.1 hg _).2 h2
  obtain ⟨t, ht⟩ := mem_stdF_one_iff.1 h3
  have := congrFun ht (.inr 2)
  simp [eu, q6] at this

theorem burnsideB46_p4_gmapG_two {g : ↥(cayleyGroup K)} (hg : g ∈ stabQ (stdF K 1)) {a e f : K}
    (hef : e ≠ 0 ∨ f ≠ 0) (hv : g2Act g (q6 0 0 0 0 0 1) = q6 a 0 0 0 e f) :
    gmapG g (stdF K 2) = burnsideB46_p4_Y K e f := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hg
  have hu : g2Act g (q6 1 0 0 0 0 0) = q6 c 0 0 0 0 0 := by
    rw [← eu_eq_q6, hc]
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [q6, eu]
  have hgen : ∀ α β : K, g2Act g (q6 α 0 0 0 0 β) = q6 (α * c + β * a) 0 0 0 (β * e) (β * f) := by
    intro α β
    rw [q6_F2_decomp, map_add, burnsideB46_p4_smul, burnsideB46_p4_smul, hu, hv, q6_smul,
      q6_smul, q6_add]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  ext w
  rw [mem_gmapG]
  constructor
  · intro hw
    have hw' := burnsideB46_p4_F2_eq hw
    have hw2 : w = q6 (g2Act g⁻¹ w (.inl 0) * c + g2Act g⁻¹ w (.inr 2) * a) 0 0 0
        (g2Act g⁻¹ w (.inr 2) * e) (g2Act g⁻¹ w (.inr 2) * f) := by
      rw [← hgen, ← hw', g2Act_apply_inv]
    rw [hw2]
    exact ⟨rfl, rfl, rfl, by simp only [q6_apply_inr1, q6_apply_inr2]; ring⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨β, hβ1, hβ2⟩ := burnsideB46_p4_exists_prop hef h4
    set α : K := (w (.inl 0) - β * a) / c with hα
    have hw2 : g2Act g (q6 α 0 0 0 0 β) = w := by
      rw [hgen, q6_eta w, h1, h2, h3, ← hβ1, ← hβ2]
      refine q6_congr ?_ rfl rfl rfl rfl rfl
      rw [hα]
      field_simp
      ring
    have : g2Act g⁻¹ w = q6 α 0 0 0 0 β := by
      rw [← hw2, g2Act_inv_apply]
    rw [this]
    exact burnsideB46_p4_F2_of

theorem burnsideB46_p4_exists_g (e f : K) (hef : e ≠ 0 ∨ f ≠ 0) :
    ∃ g ∈ stabQ (stdF K 1), ∃ a, g2Act g (q6 0 0 0 0 0 1) = q6 a 0 0 0 e f := by
  obtain ⟨A, hA, hA21, hA11⟩ : ∃ A : SL3 K,
      Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) K) ![1, 0, 0] = ![1, 0, 0] ∧
      (A : Matrix (Fin 3) (Fin 3) K) 2 1 = e ∧ (A : Matrix (Fin 3) (Fin 3) K) 1 1 = f := by
    by_cases hf : f = 0
    · have he : e ≠ 0 := hef.resolve_right (not_not.2 hf)
      refine ⟨⟨!![1, 0, 0; 0, 0, e⁻¹; 0, e, 0], ?_⟩, ?_, ?_, ?_⟩
      · simp [Matrix.det_fin_three, he, CharTwo.neg_eq]
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · rfl
      · simpa using hf.symm
    · refine ⟨⟨!![1, 0, 0; 0, f, 0; 0, e, f⁻¹], ?_⟩, ?_, ?_, ?_⟩
      · simp [Matrix.det_fin_three, hf]
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · rfl
      · rfl
  have hg : g2A A ∈ stabV0 K := g2A_mem_stabV0 hA
  have hw3 : q6 (0 : K) 0 0 0 0 1 ∈ stdF K 3 := mem_stdF_three.2 ⟨rfl, rfl, rfl⟩
  have hvp := vpart_act hg hw3
  rw [levi1Mat_g2A hA] at hvp
  have hF3 := mapsF3_of_mem hg _ hw3
  obtain ⟨hb, hc, hd⟩ := mem_stdF_three.1 hF3
  have e1 := congrFun hvp 0
  have e2 := congrFun hvp 1
  simp [vpart, Matrix.mulVec, dotProduct, Fin.sum_univ_two, q6, hA21, hA11] at e1 e2
  refine ⟨g2A A, stabV0_le_stabQ hg, (g2Act (g2A A) (q6 0 0 0 0 0 1)) (.inl 0), ?_⟩
  have e1' : (g2Act (g2A A) (q6 0 0 0 0 0 1)) (.inr 1) = e := e1
  have e2' : (g2Act (g2A A) (q6 0 0 0 0 0 1)) (.inr 2) = f := e2
  conv_lhs => rw [q6_eta (g2Act (g2A A) (q6 0 0 0 0 0 1))]
  rw [hb, hc, hd, e1', e2']

theorem burnsideB46_p4_Y_eq_some {e f : K} (hf : f ≠ 0) :
    burnsideB46_p4_Y K e f = burnsideB46_p4_Y K (e / f) 1 := by
  ext w
  rw [burnsideB46_p4_mem_Y, burnsideB46_p4_mem_Y]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  rw [one_mul, div_mul_eq_mul_div, eq_div_iff hf]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

theorem burnsideB46_p4_Y_eq_none {e : K} (he : e ≠ 0) :
    burnsideB46_p4_Y K e 0 = burnsideB46_p4_Y K 1 0 := by
  ext w
  rw [burnsideB46_p4_mem_Y, burnsideB46_p4_mem_Y]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  simp only [zero_mul, one_mul]
  constructor
  · intro h
    exact ((mul_eq_zero.1 h.symm).resolve_left he).symm
  · intro h
    rw [← h, mul_zero]

theorem burnsideB46_p4_planes_eq :
    {Y : Submodule K (Ix3 → K) | ∃ g ∈ stabQ (stdF K 1), Y = gmapG g (stdF K 2)} =
      Set.range (burnsideB46_p4_Psi K) := by
  ext Y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, e, f, hef, hv⟩ := burnsideB46_p4_gv2 hg
    rw [burnsideB46_p4_gmapG_two hg hef hv]
    by_cases hf : f = 0
    · have he : e ≠ 0 := hef.resolve_right (not_not.2 hf)
      refine ⟨none, ?_⟩
      rw [hf]
      exact (burnsideB46_p4_Y_eq_none he).symm
    · exact ⟨some (e / f), (burnsideB46_p4_Y_eq_some hf).symm⟩
  · rintro ⟨o, rfl⟩
    rcases o with _ | s
    · obtain ⟨g, hg, a, hv⟩ := burnsideB46_p4_exists_g (1 : K) 0 (Or.inl one_ne_zero)
      exact ⟨g, hg, (burnsideB46_p4_gmapG_two hg (Or.inl one_ne_zero) hv).symm⟩
    · obtain ⟨g, hg, a, hv⟩ := burnsideB46_p4_exists_g s 1 (Or.inr one_ne_zero)
      exact ⟨g, hg, (burnsideB46_p4_gmapG_two hg (Or.inr one_ne_zero) hv).symm⟩

end P4c

section P4d

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_10 (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2
  obtain ⟨x, hx0, hV₁, hP₁, hR₁, hZ₁, hV₃⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, hZ, hP, hR, hV⟩ := burnsideB46_p4_cfg2 hqs H hn hx0 hP₁ hcfg2
  set C := burnsideB46_p4_ofHyp H c with hC
  have hF3 : burnsideB46_F3 K x = gmapG c (stdF K 3) := by
    have h1 : burnsideB46_pt K x = burnsideB46_pt K (g2Act c (eu 0 1)) := by
      rw [hpt, burnsideB46_p3_pt_act, burnsideB46_p3_pt_eu]
    have h2 : burnsideB46_F3 K x = burnsideB46_F3 K (g2Act c (eu 0 1)) := by
      simp only [burnsideB46_F3, burnsideB46_Z1, burnsideB46_R1, burnsideB46_P1, h1]
    rw [h2, burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu]
  have hV₁' : V₁ = C.pre (stdF K 1) := by
    rw [hV₁, hpt]
    exact (burnsideB46_p4_ofHyp_pre H c _).symm
  have hV₃' : V₃ = C.pre (stdF K 3) := by
    rw [hV₃, hF3]
    exact (burnsideB46_p4_ofHyp_pre H c _).symm
  have hV' : V₂ = C.pre (stdF K 2) := hV.trans (burnsideB46_p4_ofHyp_pre H c _).symm
  have hP₁' : P₁ = (stabQ (stdF K 1)).map C.Φ := by
    rw [hP₁, burnsideB46_P1, hpt, burnsideB46_p3_stabQ_gmapG, Subgroup.map_map]
    rfl
  have hmap : ∀ g ∈ stabQ (stdF K 1),
      V₂.map (C.Φ g : MulAut V).toMonoidHom = C.pre (gmapG g (stdF K 2)) := by
    intro g _
    rw [hV', C.map_pre]
  have hplane : ∀ g ∈ stabQ (stdF K 1), ∃ o : Option K, gmapG g (stdF K 2) = burnsideB46_p4_Psi K o := by
    intro g hg
    have : gmapG g (stdF K 2) ∈ Set.range (burnsideB46_p4_Psi K) := by
      rw [← burnsideB46_p4_planes_eq]
      exact ⟨g, hg, rfl⟩
    obtain ⟨o, ho⟩ := this
    exact ⟨o, ho.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} =
        C.pre '' Set.range (burnsideB46_p4_Psi K) := by
      ext X
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [hP₁'] at hp
        obtain ⟨g, hg, rfl⟩ := hp
        obtain ⟨o, ho⟩ := hplane g hg
        exact ⟨burnsideB46_p4_Psi K o, ⟨o, rfl⟩, by rw [hmap g hg, ho]⟩
      · rintro ⟨_, ⟨o, rfl⟩, rfl⟩
        have : burnsideB46_p4_Psi K o ∈
            {Y : Submodule K (Ix3 → K) | ∃ g ∈ stabQ (stdF K 1), Y = gmapG g (stdF K 2)} := by
          rw [burnsideB46_p4_planes_eq]
          exact ⟨o, rfl⟩
        obtain ⟨g, hg, hgo⟩ := this
        refine ⟨C.Φ g, ?_, ?_⟩
        · rw [hP₁']
          exact ⟨g, hg, rfl⟩
        · rw [hmap g hg, hgo]
    rw [hset, Set.ncard_image_of_injective _ (fun Y Y' h => C.pre_injective h),
      Set.ncard_range_of_injective burnsideB46_p4_Psi_injective, Finite.card_option]
  · intro p hp
    rw [hP₁'] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨o, ho⟩ := hplane g hg
    rw [hmap g hg, ho, hV₁', hV₃']
    exact ⟨C.pre_le_pre_iff.2 (burnsideB46_p4_Psi_le o).1,
      C.pre_le_pre_iff.2 (burnsideB46_p4_Psi_le o).2⟩
  · intro p hp p' hp' hne
    rw [hP₁'] at hp hp'
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨g', hg', rfl⟩ := hp'
    obtain ⟨o, ho⟩ := hplane g hg
    obtain ⟨o', ho'⟩ := hplane g' hg'
    rw [hmap g hg, ho, hmap g' hg', ho'] at hne ⊢
    have hoo : o ≠ o' := fun h => hne (by rw [h])
    rw [hV₁', C.pre_inf, burnsideB46_p4_Psi_inf hoo]
  · intro v hv
    rw [hV₃'] at hv
    obtain ⟨o, ho⟩ := burnsideB46_p4_Psi_cover (show C.f v ∈ stdF K 3 from hv)
    have : burnsideB46_p4_Psi K o ∈
        {Y : Submodule K (Ix3 → K) | ∃ g ∈ stabQ (stdF K 1), Y = gmapG g (stdF K 2)} := by
      rw [burnsideB46_p4_planes_eq]
      exact ⟨o, rfl⟩
    obtain ⟨g, hg, hgo⟩ := this
    refine ⟨C.Φ g, ?_, ?_⟩
    · rw [hP₁']
      exact ⟨g, hg, rfl⟩
    · rw [hmap g hg, ← hgo]
      exact ho

end P4d

section P4e

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p4_normalizer_U0_le :
    Subgroup.normalizer ((U0 K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) ≤
      stabQ (stdF K 2) := by
  have hz : ∀ γ ∈ Subgroup.normalizer ((U0 K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)),
      ∀ z ∈ burnsideB46_p4_Z0 K, γ * z * γ⁻¹ ∈ burnsideB46_p4_Z0 K := by
    intro γ hγ z hz
    rw [← burnsideB46_p4_center_U0] at hz ⊢
    obtain ⟨hzU, hzc⟩ := hz
    have hn := Subgroup.mem_normalizer_iff.1 hγ
    refine ⟨(hn z).1 hzU, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have hu' : γ⁻¹ * u * γ ∈ U0 K := by
      have := (hn (γ⁻¹ * u * γ)).1
      have h2 : γ * (γ⁻¹ * u * γ) * γ⁻¹ = u := by group
      rw [← h2] at hu
      exact (hn _).2 hu
    have hc := Subgroup.mem_centralizer_iff.1 hzc (γ⁻¹ * u * γ) hu'
    calc u * (γ * z * γ⁻¹) = γ * ((γ⁻¹ * u * γ) * z) * γ⁻¹ := by group
      _ = γ * (z * (γ⁻¹ * u * γ)) * γ⁻¹ := by rw [hc]
      _ = (γ * z * γ⁻¹) * u := by group
  intro g hg
  rw [← burnsideB46_p4_normalizer_Z0, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hz g hg h, fun hh => ?_⟩
  have := hz g⁻¹ (Subgroup.inv_mem _ hg) _ hh
  simpa [mul_assoc] using this

theorem burnsideB46_p4_stabQ_two_ne_top : stabQ (stdF K 2) ≠ ⊤ := by
  intro h
  have h1 : g2X ![(0 : K), 0, 1] ∈ stabQ (stdF K 2) := by
    rw [h]
    exact Subgroup.mem_top _
  have h2 := (mem_stabQ.1 h1 (q6 1 0 0 0 0 0)).1 (burnsideB46_p4_F2_of)
  rw [g2Act_x2q, burnsideB46_p4_F2_q6] at h2
  obtain ⟨-, -, -, h5⟩ := h2
  simp at h5

theorem burnsideB46_p4_isParabolic2 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    IsParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2)) :=
  ⟨le_top, U0 K, burnsideB46_p4_U0_sylow hK hn, fun g hg => burnsideB46_p4_normalizer_U0_le hg.2⟩

theorem burnsideB46_p4_isMaxParabolic2_of_coatom [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n)
    (hco : ∀ Q : Subgroup ↥(cayleyGroup K), stabQ (stdF K 2) ≤ Q → Q ≠ ⊤ → Q = stabQ (stdF K 2)) :
    IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2)) :=
  ⟨burnsideB46_p4_isParabolic2 hK hn, burnsideB46_p4_stabQ_two_ne_top,
    fun Q _ hQ hle => hco Q hle hQ⟩

theorem burnsideB46_p4_hmax2_of_std [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (h : IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2))) :
    ∀ S : Subgroup ↥(cayleyGroup K), IsSylowTwoOf S ⊤ →
      IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K))
        (Subgroup.normalizer ((centerOf S : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K))) := by
  intro S hS
  obtain ⟨c, rfl⟩ := burnsideB46_p4_sylow_conj hK hn hS
  have hκ : Function.Bijective (MulAut.conj c).toMonoidHom := (MulAut.conj c).bijective
  have h1 := burnsideB46_p3_isMaxParabolic2_map (φ := (MulAut.conj c).toMonoidHom)
    hκ.1 h
  rw [Subgroup.map_top_of_surjective _ hκ.2] at h1
  rw [burnsideB46_centerOf_map _ hκ.1, burnsideB46_p4_center_U0,
    ← Subgroup.map_normalizer_eq_of_bijective _ hκ, burnsideB46_p4_normalizer_Z0]
  exact h1

theorem burnsideB46_p4_isMaxParabolic2_pi {V : Type} [CommGroup V] {n : ℕ}
    {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
    {θ : V →* Multiplicative (NatQ K)} (H : burnsideB46_Hyp V n K G L π θ)
    {P : Subgroup ↥(cayleyGroup K)} (h : IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) P) :
    IsMaxParabolic2 L (P.map (burnsideB46_pi π)) := by
  have h1 := burnsideB46_p3_isMaxParabolic2_map (burnsideB46_pi_injective H) h
  have hTop : (⊤ : Subgroup ↥(cayleyGroup K)).map (burnsideB46_pi π) = L := by
    ext l
    constructor
    · rintro ⟨g, -, rfl⟩
      exact burnsideB46_pi_mem_L H g
    · intro hl
      obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 hl
      exact ⟨g, trivial, hg⟩
  rwa [hTop] at h1

end P4e

section P4n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p4_n1_SL_le_range :
    ((burnsideB46_p4_levi2GL K).range).comap
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_range]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine ⟨⟨g2Y ![0, t, 0], sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inr rfl⟩)⟩,
      Units.ext ?_⟩
    rw [burnsideB46_p4_levi2GL_coe]
    show levi2Mat (g2Y ![0, t, 0]) = _
    rw [levi2Mat_y1]
    change _ = ((Matrix.SpecialLinearGroup.transvection hij t :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [CFSG.LinearGroups.coe_transvection]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · refine ⟨⟨g2X ![0, t, 0], sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inl rfl⟩)⟩,
      Units.ext ?_⟩
    rw [burnsideB46_p4_levi2GL_coe]
    show levi2Mat (g2X ![0, t, 0]) = _
    rw [levi2Mat_x1]
    change _ = ((Matrix.SpecialLinearGroup.transvection hij t :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    rw [CFSG.LinearGroups.coe_transvection]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · exact absurd rfl hij

theorem burnsideB46_p4_n1_levi2GL_surjective :
    Function.Surjective (burnsideB46_p4_levi2GL K) := by
  intro M
  set d : Kˣ := Matrix.GeneralLinearGroup.det M with hd
  have hdet : Matrix.GeneralLinearGroup.det (M * (burnsideB46_p4_dg d)⁻¹) = 1 := by
    rw [map_mul, map_inv, burnsideB46_p4_det_dg, ← hd, mul_inv_cancel]
  have hdetM : ((M * (burnsideB46_p4_dg d)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  let A : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨((M * (burnsideB46_p4_dg d)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), hdetM⟩
  have hAmem : A ∈ ((burnsideB46_p4_levi2GL K).range).comap
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K) := by
    rw [burnsideB46_p4_n1_SL_le_range]
    trivial
  obtain ⟨g₁, hg₁⟩ := hAmem
  have hg₂s : g2T (1, d) ∈ stabQ (stdF K 2) := g2T_mem_stabQ _ 2
  have hA : (Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) = M * (burnsideB46_p4_dg d)⁻¹ :=
    Units.ext rfl
  have h2 : burnsideB46_p4_levi2GL K ⟨g2T (1, d), hg₂s⟩ = burnsideB46_p4_dg d := by
    apply Units.ext
    rw [burnsideB46_p4_levi2GL_coe]
    show levi2Mat (g2T (1, d)) = _
    rw [levi2Mat_g2T]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [burnsideB46_p4_dg]
  refine ⟨g₁ * ⟨g2T (1, d), hg₂s⟩, ?_⟩
  rw [map_mul, hg₁, hA, h2, inv_mul_cancel_right]

theorem burnsideB46_p4_n1_pCore_P2 [Finite K] :
    pCoreOf 2 (stabQ (stdF K 2)) = burnsideB46_p4_R2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  haveI : Finite ↥(stabQ (stdF K 2)) := Subtype.finite
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hbot := burnsideB46_p4_GL2_pCore (N := (CFSG.pCore 2 ↥(stabQ (stdF K 2))).map
      (burnsideB46_p4_levi2GL K))
      (hN := (CFSG.LieType.BorelTits.pCore_normal 2).map _
        burnsideB46_p4_n1_levi2GL_surjective)
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥(stabQ (stdF K 2)))).map
        (burnsideB46_p4_levi2GL K))
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hy' : y ∈ (burnsideB46_p4_levi2GL K).ker := hbot hy
    rw [burnsideB46_p4_ker_levi2GL, Subgroup.mem_subgroupOf] at hy'
    exact hy'
  · apply CFSG.LieType.BorelTits.le_pCoreOf 2 burnsideB46_p4_R2_le_stabQ
    · rw [← burnsideB46_p4_ker_levi2GL]
      exact MonoidHom.normal_ker _
    · exact burnsideB46_p4_R2_isPGroup

theorem burnsideB46_p4_n1_natMod_std :
    burnsideB46_p4_NatMod K (stabQ (stdF K 2)) (burnsideB46_p4_R2 K) (stdF K 2) := by
  refine ⟨burnsideB46_p4_R2_le_stabQ, fun g hg y hy => (mem_stabQ.1 hg y).1 hy,
    burnsideB46_p4_levi2GL K, burnsideB46_p4_upartHom, burnsideB46_p4_n1_levi2GL_surjective,
    burnsideB46_p4_ker_levi2GL, ?_, ?_, ?_⟩
  · intro y hy y' hy' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [burnsideB46_p4_upartHom, AddMonoidHom.mk'_apply, upart] at h0 h1
    simp at h0 h1
    rw [burnsideB46_p4_F2_eq hy, burnsideB46_p4_F2_eq hy', h0, h1]
  · intro k _
    refine ⟨q6 (k 0) 0 0 0 0 (k 1), burnsideB46_p4_F2_of, ?_⟩
    funext i
    fin_cases i <;> simp [burnsideB46_p4_upartHom, upart, q6]
  · intro g y hy
    exact upart_act g.1 hy

theorem burnsideB46_p4_n1_cfg2 {V : Type} [CommGroup V] [Finite K] [Finite V] {n : ℕ}
    {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
    {θ : V →* Multiplicative (NatQ K)}
    (H : burnsideB46_Hyp V n K G L π θ) (hnormLG : G ≤ Subgroup.normalizer (L : Set (MulAut V)))
    {x : Ix3 → K} (hx : x ≠ 0)
    {P₁ T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hP₁ : P₁ = (burnsideB46_P1 K x).map (burnsideB46_pi π))
    (h : B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂) :
    ∃ c : ↥(cayleyGroup K), burnsideB46_pt K x = gmapG c (stdF K 1) ∧
      T ⊓ L = (U0 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      Z₂ = (burnsideB46_p4_Z0 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      P₂ = (stabQ (stdF K 2)).map (burnsideB46_p4_ofHyp H c).Φ ∧
      R₂ = (burnsideB46_p4_R2 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      V₂ = burnsideB46_pre θ (gmapG c (stdF K 2)) := by
  haveI : Finite (MulAut V) := Finite.of_injective (fun e : MulAut V => (e : V → V))
    (fun e e' h => MulEquiv.ext (congrFun h))
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  obtain ⟨hTG, hTLP₁, hZ₂, hP₂, hR₂, hV₂⟩ := h
  have hSyl : IsSylowTwoOf (T ⊓ L) L := B6.isSylowTwoOf_inf_normal hTG H.le hnormLG
  set S₀ : Subgroup ↥(cayleyGroup K) := (T ⊓ L).comap (burnsideB46_pi π) with hS₀def
  have hS₀map : S₀.map (burnsideB46_pi π) = T ⊓ L := by
    ext l
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hl
      obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 hl.2
      refine ⟨g, ?_, hg⟩
      show burnsideB46_pi π g ∈ T ⊓ L
      rw [hg]
      exact hl
  have hTop : (⊤ : Subgroup ↥(cayleyGroup K)).map (burnsideB46_pi π) = L := by
    ext l
    constructor
    · rintro ⟨g, -, rfl⟩
      exact burnsideB46_pi_mem_L H g
    · intro hl
      obtain ⟨g, hg⟩ := (burnsideB46_mem_L' H).1 hl
      exact ⟨g, trivial, hg⟩
  have hS₀ : IsSylowTwoOf S₀ ⊤ :=
    (burnsideB46_p3_isSylowTwoOf_map (burnsideB46_pi_injective H)).1 (by
      rw [hS₀map, hTop]
      exact hSyl)
  obtain ⟨c, hc⟩ := burnsideB46_p4_sylow_conj H.card H.one_le hS₀
  set C := burnsideB46_p4_ofHyp H c with hCdef
  have hT : T ⊓ L = (U0 K).map C.Φ := by
    rw [← hS₀map, hc, Subgroup.map_map]
    rfl
  have hS₀P : S₀ ≤ burnsideB46_P1 K x := by
    intro g hg
    have h1 : burnsideB46_pi π g ∈ P₁ := hTLP₁ hg
    rw [hP₁] at h1
    exact (Subgroup.mem_map_iff_mem (burnsideB46_pi_injective H)).1 h1
  have hpt : burnsideB46_pt K x = gmapG c (stdF K 1) := by
    have hstab : U0Stable (gmapG c⁻¹ (burnsideB46_pt K x)) := by
      intro g hg w hw
      rw [mem_gmapG] at hw ⊢
      have hmem : c * g * c⁻¹ ∈ burnsideB46_P1 K x := hS₀P (by rw [hc]; exact ⟨g, hg, rfl⟩)
      have h1 := (mem_stabQ.1 hmem (g2Act c w)).1 (by simpa using hw)
      rw [burnsideB46_p4_mul_apply, burnsideB46_p4_mul_apply, g2Act_inv_apply] at h1
      simpa using h1
    have hcard : Nat.card (gmapG c⁻¹ (burnsideB46_pt K x)) = Nat.card K ^ 1 := by
      rw [card_gmapG]
      have h1 : Nat.card (burnsideB46_pt K x) = Nat.card K ^ Module.finrank K (burnsideB46_pt K x) :=
        Module.natCard_eq_pow_finrank
      rw [h1, burnsideB46_pt, finrank_span_singleton hx]
    have h2 := eq_stdF_of_card hstab hcard
    rw [← h2, gmapG_gmapG_inv]
  have hZ : Z₂ = (burnsideB46_p4_Z0 K).map C.Φ := by
    rw [hZ₂, hT, burnsideB46_centerOf_map _ C.inj, ← burnsideB46_p4_center_U0]
  have hP : P₂ = (stabQ (stdF K 2)).map C.Φ := by
    rw [hP₂, hZ, C.inf_normalizer_map, burnsideB46_p4_normalizer_Z0]
  have hR : R₂ = (burnsideB46_p4_R2 K).map C.Φ := by
    rw [hR₂, hP, burnsideB46_pCoreOf_map _ C.inj, burnsideB46_p4_n1_pCore_P2]
  refine ⟨c, hpt, hT, hZ, hP, hR, ?_⟩
  rw [hV₂, hR, C.cPre_map, burnsideB46_p4_fixSub_R2, hCdef, burnsideB46_p4_ofHyp_pre]

end P4n

section P4na

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_4_one (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have _hn1 := hn1
  have hnormLG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hGL]
    exact Subgroup.le_normalizer
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2
  obtain ⟨x, hx0, hV₁, hP₁, hR₁, hZ₁, hV₃⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, hZ, hP, hR, hV⟩ := burnsideB46_p4_n1_cfg2 H hnormLG hx0 hP₁ hcfg2
  set C := burnsideB46_p4_ofHyp H c with hC
  have hV' : V₂ = C.pre (stdF K 2) := hV.trans (burnsideB46_p4_ofHyp_pre H c _).symm
  have hmaxstd : IsMaxParabolic2 (⊤ : Subgroup ↥(cayleyGroup K)) (stabQ (stdF K 2)) :=
    burnsideB46_wp2_isMax H.card H.one_le
  have hP₁' : P₁ = (stabQ (stdF K 1)).map C.Φ := by
    rw [hP₁, burnsideB46_P1, hpt, burnsideB46_p3_stabQ_gmapG, Subgroup.map_map]
    rfl
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hZ]
    exact burnsideB46_p3_isElemAbelian_map burnsideB46_p4_Z0_elemAbelian
  · rw [hZ, Subgroup.card_map_of_injective C.inj, burnsideB46_p4_card_Z0]
  · rw [hZ]
    exact burnsideB46_p4_isLongRootSub π c
  · have h1 := burnsideB46_p3_isMaxParabolic2_map C.inj hmaxstd
    rw [C.map_top] at h1
    rw [hP]
    exact h1
  · rw [hT, hP]
    exact Subgroup.map_mono burnsideB46_p4_U0_le_stabQ_two
  · rw [hP, hP₁']
    intro h
    exact burnsideB46_p4_stabQ_two_ne_one (Subgroup.map_injective C.inj h)
  · rw [hZ, hR]
    exact burnsideB46_p4_isSpecial2_map C.inj burnsideB46_p4_R2_special
  · rw [hR, Subgroup.card_map_of_injective C.inj, burnsideB46_p4_card_R2]
  · rw [hP, hR, hV']
    exact C.natMod burnsideB46_p4_n1_natMod_std
  · intro z hz hz1
    rw [hZ] at hz
    obtain ⟨g0, hg0, rfl⟩ := hz
    obtain ⟨s, rfl⟩ := hg0
    have hs : s ≠ 0 := by
      rintro rfl
      exact hz1 (by rw [tL_zero, map_one])
    rw [hV']
    exact (C.comm_pre (g0 := tL s) (X := burnsideB46_p4_Z0 K) (Y := stdF K 2) ⟨s, rfl⟩
      (by
        rintro _ ⟨t, rfl⟩ w
        exact g2Act_tL_sub_mem t w)
      (fun y hy => exists_tL_sub_eq hs hy)).symm
  · intro z hz hz1
    rw [hZ] at hz
    obtain ⟨g0, hg0, rfl⟩ := hz
    have hg01 : g0 ≠ 1 := fun h => hz1 (by rw [h, map_one])
    have hfix : cPre (fixV L) (burnsideB46_p4_Z0 K |>.map C.Φ) = C.pre (stdF K 4) := by
      rw [C.cPre_map, burnsideB46_p4_fixSub_Z0]
    refine ⟨?_, ?_⟩
    · rw [hZ, hfix, ← MonoidHom.map_zpowers, C.cPre_map,
        burnsideB46_p4_fixSub_zpowers hg0 hg01]
    · rw [hZ, hfix]
      refine burnsideB46_isFPre_iff.2 ⟨gmapG c (stdF K 4), ?_, ?_⟩
      · rw [burnsideB46_p3_finrank_gmapG, burnsideB46_p4_finrank_stdF (by norm_num)]
      · rw [← burnsideB46_p4_ofHyp_pre H c]

theorem burnsideB46_part_10_one (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have _hn1 := hn1
  have hnormLG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hGL]
    exact Subgroup.le_normalizer
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2
  obtain ⟨x, hx0, hV₁, hP₁, hR₁, hZ₁, hV₃⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, hZ, hP, hR, hV⟩ := burnsideB46_p4_n1_cfg2 H hnormLG hx0 hP₁ hcfg2
  set C := burnsideB46_p4_ofHyp H c with hC
  have hF3 : burnsideB46_F3 K x = gmapG c (stdF K 3) := by
    have h1 : burnsideB46_pt K x = burnsideB46_pt K (g2Act c (eu 0 1)) := by
      rw [hpt, burnsideB46_p3_pt_act, burnsideB46_p3_pt_eu]
    have h2 : burnsideB46_F3 K x = burnsideB46_F3 K (g2Act c (eu 0 1)) := by
      simp only [burnsideB46_F3, burnsideB46_Z1, burnsideB46_R1, burnsideB46_P1, h1]
    rw [h2, burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu]
  have hV₁' : V₁ = C.pre (stdF K 1) := by
    rw [hV₁, hpt]
    exact (burnsideB46_p4_ofHyp_pre H c _).symm
  have hV₃' : V₃ = C.pre (stdF K 3) := by
    rw [hV₃, hF3]
    exact (burnsideB46_p4_ofHyp_pre H c _).symm
  have hV' : V₂ = C.pre (stdF K 2) := hV.trans (burnsideB46_p4_ofHyp_pre H c _).symm
  have hP₁' : P₁ = (stabQ (stdF K 1)).map C.Φ := by
    rw [hP₁, burnsideB46_P1, hpt, burnsideB46_p3_stabQ_gmapG, Subgroup.map_map]
    rfl
  have hmap : ∀ g ∈ stabQ (stdF K 1),
      V₂.map (C.Φ g : MulAut V).toMonoidHom = C.pre (gmapG g (stdF K 2)) := by
    intro g _
    rw [hV', C.map_pre]
  have hplane : ∀ g ∈ stabQ (stdF K 1), ∃ o : Option K, gmapG g (stdF K 2) = burnsideB46_p4_Psi K o := by
    intro g hg
    have : gmapG g (stdF K 2) ∈ Set.range (burnsideB46_p4_Psi K) := by
      rw [← burnsideB46_p4_planes_eq]
      exact ⟨g, hg, rfl⟩
    obtain ⟨o, ho⟩ := this
    exact ⟨o, ho.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} =
        C.pre '' Set.range (burnsideB46_p4_Psi K) := by
      ext X
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [hP₁'] at hp
        obtain ⟨g, hg, rfl⟩ := hp
        obtain ⟨o, ho⟩ := hplane g hg
        exact ⟨burnsideB46_p4_Psi K o, ⟨o, rfl⟩, by rw [hmap g hg, ho]⟩
      · rintro ⟨_, ⟨o, rfl⟩, rfl⟩
        have : burnsideB46_p4_Psi K o ∈
            {Y : Submodule K (Ix3 → K) | ∃ g ∈ stabQ (stdF K 1), Y = gmapG g (stdF K 2)} := by
          rw [burnsideB46_p4_planes_eq]
          exact ⟨o, rfl⟩
        obtain ⟨g, hg, hgo⟩ := this
        refine ⟨C.Φ g, ?_, ?_⟩
        · rw [hP₁']
          exact ⟨g, hg, rfl⟩
        · rw [hmap g hg, hgo]
    rw [hset, Set.ncard_image_of_injective _ (fun Y Y' h => C.pre_injective h),
      Set.ncard_range_of_injective burnsideB46_p4_Psi_injective, Finite.card_option]
  · intro p hp
    rw [hP₁'] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨o, ho⟩ := hplane g hg
    rw [hmap g hg, ho, hV₁', hV₃']
    exact ⟨C.pre_le_pre_iff.2 (burnsideB46_p4_Psi_le o).1,
      C.pre_le_pre_iff.2 (burnsideB46_p4_Psi_le o).2⟩
  · intro p hp p' hp' hne
    rw [hP₁'] at hp hp'
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨g', hg', rfl⟩ := hp'
    obtain ⟨o, ho⟩ := hplane g hg
    obtain ⟨o', ho'⟩ := hplane g' hg'
    rw [hmap g hg, ho, hmap g' hg', ho'] at hne ⊢
    have hoo : o ≠ o' := fun h => hne (by rw [h])
    rw [hV₁', C.pre_inf, burnsideB46_p4_Psi_inf hoo]
  · intro v hv
    rw [hV₃'] at hv
    obtain ⟨o, ho⟩ := burnsideB46_p4_Psi_cover (show C.f v ∈ stdF K 3 from hv)
    have : burnsideB46_p4_Psi K o ∈
        {Y : Submodule K (Ix3 → K) | ∃ g ∈ stabQ (stdF K 1), Y = gmapG g (stdF K 2)} := by
      rw [burnsideB46_p4_planes_eq]
      exact ⟨o, rfl⟩
    obtain ⟨g, hg, hgo⟩ := this
    refine ⟨C.Φ g, ?_, ?_⟩
    · rw [hP₁']
      exact ⟨g, hg, rfl⟩
    · rw [hmap g hg, ← hgo]
      exact ho

end P4na

section P5

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p5_polarQ_self (x : Ix3 → K) : polarQ x x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [polarQ]
  linear_combination
    (x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1) + x (.inl 2) * x (.inr 2)) * h2

omit [CharP K 2] in
theorem burnsideB46_p5_polarQ_eu (x : Ix3 → K) (i : Fin 3) (a : K) :
    polarQ x (eu i a) = x (.inr i) * a := by
  fin_cases i <;> simp [polarQ, eu, Pi.single_apply] <;> ring

omit [CharP K 2] in
theorem burnsideB46_p5_polarQ_ev (x : Ix3 → K) (j : Fin 3) (b : K) :
    polarQ x (ev j b) = x (.inl j) * b := by
  fin_cases j <;> simp [polarQ, ev, Pi.single_apply] <;> ring

theorem burnsideB46_p5_qr_tv (i j : Fin 3) (hij : i ≠ j) (t : K) (x : Ix3 → K) :
    qr (g2A (tv i j hij t)) x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [qr, g2Act_tv]
  rw [polarQ_add_right, polarQ_add_right, burnsideB46_p5_polarQ_self,
    burnsideB46_p5_polarQ_eu, burnsideB46_p5_polarQ_ev]
  linear_combination (t * x (.inr i) * x (.inl j)) * h2

omit [CharP K 2] in
theorem burnsideB46_p5_transvection_mulVec (i j : Fin 3) (c : K) (u : Fin 3 → K) :
    Matrix.transvection i j c *ᵥ u = u + Pi.single i (c * u j) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, transvection_entry, Pi.add_apply, Pi.single_apply,
    add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  by_cases hk : k = i
  · subst hk
    simp [Finset.sum_ite_eq']
  · simp [hk, Finset.sum_ite_eq', Ne.symm hk]

omit [CharP K 2] in
theorem burnsideB46_p5_transvection_transpose_mulVec (i j : Fin 3) (c : K) (v : Fin 3 → K) :
    (Matrix.transvection i j c)ᵀ *ᵥ v = v + Pi.single j (c * v i) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, transvection_entry, Pi.add_apply, Pi.single_apply,
    add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  by_cases hk : k = j
  · subst hk
    simp [Finset.sum_ite_eq']
  · simp [hk, Finset.sum_ite_eq', Ne.symm hk]

theorem burnsideB46_p5_longRootFn_eq (i j : Fin 3) (hij : i ≠ j) (c : K) (x : quasithinZorn K) :
    longRootFn i j c x = (g2A (tv i j hij c) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x := by
  rw [g2A_apply]
  have hA : ((tv i j hij c : SL3 K) : Matrix (Fin 3) (Fin 3) K) = Matrix.transvection i j c := rfl
  rw [gAFun, adjugate_tv, hA, longRootFn, burnsideB46_p5_transvection_mulVec,
    burnsideB46_p5_transvection_transpose_mulVec]

theorem burnsideB46_p5_tv_mul_self (i j : Fin 3) (hij : i ≠ j) (t : K) :
    g2A (tv i j hij t) * g2A (tv i j hij t) = 1 := by
  rw [← map_mul, tv_mul_self, map_one]

theorem burnsideB46_p5_tv_ne_one (i j : Fin 3) (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    g2A (tv i j hij t) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : ↥(cayleyGroup K) => g2Act g (eu j 1) (.inl i)) h
  simp only [g2Act_tv, map_one] at h1
  simp [eu, ev, Pi.single_apply, hij, Ne.symm hij] at h1
  exact ht h1

theorem burnsideB46_p5_card_fixQ_tv [Finite K] (i j : Fin 3) (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    Nat.card K ^ 4 ≤ Nat.card (fixQ (g2A (tv i j hij t))) := by
  have h2 := card_commQ_mul_card_fixQ (g2A (tv i j hij t))
  rw [card_Q] at h2
  let φ : K × K →+ (Ix3 → K) := (AddMonoidHom.single (fun _ : Ix3 => K) (Sum.inl i)).coprod
    (AddMonoidHom.single (fun _ : Ix3 => K) (Sum.inr j))
  have hle : commQ (g2A (tv i j hij t)) ≤ φ.range := by
    intro w hw
    obtain ⟨z, rfl⟩ := mem_commQ.mp hw
    refine ⟨(t * z (.inl j), t * z (.inr i)), ?_⟩
    simp only [φ, AddMonoidHom.coprod_apply, AddMonoidHom.single_apply]
    rw [g2Act_tv]
    abel
  have h3 : Nat.card (commQ (g2A (tv i j hij t))) ≤ Nat.card K ^ 2 := by
    refine (AddSubgroup.card_le_of_le hle).trans ?_
    have := Nat.card_le_card_of_surjective _ (AddMonoidHom.rangeRestrict_surjective φ)
    rwa [Nat.card_prod, ← sq] at this
  have hq : 0 < Nat.card K ^ 2 := by
    have := Nat.card_pos (α := K)
    positivity
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card (commQ (g2A (tv i j hij t))) * Nat.card (fixQ (g2A (tv i j hij t))) <
      Nat.card K ^ 2 * Nat.card K ^ 4 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ h3) (Nat.mul_lt_mul_of_pos_left hlt hq)
  rw [h2, ← pow_add] at h4
  exact lt_irrefl _ h4

theorem burnsideB46_p5_tv_conj_tL [Finite K] (i j : Fin 3) (hij : i ≠ j) {t : K} (ht : t ≠ 0) :
    ∃ x : ↥(cayleyGroup K), g2A (tv i j hij t) = x * tL 1 * x⁻¹ :=
  eq_conj_tL_of_fix (burnsideB46_p5_tv_mul_self i j hij t) (burnsideB46_p5_tv_ne_one i j hij ht)
    (burnsideB46_p5_card_fixQ_tv i j hij ht)

theorem burnsideB46_p5_qr_xs (t : K) (x : Ix3 → K) :
    qr (g2X ![t, 0, 0]) x = t * t * (x (.inr 0) * x (.inr 0)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  conv_lhs => rw [q6_eta x]
  simp only [qr, g2Act_x0q, polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0,
    q6_apply_inr1, q6_apply_inr2]
  linear_combination (x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1) + x (.inl 2) * x (.inr 2) +
    t * x (.inl 1) * x (.inl 2)) * h2

theorem burnsideB46_p5_y_conj_x (a b : K) :
    g2Y ![0, a, b] * g2X ![1, 0, 0] * g2Y ![0, a, b] = g2X ![1, 0, 0] * g2A (uSL a b 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine cayley_ext fun w => ?_
  rw [q6_eta w, g2Act_mul_apply, g2Act_mul_apply, g2Act_mul_apply, g2Act_y12q, g2Act_x0q,
    g2Act_y12q, g2Act_g2A_uSL, g2Act_x0q]
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring_nf <;> reduce_mod_char!

theorem burnsideB46_p5_short_conj [Finite K] {r : ↥(cayleyGroup K)} (hr : r * r = 1)
    (hq : ∃ x, qr r x ≠ 0) : ∃ g : ↥(cayleyGroup K), r = g * g2X ![1, 0, 0] * g⁻¹ := by
  obtain ⟨x₀, hx₀⟩ := hq
  obtain ⟨p, hp⟩ := exists_qr_eq_sq hr
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hx₀
    rw [hp]
    simp [polarQ]
  obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hp0
  have hqr' : ∀ x, qr (g⁻¹ * r * g) x = x (.inr 0) * x (.inr 0) := by
    intro x
    have h1 := qr_conj g⁻¹ r (g2Act g x)
    rw [inv_inv, g2Act_inv_apply] at h1
    rw [h1, hp, ← polarQ_g2Act g⁻¹, g2Act_inv_apply, ← hg, g2Act_inv_apply, polarQ_eu0]
  have hr' : (g⁻¹ * r * g) * (g⁻¹ * r * g) = 1 := by
    calc (g⁻¹ * r * g) * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g := by group
      _ = 1 := by rw [hr]; group
  obtain ⟨a, b, hab⟩ := eq_kerElt_of_qr hr' hqr'
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  rw [hz3, g2Y_zero, mul_one] at hab
  refine ⟨g * g2Y ![0, a, b], ?_⟩
  have hconj := burnsideB46_p5_y_conj_x a b
  calc r = g * (g⁻¹ * r * g) * g⁻¹ := by group
    _ = g * (g2X ![1, 0, 0] * g2A (uSL a b 0)) * g⁻¹ := by rw [hab]
    _ = g * (g2Y ![0, a, b] * g2X ![1, 0, 0] * g2Y ![0, a, b]) * g⁻¹ := by rw [hconj]
    _ = g * g2Y ![0, a, b] * g2X ![1, 0, 0] * (g * g2Y ![0, a, b])⁻¹ := by
      rw [mul_inv_rev, JonesParshall.g2Y_inv]; group

theorem burnsideB46_p5_rank_ne_three {W : Type*} [AddCommGroup W] [Module K W]
    (B : W →ₗ[K] W →ₗ[K] K) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hsymm : ∀ x y, B x y = B y x) (T : W →ₗ[K] W) (hadj : ∀ x y, B (T x) y = B x (T y))
    (halt : ∀ x, B x (T x) = 0) : Module.finrank K (LinearMap.range T) ≠ 3 := by
  intro h3
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Module.Finite K (LinearMap.range T) := Module.finite_of_finrank_eq_succ h3
  let b := Module.finBasisOfFinrankEq K (LinearMap.range T) h3
  have hx : ∀ i, ∃ x : W, T x = (b i : W) := fun i => (b i).2
  choose x hx using hx
  have hdec : ∀ z, ∃ μ : Fin 3 → K, T z = ∑ i, μ i • T (x i) := by
    intro z
    have hz : T z ∈ LinearMap.range T := LinearMap.mem_range_self T z
    refine ⟨fun i => b.repr ⟨T z, hz⟩ i, ?_⟩
    have h := congrArg Subtype.val (b.sum_repr ⟨T z, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    simp only [hx]
  have hβs : ∀ i j, B (x i) (T (x j)) = B (x j) (T (x i)) := fun i j => by
    rw [← hadj, hsymm]
  have hy0 : B (B (x 1) (T (x 2)) • x 0 + B (x 0) (T (x 2)) • x 1 + B (x 0) (T (x 1)) • x 2)
      (T (x 0)) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination B (x 1) (T (x 2)) * halt (x 0) + B (x 0) (T (x 2)) * hβs 1 0 +
      B (x 0) (T (x 1)) * hβs 2 0 + (B (x 0) (T (x 1)) * B (x 0) (T (x 2))) * h2
  have hy1 : B (B (x 1) (T (x 2)) • x 0 + B (x 0) (T (x 2)) • x 1 + B (x 0) (T (x 1)) • x 2)
      (T (x 1)) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination B (x 0) (T (x 2)) * halt (x 1) + B (x 0) (T (x 1)) * hβs 2 1 +
      (B (x 1) (T (x 2)) * B (x 0) (T (x 1))) * h2
  have hy2 : B (B (x 1) (T (x 2)) • x 0 + B (x 0) (T (x 2)) • x 1 + B (x 0) (T (x 1)) • x 2)
      (T (x 2)) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination B (x 0) (T (x 1)) * halt (x 2) +
      (B (x 1) (T (x 2)) * B (x 0) (T (x 2))) * h2
  have hy : ∀ j, B (B (x 1) (T (x 2)) • x 0 + B (x 0) (T (x 2)) • x 1 + B (x 0) (T (x 1)) • x 2)
      (T (x j)) = 0 := by
    intro j
    fin_cases j
    exacts [hy0, hy1, hy2]
  set c₁ : K := B (x 1) (T (x 2)) with hc₁
  set c₂ : K := B (x 0) (T (x 2)) with hc₂
  set c₃ : K := B (x 0) (T (x 1)) with hc₃
  set y : W := c₁ • x 0 + c₂ • x 1 + c₃ • x 2 with hy_def
  have hyz : ∀ z, B y (T z) = 0 := by
    intro z
    obtain ⟨μ, hμ⟩ := hdec z
    rw [hμ]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_eq_zero fun i _ => by rw [hy i, mul_zero]
  have hTy : T y = 0 := hnd _ fun z => by rw [hadj, hyz]
  have hTy' : c₁ • b 0 + c₂ • b 1 + c₃ • b 2 = 0 := by
    have h := hTy
    simp only [hy_def, map_add, map_smul, hx] at h
    exact Subtype.ext h
  have hind : ∀ g : Fin 3 → K, ∑ i, g i • b i = 0 → ∀ i, g i = 0 :=
    Fintype.linearIndependent_iff.mp b.linearIndependent
  have hcoef := hind ![c₁, c₂, c₃] (by
    rw [Fin.sum_univ_three]
    simpa using hTy')
  have h12 : B (x 1) (T (x 2)) = 0 := hcoef 0
  have h02 : B (x 0) (T (x 2)) = 0 := hcoef 1
  have h01 : B (x 0) (T (x 1)) = 0 := hcoef 2
  have hβ : ∀ i j, B (x i) (T (x j)) = 0 := by
    intro i j
    fin_cases i <;> fin_cases j
    exacts [halt (x 0), h01, h02, (hβs 1 0).trans h01, halt (x 1), h12, (hβs 2 0).trans h02,
      (hβs 2 1).trans h12, halt (x 2)]
  have hall : ∀ z z', B z (T z') = 0 := by
    intro z z'
    obtain ⟨μ, hμ⟩ := hdec z'
    obtain ⟨ν, hν⟩ := hdec z
    set z₁ : W := ∑ i, ν i • x i with hz₁
    have hTz₁ : T z₁ = T z := by
      rw [hν, hz₁, map_sum]
      simp only [map_smul]
    have hk : T (z - z₁) = 0 := by rw [map_sub, hTz₁, sub_self]
    have e1 : B z₁ (T z') = 0 := by
      rw [hμ, hz₁]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hβ,
        mul_zero, Finset.sum_const_zero]
    have e2 : B (z - z₁) (T z') = 0 := by rw [← hadj, hk, map_zero, LinearMap.zero_apply]
    have e3 : B z (T z') = B z₁ (T z') + B (z - z₁) (T z') := by
      rw [← LinearMap.add_apply, ← map_add, add_sub_cancel]
    rw [e3, e1, e2, add_zero]
  have hT0 : ∀ z', T z' = 0 := fun z' => hnd _ fun z => by rw [hsymm]; exact hall z z'
  rw [LinearMap.range_eq_bot.mpr (LinearMap.ext hT0)] at h3
  simp at h3

@[expose] def burnsideB46_p5_B (K : Type) [Field K] : (Ix3 → K) →ₗ[K] (Ix3 → K) →ₗ[K] K :=
  LinearMap.mk₂ K polarQ (fun x x' y => polarQ_add_left x x' y)
    (fun c x y => by rw [polarQ_smul_left, smul_eq_mul])
    (fun x y y' => polarQ_add_right x y y')
    (fun c x y => by rw [polarQ_smul_right, smul_eq_mul])

omit [CharP K 2] in
theorem burnsideB46_p5_B_apply (x y : Ix3 → K) : burnsideB46_p5_B K x y = polarQ x y := rfl

@[expose] noncomputable def burnsideB46_p5_T (r : ↥(cayleyGroup K)) :
    (Ix3 → K) →ₗ[K] (Ix3 → K) where
  toFun w := g2Act r w - w
  map_add' a b := by
    rw [map_add]
    abel
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [JonesParshall.g2Act_smul, smul_sub]

theorem burnsideB46_p5_T_apply (r : ↥(cayleyGroup K)) (w : Ix3 → K) :
    burnsideB46_p5_T r w = g2Act r w - w := rfl

theorem burnsideB46_p5_card_fix_of_qr_zero [Finite K] {r : ↥(cayleyGroup K)} (hr : r * r = 1)
    (hq : ∀ x, qr r x = 0) : Nat.card K ^ 4 ≤ Nat.card (fixQ r) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hrr : ∀ w, g2Act r (g2Act r w) = w := fun w => by
    rw [← g2Act_mul_apply, hr, map_one]
    rfl
  have hnd : ∀ x, (∀ y, burnsideB46_p5_B K x y = 0) → x = 0 := fun x h => eq_zero_of_polarQ h
  have hsymm : ∀ x y, burnsideB46_p5_B K x y = burnsideB46_p5_B K y x := fun x y =>
    polarQ_symm x y
  have hadj : ∀ x y, burnsideB46_p5_B K (burnsideB46_p5_T r x) y =
      burnsideB46_p5_B K x (burnsideB46_p5_T r y) := by
    intro x y
    simp only [burnsideB46_p5_B_apply, burnsideB46_p5_T_apply, polarQ_sub_left, polarQ_sub_right]
    have h1 : polarQ (g2Act r x) y = polarQ x (g2Act r y) := by
      have := polarQ_g2Act r x (g2Act r y)
      rwa [hrr] at this
    rw [h1]
  have halt : ∀ x, burnsideB46_p5_B K x (burnsideB46_p5_T r x) = 0 := by
    intro x
    simp only [burnsideB46_p5_B_apply, burnsideB46_p5_T_apply, polarQ_sub_right,
      burnsideB46_p5_polarQ_self, sub_zero]
    exact hq x
  have hne3 := burnsideB46_p5_rank_ne_three (burnsideB46_p5_B K) hnd hsymm
    (burnsideB46_p5_T r) hadj halt
  have hTT : ∀ x, burnsideB46_p5_T r (burnsideB46_p5_T r x) = 0 := by
    intro x
    funext j
    simp only [burnsideB46_p5_T_apply, map_sub, hrr, Pi.sub_apply, Pi.zero_apply]
    linear_combination (x j - g2Act r x j) * h2
  have hle : LinearMap.range (burnsideB46_p5_T r) ≤ LinearMap.ker (burnsideB46_p5_T r) := by
    rintro _ ⟨x, rfl⟩
    exact hTT x
  have hrn := LinearMap.finrank_range_add_finrank_ker (burnsideB46_p5_T r)
  have h6 : Module.finrank K (Ix3 → K) = 6 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hmono := Submodule.finrank_mono hle
  have hker4 : 4 ≤ Module.finrank K (LinearMap.ker (burnsideB46_p5_T r)) := by omega
  have hcard : Nat.card (fixQ r) =
      Nat.card K ^ Module.finrank K (LinearMap.ker (burnsideB46_p5_T r)) := by
    rw [← Module.natCard_eq_pow_finrank]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [mem_fixQ, LinearMap.mem_ker, burnsideB46_p5_T_apply, sub_eq_zero])
  rw [hcard]
  exact Nat.pow_le_pow_right (by have := Nat.card_pos (α := K); omega) hker4


theorem burnsideB46_p5_qr_conj_zero {r : ↥(cayleyGroup K)} (hq : ∀ x, qr r x = 0)
    (g : ↥(cayleyGroup K)) : ∀ x, qr (g * r * g⁻¹) x = 0 := by
  intro x
  have h := qr_conj g r (g2Act g⁻¹ x)
  rw [g2Act_apply_inv] at h
  rw [h, hq]

theorem burnsideB46_p5_qr_conj_ne {r : ↥(cayleyGroup K)} (hq : ∃ x, qr r x ≠ 0)
    (g : ↥(cayleyGroup K)) : ∃ x, qr (g * r * g⁻¹) x ≠ 0 := by
  obtain ⟨x, hx⟩ := hq
  exact ⟨g2Act g x, by rw [qr_conj]; exact hx⟩

@[expose] def burnsideB46_p5_IsLongEl (γ : ↥(cayleyGroup K)) : Prop :=
  ∃ g : ↥(cayleyGroup K), γ = g * tL 1 * g⁻¹

@[expose] def burnsideB46_p5_IsShortEl (γ : ↥(cayleyGroup K)) : Prop :=
  ∃ g : ↥(cayleyGroup K), γ = g * g2X ![1, 0, 0] * g⁻¹

theorem burnsideB46_p5_tL_eq_tv (s : K) : tL s = g2A (tv 0 2 (by decide) s) := rfl

theorem burnsideB46_p5_qr_tL (s : K) (x : Ix3 → K) : qr (tL s) x = 0 :=
  burnsideB46_p5_qr_tv 0 2 (by decide) s x

theorem burnsideB46_p5_isLongEl_iff [Finite K] {γ : ↥(cayleyGroup K)} :
    burnsideB46_p5_IsLongEl γ ↔
      ∃ (h : ↥(cayleyGroup K)) (s : K), s ≠ 0 ∧ γ = h * tL s * h⁻¹ := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, 1, one_ne_zero, rfl⟩
  · rintro ⟨h, s, hs, rfl⟩
    obtain ⟨x, hx⟩ := burnsideB46_p5_tv_conj_tL 0 2 (by decide) hs
    refine ⟨h * x, ?_⟩
    rw [burnsideB46_p5_tL_eq_tv, hx]
    group

theorem burnsideB46_p5_isShortEl_iff [Finite K] {γ : ↥(cayleyGroup K)} :
    burnsideB46_p5_IsShortEl γ ↔
      ∃ (h : ↥(cayleyGroup K)) (t : K), t ≠ 0 ∧ γ = h * g2X ![t, 0, 0] * h⁻¹ := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, 1, one_ne_zero, rfl⟩
  · rintro ⟨h, t, ht, rfl⟩
    obtain ⟨x, hx⟩ := burnsideB46_p5_short_conj (g2X_mul_self ![t, 0, 0])
      ⟨q6 0 0 0 1 0 0, by
        rw [burnsideB46_p5_qr_xs]
        simpa [q6] using ht⟩
    exact ⟨h * x, by rw [hx]; group⟩

theorem burnsideB46_p5_IsLongEl.qr_zero {γ : ↥(cayleyGroup K)}
    (h : burnsideB46_p5_IsLongEl γ) : ∀ x, qr γ x = 0 := by
  obtain ⟨g, rfl⟩ := h
  exact burnsideB46_p5_qr_conj_zero (burnsideB46_p5_qr_tL 1) g

theorem burnsideB46_p5_IsShortEl.qr_ne {γ : ↥(cayleyGroup K)}
    (h : burnsideB46_p5_IsShortEl γ) : ∃ x, qr γ x ≠ 0 := by
  obtain ⟨g, rfl⟩ := h
  refine burnsideB46_p5_qr_conj_ne ⟨q6 0 0 0 1 0 0, ?_⟩ g
  rw [burnsideB46_p5_qr_xs]
  simp [q6]

theorem burnsideB46_p5_not_long_short {γ : ↥(cayleyGroup K)} (hl : burnsideB46_p5_IsLongEl γ)
    (hs : burnsideB46_p5_IsShortEl γ) : False := by
  obtain ⟨x, hx⟩ := burnsideB46_p5_IsShortEl.qr_ne hs
  exact hx (burnsideB46_p5_IsLongEl.qr_zero hl x)

theorem burnsideB46_p5_invol_cases [Finite K] {r : ↥(cayleyGroup K)} (hr : r * r = 1) (h1 : r ≠ 1) :
    burnsideB46_p5_IsLongEl r ∨ burnsideB46_p5_IsShortEl r := by
  by_cases hq : ∀ x, qr r x = 0
  · left
    exact eq_conj_tL_of_fix hr h1 (burnsideB46_p5_card_fix_of_qr_zero hr hq)
  · right
    push Not at hq
    exact burnsideB46_p5_short_conj hr hq

theorem burnsideB46_p5_IsLongEl.mul_self {γ : ↥(cayleyGroup K)} (h : burnsideB46_p5_IsLongEl γ) :
    γ * γ = 1 := by
  obtain ⟨g, rfl⟩ := h
  have : tL (1 : K) * tL 1 = 1 := burnsideB46_p5_tv_mul_self 0 2 (by decide) 1
  calc g * tL 1 * g⁻¹ * (g * tL 1 * g⁻¹) = g * (tL 1 * tL 1) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem burnsideB46_p5_IsShortEl.mul_self {γ : ↥(cayleyGroup K)} (h : burnsideB46_p5_IsShortEl γ) :
    γ * γ = 1 := by
  obtain ⟨g, rfl⟩ := h
  have : g2X ![(1 : K), 0, 0] * g2X ![1, 0, 0] = 1 := g2X_mul_self _
  calc g * g2X ![1, 0, 0] * g⁻¹ * (g * g2X ![1, 0, 0] * g⁻¹) =
      g * (g2X ![1, 0, 0] * g2X ![1, 0, 0]) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem burnsideB46_p5_IsLongEl.ne_one {γ : ↥(cayleyGroup K)} (h : burnsideB46_p5_IsLongEl γ) :
    γ ≠ 1 := by
  obtain ⟨g, rfl⟩ := h
  intro h1
  have : tL (1 : K) = 1 := by
    calc tL (1 : K) = g⁻¹ * (g * tL 1 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  exact burnsideB46_p5_tv_ne_one 0 2 (by decide) one_ne_zero this

theorem burnsideB46_p5_IsShortEl.ne_one {γ : ↥(cayleyGroup K)} (h : burnsideB46_p5_IsShortEl γ) :
    γ ≠ 1 := by
  intro h1
  obtain ⟨x, hx⟩ := burnsideB46_p5_IsShortEl.qr_ne h
  rw [h1] at hx
  exact hx (by simp [qr, burnsideB46_p5_polarQ_self])

theorem burnsideB46_p5_act_F2 {g : ↥(cayleyGroup K)} (hg : g ∈ stabQ (stdF K 2)) (a f : K) :
    g2Act g (q6 a 0 0 0 0 f) = q6 (levi2Mat g 0 0 * a + levi2Mat g 0 1 * f) 0 0 0 0
      (levi2Mat g 1 0 * a + levi2Mat g 1 1 * f) := by
  have hmem : q6 a 0 0 0 0 f ∈ stdF K 2 := mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
  have h1 := upart_act g hmem
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp ((mem_stabQ.mp hg _).mp hmem)
  have e0 := congrFun h1 0
  have e1 := congrFun h1 1
  simp only [upart, Matrix.mulVec, dotProduct, Fin.sum_univ_two, q6_apply_inl0, q6_apply_inr2] at e0 e1
  conv_lhs => rw [q6_eta (g2Act g (q6 a 0 0 0 0 f))]
  rw [b1, b2, b3, b4]
  refine q6_congr ?_ rfl rfl rfl rfl ?_
  · simpa using e0
  · simpa using e1

theorem burnsideB46_p5_act_tL (s : K) (w : Ix3 → K) :
    g2Act (tL s) w = w + q6 (s * w (.inl 2)) 0 0 0 0 (s * w (.inr 0)) := by
  conv_lhs => rw [q6_eta w]
  conv_rhs => rw [q6_eta w]
  rw [g2Act_tL, q6_add']
  simp only [q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2, add_zero]

theorem burnsideB46_p5_conj_tL {g : ↥(cayleyGroup K)} (hg : g ∈ stabQ (stdF K 2)) (s : K) :
    g * tL s * g⁻¹ = tL ((levi2Mat g).det * s) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine cayley_ext fun w => ?_
  have hA := burnsideB46_p5_act_F2 hg
  have e_u2 : g2Act g⁻¹ w (.inl 2) = levi2Mat g 0 1 * w (.inr 0) + levi2Mat g 1 1 * w (.inl 2) := by
    have h1 : polarQ (g2Act g⁻¹ w) (q6 0 0 0 0 0 1) = g2Act g⁻¹ w (.inl 2) := by
      simp [polarQ, q6]
    rw [← h1, ← polarQ_g2Act g, g2Act_apply_inv]
    have h3 := hA 0 1
    simp only [mul_zero, zero_add] at h3
    rw [h3]
    simp [polarQ, q6]
    ring
  have e_v0 : g2Act g⁻¹ w (.inr 0) = levi2Mat g 0 0 * w (.inr 0) + levi2Mat g 1 0 * w (.inl 2) := by
    have h1 : polarQ (g2Act g⁻¹ w) (q6 1 0 0 0 0 0) = g2Act g⁻¹ w (.inr 0) := by
      simp [polarQ, q6]
    rw [← h1, ← polarQ_g2Act g, g2Act_apply_inv]
    have h3 := hA 1 0
    simp only [mul_zero, add_zero, mul_one] at h3
    rw [h3]
    simp [polarQ, q6]
    ring
  rw [g2Act_mul_apply, g2Act_mul_apply, burnsideB46_p5_act_tL, map_add, g2Act_apply_inv, hA, e_u2,
    e_v0, burnsideB46_p5_act_tL, Matrix.det_fin_two]
  congr 1
  refine q6_congr ?_ rfl rfl rfl rfl ?_
  · linear_combination (s * w (.inl 2) * levi2Mat g 0 1 * levi2Mat g 1 0 +
      s * levi2Mat g 0 0 * levi2Mat g 0 1 * w (.inr 0)) * h2
  · linear_combination (s * w (.inr 0) * levi2Mat g 0 1 * levi2Mat g 1 0 +
      s * levi2Mat g 1 0 * levi2Mat g 1 1 * w (.inl 2)) * h2

theorem burnsideB46_p5_levi2_ker_le {g : ↥(cayleyGroup K)} (hgP2 : g ∈ stabQ (stdF K 2))
    (hM : levi2Mat g = 1) : g ∈ U0 K := by
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp [levi2Mat, upart] at h00 h01 h10 h11
  have hu : g ∈ stabV0 K := by
    have hmem : q6 (1 : K) 0 0 0 0 0 ∈ stdF K 2 := mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp ((mem_stabQ.mp hgP2 _).mp hmem)
    rw [mem_stabV0, eu_eq_q6, q6_eta (g2Act g (q6 1 0 0 0 0 0)), h00, b1, b2, b3, b4, h10]
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hu
  have hmem2 : q6 (0 : K) 0 0 0 0 1 ∈ stdF K 2 := mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨-, -, -, c4⟩ := mem_stdF_two.mp ((mem_stabQ.mp hgP2 _).mp hmem2)
  rw [act_v2_decomp α β γ hA] at h01 h11 c4
  simp [q6] at h01 h11 c4
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hdet := det_block_of_fix hA
  rw [h11, c4] at hdet
  have hA22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by linear_combination hdet
  rw [h11, c4] at h01
  have hβ : β = 0 := by simpa using h01
  subst hβ
  have hAu : A = uSL ((A : Matrix (Fin 3) (Fin 3) K) 0 1)
      ((A : Matrix (Fin 3) (Fin 3) K) 0 2) ((A : Matrix (Fin 3) (Fin 3) K) 1 2) := by
    apply Subtype.ext
    have hU : ((uSL ((A : Matrix (Fin 3) (Fin 3) K) 0 1) ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
        ((A : Matrix (Fin 3) (Fin 3) K) 1 2) : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
        !![1, (A : Matrix (Fin 3) (Fin 3) K) 0 1, (A : Matrix (Fin 3) (Fin 3) K) 0 2;
          0, 1, (A : Matrix (Fin 3) (Fin 3) K) 1 2; 0, 0, 1] := rfl
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, h11, c4, hA22]
  change g2X ![α, 0, 0] * g2Y ![0, 0, γ] * g2A A ∈ U0 K
  rw [hAu]
  exact (U0 K).mul_mem ((U0 K).mul_mem (g2X_mem_U0 α) (g2Y_mem_U0 0 γ)) (g2A_mem_U0 _ _ _)


theorem burnsideB46_p5_tL_zero : tL (0 : K) = 1 :=
  cayley_eq_one fun w => by
    rw [q6_eta w, g2Act_tL]
    simp

theorem burnsideB46_p5_tL_mul_self (s : K) : tL s * tL s = 1 := by
  rw [tL_mul, CharTwo.add_self_eq_zero, burnsideB46_p5_tL_zero]

theorem burnsideB46_p5_tL_inj {s t : K} (h : tL s = tL t) : s = t := by
  have h1 := congrArg (fun g : ↥(cayleyGroup K) => g2Act g (q6 0 0 1 0 0 0) (.inl 0)) h
  simp only [g2Act_tL] at h1
  simpa [q6] using h1

@[expose] def burnsideB46_p5_D (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) where
  carrier := {g | ∃ s : K, g = tL s}
  one_mem' := ⟨0, burnsideB46_p5_tL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, tL_mul s t⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨s, inv_eq_of_mul_eq_one_right (burnsideB46_p5_tL_mul_self s)⟩

theorem burnsideB46_p5_mem_D {g : ↥(cayleyGroup K)} :
    g ∈ burnsideB46_p5_D K ↔ ∃ s : K, g = tL s := Iff.rfl

theorem burnsideB46_p5_exists_tL_sub {s : K} (hs : s ≠ 0) {x : Ix3 → K} (hx : x ∈ stdF K 2) :
    ∃ y, g2Act (tL s) y - y = x := by
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hx
  refine ⟨q6 0 0 (x (.inl 0) / s) (x (.inr 2) / s) 0 0, ?_⟩
  rw [g2Act_tL]
  conv_rhs => rw [q6_eta x]
  rw [b1, b2, b3, b4]
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6] <;> field_simp

theorem burnsideB46_p5_normalizer_D :
    Subgroup.normalizer ((burnsideB46_p5_D K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) =
      stabQ (stdF K 2) := by
  ext g
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    obtain ⟨s', hs'⟩ : g * tL 1 * g⁻¹ ∈ burnsideB46_p5_D K := (h (tL 1)).mp ⟨1, rfl⟩
    have hs0 : s' ≠ 0 := by
      rintro rfl
      rw [burnsideB46_p5_tL_zero] at hs'
      exact burnsideB46_p5_IsLongEl.ne_one ⟨g, rfl⟩ hs'
    have hact : ∀ z, g2Act (tL s') (g2Act g z) = g2Act g (g2Act (tL 1) z) := fun z => by
      rw [← hs', g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    rw [mem_stabQ]
    intro w
    constructor
    · intro hw
      obtain ⟨z, hz⟩ := burnsideB46_p5_exists_tL_sub (one_ne_zero (α := K)) hw
      have : g2Act g w = g2Act (tL s') (g2Act g z) - g2Act g z := by
        rw [hact, ← hz, map_sub]
      rw [this]
      exact g2Act_tL_sub_mem s' _
    · intro hw
      obtain ⟨y, hy⟩ := burnsideB46_p5_exists_tL_sub hs0 hw
      have : w = g2Act (tL 1) (g2Act g⁻¹ y) - g2Act g⁻¹ y := by
        have h1 := hact (g2Act g⁻¹ y)
        rw [g2Act_apply_inv] at h1
        rw [← g2Act_inv_apply g w, ← hy, map_sub, h1, g2Act_inv_apply]
      rw [this]
      exact g2Act_tL_sub_mem 1 _
  · intro hg h
    constructor
    · rintro ⟨s, rfl⟩
      rw [burnsideB46_p5_conj_tL hg]
      exact ⟨_, rfl⟩
    · rintro ⟨t, ht⟩
      have hg' := (stabQ (stdF K 2)).inv_mem hg
      have : h = g⁻¹ * tL t * g⁻¹⁻¹ := by
        rw [← ht]
        group
      rw [this, burnsideB46_p5_conj_tL hg']
      exact ⟨_, rfl⟩

theorem burnsideB46_p5_centralizer_D :
    Subgroup.centralizer ((burnsideB46_p5_D K : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) =
      stabQ2Det K := by
  ext g
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hcomm : ∀ y ∈ burnsideB46_p5_D K, g * y * g⁻¹ = y := fun y hy => by
      rw [mul_inv_eq_iff_eq_mul, h y hy]
    have hg : g ∈ stabQ (stdF K 2) := by
      rw [← burnsideB46_p5_normalizer_D, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hcomm x hx]
        exact hx
      · intro hx
        have e : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
          have hy := hcomm _ hx
          calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * (g * (g * x * g⁻¹) * g⁻¹) * g := by rw [hy]
            _ = g * x * g⁻¹ := by group
        have e2 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [e2, e]
        exact hx
    refine ⟨hg, ?_⟩
    have h1 := burnsideB46_p5_conj_tL hg 1
    rw [hcomm (tL 1) ⟨1, rfl⟩] at h1
    have h3 := burnsideB46_p5_tL_inj h1
    rw [mul_one] at h3
    exact h3.symm
  · rintro ⟨hg, hdet⟩ y ⟨s, rfl⟩
    have h1 := burnsideB46_p5_conj_tL hg s
    rw [hdet, one_mul] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm

theorem burnsideB46_p5_two_elt_mem {G : Type*} [Group G] {H N : Subgroup G} (hNH : N ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (N : Set G)) (hodd : ¬ 2 ∣ N.relIndex H) {x : G}
    (hx : x ∈ H) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ N := by
  haveI : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hnorm
  have h1 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this]
    rfl
  have h2 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) ∣ N.relIndex H :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (N.relIndex H) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  exact (Subgroup.mem_subgroupOf.mp h4)

theorem burnsideB46_p5_exists_sl2E1 [Finite K] (h4 : 4 ≤ Nat.card K)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ s ∈ sl2E1 K, levi2Mat s = (M : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (by omega : 2 < Nat.card K)
  have hle : sl2E1 K ≤ perfectCore (stabQ (stdF K 2)) :=
    le_perfectCore_of_perfect sl2E1_le_stabQ (sl2E1_perfect hc0 hc1)
  have htop : ((sl2E1 K).subgroupOf (perfectCore (stabQ (stdF K 2)))).map (levi2 (F := K)) = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, t, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · refine ⟨⟨g2Y ![0, t, 0], hle (Subgroup.subset_closure ⟨t, Or.inr rfl⟩)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨t, Or.inr rfl⟩), Subtype.ext ?_⟩
      rw [levi2_apply, levi2Mat_y1, CFSG.LinearGroups.coe_transvection]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    · refine ⟨⟨g2X ![0, t, 0], hle (Subgroup.subset_closure ⟨t, Or.inl rfl⟩)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨t, Or.inl rfl⟩), Subtype.ext ?_⟩
      rw [levi2_apply, levi2Mat_x1, CFSG.LinearGroups.coe_transvection]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    · exact absurd rfl hij
  have hM : M ∈ ((sl2E1 K).subgroupOf (perfectCore (stabQ (stdF K 2)))).map (levi2 (F := K)) := by
    rw [htop]
    exact Subgroup.mem_top M
  obtain ⟨e, he, rfl⟩ := hM
  exact ⟨e.1, Subgroup.mem_subgroupOf.mp he, rfl⟩

theorem burnsideB46_p5_twoPrimeResidual [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h4 : 4 ≤ Nat.card K) :
    CFSG.Quasithin.twoPrimeResidual (stabQ (stdF K 2)) = stabQ2Det K := by
  have hfin := finite_cayleyGroup (F := K)
  apply le_antisymm
  · refine iInf₂_le (stabQ2Det K) ⟨fun g hg => hg.1, ?_, ?_⟩
    · have key : ∀ g ∈ stabQ (stdF K 2), ∀ h ∈ stabQ2Det K, g * h * g⁻¹ ∈ stabQ2Det K := by
        rintro g hg h ⟨hhP, hhdet⟩
        have hgi := (stabQ (stdF K 2)).inv_mem hg
        refine ⟨(stabQ (stdF K 2)).mul_mem ((stabQ (stdF K 2)).mul_mem hg hhP) hgi, ?_⟩
        rw [levi2Mat_mul hgi, levi2Mat_mul hhP, Matrix.det_mul, Matrix.det_mul, hhdet, mul_one]
        exact det_levi2Mat_inv hg
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact key g hg h
      · intro hh
        have := key g⁻¹ ((stabQ (stdF K 2)).inv_mem hg) _ hh
        simpa [mul_assoc] using this
    · let ν₀ : ↥(stabQ (stdF K 2)) →* K :=
        { toFun := fun g => (levi2Mat g.1).det
          map_one' := by simp [levi2Mat_one]
          map_mul' := fun a b => by
            change (levi2Mat (a.1 * b.1)).det = _
            rw [levi2Mat_mul b.2, Matrix.det_mul] }
      have hker : ν₀.toHomUnits.ker = (stabQ2Det K).subgroupOf (stabQ (stdF K 2)) := by
        ext g
        simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          refine ⟨g.2, ?_⟩
          have := congrArg Units.val h
          simpa [ν₀] using this
        · rintro ⟨-, h⟩
          apply Units.ext
          simpa [ν₀] using h
      have hidx : (stabQ2Det K).relIndex (stabQ (stdF K 2)) = Nat.card ν₀.toHomUnits.range := by
        rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
      rw [hidx]
      intro h2
      have hdvd : Nat.card ν₀.toHomUnits.range ∣ Nat.card Kˣ :=
        Subgroup.card_subgroup_dvd_card _
      rw [Nat.card_units, hK] at hdvd
      have h3 := h2.trans hdvd
      have h5 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have h6 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨hNH, hnorm, hodd⟩ := hN
    have h2el : ∀ x ∈ stabQ (stdF K 2), (∃ k, x ^ 2 ^ k = 1) → x ∈ N := fun x hx ⟨k, hk⟩ =>
      burnsideB46_p5_two_elt_mem hNH hnorm hodd hx hk
    have hsl : sl2E1 K ≤ N := by
      rw [sl2E1, Subgroup.closure_le]
      rintro g ⟨t, rfl | rfl⟩
      · exact h2el _ (sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inl rfl⟩))
          ⟨1, by rw [pow_one, pow_two, g2X_mul_self]⟩
      · exact h2el _ (sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inr rfl⟩))
          ⟨1, by rw [pow_one, pow_two, g2Y_mul_self]⟩
    rintro g ⟨hgP, hgdet⟩
    obtain ⟨s, hs, hsM⟩ := burnsideB46_p5_exists_sl2E1 h4 ⟨levi2Mat g, hgdet⟩
    have hsP : s ∈ stabQ (stdF K 2) := sl2E1_le_stabQ hs
    have hsi := (stabQ (stdF K 2)).inv_mem hsP
    have hgsP : g * s⁻¹ ∈ stabQ (stdF K 2) := (stabQ (stdF K 2)).mul_mem hgP hsi
    have hker : g * s⁻¹ ∈ U0 K := by
      refine burnsideB46_p5_levi2_ker_le hgsP ?_
      have h1 := levi2Mat_mul (g := s) hsi
      rw [mul_inv_cancel, levi2Mat_one] at h1
      rw [levi2Mat_mul hsi]
      have hsM' : levi2Mat s = levi2Mat g := hsM
      rw [← hsM']
      exact h1.symm
    obtain ⟨k, hk⟩ := isPGroup_U0 (F := K) ⟨g * s⁻¹, hker⟩
    have hgs : g * s⁻¹ ∈ N := h2el _ hgsP ⟨k, by simpa using congrArg Subtype.val hk⟩
    have := N.mul_mem hgs (hsl hs)
    simpa using this


section Transfer

variable {M N : Type*} [Group M] [Group N]

theorem burnsideB46_p5_tpr_map_aux (φ : M →* N) (hφ : Function.Injective φ) {X Y : Subgroup M}
    (h : Y ≤ X ∧ X ≤ Subgroup.normalizer (Y : Set M) ∧ ¬ 2 ∣ Y.relIndex X) :
    Y.map φ ≤ X.map φ ∧ X.map φ ≤ Subgroup.normalizer ((Y.map φ : Subgroup N) : Set N) ∧
      ¬ 2 ∣ (Y.map φ).relIndex (X.map φ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Subgroup.map_mono h1, ?_, by rwa [Subgroup.relIndex_map_map_of_injective _ _ hφ]⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp (h2 hx) y).mp hy, ?_⟩
    simp
  · rintro ⟨y, hy, hyz⟩
    have : z = φ (x⁻¹ * y * x) := by
      rw [map_mul, map_mul, map_inv, hyz]
      group
    rw [this]
    refine ⟨x⁻¹ * y * x, ?_, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (h2 (X.inv_mem hx)) y).mp hy
    simpa using this

theorem burnsideB46_p5_tpr_comap_aux (φ : M →* N) (hφ : Function.Injective φ) {X : Subgroup M}
    {Y : Subgroup N}
    (h : Y ≤ X.map φ ∧ X.map φ ≤ Subgroup.normalizer (Y : Set N) ∧ ¬ 2 ∣ Y.relIndex (X.map φ)) :
    (Y.comap φ ⊓ X) ≤ X ∧ X ≤ Subgroup.normalizer ((Y.comap φ ⊓ X : Subgroup M) : Set M) ∧
      ¬ 2 ∣ (Y.comap φ ⊓ X).relIndex X ∧ (Y.comap φ ⊓ X).map φ = Y := by
  obtain ⟨h1, h2, h3⟩ := h
  have hmap : (Y.comap φ ⊓ X).map φ = Y := by
    rw [Subgroup.map_inf _ _ _ hφ, Subgroup.map_comap_eq]
    ext y
    constructor
    · rintro ⟨⟨_, hy⟩, _⟩
      exact hy
    · intro hy
      have hyX : y ∈ X.map φ := h1 hy
      obtain ⟨x, hxX, rfl⟩ := hyX
      exact ⟨⟨⟨x, rfl⟩, hy⟩, ⟨x, hxX, rfl⟩⟩
  refine ⟨inf_le_right, ?_, ?_, hmap⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hn := Subgroup.mem_normalizer_iff.mp (h2 ⟨x, hx, rfl⟩)
    constructor
    · rintro ⟨hzY, hzX⟩
      refine ⟨?_, X.mul_mem (X.mul_mem hx hzX) (X.inv_mem hx)⟩
      show φ (x * z * x⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact (hn (φ z)).mp hzY
    · rintro ⟨hzY, hzX⟩
      have hzX' : z ∈ X := by
        have := X.mul_mem (X.mul_mem (X.inv_mem hx) hzX) hx
        simpa [mul_assoc] using this
      refine ⟨?_, hzX'⟩
      have h5 : φ (x * z * x⁻¹) ∈ Y := hzY
      rw [map_mul, map_mul, map_inv] at h5
      exact (hn (φ z)).mpr h5
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, hmap]
    exact h3

theorem burnsideB46_p5_tpr_map (φ : M →* N) (hφ : Function.Injective φ) (X : Subgroup M) :
    CFSG.Quasithin.twoPrimeResidual (X.map φ) = (CFSG.Quasithin.twoPrimeResidual X).map φ := by
  unfold CFSG.Quasithin.twoPrimeResidual
  apply le_antisymm
  · intro y hy
    have hq : ∀ N' : Subgroup N, (N' ≤ X.map φ ∧ X.map φ ≤ Subgroup.normalizer (N' : Set N) ∧
        ¬ 2 ∣ N'.relIndex (X.map φ)) → y ∈ N' := fun N' hN' =>
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hy N') hN'
    have hyX : y ∈ X.map φ := hq (X.map φ) ⟨le_rfl, Subgroup.le_normalizer, by
      rw [Subgroup.relIndex_self]
      omega⟩
    obtain ⟨x, hxX, rfl⟩ := hyX
    refine ⟨x, Subgroup.mem_iInf.mpr fun Y => Subgroup.mem_iInf.mpr fun hY => ?_, rfl⟩
    exact (Subgroup.mem_map_iff_mem hφ).mp (hq (Y.map φ) (burnsideB46_p5_tpr_map_aux φ hφ hY))
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_iInf.mpr fun N' => Subgroup.mem_iInf.mpr fun hN' => ?_
    obtain ⟨h1, h2, h3, h4⟩ := burnsideB46_p5_tpr_comap_aux φ hφ hN'
    have hxN : x ∈ N'.comap φ ⊓ X :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (N'.comap φ ⊓ X)) ⟨h1, h2, h3⟩
    exact hxN.1

end Transfer

theorem burnsideB46_p5_tL_sub_smul (s : K) (v : Ix3 → K) :
    g2Act (tL s) v - v = s • (g2Act (tL 1) v - v) := by
  rw [burnsideB46_p5_act_tL, burnsideB46_p5_act_tL]
  funext j
  rcases j with j | j <;> fin_cases j <;> simp [q6]

theorem burnsideB46_p5_tv_sub_smul (i j : Fin 3) (hij : i ≠ j) (s : K) (v : Ix3 → K) :
    g2Act (g2A (tv i j hij s)) v - v = s • (g2Act (g2A (tv i j hij 1)) v - v) := by
  rw [g2Act_tv, g2Act_tv]
  funext k
  simp [eu, ev, Pi.single_apply]
  split_ifs <;> ring

theorem burnsideB46_p5_conj_tL_eq_tv {x : ↥(cayleyGroup K)} (i j : Fin 3) (hij : i ≠ j)
    (hx : x * tL 1 * x⁻¹ = g2A (tv i j hij 1)) (s : K) :
    x * tL s * x⁻¹ = g2A (tv i j hij s) := by
  refine cayley_ext fun w => ?_
  have h1 : g2Act (tL s) (g2Act x⁻¹ w) = g2Act x⁻¹ w + s • (g2Act (tL 1) (g2Act x⁻¹ w) - g2Act x⁻¹ w) := by
    rw [← burnsideB46_p5_tL_sub_smul]
    abel
  have h2 : g2Act (g2A (tv i j hij s)) w = w + s • (g2Act (g2A (tv i j hij 1)) w - w) := by
    rw [← burnsideB46_p5_tv_sub_smul]
    abel
  rw [g2Act_mul_apply, g2Act_mul_apply, h1, h2, map_add, Vol2.Ch11.G2Q8.g2Act_smul, map_sub, g2Act_apply_inv,
    ← hx, g2Act_mul_apply, g2Act_mul_apply]

theorem burnsideB46_p5_tL_apply_eq (s : K) (v : Ix3 → K) :
    g2Act (tL s) v = v + s • (g2Act (tL 1) v - v) := by
  rw [← burnsideB46_p5_tL_sub_smul]
  abel

theorem burnsideB46_p5_comm_tL {γ : ↥(cayleyGroup K)} {s₀ : K} (hs₀ : s₀ ≠ 0)
    (h : γ * tL s₀ = tL s₀ * γ) (s : K) : γ * tL s = tL s * γ := by
  have key : ∀ w, g2Act γ (g2Act (tL 1) w - w) = g2Act (tL 1) (g2Act γ w) - g2Act γ w := by
    intro w
    have h1 := congrArg (fun g : ↥(cayleyGroup K) => g2Act g w) h
    rw [g2Act_mul_apply, g2Act_mul_apply, burnsideB46_p5_tL_apply_eq s₀ w,
      burnsideB46_p5_tL_apply_eq s₀ (g2Act γ w), map_add, Vol2.Ch11.G2Q8.g2Act_smul] at h1
    exact smul_right_injective (Ix3 → K) hs₀ (add_left_cancel h1)
  refine cayley_ext fun w => ?_
  rw [g2Act_mul_apply, g2Act_mul_apply, burnsideB46_p5_tL_apply_eq s w,
    burnsideB46_p5_tL_apply_eq s (g2Act γ w), map_add, Vol2.Ch11.G2Q8.g2Act_smul, key]

@[expose] def burnsideB46_p5_Dconj (K : Type) [Field K] [CharP K 2] (h : ↥(cayleyGroup K)) :
    Subgroup ↥(cayleyGroup K) :=
  (burnsideB46_p5_D K).map (MulAut.conj h).toMonoidHom

theorem burnsideB46_p5_mem_Dconj {h γ : ↥(cayleyGroup K)} :
    γ ∈ burnsideB46_p5_Dconj K h ↔ ∃ s : K, γ = h * tL s * h⁻¹ := by
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨tL s, ⟨s, rfl⟩, rfl⟩

theorem burnsideB46_p5_normalizer_Dconj (h : ↥(cayleyGroup K)) :
    Subgroup.normalizer ((burnsideB46_p5_Dconj K h : Subgroup ↥(cayleyGroup K)) :
      Set ↥(cayleyGroup K)) = (stabQ (stdF K 2)).map (MulAut.conj h).toMonoidHom := by
  unfold burnsideB46_p5_Dconj
  rw [← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj h).bijective,
    burnsideB46_p5_normalizer_D]

theorem burnsideB46_p5_centralizer_Dconj (h : ↥(cayleyGroup K)) :
    Subgroup.centralizer ((burnsideB46_p5_Dconj K h : Subgroup ↥(cayleyGroup K)) :
      Set ↥(cayleyGroup K)) = (stabQ2Det K).map (MulAut.conj h).toMonoidHom := by
  ext g
  rw [← burnsideB46_p5_centralizer_D]
  constructor
  · intro hg
    refine ⟨h⁻¹ * g * h, ?_, by show h * (h⁻¹ * g * h) * h⁻¹ = g; group⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro y ⟨s, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hg (h * tL s * h⁻¹)
      (burnsideB46_p5_mem_Dconj.mpr ⟨s, rfl⟩)
    calc tL s * (h⁻¹ * g * h) = h⁻¹ * ((h * tL s * h⁻¹) * g) * h := by group
      _ = h⁻¹ * (g * (h * tL s * h⁻¹)) * h := by rw [h1]
      _ = h⁻¹ * g * h * tL s := by group
  · rintro ⟨g', hg', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Dconj.mp hy
    have h1 := Subgroup.mem_centralizer_iff.mp hg' (tL s) ⟨s, rfl⟩
    change h * tL s * h⁻¹ * (h * g' * h⁻¹) = h * g' * h⁻¹ * (h * tL s * h⁻¹)
    calc h * tL s * h⁻¹ * (h * g' * h⁻¹) = h * (tL s * g') * h⁻¹ := by group
      _ = h * (g' * tL s) * h⁻¹ := by rw [h1]
      _ = h * g' * h⁻¹ * (h * tL s * h⁻¹) := by group

theorem burnsideB46_p5_centralizer_eq_tpr [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h4 : 4 ≤ Nat.card K) (h : ↥(cayleyGroup K)) :
    Subgroup.centralizer ((burnsideB46_p5_Dconj K h : Subgroup ↥(cayleyGroup K)) :
      Set ↥(cayleyGroup K)) =
      CFSG.Quasithin.twoPrimeResidual (Subgroup.normalizer ((burnsideB46_p5_Dconj K h :
        Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K))) := by
  rw [burnsideB46_p5_centralizer_Dconj, burnsideB46_p5_normalizer_Dconj,
    burnsideB46_p5_tpr_map _ (MulAut.conj h).injective, burnsideB46_p5_twoPrimeResidual hn hK h4]

theorem burnsideB46_p5_centralizer_single_Dconj (h : ↥(cayleyGroup K)) {s₀ : K} (hs₀ : s₀ ≠ 0) :
    Subgroup.centralizer ({h * tL s₀ * h⁻¹} : Set ↥(cayleyGroup K)) =
      Subgroup.centralizer ((burnsideB46_p5_Dconj K h : Subgroup ↥(cayleyGroup K)) :
        Set ↥(cayleyGroup K)) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg y hy
    obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Dconj.mp hy
    have h1 := hg (h * tL s₀ * h⁻¹) rfl
    have h2 : (h⁻¹ * g * h) * tL s₀ = tL s₀ * (h⁻¹ * g * h) := by
      calc h⁻¹ * g * h * tL s₀ = h⁻¹ * (g * (h * tL s₀ * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * tL s₀ * h⁻¹) * g) * h := by rw [h1]
        _ = tL s₀ * (h⁻¹ * g * h) := by group
    have h3 := burnsideB46_p5_comm_tL hs₀ h2 s
    calc h * tL s * h⁻¹ * g = h * (tL s * (h⁻¹ * g * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * g * h) * tL s) * h⁻¹ := by rw [← h3]
      _ = g * (h * tL s * h⁻¹) := by group
  · intro hg y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hg _ (burnsideB46_p5_mem_Dconj.mpr ⟨s₀, rfl⟩)


theorem burnsideB46_p5_smul_e0 (s : K) : s • (![1, 0, 0] : Fin 3 → K) = ![s, 0, 0] := by
  funext i
  fin_cases i <;> simp

theorem burnsideB46_p5_xs_mul (s t : K) :
    g2X ![s, 0, 0] * g2X ![t, 0, 0] = g2X ![s + t, 0, 0] := by
  have := g2X_smul_mul (![1, 0, 0] : Fin 3 → K) s t
  rwa [burnsideB46_p5_smul_e0, burnsideB46_p5_smul_e0, burnsideB46_p5_smul_e0] at this

theorem burnsideB46_p5_xs_zero : g2X ![(0 : K), 0, 0] = 1 := by
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  rw [hz3, g2X_zero]

@[expose] def burnsideB46_p5_Xe0 (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) where
  carrier := {g | ∃ t : K, g = g2X ![t, 0, 0]}
  one_mem' := ⟨0, burnsideB46_p5_xs_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, burnsideB46_p5_xs_mul s t⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨s, JonesParshall.g2X_inv _⟩

theorem burnsideB46_p5_mem_Xe0 {g : ↥(cayleyGroup K)} :
    g ∈ burnsideB46_p5_Xe0 K ↔ ∃ t : K, g = g2X ![t, 0, 0] := Iff.rfl

@[expose] def burnsideB46_p5_Xconj (K : Type) [Field K] [CharP K 2] (h : ↥(cayleyGroup K)) :
    Subgroup ↥(cayleyGroup K) :=
  (burnsideB46_p5_Xe0 K).map (MulAut.conj h).toMonoidHom

theorem burnsideB46_p5_mem_Xconj {h γ : ↥(cayleyGroup K)} :
    γ ∈ burnsideB46_p5_Xconj K h ↔ ∃ t : K, γ = h * g2X ![t, 0, 0] * h⁻¹ := by
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨g2X ![t, 0, 0], ⟨t, rfl⟩, rfl⟩


end P5

section V

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p5_pi_cg [CharP K 2] (γ : ↥(quasithinG2 K)) :
    π γ = burnsideB46_pi π (burnsideB46_cg γ) := by
  rw [burnsideB46_pi_apply, MulEquiv.symm_apply_apply]

theorem burnsideB46_p5_cg_apply [CharP K 2] (γ : ↥(quasithinG2 K)) (y : quasithinZorn K) :
    ((burnsideB46_cg γ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) y =
      (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) y := rfl

theorem burnsideB46_p5_isLongRootSub_iff [CharP K 2] [Finite K] {Z : Subgroup (MulAut V)} :
    IsLongRootSub π Z ↔ ∃ h : ↥(cayleyGroup K), ∀ ψ : MulAut V,
      ψ ∈ Z ↔ ∃ s : K, ψ = burnsideB46_pi π (h * tL s * h⁻¹) := by
  constructor
  · rintro ⟨i, j, hij, g, hg⟩
    obtain ⟨x, hx⟩ := burnsideB46_p5_tv_conj_tL i j hij (one_ne_zero (α := K))
    refine ⟨burnsideB46_cg g * x, fun ψ => ?_⟩
    rw [hg]
    constructor
    · rintro ⟨c, φ, hφ, rfl⟩
      refine ⟨c, ?_⟩
      have h1 : burnsideB46_cg φ = g2A (tv i j hij c) :=
        Subtype.ext (LinearEquiv.ext fun y =>
          (hφ y).trans (burnsideB46_p5_longRootFn_eq i j hij c y))
      have h2 := burnsideB46_p5_conj_tL_eq_tv i j hij hx.symm c
      rw [burnsideB46_p5_pi_cg φ, burnsideB46_p5_pi_cg g, h1, ← h2]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨s, rfl⟩
      refine ⟨s, burnsideB46_cg.symm (g2A (tv i j hij s)), fun y => ?_, ?_⟩
      · have := burnsideB46_p5_cg_apply (burnsideB46_cg.symm (g2A (tv i j hij s))) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm.trans (burnsideB46_p5_longRootFn_eq i j hij s y).symm
      · have h2 := burnsideB46_p5_conj_tL_eq_tv i j hij hx.symm s
        rw [burnsideB46_p5_pi_cg (burnsideB46_cg.symm (g2A (tv i j hij s))),
          MulEquiv.apply_symm_apply, burnsideB46_p5_pi_cg g, ← h2]
        simp only [map_mul, map_inv]
        group
  · rintro ⟨h, hh⟩
    refine ⟨0, 2, by decide, burnsideB46_cg.symm h, fun ψ => ?_⟩
    rw [hh]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s, burnsideB46_cg.symm (tL s), fun y => ?_, ?_⟩
      · have := burnsideB46_p5_cg_apply (burnsideB46_cg.symm (tL s)) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm.trans (burnsideB46_p5_longRootFn_eq 0 2 (by decide) s y).symm
      · rw [burnsideB46_p5_pi_cg (burnsideB46_cg.symm (tL s)), MulEquiv.apply_symm_apply,
          burnsideB46_p5_pi_cg (burnsideB46_cg.symm h), MulEquiv.apply_symm_apply]
        simp only [map_mul, map_inv]
    · rintro ⟨c, φ, hφ, rfl⟩
      refine ⟨c, ?_⟩
      have h1 : burnsideB46_cg φ = tL c :=
        Subtype.ext (LinearEquiv.ext fun y =>
          (hφ y).trans (burnsideB46_p5_longRootFn_eq 0 2 (by decide) c y))
      rw [burnsideB46_p5_pi_cg φ, burnsideB46_p5_pi_cg (burnsideB46_cg.symm h), h1,
        MulEquiv.apply_symm_apply]
      simp only [map_mul, map_inv]

theorem burnsideB46_p5_isShortRootSub_iff [CharP K 2] [Finite K] {R : Subgroup (MulAut V)} :
    IsShortRootSub π R ↔ ∃ h : ↥(cayleyGroup K), ∀ ψ : MulAut V,
      ψ ∈ R ↔ ∃ t : K, ψ = burnsideB46_pi π (h * g2X ![t, 0, 0] * h⁻¹) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨burnsideB46_cg g, fun ψ => ?_⟩
    rw [hg]
    constructor
    · rintro ⟨c, φ, hφ, rfl⟩
      refine ⟨c, ?_⟩
      have h1 : burnsideB46_cg φ = g2X ![c, 0, 0] :=
        Subtype.ext (LinearEquiv.ext fun y =>
          (hφ y).trans ((burnsideB46_shortRootFn_eq c y).trans (g2X_apply ![c, 0, 0] y).symm))
      rw [burnsideB46_p5_pi_cg φ, burnsideB46_p5_pi_cg g, h1]
      simp only [map_mul, map_inv]
    · rintro ⟨t, rfl⟩
      refine ⟨t, burnsideB46_cg.symm (g2X ![t, 0, 0]), fun y => ?_, ?_⟩
      · have := burnsideB46_p5_cg_apply (burnsideB46_cg.symm (g2X ![t, 0, 0])) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm.trans ((g2X_apply ![t, 0, 0] y).trans (burnsideB46_shortRootFn_eq t y).symm)
      · rw [burnsideB46_p5_pi_cg (burnsideB46_cg.symm (g2X ![t, 0, 0])), MulEquiv.apply_symm_apply,
          burnsideB46_p5_pi_cg g]
        simp only [map_mul, map_inv]
  · rintro ⟨h, hh⟩
    refine ⟨burnsideB46_cg.symm h, fun ψ => ?_⟩
    rw [hh]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, burnsideB46_cg.symm (g2X ![t, 0, 0]), fun y => ?_, ?_⟩
      · have := burnsideB46_p5_cg_apply (burnsideB46_cg.symm (g2X ![t, 0, 0])) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm.trans ((g2X_apply ![t, 0, 0] y).trans (burnsideB46_shortRootFn_eq t y).symm)
      · rw [burnsideB46_p5_pi_cg (burnsideB46_cg.symm (g2X ![t, 0, 0])), MulEquiv.apply_symm_apply,
          burnsideB46_p5_pi_cg (burnsideB46_cg.symm h), MulEquiv.apply_symm_apply]
        simp only [map_mul, map_inv]
    · rintro ⟨c, φ, hφ, rfl⟩
      refine ⟨c, ?_⟩
      have h1 : burnsideB46_cg φ = g2X ![c, 0, 0] :=
        Subtype.ext (LinearEquiv.ext fun y =>
          (hφ y).trans ((burnsideB46_shortRootFn_eq c y).trans (g2X_apply ![c, 0, 0] y).symm))
      rw [burnsideB46_p5_pi_cg φ, burnsideB46_p5_pi_cg (burnsideB46_cg.symm h), h1,
        MulEquiv.apply_symm_apply]
      simp only [map_mul, map_inv]

theorem burnsideB46_p5_L_inf_centralizer [CharP K 2] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (S : Set ↥(cayleyGroup K)) :
    L ⊓ Subgroup.centralizer (burnsideB46_pi π '' S) =
      (Subgroup.centralizer S).map (burnsideB46_pi π) := by
  ext l
  constructor
  · rintro ⟨hl, hc⟩
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    refine ⟨γ, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s hs
    have := Subgroup.mem_centralizer_iff.mp hc (burnsideB46_pi π s) ⟨s, hs, rfl⟩
    exact burnsideB46_pi_injective H (by rw [map_mul, map_mul]; exact this)
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨burnsideB46_pi_mem_L H γ, ?_⟩
    show burnsideB46_pi π γ ∈ Subgroup.centralizer (burnsideB46_pi π '' S)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (burnsideB46_pi π) (Subgroup.mem_centralizer_iff.mp hγ s hs)

theorem burnsideB46_p5_L_inf_normalizer [CharP K 2] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (S : Subgroup ↥(cayleyGroup K)) :
    L ⊓ Subgroup.normalizer ((S.map (burnsideB46_pi π) : Subgroup (MulAut V)) : Set (MulAut V)) =
      (Subgroup.normalizer (S : Set ↥(cayleyGroup K))).map (burnsideB46_pi π) := by
  have hcomap : (Subgroup.normalizer ((S.map (burnsideB46_pi π) : Subgroup (MulAut V)) :
      Set (MulAut V))).comap (burnsideB46_pi π) = Subgroup.normalizer (S : Set ↥(cayleyGroup K)) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range _ S),
      Subgroup.comap_map_eq_self_of_injective (burnsideB46_pi_injective H)]
  ext l
  constructor
  · rintro ⟨hl, hn⟩
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    refine ⟨γ, ?_, rfl⟩
    rw [← hcomap]
    exact hn
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨burnsideB46_pi_mem_L H γ, ?_⟩
    have : γ ∈ (Subgroup.normalizer ((S.map (burnsideB46_pi π) : Subgroup (MulAut V)) :
        Set (MulAut V))).comap (burnsideB46_pi π) := by
      rw [hcomap]
      exact hγ
    exact this

theorem burnsideB46_p5_part5_core [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) {Z₂ P₂ : Subgroup (MulAut V)} (hZ₂ : IsLongRootSub π Z₂)
    (hP₂ : P₂ = L ⊓ Subgroup.normalizer (Z₂ : Set (MulAut V))) {z : MulAut V} (hz : z ∈ Z₂)
    (hz1 : z ≠ 1) :
    (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
        ∃ l ∈ L, x = l * z * l⁻¹) ∧
      (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * r * l⁻¹) ∧
        ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
        ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
      (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
        L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = CFSG.Quasithin.twoPrimeResidual P₂) := by
  have hinj := burnsideB46_pi_injective H
  have hK : Nat.card K = 2 ^ n := H.card
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨h₂, hh₂⟩ := burnsideB46_p5_isLongRootSub_iff.mp hZ₂
  obtain ⟨s₀, hz0⟩ := (hh₂ z).mp hz
  have hs₀ : s₀ ≠ 0 := by
    rintro rfl
    apply hz1
    rw [hz0, burnsideB46_p5_tL_zero]
    simp
  have hZ₂eq : Z₂ = (burnsideB46_p5_Dconj K h₂).map (burnsideB46_pi π) := by
    ext ψ
    rw [hh₂ ψ]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, burnsideB46_p5_mem_Dconj.mpr ⟨s, rfl⟩, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Dconj.mp hγ
      exact ⟨s, rfl⟩
  obtain ⟨g₂, hg₂⟩ : burnsideB46_p5_IsLongEl (h₂ * tL s₀ * h₂⁻¹) :=
    burnsideB46_p5_isLongEl_iff.mpr ⟨h₂, s₀, hs₀, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨Z, hZ, hxZ, hx1⟩
      obtain ⟨h, hh⟩ := burnsideB46_p5_isLongRootSub_iff.mp hZ
      obtain ⟨s, hs⟩ := (hh x).mp hxZ
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hx1
        rw [hs, burnsideB46_p5_tL_zero]
        simp
      obtain ⟨g₁, hg₁⟩ : burnsideB46_p5_IsLongEl (h * tL s * h⁻¹) :=
        burnsideB46_p5_isLongEl_iff.mpr ⟨h, s, hs0, rfl⟩
      refine ⟨burnsideB46_pi π (g₁ * g₂⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
      rw [hs, hz0, hg₁, hg₂]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
      refine ⟨(burnsideB46_p5_Dconj K (γ * h₂)).map (burnsideB46_pi π), ?_, ?_, ?_⟩
      · refine burnsideB46_p5_isLongRootSub_iff.mpr ⟨γ * h₂, fun ψ => ?_⟩
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Dconj.mp hy
          exact ⟨s, rfl⟩
        · rintro ⟨s, rfl⟩
          exact ⟨_, burnsideB46_p5_mem_Dconj.mpr ⟨s, rfl⟩, rfl⟩
      · rw [hz0]
        refine ⟨(γ * h₂) * tL s₀ * (γ * h₂)⁻¹, burnsideB46_p5_mem_Dconj.mpr ⟨s₀, rfl⟩, ?_⟩
        simp only [map_mul, map_inv]
        group
      · intro h1
        apply hz1
        have h2 : burnsideB46_pi π γ * z * (burnsideB46_pi π γ)⁻¹ = 1 := h1
        calc z = (burnsideB46_pi π γ)⁻¹ * (burnsideB46_pi π γ * z * (burnsideB46_pi π γ)⁻¹) *
              burnsideB46_pi π γ := by group
          _ = 1 := by rw [h2]; group
  · have hshort1 : burnsideB46_p5_IsShortEl (g2X ![(1 : K), 0, 0]) := ⟨1, by group⟩
    refine ⟨burnsideB46_pi π (g2X ![1, 0, 0]), ?_, ?_, ?_, ?_⟩
    · refine ⟨(burnsideB46_p5_Xe0 K).map (burnsideB46_pi π), ?_, ⟨_, ⟨1, rfl⟩, rfl⟩, ?_⟩
      · refine burnsideB46_p5_isShortRootSub_iff.mpr ⟨1, fun ψ => ?_⟩
        constructor
        · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
          exact ⟨t, by simp⟩
        · rintro ⟨t, rfl⟩
          exact ⟨_, ⟨t, rfl⟩, by simp⟩
      · intro h1
        exact hshort1.ne_one (hinj (by rw [map_one]; exact h1))
    · intro x
      constructor
      · rintro ⟨Z, hZ, hxZ, hx1⟩
        obtain ⟨h, hh⟩ := burnsideB46_p5_isShortRootSub_iff.mp hZ
        obtain ⟨t, ht⟩ := (hh x).mp hxZ
        have ht0 : t ≠ 0 := by
          rintro rfl
          apply hx1
          rw [ht, burnsideB46_p5_xs_zero]
          simp
        obtain ⟨g₁, hg₁⟩ : burnsideB46_p5_IsShortEl (h * g2X ![t, 0, 0] * h⁻¹) :=
          burnsideB46_p5_isShortEl_iff.mpr ⟨h, t, ht0, rfl⟩
        refine ⟨burnsideB46_pi π g₁, burnsideB46_pi_mem_L H _, ?_⟩
        rw [ht, hg₁]
        simp only [map_mul, map_inv]
      · rintro ⟨l, hl, rfl⟩
        obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
        refine ⟨(burnsideB46_p5_Xconj K γ).map (burnsideB46_pi π), ?_, ?_, ?_⟩
        · refine burnsideB46_p5_isShortRootSub_iff.mpr ⟨γ, fun ψ => ?_⟩
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨t, rfl⟩ := burnsideB46_p5_mem_Xconj.mp hy
            exact ⟨t, rfl⟩
          · rintro ⟨t, rfl⟩
            exact ⟨_, burnsideB46_p5_mem_Xconj.mpr ⟨t, rfl⟩, rfl⟩
        · refine ⟨γ * g2X ![1, 0, 0] * γ⁻¹, burnsideB46_p5_mem_Xconj.mpr ⟨1, rfl⟩, ?_⟩
          simp only [map_mul, map_inv]
        · intro h1
          have h2 : burnsideB46_pi π γ * burnsideB46_pi π (g2X ![1, 0, 0]) *
              (burnsideB46_pi π γ)⁻¹ = 1 := h1
          have h3 : γ * g2X ![1, 0, 0] * γ⁻¹ = 1 :=
            hinj (by rw [map_one, ← h2]; simp only [map_mul, map_inv])
          exact hshort1.ne_one (by
            calc g2X ![(1 : K), 0, 0] = γ⁻¹ * (γ * g2X ![1, 0, 0] * γ⁻¹) * γ := by group
              _ = 1 := by rw [h3]; group)
    · rintro ⟨l, hl, hlr⟩
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
      rw [hz0] at hlr
      have h3 : g2X ![(1 : K), 0, 0] = γ * (h₂ * tL s₀ * h₂⁻¹) * γ⁻¹ :=
        hinj (by rw [hlr]; simp only [map_mul, map_inv])
      rw [hg₂] at h3
      exact burnsideB46_p5_not_long_short ⟨γ * g₂, by rw [h3]; group⟩ hshort1
    · intro x hxL hx1 hx2
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hxL
      have hγ2 : γ * γ = 1 := hinj (by rw [map_mul, ← sq, hx2, map_one])
      have hγ1 : γ ≠ 1 := fun h => hx1 (by rw [h, map_one])
      rcases burnsideB46_p5_invol_cases hγ2 hγ1 with ⟨g, hg⟩ | ⟨g, hg⟩
      · left
        refine ⟨burnsideB46_pi π (g * g₂⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
        rw [hz0, hg₂, hg]
        simp only [map_mul, map_inv]
        group
      · right
        refine ⟨burnsideB46_pi π g, burnsideB46_pi_mem_L H _, ?_⟩
        rw [hg]
        simp only [map_mul, map_inv]
  · have hzset : ({z} : Set (MulAut V)) = burnsideB46_pi π '' {h₂ * tL s₀ * h₂⁻¹} := by
      rw [Set.image_singleton, hz0]
    have hZ₂set : (Z₂ : Set (MulAut V)) = burnsideB46_pi π ''
        ((burnsideB46_p5_Dconj K h₂ : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) := by
      rw [hZ₂eq]
      rfl
    have hC1 : L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
        L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) := by
      rw [hzset, hZ₂set, burnsideB46_p5_L_inf_centralizer H, burnsideB46_p5_L_inf_centralizer H,
        burnsideB46_p5_centralizer_single_Dconj h₂ hs₀]
    refine ⟨hC1, ?_⟩
    have hP₂' : P₂ = (Subgroup.normalizer ((burnsideB46_p5_Dconj K h₂ :
        Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K))).map (burnsideB46_pi π) := by
      rw [hP₂, hZ₂eq, burnsideB46_p5_L_inf_normalizer H]
    rw [hP₂', burnsideB46_p5_tpr_map _ hinj,
      ← burnsideB46_p5_centralizer_eq_tpr (by omega) hK h4 h₂, hZ₂set,
      burnsideB46_p5_L_inf_centralizer H]

end V

section P5a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p5_act_stab (α β γ : K) {A : SL3 K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0]) (a b c d e f : K) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A) (q6 a b c d e f) = q6
      ((a + (A : Matrix (Fin 3) (Fin 3) K) 0 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 0 2 * c) +
        β * (((A : Matrix (Fin 3) (Fin 3) K) 0 1 * (A : Matrix (Fin 3) (Fin 3) K) 1 2 +
          (A : Matrix (Fin 3) (Fin 3) K) 0 2 * (A : Matrix (Fin 3) (Fin 3) K) 1 1) * d +
          (A : Matrix (Fin 3) (Fin 3) K) 1 2 * e + (A : Matrix (Fin 3) (Fin 3) K) 1 1 * f) +
        γ * (((A : Matrix (Fin 3) (Fin 3) K) 0 1 * (A : Matrix (Fin 3) (Fin 3) K) 2 2 +
          (A : Matrix (Fin 3) (Fin 3) K) 0 2 * (A : Matrix (Fin 3) (Fin 3) K) 2 1) * d +
          (A : Matrix (Fin 3) (Fin 3) K) 2 2 * e + (A : Matrix (Fin 3) (Fin 3) K) 2 1 * f) +
        α * α * d)
      (((A : Matrix (Fin 3) (Fin 3) K) 1 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 1 2 * c) + γ * d)
      (((A : Matrix (Fin 3) (Fin 3) K) 2 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 2 2 * c) + β * d) d
      ((((A : Matrix (Fin 3) (Fin 3) K) 0 1 * (A : Matrix (Fin 3) (Fin 3) K) 2 2 +
          (A : Matrix (Fin 3) (Fin 3) K) 0 2 * (A : Matrix (Fin 3) (Fin 3) K) 2 1) * d +
          (A : Matrix (Fin 3) (Fin 3) K) 2 2 * e + (A : Matrix (Fin 3) (Fin 3) K) 2 1 * f) +
        (β * ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 1 2 * c) +
          γ * ((A : Matrix (Fin 3) (Fin 3) K) 2 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 2 2 * c)) * β +
        α * (((A : Matrix (Fin 3) (Fin 3) K) 2 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 2 2 * c) + β * d))
      ((((A : Matrix (Fin 3) (Fin 3) K) 0 1 * (A : Matrix (Fin 3) (Fin 3) K) 1 2 +
          (A : Matrix (Fin 3) (Fin 3) K) 0 2 * (A : Matrix (Fin 3) (Fin 3) K) 1 1) * d +
          (A : Matrix (Fin 3) (Fin 3) K) 1 2 * e + (A : Matrix (Fin 3) (Fin 3) K) 1 1 * f) +
        (β * ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 1 2 * c) +
          γ * ((A : Matrix (Fin 3) (Fin 3) K) 2 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 2 2 * c)) * γ +
        α * (((A : Matrix (Fin 3) (Fin 3) K) 1 1 * b + (A : Matrix (Fin 3) (Fin 3) K) 1 2 * c) +
          γ * d)) := by
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_g2A_e0 hA, g2Act_y12q, g2Act_x0q]

theorem burnsideB46_p5_comm_xs [Finite K] {g : ↥(cayleyGroup K)} {t : K} (ht : t ≠ 0)
    (h : g * g2X ![t, 0, 0] = g2X ![t, 0, 0] * g) (s : K) :
    g * g2X ![s, 0, 0] = g2X ![s, 0, 0] * g := by
  have hp : ∀ x, qr (g2X ![t, 0, 0]) x = polarQ (t • eu 0 1) x * polarQ (t • eu 0 1) x := by
    intro x
    rw [burnsideB46_p5_qr_xs, polarQ_smul_left, polarQ_eu0]
    ring
  have hfix : g2Act g (t • eu 0 1) = t • eu 0 1 := fix_of_qr_sq hp h
  have hu : g2Act g (eu 0 1) = eu 0 1 := by
    rw [JonesParshall.g2Act_smul] at hfix
    exact smul_right_injective (Ix3 → K) ht hfix
  have hS : g ∈ stabV0 K := hu
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hS
  have h1 := congrArg (fun y => g2Act y (q6 (0 : K) 0 0 1 0 0)) h
  simp only [g2Act_mul_apply (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A) (g2X ![t, 0, 0]),
    g2Act_mul_apply (g2X ![t, 0, 0]) (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A), g2Act_x0q,
    burnsideB46_p5_act_stab α β γ hA] at h1
  obtain ⟨-, -, -, -, e4, e5⟩ := q6_inj h1
  have hβ : β = 0 := by
    have : t * β = 0 := by first | linear_combination e4 | linear_combination -e4
    exact (mul_eq_zero.mp this).resolve_left ht
  have hγ : γ = 0 := by
    have : t * γ = 0 := by first | linear_combination e5 | linear_combination -e5
    exact (mul_eq_zero.mp this).resolve_left ht
  subst hβ hγ
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  rw [hz3, JonesParshall.g2Y_zero, mul_one]
  have hAs : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![s, 0, 0] = ![s, 0, 0] := by
    rw [← burnsideB46_p5_smul_e0, Matrix.mulVec_smul, hA]
  calc g2X ![α, 0, 0] * g2A A * g2X ![s, 0, 0]
      = g2X ![α, 0, 0] * (g2A A * g2X ![s, 0, 0]) := mul_assoc _ _ _
    _ = g2X ![α, 0, 0] * (g2X ![s, 0, 0] * g2A A) := by rw [g2A_mul_g2X, hAs]
    _ = (g2X ![α, 0, 0] * g2X ![s, 0, 0]) * g2A A := (mul_assoc _ _ _).symm
    _ = (g2X ![s, 0, 0] * g2X ![α, 0, 0]) * g2A A := by
      rw [burnsideB46_p5_xs_mul, burnsideB46_p5_xs_mul, add_comm]
    _ = g2X ![s, 0, 0] * (g2X ![α, 0, 0] * g2A A) := mul_assoc _ _ _

theorem burnsideB46_p5_Z1_comm_xs (p q' s : K) :
    g2A (uSL p q' 0) * g2X ![s, 0, 0] = g2X ![s, 0, 0] * g2A (uSL p q' 0) := by
  have hAs : ((uSL p q' 0 : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![s, 0, 0] = ![s, 0, 0] := by
    rw [← burnsideB46_p5_smul_e0, Matrix.mulVec_smul, uSL_mulVec_e0]
  rw [g2A_mul_g2X, hAs]

theorem burnsideB46_p5_Z1_inf_Xe0 : Z1 K ⊓ burnsideB46_p5_Xe0 K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨v, rfl⟩, ⟨t, ht⟩⟩
  have h1 := congrArg (fun y => g2Act y (q6 (0 : K) 0 0 1 0 0)) ht
  simp only [g2Act_uSL_v0, g2Act_x0q] at h1
  obtain ⟨-, -, -, -, e4, e5⟩ := q6_inj h1
  have hv1 : v.1 = 0 := by linear_combination e4
  have hv2 : v.2 = 0 := by linear_combination e5
  rw [Subgroup.mem_bot, hv1, hv2, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]

theorem burnsideB46_p5_fix_xs_iff {t : K} (ht : t ≠ 0) (w : Ix3 → K) :
    g2Act (g2X ![t, 0, 0]) w = w ↔ w ∈ stdF K 3 := by
  constructor
  · intro h
    conv_lhs at h => rw [q6_eta w]
    rw [g2Act_x0q] at h
    conv_rhs at h => rw [q6_eta w]
    obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h
    refine mem_stdF_three.mpr ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.mp (by linear_combination e5 : t * w (.inl 1) = 0)).resolve_left ht
    · exact (mul_eq_zero.mp (by linear_combination e4 : t * w (.inl 2) = 0)).resolve_left ht
    · exact (mul_eq_zero.mp (by linear_combination e0 : t * t * w (.inr 0) = 0)).resolve_left
        (mul_ne_zero ht ht)
  · intro hw
    obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
    conv_lhs => rw [q6_eta w]
    rw [g2Act_x0q]
    conv_rhs => rw [q6_eta w]
    refine q6_congr ?_ rfl rfl rfl ?_ ?_ <;> simp [h1, h2, h3]

theorem burnsideB46_p5_fixSub_Xe0 : fixSub (burnsideB46_p5_Xe0 K) = stdF K 3 := by
  ext w
  rw [mem_fixSub]
  constructor
  · intro h
    exact (burnsideB46_p5_fix_xs_iff (one_ne_zero (α := K)) w).mp (h _ ⟨1, rfl⟩)
  · intro hw γ hγ
    obtain ⟨t, rfl⟩ := hγ
    by_cases ht : t = 0
    · subst ht
      rw [burnsideB46_p5_xs_zero, map_one]
      rfl
    · exact (burnsideB46_p5_fix_xs_iff ht w).mpr hw

theorem burnsideB46_p5_fixSub_zpowers_xs {t : K} (ht : t ≠ 0) :
    fixSub (Subgroup.zpowers (g2X ![t, 0, 0])) = stdF K 3 := by
  ext w
  rw [mem_fixSub]
  constructor
  · intro h
    exact (burnsideB46_p5_fix_xs_iff ht w).mp (h _ (Subgroup.mem_zpowers _))
  · intro hw γ hγ
    have hle : Subgroup.zpowers (g2X ![t, 0, 0]) ≤ burnsideB46_p5_Xe0 K :=
      (Subgroup.zpowers_le).mpr ⟨t, rfl⟩
    have := (mem_fixSub.mp (show w ∈ fixSub (burnsideB46_p5_Xe0 K) by
      rw [burnsideB46_p5_fixSub_Xe0]; exact hw)) γ (hle hγ)
    exact this

theorem burnsideB46_p5_commQ_xs_iff {t : K} (ht : t ≠ 0) (w : Ix3 → K) :
    (∃ z, g2Act (g2X ![t, 0, 0]) z - z = w) ↔ w ∈ stdF K 3 := by
  constructor
  · rintro ⟨z, rfl⟩
    have h : g2Act (g2X ![t, 0, 0]) z - z =
        q6 (t * t * z (.inr 0)) 0 0 0 (t * z (.inl 2)) (t * z (.inl 1)) := by
      conv_lhs => rw [q6_eta z]
      rw [g2Act_x0q]
      funext j
      rcases j with j | j <;> fin_cases j <;> simp [q6]
    rw [h]
    exact mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
  · intro hw
    obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
    refine ⟨q6 0 (w (.inr 2) / t) (w (.inr 1) / t) (w (.inl 0) / (t * t)) 0 0, ?_⟩
    rw [g2Act_x0q]
    conv_rhs => rw [q6_eta w]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, h1, h2, h3] <;> field_simp

theorem burnsideB46_p5_mem_stabQ_pt {g : ↥(cayleyGroup K)} {x : Ix3 → K} {c : K} (hc : c ≠ 0)
    (h : g2Act g x = c • x) : g ∈ stabQ (burnsideB46_pt K x) := by
  rw [mem_stabQ]
  intro w
  rw [burnsideB46_pt, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a * c, by rw [JonesParshall.g2Act_smul, h, smul_smul]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a * c⁻¹, ?_⟩
    have h1 : g2Act g⁻¹ x = c⁻¹ • x := inv_smul_of_smul hc h
    calc (a * c⁻¹) • x = a • g2Act g⁻¹ x := by rw [h1, smul_smul]
      _ = g2Act g⁻¹ (a • x) := by rw [JonesParshall.g2Act_smul]
      _ = g2Act g⁻¹ (g2Act g w) := by rw [ha]
      _ = w := g2Act_inv_apply g w

theorem burnsideB46_p5_exists_smul_of_mem_stabQ_pt {g : ↥(cayleyGroup K)} {x : Ix3 → K}
    (hx : x ≠ 0) (hg : g ∈ stabQ (burnsideB46_pt K x)) :
    ∃ c : K, c ≠ 0 ∧ g2Act g x = c • x := by
  have hxm : x ∈ burnsideB46_pt K x := Submodule.mem_span_singleton_self x
  have h1 := (mem_stabQ.mp hg x).mp hxm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  apply hx
  have h2 := congrArg (g2Act g⁻¹) hc
  rw [g2Act_inv_apply, map_zero] at h2
  exact h2.symm

@[expose] def burnsideB46_p5_Lev (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) :=
  stabQ (stdF K 1) ⊓ stabQ (burnsideB46_pt K (q6 0 0 0 1 0 0))

theorem burnsideB46_p5_v0_ne_zero : (q6 (0 : K) 0 0 1 0 0) ≠ 0 := by
  intro h
  have := congrFun h (.inr 0)
  simp [q6] at this

theorem burnsideB46_p5_Lev_inf_core [Finite K] :
    burnsideB46_p5_Lev K ⊓ pCoreOf 2 (stabV0 K) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨hg1, hgv⟩, hcore⟩
  have hcore' : g ∈ burnsideB46_R1 K (eu 0 (1 : K)) := by
    rw [burnsideB46_p3_R1_eu]
    exact hcore
  obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_R1_eu.mp hcore'
  obtain ⟨c, hc0, hc⟩ := burnsideB46_p5_exists_smul_of_mem_stabQ_pt burnsideB46_p5_v0_ne_zero hgv
  rw [burnsideB46_p3_act_kerElt, smul_q6] at hc
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := q6_inj hc
  have hγ : γ = 0 := by linear_combination e1
  have hβ : β = 0 := by linear_combination e2
  subst hγ hβ
  have hα : α = 0 := mul_self_eq_zero.mp (by linear_combination e0)
  have hp : p = 0 := by linear_combination e4
  have hq : q' = 0 := by linear_combination e5
  subst hα hp hq
  rw [Subgroup.mem_bot, burnsideB46_p3_kerElt_zero, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero,
    map_one]

theorem burnsideB46_p5_P1_factor [Finite K] {g : ↥(cayleyGroup K)}
    (hg : g ∈ stabQ (stdF K 1)) :
    ∃ ρ ∈ pCoreOf 2 (stabV0 K), ∃ ℓ ∈ burnsideB46_p5_Lev K, g = ρ * ℓ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hg
  have hB : polarQ (g2Act g (eu 0 1)) (g2Act g (q6 (0 : K) 0 0 1 0 0)) = 1 := by
    rw [polarQ_g2Act, polarQ_eu0]
    simp [q6]
  rw [hc, polarQ_smul_left, polarQ_eu0] at hB
  set w₁ : Ix3 → K := c • g2Act g (q6 (0 : K) 0 0 1 0 0) with hw₁
  have hw₁r0 : w₁ (.inr 0) = 1 := by
    simpa [hw₁] using hB
  obtain ⟨α, hα⟩ := isSquare_of_charTwo' (w₁ (.inl 0) + w₁ (.inl 2) * w₁ (.inr 2) +
    w₁ (.inl 1) * w₁ (.inr 1))
  set ρ := burnsideB46_p3_kerElt α (w₁ (.inl 2)) (w₁ (.inl 1)) (w₁ (.inr 1) + α * w₁ (.inl 2))
    (w₁ (.inr 2) + α * w₁ (.inl 1)) with hρdef
  have hρv : g2Act ρ (q6 (0 : K) 0 0 1 0 0) = w₁ := by
    rw [hρdef, burnsideB46_p3_act_kerElt]
    conv_rhs => rw [q6_eta w₁]
    rw [hw₁r0]
    refine q6_congr ?_ ?_ ?_ rfl ?_ ?_
    · linear_combination (-1 : K) * hα + (w₁ (.inl 2) * w₁ (.inr 2) + w₁ (.inl 1) * w₁ (.inr 1) +
        α * w₁ (.inl 1) * w₁ (.inl 2)) * h2
    · ring
    · ring
    · linear_combination (α * w₁ (.inl 2)) * h2
    · linear_combination (α * w₁ (.inl 1)) * h2
  have hρS : ρ ∈ stabV0 K := burnsideB46_p3_kerElt_mem_stabV0 _ _ _ _ _
  have hρR : ρ ∈ pCoreOf 2 (stabV0 K) := by
    rw [← burnsideB46_p3_R1_eu]
    exact burnsideB46_p3_mem_R1_eu.mpr ⟨_, _, _, _, _, rfl⟩
  have hρiu : g2Act ρ⁻¹ (eu 0 1) = eu 0 1 := (stabV0 K).inv_mem hρS
  refine ⟨ρ, hρR, ρ⁻¹ * g, ⟨?_, ?_⟩, by group⟩
  · have hℓu : g2Act (ρ⁻¹ * g) (eu 0 1) = c • eu 0 1 := by
      rw [g2Act_mul_apply, hc, JonesParshall.g2Act_smul, hρiu]
    have := burnsideB46_p5_mem_stabQ_pt hc0 hℓu
    rwa [burnsideB46_p3_pt_eu] at this
  · have hgv : g2Act g (q6 (0 : K) 0 0 1 0 0) = c⁻¹ • w₁ := by
      rw [hw₁, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hℓv : g2Act (ρ⁻¹ * g) (q6 (0 : K) 0 0 1 0 0) = c⁻¹ • q6 0 0 0 1 0 0 := by
      rw [g2Act_mul_apply, hgv, JonesParshall.g2Act_smul, ← hρv, g2Act_inv_apply]
    exact burnsideB46_p5_mem_stabQ_pt (inv_ne_zero hc0) hℓv

theorem burnsideB46_p5_tG_conj_xs (d : Kˣ) (s : K) :
    tG d * g2X ![s, 0, 0] * (tG d)⁻¹ = g2X ![(d : K) * s, 0, 0] := by
  have hA : (((diag3 (d : K) (d⁻¹ : Kˣ) 1 (by simp)) : SL3 K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![s, 0, 0] = ![(d : K) * s, 0, 0] := by
    funext i
    fin_cases i <;> simp [diag3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h := g2A_mul_g2X (diag3 (d : K) (d⁻¹ : Kˣ) 1 (by simp)) ![s, 0, 0]
  rw [hA] at h
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem burnsideB46_p5_tG_mem_normalizer (d : Kˣ) :
    tG d ∈ Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨s, rfl⟩
    rw [burnsideB46_p5_tG_conj_xs]
    exact ⟨_, rfl⟩
  · rintro ⟨s, hs⟩
    have hy : y = (tG d)⁻¹ * (tG d * y * (tG d)⁻¹) * tG d := by group
    rw [hs] at hy
    have h1 := burnsideB46_p5_tG_conj_xs d⁻¹ s
    rw [← tG_inv, inv_inv] at h1
    rw [hy.trans h1]
    exact ⟨_, rfl⟩

theorem burnsideB46_p5_polarQ_v0 (x : Ix3 → K) : polarQ x (eu 0 1) = x (.inr 0) := by
  rw [burnsideB46_p5_polarQ_eu, mul_one]

theorem burnsideB46_p5_Lev_le_normalizer [Finite K] :
    burnsideB46_p5_Lev K ≤ Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) := by
  rintro ℓ ⟨hℓ1, hℓv⟩
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hℓ1
  obtain ⟨c', hc'0, hc'⟩ :=
    burnsideB46_p5_exists_smul_of_mem_stabQ_pt burnsideB46_p5_v0_ne_zero hℓv
  set d : Kˣ := (Units.mk0 c hc0)⁻¹ with hd
  have hdval : (d : K) = c⁻¹ := by simp [hd]
  set ℓ' : ↥(cayleyGroup K) := ℓ * tG d with hℓ'
  have hℓ'u : g2Act ℓ' (eu 0 1) = eu 0 1 := by
    rw [hℓ', g2Act_mul_apply, g2Act_tG_eu, mul_one, ← mul_one (d : K), ← smul_eu,
      JonesParshall.g2Act_smul, hc, smul_smul, hdval, inv_mul_cancel₀ hc0, one_smul]
  have hℓ'v : g2Act ℓ' (q6 (0 : K) 0 0 1 0 0) = (c * c') • q6 (0 : K) 0 0 1 0 0 := by
    have h1 : g2Act (tG d) (q6 (0 : K) 0 0 1 0 0) = c • q6 (0 : K) 0 0 1 0 0 := by
      rw [g2Act_tG, smul_q6]
      refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [q6, hd]
    rw [hℓ', g2Act_mul_apply, h1, JonesParshall.g2Act_smul, hc', smul_smul]
  have hcc0 : c * c' ≠ 0 := mul_ne_zero hc0 hc'0
  have hℓ'iv : g2Act ℓ'⁻¹ (q6 (0 : K) 0 0 1 0 0) = (c * c')⁻¹ • q6 (0 : K) 0 0 1 0 0 :=
    inv_smul_of_smul hcc0 hℓ'v
  have hr2 : (ℓ' * g2X ![1, 0, 0] * ℓ'⁻¹) * (ℓ' * g2X ![1, 0, 0] * ℓ'⁻¹) = 1 := by
    calc (ℓ' * g2X ![1, 0, 0] * ℓ'⁻¹) * (ℓ' * g2X ![1, 0, 0] * ℓ'⁻¹) =
        ℓ' * (g2X ![(1 : K), 0, 0] * g2X ![1, 0, 0]) * ℓ'⁻¹ := by group
      _ = 1 := by rw [g2X_mul_self]; group
  have hrq : ∀ w, qr (ℓ' * g2X ![1, 0, 0] * ℓ'⁻¹) w = w (.inr 0) * w (.inr 0) := by
    intro w
    have h1 := qr_conj ℓ' (g2X ![1, 0, 0]) (g2Act ℓ'⁻¹ w)
    rw [g2Act_apply_inv, burnsideB46_p5_qr_xs] at h1
    have h2 : g2Act ℓ'⁻¹ w (.inr 0) = w (.inr 0) := by
      have e1 : g2Act ℓ'⁻¹ w (.inr 0) = polarQ (g2Act ℓ'⁻¹ w) (eu 0 1) :=
        (burnsideB46_p5_polarQ_v0 _).symm
      have e2 : polarQ (g2Act ℓ'⁻¹ w) (eu 0 1) = polarQ w (eu 0 1) := by
        have := polarQ_g2Act ℓ' (g2Act ℓ'⁻¹ w) (eu 0 1)
        rw [g2Act_apply_inv, hℓ'u] at this
        exact this.symm
      rw [e1, e2, burnsideB46_p5_polarQ_v0]
    rw [h1, h2]
    ring
  obtain ⟨a, b, hab⟩ := eq_kerElt_of_qr hr2 hrq
  have hq : (q6 (0 + 1 * 1 * 1 : K) 0 0 1 (0 + 1 * 0) (0 + 1 * 0)) =
      eu 0 1 + q6 0 0 0 1 0 0 := by
    rw [eu_eq_q6, q6_add']
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have hL : g2Act (ℓ' * g2X ![1, 0, 0] * ℓ'⁻¹) (q6 (0 : K) 0 0 1 0 0) =
      q6 (c * c')⁻¹ 0 0 1 0 0 := by
    rw [g2Act_mul_apply, g2Act_mul_apply, hℓ'iv, JonesParshall.g2Act_smul, g2Act_x0q, hq,
      JonesParshall.g2Act_smul, map_add, hℓ'u, hℓ'v, smul_add, smul_smul, inv_mul_cancel₀ hcc0,
      one_smul, eu_eq_q6, smul_q6, q6_add']
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have hv := congrArg (fun y => g2Act y (q6 (0 : K) 0 0 1 0 0)) hab
  simp only [hL, g2Act_kerElt] at hv
  obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj hv
  have ha0 : a = 0 := by linear_combination -e4
  have hb0 : b = 0 := by linear_combination -e5
  subst ha0 hb0
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  rw [hz3, JonesParshall.g2Y_zero, mul_one, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero,
    map_one, mul_one] at hab
  have hcomm : ℓ' * g2X ![1, 0, 0] = g2X ![1, 0, 0] * ℓ' := mul_inv_eq_iff_eq_mul.mp hab
  have hcent : ℓ' ∈ Subgroup.centralizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨s, rfl⟩
    exact (burnsideB46_p5_comm_xs (one_ne_zero (α := K)) hcomm s).symm
  have hnorm := Subgroup.centralizer_le_normalizer _ hcent
  have hℓ : ℓ = ℓ' * (tG d)⁻¹ := by rw [hℓ']; group
  rw [hℓ]
  exact Subgroup.mul_mem _ hnorm (Subgroup.inv_mem _ (burnsideB46_p5_tG_mem_normalizer d))

theorem burnsideB46_p5_normalizer_Xe0_data [Finite K] {g : ↥(cayleyGroup K)}
    (hg : g ∈ Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K))) :
    ∃ t : K, t ≠ 0 ∧ g * g2X ![1, 0, 0] * g⁻¹ = g2X ![t, 0, 0] ∧
      g2Act g (eu 0 1) = t • eu 0 1 := by
  rw [Subgroup.mem_normalizer_iff] at hg
  obtain ⟨t, ht⟩ : g * g2X ![1, 0, 0] * g⁻¹ ∈ burnsideB46_p5_Xe0 K := (hg _).mp ⟨1, rfl⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [burnsideB46_p5_xs_zero] at ht
    exact burnsideB46_p5_IsShortEl.ne_one ⟨g, rfl⟩ ht
  refine ⟨t, ht0, ht, ?_⟩
  have hq : ∀ w, polarQ w (g2Act g (eu 0 1)) = t * polarQ w (eu 0 1) := by
    intro w
    have h1 := qr_conj g (g2X ![1, 0, 0]) (g2Act g⁻¹ w)
    rw [g2Act_apply_inv, ht, burnsideB46_p5_qr_xs, burnsideB46_p5_qr_xs] at h1
    have h2 : g2Act g⁻¹ w (.inr 0) = polarQ w (g2Act g (eu 0 1)) := by
      rw [← burnsideB46_p5_polarQ_v0 (g2Act g⁻¹ w)]
      have := polarQ_g2Act g (g2Act g⁻¹ w) (eu 0 1)
      rw [g2Act_apply_inv] at this
      exact this.symm
    rw [h2, ← burnsideB46_p5_polarQ_v0 w] at h1
    exact eq_of_mul_self_eq_charTwo (by linear_combination -h1)
  refine (sub_eq_zero.mp (eq_zero_of_polarQ fun y => ?_))
  rw [polarQ_symm, polarQ_sub_right, hq, polarQ_smul_right]
  ring

theorem burnsideB46_p5_normalizer_Xe0_le [Finite K] :
    Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) ≤ stabQ (stdF K 1) := by
  intro g hg
  obtain ⟨t, ht0, -, hgu⟩ := burnsideB46_p5_normalizer_Xe0_data hg
  have := burnsideB46_p5_mem_stabQ_pt ht0 hgu
  rwa [burnsideB46_p3_pt_eu] at this

theorem burnsideB46_p5_A1_le_centralizer : A1 K ≤
    Subgroup.centralizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) := by
  intro g hg
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hg
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨s, rfl⟩
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  rw [hz3, JonesParshall.g2Y_zero, mul_one]
  calc g2X ![s, 0, 0] * (g2X ![α, 0, 0] * g2A (uSL p q' 0)) =
      (g2X ![s, 0, 0] * g2X ![α, 0, 0]) * g2A (uSL p q' 0) := (mul_assoc _ _ _).symm
    _ = (g2X ![α, 0, 0] * g2X ![s, 0, 0]) * g2A (uSL p q' 0) := by
      rw [burnsideB46_p5_xs_mul, burnsideB46_p5_xs_mul, add_comm]
    _ = g2X ![α, 0, 0] * (g2X ![s, 0, 0] * g2A (uSL p q' 0)) := mul_assoc _ _ _
    _ = g2X ![α, 0, 0] * (g2A (uSL p q' 0) * g2X ![s, 0, 0]) := by
      rw [burnsideB46_p5_Z1_comm_xs]
    _ = g2X ![α, 0, 0] * g2A (uSL p q' 0) * g2X ![s, 0, 0] := (mul_assoc _ _ _).symm

theorem burnsideB46_p5_A1_le_normalizer : A1 K ≤
    Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) :=
  burnsideB46_p5_A1_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)

theorem burnsideB46_p5_core_inf_normalizer_le [Finite K] :
    pCoreOf 2 (stabV0 K) ⊓ Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) ≤
      A1 K := by
  rintro g ⟨hcore, hn⟩
  have hcore' : g ∈ burnsideB46_R1 K (eu 0 (1 : K)) := by
    rw [burnsideB46_p3_R1_eu]
    exact hcore
  obtain ⟨α, β, γ, p, q', rfl⟩ := burnsideB46_p3_mem_R1_eu.mp hcore'
  obtain ⟨t, ht0, hgx, hgu⟩ := burnsideB46_p5_normalizer_Xe0_data hn
  have hS : burnsideB46_p3_kerElt α β γ p q' ∈ stabV0 K := burnsideB46_p3_kerElt_mem_stabV0 _ _ _ _ _
  have ht1 : t = 1 := by
    have h1 : g2Act (burnsideB46_p3_kerElt α β γ p q') (eu 0 1) = eu 0 1 := hS
    rw [h1] at hgu
    have := congrFun hgu (.inl 0)
    simpa [eu] using this.symm
  subst ht1
  have hcomm : burnsideB46_p3_kerElt α β γ p q' * g2X ![1, 0, 0] =
      g2X ![1, 0, 0] * burnsideB46_p3_kerElt α β γ p q' := mul_inv_eq_iff_eq_mul.mp hgx
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  have hx1 : g2X ![(1 : K), 0, 0] * g2Y ![0, 0, 0] * g2A (uSL 0 0 0) = g2X ![1, 0, 0] := by
    rw [hz3, JonesParshall.g2Y_zero, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one,
      mul_one, mul_one]
  obtain ⟨hβ, hγ⟩ := kerElt_eq_of_comm (α := α) (β := β) (γ := γ) (p := p) (q' := q') (a := 0)
    (b := 0) (by rw [hx1]; exact hcomm)
  subst hβ hγ
  exact kerElt_mem_A1 α p q'

theorem burnsideB46_p5_Xe0_le_A1 : burnsideB46_p5_Xe0 K ≤ A1 K := by
  rintro _ ⟨t, rfl⟩
  have h := kerElt_mem_A1 t (0 : K) 0
  have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
  rwa [hz3, JonesParshall.g2Y_zero, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one,
    mul_one, mul_one] at h

theorem burnsideB46_p5_A1_eq_sup : A1 K = Z1 K ⊔ burnsideB46_p5_Xe0 K := by
  apply le_antisymm
  · intro g hg
    obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hg
    have hz3 : (![0, 0, 0] : Fin 3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
    rw [hz3, JonesParshall.g2Y_zero, mul_one]
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ⟨α, rfl⟩ ⟨(p, q'), rfl⟩
  · exact sup_le Z1_le_A1 burnsideB46_p5_Xe0_le_A1

theorem burnsideB46_p5_normalizer_Xe0_eq [Finite K] :
    Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) =
      A1 K ⊔ burnsideB46_p5_Lev K := by
  apply le_antisymm
  · intro g hg
    obtain ⟨ρ, hρ, ℓ, hℓ, rfl⟩ := burnsideB46_p5_P1_factor (burnsideB46_p5_normalizer_Xe0_le hg)
    have hℓn := burnsideB46_p5_Lev_le_normalizer hℓ
    have hρn : ρ ∈ Subgroup.normalizer (burnsideB46_p5_Xe0 K : Set ↥(cayleyGroup K)) := by
      have := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hℓn)
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem_sup (burnsideB46_p5_core_inf_normalizer_le ⟨hρ, hρn⟩) hℓ
  · exact sup_le burnsideB46_p5_A1_le_normalizer burnsideB46_p5_Lev_le_normalizer

theorem burnsideB46_p5_Lev_sup_core [Finite K] :
    burnsideB46_p5_Lev K ⊔ pCoreOf 2 (stabV0 K) = stabQ (stdF K 1) := by
  apply le_antisymm
  · refine sup_le inf_le_left ?_
    have h1 : pCoreOf 2 (stabQ (stdF K 1)) ≤ stabQ (stdF K 1) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have h2 : pCoreOf 2 (stabV0 K) = pCoreOf 2 (stabQ (stdF K 1)) := by
      rw [← burnsideB46_p3_R1_eu, burnsideB46_R1, burnsideB46_p3_P1_eu]
    rwa [h2]
  · intro g hg
    obtain ⟨ρ, hρ, ℓ, hℓ, rfl⟩ := burnsideB46_p5_P1_factor hg
    rw [sup_comm]
    exact Subgroup.mul_mem_sup hρ hℓ

end P5a

section P5b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p5_centralizer_single_Xconj [Finite K] (h : ↥(cayleyGroup K)) {t : K}
    (ht : t ≠ 0) :
    Subgroup.centralizer ({h * g2X ![t, 0, 0] * h⁻¹} : Set ↥(cayleyGroup K)) =
      Subgroup.centralizer ((burnsideB46_p5_Xconj K h : Subgroup ↥(cayleyGroup K)) :
        Set ↥(cayleyGroup K)) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg y hy
    obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Xconj.mp hy
    have h1 := hg (h * g2X ![t, 0, 0] * h⁻¹) rfl
    have h2 : (h⁻¹ * g * h) * g2X ![t, 0, 0] = g2X ![t, 0, 0] * (h⁻¹ * g * h) := by
      calc h⁻¹ * g * h * g2X ![t, 0, 0] = h⁻¹ * (g * (h * g2X ![t, 0, 0] * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * g2X ![t, 0, 0] * h⁻¹) * g) * h := by rw [h1]
        _ = g2X ![t, 0, 0] * (h⁻¹ * g * h) := by group
    have h3 := burnsideB46_p5_comm_xs ht h2 s
    calc h * g2X ![s, 0, 0] * h⁻¹ * g = h * (g2X ![s, 0, 0] * (h⁻¹ * g * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * g * h) * g2X ![s, 0, 0]) * h⁻¹ := by rw [← h3]
      _ = g * (h * g2X ![s, 0, 0] * h⁻¹) := by group
  · intro hg y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hg _ (burnsideB46_p5_mem_Xconj.mpr ⟨t, rfl⟩)

theorem burnsideB46_p5_xs_sub_mem (s : K) (z : Ix3 → K) :
    g2Act (g2X ![s, 0, 0]) z - z ∈ stdF K 3 := by
  have h : g2Act (g2X ![s, 0, 0]) z - z =
      q6 (s * s * z (.inr 0)) 0 0 0 (s * z (.inl 2)) (s * z (.inl 1)) := by
    conv_lhs => rw [q6_eta z]
    rw [g2Act_x0q]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6]
  rw [h]
  exact mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩

section ConjModel

variable [Finite K]

theorem burnsideB46_p5_A1_eu : burnsideB46_A1 K (eu 0 (1 : K)) = A1 K := by
  ext g
  change (∀ w ∈ burnsideB46_F3 K (eu 0 (1 : K)), g2Act g w = w) ↔ _
  rw [burnsideB46_p3_F3_eu]
  exact Iff.rfl

theorem burnsideB46_p5_obj_act (h : ↥(cayleyGroup K)) :
    burnsideB46_P1 K (g2Act h (eu 0 1)) = (stabQ (stdF K 1)).map (MulAut.conj h).toMonoidHom ∧
    burnsideB46_R1 K (g2Act h (eu 0 1)) = (pCoreOf 2 (stabV0 K)).map (MulAut.conj h).toMonoidHom ∧
    burnsideB46_Z1 K (g2Act h (eu 0 1)) = (Z1 K).map (MulAut.conj h).toMonoidHom ∧
    burnsideB46_F3 K (g2Act h (eu 0 1)) = gmapG h (stdF K 3) ∧
    burnsideB46_A1 K (g2Act h (eu 0 1)) = (A1 K).map (MulAut.conj h).toMonoidHom := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [burnsideB46_p3_P1_act, burnsideB46_p3_P1_eu]
  · rw [burnsideB46_p3_R1_act, burnsideB46_p3_R1_eu]
  · rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu]
  · rw [burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu]
  · rw [burnsideB46_p3_A1_act, burnsideB46_p5_A1_eu]

theorem burnsideB46_p5_g2Act_ne_zero (h : ↥(cayleyGroup K)) : g2Act h (eu 0 (1 : K)) ≠ 0 := by
  intro h0
  have h1 := congrArg (g2Act h⁻¹) h0
  rw [g2Act_inv_apply, map_zero] at h1
  have := congrFun h1 (.inl 0)
  simp [eu] at this

end ConjModel

end P5b

section V6

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p5_commV_eq [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    (γ : ↥(cayleyGroup K)) (F : Submodule K (Ix3 → K))
    (hF1 : ∀ δ ∈ Subgroup.zpowers γ, ∀ y, g2Act δ y - y ∈ F)
    (hF2 : ∀ w ∈ F, ∃ z, g2Act γ z - z = w) :
    commV (Subgroup.zpowers (burnsideB46_pi π γ)) ⊔ fixV L = burnsideB46_pre θ F := by
  apply le_antisymm
  · refine sup_le ?_ (burnsideB46_pre_map_ker H F)
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← map_zpow]
    show burnsideB46_f θ (burnsideB46_pi π (γ ^ k) v * v⁻¹) ∈ F
    rw [burnsideB46_f_mul, burnsideB46_f_inv, burnsideB46_f_act H, ← sub_eq_add_neg]
    exact hF1 _ (Subgroup.zpow_mem_zpowers γ k) _
  · intro v hv
    obtain ⟨z, hz⟩ := hF2 _ (burnsideB46_mem_pre.mp hv)
    obtain ⟨u, rfl⟩ := burnsideB46_f_surj H z
    have hc : burnsideB46_pi π γ u * u⁻¹ ∈ commV (Subgroup.zpowers (burnsideB46_pi π γ)) :=
      Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, u, rfl⟩
    have hfc : burnsideB46_f θ (burnsideB46_pi π γ u * u⁻¹) = burnsideB46_f θ v := by
      rw [burnsideB46_f_mul, burnsideB46_f_inv, burnsideB46_f_act H, ← sub_eq_add_neg, hz]
    have hk : v * (burnsideB46_pi π γ u * u⁻¹)⁻¹ ∈ fixV L := by
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, hfc, sub_self]
    have hv' : v = (burnsideB46_pi π γ u * u⁻¹) * (v * (burnsideB46_pi π γ u * u⁻¹)⁻¹) := by
      rw [mul_comm (burnsideB46_pi π γ u * u⁻¹), mul_assoc, inv_mul_cancel, mul_one]
    rw [hv']
    exact Subgroup.mul_mem_sup hc hk

theorem burnsideB46_p5_cfg1_of_point [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {x : Ix3 → K} (hx : x ≠ 0)
    (hF3 : burnsideB46_F3 K x ≠ ⊥) :
    B46Cfg1 G L θ (burnsideB46_pre θ (burnsideB46_pt K x))
      ((burnsideB46_P1 K x).map (burnsideB46_pi π)) ((burnsideB46_R1 K x).map (burnsideB46_pi π))
      ((burnsideB46_Z1 K x).map (burnsideB46_pi π))
      (burnsideB46_pre θ (burnsideB46_F3 K x)) ((burnsideB46_A1 K x).map (burnsideB46_pi π)) := by
  have hinj := burnsideB46_pi_injective H
  have hP : (burnsideB46_P1 K x).map (burnsideB46_pi π) =
      L ⊓ stabSub (burnsideB46_pre θ (burnsideB46_pt K x)) := (burnsideB46_stab_pre H _).symm
  have hR : (burnsideB46_R1 K x).map (burnsideB46_pi π) =
      pCoreOf 2 ((burnsideB46_P1 K x).map (burnsideB46_pi π)) :=
    (burnsideB46_pCoreOf_map _ hinj (burnsideB46_P1 K x)).symm
  have hZ : (burnsideB46_Z1 K x).map (burnsideB46_pi π) =
      centerOf ((burnsideB46_R1 K x).map (burnsideB46_pi π)) :=
    (burnsideB46_centerOf_map _ hinj (burnsideB46_R1 K x)).symm
  refine ⟨burnsideB46_isFPre_iff.mpr ⟨burnsideB46_pt K x, finrank_span_singleton hx, rfl⟩, hP, hR,
    hZ, (burnsideB46_cPre_map H (burnsideB46_Z1 K x)).symm, fun g => ?_⟩
  have key : (∀ v ∈ burnsideB46_pre θ (burnsideB46_F3 K x), g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K x → burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  rw [key]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨H.le (burnsideB46_pi_mem_L H γ), fun v hv => ?_⟩
    rw [burnsideB46_f_act H]
    exact hγ _ hv
  · rintro ⟨hgG, hg⟩
    have hgL : g ∈ L := burnsideB46_mem_L_of_fix hqs H hn hgG hF3 hg
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hgL
    refine ⟨γ, fun w hw => ?_, rfl⟩
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
    rw [← burnsideB46_f_act H]
    exact hg v hw

theorem burnsideB46_p5_part6_core [CharP K 2] [Finite K] [Finite V] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    ∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) =
          L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
        (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁ := by
  intro R hR r hrR hr1
  have hinj := burnsideB46_pi_injective H
  obtain ⟨h, hh⟩ := burnsideB46_p5_isShortRootSub_iff.mp hR
  obtain ⟨t₀, ht₀r⟩ := (hh r).mp hrR
  have ht₀ : t₀ ≠ 0 := by
    rintro rfl
    apply hr1
    rw [ht₀r, burnsideB46_p5_xs_zero]
    simp
  have hRmap : R = (burnsideB46_p5_Xconj K h).map (burnsideB46_pi π) := by
    ext ψ
    rw [hh ψ]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, burnsideB46_p5_mem_Xconj.mpr ⟨t, rfl⟩, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨t, rfl⟩ := burnsideB46_p5_mem_Xconj.mp hγ
      exact ⟨t, rfl⟩
  have hC : L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) =
      L ⊓ Subgroup.centralizer (R : Set (MulAut V)) := by
    have hrset : ({r} : Set (MulAut V)) =
        burnsideB46_pi π '' {h * g2X ![t₀, 0, 0] * h⁻¹} := by
      rw [Set.image_singleton, ht₀r]
    have hRset : (R : Set (MulAut V)) = burnsideB46_pi π ''
        ((burnsideB46_p5_Xconj K h : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) := by
      rw [hRmap]
      rfl
    rw [hrset, hRset, burnsideB46_p5_L_inf_centralizer H, burnsideB46_p5_L_inf_centralizer H,
      burnsideB46_p5_centralizer_single_Xconj h ht₀]
  refine ⟨hC, ?_⟩
  set c : ↥(cayleyGroup K) →* ↥(cayleyGroup K) := (MulAut.conj h).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj h).injective
  obtain ⟨hP1, hR1, hZ1, hF3, hA1⟩ := burnsideB46_p5_obj_act h
  have hx : g2Act h (eu 0 (1 : K)) ≠ 0 := burnsideB46_p5_g2Act_ne_zero h
  have hF3ne : burnsideB46_F3 K (g2Act h (eu 0 (1 : K))) ≠ ⊥ := by
    intro hbot
    have := burnsideB46_p3_F3_card hx
    rw [hbot, finrank_bot] at this
    omega
  have hcfg := burnsideB46_p5_cfg1_of_point hqs H hn hx hF3ne
  have hfixX : fixSub (burnsideB46_p5_Xconj K h) = gmapG h (stdF K 3) := by
    unfold burnsideB46_p5_Xconj
    rw [burnsideB46_p3_fixSub_map_conj, burnsideB46_p5_fixSub_Xe0]
  have hzp : Subgroup.zpowers (burnsideB46_pi π (h * g2X ![t₀, 0, 0] * h⁻¹)) =
      (Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹)).map (burnsideB46_pi π) :=
    (MonoidHom.map_zpowers _ _).symm
  have hzpc : Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹) =
      (Subgroup.zpowers (g2X ![t₀, 0, 0])).map c := (MonoidHom.map_zpowers c _).symm
  have hfixr : fixSub (Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹)) = gmapG h (stdF K 3) := by
    rw [hzpc, burnsideB46_p3_fixSub_map_conj, burnsideB46_p5_fixSub_zpowers_xs ht₀]
  have hF1 : ∀ δ ∈ Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹), ∀ y,
      g2Act δ y - y ∈ gmapG h (stdF K 3) := by
    intro δ hδ y
    rw [hzpc] at hδ
    obtain ⟨δ', hδ', rfl⟩ := hδ
    obtain ⟨s, rfl⟩ : δ' ∈ burnsideB46_p5_Xe0 K :=
      (Subgroup.zpowers_le.mpr ⟨t₀, rfl⟩ : Subgroup.zpowers (g2X ![t₀, 0, 0]) ≤
        burnsideB46_p5_Xe0 K) hδ'
    have e : g2Act h⁻¹ (g2Act (h * g2X ![s, 0, 0] * h⁻¹) y - y) =
        g2Act (g2X ![s, 0, 0]) (g2Act h⁻¹ y) - g2Act h⁻¹ y := by
      rw [map_sub, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    show g2Act (h * g2X ![s, 0, 0] * h⁻¹) y - y ∈ gmapG h (stdF K 3)
    rw [mem_gmapG, e]
    exact burnsideB46_p5_xs_sub_mem s _
  have hF2 : ∀ w ∈ gmapG h (stdF K 3), ∃ z, g2Act (h * g2X ![t₀, 0, 0] * h⁻¹) z - z = w := by
    intro w hw
    obtain ⟨z', hz'⟩ := (burnsideB46_p5_commQ_xs_iff ht₀ _).mpr (mem_gmapG.mp hw)
    refine ⟨g2Act h z', ?_⟩
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, ← map_sub, hz', g2Act_apply_inv]
  refine ⟨_, _, _, _, _, _, hcfg, ?_, ?_, ?_⟩
  · rw [hA1, hZ1]
    have hcomm : ∀ a ∈ ((Z1 K).map c).map (burnsideB46_pi π), ∀ b ∈ R, a * b = b * a := by
      rintro _ ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩ b hb
      rw [hRmap] at hb
      obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩ := hb
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, burnsideB46_p5_Z1_comm_xs]
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij a ha b hb
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm a ha b hb
      · exact (hcomm b hb a ha).symm
      · exact absurd rfl hij
    · refine (iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)).mpr
        ?_
      show Disjoint (((Z1 K).map c).map (burnsideB46_pi π)) R
      rw [disjoint_iff, hRmap]
      change ((Z1 K).map c).map (burnsideB46_pi π) ⊓ ((burnsideB46_p5_Xe0 K).map c).map
        (burnsideB46_pi π) = ⊥
      rw [← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_inf _ _ _ hcinj,
        burnsideB46_p5_Z1_inf_Xe0, Subgroup.map_bot, Subgroup.map_bot]
    · have hs : (⨆ i, (![((Z1 K).map c).map (burnsideB46_pi π), R] :
          Fin 2 → Subgroup (MulAut V)) i) = ((Z1 K).map c).map (burnsideB46_pi π) ⊔ R := by
        apply le_antisymm
        · exact iSup_le fun i => by fin_cases i <;> simp
        · exact sup_le (le_iSup (fun i => (![((Z1 K).map c).map (burnsideB46_pi π), R] :
            Fin 2 → Subgroup (MulAut V)) i) 0) (le_iSup (fun i => (![((Z1 K).map c).map
              (burnsideB46_pi π), R] : Fin 2 → Subgroup (MulAut V)) i) 1)
      rw [hs, hRmap]
      change _ ⊔ ((burnsideB46_p5_Xe0 K).map c).map _ = _
      rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← burnsideB46_p5_A1_eq_sup]
  · rw [hF3, hRmap]
    refine ⟨?_, ?_, ?_⟩
    · rw [ht₀r, hzp, burnsideB46_cPre_map H, hfixr]
    · rw [burnsideB46_cPre_map H, hfixX]
    · rw [ht₀r]
      exact burnsideB46_p5_commV_eq H (h * g2X ![t₀, 0, 0] * h⁻¹) (gmapG h (stdF K 3)) hF1 hF2
  · have hcore : pCoreOf 2 ((burnsideB46_P1 K (g2Act h (eu 0 (1 : K)))).map (burnsideB46_pi π)) =
        ((pCoreOf 2 (stabV0 K)).map c).map (burnsideB46_pi π) := by
      rw [burnsideB46_pCoreOf_map _ hinj]
      change (burnsideB46_R1 K (g2Act h (eu 0 (1 : K)))).map (burnsideB46_pi π) = _
      rw [hR1]
    refine ⟨((burnsideB46_p5_Lev K).map c).map (burnsideB46_pi π), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hP1]
      exact Subgroup.map_mono (Subgroup.map_mono inf_le_left)
    · rw [hcore, ← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_inf _ _ _ hcinj,
        burnsideB46_p5_Lev_inf_core, Subgroup.map_bot, Subgroup.map_bot]
    · rw [hcore, hP1, ← Subgroup.map_sup, ← Subgroup.map_sup, burnsideB46_p5_Lev_sup_core]
    · have hN : Subgroup.normalizer ((burnsideB46_p5_Xconj K h : Subgroup ↥(cayleyGroup K)) :
          Set ↥(cayleyGroup K)) = (A1 K ⊔ burnsideB46_p5_Lev K).map c := by
        unfold burnsideB46_p5_Xconj
        rw [← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj h).bijective,
          burnsideB46_p5_normalizer_Xe0_eq]
      rw [hRmap, burnsideB46_p5_L_inf_normalizer H, hN, hA1, ← Subgroup.map_sup,
        ← Subgroup.map_sup]

end V6

section P5c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_6 (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_p5_part6_core hqs H hn

end P5c

section P5d

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_5 (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) := by
  haveI : CharP K 2 := burnsideB46_charP H
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2 z hz hz1
  obtain ⟨x, hx0, hV₁, hP₁, hR₁, hZ₁, hV₃⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, hZ, hP, hR, hV⟩ := burnsideB46_p4_cfg2 hqs H hn hx0 hP₁ hcfg2
  have hZ₂ : IsLongRootSub π Z₂ := by
    rw [hZ]
    exact burnsideB46_p4_isLongRootSub π c
  exact burnsideB46_p5_part5_core H hn hZ₂ hcfg2.2.2.2.1 hz hz1

end P5d

section P5n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_p5_exists_sl2E1_gen (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ s ∈ sl2E1 K, levi2Mat s = (M : Matrix (Fin 2) (Fin 2) K) := by
  have hM : M ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K)]
    exact Subgroup.mem_top M
  induction hM using Subgroup.closure_induction with
  | mem M hM =>
    obtain ⟨i, j, hij, t, rfl⟩ := hM
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · refine ⟨g2Y ![0, t, 0], Subgroup.subset_closure ⟨t, Or.inr rfl⟩, ?_⟩
      rw [levi2Mat_y1, CFSG.LinearGroups.coe_transvection]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    · refine ⟨g2X ![0, t, 0], Subgroup.subset_closure ⟨t, Or.inl rfl⟩, ?_⟩
      rw [levi2Mat_x1, CFSG.LinearGroups.coe_transvection]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    · exact absurd rfl hij
  | one =>
    exact ⟨1, Subgroup.one_mem _, by rw [levi2Mat_one]; rfl⟩
  | mul M N _ _ hM hN =>
    obtain ⟨s, hs, hsM⟩ := hM
    obtain ⟨t, ht, htN⟩ := hN
    refine ⟨s * t, Subgroup.mul_mem _ hs ht, ?_⟩
    rw [levi2Mat_mul (sl2E1_le_stabQ ht), hsM, htN]
    rfl
  | inv M _ hM =>
    obtain ⟨s, hs, hsM⟩ := hM
    have hsi : s⁻¹ ∈ sl2E1 K := Subgroup.inv_mem _ hs
    refine ⟨s⁻¹, hsi, ?_⟩
    have h1 := levi2Mat_mul (g := s) (sl2E1_le_stabQ hsi)
    rw [mul_inv_cancel, levi2Mat_one, hsM] at h1
    have h2 : (M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) * M = 1 := inv_mul_cancel M
    have h3 : (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        (M : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, h2]
      rfl
    calc levi2Mat s⁻¹ = (1 : Matrix (Fin 2) (Fin 2) K) * levi2Mat s⁻¹ := (one_mul _).symm
      _ = (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            (M : Matrix (Fin 2) (Fin 2) K)) * levi2Mat s⁻¹ := by rw [h3]
      _ = ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((M : Matrix (Fin 2) (Fin 2) K) * levi2Mat s⁻¹) := Matrix.mul_assoc _ _ _
      _ = ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [← h1, mul_one]

theorem burnsideB46_p5_twoPrimeResidual_gen [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    CFSG.Quasithin.twoPrimeResidual (stabQ (stdF K 2)) = stabQ2Det K := by
  have hfin := finite_cayleyGroup (F := K)
  apply le_antisymm
  · refine iInf₂_le (stabQ2Det K) ⟨fun g hg => hg.1, ?_, ?_⟩
    · have key : ∀ g ∈ stabQ (stdF K 2), ∀ h ∈ stabQ2Det K, g * h * g⁻¹ ∈ stabQ2Det K := by
        rintro g hg h ⟨hhP, hhdet⟩
        have hgi := (stabQ (stdF K 2)).inv_mem hg
        refine ⟨(stabQ (stdF K 2)).mul_mem ((stabQ (stdF K 2)).mul_mem hg hhP) hgi, ?_⟩
        rw [levi2Mat_mul hgi, levi2Mat_mul hhP, Matrix.det_mul, Matrix.det_mul, hhdet, mul_one]
        exact det_levi2Mat_inv hg
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact key g hg h
      · intro hh
        have := key g⁻¹ ((stabQ (stdF K 2)).inv_mem hg) _ hh
        simpa [mul_assoc] using this
    · let ν₀ : ↥(stabQ (stdF K 2)) →* K :=
        { toFun := fun g => (levi2Mat g.1).det
          map_one' := by simp [levi2Mat_one]
          map_mul' := fun a b => by
            change (levi2Mat (a.1 * b.1)).det = _
            rw [levi2Mat_mul b.2, Matrix.det_mul] }
      have hker : ν₀.toHomUnits.ker = (stabQ2Det K).subgroupOf (stabQ (stdF K 2)) := by
        ext g
        simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          refine ⟨g.2, ?_⟩
          have := congrArg Units.val h
          simpa [ν₀] using this
        · rintro ⟨-, h⟩
          apply Units.ext
          simpa [ν₀] using h
      have hidx : (stabQ2Det K).relIndex (stabQ (stdF K 2)) = Nat.card ν₀.toHomUnits.range := by
        rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
      rw [hidx]
      intro h2
      have hdvd : Nat.card ν₀.toHomUnits.range ∣ Nat.card Kˣ :=
        Subgroup.card_subgroup_dvd_card _
      rw [Nat.card_units, hK] at hdvd
      have h3 := h2.trans hdvd
      have h5 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have h6 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨hNH, hnorm, hodd⟩ := hN
    have h2el : ∀ x ∈ stabQ (stdF K 2), (∃ k, x ^ 2 ^ k = 1) → x ∈ N := fun x hx ⟨k, hk⟩ =>
      burnsideB46_p5_two_elt_mem hNH hnorm hodd hx hk
    have hsl : sl2E1 K ≤ N := by
      rw [sl2E1, Subgroup.closure_le]
      rintro g ⟨t, rfl | rfl⟩
      · exact h2el _ (sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inl rfl⟩))
          ⟨1, by rw [pow_one, pow_two, g2X_mul_self]⟩
      · exact h2el _ (sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inr rfl⟩))
          ⟨1, by rw [pow_one, pow_two, g2Y_mul_self]⟩
    rintro g ⟨hgP, hgdet⟩
    obtain ⟨s, hs, hsM⟩ := burnsideB46_p5_exists_sl2E1_gen ⟨levi2Mat g, hgdet⟩
    have hsP : s ∈ stabQ (stdF K 2) := sl2E1_le_stabQ hs
    have hsi := (stabQ (stdF K 2)).inv_mem hsP
    have hgsP : g * s⁻¹ ∈ stabQ (stdF K 2) := (stabQ (stdF K 2)).mul_mem hgP hsi
    have hker : g * s⁻¹ ∈ U0 K := by
      refine burnsideB46_p5_levi2_ker_le hgsP ?_
      have h1 := levi2Mat_mul (g := s) hsi
      rw [mul_inv_cancel, levi2Mat_one] at h1
      rw [levi2Mat_mul hsi]
      have hsM' : levi2Mat s = levi2Mat g := hsM
      rw [← hsM']
      exact h1.symm
    obtain ⟨k, hk⟩ := isPGroup_U0 (F := K) ⟨g * s⁻¹, hker⟩
    have hgs : g * s⁻¹ ∈ N := h2el _ hgsP ⟨k, by simpa using congrArg Subtype.val hk⟩
    have := N.mul_mem hgs (hsl hs)
    simpa using this

theorem burnsideB46_p5_centralizer_eq_tpr_gen [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h : ↥(cayleyGroup K)) :
    Subgroup.centralizer ((burnsideB46_p5_Dconj K h : Subgroup ↥(cayleyGroup K)) :
      Set ↥(cayleyGroup K)) =
      CFSG.Quasithin.twoPrimeResidual (Subgroup.normalizer ((burnsideB46_p5_Dconj K h :
        Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K))) := by
  rw [burnsideB46_p5_centralizer_Dconj, burnsideB46_p5_normalizer_Dconj,
    burnsideB46_p5_tpr_map _ (MulAut.conj h).injective, burnsideB46_p5_twoPrimeResidual_gen hn hK]

end P5n

section V5n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped Matrix

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_p5_part5_core_gen [CharP K 2] [Finite K] (H : burnsideB46_Hyp V n K G L π θ)
    {Z₂ P₂ : Subgroup (MulAut V)} (hZ₂ : IsLongRootSub π Z₂)
    (hP₂ : P₂ = L ⊓ Subgroup.normalizer (Z₂ : Set (MulAut V))) {z : MulAut V} (hz : z ∈ Z₂)
    (hz1 : z ≠ 1) :
    (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
        ∃ l ∈ L, x = l * z * l⁻¹) ∧
      (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * r * l⁻¹) ∧
        ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
        ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
      (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
        L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = CFSG.Quasithin.twoPrimeResidual P₂) := by
  have hinj := burnsideB46_pi_injective H
  have hK : Nat.card K = 2 ^ n := H.card
  obtain ⟨h₂, hh₂⟩ := burnsideB46_p5_isLongRootSub_iff.mp hZ₂
  obtain ⟨s₀, hz0⟩ := (hh₂ z).mp hz
  have hs₀ : s₀ ≠ 0 := by
    rintro rfl
    apply hz1
    rw [hz0, burnsideB46_p5_tL_zero]
    simp
  have hZ₂eq : Z₂ = (burnsideB46_p5_Dconj K h₂).map (burnsideB46_pi π) := by
    ext ψ
    rw [hh₂ ψ]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, burnsideB46_p5_mem_Dconj.mpr ⟨s, rfl⟩, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Dconj.mp hγ
      exact ⟨s, rfl⟩
  obtain ⟨g₂, hg₂⟩ : burnsideB46_p5_IsLongEl (h₂ * tL s₀ * h₂⁻¹) :=
    burnsideB46_p5_isLongEl_iff.mpr ⟨h₂, s₀, hs₀, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨Z, hZ, hxZ, hx1⟩
      obtain ⟨h, hh⟩ := burnsideB46_p5_isLongRootSub_iff.mp hZ
      obtain ⟨s, hs⟩ := (hh x).mp hxZ
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hx1
        rw [hs, burnsideB46_p5_tL_zero]
        simp
      obtain ⟨g₁, hg₁⟩ : burnsideB46_p5_IsLongEl (h * tL s * h⁻¹) :=
        burnsideB46_p5_isLongEl_iff.mpr ⟨h, s, hs0, rfl⟩
      refine ⟨burnsideB46_pi π (g₁ * g₂⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
      rw [hs, hz0, hg₁, hg₂]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
      refine ⟨(burnsideB46_p5_Dconj K (γ * h₂)).map (burnsideB46_pi π), ?_, ?_, ?_⟩
      · refine burnsideB46_p5_isLongRootSub_iff.mpr ⟨γ * h₂, fun ψ => ?_⟩
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨s, rfl⟩ := burnsideB46_p5_mem_Dconj.mp hy
          exact ⟨s, rfl⟩
        · rintro ⟨s, rfl⟩
          exact ⟨_, burnsideB46_p5_mem_Dconj.mpr ⟨s, rfl⟩, rfl⟩
      · rw [hz0]
        refine ⟨(γ * h₂) * tL s₀ * (γ * h₂)⁻¹, burnsideB46_p5_mem_Dconj.mpr ⟨s₀, rfl⟩, ?_⟩
        simp only [map_mul, map_inv]
        group
      · intro h1
        apply hz1
        have h2 : burnsideB46_pi π γ * z * (burnsideB46_pi π γ)⁻¹ = 1 := h1
        calc z = (burnsideB46_pi π γ)⁻¹ * (burnsideB46_pi π γ * z * (burnsideB46_pi π γ)⁻¹) *
              burnsideB46_pi π γ := by group
          _ = 1 := by rw [h2]; group
  · have hshort1 : burnsideB46_p5_IsShortEl (g2X ![(1 : K), 0, 0]) := ⟨1, by group⟩
    refine ⟨burnsideB46_pi π (g2X ![1, 0, 0]), ?_, ?_, ?_, ?_⟩
    · refine ⟨(burnsideB46_p5_Xe0 K).map (burnsideB46_pi π), ?_, ⟨_, ⟨1, rfl⟩, rfl⟩, ?_⟩
      · refine burnsideB46_p5_isShortRootSub_iff.mpr ⟨1, fun ψ => ?_⟩
        constructor
        · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
          exact ⟨t, by simp⟩
        · rintro ⟨t, rfl⟩
          exact ⟨_, ⟨t, rfl⟩, by simp⟩
      · intro h1
        exact hshort1.ne_one (hinj (by rw [map_one]; exact h1))
    · intro x
      constructor
      · rintro ⟨Z, hZ, hxZ, hx1⟩
        obtain ⟨h, hh⟩ := burnsideB46_p5_isShortRootSub_iff.mp hZ
        obtain ⟨t, ht⟩ := (hh x).mp hxZ
        have ht0 : t ≠ 0 := by
          rintro rfl
          apply hx1
          rw [ht, burnsideB46_p5_xs_zero]
          simp
        obtain ⟨g₁, hg₁⟩ : burnsideB46_p5_IsShortEl (h * g2X ![t, 0, 0] * h⁻¹) :=
          burnsideB46_p5_isShortEl_iff.mpr ⟨h, t, ht0, rfl⟩
        refine ⟨burnsideB46_pi π g₁, burnsideB46_pi_mem_L H _, ?_⟩
        rw [ht, hg₁]
        simp only [map_mul, map_inv]
      · rintro ⟨l, hl, rfl⟩
        obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
        refine ⟨(burnsideB46_p5_Xconj K γ).map (burnsideB46_pi π), ?_, ?_, ?_⟩
        · refine burnsideB46_p5_isShortRootSub_iff.mpr ⟨γ, fun ψ => ?_⟩
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨t, rfl⟩ := burnsideB46_p5_mem_Xconj.mp hy
            exact ⟨t, rfl⟩
          · rintro ⟨t, rfl⟩
            exact ⟨_, burnsideB46_p5_mem_Xconj.mpr ⟨t, rfl⟩, rfl⟩
        · refine ⟨γ * g2X ![1, 0, 0] * γ⁻¹, burnsideB46_p5_mem_Xconj.mpr ⟨1, rfl⟩, ?_⟩
          simp only [map_mul, map_inv]
        · intro h1
          have h2 : burnsideB46_pi π γ * burnsideB46_pi π (g2X ![1, 0, 0]) *
              (burnsideB46_pi π γ)⁻¹ = 1 := h1
          have h3 : γ * g2X ![1, 0, 0] * γ⁻¹ = 1 :=
            hinj (by rw [map_one, ← h2]; simp only [map_mul, map_inv])
          exact hshort1.ne_one (by
            calc g2X ![(1 : K), 0, 0] = γ⁻¹ * (γ * g2X ![1, 0, 0] * γ⁻¹) * γ := by group
              _ = 1 := by rw [h3]; group)
    · rintro ⟨l, hl, hlr⟩
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hl
      rw [hz0] at hlr
      have h3 : g2X ![(1 : K), 0, 0] = γ * (h₂ * tL s₀ * h₂⁻¹) * γ⁻¹ :=
        hinj (by rw [hlr]; simp only [map_mul, map_inv])
      rw [hg₂] at h3
      exact burnsideB46_p5_not_long_short ⟨γ * g₂, by rw [h3]; group⟩ hshort1
    · intro x hxL hx1 hx2
      obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hxL
      have hγ2 : γ * γ = 1 := hinj (by rw [map_mul, ← sq, hx2, map_one])
      have hγ1 : γ ≠ 1 := fun h => hx1 (by rw [h, map_one])
      rcases burnsideB46_p5_invol_cases hγ2 hγ1 with ⟨g, hg⟩ | ⟨g, hg⟩
      · left
        refine ⟨burnsideB46_pi π (g * g₂⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
        rw [hz0, hg₂, hg]
        simp only [map_mul, map_inv]
        group
      · right
        refine ⟨burnsideB46_pi π g, burnsideB46_pi_mem_L H _, ?_⟩
        rw [hg]
        simp only [map_mul, map_inv]
  · have hzset : ({z} : Set (MulAut V)) = burnsideB46_pi π '' {h₂ * tL s₀ * h₂⁻¹} := by
      rw [Set.image_singleton, hz0]
    have hZ₂set : (Z₂ : Set (MulAut V)) = burnsideB46_pi π ''
        ((burnsideB46_p5_Dconj K h₂ : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) := by
      rw [hZ₂eq]
      rfl
    have hC1 : L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
        L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) := by
      rw [hzset, hZ₂set, burnsideB46_p5_L_inf_centralizer H, burnsideB46_p5_L_inf_centralizer H,
        burnsideB46_p5_centralizer_single_Dconj h₂ hs₀]
    refine ⟨hC1, ?_⟩
    have hP₂' : P₂ = (Subgroup.normalizer ((burnsideB46_p5_Dconj K h₂ :
        Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K))).map (burnsideB46_pi π) := by
      rw [hP₂, hZ₂eq, burnsideB46_p5_L_inf_normalizer H]
    rw [hP₂', burnsideB46_p5_tpr_map _ hinj,
      ← burnsideB46_p5_centralizer_eq_tpr_gen H.one_le hK h₂, hZ₂set,
      burnsideB46_p5_L_inf_centralizer H]

theorem burnsideB46_p5_cfg1_of_point_GL [CharP K 2] [Finite K]
    (H : burnsideB46_Hyp V n K G L π θ) (hGL : G = L) {x : Ix3 → K} (hx : x ≠ 0) :
    B46Cfg1 G L θ (burnsideB46_pre θ (burnsideB46_pt K x))
      ((burnsideB46_P1 K x).map (burnsideB46_pi π)) ((burnsideB46_R1 K x).map (burnsideB46_pi π))
      ((burnsideB46_Z1 K x).map (burnsideB46_pi π))
      (burnsideB46_pre θ (burnsideB46_F3 K x)) ((burnsideB46_A1 K x).map (burnsideB46_pi π)) := by
  have hinj := burnsideB46_pi_injective H
  have hP : (burnsideB46_P1 K x).map (burnsideB46_pi π) =
      L ⊓ stabSub (burnsideB46_pre θ (burnsideB46_pt K x)) := (burnsideB46_stab_pre H _).symm
  have hR : (burnsideB46_R1 K x).map (burnsideB46_pi π) =
      pCoreOf 2 ((burnsideB46_P1 K x).map (burnsideB46_pi π)) :=
    (burnsideB46_pCoreOf_map _ hinj (burnsideB46_P1 K x)).symm
  have hZ : (burnsideB46_Z1 K x).map (burnsideB46_pi π) =
      centerOf ((burnsideB46_R1 K x).map (burnsideB46_pi π)) :=
    (burnsideB46_centerOf_map _ hinj (burnsideB46_R1 K x)).symm
  refine ⟨burnsideB46_isFPre_iff.mpr ⟨burnsideB46_pt K x, finrank_span_singleton hx, rfl⟩, hP, hR,
    hZ, (burnsideB46_cPre_map H (burnsideB46_Z1 K x)).symm, fun g => ?_⟩
  have key : (∀ v ∈ burnsideB46_pre θ (burnsideB46_F3 K x), g v * v⁻¹ ∈ fixV L) ↔
      ∀ v, burnsideB46_f θ v ∈ burnsideB46_F3 K x → burnsideB46_f θ (g v) = burnsideB46_f θ v := by
    constructor
    · intro h v hv
      have := (burnsideB46_f_eq_zero_iff H _).2 (h v hv)
      rwa [burnsideB46_f_sub, sub_eq_zero] at this
    · intro h v hv
      refine (burnsideB46_f_eq_zero_iff H _).1 ?_
      rw [burnsideB46_f_sub, sub_eq_zero]
      exact h v hv
  rw [key]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨H.le (burnsideB46_pi_mem_L H γ), fun v hv => ?_⟩
    rw [burnsideB46_f_act H]
    exact hγ _ hv
  · rintro ⟨hgG, hg⟩
    have hgL : g ∈ L := hGL ▸ hgG
    obtain ⟨γ, rfl⟩ := (burnsideB46_mem_L' H).1 hgL
    refine ⟨γ, fun w hw => ?_, rfl⟩
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H w
    rw [← burnsideB46_f_act H]
    exact hg v hw

theorem burnsideB46_p5_part6_core_gen [CharP K 2] [Finite K] [Finite V]
    (H : burnsideB46_Hyp V n K G L π θ)
    (hcfgpt : ∀ {x : Ix3 → K}, x ≠ 0 → burnsideB46_F3 K x ≠ ⊥ →
      B46Cfg1 G L θ (burnsideB46_pre θ (burnsideB46_pt K x))
        ((burnsideB46_P1 K x).map (burnsideB46_pi π)) ((burnsideB46_R1 K x).map (burnsideB46_pi π))
        ((burnsideB46_Z1 K x).map (burnsideB46_pi π))
        (burnsideB46_pre θ (burnsideB46_F3 K x)) ((burnsideB46_A1 K x).map (burnsideB46_pi π))) :
    ∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) =
          L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
        (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁ := by
  intro R hR r hrR hr1
  have hinj := burnsideB46_pi_injective H
  obtain ⟨h, hh⟩ := burnsideB46_p5_isShortRootSub_iff.mp hR
  obtain ⟨t₀, ht₀r⟩ := (hh r).mp hrR
  have ht₀ : t₀ ≠ 0 := by
    rintro rfl
    apply hr1
    rw [ht₀r, burnsideB46_p5_xs_zero]
    simp
  have hRmap : R = (burnsideB46_p5_Xconj K h).map (burnsideB46_pi π) := by
    ext ψ
    rw [hh ψ]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, burnsideB46_p5_mem_Xconj.mpr ⟨t, rfl⟩, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨t, rfl⟩ := burnsideB46_p5_mem_Xconj.mp hγ
      exact ⟨t, rfl⟩
  have hC : L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) =
      L ⊓ Subgroup.centralizer (R : Set (MulAut V)) := by
    have hrset : ({r} : Set (MulAut V)) =
        burnsideB46_pi π '' {h * g2X ![t₀, 0, 0] * h⁻¹} := by
      rw [Set.image_singleton, ht₀r]
    have hRset : (R : Set (MulAut V)) = burnsideB46_pi π ''
        ((burnsideB46_p5_Xconj K h : Subgroup ↥(cayleyGroup K)) : Set ↥(cayleyGroup K)) := by
      rw [hRmap]
      rfl
    rw [hrset, hRset, burnsideB46_p5_L_inf_centralizer H, burnsideB46_p5_L_inf_centralizer H,
      burnsideB46_p5_centralizer_single_Xconj h ht₀]
  refine ⟨hC, ?_⟩
  set c : ↥(cayleyGroup K) →* ↥(cayleyGroup K) := (MulAut.conj h).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj h).injective
  obtain ⟨hP1, hR1, hZ1, hF3, hA1⟩ := burnsideB46_p5_obj_act h
  have hx : g2Act h (eu 0 (1 : K)) ≠ 0 := burnsideB46_p5_g2Act_ne_zero h
  have hF3ne : burnsideB46_F3 K (g2Act h (eu 0 (1 : K))) ≠ ⊥ := by
    intro hbot
    have := burnsideB46_p3_F3_card hx
    rw [hbot, finrank_bot] at this
    omega
  have hcfg := hcfgpt hx hF3ne
  have hfixX : fixSub (burnsideB46_p5_Xconj K h) = gmapG h (stdF K 3) := by
    unfold burnsideB46_p5_Xconj
    rw [burnsideB46_p3_fixSub_map_conj, burnsideB46_p5_fixSub_Xe0]
  have hzp : Subgroup.zpowers (burnsideB46_pi π (h * g2X ![t₀, 0, 0] * h⁻¹)) =
      (Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹)).map (burnsideB46_pi π) :=
    (MonoidHom.map_zpowers _ _).symm
  have hzpc : Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹) =
      (Subgroup.zpowers (g2X ![t₀, 0, 0])).map c := (MonoidHom.map_zpowers c _).symm
  have hfixr : fixSub (Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹)) = gmapG h (stdF K 3) := by
    rw [hzpc, burnsideB46_p3_fixSub_map_conj, burnsideB46_p5_fixSub_zpowers_xs ht₀]
  have hF1 : ∀ δ ∈ Subgroup.zpowers (h * g2X ![t₀, 0, 0] * h⁻¹), ∀ y,
      g2Act δ y - y ∈ gmapG h (stdF K 3) := by
    intro δ hδ y
    rw [hzpc] at hδ
    obtain ⟨δ', hδ', rfl⟩ := hδ
    obtain ⟨s, rfl⟩ : δ' ∈ burnsideB46_p5_Xe0 K :=
      (Subgroup.zpowers_le.mpr ⟨t₀, rfl⟩ : Subgroup.zpowers (g2X ![t₀, 0, 0]) ≤
        burnsideB46_p5_Xe0 K) hδ'
    have e : g2Act h⁻¹ (g2Act (h * g2X ![s, 0, 0] * h⁻¹) y - y) =
        g2Act (g2X ![s, 0, 0]) (g2Act h⁻¹ y) - g2Act h⁻¹ y := by
      rw [map_sub, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    show g2Act (h * g2X ![s, 0, 0] * h⁻¹) y - y ∈ gmapG h (stdF K 3)
    rw [mem_gmapG, e]
    exact burnsideB46_p5_xs_sub_mem s _
  have hF2 : ∀ w ∈ gmapG h (stdF K 3), ∃ z, g2Act (h * g2X ![t₀, 0, 0] * h⁻¹) z - z = w := by
    intro w hw
    obtain ⟨z', hz'⟩ := (burnsideB46_p5_commQ_xs_iff ht₀ _).mpr (mem_gmapG.mp hw)
    refine ⟨g2Act h z', ?_⟩
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, ← map_sub, hz', g2Act_apply_inv]
  refine ⟨_, _, _, _, _, _, hcfg, ?_, ?_, ?_⟩
  · rw [hA1, hZ1]
    have hcomm : ∀ a ∈ ((Z1 K).map c).map (burnsideB46_pi π), ∀ b ∈ R, a * b = b * a := by
      rintro _ ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩ b hb
      rw [hRmap] at hb
      obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩ := hb
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, burnsideB46_p5_Z1_comm_xs]
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij a ha b hb
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hcomm a ha b hb
      · exact (hcomm b hb a ha).symm
      · exact absurd rfl hij
    · refine (iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)).mpr
        ?_
      show Disjoint (((Z1 K).map c).map (burnsideB46_pi π)) R
      rw [disjoint_iff, hRmap]
      change ((Z1 K).map c).map (burnsideB46_pi π) ⊓ ((burnsideB46_p5_Xe0 K).map c).map
        (burnsideB46_pi π) = ⊥
      rw [← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_inf _ _ _ hcinj,
        burnsideB46_p5_Z1_inf_Xe0, Subgroup.map_bot, Subgroup.map_bot]
    · have hs : (⨆ i, (![((Z1 K).map c).map (burnsideB46_pi π), R] :
          Fin 2 → Subgroup (MulAut V)) i) = ((Z1 K).map c).map (burnsideB46_pi π) ⊔ R := by
        apply le_antisymm
        · exact iSup_le fun i => by fin_cases i <;> simp
        · exact sup_le (le_iSup (fun i => (![((Z1 K).map c).map (burnsideB46_pi π), R] :
            Fin 2 → Subgroup (MulAut V)) i) 0) (le_iSup (fun i => (![((Z1 K).map c).map
              (burnsideB46_pi π), R] : Fin 2 → Subgroup (MulAut V)) i) 1)
      rw [hs, hRmap]
      change _ ⊔ ((burnsideB46_p5_Xe0 K).map c).map _ = _
      rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← burnsideB46_p5_A1_eq_sup]
  · rw [hF3, hRmap]
    refine ⟨?_, ?_, ?_⟩
    · rw [ht₀r, hzp, burnsideB46_cPre_map H, hfixr]
    · rw [burnsideB46_cPre_map H, hfixX]
    · rw [ht₀r]
      exact burnsideB46_p5_commV_eq H (h * g2X ![t₀, 0, 0] * h⁻¹) (gmapG h (stdF K 3)) hF1 hF2
  · have hcore : pCoreOf 2 ((burnsideB46_P1 K (g2Act h (eu 0 (1 : K)))).map (burnsideB46_pi π)) =
        ((pCoreOf 2 (stabV0 K)).map c).map (burnsideB46_pi π) := by
      rw [burnsideB46_pCoreOf_map _ hinj]
      change (burnsideB46_R1 K (g2Act h (eu 0 (1 : K)))).map (burnsideB46_pi π) = _
      rw [hR1]
    refine ⟨((burnsideB46_p5_Lev K).map c).map (burnsideB46_pi π), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hP1]
      exact Subgroup.map_mono (Subgroup.map_mono inf_le_left)
    · rw [hcore, ← Subgroup.map_inf _ _ _ hinj, ← Subgroup.map_inf _ _ _ hcinj,
        burnsideB46_p5_Lev_inf_core, Subgroup.map_bot, Subgroup.map_bot]
    · rw [hcore, hP1, ← Subgroup.map_sup, ← Subgroup.map_sup, burnsideB46_p5_Lev_sup_core]
    · have hN : Subgroup.normalizer ((burnsideB46_p5_Xconj K h : Subgroup ↥(cayleyGroup K)) :
          Set ↥(cayleyGroup K)) = (A1 K ⊔ burnsideB46_p5_Lev K).map c := by
        unfold burnsideB46_p5_Xconj
        rw [← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj h).bijective,
          burnsideB46_p5_normalizer_Xe0_eq]
      rw [hRmap, burnsideB46_p5_L_inf_normalizer H, hN, hA1, ← Subgroup.map_sup,
        ← Subgroup.map_sup]

end V5n

section P5na

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_5_one (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have _hn1 := hn1
  have hnormLG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hGL]
    exact Subgroup.le_normalizer
  intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2 z hz hz1
  obtain ⟨x, hx0, hV₁, hP₁, hR₁, hZ₁, hV₃⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, hZ, hP, hR, hV⟩ := burnsideB46_p4_n1_cfg2 H hnormLG hx0 hP₁ hcfg2
  have hZ₂ : IsLongRootSub π Z₂ := by
    rw [hZ]
    exact burnsideB46_p4_isLongRootSub π c
  exact burnsideB46_p5_part5_core_gen H hZ₂ hcfg2.2.2.2.1 hz hz1

theorem burnsideB46_part_6_one (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1) (hGL : G = L) :
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have _hn1 := hn1
  exact burnsideB46_p5_part6_core_gen H fun hx _ => burnsideB46_p5_cfg1_of_point_GL H hGL hx

end P5na

section W11

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


theorem burnsideB46_w11_polarQ_frobQ {K : Type} [Field K] (σ : K →+* K) (a b : Ix3 → K) :
    polarQ (frobQ σ a) (frobQ σ b) = σ (polarQ a b) := by
  simp only [polarQ, frobQ, map_add, map_mul]

theorem burnsideB46_w11_polarQ_smul_smul {K : Type} [Field K] (c : K) (a b : Ix3 → K) :
    polarQ (c • a) (c • b) = c * c * polarQ a b := by
  rw [polarQ_smul_left, polarQ_smul_right]
  ring

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_w11_qr_Z1_std {z : ↥(cayleyGroup K)} (hz : z ∈ Z1 K) (w : Ix3 → K) :
    qr z w = 0 := by
  obtain ⟨v, rfl⟩ := hz
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold qr
  rw [g2Act_g2A_uSL]
  simp only [polarQ, q6_apply_inl0, q6_apply_inl1, q6_apply_inl2, q6_apply_inr0, q6_apply_inr1,
    q6_apply_inr2]
  linear_combination (v.1 * w (.inl 1) * w (.inr 0) + v.2 * w (.inl 2) * w (.inr 0) +
    w (.inl 0) * w (.inr 0) + w (.inl 1) * w (.inr 1) + w (.inl 2) * w (.inr 2)) * h2

variable [Finite K]

theorem burnsideB46_w11_qr_Z1 {x : Ix3 → K} (hx : x ≠ 0) {z : ↥(cayleyGroup K)}
    (hz : z ∈ burnsideB46_Z1 K x) (w : Ix3 → K) : qr z w = 0 := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu, burnsideB46_p3_mem_map_conj] at hz
  have h := qr_conj γ⁻¹ z w
  rw [inv_inv] at h
  rw [← h]
  exact burnsideB46_w11_qr_Z1_std hz _

theorem burnsideB46_w11_R1_mem_Z1 {x : Ix3 → K} (hx : x ≠ 0) {r : ↥(cayleyGroup K)}
    (hr : r ∈ burnsideB46_R1 K x) (hq : ∀ w, qr r w = 0) : r ∈ burnsideB46_Z1 K x := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_R1_act, burnsideB46_p3_mem_map_conj] at hr
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_mem_map_conj, burnsideB46_p3_Z1_eu]
  obtain ⟨α, β, γ', p, q', hk⟩ := burnsideB46_p3_mem_R1_eu.mp hr
  have hq' : ∀ w, qr (g2X ![α, 0, 0] * g2Y ![0, β, γ'] * g2A (uSL p q' 0)) w = 0 := by
    intro w
    have h := qr_conj γ⁻¹ r (g2Act γ w)
    rw [inv_inv, g2Act_inv_apply] at h
    have hk' : g2X ![α, 0, 0] * g2Y ![0, β, γ'] * g2A (uSL p q' 0) = γ⁻¹ * r * γ := hk.symm
    rw [hk', h]
    exact hq _
  obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq_of_qr_zero hq'
  rw [hk, burnsideB46_p3_kerElt_zero]
  exact ⟨(p, q'), rfl⟩

theorem burnsideB46_w11_A1_le_R1 {x : Ix3 → K} (hx : x ≠ 0) :
    burnsideB46_A1 K x ≤ burnsideB46_R1 K x := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hx
  rw [burnsideB46_p3_A1_act, burnsideB46_p3_R1_act]
  refine Subgroup.map_mono ?_
  intro g hg
  have hg' : g ∈ A1 K := fun w hw => hg w (by rw [burnsideB46_p3_F3_eu]; exact hw)
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hg'
  exact burnsideB46_p3_mem_R1_eu.mpr ⟨α, 0, 0, p, q', rfl⟩

theorem burnsideB46_w11_A1_le_R1_eq {x y : Ix3 → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : burnsideB46_A1 K y ≤ burnsideB46_R1 K x) : burnsideB46_A1 K y = burnsideB46_A1 K x := by
  have hZ : burnsideB46_Z1 K y ≤ burnsideB46_Z1 K x := by
    intro z hz
    have hzA : z ∈ burnsideB46_A1 K y := fun w hw => mem_fixSub.1 hw z hz
    exact burnsideB46_w11_R1_mem_Z1 hx (h hzA) (burnsideB46_w11_qr_Z1 hy hz)
  have hF : burnsideB46_F3 K x ≤ burnsideB46_F3 K y := fun w hw z hz => hw z (hZ hz)
  have hF' : burnsideB46_F3 K x = burnsideB46_F3 K y :=
    Submodule.eq_of_le_of_finrank_eq hF
      (by rw [burnsideB46_p3_F3_card hx, burnsideB46_p3_F3_card hy])
  ext γ
  change (∀ w ∈ burnsideB46_F3 K y, g2Act γ w = w) ↔ (∀ w ∈ burnsideB46_F3 K x, g2Act γ w = w)
  rw [hF']

theorem burnsideB46_w11_F3_ne_bot {x : Ix3 → K} (hx : x ≠ 0) : burnsideB46_F3 K x ≠ ⊥ := by
  intro h
  have h3 := burnsideB46_p3_F3_card hx
  rw [h] at h3
  simp at h3

end Model

section VLevel

variable {K : Type} [Field K] [Finite K] {V : Type} [CommGroup V] [Finite V] {n : ℕ}
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_w11_conj_qr [CharP K 2] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) {g : MulAut V} (hg : g ∈ G)
    {γ γ' : ↥(cayleyGroup K)}
    (h : burnsideB46_pi π γ' = g * burnsideB46_pi π γ * g⁻¹) (hq : ∀ w, qr γ w = 0) :
    ∀ w, qr γ' w = 0 := by
  obtain ⟨c, γ₀, σ, hc, hform⟩ := burnsideB46_G_semilinear hqs H hn hg
  intro w
  obtain ⟨v, hv⟩ := burnsideB46_f_surj H w
  have e1 : w = c • g2Act γ₀ (frobQ (σ : K →+* K) (burnsideB46_f θ (g⁻¹ v))) := by
    rw [← hform, MulAut.apply_inv_self, hv]
  have e2 : g2Act γ' w =
      c • g2Act γ₀ (frobQ (σ : K →+* K) (g2Act γ (burnsideB46_f θ (g⁻¹ v)))) := by
    rw [← hv, ← burnsideB46_f_act H, h, MulAut.mul_apply, MulAut.mul_apply, hform,
      burnsideB46_f_act H]
  have h0 := hq (burnsideB46_f θ (g⁻¹ v))
  unfold qr at h0 ⊢
  rw [e2]
  conv_lhs => rw [e1]
  rw [burnsideB46_w11_polarQ_smul_smul, polarQ_g2Act, burnsideB46_w11_polarQ_frobQ, h0, map_zero,
    mul_zero]

structure burnsideB46_w11_Good [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) : Prop where
  normal : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L
  conj_qr : ∀ {g : MulAut V}, g ∈ G → ∀ {γ γ' : ↥(cayleyGroup K)},
    burnsideB46_pi π γ' = g * burnsideB46_pi π γ * g⁻¹ → (∀ w, qr γ w = 0) → ∀ w, qr γ' w = 0
  cfg2 : ∀ {x : Ix3 → K}, x ≠ 0 → ∀ {P₁ T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V},
    P₁ = (burnsideB46_P1 K x).map (burnsideB46_pi π) → B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
    ∃ c : ↥(cayleyGroup K), T ⊓ L = (U0 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      Z₂ = (burnsideB46_p4_Z0 K).map (burnsideB46_p4_ofHyp H c).Φ ∧
      R₂ = (burnsideB46_p4_R2 K).map (burnsideB46_p4_ofHyp H c).Φ
  A1red : ∀ {x : Ix3 → K}, x ≠ 0 → ∀ {V₃ : Subgroup V} {A₁ : Subgroup (MulAut V)},
    V₃ = burnsideB46_pre θ (burnsideB46_F3 K x) →
    (∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L) →
    A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π)

theorem burnsideB46_w11_good_ge2 [CharP K 2] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) : burnsideB46_w11_Good H where
  normal := burnsideB46_normal hqs H hn
  conj_qr := fun hg _ _ h hq => burnsideB46_w11_conj_qr hqs H hn hg h hq
  cfg2 := fun hx0 _ _ _ _ _ _ hP h => by
    obtain ⟨c, -, hT, hZ, -, hR, -⟩ := burnsideB46_p4_cfg2 hqs H hn hx0 hP h
    exact ⟨c, hT, hZ, hR⟩
  A1red := fun hx0 _ _ hV hA => burnsideB46_cfg1_A1 hqs H hn (burnsideB46_w11_F3_ne_bot hx0) hV hA

theorem burnsideB46_w11_strong_gen [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (hG : burnsideB46_w11_Good H)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁) :
    IsStrongClosedWrt Z₁ R₁ G := by
  obtain ⟨x, hx0, -, -, hR₁, hZ₁, -⟩ := burnsideB46_cfg1_point H hcfg
  intro z hz g hg hgz
  rw [hZ₁] at hz
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have hgzL : g * burnsideB46_pi π ζ * g⁻¹ ∈ L :=
    hG.normal g hg _ (burnsideB46_pi_mem_L H ζ)
  obtain ⟨ζ', hζ'⟩ := (burnsideB46_mem_L' H).1 hgzL
  have hζ'R : ζ' ∈ burnsideB46_R1 K x := by
    rw [hR₁] at hgz
    obtain ⟨ρ, hρ, hρ'⟩ := hgz
    have : ρ = ζ' := burnsideB46_pi_injective H (hρ'.trans hζ'.symm)
    exact this ▸ hρ
  have hqζ : ∀ w, qr ζ w = 0 := burnsideB46_w11_qr_Z1 hx0 hζ
  have hqζ' := hG.conj_qr hg hζ' hqζ
  have hZ := burnsideB46_w11_R1_mem_Z1 hx0 hζ'R hqζ'
  rw [← hζ', hZ₁]
  exact ⟨ζ', hZ, rfl⟩

theorem burnsideB46_w11_strong (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁) :
    IsStrongClosedWrt Z₁ R₁ G := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_w11_strong_gen H (burnsideB46_w11_good_ge2 hqs H hn) hcfg

theorem burnsideB46_w11_offenders (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁) :
    {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_part_13a hqs H hn (fun x hx => burnsideB46_w11_F3_ne_bot hx)
    (fun x hx => burnsideB46_p3_A1_conj H.card H.one_le hx) V₁ P₁ R₁ Z₁ V₃ A₁ hcfg

theorem burnsideB46_w11_ffJ_R1_gen [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (hG : burnsideB46_w11_Good H)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁)
    (hoff : {A | IsFFStarOffender G A} =
      {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom}) :
    ffJ R₁ = A₁ := by
  obtain ⟨x, hx0, -, -, hR₁, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  have hA₁ : A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) := hG.A1red hx0 hV₃ hcfg.2.2.2.2.2
  have hA₁R : A₁ ≤ R₁ := by
    rw [hA₁, hR₁]
    exact Subgroup.map_mono (burnsideB46_w11_A1_le_R1 hx0)
  have hA₁off : IsFFStarOffender G A₁ := by
    have h1 : A₁ ∈ {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} :=
      ⟨1, L.one_mem, by ext a; simp⟩
    rw [← hoff] at h1
    exact h1
  have hR₁L : R₁ ≤ L := by
    rw [hR₁]
    rintro _ ⟨γ, -, rfl⟩
    exact burnsideB46_pi_mem_L H γ
  unfold ffJ
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hAG : IsFFStarOffender G A := ⟨(hA.1.trans hR₁L).trans H.le, hA.2⟩
    have hmem : A ∈ {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
      rw [← hoff]
      exact hAG
    obtain ⟨l, hl, hAl⟩ := hmem
    obtain ⟨h, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    have hAeq : A = (burnsideB46_A1 K (g2Act h x)).map (burnsideB46_pi π) := by
      rw [hAl, hA₁, burnsideB46_of_map_conj, burnsideB46_p3_A1_act]
    have hhx : g2Act h x ≠ 0 := by
      intro h0
      apply hx0
      have h1 := g2Act_inv_apply h x
      rw [h0, map_zero] at h1
      exact h1.symm
    have hle : burnsideB46_A1 K (g2Act h x) ≤ burnsideB46_R1 K x := by
      have h2 : A ≤ R₁ := hA.1
      rw [hAeq, hR₁] at h2
      exact (Subgroup.map_le_map_iff_of_injective (burnsideB46_pi_injective H)).1 h2
    rw [hAeq, burnsideB46_w11_A1_le_R1_eq hx0 hhx hle, ← hA₁]
  · exact le_iSup₂_of_le A₁ ⟨hA₁R, hA₁off.2⟩ le_rfl

theorem burnsideB46_w11_ffJ_R1 (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁) :
    ffJ R₁ = A₁ := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_w11_ffJ_R1_gen H (burnsideB46_w11_good_ge2 hqs H hn) hcfg
    (burnsideB46_w11_offenders hqs H hn hcfg)

end VLevel

end W11

section W11a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] noncomputable def burnsideB46_w11_ell (γ : ↥(cayleyGroup K)) : Submodule K (Ix3 → K) :=
  LinearMap.range (burnsideB46_p5_T γ)

theorem burnsideB46_w11_mem_ell {γ : ↥(cayleyGroup K)} {y : Ix3 → K} :
    y ∈ burnsideB46_w11_ell γ ↔ ∃ w, burnsideB46_p5_T γ w = y := by
  unfold burnsideB46_w11_ell
  rw [LinearMap.mem_range]

theorem burnsideB46_w11_ell_conj (g γ : ↥(cayleyGroup K)) :
    burnsideB46_w11_ell (g * γ * g⁻¹) = gmapG g (burnsideB46_w11_ell γ) := by
  ext y
  rw [burnsideB46_w11_mem_ell, mem_gmapG, burnsideB46_w11_mem_ell]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨g2Act g⁻¹ w, ?_⟩
    simp only [burnsideB46_p5_T_apply, map_sub, conj_g2Act]
  · rintro ⟨w, hw⟩
    refine ⟨g2Act g w, ?_⟩
    have h1 := congrArg (g2Act g) hw
    simp only [burnsideB46_p5_T_apply, map_sub, g2Act_apply_inv] at h1
    have e : g2Act (g * γ * g⁻¹) (g2Act g w) = g2Act g (g2Act γ w) := by
      rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
    simp only [burnsideB46_p5_T_apply, e]
    exact h1

theorem burnsideB46_w11_ell_tL {s : K} (hs : s ≠ 0) : burnsideB46_w11_ell (tL s) = stdF K 2 := by
  ext y
  rw [burnsideB46_w11_mem_ell]
  constructor
  · rintro ⟨w, rfl⟩
    exact g2Act_tL_sub_mem s w
  · intro hy
    exact burnsideB46_p5_exists_tL_sub hs hy

theorem burnsideB46_w11_finrank_ell {γ : ↥(cayleyGroup K)} (hγ : burnsideB46_p5_IsLongEl γ) :
    Module.finrank K (burnsideB46_w11_ell γ) = 2 := by
  obtain ⟨g, rfl⟩ := hγ
  rw [burnsideB46_w11_ell_conj, burnsideB46_p3_finrank_gmapG,
    burnsideB46_w11_ell_tL (one_ne_zero (α := K)), burnsideB46_p4_finrank_stdF (by norm_num)]

theorem burnsideB46_w11_inv_apply {γ : ↥(cayleyGroup K)} (hγ : γ * γ = 1) (w : Ix3 → K) :
    g2Act γ (g2Act γ w) = w := by
  rw [← g2Act_mul_apply, hγ, map_one]
  rfl

theorem burnsideB46_w11_T_T {γ : ↥(cayleyGroup K)} (hγ : γ * γ = 1) (w : Ix3 → K) :
    burnsideB46_p5_T γ (burnsideB46_p5_T γ w) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext j
  simp only [burnsideB46_p5_T_apply, map_sub, burnsideB46_w11_inv_apply hγ, Pi.sub_apply,
    Pi.zero_apply]
  linear_combination (w j - g2Act γ w j) * h2

theorem burnsideB46_w11_polarQ_T {γ : ↥(cayleyGroup K)} (hγ : γ * γ = 1) (x y : Ix3 → K) :
    polarQ (burnsideB46_p5_T γ x) y = polarQ x (burnsideB46_p5_T γ y) := by
  simp only [burnsideB46_p5_T_apply, polarQ_sub_left, polarQ_sub_right]
  have h1 : polarQ (g2Act γ x) y = polarQ x (g2Act γ y) := by
    have := polarQ_g2Act γ x (g2Act γ y)
    rwa [burnsideB46_w11_inv_apply hγ] at this
  rw [h1]

theorem burnsideB46_w11_fix_of_ell {γ : ↥(cayleyGroup K)} (hγ : γ * γ = 1) {f : Ix3 → K}
    (h : ∀ y ∈ burnsideB46_w11_ell γ, polarQ y f = 0) : g2Act γ f = f := by
  have h1 : burnsideB46_p5_T γ f = 0 := eq_zero_of_polarQ fun z => by
    rw [polarQ_symm, ← burnsideB46_w11_polarQ_T hγ]
    exact h _ (burnsideB46_w11_mem_ell.2 ⟨z, rfl⟩)
  have h2 := h1
  rw [burnsideB46_p5_T_apply] at h2
  exact sub_eq_zero.mp h2

theorem burnsideB46_w11_B_nondeg : (burnsideB46_p5_B K).Nondegenerate :=
  ⟨fun x hx => eq_zero_of_polarQ hx, fun y hy => eq_zero_of_polarQ fun x => by
    rw [polarQ_symm]
    exact hy x⟩

theorem burnsideB46_w11_ti_finrank_le (U : Submodule K (Ix3 → K))
    (hU : ∀ x ∈ U, ∀ y ∈ U, polarQ x y = 0) : Module.finrank K U ≤ 3 := by
  have h1 : U ≤ LinearMap.BilinForm.orthogonal (burnsideB46_p5_B K) U := fun x hx y hy => hU y hy x hx
  have h2 := LinearMap.BilinForm.finrank_orthogonal (burnsideB46_w11_B_nondeg (K := K)) U
  have h3 := Submodule.finrank_mono h1
  have h6 : Module.finrank K (Ix3 → K) = 6 := by
    simp [Module.finrank_fintype_fun_eq_card]
  omega

theorem burnsideB46_w11_concur {a b : ↥(cayleyGroup K)} (ha : burnsideB46_p5_IsLongEl a)
    (hb : burnsideB46_p5_IsLongEl b) (hab : a * b = b * a) :
    burnsideB46_w11_ell a ⊓ burnsideB46_w11_ell b ≠ ⊥ := by
  intro hbot
  have ha2 := ha.mul_self
  have hb2 := hb.mul_self
  have hTT : ∀ w, burnsideB46_p5_T a (burnsideB46_p5_T b w) = 0 := by
    intro w
    have h1 : burnsideB46_p5_T a (burnsideB46_p5_T b w) ∈ burnsideB46_w11_ell a :=
      burnsideB46_w11_mem_ell.2 ⟨_, rfl⟩
    have h2 : burnsideB46_p5_T a (burnsideB46_p5_T b w) = burnsideB46_p5_T b (burnsideB46_p5_T a w) := by
      simp only [burnsideB46_p5_T_apply, map_sub]
      have e : g2Act a (g2Act b w) = g2Act b (g2Act a w) := by
        rw [← g2Act_mul_apply, ← g2Act_mul_apply, hab]
      rw [e]
      abel
    have h3 : burnsideB46_p5_T a (burnsideB46_p5_T b w) ∈ burnsideB46_w11_ell b := by
      rw [h2]
      exact burnsideB46_w11_mem_ell.2 ⟨_, rfl⟩
    have h4 : burnsideB46_p5_T a (burnsideB46_p5_T b w) ∈
        burnsideB46_w11_ell a ⊓ burnsideB46_w11_ell b := ⟨h1, h3⟩
    rw [hbot] at h4
    exact (Submodule.mem_bot K).1 h4
  have hti : ∀ x ∈ burnsideB46_w11_ell a ⊔ burnsideB46_w11_ell b,
      ∀ y ∈ burnsideB46_w11_ell a ⊔ burnsideB46_w11_ell b, polarQ x y = 0 := by
    intro x hx y hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨u₁, rfl⟩ := burnsideB46_w11_mem_ell.1 hx₁
    obtain ⟨u₂, rfl⟩ := burnsideB46_w11_mem_ell.1 hx₂
    obtain ⟨v₁, rfl⟩ := burnsideB46_w11_mem_ell.1 hy₁
    obtain ⟨v₂, rfl⟩ := burnsideB46_w11_mem_ell.1 hy₂
    have e11 : polarQ (burnsideB46_p5_T a u₁) (burnsideB46_p5_T a v₁) = 0 := by
      rw [burnsideB46_w11_polarQ_T ha2, burnsideB46_w11_T_T ha2]
      simp [polarQ]
    have e22 : polarQ (burnsideB46_p5_T b u₂) (burnsideB46_p5_T b v₂) = 0 := by
      rw [burnsideB46_w11_polarQ_T hb2, burnsideB46_w11_T_T hb2]
      simp [polarQ]
    have e12 : polarQ (burnsideB46_p5_T a u₁) (burnsideB46_p5_T b v₂) = 0 := by
      rw [burnsideB46_w11_polarQ_T ha2, hTT]
      simp [polarQ]
    have e21 : polarQ (burnsideB46_p5_T b u₂) (burnsideB46_p5_T a v₁) = 0 := by
      rw [polarQ_symm, burnsideB46_w11_polarQ_T ha2, hTT]
      simp [polarQ]
    rw [polarQ_add_left, polarQ_add_right, polarQ_add_right, e11, e22, e12, e21]
    simp
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (burnsideB46_w11_ell a)
    (burnsideB46_w11_ell b)
  rw [hbot, finrank_bot, burnsideB46_w11_finrank_ell ha, burnsideB46_w11_finrank_ell hb] at hfin
  have hle := burnsideB46_w11_ti_finrank_le _ hti
  omega

theorem burnsideB46_w11_tL_mem_Z1_std (s : K) : tL s ∈ Z1 K := by
  have h : tL s = g2A (uSL 0 s 0) := by
    unfold tL
    congr 1
    apply Subtype.ext
    rw [tv02_lit]
    rfl
  exact ⟨(0, s), h⟩

theorem burnsideB46_w11_exists_sl2E1 (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ s ∈ sl2E1 K, levi2Mat s = (M : Matrix (Fin 2) (Fin 2) K) := by
  have hM : M ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K)]
    exact Subgroup.mem_top M
  induction hM using Subgroup.closure_induction with
  | mem M hM =>
    obtain ⟨i, j, hij, t, rfl⟩ := hM
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · refine ⟨g2Y ![0, t, 0], Subgroup.subset_closure ⟨t, Or.inr rfl⟩, ?_⟩
      rw [levi2Mat_y1, CFSG.LinearGroups.coe_transvection]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    · refine ⟨g2X ![0, t, 0], Subgroup.subset_closure ⟨t, Or.inl rfl⟩, ?_⟩
      rw [levi2Mat_x1, CFSG.LinearGroups.coe_transvection]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    · exact absurd rfl hij
  | one =>
    exact ⟨1, Subgroup.one_mem _, by rw [levi2Mat_one]; rfl⟩
  | mul M N _ _ hM hN =>
    obtain ⟨s, hs, hsM⟩ := hM
    obtain ⟨t, ht, htN⟩ := hN
    refine ⟨s * t, Subgroup.mul_mem _ hs ht, ?_⟩
    rw [levi2Mat_mul (sl2E1_le_stabQ ht), hsM, htN]
    rfl
  | inv M _ hM =>
    obtain ⟨s, hs, hsM⟩ := hM
    have hsi : s⁻¹ ∈ sl2E1 K := Subgroup.inv_mem _ hs
    refine ⟨s⁻¹, hsi, ?_⟩
    have h1 := levi2Mat_mul (g := s) (sl2E1_le_stabQ hsi)
    rw [mul_inv_cancel, levi2Mat_one, hsM] at h1
    have h2 : (M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) * M = 1 := inv_mul_cancel M
    have h3 : (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        (M : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, h2]
      rfl
    calc levi2Mat s⁻¹ = (1 : Matrix (Fin 2) (Fin 2) K) * levi2Mat s⁻¹ := (one_mul _).symm
      _ = (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            (M : Matrix (Fin 2) (Fin 2) K)) * levi2Mat s⁻¹ := by rw [h3]
      _ = ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((M : Matrix (Fin 2) (Fin 2) K) * levi2Mat s⁻¹) := Matrix.mul_assoc _ _ _
      _ = ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [← h1, mul_one]

theorem burnsideB46_w11_exists_k {y : Ix3 → K} (hy : y ∈ stdF K 2)
    (hy0 : y ≠ 0) : ∃ k ∈ stabQ (stdF K 2), g2Act k (eu 0 (1 : K)) = y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hy' := burnsideB46_p4_F2_eq hy
  have haf : y (.inl 0) ≠ 0 ∨ y (.inr 2) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [hy', hcon.1, hcon.2]
    funext j
    rcases j with j | j <;> fin_cases j <;> rfl
  obtain ⟨M, hM0, hM1⟩ : ∃ M : Matrix.SpecialLinearGroup (Fin 2) K,
      (M : Matrix (Fin 2) (Fin 2) K) 0 0 = y (.inl 0) ∧
        (M : Matrix (Fin 2) (Fin 2) K) 1 0 = y (.inr 2) := by
    by_cases ha : y (.inl 0) = 0
    · have hf : y (.inr 2) ≠ 0 := haf.resolve_left (not_not.2 ha)
      refine ⟨⟨!![0, (y (.inr 2))⁻¹; y (.inr 2), 0], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        linear_combination (-1 : K) * inv_mul_cancel₀ hf + (-1 : K) * h2
      · simp [ha]
      · simp
    · refine ⟨⟨!![y (.inl 0), 0; y (.inr 2), (y (.inl 0))⁻¹], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        simp [ha]
      · simp
      · simp
  obtain ⟨k, hkE, hkM⟩ := burnsideB46_w11_exists_sl2E1 M
  refine ⟨k, sl2E1_le_stabQ hkE, ?_⟩
  rw [eu_eq_q6, burnsideB46_p5_act_F2 (sl2E1_le_stabQ hkE), hkM]
  conv_rhs => rw [hy']
  refine q6_congr ?_ rfl rfl rfl rfl ?_
  · rw [hM0]
    ring
  · rw [hM1]
    ring

theorem burnsideB46_w11_tL_mem_Z1 {y : Ix3 → K} (hy : y ∈ stdF K 2)
    (hy0 : y ≠ 0) (s : K) : tL s ∈ burnsideB46_Z1 K y := by
  obtain ⟨k, hk, rfl⟩ := burnsideB46_w11_exists_k hy hy0
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu, burnsideB46_p3_mem_map_conj]
  have h1 := burnsideB46_p5_conj_tL ((stabQ (stdF K 2)).inv_mem hk) s
  rw [inv_inv] at h1
  rw [h1]
  exact burnsideB46_w11_tL_mem_Z1_std _

theorem burnsideB46_w11_long_mem_Z1 {γ : ↥(cayleyGroup K)}
    (hγ : burnsideB46_p5_IsLongEl γ) {w : Ix3 → K} (hw0 : w ≠ 0)
    (hw : w ∈ burnsideB46_w11_ell γ) : γ ∈ burnsideB46_Z1 K w := by
  obtain ⟨g, rfl⟩ := hγ
  obtain ⟨y, rfl⟩ : ∃ y, w = g2Act g y := ⟨g2Act g⁻¹ w, (g2Act_apply_inv g w).symm⟩
  rw [burnsideB46_w11_ell_conj, burnsideB46_w11_ell_tL (one_ne_zero (α := K)), mem_gmapG,
    g2Act_inv_apply] at hw
  have hy0 : y ≠ 0 := fun h => hw0 (by rw [h, map_zero])
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_mem_map_conj]
  have e : g⁻¹ * (g * tL 1 * g⁻¹) * g = tL 1 := by group
  rw [e]
  exact burnsideB46_w11_tL_mem_Z1 hw hy0 1

theorem burnsideB46_w11_ell_le_F3 {w : Ix3 → K} (hw : w ≠ 0) {ζ : ↥(cayleyGroup K)}
    (hζ : ζ ∈ burnsideB46_Z1 K w) : burnsideB46_w11_ell ζ ≤ burnsideB46_F3 K w := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hw
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu] at hζ
  obtain ⟨z₀, hz₀, rfl⟩ := hζ
  have e : (MulAut.conj γ).toMonoidHom z₀ = γ * z₀ * γ⁻¹ := rfl
  rw [e, burnsideB46_w11_ell_conj, burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu]
  refine gmapG_mono ?_
  intro y hy
  obtain ⟨w', rfl⟩ := burnsideB46_w11_mem_ell.1 hy
  obtain ⟨v, rfl⟩ := hz₀
  rw [mem_stdF_three, burnsideB46_p5_T_apply, g2Act_g2A_uSL]
  simp [q6]

theorem burnsideB46_w11_F3_ti {w : Ix3 → K} (hw : w ≠ 0) {x y : Ix3 → K}
    (hx : x ∈ burnsideB46_F3 K w) (hy : y ∈ burnsideB46_F3 K w) : polarQ x y = 0 := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hw
  rw [burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu, mem_gmapG] at hx hy
  have h := polarQ_F3 hx hy
  rw [← polarQ_g2Act γ] at h
  rwa [g2Act_apply_inv, g2Act_apply_inv] at h

theorem burnsideB46_w11_long_of_ell_le {c : ↥(cayleyGroup K)} (hc : burnsideB46_p5_IsLongEl c)
    {w : Ix3 → K} (hw : w ≠ 0) (hle : burnsideB46_w11_ell c ≤ burnsideB46_F3 K w) :
    c ∈ burnsideB46_Z1 K w := by
  have hc2 := hc.mul_self
  have hA : c ∈ burnsideB46_A1 K w := fun f hf =>
    burnsideB46_w11_fix_of_ell hc2 fun y hy => burnsideB46_w11_F3_ti hw (hle hy) hf
  exact burnsideB46_w11_R1_mem_Z1 hw (burnsideB46_w11_A1_le_R1 hw hA) hc.qr_zero

theorem burnsideB46_w11_eu_ne_zero : (eu 0 (1 : K) : Ix3 → K) ≠ 0 := by
  rw [eu_eq_q6]
  intro h
  exact one_ne_zero (congrArg (fun w : Ix3 → K => w (.inl 0)) h)

theorem burnsideB46_w11_triangle {w : Ix3 → K} (hw0 : w ≠ 0)
    {a b c : ↥(cayleyGroup K)} (ha : burnsideB46_p5_IsLongEl a) (hb : burnsideB46_p5_IsLongEl b)
    (hc : burnsideB46_p5_IsLongEl c) (hwa : w ∈ burnsideB46_w11_ell a)
    (hwb : w ∈ burnsideB46_w11_ell b) (hba : burnsideB46_w11_ell b ≠ burnsideB46_w11_ell a)
    (hca : burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell a ≠ ⊥)
    (hcb : burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell b ≠ ⊥) : c ∈ burnsideB46_Z1 K w := by
  have hell : ∀ {c : ↥(cayleyGroup K)}, burnsideB46_p5_IsLongEl c →
      Module.finrank K (burnsideB46_w11_ell c) = 2 := fun hc => burnsideB46_w11_finrank_ell hc
  have haZ := burnsideB46_w11_long_mem_Z1 ha hw0 hwa
  have hbZ := burnsideB46_w11_long_mem_Z1 hb hw0 hwb
  have hwab : w ∈ burnsideB46_w11_ell a ⊓ burnsideB46_w11_ell b := ⟨hwa, hwb⟩
  have hF3d := burnsideB46_p3_F3_card (K := K) hw0
  have hinf_lt : burnsideB46_w11_ell a ⊓ burnsideB46_w11_ell b < burnsideB46_w11_ell a := by
    refine lt_of_le_of_ne inf_le_left fun h => hba ?_
    have hle : burnsideB46_w11_ell a ≤ burnsideB46_w11_ell b := h ▸ inf_le_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hell ha, hell hb])).symm
  have hinf_dim := Submodule.finrank_lt_finrank_of_lt hinf_lt
  rw [hell ha] at hinf_dim
  have hsupdim := Submodule.finrank_sup_add_finrank_inf_eq (burnsideB46_w11_ell a)
    (burnsideB46_w11_ell b)
  rw [hell ha, hell hb] at hsupdim
  have hF3 : burnsideB46_w11_ell a ⊔ burnsideB46_w11_ell b = burnsideB46_F3 K w :=
    Submodule.eq_of_le_of_finrank_le (sup_le (burnsideB46_w11_ell_le_F3 hw0 haZ)
      (burnsideB46_w11_ell_le_F3 hw0 hbZ)) (by omega)
  have hspan : Submodule.span K {w} = burnsideB46_w11_ell a ⊓ burnsideB46_w11_ell b :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem w _).2 hwab)
      (by rw [finrank_span_singleton hw0]; omega)
  by_cases hwc : w ∈ burnsideB46_w11_ell c
  · exact burnsideB46_w11_long_mem_Z1 hc hw0 hwc
  apply burnsideB46_w11_long_of_ell_le hc hw0
  rw [← hF3]
  have hdisj : Disjoint (burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell a)
      (burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell b) := by
    rw [Submodule.disjoint_def]
    intro u hu1 hu2
    by_contra hu0
    have huab : u ∈ burnsideB46_w11_ell a ⊓ burnsideB46_w11_ell b := ⟨hu1.2, hu2.2⟩
    rw [← hspan] at huab
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 huab
    have hμ : μ ≠ 0 := fun h => hu0 (by rw [h, zero_smul])
    apply hwc
    have h2 := Submodule.smul_mem _ μ⁻¹ hu1.1
    rwa [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h2
  have hXd := Submodule.one_le_finrank_iff.2 hca
  have hYd := Submodule.one_le_finrank_iff.2 hcb
  have hXY := Submodule.finrank_sup_add_finrank_inf_eq
    (burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell a) (burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell b)
  rw [hdisj.eq_bot, finrank_bot] at hXY
  have hsup_le : (burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell a) ⊔
      (burnsideB46_w11_ell c ⊓ burnsideB46_w11_ell b) ≤ burnsideB46_w11_ell c :=
    sup_le inf_le_left inf_le_left
  have hsup_eq := Submodule.eq_of_le_of_finrank_le hsup_le (by rw [hell hc]; omega)
  rw [← hsup_eq]
  exact sup_le_sup inf_le_right inf_le_right

theorem burnsideB46_w11_long_group {B : Subgroup ↥(cayleyGroup K)}
    (hB : ∀ b ∈ B, b ≠ 1 → burnsideB46_p5_IsLongEl b) :
    ∃ w : Ix3 → K, w ≠ 0 ∧ B ≤ burnsideB46_Z1 K w := by
  have hsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    by_cases h1 : b = 1
    · rw [h1, one_mul]
    · exact (hB b hb h1).mul_self
  have hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc => by
    have h1 := hsq (b * c) (B.mul_mem hb hc)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hsq c hc)
    have h2 : b * c = (b * c)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [mul_inv_rev, hb', hc'] at h2
    exact h2
  by_cases hbot : B = ⊥
  · exact ⟨eu 0 1, burnsideB46_w11_eu_ne_zero, by rw [hbot]; exact bot_le⟩
  obtain ⟨a, haB, ha1⟩ : ∃ a ∈ B, a ≠ 1 := by
    by_contra h
    push Not at h
    exact hbot ((Subgroup.eq_bot_iff_forall B).2 h)
  have ha := hB a haB ha1
  have hell_ne : ∀ {c : ↥(cayleyGroup K)}, burnsideB46_p5_IsLongEl c →
      burnsideB46_w11_ell c ≠ ⊥ := fun {c} hc h => by
    have := burnsideB46_w11_finrank_ell hc
    rw [h, finrank_bot] at this
    omega
  by_cases hsame : ∀ b ∈ B, b ≠ 1 → burnsideB46_w11_ell b = burnsideB46_w11_ell a
  · obtain ⟨w, hwa, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hell_ne ha)
    refine ⟨w, hw0, fun b hb => ?_⟩
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    · exact burnsideB46_w11_long_mem_Z1 (hB b hb hb1) hw0 (by rw [hsame b hb hb1]; exact hwa)
  push Not at hsame
  obtain ⟨b, hbB, hb1, hba⟩ := hsame
  have hbL := hB b hbB hb1
  have hne := burnsideB46_w11_concur ha hbL (hcomm a haB b hbB)
  obtain ⟨w, hwab, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨w, hw0, fun c hc => ?_⟩
  by_cases hc1 : c = 1
  · rw [hc1]
    exact Subgroup.one_mem _
  have hcL := hB c hc hc1
  refine burnsideB46_w11_triangle hw0 ha hbL hcL hwab.1 hwab.2 hba ?_ ?_
  · rw [inf_comm]
    exact burnsideB46_w11_concur ha hcL (hcomm a haB c hc)
  · rw [inf_comm]
    exact burnsideB46_w11_concur hbL hcL (hcomm b hbB c hc)

end W11a

section W11aV

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [Finite K] {V : Type} [CommGroup V] [Finite V] {n : ℕ}
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_w11_part_11_i_gen [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (hG : burnsideB46_w11_Good H)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁)
    {T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hcfg2 : B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂) {z : MulAut V} (hz : z ∈ Z₂) (hz1 : z ≠ 1) :
    ∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
      ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁ := by
  intro B _ hB
  obtain ⟨x, hx0, -, hP₁, -, hZ₁, -⟩ := burnsideB46_cfg1_point H hcfg
  obtain ⟨c, -, hZ, -⟩ := hG.cfg2 hx0 hP₁ hcfg2
  rw [hZ] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  obtain ⟨s, rfl⟩ := hz₀
  have hzs : (burnsideB46_p4_ofHyp H c).Φ (tL s) = burnsideB46_pi π (c * tL s * c⁻¹) := rfl
  have hs : s ≠ 0 := by
    rintro rfl
    apply hz1
    rw [hzs, burnsideB46_p5_tL_zero]
    simp
  have hBL : B ≤ L := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact L.one_mem
    · obtain ⟨l, hl, rfl⟩ := hB b hb hb1
      rw [hzs]
      exact L.mul_mem (L.mul_mem hl (burnsideB46_pi_mem_L H _)) (L.inv_mem hl)
  set B₀ : Subgroup ↥(cayleyGroup K) := B.comap (burnsideB46_pi π) with hB₀def
  have hBB₀ : B₀.map (burnsideB46_pi π) = B := burnsideB46_of_map_comap H hBL
  have hlong : ∀ γ ∈ B₀, γ ≠ 1 → burnsideB46_p5_IsLongEl γ := by
    intro γ hγ hγ1
    have hne : burnsideB46_pi π γ ≠ 1 := fun h =>
      hγ1 (burnsideB46_pi_injective H (by rw [h, map_one]))
    obtain ⟨l, hl, hbl⟩ := hB _ hγ hne
    obtain ⟨h, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    rw [hzs] at hbl
    have hγeq : γ = h * (c * tL s * c⁻¹) * h⁻¹ :=
      burnsideB46_pi_injective H (by rw [hbl]; simp only [map_mul, map_inv])
    exact burnsideB46_p5_isLongEl_iff.mpr ⟨h * c, s, hs, by rw [hγeq]; group⟩
  obtain ⟨w, hw0, hBw⟩ := burnsideB46_w11_long_group hlong
  obtain ⟨gw, hgw⟩ := exists_g2Act_eu_eq hw0
  obtain ⟨gx, hgx⟩ := exists_g2Act_eu_eq hx0
  have hkw : g2Act (gx * gw⁻¹) w = x := by
    rw [g2Act_mul_apply, ← hgw, g2Act_inv_apply, hgx]
  refine ⟨burnsideB46_pi π (gx * gw⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
  rw [← hBB₀, burnsideB46_of_map_conj, hZ₁, ← hkw, burnsideB46_p3_Z1_act]
  exact Subgroup.map_mono (Subgroup.map_mono hBw)

theorem burnsideB46_w11_part_11_i (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁)
    {T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hcfg2 : B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂) {z : MulAut V} (hz : z ∈ Z₂) (hz1 : z ≠ 1) :
    ∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
      ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁ := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_w11_part_11_i_gen H (burnsideB46_w11_good_ge2 hqs H hn) hcfg hcfg2 hz hz1

theorem burnsideB46_w11_part_11 (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) :=
  fun _ _ _ _ _ _ hcfg _ _ _ _ _ hcfg2 _ hz hz1 =>
    ⟨burnsideB46_w11_part_11_i hqs H hn hcfg hcfg2 hz hz1, burnsideB46_w11_strong hqs H hn hcfg⟩

end W11aV

section W11b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)


variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem burnsideB46_w11_Z1_std_mul_self {z : ↥(cayleyGroup K)} (hz : z ∈ Z1 K) : z * z = 1 := by
  obtain ⟨v, rfl⟩ := hz
  rw [← map_mul, uSL_mul]
  have h0 : uSL (v.1 + v.1) (v.2 + v.2 + v.1 * 0) (0 + 0) = (uSL (0 : K) 0 0 : SL3 K) := by
    simp [CharTwo.add_self_eq_zero]
  rw [h0, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]

theorem burnsideB46_w11_Z1_long {y : Ix3 → K} (hy : y ≠ 0) {ζ : ↥(cayleyGroup K)}
    (hζ : ζ ∈ burnsideB46_Z1 K y) (hζ1 : ζ ≠ 1) : burnsideB46_p5_IsLongEl ζ := by
  have h2 : ζ * ζ = 1 := by
    obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hy
    rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu] at hζ
    obtain ⟨z₀, hz₀, rfl⟩ := hζ
    have e : (MulAut.conj γ).toMonoidHom z₀ = γ * z₀ * γ⁻¹ := rfl
    rw [e]
    calc γ * z₀ * γ⁻¹ * (γ * z₀ * γ⁻¹) = γ * (z₀ * z₀) * γ⁻¹ := by group
      _ = 1 := by rw [burnsideB46_w11_Z1_std_mul_self hz₀]; group
  refine (burnsideB46_p5_invol_cases h2 hζ1).resolve_right fun hs => ?_
  obtain ⟨x, hx⟩ := burnsideB46_p5_IsShortEl.qr_ne hs
  exact hx (burnsideB46_w11_qr_Z1 hy hζ x)

theorem burnsideB46_w11_mem_ell_of_Z1 {y : Ix3 → K} (hy : y ≠ 0) {ζ : ↥(cayleyGroup K)}
    (hζ : ζ ∈ burnsideB46_Z1 K y) (hζ1 : ζ ≠ 1) : y ∈ burnsideB46_w11_ell ζ := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hy
  rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu] at hζ
  obtain ⟨z₀, hz₀, rfl⟩ := hζ
  have e : (MulAut.conj γ).toMonoidHom z₀ = γ * z₀ * γ⁻¹ := rfl
  rw [e, burnsideB46_w11_ell_conj, mem_gmapG, g2Act_inv_apply]
  obtain ⟨v, rfl⟩ := hz₀
  have hv : v ≠ 0 := by
    rintro rfl
    apply hζ1
    rw [e]
    change γ * g2A (uSL (0 : K × K).1 (0 : K × K).2 0) * γ⁻¹ = 1
    simp [CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero]
  rw [burnsideB46_w11_mem_ell]
  by_cases hp : v.1 = 0
  · have hq : v.2 ≠ 0 := fun h => hv (Prod.ext hp h)
    refine ⟨q6 0 0 (v.2)⁻¹ 0 0 0, ?_⟩
    rw [burnsideB46_p5_T_apply, g2Act_g2A_uSL, eu_eq_q6]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, hp, hq]
  · refine ⟨q6 0 (v.1)⁻¹ 0 0 0 0, ?_⟩
    rw [burnsideB46_p5_T_apply, g2Act_g2A_uSL, eu_eq_q6]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, hp]

theorem burnsideB46_w11_tL_eq (s : K) : tL s = g2A (uSL 0 s 0) := by
  unfold tL
  congr 1
  apply Subtype.ext
  rw [tv02_lit]
  rfl

theorem burnsideB46_w11_gmapG_inj {γ : ↥(cayleyGroup K)} {S S' : Submodule K (Ix3 → K)}
    (h : gmapG γ S = gmapG γ S') : S = S' := by
  ext x
  have h1 : g2Act γ x ∈ gmapG γ S ↔ g2Act γ x ∈ gmapG γ S' := by rw [h]
  rwa [mem_gmapG, mem_gmapG, g2Act_inv_apply] at h1

theorem burnsideB46_w11_ell_std_ne :
    burnsideB46_w11_ell (g2A (uSL (0 : K) 1 0)) ≠ burnsideB46_w11_ell (g2A (uSL (1 : K) 0 0)) := by
  have hF : burnsideB46_w11_ell (g2A (uSL (0 : K) 1 0)) = stdF K 2 := by
    rw [← burnsideB46_w11_tL_eq]
    exact burnsideB46_w11_ell_tL one_ne_zero
  have hv2 : (q6 (0 : K) 0 0 0 0 1) ∈ stdF K 2 := burnsideB46_p4_F2_of
  have hnot : (q6 (0 : K) 0 0 0 0 1) ∉ burnsideB46_w11_ell (g2A (uSL (1 : K) 0 0)) := by
    rw [burnsideB46_w11_mem_ell]
    rintro ⟨w, hw⟩
    have h1 := congrFun hw (.inr 2)
    rw [burnsideB46_p5_T_apply, g2Act_g2A_uSL] at h1
    simp [q6] at h1
  intro h
  rw [hF] at h
  exact hnot (h ▸ hv2)

theorem burnsideB46_w11_Z1_two_lines {y : Ix3 → K} (hy : y ≠ 0) :
    ∃ ζ₁ ∈ burnsideB46_Z1 K y, ∃ ζ₂ ∈ burnsideB46_Z1 K y, ζ₁ ≠ 1 ∧ ζ₂ ≠ 1 ∧
      burnsideB46_w11_ell ζ₂ ≠ burnsideB46_w11_ell ζ₁ := by
  obtain ⟨γ, rfl⟩ := exists_g2Act_eu_eq hy
  have hmem : ∀ p q' : K, γ * g2A (uSL p q' 0) * γ⁻¹ ∈
      burnsideB46_Z1 K (g2Act γ (eu 0 (1 : K))) := fun p q' => by
    rw [burnsideB46_p3_Z1_act, burnsideB46_p3_Z1_eu]
    exact ⟨g2A (uSL p q' 0), ⟨(p, q'), rfl⟩, rfl⟩
  have hne : ∀ p q' : K, (p ≠ 0 ∨ q' ≠ 0) → γ * g2A (uSL p q' 0) * γ⁻¹ ≠ 1 := fun p q' hv h => by
    have h1 : g2A (uSL p q' 0) = 1 := by
      calc g2A (uSL p q' 0) = γ⁻¹ * (γ * g2A (uSL p q' 0) * γ⁻¹) * γ := by group
        _ = 1 := by rw [h]; group
    have h2 : g2A (uSL p q' 0) = g2A (uSL (0 : K) 0 0) := by
      rw [h1, CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]
    have h3 := g2A_uSL_injective (v := (p, q')) (w := (0, 0)) h2
    rcases hv with hv | hv
    · exact hv (congrArg Prod.fst h3)
    · exact hv (congrArg Prod.snd h3)
  refine ⟨_, hmem 1 0, _, hmem 0 1, hne 1 0 (Or.inl one_ne_zero), hne 0 1 (Or.inr one_ne_zero), ?_⟩
  rw [burnsideB46_w11_ell_conj, burnsideB46_w11_ell_conj]
  intro h
  exact burnsideB46_w11_ell_std_ne (burnsideB46_w11_gmapG_inj h)

theorem burnsideB46_w11_F2_le_F3 {y : Ix3 → K} (hy : y ∈ stdF K 2)
    (hy0 : y ≠ 0) : stdF K 2 ≤ burnsideB46_F3 K y := by
  obtain ⟨k, hk, rfl⟩ := burnsideB46_w11_exists_k hy hy0
  rw [burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu]
  intro x hx
  rw [mem_gmapG]
  have hk' : k⁻¹ ∈ stabQ (stdF K 2) := (stabQ (stdF K 2)).inv_mem hk
  exact stdF_mono (by norm_num) (((mem_stabQ.1 hk') x).1 hx)

theorem burnsideB46_w11_A1_le_R2_of_F2_le {y : Ix3 → K} (h : stdF K 2 ≤ burnsideB46_F3 K y) :
    burnsideB46_A1 K y ≤ burnsideB46_p4_R2 K := fun γ hγ =>
  ⟨hγ _ (h (burnsideB46_p4_F2_of (a := 1) (f := 0))), hγ _ (h (burnsideB46_p4_F2_of (a := 0) (f := 1)))⟩

theorem burnsideB46_w11_A1_le_U0 {y : Ix3 → K} (hy0 : y ≠ 0)
    (hU : burnsideB46_A1 K y ≤ U0 K) : burnsideB46_A1 K y ≤ burnsideB46_p4_R2 K := by
  have hyF : y ∈ stdF K 2 := by
    by_contra hyF
    obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, hζ₁1, hζ₂1, hne⟩ := burnsideB46_w11_Z1_two_lines hy0
    have hl₁ := burnsideB46_w11_Z1_long hy0 hζ₁ hζ₁1
    have hl₂ := burnsideB46_w11_Z1_long hy0 hζ₂ hζ₂1
    have ha : burnsideB46_p5_IsLongEl (tL (1 : K)) := ⟨1, by group⟩
    have hcen : tL (1 : K) ∈ centerOf (U0 K) := by
      rw [burnsideB46_p4_center_U0]
      exact ⟨1, rfl⟩
    have hcomm : ∀ ζ ∈ burnsideB46_Z1 K y, tL (1 : K) * ζ = ζ * tL (1 : K) := fun ζ hζ => by
      have hζU : ζ ∈ U0 K := hU (fun w hw => mem_fixSub.1 hw ζ hζ)
      exact ((Subgroup.mem_centralizer_iff.1 hcen.2) ζ hζU).symm
    have hmem := burnsideB46_w11_triangle hy0 hl₁ hl₂ ha
      (burnsideB46_w11_mem_ell_of_Z1 hy0 hζ₁ hζ₁1) (burnsideB46_w11_mem_ell_of_Z1 hy0 hζ₂ hζ₂1)
      hne (burnsideB46_w11_concur ha hl₁ (hcomm ζ₁ hζ₁))
      (burnsideB46_w11_concur ha hl₂ (hcomm ζ₂ hζ₂))
    have h1 := burnsideB46_w11_mem_ell_of_Z1 hy0 hmem ha.ne_one
    rw [burnsideB46_w11_ell_tL (one_ne_zero (α := K))] at h1
    exact hyF h1
  exact burnsideB46_w11_A1_le_R2_of_F2_le (burnsideB46_w11_F2_le_F3 hyF hy0)

theorem burnsideB46_w11_A1_eu : burnsideB46_A1 K (eu 0 (1 : K)) = A1 K := by
  ext g
  change (∀ w ∈ burnsideB46_F3 K (eu 0 (1 : K)), g2Act g w = w) ↔ _
  rw [burnsideB46_p3_F3_eu]
  exact Iff.rfl

theorem burnsideB46_w11_inf_le_Z0 {g : ↥(cayleyGroup K)} (hg : g ∈ burnsideB46_A1 K (eu 0 1))
    (hg' : g ∈ burnsideB46_A1 K (g2Act (g2X ![0, 1, 0]) (eu 0 1))) :
    g ∈ burnsideB46_p4_Z0 K := by
  have hg1 : g ∈ A1 K := by rwa [burnsideB46_w11_A1_eu] at hg
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hg1
  have hmem : g2Act (g2X ![0, 1, 0]) (q6 0 0 0 0 1 0) ∈
      burnsideB46_F3 K (g2Act (g2X ![0, 1, 0]) (eu 0 1)) := by
    rw [burnsideB46_p3_F3_act, burnsideB46_p3_F3_eu, mem_gmapG, g2Act_inv_apply]
    exact mem_stdF_three.2 ⟨rfl, rfl, rfl⟩
  have h1 := hg' _ hmem
  rw [g2Act_x1q, g2Act_A1] at h1
  obtain ⟨e1, -, -, -, -, e6⟩ := q6_inj h1
  have hp : p = 0 := by linear_combination e1
  have hα : α = 0 := by linear_combination e6
  subst hp hα
  refine ⟨q', ?_⟩
  rw [burnsideB46_w11_tL_eq]
  exact burnsideB46_p3_kerElt_zero 0 q'

theorem burnsideB46_w11_A1_u0_le_R2 : burnsideB46_A1 K (eu 0 (1 : K)) ≤ burnsideB46_p4_R2 K :=
  burnsideB46_w11_A1_le_R2_of_F2_le (by
    rw [burnsideB46_p3_F3_eu]
    exact stdF_mono (by norm_num))

theorem burnsideB46_w11_y2_mem : g2Act (g2X ![0, 1, 0]) (eu 0 (1 : K)) ∈ stdF K 2 ∧
    g2Act (g2X ![0, 1, 0]) (eu 0 (1 : K)) ≠ 0 := by
  have hx₁mem : g2X ![0, 1, 0] ∈ stabQ (stdF K 2) :=
    sl2E1_le_stabQ (Subgroup.subset_closure ⟨1, Or.inl rfl⟩)
  refine ⟨(mem_stabQ.1 hx₁mem _).1 (by
      rw [eu_eq_q6]
      exact burnsideB46_p4_F2_of (a := 1) (f := 0)), fun h0 => ?_⟩
  have h1 := g2Act_inv_apply (g2X ![0, 1, 0]) (eu 0 (1 : K))
  rw [h0, map_zero] at h1
  exact burnsideB46_w11_eu_ne_zero h1.symm

theorem burnsideB46_w11_A1_y2_le_R2 :
    burnsideB46_A1 K (g2Act (g2X ![0, 1, 0]) (eu 0 (1 : K))) ≤ burnsideB46_p4_R2 K :=
  burnsideB46_w11_A1_le_R2_of_F2_le
    (burnsideB46_w11_F2_le_F3 burnsideB46_w11_y2_mem.1 burnsideB46_w11_y2_mem.2)

theorem burnsideB46_w11_R2_le_sup :
    burnsideB46_p4_R2 K ≤ burnsideB46_A1 K (eu 0 (1 : K)) ⊔
      burnsideB46_A1 K (g2Act (g2X ![0, 1, 0]) (eu 0 (1 : K))) := by
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  set x₁ : ↥(cayleyGroup K) := g2X ![0, 1, 0] with hx₁
  set A := burnsideB46_A1 K (eu 0 (1 : K)) with hA
  set A' := burnsideB46_A1 K (g2Act x₁ (eu 0 (1 : K))) with hA'
  have hAR : A ≤ burnsideB46_p4_R2 K := burnsideB46_w11_A1_u0_le_R2
  have hA'R : A' ≤ burnsideB46_p4_R2 K := burnsideB46_w11_A1_y2_le_R2
  have hJR : A ⊔ A' ≤ burnsideB46_p4_R2 K := sup_le hAR hA'R
  have hAJ : A ≤ A ⊔ A' := le_sup_left
  have hA'J : A' ≤ A ⊔ A' := le_sup_right
  have hcardA : Nat.card A = Nat.card K ^ 3 := by
    rw [hA, burnsideB46_w11_A1_eu]
    exact card_A1
  have hcardA' : Nat.card A' = Nat.card K ^ 3 := by
    rw [hA', burnsideB46_p3_A1_act, Subgroup.card_map_of_injective (MulAut.conj x₁).injective]
    exact hcardA
  have hinf : Nat.card ↥(A' ⊓ A) ≤ Nat.card K := by
    have hle : A' ⊓ A ≤ burnsideB46_p4_Z0 K := fun g hg => burnsideB46_w11_inf_le_Z0 hg.2 hg.1
    exact (Subgroup.card_le_of_le hle).trans (burnsideB46_p4_card_Z0 (K := K)).le
  haveI : A'.IsFiniteRelIndex (A ⊔ A') := Subgroup.isFiniteRelIndex_of_finiteIndex
  have h1 : A'.relIndex A ≤ A'.relIndex (A ⊔ A') :=
    Subgroup.relIndex_le_of_le_right hAJ Subgroup.relIndex_ne_zero
  have e1 : A'.relIndex A * Nat.card ↥(A' ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card A' A
  have e2 : A'.relIndex (A ⊔ A') * Nat.card ↥(A' ⊓ (A ⊔ A')) = Nat.card ↥(A ⊔ A') :=
    Subgroup.relIndex_mul_card A' (A ⊔ A')
  rw [inf_eq_left.2 hA'J] at e2
  have hq : 0 < Nat.card K := Nat.card_pos
  have h6 : Nat.card K ^ 5 * Nat.card K ≤ Nat.card ↥(A ⊔ A') * Nat.card K := by
    calc Nat.card K ^ 5 * Nat.card K = Nat.card A * Nat.card A' := by
          rw [hcardA, hcardA']
          ring
      _ = (A'.relIndex A * Nat.card ↥(A' ⊓ A)) * Nat.card A' := by rw [e1]
      _ ≤ (A'.relIndex (A ⊔ A') * Nat.card ↥(A' ⊓ A)) * Nat.card A' :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ = Nat.card ↥(A ⊔ A') * Nat.card ↥(A' ⊓ A) := by
          rw [← e2]
          ring
      _ ≤ Nat.card ↥(A ⊔ A') * Nat.card K := Nat.mul_le_mul_left _ hinf
  have key : Nat.card K ^ 5 ≤ Nat.card ↥(A ⊔ A') := Nat.le_of_mul_le_mul_right h6 hq
  have heq : A ⊔ A' = burnsideB46_p4_R2 K :=
    Subgroup.eq_of_le_of_card_ge hJR (by rw [burnsideB46_p4_card_R2]; exact key)
  exact heq.ge

end W11b

section W11c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [Finite K] {V : Type} [CommGroup V] [Finite V] {n : ℕ}
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_w11_ffJ_T_gen [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ)
    (hG : burnsideB46_w11_Good H)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁)
    (hoff : {A | IsFFStarOffender G A} =
      {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom})
    {T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hcfg2 : B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂) : ffJ T = R₂ := by
  obtain ⟨x, hx0, -, hP₁, -, -, hV₃⟩ := burnsideB46_cfg1_point H hcfg
  obtain ⟨c, hT, -, hR⟩ := hG.cfg2 hx0 hP₁ hcfg2
  have hA₁ : A₁ = (burnsideB46_A1 K x).map (burnsideB46_pi π) := hG.A1red hx0 hV₃ hcfg.2.2.2.2.2
  have hTG : T ≤ G := hcfg2.1.1
  have hΦ : ∀ γ, (burnsideB46_p4_ofHyp H c).Φ γ = burnsideB46_pi π (c * γ * c⁻¹) := fun γ => rfl
  have hinj := burnsideB46_pi_injective H
  unfold ffJ
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hAG : IsFFStarOffender G A := ⟨hA.1.trans hTG, hA.2⟩
    have hmem : A ∈ {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
      rw [← hoff]
      exact hAG
    obtain ⟨l, hl, hAl⟩ := hmem
    obtain ⟨h, rfl⟩ := (burnsideB46_mem_L' H).1 hl
    have hAeq : A = (burnsideB46_A1 K (g2Act h x)).map (burnsideB46_pi π) := by
      rw [hAl, hA₁, burnsideB46_of_map_conj, burnsideB46_p3_A1_act]
    have hAL : A ≤ L := by
      rw [hAeq]
      rintro _ ⟨γ, -, rfl⟩
      exact burnsideB46_pi_mem_L H γ
    have hAU : A ≤ (U0 K).map (burnsideB46_p4_ofHyp H c).Φ := by
      rw [← hT]
      exact le_inf hA.1 hAL
    have hy0 : g2Act c⁻¹ (g2Act h x) ≠ 0 := by
      intro h0
      apply hx0
      have h1 := g2Act_inv_apply h x
      have h2 := g2Act_apply_inv c (g2Act h x)
      rw [h0, map_zero] at h2
      rw [← h2, map_zero] at h1
      exact h1.symm
    have hle : burnsideB46_A1 K (g2Act c⁻¹ (g2Act h x)) ≤ U0 K := by
      rw [burnsideB46_p3_A1_act]
      rintro _ ⟨g, hg, rfl⟩
      have hpg : burnsideB46_pi π g ∈ A := by
        rw [hAeq]
        exact ⟨g, hg, rfl⟩
      obtain ⟨u, hu, hug⟩ := hAU hpg
      have hgu : g = c * u * c⁻¹ := hinj (by rw [← hug, hΦ])
      change c⁻¹ * g * c⁻¹⁻¹ ∈ U0 K
      rw [hgu, inv_inv]
      have e : c⁻¹ * (c * u * c⁻¹) * c = u := by group
      rw [e]
      exact hu
    have hR2 := burnsideB46_w11_A1_le_U0 hy0 hle
    have hA1y : burnsideB46_A1 K (g2Act h x) =
        (burnsideB46_A1 K (g2Act c⁻¹ (g2Act h x))).map (MulAut.conj c).toMonoidHom := by
      rw [← burnsideB46_p3_A1_act, g2Act_apply_inv]
    rw [hAeq, hR, hA1y, Subgroup.map_map]
    exact Subgroup.map_mono hR2
  · have hconj : ∀ y : Ix3 → K, y ≠ 0 →
        ∃ l ∈ L, (burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ =
          A₁.map (MulAut.conj l).toMonoidHom := by
      intro y hy
      have hcy : g2Act c y ≠ 0 := by
        intro h0
        apply hy
        have h1 := g2Act_inv_apply c y
        rw [h0, map_zero] at h1
        exact h1.symm
      obtain ⟨gc, hgc⟩ := exists_g2Act_eu_eq hcy
      obtain ⟨gx, hgx⟩ := exists_g2Act_eu_eq hx0
      have hkx : g2Act (gc * gx⁻¹) x = g2Act c y := by
        rw [g2Act_mul_apply, ← hgx, g2Act_inv_apply, hgc]
      refine ⟨burnsideB46_pi π (gc * gx⁻¹), burnsideB46_pi_mem_L H _, ?_⟩
      rw [hA₁, burnsideB46_of_map_conj]
      have e1 : (burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ =
          (burnsideB46_A1 K (g2Act c y)).map (burnsideB46_pi π) := by
        rw [burnsideB46_p3_A1_act, Subgroup.map_map]
        rfl
      rw [e1, ← hkx, burnsideB46_p3_A1_act]
    have hoffT : ∀ y : Ix3 → K, y ≠ 0 → burnsideB46_A1 K y ≤ burnsideB46_p4_R2 K →
        (burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ ≤ ⨆ (A : Subgroup (MulAut V))
          (_ : IsFFStarOffender T A), A := by
      intro y hy hyR
      obtain ⟨l, hl, hAl⟩ := hconj y hy
      have hAG : IsFFStarOffender G ((burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ) := by
        have h1 : (burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ ∈
            {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := ⟨l, hl, hAl⟩
        rw [← hoff] at h1
        exact h1
      have hAT : (burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ ≤ T := by
        have h1 : (burnsideB46_A1 K y).map (burnsideB46_p4_ofHyp H c).Φ ≤
            (U0 K).map (burnsideB46_p4_ofHyp H c).Φ :=
          Subgroup.map_mono (hyR.trans burnsideB46_p4_R2_le_U0)
        rw [← hT] at h1
        exact h1.trans inf_le_left
      exact le_iSup₂_of_le _ ⟨hAT, hAG.2⟩ le_rfl
    rw [hR]
    refine (Subgroup.map_mono burnsideB46_w11_R2_le_sup).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le (hoffT _ burnsideB46_w11_eu_ne_zero burnsideB46_w11_A1_u0_le_R2)
      (hoffT _ burnsideB46_w11_y2_mem.2 burnsideB46_w11_A1_y2_le_R2)

theorem burnsideB46_w11_ffJ_T (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n)
    {V₁ : Subgroup V} {P₁ R₁ Z₁ : Subgroup (MulAut V)} {V₃ : Subgroup V}
    {A₁ : Subgroup (MulAut V)} (hcfg : B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁)
    {T Z₂ P₂ R₂ : Subgroup (MulAut V)} {V₂ : Subgroup V}
    (hcfg2 : B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂) : ffJ T = R₂ := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_w11_ffJ_T_gen H (burnsideB46_w11_good_ge2 hqs H hn) hcfg
    (burnsideB46_w11_offenders hqs H hn hcfg) hcfg2

theorem burnsideB46_w11_part_13_bc (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        ffJ T = R₂ ∧ ffJ R₁ = A₁) :=
  fun _ _ _ _ _ _ hcfg _ _ _ _ _ hcfg2 =>
    ⟨burnsideB46_w11_ffJ_T hqs H hn hcfg hcfg2, burnsideB46_w11_ffJ_R1 hqs H hn hcfg⟩

theorem burnsideB46_w11_part_13 (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁) :=
  fun _ _ _ _ _ _ hcfg _ _ _ _ _ hcfg2 =>
    ⟨burnsideB46_w11_offenders hqs H hn hcfg, burnsideB46_w11_part_13_bc hqs H hn _ _ _ _ _ _ hcfg
      _ _ _ _ _ hcfg2⟩

end W11c

section W11n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [Finite K] {V : Type} [CommGroup V] [Finite V] {n : ℕ}
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_w11_good_of_GL [CharP K 2] (H : burnsideB46_Hyp V n K G L π θ) (hGL : G = L) :
    burnsideB46_w11_Good H where
  normal := fun g hg l hl => by
    rw [hGL] at hg
    exact L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg)
  conj_qr := fun {g} hg {γ γ'} h hq => by
    rw [hGL] at hg
    obtain ⟨δ, rfl⟩ := (burnsideB46_mem_L' H).1 hg
    have hγ' : γ' = δ * γ * δ⁻¹ :=
      burnsideB46_pi_injective H (by rw [h]; simp only [map_mul, map_inv])
    intro w
    have h1 := qr_conj δ γ (g2Act δ⁻¹ w)
    rw [g2Act_apply_inv] at h1
    rw [hγ', h1]
    exact hq _
  cfg2 := fun hx0 _ _ _ _ _ _ hP h => by
    have hnormLG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
      rw [hGL]
      exact Subgroup.le_normalizer
    obtain ⟨c, -, hT, hZ, -, hR, -⟩ := burnsideB46_p4_n1_cfg2 H hnormLG hx0 hP h
    exact ⟨c, hT, hZ, hR⟩
  A1red := fun hx0 _ _ hV hA => burnsideB46_of_cfg1_A1_of_le H hGL.le hV hA

theorem burnsideB46_w11_part_11_one (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1)
    (hGL : G = L) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have hG := burnsideB46_w11_good_of_GL H hGL
  exact fun _ _ _ _ _ _ hcfg _ _ _ _ _ hcfg2 _ hz hz1 =>
    ⟨burnsideB46_w11_part_11_i_gen H hG hcfg hcfg2 hz hz1, burnsideB46_w11_strong_gen H hG hcfg⟩

theorem burnsideB46_w11_part_13bc_one
    (H : burnsideB46_Hyp V n K G L π θ) (hn1 : n = 1)
    (hGL : G = L) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        ffJ T = R₂ ∧ ffJ R₁ = A₁) := by
  haveI : CharP K 2 := burnsideB46_charP H
  have hG := burnsideB46_w11_good_of_GL H hGL
  exact fun V₁ P₁ R₁ Z₁ V₃ A₁ hcfg _ _ _ _ _ hcfg2 =>
    ⟨burnsideB46_w11_ffJ_T_gen H hG hcfg (burnsideB46_part_13a_one H hn1 hGL V₁ P₁ R₁ Z₁ V₃ A₁ hcfg)
      hcfg2, burnsideB46_w11_ffJ_R1_gen H hG hcfg
      (burnsideB46_part_13a_one H hn1 hGL V₁ P₁ R₁ Z₁ V₃ A₁ hcfg)⟩

end W11n

section W14D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

open scoped commutatorElement Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_w14_levi1Mat_U0 {u : ↥(cayleyGroup K)} (hu : u ∈ U0 K) :
    levi1Mat u = !![1, 0; levi1Mat u 1 0, 1] := by
  obtain ⟨h00, h01, h11⟩ := levi1Mat_U0 hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h11]

theorem burnsideB46_w14_mem_normalizer_of_lower {x : ↥(cayleyGroup K)}
    (hxP : x ∈ stabQ (stdF K 1)) (hx3 : x ^ 3 = 1) (hlow : levi1Mat x 0 1 = 0) :
    x ∈ Subgroup.normalizer (U0 K : Set ↥(cayleyGroup K)) := by
  have hP : ∀ g ∈ U0 K, g ∈ stabQ (stdF K 1) := fun g hg => stabV0_le_stabQ (U0_le_stabV0 hg)
  have hxi : x⁻¹ ∈ stabQ (stdF K 1) := (stabQ (stdF K 1)).inv_mem hxP
  set y : Matrix (Fin 2) (Fin 2) K := levi1Mat x with hy
  have hdet : y.det ≠ 0 := by
    rw [hy, burnsideB46_p3_det_levi hxP]
    exact (burnsideB46_p3_act_eu hxP).2
  have hdet' : y.det = y 0 0 * y 1 1 := by
    rw [Matrix.det_fin_two, hlow, zero_mul, sub_zero]
  have hα : y 0 0 ≠ 0 := fun h => hdet (by rw [hdet', h, zero_mul])
  have hyYi : y * levi1Mat x⁻¹ = 1 := by
    rw [hy, ← burnsideB46_p3_levi1Mat_mul hxP hxi, mul_inv_cancel, levi1Mat_one]
  have hconj : ∀ g ∈ U0 K, x * g * x⁻¹ ∈ U0 K := by
    intro g hg
    set t : K := levi1Mat g 1 0 with ht
    have hg' : levi1Mat g = !![1, 0; t, 1] := burnsideB46_w14_levi1Mat_U0 hg
    set s : K := y 1 1 * (y 0 0)⁻¹ * t with hs
    have hu : g2A (uSL 0 0 s) ∈ U0 K := g2A_mem_U0 0 0 s
    have hg3 : x * g * x⁻¹ ∈ stabV0 K := burnsideB46_p3_conj_stabV0 hxP (U0_le_stabV0 hg)
    have hcomm : y * !![1, 0; t, 1] = !![1, 0; s, 1] * y := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hlow, hs] <;> field_simp <;> ring
    have hmat : levi1Mat (x * g * x⁻¹) = levi1Mat (g2A (uSL 0 0 s)) := by
      rw [burnsideB46_p3_levi1Mat_mul ((stabQ (stdF K 1)).mul_mem hxP (hP g hg)) hxi,
        burnsideB46_p3_levi1Mat_mul hxP (hP g hg), ← hy, hg', hcomm, Matrix.mul_assoc, hyYi,
        Matrix.mul_one, levi1Mat_uSL]
    have h1 := inv_mul_mem_U0_of_levi1Mat hg3 hu hmat
    have e : x * g * x⁻¹ = g2A (uSL 0 0 s) * ((g2A (uSL 0 0 s))⁻¹ * (x * g * x⁻¹)) := by group
    rw [e]
    exact (U0 K).mul_mem hu h1
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hconj h hh, fun hh => ?_⟩
  have h2 := hconj _ hh
  have h3' := hconj _ h2
  have hx3' : x * x * x = 1 := by simpa [pow_succ] using hx3
  have e : x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * h * (x * x * x)⁻¹ := by group
  rw [e, hx3', inv_one, one_mul, mul_one] at h3'
  exact h3'


theorem burnsideB46_w14_conj_torus [Finite K] (hK : Nat.card K = 2 ^ 2) {x : ↥(cayleyGroup K)}
    (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (U0 K : Set ↥(cayleyGroup K))) :
    ∃ u ∈ U0 K, ∃ s : Kˣ × Kˣ, x = u * g2T s * u⁻¹ := by
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  set U := U0 K with hU
  set Y : Subgroup ↥(cayleyGroup K) := U ⊔ Subgroup.zpowers x with hY
  have hUN : U ≤ Subgroup.normalizer (U : Set ↥(cayleyGroup K)) := Subgroup.le_normalizer
  have hUY : U ≤ Y := le_sup_left
  have hYN : Y ≤ Subgroup.normalizer (U : Set ↥(cayleyGroup K)) :=
    sup_le hUN ((Subgroup.zpowers_le).2 hxN)
  have hU2 : IsPGroup 2 U := isPGroup_U0
  have hodd : Odd (U.relIndex Y) := by
    have h1 := not_two_dvd_index_U0 hK (by norm_num : 1 ≤ 2)
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      h1 (h.trans (Subgroup.relIndex_dvd_index_of_le hUY)))
  have hzodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] <;> decide
  have hE₂P : U ⊓ Subgroup.zpowers x = ⊥ :=
    CFSG.Quasithin.H13.inf_eq_bot_of_odd_of_isPGroup hU2 hzodd
  have hTP : U ⊓ torusG K = ⊥ := U0_inf_eq_bot_of_odd (odd_card_torusG hK (by norm_num))
  have hE₁P : U ⊓ (Y ⊓ torusG K) = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    have : g ∈ U ⊓ torusG K := ⟨hg.1, hg.2.2⟩
    rwa [hTP] at this
  have hE₁s : U ⊔ (Y ⊓ torusG K) = Y := by
    refine le_antisymm (sup_le hUY inf_le_left) ?_
    have h1 : Y ≤ U ⊔ torusG K := by
      rw [← normalizer_U0_eq]
      exact hYN
    have h2 := CFSG.Quasithin.H13.inf_sup_le_sup_inf (P := U) (W := Y) (E := torusG K) hUY
      torusG_le_normalizer
    intro g hg
    exact h2 ⟨hg, h1 hg⟩
  obtain ⟨u, hu, hconj⟩ := CFSG.Quasithin.H13.exists_mem_conj_of_complements hUY hYN hU2 hodd
    (E₁ := Y ⊓ torusG K) (E₂ := Subgroup.zpowers x) inf_le_left hE₁P hE₁s le_sup_right hE₂P rfl
  have hxmem : x ∈ (Y ⊓ torusG K).map (MulAut.conj u).toMonoidHom := by
    rw [← hconj]
    exact Subgroup.mem_zpowers x
  obtain ⟨e, he, hex⟩ := hxmem
  obtain ⟨s, hs⟩ := he.2
  refine ⟨u, hu, s, ?_⟩
  rw [← hex, ← hs]
  simp [MulAut.conj_apply]


theorem burnsideB46_w14_conj_perfectCore {G : Type*} [Group G] {H : Subgroup G} {g y : G}
    (hg : g ∈ H) (hy : y ∈ perfectCore H) : g * y * g⁻¹ ∈ perfectCore H := by
  have hn : g ∈ Subgroup.normalizer (perfectCore H : Set G) :=
    normalizer_le_normalizer_perfectCore H (Subgroup.le_normalizer hg)
  exact (Subgroup.mem_normalizer_iff.mp hn y).mp hy

theorem burnsideB46_w14_scalar_conj {u y : ↥(cayleyGroup K)} (hu : u ∈ stabQ (stdF K 1))
    (hy : y ∈ stabQ (stdF K 1)) {a : K} (h : levi1Mat y = a • (1 : Matrix (Fin 2) (Fin 2) K)) :
    levi1Mat (u * y * u⁻¹) = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hui := (stabQ (stdF K 1)).inv_mem hu
  rw [burnsideB46_p3_levi1Mat_mul ((stabQ (stdF K 1)).mul_mem hu hy) hui,
    burnsideB46_p3_levi1Mat_mul hu hy, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← burnsideB46_p3_levi1Mat_mul hu hui, mul_inv_cancel, levi1Mat_one]

theorem burnsideB46_w14_units_pow_three [Finite K] (hK : Nat.card K = 4) (c : Kˣ) : c ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Kˣ) (x := c)
  rwa [Nat.card_units, hK] at h

theorem burnsideB46_w14_torus_scalar_iff [Finite K] (hK : Nat.card K = 4) (s : Kˣ × Kˣ) :
    (∃ a : K, levi1Mat (g2T s) = a • (1 : Matrix (Fin 2) (Fin 2) K)) ↔
      g2T s ∈ perfectCore (stabQ (stdF K 2)) := by
  constructor
  · rintro ⟨a, ha⟩
    rw [levi1Mat_g2T] at ha
    have h00 := congrFun (congrFun ha 0) 0
    have h11 := congrFun (congrFun ha 1) 1
    simp at h00 h11
    have h1 : (s.1 : K) = (s.2 : K)⁻¹ * (s.2 : K)⁻¹ := by
      have h2 : (s.2 : K) ≠ 0 := s.2.ne_zero
      field_simp
      have : (s.1 : K) * s.2 = (s.2 : K)⁻¹ := h11.trans h00.symm
      field_simp at this
      linear_combination this
    have hs : s = torHomC1 K s.2 := by
      refine Prod.ext (Units.ext ?_) rfl
      rw [torHomC1_apply]
      simpa using h1
    have hy' : g2T s ∈ torusG K ⊓ sectionCentralizer (stabV0 K) (pCoreOf 2 (stabV0 K)) := by
      rw [torusG_inf_sc1]
      exact ⟨s.2, by rw [MonoidHom.comp_apply, ← hs]⟩
    exact torusG_inf_sc1_le_gam2 hK hy'
  · intro hmem
    have hmem' : g2T s ∈ torusG K ⊓ perfectCore (stabQ (stdF K 2)) := ⟨⟨s, rfl⟩, hmem⟩
    rw [torusG_inf_gam2 (by omega)] at hmem'
    obtain ⟨c, hc⟩ := hmem'
    have hs : torHom2 K c = s := g2T_injective hc
    have hc3 : ((c : K)) ^ 3 = 1 := by
      have := congrArg Units.val (burnsideB46_w14_units_pow_three hK c)
      simpa using this
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have hcc : (c : K) * c = (c : K)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination hc3)
    have e1 : (((c⁻¹ * c⁻¹ : Kˣ) : K))⁻¹ = (c : K)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv, hcc]
    have e2 : (c : K) * ((c⁻¹ * c⁻¹ : Kˣ) : K) = (c : K)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    refine ⟨(c : K)⁻¹, ?_⟩
    rw [← hs, levi1Mat_g2T, torHom2_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, hcc]


theorem burnsideB46_w14_pCore_stabQ_one [Finite K] :
    pCoreOf 2 (stabQ (stdF K 1)) = pCoreOf 2 (stabV0 K) := by
  have h := burnsideB46_p3_R1_eu (K := K)
  rwa [burnsideB46_R1, burnsideB46_p3_P1_eu] at h

theorem burnsideB46_w14_K1 [Finite K] (hK : Nat.card K = 4) {x : ↥(cayleyGroup K)}
    (hxP : x ∈ stabQ (stdF K 1)) (hx3 : x ^ 3 = 1) (hx2 : x ∈ perfectCore (stabQ (stdF K 2))) :
    ∃ a : K, levi1Mat x = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hx2' : x ∈ stabQ (stdF K 2) := perfectCore_le _ hx2
  have hlow : levi1Mat x 0 1 = 0 := by
    rw [levi1Mat_01]
    have h := (mem_stabQ.mp hx2' (q6 0 0 0 0 0 1)).mp (mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩)
    exact (mem_stdF_two.mp h).2.2.2
  have hN := burnsideB46_w14_mem_normalizer_of_lower hxP hx3 hlow
  obtain ⟨u, hu, s, hxs⟩ := burnsideB46_w14_conj_torus (by rw [hK]; norm_num) hx3 hN
  have huP2 : u⁻¹ ∈ stabQ (stdF K 2) :=
    (stabQ (stdF K 2)).inv_mem (burnsideB46_p4_U0_le_stabQ_two hu)
  have huP1 : u ∈ stabQ (stdF K 1) := stabV0_le_stabQ (U0_le_stabV0 hu)
  have ht : g2T s ∈ perfectCore (stabQ (stdF K 2)) := by
    have e : g2T s = u⁻¹ * x * u⁻¹⁻¹ := by rw [hxs]; group
    rw [e]
    exact burnsideB46_w14_conj_perfectCore huP2 hx2
  obtain ⟨a, ha⟩ := (burnsideB46_w14_torus_scalar_iff hK s).2 ht
  refine ⟨a, ?_⟩
  rw [hxs]
  exact burnsideB46_w14_scalar_conj huP1 (g2T_mem_stabQ s 1) ha

theorem burnsideB46_w14_K4 [Finite K] (hK : Nat.card K = 4) {x : ↥(cayleyGroup K)}
    (hxP : x ∈ stabQ (stdF K 1)) (hx3 : x ^ 3 = 1) {a : K}
    (ha : levi1Mat x = a • (1 : Matrix (Fin 2) (Fin 2) K)) :
    x ∈ perfectCore (stabQ (stdF K 2)) := by
  have hlow : levi1Mat x 0 1 = 0 := by rw [ha]; simp
  have hN := burnsideB46_w14_mem_normalizer_of_lower hxP hx3 hlow
  obtain ⟨u, hu, s, hxs⟩ := burnsideB46_w14_conj_torus (by rw [hK]; norm_num) hx3 hN
  have huP2 : u ∈ stabQ (stdF K 2) := burnsideB46_p4_U0_le_stabQ_two hu
  have huP1 : u⁻¹ ∈ stabQ (stdF K 1) :=
    (stabQ (stdF K 1)).inv_mem (stabV0_le_stabQ (U0_le_stabV0 hu))
  have hts : levi1Mat (g2T s) = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e : g2T s = u⁻¹ * x * u⁻¹⁻¹ := by rw [hxs]; group
    rw [e]
    exact burnsideB46_w14_scalar_conj huP1 hxP ha
  have ht := (burnsideB46_w14_torus_scalar_iff hK s).1 ⟨a, hts⟩
  rw [hxs]
  exact burnsideB46_w14_conj_perfectCore huP2 ht

theorem burnsideB46_w14_K2 [Finite K] {x g : ↥(cayleyGroup K)} (hxP : x ∈ stabQ (stdF K 1))
    (hgP : g ∈ stabQ (stdF K 1)) {a : K}
    (ha : levi1Mat x = a • (1 : Matrix (Fin 2) (Fin 2) K)) :
    x * g * x⁻¹ * g⁻¹ ∈ pCoreOf 2 (stabQ (stdF K 1)) := by
  rw [burnsideB46_w14_pCore_stabQ_one, mem_pCoreOf_stabV0_iff]
  have hxi : x⁻¹ ∈ stabQ (stdF K 1) := (stabQ (stdF K 1)).inv_mem hxP
  have hgi : g⁻¹ ∈ stabQ (stdF K 1) := (stabQ (stdF K 1)).inv_mem hgP
  have hcomm : x * g * x⁻¹ * g⁻¹ = ⁅x, g⁆ := (commutatorElement_def x g).symm
  refine ⟨?_, ?_⟩
  · rw [hcomm]
    exact commutator_stabQ_one_le (Subgroup.commutator_mem_commutator hxP hgP)
  · have ha0 : a ≠ 0 := by
      intro h0
      have h1 := burnsideB46_p3_det_levi hxP
      rw [ha, h0, zero_smul] at h1
      simp at h1
      exact (burnsideB46_p3_act_eu hxP).2 h1.symm
    have hxi' : levi1Mat x⁻¹ = a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h1 := burnsideB46_p3_levi1Mat_mul hxP hxi
      rw [mul_inv_cancel, levi1Mat_one, ha, Matrix.smul_mul, Matrix.one_mul] at h1
      calc levi1Mat x⁻¹ = a⁻¹ • (a • levi1Mat x⁻¹) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
        _ = a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [h1]
    have hw := burnsideB46_w14_scalar_conj hgP hxi hxi'
    have hxw : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
    rw [hxw, burnsideB46_p3_levi1Mat_mul hxP ((stabQ (stdF K 1)).mul_mem
      ((stabQ (stdF K 1)).mul_mem hgP hxi) hgi), hw, ha, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ ha0, one_smul]


theorem burnsideB46_w14_K3 [Finite K] {x : ↥(cayleyGroup K)} (hxP : x ∈ stabQ (stdF K 1))
    (h : ∀ s ∈ stabV0 K, x * s * x⁻¹ * s⁻¹ ∈ pCoreOf 2 (stabQ (stdF K 1))) :
    ∃ a : K, levi1Mat x = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hcomm : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
      levi1Mat x * (M : Matrix (Fin 2) (Fin 2) K) = (M : Matrix (Fin 2) (Fin 2) K) * levi1Mat x := by
    intro M
    obtain ⟨q, rfl⟩ := levi1_surjective M
    have hs := q.2
    have h1 := h q.1 hs
    rw [burnsideB46_w14_pCore_stabQ_one, mem_pCoreOf_stabV0_iff] at h1
    have hsP : q.1 ∈ stabQ (stdF K 1) := stabV0_le_stabQ hs
    have hxi : x⁻¹ ∈ stabQ (stdF K 1) := (stabQ (stdF K 1)).inv_mem hxP
    have hsi : q.1⁻¹ ∈ stabQ (stdF K 1) := (stabQ (stdF K 1)).inv_mem hsP
    have hc : x * q.1 * x⁻¹ * q.1⁻¹ ∈ stabQ (stdF K 1) :=
      (stabQ (stdF K 1)).mul_mem ((stabQ (stdF K 1)).mul_mem
        ((stabQ (stdF K 1)).mul_mem hxP hsP) hxi) hsi
    have e : (x * q.1 * x⁻¹ * q.1⁻¹) * (q.1 * x) = x * q.1 := by group
    have hm := congrArg levi1Mat e
    rw [burnsideB46_p3_levi1Mat_mul hc ((stabQ (stdF K 1)).mul_mem hsP hxP), h1.2,
      burnsideB46_p3_levi1Mat_mul hsP hxP, burnsideB46_p3_levi1Mat_mul hxP hsP, one_mul] at hm
    rw [levi1_apply]
    exact hm.symm
  let E : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let F' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hE := hcomm E
  have hF := hcomm F'
  set y := levi1Mat x with hy
  have e1 := congrFun (congrFun hE 0) 0
  have e2 := congrFun (congrFun hE 0) 1
  have e3 := congrFun (congrFun hF 0) 0
  simp [E, F', Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have h10 : y 1 0 = 0 := e1
  have h00 : y 0 0 = y 1 1 := by linear_combination e2
  have h01 : y 0 1 = 0 := e3
  refine ⟨y 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, h00]

theorem burnsideB46_w14_core_alt [Finite K] (hK : Nat.card K = 4) {X : Subgroup ↥(cayleyGroup K)}
    (hX : Nat.card X = 3) (hXP : X ≤ stabQ (stdF K 1)) :
    X ≤ perfectCore (stabQ (stdF K 2)) ↔
      ⁅X, perfectCore (stabQ (stdF K 1))⁆ ≤ pCoreOf 2 (stabQ (stdF K 1)) := by
  have hx3 : ∀ x ∈ X, x ^ 3 = 1 := fun x hx => by
    have h := pow_card_eq_one' (G := ↥X) (x := ⟨x, hx⟩)
    rw [hX] at h
    exact congrArg Subtype.val h
  have h4 : 4 ≤ Nat.card K := hK ▸ le_rfl
  rw [perfectCore_stabQ_one h4]
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro x hx g hg
    obtain ⟨a, ha⟩ := burnsideB46_w14_K1 hK (hXP hx) (hx3 x hx) (h hx)
    exact burnsideB46_w14_K2 (hXP hx) (stabV0_le_stabQ hg) ha
  · intro h x hx
    obtain ⟨a, ha⟩ := burnsideB46_w14_K3 (hXP hx)
      (fun s hs => h (Subgroup.commutator_mem_commutator hx hs))
    exact burnsideB46_w14_K4 hK (hXP hx) (hx3 x hx) ha

end W14D

section W14

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise

section PartA

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_w14_mem_L_of_pow_three [CharP K 2] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : n = 2) {g : MulAut V} (hg : g ∈ G)
    (hg3 : g ^ 3 = 1) : g ∈ L := by
  have hn2 : 2 ≤ n := hn ▸ le_rfl
  obtain ⟨c, γ, σ, hc, hform⟩ := burnsideB46_G_semilinear hqs H hn2 hg
  have hrep : ∀ v, burnsideB46_f θ (g v) = semiMap c γ σ (burnsideB46_f θ v) := hform
  have hTTT : ∀ x, semiMap c γ σ (semiMap c γ σ (semiMap c γ σ x)) = x := by
    intro x
    obtain ⟨v, rfl⟩ := burnsideB46_f_surj H x
    rw [← hrep, ← hrep, ← hrep]
    have h1 : (g ^ 3) v = v := by rw [hg3]; rfl
    have h2 : g (g (g v)) = v := by simpa [pow_succ, MulAut.mul_apply] using h1
    rw [h2]
  have hσ3 : ∀ k, σ (σ (σ k)) = k := by
    intro k
    refine eq_of_semilinear (T := fun x => semiMap c γ σ (semiMap c γ σ (semiMap c γ σ x)))
      (x₀ := eu 0 1) (σ := fun k => σ (σ (σ k))) (σ' := fun k => k) ?_ (fun k x => ?_)
      (fun k x => ?_) k
    · rw [hTTT]
      intro h0
      have h1 := congrFun h0 (.inl 0)
      simp [eu] at h1
    · rw [semiMap_smul, semiMap_smul, semiMap_smul]
    · rw [hTTT, hTTT]
  have hcard : Nat.card (K ≃+* K) = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        (F := K) Nat.prime_two (by omega : 1 ≤ n) H.card
    rw [h, hn]
  have hσ2 : σ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := K ≃+* K) (x := σ)
    rwa [hcard] at this
  have hsq : ∀ a, σ (σ a) = a := fun a => by
    have := congrArg (fun e : K ≃+* K => e a) hσ2
    simpa [pow_two] using this
  have hσ : ∀ k, σ k = k := fun k => by
    have h1 : σ (σ (σ k)) = σ k := hsq (σ k)
    exact h1.symm.trans (hσ3 k)
  exact burnsideB46_as_mem_L_of_lin hqs H hn2 hg hc hrep hσ

theorem burnsideB46_w14_le_L [CharP K 2] (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : n = 2) {X : Subgroup (MulAut V)} (hXG : X ≤ G)
    (hX3 : Nat.card X = 3) : X ≤ L := by
  intro g hg
  refine burnsideB46_w14_mem_L_of_pow_three hqs H hn (hXG hg) ?_
  have h := pow_card_eq_one' (G := ↥X) (x := ⟨g, hg⟩)
  rw [hX3] at h
  exact congrArg Subtype.val h

end PartA

section Abstract

variable {M N : Type*} [Group M] [Group N]

theorem burnsideB46_w14_set_comm (Φ : M →* N) (hΦ : Function.Injective Φ) {X T L : Subgroup N}
    {U : Subgroup M} (hΦL : ∀ g, Φ g ∈ L) (hL : ∀ l ∈ L, ∃ g, Φ g = l) (hXL : X ≤ L)
    (hTL : T ⊓ L = U.map Φ) (hXT : (X : Set N) * (T : Set N) = (T : Set N) * (X : Set N)) :
    ((X.comap Φ : Subgroup M) : Set M) * (U : Set M) =
      (U : Set M) * ((X.comap Φ : Subgroup M) : Set M) := by
  have hUT : ∀ u ∈ U, Φ u ∈ T := fun u hu => ((hTL ▸ ⟨u, hu, rfl⟩ : Φ u ∈ T ⊓ L)).1
  have hTmem : ∀ t ∈ T, t ∈ L → ∃ u ∈ U, Φ u = t := fun t ht htL => by
    have : t ∈ U.map Φ := hTL ▸ ⟨ht, htL⟩
    obtain ⟨u, hu, rfl⟩ := this
    exact ⟨u, hu, rfl⟩
  have hXmem : ∀ x ∈ X, ∃ y ∈ (X.comap Φ : Subgroup M), Φ y = x := fun x hx => by
    obtain ⟨y, hy⟩ := hL x (hXL hx)
    exact ⟨y, by simpa [hy] using hx, hy⟩
  ext m
  constructor
  · rintro ⟨x₀, hx₀, u₀, hu₀, rfl⟩
    have hx₀X : Φ x₀ ∈ X := hx₀
    have h1 : Φ x₀ * Φ u₀ ∈ (T : Set N) * (X : Set N) := by
      rw [← hXT]
      exact ⟨Φ x₀, hx₀X, Φ u₀, hUT u₀ hu₀, rfl⟩
    obtain ⟨t, ht, x', hx', hxt⟩ := h1
    replace hxt : t * x' = Φ x₀ * Φ u₀ := hxt
    have htL : t ∈ L := by
      have : t = Φ (x₀ * u₀) * x'⁻¹ := by rw [map_mul]; exact eq_mul_inv_of_mul_eq hxt
      rw [this]
      exact L.mul_mem (hΦL _) (L.inv_mem (hXL hx'))
    obtain ⟨u', hu', hu't⟩ := hTmem t ht htL
    obtain ⟨y, hy, hyx⟩ := hXmem x' hx'
    refine ⟨u', hu', y, hy, hΦ ?_⟩
    rw [map_mul, map_mul, hu't, hyx, hxt]
  · rintro ⟨u₀, hu₀, x₀, hx₀, rfl⟩
    have hx₀X : Φ x₀ ∈ X := hx₀
    have h1 : Φ u₀ * Φ x₀ ∈ (X : Set N) * (T : Set N) := by
      rw [hXT]
      exact ⟨Φ u₀, hUT u₀ hu₀, Φ x₀, hx₀X, rfl⟩
    obtain ⟨x', hx', t, ht, hxt⟩ := h1
    replace hxt : x' * t = Φ u₀ * Φ x₀ := hxt
    have htL : t ∈ L := by
      have : t = x'⁻¹ * Φ (u₀ * x₀) := by rw [map_mul]; exact eq_inv_mul_of_mul_eq hxt
      rw [this]
      exact L.mul_mem (L.inv_mem (hXL hx')) (hΦL _)
    obtain ⟨u', hu', hu't⟩ := hTmem t ht htL
    obtain ⟨y, hy, hyx⟩ := hXmem x' hx'
    refine ⟨y, hy, u', hu', hΦ ?_⟩
    rw [map_mul, map_mul, hu't, hyx, hxt]

theorem burnsideB46_w14_relIndex_le {A B : Subgroup M} [Finite B]
    (h : (B : Set M) * (A : Set M) = (A : Set M) * (B : Set M)) :
    ∃ H : Subgroup M, A ≤ H ∧ B ≤ H ∧ A.relIndex H ≤ Nat.card B := by
  let H : Subgroup M :=
    { carrier := (B : Set M) * (A : Set M)
      one_mem' := ⟨1, B.one_mem, 1, A.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨b₁, hb₁, a₁, ha₁, rfl⟩ ⟨b₂, hb₂, a₂, ha₂, rfl⟩
        have h1 : a₁ * b₂ ∈ (B : Set M) * (A : Set M) := by
          rw [h]
          exact ⟨a₁, ha₁, b₂, hb₂, rfl⟩
        obtain ⟨b₃, hb₃, a₃, ha₃, h3⟩ := h1
        replace h3 : b₃ * a₃ = a₁ * b₂ := h3
        refine ⟨b₁ * b₃, B.mul_mem hb₁ hb₃, a₃ * a₂, A.mul_mem ha₃ ha₂, ?_⟩
        calc b₁ * b₃ * (a₃ * a₂) = b₁ * (b₃ * a₃) * a₂ := by group
          _ = b₁ * (a₁ * b₂) * a₂ := by rw [h3]
          _ = b₁ * a₁ * (b₂ * a₂) := by group
      inv_mem' := by
        rintro _ ⟨b, hb, a, ha, rfl⟩
        have h1 : a⁻¹ * b⁻¹ ∈ (B : Set M) * (A : Set M) := by
          rw [h]
          exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, rfl⟩
        simpa [mul_inv_rev] using h1 }
  have hAH : A ≤ H := fun a ha => ⟨1, B.one_mem, a, ha, one_mul a⟩
  have hBH : B ≤ H := fun b hb => ⟨b, hb, 1, A.one_mem, mul_one b⟩
  refine ⟨H, hAH, hBH, ?_⟩
  let f : B → H ⧸ A.subgroupOf H := fun b => QuotientGroup.mk ⟨b.1, hBH b.2⟩
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨_, b, hb, a, ha, rfl⟩, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk ⟨b, hBH hb⟩ : H ⧸ A.subgroupOf H) = _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using A.inv_mem (A.inv_mem ha)
  have := Nat.card_le_card_of_surjective f hf
  exact this

end Abstract


section Model

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB46_w14_fix_of_index_three [Finite K] (hK : 4 ≤ Nat.card K)
    {H : Subgroup ↥(cayleyGroup K)} (hU : U0 K ≤ H) (hidx : (U0 K).relIndex H ≤ 3) :
    H ≤ stabQ (stdF K 1) :=
  burnsideB46_w14b_le_P1 hK hU hidx

theorem burnsideB46_w14_model [Finite K] (hK : Nat.card K = 4) {X : Subgroup ↥(cayleyGroup K)}
    (hX3 : Nat.card X = 3)
    (hXU : (X : Set ↥(cayleyGroup K)) * (U0 K : Set ↥(cayleyGroup K)) =
      (U0 K : Set ↥(cayleyGroup K)) * (X : Set ↥(cayleyGroup K))) :
    X ≤ stabQ (stdF K 1) ⊓ perfectCore (stabQ (stdF K 2)) ↔
      ⁅X, perfectCore (stabQ (stdF K 1))⁆ ≤ pCoreOf 2 (stabQ (stdF K 1)) := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX3]; norm_num)
  obtain ⟨H, hUH, hXH, hidx⟩ := burnsideB46_w14_relIndex_le hXU
  have hXP : X ≤ stabQ (stdF K 1) :=
    hXH.trans (burnsideB46_w14_fix_of_index_three (by omega) hUH (hidx.trans (by rw [hX3])))
  rw [le_inf_iff]
  have h := burnsideB46_w14_core_alt hK hX3 hXP
  exact ⟨fun h' => h.1 h'.2, fun h' => ⟨hXP, h.2 h'⟩⟩

end Model

theorem burnsideB46_w14_perfectCore_map {M N : Type*} [Group M] [Group N] (φ : M →* N)
    (hφ : Function.Injective φ) (X : Subgroup M) :
    perfectCore (X.map φ) = (perfectCore X).map φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf φ hφ]
  congr 1
  funext n
  rw [map_derivedSeriesOf]

section VLevel

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_w14_part_14 (hqs : burnsideB46_G2Qs) (H : burnsideB46_Hyp V n K G L π θ)
    (hn : 2 ≤ n) :
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
        (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 →
        (X : Set (MulAut V)) * (T : Set (MulAut V)) = (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁)) := by
  intro hn2 V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2 X hXG hX3 hXT
  haveI := burnsideB46_charP H
  haveI : Finite (MulAut V) := Finite.of_injective (fun e : MulAut V => (e : V → V))
    (fun e e' h => MulEquiv.ext (congrFun h))
  haveI : Finite ↥(cayleyGroup K) := finite_cayleyGroup (F := K)
  have hK : Nat.card K = 4 := by rw [H.card, hn2]; norm_num
  obtain ⟨x, hx0, -, hP₁, -, -, -⟩ := burnsideB46_cfg1_point H hcfg1
  obtain ⟨c, hpt, hT, -, hP₂, -, -⟩ := burnsideB46_p4_cfg2 hqs H hn hx0 hP₁ hcfg2
  set Φ := (burnsideB46_p4_ofHyp H c).Φ with hΦ
  have hinj : Function.Injective Φ := (burnsideB46_p4_ofHyp H c).inj
  have hmemL : ∀ l, l ∈ L ↔ ∃ g, Φ g = l := (burnsideB46_p4_ofHyp H c).mem_L
  have hΦL : ∀ g, Φ g ∈ L := fun g => (hmemL _).2 ⟨g, rfl⟩
  have hP₁' : P₁ = (stabQ (stdF K 1)).map Φ := by
    rw [hP₁, burnsideB46_P1, hpt, burnsideB46_p3_stabQ_gmapG, Subgroup.map_map]
    rfl
  have hR₁' : R₁ = (pCoreOf 2 (stabQ (stdF K 1))).map Φ := by
    rw [hcfg1.2.2.1, hP₁', burnsideB46_pCoreOf_map Φ hinj]
  have hXL : X ≤ L := burnsideB46_w14_le_L hqs H hn2 hXG hX3
  have hXrange : X ≤ Φ.range := fun g hg => by
    obtain ⟨g', hg'⟩ := (hmemL g).1 (hXL hg)
    exact ⟨g', hg'⟩
  have hXX₀ : (X.comap Φ).map Φ = X := Subgroup.map_comap_eq_self hXrange
  have hX₀3 : Nat.card (X.comap Φ) = 3 := by
    have h1 : Nat.card ((X.comap Φ).map Φ) = Nat.card (X.comap Φ) :=
      Subgroup.card_map_of_injective hinj
    rw [hXX₀, hX3] at h1
    exact h1.symm
  have hset := burnsideB46_w14_set_comm Φ hinj (X := X) (T := T) (L := L) (U := U0 K) hΦL
    (fun l hl => (hmemL l).1 hl) hXL hT hXT
  have hmodel := burnsideB46_w14_model hK hX₀3 hset
  have hP₂' : perfectCore P₂ = (perfectCore (stabQ (stdF K 2))).map Φ := by
    rw [hP₂, burnsideB46_w14_perfectCore_map Φ hinj]
  have hP₁c : perfectCore P₁ = (perfectCore (stabQ (stdF K 1))).map Φ := by
    rw [hP₁', burnsideB46_w14_perfectCore_map Φ hinj]
  rw [hP₂', hP₁c, hR₁', hP₁', ← Subgroup.map_inf _ _ _ hinj, ← hXX₀, ← Subgroup.map_commutator,
    Subgroup.map_le_map_iff_of_injective hinj, Subgroup.map_le_map_iff_of_injective hinj]
  exact hmodel

end VLevel

end W14

section Fin2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

theorem burnsideB46_part_3_twisted_final (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧
        IsNatGL2QuotTw K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_part_3_twisted hqs H hn
    (fun x hx => burnsideB46_mp_hmax1 H.card H.one_le hx)

theorem burnsideB46_part_3_final (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) (h3 : ∀ w : K, w ^ 3 = 1 → w = 1) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2Quot K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_part_3 hqs H hn h3 (fun x hx => burnsideB46_mp_hmax1 H.card H.one_le hx)

theorem burnsideB46_part_13a_final (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
      (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_part_13a hqs H hn (fun x hx => burnsideB46_as_F3_ne_bot hx)
    (fun x hx => (burnsideB46_as_std hx).imp fun _ h => h.2)

theorem burnsideB46_part_4_final (hqs : burnsideB46_G2Qs)
    (H : burnsideB46_Hyp V n K G L π θ) (hn : 2 ≤ n) :
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) := by
  haveI : CharP K 2 := burnsideB46_charP H
  exact burnsideB46_part_4 hqs
    (burnsideB46_p4_hmax2_of_std H.card H.one_le (burnsideB46_wp2_isMax H.card H.one_le)) H hn

end Fin2

section Asm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

@[expose] def burnsideB46_B_4_6_tw_ge2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (n : ℕ), 2 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
  ∀ (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
    (θ : V →* Multiplicative (NatQ K)),
    Function.Injective π → π.range = L → L ≤ G →
    quasithinGenFitting G = layerOf L → commV (layerOf L) = ⊤ →
    Function.Surjective θ → θ.ker = fixV L →
    (∀ (γ : ↥(quasithinG2 K)) (v : V), θ ((π γ) v) = Multiplicative.ofAdd
      (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)))) →
    ((∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
        (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
          ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x)) ∧
      (∀ (c : K), ∀ l ∈ L, ∀ v w : V,
        θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
          θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v)))) ∧
      Nat.card V ≤ 2 ^ (7 * n) ∧
      (Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
        ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
          (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))))) ∧
    (∀ v w : V, θ v ≠ 1 → θ w ≠ 1 → ∃ l ∈ L, θ (l v) = θ w) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2QuotTw K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) ∧
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) ∧
    (∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L) ∧
    (1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R) ∧
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) ∧
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ → ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁) ∧
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 → (X : Set (MulAut V)) * (T : Set (MulAut V)) =
          (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁))

@[expose] def burnsideB46_Cl11 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G)
@[expose] def burnsideB46_Cl13bc (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
  (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        ffJ T = R₂ ∧ ffJ R₁ = A₁)

@[expose] def burnsideB46_Cl14 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 → (X : Set (MulAut V)) * (T : Set (MulAut V)) =
          (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁))
theorem burnsideB46_assembly_tw_ge2 (hqs : burnsideB46_G2Qs)
    (h11 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), 2 ≤ n →
        burnsideB46_Cl11 H)
    (h13 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), 2 ≤ n →
        burnsideB46_Cl13bc H)
    (h14 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), 2 ≤ n →
        burnsideB46_Cl14 H) :
    burnsideB46_B_4_6_tw_ge2 := by
  intro V _ _ hV2 n hn K _ _ hK G L π θ hπ hr hl hf hc hs hk he
  have H : burnsideB46_Hyp V n K G L π θ := ⟨hV2, by omega, hK, hπ, hr, hl, hf, hc, hs, hk, he⟩
  exact ⟨⟨burnsideB46_part_1a H, burnsideB46_part_1b H, burnsideB46_part_1c_ge2 H hn,
      burnsideB46_part_1d_ge2 H hn⟩, burnsideB46_part_2 H,
    burnsideB46_part_3_twisted_final hqs H hn, burnsideB46_part_4_final hqs H hn,
    burnsideB46_part_5 hqs H hn, burnsideB46_part_6 hqs H hn, burnsideB46_part_7_ge2 H hn,
    burnsideB46_part_8_ge2 H hn, burnsideB46_as_part_9 hqs H hn, burnsideB46_part_10 hqs H hn,
    h11 V n K G L π θ H hn, burnsideB46_as_part_12 hqs H hn,
    fun V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2 =>
      ⟨burnsideB46_part_13a_final hqs H hn V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1,
        (h13 V n K G L π θ H hn V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2)⟩,
    h14 V n K G L π θ H hn⟩

end Asm

section AsmOne

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

variable {V : Type} [CommGroup V] [Finite V] {n : ℕ} {K : Type} [Field K] [Finite K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}

@[expose] def burnsideB46_B_4_6_one : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (n : ℕ), n = 1 → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
  ∀ (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
    (θ : V →* Multiplicative (NatQ K)),
    Function.Injective π → π.range = L → L ≤ G →
    quasithinGenFitting G = layerOf L → commV (layerOf L) = ⊤ →
    Function.Surjective θ → θ.ker = fixV L →
    (∀ (γ : ↥(quasithinG2 K)) (v : V), θ ((π γ) v) = Multiplicative.ofAdd
      (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)))) →
    ((∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
        (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
          ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x)) ∧
      (∀ (c : K), ∀ l ∈ L, ∀ v w : V,
        θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
          θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v)))) ∧
      Nat.card V ≤ 2 ^ (7 * n) ∧
      (Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
        ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
          (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))))) ∧
    (∀ v w : V, θ v ≠ 1 → θ w ≠ 1 → ∃ l ∈ L, θ (l v) = θ w) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2Quot K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) ∧
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) ∧
    (∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L) ∧
    (1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R) ∧
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) ∧
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ → ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁) ∧
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 → (X : Set (MulAut V)) * (T : Set (MulAut V)) =
          (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁))

@[expose] def burnsideB46_Cl4 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂)))

@[expose] def burnsideB46_Cl5 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂))

@[expose] def burnsideB46_Cl6 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁)

@[expose] def burnsideB46_Cl9 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁)

@[expose] def burnsideB46_Cl10 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom))

@[expose] def burnsideB46_Cl13 (H : burnsideB46_Hyp V n K G L π θ) : Prop :=
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁)


theorem burnsideB46_assembly_one
    (hGL : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)), burnsideB46_Hyp V n K G L π θ → n = 1 → G = L)
    (h4 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl4 H)
    (h5 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl5 H)
    (h6 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl6 H)
    (h9 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl9 H)
    (h10 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl10 H)
    (h11 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl11 H)
    (h13 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), n = 1 → G = L →
        burnsideB46_Cl13 H) :
    burnsideB46_B_4_6_one := by
  intro V _ _ hV2 n hn1 K _ _ hK G L π θ hπ hr hl hf hc hs hk he
  have H : burnsideB46_Hyp V n K G L π θ := ⟨hV2, by omega, hK, hπ, hr, hl, hf, hc, hs, hk, he⟩
  have hG : G = L := hGL V n K G L π θ H hn1
  exact ⟨burnsideB46_part_1 H, burnsideB46_part_2 H, burnsideB46_part_3_one H hn1 hG,
    h4 V n K G L π θ H hn1 hG, h5 V n K G L π θ H hn1 hG, h6 V n K G L π θ H hn1 hG,
    burnsideB46_part_7 H, burnsideB46_part_8 H, h9 V n K G L π θ H hn1 hG,
    h10 V n K G L π θ H hn1 hG, h11 V n K G L π θ H hn1 hG,
    fun h => absurd hn1 (by omega), h13 V n K G L π θ H hn1 hG,
    fun h => absurd (hn1.symm.trans h) (by omega)⟩

end AsmOne

section Asm2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

theorem burnsideB46_tw_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {M : Type*} [Group M] {P R Y A : Subgroup M} (h : IsNatGL2Quot K P R Y A) :
    IsNatGL2QuotTw K P R Y A := by
  obtain ⟨h1, h2, h3, h4, hN, θ', ζ, hs, hk, ha⟩ := h
  refine ⟨h1, h2, h3, h4, hN, θ', ζ, hs, hk, fun p y y' hy => ?_⟩
  have hdet : ((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have hne : ((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
      (Matrix.GeneralLinearGroup.det (θ' (QuotientGroup.mk p))).ne_zero
    have hcard : ∀ a : K, a ≠ 0 → a = 1 := by
      intro a ha0
      have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
      haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
      have := Subsingleton.elim (Units.mk0 a ha0) 1
      simpa using congrArg Units.val this
    exact hcard _ hne
  rw [ha p y y' hy, hdet, one_smul]

theorem burnsideB46_corrected_of (hone : burnsideB46_B_4_6_one) (hge : burnsideB46_B_4_6_tw_ge2) :
    B_4_6 := by
  intro V _ _ hV2 n hn K _ _ hK G L π θ hπ hr hl hf hc hs hk he
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ :=
      hone V hV2 n hn1 K hK G L π θ hπ hr hl hf hc hs hk he
    refine ⟨c1, c2, ?_, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩
    intro V₁ P₁ R₁ Z₁ V₃ A₁ hcfg
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := c3 V₁ P₁ R₁ Z₁ V₃ A₁ hcfg
    exact ⟨a1, a2, burnsideB46_tw_of_card_two hK2 a3, a4, a5, a6, a7⟩
  · exact hge V hV2 n h2 K hK G L π θ hπ hr hl hf hc hs hk he

end Asm2

section Fin3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

theorem burnsideB46_corrected_modulo_14
    (hqs : burnsideB46_G2Qs)
    (h14 : ∀ (V : Type) [CommGroup V] [Finite V] (n : ℕ) (K : Type) [Field K] [Finite K]
      (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
      (θ : V →* Multiplicative (NatQ K)) (H : burnsideB46_Hyp V n K G L π θ), 2 ≤ n →
        burnsideB46_Cl14 H) :
    B_4_6 := by
  refine burnsideB46_corrected_of ?_ (burnsideB46_assembly_tw_ge2 hqs
    (fun V _ _ n K _ _ G L π θ H hn => burnsideB46_w11_part_11 hqs H hn)
    (fun V _ _ n K _ _ G L π θ H hn => burnsideB46_w11_part_13_bc hqs H hn) h14)
  refine burnsideB46_assembly_one (fun V _ _ n K _ _ G L π θ H hn1 => burnsideB46_w1g_G_eq_L H hn1)
    (fun V _ _ n K _ _ G L π θ H hn1 hG => burnsideB46_part_4_one H hn1 hG)
    (fun V _ _ n K _ _ G L π θ H hn1 hG => burnsideB46_part_5_one H hn1 hG)
    (fun V _ _ n K _ _ G L π θ H hn1 hG => burnsideB46_part_6_one H hn1 hG)
    (fun V _ _ n K _ _ G L π θ H hn1 hG => burnsideB46_as_part_9_one H hn1 hG)
    (fun V _ _ n K _ _ G L π θ H hn1 hG => burnsideB46_part_10_one H hn1 hG)
    (fun V _ _ n K _ _ G L π θ H hn1 hG => burnsideB46_w11_part_11_one H hn1 hG)
    (fun V _ _ n K _ _ G L π θ H hn1 hG V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2 =>
      ⟨burnsideB46_part_13a_one H hn1 hG V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1,
        burnsideB46_w11_part_13bc_one H hn1 hG V₁ P₁ R₁ Z₁ V₃ A₁ hcfg1 T Z₂ P₂ R₂ V₂ hcfg2⟩)

end Fin3

section Fin4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

end Fin4

section Target

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


theorem as_B_4_6 : B_4_6 := by
  exact burnsideB46_corrected_modulo_14 burnsideB46_G2Qs_of_cert
    (fun V _ _ n K _ _ G L π θ H hn => burnsideB46_w14_part_14 burnsideB46_G2Qs_of_cert H hn)

end Target

section Printed

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def burnsideB46_B_4_6_printed : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
  ∀ (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
    (θ : V →* Multiplicative (NatQ K)),
    Function.Injective π → π.range = L → L ≤ G →
    quasithinGenFitting G = layerOf L → commV (layerOf L) = ⊤ →
    Function.Surjective θ → θ.ker = fixV L →
    (∀ (γ : ↥(quasithinG2 K)) (v : V), θ ((π γ) v) = Multiplicative.ofAdd
      (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)))) →
    ((∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
        (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
          ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x)) ∧
      (∀ (c : K), ∀ l ∈ L, ∀ v w : V,
        θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
          θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v)))) ∧
      Nat.card V ≤ 2 ^ (7 * n) ∧
      (Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
        ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
          (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))))) ∧
    (∀ v w : V, θ v ≠ 1 → θ w ≠ 1 → ∃ l ∈ L, θ (l v) = θ w) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2Quot K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) ∧
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) ∧
    (∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L) ∧
    (1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R) ∧
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) ∧
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ → ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁) ∧
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 → (X : Set (MulAut V)) * (T : Set (MulAut V)) =
          (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁))

end Printed

section Neg

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] noncomputable def burnsideB46_neg_aut (g : ↥(cayleyGroup K)) : (Ix3 → K) ≃+ (Ix3 → K) where
  toFun := g2Act g
  invFun := g2Act g⁻¹
  left_inv := fun x => g2Act_inv_apply g x
  right_inv := fun x => g2Act_apply_inv g x
  map_add' := fun x y => map_add (g2Act g) x y

@[expose] noncomputable def burnsideB46_neg_pi :
    ↥(quasithinG2 K) →* MulAut (Multiplicative (Ix3 → K)) where
  toFun γ := (burnsideB46_neg_aut (burnsideB46_cg γ)).toMultiplicative
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    change Multiplicative.ofAdd (g2Act (burnsideB46_cg (1 : ↥(quasithinG2 K)))
      (Multiplicative.toAdd x)) = x
    rw [map_one, map_one]
    rfl
  map_mul' γ γ' := by
    refine MulEquiv.ext fun x => ?_
    change Multiplicative.ofAdd (g2Act (burnsideB46_cg (γ * γ')) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (g2Act (burnsideB46_cg γ) (Multiplicative.toAdd
        (Multiplicative.ofAdd (g2Act (burnsideB46_cg γ') (Multiplicative.toAdd x)))))
    rw [map_mul, g2Act_mul_apply]
    rfl

@[expose] noncomputable def burnsideB46_neg_theta :
    Multiplicative (Ix3 → K) →* Multiplicative (NatQ K) :=
  AddMonoidHom.toMultiplicative
    { toFun := burnsideB46_nat
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem burnsideB46_neg_exp2 (v : Multiplicative (Ix3 → K)) : v ^ 2 = 1 := by
  have h : Multiplicative.toAdd v + Multiplicative.toAdd v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero _
  rw [pow_two]
  exact congrArg Multiplicative.ofAdd h

theorem burnsideB46_neg_pi_injective : Function.Injective (burnsideB46_neg_pi (K := K)) := by
  intro γ γ' h
  have h1 : ∀ w, g2Act (burnsideB46_cg γ) w = g2Act (burnsideB46_cg γ') w := by
    intro w
    exact congrArg (fun f : MulAut (Multiplicative (Ix3 → K)) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd w))) h
  have h2 : (burnsideB46_cg γ)⁻¹ * burnsideB46_cg γ' = 1 := cayley_eq_one fun w => by
    rw [g2Act_mul_apply, ← h1, g2Act_inv_apply]
  exact burnsideB46_cg.injective (inv_mul_eq_one.mp h2)

noncomputable abbrev burnsideB46_neg_L : Subgroup (MulAut (Multiplicative (Ix3 → K))) :=
  (burnsideB46_neg_pi (K := K)).range

theorem burnsideB46_neg_pi_apply (γ : ↥(quasithinG2 K)) (v : Multiplicative (Ix3 → K)) :
    Multiplicative.toAdd ((burnsideB46_neg_pi γ) v) =
      g2Act (burnsideB46_cg γ) (Multiplicative.toAdd v) := rfl

theorem burnsideB46_neg_trans {a b : Ix3 → K} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ l ∈ burnsideB46_neg_L (K := K), Multiplicative.toAdd (l (Multiplicative.ofAdd a)) = b := by
  obtain ⟨g₁, hg₁⟩ := exists_g2Act_eu_eq ha
  obtain ⟨g₂, hg₂⟩ := exists_g2Act_eu_eq hb
  refine ⟨burnsideB46_neg_pi (burnsideB46_cg.symm (g₂ * g₁⁻¹)), ⟨_, rfl⟩, ?_⟩
  rw [burnsideB46_neg_pi_apply, MulEquiv.apply_symm_apply, g2Act_mul_apply]
  change g2Act g₂ (g2Act g₁⁻¹ a) = b
  rw [← hg₁, g2Act_inv_apply, hg₂]

theorem burnsideB46_neg_comm (hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    commV (burnsideB46_neg_L (K := K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  set b := Multiplicative.toAdd v with hb
  by_cases hb0 : b = 0
  · rw [toAdd_eq_zero.mp hb0]
    exact Subgroup.one_mem _
  · obtain ⟨c, hc0, hc1⟩ := hc
    have hu : (eu 0 1 : Ix3 → K) ≠ 0 := by
      rw [eu_eq_q6]
      intro h
      exact one_ne_zero (congrArg (fun w : Ix3 → K => w (.inl 0)) h)
    have hcu : c • (eu 0 1 : Ix3 → K) ≠ 0 := smul_ne_zero hc0 hu
    obtain ⟨a, ha0, hab⟩ : ∃ a : Ix3 → K, a ≠ 0 ∧ a + b ≠ 0 := by
      by_cases h1 : (eu 0 1 : Ix3 → K) + b = 0
      · refine ⟨c • eu 0 1, hcu, fun h2 => ?_⟩
        have : (eu 0 1 : Ix3 → K) = c • eu 0 1 := by
          have := h1.trans h2.symm
          exact add_right_cancel this
        have h3 : (c - 1) • (eu 0 1 : Ix3 → K) = 0 := by
          rw [sub_smul, one_smul, ← this, sub_self]
        exact hu ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc1))
      · exact ⟨eu 0 1, hu, h1⟩
    obtain ⟨l, hl, hla⟩ := burnsideB46_neg_trans ha0 hab
    refine Subgroup.subset_closure ⟨l, hl, Multiplicative.ofAdd a, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hla, toAdd_ofAdd, ← hb]
    abel

theorem burnsideB46_neg_qs (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) : CFSG.Open.IsQuasisimple ↥(burnsideB46_neg_L (K := K)) := by
  let e : ↥(quasithinG2 K) ≃* ↥(burnsideB46_neg_L (K := K)) :=
    MonoidHom.ofInjective burnsideB46_neg_pi_injective
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm (hqs K n hn hK)

theorem burnsideB46_neg_layer (hq : CFSG.Open.IsQuasisimple ↥(burnsideB46_neg_L (K := K))) :
    layerOf (burnsideB46_neg_L (K := K)) = burnsideB46_neg_L :=
  le_antisymm (burnsideB46_layerOf_le _) (le_sSup ⟨le_rfl, IsSubnormal.refl _, hq⟩)

theorem burnsideB46_neg_fstar (hq : CFSG.Open.IsQuasisimple ↥(burnsideB46_neg_L (K := K))) :
    quasithinGenFitting (burnsideB46_neg_L (K := K)) = layerOf (burnsideB46_neg_L (K := K)) :=
  (le_antisymm (CFSG.Quasithin.quasithinGenFitting_le _)
    (le_sup_of_le_right (le_sSup ⟨le_rfl, IsSubnormal.refl _, hq⟩))).trans
      (burnsideB46_neg_layer hq).symm

theorem burnsideB46_neg_theta_eq_one {v : Multiplicative (Ix3 → K)} :
    burnsideB46_neg_theta v = 1 ↔ v = 1 := by
  constructor
  · intro h
    have h1 : burnsideB46_nat (Multiplicative.toAdd v) = 0 := h
    have h2 := congrArg burnsideB46_ix h1
    rw [burnsideB46_ix_nat, burnsideB46_ix_zero] at h2
    exact toAdd_eq_zero.mp h2
  · intro h
    rw [h, map_one]

theorem burnsideB46_neg_ker (hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1) :
    (burnsideB46_neg_theta (K := K)).ker = fixV (burnsideB46_neg_L (K := K)) := by
  ext v
  rw [MonoidHom.mem_ker, mem_fixV, burnsideB46_neg_theta_eq_one]
  constructor
  · intro hv l _
    rw [hv, map_one]
  · intro h
    by_contra hv
    obtain ⟨c, hc0, hc1⟩ := hc
    have ha : Multiplicative.toAdd v ≠ 0 := fun h0 => hv (toAdd_eq_zero.mp h0)
    obtain ⟨l, hl, hla⟩ := burnsideB46_neg_trans (K := K) ha (smul_ne_zero hc0 ha)
    have h1 := h l hl
    rw [ofAdd_toAdd] at hla
    rw [h1] at hla
    have h2 : (c - 1) • Multiplicative.toAdd v = 0 := by
      rw [sub_smul, one_smul, ← hla, sub_self]
    exact ha ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc1))

theorem burnsideB46_neg_equiv (γ : ↥(quasithinG2 K)) (v : Multiplicative (Ix3 → K)) :
    burnsideB46_neg_theta ((burnsideB46_neg_pi γ) v) = Multiplicative.ofAdd
      (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd (burnsideB46_neg_theta v))) := by
  change Multiplicative.ofAdd (burnsideB46_nat (g2Act (burnsideB46_cg γ) (Multiplicative.toAdd v))) =
    Multiplicative.ofAdd (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (burnsideB46_nat (Multiplicative.toAdd v)))
  congr 1
  have h := burnsideB46_ix_qAct γ (burnsideB46_nat (Multiplicative.toAdd v))
  rw [burnsideB46_ix_nat] at h
  rw [← h, burnsideB46_nat_ix]

theorem burnsideB46_neg_Hyp (hqs : burnsideB46_G2Qs) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    burnsideB46_Hyp (Multiplicative (Ix3 → K)) n K (burnsideB46_neg_L (K := K))
      (burnsideB46_neg_L (K := K)) burnsideB46_neg_pi burnsideB46_neg_theta := by
  have hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := exists_ne_zero_ne_one (K := K)
    (by rw [hK]; calc 2 < 2 ^ 2 := by norm_num
                       _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hq := burnsideB46_neg_qs hqs hn hK
  refine ⟨burnsideB46_neg_exp2, by omega, hK, burnsideB46_neg_pi_injective, rfl, le_rfl,
    burnsideB46_neg_fstar hq, ?_, ?_, burnsideB46_neg_ker hc, burnsideB46_neg_equiv⟩
  · rw [burnsideB46_neg_layer hq]
    exact burnsideB46_neg_comm hc
  · intro y
    exact ⟨Multiplicative.ofAdd (burnsideB46_ix (Multiplicative.toAdd y)),
      congrArg Multiplicative.ofAdd (burnsideB46_nat_ix _)⟩

theorem burnsideB46_not_printed :
    ¬ burnsideB46_B_4_6_printed := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have hqs : burnsideB46_G2Qs := burnsideB46_G2Qs_of_cert
  have hH := burnsideB46_neg_Hyp (K := GaloisField 2 2) hqs (le_refl 2) hK
  obtain ⟨ω, h3, h1⟩ := burnsideB46_p3_exists_cube_root_of_even (K := GaloisField 2 2) hK
    (by decide : Even 2)
  obtain ⟨V₁, P₁, R₁, Z₁, V₃, A₁, hcfg, hneg⟩ :=
    burnsideB46_p3_not_isNatGL2Quot_Z1 hqs hH (le_refl 2) h3 h1
  have hB := h (Multiplicative (Ix3 → GaloisField 2 2)) burnsideB46_neg_exp2 2 (by norm_num)
    (GaloisField 2 2) hK _ _ _ _ hH.inj hH.range hH.le hH.fstar hH.comm hH.surj hH.ker hH.equiv
  exact hneg ((hB.2.2.1 V₁ P₁ R₁ Z₁ V₃ A₁ hcfg).2.2.1)

end Neg

end CFSG.ASVolI
