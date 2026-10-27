module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SL2Borel
public import CFSG.Quasithin.Vol2.Ch10SecDBasic
public import CFSG.Quasithin.Vol2.Ch6NatRho
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrthCoord
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative MatrixGroups Matrix
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL lower_left_eq_zero
  exists_conj_unip twist_conj twistTensor_faithful coe_inv_mul_SL coe_mul_inv_SL)

variable {G : Type} [Group G]

section Glue

theorem conjAct_mem_normalizer_autOn {K W : Subgroup G} (t : Subgroup.normalizer (W : Set G))
    (htK : (t : G) ∈ Subgroup.normalizer (K : Set G)) :
    conjAct W t ∈ Subgroup.normalizer (autOn K W : Set (MulAut ↥W)) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn t htK

theorem mem_of_conjAct_mem_autOn {L T W : Subgroup G}
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (c : Subgroup.normalizer (W : Set G))
    (hcLT : (c : G) ∈ L ⊔ T) (hc : conjAct W c ∈ autOn (T ⊓ L) W) : (c : G) ∈ T := by
  obtain ⟨p, hp, hpc⟩ := mem_autOn_iff.mp hc
  have hpT : (p : G) ∈ T := hp.1
  have hcent : ((p⁻¹ * c : Subgroup.normalizer (W : Set G)) : G) ∈
      Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) hpc
    simp only [conjAct_apply_coe] at h1
    have h2 : (c : G) * w = (p : G) * w * (p : G)⁻¹ * c := by
      rw [h1]
      group
    calc w * ((p⁻¹ * c : Subgroup.normalizer (W : Set G)) : G)
        = (p : G)⁻¹ * ((p : G) * w * (p : G)⁻¹ * c) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
      _ = ((p⁻¹ * c : Subgroup.normalizer (W : Set G)) : G) * w := by
          rw [← h2]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
  have hmem : ((p⁻¹ * c : Subgroup.normalizer (W : Set G)) : G) ∈ T := by
    refine hC (Subgroup.mem_inf.mpr ⟨?_, hcent⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem ((le_sup_right : T ≤ L ⊔ T) hpT)) hcLT
  have : (c : G) = (p : G) * ((p⁻¹ * c : Subgroup.normalizer (W : Set G)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this]
  exact mul_mem hpT hmem

theorem mem_normalizer_of_conj_mem [Finite G] {T : Subgroup G} {d : G}
    (h : ∀ t ∈ T, d * t * d⁻¹ ∈ T) : d ∈ Subgroup.normalizer (T : Set G) := by
  have hle : T.map (MulAut.conj d).toMonoidHom ≤ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  have heq : T.map (MulAut.conj d).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h t, fun ht => ?_⟩
  rw [← heq] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have hst' : (MulAut.conj d) s = (MulAut.conj d) t := hst
  rw [(MulAut.conj d).injective hst'] at hs
  exact hs

theorem inf_centralizer_ne_bot_of_two [Finite G] {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hB1 : B ≠ ⊥) :
    B ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := A ⊔ B with hX
  have hXp : IsPGroup 2 X := hA.to_sup_of_normal_right' hB hAB
  have hBX : B ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (B : Set G) := sup_le hAB Subgroup.le_normalizer
  have hBn : (B.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).mpr hXN
  have : Group.IsNilpotent X := hXp.isNilpotent
  have hB1' : B.subgroupOf X ≠ ⊥ := by
    intro h
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have : (⟨b, hBX hb⟩ : X) ∈ B.subgroupOf X := Subgroup.mem_subgroupOf.mpr hb
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hB1'
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  obtain ⟨hyB, hyZ⟩ := Subgroup.mem_inf.mp y.2
  intro h'
  apply hy1
  have hyZ' : (y : X) ∈ Subgroup.center X := hyZ
  have hmem : ((y : X) : G) ∈ B ⊓ Subgroup.centralizer (A : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hyB, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hyZ')
      ⟨a, (le_sup_left : A ≤ A ⊔ B) ha⟩)
  rw [h', Subgroup.mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

@[expose] noncomputable def autHom {L W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : ↥L →* ↥(autOn L W) where
  toFun ℓ := ⟨conjAct W ⟨ℓ, hLW ℓ.2⟩, mem_autOn_iff.mpr ⟨_, ℓ.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (conjAct W))
  map_mul' ℓ ℓ' := Subtype.ext (map_mul (conjAct W) ⟨ℓ, hLW ℓ.2⟩ ⟨ℓ', hLW ℓ'.2⟩)

theorem autHom_apply_coe {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (ℓ : ↥L) (w : ↥W) :
    ((((autHom hLW ℓ : ↥(autOn L W)) : MulAut ↥W) w : ↥W) : G) = (ℓ : G) * w * (ℓ : G)⁻¹ :=
  conjAct_apply_coe _ w

theorem mem_centralizer_of_autHom_eq_one {L W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) {ℓ : ↥L} (h : autHom hLW ℓ = 1) :
    (ℓ : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 := autHom_apply_coe hLW ℓ ⟨w, hw⟩
  rw [h] at h1
  have h2 : (w : G) = (ℓ : G) * w * (ℓ : G)⁻¹ := h1
  calc w * (ℓ : G) = ((ℓ : G) * w * (ℓ : G)⁻¹) * ℓ := by rw [← h2]
    _ = ℓ * w := by group

theorem mat2_ext {α : Type*} {A B : Matrix (Fin 2) (Fin 2) α} (h00 : A 0 0 = B 0 0)
    (h01 : A 0 1 = B 0 1) (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  rw [Matrix.eta_fin_two A, Matrix.eta_fin_two B, h00, h01, h10, h11]

theorem inv_mul_mem_centralizer {W : Subgroup G} {p c : Subgroup.normalizer (W : Set G)}
    (h : conjAct W p = conjAct W c) :
    ((p⁻¹ * c : Subgroup.normalizer (W : Set G)) : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) h
  simp only [conjAct_apply_coe] at h1
  have h2 : (c : G) * w = (p : G) * w * (p : G)⁻¹ * c := by
    rw [h1]
    group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc w * ((p : G)⁻¹ * c) = (p : G)⁻¹ * ((p : G) * w * (p : G)⁻¹ * c) := by group
    _ = (p : G)⁻¹ * c * w := by rw [← h2]; group

theorem mem_centralizer_iff_autOn {S W : Subgroup G} (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (w : ↥W) : (w : G) ∈ Subgroup.centralizer (S : Set G) ↔ ∀ x ∈ autOn S W, x w = w := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    obtain ⟨s, hs, rfl⟩ := mem_autOn_iff.mp hx
    apply Subtype.ext
    rw [conjAct_apply_coe, h s hs]
    group
  · intro h s hs
    have h1 := congrArg Subtype.val (h _ (mem_autOn_iff.mpr ⟨⟨s, hSW hs⟩, hs, rfl⟩))
    rw [conjAct_apply_coe] at h1
    have h1' : s * (w : G) * s⁻¹ = w := h1
    calc s * (w : G) = (s * w * s⁻¹) * s := by group
      _ = w * s := by rw [h1']

end Glue

section Induced

variable {F : Type} [Field F] {W : Type*} [Group W] {H P : Subgroup (MulAut W)}

theorem upper_of_mem_normalizer (ψ : ↥H ≃* SL(2, F))
    (hP : ∀ x : ↥H, (x : MulAut W) ∈ P ↔ ∃ b : F, ψ x = unipSL b) (x : ↥H)
    (hx : (x : MulAut W) ∈ Subgroup.normalizer (P : Set (MulAut W))) :
    (ψ x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  set u := ψ.symm (unipSL 1) with hu
  have huP : (u : MulAut W) ∈ P := (hP u).mpr ⟨1, by rw [hu, MulEquiv.apply_symm_apply]⟩
  have hxu : ((x * u * x⁻¹ : ↥H) : MulAut W) ∈ P := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp huP
  obtain ⟨b, hb⟩ := (hP _).mp hxu
  rw [map_mul, map_mul, map_inv, hu, MulEquiv.apply_symm_apply] at hb
  exact lower_left_eq_zero hb

theorem exists_upper_of_normalizes [Finite F] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (ψ : ↥H ≃* SL(2, F)) (hP : ∀ x : ↥H, (x : MulAut W) ∈ P ↔ ∃ b : F, ψ x = unipSL b)
    (τ : Subgroup.normalizer (H : Set (MulAut W)))
    (hτP : (τ : MulAut W) ∈ Subgroup.normalizer (P : Set (MulAut W))) :
    ∃ (h : SL(2, F)) (σ : RingAut F), (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (∀ y : ↥H, ψ (H.normalizerMonoidHom τ y) =
        h * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ y) * h⁻¹) ∧
      ∀ N : ℕ, τ ^ N = 1 → σ ^ N = 1 := by
  set α : MulAut SL(2, F) := MulAut.congr ψ (H.normalizerMonoidHom τ) with hαdef
  have hαy : ∀ y : ↥H, α (ψ y) = ψ (H.normalizerMonoidHom τ y) := fun y => by
    rw [hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hα : ∃ b : F, α (unipSL 1) = unipSL b := by
    set u := ψ.symm (unipSL 1) with hu
    have huP : (u : MulAut W) ∈ P := (hP u).mpr ⟨1, by rw [hu, MulEquiv.apply_symm_apply]⟩
    have h1 : ((H.normalizerMonoidHom τ u : ↥H) : MulAut W) ∈ P := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hτP _).mp huP
    obtain ⟨b, hb⟩ := (hP _).mp h1
    refine ⟨b, ?_⟩
    rw [show (unipSL 1 : SL(2, F)) = ψ u by rw [hu, MulEquiv.apply_symm_apply], hαy, hb]
  obtain ⟨h, σ, hh, hασ, hN⟩ := exists_upper_ringAut hn hcard α hα
  refine ⟨h, σ, hh, fun y => by rw [← hαy, hασ], fun N hτN => hN N ?_⟩
  rw [hαdef, ← map_pow, ← map_pow, hτN, map_one, map_one]

end Induced

section Orth

theorem IsOrthCh5.le_normalizer {L W : Subgroup G} {n : ℕ} (h : IsOrthCh5 L W n) :
    L ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨_, _, hLW, _⟩ := h
  exact hLW

theorem IsOrthCh5.exists_equiv {L W : Subgroup G} {m : ℕ} (h : IsOrthCh5 L W (2 * m)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * m) ∧
      ∃ (eρ : SL(2, F) ≃* ↥(autOn L W)) (E : ↥W ≃* ↥(hermSub m (Fin 2) F)),
        ∀ (γ : SL(2, F)) (w : ↥W),
          ((E (((eρ γ : ↥(autOn L W)) : MulAut ↥W) w) : ↥(hermSub m (Fin 2) F)) :
              Multiplicative (Matrix (Fin 2) (Fin 2) F)) =
            Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) F) *
              Multiplicative.toAdd ((E w : ↥(hermSub m (Fin 2) F)) :
                Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
              (frobPow m (γ : Matrix (Fin 2) (Fin 2) F))ᵀ) := by
  obtain ⟨m', hm', -, hc, K, _, _, _, hK, π, hR⟩ := h
  obtain rfl : m = m' := by omega
  have hπinj := FFModel.RealizesVia.injective_of_faithful (twistTensor_faithful (F := K) m) hR
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv
    (D := FFModel.twistTensor m (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) rfl hR
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
    (specialLinearGroupEquivStatedSL 2 K).trans (MulEquiv.ofBijective π ⟨hπinj, hR.1⟩), E,
    fun γ w => hE (specialLinearGroupEquivStatedSL 2 K γ) w⟩

variable {F : Type} [Field F] [CharP F 2]

theorem twist_inv_twist (m : ℕ) (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow m (g : Matrix (Fin 2) (Fin 2) F))ᵀ) *
        (frobPow m ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ = X := by
  calc _ = (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) * X *
        (frobPow m (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
          (g : Matrix (Fin 2) (Fin 2) F)))ᵀ := by
        rw [frobPow_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = X := by
        rw [coe_inv_mul_SL, frobPow_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem twist_twist_inv (m : ℕ) (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) *
        (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X *
          (frobPow m ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ) *
        (frobPow m (g : Matrix (Fin 2) (Fin 2) F))ᵀ = X := by
  have := twist_inv_twist m g⁻¹ X
  rwa [inv_inv] at this

theorem twist_herm [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ (2 * m))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : (frobPow m X)ᵀ = X) (g : Matrix (Fin 2) (Fin 2) F) :
    (frobPow m (g * X * (frobPow m g)ᵀ))ᵀ = g * X * (frobPow m g)ᵀ := by
  rw [frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow m hF, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hX, Matrix.mul_assoc]

theorem IsOrthCh5.exists_sylowCoord [Finite G] {L W S : Subgroup G} {m : ℕ}
    (h : IsOrthCh5 L W (2 * m)) (hS : IsSylowTwoOf S L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * m) ∧
      ∃ (ψ : ↥(autOn L W) ≃* SL(2, F)) (Y : ↥W →* Multiplicative (Matrix (Fin 2) (Fin 2) F)),
        Function.Injective Y ∧
        (∀ w, (frobPow m (Multiplicative.toAdd (Y w)))ᵀ = Multiplicative.toAdd (Y w)) ∧
        (∀ X : Matrix (Fin 2) (Fin 2) F, (frobPow m X)ᵀ = X →
          ∃ w, Multiplicative.toAdd (Y w) = X) ∧
        (∀ (x : ↥(autOn L W)) (w : ↥W), Multiplicative.toAdd (Y ((x : MulAut ↥W) w)) =
          (ψ x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (Y w) *
            (frobPow m (ψ x : Matrix (Fin 2) (Fin 2) F))ᵀ) ∧
        (∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn S W ↔ ∃ b : F, ψ x = unipSL b) := by
  have hLN : L ≤ Subgroup.normalizer (W : Set G) := h.le_normalizer
  obtain ⟨F, _, _, _, hF, eρ, E, hE⟩ := h.exists_equiv
  set P : Subgroup (MulAut ↥W) := autOn S W with hPdef
  have hP : IsSylowTwoOf P (autOn L W) := Vol2.Ch10.SecD.isSylowTwoOf_autOn hS hLN
  set P' : Subgroup SL(2, F) := (P.subgroupOf (autOn L W)).comap eρ.toMonoidHom with hP'def
  have hP'mem : ∀ γ, γ ∈ P' ↔ ((eρ γ : ↥(autOn L W)) : MulAut ↥W) ∈ P := fun γ => Iff.rfl
  have hP'2 : IsPGroup 2 P' :=
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).comap_of_injective
      eρ.toMonoidHom eρ.injective
  have hP'idx : ¬ 2 ∣ P'.index := by
    rw [hP'def, Subgroup.index_comap_of_surjective _ eρ.surjective]
    exact hP.2.2
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip hF hP'2 hP'idx
  let Y : ↥W →* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    { toFun := fun w => Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) F) *
        Multiplicative.toAdd ((E w : ↥(hermSub m (Fin 2) F)) :
          Multiplicative (Matrix (Fin 2) (Fin 2) F)) * (frobPow m (g : Matrix (Fin 2) (Fin 2) F))ᵀ)
      map_one' := by simp
      map_mul' := fun w w' => by
        rw [← ofAdd_add, map_mul E w w', Subgroup.coe_mul, toAdd_mul, Matrix.mul_add,
          Matrix.add_mul] }
  have hYv : ∀ w, Multiplicative.toAdd (Y w) = (g : Matrix (Fin 2) (Fin 2) F) *
      Multiplicative.toAdd ((E w : ↥(hermSub m (Fin 2) F)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) F)) * (frobPow m (g : Matrix (Fin 2) (Fin 2) F))ᵀ :=
    fun w => rfl
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, eρ.symm.trans (MulAut.conj g), Y,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro w w' hww'
    have h1 := congrArg Multiplicative.toAdd hww'
    rw [hYv, hYv] at h1
    have h2 := congrArg (fun X => ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X *
      (frobPow m ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ) h1
    simp only [twist_inv_twist] at h2
    exact E.injective (Subtype.ext (Multiplicative.toAdd.injective h2))
  ·
    intro w
    rw [hYv]
    exact twist_herm hF ((mem_hermSub m).mp (E w).2) _
  ·
    intro X hX
    set X' := ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X *
      (frobPow m ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ with hX'
    have hX'h : Multiplicative.ofAdd X' ∈ hermSub m (Fin 2) F :=
      (mem_hermSub m).mpr (twist_herm hF hX _)
    obtain ⟨w, hw⟩ := E.surjective ⟨Multiplicative.ofAdd X', hX'h⟩
    refine ⟨w, ?_⟩
    rw [hYv, hw]
    exact twist_twist_inv m g X
  ·
    intro x w
    have hx : x = eρ (eρ.symm x) := (eρ.apply_symm_apply x).symm
    have h1 := hE (eρ.symm x) w
    rw [← hx] at h1
    rw [hYv, hYv, h1, toAdd_ofAdd]
    have hU : ((g * eρ.symm x * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * ((eρ.symm x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
        coe_inv_mul_SL, Matrix.mul_one]
    have hψ : ((eρ.symm.trans (MulAut.conj g)) x : SL(2, F)) = g * eρ.symm x * g⁻¹ := rfl
    rw [hψ]
    exact (twist_conj m _ _ _ _ hU).symm
  ·
    intro x
    have hψ : ((eρ.symm.trans (MulAut.conj g)) x : SL(2, F)) = g * eρ.symm x * g⁻¹ := rfl
    rw [hψ]
    constructor
    · intro hxP
      have hmem : eρ.symm x ∈ P' := by
        rw [hP'mem, eρ.apply_symm_apply]
        exact hxP
      exact hgP _ hmem
    · rintro ⟨b, hb⟩
      have h1 : eρ.symm x = g⁻¹ * unipSL b * g := by
        rw [← hb]
        group
      have h2 := (hP'mem _).mp (hPg b)
      rw [← h1, eρ.apply_symm_apply] at h2
      exact h2

omit [CharP F 2] in
theorem twist_upper (a : ℕ) {ψ Y : Matrix (Fin 2) (Fin 2) F} (hψ : ψ 1 0 = 0)
    (h01 : Y 0 1 = 0) (h10 : Y 1 0 = 0) (h11 : Y 1 1 = 0) :
    (ψ * Y * (frobPow a ψ)ᵀ) 0 0 = ψ 0 0 * Y 0 0 * ψ 0 0 ^ 2 ^ a ∧
      (ψ * Y * (frobPow a ψ)ᵀ) 0 1 = 0 ∧ (ψ * Y * (frobPow a ψ)ᵀ) 1 0 = 0 ∧
        (ψ * Y * (frobPow a ψ)ᵀ) 1 1 = 0 := by
  have h0 : (0 : F) ^ 2 ^ a = 0 := zero_pow (by positivity)
  simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, Matrix.transpose_apply, h01, h10, h11, hψ,
    h0]

omit [CharP F 2] in
theorem twist_swap (a : ℕ) (k : F) :
    (!![0, 1; 1, 0] * !![k, 0; 0, 0] * (frobPow a !![(0 : F), 1; 1, 0])ᵀ) = !![0, 0; 0, k] := by
  have h0 : (0 : F) ^ 2 ^ a = 0 := zero_pow (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, Matrix.transpose_apply, h0]

omit [CharP F 2] in
theorem twist_lower (a : ℕ) (c : F) :
    (!![1, 0; c, 1] * !![(1 : F), 0; 0, 0] * (frobPow a !![(1 : F), 0; c, 1])ᵀ) =
      !![1, c ^ 2 ^ a; c, c * c ^ 2 ^ a] := by
  have h0 : (0 : F) ^ 2 ^ a = 0 := zero_pow (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, Matrix.transpose_apply, h0]

end Orth

section Nat

theorem IsNatModCh5.exists_sylowCoord [Finite G] {L W S : Subgroup G} {n : ℕ}
    (h : IsNatModCh5 L W n) (hS : IsSylowTwoOf S L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (ψ : ↥(autOn L W) ≃* SL(2, F)) (Y : ↥W ≃* Multiplicative (Fin 2 → F)),
        (∀ (x : ↥(autOn L W)) (w : ↥W), Multiplicative.toAdd (Y ((x : MulAut ↥W) w)) =
          (ψ x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y w))) ∧
        (∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn S W ↔ ∃ b : F, ψ x = unipSL b) := by
  have hLN : L ≤ Subgroup.normalizer (W : Set G) := h.1
  let D := h.data
  have : CharP D.K 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D.card
  set eρ : SL(2, D.K) ≃* ↥(autOn L W) :=
    (specialLinearGroupEquivStatedSL 2 D.K).trans
      (MulEquiv.ofBijective D.π ⟨D.π_injective, D.surj⟩) with heρ
  have hE : ∀ (γ : SL(2, D.K)) (w : ↥W), Multiplicative.toAdd
      (D.E (((eρ γ : ↥(autOn L W)) : MulAut ↥W) w)) =
        (γ : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd (D.E w)) :=
    fun γ w => D.inter (specialLinearGroupEquivStatedSL 2 D.K γ) w
  set P : Subgroup (MulAut ↥W) := autOn S W with hPdef
  have hP : IsSylowTwoOf P (autOn L W) := Vol2.Ch10.SecD.isSylowTwoOf_autOn hS hLN
  set P' : Subgroup SL(2, D.K) := (P.subgroupOf (autOn L W)).comap eρ.toMonoidHom with hP'def
  have hP'mem : ∀ γ, γ ∈ P' ↔ ((eρ γ : ↥(autOn L W)) : MulAut ↥W) ∈ P := fun γ => Iff.rfl
  have hP'2 : IsPGroup 2 P' :=
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).comap_of_injective
      eρ.toMonoidHom eρ.injective
  have hP'idx : ¬ 2 ∣ P'.index := by
    rw [hP'def, Subgroup.index_comap_of_surjective _ eρ.surjective]
    exact hP.2.2
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip D.card hP'2 hP'idx
  let M : Multiplicative (Fin 2 → D.K) ≃* Multiplicative (Fin 2 → D.K) :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : SL(2, D.K)) : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        simp only [toAdd_ofAdd, inv_mulVec_mulVec, ofAdd_toAdd]
      right_inv := fun v => by
        simp only [toAdd_ofAdd, mulVec_inv_mulVec, ofAdd_toAdd]
      map_mul' := fun v v' => by
        simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add] }
  have hMv : ∀ v, Multiplicative.toAdd (M v) =
      (g : Matrix (Fin 2) (Fin 2) D.K).mulVec (Multiplicative.toAdd v) := fun v => rfl
  refine ⟨D.K, inferInstance, inferInstance, inferInstance, D.card,
    eρ.symm.trans (MulAut.conj g), D.E.trans M, ?_, ?_⟩
  · intro x w
    have hx : x = eρ (eρ.symm x) := (eρ.apply_symm_apply x).symm
    have h1 := hE (eρ.symm x) w
    rw [← hx] at h1
    have hψ : ((eρ.symm.trans (MulAut.conj g)) x : SL(2, D.K)) = g * eρ.symm x * g⁻¹ := rfl
    rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, hMv, hMv, h1, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_assoc _ _ (g : Matrix (Fin 2) (Fin 2) D.K), coe_inv_mul_SL, Matrix.mul_one]
  · intro x
    have hψ : ((eρ.symm.trans (MulAut.conj g)) x : SL(2, D.K)) = g * eρ.symm x * g⁻¹ := rfl
    rw [hψ]
    constructor
    · intro hxP
      have hmem : eρ.symm x ∈ P' := by
        rw [hP'mem, eρ.apply_symm_apply]
        exact hxP
      exact hgP _ hmem
    · rintro ⟨b, hb⟩
      have h1 : eρ.symm x = g⁻¹ * unipSL b * g := by
        rw [← hb]
        group
      have h2 := (hP'mem _).mp (hPg b)
      rw [← h1, eρ.apply_symm_apply] at h2
      exact h2

end Nat

end CFSG.Quasithin.H13
