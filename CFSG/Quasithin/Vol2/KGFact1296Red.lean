module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.H13.KG1296

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped Pointwise

@[expose] noncomputable def descendO2 (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ CFSG.pCore 2 K) where
  toFun α := QuotientGroup.congr (CFSG.pCore 2 K) (CFSG.pCore 2 K) α
    (Subgroup.characteristic_iff_map_eq.1 inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {G : Type} [Group G]

@[expose] noncomputable def actBar (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (descendO2 ↥K).comp K.normalizerMonoidHom

theorem actBar_mk {K : Subgroup G} (x : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    actBar K x (k : ↥K ⧸ CFSG.pCore 2 ↥K) =
      ((⟨x * k * (x : G)⁻¹, (x.2 k).1 k.2⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) :=
  rfl

theorem mem_pCoreOf_iff {K : Subgroup G} (k : ↥K) :
    (k : G) ∈ pCoreOf 2 K ↔ k ∈ CFSG.pCore 2 ↥K := CFSG.mem_openPCoreOf_iff k

theorem actBar_of_mem {K : Subgroup G} (x : ↥(Subgroup.normalizer (K : Set G))) (hx : (x : G) ∈ K) :
    actBar K x = MulAut.conj ((⟨x, hx⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [actBar_mk, MulAut.conj_apply]
    rfl

theorem actBar_eq_one_iff {K : Subgroup G} (x : ↥(Subgroup.normalizer (K : Set G))) :
    actBar K x = 1 ↔ ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  constructor
  · intro h k hk
    have := congrArg (fun α : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => α (⟨k, hk⟩ : ↥K)) h
    simp only [actBar_mk, MulAut.one_apply] at this
    rw [QuotientGroup.eq, ← mem_pCoreOf_iff] at this
    have h2 := Subgroup.inv_mem _ this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h2
    have h3 := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).1 h2
    have e : k * (k⁻¹ * ((x : G) * k * (x : G)⁻¹)) * k⁻¹ =
        (x : G) * k * (x : G)⁻¹ * k⁻¹ := by group
    rwa [e] at h3
  · intro h
    ext y
    induction y using QuotientGroup.induction_on with
    | H k =>
      rw [actBar_mk, MulAut.one_apply, QuotientGroup.eq, ← mem_pCoreOf_iff]
      have h1 := h k k.2
      have h2 := Subgroup.inv_mem _ h1
      have h3 := (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (Subgroup.inv_mem _ k.2)) _).1 h2
      have e : ((⟨x * k * (x : G)⁻¹, (x.2 k).1 k.2⟩ : ↥K)⁻¹ * k : ↥K) =
          (k : G)⁻¹ * ((x : G) * k * (x : G)⁻¹ * k⁻¹)⁻¹ * (k : G)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact h3

theorem mem_centralizerMod_iff {X K : Subgroup G} (hXN : X ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ X) :
    x ∈ centralizerMod (pCoreOf 2 K) X K ↔ actBar K ⟨x, hXN hx⟩ = 1 := by
  rw [actBar_eq_one_iff]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨hx, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hXN hx), h⟩

theorem le_normalizer_of_forall {M : Type*} [Group M] {A H : Subgroup M}
    (h : ∀ a ∈ A, ∀ y ∈ H, a * y * a⁻¹ ∈ H) : A ≤ Subgroup.normalizer (H : Set M) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h a ha y hy, fun hy => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hy
  rwa [show a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y by group] at this

@[expose] noncomputable def barOf (K B : Subgroup G) : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

@[expose] def InnClosed {M : Type*} [Group M] (B : Subgroup M) : Prop :=
  ∀ α : MulAut M, (∀ x ∈ B, α x ∈ B) → (∀ x ∈ B, α x * x⁻¹ ∈ pCoreOf 2 B) →
    ∃ β ∈ B, α = MulAut.conj β

@[expose] def ParConclusion {M : Type*} [Group M] (B : Subgroup M) (m : ℕ) : Prop :=
  ∀ Q : Subgroup M, Q ≤ pCoreOf 2 B → Q ≠ pCoreOf 2 B → Q ≠ ⊥ →
    B ≤ Subgroup.normalizer (Q : Set M) → Nat.card ↥(pCoreOf 2 B) ≤ 2 ^ m * Nat.card Q →
      ∃ P : Subgroup M, B ≤ P ∧ P ≤ Subgroup.normalizer (Q : Set M) ∧
        ¬ P ≤ Subgroup.normalizer (B : Set M)

structure Hyp1296 (X K S B Q : Subgroup G) (m : ℕ) : Prop where
  hKX : K ≤ X
  hXN : X ≤ Subgroup.normalizer (K : Set G)
  hS : QuasithinUnique.IsSylowTwoOf S X
  hKS : K ⊔ S = X
  hBK : B ≤ K
  hSB : S ≤ Subgroup.normalizer (B : Set G)
  hinn : ∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B
  hcard : Nat.card ↥(pCoreOf 2 (B ⊔ S)) ≤ 2 ^ m * Nat.card Q
  hQlt : Q < pCoreOf 2 (B ⊔ S)
  hQN : B ⊔ S ≤ Subgroup.normalizer (Q : Set G)
  hD : centralizerMod (pCoreOf 2 K) X K ≤ Q
  hXQ : ¬ X ≤ Subgroup.normalizer (Q : Set G)

theorem reduction [Finite G] {X K S B Q : Subgroup G} {m : ℕ} (h : Hyp1296 X K S B Q m)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hInn : InnClosed (barOf K B))
    (hPar : ParConclusion (barOf K B) m) :
    ∃ P : Subgroup G, S ≤ P ∧ P ≤ X ∧ P ≤ Subgroup.normalizer (Q : Set G) ∧
      ¬ P ≤ Subgroup.normalizer (B : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := centralizerMod (pCoreOf 2 K) X K with hDdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set Bb := barOf K B with hBb
  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (actBar K).comp (Subgroup.inclusion h.hXN)
    with hφdef
  have hmemD : ∀ x (hx : x ∈ X), x ∈ D ↔ φ ⟨x, hx⟩ = 1 := fun x hx =>
    mem_centralizerMod_iff h.hXN hx
  have hDX : D ≤ X := fun x hx => hx.1
  have hφK : ∀ k (hk : k ∈ K), φ ⟨k, h.hKX hk⟩ = MulAut.conj (π ⟨k, hk⟩) := fun k hk =>
    actBar_of_mem _ hk
  have hconj : Function.Injective
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw := congrArg (fun f : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => f w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at hw
      calc w * z = (z * w * z⁻¹) * z := by rw [hw]
        _ = z * w := by group
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    refine le_normalizer_of_forall fun x hx d hd => ?_
    have hdX := hDX hd
    have hxd : x * d * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hx hdX) (X.inv_mem hx)
    rw [hmemD _ hxd]
    have e : (⟨x * d * x⁻¹, hxd⟩ : ↥X) = ⟨x, hx⟩ * ⟨d, hdX⟩ * (⟨x, hx⟩ : ↥X)⁻¹ := rfl
    rw [e, map_mul, map_mul, (hmemD d hdX).1 hd, mul_one, map_inv, mul_inv_cancel]
  set R := pCoreOf 2 (B ⊔ S) with hR
  have hQR : Q ≤ R := h.hQlt.le
  have hRBS : R ≤ B ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hDR : D ≤ R := h.hD.trans hQR
  have hSBD : S ≤ B ⊔ D := by
    intro s hs
    obtain ⟨b, hb, hc⟩ := h.hinn s hs
    have hsX : s ∈ X := h.hKS ▸ Subgroup.mem_sup_right hs
    have hbK : b ∈ K := h.hBK hb
    have hbX : b ∈ X := h.hKX hbK
    have hcX : b⁻¹ * s ∈ X := X.mul_mem (X.inv_mem hbX) hsX
    have hcN : b⁻¹ * s ∈ Subgroup.normalizer (B : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hb)) (h.hSB hs)
    set α := φ ⟨b⁻¹ * s, hcX⟩ with hα
    have hαmk : ∀ y (hy : y ∈ K), α (π ⟨y, hy⟩) =
        π ⟨(b⁻¹ * s) * y * (b⁻¹ * s)⁻¹, (h.hXN hcX y).1 hy⟩ := fun y hy => rfl
    have h1 : ∀ x ∈ Bb, α x ∈ Bb := by
      rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩
      rw [hαmk]
      exact ⟨_, (Subgroup.mem_normalizer_iff.1 hcN y).1 hyB, rfl⟩
    have hO2 : ∀ z (hz : z ∈ pCoreOf 2 B), π ⟨z, h.hBK (CFSG.LieType.BorelTits.pCoreOf_le 2 B hz)⟩ ∈
        pCoreOf 2 Bb := by
      intro z hz
      set W := ((pCoreOf 2 B).subgroupOf K).map π with hW
      have hWB : W ≤ Bb := Subgroup.map_mono (Subgroup.subgroupOf_mono K
        (CFSG.LieType.BorelTits.pCoreOf_le 2 B))
      have hWn : Bb ≤ Subgroup.normalizer (W : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
        refine le_normalizer_of_forall ?_
        rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩ _ ⟨⟨w, hwK⟩, hwB, rfl⟩
        refine ⟨⟨y * w * y⁻¹, K.mul_mem (K.mul_mem hyK hwK) (K.inv_mem hyK)⟩, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
            hyB) w).1 hwB
        · show π ⟨y * w * y⁻¹, _⟩ = π ⟨y, hyK⟩ * π ⟨w, hwK⟩ * (π ⟨y, hyK⟩)⁻¹
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
      have hW2 : IsPGroup 2 W := by
        have h2 : IsPGroup 2 ((pCoreOf 2 B).subgroupOf K) :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B).comap_subtype
        exact h2.map π
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWB hWn hW2 ⟨⟨z, _⟩, hz, rfl⟩
    have h2 : ∀ x ∈ Bb, α x * x⁻¹ ∈ pCoreOf 2 Bb := by
      rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩
      rw [hαmk, ← map_inv, ← map_mul]
      have := hO2 _ (hc y hyB)
      convert this using 2
    obtain ⟨β, hβ, hαβ⟩ := hInn α h1 h2
    obtain ⟨⟨b', hb'K⟩, hb'B, rfl⟩ := hβ
    have hb'X : b' ∈ X := h.hKX hb'K
    have hd : b⁻¹ * s * b'⁻¹ ∈ D := by
      have hX' : b⁻¹ * s * b'⁻¹ ∈ X := X.mul_mem hcX (X.inv_mem hb'X)
      rw [hmemD _ hX']
      have e : (⟨b⁻¹ * s * b'⁻¹, hX'⟩ : ↥X) = ⟨b⁻¹ * s, hcX⟩ * (⟨b', hb'X⟩ : ↥X)⁻¹ := rfl
      rw [e, map_mul, map_inv, ← hα, hαβ, hφK b' hb'K]
      exact mul_inv_cancel _
    have e : s = b * (b⁻¹ * s * b'⁻¹) * b' := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
      (Subgroup.mem_sup_right hd)) (Subgroup.mem_sup_left hb'B)
  have hBD : B ⊔ S = B ⊔ D :=
    le_antisymm (sup_le le_sup_left hSBD) (sup_le le_sup_left (hDR.trans hRBS))
  have hBX : B ≤ X := h.hBK.trans h.hKX
  have hset : ((B ⊔ D : Subgroup G) : Set G) = (B : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B D (hBX.trans hXD)
  have hdecomp : ∀ y ∈ B ⊔ S, ∃ b ∈ B, ∃ d ∈ D, y = b * d := by
    intro y hy
    rw [hBD] at hy
    have : y ∈ (B : Set G) * (D : Set G) := by rw [← hset]; exact hy
    obtain ⟨b, hb, d, hd, rfl⟩ := Set.mem_mul.1 this
    exact ⟨b, hb, d, hd, rfl⟩
  have himg : ∀ {Y : Subgroup G}, D ≤ Y → Y ≤ B ⊔ S →
      ∃ Yb : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), Yb = ((Y ⊓ B).subgroupOf K).map π ∧
        Nat.card Y = Nat.card D * Nat.card Yb ∧
        ∀ y (hy : y ∈ X), y ∈ Y ↔ φ ⟨y, hy⟩ ∈ Yb.map MulAut.conj := by
    intro Y hDY hYBS
    refine ⟨((Y ⊓ B).subgroupOf K).map π, rfl, ?_, ?_⟩
    · have hYX : Y ≤ X := hYBS.trans (sup_le hBX (h.hKS ▸ le_sup_right))
      set ψ := φ.comp (Subgroup.inclusion hYX) with hψ
      have hker : ψ.ker = D.subgroupOf Y := by
        ext y
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmemD _ (hYX y.2)]
        rfl
      have hrange : ψ.range = (((Y ⊓ B).subgroupOf K).map π).map MulAut.conj := by
        apply le_antisymm
        · rintro _ ⟨y, rfl⟩
          obtain ⟨b, hb, d, hd, hyd⟩ := hdecomp y (hYBS y.2)
          have hbY : b ∈ Y := by
            have := Y.mul_mem y.2 (Y.inv_mem (hDY hd))
            rwa [hyd, mul_inv_cancel_right] at this
          refine ⟨π ⟨b, h.hBK hb⟩, ⟨⟨b, h.hBK hb⟩, ⟨hbY, hb⟩, rfl⟩, ?_⟩
          rw [← hφK b (h.hBK hb)]
          show φ ⟨b, _⟩ = φ ⟨y, _⟩
          have e : (⟨y, hYX y.2⟩ : ↥X) = ⟨b, h.hKX (h.hBK hb)⟩ * ⟨d, hDX hd⟩ := Subtype.ext hyd
          rw [e, map_mul, (hmemD d (hDX hd)).1 hd, mul_one]
        · rintro _ ⟨_, ⟨⟨b, hbK⟩, hb, rfl⟩, rfl⟩
          refine ⟨⟨b, hb.1⟩, ?_⟩
          show φ ⟨b, _⟩ = _
          rw [hφK b hbK]
      have h1 := Subgroup.card_mul_index ψ.ker
      rw [Subgroup.index_ker, hker, hrange, Subgroup.card_map_of_injective hconj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv] at h1
      exact h1.symm
    · intro y hy
      constructor
      · intro hyY
        obtain ⟨b, hb, d, hd, hyd⟩ := hdecomp y (hYBS hyY)
        have hbY : b ∈ Y := by
          have := Y.mul_mem hyY (Y.inv_mem (hDY hd))
          rwa [hyd, mul_inv_cancel_right] at this
        refine ⟨π ⟨b, h.hBK hb⟩, ⟨⟨b, h.hBK hb⟩, ⟨hbY, hb⟩, rfl⟩, ?_⟩
        rw [← hφK b (h.hBK hb)]
        have e : (⟨y, hy⟩ : ↥X) = ⟨b, h.hKX (h.hBK hb)⟩ * ⟨d, hDX hd⟩ := Subtype.ext hyd
        rw [e, map_mul, (hmemD d (hDX hd)).1 hd, mul_one]
      · rintro ⟨_, ⟨⟨b, hbK⟩, hb, rfl⟩, hφy⟩
        have hbX : b ∈ X := h.hKX hbK
        have hyb : y * b⁻¹ ∈ D := by
          have hX' : y * b⁻¹ ∈ X := X.mul_mem hy (X.inv_mem hbX)
          rw [hmemD _ hX']
          have e : (⟨y * b⁻¹, hX'⟩ : ↥X) = ⟨y, hy⟩ * (⟨b, hbX⟩ : ↥X)⁻¹ := rfl
          rw [e, map_mul, map_inv, hφK b hbK, ← hφy]
          exact mul_inv_cancel _
        have hbY : b ∈ Y := hb.1
        have := Y.mul_mem (hDY hyb) hbY
        rwa [inv_mul_cancel_right] at this
  obtain ⟨Qb, hQb, hQcard, hQmem⟩ := himg h.hD (hQR.trans hRBS)
  obtain ⟨Rb, hRb, hRcard, hRmem⟩ := himg hDR hRBS
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hRbO2 : Rb = pCoreOf 2 Bb := by
    apply le_antisymm
    ·
      have hRbB : Rb ≤ Bb := by
        rw [hRb]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono K inf_le_right)
      have hRbn : Bb ≤ Subgroup.normalizer (Rb : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
        refine le_normalizer_of_forall ?_
        rw [hRb]
        rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩ _ ⟨⟨w, hwK⟩, hw, rfl⟩
        refine ⟨⟨y * w * y⁻¹, K.mul_mem (K.mul_mem hyK hwK) (K.inv_mem hyK)⟩, ⟨?_, ?_⟩, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
            (B ⊔ S) (Subgroup.mem_sup_left hyB)) w).1 hw.1
        · exact B.mul_mem (B.mul_mem hyB hw.2) (B.inv_mem hyB)
        · show π ⟨y * w * y⁻¹, _⟩ = π ⟨y, hyK⟩ * π ⟨w, hwK⟩ * (π ⟨y, hyK⟩)⁻¹
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
      have hRb2 : IsPGroup 2 Rb := by
        rw [hRb]
        have h2 : IsPGroup 2 ((R ⊓ B).subgroupOf K) := (hR2.to_inf_left).comap_subtype
        exact h2.map π
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRbB hRbn hRb2
    ·
      set W := ((pCoreOf 2 Bb).comap π).map K.subtype ⊓ B with hW
      have hWB : W ≤ B := inf_le_right
      have hW2 : IsPGroup 2 W := by
        rintro ⟨w, hwW, hwB⟩
        obtain ⟨⟨w', hw'K⟩, hw', rfl⟩ := hwW
        obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Bb ⟨_, hw'⟩
        have h1 : (⟨w', hw'K⟩ : ↥K) ^ 2 ^ a ∈ CFSG.pCore 2 ↥K := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
          exact congrArg Subtype.val ha
        obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, h1⟩
        refine ⟨a + c, Subtype.ext ?_⟩
        have := congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => ((z : ↥K) : G)) hc
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
        exact this
      have hD2 : IsPGroup 2 D := hR2.to_le hDR
      have hWD2 : IsPGroup 2 (W ⊔ D : Subgroup G) :=
        hW2.to_sup_of_normal_right' hD2 ((hWB.trans hBX).trans hXD)
      have hWn : B ⊔ S ≤ Subgroup.normalizer ((W ⊔ D : Subgroup G) : Set G) := by
        rw [hBD]
        refine le_normalizer_of_forall fun x hx y hy => ?_
        have hxX : x ∈ X := (sup_le hBX hDX) hx
        have hconjWD : W ⊔ D ≤ (W ⊔ D).comap (MulAut.conj x).toMonoidHom := by
          refine sup_le (fun w hw => ?_) (fun d hd => ?_)
          ·
            obtain ⟨b, hb, d', hd', rfl⟩ := hdecomp x (hBD ▸ hx)
            have hwB := hWB hw
            have hbw : b * w * b⁻¹ ∈ W := by
              refine ⟨?_, B.mul_mem (B.mul_mem hb hwB) (B.inv_mem hb)⟩
              obtain ⟨⟨w', hw'K⟩, hw', hww'⟩ := hw.1
              refine ⟨⟨b * w * b⁻¹, K.mul_mem (K.mul_mem (h.hBK hb) (h.hBK hwB))
                (K.inv_mem (h.hBK hb))⟩, ?_, rfl⟩
              have hmem : π ⟨b, h.hBK hb⟩ * π ⟨w', hw'K⟩ * (π ⟨b, h.hBK hb⟩)⁻¹ ∈ pCoreOf 2 Bb :=
                (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Bb
                  ⟨⟨b, h.hBK hb⟩, hb, rfl⟩) _).1 hw'
              have e : (⟨b * w * b⁻¹, K.mul_mem (K.mul_mem (h.hBK hb) (h.hBK hwB))
                  (K.inv_mem (h.hBK hb))⟩ : ↥K) =
                  ⟨b, h.hBK hb⟩ * ⟨w', hw'K⟩ * (⟨b, h.hBK hb⟩ : ↥K)⁻¹ := by
                apply Subtype.ext
                simp only [Subgroup.coe_mul, Subgroup.coe_inv]
                rw [← hww']
                rfl
              show π _ ∈ pCoreOf 2 Bb
              rw [e, map_mul, map_mul, map_inv]
              exact hmem
            have hd'X := hDX hd'
            have hdw : d' * w * d'⁻¹ * w⁻¹ ∈ D := by
              have h1 : w * d'⁻¹ * w⁻¹ ∈ D :=
                (Subgroup.mem_normalizer_iff.1 (hXD (hBX hwB)) _).1 (D.inv_mem hd')
              have := D.mul_mem hd' h1
              rwa [show d' * (w * d'⁻¹ * w⁻¹) = d' * w * d'⁻¹ * w⁻¹ by group] at this
            have hdw' : d' * w * d'⁻¹ ∈ W ⊔ D := by
              have := Subgroup.mul_mem _ (Subgroup.mem_sup_right hdw) (Subgroup.mem_sup_left hw)
              rwa [show d' * w * d'⁻¹ * w⁻¹ * w = d' * w * d'⁻¹ by group] at this
            show (MulAut.conj (b * d')) w ∈ W ⊔ D
            rw [MulAut.conj_apply]
            have e : b * d' * w * (b * d')⁻¹ = b * (d' * w * d'⁻¹) * b⁻¹ := by group
            rw [e]
            have hbWD : W ⊔ D ≤ (W ⊔ D).comap (MulAut.conj b).toMonoidHom := by
              refine sup_le (fun w₁ hw₁ => ?_) (fun d₁ hd₁ => ?_)
              · show b * w₁ * b⁻¹ ∈ W ⊔ D
                refine Subgroup.mem_sup_left ⟨?_, B.mul_mem (B.mul_mem hb (hWB hw₁)) (B.inv_mem hb)⟩
                obtain ⟨⟨w', hw'K⟩, hw', hww'⟩ := hw₁.1
                refine ⟨⟨b * w₁ * b⁻¹, K.mul_mem (K.mul_mem (h.hBK hb) (h.hBK (hWB hw₁)))
                  (K.inv_mem (h.hBK hb))⟩, ?_, rfl⟩
                have hmem : π ⟨b, h.hBK hb⟩ * π ⟨w', hw'K⟩ * (π ⟨b, h.hBK hb⟩)⁻¹ ∈
                    pCoreOf 2 Bb :=
                  (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Bb
                    ⟨⟨b, h.hBK hb⟩, hb, rfl⟩) _).1 hw'
                have e : (⟨b * w₁ * b⁻¹, K.mul_mem (K.mul_mem (h.hBK hb) (h.hBK (hWB hw₁)))
                    (K.inv_mem (h.hBK hb))⟩ : ↥K) =
                    ⟨b, h.hBK hb⟩ * ⟨w', hw'K⟩ * (⟨b, h.hBK hb⟩ : ↥K)⁻¹ := by
                  apply Subtype.ext
                  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
                  rw [← hww']
                  rfl
                show π _ ∈ pCoreOf 2 Bb
                rw [e, map_mul, map_mul, map_inv]
                exact hmem
              · show b * d₁ * b⁻¹ ∈ W ⊔ D
                exact Subgroup.mem_sup_right
                  ((Subgroup.mem_normalizer_iff.1 (hXD (hBX hb)) d₁).1 hd₁)
            exact hbWD hdw'
          · show x * d * x⁻¹ ∈ W ⊔ D
            exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hXD hxX) d).1 hd)
        exact hconjWD hy
      have hWDR : W ⊔ D ≤ R :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          (sup_le (hWB.trans le_sup_left) (hDR.trans hRBS)) hWn hWD2
      rintro z hz
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
      have hzB : π k ∈ Bb := CFSG.LieType.BorelTits.pCoreOf_le 2 Bb hz
      obtain ⟨⟨b, hbK⟩, hbB, hbk⟩ := hzB
      have hbW : b ∈ W := ⟨⟨⟨b, hbK⟩, by show π ⟨b, hbK⟩ ∈ pCoreOf 2 Bb; rw [hbk]; exact hz, rfl⟩,
        hbB⟩
      rw [hRb]
      exact ⟨⟨b, hbK⟩, ⟨hWDR (Subgroup.mem_sup_left hbW), hbB⟩, hbk⟩
  have hQbR : Qb ≤ Rb := by
    rw [hQb, hRb]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K (inf_le_inf_right _ hQR))
  have hQbne : Qb ≠ pCoreOf 2 Bb := by
    intro heq
    have h1 : Rb = Qb := hRbO2.trans heq.symm
    have h2 : Nat.card Q = Nat.card R := by rw [hQcard, hRcard, h1]
    exact h.hQlt.ne (Subgroup.eq_of_le_of_card_ge hQR h2.ge)
  have hQbot : Qb ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Q = Nat.card D := by rw [hQcard, hbot, Subgroup.card_bot, mul_one]
    have hQD : D = Q := Subgroup.eq_of_le_of_card_ge h.hD h1.le
    exact h.hXQ (hQD ▸ hXD)
  have hQbN : Bb ≤ Subgroup.normalizer (Qb : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    refine le_normalizer_of_forall ?_
    rw [hQb]
    rintro _ ⟨⟨y, hyK⟩, hyB, rfl⟩ _ ⟨⟨w, hwK⟩, hw, rfl⟩
    refine ⟨⟨y * w * y⁻¹, K.mul_mem (K.mul_mem hyK hwK) (K.inv_mem hyK)⟩, ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (h.hQN (Subgroup.mem_sup_left hyB)) w).1 hw.1
    · exact B.mul_mem (B.mul_mem hyB hw.2) (B.inv_mem hyB)
    · show π ⟨y * w * y⁻¹, _⟩ = π ⟨y, hyK⟩ * π ⟨w, hwK⟩ * (π ⟨y, hyK⟩)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
  have hQbcard : Nat.card ↥(pCoreOf 2 Bb) ≤ 2 ^ m * Nat.card Qb := by
    have h1 := h.hcard
    rw [hRcard, hQcard] at h1
    have h2 : Nat.card D * Nat.card Rb ≤ Nat.card D * (2 ^ m * Nat.card Qb) := by
      calc Nat.card D * Nat.card Rb ≤ 2 ^ m * (Nat.card D * Nat.card Qb) := h1
        _ = Nat.card D * (2 ^ m * Nat.card Qb) := by ring
    rw [← hRbO2]
    exact Nat.le_of_mul_le_mul_left h2 hDpos
  obtain ⟨Pb, hBP, hPN, hPB⟩ := hPar Qb (hRbO2 ▸ hQbR) hQbne hQbot hQbN hQbcard
  refine ⟨((Pb.map MulAut.conj).comap φ).map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hsX : s ∈ X := h.hKS ▸ Subgroup.mem_sup_right hs
    refine ⟨⟨s, hsX⟩, ?_, rfl⟩
    obtain ⟨b, hb, d, hd, hsd⟩ := hdecomp s (Subgroup.mem_sup_right hs)
    refine ⟨π ⟨b, h.hBK hb⟩, hBP ⟨⟨b, h.hBK hb⟩, hb, rfl⟩, ?_⟩
    rw [← hφK b (h.hBK hb)]
    have e : (⟨s, hsX⟩ : ↥X) = ⟨b, h.hKX (h.hBK hb)⟩ * ⟨d, hDX hd⟩ := Subtype.ext hsd
    rw [e, map_mul, (hmemD d (hDX hd)).1 hd, mul_one]
  · exact Subgroup.map_subtype_le _
  · refine le_normalizer_of_forall ?_
    rintro _ ⟨x, ⟨p, hp, hpx⟩, rfl⟩ q hq
    have hqX : q ∈ X := (hQR.trans (hRBS.trans (sup_le hBX (h.hKS ▸ le_sup_right)))) hq
    have hxq : (x : G) * q * (x : G)⁻¹ ∈ X := X.mul_mem (X.mul_mem x.2 hqX) (X.inv_mem x.2)
    show (x : G) * q * (x : G)⁻¹ ∈ Q
    rw [hQmem _ hxq]
    obtain ⟨q', hq', hφq⟩ := (hQmem q hqX).1 hq
    refine ⟨p * q' * p⁻¹, (Subgroup.mem_normalizer_iff.1 (hPN hp) q').1 hq', ?_⟩
    have e : (⟨(x : G) * q * (x : G)⁻¹, hxq⟩ : ↥X) = x * ⟨q, hqX⟩ * x⁻¹ := rfl
    rw [e, map_mul φ, map_mul φ, map_inv φ, ← hpx, ← hφq, map_mul, map_mul, map_inv]
  · intro hPBN
    apply hPB
    refine le_normalizer_of_forall fun p hp y hy => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) p
    obtain ⟨⟨b, hbK⟩, hbB, rfl⟩ := hy
    have hkX : (k : G) ∈ X := h.hKX k.2
    have hkP : (k : G) ∈ ((Pb.map MulAut.conj).comap φ).map X.subtype := by
      refine ⟨⟨k, hkX⟩, ⟨_, hp, ?_⟩, rfl⟩
      rw [hφK k k.2]
    have hkb : (k : G) * b * (k : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.1 (hPBN hkP) b).1 hbB
    refine ⟨⟨(k : G) * b * (k : G)⁻¹, K.mul_mem (K.mul_mem k.2 hbK) (K.inv_mem k.2)⟩, hkb, ?_⟩
    show π _ = _
    have e : (⟨(k : G) * b * (k : G)⁻¹, K.mul_mem (K.mul_mem k.2 hbK) (K.inv_mem k.2)⟩ : ↥K) =
        k * ⟨b, hbK⟩ * k⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]

theorem le_pCore_of_normal {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N ≤ CFSG.pCore 2 H :=
  show N ≤ sSup {K : Subgroup H | K.Normal ∧ IsPGroup 2 K} from le_sSup ⟨hN, hp⟩

theorem nonempty_modO2_equiv {H : Type} [Group H] {B : Subgroup G} {B' : Subgroup H}
    (f : ↥B →* ↥B') (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nonempty (ModO2 B ≃* ModO2 B') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (CFSG.pCore 2 ↥B).map f ≤ CFSG.pCore 2 ↥B' :=
    le_pCore_of_normal (Subgroup.Normal.map CFSG.pCore_normal f hf) (CFSG.pCore_isPGroup.map f)
  have h2 : (CFSG.pCore 2 ↥B').comap f ≤ CFSG.pCore 2 ↥B :=
    le_pCore_of_normal (Subgroup.Normal.comap CFSG.pCore_normal f)
      (CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hker)
  have hle : CFSG.pCore 2 ↥B ≤ (CFSG.pCore 2 ↥B').comap f := Subgroup.map_le_iff_le_comap.1 h1
  set g := QuotientGroup.map (CFSG.pCore 2 ↥B) (CFSG.pCore 2 ↥B') f hle with hg
  refine ⟨MulEquiv.ofBijective g ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H b =>
      rw [hg, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
      exact (QuotientGroup.eq_one_iff b).2 (h2 hx)
  · intro y
    induction y using QuotientGroup.induction_on with
    | H b' =>
      obtain ⟨b, rfl⟩ := hf b'
      exact ⟨b, rfl⟩

@[expose] noncomputable def barHom {K B : Subgroup G} (hBK : B ≤ K) : ↥B →* ↥(barOf K B) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).subgroupMap (B.subgroupOf K)).comp
    (Subgroup.subgroupOfEquivOfLe hBK).symm.toMonoidHom

theorem barHom_surjective {K B : Subgroup G} (hBK : B ≤ K) : Function.Surjective (barHom hBK) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBK).symm.surjective

theorem isPGroup_ker_barHom [Finite G] {K B : Subgroup G} (hBK : B ≤ K) :
    IsPGroup 2 (barHom hBK).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x
  have hx : barHom hBK x = 1 := x.2
  have hk : (⟨x, hBK (x : ↥B).2⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff]
    exact congrArg Subtype.val hx
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hk⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥K) => ((z : ↥K) : G)) hn
  simpa using this

theorem nonempty_modO2_barOf [Finite G] {K B : Subgroup G} (hBK : B ≤ K) :
    Nonempty (ModO2 B ≃* ModO2 (barOf K B)) :=
  nonempty_modO2_equiv (barHom hBK) (barHom_surjective hBK) (isPGroup_ker_barHom hBK)

theorem exists_sylow_normalizing [Finite G] {X K S B : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hS : QuasithinUnique.IsSylowTwoOf S X)
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    ∃ T : Sylow 2 (↥K ⧸ CFSG.pCore 2 ↥K),
      (T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤
        Subgroup.normalizer ((barOf K B : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSX, hS2, hSodd⟩ := hS
  let S₀ : Sylow 2 ↥X := hS2.comap_subtype.toSylow hSodd
  have : (K.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hXN g.2) n).1 hn⟩
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S₀ (N := K.subgroupOf X)
  let e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  let ψ : ↥(K.subgroupOf X) →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp e.toMonoidHom
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp e.surjective
  refine ⟨P.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective]
  refine le_normalizer_of_forall ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨⟨y, hyK⟩, hyB, rfl⟩
  have hx' : x ∈ ((S₀ : Subgroup ↥X) ⊓ K.subgroupOf X).subgroupOf (K.subgroupOf X) := by
    rw [← hP]
    exact hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx'
  have hxS : ((x : ↥X) : G) ∈ S := hx'.1
  have hxy : ((x : ↥X) : G) * y * ((x : ↥X) : G)⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.1 (hSB hxS) y).1 hyB
  refine ⟨⟨_, K.mul_mem (K.mul_mem (e x).2 hyK) (K.inv_mem (e x).2)⟩, hxy, ?_⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥K) _ =
    QuotientGroup.mk' (CFSG.pCore 2 ↥K) (e x) * QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hyK⟩ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (e x))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

section Transport

variable {M M' : Type*} [Group M] [Group M']

theorem map_le_normalizer_map (ι : M ≃* M') {A H : Subgroup M}
    (h : A ≤ Subgroup.normalizer (H : Set M)) :
    A.map ι.toMonoidHom ≤ Subgroup.normalizer ((H.map ι.toMonoidHom : Subgroup M') : Set M') := by
  refine le_normalizer_of_forall ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨y, hy, rfl⟩
  refine ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.1 (h ha) y).1 hy, ?_⟩
  simp

theorem innClosed_map (ι : M ≃* M') {B : Subgroup M} (hB : InnClosed B) :
    InnClosed (B.map ι.toMonoidHom) := by
  intro α' h1 h2
  set α : MulAut M := (MulAut.congr ι.symm) α' with hα
  have hαapp : ∀ x, α x = ι.symm (α' (ι x)) := fun x => rfl
  have hO2 := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 ι B
  have h1' : ∀ x ∈ B, α x ∈ B := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h1 (ι x) ⟨x, hx, rfl⟩
    rw [hαapp, ← hyx]
    simpa using hy
  have h2' : ∀ x ∈ B, α x * x⁻¹ ∈ pCoreOf 2 B := by
    intro x hx
    have h3 := h2 (ι x) ⟨x, hx, rfl⟩
    rw [hO2] at h3
    obtain ⟨z, hz, hzx⟩ := h3
    have : α x * x⁻¹ = z := by
      apply ι.injective
      rw [map_mul, map_inv, hαapp, MulEquiv.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  obtain ⟨β, hβ, hαβ⟩ := hB α h1' h2'
  refine ⟨ι β, ⟨β, hβ, rfl⟩, ?_⟩
  ext y
  have := congrArg (fun f : MulAut M => ι (f (ι.symm y))) hαβ
  simp only [hαapp, MulEquiv.apply_symm_apply, MulAut.conj_apply, map_mul, map_inv] at this
  rw [MulAut.conj_apply]
  exact this

theorem parConclusion_map (ι : M ≃* M') {B : Subgroup M} {m : ℕ} (hB : ParConclusion B m) :
    ParConclusion (B.map ι.toMonoidHom) m := by
  intro Q' hQ1 hQ2 hQ3 hQ4 hQ5
  have hO2 := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 ι B
  set Q := Q'.map ι.symm.toMonoidHom with hQ
  have hQ' : Q.map ι.toMonoidHom = Q' := by
    rw [hQ, Subgroup.map_map]
    convert Subgroup.map_id Q'
    ext x
    simp
  have hmapB : (B.map ι.toMonoidHom).map ι.symm.toMonoidHom = B := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id B
    ext x
    simp
  have hO2' : (pCoreOf 2 B).map ι.toMonoidHom = pCoreOf 2 (B.map ι.toMonoidHom) := hO2.symm
  have hinj : ∀ {H H' : Subgroup M}, H.map ι.toMonoidHom = H'.map ι.toMonoidHom → H = H' :=
    fun h => Subgroup.map_injective ι.injective h
  obtain ⟨P, hBP, hPN, hPB⟩ := hB Q
    (by
      have := Subgroup.map_mono (f := ι.symm.toMonoidHom) hQ1
      rw [← hO2', Subgroup.map_map] at this
      convert this using 1
      convert (Subgroup.map_id (pCoreOf 2 B)).symm
      ext x
      simp)
    (fun h => hQ2 (by rw [← hQ', h, hO2']))
    (fun h => hQ3 (by rw [← hQ', h, Subgroup.map_bot]))
    (by
      have := map_le_normalizer_map ι.symm hQ4
      rwa [hmapB] at this)
    (by
      rw [Subgroup.card_map_of_injective ι.symm.injective]
      rw [← hO2', Subgroup.card_map_of_injective ι.injective] at hQ5
      exact hQ5)
  refine ⟨P.map ι.toMonoidHom, Subgroup.map_mono hBP, ?_, fun h => hPB ?_⟩
  · have := map_le_normalizer_map ι hPN
    rwa [hQ'] at this
  · have := map_le_normalizer_map ι.symm h
    rwa [hmapB, Subgroup.map_map, show ι.symm.toMonoidHom.comp ι.toMonoidHom = MonoidHom.id M by
      ext x; simp, Subgroup.map_id] at this

theorem center_eq_bot_of_mulEquiv (ι : M ≃* M') (h : Subgroup.center M' = ⊥) :
    Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : ι z ∈ Subgroup.center M' := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨w', rfl⟩ := ι.surjective w
    rw [← map_mul, ← map_mul, hz]
  rw [h, Subgroup.mem_bot] at hz'
  exact ι.injective (hz'.trans (map_one ι).symm)

end Transport

end CFSG.Quasithin.H13.KG1296
