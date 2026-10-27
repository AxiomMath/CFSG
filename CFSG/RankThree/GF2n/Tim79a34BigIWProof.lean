module

public import CFSG.RankThree.GF2n.Tim79a34BigNatural
public import CFSG.RankThree.GF2n.Tim79a34BigPAct
public import CFSG.RankThree.GF2n.Tim79a34SpRadLine
import CFSG.RankThree.GF2n.Tim79a34BigIWPair
import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof
public import CFSG.RankThree.GF2n.Tim79a34Pairing

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V Q P H : Subgroup G}

theorem mem_of_mem_spRad_of_forall_mulVec_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {T : Subgroup (StatedSp n F)}
    (hT : CaseM.IsTransGroup a T) {g : StatedSp n F} (hg : g ∈ spRad a)
    (hfix : ∀ x, CaseM.spForm a x = 0 → SpExtras.mat n F g *ᵥ x = x) :
    g ∈ T := by
  obtain ⟨u, hu, c, hparam⟩ := exists_spRad_param ha hg
  have hforall : ∀ x, spForm a x = 0 → spForm (0 : Fin n ⊕ Fin n → F) x = 0 →
      spForm u x = 0 := by
    intro x hx _
    exact (spRad_mulVec_eq_self_iff ha hparam hx).1 (hfix x hx)
  obtain ⟨μ, ν, hμν⟩ := exists_eq_smul_add_smul_of_forall_spForm hforall
  have hν : u = ν • a := by simpa using hμν
  have hmat : SpExtras.mat n F g = spTrans a c := mat_eq_spTrans_of_param hparam hν
  exact (hT.1 g).2 ⟨c, hmat⟩

theorem BigEndHyp.bigPAct_mulVec_eq_self_iff (h : BigEndHyp M V Q P H)
    {n f : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (p : ↥P)
    (x : Fin n ⊕ Fin n → GaloisField 2 f) :
    SpExtras.mat n (GaloisField 2 f) (h.bigPAct hNat p) *ᵥ x = x ↔
      (p : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p : G) := by
  constructor
  · intro hx
    have hspec := h.bigPAct_spec hNat p x
    rw [hx] at hspec
    calc (p : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G)
        = ((p : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p : G)⁻¹) *
            (p : G) := by group
      _ = ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p : G) := by rw [← hspec]
  · intro hcomm
    have hspec := h.bigPAct_spec hNat p x
    have h1 : (p : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p : G)⁻¹ =
        ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) := by
      rw [hcomm]
      group
    rw [h1] at hspec
    exact ψ.injective (Additive.toMul.injective (Subtype.ext hspec))

theorem BigEndHyp.centralizes_of_commute_spForm_zero (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (hf : 2 ^ f = qBar V H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {B : Subgroup G} (hBP : B ≤ P) (hBV : B ⊓ V = ⊥)
    (hBTI : ∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀1 : b₀ ≠ 1)
    (x : Fin n ⊕ Fin n → GaloisField 2 f) (hx : CaseM.spForm a x = 0)
    (hcomm : b₀ * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * b₀) :
    ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) ∈
      Subgroup.centralizer (B : Set G) := by
  have hψP : ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) ∈ P :=
    (h.psi_mem_P_iff hf hNat ha hT hTV x).2 hx
  have hψI : ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) ∈ wOf V H ⊔ cPbar V H P :=
    Subgroup.mem_sup_left (Additive.toMul (ψ x)).2
  have hmem : ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) ∈
      (wOf V H ⊔ cPbar V H P) ⊓ P := Subgroup.mem_inf.mpr ⟨hψI, hψP⟩
  exact h.centralizes_of_commute_of_isTI hZ hBP hBV hBTI hmem hb₀ hb₀1 hcomm.symm

theorem BigEndHyp.B_inf_sup_Eof_eq_bot (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (hf : 2 ^ f = qBar V H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {B : Subgroup G} (hBP : B ≤ P) (hBV : B ⊓ V = ⊥)
    (hBTI : ∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B)
    (hBL : ¬ B ≤ V ⊔ Eof V H P) :
    B ⊓ (V ⊔ Eof V H P) = ⊥ := by
  classical
  by_contra hne
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb₀1' : b₀ ≠ 1 := fun h1 => hb₀1 (Subtype.ext h1)
  have hb₀B : b₀ ∈ B := (Subgroup.mem_inf.mp hb₀).1
  have hb₀sup : b₀ ∈ V ⊔ Eof V H P := (Subgroup.mem_inf.mp hb₀).2
  have hb₀P : b₀ ∈ P := hBP hb₀B
  have hb₀T : h.bigPAct hNat ⟨b₀, hb₀P⟩ ∈ T :=
    (h.bigPAct_mem_T_iff hNat hZ hTV ⟨b₀, hb₀P⟩).2 hb₀sup
  have hfix₀ : ∀ x, CaseM.spForm a x = 0 →
      SpExtras.mat n (GaloisField 2 f) (h.bigPAct hNat ⟨b₀, hb₀P⟩) *ᵥ x = x := by
    intro x hx
    obtain ⟨c, hc⟩ := (hT.1 (h.bigPAct hNat ⟨b₀, hb₀P⟩)).1 hb₀T
    rw [hc, spTrans_mulVec, hx, mul_zero, zero_smul, add_zero]
  have hcent : ∀ x, CaseM.spForm a x = 0 →
      ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) ∈ Subgroup.centralizer (B : Set G) := by
    intro x hx
    have hcomm : b₀ * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * b₀ :=
      (h.bigPAct_mulVec_eq_self_iff hNat ⟨b₀, hb₀P⟩ x).1 (hfix₀ x hx)
    exact h.centralizes_of_commute_spForm_zero hZ hNat hf ha hT hTV hBP hBV hBTI
      hb₀B hb₀1' x hx hcomm
  have hBfix : ∀ p : ↥P, (p : G) ∈ B → ∀ x, CaseM.spForm a x = 0 →
      SpExtras.mat n (GaloisField 2 f) (h.bigPAct hNat p) *ᵥ x = x := by
    intro p hp x hx
    have hcomm : (p : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p : G) :=
      Subgroup.mem_centralizer_iff.mp (hcent x hx) (p : G) hp
    exact (h.bigPAct_mulVec_eq_self_iff hNat p x).2 hcomm
  have hBsub : B ≤ V ⊔ Eof V H P := by
    intro b hbB
    have hbP : b ∈ P := hBP hbB
    have hrad : h.bigPAct hNat ⟨b, hbP⟩ ∈ spRad a :=
      h.bigPAct_mem_spRad hNat hZ ha hT hTV ⟨b, hbP⟩
    have hbT : h.bigPAct hNat ⟨b, hbP⟩ ∈ T :=
      mem_of_mem_spRad_of_forall_mulVec_eq ha hT hrad (hBfix ⟨b, hbP⟩ hbB)
    exact (h.bigPAct_mem_T_iff hNat hZ hTV ⟨b, hbP⟩).1 hbT
  exact hBL hBsub

theorem BigEndHyp.image_B_inf_T_eq_bot (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (hTV : T.map Φ.toMonoidHom = Vy V H)
    {B : Subgroup G} (hbot : B ⊓ (V ⊔ Eof V H P) = ⊥) :
    (B.subgroupOf P).map (h.bigPAct hNat) ⊓ T = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨hxD, hxT⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxD
  have hpB : (p : G) ∈ B := Subgroup.mem_subgroupOf.mp hp
  have hxT' : h.bigPAct hNat p ∈ T := hpx ▸ hxT
  have hpE : (p : G) ∈ V ⊔ Eof V H P :=
    (h.bigPAct_mem_T_iff hNat hZ hTV p).1 hxT'
  have hpbot : (p : G) ∈ B ⊓ (V ⊔ Eof V H P) := Subgroup.mem_inf.mpr ⟨hpB, hpE⟩
  rw [hbot, Subgroup.mem_bot] at hpbot
  have hp1 : p = 1 := Subtype.ext hpbot
  rw [← hpx, hp1, map_one]

theorem BigEndHyp.card_map_bigPAct_subgroupOf (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    {B : Subgroup G} (hBP : B ≤ P)
    (hbot : B ⊓ (V ⊔ Eof V H P) = ⊥)
    (hBcard : Nat.card ↥B = Nat.card (GaloisField 2 f)) :
    Nat.card ↥((B.subgroupOf P).map (h.bigPAct hNat)) =
      Nat.card (GaloisField 2 f) := by
  let φB : ↥(B.subgroupOf P) →* ↥(StatedSp n (GaloisField 2 f)) :=
    (h.bigPAct hNat).comp (B.subgroupOf P).subtype
  have hinj : Function.Injective φB := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxP : ((x : ↥P)) = 1 := by
      have hmemI : ((x : ↥P) : G) ∈ wOf V H ⊔ cPbar V H P :=
        (h.bigPAct_eq_one_iff hNat hZ (x : ↥P)).1 hx
      have hmemE : ((x : ↥P) : G) ∈ V ⊔ Eof V H P :=
        Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨(x : ↥P).2, hmemI⟩)
      have hmemB : ((x : ↥P) : G) ∈ B := Subgroup.mem_subgroupOf.mp x.2
      have h0 : ((x : ↥P) : G) ∈ B ⊓ (V ⊔ Eof V H P) :=
        Subgroup.mem_inf.mpr ⟨hmemB, hmemE⟩
      rw [hbot, Subgroup.mem_bot] at h0
      exact Subtype.ext h0
    exact Subtype.ext hxP
  let e : ↥(B.subgroupOf P) → ↥((B.subgroupOf P).map (h.bigPAct hNat)) := fun x =>
    ⟨φB x, Subgroup.mem_map_of_mem (h.bigPAct hNat) x.2⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro x y hxy
      exact hinj (Subtype.ext_iff.mp hxy)
    · intro x
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hmap : Nat.card ↥((B.subgroupOf P).map (h.bigPAct hNat)) =
      Nat.card ↥(B.subgroupOf P) :=
    (Nat.card_congr (Equiv.ofBijective e hbij)).symm
  have hsub : Nat.card ↥(B.subgroupOf P) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  rw [hmap, hsub, hBcard]

theorem BigEndHyp.image_B_fixes (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (hf : 2 ^ f = qBar V H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {B : Subgroup G} (hBP : B ≤ P) (hBV : B ⊓ V = ⊥)
    (hBTI : ∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B) :
    ∀ d₀ ∈ (B.subgroupOf P).map (h.bigPAct hNat), d₀ ≠ 1 →
      ∀ x, CaseM.spForm a x = 0 →
        SpExtras.mat n (GaloisField 2 f) d₀ *ᵥ x = x →
        ∀ d ∈ (B.subgroupOf P).map (h.bigPAct hNat),
          SpExtras.mat n (GaloisField 2 f) d *ᵥ x = x := by
  intro d₀ hd₀ hd₀1 x hx hfix₀ d hd
  obtain ⟨p₀, hp₀, hp₀d⟩ := Subgroup.mem_map.mp hd₀
  have hp₀B : (p₀ : G) ∈ B := Subgroup.mem_subgroupOf.mp hp₀
  have hp₀1 : p₀ ≠ 1 := by
    intro h1
    apply hd₀1
    rw [← hp₀d, h1, map_one]
  have hp₀1' : (p₀ : G) ≠ 1 := fun h1 => hp₀1 (Subtype.ext h1)
  have hfix₀' : SpExtras.mat n (GaloisField 2 f) (h.bigPAct hNat p₀) *ᵥ x = x := by
    simpa [← hp₀d] using hfix₀
  have hcomm₀ : (p₀ : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p₀ : G) :=
    (h.bigPAct_mulVec_eq_self_iff hNat p₀ x).1 hfix₀'
  have hcent := h.centralizes_of_commute_spForm_zero hZ hNat hf ha hT hTV hBP hBV hBTI
    hp₀B hp₀1' x hx hcomm₀
  obtain ⟨p, hp, hpd⟩ := Subgroup.mem_map.mp hd
  have hpB : (p : G) ∈ B := Subgroup.mem_subgroupOf.mp hp
  have hcomm : (p : G) * ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ x) : ↥(wOf V H)) : G) * (p : G) :=
    Subgroup.mem_centralizer_iff.mp hcent (p : G) hpB
  rw [← hpd]
  exact (h.bigPAct_mulVec_eq_self_iff hNat p x).2 hcomm

theorem BigEndHyp.exists_line_of_isTI (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (hf : 2 ^ f = qBar V H)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {B : Subgroup G} (hBP : B ≤ P) (hBV : B ⊓ V = ⊥)
    (hBTI : ∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B)
    (hbot : B ⊓ (V ⊔ Eof V H P) = ⊥)
    (hBcard : Nat.card ↥B = Nat.card (GaloisField 2 f)) :
    ∃ w : Fin n ⊕ Fin n → GaloisField 2 f,
      CaseM.spForm a w = 0 ∧ (∀ μ : GaloisField 2 f, w ≠ μ • a) ∧
        (B.subgroupOf P).map (h.bigPAct hNat) ⊔ T = spRadLine a w := by
  have hD'rad : (B.subgroupOf P).map (h.bigPAct hNat) ≤ spRad a := by
    rintro x hx
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact h.bigPAct_mem_spRad hNat hZ ha hT hTV p
  have hD'T := h.image_B_inf_T_eq_bot hZ hNat hTV hbot
  have hcard := h.card_map_bigPAct_subgroupOf hZ hNat hBP hbot hBcard
  have hfix := h.image_B_fixes hZ hNat hf ha hT hTV hBP hBV hBTI
  exact exists_sup_eq_spRadLine ha hT hD'rad hD'T hcard hfix

theorem BigEndHyp.conjSubgroup_isTI (h : BigEndHyp M V Q P H)
    {B : Subgroup G} (hBP : B ≤ P) (hBV : B ⊓ V = ⊥)
    (hBTI : ∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B)
    {y : G} (hyM : y ∈ M) :
    conjSubgroup y B ≤ P ∧ conjSubgroup y B ⊓ V = ⊥ ∧
      (∀ m ∈ M, conjSubgroup m (conjSubgroup y B) ⊓ conjSubgroup y B ≠ ⊥ →
        conjSubgroup m (conjSubgroup y B) = conjSubgroup y B) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rw [mem_conjSubgroup] at hb
    have h1 : y * (y⁻¹ * b * y) * y⁻¹ ∈ P := h.conj_mem_P_of_mem_M hyM (hBP hb)
    have h2 : y * (y⁻¹ * b * y) * y⁻¹ = b := by group
    rwa [h2] at h1
  · have hyV : conjSubgroup y V = V :=
      mem_normalizer_iff_conjSubgroup_eq.mp (hc.normalizer_eq ▸ hyM)
    calc conjSubgroup y B ⊓ V = conjSubgroup y B ⊓ conjSubgroup y V := by rw [hyV]
      _ = conjSubgroup y (B ⊓ V) := (conjSubgroup_inf y B V).symm
      _ = ⊥ := by rw [hBV, conjSubgroup_bot]
  · intro m hm hne
    have hmy : y⁻¹ * (m * y) ∈ M :=
      M.mul_mem (M.inv_mem hyM) (M.mul_mem hm hyM)
    have hconj : conjSubgroup y (conjSubgroup (y⁻¹ * (m * y)) B ⊓ B) =
        conjSubgroup m (conjSubgroup y B) ⊓ conjSubgroup y B := by
      have harg : y * (y⁻¹ * (m * y)) = m * y := by group
      rw [conjSubgroup_inf, ← conjSubgroup_mul, ← conjSubgroup_mul, harg]
    have hkey : conjSubgroup (y⁻¹ * (m * y)) B ⊓ B ≠ ⊥ := by
      intro hbot
      apply hne
      rw [← hconj, hbot, conjSubgroup_bot]
    have heq := hBTI (y⁻¹ * (m * y)) hmy hkey
    have hconj3 : conjSubgroup (m * y) B = conjSubgroup y B := by
      have h1 := congrArg (fun K => conjSubgroup y K) heq
      rw [← conjSubgroup_mul] at h1
      have h2 : y * (y⁻¹ * (m * y)) = m * y := by group
      rwa [h2] at h1
    rw [← conjSubgroup_mul]
    exact hconj3

theorem BigEndHyp.map_conj_image_B (h : BigEndHyp M V Q P H)
    {n f : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    {B : Subgroup G} (hBP : B ≤ P)
    {y : ↥(xOf V H)} (hyM : (y : G) ∈ M)
    {g : ↥(StatedSp n (GaloisField 2 f))}
    (hyg : Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H y) = g) :
    ((conjSubgroup (y : G) B).subgroupOf P).map (h.bigPAct hNat) =
      ((B.subgroupOf P).map (h.bigPAct hNat)).map
        (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · rintro x ⟨d, hd, rfl⟩
    obtain ⟨b, hbB, hbd⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hd)
    have hbP : b ∈ P := hBP hbB
    have hmemP : (y : G) * b * (y : G)⁻¹ ∈ P :=
      h.conj_mem_P_of_mem_M hyM hbP
    have hd_eq : (⟨(y : G) * b * (y : G)⁻¹, hmemP⟩ : ↥P) = d := by
      apply Subtype.ext
      exact hbd
    rw [← hd_eq]
    have hbig := h.bigPAct_conj hNat hyM ⟨b, hbP⟩
    rw [hyg] at hbig
    rw [hbig]
    exact Subgroup.mem_map.mpr ⟨h.bigPAct hNat ⟨b, hbP⟩,
      Subgroup.mem_map_of_mem (h.bigPAct hNat) (by
        rw [Subgroup.mem_subgroupOf]
        exact hbB), rfl⟩
  · rintro x ⟨d, hd, rfl⟩
    obtain ⟨b, hb, hbd⟩ := Subgroup.mem_map.mp hd
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hmemD : (y : G) * (b : G) * (y : G)⁻¹ ∈ conjSubgroup (y : G) B :=
      conj_mem_conjSubgroup (y : G) hbB
    have hmemP : (y : G) * (b : G) * (y : G)⁻¹ ∈ P :=
      h.conj_mem_P_of_mem_M hyM b.2
    have hbig := h.bigPAct_conj hNat hyM b
    rw [hyg] at hbig
    rw [← hbd]
    change g * h.bigPAct hNat b * g⁻¹ ∈
      ((conjSubgroup (y : G) B).subgroupOf P).map (h.bigPAct hNat)
    rw [← hbig]
    exact Subgroup.mem_map.mpr ⟨⟨_, hmemP⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact hmemD, rfl⟩

theorem BigEndHyp.T_le_map_of_le (h : BigEndHyp M V Q P H)
    {n f : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (hTV : T.map Φ.toMonoidHom = Vy V H)
    {S : Subgroup G} (hVS : V ≤ S) :
    T ≤ (S.subgroupOf P).map (h.bigPAct hNat) := by
  intro t ht
  obtain ⟨v, hvV, hvt⟩ := h.exists_bigPAct_eq_of_mem_T hNat hTV ht
  exact Subgroup.mem_map.mpr ⟨⟨v, h.setup.mc.toMinCex.V_le_P hvV⟩, by
    rw [Subgroup.mem_subgroupOf]
    exact hVS hvV, hvt⟩

theorem BigEndHyp.cover_of_lines (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {n f : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    {a : Fin n ⊕ Fin n → GaloisField 2 f}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {B : Subgroup G} (hBP : B ≤ P)
    {w : Fin n ⊕ Fin n → GaloisField 2 f}
    (hline : (B.subgroupOf P).map (h.bigPAct hNat) ⊔ T = spRadLine a w)
    {g : Fin (2 * n - 2) → ↥(StatedSp n (GaloisField 2 f))}
    (hgN : ∀ i, g i ∈
      Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 f))))
    (hgcover : spRad a ≤ T ⊔ ⨆ i,
      (spRadLine a w).map (MulAut.conj (g i)).toMonoidHom)
    {y : Fin (2 * n - 2) → ↥(xOf V H)}
    (hyM : ∀ i, (y i : G) ∈ M)
    (hyg : ∀ i, Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H (y i)) = g i) :
    P ≤ V ⊔ ((wOf V H ⊔ cPbar V H P) ⊓ P) ⊔ ⨆ i, conjSubgroup (y i : G) B := by
  let S : Subgroup G :=
    V ⊔ ((wOf V H ⊔ cPbar V H P) ⊓ P) ⊔ ⨆ i, conjSubgroup (y i : G) B
  have hDS : ∀ i, conjSubgroup (y i : G) B ≤ S := fun i =>
    (le_iSup (fun i => conjSubgroup (y i : G) B) i).trans le_sup_right
  have hES : ((wOf V H ⊔ cPbar V H P) ⊓ P) ≤ S := le_sup_right.trans le_sup_left
  have hVS : V ≤ S := le_sup_left.trans le_sup_left
  have hDSsub : ∀ i, (conjSubgroup (y i : G) B).subgroupOf P ≤ S.subgroupOf P := by
    intro i b hb
    exact Subgroup.mem_subgroupOf.mpr (hDS i (Subgroup.mem_subgroupOf.mp hb))
  have hTconj : ∀ i, T.map (MulAut.conj (g i)).toMonoidHom = T := fun i =>
    mem_normalizer_iff_conjSubgroup_eq.mp (hgN i)
  have hconjD : ∀ i, ((conjSubgroup (y i : G) B).subgroupOf P).map (h.bigPAct hNat) =
      ((B.subgroupOf P).map (h.bigPAct hNat)).map
        (MulAut.conj (g i)).toMonoidHom := fun i =>
    h.map_conj_image_B hNat hBP (hyM i) (hyg i)
  have hTle : T ≤ (S.subgroupOf P).map (h.bigPAct hNat) :=
    h.T_le_map_of_le hNat hTV hVS
  have hlinele : ∀ i, (spRadLine a w).map (MulAut.conj (g i)).toMonoidHom ≤
      (S.subgroupOf P).map (h.bigPAct hNat) := by
    intro i
    rw [← hline, Subgroup.map_sup, hTconj i, ← hconjD i]
    exact sup_le (Subgroup.map_mono (hDSsub i)) hTle
  have hSpRad : spRad a ≤ (S.subgroupOf P).map (h.bigPAct hNat) :=
    hgcover.trans (sup_le hTle (iSup_le hlinele))
  have hcover : P ≤ S := by
    intro p hp
    have hφsp : h.bigPAct hNat ⟨p, hp⟩ ∈ spRad a :=
      h.bigPAct_mem_spRad hNat hZ ha hT hTV ⟨p, hp⟩
    obtain ⟨s, hs, hsφ⟩ := Subgroup.mem_map.mp (hSpRad hφsp)
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hker : h.bigPAct hNat (s⁻¹ * ⟨p, hp⟩) = 1 := by
      rw [map_mul, map_inv, hsφ, inv_mul_cancel]
    have hmemI : ((s⁻¹ * ⟨p, hp⟩ : ↥P) : G) ∈ wOf V H ⊔ cPbar V H P :=
      (h.bigPAct_eq_one_iff hNat hZ (s⁻¹ * ⟨p, hp⟩)).1 hker
    have hmemE : ((s⁻¹ * ⟨p, hp⟩ : ↥P) : G) ∈
        (wOf V H ⊔ cPbar V H P) ⊓ P :=
      Subgroup.mem_inf.mpr ⟨hmemI, (s⁻¹ * ⟨p, hp⟩).2⟩
    have hp_eq : p = (s : G) * ((s⁻¹ * ⟨p, hp⟩ : ↥P) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hp_eq]
    exact S.mul_mem hsS (hES hmemE)
  exact hcover

theorem bigIWStatement_holds : BigIWStatement := by
  intro G _ _ M V Q P H h hZ
  obtain ⟨n, f, Φ, ψ, hn, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hVH : V ≤ H := h.setup.mc.toMinCex.V_le_H
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hf
    have := h.q_big
    omega
  have hFcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  obtain ⟨B, hBP, hBL, hBV, hBTI, hBcard, -⟩ :=
    sec34PairingStatement_holds G M V Q P H ⟨h.setup, h.tilde, h.concl⟩ h.three
  have hBcardF : Nat.card ↥B = Nat.card (GaloisField 2 f) := by
    rw [hBcard, h.module, ← hFcard]
  have hbot : B ⊓ (V ⊔ Eof V H P) = ⊥ :=
    h.B_inf_sup_Eof_eq_bot hZ hNat hf ha hT hTV hBP hBV hBTI hBL
  obtain ⟨w, hw, hwa, hline⟩ :=
    h.exists_line_of_isTI hZ hNat hf ha hT hTV hBP hBV hBTI hbot hBcardF
  obtain ⟨g, hgN, hgcover⟩ := exists_cover_spRad ha hT hw hwa
  choose y hy using fun i => h.exists_lift_normalizer_T hTV (hgN i)
  have hyM : ∀ i, (y i : G) ∈ M := fun i => (hy i).1
  have hyg : ∀ i, Φ.symm (xToXbar hVH (y i)) = g i := fun i => (hy i).2
  have hDP : ∀ i, conjSubgroup (y i : G) B ≤ P := fun i =>
    (h.conjSubgroup_isTI hBP hBV hBTI (hyM i)).1
  have hDV : ∀ i, conjSubgroup (y i : G) B ⊓ V = ⊥ := fun i =>
    (h.conjSubgroup_isTI hBP hBV hBTI (hyM i)).2.1
  have hTI : ∀ i, ∀ m ∈ M, conjSubgroup m (conjSubgroup (y i : G) B) ⊓
      conjSubgroup (y i : G) B ≠ ⊥ →
      conjSubgroup m (conjSubgroup (y i : G) B) = conjSubgroup (y i : G) B := fun i =>
    (h.conjSubgroup_isTI hBP hBV hBTI (hyM i)).2.2
  have hcover := h.cover_of_lines hZ hNat ha hT hTV hBP hline hgN hgcover hyM hyg
  have hPW : Nat.card ↥(P ⊓ wOf V H) = qBar V H ^ ((2 * n - 2) + 1) := by
    rw [h.natCard_P_inf_wOf hf ψ]
    congr 1
    omega
  exact h.cPbar_le_wOf_of_cover hZ (fun i => conjSubgroup (y i : G) B) hDP hDV hTI hcover hPW

end CFSG.RankThree.GF2n.Tim79a
