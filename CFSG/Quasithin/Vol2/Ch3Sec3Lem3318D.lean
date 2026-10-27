module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318B
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2B

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

structure Data (G : Type) [Group G] [Finite G] (T M L D : Subgroup G) (n k : ℕ)
    (α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2))
    (Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)) : Prop where
  hyp : Hyp331 G T M L D
  n4 : 4 ≤ n
  n5 : n ≤ 5
  k1 : 1 ≤ k
  TL : T ≤ Subgroup.normalizer (L : Set G)
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥L
  ker_iff : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G)
  mapU : ((T ⊓ L).subgroupOf L).map α = unitriangular n (ZMod 2)
  inj : Function.Injective Φ
  range : Φ.range = commVPlus L T L
  equiv : ∀ (l : ↥L) (c : Fin k → Multiplicative (Fin n → ZMod 2)),
    (l : G) * (Φ c : G) * (l : G)⁻¹ =
      (Φ (vecAct k ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) c) : G)

theorem le_normalizer_of_h14 (h14 : Stmt3_3_14) {T M L D : Subgroup G} (h : Hyp331 G T M L D) :
    T ≤ Subgroup.normalizer (L : Set G) :=
  h.TM.trans (h14 G T M L D h).2

theorem exists_data (h14 : Stmt3_3_14) (hGA : CFSG.Open.GriessAllModelsStatement)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (e : ↥(autOn L (vPlus L T)) ≃* SpecialLinearGroup (Fin n) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] {k : ℕ} (hk : 1 ≤ k)
    (hDS : DirectSumOfCopies (autOn L (vPlus L T)) (commVPlus L T L) ⊥
      (FFModel.nat (StatedSL n (ZMod 2))) k) :
    ∃ (α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2))
      (Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)),
      Data G T M L D n k α Φ := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hTL := le_normalizer_of_h14 h14 h
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  obtain ⟨α₀, Φ₀, hα₀s, hα₀k, hΦ₀i, hΦ₀r, hΦ₀e⟩ :=
    exists_coords hLV hk hDS (Nat.card_congr e.toEquiv)
  obtain ⟨α', -, hα'k, hα'c⟩ := Ln2.exists_modO2Surj h hGA hTL hK hn4 hn5 e
  have hker₀ : α₀.ker = CFSG.pCore 2 ↥L := by
    rw [← hα'k]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα₀k, hα'c]
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := exists_conj_unitriangular hS₀ (K := ZMod 2) (by omega) hα₀s
  refine ⟨(MulAut.conj g).toMonoidHom.comp α₀,
    Φ₀.comp (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))), ⟨h, hn4, hn5, hk, hTL, ?_, ?_, fun l => ?_, hg, ?_, ?_,
    coords_conj hΦ₀e g⟩⟩
  · rw [MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hα₀s
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hker₀]
  · rw [← hα₀k]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · have hinj : Function.Injective (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) := by
      intro c d hcd
      have := congrArg (vecAct k ((g : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) hcd
      rwa [← vecAct_mul, ← vecAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, vecAct_one, vecAct_one] at this
    exact hΦ₀i.comp hinj
  · have hsurj : Function.Surjective (vecAct k ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) := by
      intro c
      refine ⟨vecAct k ((g : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) c, ?_⟩
      rw [← vecAct_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, vecAct_one]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, ← MonoidHom.range_eq_map, hΦ₀r]

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem mem_commV (hD : Data G T M L D n k α Φ) (c : Fin k → Multiplicative (Fin n → ZMod 2)) :
    (Φ c : G) ∈ ⁅vPlus L T, L⁆ := by
  have : Φ c ∈ Φ.range := ⟨c, rfl⟩
  rw [hD.range] at this
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_eq (hD : Data G T M L D n k α Φ) {x : G} (hx : x ∈ ⁅vPlus L T, L⁆) :
    ∃ c, (Φ c : G) = x := by
  have hxV : x ∈ vPlus L T := by
    have hred := Hyp331.vPlus_reduced hD.hyp.toSetup331
    have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
    exact Ch1Sec3.commutator_le_left_of_le_normalizer hLV hx
  have : (⟨x, hxV⟩ : ↥(vPlus L T)) ∈ Φ.range := by
    rw [hD.range]
    exact Subgroup.mem_subgroupOf.mpr hx
  obtain ⟨c, hc⟩ := this
  exact ⟨c, congrArg Subtype.val hc⟩

theorem comm_iff (hD : Data G T M L D n k α Φ) (l : ↥L)
    (c : Fin k → Multiplicative (Fin n → ZMod 2)) :
    (l : G) * (Φ c : G) * (l : G)⁻¹ = (Φ c : G) ↔
      ∀ i, ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (c i) = Multiplicative.toAdd (c i) := by
  rw [hD.equiv]
  constructor
  · intro hc i
    have h1 := hD.inj (Subtype.ext hc)
    have := congrFun h1 i
    rw [vecAct_apply] at this
    exact congrArg Multiplicative.toAdd this
  · intro hc
    congr 2
    funext i
    rw [vecAct_apply, hc]
    rfl

theorem coord_eq_zero (hD : Data G T M L D n k α Φ) {c : Fin k → Multiplicative (Fin n → ZMod 2)}
    (hc : ∀ t ∈ T ⊓ L, t * (Φ c : G) * t⁻¹ = (Φ c : G)) (i : Fin k) (j : Fin n)
    (hj : (j : ℕ) ≠ 0) : Multiplicative.toAdd (c i) j = 0 := by
  refine eq_zero_of_unitriangular_fix (fun u hu => ?_) j hj
  rw [← hD.mapU] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  exact (hD.comm_iff t c).mp (hc t (Subgroup.mem_subgroupOf.mp ht)) i

theorem col_zero_of_mem (hD : Data G T M L D n k α Φ) {l : ↥L} (hl : (l : G) ∈ T) (r : Fin n) :
    ((α l : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) r
      ⟨0, by have := hD.n4; omega⟩ = if (r : ℕ) = 0 then 1 else 0 := by
  have hu : α l ∈ unitriangular n (ZMod 2) := by
    rw [← hD.mapU]
    exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hl, l.2⟩, rfl⟩
  split_ifs with hr
  · rw [show r = ⟨0, _⟩ from Fin.ext hr]
    exact hu.2 _
  · exact hu.1 r _ (Fin.lt_def.mpr (by simp; omega))

end Data

end CFSG.Quasithin.H13.L3318
