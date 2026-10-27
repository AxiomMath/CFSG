module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre
public import CFSG.Quasithin.Vol2.Ch3Sec3L32Center
public import CFSG.Quasithin.Vol2.Ch3Sec3L32Cocycle
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

@[expose] def Stmt3_3_28L32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      qL L T = vPlus L T ⊔ tC L T ∧ ⁅vPlus L T, tC L T⁆ = ⊥ ∧ frattini ↥(qL L T) = ⊥

@[expose] def Stmt3_3_28U33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSU 3 3 1 ↥(autOn L (vPlus L T)) → tC L T = ⊥ ∧ qL L T = vPlus L T

namespace Lem3328

variable {G : Type} [Group G]

theorem mem_preCenterAut {T V : Subgroup G} {x : G} :
    x ∈ preCenterAut T V ↔ x ∈ T ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨x, hx⟩ ∈ (Subgroup.center ↥(autOn T V)).map (autOn T V).subtype := by
  unfold preCenterAut
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    exact ⟨hxT, y.2, hy⟩
  · rintro ⟨hxT, hx, hc⟩
    exact ⟨hxT, ⟨x, hx⟩, hc, rfl⟩

theorem eq_of_card_two {H : Type*} [Group H] (h : Nat.card H = 2) {x y : H} (hx : x ≠ 1)
    (hy : y ≠ 1) : x = y := by
  obtain ⟨a, b, -, huniv⟩ := Nat.card_eq_two_iff.mp h
  have hall : ∀ t : H, t = a ∨ t = b := fun t => by
    have : t ∈ ({a, b} : Set H) := huniv ▸ Set.mem_univ t
    simpa using this
  rcases hall 1 with h1 | h1 <;> rcases hall x with h2 | h2 <;> rcases hall y with h3 | h3
  all_goals first
    | exact h2.trans h3.symm
    | exact absurd (h2.trans h1.symm) hx
    | exact absurd (h3.trans h1.symm) hy

theorem mem_centralizer_of_conjAct_eq_one {V : Subgroup G} (g : Subgroup.normalizer (V : Set G))
    (h : conjAct V g = 1) : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
  simp only [InternalSec.coe_conjAct_apply, MulAut.one_apply] at this
  calc v * g = ((g : G) * v * (g : G)⁻¹) * g := by rw [this]
    _ = g * v := by group

theorem mem_pCore_iff {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff x).symm

theorem exists_mem_blockU_of_cocycle {L Q : Subgroup G} (hLn : IsLnBlock L 3)
    (hQU : ∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ blockU L)
    (hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Subgroup.centralizer (L : Set G))
    (hOQ : pCoreOf 2 L ≤ Q) {c : G} (hc : c ∈ Q) {s : G} (hs : s ∈ L)
    (hs2 : s ^ 2 ∈ pCoreOf 2 L) (hs1 : s ∉ pCoreOf 2 L) (hcs : ⁅c, s⁆ ∈ blockZ L) :
    ∃ u ∈ blockU L, u⁻¹ * c ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hL, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hLn
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := fun x hx =>
    mem_normalizer_commutator (hLQ hx) (Subgroup.le_normalizer hx)
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := by
    intro a ha b hb
    have h1 := hL.2.2.1.1 ha
    have h2 := hL.2.2.1.1 hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1).2 b
      (Subgroup.mem_inf.mp h2).1).symm
  have hβZ : ∀ u : ↥(blockU L), (u : G) ∈ blockZ L → β u = 1 := by
    intro u hu
    have : u ∈ β.ker := by rw [hβk]; exact Subgroup.mem_subgroupOf.mpr hu
    exact this
  let cU : ↥L → ↥(blockU L) := fun ℓ => ⟨⁅c, (ℓ : G)⁆, hQU c hc ℓ ℓ.2⟩
  have hdep : ∀ ℓ ℓ' : ↥L, α ℓ = α ℓ' → β (cU ℓ) = β (cU ℓ') := by
    intro ℓ ℓ' he
    have hk : ℓ'⁻¹ * ℓ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [hαk, mem_pCore_iff] at hk
    have hz : ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ ∈ blockZ L :=
      ⟨hQU c hc _ (ℓ'⁻¹ * ℓ).2, hQQ c hc _ (hOQ hk)⟩
    have hcen : (ℓ' : G) * ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ = ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ * ℓ' :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 ℓ' ℓ'.2
    have e : cU ℓ = cU ℓ' * ⟨⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆, (Subgroup.mem_inf.mp hz).1⟩ := by
      apply Subtype.ext
      show ⁅c, (ℓ : G)⁆ = ⁅c, (ℓ' : G)⁆ * ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆
      have e1 : ⁅c, (ℓ : G)⁆ = ⁅c, (ℓ' : G)⁆ *
          ((ℓ' : G) * ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ * (ℓ' : G)⁻¹) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1, hcen, mul_inv_cancel_right]
    rw [e, map_mul, hβZ ⟨_, (Subgroup.mem_inf.mp hz).1⟩ hz, mul_one]
  let δ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) → (Fin 3 → ZMod 2) := fun g =>
    Multiplicative.toAdd (β (cU (Function.surjInv hαs g)))
  have hδα : ∀ ℓ, δ (α ℓ) = Multiplicative.toAdd (β (cU ℓ)) := by
    intro ℓ
    show Multiplicative.toAdd (β (cU (Function.surjInv hαs (α ℓ)))) = _
    rw [hdep _ ℓ (Function.surjInv_eq hαs (α ℓ))]
  have hδc : ∀ g h, δ (g * h) = δ g +
      ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (δ h) := by
    intro g h
    obtain ⟨ℓ₁, rfl⟩ := hαs g
    obtain ⟨ℓ₂, rfl⟩ := hαs h
    rw [← map_mul, hδα, hδα, hδα]
    have hw : (ℓ₁ : G) * ⁅c, (ℓ₂ : G)⁆ * (ℓ₁ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hLU ℓ₁.2) _).mp (hQU c hc ℓ₂ ℓ₂.2)
    have e : cU (ℓ₁ * ℓ₂) = cU ℓ₁ * ⟨_, hw⟩ := by
      apply Subtype.ext
      show ⁅c, ((ℓ₁ * ℓ₂ : ↥L) : G)⁆ = ⁅c, (ℓ₁ : G)⁆ * ((ℓ₁ : G) * ⁅c, (ℓ₂ : G)⁆ * (ℓ₁ : G)⁻¹)
      simp only [commutatorElement_def, Subgroup.coe_mul]
      group
    rw [e, map_mul, toAdd_mul, hβe ℓ₁ (cU ℓ₂) ⟨_, hw⟩ rfl]
  have hsα1 : α ⟨s, hs⟩ ≠ 1 := by
    intro h1
    have : (⟨s, hs⟩ : ↥L) ∈ α.ker := h1
    rw [hαk, mem_pCore_iff] at this
    exact hs1 this
  have hsα2 : α ⟨s, hs⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨s, hs⟩ : ↥L) ^ 2 ∈ α.ker := by
      rw [hαk, mem_pCore_iff]
      simpa using hs2
    exact this
  have hδs : δ (α ⟨s, hs⟩) = 0 := by
    rw [hδα, hβZ _ hcs]
    rfl
  obtain ⟨v, hv⟩ := factL32Cocycle_holds δ hδc _ hsα1 hsα2 hδs
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
  refine ⟨u, u.2, Lem3328.mem_centralizer_of_commutator_mem_blockZ hL fun ℓ hℓ => ?_⟩
  have hul : (ℓ : G) * (u : G)⁻¹ * ℓ⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (hLU hℓ) _).mp (Subgroup.inv_mem _ u.2)
  have hcu : (⁅(u : G), ℓ⁆ : G) ∈ blockU L := by
    have : ⁅(u : G), ℓ⁆ = (u : G) * ((ℓ : G) * (u : G)⁻¹ * ℓ⁻¹) := by
      rw [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ u.2 hul
  have hβu : Multiplicative.toAdd (β ⟨⁅(u : G), ℓ⁆, hcu⟩) =
      v - ((α ⟨ℓ, hℓ⟩ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := by
    have e : (⟨⁅(u : G), ℓ⁆, hcu⟩ : ↥(blockU L)) = u * ⟨_, hul⟩ :=
      Subtype.ext (by
        show ⁅(u : G), ℓ⁆ = (u : G) * ((ℓ : G) * (u : G)⁻¹ * ℓ⁻¹)
        rw [commutatorElement_def]; group)
    rw [e, map_mul, toAdd_mul, hβe ⟨ℓ, hℓ⟩ u⁻¹ ⟨_, hul⟩ rfl, map_inv, toAdd_inv, hu,
      toAdd_ofAdd, sub_eq_add_neg]
    congr 1
    exact Matrix.mulVec_neg ..
  have hβc : Multiplicative.toAdd (β (cU ⟨ℓ, hℓ⟩)) =
      v - ((α ⟨ℓ, hℓ⟩ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := by
    rw [← hδα]
    exact hv _
  have hββ : β (cU ⟨ℓ, hℓ⟩) = β ⟨⁅(u : G), ℓ⁆, hcu⟩ :=
    Multiplicative.toAdd.injective (hβc.trans hβu.symm)
  have hker : cU ⟨ℓ, hℓ⟩ * (⟨⁅(u : G), ℓ⁆, hcu⟩ : ↥(blockU L))⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hββ]
    exact mul_inv_cancel _
  rw [hβk, Subgroup.mem_subgroupOf] at hker
  have hz : ⁅c, ℓ⁆ * ⁅(u : G), ℓ⁆⁻¹ ∈ blockZ L := hker
  have hwU : ⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹) ∈ blockU L :=
    Subgroup.mul_mem _ (hQU c hc ℓ hℓ)
      ((Subgroup.mem_normalizer_iff.mp (hLU hℓ) _).mp u.2)
  have huw := hUab _ u.2 _ hwU
  have e : ⁅(u : G)⁻¹ * c, ℓ⁆ = ⁅c, ℓ⁆ * ⁅(u : G), ℓ⁆⁻¹ := by
    have e1 : ⁅(u : G)⁻¹ * c, ℓ⁆ = (u : G)⁻¹ * (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) := by
      simp only [commutatorElement_def]; group
    have e2 : ⁅c, ℓ⁆ * ⁅(u : G), ℓ⁆⁻¹ = (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) * (u : G)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1, e2]
    calc (u : G)⁻¹ * (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) =
        (u : G)⁻¹ * ((⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) * u) * (u : G)⁻¹ := by group
      _ = (u : G)⁻¹ * ((u : G) * (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹))) * (u : G)⁻¹ := by rw [huw]
      _ = _ := by group
  rw [e]
  exact hz

end Lem3328

open Lem3328

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

namespace Hyp331

theorem preCenterAut_of_isPSL
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hP : IsPSL 3 2 1 ↥(autOn L (vPlus L T))) :
    qL L T ≤ preCenterAut T (vPlus L T) ∧
    (∀ x ∈ preCenterAut T (vPlus L T), ∃ hx : x ∈ Subgroup.normalizer (vPlus L T : Set G),
      conjAct (vPlus L T) ⟨x, hx⟩ ∈ autOn L (vPlus L T)) ∧
    ∀ a ∈ preCenterAut T (vPlus L T), ∀ b ∈ preCenterAut T (vPlus L T),
      a ∉ qL L T → b ∉ qL L T → a⁻¹ * b ∈ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := vPlus_reduced h.toSetup331
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hMp := mPlus_eq_of_le hTL
  obtain ⟨hKX, hXK, h2X, hSyl⟩ := h.autOn_data
  rw [hMp] at hKX hXK h2X
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) (vPlus L T)) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  obtain ⟨hZ2, hZL⟩ := factL32CenterTwo_holds (MulAut ↥(vPlus L T)) _ _ _ hKX hXK hP h2X hO2 hSyl
  have hcen : ∀ x ∈ preCenterAut T (vPlus L T), x ∉ qL L T → ∃ hx : x ∈ Subgroup.normalizer
      (vPlus L T : Set G), ∃ z : ↥(Subgroup.center ↥(autOn T (vPlus L T))), z ≠ 1 ∧
        ((z : ↥(autOn T (vPlus L T))) : MulAut ↥(vPlus L T)) = conjAct (vPlus L T) ⟨x, hx⟩ := by
    intro x hx hxQ
    obtain ⟨hxT, hxN, z, hz, hzx⟩ := mem_preCenterAut.mp hx
    refine ⟨hxN, ⟨z, hz⟩, fun h1 => hxQ ?_, hzx⟩
    have h2 : conjAct (vPlus L T) ⟨x, hxN⟩ = 1 := by
      rw [← hzx]
      have := congrArg (fun t : ↥(Subgroup.center ↥(autOn T (vPlus L T))) =>
        ((t : ↥(autOn T (vPlus L T))) : MulAut ↥(vPlus L T))) h1
      exact this
    rw [← hCQ]
    exact ⟨hxT, mem_centralizer_of_conjAct_eq_one _ h2⟩
  have hidx : ∀ a ∈ preCenterAut T (vPlus L T), ∀ b ∈ preCenterAut T (vPlus L T),
      a ∉ qL L T → b ∉ qL L T → a⁻¹ * b ∈ qL L T := by
    intro a ha b hb haQ hbQ
    obtain ⟨haN, za, hza1, hza⟩ := hcen a ha haQ
    obtain ⟨hbN, zb, hzb1, hzb⟩ := hcen b hb hbQ
    have hzz := eq_of_card_two hZ2 hza1 hzb1
    have hab : conjAct (vPlus L T) ⟨a, haN⟩ = conjAct (vPlus L T) ⟨b, hbN⟩ := by
      rw [← hza, ← hzb, hzz]
    have h1 : conjAct (vPlus L T) (⟨a, haN⟩⁻¹ * ⟨b, hbN⟩) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 := mem_centralizer_of_conjAct_eq_one _ h1
    rw [← hCQ]
    refine ⟨T.mul_mem (T.inv_mem (mem_preCenterAut.mp ha).1) (mem_preCenterAut.mp hb).1, ?_⟩
    simpa using h2
  have hQT₀ : qL L T ≤ preCenterAut T (vPlus L T) := by
    intro q hq
    have h1 := InternalSec.conjAct_eq_one_of_mem_centralizer ⟨q, hTV (hQT hq)⟩ (hQC hq)
    refine mem_preCenterAut.mpr ⟨hQT hq, hTV (hQT hq), ⟨1, Subgroup.one_mem _, ?_⟩⟩
    rw [h1]
    rfl
  refine ⟨hQT₀, fun x hx => ?_, hidx⟩
  obtain ⟨-, hxN, z, hz, hzx⟩ := mem_preCenterAut.mp hx
  exact ⟨hxN, hzx ▸ hZL ⟨z, hz, rfl⟩⟩

theorem qL_le_sup_tC
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hP : IsPSL 3 2 1 ↥(autOn L (vPlus L T)))
    (hLn : IsLnBlock L 3)
    (hDT₀ : D ≤ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G)) {d : G}
    (hdD : d ∈ D) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) :
    qL L T ≤ vPlus L T ⊔ tC L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hshort := hLn.1
  have hred := vPlus_reduced h.toSetup331
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hHV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hHV
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hHV
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hd₀ : d ∈ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G) := hDT₀ hdD
  have hV2 : ∀ v ∈ vPlus L T, v ^ 2 = 1 := hred.2.1.2
  have hFQ := h.frattini_qL_le_tC h38 h39 hshort hTL
  have hQQ : ∀ a ∈ qL L T, ∀ b ∈ qL L T, ⁅a, b⁆ ∈ tC L T := by
    intro a ha b hb
    have : Fact (IsPGroup 2 ↥(qL L T)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
    have hF := CFSG.frattini_eq_closure_commutator_union_powers (R := ↥(qL L T)) (p := 2)
    have h1 : ⁅(⟨a, ha⟩ : ↥(qL L T)), ⟨b, hb⟩⁆ ∈ frattini ↥(qL L T) :=
      hF ▸ Subgroup.subset_closure (Or.inl (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) (Subgroup.mem_top _)))
    exact hFQ ⟨_, h1, rfl⟩
  have hQU : ∀ q ∈ qL L T, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ blockU L := fun q hq ℓ hℓ =>
    commutator_qL_le_blockU hshort hTL (Subgroup.commutator_mem_commutator hq hℓ)
  have hUV := h.blockU_le_vPlus h38 h39 hshort hTL
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hnt := h.not_L_le_centralizer h38 h39
  have hCLV := inf_centralizer_le_of_isLnBlock hLn hLV (hOQ.trans hQC) hnt
  have hCLT := sup_inf_centralizer_le_pCoreOf h.sylow.1 hTL hHV
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hCLV)
  obtain ⟨hQT₀, hinL, hidx⟩ := h.preCenterAut_of_isPSL h38 h39 hTL hP
  have hd₀' : ∀ x ∈ preCenterAut T (vPlus L T), d * x * d⁻¹ ∈ preCenterAut T (vPlus L T) :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hd₀ x).mp hx
  have hd₀'' : ∀ x ∈ preCenterAut T (vPlus L T), d⁻¹ * x * d ∈ preCenterAut T (vPlus L T) := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hd₀) x).mp hx
    simpa using this
  have hmemW : ∀ x, x ∈ CFSG.conjugate (vPlus L T) d ↔ d * x * d⁻¹ ∈ vPlus L T := by
    intro x
    rw [CFSG.conjugate, A38.mem_map_conj, inv_inv]
  obtain ⟨v₀, hv₀, hv₀Q⟩ : ∃ v₀ ∈ vPlus L T, d * v₀ * d⁻¹ ∉ qL L T := by
    by_contra hall
    push Not at hall
    apply hdV
    intro w hw
    rw [hmemW] at hw
    have hwT : w ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdT) _).mp (hQT (hVQ hw))
      simpa [mul_assoc] using this
    rw [← hCQ]
    refine ⟨hwT, Subgroup.mem_centralizer_iff.mpr fun v' hv' => ?_⟩
    have h2 := Subgroup.mem_centralizer_iff.mp (hQC (hall v' hv')) _ hw
    have h3 : d * (w * v') * d⁻¹ = d * (v' * w) * d⁻¹ := by
      calc d * (w * v') * d⁻¹ = (d * w * d⁻¹) * (d * v' * d⁻¹) := by group
        _ = (d * v' * d⁻¹) * (d * w * d⁻¹) := h2
        _ = d * (v' * w) * d⁻¹ := by group
    have h4 : w * v' = v' * w := by
      have := congrArg (fun x => d⁻¹ * x * d) h3
      simpa [mul_assoc] using this
    exact h4.symm
  have hdec : ∀ q ∈ qL L T, ∃ v ∈ vPlus L T, v⁻¹ * q ∈ qL L T ∧ d * (v⁻¹ * q) * d⁻¹ ∈ qL L T := by
    intro q hq
    by_cases hdq : d * q * d⁻¹ ∈ qL L T
    · exact ⟨1, (vPlus L T).one_mem, by simpa using hq, by simpa using hdq⟩
    · refine ⟨v₀, hv₀, (qL L T).mul_mem ((qL L T).inv_mem (hVQ hv₀)) hq, ?_⟩
      have := hidx _ (hd₀' _ (hQT₀ (hVQ hv₀))) _ (hd₀' _ (hQT₀ hq)) hv₀Q hdq
      have e : (d * v₀ * d⁻¹)⁻¹ * (d * q * d⁻¹) = d * (v₀⁻¹ * q) * d⁻¹ := by group
      rwa [e] at this
  obtain ⟨t, htW, htQ⟩ := IsConcreteLE.not_le_iff_exists.mp hdV
  have htV : d * t * d⁻¹ ∈ vPlus L T := (hmemW t).mp htW
  have htT₀ : t ∈ preCenterAut T (vPlus L T) := by
    have := hd₀'' _ (hQT₀ (hVQ htV))
    simpa [mul_assoc] using this
  obtain ⟨htN, hztL⟩ := hinL t htT₀
  obtain ⟨⟨s, hsN⟩, hsL, hst⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hztL
  have hk : s⁻¹ * t ∈ qL L T := by
    refine hCLT (Subgroup.mem_inf.mpr ⟨(L ⊔ T).mul_mem (Subgroup.mem_sup_left (L.inv_mem hsL))
      (Subgroup.mem_sup_right (mem_preCenterAut.mp htT₀).1), ?_⟩)
    have h1 : conjAct (vPlus L T) (⟨s, hsN⟩⁻¹ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, map_inv, hst, inv_mul_cancel]
    simpa using mem_centralizer_of_conjAct_eq_one _ h1
  have ht2 : t ^ 2 = 1 := by
    have h1 := hV2 _ htV
    have h2 : d * t ^ 2 * d⁻¹ = 1 := by
      rw [show d * t ^ 2 * d⁻¹ = (d * t * d⁻¹) ^ 2 by rw [pow_two, pow_two]; group, h1]
    have := congrArg (fun x => d⁻¹ * x * d) h2
    simpa [mul_assoc] using this
  have hs2 : s ^ 2 ∈ pCoreOf 2 L := by
    refine hCLV (Subgroup.mem_inf.mpr ⟨L.pow_mem hsL 2, ?_⟩)
    have h1 : conjAct (vPlus L T) (⟨s, hsN⟩ ^ 2) = 1 := by
      rw [map_pow, hst, ← map_pow]
      have : (⟨t, htN⟩ : Subgroup.normalizer (vPlus L T : Set G)) ^ 2 = 1 :=
        Subtype.ext (by simpa using ht2)
      rw [this, map_one]
    simpa using mem_centralizer_of_conjAct_eq_one _ h1
  have hs1 : s ∉ pCoreOf 2 L := by
    intro hsO
    apply htQ
    have h1 := InternalSec.conjAct_eq_one_of_mem_centralizer ⟨s, hsN⟩ (hQC (hOQ hsO))
    rw [hst] at h1
    rw [← hCQ]
    exact ⟨(mem_preCenterAut.mp htT₀).1, mem_centralizer_of_conjAct_eq_one _ h1⟩
  have hQQ' : ∀ a ∈ qL L T, ∀ b ∈ qL L T, ⁅a, b⁆ ∈ Subgroup.centralizer (L : Set G) :=
    fun a ha b hb => (Subgroup.mem_inf.mp (hQQ a ha b hb)).2
  have hmain : ∀ c ∈ qL L T, d * c * d⁻¹ ∈ qL L T → c ∈ vPlus L T ⊔ tC L T := by
    intro c hc hdc
    have hct : c * t = t * c := by
      have h1 := Subgroup.mem_centralizer_iff.mp (hQC hdc) _ htV
      have h3 : d * (c * t) * d⁻¹ = d * (t * c) * d⁻¹ := by
        calc d * (c * t) * d⁻¹ = (d * c * d⁻¹) * (d * t * d⁻¹) := by group
          _ = (d * t * d⁻¹) * (d * c * d⁻¹) := h1.symm
          _ = d * (t * c) * d⁻¹ := by group
      have := congrArg (fun x => d⁻¹ * x * d) h3
      simpa [mul_assoc] using this
    have hcs : ⁅c, s⁆ ∈ blockZ L := by
      refine ⟨hQU c hc s hsL, ?_⟩
      have hck := hQQ' c hc _ hk
      have e : ⁅c, s⁆ = s * ⁅c, s⁻¹ * t⁆⁻¹ * s⁻¹ := by
        have e1 : ⁅c, t⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm]; exact hct
        have e2 : ⁅c, t⁆ = ⁅c, s⁆ * (s * ⁅c, s⁻¹ * t⁆ * s⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1] at e2
        have := eq_inv_of_mul_eq_one_left e2.symm
        rw [this]
        group
      rw [e]
      have hck' : ⁅c, s⁻¹ * t⁆⁻¹ ∈ Subgroup.centralizer (L : Set G) := inv_mem hck
      have hcomm := Subgroup.mem_centralizer_iff.mp hck' s hsL
      rw [hcomm, mul_inv_cancel_right]
      exact hck'
    obtain ⟨u, hu, huc⟩ := exists_mem_blockU_of_cocycle hLn hQU hQQ' hOQ hc hsL hs2 hs1 hcs
    have huT : (u : G)⁻¹ * c ∈ tC L T :=
      Subgroup.mem_inf.mpr ⟨T.mul_mem (T.inv_mem (hQT (hVQ (hUV hu)))) (hQT hc), huc⟩
    have : c = u * (u⁻¹ * c) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hUV hu)) (Subgroup.mem_sup_right huT)
  intro q hq
  obtain ⟨v, hv, hvq, hdvq⟩ := hdec q hq
  have : q = v * (v⁻¹ * q) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (hmain _ hvq hdvq)

end Hyp331

theorem stmt3_3_28L32_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h23 : Stmt3_3_23) (h25 : Stmt3_3_25) (h26 : Stmt3_3_26) (h27 : Stmt3_3_27) :
    Stmt3_3_28L32 := by
  intro G _ _ T M L D h hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hshort : IsShort2 L := by
    rcases (h25 G T M L D h).1 with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  obtain ⟨hLn, hDT₀⟩ : IsLnBlock L 3 ∧
      D ≤ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G) := by
    rcases h23 G T M L D h hP with h1 | ⟨⟨h2c, -⟩, -⟩
    · exact h1
    · exact absurd h2c (not_hasNoncentralTwoChief_two_of_isShort2 hshort)
  obtain ⟨d, hdD, hdM, hdV⟩ := h26 G T M L D h
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hCL : tC L T ≤ qL L T := h.tC_le_qL h38 h39 hTL
  have hQeq : qL L T = vPlus L T ⊔ tC L T :=
    le_antisymm (h.qL_le_sup_tC h38 h39 hTL hP hLn hDT₀ hdD hdV) (sup_le hVQ hCL)
  have hVT : vPlus L T ≤ Subgroup.centralizer (tC L T : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hCL.trans hQC)
  refine ⟨hQeq, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hVT, ?_⟩
  have hTCe : IsElemAbelian 2 (tC L T) := by
    by_cases hTC : tC L T = ⊥
    · rw [hTC]
      refine ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => ?_⟩
      rw [Subgroup.mem_bot] at hx
      rw [hx, one_pow]
    · obtain ⟨-, hF, -⟩ := h27 G T M L D h d hdD hdM hdV hTC
      exact isElemAbelian_of_frattini_eq_bot (h.sylow.1.to_le inf_le_left) hF
  have hQe : IsElemAbelian 2 (qL L T) := by
    rw [hQeq]
    exact B2F.isElemAbelian_sup_of_commute hred.2.1 hTCe fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hCL.trans hQC hb) a ha)
  exact frattini_eq_bot_of_isElemAbelian hQe

end CFSG.Quasithin.H13
