module

public import CFSG.Quasithin.EmptyFaithful.S151YH
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem ya7_exists_orderOf_three [Finite G] {K : Subgroup G} (h : IsAltType K 3) :
    ∃ b ∈ K, orderOf b = 3 := by
  obtain ⟨α₃, hs, -⟩ := h
  have hdvd := Subgroup.card_dvd_of_surjective hs
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' 3 (hcard ▸ hdvd)
  exact ⟨(b₀ : G), b₀.2, by rw [Subgroup.orderOf_coe, hb₀]⟩

theorem ya7_not_mem_of_orderOf_three {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {y : G} (hy : y ∈ Q)
    (h3 : orderOf y = 3) : False := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨y, hy⟩
  rw [Subgroup.orderOf_mk, h3] at hk
  have h1 : 3 ∣ 2 ^ k := hk ▸ dvd_refl 3
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h1)
  omega

theorem ya7_coe_sub_perm (σ : Equiv.Perm (Fin 7)) (ζ : ↥(evenWeight 7)) :
    ((ζ - permWeight 7 σ ζ : ↥(evenWeight 7)) : Fin 7 → ZMod 2) = ya7Sub σ (ζ : Fin 7 → ZMod 2) := rfl

theorem ya7_rank3_le_card [Finite G] {U : Subgroup G} {x : G}
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) {γ : ↥U →* Multiplicative ↥(evenWeight 7)}
    (hγs : Function.Surjective γ) {σ : Equiv.Perm (Fin 7)}
    (hγe : ∀ u v : ↥U, (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (γ v) = permWeight 7 σ (Multiplicative.toAdd (γ u))) :
    (ya7ImVecs3 σ).card ≤
      Nat.card ↥⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ := by
  have hPN : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) := Subgroup.zpowers_le.mpr hxU
  have hW₁U : ⁅U, Subgroup.zpowers x⁆ ≤ U :=
    CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPN
  have hPW₁ : Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅U, Subgroup.zpowers x⁆ : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPN
  have hW₂W₁ : ⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ ⁅U, Subgroup.zpowers x⁆ :=
    CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPW₁
  have hPW₂ : Subgroup.zpowers x ≤
      Subgroup.normalizer ((⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPW₁
  have hW₃W₂ : ⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤
      ⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ :=
    CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPW₂
  have hW₃U : ⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ U :=
    hW₃W₂.trans (hW₂W₁.trans hW₁U)
  have hstep : ∀ a : ↥U, ∃ b : ↥U, (b : G) = ⁅(a : G), x⁆ ∧
      Multiplicative.toAdd (γ b) =
        Multiplicative.toAdd (γ a) - permWeight 7 σ (Multiplicative.toAdd (γ a)) := by
    intro a
    have hxn : x * (a : G) * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU (a : G)).mp a.2
    refine ⟨a * ⟨x * (a : G) * x⁻¹, hxn⟩⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    · rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hγe a ⟨x * (a : G) * x⁻¹, hxn⟩ rfl]
      exact (sub_eq_add_neg _ _).symm
  refine ya7_card_le_of_range σ
    (X := ↥⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆)
    (fun w => ((Multiplicative.toAdd (γ ⟨w, hW₃U w.2⟩) : ↥(evenWeight 7)) : Fin 7 → ZMod 2)) ?_
  intro z hz
  have hzmem : z ∈ evenWeight 7 := by
    simp only [ya7Delta, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact hz
  obtain ⟨u, hu⟩ := hγs (Multiplicative.ofAdd ⟨z, hzmem⟩)
  have hγu : Multiplicative.toAdd (γ u) = ⟨z, hzmem⟩ := by rw [hu]; rfl
  obtain ⟨b₁, hb₁, hγb₁⟩ := hstep u
  have hb₁W : (b₁ : G) ∈ ⁅U, Subgroup.zpowers x⁆ := by
    rw [hb₁]
    exact Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_zpowers x)
  obtain ⟨b₂, hb₂, hγb₂⟩ := hstep b₁
  have hb₂W : (b₂ : G) ∈ ⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ := by
    rw [hb₂]
    exact Subgroup.commutator_mem_commutator hb₁W (Subgroup.mem_zpowers x)
  obtain ⟨b₃, hb₃, hγb₃⟩ := hstep b₂
  have hb₃W : (b₃ : G) ∈ ⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ := by
    rw [hb₃]
    exact Subgroup.commutator_mem_commutator hb₂W (Subgroup.mem_zpowers x)
  refine ⟨⟨(b₃ : G), hb₃W⟩, ?_⟩
  have hb₃U : (⟨(b₃ : G), hW₃U hb₃W⟩ : ↥U) = b₃ := rfl
  show ((Multiplicative.toAdd (γ ⟨(b₃ : G), hW₃U hb₃W⟩) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) =
    ya7Sub3 σ z
  rw [hb₃U, hγb₃, ya7_coe_sub_perm, hγb₂, ya7_coe_sub_perm, hγb₁, ya7_coe_sub_perm, hγu]
  rfl

theorem ya7_rank3_le_card_block [Finite G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    (hα : IsAltBlockTypeWith L 7 α) {x : G} (hxL : x ∈ L) :
    (ya7ImVecs3 (α ⟨x, hxL⟩ : Equiv.Perm (Fin 7))).card ≤
      Nat.card ↥⁅⁅⁅blockU L, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ := by
  obtain ⟨γ, hγs, hγe⟩ := ya7_gamma hα
  have hUn : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  exact ya7_rank3_le_card (hUn hxL) hγs (fun u v huv => hγe ⟨x, hxL⟩ u v huv)

theorem ya7_commutator_card_le [Finite G] {U Kt : Subgroup G} {x : G} (hUp : IsPGroup 2 ↥U)
    (hKU : Kt ≤ Subgroup.normalizer (U : Set G)) (hUK : U ≤ Subgroup.normalizer (Kt : Set G))
    (hshort : IsShort2 Kt) (hA3 : IsAltType Kt 3) (hxK : x ∈ Kt) (hx3 : orderOf x = 3) :
    Nat.card ↥⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ 8 := by
  classical
  set P : Subgroup G := Subgroup.zpowers x with hPdef
  have hPK : P ≤ Kt := by rw [hPdef, Subgroup.zpowers_le]; exact hxK
  have hPN : P ≤ Subgroup.normalizer (U : Set G) := hPK.trans hKU
  set W₁ : Subgroup G := ⁅U, P⁆ with hW₁def
  set W₂ : Subgroup G := ⁅W₁, P⁆ with hW₂def
  set W₃ : Subgroup G := ⁅W₂, P⁆ with hW₃def
  have hW₁U : W₁ ≤ U := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPN
  have hPW₁ : P ≤ Subgroup.normalizer (W₁ : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPN
  have hW₂W₁ : W₂ ≤ W₁ := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPW₁
  have hPW₂ : P ≤ Subgroup.normalizer (W₂ : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPW₁
  have hW₃W₂ : W₃ ≤ W₂ := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPW₂
  have hW₂U : W₂ ≤ U := hW₂W₁.trans hW₁U
  have hN_le_Kt : ⁅U, Kt⁆ ≤ Kt := by
    refine Subgroup.commutator_le.2 fun u hu k hk => ?_
    have h1 : u * k * u⁻¹ ∈ Kt := (Subgroup.mem_normalizer_iff.mp (hUK hu) k).mp hk
    have e : ⁅u, k⁆ = (u * k * u⁻¹) * k⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Kt.mul_mem h1 (Kt.inv_mem hk)
  have hN_le_U : ⁅U, Kt⁆ ≤ U := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hKU
  have hN_norm : Kt ≤ Subgroup.normalizer ((⁅U, Kt⁆ : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hKU
  have hN_p : IsPGroup 2 ↥(⁅U, Kt⁆ : Subgroup G) := hUp.to_le hN_le_U
  have hN_O2 : ⁅U, Kt⁆ ≤ pCoreOf 2 Kt :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN_le_Kt hN_norm hN_p
  have hW₁N : W₁ ≤ ⁅U, Kt⁆ := Subgroup.commutator_mono le_rfl hPK
  have hW₂UK : W₂ ≤ blockU Kt := Subgroup.commutator_mono (hW₁N.trans hN_O2) hPK
  have hab : ∀ a b : ↥W₂, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have ha := hshort.2.2.1.1 (hW₂UK a.2)
    have hb := hshort.2.2.1.1 (hW₂UK b.2)
    exact (Subgroup.mem_centralizer_iff.mp ha.2 (b : G) hb.1).symm
  have hcopU : Nat.Coprime (Nat.card ↥P) (Nat.card ↥U) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUp
    rw [hPdef, Nat.card_zpowers, hx3, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hcopW : Nat.Coprime (Nat.card ↥P) (Nat.card ↥W₂) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hW₂U) hcopU
  obtain ⟨-, hdisj⟩ := CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp W₂ P hPW₂ hab hcopW
  have hWC : W₃ ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ (hdisj.le_bot))
    exact le_inf (le_inf (hW₃W₂.trans' inf_le_left) inf_le_right) inf_le_left
  obtain ⟨α₃, -, -, β₃, -, hβ₃k, -⟩ := hA3
  have hW₃UK : W₃ ≤ blockU Kt := hW₃W₂.trans hW₂UK
  let f : ↥W₃ →* Multiplicative ↥(evenWeight 3) := β₃.comp (Subgroup.inclusion hW₃UK)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (Subgroup.inclusion hW₃UK w) ∈ β₃.ker := hw
    rw [hβ₃k] at h1
    have h2 : (w : G) ∈ blockZ Kt := Subgroup.mem_subgroupOf.mp h1
    have h3 : (w : G) ∈ Subgroup.centralizer (Kt : Set G) := h2.2
    have h4 : (w : G) ∈ W₃ ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨w.2, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPK) h3⟩
    rw [hWC] at h4
    exact Subtype.ext (Subgroup.mem_bot.mp h4)
  calc Nat.card ↥W₃ ≤ Nat.card (Multiplicative ↥(evenWeight 3)) := Nat.card_le_card_of_injective f hf
    _ = Nat.card ↥(evenWeight 3) := Nat.card_congr Multiplicative.toAdd
    _ ≤ Nat.card (Fin 3 → ZMod 2) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = 8 := by
      rw [Nat.card_eq_fintype_card]
      simp

variable {L S : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)} {P : Finset (Finset (Fin 7))}

theorem Ya7Core.alpha_order_three [Finite G] (hc : Ya7Core L S α P) {y : G}
    (hy : y ∈ ya7Pre L α P) (hy3 : orderOf y = 3) :
    ∃ hyL : y ∈ L, (α ⟨y, hyL⟩) ^ 3 = 1 ∧ α ⟨y, hyL⟩ ≠ 1 := by
  have hyL := ya7Pre_le L α P hy
  refine ⟨hyL, ?_, ?_⟩
  · have h3 : y ^ 3 = 1 := by simpa [hy3] using pow_orderOf_eq_one y
    have : (⟨y, hyL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [← map_pow, this, map_one]
  · intro h1
    have hR : y ∈ pCoreOf 2 L := (mem_pCoreOf_iff_ker hc.ker).mpr ⟨hyL, h1⟩
    exact ya7_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hR hy3

theorem Ya7Core.eq_of_alpha_eq [Finite G] (hc : Ya7Core L S α P) {a b : G} (ha : a ∈ L) (hb : b ∈ L)
    (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (h : α ⟨a, ha⟩ = α ⟨b, hb⟩) : a = b := by
  have hρ : b⁻¹ * a ∈ pCoreOf 2 L := hc.inv_mul_mem_pCoreOf ha h.symm
  have hcomm : Commute b⁻¹ a := (show Commute b a from hab.symm).inv_left
  have hρ3 : (b⁻¹ * a) ^ 3 = 1 := by
    rw [hcomm.mul_pow, ha3, inv_pow, hb3]
    simp
  have hRp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hRp) ⟨b⁻¹ * a, hρ⟩
  have hdvd : orderOf (⟨b⁻¹ * a, hρ⟩ : ↥(pCoreOf 2 L)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hρ3))
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ 3 := (dvd_pow_self 2 hne).trans hdvd
    omega
  rw [hk0, pow_zero] at hk
  have h1 : (⟨b⁻¹ * a, hρ⟩ : ↥(pCoreOf 2 L)) = 1 := orderOf_eq_one_iff.mp hk
  have h2 : b⁻¹ * a = 1 := congrArg Subtype.val h1
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [h2, mul_one]

theorem ya7_module_contra [Finite G] (hc : Ya7Core L S α P) (hα : IsAltBlockTypeWith L 7 α)
    {Kt : Subgroup G} (hshort : IsShort2 Kt) (hA3 : IsAltType Kt 3) (hKP : Kt ≤ ya7Pre L α P)
    (hKN : ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (Kt : Set G)) {x : G} (hxK : x ∈ Kt)
    (hx3 : orderOf x = 3) : False := by
  obtain ⟨-, -, -, -, -, hrank, -⟩ := ya7_data (ya7D L S α) hc.sylowD hc.part hc.stabD
  have hxPt : x ∈ ya7Pre L α P := hKP hxK
  obtain ⟨hxL, hσ3, hσ1⟩ := hc.alpha_order_three hxPt hx3
  have hσQ : α ⟨x, hxL⟩ ∈ ya7PartStab P := (mem_ya7Pre.mp hxPt).2
  have h16 := hrank _ hσQ hσ3 hσ1
  have hA := ya7_rank3_le_card_block hα hxL
  have hUn : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hUp : IsPGroup 2 ↥(blockU L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le (ya7_blockU_le L)
  have hKU : Kt ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) :=
    hKP.trans ((ya7Pre_le L α P).trans hUn)
  have hUK : blockU L ≤ Subgroup.normalizer (Kt : Set G) :=
    (ya7_blockU_le L).trans (hc.pCoreOf_le_pre.trans (le_sup_left.trans hKN))
  have hB := ya7_commutator_card_le hUp hKU hUK hshort hA3 hxK hx3
  omega

theorem Ya7Core.not_C126Third [Finite G] (hc : Ya7Core L S α P) (hα : IsAltBlockTypeWith L 7 α) :
    ¬ C126Third (ya7Pre L α P ⊔ S) S := by
  rintro ⟨r, K, hr, hK, hcomm, hres, -, -⟩
  obtain ⟨-, -, -, -, -, -, hcomm3⟩ := ya7_data (ya7D L S α) hc.sylowD hc.part hc.stabD
  have hsolv := hc.isSolvable_H
  have hA3 : ∀ i, IsAltType (K i) 3 := fun i =>
    CFSG.Quasithin.C1Pack.isAltType_three_of_isBlock2_of_solvable (hK i).1.1 hsolv
  have hshort : ∀ i, IsShort2 (K i) := fun i => (hK i).1.1.1
  have hTR : twoResidual (ya7Pre L α P ⊔ S) ≤ ya7Pre L α P :=
    twoResidual_le_of_isTwoQuotient le_sup_left hc.H_le_normalizer hc.two_pow
  have hKP : ∀ i, K i ≤ ya7Pre L α P := fun i =>
    calc K i ≤ ⨆ j, K j := le_iSup K i
      _ = twoResidual (ya7Pre L α P ⊔ S) := hres.symm
      _ ≤ ya7Pre L α P := hTR
  have hx3 : ∀ i, ∃ y ∈ K i, orderOf y = 3 := fun i => ya7_exists_orderOf_three (hA3 i)
  have hr1 : r = 1 := by
    by_contra hne
    have hr2 : 2 ≤ r := by omega
    let i0 : Fin r := ⟨0, by omega⟩
    let j0 : Fin r := ⟨1, by omega⟩
    have hij : i0 ≠ j0 := by simp [i0, j0, Fin.ext_iff]
    obtain ⟨x₀, hx₀K, hx₀3⟩ := hx3 i0
    obtain ⟨x₁, hx₁K, hx₁3⟩ := hx3 j0
    have hcomm0 := hcomm i0 j0 hij
    have hcom : x₀ * x₁ = x₁ * x₀ := by
      have h1 : ⁅x₀, x₁⁆ ∈ ⁅K i0, K j0⁆ := Subgroup.commutator_mem_commutator hx₀K hx₁K
      rw [hcomm0] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
    obtain ⟨hx₀L, hσ₀3, hσ₀1⟩ := hc.alpha_order_three (hKP i0 hx₀K) hx₀3
    obtain ⟨hx₁L, hσ₁3, hσ₁1⟩ := hc.alpha_order_three (hKP j0 hx₁K) hx₁3
    have hσ₀Q : α ⟨x₀, hx₀L⟩ ∈ ya7PartStab P := (mem_ya7Pre.mp (hKP i0 hx₀K)).2
    have hσ₁Q : α ⟨x₁, hx₁L⟩ ∈ ya7PartStab P := (mem_ya7Pre.mp (hKP j0 hx₁K)).2
    have hcommα : α ⟨x₀, hx₀L⟩ * α ⟨x₁, hx₁L⟩ = α ⟨x₁, hx₁L⟩ * α ⟨x₀, hx₀L⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcom
    have hx₀cube : x₀ ^ 3 = 1 := by simpa [hx₀3] using pow_orderOf_eq_one x₀
    have hx₁cube : x₁ ^ 3 = 1 := by simpa [hx₁3] using pow_orderOf_eq_one x₁
    have hx₁eq : x₁ ∈ K i0 := by
      rcases hcomm3 _ hσ₀Q _ hσ₁Q hσ₀3 hσ₀1 hσ₁3 hσ₁1 hcommα with h | h
      · have := hc.eq_of_alpha_eq hx₁L hx₀L hcom.symm hx₁cube hx₀cube h
        rw [this]
        exact hx₀K
      · have hinvL : x₀⁻¹ ∈ L := L.inv_mem hx₀L
        have h' : α ⟨x₁, hx₁L⟩ = α ⟨x₀⁻¹, hinvL⟩ := by
          rw [h, show (⟨x₀⁻¹, hinvL⟩ : ↥L) = (⟨x₀, hx₀L⟩ : ↥L)⁻¹ from rfl, map_inv]
        have hcom' : x₁ * x₀⁻¹ = x₀⁻¹ * x₁ :=
          ((show Commute x₀ x₁ from hcom).inv_left).symm.eq
        have hcube' : x₀⁻¹ ^ 3 = 1 := by rw [inv_pow, hx₀cube, inv_one]
        have := hc.eq_of_alpha_eq hx₁L hinvL hcom' hx₁cube hcube' h'
        rw [this]
        exact (K i0).inv_mem hx₀K
    have hx₁C : x₁ ∈ Subgroup.centralizer (pCoreOf 2 (K j0) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkK : k ∈ K j0 := CFSG.LieType.BorelTits.pCoreOf_le 2 (K j0) hk
      have h1 : ⁅x₁, k⁆ ∈ ⁅K i0, K j0⁆ := Subgroup.commutator_mem_commutator hx₁eq hkK
      rw [hcomm0] at h1
      have := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      exact this.symm
    have hx₁O : x₁ ∈ pCoreOf 2 (K j0) := (hshort j0).2.1 ⟨hx₁K, hx₁C⟩
    exact ya7_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K j0)) hx₁O hx₁3
  subst hr1
  have hK0 : twoResidual (ya7Pre L α P ⊔ S) = K 0 := by
    rw [hres]
    exact iSup_unique K
  have hKN : ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (K 0 : Set G) := by
    rw [← hK0]
    exact le_normalizer_twoResidual _
  obtain ⟨x, hxK, hx3'⟩ := hx3 0
  exact ya7_module_contra hc hα (hshort 0) (hA3 0) (hKP 0) hKN hxK hx3'

end CFSG.Quasithin
